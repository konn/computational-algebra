{-# LANGUAGE BangPatterns, ScopedTypeVariables, StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns                                          #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Algebra.Algorithms.Groebner.Signature (f5) where
import           Algebra.Prelude.Core         hiding (Vector)
import qualified Control.Foldl                as Fl
import           Control.Monad.Loops          (whileJust_)
import           Control.Monad.ST.Combinators (ST, STRef, modifySTRef',
                                               newSTRef, readSTRef, runST,
                                               writeSTRef)
import qualified Data.Heap                    as H
import           Data.Monoid                  (First (..))
import qualified Data.Set                     as Set
import qualified Data.Vector                  as V
import qualified Data.Vector.Mutable          as MV

data Entry a b = Entry { priority :: !a
                       , payload :: !b
                       } deriving (Show)

instance Eq a => Eq (Entry a b) where
  (==) = (==) `on` priority
  {-# INLINE (==) #-}
  (/=) = (/=) `on` priority
  {-# INLINE (/=) #-}

instance Ord a => Ord (Entry a b) where
  compare = comparing priority

f5 :: (IsOrderedPolynomial a, Field (Coefficient a))
   => Ideal a -> [a]
f5 ideal = let sideal = V.fromList $ generators ideal
  in V.toList $ V.map snd $ calcSignatureGB  sideal

data ModuleElement poly = ME { syzSign :: !(Signature poly)
                             , _polElem :: !poly
                             }
                        deriving (Eq, Ord)

data JPair poly = JPair { _jpTerm  :: !(OMonom poly)
                        , _jpIndex :: !Int
                        }
deriving instance KnownNat (Arity poly) => Show (JPair poly)
deriving instance KnownNat (Arity poly) => Eq (JPair poly)

type OMonom p = OrderedMonomial (MOrder p) (Arity p)

class Multiplicative c => Action c a where
  (.*!) :: c -> a -> a

infixl 7 .*!

instance {-# OVERLAPPING #-} (Arity poly ~ k, MOrder poly ~ ord, IsOrderedPolynomial poly) =>
         Action (OrderedMonomial ord k) (ModuleElement poly) where
  m .*! ME u v = ME (m .*! u) (m >* v)
  {-# INLINE (.*!) #-}

instance {-# OVERLAPPING #-} (Arity poly ~ k, MOrder poly ~ ord, IsOrderedPolynomial poly) =>
         Action (OrderedMonomial ord k) (Signature poly) where
  m .*! Signature i f = Signature i (m * f)
  {-# INLINE (.*!) #-}

calcSignatureGB :: forall poly.
                   (Field (Coefficient poly), IsOrderedPolynomial poly)
                => V.Vector poly -> V.Vector (Signature poly, poly)
calcSignatureGB side | all isZero side = V.empty
calcSignatureGB (V.map monoize . V.filter (not . isZero) -> sideal) = runST $ do
  let n = V.length sideal
      mods0 = V.generate n basis
      preGs = V.zipWith ME mods0 sideal
  gs :: STRef s (MV.MVector s (ModuleElement poly)) <- newSTRef =<< V.unsafeThaw preGs
  hs <- newSTRef $ Set.fromList [ Signature j lm
                                | j <- [0..n - 1]
                                , i <- [0..j - 1]
                                , let lm = leadingMonomial (sideal V.! i)
                                ]
  let preDecode :: JPair poly -> ModuleElement poly
      preDecode (JPair m i) = m .*! (preGs V.! i)
      {-# INLINE preDecode #-}
  jprs <- newSTRef $ H.fromList $
          Fl.fold Fl.nub
          [ Entry sig jpr
          | j <- [0..n - 1]
          , i <- [0..j - 1]
          , let qi = preGs V.! i
          , let qj = preGs V.! j
          , (sig, jpr) <- maybeToList $ jPair (i, qi) (j, qj)
          , let me = preDecode jpr
          , not $ any (`covers` me) preGs
          ]
  whileJust_ (H.viewMin <$> readSTRef jprs) $ \(Entry sig (JPair m0 i0), jprs') -> do
    writeSTRef jprs jprs'
    curGs <- V.unsafeFreeze =<< readSTRef gs
    hs0   <- readSTRef hs
    let me = m0 .*! (curGs V.! i0)
        next = any (`covers` me) curGs || any (`sigDivs` sig) hs0
    unless next $ do
      let me'@(ME t v) = reduceModuleElement me curGs
      if isZero v
        then modifySTRef' hs $ Set.insert t
        else do
        let k = V.length curGs
            decodeJpr :: JPair poly -> ModuleElement poly
            decodeJpr (JPair m i) | i == k = m .*! me'
                                  | otherwise = m .*! (curGs V.! i)
            {-# INLINE decodeJpr #-}
            syzs = V.foldl' (flip Set.insert) Set.empty $
                   V.mapMaybe (syzME me') curGs
        modifySTRef' hs (`Set.union` syzs)
        curHs <- readSTRef hs
        let newJprs = V.filter (\(Entry sg jp) -> not $ any (`covers` decodeJpr jp) curGs || any (`sigDivs` sg) curHs) $
                      V.imapMaybe (curry $ fmap (uncurry Entry) . jPair (k, me')) curGs
        modifySTRef' jprs $ H.union $ H.fromList $ nubBy ((==) `on` priority) $ V.toList newJprs
        append gs me'
  V.map (\(ME u v) -> (u, v)) <$> (V.unsafeFreeze =<< readSTRef gs)

append :: STRef s (MV.MVector s a) -> a -> ST s ()
append mv a = do
  g <- readSTRef mv
  let n = MV.length g
  g' <- MV.unsafeGrow g 1
  MV.write g' n a
  writeSTRef mv g'
{-# INLINE append #-}

jPair :: (IsOrderedPolynomial poly, Field (Coefficient poly))
      => (Int, ModuleElement poly)
      -> (Int, ModuleElement poly)
      -> Maybe (Signature poly, JPair poly)
jPair (i, p1@(ME u1 v1)) (j, p2@(ME u2 v2)) = do
  let (lc1, lm1) = leadingTerm v1
      (lc2, lm2) = leadingTerm v2
      t = lcmMonomial lm1 lm2
      t1 = t / lm1
      t2 = t / lm2
  let jSig1 = t1 .*! u1
  let jSig2 = t2 .*! u2
  if  jSig1 >= jSig2
    then loop i jSig1 (lc1 / lc2) t1 p1 t2 p2
    else loop j jSig2 (lc2 / lc1) t2 p2 t1 p1
  where
    {-# INLINE loop #-}
    loop k sig c t1 w1 t2 w2 = do
      sgn <- cancelModuleElement (t1 .*! w1) (Just c) (t2 .*! w2)
      guard $ sig == syzSign sgn
      return (sig, JPair t1 k)
{-# INLINE jPair #-}

data Signature poly =
  Signature { position :: {-# UNPACK #-} !Int
            , sigMonom :: !(OrderedMonomial (MOrder poly) (Arity poly))
            }

instance (Show (Coefficient poly), KnownNat (Arity poly)) => Show (Signature poly) where
  showsPrec _ (Signature pos m) =
    showChar '('  . showChar ' ' . shows m . showChar ')' . showChar 'e' . shows pos

instance Eq (Signature poly) where
  Signature i m == Signature j n = i == j && n == m

instance IsOrderedPolynomial poly => Ord (Signature poly) where
  compare (Signature i m) (Signature j n) = compare i j <> compare m n

basis :: IsOrderedPolynomial a => Int -> Signature a
basis i = Signature i one
{-# INLINE basis #-}

reduceModuleElement :: (IsOrderedPolynomial poly,
                        Field (Coefficient poly), Functor t, Foldable t)
                    => ModuleElement poly -> t (ModuleElement poly)
                    -> ModuleElement poly
reduceModuleElement p qs = loop p
  where
    loop !r =
      case getFirst $ foldMap (First . regularTopReduce r) qs of
        Nothing -> r
        Just r' -> loop r'
{-# INLINE reduceModuleElement #-}

regularTopReduce :: (IsOrderedPolynomial poly, Field (Coefficient poly))
                 => ModuleElement poly -> ModuleElement poly
                 -> Maybe (ModuleElement poly)
regularTopReduce p1@(ME u1 v1) p2@(ME u2 v2) = do
  guard $ not (isZero v2 || isZero v1) && leadingMonomial v2 `divs` leadingMonomial v1
  let (c, t) = tryDiv (leadingTerm v1) (leadingTerm v2)
  guard $ (t .*! u2) <= u1
  p <- cancelModuleElement p1 (Just c) (t .*! p2)
  guard $ syzSign p == syzSign p1
  return p

cancelModuleElement :: (Field (Coefficient poly), IsOrderedPolynomial poly)
                    => ModuleElement poly
                    -> Maybe (Coefficient poly)
                    -> ModuleElement poly -> Maybe (ModuleElement poly)
cancelModuleElement (ME u1 v1) mc (ME u2 v2) =
  let c = fromMaybe one mc
      v' = v1 - c .*. v2
  in case compare u1 u2 of
    LT -> do
      guard $ not $ isZero c
      return $ ME u2 (recip c .*. v')
    GT -> return $ ME u1 v'
    EQ -> do
      guard $ c /= one
      return $ ME u1 (recip (one - c) .*. v')
{-# INLINE cancelModuleElement #-}

syzME :: (Field (Coefficient poly), IsOrderedPolynomial poly)
      => ModuleElement poly -> ModuleElement poly -> Maybe (Signature poly)
syzME (ME u1 v1) (ME u2 v2) =
  case comparing position u1 u2 of
    LT -> Just (leadingMonomial v1 .*! u2)
    GT -> Just (leadingMonomial v2 .*! u1)
    EQ -> do
      let f = sigMonom u1 >* v2 - sigMonom u2 >* v1
      guard $ not $ isZero f
      return $ Signature (position u1) $ leadingMonomial f

sigDivs :: IsOrderedPolynomial poly => Signature poly -> Signature poly -> Bool
sigDivs (Signature i n) (Signature j m) = i == j && n `divs` m
{-# INLINE sigDivs #-}

covers :: (IsOrderedPolynomial poly)
       => ModuleElement poly -> ModuleElement poly -> Bool
covers (ME sig2 v2) (ME sig1 v1) = fromMaybe False $ do
  let t = sigMonom sig1 / sigMonom sig2
  return $ sig2 `sigDivs` sig1 && (isZero v2 || t * leadingMonomial v2 < leadingMonomial v1)
{-# INLINE covers #-}
