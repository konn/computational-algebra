{-# LANGUAGE BangPatterns, DeriveAnyClass, DeriveGeneric, LambdaCase   #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TypeApplications #-}
{-# LANGUAGE ViewPatterns                                              #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Algebra.Algorithms.Groebner.Signature (f5) where
import           Algebra.Prelude.Core         hiding (Vector)
import           Control.Lens                 hiding ((.=))
import           Control.Monad.Loops          (whileJust_)
import           Control.Monad.ST.Combinators (ST, STRef, modifySTRef',
                                               newSTRef, readSTRef, runST,
                                               writeSTRef)
import qualified Data.Coerce                  as DC
import           Data.Hashable                (Hashable)
import qualified Data.HashTable.ST.Cuckoo     as HT
import qualified Data.Heap                    as H
import           Data.Maybe                   (fromJust)
import           Data.Monoid                  (First (..))
import           Data.Reflection              (Reifies (..), reify)
import           Data.Semigroup               hiding (First, getFirst, (<>))
import qualified Data.Set                     as Set
import           Data.Vector                  (Vector)
import qualified Data.Vector                  as V
import qualified Data.Vector.Mutable          as MV
import           GHC.Generics                 (Generic)

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

data ModuleElement n poly = ME { syzElem :: !(Syzygy n poly)
                               , polElem :: !poly
                               }
                          deriving (Read, Show, Eq, Ord)


data JPair poly = JPair { _jpTerm  :: !(OMonom poly)
                        , _jpIndex :: !Int
                        }
                deriving (Generic, Hashable)
deriving instance KnownNat (Arity poly) => Show (JPair poly)
deriving instance KnownNat (Arity poly) => Eq (JPair poly)

instance Monoidal a => Additive (Syzygy n a) where
  Syzygy u + Syzygy u' = Syzygy $ V.zipWith (+) u u'
  {-# INLINE (+) #-}

instance {-# OVERLAPPING #-}  Monoidal a => LeftModule Natural (Syzygy n a) where
  n .* Syzygy u = Syzygy $ V.map (n .*) u
  {-# INLINE (.*) #-}

instance {-# OVERLAPPING #-} Monoidal a => RightModule Natural (Syzygy n a) where
  Syzygy u *. n = Syzygy $ V.map (*. n) u
  {-# INLINE (*.) #-}

instance (Reifies n Integer, Monoidal a) => Monoidal (Syzygy n a) where
  zero = Syzygy $ V.replicate (fromInteger $ reflect @n Proxy) zero
  {-# INLINE zero #-}

instance {-# OVERLAPPING #-} Group a => LeftModule Integer (Syzygy n a) where
  n .* Syzygy u = Syzygy $ V.map (n .*) u
  {-# INLINE (.*) #-}

instance {-# OVERLAPPING #-} Group a => RightModule Integer (Syzygy n a) where
  Syzygy u *. n = Syzygy $ V.map (*. n) u
  {-# INLINE (*.) #-}

instance (Reifies n Integer, Group a) => Group (Syzygy n a) where
  negate = DC.coerce @(Vector a -> Vector a) $ V.map negate
  {-# INLINE negate #-}
  (-) = DC.coerce @(Vector a -> Vector a -> Vector a) $ V.zipWith (-)
  {-# INLINE (-) #-}

instance (Monoidal poly) => Additive (ModuleElement n poly) where
  ME u v + ME u' v' = ME (u + u') (v + v')
  {-# INLINE (+) #-}

instance (Reifies n Integer, Monoidal poly) => Monoidal (ModuleElement n poly) where
  zero = ME zero zero
  {-# INLINE zero #-}

instance (Reifies n Integer, Group poly) => Group (ModuleElement n poly) where
  ME u1 v1 - ME u2 v2 = ME (u1 - u2) (v1 - v2)
  {-# INLINE (-) #-}

instance {-# OVERLAPPABLE #-} (Group poly)
      => LeftModule Integer (ModuleElement n poly) where
  c .* ME u v = ME (c .* u) (c .* v)
  {-# INLINE (.*) #-}

instance {-# OVERLAPPABLE #-} (Group poly)
      => RightModule Integer (ModuleElement n poly) where
  ME u v *. c = ME (u *. c) (v *. c)
  {-# INLINE (*.) #-}

instance {-# OVERLAPPABLE #-} (Monoidal poly)
      => LeftModule Natural (ModuleElement n poly) where
  c .* ME u v = ME (c .* u) (c .* v)
  {-# INLINE (.*) #-}

instance {-# OVERLAPPABLE #-} (Monoidal poly)
      => RightModule Natural (ModuleElement n poly) where
  ME u v *. c = ME (u *. c) (v *. c)
  {-# INLINE (*.) #-}

type OMonom p = OrderedMonomial (MOrder p) (Arity p)

class Multiplicative c => Action c a where
  (.*!) :: c -> a -> a

infixl 7 .*!

instance {-# OVERLAPPING #-} (Arity poly ~ k, MOrder poly ~ ord, IsOrderedPolynomial poly) =>
         Action (OrderedMonomial ord k) (ModuleElement n poly) where
  m .*! ME u v = ME (m .*! u) (m .*! v)
  {-# INLINE (.*!) #-}

instance {-# OVERLAPPING #-}
         (r ~ Coefficient poly, Arity poly ~ k, MOrder poly ~ ord, IsOrderedPolynomial poly)
         => Action (r, OrderedMonomial ord k) (Syzygy n poly) where
  (.*!) = DC.coerce @((r, OrderedMonomial ord k) -> Vector poly -> Vector poly) $ V.map . (*) . toPolynomial
  {-# INLINE (.*!) #-}

instance {-# OVERLAPPING #-}
         (r ~ Coefficient poly, Arity poly ~ k, MOrder poly ~ ord, IsOrderedPolynomial poly)
         => Action (r, OrderedMonomial ord k) (ModuleElement n poly) where
  t .*! ME u v = ME (t .*! u) (toPolynomial t * v)
  {-# INLINE (.*!) #-}

instance {-# OVERLAPPING #-} (Arity poly ~ k, MOrder poly ~ ord, IsOrderedPolynomial poly) =>
         Action (OrderedMonomial ord k) (Signature n poly) where
  m .*! Signature i f = Signature i (m * f)
  {-# INLINE (.*!) #-}

instance {-# OVERLAPPING #-} (Arity poly ~ k, MOrder poly ~ ord, IsOrderedPolynomial poly) =>
         Action (OrderedMonomial ord k) (Syzygy n poly) where
  (.*!) = DC.coerce @(OrderedMonomial ord k -> Vector poly -> Vector poly) $ V.map . (>*)
  {-# INLINE (.*!) #-}

instance {-# OVERLAPPABLE #-}  (Arity poly ~ k, MOrder poly ~ ord, IsOrderedPolynomial poly) =>
         Action (OrderedMonomial ord k) poly where
  (.*!) = (>*)
  {-# INLINE (.*!) #-}

(*!) :: Multiplicative r => r -> Syzygy n r -> Syzygy n r
p *! Syzygy u = Syzygy $ V.map (p *) u
{-# INLINE (*!) #-}

newtype Syzygy n r = Syzygy { runSyzygy :: Vector r }
  deriving (Read, Show, Eq, Ord)

calcSignatureGB :: forall poly.
                   (Field (Coefficient poly), IsOrderedPolynomial poly)
                => V.Vector poly -> V.Vector (Vector poly, poly)
calcSignatureGB side | all isZero side = V.empty
calcSignatureGB (V.map monoize . V.filter (not . isZero) -> sideal) = runST $
  let n = V.length sideal
  in reify (toInteger n) $ \(Proxy :: Proxy n) -> do
  jpTable <- HT.new
  let mods0 = V.generate n basis
      preGs = V.zipWith ME mods0 sideal
      jprWithDefault calc jp = HT.lookup jpTable jp >>= \case
        Just v -> return v
        Nothing -> do
          let ans = calc jp
          HT.insert jpTable jp ans
          return ans

  gs :: STRef s (MV.MVector s (ModuleElement n poly)) <- newSTRef =<< V.unsafeThaw preGs
  hs <- newSTRef $ Set.fromList [ Signature j lm
                                | j <- [0..n - 1]
                                , i <- [0..j - 1]
                                , let lm = leadingMonomial (sideal V.! i)
                                ]
  let preDecode :: JPair poly -> ModuleElement n poly
      preDecode (JPair m i) = m .*! (preGs V.! i)
      {-# INLINE preDecode #-}
  jprs <- newSTRef . H.fromList . nubBy ((==) `on` priority) =<<
          filterM (\ (Entry _ pr) -> not . flip any preGs . flip covers <$> jprWithDefault preDecode pr)
          [ Entry sig jpr
          | j <- [0..n - 1]
          , i <- [0..j - 1]
          , let qi = preGs V.! i
          , let qj = preGs V.! j
          , (sig, jpr) <- maybeToList $ jPair (i, qi) (j, qj)
          ]
  whileJust_ (H.viewMin <$> readSTRef jprs) $ \(Entry sig (JPair m0 i0), jprs') -> do
    writeSTRef jprs jprs'
    curGs <- V.unsafeFreeze =<< readSTRef gs
    hs0   <- readSTRef hs
    let me = m0 .*! (curGs V.! i0)
        next = any (`covers` me) curGs || sig `elem` hs0
    unless next $ do
      let me'@(ME t v) = reduceModuleElement me curGs
      if isZero v
        then modifySTRef' hs $ Set.insert $ fromJust $ sign t
        else do
        let k = V.length curGs
            decodeJpr :: JPair poly -> ModuleElement n poly
            decodeJpr (JPair m i) | i == k = m .*! me'
                                  | otherwise = m .*! (curGs V.! i)
            {-# INLINE decodeJpr #-}
            syzs = foldMap (\(ME tj vj) -> maybe Set.empty Set.singleton $ sign $ v *! tj - vj *! t) curGs
        modifySTRef' hs (`Set.union` syzs)
        curHs <- readSTRef hs
        newJprs <- V.filterM (\(Entry sg jp) -> do
                                 pr <- jprWithDefault decodeJpr jp
                                 return $ not $ any (`covers` pr) curGs || sg `elem` curHs) $
                      V.imapMaybe (curry $ fmap (uncurry Entry) . jPair (k, me')) curGs
        modifySTRef' jprs $ H.union $ H.fromList $ nubBy ((==) `on` priority) $ V.toList newJprs
        append gs me'
  V.map (\(ME (Syzygy u) v) -> (u, v)) <$> (V.unsafeFreeze =<< readSTRef gs)

append :: STRef s (MV.MVector s a) -> a -> ST s ()
append mv a = do
  g <- readSTRef mv
  let n = MV.length g
  g' <- MV.unsafeGrow g 1
  MV.write g' n a
  writeSTRef mv g'

jPair :: (Reifies n Integer, IsOrderedPolynomial poly, Field (Coefficient poly))
      => (Int, ModuleElement n poly)
      -> (Int, ModuleElement n poly)
      -> Maybe (Signature n poly, JPair poly)
jPair (i, ME u1 v1) (j, ME u2 v2) = do
  let (lc1, lm1) = leadingTerm v1
      (lc2, lm2) = leadingTerm v2
      t = lcmMonomial lm1 lm2
      t1 = t / lm1
      t2 = t / lm2
  jSig1 <- (t1 .*!) <$> sign u1
  jSig2 <- (t2 .*!) <$> sign u2
  if  jSig1 >= jSig2
    then loop i jSig1 t1 u1 (lc1 / lc2) t2 u2
    else loop j jSig2 t2 u2 (lc2 / lc1) t1 u1
  where
    loop k sig t1 w1 c t2 w2 = do
      sgn <- sign (t1 .*! w1 - (c, t2) .*! w2)
      guard $ sig == sgn
      return (sig, JPair t1 k)

data Signature n poly =
  Signature { _position :: {-# UNPACK #-} !Int
            , _sigMonom :: OrderedMonomial (MOrder poly) (Arity poly)
            }

instance (Show (Coefficient poly), KnownNat (Arity poly)) => Show (Signature n poly) where
  showsPrec _ (Signature pos m) =
    showChar '('  . showChar ' ' . shows m . showChar ')' . showChar 'e' . shows pos

instance Eq (Signature n poly) where
  Signature i m == Signature j n = i == j && n == m

instance IsOrderedPolynomial poly => Ord (Signature n poly) where
  compare (Signature i m) (Signature j n) = compare i j <> compare m n

sign :: forall poly n . (Reifies n Integer, IsOrderedPolynomial poly)
     => Syzygy n poly
     -> Maybe (Signature n poly)
sign = {-# SCC "sign" #-}
            DC.coerce
          . ifoldMap (\i v -> Option $ do
                         let (lc, lm) = leadingTerm v
                         guard $ not $ isZero lc
                         return $ Max $ Signature @n @poly i lm
                     )
          . runSyzygy

basis :: forall a n. (Monoidal a, Unital a, Reifies n Integer) => Int -> Syzygy n a
basis i =
  let len = fromInteger $ reflect (Proxy :: Proxy n)
  in Syzygy $ V.generate len $ \j -> if i == j then one else zero

reduceModuleElement :: (Reifies n Integer, IsOrderedPolynomial poly,
                        Field (Coefficient poly), Functor t, Foldable t)
                    => ModuleElement n poly -> t (ModuleElement n poly)
                    -> ModuleElement n poly
reduceModuleElement p qs = loop p
  where
    loop !r =
      case getFirst $ foldMap (First . regularTopReduce r) qs of
        Nothing -> r
        Just r' -> loop r'
{-# INLINE reduceModuleElement #-}

regularTopReduce :: (Reifies n Integer, IsOrderedPolynomial poly, Field (Coefficient poly))
                 => ModuleElement n poly -> ModuleElement n poly
                 -> Maybe (ModuleElement n poly)
regularTopReduce p1@(ME u1 v1) p2@(ME u2 v2) = do
  guard $ not (isZero v2 || isZero v1) && leadingMonomial v2 `divs` leadingMonomial v1
  let (c, t) = tryDiv (leadingTerm v1) (leadingTerm v2)
  l <- sign (t .*! u2)
  r <- sign u1
  guard $ l <= r
  let p = p1 - (c, t) .*! p2
  guard $ sign (syzElem p) == sign (syzElem p1)
  return p

sigDivs :: IsOrderedPolynomial poly => Signature n poly -> Signature n poly -> Bool
sigDivs (Signature i n) (Signature j m) = i == j && n `divs` m

covers :: (IsOrderedPolynomial poly , Reifies n Integer)
       => ModuleElement n poly -> ModuleElement n poly -> Bool
covers (ME u2 v2) (ME u1 v1) = fromMaybe False $ do
  sig2@Signature{ _sigMonom = lm2 } <- sign u2
  sig1@Signature{ _sigMonom = lm1 } <- sign u1
  let t = lm1 / lm2
  return $ sig2 `sigDivs` sig1 && t * leadingMonomial v2 < leadingMonomial v1
