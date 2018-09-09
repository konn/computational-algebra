{-# LANGUAGE ScopedTypeVariables, TypeApplications, ViewPatterns #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Algebra.Algorithms.Groebner.Signature (f5) where
import           Algebra.Prelude.Core         hiding (Vector)
import           Control.Lens                 hiding ((.=))
import           Control.Monad.Loops
import           Control.Monad.ST.Combinators
import qualified Data.Coerce                  as DC
import qualified Data.Foldable                as F
import qualified Data.Heap                    as H
import           Data.Maybe                   (fromJust)
import           Data.Semigroup               hiding (First, getFirst, (<>))
import qualified Data.Set                     as Set
import           Data.Vector                  (Vector)
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
  in V.toList $ V.map polElem $ calcSignatureGB  sideal

data ModuleElement poly = ME { syzElem :: !(Syzygy poly)
                             , polElem :: !poly
                             }
                        deriving (Read, Show, Eq, Ord)


data JPair poly = JPair { _jpTerm  :: !(OMonom poly)
                        , _jpIndex :: !Int
                        }

instance Monoidal a => Additive (Syzygy a) where
  Syzygy u + Syzygy u'
    | V.length u == V.length u' = Syzygy $ V.zipWith (+) u u'
    | otherwise = Syzygy $ V.generate (max (V.length u) (V.length u')) $ \i ->
        fromMaybe zero (u V.!? i) + fromMaybe zero (u' V.!? i)
  {-# INLINE (+) #-}

instance {-# OVERLAPPING #-}  Monoidal a => LeftModule Natural (Syzygy a) where
  n .* Syzygy u = Syzygy $ V.map (n .*) u
  {-# INLINE (.*) #-}

instance {-# OVERLAPPING #-} Monoidal a => RightModule Natural (Syzygy a) where
  Syzygy u *. n = Syzygy $ V.map (*. n) u
  {-# INLINE (*.) #-}

instance Monoidal a => Monoidal (Syzygy a) where
  zero = Syzygy V.empty
  {-# INLINE zero #-}

instance {-# OVERLAPPING #-} Group a => LeftModule Integer (Syzygy a) where
  n .* Syzygy u = Syzygy $ V.map (n .*) u
  {-# INLINE (.*) #-}

instance {-# OVERLAPPING #-} Group a => RightModule Integer (Syzygy a) where
  Syzygy u *. n = Syzygy $ V.map (*. n) u
  {-# INLINE (*.) #-}

instance Group a => Group (Syzygy a) where
  negate = Syzygy . V.map negate . runSyzygy
  {-# INLINE negate #-}

instance (Monoidal poly) => Additive (ModuleElement poly) where
  ME u v + ME u' v' = ME (u + u') (v + v')
  {-# INLINE (+) #-}

instance (Monoidal poly) => Monoidal (ModuleElement poly) where
  zero = ME zero zero
  {-# INLINE zero #-}

instance (Group poly) => Group (ModuleElement poly) where
  ME u1 v1 - ME u2 v2 = ME (u1 - u2) (v1 - v2)
  {-# INLINE (-) #-}

instance {-# OVERLAPPABLE #-} (Group poly)
      => LeftModule Integer (ModuleElement poly) where
  c .* ME u v = ME (c .* u) (c .* v)
  {-# INLINE (.*) #-}

instance {-# OVERLAPPABLE #-} (Group poly)
      => RightModule Integer (ModuleElement poly) where
  ME u v *. c = ME (u *. c) (v *. c)
  {-# INLINE (*.) #-}

instance {-# OVERLAPPABLE #-} (Monoidal poly)
      => LeftModule Natural (ModuleElement poly) where
  c .* ME u v = ME (c .* u) (c .* v)
  {-# INLINE (.*) #-}

instance {-# OVERLAPPABLE #-} (Monoidal poly)
      => RightModule Natural (ModuleElement poly) where
  ME u v *. c = ME (u *. c) (v *. c)
  {-# INLINE (*.) #-}

type OMonom p = OrderedMonomial (MOrder p) (Arity p)

class Multiplicative c => Action c a where
  (.*!) :: c -> a -> a

infixl 7 .*!

instance {-# OVERLAPPING #-} (Arity poly ~ k, MOrder poly ~ ord, IsOrderedPolynomial poly) =>
         Action (OrderedMonomial ord k) (ModuleElement poly) where
  m .*! ME u v = ME (m .*! u) (m .*! v)
  {-# INLINE (.*!) #-}

instance {-# OVERLAPPING #-}
         (r ~ Coefficient poly, Arity poly ~ k, MOrder poly ~ ord, IsOrderedPolynomial poly)
         => Action (r, OrderedMonomial ord k) (Syzygy poly) where
  t .*! Syzygy u = Syzygy $ V.map (toPolynomial t *) u
  {-# INLINE (.*!) #-}

instance {-# OVERLAPPING #-}
         (r ~ Coefficient poly, Arity poly ~ k, MOrder poly ~ ord, IsOrderedPolynomial poly)
         => Action (r, OrderedMonomial ord k) (ModuleElement poly) where
  (c, m) .*! ME u v = ME ((c, m) .*! u) (toPolynomial (c, m) * v)
  {-# INLINE (.*!) #-}

instance {-# OVERLAPPING #-} (Arity poly ~ k, MOrder poly ~ ord, IsOrderedPolynomial poly) =>
         Action (OrderedMonomial ord k) (Signature poly) where
  m .*! Signature i f = Signature i (m * f)
  {-# INLINE (.*!) #-}

instance {-# OVERLAPPING #-} (Arity poly ~ k, MOrder poly ~ ord, IsOrderedPolynomial poly) =>
         Action (OrderedMonomial ord k) (Syzygy poly) where
  m .*! Syzygy u = Syzygy $ V.map (m >*) u
  {-# INLINE (.*!) #-}

instance {-# OVERLAPPABLE #-}  (Arity poly ~ k, MOrder poly ~ ord, IsOrderedPolynomial poly) =>
         Action (OrderedMonomial ord k) poly where
  (.*!) = (>*)
  {-# INLINE (.*!) #-}

(*!) :: Multiplicative r => r -> Syzygy r -> Syzygy r
p *! Syzygy u = Syzygy $ V.map (p *) u
{-# INLINE (*!) #-}

newtype Syzygy r = Syzygy { runSyzygy :: Vector r }
  deriving (Read, Show, Eq, Ord)

calcSignatureGB :: forall poly.
                   (Field (Coefficient poly), IsOrderedPolynomial poly)
                => V.Vector poly -> V.Vector (ModuleElement poly)
calcSignatureGB side | all isZero side = V.empty
calcSignatureGB (V.map monoize . V.filter (not . isZero) -> sideal) = runST $ do
  let n = V.length sideal
      mods0 = V.generate n $ basis n
      preGs = V.zipWith ME mods0 sideal
  gs :: STRef s (MV.MVector s (ModuleElement poly)) <- newSTRef =<< V.unsafeThaw preGs
  hs <- newSTRef $ Set.fromList [ Signature @poly j lm
                                | j <- [0..n - 1]
                                , let lm = leadingMonomial (sideal V.! j)
                                ]
  let preDecode :: JPair poly -> ModuleElement poly
      preDecode (JPair m i) = m .*! (preGs V.! i)
      {-# INLINE preDecode #-}
  jprs <- newSTRef $ H.fromList $ nub
          [ Entry sig jpr
          | j <- [0..n - 1]
          , i <- [0..j  - 1]
          , let qi = ME (mods0 V.! i) (sideal V.! i)
          , let qj = ME (mods0 V.! j) (sideal V.! j)
          , (sig, jpr) <- maybeToList $ jPair qi qj
          , let me = preDecode jpr
          , all ((me /=) . (preGs V.!)) [0..n - 1]
          ]
  whileJust_ (H.viewMin <$> readSTRef jprs) $ \(Entry _ me0, jprs') -> do
    writeSTRef jprs jprs'
    curGs <- V.unsafeFreeze =<< readSTRef gs
    let decodeJpr :: JPair poly -> ModuleElement poly
        decodeJpr (JPair m i) = m .*! (curGs V.! i)
        {-# INLINE decodeJpr #-}
        me = decodeJpr me0
        next = me `elem` curGs
    unless next $ do
      let me'@(ME t v) = reduceModuleElement me curGs
      if isZero v
        then modifySTRef' hs $ Set.insert (sign t)
        else do
        let syzs = foldMap (\(ME tj vj) -> Set.singleton $ sign $ v *! tj - vj *! t) curGs
            newJprs = V.filter (not . (`F.elem` jprs')) $ V.mapMaybe (fmap (uncurry Entry) .jPair me') curGs
        modifySTRef' hs $ Set.union syzs
        modifySTRef' jprs $ H.union $ H.fromList $ nub $ V.toList newJprs
        append gs me'
  V.unsafeFreeze =<< readSTRef gs

append :: STRef s (MV.MVector s a) -> a -> ST s ()
append mv a = do
  g <- readSTRef mv
  let n = MV.length g
  g' <- MV.unsafeGrow g 1
  MV.write g' n a
  writeSTRef mv g'

jPair :: (IsOrderedPolynomial poly, Field (Coefficient poly))
      => ModuleElement poly
      -> ModuleElement poly
      -> Maybe (Signature poly, JPair poly)
jPair (ME u1 v1) (ME u2 v2) =
  let (lc1, lm1) = leadingTerm v1
      (lc2, lm2) = leadingTerm v2
      t = lcmMonomial lm1 lm2
      t1 = t / lm1
      t2 = t / lm2
      jSig1 = t1 .*! sign u1
      jSig2 = t2 .*! sign u2
  in if  jSig1 >= jSig2
  then loop jSig1 t1 u1 (lc1 / lc2) t2 u2
  else loop jSig2 t2 u2 (lc2 / lc1) t1 u1
  where
    loop sig t1 w1 c t2 w2 = do
      guard $ sig == sign (t1 .*! w1 -(c, t2) .*! w2)
      return (sig, JPair t1 (_position sig))

data Signature poly =
  Signature { _position :: {-# UNPACK #-} !Int
            , _sigMonom :: OrderedMonomial (MOrder poly) (Arity poly)
            }

instance (Show (Coefficient poly), KnownNat (Arity poly)) => Show (Signature poly) where
  showsPrec _ (Signature pos m) =
    showChar '('  . showChar ' ' . shows m . showChar ')' . showChar 'e' . shows pos

instance Eq (Signature poly) where
  Signature i m == Signature j n = i == j && n == m

instance IsOrderedPolynomial poly => Ord (Signature poly) where
  compare (Signature i m) (Signature j n) = compare i j <> compare m n

sign :: forall poly . (IsOrderedPolynomial poly)
     => Syzygy poly
     -> Signature poly
sign = {-# SCC "sign" #-}
            fromJust . DC.coerce
          . ifoldMap (\i v -> Option $ do
                         let (lc, lm) = leadingTerm v
                         guard $ not $ isZero lc
                         return $ Max $ Signature @poly i lm
                     )
          . runSyzygy

basis :: (Monoidal a, Unital a) => Int -> Int -> Syzygy a
basis len i = Syzygy $ V.generate len $ \j -> if i == j then one else zero

reduceModuleElement :: (IsOrderedPolynomial poly, Field (Coefficient poly), Functor t, Foldable t)
                    => ModuleElement poly -> t (ModuleElement poly)
                    -> ModuleElement poly
reduceModuleElement p qs =
  fromMaybe p $ iterateUntil isNothing (\r -> asum $ fmap (regularTopReduce r) qs) p

regularTopReduce :: (IsOrderedPolynomial poly, Field (Coefficient poly))
                 => ModuleElement poly -> ModuleElement poly
                 -> Maybe (ModuleElement poly)
regularTopReduce p1@(ME u1 v1) p2@(ME u2 v2) = do
  guard $ not (isZero v1) && leadingMonomial v1 `divs` leadingMonomial v2
  let (c, t) = tryDiv (leadingTerm v1) (leadingTerm v2)
  guard $ sign (t .*! u2) <= sign u1
  let p = p1 - (c, t) .*! p2
  guard $ sign (syzElem p) == sign (syzElem p1)
  return p
