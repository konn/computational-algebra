{-# LANGUAGE DeriveFunctor, DeriveTraversable, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables, ViewPatterns                            #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Algebra.Algorithms.Groebner.Signature (f5) where
import           Algebra.Prelude.Core hiding (Vector)
import           Control.Arrow        (second)
import           Control.Lens
import           Control.Monad.Loops
import           Control.Monad.ST
import qualified Data.Coerce          as DC
import           Data.Heap            (Entry (..))
import qualified Data.Heap            as H
import           Data.Maybe           (fromJust)
import           Data.Monoid          (First (..))
import           Data.Semigroup       hiding (First, getFirst, (<>))
import qualified Data.Sized.Builtin   as SV
import           Data.STRef
import qualified Data.Vector          as V
import qualified Data.Vector.Generic  as GV

mkEntry :: (KnownNat s, IsOrderedPolynomial poly)
        => Vector s poly -> Entry (Signature s poly) (Vector s poly)
mkEntry = Entry <$> signature <*> id

f5 :: (IsOrderedPolynomial a, Field (Coefficient a))
   => Ideal a -> [a]
f5 ideal =
  case SV.toSomeSized $ V.fromList $ generators ideal of
    SV.SomeSized s sideal -> map snd $ withKnownNat s $ calcSignatureGB (Vector sideal)

calcSignatureGB :: forall s poly.
                   (KnownNat s, Field (Coefficient poly), IsOrderedPolynomial poly)
                => Vector s poly -> [(Vector s poly, poly)]
calcSignatureGB side | null side = []
calcSignatureGB (fmap monoize -> sideal) = runST $ do
  gs <- newSTRef []
  ps <- newSTRef $ H.fromList [ mkEntry $ basis i | i <- [0..]]
  syzs <- newSTRef [ mkEntry (negate (sideal %!! j) .*. basis i + (sideal %!! i) .*. basis j)
                   | j <- [0..]
                   , i <- map toEnum [0..fromEnum j - 1]
                   ]
  whileJust_ (H.viewMin <$> readSTRef ps) $ \(Entry gSig g, ps') -> do
    writeSTRef ps ps'
    gs0 <- readSTRef gs
    ss0 <- readSTRef syzs
    unless (standardCriterion gSig ss0 || any ((== gSig) . priority . snd) gs0) $ do
      let h = reduceSignature sideal g gs0
          ph = phi h
          h' = fmap (* injectCoeff (recip $ leadingCoeff ph)) h
      if isZero ph
        then modifySTRef' syzs (mkEntry h : )
        else do
        modifySTRef' ps $ H.union $ H.fromList $
          mapMaybe (fmap mkEntry . flip regularSVector (monoize ph, h') . second payload) gs0
        modifySTRef' gs ((monoize ph, mkEntry h') :)

  map (\ (p, Entry _ a) -> (a, p)) <$> readSTRef gs
  where
    phi = dot sideal

regularSVector :: (KnownNat s, IsOrderedPolynomial poly)
               => (poly, Vector s poly)
               -> (poly, Vector s poly)
               -> Maybe (Vector s poly)
regularSVector (pg, g) (ph, h) =
  let l = lcmMonomial (leadingMonomial pg) (leadingMonomial ph)
      vl = fmap (l / leadingMonomial pg >*) g
      vr = fmap (l / leadingMonomial ph >*) h
  in if signature vl /= signature vr
  then Just $ vl - vr
  else Nothing

standardCriterion :: (KnownNat s, IsOrderedPolynomial poly, Foldable t)
                  => Signature s poly -> t (Entry (Signature s poly) (Vector s poly))
                  -> Bool
standardCriterion g = any ((`divSig` g) . priority)

divSig :: Signature s poly -> Signature s poly -> Bool
divSig (Signature i _ c) (Signature j _ d) =
  i == j && c `divs` d

data Signature (s :: Nat) poly =
  Signature { _position :: {-# UNPACK #-} !Int
            , _sigCoeff :: Coefficient poly
            , _sigMonom :: OrderedMonomial (MOrder poly) (Arity poly)
            }

instance (Show (Coefficient poly), KnownNat (Arity poly), KnownNat s) => Show (Signature s poly) where
  showsPrec _ (Signature pos coe m) =
    showChar '('  . shows coe . showChar ' ' . shows m . showChar ')' . showChar 'e' . shows pos

instance Eq (Signature s poly) where
  Signature i _ m == Signature j _ n = i == j && n == m

instance IsOrderedPolynomial poly => Ord (Signature s poly) where
  compare (Signature i _ m) (Signature j _ n) = compare i j <> compare m n

(%!!) :: Vector n c -> Ordinal n -> c
Vector v %!! i = v SV.%!! i

signature :: (KnownNat s, IsOrderedPolynomial poly)
          => Vector s poly
          -> Signature s poly
signature = fromJust . DC.coerce
          . ifoldMap (\i v -> Option $ do
                         let lt =  leadingTerm v
                         guard $ not $ isZero $ fst lt
                         return $ Max $ uncurry (Signature i) lt
                     )

newtype Vector n a = Vector { runVector :: Sized n a }
                   deriving ( Show, Eq, Ord
                            , Functor, Traversable, Foldable
                            )

instance FoldableWithIndex Int (Vector n) where
  ifoldMap f = ifoldMap f . SV.unsized . runVector

type instance GV.Mutable (Vector n) = GV.Mutable V.Vector

instance Additive a => Additive (Vector n a) where
  Vector a + Vector b = Vector $ zipWithSame (+) a b

instance LeftModule Natural a => LeftModule Natural (Vector n a) where
  n .* Vector a = Vector $ fmap (n.*) a

instance RightModule Natural a => RightModule Natural (Vector n a) where
  Vector a *. n = Vector $ fmap (*.n) a

instance LeftModule Integer a => LeftModule Integer (Vector n a) where
  n .* Vector a = Vector $ fmap (n.*) a

instance RightModule Integer a => RightModule Integer (Vector n a) where
  Vector a *. n = Vector $ fmap (*.n) a

instance (KnownNat n, Monoidal a) => Monoidal (Vector n a) where
  zero = Vector $ SV.replicate' zero

instance (KnownNat n, Group a) => Group (Vector n a) where
  negate = Vector . fmap negate . runVector
  Vector v - Vector u = Vector $ zipWithSame (-) v u

instance (Semiring a, Multiplicative a) => LeftModule (Scalar a) (Vector n a) where
  Scalar r .* Vector v = Vector $ fmap (r*) v

instance (Semiring a, Multiplicative a) => RightModule (Scalar a) (Vector n a) where
  Vector v *. Scalar r = Vector $ fmap (*r) v

basis :: (Monoidal a, Unital a, KnownNat n) => Ordinal n -> Vector n a
basis i = Vector $ SV.generate sing $ \j -> if i == j then one else zero

reduceSignature :: (KnownNat s, IsOrderedPolynomial poly, Field (Coefficient poly), Foldable t)
                => Vector s poly -> Vector s poly
                -> t (poly, Entry (Signature s poly) (Vector s poly))
                -> Vector s poly
reduceSignature ideal g hs =
  fst $ flip (until (\(u, r) -> phi u == r)) (g, zero) $ \(u, r) ->
  let m = leadingTerm $ phi u - r
      tryCancel (hi', Entry _ hi) = First $ do
        let quo = fmap (toPolynomial (m `tryDiv` leadingTerm hi') *) hi
        guard $ (leadingMonomial hi' `divs` snd m) && (signature quo < signature u)
        return quo
  in case getFirst $ foldMap tryCancel hs of
    Nothing -> (u, r + toPolynomial m)
    Just d  -> (u - d, r)
  where
    phi = dot ideal

dot :: (Multiplicative c, Monoidal c) => Vector n c -> Vector n c -> c
dot xs = sum . zipWithSame (*) (runVector xs) . runVector
