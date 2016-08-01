{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, NoMonomorphismRestriction        #-}
{-# LANGUAGE ParallelListComp, PolyKinds, RankNTypes, ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies, UndecidableInstances                             #-}
module Algebra.Field.Galois (GF0(), IsGF0, modPoly, modVec, reifyGF0,
                             withGF0, GF'(), Conway, primitive, conway,
                             conwayFile, addConwayPolynomials)  where
import           Algebra.Field.Finite
import           Algebra.Field.Galois.Conway
import           Algebra.Internal
import           Algebra.Prelude
import           Control.Lens                (imap)
import           Control.Monad               (replicateM)
import           Control.Monad.Loops         (iterateUntil)
import           Control.Monad.Random        (MonadRandom)
import           Control.Monad.Random        (uniform)
import qualified Data.Ratio                  as Rat
import           Data.Reflection
import           Data.Type.Monomorphic       (promote)
import           Data.Type.Monomorphic       (Monomorphic (..))
import           Data.Type.Natural           hiding (one, zero)
import qualified Data.Type.Natural           as TN
import qualified Data.Vector                 as V
import           Data.Vector.Sized           (Vector ((:-), Nil))
import qualified Data.Vector.Sized           as SV
import           Numeric.Decidable.Units
import           Numeric.Decidable.Zero
import           Numeric.Semiring.Integral   (IntegralSemiring)
import           Prelude                     hiding (Fractional (..), Num (..),
                                              gcd, quot, rem, sum, (^))
import qualified Prelude                     as P

-- | Galois field of order @p^n@.
--   @f@ stands for the irreducible polynomial over @F_p@ of degree @n@.
data GF0 p n f = GF0 { runGF0 :: SV.Vector (F p) n } deriving (Eq)
type Unipol a = OrderedPolynomial a Grevlex One

-- | Galois Field of order @p^n@. This uses conway polynomials
--   as canonical minimal polynomial and it should be known at
--   compile-time (i.e. @Reifies (Conway p n) (Unipol (F n))@
--   instances should be defined to use field operations).
type GF' p n = GF0 p n (Conway p n)

modPoly :: (SingI n, Reifies p Integer) => Unipol (F p) -> GF0 p n f
modPoly = GF0 . polyToVec

modVec :: Vector (F p) n -> GF0 p n f
modVec = GF0

instance (Reifies p Integer, Show (F p), SingI n) => Show (GF0 p n f)  where
  showsPrec _ (GF0 Nil) = showString "0"
  showsPrec d (GF0 (v :- vs)) =
    if SV.all isZero vs
    then showsPrec d v
    else showChar '<' . shows (vecToPoly $ v :- vs) . showChar '>'

vecToPoly :: (SingI n, CoeffRing r)
          => SV.Vector r n -> Unipol r
vecToPoly v = sum $ imap (\i c -> injectCoeff c * varX^fromIntegral i) $ SV.toList v

polyToVec :: forall n r. (CoeffRing r, SingI n) => Unipol r -> SV.Vector r n
polyToVec f = SV.unsafeFromList' [ coeff (leadingMonomial $ (varX ^ i) `asTypeOf` f) f
                                 | i <- [0..sNatToInt (sing :: SNat n)]]

instance Reifies p Integer => Additive (GF0 p n f)  where
  GF0 v + GF0 u = GF0 $ SV.zipWithSame (+) v u

instance (Reifies p Integer, SingI n) => Monoidal (GF0 p n f) where
  zero = GF0 $ SV.replicate' zero

instance Reifies p Integer => LeftModule Natural (GF0 p n f) where
  n .* GF0 v = GF0 $ SV.map (n .*) v

instance Reifies p Integer => RightModule Natural (GF0 p n f) where
  GF0 v *. n = GF0 $ SV.map (*. n) v

instance Reifies p Integer => LeftModule Integer (GF0 p n f) where
  n .* GF0 v = GF0 $ SV.map (n .*) v

instance Reifies p Integer => RightModule Integer (GF0 p n f) where
  GF0 v *. n = GF0 $ SV.map (*. n) v

instance (SingI n, Reifies p Integer) => Group (GF0 p n f) where
  negate (GF0 v) = GF0 $ SV.map negate v
  GF0 u - GF0 v  = GF0 $ SV.zipWithSame (-) u v

instance (SingI n, Reifies p Integer) => Abelian (GF0 p n f)

instance (SingI n, Reifies f (Unipol (F p)), Reifies p Integer)
      => Multiplicative (GF0 p n f) where
  GF0 u * GF0 v =
    let t = (vecToPoly u * vecToPoly v) `rem` reflect (Proxy :: Proxy f)
    in GF0 $ polyToVec t

instance (SingI n, Reifies f (Unipol (F p)), Reifies p Integer) => Unital (GF0 p n f) where
  one =
    case sing :: SNat n of
      SZ   -> GF0 Nil
      SS k -> withSingI k $ GF0 $ one :- SV.replicate' zero

instance (SingI n, Reifies f (Unipol (F p)), Reifies p Integer) => Semiring (GF0 p n f)

instance (SingI n, Reifies f (Unipol (F p)), Reifies p Integer) => Rig (GF0 p n f) where
  fromNatural n =
    case sing :: SNat n of
      SZ -> GF0 Nil
      SS k -> withSingI k $ GF0 $ fromNatural n :- SV.replicate' zero

instance (SingI n, Reifies f (Unipol (F p)), Reifies p Integer) => Commutative (GF0 p n f)

instance (SingI n, Reifies f (Unipol (F p)), Reifies p Integer) => Ring (GF0 p n f) where
  fromInteger n =
    case sing :: SNat n of
      SZ -> GF0 Nil
      SS k -> withSingI k $ GF0 $ fromInteger n :- SV.replicate' zero

instance (SingI n, Reifies p Integer) => DecidableZero (GF0 p n f) where
  isZero (GF0 sv) = SV.all isZero sv

instance (SingI n, Reifies p Integer, Reifies f (Unipol (F p))) => DecidableUnits (GF0 p n f) where
  isUnit (GF0 sv) = not $ SV.all isZero sv
  recipUnit a | isZero a = Nothing
              | otherwise = Just $ recip a

instance (Reifies p Integer, Reifies f (Unipol (F p)), SingI n)
      => Characteristic (GF0 p n f) where
  char _ = char (Proxy :: Proxy (F p))

instance (Reifies p Integer, Reifies f (Unipol (F p)), SingI n)
      => Division (GF0 p n f) where
  recip f =
    let p = reflect (Proxy :: Proxy f)
        (_,_,r) = head $ euclid p $ vecToPoly $ runGF0 f
    in GF0 $ polyToVec $ r `rem` p

instance (Reifies p Integer, Reifies f (Unipol (F p)), SingI n) => P.Num (GF0 p n f) where
  (+) = (+)
  (-) = (-)
  negate = negate
  (*) = (*)
  fromInteger = fromInteger
  abs = error "not defined"
  signum = error "not defined"

instance (Reifies p Integer, Reifies f (Unipol (F p)), SingI n) => P.Fractional (GF0 p n f) where
  fromRational u = fromInteger (Rat.numerator u) / fromInteger (Rat.denominator u)
  (/) = (/)
  recip = recip

-- | @generateIrreducible p n@ generates irreducible polynomial over F_@p@ of degree @n@.
generateIrreducible :: (DecidableZero k, MonadRandom m, FiniteField k,
                        IntegralSemiring k, DecidableUnits k, Eq k)
                    => proxy k -> Natural -> m (Unipol k)
generateIrreducible p n =
  iterateUntil (\f -> all (\i -> one == gcd (varX^(order p^i) - varX) f ) [1.. n `div` 2]) $ do
    cs <- replicateM (fromIntegral n) $ uniform (elements p)
    let f = varX^n + sum [ injectCoeff c * (varX^i) | c <- cs | i <- [0..]]
    return f

reifyGF0 :: MonadRandom m => Natural -> Natural
         -> (forall (p :: *) (f :: *) (n :: Nat) . (Reifies p Integer, Reifies f (Unipol (F p)), SingI n)
             => Proxy (GF0 p n f) -> a)
         -> m a
reifyGF0 p n f = reifyPrimeField (toInteger p) $ \pxy -> do
  mpol <- generateIrreducible pxy n
  case promote (fromIntegral n) of
    Monomorphic sn ->
      case singInstance sn of
        TN.SingInstance -> return $ reify mpol (f . proxyGF0 pxy sn)

withGF0 :: MonadRandom m
        => Natural -> Natural
        -> (forall (p :: *) (f :: *) (n :: Nat) . (Reifies p Integer, Reifies f (Unipol (F p)), SingI n)
            => GF0 p n f)
        -> m (V.Vector Integer)
withGF0 p n f = reifyGF0 p n $ V.fromList . SV.toList . SV.map naturalRepr . runGF0 . asProxyTypeOf f

proxyGF0 :: Proxy (F p) -> SNat n -> Proxy f -> Proxy (GF0 p n f)
proxyGF0 _ _ Proxy = Proxy

-- | Type-constraint synonym to work with Galois field.
class (SingI n, Reifies p Integer, Reifies f (Unipol (F p))) => IsGF0 p n f
instance (SingI n, Reifies p Integer, Reifies f (Unipol (F p))) => IsGF0 p n f


instance (IsGF0 p n f) => IntegralSemiring (GF0 p n f)

instance IsGF0 p n f => FiniteField (GF0 p n f) where
  power _ = sNatToInt (sing :: SNat n)
  elements _ = map (GF0 . SV.unsafeFromList') $ sequence $
               replicate (sNatToInt (sing :: SNat n)) $ elements Proxy

primitive :: (IsGF0 p n f) => GF0 p ('S n) f
primitive = GF0 $ polyToVec varX

-- | Conway polynomial (if definition is known).
conway :: forall p n. (Reifies (Conway p n) (Unipol (F p)))
       => SNat p -> SNat n -> Unipol (F p)
conway _ _ = reflect (Proxy :: Proxy (Conway p n))
