{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction      #-}
{-# LANGUAGE ParallelListComp, PolyKinds, QuasiQuotes, RankNTypes  #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TypeFamilies #-}
{-# LANGUAGE TypeOperators, UndecidableInstances                   #-}
module Algebra.Field.Galois (GF'(), IsGF', modPoly, modVec,
                             withIrreducible, linearRepGF, linearRepGF',
                             reifyGF', generateIrreducible,
                             withGF', GF, ConwayPolynomial(..),
                             Conway, primitive, conway,
                             conwayFile, addConwayPolynomials)  where
import Algebra.Field.Galois.Conway
import Algebra.Field.Prime
import Algebra.Internal
import Algebra.Prelude.Core               hiding (varX)
import Algebra.Ring.Polynomial.Univariate

import           Control.Lens                 (imap)
import           Control.Monad                (replicateM)
import           Control.Monad.Loops          (iterateUntil)
import           Control.Monad.Random         (MonadRandom)
import           Control.Monad.Random         (uniform)
import qualified Data.Foldable                as F
import           Data.Kind                    (Type)
import qualified Data.Ratio                   as Rat
import           Data.Reflection              (Reifies (..), reify)
import           Data.Singletons.Prelude.Enum (SEnum (..))
import           Data.Singletons.TypeLits     (withKnownNat)
import qualified Data.Sized.Builtin           as SV
import qualified Data.Traversable             as T
import qualified Data.Vector                  as V
import qualified GHC.TypeLits                 as TL
import qualified Numeric.Algebra              as NA
import           Numeric.Domain.Euclidean     (Euclidean)
import           Numeric.Domain.GCD           (GCDDomain, gcd)
import           Numeric.Semiring.ZeroProduct (ZeroProductSemiring)
import qualified Prelude                      as P

-- | Galois field of order @p^n@.
--   @f@ stands for the irreducible polynomial over @F_p@ of degree @n@.
newtype GF' p (n :: TL.Nat) (f :: Type) = GF' { runGF' :: Sized n (F p) }
deriving instance Reifies p Integer => Eq (GF' p n f)

-- | Galois Field of order @p^n@. This uses conway polynomials
--   as canonical minimal polynomial and it should be known at
--   compile-time (i.e. @Reifies (Conway p n) (Unipol (F n))@
--   instances should be defined to use field operations).
type GF (p :: TL.Nat) n = GF' p n (Conway p n)

modPoly :: forall p n f. (KnownNat n, Reifies p Integer) => Unipol (F p) -> GF' p n f
modPoly = GF' . polyToVec

modVec :: Sized n (F p) -> GF' p n f
modVec = GF'

instance (Reifies p Integer, Show (F p)) => Show (GF' p n f)  where
  showsPrec d (GF' (v :< vs)) =
    if F.all isZero vs
    then showsPrec d v
    else showChar '<' . showString (showPolynomialWith (singleton "ξ") 0 $ vecToPoly $ v :< vs) . showChar '>'
  showsPrec _ _ = showString "0"

instance (Reifies p Integer, Show (F p)) => PrettyCoeff (GF' p n f)

varX :: CoeffRing r => Unipol r
varX = var [od|0|]

vecToPoly :: (CoeffRing r)
          => Sized n r -> Unipol r
vecToPoly v = sum $ imap (\i c -> injectCoeff c * varX^fromIntegral i) $ F.toList v

polyToVec :: forall n r. (CoeffRing r, KnownNat n) => Unipol r -> Sized n r
polyToVec f = unsafeFromList' [ coeff (leadingMonomial $ (varX ^ i) `asTypeOf` f) f
                              | i <- [0..fromIntegral (fromSing (sing :: SNat n))]]

instance Reifies p Integer => Additive (GF' p n f)  where
  GF' v + GF' u = GF' $ SV.zipWithSame (+) v u

instance (Reifies p Integer, KnownNat n) => Monoidal (GF' p n f) where
  zero = GF' $ SV.replicate' zero

instance Reifies p Integer => LeftModule Natural (GF' p n f) where
  n .* GF' v = GF' $ SV.map (n .*) v

instance Reifies p Integer => RightModule Natural (GF' p n f) where
  GF' v *. n = GF' $ SV.map (*. n) v

instance Reifies p Integer => LeftModule Integer (GF' p n f) where
  n .* GF' v = GF' $ SV.map (n .*) v

instance Reifies p Integer => RightModule Integer (GF' p n f) where
  GF' v *. n = GF' $ SV.map (*. n) v

instance (KnownNat n, Reifies p Integer) => Group (GF' p n f) where
  negate (GF' v) = GF' $ SV.map negate v
  GF' u - GF' v  = GF' $ SV.zipWithSame (-) u v

instance (Reifies p Integer) => Abelian (GF' p n f)

instance (KnownNat n, Reifies f (Unipol (F p)), Reifies p Integer)
      => Multiplicative (GF' p n f) where
  GF' u * GF' v =
    let t = (vecToPoly u * vecToPoly v) `rem` reflect (Proxy :: Proxy f)
    in GF' $ polyToVec t

instance (KnownNat n, Reifies f (Unipol (F p)), Reifies p Integer) => Unital (GF' p n f) where
  one =
    case zeroOrSucc (sing :: SNat n) of
      IsZero   -> GF' NilL
      IsSucc k -> withKnownNat k $ GF' $ one :< SV.replicate' zero

instance (KnownNat n, Reifies f (Unipol (F p)), Reifies p Integer) => Semiring (GF' p n f)

instance (KnownNat n, Reifies f (Unipol (F p)), Reifies p Integer) => Rig (GF' p n f) where
  fromNatural n =
    case zeroOrSucc (sing :: SNat n) of
      IsZero -> GF' SV.empty
      IsSucc k -> withKnownNat k $ GF' $ fromNatural n :< SV.replicate' zero

instance (KnownNat n, Reifies f (Unipol (F p)), Reifies p Integer) => Commutative (GF' p n f)

instance (KnownNat n, Reifies f (Unipol (F p)), Reifies p Integer) => Ring (GF' p n f) where
  fromInteger n =
    case zeroOrSucc (sing :: SNat n) of
      IsZero   -> GF' NilL
      IsSucc k -> withKnownNat k $ GF' $ fromInteger n :< SV.replicate' zero

instance (KnownNat n, Reifies p Integer) => DecidableZero (GF' p n f) where
  isZero (GF' sv) = F.all isZero sv

instance (KnownNat n, Reifies p Integer, Reifies f (Unipol (F p))) => DecidableUnits (GF' p n f) where
  isUnit (GF' sv) = not $ F.all isZero sv
  recipUnit a | isZero a = Nothing
              | otherwise = Just $ recip a

instance (Reifies p Integer, Reifies f (Unipol (F p)), KnownNat n)
      => Characteristic (GF' p n f) where
  char _ = char (Proxy :: Proxy (F p))

instance (Reifies p Integer, Reifies f (Unipol (F p)), KnownNat n)
      => Division (GF' p n f) where
  recip f =
    let p = reflect (Proxy :: Proxy f)
        (_,_,r) = P.head $ euclid p $ vecToPoly $ runGF' f
    in GF' $ polyToVec $ r `rem` p

instance (KnownNat n, Reifies p Integer, Reifies f (Unipol (F p)))
      => DecidableAssociates (GF' p n f) where
  isAssociate p n =
    (isZero p && isZero n) || (not (isZero p) && not (isZero n))
instance (KnownNat n, Reifies p Integer, Reifies f (Unipol (F p)))
      => ZeroProductSemiring (GF' p n f)
instance (KnownNat n, Reifies p Integer, Reifies f (Unipol (F p)))
      => UnitNormalForm (GF' p n f)
instance (KnownNat n, Reifies p Integer, Reifies f (Unipol (F p)))
      => IntegralDomain (GF' p n f)
instance (KnownNat n, Reifies p Integer, Reifies f (Unipol (F p)))
      => GCDDomain (GF' p n f)
instance (KnownNat n, Reifies p Integer, Reifies f (Unipol (F p)))
      => UFD (GF' p n f)
instance (KnownNat n, Reifies p Integer, Reifies f (Unipol (F p)))
      => PID (GF' p n f)
instance (KnownNat n, Reifies p Integer, Reifies f (Unipol (F p)))
      => Euclidean (GF' p n f)

instance (Reifies p Integer, Reifies f (Unipol (F p)), KnownNat n) => P.Num (GF' p n f) where
  (+) = (NA.+)
  (-) = (NA.-)
  negate = NA.negate
  (*) = (NA.*)
  fromInteger = NA.fromInteger
  abs = error "not defined"
  signum = error "not defined"

instance (Reifies p Integer, Reifies f (Unipol (F p)), KnownNat n) => P.Fractional (GF' p n f) where
  fromRational u = fromInteger (Rat.numerator u) / fromInteger (Rat.denominator u)
  (/) = (/)
  recip = recip

-- | @generateIrreducible p n@ generates irreducible polynomial over F_@p@ of degree @n@.
generateIrreducible :: (MonadRandom m, FiniteField k, Eq k)
                    => proxy k -> Natural -> m (Unipol k)
generateIrreducible p n =
  iterateUntil (\f -> all (\i -> one == gcd (varX^(order p^i) - varX) f ) [1.. n `div` 2]) $ do
    cs <- replicateM (fromIntegral n) $ uniform (elements p)
    let f = varX^n + sum [ injectCoeff c * (varX^i) | c <- cs | i <- [0..n P.- 1]]
    return f

withIrreducible :: forall p a. KnownNat p
                => Unipol (F p)
                -> (forall f (n :: Nat). (Reifies f (Unipol (F p))) => Proxy (GF' p n f) -> a)
                -> a
withIrreducible r f =
  case toSing (fromIntegral $ totalDegree' r) of
    SomeSing sn ->
      withKnownNat sn $
      reify r (f. proxyGF' (Proxy :: Proxy (F n)) sn)

reifyGF' :: MonadRandom m => Natural -> Natural
         -> (forall (p :: TL.Nat) (f :: Type) (n :: TL.Nat) . (Reifies p Integer, Reifies f (Unipol (F p)))
                       => Proxy (GF' p n f) -> a)
         -> m a
reifyGF' p n f = reifyPrimeField (P.toInteger p) $ \pxy -> do
  mpol <- generateIrreducible pxy n
  case toSing (fromIntegral p) of
    SomeSing sp -> return $ withKnownNat sp $ withIrreducible mpol f

linearRepGF :: GF' p n f -> V.Vector (F p)
linearRepGF = SV.unsized . runGF'

linearRepGF' :: GF' p n f -> V.Vector Integer
linearRepGF' = V.map naturalRepr . linearRepGF

withGF' :: MonadRandom m
        => Natural -> Natural
        -> (forall (p :: TL.Nat) f (n :: TL.Nat) . (Reifies p Integer, Reifies f (Unipol (F p)))
            => GF' p n f)
        -> m (V.Vector Integer)
withGF' p n f = reifyGF' p n $ V.map naturalRepr . linearRepGF . asProxyTypeOf f

proxyGF' :: Proxy (F p) -> SNat n -> Proxy f -> Proxy (GF' p n f)
proxyGF' _ _ Proxy = Proxy

-- | Type-constraint synonym to work with Galois field.
class (KnownNat n, KnownNat p, Reifies f (Unipol (F p))) => IsGF' p n f
instance (KnownNat n, KnownNat p, Reifies f (Unipol (F p))) => IsGF' p n f


instance (KnownNat n, IsGF' p n f) => ZeroProductSemiring (GF' p n f)

instance (KnownNat n, IsGF' p n f) => FiniteField (GF' p n f) where
  power _ = fromIntegral $ fromSing (sing :: SNat n)
  elements _ =
    let sn = sing :: SNat n
    in P.map GF' $ T.sequence $
       SV.replicate sn $ elements Proxy

primitive :: forall p n f. (IsGF' p n f) => GF' p (n + 1) f
primitive = withKnownNat (sSucc (sing :: SNat n)) $ GF' $ polyToVec $ var [od|0|]

-- | Conway polynomial (if definition is known).
conway :: forall p n. ConwayPolynomial p n
       => SNat p -> SNat n -> Unipol (F p)
conway = conwayPolynomial
