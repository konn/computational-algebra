{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses, PolyKinds, RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
module Algebra.Field.Finite (F(), naturalRepr, reifyPrimeField, withPrimeField,
                             modNat, FiniteField(..), order) where
import           Algebra.NumberTheory.PrimeTest
import           Algebra.Wrapped
import           Data.Proxy
import qualified Data.Ratio                     as R
import           Data.Reflection
import qualified Data.Type.Natural              as TN
import           Numeric.Algebra                (Field)
import           Numeric.Algebra                (char)
import           Numeric.Algebra                (Natural)
import qualified Numeric.Algebra                as NA
import           Numeric.Decidable.Units
import           Numeric.Decidable.Zero
import           Numeric.Rig.Characteristic     (Characteristic)
import           Numeric.Semiring.Integral      (IntegralSemiring)

-- | Prime field of characteristic @p@. @p@ should be prime, and not statically checked.
newtype F (p :: k) = F { runF :: Natural }

naturalRepr :: F p -> Natural
naturalRepr = runF

instance Reifies p Natural => Show (F p) where
  showsPrec d n@(F p) = showsPrec d (p `mod` reflect n)

modNat :: forall p. Reifies p Natural => Natural -> F p
modNat i = F (i `mod` reflect (Proxy :: Proxy p))

reifyPrimeField :: Natural -> (forall (p :: *). Reifies p Natural => Proxy (F p) -> a) -> a
reifyPrimeField p f = reify p (\pxy -> f (proxyF pxy))

withPrimeField :: Natural -> (forall (p :: *). Reifies p Natural => F p) -> Natural
withPrimeField p f = reifyPrimeField p $ runF . asProxyTypeOf f

proxyF :: Proxy (a :: k) -> Proxy (F a)
proxyF = reproxy

-- instance Reifies p Int => Noetherian (F p)

instance Reifies p Natural => Eq (F p) where
  n == m = runF n `mod` reflect n == runF m `mod` reflect n

instance Reifies p Natural => Normed (F p) where
  type Norm (F p) = Natural
  norm n@(F p) = p `mod` reflect n
  liftNorm = F . (`mod` reflect (Proxy :: Proxy p))

instance Reifies p Natural => Num (F p) where
  fromInteger n = modNat $ fromInteger n
  F a + F b = modNat $ a + b
  F a - F b =
    let p = reflect (Proxy :: Proxy p)
    in modNat $ a + (p - (b `mod` p))
  negate c = modNat $ reflect c - runF c
  a * b = modNat $ runF a * runF b
  abs (F n) = modNat $ abs n
  signum (F n) = modNat $ signum n

pow :: (Integral a1, Reifies p Natural) => F p -> a1 -> F p
pow a n = modNat $ fromIntegral $ modPow (fromIntegral $ runF a :: Integer)
          (fromIntegral (reflect a :: Natural)) n

instance Reifies p Natural => NA.Additive (F p) where
  (+) = (+)

instance Reifies p Natural => NA.Multiplicative (F p) where
  (*) = (*)
  pow1p n p = pow n (p + 1)

instance Reifies p Natural => NA.Monoidal (F p) where
  zero = 0

instance Reifies p Natural => NA.LeftModule Natural (F p) where
  n .* p = fromIntegral n * p

instance Reifies p Natural => NA.RightModule Natural (F p) where
  p *. n = fromIntegral n * p

instance Reifies p Natural => NA.LeftModule Integer (F p) where
  n .* p = fromIntegral n * p

instance Reifies p Natural => NA.RightModule Integer (F p) where
  p *. n = fromIntegral n * p

instance Reifies p Natural => NA.Group (F p) where
  (-) = (-)
  negate = negate

instance Reifies p Natural => NA.Abelian (F p)

instance Reifies p Natural => NA.Semiring (F p)

instance Reifies p Natural => NA.Rig (F p) where
  fromNatural = fromInteger . toInteger

instance Reifies p Natural => NA.Ring (F p) where
  fromInteger = fromInteger

instance Reifies p Natural => NA.DecidableZero (F p) where
  isZero n@(F p) = p `mod` reflect n == 0

instance Reifies p Natural => NA.Unital (F p) where
  one = 1
  pow = pow

instance Reifies p Natural => IntegralSemiring (F p)

instance Reifies p Natural => DecidableUnits (F p) where
  isUnit = not . isZero
  recipUnit n
    | isZero n  = Nothing
    | otherwise = Just $ recip n

instance Reifies p Natural => NA.Division (F p) where
  recip = recip
  (/)   = (/)
  (^)   = pow

instance Reifies p Natural => Fractional (F p) where
  a / b = a * recip b
  fromRational r =
    modNat (fromInteger $ R.numerator r) * recip (modNat (fromInteger $ R.denominator r))
  recip 0 = error "divide by 0"
  recip n = pow n (reflect n - 2)

instance Reifies p Natural => NA.Commutative (F p)

instance Reifies p Natural => NA.Characteristic (F p) where
  char _ = fromIntegral $ reflect (Proxy :: Proxy p)

instance Reifies TN.Z Natural  where
  reflect _ = 0

instance Reifies n Natural => Reifies (TN.S n) Natural where
  reflect _ = 1 + reflect (Proxy :: Proxy n)

class (Field k, Characteristic k) => FiniteField k where
  power :: proxy k -> Natural
  elements :: proxy k -> [k]

instance Reifies p Natural => FiniteField (F p) where
  power _ = 1
  elements p = map F [0.. char p - 1]

order :: FiniteField k => proxy k -> Natural
order p = char p ^ power p
