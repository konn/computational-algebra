{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses, PolyKinds, RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
module Algebra.Field.Finite (F(), withModulo, FiniteField(..), order) where
import           Algebra.Wrapped
import           Data.Proxy
import qualified Data.Ratio                 as R
import           Data.Reflection
import qualified Data.Type.Natural          as TN
import           Numeric.Algebra            (Field)
import           Numeric.Algebra            (char)
import qualified Numeric.Algebra            as NA
import           Numeric.Decidable.Units
import           Numeric.Decidable.Zero
import           Numeric.Rig.Characteristic (Characteristic)
import           Numeric.Semiring.Integral  (IntegralSemiring)

-- | @p@ should be prime, and not statically checked.
newtype F (p :: k) = F { runF :: NA.Natural }

instance Reifies p NA.Natural => Show (F p) where
  showsPrec d n@(F p) = showsPrec d (p `mod` reflect n)

withModulo :: forall p. Reifies p NA.Natural => NA.Natural -> F p
withModulo i = F (i `mod` reflect (Proxy :: Proxy p))

asProxyOf :: f a -> Proxy a -> f a
asProxyOf = const

{-
reifyMod :: Int -> (forall p. Reifies p Int => F p) -> Int
reifyMod p a = reify p (runF . asProxyOf a)
-}
-- instance Reifies p Int => Noetherian (F p)

instance Reifies p NA.Natural => Eq (F p) where
  n == m = runF n `mod` reflect n == runF m `mod` reflect n

instance Reifies p NA.Natural => Normed (F p) where
  type Norm (F p) = NA.Natural
  norm n@(F p) = p `mod` reflect n
  liftNorm = F . (`mod` reflect (Proxy :: Proxy p))

instance Reifies p NA.Natural => Num (F p) where
  fromInteger n = withModulo $ fromInteger n
  F a + F b = withModulo $ a + b
  F a - F b = withModulo $ a - b
  negate c = withModulo $ reflect c - runF c
  a * b = withModulo $ runF a * runF b
  abs (F n) = withModulo $ abs n
  signum (F n) = withModulo $ signum n

modPow :: (Integral a, Integral a1) => a -> a -> a1 -> a
modPow i p = go i 1
  where
    go _ acc 0 = acc
    go b acc e = go ((b*b) `mod` p) (if e `mod` 2 == 1 then (acc * b) `mod` p else acc) (e `div` 2)

pow :: (Integral a1, Reifies p NA.Natural) => F p -> a1 -> F p
pow a n = withModulo $ modPow (runF a) (reflect a) n

instance Reifies p NA.Natural => NA.Additive (F p) where
  (+) = (+)

instance Reifies p NA.Natural => NA.Multiplicative (F p) where
  (*) = (*)
  pow1p n p = pow n (p + 1)

instance Reifies p NA.Natural => NA.Monoidal (F p) where
  zero = 0

instance Reifies p NA.Natural => NA.LeftModule NA.Natural (F p) where
  n .* p = fromIntegral n * p

instance Reifies p NA.Natural => NA.RightModule NA.Natural (F p) where
  p *. n = fromIntegral n * p

instance Reifies p NA.Natural => NA.LeftModule Integer (F p) where
  n .* p = fromIntegral n * p

instance Reifies p NA.Natural => NA.RightModule Integer (F p) where
  p *. n = fromIntegral n * p

instance Reifies p NA.Natural => NA.Group (F p) where
  (-) = (-)
  negate = negate

instance Reifies p NA.Natural => NA.Abelian (F p)

instance Reifies p NA.Natural => NA.Semiring (F p)

instance Reifies p NA.Natural => NA.Rig (F p) where
  fromNatural = fromInteger . toInteger

instance Reifies p NA.Natural => NA.Ring (F p) where
  fromInteger = fromInteger

instance Reifies p NA.Natural => NA.DecidableZero (F p) where
  isZero n@(F p) = p `mod` reflect n == 0

instance Reifies p NA.Natural => NA.Unital (F p) where
  one = 1
  pow = pow

instance Reifies p NA.Natural => IntegralSemiring (F p)

instance Reifies p NA.Natural => DecidableUnits (F p) where
  isUnit = not . isZero
  recipUnit n
    | isZero n  = Nothing
    | otherwise = Just $ recip n

instance Reifies p NA.Natural => NA.Division (F p) where
  recip = recip
  (/)   = (/)
  (^)   = pow

instance Reifies p NA.Natural => Fractional (F p) where
  a / b = a * recip b
  fromRational r =
    withModulo (fromInteger $ R.numerator r) * recip (withModulo (fromInteger $ R.denominator r))
  recip 0 = error "divide by 0"
  recip n = pow n (reflect n - 2)

instance Reifies p NA.Natural => NA.Commutative (F p)

instance Reifies p NA.Natural => NA.Characteristic (F p) where
  char _ = fromIntegral $ reflect (Proxy :: Proxy p)

instance Reifies TN.Z NA.Natural  where
  reflect _ = 0

instance Reifies n NA.Natural => Reifies (TN.S n) NA.Natural where
  reflect _ = 1 + reflect (Proxy :: Proxy n)

class (Field k, Characteristic k) => FiniteField k where
  power :: proxy k -> NA.Natural
  elements :: proxy k -> [k]

instance Reifies p NA.Natural => FiniteField (F p) where
  power _ = 1
  elements p = map F [0.. char p - 1]

order :: FiniteField k => proxy k -> NA.Natural
order p = char p ^ power p
