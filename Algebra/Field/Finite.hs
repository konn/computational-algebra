{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses, PolyKinds, RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
module Algebra.Field.Finite (F(), withModulo) where
import           Algebra.Ring.Noetherian
import           Algebra.Wrapped
import           Data.Proxy
import           Data.Ratio
import           Data.Reflection
import qualified Data.Type.Natural       as TN
import qualified Numeric.Algebra         as NA

-- | @p@ should be prime, and not statically checked.
newtype F p = F { runF :: Int }

instance Reifies p Int => Show (F p) where
  showsPrec d n@(F p) = showsPrec d (p `mod` reflect n)

withModulo :: forall p. Reifies p Int => Int -> F p
withModulo i = F (i `mod` reflect (Proxy :: Proxy p))

asProxyOf :: f a -> Proxy a -> f a
asProxyOf = const

{-
reifyMod :: Int -> (forall p. Reifies p Int => F p) -> Int
reifyMod p a = reify p (runF . asProxyOf a)
-}
instance Reifies p Int => NoetherianRing (F p)

instance Reifies p Int => Eq (F p) where
  n == m = runF n `mod` reflect n == runF m `mod` reflect n

instance Reifies p Int => Normed (F p) where
  type Norm (F p) = Int
  norm n@(F p) = p `mod` reflect n
  liftNorm = F . (`mod` reflect (Proxy :: Proxy p))

instance Reifies p Int => Num (F p) where
  fromInteger n = F $ fromInteger n `mod` reflect (Proxy :: Proxy p)
  F a + F b = withModulo $ a + b
  F a - F b = withModulo $ a - b
  negate c = F $ reflect c - runF c
  a * b = withModulo $ runF a * runF b
  abs (F n) = withModulo $ abs n
  signum (F n) = withModulo $ signum n

modPow :: (Integral a, Integral a1) => a -> a -> a1 -> a
modPow i p = go i 1
  where
    go _ acc 0 = acc
    go b acc e = go ((b*b) `mod` p) (if e `mod` 2 == 1 then (acc * b) `mod` p else acc) (e `div` 2)

pow :: (Integral a1, Reifies p Int) => F p -> a1 -> F p
pow a n = withModulo $ modPow (runF a) (reflect a) n

instance Reifies p Int => NA.Additive (F p) where
  (+) = (+)

instance Reifies p Int => NA.Multiplicative (F p) where
  (*) = (*)
  pow1p n p = pow n (p + 1)

instance Reifies p Int => NA.Monoidal (F p) where
  zero = 0

instance Reifies p Int => NA.LeftModule NA.Natural (F p) where
  n .* p = fromIntegral n * p

instance Reifies p Int => NA.RightModule NA.Natural (F p) where
  p *. n = fromIntegral n * p

instance Reifies p Int => NA.LeftModule Integer (F p) where
  n .* p = fromIntegral n * p

instance Reifies p Int => NA.RightModule Integer (F p) where
  p *. n = fromIntegral n * p

instance Reifies p Int => NA.Group (F p) where
  (-) = (-)
  negate = negate

instance Reifies p Int => NA.Abelian (F p)

instance Reifies p Int => NA.Semiring (F p)

instance Reifies p Int => NA.Rig (F p) where
  fromNatural = fromInteger . toInteger

instance Reifies p Int => NA.Ring (F p) where
  fromInteger = fromInteger

instance Reifies p Int => NA.Unital (F p) where
  one = 1
  pow = pow

instance Reifies p Int => NA.Division (F p) where
  recip = recip
  (/)   = (/)
  (^)   = pow

instance Reifies p Int => Fractional (F p) where
  a / b = a * recip b
  fromRational r = withModulo (fromInteger $ numerator r) * recip (withModulo (fromInteger $ denominator r))
  recip 0 = error "divide by 0"
  recip n = pow n (reflect n - 2)

instance Reifies p Int => NA.Commutative (F p)

instance Reifies p Int => NA.Characteristic (F p) where
  char _ = fromIntegral $ reflect (Proxy :: Proxy p)

instance Reifies TN.Z Int  where
  reflect _ = 0

instance Reifies n Int => Reifies (TN.S n) Int where
  reflect _ = 1 + reflect (Proxy :: Proxy n)
