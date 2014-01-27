{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, UndecidableInstances      #-}
module Algebra.Field.Finite where
import           Data.Proxy
import           Data.Ratio
import           Data.Reflection
import qualified Numeric.Algebra as NA

-- | @p@ should be prime, and not statically checked.
newtype Finite p = Finite { runFinite :: Int }

instance Reifies p Int => Show (Finite p) where
  showsPrec d n@(Finite p) = showsPrec d (p `mod` reflect n)

withModulo :: forall p. Reifies p Int => Int -> Finite p
withModulo i = Finite (i `mod` reflect (Proxy :: Proxy p))

asProxyOf :: f a -> Proxy a -> f a
asProxyOf = const

reifyMod :: Int -> (forall p. Reifies p Int => Finite p) -> Int
reifyMod p a = reify p (runFinite . asProxyOf a)

instance Reifies p Int => Eq (Finite p) where
  n == m = runFinite n `mod` reflect n == runFinite m `mod` reflect n

instance Reifies p Int => Num (Finite p) where
  fromInteger n = Finite $ fromInteger n `mod` reflect (Proxy :: Proxy p)
  Finite a + Finite b = withModulo $ a + b
  Finite a - Finite b = withModulo $ a - b
  negate c = Finite $ reflect c - runFinite c
  a * b = withModulo $ runFinite a * runFinite b
  abs (Finite n) = withModulo $ abs n
  signum (Finite n) = withModulo $ signum n

modPow :: (Integral a, Integral a1) => a -> a -> a1 -> a
modPow i p = go i 1
  where
    go _ acc 0 = acc
    go b acc e = go ((b*b) `mod` p) (if e `mod` 2 == 1 then (acc * b) `mod` p else acc) (e `div` 2)

pow :: (Integral a1, Reifies p Int) => Finite p -> a1 -> Finite p
pow a n = withModulo $ modPow (runFinite a) (reflect a) n

instance Reifies p Int => NA.Additive (Finite p) where
  (+) = (+)

instance Reifies p Int => NA.Multiplicative (Finite p) where
  (*) = (*)
  pow1p n p = pow n (p + 1)

instance Reifies p Int => NA.Monoidal (Finite p) where
  zero = 0

instance Reifies p Int => NA.LeftModule NA.Natural (Finite p) where
  n .* p = fromIntegral n * p

instance Reifies p Int => NA.RightModule NA.Natural (Finite p) where
  p *. n = fromIntegral n * p

instance Reifies p Int => NA.LeftModule Integer (Finite p) where
  n .* p = fromIntegral n * p

instance Reifies p Int => NA.RightModule Integer (Finite p) where
  p *. n = fromIntegral n * p

instance Reifies p Int => NA.Group (Finite p) where
  (-) = (-)
  negate = negate

instance Reifies p Int => NA.Abelian (Finite p)

instance Reifies p Int => NA.Semiring (Finite p)

instance Reifies p Int => NA.Rig (Finite p) where
  fromNatural = fromInteger . toInteger

instance Reifies p Int => NA.Ring (Finite p) where
  fromInteger = fromInteger

instance Reifies p Int => NA.Unital (Finite p) where
  one = 1
  pow = pow

instance Reifies p Int => NA.Division (Finite p) where
  recip = recip
  (/)   = (/)
  (^)   = pow

instance Reifies p Int => Fractional (Finite p) where
  a / b = a * recip b
  fromRational r = withModulo (fromInteger $ numerator r) * recip (withModulo (fromInteger $ denominator r))
  recip 0 = error "divide by 0"
  recip n = pow n (reflect n - 2)

instance Reifies p Int => NA.Commutative (Finite p)

instance Reifies p Int => NA.Characteristic (Finite p) where
  char _ = fromIntegral $ reflect (Proxy :: Proxy p)
