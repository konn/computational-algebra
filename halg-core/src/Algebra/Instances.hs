{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, TypeFamilies                   #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | This Library provides some *dangerous* instances for @Double@s and @Complex@.
module Algebra.Instances () where
import Algebra.Scalar

import           AlgebraicPrelude
import           Control.DeepSeq       (NFData (..))
import           Control.Monad.Random  (Random (..), getRandom)
import           Control.Monad.Random  (getRandomR, runRand)
import           Data.Complex          (Complex (..))
import           Data.Convertible.Base (Convertible (..))
import qualified Data.Ratio            as P
import qualified Data.Vector           as DV
import           Data.Vector.Instances ()
import qualified Numeric.Algebra       as NA
import qualified Prelude               as P

instance Additive r => Additive (DV.Vector r) where
  (+) = DV.zipWith (+)

-- | These Instances are not algebraically right, but for the sake of convenience.
instance DecidableZero r => DecidableZero (Complex r) where
  isZero (a :+ b) = isZero a && isZero b

instance (NFData a) => NFData (Fraction a) where
  rnf a = rnf (numerator a) `seq` rnf (denominator a) `seq` ()

instance Additive r => Additive (Complex r) where
  (a :+ b) + (c :+ d) = (a + c) :+ (b + d)
instance Abelian r => Abelian (Complex r) where
instance (Group r, Semiring r) => Semiring (Complex r) where
instance (Group r, Rig r) => Rig (Complex r) where
  fromNatural = (:+ zero) . fromNatural
instance (Group r, Commutative r) => Commutative (Complex r) where
instance Ring r => Ring (Complex r) where
  fromInteger = (:+ zero) . fromInteger'
instance Group r => Group (Complex r) where
  (a :+ b) - (c :+ d) = (a - c) :+ (b - d)
  negate (a :+ b) = negate a :+ negate b
  times n (a :+ b) = times n a :+ times n b
instance LeftModule a r => LeftModule a (Complex r) where
  r .* (a :+ b) = (r .* a) :+ (r .* b)
instance RightModule a r => RightModule a (Complex r) where
  (a :+ b) *. r = (a *. r) :+ (b *. r)
instance Monoidal r => Monoidal (Complex r) where
  zero = zero :+ zero
instance (Group r, Monoidal r, Unital r) => Unital (Complex r) where
  one = one :+ zero
instance Additive Double where
  (+) = (P.+)
instance (Group r, Multiplicative r) => Multiplicative (Complex r) where
  (a :+ b) * (c :+ d) = (a*c - b*d) :+ (a*d + b*c)
instance LeftModule Natural Double where
  n .* d = fromIntegral n P.* d
instance RightModule Natural Double where
  d *. n = d P.* fromIntegral n
instance Monoidal Double where
  zero = 0
instance Unital Double where
  one = 1
instance Multiplicative Double where
  (*) = (P.*)
instance Commutative Double where
instance Group Double where
  (-) = (P.-)
  negate = P.negate
  subtract = P.subtract
  times n r = P.fromIntegral n P.* r
instance LeftModule Integer Double where
  n .* r = P.fromInteger n * r
instance RightModule Integer Double where
  r *. n = r * P.fromInteger n
instance Rig Double where
  fromNatural = P.fromInteger . fromNatural
instance Semiring Double where
instance Abelian Double where
instance Ring Double where
  fromInteger = P.fromInteger
instance DecidableZero Double where
  isZero 0 = True
  isZero _ = False

instance Division Double where
  recip = P.recip
  (/)   = (P./)

instance P.Integral r => Additive (P.Ratio r) where
  (+) = (P.+)

instance P.Integral r => Abelian (P.Ratio r)

instance P.Integral r => LeftModule Natural (P.Ratio r) where
  n .* r = fromIntegral n P.* r

instance P.Integral r => RightModule Natural (P.Ratio r) where
  r *. n = r P.* fromIntegral n

instance P.Integral r => LeftModule Integer (P.Ratio r) where
  n .* r = P.fromInteger n P.* r

instance P.Integral r => RightModule Integer (P.Ratio r) where
  r *. n = r P.* P.fromInteger n

instance P.Integral r => Group (P.Ratio r) where
  (-)    = (P.-)
  negate = P.negate
  subtract = P.subtract
  times n r = P.fromIntegral n P.* r

instance P.Integral r => Commutative (P.Ratio r)

instance (Semiring r, P.Integral r) => LeftModule (Scalar r) (P.Ratio r) where
  Scalar n .* r = (n P.% 1) * r

instance (Semiring r, P.Integral r) => RightModule (Scalar r) (P.Ratio r) where
  r *. Scalar n = r * (n P.% 1)

instance P.Integral r => Multiplicative (P.Ratio r) where
  (*) = (P.*)

instance P.Integral r => Unital (P.Ratio r) where
  one = 1

instance P.Integral r => Division (P.Ratio r) where
  (/) = (P./)
  recip = P.recip

instance P.Integral r => Monoidal (P.Ratio r) where
  zero = 0

instance P.Integral r => Semiring (P.Ratio r)

instance P.Integral r => Rig (P.Ratio r) where
  fromNatural = P.fromIntegral

instance P.Integral r => Ring (P.Ratio r) where
  fromInteger = P.fromInteger

instance P.Integral r => DecidableZero (P.Ratio r) where
  isZero 0 = True
  isZero _ = False

instance P.Integral r => DecidableUnits (P.Ratio r) where
  isUnit 0 = False
  isUnit _ = True
  recipUnit 0 = Nothing
  recipUnit n = Just (P.recip n)
  r ^? n
    | r == 0 = Just 1
    | r /= 0 = Just (r P.^^ n)
    | r == 0 && n P.> 0 = Just 0
    | otherwise = Nothing

instance Convertible (Fraction Integer) Double where
  safeConvert a = Right $ P.fromInteger (numerator a) P./ P.fromInteger (denominator a)

instance Convertible (Fraction Integer) (Complex Double) where
  safeConvert a = Right $ P.fromInteger (numerator a) P./ P.fromInteger (denominator a) :+ 0

instance (Random (Fraction Integer)) where
  random = runRand $ do
    i <- getRandom
    j <- getRandom
    return $ i % (P.abs j + 1)
  randomR (a, b) = runRand $ do
    j <- succ . P.abs <$> getRandom
    let g = foldl1 P.lcm  [denominator a, denominator b, j]
        lb = g * numerator a `quot` denominator a
        ub = g * numerator b `quot` denominator b
    i <- getRandomR (lb, ub)
    return $ i % g
