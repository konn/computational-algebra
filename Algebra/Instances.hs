{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, TypeFamilies                   #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | This Library provides some *dangerous* instances for @Double@s and @Complex@.
module Algebra.Instances () where
import           Control.Lens
import           Data.Complex
import           Data.Convertible.Base    (Convertible (..))
import qualified Data.Ratio               as P
import           Data.Type.Natural        (bugInGHC)
import qualified Data.Vector.Sized        as V
import           Numeric.Algebra
import qualified Numeric.Algebra          as NA
import           Numeric.Decidable.Zero
import           Numeric.Domain.Euclidean (Euclidean)
import           Numeric.Domain.Euclidean (splitUnit)
import           Numeric.Field.Fraction
import           Prelude                  hiding (Num (..))
import qualified Prelude                  as P

type instance Index (V.Vector a n) = V.Index n
type instance IxValue (V.Vector a n) = a
instance Functor f => Ixed f (V.Vector a  n) where
  ix idx = ilens getter setter
    where
      getter v = (idx, V.sIndex idx v)
      setter v val = updateNth idx (const val) v

updateNth :: V.Index n -> (a -> a) -> V.Vector a n -> V.Vector a n
updateNth V.OZ     f (a V.:- as) = f a V.:- as
updateNth (V.OS n) f (a V.:- b V.:- bs) = a V.:- updateNth n f (b V.:- bs)
updateNth _      _ _              = bugInGHC

-- | These Instances are not algebraically right, but for the sake of convenience.
instance DecidableZero r => DecidableZero (Complex r) where
  isZero (a :+ b) = isZero a && isZero b

instance Euclidean a => P.Num (Fraction a) where
  (+) = (NA.+)
  (-) = (NA.-)
  negate = NA.negate
  (*) = (NA.*)
  fromInteger = NA.fromInteger
  abs p = snd (splitUnit (numerator p)) % snd (splitUnit (denominator p))
  signum p = fst (splitUnit (numerator p)) % fst (splitUnit (denominator p))

instance Additive r => Additive (Complex r) where
  (a :+ b) + (c :+ d) = (a + c) :+ (b + d)
instance Abelian r => Abelian (Complex r) where
instance (Group r, Semiring r) => Semiring (Complex r) where
instance (Group r, Rig r) => Rig (Complex r) where
  fromNatural = (:+ zero) . fromNatural
instance (Group r, Commutative r) => Commutative (Complex r) where
instance Ring r => Ring (Complex r) where
  fromInteger = (:+ zero) . fromInteger
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

instance Euclidean d => Fractional (Fraction d) where
  fromRational r = fromInteger (P.numerator r) % fromInteger (P.denominator r)
  recip = NA.recip
  (/) = (NA./)

instance Convertible (Fraction Integer) Double where
  safeConvert a = Right $ P.fromInteger (numerator a) P./ P.fromInteger (denominator a)

instance Convertible (Fraction Integer) (Complex Double) where
  safeConvert a = Right $ P.fromInteger (numerator a) P./ P.fromInteger (denominator a) :+ 0
