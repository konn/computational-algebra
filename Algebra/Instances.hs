{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, TypeFamilies                   #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | This Library provides some *dangerous* instances for @Double@s and @Complex@.
module Algebra.Instances () where
import           Control.Lens
import           Data.Complex
import           Data.Type.Natural (Nat (..), bugInGHC)
import qualified Data.Vector.Sized as V
import           Numeric.Algebra
import           Prelude           hiding (Num (..))
import qualified Prelude           as P

type instance Index (V.Vector a n) = V.Index n
type instance IxValue (V.Vector a n) = a
instance Functor f => Ixed f (V.Vector a (S n)) where
  ix idx = ilens getter setter
    where
      getter v = (idx, V.sIndex idx v)
      setter v val = updateNth idx (const val) v

updateNth :: V.Index (S n) -> (a -> a) -> V.Vector a (S n) -> V.Vector a (S n)
updateNth V.OZ     f (a V.:- as) = f a V.:- as
updateNth (V.OS n) f (a V.:- b V.:- bs) = a V.:- updateNth n f (b V.:- bs)
updateNth _      _ _              = bugInGHC

-- | These Instances are not algebraically right, but for the sake of convenience.
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
