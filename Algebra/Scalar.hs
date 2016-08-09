{-# LANGUAGE FlexibleContexts, FlexibleInstances               #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving                                #-}
module Algebra.Scalar (Scalar(..), (.*.)) where
import           AlgebraicPrelude
import qualified Prelude          as P
import Numeric.Algebra.Unital.UnitNormalForm hiding (normalize)

newtype Scalar r = Scalar { runScalar :: r }
    deriving (Read, Show, Eq, Ord, Additive,
              P.Integral, P.Real, Enum
             ,Multiplicative, Unital)

(.*.) :: (Module (Scalar r) m)
      => r -> m -> m
r .*. f = Scalar r .* f

infixr 8 .*.
instance Normed r => Normed (Scalar r) where
  type Norm (Scalar r) = Norm r
  norm = norm . runScalar
  liftNorm = runScalar . liftNorm

instance (Ring r, Normed r, UnitNormalForm r) => P.Num (Scalar r) where
  abs = abs
  (+) = (+)
  (-) = (-)
  (*) = (*)
  negate = negate
  fromInteger = Scalar . fromInteger'
  signum = Scalar . fst . splitUnit . runScalar

instance (Ring r, Normed r, Division r, UnitNormalForm r) => P.Fractional (Scalar r) where
  (/) = (/)
  recip = recip
  fromRational = fromRational


deriving instance Monoidal r => Monoidal (Scalar r)
deriving instance Group r => Group (Scalar r)
deriving instance Semiring r => Semiring (Scalar r)
deriving instance Ring r => Ring (Scalar r)
deriving instance Abelian r => Abelian (Scalar r)
deriving instance Rig r => Rig (Scalar r)
deriving instance Commutative r => Commutative (Scalar r)
deriving instance Division r => Division (Scalar r)

instance LeftModule Integer r => LeftModule Integer (Scalar r) where
  n .* Scalar r = Scalar $ n .* r
instance RightModule Integer r => RightModule Integer (Scalar r) where
  Scalar r *. n = Scalar $ r *. n
instance LeftModule Natural r => LeftModule Natural (Scalar r) where
  n .* Scalar r = Scalar $ n .* r
instance RightModule Natural r => RightModule Natural (Scalar r) where
  Scalar r *. n = Scalar $ r *. n
instance Ring r => RightModule r (Scalar r) where
  Scalar r *. q = Scalar $ r * q
instance Ring r => LeftModule r (Scalar r) where
  r .* Scalar q = Scalar $ r * q

instance (Semiring r) => LeftModule (Scalar r) (Scalar r) where
  Scalar r .* Scalar q = Scalar $ r * q

instance (Semiring r) => RightModule (Scalar r) (Scalar r) where
  Scalar r *. Scalar q = Scalar $ r * q
