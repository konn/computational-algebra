{-# LANGUAGE FlexibleContexts, FlexibleInstances               #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving                                #-}
module Algebra.Scalar (Scalar(..), (.*.)) where
import           AlgebraicPrelude
import Algebra.Normed
import qualified Prelude          as P

-- | @'Scalar' r@ provides almost the same type-instances as @r@,
--   but it can also behave as a @'Module'@ over @r@ itself.
newtype Scalar r = Scalar { runScalar :: r }
    deriving (Read, Show, Eq, Ord, Additive,
              Integral, Real, Enum
             ,Multiplicative, Unital)

(.*.) :: (Module (Scalar r) m)
      => r -> m -> m
r .*. f = Scalar r .* f

infixr 8 .*.
instance Normed r => Normed (Scalar r) where
  type Norm (Scalar r) = Norm r
  norm = norm . runScalar
  liftNorm = runScalar . liftNorm
deriving instance DecidableAssociates r => DecidableAssociates (Scalar r)
deriving instance DecidableUnits r => DecidableUnits (Scalar r)
deriving instance UnitNormalForm r => UnitNormalForm (Scalar r)

deriving instance P.Num r => P.Num (Scalar r)

deriving instance P.Fractional r => P.Fractional (Scalar r)
deriving instance Monoidal r => Monoidal (Scalar r)
deriving instance Group r => Group (Scalar r)
deriving instance Semiring r => Semiring (Scalar r)
deriving instance Ring r => Ring (Scalar r)
deriving instance Abelian r => Abelian (Scalar r)
deriving instance Rig r => Rig (Scalar r)
deriving instance Commutative r => Commutative (Scalar r)
deriving instance Division r => Division (Scalar r)
deriving instance LeftModule Integer r => LeftModule Integer (Scalar r)
deriving instance RightModule Integer r => RightModule Integer (Scalar r)
deriving instance LeftModule Natural r => LeftModule Natural (Scalar r)
deriving instance RightModule Natural r => RightModule Natural (Scalar r)
instance Semiring r => RightModule r (Scalar r) where
  Scalar r *. q = Scalar $ r * q
  {-# INLINE (*.) #-}
instance Semiring r => LeftModule r (Scalar r) where
  r .* Scalar q = Scalar $ r * q
  {-# INLINE (.*) #-}

instance (Semiring r) => LeftModule (Scalar r) (Scalar r) where
  Scalar r .* Scalar q = Scalar $ r * q

instance (Semiring r) => RightModule (Scalar r) (Scalar r) where
  Scalar r *. Scalar q = Scalar $ r * q
