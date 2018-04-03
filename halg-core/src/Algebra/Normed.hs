{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving, TypeFamilies                     #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Algebra.Normed where
import AlgebraicPrelude

-- | Additional types for /normed/ types.
class (Ord (Norm a)) => Normed a where
  type Norm a
  norm :: a -> Norm a
  liftNorm :: Norm a -> a

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 802
deriving instance Normed a => Normed (WrapNum a)
deriving instance Normed a => Normed (WrapFractional a)
deriving instance Normed a => Normed (WrapAlgebra a)
deriving instance Normed a => Normed (WrapIntegral a)

deriving instance Normed a => Normed (Add a)
deriving instance Normed a => Normed (Mult a)
#else
instance Normed a => Normed (WrapNum a) where
  type Norm (WrapNum a) = Norm a
  norm = norm . unwrapNum
  liftNorm = WrapNum . liftNorm

instance Normed a => Normed (WrapFractional a) where
  type Norm (WrapFractional a) = Norm a
  norm = norm . unwrapFractional
  liftNorm = WrapFractional . liftNorm

instance Normed a => Normed (WrapAlgebra a) where
  type Norm (WrapAlgebra a) = Norm a
  norm = norm . unwrapAlgebra
  liftNorm = WrapAlgebra . liftNorm

instance Normed a => Normed (WrapIntegral a) where
  type Norm (WrapIntegral a) = Norm a
  norm = norm . unwrapIntegral
  liftNorm = WrapIntegral . liftNorm

instance Normed a => Normed (Add a) where
  type Norm (Add a) = Norm a
  norm = norm . runAdd
  liftNorm = Add . liftNorm

instance Normed a => Normed (Mult a) where
  type Norm (Mult a) = Norm a
  norm = norm . runMult
  liftNorm = Mult . liftNorm
#endif

instance Normed Double where
  type Norm Double = Double
  norm = abs
  liftNorm = id

instance Normed Int where
  type Norm Int = Int
  norm = abs
  liftNorm = id

instance Normed Integer where
  type Norm Integer = Integer
  norm = abs
  liftNorm = id

instance (Ord (Norm d), Euclidean d, Euclidean (Norm d), Normed d)
     =>  Normed (Fraction d) where
  type Norm (Fraction d) = Fraction (Norm d)
  norm f = norm (numerator f) % norm (denominator f)
  liftNorm f = liftNorm (numerator f) % liftNorm (denominator f)

{-# ANN module "Hlint: ignore Unused LANGUAGE pragma" #-}
