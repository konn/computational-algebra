{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Algebra.Normed where
import AlgebraicPrelude

-- | Additional types for /normed/ types.
class (Ord (Norm a)) => Normed a where
  type Norm a
  norm :: a -> Norm a
  liftNorm :: Norm a -> a

deriving instance Normed a => Normed (WrapNum a)
deriving instance Normed a => Normed (WrapFractional a)
deriving instance Normed a => Normed (WrapAlgebra a)
deriving instance Normed a => Normed (WrapIntegral a)

deriving instance Normed a => Normed (Add a)
deriving instance Normed a => Normed (Mult a)

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
