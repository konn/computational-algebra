{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving, TypeOperators                      #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module Algebra.Ring.Polynomial.Homogenised where
import Algebra.Prelude.Core
import Algebra.Ring.Polynomial.Class
import Algebra.Ring.Polynomial.Univariate

newtype Homogenised poly = Homogenised { runHomogenised :: Unipol poly }

deriving instance IsOrderedPolynomial poly => Additive (Homogenised poly)
deriving instance IsOrderedPolynomial poly => Unital (Homogenised poly)
deriving instance IsOrderedPolynomial poly => LeftModule Natural (Homogenised poly)
deriving instance IsOrderedPolynomial poly => RightModule Natural (Homogenised poly)
deriving instance IsOrderedPolynomial poly => LeftModule Integer (Homogenised poly)
deriving instance IsOrderedPolynomial poly => RightModule Integer (Homogenised poly)
deriving instance IsOrderedPolynomial poly => Multiplicative (Homogenised poly)
deriving instance IsOrderedPolynomial poly => Monoidal (Homogenised poly)
deriving instance IsOrderedPolynomial poly => Group (Homogenised poly)
deriving instance IsOrderedPolynomial poly => Abelian (Homogenised poly)
deriving instance IsOrderedPolynomial poly => Commutative (Homogenised poly)
deriving instance IsOrderedPolynomial poly => Eq (Homogenised poly)
deriving instance IsOrderedPolynomial poly => DecidableZero (Homogenised poly)
deriving instance IsOrderedPolynomial poly => Semiring (Homogenised poly)
deriving instance IsOrderedPolynomial poly => Rig (Homogenised poly)
deriving instance IsOrderedPolynomial poly => Ring (Homogenised poly)
deriving instance IsOrderedPolynomial poly => Num (Homogenised poly)
instance (IsOrderedPolynomial poly, LeftModule (Scalar r) poly)
      => LeftModule (Scalar r) (Homogenised poly) where
  r .* Homogenised f = Homogenised $ mapCoeff' (r .*) f
instance (IsOrderedPolynomial poly, RightModule (Scalar r) poly)
      => RightModule (Scalar r) (Homogenised poly) where
   Homogenised f *. r = Homogenised $ mapCoeff' (*. r) f

instance IsOrderedPolynomial poly => IsPolynomial (Homogenised poly) where
  type Coefficient (Homogenised poly) = Coefficient poly
  type Arity (Homogenised poly) = Succ (Arity poly)
  sArity _ = sing
  -- liftMap gen (Homogenised f) =
  --   let g = liftMap (gen . OS)
  --   in liftMap (const $ _ $ gen 0) f

-- deriving instance IsOrderedPolynomial poly => PID (Homogenised poly)
-- deriving instance IsOrderedPolynomial poly => Euclidean (Homogenised poly)
-- deriving instance IsOrderedPolynomial poly => DecidableUnits (Homogenised poly)
