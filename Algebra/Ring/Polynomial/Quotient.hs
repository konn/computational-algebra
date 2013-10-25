{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, PolyKinds, ScopedTypeVariables           #-}
{-# LANGUAGE UndecidableInstances                                            #-}
module Algebra.Ring.Polynomial.Quotient (Quotient(), quotRepr) where
import           Algebra.Algorithms.Groebner
import           Algebra.Ring.Polynomial
import           Algebra.Scalar
import           Data.Proxy
import           Data.Reflection
import           Numeric.Algebra
import qualified Numeric.Algebra             as NA
import           Prelude                     hiding (lex, negate, recip, sum,
                                              (*), (+), (-), (^), (^^))
import qualified Prelude                     as P

data Quotient r n ideal = Quotient { quotRepr_ :: Polynomial r n } deriving (Eq)

instance Show (Polynomial r n) => Show (Quotient r n ideal) where
  show (Quotient f) = show f

reduceQuot :: forall r n ideal. (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r)
           => Polynomial r n -> Quotient r n ideal
reduceQuot f = Quotient $ f `modPolynomial` reflect (Proxy :: Proxy ideal)

quotRepr :: Quotient r n ideal -> Polynomial r n
quotRepr = quotRepr_

instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Additive (Quotient r n ideal) where
  f + g = Quotient $ quotRepr_ f + quotRepr_ g
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => LeftModule Natural (Quotient r n ideal) where
  n .* f = reduceQuot $ n .* quotRepr_ f
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => RightModule Natural (Quotient r n ideal) where
  f *. n = reduceQuot $ quotRepr_ f *. n
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Monoidal (Quotient r n ideal) where
  zero   = reduceQuot zero
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => LeftModule Integer (Quotient r n ideal) where
  n .* f = reduceQuot $ n .* quotRepr_ f
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => RightModule Integer (Quotient r n ideal) where
  f *. n = reduceQuot $ quotRepr_ f *. n
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Group (Quotient r n ideal) where
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Abelian (Quotient r n ideal) where
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Multiplicative (Quotient r n ideal) where
  f * g = reduceQuot $ quotRepr_ f * quotRepr_ g
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Semiring (Quotient r n ideal) where
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Unital (Quotient r n ideal) where
  one   = reduceQuot one
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Rig (Quotient r n ideal) where
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Ring (Quotient r n ideal) where
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => LeftModule (Scalar r) (Quotient r n ideal) where
  r .* f = Quotient $ r .* quotRepr_ f
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => RightModule (Scalar r) (Quotient r n ideal) where
  f *. r = Quotient $ quotRepr_ f *. r

instance (Num r, Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Num (Quotient r n ideal) where
  (+) = (NA.+)
  (*) = (NA.*)
  fromInteger = reduceQuot . P.fromInteger
  signum = reduceQuot . signum . quotRepr_
  abs    = id
  negate = reduceQuot . negate . quotRepr_
