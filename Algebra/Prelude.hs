{-# LANGUAGE FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction #-}
module Algebra.Prelude
       ((^), (^^),(%),Scalar(..),(.*.),Rational,
        module Prelude,
        module Numeric.Algebra,
        module Algebra.Ring.Polynomial,
        module Numeric.Domain.Class,
        module Numeric.Domain.Euclidean,
        module Algebra.Ring.Ideal,
        module Numeric.Field.Fraction,
        module Algebra.Internal) where

import Algebra.Internal

import           Algebra.Ring.Ideal
import           Algebra.Ring.Polynomial
import           Algebra.Scalar
import           Numeric.Algebra          hiding (Order (..), (^))
import qualified Numeric.Algebra          as NA
import           Numeric.Domain.Class
import           Numeric.Domain.Euclidean
import           Numeric.Field.Fraction   hiding ((%))
import           Prelude                  hiding (Fractional (..),
                                           Integral (..), Num (..), Rational,
                                           Real (..), gcd, lcm, lex, product,
                                           subtract, sum, (^), (^^))
import           Prelude                  (fromRational)

(^) :: Unital r => r -> Natural -> r
(^) = pow

(^^) :: Division r => r -> Integer -> r
(^^) = (NA.^)

(%) :: (IsPolynomial poly, Division (Coefficient poly))
    => Coefficient poly -> Coefficient poly -> poly
n % m = injectCoeff (n / m)
infixl 7 %
infixr 8 ^, ^^

type Rational = Ratio Integer
