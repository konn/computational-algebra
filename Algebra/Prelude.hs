{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction #-}
module Algebra.Prelude
       ((^), (^^),(%),Scalar(..),(.*.),Rational,
        module Prelude,
        module Numeric.Algebra,
        module Algebra.Ring.Polynomial,
        module Numeric.Algebra.Domain,
        module Numeric.Algebra.Domain.Euclidean,
        module Data.Ratio) where
        module Algebra.Ring.Ideal,
import           Algebra.Ring.Polynomial
import           Algebra.Scalar
import           Data.Ratio                       hiding ((%))
import           Data.Singletons
import           Numeric.Algebra                  hiding (Order (..), (^))
import qualified Numeric.Algebra                  as NA
import           Numeric.Algebra.Domain
import           Numeric.Algebra.Domain.Euclidean hiding (normalize)
import           Prelude                          hiding (Fractional (..),
                                                   Integral (..), Num (..),
                                                   Real (..), gcd, lex, product,
                                                   subtract, sum, (^), (^^))
import           Prelude                          (fromRational)

(^) :: Unital r => r -> Natural -> r
(^) = pow

(^^) :: Division r => r -> Integer -> r
(^^) = (NA.^)

(%) :: (Eq r, Division r, SingI n, DecidableZero r)
    => r -> r -> OrderedPolynomial r order n
n % m = injectCoeff (n / m)
infixl 7 %
infixr 8 ^, ^^
