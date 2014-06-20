{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction #-}
module Algebra.Prelude
       ((^), (^^),(%),Scalar(..),(.*.),Rational,
        module Prelude,
        module Numeric.Algebra,
        module Algebra.Ring.Polynomial,
        module Numeric.Domain.Class,
        module Numeric.Domain.Euclidean,
        module Algebra.Ring.Ideal,
        module Numeric.Field.Fraction) where
import           Algebra.Ring.Ideal
import           Algebra.Ring.Polynomial
import           Algebra.Scalar
import           Data.Ratio               hiding ((%))
import           Data.Singletons
import           Numeric.Algebra          hiding (Order (..), (^))
import qualified Numeric.Algebra          as NA
import           Numeric.Domain.Class
import           Numeric.Domain.Euclidean hiding (normalize)
import           Numeric.Field.Fraction
import           Prelude                  hiding (Fractional (..),
                                           Integral (..), Num (..), Rational,
                                           Real (..), gcd, lex, product,
                                           subtract, sum, (^), (^^))
import           Prelude                  (fromRational)

(^) :: Unital r => r -> Natural -> r
(^) = pow

(^^) :: Division r => r -> Integer -> r
(^^) = (NA.^)

(%) :: (Eq r, Division r, SingI n, DecidableZero r)
    => r -> r -> OrderedPolynomial r order n
n % m = injectCoeff (n / m)
infixl 7 %
infixr 8 ^, ^^

type Rational = Ratio Integer
