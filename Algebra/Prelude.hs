{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction #-}
module Algebra.Prelude
       ((^), (^^),(%),
        module Prelude,
        module Numeric.Algebra,
        module Algebra.Ring.Polynomial,
        module Data.Ratio) where
import Prelude hiding (Num(..), Integral(..), Real(..),
                       product, sum, lex,
                       Fractional(..), (^^), (^), subtract)
import Prelude (fromRational)
import Numeric.Algebra hiding ((^), (^^), Order(..))
import qualified Numeric.Algebra as NA
import Algebra.Ring.Polynomial
import Algebra.Ring.Noetherian
import Data.Ratio hiding ((%))
import Data.Type.Natural
import Data.Type.Ordinal
import Data.Singletons

(^) :: Unital r => r -> Natural -> r
(^) = pow

(^^) :: Division r => r -> Integer -> r
(^^) = (NA.^)

(%) :: (Eq r, Division r, SingRep n, NoetherianRing r)
    => r -> r -> OrderedPolynomial r order n
n % m = injectCoeff (n / m)
infixl 7 %
infixr 8 ^, ^^
