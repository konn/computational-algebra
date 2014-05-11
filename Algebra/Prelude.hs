{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction #-}
module Algebra.Prelude
       ((^), (^^),(%),Scalar(..),(.*.),
        module Prelude,
        module Numeric.Algebra,
        module Algebra.Ring.Polynomial,
        module Data.Ratio) where
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Algebra.Scalar
import           Data.Ratio              hiding ((%))
import           Data.Singletons
import           Numeric.Algebra         hiding (Order (..), (^))
import qualified Numeric.Algebra         as NA
import           Prelude                 hiding (Fractional (..), Integral (..),
                                          Num (..), Real (..), lex, product,
                                          subtract, sum, (^), (^^))
import           Prelude                 (fromRational)

(^) :: Unital r => r -> Natural -> r
(^) = pow

(^^) :: Division r => r -> Integer -> r
(^^) = (NA.^)

(%) :: (Eq r, Division r, SingI n, NoetherianRing r)
    => r -> r -> OrderedPolynomial r order n
n % m = injectCoeff (n / m)
infixl 7 %
infixr 8 ^, ^^
