{-# LANGUAGE DataKinds, OverlappingInstances, PolyKinds #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Main (module Algebra.Algorithms.Groebner, module Algebra.Ring.Polynomial
            , module Data.Ratio, module Main, module Algebra.Internal
            ) where
import           Algebra.Algorithms.Groebner
import           Algebra.Internal
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Data.Ratio
import qualified Numeric.Algebra             as NA

u, v, x, y, z :: Polynomial Rational (S (S Three))
[u, v, x, y, z] = genVars (sS (sS sThree))

(.+), (.*), (.-) :: Polynomial Rational (S Three) -> Polynomial Rational (S Three) -> Polynomial Rational (S Three)
(.+) = (NA.+)
(.*) = (NA.*)
(.-) = (NA.-)

infixl 6 .+, .-
infixl 7 .*

(^^^) :: Polynomial Rational (S Three) -> NA.Natural -> Polynomial Rational (S Three)
(^^^) = NA.pow

fromRight :: Either t t1 -> t1
fromRight (Right a) = a
fromRight _ = error "fromRight"
{-
parse :: String -> Polynomial Rational
parse = fromRight . parsePolyn
-}

main :: IO ()
main = print $ thEliminationIdealWith (eliminationOrder sTwo) sTwo $
         toIdeal [x - (3*u + 3*u*v^2 - u^3), y - (3*v + 3*u^2*v -  v^3), z - (3*u^2 - 3*v^2)]
