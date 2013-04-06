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

c, s, x, y :: Polynomial Rational (S Three)
[c, s, x, y] = genVars (sS sThree)

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

{-
parse :: String -> Polynomial Rational
parse = fromRight . parsePolyn
-}

main :: IO ()
main = print $ thEliminationIdealWith (weightedEliminationOrder sTwo) sTwo (toIdeal [x-c^3, y-s^3, c^2+s^2-1])
