{-# LANGUAGE NoImplicitPrelude #-}
module Main where
import Algebra.Algorithms.Groebner
import Algebra.Prelude
import Algebra.Ring.Noetherian
import SingularBridge
import Test.QuickCheck
import Utils

main :: IO ()
main = quickCheck $ checkForArity [2..3] $ \sarity ->
  forAll (sized $ \size -> vectorOf (size+2) (homogPolyOfDim sarity)) $ \ideal ->
    let i = filter ((/= 0) . totalDegree' ) ideal
    in not (null i) ==> isGroebnerBasis (singIdealFun "basis_c" (toIdeal i))

