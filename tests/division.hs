{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
module Main where
import Algebra.Algorithms.Groebner
import Algebra.Ring.Noetherian
import Algebra.Ring.Polynomial
import Data.Type.Monomorphic
import Data.Type.Natural           hiding (one, promote, zero)
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck             hiding (promote)
import Utils

main :: IO ()
main = hspec $ do
  describe "divModPolynomial'" $ do
    prop "quotient cannot be diveided by any denoms (ternary)" $
      checkForArity [3] prop_indivisible
    prop "satisfies a_i f_i /= 0 ==> deg(f) >= deg (a_i f_i)" $
      checkForArity [3] prop_degdecay
    prop "divides correctly" $
      checkForArity [3] prop_divCorrect

prop_divCorrect :: SingRep n => SNat n -> Property
prop_divCorrect sdim =
  forAll (polyOfDim sdim) $ \poly ->
  forAll (idealOfDim sdim) $ \ideal ->
  let dvs = take 5 $ generators ideal
      (qds, r) = poly `divModPolynomial'` dvs
  in poly == sum (map (uncurry (*)) qds) + r

prop_indivisible :: SingRep n => SNat n -> Property
prop_indivisible sdim =
  forAll (polyOfDim sdim) $ \poly ->
  forAll (idealOfDim sdim) $ \ideal ->
  let dvs = take 5 $ generators ideal
      (_, r) = changeOrder Grevlex poly `divModPolynomial'` dvs
  in r /= 0 ==> all (\f -> all (\(_, m) -> not $ leadingMonomial f `divs` m) $ getTerms r)  dvs

prop_degdecay :: SingRep n => SNat n -> Property
prop_degdecay sdim =
  forAll (polyOfDim sdim) $ \poly ->
  forAll (idealOfDim sdim) $ \ideal ->
  let dvs = take 5 $ generators ideal
      (qs, _) = poly `divModPolynomial'` dvs
  in all (\(a, f) -> (a * f == 0) || (leadingMonomial poly >= leadingMonomial (a * f))) qs
