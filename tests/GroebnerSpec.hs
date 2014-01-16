{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
module GroebnerSpec where
import Algebra.Algorithms.Groebner
import Algebra.Ring.Noetherian
import Algebra.Ring.Polynomial
import Data.Type.Monomorphic
import Data.Type.Natural           hiding (one, promote, zero)
import Instances
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck             hiding (promote)

asGenListOf :: Gen [a] -> a -> Gen [a]
asGenListOf = const

spec :: Spec
spec = do
  describe "divModPolynomial" $ do
    prop "quotient cannot be diveided by any denoms (ternary)" $
      forAll (elements [2..3 :: Int]) $ liftPoly prop_indivisible
    prop "satisfies a_i f_i /= 0 ==> deg(f) >= deg (a_i f_i)" $
      forAll (elements [2..3 :: Int]) $ liftPoly prop_degdecay
    prop "divides correctly" $
      forAll (elements [2..3 :: Int]) $ liftPoly prop_divCorrect
  describe "calcGroebnerBasis" $ do
    prop "divides all original generators" $ do
      forAll (elements [2..3 :: Int]) $ liftPoly prop_groebnerDivsOrig
    it "generates the same ideal as original" $ do
      pendingWith "need example"
    it "passes S-test" $ do
      forAll (elements [2..3 :: Int]) $ liftPoly prop_passesSTest

prop_passesSTest :: SNat n -> Property
prop_passesSTest sdim =
  case singInstance sdim of
    SingInstance ->
      forAll (idealOfDim sdim) $ \ideal ->
      let gs = calcGroebnerBasis ideal
      in all ((== 0) . (`modPolynomial` gs)) [sPolynomial f g | f <- gs, g <- gs, f /= g]

prop_groebnerDivsOrig :: SNat n -> Property
prop_groebnerDivsOrig sdim =
  case singInstance sdim of
    SingInstance ->
      forAll (idealOfDim sdim) $ \ideal ->
      let gs = calcGroebnerBasis ideal
      in all ((== 0) . (`modPolynomial` gs)) (generators ideal)

prop_divCorrect :: SNat n -> Property
prop_divCorrect sdim =
  case singInstance sdim of
    SingInstance ->
      forAll (polyOfDim sdim) $ \poly ->
      forAll (idealOfDim sdim) $ \ideal ->
      let dvs = generators ideal
          (qds, r) = poly `divModPolynomial` dvs
      in poly == sum (map (uncurry (*)) qds) + r

prop_indivisible :: SNat n -> Property
prop_indivisible sdim =
  case singInstance sdim of
    SingInstance ->
      forAll (polyOfDim sdim) $ \poly ->
      forAll (idealOfDim sdim) $ \ideal ->
      let dvs = generators ideal
          (_, r) = changeOrder Grevlex poly `divModPolynomial` dvs
      in r /= 0 ==> all (\f -> all (\(_, m) -> not $ leadingMonomial f `divs` m) $ getTerms r)  dvs

prop_degdecay :: SNat n -> Property
prop_degdecay sdim =
  case singInstance sdim of
    SingInstance ->
      forAll (polyOfDim sdim) $ \poly ->
      forAll (idealOfDim sdim) $ \ideal ->
      let dvs = generators ideal
          (qs, _) = poly `divModPolynomial` dvs
      in all (\(a, f) -> (a * f == 0) || (leadingOrderedMonomial poly >= leadingOrderedMonomial (a * f))) qs
