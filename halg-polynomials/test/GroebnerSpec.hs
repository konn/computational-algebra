{-# LANGUAGE DataKinds, ExplicitNamespaces, GADTs, PatternSynonyms #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
module GroebnerSpec where
import Algebra.Algorithms.Groebner
import Algebra.Internal            (pattern (:<), KnownNat, pattern NilL, SNat)
import Algebra.Ring.Ideal
import Algebra.Ring.Polynomial
import Utils

import           Control.Monad
import qualified Data.Foldable          as F
import           Data.List              (delete, tails)
import qualified Data.Sized.Builtin     as SV
import           Numeric.Field.Fraction (Fraction)
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck

asGenListOf :: Gen [a] -> a -> Gen [a]
asGenListOf = const

type Microsecs = Int
minutes, seconds :: Int -> Microsecs
seconds n = n * 1000000
minutes n = n * seconds 60

spec :: Spec
spec = parallel $ do
  describe "divModPolynomial" $ modifyMaxSize (const 10) $ modifyMaxSuccess (const 10) $ do
    prop "remainder cannot be diveided by any denoms (ternary)" $
      within (minutes 1) $ checkForArity [1..4] prop_indivisible
    prop "satisfies a_i f_i /= 0 ==> deg(f) >= deg (a_i f_i)" $
      within (minutes 1) $ checkForArity [1..4] prop_degdecay
    prop "divides correctly" $
      within (minutes 1) $ checkForArity [1..4] prop_divCorrect
  describe "calcGroebnerBasis" $ modifyMaxSize (const 5) $ modifyMaxSuccess (const 10) $ do
    prop "passes S-test" $
      mapSize (const 3) $ withMaxSuccess 10 $
      within (minutes 1) $ checkForArity [2..3] prop_passesSTest
    prop "divides all original generators" $ do
      within (minutes 1) $ checkForArity [2..3] prop_groebnerDivsOrig
    it "generates the same ideal as original" $ do
      pendingWith "need example"
    it "produces minimal basis" $ do
      within (minutes 1) $ checkForArity [2..3] prop_isMinimal
    it "produces reduced basis" $ do
      within (minutes 1) $ checkForArity [2..3] prop_isReduced
  describe "isIdealMember" $ do
    it "determins membership correctly" $ do
      pendingWith "need example"
  describe "intersection" $ modifyMaxSize (const 4) $ modifyMaxSuccess (const 25) $ do
    it "can calculate correctly" $ do
      within (minutes 1) $ checkForArity [2..3] prop_intersection
    it "can solve test-cases correctly" $ do
      forM_ ics_binary $ \(IC i j ans) ->
        F.toList (intersection [toIdeal i, toIdeal j]) `shouldBe` ans

prop_intersection :: KnownNat n => SNat n -> Property
prop_intersection sdim =
  forAll (idealOfArity sdim) $ \ideal ->
  forAll (idealOfArity sdim) $ \jdeal ->
  forAll (polynomialOfArity sdim) $ \f ->
  (f `isIdealMember` ideal && f `isIdealMember` jdeal)
  == f `isIdealMember` intersection [ideal, jdeal]

prop_isMinimal :: KnownNat n => SNat n -> Property
prop_isMinimal sdim =
  forAll (idealOfArity sdim) $ \ideal ->
  let gs = calcGroebnerBasis ideal
  in all ((== 1) . leadingCoeff) gs &&
     all (\f -> all (\g -> not $ leadingMonomial g `divs` leadingMonomial f) (delete f gs)) gs

prop_isReduced :: KnownNat n => SNat n -> Property
prop_isReduced sdim =
  forAll (idealOfArity sdim) $ \ideal ->
  let gs = calcGroebnerBasis ideal
  in all ((== 1) . leadingCoeff) gs &&
     all (\f -> all (\g -> all (\(_, m) -> not $ leadingMonomial g `divs` m) $ getTerms f) (delete f gs)) gs

prop_passesSTest :: KnownNat n => SNat n -> Property
prop_passesSTest sdim =
  forAll (sized $ \size -> vectorOf size (polynomialOfArity sdim)) $ \ideal ->
  let gs = calcGroebnerBasis $ toIdeal ideal
  in all ((== 0) . (`modPolynomial` gs)) [sPolynomial f g | (f : gs) <- init $ tails gs, g <- gs]

prop_groebnerDivsOrig :: KnownNat n => SNat n -> Property
prop_groebnerDivsOrig sdim =
  forAll (elements [3..15]) $ \count ->
  forAll (vectorOf count (polynomialOfArity sdim)) $ \ideal ->
  let gs = calcGroebnerBasis $ toIdeal ideal
  in all ((== 0) . (`modPolynomial` gs)) ideal

prop_divCorrect :: KnownNat n => SNat n -> Property
prop_divCorrect sdim =
  forAll (polynomialOfArity sdim) $ \poly ->
  forAll (idealOfArity sdim) $ \ideal ->
  let dvs = generators ideal
      (qds, r) = poly `divModPolynomial` dvs
  in poly == sum (map (uncurry (*)) qds) + r

prop_indivisible :: KnownNat n => SNat n -> Property
prop_indivisible sdim =
  forAll (polynomialOfArity sdim) $ \poly ->
  forAll (idealOfArity sdim) $ \ideal ->
  let dvs = generators ideal
      (_, r) = changeOrder Grevlex poly `divModPolynomial` dvs
  in r /= 0 ==> all (\f -> all (\(_, m) -> not $ leadingMonomial f `divs` m) $ getTerms r)  dvs

prop_degdecay :: KnownNat n => SNat n -> Property
prop_degdecay sdim =
  forAll (polynomialOfArity sdim) $ \poly ->
  forAll (idealOfArity sdim) $ \ideal ->
  let dvs = generators ideal
      (qs, _) = poly `divModPolynomial` dvs
  in all (\(a, f) -> (a * f == 0) || (leadingMonomial poly >= leadingMonomial (a * f))) qs

data IntersectCase r ord n = IC [OrderedPolynomial r ord n] [OrderedPolynomial r ord n] [OrderedPolynomial r ord n]

ics_binary :: [IntersectCase (Fraction Integer) Grevlex 2]
ics_binary =
  let [x, y] = F.toList allVars
  in [IC [x*y] [y] [x*y]]
