{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
module GroebnerSpec where
import           Algebra.Algorithms.Groebner
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Control.Monad
import           Data.List                   (delete)
import           Data.Type.Monomorphic
import           Data.Type.Natural           hiding (one, promote, zero)
import           Data.Vector.Sized           (Vector (..))
import qualified Data.Vector.Sized           as SV
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck             hiding (promote)
import           Utils

asGenListOf :: Gen [a] -> a -> Gen [a]
asGenListOf = const

spec :: Spec
spec = do
  describe "divModPolynomial" $ modifyMaxSize (const 25) $ modifyMaxSuccess (const 100) $ do
    prop "quotient cannot be diveided by any denoms (ternary)" $
      checkForArity [1..4] prop_indivisible
    prop "satisfies a_i f_i /= 0 ==> deg(f) >= deg (a_i f_i)" $
      checkForArity [1..4] prop_degdecay
    prop "divides correctly" $
      checkForArity [1..4] prop_divCorrect
  describe "calcGroebnerBasis" $ modifyMaxSize (const 4) $ modifyMaxSuccess (const 50) $ do
    prop "passes S-test" $
      checkForArity [2..3] prop_passesSTest
    prop "divides all original generators" $ do
      checkForArity [2..3] prop_groebnerDivsOrig
    it "generates the same ideal as original" $ do
      pendingWith "need example"
    it "contains the original ideal" $ checkForArity [1..3] $ \ari ->
      forAll (idealOfDim ari) $ \i ->
      forAll (vectorOf (length $ generators i) $ polyOfDim ari) $ \fs ->
      let f = sum $ zipWith (*) fs (generators i)
          gs = calcGroebnerBasis i
      in f `modPolynomial` gs == 0
    it "produces minimal basis" $ do
      checkForArity [2..3] prop_isMinimal
    it "produces reduced basis" $ do
      checkForArity [2..3] prop_isReduced
  describe "isIdealMember" $ do
    it "determins membership correctly" $ do
      pendingWith "need example"
  describe "intersection" $ modifyMaxSize (const 3) $ modifyMaxSuccess (const 50) $ do
    it "can calculate correctly" $ do
      checkForArity [2..3] prop_intersection
    it "can solve test-cases correctly" $ do
      forM_ ics_binary $ \(IC i j ans) ->
        intersection (toIdeal i :- toIdeal j :- Nil) `shouldBe` toIdeal ans

prop_intersection :: SingRep n => SNat n -> Property
prop_intersection sdim =
  forAll (idealOfDim sdim) $ \ideal ->
  forAll (idealOfDim sdim) $ \jdeal ->
  forAll (polyOfDim sdim) $ \f ->
  (f `isIdealMember` ideal && f `isIdealMember` jdeal)
  == f `isIdealMember` (intersection $ ideal :- jdeal :- Nil)

prop_isMinimal :: SingRep n => SNat n -> Property
prop_isMinimal sdim =
  forAll (idealOfDim sdim) $ \ideal ->
  let gs = calcGroebnerBasis ideal
  in all ((== 1) . leadingCoeff) gs &&
     all (\f -> all (\g -> not $ leadingMonomial g `divs` leadingMonomial f) (delete f gs)) gs

prop_isReduced :: SingRep n => SNat n -> Property
prop_isReduced sdim =
  forAll (idealOfDim sdim) $ \ideal ->
  let gs = calcGroebnerBasis ideal
  in all ((== 1) . leadingCoeff) gs &&
     all (\f -> all (\g -> all (\(_, m) -> not $ leadingMonomial g `divs` m) $ getTerms f) (delete f gs)) gs

prop_passesSTest :: SingRep n => SNat n -> Property
prop_passesSTest sdim =
  forAll (sized $ \size -> vectorOf size (polyOfDim sdim)) $ \ideal ->
  let gs = calcGroebnerBasis $ toIdeal ideal
  in all ((== 0) . (`modPolynomial` gs)) [sPolynomial f g | f <- gs, g <- gs, f /= g]

prop_groebnerDivsOrig :: SingRep n => SNat n -> Property
prop_groebnerDivsOrig sdim =
  forAll (elements [3..15]) $ \count ->
  forAll (vectorOf count (polyOfDim sdim)) $ \ideal ->
  let gs = calcGroebnerBasis $ toIdeal ideal
  in all ((== 0) . (`modPolynomial` gs)) ideal

prop_divCorrect :: SingRep n => SNat n -> Property
prop_divCorrect sdim =
  forAll (polyOfDim sdim) $ \poly ->
  forAll (idealOfDim sdim) $ \ideal ->
  let dvs = generators ideal
      (qds, r) = poly `divModPolynomial` dvs
  in poly == sum (map (uncurry (*)) qds) + r

prop_indivisible :: SingRep n => SNat n -> Property
prop_indivisible sdim =
  forAll (polyOfDim sdim) $ \poly ->
  forAll (idealOfDim sdim) $ \ideal ->
  let dvs = generators ideal
      (_, r) = changeOrder Grevlex poly `divModPolynomial` dvs
  in r /= 0 ==> all (\f -> all (\(_, m) -> not $ leadingMonomial f `divs` m) $ getTerms r)  dvs

prop_degdecay :: SingRep n => SNat n -> Property
prop_degdecay sdim =
  forAll (polyOfDim sdim) $ \poly ->
  forAll (idealOfDim sdim) $ \ideal ->
  let dvs = generators ideal
      (qs, _) = poly `divModPolynomial` dvs
  in all (\(a, f) -> (a * f == 0) || (leadingMonomial poly >= leadingMonomial (a * f))) qs

data IntersectCase r ord n = IC [OrderedPolynomial r ord n] [OrderedPolynomial r ord n] [OrderedPolynomial r ord n]

ics_binary :: [IntersectCase Rational Grevlex Two]
ics_binary =
  let [x, y] = SV.toList allVars
  in [IC [x*y] [y] [x*y]]
