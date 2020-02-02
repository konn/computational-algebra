{-# LANGUAGE DataKinds, ExplicitNamespaces, GADTs, NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms, ScopedTypeVariables, TypeApplications  #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
module GroebnerSpec where
import Algebra.Algorithms.Groebner
import Algebra.Internal            (pattern (:<), KnownNat, pattern NilL, SNat)
import Algebra.Prelude.Core        hiding ((===))
import Algebra.Ring.Ideal
import Algebra.Ring.Polynomial
import Utils

import           Control.Monad
import qualified Data.Foldable            as F
import           Data.List                (delete, tails)
import qualified Data.Sized.Builtin       as SV
import           Numeric.Field.Fraction   (Fraction)
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck
import           Test.QuickCheck.Property

asGenListOf :: Gen [a] -> a -> Gen [a]
asGenListOf = const

type Microsecs = Int
minutes, seconds :: Int -> Microsecs
seconds n = n * 1000000
minutes n = n * seconds 60

setSize :: Testable prop => Int -> prop -> Property
setSize n p =  MkProperty (sized ((`resize` unProperty (property p)) . const n))

spec :: Spec
spec = parallel $ do
  describe "divModPolynomial" $ modifyMaxSize (const 10) $ modifyMaxSuccess (const 10) $ do
    prop "remainder cannot be diveided by any denoms (ternary)" $
      within (minutes 5) $ checkForTypeNat [1..4] prop_indivisible
    prop "satisfies a_i f_i /= 0 ==> deg(f) >= deg (a_i f_i)" $
      within (minutes 5) $ checkForTypeNat [1..4] prop_degdecay
    prop "divides correctly" $
      within (minutes 5) $ checkForTypeNat [1..4] prop_divCorrect
  describe "modPolynomial" $ modifyMaxSize (const 10) $ modifyMaxSuccess (const 10) $
    prop "Generates the same remainder as divModPolynomial" $
      within (minutes 5) $ checkForTypeNat [1..4] $ \(sdim :: SNat n) ->
      forAll (ratPolynomialOfArity sdim) $ \poly ->
      forAll (idealOfArity sdim) $ \ideal ->
        let gs = F.toList ideal
        in (poly `modPolynomial` gs) === snd (divModPolynomial poly gs)
  describe "calcGroebnerBasis" $ modifyMaxSize (const 5) $ modifyMaxSuccess (const 10) $ do
    prop "passes S-test" $
      setSize 3 $
      within (minutes 5) $ checkForTypeNat [2..3] prop_passesSTest
    prop "passes S-test (regression)" $ once $
      conjoin [ counterexample (show i) $ passesSTest i
              | SomeIdeal i <- gbRegress
              ]
    prop "divides all original generators" $
      within (minutes 5) $ checkForTypeNat [2..3] prop_groebnerDivsOrig
    it "generates the same ideal as original" $
      pendingWith "need example"
    it "produces minimal basis" $
      within (minutes 5) $ checkForTypeNat [2..3] prop_isMinimal
    it "produces reduced basis" $
      within (minutes 5) $ checkForTypeNat [2..3] prop_isReduced
  describe "isIdealMember" $
    it "determins membership correctly" $
    pendingWith "need example"
  describe "intersection" $ modifyMaxSize (const 4) $ modifyMaxSuccess (const 25) $ do
    it "can calculate correctly" $
      within (minutes 5) $ checkForTypeNat [2..3] prop_intersection
    it "can solve test-cases correctly" $
      forM_ ics_binary $ \(IC i j ans) ->
      F.toList (intersection [toIdeal i, toIdeal j]) `shouldBe` ans

prop_intersection :: KnownNat n => SNat n -> Property
prop_intersection sdim =
  forAll (idealOfArity sdim) $ \ideal ->
  forAll (idealOfArity sdim) $ \jdeal ->
  forAll (ratPolynomialOfArity sdim) $ \f ->
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
  forAll (sized $ \size -> vectorOf size (ratPolynomialOfArity sdim)) passesSTest

passesSTest :: (Field (Coefficient poly), IsOrderedPolynomial poly) => [poly] -> Bool
passesSTest ideal =
  let gs = calcGroebnerBasis $ toIdeal ideal
  in all (isZero . (`modPolynomial` gs)) [sPolynomial f g | (f : fs) <- init $ tails gs, g <- fs]

prop_groebnerDivsOrig :: KnownNat n => SNat n -> Property
prop_groebnerDivsOrig sdim =
  forAll (elements [3..15]) $ \count ->
  forAll (vectorOf count (ratPolynomialOfArity sdim)) $ \ideal ->
  let gs = calcGroebnerBasis $ toIdeal ideal
  in all ((== 0) . (`modPolynomial` gs)) ideal

prop_divCorrect :: KnownNat n => SNat n -> Property
prop_divCorrect sdim =
  forAll (ratPolynomialOfArity sdim) $ \poly ->
  forAll (idealOfArity sdim) $ \ideal ->
  let dvs = generators ideal
      (qds, r) = poly `divModPolynomial` dvs
  in poly == sum (map (uncurry (*)) qds) + r

prop_indivisible :: KnownNat n => SNat n -> Property
prop_indivisible sdim =
  forAll (ratPolynomialOfArity sdim) $ \poly ->
  forAll (idealOfArity sdim) $ \ideal ->
  let dvs = generators ideal
      (_, r) = changeOrder Grevlex poly `divModPolynomial` dvs
  in r /= 0 ==> all (\f -> all (\(_, m) -> not $ leadingMonomial f `divs` m) $ getTerms r)  dvs

prop_degdecay :: KnownNat n => SNat n -> Property
prop_degdecay sdim =
  forAll (ratPolynomialOfArity sdim) $ \poly ->
  forAll (idealOfArity sdim) $ \ideal ->
  let dvs = generators ideal
      (qs, _) = poly `divModPolynomial` dvs
  in all (\(a, f) -> (a * f == 0) || (leadingMonomial poly >= leadingMonomial (a * f))) qs

data IntersectCase r ord n = IC [OrderedPolynomial r ord n] [OrderedPolynomial r ord n] [OrderedPolynomial r ord n]

ics_binary :: [IntersectCase (Fraction Integer) Grevlex 2]
ics_binary =
  let [x, y] = F.toList allVars
  in [IC [x*y] [y] [x*y]]

data SomeIdeal where
  SomeIdeal :: (Show poly, Field (Coefficient poly), IsOrderedPolynomial poly) => [poly] -> SomeIdeal

gbRegress :: [SomeIdeal]
gbRegress =
  [ let [x,y,z] = vars
    in SomeIdeal @(OrderedPolynomial Rational Grevlex 3)
       [ x * y ^3* z ^4
       , (1 % 3) * x ^3* y ^4* z ^2 + 3* x * y ^2* z ^4
       , - x ^3* y ^3* z ^3 +  x ^4* y * z ^4]
  ]
