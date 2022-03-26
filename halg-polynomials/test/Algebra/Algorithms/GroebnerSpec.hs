{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Algebra.Algorithms.GroebnerSpec where

import Algebra.Algorithms.Groebner
import Algebra.Internal (KnownNat, SNat, pattern Nil, pattern (:<))
import Algebra.Prelude.Core hiding ((===))
import Algebra.Ring.Ideal
import Algebra.Ring.Polynomial
import Control.Monad
import qualified Data.Foldable as F
import Data.List (delete, tails)
import qualified Data.Sized as SV
import Numeric.Field.Fraction (Fraction)
import Test.Tasty
import Test.Tasty.ExpectedFailure (expectFail, ignoreTestBecause)
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Utils

asGenListOf :: Gen [a] -> a -> Gen [a]
asGenListOf = const

type Microsecs = Int

minutes, seconds :: Int -> Microsecs
seconds n = n * 1000000
minutes n = n * seconds 60

test_divModPolynomial :: TestTree
test_divModPolynomial =
  testGroup
    "divModPolynomial"
    [ testProperty "remainder cannot be diveided by any denoms (ternary)" $
        withMaxSuccess 10 $
          setSize 10 $
            within (minutes 5) $ checkForTypeNat [1 .. 4] checkindivisible
    , testProperty "satisfies a_i f_i /= 0 ==> deg(f) >= deg (a_i f_i)" $
        withMaxSuccess 10 $
          setSize 10 $
            within (minutes 5) $ checkForTypeNat [1 .. 4] checkdegdecay
    , testProperty "divides correctly" $
        withMaxSuccess 10 $
          setSize 10 $
            within (minutes 5) $ checkForTypeNat [1 .. 4] checkdivCorrect
    ]

-- spec :: Spec
test_modPolynomial :: TestTree
test_modPolynomial =
  testGroup
    "modPolynomial"
    [ testProperty "Generates the same remainder as divModPolynomial" $
        setSize 10 $
          withMaxSuccess 10 $
            within (minutes 5) $
              checkForTypeNat [1 .. 4] $ \(sdim :: SNat n) ->
                forAll (ratPolynomialOfArity sdim) $ \poly ->
                  forAll (idealOfArity sdim) $ \ideal ->
                    let gs = F.toList ideal
                     in (poly `modPolynomial` gs) === snd (divModPolynomial poly gs)
    ]

test_calcGroebnerBasis :: TestTree
test_calcGroebnerBasis =
  testGroup "calcGroebnerBasis" $
    [ testProperty "passes S-test" $
        setSize 3 $
          withMaxSuccess 10 $
            within (minutes 5) $ checkForTypeNat [2 .. 3] checkpassesSTest
    , testProperty "passes S-test (regression)" $
        once $
          conjoin
            [ counterexample (show i) $ passesSTest i
            | SomeIdeal i <- gbRegress
            ]
    , testProperty "divides all original generators" $
        withMaxSuccess 10 $
          setSize 5 $
            within (minutes 5) $ checkForTypeNat [2 .. 3] checkgroebnerDivsOrig
    , expectFail $
        testCase "generates the same ideal as original" $
          assertFailure "need example"
    , testProperty "produces minimal basis" $
        withMaxSuccess 10 $
          setSize 5 $
            within (minutes 5) $ checkForTypeNat [2 .. 3] checkisMinimal
    , testProperty "produces reduced basis" $
        withMaxSuccess 10 $
          setSize 5 $
            within (minutes 5) $ checkForTypeNat [2 .. 3] checkisReduced
    ]

test_isIdealMember :: TestTree
test_isIdealMember =
  testGroup
    "isIdealMember"
    [ expectFail $
        testCase "determins membership correctly" $
          assertFailure "not implemented"
    ]

test_intersection :: TestTree
test_intersection =
  testGroup
    "intersection"
    [ testProperty "can calculate correctly" $
        setSize 4 $
          withMaxSuccess 25 $
            within (minutes 5) $ checkForTypeNat [2 .. 3] checkintersection
    , testCase "can solve test-cases correctly" $
        forM_ icsBinary $ \(IC i j ans) ->
          F.toList (intersection [toIdeal i, toIdeal j]) @?= ans
    ]

checkintersection :: KnownNat n => SNat n -> Property
checkintersection sdim =
  forAll (idealOfArity sdim) $ \ideal ->
    forAll (idealOfArity sdim) $ \jdeal ->
      forAll (ratPolynomialOfArity sdim) $ \f ->
        (f `isIdealMember` ideal && f `isIdealMember` jdeal)
          == f `isIdealMember` intersection [ideal, jdeal]

checkisMinimal :: KnownNat n => SNat n -> Property
checkisMinimal sdim =
  forAll (idealOfArity sdim) $ \ideal ->
    let gs = calcGroebnerBasis ideal
     in all ((== 1) . leadingCoeff) gs
          && all (\f -> all (\g -> not $ leadingMonomial g `divs` leadingMonomial f) (delete f gs)) gs

checkisReduced :: KnownNat n => SNat n -> Property
checkisReduced sdim =
  forAll (idealOfArity sdim) $ \ideal ->
    let gs = calcGroebnerBasis ideal
     in all ((== 1) . leadingCoeff) gs
          && all (\f -> all (\g -> all (\(_, m) -> not $ leadingMonomial g `divs` m) $ getTerms f) (delete f gs)) gs

checkpassesSTest :: KnownNat n => SNat n -> Property
checkpassesSTest sdim =
  forAll (sized $ \size -> vectorOf size (ratPolynomialOfArity sdim)) passesSTest

passesSTest :: (Field (Coefficient poly), IsOrderedPolynomial poly) => [poly] -> Bool
passesSTest ideal =
  let gs = calcGroebnerBasis $ toIdeal ideal
   in all (isZero . (`modPolynomial` gs)) [sPolynomial f g | (f : fs) <- init $ tails gs, g <- fs]

checkgroebnerDivsOrig :: KnownNat n => SNat n -> Property
checkgroebnerDivsOrig sdim =
  forAll (elements [3 .. 15]) $ \count ->
    forAll (vectorOf count (ratPolynomialOfArity sdim)) $ \ideal ->
      let gs = calcGroebnerBasis $ toIdeal ideal
       in all ((== 0) . (`modPolynomial` gs)) ideal

checkdivCorrect :: KnownNat n => SNat n -> Property
checkdivCorrect sdim =
  forAll (ratPolynomialOfArity sdim) $ \poly ->
    forAll (idealOfArity sdim) $ \ideal ->
      let dvs = generators ideal
          (qds, r) = poly `divModPolynomial` dvs
       in poly == sum (map (uncurry (*)) qds) + r

checkindivisible :: KnownNat n => SNat n -> Property
checkindivisible sdim =
  forAll (ratPolynomialOfArity sdim) $ \poly ->
    forAll (idealOfArity sdim) $ \ideal ->
      let dvs = generators ideal
          (_, r) = changeOrder Grevlex poly `divModPolynomial` dvs
       in r /= 0 ==> all (\f -> all (\(_, m) -> not $ leadingMonomial f `divs` m) $ getTerms r) dvs

checkdegdecay :: KnownNat n => SNat n -> Property
checkdegdecay sdim =
  forAll (ratPolynomialOfArity sdim) $ \poly ->
    forAll (idealOfArity sdim) $ \ideal ->
      let dvs = generators ideal
          (qs, _) = poly `divModPolynomial` dvs
       in all (\(a, f) -> (a * f == 0) || (leadingMonomial poly >= leadingMonomial (a * f))) qs

data IntersectCase r ord n = IC [OrderedPolynomial r ord n] [OrderedPolynomial r ord n] [OrderedPolynomial r ord n]

icsBinary :: [IntersectCase (Fraction Integer) Grevlex 2]
icsBinary =
  let [x, y] = F.toList allVars
   in [IC [x * y] [y] [x * y]]

data SomeIdeal where
  SomeIdeal :: (Show poly, Field (Coefficient poly), IsOrderedPolynomial poly) => [poly] -> SomeIdeal

gbRegress :: [SomeIdeal]
gbRegress =
  [ let [x, y, z] = vars
     in SomeIdeal @(OrderedPolynomial Rational Grevlex 3)
          [ x * y ^ 3 * z ^ 4
          , (1 % 3) * x ^ 3 * y ^ 4 * z ^ 2 + 3 * x * y ^ 2 * z ^ 4
          , -x ^ 3 * y ^ 3 * z ^ 3 + x ^ 4 * y * z ^ 4
          ]
  ]
