{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Algebra.Ring.Polynomial.UnivariateSpec where

import Algebra.Field.Prime
import Algebra.Prelude.Core hiding ((===))
import Algebra.Ring.Euclidean.Quotient (Quotient)
import Algebra.Ring.Polynomial.Univariate
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Utils

asGenListOf :: Gen [a] -> a -> Gen [a]
asGenListOf = const

toOP :: Unipol Integer -> OrderedPolynomial Integer Grevlex 1
toOP = injectVars

liftMult :: Unipol Integer -> Unipol Integer -> Unipol Integer
liftMult f g =
  let (f', g') = (toOP f, toOP g)
   in injectVars (f' * g')

test_naiveMult :: TestTree
test_naiveMult =
  testGroup
    "naiveMult"
    [ testProperty "Works as expected" $
        setSize 5 $
          withMaxSuccess 10 $ \f g ->
            (f `naiveMult` g) == (f `liftMult` g)
    ]

test_karatsuba :: TestTree
test_karatsuba =
  testGroup
    "karatsuba"
    [ testProperty "Works as expected" $ \f g ->
        setSize 5 $
          withMaxSuccess 25 $
            karatsuba f g == (f `liftMult` g)
    ]

test_divModUnipolByMult :: TestTree
test_divModUnipolByMult =
  testGroup
    "divModUnipolByMult"
    [ testProperty "remainder has degree smaller than divisor" $
        setSize 5 $
          withMaxSuccess 25 $ \f g ->
            let (_, r) = divModUnipolByMult f (g :: Unipol (F 5))
             in (totalDegree' f > 0 && totalDegree' g > 0)
                  ==> totalDegree' r < totalDegree' g
    , testProperty "divides correctly" $
        setSize 5 $
          withMaxSuccess 25 $ \f g ->
            let (q, r) = divModUnipolByMult f (g :: Unipol (F 5))
             in not (isZero g) ==> q * g + r === f
    , testCase "passes regression tests" $
        mapM_
          (\((a, b), (c, d)) -> divModUnipolByMult a b @?= (c, d))
          divModUnipolCases
    ]

test_divModUnipol :: TestTree
test_divModUnipol =
  testGroup
    "divModUnipol"
    [ testProperty "remainder has degree smaller than divisor" $
        setSize 5 $
          withMaxSuccess 25 $ \f g ->
            let (_, r) = divModUnipol f (g :: Unipol (F 5))
             in totalDegree' f > 0 && totalDegree' g > 0
                  ==> totalDegree' r < totalDegree' g
    , testProperty "divides correctly" $
        setSize 5 $
          withMaxSuccess 25 $ \f g ->
            let (q, r) = divModUnipol f (g :: Unipol (F 5))
             in not (isZero g)
                  ==> q * g + r == f
    ]

test_operations :: TestTree
test_operations =
  testGroup
    "Normal forms"
    [ testProperty "addition preserves normal form (F_17)" $ \f g ->
        isNormalForm (f + g :: Unipol (F 17))
    , testProperty "addition preserves normal form (Q)" $ \f g ->
        isNormalForm (f + g :: Unipol Rational)
    , testProperty "subtraction preserves normal form (Q)" $ \f g ->
        isNormalForm (f - g :: Unipol Rational)
    , testProperty "subtraction preserves normal form (F_17)" $ \f g ->
        isNormalForm (f - g :: Unipol (F 17))
    , testProperty "f - f is normal form (F_17)" $ \f ->
        isNormalForm (f - f :: Unipol (F 17))
    , testProperty "f - f is normal form (Q)" $ \f ->
        isNormalForm (f - f :: Unipol Rational)
    , testProperty "division preserves normal form (Q)" $
        withMaxSuccess 25 $
          \(NonZero f) (NonZero g) ->
            let [f', g'] = sortOn (Down . leadingMonomial) [f, g :: Unipol Rational]
                (q, r) = f' `divModUnipol` g'
             in isNormalForm q .&&. isNormalForm r
    , testProperty "division preserves normal form (F_17)" $ \(NonZero f) (NonZero g) ->
        let [f', g'] = sortOn (Down . leadingMonomial) [f, g :: Unipol (F 17)]
            (q, r) = f' `divModUnipol` g'
         in isNormalForm q .&&. isNormalForm r
    , testProperty "splitLeadingTerm preserves normal form (Q)" $ \f ->
        let (_, g) = splitLeadingTerm (f :: Unipol Rational)
         in isNormalForm g
    , testProperty "multiplication preserves normal form (F_5)" $
        setSize 10 $
          withMaxSuccess 25 $ \f g ->
            tabulate "# of terms" (map (show . length . terms) [f, g]) $
              isNormalForm (f * g :: Unipol (F 5))
    , testProperty "f + f + f + f + f = 0 and it's normal form (F_5)" $ \f ->
        let f5 = f + f + f + f + f :: Unipol (F 5)
         in f5 === 0 .&&. isNormalForm f5
    , testCase "2 x * 3x^2 = 0 and normal form (in Z/6Z)" $ do
        let mustBeZero = (2 * #x) * (3 * #x ^ 2) :: Unipol (Quotient 6 Integer)
        mustBeZero @?= 0
        assertBool "not normal form!" $ isNormalForm mustBeZero
    ]

divModUnipolCases :: [((Unipol (F 5), Unipol (F 5)), (Unipol (F 5), Unipol (F 5)))]
divModUnipolCases =
  [((3 * x ^ 57 + x ^ 56 + x ^ 55 + 2 * x ^ 52 + 2 * x ^ 51 + 4 * x ^ 50 + x ^ 49 + 4 * x ^ 48 + 3 * x ^ 47 + 4 * x ^ 46 + 3 * x ^ 45 + 3 * x ^ 44 + 3 * x ^ 42 + 3 * x ^ 41 + x ^ 40 + x ^ 39 + 2 * x ^ 38 + 3 * x ^ 37 + x ^ 36 + 2 * x ^ 35 + 4 * x ^ 34 + 3 * x ^ 33 + 4 * x ^ 32 + 3 * x ^ 31 + x ^ 30 + 3 * x ^ 28 + x ^ 26 + x ^ 25 + 3 * x ^ 24 + x ^ 22 + 4 * x ^ 21 + 3 * x ^ 20 + 2 * x ^ 19 + 4 * x ^ 18 + 4 * x ^ 17 + 2 * x ^ 16 + x ^ 15 + 3 * x ^ 13 + 2 * x ^ 12 + x ^ 11 + x ^ 10 + 4 * x ^ 9 + 4 * x ^ 8 + 2 * x ^ 7 + x ^ 6 + 2 * x ^ 5 + 4 * x ^ 4 + 2 * x ^ 3 + 2 * x ^ 2 + 3 * x + 4, 3 * x ^ 19 + 2 * x ^ 18 + 4 * x ^ 17 + 3 * x ^ 16 + 4 * x ^ 13 + 3 * x ^ 12 + x ^ 11 + 4 * x ^ 10 + 2 * x ^ 8 + 2 * x ^ 7 + 2 * x ^ 6 + 4 * x ^ 4 + 2 * x ^ 3 + 4 * x ^ 2 + 3 * x + 2), (x ^ 38 + 3 * x ^ 37 + 2 * x ^ 36 + 2 * x ^ 35 + 3 * x ^ 34 + 4 * x ^ 33 + 4 * x ^ 32 + 2 * x ^ 31 + 2 * x ^ 30 + 3 * x ^ 29 + 2 * x ^ 28 + 3 * x ^ 26 + x ^ 25 + x ^ 24 + 3 * x ^ 23 + 2 * x ^ 22 + 2 * x ^ 20 + 3 * x ^ 18 + 2 * x ^ 17 + 3 * x ^ 16 + 4 * x ^ 15 + x ^ 14 + 4 * x ^ 13 + 3 * x ^ 12 + 2 * x ^ 11 + 3 * x ^ 10 + 2 * x ^ 9 + 4 * x ^ 7 + 3 * x ^ 5 + 2 * x ^ 4 + 3 * x ^ 3 + 2 * x ^ 2 + x + 2, 2 * x ^ 18 + 4 * x ^ 17 + 3 * x ^ 16 + 2 * x ^ 15 + 4 * x ^ 14 + 4 * x ^ 12 + 2 * x ^ 11 + 4 * x ^ 10 + 3 * x ^ 8 + x ^ 6 + 3 * x ^ 4 + 2 * x ^ 3 + 2 * x ^ 2))]
  where
    x = var 0
