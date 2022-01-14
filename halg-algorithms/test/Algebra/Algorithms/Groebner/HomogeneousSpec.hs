{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Algebra.Algorithms.Groebner.HomogeneousSpec where

import Algebra.Algorithms.Groebner
import Algebra.Algorithms.Groebner.Homogeneous
import Algebra.Bridge.Singular
import Algebra.Internal
  ( KnownNat,
    SNat,
    sSucc,
    pattern Nil,
    pattern (:<),
  )
import Algebra.Prelude.Core
import Algebra.Ring.Ideal
import Algebra.Ring.Polynomial
import Algebra.Ring.Polynomial.Homogenised
import Control.Monad
import qualified Data.Foldable as F
import Data.List (delete)
import qualified Data.Sized as SV
import Numeric.Field.Fraction (Fraction)
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Utils

asGenListOf :: Gen [a] -> a -> Gen [a]
asGenListOf = const

test_calcHomogeneousGroebnerBasis :: TestTree
test_calcHomogeneousGroebnerBasis =
  testGroup
    "calcHomogeneousGroebnerBasis"
    [ testProperty "passes S-test" $
        withMaxSuccess 5 $
          mapSize (const 4) $
            checkForTypeNat [2 .. 3] $ passesSTestWith homogenise unsafeCalcHomogeneousGroebnerBasis
    , testProperty "includes the original ideal" $
        withMaxSuccess 5 $
          mapSize (const 4) $
            checkForTypeNat [2 .. 3] $ groebnerDivsOrigWith homogenise unsafeCalcHomogeneousGroebnerBasis
    , testProperty "is included in the orignal ideal" $
        withMaxSuccess 5 $
          mapSize (const 4) $
            checkForTypeNat [2 .. 3] $ groebnerIncludedWith homogenise unsafeCalcHomogeneousGroebnerBasis
    ]

test_calcHomogeneousGroebnerBasisHilbert :: TestTree
test_calcHomogeneousGroebnerBasisHilbert =
  testGroup
    "calcHomogeneousGroebnerBasisHilbert"
    [ testProperty "passes S-test" $
        withMaxSuccess 5 $
          mapSize (const 4) $
            checkForTypeNat [2 .. 3] $
              passesSTestWith
                (homogenise . changeOrder Lex)
                calcHomogeneousGroebnerBasisHilbert
    , testProperty "includes the original ideal" $
        withMaxSuccess 5 $
          mapSize (const 4) $
            checkForTypeNat [2 .. 3] $ groebnerDivsOrigWith (homogenise . changeOrder Lex) calcHomogeneousGroebnerBasisHilbert
    , testProperty "is included in the orignal ideal" $
        withMaxSuccess 5 $
          mapSize (const 4) $
            checkForTypeNat [2 .. 3] $ groebnerIncludedWith (homogenise . changeOrder Lex) calcHomogeneousGroebnerBasisHilbert
    ]

test_calcGroebnerBasisAfterHomogenising :: TestTree
test_calcGroebnerBasisAfterHomogenising =
  testGroup
    "calcGroebnerBasisAfterHomogenising"
    [ testProperty "passes S-test" $
        withMaxSuccess 25 $
          mapSize (const 4) $
            checkForTypeNat [2 .. 3] $ passesSTestWith id calcGroebnerBasisAfterHomogenising
    , testProperty "includes the original ideal" $
        withMaxSuccess 25 $
          mapSize (const 4) $
            checkForTypeNat [2 .. 3] $ groebnerDivsOrigWith id calcGroebnerBasisAfterHomogenising
    , testProperty "is included in the orignal ideal" $
        withMaxSuccess 25 $
          mapSize (const 4) $
            checkForTypeNat [2 .. 3] $ groebnerIncludedWith id calcGroebnerBasisAfterHomogenising
    ]

passesSTestWith ::
  ( KnownNat n
  , Coefficient poly' ~ Rational
  , IsOrderedPolynomial poly'
  , DecidableZero poly'
  ) =>
  (Polynomial Rational n -> poly') ->
  (Ideal poly' -> [poly']) ->
  SNat n ->
  Property
passesSTestWith prepro calc sdim =
  forAll (sized $ \size -> vectorOf size (polynomialOfArity sdim)) $ \ideal ->
    let gs = calc $ toIdeal $ map prepro ideal
     in all (isZero . (`modPolynomial` gs)) [sPolynomial f g | f <- gs, g <- gs, f /= g]

groebnerDivsOrigWith ::
  ( KnownNat n
  , Coefficient poly' ~ Rational
  , IsOrderedPolynomial poly'
  , DecidableZero poly'
  ) =>
  (Polynomial Rational n -> poly') ->
  (Ideal poly' -> [poly']) ->
  SNat n ->
  Property
groebnerDivsOrigWith prepro calc sdim =
  forAll (elements [3 .. 15]) $ \count ->
    forAll (vectorOf count (polynomialOfArity sdim)) $ \jdeal ->
      let ideal = map prepro jdeal
          gs = calc $ toIdeal ideal
       in all (isZero . (`modPolynomial` gs)) ideal

groebnerIncludedWith ::
  ( KnownNat n
  , Coefficient poly' ~ Rational
  , IsSingularPolynomial poly'
  , DecidableZero poly'
  ) =>
  (Polynomial Rational n -> poly') ->
  (Ideal poly' -> [poly']) ->
  SNat n ->
  Property
groebnerIncludedWith prepro calc sdim =
  forAll (elements [3 .. 15]) $ \count ->
    forAll (vectorOf count (polynomialOfArity sdim)) $ \jdeal -> ioProperty $ do
      let ideal = map prepro jdeal
          gs = calc $ toIdeal ideal
      is <-
        evalSingularIdealWith [] [] $
          funE "reduce" [idealE' $ toIdeal gs, funE "groebner" [idealE' $ toIdeal ideal]]
      pure $ all isZero is
