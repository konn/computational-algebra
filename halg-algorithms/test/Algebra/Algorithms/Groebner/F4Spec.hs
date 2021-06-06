{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Algebra.Algorithms.Groebner.F4Spec where

import Algebra.Algorithms.Groebner
import Algebra.Algorithms.Groebner.F4
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

test_f4 :: TestTree
test_f4 =
  testGroup
    "f4"
    [ testProperty "passes S-test" $
        withMaxSuccess 10 $
          mapSize (const 4) $
            checkForTypeNat [2 .. 3] $ passesSTest f4
    , testProperty "includes the original ideal" $
        withMaxSuccess 10 $
          mapSize (const 4) $
            checkForTypeNat [2 .. 3] $ groebnerDivsOrig f4
    , testProperty "is included in the orignal ideal" $
        withMaxSuccess 10 $
          mapSize (const 4) $
            checkForTypeNat [2 .. 3] $ groebnerIncluded f4
    ]

passesSTest ::
  (Ideal (Polynomial Rational n) -> [Polynomial Rational n]) ->
  SNat n ->
  Property
passesSTest calc sdim = withKnownNat sdim $
  forAll (sized $ \size -> vectorOf size (polynomialOfArity sdim)) $ \ideal ->
    let gs = calc $ toIdeal ideal
     in all (isZero . (`modPolynomial` gs)) [sPolynomial f g | f <- gs, g <- gs, f /= g]

groebnerDivsOrig ::
  (Ideal (Polynomial Rational n) -> [Polynomial Rational n]) ->
  SNat n ->
  Property
groebnerDivsOrig calc sdim = withKnownNat sdim $
  forAll (elements [3 .. 15]) $ \count ->
    forAll (vectorOf count (polynomialOfArity sdim)) $ \ideal ->
      let gs = calc $ toIdeal ideal
       in all (isZero . (`modPolynomial` gs)) ideal

groebnerIncluded ::
  (Ideal (Polynomial Rational n) -> [Polynomial Rational n]) ->
  SNat n ->
  Property
groebnerIncluded calc sdim = withKnownNat sdim $
  forAll (elements [3 .. 15]) $ \count ->
    forAll (vectorOf count (polynomialOfArity sdim)) $ \ideal -> ioProperty $ do
      let gs = calc $ toIdeal ideal
      is <-
        evalSingularIdealWith [] [] $
          funE "reduce" [idealE' $ toIdeal gs, funE "groebner" [idealE' $ toIdeal ideal]]
      pure $ all isZero is
