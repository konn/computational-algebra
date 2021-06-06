{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Algebra.Algorithms.Groebner.SignatureSpec where

import Algebra.Algorithms.Groebner
import Algebra.Algorithms.Groebner.Signature
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
import Algebra.Ring.Polynomial.Labeled
import Control.Monad
import qualified Data.Foldable as F
import Data.List (delete)
import qualified Data.Sized as SV
import qualified Data.Vector as V
import Numeric.Field.Fraction (Fraction)
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Utils

asGenListOf :: Gen [a] -> a -> Gen [a]
asGenListOf = const

newtype Calc = Calc {runCalc :: forall poly. (Field (Coefficient poly), IsOrderedPolynomial poly) => Ideal poly -> [poly]}

f5Calcs :: [(String, Calc)]
f5Calcs =
  [ ("f5", Calc f5)
  , ("f5With pot", Calc $ f5With (Proxy @POT))
  , ("f5With top", Calc $ f5With (Proxy @TOP))
  ,
    ( "f5With term-w-pot"
    , Calc $ withTermWeights (Proxy @POT) (\pxy -> f5With pxy . toIdeal . V.toList) . V.fromList . generators
    )
  ,
    ( "f5With term-w-top"
    , Calc $ withTermWeights (Proxy @TOP) (\pxy -> f5With pxy . toIdeal . V.toList) . V.fromList . generators
    )
  ,
    ( "f5With deg-w-pot"
    , Calc $ withDegreeWeights (Proxy @POT) (\pxy -> f5With pxy . toIdeal . V.toList) . V.fromList . generators
    )
  ,
    ( "f5With deg-w-top"
    , Calc $ withDegreeWeights (Proxy @TOP) (\pxy -> f5With pxy . toIdeal . V.toList) . V.fromList . generators
    )
  ]

test_f5 :: TestTree
test_f5 =
  testGroup "f5" $
    [ testGroup
      name
      [ testProperty "passes S-test" $
          withMaxSuccess 25 $
            mapSize (const 4) $
              checkForTypeNat [2 .. 3] $ chkPassesSTest calc
      , testProperty "passes S-test (regression)" $
          withMaxSuccess 25 $
            mapSize (const 4) $
              once $ conjoin [counterexample (show ideal) $ passesSTest calc ideal | SomeIdeal ideal <- regression]
      , testProperty "includes the original ideal" $
          withMaxSuccess 25 $
            mapSize (const 4) $
              checkForTypeNat [2 .. 3] $ chkGroebnerDivsOrig calc
      , testProperty "includes the original ideal (regression)" $
          withMaxSuccess 25 $
            mapSize (const 4) $
              once $
                once $ conjoin [counterexample (show ideal) $ groebnerDivsOrig calc ideal | SomeIdeal ideal <- regression]
      , testProperty "is included in the orignal ideal" $
          withMaxSuccess 25 $
            mapSize (const 4) $
              checkForTypeNat [2 .. 3] $ chkGroebnerIncluded calc
      , testProperty "is included in the orignal ideal (regression)" $
          withMaxSuccess 25 $
            mapSize (const 4) $
              once $ conjoin [counterexample (show ideal) $ groebnerIncluded calc ideal | SomeIdeal ideal <- regression]
      ]
    | (name, Calc calc) <- f5Calcs
    ]

data SomeIdeal where
  SomeIdeal :: (Show poly, Field (Coefficient poly), IsSingularPolynomial poly) => [poly] -> SomeIdeal

type QQxy = LabPolynomial' Rational Grevlex '["x", "y"]

type QQxyz = LabPolynomial' Rational Grevlex '["x", "y", "z"]

regression :: [SomeIdeal]
regression =
  [ SomeIdeal @QQxyz
      [ 2 * #x ^ 2 * #y * #z ^ 2 - (3 % 4) * #x ^ 2 * #y * #z
      , 3 * #x ^ 3 * #y ^ 3 * #z ^ 2 - 3 * #x ^ 2 * #y ^ 3 * #z ^ 4
      , -3 * #x ^ 2 * #z + 2 * #y ^ 4 * #z ^ 3 - (1 % 3)
      ]
  , SomeIdeal @QQxy
      [ -2 * #x * #y ^ 2 - (2 % 3) * #y
      , - (1 % 3) * #x ^ 3 * #y - (1 % 3) * #x ^ 3 - 2 * #y ^ 4
      , - #x ^ 3 * #y ^ 4 + 2 * #y ^ 4
      ]
  , SomeIdeal @QQxyz
      [ (2 % 3) * #x ^ 4 * #y ^ 4 * #z ^ 4 - (1 % 3) * #x * #y * #z ^ 4
      , - (1 % 2) * #x ^ 3 * #y ^ 3 * #z + 3 * #x * #z ^ 3
      , -2 * #x ^ 4 * #y ^ 3 * #z ^ 4 + 2 * #x ^ 3 * #y ^ 2 * #z ^ 4 - 3 * #x * #y ^ 2
      ]
  , SomeIdeal @QQxy
      [ 2 * #x ^ 4 * #y + (2 % 3) * #x ^ 3 * #y ^ 2
      , (2 % 3) * #x ^ 3 * #y ^ 4 + (3 % 4) * #x * #y ^ 2
      , -3 * #y
      , (1 % 3) * #x ^ 2 * #y + (3 % 2) * #x * #y ^ 2
      , -3 * #x ^ 4 * #y ^ 2 - (1 % 3) * #x ^ 4 + 2 * #x ^ 3 * #y
      ]
  , SomeIdeal @QQxy
      [ (1 % 3) * #x
      , - (1 % 2) * #x ^ 4 * #y ^ 3 - (3 % 4) * #x ^ 2 * #y ^ 2 + (3 % 4) * #y ^ 4
      , (2 % 3) * #x ^ 2 * #y ^ 4 - 3 * #x * #y + 3 * #y
      , - (3 % 4) * #x ^ 2 * #y - (1 % 2) * #x * #y ^ 4
      , - (2 % 3) * #x ^ 4 * #y ^ 3 - 3
      ]
  , SomeIdeal @QQxyz
      [ - (3 % 4) * #x ^ 3 * #y ^ 2 * #z + 3 * #x ^ 2 * #y ^ 3 * #z ^ 2 - (2 % 3) * #z ^ 2
      , (3 % 4) * #x * #y ^ 2 * #z - (1 % 3) * #x - (2 % 5) * #y ^ 4 * #z ^ 2
      , (1 % 2) * #x ^ 4 * #y ^ 4 * #z ^ 4 + (2 % 3) * #x * #y ^ 3 * #z
      ]
  ]

chkPassesSTest ::
  (Ideal (Polynomial Rational n) -> [Polynomial Rational n]) ->
  SNat n ->
  Property
chkPassesSTest calc sdim =
  withKnownNat sdim $
    forAll (sized $ \size -> vectorOf size (polynomialOfArity sdim)) $ passesSTest calc

passesSTest :: (Field (Coefficient poly), IsOrderedPolynomial poly) => (Ideal poly -> [poly]) -> [poly] -> Bool
passesSTest calc ideal =
  let gs = calc $ toIdeal ideal
   in all (isZero . (`modPolynomial` gs)) [sPolynomial f g | f <- gs, g <- gs, f /= g]

chkGroebnerDivsOrig ::
  (Ideal (Polynomial Rational n) -> [Polynomial Rational n]) ->
  SNat n ->
  Property
chkGroebnerDivsOrig calc sdim = withKnownNat sdim $
  forAll (elements [3 .. 5]) $ \count ->
    forAll (vectorOf count (polynomialOfArity sdim)) $ groebnerDivsOrig calc

groebnerDivsOrig ::
  (IsOrderedPolynomial r, Euclidean (Coefficient r), Division (Coefficient r), Functor t, Foldable t) =>
  (Ideal r -> t r) ->
  [r] ->
  Bool
groebnerDivsOrig calc ideal =
  let gs = calc $ toIdeal ideal
   in all (isZero . (`modPolynomial` gs)) ideal

chkGroebnerIncluded ::
  (Ideal (Polynomial Rational n) -> [Polynomial Rational n]) ->
  SNat n ->
  Property
chkGroebnerIncluded calc sdim = withKnownNat sdim $
  forAll (elements [3 .. 5]) $ \count ->
    forAll (vectorOf count (polynomialOfArity sdim)) $ groebnerIncluded calc

groebnerIncluded :: (IsSingularPolynomial r) => (Ideal r -> [r]) -> [r] -> Property
groebnerIncluded calc ideal = ioProperty $ do
  let gs = calc $ toIdeal ideal
  is <-
    evalSingularIdealWith [] [] $
      funE "reduce" [idealE' $ toIdeal gs, funE "groebner" [idealE' $ toIdeal ideal]]
  pure $ all isZero is
