{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Algebra.Ring.PolynomialSpec where

import Algebra.Algorithms.Groebner
import Algebra.Internal
import Algebra.Ring.Ideal
import Algebra.Ring.Polynomial
import qualified Data.Matrix as M
import qualified Data.Vector as V
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Utils

asGenListOf :: Gen [a] -> a -> Gen [a]
asGenListOf = const

prop_passesSTest :: Property
prop_passesSTest = forAll (elements [1 .. 5]) $ \n ->
  case toSomeSNat n of
    (SomeSNat (sdim :: SNat n)) -> withKnownNat sdim $
      forAll (elements [3 .. 15]) $ \count ->
        forAll (vectorOf count (ratPolynomialOfArity sdim)) $ \ideal ->
          let gs = calcGroebnerBasis $ toIdeal ideal
           in all ((== 0) . (`modPolynomial` gs)) [sPolynomial f g | f <- gs, g <- gs, f /= g]

prop_groebnerDivsOrig :: Property
prop_groebnerDivsOrig = forAll (elements [1 .. 5]) $ \n -> case toSomeSNat n of
  SomeSNat (sdim :: SNat n) ->
    withKnownNat sdim $
      forAll (elements [3 .. 15]) $ \count ->
        forAll (vectorOf count (ratPolynomialOfArity sdim)) $ \ideal ->
          let gs = calcGroebnerBasis $ toIdeal ideal
           in all ((== 0) . (`modPolynomial` gs)) ideal

prop_divCorrect :: Property
prop_divCorrect = forAll (elements [1 .. 5]) $ \n -> case toSomeSNat n of
  SomeSNat (sdim :: SNat n) ->
    withKnownNat sdim $
      forAll (ratPolynomialOfArity sdim) $ \poly ->
        forAll (idealOfArity sdim) $ \ideal ->
          let dvs = generators ideal
              (qds, r) = poly `divModPolynomial` dvs
           in poly == sum (map (uncurry (*)) qds) + r

prop_indivisible :: Property
prop_indivisible = forAll (elements [1 .. 5]) $ \n -> case toSomeSNat n of
  SomeSNat (sdim :: SNat n) ->
    withKnownNat sdim $
      forAll (ratPolynomialOfArity sdim) $ \poly ->
        forAll (idealOfArity sdim) $ \ideal ->
          let dvs = generators ideal
              (_, r) = changeOrder Grevlex poly `divModPolynomial` dvs
           in r /= 0 ==> all (\f -> all (\(_, m) -> not $ leadingMonomial f `divs` m) $ getTerms r) dvs

prop_degdecay :: Property
prop_degdecay = forAll (elements [1 .. 5]) $ \n -> case toSomeSNat n of
  SomeSNat (sdim :: SNat n) ->
    withKnownNat sdim $
      forAll (ratPolynomialOfArity sdim) $ \poly ->
        forAll (idealOfArity sdim) $ \ideal ->
          let dvs = generators ideal
              (qs, _) = poly `divModPolynomial` dvs
           in all (\(a, f) -> (a * f == 0) || (leadingMonomial poly >= leadingMonomial (a * f))) qs

rank :: (Ord r, Fractional r) => M.Matrix r -> Int
rank mat =
  let Just (u, _, _, _, _, _) = M.luDecomp' mat
   in V.foldr (\a acc -> if a /= 0 then acc + 1 else acc) (0 :: Int) $ M.getDiag u
