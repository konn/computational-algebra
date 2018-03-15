{-# LANGUAGE DataKinds, ExplicitNamespaces, GADTs, NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings, PatternSynonyms                      #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module HomogeneousSpec where
import           Algebra.Algorithms.Groebner
import           Algebra.Algorithms.Groebner.Homogeneous
import           Algebra.Bridge.Singular
import           Algebra.Internal                        (pattern (:<),
                                                          KnownNat,
                                                          pattern NilL, SNat,
                                                          sSucc)
import           Algebra.Prelude.Core
import           Algebra.Ring.Ideal
import           Algebra.Ring.Polynomial
import           Algebra.Ring.Polynomial.Homogenised
import           Control.Monad
import qualified Data.Foldable                           as F
import           Data.List                               (delete)
import qualified Data.Sized.Builtin                      as SV
import           Numeric.Field.Fraction                  (Fraction)
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.HUnit.Lang
import           Test.QuickCheck
import           Utils


asGenListOf :: Gen [a] -> a -> Gen [a]
asGenListOf = const

spec :: Spec
spec = do
  describe "calcHomogeneousGroebnerBasis" $ modifyMaxSize (const 4) $ modifyMaxSuccess (const 25) $ do
    prop "passes S-test" $
      checkForArity [2..3] $ prop_passesSTestWith homogenise unsafeCalcHomogeneousGroebnerBasis
    prop "includes the original ideal" $
      checkForArity [2..3] $ prop_groebnerDivsOrigWith homogenise unsafeCalcHomogeneousGroebnerBasis
    prop "is included in the orignal ideal" $
      checkForArity [2..3] $ prop_groebnerIncludedWith homogenise unsafeCalcHomogeneousGroebnerBasis
  describe "calcHomogeneousGroebnerBasisHilbert" $ modifyMaxSize (const 4) $ modifyMaxSuccess (const 25) $ do
    prop "passes S-test" $
      checkForArity [2..3] $ prop_passesSTestWith (homogenise . changeOrder Lex)
      calcHomogeneousGroebnerBasisHilbert
    prop "includes the original ideal" $
      checkForArity [2..3] $ prop_groebnerDivsOrigWith (homogenise . changeOrder Lex) calcHomogeneousGroebnerBasisHilbert
    prop "is included in the orignal ideal" $
      checkForArity [2..3] $ prop_groebnerIncludedWith (homogenise . changeOrder Lex) calcHomogeneousGroebnerBasisHilbert
  describe "calcGroebnerBasisAfterHomogenising" $ modifyMaxSize (const 4) $ modifyMaxSuccess (const 25) $ do
    prop "passes S-test" $
      checkForArity [2..3] $ prop_passesSTestWith id calcGroebnerBasisAfterHomogenising
    prop "includes the original ideal" $
      checkForArity [2..3] $ prop_groebnerDivsOrigWith id calcGroebnerBasisAfterHomogenising
    prop "is included in the orignal ideal" $
      checkForArity [2..3] $ prop_groebnerIncludedWith id calcGroebnerBasisAfterHomogenising

prop_passesSTestWith :: (KnownNat n, Coefficient poly' ~ Rational,
                         IsOrderedPolynomial poly', DecidableZero poly')
                     => (Polynomial Rational n -> poly')
                     -> (Ideal poly' -> [poly'])
                     -> SNat n -> Property
prop_passesSTestWith prepro calc sdim =
  forAll (sized $ \size -> vectorOf size (polynomialOfArity sdim)) $ \ideal ->
  let gs = calc $ toIdeal $ map prepro ideal
  in all (isZero . (`modPolynomial` gs)) [sPolynomial f g | f <- gs, g <- gs, f /= g]

prop_groebnerDivsOrigWith :: (KnownNat n, Coefficient poly' ~ Rational,
                              IsOrderedPolynomial poly', DecidableZero poly')
                          => (Polynomial Rational n -> poly')
                          -> (Ideal poly' -> [poly'])
                          -> SNat n -> Property
prop_groebnerDivsOrigWith prepro calc sdim =
  forAll (elements [3..15]) $ \count ->
  forAll (vectorOf count (polynomialOfArity sdim)) $ \jdeal ->
  let ideal = map prepro jdeal
      gs = calc $ toIdeal ideal
  in all (isZero . (`modPolynomial` gs)) ideal

prop_groebnerIncludedWith :: (KnownNat n, Coefficient poly' ~ Rational,
                              IsSingularPolynomial poly', DecidableZero poly')
                          => (Polynomial Rational n -> poly')
                          -> (Ideal poly' -> [poly'])
                          -> SNat n -> Property
prop_groebnerIncludedWith prepro calc sdim =
  forAll (elements [3..15]) $ \count ->
  forAll (vectorOf count (polynomialOfArity sdim)) $ \jdeal -> do
  let ideal = map prepro jdeal
      gs = calc $ toIdeal ideal
  is <- evalSingularIdealWith [] [] $
        funE "reduce" [idealE' $ toIdeal gs, funE "groebner" [idealE' $ toIdeal ideal]]
  if all isZero is
    then return ()
    else assertFailure "Non-zero element found"
