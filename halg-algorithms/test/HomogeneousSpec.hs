{-# LANGUAGE DataKinds, ExplicitNamespaces, GADTs, OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms                                         #-}
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
import           Algebra.Ring.Ideal
import           Algebra.Ring.Polynomial
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
spec =
  describe "calcHomogeneousGroebnerBasis" $ modifyMaxSize (const 4) $ modifyMaxSuccess (const 25) $ do
    prop "passes S-test" $
      checkForArity [2..3] prop_passesSTest
    prop "includes the original ideal" $
      checkForArity [2..3] prop_groebnerDivsOrig
    prop "is included in the orignal ideal" $
      checkForArity [2..3] prop_groebnerIncluded

prop_passesSTest :: KnownNat n => SNat n -> Property
prop_passesSTest sdim =
  forAll (sized $ \size -> vectorOf size (polynomialOfArity sdim)) $ \ideal ->
  let gs = unsafeCalcHomogeneousGroebnerBasis $ toIdeal $ map homogenize ideal
  in all ((== 0) . (`modPolynomial` gs)) [sPolynomial f g | f <- gs, g <- gs, f /= g]

prop_groebnerDivsOrig :: KnownNat n => SNat n -> Property
prop_groebnerDivsOrig sdim =
  forAll (elements [3..15]) $ \count ->
  forAll (vectorOf count (polynomialOfArity sdim)) $ \jdeal ->
  let ideal = map homogenize jdeal
      gs = unsafeCalcHomogeneousGroebnerBasis $ toIdeal ideal
  in all ((== 0) . (`modPolynomial` gs)) ideal

prop_groebnerIncluded :: KnownNat n => SNat n -> Property
prop_groebnerIncluded sdim =
  forAll (elements [3..15]) $ \count ->
  forAll (vectorOf count (polynomialOfArity sdim)) $ \jdeal -> do
  let ideal = map homogenize jdeal
      gs = unsafeCalcHomogeneousGroebnerBasis $ toIdeal ideal
  is <- evalSingularIdealWith [] [] $
        funE "reduce" [idealE' $ toIdeal gs, funE "groebner" [idealE' $ toIdeal ideal]]
  if all (==0) is
    then return ()
    else assertFailure "Non-zero element found"
