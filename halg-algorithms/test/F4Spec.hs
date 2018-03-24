{-# LANGUAGE DataKinds, ExplicitNamespaces, GADTs, NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings, PartialTypeSignatures, PatternSynonyms #-}
{-# LANGUAGE TypeApplications                                          #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module F4Spec where
import           Algebra.Algorithms.Groebner
import           Algebra.Algorithms.Groebner.F4
import           Algebra.Bridge.Singular
import           Algebra.Internal                    (pattern (:<), KnownNat,
                                                      pattern NilL, SNat, sSucc)
import           Algebra.Prelude.Core
import           Algebra.Ring.Ideal
import           Algebra.Ring.Polynomial
import           Algebra.Ring.Polynomial.Homogenised
import           Control.Monad
import qualified Data.Foldable                       as F
import           Data.List                           (delete)
import qualified Data.Sized.Builtin                  as SV
import           Numeric.Field.Fraction              (Fraction)
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.HUnit.Lang
import           Test.QuickCheck
import           Utils


asGenListOf :: Gen [a] -> a -> Gen [a]
asGenListOf = const

spec :: Spec
spec = do
  describe "f4" $ modifyMaxSize (const 4) $ modifyMaxSuccess (const 25) $ do
    prop "passes S-test" $
      checkForArity [2..3] $ prop_passesSTest f4
    prop "includes the original ideal" $
      checkForArity [2..3] $ prop_groebnerDivsOrig f4
    prop "is included in the orignal ideal" $
      checkForArity [2..3] $ prop_groebnerIncluded f4

prop_passesSTest :: (Ideal (Polynomial Rational n) -> [Polynomial Rational n])
                 -> SNat n -> Property
prop_passesSTest calc sdim = withKnownNat sdim $
  forAll (sized $ \ size -> vectorOf size (polynomialOfArity sdim)) $ \ideal ->
  let gs = calc $ toIdeal ideal
  in all (isZero . (`modPolynomial` gs)) [sPolynomial f g | f <- gs, g <- gs, f /= g]

prop_groebnerDivsOrig :: (Ideal (Polynomial Rational n) -> [Polynomial Rational n])
                      -> SNat n -> Property
prop_groebnerDivsOrig calc sdim =withKnownNat sdim $
  forAll (elements [3..15]) $ \count ->
  forAll (vectorOf count (polynomialOfArity sdim)) $ \ideal ->
  let gs = calc $ toIdeal ideal
  in all (isZero . (`modPolynomial` gs)) ideal

prop_groebnerIncluded :: (Ideal (Polynomial Rational n) -> [Polynomial Rational n])
                      -> SNat n -> Property
prop_groebnerIncluded calc sdim = withKnownNat sdim $
  forAll (elements [3..15]) $ \count ->
  forAll (vectorOf count (polynomialOfArity sdim)) $ \ideal -> do
  let gs = calc $ toIdeal ideal
  is <- evalSingularIdealWith [] [] $
        funE "reduce" [idealE' $ toIdeal gs, funE "groebner" [idealE' $ toIdeal ideal]]
  if all isZero is
    then return ()
    else assertFailure "Non-zero element found"
