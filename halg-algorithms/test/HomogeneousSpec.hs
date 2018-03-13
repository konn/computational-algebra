{-# LANGUAGE DataKinds, ExplicitNamespaces, GADTs, PatternSynonyms #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module HomogeneousSpec where
import Algebra.Algorithms.Groebner
import Algebra.Algorithms.Groebner.Homogeneous
import Algebra.Internal                        (pattern (:<), KnownNat,
                                                pattern NilL, SNat, sSucc)
import Algebra.Ring.Ideal
import Algebra.Ring.Polynomial
import Utils

import           Control.Monad
import qualified Data.Foldable          as F
import           Data.List              (delete)
import qualified Data.Sized.Builtin     as SV
import           Numeric.Field.Fraction (Fraction)
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck
import           Utils

asGenListOf :: Gen [a] -> a -> Gen [a]
asGenListOf = const

spec :: Spec
spec = do
  describe "calcHomogeneousGroebnerBasis" $ modifyMaxSize (const 4) $ modifyMaxSuccess (const 25) $ do
    prop "passes S-test" $
      checkForArity [2..3] prop_passesSTest
    prop "divides all original generators" $
      checkForArity [2..3] prop_groebnerDivsOrig
    it "generates the same ideal as original" $ do
      pendingWith "need example"

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
