{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
module Faugere5Spec where
import           Algebra.Algorithms.Faugere5
import           Algebra.Algorithms.Groebner
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Control.Monad
import           Data.List                   (delete)
import           Data.List                   (sort)
import           Data.Type.Monomorphic
import           Data.Type.Natural           hiding (one, promote, zero)
import           Data.Vector.Sized           (Vector (..))
import qualified Data.Vector.Sized           as SV
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck             hiding (promote)
import           Utils

spec :: Spec
spec = do
  describe "f5Original" $ modifyMaxSize (const 10) $ modifyMaxSuccess (const 100) $ do
    it "computes Groebner basis for homogeneous ideals" $ do
      checkForArity [2..3] prop_computesGroebner

prop_computesGroebner :: SingI n => SNat n -> Property
prop_computesGroebner sdim =
  forAll (sized $ \size -> vectorOf size (homogPolyOfDim sdim)) $ \ideal ->
  let answer = sort $ reduceMinimalGroebnerBasis $ minimizeGroebnerBasis $ calcGroebnerBasis $ toIdeal ideal
      gs = sort $ reduceMinimalGroebnerBasis $ minimizeGroebnerBasis $ generators $ f5Original $ toIdeal ideal
  in gs == answer

{-
testCases :: [Ideal (OrderedPolynomial Rational Grevlex Three)]
testCases = [toIdeal [-8%5 *x^2 + 2*x *y - 3%2 *y^2,-1%2 *x^2 + 7%3 *x *y,2%7 *x^3 + 1%7 *x^2 *y + 7%6 *x *y^2 + 5*y^3 - 3%4 *y *z^2,5%8 *x^2 + 4%5 *y^2,-4%5 *x^2 - 3%7 *y *z,-3%7 *x^2 + 8*x *y - 3%4 *y^2 + 8%7 *x *z - 8%11 *z^2,-4%5 *x^2 *z - 7%2 *x *z^2,-3%5 *x^2 - 8%5 *x *y + 8%5 *y^2 + 2*y *z - 5%6 *z^2]]
  where
    [x,y,z] = genVars sThree :: [Polynomial Rational Three]
-}
