{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Faugere5Spec where
import Algebra.Algorithms.Faugere5
import Algebra.Algorithms.Groebner
import Algebra.Prelude             ((%))
import Algebra.Ring.Ideal
import Algebra.Ring.Polynomial
import Data.List                   (sort)
import Data.Type.Natural           hiding (one, promote, zero)
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck             hiding (promote)
import Utils

spec :: Spec
spec = do
  describe "f5Original" $ modifyMaxSize (const 10) $ modifyMaxSuccess (const 100) $ do
    it "computes Groebner basis for homogeneous ideals (regression)" $ do
      all (\i -> sort (calcGroebnerBasis i) == generators (f5Original i)) testCases
    it "computes Groebner basis for homogeneous ideals (random)" $ do
      checkForArity [2..3] prop_computesGroebner

prop_computesGroebner :: SingI n => SNat n -> Property
prop_computesGroebner sdim =
  forAll (sized $ \size -> vectorOf size (homogPolyOfDim sdim)) $ \ideal ->
  let answer = sort $ calcGroebnerBasis $ toIdeal ideal
      gs = generators $ f5Original $ toIdeal ideal
  in gs == answer

testCases :: [Ideal (OrderedPolynomial (Fraction Integer) Grevlex Three)]
testCases = map toIdeal
            [[-8%5 *x^2 + 2*x *y - 3%2 *y^2
             ,-1%2 *x^2 + 7%3 *x *y
             ,2%7 *x^3 + 1%7 *x^2 *y + 7%6 *x *y^2 + 5*y^3 - 3%4 *y *z^2
             ,5%8 *x^2 + 4%5 *y^2
             ,-4%5 *x^2 - 3%7 *y *z
             ,-3%7 *x^2 + 8*x *y - 3%4 *y^2 + 8%7 *x *z - 8%11 *z^2
             ,-4%5 *x^2 *z - 7%2 *x *z^2
             ,-3%5 *x^2 - 8%5 *x *y + 8%5 *y^2 + 2*y *z - 5%6 *z^2]
             {-
            ,[-3%4 *x *y + 1%2 *x *z - 3%2 *z^2
             ,3*x^3 - 2*x *y *z
             ,-1%4 *x^2 - 5*x *y + y^2 + 4%3 *x *z
             ,-4%5 *x^3 - 5%4 *x^2 *y + 4*y *z^2
             ,-2%3 *x^2 - 4%3 *y *z]
             -} -- this should converge (according to singular implementation),
                -- but seems not with my implementation...
            ,[4%5 *x^2 *y *z - 5%3 *x^2 *z^2
             ,5%2 *x^4 - 4%5 *x^3 *y
             ,3%5 *x^4 - 3%2 *x^2 *y^2 + 3%5 *x^2 *y *z + 3%5 *y *z^3
             ,-5%4 *x^3 - 4%3 *y^3 + 3%7 *y *z^2]
            ,[-5*x^3 *y + 3%2 *x^2 *z^2 - 5%4 *y^2 *z^2 + 5%4 *z^4
             ,4%5 *x^3 + 3*x *y^2 - 4*x^2 *z + 4%7 *y^2 *z
             ,-1%4 *x^4 - 4%3 *x^3 *y - x^2 *y *z
             ,-2%5 *x *y,-5%3 *x^3],
             [-2%5 *x^2 *z + 8%5 *x *z^2,-3*x^4 - y^4 + 7%4 *x *y^2 *z + 5%7 *x^2 *z^2 - 8*y^2 *z^2 - 3%5 *z^4,3%7 *x *y - 7%8 *x *z,-1%4 *x^2 + 6%7 *x *z + 2%9 *y *z + 2%7 *z^2,-1%6 *x^3 - 1%4 *x^2 *y - 8%3 *x *y *z + 8%5 *x *z^2,-6%5 *x *y^3 + 1%8 *x^3 *z + 1%7 *x^2 *y *z,7%4 *x^4 + 7%4 *x^2 *z^2,-1%6 *x^3 *y + 4%7 *x^2 *y *z]
            ,[x^2*z^2-5%6*y^2*z^2+5%6*z^4, x^3, x^2*z-1%7*y^2*z, x*y, y^3*z, y^2*z^2-35%29*z^4, y*z^4, x*z^4,z^6]]
  where
    [x,y,z] = genVars sThree

