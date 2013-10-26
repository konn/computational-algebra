{-# LANGUAGE DataKinds, NoMonomorphismRestriction, OverloadedStrings #-}
module Main where
import           Algebra.Algorithms.Groebner
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Algebra.Ring.Polynomial.Quotient
import           Control.Applicative
import qualified Data.Map                         as M
import           Data.Type.Natural
import           Data.Vector.Sized                (Vector (..))
import           Instances
import           Test.Hspec
import qualified Test.Hspec.QuickCheck            as QC
import qualified Test.Hspec.SmallCheck            as SC
import           Test.QuickCheck                  (Arbitrary (..))
import qualified Test.QuickCheck                  as QC
import qualified Test.SmallCheck                  as SC

main :: IO ()
main = hspec spec

i1 :: Ideal (OrderedPolynomial Rational Lex Two)
i1 = toIdeal []

spec :: Spec
spec = do
  describe "Table multiplication" $ do
    it "coincides with ordinary multiplication" $ QC.property prop01

prop01 :: QC.Property
prop01 =
    QC.forAll (QC.resize 4 arbitrary) $ \(ZeroDimIdeal ideal) ->
        QC.forAll (QC.resize 6 $ polyOfDim sThree) $ \f -> QC.forAll (QC.resize 6 $ polyOfDim sThree) $ \g ->
          withQuotient ideal (modIdeal f * modIdeal g)
            == withQuotient ideal (multWithTable (modIdeal f) (modIdeal g))

polynG :: QC.Gen (Polynomial Rational Two)
polynG = arbitrary
