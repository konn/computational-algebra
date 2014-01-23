module Main where
import           Algebra.Algorithms.ZeroDim
import qualified Algebra.Linear                   as M
import           Algebra.Ring.Polynomial.Quotient
import           Data.Type.Monomorphic            (liftPoly)
import           Data.Type.Natural
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck
import           Utils

main :: IO ()
main = hspec $ do
  describe "matRepr'" $ do
    prop "coincids with matrixRep" $ checkForArity [1..3] prop_matrixRep
  return ()

prop_matrixRep :: SingRep n => SNat n -> Property
prop_matrixRep sn =
  forAll arbitrary $ \(ZeroDimIdeal ideal) ->
  forAll (polyOfDim sn) $ \poly ->
  reifyQuotient ideal $ \pxy ->
  let f = modIdeal' pxy poly
  in matrixRep f == M.toLists (matRepr' f)
