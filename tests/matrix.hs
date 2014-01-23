module Main where
import           Algebra.Algorithms.ZeroDim
import           Algebra.Ring.Polynomial.Quotient
import qualified Data.Matrix                      as M
import           Data.Type.Monomorphic            (liftPoly)
import           Data.Type.Natural
import qualified Data.Vector                      as V
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
  in matrixRep f == matToLists (matRepr' f)

matToLists :: M.Matrix a -> [[a]]
matToLists mat = [ V.toList $ M.getRow i mat | i <- [1..M.nrows mat] ]
