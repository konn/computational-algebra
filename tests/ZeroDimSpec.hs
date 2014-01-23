{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
module ZeroDimSpec where
import           Algebra.Algorithms.Groebner
import           Algebra.Algorithms.ZeroDim
import qualified Algebra.Linear              as M
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Control.Monad
import           Data.Type.Monomorphic
import           Data.Type.Natural           hiding (one, promote, zero)
import           Data.Type.Ordinal
import qualified Data.Vector                 as V
import           SingularBridge
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck             hiding (promote)
import           Utils

asGenListOf :: Gen [a] -> a -> Gen [a]
asGenListOf = const

spec :: Spec
spec = do
  describe "solveLinear" $ do
    it "solves data set correctly" $
      forM_ linSet $ \set ->
      solveLinear (M.fromLists $ inputMat set) (V.fromList $ inputVec set)
      `shouldBe` Just (V.fromList $ answer set)
    prop "solves any solvable cases" $
      forAll (resize 10 arbitrary) $ \(MatrixCase ms) ->
      let mat = M.fromLists ms :: M.Matrix Rational
      in rank mat == M.ncols mat ==>
           forAll (vector (length $ head ms)) $ \v ->
             let ans = M.getCol 1 $ mat * M.colVector (V.fromList v)
             in solveLinear mat ans == Just (V.fromList v)
    it "cannot solve unsolvable cases" $ do
      pendingWith "need example"
  describe "univPoly" $ modifyMaxSuccess (const 50) $ modifyMaxSize (const 5) $ do
    prop "produces elimination ideal's monic generator" $ do
      checkForArity [2..4] prop_univPoly
  describe "radical" $ modifyMaxSuccess (const 50) $ modifyMaxSize (const 5) $ do
    prop "really computes radical" $ do
      pendingWith "We can verify correctness by comparing with singular, but it's not quite smart way..."
{-
      checkForArity [2..4] $ \sdim ->
        forAll (zeroDimOf sdim) $ \(ZeroDimIdeal ideal) ->
        stdReduced (generators $ radical ideal) == calcGroebnerBasis (singIdealFun "radical" ideal)
      -- pendingWith "I couldn't formulate the spec for radical without existentials :-("
-}

prop_univPoly :: SingRep n => SNat n -> Property
prop_univPoly sdim =
  forAll (zeroDimOf sdim) $ \(ZeroDimIdeal ideal) ->
  let ods = enumOrdinal sdim
  in conjoin $ flip map ods $ \nth ->
  let gen = univPoly nth ideal
  in forAll (unaryPoly sdim nth) $ \f ->
  (f `modPolynomial` [gen] == 0) == (f `isIdealMember` ideal)

rank :: (Eq r, Num r, Ord r, Fractional r) => M.Matrix r -> Int
rank mat =
  let (u, _, _, _,_, _) = M.luDecomp' mat
  in V.foldr (\a acc -> if a /= 0 then acc + 1 else acc) (0 :: Int) $ M.getDiag u

data TestSet = TestSet { inputMat :: [[Rational]]
                       , inputVec :: [Rational]
                       , answer   :: [Rational]
                       } deriving (Read, Show, Eq, Ord)

linSet :: [TestSet]
linSet =
  [TestSet
   [[1 ,0 ,0 ,0 ,0 ]
   ,[0 ,(-2) ,(-2) ,(-2) ,(-2) ]
   ,[0 ,0 ,3 / 2,0 ,(-1) / 2]
   ,[0 ,0 ,0 ,0 ,(-5) / 2]
   ,[0 ,1 ,1 ,1 ,1 ]
   ,[0 ,0 ,(-2) ,1 ,(-1) ]
   ]
   [0 ,(-2) ,19 / 5,14 / 5,1 ,0 ]
   [0 ,(-81) / 25,54 / 25,16 / 5,(-28) / 25]
  ]
