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
import qualified Data.Vector                 as V
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
      solveLinear (M.fromLists $ inputMat set) (V.fromList $ inputVec set) `shouldBe` Just (V.fromList $ answer set)
    prop "solves any solvable cases" $
      forAll (resize 10 arbitrary) $ \(MatrixCase ms) ->
      let mat = M.fromLists ms :: M.Matrix Rational
      in rank mat == M.ncols mat ==>
           forAll (vector (length $ head ms)) $ \v ->
             let ans = M.getCol 1 $ mat * M.colVector (V.fromList v)
             in solveLinear mat ans == Just (V.fromList v)
    it "cannot solve unsolvable cases" $ do
      pendingWith "need example"
  describe "univPoly" $ do
    it "produces elimination ideal's monic generator" $ do
      pendingWith "need example"

prop_passesSTest :: SNat n -> Property
prop_passesSTest sdim =
  case singInstance sdim of
    SingInstance ->
      forAll (elements [3..15]) $ \count ->
      forAll (vectorOf count (polyOfDim sdim)) $ \ideal ->
      let gs = calcGroebnerBasis $ toIdeal ideal
      in all ((== 0) . (`modPolynomial` gs)) [sPolynomial f g | f <- gs, g <- gs, f /= g]

prop_groebnerDivsOrig :: SNat n -> Property
prop_groebnerDivsOrig sdim =
  case singInstance sdim of
    SingInstance ->
      forAll (elements [3..15]) $ \count ->
      forAll (vectorOf count (polyOfDim sdim)) $ \ideal ->
      let gs = calcGroebnerBasis $ toIdeal ideal
      in all ((== 0) . (`modPolynomial` gs)) ideal

prop_divCorrect :: SNat n -> Property
prop_divCorrect sdim =
  case singInstance sdim of
    SingInstance ->
      forAll (polyOfDim sdim) $ \poly ->
      forAll (idealOfDim sdim) $ \ideal ->
      let dvs = generators ideal
          (qds, r) = poly `divModPolynomial` dvs
      in poly == sum (map (uncurry (*)) qds) + r

prop_indivisible :: SNat n -> Property
prop_indivisible sdim =
  case singInstance sdim of
    SingInstance ->
      forAll (polyOfDim sdim) $ \poly ->
      forAll (idealOfDim sdim) $ \ideal ->
      let dvs = generators ideal
          (_, r) = changeOrder Grevlex poly `divModPolynomial` dvs
      in r /= 0 ==> all (\f -> all (\(_, m) -> not $ leadingMonomial f `divs` m) $ getTerms r)  dvs

prop_degdecay :: SNat n -> Property
prop_degdecay sdim =
  case singInstance sdim of
    SingInstance ->
      forAll (polyOfDim sdim) $ \poly ->
      forAll (idealOfDim sdim) $ \ideal ->
      let dvs = generators ideal
          (qs, _) = poly `divModPolynomial` dvs
      in all (\(a, f) -> (a * f == 0) || (leadingMonomial poly >= leadingMonomial (a * f))) qs

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
