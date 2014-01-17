module Main where
import           Algebra.Algorithms.ZeroDim
import qualified Algebra.Linear             as M
import           Control.Monad
import           Data.Ratio
import qualified Data.Vector                as V
import qualified Data.Vector.Mutable        as MV
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck
import           Utils

main :: IO ()
main = hspec $ do
  describe "luDecomp'" $ do
    prop "works correctly" $ forAll (resize 10 arbitrary)  $ \(MatrixCase ms) ->
      let m = M.fromLists ms :: M.Matrix Rational
          (u,l,p,q,_,_) = M.luDecomp' m
      in p * m * q == l * u && isUpperTriangle u && isLowerTriangle l && M.diagProd l == 1
  describe "solveLinear'" $ do
    prop "solves any solvable cases" $ forAll (resize 10 arbitrary) $ \(MatrixCase ms) ->
      let mat = M.fromLists ms :: M.Matrix Rational
      in rank mat == M.ncols mat ==>
           forAll (vector (length $ head ms)) $ \v ->
             let ans = M.getCol 1 $ mat * M.colVector (V.fromList v)
             in solveLinear' mat ans == Just (V.fromList v)
    it "cannot solve unsolvable cases" $ do
      pendingWith "need example"
  describe "solveLinear" $ do
    prop "generates same answer as solveLinear'" $ forAll (resize 20 arbitrary) $ \(Equation mat0 v0) ->
      let mat = M.fromLists mat0
          v   = V.fromList v0
      in solveLinear mat v == solveLinear' mat v
  return ()

badM :: M.Matrix Rational
badM =
  M.fromLists [[1, 2 ,3]]

badV :: V.Vector Rational
badV = V.fromList [1,0,1]

badAns :: V.Vector Rational
badAns = M.getCol 1 $ badM * M.colVector badV

isLowerTriangle :: (Num r, Eq r) => M.Matrix r -> Bool
isLowerTriangle m = all (\i -> all (\j -> m M.! (i, j) == 0) [i+1..M.ncols m]) [1..M.nrows m]

isUpperTriangle :: (Num r, Eq r) => M.Matrix r -> Bool
isUpperTriangle m = all (\i -> all (\j -> m M.! (i, j) == 0) [1..min (i-1) (M.ncols m)]) [1..M.nrows m]

printLvl :: Show a => Int -> a -> IO ()
printLvl lvl = putStrLn . unlines . map (replicate lvl '\t' ++) . lines . show

rank :: (Eq r, Num r, Ord r, Fractional r) => M.Matrix r -> Int
rank mat =
  let (u, _, _, _,_, _) = M.luDecomp' mat
  in V.foldr (\a acc -> if a /= 0 then acc + 1 else acc) (0 :: Int) $ M.getDiag u
