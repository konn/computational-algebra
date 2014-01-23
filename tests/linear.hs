module Main where
import qualified Data.Matrix           as M
import qualified Data.Vector           as V
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck
import           Utils

main :: IO ()
main = hspec $ do
  describe "luDecomp'" $ do
    prop "works correctly" $ prop_luDecomp
  return ()

prop_luDecomp :: Property
prop_luDecomp = forAll (resize 10 arbitrary)  $ \(MatrixCase ms) ->
      let m = M.fromLists ms :: M.Matrix Rational
          (u,l,p,q,_,_) = M.luDecomp' m
      in collect (minimum $ map (minimum . map abs) ms) $ collect (M.ncols m, M.nrows m) $
         p * m * q == l * u && isUpperTriangle u && isLowerTriangle l && M.diagProd l == 1

isLowerTriangle :: (Num r, Eq r) => M.Matrix r -> Bool
isLowerTriangle m = all (\i -> all (\j -> m M.! (i, j) == 0) [i+1..M.ncols m]) [1..M.nrows m]

isUpperTriangle :: (Num r, Eq r) => M.Matrix r -> Bool
isUpperTriangle m = all (\i -> all (\j -> m M.! (i, j) == 0) [1..min (i-1) (M.ncols m)]) [1..M.nrows m]

rank :: (Eq r, Num r, Ord r, Fractional r) => M.Matrix r -> Int
rank mat =
  let (u, _, _, _,_, _) = M.luDecomp' mat
  in V.foldr (\a acc -> if a /= 0 then acc + 1 else acc) (0 :: Int) $ M.getDiag u

