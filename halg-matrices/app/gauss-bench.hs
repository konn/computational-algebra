{-# LANGUAGE ScopedTypeVariables, TypeApplications #-}
module Main where
import           Algebra.Field.Fraction.Test ()
import           Algebra.Field.Prime         (F)
import           Algebra.Field.Prime.Test    ()
import qualified Algebra.Matrix.DataMatrix   as DM
import           Algebra.Matrix.Generic
import qualified Algebra.Matrix.Generic      as Mat
import qualified Algebra.Matrix.IntMap       as IM
import qualified Algebra.Matrix.RepaIntMap   as RIM
import           Algebra.Prelude.Core
import           Control.DeepSeq
import           Control.Lens                (ifoldMap, view, _1)
import           Data.List.Split
import           Data.Reflection             ()
import           Data.Vector                 (Vector)
import qualified Data.Vector.Generic         as GV
import           Gauge.Main
import           Gauge.Types
import qualified Prelude                     as P
import           System.Directory
import           System.FilePath
import           Test.QuickCheck
import qualified Test.QuickCheck             as QC

sparseMatrixOf :: (DecidableZero a)
                  => Gen a -> Double -> Int -> Int -> Gen [Vector a]
sparseMatrixOf gen ratio nrow ncol = do
  let nonZeros = floor $ fromIntegral (nrow * ncol) * ratio
  nzs <- vectorOf nonZeros gen
  let zeros = replicate (nrow * ncol - nonZeros) zero
  mat0 <- shuffle $ nzs ++ zeros
  return $ map GV.fromList $ chunksOf nrow mat0

-- | @Sparse r n m mat a@ stands for a @m@x@n@ sparse matrix of
--   type @mat a@, with non-zero elements at most @r@%.
newtype Sparse ratio n m a = Sparse { runSparse :: [Vector a] }
  deriving (Read, Show, Eq, Ord)

instance (KnownNat r, KnownNat n, KnownNat m, DecidableZero a, Arbitrary a)
      => Arbitrary (Sparse r n m a) where
  arbitrary =
    let r = fromIntegral (toNatural (sing :: Sing r)) P./ 100
        nrows = fromIntegral $ toNatural (sing :: Sing n)
        ncols = fromIntegral $ toNatural (sing :: Sing m)
    in Sparse <$> sparseMatrixOf arbitrary r nrows ncols

main :: IO ()
main =
  defaultMainWith
  defaultConfig { reportFile = Just "bench-results/gauss.html"}
  []

decodeMat :: (Field a, Read a) => Int -> Int -> FilePath -> IO [Vector a]
decodeMat nr nc fp =
  toRows @IM.IMMatrix .
  Mat.generate nr nc . foldr toIdx (const $ const zero) . map words . lines <$> readFile fp
  where
    toIdx ~[rs, cs, val] f =
      let (r, c, coe) = (P.read rs, P.read cs, P.read val)
      in \ x y -> if x == r && y == c then coe else f x y

encodeMat :: (DecidableZero a, Show a) => FilePath -> [Vector a] -> IO ()
encodeMat fp = writeFile fp . unlines . enc
  where
    enc = ifoldMap $ \i -> ifoldMap $ \j a ->
      if isZero a
      then []
      else [ unwords [show i, show j, show a] ]

getMatrix :: (Show a, Read a, Field a, Arbitrary a)
          => String -> proxy a -> Double -> Int -> Int -> IO [Vector a]
getMatrix lab _ r nr nc = do
  let fp = "data" </> concat ["gauss", "-", lab, "-", show r, "-", show nr, "-", show nc] <.> "dat"
  there <- doesFileExist fp
  if there
    then decodeMat nr nc fp
    else do
    vec <- QC.generate $ sparseMatrixOf arbitrary r nr nc
    encodeMat fp vec
    return vec

mkCases :: (Normed a, Field a, NFData a, Eq a,
            Matrix DM.DMatrix a, Matrix IM.IMMatrix a, Matrix RIM.DRIMMatrix a)
        => String -> [Vector a] -> Benchmark
mkCases lab rows =
  env (return $! (fromRows @DM.DMatrix rows,
                  fromRows @IM.IMMatrix rows,
                  fromRows @RIM.DRIMMatrix rows)) $ \ (dm, im, drim) ->
  bgroup lab
  [ bench "matrix package" $ nf (view _1 . gaussReduction) dm
  , bench "IntMap sparse"  $ nf (view _1 . gaussReduction) im
  , bgroup "repa"
    [ bgroup "generic"
      [ bench "par"  $ nf (RIM.forceToVPar . view _1 . gaussReduction) drim
      , bench "seq"  $ nf (RIM.forceToVSeq . view _1 . gaussReduction) drim
      ]
    , bgroup "custom"
      [ bench "par" $ nf RIM.gaussReductionP drim
      , bench "seq" $ nf RIM.gaussReductionS drim
      ]
    ]
  ]
