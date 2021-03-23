{-# LANGUAGE ScopedTypeVariables, TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main where
import           Algebra.Field.Fraction.Test     ()
import           Algebra.Field.Prime             (F)
import           Algebra.Field.Prime.Test        ()
import qualified Algebra.Matrix.DataMatrix       as DM
import           Algebra.Matrix.Generic
import qualified Algebra.Matrix.Generic          as Mat
import qualified Algebra.Matrix.IntMap           as IM
import qualified Algebra.Matrix.RepaIntMap       as RIM
import           Algebra.Prelude.Core
import           Control.Applicative             ((<|>))
import           Control.DeepSeq
import           Control.Lens                    (ifoldMap, view, (<&>), _1)
import           Data.Char                       (isSpace)
import           Data.List.Split
import qualified Data.Ratio                      as PRat
import           Data.Reflection                 ()
import           Data.Vector                     (Vector)
import qualified Data.Vector.Generic             as GV
import           Gauge.Main
import           Gauge.Main.Options
import           GHC.Read
import qualified Numeric.Field.Fraction          as NA
import qualified Prelude                         as P
import           System.Directory
import           Test.QuickCheck
import qualified Test.QuickCheck                 as QC
import           Text.ParserCombinators.ReadP
import qualified Text.ParserCombinators.ReadP    as Read
import qualified Text.ParserCombinators.ReadPrec as Read

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
    let r = fromIntegral (toNatural (sNat :: SNat r)) P./ 100
        nrows = fromIntegral $ toNatural (sNat :: SNat n)
        ncols = fromIntegral $ toNatural (sNat :: SNat m)
    in Sparse <$> sparseMatrixOf arbitrary r nrows ncols

main :: IO ()
main =
  defaultMainWith
  defaultConfig { reportFile = Just "bench-results/gauss.html"}
  [ toCases "QQ" (Proxy :: Proxy Rational) 0.05 10 10
  , toCases "QQ" (Proxy :: Proxy Rational) 0.10 10 10
  , toCases "QQ" (Proxy :: Proxy Rational) 0.25 10 10
  , toCases "QQ" (Proxy :: Proxy Rational) 0.50 10 10
  , toCases "QQ" (Proxy :: Proxy Rational) 0.75 10 10
  , toCases "QQ" (Proxy :: Proxy Rational) 0.05 50 50
  , toCases "QQ" (Proxy :: Proxy Rational) 0.10 50 50
  , toCases "QQ" (Proxy :: Proxy Rational) 0.25 50 50
  , toCases "QQ" (Proxy :: Proxy Rational) 0.50 50 50
  , toCases "QQ" (Proxy :: Proxy Rational) 0.75 50 50
  , toCases "QQ" (Proxy :: Proxy Rational) 0.05 50 75
  , toCases "QQ" (Proxy :: Proxy Rational) 0.10 50 75
  , toCases "QQ" (Proxy :: Proxy Rational) 0.25 50 75
  , toCases "QQ" (Proxy :: Proxy Rational) 0.50 50 75
  , toCases "QQ" (Proxy :: Proxy Rational) 0.75 50 75
  , toCases "F_5" (Proxy :: Proxy (F 5)) 0.05 10 10
  , toCases "F_5" (Proxy :: Proxy (F 5)) 0.10 10 10
  , toCases "F_5" (Proxy :: Proxy (F 5)) 0.25 10 10
  , toCases "F_5" (Proxy :: Proxy (F 5)) 0.50 10 10
  , toCases "F_5" (Proxy :: Proxy (F 5)) 0.75 10 10
  , toCases "F_5" (Proxy :: Proxy (F 5)) 0.05 50 50
  , toCases "F_5" (Proxy :: Proxy (F 5)) 0.10 50 50
  , toCases "F_5" (Proxy :: Proxy (F 5)) 0.25 50 50
  , toCases "F_5" (Proxy :: Proxy (F 5)) 0.50 50 50
  , toCases "F_5" (Proxy :: Proxy (F 5)) 0.75 50 50
  , toCases "F_5" (Proxy :: Proxy (F 5)) 0.05 50 75
  , toCases "F_5" (Proxy :: Proxy (F 5)) 0.10 50 75
  , toCases "F_5" (Proxy :: Proxy (F 5)) 0.25 50 75
  , toCases "F_5" (Proxy :: Proxy (F 5)) 0.50 50 75
  , toCases "F_5" (Proxy :: Proxy (F 5)) 0.75 50 75
  ]

decodeMat :: (Field a, Read a) => Int -> Int -> FilePath -> IO [Vector a]
decodeMat nr nc fp =
  toRows @IM.IMMatrix .
  Mat.generate nr nc . foldr toIdx (const $ const zero) . map (splitOn "\t") . lines <$> readFile fp
  where
    toIdx ~[rs, cs, val] f =
      let (r, c, coe) = (P.read rs, P.read cs, P.read val)
      in \ x y -> if x == r && y == c then coe else f x y

instance Read Rational where
  readPrec =
    (readPrec <&> \r ->
               PRat.numerator (P.toRational (r :: Double)) NA.% PRat.denominator (P.toRational r))
   <|> (NA.%) <$> readPrec
              <*  Read.lift (munch isSpace)
              <*  Read.lift (Read.char '/')
              <*  Read.lift (munch isSpace)
              <*> readPrec


encodeMat :: (DecidableZero a, Show a) => FilePath -> [Vector a] -> IO ()
encodeMat fp = writeFile fp . unlines . enc
  where
    enc = ifoldMap $ \i -> ifoldMap $ \j a ->
      if isZero a
      then []
      else [ intercalate "\t" [show i, show j, show a] ]

toLabel :: String -> Double -> Int -> Int -> String
toLabel lab r nr nc = concat [ lab, "-"
                             , show (floor $ 100 * r :: Integer)
                             , "%-", show nr, "-", show nc
                             ]

getMatrix :: (Show a, Read a, Field a, Arbitrary a)
          => String -> proxy a -> Double -> Int -> Int -> IO [Vector a]
getMatrix lab _ r nr nc = do
  let fp = "data" </> concat ["gauss", "-", toLabel lab r nr nc] <.> "dat"
  there <- doesFileExist fp
  if there
    then decodeMat nr nc fp
    else do
    vec <- QC.generate $ sparseMatrixOf arbitrary r nr nc
    encodeMat fp vec
    return vec

mkCases :: (Normed a, Field a, NFData a, Eq a,
            Matrix DM.DMatrix a, Matrix IM.IMMatrix a, Matrix RIM.DRIMMatrix a)
        => String -> IO [Vector a] -> Benchmark
mkCases lab mrows =
  env (do rows <- mrows
          return (fromRows @DM.DMatrix rows,
                  fromRows @IM.IMMatrix rows,
                  fromRows @RIM.DRIMMatrix rows)) $ \ ~(dm, im, drim) ->
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

toCases :: (Normed a, Field a, NFData a, Eq a, Show a, Read a, Arbitrary a,
            Matrix DM.DMatrix a, Matrix IM.IMMatrix a, Matrix RIM.DRIMMatrix a)
        => String -> proxy a -> Double -> Int -> Int -> Benchmark
toCases lab pxy rat col row =
  mkCases (toLabel lab rat col row) (getMatrix lab pxy rat col row)
