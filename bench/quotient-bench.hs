{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs            #-}
{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings, PolyKinds, QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell, UndecidableInstances                            #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Algebra.Ring.Polynomial.Quotient
import           Control.DeepSeq
import           Control.Parallel.Strategies
import           Criterion.Main
import           Data.Type.Natural
import           Data.Vector.Sized                hiding (fromList, map, take,
                                                   toList, zipWith)
import qualified Data.Vector.Sized                as V
import           Instances
import           Test.QuickCheck

makeDataSet :: (SingRep n, NFData (Monomial n))
            => SNat n
            -> Int -> Int
            -> IO [(Ideal (Polynomial Rational n), Polynomial Rational n, Polynomial Rational n)]
makeDataSet n dpI dpP = do
  tss <- sample' $ do
    ZeroDimIdeal ideal <- resize dpI arbitrary
    f <- resize dpP $ polyOfDim n
    g <- resize dpP $ polyOfDim n
    return (ideal `using` rdeepseq, f `using` rdeepseq, g `using` rdeepseq)
  return $! (take 5 tss `using` rdeepseq)

makeTestSet :: (SingRep n, NFData (Monomial n))
            => [(Ideal (Polynomial Rational n), Polynomial Rational n, Polynomial Rational n)]
            -> [Benchmark]
makeTestSet = concat . zipWith mk [1..]
  where
    mk n test =
        [ bench ("naive-" ++ show n) $ nf (\(i,f,g) -> withQuotient i $ modIdeal f * modIdeal g) test
        , bench ("table-" ++ show n) $ nf (\(i,f,g) -> withQuotient i $ multWithTable (modIdeal f) (modIdeal g)) test
        ]


main :: IO ()
main = do
  test01 <- makeDataSet sTwo 4 6
  test02 <- makeDataSet sThree 4 6
  test03 <- makeDataSet sTwo 7 8
  test04 <- makeDataSet sFour 5 7
  defaultMain $ [ bgroup "2-4-6" $ makeTestSet test01
                , bgroup "3-4-6" $ makeTestSet test02
                , bgroup "2-7-8" $ makeTestSet test03
                ]

