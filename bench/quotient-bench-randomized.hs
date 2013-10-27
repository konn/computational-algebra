{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs            #-}
{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings, PolyKinds, QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell, UndecidableInstances                            #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Main where
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Algebra.Ring.Polynomial.Quotient
import qualified Algebra.Ring.Polynomial.QuotientMemo as QM
import           Control.DeepSeq
import           Control.Monad
import           Control.Parallel.Strategies
import           Criterion.Main
import           Data.List                            (foldl')
import           Data.Type.Natural                    hiding (one)
import           Data.Vector.Sized                    hiding (fromList, map,
                                                       take, toList, zipWith)
import qualified Data.Vector.Sized                    as V
import           Instances
import           Numeric.Algebra
import           Prelude                              hiding ()
import           Test.QuickCheck

makeDataSet :: (SingRep n, NFData (Monomial n))
            => SNat n
            -> Int -> Int -> Int
            -> IO [(Ideal (Polynomial Rational n), [Polynomial Rational n])]
makeDataSet n count dpI dpP = do
  tss <- sample' $ do
    ZeroDimIdeal ideal <- resize dpI arbitrary
    fs <- replicateM count $ resize dpP $ polyOfDim n
    return (ideal `using` rdeepseq, fs `using` rdeepseq)
  return $! (take 5 tss `using` rdeepseq)

makeTestSet :: (SingRep n, NFData (Monomial n))
            => [(Ideal (Polynomial Rational n), [Polynomial Rational n])]
            -> [Benchmark]
makeTestSet = concat . zipWith mk [1..]
  where
    mk n test =
        [ bench ("naive-" ++ show n) $
            nf (\(i,fs) -> withQuotient i $ product $ map modIdeal fs) test
        , bench ("table-" ++ show n) $
            nf (\(i,fs) -> withQuotient i $ foldl' multWithTable one (map modIdeal fs)) test
        , bench ("mtrie-" ++ show n) $
            nf (\(i,fs) -> QM.withQuotient i $ foldl' QM.multWithTable one (map QM.modIdeal fs)) test
        ]

main :: IO ()
main = do
  test01 <- makeDataSet sTwo 2 4 6 `using` rdeepseq
  test02 <- makeDataSet sThree 2 4 6
  test03 <- makeDataSet sTwo 2 7 8
  test04 <- makeDataSet sTwo 3 7 8
  defaultMain $
    [ bgroup "2-4-6" $ makeTestSet test01
    , bgroup "3-4-6" $ makeTestSet test02
    , bgroup "2-7-8" $ makeTestSet test03
    , bgroup "ternary 2-7-8" makeTestSet test04
    ]
