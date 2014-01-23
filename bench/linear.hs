{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs            #-}
{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings, PolyKinds, QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell, UndecidableInstances                            #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Main where
import           Algebra.Algorithms.ZeroDim
import           Control.Concurrent
import           Control.DeepSeq
import           Control.Monad
import           Control.Parallel.Strategies
import           Criterion.Main
import qualified Data.Matrix                 as M
import qualified Data.Vector                 as V
import           Prelude                     hiding (product)
import           System.Process
import           Test.QuickCheck
import           Utils

makeLinear :: Int -> Int -> IO [(M.Matrix Rational, V.Vector Rational)]
makeLinear count dpI =
  liftM (take count) $ sample' $ do
    Equation m v <- resize dpI arbitrarySolvable
    return (M.fromLists m, V.fromList v)

mkTestCases :: [(M.Matrix Rational, V.Vector Rational)] -> IO [Benchmark]
mkTestCases lins0 = do
  lins <- return $!! (lins0 `using` rdeepseq)
  forM (zip [1..] lins) $ \(n,ex) -> do
    return $ bgroup (concat ["case-",show n])
      [ bench "rank" $ nf (uncurry solveLinear') ex
      , bench "length" $ nf (uncurry solveLinear) ex
      ]

main :: IO ()
main = do
  putStrLn "generating case01..."
  case01 <- mkTestCases =<< makeLinear 5 10
  putStrLn "generating case02..."
  case02 <- mkTestCases =<< makeLinear 5 5
  putStrLn "generating case03..."
  case03 <- mkTestCases =<< makeLinear 5 20
  putStrLn "done. purge and sleep 10secs..."
  _ <- system "purge"
  threadDelay $ 10^7
  defaultMain $
    [ bgroup "size5" case02
    , bgroup "size10" case01
    , bgroup "size20" case03
    ]
