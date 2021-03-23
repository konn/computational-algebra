{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}

module Main where

import Algebra.Prelude
import Algebra.Ring.Ideal
import Algebra.Ring.Polynomial
import Algebra.Ring.Polynomial.Quotient
import Control.Applicative
import Control.Concurrent
import Control.DeepSeq
import Control.Monad
import Control.Parallel.Strategies
import Data.List (foldl')
import Data.Maybe
import Gauge.Main
import Numeric.Algebra hiding ((>), (^))
import Numeric.Field.Fraction (Fraction)
import System.Process
import Test.QuickCheck
import Utils
import Prelude hiding (concat, map, product)
import qualified Prelude as P

sTwo :: SNat 2
sTwo = sNat

makeIdeals :: KnownNat n => Int -> SNat n -> Int -> IO [Ideal (Polynomial (Fraction Integer) n)]
makeIdeals count _ dpI = take count . map getIdeal <$> sample' (resize dpI arbitrary `suchThat` isNonTrivial)

mkTestCases :: KnownNat n => Int -> Int -> [Ideal (Polynomial (Fraction Integer) n)] -> IO [Benchmark]
mkTestCases count size is =
  forM (zip [1 ..] is) $ \(n, ideal) -> do
    reifyQuotient ideal $ \ii -> do
      let dim = maybe 0 length $ standardMonomials' ii
      fs0 <- take count <$> sample' (resize size $ quotOfDim ii)
      putStrLn $
        concat
          [ "\t subcase "
          , show n
          , " has dimension "
          , show dim
          ]
      fs <- return $! (fs0 `using` rdeepseq)
      return $
        bgroup
          (concat ["case-", show n, "-", show dim, "dim"])
          [ bench "naive" $ nf product fs
          , bench "table" $ nf (foldl multWithTable one) fs
          ]

main :: IO ()
main = do
  putStrLn "generating case01..."
  case01 <- mkTestCases 2 8 =<< makeIdeals 3 sTwo 7
  putStrLn "generating case02..."
  case02 <- mkTestCases 3 8 =<< makeIdeals 3 sTwo 7
  putStrLn "generating case03..."
  case04 <- mkTestCases 10 8 =<< makeIdeals 3 sTwo 7
  putStrLn "done. purge and sleep 10secs..."
  system "purge"
  threadDelay $ 10 P.^ 7
  defaultMain $
    [ bgroup "binary" case01
    , bgroup "ternary" case02
    , bgroup "10-ary" case04
    ]
