{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs            #-}
{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings, PolyKinds, QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell, UndecidableInstances                            #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Main where
import Algebra.Algorithms.Groebner
import Algebra.Ring.Noetherian
import Algebra.Ring.Polynomial
import Control.Applicative
import Control.Concurrent
import Control.DeepSeq
import Control.Monad
import Control.Parallel.Strategies
import Criterion.Main
import Data.Type.Natural           hiding (one)
import Prelude                     hiding (product)
import System.Process
import Test.QuickCheck
import Utils

makeIdeals :: SingRep n => Int -> SNat n -> Int -> IO [(Polynomial Rational n, [Polynomial Rational n])]
makeIdeals count sn dpI = do
  ideals <- take count . map generators <$> sample' (resize dpI (idealOfDim sn))
  fs <- take count <$> sample' (polyOfDim sn)
  return $ zip fs ideals

mkTestCases :: SingRep n => [(Polynomial Rational n, [Polynomial Rational n])] -> IO [Benchmark]
mkTestCases is =
  forM (zip [1..] is) $ \(n, (f0, gs0)) -> do
      f  <- return $!! (f0 `using` rdeepseq)
      gs <- return $!! (gs0 `using` rdeepseq)
      return $ bgroup (concat ["case-",show n])
                 [ bench "ST+LoopT" $ nf (uncurry divModPolynomial') (f, gs)
                 , bench "ST+monad" $ nf (uncurry divModPolynomial'') (f, gs)
                 , bench "List" $ nf (uncurry divModPolynomial) (f, gs)
                 ]

main :: IO ()
main = do
  putStrLn "generating case01..."
  case01 <- mkTestCases =<< makeIdeals 3 sTwo 5
  putStrLn "generating case02..."
  case02 <- mkTestCases =<< makeIdeals 3 sThree 7
  putStrLn "generating case03..."
  case04 <- mkTestCases =<< makeIdeals 3 sFour 7
  putStrLn "done. purge and sleep 10secs..."
  system "purge"
  threadDelay $ 10^7
  defaultMain $
    [ bgroup "2-ary" case01
    , bgroup "3-ary" case02
    , bgroup "4-ary" case04
    ]

{-
divModPolynomial' :: (IsMonomialOrder order, IsPolynomial r n, Field r)
                 => OrderedPolynomial r order n -> [OrderedPolynomial r order n]
                 -> ([(OrderedPolynomial r order n, OrderedPolynomial r order n)], OrderedPolynomial r order n)
divModPolynomial' f0 fs = runST $ do
  f <- newSTRef f0
  r <- newSTRef zero
  dic <- V.unsafeThaw $ V.fromList (zip (nub fs) (repeat zero))
  let len = MV.length dic
  whileM_ ((/= zero) <$> readSTRef f) $ do
    p <- readSTRef f
    divable <- foreach' False [0..len - 1] $ \i -> do
      (g, old) <- lift $ MV.read dic i
      when (leadingMonomial g `divs` leadingMonomial p) $ do
        let q = toPolynomial $ leadingTerm p `tryDiv` leadingTerm g
        lift $ do
          MV.write dic i (g, old + q)
          modifySTRef f (subtract $ q * g)
        exitWith True
    unless divable $ do
      let ltP = toPolynomial $ leadingTerm p
      modifySTRef' f (subtract ltP)
      modifySTRef' r (+ ltP)
  (,) <$> (V.toList <$> V.unsafeFreeze dic)
      <*> readSTRef r

divModPolynomial'' :: (IsMonomialOrder order, IsPolynomial r n, Field r)
                 => OrderedPolynomial r order n -> [OrderedPolynomial r order n]
                 -> ([(OrderedPolynomial r order n, OrderedPolynomial r order n)], OrderedPolynomial r order n)
divModPolynomial'' f0 fs = runST $ do
  f <- newSTRef f0
  r <- newSTRef zero
  dic <- V.unsafeThaw $ V.fromList (zip (nub fs) (repeat zero))
  let len = MV.length dic
  whileM_ ((/= zero) <$> readSTRef f) $ do
    p <- readSTRef f
    mi <- newSTRef 0
    divable <- newSTRef False
    whileM_ (andM [not <$> readSTRef divable, (<len) <$> readSTRef mi]) $ do
      i <- readSTRef mi
      (g, old) <- MV.read dic i
      when (leadingMonomial g `divs` leadingMonomial p) $ do
        let q = toPolynomial $ leadingTerm p `tryDiv` leadingTerm g
        MV.write dic i (g, old + q)
        modifySTRef f (subtract $ q * g)
        writeSTRef divable True
      modifySTRef mi (+1)
    gone <- readSTRef divable
    unless gone $ do
      let ltP = toPolynomial $ leadingTerm p
      modifySTRef' f (subtract ltP)
      modifySTRef' r (+ ltP)
  (,) <$> (V.toList <$> V.unsafeFreeze dic)
      <*> readSTRef r
-}
