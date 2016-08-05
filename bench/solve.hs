{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude, PolyKinds #-}
{-# LANGUAGE TypeFamilies, TypeOperators                         #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Main where
import Algebra.Algorithms.ZeroDim
import Algebra.Prelude            hiding ((^), (^^))
import Algebra.Ring.Ideal
import Algebra.Ring.Polynomial
import Algebra.Scalar

import           Control.Applicative
import           Control.DeepSeq
import           Control.Monad
import           Control.Monad.Random
import           Control.Parallel.Strategies
import           Criterion
import           Criterion.Main
import           Numeric.Algebra             hiding ((<), (^))
import qualified Numeric.Algebra             as NA
import           Numeric.Field.Fraction      (Fraction)
import           Prelude                     hiding (Fractional (..),
                                              Integral (..), Num (..),
                                              Real (..), sum, (^^))
import qualified Prelude                     as P
import           Test.QuickCheck
import           Utils

sFour :: Sing 4
sFour = sing :: SNat 4

x, y, z :: Polynomial (Fraction Integer) 3
[x, y, z] = vars

(.*) :: KnownNat n => Fraction Integer -> Polynomial (Fraction Integer) n -> Polynomial (Fraction Integer) n
(.*) = (.*.)

infixl 7 .*

(^^) :: Unital r => r -> NA.Natural -> r
(^^) = NA.pow

eqn01 :: Ideal (Polynomial (Fraction Integer) 3)
eqn01 = toIdeal [x^^2 - 2*x*z + 5, x*y^^2+y*z+1, 3*y^^2 - 8*x*z]

eqn02 :: Ideal (Polynomial (Fraction Integer) 3)
eqn02 =
  toIdeal [x^^2 + 2*y^^2 - y - 2*z
          ,x^^2 - 8*y^^2 + 10*z - 1
          ,x^^2 - 7*y*z
          ]

eqn03 :: Ideal (Polynomial (Fraction Integer) 3)
eqn03 = toIdeal [x^^2 + y^^2 + z^^2 - 2*x
                ,x^^3 - y*z - x
                ,x - y + 2*z
                ]

eqn04 :: Ideal (Polynomial (Fraction Integer) 3)
eqn04 = toIdeal [x*y + z - x*z, x^^2 - z, 2*x^^3 - x^^2 * y * z - 1]

mkBench :: (KnownNat n, (0 :< n) ~ 'True) => Ideal (Polynomial (Fraction Integer) n) -> IO [Benchmark]
mkBench is = do
  gen <- newStdGen
  return [ bench "naive" $ nf (solve' 1e-10) is
         , bench "lefteigen" $ nf (flip evalRand gen . solveM) is
         , bench "companion" $ nf (solveViaCompanion 1e-10) is
         -- , bench "power" $ nf (solve'' 1e-10) is
         ]

randomCase :: (0 :< n) ~ 'True
           => Int -> SNat n -> IO [Ideal (Polynomial (Fraction Integer) n)]
randomCase count sn = do
  as <- take count . map getIdeal <$> sample' (zeroDimOf sn)
  mapM (\a -> return $!! (a `using` rdeepseq)) as

main :: IO ()
main = do
  case01 <- mkBench =<< (return $!! (eqn01 `using` rdeepseq))
  case02 <- mkBench =<< (return $!! (eqn02 `using` rdeepseq))
  case03 <- mkBench =<< (return $!! (eqn03 `using` rdeepseq))
  case04 <- mkBench =<< (return $!! (eqn04 `using` rdeepseq))
  cases  <- mapM mkBench =<< randomCase 4 sFour
--  cases'  <- mapM mkBench =<< randomCase 1 sTen
  -- name : rest <- getArgs
  -- withArgs (("-n"++name) : rest) $ defaultMain $ {-bgroup "solution" $ -}
  defaultMain $
    [ bgroup "ternary-01" case01
    , bgroup "ternary-02" case02
    , bgroup "ternary-03" case03
    , bgroup "ternary-04" case04
    ] ++ zipWith (\i -> bgroup ("4-ary-0"++show i)) [5..]  cases
--    ++ zipWith (\i -> bgroup ("10-ary-0"++show i)) [8]  cases'
