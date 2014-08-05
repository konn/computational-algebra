{-# LANGUAGE NoMonomorphismRestriction #-}
module Main where
import           Algebra.Algorithms.Faugere4
import           Algebra.Algorithms.Groebner
import           Algebra.Matrix
import           Algebra.Ring.Polynomial
import           Control.DeepSeq
import           Control.Parallel.Strategies
import           Criterion
import           Criterion.Main
import qualified Data.Matrix                 as DM
import           Data.Proxy                  (Proxy (..))
import           Data.Type.Natural           (sFive, sFour, sThree)

f4Repa = faugere4 optimalStrategy
f4DM = faugere4G (Proxy :: Proxy DM.Matrix) optimalStrategy
f4SM = faugere4G (Proxy :: Proxy Sparse) optimalStrategy
f4LM = faugere4LM optimalStrategy

main :: IO ()
main = do
  i1 <- return $!! (cyclic sThree `using` rdeepseq)
  i2 <- return $!! (cyclic sFour `using` rdeepseq)
  i3 <- return $!! (cyclic sFive `using` rdeepseq)
  defaultMain [ bgroup "cyclic-3"
                [ bench "buchberger"    $ nf calcGroebnerBasis i1
                , bench "F4-repa" $ nf f4Repa i1
                , bench "F4-dm"   $ nf f4DM i1
                , bench "F4-sparse" $ nf f4SM i1
                , bench "F4-linked" $ nf f4LM i1
                ]
              , bgroup "cyclic-4"
                [ bench "buchberger" $ nf calcGroebnerBasis i2
                , bench "F4-repa" $ nf f4Repa i2
                , bench "F4-dm"   $ nf f4DM i2
                , bench "F4-sparse" $ nf f4SM i2
                , bench "F4-linked" $ nf f4LM i2
                ]

                {-
              , bgroup "cyclic-5"
                [ bench "buchberger" $ nf calcGroebnerBasis i3
                , bench "F4-dm"   $ nf f4DM i3
                , bench "F4-linked" $ nf f4LM i3
                ]
-}
                ]
