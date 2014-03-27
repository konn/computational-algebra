module Main where
import Algebra.Algorithms.Faugere
import Algebra.Algorithms.Groebner
import Algebra.Ring.Polynomial
import Control.DeepSeq
import Control.Parallel.Strategies
import Criterion
import Criterion.Main
import Data.Type.Natural           (sFive, sFour, sThree)

main :: IO ()
main = do
  i1 <- return $!! (cyclic sThree `using` rdeepseq)
  i2 <- return $!! (cyclic sFour `using` rdeepseq)
  i3 <- return $!! (cyclic sFive `using` rdeepseq)
  defaultMain [ bgroup "cyclic-3"
                [ bench "buchberger" $ nf calcGroebnerBasis i1
                , bench "faugere4" $ nf (faugere4 optimalStrategy) i1
                , bench "faugere4-dm" $ nf (faugere4DM optimalStrategy) i1
                ]
              , bgroup "cyclic-4"
                [ bench "buchberger" $ nf calcGroebnerBasis i2
                , bench "faugere4" $ nf (faugere4 optimalStrategy) i2
                , bench "faugere4-dm" $ nf (faugere4DM optimalStrategy) i2
                ]
                ]
