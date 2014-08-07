{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction #-}
module Main where
import           Algebra.Algorithms.Faugere4
import           Algebra.Algorithms.Groebner
import           Algebra.Matrix
import           Algebra.Prelude
import           Algebra.Ring.Polynomial
import           Control.DeepSeq
import           Control.Parallel.Strategies
import           Criterion
import           Criterion.Main
import qualified Data.Matrix                 as DM
import           Data.Proxy                  (Proxy (..))
import           Data.Type.Natural           (sFive, sFour, sThree)
import           Data.Type.Natural           (sSix)
import           Data.Type.Natural           (Three)
import           Data.Type.Natural           (Six)
import           Numeric.Field.Fraction      (Fraction)
import           Test.QuickCheck

import Utils

f4Repa = faugere4 optimalStrategy
f4DM = faugere4G (Proxy :: Proxy DM.Matrix) optimalStrategy
f4SM = faugere4G (Proxy :: Proxy Sparse) optimalStrategy
f4LM  = faugere4LM optimalStrategy

ideal3 :: [OrderedPolynomial (Fraction Integer) Grevlex Three]
ideal3 = [x^2 + y^2 + z^2 - 1, x^2 + y^2 + z^2 - 2*x, 2*x -3*y - z]
  where
    [x,y,z] = genVars sThree

ideal4 :: [OrderedPolynomial (Fraction Integer) Grevlex Three]
ideal4 = [x^2 * y - 2*x*y - 4*z - 1, z-y^2, x^3 - 4*z*y]
  where
    [x,y,z] = genVars sThree

ideal5 :: [OrderedPolynomial (Fraction Integer) Grevlex Six]
ideal5 = [ 2 * s - a * y, b^2 - (x^2 + y^2), c^2 - ( (a-x) ^ 2 + y^2)
         ]
  where
    [s,x,y,a,b,c] = genVars sSix

ideal6 ::  [OrderedPolynomial (Fraction Integer) Grevlex Three]
ideal6 = [ z^5 + y^4 + x^3 - 1, z^3 + y^3 + x^2 - 1]
  where
    [x,y,z] = genVars sThree


main :: IO ()
main = do
  i1 <- return $!! (cyclic sThree `using` rdeepseq)
  i2 <- return $!! (cyclic sFour `using` rdeepseq)
  i3 <- return $!! (toIdeal ideal3 `using` rdeepseq)
  i4 <- return $!! (toIdeal ideal4 `using` rdeepseq)
  i5 <- return $!! (toIdeal ideal5 `using` rdeepseq)
  i6 <- return $!! (toIdeal ideal6 `using` rdeepseq)
  rand0 <- sample' $ idealOfDim sThree
  rnd <- return $!! (head (drop 2 rand0) `using` rdeepseq)
  defaultMain $
    [ bgroup "cyclic-3"
      [ bench "buchberger" $ nf calcGroebnerBasis i1
      , bench "F4-repa"    $ nf f4Repa i1
      , bench "F4-dm"      $ nf f4DM i1
      , bench "F4-sparse"  $ nf f4SM i1
      , bench "F4-linked"  $ nf f4LM i1
      ]
    , bgroup "cyclic-4"
      [ bench "buchberger" $ nf calcGroebnerBasis i2
      , bench "F4-repa"    $ nf f4Repa i2
      , bench "F4-dm"      $ nf f4DM i2
      , bench "F4-sparse"  $ nf f4SM i2
      , bench "F4-linked"  $ nf f4LM i2
      ]
    , bgroup "I3"
      [ bench "buchberger" $ nf calcGroebnerBasis i3
      , bench "F4-repa"    $ nf f4Repa i3
      , bench "F4-dm"      $ nf f4DM i3
      , bench "F4-sparse"  $ nf f4SM i3
      , bench "F4-linked"  $ nf f4LM i3
      ]
    , bgroup "I4"
      [  bench "buchberger" $ nf calcGroebnerBasis i4
      , bench "F4-repa"    $ nf f4Repa i4
      , bench "F4-dm"      $ nf f4DM i4
      , bench "F4-sparse"  $ nf f4SM i4
      , bench "F4-linked"  $ nf f4LM i4
      ]
    , bgroup "I5"
      [ bench "buchberger" $ nf calcGroebnerBasis i5
      , bench "F4-repa"    $ nf f4Repa i5
      , bench "F4-dm"      $ nf f4DM i5
      , bench "F4-sparse"  $ nf f4SM i5
      , bench "F4-linked"  $ nf f4LM i5
      ]
    , bgroup "I6"
      [ bench "buchberger" $ nf calcGroebnerBasis i6
      , bench "F4-repa"    $ nf f4Repa i6
      , bench "F4-dm"      $ nf f4DM i6
      , bench "F4-sparse"  $ nf f4SM i6
      , bench "F4-linked"  $ nf f4LM i6
      ]
    , bgroup "random-3ary"
      [ bench "buchberger" $ nf calcGroebnerBasis rnd
      , bench "F4-repa"    $ nf f4Repa rnd
      , bench "F4-dm"      $ nf f4DM rnd
      , bench "F4-sparse"  $ nf f4SM rnd
      , bench "F4-linked"  $ nf f4LM rnd
      ]
    ]
