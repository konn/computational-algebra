{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction, DataKinds, FlexibleContexts #-}
module Main where
import           Algebra.Algorithms.Faugere4
import           Algebra.Algorithms.Groebner
import qualified Algebra.LinkedMatrix        as LM
import           Algebra.Matrix
import           Algebra.Prelude
import           Control.DeepSeq
import           Control.Parallel.Strategies
import           Criterion
import           Criterion.Main
import qualified Data.Matrix                 as DM
import           Data.Proxy                  (Proxy (..))
import           Test.QuickCheck

import Utils

s3 :: SNat 3
s3 = sing

s4 :: SNat 4
s4 = sing

s6 :: SNat 6
s6 = sing

f4Repa = faugere4 optimalStrategy
f4DM = faugere4G (Proxy :: Proxy DM.Matrix) optimalStrategy
-- f4SM = faugere4G (Proxy :: Proxy Sparse) optimalStrategy
f4LM  = faugere4LM optimalStrategy
f4LMN = faugere4G  (Proxy :: Proxy LM.Matrix) optimalStrategy
f4Mod  = faugere4Modular optimalStrategy

ideal3 :: [OrderedPolynomial (Fraction Integer) Grevlex 3]
ideal3 = [x^2 + y^2 + z^2 - 1, x^2 + y^2 + z^2 - 2*x, 2*x -3*y - z]
  where
    [x,y,z] = vars

ideal4 :: [OrderedPolynomial (Fraction Integer) Grevlex 3]
ideal4 = [x^2 * y - 2*x*y - 4*z - 1, z-y^2, x^3 - 4*z*y]
  where
    [x,y,z] = vars

ideal5 :: [OrderedPolynomial (Fraction Integer) Grevlex 6]
ideal5 = [ 2 * s - a * y, b^2 - (x^2 + y^2), c^2 - ( (a-x) ^ 2 + y^2)
         ]
  where
    [s,x,y,a,b,c] = vars

ideal6 ::  [OrderedPolynomial (Fraction Integer) Grevlex 3]
ideal6 = [ z^5 + y^4 + x^3 - 1, z^3 + y^3 + x^2 - 1]
  where
    [x,y,z] = vars

buildCase :: NFData b => a -> String -> (a -> b) -> Benchmark
buildCase i name calc = bench name $ nf calc i

main :: IO ()
main = do
  i1 <- return $!! (cyclic s3 `using` rdeepseq)
  i2 <- return $!! (cyclic s4 `using` rdeepseq)
  i3 <- return $!! (toIdeal ideal3 `using` rdeepseq)
  i4 <- return $!! (toIdeal ideal4 `using` rdeepseq)
  i5 <- return $!! (toIdeal ideal5 `using` rdeepseq)
  i6 <- return $!! (toIdeal ideal6 `using` rdeepseq)
  rand0 <- sample' $ idealOfDim s3
  rnd <- return $!! (head (drop 2 rand0) `using` rdeepseq)
  putStrLn $ concat [ "random ideal: ", show rnd ]
  defaultMain $
    [ bgroup "cyclic-3" $
      map (uncurry $ buildCase i1)
      [("buchberger", toIdeal . calcGroebnerBasis)
      , ("F4-repa", f4Repa)
      , ("F4-dm", f4DM)
      -- , ("F4-sparse", f4SM)
      , ("F4-link-naive", f4LMN)
      , ("F4-link-str", f4LM)
      , ("F4-modular" , f4Mod)
      ]
    , bgroup "cyclic-4" $
      map (uncurry $ buildCase i2)
      [("buchberger", toIdeal . calcGroebnerBasis)
      , ("F4-repa", f4Repa)
      , ("F4-dm", f4DM)
      -- , ("F4-sparse", f4SM)
      , ("F4-link-naive", f4LMN)
      , ("F4-link-str", f4LM)
      , ("F4-modular" , f4Mod)
      ]
    , bgroup "I3" $
      map (uncurry $ buildCase i3)
      [("buchberger", toIdeal . calcGroebnerBasis)
      , ("F4-repa", f4Repa)
      , ("F4-dm", f4DM)
      -- , ("F4-sparse", f4SM)
      , ("F4-link-naive", f4LMN)
      , ("F4-link-str", f4LM)
      , ("F4-modular" , f4Mod)
      ]
    , bgroup "I4" $
      map (uncurry $ buildCase i4)
      [("buchberger", toIdeal . calcGroebnerBasis)
      , ("F4-repa", f4Repa)
      , ("F4-dm", f4DM)
      -- , ("F4-sparse", f4SM)
      , ("F4-link-naive", f4LMN)
      , ("F4-link-str", f4LM)
      , ("F4-modular" , f4Mod)
      ]
    , bgroup "I5" $
      map (uncurry $ buildCase i5)
      [("buchberger", toIdeal . calcGroebnerBasis)
      , ("F4-repa", f4Repa)
      , ("F4-dm", f4DM)
      -- , ("F4-sparse", f4SM)
      , ("F4-link-naive", f4LMN)
      , ("F4-link-str", f4LM)
      , ("F4-modular" , f4Mod)
      ]
    , bgroup "I6" $
      map (uncurry $ buildCase i6)
      [("buchberger", toIdeal . calcGroebnerBasis)
      , ("F4-repa", f4Repa)
      , ("F4-dm", f4DM)
      -- , ("F4-sparse", f4SM)
      , ("F4-link-naive", f4LMN)
      , ("F4-link-str", f4LM)
      , ("F4-modular" , f4Mod)
      ]
    , bgroup "random-3ary" $
      map (uncurry $ buildCase rnd)
      [("buchberger", toIdeal . calcGroebnerBasis)
      , ("F4-repa", f4Repa)
      , ("F4-dm", f4DM)
      -- , ("F4-sparse", f4SM)
      , ("F4-link-naive", f4LMN)
      , ("F4-link-str", f4LM)
      , ("F4-modular" , f4Mod)
      ]
    ]
