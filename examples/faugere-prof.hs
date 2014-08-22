{-# LANGUAGE NoImplicitPrelude #-}
module Main where
import Algebra.Algorithms.Faugere4
import Algebra.Prelude
import Control.DeepSeq
import Data.Type.Natural           (sThree)
import Data.Type.Natural           (Three)

main :: IO ()
main = faugere4Modular optimalStrategy ideal3 `deepseq` return ()

ideal3 :: Ideal (Polynomial (Fraction Integer) Three)
ideal3 = toIdeal [2*x^2*y^5*z^5 - 5%3*x^3*y*z^7 - 3*x^2*z^8,4%3*x*y^3*z^4 - x*y,-3*x^4*y^2*z]
  where
    [x,y,z] = genVars sThree
