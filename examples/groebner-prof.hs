{-# LANGUAGE DataKinds, NoImplicitPrelude #-}
module Main where
import Algebra.Algorithms.Groebner
import Algebra.Prelude
import Control.DeepSeq

i :: Ideal (Polynomial Rational 3)
i = toIdeal [x^2 + y^2 + z^2 - 1, x^2 + y^2 + z^2 - 2*x, 2*x -3*y - z]
  where [x,y,z] = vars

main :: IO ()
main = calcGroebnerBasis i `deepseq` return ()
