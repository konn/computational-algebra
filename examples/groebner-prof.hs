{-# LANGUAGE DataKinds, NoImplicitPrelude #-}
module Main where
import Algebra.Algorithms.Groebner
import Algebra.Prelude
import Control.DeepSeq
import Data.Type.Natural (Five, sFive)

i :: Ideal (Polynomial Rational Five)
i = toIdeal
    [35 * y^4 - 30*x*y^2 - 210*y^2*z + 3*x^2 + 30*x*z - 105*z^2 +140*y*t - 21*u
    ,5*x*y^3 - 140*y^3*z - 3*x^2*y + 45*x*y*z - 420*y*z^2 + 210*y^2*t -25*x*t + 70*z*t + 126*y*u
    ]
  where [t,u,x,y,z] = genVars sFive


main :: IO ()
main = calcGroebnerBasis i `deepseq` return ()
