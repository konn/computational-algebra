{-# LANGUAGE NoImplicitPrelude #-}
module Main where
import Algebra.Algorithms.Groebner.Signature
import Algebra.Field.Prime
import Algebra.Prelude.Core
import Control.DeepSeq

i2 :: [OrderedPolynomial (Fraction Integer) Grevlex 5]
i2 =  [35 * y^4 - 30*x*y^2 - 210*y^2*z + 3*x^2 + 30*x*z - 105*z^2 +140*y*t - 21*u
      ,5*x*y^3 - 140*y^3*z - 3*x^2*y + 45*x*y*z - 420*y*z^2 + 210*y^2*t -25*x*t + 70*z*t + 126*y*u
      ]
     where [t,u,x,y,z] = vars

i3 :: [OrderedPolynomial (F 5) Grevlex 4]
i3 = [ x^31 - x^6 - x- y, x^8 - z, x^10 -t]
  where
    [t,x,y,z] = vars

main :: IO ()
main = f5 (toIdeal i3) `deepseq` return ()
