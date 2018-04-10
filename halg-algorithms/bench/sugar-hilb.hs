{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction      #-}
{-# LANGUAGE OverloadedStrings, PolyKinds, TypeFamilies            #-}
{-# LANGUAGE UndecidableInstances                                  #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Main where
import Algebra.Algorithms.Groebner.Homogeneous
import Algebra.Internal
import Algebra.Ring.Ideal
import Algebra.Ring.Polynomial
import Control.Parallel.Strategies
import Gauge.Main
import Gauge.Main.Options
import Numeric.Field.Fraction                  (Fraction)

i1 :: [OrderedPolynomial (Fraction Integer) Lex 7]
i1 = [y * w - (1 / 2) !* z * w + t*w
     ,(-2/7) !* u * w^2 + (10/7) !* v * w^2 - (20/7) !* w^3 + t* u - 5 * t* v + 10 * t* w
     ,(2/7) !* y* w^2 - (2/7) !* z* w^2 + (6/7) !* t* w^2 - y* t + z* t - 3 * t^2
     ,-2 * v^3 + 4 * u* v* w + 5 * v^2 * w - 6 * u* w^2 - 7 * v* w^2 + 15 * w^3 + 42 * y* v
     ,-14 * z* v - 63 * y* w + 21 * z* w - 42 * t* w + 147 * x
     ,(-9/7) !* u* w^3 + (45/7) !* v* w^3 - (135/7) !* w^4 + 2 * z* v^2 - 2 * t* v^2 - 4 * z* u* w+10 * t* u* w - 2 * z* v* w - 28 * t* v* w + 4 * z* w^2 + 86 * t* w^2 - 42 * y* z+14 * z^2 + 42 * y* t - 14 * z* t - 21 * x* u + 105 * x* v - 315 * x* w
     ,(6/7) !* y* w^3 - (9/7) !* z* w^3 + (36/7) !* t* w^3 - 2 * z* v^2 - 4 * y* t* w + 6 * z* t* w - 24 * t^2 * w + 4 * x* u* w + 2 * x* v* w - 4 * x* w^2 + 56 * x* y - 35 * x* z + 84 * x* t
     ,2 * u* v* w - 6 !* v^2 * w - u* w^2 + 13 * v* w^2 - 5 * w^3 + 14 * y* w - 28 * t* w
     ,u^2 * w - 3 * u* v* w + 5 * u* w^2 + 14 * y* w - 28 * t* w
     ,-2 * z* u* w - 2 * t* u* w + 4 * y* v* w + 6 * z* v* w - 2 * t* v* w - 16 * y* w^2 - 10 * z* w^2 + 22 * t* w^2 + 42 * x* w
     ,(28/3) !* y* u* w + (8/3) !* z* u* w - (20/3) !* t* u* w - (88/3) !* y* v* w - 8 * z* v* w +(68/3) !* t* v* w + 52 * y* w^2 + (40/3) !* z* w^2 - 44 * t* w^2 - 84 * x* w
     ,-4 * y* z* w + 10 * y* t* w + 8 * z* t* w - 20 * t^2 * w + 12 * x* u* w - 30 * x* v* w + 15 * x* w^2
     ,-1 * y^2 * w + (1/2) !* y* z* w + y* t* w - z* t* w + 2 * t^2 * w - 3 * x* u* w + 6 * x* v* w - 3 * x* w^2
     , 8 * x* y* w - 4 * x* z* w + 8 * x* t* w
     ]
     where
       [t,u,v,w,x,y,z] = vars

i2 :: [OrderedPolynomial (Fraction Integer) Lex 5]
i2 =  [35 * y^4 - 30*x*y^2 - 210*y^2*z + 3*x^2 + 30*x*z - 105*z^2 +140*y*t - 21*u
      ,5*x*y^3 - 140*y^3*z - 3*x^2*y + 45*x*y*z - 420*y*z^2 + 210*y^2*t -25*x*t + 70*z*t + 126*y*u
      ]
     where [t,u,x,y,z] = vars

i3 :: [OrderedPolynomial (Fraction Integer) Lex 4]
i3 = [ x^31 - x^6 - x- y, x^8 - z, x^10 -t]
  where
    [t,x,y,z] = vars

i4 :: [OrderedPolynomial (Fraction Integer) Lex 4]
i4 = [ w+x+y+z, w*x+x*y+y*z+z*w, w*x*y + x*y*z + y*z*w + z*w*x, w*x*y*z - 1]
  where
    [w, x,y,z] = vars

i5 :: [OrderedPolynomial (Fraction Integer) Lex 3]
i5 = [ x+y+z, x*y + y*z + z*x, x*y*z - 1]
  where
    [x,y,z] = vars

mkTestCases :: (KnownNat n) => Either Int String -> Ideal (OrderedPolynomial (Fraction Integer) Lex n) -> [Benchmark]
mkTestCases num ideal = [ mkTC ("lex-" ++ either show id num) (mapIdeal (changeOrder Lex) ideal)
                        ]

mkTC :: (IsMonomialOrder n ord, KnownNat n) => String -> Ideal (OrderedPolynomial (Fraction Integer) ord n) -> Benchmark
mkTC name jdeal =
  env (return jdeal) $ \ ideal ->
  bgroup name [ bench "hilb/std+par" $ nf calcGroebnerBasisAfterHomogenisingHilb ideal
              ]

main :: IO ()
main = do
  -- ideal1 <- return $! (toIdeal i1 `using` rdeepseq)
  ideal2 <- return $! (toIdeal i2 `using` rdeepseq)
  ideal3 <- return $! (toIdeal i3 `using` rdeepseq)
  ideal4 <- return $! (toIdeal i4 `using` rdeepseq)
  defaultMainWith defaultConfig { reportFile = Just "bench-results/sugar-paper.html"} $
       mkTestCases (Left 1) ideal2
    ++ mkTestCases (Right "Cyclic-3") (toIdeal i5)
    ++ mkTestCases (Right "Cyclic-4") ideal4
