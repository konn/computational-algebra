{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs   #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude                #-}
{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings, PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Main where
import Algebra.Algorithms.Groebner.F4
import Algebra.Field.Prime
import Algebra.Prelude.Core
import Data.List                      (tails)
import Gauge.Main
import Gauge.Main.Options

ratToF :: Rational -> F 65521
ratToF = modRat'

mkTC :: (KnownNat n) => String -> Ideal (Polynomial Rational n) -> Benchmark
mkTC name jdeal =
  env (return
        ( map (changeOrder Grevlex) jdeal
        , map (changeOrder Lex) jdeal
        , map (mapCoeff ratToF . changeOrder Grevlex) jdeal
        , map (mapCoeff ratToF . changeOrder Lex) jdeal
        )
      ) $ \ ~(grjQ, lxjQ, grjF, lxjF) ->
  bgroup name
  [ bgroup "F4"
    [bench "Q,Grevlex" $ nf f4 grjQ
    ,bench "Q,Lex" $ nf f4 lxjQ
    ,bench "F_65521,Grevlex" $ nf f4 grjF
    ,bench "F_65521,Lex" $ nf f4 lxjF
    ]
  ]

main :: IO ()
main =
  defaultMainWith defaultConfig
    [mkTC "Cyclic 4" $ cyclic (sing :: Sing 4)
    ,mkTC "Cyclic 7" $ cyclic (sing :: Sing 7)
    ,mkTC "Cyclic 8" $ cyclic (sing :: Sing 8)
    ,mkTC "I3" i3
    ]

i3 :: Ideal (Polynomial (Fraction Integer) 4)
i3 = toIdeal [ x^31 - x^6 - x- y, x^8 - z, x^10 -t]
  where
    [t,x,y,z] = vars

cyclic :: forall n. Sing n
       -> Ideal (OrderedPolynomial Rational Grevlex n)
cyclic n = withKnownNat n $
  let vs = vars :: [OrderedPolynomial Rational Grevlex n]
      cycs = map (`mkCyclic` vs) [1..length vs - 1]
  in toIdeal (product vs - 1 : cycs)

mkCyclic :: Ring r => Int -> [r] -> r
mkCyclic n cycs = sum $ map product $ take (length cycs) $ map (take n) $ tails $ cycle cycs
