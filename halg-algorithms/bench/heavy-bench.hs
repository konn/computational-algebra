{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs   #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude                #-}
{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings, PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Main where
import Algebra.Algorithms.Groebner
import Algebra.Algorithms.Groebner.Homogeneous
import Algebra.Algorithms.Groebner.Signature
import Algebra.Field.Prime
import Algebra.Prelude.Core
import Data.List                               (tails)
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
  [  bgroup "syz+sugar"
    [bench "Q,Grevlex" $ nf (syzygyBuchbergerWithStrategy (SugarStrategy NormalStrategy)) grjQ
    ,bench "Q,Lex" $ nf (syzygyBuchbergerWithStrategy (SugarStrategy NormalStrategy)) lxjQ
    ,bench "F_65521,Grevlex" $ nf (syzygyBuchbergerWithStrategy (SugarStrategy NormalStrategy)) grjF
    ,bench "F_65521,Lex" $ nf (syzygyBuchbergerWithStrategy (SugarStrategy NormalStrategy)) lxjF
    ]
  ,  bgroup "naive-homog"
    [bench "Q,Grevlex" $ nf calcGroebnerBasisAfterHomogenising grjQ
    ,bench "Q,Lex" $ nf calcGroebnerBasisAfterHomogenising lxjQ
    ,bench "F_65521,Grevlex" $ nf calcGroebnerBasisAfterHomogenising grjF
    ,bench "F_65521,Lex" $ nf calcGroebnerBasisAfterHomogenising lxjF
    ]
  ,  bgroup "hilb"
    [bench "Q,Grevlex" $ nf calcGroebnerBasisAfterHomogenisingHilb grjQ
    ,bench "Q,Lex" $ nf calcGroebnerBasisAfterHomogenisingHilb lxjQ
    ,bench "F_65521,Grevlex" $ nf calcGroebnerBasisAfterHomogenisingHilb grjF
    ,bench "F_65521,Lex" $ nf calcGroebnerBasisAfterHomogenisingHilb lxjF
    ]
  ,  bgroup "F5"
    [bench "Q,Grevlex" $ nf f5 grjQ
    ,bench "Q,Lex" $ nf f5 lxjQ
    ,bench "F_65521,Grevlex" $ nf f5 grjF
    ,bench "F_65521,Lex" $ nf f5 lxjF
    ]
  ]

main :: IO ()
main =
  defaultMainWith defaultConfig
    [mkTC "Cyclic 4" $ cyclic (sing :: Sing 4)
    ,mkTC "Cyclic 7" $ cyclic (sing :: Sing 7)
    ,mkTC "Cyclic 8" $ cyclic (sing :: Sing 8)
    ,mkTC "Katsura 8" katsura8
    ,mkTC "Katsura 9" katsura9
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

katsura8 :: Ideal (Polynomial Rational 9)
katsura8 =
  let [x0,x1,x2,x3,x4,x5,x6,x7,_] = vars
  in toIdeal
     [ x0 +  2 * x1 + 2 * x2 + 2 * x3 + 2 * x4 + 2 * x5 + 2 * x6+ 2 * x7 - x0^2+2 * x1^2+2 * x2^2+2 * x3^2+2 * x4^2+ 2 * x5^2+2 * x6^2+2 * x7^2-x0
     , 2 * x0  * x1 + 2 * x1  * x2 + 2 * x2  * x3 + 2 * x3  * x4+ 2 * x4  * x5 + 2 * x5  * x6 + 2 * x6  * x7 -x1 * x1^2+2 * x0  * x2 + 2 * x1  * x3 + 2 * x2  * x4+ 2 * x3  * x5 + 2 * x4  * x6 + 2 * x5  * x7 -x2
     , 2 * x1  * x2 + 2 * x0  * x3 + 2 * x1  * x4 + 2 * x2  * x5+ 2 * x3  * x6 + 2 * x4  * x7 -x3
     , x2^2+2 * x1  * x3 + 2 * x0  * x4 + 2 * x1  * x5+ 2 * x2  * x6 + 2 * x3  * x7 -x4
     , 2 * x2  * x3 + 2 * x1  * x4 + 2 * x0  * x5 + 2 * x1  * x6+ 2 * x2  * x7 -x5
     , x3^2+2 * x2  * x4 + 2 * x1  * x5 + 2 * x0  * x6+ 2 * x1  * x7 - x6
     ]


katsura9 :: Ideal (Polynomial Rational 10)
katsura9 =
  let [x0,x1,x2,x3,x4,x5,x6,x7,x8,_] = vars
  in toIdeal
     [x0 +2*x1 +2*x2 +2*x3 +2*x4 +2*x5 +2*x6+ 2*x7 +2*x8 -x0^2+2*x1^2+2*x2^2+2*x3^2+2*x4^2+ 2*x5^2+2*x6^2+2*x7^2+2*x8^2-x0
     , 2*x0 *x1 +2*x1 *x2 +2*x2 *x3 +2*x3 *x4+ 2*x4 *x5 +2*x5 *x6 +2*x6 *x7 +2*x7 *x8- x1
     , x1^2+2*x0 *x2 +2*x1 *x3 +2*x2 *x4+ 2*x3 *x5 +2*x4 *x6 +2*x5 *x7 +2*x6 *x8- x2
     , 2*x1 *x2 +2*x0 *x3 +2*x1 *x4 +2*x2 *x5+ 2*x3 *x6 +2*x4 *x7 +2*x5 *x8 -x3*x2^2+2*x1 *x3 +2*x0 *x4 +2*x1 *x5+ 2*x2 *x6 +2*x3 *x7 +2*x4 *x8 -x4
     , 2*x2 *x3 +2*x1 *x4 +2*x0 *x5 +2*x1 *x6+ 2*x2 *x7 +2*x3 *x8 -x5
     , x3^2+2*x2 *x4 +2*x1 *x5 +2*x0 *x6+ 2*x1 *x7 +2*x2 *x8 -x6
     , 2*x3 *x4 +2*x2 *x5 +2*x1 *x6 +2*x0 *x7+ 2*x1 *x8 -x7
     ]
