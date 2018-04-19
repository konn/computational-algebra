{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts            #-}
{-# LANGUAGE FlexibleInstances, GADTs, MultiParamTypeClasses         #-}
{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction            #-}
{-# LANGUAGE OverloadedStrings, PolyKinds, Rank2Types, RankNTypes    #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Heavy (makeCase, FPol, CalcPoly(..)) where
import Algebra.Field.Prime
import Algebra.Normed
import Algebra.Prelude.Core
import Data.List            (tails)
import Gauge.Main


newtype CalcPoly where
  CalcPoly :: (forall poly. FPol poly => Ideal poly -> [poly]) -> CalcPoly

makeCase :: String
         -> CalcPoly
         -> [Benchmark]
makeCase name calc =
  [   bgroup name
      [mkTC calc "Cyclic 4"  $ cyclic (sing :: Sing 4)
      ,mkTC calc "Cyclic 7"  $ cyclic (sing :: Sing 7)
      ,mkTC calc "Cyclic 8"  $ cyclic (sing :: Sing 8)
      ,mkTC calc "Katsura 8" katsura8
      ,mkTC calc "Katsura 9" katsura9
      ,mkTC calc "I3"        i3
      ]
  ]

type FPol p = (IsOrderedPolynomial p, Num (Coefficient p),
               Normed (Coefficient p), Field (Coefficient p))

mkTC :: (KnownNat n)
     => CalcPoly
     -> String
     -> Ideal (Polynomial Rational n) -> Benchmark
mkTC (CalcPoly calc) name jdeal =
  env (return
       ( map (changeOrder Grevlex) jdeal
        , map (changeOrder Lex) jdeal
        , map (mapCoeff ratToF . changeOrder Grevlex) jdeal
        , map (mapCoeff ratToF . changeOrder Lex) jdeal
        , calc
        , calc
        , calc
        , calc
        )
      ) $ \ ~(grjQ, lxjQ, grjF, lxjF, calcGF, calcLF, calcGQ, calcLQ) ->
  bgroup name
    [bench "Q,Grevlex"       $ nf calcGQ grjQ
    ,bench "Q,Lex"           $ nf calcLQ lxjQ
    ,bench "F_65521,Grevlex" $ nf calcGF grjF
    ,bench "F_65521,Lex"     $ nf calcLF lxjF
    ]


ratToF :: Rational -> F 65521
ratToF = modRat'


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
