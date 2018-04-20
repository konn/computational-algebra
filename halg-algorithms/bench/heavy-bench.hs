{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs      #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude                   #-}
{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings, PolyKinds    #-}
{-# LANGUAGE Rank2Types, RankNTypes, ScopedTypeVariables, TupleSections #-}
{-# LANGUAGE TypeFamilies, UndecidableInstances                         #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Main where
import Algebra.Algorithms.Groebner
import Algebra.Algorithms.Groebner.F4
import Algebra.Algorithms.Groebner.Homogeneous
import Algebra.Algorithms.Groebner.Signature
import Algebra.Prelude.Core
import Cases
import Gauge.Main
import Gauge.Main
import Gauge.Main.Options
import System.Environment

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

dic :: [(String, CalcPoly)]
dic = [("buchberger", CalcPoly $ syzygyBuchbergerWithStrategy (SugarStrategy NormalStrategy))
      ,("dbd", CalcPoly calcGroebnerBasisAfterHomogenising)
      ,("hilb", CalcPoly calcGroebnerBasisAfterHomogenisingHilb)
      ,("f4", CalcPoly f4)
      ,("f5", CalcPoly f5)
      ]

main :: IO ()
main = do
  args <- getArgs
  let (as, (nam, calc)) = maybe (args, ("f5", CalcPoly f5)) (tail args ,) $
          flip find dic . (\s -> (== s) . fst) =<< listToMaybe args
  withArgs as $
    defaultMainWith defaultConfig {csvFile = Just $ "heavy-" ++ nam ++ ".csv"} $
    makeCase nam calc

{-
              , bench "syz+sugar" $ nf (syzygyBuchbergerWithStrategy (SugarStrategy NormalStrategy)) ideal
              , bench "standard" $ nf calcGroebnerBasis ideal
              , bench "naive-homog" $ nf calcGroebnerBasisAfterHomogenising ideal
              , bench "hilb" $ nf calcGroebnerBasisAfterHomogenisingHilb ideal
              -- , bench "F4" $ nf f4 ideal
              , bench "F5" $ nf f5 ideal
-}
