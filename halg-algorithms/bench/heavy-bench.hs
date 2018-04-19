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
import Gauge.Main
import Gauge.Main.Options
import Heavy
import System.Environment

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
