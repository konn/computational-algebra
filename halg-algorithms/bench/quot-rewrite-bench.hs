{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs   #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude                #-}
{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings, PolyKinds #-}
{-# LANGUAGE TypeFamilies, UndecidableInstances                      #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fenable-rewrite-rules #-}
module Main where
import Cases

import Algebra.Algorithms.Groebner
import Algebra.Algorithms.Groebner.Signature.Rules ()
import Algebra.Prelude.Core
import Gauge.Main
import Gauge.Main.Options

main :: IO ()
main =
  defaultMainWith defaultConfig
    [ env (return quotPair) $ \ args ->
        bgroup "rewrite"
        [ bench "quot" $ nf (uncurry quotIdeal) args
        ]
    ]
