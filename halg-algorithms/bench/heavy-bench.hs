{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs      #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude                   #-}
{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings, PolyKinds    #-}
{-# LANGUAGE Rank2Types, RankNTypes, ScopedTypeVariables, TupleSections #-}
{-# LANGUAGE TypeApplications, TypeFamilies, UndecidableInstances       #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Main where
import           Algebra.Algorithms.Groebner.Signature
import           Algebra.Field.Prime
import           Algebra.Prelude.Core
import           Cases
import           Data.Reflection
import           Data.Vector                           (Vector)
import qualified Data.Vector                           as V
import           Gauge.Main
import           Gauge.Main.Options

newtype CalcPoly where
  CalcPoly :: (forall poly. FPol poly => Vector poly -> Ideal poly -> [poly]) -> CalcPoly

makeCase :: String
         -> CalcPoly
         -> [Benchmark]
makeCase name calc =
  [   bgroup name
      [mkTC calc "Cyclic 4"  $ cyclic (sing :: Sing 4)
      ,mkTC calc "Cyclic 5"  $ cyclic (sing :: Sing 5)
      ,mkTC calc "Cyclic 6"  $ cyclic (sing :: Sing 6)
      ,mkTC calc "Katsura 5" $ katsura (sing :: Sing 5)
      ,mkTC calc "Katsura 6" $ katsura (sing :: Sing 6)
      ,mkTC calc "Katsura 7" $ katsura (sing :: Sing 7)
      ]
  ]

mkTC :: forall n. (KnownNat n)
     => CalcPoly
     -> String
     -> Ideal (Polynomial Rational n) -> Benchmark
mkTC (CalcPoly calc) name jdeal =
  let mkPair :: (IsOrderedPolynomial poly)
             => (Polynomial Rational n -> poly)
             -> (Vector poly, Ideal poly)
      mkPair f = (V.fromList $ generators $ map f jdeal, map f jdeal)
  in env (return
        ( mkPair (changeOrder Grevlex)
        , mkPair (changeOrder Lex)
        , mkPair (mapCoeff ratToF . changeOrder Grevlex)
        , mkPair (mapCoeff ratToF . changeOrder Lex)
        , calc
        , calc
        , calc
        , calc
        )
      ) $ \ ~(grjQ, lxjQ, grjF, lxjF, calcGF, calcLF, calcGQ, calcLQ) ->
  bgroup name
    [bench "Q,Grevlex"       $ nf (uncurry calcGQ) grjQ
    ,bench "Q,Lex"           $ nf (uncurry calcLQ) lxjQ
    ,bench "F_65521,Grevlex" $ nf (uncurry calcGF) grjF
    ,bench "F_65521,Lex"     $ nf (uncurry calcLF) lxjF
    ]


ratToF :: Rational -> F 65521
ratToF = modRat'

dic :: [(String, CalcPoly)]
dic = [ ("f5+pot", CalcPoly $ const $ f5With (Proxy :: Proxy POT))
      , ("f5+top", CalcPoly $ const $ f5With (Proxy :: Proxy TOP))
      , ("f5+term-w-pot", CalcPoly $ \vec ->
            reify vec $ \(Proxy :: Proxy vec) ->
            f5With (Proxy @(TermWeightedPOT vec)))
      , ("f5+term-w-top", CalcPoly $ \vec ->
            reify vec $ \(Proxy :: Proxy vec) ->
            f5With (Proxy @(TermWeightedTOP vec)))
      , ("f5+deg-w-pot", CalcPoly $ \vec ->
            reify vec $ \(Proxy :: Proxy vec) ->
            f5With (Proxy @(DegreeWeightedPOT vec)))
      , ("f5+deg-w-top", CalcPoly $ \vec ->
            reify vec $ \(Proxy :: Proxy vec) ->
            f5With (Proxy @(DegreeWeightedTOP vec)))
      ]

main :: IO ()
main = defaultMainWith defaultConfig {csvFile = Just "heavy-f5.csv"} $
    concat [ makeCase nam calc | (nam, calc) <- dic ]
