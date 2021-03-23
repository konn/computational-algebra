{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}

module Main where

import Algebra.Algorithms.Groebner.Signature
import Algebra.Field.Prime
import Algebra.Prelude.Core
import Algebra.Ring.Polynomial.Homogenised
import Cases
import Control.DeepSeq
import Gauge.Main
import Gauge.Main.Options

newtype CalcPoly where
  CalcPoly :: (forall poly. (IsOrderedPolynomial poly, Field (Coefficient poly)) => Ideal poly -> [poly]) -> CalcPoly

makeCase ::
  String ->
  CalcPoly ->
  [Benchmark]
makeCase name calc =
  [ bgroup
      name
      [ mkTC calc "Cyclic-4" $ cyclic (sNat :: SNat 4)
      , mkTC calc "Cyclic-5" $ cyclic (sNat :: SNat 5)
      , mkTC calc "Cyclic-6" $ cyclic (sNat :: SNat 6)
      , mkTC calc "Katsura-5" $ katsura (sNat :: SNat 5)
      , mkTC calc "Katsura-6" $ katsura (sNat :: SNat 6)
      , mkTC calc "Katsura-7" $ katsura (sNat :: SNat 7)
      ]
  ]

data SomeRatIdeal where
  SomeRatIdeal :: (KnownNat n) => Ideal (Polynomial Rational n) -> SomeRatIdeal

data SomeIdeal where
  SomeIdeal ::
    (Field k, NFData k, CoeffRing k, IsMonomialOrder n ord, KnownNat n) =>
    Ideal (OrderedPolynomial k ord n) ->
    SomeIdeal

inputs :: [(String, SomeRatIdeal)]
inputs =
  [ ("Cyclic-4", SomeRatIdeal $ cyclic (sNat :: SNat 4))
  , ("Cyclic-5", SomeRatIdeal $ cyclic (sNat :: SNat 5))
  , ("Cyclic-6", SomeRatIdeal $ cyclic (sNat :: SNat 6))
  , ("Katsura-5", SomeRatIdeal $ katsura (sNat :: SNat 5))
  , ("Katsura-6", SomeRatIdeal $ katsura (sNat :: SNat 6))
  , ("Katsura-7", SomeRatIdeal $ katsura (sNat :: SNat 7))
  ]

data SomeOrd n where
  SomeOrd :: IsMonomialOrder n ord => ord -> SomeOrd n

data SomeToCoe where
  SomeToCoe :: (CoeffRing a, NFData a, Euclidean a, Field a) => (Rational -> a) -> SomeToCoe

variateSetting :: [(String, SomeRatIdeal)] -> [(String, SomeIdeal)]
variateSetting is =
  concat
    [ [toCase name i (coe, toCoe) (ordName, ord)]
    | (name, SomeRatIdeal i) <- is
    , (coe, toCoe) <- [("Q", SomeToCoe id), ("F_65521", SomeToCoe ratToF)]
    , (ordName, ord) <- [("Grevlex", SomeOrd Grevlex), ("Lex", SomeOrd Lex)]
    ]
  where
    toCase ::
      KnownNat n =>
      String ->
      Ideal (Polynomial Rational n) ->
      (String, SomeToCoe) ->
      (String, SomeOrd n) ->
      (String, SomeIdeal)
    toCase name i (coe, SomeToCoe toCoe) (ordName, SomeOrd ord) =
      ( name ++ "/" ++ ordName ++ "," ++ coe
      , SomeIdeal $ fmap (changeOrder ord . mapCoeff toCoe) i
      )

mkTC ::
  forall k ord n.
  (NFData k, KnownNat n, Field k, CoeffRing k, IsMonomialOrder n ord) =>
  CalcPoly ->
  String ->
  Ideal (OrderedPolynomial k ord n) ->
  Benchmark
mkTC (CalcPoly calc) name jdeal =
  env (return jdeal) $ \ideal -> bench name $ nf calc ideal

ratToF :: Rational -> F 65521
ratToF = modRat'

dic :: [(String, CalcPoly)]
dic =
  [ ("f5+pot", CalcPoly $ f5With (Proxy :: Proxy POT))
  , ("f5+top", CalcPoly $ f5With (Proxy :: Proxy TOP))
  , ("f5+t-pot", CalcPoly $ withTermWeights (Proxy @POT) f5With)
  , ("f5+t-top", CalcPoly $ withTermWeights (Proxy @TOP) f5With)
  , ("f5+d-pot", CalcPoly $ withDegreeWeights (Proxy @POT) f5With)
  , ("f5+d-top", CalcPoly $ withDegreeWeights (Proxy @TOP) f5With)
  , ("homog+f5+pot", CalcPoly $ fmap unhomogenise . f5With (Proxy :: Proxy POT) . fmap homogenise)
  , ("homog+f5+top", CalcPoly $ fmap unhomogenise . f5With (Proxy :: Proxy TOP) . fmap homogenise)
  , ("homog+f5+t-pot", CalcPoly $ fmap unhomogenise . withTermWeights (Proxy @POT) f5With . fmap homogenise)
  , ("homog+f5+t-top", CalcPoly $ fmap unhomogenise . withTermWeights (Proxy @TOP) f5With . fmap homogenise)
  , ("homog+f5+d-pot", CalcPoly $ fmap unhomogenise . withDegreeWeights (Proxy @POT) f5With . fmap homogenise)
  , ("homog+f5+d-top", CalcPoly $ fmap unhomogenise . withDegreeWeights (Proxy @TOP) f5With . fmap homogenise)
  ]

main :: IO ()
main =
  defaultMainWith
    defaultConfig {csvFile = Just "heavy-f5.csv"}
    [ bgroup iname [mkTC calc nam jdeal | (nam, calc) <- dic]
    | (iname, SomeIdeal jdeal) <- variateSetting inputs
    ]
