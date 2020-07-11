{-# LANGUAGE DataKinds, TypeApplications #-}
module Main where
import Algebra.Field.Finite
import Algebra.Field.Prime
import AlgebraicPrelude
import Control.DeepSeq      (($!!))
import Data.Proxy           (Proxy (Proxy))
import Gauge

main :: IO ()
main = defaultMain
  [ bgroup "recip a middle"
    [ env (pure $!! modNat @_ @2 (2 `div` 2 :: Integer)) $ \ pr ->
        bench "F 2" $ nf recip pr
    , env (pure $!! modNat @_ @5 (5 `div` 2 :: Integer)) $ \ pr ->
        bench "F 5" $ nf recip pr
    , env (pure $!! modNat @_ @59 (59 `div` 2 :: Integer)) $ \ pr ->
        bench "F 59" $ nf recip pr
    , env (pure $!! modNat @_ @12379 (12379 `div` 2 :: Integer)) $ \ pr ->
        bench "F 12379" $ nf recip pr
    , env (pure $!! modNat @_ @3037000507 (3037000507 `div` 2 :: Integer)) $ \ pr ->
        bench "F 3037000507 (large)" $ nf recip pr
    ]
  , bgroup "product of units"
    [ env (pure $!! filter isUnit (elements @(F 2) Proxy)) $ \units ->
        bench "F 2" $ nf product units
    , env (pure $!! filter isUnit (elements @(F 5) Proxy)) $ \units ->
        bench "F 5" $ nf product units
    , env (pure $!! filter isUnit (elements @(F 59) Proxy)) $ \units ->
        bench "F 59" $ nf product units
    , env (pure $!! filter isUnit (elements @(F 12379) Proxy)) $ \units ->
        bench "F 12379" $ nf product units
    ]
  , bgroup "sum of prefix-products"
    [ env (pure $!! tail $ inits $ filter isUnit (elements @(F 2) Proxy)) $ \units ->
        bench "F 2" $ nf (sum . map product) units
    , env (pure $!! tail $ inits $ filter isUnit (elements @(F 5) Proxy)) $ \units ->
        bench "F 5" $ nf (sum . map product) units
    , env (pure $!! tail $ inits $ filter isUnit (elements @(F 59) Proxy)) $ \units ->
        bench "F 59" $ nf (sum . map product) units
    , env (pure $!! tail $ inits $ filter isUnit (elements @(F 6197) Proxy)) $ \units ->
        bench "F 6197" $ nf (sum . map product) units
    ]
  ]
