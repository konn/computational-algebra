{-# LANGUAGE DataKinds, NoImplicitPrelude, OverloadedLabels #-}
module Main where
import Algebra.LinkedMatrix
import Algebra.Prelude
import Algebra.Ring.Polynomial.Factorise
import Control.DeepSeq
import Control.Exception                 (evaluate)

main :: IO ()
main = do
  print =<< factorHensel (#x ^5)
