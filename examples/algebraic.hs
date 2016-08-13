{-# LANGUAGE DataKinds, NoImplicitPrelude, OverloadedLabels #-}
module Main where
import Algebra.Field.AlgebraicReal
import Algebra.Prelude
import Algebra.Ring.Polynomial.Univariate

f :: Unipol Rational
f = 8 - 16 * #x + 12* #x^2 - 4* #x^3 + #x^4

main :: IO ()
main = do
  print f
  print $ complexRoots f
