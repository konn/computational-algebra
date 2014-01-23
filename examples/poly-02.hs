{-# LANGUAGE DataKinds, OverloadedStrings, PolyKinds #-}
module Main where
import Algebra.Algorithms.Groebner
import Algebra.Internal
import Algebra.Ring.Noetherian
import Algebra.Ring.Polynomial

x, y :: OrderedPolynomial Rational Lex Two
[x, y] = genVars sTwo

main :: IO ()
main = print $ reduceMinimalGroebnerBasis $ minimizeGroebnerBasis $ simpleBuchberger $ toIdeal [x^2*y-1,x^3-y^2-x]
