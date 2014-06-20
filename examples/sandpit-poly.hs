{-# LANGUAGE DataKinds, NoImplicitPrelude, OverlappingInstances, PolyKinds #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Main (module Algebra.Algorithms.Groebner, module Algebra.Ring.Polynomial
            , module Numeric.Field.Fraction, module Main, module Algebra.Internal
            ) where
import Algebra.Algorithms.Groebner
import Algebra.Internal
import Algebra.Prelude
import Algebra.Ring.Ideal
import Algebra.Ring.Polynomial
import Data.Type.Natural
import Numeric.Field.Fraction

u, v, x, y, z :: Polynomial (Fraction Integer) Five
[u, v, x, y, z] = genVars sFive

fromRight :: Either t t1 -> t1
fromRight (Right a) = a
fromRight _ = error "fromRight"


main :: IO ()
main = do
  print $ thEliminationIdealWith (eliminationOrder sTwo) sTwo $
        toIdeal [x - (3*u + 3*u*v^2 - u^3), y - (3*v + 3*u^2*v -  v^3), z - (3*u^2 - 3*v^2)]
