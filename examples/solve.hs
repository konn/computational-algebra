{-# LANGUAGE DataKinds, FlexibleContexts, MultiParamTypeClasses              #-}
{-# LANGUAGE NoImplicitPrelude, OverlappingInstances, PolyKinds, QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell                                                 #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Main (module Algebra.Algorithms.Groebner, module Algebra.Ring.Polynomial
            , module Data.Ratio, module Main, module Algebra.Internal
            ) where
import           Algebra.Algorithms.Groebner
import           Algebra.Algorithms.ZeroDim
import           Algebra.Internal
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Algebra.Ring.Polynomial.Quotient
import           Algebra.Scalar
import           Control.Applicative
import           Control.Monad.Random
import           Data.Complex
import           Data.Ratio
import           Data.Type.Natural
import qualified Data.Vector.Sized                as V
import           Numeric.Algebra                  hiding ((<), (^^))
import qualified Numeric.Algebra                  as NA
import           Numeric.LinearAlgebra
import           Prelude                          hiding (Fractional (..),
                                                   Integral (..), Num (..),
                                                   Real (..), (^^))
import qualified Prelude                          as P
import           System.Random

x, y, z :: Polynomial Rational Three
[x, y, z] = genVars sThree

(.*) :: Rational -> Polynomial Rational Three -> Polynomial Rational Three
(.*) = (.*.)

infixl 7 .*

(^^) :: Polynomial Rational Three -> NA.Natural -> Polynomial Rational Three
(^^) = NA.pow

fromRight :: Either t t1 -> t1
fromRight (Right a) = a
fromRight _ = error "fromRight"

main :: IO ()
main = do
  let err = 1e-5
      orig = [x^^2 - 2*x*z + 5, x*y^^2+y*z+1, 3*y^^2 - 8*x*z]
      showSols sols = do
        mapM_ print $ map (\ [a,b,c] -> (a, b, c)) $  map V.toList sols
        putStrLn $ show (length $ filter (all ((<err).P.abs.imagPart)) $ map V.toList sols) ++ " real solution(s)."
  let ideal = toIdeal [ 3*y^^2-8*x*z
                      , x^^2-2*x*z+5
                      , 160*z^^3-160*x*z+415*y*z+12*x-30*y-224*z+15
                      , 1920*y*z^^2+13280*z^^3-72*x*y-480*x*z+34589*y*z+960*z^^2+36*x-2490*y-16672*z+1245
                      , 16*x*z^^2+3*y*z-40*z+3
                      , 12*x*y*z-24*y*z^^2-160*z^^3-415*y*z+30*y+200*z-15
                      ]
  showSols =<< evalRandT (solveM ideal) =<< getStdGen
  showSols $ solve' err ideal
  return ()




coerceDouble :: Coercible a (Complex Double) => a -> Complex Double
coerceDouble = coerce
