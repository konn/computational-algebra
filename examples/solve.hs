{-# LANGUAGE DataKinds, FlexibleContexts, MultiParamTypeClasses              #-}
{-# LANGUAGE NoImplicitPrelude, OverlappingInstances, PolyKinds, QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell                                                 #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Main (module Algebra.Algorithms.Groebner, module Algebra.Ring.Polynomial
            , module Data.Ratio, module Main, module Algebra.Internal
            ) where
import           Algebra.Algorithms.FGLM
import           Algebra.Algorithms.Groebner
import           Algebra.Algorithms.ZeroDim
import           Algebra.Internal
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Algebra.Scalar
import           Data.Complex
import           Data.Ratio
import           Data.Type.Natural
import qualified Data.Vector.Sized           as SV
import           Numeric.Algebra             hiding ((<))
import qualified Numeric.Algebra             as NA
import           Prelude                     hiding (Fractional (..),
                                              Integral (..), Num (..),
                                              Real (..), sum, (^^))
import qualified Prelude                     as P

x, y, z :: Polynomial Rational Three
[x, y, z] = genVars sThree

(.*) :: SingRep n => Rational -> Polynomial Rational n -> Polynomial Rational n
(.*) = (.*.)

infixl 7 .*

(^^) :: SingRep n => Polynomial Rational n -> NA.Natural -> Polynomial Rational n
(^^) = NA.pow

fromRight :: Either t t1 -> t1
fromRight (Right a) = a
fromRight _ = error "fromRight"

printLvl :: Show a => Int -> a -> IO ()
printLvl lvl = putStrLn . unlines . map (replicate lvl '\t' ++) . lines . show

main :: IO ()
main = do
  putStrLn "---- solving equation system"
  let err = 1e-5
      orig = [x^^2 - 2*x*z + 5, x*y^^2+y*z+1, 3*y^^2 - 8*x*z]
      showSols sols = do
        mapM_ print $ map (\ [a,b,c] -> (a, b, c)) $  map SV.toList sols
        putStrLn $ show (length $ filter (all ((<err).P.abs.imagPart)) $ map SV.toList sols) ++ " real solution(s)."
  let ideal = toIdeal orig
  showSols $ solve' err ideal
  putStrLn "\n---- FGLM Algorithm"
  let jdeal = toIdeal [x*y + z - x*z, x^^2 - z, 2*x^^3 - x^^2 * y * z - 1]
  print $ fglm jdeal
  print $ calcGroebnerBasisWith Lex jdeal
  return ()
