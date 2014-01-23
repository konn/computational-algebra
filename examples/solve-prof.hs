{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts                   #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude, OverlappingInstances #-}
{-# LANGUAGE PolyKinds, QuasiQuotes, TemplateHaskell                        #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Main (module Algebra.Algorithms.Groebner, module Algebra.Ring.Polynomial
            , module Data.Ratio, module Main, module Algebra.Internal
            ) where
import           Algebra.Algorithms.Groebner
import           Algebra.Algorithms.ZeroDim
import           Algebra.Internal
import qualified Algebra.Linear                   as M
import           Algebra.Matrix                   (companion)
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Algebra.Ring.Polynomial.Quotient
import           Algebra.Scalar
import           Control.DeepSeq
import           Control.Lens
import           Control.Monad.Random             hiding (fromList)
import           Control.Parallel.Strategies
import           Data.Complex
import           Data.Convertible
import           Data.Foldable                    (foldrM)
import           Data.List                        (find, nub, partition, sortBy)
import           Data.Ord
import           Data.Ratio
import           Data.Type.Natural                hiding (one, zero)
import           Data.Type.Ordinal
import qualified Data.Vector                      as V
import qualified Data.Vector.Sized                as SV
import           Debug.Trace
import           Numeric.Algebra                  hiding ((.*), (<))
import qualified Numeric.Algebra                  as NA
import           Numeric.GSL.Polynomials
import qualified Numeric.LinearAlgebra            as LA
import           Prelude                          hiding (Fractional (..),
                                                   Integral (..), Num (..),
                                                   Real (..), sum, (^^))
import qualified Prelude                          as P

tr :: Show a => a -> a
tr a = trace (show a) a

x, y, z, w :: Polynomial Rational Four
[x, y, z, w] = genVars sFour

(.*) :: SingRep n => Rational -> Polynomial Rational n -> Polynomial Rational n
(.*) = (.*.)

infixl 7 .*

(^^) :: Unital r => r -> NA.Natural -> r
(^^) = NA.pow

fromRight :: Either t t1 -> t1
fromRight (Right a) = a
fromRight _ = error "fromRight"

printLvl :: Show a => Int -> a -> IO ()
printLvl lvl = putStrLn . unlines . map (replicate lvl '\t' ++) . lines . show

eqn01 :: Ideal (Polynomial Rational Four)
eqn01 = toIdeal [ x^^2 - 2*x*z + 5
                , x*y^^2+y*z+1
                , 3*y^^2 - 8*x*z
                , w^^3+x^^2+x*y*z-1
                ]

findUnivar :: (NoetherianRing r, Eq r, IsOrder ord, SingRep n) => OrderedPolynomial r ord n -> Maybe (Ordinal n)
findUnivar poly =
  let os = enumOrdinal (sArity poly)
      ms = map snd $ getTerms poly
  in find (\a -> all (`isPowerOf` (leadingMonomial (var a `asTypeOf` poly))) ms) os

toCoeffList :: (Eq r, SingRep n, NoetherianRing r, IsOrder ord) => Ordinal n -> OrderedPolynomial r ord n -> [r]
toCoeffList on f =
  let v = var on  `asTypeOf` f
  in [ coeff (leadingMonomial $ v ^^ i) f | i <- [0.. fromIntegral (totalDegree' f)]]

showSols err eqn sols = do
  let (rs, is) = partition (all ((<err).P.abs.imagPart)) $ map SV.toList sols
      subs a b c = generators $
                   mapIdeal (magnitude . substWith (*) (SV.unsafeFromList' [a, b, c]) . mapCoeff toComplex)
                            eqn
      showCase [a,b,c] = print (a, b, c) >> putStr "\terror: ">> print (maximum $ subs a b c)
  putStrLn $ "- " ++ show (length rs) ++ " real solution(s):"
  mapM_ showCase $ sortBy (comparing $ map magnitude) rs
  putStrLn $ "- " ++ show (length is) ++ " imaginary solution(s):"
  mapM_  showCase $ sortBy (comparing $ map magnitude) is
  let errs = concatMap (\ [a,b,c] -> subs a b c) $ rs ++ is
  putStrLn $ "- maximum error: " ++ show (maximum errs)
  putStrLn $ "- minimum error: " ++ show (minimum errs)
  putStrLn $ "- average error: " ++ show (sum errs P./ fromIntegral (length errs))

main :: IO ()
main = do
  evaluate' =<< evalRandIO (solveM eqn01)
  return ()

evaluate' :: NFData a => a -> IO a
evaluate' a  = return $!! (a `using` rdeepseq)

substIdeal :: [OrderedPolynomial Rational Grevlex Three]
           -> Ideal (OrderedPolynomial Rational order Three)
           -> Ideal (OrderedPolynomial Rational Grevlex Three)
substIdeal = mapIdeal . substWith (.*.) . SV.unsafeFromList'

toComplex :: Convertible r Double => r -> Complex Double
toComplex = (:+ 0) . convert
