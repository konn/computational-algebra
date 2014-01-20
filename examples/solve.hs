{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts                   #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude, OverlappingInstances #-}
{-# LANGUAGE PolyKinds, QuasiQuotes, TemplateHaskell                        #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Main (module Algebra.Algorithms.Groebner, module Algebra.Ring.Polynomial
            , module Data.Ratio, module Main, module Algebra.Internal
            ) where
import           Algebra.Algorithms.FGLM
import           Algebra.Algorithms.Groebner
import           Algebra.Algorithms.ZeroDim
import           Algebra.Internal
import qualified Algebra.Linear                   as M
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Algebra.Ring.Polynomial.Quotient
import           Algebra.Scalar
import           Control.Lens
import           Control.Monad.Random             hiding (fromList)
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

x, y, z :: Polynomial Rational Three
[x, y, z] = genVars sThree

(.*) :: SingRep n => Rational -> Polynomial Rational n -> Polynomial Rational n
(.*) = (.*.)

infixl 7 .*

(^^) :: Unital r => r -> NA.Natural -> r
(^^) = NA.pow

seed :: Polynomial Rational Three
seed = -412742019532366985 * x -7641395389638504101 * y + 4362835172800530323 * z

seedMat :: LA.Matrix Double
seedMat = LA.fromLists $ map (map P.fromRational) $ reifyQuotient eqn02 $ \pxy -> matrixRep (modIdeal' pxy seed)

fromRight :: Either t t1 -> t1
fromRight (Right a) = a
fromRight _ = error "fromRight"

printLvl :: Show a => Int -> a -> IO ()
printLvl lvl = putStrLn . unlines . map (replicate lvl '\t' ++) . lines . show

eqn01 :: Ideal (Polynomial Rational Three)
eqn01 = toIdeal [x^^2 - 2*x*z + 5, x*y^^2+y*z+1, 3*y^^2 - 8*x*z]

eqn02 :: Ideal (Polynomial Rational Three)
eqn02 =
  toIdeal [x^^2 + 2*y^^2 - y - 2*z
          ,x^^2 - 8*y^^2 + 10*z - 1
          ,x^^2 - 7*y*z
          ]

eqn03 :: Ideal (Polynomial Rational Three)
eqn03 = toIdeal [x^^2 + y^^2 + z^^2 - 2*x
                ,x^^3 - y*z - x
                ,x - y + 2*z
                ]

jdeal :: Ideal (Polynomial Rational Three)
jdeal = toIdeal [x*y + z - x*z, x^^2 - z, 2*x^^3 - x^^2 * y * z - 1]


vs :: [V.Vector Rational]
vs = reifyQuotient eqn03 $ \pxy -> map (vectorRep . modIdeal' pxy) [var 0 ^^ i | i <- [0..6::Natural]]

mat :: M.Matrix Rational
mat = fromCols $ take 4 vs

fromCols :: [V.Vector a] -> M.Matrix a
fromCols = foldr1 (M.<|>) . map M.colVector

findUnivar :: (NoetherianRing r, Eq r, IsOrder ord, SingRep n) => OrderedPolynomial r ord n -> Maybe (Ordinal n)
findUnivar poly =
  let os = enumOrdinal (sArity poly)
      ms = map snd $ getTerms poly
  in find (\a -> all (`isPowerOf` (leadingMonomial (var a `asTypeOf` poly))) ms) os

toCoeffList :: (Eq r, SingRep n, NoetherianRing r, IsOrder ord) => Ordinal n -> OrderedPolynomial r ord n -> [r]
toCoeffList on f =
  let v = var on  `asTypeOf` f
  in [ coeff (leadingMonomial $ v ^^ i) f | i <- [0.. fromIntegral (totalDegree' f)]]


{-
solveByElimination :: (Eq r, Ord r, SingRep n, NoetherianRing r,
                       IsMonomialOrder ord, Convertible r Double, Field r)
                   => Ideal (OrderedPolynomial r ord (S n)) -> [SV.Vector (Complex Double) (S n)]
solveByElimination ideal =
  let gb = map (mapCoeff toComplex) $ fst $ fglm $ toIdeal $ calcGroebnerBasisWith Grevlex ideal
      step f vec =
        let g = substWith (.*.) vec f
            typ = [g] `asTypeOf` gb
        in if totalDegree' g == 0
           then return vec
           else do
             let Just v = findUnivar g
             ans <- polySolve (map realPart $ toCoeffList v g)
             return $ vec & ix v .~ injectCoeff ans
  in map (SV.map (coeff (fromList (sArity $ head gb) []))) $ foldrM step allVars gb
-}
main :: IO ()
main = do
  putStrLn "---- solving equation system"
  let err = 1e-10
      showSols eqn sols = do
        let (rs, is) = partition (all ((<err).P.abs.imagPart)) $ map SV.toList sols
            subs a b c = maximum $ generators $ mapIdeal (magnitude . substWith (*) (SV.unsafeFromList' [a, b, c]) . mapCoeff toComplex) eqn
            showCase [a,b,c] = print (a, b, c) >> putStr "\terror: ">> print (subs a b c)
        putStrLn $ "- " ++ show (length rs) ++ " real solution(s):"
        mapM_ showCase $ sortBy (comparing $ map magnitude) rs
        putStrLn $ "- " ++ show (length is) ++ " imaginary solution(s):"
        mapM_  showCase $ sortBy (comparing $ map magnitude) is
  putStrLn "< naive method"
  showSols eqn01 $ solve' err eqn01
  putStrLn "\n< randomized method"
  showSols eqn01 =<< evalRandIO (solveM eqn01)
  putStrLn "\n< companion characteristics"
  showSols eqn01 $ solveViaCompanion err eqn01
  putStrLn "\n\n---- exercise 8"
  putStrLn "< Solving 1-6"
  putStrLn "< Naive Method: "
  showSols eqn02 $ nub $ solve' err eqn02
  putStrLn "\n< new method"

  showSols eqn02 =<< evalRandIO (solveM eqn02)
  putStrLn "\n< Solving 1-7"
  putStrLn "< Naive Method: "
  showSols eqn03 $ nub $ solve' err eqn03
  putStrLn "\n< new method"
  showSols eqn03 =<< evalRandIO (solveM eqn03)
  putStrLn "\n\n---- FGLM Algorithm"
  print $ fglm jdeal
  print $ calcGroebnerBasisWith Lex jdeal
  print $ univPoly 0 jdeal
  print $ univPoly 1 jdeal
  print $ univPoly 2 jdeal
  return ()

substIdeal :: [OrderedPolynomial Rational Grevlex Three]
           -> Ideal (OrderedPolynomial Rational order Three)
           -> Ideal (OrderedPolynomial Rational Grevlex Three)
substIdeal = mapIdeal . substWith (.*.) . SV.unsafeFromList'

toComplex :: Convertible r Double => r -> Complex Double
toComplex = (:+ 0) . convert
