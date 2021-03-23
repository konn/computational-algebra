{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts        #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude, PolyKinds #-}
{-# LANGUAGE QuasiQuotes, TemplateHaskell                        #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Main (module Algebra.Algorithms.Groebner, module Algebra.Prelude
            , module Main
            ) where
import           Algebra.Algorithms.Groebner
import           Algebra.Algorithms.ZeroDim
import           Algebra.Ring.Ideal
import           Algebra.Ring.Polynomial.Quotient
import           Algebra.Prelude
import           Control.Monad.Random             hiding (fromList)
import           Data.Complex
import           Data.Convertible
import           Data.List                        (find, nub, partition, sortBy)
import qualified Data.Matrix                      as M
import qualified Data.Sized               as SV
import qualified Data.Vector                      as V
import           Debug.Trace
import qualified Numeric.LinearAlgebra            as LA
import qualified Prelude                          as P

tr :: Show a => a -> a
tr a = trace (show a) a

x, y, z :: Polynomial (Fraction Integer) 3
[x, y, z] = vars

seed :: Polynomial (Fraction Integer) 3
seed = -412742019532366985 * x -7641395389638504101 * y + 4362835172800530323 * z

seedMat :: LA.Matrix Double
seedMat = LA.fromLists $ map (map toDouble) $ reifyQuotient eqn02 $ \pxy -> matrixRep (modIdeal' pxy seed)

toDouble :: Fractional a => Fraction Integer -> a
toDouble rat = fromIntegral (numerator rat) P./ fromIntegral (denominator rat)

fromRight :: Either t t1 -> t1
fromRight (Right a) = a
fromRight _ = error "fromRight"

printLvl :: Show a => Int -> a -> IO ()
printLvl lvl = putStrLn . unlines . map (replicate lvl '\t' ++) . lines . show

eqn01 :: Ideal (Polynomial (Fraction Integer) 3)
eqn01 = toIdeal [x^2 - 2*x*z + 5, x*y^2+y*z+1, 3*y^2 - 8*x*z]

eqn02 :: Ideal (Polynomial (Fraction Integer) 3)
eqn02 =
  toIdeal [x^2 + 2*y^2 - y - 2*z
          ,x^2 - 8*y^2 + 10*z - 1
          ,x^2 - 7*y*z
          ]

eqn03 :: Ideal (Polynomial (Fraction Integer) 3)
eqn03 = toIdeal [x^2 + y^2 + z^2 - 2*x
                ,x^3 - y*z - x
                ,x - y + 2*z
                ]

jdeal :: Ideal (Polynomial (Fraction Integer) 3)
jdeal = toIdeal [x*y + z - x*z, x^2 - z, 2*x^3 - x^2 * y * z - 1]


vs :: [V.Vector (Fraction Integer)]
vs = reifyQuotient eqn03 $ \pxy -> map (vectorRep . modIdeal' pxy) [var 0 ^ i | i <- [0..6::Natural]]

mat :: M.Matrix (Fraction Integer)
mat = fromCols $ take 4 vs

fromCols :: [V.Vector a] -> M.Matrix a
fromCols = foldr1 (M.<|>) . map M.colVector

findUnivar :: (CoeffRing r, IsMonomialOrder n ord, KnownNat n)
           => OrderedPolynomial r ord n -> Maybe (Ordinal n)
findUnivar poly =
  let os = enumOrdinal (sArity' poly)
      ms = map snd $ getTerms poly
  in find (\a -> all (`isPowerOf` (leadingMonomial (var a `asTypeOf` poly))) ms) os

toCoeffList :: (CoeffRing r,  KnownNat n, IsMonomialOrder n ord) => Ordinal n -> OrderedPolynomial r ord n -> [r]
toCoeffList on f =
  let v = var on  `asTypeOf` f
  in [ coeff (leadingMonomial $ v ^ i) f | i <- [0.. fromIntegral (totalDegree' f)]]

showSols :: (KnownNat n, IsMonomialOrder n order, Convertible a Double)
         => Double -> Ideal (OrderedPolynomial a order n) -> [Sized n1 (Complex Double)] -> IO ()
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
  putStrLn "---- solving equation system"
  let err = 1e-10
  putStrLn "< naive method"
  showSols err eqn01 $ solve' err eqn01
  putStrLn "\n< randomized method"
  showSols err eqn01 =<< evalRandIO (solveM eqn01)
  putStrLn "\n< companion characteristics"
  showSols err eqn01 $ solveViaCompanion err eqn01
  putStrLn "\n< univariate spanning"
  showSols err eqn01 $ solve' err eqn01

  putStrLn "\n\n---- exercise 8"
  putStrLn "< Solving 1-6"
  putStrLn "< Naive Method: "
  showSols err eqn02 $ nub $ solve' err eqn02
  putStrLn "\n< new method"
  showSols err eqn02 =<< evalRandIO (solveM eqn02)

  putStrLn "\n< Solving 1-7"
  putStrLn "< Naive Method: "
  showSols err eqn03 $ nub $ solve' err eqn03
  putStrLn "\n< new method"
  showSols err eqn03 =<< evalRandIO (solveM eqn03)
  putStrLn "\n\n---- FGLM Algorithm"
  print $ fglm jdeal
  print $ calcGroebnerBasisWith Lex jdeal
  print $ univPoly 0 jdeal
  print $ univPoly 1 jdeal
  print $ univPoly 2 jdeal
  return ()

substIdeal :: IsMonomialOrder 3 order
           => [OrderedPolynomial (Fraction Integer) Grevlex 3]
           -> Ideal (OrderedPolynomial (Fraction Integer) order 3)
           -> Ideal (OrderedPolynomial (Fraction Integer) Grevlex 3)
substIdeal = mapIdeal . substWith (.*.) . SV.unsafeFromList'

toComplex :: Convertible r Double => r -> Complex Double
toComplex = (:+ 0) . convert
