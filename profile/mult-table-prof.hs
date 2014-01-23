{-# LANGUAGE DataKinds, ExtendedDefaultRules, NoImplicitPrelude, PatternGuards #-}
module Main where
import Algebra.Algorithms.GroebnerOld
import Algebra.Ring.Noetherian
import Algebra.Ring.Polynomial.QuotientOld
import Algebra.Ring.PolynomialOld
import Algebra.Scalar
import Control.Applicative
import Control.DeepSeq
import Control.Parallel.Strategies
import Data.List                           (foldl')
import Data.Ratio
import Data.Type.Natural
import Numeric.Algebra                     hiding ((/))
import Prelude                             hiding (Integral (..), Num (..),
                                            product, (-), (/), (^), (^^))
import System.Environment
import Test.QuickCheck
import Utils

default (Integer)

type Polyn = Polynomial Rational Two

(^^) :: Unital r => r -> Natural -> r
(^^) = pow

(/) :: Integer -> Integer -> Polynomial Rational Two
a / b = injectCoeff $ a % b

x, y :: Polynomial Rational Two
[x, y] = genVars sTwo

ideal :: Ideal (Polynomial Rational Two)
ideal = toIdeal [-7/3 * x^^9 - 2/5 ,-5/8 * y^^21 + 8/3 * y^^7 + 5/7 * y^^3 - 8/7 * y^^2 - 1/3 * y]

fs :: [Polynomial Rational Two]
fs = [7/10 * x^^18 * y^^19 - 5 * x^^28 - 7/2 * y^^28 - 9/5 * y^^27]

main :: IO ()
main = do
  args <- getArgs
  let (l, n, m) | ([(l0, _)]:[(n0, _)]:[(m0, _)]:_) <- map reads args = (l0, n0, m0)
                | otherwise               = (2, 5, 6)
  -- ideal <- withStrategy rdeepseq . getIdeal . head <$> sample' (resize n arbitrary)
  -- fs <- return . (withStrategy rdeepseq) . take l =<< sample' (resize m $ polyOfDim sTwo)
  putStrLn "generated!"
  return $!! ideal `deepseq` rnf fs
  print $ withQuotient ideal $ product $ map modIdeal fs
