{-# LANGUAGE DataKinds #-}
module Main where
import           Algebra.Ring.Polynomial            (OrderedPolynomial)
import           Algebra.Ring.Polynomial.Univariate
import           Data.Char                          (toLower)
import           Data.List                          (intercalate)
import qualified Data.Map                           as M
import           Data.Proxy                         (Proxy (..))
import           Data.Sized.Builtin                 (singleton)
import           Data.Typeable
import           Gauge.Main
import           Numeric.Field.Fraction
import qualified Test.QuickCheck                    as QC
import           Utils                              ()

x :: Unipol (Fraction Integer)
x = var 0

mkSimpleEnv :: Int -> IO (Unipol (Fraction Integer), Unipol (Fraction Integer))
mkSimpleEnv n = return (x ^ n - 1, x - 1)

fromOP :: OrderedPolynomial (Fraction Integer) Grevlex 1
       -> Unipol (Fraction Integer)
fromOP = injectVars

fromCoeffVec :: CoeffRing r => [r] -> Unipol r
fromCoeffVec = polynomial' . M.fromList . zip [singleton n | n <- [0..]]

genPoly :: Int -> IO (Unipol (Fraction Integer))
genPoly len = QC.generate $ fromCoeffVec <$> QC.vectorOf len QC.arbitrary

genPair l r = do
  (f, g) <- (,) <$> genPoly l <*> genPoly r
  let path = intercalate "-" ["bench/results/unipol-div-", show l, "-", show r]
             ++ ".txt"
  writeFile path $ unlines [show f, show g]
  return (f, g)

main :: IO ()
main = do
  defaultMain $
    [ bgroup "(x^n-1)%(x-1)"
      [ env (mkSimpleEnv n) $ \ ~(f, g) ->
         bgroup (show n)
         [bench "naive" $ nf (uncurry divModUnipol) (f, g)
         ,bench "mult" $ nf (uncurry divModUnipol) (f, g)
         ]
      | n <- [1,4,8,16] ++ [50,100,500,1000,10000]
      ]
    , bgroup "random" $
      [ env (genPair l r) $ \ ~(f, g) ->
         bgroup (show l ++ " % " ++ show r)
         [bench "naive" $ nf (uncurry divModUnipol) (f, g)
         ,bench "mult" $ nf (uncurry divModUnipolByMult) (f, g)
         ]
      | (l, r) <- [(5,2), (10,5), (100,50),(200,100),(500,250)]
      ]
    ]
