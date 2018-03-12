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

x :: Unipol Integer
x = var 0

allCoeffOne :: Int -> Unipol Integer
allCoeffOne n = sum [x ^ i | i <- [0..n]]

mkSimpleEnv :: Int -> IO (Unipol Integer, Unipol Integer)
mkSimpleEnv n = return (x - 1, allCoeffOne n)

fromOP :: OrderedPolynomial (Fraction Integer) Grevlex 1
       -> Unipol (Fraction Integer)
fromOP = injectVars

showProxyType :: Typeable a => Proxy a -> String
showProxyType pxy =
  let str = show $ typeRep pxy
  in if str == "Fraction Integer"
     then "rational"
     else map toLower str

fromCoeffVec :: CoeffRing r => [r] -> Unipol r
fromCoeffVec = polynomial' . M.fromList . zip [singleton n | n <- [0..]]

genPoly :: (Typeable r, CoeffRing r, QC.Arbitrary r)
        => Proxy r -> Int -> IO (Unipol r)
genPoly _ len = QC.generate $ fromCoeffVec <$> QC.vectorOf len QC.arbitrary

genPair pxy l r = do
  (f, g) <- (,) <$> genPoly pxy l <*> genPoly pxy r
  let path = intercalate "-" ["bench/results/unipol-mult", showProxyType pxy, show l, show r]
             ++ ".txt"
  writeFile path $ unlines [show f, show g]
  return (f, g)

int :: Proxy Integer
int = Proxy

rat :: Proxy (Fraction Integer)
rat = Proxy

main :: IO ()
main = do
  defaultMain $
    [ bgroup "(x-1)(x^n+...+x+1)"
      [ env (mkSimpleEnv n) $ \ ~(f, g) ->
         bgroup (show n)
         [bench "naive" $ nf (uncurry naiveMult) (f, g)
         ,bench "karatsuba" $ nf (uncurry karatsuba) (f, g)
         ]
      | n <- [1,4,8,16] ++ [50,100,500,1000,10000]
      ]
    , bgroup "(x^n+...+x+1)^2"
      [ env (return (allCoeffOne n, allCoeffOne n)) $ \ ~(f, g) ->
         bgroup (show n)
         [bench "naive" $ nf (uncurry naiveMult) (f, g)
         ,bench "karatsuba" $ nf (uncurry karatsuba) (f, g)
         ]
      | n <- [1,4,8,16] ++ [50,100,500,1000,10000]
      ]
    , bgroup "random" $
      [ env (genPair int l r) $ \ ~(f, g) ->
         bgroup ("Integer: " ++ show l ++ " x " ++ show r)
         [bench "naive" $ nf (uncurry naiveMult) (f, g)
         ,bench "karatsuba" $ nf (uncurry karatsuba) (f, g)
         ]
      | (l, r) <- [(5,5), (10,10), (100,100),(1000,1000)]
      ] ++
      [ env (genPair rat l r) $ \ ~(f, g) ->
         bgroup ("Rational: " ++ show l ++ " x " ++ show r)
         [bench "naive" $ nf (uncurry naiveMult) (f, g)
         ,bench "karatsuba" $ nf (uncurry karatsuba) (f, g)
         ]
      | (l, r) <- [(5,5), (10,10), (100,100),(1000,1000)]
      ]
    ]
