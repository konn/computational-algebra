module Main where
import Algebra.Ring.Polynomial.Univariate
import Criterion.Main

x :: Unipol Integer
x = var 0

allCoeffOne :: Int -> Unipol Integer
allCoeffOne n = sum [x ^ i | i <- [0..n]]

mkSimpleEnv :: Int -> IO (Unipol Integer, Unipol Integer)
mkSimpleEnv n = return (x - 1, allCoeffOne n)

main :: IO ()
main = do
  defaultMain $
    [ bgroup "(x-1)(x^n+...+x+1)"
      [ env (mkSimpleEnv n) $ \ ~(f, g) ->
         bgroup (show n)
         [bench "naive" $ nf (uncurry naiveMult) (f, g)
         ,bench "karatsuba" $ nf (uncurry naiveMult) (f, g)
         ]
      | n <- [1..10] ++ [20,40,80,100, 200,500,1000]
      ],
      bgroup "(x^n+...+x+1)^2"
      [ env (return (allCoeffOne n, allCoeffOne n)) $ \ ~(f, g) ->
         bgroup (show n)
         [bench "naive" $ nf (uncurry naiveMult) (f, g)
         ,bench "karatsuba" $ nf (uncurry naiveMult) (f, g)
         ]
      | n <- [1..10] ++ [20,40,80,100, 200,500,1000]
      ]
    ]
