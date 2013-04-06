{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings, PolyKinds   #-}
{-# LANGUAGE QuasiQuotes, TemplateHaskell, UndecidableInstances    #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
import Algebra.Algorithms.Groebner.Monomorphic
import Algebra.Ring.Polynomial.Monomorphic
import Control.DeepSeq
import Control.Parallel.Strategies
import Criterion.Main

x, y, z, w, s, a, b, c :: Polynomial Rational
[x, y, z, w, s, a, b, c] = map (injectVar . flip Variable Nothing) "xyzwSabc"

instance NFData Variable where
  rnf (Variable x y) = rnf x `seq` rnf y `seq` ()

instance NFData (Polynomial Rational) where
  rnf (Polynomial dic) = rnf dic

i1, i2, i3, i4 :: [Polynomial Rational]
i1 = [x^2 + y^2 + z^2 - 1, x^2 + y^2 + z^2 - 2*x, 2*x -3*y - z]
i2 = [x^2 * y - 2*x*y - 4*z - 1, z-y^2, x^3 - 4*z*y]
i3 = [ 2 * s - a * y, b^2 - (x^2 + y^2), c^2 - ( (a-x) ^ 2 + y^2)
         ]
i4 = [ z^5 + y^4 + x^3 - 1, z^3 + y^3 + x^2 - 1]

mkTestCases :: (Eq r, Show a, r ~ Rational) => a -> [Polynomial r] -> [Benchmark]
mkTestCases num ideal = [ mkTC ("lex0" ++ show num) ideal Lex
                        , mkTC ("grlex0" ++ show num) ideal Grlex
                        , mkTC ("grevlex0" ++ show num) ideal Grevlex
                        ]

mkTC :: (r ~ Rational, IsMonomialOrder ord) => String -> [Polynomial r] -> ord -> Benchmark
mkTC name ideal ord =
    bgroup name [ bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy ord) ideal
                , bench "syz+grad" $ nf (syzygyBuchbergerWithStrategy GradedStrategy ord) ideal
                , bench "syz+sugar" $ nf (syzygyBuchbergerWithStrategy (SugarStrategy NormalStrategy) ord) ideal
                , bench "syz+grsugar" $ nf (syzygyBuchbergerWithStrategy (SugarStrategy GradedStrategy) ord) ideal
                ]

main :: IO ()
main = do
  ideal1 <- return $! (i1 `using` rdeepseq)
  ideal2 <- return $! (i2 `using` rdeepseq)
  ideal3 <- return $! (i3 `using` rdeepseq)
  ideal4 <- return $! (i4 `using` rdeepseq)
  defaultMain $ concat $ zipWith mkTestCases [1..] [ideal1, ideal2, ideal3, ideal4]

