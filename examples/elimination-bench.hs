{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings, PolyKinds #-}
{-# LANGUAGE TemplateHaskell, UndecidableInstances               #-}
import           Algebra.Algorithms.Groebner.Monomorphic
import           Algebra.Internal
import           Algebra.Ring.Polynomial                 (eliminationOrder, weightedEliminationOrder)
import           Algebra.Ring.Polynomial.Monomorphic
import           Control.DeepSeq
import           Control.Parallel.Strategies
import           Criterion.Main
import           Criterion.Types
import           Numeric.Algebra                         (LeftModule (..))
import qualified Numeric.Algebra                         as NA

x, y, z, w, s, a, b, c, t, u, v :: Polynomial Rational
[x, y, z, w, s, a, b, c, t, u, v, x', y'] = map (injectVar . flip Variable Nothing) "xyzwsabctuvXY"

instance NFData Variable where
  rnf (Variable x y) = rnf x `seq` rnf y `seq` ()

instance NFData (Polynomial Rational) where
  rnf (Polynomial dic) = rnf dic

i1, i2, i3, i4, i5 :: [Polynomial Rational]
i1 = [x - (t + u), y - (t^2 + 2*t*u), z - (t^3 + 3*t^2*u)]
i2 = [t^2 + x^2+y^2+z^2, t^2 + 2*x^2 - x*y -z^2, t+ y^3-z^3]
i3 = [ 2 * s - a * y', b^2 - (x'^2 + y'^2), c^2 - ( (a-x') ^ 2 + y'^2)
     ]
i4 = [ x - (3*u + 3*u*v^2 - u^3), y - (3*v + 3*u^2*v -  v^3), z - (3*u^2 - 3*v^2)]

mkTestCase :: Sing n => String -> [Polynomial Rational] -> SNat n -> Benchmark
mkTestCase name ideal nth =
  bgroup name [ bench "lex" $ nf (calcGroebnerBasisWith Lex) ideal
              , bench "product" $ nf (calcGroebnerBasisWith (eliminationOrder nth)) ideal
              , bench "weight" $ nf (calcGroebnerBasisWith (weightedEliminationOrder nth)) ideal
              ]

main :: IO ()
main = do
  ideal1 <- return $! (i1 `using` rdeepseq)
  ideal2 <- return $! (i2 `using` rdeepseq)
  ideal3 <- return $! (i3 `using` rdeepseq)
  ideal4 <- return $! (i4 `using` rdeepseq)
  ideal5 <- return $! (i5 `using` rdeepseq)
  [var_x, var_y, var_t] <- return $! (map (flip Variable Nothing) "xyt" `using` rdeepseq)
  defaultMain $  [ mkTestCase "heron" ideal3 sTwo
                 , mkTestCase "implicit01" ideal5 sOne
                 , mkTestCase "implicit03" ideal1 sTwo
                 , mkTestCase "implicit04" ideal4 sTwo
                 ]

