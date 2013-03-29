{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings, PolyKinds #-}
{-# LANGUAGE TemplateHaskell, UndecidableInstances               #-}
import           Algebra.Algorithms.Groebner.Monomorphic
import           Algebra.Internal
import           Algebra.Ring.Polynomial                 (eliminationOrder,
                                                          weightedEliminationOrder)
import           Algebra.Ring.Polynomial.Monomorphic
import           Control.DeepSeq
import           Control.Parallel.Strategies
import           Criterion.Main
import           Criterion.Types
import           Numeric.Algebra                         (LeftModule (..))
import qualified Numeric.Algebra                         as NA

x, y, z, w, s, a, b, c, t, u, v :: Polynomial Rational
[x, y, z, w, s, a, b, c, t, u, v] = map (injectVar . flip Variable Nothing) "xyzwSabctuv"

instance NFData Variable where
  rnf (Variable x y) = rnf x `seq` rnf y `seq` ()

instance NFData (Polynomial Rational) where
  rnf (Polynomial dic) = rnf dic

i1, i2, i3, i4, i5 :: [Polynomial Rational]
i1 = [x - (t + u), y - (t^2 + 2*t*u), z - (t^3 + 3*t^2*u)]
i2 = [t^2 + x^2+y^2+z^2, t^2 + 2*x^2 - x*y -z^2, t+ y^3-z^3]
i3 = [ 2 * s - a * y, b^2 - (x^2 + y^2), c^2 - ( (a-x) ^ 2 + y^2)
         ]
i4 = [ x - (3*u + 3*u*v^2 - u^3), y - (3*v + 3*u^2*v -  v^3), z - (3*u^2 - 3*v^2)]
i5 = [t^2+x^2+y^2+z^2, t^2+2*x^2-x*y-z^2, t+y^3-z^3]


main :: IO ()
main = do
  ideal1 <- return $! (i1 `using` rdeepseq)
  ideal2 <- return $! (i2 `using` rdeepseq)
  ideal3 <- return $! (i3 `using` rdeepseq)
  ideal4 <- return $! (i4 `using` rdeepseq)
  ideal5 <- return $! (i5 `using` rdeepseq)
  [var_x, var_y, var_t] <- return $! (map (flip Variable Nothing) "xyt" `using` rdeepseq)
  defaultMain $ [ bgroup "heron"
                            [ bench "lex" $ nf (eliminateWith Lex [var_x, var_y]) ideal3
                            , bench "product" $ nf (eliminateWith (eliminationOrder sTwo) [var_x, var_y]) ideal3
                            , bench "weight" $ nf (eliminateWith (weightedEliminationOrder sTwo) [var_x, var_y]) ideal3
                            ]
                , bgroup "implicit01"
                            [ bench "lex" $ nf (eliminateWith Lex [var_t]) ideal5
                            , bench "product" $ nf (eliminateWith (eliminationOrder sOne) [var_t]) ideal5
                            , bench "weight" $ nf (eliminateWith (weightedEliminationOrder sOne) [var_t]) ideal5
                            ]
                , bgroup "implicit02"
                            [ bench "lex" $ nf (eliminateWith Lex [var_t]) ideal2
                            , bench "product" $ nf (eliminateWith (eliminationOrder sOne) [var_t]) ideal2
                            , bench "weight" $ nf (eliminateWith (weightedEliminationOrder sOne) [var_t]) ideal2
                            ]
                , bgroup "implicit03"
                            [ bench "lex" $ nf (eliminateWith Lex [var_t]) ideal1
                            , bench "product" $ nf (eliminateWith (eliminationOrder sOne) [var_t]) ideal1
                            , bench "weight" $ nf (eliminateWith (weightedEliminationOrder sOne) [var_t]) ideal1
                            ]
                , bgroup "implicit04"
                            [ bench "lex" $ nf (eliminateWith Lex [var_t]) ideal4
                            , bench "product" $ nf (eliminateWith (eliminationOrder sOne) [var_t]) ideal4
                            , bench "weight" $ nf (eliminateWith (weightedEliminationOrder sOne) [var_t]) ideal4
                            ]
                ]

