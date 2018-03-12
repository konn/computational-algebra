{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings, PolyKinds   #-}
{-# LANGUAGE QuasiQuotes, TemplateHaskell, UndecidableInstances    #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
import Algebra.Algorithms.Groebner.Monomorphic
import Algebra.Ring.Polynomial.Monomorphic
import Control.DeepSeq
import Control.Parallel.Strategies
import Gauge.Main
import SingularBench

x, y, z, w, s, a, b, c :: Polynomial (Fraction Integer)
[x, y, z, w, s, a, b, c] = map (injectVar . flip Variable Nothing) "xyzwSabc"

instance NFData Variable where
  rnf (Variable x y) = rnf x `seq` rnf y `seq` ()

instance NFData (Polynomial (Fraction Integer)) where
  rnf (Polynomial dic) = rnf dic

i1, i2, i3, i4 :: [Polynomial (Fraction Integer)]
i1 = [x^2 + y^2 + z^2 - 1, x^2 + y^2 + z^2 - 2*x, 2*x -3*y - z]
i2 = [x^2 * y - 2*x*y - 4*z - 1, z-y^2, x^3 - 4*z*y]
i3 = [ 2 * s - a * y, b^2 - (x^2 + y^2), c^2 - ( (a-x) ^ 2 + y^2)
         ]
i4 = [ z^5 + y^4 + x^3 - 1, z^3 + y^3 + x^2 - 1]

main :: IO ()
main = do
  ideal1 <- return $! (i1 `using` rdeepseq)
  ideal2 <- return $! (i2 `using` rdeepseq)
  ideal3 <- return $! (i3 `using` rdeepseq)
  ideal4 <- return $! (i4 `using` rdeepseq)
  defaultMain $ [bgroup "lex01"
                            [ bench "simple" $ nf (simpleBuchbergerWith Lex) ideal1
                            , bench "relprime" $ nf (primeTestBuchbergerWith Lex) ideal1
                            , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy Lex) ideal1
                            , bench "syz+sugar" $ nf (syzygyBuchbergerWith Lex) ideal1
                            ]
                ,bgroup "grlex01"
                            [ bench "simple" $ nf (simpleBuchbergerWith Grlex) ideal1
                            , bench "relprime" $ nf (primeTestBuchbergerWith Grlex) ideal1
                            , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy Grlex) ideal1
                            , bench "syz+sugar" $ nf (syzygyBuchbergerWith Grlex) ideal1
                            ]
                ,bgroup "grevlex01"
                            [ bench "simple" $ nf (simpleBuchbergerWith Grevlex) ideal1
                            , bench "relprime" $ nf (primeTestBuchbergerWith Grevlex) ideal1
                            , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy Grevlex) ideal1
                            , bench "syz+sugar" $ nf (syzygyBuchbergerWith Grevlex) ideal1
                            ]
                ,bgroup "grlex02"
                            [ bench "simple" $ nf (simpleBuchbergerWith Grlex) ideal2
                            , bench "relprime" $ nf (primeTestBuchbergerWith Grlex) ideal2
                            , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy Grlex) ideal2
                            , bench "syz+sugar" $ nf (syzygyBuchbergerWith Grlex) ideal2
                            ]
                ,bgroup "grevlex02"
                            [ bench "simple" $ nf (simpleBuchbergerWith Grevlex) ideal2
                            , bench "relprime" $ nf (primeTestBuchbergerWith Grevlex) ideal2
                            , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy Grevlex) ideal2
                            , bench "syz+sugar" $ nf (syzygyBuchbergerWith Grevlex) ideal2
                            -- , bench "singular" $ nfIO (singularWith Grevlex ideal2)
                            ]
                ,bgroup "lex03"
                            [ bench "simple" $ nf (simpleBuchbergerWith Lex) ideal3
                            , bench "relprime" $ nf (primeTestBuchbergerWith Lex) ideal3
                            , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy Lex) ideal3
                            , bench "syz+sugar" $ nf (syzygyBuchbergerWith Lex) ideal3
                            -- , bench "singular" $ nfIO (singularWith Lex ideal3)
                            ]
                ,bgroup "grlex03"
                            [ bench "simple" $ nf (simpleBuchbergerWith Grlex) ideal3
                            , bench "relprime" $ nf (primeTestBuchbergerWith Grlex) ideal3
                            , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy Grlex) ideal3
                            , bench "syz+sugar" $ nf (syzygyBuchbergerWith Grlex) ideal3
                            -- , bench "singular" $ nfIO (singularWith Grlex ideal3)
                            ]
                ,bgroup "grevlex03"
                            [ bench "simple" $ nf (simpleBuchbergerWith Grevlex) ideal3
                            , bench "relprime" $ nf (primeTestBuchbergerWith Grevlex) ideal3
                            , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy Grevlex) ideal3
                            , bench "syz+sugar" $ nf (syzygyBuchbergerWith Grevlex) ideal3
                            ]
                ,bgroup "grlex04"
                            [ bench "simple" $ nf (simpleBuchbergerWith Grlex) ideal4
                            , bench "relprime" $ nf (primeTestBuchbergerWith Grlex) ideal4
                            , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy Grlex) ideal4
                            , bench "syz+sugar" $ nf (syzygyBuchbergerWith Grlex) ideal4
                            -- , bench "singular" $ nfIO (singularWith Grlex ideal4)
                            ]
                ,bgroup "grevlex04"
                            [ bench "simple" $ nf (simpleBuchbergerWith Grevlex) ideal4
                            , bench "relprime" $ nf (primeTestBuchbergerWith Grevlex) ideal4
                            , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy Grevlex) ideal4
                            , bench "syz+sugar" $ nf (syzygyBuchbergerWith Grevlex) ideal4
                            -- , bench "singular" $ nfIO (singularWith Grevlex ideal4)
                            ]
                ]
