{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings, PolyKinds #-}
{-# LANGUAGE TemplateHaskell, UndecidableInstances               #-}
import           Algebra.Algorithms.Groebner.Monomorphic
import           Algebra.Ring.Polynomial.Monomorphic
import           Control.DeepSeq
import           Criterion.Types
import           Numeric.Algebra                         (LeftModule (..))
import qualified Numeric.Algebra                         as NA
import           Progression.Main

x, y, z, w, s, a, b, c :: Polynomial Rational
[x, y, z, w, s, a, b, c] = map (injectVar . flip Variable Nothing) "xyzwSabc"

instance NFData Variable where
  rnf (Variable x y) = rnf x `seq` rnf y `seq` ()

instance NFData (Polynomial Rational) where
  rnf (Polynomial dic) = rnf dic

ideal1, ideal2, ideal3, ideal4 :: [Polynomial Rational]
ideal1 = [x^2 + y^2 + z^2 - 1, x^2 + y^2 + z^2 - 2*x, 2*x -3*y - z]
ideal2 = [x^2 * y - 2*x*y - 4*z - 1, z-y^2, x^3 - 4*z*y]
ideal3 = [ 2 * s - a * y, b^2 - (x^2 + y^2), c^2 - ( (a-x) ^ 2 + y^2)
         ]
ideal4 = [ z^5 + y^4 + x^3 - 1, z^3 + y^3 + x^2 - 1]

main :: IO ()
main =
    defaultMain $ bgroup "groebner"
                    [ bench "simple" $ nf (simpleBuchbergerWith Lex) ideal3
                    , bench "relprime" $ nf (primeTestBuchbergerWith Lex) ideal3
                    , bench "syzygy" $ nf (syzygyBuchbergerWith Lex) ideal3
                    ]
