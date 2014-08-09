{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts                   #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude, OverlappingInstances #-}
{-# LANGUAGE PolyKinds, QuasiQuotes, TemplateHaskell                        #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans -fcontext-stack=1000 #-}
module Main where
import           Algebra.Algorithms.Groebner
import           Algebra.Ring.Ideal
import           Algebra.Ring.Polynomial
import           Algebra.Scalar
import           Control.DeepSeq
import           Control.Monad
import           Control.Parallel.Strategies
import           Criterion
import           Data.Type.Natural           hiding (one)
import           Data.Vector.Sized           (Vector (..))
import qualified Data.Vector.Sized           as V
import           Numeric.Algebra             hiding ((.*), (<), (^))
import qualified Numeric.Algebra             as NA
import           Numeric.Field.Fraction      (Fraction)
import           Prelude                     hiding (Fractional (..),
                                              Integral (..), Num (..),
                                              Real (..), sum, (^^))
import qualified Prelude                     as P
import           Progression.Main

x, y, z :: Polynomial (Fraction Integer) Three
[x, y, z] = genVars sThree

(.*) :: SingI n => (Fraction Integer) -> Polynomial (Fraction Integer) n -> Polynomial (Fraction Integer) n
(.*) = (.*.)

infixl 7 .*

(^^) :: Unital r => r -> NA.Natural -> r
(^^) = NA.pow

eqn01 :: Ideal (Polynomial (Fraction Integer) Three)
eqn01 = toIdeal [x^^2 - 2*x*z + 5, x*y^^2+y*z+1, 3*y^^2 - 8*x*z]

eqn02 :: Ideal (Polynomial (Fraction Integer) Three)
eqn02 =
  toIdeal [x^^2 + 2*y^^2 - y - 2*z
          ,x^^2 - 8*y^^2 + 10*z - 1
          ,x^^2 - 7*y*z
          ]

eqn03 :: Ideal (Polynomial (Fraction Integer) Three)
eqn03 = toIdeal [x^^2 + y^^2 + z^^2 - 2*x
                ,x^^3 - y*z - x
                ,x - y + 2*z
                ]

eqn04 :: Ideal (Polynomial (Fraction Integer) Three)
eqn04 = toIdeal [x*y + z - x*z, x^^2 - z, 2*x^^3 - x^^2 * y * z - 1]

f01 :: Polynomial (Fraction Integer) Three
f01 = -4*x^^4*y^^4 - (1/3).*(x^^3*y^^4*z) + (4/5).*(x^^2*y^^2*z^^4) - (1/5).*(x*y^^2*z^^5)

f02 :: Polynomial (Fraction Integer) Three
f02 = (3/4).*x^^6 - (6/5).*(x^^5*y) + 4*y^^5*z

f03 :: Polynomial (Fraction Integer) Four
f03 = (6/7).* (a^^7*b^^3*c^^4) - (4/3) .* (a^^5*b^^6*c*d^^2) - a^^4*b^^2*c^^4*d^^4
  where
    a, b, c, d :: Polynomial (Fraction Integer) Four
    [a, b, c, d] = genVars sFour

main :: IO ()
main = do
  v10 <- return $!! ((V.replicate [snat|10|] ()) `using` rdeepseq)
  v100 <- return $!! ((V.replicate [snat|100|] ()) `using` rdeepseq)
  v200 <- return $!! ((V.replicate [snat|200|] ()) `using` rdeepseq)
  v300 <- return $!! ((V.replicate [snat|300|] ()) `using` rdeepseq)
  v400 <- return $!! ((V.replicate [snat|400|] ()) `using` rdeepseq)
  case01 <- return $!! (eqn01 `using` rdeepseq)
  case02 <- return $!! (eqn02 `using` rdeepseq)
  case03 <- return $!! (eqn03 `using` rdeepseq)
  case04 <- return $!! (eqn04 `using` rdeepseq)
  poly01 <- return $!! (f01 `using` rdeepseq)
  poly02 <- return $!! (f02 `using` rdeepseq)
  poly03 <- return $!! (f03 `using` rdeepseq)
  defaultMain $ bgroup "coercion" $
    [ bgroup "padVec"
      [ bench "10-100" $ nf (padVec () v10) v100
      , bench "100-10" $ nf (padVec () v100) v10
      , bench "100-400" $ nf (padVec () v100) v400
      , bench "100-200" $ nf (padVec () v100) v200
      , bench "400-300" $ nf (padVec () v400) v300
      ]
    , bgroup "unhomogenize"
      [ bench "01" $ nf unhomogenize poly01
      , bench "02" $ nf unhomogenize poly02
      , bench "03" $ nf unhomogenize poly03
      ]
-- These are too expensive...
    , bgroup "intersection"
      [ bench "two"   $ nf intersection (case01 :- case02 :- Nil)
      , bench "three" $ nf intersection (case03 :- case01 :- case02 :- Nil)
      , bench "four"  $ nf intersection (case04 :- case03 :- case01 :- case02 :- Nil)
      ]
    , bgroup "satByPrinc"
      [ bench "01" $ nf (saturationByPrincipalIdeal case01) f01
      , bench "02" $ nf (saturationByPrincipalIdeal case02) f01
      , bench "03" $ nf (saturationByPrincipalIdeal case03) f01
      , bench "04" $ nf (saturationByPrincipalIdeal case01) f02
      , bench "05" $ nf (saturationByPrincipalIdeal case02) f02
      , bench "06" $ nf (saturationByPrincipalIdeal case03) f02
      ]
    ]
