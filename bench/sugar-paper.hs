{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs      #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction           #-}
{-# LANGUAGE OverloadedStrings, PolyKinds, QuasiQuotes, TemplateHaskell #-}
{-# LANGUAGE TypeFamilies, UndecidableInstances                         #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Main where
import           Algebra.Algorithms.Groebner
import           Algebra.Ring.Ideal
import           Algebra.Ring.Polynomial
import           Algebra.Ring.Polynomial.Monomorphic (promoteWithVars, varChar)
import qualified Algebra.Ring.Polynomial.Monomorphic as MP
import           Algebra.Ring.Polynomial.Parser
import           Control.DeepSeq
import           Control.Parallel.Strategies
import           Criterion.Main
import           Data.Type.Natural
import           Data.Vector.Sized                   (Vector (..))
import qualified Data.Vector.Sized                   as V
import           Numeric.Field.Fraction              (Fraction)

parse :: String -> MP.Polynomial (Fraction Integer)
parse x = case parsePolyn x of
            Right y -> y
            Left er -> error $ show er

i1 :: [OrderedPolynomial (Fraction Integer) Grevlex Seven]
i1 = map (promoteWithVars (V.map varChar $ 't' :- 'u' :- 'v' :- 'w' :- 'x' :- 'y' :- 'z' :- Nil) . parse)
     ["yw - 1/2 zw + tw"
     ,"-2/7 uw^2 + 10/7 vw^2 - 20/7 w^3 + tu - 5tv + 10tw"
     ,"2/7 yw^2 - 2/7 zw^2 + 6/7 tw^2 - yt + zt - 3t^2"
     ,"-2v^3 + 4uvw + 5v^2w - 6uw^2 - 7vw^2 + 15w^3 + 42yv"
     ,"-14zv - 63yw + 21zw - 42tw + 147x"
     ,"-9/7uw^3 + 45/7vw^3 - 135/7w^4 + 2zv^2 - 2tv^2 - 4zuw+10tuw - 2zvw - 28tvw + 4zw^2 + 86tw^2 - 42yz+14z^2 + 42yt - 14zt - 21xu + 105xv - 315xw"
     ,"6/7yw^3 - 9/7zw^3 + 36/7tw^3 - 2zv^2 - 4ytw + 6ztw - 24t^2w\
     \+ 4xuw + 2xvw - 4xw^2 + 56xy - 35xz + 84xt"
     ,"2uvw - 6v^2w - uw^2 + 13vw^2 - 5w^3 + 14yw - 28tw"
     ,"u^2w - 3uvw + 5uw^2 + 14yw - 28tw"
     ,"-2zuw - 2tuw + 4yvw + 6zvw - 2tvw - 16yw^2 - 10 zw^2 + 22tw^2 + 42xw"
     ,"28/3yuw + 8/3zuw - 20/3tuw - 88/3yvw - 8zvw\
     \+68/3tvw + 52yw^2 + 40/3zw^2 - 44tw^2 - 84xw"
     ,"-4yzw + 10ytw + 8ztw - 20t^2w + 12xuw - 30xvw + 15xw^2"
     ,"-1 y^2w + 1/2 yzw + ytw - ztw + 2 t^2 w - 3xuw + 6xvw - 3xw^2"
     , "8xyw - 4xzw + 8xtw"
     ]

i2 :: [OrderedPolynomial (Fraction Integer) Grevlex Five]
i2 =  [35 * y^4 - 30*x*y^2 - 210*y^2*z + 3*x^2 + 30*x*z - 105*z^2 +140*y*t - 21*u
      ,5*x*y^3 - 140*y^3*z - 3*x^2*y + 45*x*y*z - 420*y*z^2 + 210*y^2*t -25*x*t + 70*z*t + 126*y*u
      ]
     where [t,u,x,y,z] = genVars sFive

i3 :: [OrderedPolynomial (Fraction Integer) Grevlex Four]
i3 = [ x^31 - x^6 - x- y, x^8 - z, x^10 -t]
  where
    [t,x,y,z] = genVars sFour

i4 :: [OrderedPolynomial (Fraction Integer) Grevlex Four]
i4 = [ w+x+y+z, w*x+x*y+y*z+z*w, w*x*y + x*y*z + y*z*w + z*w*x, w*x*y*z]
  where
    [x,y,z,w] = genVars sFour

mkTestCases :: (Show a, SingI n) => a -> Ideal (Polynomial (Fraction Integer) n) -> [Benchmark]
mkTestCases num ideal = [ mkTC ("lex0" ++ show num) (mapIdeal (changeOrder Lex) ideal)
                        , mkTC ("grevlex0" ++ show num) (mapIdeal (changeOrder Grevlex) ideal)
                        ]

mkTC :: (IsMonomialOrder ord, SingI n) => String -> Ideal (OrderedPolynomial (Fraction Integer) ord n) -> Benchmark
mkTC name ideal =
    bgroup name [ bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy) ideal
                , bench "syz+sugar" $ nf (syzygyBuchbergerWithStrategy (SugarStrategy NormalStrategy)) ideal
                ]

main :: IO ()
main = do
  ideal1 <- return $! (toIdeal i1 `using` rdeepseq)
  ideal2 <- return $! (toIdeal i2 `using` rdeepseq)
  ideal3 <- return $! (toIdeal i3 `using` rdeepseq)
  ideal4 <- return $! (toIdeal i4 `using` rdeepseq)
  defaultMain $
       mkTestCases 1 ideal2
    ++ mkTestCases 2 ideal4
    ++ [mkTC "grevlex03" ideal3]

