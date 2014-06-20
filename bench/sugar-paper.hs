{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings, PolyKinds   #-}
{-# LANGUAGE QuasiQuotes, TemplateHaskell, UndecidableInstances    #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
import Algebra.Algorithms.Groebner.Monomorphic
import Algebra.Ring.Polynomial.Monomorphic
import Algebra.Ring.Polynomial.Parser
import Control.DeepSeq
import Control.Parallel.Strategies
import Criterion.Main

x, y, z, w, s, a, b, c :: Polynomial (Fraction Integer)
[x, y, z, w, s, a, b, c, t] = map (injectVar . flip Variable Nothing) "xyzwSabct"

instance NFData Variable where
  rnf (Variable x y) = rnf x `seq` rnf y `seq` ()

instance NFData (Polynomial (Fraction Integer)) where
  rnf (Polynomial dic) = rnf dic

parse x = case parsePolyn x of
            Right y -> y
            Left er -> error $ show er

i1, i2, i3, i4 :: [Polynomial (Fraction Integer)]
i1 = map parse ["yw - 1/2 zw + tw"
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
i2 = map parse ["35y^4 - 30xy^2 - 210y^2z + 3x^2 + 30xz - 105z^2 +140yt - 21u"
               ,"5xy^3 - 140y^3z - 3x^2y + 45xyz - 420yz^2 + 210y^2t -25xt + 70zt + 126yu"
               ]
i3 = [ x^31 - x^6 - x- y, x^8 - z, x^10 -t]
i4 = [ w+x+y+z, w*x+x*y+y*z+z*w, w*x*y + x*y*z + y*z*w + z*w*x, w*x*y*z]

mkTestCases :: (Eq r, Show a, r ~ (Fraction Integer)) => a -> [Polynomial r] -> [Benchmark]
mkTestCases num ideal = [ mkTC ("lex0" ++ show num) ideal Lex
                        , mkTC ("grevlex0" ++ show num) ideal Grevlex
                        ]

mkTC :: (r ~ (Fraction Integer), IsMonomialOrder ord) => String -> [Polynomial r] -> ord -> Benchmark
mkTC name ideal ord =
    bgroup name [ bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy ord) ideal
                , bench "syz+sugar" $ nf (syzygyBuchbergerWithStrategy (SugarStrategy NormalStrategy) ord) ideal
                ]

main :: IO ()
main = do
  ideal1 <- return $! (i1 `using` rdeepseq)
  ideal2 <- return $! (i2 `using` rdeepseq)
  ideal3 <- return $! (i3 `using` rdeepseq)
  ideal4 <- return $! (i4 `using` rdeepseq)
  defaultMain $ concat (zipWith mkTestCases [1..] [ideal2, ideal4])
                  ++ [mkTC "grevlex03" ideal3 Grevlex]

