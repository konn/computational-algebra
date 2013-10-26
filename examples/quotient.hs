{-# LANGUAGE DataKinds, NoImplicitPrelude, NoMonomorphismRestriction #-}
{-# LANGUAGE OverlappingInstances, PolyKinds                         #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Main (module Algebra.Algorithms.Groebner, module Algebra.Ring.Polynomial
            , module Data.Ratio, module Main, module Algebra.Internal
            ) where
import           Algebra.Algorithms.Groebner
import           Algebra.Internal
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Algebra.Ring.Polynomial.Quotient
import           Algebra.Scalar
import           Control.Arrow
import           Data.Ratio
import           Data.Reflection
import           Data.Type.Natural
import           Numeric.Additive.Group
import           Numeric.Algebra                  hiding ((/))
import           Prelude                          hiding (Num (..), Real (..),
                                                   (/), (^), (^^))
import qualified Prelude                          as P

default (Integer)

x, y :: Polynomial Rational Two
[x, y] = genVars sTwo

(^^) :: Unital r => r -> Natural -> r
(^^) = pow

(/) :: Integer -> Integer -> Rational
(/) = (%)

infixr 8 ^^

fromRight :: Either t t1 -> t1
fromRight (Right a) = a
fromRight _ = error "fromRight"

main :: IO ()
main = do
  let f = y^^4 * x+ 3*x^^3 - y^^4 -3*x^^2
      g = x^^2*y-2*x^^2
      h = 2*y^^4*x - x^^3 - 2*y^^4 +x^^2
      ideal = toIdeal [f, g, h]
      r = reifyQuotient ideal $ \ii ->
            let Just bs = standardMonomials' ii
                tbl = [ [p*q | q <- bs] | p <- bs]
            in (map quotRepr bs, map (map quotRepr) tbl)
  print r

  let ideal2 = [(-26522079073807/3789408304503) .*. x^^20 - (45981059324371/6069538029208) .*. x^^18 + (87120042561463/371075270539) .*. y^^18 + (79291926719113/9049615744576) .*. (x^^8 * x^^7)
              ,(-51798333070002/2209756160027) .*. y^^21 - (74815570129865/7910242500601) .*. y^^2
              ,(88733941750461/7841330684716) .*. y^^32 - (42199913575574/5828711194795) .*. x^^19 - (71276557990061/9562339937814) .*. y^^14
              ,(-31510669207222/5962081412485) .*. (x^^21 * x^^27) - (36222490648769/8305690306244) .*. (x^^16 * x^^22) - (7233172975215/829632241931) .*. (x^^14 * x^^23) - (3805361578555/167149832969) .*. y^^32 + (69415740054815/6652687446689) .*. y^^29 + (7752028007245/3200657266301) .*. (x^^11 * x^^16) - (19808984350455/4059069629924) .*. x^^19 - (65045682499208/4121663815257) .*. (x^^15 * x^^4) - (15986236131409/1581470273329) .*. x^^7
              ,(6739930354481/646188839176) .*. (x^^27 * x^^12) + (3332373494769/455527457959) .*. (x^^19 * x^^19) + (8664121226147/56503077513) .*. (x^^9 * x^^26) + (7484145267923/6252920124858) .*. y^^25 + (14388640369417/1948009422683) .*. (x^^6 * x^^18) + (31709851046421/2064507686732) .*. (x^^15 * x^^3) - (25628590194323/2964425883134) .*. (x^^4 * x^^14) + (49473826041010/2299762404251) .*. x^^17 - (85383428250299/8861518460758) .*. (x^^5 * x^^3)
              ]
      f2 = (80554074773357/4347721547917) .*. (x^^30 * y^^14) - (42677827243839/6070945287334) .*. (x^^28 * y^^14) - (644551542381/356632156135) .*. (x^^9 * y^^32) + (82812585264442/1694267049817) .*. (x^^32 * y^^8) + (13143129720339/1541218520317) .*. y^^28 + (35169339928528/3273364681879) .*. (x^^14 * y^^12) + (6016316529539/857674706980) .*. y^^13 - (31839563822059/2132443079266) .*. x^^11 - injectCoeff (13611257149310/7379272303073)
      g2 = (71897304622813/8341793645760) .*. (x^^30 * y^^11) - (16418454876309/1094197015679) .*. (x^^20 * y^^9) - (369944330392/960955134031) .*. (x^^10 * y^^12) + (32278788235340/40762635223) .*. y
  print $ calcGroebnerBasis (toIdeal ideal2) -- $ reflect >>> vBasis &&& multTable
