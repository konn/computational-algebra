{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module Main
  ( module Algebra.Algorithms.Groebner,
    module Main,
  )
where

import Algebra.Algorithms.Groebner
import Algebra.Prelude
import Algebra.Ring.Polynomial.Univariate (Unipol)
import Data.Maybe (fromJust, fromMaybe, isJust)
import qualified Data.Sized as SV
import Numeric.Decidable.Zero (isZero)

u, v, x, y, z :: Polynomial (Fraction Integer) 5
[u, v, x, y, z] = vars

fromRight :: Either t t1 -> t1
fromRight (Right a) = a
fromRight _ = error "fromRight"

main, act :: IO ()
main = act
act = do
  print (var 0 ^ 51245 :: Unipol Integer)
  let n =
        thEliminationIdeal sTwo $
          toIdeal [x - (3 * u + 3 * u * v ^ 2 - u ^ 3), y - (3 * v + 3 * u ^ 2 * v - v ^ 3), z - (3 * u ^ 2 - 3 * v ^ 2)]
  return ()
  where
    sTwo = sNat :: SNat 2; sThree = sNat :: SNat 3

findDifference ::
  (Eq r, Field r) =>
  [Polynomial r 1] ->
  (r, r, [r], Int)
findDifference = go 0
  where
    go n [f] =
      let ans = fromMaybe zero $ findRoot f
          sol = eval (SV.singleton ans) f
       in (ans, sol, [sol], n)
    go n xs =
      let ds = zipWith (-) xs (tail xs)
          rs = map findRoot ds
          ans = fromJust $ head rs
          sol = eval (SV.singleton ans) $ head xs
       in if isJust (head rs) && all (== head rs) rs
            then (ans, sol, [sol], n)
            else case go (n + 1) (zipWith (-) (tail xs) xs) of
              (a, d, ss, k) -> (a, d, eval (SV.singleton a) (head xs) : ss, k)

findRoot :: (Eq r, Field r, DecidableZero r) => Polynomial r 1 -> Maybe r
findRoot f =
  if
      | totalDegree' f == 1 ->
        Just $ negate $ coeff one f / leadingCoeff f
      | isZero f -> Just zero
      | otherwise -> Nothing

sPolLex :: OrderedPolynomial Rational Lex 2
sPolLex =
  let [x, y] = vars
   in sPolynomial (x ^ 3 * y ^ 2 + x ^ 2 * y ^ 3) (3 * x ^ 4 * y + y ^ 2)

sPolGrevlex :: OrderedPolynomial Rational Grevlex 2
sPolGrevlex =
  let [x, y] = vars
   in sPolynomial (x ^ 3 * y ^ 2 + x ^ 2 * y ^ 3) (3 * x ^ 4 * y + y ^ 2)
