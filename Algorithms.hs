{-# LANGUAGE ConstraintKinds, FlexibleContexts, MultiParamTypeClasses #-}
module Algorithms where
import Data.List
import Polynomial

x, y, f, f1, f2 :: OrderedPolynomial Rational Lex Two
x = var sTwo
y = var sOne
f = x^2 * y + x * y^2 + y^2
f1 = x * y - 1
f2 = y^2 - 1

divPolynomial :: (IsMonomialOrder order, IsPolynomial r n, Field r)
                  => OrderedPolynomial r order n -> [OrderedPolynomial r order n] -> ([(OrderedPolynomial r order n, OrderedPolynomial r order n)], OrderedPolynomial r order n)
divPolynomial f fs = loop f zero (zip (nub fs) (repeat zero))
  where
    loop p r dic
        | p == zero = (dic, r)
        | otherwise =
            let ltP = toPolynomial $ leadingTerm p
            in case break ((`divs` leadingMonomial p) . leadingMonomial . fst) dic of
                 (_, []) -> loop (p .-. ltP) (r .+. ltP) dic
                 (xs, (g, old):ys) ->
                     let q = toPolynomial $ leadingTerm p `tryDiv` leadingTerm g
                         dic' = xs ++ (g, old .+. q) : ys
                     in loop (p .-. (q .*. g)) r dic'
