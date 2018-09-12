{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts              #-}
{-# LANGUAGE FlexibleInstances, GADTs, MultiParamTypeClasses           #-}
{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction, PolyKinds   #-}
{-# LANGUAGE Rank2Types, RankNTypes, ScopedTypeVariables, TypeFamilies #-}
{-# LANGUAGE TypeOperators, UndecidableInstances                       #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module Cases (FPol, cyclic, katsura, katsura8, katsura9, i3, quotPair) where
import           Algebra.Normed
import           Algebra.Prelude.Core
import           Algebra.Ring.Polynomial.Labeled
import           Data.List                       (tails)
import qualified Data.Vector                     as V

type FPol p = (IsOrderedPolynomial p, Num (Coefficient p),
               Normed (Coefficient p), Field (Coefficient p))


i3 :: Ideal (Polynomial (Fraction Integer) 4)
i3 = toIdeal [ x^31 - x^6 - x- y, x^8 - z, x^10 -t]
  where
    [t,x,y,z] = vars

cyclic :: forall n. Sing n
       -> Ideal (OrderedPolynomial Rational Grevlex n)
cyclic n = withKnownNat n $
  let vs = vars :: [OrderedPolynomial Rational Grevlex n]
      cycs = map (`mkCyclic` vs) [1..length vs - 1]
  in toIdeal (product vs - 1 : cycs)

mkCyclic :: Ring r => Int -> [r] -> r
mkCyclic n cycs = sum $ map product $ take (length cycs) $ map (take n) $ tails $ cycle cycs

katsura8 :: Ideal (Polynomial Rational 9)
katsura8 = katsura sing

katsura9 :: Ideal (Polynomial Rational 10)
katsura9 = katsura sing

katsura :: SNat n -> Ideal (Polynomial Rational (n + 1))
katsura sn = withKnownNat sn $
  let vs = V.fromList vars
      n  = fromIntegral (toNatural sn)
      u k | k >= n + 1 = zero
          | k < 0 = u (- k)
          | otherwise = vs V.! k
      f = sum [ u l | l <- [- n, - (n - 1) .. n ] ] - 1
  in toIdeal $ nub $ f : [ sum [ u k * u (l - k) | k <- [- n, - (n-1) .. n] ] - u l
                         | l <- [- (n - 1), -(n - 2) .. n - 1] ]

type QXYZ = LabPolynomial' Rational Grevlex '["x", "y", "z"]
quotPair :: (Ideal QXYZ, Ideal QXYZ)
quotPair = ( toIdeal [ (#x + #y)^2 * (#x - #y) * (#x + #z^2)]
           , toIdeal [ (#x + #z^2)^3 * (#x - #y) * (#z + #y)]
           )
