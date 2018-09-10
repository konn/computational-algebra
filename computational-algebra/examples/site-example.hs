{-# LANGUAGE ConstraintKinds, DataKinds, GADTs, KindSignatures     #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude              #-}
{-# LANGUAGE NoMonomorphismRestriction, QuasiQuotes, TypeOperators #-}
module Main where
import Algebra.Algorithms.Groebner
import Algebra.Field.Finite
import Algebra.Prelude
import Data.Type.Ordinal.Builtin

-- | 0-th variable of polynomial ring with at least one variable.
-- Variables are 0-origin.
x :: (KnownNat n, CoeffRing r, IsMonomialOrder n order, (0 < n) ~ 'True)
  => OrderedPolynomial r order n
x = var [od|0|]

-- | 1-st variable of polynomial ring with at least two variable.
y :: (KnownNat n, CoeffRing r, IsMonomialOrder n order, (1 < n) ~ 'True)
  => OrderedPolynomial r order n
y = var [od|1|]

-- | The last variable of
z :: Polynomial Rational 3
z = var [od|2|]

-- | f in QQ[x,y,z]
f :: OrderedPolynomial Rational Grevlex 3
f = 1%2*x*y^2 + y^2

-- | map f to the F_5[x,y,z], where F_5 = ZZ/5ZZ
f' :: Polynomial (F 5) 3
f' = mapCoeff (\r -> fromInteger (numerator r) / fromInteger (denominator r) ) f

-- | ideal of QQ[x,y,a,b,c,s]
heron :: Ideal (OrderedPolynomial Rational Lex 6)
heron = toIdeal [ 2 * s - a * y
                , b^2 - (x^2 + y^2)
                , c^2 - ((a - x)^2 + y^2)
                ]
  where
    -- | Get the last four variables of QQ[x,y,a,b,c,s]
    [_, _, a, b, c, s] = vars

main :: IO ()
main = act

act = do
  print f
  print f'
  print $ x * f'^2
  print $ calcGroebnerBasis heron
  -- print $ f' * 5 + f -- ^ Type error!
