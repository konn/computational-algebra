{-# LANGUAGE FlexibleContexts, NoImplicitPrelude, NoMonomorphismRestriction #-}
module Algebra.Prelude
       ((%),Scalar(..),(.*.), od,Ordinal, enumOrdinal,
        logBase2,ceilingLogBase2,
        module AlgebraicPrelude,
        module Algebra.Ring.Polynomial,
        module Algebra.Ring.Ideal,
        module Algebra.Normed,
        module Algebra.Internal) where

import Algebra.Internal
import Algebra.Normed
import Algebra.Ring.Ideal
import Algebra.Ring.Polynomial
import Algebra.Scalar

import AlgebraicPrelude          hiding (lex, (%))
import Data.Bits                 (Bits (..), FiniteBits (..))
import Data.Type.Ordinal.Builtin (Ordinal, enumOrdinal, od)

(%) :: (IsPolynomial poly, Division (Coefficient poly))
    => Coefficient poly -> Coefficient poly -> poly
n % m = injectCoeff (n / m)
infixl 7 %

type Rational = Fraction Integer

logBase2 :: Int -> Int
logBase2 x = finiteBitSize x - 1 - countLeadingZeros x
{-# INLINE logBase2 #-}

ceilingLogBase2 :: Int -> Int
ceilingLogBase2 n =
  if popCount n == 1
  then logBase2 n
  else logBase2 n + 1
