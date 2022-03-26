{-# LANGUAGE PolyKinds #-}

module Algebra.Ring.Euclidean.Quotient.Test () where

import Algebra.Ring.Euclidean.Quotient
import AlgebraicPrelude (Euclidean)
import Data.Reflection
import Test.QuickCheck

instance
  (Euclidean a, Arbitrary a, Reifies s a) =>
  Arbitrary (Quotient s a)
  where
  arbitrary = quotient <$> arbitrary
