{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Utils (module Utils, module Algebra.TestUtils) where

import Algebra.Prelude.Core
import Algebra.Ring.Polynomial.Univariate
import Algebra.Ring.Polynomial.List
import Algebra.TestUtils
import AlgebraicPrelude ()
import Test.QuickCheck

instance
  (Arbitrary k, KnownNat n, CoeffRing k, IsMonomialOrder n o) =>
  Arbitrary (OrderedPolynomial k o n)
  where
  arbitrary = arbitraryPolynomial

instance
  (Arbitrary k, KnownNat n, CoeffRing k, IsMonomialOrder n o) =>
  Arbitrary (ListPoly k o n)
  where
  arbitrary = arbitraryPolynomial

instance
  (Arbitrary k, CoeffRing k) =>
  Arbitrary (Unipol k)
  where
  arbitrary = arbitraryPolynomial

idealOfArity :: SNat n -> Gen (Ideal (Polynomial (Fraction Integer) n))
idealOfArity sn = withKnownNat sn arbitrary

ratPolynomialOfArity :: KnownNat n => SNat n -> Gen (Polynomial (Fraction Integer) n)
ratPolynomialOfArity = polynomialOfArity

polynomialOfArity ::
  (KnownNat n, DecidableZero k, Field k, Eq k, Arbitrary k) =>
  SNat n ->
  Gen (Polynomial k n)
polynomialOfArity sn = withKnownNat sn (runWrapPolynomial <$> arbitrary)

setSize :: Testable prop => Int -> prop -> Property
setSize = mapSize . const
