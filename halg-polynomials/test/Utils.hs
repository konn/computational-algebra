{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs                   #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude                     #-}
{-# LANGUAGE NoMonomorphismRestriction, ScopedTypeVariables, TypeFamilies #-}
{-# LANGUAGE UndecidableInstances                                         #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Utils (module Utils, module Algebra.TestUtils) where
import Algebra.Field.Prime
import Algebra.Prelude.Core
import Algebra.Ring.Polynomial.Univariate
import Algebra.TestUtils
import AlgebraicPrelude                   ()
import Test.QuickCheck

instance (Arbitrary k, KnownNat n, CoeffRing k, IsMonomialOrder n o)
      => Arbitrary (OrderedPolynomial k o n) where
  arbitrary = arbitraryPolynomial

instance (Arbitrary k, CoeffRing k)
      => Arbitrary (Unipol k) where
  arbitrary = arbitraryPolynomial

idealOfArity :: SNat n -> Gen (Ideal (Polynomial (Fraction Integer) n))
idealOfArity sn = withKnownNat sn arbitrary

ratPolynomialOfArity :: KnownNat n => SNat n -> Gen (Polynomial (Fraction Integer) n)
ratPolynomialOfArity = polynomialOfArity

polynomialOfArity :: (KnownNat n, DecidableZero k, Field k, Eq k, Arbitrary k)
                  => SNat n -> Gen (Polynomial k n)
polynomialOfArity sn = withKnownNat sn (runWrapPolynomial <$> arbitrary)
