{-# LANGUAGE ConstraintKinds, DataKinds, ExplicitNamespaces   #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs       #-}
{-# LANGUAGE LiberalTypeSynonyms, MultiParamTypeClasses       #-}
{-# LANGUAGE NoMonomorphismRestriction, PolyKinds, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances       #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-type-defaults #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
module Algebra.Ring.Polynomial
    ( module Algebra.Ring.Polynomial.Monomial,
      module Algebra.Ring.Polynomial.Class,
      Polynomial,
      transformMonomial,
      castPolynomial, changeOrder, changeOrderProxy,
      scastPolynomial, OrderedPolynomial(..),
      allVars, substVar, homogenize, unhomogenize,
      normalize, varX, getTerms, shiftR, orderedBy,
      mapCoeff, reversal, padeApprox,
      eval, evalUnivariate,
      substUnivariate, minpolRecurrent,
      IsOrder(..), PadPolyL(..), padLeftPoly
    )  where
import Algebra.Algorithms.Groebner
import Algebra.Internal
import Algebra.Ring.Polynomial.Class
import Algebra.Ring.Polynomial.Internal
import Algebra.Ring.Polynomial.Monomial

import AlgebraicPrelude

instance {-# OVERLAPPABLE #-}
         (KnownNat n, Eq r, DecidableUnits r, DecidableZero r, Field r,
          IsMonomialOrder n ord, ZeroProductSemiring r)
      => UFD (OrderedPolynomial r ord n)

instance {-# OVERLAPPABLE #-}
         (KnownNat n, Eq r, DecidableUnits r, DecidableZero r, Field r,
          IsMonomialOrder n ord, ZeroProductSemiring r)
      => GCDDomain (OrderedPolynomial r ord n) where
  gcd = gcdPolynomial
  lcm = lcmPolynomial
