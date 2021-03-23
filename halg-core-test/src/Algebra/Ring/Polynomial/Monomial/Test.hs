{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin Data.Singletons.TypeNats.Presburger #-}

module Algebra.Ring.Polynomial.Monomial.Test
  ( arbitraryMonomialOfSum,
    arbitraryMonomial,
  )
where

import Algebra.Internal
import Algebra.Ring.Polynomial.Monomial
  ( Monomial,
    OrderedMonomial (..),
  )
import qualified Data.Sized as SV
import Data.Type.Equality (gcastWith)
import Data.Type.Natural.Lemma.Arithmetic (succAndPlusOneL)
import Test.QuickCheck
  ( Arbitrary,
    Gen,
    arbitrary,
    arbitrarySizedBoundedIntegral,
    vectorOf,
  )
import qualified Test.QuickCheck as QC
import Test.SmallCheck.Series
  ( Serial,
    cons0,
    newtypeCons,
    series,
  )
import qualified Test.SmallCheck.Series as SC
import Prelude

instance (KnownNat n, Monad m) => Serial m (Monomial n) where
  series =
    case zeroOrSucc (sNat @n) of
      IsZero -> cons0 SV.empty
      IsSucc n ->
        gcastWith (succAndPlusOneL n) $
          withKnownNat n $ SV.cons <$> (SC.getNonNegative <$> series) <*> series

instance (Monad m, Serial m (Monomial n)) => Serial m (OrderedMonomial ord n) where
  series = newtypeCons OrderedMonomial

arbitraryMonomialOfSum :: SNat n -> Int -> Gen (Monomial n)
arbitraryMonomialOfSum n k = withKnownNat n $
  case zeroOrSucc n of
    IsZero
      | k == 0 -> QC.elements [SV.empty]
      | otherwise -> error "Impossible"
    IsSucc m -> withKnownNat m $ do
      l <- QC.elements [0 .. abs k]
      (l :<) <$> arbitraryMonomialOfSum m (abs k - l)

-- * Instances for QuickCheck.

instance KnownNat n => Arbitrary (Monomial n) where
  arbitrary = arbitraryMonomial

arbitraryMonomial :: forall n. KnownNat n => Gen (Monomial n)
arbitraryMonomial =
  SV.unsafeFromList len . map abs
    <$> vectorOf (sNatToInt len) arbitrarySizedBoundedIntegral
  where
    len = sNat :: SNat n

instance (KnownNat n) => Arbitrary (OrderedMonomial ord n) where
  arbitrary = OrderedMonomial <$> arbitrary
