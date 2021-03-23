{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Algebra.TestUtils
  ( liftSNat,
    checkForTypeNat,
    module Algebra.Ring.Polynomial.Test,
    module Algebra.Ring.Polynomial.Monomial.Test,
    module Algebra.Field.Fraction.Test,
    module Algebra.Field.Finite.Test,
  )
where

import Algebra.Field.Finite.Test
import Algebra.Field.Fraction.Test
import Algebra.Field.Prime.Test ()
import Algebra.Internal
import Algebra.Ring.Ideal.Test ()
import Algebra.Ring.Polynomial.Monomial.Test
import Algebra.Ring.Polynomial.Test
import Numeric.Natural (Natural)
import Test.QuickCheck (Property, forAll)
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Instances ()
import Prelude (($))

liftSNat :: (forall n. KnownNat (n :: Nat) => SNat n -> Property) -> Natural -> Property
liftSNat f i =
  case toSomeSNat i of
    SomeSNat sn -> withKnownNat sn $ f sn

checkForTypeNat :: [Natural] -> (forall n. KnownNat (n :: Nat) => SNat n -> Property) -> Property
checkForTypeNat as test = forAll (QC.elements as) $ liftSNat test
