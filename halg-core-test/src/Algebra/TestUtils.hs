{-# LANGUAGE CPP, DataKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses, RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables, TypeOperators, UndecidableInstances   #-}
module Algebra.TestUtils
       ( liftSNat, checkForArity
       , module Algebra.Ring.Polynomial.Test
       , module Algebra.Ring.Polynomial.Monomial.Test
       , module Algebra.Field.Fraction.Test
       , module Algebra.Field.Finite.Test
       )
       where
import           Algebra.Field.Finite.Test
import           Algebra.Field.Fraction.Test
import           Algebra.Field.Prime.Test              ()
import           Algebra.Internal
import           Algebra.Ring.Ideal.Test               ()
import           Algebra.Ring.Polynomial.Monomial.Test
import           Algebra.Ring.Polynomial.Test
import qualified Data.Type.Natural.Builtin             as TN
import           Numeric.Natural                       (Natural)
import           Prelude                               (($))
import           Test.QuickCheck                       (Property, forAll)
import qualified Test.QuickCheck                       as QC
import           Test.QuickCheck.Instances             ()

liftSNat :: (forall n. KnownNat (n :: Nat) => Sing n -> Property) -> Natural -> Property
liftSNat f i =
  case TN.fromNatural i of
    SomeSing sn -> withKnownNat sn $ f sn

checkForArity :: [Natural] -> (forall n. KnownNat (n :: Nat) => Sing n -> Property) -> Property
checkForArity as test = forAll (QC.elements as) $ liftSNat test



