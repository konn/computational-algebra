{-# LANGUAGE DataKinds, DerivingStrategies, GADTs                          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, KindSignatures, MagicHash         #-}
{-# LANGUAGE NoImplicitPrelude, PolyKinds, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell, TypeApplications                             #-}
{-# OPTIONS_GHC -Wno-orphans -O2 #-}
{-# OPTIONS_GHC -dsuppress-idinfo -dsuppress-coercions
      -dsuppress-type-applications
      -dsuppress-module-prefixes -dsuppress-type-signatures
      -dsuppress-uniques
  #-}
module Algebra.Field.PrimeSpec where
import           Algebra.Field.Finite.Test ()
import           Algebra.Field.Prime
import           Algebra.Field.Prime.Test  ()
import           AlgebraicPrelude
import           Data.Proxy                (Proxy (..))
import           GHC.TypeLits              (Nat)
import           Language.Haskell.TH
import           Math.NumberTheory.Primes
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck           hiding (elements)
import qualified Test.QuickCheck           as QC

bigEnoughPrime :: Prime Integer
bigEnoughPrime = precPrime $ floor @Double
  $ sqrt $ fromIntegral $ maxBound @Int

type LargeP = $(litT $ numTyLit $ unPrime
  $ nextPrime $ floor @Double
  $ sqrt $ fromIntegral $ maxBound @Int)

spec :: Spec
spec = describe "F p" $ do
  prop "is a field (for small primes)" $ \(SmallPrime p) ->
        tabulate "p" [show p] $
        reifyPrimeField p $ property . isField
  prop "is a field (for small, but medium primes)" $ \(MediumPrime p) ->
        tabulate "p" [show p] $
        reifyPrimeField p $ property . isField
  prop "is a field (for big primes)" $ \(BigPrime p) ->
    tabulate "p" [show p] $
    reifyPrimeField p $ property . isField

newtype SmallPrime = SmallPrime { runSmallPrime :: Integer }
  deriving newtype (Show)

instance Arbitrary SmallPrime where
  arbitrary = SmallPrime . unPrime
    <$> QC.elements (take 10 primes)

newtype MediumPrime = MediumPrime { runMediumPrime :: Integer }
  deriving newtype (Show)

instance Arbitrary MediumPrime where
  arbitrary = MediumPrime . unPrime
    <$> QC.elements
        (take 10 [nextPrime
          $ floor @Double $ sqrt
          $ fromIntegral $ unPrime bigEnoughPrime
          .. ])

newtype BigPrime = BigPrime { runBigPrime :: Integer }
  deriving newtype (Show)

instance Arbitrary BigPrime where
  arbitrary = BigPrime . unPrime
    <$> QC.elements (take 10 [bigEnoughPrime ..])

isField :: IsPrimeChar (p :: Nat) => Proxy (F p) -> F p -> F p -> F p -> Property
isField _ e f g =
  1 * e === e .&&. e * 1 === e .&&. e + 0 === e
  .&&. (0 + e === e) .&&. (e - e === 0)
  .&&. (e /= 0 ==> e * recip e === 1 .&&. recip e * e === 1)
  .&&. e + f === f + e .&&. e * f === f * e
  .&&. e * (f * g) === (e * f) * g
  .&&. e + (f + g) === (e + f) + g
  .&&. e * (f + g) === e*f + e*g
