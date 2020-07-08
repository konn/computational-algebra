{-# LANGUAGE DataKinds, DerivingStrategies, GADTs                          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, KindSignatures, NoImplicitPrelude #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables, TemplateHaskell   #-}
{-# LANGUAGE TypeApplications                                              #-}
{-# OPTIONS_GHC -Wno-orphans #-}
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
import qualified AlgebraicPrelude          as NA
import           Data.Proxy                (Proxy (..))
import           Data.Singletons.Prelude
import           GHC.TypeLits              (Nat)
import           Math.NumberTheory.Primes
import qualified Prelude                   as P
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.Inspection           hiding (Property, property, (===))
import qualified Test.Inspection           as IT
import           Test.QuickCheck           hiding (elements)
import qualified Test.QuickCheck           as QC
import           Unsafe.Coerce             (unsafeCoerce)

bigEnoughPrime :: Prime Integer
bigEnoughPrime = precPrime $ floor @Double
  $ sqrt $ fromIntegral $ maxBound @Int

n102F59 :: F 59
n102F59 = 102

n102F59Manual :: F 59
n102F59Manual = unsafeCoerce (102 `mod` 59 :: Int)

f59AddPrelude :: F 59 -> F 59 -> F 59
f59AddPrelude = (P.+)

f59AddAlgebra :: F 59 -> F 59 -> F 59
f59AddAlgebra = (NA.+)

f59AddManual :: F 59 -> F 59 -> F 59
f59AddManual = unsafeCoerce $ \(l :: Int) (r :: Int) ->
  (l + r) `mod` 59

checkInspection
  :: IT.Result -> Expectation
checkInspection IT.Success{} = pure ()
checkInspection (IT.Failure msg) =
  fail msg

spec :: Spec
spec = do
  describe "F p" $ do
    prop "is a field (for small primes)" $ \(SmallPrime p) ->
          tabulate "p" [show p] $
          reifyPrimeField p $ property . isField
    prop "is a field (for big primes)" $ \(BigPrime p) ->
      tabulate "p" [show p] $
      reifyPrimeField p $ property . isField
    describe "optimisation for small primes (F 59)" $ do
      it "literal doesn't contain type-natural comparison"
        $ checkInspection $(inspectTest $ 'n102F59 `doesNotUse` 'SLT)
      describe "(Prelude.+)" $ do
        it "doesn't contain type-natural comparison"
          $ checkInspection $(inspectTest $ 'f59AddPrelude `doesNotUse` 'SLT)
        it "has the same core as \a b -> (a + b) `mod` 59"
          $ checkInspection $(inspectTest $ 'f59AddPrelude IT.=== 'f59AddManual)
      describe "(NA.+)" $ do
        it "doesn't contain type-natural comparison"
          $ checkInspection $(inspectTest $ 'f59AddAlgebra `doesNotUse` 'SLT)
        it "has the same core as \a b -> (a + b) `mod` 59"
          $ checkInspection $(inspectTest $ 'f59AddAlgebra IT.=== 'f59AddManual)

newtype SmallPrime = SmallPrime { runSmallPrime :: Integer }
  deriving newtype (Show)

instance Arbitrary SmallPrime where
  arbitrary = SmallPrime . unPrime
    <$> QC.elements (take 1000 primes)

newtype BigPrime = BigPrime { runBigPrime :: Integer }
  deriving newtype (Show)

instance Arbitrary BigPrime where
  arbitrary = BigPrime . unPrime
    <$> QC.elements (take 1000 [bigEnoughPrime ..])

isField :: IsPrimeChar (p :: Nat) => Proxy (F p) -> F p -> F p -> F p -> Property
isField _ e f g =
  1 * e === e .&&. e * 1 === e .&&. e + 0 === e
  .&&. (0 + e === e) .&&. (e - e === 0)
  .&&. (e /= 0 ==> e * recip e === 1 .&&. recip e * e === 1)
  .&&. e + f === f + e .&&. e * f === f * e
  .&&. e * (f * g) === (e * f) * g
  .&&. e + (f + g) === (e + f) + g
  .&&. e * (f + g) === e*f + e*g

instance Testable IT.Result where
  property IT.Success{} = property True
  property (IT.Failure msg) = error $ "Inspection failure: " ++ msg
