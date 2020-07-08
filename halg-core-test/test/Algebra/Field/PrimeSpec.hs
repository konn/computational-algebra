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
import qualified AlgebraicPrelude          as NA
import           Data.Proxy                (Proxy (..))
import           Data.Singletons.Prelude
import           GHC.Base                  (modInt#)
import           GHC.Integer
import           GHC.TypeLits              (Nat, natVal)
import           Language.Haskell.TH
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

type LargeP = $(litT $ numTyLit $ unPrime
  $ nextPrime $ floor @Double
  $ sqrt $ fromIntegral $ maxBound @Int)

n102F59 :: F 59
n102F59 = 102

n102F59Manual :: F 59
n102F59Manual = unsafeCoerce (102 `mod` 59 :: Int)

f59AddPrelude :: F 59 -> F 59 -> F 59
f59AddPrelude = (P.+)

f59AddAlgebra :: F 59 -> F 59 -> F 59
f59AddAlgebra = (NA.+)

f59AddManual :: Int -> Int -> Int
f59AddManual = \l r ->
  (l + r) `mod` 59

fLargeAddPrelude :: F LargeP -> F LargeP -> F LargeP
fLargeAddPrelude = (P.+)

fLargeAddAlgebra :: F LargeP -> F LargeP -> F LargeP
fLargeAddAlgebra = (NA.+)

fLargeAddManual :: Integer -> Integer -> Integer
fLargeAddManual = \ l r ->
  (l + r) `mod` natVal @LargeP Proxy

checkInspection
  :: IT.Result -> Expectation
checkInspection IT.Success{} = pure ()
checkInspection (IT.Failure msg) =
  fail msg

n43 :: Int
n43 = 43

litLarge :: F LargeP
litLarge = $(
  let p = unPrime $ nextPrime $ floor @Double
        $ sqrt $ fromIntegral $ maxBound @Int
  in litE $ integerL $ p*3 `div` 2
  )

litLargeAnswer :: Integer
litLargeAnswer = $(
  let p = unPrime $ nextPrime $ floor @Double
        $ sqrt $ fromIntegral $ maxBound @Int
  in litE $ integerL $ (p*3 `div` 2) `mod` p
  )

spec :: Spec
spec = do
  describe "F p" $ do
    prop "is a field (for small primes)" $ \(SmallPrime p) ->
          tabulate "p" [show p] $
          reifyPrimeField p $ property . isField
    prop "is a field (for small, but medium primes)" $ \(MediumPrime p) ->
          tabulate "p" [show p] $
          reifyPrimeField p $ property . isField
    prop "is a field (for big primes)" $ \(BigPrime p) ->
      tabulate "p" [show p] $
      reifyPrimeField p $ property . isField
    describe "optimisation for small primes (F 59)" $ do
      describe "literal" $ do
        it "doesn't contain type-classes"
          $ checkInspection $(inspectTest $ hasNoTypeClasses 'n102F59)
        it "is an immediate value modulo casting"
          $ checkInspection $(inspectTest $ 'n102F59 ==- 'n43)
      describe "(Prelude.+)" $ do
        it "has the same core representation as (NA.+) modulo casting" $
          checkInspection $(inspectTest $ 'f59AddPrelude ==- 'f59AddAlgebra)
      describe "(NA.+)" $ do
        it "doesn't contain type-classes" $ do
          checkInspection $(inspectTest $ hasNoTypeClasses 'f59AddAlgebra)
        it "doesn't contain type-natural comparison"
          $ checkInspection $(inspectTest $ 'f59AddAlgebra `doesNotUse` 'SLT)
        it "doesn't contain Integer type" $
          checkInspection $(inspectTest $ 'f59AddAlgebra `hasNoType` ''Integer)
        it "doesn't contain modInteger operation"
          $ checkInspection $(inspectTest $ 'f59AddAlgebra `doesNotUse` 'modInteger)
        it "has the same core as \a b -> (a + b) `mod` 59"
          $ checkInspection $(inspectTest $ 'f59AddAlgebra ==- 'f59AddManual)
    describe ("optimisation for big prime (F " ++ show (natVal @LargeP Proxy) ++ ")") $ do
      describe "literal" $ do
        it "doesn't contain type-classes"
          $ checkInspection $(inspectTest $ hasNoTypeClasses 'litLarge)
        it "is an immediate value modulo casting"
          $ checkInspection $(inspectTest $ 'litLarge ==- 'litLargeAnswer)
      describe "(Prelude.+)" $ do
        it "has the same core representation as (NA.+) modulo casting" $
          checkInspection $(inspectTest $ 'fLargeAddPrelude ==- 'fLargeAddAlgebra)
      describe "(NA.+)" $ do
        it "doesn't contain type-classes" $ do
          checkInspection $(inspectTest $ hasNoTypeClasses 'fLargeAddAlgebra)
        it "doesn't contain type-natural comparison"
          $ checkInspection $(inspectTest $ 'fLargeAddAlgebra `doesNotUse` 'SLT)
        it "doesn't contain Integer type" $
          checkInspection $(inspectTest $ 'fLargeAddAlgebra `hasNoType` ''Int)
        it "doesn't contain modInt# operation"
          $ checkInspection $(inspectTest $ 'fLargeAddAlgebra `doesNotUse` 'modInt#)
        it "has the same core as \a b -> (a + b) `mod` p"
          $ checkInspection $(inspectTest $ 'fLargeAddAlgebra ==- 'fLargeAddManual)

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

instance Testable IT.Result where
  property IT.Success{} = property True
  property (IT.Failure msg) = error $ "Inspection failure: " ++ msg
