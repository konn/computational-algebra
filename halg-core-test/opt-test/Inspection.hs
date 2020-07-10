{-# LANGUAGE DataKinds, DerivingStrategies, GADTs                          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, KindSignatures, MagicHash         #-}
{-# LANGUAGE NoImplicitPrelude, PolyKinds, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell, TypeApplications                             #-}
{-# OPTIONS_GHC -fno-hpc -Wno-orphans -O2 #-}
{-# OPTIONS_GHC -dsuppress-idinfo -dsuppress-coercions
      -dsuppress-type-applications
      -dsuppress-module-prefixes -dsuppress-type-signatures
      -dsuppress-uniques
  #-}
module Inspection (main) where
import           Algebra.Arithmetic       (modPow)
import           Algebra.Field.Prime
import           AlgebraicPrelude
import qualified AlgebraicPrelude         as NA
import           Data.Proxy               (Proxy (..))
import           Data.Singletons.Prelude
import           GHC.Base                 (modInt#)
import           GHC.Integer
import           GHC.TypeLits             (natVal)
import           Language.Haskell.TH
import           Math.NumberTheory.Primes
import qualified Prelude                  as P
import           Test.Hspec
import           Test.Inspection

type LargeP = $(litT $ numTyLit $ unPrime
  $ nextPrime $ floor @Double
  $ sqrt $ fromIntegral $ maxBound @Int)

n102F59 :: F 59
n102F59 = 102

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

f59ProductSum :: [[F 59]] -> F 59
f59ProductSum xs = product $ map sum xs

f59PowPrelude :: F 59 -> Natural -> F 59
f59PowPrelude = (P.^)

f59PowAlgebra :: F 59 -> Natural -> F 59
f59PowAlgebra = (NA.^)

f59ModPow :: WrapIntegral Int -> Natural -> WrapIntegral Int
f59ModPow i n = modPow i 59 n

checkInspection
  :: Result -> Expectation
checkInspection Success{} = pure ()
checkInspection (Failure msg) =
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

main :: IO ()
main = hspec $ do
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
      it "has the same core as \\a b -> (a + b) `mod` 59"
        $ checkInspection $(inspectTest $ 'f59AddAlgebra ==- 'f59AddManual)
    describe "productSum" $ do
      it "doesn't contain type-classes" $
        checkInspection $(inspectTest $ hasNoTypeClasses 'f59ProductSum)
      it "doesn't contain modInteger" $
        checkInspection $(inspectTest $ 'f59ProductSum `doesNotUse` 'modInteger)

    describe "(P.^)" $ do
      it "doesn't contain type-classes" $ do
        checkInspection $(inspectTest $ hasNoTypeClasses 'f59PowPrelude)
      it "doesn't contain type-natural comparison"
        $ checkInspection $(inspectTest $ 'f59PowPrelude `doesNotUse` 'SLT)
      it "doesn't contain modInteger operation"
        $ checkInspection $(inspectTest $ 'f59PowPrelude `doesNotUse` 'modInteger)

    describe "(NA.^)" $ do
      it "is almost the same as modPow" $
        checkInspection
          $(inspectTest
          $ 'f59PowAlgebra ==- 'f59ModPow
          )
      it "doesn't contain type-natural comparison"
        $ checkInspection $(inspectTest $ 'f59PowAlgebra `doesNotUse` 'SLT)
      it "doesn't contain modInteger operation"
        $ checkInspection $(inspectTest $ 'f59PowAlgebra `doesNotUse` 'modInteger)

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
      it "doesn't contain Int type" $
        checkInspection $(inspectTest $ 'fLargeAddAlgebra `hasNoType` ''Int)
      it "doesn't contain modInt# operation"
        $ checkInspection $(inspectTest $ 'fLargeAddAlgebra `doesNotUse` 'modInt#)
      it "has the same core as \\a b -> (a + b) `mod` p"
        $ checkInspection $(inspectTest $ 'fLargeAddAlgebra ==- 'fLargeAddManual)
