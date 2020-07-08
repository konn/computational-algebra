{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes, DataKinds, FlexibleInstances, GADTs #-}
{-# LANGUAGE OverloadedLabels, ParallelListComp, PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications                    #-}
module Algebra.Ring.Polynomial.FactoriseSpec where
import qualified Algebra.Field.Finite               as Fin
import           Algebra.Field.Galois
import           Algebra.Field.Prime
import           Algebra.Prelude.Core               hiding ((===))
import           Algebra.Ring.Polynomial.Factorise
import           Algebra.Ring.Polynomial.Univariate
import           Control.Arrow
import           Data.Functor                       ((<&>))
import qualified Data.IntMap                        as IM
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.HUnit                         hiding (Testable)
import           Test.QuickCheck                    as QC
import           Type.Reflection

data Regression where
  MkRegression
    :: (Num k, FiniteField k, PrettyCoeff k, CoeffRing k, Typeable k)
    => Unipol k -> Regression

regressions :: [Regression]
regressions =
  [ MkRegression @(GF 2 5) $ #x^2 + injectCoeff (ξ^2 + ξ + 1)
  , MkRegression @(GF 2 5) $
      (ξ^4 + 1) .*. #x^2 + injectCoeff (ξ^4 + ξ^3)
  , MkRegression @(GF 2 5) $
    #x^6 + (ξ^4 + ξ^3 + ξ^2 + ξ) .*. #x^5 + (ξ^4 + ξ + 1) .*. #x^4
    + (ξ^3 + ξ^2 + ξ + 1) .*. #x^3 + (ξ^3 + 1) .*. #x^2
    + (ξ^4 + ξ^3 + ξ + 1) .*. #x
    + injectCoeff (ξ^4 + ξ^3 + ξ)
  ]
  where
    ξ :: GF 2 5
    ξ = primitive

instance IsPrimeChar n => Arbitrary (F n) where
  arbitrary = QC.elements $ Fin.elements $ Proxy @(F n)

instance (IsPrimeChar p, KnownNat n, ConwayPolynomial p n)
      => Arbitrary (GF p n) where
  arbitrary = QC.elements $ Fin.elements $ Proxy @(GF p n)

instance (Num r, Arbitrary r, CoeffRing r) => Arbitrary (Unipol r) where
  arbitrary = arbitrary <&> \pns ->
    sum [ (c :: r) .*. #x ^ fromInteger n
        | c <- pns
        | n <- [0..]
        ]

spec :: Spec
spec = parallel $ do
  describe "isReducible" $ modifyMaxSize (const 20) $ do
    checkIsReducible @(F 2)
    checkIsReducible @(F 3)
    checkIsReducible @(F 5)

  describe "squareFreeDecompFiniteField" $
    describe "correctly factors polynomials in regression tests" $
      forM_ regressions $ \(MkRegression f) ->
      when (leadingCoeff f == one) $
      it (show f) $
      let facts = map (swap >>> second fromIntegral)
            $ IM.toList
            $ squareFreeDecompFiniteField f
      in fromFactorisation facts @?= f

  describe "factorise" $ do
    describe "correctly factors polynomials in regression tests" $
      forM_ regressions $ \(MkRegression f) ->
      it (show f) $ do
      facts <- factorise f
      fromFactorisation facts @?= f
    factorReconstructsIn @(F 2)
    factorIrreducibility @(F 2)
    factorReconstructsIn @(F 3)
    factorIrreducibility @(F 3)
    modifyMaxSize (const 50) $
      modifyMaxSuccess (const 25) $
      factorReconstructsIn @(F 5)
    modifyMaxSize (const 50) $
      modifyMaxSuccess (const 25) $
      factorIrreducibility @(F 5)

    modifyMaxSize (const 25) $
      modifyMaxSuccess (const 25) $
      factorReconstructsIn @(GF 2 5)
    modifyMaxSize (const 25) $
      modifyMaxSuccess (const 25) $
      factorIrreducibility @(GF 2 5)

    modifyMaxSize (const 25) $
      modifyMaxSuccess (const 25) $
      factorReconstructsIn @(GF 3 4)
    modifyMaxSize (const 25) $
      modifyMaxSuccess (const 25) $
      factorIrreducibility @(GF 3 4)

factorReconstructsIn
  :: forall r.
      ( Arbitrary r,
        CoeffRing r, PrettyCoeff r,
        Typeable r, Num r, FiniteField r
      ) => Spec
factorReconstructsIn =
  prop ("reconstructs the original input (" ++ show (typeRep @r) ++ ")") $
    \(NonZero (f :: Unipol r)) -> ioProperty $ do
      facts <- factorise f
      pure $ tabulate "total degree"
          [show $ totalDegree' f]
        $ tabulate "number of factors"
          [show $ length facts]
        $ classify (isZero f) "zero" $
        product [g ^ n | (g, n) <- facts] === f

factorIrreducibility
  :: forall r.
      ( Arbitrary r,
        CoeffRing r, PrettyCoeff r,
        Typeable r, Num r, FiniteField r
      ) => Spec
factorIrreducibility =
  prop ("gives irreducible polynomials (" ++ show (typeRep @r) ++ ")") $
    \(NonZero (f :: Unipol r)) -> ioProperty $ do
      facts <- factorise f
      pure $ conjoin
        [ counterexample ("Reducible factor: " ++ show p)
          $ totalDegree' p == 0 || not (isReducible p)
        | (p, _) <- facts]

checkIsReducible
  :: forall r.
      ( Arbitrary r,
        CoeffRing r, PrettyCoeff r,
        Typeable r, Num r, FiniteField r
      ) => Spec
checkIsReducible = do
  prop' "detects reducible polynomial correctly" $
    \(f :: Unipol r) (g :: Unipol r) ->
      tabulate "total degree" [show $ totalDegree' $ f * g] $
      classify ( totalDegree' f == 0 || totalDegree' g == 0)
          "degenerate"
      $ (totalDegree' f /= 0 && totalDegree' g /= 0) ==> isReducible (f * g)
  prop' "if it returns False, it must be irreducible" $
    \(f :: Unipol r) ->
      tabulate "total degree" [show $ totalDegree' f] $
      let n = totalDegree' f
      in not (isReducible f) ==>
          (n === 1 .||. (n === 2 .&&. \a0 ->
              let g = #x + injectCoeff a0
              in counterexample ("Divisor found: " ++ show g)
                $ not $ g `divides` f
          )
            .||. (n > 2 .&&. forAll (QC.elements [1..n-2]) (\m ->
            forAll (vectorOf m $ QC.elements $ Fin.elements $ Proxy @r) $ \coes ->
              let g = #x ^ fromIntegral m + sum (zipWith (.*.) coes [#x ^ i | i <- [0..]])
              in counterexample ("Divisor found: " ++ show g)
              $ not $ g `divides` f))
          )
  where
    prop' :: Testable prop => String -> prop -> Spec
    prop' txt = prop (txt <> "(" ++ show (typeRep @r) ++ ")")

fromFactorisation
  :: CoeffRing r => [(Unipol r, Natural)] -> Unipol r
fromFactorisation facs =
  product [g^n | (g, n) <- facs]
