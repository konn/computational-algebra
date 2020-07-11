{-# OPTIONS_GHC -Wno-orphans -Wno-type-defaults #-}
{-# LANGUAGE AllowAmbiguousTypes, DataKinds, ExtendedDefaultRules        #-}
{-# LANGUAGE FlexibleInstances, GADTs, OverloadedLabels, OverloadedLists #-}
{-# LANGUAGE ParallelListComp, PolyKinds, ScopedTypeVariables            #-}
{-# LANGUAGE TypeApplications                                            #-}
module Algebra.Ring.Polynomial.FactoriseSpec where
import qualified Algebra.Field.Finite               as Fin
import           Algebra.Field.Fraction.Test        ()
import           Algebra.Field.Galois
import           Algebra.Field.Prime
import           Algebra.Field.Prime.Test           ()
import           Algebra.Prelude.Core               hiding ((===))
import           Algebra.Ring.Polynomial.Factorise
import           Algebra.Ring.Polynomial.Univariate
import           Control.Arrow
import           Control.Lens
import           Control.Monad.Random
import           Data.Functor                       ((<&>))
import qualified Data.IntMap                        as IM
import           Data.Monoid                        (Sum (..))
import qualified Data.Set                           as S
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.HUnit                         hiding (Testable)
import           Test.QuickCheck                    as QC
import           Type.Reflection

default ([])

data Regression where
  MkRegression
    :: (Num k, FiniteField k, Random k, PrettyCoeff k, CoeffRing k, Typeable k)
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
  , MkRegression @(F 2) $
    #x^66 + #x^65 + #x^64 + #x^62 + #x^57
    + #x^56 + #x^55 + #x^54 + #x^52 + #x^50
    + #x^48 + #x^47 + #x^45 + #x^44 + #x^41
    + #x^38 + #x^37 + #x^35 + #x^33 + #x^30
    + #x^29 + #x^27 + #x^23 + #x^22 + #x^21
    + #x^19 + #x^15 + #x^14 + #x^13 + #x^11
    + #x^10 + #x^9 + #x^7 + #x^5
    + #x^3 + #x^2 + #x + 1
  , MkRegression @(F 3) $
    #x^67 + 2* #x^64 + 2* #x^63 + #x^62 + #x^61 +
    #x^59 + 2* #x^57 + 2* #x^55 + 2* #x^54 + 2* #x^53
    + 2* #x^52 + #x^51 + 2* #x^50 + #x^46 + 2* #x^45
    + #x^43 + #x^40 + 2* #x^39 + #x^38 + #x^37
    + #x^36 + #x^33 + 2* #x^32 + 2* #x^30 + 2* #x^29
    + 2* #x^27 + 2* #x^26 + 2* #x^24 + #x^23 + 2* #x^22
    + #x^21 + 2* #x^20 + #x^19 + 2* #x^18 + #x^16
    + #x^15 + 2* #x^14 + 2* #x^13 + 2* #x^12
    + #x^11 + #x^10 + 2* #x^8 + 2* #x^5
    + 2* #x^4 + 2* #x^3 + 2* #x + 2
  ]
  where
    ξ :: GF 2 5
    ξ = primitive

instance (KnownNat p, KnownNat n, ConwayPolynomial p n)
      => Arbitrary (GF p n) where
  arbitrary = QC.elements $ Fin.elements $ Proxy @(GF p n)

instance (Num r, Arbitrary r, CoeffRing r) => Arbitrary (Unipol r) where
  arbitrary = arbitrary <&> \pns ->
    sum [ (c :: r) .*. #x ^ fromInteger n
        | c <- pns
        | n <- [0..]
        ]

sqFree
  :: Unipol Rational -> Unipol Rational
sqFree g =
  g `quot` gcd g (diff 0 g)

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
  forM_ [("factorQBigPrime", factorQBigPrime), ("factorHensel", factorHensel)]
    $ \(lab, factorer) -> describe lab $ do
      describe "factors regression cases correctly" $
        forM_ intPolys $ \fs ->
        it (show fs) $ do
          (i, dic) <- factorer $ product fs
          i @?= foldr (gcd . content) 1 fs
          dic @?= IM.singleton 1 fs
      modifyMaxSize (const 5) $
        modifyMaxSuccess (const 25) $
        prop "factors a product of distinct polynomials of degree 1"
        $ \(Blind coes) -> again $ ioProperty $ do
          let pls = [ injectCoeff i * #x + injectCoeff j
                    | QC.NonZero r <- S.toList coes
                    , let i = denominator r
                          j = numerator r
                    ]
              expected = product pls
              expectCount = length pls
          (i, facs) <- factorer $ product pls
          let f = i .*. runMult
                    (ifoldMap (\n fs -> Mult $ product fs ^ fromIntegral n) facs)
              givenFact = runAdd $ foldMap (Add . length) facs
              factNumError = unlines
                [ "# of factor mismatched!"
                , "\texpected: " <> show expectCount
                , "\t but got: " <> show givenFact
                , "\t factors: " <> show facs
                ]
              prodLabel =
                unlines
                [ "Product doesnt match the result;"
                , "\texpected: " ++ show expected
                , "\t but got: " ++ show f
                ]
          pure  $ counterexample (show pls)
                $ tabulate "# of factors" [show expectCount]
                $ tabulate "0-Norm" [show $ foldr (max.abs) 0 f]
                $ counterexample prodLabel (f === expected)
            .&&. counterexample factNumError
                  (givenFact === expectCount)


      modifyMaxSize (const 3)
          $ modifyMaxSuccess (const 25)
          $ prop "reconstructs the original " $ \(NonZero f00) (NonZero g00) -> ioProperty $ do
            let h0 = sqFree $ f00 * g00
                f0 = h0 `quot` gcd (diff 0 h0) h0
                c = foldr' (lcm . denominator) 1 f0
                f = mapCoeffUnipol (numerator . (fromInteger c*)) f0
            (i, dic) <- factorQBigPrime f
            let facts = getSum $ ifoldMap (\n -> Sum . (n*) . length) dic
            pure
              $ tabulate "totalDegree" [show $ totalDegree' f]
              $ tabulate "number of factors"
                [show facts]
              $ counterexample
                "reconstruction failed"
                (i .*. runMult
                  (ifoldMap (\n fs ->
                      Mult $ product fs ^ fromIntegral n
                  ) dic)
                  === f)
                  .&&.
                counterexample
                  "# of factor mismatched"
                (facts >= length (filter ((>0) . totalDegree') [f00,g00]))

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
      ( Arbitrary r, Random r,
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
      ( Arbitrary r, Random r,
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

intPolys :: [S.Set (Unipol Integer)]
intPolys =
  [ [#x + 2, 2 * #x ^ 2 + 1, #x - 2]
  , [3 * #x + 1, 4 * #x + 3]
  , [#x - 2, 4 * #x + 1]
  ]

fromFactorisation
  :: CoeffRing r => [(Unipol r, Natural)] -> Unipol r
fromFactorisation facs =
  product [g^n | (g, n) <- facs]
