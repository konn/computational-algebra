{-# LANGUAGE AllowAmbiguousTypes, BangPatterns, DataKinds                   #-}
{-# LANGUAGE ExtendedDefaultRules, FlexibleInstances, GADTs                 #-}
{-# LANGUAGE OverloadedLabels, OverloadedLists, ParallelListComp            #-}
{-# LANGUAGE PolyKinds, ScopedTypeVariables, TypeApplications, ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans -Wno-type-defaults #-}
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
import qualified Data.HashMap.Strict                as HM
import qualified Data.IntMap                        as IM
import           Data.Monoid                        (Sum (..))
import qualified Data.Set                           as S
import           Math.NumberTheory.Primes           hiding (factorise)
import           Math.NumberTheory.Primes.Counting  (nthPrime)
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
  [ MkRegression @(F 3) $
    #x^19 + 2* #x^18 + #x^15 + 2* #x^14 + 2* #x^12 + #x^11 + #x^7 +  #x^6 +  #x^5
  , MkRegression @(F 3)
  $ #x^89 + #x^88 + #x^87 + 2* #x^83 + 2* #x^82 + 2* #x^81 + 2* #x^79
  + 2* #x^77 + 2* #x^76 + 2* #x^75 + #x^74 + 2* #x^73 + #x^72 + 2* #x^71
  + 2* #x^68 + #x^67 + #x^66 + #x^64 + #x^62 + #x^61 + 2* #x^60 + #x^59
  + 2* #x^58 + 2* #x^54 + #x^53 + #x^52 + #x^51 + 2* #x^50 + #x^49 + #x^48
  + #x^47 + #x^45 + #x^44 + 2* #x^41 + 2* #x^38 + #x^36 + #x^34 + 2* #x^33
  + #x^32 + 2* #x^29 + 2* #x^28 + #x^26 + 2* #x^25 + 2* #x^23 + 2* #x^22
  + #x^21 + #x^20 + 2* #x^19 + 2* #x^17 + 2* #x^16 + 2* #x^15 + 2* #x^14
  + 2* #x^12 + #x^10 + 2* #x^9 + 2* #x^7 + 2* #x^6 + 2* #x^3 + #x^2 + 2
  , MkRegression @(GF 2 5) $ #x^2 + injectCoeff (ξ^2 + ξ + 1)
  , MkRegression @(GF 2 5) $
      (ξ^4 + 1) .*. #x^2 + injectCoeff (ξ^4 + ξ^3)
  , MkRegression @(GF 2 5) $
    #x^6 + (ξ^4 + ξ^3 + ξ^2 + ξ) .*. #x^5 + (ξ^4 + ξ + 1) .*. #x^4
    + (ξ^3 + ξ^2 + ξ + 1) .*. #x^3 + (ξ^3 + 1) .*. #x^2
    + (ξ^4 + ξ^3 + ξ + 1) .*. #x
    + injectCoeff (ξ^4 + ξ^3 + ξ)
  , MkRegression @(F 2) $
      #x^8 + #x^3 + #x^2 + #x
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
      it (show f) $ do
      let resls = squareFreeDecompFiniteField f
          facts = map (swap >>> second fromIntegral)
            $ IM.toList resls
          onlyFacts = IM.toList resls
      fromFactorisation facts @?= f
      forM_ (init $ tails onlyFacts) $ \((i,h) : jfs) ->
        forM_ jfs $ \(j, g) -> do
          let common = gcd h g
          common == 1 @? show (i, j) <> " = "
            <> show (h, g)
            <> " must be coprime, but has gcd: "
            <> show common


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
            let h0 = f00 * g00
                f0 = h0 `quot` gcd (diff 0 h0) h0
                c = foldr' (lcm . denominator) 1 f0
                f = mapCoeffUnipol (numerator . (fromInteger c*)) f0
            (i, dic) <- factorer f
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

  describe "henselStep" $ do
    describe "lifts all regression tests correctly" $
      forM_ henselRegressions $ \inp@(HenselCase m f g h s t) ->
      it (show inp) $ do
      let (g', h', s', t') = henselStep m f g h s t
          quo = mapCoeffUnipol (`mod` (m^2))
          fgh' = quo (f - g' * h')
          sgth = quo $ s' * g' + t' * h' - one
      assertEqual "f - g' h' = 0 mod m^2, but:"
        0
        fgh'
      assertEqual "s' g' + t' h' -1 = 0 mod m^2, but:"
        0
        sgth

    modifyMaxSuccess (const 50) $ modifyMaxSize (const 50) $
      prop "successively lifts f = gh mod m with sg + th = 1 to mod m^2 in Z[x]" $
      forAll (QC.elements [1..10]) $
      \ n
        (unPrime -> p)
        (NonZero x)
        (NonEmpty xs)
        (NonZero y)
        (NonEmpty ys)
        zeros ->
      let g0 = ascendingTerms $ xs ++ [x `div` gcd p x]
          h0 = ascendingTerms $ ys ++ [y `div` gcd p y]
          (g,h,s,t) = reifyPrimeField p $ \fp ->
            let g'0 = mapCoeffUnipol (modNat' fp) g0
                h'0 = mapCoeffUnipol (modNat' fp) h0
                g' = g'0 `quot` gcd g'0 h'0
                h' = h'0 `quot` gcd g'0 h'0
                (_,s',t') = egcd g' h'
            in (mapCoeffUnipol naturalRepr g',
                mapCoeffUnipol naturalRepr h',
                mapCoeffUnipol naturalRepr s',
                mapCoeffUnipol naturalRepr t'
                )
          f = g * h + p .*. zeros
      in tabulate "iterateion" [show n]
        $ tabulate "p" [show p]
        $ tabulate "deg(g), deg(h)"
            [ show $ totalDegree' g
            , show $ totalDegree' h
            ]
        $ counterexample (show $ HenselCase p f g h s t)
        $ chkIterateHensel n
        $ HenselCase p f g h s t

  modifyMaxSuccess (const 50) $
    modifyMaxSize (const 50) $
    describe "pthRoot" $ do
    prop "gives pth root" $ \(unPrime -> p) ->
      reifyPrimeField p $ \(_ :: Proxy (F p)) ->
        forAll arbitrary $ \(f :: Unipol (F p)) ->
          pthRoot (f ^ fromIntegral p) === f

  describe "multiHensel" $ do
    it "solves regressions correctly" $ do
      let facs = multiHensel 5 4 (#x^4 - 1)
              [#x-1, #x-2, #x+2, #x+1]
      assertEqual
        "products reconstruct fail"
        0
        $ mapCoeffUnipol (`rem` 5^4) (product facs - (#x^4 - 1))

    modifyMaxSuccess (const 25)
      $ modifyMaxSize (const 20)
      $ prop "lifts coprime factorisation correctly"
      $ \(unPrime -> p) (QC.Positive (Small l))
        (NonZero lca) (NonZero lcb)
        (NonEmpty f00) (NonEmpty g00) ->
        reifyPrimeField p $ \fp ->
        tabulate "p" [show p] $
        tabulate "iterateion" [show l] $
        ioProperty $ do
          let f = ascendingTerms (f00 ++ [clearFactor p lca])
                  *
                  ascendingTerms (g00 ++ [clearFactor p lcb])
              proj = mapCoeffUnipol naturalRepr
          fps0 <- factorise $ mapCoeffUnipol (modNat' fp) f
          let (_, facs) = first (mapCoeffUnipol naturalRepr
                                . product . map (uncurry (^)))
                $ partition ((<1). totalDegree'.fst) fps0
          let gs = map (proj . uncurry (^)) facs
          let facs' = multiHensel (fromIntegral p) l f gs
          pure
            $ tabulate "lc(f)"
              [show $ leadingCoeff f]
            $ tabulate
              "deg(f)"
              [show $ totalDegree' f]
            $ tabulate "# of factors"
              [show $ length gs]
            $ counterexample ("(p,l,f,gs,lc(f)) = " ++ show (p,l,f, gs, leadingCoeff f))
            $ mapCoeffUnipol (`mod` p^fromIntegral l) (f - leadingCoeff f .*. product facs')
                === 0
              .&&.
              conjoin
                (map (\k -> counterexample ("must be monic, but got: " ++ show k)
                      $ leadingCoeff k === 1) facs')
              .&&.
              conjoin
                  (zipWith
                    (\k k' ->
                        counterexample
                          (unwords
                            ["The polynomial", show k
                            , "is lifted to", show k',
                            "but not equal modulo p!"])
                          (mapCoeffUnipol (modNat' fp) k ===
                          mapCoeffUnipol (modNat' fp) k')
                      )
                  gs facs')

hasCommon :: Euclidean d => d -> d -> Bool
hasCommon = ((not . isUnit) .) . gcd
{-# INLINE hasCommon #-}

newtype ShortList a = ShortList { runShortList :: [a] }
  deriving (Read, Show, Eq, Ord)

instance Arbitrary a => Arbitrary (ShortList a) where
  arbitrary = do
    i <- QC.elements [1..5]
    ShortList <$> vectorOf i arbitrary

clearFactor :: Euclidean r => r -> r -> r
clearFactor p = go
  where
    go !x
      | isZero r = go q
      | otherwise = x
      where (q, r) = x `divide` p

chkIterateHensel :: Int -> HenselCase -> Property
chkIterateHensel 0 _ = property True
chkIterateHensel n case_ =
  let (cond, nextCase) = checkHenselOutput case_
  in cond .&&. chkIterateHensel (pred n) nextCase

checkHenselOutput
  :: HenselCase
  -> (Property, HenselCase)
checkHenselOutput (HenselCase m f g h s t) =
  let sqQuo = mapCoeffUnipol (`rem` m^2)
      (gSq, hSq, sSq, tSq) = henselStep m f g h s t
      gh' = sqQuo $ gSq * hSq
      sgth' = sqQuo $ gSq * sSq + hSq * tSq
      chk = counterexample (show $ HenselCase m f gSq hSq sSq tSq)
        $ conjoin
              [ counterexample
                  (mconcat
                    [ "g * h = ", show gSq, " * ", show hSq, " == "
                    , show (sqQuo $ gSq * hSq)
                    , "/=", show (sqQuo f), " mod ", show m]
                  )
                  (gh' === sqQuo f)
              , counterexample
                  (mconcat
                    [ "sg + th = ("
                    , show sSq, ") * (", show gSq
                    , ") + (", show tSq, ") * (", show hSq, ") == "
                    , show (sqQuo $ gSq * sSq + hSq * tSq)
                    , " /= 1", " mod ", show m
                    ]
                  )
                  (sgth' === 1)
              ]
  in (chk, HenselCase (m^2) f gSq hSq sSq tSq)

instance Arbitrary (Prime Integer) where
  arbitrary = nthPrime . getSmall . getPositive <$> arbitrary

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

ascendingTerms
  :: CoeffRing r => [r] -> Unipol r
ascendingTerms
  = runAdd
  . ifoldMap (\i -> Add .
      ((#x^ fromIntegral i) *) . injectCoeff)

data HenselCase =
  HenselCase Integer (Unipol Integer) (Unipol Integer) (Unipol Integer) (Unipol Integer) (Unipol Integer)
  deriving (Show, Eq, Ord)

henselRegressions :: [HenselCase]
henselRegressions =
  [ HenselCase 5
      (#x^4 - 1)
      (#x^3 + 2 * #x^2 - #x - 2)
      (#x - 2)
      (-2)
      (2 * #x^2 - 2 * #x - 1)
  , HenselCase 5
      (#x^4 - 1)
      (#x^2 + 2 * #x + 2)
      (#x^2 - 2 * #x + 2)
      (-2 * #x - 1)
      ( 2 * #x - 1)
  , HenselCase 25
      (#x^4 - 1)
      (#x^3 + 7 * #x^2 - #x - 7)
      (#x - 7)
      8
      (-8 * #x^2 - 12 * #x - 1)
  ]
