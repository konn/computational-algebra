{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fplugin Data.Singletons.TypeNats.Presburger #-}

module Algebra.Algorithms.Groebner.ZeroDimSpec where

import Algebra.Algorithms.Groebner
import Algebra.Algorithms.ZeroDim
import Algebra.Internal
import Algebra.Prelude.Core hiding ((%))
import Algebra.Ring.Ideal
import Algebra.Ring.Polynomial
import Algebra.Ring.Polynomial.Quotient
import Control.Monad
import Control.Monad.Random
import Data.Complex
import Data.Convertible (convert)
import qualified Data.Foldable as F
import qualified Data.Matrix as M
import Data.Maybe
import qualified Data.Sized as SV
import Data.Type.Natural.Lemma.Order
import qualified Data.Vector as V
import Numeric.Field.Fraction (Fraction, (%))
import Numeric.Natural
import Test.QuickCheck hiding (promote)
import qualified Test.QuickCheck as QC
import Test.Tasty
import Test.Tasty.ExpectedFailure
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Utils
import qualified Prelude as P

default (Fraction Integer, Natural)

asGenListOf :: Gen [a] -> a -> Gen [a]
asGenListOf = const

test_solveLinear :: TestTree
test_solveLinear =
  testGroup
    "solveLinear"
    [ testCase "solves data set correctly" $
        forM_ linSet $ \set ->
          solveLinear (M.fromLists $ inputMat set) (V.fromList $ inputVec set)
            @?= Just (V.fromList $ answer set)
    , testProperty "solves any solvable cases" $
        forAll (resize 10 arbitrary) $ \(MatrixCase ms) ->
          let mat = M.fromLists ms :: M.Matrix (Fraction Integer)
           in rank mat == M.ncols mat
                ==> forAll (vector (length $ head ms))
                $ \v ->
                  let ans = M.getCol 1 $ mat P.* M.colVector (V.fromList v)
                   in solveLinear mat ans == Just (V.fromList v)
    , ignoreTestBecause "Needs effective inputs for this" $
        testCase "cannot solve unsolvable cases" $
          pure ()
    ]

test_univPoly :: TestTree
test_univPoly =
  testGroup
    "univPoly"
    [ testProperty "produces monic generators of the elimination ideal" $
        withMaxSuccess 25 $
          QC.mapSize (const 4) $
            checkForTypeNat [2 .. 4] chk_univPoly
    ]

test_radical :: TestTree
test_radical =
  testGroup
    "radical"
    [ ignoreTestBecause "We can verify correctness by comparing with singular, but it's not quite smart way..." $
        testCase "really computes radical" $ pure ()
    ]

test_fglm :: TestTree
test_fglm =
  testGroup
    "fglm"
    [ testProperty "computes monomial basis" $
        withMaxSuccess 25 $
          mapSize (const 3) $
            checkForTypeNat [2 .. 4] $ \sdim ->
              case zeroOrSucc sdim of
                IsZero -> error "impossible"
                IsSucc k ->
                  withWitness (lneqSucc k) $
                    withWitness (lneqZero k) $
                      withKnownNat k $
                        forAll (zeroDimOf sdim) $ \(ZeroDimIdeal ideal) ->
                          let base =
                                reifyQuotient (mapIdeal (changeOrder Lex) ideal) $ \ii ->
                                  map quotRepr $ fromJust $ standardMonomials' ii
                           in stdReduced (snd $ fglm ideal) == stdReduced base
    , testProperty "computes lex base" $
        checkForTypeNat [2 .. 4] $ \sdim ->
          case zeroOrSucc sdim of
            IsZero -> error "impossible"
            IsSucc k -> withKnownNat k $
              withWitness (lneqSucc k) $
                withWitness (lneqZero k) $
                  forAll (zeroDimOf sdim) $ \(ZeroDimIdeal ideal) ->
                    stdReduced (fst $ fglm ideal)
                      == stdReduced (calcGroebnerBasisWith Lex ideal)
    , testProperty "returns lex base in descending order" $
        checkForTypeNat [2 .. 4] $ \sdim ->
          case zeroOrSucc sdim of
            IsZero -> error "impossible"
            IsSucc k -> withKnownNat k $
              case (lneqSucc k, lneqZero k) of
                (Witness, Witness) ->
                  forAll (zeroDimOf sdim) $ \(ZeroDimIdeal ideal) ->
                    isDescending (map leadingMonomial $ fst $ fglm ideal)
    ]

test_solve' :: TestTree
test_solve' =
  testGroup
    "solve'"
    [ testProperty "solves equation with admissible error" $
        withMaxSuccess 50 $
          mapSize (const 4) $ do
            checkForTypeNat [2 .. 4] $ chkIsApproximateZero 1e-5 (pure . solve' 1e-5)
    , testGroup "solves regression cases correctly" $
        map (approxZeroTestCase 1e-5 (pure . solve' 1e-5)) companionRegressions
    ]

test_solveViaCompanion :: TestTree
test_solveViaCompanion =
  testGroup
    "solveViaCompanion"
    [ testProperty "solves equation with admissible error" $
        withMaxSuccess 50 $
          mapSize (const 4) $
            checkForTypeNat [2 .. 4] $
              chkIsApproximateZero
                1e-5
                (pure . solveViaCompanion 1e-5)
    , testGroup "solves regression cases correctly" $
        map (approxZeroTestCase 1e-5 (pure . solveViaCompanion 1e-5)) companionRegressions
    ]

test_solveM :: TestTree
test_solveM =
  testGroup
    "solveM"
    [ testProperty "solves equation with admissible error" $
        withMaxSuccess 50 $
          mapSize (const 4) $
            checkForTypeNat [2 .. 4] $ chkIsApproximateZero 1e-9 solveM
    , testGroup "solves regressions correctly" $
        map (approxZeroTestCase 1e-9 solveM) companionRegressions
    ]

isDescending :: Ord a => [a] -> Bool
isDescending xs = and $ zipWith (>=) xs (drop 1 xs)

chkIsApproximateZero ::
  (KnownNat n) =>
  Double ->
  ( forall m.
    (0 < m, KnownNat m) =>
    Ideal (Polynomial (Fraction Integer) m) ->
    IO [Sized m (Complex Double)]
  ) ->
  SNat n ->
  Property
chkIsApproximateZero err solver sn =
  case zeroOrSucc sn of
    IsSucc _ ->
      withKnownNat sn $
        forAll (zeroDimOf sn) $ ioProperty . checkSolverApproxZero err solver
    IsZero -> error "chkIsApproximateZero must be called with non-zero typenats!"

companionRegressions ::
  [SolverTestCase]
companionRegressions =
  [ SolverTestCase @3 $
      let [x, y, z] = vars
       in ZeroDimIdeal $
            toIdeal
              [ 2 * x ^ 2 + (0.5 :: Fraction Integer) .*. x * y
              , - (0.5 :: Fraction Integer) .*. y ^ 2 + y * z
              , z ^ 2 - z
              ]
  , SolverTestCase @3 $
      let [x, y, z] = vars
       in ZeroDimIdeal $
            toIdeal
              [2 * x + 1, 2 * y ^ 2, - z ^ 2 - 1]
  , SolverTestCase @2 $
      let [x, y] = vars
       in ZeroDimIdeal $
            toIdeal
              [x ^ 2 - y, -2 * y ^ 2]
  ]

approxZeroTestCase ::
  Double ->
  ( forall n.
    (0 < n, KnownNat n) =>
    Ideal (Polynomial (Fraction Integer) n) ->
    IO [Sized n (Complex Double)]
  ) ->
  SolverTestCase ->
  TestTree
approxZeroTestCase err calc (SolverTestCase f@(ZeroDimIdeal i)) =
  testCase (show $ getIdeal f) $ do
    isZeroDimensional (F.toList i) @? "Not zero-dimensional!"
    checkSolverApproxZero err calc f
      @? "Solved correctly"

checkSolverApproxZero ::
  (0 < n, KnownNat n) =>
  Double ->
  (Ideal (Polynomial (Fraction Integer) n) -> IO [Sized n (Complex Double)]) ->
  ZeroDimIdeal n ->
  IO Bool
checkSolverApproxZero err solver (ZeroDimIdeal ideal) = do
  anss <- solver ideal
  let mul r d = convert r * d
  pure $
    all
      ( \as ->
          all ((< err) . magnitude . substWith mul as) $
            generators ideal
      )
      anss

data SolverTestCase where
  SolverTestCase ::
    (0 < n, KnownNat n) =>
    ZeroDimIdeal n ->
    SolverTestCase

chk_univPoly :: KnownNat n => SNat n -> Property
chk_univPoly sdim =
  forAll (zeroDimOf sdim) $ \(ZeroDimIdeal ideal) ->
    let ods = enumOrdinal sdim
     in conjoin $
          flip map ods $ \nth ->
            let gen = univPoly nth ideal
             in forAll (unaryPoly sdim nth) $ \f ->
                  (f `modPolynomial` [gen] == 0) == (f `isIdealMember` ideal)

rank :: (Ord r, Fractional r) => M.Matrix r -> Int
rank mat =
  let Just (u, _, _, _, _, _) = M.luDecomp' mat
   in V.foldr (\a acc -> if a /= 0 then acc + 1 else acc) (0 :: Int) $ M.getDiag u

data TestSet = TestSet
  { inputMat :: [[Fraction Integer]]
  , inputVec :: [Fraction Integer]
  , answer :: [Fraction Integer]
  }
  deriving (Show, Eq, Ord)

linSet :: [TestSet]
linSet =
  [ TestSet
      [ [1, 0, 0, 0, 0]
      , [0, (-2), (-2), (-2), (-2)]
      , [0, 0, 3 % 2, 0, (-1) % 2]
      , [0, 0, 0, 0, (-5) % 2]
      , [0, 1, 1, 1, 1]
      , [0, 0, (-2), 1, (-1)]
      ]
      [0, (-2), 19 % 5, 14 % 5, 1, 0]
      [0, (-81) % 25, 54 % 25, 16 % 5, (-28) % 25]
  ]
