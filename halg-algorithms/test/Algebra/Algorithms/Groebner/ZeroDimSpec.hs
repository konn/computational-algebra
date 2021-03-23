{-# LANGUAGE DataKinds, GADTs, LambdaCase, NoImplicitPrelude, RankNTypes #-}
{-# LANGUAGE TypeApplications, TypeOperators                             #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -fplugin Data.Singletons.TypeNats.Presburger #-}
module Algebra.Algorithms.Groebner.ZeroDimSpec where
import           Algebra.Algorithms.Groebner
import           Algebra.Algorithms.ZeroDim
import           Algebra.Internal
import           Algebra.Internal
import           Algebra.Prelude.Core             hiding ((%))
import           Algebra.Ring.Ideal
import           Algebra.Ring.Polynomial
import           Algebra.Ring.Polynomial.Quotient
import qualified Prelude                          as P

import           Control.Monad
import           Control.Monad.Random
import           Data.Complex
import           Data.Convertible       (convert)
import qualified Data.Foldable          as F
import qualified Data.Matrix            as M
import           Data.Maybe
import qualified Data.Sized     as SV
import qualified Data.Vector            as V
import           Numeric.Field.Fraction (Fraction, (%))
import           Numeric.Natural
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.HUnit
import           Test.QuickCheck        hiding (promote)
import           Utils

default (Fraction Integer, Natural)

asGenListOf :: Gen [a] -> a -> Gen [a]
asGenListOf = const

spec :: Spec
spec = parallel $ do
  describe "solveLinear" $ do
    it "solves data set correctly" $
      forM_ linSet $ \set ->
      solveLinear (M.fromLists $ inputMat set) (V.fromList $ inputVec set)
      `shouldBe` Just (V.fromList $ answer set)
    prop "solves any solvable cases" $
      forAll (resize 10 arbitrary) $ \(MatrixCase ms) ->
      let mat = M.fromLists ms :: M.Matrix (Fraction Integer)
      in rank mat == M.ncols mat ==>
           forAll (vector (length $ head ms)) $ \v ->
             let ans = M.getCol 1 $ mat P.* M.colVector (V.fromList v)
             in solveLinear mat ans == Just (V.fromList v)
    it "cannot solve unsolvable cases" $
      pendingWith "need example"
  describe "univPoly" $ modifyMaxSuccess (const 25) $ modifyMaxSize (const 4) $
    prop "produces monic generators of the elimination ideal" $
      checkForTypeNat [2..4] prop_univPoly
  describe "radical" $
    it "really computes radical" $
      pendingWith "We can verify correctness by comparing with singular, but it's not quite smart way..."

  describe "fglm" $ modifyMaxSuccess (const 25) $ modifyMaxSize (const 3) $ do
    prop "computes monomial basis" $
      checkForTypeNat [2..4] $ \sdim ->
        case zeroOrSucc sdim of
          IsZero -> error "impossible"
          IsSucc k ->
            withWitness (lneqSucc k) $ withWitness (lneqZero k) $
            withKnownNat k $
            forAll (zeroDimOf sdim) $ \(ZeroDimIdeal ideal) ->
            let base =
                  reifyQuotient (mapIdeal (changeOrder Lex) ideal) $ \ii ->
                  map quotRepr $ fromJust $ standardMonomials' ii
            in stdReduced (snd $ fglm ideal) == stdReduced base
    prop "computes lex base" $
      checkForTypeNat [2..4] $ \sdim ->
        case zeroOrSucc sdim of
          IsZero -> error "impossible"
          IsSucc k -> withKnownNat k $
            withWitness (lneqSucc k) $
            withWitness (lneqZero k) $
            forAll (zeroDimOf sdim) $ \(ZeroDimIdeal ideal) ->
            stdReduced (fst $ fglm ideal)
              == stdReduced (calcGroebnerBasisWith Lex ideal)
    prop "returns lex base in descending order" $
      checkForTypeNat [2..4] $ \sdim ->
      case zeroOrSucc sdim of
        IsZero -> error "impossible"
        IsSucc k -> withKnownNat k $
          case (lneqSucc k, lneqZero k) of
            (Witness, Witness) ->
              forAll (zeroDimOf sdim) $ \(ZeroDimIdeal ideal) ->
              isDescending (map leadingMonomial $ fst $ fglm ideal)
  describe "solve'" $ modifyMaxSuccess (const 50) $ modifyMaxSize (const 4) $ do
    it "solves equation with admissible error" $
      checkForTypeNat [2..4] $ prop_isApproximateZero 1e-5 (pure . solve' 1e-5)
    describe "solves regression cases correctly" $
      forM_ companionRegressions $
      approxZeroTestCase 1e-5 (pure . solve' 1e-5)

  describe "solveViaCompanion" $
    modifyMaxSuccess (const 50) $ modifyMaxSize (const 4) $ do
    it "solves equation with admissible error" $
      checkForTypeNat [2..4] $ prop_isApproximateZero 1e-5
        (pure . solveViaCompanion 1e-5)
    describe "solves regression cases correctly" $
      forM_ companionRegressions $
      approxZeroTestCase 1e-5 (pure . solveViaCompanion 1e-5)

  describe "solveM" $ modifyMaxSuccess (const 50) $ modifyMaxSize (const 4) $ do
    prop "solves equation with admissible error" $
      checkForTypeNat [2..4] $ prop_isApproximateZero 1e-9 solveM
    describe "solves regressions correctly" $
      forM_ companionRegressions $
      approxZeroTestCase 1e-9 solveM

isDescending :: Ord a => [a] -> Bool
isDescending xs = and $ zipWith (>=) xs (drop 1 xs)

prop_isApproximateZero
  :: (KnownNat n)
  => Double
  -> (forall m. ((0 < m) ~ 'True, KnownNat m) =>
      Ideal (Polynomial (Fraction Integer) m) -> IO [Sized m (Complex Double)])
  -> SNat n -> Property
prop_isApproximateZero err solver sn =
  case zeroOrSucc sn of
    IsSucc _ -> withKnownNat sn $
      forAll (zeroDimOf sn) $ ioProperty . checkSolverApproxZero err solver
    IsZero -> error "prop_isApproximateZero must be called with non-zero typenats!"

companionRegressions
  :: [SolverTestCase]
companionRegressions =
  [ SolverTestCase @3 $
    let [x,y,z] = vars
    in ZeroDimIdeal $ toIdeal
        [ 2*x^2 + (0.5 :: Fraction Integer) .*. x * y
        , -(0.5 :: Fraction Integer) .*. y ^ 2 + y * z
        , z^2 - z]
  , SolverTestCase @3 $
    let [x,y,z] = vars
    in ZeroDimIdeal $ toIdeal
        [ 2*x + 1, 2*y^2,-z^2 - 1]
  , SolverTestCase @2 $
    let [x,y] = vars
    in ZeroDimIdeal $ toIdeal
        [ x^2 - y, -2*y^2]
  ]

approxZeroTestCase
  :: Double
  -> (forall n. ((0 < n) ~ 'True, KnownNat n)
        => Ideal (Polynomial (Fraction Integer) n) -> IO [Sized n (Complex Double)]
      )
  -> SolverTestCase
  -> SpecWith ()
approxZeroTestCase err calc (SolverTestCase f@(ZeroDimIdeal i)) =
  it (show $ getIdeal f) $ do
    isZeroDimensional (F.toList i) @? "Not zero-dimensional!"
    checkSolverApproxZero err calc f
      @? "Solved correctly"


checkSolverApproxZero
  :: ((0 < n) ~ 'True, KnownNat n)
  => Double
  -> (Ideal (Polynomial (Fraction Integer) n) -> IO [Sized n (Complex Double)])
  -> ZeroDimIdeal n
  -> IO Bool
checkSolverApproxZero err solver (ZeroDimIdeal ideal) = do
  anss <- solver ideal
  let mul r d = convert r * d
  pure
    $ all (\as -> all ((<err) . magnitude . substWith mul as)
    $ generators ideal) anss

data SolverTestCase where
  SolverTestCase
    :: ((0 < n) ~ 'True, KnownNat n)
    => ZeroDimIdeal n -> SolverTestCase

prop_univPoly :: KnownNat n => SNat n -> Property
prop_univPoly sdim =
  forAll (zeroDimOf sdim) $ \(ZeroDimIdeal ideal) ->
  let ods = enumOrdinal sdim
  in conjoin $ flip map ods $ \nth ->
  let gen = univPoly nth ideal
  in forAll (unaryPoly sdim nth) $ \f ->
  (f `modPolynomial` [gen] == 0) == (f `isIdealMember` ideal)

rank :: (Ord r, Fractional r) => M.Matrix r -> Int
rank mat =
  let Just (u, _, _, _,_, _) = M.luDecomp' mat
  in V.foldr (\a acc -> if a /= 0 then acc + 1 else acc) (0 :: Int) $ M.getDiag u

data TestSet = TestSet { inputMat :: [[Fraction Integer]]
                       , inputVec :: [Fraction Integer]
                       , answer   :: [Fraction Integer]
                       } deriving (Show, Eq, Ord)

linSet :: [TestSet]
linSet =
  [TestSet
   [[1 ,0 ,0 ,0 ,0 ]
   ,[0 ,(-2) ,(-2) ,(-2) ,(-2) ]
   ,[0 ,0 ,3 % 2,0 ,(-1) % 2]
   ,[0 ,0 ,0 ,0 ,(-5) % 2]
   ,[0 ,1 ,1 ,1 ,1 ]
   ,[0 ,0 ,(-2) ,1 ,(-1) ]
   ]
   [0 ,(-2) ,19 % 5,14 % 5,1 ,0 ]
   [0 ,(-81) % 25,54 % 25,16 % 5,(-28) % 25]
  ]

