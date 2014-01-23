{-# LANGUAGE DataKinds, GADTs, RankNTypes #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
module ZeroDimSpec where
import           Algebra.Algorithms.Groebner
import           Algebra.Algorithms.ZeroDim
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Algebra.Ring.Polynomial.Quotient
import           Control.Monad
import           Control.Monad.Random
import           Data.Complex
import qualified Data.Matrix                      as M
import           Data.Maybe
import           Data.Type.Monomorphic
import           Data.Type.Natural                hiding (one, promote, zero)
import           Data.Type.Ordinal
import qualified Data.Vector                      as V
import qualified Data.Vector.Sized                as SV
import           SingularBridge
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck                  hiding (promote)
import           Utils

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
      let mat = M.fromLists ms :: M.Matrix Rational
      in rank mat == M.ncols mat ==>
           forAll (vector (length $ head ms)) $ \v ->
             let ans = M.getCol 1 $ mat * M.colVector (V.fromList v)
             in solveLinear mat ans == Just (V.fromList v)
    it "cannot solve unsolvable cases" $ do
      pendingWith "need example"
  describe "univPoly" $ modifyMaxSuccess (const 50) $ modifyMaxSize (const 4) $ do
    prop "produces elimination ideal's monic generator" $ do
      checkForArity [2..4] prop_univPoly
  describe "radical" $ do
    it "really computes radical" $ do
      pendingWith "We can verify correctness by comparing with singular, but it's not quite smart way..."
{-
      checkForArity [2..4] $ \sdim ->
        forAll (zeroDimOf sdim) $ \(ZeroDimIdeal ideal) ->
        stdReduced (generators $ radical ideal) == calcGroebnerBasis (singIdealFun "radical" ideal)
      -- pendingWith "I couldn't formulate the spec for radical without existentials :-("
-}
  describe "fglm" $ modifyMaxSuccess (const 25) $ modifyMaxSize (const 3) $ do
    prop "computes monomial basis" $
      checkForArity [2..4] $ \sdim ->
        case sdim of
          SZ -> error "impossible"
          SS _ ->
            forAll (zeroDimOf sdim) $ \(ZeroDimIdeal ideal) ->
            let base = reifyQuotient (mapIdeal (changeOrder Lex) ideal) $ \ii ->
                  map quotRepr $ fromJust $ standardMonomials' ii
            in stdReduced (snd $ fglm ideal) == stdReduced base
    prop "computes lex base" $ do
      checkForArity [2..4] $ \sdim ->
        case sdim of
          SZ -> error "impossible"
          SS _ ->
            forAll (zeroDimOf sdim) $ \(ZeroDimIdeal ideal) ->
            stdReduced (fst $ fglm ideal) == stdReduced (calcGroebnerBasisWith Lex ideal)
    prop "returns lex base in descending order" $
      checkForArity [2..4] $ \sdim ->
      case sdim of
          SZ -> error "impossible"
          SS _ ->
            forAll (zeroDimOf sdim) $ \(ZeroDimIdeal ideal) ->
            isDescending (map leadingMonomial $ fst $ fglm ideal)
  describe "solve'" $ modifyMaxSuccess (const 50) $ modifyMaxSize (const 4) $ do
    it "solves equation with admissible error" $ do
      checkForArity [2..4] $ prop_isApproximateZero 1e-10 (solve' 1e-10)
  describe "solve''" $ modifyMaxSuccess (const 50) $ modifyMaxSize (const 4) $ do
    it "solves equation with admissible error" $ do
      checkForArity [2..4] $ prop_isApproximateZero 1e-5 (solve'' 1e-10)
  describe "solveViaCompanion" $ modifyMaxSuccess (const 50) $ modifyMaxSize (const 4) $ do
    it "solves equation with admissible error" $ do
      checkForArity [2..4] $ prop_isApproximateZero 1e-5 (solveViaCompanion 1e-10)
  describe "solveM" $ modifyMaxSuccess (const 50) $ modifyMaxSize (const 4) $ do
    prop "solves equation with admissible error" $ \seed ->
      let gen = mkStdGen seed
      in checkForArity [2..4] $ prop_isApproximateZero 1e-10 (\t -> evalRand (solveM t) gen)

isDescending :: Ord a => [a] -> Bool
isDescending xs = and $ zipWith (>=) xs (drop 1 xs)

prop_isApproximateZero :: SingRep n
                       => Double
                       -> (forall m ord. (SingRep m, IsMonomialOrder ord) =>
                           Ideal (OrderedPolynomial Rational ord (S m)) -> [SV.Vector (Complex Double) (S m)])
                       -> SNat n -> Property
prop_isApproximateZero err solver sn =
  case sn of
    SS _ -> forAll (zeroDimOf sn) $ \(ZeroDimIdeal ideal) ->
      let anss = solver ideal
          mul r d = fromRational r * d
      in all (\as -> all ((<err) . magnitude . substWith mul as) $ generators ideal) anss

prop_univPoly :: SingRep n => SNat n -> Property
prop_univPoly sdim =
  forAll (zeroDimOf sdim) $ \(ZeroDimIdeal ideal) ->
  let ods = enumOrdinal sdim
  in conjoin $ flip map ods $ \nth ->
  let gen = univPoly nth ideal
  in forAll (unaryPoly sdim nth) $ \f ->
  (f `modPolynomial` [gen] == 0) == (f `isIdealMember` ideal)

rank :: (Eq r, Num r, Ord r, Fractional r) => M.Matrix r -> Int
rank mat =
  let (u, _, _, _,_, _) = M.luDecomp' mat
  in V.foldr (\a acc -> if a /= 0 then acc + 1 else acc) (0 :: Int) $ M.getDiag u

data TestSet = TestSet { inputMat :: [[Rational]]
                       , inputVec :: [Rational]
                       , answer   :: [Rational]
                       } deriving (Read, Show, Eq, Ord)

linSet :: [TestSet]
linSet =
  [TestSet
   [[1 ,0 ,0 ,0 ,0 ]
   ,[0 ,(-2) ,(-2) ,(-2) ,(-2) ]
   ,[0 ,0 ,3 / 2,0 ,(-1) / 2]
   ,[0 ,0 ,0 ,0 ,(-5) / 2]
   ,[0 ,1 ,1 ,1 ,1 ]
   ,[0 ,0 ,(-2) ,1 ,(-1) ]
   ]
   [0 ,(-2) ,19 / 5,14 / 5,1 ,0 ]
   [0 ,(-81) / 25,54 / 25,16 / 5,(-28) / 25]
  ]

