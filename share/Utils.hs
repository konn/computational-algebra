{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds, DeriveGeneric, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, MultiParamTypeClasses      #-}
{-# LANGUAGE OverlappingInstances, RankNTypes, ScopedTypeVariables         #-}
{-# LANGUAGE StandaloneDeriving, UndecidableInstances                      #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Utils (ZeroDimIdeal(..), polyOfDim, arbitraryRational,
              arbitrarySolvable, zeroDimOf, zeroDimG, unaryPoly, stdReduced,
              quotOfDim, isNonTrivial, Equation(..), liftSNat, checkForArity,
              MatrixCase(..), idealOfDim) where
import qualified Data.Matrix                   as M hiding (fromList)
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial          hiding (Positive)
import           Algebra.Ring.Polynomial.Quotient
import           Control.Applicative
import           Proof.Equational ((:=:)(..))
import           Control.Lens
import           Control.Monad
import Data.Constraint
import qualified Data.Map                         as M
import           Data.Proxy
import           Data.Ratio
import           Data.Reflection                  hiding (Z)
import           Data.Type.Monomorphic
import qualified Data.Type.Monomorphic            as M
import           Data.Type.Natural
import           Data.Type.Ordinal
import qualified Data.Vector                      as V
import           Data.Vector.Sized                (Vector (..))
import qualified Data.Vector.Sized                as SV
import qualified Numeric.Algebra                  as NA
import           Test.QuickCheck
import qualified Test.QuickCheck                  as QC
import           Test.QuickCheck.Instances        ()
import           Test.SmallCheck.Series
import qualified Test.SmallCheck.Series           as SC
import Data.Ord
import Data.List (sortBy)

newtype ZeroDimIdeal n = ZeroDimIdeal { getIdeal :: Ideal (Polynomial Rational n)
                                      } deriving (Show, Eq, Ord)

(%.) :: Integral a => a -> SC.Positive a -> Ratio a
a %. SC.Positive b = a % b

-- * Instances for SmallCheck.
instance Monad m => Serial m (Monomial Z) where
  series = cons0 Nil

instance (Serial m (Monomial n)) => Serial m (Monomial (S n)) where
  series = (:-) <$> (SC.getNonNegative <$> series) <*> series

instance (Ord k, Serial m k, Serial m v) => Serial m (M.Map k v) where
  series = M.fromList <$> series

instance Serial m (Monomial n) => Serial m (OrderedMonomial ord n) where
  series = newtypeCons OrderedMonomial

instance (Eq r, Noetherian r, SingI n, IsMonomialOrder ord, Serial m r, Serial m (Monomial n))
          => Serial m (OrderedPolynomial r ord n) where
  series = cons2 (curry toPolynomial) \/ cons2 (NA.+)

instance (Num r, Ord r, Noetherian r, Serial m r) => Serial m (Ideal r) where
  series = newtypeCons toIdeal

appendLM :: Rational -> Monomial Two -> Polynomial Rational Two -> Polynomial Rational Two
appendLM coef lm = unwrapped %~ M.insert (OrderedMonomial lm) coef

xPoly :: Monad m => SC.Series m (Polynomial Rational Two)
xPoly = do
  (series SC.>< series) >>- \(c, d) ->
    series >>- \p -> do
      guard $ (leadingMonomial p) < (OrderedMonomial (d :- 0 :- Nil))
      return $ appendLM c (d :- 0 :- Nil) p

yPoly :: Monad m => SC.Series m (Polynomial Rational Two)
yPoly = do
  (series SC.>< series) >>- \(c, d) ->
    series >>- \p -> do
      guard $ leadingMonomial p < OrderedMonomial (d :- 0 :- Nil)
      return $ appendLM c (0 :- d :- Nil) p

instance Monad m => Serial m (ZeroDimIdeal Two) where
  series = do
    (f, g, ideal) <- (,,) <$> xPoly <~> yPoly <~> series
    return $ ZeroDimIdeal $ f `addToIdeal` g `addToIdeal` ideal

-- * Instances for QuickCheck.
instance SingI n => Arbitrary (Monomial n) where
  arbitrary = arbVec

arbVec :: forall n. SingI n => Gen (Monomial n)
arbVec =  SV.unsafeFromList len . map abs <$> vectorOf (sNatToInt len) arbitrarySizedBoundedIntegral
    where
      len = sing :: SNat n

instance (IsOrder ord, Arbitrary (Monomial n)) => Arbitrary (OrderedMonomial ord n) where
  arbitrary = OrderedMonomial <$> arbitrary

instance (SingI n, IsOrder ord)
      => Arbitrary (OrderedPolynomial Rational ord n) where
  arbitrary = polynomial . M.fromList <$> listOf1 ((,) <$> arbitrary <*> arbitraryRational)

instance (Ord r, Noetherian r, Arbitrary r, Num r) => Arbitrary (Ideal r) where
  arbitrary = toIdeal . map QC.getNonZero . QC.getNonEmpty <$> arbitrary

instance (SingI n) => Arbitrary (ZeroDimIdeal n) where
  arbitrary = zeroDimG

instance (NA.Field r, Noetherian r, Reifies ideal (QIdeal r ord n)
         , Arbitrary (OrderedPolynomial r ord n)
         , IsMonomialOrder ord, SingI n, Eq r)
    => Arbitrary (Quotient r ord n ideal) where
  arbitrary = modIdeal <$> arbitrary

polyOfDim :: SNat n -> QC.Gen (Polynomial Rational n)
polyOfDim sn = case singInstance sn of SingInstance -> arbitrary

idealOfDim :: SNat n -> QC.Gen (Ideal (Polynomial Rational n))
idealOfDim sn = case singInstance sn of SingInstance -> arbitrary

quotOfDim :: (SingI n, Reifies ideal (QIdeal Rational Grevlex n))
          => Proxy ideal -> QC.Gen (Quotient Rational Grevlex n ideal)
quotOfDim _ = arbitrary

genLM :: forall n. SNat n -> QC.Gen [Polynomial Rational n]
genLM SZ = return []
genLM (SS n) = do
  fs <- map (shiftR sOne) <$> genLM n
  QC.NonNegative deg <- arbitrary
  coef <- arbitraryRational `suchThat` (/= 0)
  xf <- arbitrary :: QC.Gen (Polynomial Rational n)
  let xlm = OrderedMonomial $ fromList (sS n) [deg + 1]
      f = xf & unwrapped %~ M.insert xlm coef . M.filterWithKey (\k _ -> k < xlm)
  return $ f : fs

zeroDimOf :: SNat n -> QC.Gen (ZeroDimIdeal n)
zeroDimOf sn =
  case singInstance sn of
    SingInstance -> do
      fs <- genLM sn
      i0 <- arbitrary
      return $ ZeroDimIdeal $ toIdeal $ fs ++ i0

zeroDimG :: forall n. (SingI n) => QC.Gen (ZeroDimIdeal n)
zeroDimG = do
  fs <- genLM (sing :: SNat n)
  i0 <- arbitrary
  return $ ZeroDimIdeal $ toIdeal $ fs ++ i0

arbitraryRational :: QC.Gen Rational
arbitraryRational = do
  a <- QC.arbitrarySizedIntegral
  QC.NonZero b <- QC.arbitrarySizedIntegral
                    `suchThat` \(QC.NonZero b) -> gcd a b == 1 && b /= 0
  return $ a % b

isNonTrivial :: SingI n => ZeroDimIdeal n -> Bool
isNonTrivial (ZeroDimIdeal ideal) = reifyQuotient ideal $ maybe False ((>0).length) . standardMonomials'

data Equation = Equation { coefficients :: [[Rational]]
                         , answers      :: [Rational]
                         } deriving (Read, Show, Eq, Ord)

newtype MatrixCase a = MatrixCase { getMatrix :: [[a]]
                                  } deriving (Read, Show, Eq, Ord)

instance (Eq a, Num a, Arbitrary a) => Arbitrary (MatrixCase a) where
  arbitrary = flip suchThat (any (any (/= 0)) . getMatrix) $ sized $ \len -> do
    a <- resize len $ listOf1 arbitrary
    as <- listOf (vector $ length a)
    return $ MatrixCase $ a : as

instance Arbitrary Equation where
  arbitrary = do
    MatrixCase as <- arbitrary
    v <- vector $ length as
    return $ Equation as v

arbitrarySolvable :: Gen Equation
arbitrarySolvable = do
    MatrixCase as <- arbitrary
    v <- vector $ length $ head as
    return $ Equation as (V.toList $ M.getCol 1 $ M.fromLists as * M.colVector (V.fromList v))

liftSNat :: (forall n. SingI (n :: Nat) => Sing n -> Property) -> MonomorphicRep (Sing :: Nat -> *) -> Property
liftSNat f int =
  case M.promote int of
    Monomorphic snat ->
      case singInstance snat of
        SingInstance -> f snat

unaryPoly :: SNat n -> Ordinal n -> Gen (Polynomial Rational n)
unaryPoly arity mth = do
  f <- polyOfDim sOne
  case singInstance arity of
    SingInstance ->
      case ordToSNat' mth of
        CastedOrdinal sm ->
          case singInstance (sm %:+ sOne) of
            SingInstance ->
              case sAndPlusOne sm of
                Refl ->
                  case boolToClassLeq (sm %:+ sOne) arity of
                    Dict -> return $ scastPolynomial arity $ shiftR sm f

checkForArity :: [Int] -> (forall n. SingI (n :: Nat) => Sing n -> Property) -> Property
checkForArity as test = forAll (QC.elements as) $ liftSNat test

stdReduced :: (Eq r, Num r, SingI n, NA.Division r, Noetherian r, IsMonomialOrder order)
           => [OrderedPolynomial r order n] -> [OrderedPolynomial r order n]
stdReduced ps = sortBy (comparing leadingMonomial) $ map (\f -> injectCoeff (NA.recip $ leadingCoeff f) * f) ps
