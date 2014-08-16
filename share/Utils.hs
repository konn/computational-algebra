{-# LANGUAGE CPP, DataKinds, DeriveGeneric, FlexibleContexts             #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving        #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses, OverlappingInstances #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, StandaloneDeriving         #-}
{-# LANGUAGE UndecidableInstances                                        #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Utils (ZeroDimIdeal(..), polyOfDim, arbitraryRational,homogPolyOfDim,arbVecOfSum,
              arbitrarySolvable, zeroDimOf, zeroDimG, unaryPoly, stdReduced,
              quotOfDim, isNonTrivial, Equation(..), liftSNat, checkForArity,
              MatrixCase(..), idealOfDim) where
import           Algebra.Internal
import           Algebra.Ring.Ideal
import           Algebra.Ring.Polynomial          hiding (Positive)
import           Algebra.Ring.Polynomial.Quotient
import           Control.Applicative
import           Control.Lens
import           Control.Monad
import           Data.Constraint
import           Data.List                        (sortBy)
import qualified Data.Map                         as M
import qualified Data.Matrix                      as M hiding (fromList)
import           Data.Ord
import           Data.Proxy
import           Data.Reflection                  hiding (Z)
import           Data.Type.Monomorphic
import qualified Data.Type.Monomorphic            as M
import           Data.Type.Natural
import           Data.Type.Ordinal
import qualified Data.Vector                      as V
import           Data.Vector.Sized                (Vector (..))
import qualified Data.Vector.Sized                as SV
import           Numeric.Algebra                  (DecidableZero)
import           Numeric.Algebra                  (Ring)
import qualified Numeric.Algebra                  as NA
import           Numeric.Domain.Euclidean         (Euclidean)
import           Numeric.Field.Fraction
import           Proof.Equational                 ((:=:) (..))
import           Test.QuickCheck
import qualified Test.QuickCheck                  as QC
import           Test.QuickCheck.Instances        ()
import qualified Test.QuickCheck.Modifiers        as QC
import           Test.SmallCheck.Series
import qualified Test.SmallCheck.Series           as SC
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
import Data.Type.Equality
#endif

newtype ZeroDimIdeal n = ZeroDimIdeal { getIdeal :: Ideal (Polynomial (Fraction Integer) n)
                                      } deriving (Show, Eq, Ord)

(%.) :: Euclidean a => a -> SC.Positive a -> Fraction a
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

instance (Eq r, DecidableZero r, Ring r, SingI n, IsMonomialOrder ord, Serial m r, Serial m (Monomial n))
          => Serial m (OrderedPolynomial r ord n) where
  series = cons2 (curry toPolynomial) \/ cons2 (NA.+)

instance (Num r, Ord r, Ring r, Serial m r) => Serial m (Ideal r) where
  series = newtypeCons toIdeal

appendLM :: (Fraction Integer) -> Monomial Two -> Polynomial (Fraction Integer) Two -> Polynomial (Fraction Integer) Two
appendLM coef lm = _Wrapped %~ M.insert (OrderedMonomial lm) coef

xPoly :: Monad m => SC.Series m (Polynomial (Fraction Integer) Two)
xPoly = do
  (series SC.>< series) >>- \(c, d) ->
    series >>- \p -> do
      guard $ (leadingMonomial p) < (OrderedMonomial (d :- 0 :- Nil))
      return $ appendLM c (d :- 0 :- Nil) p

yPoly :: Monad m => SC.Series m (Polynomial (Fraction Integer) Two)
yPoly = do
  (series SC.>< series) >>- \(c, d) ->
    series >>- \p -> do
      guard $ leadingMonomial p < OrderedMonomial (d :- 0 :- Nil)
      return $ appendLM c (0 :- d :- Nil) p

instance Monad m => Serial m (ZeroDimIdeal (S (S Z))) where
  series = do
    (f, g, ideal) <- (,,) <$> xPoly <~> yPoly <~> series
    return $ ZeroDimIdeal $ f `addToIdeal` g `addToIdeal` ideal

instance (Euclidean i, Integral i, Serial m i) => Serial m (Fraction i) where
  series = pairToRatio <$> series
    where
      pairToRatio (n, SC.Positive d) = n % d
instance (Euclidean i, Integral i, CoSerial m i) => CoSerial m (Fraction i) where
  coseries rs = (. ratioToPair) <$> coseries rs
    where
      ratioToPair r = (numerator r, denominator r)

arbVecOfSum :: SNat n -> Int -> Gen (Monomial n)
arbVecOfSum SZ      _ = fail "boo"
arbVecOfSum (SS SZ) n = return $ n :- Nil
arbVecOfSum (SS (SS sn)) n = do
  k <- QC.elements [0..abs n]
  (:-) k <$> arbVecOfSum (SS sn) (abs n - k)

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
      => Arbitrary (OrderedPolynomial (Fraction Integer) ord n) where
  arbitrary = polynomial . M.fromList <$> listOf1 ((,) <$> arbitrary <*> arbitraryRational)

instance (SingI n, IsOrder ord)
      => Arbitrary (HomogPoly (Fraction Integer) ord n) where
  arbitrary = do
    deg <- QC.elements [2, 3, 4]
    HomogPoly . polynomial . M.fromList <$>
      listOf1 ((,) <$> (OrderedMonomial <$> arbVecOfSum (sing :: SNat n) deg) <*> arbitraryRational)

instance (Ord r, Ring r, Arbitrary r, Num r) => Arbitrary (Ideal r) where
  arbitrary = toIdeal . map QC.getNonZero . QC.getNonEmpty <$> arbitrary

instance (SingI n) => Arbitrary (ZeroDimIdeal n) where
  arbitrary = zeroDimG

instance (DecidableZero r, NA.Field r, Ring r, Reifies ideal (QIdeal r ord n)
         , Arbitrary (OrderedPolynomial r ord n)
         , IsMonomialOrder ord, SingI n, Eq r)
    => Arbitrary (Quotient r ord n ideal) where
  arbitrary = modIdeal <$> arbitrary

polyOfDim :: SNat n -> QC.Gen (Polynomial (Fraction Integer) n)
polyOfDim sn = case singInstance sn of SingInstance -> arbitrary

newtype HomogPoly r ord n = HomogPoly { getHomogPoly :: OrderedPolynomial r ord n }

homogPolyOfDim :: SNat n -> QC.Gen (Polynomial (Fraction Integer) n)
homogPolyOfDim sn = case singInstance sn of SingInstance -> getHomogPoly <$> arbitrary

idealOfDim :: SNat n -> QC.Gen (Ideal (Polynomial (Fraction Integer) n))
idealOfDim sn = case singInstance sn of SingInstance -> arbitrary

quotOfDim :: (SingI n, Reifies ideal (QIdeal (Fraction Integer) Grevlex n))
          => Proxy ideal -> QC.Gen (Quotient (Fraction Integer) Grevlex n ideal)
quotOfDim _ = arbitrary

genLM :: forall n. SNat n -> QC.Gen [Polynomial (Fraction Integer) n]
genLM SZ = return []
genLM (SS n) = withSingI n $ do
  fs <- map (shiftR sOne) <$> genLM n
  QC.NonNegative deg <- arbitrary
  coef <- arbitraryRational `suchThat` (/= 0)
  xf <- arbitrary :: QC.Gen (Polynomial (Fraction Integer) n)
  let xlm = OrderedMonomial $ fromList (SS n) [deg + 1]
      f = xf & _Wrapped %~ M.insert xlm coef . M.filterWithKey (\k _ -> k < xlm)
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

arbitraryRational :: QC.Gen (Fraction Integer)
arbitraryRational = do
  a <- QC.arbitrarySizedIntegral
  b <- QC.arbitrarySizedIntegral
                    `suchThat` \b -> gcd a b == 1 && b /= 0
  return $ a % abs b

isNonTrivial :: SingI n => ZeroDimIdeal n -> Bool
isNonTrivial (ZeroDimIdeal ideal) = reifyQuotient ideal $ maybe False ((>0).length) . standardMonomials'

data Equation = Equation { coefficients :: [[(Fraction Integer)]]
                         , answers      :: [(Fraction Integer)]
                         } deriving (Show, Eq, Ord)

newtype MatrixCase a = MatrixCase { getMatrix :: [[a]]
                                  } deriving (Read, Show, Eq, Ord)

instance Arbitrary (Fraction Integer) where
  arbitrary = arbitraryRational

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
liftSNat f i =
  case M.promote i of
    Monomorphic sn ->
      case singInstance sn of
        SingInstance -> f sn

unaryPoly :: SNat n -> Ordinal n -> Gen (Polynomial (Fraction Integer) n)
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

stdReduced :: (DecidableZero r, Eq r, Num r, SingI n, NA.Division r, Ring r, IsMonomialOrder order)
           => [OrderedPolynomial r order n] -> [OrderedPolynomial r order n]
stdReduced ps = sortBy (comparing leadingMonomial) $ map (\f -> injectCoeff (NA.recip $ leadingCoeff f) * f) ps
