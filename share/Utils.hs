{-# LANGUAGE CPP, DataKinds, DeriveGeneric, FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving   #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses, RankNTypes      #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TypeOperators #-}
{-# LANGUAGE UndecidableInstances                                   #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Utils (ZeroDimIdeal(..), polyOfDim, arbitraryRational,homogPolyOfDim,arbVecOfSum,
              arbitrarySolvable, zeroDimOf, zeroDimG, unaryPoly, stdReduced,
              quotOfDim, isNonTrivial, Equation(..), liftSNat, checkForArity,
              MatrixCase(..), idealOfDim) where
import           Algebra.Field.Finite
import qualified Algebra.Field.Finite               as F
import           Algebra.Internal
import           Algebra.Ring.Ideal
import           Algebra.Ring.Polynomial            hiding (Positive)
import           Algebra.Ring.Polynomial.Quotient
import           Algebra.Ring.Polynomial.Univariate
import           Control.Lens                       hiding ((:<))
import           Control.Monad
import           Data.List                          (sortBy)
import qualified Data.List                          as L
import qualified Data.Map                           as M
import qualified Data.Matrix                        as M hiding (fromList)
import           Data.Ord
import           Data.Reflection
import           Data.Sized.Builtin                 hiding (head, length, map,
                                                     sortBy, (++))
import qualified Data.Sized.Builtin                 as SV
import           Data.Type.Monomorphic
import qualified Data.Type.Monomorphic              as M
import qualified Data.Vector                        as V
import           Numeric.Algebra                    (DecidableZero)
import           Numeric.Algebra                    (Ring)
import qualified Numeric.Algebra                    as NA
import           Numeric.Domain.Euclidean           (Euclidean)
import           Numeric.Field.Fraction
import           Test.QuickCheck
import qualified Test.QuickCheck                    as QC
import           Test.QuickCheck.Instances          ()
import           Test.SmallCheck.Series
import qualified Test.SmallCheck.Series             as SC

newtype ZeroDimIdeal n = ZeroDimIdeal { getIdeal :: Ideal (Polynomial (Fraction Integer) n)
                                      } deriving (Show, Eq, Ord)

(%.) :: Euclidean a => a -> SC.Positive a -> Fraction a
a %. SC.Positive b = a % b

-- * Instances for SmallCheck.
instance (KnownNat n, Monad m) => Serial m (Monomial n) where
  series =
    case zeroOrSucc (sing :: SNat n) of
      IsZero   -> cons0 SV.empty
      IsSucc n -> withKnownNat n $ SV.cons <$> (SC.getNonNegative <$> series) <*> series

instance (Ord k, Serial m k, Serial m v) => Serial m (M.Map k v) where
  series = M.fromList <$> series

instance KnownNat n => Arbitrary (F n) where
  arbitrary = QC.elements (F.elements Proxy)

instance (Monad m, Serial m (Monomial n)) => Serial m (OrderedMonomial ord n) where
  series = newtypeCons OrderedMonomial

instance (Eq r, CoeffRing r, KnownNat n, IsMonomialOrder n ord,
          Serial m r, Serial m (Monomial n))
          => Serial m (OrderedPolynomial r ord n) where
  series = cons2 (curry toPolynomial) \/ cons2 (NA.+)

instance (Ord r, Ring r, Serial m r) => Serial m (Ideal r) where
  series = newtypeCons toIdeal

instance (CoeffRing r, Arbitrary r) => Arbitrary (Unipol r) where
  arbitrary = fromCoeffVec <$> QC.listOf QC.arbitrary
    where
      fromCoeffVec = polynomial' . M.fromList . L.zip [singleton n | n <- [0..]]

genUnipol :: (CoeffRing r, Arbitrary r) => Int -> IO (Unipol r)
genUnipol len = QC.generate $ fromCoeffVec <$> QC.vectorOf len QC.arbitrary
    where
      fromCoeffVec = polynomial' . M.fromList . L.zip [singleton n | n <- [0..]]

appendLM :: (Fraction Integer) -> Monomial 2 -> Polynomial (Fraction Integer) 2 -> Polynomial (Fraction Integer) 2
appendLM coef lm = _Wrapped %~ M.insert (OrderedMonomial lm) coef

xPoly :: Monad m => SC.Series m (Polynomial (Fraction Integer) 2)
xPoly = do
  (series SC.>< series) >>- \(c, d) ->
    series >>- \p -> do
      guard $ (leadingMonomial p) < (OrderedMonomial (d :< 0 :< NilL))
      return $ appendLM c (d :< 0 :< NilL) p

yPoly :: Monad m => SC.Series m (Polynomial (Fraction Integer) 2)
yPoly = do
  (series SC.>< series) >>- \(c, d) ->
    series >>- \p -> do
      guard $ leadingMonomial p < OrderedMonomial (d :< 0 :< NilL)
      return $ appendLM c (0 :< d :< NilL) p

instance Monad m => Serial m (ZeroDimIdeal 2) where
  series = do
    (f, g, ideal) <- (,,) <$> xPoly <~> yPoly <~> series
    return $ ZeroDimIdeal $ f `addToIdeal` g `addToIdeal` ideal

instance (Euclidean i, Integral i, Serial m i) => Serial m (Fraction i) where
  series = pairToRatio <$> series
    where
      pairToRatio (n, SC.Positive d) = n % d
instance (CoSerial m i) => CoSerial m (Fraction i) where
  coseries rs = (. ratioToPair) <$> coseries rs
    where
      ratioToPair r = (numerator r, denominator r)

arbVecOfSum :: SNat n -> Int -> Gen (Monomial n)
arbVecOfSum n k =
  case zeroOrSucc n of
    IsZero | k == 0 -> QC.elements [SV.empty]
           | otherwise -> fail "Empty list with positive sum"
    IsSucc m -> withKnownNat m $ do
      l <- QC.elements [0..abs k]
      (l :<) <$> arbVecOfSum m (abs k - l)

-- * Instances for QuickCheck.
instance KnownNat n => Arbitrary (Monomial n) where
  arbitrary = arbVec

arbVec :: forall n. KnownNat n => Gen (Monomial n)
arbVec =  SV.unsafeFromList len . map abs <$> vectorOf (sNatToInt len) arbitrarySizedBoundedIntegral
    where
      len = sing :: SNat n

instance (Arbitrary (Monomial n)) => Arbitrary (OrderedMonomial ord n) where
  arbitrary = OrderedMonomial <$> arbitrary

instance (KnownNat n, IsMonomialOrder n ord)
      => Arbitrary (OrderedPolynomial (Fraction Integer) ord n) where
  arbitrary = polynomial . M.fromList <$> listOf1 ((,) <$> arbitrary <*> arbitraryRational)

instance (KnownNat n, IsMonomialOrder n ord)
      => Arbitrary (HomogPoly (Fraction Integer) ord n) where
  arbitrary = do
    deg <- QC.elements [2, 3, 4]
    HomogPoly . polynomial . M.fromList <$>
      listOf1 ((,) <$> (OrderedMonomial <$> arbVecOfSum (sing :: SNat n) deg) <*> arbitraryRational)

instance (Num r, Ord r, Ring r, Arbitrary r) => Arbitrary (Ideal r) where
  arbitrary = toIdeal . map QC.getNonZero . QC.getNonEmpty <$> arbitrary

instance (KnownNat n) => Arbitrary (ZeroDimIdeal n) where
  arbitrary = zeroDimG

instance (DecidableZero r, NA.Field r, Ring r, Reifies ideal (QIdeal r ord n)
         , Arbitrary (OrderedPolynomial r ord n)
         , IsMonomialOrder n ord, KnownNat n, Eq r)
    => Arbitrary (Quotient r ord n ideal) where
  arbitrary = modIdeal <$> arbitrary

polyOfDim :: SNat n -> QC.Gen (Polynomial (Fraction Integer) n)
polyOfDim sn = withKnownNat sn  arbitrary

newtype HomogPoly r ord n = HomogPoly { getHomogPoly :: OrderedPolynomial r ord n }

homogPolyOfDim :: SNat n -> QC.Gen (Polynomial (Fraction Integer) n)
homogPolyOfDim sn = withKnownNat sn $ getHomogPoly <$> arbitrary

idealOfDim :: SNat n -> QC.Gen (Ideal (Polynomial (Fraction Integer) n))
idealOfDim sn = withKnownNat sn arbitrary

quotOfDim :: (KnownNat n, Reifies ideal (QIdeal (Fraction Integer) Grevlex n))
          => Proxy ideal -> QC.Gen (Quotient (Fraction Integer) Grevlex n ideal)
quotOfDim _ = arbitrary

genLM :: forall n. SNat n -> QC.Gen [Polynomial (Fraction Integer) n]
genLM m = withKnownNat m $ case zeroOrSucc m of
  IsZero -> return []
  IsSucc n -> withKnownNat n $ do
    fs <- map (coerce (plusComm sOne n) . shiftR sOne) <$> genLM n
    QC.NonNegative deg <- arbitrary
    coef <- arbitraryRational `suchThat` (/= 0)
    xf <- arbitrary :: QC.Gen (Polynomial (Fraction Integer) n)
    let xlm = OrderedMonomial $ fromListWithDefault (sSucc n) 0 [deg + 1]
        f = xf & _Wrapped %~ M.insert xlm coef . M.filterWithKey (\k _ -> k < xlm)
    return $ f : fs

zeroDimOf :: SNat n -> QC.Gen (ZeroDimIdeal n)
zeroDimOf sn = withKnownNat sn $ do
  fs <- genLM sn
  i0 <- arbitrary
  return $ ZeroDimIdeal $ toIdeal $ fs ++ i0

zeroDimG :: forall n. (KnownNat n) => QC.Gen (ZeroDimIdeal n)
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

isNonTrivial :: KnownNat n => ZeroDimIdeal n -> Bool
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

liftSNat :: (forall n. KnownNat (n :: Nat) => Sing n -> Property) -> Integer -> Property
liftSNat f i =
  case M.promote i of
    Monomorphic sn -> withKnownNat sn $ f sn

unaryPoly :: SNat n -> Ordinal n -> Gen (Polynomial (Fraction Integer) n)
unaryPoly ar (OLt sm) = do
  f <- polyOfDim sOne
  withKnownNat ar $ withKnownNat (sm %:+ sOne) $
    return $ scastPolynomial ar $ shiftR sm f

checkForArity :: [Integer] -> (forall n. KnownNat (n :: Nat) => Sing n -> Property) -> Property
checkForArity as test = forAll (QC.elements as) $ liftSNat test

stdReduced :: (CoeffRing r, KnownNat n, NA.Field r, IsMonomialOrder n order)
           => [OrderedPolynomial r order n] -> [OrderedPolynomial r order n]
stdReduced ps = sortBy (comparing leadingMonomial) $
                map (\f -> injectCoeff (NA.recip $ leadingCoeff f) NA.* f) ps
