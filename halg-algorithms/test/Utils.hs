{-# LANGUAGE CPP, DataKinds, FlexibleContexts, FlexibleInstances, GADTs   #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, TypeOperators             #-}
{-# LANGUAGE UndecidableInstances                                         #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Utils (module Utils, module Algebra.TestUtils) where
import           Algebra.Internal
import           Algebra.Ring.Ideal
import           Algebra.Ring.Polynomial            hiding (Positive)
import           Algebra.Ring.Polynomial.Quotient
import           Algebra.Ring.Polynomial.Univariate
import           Algebra.TestUtils
import           Control.Monad
import           Data.List                          (sortOn)
import qualified Data.List                          as L
import qualified Data.Map                           as M
import qualified Data.Matrix                        as M hiding (fromList)
import           Data.Ord
import           Data.Reflection
import           Data.Sized.Builtin                 (fromListWithDefault)
import qualified Data.Vector                        as V
import qualified Numeric.Algebra                    as NA
import           Numeric.Field.Fraction
import           Prelude
import           Test.QuickCheck
import qualified Test.QuickCheck                    as QC
import           Test.QuickCheck.Instances          ()
import           Test.SmallCheck.Series
import qualified Test.SmallCheck.Series             as SC

newtype ZeroDimIdeal n = ZeroDimIdeal { getIdeal :: Ideal (Polynomial (Fraction Integer) n)
                                      } deriving (Show)

genUnipol :: (CoeffRing r, Arbitrary r) => Int -> IO (Unipol r)
genUnipol len = QC.generate $ fromCoeffVec <$> QC.vectorOf len QC.arbitrary
    where
      fromCoeffVec = polynomial' . M.fromList . L.zip [singleton n | n <- [0..]]

appendLM :: Fraction Integer -> Monomial 2 -> Polynomial (Fraction Integer) 2 -> Polynomial (Fraction Integer) 2
appendLM coef lm f =
  let c = coeff' lm f
  in f + toPolynomial (coef - c, OrderedMonomial lm)

xPoly :: Monad m => SC.Series m (Polynomial (Fraction Integer) 2)
xPoly =
  (series SC.>< series) >>- \(c, d) ->
    series >>- \p -> do
      guard $ leadingMonomial p < OrderedMonomial (d :< 0 :< Nil)
      return $ appendLM c (d :< 0 :< Nil) p

yPoly :: Monad m => SC.Series m (Polynomial (Fraction Integer) 2)
yPoly =
  (series SC.>< series) >>- \(c, d) ->
    series >>- \p -> do
      guard $ leadingMonomial p < OrderedMonomial (d :< 0 :< Nil)
      return $ appendLM c (0 :< d :< Nil) p

instance Monad m => Serial m (ZeroDimIdeal 2) where
  series = do
    (f, g, ideal) <- (,,) <$> xPoly <~> yPoly <~> series
    return $ ZeroDimIdeal $ f `addToIdeal` g `addToIdeal` ideal

instance (KnownNat n) => Arbitrary (ZeroDimIdeal n) where
  arbitrary = zeroDimG

instance (NA.Field (Coefficient poly),
          IsOrderedPolynomial poly,
          Reifies ideal (QIdeal poly),
          Arbitrary poly)
    => Arbitrary (Quotient poly ideal) where
  arbitrary = modIdeal <$> arbitrary

genLM :: forall n. SNat n -> QC.Gen [Polynomial (Fraction Integer) n]
genLM m = withKnownNat m $ case zeroOrSucc m of
  IsZero -> return []
  IsSucc n -> withKnownNat n $ do
    fs <- map (coerce (plusComm sOne n) . shiftR sOne) <$> genLM n
    QC.NonNegative deg <- arbitrary
    coef <- arbitraryRational `suchThat` (/= 0)
    xf <- arbitrary :: QC.Gen (Polynomial (Fraction Integer) n)
    let xlm = OrderedMonomial $ fromListWithDefault (sSucc n) 0 [deg + 1]
        f = polynomial $ M.insert xlm coef . M.filterWithKey (\k _ -> k < xlm) $ terms xf
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

isNonTrivial :: KnownNat n => ZeroDimIdeal n -> Bool
isNonTrivial (ZeroDimIdeal ideal) = reifyQuotient ideal $ maybe False (not . null) . standardMonomials'

data Equation = Equation { coefficients :: [[Fraction Integer]]
                         , answers      :: [Fraction Integer]
                         } deriving (Show, Eq, Ord)

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

unaryPoly :: SNat n -> Ordinal n -> Gen (Polynomial (Fraction Integer) n)
unaryPoly ar (OLt sm) = do
  f <- polynomialOfArity sOne
  withKnownNat ar $ withKnownNat (sm %+ sOne) $
    return $ scastPolynomial ar $ shiftR sm f

stdReduced :: (CoeffRing r, KnownNat n, NA.Field r, IsMonomialOrder n order)
           => [OrderedPolynomial r order n] -> [OrderedPolynomial r order n]
stdReduced ps = sortOn leadingMonomial $
                map (\f -> injectCoeff (NA.recip $ leadingCoeff f) NA.* f) ps

instance (Arbitrary k, KnownNat n, CoeffRing k, IsMonomialOrder n o)
      => Arbitrary (OrderedPolynomial k o n) where
  arbitrary = arbitraryPolynomial

instance (Arbitrary k, CoeffRing k)
      => Arbitrary (Unipol k) where
  arbitrary = arbitraryPolynomial

idealOfArity :: (KnownNat n, Eq k, NA.Field k, Arbitrary k)
             => SNat n -> Gen (Ideal (Polynomial k n))
idealOfArity sn = withKnownNat sn arbitrary


polynomialOfArity :: (KnownNat n, Eq k, NA.Field k, Arbitrary k)
                  => SNat n -> Gen (Polynomial k n)
polynomialOfArity sn = withKnownNat sn (runWrapPolynomial <$> arbitrary)

instance (Monad m, Serial m k, CoeffRing k, KnownNat n, IsMonomialOrder n ord)
      =>  Serial m (OrderedPolynomial k ord n) where
  series = seriesPolynomial



