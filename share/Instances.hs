{-# LANGUAGE DataKinds, DeriveGeneric, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, MultiParamTypeClasses      #-}
{-# LANGUAGE OverlappingInstances, ScopedTypeVariables, StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances, ViewPatterns                            #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Instances (ZeroDimIdeal(..), polyOfDim, arbitraryRational) where
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial   hiding (Positive)
import           Control.Applicative
import           Control.DeepSeq
import           Control.Lens
import           Control.Monad
import           Data.Functor.Identity
import qualified Data.Map                  as M
import           Data.Ratio
import           Data.Type.Natural
import           Data.Vector.Sized         (Vector (..))
import qualified Data.Vector.Sized         as V
import qualified Numeric.Algebra           as NA
import           Test.QuickCheck
import qualified Test.QuickCheck           as QC
import           Test.QuickCheck.Instances ()
import           Test.SmallCheck.Series
import qualified Test.SmallCheck.Series    as SC

newtype ZeroDimIdeal n = ZeroDimIdeal { getIdeal :: Ideal (Polynomial Rational n)
                                      } deriving (Show, Eq, Ord)

(%.) :: Integral a => a -> SC.Positive a -> Ratio a
a %. SC.Positive b = a % b

-- * Instances for SmallCheck.
instance (Integral a, Ord a, Serial m a) => Serial m (Ratio a) where
  series = cons2 (%.)

instance Monad m => Serial m (Monomial Z) where
  series = cons0 Nil

instance (Serial m (Monomial n)) => Serial m (Monomial (S n)) where
  series = (:-) <$> (SC.getNonNegative <$> series) <*> series

instance (Ord k, Serial m k, Serial m v) => Serial m (M.Map k v) where
  series = M.fromList <$> series

instance Serial m (Monomial n) => Serial m (OrderedMonomial ord n) where
  series = newtypeCons OrderedMonomial

instance (Eq r, NoetherianRing r, SingRep n, IsMonomialOrder ord, Serial m r, Serial m (Monomial n))
          => Serial m (OrderedPolynomial r ord n) where
  series = cons2 (curry toPolynomial) \/ cons2 (NA.+)

type Ser = SC.Series Identity

instance (Num r, Ord r, NoetherianRing r, Serial m r) => Serial m (Ideal r) where
  series = newtypeCons toIdeal

appendLM :: Rational -> Monomial Two -> Polynomial Rational Two -> Polynomial Rational Two
appendLM coeff lm = unwrapped %~ M.insert (OrderedMonomial lm) coeff

xPoly :: Monad m => SC.Series m (Polynomial Rational Two)
xPoly = do
  (series SC.>< series) >>- \(c, d) ->
    series >>- \p -> do
      guard $ OrderedMonomial (leadingMonomial p) < (OrderedMonomial (d :- 0 :- Nil) :: OrderedMonomial Grevlex Two)
      return $ appendLM c (d :- 0 :- Nil) p

yPoly :: Monad m => SC.Series m (Polynomial Rational Two)
yPoly = do
  (series SC.>< series) >>- \(c, d) ->
    series >>- \p -> do
      guard $ OrderedMonomial (leadingMonomial p) < (OrderedMonomial (d :- 0 :- Nil) :: OrderedMonomial Grevlex Two)
      return $ appendLM c (0 :- d :- Nil) p

instance Monad m => Serial m (ZeroDimIdeal Two) where
  series = do
    (f, g, ideal) <- (,,) <$> xPoly <~> yPoly <~> series
    return $ ZeroDimIdeal $ f `addToIdeal` g `addToIdeal` ideal

-- * Instances for QuickCheck.
instance SingRep n => Arbitrary (Monomial n) where
  arbitrary = arbVec

arbVec :: forall n. SingRep n => Gen (Monomial n)
arbVec = V.unsafeFromList len . map QC.getNonNegative <$> vector (sNatToInt len)
    where
      len = sing :: SNat n

instance (IsOrder ord, Arbitrary (Monomial n)) => Arbitrary (OrderedMonomial ord n) where
  arbitrary = OrderedMonomial <$> arbitrary

instance (SingRep n, IsOrder ord)
      => Arbitrary (OrderedPolynomial Rational ord n) where
  arbitrary = polynomial . M.fromList <$> listOf1 ((,) <$> arbitrary <*> arbitraryRational)

instance (Ord r, NoetherianRing r, Arbitrary r, Num r) => Arbitrary (Ideal r) where
  arbitrary = toIdeal . map QC.getNonZero . getNonEmpty <$> arbitrary

instance (SingRep n) => Arbitrary (ZeroDimIdeal n) where
  arbitrary = zeroDimG

polyOfDim :: SingRep n => SNat n -> QC.Gen (Polynomial Rational n)
polyOfDim _ = arbitrary

genLM :: forall n. SNat n -> QC.Gen [Polynomial Rational n]
genLM SZ = return []
genLM (SS n) = do
  fs <- map (shiftR sOne) <$> genLM n
  QC.NonNegative deg <- arbitrary
  coef <- arbitraryRational `suchThat` (/= 0)
  xf <- arbitrary :: QC.Gen (Polynomial Rational n)
  let xlm = OrderedMonomial $ fromList (sS n) [deg]
      f = xf & unwrapped %~ M.insert xlm coef . M.filterWithKey (\k _ -> k < xlm)
  return $ f : fs

zeroDimG :: forall n. (SingRep n) => QC.Gen (ZeroDimIdeal n)
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

instance NFData (V.Vector a Z) where
  rnf V.Nil = V.Nil `seq` ()

instance (NFData a, NFData (V.Vector a n)) => NFData (V.Vector a (S n)) where
  rnf (x :- ys) = rnf x `seq` rnf ys `seq` ()

instance (NFData (Monomial n)) => NFData (OrderedMonomial ord n) where
  rnf (OrderedMonomial m) = rnf m `seq` ()

instance (NFData (Monomial n), NFData r) => NFData (OrderedPolynomial r ord n) where
  rnf (getTerms -> dic) = rnf dic

instance NFData r => NFData (Ideal r) where
  rnf (generators -> is) = rnf is
