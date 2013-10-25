{-# LANGUAGE DataKinds, DeriveGeneric, FlexibleContexts, FlexibleInstances  #-}
{-# LANGUAGE MultiParamTypeClasses, ScopedTypeVariables, StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances                                           #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Instances (ZeroDimIdeal(..)) where
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial   hiding (Positive)
import           Control.Applicative
import           Control.Lens
import           Control.Monad
import           Data.Functor.Identity
import           Data.List                 (nub)
import qualified Data.Map                  as M
import           Data.Ratio
import           Data.Type.Natural         hiding (zero, (+))
import           Data.Vector.Sized         (Vector (..))
import qualified Data.Vector.Sized         as V
import qualified Numeric.Algebra           as NA
import           Test.QuickCheck
import qualified Test.QuickCheck           as QC
import           Test.QuickCheck.Instances ()
import           Test.SmallCheck.Series
import qualified Test.SmallCheck.Series    as SC

newtype ZeroDimIdeal = ZeroDimIdeal { getIdeal :: Ideal (Polynomial Rational Two)
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

instance Monad m => Serial m ZeroDimIdeal where
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

instance (Eq r, NoetherianRing r, SingRep n, IsOrder ord, Arbitrary r)
      => Arbitrary (OrderedPolynomial r ord n) where
  arbitrary = polynomial <$> arbitrary

instance (Ord r, NoetherianRing r, Arbitrary r, Num r) => Arbitrary (Ideal r) where
  arbitrary = toIdeal . map QC.getNonZero . getNonEmpty <$> arbitrary

instance Arbitrary ZeroDimIdeal where
  arbitrary = zeroDimG

zeroDimG :: QC.Gen ZeroDimIdeal
zeroDimG = do
  xlm <- (OrderedMonomial . (:- 0 :- Nil)) . QC.getNonNegative <$> arbitrary
  QC.NonZero xco <- arbitrary
  ylm <- (OrderedMonomial . (\a -> 0 :- a :- Nil)) . QC.getNonNegative <$> arbitrary
  QC.NonZero yco <- arbitrary
  xf <- arbitrary :: QC.Gen (Polynomial Rational Two)
  yg <- arbitrary :: QC.Gen (Polynomial Rational Two)
  let f = xf & unwrapped %~ M.insert xlm xco . M.filterWithKey (\k _ -> k < xlm)
      g = yg & unwrapped %~ M.insert ylm yco . M.filterWithKey (\k _ -> k < ylm)
  i0 <- arbitrary
  return $ ZeroDimIdeal $ toIdeal $ f : g : i0
