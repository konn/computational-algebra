{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude, UndecidableInstances                    #-}
module Algebra.Field.Fraction.Test (arbitraryRational) where
import           AlgebraicPrelude
import           Test.QuickCheck        (Arbitrary (..), Gen,
                                         arbitrarySizedIntegral, suchThat)
import           Test.SmallCheck.Series (CoSerial (..), Serial (..))
import qualified Test.SmallCheck.Series as SC

arbitraryRational :: Gen (Fraction Integer)
arbitraryRational = do
  a <- arbitrarySizedIntegral
  b <- arbitrarySizedIntegral `suchThat` \b -> gcd a b == 1 && b /= 0
  return $ a % abs b

instance (GCDDomain r, Eq r, Arbitrary r) => Arbitrary (Fraction r) where
  arbitrary = do
    a <- arbitrary
    b <- arbitrary `suchThat` \b -> gcd a b == one && not (isZero b)
    return $ a % b

instance {-# OVERLAPPING #-} Arbitrary (Fraction Integer) where
  arbitrary = arbitraryRational

instance (Euclidean i, Integral i, Serial m i) => Serial m (Fraction i) where
  series = pairToRatio <$> series
    where
      pairToRatio (n, SC.Positive d) = n % d

instance (CoSerial m i) => CoSerial m (Fraction i) where
  coseries rs = (. ratioToPair) <$> coseries rs
    where
      ratioToPair r = (numerator r, denominator r)
