{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude, UndecidableInstances                    #-}
module Algebra.Ring.Ideal.Test () where
import           Algebra.Ring.Ideal     (Ideal, toIdeal)
import           AlgebraicPrelude       (DecidableZero, return, ($), (<$>))
import qualified Data.Foldable          as F
import           Test.QuickCheck        (Arbitrary (..))
import           Test.SmallCheck.Series (CoSerial (..), Serial (..),
                                         newtypeAlts, newtypeCons, (>>-))

instance (DecidableZero r, Arbitrary r) => Arbitrary (Ideal r) where
  arbitrary = toIdeal <$> arbitrary

instance (DecidableZero r, Serial m r) => Serial m (Ideal r) where
  series = newtypeCons toIdeal

instance (CoSerial m r) => CoSerial m (Ideal r) where
  coseries rs =
    newtypeAlts rs >>- \f ->
      return $ \l -> f (F.toList l)
