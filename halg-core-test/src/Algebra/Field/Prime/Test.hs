{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction, PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, UndecidableInstances     #-}
module Algebra.Field.Prime.Test where
import Algebra.Field.Finite.Test

import Algebra.Field.Prime    (F)
import Data.Reflection        (Reifies)
import Prelude                (Integer, Maybe (..), Monad)
import Test.QuickCheck        (Arbitrary (..))
import Test.SmallCheck.Series (Serial (..))

instance Reifies p Integer => Arbitrary (F p) where
  arbitrary = arbitraryFiniteField (Nothing :: Maybe (F p))

instance (Monad m, Reifies p Integer) => Serial m (F p) where
  series = seriesFiniteField (Nothing :: Maybe (F p))
