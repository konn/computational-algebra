{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction, PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, UndecidableInstances     #-}
module Algebra.Field.Prime.Test where
import Algebra.Field.Finite.Test

import Algebra.Field.Prime    (F, IsPrimeChar)
import Prelude                (Maybe (..), Monad)
import Test.QuickCheck        (Arbitrary (..))
import Test.SmallCheck.Series (Serial (..))

instance IsPrimeChar p => Arbitrary (F p) where
  arbitrary = arbitraryFiniteField (Nothing :: Maybe (F p))

instance (Monad m, IsPrimeChar p) => Serial m (F p) where
  series = seriesFiniteField (Nothing :: Maybe (F p))
