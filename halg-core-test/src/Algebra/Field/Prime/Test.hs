{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction, PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, UndecidableInstances     #-}
module Algebra.Field.Prime.Test where
import Algebra.Field.Finite.Test

import Algebra.Field.Prime    (F, IsPrimeChar, charInfo, modNat)
import Data.Proxy
import Prelude                (Maybe (..), Monad, fromIntegral, (-), (<$>))
import Test.QuickCheck        (Arbitrary (..), resize)
import Test.SmallCheck.Series (Serial (..))

instance IsPrimeChar p => Arbitrary (F p) where
  arbitrary = modNat <$>
    resize (fromIntegral (charInfo (Proxy :: Proxy p)) - 1) arbitrary

instance (Monad m, IsPrimeChar p) => Serial m (F p) where
  series = seriesFiniteField (Nothing :: Maybe (F p))
