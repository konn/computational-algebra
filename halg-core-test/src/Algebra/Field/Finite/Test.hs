{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs              #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction        #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
module Algebra.Field.Finite.Test
       (WrapFiniteField(..), arbitraryFiniteField, seriesFiniteField
       )where
import           Algebra.Field.Finite   (FiniteField (..))
import qualified Algebra.Field.Finite   as FF
import           Data.Coerce            (coerce)
import           Prelude
import           Test.QuickCheck        (Arbitrary (..), Gen)
import qualified Test.QuickCheck        as QC
import           Test.SmallCheck.Series (Serial (..), Series, generate)

newtype WrapFiniteField k = WrapFiniteField { runWrapFiniteField :: k }
                            deriving (Read, Show, Eq, Ord)

instance FiniteField k => Arbitrary (WrapFiniteField k) where
  arbitrary = coerce $ QC.elements (FF.elements ([] :: [k]))

arbitraryFiniteField :: FiniteField k => proxy k -> Gen k
arbitraryFiniteField _ = runWrapFiniteField <$> arbitrary

instance (Monad m, FiniteField k) => Serial m (WrapFiniteField k) where
  series = generate $ \n ->
    coerce $ take n $ FF.elements ([] :: [k])

seriesFiniteField :: (FiniteField k, Monad m) => proxy k -> Series m k
seriesFiniteField _ = runWrapFiniteField <$> series
