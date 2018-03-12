{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses, PolyKinds, RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Algebra.Field.Finite (FiniteField(..), order) where
import           Numeric.Algebra            (Field, Natural, char)
import           Numeric.Rig.Characteristic (Characteristic)
import qualified Prelude                    as P

-- | Abstract class for finite fields.
class (Field k, Characteristic k) => FiniteField k where
  power :: proxy k -> Natural
  elements :: proxy k -> [k]

order :: FiniteField k => proxy k -> Natural
order p = char p P.^ power p
{-# INLINE order #-}
