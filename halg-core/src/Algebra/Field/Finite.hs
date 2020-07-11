{-# LANGUAGE DataKinds, DerivingStrategies, FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, PolyKinds #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, TypeApplications   #-}
{-# LANGUAGE TypeFamilies, UndecidableInstances                  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Algebra.Field.Finite
  ( FiniteField(..), order,
    ViaElements(..)
  ) where
import           Control.Monad.Random              (Random (..), uniform)
import           Control.Monad.Trans.Random.Strict (runRand)
import           Data.Coerce                       (coerce)
import           Data.Proxy                        (Proxy (Proxy))
import           Numeric.Algebra                   (Field, Natural, char)
import           Numeric.Rig.Characteristic        (Characteristic)
import           Prelude                           (($))
import qualified Prelude                           as P

-- | Abstract class for finite fields.
class (Field k, Characteristic k) => FiniteField k where
  power :: proxy k -> Natural
  elements :: proxy k -> [k]

order :: FiniteField k => proxy k -> Natural
order p = char p P.^ power p
{-# INLINE order #-}

newtype ViaElements k = ViaElements { runViaElements :: k }

instance FiniteField k => Random (ViaElements k) where
  random = runRand
    $ uniform $ coerce @_ @[ViaElements k]
    $ elements (Proxy :: Proxy k)
  {-# INLINE random #-}
  randomR = P.error "randomR: general finite fields not supported"
  {-# INLINE randomR #-}
