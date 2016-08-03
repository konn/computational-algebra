{-# LANGUAGE DataKinds, ExistentialQuantification, FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, GADTs, MultiParamTypeClasses        #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances             #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Algebra.Ring.Ideal ( Ideal(..), addToIdeal, toIdeal, appendIdeal
                          , generators, filterIdeal, mapIdeal, principalIdeal, isEmptyIdeal) where
import Algebra.Internal

import           Control.DeepSeq
import qualified Data.Foldable      as F
import           Data.Function
import           Data.Ord
import qualified Data.Sized.Builtin as S
import           Numeric.Algebra
import           Prelude            hiding (negate, subtract, (*), (+), (-))

data Ideal r = forall n. Ideal (Vector r n)

isEmptyIdeal :: Ideal t -> Bool
isEmptyIdeal (Ideal t) = S.null t

instance Eq r => Eq (Ideal r) where
  (==) = (==) `on` generators

instance Ord r => Ord (Ideal r) where
  compare = comparing generators

instance Show r => Show (Ideal r) where
  show = show . generators

addToIdeal :: (Monoidal r, Eq r) => r -> Ideal r -> Ideal r
addToIdeal i (Ideal is)
    | i == zero = Ideal is
    | otherwise = Ideal (S.cons i is)

infixr `addToIdeal`

toIdeal :: (Eq r, Monoidal r) => [r] -> Ideal r
toIdeal = foldr addToIdeal (Ideal S.empty)

appendIdeal :: Ideal r -> Ideal r -> Ideal r
appendIdeal (Ideal is) (Ideal js) = Ideal (is `S.append` js)

generators :: Ideal r -> [r]
generators (Ideal is) = S.toList is

filterIdeal :: (Eq r, Monoidal r) => (r -> Bool) -> Ideal r -> Ideal r
filterIdeal p (Ideal i) = F.foldr (\h -> if p h then addToIdeal h else id) (toIdeal []) i

principalIdeal :: r -> Ideal r
principalIdeal = Ideal . singleton

mapIdeal :: (r -> r') -> Ideal r -> Ideal r'
mapIdeal fun (Ideal xs) = Ideal $ S.map fun xs

instance NFData r => NFData (Ideal r) where
  rnf (Ideal is) = rnf is
