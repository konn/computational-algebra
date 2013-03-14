{-# LANGUAGE DataKinds, ExistentialQuantification, FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances                                           #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Algebra.Ring.Noetherian ( NoetherianRing, Ideal(..), addToIdeal, toIdeal, appendIdeal
                               , generators, filterIdeal, mapIdeal, principalIdeal) where
import Algebra.Internal
import Data.Complex
import Data.Function
import Data.Ord
import Data.Ratio
import Data.Type.Monomorphic
import Numeric.Algebra
import Prelude               hiding ((*), (+))

class (Commutative r, Ring r) => NoetherianRing r where

instance NoetherianRing Int where

instance NoetherianRing Integer where

{-
instance NoetherianRing Double where

instance NoetherianRing Float where
-}

instance (Commutative (Complex r), Ring (Complex r)) => NoetherianRing (Complex r) where


data Ideal r = forall n. Ideal (Vector r n)

instance Eq r => Eq (Ideal r) where
  (==) = (==) `on` generators

instance Ord r => Ord (Ideal r) where
  compare = comparing generators

instance Show r => Show (Ideal r) where
  show = show . generators

addToIdeal :: r -> Ideal r -> Ideal r
addToIdeal i (Ideal is) = Ideal (i :- is)

toIdeal :: NoetherianRing r => [r] -> Ideal r
toIdeal = foldr addToIdeal (Ideal Nil)

appendIdeal :: Ideal r -> Ideal r -> Ideal r
appendIdeal (Ideal is) (Ideal js) = Ideal (is `appendV` js)

generators :: Ideal r -> [r]
generators (Ideal is) = toList is

filterIdeal :: NoetherianRing r => (r -> Bool) -> Ideal r -> Ideal r
filterIdeal p (Ideal i) = foldrV (\h -> if p h then addToIdeal h else id) (toIdeal []) i

principalIdeal :: r -> Ideal r
principalIdeal = Ideal . singletonV

mapIdeal :: (r -> r') -> Ideal r -> Ideal r'
mapIdeal fun (Ideal xs) = Ideal $ mapV fun xs
