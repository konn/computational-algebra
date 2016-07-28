{-# LANGUAGE DataKinds, ExistentialQuantification, FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, GADTs, MultiParamTypeClasses        #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances             #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Algebra.Ring.Ideal ( Ideal(..), addToIdeal, toIdeal, appendIdeal
                          , generators, filterIdeal, mapIdeal, principalIdeal, isEmptyIdeal) where
import           Control.DeepSeq
import           Data.Function
import           Data.Ord
import           Data.Vector.Sized (Vector (..))
import qualified Data.Vector.Sized as V
import           Numeric.Algebra
import           Prelude           hiding (negate, subtract, (*), (+), (-))

data Ideal r = forall n. Ideal (V.Vector r n)

isEmptyIdeal :: Ideal t -> Bool
isEmptyIdeal (Ideal Nil) = True
isEmptyIdeal _ = False

instance Eq r => Eq (Ideal r) where
  (==) = (==) `on` generators

instance Ord r => Ord (Ideal r) where
  compare = comparing generators

instance Show r => Show (Ideal r) where
  show = show . generators

addToIdeal :: (Monoidal r, Eq r) => r -> Ideal r -> Ideal r
addToIdeal i (Ideal is)
    | i == zero = Ideal is
    | otherwise = Ideal (i :- is)

infixr `addToIdeal`

toIdeal :: (Eq r, Monoidal r) => [r] -> Ideal r
toIdeal = foldr addToIdeal (Ideal Nil)

appendIdeal :: Ideal r -> Ideal r -> Ideal r
appendIdeal (Ideal is) (Ideal js) = Ideal (is `V.append` js)

generators :: Ideal r -> [r]
generators (Ideal is) = V.toList is

filterIdeal :: (Eq r, Monoidal r) => (r -> Bool) -> Ideal r -> Ideal r
filterIdeal p (Ideal i) = V.foldr (\h -> if p h then addToIdeal h else id) (toIdeal []) i

principalIdeal :: r -> Ideal r
principalIdeal = Ideal . V.singleton

mapIdeal :: (r -> r') -> Ideal r -> Ideal r'
mapIdeal fun (Ideal xs) = Ideal $ V.map fun xs

instance NFData r => NFData (Ideal r) where
  rnf (Ideal is) = rnf is
