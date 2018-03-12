{-# LANGUAGE DataKinds, DeriveTraversable, ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses       #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances              #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Algebra.Ring.Ideal ( Ideal(..), addToIdeal, toIdeal, appendIdeal
                          , generators, filterIdeal, mapIdeal
                          , principalIdeal, isEmptyIdeal
                          , someSizedIdeal
                          ) where
import Algebra.Internal (Nat)

import           AlgebraicPrelude
import           Control.DeepSeq
import qualified Data.Foldable      as F
import           Data.Sequence      (Seq, (<|), (><))
import qualified Data.Sequence      as Seq
import qualified Data.Sized.Builtin as S
import qualified Data.Vector        as V

newtype Ideal r = Ideal (Seq r)
                  deriving (Hashable, NFData,
                            Foldable, Traversable, Functor)

isEmptyIdeal :: Ideal t -> Bool
isEmptyIdeal (Ideal t) = Seq.null t

instance Show r => Show (Ideal r) where
  showsPrec d = showsPrec d . generators

addToIdeal :: (Monoidal r, DecidableZero r) => r -> Ideal r -> Ideal r
addToIdeal i (Ideal is)
    | isZero i = Ideal is
    | otherwise = Ideal (i <| is)

infixr `addToIdeal`

toIdeal :: (DecidableZero r, Monoidal r) => [r] -> Ideal r
toIdeal = foldr addToIdeal (Ideal Seq.empty)

appendIdeal :: Ideal r -> Ideal r -> Ideal r
appendIdeal (Ideal is) (Ideal js) = Ideal (is >< js)

generators :: Ideal r -> [r]
generators (Ideal is) = F.toList is

filterIdeal :: (r -> Bool) -> Ideal r -> Ideal r
filterIdeal p (Ideal i) = Ideal $ Seq.filter p i

principalIdeal :: r -> Ideal r
principalIdeal = Ideal . Seq.singleton

mapIdeal :: (r -> r') -> Ideal r -> Ideal r'
mapIdeal fun (Ideal xs) = Ideal $ fmap fun xs
{-# INLINE [1] mapIdeal #-}

someSizedIdeal :: Ideal r -> S.SomeSized Vector Nat r
someSizedIdeal (Ideal xs) =
  S.toSomeSized $ V.fromList $ F.toList xs
