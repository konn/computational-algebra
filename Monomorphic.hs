{-# LANGUAGE DataKinds, ExistentialQuantification, FlexibleContexts, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, TypeFamilies, TypeOperators            #-}
{-# LANGUAGE UndecidableInstances                                          #-}
module Monomorphic ( (:.:), Monomorphic (..), Monomorphicable(..)
                             , demote', demoteComposed, monomorphicCompose
                             , withPolymorhic, liftPoly, viaPoly, Compose(..)
                             ) where
import Control.Arrow
import Data.Functor.Compose

type (:.:) f g = Compose f g

-- | A wrapper type for polymophic types.
data Monomorphic k = forall a. Monomorphic (k a)

-- | A types which have the monomorphic representation.
class Monomorphicable k where
  -- | Monomorphic representation
  type MonomorphicRep k :: *
  -- | Promote the monomorphic value to the polymophic one.
  promote :: MonomorphicRep k -> Monomorphic k
  -- | Demote the polymorphic value to the monomorphic representation.
  demote  :: Monomorphic k -> MonomorphicRep k

-- | Convinience function to demote polymorphic types into monomorphic one directly.
demote' :: Monomorphicable k => k a -> MonomorphicRep k
demote' = demote . Monomorphic

-- | Demote polymorphic nested types directly into monomorphic representation.
demoteComposed :: Monomorphicable (f :.: g) => f (g a) -> MonomorphicRep (f :.: g)
demoteComposed = demote . Monomorphic . Compose

monomorphicCompose :: f (g a) -> Monomorphic (f :.: g)
monomorphicCompose = Monomorphic . Compose

-- | Apply dependently-typed function to the monomorphic representation.
withPolymorhic :: Monomorphicable k
               => MonomorphicRep k -> (forall a. k a -> b) -> b
withPolymorhic k trans =
  case promote k of
    Monomorphic a -> trans a

-- | Flipped version of 'withPolymorhic'.
liftPoly :: Monomorphicable k
         => (forall a. k a -> b) -> MonomorphicRep k -> b
liftPoly = flip withPolymorhic

-- | Demote the function between polymorphic types into the one between monomorphic one.
viaPoly :: (Monomorphicable k, Monomorphicable k')
        => (forall x y. k x -> k' y) -> MonomorphicRep k -> MonomorphicRep k'
viaPoly f a = demote $ Monomorphic $ liftPoly f a

instance (Show (MonomorphicRep k), Monomorphicable k) => Show (Monomorphic k) where
  showsPrec d x = showString "Polymorphic " . showsPrec (d + 1) (demote x)

instance (Read (MonomorphicRep k), Monomorphicable k) => Read (Monomorphic k) where
  readsPrec i = map (first promote) . readsPrec i
