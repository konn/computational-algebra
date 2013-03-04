{-# LANGUAGE ConstraintKinds, DataKinds, ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts, PolyKinds, Rank2Types, TypeFamilies #-}
{-# LANGUAGE UndecidableInstances                                  #-}
module Wrappers where
import BaseTypes
import Control.Arrow

data Monomorphic k = forall a. Monomorphic (k a)

class Wrappable a where
  type BasicType a :: *
  promote :: BasicType a -> Monomorphic a
  demote  :: Monomorphic a -> BasicType a

instance Wrappable SNat where
  type BasicType SNat = Int
  promote 0     = Monomorphic SZ
  promote n
    | n < 0     = error "negative number"
    | otherwise =
        case promote (n - 1) of
          Monomorphic sn -> Monomorphic (SS sn)
  demote (Monomorphic sn) = toInt sn

liftPoly :: Wrappable k => (forall x. k x -> b) -> BasicType k -> b
liftPoly orig a =
  case promote a of
    Monomorphic sval -> orig sval

viaPoly :: Wrappable k => (forall x y. k x -> k y) -> BasicType k -> BasicType k
viaPoly f a = demote $ Monomorphic $ liftPoly f a

instance Wrappable (Vector a) where
  type BasicType (Vector a) = [a]
  demote  (Monomorphic n) = toList n
  promote [] = Monomorphic Nil
  promote (x:xs) =
    case promote xs of
      Monomorphic xs' -> Monomorphic $ x :- xs'

instance (Show (BasicType k), Wrappable k) => Show (Monomorphic k) where
  showsPrec d x = showString "Polymorphic " . showsPrec (d + 1) (demote x)

instance (Read (BasicType k), Wrappable k) => Read (Monomorphic k) where
  readsPrec i = map (first promote) . readsPrec i
