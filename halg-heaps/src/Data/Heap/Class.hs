{-# LANGUAGE NoMonomorphismRestriction #-}
module Data.Heap.Class (Heap(..), Entry(..), union, uncons) where
import Data.Entry (Entry (..))

-- | Synonym for @'merge'@.
union :: (Ord a, Heap f) => f a -> f a -> f a
union = merge
{-# INLINE union #-}

-- | Synonym for @'viewMin'@.
uncons :: (Ord a, Heap f) => f a -> Maybe (a, f a)
uncons = viewMin
{-# INLINE uncons #-}

class Heap f where
  empty     :: Ord a => f a
  null      :: Ord a => f a -> Bool
  insert    :: Ord a =>   a -> f a -> f a
  merge     :: Ord a => f a -> f a -> f a
  findMin   :: Ord a => f a -> Maybe a
  deleteMin :: Ord a => f a -> Maybe (f a)
  singleton :: Ord a => a -> f a
  singleton = flip insert empty
  {-# INLINE singleton #-}
  viewMin :: Ord a => f a -> Maybe (a, f a)
  viewMin q = (,) <$> findMin q <*> deleteMin q
  {-# INLINE viewMin #-}
  fromList :: Ord a => [a] -> f a
  fromList = foldr insert empty
  {-# INLINE fromList #-}
  toList :: Ord a => f a -> [a]
  toList =
    let go q =
          case viewMin q of
            Nothing -> []
            Just (x, q') -> x : go q'
    in go
  {-# INLINE toList #-}
  span :: Ord a => (a -> Bool) -> f a -> (f a, f a)
  span p =
    let go q =
          case viewMin q of
            Nothing -> (empty, q)
            Just (x, r)
              | p x -> let (yes, no) = go r
                       in (insert x yes, no)
              | otherwise -> (empty, q)
    in go
  {-# INLINE span #-}
