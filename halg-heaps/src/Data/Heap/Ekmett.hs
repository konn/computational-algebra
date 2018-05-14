module Data.Heap.Ekmett (H.Heap, module HC) where
import qualified Data.Foldable   as F
import qualified Data.Heap       as H
import qualified Data.Heap.Class as HC

instance HC.Heap H.Heap where
  empty = H.empty
  {-# INLINE empty #-}
  null  = H.null
  {-# INLINE null #-}
  insert = H.insert
  {-# INLINE insert #-}
  merge  = H.union
  {-# INLINE merge #-}
  findMin = fmap fst . H.viewMin
  {-# INLINE findMin #-}
  deleteMin = fmap snd . H.viewMin
  {-# INLINE deleteMin #-}
  singleton = H.singleton
  {-# INLINE singleton #-}
  span = H.span
  {-# INLINE span #-}
  toList = F.toList
  {-# INLINE toList #-}
  fromList = H.fromList
  {-# INLINE fromList #-}
