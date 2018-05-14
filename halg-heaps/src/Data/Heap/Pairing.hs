{-# LANGUAGE FlexibleContexts, LambdaCase, MultiParamTypeClasses        #-}
{-# LANGUAGE NoMonomorphismRestriction, PatternSynonyms, RankNTypes     #-}
{-# LANGUAGE RoleAnnotations, ScopedTypeVariables, UndecidableInstances #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Data.Heap.Pairing
  ( Pairing,
    -- * Basic Operations
    empty, null, singleton, fromList, insert,
    merge, union, mapMonotonic,
    -- * Query
    findMin, deleteMin, viewMin, uncons, span
  ) where
import           Data.Coerce     (coerce)
import qualified Data.Foldable   as F
import qualified Data.Heap.Class as HC
import           Data.List       (unfoldr)
import           Data.Maybe      (fromJust)
import           Data.Proxy      (Proxy (..))
import           Data.Reflection (Reifies (..), reify)
import           Data.Semigroup  (Semigroup (..))
import           Prelude         hiding (null, span)

-- | Ephemeral heap, implemented as a Pairing Pairing.
data Pairing a = Empty
            | Pairing (a -> a -> Ordering) (Rose a)
type role Pairing nominal

reifyOrd :: (a -> a -> Ordering) -> (forall s. Reifies s (ReifiedOrd a) => Proxy s -> r) -> r
reifyOrd c = reify $ ReifiedOrd c
{-# INLINE reifyOrd #-}

newtype ReflectedOrd a s = ReflectedOrd a
newtype ReifiedOrd a = ReifiedOrd { reifiedCompare :: a -> a -> Ordering }

instance Reifies s (ReifiedOrd a) => Eq (ReflectedOrd a s) where
  a@(ReflectedOrd x) == ReflectedOrd y =
    case reifiedCompare (reflect a) x y of
      EQ -> True
      _  -> False
  {-# INLINE (==) #-}

instance (Reifies s (ReifiedOrd a)) => Ord (ReflectedOrd a s) where
  compare a@(ReflectedOrd x) (ReflectedOrd y) =
    reifiedCompare (reflect a) x y
  {-# INLINE compare #-}

-- | Folds item in an increasing order
instance Foldable Pairing where
  minimum = fromJust . findMin
  {-# INLINE minimum #-}
  foldMap _ Empty = mempty
  foldMap f (Pairing c t) =
    reifyOrd c $ \m ->
    rfoldMap (coerce f) (castRose m t)
  {-# INLINE foldMap #-}

rfoldMap :: (Monoid m, Ord a) => (a -> m) -> Rose a -> m
rfoldMap f (T' x []) = f x
rfoldMap f (T' x rs) =
  f x `mappend` rfoldMap f (merges rs)

castRose :: Proxy s -> Rose a -> Rose (ReflectedOrd a s)
castRose _ = coerce
{-# INLINE castRose #-}

castRoses :: Proxy s -> [Rose a] -> [Rose (ReflectedOrd a s)]
castRoses  _ = coerce
{-# INLINE castRoses #-}

instance Eq (Pairing a) where
  Empty    == Empty    = True
  Empty    == _        = False
  _        == Empty    = False
  Pairing c t == Pairing _ u =
    reifyOrd c $ \pxy ->
    castRose pxy t == castRose pxy u
  {-# INLINE (==) #-}

instance Ord (Pairing a) where
  Empty    `compare` Empty    = EQ
  Empty    `compare` _        = LT
  _        `compare` Empty    = GT
  Pairing c t `compare` Pairing _ u =
    reifyOrd c $ \pxy ->
    compare (castRose pxy t) (castRose pxy u)
  {-# INLINE compare #-}

data Rose a = T' !a ![Rose a]
  deriving (Read, Show, Eq, Ord)

pattern T :: (Ord a) => () => a -> [Rose a] -> Pairing a
pattern T x ts <- Pairing _ (T' x ts) where
  T x ts = Pairing compare (T' x ts)

chunksOf :: Int -> [a] -> [[a]]
chunksOf n = unfoldr $ \case
  [] -> Nothing
  xs -> Just $ splitAt n xs
{-# INLINE chunksOf #-}

-- | O(1), amortised and worst
singleton :: Ord a => a -> Pairing a
singleton a = T a []
{-# INLINE singleton #-}

-- | O(1), both amortised and worst, merges two heaps.
merge :: Pairing a -> Pairing a -> Pairing a
merge h     Empty = h
merge Empty h     = h
merge (Pairing c h1) (Pairing _ h2) =
  reifyOrd c $ \m ->
  Pairing c $ coerce $ merge' (castRose m h1) (castRose m h2)
{-# INLINE merge #-}

merge' :: Ord a => Rose a -> Rose a -> Rose a
merge' l@(T' x hs) r@(T' y hs')
  | x <= y    = T' x (r : hs)
  | otherwise = T' y (l : hs')
{-# INLINE merge' #-}

-- | Synonym for @'merge'@.
union :: Pairing a -> Pairing a -> Pairing a
union = merge
{-# INLINE union #-}

-- | O(1), both amortised and worst, insert an element into a heap.
insert :: Ord a => a -> Pairing a -> Pairing a
insert x = merge (T x [])
{-# INLINE insert #-}

empty :: Pairing a
empty = Empty
{-# INLINE empty #-}

null :: Pairing a -> Bool
null Empty = True
null _     = False
{-# INLINE null #-}

fromList :: Ord a => [a] -> Pairing a
fromList = foldr insert empty
{-# INLINE fromList #-}

-- | O(1), both amortised and worst, find the minimum element.
findMin :: Pairing a -> Maybe a
findMin (Pairing _ (T' x _)) = Just x
findMin Empty             = Nothing
{-# INLINE findMin #-}

merges :: forall a. Ord a => [Rose a] -> Rose a
merges xs = reifyOrd compare $ \m ->
  let aux [x]    = x
      aux ~[x,y] = merge' x y
  in coerce $ foldr1 merge' $ map aux $
     chunksOf 2 $ castRoses m xs
{-# INLINE merges #-}

mapMonotonic :: Ord a => (t -> a) -> Pairing t -> Pairing a
mapMonotonic _ Empty      = Empty
mapMonotonic f (Pairing _ t) = Pairing compare $ monomap f t

monomap :: (t -> a) -> Rose t -> Rose a
monomap f (T' x rs) = T' (f x) $ map (monomap f) rs

-- | O(log n) amortised and O(n) worst, removes the least element
--   and returns remainder.
deleteMin :: Pairing a -> Maybe (Pairing a)
deleteMin (Pairing _ (T' _ [])) = Just Empty
deleteMin (Pairing c (T' _ xs)) =
  reifyOrd c $ \m ->
  Just $ Pairing c $ coerce $ merges $ castRoses m xs
deleteMin _ = Nothing
{-# INLINE deleteMin #-}

-- | O(1), amortised and worst, for the least element;
--   O(log n) amortised and O(n) worst for the remainder.
viewMin :: Pairing a -> Maybe (a, Pairing a)
viewMin h = (,) <$> findMin h <*> deleteMin h
{-# INLINE viewMin #-}

-- | Synonym for @'viewMin'@.
uncons :: Ord a => Pairing a -> Maybe (a, Pairing a)
uncons = viewMin
{-# INLINE uncons #-}

instance Semigroup (Pairing a) where
  (<>) = merge
  {-# INLINE (<>) #-}

instance Monoid (Pairing a) where
  mappend = (<>)
  {-# INLINE mappend #-}
  mempty  = Empty
  {-# INLINE mempty #-}

insertWith :: (a -> a -> Ordering) -> a -> Pairing a -> Pairing a
insertWith c x Empty = Pairing c (T' x [])
insertWith c x (Pairing _ r) =
  reifyOrd c $ \m ->
  Pairing c $ coerce $ merge' (T' (ReflectedOrd x) []) $ castRose m r
{-# INLINE insertWith #-}

-- | O(n log n), amortised, and O(n^2) worst.
span :: (a -> Bool) -> Pairing a -> (Pairing a, Pairing a)
span _ Empty = (Empty, Empty)
span p h@(Pairing c _) =
  case viewMin h of
    Nothing -> (Empty, Empty)
    Just (x, h')
      | p x -> let (as, bs) = span p h'
               in (insertWith c x as, bs)
      | otherwise -> (Empty, h)

instance HC.Heap Pairing where
  null  = null
  {-# INLINE null #-}
  empty = empty
  {-# INLINE empty #-}
  insert = insert
  {-# INLINE insert #-}
  merge  = merge
  {-# INLINE merge #-}
  singleton = singleton
  {-# INLINE singleton #-}
  findMin = findMin
  {-# INLINE findMin #-}
  deleteMin = deleteMin
  {-# INLINE deleteMin #-}
  viewMin = viewMin
  {-# INLINE viewMin #-}
  toList = F.toList
  {-# INLINE toList #-}
  fromList = fromList
  {-# INLINE fromList #-}
  span = span
  {-# INLINE span #-}

