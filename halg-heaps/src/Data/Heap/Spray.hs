module Data.Heap.Spray (Spray, spraySort) where
import Data.Heap.Class

data Spray a = Empty | Branch (Spray a) a (Spray a)
  deriving (Read, Show, Eq, Ord)

instance Heap Spray where
  empty = Empty
  {-# INLINE empty #-}

  null Empty = True
  null _     = False
  {-# INLINE null #-}

  insert x t =
    let (small, big) = partite x t
    in Branch small x big
  {-# INLINE insert #-}

  findMin (Branch Empty x _) = Just x
  findMin (Branch l _ _)     = findMin l
  findMin Empty              = Nothing

  deleteMin (Branch Empty _ b)              = Just b
  deleteMin (Branch (Branch Empty _ b) y c) = Just $ Branch b y c
  deleteMin (Branch (Branch a x b) y c) =
    (\l -> Branch l x (Branch b y c)) <$> deleteMin a
  deleteMin Empty = Nothing

  merge Empty t = t
  merge (Branch a x b) t =
    let (ta, tb) = partite x t
    in Branch (merge ta a) x (merge tb b)

  toList = ($ []) . go where
    go Empty          = id
    go (Branch l x r) = go l . (x:) . go r
  {-# INLINE toList #-}

partite :: Ord a => a -> Spray a -> (Spray a, Spray a)
partite _ Empty = (Empty, Empty)
partite p t@(Branch a x b)
  | x <= p =
    case b of
      Empty -> (t, Empty)
      Branch b1 y b2
        | y <= p  ->
          let (small, big) = partite p b2
          in (Branch (Branch a x b1) y small, big)
        | otherwise ->
          let (small, big) = partite p b1
          in (Branch a x small, Branch big y b2)

  | otherwise =
    case a of
      Empty -> (Empty, t)
      Branch a1 y a2
        | y <= p ->
          let (small, big) = partite p a2
          in (Branch a1 y small, Branch big x b)
        | otherwise ->
          let (small, big) = partite p a1
          in (small, Branch big y (Branch a2 x b))

spraySort :: Ord a => [a] -> [a]
spraySort = toList . foldr insert Empty
