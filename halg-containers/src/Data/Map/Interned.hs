{-# LANGUAGE BangPatterns, NoImplicitPrelude, NoMonomorphismRestriction #-}
{-# LANGUAGE PartialTypeSignatures, TypeOperators                       #-}
module Data.Map.Interned
  ( Map, null, singleton, empty, size, foldrWithKey, foldlWithKey
  , mapKeysMonotonic, mapKeysAntitonic, lookup, fromList
  , toList, toDescList, toAscList, split, insertWith, map, mapWithKey
  , insertSparse, maxViewWithKey, filter, filterWithKey, mapKeys
  , mapSparse, keys, mapMaybeWithKey, mapMaybe, merge, splitLookup
  , WhenMatched, WhenMissing, zipWithMatched, zipWithMaybeMatched, preserveMissing
  ) where
import AlgebraicPrelude           hiding (Map, empty, filter, lookup, map,
                                   mapMaybe, null)
import Data.Bits                  (shiftL, shiftR)
import Data.Hashable              (Hashable)
import Data.Map.Interned.Internal

null :: Map k v -> Bool
null Tip = True
null _   = False
{-# INLINE null #-}

size :: Map k v -> Int
size (Map TipF) = 0
size (Map (BinF _ s _ _ _ _)) = s
{-# INLINE size #-}

keys :: Map a1 a2 -> [a1]
keys = foldrWithKey (\k _ ks -> k : ks) []

map :: (Eq v, Hashable v, Hashable b, Ord b) => (a -> v) -> Map b a -> Map b v
map f = mapMaybeWithKey $ const $ Just . f
{-# INLINE map #-}

mapWithKey :: (Eq v, Hashable v, Hashable a1, Ord a1) => (a1 -> a2 -> v) -> Map a1 a2 -> Map a1 v
mapWithKey f = mapMaybeWithKey $ (Just .) . f

toList, toAscList, toDescList :: Map k v -> [(k, v)]
{-# INLINE toAscList #-}
{-# INLINE toList #-}
{-# INLINE toDescList #-}
toList = toAscList
toAscList = foldrWithKey (\k v l -> (k, v) : l) []
toDescList = foldlWithKey (\l k v -> (k, v) : l) []

foldlWithKey :: (a -> k -> b -> a) -> a -> Map k b -> a
foldlWithKey f = go
  where
    go z' Tip              = z'
    go z' (Bin _ kx x l r) = go (f (go z' l) kx x) r
{-# INLINE foldlWithKey #-}

foldrWithKey :: (k -> a -> b -> b) -> b -> Map k a -> b
foldrWithKey f = go
  where
    go z' Tip              = z'
    go z' (Bin _ kx x l r) = go (f kx x (go z' r)) l
{-# INLINE foldrWithKey #-}

data a :*: b = !a :*: !b

toPair :: a :*: b -> (a, b)
toPair (a :*: b) = (a, b)

delta,ratio :: Int
delta = 3
ratio = 2

bin :: (Eq v, Hashable v, Hashable k, Ord k) => k -> v -> Map k v -> Map k v -> Map k v
bin kx x l r = Bin' (size l + size r + 1) kx x l r
{-# INLINE bin #-}

balanceL :: (Eq v, Hashable v, Hashable k, Ord k) => k -> v -> Map k v -> Map k v -> Map k v
balanceL k x l r = case r of
  Tip -> case l of
           Tip -> Bin' 1 k x Tip Tip
           (Bin _ _ _ Tip Tip) -> Bin' 2 k x l Tip
           (Bin _ lk lx Tip (Bin _ lrk lrx _ _)) -> Bin' 3 lrk lrx (Bin' 1 lk lx Tip Tip) (Bin' 1 k x Tip Tip)
           (Bin _ lk lx ll@Bin{} Tip) -> Bin' 3 lk lx ll (Bin' 1 k x Tip Tip)
           (Bin ls lk lx ll@(Bin lls _ _ _ _) lr@(Bin lrs lrk lrx lrl lrr))
             | lrs < ratio*lls -> Bin' (1+ls) lk lx ll (Bin' (1+lrs) k x lr Tip)
             | otherwise -> Bin' (1+ls) lrk lrx (Bin' (1+lls+size lrl) lk lx ll lrl) (Bin' (1+size lrr) k x lrr Tip)

  (Bin rs _ _ _ _) -> case l of
           Tip -> Bin' (1+rs) k x Tip r

           (Bin ls lk lx ll lr)
              | ls > delta*rs  -> case (ll, lr) of
                   (Bin lls _ _ _ _, Bin lrs lrk lrx lrl lrr)
                     | lrs < ratio*lls -> Bin' (1+ls+rs) lk lx ll (Bin' (1+rs+lrs) k x lr r)
                     | otherwise -> Bin' (1+ls+rs) lrk lrx (Bin' (1+lls+size lrl) lk lx ll lrl) (Bin' (1+rs+size lrr) k x lrr r)
                   (_, _) -> error "Failure in Data.Map.balanceL"
              | otherwise -> Bin' (1+ls+rs) k x l r
{-# NOINLINE balanceL #-}

-- balanceR is called when right subtree might have been inserted to or when
-- left subtree might have been deleted from.
balanceR :: (Eq v, Hashable v, Hashable k, Ord k) => k -> v -> Map k v -> Map k v -> Map k v
balanceR k x l r = case l of
  Tip -> case r of
           Tip -> Bin' 1 k x Tip Tip
           (Bin _ _ _ Tip Tip) -> Bin' 2 k x Tip r
           (Bin _ rk rx Tip rr@Bin{}) -> Bin' 3 rk rx (Bin' 1 k x Tip Tip) rr
           (Bin _ rk rx (Bin _ rlk rlx _ _) Tip) -> Bin' 3 rlk rlx (Bin' 1 k x Tip Tip) (Bin' 1 rk rx Tip Tip)
           (Bin rs rk rx rl@(Bin rls rlk rlx rll rlr) rr@(Bin rrs _ _ _ _))
             | rls < ratio*rrs -> Bin' (1+rs) rk rx (Bin' (1+rls) k x Tip rl) rr
             | otherwise -> Bin' (1+rs) rlk rlx (Bin' (1+size rll) k x Tip rll) (Bin' (1+rrs+size rlr) rk rx rlr rr)

  (Bin ls _ _ _ _) -> case r of
           Tip -> Bin' (1+ls) k x l Tip

           (Bin rs rk rx rl rr)
              | rs > delta*ls  -> case (rl, rr) of
                   (Bin rls rlk rlx rll rlr, Bin rrs _ _ _ _)
                     | rls < ratio*rrs -> Bin' (1+ls+rs) rk rx (Bin' (1+ls+rls) k x l rl) rr
                     | otherwise -> Bin' (1+ls+rs) rlk rlx (Bin' (1+ls+size rll) k x l rll) (Bin' (1+rrs+size rlr) rk rx rlr rr)
                   (_, _) -> error "Failure in Data.Map.balanceR"
              | otherwise -> Bin' (1+ls+rs) k x l r
{-# NOINLINE balanceR #-}

link :: (Eq v, Hashable v, Hashable k, Ord k) => k -> v -> Map k v -> Map k v -> Map k v
link kx x Tip r  = insertMin kx x r
link kx x l Tip  = insertMax kx x l
link kx x l@(Bin sizeL ky y ly ry) r@(Bin sizeR kz z lz rz)
  | delta*sizeL < sizeR  = balanceL kz z (link kx x l lz) rz
  | delta*sizeR < sizeL  = balanceR ky y ly (link kx x ry r)
  | otherwise            = bin kx x l r

-- insertMin and insertMax don't perform potentially expensive comparisons.
insertMax :: (Eq t1, Ord t2, Hashable t2, Hashable t1) => t2 -> t1 -> Map t2 t1 -> Map t2 t1
insertMax kx x t
  = case t of
      Tip -> singleton kx x
      Bin _ ky y l r
          -> balanceR ky y l (insertMax kx x r)

insertMin :: (Eq t1, Ord t2, Hashable t2, Hashable t1) => t2 -> t1 -> Map t2 t1 -> Map t2 t1
insertMin kx x t
  = case t of
      Tip -> singleton kx x
      Bin _ ky y l r
          -> balanceL ky y (insertMin kx x l) r

split :: (Eq v, Ord k, Hashable v, Hashable k) => k -> Map k v -> (Map k v, Map k v)
split !k0 t0 = toPair $ go k0 t0
  where
    go k t =
      case t of
        Tip            -> Tip :*: Tip
        Bin _ kx x l r -> case compare k kx of
          LT -> let (lt :*: gt) = go k l in lt :*: link kx x gt r
          GT -> let (lt :*: gt) = go k r in link kx x l lt :*: gt
          EQ -> l :*: r
{-# INLINABLE split #-}

insertWith :: (Eq a, Hashable a, Hashable k, Ord k) => (a -> a -> a) -> k -> a -> Map k a -> Map k a
insertWith = go
  where
    -- We have no hope of making pointer equality tricks work
    -- here, because lazy insertWith *always* changes the tree,
    -- either adding a new entry or replacing an element with a
    -- thunk.
    go :: (Eq a, Ord k, Hashable k, Hashable a)
       => (a -> a -> a) -> k -> a -> Map k a -> Map k a
    go _ !kx x Tip = singleton kx x
    go f !kx x (Bin sy ky y l r) =
        case compare kx ky of
            LT -> balanceL ky y (go f kx x l) r
            GT -> balanceR ky y l (go f kx x r)
            EQ -> Bin' sy kx (f x y) l r
{-# INLINEABLE insertWith #-}

insertSparse :: (Eq a, DecidableZero a, Ord k, Hashable k, Hashable a)
             => k -> a -> Map k a -> Map k a
insertSparse = go
  where
    go :: (Eq a, DecidableZero a, Ord k, Hashable k, Hashable a)
       => k -> a -> Map k a -> Map k a
    go !kx x Tip = singleton kx x
    go !kx x (Bin sy ky y l r) =
        case compare kx ky of
            LT -> balanceL ky y (go kx x l) r
            GT -> balanceR ky y l (go kx x r)
            EQ -> let !z = x + y
                  in if isZero z then glue l r
                     else Bin' sy kx z l r
{-# INLINABLE insertSparse #-}

mapKeysMonotonic :: (Eq v, Hashable v, Hashable k, Ord k)
                 => (t -> k) -> Map t v -> Map k v
mapKeysMonotonic _ (Map TipF) = Tip
mapKeysMonotonic f (Map (BinF _ s k v l r)) = Bin' s (f k) v (mapKeysMonotonic f l) (mapKeysMonotonic f r)

mapKeysAntitonic :: (Eq v, Hashable v, Hashable k, Ord k) => (t -> k) -> Map t v -> Map k v
mapKeysAntitonic _ Tip = Tip
mapKeysAntitonic f (Bin s k v l r) = Bin' s (f k) v (mapKeysAntitonic f r) (mapKeysAntitonic f l)

singleton :: (Eq v, Hashable v, Hashable k, Ord k) => k -> v -> Map k v
singleton k v = Bin' 1 k v Tip Tip

empty :: Map k v
empty = Tip

lookup :: (Ord t) => t -> Map t a -> Maybe a
lookup = go
  where
    go !_ Tip = Nothing
    go k (Bin _ kx x l r) =
      case compare k kx of
        LT -> go k l
        GT -> go k r
        EQ -> Just x
{-# INLINABLE lookup #-}

maxViewWithKey :: (Eq b, Ord a, Hashable a, Hashable b)
               => Map a b -> Maybe ((a, b), Map a b)
maxViewWithKey Tip = Nothing
maxViewWithKey (Bin _ k x l r) = Just $
  case maxViewSure k x l r of
    MaxView km xm t -> ((km, xm), t)
{-# INLINE maxViewWithKey #-}

data MinView k a = MinView !k a !(Map k a)
data MaxView k a = MaxView !k a !(Map k a)
maxViewSure :: (Eq t2, Hashable t2, Hashable t1, Ord t1) => t1 -> t2 -> Map t1 t2 -> Map t1 t2 -> MaxView t1 t2
maxViewSure = go
  where
    go k x l Tip = MaxView k x l
    go k x l (Bin _ kr xr rl rr) =
      case go kr xr rl rr of
        MaxView km xm r' -> MaxView km xm (balanceL k x l r')
{-# NOINLINE maxViewSure #-}

minViewSure :: (Eq t2, Hashable t2, Hashable t1, Ord t1) => t1 -> t2 -> Map t1 t2 -> Map t1 t2 -> MinView t1 t2
minViewSure = go
  where
    go k x Tip r = MinView k x r
    go k x (Bin _ kl xl ll lr) r =
      case go kl xl ll lr of
        MinView km xm l' -> MinView km xm (balanceR k x l' r)
{-# NOINLINE minViewSure #-}

glue :: (Eq v, Ord k, Hashable k, Hashable v) => Map k v -> Map k v -> Map k v
glue Tip r = r
glue l Tip = l
glue l@(Bin sl kl xl ll lr) r@(Bin sr kr xr rl rr)
  | sl > sr = let !(MaxView km m l') = maxViewSure kl xl ll lr in balanceR km m l' r
  | otherwise = let !(MinView km m r') = minViewSure kr xr rl rr in balanceL km m l r'


filter :: (Eq t, Hashable t, Hashable k, Ord k) => (t -> Bool) -> Map k t -> Map k t
filter p = filterWithKey (\_ x -> p x)

-- | /O(n)/. Filter all keys\/values that satisfy the predicate.
--
-- > filterWithKey (\k _ -> k > 4) (fromList [(5,"a"), (3,"b")]) == singleton 5 "a"

filterWithKey :: (Eq v, Ord k, Hashable k, Hashable v) => (k -> v -> Bool) -> Map k v -> Map k v
filterWithKey _ Tip = Tip
filterWithKey p t@(Bin _ kx x l r)
  | p kx x    = if pl `idEq` l && pr `idEq` r
                then t
                else link kx x pl pr
  | otherwise = link2 pl pr
  where !pl = filterWithKey p l
        !pr = filterWithKey p r

link2 :: (Eq v, Ord k, Hashable k, Hashable v) => Map k v -> Map k v -> Map k v
link2 Tip r   = r
link2 l Tip   = l
link2 l@(Bin sizeL kx x lx rx) r@(Bin sizeR ky y ly ry)
  | delta*sizeL < sizeR = balanceL ky y (link2 l ly) ry
  | delta*sizeR < sizeL = balanceR kx x lx (link2 rx r)
  | otherwise           = glue l r

mapSparse :: (Eq v1, Hashable v1, Hashable k, Ord k, DecidableZero v1) => (v2 -> v1) -> Map k v2 -> Map k v1
mapSparse _ Tip = Tip
mapSparse f (Bin _ kx x l r) =
  let !z = f x
  in if isZero z
  then link2 (mapSparse f l) (mapSparse f r)
  else link kx z (mapSparse f l) (mapSparse f r)

type WhenMissing k a c = k -> a -> Maybe c
type WhenMatched k a b c = k -> a -> b -> Maybe c

merge
  :: (Eq b, Eq c, Hashable b, Hashable c, Hashable k, Ord k)
  => WhenMissing k a c -- ^ What to do with keys in @m1@ but not @m2@
  -> WhenMissing k b c -- ^ What to do with keys in @m2@ but not @m1@
  -> WhenMatched k a b c -- ^ What to do with keys in both @m1@ and @m2@
  -> Map k a -- ^ Map @m1@
  -> Map k b -- ^ Map @m2@
  -> Map k c
merge leftThere rightThere f = go
  where
    go t1 Tip = mapMaybeWithKey leftThere t1
    go Tip t2 = mapMaybeWithKey rightThere t2
    go (Bin _ kx x1 l1 r1) t2 = case splitLookup kx t2 of
      (l2, mx2, r2) -> case mx2 of
          Nothing -> maybe link2 (link kx) (leftThere kx x1) l' r'
          Just x2 -> maybe link2 (link kx) (f kx x1 x2) l' r'
        where
          !l' = go l1 l2
          !r' = go r1 r2
{-# INLINE merge #-}

data StrictTriple a b c = StrictTriple !a !b !c
splitLookup :: (Eq a, Hashable a, Hashable k, Ord k) => k -> Map k a -> (Map k a, Maybe a, Map k a)
splitLookup k0 m = case go k0 m of
     StrictTriple l mv r -> (l, mv, r)
  where
    go !k t =
      case t of
        Tip            -> StrictTriple Tip Nothing Tip
        Bin _ kx x l r -> case compare k kx of
          LT -> let StrictTriple lt z gt = go k l
                    !gt' = link kx x gt r
                in StrictTriple lt z gt'
          GT -> let StrictTriple lt z gt = go k r
                    !lt' = link kx x l lt
                in StrictTriple lt' z gt
          EQ -> StrictTriple l (Just x) r
{-# INLINABLE splitLookup #-}

mapMaybeWithKey :: (Eq v, Ord k, Hashable k, Hashable v) => (k -> t -> Maybe v) -> Map k t -> Map k v
mapMaybeWithKey _ Tip = Tip
mapMaybeWithKey f (Bin _ kx x l r) = case f kx x of
  Just y  -> link kx y (mapMaybeWithKey f l) (mapMaybeWithKey f r)
  Nothing -> link2 (mapMaybeWithKey f l) (mapMaybeWithKey f r)

mapMaybe :: (Eq v, Hashable v, Hashable k, Ord k)
  => (t -> Maybe v) -> Map k t -> Map k v
mapMaybe = mapMaybeWithKey . const
{-# INLINE mapMaybe #-}

preserveMissing :: WhenMissing k a a
preserveMissing = const Just

zipWithMaybeMatched :: (k -> a -> b -> Maybe c)
                    -> WhenMatched k a b c
zipWithMaybeMatched = id
{-# INLINE zipWithMaybeMatched #-}

zipWithMatched :: (k -> a -> b -> c)
               -> WhenMatched k a b c
zipWithMatched = fmap $ fmap $ fmap Just
{-# INLINE zipWithMatched #-}

mapKeys :: (Eq b, Ord k, Hashable k, Hashable b) => (t -> k) -> Map t b -> Map k b
mapKeys f = fromList . foldrWithKey (\k x xs -> (f k, x) : xs) []
{-# INLINABLE mapKeys #-}

foldlStrict :: (a -> b -> a) -> a -> [b] -> a
foldlStrict f = go
  where
    go z []     = z
    go z (x:xs) = let z' = f z x in z' `seq` go z' xs
{-# INLINE foldlStrict #-}

fromList :: (Eq b, Hashable b, Hashable k, Ord k) => [(k, b)] -> Map k b
fromList [] = Tip
fromList [(kx, x)] = Bin' 1 kx x Tip Tip
fromList ((kx0, x0) : xs0) | not_ordered kx0 xs0 = fromList' (Bin' 1 kx0 x0 Tip Tip) xs0
                           | otherwise = go (1::Int) (Bin' 1 kx0 x0 Tip Tip) xs0
  where
    not_ordered _ [] = False
    not_ordered kx ((ky,_) : _) = kx >= ky
    {-# INLINE not_ordered #-}

    fromList' = foldlStrict ins
      where ins t (k,x) = insertWith const k x t

    go !_ t [] = t
    go _ t [(kx, x)] = insertMax kx x t
    go s l xs@((kx, x) : xss) | not_ordered kx xss = fromList' l xs
                              | otherwise = case create s xss of
                                  (r, ys, []) -> go (s `shiftL` 1) (link kx x l r) ys
                                  (r, _,  ys) -> fromList' (link kx x l r) ys

    -- The create is returning a triple (tree, xs, ys). Both xs and ys
    -- represent not yet processed elements and only one of them can be nonempty.
    -- If ys is nonempty, the keys in ys are not ordered with respect to tree
    -- and must be inserted using fromList'. Otherwise the keys have been
    -- ordered so far.
    create !_ [] = (Tip, [], [])
    create s xs@(xp : xss)
      | s == 1 = case xp of (kx, x) | not_ordered kx xss -> (Bin' 1 kx x Tip Tip, [], xss)
                                    | otherwise -> (Bin' 1 kx x Tip Tip, xss, [])
      | otherwise = case create (s `shiftR` 1) xs of
                      res@(_, [], _) -> res
                      (l, [(ky, y)], zs) -> (insertMax ky y l, [], zs)
                      (l, ys@((ky, y):yss), _) | not_ordered ky yss -> (l, [], ys)
                                               | otherwise -> case create (s `shiftR` 1) yss of
                                                   (r, zs, ws) -> (link ky y l r, zs, ws)
{-# INLINABLE fromList #-}
