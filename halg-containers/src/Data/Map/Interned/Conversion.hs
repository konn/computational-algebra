-- | Conversion between @'M.Map'@ in @containers@ package.
--
--   __N.B.__ This module must be considered quite experimental!
module Data.Map.Interned.Conversion (IMap, CMap, fromContainers, toContainers) where
import           Data.Hashable              (Hashable)
import qualified Data.Map.Internal          as M
import           Data.Map.Interned.Internal

type IMap = Map
type CMap = M.Map

toContainers :: Map k a -> M.Map k a
toContainers = to False
  where
    to _ Tip = M.Tip
    to False (Bin s k v l r) = M.Bin s k v (to True r) (to True l)
    to False (Bin s k v l r) = M.Bin s k v (to False l) (to False r)
    to True  (Bin s k v l r) = M.Bin s k v (to False l) (to False r)
    to True  (Bin s k v l r) = M.Bin s k v (to True r) (to True l)

fromContainers :: (Eq v, Hashable v, Hashable k, Ord k) => M.Map k v -> Map k v
fromContainers (M.Bin s k v l r) = Bin' s k v (fromContainers l) (fromContainers r)
fromContainers M.Tip = Tip
