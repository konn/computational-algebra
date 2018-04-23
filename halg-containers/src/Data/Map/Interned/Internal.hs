{-# LANGUAGE DeriveAnyClass, DeriveFoldable, DeriveFunctor, DeriveGeneric  #-}
{-# LANGUAGE DeriveTraversable, ImplicitPrelude, NoMonomorphismRestriction #-}
{-# LANGUAGE PatternSynonyms, TypeFamilies                                 #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Data.Map.Interned.Internal where
import Control.DeepSeq
import Data.Hashable   (Hashable)
import Data.Interned
import GHC.Generics

type Size = Int
type Flipped = Bool

data MapF tag k v a = BinF !tag !Size !k !v !a !a
                    | TipF
                    deriving (Functor, Foldable, Traversable,
                              Generic, Hashable, Eq, NFData)

newtype Map k v =
  Map (MapF Id k v (Map k v))
  deriving (Generic, Hashable, NFData)

instance Eq (Map k v) where
  Map (BinF i _ _ _ _ _) == Map (BinF j _ _ _ _ _) = i == j
  Map TipF{} == Map TipF{} = True
  _ == _ = False

instance Ord (Map k v) where
  compare Tip Tip = EQ
  compare Tip _   = LT
  compare (Bin i _ _ _ _) (Bin j _ _ _ _) = compare i j

newtype UMap k v = UMap (MapF () k v (Map k v))
  deriving (Generic, Hashable, Eq)

pattern UBin :: Size -> k -> v -> Map k v -> Map k v -> UMap k v
pattern UBin size k v l r = UMap (BinF () size k v l r)

pattern UTip :: UMap k v
pattern UTip = UMap TipF

{-# COMPLETE UBin, UTip #-}

pattern Bin' :: (Ord k, Hashable k, Eq v, Hashable v) => () => Size -> k -> v -> Map k v -> Map k v -> Map k v
pattern Bin' size k v l r <- Map (BinF _ size k v l r) where
  Bin' size k v l r = intern (UBin size k v l r)

pattern Bin :: Size -> k -> v -> Map k v -> Map k v -> Map k v
pattern Bin size k v l r <- Map (BinF _ size k v l r)

pattern Tip :: Map k v
pattern Tip = Map TipF

idEq :: Map k1 v1 -> Map k1 v1 -> Bool
idEq (Map TipF) (Map TipF) = True
idEq (Map (BinF i _ _ _ _ _)) (Map (BinF j _ _ _ _ _)) = i == j
idEq _ _ = False

{-# COMPLETE Bin, Tip #-}
{-# COMPLETE Bin', Tip #-}

instance (Hashable k, Ord k, Eq v, Hashable v) => Interned (Map k v) where
  type Uninterned (Map k v) = UMap k v
  newtype Description (Map k v) =
    DMap (MapF () k v (Map k v))
    deriving (Generic, Hashable, Eq)
  describe (UBin s k v l r) = DMap (BinF () s k v l r)
  describe UTip             = DMap TipF
  identify i (UBin s k v l r) = Map (BinF i s k v l r)
  identify _ UTip             = Map TipF
  cacheWidth _ = 16384
  cache = mapCache

instance (Hashable k, Ord k, Eq v, Hashable v) => Uninternable (Map k v)  where
  unintern Tip = UTip
  unintern (Bin s k v l r) = UBin s k v l r

mapCache :: (Hashable k, Ord k, Eq v, Hashable v) => Cache (Map k v)
mapCache = mkCache
{-# NOINLINE mapCache #-}
