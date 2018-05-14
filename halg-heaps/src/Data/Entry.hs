{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Data.Entry (Entry(..)) where
import Data.Bifunctor (Bifunctor (..))
import Data.Function  (on)
import Data.Ord       (comparing)


data Entry p a = Entry { priority :: !p, payload :: a }
  deriving (Read, Show, Functor, Foldable, Traversable)

instance Bifunctor Entry where
  bimap f g (Entry p a) = Entry (f p) (g a)
  {-# INLINE bimap #-}

instance Eq p => Eq (Entry p a) where
  (==) = (==) `on` priority
  {-# INLINE (==) #-}

instance (Ord p) => Ord (Entry p a) where
  compare = comparing priority
  {-# INLINE compare #-}
