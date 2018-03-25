{-# LANGUAGE DeriveFunctor, DeriveTraversable #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Algebra.Algorithms.Groebner.Signature where
import           Algebra.Prelude.Core
import           Control.Lens
import qualified Data.Coerce          as DC
import           Data.Maybe           (fromJust)
import           Data.Semigroup       hiding ((<>))
import qualified Data.Vector.Generic  as GV

-- | Induces position-over-term ordering
data Coordinate a = Coordinate { position :: {-# UNPACK #-} !Int
                               , factor   :: a
                               }
                  deriving (Eq, Functor, Traversable, Foldable, Show)

fromCoordinate :: GV.Vector v a => Int -> a -> Coordinate a -> v a
fromCoordinate len def c = GV.generate len $ \i -> if i == position c then factor c else def

newtype WeightLatter a b = WeightLatter { runWeightLatter :: (a, b) }

instance Eq b => Eq (WeightLatter a b) where
  (==) = (==) `on` (snd . runWeightLatter)

instance Ord b => Ord (WeightLatter a b) where
  compare = comparing $ snd . runWeightLatter

instance (Ord a) => Ord (Coordinate a) where
  compare (Coordinate ei a) (Coordinate ej b) = compare ei ej <> compare a b

signature :: IsOrderedPolynomial poly
          => [poly]
          -> Coordinate (Coefficient poly, OrderedMonomial (MOrder poly) (Arity poly))
signature = fromJust . DC.coerce
          . ifoldMap (\i -> Option . Just . Max . Coordinate i . WeightLatter . leadingTerm)
