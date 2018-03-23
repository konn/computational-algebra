{-# LANGUAGE NoMonomorphismRestriction, PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications      #-}
-- | Faugere's F4 algorithm
module Algebra.Algorithms.Groebner.F4
  (f4WithStrategy', f4WithStrategy, normalStrategy) where
import           Algebra.Matrix.Generic
import           Algebra.Matrix.RepaIntMap
import           Algebra.Prelude.Core      hiding (Min)
import qualified Data.DList                as DL
import           Data.Semigroup            (Semigroup)
import qualified Data.Semigroup            as Semi

data MinTag w m = MinTag { _getWeight :: w
                         , getMonoid :: m
                         }
                | NoMin
  deriving (Read, Show, Eq, Ord)


instance (Semigroup m, Ord w) => Monoid (MinTag w m) where
  mempty = NoMin
  NoMin `mappend` r = r
  r `mappend` NoMin = r
  MinTag w m `mappend` MinTag u n =
    case compare w u of
      EQ -> MinTag w (m Semi.<> n)
      LT -> MinTag w m
      GT -> MinTag w n

degPair :: (IsOrderedPolynomial poly) => poly -> poly -> Int
degPair f g = totalDegree $ lcmMonomial (leadingMonomial f) (leadingMonomial g)

normalStrategy :: (IsOrderedPolynomial poly, Foldable t)
               => t (poly, poly)
               -> [(poly, poly)]
normalStrategy =
  DL.toList . getMonoid . foldMap (\(f, g) -> MinTag (degPair f g) $ DL.singleton (f,g))

-- | Computes Gröbner Basis for the given ideal by F_4 algorithm, with specified
--   internal representation of matrix.
f4WithStrategy' :: (IsOrderedPolynomial poly, Field (Coefficient poly), Matrix mat (Coefficient poly))
                => proxy mat -> ([(poly, poly)] -> [(poly, poly)]) -> Ideal poly -> [poly]
f4WithStrategy' _ select ideal = undefined

-- | F_4 algorithm, using parallel array as an internal representation
f4WithStrategy :: (Field (Coefficient poly), IsOrderedPolynomial poly)
   => ([(poly, poly)] -> [(poly, poly)]) -> Ideal poly -> [poly]
f4WithStrategy = f4WithStrategy' (Proxy :: Proxy DRIMMatrix)

computeMatrix :: (IsOrderedPolynomial poly,
                  Field (Coefficient poly),
                  Matrix mat (Coefficient poly)
                 )
              => proxy mat -> [poly] -> [poly] -> mat (Coefficient poly)
computeMatrix _ = undefined
