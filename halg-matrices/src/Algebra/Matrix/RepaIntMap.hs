{-# LANGUAGE DeriveFunctor, PartialTypeSignatures, PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving, TypeOperators, ViewPatterns       #-}
{-# OPTIONS_GHC -Odph -rtsopts -threaded -fno-liberate-case     #-}
{-# OPTIONS_GHC -funfolding-keeness-factor1000 -fllvm -optlo-O3 #-}
{-# OPTIONS_GHC -funfolding-use-threshold1000                   #-}
module Algebra.Matrix.RepaIntMap
  ( RIMMatrix', RIMMatrix, URIMMatrix, fromRows
  , gaussReductionD, gaussReductionP, gaussReductionS
  ) where
import Algebra.Prelude.Core hiding (Max, Min, traverse)
import Control.Lens         (ifoldMap, imap, (%=), _1, _2)

import           Control.Monad.State
import           Data.Array.Repa             as Repa
import           Data.Array.Repa.Eval        as Repa hiding (zero)
import           Data.Array.Repa.Repr.Vector as Repa
import           Data.Functor.Identity       (runIdentity)
import           Data.IntMap                 (IntMap)
import qualified Data.IntMap                 as IM
import qualified Data.IntSet                 as IS
import           Data.Ord                    (Down (..))
import           Data.Semigroup              (Min (..), Option (..))
import qualified Data.Vector                 as V

type RIMMatrix  = RIMMatrix' V
type URIMMatrix = RIMMatrix' U

data RIMMatrix' repr a = RIM { _rimColCount :: Int
                             , _rimRows :: Array repr (Z :. Int) (IntMap a)
                             }

deriving instance (Eq a, Source repr (IntMap a)) => Eq (RIMMatrix' repr a)

instance (Monoidal a, Show a, Source repr (IntMap a)) => Show (RIMMatrix' repr a) where
  showsPrec d = showsPrec d . toRows

toRows :: (Monoidal a, Source r (IntMap a)) => RIMMatrix' r a -> [Vector a]
toRows (RIM c rs) = toList $ Repa.map (\ d -> V.generate c $ \i -> fromMaybe zero $ IM.lookup i d) rs

fromRows :: DecidableZero a => [Vector a] -> RIMMatrix a
fromRows vs =
  let cols = V.length $ head vs
      rows = length vs
  in RIM cols $
     fromListVector (Z :. rows) $ fmap vecToIM vs

vecToIM :: DecidableZero a => Vector a -> IntMap a
vecToIM = IM.fromList . catMaybes . imap (\i v -> (,) i <$> guardZero v) . V.toList

indexed :: (Source r b)
        => Array r DIM1 b -> Array D DIM1 (Int, b)
indexed xs = traverse xs id (\f (Z :. i) -> (i, f (Z :.i)))

data Weighted w a = Weighted { getWeight :: w
                             , unWeight :: a
                             }
                    deriving (Read, Show, Functor)

instance Eq a => Eq (Weighted a b) where
  (==) = (==) `on` getWeight

instance Ord a => Ord (Weighted a b) where
  compare = comparing getWeight

type Trivial a = Weighted () a

guardZero :: DecidableZero a => a -> Maybe a
guardZero c | isZero c = Nothing
            | otherwise = Just c

{-# INLINE withArray #-}
withArray :: (Array rep DIM1 (IntMap a) -> Array rep' DIM1 (IntMap a))
          -> RIMMatrix' rep a -> RIMMatrix' rep' a
withArray f (RIM c rs) = RIM c (f rs)

-- | Perofms row echelon reduction, sequentially
gaussReductionS :: ( Source repr (IntMap a), Target repr (IntMap a)
                   , Field a, DecidableZero a, Normed a
                   )
                => RIMMatrix' repr a -> RIMMatrix' repr a
gaussReductionS = withArray computeS . gaussReductionD

-- | Perofms row echelon reduction, parallelly
gaussReductionP :: ( Source repr (IntMap a), Target repr (IntMap a)
                   , Field a, DecidableZero a, Normed a
                   )
                => RIMMatrix' repr a -> RIMMatrix' repr a
gaussReductionP = withArray (runIdentity . computeP) . gaussReductionD

rankG :: Normed a
      => IntSet ->  Int -> IntMap a
      -> Option (Min (Int, Weighted (Down (Norm a)) a, Int, Trivial (IntMap a)))
rankG remain i dic
  | i `IS.notMember` remain = Option Nothing
  | otherwise = Option $ do
  ((k, v), _) <- IM.minViewWithKey dic
  return (Min (k, Weighted (Down $ norm v) v, i, Weighted () dic))


gaussReductionD :: (DecidableZero a, Normed a , Field a, Source repr (IntMap a))
                => RIMMatrix' repr a -> RIMMatrix' D a
gaussReductionD (RIM nCol r0) = RIM nCol $ fst $ execState loop (delay r0, IS.fromList [0..nRow - 1])
  where
    Z :. nRow = extent r0
    loop = do
      (rs, remain) <- get
      unless (IS.null remain) $
        case getOption $ ifoldMap (rankG remain) $ toList rs of
          Nothing -> return ()
          Just (Min (col, Weighted _ newC, k, unWeight -> dic)) -> do
            _2 %= IS.delete k
            let cancel d =
                  case IM.lookup col d of
                    Nothing -> d
                    Just c ->
                      let scale = c * recip newC
                      in IM.filter (not . isZero) $ IM.unionWith (-) d (fmap (scale *) dic)
                cases i
                  | i == k = fmap (/newC)
                  | otherwise = cancel
            _1 %= Repa.map (uncurry cases) . indexed
            loop
