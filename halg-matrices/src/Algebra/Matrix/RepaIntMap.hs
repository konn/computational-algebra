{-# LANGUAGE DeriveFunctor, PartialTypeSignatures, PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving, TypeOperators, ViewPatterns       #-}
{-# OPTIONS_GHC -Odph -rtsopts -threaded -fno-liberate-case     #-}
{-# OPTIONS_GHC -funfolding-keeness-factor1000 -fllvm -optlo-O3 #-}
{-# OPTIONS_GHC -funfolding-use-threshold1000                   #-}
module Algebra.Matrix.RepaIntMap
  ( RIMMatrix', RIMMatrix, URIMMatrix, DRIMMatrix, fromRows
  , delayMatrix, forceToVPar, forceToVSeq
  , gaussReductionD, gaussReductionP, gaussReductionS
  ) where
import           Algebra.Matrix.Generic      (Column, Matrix, Mutable, Row,
                                              WrapImmutable)
import qualified Algebra.Matrix.Generic      as GM
import           Algebra.Prelude.Core        hiding (Max, Min, traverse)
import           Control.DeepSeq             (NFData (..))
import           Control.Lens                (ifoldMap, imap, (%=), _1, _2)
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
type DRIMMatrix = RIMMatrix' D

data RIMMatrix' repr a = RIM { _rimColCount :: Int
                             , _rimRows :: Array repr (Z :. Int) (IntMap a)
                             }

instance (NFData a) => NFData (RIMMatrix' V a) where
  rnf (RIM i arr) = rnf i `seq` rnf (Repa.toVector arr)

instance (NFData a) => NFData (RIMMatrix' U a) where
  rnf (RIM i arr) = rnf i `seq` rnf (Repa.toUnboxed arr)

instance (NFData a) => NFData (RIMMatrix' D a) where
  rnf (RIM i arr) =
    let (Z :. j, fun) = toFunction arr
    in rnf i `seq` rnf j `seq` rnf fun

deriving instance (Eq a, Source repr (IntMap a)) => Eq (RIMMatrix' repr a)

instance (Monoidal a, Show a, Source repr (IntMap a)) => Show (RIMMatrix' repr a) where
  showsPrec d = showsPrec d . toRows

forceToVPar :: DRIMMatrix a -> RIMMatrix a
forceToVPar = withArray (runIdentity . computeP)

forceToVSeq :: DRIMMatrix a -> RIMMatrix a
forceToVSeq = withArray computeS

toRows :: (Monoidal a, Source r (IntMap a)) => RIMMatrix' r a -> [Vector a]
toRows (RIM c rs) = toList $ Repa.map (dicToRow c) rs

dicToRow :: Monoidal a => Int -> IntMap a -> Vector a
dicToRow c d = V.generate c $ \i -> fromMaybe zero $ IM.lookup i d

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

delayMatrix :: Source rep (IntMap a) => RIMMatrix' rep a -> RIMMatrix' D a
delayMatrix = withArray delay

-- | Perofms row echelon reduction, sequentially
gaussReductionS :: (Field a, DecidableZero a, Normed a)
                => DRIMMatrix a -> RIMMatrix a
gaussReductionS = withArray computeS . gaussReductionD

-- | Perofms row echelon reduction, parallelly
gaussReductionP :: (Field a, DecidableZero a, Normed a)
                => DRIMMatrix a -> RIMMatrix a
gaussReductionP = withArray (runIdentity . computeP) . gaussReductionD

rankG :: Normed a
      => IntSet ->  Int -> IntMap a
      -> Option (Min (Int, Weighted (Down (Norm a)) a, Int, Trivial (IntMap a)))
rankG remain i dic
  | i `IS.notMember` remain = Option Nothing
  | otherwise = Option $ do
  ((k, v), _) <- IM.minViewWithKey dic
  return (Min (k, Weighted (Down $ norm v) v, i, Weighted () dic))

rowCount :: Source r (IntMap a) => RIMMatrix' r a -> Int
rowCount m = let (Z :. n) = extent $ _rimRows m in n

gaussReductionD :: (DecidableZero a, Normed a , Field a, Source repr (IntMap a))
                => RIMMatrix' repr a -> RIMMatrix' D a
gaussReductionD matr@(RIM nCol r0) = RIM nCol $ fst $ execState loop (delay r0, IS.fromList [0..nRow - 1])
  where
    nRow = rowCount matr
    loop = do
      (rs, remain) <- get
      unless (IS.null remain) $
        case getOption $ ifoldMap (rankG remain) $ toList rs of
          Nothing -> return ()
          Just (Min (col, Weighted _ newC, k, unWeight -> dic)) -> do
            _2 %= IS.delete k
            let cases i d
                  | i == k = fmap (/newC) d
                  | otherwise =
                    case IM.lookup col d of
                      Nothing -> d
                      Just c ->
                        let scale = c * recip newC
                        in IM.filter (not . isZero) $
                           IM.unionWith (-) d $
                           fmap (scale *) dic
            _1 %= Repa.map (uncurry cases) . indexed
            loop

type instance Mutable (RIMMatrix' r) = WrapImmutable (RIMMatrix' r)
type instance Row (RIMMatrix' r) = Vector
type instance Column (RIMMatrix' r) = Vector

lookCoe :: Monoidal c => Int -> IntMap c -> c
lookCoe i = fromMaybe zero . IM.lookup i

updateAtRowIndex :: Source r1 (IntMap a) => RIMMatrix' r1 a -> Int -> (IntMap a -> IntMap a) -> RIMMatrix' D a
updateAtRowIndex (RIM c m) i f = RIM c $
  let (sh, fun) = toFunction m
  in fromFunction sh $ \(Z :. k) ->
    if k == i
    then f $ fun $ Z :. k
    else fun $ Z :. k
{-# INLINE updateAtRowIndex #-}

instance (DecidableZero a) => Matrix (RIMMatrix' D) a where
  {-# SPECIALISE instance DecidableZero a => Matrix (RIMMatrix' D) a #-}
  basicRowCount = rowCount
  basicColumnCount = _rimColCount
  basicUnsafeIndexM (RIM _ m) i j =
    return $ lookCoe j $ m Repa.! (Z :. i)
  basicUnsafeGetRowM (RIM c m) i = return $ dicToRow c $ m Repa.! (Z :. i)
  basicUnsafeGetColumnM (RIM _ m) i = toVector <$> computeP (Repa.map (lookCoe i) m)
  unsafeGenerate rs cs f = RIM cs $ fromFunction (Z :. rs) $ \(Z :. i) ->
    vecToIM $ V.generate cs $ \j -> f i j
  unsafeWrite m i j x = flip withArray m $ \n ->
    let (sh, fun) = toFunction n
    in fromFunction sh $ \(Z :. k) ->
      if k == i
      then if isZero x
      then IM.delete j $ fun $ Z:. k
      else IM.insert j x $ fun $ Z:. k
      else fun $ Z :. k
  unsafeFromRows = withArray delay . fromRows
  unsafeFromColumns cs0 =
    let cs = V.fromList cs0
        ncol = V.length cs
    in RIM ncol $ fromFunction (Z :. V.length (head cs0)) $ \(Z :. i) ->
      IM.fromList [ (i, c)
                  | j <- [0.. ncol - 1]
                  , let c = cs V.! j V.! i
                  , not $ isZero c
                  ]
  toRows = toRows
  toColumns (RIM c m) =
    fmap (\j -> V.map (lookCoe j) $ toVector $ runIdentity $ computeP m) [0.. c - 1]

  swapRows im i j = flip withArray im $ \m ->
    let (sh, fun) = toFunction m
    in fromFunction sh $ \(Z :. k) ->
      if i == k
      then fun (Z :. j)
      else if j == k
      then fun (Z :. i)
      else fun (Z :. k)
  scaleRow im i c = updateAtRowIndex im i $ \d ->
      if isZero c
      then IM.empty
      else IM.map (c *) d
  unsafeIMapRow m i f =
    updateAtRowIndex m i $
    IM.mapMaybeWithKey (\ j -> guardZero . f j)
