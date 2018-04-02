{-# LANGUAGE DefaultSignatures, NoMonomorphismRestriction, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables                                      #-}
module Algebra.Matrix.Generic
  ( Matrix(..), Column, Row, Size, Index, WrapImmutable, Mutable
  , rowCount, columnCount, generate, freeze, thaw
  , fromRows, fromColumns, create, (!), wrapImmutable
  ) where
import           Algebra.Matrix.Generic.Base
import           Algebra.Matrix.Generic.Mutable (Index, MMatrix, Size)
import qualified Algebra.Matrix.Generic.Mutable as GM
import           Algebra.Prelude.Core           hiding (Vector, generate)
import           Control.Monad.Primitive        (PrimMonad, PrimState)
import           Control.Monad.ST
import           Data.Foldable                  (foldrM)
import           Data.Functor.Identity
import           Data.Primitive.MutVar
import           Data.Vector.Generic            (Mutable, Vector)
import qualified Data.Vector.Generic            as GV

-- | General Matrix type, with associated mutable matrix.
class ( Vector (Column mat) a, Vector (Row mat) a
      , MMatrix (Mutable mat) a
      , Row mat    ~ Row (Mutable mat)
      , Column mat ~ Column (Mutable mat)
      )
   => Matrix mat a where
  basicRowCount         :: mat a -> Size
  basicColumnCount      :: mat a -> Size

  unsafeFreeze          :: PrimMonad m => Mutable mat (PrimState m) a -> m (mat a)
  default unsafeFreeze  :: (PrimMonad m, Mutable mat ~ WrapImmutable mat)
                        => Mutable mat (PrimState m) a -> m (mat a)
  unsafeFreeze (WrapImmutable m _ _) = readMutVar m

  unsafeThaw            :: PrimMonad m => mat a -> m (Mutable mat (PrimState m) a)
  default unsafeThaw    :: (Mutable mat ~ WrapImmutable mat, PrimMonad m)
                        => mat a -> m (Mutable mat (PrimState m) a)
  unsafeThaw = wrapImmutable

  basicUnsafeIndexM     :: Monad m => mat a -> Index -> Index -> m a
  basicUnsafeGetRowM    :: Monad m => mat a -> Index -> m (Row mat a)
  basicUnsafeGetRowM m i = return $ runST $
    GM.unsafeGetRow i =<< unsafeThaw m
  basicUnsafeGetColumnM :: Monad m => mat a -> Index -> m (Column mat a)
  basicUnsafeGetColumnM m i = return $ runST $
    GM.unsafeGetColumn i =<< unsafeThaw m

  basicUnsafeCopy      :: PrimMonad m => Mutable mat (PrimState m) a -> mat a -> m ()
  basicUnsafeCopy mmat = GM.unsafeCopy mmat <=< unsafeThaw

  unsafeGenerate :: Size -> Size -> (Index -> Index -> a) -> mat a
  unsafeGenerate w h f = runST $ unsafeFreeze =<< GM.unsafeGenerate w h f

  unsafeWrite :: mat a -> Index -> Index -> a -> mat a
  unsafeWrite mat i j x = withMutable mat $ \m -> GM.unsafeWrite m i j x

  unsafeFromRows :: [Row mat a] -> mat a
  unsafeFromRows rs = runST $ unsafeFreeze =<< GM.unsafeFromRows rs

  unsafeFromColumns :: [Column mat a] -> mat a
  unsafeFromColumns rs = runST $ unsafeFreeze =<< GM.unsafeFromColumns rs

  toRows :: mat a -> [Row mat a]
  toRows mat = runST $ GM.toRows =<< unsafeThaw mat

  toColumns ::mat a -> [Column mat a]
  toColumns mat = runST $ GM.toColumns =<< unsafeThaw mat

  swapRows :: mat a -> Index -> Index -> mat a
  swapRows mat i j = withMutable mat $ GM.swapRows i j

  scaleRow :: (Commutative a) => mat a -> Index -> a -> mat a
  scaleRow mat i c = withMutable mat $ GM.scaleRow i c

  unsafeIMapRowM :: Monad m => mat a -> Index -> (Index -> a -> m a) -> m (mat a)
  unsafeIMapRowM mat i f =
    let act j m = unsafeWrite m i j <$> (f i =<< basicUnsafeIndexM m i j)
    in foldrM act mat [0.. columnCount mat - 1]

  unsafeIMapRowM_ :: Monad m => mat a -> Index -> (Index -> a -> m b) -> m ()
  unsafeIMapRowM_ mat i f = void $ unsafeIMapRowM mat i (\j x -> f j x >> return x)

  unsafeIMapRow :: mat a -> Index -> (Index -> a -> a) -> mat a
  unsafeIMapRow mat i f = withMutable mat $ \n -> GM.basicUnsafeIMapRow n i f

  combineRows :: (Commutative a, Semiring a) => Index -> a -> Index -> mat a -> mat a
  combineRows i c j mat = withMutable mat $ GM.combineRows i c j

  gaussReduction :: (Eq a, Normed a, Field a) => mat a -> (mat a, mat a, a)
  gaussReduction mat = runST $ do
    (m', p, d) <- GM.gaussReduction =<< unsafeThaw mat
    tmat <- unsafeFreeze m'
    piv <- unsafeFreeze p
    return (tmat, piv, d)

-- | Wrapper type for matrix types without mutable representation.
--
--   __N.B.__ To make things work, you have to provide all methods of
--    @'Matrix'@ class except @'unsafeThaw'@, @'unsafeFreeze'@,
--    @'basicUnsafeCopy'@, @'unsafeIMapRowM'@, and @'gaussReduction'@.
data WrapImmutable mat s a = WrapImmutable { _getMutVar :: MutVar s (mat a)
                                           , _wiRowCount :: Size
                                           , _wiColCount :: Size
                                           }

type instance Column (WrapImmutable mat) = Column mat
type instance Row   (WrapImmutable mat) = Row mat

wrapImmutable :: (PrimMonad m, Matrix mat a) => mat a -> m (WrapImmutable mat (PrimState m) a)
wrapImmutable mat = do
  mvar <- newMutVar mat
  return $ WrapImmutable mvar (rowCount mat) (columnCount mat)

instance (Monoidal a, Matrix mat a) => MMatrix (WrapImmutable mat) a where
  basicUnsafeNew n m = wrapImmutable $ generate n m $ const zero
  basicInitialise _ = return ()
  basicRowCount    (WrapImmutable _ r _) = r
  basicColumnCount (WrapImmutable _ _ c) = c
  unsafeGetRow i (WrapImmutable m _ _) = flip basicUnsafeGetRowM i =<< readMutVar m
  unsafeGetColumn i (WrapImmutable m _ _) = flip basicUnsafeGetColumnM i =<< readMutVar m
  unsafeFromRows = wrapImmutable . unsafeFromRows
  unsafeFromColumns = wrapImmutable . unsafeFromColumns
  unsafeCopy (WrapImmutable dest _ _) (WrapImmutable src _ _) =
    writeMutVar dest =<< readMutVar src
  unsafeRead (WrapImmutable m _ _) i j =
    readMutVar m >>= \n -> basicUnsafeIndexM n i j
  unsafeWrite im i j x = withImmutable im $ \n -> unsafeWrite n i j x
  unsafeGenerate w h f = do
    m <- newMutVar $ unsafeGenerate w h f
    return $ WrapImmutable m w h
  basicSet im x =
    withImmutable im $ const $ generate (_wiRowCount im) (_wiColCount im) $ const $ const x
  basicUnsafeIMapRowM (WrapImmutable m _ c) i f =
    forM_ [0..c-1] $ \j -> do
      n <- readMutVar m
      writeMutVar m . unsafeWrite n i j =<< f j (n ! (i, j))
  basicUnsafeIMapRow im i f = withImmutable im $ \n -> unsafeIMapRow n i f
  basicUnsafeSwapRows im i j = withImmutable im $ \n -> swapRows n i j
  unsafeScaleRow im i c = withImmutable im $ \n -> scaleRow n i c
  combineRows i c j m = withImmutable m $ \n -> combineRows i c j n

withImmutable :: PrimMonad m => WrapImmutable mat (PrimState m) a ->  (mat a -> mat a) -> m ()
withImmutable (WrapImmutable m _ _) mut =
  readMutVar m >>= writeMutVar m . mut

withMutable :: Matrix mat a => mat a -> (forall s. Mutable mat s a -> ST s ()) -> mat a
withMutable m act = runST $ do
  mat' <- thaw m
  act mat'
  unsafeFreeze mat'
{-# INLINE withMutable #-}

rowCount :: Matrix mat a => mat a -> Size
rowCount = basicRowCount

columnCount :: Matrix mat a => mat a -> Size
columnCount = basicColumnCount

generate :: Matrix mat a => Size -> Size -> (Index -> Index -> a) -> mat a
generate w h f = runST $ unsafeFreeze =<< GM.generate w h f

freeze :: (Matrix mat a, PrimMonad m) => Mutable mat (PrimState m) a -> m (mat a)
freeze = unsafeFreeze <=< GM.clone

thaw :: (Matrix mat a, PrimMonad m) => mat a -> m (Mutable mat (PrimState m) a)
thaw   = GM.clone <=< unsafeThaw

fromRows :: Matrix mat a => [Row mat a] -> mat a
fromRows rs
  | let lens = map GV.length rs
  , and $ zipWith (==) lens (tail lens) = unsafeFromRows rs
  | otherwise = error "fromRows: rows should be of the same length"

fromColumns :: Matrix mat a => [Column mat a] -> mat a
fromColumns cs
  | let lens = map GV.length cs
  , and $ zipWith (==) lens (tail lens) = unsafeFromColumns cs
  | otherwise = error "fromColumns: columns should be of the same length"

create :: Matrix mat a => (forall s. ST s (Mutable mat s a)) -> mat a
create act = runST $ unsafeFreeze =<< act

(!) :: Matrix mat a => mat a -> (Index, Index) -> a
(!) mat (i, j) = runIdentity $ basicUnsafeIndexM mat i j
