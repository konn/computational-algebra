{-# LANGUAGE TupleSections #-}
module Algebra.Matrix.Generic.Mutable
  ( MMatrix(..), Index, Size, Column, Row
  , new, unsafeNew, copy, clone, generate, generateM
  , fromRow, fromColumn, getRow, getColumn
  , imapRow, mapRow, fill, read, write
  , scaleRow, unsafeSwapRows, swapRows
  , gaussReduction, unsafeGaussReduction
  ) where
import           Algebra.Matrix.Generic.Base
import           Algebra.Prelude.Core        hiding (Vector, generate)
import           Control.Monad.Primitive     (PrimMonad, PrimState)
import qualified Data.Vector.Generic         as GV

-- | Mutable, row-based @0@-origin matrix
class (GV.Vector (Column mat) a, GV.Vector (Row mat) a) => MMatrix mat a where
  -- | @'basicUnsafeNew' n m@ creates a mutable matrix with @n@ rows and @m@ columns,
  --   without initialisation.
  --   This method should not be used directly, use @'unsafeNew'@ instead.
  basicUnsafeNew            :: PrimMonad m => Size -> Size -> m (mat (PrimState m) a)
  basicInitialise           :: PrimMonad m => mat (PrimState m) a -> m ()
  basicRowCount             :: mat s a -> Size
  basicColumnCount          :: mat s a -> Size
  unsafeGetRow              :: PrimMonad m => Index -> mat (PrimState m) a -> m (Row    mat a)
  unsafeGetColumn           :: PrimMonad m => Index -> mat (PrimState m) a -> m (Column mat a)
  unsafeFill                :: PrimMonad m => Size -> Size -> a -> m (mat (PrimState m) a)
  unsafeFill w h a = do
    m <- basicUnsafeNew w h
    forM_ [0..w-1] $ \i -> forM_ [0..h-1] $ \j -> unsafeWrite m i j a
    return m
  -- | Construct a mutable matrix consisting of a single row, perhaps without any copy.
  unsafeFromRow             :: PrimMonad m => Row mat a -> m (mat (PrimState m) a)
  unsafeFromRow = unsafeFromRows . (:[])
  -- | Construct a mutable matrix consisting a single column, perhaps without any copy.
  unsafeFromRows            :: PrimMonad m => [Row mat a] -> m (mat (PrimState m) a)

  -- | Construct a mutable matrix consisting a single column, perhaps without any copy.
  unsafeFromColumn          :: PrimMonad m => Column mat a -> m (mat (PrimState m) a)
  unsafeFromColumn          = unsafeFromColumns . (:[])
  unsafeFromColumns         :: PrimMonad m => [Column mat a] -> m (mat (PrimState m) a)
  unsafeFromColumns [] = new 0 0
  unsafeFromColumns xs = unsafeGenerate (GV.length $ head xs) (length xs) $ \i j -> (xs !! j) GV.! i

  -- | @'usnafeCopy' target source@ copies the content of @source@ to @target@, without boundary check.
  unsafeCopy                :: PrimMonad m => mat (PrimState m) a -> mat (PrimState m) a -> m ()
  -- | @'unsafeRead' i j m@ reads the value at @i@th row in @j@th column in @m@, without boundary check.
  --
  --   __N.B.__ Rows and columns are regarded as /zero-origin/, not @1@!.
  unsafeRead                :: PrimMonad m => mat (PrimState m) a -> Index ->Index -> m a
  unsafeWrite               :: PrimMonad m => mat (PrimState m) a -> Index -> Index -> a -> m ()
  basicSet                  :: PrimMonad m => mat (PrimState m) a -> a -> m ()
  basicUnsafeIMapRowM       :: PrimMonad m => mat (PrimState m) a -> Index -> (Index -> a -> m a) -> m ()
  basicUnsafeIMapRow        :: PrimMonad m => mat (PrimState m) a -> Index -> (Index -> a -> a) -> m ()
  basicUnsafeIMapRow m i f  = basicUnsafeIMapRowM m i ((return .). f)
  basicUnsafeSwapRows       :: PrimMonad m => mat (PrimState m) a -> Index -> Index -> m ()
  basicUnsafeSwapRows m i i' = forM_ [0.. basicColumnCount m - 1] $ \j -> do
    x <- unsafeRead m i  j
    y <- unsafeRead m i' j
    unsafeWrite m i  j y
    unsafeWrite m i' j x

  unsafeScaleRow :: (PrimMonad m, Commutative a) => mat (PrimState m) a -> Index -> a -> m ()

  unsafeGenerate :: (PrimMonad m) => Size -> Size -> (Index -> Index -> a) -> m (mat (PrimState m) a)
  unsafeGenerate w h f = do
    m <- unsafeNew w h
    basicInitialise m
    forM_ [0..w-1] $ \i -> forM_ [0..h-1] $ \j ->
      unsafeWrite m i j (f i j)
    return m


  unsafeGenerateM :: (PrimMonad m) => Size -> Size -> (Index -> Index -> m a) -> m (mat (PrimState m) a)
  unsafeGenerateM w h f = do
    m <- unsafeNew w h
    basicInitialise m
    forM_ [0..w-1] $ \i -> forM_ [0..h-1] $ \j ->
      unsafeWrite m i j =<< f i j
    return m

  toRows :: PrimMonad m => mat (PrimState m) a -> m [Row mat a]
  toRows mat = forM [0..rowCount mat-1] $ \i -> unsafeGetRow i mat

  toColumns :: PrimMonad m => mat (PrimState m) a -> m [Column mat a]
  toColumns mat = forM [0..columnCount mat-1] $ \i -> unsafeGetColumn i mat

  -- | @'combineRows' i c j mat@ adds scalar multiple of @j@th row by @c@ to @i@th.
  combineRows :: (Semiring a, Commutative a, PrimMonad m) => Index -> a -> Index -> mat (PrimState m) a -> m ()
  combineRows i c j m = checkBound i rowCount m $ checkBound j rowCount m $
    basicUnsafeIMapRowM m i (\k a -> (a+) . (c*) <$> unsafeRead m j k)


columnCount :: MMatrix mat a => mat s a -> Size
columnCount = basicColumnCount
{-# INLINE columnCount #-}

rowCount :: MMatrix mat a => mat s a -> Size
rowCount = basicRowCount
{-# INLINE rowCount #-}

-- | @'new' n m@ creates a mutable matrix with @n@ rows and @m@ columns.
new :: (MMatrix mat a, PrimMonad m) => Size -> Size -> m (mat (PrimState m) a)
new n m | n >= 0 && m >= 0 = basicUnsafeNew n m >>= \v -> basicInitialise v >> return v
        | otherwise = error $ "negative length: " ++ show n

-- | @'unsafeNew' n m@ creates a mutable matrix with @n@ rows and @m@ columns, without memory initialisation.
--
--   See also: @'new'@.
unsafeNew :: (MMatrix mat a, PrimMonad m) => Size -> Size -> m (mat (PrimState m) a)
unsafeNew n m | n >= 0 && m >= 0 = basicUnsafeNew n m
              | otherwise = error $ "negative length: " ++ show n

checkBound :: (Show a, Num a, Ord a) => a -> (t -> a) -> t -> p -> p
checkBound i f m a | 0 <= i && i < f m = a
                   | otherwise = error $  unwords ["Out of bouds:", show i, "out of", show (f m)]

-- | @'getRow' n mat@ retrieves @n@th row in @mat@
--
--   __N.B.__ Index is considered as /@0@-origin/, NOT @1@!
getRow :: (MMatrix mat a, PrimMonad m) => Index -> mat (PrimState m) a -> m (Row mat a)
getRow i m = checkBound i rowCount m $ unsafeGetRow i m

-- | @'getColumn' n mat@ retrieves @n@th colun in @mat@
--
--   __N.B.__ Index is considered as /@0@-origin/, NOT @1@!
getColumn :: (MMatrix mat a, PrimMonad m) => Index -> mat (PrimState m) a -> m (Column mat a)
getColumn i m = checkBound i columnCount m $ unsafeGetColumn i m

-- | @'imapRow' i f m@ mutates @i@th row in the matrix @m@ by applying @f@ with column index.
--
--   See also: @'mapRow'@, @'imapColumn'@, @'mapColumn'@.
--
--   __N.B.__ Index is considered as /@0@-origin/, NOT @1@!
imapRow :: (PrimMonad m, MMatrix mat a) => Index -> (Index -> a -> a) -> mat (PrimState m) a -> m ()
imapRow i f m = checkBound i rowCount m $ basicUnsafeIMapRow m i f

-- | @'mapRow' i f m@ mutates @i@th row in the matrix @m@ by applying @f@.
--
--   See also: @'imapRow'@, @'imapColumn'@, @'mapColumn'@.
--
--   __N.B.__ Index is considered as /@0@-origin/, NOT @1@!
mapRow :: (PrimMonad m, MMatrix mat a) => Index -> (a -> a) -> mat (PrimState m) a -> m ()
mapRow i f m = checkBound i rowCount m $ basicUnsafeIMapRow m i (const f)

-- | @'scaleRowL' i c m@ multiplies every element in @i@th row in @m@ by @c@, from right.
--
--   See also: @'scaleRowL'@ and @'scaleRow'@
scaleRow :: (Multiplicative a, Commutative a, MMatrix mat a, PrimMonad m)
         => Index -> a -> mat (PrimState m) a -> m ()
scaleRow i c m = checkBound i rowCount m $ unsafeScaleRow m i c
{-# INLINE scaleRow #-}

-- | @'fill' n m c@ creates a mutable constant matrix with @n@ rows and @m@ columns.
--
--   __N.B.__ Index is considered as /@0@-origin/, NOT @1@!
fill :: (PrimMonad m, MMatrix mat a) => Size -> Size -> a -> m (mat (PrimState m) a)
fill i j | 0 <= i && 0 <= j = unsafeFill i j
         | otherwise = error $ unwords[ "fill:", "out of bounds:", show (i, j)]

-- | @'read' i j m@ reads the value at @i@th row in @j@th column in @m@
--
--   __N.B.__ Index is considered as /@0@-origin/, NOT @1@!
read :: (PrimMonad m, MMatrix mat a) => Index -> Index -> mat (PrimState m) a -> m a
read i j m = checkBound i rowCount m $ checkBound j columnCount m $ unsafeRead m i j

-- | @'read' i j m@ writes the value at @i@th row in @j@th column in @m@
--
--   __N.B.__ Index is considered as /@0@-origin/, NOT @1@!
write :: (PrimMonad m, MMatrix mat a) => Index -> Index -> mat (PrimState m) a -> a -> m ()
write i j m = checkBound i rowCount m $ checkBound j columnCount m $ unsafeWrite m i j

-- | @'unsafeSwapRows' n m mat@ swaps @n@th and @m@th rows in @m@, without boundary check.
--
--   See also: @'swapRows'@.
unsafeSwapRows :: (PrimMonad m, MMatrix mat a) => Index -> Index -> mat (PrimState m) a -> m ()
unsafeSwapRows i j m = basicUnsafeSwapRows m i j

-- | @'swapRows' n m mat@ swaps @n@th and @m@th rows in @m@.
--
--   See also: @'unsafeSwapRows'@.
swapRows :: (PrimMonad m, MMatrix mat a) => Index -> Index -> mat (PrimState m) a -> m ()
swapRows i j m = checkBound i rowCount m $ checkBound j rowCount m $ unsafeSwapRows i j m

copy :: (PrimMonad m, MMatrix mat a) => mat (PrimState m) a -> mat (PrimState m) a -> m ()
copy targ src | rowCount targ == rowCount src
                && columnCount targ == columnCount src = unsafeCopy targ src
              | otherwise = error "Two matrices should be of the same size"

clone :: (PrimMonad m, MMatrix mat a) => mat (PrimState m) a -> m (mat (PrimState m) a)
clone m = do
  m' <- new (rowCount m) (columnCount m)
  unsafeCopy m' m
  return m'

fromRow :: (PrimMonad m, MMatrix mat a) => Row mat a -> m (mat (PrimState m) a)
fromRow = unsafeFromRow

fromColumn :: (PrimMonad m, MMatrix mat a) => Column mat a -> m (mat (PrimState m) a)
fromColumn = unsafeFromColumn

generate :: (PrimMonad m, MMatrix mat a)
         => Int -> Int -> (Index -> Index -> a) -> m (mat (PrimState m) a)
generate w h | 0 <= w && 0 <= h = unsafeGenerate w h
             | otherwise = error $ concat ["Generating matrix with negative width or height: ", show w, "x", show h]

generateM :: (PrimMonad m, MMatrix mat a)
          => Int -> Int -> (Index -> Index -> m a) -> m (mat (PrimState m) a)
generateM w h | 0 <= w && 0 <= h = unsafeGenerateM w h
              | otherwise = error $ concat ["Generating matrix with negative width or height: ", show w, "x", show h]

-- | Performs Gaussian reduction to given matrix, returns the pair of triangulated matrix, pivot matrix
--   and determinant.
gaussReduction :: (Eq a, PrimMonad m, Field a, Normed a, MMatrix mat a)
               => mat (PrimState m) a -> m (mat (PrimState m) a, mat (PrimState m) a, a)
gaussReduction mat = do
  m' <- clone mat
  (p, d) <- unsafeGaussReduction m'
  return (m', p, d)

-- | Performs in-place gaussian reduction to the mutable matrix, and returns the pivoting matrix and determinant.
unsafeGaussReduction :: (MMatrix mat a, Normed a, Eq a, Field a, PrimMonad m)
                      => mat (PrimState m) a -> m (mat (PrimState m) a, a)
unsafeGaussReduction mat = {-# SCC "gaussRed" #-} do
  pivot <- generate (rowCount mat) (rowCount mat) $ \ i j -> if i == j then one else zero
  det <- go 0 0 pivot one
  return (pivot, det)
  where
    nrows = rowCount mat
    ncols = columnCount mat
    go i j p dAcc
      | i >= nrows || j >= ncols = return dAcc
      | otherwise = do
          (k, newC) <- maximumBy (comparing $ norm . snd) <$>
            mapM (\ l -> (l,) <$> read l j mat) [i..rowCount mat - 1]
          if isZero newC
            then go i (j + 1) p zero
            else do
            let cancel l = do
                  coe <- negate <$> read l j mat
                  combineRows l coe i mat
                  combineRows l coe i p
            swapRows i k mat
            scaleRow i (recip newC) mat
            swapRows i k p
            scaleRow i (recip newC) p
            forM_ [0..i - 1] cancel
            forM_ [i+1..nrows - 1] cancel
            let offset = if i == k then id else negate
            go (i+1) (j+1) p (offset $ dAcc * newC)
