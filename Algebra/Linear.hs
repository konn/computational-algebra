-- | This module is borrowed from @matrix@ package.
-- If existing bugs are fixed, this module is redundant.
module Algebra.Linear (
    -- * Matrix type
    Matrix , prettyMatrix
  , nrows , ncols
  , forceMatrix
    -- * Builders
  , matrix
  , fromList , fromLists
  , rowVector
  , colVector
    -- ** Special matrices
  , zero
  , identity
  , permMatrix
    -- * Accessing
  , getElem , (!) , safeGet
  , getRow  , getCol
  , getDiag
    -- * Manipulating matrices
  , setElem
  , transpose , extendTo
  , mapRow , mapCol
    -- * Submatrices
    -- ** Splitting blocks
  , submatrix
  , minorMatrix
  , splitBlocks
    -- ** Joining blocks
  , (<|>) , (<->)
  , joinBlocks
    -- * Matrix multiplication
    -- ** About matrix multiplication
    -- $mult

    -- ** Functions
  , multStd
  , multStrassen
  , multStrassenMixed
    -- * Linear transformations
  , scaleMatrix
  , scaleRow
  , combineRows
  , switchRows
  , switchCols
    -- * Decompositions
  , luDecomp, luDecomp'
    -- * Properties
  , trace , diagProd
    -- ** Determinants
  , detLaplace
  , detLU
  ) where

-- Classes
import Control.DeepSeq
import Control.Monad    (forM_)
import Data.Foldable    (Foldable (..))
import Data.Monoid
import Data.Traversable
-- Data
import           Control.Monad.Primitive (PrimMonad, PrimState)
import           Data.List               (maximumBy)
import           Data.Ord
import qualified Data.Vector             as V
import qualified Data.Vector.Mutable     as MV

-------------------------------------------------------
-------------------------------------------------------
---- MATRIX TYPE

encode :: Int -> (Int,Int) -> Int
{-# INLINE encode #-}
encode m (i,j) = (i-1)*m + j - 1

decode :: Int -> Int -> (Int,Int)
{-# INLINE decode #-}
decode m k = (q+1,r+1)
 where
  (q,r) = quotRem k m

-- | Type of matrices.
data Matrix a = M {
   nrows :: {-# UNPACK #-} !Int -- ^ Number of rows.
 , ncols :: {-# UNPACK #-} !Int -- ^ Number of columns.
 , mvect :: (V.Vector a) -- ^ Content of the matrix as a plain vector.
   } deriving Eq

-- | Just a cool way to output the size of a matrix.
sizeStr :: Int -> Int -> String
sizeStr n m = show n ++ "x" ++ show m

-- | Display a matrix as a 'String' using the 'Show' instance of its elements.
prettyMatrix :: Show a => Matrix a -> String
prettyMatrix m@(M _ _ v) = unlines
 [ "( " <> unwords (fmap (\j -> fill mx $ show $ m ! (i,j)) [1..ncols m]) <> " )" | i <- [1..nrows m] ]
 where
  mx = V.maximum $ fmap (length . show) v
  fill k str = replicate (k - length str) ' ' ++ str

instance Show a => Show (Matrix a) where
 show = prettyMatrix

instance NFData a => NFData (Matrix a) where
 rnf (M _ _ v) = rnf v

-- | /O(rows*cols)/. Similar to 'V.force', drop any extra memory.
--
--   Useful when using 'submatrix' from a big matrix.
forceMatrix :: Matrix a -> Matrix a
forceMatrix (M n m v) = M n m $ V.force v

-------------------------------------------------------
-------------------------------------------------------
---- FUNCTOR INSTANCE

instance Functor Matrix where
 fmap f (M n m v) = M n m $ V.map f v

-- | /O(rows*cols)/. Map a function over a row.
--   Example:
--
-- >                          ( 1 2 3 )   ( 1 2 3 )
-- >                          ( 4 5 6 )   ( 5 6 7 )
-- > mapRow (\_ x -> x + 1) 2 ( 7 8 9 ) = ( 7 8 9 )
--
mapRow :: (Int -> a -> a) -- ^ Function takes the current column as additional argument.
        -> Int            -- ^ Row to map.
        -> Matrix a -> Matrix a
mapRow f r (M n m v) =
    M n m $ V.imap (\k x -> let (i,j) = decode m k
                            in  if i == r then f j x else x) v

-- | /O(rows*cols)/. Map a function over a column.
--   Example:
--
-- >                          ( 1 2 3 )   ( 1 3 3 )
-- >                          ( 4 5 6 )   ( 4 6 6 )
-- > mapCol (\_ x -> x + 1) 2 ( 7 8 9 ) = ( 7 9 9 )
--
mapCol :: (Int -> a -> a) -- ^ Function takes the current row as additional argument.
        -> Int            -- ^ Column to map.
        -> Matrix a -> Matrix a
mapCol f c (M n m v) =
    M n m $ V.imap (\k x -> let (i,j) = decode m k
                            in  if j == c then f i x else x) v

-------------------------------------------------------
-------------------------------------------------------
---- FOLDABLE AND TRAVERSABLE INSTANCES

instance Foldable Matrix where
 foldMap f = foldMap f . mvect

instance Traversable Matrix where
 sequenceA (M n m v) = fmap (M n m) $ sequenceA v

-------------------------------------------------------
-------------------------------------------------------
---- BUILDERS

-- | /O(rows*cols)/. The zero matrix of the given size.
--
-- > zero n m =
-- >                 n
-- >   1 ( 0 0 ... 0 0 )
-- >   2 ( 0 0 ... 0 0 )
-- >     (     ...     )
-- >     ( 0 0 ... 0 0 )
-- >   n ( 0 0 ... 0 0 )
zero :: Num a =>
     Int -- ^ Rows
  -> Int -- ^ Columns
  -> Matrix a
zero n m = M n m $ V.replicate (n*m) 0

-- | /O(rows*cols)/. Generate a matrix from a generator function.
--   Example of usage:
--
-- >                                  (  1  0 -1 -2 )
-- >                                  (  3  2  1  0 )
-- >                                  (  5  4  3  2 )
-- > matrix 4 4 $ \(i,j) -> 2*i - j = (  7  6  5  4 )
matrix :: Int -- ^ Rows
       -> Int -- ^ Columns
       -> ((Int,Int) -> a) -- ^ Generator function
       -> Matrix a
{-# INLINE matrix #-}
matrix n m f = M n m $ V.generate (n*m) $ f . decode m

-- | /O(rows*cols)/. Identity matrix of the given order.
--
-- > identity n =
-- >                 n
-- >   1 ( 1 0 ... 0 0 )
-- >   2 ( 0 1 ... 0 0 )
-- >     (     ...     )
-- >     ( 0 0 ... 1 0 )
-- >   n ( 0 0 ... 0 1 )
--
identity :: Num a => Int -> Matrix a
identity n = matrix n n $ \(i,j) -> if i == j then 1 else 0

-- | Create a matrix from a non-empty list given the desired size.
--   The list must have at least /rows*cols/ elements.
--   An example:
--
-- >                       ( 1 2 3 )
-- >                       ( 4 5 6 )
-- > fromList 3 3 [1..] =  ( 7 8 9 )
--
fromList :: Int -- ^ Rows
         -> Int -- ^ Columns
         -> [a] -- ^ List of elements
         -> Matrix a
{-# INLINE fromList #-}
fromList n m = M n m . V.fromList

-- | Create a matrix from an non-empty list of non-empty lists.
--   /Each list must have the same number of elements/.
--   For example:
--
-- > fromLists [ [1,2,3]      ( 1 2 3 )
-- >           , [4,5,6]      ( 4 5 6 )
-- >           , [7,8,9] ] =  ( 7 8 9 )
--
fromLists :: [[a]] -> Matrix a
{-# INLINE fromLists #-}
fromLists xss = fromList (length xss) (length $ head xss) $ concat xss

-- | /O(1)/. Represent a vector as a one row matrix.
rowVector :: V.Vector a -> Matrix a
rowVector v = M 1 (V.length v) v

-- | /O(1)/. Represent a vector as a one column matrix.
colVector :: V.Vector a -> Matrix a
colVector v = M (V.length v) 1 v

-- | /O(rows*cols)/. Permutation matrix.
--
-- > permMatrix n i j =
-- >               i     j       n
-- >   1 ( 1 0 ... 0 ... 0 ... 0 0 )
-- >   2 ( 0 1 ... 0 ... 0 ... 0 0 )
-- >     (     ...   ...   ...     )
-- >   i ( 0 0 ... 0 ... 1 ... 0 0 )
-- >     (     ...   ...   ...     )
-- >   j ( 0 0 ... 1 ... 0 ... 0 0 )
-- >     (     ...   ...   ...     )
-- >     ( 0 0 ... 0 ... 0 ... 1 0 )
-- >   n ( 0 0 ... 0 ... 0 ... 0 1 )
--
-- When @i == j@ it reduces to 'identity' @n@.
--
permMatrix :: Num a
           => Int -- ^ Size of the matrix.
           -> Int -- ^ Permuted row 1.
           -> Int -- ^ Permuted row 2.
           -> Matrix a -- ^ Permutation matrix.
permMatrix n r1 r2 | r1 == r2 = identity n
permMatrix n r1 r2 = matrix n n f
 where
  f (i,j)
   | i == r1 = if j == r2 then 1 else 0
   | i == r2 = if j == r1 then 1 else 0
   | i == j = 1
   | otherwise = 0

-------------------------------------------------------
-------------------------------------------------------
---- ACCESSING

-- | /O(1)/. Get an element of a matrix. Indices range from /(1,1)/ to /(n,m)/.
getElem :: Int      -- ^ Row
        -> Int      -- ^ Column
        -> Matrix a -- ^ Matrix
        -> a
{-# INLINE getElem #-}
getElem i j (M _ m v) = v V.! encode m (i,j)

-- | Short alias for 'getElem'.
{-# INLINE (!) #-}
(!) :: Matrix a -> (Int,Int) -> a
m ! (i,j) = getElem i j m

-- | Safe variant of 'getElem'.
safeGet :: Int -> Int -> Matrix a -> Maybe a
safeGet i j a@(M n m _)
 | i > n || j > m = Nothing
 | otherwise = Just $ getElem i j a

-- | /O(cols)/. Get a row of a matrix as a vector.
getRow :: Int -> Matrix a -> V.Vector a
getRow i (M _ m v) = V.generate m $ \j -> v V.! encode m (i,j+1)

-- | /O(rows)/. Get a column of a matrix as a vector.
getCol :: Int -> Matrix a -> V.Vector a
getCol j (M n m v) = V.generate n $ \i -> v V.! encode m (i+1,j)

-- | /O(min rows cols)/. Diagonal of a /not necessarily square/ matrix.
getDiag :: Matrix a -> V.Vector a
getDiag m = V.generate k $ \i -> m ! (i+1,i+1)
 where
  k = min (nrows m) (ncols m)

-------------------------------------------------------
-------------------------------------------------------
---- MANIPULATING MATRICES

msetElem:: PrimMonad m => a -> Int -> (Int,Int) -> MV.MVector (PrimState m) a -> m ()
msetElem x m p v = MV.write v (encode m p) x

-- | /O(1)/. Replace the value of a cell in a matrix.
setElem :: a -- ^ New value.
        -> (Int,Int) -- ^ Position to replace.
        -> Matrix a -- ^ Original matrix.
        -> Matrix a -- ^ Matrix with the given position replaced with the given value.
setElem x p (M n m v) = M n m $ V.modify (msetElem x m p) v

-- | /O(rows*cols)/. The transpose of a matrix.
--   Example:
--
-- >           ( 1 2 3 )   ( 1 4 7 )
-- >           ( 4 5 6 )   ( 2 5 8 )
-- > transpose ( 7 8 9 ) = ( 3 6 9 )
transpose :: Matrix a -> Matrix a
transpose m = matrix (ncols m) (nrows m) $ \(i,j) -> m ! (j,i)

-- | Extend a matrix to a given size adding zeroes.
--   If the matrix already has the required size, nothing happens.
--   The matrix is /never/ reduced in size.
--   Example:
--
-- >                          ( 1 2 3 0 0 )
-- >              ( 1 2 3 )   ( 4 5 6 0 0 )
-- >              ( 4 5 6 )   ( 7 8 9 0 0 )
-- > extendTo 4 5 ( 7 8 9 ) = ( 0 0 0 0 0 )
extendTo :: Num a
         => Int -- ^ Minimal number of rows.
         -> Int -- ^ Minimal number of columns.
         -> Matrix a -> Matrix a
extendTo n m a = a''
 where
  n'  = n - nrows a
  a'  = if n' <= 0 then a  else a  <-> zero n' (ncols a)
  m'  = m - ncols a
  a'' = if m' <= 0 then a' else a' <|> zero (nrows a') m'

-------------------------------------------------------
-------------------------------------------------------
---- WORKING WITH BLOCKS

-- | /O(subrows*subcols)/. Extract a submatrix given row and column limits.
--   Example:
--
-- >                   ( 1 2 3 )
-- >                   ( 4 5 6 )   ( 2 3 )
-- > submatrix 1 2 2 3 ( 7 8 9 ) = ( 5 6 )
submatrix :: Int    -- ^ Starting row
             -> Int -- ^ Ending row
          -> Int    -- ^ Starting column
             -> Int -- ^ Ending column
          -> Matrix a
          -> Matrix a
{-# INLINE submatrix #-}
submatrix r1 r2 c1 c2 (M _ m vs) = M r' c' $ V.generate (r'*c') $
 \k -> let (i,j) = decode c' k in vs V.! encode m (i+r1-1,j+c1-1)
  where
   r' = r2-r1+1
   c' = c2-c1+1

-- | /O(rows*cols)/. Remove a row and a column from a matrix.
--   Example:
--
-- >                 ( 1 2 3 )
-- >                 ( 4 5 6 )   ( 1 3 )
-- > minorMatrix 2 2 ( 7 8 9 ) = ( 7 9 )
minorMatrix :: Int -- ^ Row @r@ to remove.
            -> Int -- ^ Column @c@ to remove.
            -> Matrix a -- ^ Original matrix.
            -> Matrix a -- ^ Matrix with row @r@ and column @c@ removed.
minorMatrix r c (M n m v) =
 M (n-1) (m-1) $ V.ifilter (\k _ -> let (i,j) = decode m k in i /= r && j /= c) v

-- | Make a block-partition of a matrix using a given element as reference.
--   The element will stay in the bottom-right corner of the top-left corner matrix.
--
-- >                 (             )   (      |      )
-- >                 (             )   ( ...  | ...  )
-- >                 (    x        )   (    x |      )
-- > splitBlocks i j (             ) = (-------------) , where x = a_{i,j}
-- >                 (             )   (      |      )
-- >                 (             )   ( ...  | ...  )
-- >                 (             )   (      |      )
--
--   Note that some blocks can end up empty. We use the following notation for these blocks:
--
-- > ( TL | TR )
-- > (---------)
-- > ( BL | BR )
--
--   Where T = Top, B = Bottom, L = Left, R = Right.
--
--   Implementation is done via slicing of vectors.
splitBlocks :: Int      -- ^ Row of the splitting element.
            -> Int      -- ^ Column of the splitting element.
            -> Matrix a -- ^ Matrix to split.
            -> (Matrix a,Matrix a
               ,Matrix a,Matrix a) -- ^ (TL,TR,BL,BR)
{-# INLINE splitBlocks #-}
splitBlocks i j a@(M n m _) = ( submatrix    1  i 1 j a , submatrix    1  i (j+1) m a
                              , submatrix (i+1) n 1 j a , submatrix (i+1) n (j+1) m a )

-- | Join blocks of the form detailed in 'splitBlocks'.
joinBlocks :: (Matrix a,Matrix a
              ,Matrix a,Matrix a)
           ->  Matrix a
{-# INLINE joinBlocks #-}
joinBlocks (tl,tr,bl,br) = (tl <|> tr)
                               <->
                           (bl <|> br)

{-# RULES
"matrix/splitAndJoin"
   forall i j m. joinBlocks (splitBlocks i j m) = m
  #-}

-- | Horizontally join two matrices. Visually:
--
-- > ( A ) <|> ( B ) = ( A | B )
--
-- Where both matrices /A/ and /B/ have the same number of rows.
-- /This condition is not checked/.
(<|>) :: Matrix a -> Matrix a -> Matrix a
{-# INLINE (<|>) #-}
(M n m v) <|> (M _ m' v') = M n m'' $ V.generate (n*m'') $
  \k -> let (i,j) = decode m'' k in if j <= m
                                       then v  V.! encode m  (i,j)
                                       else v' V.! encode m' (i,j-m)
 where
  m'' = m + m'

-- | Vertically join two matrices. Visually:
--
-- >                   ( A )
-- > ( A ) <-> ( B ) = ( - )
-- >                   ( B )
--
-- Where both matrices /A/ and /B/ have the same number of columns.
-- /This condition is not checked/.
(<->) :: Matrix a -> Matrix a -> Matrix a
{-# INLINE (<->) #-}
(M n m v) <-> (M n' _ v') = M (n+n') m $ v V.++ v'

-------------------------------------------------------
-------------------------------------------------------
---- MATRIX MULTIPLICATION

{- $mult

Three methods are provided for matrix multiplication.

* 'multStd':
     Matrix multiplication following directly the definition.
     This is the best choice when you know for sure that your
     matrices are small.

* 'multStrassen':
     Matrix multiplication following the Strassen's algorithm.
     Complexity grows slower but also some work is added
     partitioning the matrix. Also, it only works on square
     matrices of order @2^n@, so if this condition is not
     met, it is zero-padded until this is accomplished.
     Therefore, its use it is not recommended.

* 'multStrassenMixed':
     This function mixes the 'multStd' and 'multStrassen' methods.
     It provides a better performance in general. Method @(@'*'@)@
     of the 'Num' class uses this function because it gives the best
     average performance. However, if you know for sure that your matrices are
     small, you should use 'multStd' instead, since
     'multStrassenMixed' is going to switch to that function anyway.

-}

-- | Standard matrix multiplication by definition.
multStd :: Num a => Matrix a -> Matrix a -> Matrix a
{-# INLINE multStd #-}
multStd a1@(M n m _) a2@(M n' m' _)
   -- Checking that sizes match...
   | m /= n' = error $ "Multiplication of " ++ sizeStr n m ++ " and "
                    ++ sizeStr n' m' ++ " matrices."
   | otherwise = multStd_ a1 a2

-- | Standard matrix multiplication by definition, without checking if sizes match.
multStd_ :: Num a => Matrix a -> Matrix a -> Matrix a
{-# INLINE multStd_  #-}
multStd_ a1@(M n m _) a2@(M _ m' _) = matrix n m' $ \(i,j) -> sum [ a1 ! (i,k) * a2 ! (k,j) | k <- [1 .. m] ]

first :: (a -> Bool) -> [a] -> a
first f = go
 where
  go (x:xs) = if f x then x else go xs
  go [] = error "first: no element match the condition."

-- | Strassen's algorithm over square matrices of order @2^n@.
strassen :: Num a => Matrix a -> Matrix a -> Matrix a
-- Trivial 1x1 multiplication.
strassen (M 1 1 v) (M 1  1  v') = M 1 1 $ V.zipWith (*) v v'
-- General case guesses that the input matrices are square matrices
-- whose order is a power of two.
strassen a b = joinBlocks (c11,c12,c21,c22)
 where
  -- Size of the subproblem is halved.
  n = div (nrows a) 2
  -- Split of the original problem into smaller subproblems.
  (a11,a12,a21,a22) = splitBlocks n n a
  (b11,b12,b21,b22) = splitBlocks n n b
  -- The seven Strassen's products.
  p1 = strassen (a11 + a22) (b11 + b22)
  p2 = strassen (a21 + a22)  b11
  p3 = strassen  a11        (b12 - b22)
  p4 = strassen        a22  (b21 - b11)
  p5 = strassen (a11 + a12)        b22
  p6 = strassen (a21 - a11) (b11 + b12)
  p7 = strassen (a12 - a22) (b21 + b22)
  -- Merging blocks
  c11 = p1 + p4 - p5 + p7
  c12 = p3 + p5
  c21 = p2 + p4
  c22 = p1 - p2 + p3 + p6

-- | Strassen's matrix multiplication.
multStrassen :: Num a => Matrix a -> Matrix a -> Matrix a
multStrassen a1@(M n m _) a2@(M n' m' _)
   | m /= n' = error $ "Multiplication of " ++ sizeStr n m ++ " and "
                    ++ sizeStr n' m' ++ " matrices."
   | otherwise =
       let mx = maximum [n,m,n',m']
           n2  = first (>= mx) $ fmap (2^) [(0 :: Int)..]
           b1 = extendTo n2 n2 a1
           b2 = extendTo n2 n2 a2
       in  submatrix 1 n 1 m' $ strassen b1 b2

strmixFactor :: Int
strmixFactor = 100

-- | Strassen's mixed algorithm.
strassenMixed :: Num a => Matrix a -> Matrix a -> Matrix a
{-# SPECIALIZE strassenMixed :: Matrix Double -> Matrix Double -> Matrix Double #-}
{-# SPECIALIZE strassenMixed :: Matrix Int -> Matrix Int -> Matrix Int #-}
strassenMixed a@(M r _ _) b
 | r < strmixFactor = multStd_ a b
 | odd r = let r' = r + 1
               a' = extendTo r' r' a
               b' = extendTo r' r' b
           in  submatrix 1 r 1 r $ strassenMixed a' b'
 | otherwise = joinBlocks (c11,c12,c21,c22)
 where
  -- Size of the subproblem is halved.
  n = quot r 2
  -- Split of the original problem into smaller subproblems.
  (a11,a12,a21,a22) = splitBlocks n n a
  (b11,b12,b21,b22) = splitBlocks n n b
  -- The seven Strassen's products.
  p1 = strassenMixed (a11 + a22) (b11 + b22)
  p2 = strassenMixed (a21 + a22)  b11
  p3 = strassenMixed  a11        (b12 - b22)
  p4 = strassenMixed        a22  (b21 - b11)
  p5 = strassenMixed (a11 + a12)        b22
  p6 = strassenMixed (a21 - a11) (b11 + b12)
  p7 = strassenMixed (a12 - a22) (b21 + b22)
  -- Merging blocks
  c11 = p1 + p4 - p5 + p7
  c12 = p3 + p5
  c21 = p2 + p4
  c22 = p1 - p2 + p3 + p6

-- | Mixed Strassen's matrix multiplication.
multStrassenMixed :: Num a => Matrix a -> Matrix a -> Matrix a
{-# INLINE multStrassenMixed #-}
multStrassenMixed a1@(M n m _) a2@(M n' m' _)
   | m /= n' = error $ "Multiplication of " ++ sizeStr n m ++ " and "
                    ++ sizeStr n' m' ++ " matrices."
   | n < strmixFactor = multStd_ a1 a2
   | otherwise =
       let mx = maximum [n,m,n',m']
           n2 = if even mx then mx else mx+1
           b1 = extendTo n2 n2 a1
           b2 = extendTo n2 n2 a2
       in  submatrix 1 n 1 m' $ strassenMixed b1 b2

-------------------------------------------------------
-------------------------------------------------------
---- NUMERICAL INSTANCE

instance Num a => Num (Matrix a) where
 fromInteger = M 1 1 . V.singleton . fromInteger
 negate = fmap negate
 abs = fmap abs
 signum = fmap signum

 -- Addition of matrices.
 {-# SPECIALIZE (+) :: Matrix Double -> Matrix Double -> Matrix Double #-}
 {-# SPECIALIZE (+) :: Matrix Int -> Matrix Int -> Matrix Int #-}
 (M n m v) + (M n' m' v')
   -- Checking that sizes match...
   | n /= n' || m /= m' = error $ "Addition of " ++ sizeStr n m ++ " and "
                               ++ sizeStr n' m' ++ " matrices."
   -- Otherwise, trivial zip.
   | otherwise = M n m $ V.zipWith (+) v v'

 -- Substraction of matrices.
 {-# SPECIALIZE (-) :: Matrix Double -> Matrix Double -> Matrix Double #-}
 {-# SPECIALIZE (-) :: Matrix Int -> Matrix Int -> Matrix Int #-}
 (M n m v) - (M n' m' v')
   -- Checking that sizes match...
   | n /= n' || m /= m' = error $ "Substraction of " ++ sizeStr n m ++ " and "
                               ++ sizeStr n' m' ++ " matrices."
   -- Otherwise, trivial zip.
   | otherwise = M n m $ V.zipWith (-) v v'

 -- Multiplication of matrices.
 {-# INLINE (*) #-}
 (*) = multStrassenMixed

-------------------------------------------------------
-------------------------------------------------------
---- TRANSFORMATIONS

-- | Scale a matrix by a given factor.
--   Example:
--
-- >               ( 1 2 3 )   (  2  4  6 )
-- >               ( 4 5 6 )   (  8 10 12 )
-- > scaleMatrix 2 ( 7 8 9 ) = ( 14 16 18 )
scaleMatrix :: Num a => a -> Matrix a -> Matrix a
scaleMatrix = fmap . (*)

-- | Scale a row by a given factor.
--   Example:
--
-- >              ( 1 2 3 )   (  1  2  3 )
-- >              ( 4 5 6 )   (  8 10 12 )
-- > scaleRow 2 2 ( 7 8 9 ) = (  7  8  9 )
scaleRow :: Num a => a -> Int -> Matrix a -> Matrix a
scaleRow = mapRow . const . (*)

-- | Add to one row a scalar multiple of other row.
--   Example:
--
-- >                   ( 1 2 3 )   (  1  2  3 )
-- >                   ( 4 5 6 )   (  6  9 12 )
-- > combineRows 2 2 1 ( 7 8 9 ) = (  7  8  9 )
combineRows :: Num a => Int -> a -> Int -> Matrix a -> Matrix a
combineRows r1 l r2 m = mapRow (\j x -> x + l * getElem r2 j m) r1 m

-- | Switch two rows of a matrix.
--   Example:
--
-- >                ( 1 2 3 )   ( 4 5 6 )
-- >                ( 4 5 6 )   ( 1 2 3 )
-- > switchRows 1 2 ( 7 8 9 ) = ( 7 8 9 )
switchRows :: Int -- ^ Row 1.
           -> Int -- ^ Row 2.
           -> Matrix a -- ^ Original matrix.
           -> Matrix a -- ^ Matrix with rows 1 and 2 switched.
switchRows r1 r2 (M n m vs) = M n m $ V.modify (\mv -> do
  forM_ [1..m] $ \j ->
    MV.swap mv (encode m (r1, j)) (encode m (r2, j))) vs

-- | Switch two coumns of a matrix.
--   Example:
--
-- >                ( 1 2 3 )   ( 2 1 3 )
-- >                ( 4 5 6 )   ( 5 4 6 )
-- > switchCols 1 2 ( 7 8 9 ) = ( 8 7 9 )
switchCols :: Int -- ^ Col 1.
           -> Int -- ^ Col 2.
           -> Matrix a -- ^ Original matrix.
           -> Matrix a -- ^ Matrix with cols 1 and 2 switched.
switchCols c1 c2 (M n m vs) = M n m $ V.modify (\mv -> do
  forM_ [1..n] $ \j ->
    MV.swap mv (encode m (j, c1)) (encode m (j, c2))) vs

-------------------------------------------------------
-------------------------------------------------------
---- DECOMPOSITIONS

-- LU DECOMPOSITION

-- | Matrix LU decomposition with /partial pivoting/.
--   The result for a matrix /M/ is given in the format /(U,L,P,d)/ where:
--
--   * /U/ is an upper triangular matrix.
--
--   * /L/ is an /unit/ lower triangular matrix.
--
--   * /P/ is a permutation matrix.
--
--   * /d/ is the determinant of /P/.
--
--   * /PM = LU/.
--
--   These properties are only guaranteed when the input matrix is invertible.
--   An additional property matches thanks to the strategy followed for pivoting:
--
--   * /L_(i,j)/ <= 1, for all /i,j/.
--
--   This follows from the maximal property of the selected pivots, which also
--   leads to a better numerical stability of the algorithm.
--
--   Example:
--
-- >          ( 1 2 0 )     ( 2 0  2 )   (   1 0 0 )   ( 0 0 1 )
-- >          ( 0 2 1 )     ( 0 2 -1 )   ( 1/2 1 0 )   ( 1 0 0 )
-- > luDecomp ( 2 0 2 ) = ( ( 0 0  2 ) , (   0 1 1 ) , ( 0 1 0 ) , 1 )
luDecomp :: (Ord a, Fractional a) => Matrix a -> (Matrix a,Matrix a,Matrix a,a)
luDecomp a = recLUDecomp a i i 1 1 n
 where
  i = (identity $ nrows a)
  n = min (nrows a) (ncols a)

recLUDecomp ::  (Ord a, Fractional a)
            =>  Matrix a -- ^ U
            ->  Matrix a -- ^ L
            ->  Matrix a -- ^ P
            ->  a        -- ^ d
            ->  Int      -- ^ Current row
            ->  Int      -- ^ Total rows
            -> (Matrix a,Matrix a,Matrix a,a)
recLUDecomp u l p d k n =
    if k > n then (u,l,p,d)
    else recLUDecomp u'' l'' p' d' (k+1) n
 where
  -- Pivot strategy: maximum value in absolute value below the current row.
  i  = maximumBy (\x y -> compare (abs $ u ! (x,k)) (abs $ u ! (y,k))) [ k .. n ]
  -- Switching to place pivot in current row.
  u' = switchRows k i u
  l' = M (nrows l) (ncols l) $
       V.modify (\mv -> mapM_ (\j -> do
         msetElem (l ! (k,j)) (ncols l) (i,j) mv
         msetElem (l ! (i,j)) (ncols l) (k,j) mv
           ) [1 .. k-1] ) $ mvect l
  p' = switchRows k i p
  -- Permutation determinant
  d' = if i == k then d else negate d
  -- Cancel elements below the pivot.
  (u'',l'') = go u' l' (k+1)
  ukk = u' ! (k,k)
  go u_ l_ j =
    if j > nrows u_
    then (u_,l_)
    else let x = (u_ ! (j,k)) / ukk
         in  go (combineRows j (-x) k u_) (setElem x (j,k) l_) (j+1)

-- | Matrix LU decomposition with /complete pivoting/.
--   The result for a matrix /M/ is given in the format /(U,L,P,Q,d,e)/ where:
--
--   * /U/ is an upper triangular matrix.
--
--   * /L/ is an /unit/ lower triangular matrix.
--
--   * /P,Q/ is a permutation matrix.
--
--   * /d,e/ is the determinant of /P,Q/.
--
--   * /PMQ = LU/.
--
--   These properties are only guaranteed when the input matrix is invertible.
--   An additional property matches thanks to the strategy followed for pivoting:
--
--   * /L_(i,j)/ <= 1, for all /i,j/.
--
--   This follows from the maximal property of the selected pivots, which also
--   leads to a better numerical stability of the algorithm.
--
--   Example:
--
-- >           ( 1 0 )     ( 2 1 )   (   1    0 0 )   ( 0 0 1 )
-- >           ( 0 2 )     ( 0 2 )   (   0    1 0 )   ( 0 1 0 )   ( 1 0 )
-- > luDecomp' ( 2 1 ) = ( ( 0 0 ) , ( 1/2 -1/4 1 ) , ( 1 0 0 ) , ( 0 1 ) , -1 , 1 )
luDecomp' :: (Ord a, Fractional a) => Matrix a -> (Matrix a,Matrix a,Matrix a,Matrix a,a,a)
luDecomp' a = recLUDecomp' a i i (identity $ ncols a) 1 1 1 n
 where
  i = identity $ nrows a
  n = min (nrows a) (ncols a)

recLUDecomp' ::  (Ord a, Fractional a)
            =>  Matrix a -- ^ U
            ->  Matrix a -- ^ L
            ->  Matrix a -- ^ P
            ->  Matrix a -- ^ Q
            ->  a        -- ^ d
            ->  a        -- ^ e
            ->  Int      -- ^ Current row
            ->  Int      -- ^ Total rows
            -> (Matrix a,Matrix a,Matrix a,Matrix a,a,a)
recLUDecomp' u l p q d e k n =
    if k > n || u'' ! (k, k) == 0
    then (u,l,p,q,d,e)
    else recLUDecomp' u'' l'' p' q' d' e' (k+1) n
 where
  -- Pivot strategy: maximum value in absolute value below the current row & col.
  (i, j) = maximumBy (comparing (\(i0, j0) -> abs $ u ! (i0,j0)))
           [ (i0, j0) | i0 <- [k .. nrows u], j0 <- [k .. ncols u] ]
  -- Switching to place pivot in current row.
  u' = switchCols k j $ switchRows k i u
  l'0 = M (nrows l) (ncols l) $
        V.modify (\mv -> forM_ [1..k-1] $ \ h -> do
                     msetElem (l ! (k,h)) (ncols l) (i,h) mv
                     msetElem (l ! (i,h)) (ncols l) (k,h) mv
                 )
        $ mvect l
  l'  = M (nrows l) (ncols l) $
        V.modify (\mv -> forM_ [1..k-1] $ \h -> do
                     msetElem (l'0 ! (h,k)) (ncols l) (h,i) mv
                     msetElem (l'0 ! (h,i)) (ncols l) (h,k) mv
                 )
        $ mvect l'0
  p' = switchRows k i p
  q' = switchCols k j q
  -- Permutation determinant
  d' = if i == k then d else negate d
  e' = if j == k then e else negate e
  -- Cancel elements below the pivot.
  (u'',l'') = go u' l' (k+1)
  ukk = u' ! (k,k)
  go u_ l_ h =
    if h > nrows u_
    then (u_,l_)
    else let x = (u_ ! (h,k)) / ukk
         in  go (combineRows h (-x) k u_) (setElem x (h,k) l_) (h+1)

-------------------------------------------------------
-------------------------------------------------------
---- PROPERTIES

{-# RULES
"matrix/traceOfSum"
    forall a b. trace (a + b) = trace a + trace b

"matrix/traceOfScale"
    forall k a. trace (scaleMatrix k a) = k * trace a
  #-}

-- | Sum of the elements in the diagonal. See also 'getDiag'.
--   Example:
--
-- >       ( 1 2 3 )
-- >       ( 4 5 6 )
-- > trace ( 7 8 9 ) = 15
trace :: Num a => Matrix a -> a
trace = V.sum . getDiag

-- | Product of the elements in the diagonal. See also 'getDiag'.
--   Example:
--
-- >          ( 1 2 3 )
-- >          ( 4 5 6 )
-- > diagProd ( 7 8 9 ) = 45
diagProd :: Num a => Matrix a -> a
diagProd = V.product . getDiag

-- DETERMINANT

{-# RULES
"matrix/detOfProduct"
    forall a b. detLaplace (a*b) = detLaplace a * detLaplace b

"matrix/detLUOfProduct"
    forall a b. detLU (a*b) = detLU a * detLU b
  #-}

-- | Matrix determinant using Laplace expansion.
--   If the elements of the 'Matrix' are instance of 'Ord' and 'Fractional'
--   consider to use 'detLU' in order to obtain better performance.
detLaplace :: Num a => Matrix a -> a
detLaplace (M 1 1 v) = V.head v
detLaplace m =
    sum [ (-1)^(i-1) * m ! (i,1) * detLaplace (minorMatrix i 1 m) | i <- [1 .. nrows m] ]

-- | Matrix determinant using LU decomposition.
detLU :: (Ord a, Fractional a) => Matrix a -> a
detLU m = d * diagProd u
 where
  (u,_,_,d) = luDecomp m
