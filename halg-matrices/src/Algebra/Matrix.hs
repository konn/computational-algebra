{-# LANGUAGE ConstraintKinds, FlexibleContexts, FlexibleInstances, GADTs   #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses                         #-}
{-# LANGUAGE NoMonomorphismRestriction, TypeFamilies, TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Algebra.Matrix (Matrix(..), delta, companion,
                       gaussReduction, maxNorm, rankWith, det,
                       inverse, inverseWith) where
import           Algebra.Internal
import qualified Algebra.LinkedMatrix as LM
import           Algebra.Prelude.Core hiding (maxNorm, zero)

import           Control.Lens                (both, view, (%~), (&), _3)
import           Control.Monad               (when)
import qualified Data.Matrix                 as DM
import qualified Data.Vector                 as V
import           GHC.Exts                    (Constraint)
import           Numeric.Algebra             (Additive, DecidableZero)
import           Numeric.Algebra             (Monoidal, Multiplicative)
import           Numeric.Algebra             (Unital)
import qualified Numeric.Algebra             as NA
import qualified Numeric.Decidable.Zero      as NA
import qualified Numeric.LinearAlgebra       as LA
import qualified Numeric.LinearAlgebra.Devel as LA
import qualified Prelude                     as P

{-# ANN module "HLint: ignore Redundant bang pattern" #-}

class Matrix mat where
  type Elem mat a :: Constraint
  cmap  :: (Elem mat a, Elem mat b) => (a -> b) -> mat a -> mat b
  empty :: Elem mat b => mat b
  fromLists :: Elem mat a => [[a]] -> mat a
  fromCols  :: Elem mat a => [V.Vector a] -> mat a
  fromCols [] = zero 0 0
  fromCols xs = foldr1 (<||>) $ map colVector xs
  fromRows :: Elem mat a => [V.Vector a] -> mat a
  fromRows [] = zero 0 0
  fromRows xs = foldr1 (<-->) $ map rowVector xs
  toCols :: Elem mat a => mat a -> [V.Vector a]
  toCols m = map (`getCol` m) [1..ncols m]
  toRows :: Elem mat a => mat a -> [V.Vector a]
  toRows m = map (`getRow` m) [1..nrows m]
  ncols :: mat a -> Int
  nrows :: mat a -> Int
  identity :: Elem mat a => Int -> mat a
  diag     :: Elem mat a => V.Vector a -> mat a
  getDiag :: Elem mat a => mat a -> V.Vector a
  trace :: Elem mat a => mat a -> a
  diagProd :: Elem mat a => mat a -> a
  zero :: Elem mat a => Int -> Int -> mat a
  colVector :: Elem mat a => V.Vector a -> mat a
  rowVector :: Elem mat a => V.Vector a -> mat a
  getCol :: Elem mat a => Int -> mat a -> V.Vector a
  getRow :: Elem mat a => Int -> mat a -> V.Vector a
  switchRows :: Elem mat a => Int -> Int -> mat a -> mat a
  scaleRow :: Elem mat a => a -> Int -> mat a -> mat a
  combineRows :: Elem mat a => Int -> a -> Int -> mat a -> mat a
  trans :: Elem mat a => mat a -> mat a
  buildMatrix :: Elem mat a => Int -> Int -> ((Int, Int) -> a) -> mat a
  index :: Elem mat a => Int -> Int -> mat a -> Maybe a
  index i j m = if 1 <= i && i <= nrows m && 1 <= j && j <= ncols m
                then Just $ m ! (i, j)
                else Nothing
  (!) :: Elem mat a => mat a -> (Int, Int) -> a
  (<||>) :: Elem mat a => mat a -> mat a -> mat a
  (<-->) :: Elem mat a => mat a -> mat a -> mat a
  nonZeroRows :: (DecidableZero a, Elem mat a) => mat a -> [Int]
  nonZeroRows = map fst . filter (V.any (not . NA.isZero) . snd) . zip [1..] . toRows
  nonZeroCols :: (DecidableZero a, Elem mat a) => mat a -> [Int]
  nonZeroCols = map fst . filter (V.any (not . NA.isZero) . snd) . zip [1..] . toCols

instance Matrix DM.Matrix where
  type Elem DM.Matrix a = P.Num a
  empty = DM.zero 0 0
  cmap  = fmap
  fromLists = DM.fromLists
  ncols = DM.ncols
  nrows = DM.nrows
  trans = DM.transpose
  identity = DM.identity
  diag v = DM.matrix (V.length v) (V.length v) $ \(i, j) ->
    if i == j then v V.! (i-1) else 0
  getDiag = DM.getDiag
  trace = DM.trace
  diagProd = DM.diagProd
  zero = DM.zero
  colVector = DM.colVector
  rowVector = DM.rowVector
  getCol = DM.getCol
  getRow = DM.getRow
  switchRows = DM.switchRows
  combineRows = DM.combineRows
  scaleRow = DM.scaleRow
  buildMatrix = DM.matrix
  (!) = (DM.!)
  (<||>) = (DM.<|>)
  (<-->) = (DM.<->)

swapIJ :: Eq a => a -> a -> a -> a
swapIJ i j k
  | k == i = j
  | k == j = i
  | otherwise = k

instance Matrix LA.Matrix where
  type Elem LA.Matrix a = (P.Num a, LA.Numeric  a, LA.Element a, LA.Container LA.Vector a)
  empty = LA.fromLists [[]]
  fromLists = LA.fromLists
  cmap = LA.cmap
  ncols = LA.cols
  nrows = LA.rows
  trans = LA.tr
  identity = LA.ident
  fromCols = LA.fromColumns . map (LA.fromList . V.toList)
  diag = LA.diag . LA.fromList . V.toList
  getDiag = V.fromList . LA.toList . LA.takeDiag
  trace = LA.sumElements . LA.takeDiag
  diagProd = LA.prodElements . LA.takeDiag
  zero i j = LA.konst 0 (i, j)
  colVector = LA.asColumn . LA.fromList . V.toList
  rowVector = LA.asRow . LA.fromList . V.toList
  toCols = map (V.fromList . LA.toList) . LA.toColumns
  toRows = map (V.fromList . LA.toList) . LA.toRows
  getCol i = V.fromList . LA.toList . (!! (i - 1)) . LA.toColumns
  getRow i = V.fromList . LA.toList . (!! (i - 1)) . LA.toRows
  switchRows i j m = m LA.? map (swapIJ (i-1) (j-1)) [0.. nrows m - 1]
  combineRows j s i m = LA.mapMatrixWithIndex (\(k,l) v -> if k == j - 1 then s P.* (m ! (i,l+1)) P.+ v else v) m
  buildMatrix w h f = LA.build (w, h) (\i j -> f (toIntLA i+1, toIntLA j+1))
  scaleRow a i = (fst .) $ LA.mutable $ \(k, l) m -> do
    v <- LA.readMatrix m k l
    when (k == i - 1) $
      LA.writeMatrix m k l (a P.* v)
  m ! (i, j) = m `LA.atIndex` (i - 1, j - 1)
  m <||> n = LA.fromColumns $ LA.toColumns m ++ LA.toColumns n
  m <--> n = LA.fromRows $ LA.toRows m ++ LA.toRows n

toIntLA :: LA.Container LA.Matrix e => e -> Int
toIntLA e = fromIntegral $ LA.toZ ((1 LA.>< 1) [e]) `LA.atIndex` (0, 0)

instance Matrix LM.Matrix where
  type Elem LM.Matrix a = (CoeffRing a, Unital a, Monoidal a, Multiplicative a, Additive a)
  cmap = LM.cmap
  (!) m pos = m LM.! (pos & both %~ pred)
  index i j = LM.index (i-1) (j-1)
  empty = LM.empty
  buildMatrix h w f = LM.fromList [((i, j), f (i,j)) | j <- [1..w], i <- [1..h]]
  trans = LM.transpose
  combineRows j s i = LM.combineRows s (i-1) (j-1)
  switchRows i j = LM.switchRows (i-1) (j-1)
  scaleRow a i = LM.scaleRow a (pred i)
  zero = LM.zeroMat
  identity = LM.identity
  diag = LM.diag
  getDiag = LM.getDiag
  diagProd = LM.diagProd
  trace = LM.trace
  getRow = LM.getRow . pred
  getCol = LM.getCol . pred
  nrows = LM.nrows
  ncols = LM.ncols
  fromLists = LM.fromLists
  (<||>) = (LM.<||>)
  (<-->) = (LM.<-->)
  rowVector = LM.rowVector
  colVector = LM.colVector
  nonZeroRows = LM.nonZeroRows
  nonZeroCols = LM.nonZeroCols

delta :: (NA.Monoidal r, NA.Unital r) => Int -> Int -> r
delta i j | i == j = NA.one
          | otherwise = NA.zero

companion :: (KnownNat n, CoeffRing r, Matrix mat,
              Elem mat r, IsMonomialOrder n ord)
          => Ordinal n -> OrderedPolynomial r ord n -> mat r
companion odn poly =
  let deg = totalDegree' poly
      vx  = leadingMonomial (var odn `asTypeOf` poly)
  in buildMatrix deg deg $ \(j, k) ->
  if 1 <= k && k <= deg - 1
  then delta j (k+1)
  else NA.negate $ coeff (NA.pow vx (fromIntegral $ j-1 :: NA.Natural)) poly

-- | @gaussReduction a = (a', p)@ where @a'@ is row echelon form and @p@ is pivoting matrix.
gaussReduction :: (Matrix mat, Elem mat a, Normed a, Eq a, NA.Field a)
               => mat a -> (mat a, mat a)
gaussReduction mat =
  let (a, b, _) = gaussReduction' mat in (a, b)

-- | @gaussReduction a = (a', p)@ where @a'@ is row echelon form and @p@ is pivoting matrix.
gaussReduction' :: (Matrix mat, Elem mat a, Normed a, Eq a, NA.Field a)
               => mat a -> (mat a, mat a, a)
gaussReduction' mat = {-# SCC "gaussRed" #-} go 1 1 mat (identity $ nrows mat) NA.one
  where
    go i j a p acc
      | i > nrows mat || j > ncols mat = (a, p, acc)
      | otherwise =
        let (k, new) = maximumBy (comparing $ norm . snd) [(l, a ! (l, j)) | l <- [i..nrows mat]]
        in if new == NA.zero
           then go i (j + 1) a p NA.zero
           else let prc l a0 p0
                      | l == i = prc (l+1) a0 p0
                      | l > nrows mat = (a0, p0)
                      | otherwise     =
                        let coe = NA.negate (a0 ! (l, j))
                            a'' = combineRows l coe i a0
                            p'' = combineRows l coe i p0
                        in prc (l+1) a'' p''
                    (a', p') = prc 1 (scaleRow (NA.recip new) i $ switchRows i k a)
                                     (scaleRow (NA.recip new) i $ switchRows i k p)
                    offset = if i == k then id else NA.negate
                in go (i+1) (j+1) a' p' (offset $ acc NA.* new)

det :: (Elem mat a, Eq a, NA.Field a, Normed a, Matrix mat)
    => mat a -> a
det = view _3 . gaussReduction'

maxNorm :: (Elem mat a, Normed a, Matrix mat) => mat a -> Norm a
maxNorm = maximum . concat . map (map norm . V.toList) . toRows

rankWith :: (Elem mat r, CoeffRing r, Matrix mat)
         => (mat r -> mat r) -> mat r -> Int
rankWith gauss = length . nonZeroRows . gauss

inverse :: (Elem mat a, Eq a, NA.Field a, Normed a, Matrix mat)
        => mat a -> mat a
inverse = snd . gaussReduction

inverseWith :: (mat a -> (mat a, mat a)) -> mat a -> mat a
inverseWith = (snd .)
