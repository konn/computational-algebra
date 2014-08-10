{-# LANGUAGE ConstraintKinds, FlexibleContexts, FlexibleInstances, GADTs   #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses                         #-}
{-# LANGUAGE NoMonomorphismRestriction, TypeFamilies, TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Algebra.Matrix (Matrix(..), mapSM, delta, companion, Sparse(..),
                       gaussReduction, maxNorm, intDet, rankWith, det,
                       inverse, inverseWith) where
import           Algebra.Field.Finite
import qualified Algebra.LinkedMatrix             as LM
import           Algebra.Ring.Polynomial
import           Algebra.Wrapped                  (Normed (..))
import           Control.Arrow
import           Control.Lens
import           Data.Complex
import qualified Data.IntSet                      as IS
import           Data.List
import qualified Data.Matrix                      as DM
import           Data.Maybe
import           Data.Numbers.Primes
import           Data.Ord
import           Data.Singletons                  (SingI)
import           Data.Type.Ordinal
import qualified Data.Vector                      as V
import qualified Data.Vector.Algorithms.Insertion as Sort
import qualified Data.Vector.Generic              as GV
import qualified Data.Vector.Hybrid               as H
import           Data.Vector.Hybrid.Internal
import           Numeric.Algebra                  (Additive, DecidableZero)
import           Numeric.Algebra                  (Monoidal, Multiplicative)
import           Numeric.Algebra                  (Ring, Unital)
import qualified Numeric.Algebra                  as NA
import qualified Numeric.Decidable.Zero           as NA
import           Numeric.Domain.Euclidean         (chineseRemainder)
import           Numeric.Field.Fraction
import qualified Numeric.LinearAlgebra            as LA
import           Sparse.Matrix                    (_Mat)
import qualified Sparse.Matrix                    as SM

class Matrix mat where
  type Elem mat a
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
  nonZeroRows :: (NA.DecidableZero a, Elem mat a) => mat a -> [Int]
  nonZeroRows = map fst . filter (V.any (not . NA.isZero) . snd) . zip [1..] . toRows
  nonZeroCols :: (NA.DecidableZero a, Elem mat a) => mat a -> [Int]
  nonZeroCols = map fst . filter (V.any (not . NA.isZero) . snd) . zip [1..] . toCols

instance Matrix DM.Matrix where
  type Elem DM.Matrix a = Num a
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
swapIJ i j k = if k == i then j else if k == j then i else k

instance Matrix LA.Matrix where
  type Elem LA.Matrix a = (Num a, LA.Element a, LA.Container LA.Vector a)
  empty = LA.fromLists [[]]
  fromLists = LA.fromLists
  cmap = LA.cmap
  ncols = LA.cols
  nrows = LA.rows
  trans = LA.trans
  identity = LA.ident
  fromCols = LA.fromColumns . map (LA.fromList . V.toList)
  diag = LA.diag . LA.fromList . V.toList
  getDiag = V.fromList . LA.toList . LA.takeDiag
  trace = LA.sumElements . LA.takeDiag
  diagProd = LA.prodElements . LA.takeDiag
  zero i j = LA.buildMatrix i j (const 0)
  colVector = LA.asColumn . LA.fromList . V.toList
  rowVector = LA.asRow . LA.fromList . V.toList
  toCols = map (V.fromList . LA.toList) . LA.toColumns
  toRows = map (V.fromList . LA.toList) . LA.toRows
  getCol i = V.fromList . LA.toList . (!! (i - 1)) . LA.toColumns
  getRow i = V.fromList . LA.toList . (!! (i - 1)) . LA.toRows
  switchRows i j m = LA.extractRows (map (swapIJ (i-1) (j-1)) [0.. nrows m - 1]) m
  combineRows j s i m = LA.mapMatrixWithIndex (\(k,l) v -> if k == j - 1 then s * (m ! (i,l+1)) + v else v) m
  buildMatrix w h f = LA.buildMatrix w h (\(i, j) -> f (i-1, j-1))
  scaleRow a i = LA.mapMatrixWithIndex (\(k, l) v -> if k == i - 1 then a * v else v)
  m ! (i, j) = m LA.@@> (i - 1, j - 1)
  m <||> n = LA.fromColumns $ LA.toColumns m ++ LA.toColumns n
  m <--> n = LA.fromRows $ LA.toRows m ++ LA.toRows n

mapSM :: (SM.Vectored a, SM.Vectored b) => (a -> b) -> SM.Mat a -> SM.Mat b
mapSM f m =
  case m ^._Mat of
    V ks as  -> V ks (GV.fromList $ map f $ GV.toList as) ^.from _Mat

data Sparse r = Sparse { rawSM :: !(SM.Mat r)
                       , cols  :: !Int
                       , rows  :: !Int
                       }

instance (SM.Vectored a, SM.Eq0 a) => Num (Sparse a) where
  {-# SPECIALIZE instance Num (Sparse Int) #-}
  {-# SPECIALIZE instance Num (Sparse Double) #-}
  {-# SPECIALIZE instance Num (Sparse (Complex Double)) #-}
  Sparse m r _ * Sparse n _ c = Sparse (m * n) r c
  {-# INLINE (*) #-}
  abs (Sparse m r c) = Sparse (m & over each abs) r c
  {-# INLINE abs #-}
  signum (Sparse m r c) = Sparse (m & over each signum) r c
  {-# INLINE signum #-}
  negate (Sparse m r c) = Sparse (m & over each negate) r c
  {-# INLINE negate #-}
  fromInteger _ = error "Sparse: fromInteger"
  {-# INLINE fromInteger #-}
  Sparse m r c + Sparse n r' c' = Sparse (m + n) (max r r') (max c c')
  {-# INLINE (+) #-}
  Sparse m r c - Sparse n r' c' = Sparse (m - n) (max r r') (max c c')
  {-# INLINE (-) #-}

instance (SM.Vectored a, Show a) => Show (Sparse a) where
  showsPrec d = showsPrec d . rawSM

instance Matrix LM.Matrix where
  type Elem LM.Matrix a = (DecidableZero a, Unital a, Monoidal a, Multiplicative a, Additive a)
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

instance Matrix Sparse where
  type Elem Sparse a = (Num a, SM.Vectored a, SM.Eq0 a)
  cmap f (Sparse raw nc nr) = Sparse (mapSM f raw) nc nr
  empty = Sparse (SM.fromList []) 0 0
  fromLists ls =
    Sparse (SM.fromList . concat. zipWith (\i -> zipWith (\j v -> (SM.Key i j, v)) [0..]) [0..] $ ls)
    (length ls) (maximum $ map length ls)
  nrows (Sparse _ _ r) = r
  ncols (Sparse _ c _) = c
  identity n = Sparse (SM.ident n) n n
  diag v = Sparse (SM.fromList [ (SM.Key (fromIntegral i) (fromIntegral i), v V.! i) | i <- [0.. V.length v - 1]])
             (V.length v) (V.length v)
  getDiag (Sparse m r c) =
    let s = fromIntegral $ min r c
    in V.fromList [ fromMaybe 0 $ m ^? ix (SM.Key i i) | i <- [1..s] ]
  trace = V.sum . getDiag
  diagProd = V.product . getDiag
  zero n m = Sparse (SM.fromList []) n m
  colVector v = Sparse (SM.fromList [(SM.Key (fromIntegral i) 0, v V.! i) | i <- [0..V.length v - 1]]) (V.length v) 1
  rowVector v = Sparse (SM.fromList [(SM.Key 0 (fromIntegral i), v V.! i) | i <- [0..V.length v - 1]]) 1 (V.length v)
  switchRows i j = wrapSM $ modifyKey $ _1 %~ swapIJ (fromIntegral i - 1) (fromIntegral j - 1)
  combineRows j s i spm = flip wrapSM spm $ \m ->
    m & _Mat %~ H.map (\(SM.Key k l, v) -> (SM.Key k l,
                                            if k == fromIntegral j - 1
                                            then s * (spm ! (i, fromIntegral l+1)) + v
                                            else v))
  scaleRow a i = wrapSM $ _Mat %~ H.map (\(key@(SM.Key l _), v) -> (key, if l == fromIntegral i - 1 then a * v else v))
  getCol j (Sparse m rs _) = V.fromList $ [ fromMaybe 0 $ m ^? ix (SM.Key (fromIntegral i) (fromIntegral (j-1)))
                                          | i <- [0..rs - 1]]
  getRow i (Sparse m _ cs) = V.fromList $ [ fromMaybe 0 $ m ^? ix (SM.Key (fromIntegral (i-1)) (fromIntegral j))
                                          | j <- [0..cs - 1]]
  trans (Sparse m r c) = Sparse (SM.transpose m) c r
  buildMatrix h w f = Sparse (SM.fromList [(SM.Key (fromIntegral $ i-1) (fromIntegral $ j-1), f (i,j))
                                          | i <- [1..h], j <- [1..w]]) h w
  Sparse m _ _ ! (i, j) = fromMaybe 0 $ m ^? ix (SM.Key (fromIntegral i - 1) (fromIntegral j - 1))
  Sparse m r c1 <||> Sparse n r' c2 =
    Sparse (m + modifyKey (_2 %~ (+ fromIntegral c1)) n) (max r r') (c1 + c2)
  Sparse m r1 c <--> Sparse n r2 c' =
    Sparse (m + modifyKey (_1 %~ (+ fromIntegral r1)) n) (r1 + r2) (max c c')
  nonZeroRows (Sparse mat _ _) = IS.toList $ IS.fromList $ map (succ . fromIntegral) (mat ^.. SM.keys.each._1)
  nonZeroCols (Sparse mat _ _) = IS.toList $ IS.fromList $ map (succ . fromIntegral) (mat ^.. SM.keys.each._2)

modifyKey :: (SM.Vectored a) => (SM.Key -> SM.Key) -> SM.Mat a -> SM.Mat a
modifyKey f m =
  m & _Mat %~ H.modify (Sort.sortBy (comparing fst)). H.map (first f)

wrapSM :: (SM.Mat a -> SM.Mat b) -> Sparse a -> Sparse b
wrapSM f (Sparse m r c) = Sparse (f m) r c

delta :: (NA.Monoidal r, NA.Unital r) => Int -> Int -> r
delta i j | i == j = NA.one
          | otherwise = NA.zero

companion :: (SingI n, DecidableZero r, Matrix mat, Eq r,
              Elem mat r, IsMonomialOrder ord, Ring r)
          => Ordinal n -> OrderedPolynomial r ord n -> mat r
companion on poly =
  let deg = totalDegree' poly
      vx  = leadingMonomial (var on `asTypeOf` poly)
  in buildMatrix deg deg $ \(j, k) ->
  if 1 <= k && k <= deg - 1
  then delta j (k+1)
  else NA.negate $ coeff (NA.pow vx (fromIntegral $ j-1 :: NA.Natural)) poly

instance SM.Vectored (Fraction Integer) where
  type Vec (Fraction Integer) = V.Vector

instance SM.Eq0 (Fraction Integer)

-- | @gaussReduction a = (a', p)@ where @a'@ is row echelon form and @p@ is pivoting matrix.
gaussReduction :: (Matrix mat, Elem mat a, Normed a, Ord (Norm a), Eq a, NA.Field a)
               => mat a -> (mat a, mat a)
gaussReduction mat =
  let (a, b, _) = gaussReduction' mat in (a, b)

-- | @gaussReduction a = (a', p)@ where @a'@ is row echelon form and @p@ is pivoting matrix.
gaussReduction' :: (Matrix mat, Elem mat a, Normed a, Ord (Norm a), Eq a, NA.Field a)
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

det :: (Elem mat a, Eq a, Ring a, NA.Division a, NA.Commutative a, Normed a, Matrix mat)
    => mat a -> a
det = view _3 . gaussReduction'

maxNorm :: (Elem mat a, Normed a, Matrix mat) => mat a -> Norm a
maxNorm = maximum . concat . map (map norm . V.toList) . toRows

rankWith :: (Elem mat r, DecidableZero r, Matrix mat)
         => (mat r -> mat r) -> mat r -> Int
rankWith gauss = length . nonZeroRows . gauss

intDet :: LM.Matrix Integer -> Integer
intDet mat =
  let b = maxNorm mat
      n = fromIntegral $ ncols mat
      c = n^(n `div` 2) * b^n
      r = ceiling $ logBase (2 :: Double) (2*fromIntegral c + 1)
      ps = take (fromInteger r) primes
      m  = product ps
      d  = chineseRemainder [ (p,
                               reifyPrimeField p $ \pxy ->
                               shiftHalf p $ naturalRepr $ view _3 $
                               gaussReduction' (cmap (modNat' pxy) mat))
                            | p <- ps]
      off = d `div` m
  in if d == 0
     then 0
     else minimumBy (comparing abs) [d - m * off, d - m * (off + 1)]

inverse :: (Elem mat a, Eq a, Ring a, NA.Division a, NA.Commutative a, Normed a, Matrix mat)
        => mat a -> mat a
inverse = snd . gaussReduction

inverseWith :: (mat a -> (mat a, mat a)) -> mat a -> mat a
inverseWith = (snd .)

shiftHalf :: Integral a => a -> a -> a
shiftHalf p n =
  let s = p `div` 2
  in (n + s) `mod` p - s
