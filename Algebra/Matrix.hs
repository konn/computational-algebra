{-# LANGUAGE ConstraintKinds, FlexibleInstances, GADTs, KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses, TypeFamilies, TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Algebra.Matrix (Matrix(..), mapSM, delta, companion) where
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Algebra.Wrapped             ()
import           Control.Lens
import qualified Data.Matrix                 as DM
import           Data.Maybe
import           Data.Singletons             (SingRep (..))
import           Data.Type.Ordinal
import qualified Data.Vector                 as V
import qualified Data.Vector.Generic         as GV
import           Data.Vector.Hybrid.Internal
import qualified Numeric.Algebra             as NA
import qualified Numeric.LinearAlgebra       as LA
import           Sparse.Matrix               (keys, _Mat)
import qualified Sparse.Matrix               as SM

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
  trans :: Elem mat a => mat a -> mat a
  buildMatrix :: Elem mat a => Int -> Int -> ((Int, Int) -> a) -> mat a
  index :: Elem mat a => Int -> Int -> mat a -> Maybe a
  index i j m = if 1 <= i && i <= nrows m && 1 <= j && j <= ncols m
                then Just $ m ! (i, j)
                else Nothing
  (!) :: Elem mat a => mat a -> (Int, Int) -> a
  (<||>) :: Elem mat a => mat a -> mat a -> mat a
  (<-->) :: Elem mat a => mat a -> mat a -> mat a

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
  buildMatrix = DM.matrix
  (!) = (DM.!)
  (<||>) = (DM.<|>)
  (<-->) = (DM.<->)

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
  buildMatrix w h f = LA.buildMatrix w h (\(i, j) -> f (i-1, j-1))
  m ! (i, j) = m LA.@@> (i - 1, j - 1)
  m <||> n = LA.fromColumns $ LA.toColumns m ++ LA.toColumns n
  m <--> n = LA.fromRows $ LA.toRows m ++ LA.toRows n

mapSM :: (SM.Vectored a, SM.Vectored b) => (a -> b) -> SM.Mat a -> SM.Mat b
mapSM f m =
  case m ^._Mat of
    V ks as  -> V ks (GV.fromList $ map f $ GV.toList as) ^.from _Mat

instance Matrix SM.Mat where
  type Elem SM.Mat a = (Num a, SM.Vectored a)
  cmap = mapSM
  empty = SM.fromList []
  fromLists = SM.fromList . concat. zipWith (\i -> zipWith (\j v -> (SM.Key i j, v)) [0..]) [0..]
  nrows m = maybe 0 (succ . fromIntegral) $ maximumOf (traverse._1) $ m^.keys.to GV.toList
  ncols m = maybe 0 (succ . fromIntegral) $ maximumOf (traverse._2) $ m^.keys.to GV.toList
  identity = SM.ident
  diag v = SM.fromList [ (SM.Key (fromIntegral i) (fromIntegral i), v V.! i) | i <- [0.. V.length v - 1]]
  getDiag m =
    let s = fromIntegral $ min (nrows m) (ncols m)
    in V.fromList [ fromMaybe 0 $ m ^? ix (SM.Key i i) | i <- [1..s] ]
  trace = V.sum . getDiag
  diagProd = V.product . getDiag
  zero n m = SM.fromList []
  colVector v = SM.fromList [(SM.Key (fromIntegral i) 0, v V.! i) | i <- [0..V.length v - 1]]
  rowVector v = SM.fromList [(SM.Key 0 (fromIntegral i), v V.! i) | i <- [0..V.length v - 1]]
  getCol j m = V.fromList $ [ fromMaybe 0 $ m ^? ix (SM.Key (fromIntegral i) (fromIntegral (j-1)))
                            | i <- [0..nrows m - 1]]
  getRow i m = V.fromList $ [ fromMaybe 0 $ m ^? ix (SM.Key (fromIntegral (i-1)) (fromIntegral j))
                            | j <- [0..ncols m - 1]]
  trans = SM.transpose
  buildMatrix h w f = SM.fromList [(SM.Key (fromIntegral $ i-1) (fromIntegral $ j-1), f (i,j))
                                  | i <- [1..h], j <- [1..w]]
  m ! (i, j) = fromMaybe 0 $ m ^? ix (SM.Key (fromIntegral i - 1) (fromIntegral j - 1))
  m <||> n = SM.addWith (+) m (n & keys %~ GV.map (_2 %~ (+ (fromIntegral $ ncols m))))
  m <--> n = SM.addWith (+) m (n & keys %~ GV.map (_1 %~ (+ (fromIntegral $ nrows m))))

delta :: (NA.Monoidal r, NA.Unital r) => Int -> Int -> r
delta i j | i == j = NA.one
          | otherwise = NA.zero

companion :: (SingRep n, NoetherianRing r, Matrix mat, Eq r,
              Elem mat r, IsMonomialOrder ord)
          => Ordinal n -> OrderedPolynomial r ord n -> mat r
companion on poly =
  let deg = totalDegree' poly
      vx  = leadingMonomial (var on `asTypeOf` poly)
  in buildMatrix deg deg $ \(j, k) ->
  if 1 <= k && k <= deg - 1
  then delta j (k+1)
  else NA.negate $ coeff (NA.pow vx (fromIntegral $ j-1 :: NA.Natural)) poly

instance SM.Vectored Rational where
  type Vec Rational = V.Vector

instance SM.Eq0 Rational where
