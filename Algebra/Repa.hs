{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction, TypeFamilies                    #-}
module Algebra.Repa where
import           Algebra.Wrapped
import           Control.Applicative
import           Control.Arrow
import           Data.Array.Repa                   hiding (map)
import           Data.Array.Repa.Algorithms.Matrix
import           Data.Array.Repa.Eval
import           Data.Array.Repa.Repr.Vector
import           Data.List                         (maximumBy)
import           Data.Ord
import           Data.Ratio
import qualified Data.Vector                       as V

type Matrix a = Array (DefVec a) DIM2 a

type family DefVec a
type instance DefVec Double  = U
type instance DefVec Integer = V
type instance DefVec Rational = V

instance Elt Rational where
  zero = 0
  one  = 1
  touch r = touch (fromInteger $ numerator r :: Int) >> touch (fromInteger $ denominator r :: Int)

switchRows :: (Source r e) => Int -> Int -> Array r DIM2 e -> Array D DIM2 e
switchRows i j m = backpermute (extent m) swap m
  where
    swap (Z :. k :. l)
      | k == i = j >< l
      | k == j = i >< l
      | otherwise = k >< l

(><) :: Int -> Int -> DIM2
i >< j = Z :. i :. j

toRows :: Source r e => Array r DIM2 e -> [V.Vector e]
toRows m = [ getRow i m | i <- [0..nrows m-1]]

switchCols :: (Source r e) => Int -> Int -> Array r DIM2 e -> Array D DIM2 e
switchCols i j m = backpermute (extent m) swap m
  where
    swap (Z :. l :. k)
      | k == i = Z :. l :. j
      | k == j = Z :. l :. i
      | otherwise = Z :. l :. k

getCol :: Source r e => Int -> Array r DIM2 e -> V.Vector e
getCol i m = V.fromList $ toList $ slice m (Z :. i :. All)

getRow :: Source r e => Int -> Array r DIM2 e -> V.Vector e
getRow j m = V.fromList $ toList $ slice m (Z :. j :. All)

scaleRow :: (Source r a, Num a) => a -> Int -> Array r DIM2 a -> Array D DIM2 a
scaleRow a i m = traverse m id scale
  where
    scale f (Z :. k :. l)
      | k == i = a * f (k >< l)
      | otherwise = f (k >< l)

combineRows :: (Source r a, Num a) => Int -> a -> Int -> Array r DIM2 a -> Array D DIM2 a
combineRows i a j m = traverse m id comb
  where
    comb f (Z :. k :. l)
      | k == i = f (k >< l) + a * f (j >< l)
      | otherwise = f (k >< l)

identity :: (Num e, Target r2 e) => Int -> Array r2 DIM2 e
identity n = computeS $ fromFunction (n >< n) $ \(Z :. i :. j) -> if i == j then 1 else 0

fromLists :: (Target (DefVec a) a) => [[a]] -> Array (DefVec a) DIM2 a
fromLists xss =
  fromList (length xss >< maximum (map length xss)) $ concat xss

ncols :: Source r e => Array r DIM2 e -> Int
ncols = col . extent

nrows :: Source r e => Array r DIM2 e -> Int
nrows = row . extent

gaussReductionP :: (Eq e, Fractional e, Monad m, Normed e, Source r e, Target r e, Elt e)
                => Array r DIM2 e -> m (Array r DIM2 e, Array r DIM2 e)
gaussReductionP mat = {-# SCC "repaGauss" #-} mat `deepSeqArray` go 0 0 mat (identity $ nrows mat)
  where
    go i j a p
      | i >= nrows mat || j >= ncols mat = return (a, p)
      | otherwise = do
        let (k, new) =  maximumBy (comparing $ norm . snd) [(l, a ! (l >< j)) | l <- [i..nrows mat-1]]
        if new == zero
          then go i (j + 1) a p
          else do
          let prc l a0 p0
                | l == i = prc (l+1) a0 p0
                | l >= nrows mat = (a0, p0)
                | otherwise     =
                  let coe = negate (a0 ! (l >< j))
                  in prc (l+1) (combineRows l coe i a0) (combineRows l coe i p0)
              (a', p') = prc 0
                         (scaleRow (recip new) i $ switchRows i k a)
                         (scaleRow (recip new) i $ switchRows i k p)
          a'' <- computeP a'
          p'' <- computeP p'
          go (i+1) (j+1) a'' p''
