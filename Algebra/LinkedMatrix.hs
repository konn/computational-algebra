{-# LANGUAGE BangPatterns, FlexibleContexts, MultiParamTypeClasses        #-}
{-# LANGUAGE NamedFieldPuns, NoImplicitPrelude, NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, TemplateHaskell             #-}
module Algebra.LinkedMatrix where
import           Control.Applicative        ((<$>))
import           Control.Lens
import           Control.Monad              (zipWithM)
import           Control.Monad              (forM)
import           Control.Monad.Identity     (runIdentity)
import           Control.Monad.State.Strict (runState)
import           Data.IntMap                (empty)
import           Data.IntMap.Strict         (IntMap)
import           Data.IntMap.Strict         (insertWith)
import           Data.IntMap.Strict         (alter)
import qualified Data.IntMap.Strict         as IM
import           Data.Vector                (Vector)
import           Data.Vector                (create)
import qualified Data.Vector                as V
import qualified Data.Vector.Mutable        as MV
import           Numeric.Algebra
import           Numeric.Decidable.Zero     (isZero)
import           Prelude                    hiding (Num (..))

data Entry a = Entry { _value   :: !a
                     , _idx     :: !(Int, Int)
                     , _rowNext :: !(Maybe Int)
                     , _colNext :: !(Maybe Int)
                     } deriving (Read, Show, Eq, Ord)

makeLenses ''Entry

data Matrix a = Matrix { _coefficients :: !(Vector (Entry a))
                       , _rowStart     :: !(IntMap Int)
                       , _colStart     :: !(IntMap Int)
                       , _height       :: !Int
                       , _width        :: !Int
                       } deriving (Read, Show, Eq, Ord)

makeLenses ''Matrix

data BuildState = BuildState { _colMap :: !(IntMap [Int])
                             , _rowMap :: !(IntMap [Int])
                             , _curIdx :: !Int
                             }
makeLenses ''BuildState

fromList :: DecidableZero a => [[a]] -> Matrix a
fromList xss =
  let (as, bs) = runState (zipWithM initialize [0..] xss) (BuildState empty empty (-1))
      vec = V.fromList $ concat as
  in Matrix vec (head <$> _rowMap bs) (head <$> _colMap bs) h w
  where
    h = length xss
    w  = maximum $ map length xss
    initialize i xs = do
      forM (filter (not . isZero . snd) $ zip [0..] xs) $ \(j,c) -> do
        curIdx += 1
        n <- use curIdx
        nc <- use $ colMap.at j
        nr <- use $ rowMap.at i
        colMap %= insertWith (++) j [n]
        rowMap %= insertWith (++) i [n]
        return $ Entry { _value = c
                       , _idx = (i, j)
                       , _rowNext = head <$> nr
                       , _colNext = head <$> nc
                       }
toList :: Monoidal a => Matrix a -> [[a]]
toList mat =
  let orig = replicate (_height mat) $ replicate (_width mat) zero
  in go (V.toList $ _coefficients mat) orig
  where
    go [] m = m
    go (Entry{_value = v, _idx = (i,j) }:es) m =
      go es (m&ix i.ix j .~ v)

swapRows :: Int -> Int -> Matrix a -> Matrix a
swapRows = swapper Row

swapCols :: Int -> Int -> Matrix a -> Matrix a
swapCols = swapper Column

swapper :: Direction -> Int -> Int -> Matrix a -> Matrix a
swapper dir i j mat =
  let ith = IM.lookup i $ mat^.startL dir
      jth = IM.lookup j $ mat^.startL dir
  in  mat & startL dir %~ alter (const jth) i . alter (const ith) j
          & coefficients %~ go ith . go jth
  where
    go Nothing v = v
    go (Just k) vec =
      let !cur = vec V.! k
      in go (cur ^. nextL dir) (vec & ix k . coordL dir %~ change)
    change k | k == i = j
         | k == j = i
         | otherwise = k

scaleRow :: Multiplicative a => a -> Int -> Matrix a -> Matrix a
scaleRow a = mapMat (*a) Row

scaleCol :: Multiplicative a => a -> Int -> Matrix a -> Matrix a
scaleCol a = mapMat (*a) Column

mapMat :: (a -> a) -> Direction
       -> Int -> Matrix a -> Matrix a
mapMat f dir i mat = traverseMatrix mat tr dir i mat
  where
    tr m k _ = m & coefficients . ix k . value %~ f

traverseMatrix :: b -> (b -> Int -> Entry a -> b)
               -> Direction
               -> Int -> Matrix a -> b
traverseMatrix ini f dir i mat =
  runIdentity $  traverseMatrixM ini (\b j e -> return $ f b j e) dir i mat

traverseMatrixM :: Monad m => b -> (b -> Int -> Entry a -> m b)
                -> Direction
                -> Int -> Matrix a -> m b
traverseMatrixM ini f dir i mat = go (IM.lookup i (mat^.startL dir)) ini
  where
    vec = mat ^. coefficients
    go Nothing  b = return b
    go (Just k) b = do
      let !cur = vec V.! k
      go (cur ^. nextL dir) =<< f b k cur

getDir :: Monoidal a
       => Direction -> Int -> Matrix a -> Vector a
getDir dir i mat =
  create $ do
    v <- MV.replicate (mat ^. lenL dir) zero
    traverseMatrixM v trav dir i mat
  where
    trav v _ ent = MV.write v (ent ^. nthL dir) (ent ^. value) >> return v

getRow :: Monoidal a => Int -> Matrix a -> Vector a
getRow = getDir Row
getCol :: Monoidal a => Int -> Matrix a -> Vector a
getCol = getDir Column

data Direction = Row | Column deriving (Read, Show, Eq, Ord)

lenL, countL :: Direction -> Lens' (Matrix a) Int
lenL Row = width
lenL Column = height
countL Row = height
countL Column = width

nthL, coordL :: Direction -> Lens' (Entry a) Int
coordL Row = idx . _1
coordL Column = idx . _2

nthL Row = idx . _2
nthL Column = idx . _1

startL :: Direction -> Lens' (Matrix a) (IntMap Int)
startL Row = rowStart
startL Column = colStart

nextL :: Direction -> Lens' (Entry a) (Maybe Int)
nextL Row    = rowNext
nextL Column = colNext
