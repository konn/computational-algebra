{-# LANGUAGE BangPatterns, FlexibleContexts, LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses, NamedFieldPuns, NoImplicitPrelude   #-}
{-# LANGUAGE NoMonomorphismRestriction, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell                                            #-}
module Algebra.LinkedMatrix where
import           Control.Applicative        ((<$>))
import           Control.Lens               hiding (index)
import           Control.Monad              (forM, zipWithM)
import           Control.Monad.Identity     (runIdentity)
import           Control.Monad.State.Strict (runState)
import           Data.IntMap                (empty)
import           Data.IntMap.Strict         (IntMap, alter, insertWith)
import           Data.IntMap.Strict         (mapMaybeWithKey)
import qualified Data.IntMap.Strict         as IM
import           Data.List                  (sort)
import           Data.Maybe                 (fromJust)
import           Data.Maybe                 (isJust)
import           Data.Maybe                 (mapMaybe)
import           Data.Vector                (Vector, create)
import           Data.Vector                (modify)
import           Data.Vector                (generate)
import qualified Data.Vector                as V
import qualified Data.Vector.Mutable        as MV
import           Numeric.Algebra            hiding ((<), (>))
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

scaleDir :: (DecidableZero a, Multiplicative a) => Direction -> a -> Int -> Matrix a -> Matrix a
scaleDir dir a i mat
  | otherwise = mapDir (*a) dir i mat
  | isZero a  = clearDir dir i mat

clearAt :: Int -> Matrix a -> Matrix a
clearAt k mat = mat & coefficients %~ go
                    & forwardStart Column
                    & forwardStart Row
  where
    !old = ((mat ^. coefficients) V.! k)
           & colNext._Just %~ shifter
           & rowNext._Just %~ shifter
    forwardStart dir =
      let l = (old ^. coordL dir)
      in startL dir %~ mapMaybeWithKey
                       (\d v -> if d == l && v == k
                                then old ^. nextL dir
                                else Just $ shifter v)
    shiftDir sel = nextL sel %~ \case
      Nothing -> Nothing
      Just l ->
        if l == k
        then old ^. nextL sel
        else Just $ shifter l
    shifter n = if n < k then n else n - 1
    go vs = generate (V.length vs - 1) $ \n ->
      vs V.! (if n < k then n else n + 1) & shiftDir Column & shiftDir Row

clearDir :: Monoidal a => Direction -> Int -> Matrix a -> Matrix a
clearDir dir i mat = foldl (flip clearAt) mat $ sort $ mapMaybe (fmap fst) $ V.toList $ igetDir dir i mat

clearRow :: Monoidal a => Int -> Matrix a -> Matrix a
clearRow = clearDir Row

clearCol :: Monoidal a => Int -> Matrix a -> Matrix a
clearCol = clearDir Column

scaleRow :: (DecidableZero a, Multiplicative a) => a -> Int -> Matrix a -> Matrix a
scaleRow = scaleDir Row

scaleCol :: (DecidableZero a, Multiplicative a) => a -> Int -> Matrix a -> Matrix a
scaleCol = scaleDir Column

mapDir :: (a -> a) -> Direction
       -> Int -> Matrix a -> Matrix a
mapDir f dir i mat = traverseDir mat tr dir i mat
  where
    tr m k _ = m & coefficients . ix k . value %~ f

traverseDir :: b -> (b -> Int -> Entry a -> b)
               -> Direction
               -> Int -> Matrix a -> b
traverseDir ini f dir i mat =
  runIdentity $  traverseDirM ini (\b j e -> return $ f b j e) dir i mat

traverseDirM :: Monad m => b -> (b -> Int -> Entry a -> m b)
                -> Direction
                -> Int -> Matrix a -> m b
traverseDirM ini f dir i mat = go (IM.lookup i (mat^.startL dir)) ini
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
    traverseDirM () (trav v) dir i mat
    return v
  where
    trav v _ _ ent = MV.write v (ent ^. nthL dir) (ent ^. value)

igetDir :: Monoidal a
       => Direction -> Int -> Matrix a -> Vector (Maybe (Int, Entry a))
igetDir dir i mat =
  create $ do
    v <- MV.replicate (mat ^. lenL dir) Nothing
    traverseDirM () (trav v) dir i mat
    return v
  where
    trav v _ k ent = MV.write v (ent ^. nthL dir) (Just (k, ent))

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

addDir :: Additive a => Direction -> Vector a -> Int -> Matrix a -> Matrix a
addDir dir vec i mat = mat & coefficients %~ go
  where
    go = modify $ \mv -> do
      traverseDirM () (\_ k e -> MV.write mv k (e & value %~ (+ vec V.! (e ^. nthL dir)))) dir i mat

addRow :: Additive a => Vector a -> Int -> Matrix a -> Matrix a
addRow = addDir Row

addCol :: Additive a => Vector a -> Int -> Matrix a -> Matrix a
addCol = addDir Column

inBound :: (Int, Int) -> Matrix a -> Bool
inBound (i, j) mat = 0 <= i && i < mat ^. height && 0 <= j && j < mat ^. width

index :: Monoidal a => IM.Key -> Int -> Matrix a -> Maybe a
index i j mat
  | not $ inBound (i, j) mat = Nothing
  | otherwise = Just $ go (IM.lookup i $ mat ^. rowStart)
  where
    go Nothing  = zero
    go (Just k) =
      let e = (mat ^. coefficients) V.! k
      in if e^.idx._2 == j
         then e ^. value
         else go (e^.rowNext)

(!) :: Monoidal a => Matrix a -> (Int, Int) -> a
(!) a (i, j) = fromJust $ index i j a

combineDir :: (Multiplicative a, Monoidal a) => Direction -> a -> Int -> Int -> Matrix a -> Matrix a
combineDir dir alpha i j mat = mat & coefficients %~ go
  where
    go = modify $ \mv -> do
      let !is = getDir dir i mat
      traverseDirM () (\_ k e -> MV.write mv k (e & value %~ (+ (alpha * is V.! (e ^. nthL dir))))) dir j mat


