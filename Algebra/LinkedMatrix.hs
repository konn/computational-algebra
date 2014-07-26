{-# LANGUAGE BangPatterns, FlexibleContexts, LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses, NamedFieldPuns, NoImplicitPrelude   #-}
{-# LANGUAGE NoMonomorphismRestriction, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell                                            #-}
module Algebra.LinkedMatrix (Matrix, toList, fromList, swapRows, identity,
                             swapCols, switchCols, switchRows, addRow,
                             addCol, ncols, nrows, getRow, getCol,
                             scaleRow, combineRows, combineCols, transpose,
                             inBound, height, width, cmap, empty, rowVector,
                             colVector,
                             catRow, catCol, (<||>), (<-->), toRows, toCols,
                             zeroMat, getDiag, trace, diagProd, diag,
                             scaleCol, clearRow, clearCol, index, (!)) where
import           Algebra.Wrapped
import           Control.Applicative        ((<$>))
import           Control.Applicative        ((<|>))
import           Control.Lens               hiding (index)
import           Control.Monad              (forM, zipWithM)
import           Control.Monad.Identity     (runIdentity)
import           Control.Monad.ST.Strict    (runST)
import           Control.Monad.State.Strict (runState)
import           Data.IntMap.Strict         (IntMap, alter, insertWith)
import           Data.IntMap.Strict         (mapMaybeWithKey)
import qualified Data.IntMap.Strict         as IM
import           Data.List                  (sort)
import           Data.Maybe                 (fromJust, mapMaybe)
import           Data.Maybe                 (fromMaybe)
import           Data.Tuple                 (swap)
import           Data.Vector                (Vector, create, generate, thaw)
import           Data.Vector                (unsafeFreeze)
import qualified Data.Vector                as V
import           Data.Vector.Mutable        (grow)
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

newEntry :: a -> Entry a
newEntry v = Entry v (-1,-1) Nothing Nothing

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

empty :: Matrix a
empty = Matrix V.empty IM.empty IM.empty 0 0

fromList :: DecidableZero a => [[a]] -> Matrix a
fromList xss =
  let (as, bs) = runState (zipWithM initialize [0..] xss) (BuildState IM.empty IM.empty (-1))
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

getDiag :: Monoidal a => Matrix a -> Vector a
getDiag mat = V.generate (min (mat^.height) (mat^.width)) $ \i ->
  fromMaybe zero $ traverseDir Nothing (\a _ e -> a <|> if i == e^.nthL Row
                                                        then Just (e^.value )
                                                        else Nothing) Row i mat

diagProd :: (Unital c, Monoidal c) => Matrix c -> c
diagProd = V.foldr' (*) one . getDiag

trace :: Monoidal c => Matrix c -> c
trace = V.foldr' (+) zero . getDiag

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

addDir :: forall a. (DecidableZero a, Additive a)
       => Direction -> Vector a -> Int -> Matrix a -> Matrix a
addDir dir vec i mat = runST $ do
    mv <- thaw $ mat ^. coefficients
    let n = MV.length mv
        upd (dic, del) k e = do
          let v' = e ^. value + IM.findWithDefault zero (e ^. nthL dir) mp
          d' <- if isZero v'
                then return $ k : del
                else MV.write mv k (e & value .~ v') >> return del
          return (IM.delete (e ^. nthL dir) dic, d')
    (rest, dels) <- traverseDirM (mp, []) upd dir i mat
    mv' <- if IM.null rest
           then return mv
           else grow mv (IM.size rest)
    let app j (p, k, opo) v = do
          let preOpo = mat ^. startL (perp dir) . at i
          MV.write mv' k $ newEntry v
                         & nextL dir .~ p
                         & nextL (perp dir) .~ preOpo
                         & coordL dir .~ i
                         & nthL dir .~ j

          return (Just k, k+1, alter (const $ Just k) j opo)
    (l, _, opoStart) <- ifoldlMOf ifolded app (mat ^. startL dir . at i, n, mat ^. startL (perp dir)) rest
    v' <- unsafeFreeze mv'
    let mat' = mat & coefficients .~ v'
                   & startL dir %~ alter (const l) i
                   & startL (perp dir) .~ opoStart
    return $ foldr clearAt mat' dels
  where
    mp :: IntMap a
    mp = V.ifoldr (\k v d -> if isZero v then d else IM.insert k v d) IM.empty vec

perp :: Direction -> Direction
perp Row = Column
perp Column = Row

addRow :: DecidableZero a => Vector a -> Int -> Matrix a -> Matrix a
addRow = addDir Row

addCol :: DecidableZero a => Vector a -> Int -> Matrix a -> Matrix a
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

combineDir :: (DecidableZero a, Multiplicative a) => Direction -> a -> Int -> Int -> Matrix a -> Matrix a
combineDir dir alpha i j mat = addDir dir (V.map (alpha *) $ getDir dir i mat) j mat

combineRows :: (DecidableZero a, Multiplicative a) => a -> Int -> Int -> Matrix a -> Matrix a
combineRows = combineDir Row

combineCols :: (DecidableZero a, Multiplicative a) => a -> Int -> Int -> Matrix a -> Matrix a
combineCols = combineDir Column

nrows, ncols :: Matrix a -> Int
ncols = view width
nrows = view height

identity :: Unital a => Int -> Matrix a
identity n =
  let idMap = IM.fromList [(i,i) | i <- [0..n-1]]
  in Matrix (V.fromList [newEntry one & idx .~ (i,i) | i <- [0..n-1]])
            idMap idMap n n

diag :: DecidableZero a => Vector a -> Matrix a
diag v =
  let n = V.length v
      idMap = IM.fromList [(i,i) | i <- [0..n-1]]
  in clearZero $ Matrix (V.imap (\i a -> newEntry a & idx .~ (i,i)) v)
                 idMap idMap n n

catDir :: DecidableZero b => Direction -> Matrix b -> Vector b -> Matrix b
catDir dir mat vec = runST $ do
  let seed = V.filter (not . isZero . snd) $ V.take (mat ^. lenL dir) $ V.indexed vec
      n    = V.length $ mat ^. coefficients
      curD = mat ^. countL dir
      getNextIdx l | l == 0 = Nothing
                   | otherwise = Just (n+l-1)
  mv <- flip grow (V.length seed) =<< thaw (mat^.coefficients)
  let upd (k, v) (l, opdic) = do
        MV.write mv (n+l) $ newEntry v
                          & nthL dir .~ k
                          & coordL dir .~ curD
                          & nextL dir .~ getNextIdx l
                          & nextL (perp dir) .~ IM.lookup k opdic
        return (l+1, alter (const $ Just $ n+l) k opdic)
  (l, op') <- foldlMOf folded (flip upd) (0, mat ^. startL (perp dir)) seed
  v <- unsafeFreeze mv
  return $ mat & countL dir +~ 1
               & startL dir %~ alter (const $ getNextIdx l) curD
               & startL (perp dir) .~ op'
               & coefficients .~ v

rowVector :: DecidableZero a => Vector a -> Matrix a
rowVector = fromList . (:[]) . V.toList

colVector :: DecidableZero a => Vector a -> Matrix a
colVector = fromList . map (:[]) . V.toList

toDirs :: Monoidal a => Direction -> Matrix a -> [Vector a]
toDirs dir mat = [ getDir dir i mat | i <- [0..mat^.countL dir-1]]

toRows :: Monoidal a => Matrix a -> [Vector a]
toRows = toDirs Row

toCols :: Monoidal a => Matrix a -> [Vector a]
toCols = toDirs Column

appendDir :: DecidableZero b => Direction -> Matrix b -> Matrix b -> Matrix b
appendDir dir m = foldl (catDir dir) m . toDirs dir

(<-->) :: DecidableZero b => Matrix b -> Matrix b -> Matrix b
(<-->) = appendDir Row

(<||>) :: DecidableZero b => Matrix b -> Matrix b -> Matrix b
(<||>) = appendDir Column

catRow :: DecidableZero b => Matrix b -> Vector b -> Matrix b
catRow = catDir Row

catCol :: DecidableZero b => Matrix b -> Vector b -> Matrix b
catCol = catDir Column

switchRows :: Int -> Int -> Matrix a -> Matrix a
switchRows = swapRows

switchCols :: Int -> Int -> Matrix a -> Matrix a
switchCols = swapCols

cmap :: DecidableZero a => (a1 -> a) -> Matrix a1 -> Matrix a
cmap f = clearZero . (coefficients . mapped . value %~ f)

clearZero :: DecidableZero a => Matrix a -> Matrix a
clearZero mat = V.ifoldr (\i v m -> if isZero (v^.value) then clearAt i m else m)
                mat (mat ^. coefficients)

transpose :: Matrix a -> Matrix a
transpose mat = mat & rowStart .~ mat^.colStart
                    & colStart .~ mat^.rowStart
                    & height   .~ mat^.width
                    & width    .~ mat^.height
                    & coefficients . each . idx %~ swap

zeroMat :: Int -> Int -> Matrix a
zeroMat = Matrix V.empty IM.empty IM.empty

{-
gaussReduction :: (Normed a, DecidableZero a, Field a, Unital a)
               => Matrix a -> (Matrix a, Matrix a)
gaussReduction mat = go 1 1 mat (identity $ nrows mat)
  where
    go i j a p
      | i > nrows mat || j > ncols mat = (a, p)
      | otherwise =
        let (k, new) =  maximumBy (comparing $ norm . snd) [(l, a ! (l, j)) | l <- [i..nrows mat]]
        in if isZero new
           then go i (j + 1) a p
           else let prc l a0 p0
                      | l == i = prc (l+1) a0 p0
                      | l > nrows mat = (a0, p0)
                      | otherwise     =
                        let coe = NA.negate (a0 ! (l, j))
                            a'' = combineRows coe i l a0
                            p'' = combineRows coe i l p0
                        in prc (l+1) a'' p''
                    (a', p') = prc 1 (scaleRow (NA.recip new) i $ switchRows i k a)
                                     (scaleRow (NA.recip new) i $ switchRows i k p)
                in go (i+1) (j+1) a' p'
-}
