{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE BangPatterns, DataKinds, FlexibleContexts, FlexibleInstances  #-}
{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, KindSignatures, LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses, NamedFieldPuns, NoImplicitPrelude      #-}
{-# LANGUAGE NoMonomorphismRestriction, PolyKinds, RankNTypes              #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TemplateHaskell      #-}
{-# LANGUAGE TupleSections, UndecidableInstances, ViewPatterns             #-}
{-# OPTIONS_GHC -funbox-strict-fields -Wno-type-defaults -Wno-redundant-constraints #-}
module Algebra.LinkedMatrix (Matrix, toLists, fromLists, fromList,
                             swapRows, identity,nonZeroRows,nonZeroCols,
                             swapCols, switchCols, switchRows, addRow,
                             addCol, ncols, nrows, getRow, getCol, triangulateModular,
                             scaleRow, combineRows, combineCols, transpose,
                             inBound, height, width, cmap, empty, rowVector,
                             colVector, rowCount, colCount, traverseRow,
                             traverseCol, Entry, idx, value, substMatrix,
                             catRow, catCol, (<||>), (<-->), toRows, toCols,
                             zeroMat, getDiag, trace, diagProd, diag,
                             scaleCol, clearRow, clearCol, index, (!),
                             nonZeroEntries, rankLM, splitIndependentDirs,
                             structuredGauss, multWithVector, solveWiedemann,
                             henselLift, solveHensel, structuredGauss', intDet) where
import Algebra.Algorithms.ChineseRemainder
import Algebra.Field.Prime
import Algebra.Instances                   ()
import Algebra.Prelude.Core                hiding (Vector, empty, fromList,
                                            generate, insert, transpose, (%),
                                            (<.>), (<>))

import           Control.Applicative          ((<|>))
import           Control.Arrow                ((&&&))
import           Control.Arrow                ((>>>))
import           Control.Lens                 hiding (index, (<.>))
import           Control.Monad                (replicateM)
import           Control.Monad.Loops          (iterateUntil)
import           Control.Monad.Random         hiding (fromList)
import           Control.Monad.ST.Strict      (ST, runST)
import           Control.Monad.State.Strict   (evalState, runState)
import           Control.Parallel.Strategies  (parMap)
import           Control.Parallel.Strategies  (rdeepseq)
import           Data.IntMap.Strict           (IntMap, alter, insert,
                                               mapMaybeWithKey, minViewWithKey)
import qualified Data.IntMap.Strict           as IM
import           Data.IntSet                  (IntSet)
import qualified Data.IntSet                  as IS
import           Data.List                    (minimumBy, sort)
import           Data.List                    (sortBy)
import           Data.Maybe                   (fromJust, fromMaybe, mapMaybe)
import           Data.Monoid                  (First (..))
import           Data.Numbers.Primes          (primes)
import           Data.Ord                     (comparing)
import           Data.Proxy                   (Proxy (..))
import           Data.Reflection              (Reifies (..), reify)
import           Data.Semigroup               hiding (First (..))
import           Data.Tuple                   (swap)
import           Data.Vector                  (Vector, create, generate, thaw,
                                               unsafeFreeze)
import qualified Data.Vector                  as V
import           Data.Vector.Mutable          (grow)
import qualified Data.Vector.Mutable          as MV
import           Numeric.Decidable.Zero       (isZero)
import           Numeric.Domain.GCD           (gcd, lcm)
import           Numeric.Field.Fraction       ((%))
import           Numeric.Semiring.ZeroProduct (ZeroProductSemiring)
import qualified Prelude                      as P

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
                       } deriving (Read, Show)

makeLenses ''Matrix

data BuildState = BuildState { _colMap :: !(IntMap Int)
                             , _rowMap :: !(IntMap Int)
                             , _curIdx :: !Int
                             }
makeLenses ''BuildState

data GaussianState a = GaussianState { _input     :: !(Matrix a)
                                     , _output    :: !(Matrix a)
                                     , _prevCol   :: !Int
                                     , _heavyCols :: !IntSet
                                     , _curRow    :: !Int
                                     , _detAcc    :: !a
                                     }
makeLenses ''GaussianState

instance Eq a => Eq (Matrix a) where
  n == m =
    n^.height == m^.height && n^.width == m^.width && content n == content m
    where
      content = sortBy (comparing fst) . V.toList . nonZeroEntries

data MaxEntry a b = MaxEntry { _weight :: !a
                             , entry   :: b
                             } deriving (Read, Show, Eq, Ord)

empty :: Matrix a
empty = Matrix V.empty IM.empty IM.empty 0 0

fromLists :: DecidableZero a => [[a]] -> Matrix a
fromLists xss =
  fromList (concat $ zipWith (\i -> zipWith (\j -> ((i,j),)) [0..]) [0..] xss)
  & width  .~ maximum (0 : map length xss)
  & height .~ length xss

fromCols :: DecidableZero a => [Vector a] -> Matrix a
fromCols xss =
  let h = maximum $ map V.length xss
      w = length xss
  in fromList (concat $ zipWith (\i -> V.toList . V.imap (\j -> ((j,i),))) [0..] xss)
     & width .~ w
     & height .~ h

fromList :: DecidableZero a => [((Int, Int), a)] -> Matrix a
fromList cs =
  let (as, bs) = runState (mapM initialize $ filter (view $ _2 . to (not.isZero)) cs)
                 (BuildState IM.empty IM.empty (-1))
      vec = V.fromList as
      h = maximum (0:map (view $ _1._1) cs) + 1
      w = maximum (0:map (view $ _1._2) cs) + 1
  in Matrix vec (bs^.rowMap) (bs^.colMap) h w
  where
    initialize ((i, j), c) =  do
        curIdx += 1
        n <- use curIdx
        nc <- use $ colMap.at j
        nr <- use $ rowMap.at i
        colMap %= insert j n
        rowMap %= insert i n
        return $ Entry { _value = c
                       , _idx = (i, j)
                       , _rowNext = nr
                       , _colNext = nc
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

toLists :: forall a. Monoidal a => Matrix a -> [[a]]
toLists mat =
  let orig = replicate (_height mat) $ replicate (_width mat) (zero :: a)
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
  let ith = mat^.startL dir.at i
      jth = mat^.startL dir.at j
  in  mat & startL dir   %~ alter (const jth) i . alter (const ith) j
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

clearDir :: Direction -> Int -> Matrix a -> Matrix a
clearDir dir i mat = foldl (flip clearAt) mat $ sort $ mapMaybe (fmap fst) $ V.toList $ igetDir dir i mat

clearRow :: Int -> Matrix a -> Matrix a
clearRow = clearDir Row

clearCol :: Int -> Matrix a -> Matrix a
clearCol = clearDir Column

scaleRow :: (DecidableZero a, Multiplicative a) => a -> Int -> Matrix a -> Matrix a
scaleRow = scaleDir Row

scaleCol :: (DecidableZero a, Multiplicative a) => a -> Int -> Matrix a -> Matrix a
scaleCol = scaleDir Column

mapDir :: (a -> a) -> Direction
       -> Int -> Matrix a -> Matrix a
mapDir f dir i mat = traverseDir mat trv dir i mat
  where
    trv m k _ = m & coefficients . ix k . value %~ f

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

getDir :: forall a. Monoidal a
       => Direction -> Int -> Matrix a -> Vector a
getDir dir i mat =
  create $ do
    v <- MV.replicate (mat ^. lenL dir) (zero :: a)
    traverseDirM () (trav v) dir i mat
    return v
  where
    trav :: forall s. MV.MVector s a -> () -> Int -> Entry a -> ST s ()
    trav v _ _ ent = MV.write v (ent ^. nthL dir) (ent ^. value)

igetDir :: forall a. Direction -> Int -> Matrix a -> Vector (Maybe (Int, Entry a))
igetDir dir i mat =
  create $ do
    v <- MV.replicate (mat ^. lenL dir) Nothing
    traverseDirM () (trav v) dir i mat
    return v
  where
    trav :: forall s. MV.MVector s (Maybe (Int, Entry a)) -> () -> Int -> Entry a -> ST s ()
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

addDir :: forall a. (DecidableZero a)
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
          let preOpo = mat ^. startL (perp dir) . at j
          MV.write mv' k $ newEntry v
                         & nextL dir .~ p
                         & nextL (perp dir) .~ preOpo
                         & coordL dir .~ i
                         & nthL dir .~ j

          return (Just k, k+1, alter (const $ Just k) j opo)
    (l, _, opoStart) <- ifoldlM app (mat ^. startL dir . at i, n, mat ^. startL (perp dir)) rest
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

addRow :: (DecidableZero a) => Vector a -> Int -> Matrix a -> Matrix a
addRow = addDir Row

addCol :: (DecidableZero a) => Vector a -> Int -> Matrix a -> Matrix a
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

dirVector :: DecidableZero a => Direction -> Vector a -> Matrix a
dirVector Row = rowVector
dirVector Column = colVector

rowVector :: DecidableZero a => Vector a -> Matrix a
rowVector = fromLists. (:[]) . V.toList

colVector :: DecidableZero a => Vector a -> Matrix a
colVector = fromLists . map (:[]) . V.toList

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
                    & coefficients . each %~ swapEntry
  where
    swapEntry ent = ent & idx     %~ swap
                        & rowNext .~ ent ^. colNext
                        & colNext .~ ent ^. rowNext

zeroMat :: Int -> Int -> Matrix a
zeroMat = Matrix V.empty IM.empty IM.empty

dirCount :: Direction -> Int -> Matrix a -> Int
dirCount = traverseDir 0 (\a _ _ -> succ a)

rowCount :: Int -> Matrix a -> Int
rowCount = dirCount Row

colCount :: Int -> Matrix a -> Int
colCount = dirCount Column

instance (Ord a, Semigroup b) => Semigroup (MaxEntry a b) where
  MaxEntry a as <> MaxEntry b bs =
    case compare a b of
      EQ -> MaxEntry a (as <> bs)
      LT -> MaxEntry b bs
      GT -> MaxEntry a as

instance (Ord a, Bounded a, Monoid b) => Monoid (MaxEntry a b) where
  mappend (MaxEntry a as) (MaxEntry b bs) =
    case compare a b of
      EQ -> MaxEntry a (as `mappend` bs)
      LT -> MaxEntry b bs
      GT -> MaxEntry a as
  mempty = MaxEntry minBound mempty


newGaussianState :: Unital a => Matrix a -> GaussianState a
newGaussianState inp =
  GaussianState inp (identity $ inp ^. height) (-1) (getHeaviest IS.empty inp) 0 one

getHeaviest :: IntSet -> Matrix a -> IntSet
getHeaviest old inp =
  if IS.size old >= inp^.width*5`P.div`100
  then old
  else  let news = entry $ mconcat $ map (\k -> MaxEntry (colCount k inp) (IS.singleton k)) $
                   IS.toList $ IM.keysSet (inp^.colStart) IS.\\ old
        in news `IS.union` old

traverseRow :: b -> (b -> Int -> Entry a -> b) -> Int -> Matrix a -> b
traverseRow a f = traverseDir a f Row

traverseCol :: b -> (b -> Int -> Entry a -> b) -> Int -> Matrix a -> b
traverseCol a f = traverseDir a f Column

structuredGauss :: (DecidableZero a, Division a, Group a)
                => Matrix a -> (Matrix a, Matrix a)
structuredGauss = structuredGauss' >>> view _1 &&& view _2

structuredGauss' :: (DecidableZero a, Division a, Group a)
                 => Matrix a -> (Matrix a, Matrix a, a)
structuredGauss' = evalState go . newGaussianState
  where
    countLight heavys = traverseRow (0 :: Int)
                           (\(!c) _ ent -> if (ent^.coordL Column) `IS.member` heavys
                                        then c
                                        else c+1)
    go = do
      old <- use input
      destRow <- use curRow
      pcol <- use prevCol
      (_, rest) <- uses (input.colStart) (IM.split pcol)
      case minViewWithKey rest of
        _ | destRow >= old ^. height -> (,,) <$> use input <*> use output <*> use detAcc
        Nothing -> (,,) <$> use input <*> use output <*> use detAcc
        Just ((pivCol, _), _) -> do
          heavys <- use heavyCols
          prevCol .= pivCol
          let trav b _ ent = do
                if (ent ^. coordL Row) < destRow
                  then do
                  return b
                  else do
                  let lc = countLight heavys (ent ^. coordL Row) old
                  return $ case b of
                    Nothing -> Just (ent, lc)
                    Just (p, l0)
                      | l0 <= lc  -> Just (p, l0)
                      | otherwise -> Just (ent, lc)
          mans <- traverseDirM Nothing trav Column pivCol old
          case mans of
            Nothing -> nextElim
            Just (pivot, _) -> do
              let pivRow = pivot ^. coordL Row
                  pivCoe = pivot ^. value
                  sgn    = if pivRow == destRow then one else negate one
              p0 <- use output
              let elim (m, p) _ ent = do
                    if ent^.coordL Row /= pivRow
                      then do
                        let coe = negate (ent ^. value) / pivCoe
                        return $ (m, p) & both %~ combineRows coe pivRow (ent ^. coordL Row)
                      else do
                        return (m, p)
              (input', output') <- traverseDirM (old, p0) elim Column pivCol old
                    <&> both %~ scaleRow (recip pivCoe) destRow . switchRows destRow pivRow
              input .= input'
              output .= output'
              curRow += 1
              detAcc %= (*(pivCoe*sgn))
              nextElim
    nextElim = do
      oldHeavys <- use heavyCols
      newHeavyCols <- uses input (getHeaviest oldHeavys)
      heavyCols %= IS.union newHeavyCols
      go

nonZeroEntries :: Matrix a -> Vector ((Int, Int), a)
nonZeroEntries mat = V.map (view idx &&& view value) $ mat ^. coefficients

multWithVector :: (Multiplicative a, Monoidal a)
               => Matrix a -> Vector a -> Vector a
multWithVector mat v =
  V.generate (mat^.height) $ \i ->
  traverseRow zero (\acc _ ent -> acc + (ent^.value)*(v V.! (ent^.nthL Row))) i mat

nonZeroDirs :: Direction -> Matrix r -> [Int]
nonZeroDirs dir = view $ startL dir . to IM.keys

nonZeroRows :: Matrix r -> [Int]
nonZeroRows = nonZeroDirs Row

nonZeroCols :: Matrix r -> [Int]
nonZeroCols = nonZeroDirs Column

{-
testCase :: Matrix (Fraction Integer)
testCase = fromLists [[0,0,0,0,0,0,2,-3,-1,0]
                      ,[0,0,0,2,-3,-1,0,0,0,0]
                      ,[0,2,-3,0,-1,0,0,0,0,0]
                      ,[1,0,1,0,0,1,-2,0,0,0]
                      ,[2,-3,0,-1,0,0,0,0,0,0]
                      ,[1,0,1,0,0,1,0,0,0,-1]
                      ,[1,0,1,0,0,1,-2,0,0,0]]
-}

newtype Square n r = Square { runSquare :: Matrix r
                            } deriving (Show, Eq, Additive, Multiplicative)

deriving instance (DecidableZero r, Semiring r, Multiplicative r)
               => LeftModule (Scalar r) (Square n r)
deriving instance (DecidableZero r, Semiring r, Multiplicative r)
               => RightModule (Scalar r) (Square n r)

instance (Unital r, Multiplicative r, Reifies n Integer, DecidableZero r) => Unital (Square n r) where
  one = Square $ identity $ fromInteger $ reflect (Proxy :: Proxy n)

instance (DecidableZero r, Multiplicative r) => Multiplicative (Matrix r) where
  m * n = fromList [ ((i,j),sum $ V.zipWith (*) (getRow i m) (getCol j n))
                   | i <- nonZeroRows m
                   , j <- nonZeroCols n
                   ] & width .~ n^.width
                     & height .~ m^.height


instance (DecidableZero r, RightModule Natural r) => RightModule Natural (Matrix r) where
  m *. n = cmap (*. n) m

instance (DecidableZero r, LeftModule Natural r) => LeftModule Natural (Matrix r) where
  n .* m = cmap (n .*) m

instance (DecidableZero r, RightModule Integer r) => RightModule Integer (Matrix r) where
  m *. n = cmap (*. n) m

instance (DecidableZero r, LeftModule Integer r) => LeftModule Integer (Matrix r) where
  n .* m = cmap (n .*) m

instance (DecidableZero r)
      => Monoidal (Matrix r) where
  zero = zeroMat 0 0

instance (DecidableZero r) => Additive (Matrix r) where
  m + n =
    let dir = minimumBy (comparing $ length . flip nonZeroDirs n)
              [Row, Column]
    in foldr (\i l -> addDir dir (getDir dir i n) i l) m (nonZeroDirs dir n)

instance (DecidableZero r, Semiring r, Multiplicative r)
      => LeftModule (Scalar r) (Matrix r) where
  Scalar r .* mat = cmap (r*) mat

instance (DecidableZero r, Semiring r, Multiplicative r)
      => RightModule (Scalar r) (Matrix r) where
  mat *. Scalar r = cmap (*r) mat

instance (DecidableZero r, Group r) => Group (Matrix r) where
  negate = cmap negate

instance (DecidableZero r, Abelian r) => Abelian (Matrix r)

instance (DecidableZero r, Semiring r) => Semiring (Matrix r)

substMatrix :: (CoeffRing r)
            => Matrix r -> Polynomial r 1 -> Matrix r
substMatrix m f =
  let n = ncols m
  in if n == nrows m
     then reify (P.toInteger n) $ \pxy -> runSquare $ substUnivariate (toSquare pxy m) f
     else error "Matrix must be square"

toSquare :: proxy n -> Matrix r -> Square n r
toSquare _ = Square

(<.>) :: (Multiplicative m, Monoidal m) => Vector m -> Vector m -> m
v <.> u = sum $ V.zipWith (*) v u

krylovMinpol :: (Eq a, Ring a, DecidableZero a, DecidableUnits a,
                 Field a, ZeroProductSemiring a,
                 Random a, MonadRandom m)
             => Matrix a -> Vector a -> m (Polynomial a 1)
krylovMinpol m b
  | V.all isZero b = return one
  | otherwise = reify (P.toInteger n) $ \pxy -> do
    iterateUntil (\h -> V.all isZero $ multWithVector (substMatrix m h) b) $ do
      u <- replicateM n getRandom
      return $ minpolRecurrent (fromIntegral n)
        [ V.fromList u <.> multWithVector (runSquare $ toSquare pxy m ^ fromIntegral i) b
        | i <- [0..2*n-1]]
    where
      n = ncols m

-- | Solving linear equation using linearly recurrent sequence (Wiedemann algorithm).
solveWiedemann :: (Eq a, Field a, DecidableZero a, DecidableUnits a,
                ZeroProductSemiring a, Random a, MonadRandom m)
            => Matrix a -> Vector a -> m (Either (Vector a) (Vector a))
solveWiedemann a b = do
  m <- krylovMinpol a b
  return $
    let m0 = injectCoeff (coeff one m)
        g = (m - m0) `quot` varX
    in if isZero (coeff one m)
       then Left $ substMatrix a g `multWithVector` b
       else let h = negate g `quot` m0
            in Right $ substMatrix a h `multWithVector` b

rankLM :: (DecidableZero r, Division r, Group r) => Matrix r -> Int
rankLM mat =
  let m' = fst $ structuredGauss mat
  in min (length $ nonZeroRows m') (length $ nonZeroCols m')

splitIndependentDirs :: (DecidableZero a, Field a)
                     => Direction -> Matrix a
                     -> (Matrix a, [Int], [Int])
                     -- ^ @(m', bs, as)@ with @m@ is full-rank submatrix,
                     --   @bs@ are independent and @as@ are dependent.
splitIndependentDirs dir mat =
  case nonZeroDirs dir mat of
    []  -> (zero, [], [])
    [a] -> (dirVector dir $ getDir dir a mat, [a], [])
    (x:xs)  -> go 1 xs (dirVector dir $ getDir dir x mat) [x] []
  where
    n = min (nrows mat) (ncols mat)
    go _ []     nat ok bad = (nat, ok, bad)
    go i (k:ks) nat ok bad
      | i >= n = (nat, ok, bad)
      | otherwise =
        let nat' = catDir dir nat $ getDir dir k mat
        in if ({-# SCC "rankLM" #-} rankLM nat') == i
           then go i     ks nat  ok     (k:bad)
           else go (i+1) ks nat' (k:ok) bad

intDet :: Matrix Integer -> Integer
intDet mat =
  let b = V.maximum $ V.map (P.fromInteger . abs . snd) $ nonZeroEntries mat
      n = fromIntegral $ ncols mat
      c = n^(n `P.div` 2) * b^n
      r = ceilingLogBase2 (2*fromIntegral c + 1)
      ps = take r primes
      m  = product ps
      d  = chineseRemainder [ (p,
                               reifyPrimeField p $ \pxy ->
                               shiftHalf p $ naturalRepr $ view _3 $
                               structuredGauss' (cmap (modNat' pxy) mat))
                            | p <- ps]
      off = d `div` m
  in if d == 0
     then 0
     else minimumBy (comparing abs) [d - m * off, d - m * (off + 1)]

shiftHalf :: P.Integral a => a -> a -> a
shiftHalf p n =
  let s = p `P.div` 2
  in (n P.+ s) `P.mod` p P.- s

triangulateModular :: Matrix (Fraction Integer)
                   -> (Matrix (Fraction Integer),
                       Matrix (Fraction Integer))
triangulateModular mat0 =
  let ps = filter ((/= 0) . (P.mod l)) primes
  in go ps
  where
    ds = V.foldr (lcm' . abs . denominator.snd) 1 $ nonZeroEntries mat0
    mN = V.foldr (lcm' . abs . numerator . snd) 1 $ nonZeroEntries mat0
    l  = lcm' ds mN
    go (p:ps) =
      let (indepRows, _, indepCols, depCols) = reifyPrimeField p $ \pxy ->
            let mat = cmap (modRat pxy) mat0
                (koho, IS.fromList -> irs, IS.fromList -> drs) =
                  {-# SCC "splitRow" #-} splitIndependentDirs Row mat
                (_, IS.fromList -> ics, IS.fromList -> dcs) =
                  {-# SCC "splitCol" #-} splitIndependentDirs Column koho
            in (irs,
                drs `IS.union` (IS.fromList (nonZeroRows mat0) IS.\\ irs),
                ics,
                dcs `IS.union` (IS.fromList (nonZeroCols $ extract irdic colIdentDic) IS.\\ ics))
          colIdentDic = IM.fromList $ zip [0..ncols mat0 - 1] [0..]
          irdic = IM.fromList $ zip (IS.toAscList indepRows) [0..]
          icdic = IM.fromList $ zip (IS.toAscList indepCols) [0..]
          dcdic = IM.fromList $ zip (IS.toDescList depCols) [0..]
          newIdx rd cd (i, j) = (,) <$> IM.lookup i rd <*> IM.lookup j cd
          extract rd cd = fromList (mapMaybe (\(ind, c) -> (,c) <$> newIdx rd cd ind) $
                          V.toList $ nonZeroEntries mat0)
                          & height .~ IM.size rd
                          & width  .~ IM.size cd
          spec = extract irdic icdic
          qs = filter (\r -> ds `mod` r /= 0 && ({-# SCC "checkDet" #-} reifyPrimeField r $ \pxy ->
                          not $ isZero $ view _3 $
                          structuredGauss' $ cmap (modRat pxy) $ spec)) primes
          anss = parMap rdeepseq (\xs -> fromJust $ ala First foldMap $
                                         map (\q -> solveHensel 10 q spec xs) qs) $
                 toCols $ extract irdic dcdic
          permMat = build [] (ncols mat0 - 1)
                    (zip (IS.toDescList indepCols) $ reverse $ toCols $ identity $ nrows spec) $
                    zip (IS.toDescList depCols) anss
          origDeled = extract irdic colIdentDic & width .~ mat0^.width
     in if (spec * permMat) == origDeled
        then (permMat, spec)
        else go ps
    go _ = error "Cannot happen!"
    build ans i mns vecs
      | i < 0 = fromCols ans
      | otherwise = {-# SCC "building" #-}
        case vecs of
          ((k, v) : vs) | i == k -> build (v : ans) (i-1) mns vs
          _ ->
            case mns of
              ((l,m):mn) | i == l -> build (m : ans) (i-1) mn vecs
              _ -> build (V.empty : ans) (i-1) mns vecs

lcm' :: Euclidean r => r -> r -> r
lcm' n m = n * m `quot` gcd n m

henselLift :: Integer           -- ^ prime number @p@
           -> Matrix Integer -- ^ original matrix @M@
           -> Matrix Integer -- ^ inverse matrix of @M@ mod @p@
           -> V.Vector Integer  -- ^ coefficient vector @v@
           -> [V.Vector Integer]  -- ^ vector @x@ with @Mx = b mod p@
henselLift p m q b =
  map (view _2) $ iterate step (1, V.replicate (V.length b) 0, b)
  where
    step (s, acc, r)
      | otherwise =
        let u = reifyPrimeField p $ \pxy ->
              V.map (naturalRepr . modNat' pxy) $ q `multWithVector` r
            r' = V.map (`quot` p) $ V.zipWith (-) r (m `multWithVector` u)
        in (s*p, acc + V.map (s*) u, r')


solveHensel :: Int -> Integer
            -> Matrix (Fraction Integer)
            -> Vector (Fraction Integer)
            -> Maybe (Vector (Fraction Integer))
solveHensel cyc p mat b = {-# SCC "solveHensel" #-}
  let g0 = V.foldr (lcm . denominator . view _2) one $ nonZeroEntries mat
      g1 = V.foldr (lcm . denominator) one b
      g  = lcm g0 g1 % 1
      mat' = cmap (numerator . (*g)) mat
      b'   = V.map (numerator . (*g)) b
      q = reifyPrimeField p $ \pxy ->
        cmap naturalRepr $ snd $ structuredGauss $ cmap (modNat' pxy) mat'
      hls = henselLift p mat' q b'
  in go Nothing $ drop cyc $ zip [p^i | i <- [0..]] hls
  where
    go _ [] = Nothing
    go prev ((q,x):xs) =
      let mans = V.mapM (recoverRat (P.floor $ P.sqrt (fromIntegral q P./ 2 :: Double)) q) x
      in case mans of
        Just x' | mat `multWithVector` x' == b -> Just x'
                | mans == prev -> Nothing
        _ -> go mans (drop cyc xs)
