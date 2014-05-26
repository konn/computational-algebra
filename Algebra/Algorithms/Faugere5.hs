{-# LANGUAGE ConstraintKinds, DataKinds, DeriveDataTypeable, FlexibleContexts  #-}
{-# LANGUAGE GADTs, ImplicitParams, MultiParamTypeClasses, NoImplicitPrelude   #-}
{-# LANGUAGE NoMonomorphismRestriction, ParallelListComp, RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables, TemplateHaskell, TypeOperators, ViewPatterns #-}
module Algebra.Algorithms.Faugere5 (f5Original) where
import           Algebra.Algorithms.Groebner
import           Algebra.Prelude
import           Algebra.Ring.Noetherian
import           Control.Applicative         ((<$>))
import           Control.Arrow               ((>>>))
import           Control.Lens                (makeLenses, view, (%~), (&), (.~))
import           Control.Lens                ((^.), _1, _2)
import           Control.Monad               (filterM, forM_, liftM)
import           Control.Monad               (zipWithM_)
import           Control.Monad.Loops         (anyM, whileM_)
import           Control.Monad.ST            (ST, runST)
import           Data.Foldable               (foldrM)
import qualified Data.Foldable               as T
import           Data.Function               (on)
import           Data.Heap                   (Entry (..), insert)
import qualified Data.Heap                   as H
import           Data.IntSet                 (IntSet)
import qualified Data.IntSet                 as IS
import           Data.List                   (find, partition)
import           Data.List                   (sort, sortBy)
import           Data.List                   (tails)
import           Data.Maybe                  (listToMaybe)
import           Data.Monoid                 ((<>))
import           Data.Ord                    (comparing)
import           Data.Singletons             (SingRep)
import           Data.STRef                  (STRef, modifySTRef', newSTRef)
import           Data.STRef                  (readSTRef, writeSTRef)
import qualified Data.Vector                 as V
import qualified Data.Vector                 as V
import qualified Data.Vector.Mutable         as MV
import           Numeric.Decidable.Zero      (isZero)

type CriticalPair ord n = (OrderedMonomial ord n, OrderedMonomial ord n, Int, OrderedMonomial ord n, Int)
type Rule ord n = [(OrderedMonomial ord n, Int)]

data PolyRepr r ord n = PolyRepr { _signature :: (Int, OrderedMonomial ord n)
                                 , _poly      :: OrderedPolynomial r ord n
                                 } deriving (Show)

type RefVector s a = STRef s (MV.MVector s a)

monoize :: ( DecidableZero r, SingRep n, Division r, Noetherian r, IsMonomialOrder order)
        => OrderedPolynomial r order n -> OrderedPolynomial r order n
monoize f | isZero f  = zero
          | otherwise = recip (leadingCoeff f) .*. f

makeLenses ''PolyRepr

instance (IsMonomialOrder ord, SingRep n) => Eq (PolyRepr r ord n) where
  (==) = (==) `on` view signature

instance (IsMonomialOrder ord, SingRep n) => Ord (PolyRepr r ord n) where
  compare = flip (comparing (view $ signature._1)) <> comparing (view $ signature._2)

(*@) :: (DecidableZero r, Eq r, IsMonomialOrder ord, SingRep n, Noetherian r)
     => OrderedMonomial ord n -> PolyRepr r ord n -> PolyRepr r ord n
(*@) v = (signature._2 %~ (v*)) >>> (poly %~ (toPolynomial (one, v) *))

nf :: (DecidableZero r, Eq r, SingRep n, Division r, Noetherian r, IsMonomialOrder ord)
   => PolyRepr r ord n -> [OrderedPolynomial r ord n] -> PolyRepr r ord n
nf r g = r & poly %~ (`modPolynomial` g)

infixl 7 *@

f5Original :: ( Ord r, Eq r, DecidableZero r, SingRep n, Division r, Noetherian r, IsMonomialOrder ord)
           => Ideal (OrderedPolynomial r ord n) -> Ideal (OrderedPolynomial r ord n)
f5Original = toIdeal . sort . reduceMinimalGroebnerBasis . minimizeGroebnerBasis . generators . mainLoop

mainLoop :: ( IsMonomialOrder ord, IsPolynomial r n, Field r)
         => Ideal (OrderedPolynomial r ord n) -> Ideal (OrderedPolynomial r ord n)
mainLoop (filter (not . isZero) . generators -> ideal)
  | null ideal = toIdeal [zero]
  | otherwise = runST $ do
  let gs = sortBy (comparing totalDegree' <> comparing leadingMonomial) $
            ideal
      m  = length gs
      (f0 : fs) = gs
  lps0 <- newSTRef =<< MV.new 2
  writeAt lps0 0 (PolyRepr (0, one) $ monoize f0)
  rs0  <- newSTRef =<< V.unsafeThaw (V.fromList [[], []])
  let ?labPolys = lps0
      ?rules    = rs0
  loop [f0] (IS.fromList [0]) $ zip [1..] fs
  where
    zeroRule []     _ = return ()
    zeroRule (f:fs) i =
      let t = leadingMonomial f
      in forM_ (zip [i+1..] fs) $ \(j, fj) -> do
        let u = lcm t (leadingMonomial fj) / leadingMonomial fj
        snoc ?labPolys $ PolyRepr (j, u) zero
        addRule
    loop bs _ [] = return $ toIdeal bs
    loop bs g ((i, f):xs) = do
      g' <- f5Core (length bs) bs g
      p  <- anyM (liftM ((== one) . view poly) . readAt ?labPolys) $ IS.toList g'
      if p
        then return $ toIdeal [one]
        else do
        bs' <- reduceMinimalGroebnerBasis . minimizeGroebnerBasis <$>
               mapM (liftM (view poly) . readAt ?labPolys) (IS.toList g')
        let count = length bs'
        writeSTRef ?labPolys
          =<< V.unsafeThaw (V.fromList $ [ PolyRepr (j, one) p
                                         | p <- bs'
                                         | j <- [0..] ])
        writeSTRef ?rules =<< MV.replicate count []
        zipWithM_ zeroRule (tails bs') [0..]
        loop bs' (IS.fromList [0..length bs' - 1]) xs

f5Core :: ( ?labPolys :: (RefVector s (PolyRepr r ord n)),
           ?rules :: (RefVector s (Rule ord n)),
           Eq r, Division r, SingRep n, DecidableZero r, Noetherian r, IsMonomialOrder ord)
       => Int
       -> IntSet
       -> ST s IntSet
f5Core i g = do
  curIdx <- pred . MV.length <$> readSTRef ?labPolys
  g' <- newSTRef $ IS.insert curIdx g
  ps <- newSTRef =<< mapMaybeM (\j -> criticalPair curIdx j i g) (IS.toList g)
  whileM_ (not . null <$> readSTRef ps) $ do
    p <- readSTRef ps
    let d = minimum $ map (totalDegree.view _1) p
        (pd, p') = partition ((== d) . totalDegree . view _1) p
    writeSTRef ps p'
    sd <- spols pd
    rd <- reduction sd g =<< readSTRef g'
    forM_ (IS.toList rd) $ \k -> do
      pss <- mapMaybeM (\l -> criticalPair k l i g) . IS.toList =<< readSTRef g'
      modifySTRef' ps (pss ++)
      modifySTRef' g' (IS.insert k)
  readSTRef g'


mapMaybeM :: Monad m => (t -> m (Maybe a)) -> [t] -> m [a]
mapMaybeM f as = go as id
  where
    go []       acc = return $ acc []
    go (x : xs) acc = do
      ma <- f x
      case ma of
        Nothing -> go xs acc
        Just x' -> go xs (acc . (x' :))

reduction :: (Eq r, ?labPolys :: (RefVector s (PolyRepr r ord n)),
              ?rules :: (RefVector s (Rule ord n)),
              SingRep n, DecidableZero r, Division r, Noetherian r,
              IsMonomialOrder ord)
          => [Int] -> IntSet -> IntSet -> ST s IntSet
reduction t0 g g' = do
  pgs <- mapM (liftM _poly . readAt ?labPolys) $ IS.toList g
  let
    loop ds t00 = do
      case H.uncons t00 of
        Nothing -> return ds
        Just (Entry rk k, t) -> do
          writeAt ?labPolys k $ nf rk pgs
          (ks, t'0) <- topReduction k (g' `IS.union` ds) g
          t' <- mapM (\l -> flip Entry l <$> readAt ?labPolys l) t'0
          loop (ds `IS.union` IS.fromList ks) (t `H.union` H.fromList t')
  loop IS.empty . H.fromList =<< mapM (\l -> flip Entry l <$> readAt ?labPolys l) t0


findReductor :: (Eq r, ?labPolys :: RefVector s (PolyRepr r ord n),
                ?rules :: RefVector s (Rule ord n), SingRep n,
                DecidableZero r, Noetherian r, IsMonomialOrder ord)
             => Int -> IntSet -> IntSet -> ST s (Maybe Int)
findReductor k g' g = do
  rk <- readAt ?labPolys k
  let t = leadingMonomial $ rk ^. poly
      cond j = do
        rj <- readAt ?labPolys j
        let t' = leadingMonomial $ rj ^. poly
            (_, vj) = rj ^. signature
            u  = t/t'
        p1 <- isRewritable u j
        p2 <- isTopReducible (u*vj) g
        return $ t' `divs` t
              && (u *@ rj)^.signature  /= view signature rk
              && not p1 && not p2
  listToMaybe <$> filterM cond (IS.toList g')

topReduction :: (Eq r, ?labPolys :: (RefVector s (PolyRepr r ord n)),
                 ?rules :: (RefVector s (Rule ord n)), SingRep n,
                 DecidableZero r, Division r, Noetherian r, IsMonomialOrder ord)
             => Int -> IntSet -> IntSet -> ST s ([Int], [Int])
topReduction k g' g = do
  rk <- readAt ?labPolys k
  let p = rk ^. poly
  if isZero p
     then return ([], [])
     else do
  mj <- findReductor k g' g
  case mj of
    Nothing -> do
      writeAt ?labPolys k $ rk & poly %~ monoize
      return ([k], [])
    Just j ->  do
      rj <- readAt ?labPolys j
      let q = rj ^. poly
          u = leadingMonomial p / leadingMonomial q
          c = leadingCoeff p % leadingCoeff q
          p' = monoize $ p - c * toPolynomial (one, u) * q
      if u *@ rj < rk
        then do
          writeAt ?labPolys k $ rk & poly .~ p'
          return ([], [k])
        else do
          n <- lengthMV ?labPolys
          snoc ?labPolys $ (u *@ rj) & poly .~ p'
          addRule -- n
          return ([], [k, n])

spols :: (?labPolys :: (RefVector s (PolyRepr r ord n)),
          ?rules :: (RefVector s (Rule ord n)), Eq r,
          SingRep n,
          DecidableZero r, Division r, Noetherian r, IsMonomialOrder ord)
      => [CriticalPair ord n] -> ST s [Int]
spols bs = do
  map payload . T.toList <$> foldrM step H.empty (sortBy (comparing $ view _1) bs)
  where
    step (_, u,k,v,l) fs = do
      rk <- readAt ?labPolys k
      rl <- readAt ?labPolys l
      p1 <- isRewritable u k
      p2 <- isRewritable v l
      if not p1 && not p2
        then do
          let s0 = monoize $ sPolynomial (rk^.poly)  (rl^.poly)
              rn = (u *@ rk) & poly .~ s0
          snoc ?labPolys rn
          n <- lengthMV ?labPolys
          addRule  -- (n-1)
          if isZero s0
            then return fs
            else return $ insert (Entry rn (n-1)) fs
        else return fs

addRule :: (IsMonomialOrder ord, Noetherian r, DecidableZero r, ?labPolys :: (RefVector s (PolyRepr r ord n)),
            ?rules :: (RefVector s (Rule ord n)), SingRep n)
        => ST s ()
addRule = do
  j <- MV.length <$> readSTRef ?labPolys
  (i, t) <- view signature <$> readAt ?labPolys j
  writeAt ?rules i . ((t, j):) =<< readAt ?rules i

isRewritable :: (?labPolys :: (RefVector s (PolyRepr r ord n)),
                 ?rules :: (RefVector s (Rule ord n)))
              => OrderedMonomial ord n -> Int -> ST s Bool
isRewritable u k = do
  k' <- rewrite u k
  return $ k /= k'

rewrite :: (?labPolys :: (RefVector s (PolyRepr r ord n)),
            ?rules :: (RefVector s (Rule ord n)))
        => OrderedMonomial ord n -> Int -> ST s Int
rewrite u k = do
  (l, v) <- view signature <$> readAt ?labPolys k
  rs <- readAt ?rules l
  return $ maybe k snd $ find (\(t, _) -> t `divs` (u * v)) rs

criticalPair :: (?labPolys :: RefVector s (PolyRepr r ord n),
                 Eq r, SingRep n, DecidableZero r, Noetherian r, IsMonomialOrder ord)
             => Int
             -> Int
             -> Int
             -> IntSet
             -> ST s (Maybe (CriticalPair ord n))
criticalPair k l i g = do
  rk <- readAt ?labPolys k
  rl <- readAt ?labPolys l
  let tk = leadingMonomial $ rk^.poly
      tl = leadingMonomial $ rl^.poly
      t  = lcmMonomial tk tl
      u1 = t / leadingMonomial (rk^.poly)
      u2 = t / leadingMonomial (rl^.poly)
      (k1, t1) = rk ^. signature
      (k2, t2) = rl ^. signature
  p1 <- isTopReducible (u1 * t1) g
  p2 <- isTopReducible (u2 * t2) g
  if k1 == i && p1 || k2 == i && p2
    then return Nothing
    else if u1 *@ rk < u2 *@ rl
         then return $ Just (t, u2, l, u1, k)
         else return $ Just (t, u1, k, u2, l)

isTopReducible :: (?labPolys :: RefVector s (PolyRepr r ord n), SingRep n,
                   DecidableZero r, Noetherian r, IsMonomialOrder ord)
               => OrderedMonomial ord n -> IntSet -> ST s Bool
isTopReducible f gs =
  any (`divs` f) <$> mapM (liftM (leadingMonomial . view poly) . readAt ?labPolys) (IS.toList gs)

readAt :: STRef s (MV.MVector s b) -> Int -> ST s b
readAt m i = flip MV.read i =<< readSTRef m

writeAt :: STRef s (MV.MVector s a) -> Int -> a -> ST s ()
writeAt m i x = do
  v <- readSTRef m
  MV.write v i x

snoc :: STRef s (MV.MVector s a) -> a -> ST s ()
snoc m x = do
  v <- flip MV.grow 1 =<< readSTRef m
  MV.write v (MV.length v - 1) x
  writeSTRef m v

lengthMV :: STRef s1 (MV.MVector s a) -> ST s1 Int
lengthMV = liftM MV.length . readSTRef

