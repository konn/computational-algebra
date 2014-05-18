{-# LANGUAGE ConstraintKinds, DeriveDataTypeable, FlexibleContexts      #-}
{-# LANGUAGE ImplicitParams, MultiParamTypeClasses, NoImplicitPrelude   #-}
{-# LANGUAGE NoMonomorphismRestriction, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell, TypeOperators                             #-}
module Algebra.Algorithms.Faugere5 where
import           Algebra.Algorithms.Groebner
import           Algebra.Prelude
import           Algebra.Ring.Noetherian
import           Control.Applicative         ((<$>))
import           Control.Arrow               ((>>>))
import           Control.Lens                (makeLenses, view, (%~), (&), (.~))
import           Control.Lens                ((^.), _1, _2)
import           Control.Monad               (filterM, forM_, liftM, when)
import           Control.Monad.Loops         (anyM, whileM_)
import           Control.Monad.ST            (ST, runST)
import           Control.Monad.ST.Unsafe     (unsafeIOToST)
import           Control.Monad.Trans         (lift)
import           Control.Monad.Trans.Loop    (exit, foreach)
import           Data.Foldable               (foldrM)
import qualified Data.Foldable               as T
import           Data.Heap                   (Entry (..), insert)
import qualified Data.Heap                   as H
import qualified Data.IntSet                 as IS
import           Data.List                   (find, minimumBy, partition)
import           Data.Maybe                  (listToMaybe)
import           Data.Monoid                 ((<>))
import           Data.Ord                    (comparing)
import           Data.Singletons             (SingRep)
import           Data.STRef                  (modifySTRef', newSTRef, readSTRef)
import           Data.STRef                  (writeSTRef)
import           Data.STRef                  (STRef)
import           Data.Vector                 (unsafeFreeze)
import qualified Data.Vector                 as V
import qualified Data.Vector.Mutable         as MV
import           Numeric.Decidable.Zero      (isZero)

type CriticalPair ord n = (OrderedMonomial ord n, OrderedMonomial ord n, Int, OrderedMonomial ord n, Int)
type Rule ord n = [(OrderedMonomial ord n, Int)]

data PolyRepr r ord n = PolyRepr { _signature :: (Int, OrderedMonomial ord n)
                                 , _poly      :: OrderedPolynomial r ord n
                                 } deriving (Show, Eq)

type RefVector s a = STRef s (MV.MVector s a)

monoize f | isZero f  = zero
          | otherwise = recip (leadingCoeff f) .*. f

makeLenses ''PolyRepr

instance (Noetherian r, IsOrder ord, DecidableZero r, SingRep n, Eq r)
      => Ord (PolyRepr r ord n) where
  PolyRepr (i, t) _ `compare` PolyRepr (j, u) _ =
    j `compare` i <> t `compare` u

(*|) :: (DecidableZero r, Eq r, IsOrder ord, SingRep n, Noetherian r)
     => r -> PolyRepr r ord n -> PolyRepr r ord n
(*|) k = poly %~ (k .*.)

(*@) :: (DecidableZero r, Eq r, IsOrder ord, SingRep n, Noetherian r)
     => OrderedMonomial ord n -> PolyRepr r ord n -> PolyRepr r ord n
(*@) v = (signature._2 %~ (v*)) >>> (poly %~ (toPolynomial (one, v) *))

nf :: (DecidableZero r, Eq r, SingRep n, Division r, Noetherian r, IsMonomialOrder ord)
   => PolyRepr r ord n -> [OrderedPolynomial r ord n] -> PolyRepr r ord n
nf r g = r & poly %~ (`modPolynomial` g)

infixl 7 *|, *@

f5Original :: (Show r, Eq r, DecidableZero r, SingRep n, Division r, Noetherian r, IsMonomialOrder ord)
           => Ideal (OrderedPolynomial r ord n) -> Ideal (OrderedPolynomial r ord n)
f5Original = mainLoop

mainLoop :: (Show r, IsMonomialOrder ord, IsPolynomial r n, Field r)
         => Ideal (OrderedPolynomial r ord n) -> Ideal (OrderedPolynomial r ord n)
mainLoop ideal = runST $ do
  let gs = generators ideal
      m  = length gs
      f0 = head gs
  lps0 <- newSTRef =<< MV.new m
  writeAt lps0 (m-1) (PolyRepr (m-1, one) $ monoize f0)
  rs0  <- newSTRef =<< MV.replicate m []
  g    <- MV.replicate m []
  MV.write g (m-1) [m-1]
  let ?labPolys = lps0
      ?rules    = rs0
  foreach (zip (reverse $ init gs) [m-2,m-3..0]) $ \(h, i) -> do
    lift $! unsafeIOToST $! putStr "iteration: \t" >> print (i, h)
    v000 <- lift $ V.freeze =<< readSTRef ?labPolys
    lift $! unsafeIOToST $! putStr "\tlabs = " >> print (drop (i+1) $ zip [(0::Int)..] $ V.toList v000)
    gi <- lift $ f5Core h i g
    lift $! unsafeIOToST $! putStr "\tgi =" >> print gi
    p  <- anyM (liftM ((== one) . _poly) . lift . readAt lps0) gi
    lift $! unsafeIOToST $! putStr "\texit? " >> print p
    when p $ do
      lift $ MV.write g 0 []
      exit
    lift $ MV.write g i gi
    test <- lift $ V.freeze g
    lift $! unsafeIOToST $! putStr "\t g[i..] = " >> print test
  g0 <- MV.read g 0
  if null g0 then return $ toIdeal [one]
    else toIdeal <$> mapM (liftM _poly . readAt lps0) g0

f5Core :: (Show r, ?labPolys :: (RefVector s (PolyRepr r ord n)),
           ?rules :: (RefVector s (Rule ord n)),
           Eq r, Division r, SingRep n, DecidableZero r, Noetherian r, IsMonomialOrder ord)
       => OrderedPolynomial r ord n
       -> Int -> MV.MVector s [Int]
       -> ST s [Int]
f5Core f i g = do
  unsafeIOToST $! putStr "f5Core:\t" >> print (f, i)
  writeAt ?labPolys i $ PolyRepr (i, one) (leadingCoeff f .*. f)
  unsafeIOToST $ putStr "\tr_{i+1} = "
  unsafeIOToST . print =<< readAt ?labPolys (i+1)
  unsafeIOToST $! putStr "\tr_i = " >> print (PolyRepr (i, one) (leadingCoeff f .*. f))
  gi1 <- MV.read g (i+1)
  unsafeIOToST $! putStr ("\tG_" ++ show (i+1) ++ "=") >> print gi1
  g' <- newSTRef $ i : gi1
  ps <- newSTRef . concat =<< mapM (\j -> criticalPair i j g) gi1
  unsafeIOToST $ putStr "core: ps = "
  unsafeIOToST . print =<< readSTRef ps
  whileM_ (not . null <$> (readSTRef ps)) $ do
    p <- readSTRef ps
    unsafeIOToST $ putStr "\titer p = " >> print p
    let d = minimum $ map (totalDegree.view _1) p
        (pd, p') = partition ((== d) . totalDegree . view _1) p
    unsafeIOToST $ putStr "\titer (d, pd, p') = " >> print (d, pd, p')
    sd <- spols pd
    unsafeIOToST $ putStr "\tsd = " >> print sd
    g'0 <- readSTRef g'
    rd <- reduction sd g'0 . V.toList =<< V.freeze g
    writeSTRef ps p'
    forM_ rd $ \k -> do
      p0 <- readSTRef ps
      pss <- mapM (\l -> criticalPair k l g) =<< readSTRef g'
      writeSTRef ps $ concat pss ++ p0
      modifySTRef' g' (k:)
  readSTRef g'

reduction :: (Eq r, ?labPolys :: (RefVector s (PolyRepr r ord n)),
              ?rules :: (RefVector s (Rule ord n)),Show r,
              SingRep n, DecidableZero r, Division r, Noetherian r,
              IsMonomialOrder ord)
          => [Int] -> [Int] -> [[Int]] -> ST s [Int]
reduction t0 g' g = unsafeIOToST (putStrLn $ "reduction: "++ show (t0,g',g)) >> loop IS.empty (IS.fromList t0)
  where
    loop ds t | IS.null t = return $ IS.elems ds
    loop ds t00  = do
      k   <- fst . minimumBy (comparing snd) <$> mapM (\l -> (,) l <$> readAt ?labPolys l) (IS.toList t00)
      let t = IS.delete k t00
      rk  <- readAt ?labPolys k
      pgs <- mapM (liftM _poly .  readAt ?labPolys) g'
      let h = _poly rk `modPolynomial` pgs
      writeAt ?labPolys k $ PolyRepr (_signature rk) h
      (ks, t') <- topReduction k (g' ++ IS.toList ds) g
      loop (ds `IS.union` IS.fromList ks) (t `IS.union` IS.fromList t')

findReductor :: (Eq r, ?labPolys :: RefVector s (PolyRepr r ord n),
                ?rules :: RefVector s (Rule ord n), SingRep n,
                DecidableZero r, Noetherian r, IsOrder ord)
             => Int -> [Int] -> [[Int]] -> ST s (Maybe Int)
findReductor k g' g = do
  t <- leadingMonomial . view poly <$> readAt ?labPolys k
  let cond j = do
        rj <- readAt ?labPolys k
        let t' = leadingMonomial $ view poly rj
            (kj, vj) = rj ^. signature
        if t' `divs` t
          then do
            let u = t / t'
            p1 <- isRewritable u j
            p2 <- isTopReducible (u*vj) $ g !! kj
            return $ view signature (u *@ rj) /= view signature rj
              && not p1 && not p2
          else return False
  listToMaybe <$> filterM cond g'

topReduction :: (Eq r, ?labPolys :: (RefVector s (PolyRepr r ord n)),
                 ?rules :: (RefVector s (Rule ord n)), SingRep n, Show r,
                 DecidableZero r, Division r, Noetherian r, IsOrder ord)
             => Int -> [Int] -> [[Int]] -> ST s ([Int], [Int])
topReduction k g' g = do
  unsafeIOToST $ putStr "topReduce: ">> print (k, g', g)
  rk <- readAt ?labPolys k
  unsafeIOToST $ putStr ("\t r_" ++ show k ++ " = ") >> print rk
  let f = rk ^. poly
  mj <- findReductor k g' g
  case mj of
    Nothing -> do
      let f' = monoize f
      writeAt ?labPolys k $ rk & poly .~ f'
      return ([k], [])
    Just j ->  do
      rj <- readAt ?labPolys j
      let q = rj ^. poly
          u = leadingMonomial f / leadingMonomial q
          f' = f - (leadingCoeff f / leadingCoeff q) .*. (toPolynomial (one, u) * q)
      if u *@ rj < rk
        then do
          writeAt ?labPolys k $ rk & poly .~ f'
          return ([], [k])
        else do
          n <- lengthMV ?labPolys
          writeAt ?labPolys n $ (u *@ rj) & poly .~ f'
          addRule n
          return ([], [k, n])

spols :: (?labPolys :: (RefVector s (PolyRepr r ord n)),
          ?rules :: (RefVector s (Rule ord n)),
          SingRep n, Show r,
          DecidableZero r, Division r, Noetherian r, IsOrder ord)
      => [CriticalPair ord n] -> ST s [Int]
spols bs = do
  unsafeIOToST $ putStr "spols: " >> print bs
  map payload . T.toList <$> foldrM step H.empty bs
  where
    step (_, u,k,v,l) fs = do
      unsafeIOToST $ putStr "\tspol-iter: (u,k,v,l,fs) = " >> print (u,k,v,l,fs)
      rk <- readAt ?labPolys k
      rl <- readAt ?labPolys l
      unsafeIOToST $ putStr "\t\t(rk, rl) = " >> print (rk, rl)
      let c1 = leadingCoeff $ rk^.poly
          c2 = leadingCoeff $ rl^.poly
          s0  = toPolynomial (one, u) * (rk ^. poly)
               - toPolynomial (one, v) * ((c1/c2).*.(rl ^. poly))
      p1 <- isRewritable u k
      unsafeIOToST $ putStr "\t\trewrite?(u, k) = " >> print p1
      p2 <- isRewritable v l
      unsafeIOToST $ putStr "\t\trewrite?(v, l) = " >> print p2
      if not (isZero s0) && not p1 && not p2
        then do
          let rn = rl & signature._2 %~ (*u)
                      & poly .~ s0
          snoc ?labPolys rn
          n <- lengthMV ?labPolys
          addRule (n-1)
          return $ insert (Entry (rn^.signature) (n-1)) fs
        else return fs

addRule :: (IsOrder ord, Show r, Noetherian r, DecidableZero r, ?labPolys :: (RefVector s (PolyRepr r ord n)),
            ?rules :: (RefVector s (Rule ord n)), SingRep n)
        => Int -> ST s ()
addRule j = do
  unsafeIOToST $ putStr $ "addRule(" ++ show j ++ "): r_j = "
  unsafeIOToST . print =<< readAt ?labPolys j
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

criticalPair :: (Show r, ?labPolys :: RefVector s (PolyRepr r ord n),
                 Eq r, SingRep n, DecidableZero r, Noetherian r, IsOrder ord)
             => Int
             -> Int
             -> MV.MVector s [Int]
             -> ST s [CriticalPair ord n]
criticalPair k0 l0 gs = do
  unsafeIOToST $! putStr "criticalPair: " >> print (k0, l0)
  rk <- readAt ?labPolys k0
  rl <- readAt ?labPolys l0
  unsafeIOToST $! putStr (concat ["\t(r_", show k0, ", r_", show l0, ") = "]) >> print (view poly rk, view poly rl)
  let t  = lcmMonomial (leadingMonomial $ rk^.poly) (leadingMonomial $ rl^.poly)
      u10 = t / leadingMonomial (rk^.poly)
      u20 = t / leadingMonomial (rl^.poly)
      (k, l, u1, u2)
        | u10 *@ rk < u20 *@ rl = (l0, k0, u20, u10)
        | otherwise = (k0, l0, u10, u20)
  unsafeIOToST $! putStr (concat ["\t(t, r_", show k, ", r_", show l, ") = "]) >> print (t, view poly rk, view poly rl)
  unsafeIOToST $! putStr "\t(S(rk), S(rl)) = " >> print (rk^.signature, rl^.signature)
  unsafeIOToST $! putStr "\t(k, l, u1, u2) = " >> print (k, l, u1, u2)
  (k1, t1) <- view signature <$> readAt ?labPolys k
  (k2, t2) <- view signature <$> readAt ?labPolys l
  unsafeIOToST $! putStr "\t(k1,t1,k2,t2)= " >> print (k1, t1, k2, t2)
  gk1 <- MV.read gs k1
  p1 <- isTopReducible (u1 * t1) gk1
  rrr <- mapM (liftM (view poly) . readAt ?labPolys) gk1
  unsafeIOToST $! putStr "\t(u1, t1, u1*t1, gk1): " >> print (u1, t1, u1*t1, rrr)
  unsafeIOToST $! putStr "\tu1*t1 top red by gk1? " >> print p1
  if p1
    then return []
    else do
      gk2 <- MV.read gs k2
      p2 <- isTopReducible (u2*t2) gk2
      if p2
         then return []
         else return [(t, u1, k, u2, l)]

isTopReducible :: (?labPolys :: RefVector s (PolyRepr r ord n), SingRep n,
                   DecidableZero r, Noetherian r, IsOrder ord)
               => OrderedMonomial ord n -> [Int] -> ST s Bool
isTopReducible f gs = any (\g -> leadingMonomial (g^.poly) `divs` f) <$> mapM (readAt ?labPolys) gs

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
