{-# LANGUAGE BangPatterns, ConstraintKinds, DataKinds, DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts, GADTs, ImplicitParams                      #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude                     #-}
{-# LANGUAGE NoMonomorphismRestriction, ParallelListComp, RankNTypes      #-}
{-# LANGUAGE ScopedTypeVariables, TemplateHaskell, TupleSections          #-}
{-# LANGUAGE TypeOperators, ViewPatterns                                  #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module Algebra.Algorithms.Faugere5 (f5Original, showSingular) where
import Algebra.Algorithms.Groebner
import Algebra.Prelude.Core        hiding (insert)

import           Control.Arrow           ((>>>))
import           Control.Lens            (makeLenses, view, (%~), (&), (.~))
import           Control.Lens            ((^.), _1, _2)
import           Control.Monad           (filterM, forM_, liftM, when)
import           Control.Monad           (zipWithM_)
import           Control.Monad.Loops     (anyM, whileM_)
import           Control.Monad.ST        (ST, runST)
import           Control.Monad.ST.Unsafe (unsafeIOToST)
import           Data.Foldable           (foldrM)
import qualified Data.Foldable           as T
import           Data.Function           (on)
import           Data.Heap               (Entry (..), insert)
import qualified Data.Heap               as H
import           Data.IntSet             (IntSet)
import qualified Data.IntSet             as IS
import           Data.List               (find, partition, sort, sortBy)
import           Data.List               (tails)
import           Data.Maybe              (listToMaybe)
import           Data.Monoid             ((<>))
import           Data.Ord                (comparing)
import           Data.STRef              (STRef, modifySTRef', newSTRef)
import           Data.STRef              (readSTRef, writeSTRef)
import qualified Data.Vector             as V
import qualified Data.Vector.Mutable     as MV
import           Numeric.Decidable.Zero  (isZero)
import           Text.Printf             (printf)


{-
unsafeIOToST :: Monad m => t -> m ()
unsafeIOToST _ = return ()
-}

type CriticalPair ord n = (OrderedMonomial ord n, OrderedMonomial ord n, Int, OrderedMonomial ord n, Int)
type Rule ord n = [(OrderedMonomial ord n, Maybe Int)]

data PolyRepr r ord n =
  PolyRepr { _signature :: (Int, OrderedMonomial ord n)
           , _poly      :: OrderedPolynomial r ord n
           }

showsIf :: Bool -> ShowS -> ShowS
showsIf True  a = a
showsIf False _ = id

instance (CoeffRing r, PrettyCoeff r, KnownNat n, IsMonomialOrder n ord)
         => Show (PolyRepr r ord n) where
  showsPrec _ (PolyRepr (n, m) p) = showParen True $
    showsIf (m /= one) (shows m . showChar ' ') . showString "F_" . shows n . showString ", " . shows p

type RefVector s a = STRef s (MV.MVector s a)

makeLenses ''PolyRepr

instance Eq (PolyRepr r ord n) where
  (==) = (==) `on` view signature

instance (IsMonomialOrder n ord) => Ord (PolyRepr r ord n) where
  compare = comparing $ view signature

(*@) :: (CoeffRing r, IsMonomialOrder n ord, KnownNat n)
     => OrderedMonomial ord n -> PolyRepr r ord n -> PolyRepr r ord n
(*@) v = (signature._2 %~ (v*)) >>> (poly %~ (toPolynomial (one, v) *))

nf :: (Eq r, KnownNat n, Field r, IsMonomialOrder n ord)
   => PolyRepr r ord n -> [OrderedPolynomial r ord n] -> PolyRepr r ord n
nf r g = r & poly %~ (`modPolynomial` g)

infixl 7 *@

preReduction :: (Eq r, KnownNat n, Field r, IsMonomialOrder n order)
             => [OrderedPolynomial r order n] -> [OrderedPolynomial r order n]
preReduction fs = map monoize $ go [] fs
  where
    go xs []    = xs
    go xs (y:ys) =
      let r = y `modPolynomial` (xs++ys)
      in if r == y
         then go (xs++[y]) ys
         else go [] (xs ++ if isZero r then ys else r : ys)

f5Original :: (PrettyCoeff r, Ord r, KnownNat n, Field r, IsMonomialOrder n ord)
           => Ideal (OrderedPolynomial r ord n) -> Ideal (OrderedPolynomial r ord n)
f5Original = toIdeal . sort . generators . mainLoop

mainLoop :: (PrettyCoeff r, IsMonomialOrder n ord, CoeffRing r, KnownNat n, Field r)
         => Ideal (OrderedPolynomial r ord n) -> Ideal (OrderedPolynomial r ord n)
mainLoop (preReduction . filter (not . isZero) . generators -> ij)
  | null ij = toIdeal [zero]
  | otherwise = runST $ do
  let (f0 : fs) =
        sortBy (comparing totalDegree' <> comparing leadingMonomial) ij
  lps0 <- newSTRef =<< V.unsafeThaw (V.singleton (PolyRepr (0, one) f0))
  rs0  <- newSTRef =<< V.unsafeThaw (V.fromList [[]])
  let ?labPolys = lps0
      ?rules    = rs0
  loop [f0] (IS.fromList [0]) fs
  where
    loop bs _ [] = return $ toIdeal bs
    loop bs g (f:xs) = do
      rlen <- lengthMV ?labPolys
      unsafeIOToST $ putStrLn $ show (rlen+1) ++ "th iteration"
      addLabPoly $ PolyRepr (rlen, one) f
      g' <- f5Core rlen bs g
      p  <- anyM (liftM ((== one) . view poly) . readAt ?labPolys) $ IS.toList g'
      if p
        then return $ toIdeal [one]
        else do
        !g'' <- setupReducedBasis g'
        !bs' <- toPolys g''
        -- unsafeIOToST $ putStrLn $ concat
        --  ["reduced(", show i, "th): ", show (isGroebnerBasis $ toIdeal bs'), ", ", show bs']
        loop bs' g'' xs

interred :: (Eq k, KnownNat n, Field k, IsMonomialOrder n order)
         => [OrderedPolynomial k order n] -> [OrderedPolynomial k order n]
interred = reduceMinimalGroebnerBasis . minimizeGroebnerBasis

toPolys :: (?labPolys::STRef s (MV.MVector s (PolyRepr r ord n)))
        => IntSet -> ST s [OrderedPolynomial r ord n]
toPolys = mapM (liftM (view poly) . readAt ?labPolys) . IS.toList

setupReducedBasis :: (Eq r, ?labPolys :: STRef s (MV.MVector s (PolyRepr r ord n)),
                     ?rules :: STRef s (MV.MVector s (Rule ord n)),
                     KnownNat n, Field r, IsMonomialOrder n ord)
                 => IntSet -> ST s IntSet
setupReducedBasis gs = do
  bs <- interred <$> toPolys gs
  -- unsafeIOToST $ putStr "setup for: " >> print bs
  let count = length bs
      g0 = [0..count-1]
  writeSTRef ?labPolys
    =<< V.unsafeThaw (V.fromList $ [ PolyRepr (j, one) h
                                   | h <- bs
                                   | j <- [0..] ])
  writeSTRef ?rules =<< MV.replicate count []
  zipWithM_ zeroRule (tails bs) [0..]
  return $ IS.fromList g0
  where
    zeroRule []     _ = return ()
    zeroRule (f:fs) j =
      let !t = leadingMonomial f
      in forM_ (zip [j+1..] fs) $ \(k, fk) -> do
        let !u = t / gcdMonomial (leadingMonomial fk) t
        addRule (k, u) Nothing

f5Core :: ( ?labPolys :: (RefVector s (PolyRepr r ord n)),
           ?rules :: (RefVector s (Rule ord n)), PrettyCoeff r,
           Eq r, Field r, KnownNat n, IsMonomialOrder n ord)
       => Int
       -> [OrderedPolynomial r ord n]
       -> IntSet
       -> ST s IntSet
f5Core i bs g = do
  curIdx <- pred . MV.length <$> readSTRef ?labPolys
  g' <- newSTRef $ IS.insert curIdx g
  ps <- newSTRef =<< mapMaybeM (\j -> criticalPair curIdx j i g) (IS.toList g)
  whileM_ (not . null <$> readSTRef ps) $ do
    p <- readSTRef ps
    let d = minimum $ map (totalDegree.view _1) p
        (pd, p') = partition ((== d) . totalDegree . view _1) p
    unsafeIOToST $ printf "processing %d critical pairs of degree %d\n" (length pd) d
    writeSTRef ps p'
    sd <- spols pd
    rd <- reduction sd bs g =<< readSTRef g'
    forM_ (IS.toList rd) $ \k -> do
      unsafeIOToST . printf "polynomial %d reduced to %s\n" (k+1) . showSingular . view poly =<< readAt ?labPolys k
      pss <- mapMaybeM (\j -> criticalPair j k i g) . IS.toList =<< readSTRef g'
      modifySTRef' ps (pss ++)
      modifySTRef' g' (IS.insert k)
  readSTRef g'

replace :: Eq b => b -> b -> [b] -> [b]
replace f t = map (\c -> if c == f then t else c)

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
              ?rules :: (RefVector s (Rule ord n)), PrettyCoeff r,
              KnownNat n, Field r,
              IsMonomialOrder n ord)
          => [Int] -> [OrderedPolynomial r ord n] -> IntSet -> IntSet -> ST s IntSet
reduction t0 bs g g' =
  loop IS.empty . H.fromList =<< mapM (\l -> flip Entry l . view signature <$> readAt ?labPolys l) t0
  where
    loop !completed !todo =
      case H.uncons todo of
        Nothing -> return completed
        Just (Entry _ k, todo') -> do
          rk <- readAt ?labPolys k
          writeAt ?labPolys k $ nf rk bs
          (new, redo) <- topReduction k g (g' `IS.union` completed)
          redo' <- mapM (\l -> flip Entry l . view signature <$> readAt ?labPolys l) redo
          loop (completed `IS.union` IS.fromList new) (todo' `H.union` H.fromList redo')

findReductor :: (CoeffRing r, ?labPolys :: RefVector s (PolyRepr r ord n),
                ?rules :: RefVector s (Rule ord n), KnownNat n,
                IsMonomialOrder n ord)
             => Int -> IntSet -> IntSet -> ST s (Maybe Int)
findReductor k g g' = do
  rk <- readAt ?labPolys k
  let t = leadingMonomial $! rk ^. poly
      cond j = do
        rj <- readAt ?labPolys j
        let t' = leadingMonomial $ rj ^. poly
            (_, vj) = rj ^. signature
            u  = t/t'
        p1 <- isRewritable u j
        p2 <- isTopReducible (u*vj) g
        return $ t' `divs` t
              -- && (u *@ rj)^.signature  /= rk ^. signature
              && not p1 && not p2
  listToMaybe <$> filterM cond (IS.toList g')

topReduction :: (Eq r, ?labPolys :: (RefVector s (PolyRepr r ord n)),
                 ?rules :: (RefVector s (Rule ord n)), KnownNat n, PrettyCoeff r,
                 Field r, IsMonomialOrder n ord)
             => Int -> IntSet -> IntSet -> ST s ([Int], [Int])
topReduction k g g' = do
  rk <- readAt ?labPolys k
  let !p = rk ^. poly
  if isZero p
    then do
      unsafeIOToST $ printf "Polynomial %d reduced to zero!\n" (k+1)
      return ([], [])
    else do
      mj <- findReductor k g g'
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
              addLabPoly $ (u *@ rj) & poly .~ p'
              unsafeIOToST $
                printf "In topreduction pair (%d,%d) generated polynomial %d:%s\n" (k+1) (j+1) n (showSingular p)
              addRule ((u*@rj) ^. signature) $ Just n
              return ([], [k, n])

spols :: (?labPolys :: (RefVector s (PolyRepr r ord n)),
          ?rules :: (RefVector s (Rule ord n)), Eq r,
          KnownNat n, PrettyCoeff r,
          Field r, IsMonomialOrder n ord)
      => [CriticalPair ord n] -> ST s [Int]
spols bs =
  map payload . T.toList <$> foldrM step H.empty (sortBy (comparing $ view _1) bs)
  where
    step (_, _, k, _,l) fs = do
      rk <- readAt ?labPolys k
      rl <- readAt ?labPolys l
      let t1 = leadingMonomial $ rk^.poly
          t2 = leadingMonomial $ rl^.poly
          u = t2 / gcdMonomial t1 t2
          v = t1 / gcdMonomial t1 t2
      p1 <- isRewritable u k
      p2 <- isRewritable v l
      if not p1 && not p2
        then do
          let (fk, fl) = (rk^.poly, rl^.poly)
              s0 = monoize $ leadingCoeff fl % one * toPolynomial (one, u) * fk
                   - leadingCoeff fk %one * toPolynomial (one, v) * fl
              rn = (u *@ rk) & poly .~ s0
          n <- lengthMV ?labPolys
          addLabPoly rn
          --unsafeIOToST $ putStrLn $ concat
          --  [ "spol with: Rule = ", drop 9 $ show rs, ", ((k,u),n) = ", show ((k, u), n)]
          addRule (k, u*(rk^.signature._2)) (Just n)
          if isZero s0
            then return fs
            else do
            count <- lengthMV ?labPolys
            unsafeIOToST $
              printf "In spols pair (%d,%d) generated polynomial %d:%s\n" (k+1) (l+1) count (showSingular s0)
            return $ insert (Entry (rn^.signature) n) fs
        else return fs

addLabPoly :: (?labPolys :: STRef s (MV.MVector s a),
               ?rules :: STRef s (MV.MVector s [a1])) => a -> ST s ()
addLabPoly r = snoc ?labPolys r >> snoc ?rules []

addRule :: (?rules :: (RefVector s (Rule ord n)))
        => (Int, OrderedMonomial ord n) -> Maybe Int -> ST s ()
addRule (n, m) k = do
  --unsafeIOToST $ putStr ("\tadding rule for" ++ show ((n,m),k) ++ ": ") >> print cst
  writeAt ?rules n . ((m, k):) =<< readAt ?rules n
  --unsafeIOToST . putStrLn . ("\tnew rule : "++).show =<< V.freeze =<< readSTRef ?rules

isRewritable :: (?labPolys :: (RefVector s (PolyRepr r ord n)),
                 ?rules :: (RefVector s (Rule ord n)))
              => OrderedMonomial ord n -> Int -> ST s Bool
isRewritable u k = do
  j <- rewrite u k
  return $ Just k /= j

rewrite :: (?labPolys :: (RefVector s (PolyRepr r ord n)),
            ?rules :: (RefVector s (Rule ord n)))
        => OrderedMonomial ord n -> Int -> ST s (Maybe Int)
rewrite u k = do
  (l, v) <- view signature <$> readAt ?labPolys k
  rs <- readAt ?rules l
  return $ maybe (Just k) snd $ find (\(t, _) -> t `divs` (u * v)) rs

criticalPair :: (?labPolys :: RefVector s (PolyRepr r ord n),
                 ?rules::RefVector s (Rule ord n),
                 CoeffRing r, KnownNat n, IsMonomialOrder n ord)
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
      tgcd = gcdMonomial tk tl
      u1 = tl / tgcd
      u2 = tk / tgcd
      (k1, t1) = rk ^. signature
      (k2, t2) = rl ^. signature
  p1 <- isTopReducible (u1 * t1) g
  p2 <- isTopReducible (u2 * t2) g
  q1 <- isRewritable u1 k
  q2 <- isRewritable u2 l
  when ((u1 *@ rk)^.signature == (u2 *@ rl)^.signature ||
        k1 == i && p1 || k2 == i && p2 || q1 || q2) $ unsafeIOToST $
    printf "  (%d,%d): %s, %s was rejected\n" (k+1) (l+1) (show $ (u1*@rk)^.signature._2) (show $ (u2*@rl)^.signature._2)
  return $! if (u1 *@ rk)^.signature == (u2 *@ rl)^.signature ||
     k1 == i && p1 || k2 == i && p2 || q1 || q2
    then Nothing
    else Just $ if (u1 *@ rk)^.signature < (u2 *@ rl)^.signature
         then (t, u2, l, u1, k)
         else (t, u1, k, u2, l)

isTopReducible :: (?labPolys :: RefVector s (PolyRepr r ord n), KnownNat n,
                   CoeffRing r, IsMonomialOrder n ord)
               => OrderedMonomial ord n -> IntSet -> ST s Bool
isTopReducible f gs =
  anyM (liftM ((`divs` f) . leadingMonomial . view poly) . readAt ?labPolys) (IS.toList gs)

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

showSingular :: (KnownNat n, IsMonomialOrder n ord, PrettyCoeff r, CoeffRing r)
             => OrderedPolynomial r ord n -> String
showSingular = replace '%' '/' . showPolynomialWith prettyVars 0
  where
    prettyVars = generate sing $ \o -> "x(" ++ show (fromEnum o) ++ ")"

ideal :: Ideal (OrderedPolynomial (Fraction Integer) Grevlex 3)
ideal = toIdeal
        [4%5 *x^2 *y *z - 5%3 *x^2 *z^2
        ,5%2 *x^4 - 4%5 *x^3 *y
        ,3%5 *x^4 - 3%2 *x^2 *y^2 + 3%5 *x^2 *y *z + 3%5 *y *z^3
        ,-5%4 *x^3 - 4%3 *y^3 + 3%7 *y *z^2]
  where
    [x,y,z] = vars
