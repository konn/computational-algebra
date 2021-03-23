{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans -Wall #-}

module Main where

import Algebra.Algorithms.Groebner
import Algebra.Algorithms.Groebner.Signature
import Algebra.Internal
import Algebra.Prelude.Core
import Control.Foldl (Fold)
import qualified Control.Foldl as Fl
import Control.Lens (_1, _2)
import Data.Monoid (Dual (..))
import Data.Sequence (Seq ((:<|), (:|>)))
import qualified Data.Sequence as Seq
import Data.Sized (unsized)
import qualified Data.Vector.Unboxed as U
import Gauge.Main

type Comparer = Fold (Int, Int) Ordering

gradeF :: Comparer
gradeF = compare <$> Fl.handles _1 Fl.sum <*> Fl.handles _2 Fl.sum
{-# INLINE gradeF #-}

lexF :: Comparer
lexF = Fl.foldMap (uncurry compare) id

revlexF :: Comparer
revlexF = Fl.foldMap (Dual . uncurry (flip compare)) getDual
{-# INLINE revlexF #-}

data FoldlGrevlex = FoldlGrevlex

instance SingI n => IsOrder n FoldlGrevlex where
  cmpMonomial _ (unsized -> m) (unsized -> n) =
    Fl.fold (gradeF <> revlexF) $ Seq.zip m n
  {-# INLINE cmpMonomial #-}

instance SingI n => IsMonomialOrder n FoldlGrevlex

newtype Seq' a = Seq' {runSeq' :: Seq a}

instance Foldable Seq' where
  foldl f z (Seq' (as :|> a)) = f (foldl f z (Seq' as)) a
  foldl _ z _ = z
  foldr f z (Seq' (a :<| as)) = f a (foldr f z (Seq' as))
  foldr _ z _ = z
  foldMap f (Seq' (as :|> a)) = foldMap f (Seq' as) <> f a
  foldMap _ _ = mempty

data Seqs a where
  Seqs :: Seq a -> Seq b -> Seqs (a, b)

instance Foldable Seqs where
  foldl f z (Seqs (as :|> a) (bs :|> b)) = f (foldl f z (Seqs as bs)) (a, b)
  foldl _ z _ = z
  foldr f z (Seqs (a :<| as) (b :<| bs)) = f (a, b) (foldr f z (Seqs as bs))
  foldr _ z _ = z

foldlSeq :: Fold a b -> Seq a -> b
foldlSeq (Fl.Fold step begin done) s = done $! loop s
  where
    loop (as :|> a) = (step $ loop as) $! a
    loop _ = begin
{-# INLINE foldlSeq #-}

data FoldlSeq'Grevlex = FoldlSeq'Grevlex

instance SingI n => IsOrder n FoldlSeq'Grevlex where
  cmpMonomial _ (unsized -> m) (unsized -> n) =
    foldlSeq (gradeF <> revlexF) $ U.zip m n
  {-# INLINE cmpMonomial #-}

instance SingI n => IsMonomialOrder n FoldlSeq'Grevlex

data FoldlSeqsGrevlex = FoldlSeqsGrevlex

foldlSeqs :: Fold (a, b) c -> Seqs (a, b) -> c
foldlSeqs (Fl.Fold step begin done) (Seqs as bs) =
  done $! loop as bs
  where
    loop (xs :|> x) (ys :|> y) = step (loop xs ys) (x, y)
    loop _ _ = begin
{-# INLINE foldlSeqs #-}

instance SingI n => IsOrder n FoldlSeqsGrevlex where
  cmpMonomial _ (unsized -> m) (unsized -> n) =
    foldlSeqs (gradeF <> revlexF) $ Seqs (toSeq m) (toSeq n)
  {-# INLINE cmpMonomial #-}

instance SingI n => IsMonomialOrder n FoldlSeqsGrevlex

grevlexHW :: Seq Int -> Seq Int -> Int -> Int -> Ordering -> Ordering
grevlexHW (as :|> a) (bs :|> b) !accl !accr EQ =
  grevlexHW as bs (accl + a) (accr + b) $ compare b a
grevlexHW as bs !accl !accr cmp = compare (sum as + accl) (sum bs + accr) <> cmp

data HandWrittenGrevlex = HandWrittenGrevlex

toSeq :: U.Unbox a => U.Vector a -> Seq a
toSeq = Seq.fromList . U.toList

instance SingI n => IsOrder n HandWrittenGrevlex where
  cmpMonomial _ (unsized -> m) (unsized -> n) = grevlexHW (toSeq m) (toSeq n) 0 0 EQ
  {-# INLINE cmpMonomial #-}

instance SingI n => IsMonomialOrder n HandWrittenGrevlex

i2 :: [OrderedPolynomial (Fraction Integer) Grevlex 5]
i2 =
  [ 35 * y ^ 4 - 30 * x * y ^ 2 - 210 * y ^ 2 * z + 3 * x ^ 2 + 30 * x * z - 105 * z ^ 2 + 140 * y * t - 21 * u
  , 5 * x * y ^ 3 - 140 * y ^ 3 * z - 3 * x ^ 2 * y + 45 * x * y * z - 420 * y * z ^ 2 + 210 * y ^ 2 * t -25 * x * t + 70 * z * t + 126 * y * u
  ]
  where
    [t, u, x, y, z] = vars

mkTC :: (IsMonomialOrder 5 ord) => String -> ord -> Benchmark
mkTC name ord =
  env (return $ toIdeal $ map (changeOrder ord) i2) $ \ideal ->
    bgroup
      name
      [ bench "calcGroebnerBasis" $ nf calcGroebnerBasis ideal
      , bench "F5" $ nf f5 ideal
      ]

main :: IO ()
main =
  defaultMain
    [ mkTC "default" Grevlex
    , mkTC "foldl" FoldlGrevlex
    , mkTC "foldl-custom" FoldlSeq'Grevlex
    , mkTC "foldl-seqs" FoldlSeqsGrevlex
    ]

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
