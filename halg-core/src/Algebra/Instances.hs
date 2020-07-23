{-# LANGUAGE BangPatterns, DataKinds, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, ScopedTypeVariables            #-}
{-# LANGUAGE TypeApplications, TypeFamilies                               #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | This Library provides some *dangerous* instances for @Double@s and @Complex@.
module Algebra.Instances () where
import Algebra.Scalar

import           AlgebraicPrelude
import           Control.DeepSeq              (NFData (..))
import           Control.Monad.Random         (Random (..), getRandom)
import           Control.Monad.Random         (getRandomR, runRand)
import           Control.Monad.ST.Strict      (runST)
import qualified Data.Coerce                  as DC
import           Data.Complex                 (Complex (..))
import           Data.Convertible.Base        (Convertible (..))
import           Data.Functor.Identity
import           Data.ListLike                (ListLike)
import qualified Data.ListLike                as LL
import           Data.MonoTraversable
import qualified Data.Primitive.PrimArray     as PA
import qualified Data.Ratio                   as P
import qualified Data.Sized.Builtin           as SV
import qualified Data.Vector                  as DV
import qualified Data.Vector.Algorithms.Intro as AI
import           Data.Vector.Instances        ()
import qualified Data.Vector.Primitive        as PV
import qualified Numeric.Algebra              as NA
import qualified Prelude                      as P
import           Unsafe.Coerce                (unsafeCoerce)
import qualified VectorBuilder.Builder        as VB
import qualified VectorBuilder.Vector         as VB

instance Additive r => Additive (DV.Vector r) where
  (+) = DV.zipWith (+)

-- | These Instances are not algebraically right, but for the sake of convenience.
instance DecidableZero r => DecidableZero (Complex r) where
  isZero (a :+ b) = isZero a && isZero b

instance (NFData a) => NFData (Fraction a) where
  rnf a = rnf (numerator a) `seq` rnf (denominator a) `seq` ()

instance Additive r => Additive (Complex r) where
  (a :+ b) + (c :+ d) = (a + c) :+ (b + d)
instance Abelian r => Abelian (Complex r) where
instance (Group r, Semiring r) => Semiring (Complex r) where
instance (Group r, Rig r) => Rig (Complex r) where
  fromNatural = (:+ zero) . fromNatural
instance (Group r, Commutative r) => Commutative (Complex r) where
instance Ring r => Ring (Complex r) where
  fromInteger = (:+ zero) . fromInteger'
instance Group r => Group (Complex r) where
  (a :+ b) - (c :+ d) = (a - c) :+ (b - d)
  negate (a :+ b) = negate a :+ negate b
  times n (a :+ b) = times n a :+ times n b
instance LeftModule a r => LeftModule a (Complex r) where
  r .* (a :+ b) = (r .* a) :+ (r .* b)
instance RightModule a r => RightModule a (Complex r) where
  (a :+ b) *. r = (a *. r) :+ (b *. r)
instance Monoidal r => Monoidal (Complex r) where
  zero = zero :+ zero
instance (Group r, Monoidal r, Unital r) => Unital (Complex r) where
  one = one :+ zero
instance Additive Double where
  (+) = (P.+)
instance (Group r, Multiplicative r) => Multiplicative (Complex r) where
  (a :+ b) * (c :+ d) = (a*c - b*d) :+ (a*d + b*c)
instance LeftModule Natural Double where
  n .* d = fromIntegral n P.* d
instance RightModule Natural Double where
  d *. n = d P.* fromIntegral n
instance Monoidal Double where
  zero = 0
instance Unital Double where
  one = 1
instance Multiplicative Double where
  (*) = (P.*)
instance Commutative Double where
instance Group Double where
  (-) = (P.-)
  negate = P.negate
  subtract = P.subtract
  times n r = P.fromIntegral n P.* r
instance LeftModule Integer Double where
  n .* r = P.fromInteger n * r
instance RightModule Integer Double where
  r *. n = r * P.fromInteger n
instance Rig Double where
  fromNatural = P.fromInteger . fromNatural
instance Semiring Double where
instance Abelian Double where
instance Ring Double where
  fromInteger = P.fromInteger
instance DecidableZero Double where
  isZero 0 = True
  isZero _ = False

instance Division Double where
  recip = P.recip
  (/)   = (P./)

instance P.Integral r => Additive (P.Ratio r) where
  (+) = (P.+)

instance P.Integral r => Abelian (P.Ratio r)

instance P.Integral r => LeftModule Natural (P.Ratio r) where
  n .* r = fromIntegral n P.* r

instance P.Integral r => RightModule Natural (P.Ratio r) where
  r *. n = r P.* fromIntegral n

instance P.Integral r => LeftModule Integer (P.Ratio r) where
  n .* r = P.fromInteger n P.* r

instance P.Integral r => RightModule Integer (P.Ratio r) where
  r *. n = r P.* P.fromInteger n

instance P.Integral r => Group (P.Ratio r) where
  (-)    = (P.-)
  negate = P.negate
  subtract = P.subtract
  times n r = P.fromIntegral n P.* r

instance P.Integral r => Commutative (P.Ratio r)

instance (Semiring r, P.Integral r) => LeftModule (Scalar r) (P.Ratio r) where
  Scalar n .* r = (n P.% 1) * r

instance (Semiring r, P.Integral r) => RightModule (Scalar r) (P.Ratio r) where
  r *. Scalar n = r * (n P.% 1)

instance P.Integral r => Multiplicative (P.Ratio r) where
  (*) = (P.*)

instance P.Integral r => Unital (P.Ratio r) where
  one = 1

instance P.Integral r => Division (P.Ratio r) where
  (/) = (P./)
  recip = P.recip

instance P.Integral r => Monoidal (P.Ratio r) where
  zero = 0

instance P.Integral r => Semiring (P.Ratio r)

instance P.Integral r => Rig (P.Ratio r) where
  fromNatural = P.fromIntegral

instance P.Integral r => Ring (P.Ratio r) where
  fromInteger = P.fromInteger

instance P.Integral r => DecidableZero (P.Ratio r) where
  isZero 0 = True
  isZero _ = False

instance P.Integral r => DecidableUnits (P.Ratio r) where
  isUnit 0 = False
  isUnit _ = True
  recipUnit 0 = Nothing
  recipUnit n = Just (P.recip n)
  r ^? n
    | r == 0 = Just 1
    | r /= 0 = Just (r P.^^ n)
    | r == 0 && n P.> 0 = Just 0
    | otherwise = Nothing

instance Convertible (Fraction Integer) Double where
  safeConvert a = Right $ P.fromInteger (numerator a) P./ P.fromInteger (denominator a)

instance Convertible (Fraction Integer) (Complex Double) where
  safeConvert a = Right $ P.fromInteger (numerator a) P./ P.fromInteger (denominator a) :+ 0

instance (Random (Fraction Integer)) where
  random = runRand $ do
    i <- getRandom
    j <- getRandom
    return $ i % (P.abs j + 1)
  randomR (a, b) = runRand $ do
    j <- succ . P.abs <$> getRandom
    let g = foldl1 P.lcm  [denominator a, denominator b, j]
        lb = g * numerator a `quot` denominator a
        ub = g * numerator b `quot` denominator b
    i <- getRandomR (lb, ub)
    return $ i % g

type instance Element (PV.Vector a) = a
instance PV.Prim a => MonoFoldable (PV.Vector a) where
  ofoldl' = PV.foldl'
  ofoldMap = \f -> PV.foldl' (\a b -> a <> f b) mempty
  ofoldr = PV.foldr'
  ofoldr1Ex = PV.foldr1'
  ofoldl1Ex' = PV.foldl1'
  olength = PV.length
  otoList = PV.toList
  oall = PV.all
  oany = PV.any
  onull = PV.null
  headEx = PV.head
  lastEx = PV.last
  oelem = PV.elem
  onotElem = PV.notElem

instance PV.Prim a => MonoFunctor (PV.Vector a) where
  omap = PV.map

instance PV.Prim a => MonoTraversable (PV.Vector a) where
  otraverse = \f -> fmap PV.fromList . traverse f . PV.toList

instance PV.Prim a => ListLike (PV.Vector a) a where
  singleton = PV.singleton
  null = PV.null
  genericLength = fromIntegral . PV.length
  head = PV.head
  tail = PV.tail
  cons = PV.cons
  empty = PV.empty
  snoc = PV.snoc
  append = (<>)
  last = PV.last
  init = PV.init
  length = PV.length
  rigidMap = PV.map
  reverse = PV.reverse
  concat = VB.build . LL.foldMap VB.vector
  rigidConcatMap = PV.concatMap
  any = PV.any
  all = PV.all
  maximum = PV.maximum
  minimum = PV.minimum

  replicate = PV.replicate
  take = PV.take
  drop = PV.drop
  splitAt = PV.splitAt
  takeWhile = PV.takeWhile
  dropWhile = PV.dropWhile
  span = PV.span
  elem = PV.elem
  notElem = PV.notElem
  find = PV.find
  filter = PV.filter
  partition = PV.partition
  index = DC.coerce $ PV.indexM @a @Identity
  elemIndex = PV.elemIndex
  elemIndices = fmap LL.fromListLike . PV.elemIndices
  findIndex = PV.findIndex
  findIndices = fmap LL.fromListLike . PV.findIndices
  rigidMapM = PV.mapM
  sort = PV.modify AI.sort
  sortBy f = PV.modify (AI.sortBy f)

instance PV.Prim a => LL.FoldableLL (PV.Vector a) a where
  foldl = PV.foldl
  foldl' = PV.foldl'
  foldl1 = PV.foldl1
  foldr = PV.foldr
  foldr' = PV.foldr'
  foldr1 = PV.foldr1

instance PV.Prim a => LL.ListLike (PA.PrimArray a) a where
  null = (== 0) . PA.sizeofPrimArray
  singleton = PA.replicatePrimArray 1
  genericLength = fromIntegral . PA.sizeofPrimArray
  head = (`PA.indexPrimArray` 0)
  tail = \xs -> runST $ do
    let !len = PA.sizeofPrimArray xs
    mxs <- PA.newPrimArray (len - 1)
    PA.copyPrimArray mxs 0 xs 0 (len - 1)
    PA.unsafeFreezePrimArray mxs
  cons = \x xs -> runST $ do
    let !len = PA.sizeofPrimArray xs
    mxxs <- PA.newPrimArray (1 + len)
    PA.writePrimArray mxxs 0 x
    PA.copyPrimArray
      mxxs 0 xs 1 len
    PA.unsafeFreezePrimArray mxxs
  empty = runST $ do
    PA.unsafeFreezePrimArray =<< PA.newPrimArray 0
  snoc = \ xs x -> runST $ do
    let !len = PA.sizeofPrimArray xs
    mxxs <- PA.newPrimArray (1 + len)
    PA.writePrimArray mxxs len x
    PA.copyPrimArray
      mxxs 0 xs 0 len
    PA.unsafeFreezePrimArray mxxs
  append = (<>)
  last = PA.indexPrimArray <$> id <*> pred . PA.sizeofPrimArray
  init = \xs -> runST $ do
    let !len = PA.sizeofPrimArray xs
    mxs <- PA.newPrimArray (len - 1)
    PA.copyPrimArray mxs 0 xs 0 (len - 1)
    PA.unsafeFreezePrimArray mxs
  length = PA.sizeofPrimArray
  rigidMap = PA.mapPrimArray

  replicate = PA.replicatePrimArray
  filter = PA.filterPrimArray
  index = PA.indexPrimArray
  rigidMapM = PA.traversePrimArray
  toList = PA.primArrayToList
  fromList = PA.primArrayFromList

instance PV.Prim a => LL.FoldableLL (PA.PrimArray a) a where
  foldl = PA.foldlPrimArray
  foldr = PA.foldrPrimArray
  foldl' = PA.foldlPrimArray'
  foldr' = PA.foldrPrimArray'

type instance Element (PA.PrimArray a) = a
instance PV.Prim a => MonoFoldable (PA.PrimArray a) where
  ofoldMap f = PA.foldrPrimArray' (mappend . f) mempty
  ofoldr = PA.foldrPrimArray'
  ofoldl' = PA.foldlPrimArray'
  ofoldl1Ex' = \f xs ->
    PA.foldlPrimArray' f (LL.head xs) (LL.tail xs)
  ofoldr1Ex = \f xs ->
    PA.foldrPrimArray' f (LL.last xs) (LL.init xs)
  otoList = PA.primArrayToList
  olength = PA.sizeofPrimArray
  onull = (== 0) . PA.sizeofPrimArray
  otraverse_ = PA.traversePrimArray_
  ofoldlM = PA.foldlPrimArrayM'
  headEx = (`PA.indexPrimArray` 0)
  lastEx = PA.indexPrimArray <$> id <*> pred . PA.sizeofPrimArray

instance PV.Prim a => MonoFunctor (PA.PrimArray a) where
  omap = PA.mapPrimArray

instance PV.Prim a => MonoTraversable (PA.PrimArray a) where
  otraverse = PA.traversePrimArray
  omapM = PA.traversePrimArray

{-# RULES
  "zipWithSame/PVector" [~1]
  forall (f :: (PV.Prim a, PV.Prim b, PV.Prim c) => a -> b -> c).
  SV.zipWithSame f = (unsafeCoerce .) . (. SV.unsized) . PV.zipWith f . SV.unsized
  #-}
