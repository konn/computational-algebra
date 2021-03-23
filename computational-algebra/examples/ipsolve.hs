{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Main where

import Algebra.Algorithms.Groebner
import Algebra.Instances ()
import Algebra.Prelude
import Control.Applicative ((<$>))
import Control.Lens (ix, makeLenses, view, (&), (.~))
import Data.Reflection
import Data.Singletons.Prelude (SList)
import Data.Singletons.Prelude.List
import qualified Data.Sized as V

newtype IsOrder_ n = IsOrder_ {cmp :: Monomial n -> Monomial n -> Ordering}

data ReifiedOrder a = ReifiedOrder

retrieveOrder :: Proxy (ReifiedOrder a) -> Proxy a
retrieveOrder Proxy = Proxy

instance Reifies a (IsOrder_ n) => IsOrder n (ReifiedOrder a) where
  cmpMonomial pxy = cmp $ reflect (retrieveOrder pxy)

instance Reifies a (IsOrder_ n) => IsMonomialOrder n (ReifiedOrder a)

type IPOrder n vs =
  ProductOrder
    n
    (1 + Length vs)
    Grevlex
    (ProductOrder 1 (Length vs) Grevlex (WeightOrder vs Grevlex))

ipOrder :: SNat n -> SList vs -> IPOrder n vs
ipOrder n vs =
  ProductOrder
    n
    (sOne %:+ sLength vs)
    Grevlex
    (ProductOrder sOne (sLength vs) Grevlex (WeightOrder vs Proxy))

toMonomial ::
  forall k n ord.
  (KnownNat n, IsMonomialOrder (n + 1 + k) ord) =>
  SNat k ->
  Monomial n ->
  OrderedPolynomial (Fraction Integer) ord (S n :+ k)
toMonomial k ds =
  withKnownNat k $
    withKnownNat (sSucc (sNat :: SNat n) %:+ k) $
      let !c = foldl' (\a b -> if b < 0 then a + abs b else a) 0 ds
       in toPolynomial'
            ( 1
            , -- coerce (symmetry $ sAndPlusOne (V.sLength ds)) $
              V.map (+ c) ds `V.append` V.singleton c `V.append` V.replicate' 0
            )

calcCost :: Sized' n Int -> Sized' m Int -> Int
calcCost ns ms = sum $ V.zipWith (*) ns ms

costCmp :: SNat m -> Sized' n Int -> Monomial m -> Monomial m -> Ordering
costCmp _ cost ns ms =
  comparing (calcCost cost) ns ms <> grevlex ns ms

toReifiedOrder :: Proxy m -> ReifiedOrder m
toReifiedOrder Proxy = ReifiedOrder

-- | Solve integer programming problem with general signature.
solveIP' ::
  forall n m.
  (KnownNat n, KnownNat m) =>
  -- | cost vector
  Sized' n Int ->
  -- | constraint matrix
  Sized' m (Sized' n Int) ->
  -- | constraint
  Sized' m Int ->
  -- | answer
  Maybe (Sized' n Int)
solveIP' c mat b =
  let n = sNat :: SNat n
      m = sNat :: SNat m
      vlen = sSucc m %:+ n
   in withKnownNat (sSucc m) $
        reify (IsOrder_ $ costCmp n c) $ \pxy ->
          withWitness (plusLeqL (sSucc m) n) $
            withKnownNat vlen $
              let ord = ProductOrder (sSucc m) n Grevlex (toReifiedOrder pxy)
                  !b' = toMonomial n b
                  as =
                    map (toMonomial n) $
                      V.toList $ sequenceA mat
                  (xsw, ys) = splitAt (sNatToInt m + 1) (vars' ord vlen)
                  gs = calcGroebnerBasis $ toIdeal $ product xsw - one : zipWith (-) ys as
                  ans = b' `modPolynomial` gs
                  (cond, solution) = V.splitAt (sSucc m) $ getMonomial $ leadingMonomial ans
               in if all (== 0) cond
                    then Just $ coerceLength (plusMinus' (sSucc m) n) solution
                    else Nothing

vars' :: IsPolynomial poly => (MOrder poly) -> SNat (Arity poly) -> [poly]
vars' _ _ = vars

data Cnstr n
  = (:<=) {_lhs :: Sized' n Int, _rhs :: Int}
  | (:>=) {_lhs :: Sized' n Int, _rhs :: Int}
  | (:==) {_lhs :: Sized' n Int, _rhs :: Int}
  deriving (Show, Eq, Ord)

infix 4 :<=, :>=, :==

data IPProblem n m = IPProblem
  { objectCnstr :: Sized' n Int
  , cnstrs :: Sized' m (Cnstr n)
  }
  deriving (Show, Eq)

makeLenses ''Cnstr

solveCnstrs :: forall n m. (KnownNat m, KnownNat n) => IPProblem n m -> Maybe (Sized' n Int)
solveCnstrs ipp =
  let sn = sNat :: SNat n
      sm = sNat :: SNat m
      (obj, mat, vec) = extractProblem $ nfProblem ipp
   in withWitness (plusLeqL sn sm) $
        withKnownNat (sn %:+ sm) $
          V.take (sNat :: SNat n) <$> solveIP' obj mat vec

extractProblem :: IPProblem n m -> (Sized' n Int, Sized' m (Sized' n Int), Sized' m Int)
extractProblem (IPProblem obj css) = (obj, V.map (view lhs) css, V.map (view rhs) css)

nfProblem :: forall n m. KnownNat m => IPProblem n m -> IPProblem (n :+ m) m
nfProblem (IPProblem obj css) =
  IPProblem
    (obj `V.append` V.replicate (sNat :: SNat m) 0)
    (nfCnstrs css)

ordVec :: SNat n -> Sized' n (V.Ordinal n)
ordVec n = generate n id

nfCnstrs ::
  forall n m.
  (KnownNat m) =>
  Sized' m (Cnstr n) ->
  Sized' m (Cnstr (n :+ m))
nfCnstrs css = V.zipWithSame conv css (ordVec (sNat :: SNat m))
  where
    conv (lh :<= r) nth = (lh `V.append` (V.replicate (sNat :: SNat m) 0 & ix nth .~ 1)) :== r
    conv (lh :>= r) nth = (lh `V.append` (V.replicate (sNat :: SNat m) 0 & ix nth .~ -1)) :== r
    conv (lh :== r) _ = (lh `V.append` V.replicate (sNat :: SNat m) 0) :== r

testC :: Sized' 4 Int
testM :: Sized' 2 (Sized' 4 Int)
testB :: Sized' 2 Int
(testC, testM, testB) =
  ( 1000 :< 1 :< 1 :< 100 :< Nil
  , (3 :< -2 :< 1 :< -1 :< Nil) :< (4 :< 1 :< -1 :< 0 :< Nil) :< Nil
  , -1 :< 5 :< Nil
  )

data Rect = Rect
  { _height :: Int
  , _width :: Int
  }
  deriving (Read, Show, Eq, Ord)

makeLenses ''Rect

data Design = Design
  { _frame :: Rect
  , _pictures :: [Rect]
  }
  deriving (Read, Show, Eq, Ord)

makeLenses ''Design

data Department = Department
  { _area :: Int
  , _aspect :: Int
  , _maxSide :: Int
  , _minSide :: Int
  }
  deriving (Read, Show, Eq, Ord)

data SomeIPProblem = forall n m. SomeIPProblem (IPProblem n m)

designConstraint :: Design -> SomeIPProblem
designConstraint = undefined

main :: IO ()
main = act

act :: IO ()
act = print $ solveIP' testC testM testB
