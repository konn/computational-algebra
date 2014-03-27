{-# LANGUAGE BangPatterns, DataKinds, FlexibleContexts, GADTs, KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude, RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables, TypeOperators, UndecidableInstances         #-}
module Main where
import           Algebra.Algorithms.Groebner
import           Algebra.Prelude
import           Algebra.Ring.Noetherian
import           Control.Parallel.Strategies
import           Data.Constraint
import           Data.Monoid
import           Data.Ord
import           Data.Reflection
import           Data.Type.Natural           hiding (one)
import           Data.Vector.Sized           (Vector (..))
import qualified Data.Vector.Sized           as V
import qualified Prelude                     as P
import           Proof.Equational

newtype IsOrder_ = IsOrder_ { cmp :: forall n. Monomial n -> Monomial n -> Ordering }
data MOrder a = MOrder

retrieveOrder :: Proxy (MOrder a) -> Proxy a
retrieveOrder Proxy = Proxy

instance Reifies a IsOrder_ => IsOrder (MOrder a) where
  cmpMonomial pxy = cmp $ reflect (retrieveOrder pxy)

instance Reifies a IsOrder_ => IsMonomialOrder (MOrder a)

type IPOrder n vs = ProductOrder n Grevlex (ProductOrder One Grevlex (WeightOrder vs Grevlex))
ipOrder :: SNat n -> SList vs -> IPOrder n vs
ipOrder n vs = ProductOrder n Grevlex (ProductOrder sOne Grevlex (WeightOrder vs Grevlex))

toMonomial :: forall n ord . (SingI n, IsMonomialOrder ord)
           => ord -> Vector Int n -> OrderedPolynomial Rational ord (S n)
toMonomial _ ds =
  let !c = V.foldl' (\a b -> if b < 0 then a + P.abs b else a) 0 ds
  in toPolynomial (1, OrderedMonomial $
     coerce (symmetry $ sAndPlusOne (V.sLength ds)) $
     V.map (+c) ds `V.append` V.singleton c)

calcCost :: Vector Int n -> Vector Int m -> Int
calcCost ns ms = V.sum $ V.zipWith (*) ns ms

costCmp :: Vector Int n -> Monomial m -> Monomial m -> Ordering
costCmp cost ns ms =
  comparing (calcCost cost) ns ms <> grevlex ns ms

toMOrder :: Proxy m -> MOrder m
toMOrder Proxy = MOrder

solveIP' :: forall n m . (SingI n, SingI m)
         => Vector Int n            -- ^ cost vector
         -> Vector (Vector Int n) m -- ^ constraint matrix
         -> Vector Int m            -- ^ constraint
         -> Maybe (Vector Int n)    -- ^ answer
solveIP' c mat b =
  reify (IsOrder_ $ costCmp c) $ \pxy ->
  let n    = sing :: SNat n
      m    = sing :: SNat m
      ord  = ProductOrder (sS m) Grevlex (toMOrder pxy)
      vlen = sS m %+ n
      pf1  = plusLeqL m n
      pf2 = leqSucc (m %+ n)
  in case (propToClassLeq pf1, propToBoolLeq pf1, propToBoolLeq (pf1 `leqTrans` pf2)) of
    (Dict, Dict, Dict) ->
      case singInstance vlen of
        SingInstance ->
          let !b' = scastPolynomial vlen (toMonomial ord b) `orderedBy` ord
              as  = map (scastPolynomial vlen . toMonomial ord) $ V.toList $ V.transpose mat
              (xsw, ys)  = splitAt (sNatToInt m+1) $ genVars vlen
              gs  = calcGroebnerBasis $ toIdeal $ product xsw - one : zipWith (-) ys as
              ans = b' `modPolynomial` gs
              (cond, solution) = V.splitAt (sS m) $ getMonomial $ leadingMonomial ans
          in if V.all (== 0) cond
             then Just $ coerce (plusMinusEqR n m) $ solution
             else Nothing

testC :: Vector Int Four
testM :: Vector (Vector Int Four) Two
testB :: Vector Int Two
(testC, testM, testB) =
  (1000 :- 1 :- 1 :- 100 :- Nil,
   (3 :- -2 :- 1 :- -1 :- Nil) :- (4 :- 1 :- -1 :- 0 :- Nil) :- Nil,
   -1 :- 5 :- Nil)

main :: IO ()
main = print $ solveIP' testC testM testB
