{-# LANGUAGE BangPatterns, CPP, DataKinds, ExistentialQuantification        #-}
{-# LANGUAGE FlexibleContexts, GADTs, KindSignatures, MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude, RankNTypes, ScopedTypeVariables             #-}
{-# LANGUAGE TemplateHaskell, TypeOperators, UndecidableInstances           #-}
module Main where
import           Algebra.Algorithms.Groebner
import           Algebra.Instances           ()
import           Algebra.Prelude
import           Control.Applicative         ((<$>))
import           Control.Lens                (ix, makeLenses, view, (&), (.~))
import           Data.Constraint
import           Data.Monoid
import           Data.Ord
import           Data.Reflection
import           Data.Type.Natural           hiding (one)
import           Data.Vector.Sized           (Vector (..))
import qualified Data.Vector.Sized           as V
import qualified Prelude                     as P
import           Proof.Equational
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
import Data.Singletons.Prelude (SList)
#endif

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
           => ord -> Vector Int n -> OrderedPolynomial (Fraction Integer) ord (S n)
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

-- | Solve integer programming problem with general signature.
solveIP' :: forall n m . (SingI n, SingI m)
         => Vector Int n            -- ^ cost vector
         -> Vector (Vector Int n) m -- ^ constraint matrix
         -> Vector Int m            -- ^ constraint
         -> Maybe (Vector Int n)    -- ^ answer
solveIP' c mat b =
  reify (IsOrder_ $ costCmp c) $ \pxy ->
  let n    = sing :: SNat n
      m    = sing :: SNat m
      ord  = ProductOrder (SS m) Grevlex (toMOrder pxy)
      vlen = SS m %+ n
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
              (cond, solution) = V.splitAt (SS m) $ getMonomial $ leadingMonomial ans
          in if V.all (== 0) cond
             then Just $ coerce (plusMinusEqR n m) solution
             else Nothing

data Cnstr n = (:<=) { _lhs :: Vector Int n, _rhs :: Int }
             | (:>=) { _lhs :: Vector Int n, _rhs :: Int }
             | (:==) { _lhs :: Vector Int n, _rhs :: Int }
             deriving (Show, Eq, Ord)

infix 4 :<=, :>=, :==

data IPProblem n m = IPProblem { objectCnstr :: Vector Int n
                               , cnstrs      :: Vector (Cnstr n) m
                               } deriving (Show, Eq)
makeLenses ''Cnstr

solveCnstrs :: forall n m. (SingI m, SingI n) => IPProblem n m -> Maybe (Vector Int n)
solveCnstrs ipp =
  let sn = sing :: SNat n
      sm = sing :: SNat m
      (obj, mat, vec) = extractProblem $ nfProblem ipp
  in case propToBoolLeq (plusLeqL sn sm) of
    Dict -> case singInstance (sn %:+ sm) of
      SingInstance -> V.take (sing :: SNat n) <$> solveIP' obj mat vec

extractProblem :: IPProblem n m -> (Vector Int n, Vector (Vector Int n) m, Vector Int m)
extractProblem (IPProblem obj css) = (obj, V.map (view lhs) css, V.map (view rhs) css)

nfProblem :: forall n m . SingI m => IPProblem n m -> IPProblem (n :+ m) m
nfProblem (IPProblem obj css) =
  IPProblem (obj `V.append` V.replicate (sing :: SNat m) 0)
            (nfCnstrs css)

enumOrd' :: SNat n -> V.Vector (V.Ordinal n) n
enumOrd' SZ = Nil
enumOrd' (SS n) = V.OZ :- V.map V.OS (enumOrd' n)

nfCnstrs :: forall n m. (SingI m)
         => Vector (Cnstr n) m -> Vector (Cnstr (n :+ m)) m
nfCnstrs css = V.zipWithSame conv css (enumOrd' (sing :: SNat m))
  where
    conv (lh :<= r) nth = (lh `V.append` (V.replicate (sing :: SNat m) 0 & ix nth .~  1)) :== r
    conv (lh :>= r) nth = (lh `V.append` (V.replicate (sing :: SNat m) 0 & ix nth .~ -1)) :== r
    conv (lh :== r) _   = (lh `V.append`  V.replicate (sing :: SNat m) 0) :== r

testC :: Vector Int Four
testM :: Vector (Vector Int Four) Two
testB :: Vector Int Two
(testC, testM, testB) =
  (1000 :- 1 :- 1 :- 100 :- Nil,
   (3 :- -2 :- 1 :- -1 :- Nil) :- (4 :- 1 :- -1 :- 0 :- Nil) :- Nil,
   -1 :- 5 :- Nil)

data Rect = Rect { _height :: Int, _width :: Int
                 } deriving (Read, Show, Eq, Ord)
makeLenses ''Rect

data Design = Design { _frame    :: Rect
                     , _pictures :: [Rect]
                     } deriving (Read, Show, Eq, Ord)
makeLenses ''Design

data Department = Department { _area    :: Int
                             , _aspect  :: Int
                             , _maxSide :: Int
                             , _minSide :: Int
                             } deriving (Read, Show, Eq, Ord)

data SomeIPProblem = forall n m. SomeIPProblem (IPProblem n m)

designConstraint :: Design -> SomeIPProblem
designConstraint = undefined

main :: IO ()
main = print $ solveIP' testC testM testB
