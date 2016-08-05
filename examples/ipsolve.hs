{-# LANGUAGE BangPatterns, CPP, DataKinds, ExistentialQuantification    #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs, KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude, RankNTypes       #-}
{-# LANGUAGE ScopedTypeVariables, TemplateHaskell, TypeOperators        #-}
{-# LANGUAGE UndecidableInstances                                       #-}
module Main where
import           Algebra.Algorithms.Groebner
import           Algebra.Instances            ()
import           Algebra.Prelude
import           Control.Applicative          ((<$>))
import           Control.Lens                 (ix, makeLenses, view, (&), (.~))
import           Data.Foldable
import           Data.Monoid
import           Data.Ord
import           Data.Reflection
import           Data.Singletons.Prelude      (SList)
import           Data.Singletons.Prelude.List
import qualified Data.Sized.Builtin           as V
import qualified Data.Traversable             as T
import qualified Prelude                      as P
import           Proof.Propositional          (IsTrue (..))

newtype IsOrder_ n = IsOrder_ { cmp :: Monomial n -> Monomial n -> Ordering }
data ReifiedOrder a = ReifiedOrder

retrieveOrder :: Proxy (ReifiedOrder a) -> Proxy a
retrieveOrder Proxy = Proxy

instance Reifies a (IsOrder_ n) => IsOrder n (ReifiedOrder a) where
  cmpMonomial pxy = cmp $ reflect (retrieveOrder pxy)

instance Reifies a (IsOrder_ n) => IsMonomialOrder n (ReifiedOrder a)

type IPOrder n vs = ProductOrder n (1 + Length vs)
                      Grevlex
                      (ProductOrder 1 (Length vs) Grevlex (WeightOrder vs Grevlex))
ipOrder :: SNat n -> SList vs -> IPOrder n vs
ipOrder n vs =
  ProductOrder n (sOne %:+ sLength vs)
    Grevlex
    (ProductOrder sOne (sLength vs) Grevlex (WeightOrder vs Proxy))

toMonomial :: forall k n ord .
              (KnownNat n, IsMonomialOrder (n + 1 + k) ord)
           => Sing k -> Vector Int n -> OrderedPolynomial (Fraction Integer) ord (S n :+ k)
toMonomial k ds =
  withKnownNat k $
  withKnownNat (sSucc (sing :: SNat n) %:+ k) $
  let !c = foldl' (\a b -> if b < 0 then a + P.abs b else a) 0 ds
  in toPolynomial (1, OrderedMonomial $
     -- coerce (symmetry $ sAndPlusOne (V.sLength ds)) $
     V.map (+c) ds `V.append` V.singleton c `V.append` V.replicate' 0)

calcCost :: Vector Int n -> Vector Int m -> Int
calcCost ns ms = P.sum $ V.zipWith (*) ns ms

costCmp :: Sing m -> Vector Int n -> Monomial m -> Monomial m -> Ordering
costCmp _ cost ns ms =
  comparing (calcCost cost) ns ms <> grevlex ns ms

toReifiedOrder :: Proxy m -> ReifiedOrder m
toReifiedOrder Proxy = ReifiedOrder

-- | Solve integer programming problem with general signature.
solveIP' :: forall n m . (KnownNat n, KnownNat m)
         => Vector Int n            -- ^ cost vector
         -> Vector (Vector Int n) m -- ^ constraint matrix
         -> Vector Int m            -- ^ constraint
         -> Maybe (Vector Int n)    -- ^ answer
solveIP' c mat b =
  let n    = sing :: SNat n
      m    = sing :: SNat m
      vlen = sSucc m %:+ n
  in withKnownNat (sSucc m) $
     reify (IsOrder_ $ costCmp n c) $ \pxy ->
     withWitness (plusLeqL (sSucc m) n) $
          withKnownNat vlen $
            let ord  = ProductOrder (sSucc m) n Grevlex (toReifiedOrder pxy)
                !b' = toMonomial n b
                as  = map  (toMonomial n) $
                      V.toList $ T.sequenceA mat
                (xsw, ys)  = splitAt (sNatToInt m+1) (vars' ord vlen)
                gs  = calcGroebnerBasis $ toIdeal $ P.product xsw - one : zipWith (-) ys as
                ans = b' `modPolynomial` gs
                (cond, solution) = V.splitAt (sSucc m) $ getMonomial $ leadingMonomial ans
            in if all (== 0) cond
               then Just $ coerceLength (plusMinus' (sSucc m) n) solution
               else Nothing

vars' :: IsPolynomial poly => (MOrder poly) -> SNat (Arity poly) -> [poly]
vars' _ _ = vars

data Cnstr n = (:<=) { _lhs :: Vector Int n, _rhs :: Int }
             | (:>=) { _lhs :: Vector Int n, _rhs :: Int }
             | (:==) { _lhs :: Vector Int n, _rhs :: Int }
             deriving (Show, Eq, Ord)

infix 4 :<=, :>=, :==

data IPProblem n m = IPProblem { objectCnstr :: Vector Int n
                               , cnstrs      :: Vector (Cnstr n) m
                               } deriving (Show, Eq)
makeLenses ''Cnstr

solveCnstrs :: forall n m. (KnownNat m, KnownNat n) => IPProblem n m -> Maybe (Vector Int n)
solveCnstrs ipp =
  let sn = sing :: SNat n
      sm = sing :: SNat m
      (obj, mat, vec) = extractProblem $ nfProblem ipp
  in withWitness (plusLeqL sn sm) $
     withKnownNat (sn %:+ sm) $
     V.take (sing :: SNat n) <$> solveIP' obj mat vec

extractProblem :: IPProblem n m -> (Vector Int n, Vector (Vector Int n) m, Vector Int m)
extractProblem (IPProblem obj css) = (obj, V.map (view lhs) css, V.map (view rhs) css)

nfProblem :: forall n m . KnownNat m => IPProblem n m -> IPProblem (n :+ m) m
nfProblem (IPProblem obj css) =
  IPProblem (obj `V.append` V.replicate (sing :: SNat m) 0)
            (nfCnstrs css)

ordVec :: SNat n -> Vector (V.Ordinal n) n
ordVec n = generate n id

nfCnstrs :: forall n m. (KnownNat m)
         => Vector (Cnstr n) m -> Vector (Cnstr (n :+ m)) m
nfCnstrs css = V.zipWithSame conv css (ordVec (sing :: SNat m))
  where
    conv (lh :<= r) nth = (lh `V.append` (V.replicate (sing :: SNat m) 0 & ix nth .~  1)) :== r
    conv (lh :>= r) nth = (lh `V.append` (V.replicate (sing :: SNat m) 0 & ix nth .~ -1)) :== r
    conv (lh :== r) _   = (lh `V.append`  V.replicate (sing :: SNat m) 0) :== r

testC :: Vector Int 4
testM :: Vector (Vector Int 4) 2
testB :: Vector Int 2
(testC, testM, testB) =
  (1000 :< 1 :< 1 :< 100 :< NilL,
   (3 :< -2 :< 1 :< -1 :< NilL) :< (4 :< 1 :< -1 :< 0 :< NilL) :< NilL,
   -1 :< 5 :< NilL)

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
main = act

act :: IO ()
act = print $ solveIP' testC testM testB
