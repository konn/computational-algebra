{-# LANGUAGE ConstraintKinds, DataKinds, ExistentialQuantification        #-}
{-# LANGUAGE ExplicitNamespaces, FlexibleContexts, FlexibleInstances      #-}
{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, IncoherentInstances       #-}
{-# LANGUAGE LiberalTypeSynonyms, MultiParamTypeClasses, ParallelListComp #-}
{-# LANGUAGE PatternSynonyms, PolyKinds, RankNTypes, ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving, TemplateHaskell, TypeApplications        #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances            #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Algebra.Ring.Polynomial.Monomial
       ( Monomial, OrderedMonomial(..),
         IsOrder(..), IsMonomialOrder, MonomialOrder,
         IsStrongMonomialOrder,
         isRelativelyPrime, totalDegree, ProductOrder(..),
         productOrder, productOrder', WeightProxy, WeightOrder(..),
         gcdMonomial, divs, isPowerOf, tryDiv, lcmMonomial,
         Lex(..), EliminationType, EliminationOrder,
         WeightedEliminationOrder, eliminationOrder, weightedEliminationOrder,
         lex, revlex, graded, grlex, grevlex,
         weightOrder, Grevlex(..), fromList,
         Revlex(..), Grlex(..), Graded(..),
         castMonomial, scastMonomial, varMonom,
         changeMonomialOrder, changeMonomialOrderProxy, sOnes,
         withStrongMonomialOrder, cmpAnyMonomial, orderMonomial
       ) where
import Algebra.Internal

import           AlgebraicPrelude                hiding (lex)
import           Control.DeepSeq                 (NFData (..))
import           Control.Lens                    (Ixed (..), alaf, imap,
                                                  makeLenses, makeWrapped, (%~),
                                                  (&), (.~), _Wrapped)
import           Data.Constraint                 ((:=>) (..), Dict (..))
import qualified Data.Constraint                 as C
import           Data.Constraint.Forall
import           Data.Hashable                   (Hashable (..))
import           Data.Kind                       (Type)
import           Data.Kind                       (Type)
import           Data.Maybe                      (catMaybes)
import           Data.Monoid                     (Dual (..))
import           Data.Monoid                     ((<>))
import qualified Data.MonoTraversable.Unprefixed as MT
import           Data.Ord                        (comparing)
import           Data.Singletons.Prelude         (POrd (..), SList, Sing ())
import           Data.Singletons.Prelude         (SingKind (..))
import           Data.Singletons.Prelude.List    (Length, Replicate, sReplicate)
import           Data.Singletons.TypeLits        (withKnownNat)
import qualified Data.Sized.Builtin              as V
import           Data.Type.Natural.Class         (IsPeano (..), PeanoOrder (..))
import           Data.Type.Ordinal               (Ordinal (..), ordToInt)
-- import           Prelude                         hiding (Fractional (..),
--                                                   Integral (..), Num (..),
--                                                   Real (..), lex, product, sum)
import qualified Prelude as P

-- | N-ary Monomial. IntMap contains degrees for each x_i- type Monomial (n :: Nat) = Sized n Int
type Monomial n = Sized n Int

-- | A wrapper for monomials with a certain (monomial) order.
newtype OrderedMonomial ordering n =
  OrderedMonomial { getMonomial :: Monomial n }
  deriving (NFData)

makeLenses ''OrderedMonomial
makeWrapped ''OrderedMonomial

-- | convert NAry list into Monomial.
fromList :: SNat n -> [Int] -> Monomial n
fromList len = V.fromListWithDefault len 0

-- | Monomial order (of degree n). This should satisfy following laws:
-- (1) Totality: forall a, b (a < b || a == b || b < a)
-- (2) Additivity: a <= b ==> a + c <= b + c
-- (3) Non-negative: forall a, 0 <= a
type MonomialOrder n = Monomial n -> Monomial n -> Ordering

isRelativelyPrime :: OrderedMonomial ord n -> OrderedMonomial ord n -> Bool
isRelativelyPrime n m = lcmMonomial n m == n * m

totalDegree :: OrderedMonomial ord n -> Int
totalDegree = P.sum . getMonomial
{-# INLINE totalDegree #-}

-- | Lexicographical order. This *is* a monomial order.
lex :: MonomialOrder n
lex m n = P.foldMap (uncurry compare) $ V.zipSame m n

-- | Reversed lexicographical order. This is *not* a monomial order.
revlex :: MonomialOrder n
revlex xs ys = alaf Dual foldMap (uncurry (flip compare)) $ V.zipSame xs ys

-- | Convert ordering into graded one.
graded :: MonomialOrder n -> MonomialOrder n
graded cmp xs ys = comparing MT.sum xs ys <> cmp xs ys
{-# INLINE[1] graded #-}
{-# RULES
"graded/graded"  [~1] forall x. graded (graded x) = graded x
  #-}

-- | Graded lexicographical order. This *is* a monomial order.
grlex :: MonomialOrder n
grlex = graded lex
{-# INLINE [2] grlex #-}

-- | Graded reversed lexicographical order. This *is* a monomial order.
grevlex :: MonomialOrder n
grevlex = graded revlex
{-# INLINE [2] grevlex #-}

deriving instance Hashable (Monomial n) => Hashable (OrderedMonomial ordering n)
deriving instance (Eq (Monomial n)) => Eq (OrderedMonomial ordering n)
instance KnownNat n => Show (OrderedMonomial ord n) where
  show xs =
    let vs = catMaybes $ V.toList $
            imap (\n i ->
                   if i > 0
                   then Just ("X_" ++ show (ordToInt n) ++ if i == 1 then "" else "^" ++ show i)
                   else Nothing)
            $ getMonomial xs
    in if null vs then "1" else unwords vs

instance Multiplicative (OrderedMonomial ord n) where
  OrderedMonomial n * OrderedMonomial m = OrderedMonomial $ V.zipWithSame (+) n m

instance KnownNat n => Division (OrderedMonomial ord n) where
  recip = _Wrapped %~ V.map P.negate
  OrderedMonomial n / OrderedMonomial m = OrderedMonomial $ V.zipWithSame (-) n m

instance KnownNat n => Unital (OrderedMonomial ord n) where
  one = OrderedMonomial $ fromList sing []

-- | Class to lookup ordering from its (type-level) name.
class IsOrder (n :: Nat) (ordering :: *) where
  cmpMonomial :: Proxy ordering -> MonomialOrder n

head' :: (0 :< n) ~ 'True => Sized n a -> a
head' = V.head
{-# INLINE head' #-}

-- We know that Monomial ordering coincides on lex ordering
-- on univariate monomials.
{-# RULES
"cmpMonomial/unary" [~1]
              forall (pxy :: IsMonomialOrder 1 (o :: *) => Proxy o)
                     (xs :: Sized 1 Int)
                     (ys :: Sized 1 Int).
  cmpMonomial pxy xs ys = comparing head' xs ys
 #-}

-- * Names for orderings.
--   We didn't choose to define one single type for ordering names for the extensibility.
-- | Lexicographical order
data Lex = Lex
           deriving (Show, Eq, Ord)

-- | Reversed lexicographical order
data Revlex = Revlex
              deriving (Show, Eq, Ord)

-- | Graded reversed lexicographical order. Same as @Graded Revlex@.
data Grevlex = Grevlex
               deriving (Show, Eq, Ord)

-- | Graded lexicographical order. Same as @Graded Lex@.
data Grlex = Grlex
             deriving (Show, Eq, Ord)

-- | Graded order from another monomial order.
data Graded ord = Graded ord
                  deriving (Read, Show, Eq, Ord)

instance IsOrder n ord => IsOrder n (Graded ord) where
  cmpMonomial Proxy = graded (cmpMonomial (Proxy :: Proxy ord))
  {-# INLINE [1] cmpMonomial #-}

instance IsMonomialOrder n ord => IsMonomialOrder n (Graded ord)

data ProductOrder (n :: Nat) (m :: Nat) (a :: *) (b :: *) where
  ProductOrder :: Sing n -> Sing m -> ord -> ord' -> ProductOrder n m ord ord'

productOrder :: forall ord ord' n m. (IsOrder n ord, IsOrder m ord', KnownNat n, KnownNat m)
             => Proxy (ProductOrder n m ord ord') -> MonomialOrder (n + m)
productOrder _ mon mon' =
  let n = sing :: SNat n
      m = sing :: SNat m
  in withWitness (plusLeqL n m) $
     case (V.splitAt n mon, V.splitAt n mon') of
      ((xs, xs'), (ys, ys')) ->
        cmpMonomial (Proxy :: Proxy ord) xs ys <>
        cmpMonomial (Proxy :: Proxy ord')
          (coerceLength (plusMinus' n m) xs')
          (coerceLength (plusMinus' n m) ys')

productOrder' :: forall n ord ord' m.(IsOrder n ord, IsOrder m ord')
              => SNat n -> SNat m -> ord -> ord' -> MonomialOrder (n + m)
productOrder' n m _ _ =
  withKnownNat n $ withKnownNat m $
  productOrder (Proxy :: Proxy (ProductOrder n m ord ord'))

type WeightProxy (v :: [Nat]) = SList v

data WeightOrder (v :: [Nat]) (ord :: Type) where
  WeightOrder :: SList (v :: [Nat]) -> Proxy ord -> WeightOrder v ord

calcOrderWeight :: forall vs n. (SingI vs, KnownNat n)
                 => Proxy (vs :: [Nat]) -> Monomial n -> Int
calcOrderWeight Proxy = calcOrderWeight' (sing :: SList vs)
{-# INLINE calcOrderWeight #-}

calcOrderWeight' :: forall vs n. KnownNat n => SList (vs :: [Nat]) -> Monomial n -> Int
calcOrderWeight' slst m =
  let cfs = V.fromListWithDefault' (0 :: Int) $ map P.fromIntegral $ fromSing slst
  in P.sum $ V.zipWithSame (*) cfs m
{-# INLINE calcOrderWeight' #-}

weightOrder :: forall n ns ord. (KnownNat n, IsOrder n ord, SingI ns)
            => Proxy (WeightOrder ns ord) -> MonomialOrder n
weightOrder Proxy m m' =
     comparing (calcOrderWeight (Proxy :: Proxy ns)) m m'
  <> cmpMonomial (Proxy :: Proxy ord) m m'
{-# INLINE weightOrder #-}

instance (KnownNat n, IsOrder n ord, SingI ws)
       => IsOrder n (WeightOrder ws ord) where
  cmpMonomial p = weightOrder p
  {-# INLINE [1] cmpMonomial #-}

instance (IsOrder n ord, IsOrder m ord', KnownNat m, KnownNat n, k ~ (n + m))
      => IsOrder k (ProductOrder n m ord ord') where
  cmpMonomial p = productOrder p
  {-# INLINE [1] cmpMonomial #-}

-- They're all total orderings.
instance IsOrder n Grevlex where
  cmpMonomial _ = grevlex
  {-# INLINE [1] cmpMonomial #-}

instance IsOrder n Revlex where
  cmpMonomial _ = revlex
  {-# INLINE [1] cmpMonomial #-}

instance IsOrder n Lex where
  cmpMonomial _ = lex
  {-# INLINE [1] cmpMonomial #-}

instance IsOrder n Grlex where
  cmpMonomial _ = grlex
  {-# INLINE [1] cmpMonomial #-}

-- | Class for Monomial orders.
class IsOrder n name => IsMonomialOrder n name where

-- Note that Revlex is not a monomial order.
-- This distinction is important when we calculate a quotient or Groebner basis.
instance IsMonomialOrder n Grlex
instance IsMonomialOrder n Grevlex
instance IsMonomialOrder n Lex
instance (KnownNat n, KnownNat m, IsMonomialOrder n o, IsMonomialOrder m o', k ~ (n + m))
      => IsMonomialOrder k (ProductOrder n m o o')
instance (KnownNat k, SingI ws, IsMonomialOrder k ord)
      => IsMonomialOrder k (WeightOrder ws ord)

lcmMonomial :: OrderedMonomial ord n -> OrderedMonomial ord n -> OrderedMonomial ord n
lcmMonomial (OrderedMonomial m) (OrderedMonomial n) = OrderedMonomial $ V.zipWithSame max m n

gcdMonomial :: OrderedMonomial ord n -> OrderedMonomial ord n -> OrderedMonomial ord n
gcdMonomial (OrderedMonomial m) (OrderedMonomial n) = OrderedMonomial $ V.zipWithSame P.min m n


divs :: OrderedMonomial ord n -> OrderedMonomial ord n -> Bool
(OrderedMonomial xs) `divs` (OrderedMonomial ys) = and $ V.toList $ V.zipWith (<=) xs ys

isPowerOf :: KnownNat n => OrderedMonomial ord n -> OrderedMonomial ord n -> Bool
OrderedMonomial n `isPowerOf` OrderedMonomial m =
  case V.sFindIndices (> 0) m of
    [ind] -> MT.sum n == V.sIndex ind n
    _     -> False

tryDiv :: Field r => (r, OrderedMonomial ord n) -> (r, OrderedMonomial ord n) -> (r, OrderedMonomial ord n)
tryDiv (a, f) (b, g)
    | g `divs` f = (a * recip b, OrderedMonomial $ V.zipWithSame (-) (getMonomial f) (getMonomial g))
    | otherwise  = error "cannot divide."

varMonom :: SNat n -> Ordinal n -> Monomial n
varMonom len o = V.replicate len 0 & ix o .~ 1
{-# INLINE varMonom #-}

-- | Monomial order which can be use to calculate n-th elimination ideal of m-ary polynomial.
-- This should judge monomial to be bigger if it contains variables to eliminate.
class (IsMonomialOrder n ord, KnownNat n) => EliminationType n m ord
instance KnownNat n => EliminationType n m Lex
instance (KnownNat n, KnownNat m, IsMonomialOrder n ord, IsMonomialOrder m ord', k ~ (n + m), KnownNat k)
      => EliminationType k n (ProductOrder n m ord ord')
instance (IsMonomialOrder k ord, ones ~ (Replicate n 1), SingI ones,
          (Length ones :<= k) ~ 'True, KnownNat k)
      => EliminationType k n (WeightOrder ones ord)

type EliminationOrder n m = ProductOrder n m Grevlex Grevlex

eliminationOrder :: SNat n -> SNat m -> EliminationOrder n m
eliminationOrder n m =
  withKnownNat n $ ProductOrder n m Grevlex Grevlex

sOnes :: Sing n -> Sing (Replicate n 1)
sOnes n = sReplicate n (sing :: Sing 1)

weightedEliminationOrder :: SNat n -> WeightedEliminationOrder n Grevlex
weightedEliminationOrder n =
  WeightOrder (sOnes n) (Proxy :: Proxy Grevlex)

type WeightedEliminationOrder (n :: Nat) (ord :: Type) =
  WeightOrder (Replicate n 1) ord

-- | Special ordering for ordered-monomials.
instance (Eq (Monomial n), IsOrder n name) => Ord (OrderedMonomial name n) where
  OrderedMonomial m `compare` OrderedMonomial n = cmpMonomial (Proxy :: Proxy name) m n

-- | For simplicity, we choose grevlex for the default monomial ordering (for the sake of efficiency).
instance {-# OVERLAPPING #-} Ord (Monomial n) where
  compare = grevlex

castMonomial :: (KnownNat m) => OrderedMonomial o n -> OrderedMonomial o' m
castMonomial = _Wrapped %~ fromList sing . V.toList

scastMonomial :: SNat m -> OrderedMonomial o n -> OrderedMonomial o m
scastMonomial sdim = _Wrapped %~ fromList sdim . V.toList

changeMonomialOrder :: o' -> OrderedMonomial ord n -> OrderedMonomial o' n
changeMonomialOrder _ = OrderedMonomial . getMonomial

changeMonomialOrderProxy :: Proxy o' -> OrderedMonomial ord n -> OrderedMonomial o' n
changeMonomialOrderProxy _ = OrderedMonomial . getMonomial

class    (IsMonomialOrder n ord) => IsMonomialOrder' ord n
instance (IsMonomialOrder n ord) => IsMonomialOrder' ord n

instance IsMonomialOrder' ord n :=> IsMonomialOrder n ord where
  ins = C.Sub Dict

-- | Monomial ordering which can do with monomials of arbitrary large arity.
type IsStrongMonomialOrder ord = Forall (IsMonomialOrder' ord)

withStrongMonomialOrder :: forall ord n r proxy (proxy' :: Nat -> Type).
                           (IsStrongMonomialOrder ord)
                        => proxy ord -> proxy' n -> (IsMonomialOrder n ord => r) -> r
withStrongMonomialOrder _ _ r = r C.\\ dict
  where
    ismToPrim = (ins :: IsMonomialOrder' ord n C.:- IsMonomialOrder n ord)
    primeInst = inst :: Forall (IsMonomialOrder' ord) C.:- IsMonomialOrder' ord n
    dict = ismToPrim `C.trans` primeInst

-- | Comparing monomials with different arity,
--   padding with @0@ at bottom of the shorter monomial to
--   make the length equal.
cmpAnyMonomial :: IsStrongMonomialOrder ord
               => Proxy ord -> Monomial n -> Monomial m -> Ordering
cmpAnyMonomial pxy t t' =
  let (l, u, u') = padVecs 0 t t'
  in withStrongMonomialOrder pxy l $ cmpMonomial pxy u u'

orderMonomial :: proxy ord -> Monomial n -> OrderedMonomial ord n
orderMonomial _ = OrderedMonomial
{-# INLINE orderMonomial #-}
