{-# LANGUAGE DataKinds, ExplicitNamespaces, FlexibleContexts              #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving         #-}
{-# LANGUAGE LiberalTypeSynonyms, MultiParamTypeClasses, ParallelListComp #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables                   #-}
{-# LANGUAGE StandaloneDeriving, TemplateHaskell, TypeFamilies            #-}
{-# LANGUAGE TypeOperators, UndecidableInstances                          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Algebra.Ring.Polynomial.Monomial
       ( Monomial, OrderedMonomial(..),
         IsOrder(..), IsMonomialOrder, MonomialOrder,
         isRelativelyPrime, totalDegree, ProductOrder(..),
         productOrder, productOrder', WeightProxy, WeightOrder(..),
         gcdMonomial, divs, isPowerOf, tryDiv, lcmMonomial,
         Lex(..), EliminationType, EliminationOrder,
         WeightedEliminationOrder, eliminationOrder, weightedEliminationOrder,
         lex, revlex, graded, grlex, grevlex,
         weightOrder, Grevlex(..), fromList,
         Revlex(..), Grlex(..), Graded(..),
         castMonomial, scastMonomial, varMonom
       ) where
import Algebra.Internal

import           Control.DeepSeq         (NFData (..))
import           Control.Lens            (makeLenses, makeWrapped, (%~),
                                          _Wrapped)
import           Data.Hashable           (Hashable (..))
import           Data.Maybe              (catMaybes)
import           Data.Monoid             ((<>))
import           Data.Ord                (comparing)
import           Data.Singletons.Prelude (POrd (..), SList, Sing (SCons, SNil))
import           Data.Singletons.Prelude (SingI (..), SingInstance (..))
import           Data.Singletons.Prelude (bugInGHC, singInstance)
import           Data.Type.Natural       (Nat (..), One, SNat, Sing (SS, SZ),
                                          sNatToInt)
import           Data.Type.Ordinal       (Ordinal (..))
import           Data.Vector.Sized       (Vector (..))
import qualified Data.Vector.Sized       as V
import           Numeric.Algebra         hiding (Order (..))
import           Prelude                 hiding (Fractional (..), Integral (..),
                                          Num (..), Real (..), lex, product,
                                          sum)
import qualified Prelude                 as P

-- | N-ary Monomial. IntMap contains degrees for each x_i.
type Monomial (n :: Nat) = V.Vector Int n


-- | A wrapper for monomials with a certain (monomial) order.
newtype OrderedMonomial ordering n =
  OrderedMonomial { getMonomial :: Monomial n }
  deriving (NFData)

makeLenses ''OrderedMonomial
makeWrapped ''OrderedMonomial

-- | convert NAry list into Monomial.
fromList :: SNat n -> [Int] -> Monomial n
fromList SZ _ = Nil
fromList (SS n) [] = 0 :- fromList n []
fromList (SS n) (x : xs) = x :- fromList n xs

-- | Monomial order (of degree n). This should satisfy following laws:
-- (1) Totality: forall a, b (a < b || a == b || b < a)
-- (2) Additivity: a <= b ==> a + c <= b + c
-- (3) Non-negative: forall a, 0 <= a
type MonomialOrder = forall n. Monomial n -> Monomial n -> Ordering

isRelativelyPrime :: IsMonomialOrder ord => OrderedMonomial ord n -> OrderedMonomial ord n -> Bool
isRelativelyPrime n m = lcmMonomial n m == n * m

totalDegree :: OrderedMonomial ord n -> Int
totalDegree = V.sum . getMonomial
{-# INLINE totalDegree #-}

-- | Lexicographical order. This *is* a monomial order.
lex :: MonomialOrder
lex Nil Nil = EQ
lex (x :- xs) (y :- ys) = x `compare` y <> xs `lex` ys
lex _ _ = bugInGHC

-- | Reversed lexicographical order. This is *not* a monomial order.
revlex :: Monomial n -> Monomial n -> Ordering
revlex (x :- xs) (y :- ys) = xs `revlex` ys <> y `compare` x
revlex Nil       Nil       = EQ
revlex _ _ = bugInGHC

-- | Convert ordering into graded one.
graded :: (Monomial n -> Monomial n -> Ordering) -> (Monomial n -> Monomial n -> Ordering)
graded cmp xs ys = comparing (V.sum) xs ys <> cmp xs ys
{-# INLINE[2] graded #-}
{-# RULES
"graded/grevlex" graded grevlex = grevlex
"graded/grlex"   graded grlex   = grlex
  #-}

-- | Graded lexicographical order. This *is* a monomial order.
grlex :: MonomialOrder
grlex = graded lex
{-# INLINE grlex #-}

-- | Graded reversed lexicographical order. This *is* a monomial order.
grevlex :: MonomialOrder
grevlex = graded revlex
{-# INLINE grevlex #-}

deriving instance Hashable (Monomial n) => Hashable (OrderedMonomial ordering n)
deriving instance (Eq (Monomial n)) => Eq (OrderedMonomial ordering n)
instance SingI n => Show (OrderedMonomial ord n) where
  show xs =
    let vs = catMaybes $ V.toList $
            V.zipWithSame (\n i -> if i > 0
                                   then Just ("X_" ++ show n ++ if i == 1 then "" else "^" ++ show i)
                                   else Nothing)
            (V.unsafeFromList' [0 :: Int ..])
            $ getMonomial xs
    in if null vs then "1" else unwords vs

instance Multiplicative (OrderedMonomial ord n) where
  OrderedMonomial n * OrderedMonomial m = OrderedMonomial $ V.zipWithSame (+) n m

instance SingI n => Division (OrderedMonomial ord n) where
  recip = _Wrapped %~ V.map P.negate
  OrderedMonomial n / OrderedMonomial m = OrderedMonomial $ V.zipWithSame (-) n m

instance SingI n => Unital (OrderedMonomial ord n) where
  one = OrderedMonomial $ fromList sing []

-- | Class to lookup ordering from its (type-level) name.
class IsOrder (ordering :: *) where
  cmpMonomial :: Proxy ordering -> MonomialOrder

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

instance IsOrder ord => IsOrder (Graded ord) where
  cmpMonomial Proxy = graded (cmpMonomial (Proxy :: Proxy ord))

instance IsMonomialOrder ord => IsMonomialOrder (Graded ord)

data ProductOrder (n :: Nat) (a :: *) (b :: *) where
  ProductOrder :: SNat n -> ord -> ord' -> ProductOrder n ord ord'

productOrder :: forall ord ord' n m. (IsOrder ord, IsOrder ord', SingI n)
             => Proxy (ProductOrder n ord ord') -> Monomial m -> Monomial m -> Ordering
productOrder _ m m' =
  case sing :: SNat n of
    n -> case (V.splitAtMost n m, V.splitAtMost n m') of
           ((xs, xs'), (ys, ys')) -> cmpMonomial (Proxy :: Proxy ord) xs ys <> cmpMonomial (Proxy :: Proxy ord') xs' ys'

productOrder' :: forall n ord ord' m.(IsOrder ord, IsOrder ord')
              => SNat n -> ord -> ord' -> Monomial m -> Monomial m -> Ordering
productOrder' n ord ord' =
  case singInstance n of SingInstance -> productOrder (toProxy $ ProductOrder n ord ord')

type WeightProxy (v :: [Nat]) = SList v

data WeightOrder (v :: [Nat]) (ord :: *) where
  WeightOrder :: SList (v :: [Nat]) -> ord -> WeightOrder v ord

calcOrderWeight :: forall vs n. (SingI vs)
                 => Proxy (vs :: [Nat]) -> V.Vector Int n -> Int
calcOrderWeight Proxy = calcOrderWeight' (sing :: SList vs)

calcOrderWeight' :: forall vs n. SList (vs :: [Nat]) -> V.Vector Int n -> Int
calcOrderWeight' SNil _ = 0
calcOrderWeight' (SCons n ns) (x :- xs) =
  x * sNatToInt n + calcOrderWeight' ns xs
calcOrderWeight' (SCons _ _) Nil = 0

weightOrder :: forall ns ord m. (IsOrder ord, SingI ns)
            => Proxy (WeightOrder ns ord) -> Monomial m -> Monomial m -> Ordering
weightOrder Proxy m m' = comparing (calcOrderWeight (Proxy :: Proxy ns)) m m'
                         <> cmpMonomial (Proxy :: Proxy ord) m m'

instance (IsOrder ord, SingI ws) => IsOrder (WeightOrder ws ord) where
  cmpMonomial p = weightOrder p

instance (IsOrder ord, IsOrder ord', SingI n) => IsOrder (ProductOrder n ord ord') where
  cmpMonomial p = productOrder p

-- They're all total orderings.
instance IsOrder Grevlex where
  cmpMonomial _ = grevlex

instance IsOrder Revlex where
  cmpMonomial _ = revlex

instance IsOrder Lex where
  cmpMonomial _ = lex

instance IsOrder Grlex where
  cmpMonomial _ = grlex

-- | Class for Monomial orders.
class IsOrder name => IsMonomialOrder name where

-- Note that Revlex is not a monomial order.
-- This distinction is important when we calculate a quotient or Groebner basis.
instance IsMonomialOrder Grlex
instance IsMonomialOrder Grevlex
instance IsMonomialOrder Lex
instance (SingI n, IsMonomialOrder o, IsMonomialOrder o') => IsMonomialOrder (ProductOrder n o o')
instance (SingI ws, IsMonomialOrder ord) => IsMonomialOrder (WeightOrder ws ord)

lcmMonomial :: OrderedMonomial ord n -> OrderedMonomial ord n -> OrderedMonomial ord n
lcmMonomial (OrderedMonomial m) (OrderedMonomial n) = OrderedMonomial $ V.zipWithSame max m n

gcdMonomial :: OrderedMonomial ord n -> OrderedMonomial ord n -> OrderedMonomial ord n
gcdMonomial (OrderedMonomial m) (OrderedMonomial n) = OrderedMonomial $ V.zipWithSame P.min m n


divs :: OrderedMonomial ord n -> OrderedMonomial ord n -> Bool
(OrderedMonomial xs) `divs` (OrderedMonomial ys) = and $ V.toList $ V.zipWith (<=) xs ys

isPowerOf :: OrderedMonomial ord n -> OrderedMonomial ord n -> Bool
OrderedMonomial n `isPowerOf` OrderedMonomial m =
  case V.sFindIndices (> 0) m of
    [ind] -> V.sum n == V.sIndex ind n
    _     -> False

tryDiv :: Field r => (r, OrderedMonomial ord n) -> (r, OrderedMonomial ord n) -> (r, OrderedMonomial ord n)
tryDiv (a, f) (b, g)
    | g `divs` f = (a * recip b, OrderedMonomial $ V.zipWithSame (-) (getMonomial f) (getMonomial g))
    | otherwise  = error "cannot divide."

varMonom :: SNat n -> Ordinal m -> Monomial n
varMonom SZ     _      = V.Nil
varMonom (SS n) OZ     = 1 :- V.replicate n 0
varMonom (SS n) (OS m) = 0 :- varMonom n m
{-# INLINE varMonom #-}

-- | Monomial order which can be use to calculate n-th elimination ideal.
-- This should judge monomial to be bigger if it contains variables to eliminate.
class (IsMonomialOrder ord, SingI n) => EliminationType n ord
instance SingI n => EliminationType n Lex
instance (SingI n, IsMonomialOrder ord, IsMonomialOrder ord') => EliminationType n (ProductOrder n ord ord')
instance (IsMonomialOrder ord) => EliminationType 'Z (WeightOrder '[] ord)
instance (SingI ns, IsMonomialOrder ord, EliminationType n (WeightOrder ns ord))
    => EliminationType ('S n) (WeightOrder ('S 'Z ': ns) ord)

type EliminationOrder n = ProductOrder n Grevlex Grevlex

eliminationOrder :: SNat n -> EliminationOrder n
eliminationOrder n =
  case singInstance n of
    SingInstance -> ProductOrder n Grevlex Grevlex

weightedEliminationOrder :: SNat n -> WeightedEliminationOrder n Grevlex
weightedEliminationOrder n = WEOrder n (Proxy :: Proxy Grevlex)

type family EWeight (n :: Nat) :: [Nat]
type instance EWeight 'Z = '[]
type instance EWeight ('S n) = One ': EWeight n

data WeightedEliminationOrder (n :: Nat) (ord :: *) where
    WEOrder :: SNat n -> Proxy ord -> WeightedEliminationOrder n ord

instance (SingI n, IsMonomialOrder ord) => IsOrder (WeightedEliminationOrder n ord) where
  cmpMonomial Proxy m m' = comparing (calc (sing :: SNat n)) m m' <> cmpMonomial (Proxy :: Proxy ord) m m'
    where
      calc :: SNat l -> V.Vector Int m -> Int
      calc (SS _) Nil = 0
      calc SZ _ = 0
      calc (SS l) (x :- xs)= x + calc l xs

instance (SingI n, IsMonomialOrder ord) => IsMonomialOrder (WeightedEliminationOrder n ord)

instance (SingI n, IsMonomialOrder ord) => EliminationType n (WeightedEliminationOrder n ord) where

-- | Special ordering for ordered-monomials.
instance (Eq (Monomial n), IsOrder name) => Ord (OrderedMonomial name n) where
  OrderedMonomial m `compare` OrderedMonomial n = cmpMonomial (Proxy :: Proxy name) m n

-- | For simplicity, we choose grevlex for the default monomial ordering (for the sake of efficiency).
instance {-# OVERLAPPING #-} Ord (Monomial n) where
  compare = grevlex

castMonomial :: (IsOrder o, IsOrder o', SingI m, (n :<= m) ~ 'True) => OrderedMonomial o n -> OrderedMonomial o' m
castMonomial = _Wrapped %~ fromList sing . V.toList

scastMonomial :: (n :<= m) ~ 'True => SNat m -> OrderedMonomial o n -> OrderedMonomial o m
scastMonomial sdim = _Wrapped %~ fromList sdim . V.toList

