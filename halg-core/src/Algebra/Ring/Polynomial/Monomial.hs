{-# LANGUAGE CPP, ConstraintKinds, DataKinds, ExistentialQuantification   #-}
{-# LANGUAGE ExplicitNamespaces, FlexibleContexts, FlexibleInstances      #-}
{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, IncoherentInstances       #-}
{-# LANGUAGE LiberalTypeSynonyms, MultiParamTypeClasses, ParallelListComp #-}
{-# LANGUAGE PatternSynonyms, PolyKinds, RankNTypes, ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving, TemplateHaskell, TypeApplications        #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances            #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Algebra.Ring.Polynomial.Monomial
       ( Monomial, OrderedMonomial(OrderedMonomial), getMonomial,
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
         withStrongMonomialOrder, cmpAnyMonomial, orderMonomial,
         ifoldMapMonom
       ) where
import           Algebra.Internal             hiding ((:>))
import           AlgebraicPrelude             hiding (lex)
import           Control.DeepSeq              (NFData (..))
import qualified Control.Foldl                as Fl
import           Control.Lens                 (Ixed (..), imap, makeLenses,
                                               makeWrapped, (%~), (&), (.~), _1,
                                               _2, _Wrapped)
import qualified Data.Coerce                  as DC
import           Data.Constraint              ((:=>) (..), Dict (..))
import qualified Data.Constraint              as C
import           Data.Constraint.Forall       (Forall, inst)
import           Data.Functor.Identity        (Identity (..))
import           Data.Hashable                (Hashable (..))
import           Data.Kind                    (Type)
import           Data.Maybe                   (catMaybes)
import           Data.Monoid                  (Dual (..), Sum (..), (<>))
import           Data.MonoTraversable         (MonoFoldable (..), oand,
                                               ofoldMap, ofoldl', ofoldlUnwrap,
                                               osum)
import           Data.Ord                     (comparing)
import qualified Data.Semigroup               as Semi
import           Data.Singletons.Prelude      (SList, Sing)
import           Data.Singletons.Prelude      (SingKind (..))
import           Data.Singletons.Prelude.List (Length, Replicate, sReplicate)
import           Data.Singletons.TypeLits     (withKnownNat)
import qualified Data.Sized.Builtin           as V
import           Data.Type.Natural.Class      (IsPeano (..), PeanoOrder (..))
import qualified Data.Vector.Generic          as G
import qualified Data.Vector.Generic.Mutable  as M
import           Data.Vector.Instances        ()
import qualified Data.Vector.Unboxed          as UV
import qualified Prelude                      as P

type Monomial n = USized n Int

-- | A wrapper for monomials with a certain (monomial) order.
newtype OrderedMonomial ordering n =
  OrderedMonomial { getMonomial :: Monomial n }
  deriving (NFData, Eq, Hashable)

makeLenses ''OrderedMonomial
makeWrapped ''OrderedMonomial

-- | convert NAry list into Monomial'.
fromList :: SNat n -> [Int] -> Monomial n
fromList len = V.fromListWithDefault len 0

-- We don't call Sized.zipWithSame here; it doesn't uses UV.zipWith at all!
zws :: (KnownNat n, Unbox a) => (Int -> Int -> a) -> USized n Int -> USized n Int -> USized n a
zws = ((V.unsafeToSized' .) .) . (`on` V.unsized) . UV.zipWith
{-# INLINE zws #-}

instance KnownNat n => Multiplicative (Monomial n) where
  (*) = zws (+)
  {-# INLINE (*) #-}

instance KnownNat n => Unital (Monomial n) where
  one = fromList sing []

-- | Monomial' order (of degree n). This should satisfy following laws:
-- (1) Totality: forall a, b (a < b || a == b || b < a)
-- (2) Additivity: a <= b ==> a + c <= b + c
-- (3) Non-negative: forall a, 0 <= a
type MonomialOrder n = Monomial n -> Monomial n -> Ordering

isRelativelyPrime :: KnownNat n => OrderedMonomial ord n -> OrderedMonomial ord n -> Bool
isRelativelyPrime n m = lcmMonomial n m == n * m

totalDegree :: OrderedMonomial ord n -> Int
totalDegree = osum . getMonomial
{-# INLINE totalDegree #-}

-- | Lexicographical order. This *is* a monomial order.
lex :: KnownNat n => MonomialOrder n
lex m n = ofoldMap (uncurry compare) $ V.zipSame m n
{-# INLINE [2] lex #-}

-- | Reversed lexicographical order. This is *not* a monomial order.
revlex :: KnownNat n => MonomialOrder n
revlex xs ys =
  unWrapOrdering . ofoldl' (flip (<>)) (WrapOrdering EQ) $ zws ((WrapOrdering .) .flip compare) xs ys
{-# INLINE [2] revlex #-}

-- | Convert ordering into graded one.
graded :: MonomialOrder n -> MonomialOrder n
graded cmp xs ys = comparing osum xs ys <> cmp xs ys
{-# INLINE[2] graded #-}
{-# RULES
"graded/graded"  [~1] forall x. graded (graded x) = graded x
  #-}

-- | Graded lexicographical order. This *is* a monomial order.
grlex :: KnownNat n => MonomialOrder n
grlex = graded lex
{-# INLINE [2] grlex #-}

newtype WrapOrdering  = WrapOrdering { unWrapOrdering :: Ordering }
  deriving (Read, Show, Eq, Ord, Monoid, Semi.Semigroup)
newtype instance UV.Vector    WrapOrdering = V_WrapOrdering (UV.Vector Word8)
newtype instance UV.MVector s WrapOrdering = MV_WrapOrdering (UV.MVector s Word8)
instance Unbox WrapOrdering
instance M.MVector UV.MVector WrapOrdering where
  {-# INLINE basicLength #-}
  {-# INLINE basicUnsafeSlice #-}
  {-# INLINE basicOverlaps #-}
  {-# INLINE basicUnsafeNew #-}
  {-# INLINE basicInitialize #-}
  {-# INLINE basicUnsafeReplicate #-}
  {-# INLINE basicUnsafeRead #-}
  {-# INLINE basicUnsafeWrite #-}
  {-# INLINE basicClear #-}
  {-# INLINE basicSet #-}
  {-# INLINE basicUnsafeCopy #-}
  {-# INLINE basicUnsafeGrow #-}
  basicLength (MV_WrapOrdering v) = M.basicLength v
  basicUnsafeSlice i n (MV_WrapOrdering v) = MV_WrapOrdering $ M.basicUnsafeSlice i n v
  basicOverlaps (MV_WrapOrdering v1) (MV_WrapOrdering v2) = M.basicOverlaps v1 v2
  basicUnsafeNew n = MV_WrapOrdering `liftM` M.basicUnsafeNew n
  basicInitialize (MV_WrapOrdering v) = M.basicInitialize v
  basicUnsafeReplicate n x = MV_WrapOrdering `liftM` M.basicUnsafeReplicate n (fromWrapOrdering x)
  basicUnsafeRead (MV_WrapOrdering v) i = toWrapOrdering `liftM` M.basicUnsafeRead v i
  basicUnsafeWrite (MV_WrapOrdering v) i x = M.basicUnsafeWrite v i (fromWrapOrdering x)
  basicClear (MV_WrapOrdering v) = M.basicClear v
  basicSet (MV_WrapOrdering v) x = M.basicSet v (fromWrapOrdering x)
  basicUnsafeCopy (MV_WrapOrdering v1) (MV_WrapOrdering v2) = M.basicUnsafeCopy v1 v2
  basicUnsafeMove (MV_WrapOrdering v1) (MV_WrapOrdering v2) = M.basicUnsafeMove v1 v2
  basicUnsafeGrow (MV_WrapOrdering v) n = MV_WrapOrdering `liftM` M.basicUnsafeGrow v n

instance G.Vector UV.Vector WrapOrdering where
  {-# INLINE basicUnsafeFreeze #-}
  {-# INLINE basicUnsafeThaw #-}
  {-# INLINE basicLength #-}
  {-# INLINE basicUnsafeSlice #-}
  {-# INLINE basicUnsafeIndexM #-}
  {-# INLINE elemseq #-}
  basicUnsafeFreeze (MV_WrapOrdering v) = V_WrapOrdering `liftM` G.basicUnsafeFreeze v
  basicUnsafeThaw (V_WrapOrdering v) = MV_WrapOrdering `liftM` G.basicUnsafeThaw v
  basicLength (V_WrapOrdering v) = G.basicLength v
  basicUnsafeSlice i n (V_WrapOrdering v) = V_WrapOrdering $ G.basicUnsafeSlice i n v
  basicUnsafeIndexM (V_WrapOrdering v) i = toWrapOrdering `liftM` G.basicUnsafeIndexM v i
  basicUnsafeCopy (MV_WrapOrdering mv) (V_WrapOrdering v) = G.basicUnsafeCopy mv v
  elemseq _ = seq


fromWrapOrdering :: WrapOrdering -> Word8
{-# INLINE fromWrapOrdering #-}
fromWrapOrdering (WrapOrdering LT) = 0
fromWrapOrdering (WrapOrdering EQ) = 1
fromWrapOrdering (WrapOrdering GT) = 2

toWrapOrdering :: Word8 -> WrapOrdering
{-# INLINE toWrapOrdering #-}
toWrapOrdering 0 = WrapOrdering LT
toWrapOrdering 1 = WrapOrdering EQ
toWrapOrdering _ = WrapOrdering GT

-- | Graded reversed lexicographical order. This *is* a monomial order.
grevlex :: MonomialOrder n
grevlex = grevlexF
{-# INLINE [2] grevlex #-}

grevlexF :: MonomialOrder n
grevlexF = (Fl.purely ofoldlUnwrap body .) . (UV.zip `on` V.unsized)
  where
    body :: Fl.Fold (Int, Int) Ordering
    body = (<>) <$> Fl.foldMap (DC.coerce @_ @(Sum Int, Sum Int)) (uncurry compare)
                <*> Fl.foldMap (Dual . uncurry (flip compare)) getDual
{-# INLINE grevlexF #-}

instance KnownNat n => Show (OrderedMonomial ord n) where
  show xs =
    let vs = catMaybes $
            imap (\n i ->
                   if i > 0
                   then Just ("X_" ++ show n ++ if i == 1 then "" else "^" ++ show i)
                   else Nothing)
            $ otoList $ getMonomial xs
    in if null vs then "1" else unwords vs

instance KnownNat n => Multiplicative (OrderedMonomial ord n) where
  OrderedMonomial n * OrderedMonomial m = OrderedMonomial $ zws (+) n m

instance KnownNat n => Division (OrderedMonomial ord n) where
  recip (OrderedMonomial n) = OrderedMonomial $ V.map P.negate n
  OrderedMonomial n / OrderedMonomial m = OrderedMonomial $ zws (-) n m

instance KnownNat n => Unital (OrderedMonomial ord n) where
  one = OrderedMonomial one

-- | Class to lookup ordering from its (type-level) name.
class IsOrder (n :: Nat) (ordering :: Type) where
  cmpMonomial :: Proxy ordering -> MonomialOrder n

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
newtype Graded ord = Graded ord
                  deriving (Read, Show, Eq, Ord)

instance IsOrder n ord => IsOrder n (Graded ord) where
  cmpMonomial Proxy = graded (cmpMonomial (Proxy :: Proxy ord))
  {-# INLINE [1] cmpMonomial #-}

instance IsMonomialOrder n ord => IsMonomialOrder n (Graded ord)

data ProductOrder (n :: Nat) (m :: Nat) (a :: Type) (b :: Type) where
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
  in osum $ zws (*) cfs m
{-# INLINE [2] calcOrderWeight' #-}

weightOrder :: forall n ns ord. (KnownNat n, IsOrder n ord, SingI ns)
            => Proxy (WeightOrder ns ord) -> MonomialOrder n
weightOrder Proxy m m' =
     comparing (calcOrderWeight (Proxy :: Proxy ns)) m m'
  <> cmpMonomial (Proxy :: Proxy ord) m m'
{-# INLINE weightOrder #-}

instance (KnownNat n, IsOrder n ord, SingI ws)
       => IsOrder n (WeightOrder ws ord) where
  cmpMonomial = weightOrder
  {-# INLINE [1] cmpMonomial #-}

instance (IsOrder n ord, IsOrder m ord', KnownNat m, KnownNat n, k ~ (n + m))
      => IsOrder k (ProductOrder n m ord ord') where
  cmpMonomial = productOrder
  {-# INLINE [1] cmpMonomial #-}

-- They're all total orderings.
instance KnownNat n => IsOrder n Grevlex where
  cmpMonomial _ = grevlex
  {-# INLINE [1] cmpMonomial #-}

instance KnownNat n => IsOrder n Revlex where
  cmpMonomial _ = revlex
  {-# INLINE [1] cmpMonomial #-}

instance KnownNat n => IsOrder n Lex where
  cmpMonomial _ = lex
  {-# INLINE [1] cmpMonomial #-}

instance KnownNat n => IsOrder n Grlex where
  cmpMonomial _ = grlex
  {-# INLINE [1] cmpMonomial #-}

-- | Class for Monomial' orders.
class IsOrder n name => IsMonomialOrder n name where

-- Note that Revlex is not a monomial order.
-- This distinction is important when we calculate a quotient or Groebner basis.
instance KnownNat n => IsMonomialOrder n Grlex
instance KnownNat n => IsMonomialOrder n Grevlex
instance KnownNat n => IsMonomialOrder n Lex
instance (KnownNat n, KnownNat m, IsMonomialOrder n o, IsMonomialOrder m o', k ~ (n + m))
      => IsMonomialOrder k (ProductOrder n m o o')
instance (KnownNat k, SingI ws, IsMonomialOrder k ord)
      => IsMonomialOrder k (WeightOrder ws ord)

lcmMonomial :: KnownNat n => OrderedMonomial ord n -> OrderedMonomial ord n -> OrderedMonomial ord n
lcmMonomial (OrderedMonomial m) (OrderedMonomial n) = OrderedMonomial $ zws max m n
{-# INLINE lcmMonomial #-}

gcdMonomial :: KnownNat n => OrderedMonomial ord n -> OrderedMonomial ord n -> OrderedMonomial ord n
gcdMonomial (OrderedMonomial m) (OrderedMonomial n) = OrderedMonomial $ zws P.min m n
{-# INLINE gcdMonomial #-}

divs :: KnownNat n => OrderedMonomial ord n -> OrderedMonomial ord n -> Bool
(OrderedMonomial xs) `divs` (OrderedMonomial ys) = oand $ zws (<=) xs ys

isPowerOf :: KnownNat n => OrderedMonomial ord n -> OrderedMonomial ord n -> Bool
OrderedMonomial n `isPowerOf` OrderedMonomial m =
  case V.sFindIndices (> 0) m of
    [ind] -> osum n == V.sIndex ind n
    _     -> False

tryDiv :: (KnownNat n, Field r) => (r, OrderedMonomial ord n) -> (r, OrderedMonomial ord n) -> (r, OrderedMonomial ord n)
tryDiv (a, f) (b, g)
    | g `divs` f = (a * recip b, OrderedMonomial $ zws (-) (getMonomial f) (getMonomial g))
    | otherwise  = error "cannot divide."

varMonom :: SNat n -> Ordinal n -> Monomial n
varMonom len o = V.replicate len 0 & ix o .~ 1
{-# INLINE varMonom #-}

-- | Monomial' order which can be use to calculate n-th elimination ideal of m-ary polynomial.
-- This should judge monomial to be bigger if it contains variables to eliminate.
class (IsMonomialOrder n ord, KnownNat n) => EliminationType n m ord
instance KnownNat n => EliminationType n m Lex
instance (KnownNat n, KnownNat m, IsMonomialOrder n ord, IsMonomialOrder m ord', k ~ (n + m), KnownNat k)
      => EliminationType k n (ProductOrder n m ord ord')
instance (IsMonomialOrder k ord, ones ~ (Replicate n 1), SingI ones,
          (Length ones <= k) ~ 'True, KnownNat k)
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

castMonomial :: (KnownNat m) => OrderedMonomial o n -> OrderedMonomial o' m
castMonomial = _Wrapped %~ fromList sing . otoList

scastMonomial :: SNat m -> OrderedMonomial o n -> OrderedMonomial o m
scastMonomial sdim = _Wrapped %~ fromList sdim . otoList

changeMonomialOrder :: o' -> OrderedMonomial ord n -> OrderedMonomial o' n
changeMonomialOrder _ = DC.coerce

changeMonomialOrderProxy :: Proxy o' -> OrderedMonomial ord n -> OrderedMonomial o' n
changeMonomialOrderProxy _ = DC.coerce

class    (IsMonomialOrder n ord) => IsMonomialOrder' ord n
instance (IsMonomialOrder n ord) => IsMonomialOrder' ord n

instance IsMonomialOrder' ord n :=> IsMonomialOrder n ord where
  ins = C.Sub Dict

-- | Monomial' ordering which can do with monomials of arbitrary large arity.
type IsStrongMonomialOrder ord = Forall (IsMonomialOrder' ord)

withStrongMonomialOrder :: forall ord n r proxy (proxy' :: Nat -> Type).
                           (IsStrongMonomialOrder ord)
                        => proxy ord -> proxy' n -> (IsMonomialOrder n ord => r) -> r
withStrongMonomialOrder _ _ r = r C.\\ dict
  where
    ismToPrim = ins :: IsMonomialOrder' ord n C.:- IsMonomialOrder n ord
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

ifoldMapMonom :: (KnownNat n, Monoid m) => (Ordinal n -> Int -> m) -> Monomial n -> m
ifoldMapMonom f =
  UV.ifoldr (\i -> mappend . f (unsafeNaturalToOrd $ fromIntegral i)) mempty . V.unsized
