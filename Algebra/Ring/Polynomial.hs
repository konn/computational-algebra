{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, MultiParamTypeClasses        #-}
{-# LANGUAGE PolyKinds, ScopedTypeVariables, StandaloneDeriving              #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances, ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-type-defaults                    #-}
module Algebra.Ring.Polynomial
    ( Polynomial, Monomial, MonomialOrder, Order
    , lex, revlex, graded, grlex, grevlex, transformMonomial
    , IsPolynomial, coeff, lcmMonomial, sPolynomial, polynomial
    , castMonomial, castPolynomial, toPolynomial, changeOrder
    , scastMonomial, scastPolynomial, OrderedPolynomial, showPolynomialWithVars
    , normalize, injectCoeff, varX, var, getTerms, shiftR, orderedBy
    , divs, tryDiv, fromList -- , genVarsV
    , leadingTerm, leadingMonomial, leadingCoeff, genVars, sDegree
    , OrderedMonomial(..), Grevlex(..), Revlex(..), Lex(..), Grlex(..)
    , IsOrder, IsMonomialOrder)  where

import           Algebra.Internal
import           Algebra.Ring.Noetherian
import           Control.Arrow
import           Control.Lens
import           Data.List               (intercalate)
import           Data.Map                (Map)
import qualified Data.Map                as M
import           Data.Maybe
import           Data.Monoid
import           Data.Ord
import           Data.Proxy
import           Numeric.Algebra
import           Prelude                 hiding (lex, (*), (+), (-), (^), (^^), recip, negate)
import qualified Prelude                 as P

-- | N-ary Monomial. IntMap contains degrees for each x_i.
type Monomial (n :: Nat) = Vector Int n

-- | convert NAry list into Monomial.
fromList :: SNat n -> [Int] -> Monomial n
fromList SZ _ = Nil
fromList (SS n) [] = 0 :- fromList n []
fromList (SS n) (x : xs) = x :- fromList n xs

-- | Monomial order (of degree n). This should satisfy following laws:
-- (1) Totality: forall a, b (a < b || a == b || b < a)
-- (2) Additivity: a <= b ==> a + c <= b + c
-- (3) Non-negative: forall a, 0 <= a
type MonomialOrder n = Monomial n -> Monomial n -> Ordering

totalDegree :: Monomial n -> Int
totalDegree = foldrV (+) 0

-- | Lexicographical order. This *is* a monomial order.
lex :: MonomialOrder n
lex Nil Nil = EQ
lex (x :- xs) (y :- ys) = x `compare` y <> xs `lex` ys
lex _ _ = error "cannot happen"

-- | Reversed lexicographical order. This is *not* a monomial order.
revlex :: Monomial n -> Monomial n -> Ordering
revlex (x :- xs) (y :- ys) = xs `revlex` ys <> y `compare` x
revlex Nil       Nil       = EQ
revlex _ _ = error "cannot happen!"

-- | Convert ordering into graded one.
graded :: (Monomial n -> Monomial n -> Ordering) -> (Monomial n -> Monomial n -> Ordering)
graded cmp xs ys = comparing totalDegree xs ys <> cmp xs ys

-- | Graded lexicographical order. This *is* a monomial order.
grlex :: MonomialOrder n
grlex = graded lex

-- | Graded reversed lexicographical order. This *is* a monomial order.
grevlex :: MonomialOrder n
grevlex = graded revlex

-- | A wrapper for monomials with a certain (monomial) order.
newtype OrderedMonomial (ordering :: *) n = OrderedMonomial { getMonomial :: Monomial n }
deriving instance (Eq (Monomial n)) => Eq (OrderedMonomial ordering n)

instance Wrapped (Monomial n) (Monomial m) (OrderedMonomial o n) (OrderedMonomial o' m) where
  wrapped = iso OrderedMonomial getMonomial

-- | Class to lookup ordering from its (type-level) name.
class IsOrder (ordering :: *) where
  cmpMonomial :: Proxy ordering -> MonomialOrder n

-- * Names for orderings.
--   We didn't choose to define one single type for ordering names for the extensibility.
data Grevlex = Grevlex          -- Graded reversed lexicographical order
               deriving (Show, Eq, Ord)
data Lex = Lex                  -- Lexicographical order
           deriving (Show, Eq, Ord)
data Grlex = Grlex              -- Graded lexicographical order
             deriving (Show, Eq, Ord)
data Revlex = Revlex            -- Reversed lexicographical order
              deriving (Show, Eq, Ord)

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

-- | Special ordering for ordered-monomials.
instance (Eq (Monomial n), IsOrder name) => Ord (OrderedMonomial name n) where
  OrderedMonomial m `compare` OrderedMonomial n = cmpMonomial (Proxy :: Proxy name) m n

-- | For simplicity, we choose grevlex for the default monomial ordering (for the sake of efficiency).
instance (Eq (Monomial n)) => Ord (Monomial n) where
  compare = grevlex

-- | n-ary polynomial ring over some noetherian ring R.
newtype OrderedPolynomial r order n = Polynomial { terms :: Map (OrderedMonomial order n) r }
type Polynomial r = OrderedPolynomial r Grevlex

-- | Type-level constraint to check whether it forms polynomial ring or not.
type IsPolynomial r n = (NoetherianRing r, Sing n, Eq r)

-- | coefficient for a degree.
coeff :: (IsOrder order, IsPolynomial r n) => Monomial n -> OrderedPolynomial r order n -> r
coeff d = M.findWithDefault zero (OrderedMonomial d) . terms

instance Wrapped (Map (OrderedMonomial order n) r) (Map (OrderedMonomial order' m) q)
                 (OrderedPolynomial r order n)     (OrderedPolynomial q order' m) where
    wrapped = iso Polynomial  terms

castMonomial :: (IsOrder o, IsOrder o', Sing m, n :<= m) => OrderedMonomial o n -> OrderedMonomial o' m
castMonomial = unwrapped %~ fromList sing . toList

scastMonomial :: (n :<= m) => SNat m -> OrderedMonomial o n -> OrderedMonomial o m
scastMonomial snat = unwrapped %~ fromList snat . toList

castPolynomial :: (IsPolynomial r n, IsPolynomial r m, Sing m, IsOrder o, IsOrder o', n :<= m)
               => OrderedPolynomial r o n
               -> OrderedPolynomial r o' m
castPolynomial = unwrapped %~ M.mapKeys castMonomial

scastPolynomial :: (IsOrder o, IsOrder o', IsPolynomial r n, IsPolynomial r m, n :<= m, Sing m)
                => SNat m -> OrderedPolynomial r o n -> OrderedPolynomial r o' m
scastPolynomial _ = castPolynomial

normalize :: (Eq r, IsOrder order, IsPolynomial r n)
          => OrderedPolynomial r order n -> OrderedPolynomial r order n
normalize = unwrapped %~ M.insertWith (+) (OrderedMonomial $ fromList sing []) zero . M.filter (/= zero)

instance (Eq r, IsOrder order, IsPolynomial r n) => Eq (OrderedPolynomial r order n) where
  (normalize -> Polynomial f) == (normalize -> Polynomial g) = f == g

injectCoeff :: (IsPolynomial r n) => r -> OrderedPolynomial r order n
injectCoeff r = Polynomial $ M.singleton (OrderedMonomial $ fromList sing []) r

-- | By Hilbert's finite basis theorem, a polynomial ring over a noetherian ring is also a noetherian ring.
instance (IsOrder order, IsPolynomial r n) => NoetherianRing (OrderedPolynomial r order n) where
instance (IsOrder order, IsPolynomial r n) => Ring (OrderedPolynomial r order n) where
instance (IsOrder order, IsPolynomial r n) => Rig (OrderedPolynomial r order n) where
instance (IsOrder order, IsPolynomial r n) => Group (OrderedPolynomial r order n) where
  negate (Polynomial dic) = Polynomial $ fmap negate dic
instance (IsOrder order, IsPolynomial r n) => LeftModule Integer (OrderedPolynomial r order n) where
  n .* Polynomial dic = Polynomial $ fmap (n .*) dic  
instance (IsOrder order, IsPolynomial r n) => RightModule Integer (OrderedPolynomial r order n) where
  (*.) = flip (.*)
instance (IsOrder order, IsPolynomial r n) => Additive (OrderedPolynomial r order n) where
  (Polynomial f) + (Polynomial g) = normalize $ Polynomial $ M.unionWith (+) f g
instance (IsOrder order, IsPolynomial r n) => Monoidal (OrderedPolynomial r order n) where
  zero = injectCoeff zero
instance (IsOrder order, IsPolynomial r n) => LeftModule Natural (OrderedPolynomial r order n) where
  n .* Polynomial dic = Polynomial $ fmap (n .*) dic
instance (IsOrder order, IsPolynomial r n) => RightModule Natural (OrderedPolynomial r order n) where
  (*.) = flip (.*)
instance (IsOrder order, IsPolynomial r n) => Unital (OrderedPolynomial r order n) where
  one = injectCoeff one
instance (IsOrder order, IsPolynomial r n) => Multiplicative (OrderedPolynomial r order n) where
  Polynomial (M.toList -> d1) *  Polynomial (M.toList -> d2) =
    let dic = [ (OrderedMonomial $ zipWithV (+) a b, r * r') | (getMonomial -> a, r) <- d1, (getMonomial -> b, r') <- d2 ]
    in normalize $ Polynomial $ M.fromListWith (+) dic
instance (IsOrder order, IsPolynomial r n) => Semiring (OrderedPolynomial r order n) where
instance (IsOrder order, IsPolynomial r n) => Commutative (OrderedPolynomial r order n) where
instance (IsOrder order, IsPolynomial r n) => Abelian (OrderedPolynomial r order n) where

instance (Eq r, IsPolynomial r n, IsOrder order, Show r) => Show (OrderedPolynomial r order n) where
  show = showPolynomialWithVars [(n, "X_"++ show n) | n <- [1..]]

showPolynomialWithVars :: (Eq a, Show a, Sing n, NoetherianRing a, IsOrder ordering)
                       => [(Int, String)] -> OrderedPolynomial a ordering n -> String
showPolynomialWithVars dic p0@(Polynomial d)
    | p0 == zero = "0"
    | otherwise = intercalate " + " $ mapMaybe showTerm $ M.toDescList d
    where
      showTerm (getMonomial -> deg, c)
          | c == zero = Nothing
          | otherwise =
              let cstr = if (c == zero - one)
                         then if any (/= zero) (toList deg) then "-" else "-1"
                         else if (c /= one || isConstantMonomial deg)
                              then show c ++ " "
                              else ""
              in Just $ cstr ++ unwords (mapMaybe showDeg (zip [1..] $ toList deg))
      showDeg (n, p) | p == 0    = Nothing
                     | p == 1    = Just $ showVar n
                     | otherwise = Just $ showVar n ++ "^" ++ show p
      showVar n = fromMaybe ("X_" ++ show n) $ lookup n dic

isConstantMonomial :: (Eq a, Num a) => Vector a n -> Bool
isConstantMonomial v = all (== 0) $ toList v

-- | We provide Num instance to use trivial injection R into R[X].
--   Do not use signum or abs.
instance (IsMonomialOrder order, IsPolynomial r n, Num r) => Num (OrderedPolynomial r order n) where
  (+) = (Numeric.Algebra.+)
  (*) = (Numeric.Algebra.*)
  fromInteger = injectCoeff . P.fromInteger
  signum f = if f == zero then zero else injectCoeff 1
  abs = id
  negate = ((P.negate 1 :: Integer) .*)

varX :: (NoetherianRing r, Sing n, One :<= n) => OrderedPolynomial r order n
varX = Polynomial $ M.singleton (OrderedMonomial $ fromList sing [1]) one

var :: (NoetherianRing r, Sing m, S n :<= m) => SNat (S n) -> OrderedPolynomial r order m
var vIndex = Polynomial $ M.singleton (OrderedMonomial $ fromList sing (buildIndex vIndex)) one

toPolynomial :: (IsOrder order, IsPolynomial r n) => (r, Monomial n) -> OrderedPolynomial r order n
toPolynomial (c, deg) = Polynomial $ M.singleton (OrderedMonomial deg) c

polynomial :: (Sing n, Eq r, NoetherianRing r, IsOrder order) => Map (OrderedMonomial order n) r -> OrderedPolynomial r order n
polynomial dic = normalize $ Polynomial dic

buildIndex :: SNat (S n) -> [Int]
buildIndex (SS SZ) = [1]
buildIndex (SS (SS n))  = 0 : buildIndex (SS n)

leadingTerm :: (IsOrder order, IsPolynomial r n)
                => OrderedPolynomial r order n -> (r, Monomial n)
leadingTerm (Polynomial d) =
  case M.maxViewWithKey d of
    Just ((deg, c), _) -> (c, getMonomial deg)
    Nothing -> (zero, fromList sing [])

leadingMonomial :: (IsOrder order, IsPolynomial r n) => OrderedPolynomial r order n -> Monomial n
leadingMonomial = snd . leadingTerm

leadingCoeff :: (IsOrder order, IsPolynomial r n) => OrderedPolynomial r order n -> r
leadingCoeff = fst . leadingTerm

divs :: Monomial n -> Monomial n -> Bool
xs `divs` ys = and $ toList $ zipWithV (<=) xs ys

tryDiv :: Field r => (r, Monomial n) -> (r, Monomial n) -> (r, Monomial n)
tryDiv (a, f) (b, g)
    | g `divs` f = (a * recip b, zipWithV (-) f g)
    | otherwise  = error "cannot divide."

lcmMonomial :: Monomial n -> Monomial n -> Monomial n
lcmMonomial = zipWithV max

sPolynomial :: (IsPolynomial k n, Field k, IsOrder order)
            => OrderedPolynomial k order n
            -> OrderedPolynomial k order n -> OrderedPolynomial k order n
sPolynomial f g =
    let h = (one, lcmMonomial (leadingMonomial f) (leadingMonomial g))
    in toPolynomial (h `tryDiv` leadingTerm f) * f - toPolynomial (h `tryDiv` leadingTerm g) * g

changeOrder :: (Eq (Monomial n), IsOrder o, IsOrder o',  Sing n)
            => o' -> OrderedPolynomial k o n -> OrderedPolynomial k o' n
changeOrder _ = unwrapped %~ M.mapKeys (OrderedMonomial . getMonomial)

getTerms :: OrderedPolynomial k order n -> [(k, Monomial n)]
getTerms = map (snd &&& getMonomial . fst) . M.toDescList . terms

transformMonomial :: (IsOrder o, IsPolynomial k n, IsPolynomial k m)
                  => (Monomial n -> Monomial m) -> OrderedPolynomial k o n -> OrderedPolynomial k o m
transformMonomial trans (Polynomial d) = Polynomial $ M.mapKeys (OrderedMonomial . trans . getMonomial) d

orderedBy :: IsOrder o => OrderedPolynomial k o n -> o -> OrderedPolynomial k o n
p `orderedBy` _ = p

shiftR :: forall k r n ord. (Field r, IsPolynomial r n, IsPolynomial r (k :+: n), IsOrder ord)
       => SNat k -> OrderedPolynomial r ord n -> OrderedPolynomial r ord (k :+: n)
shiftR k =
  case singInstance k of
    SingInstance -> transformMonomial (appendV (fromList k []))

genVars :: forall k o n. (IsPolynomial k (S n), IsOrder o)
        => SNat (S n) -> [OrderedPolynomial k o (S n)]
genVars sn =
    let n  = toInt sn
        seed = cycle $ 1 : replicate (n - 1) 0
    in map (\m -> Polynomial $ M.singleton (OrderedMonomial $ fromList sn $ take n (drop (n-m) seed)) one) [0..n-1]

sDegree :: OrderedPolynomial k ord n -> SNat n
sDegree (Polynomial dic) = sLengthV $ getMonomial $ fst $ M.findMin dic
