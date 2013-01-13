{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, PolyKinds, ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances, ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-type-defaults                    #-}
module Polynomial where
import           BaseTypes
import           Control.Lens
import           Data.List    (intercalate)
import           Data.Map     (Map)
import qualified Data.Map     as M
import           Data.Maybe
import           Data.Monoid
import           Data.Ord
import           Field
import           Prelude      hiding (lex)

-- | N-ary Monomial. IntMap contains degrees for each x_i.
type Monomial n = Vector n Int

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

-- | Total Ordering.
type Order n = Monomial n -> Monomial n -> Ordering

totalDegree :: Monomial n -> Int
totalDegree = foldrV (+) 0

-- | Lexicographical order. This *is* a monomial order.
lex :: MonomialOrder n
lex Nil Nil = EQ
lex (x :- xs) (y :- ys) = x `compare` y <> xs `lex` ys
lex _ _ = error "cannot happen"

-- | Reversed lexicographical order. This is *not* a monomial order.
revlex :: Order n
revlex (x :- xs) (y :- ys) = xs `revlex` ys <> y `compare` x
revlex Nil       Nil       = EQ
revlex _ _ = error "cannot happen!"

-- | Convert ordering into graded one.
graded :: Order n -> Order n
graded cmp xs ys = comparing totalDegree xs ys <> cmp xs ys

-- | Graded lexicographical order. This *is* a monomial order.
grlex :: MonomialOrder n
grlex = graded lex

-- | Graded reversed lexicographical order. This *is* a monomial order.
grevlex :: MonomialOrder n
grevlex = graded revlex

instance (Eq (Monomial n)) => Ord (Monomial n) where
  -- | We choose `grevlex` for the default monomial ordering (for tha sake of efficiency).
  compare = grevlex

-- | n-ary polynomial ring over some noetherian ring R.
newtype Polynomial r n = Polynomial { terms :: Map (Monomial n) r }

-- | Type-level constraint to check whether it forms polynomial ring or not.
type IsPolynomial r n = (NoetherianRing r, Eq (Monomial n), Sing n)

-- | coefficient for a degree.
coeff :: IsPolynomial r n => Monomial n -> Polynomial r n -> r
coeff d = M.findWithDefault zero d . terms

instance Wrapped (Map (Monomial n) r) (Map (Monomial m) q) (Polynomial r n) (Polynomial q m) where
    wrapped = iso Polynomial terms

-- | Polynomial addition, which automatically casts polynomial type.
(|+|) :: ( IsPolynomial r (Max n m), n :<= Max n m, m :<= Max n m)
      => Polynomial r n -> Polynomial r m -> Polynomial r (Max n m)
f |+| g = castPolynomial f .+. castPolynomial g

(|*|) :: ( IsPolynomial r (Max n m), n :<= Max n m, m :<= Max n m)
      => Polynomial r n -> Polynomial r m -> Polynomial r (Max n m)
f |*| g = castPolynomial f .*. castPolynomial g

castMonomial :: forall n m. (Sing m, n :<= m) => Monomial n -> Monomial m
castMonomial = fromList (sing :: SNat m) . toList

scastMonomial :: (n :<= m) => SNat m -> Monomial n -> Monomial m
scastMonomial snat = fromList snat . toList

castPolynomial :: (IsPolynomial r m, n :<= m) => Polynomial r n -> Polynomial r m
castPolynomial = unwrapped %~ M.mapKeys castMonomial

scastPolynomial :: (Eq (Monomial m), n :<= m) => SNat m -> Polynomial r n -> Polynomial r m
scastPolynomial m = unwrapped %~ M.mapKeys (scastMonomial m)

normalize :: IsPolynomial r n => Polynomial r n -> Polynomial r n
normalize = unwrapped %~ M.filter (/= zero)

instance IsPolynomial r n => Eq (Polynomial r n) where
  (normalize -> Polynomial f) == (normalize -> Polynomial g) = f == g

injectCoeff :: forall r n. (Sing n) => r -> Polynomial r n
injectCoeff r = Polynomial $ M.singleton (fromList (sing :: SNat n) []) r

-- | By Hilbert's finite basis theorem, a polynomial ring over a noetherian ring is also a noetherian ring.
instance IsPolynomial r n => NoetherianRing (Polynomial r n) where
  (Polynomial f) .+. (Polynomial g) = Polynomial $ M.unionWith (.+.) f g
  Polynomial (M.toList -> d1) .*.  Polynomial (M.toList -> d2) =
    let dic = [ (zipWithV (+) a b, r .*. r') | (a, r) <- d1, (b, r') <- d2 ]
    in Polynomial $ M.fromListWith (.+.) dic
  neg = unwrapped %~ fmap neg
  one  = injectCoeff one
  zero = Polynomial M.empty

instance (IsPolynomial r n, Show r) => Show (Polynomial r n) where
  show p@(Polynomial d)
      | p == zero = "0"
      | otherwise = intercalate " + " $ map showTerm $ M.toDescList d
    where
      showTerm (deg, c) = let cstr = if (c /= one || isConstantMonomial deg) then show c ++ " " else ""
                          in cstr ++ unwords (mapMaybe showDeg (zip [1..] $ toList deg))
      showDeg (n, p) | p == 0    = Nothing
                     | p == 1    = Just $ "X_" ++ show n
                     | otherwise = Just $ "X_" ++ show n ++ "^" ++ show p

isConstantMonomial :: (Eq a, Num a) => Vector n a -> Bool
isConstantMonomial v = all (== 0) $ toList v

-- | We provide Num instance to use trivial injection R into R[X].
--   Do not use signum or abs.
instance (IsPolynomial r n, Num r) => Num (Polynomial r n) where
  (+) = (.+.)
  (*) = (.*.)
  fromInteger = normalize . injectCoeff . fromInteger
  signum f = if f == zero then zero else injectCoeff 1
  abs = id
  negate = neg

varX :: forall r n. (NoetherianRing r, Sing n, One :<= n) => Polynomial r n
varX = Polynomial $ M.singleton (fromList (sing :: SNat n) [1]) one

var :: (NoetherianRing r, Sing m, S n :<= m) => SNat (S n) -> Polynomial r m
var vIndex = Polynomial $ M.singleton (fromList sing (buildIndex vIndex)) one

buildIndex :: SNat (S n) -> [Int]
buildIndex (SS SZ) = [1]
buildIndex (SS (SS n))  = 0 : buildIndex (SS n)

