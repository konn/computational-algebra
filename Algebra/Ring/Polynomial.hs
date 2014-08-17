{-# LANGUAGE CPP, ConstraintKinds, DataKinds, FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving       #-}
{-# LANGUAGE LiberalTypeSynonyms                   #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction           #-}
{-# LANGUAGE OverlappingInstances, PatternGuards, PolyKinds, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies, TypeOperators, TypeSynonymInstances          #-}
{-# LANGUAGE UndecidableInstances, ViewPatterns                         #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-type-defaults -fwarn-incomplete-patterns #-}
module Algebra.Ring.Polynomial
    ( Polynomial, Monomial, MonomialOrder, EliminationType, EliminationOrder
    , WeightedEliminationOrder, eliminationOrder, weightedEliminationOrder
    , lex, revlex, graded, grlex, grevlex, productOrder, productOrder', (*<), (>*)
    , transformMonomial, WeightProxy, weightOrder, totalDegree, totalDegree'
    , IsPolynomial, coeff, lcmMonomial, gcdMonomial, sPolynomial, polynomial, monoize
    , castMonomial, castPolynomial, toPolynomial, changeOrder, changeOrderProxy
    , changeMonomialOrder, changeMonomialOrderProxy, isRelativelyPrime
    , scastMonomial, scastPolynomial, OrderedPolynomial, showPolynomialWithVars
    , showPolynomialWith, showRational, allVars, subst', homogenize, unhomogenize
    , normalize, injectCoeff, varX, var, varMonom, getTerms, shiftR, orderedBy, monomials
    , divs, isPowerOf, tryDiv, fromList, Coefficient(..)
    , leadingTerm, leadingMonomial, leadingCoeff, genVars, sArity
    , OrderedMonomial(..), Grevlex(..), mapCoeff,pDivModPoly
    , Revlex(..), Lex(..), Grlex(..), Graded(..), reversal, padeApprox
    , ProductOrder (..), WeightOrder(..), subst, substWith, eval, evalUnivariate
    , substUnivariate, diff, minpolRecurrent
    , IsOrder(..), IsMonomialOrder)  where
import           Algebra.Internal
import           Algebra.Scalar
import           Control.Applicative       ((<$>))
import           Control.Arrow
import           Control.DeepSeq
import           Control.Lens              hiding (assign, coerce)
import           Data.Function
import           Data.Hashable
import           Data.List                 (intercalate)
import           Data.Map                  (Map)
import qualified Data.Map.Strict           as M
import           Data.Maybe
import           Data.Monoid
import           Data.Ord
import           Data.Type.Monomorphic
import           Data.Type.Natural         hiding (max, one, promote, zero)
import           Data.Type.Ordinal
import           Data.Vector.Sized         (Vector (..))
import qualified Data.Vector.Sized         as V
import           Numeric.Algebra           hiding (Order (..))
import           Numeric.Decidable.Units
import           Numeric.Decidable.Zero
import           Numeric.Domain.Class
import           Numeric.Domain.Euclidean  hiding (normalize)
import           Numeric.Field.Fraction
import           Numeric.Ring.Class
import qualified Numeric.Ring.Class        as NA
import           Numeric.Semiring.Integral (IntegralSemiring)
import           Prelude                   hiding (Rational, fromInteger, lex,
                                            negate, quot, recip, rem, sum, (*),
                                            (+), (-), (/), (^), (^^))
import qualified Prelude                   as P
import           Proof.Equational          (coerce, symmetry)
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
import Data.Singletons.Prelude (SList, Sing (SCons, SNil))
#else
import Data.Singletons (SList, Sing (SCons, SNil))
#endif

-- | N-ary Monomial. IntMap contains degrees for each x_i.
type Monomial (n :: Nat) = V.Vector Int n


-- | A wrapper for monomials with a certain (monomial) order.
newtype OrderedMonomial (ordering :: *) n = OrderedMonomial { getMonomial :: Monomial n }

makeLenses ''OrderedMonomial
makeWrapped ''OrderedMonomial

monoize :: (DecidableZero r, SingI n, Field r, IsMonomialOrder order)
        => OrderedPolynomial r order n -> OrderedPolynomial r order n
monoize f | isZero f  = zero
          | otherwise = recip (leadingCoeff f) .*. f

instance Hashable r => Hashable (OrderedPolynomial r ord n) where
  hashWithSalt salt poly = hashWithSalt salt $ getTerms poly

instance (NFData (Monomial n)) => NFData (OrderedMonomial ord n) where
  rnf (OrderedMonomial m) = rnf m `seq` ()

instance (NFData (Monomial n), NFData r) => NFData (OrderedPolynomial r ord n) where
  rnf (Polynomial dic) = rnf dic

instance Monomorphicable (V.Vector Int) where
  type MonomorphicRep (V.Vector Int) = [Int]
  promote []       = Monomorphic Nil
  promote (n : ns) =
    case promote ns of
      Monomorphic ns' -> Monomorphic (n :- ns')
  demote (Monomorphic Nil) = []
  demote (Monomorphic (n :- ns)) = n : demote (Monomorphic ns)

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

totalDegree' :: OrderedPolynomial k ord n -> Int
totalDegree' = maximum . (0:) . map (totalDegree . snd) . getTerms

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

-- | Monomial order which can be use to calculate n-th elimination ideal.
-- This should judge monomial to be bigger if it contains variables to eliminate.
class (IsMonomialOrder ord, SingI n) => EliminationType n ord
instance SingI n => EliminationType n Lex
instance (SingI n, IsMonomialOrder ord, IsMonomialOrder ord') => EliminationType n (ProductOrder n ord ord')
instance (IsMonomialOrder ord) => EliminationType Z (WeightOrder '[] ord)
instance (SingI ns, IsMonomialOrder ord, EliminationType n (WeightOrder ns ord))
    => EliminationType (S n) (WeightOrder (S Z ': ns) ord)

type EliminationOrder n = ProductOrder n Grevlex Grevlex

eliminationOrder :: SNat n -> EliminationOrder n
eliminationOrder n =
  case singInstance n of
    SingInstance -> ProductOrder n Grevlex Grevlex

weightedEliminationOrder :: SNat n -> WeightedEliminationOrder n Grevlex
weightedEliminationOrder n = WEOrder n (Proxy :: Proxy Grevlex)

type family EWeight (n :: Nat) :: [Nat]
type instance EWeight Z = '[]
type instance EWeight (S n) = One ': EWeight n

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
instance (Eq (Monomial n)) => Ord (Monomial n) where
  compare = grevlex

deriving instance (DecidableZero r, SingI n, IsOrder ord, Ring r, Ord r, Ord (OrderedMonomial ord n))
               => Ord (OrderedPolynomial r ord n)

-- | n-ary polynomial ring over some noetherian ring R.
newtype OrderedPolynomial r order n = Polynomial { terms :: Map (OrderedMonomial order n) r }
type Polynomial r = OrderedPolynomial r Grevlex

-- | Type-level constraint to check whether it forms polynomial ring or not.
type IsPolynomial r n = (Ring r, SingI n, DecidableZero r, Eq r)

-- | coefficient for a degree.
coeff :: (IsOrder order, Ring r, SingI n) => OrderedMonomial order n -> OrderedPolynomial r order n -> r
coeff d = M.findWithDefault zero d . terms

instance (SingI n, DecidableZero r, Ring r, IsOrder order)
         => Wrapped (OrderedPolynomial r order n) where
  type Unwrapped (OrderedPolynomial r order n) = Map (OrderedMonomial order n) r
  _Wrapped' = iso terms polynomial

instance (SingI n, DecidableZero r, Ring r, IsOrder ord
         ,SingI m, DecidableZero q, Ring q, IsOrder ord'
         ,t ~ OrderedPolynomial q ord' m)
         => Rewrapped (OrderedPolynomial r ord n) t

castMonomial :: (IsOrder o, IsOrder o', SingI m, n :<= m) => OrderedMonomial o n -> OrderedMonomial o' m
castMonomial = _Wrapped %~ fromList sing . V.toList

scastMonomial :: (n :<= m) => SNat m -> OrderedMonomial o n -> OrderedMonomial o m
scastMonomial sdim = _Wrapped %~ fromList sdim . V.toList

castPolynomial :: (Ring r, DecidableZero r, SingI n, SingI m, IsOrder o, IsOrder o', n :<= m)
               => OrderedPolynomial r o n
               -> OrderedPolynomial r o' m
castPolynomial = _Wrapped %~ M.mapKeys castMonomial

scastPolynomial :: (IsOrder o, IsOrder o', DecidableZero r, Ring r, SingI n, n :<= m, SingI m)
                => SNat m -> OrderedPolynomial r o n -> OrderedPolynomial r o' m
scastPolynomial _ = castPolynomial

mapCoeff :: (SingI n, Ring b, DecidableZero b, IsOrder ord)
         => (a -> b) -> OrderedPolynomial a ord n -> OrderedPolynomial b ord n
mapCoeff f (Polynomial dic) = polynomial $ M.map f dic

normalize :: (DecidableZero r, IsOrder order, Ring r, SingI n)
          => OrderedPolynomial r order n -> OrderedPolynomial r order n
normalize (Polynomial dic) =
  Polynomial $ M.filter (not . isZero) dic

instance (Eq r, IsOrder order, Ring r, DecidableZero r, SingI n) => Eq (OrderedPolynomial r order n) where
  Polynomial f == Polynomial g = f == g

injectCoeff :: (DecidableZero r, SingI n) => r -> OrderedPolynomial r order n
injectCoeff r | isZero r  = Polynomial M.empty
              | otherwise = Polynomial $ M.singleton one r

(>*) :: (IsMonomialOrder ord, Ring r, DecidableZero r, SingI n)
     => OrderedMonomial ord n -> OrderedPolynomial r ord n -> OrderedPolynomial r ord n
m >* f = toPolynomial (one, m) * f

(*<) :: (IsMonomialOrder ord, Ring r, DecidableZero r, SingI n)
     => OrderedPolynomial r ord n -> OrderedMonomial ord n -> OrderedPolynomial r ord n
(*<) = flip (>*)

infixl 7 *<, >*

-- -- | By Hilbert's finite basis theorem, a polynomial ring over a noetherian ring is also a noetherian ring.
-- instance (IsOrder order, Ring r, DecidableZero r, SingI n) => Ring (OrderedPolynomial r order n) where
instance (IsOrder order, Ring r, DecidableZero r, SingI n) => Ring (OrderedPolynomial r order n) where
instance (IsOrder order, Ring r, DecidableZero r, SingI n) => Rig (OrderedPolynomial r order n) where
instance (IsOrder order, Ring r, DecidableZero r, SingI n) => Group (OrderedPolynomial r order n) where
  negate (Polynomial dic) = Polynomial $ fmap negate dic
instance (IsOrder order, Ring r, DecidableZero r, SingI n) => LeftModule Integer (OrderedPolynomial r order n) where
  n .* Polynomial dic = polynomial $ fmap (n .*) dic
instance (IsOrder order, Ring r, DecidableZero r, SingI n) => RightModule Integer (OrderedPolynomial r order n) where
  (*.) = flip (.*)
instance (IsOrder order, Ring r, DecidableZero r, SingI n) => Additive (OrderedPolynomial r order n) where
  (Polynomial f) + (Polynomial g) = polynomial $ M.unionWith (+) f g
instance (IsOrder order, Ring r, DecidableZero r, SingI n) => Monoidal (OrderedPolynomial r order n) where
  zero = injectCoeff zero
instance (IsOrder order, Ring r, DecidableZero r, SingI n) => LeftModule Natural (OrderedPolynomial r order n) where
  n .* Polynomial dic = polynomial $ fmap (n .*) dic
instance (IsOrder order, Ring r, DecidableZero r, SingI n) => RightModule Natural (OrderedPolynomial r order n) where
  (*.) = flip (.*)
instance (IsOrder order, Ring r, DecidableZero r, SingI n) => Unital (OrderedPolynomial r order n) where
  one = injectCoeff one
instance (IsOrder order, Ring r, DecidableZero r, SingI n) => Multiplicative (OrderedPolynomial r order n) where
  Polynomial (M.toList -> d1) *  Polynomial (M.toList -> d2) =
    let dic = (one, zero) : [ (a * b, r * r') | (a, r) <- d1, (b, r') <- d2, not $ isZero (r * r')
              ]
    in polynomial $ M.fromListWith (+) dic
instance (IsOrder order, Ring r, DecidableZero r, SingI n) => Semiring (OrderedPolynomial r order n) where
instance (IsOrder order, Ring r, DecidableZero r, SingI n) => Commutative (OrderedPolynomial r order n) where
instance (IsOrder order, Ring r, DecidableZero r, SingI n) => Abelian (OrderedPolynomial r order n) where
instance (IsOrder order, Ring r, DecidableZero r, SingI n) => LeftModule (Scalar r) (OrderedPolynomial r order n) where
  Scalar r .* Polynomial dic = polynomial $ fmap (r*) dic
instance (IsOrder order, Ring r, DecidableZero r, SingI n) => RightModule (Scalar r) (OrderedPolynomial r order n) where
  Polynomial dic *. Scalar r = polynomial $ fmap (r*) dic

instance (IsOrder ord, Characteristic r, SingI n, DecidableZero r, Ring r)
      => Characteristic (OrderedPolynomial r ord n) where
  char _ = char (Proxy :: Proxy r)

instance (DecidableZero r, Ring r, SingI n, IsOrder order, Show r) => Show (OrderedPolynomial r order n) where
  show = showPolynomialWithVars [(n, "X_"++ show n) | n <- [0..]]


instance (SingI n, IsOrder order) => Show (OrderedPolynomial (Fraction Integer) order n) where
  show = showPolynomialWith False [(n, "X_"++ show n) | n <- [0..]] showRational

showPolynomialWithVars :: (DecidableZero a, Show a, SingI n, Ring a, IsOrder ordering)
                       => [(Int, String)] -> OrderedPolynomial a ordering n -> String
showPolynomialWithVars dic p0@(Polynomial d)
    | isZero p0 = "0"
    | otherwise = intercalate " + " $ mapMaybe showTerm $ M.toDescList d
    where
      showTerm (getMonomial -> deg, c)
          | isZero c = Nothing
          | otherwise =
              let cstr = if (not (isZero $ c - one) || isConstantMonomial deg)
                         then show c ++ " "
                         else if isZero (c - one) then ""
                              else if isZero (c + one)
                              then if any (not . isZero) (V.toList deg) then "-" else "-1"
                              else  ""
              in Just $ cstr ++ unwords (mapMaybe showDeg (zip [0..] $ V.toList deg))
      showDeg (n, p) | p == 0    = Nothing
                     | p == 1    = Just $ showVar n
                     | otherwise = Just $ showVar n ++ "^" ++ show p
      showVar n = fromMaybe ("X_" ++ show n) $ lookup n dic

data Coefficient = Zero | Negative String | Positive String | Eps
                 deriving (Show, Eq, Ord)

showRational :: (Ord a, Show a, Euclidean a) => Fraction a -> Coefficient
showRational r | isZero r  = Zero
               | r >  zero = Positive $ formatRat r
               | otherwise = Negative $ formatRat $ negate  r
  where
    formatRat q | denominator q == one = show $ numerator q
                | otherwise            = show (numerator q) ++ "/" ++ show (denominator q) ++ " "

showPolynomialWith  :: (DecidableZero a, Show a, SingI n, Ring a, IsOrder ordering)
                    => Bool -> [(Int, String)] -> (a -> Coefficient) -> OrderedPolynomial a ordering n -> String
showPolynomialWith useAst vDic showCoeff p0@(Polynomial d)
    | isZero p0 = "0"
    | otherwise  = catTerms $ mapMaybe procTerm $ M.toDescList d
    where
      ast | useAst    = "*"
          | otherwise = ""
      catTerms [] = "0"
      catTerms (x:xs) = concat $ showTerm True x : map (showTerm False) xs
      showTerm isLeading (Zero, _) = if isLeading then "0" else ""
      showTerm isLeading (Positive s, deg) = if isLeading then s ++ deg else " + " ++ s ++ deg
      showTerm isLeading (Negative s, deg) = if isLeading then '-' : s ++ deg else " - " ++ s ++ deg
      showTerm isLeading (Eps, deg) = if isLeading then deg else " + " ++ deg
      procTerm (getMonomial -> deg, c)
          | isZero c = Nothing
          | otherwise =
              let cKind = showCoeff c
                  cff | isConstantMonomial deg && isZero (c - one) = Positive "1"
                      | isConstantMonomial deg && isZero (c + one) = Negative "1"
                      | isZero (c - one) = Positive ""
                      | isZero (c + one) = Negative ""
                      | not (isConstantMonomial deg)              =
                        case cKind of
                          Negative c' -> Negative $ c' ++ ast
                          Positive c' -> Positive $ c' ++ ast
                          i          -> i
                      | otherwise                                 = cKind
                  catnate | useAst    = intercalate "*"
                          | otherwise = unwords
              in Just $ (cff, catnate (mapMaybe showDeg (zip [0..] $ V.toList deg)))
      showDeg (n, p) | p == 0    = Nothing
                     | p == 1    = Just $ showVar n
                     | otherwise = Just $ showVar n ++ "^" ++ show p
      showVar n = fromMaybe ("X_" ++ show n) $ lookup n vDic

isConstantMonomial :: (Eq a, Num a) => V.Vector a n -> Bool
isConstantMonomial v = all (== 0) $ V.toList v

-- | We provide Num instance to use trivial injection R into R[X].
--   Do not use signum or abs.
instance (IsMonomialOrder order, Ring r, DecidableZero r, SingI n, Num r) => Num (OrderedPolynomial r order n) where
  (+) = (Numeric.Algebra.+)
  (*) = (Numeric.Algebra.*)
  fromInteger = normalize . injectCoeff . P.fromInteger
  signum f = if isZero f then zero else injectCoeff 1
  abs = id
  negate = ((P.negate 1 :: Integer) .*)

instance (Ring r, DecidableZero r, SingI n, IsOrder ord) => DecidableZero (OrderedPolynomial r ord n) where
  isZero (Polynomial d) = M.null d

instance (DecidableZero r, Ring r, IsOrder ord, SingI n, IntegralSemiring r) => IntegralSemiring (OrderedPolynomial r ord n)
instance (Eq r, DecidableUnits r, DecidableZero r, Field r, IsMonomialOrder ord, IntegralSemiring r) => Euclidean (OrderedPolynomial r ord (S Z)) where
  f0 `divide` g = step f0 zero
    where
      lm = leadingMonomial g
      step p quo
          | isZero p = (quo, p)
          | lm `divs` leadingMonomial p =
              let q   = toPolynomial $ leadingTerm p `tryDiv` leadingTerm g
              in step (p - (q * g)) (quo + q)
          | otherwise = (quo, p)
  degree f | isZero f  = Nothing
           | otherwise = Just $ P.fromIntegral $ totalDegree' f
  splitUnit f
    | isZero f = (zero, f)
    | otherwise = let lc = leadingCoeff f
                  in (injectCoeff lc, injectCoeff (recip lc) * f)

pDivModPoly :: (Euclidean k, SingI n, IsOrder ord)
            => OrderedPolynomial k ord n -> OrderedPolynomial k ord n
            -> (OrderedPolynomial k ord n, OrderedPolynomial k ord n)
f0 `pDivModPoly` g =
  step (injectCoeff (pow (leadingCoeff g) (P.fromIntegral $ totalDegree' f0 - totalDegree' g + 1 :: Natural)) * f0) zero
  where
    lm = leadingMonomial g
    step p quo
        | isZero p = (quo, p)
        | lm `divs` leadingMonomial p =
            let q   = toPolynomial $ (leadingCoeff p `quot` leadingCoeff g, leadingMonomial p / leadingMonomial g)
            in step (p - (q * g)) (quo + q)
        | otherwise = (quo, p)

instance (Ring r, DecidableZero r, IsOrder ord, DecidableUnits r, SingI n) => DecidableUnits (OrderedPolynomial r ord n) where
  isUnit f =
    let (lc, lm) = leadingTerm f
    in lm == one && isUnit lc
  recipUnit f | isUnit f  = injectCoeff <$> recipUnit (leadingCoeff f)
              | otherwise = Nothing

varX :: (DecidableZero r, Ring r, SingI n, IsOrder order) => OrderedPolynomial r order (S n)
varX = var OZ

var :: (DecidableZero r, Ring r, SingI m, IsOrder order) => Ordinal m -> OrderedPolynomial r order m
var vIndex = polynomial $ M.singleton (OrderedMonomial $ varMonom vIndex) one

varMonom :: forall n. SingI n => Ordinal n -> Monomial n
varMonom OZ =
  case sing :: SNat n of
    SS n -> 1 :- V.replicate n 0
    _   -> error "impossible"
varMonom (OS n) =
  case sing :: SNat n of
    SS sn -> case singInstance sn of SingInstance -> 0 :- varMonom n
    _    -> error "impossible"

toPolynomial :: (IsOrder order, Ring r, DecidableZero r, SingI n) => (r, OrderedMonomial order n) -> OrderedPolynomial r order n
toPolynomial (c, deg) = polynomial $ M.singleton deg c

polynomial :: (SingI n, DecidableZero r, Ring r, IsOrder order) => Map (OrderedMonomial order n) r -> OrderedPolynomial r order n
polynomial dic = normalize $ Polynomial dic

leadingTerm :: (IsOrder order, Ring r, DecidableZero r, SingI n)
            => OrderedPolynomial r order n -> (r, OrderedMonomial order n)
leadingTerm (Polynomial d) =
  case M.maxViewWithKey d of
    Just ((deg, c), _) -> (c, deg)
    Nothing -> (zero, one)

leadingMonomial :: (IsOrder order, Ring r, DecidableZero r, SingI n)
                => OrderedPolynomial r order n
                -> OrderedMonomial order n
leadingMonomial = snd . leadingTerm

leadingCoeff :: (IsOrder order, Ring r, DecidableZero r, SingI n) => OrderedPolynomial r order n -> r
leadingCoeff = fst . leadingTerm

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

lcmMonomial :: OrderedMonomial ord n -> OrderedMonomial ord n -> OrderedMonomial ord n
lcmMonomial (OrderedMonomial m) (OrderedMonomial n) = OrderedMonomial $ V.zipWithSame max m n

gcdMonomial :: OrderedMonomial ord n -> OrderedMonomial ord n -> OrderedMonomial ord n
gcdMonomial (OrderedMonomial m) (OrderedMonomial n) = OrderedMonomial $ V.zipWithSame P.min m n

-- | Substitute univariate polynomial using Horner's rule
substUnivariate :: (Module (Scalar r) b, Unital b, Ring r, IsOrder order)
                => b -> OrderedPolynomial r order One -> b
substUnivariate u f =
  let n = totalDegree' f
  in foldr (\a b -> Scalar a .* one + b * u) (Scalar (coeff (OrderedMonomial $ n :- Nil) f) .* one)
           [ coeff (OrderedMonomial $ i :- Nil) f | i <- [0 .. n-1] ]

evalUnivariate :: (Ring b, IsOrder order) => b -> OrderedPolynomial b order ('S 'Z) -> b
evalUnivariate u f =
  let n = totalDegree' f
  in foldr1 (\a b -> a + b * u)  [ coeff (OrderedMonomial $ i :- Nil) f | i <- [0 .. n] ]

subst :: (Module r a, Ring a, Ring r, SingI n) => V.Vector a n -> OrderedPolynomial r order n -> a
subst assign poly = sum $ map (uncurry (.*) . second extractPower) $ getTerms poly
  where
    extractPower = V.foldr (*) one . V.zipWithSame pow assign .
                   V.map (P.fromIntegral :: Int -> Natural) . getMonomial

-- | Evaluate polynomial at some point.
eval :: (Monoidal m, Unital m) => Vector m n -> OrderedPolynomial m order n -> m
eval = substWith (*)

substWith :: (Unital c, Monoidal m) => (d -> c -> m) -> V.Vector c n -> OrderedPolynomial d order n -> m
substWith o assign poly = sum $ map (uncurry o . second extractPower) $ getTerms poly
  where
    extractPower = V.foldr (*) one . V.zipWithSame pow assign .
                   V.map (P.fromIntegral :: Int -> Natural) . getMonomial

subst' :: (Ring r, DecidableZero r, SingI n, IsOrder ord)
       => OrderedPolynomial r ord (S n)
       -> OrderedPolynomial r ord (S n)
       -> OrderedPolynomial r ord (S n)
       -> OrderedPolynomial r ord (S n)
subst' p val f
  | v <- leadingMonomial p
  , totalDegree v == 1 =
    substWith (.*.) (V.zipWithSame (\i mn -> if i == 0 then mn else val) (getMonomial v) allVars) f
  | otherwise = error "Not an "

allVars :: forall k ord n . (IsOrder ord, Ring k, DecidableZero k, SingI n)
        => V.Vector (OrderedPolynomial k ord n) n
allVars = V.unsafeFromList' $ genVars (sing :: SNat n)

-- | Partially difference at (m+1)-th variable
diff :: forall n ord r. (DecidableZero r, Ring r, SingI n, IsMonomialOrder ord)
     => Ordinal n -> OrderedPolynomial r ord n -> OrderedPolynomial r ord n
diff mthVar = _Wrapped %~ M.mapKeysWith (+) (_Wrapped %~ dropDegree)
                         . M.mapMaybeWithKey (\k c -> if (V.sIndex mthVar (getMonomial k) > 0)
                                                      then Just $ c * NA.fromIntegral (V.sIndex mthVar (getMonomial k))
                                                      else Nothing)
  where
    dropDegree = updateNth mthVar (max 0 . pred)

updateNth :: Ordinal n -> (a -> a) -> V.Vector a n -> V.Vector a n
updateNth OZ     f (a :- as) = f a :- as
updateNth (OS n) f (a :- b :- bs) = a :- updateNth n f (b :- bs)
updateNth _      _ _              = bugInGHC

sPolynomial :: (Ring k, DecidableZero k, SingI n, Field k, IsOrder order)
            => OrderedPolynomial k order n
            -> OrderedPolynomial k order n -> OrderedPolynomial k order n
sPolynomial f g =
    let h = (one, lcmMonomial (leadingMonomial f) (leadingMonomial g))
    in toPolynomial (h `tryDiv` leadingTerm f) * f - toPolynomial (h `tryDiv` leadingTerm g) * g

changeMonomialOrder :: o' -> OrderedMonomial ord n -> OrderedMonomial o' n
changeMonomialOrder _ = OrderedMonomial . getMonomial

changeMonomialOrderProxy :: Proxy o' -> OrderedMonomial ord n -> OrderedMonomial o' n
changeMonomialOrderProxy _ = OrderedMonomial . getMonomial


changeOrder :: (DecidableZero k, Ring k, Eq (Monomial n), IsOrder o, IsOrder o',  SingI n)
            => o' -> OrderedPolynomial k o n -> OrderedPolynomial k o' n
changeOrder _ = _Wrapped %~ M.mapKeys (OrderedMonomial . getMonomial)

changeOrderProxy :: (DecidableZero k, Ring k, Eq (Monomial n), IsOrder o, IsOrder o',  SingI n)
            => Proxy o' -> OrderedPolynomial k o n -> OrderedPolynomial k o' n
changeOrderProxy _ = _Wrapped %~ M.mapKeys (OrderedMonomial . getMonomial)

getTerms :: OrderedPolynomial k order n -> [(k, OrderedMonomial order n)]
getTerms = map (snd &&& fst) . M.toDescList . terms

monomials :: OrderedPolynomial a order n -> [OrderedMonomial order n]
monomials = M.keys . terms

transformMonomial :: (IsOrder o, Ring k, SingI n, SingI m, DecidableZero k)
                  => (Monomial n -> Monomial m) -> OrderedPolynomial k o n -> OrderedPolynomial k o m
transformMonomial tr (Polynomial d) = polynomial $ M.mapKeys (OrderedMonomial . tr . getMonomial) d

orderedBy :: IsOrder o => OrderedPolynomial k o n -> o -> OrderedPolynomial k o n
p `orderedBy` _ = p

shiftR :: forall k r n ord. (Field r, Ring r, DecidableZero r, SingI n, IsPolynomial r (k :+: n), IsOrder ord)
       => SNat k -> OrderedPolynomial r ord n -> OrderedPolynomial r ord (k :+: n)
shiftR k =
  case singInstance k of
    SingInstance -> transformMonomial (V.append (fromList k []))

genVars :: forall k o n. (Ring k, DecidableZero k, SingI n, IsOrder o)
        => SNat n -> [OrderedPolynomial k o n]
genVars sn = map var $ enumOrdinal sn

-- | Calculate the homogenized polynomial of given one, with additional variable is the last variable.
homogenize :: forall k ord n. (Ring k, DecidableZero k, SingI n, IsMonomialOrder ord)
           => OrderedPolynomial k ord n -> OrderedPolynomial k ord (S n)
homogenize f =
  let g = substWith (.*.) (initSV allVars) f
      d = totalDegree' g
  in transformMonomial (\m -> m & ix maxBound .~ d - V.sum m) g

unhomogenize :: forall k ord n. (Ring k, DecidableZero k, SingI n, IsMonomialOrder ord)
             => OrderedPolynomial k ord (S n) -> OrderedPolynomial k ord n
unhomogenize f =
  substWith (.*.)
  (coerce (symmetry $ sAndPlusOne (sing :: SNat n)) $ allVars `V.append` V.singleton one) f

initSV :: V.Vector a (S n) -> V.Vector a n
initSV (_ :- Nil) = Nil
initSV (x :- xs@(_ :- _))  = x :- initSV xs

reversal :: (Ring k, DecidableZero k, IsOrder o)
         => Int -> OrderedPolynomial k o One -> OrderedPolynomial k o One
reversal k = transformMonomial (\(i :- Nil) -> (k - i) :- Nil)

sArity :: OrderedPolynomial k ord n -> SNat n
sArity (Polynomial dic) = V.sLength $ getMonomial $ fst $ M.findMin dic

padeApprox :: (Field r, Eq r, DecidableUnits r, DecidableZero r, IntegralSemiring r,
              IsMonomialOrder order)
           => Natural -> Natural -> OrderedPolynomial r order One
           -> (OrderedPolynomial r order One, OrderedPolynomial r order One)
padeApprox k nmk g =
  let (r, _, t) = last $ filter ((< P.fromIntegral k) . totalDegree' . view _1) $ euclid (pow varX (k+nmk)) g
  in (r, t)


minpolRecurrent :: forall k. (Eq k, IntegralSemiring k, DecidableUnits k, DecidableZero k, Field k)
                => Natural -> [k] -> Polynomial k One
minpolRecurrent n xs =
  let h = sum $ zipWith (\a b -> injectCoeff a * b) xs [pow varX i | i <- [0.. pred (2 * n)]]
          :: Polynomial k One
      (s, t) = padeApprox n n h
      d = max (1 + totalDegree' s) (totalDegree' t)
  in reversal d (recip (coeff one t) .*. t)
