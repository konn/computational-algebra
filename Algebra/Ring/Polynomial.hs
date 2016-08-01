{-# LANGUAGE ConstraintKinds, DataKinds, ExplicitNamespaces           #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs               #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, IncoherentInstances          #-}
{-# LANGUAGE LiberalTypeSynonyms, MultiParamTypeClasses               #-}
{-# LANGUAGE NoMonomorphismRestriction, PatternGuards, PolyKinds      #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, StandaloneDeriving      #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, TypeOperators             #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances, ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-type-defaults #-}
module Algebra.Ring.Polynomial
    ( module Algebra.Ring.Polynomial.Monomial,
      module Algebra.Ring.Polynomial.Class,
      Polynomial,
      transformMonomial,
      sPolynomial, monoize,
      castPolynomial, changeOrder, changeOrderProxy,
      changeMonomialOrder, changeMonomialOrderProxy,
      scastPolynomial, OrderedPolynomial(..), showPolynomialWithVars,
      showPolynomialWith, showRational, allVars, subst', homogenize, unhomogenize,
      normalize, injectCoeff, varX, getTerms, shiftR, orderedBy,
      CoeffView(..), maxNorm, oneNorm,
      genVars,
      mapCoeff,pDivModPoly,
      reversal, padeApprox,
      eval, evalUnivariate, evalOn,
      substUnivariate, diff, minpolRecurrent,content,pp,
      IsOrder(..), withPolynSingI
    )  where
import Algebra.Internal
import Algebra.Ring.Polynomial.Class
import Algebra.Ring.Polynomial.Monomial
import Algebra.Scalar
import Algebra.Wrapped

import           Control.Arrow
import           Control.DeepSeq
import           Control.Lens              hiding (assign, coerce)
import           Data.Function
import           Data.Hashable
import qualified Data.HashMap.Strict       as HM
import qualified Data.HashSet              as HS
import           Data.List                 (intercalate)
import           Data.Map                  (Map)
import qualified Data.Map.Strict           as M
import           Data.Maybe
import           Data.Ord
import qualified Data.Set                  as S
import           Data.Singletons.Prelude   (POrd (..))
import           Data.Type.Monomorphic
import           Data.Type.Natural         hiding ((:<=), max, one, zero)
import           Data.Type.Ordinal
import           Data.Vector.Sized         (Vector (..))
import qualified Data.Vector.Sized         as V
import           Numeric.Algebra           hiding (Order (..))
import           Numeric.Decidable.Units
import           Numeric.Decidable.Zero
import           Numeric.Domain.Euclidean  hiding (normalize)
import           Numeric.Field.Fraction
import qualified Numeric.Ring.Class        as NA
import           Numeric.Semiring.Integral (IntegralSemiring)
import           Prelude                   hiding (Rational, fromInteger, gcd,
                                            lex, negate, quot, recip, rem, sum,
                                            (*), (+), (-), (/), (^), (^^))
import qualified Prelude                   as P
import           Proof.Equational          (coerce, symmetry)

content :: Euclidean c => OrderedPolynomial c order n -> c
content = foldr (gcd . fst) zero . getTerms

pp :: (IsMonomialOrder ord, CoeffRing b, Euclidean b, SingI n)
   => OrderedPolynomial b ord n -> OrderedPolynomial b ord n
pp f = mapCoeff (`quot` content f) f

oneNorm :: (Normed b, Monoidal (Norm b)) => OrderedPolynomial b order n -> Norm b
oneNorm = sum . map (norm . fst) . getTerms

maxNorm :: Normed b => OrderedPolynomial b order n -> Norm b
maxNorm = maximum . map (norm . fst) . getTerms

monoize :: (DecidableZero r, Eq r, SingI n, Field r, IsMonomialOrder order)
        => OrderedPolynomial r order n -> OrderedPolynomial r order n
monoize f | isZero f  = zero
          | otherwise = recip (leadingCoeff f) .*. f

instance Hashable r => Hashable (OrderedPolynomial r ord n) where
  hashWithSalt salt poly = hashWithSalt salt $ getTerms poly

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

deriving instance (CoeffRing r, SingI n, IsOrder ord, Ord r, Ord (OrderedMonomial ord n))
               => Ord (OrderedPolynomial r ord n)

-- | n-ary polynomial ring over some noetherian ring R.
newtype OrderedPolynomial r order n = Polynomial { _terms :: Map (OrderedMonomial order n) r }
type Polynomial r = OrderedPolynomial r Grevlex

withPolynSingI :: IsOrder ord => OrderedPolynomial k ord m -> (SingI m => r) -> r
withPolynSingI (Polynomial f) r =
  case singInstance (V.sLength $ getMonomial $ fst $ M.findMin f) of
    SingInstance -> r

instance (SingI n, IsMonomialOrder ord, CoeffRing r) => IsPolynomial (OrderedPolynomial r ord n) where
  type Coefficient (OrderedPolynomial r ord n) = r
  type Arity       (OrderedPolynomial r ord n) = n

  sArity' = V.sLength . getMonomial . leadingMonomial

  monomials = HS.fromList . map getMonomial . S.toList . orderedMonomials
  {-# INLINE monomials #-}

  fromMonomial = fromOrderedMonomial . OrderedMonomial
  {-# INLINE fromMonomial #-}

  terms'    = HM.fromList . M.toList . M.mapKeys getMonomial . terms
  {-# INLINE terms' #-}

  liftMap mor poly = sum $ map (uncurry (.*) . (Scalar *** extractPower)) $ getTerms poly
    where
      extractPower =
        V.foldr (*) one . V.zipWithSame (\ o r -> pow  (mor o) (fromIntegral r)) ordVec . getMonomial
  {-# INLINE liftMap #-}

  toPolynomial' (r, deg) = toPolynomial (r, OrderedMonomial deg)
  {-# INLINE toPolynomial' #-}


ordVec :: forall n. SingI n => Vector (Ordinal n) n
ordVec = V.unsafeFromList' $ enumOrdinal (sing :: SNat n)

instance (SingI n, CoeffRing r, IsMonomialOrder ord)
      => IsOrderedPolynomial (OrderedPolynomial r ord n) where
-- | coefficient for a degree.
  type MOrder (OrderedPolynomial r ord n) = ord
  coeff d = M.findWithDefault zero d . terms
  terms = _terms

  orderedMonomials = M.keysSet . terms

  toPolynomial (c, deg) = polynomial $ M.singleton deg c
  polynomial dic = normalize $ Polynomial dic


  leadingTerm (Polynomial d) =
    case M.maxViewWithKey d of
      Just ((deg, c), _) -> (c, deg)
      Nothing -> (zero, one)

  leadingMonomial = snd . leadingTerm

  leadingCoeff = fst . leadingTerm

instance (SingI n, CoeffRing r, IsMonomialOrder order)
         => Wrapped (OrderedPolynomial r order n) where
  type Unwrapped (OrderedPolynomial r order n) = Map (OrderedMonomial order n) r
  _Wrapped' = iso terms polynomial

instance (SingI n, CoeffRing r, IsMonomialOrder ord
         ,SingI m, CoeffRing q, IsMonomialOrder ord'
         ,t ~ OrderedPolynomial q ord' m)
         => Rewrapped (OrderedPolynomial r ord n) t

castPolynomial :: (CoeffRing r, SingI n, SingI m,
                   IsMonomialOrder o, IsMonomialOrder o', (n :<= m) ~ 'True)
               => OrderedPolynomial r o n
               -> OrderedPolynomial r o' m
castPolynomial = _Wrapped %~ M.mapKeys castMonomial

scastPolynomial :: (IsMonomialOrder o, IsMonomialOrder o',
                    CoeffRing r, SingI n, (n :<= m) ~ 'True, SingI m)
                => SNat m -> OrderedPolynomial r o n -> OrderedPolynomial r o' m
scastPolynomial _ = castPolynomial

mapCoeff :: (SingI n, CoeffRing b, IsMonomialOrder ord)
         => (a -> b) -> OrderedPolynomial a ord n -> OrderedPolynomial b ord n
mapCoeff f (Polynomial dic) = polynomial $ M.map f dic

normalize :: (DecidableZero r, IsOrder order, Ring r, SingI n)
          => OrderedPolynomial r order n -> OrderedPolynomial r order n
normalize (Polynomial dic) =
  Polynomial $ M.filter (not . isZero) dic

instance (Eq r, IsOrder order, CoeffRing r, SingI n) => Eq (OrderedPolynomial r order n) where
  Polynomial f == Polynomial g = f == g

injectCoeff :: (DecidableZero r, SingI n) => r -> OrderedPolynomial r order n
injectCoeff r | isZero r  = Polynomial M.empty
              | otherwise = Polynomial $ M.singleton one r

-- -- | By Hilbert's finite basis theorem, a polynomial ring over a noetherian ring is also a noetherian ring.
-- instance (IsMonomialOrder order, CoeffRing r, SingI n) => Ring (OrderedPolynomial r order n) where
instance (IsMonomialOrder order, CoeffRing r, SingI n) => Ring (OrderedPolynomial r order n)
instance (IsMonomialOrder order, CoeffRing r, SingI n) => Rig (OrderedPolynomial r order n)
instance (IsMonomialOrder order, CoeffRing r, SingI n) => Group (OrderedPolynomial r order n) where
  negate (Polynomial dic) = Polynomial $ fmap negate dic
instance (IsMonomialOrder order, CoeffRing r, SingI n) => LeftModule Integer (OrderedPolynomial r order n) where
  n .* Polynomial dic = polynomial $ fmap (n .*) dic
instance (IsMonomialOrder order, CoeffRing r, SingI n) => RightModule Integer (OrderedPolynomial r order n) where
  (*.) = flip (.*)
instance (IsMonomialOrder order, CoeffRing r, SingI n) => Additive (OrderedPolynomial r order n) where
  (Polynomial f) + (Polynomial g) = polynomial $ M.unionWith (+) f g
instance (IsMonomialOrder order, CoeffRing r, SingI n) => Monoidal (OrderedPolynomial r order n) where
  zero = injectCoeff zero
instance (IsMonomialOrder order, CoeffRing r, SingI n) => LeftModule Natural (OrderedPolynomial r order n) where
  n .* Polynomial dic = polynomial $ fmap (n .*) dic
instance (IsMonomialOrder order, CoeffRing r, SingI n) => RightModule Natural (OrderedPolynomial r order n) where
  (*.) = flip (.*)
instance (IsMonomialOrder order, CoeffRing r, SingI n) => Unital (OrderedPolynomial r order n) where
  one = injectCoeff one
instance (IsMonomialOrder order, CoeffRing r, SingI n) => Multiplicative (OrderedPolynomial r order n) where
  Polynomial (M.toList -> d1) *  Polynomial (M.toList -> d2) =
    let dic = (one, zero) : [ (a * b, r * r') | (a, r) <- d1, (b, r') <- d2, not $ isZero (r * r')
              ]
    in polynomial $ M.fromListWith (+) dic
instance (IsMonomialOrder order, CoeffRing r, SingI n) => Semiring (OrderedPolynomial r order n) where
instance (IsMonomialOrder order, CoeffRing r, SingI n) => Commutative (OrderedPolynomial r order n) where
instance (IsMonomialOrder order, CoeffRing r, SingI n) => Abelian (OrderedPolynomial r order n) where
instance (IsMonomialOrder order, CoeffRing r, SingI n) => LeftModule (Scalar r) (OrderedPolynomial r order n) where
  Scalar r .* Polynomial dic = polynomial $ fmap (r*) dic
instance (IsMonomialOrder order, CoeffRing r, SingI n) => RightModule (Scalar r) (OrderedPolynomial r order n) where
  Polynomial dic *. Scalar r = polynomial $ fmap (r*) dic

instance (IsMonomialOrder ord, Characteristic r, SingI n, CoeffRing r)
      => Characteristic (OrderedPolynomial r ord n) where
  char _ = char (Proxy :: Proxy r)

instance {-# INCOHERENT #-} (SingI n, IsMonomialOrder order)
       => Show (OrderedPolynomial (Fraction Integer) order n) where
  show = showPolynomialWith False [(n, "X_"++ show n) | n <- [0..]] showRational

instance {-# OVERLAPPABLE #-} (CoeffRing r, SingI n, IsMonomialOrder order, Show r)
         =>  Show (OrderedPolynomial r order n) where
  show = showPolynomialWithVars [(n, "X_"++ show n) | n <- [0..]]

showPolynomialWithVars :: (CoeffRing a, Show a, SingI n, IsMonomialOrder ordering)
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

data CoeffView = Zero | Negative String | Positive String | Eps
                 deriving (Show, Eq, Ord)

showRational :: (Ord a, Show a, Euclidean a) => Fraction a -> CoeffView
showRational r | isZero r  = Zero
               | r >  zero = Positive $ formatRat r
               | otherwise = Negative $ formatRat $ negate  r
  where
    formatRat q | denominator q == one = show $ numerator q
                | otherwise            = show (numerator q) ++ "/" ++ show (denominator q) ++ " "

showPolynomialWith  :: (CoeffRing a, Show a, SingI n, IsMonomialOrder ordering)
                    => Bool -> [(Int, String)] -> (a -> CoeffView) -> OrderedPolynomial a ordering n -> String
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
instance (IsMonomialOrder order, CoeffRing r, SingI n, Num r) => Num (OrderedPolynomial r order n) where
  (+) = (Numeric.Algebra.+)
  (*) = (Numeric.Algebra.*)
  fromInteger = normalize . injectCoeff . P.fromInteger
  signum f = if isZero f then zero else injectCoeff 1
  abs = id
  negate = ((P.negate 1 :: Integer) .*)

instance (CoeffRing r, SingI n, IsMonomialOrder ord) => DecidableZero (OrderedPolynomial r ord n) where
  isZero (Polynomial d) = M.null d

instance (CoeffRing r, IsMonomialOrder ord, SingI n, IntegralSemiring r) => IntegralSemiring (OrderedPolynomial r ord n)
instance (Eq r, DecidableUnits r, DecidableZero r, Field r, IsMonomialOrder ord, IntegralSemiring r) => Euclidean (OrderedPolynomial r ord ('S 'Z)) where
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

pDivModPoly :: (Euclidean k, CoeffRing k, SingI n, IsMonomialOrder ord)
            => OrderedPolynomial k ord n -> OrderedPolynomial k ord n
            -> (OrderedPolynomial k ord n, OrderedPolynomial k ord n)
f0 `pDivModPoly` g =
  step (injectCoeff (pow (leadingCoeff g) (P.fromIntegral $ totalDegree' f0 P.- totalDegree' g + 1 :: Natural)) * f0) zero
  where
    lm = leadingMonomial g
    step p quo
        | isZero p = (quo, p)
        | lm `divs` leadingMonomial p =
            let q   = toPolynomial $ (leadingCoeff p `quot` leadingCoeff g, leadingMonomial p / leadingMonomial g)
            in step (p - (q * g)) (quo + q)
        | otherwise = (quo, p)

instance (CoeffRing r, IsMonomialOrder ord, DecidableUnits r, SingI n) => DecidableUnits (OrderedPolynomial r ord n) where
  isUnit f =
    let (lc, lm) = leadingTerm f
    in lm == one && isUnit lc
  recipUnit f | isUnit f  = injectCoeff <$> recipUnit (leadingCoeff f)
              | otherwise = Nothing

varX :: (CoeffRing r, SingI n, IsMonomialOrder order) => OrderedPolynomial r order ('S n)
varX = var OZ

-- | Substitute univariate polynomial using Horner's rule
substUnivariate :: (Module (Scalar r) b, Unital b, CoeffRing r, IsMonomialOrder order)
                => b -> OrderedPolynomial r order One -> b
substUnivariate u f =
  let n = totalDegree' f
  in foldr (\a b -> Scalar a .* one + b * u) (Scalar (coeff (OrderedMonomial $ fromIntegral n :- Nil) f) .* one)
           [ coeff (OrderedMonomial $ fromIntegral i :- Nil) f | i <- [0 .. n P.- 1] ]

evalUnivariate :: (CoeffRing b, IsMonomialOrder order) => b -> OrderedPolynomial b order ('S 'Z) -> b
evalUnivariate u f =
  let n = totalDegree' f
  in foldr1 (\a b -> a + b * u)  [ coeff (OrderedMonomial $ fromIntegral i :- Nil) f | i <- [0 .. n] ]

-- | Evaluate polynomial at some point.
eval :: (CoeffRing m, IsMonomialOrder order, SingI n)
     => Vector m n -> OrderedPolynomial m order n -> m
eval = substWith (*)

type family RepArgs (k :: Nat) (a :: *) (b :: *)
type instance RepArgs 'Z     a b = b
type instance RepArgs ('S n) a b = a -> RepArgs n a b

data NAry n a b where
  ValueN :: b -> NAry 'Z a b
  AppN   :: (a -> NAry n a b) -> NAry ('S n) a b

fromNAry :: NAry n a b -> RepArgs n a b
fromNAry (ValueN b) = b
fromNAry (AppN f)   = fromNAry . f

fromVecFun0 :: Sing k -> (Vector a k -> b) -> NAry k a b
fromVecFun0 SZ     f = ValueN $ f Nil
fromVecFun0 (SS n) f = AppN $ \a -> fromVecFun0 n (f . (a:-))

fromVecFun :: forall k a b. SingI k => (Vector a k -> b) -> NAry k a b
fromVecFun = fromVecFun0 (sing :: SNat k)

evalOn :: forall k a order . (SingI k, CoeffRing a, IsMonomialOrder order)
      => OrderedPolynomial a order k -> RepArgs k a a
evalOn p = fromNAry $ (fromVecFun (flip eval p) :: NAry k a a)

subst' :: (CoeffRing r, SingI n, IsMonomialOrder ord)
       => OrderedPolynomial r ord ('S n)
       -> OrderedPolynomial r ord ('S n)
       -> OrderedPolynomial r ord ('S n)
       -> OrderedPolynomial r ord ('S n)
subst' p val f
  | v <- leadingMonomial p
  , totalDegree v == 1 =
    substWith (.*.) (V.zipWithSame (\i mn -> if i == 0 then mn else val) (getMonomial v) allVars) f
  | otherwise = error "Not an "

allVars :: forall k ord n . (IsMonomialOrder ord, CoeffRing k, SingI n)
        => V.Vector (OrderedPolynomial k ord n) n
allVars = V.unsafeFromList' $ genVars (sing :: SNat n)

-- | Partially difference at (m+1)-th variable
diff :: forall n ord r. (CoeffRing r, SingI n, IsMonomialOrder ord)
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

sPolynomial :: (CoeffRing k, SingI n, Field k, IsMonomialOrder order)
            => OrderedPolynomial k order n
            -> OrderedPolynomial k order n -> OrderedPolynomial k order n
sPolynomial f g =
    let h = (one, lcmMonomial (leadingMonomial f) (leadingMonomial g))
    in toPolynomial (h `tryDiv` leadingTerm f) * f - toPolynomial (h `tryDiv` leadingTerm g) * g

changeMonomialOrder :: o' -> OrderedMonomial ord n -> OrderedMonomial o' n
changeMonomialOrder _ = OrderedMonomial . getMonomial

changeMonomialOrderProxy :: Proxy o' -> OrderedMonomial ord n -> OrderedMonomial o' n
changeMonomialOrderProxy _ = OrderedMonomial . getMonomial


changeOrder :: (CoeffRing k, Eq (Monomial n), IsMonomialOrder o, IsMonomialOrder o',  SingI n)
            => o' -> OrderedPolynomial k o n -> OrderedPolynomial k o' n
changeOrder _ = _Wrapped %~ M.mapKeys (OrderedMonomial . getMonomial)

changeOrderProxy :: (CoeffRing k, Eq (Monomial n), IsMonomialOrder o, IsMonomialOrder o',  SingI n)
            => Proxy o' -> OrderedPolynomial k o n -> OrderedPolynomial k o' n
changeOrderProxy _ = _Wrapped %~ M.mapKeys (OrderedMonomial . getMonomial)

getTerms :: OrderedPolynomial k order n -> [(k, OrderedMonomial order n)]
getTerms = map (snd &&& fst) . M.toDescList . _terms

transformMonomial :: (IsMonomialOrder o, CoeffRing k, SingI n, SingI m, DecidableZero k)
                  => (Monomial n -> Monomial m) -> OrderedPolynomial k o n -> OrderedPolynomial k o m
transformMonomial tr (Polynomial d) = polynomial $ M.mapKeys (OrderedMonomial . tr . getMonomial) d

orderedBy :: IsMonomialOrder o => OrderedPolynomial k o n -> o -> OrderedPolynomial k o n
p `orderedBy` _ = p

shiftR :: forall k r n ord. (Field r, CoeffRing r, SingI n, Ring r, IsMonomialOrder ord)
       => SNat k -> OrderedPolynomial r ord n -> OrderedPolynomial r ord (k :+: n)
shiftR k = withSingI (k %:+ (sing :: Sing n)) $
  case singInstance k of
    SingInstance -> transformMonomial (V.append (fromList k []))

genVars :: forall k o n. (Commutative k, CoeffRing k, SingI n, IsMonomialOrder o)
        => SNat n -> [OrderedPolynomial k o n]
genVars sn = map var $ enumOrdinal sn

-- | Calculate the homogenized polynomial of given one, with additional variable is the last variable.
homogenize :: forall k ord n. (Commutative k, CoeffRing k, SingI n, IsMonomialOrder ord)
           => OrderedPolynomial k ord n -> OrderedPolynomial k ord ('S n)
homogenize f =
  let g = substWith (.*.) (initSV allVars) f
      d = fromIntegral (totalDegree' g)
  in transformMonomial (\m -> m & ix maxBound .~ d - V.sum m) g

unhomogenize :: forall k ord n. (CoeffRing k, SingI n, IsMonomialOrder ord)
             => OrderedPolynomial k ord ('S n) -> OrderedPolynomial k ord n
unhomogenize f =
  substWith (.*.)
  (coerce (symmetry $ succAndPlusOneR (sing :: SNat n)) $ allVars `V.append` V.singleton one) f

initSV :: V.Vector a ('S n) -> V.Vector a n
initSV (_ :- Nil) = Nil
initSV (x :- xs@(_ :- _))  = x :- initSV xs

reversal :: (Commutative k, CoeffRing k, IsMonomialOrder o)
         => Int -> OrderedPolynomial k o One -> OrderedPolynomial k o One
reversal k = transformMonomial (\(i :- Nil) -> (k - i) :- Nil)

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
      d = fromIntegral $ max (1 + totalDegree' s) (totalDegree' t)
  in reversal d (recip (coeff one t) .*. t)
