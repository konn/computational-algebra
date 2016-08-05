{-# LANGUAGE ConstraintKinds, DataKinds, ExplicitNamespaces           #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs               #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, IncoherentInstances          #-}
{-# LANGUAGE LiberalTypeSynonyms, MultiParamTypeClasses               #-}
{-# LANGUAGE NoMonomorphismRestriction, PatternGuards, PolyKinds      #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, StandaloneDeriving      #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, TypeOperators             #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances, ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-type-defaults #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
module Algebra.Ring.Polynomial
    ( module Algebra.Ring.Polynomial.Monomial,
      module Algebra.Ring.Polynomial.Class,
      Polynomial,
      transformMonomial,
      castPolynomial, changeOrder, changeOrderProxy,
      scastPolynomial, OrderedPolynomial(..),
      allVars, subst', homogenize, unhomogenize,
      normalize, varX, getTerms, shiftR, orderedBy,
      mapCoeff, reversal, padeApprox,
      eval, evalUnivariate,
      substUnivariate, diff, minpolRecurrent,
      IsOrder(..)
    )  where
import Algebra.Internal
import Algebra.Ring.Polynomial.Class
import Algebra.Ring.Polynomial.Monomial
import Algebra.Scalar

import           Control.Arrow
import           Control.DeepSeq           (NFData)
import           Control.Lens              hiding (assign)
import qualified Data.Foldable             as F
import           Data.Function
import           Data.Hashable
import qualified Data.HashSet              as HS
import           Data.List                 (intercalate)
import           Data.Map                  (Map)
import qualified Data.Map.Strict           as M
import           Data.Maybe
import           Data.Ord
import qualified Data.Set                  as Set
import           Data.Singletons.Prelude   (POrd (..))
import qualified Data.Sized.Builtin        as S
import           Data.Type.Ordinal
import           Numeric.Algebra           hiding (Order (..))
import           Numeric.Decidable.Units
import           Numeric.Decidable.Zero
import           Numeric.Domain.Euclidean  hiding (normalize)
import qualified Numeric.Ring.Class        as NA
import           Numeric.Semiring.Integral (IntegralSemiring)
import           Prelude                   hiding (Rational, fromInteger, gcd,
                                            lex, negate, quot, recip, rem, sum,
                                            (*), (+), (-), (/), (^), (^^))
import qualified Prelude                   as P
import           Proof.Equational          (symmetry)

instance Hashable r => Hashable (OrderedPolynomial r ord n) where
  hashWithSalt salt poly = hashWithSalt salt $ getTerms poly

deriving instance (CoeffRing r, IsOrder n ord, Ord r) => Ord (OrderedPolynomial r ord n)

-- | n-ary polynomial ring over some noetherian ring R.
newtype OrderedPolynomial r order n = Polynomial { _terms :: Map (OrderedMonomial order n) r }
                                    deriving (NFData)
type Polynomial r = OrderedPolynomial r Grevlex

instance (KnownNat n, IsMonomialOrder n ord, CoeffRing r) => IsPolynomial (OrderedPolynomial r ord n) where
  type Coefficient (OrderedPolynomial r ord n) = r
  type Arity       (OrderedPolynomial r ord n) = n

  injectCoeff r | isZero r  = Polynomial M.empty
                | otherwise = Polynomial $ M.singleton one r
  {-# INLINE injectCoeff #-}

  sArity' = sizedLength . getMonomial . leadingMonomial
  {-# INLINE sArity' #-}

  mapCoeff' = mapCoeff
  {-# INLINE mapCoeff' #-}

  monomials = HS.fromList . map getMonomial . Set.toList . orderedMonomials
  {-# INLINE monomials #-}

  fromMonomial m = Polynomial $ M.singleton (OrderedMonomial m) one
  {-# INLINE fromMonomial #-}

  toPolynomial' (r, m) = Polynomial $ M.singleton (OrderedMonomial m) r
  {-# INLINE toPolynomial' #-}

  polynomial' dic = normalize $ Polynomial $ M.mapKeys OrderedMonomial dic
  {-# INLINE polynomial' #-}

  terms'    = M.mapKeys getMonomial . terms
  {-# INLINE terms' #-}

  liftMap mor poly = sum $ map (uncurry (.*) . (Scalar *** extractPower)) $ getTerms poly
    where
      extractPower =
        P.foldr (*) one . zipWithSame (\ o r -> pow  (mor o) (fromIntegral r)) ordVec . getMonomial
  {-# INLINE liftMap #-}




ordVec :: forall n. KnownNat n => Vector (Ordinal n) n
ordVec = unsafeFromList' $ enumOrdinal (sing :: SNat n)

instance (KnownNat n, CoeffRing r, IsMonomialOrder n ord)
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

instance (KnownNat n, CoeffRing r, IsMonomialOrder n order)
         => Wrapped (OrderedPolynomial r order n) where
  type Unwrapped (OrderedPolynomial r order n) = Map (OrderedMonomial order n) r
  _Wrapped' = iso terms polynomial

instance (KnownNat n, CoeffRing r, IsMonomialOrder n ord, t ~ OrderedPolynomial q ord' m)
         => Rewrapped (OrderedPolynomial r ord n) t

castPolynomial :: (CoeffRing r, KnownNat n, KnownNat m,
                   IsMonomialOrder n o, IsMonomialOrder m o')
               => OrderedPolynomial r o n
               -> OrderedPolynomial r o' m
castPolynomial = _Wrapped %~ M.mapKeys castMonomial

scastPolynomial :: (IsMonomialOrder n o, IsMonomialOrder m o', KnownNat m,
                    CoeffRing r, KnownNat n)
                => SNat m -> OrderedPolynomial r o n -> OrderedPolynomial r o' m
scastPolynomial _ = castPolynomial

mapCoeff :: (KnownNat n, CoeffRing b, IsMonomialOrder n ord)
         => (a -> b) -> OrderedPolynomial a ord n -> OrderedPolynomial b ord n
mapCoeff f (Polynomial dic) = polynomial $ M.map f dic

normalize :: (DecidableZero r)
          => OrderedPolynomial r order n -> OrderedPolynomial r order n
normalize (Polynomial dic) =
  Polynomial $ M.filter (not . isZero) dic

instance (Eq r) => Eq (OrderedPolynomial r order n) where
  Polynomial f == Polynomial g = f == g

-- -- | By Hilbert's finite basis theorem, a polynomial ring over a noetherian ring is also a noetherian ring.
-- instance (IsMonomialOrder order, CoeffRing r, KnownNat n) => Ring (OrderedPolynomial r order n) where
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Ring (OrderedPolynomial r order n)
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Rig (OrderedPolynomial r order n)
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Group (OrderedPolynomial r order n) where
  negate (Polynomial dic) = Polynomial $ fmap negate dic
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => LeftModule Integer (OrderedPolynomial r order n) where
  n .* Polynomial dic = polynomial $ fmap (n .*) dic
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => RightModule Integer (OrderedPolynomial r order n) where
  (*.) = flip (.*)
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Additive (OrderedPolynomial r order n) where
  (Polynomial f) + (Polynomial g) = polynomial $ M.unionWith (+) f g
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Monoidal (OrderedPolynomial r order n) where
  zero = injectCoeff zero
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => LeftModule Natural (OrderedPolynomial r order n) where
  n .* Polynomial dic = polynomial $ fmap (n .*) dic
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => RightModule Natural (OrderedPolynomial r order n) where
  (*.) = flip (.*)
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Unital (OrderedPolynomial r order n) where
  one = injectCoeff one
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Multiplicative (OrderedPolynomial r order n) where
  Polynomial (M.toList -> d1) *  Polynomial (M.toList -> d2) =
    let dic = (one, zero) : [ (a * b, r * r') | (a, r) <- d1, (b, r') <- d2, not $ isZero (r * r')
              ]
    in polynomial $ M.fromListWith (+) dic
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Semiring (OrderedPolynomial r order n) where
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Commutative (OrderedPolynomial r order n) where
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Abelian (OrderedPolynomial r order n) where
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => LeftModule (Scalar r) (OrderedPolynomial r order n) where
  Scalar r .* Polynomial dic = polynomial $ fmap (r*) dic
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => RightModule (Scalar r) (OrderedPolynomial r order n) where
  Polynomial dic *. Scalar r = polynomial $ fmap (r*) dic

instance (IsMonomialOrder n ord, Characteristic r, KnownNat n, CoeffRing r)
      => Characteristic (OrderedPolynomial r ord n) where
  char _ = char (Proxy :: Proxy r)

instance (KnownNat n, CoeffRing r, IsMonomialOrder n order, PrettyCoeff r)
       => Show (OrderedPolynomial r order n) where
  showsPrec = showsPolynomialWith $ generate sing (\i -> "X_" ++ show (fromEnum i))

showPolynomialWithVars :: (CoeffRing a, Show a, KnownNat n, IsMonomialOrder n ordering)
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
                              then if any (not . isZero) (F.toList deg) then "-" else "-1"
                              else  ""
              in Just $ cstr ++ unwords (mapMaybe showDeg (zip [0..] $ F.toList deg))
      showDeg (n, p) | p == 0    = Nothing
                     | p == 1    = Just $ showVar n
                     | otherwise = Just $ showVar n ++ "^" ++ show p
      showVar n = fromMaybe ("X_" ++ show n) $ lookup n dic

isConstantMonomial :: (Eq a, Num a) => Vector a n -> Bool
isConstantMonomial v = all (== 0) $ F.toList v

-- | We provide Num instance to use trivial injection R into R[X].
--   Do not use signum or abs.
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n, Num r)
      => Num (OrderedPolynomial r order n) where
  (+) = (Numeric.Algebra.+)
  (*) = (Numeric.Algebra.*)
  fromInteger = normalize . injectCoeff . P.fromInteger
  signum f = if isZero f then zero else injectCoeff 1
  abs = id
  negate = ((P.negate 1 :: Integer) .*)

instance (CoeffRing r, KnownNat n, IsMonomialOrder n ord) => DecidableZero (OrderedPolynomial r ord n) where
  isZero (Polynomial d) = M.null d

instance (CoeffRing r, IsMonomialOrder 1 ord, IntegralSemiring r)
      => IntegralSemiring (OrderedPolynomial r ord 1)
instance (Eq r, DecidableUnits r, DecidableZero r, Field r, IsMonomialOrder 1 ord, IntegralSemiring r) => Euclidean (OrderedPolynomial r ord 1) where
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

instance (CoeffRing r, IsMonomialOrder n ord, DecidableUnits r, KnownNat n) => DecidableUnits (OrderedPolynomial r ord n) where
  isUnit f =
    let (lc, lm) = leadingTerm f
    in lm == one && isUnit lc
  recipUnit f | isUnit f  = injectCoeff <$> recipUnit (leadingCoeff f)
              | otherwise = Nothing

varX :: forall r n order. (CoeffRing r, KnownNat n, IsMonomialOrder n order, (0 :< n) ~ 'True)
     => OrderedPolynomial r order n
varX = var OZ

-- | Substitute univariate polynomial using Horner's rule
substUnivariate :: (Module (Scalar r) b, Unital b, CoeffRing r, IsMonomialOrder 1 order)
                => b -> OrderedPolynomial r order 1 -> b
substUnivariate u f =
  let n = totalDegree' f
  in foldr (\a b -> Scalar a .* one + b * u) (Scalar (coeff (OrderedMonomial $ singleton $ fromIntegral n) f) .* one)
           [ coeff (OrderedMonomial $ singleton $ fromIntegral i) f | i <- [0 .. n P.- 1] ]

evalUnivariate :: (CoeffRing b, IsMonomialOrder 1 order) => b -> OrderedPolynomial b order 1 -> b
evalUnivariate u f =
  let n = totalDegree' f
  in if n == 0
     then coeff one f
     else foldr1 (\a b -> a + b * u)  [ coeff (OrderedMonomial $ singleton $ fromIntegral i) f | i <- [0 .. n] ]

-- | Evaluate polynomial at some point.
eval :: (CoeffRing r, IsMonomialOrder n order, KnownNat n)
     => Vector r n -> OrderedPolynomial r order n -> r
eval = substWith (*)

-- evalOn :: forall k a order . (SingI k, CoeffRing a, IsMonomialOrder order)
--       => OrderedPolynomial a order k -> RepArgs k a a
-- evalOn p = fromNAry $ (fromVecFun (flip eval p) :: NAry k a a)

subst' :: (CoeffRing r, KnownNat n, IsMonomialOrder n ord, (1 :<= n) ~  'True)
       => OrderedPolynomial r ord n
       -> OrderedPolynomial r ord n
       -> OrderedPolynomial r ord n
       -> OrderedPolynomial r ord n
subst' p val f
  | v <- leadingMonomial p
  , totalDegree v == 1 =
    substWith (.*.) (zipWithSame (\i mn -> if i == 0 then mn else val) (getMonomial v) allVars) f
  | otherwise = error "Not an "

allVars :: forall k ord n . (IsMonomialOrder n ord, CoeffRing k, KnownNat n)
        => Vector (OrderedPolynomial k ord n) n
allVars = unsafeFromList' vars

-- | Partially difference at (m+1)-th variable
diff :: forall n ord r. (CoeffRing r, KnownNat n, IsMonomialOrder n ord)
     => Ordinal n -> OrderedPolynomial r ord n -> OrderedPolynomial r ord n
diff mthVar = _Wrapped %~ M.mapKeysWith (+) (_Wrapped %~ dropDegree)
                         . M.mapMaybeWithKey (\k c -> if (sIndex mthVar (getMonomial k) > 0)
                                                      then Just $ c * NA.fromIntegral (sIndex mthVar (getMonomial k))
                                                      else Nothing)
  where
    dropDegree = ix mthVar %~ (max 0 . pred)

changeOrder :: (CoeffRing k, Eq (Monomial n), IsMonomialOrder n o, IsMonomialOrder n o',  KnownNat n)
            => o' -> OrderedPolynomial k o n -> OrderedPolynomial k o' n
changeOrder _ = _Wrapped %~ M.mapKeys (OrderedMonomial . getMonomial)

changeOrderProxy :: (CoeffRing k, Eq (Monomial n), IsMonomialOrder n o,
                     IsMonomialOrder n o',  KnownNat n)
                 => Proxy o' -> OrderedPolynomial k o n -> OrderedPolynomial k o' n
changeOrderProxy _ = _Wrapped %~ M.mapKeys (OrderedMonomial . getMonomial)

getTerms :: OrderedPolynomial k order n -> [(k, OrderedMonomial order n)]
getTerms = map (snd &&& fst) . M.toDescList . _terms

transformMonomial :: (IsMonomialOrder m o, CoeffRing k, KnownNat m)
                  => (Monomial n -> Monomial m) -> OrderedPolynomial k o n -> OrderedPolynomial k o m
transformMonomial tr (Polynomial d) =
  polynomial $ M.mapKeys (OrderedMonomial . tr . getMonomial) d

orderedBy :: OrderedPolynomial k o n -> o -> OrderedPolynomial k o n
p `orderedBy` _ = p

shiftR :: forall k r n ord. (CoeffRing r, KnownNat n, IsMonomialOrder n ord,
                             IsMonomialOrder (k + n) ord)
       => SNat k -> OrderedPolynomial r ord n -> OrderedPolynomial r ord (k :+ n)
shiftR k = withKnownNat (k %:+ (sing :: SNat n)) $
  withKnownNat k $ transformMonomial (S.append (fromList k []))

-- | Calculate the homogenized polynomial of given one, with additional variable is the last variable.
homogenize :: forall k ord n.
              (CoeffRing k, KnownNat n, IsMonomialOrder (n+1) ord, IsMonomialOrder n ord)
           => OrderedPolynomial k ord n -> OrderedPolynomial k ord (n + 1)
homogenize f =
  withKnownNat (sSucc (sing :: SNat n)) $
  let g = substWith (.*.) (S.init allVars) f
      d = fromIntegral (totalDegree' g)
  in transformMonomial (\m -> m & ix maxBound .~ d - P.sum m) g

unhomogenize :: forall k ord n.
                (CoeffRing k, KnownNat n, IsMonomialOrder n ord,
                 IsMonomialOrder (n+1) ord)
             => OrderedPolynomial k ord (Succ n) -> OrderedPolynomial k ord n
unhomogenize f =
  withKnownNat (sSucc (sing :: SNat n)) $
  substWith (.*.)
    (coerceLength (symmetry $ succAndPlusOneR (sing :: SNat n)) $
     allVars `S.append` S.singleton one)
    f

reversal :: (CoeffRing k, IsMonomialOrder 1 o)
         => Int -> OrderedPolynomial k o 1 -> OrderedPolynomial k o 1
reversal k = transformMonomial (S.map (k - ))

padeApprox :: (Field r, DecidableUnits r, CoeffRing r, IntegralSemiring r,
              IsMonomialOrder 1 order)
           => Natural -> Natural -> OrderedPolynomial r order 1
           -> (OrderedPolynomial r order 1, OrderedPolynomial r order 1)
padeApprox k nmk g =
  let (r, _, t) = last $ filter ((< P.fromIntegral k) . totalDegree' . view _1) $ euclid (pow varX (k+nmk)) g
  in (r, t)


minpolRecurrent :: forall k. (Eq k, IntegralSemiring k, DecidableUnits k, DecidableZero k, Field k)
                => Natural -> [k] -> Polynomial k 1
minpolRecurrent n xs =
  let h = sum $ zipWith (\a b -> injectCoeff a * b) xs [pow varX i | i <- [0.. pred (2 * n)]]
          :: Polynomial k 1
      (s, t) = padeApprox n n h
      d = fromIntegral $ max (1 + totalDegree' s) (totalDegree' t)
  in reversal d (recip (coeff one t) .*. t)
