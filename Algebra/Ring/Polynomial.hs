{-# LANGUAGE ConstraintKinds, DataKinds, ExplicitNamespaces            #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs                #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, LiberalTypeSynonyms           #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction          #-}
{-# LANGUAGE PatternGuards, PolyKinds, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving, TemplateHaskell, TypeFamilies         #-}
{-# LANGUAGE TypeOperators, TypeSynonymInstances, UndecidableInstances #-}
{-# LANGUAGE ViewPatterns                                              #-}
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

import           AlgebraicPrelude
import           Control.DeepSeq                       (NFData)
import           Control.Lens                          hiding (assign)
import qualified Data.Foldable                         as F
import qualified Data.HashSet                          as HS
import           Data.Map                              (Map)
import qualified Data.Map.Strict                       as M
import qualified Data.Set                              as Set
import           Data.Singletons.Prelude               (POrd (..))
import           Data.Sized.Builtin                    ((%!!))
import qualified Data.Sized.Builtin                    as S
import           Data.Type.Ordinal
import qualified Numeric.Algebra                       as NA
import           Numeric.Algebra.Unital.UnitNormalForm (UnitNormalForm (..))
import qualified Numeric.Algebra.Unital.UnitNormalForm as NA
import           Numeric.Domain.Integral               (IntegralDomain (..))
import qualified Numeric.Ring.Class                    as NA
import           Numeric.Semiring.ZeroProduct          (ZeroProductSemiring)
import qualified Prelude                               as P
import           Proof.Equational                      (symmetry)

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
      extractPower m =
       NA.product $ generate (sing :: SNat n) (\ o -> pow  (mor o) (fromIntegral $ getMonomial m %!! o))
  {-# INLINE liftMap #-}




ordVec :: forall n. KnownNat n => Sized n (Ordinal n)
ordVec = unsafeFromList' $ enumOrdinal (sing :: SNat n)

instance (KnownNat n, CoeffRing r, IsMonomialOrder n ord)
      => IsOrderedPolynomial (OrderedPolynomial r ord n) where
  -- | coefficient for a degree.
  type MOrder (OrderedPolynomial r ord n) = ord
  coeff d = M.findWithDefault zero d . terms
  {-# INLINE coeff #-}

  terms = _terms
  {-# INLINE terms #-}

  orderedMonomials = M.keysSet . terms
  {-# INLINE orderedMonomials #-}

  toPolynomial (c, deg) = polynomial $ M.singleton deg c
  {-# INLINE toPolynomial #-}

  polynomial dic = normalize $ Polynomial dic
  {-# INLINE polynomial #-}

  leadingTerm (Polynomial d) =
    case M.maxViewWithKey d of
      Just ((deg, c), _) -> (c, deg)
      Nothing -> (zero, one)
  {-# INLINE leadingTerm #-}

  leadingMonomial = snd . leadingTerm
  {-# INLINE leadingMonomial #-}

  leadingCoeff = fst . leadingTerm
  {-# INLINE leadingCoeff #-}

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
{-# INLINE castPolynomial #-}

scastPolynomial :: (IsMonomialOrder n o, IsMonomialOrder m o', KnownNat m,
                    CoeffRing r, KnownNat n)
                => SNat m -> OrderedPolynomial r o n -> OrderedPolynomial r o' m
scastPolynomial _ = castPolynomial
{-# INLINE scastPolynomial #-}

mapCoeff :: (KnownNat n, CoeffRing b, IsMonomialOrder n ord)
         => (a -> b) -> OrderedPolynomial a ord n -> OrderedPolynomial b ord n
mapCoeff f (Polynomial dic) = polynomial $ M.map f dic
{-# INLINE mapCoeff #-}

normalize :: (DecidableZero r)
          => OrderedPolynomial r order n -> OrderedPolynomial r order n
normalize (Polynomial dic) =
  Polynomial $ M.filter (not . isZero) dic
{-# INLINE normalize #-}


instance (Eq r) => Eq (OrderedPolynomial r order n) where
  Polynomial f == Polynomial g = f == g
  {-# INLINE (==) #-}

-- -- | By Hilbert's finite basis theorem, a polynomial ring over a noetherian ring is also a noetherian ring.
-- instance (IsMonomialOrder order, CoeffRing r, KnownNat n) => Ring (OrderedPolynomial r order n) where
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Ring (OrderedPolynomial r order n) where
  fromInteger 0 = Polynomial M.empty
  fromInteger n = Polynomial $ M.singleton one (fromInteger' n)
  {-# INLINE fromInteger #-}

decZero :: DecidableZero r => r -> Maybe r
decZero n | isZero n = Nothing
          | otherwise = Just n
{-# INLINE decZero #-}

instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Rig (OrderedPolynomial r order n)
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Group (OrderedPolynomial r order n) where
  negate (Polynomial dic) = Polynomial $ fmap negate dic
  {-# INLINE negate #-}

  Polynomial f - Polynomial g = Polynomial $ M.mergeWithKey (\_ i j -> decZero (i - j)) id (fmap negate) f g
  {-# INLINE (-) #-}


instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => LeftModule Integer (OrderedPolynomial r order n) where
  n .* Polynomial dic = polynomial $ fmap (n .*) dic
  {-# INLINE (.*) #-}

instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => RightModule Integer (OrderedPolynomial r order n) where
  (*.) = flip (.*)
  {-# INLINE (*.) #-}
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Additive (OrderedPolynomial r order n) where
  (Polynomial f) + (Polynomial g) = polynomial $ M.unionWith (+) f g
  {-# INLINE (+) #-}
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Monoidal (OrderedPolynomial r order n) where
  zero = Polynomial M.empty
  {-# INLINE zero #-}
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => LeftModule Natural (OrderedPolynomial r order n) where
  n .* Polynomial dic = polynomial $ fmap (n .*) dic
  {-# INLINE (.*) #-}
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => RightModule Natural (OrderedPolynomial r order n) where
  (*.) = flip (.*)
  {-# INLINE (*.) #-}

instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Unital (OrderedPolynomial r order n) where
  one = Polynomial $ M.singleton one one
  {-# INLINE one #-}

instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Multiplicative (OrderedPolynomial r order n) where
  Polynomial (M.toList -> d1) *  Polynomial (M.toList -> d2) =
    let dic = (one, zero) : [ (a * b, r * r') | (a, r) <- d1, (b, r') <- d2, not $ isZero (r * r')
              ]
    in polynomial $ M.fromListWith (+) dic
  {-# INLINE (*) #-}

instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Semiring (OrderedPolynomial r order n) where
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Commutative (OrderedPolynomial r order n) where
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Abelian (OrderedPolynomial r order n) where
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => LeftModule (Scalar r) (OrderedPolynomial r order n) where
  Scalar r .* Polynomial dic = polynomial $ fmap (r*) dic
  {-# INLINE (.*) #-}

instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => RightModule (Scalar r) (OrderedPolynomial r order n) where
  Polynomial dic *. Scalar r = polynomial $ fmap (r*) dic
  {-# INLINE (*.) #-}


instance (IsMonomialOrder n ord, Characteristic r, KnownNat n, CoeffRing r)
      => Characteristic (OrderedPolynomial r ord n) where
  char _ = char (Proxy :: Proxy r)
  {-# INLINE char #-}

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

isConstantMonomial :: (Eq a, P.Num a) => Sized n a -> Bool
isConstantMonomial v = all (== 0) $ F.toList v

-- | We provide Num instance to use trivial injection R into R[X].
--   Do not use signum or abs.
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n)
      => P.Num (OrderedPolynomial r order n) where
  (+) = (+)
  {-# INLINE (+) #-}

  (*) = (*)
  {-# INLINE (*) #-}

  fromInteger = normalize . injectCoeff . fromInteger'
  {-# INLINE fromInteger #-}

  signum f = if isZero f then zero else injectCoeff one
  {-# INLINE signum #-}

  abs = id
  {-# INLINE abs #-}

  negate = ((P.negate 1 :: Integer) .*)
  {-# INLINE negate #-}


instance (CoeffRing r, KnownNat n, IsMonomialOrder n ord) => DecidableZero (OrderedPolynomial r ord n) where
  isZero (Polynomial d) = M.null d
  {-# INLINE isZero #-}

instance (CoeffRing r, IsMonomialOrder 1 ord, ZeroProductSemiring r)
      => ZeroProductSemiring (OrderedPolynomial r ord 1)

instance (Eq r, DecidableUnits r, DecidableZero r, Field r,
          IsMonomialOrder 1 ord, ZeroProductSemiring r)
      => DecidableAssociates (OrderedPolynomial r ord 1) where
  isAssociate = (==) `on` NA.normalize
  {-# INLINE isAssociate #-}

instance (Eq r, DecidableUnits r, DecidableZero r, Field r,
          IsMonomialOrder 1 ord, ZeroProductSemiring r)
      => UnitNormalForm (OrderedPolynomial r ord 1) where
  splitUnit f
    | isZero f = (zero, f)
    | otherwise = let lc = leadingCoeff f
                  in (injectCoeff lc, injectCoeff (recip lc) * f)
  {-# INLINE splitUnit #-}

instance (Eq r, DecidableUnits r, DecidableZero r, Field r,
          IsMonomialOrder 1 ord, ZeroProductSemiring r)
      => GCDDomain (OrderedPolynomial r ord 1)
instance (Eq r, DecidableUnits r, DecidableZero r, Field r,
          IsMonomialOrder 1 ord, ZeroProductSemiring r)
      => UFD (OrderedPolynomial r ord 1)
instance (Eq r, DecidableUnits r, DecidableZero r, Field r,
          IsMonomialOrder 1 ord, ZeroProductSemiring r)
      => PID (OrderedPolynomial r ord 1)
instance (Eq r, DecidableUnits r, DecidableZero r, Field r, IsMonomialOrder 1 ord, ZeroProductSemiring r) => Euclidean (OrderedPolynomial r ord 1) where
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


instance (Eq r, DecidableUnits r, DecidableZero r, KnownNat n,
          Field r, IsMonomialOrder n ord, ZeroProductSemiring r)
       => ZeroProductSemiring (OrderedPolynomial r ord n)

instance (Eq r, DecidableUnits r, DecidableZero r, KnownNat n,
          Field r, IsMonomialOrder n ord, ZeroProductSemiring r)
       => IntegralDomain (OrderedPolynomial r ord n) where
  p `divides` q = isZero $ p `modPolynomial` [q]
  p `maybeQuot` q =
    if isZero q
    then Nothing
    else let (r, s) = p `divModPolynomial` [q]
         in if isZero s
            then Just $ snd $ head r
            else Nothing

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
  in foldr (\a b -> Scalar a .* one + b * u)
           (Scalar (coeff (OrderedMonomial $ singleton $ fromIntegral n) f) .* one)
           [ coeff (OrderedMonomial $ singleton $ fromIntegral i) f | i <- [0 .. n P.- 1] ]

evalUnivariate :: (CoeffRing b, IsMonomialOrder 1 order) => b -> OrderedPolynomial b order 1 -> b
evalUnivariate u f =
  let n = totalDegree' f
  in if n == 0
     then coeff one f
     else foldr1 (\a b -> a + b * u)  [ coeff (OrderedMonomial $ singleton $ fromIntegral i) f | i <- [0 .. n] ]

-- | Evaluate polynomial at some point.
eval :: (CoeffRing r, IsMonomialOrder n order, KnownNat n)
     => Sized n r -> OrderedPolynomial r order n -> r
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
        => Sized n (OrderedPolynomial k ord n)
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

padeApprox :: (Field r, DecidableUnits r, CoeffRing r, ZeroProductSemiring r,
              IsMonomialOrder 1 order)
           => Natural -> Natural -> OrderedPolynomial r order 1
           -> (OrderedPolynomial r order 1, OrderedPolynomial r order 1)
padeApprox k nmk g =
  let (r, _, t) = last $ filter ((< P.fromIntegral k) . totalDegree' . view _1) $ euclid (pow varX (k+nmk)) g
  in (r, t)


minpolRecurrent :: forall k. (Eq k, ZeroProductSemiring k, DecidableUnits k, DecidableZero k, Field k)
                => Natural -> [k] -> Polynomial k 1
minpolRecurrent n xs =
  let h = sum $ zipWith (\a b -> injectCoeff a * b) xs [pow varX i | i <- [0.. pred (2 * n)]]
          :: Polynomial k 1
      (s, t) = padeApprox n n h
      d = fromIntegral $ max (1 + totalDegree' s) (totalDegree' t)
  in reversal d (recip (coeff one t) .*. t)
