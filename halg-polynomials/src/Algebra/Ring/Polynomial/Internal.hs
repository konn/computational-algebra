{-# LANGUAGE ConstraintKinds, DataKinds, ExplicitNamespaces              #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs                  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, LiberalTypeSynonyms             #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction, PolyKinds #-}
{-# LANGUAGE RankNTypes, RoleAnnotations, ScopedTypeVariables            #-}
{-# LANGUAGE StandaloneDeriving, TypeApplications, TypeFamilies          #-}
{-# LANGUAGE TypeOperators, TypeSynonymInstances, UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns                                                #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-type-defaults #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module Algebra.Ring.Polynomial.Internal
    ( module Algebra.Ring.Polynomial.Monomial,
      module Algebra.Ring.Polynomial.Class,
      Polynomial,
      transformMonomial,
      castPolynomial, changeOrder, changeOrderProxy,
      scastPolynomial, OrderedPolynomial(..),
      allVars, substVar, homogenize, unhomogenize,
      normalize, varX, getTerms, shiftR, orderedBy,
      mapCoeff, reversal, padeApprox,
      eval, evalUnivariate,
      substUnivariate, minpolRecurrent,
      IsOrder(..),
      PadPolyL(..),
      padLeftPoly
    )  where
import Algebra.Internal
import Algebra.Ring.Polynomial.Class
import Algebra.Ring.Polynomial.Monomial
import Algebra.Scalar

import           AlgebraicPrelude
import           Control.DeepSeq                       (NFData)
import           Control.Lens
import qualified Data.Coerce                           as C
import qualified Data.HashSet                          as HS
import           Data.Map                              (Map)
import qualified Data.Map.Merge.Strict                 as MM
import qualified Data.Map.Strict                       as M
import           Data.MonoTraversable                  (osum)
import qualified Data.Set                              as Set
import           Data.Singletons.Prelude.List          (Replicate)
import qualified Data.Sized.Builtin                    as S
import qualified Numeric.Algebra                       as NA
import           Numeric.Algebra.Unital.UnitNormalForm (UnitNormalForm (..))
import           Numeric.Domain.Integral               (IntegralDomain (..))
import           Numeric.Semiring.ZeroProduct          (ZeroProductSemiring)
import qualified Prelude                               as P
import           Proof.Equational                      (symmetry)

instance Hashable r => Hashable (OrderedPolynomial r ord n) where
  hashWithSalt salt poly = hashWithSalt salt $ getTerms poly

deriving instance (CoeffRing r, IsOrder n ord, Ord r) => Ord (OrderedPolynomial r ord n)

-- | n-ary polynomial ring over some noetherian ring R.
newtype OrderedPolynomial r order n = Polynomial { _terms :: Map (OrderedMonomial order n) r }
                                    deriving (NFData)
type role OrderedPolynomial representational nominal nominal

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
      extractPower = runMult . ifoldMapMonom (\ o -> Mult . pow (mor o) . fromIntegral) . getMonomial
  {-# INLINE liftMap #-}

instance (KnownNat n, CoeffRing r, IsMonomialOrder n ord)
      => IsOrderedPolynomial (OrderedPolynomial r ord n) where
  -- | coefficient for a degree.
  type MOrder (OrderedPolynomial r ord n) = ord
  coeff d = M.findWithDefault zero d . terms
  {-# INLINE coeff #-}

  terms = C.coerce
  {-# INLINE terms #-}

  orderedMonomials = M.keysSet . terms
  {-# INLINE orderedMonomials #-}

  toPolynomial (c, deg) =
    if isZero c
    then Polynomial M.empty
    else Polynomial $ M.singleton deg c
  {-# INLINE toPolynomial #-}

  polynomial = normalize . C.coerce
  {-# INLINE polynomial #-}

  (>*) m = Polynomial . M.mapKeysMonotonic (m *) . C.coerce
  {-# INLINE (>*) #-}

  leadingTerm (Polynomial d) =
    case M.maxViewWithKey d of
      Just ((deg, c), _) -> (c, deg)
      Nothing -> (zero, one)
  {-# INLINE leadingTerm #-}

  leadingMonomial = snd . leadingTerm
  {-# INLINE leadingMonomial #-}

  leadingCoeff = fst . leadingTerm
  {-# INLINE leadingCoeff #-}

  splitLeadingTerm (Polynomial d) =
    case M.maxViewWithKey d of
      Just ((deg, c), p) -> ((c, deg), Polynomial p)
      Nothing -> ((zero, one), zero)
  {-# INLINE splitLeadingTerm #-}

  mapMonomialMonotonic f = Polynomial . M.mapKeysMonotonic f . C.coerce
  {-# INLINE mapMonomialMonotonic #-}

castPolynomial :: forall r n m o o'.
                  (CoeffRing r, KnownNat n, KnownNat m,
                   IsMonomialOrder n o, IsMonomialOrder m o')
               => OrderedPolynomial r o n
               -> OrderedPolynomial r o' m
castPolynomial = C.coerce @(Map (OrderedMonomial o n) r  -> Map (OrderedMonomial o' m) r)
                 (M.mapKeys castMonomial)
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
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Ring (OrderedPolynomial r order n) where
  fromInteger 0 = Polynomial M.empty
  fromInteger n = Polynomial $ M.singleton one (NA.fromInteger n)
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
  Polynomial (M.toList -> d1) *  Polynomial d2 =
    let ds = [ M.map (c*) $ M.mapKeysMonotonic (k *) d2 | (k, c) <- d1 ]
        fuse = MM.zipWithMaybeMatched $ \_ x y -> guardZero $ x + y
    in Polynomial $ foldr (MM.merge MM.preserveMissing MM.preserveMissing fuse) M.empty ds
  {-# INLINE (*) #-}

guardZero :: DecidableZero a => a -> Maybe a
guardZero x = if isZero x then Nothing else Just x
{-# INLINE guardZero #-}

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

-- | We provide Num instance to use trivial injection R into R[X].
--   Do not use signum or abs.
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n)
      => P.Num (OrderedPolynomial r order n) where
  (+) = (NA.+)
  {-# INLINE (+) #-}

  (*) = (NA.*)
  {-# INLINE (*) #-}

  fromInteger = NA.fromInteger
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

instance (Eq r, KnownNat n, Euclidean r, IsMonomialOrder n ord)
      => DecidableAssociates (OrderedPolynomial r ord n) where
  isAssociate = isAssociateDefault
  {-# INLINE isAssociate #-}

instance (Eq r, Euclidean r, KnownNat n,
          IsMonomialOrder n ord)
      => UnitNormalForm (OrderedPolynomial r ord n) where
  splitUnit = splitUnitDefault
  {-# INLINE splitUnit #-}

instance {-# OVERLAPPING #-}
         (Eq r, DecidableUnits r, DecidableZero r, Field r,
          IsMonomialOrder 1 ord, ZeroProductSemiring r)
         => GCDDomain (OrderedPolynomial r ord 1)
instance {-# OVERLAPPING #-}
         (Eq r, DecidableUnits r, DecidableZero r, Field r,
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

instance {-# OVERLAPPING #-}
         (Eq r, DecidableUnits r, DecidableZero r,
          Field r, IsMonomialOrder 1 ord, ZeroProductSemiring r)
       => IntegralDomain (OrderedPolynomial r ord 1)

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

instance (CoeffRing r, IsMonomialOrder n ord, DecidableUnits r, KnownNat n)
       => DecidableUnits (OrderedPolynomial r ord n) where
  isUnit = isUnitDefault
  recipUnit = recipUnitDefault

varX :: forall r n order. (CoeffRing r, KnownNat n, IsMonomialOrder n order, (0 < n) ~ 'True)
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

-- | @substVar n f@ substitutes @n@-th variable with polynomial @f@,
--   without changing arity.
substVar :: (CoeffRing r, KnownNat n, IsMonomialOrder n ord, (1 <= n) ~  'True)
         => Ordinal n
         -> OrderedPolynomial r ord n
         -> OrderedPolynomial r ord n
         -> OrderedPolynomial r ord n
substVar p val =
  liftMap  (\o -> if o == p then val else var o)

allVars :: forall k ord n . (IsMonomialOrder n ord, CoeffRing k, KnownNat n)
        => Sized n (OrderedPolynomial k ord n)
allVars = unsafeFromList' vars

changeOrder :: forall k n o o'.
               (CoeffRing k, Eq (Monomial n), IsMonomialOrder n o, IsMonomialOrder n o',  KnownNat n)
            => o' -> OrderedPolynomial k o n -> OrderedPolynomial k o' n
changeOrder _ =
  C.coerce @(Map (OrderedMonomial o n) k -> Map (OrderedMonomial o' n) k) $
  M.mapKeys (OrderedMonomial . getMonomial)

changeOrderProxy :: forall k n o o'.
                    (CoeffRing k, Eq (Monomial n), IsMonomialOrder n o,
                     IsMonomialOrder n o',  KnownNat n)
                 => Proxy o' -> OrderedPolynomial k o n -> OrderedPolynomial k o' n
changeOrderProxy _ =
  C.coerce @(Map (OrderedMonomial o n) k -> Map (OrderedMonomial o' n) k) $
  M.mapKeys (OrderedMonomial . getMonomial)

getTerms :: OrderedPolynomial k order n -> [(k, OrderedMonomial order n)]
getTerms = map (snd &&& fst) . M.toDescList . _terms

transformMonomial :: (IsMonomialOrder m o', CoeffRing k, KnownNat m)
                  => (USized n Int -> USized m Int) -> OrderedPolynomial k o n -> OrderedPolynomial k o' m
transformMonomial tr (Polynomial d) =
  polynomial $ M.mapKeys (OrderedMonomial . tr . getMonomial) d

orderedBy :: OrderedPolynomial k o n -> o -> OrderedPolynomial k o n
p `orderedBy` _ = p

shiftR :: forall k r n ord. (CoeffRing r, KnownNat n, IsMonomialOrder n ord,
                             IsMonomialOrder (k + n) ord)
       => SNat k -> OrderedPolynomial r ord n -> OrderedPolynomial r ord (k + n)
shiftR k = withKnownNat (k %+ (sing :: SNat n)) $
  withKnownNat k $ transformMonomial (S.append (S.replicate' 0))

-- | Calculate the homogenized polynomial of given one, with additional variable is the last variable.
homogenize :: forall k ord n.
              (CoeffRing k, KnownNat n, IsMonomialOrder (n+1) ord, IsMonomialOrder n ord)
           => OrderedPolynomial k ord n -> OrderedPolynomial k ord (n + 1)
homogenize f =
  withKnownNat (sSucc (sing :: SNat n)) $
  let g = substWith (.*.) (S.init allVars) f
      d = fromIntegral (totalDegree' g)
  in mapMonomialMonotonic (\m -> m & _Wrapped.ix maxBound .~ d - osum (m^._Wrapped)) g

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

newtype PadPolyL n ord poly = PadPolyL { runPadPolyL :: OrderedPolynomial poly (Graded ord) n }
deriving instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Additive (PadPolyL n ord poly)
deriving instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => LeftModule Natural (PadPolyL n ord poly)
deriving instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => RightModule Natural (PadPolyL n ord poly)
deriving instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Monoidal (PadPolyL n ord poly)
deriving instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => LeftModule Integer (PadPolyL n ord poly)
deriving instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => RightModule Integer (PadPolyL n ord poly)
deriving instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Group (PadPolyL n ord poly)
deriving instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Abelian (PadPolyL n ord poly)
deriving instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Multiplicative (PadPolyL n ord poly)
deriving instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Unital (PadPolyL n ord poly)
deriving instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Commutative (PadPolyL n ord poly)
deriving instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Eq (PadPolyL n ord poly)
deriving instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Semiring (PadPolyL n ord poly)
deriving instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Rig (PadPolyL n ord poly)
deriving instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Ring (PadPolyL n ord poly)
deriving instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => DecidableZero (PadPolyL n ord poly)
instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly,
          LeftModule (Scalar r) poly)
       => LeftModule (Scalar r) (PadPolyL n ord poly) where
  r .* PadPolyL f = PadPolyL $ mapCoeff' (r .*) f
  {-# INLINE (.*) #-}
instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly,
          RightModule (Scalar r) poly)
       => RightModule (Scalar r) (PadPolyL n ord poly) where
  PadPolyL f *. r = PadPolyL $ mapCoeff' (*. r) f
  {-# INLINE (*.) #-}
deriving instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Num (PadPolyL n ord poly)

instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
     =>  IsPolynomial (PadPolyL n ord poly) where
  type Coefficient (PadPolyL n ord poly) = Coefficient poly
  type Arity (PadPolyL n ord poly) = n + Arity poly
  sArity _ = sing
  liftMap f = subst $ S.generate sing f
  subst vec (PadPolyL f) =
    let sn = sing :: Sing n
        sm = sing :: Sing (Arity poly)
    in withWitness (plusLeqL sn sm) $
       withRefl (plusMinus' sn sm) $
       case S.splitAt sn vec of
         (ls, rs) -> substWith (\ g a -> a * subst rs g) ls f
  injectCoeff = PadPolyL . injectCoeff . injectCoeff
  fromMonomial m =
    let sn = sing :: Sing n
        sm = sing :: Sing (Arity poly)
    in withWitness (plusLeqL sn sm) $
       withRefl (plusMinus' sn sm) $
       case S.splitAt sn m of
         (ls, rs) -> PadPolyL $ fromMonomial ls * injectCoeff (fromMonomial rs)
  terms' (PadPolyL m) =
    M.fromList
    [ (ls S.++ rs, k)
    | (ls, pol) <- M.toList $ terms' m
    , (rs, k)   <- M.toList $ terms' pol
    ]

instance (SingI (Replicate n 1), KnownNat n, IsMonomialOrder n ord, IsOrderedPolynomial poly)
     =>  IsOrderedPolynomial (PadPolyL n ord poly) where
  type MOrder (PadPolyL n ord poly) =
    ProductOrder n (Arity poly) (Graded ord) (MOrder poly)
  leadingTerm (PadPolyL f) =
    let (p, OrderedMonomial ls) = leadingTerm f
        (k, OrderedMonomial rs) = leadingTerm p
    in (k, OrderedMonomial $ ls S.++ rs)

padLeftPoly :: (IsMonomialOrder n ord, IsPolynomial poly)
            => Sing n -> ord -> poly -> PadPolyL n ord poly
padLeftPoly n _ = withKnownNat n $ PadPolyL . injectCoeff

instance (r ~ Coefficient poly, IsOrderedPolynomial poly, SingI (Replicate n 1),
          KnownNat n, CoeffRing r, IsMonomialOrder n order, PrettyCoeff r)
       => Show (PadPolyL n order poly) where
  showsPrec = showsPolynomialWith $ generate sing (\i -> "X_" ++ show (fromEnum i))

mapOrderedPolynomial :: forall r r' n n' ord' ord.
                        (KnownNat n, KnownNat n', CoeffRing r', IsMonomialOrder n' ord')
                     => (r -> r') -> (Ordinal n -> Ordinal n')
                     -> OrderedPolynomial r ord n -> OrderedPolynomial r' ord' n'
mapOrderedPolynomial mapCoe mapVar (Polynomial dic) =
  let toGenerator = OrderedMonomial
                  . generate sing . (runAdd .)
                  . ifoldMapMonom (\o l j -> Add $ if j == mapVar o then l else 0)
                  . getMonomial
  in Polynomial $ M.mapKeys toGenerator $
     M.mapMaybe (\i -> let c = mapCoe i in if isZero c then Nothing else Just c) dic
-- Orphan Rules
{-# RULES
"convertPolynomial/OrderedPolynomial" [~2]
    convertPolynomial = id
"convertPolynomial'/OrderedPolynomial" [~2]
    convertPolynomial' = castPolynomial
"mapPolynomial/OrderedPolynomial" [~2]
  forall
    (mapC :: CoeffRing r' => r -> r')
    (mapV :: KnownNat n' => Ordinal n -> Ordinal n').
  mapPolynomial mapC mapV = mapOrderedPolynomial mapC mapV
  #-}
