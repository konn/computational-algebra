{-# LANGUAGE ConstraintKinds, DataKinds, DeriveAnyClass, DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies, ExplicitNamespaces, FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving      #-}
{-# LANGUAGE LiberalTypeSynonyms, MultiParamTypeClasses                #-}
{-# LANGUAGE NoMonomorphismRestriction, PolyKinds, RankNTypes          #-}
{-# LANGUAGE RoleAnnotations, ScopedTypeVariables, StandaloneDeriving  #-}
{-# LANGUAGE TypeFamilies, TypeOperators, TypeSynonymInstances         #-}
{-# LANGUAGE UndecidableInstances, ViewPatterns                        #-}
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
import           Control.DeepSeq                       (NFData (..))
import           Control.Lens
import qualified Data.Coerce                           as C
import qualified Data.Foldable                         as F
import qualified Data.HashSet                          as HS
import qualified Data.Heap                             as H
import qualified Data.Map.Strict                       as M
import           Data.MonoTraversable                  (osum)
import qualified Data.Set                              as Set
import           Data.Singletons.Prelude.List          (Replicate)
import qualified Data.Sized.Builtin                    as S
import           GHC.Generics                          (Generic)
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
newtype OrderedPolynomial r order n = Polynomial { _terms :: H.Heap (REntry (OrderedMonomial order n) r) }

data REntry a b = REntry { priority :: !a, payload :: !b }
  deriving (Read, Show, NFData, Generic)

instance Eq a => Eq (REntry a b) where
  (==) = (==) `on` priority
  {-# INLINE (==) #-}

  (/=) = (/=) `on` priority
  {-# INLINE (/=) #-}

instance Ord a => Ord (REntry a b) where
  compare = flip $ comparing priority
  {-# INLINE compare #-}

instance NFData r => NFData (OrderedPolynomial r order n) where
  rnf (Polynomial h) = rnf $ F.toList h
  {-# INLINE rnf #-}

type Polynomial r = OrderedPolynomial r Grevlex

type RHeap a b = H.Heap (REntry a b)

onPayload :: (b -> c) -> REntry a b -> REntry a c
onPayload f (REntry a b) = REntry a (f b)
{-# INLINE onPayload #-}

mapPayload :: Ord a => (b -> c) -> RHeap a b -> RHeap a c
mapPayload  = H.mapMonotonic . onPayload
{-# INLINE mapPayload #-}

mergeWith :: Ord a => (b -> b -> b) -> (b -> b) -> (b -> b) -> RHeap a b -> RHeap a b -> RHeap a b
mergeWith f fl fr l r =
  H.mapMonotonic (\h -> REntry (priority $ H.minimum h) (foldr1 f $ map payload $ F.toList h)) $
  H.group $ H.union (H.mapMonotonic (onPayload fl) l) (H.mapMonotonic (onPayload fr) r)
{-# INLINE mergeWith #-}

single :: Ord a => a -> b -> H.Heap (REntry a b)
single a = H.singleton . REntry a

mapKeys :: Ord a' => (a -> a') -> H.Heap (REntry a b) -> H.Heap (REntry a' b)
mapKeys f = H.map (\(REntry a b) -> REntry (f a) b)

htoList :: H.Heap (REntry a b) -> [(a, b)]
htoList = map (\(REntry a b) -> (a, b)) .  F.toList
{-# INLINE htoList #-}

hfromList :: Ord a => [(a, b)] -> H.Heap (REntry a b)
hfromList = H.fromList . map (uncurry REntry)

mapKeysMonotonic :: Ord a' => (a -> a') -> H.Heap (REntry a b) -> H.Heap (REntry a' b)
mapKeysMonotonic f = H.mapMonotonic (\(REntry a b) -> REntry (f a) b)

viewMax :: H.Heap (REntry a b) -> Maybe ((a, b), H.Heap (REntry a b))
viewMax d = H.viewMin d <&> \ (REntry a b,c) -> ((a,b), c)
{-# INLINE viewMax #-}

instance (KnownNat n, IsMonomialOrder n ord, CoeffRing r) => IsPolynomial (OrderedPolynomial r ord n) where
  type Coefficient (OrderedPolynomial r ord n) = r
  type Arity       (OrderedPolynomial r ord n) = n

  injectCoeff r | isZero r  = Polynomial H.empty
                | otherwise = Polynomial $ H.singleton $ REntry one r
  {-# INLINE injectCoeff #-}

  sArity' = sizedLength . getMonomial . leadingMonomial
  {-# INLINE sArity' #-}

  mapCoeff' = mapCoeff
  {-# INLINE mapCoeff' #-}

  monomials = HS.fromList . map getMonomial . Set.toList . orderedMonomials
  {-# INLINE monomials #-}

  fromMonomial m = Polynomial $ single (OrderedMonomial m) one
  {-# INLINE fromMonomial #-}

  toPolynomial' (r, m) = Polynomial $ single (OrderedMonomial m) r
  {-# INLINE toPolynomial' #-}

  polynomial' dic = normalize $ Polynomial $ hfromList $ M.toList $ M.mapKeysMonotonic OrderedMonomial dic
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

  terms = M.fromList . htoList . _terms
  {-# INLINE terms #-}

  orderedMonomials = M.keysSet . terms
  {-# INLINE orderedMonomials #-}

  toPolynomial (c, deg) =
    if isZero c
    then Polynomial H.empty
    else Polynomial $ single deg c
  {-# INLINE toPolynomial #-}

  polynomial = normalize . Polynomial . hfromList . M.toList
  {-# INLINE polynomial #-}

  (>*) m = C.coerce (mapKeysMonotonic (m *))
  {-# INLINE (>*) #-}

  leadingTerm (Polynomial d) =
    case viewMax d of
      Just ((deg, c), _) -> (c, deg)
      Nothing -> (zero, one)
  {-# INLINE leadingTerm #-}

  leadingMonomial = snd . leadingTerm
  {-# INLINE leadingMonomial #-}

  leadingCoeff = fst . leadingTerm
  {-# INLINE leadingCoeff #-}

  splitLeadingTerm (Polynomial d) =
    case viewMax d of
      Just ((deg, c), p) -> ((c, deg), Polynomial p)
      Nothing -> ((zero, one), zero)
  {-# INLINE splitLeadingTerm #-}

  mapMonomialMonotonic f = Polynomial . mapKeysMonotonic f . C.coerce
  {-# INLINE mapMonomialMonotonic #-}

castPolynomial :: (CoeffRing r, KnownNat n, KnownNat m,
                   IsMonomialOrder n o, IsMonomialOrder m o')
               => OrderedPolynomial r o n
               -> OrderedPolynomial r o' m
castPolynomial = C.coerce (mapKeys castMonomial)
{-# INLINE castPolynomial #-}

scastPolynomial :: (IsMonomialOrder n o, IsMonomialOrder m o', KnownNat m,
                    CoeffRing r, KnownNat n)
                => SNat m -> OrderedPolynomial r o n -> OrderedPolynomial r o' m
scastPolynomial _ = castPolynomial
{-# INLINE scastPolynomial #-}

mapCoeff :: (KnownNat n, CoeffRing b, IsMonomialOrder n ord)
         => (a -> b) -> OrderedPolynomial a ord n -> OrderedPolynomial b ord n
mapCoeff f (Polynomial dic) = normalize $ Polynomial $ H.mapMonotonic (\(REntry a b) -> REntry a (f b)) dic
{-# INLINE mapCoeff #-}

normalize :: (DecidableZero r)
          => OrderedPolynomial r order n -> OrderedPolynomial r order n
normalize (Polynomial dic) =
  Polynomial $ H.filter (not . isZero . payload) dic
{-# INLINE normalize #-}


instance (Eq r) => Eq (OrderedPolynomial r order n) where
  Polynomial f == Polynomial g = f == g
  {-# INLINE (==) #-}

-- -- | By Hilbert's finite basis theorem, a polynomial ring over a noetherian ring is also a noetherian ring.
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Ring (OrderedPolynomial r order n) where
  fromInteger 0 = Polynomial H.empty
  fromInteger n = Polynomial $ single one (NA.fromInteger n)
  {-# INLINE fromInteger #-}

instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Rig (OrderedPolynomial r order n)
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Group (OrderedPolynomial r order n) where
  negate (Polynomial dic) = Polynomial $ mapPayload negate dic
  {-# INLINE negate #-}

  Polynomial f - Polynomial g = Polynomial $ mergeWith (-) id negate f g
  {-# INLINE (-) #-}


instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => LeftModule Integer (OrderedPolynomial r order n) where
  n .* Polynomial dic = normalize $ Polynomial $ mapPayload (n .*) dic
  {-# INLINE (.*) #-}

instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => RightModule Integer (OrderedPolynomial r order n) where
  (*.) = flip (.*)
  {-# INLINE (*.) #-}
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Additive (OrderedPolynomial r order n) where
  (Polynomial f) + (Polynomial g) = normalize $ Polynomial $ mergeWith (+) id id f g
  {-# INLINE (+) #-}
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Monoidal (OrderedPolynomial r order n) where
  zero = Polynomial H.empty
  {-# INLINE zero #-}
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => LeftModule Natural (OrderedPolynomial r order n) where
  n .* Polynomial dic = normalize $ Polynomial $ mapPayload (n .*) dic
  {-# INLINE (.*) #-}
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => RightModule Natural (OrderedPolynomial r order n) where
  (*.) = flip (.*)
  {-# INLINE (*.) #-}

instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Unital (OrderedPolynomial r order n) where
  one = Polynomial $ single one one
  {-# INLINE one #-}

instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Multiplicative (OrderedPolynomial r order n) where
  Polynomial (htoList -> d1) *  Polynomial d2 =
    let ds = [ mapPayload (c*) $ mapKeysMonotonic (k *) d2 | (k, c) <- d1 ]
    in normalize $ Polynomial $ foldr (mergeWith (+) id id) H.empty ds
  {-# INLINE (*) #-}

instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Semiring (OrderedPolynomial r order n) where
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Commutative (OrderedPolynomial r order n) where
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => Abelian (OrderedPolynomial r order n) where
instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => LeftModule (Scalar r) (OrderedPolynomial r order n) where
  Scalar r .* Polynomial dic = normalize $ Polynomial $ mapPayload (r*) dic
  {-# INLINE (.*) #-}

instance (IsMonomialOrder n order, CoeffRing r, KnownNat n) => RightModule (Scalar r) (OrderedPolynomial r order n) where
  Polynomial dic *. Scalar r = normalize $ Polynomial $ mapPayload (r*) dic
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
  isZero (Polynomial d) = H.null d
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

changeOrder :: (CoeffRing k, Eq (Monomial n), IsMonomialOrder n o, IsMonomialOrder n o',  KnownNat n)
            => o' -> OrderedPolynomial k o n -> OrderedPolynomial k o' n
changeOrder _ = C.coerce $ mapKeys (OrderedMonomial . getMonomial)

changeOrderProxy :: (CoeffRing k, Eq (Monomial n), IsMonomialOrder n o,
                     IsMonomialOrder n o',  KnownNat n)
                 => Proxy o' -> OrderedPolynomial k o n -> OrderedPolynomial k o' n
changeOrderProxy _ = C.coerce $ mapKeys (OrderedMonomial . getMonomial)

getTerms :: OrderedPolynomial k order n -> [(k, OrderedMonomial order n)]
getTerms = map (snd &&& fst) . htoList . _terms

transformMonomial :: (IsMonomialOrder m o', IsMonomialOrder n o, CoeffRing k, KnownNat m)
                  => (USized n Int -> USized m Int) -> OrderedPolynomial k o n -> OrderedPolynomial k o' m
transformMonomial tr (Polynomial d) =
  Polynomial $ mapKeys (OrderedMonomial . tr . getMonomial) d

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
deriving newtype instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Additive (PadPolyL n ord poly)
deriving newtype instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => LeftModule Natural (PadPolyL n ord poly)
deriving newtype instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => RightModule Natural (PadPolyL n ord poly)
deriving newtype instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Monoidal (PadPolyL n ord poly)
deriving newtype instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => LeftModule Integer (PadPolyL n ord poly)
deriving newtype instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => RightModule Integer (PadPolyL n ord poly)
deriving newtype instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Group (PadPolyL n ord poly)
deriving newtype instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Abelian (PadPolyL n ord poly)
deriving newtype instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Multiplicative (PadPolyL n ord poly)
deriving newtype instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Unital (PadPolyL n ord poly)
deriving newtype instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Commutative (PadPolyL n ord poly)
deriving newtype instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Eq (PadPolyL n ord poly)
deriving newtype instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Semiring (PadPolyL n ord poly)
deriving newtype instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Rig (PadPolyL n ord poly)
deriving newtype instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
               => Ring (PadPolyL n ord poly)
deriving newtype instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
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
deriving newtype instance (KnownNat n, IsMonomialOrder n ord, IsPolynomial poly)
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

instance (r ~ Coefficient poly, IsPolynomial poly,
          KnownNat n, CoeffRing r, IsMonomialOrder n order, PrettyCoeff r)
       => Show (PadPolyL n order poly) where
  showsPrec = showsPolynomialWith $ generate sing (\i -> "X_" ++ show (fromEnum i))

mapOrderedPolynomial :: forall r r' n n' ord' ord.
                        (KnownNat n, KnownNat n', CoeffRing r', IsMonomialOrder n' ord', IsMonomialOrder n ord)
                     => (r -> r') -> (Ordinal n -> Ordinal n')
                     -> OrderedPolynomial r ord n -> OrderedPolynomial r' ord' n'
mapOrderedPolynomial mapCoe mapVar (Polynomial dic) =
  let toGenerator = OrderedMonomial
                  . generate sing . (runAdd .)
                  . ifoldMapMonom (\o l j -> Add $ if j == mapVar o then l else 0)
                  . getMonomial
  in normalize $ Polynomial $ mapKeys toGenerator $ mapPayload mapCoe dic
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
