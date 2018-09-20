{-# LANGUAGE BangPatterns, CPP, ConstraintKinds, DataKinds              #-}
{-# LANGUAGE FlexibleContexts, GADTs, GeneralizedNewtypeDeriving        #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude, RoleAnnotations  #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
-- | Polynomial type optimized to univariate polynomial.
module Algebra.Ring.Polynomial.Univariate
       (Unipol(), naiveMult, karatsuba,
        coeffList,
        divModUnipolByMult, divModUnipol,
        mapCoeffUnipol, liftMapUnipol,
        module Algebra.Ring.Polynomial.Class,
        module Algebra.Ring.Polynomial.Monomial) where
import           Algebra.Prelude.Core
import           Algebra.Ring.Polynomial.Class
import           Algebra.Ring.Polynomial.Monomial
import qualified Data.Foldable                    as F

import           Control.Arrow          (first)
import           Control.DeepSeq        (NFData)
import           Data.Function          (on)
import           Data.Hashable          (Hashable (hashWithSalt))
import qualified Data.HashSet           as HS
import           Data.IntMap            (IntMap)
import qualified Data.IntMap            as IM
import qualified Data.Map.Strict        as M
import           Data.Maybe             (mapMaybe)
import           Data.Ord               (comparing)
import qualified Data.Sized.Builtin     as SV
import qualified Numeric.Algebra        as NA
import           Numeric.Decidable.Zero (DecidableZero (..))
import qualified Prelude                as P

-- | Univariate polynomial.
--   It uses @'IM.IntMap'@ as its internal representation;
--   so if you want to treat the power greater than @maxBound :: Int@,
--   please consider using other represntation.
newtype Unipol r = Unipol { runUnipol :: IM.IntMap r }
                 deriving (NFData)
type role Unipol representational

instance Hashable r => Hashable (Unipol r) where
  hashWithSalt p = hashWithSalt p . IM.toList . runUnipol

-- | By this instance, you can use @#x@ for
--   the unique variable of @'Unipol' r@.
instance Unital r => IsLabel "x" (Unipol r) where
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 802
  fromLabel   = Unipol $ IM.singleton 1 one
#else
  fromLabel _ = Unipol $ IM.singleton 1 one
#endif

divModUnipol :: (CoeffRing r, Field r) => Unipol r -> Unipol r -> (Unipol r, Unipol r)
divModUnipol f g =
  if isZero g then error "Divided by zero!" else loop f zero
  where
    (dq, cq) = leadingTermIM g
    loop p !acc =
      let (dp, cp) = leadingTermIM p
          coe = cp/cq
          deg = dp - dq
          canceler = Unipol $ IM.map (*coe) $ IM.mapKeysMonotonic (+ deg) (runUnipol g)
      in if dp < dq || isZero p
         then (acc, p)
         else loop (p - canceler) $
              Unipol $ IM.insert deg coe $ runUnipol acc
{-# INLINE divModUnipol #-}

divModUnipolByMult :: (Eq r, Field r) => Unipol r -> Unipol r -> (Unipol r, Unipol r)
divModUnipolByMult f g =
  if isZero g then error "Divided by zero!" else
  let ((n,_), (m,_)) = (leadingTermIM f, leadingTermIM g)
      i = logBase2 (n - m + 1) + 1
      g' = reversalIM g
      t  = recipBinPow i g'
      q  = reversalIMWith (n - m) $
           modVarPower (n - m + 1) $
           t * reversalIM f
  in if n >= m
     then (q, f - g * q)
     else (zero, f)
{-# INLINE divModUnipolByMult #-}

recipBinPow :: (Eq r, Field r)
            => Int -> Unipol r -> Unipol r
recipBinPow i f =
  let g 0 = Unipol $ IM.singleton 0 $ recip (constantTerm f)
      g k = let p = g (k - 1)
            in modVarPower (2^fromIntegral k) (P.fromInteger 2 * p - p*p * f)
  in g i
{-# INLINE recipBinPow #-}

modVarPower :: Int -> Unipol r -> Unipol r
modVarPower n = Unipol . fst . IM.split n . runUnipol
{-# INLINE modVarPower #-}

reversalIM :: Monoidal r => Unipol r -> Unipol r
reversalIM m = reversalIMWith (fst $ leadingTermIM m) m
{-# INLINE reversalIM  #-}

reversalIMWith :: Monoidal r => Int -> Unipol r -> Unipol r
reversalIMWith d = Unipol . IM.mapKeys (d -) . runUnipol
{-# INLINE reversalIMWith  #-}



instance (Eq r, Field r) => DecidableUnits (Unipol r) where
  isUnit f =
    let (lc, lm) = leadingTerm f
    in lm == one && isUnit lc
  recipUnit f | isUnit f  = injectCoeff <$> recipUnit (leadingCoeff f)
              | otherwise = Nothing
instance (Eq r, Field r) => DecidableAssociates (Unipol r) where
  isAssociate = (==) `on` normaliseUnit

instance (Eq r, Field r) => UnitNormalForm (Unipol r) where
  splitUnit f
      | isZero f = (zero, f)
      | otherwise = let lc = leadingCoeff f
                    in (injectCoeff lc, injectCoeff (recip lc) * f)
instance (Eq r, Field r) => GCDDomain (Unipol r)
instance (Eq r, Field r) => ZeroProductSemiring (Unipol r)
instance (Eq r, Field r) => IntegralDomain (Unipol r)
instance (Eq r, Field r) => UFD (Unipol r)
instance (Eq r, Field r) => PID (Unipol r)
instance (Eq r, Field r) => Euclidean (Unipol r) where
  divide f g =
    if totalDegree' f `min` totalDegree' g < 50
    then divModUnipol f g
    else divModUnipolByMult f g
  degree f = if isZero f then Nothing else Just (fromIntegral $ totalDegree' f)

leadingTermIM :: Monoidal r => Unipol r -> (Int, r)
leadingTermIM = maybe (0, zero) fst . IM.maxViewWithKey . runUnipol
{-# INLINE leadingTermIM #-}

instance CoeffRing r => P.Num (Unipol r) where
  fromInteger = NA.fromInteger
  (+) = (NA.+)
  (*) = (NA.*)
  negate = NA.negate
  (-) = (NA.-)
  abs = id
  signum f =
    if isZero f
    then zero
    else one

varUnipol :: Unital r => SV.Ordinal 1 -> Unipol r
varUnipol _ = Unipol $ IM.singleton 1 one
{-# NOINLINE [1] varUnipol #-}

instance (Eq r, DecidableZero r) => Eq (Unipol r) where
  (==) = (==) `on` IM.filter (not . isZero) . runUnipol
  (/=) = (/=) `on` IM.filter (not . isZero) . runUnipol

instance (Ord r, DecidableZero r) => Ord (Unipol r) where
  compare = comparing runUnipol
  (<)  = (<) `on` runUnipol
  (>)  = (>) `on` runUnipol
  (<=) = (<=) `on` runUnipol
  (>=) = (>=) `on` runUnipol

-- | Polynomial multiplication, naive version.
naiveMult :: (DecidableZero r, Multiplicative r) => Unipol r -> Unipol r -> Unipol r
naiveMult (Unipol f) (Unipol g) =
  Unipol $
  IM.filter (not . isZero) $
  IM.fromListWith (+)
  [ (n+m, p*q)
  | (n, p) <- IM.toList f, (m, q) <- IM.toList g
  ]

-- | Polynomial multiplication using Karatsuba's method.
karatsuba :: forall r. CoeffRing r => Unipol r -> Unipol r -> Unipol r
karatsuba f0 g0 =
  let n0 = (totalDegree' f0 `max` totalDegree' g0) + 1
      -- The least @m@ such that deg(f), deg(g) <= 2^m - 1.
      m0  = toEnum $ ceilingLogBase2 n0
  in Unipol $ loop m0 (runUnipol f0) (runUnipol g0)
  where
    linearProduct op (a, b) (c, d) =
      let (ac, bd, abdc)  = (a `op` c, b `op` d, (a - b) `op` (d - c))
      in (ac, abdc + ac + bd, bd)
    {-# SPECIALISE INLINE
        linearProduct :: (r -> r -> r) -> (r, r) -> (r, r) -> (r, r, r)
     #-}
    {-# SPECIALISE INLINE
        linearProduct :: (Unipol r -> Unipol r -> Unipol r)
                      -> (Unipol r, Unipol r)
                      -> (Unipol r, Unipol r)
                      -> (Unipol r, Unipol r, Unipol r)
     #-}

    divideAt m h =
        let (l, mk, u) = IM.splitLookup m h
        in (maybe id (IM.insert 0) mk $ IM.mapKeysMonotonic (subtract m) u, l)
    {-# INLINE divideAt #-}

    xCoeff = IM.findWithDefault zero 1
    {-# INLINE xCoeff #-}
    cCoeff = IM.findWithDefault zero 0
    {-# INLINE cCoeff #-}

    loop !m !f !g
      | m <= 1 =
        let (a, b, c) =
              linearProduct (*)
              (xCoeff f, cCoeff f)
              (xCoeff g, cCoeff g)
        in IM.fromAscList $
           filter (not . isZero . snd)
           [(0, c), (1, b), (2, a)]
      | otherwise =
        let (f1, f2) = divideAt (2^(m P.- 1)) f -- f = f1 x^m + f2
            (g1, g2) = divideAt (2^(m P.- 1)) g -- g = g1 x^m + g2
            (Unipol m2, Unipol m1, Unipol c) =
              linearProduct ((Unipol .) . loop (m P.- 1) `on` runUnipol)
              (Unipol f1, Unipol f2)
              (Unipol g1, Unipol g2)
        in IM.unionsWith (+) [IM.mapKeysMonotonic (2^m+) m2,
                              IM.mapKeysMonotonic (2^(m P.- 1)+) m1, c]
{-# INLINABLE karatsuba #-}


decZero :: DecidableZero r => r -> Maybe r
decZero r = if isZero r then Nothing else Just r

instance (DecidableZero r) => Additive (Unipol r) where
  Unipol f + Unipol g =
    Unipol $ IM.mergeWithKey (\_ a b -> decZero (a + b)) id id f g

instance (DecidableZero r, Abelian r) => Abelian (Unipol r)

instance (DecidableZero r, RightModule Natural r) => RightModule Natural (Unipol r) where
  Unipol r *. n = Unipol $ IM.mapMaybe (decZero . (*. n)) r

instance (DecidableZero r, LeftModule Natural r) => LeftModule Natural (Unipol r) where
  n .* Unipol r = Unipol $ IM.mapMaybe (decZero . (n .*)) r

instance (DecidableZero r, RightModule Integer r) => RightModule Integer (Unipol r) where
  Unipol r *. n = Unipol $ IM.mapMaybe (decZero . (*. n)) r

instance (DecidableZero r, LeftModule Integer r) => LeftModule Integer (Unipol r) where
  n .* Unipol r = Unipol $ IM.mapMaybe (decZero . (n .*)) r

instance (CoeffRing r, Multiplicative r) => Multiplicative (Unipol r) where
  f * g =
    if totalDegree' f `min` totalDegree' g > 50
    then karatsuba f g
    else f `naiveMult` g

diffIMap :: (DecidableZero r, Group r) => IntMap r -> IntMap r -> IntMap r
diffIMap = IM.mergeWithKey (\_ a b -> decZero (a - b)) id (fmap negate)
{-# INLINE diffIMap #-}

instance (DecidableZero r, Group r) => Group (Unipol r) where
  negate (Unipol r)   = Unipol $ IM.map negate r
  {-# INLINE negate #-}

  Unipol f - Unipol g = Unipol $ diffIMap f g
  {-# INLINE (-) #-}

instance (CoeffRing r, Unital r) => Unital (Unipol r) where
  one = Unipol $ IM.singleton 0 one

instance (CoeffRing r, Commutative r) => Commutative (Unipol r)

instance (DecidableZero r, Semiring r) => LeftModule (Scalar r) (Unipol r) where
  Scalar q .* Unipol f
    | isZero q  = zero
    | otherwise = Unipol $ IM.mapMaybe (decZero . (q *)) f

instance (CoeffRing r, DecidableZero r) => Semiring (Unipol r)

instance (CoeffRing r, DecidableZero r) => Rig (Unipol r) where
  fromNatural 0 = Unipol IM.empty
  fromNatural n = Unipol $ IM.singleton 0 (fromNatural n)

instance (CoeffRing r, DecidableZero r) => Ring (Unipol r) where
  fromInteger 0 = Unipol IM.empty
  fromInteger n = Unipol $ IM.singleton 0 (fromInteger' n)

instance (DecidableZero r, Semiring r) => RightModule (Scalar r) (Unipol r) where
  Unipol f *. Scalar q
    | isZero q  = zero
    | otherwise = Unipol $ IM.mapMaybe (decZero . (* q)) f

instance DecidableZero r => Monoidal (Unipol r) where
  zero = Unipol IM.empty

instance DecidableZero r => DecidableZero (Unipol r) where
  isZero = IM.null . runUnipol

instance CoeffRing r => IsPolynomial (Unipol r) where
  type Arity (Unipol r) = 1
  type Coefficient (Unipol r) = r
  injectCoeff r =
    if   isZero r
    then zero
    else Unipol $ IM.singleton 0 r
  {-# INLINE injectCoeff #-}
  coeff' l = IM.findWithDefault zero (SV.head l) . runUnipol
  {-# INLINE coeff' #-}
  monomials = HS.fromList . map singleton . IM.keys . runUnipol
  {-# INLINE monomials #-}
  terms' = M.fromList . map (first singleton) . IM.toList . runUnipol
  {-# INLINE terms' #-}
  sArity _ = sing
  sArity' _ = sing
  arity _ = 1
  constantTerm = IM.findWithDefault zero 0 . runUnipol
  {-# INLINE constantTerm #-}
  liftMap = liftMapUnipol
  {-# INLINABLE liftMap #-}
  substWith = substWithUnipol
  {-# INLINE substWith #-}
  fromMonomial = Unipol . flip IM.singleton one . SV.head
  {-# INLINE fromMonomial #-}
  toPolynomial' (c, m) =
    if isZero c
    then Unipol IM.empty
    else Unipol $ IM.singleton (SV.head m) c
  {-# INLINE toPolynomial' #-}
  polynomial' = Unipol . IM.fromList
              . mapMaybe (\(s, v) -> if isZero v then Nothing else Just (SV.head s, v))
              . M.toList
  {-# INLINE polynomial' #-}
  totalDegree' = maybe 0 (fst . fst) . IM.maxViewWithKey . runUnipol
  {-# INLINE totalDegree' #-}
  var = varUnipol
  mapCoeff' f = Unipol . IM.mapMaybe (decZero . f) . runUnipol
  {-# INLINE mapCoeff' #-}
  m >|* Unipol dic =
    let n = SV.head m
    in if n == 0
       then Unipol dic
       else Unipol $ IM.mapKeysMonotonic (n +) dic
  {-# INLINE (>|*) #-}

instance CoeffRing r => IsOrderedPolynomial (Unipol r) where
  type MOrder (Unipol r) = Grevlex
  terms = M.mapKeysMonotonic (orderMonomial (Nothing :: Maybe Grevlex)) . terms'
  leadingTerm =
    maybe (zero, one)
          (\((a, b),_) -> (b, OrderedMonomial $ SV.singleton a))
    . IM.maxViewWithKey . runUnipol
  {-# INLINE leadingTerm #-}
  splitLeadingTerm  =
    maybe ((zero, one), zero)
          (\((a, b),d) -> ((b, OrderedMonomial $ SV.singleton a), Unipol d))
    . IM.maxViewWithKey . runUnipol
  {-# INLINE splitLeadingTerm #-}

instance (CoeffRing r, PrettyCoeff r) => Show (Unipol r) where
  showsPrec = showsPolynomialWith (SV.singleton "x")

mapCoeffUnipol :: DecidableZero b => (a -> b) -> Unipol a -> Unipol b
mapCoeffUnipol f (Unipol a) =
  Unipol $ IM.mapMaybe (decZero . f) a
{-# INLINE mapCoeffUnipol #-}

liftMapUnipol :: (Module (Scalar k) r, Monoidal k, Unital r)
              => (Ordinal 1 -> r) -> Unipol k -> r
liftMapUnipol g f@(Unipol dic) =
    let u = g 0
        n = maybe 0 (fst . fst) $ IM.maxViewWithKey $ runUnipol f
    in foldr (\a b -> a .*. one + b * u)
             (IM.findWithDefault zero n dic .*. one)
             [IM.findWithDefault zero k dic | k <- [0..n-1]]
{-# INLINE liftMapUnipol #-}

substWithUnipol :: (Ring m, CoeffRing k)
                => (k -> m -> m)
                -> Sized 1 m
                -> Unipol k -> m
substWithUnipol (|*) g f@(Unipol dic) =
    let u = g SV.%!! 0
        n = maybe 0 (fst . fst) $ IM.maxViewWithKey $ runUnipol f
    in foldr (\a b -> (a |* one) + (b * u))
             (IM.findWithDefault zero n dic |* one)
             [IM.findWithDefault zero k dic | k <- [0..n-1]]
{-# INLINE substWithUnipol #-}

-- | The list of coefficients, in ascending order.
coeffList :: Monoidal k => Unipol k -> [k]
coeffList (Unipol dic) =
  F.toList $ IM.unionWith (+) dic $
  IM.fromList [(n, zero) | n <- [0..maybe (- 1) (fst . fst) (IM.maxViewWithKey dic)] ]
