{-# LANGUAGE BangPatterns, ConstraintKinds, DataKinds, FlexibleContexts #-}
{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, MultiParamTypeClasses   #-}
{-# LANGUAGE NoImplicitPrelude, ScopedTypeVariables, StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies, UndecidableSuperClasses                      #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
-- | Polynomial type optimized to univariate polynomial.
module Algebra.Ring.Polynomial.Univariate
       (Unipol, naiveMult, karatsuba,
        module Algebra.Ring.Polynomial.Class,
        module Algebra.Ring.Polynomial.Monomial) where
import Algebra.Prelude
import Algebra.Ring.Polynomial.Class
import Algebra.Ring.Polynomial.Monomial

import           Control.Arrow          (first)
import           Control.DeepSeq        (NFData)
import           Data.Bits              (Bits (..), FiniteBits (..))
import           Data.Function          (on)
import           Data.Hashable          (Hashable (hashWithSalt))
import qualified Data.HashSet           as HS
import qualified Data.IntMap            as IM
import qualified Data.Map.Strict        as M
import           Data.MonoTraversable   (oall)
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

instance Hashable r => Hashable (Unipol r) where
  hashWithSalt p = hashWithSalt p . IM.toList . runUnipol

normaliseUP :: DecidableZero r => Unipol r -> Unipol r
normaliseUP (Unipol r) = Unipol $ IM.filter (not . isZero) r

instance CoeffRing r => P.Num (Unipol r) where
  fromInteger = fromInteger
  (+) = (NA.+)
  (*) = (NA.*)
  negate = NA.negate
  (-) = (NA.-)
  abs = id
  signum f =
    if isZero f
    then zero
    else one


instance (Eq r, DecidableZero r) => Eq (Unipol r) where
  (==) = (==) `on` IM.filter (not . isZero) . runUnipol
  (/=) = (/=) `on` IM.filter (not . isZero) . runUnipol

instance (Ord r, DecidableZero r) => Ord (Unipol r) where
  compare = comparing (runUnipol . normaliseUP)
  (<)  = (<)  `on` IM.filter (not . isZero) . runUnipol
  (>)  = (>)  `on` IM.filter (not . isZero) . runUnipol
  (<=) = (<=) `on` IM.filter (not . isZero) . runUnipol
  (>=) = (>=) `on` IM.filter (not . isZero) . runUnipol


logBase2 :: Int -> Int
logBase2 x = finiteBitSize x - 1 - countLeadingZeros x
{-# INLINE logBase2 #-}

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
  let n0 = fromIntegral $ totalDegree' f0 `max` totalDegree' g0
      -- The least @m@ such that deg(f), deg(g) <= 2^m - 1.
      m0  = if popCount n0 == 1
            then logBase2 n0 + 1
            else logBase2 (n0 + 1)
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
        in (maybe id (IM.insert 0) mk $ IM.mapKeys (subtract m) u, l)
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
        let (f1, f2) = divideAt m f -- f = f1 x^m + f2
            (g1, g2) = divideAt m g -- g = g1 x^m + g2
            (Unipol m2, Unipol m1, Unipol c) =
              linearProduct ((Unipol .) . loop (m - 1) `on` runUnipol)
              (Unipol f1, Unipol f2)
              (Unipol g1, Unipol g2)
        in IM.unionsWith (+) [IM.mapKeys (2*m+) m2, IM.mapKeys (m+) m1, c]
{-# INLINABLE karatsuba #-}


decZero :: DecidableZero r => r -> Maybe r
decZero r = if isZero r then Nothing else Just r

instance (DecidableZero r)=> Additive (Unipol r) where
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
  (*) = karatsuba

instance (DecidableZero r, Group r) => Group (Unipol r) where
  negate (Unipol r)   = Unipol $ IM.map negate r
  Unipol f - Unipol g = Unipol $ IM.mergeWithKey (\_ a b -> decZero (a - b)) id (fmap negate) f g

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
  fromInteger n = Unipol $ IM.singleton 0 (fromInteger n)

instance (DecidableZero r, Semiring r) => RightModule (Scalar r) (Unipol r) where
  Unipol f *. Scalar q
    | isZero q  = zero
    | otherwise = Unipol $ IM.mapMaybe (decZero . (* q)) f

instance DecidableZero r => Monoidal (Unipol r) where
  zero = Unipol IM.empty

instance DecidableZero r => DecidableZero (Unipol r) where
  isZero = oall isZero . runUnipol

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
  monomials = HS.fromList . map (singleton) . IM.keys . runUnipol
  {-# INLINE monomials #-}
  terms' = M.fromList . map (first singleton) . IM.toList . runUnipol
  {-# INLINE terms' #-}
  sArity _ = sing
  sArity' _ = sing
  arity _ = 1
  constantTerm = IM.findWithDefault zero 0 . runUnipol
  {-# INLINE constantTerm #-}
  liftMap g f@(Unipol dic) =
    let u = g 0
        n = maybe 0 (fst . fst) $ IM.maxViewWithKey $ runUnipol f
    in foldr (\a b -> a .*. one + b * u)
             (IM.findWithDefault zero n dic .*. one)
             [IM.findWithDefault zero k dic | k <- [0..n-1]]
  {-# INLINABLE liftMap #-}
  fromMonomial = Unipol . flip IM.singleton one . SV.head
  {-# INLINE fromMonomial #-}
  toPolynomial' (c, m) = Unipol $ IM.singleton (SV.head m) c
  {-# INLINE toPolynomial' #-}
  polynomial' = Unipol . IM.fromList . map (first SV.head) . M.toList
  {-# INLINE polynomial' #-}
  totalDegree' = fromIntegral . maybe 0 (fst . fst) . IM.maxViewWithKey . runUnipol
  {-# INLINE totalDegree' #-}
  var _ = Unipol $ IM.singleton 1 one
  {-# INLINE var #-}
  mapCoeff' f = Unipol . IM.mapMaybe (decZero . f) . runUnipol
  {-# INLINE mapCoeff' #-}
  m >|* Unipol dic =
    let n = SV.head m
    in if n == 0
       then Unipol dic
       else Unipol $ IM.mapKeys (n +) dic
  {-# INLINE (>|*) #-}

instance CoeffRing r => IsOrderedPolynomial (Unipol r) where
  type MOrder (Unipol r) = Grevlex
  terms = M.mapKeys (orderMonomial (Nothing :: Maybe Grevlex)) . terms'
  leadingTerm =
    maybe (zero, one)
          (\((a, b),_) -> (b, OrderedMonomial $ SV.singleton a))
    . IM.maxViewWithKey . runUnipol
  {-# INLINE leadingTerm #-}

instance (CoeffRing r, PrettyCoeff r) => Show (Unipol r) where
  showsPrec = showsPolynomialWith (SV.singleton "x")
