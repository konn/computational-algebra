{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Partial fraction decomposition for unary polynomials
module Algebra.Ring.Fraction.Decomp where

import Algebra.Prelude.Core
import Algebra.Ring.Euclidean.Quotient
import Algebra.Ring.Polynomial.Univariate
import Data.Functor ((<&>))
import qualified Data.IntMap.Strict as IM
import Data.List.NonEmpty (NonEmpty (..))
import Data.Monoid (Dual (..))

data PartialFractionDecomp k = PartialFraction
  { residualPoly :: Unipol k
  , partialFracs :: NonEmpty (Unipol k, IntMap (Unipol k))
  }
  deriving (Show, Eq, Ord)

partialFractionDecomposition ::
  (Field k, CoeffRing k, Functor m) =>
  (Unipol k -> m (k, NonEmpty (Unipol k, Natural))) ->
  Fraction (Unipol k) ->
  m (PartialFractionDecomp k)
partialFractionDecomposition factor q =
  let g0 = numerator q
      f0 = denominator q
      g = recip (leadingCoeff f0) .*. g0
      f = monoize f0
   in factor f <&> \(k, fs) ->
        scalePF k $ partialFractionDecompositionWith g fs

scalePF :: (CoeffRing k) => k -> PartialFractionDecomp k -> PartialFractionDecomp k
scalePF c pf =
  PartialFraction
    { residualPoly = c .*. residualPoly pf
    , partialFracs = second (fmap (c .*.)) <$> partialFracs pf
    }

{- | Calculates the partial fraction decomposition
with respect to the given pairwise coprime
monic factorisation of the denominator.

>>> partialFractionDecompositionWith (#x ^ 3 + 4 * #x^2 - #x - 2 :: Unipol Rational) ((#x, 2) :| [(#x - 1, 1), (#x + 1, 1)])
(x,fromList [(1,1),(2,2)]) :| [(x - 1,fromList [(1,1)]),(x + 1,fromList [(1,-1)])]
-}
partialFractionDecompositionWith ::
  (CoeffRing k, Field k) =>
  -- | Numerator
  Unipol k ->
  -- | Pairwise coprime (partial) factorisation of
  -- denominator \(f = \sum_i f_i^{e_i}\) with each
  -- \(f_i\) monic and non-constant.
  NonEmpty (Unipol k, Natural) ->
  PartialFractionDecomp k
partialFractionDecompositionWith g fs =
  let f = runMult $ foldMap (Mult . uncurry (^)) fs
      (q, r)
        | degree g < degree f = (zero, g)
        | otherwise = g `divModUnipol` f
      pf = poweredPartialFraction r fs
      pows =
        pf <&> \((fi, e), gi) ->
          (fi, IM.mapKeys (fromIntegral e -) $ pAdicExpansion gi fi)
   in PartialFraction q pows

{- | @'pAdicExpansion' f p@ gives a @p@-adic expansion of @f@ by a monic nonconstant polynomial @p@; i.e. \(a_i \in k[X]\) such that \(\deg a_i < \deg p\)_{i < k}, \(\deg f < km\), and:

\[
  f = a_{k - 1} p^{k-1} + \cdots + a_1 p + a_0.
\]

>>> pAdicExpansion (#x + 2 :: Unipol Rational) #x
fromList [(0,2),(1,1)]
-}
pAdicExpansion ::
  (Field k, CoeffRing k) =>
  Unipol k ->
  Unipol k ->
  IntMap (Unipol k)
pAdicExpansion f p = loop 0 f IM.empty
  where
    !degp = degree p
    loop !n !ai !acc
      | degree ai < degp =
        if isZero ai then acc else IM.insert n ai acc
      | otherwise =
        let (q, r) = ai `divModUnipol` p
            !acc'
              | isZero r = acc
              | otherwise = IM.insert n r acc
         in loop (n + 1) q acc'

-- >>> poweredPartialFraction (#x ^ 3 + 4 * #x^2 - #x - 2 :: Unipol Rational) ((#x, 2) :| [(#x - 1, 1), (#x + 1, 1)])
-- ((x,2),x + 2) :| [((x - 1,1),1),((x + 1,1),-1)]

-- | Pseudo-partial fraction decomposition
poweredPartialFraction ::
  forall k.
  (Field k, CoeffRing k) =>
  -- | Numerator @g@ with \(\deg g < \deg f).
  Unipol k ->
  -- | Pairwise coprime (partial) factorisation of
  -- denominator \(f = \sum_i f_i^{e_i}\) with each
  -- \(f_i\) monic and non-constant.
  NonEmpty (Unipol k, Natural) ->
  NonEmpty ((Unipol k, Natural), Unipol k)
poweredPartialFraction g = scanZipper ci
  where
    invert (fi, ei) =
      fromMaybe (error "Not coprime!") (recipUnit $ quotient fi) ^ ei
    ci ((f, e) :| fs) xs =
      let fe = f ^ e
       in ( (f, e)
          , withQuotient fe $
              quotient
                g
                * runMult (getDual (foldMap (Dual . Mult . invert) xs))
                * runMult (foldMap (Mult . invert) fs)
          )

scanZipper :: (NonEmpty a -> [a] -> b) -> NonEmpty a -> NonEmpty b
{-# INLINE scanZipper #-}
scanZipper f (x0 :| ini) = f (x0 :| ini) [] :| go ini [x0]
  where
    go [] _ = []
    go (x : xs) rest = f (x :| xs) rest : go xs (x : rest)
