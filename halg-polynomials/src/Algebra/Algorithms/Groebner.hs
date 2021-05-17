{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Algebra.Algorithms.Groebner
  ( -- * Groebner basis
    isGroebnerBasis,
    calcGroebnerBasis,
    calcGroebnerBasisWith,
    calcGroebnerBasisWithStrategy,
    buchberger,
    syzygyBuchberger,
    simpleBuchberger,
    primeTestBuchberger,
    reduceMinimalGroebnerBasis,
    minimizeGroebnerBasis,

    -- ** Selection Strategies
    syzygyBuchbergerWithStrategy,
    module Algebra.Algorithms.Groebner.SelectionStrategy,

    -- * Ideal operations
    isIdealMember,
    intersection,
    thEliminationIdeal,
    thEliminationIdealWith,
    unsafeThEliminationIdealWith,
    eliminatePadding,
    quotIdeal,
    quotByPrincipalIdeal,
    saturationIdeal,
    saturationByPrincipalIdeal,

    -- * Resultant
    resultant,
    hasCommonFactor,
    lcmPolynomial,
    gcdPolynomial,
  )
where

import Algebra.Algorithms.Groebner.SelectionStrategy
import Algebra.Internal
import Algebra.Prelude.Core
import Algebra.Ring.Polynomial.Univariate (Unipol)
import Control.Monad.Loops (whileM_)
import Control.Monad.ST (ST, runST)
import qualified Data.Foldable as F
import qualified Data.Heap as H
import Data.MonoTraversable (oall)
import Data.STRef (STRef, modifySTRef, modifySTRef', newSTRef, readSTRef, writeSTRef)
import Data.Sequence (Seq ((:<|)))
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
#if MIN_VERSION_singletons(3,0,0)
import Data.List.Singletons
#else
import Data.Singletons.Prelude.List
#endif
import qualified Data.Sized as V
import Data.Type.Natural.Lemma.Arithmetic (plusCongR, plusMinus')
import Unsafe.Coerce (unsafeCoerce)
import qualified Prelude as P

-- | Test if the given ideal is Groebner basis, using Buchberger criteria and relatively primeness.
isGroebnerBasis ::
  (IsOrderedPolynomial poly, Field (Coefficient poly)) =>
  Ideal poly ->
  Bool
isGroebnerBasis (nub . generators -> ideal) = all check $ combinations ideal
  where
    check (f, g) =
      let (t, u) = (leadingMonomial f, leadingMonomial g)
       in t * u == lcmMonomial t u || sPolynomial f g `modPolynomial` ideal == zero

-- | The Naive buchberger's algorithm to calculate Groebner basis for the given ideal.
simpleBuchberger ::
  (Field (Coefficient poly), IsOrderedPolynomial poly) =>
  Ideal poly ->
  [poly]
simpleBuchberger ideal =
  let gs = nub $ generators ideal
   in fst $
        until
          (null . snd)
          ( \(ggs, acc) ->
              let cur = nub $ ggs ++ acc
               in (cur, calc cur)
          )
          (gs, calc gs)
  where
    calc acc =
      [ q | f <- acc, g <- acc, let q = sPolynomial f g `modPolynomial` acc, q /= zero
      ]

-- | Buchberger's algorithm slightly improved by discarding relatively prime pair.
primeTestBuchberger ::
  (Field (Coefficient poly), IsOrderedPolynomial poly) =>
  Ideal poly ->
  [poly]
primeTestBuchberger ideal =
  let gs = nub $ generators ideal
   in fst $
        until
          (null . snd)
          ( \(ggs, acc) ->
              let cur = nub $ ggs ++ acc
               in (cur, calc cur)
          )
          (gs, calc gs)
  where
    calc acc =
      [ q | f <- acc, g <- acc, f /= g, let f0 = leadingMonomial f, let g0 = leadingMonomial g, lcmMonomial f0 g0 /= f0 * g0, let q = sPolynomial f g `modPolynomial` acc, q /= zero
      ]

(.=) :: STRef s a -> a -> ST s ()
x .= v = writeSTRef x v

(%=) :: STRef s a -> (a -> a) -> ST s ()
x %= f = modifySTRef x f

combinations :: [a] -> [(a, a)]
combinations xs = concat $ zipWith (map . (,)) xs $ drop 1 $ tails xs
{-# INLINE combinations #-}

{- | Calculate Groebner basis applying (modified) Buchberger's algorithm.
 This function is same as 'syzygyBuchberger'.
-}
buchberger ::
  (Field (Coefficient poly), IsOrderedPolynomial poly) =>
  Ideal poly ->
  [poly]
buchberger = syzygyBuchberger

{- | Buchberger's algorithm greately improved using the syzygy theory with the sugar strategy.
 Utilizing priority queues, this function reduces division complexity and comparison time.
 If you don't have strong reason to avoid this function, this function is recommended to use.
-}
syzygyBuchberger ::
  (Field (Coefficient poly), IsOrderedPolynomial poly) =>
  Ideal poly ->
  [poly]
syzygyBuchberger = syzygyBuchbergerWithStrategy (SugarStrategy NormalStrategy)
{-# SPECIALIZE INLINE [0] syzygyBuchberger ::
  (CoeffRing r, Field r, IsMonomialOrder n ord, KnownNat n) =>
  Ideal (OrderedPolynomial r ord n) ->
  [OrderedPolynomial r ord n]
  #-}
{-# SPECIALIZE INLINE [0] syzygyBuchberger ::
  (CoeffRing r, Field r) =>
  Ideal (Unipol r) ->
  [Unipol r]
  #-}
{-# INLINE [1] syzygyBuchberger #-}

-- | apply buchberger's algorithm using given selection strategy.
syzygyBuchbergerWithStrategy ::
  ( Field (Coefficient poly)
  , IsOrderedPolynomial poly
  , SelectionStrategy (Arity poly) strategy
  , Ord (Weight (Arity poly) strategy (MOrder poly))
  ) =>
  strategy ->
  Ideal poly ->
  [poly]
syzygyBuchbergerWithStrategy strategy ideal = runST $ do
  let gens = zip [1 ..] $ filter (/= zero) $ generators ideal
  gs <- newSTRef $ H.fromList [H.Entry (leadingMonomial g) g | (_, g) <- gens]
  b <- newSTRef $ H.fromList [H.Entry (calcWeight' strategy f g, j) (f, g) | ((_, f), (j, g)) <- combinations gens]
  len <- newSTRef (genericLength gens :: Integer)
  whileM_ (not . H.null <$> readSTRef b) $ do
    Just (H.Entry _ (f, g), rest) <- H.viewMin <$> readSTRef b
    gs0 <- readSTRef gs
    b .= rest
    let f0 = leadingMonomial f
        g0 = leadingMonomial g
        l = lcmMonomial f0 g0
        redundant =
          F.any
            ( \(H.Entry _ h) ->
                (h `notElem` [f, g])
                  && all
                    (\k -> F.all ((/= k) . H.payload) rest)
                    [(f, h), (g, h), (h, f), (h, g)]
                  && leadingMonomial h `divs` l
            )
            gs0
    when (l /= f0 * g0 && not redundant) $ do
      len0 <- readSTRef len
      let qs = F.toList gs0
          s = sPolynomial f g `modPolynomial` map H.payload qs
      when (s /= zero) $ do
        b %= H.union (H.fromList [H.Entry (calcWeight' strategy q s, j) (q, s) | H.Entry _ q <- qs | j <- [len0 + 1 ..]])
        gs %= H.insert (H.Entry (leadingMonomial s) s)
        len %= (* 2)
  map H.payload . F.toList <$> readSTRef gs
{-# SPECIALIZE INLINE [0] syzygyBuchbergerWithStrategy ::
  (Field k, CoeffRing k, KnownNat n) =>
  SugarStrategy NormalStrategy ->
  Ideal (OrderedPolynomial k Grevlex n) ->
  [OrderedPolynomial k Grevlex n]
  #-}
{-# SPECIALIZE INLINE [0] syzygyBuchbergerWithStrategy ::
  (Field k, CoeffRing k) =>
  SugarStrategy NormalStrategy ->
  Ideal (Unipol k) ->
  [Unipol k]
  #-}
{-# SPECIALIZE INLINE [1] syzygyBuchbergerWithStrategy ::
  (Field k, CoeffRing k, KnownNat n, IsMonomialOrder n ord) =>
  SugarStrategy NormalStrategy ->
  Ideal (OrderedPolynomial k ord n) ->
  [OrderedPolynomial k ord n]
  #-}
{-# SPECIALIZE INLINE [1] syzygyBuchbergerWithStrategy ::
  ( Field k
  , CoeffRing k
  , IsMonomialOrder n ord
  , SelectionStrategy n strategy
  , KnownNat n
  , Ord (Weight n strategy ord)
  ) =>
  strategy ->
  Ideal (OrderedPolynomial k ord n) ->
  [OrderedPolynomial k ord n]
  #-}
{-# INLINEABLE [2] syzygyBuchbergerWithStrategy #-}

data PolyEntry p = PE
  { leadMon :: !(OrderedMonomial (MOrder p) (Arity p))
  , poly :: p
  }

instance IsOrderedPolynomial p => Eq (PolyEntry p) where
  (==) = (==) `on` leadMon
  {-# INLINE (==) #-}

instance IsOrderedPolynomial p => Ord (PolyEntry p) where
  compare = comparing leadMon
  {-# INLINE compare #-}

toPE :: (Field (Coefficient p), IsOrderedPolynomial p) => p -> PolyEntry p
toPE p = PE (leadingMonomial p) $ monoize p
{-# INLINE toPE #-}

divsPE :: IsOrderedPolynomial p => PolyEntry p -> PolyEntry p -> Bool
divsPE = divs `on` leadMon
{-# INLINE divsPE #-}

insPE :: (Field (Coefficient p), IsOrderedPolynomial p) => p -> Set (PolyEntry p) -> Set (PolyEntry p)
insPE p s
  | Set.null s = Set.singleton $ toPE p
  | otherwise =
    let pe = toPE p
        (l, there, r) = Set.splitMember pe s -- log(k)
     in if there || F.any (`divsPE` pe) l -- k
          then s
          else Set.union l (Set.insert pe $ Set.filter (not . (pe `divsPE`)) r) -- log(k) + k
{-# INLINE insPE #-}

-- | Minimises a Groebner basis
minimizeGroebnerBasis ::
  (Foldable t, Field (Coefficient poly), IsOrderedPolynomial poly) =>
  t poly ->
  [poly]
minimizeGroebnerBasis = map poly . Set.toList . F.foldr insPE Set.empty
{-# INLINE minimizeGroebnerBasis #-}

-- | Reduce minimum Groebner basis into the reduced Groebner basis.
reduceMinimalGroebnerBasis ::
  (Foldable t, Field (Coefficient poly), IsOrderedPolynomial poly) =>
  t poly ->
  [poly]
reduceMinimalGroebnerBasis bs = runST $ do
  left <- newSTRef $ Seq.fromList $ F.toList bs
  right <- newSTRef Seq.empty
  whileM_ (not . Seq.null <$> readSTRef left) $ do
    f :<| xs <- readSTRef left
    writeSTRef left xs
    ys <- readSTRef right
    let q = f `modPolynomial` (xs Seq.>< ys)
    unless (isZero q) $ modifySTRef' right (q :<|)
  F.toList <$> readSTRef right

-- | Caliculating reduced Groebner basis of the given ideal w.r.t. the specified monomial order.
calcGroebnerBasisWith ::
  ( IsOrderedPolynomial poly
  , Field (Coefficient poly)
  , IsMonomialOrder (Arity poly) order
  ) =>
  order ->
  Ideal poly ->
  [OrderedPolynomial (Coefficient poly) order (Arity poly)]
calcGroebnerBasisWith _ord = calcGroebnerBasis . mapIdeal injectVars
{-# INLINE [2] calcGroebnerBasisWith #-}

{-# RULES
"calcGroebnerBasisWith/sameOrderPolyn" [~2] forall x.
  calcGroebnerBasisWith x =
    calcGroebnerBasis
  #-}

-- | Caliculating reduced Groebner basis of the given ideal w.r.t. the specified monomial order.
calcGroebnerBasisWithStrategy ::
  ( Field (Coefficient poly)
  , IsOrderedPolynomial poly
  , SelectionStrategy (Arity poly) strategy
  , Ord (Weight (Arity poly) strategy (MOrder poly))
  ) =>
  strategy ->
  Ideal poly ->
  [poly]
calcGroebnerBasisWithStrategy strategy =
  reduceMinimalGroebnerBasis . minimizeGroebnerBasis . syzygyBuchbergerWithStrategy strategy

-- | Caliculating reduced Groebner basis of the given ideal.
calcGroebnerBasis ::
  (Field (Coefficient poly), IsOrderedPolynomial poly) =>
  Ideal poly ->
  [poly]
calcGroebnerBasis = reduceMinimalGroebnerBasis . minimizeGroebnerBasis . syzygyBuchberger
{-# SPECIALIZE INLINE [2] calcGroebnerBasis ::
  (CoeffRing r, Field r, IsMonomialOrder n ord, KnownNat n) =>
  Ideal (OrderedPolynomial r ord n) ->
  [OrderedPolynomial r ord n]
  #-}
{-# SPECIALIZE INLINE [2] calcGroebnerBasis ::
  (CoeffRing r, Field r) =>
  Ideal (Unipol r) ->
  [Unipol r]
  #-}
{-# INLINE [2] calcGroebnerBasis #-}

-- | Test if the given polynomial is the member of the ideal.
isIdealMember ::
  (Field (Coefficient poly), IsOrderedPolynomial poly) =>
  poly ->
  Ideal poly ->
  Bool
isIdealMember f ideal = groebnerTest f (calcGroebnerBasis ideal)
{-# INLINE isIdealMember #-}

-- | Test if the given polynomial can be divided by the given polynomials.
groebnerTest ::
  (Field (Coefficient poly), IsOrderedPolynomial poly) =>
  poly ->
  [poly] ->
  Bool
groebnerTest f fs = f `modPolynomial` fs == zero

lengthReplicate :: forall m x p. SNat m -> p x -> Length (Replicate m x) :~: m
lengthReplicate _ _ = unsafeCoerce $ Refl @()

-- | Calculate n-th elimination ideal using 'WeightedEliminationOrder' ordering.
thEliminationIdeal ::
  forall poly n.
  ( IsMonomialOrder (Arity poly - n) (MOrder poly)
  , Field (Coefficient poly)
  , IsOrderedPolynomial poly
  , (n <= Arity poly)
  ) =>
  SNat n ->
  Ideal poly ->
  Ideal (OrderedPolynomial (Coefficient poly) (MOrder poly) (Arity poly - n))
thEliminationIdeal n =
  withSingI (sOnes n) $
    withRefl (lengthReplicate n (sNat @1)) $
      withKnownNat n $
        withKnownNat ((sNat :: SNat (Arity poly)) %- n) $
          mapIdeal (changeOrderProxy Proxy) . thEliminationIdealWith (weightedEliminationOrder n) n
{-# INLINE CONLIKE thEliminationIdeal #-}

-- | Calculate n-th elimination ideal using the specified n-th elimination type order.
thEliminationIdealWith ::
  ( IsOrderedPolynomial poly
  , m ~ Arity poly
  , k ~ Coefficient poly
  , Field k
  , KnownNat (m - n)
  , (n <= m)
  , EliminationType m n ord
  ) =>
  ord ->
  SNat n ->
  Ideal poly ->
  Ideal (OrderedPolynomial k Grevlex (m - n))
thEliminationIdealWith = unsafeThEliminationIdealWith

{- | Calculate n-th elimination ideal using the specified n-th elimination type order.
 This function should be used carefully because it does not check whether the given ordering is
 n-th elimintion type or not.
-}
unsafeThEliminationIdealWith ::
  ( IsOrderedPolynomial poly
  , m ~ Arity poly
  , k ~ Coefficient poly
  , Field k
  , IsMonomialOrder m ord
  , (n <= m)
  ) =>
  ord ->
  SNat n ->
  Ideal poly ->
  Ideal (OrderedPolynomial k Grevlex (m - n))
unsafeThEliminationIdealWith ord n ideal =
  withKnownNat n $
    toIdeal
      [ transformMonomial (V.drop n) f
      | f <- calcGroebnerBasisWith ord ideal
      , all (oall (== 0) . V.takeAtMost n . getMonomial . snd) $ getTerms f
      ]
{-# INLINE CONLIKE unsafeThEliminationIdealWith #-}

eliminatePadding ::
  ( IsOrderedPolynomial poly
  , IsMonomialOrder n ord
  , Field (Coefficient poly)
  , SingI (Replicate n 1)
  , KnownNat n
  ) =>
  Ideal (PadPolyL n ord poly) ->
  Ideal poly
eliminatePadding ideal =
  toIdeal
    [ c
    | f0 <- calcGroebnerBasis ideal
    , let (c, m) = leadingTerm $ runPadPolyL f0
    , m == one
    ]
{-# INLINE CONLIKE eliminatePadding #-}

-- | An intersection ideal of given ideals (using 'WeightedEliminationOrder').
intersection ::
  forall poly.
  (Field (Coefficient poly), IsOrderedPolynomial poly) =>
  [Ideal poly] ->
  Ideal poly
intersection ideals
  | null ideals = principalIdeal one
  | otherwise =
    case toSomeSNat $ fromIntegral $ F.length ideals of
      SomeSNat sk ->
        withSingI (sOnes sk) $
          withKnownNat sk $
            let ts = genericTake (toNatural sk) vars
                inj = padLeftPoly sk Grevlex
                tis = zipWith (\ideal t -> mapIdeal ((t *) . inj) ideal) (F.toList ideals) ts
                j = foldr appendIdeal (principalIdeal (one - foldr (+) zero ts)) tis
             in eliminatePadding j
{-# INLINE CONLIKE intersection #-}

-- | Ideal quotient by a principal ideals.
quotByPrincipalIdeal ::
  (Field (Coefficient poly), IsOrderedPolynomial poly) =>
  Ideal poly ->
  poly ->
  Ideal poly
quotByPrincipalIdeal i g =
  fmap (snd . head . (`divPolynomial` [g])) $ intersection [i, principalIdeal g]
{-# INLINE CONLIKE quotByPrincipalIdeal #-}

-- | Ideal quotient by the given ideal.
quotIdeal ::
  forall poly.
  (IsOrderedPolynomial poly, Field (Coefficient poly)) =>
  Ideal poly ->
  Ideal poly ->
  Ideal poly
quotIdeal i g =
  intersection $ map (i `quotByPrincipalIdeal`) $ F.toList g
{-# INLINE CONLIKE quotIdeal #-}

-- | Saturation by a principal ideal.
saturationByPrincipalIdeal ::
  forall poly.
  (IsOrderedPolynomial poly, Field (Coefficient poly)) =>
  Ideal poly ->
  poly ->
  Ideal poly
saturationByPrincipalIdeal is g =
  let n = sArity' g
   in withKnownNat n $
        eliminatePadding $
          addToIdeal (one - (padLeftPoly (sNat @1) Grevlex g * var 0)) $
            mapIdeal (padLeftPoly (sNat @1) Grevlex) is
{-# INLINE CONLIKE saturationByPrincipalIdeal #-}

-- | Saturation ideal
saturationIdeal ::
  forall poly.
  ( Field (Coefficient poly)
  , IsOrderedPolynomial poly
  ) =>
  Ideal poly ->
  Ideal poly ->
  Ideal poly
saturationIdeal i g =
  intersection $ map (i `saturationByPrincipalIdeal`) $ F.toList g
{-# INLINE CONLIKE saturationIdeal #-}

-- | Calculate resultant for given two unary polynomimals.
resultant ::
  forall poly.
  ( Field (Coefficient poly)
  , IsOrderedPolynomial poly
  , Arity poly ~ 1
  ) =>
  poly ->
  poly ->
  Coefficient poly
resultant = go one
  where
    go res h s
      | totalDegree' s > 0 =
        let r = h `modPolynomial` [s]
            res' =
              res * negate one ^ fromIntegral (totalDegree' h * totalDegree' s)
                * leadingCoeff s ^ fromIntegral (totalDegree' h P.- totalDegree' r)
         in go res' s r
      | isZero h || isZero s = zero
      | totalDegree' h > 0 = (leadingCoeff s ^ fromIntegral (totalDegree' h)) * res
      | otherwise = res

    _ = Refl :: Arity poly :~: 1

-- to suppress "redundant" warning for univariate constraint.

-- | Determine whether two polynomials have a common factor with positive degree using resultant.
hasCommonFactor ::
  ( Field (Coefficient poly)
  , IsOrderedPolynomial poly
  , Arity poly ~ 1
  ) =>
  poly ->
  poly ->
  Bool
hasCommonFactor f g = isZero $ resultant f g

-- | Calculates the Least Common Multiply of the given pair of polynomials.
lcmPolynomial ::
  forall poly.
  ( Field (Coefficient poly)
  , IsOrderedPolynomial poly
  ) =>
  poly ->
  poly ->
  poly
lcmPolynomial f g = head $ generators $ intersection [principalIdeal f, principalIdeal g]
{-# INLINE lcmPolynomial #-}

-- | Calculates the Greatest Common Divisor of the given pair of polynomials.
gcdPolynomial ::
  ( Field (Coefficient poly)
  , IsOrderedPolynomial poly
  ) =>
  poly ->
  poly ->
  poly
gcdPolynomial f g = snd $ head $ f * g `divPolynomial` [lcmPolynomial f g]
{-# INLINE CONLIKE gcdPolynomial #-}
