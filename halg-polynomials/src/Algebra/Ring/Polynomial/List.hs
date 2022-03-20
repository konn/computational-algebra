{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}

-- | Multivariate polynomials, expressed as a list of terms with decreasing monomials.
module Algebra.Ring.Polynomial.List
  ( ListPoly (),
  )
where

import Algebra.Prelude.Core hiding (coerce)
import Control.Arrow ((>>>))
import Control.DeepSeq (NFData)
import Control.Lens (alaf)
import qualified Data.Bifunctor as Bi
import Data.Coerce
import qualified Data.HashSet as HS
import Data.Kind (Type)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Sized as SV
import Data.Strict (toLazy, toStrict)
import Data.Strict.Tuple (Pair (..))
import qualified Data.Strict.Tuple as STuple
import GHC.Exts (proxy#)
import qualified GHC.TypeLits as TL
import Numeric.Algebra (Ring (fromInteger))
import qualified Numeric.Algebra as A

newtype ListPoly r (order :: Type) n = ListPoly {runListPoly :: [Pair r (OrderedMonomial order n)]}
  deriving (Eq)
  deriving (NFData) via [Pair r (OrderedMonomial order n)]

deriving via
  WrapAlgebra (ListPoly r order n)
  instance
    ( IsMonomialOrder n order
    , KnownNat n
    , Ring r
    , CoeffRing r
    , UnitNormalForm r
    ) =>
    Num (ListPoly r order n)

deriving instance
  (Eq r, Ord r, IsMonomialOrder n order) =>
  Ord (ListPoly r order n)

instance
  (CoeffRing r, UnitNormalForm r, KnownNat n, IsMonomialOrder n order) =>
  UnitNormalForm (ListPoly r order n)
  where
  splitUnit = splitUnitDefault

instance
  ( CoeffRing r
  , UnitNormalForm r
  , KnownNat n
  , IsMonomialOrder n order
  ) =>
  DecidableAssociates (ListPoly r order n)
  where
  isAssociate = isAssociateDefault
  {-# INLINE isAssociate #-}

instance
  (CoeffRing r, ZeroProductSemiring r, KnownNat n, IsMonomialOrder n order) =>
  ZeroProductSemiring (ListPoly r order n)

instance
  ( CoeffRing r
  , KnownNat n
  , IsMonomialOrder n order
  , Field r
  ) =>
  IntegralDomain (ListPoly r order n)
  where
  p `divides` q = isZero $ p `modPolynomial` [q]
  {-# INLINE divides #-}
  p `maybeQuot` q =
    if isZero q
      then Nothing
      else
        let (r, s) = p `divModPolynomial` [q]
         in if isZero s
              then Just $ snd $ head r
              else Nothing
  {-# INLINE maybeQuot #-}

instance
  (CoeffRing r, IsMonomialOrder n order, DecidableUnits r, KnownNat n) =>
  DecidableUnits (ListPoly r order n)
  where
  isUnit = isUnitDefault
  recipUnit = recipUnitDefault

mergePolyWith ::
  forall n order r s t.
  (IsMonomialOrder n order, DecidableZero t) =>
  (r -> s -> t) ->
  (r -> t) ->
  (s -> t) ->
  ListPoly r order n ->
  ListPoly s order n ->
  ListPoly t order n
{-# INLINE mergePolyWith #-}
mergePolyWith mg inl inr = coerce loop
  where
    loop ::
      [Pair r (OrderedMonomial order n)] ->
      [Pair s (OrderedMonomial order n)] ->
      [Pair t (OrderedMonomial order n)]
    {-# INLINE loop #-}
    loop [] rs = map (Bi.first inr) rs
    loop ls [] = map (Bi.first inl) ls
    loop ls@((c :!: mon) : ls') rs@((d :!: mon') : rs') =
      case compare mon mon' of
        LT -> (inr d :!: mon') : loop ls rs'
        EQ ->
          let !coe = mg c d
           in if isZero coe
                then loop ls' rs'
                else (coe :!: mon) : loop ls' rs'
        GT -> (inl c :!: mon) : loop ls' rs

instance
  (DecidableZero r, IsMonomialOrder n order) =>
  Additive (ListPoly r order n)
  where
  (+) = mergePolyWith (+) id id
  {-# INLINE (+) #-}

instance
  (DecidableZero r, IsMonomialOrder n order) =>
  LeftModule Natural (ListPoly r order n)
  where
  n .* ListPoly xs
    | n == 0 = ListPoly []
    | otherwise =
      ListPoly $ filter (not . isZero . STuple.fst) $ map (Bi.first (n .*)) xs
  {-# INLINE (.*) #-}

instance
  (DecidableZero r, IsMonomialOrder n order) =>
  RightModule Natural (ListPoly r order n)
  where
  ListPoly xs *. n
    | n == 0 = ListPoly []
    | otherwise =
      ListPoly $ filter (not . isZero . STuple.fst) $ map (Bi.first (*. n)) xs
  {-# INLINE (*.) #-}

instance
  (DecidableZero r, IsMonomialOrder n order) =>
  Monoidal (ListPoly r order n)
  where
  zero = ListPoly []
  {-# INLINE zero #-}

instance
  ( DecidableZero r
  , Abelian r
  , IsMonomialOrder n order
  ) =>
  Abelian (ListPoly r order n)

instance
  (DecidableZero r, LeftModule Integer r, IsMonomialOrder n order) =>
  LeftModule Integer (ListPoly r order n)
  where
  n .* ListPoly xs
    | n == 0 = ListPoly []
    | otherwise =
      ListPoly $ filter (not . isZero . STuple.fst) $ map (Bi.first (n .*)) xs
  {-# INLINE (.*) #-}

instance
  (DecidableZero r, RightModule Integer r, IsMonomialOrder n order) =>
  RightModule Integer (ListPoly r order n)
  where
  ListPoly xs *. n
    | n == 0 = ListPoly []
    | otherwise =
      ListPoly $ filter (not . isZero . STuple.fst) $ map (Bi.first (*. n)) xs
  {-# INLINE (*.) #-}

instance
  (DecidableZero r, Group r, IsMonomialOrder n order) =>
  Group (ListPoly r order n)
  where
  (-) = mergePolyWith (-) id negate
  {-# INLINE (-) #-}
  negate = coerce $ map @[] (Bi.first @Pair @r @r @(OrderedMonomial order n) negate)
  {-# INLINE negate #-}

instance
  (DecidableZero r, KnownNat n, Multiplicative r, IsMonomialOrder n order) =>
  Multiplicative (ListPoly r order n)
  where
  l@(ListPoly []) * _ = l
  _ * r@(ListPoly []) = r
  ListPoly ls * ListPoly r =
    alaf
      Add
      foldMap
      ( \(o :!: m) ->
          ListPoly
            [ c' :!: (m * m')
            | c :!: m' <- r
            , let c' = o * c
            , not $ isZero c'
            ]
      )
      ls
  {-# INLINE (*) #-}

instance
  ( DecidableZero r
  , Semiring r
  , KnownNat n
  , IsMonomialOrder n order
  ) =>
  Semiring (ListPoly r order n)

instance
  ( DecidableZero r
  , Unital r
  , IsMonomialOrder n order
  , KnownNat n
  ) =>
  Unital (ListPoly r order n)
  where
  one = ListPoly [one :!: one]

instance
  ( DecidableZero r
  , Commutative r
  , KnownNat n
  , IsMonomialOrder n order
  ) =>
  Commutative (ListPoly r order n)

instance
  (DecidableZero r, IsMonomialOrder n order) =>
  DecidableZero (ListPoly r order n)
  where
  isZero = null . runListPoly
  {-# INLINE isZero #-}

instance
  (Semiring r, DecidableZero r, IsMonomialOrder n order) =>
  LeftModule (Scalar r) (ListPoly r order n)
  where
  (.*) a =
    coerce $
      filter (not . isZero @r . STuple.fst)
        . map @[]
          ( Bi.first @Pair @r @r @(OrderedMonomial order n)
              (runScalar a *)
          )
  {-# INLINE (.*) #-}

instance
  (Semiring r, DecidableZero r, IsMonomialOrder n order) =>
  RightModule (Scalar r) (ListPoly r order n)
  where
  (*.) = flip $ \a ->
    coerce $
      filter (not . isZero @r . STuple.fst)
        . map @[]
          ( Bi.first @Pair @r @r @(OrderedMonomial order n)
              (* runScalar a)
          )
  {-# INLINE (*.) #-}

instance
  (IsMonomialOrder n order, KnownNat n, Rig r, DecidableZero r) =>
  Rig (ListPoly r order n)

instance
  (IsMonomialOrder n order, KnownNat n, Ring r, DecidableZero r) =>
  Ring (ListPoly r order n)
  where
  fromInteger n =
    let !c = A.fromInteger n
     in if isZero c
          then ListPoly []
          else ListPoly [c :!: one]

instance
  (CoeffRing r, KnownNat n, IsMonomialOrder n order) =>
  IsPolynomial (ListPoly r order n)
  where
  type Arity (ListPoly r order n) = n
  type Coefficient (ListPoly r order n) = r
  liftMap f =
    alaf
      Add
      foldMap
      ( \(c :!: OrderedMonomial mon) ->
          Scalar c
            .* runMult
              ( ifoldMapMonom
                  (\i p -> Mult $ f i ^ fromIntegral p)
                  mon
              )
      )
      . runListPoly
  {-# INLINE liftMap #-}
  monomials = HS.fromList . map (getMonomial . STuple.snd) . runListPoly
  {-# INLINE monomials #-}
  terms' = M.fromList . map (toLazy . STuple.swap) . coerce
  {-# INLINE terms' #-}
  sArity = const sNat
  {-# INLINE sArity #-}
  arity = const $ TL.natVal' @n proxy#
  {-# INLINE arity #-}
  injectCoeff c
    | isZero c = ListPoly []
    | otherwise = ListPoly [c :!: one]
  {-# INLINE injectCoeff #-}
  coeff' = coeff . OrderedMonomial
  {-# INLINE coeff' #-}
  constantTerm =
    runListPoly >>> last >>> \(c :!: mon) ->
      if mon == one
        then c
        else zero
  {-# INLINE constantTerm #-}
  fromMonomial = ListPoly . (: []) . (one :!:) . OrderedMonomial
  {-# INLINE fromMonomial #-}
  toPolynomial' = coerce $ toPolynomial @(ListPoly r order n)
  {-# INLINE toPolynomial' #-}

instance
  (CoeffRing r, KnownNat n, IsMonomialOrder n order) =>
  IsOrderedPolynomial (ListPoly r order n)
  where
  type MOrder (ListPoly r order n) = order
  leadingTerm =
    runListPoly
      >>> \case
        [] -> (zero, one)
        tm : _ -> toLazy tm
  {-# INLINE leadingTerm #-}
  leadingCoeff =
    runListPoly
      >>> \case
        [] -> zero
        (c :!: _) : _ -> c
  {-# INLINE leadingCoeff #-}
  leadingMonomial =
    runListPoly
      >>> \case
        [] -> one
        (_ :!: mon) : _ -> mon
  {-# INLINE leadingMonomial #-}
  splitLeadingTerm =
    runListPoly
      >>> \case
        [] -> ((zero, one), ListPoly [])
        tm : rest -> (toLazy tm, ListPoly rest)
  {-# INLINE splitLeadingTerm #-}
  coeff mon =
    runListPoly
      >>> dropWhile ((> mon) . STuple.snd)
      >>> \case
        (c :!: mon') : _ | mon == mon' -> c
        _ -> zero
  {-# INLINE coeff #-}
  toPolynomial tm@(c, _)
    | isZero c = ListPoly []
    | otherwise = ListPoly [toStrict tm]
  {-# INLINE toPolynomial #-}
  fromOrderedMonomial = ListPoly . (: []) . (one :!:)
  {-# INLINE fromOrderedMonomial #-}
  orderedMonomials = S.fromDescList . map STuple.snd . runListPoly
  {-# INLINE orderedMonomials #-}
  polynomial = ListPoly . filter (not . isZero . STuple.fst) . map (toStrict . swap) . M.toDescList
  {-# INLINE polynomial #-}
  mapMonomialMonotonic f = ListPoly . map (Bi.second f) . runListPoly
  {-# INLINE mapMonomialMonotonic #-}

instance
  (PrettyCoeff r, CoeffRing r, KnownNat n, IsMonomialOrder n order) =>
  Show (ListPoly r order n)
  where
  showsPrec = showsPolynomialWith $
    SV.generate' $ \i ->
      "X_" <> show (ordToNatural i)
  {-# INLINE showsPrec #-}
