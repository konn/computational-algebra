{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Algebra.Ring.LinearRecurrentSequence where

import Algebra.Prelude.Core
import Algebra.Ring.Euclidean.Quotient (Quotient, quotient, quotientBy, reifyQuotient, representative, withQuotient)
import Algebra.Ring.Fraction.Decomp
import Algebra.Ring.Polynomial.Factorise (clearDenom, factorHensel)
import Algebra.Ring.Polynomial.Univariate
import Control.Exception (assert)
import Control.Lens (ifoldMap)
import Control.Monad.Random
import qualified Data.DList as DL
import qualified Data.IntMap.Strict as IM
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE
import Data.Maybe
import Data.Reflection (Reifies (reflect))
import qualified Data.Sized as S
import qualified Data.Sized as SV
import qualified Data.Vector as V
import qualified Numeric.Field.Fraction as F
import qualified Numeric.Ring.Class as AC

data Power = P Natural | Np
  deriving (Eq, Ord)

instance Show Power where
  showsPrec _ (P n) = shows n
  showsPrec _ Np = showString "n"

data GeneralTerm k
  = Const k
  | N
  | GeneralTerm k :^ Power
  | GeneralTerm k :+ GeneralTerm k
  | GeneralTerm k :* GeneralTerm k
  | GeneralTerm k :- GeneralTerm k
  | Sqrt (GeneralTerm k)
  | Root (Unipol k)
  deriving (Eq, Ord, Foldable)

instance Additive (GeneralTerm k) where
  (+) = (:+)

instance Rig k => Monoidal (GeneralTerm k) where
  zero = Const zero

instance Abelian k => Abelian (GeneralTerm k)

instance Ring k => Group (GeneralTerm k) where
  (-) = (:-)

instance Ring k => Semiring (GeneralTerm k)

instance Multiplicative (GeneralTerm k) where
  (*) = (:*)

instance
  {-# OVERLAPPABLE #-}
  Semiring k =>
  LeftModule k (GeneralTerm k)
  where
  (.*) = (:*) . Const

instance
  {-# OVERLAPPABLE #-}
  Semiring k =>
  RightModule k (GeneralTerm k)
  where
  (*.) = flip $ flip (:*) . Const

instance
  {-# OVERLAPPABLE #-}
  Semiring k =>
  LeftModule (Scalar k) (GeneralTerm k)
  where
  (.*) = (:*) . Const . runScalar

instance Unital k => Unital (GeneralTerm k) where
  one = Const one

instance
  {-# OVERLAPPABLE #-}
  Semiring k =>
  RightModule (Scalar k) (GeneralTerm k)
  where
  (*.) = flip $ flip (:*) . Const . runScalar

instance Ring k => LeftModule Integer (GeneralTerm k) where
  c .* a = Const (fromInteger' c) :* a

instance Ring k => RightModule Integer (GeneralTerm k) where
  a *. c = a :* Const (fromInteger' c)

instance Rig k => LeftModule Natural (GeneralTerm k) where
  c .* a = Const (fromNatural c) :* a

instance Rig k => RightModule Natural (GeneralTerm k) where
  a *. c = a :* Const (fromNatural c)

instance Ring k => Rig (GeneralTerm k) where
  fromNatural = Const . fromNatural

instance Ring k => Ring (GeneralTerm k) where
  fromInteger = Const . fromInteger'

instance (Show k, CoeffRing k, PrettyCoeff k) => Show (GeneralTerm k) where
  showsPrec d (Const k) = showsPrec d k
  showsPrec _ N = showString "n"
  showsPrec d (gt :^ po) =
    showParen (d > 8) $
      showsPrec 9 gt . showString " ^ " . shows po
  showsPrec d (gt :+ gt') =
    showParen (d > 6) $
      showsPrec 6 gt . showString " + " . showsPrec 7 gt'
  showsPrec d (gt :- gt') =
    showParen (d > 6) $
      showsPrec 6 gt . showString " - " . showsPrec 7 gt'
  showsPrec d (gt :* gt') =
    showParen (d > 7) $
      showsPrec 7 gt . showString " * " . showsPrec 8 gt'
  showsPrec d (Sqrt gt) =
    showParen (d > 10) $
      showString "√" . showsPrec 10 gt
  showsPrec _ (Root un) =
    showString "Root("
      . showsPrec 10 un
      . showChar ')'

infixl 6 :+, :-

infixl 7 :*

infixr 8 :^

data RecurrenceCoeff a = RC {recCoefficient :: a, initialValue :: a}
  deriving (Show, Eq, Ord)

data Recurrence a where
  Recurrence ::
    { recCoefficients_ :: Sized n a
    , initialValues_ :: Sized n a
    } ->
    Recurrence a

recurrenceSize :: Recurrence a -> Int
{-# INLINE recurrenceSize #-}
recurrenceSize Recurrence {..} = V.length $ S.unsized recCoefficients_

recCoefficients :: Recurrence a -> Vector a
recCoefficients Recurrence {..} = S.unsized recCoefficients_

initialValues :: Recurrence a -> Vector a
initialValues Recurrence {..} = S.unsized initialValues_

{- | Generating function for the sequence defined by
the n-ary linear recurrence formula:
\[
  a_{n + k} = c_0 a_n + c_1 a_1 + \cdots + c_{k - 1} a_{n + k - 1}.
\]
Where initial values \(a_0, \ldots, a_{k - 1}\) are given.

Fibonacci \(a0 = 0, a1 = 1, a(n+2) = an + a(n+1)\):

>>> generatingFunction $ Recurrence (1 :< 1 :< Nil) (0 :< (1 :: Rational) :< Nil)
-x / x^2 + x - 1

Tribonacci:

>>> generatingFunction $ Recurrence (1 :< 1 :< 1 :< Nil) (0 :< 1 :< (1 :: Rational) :< Nil)
-x / x^3 + x^2 + x - 1
-}
generatingFunction ::
  forall k.
  (Field k, CoeffRing k) =>
  Recurrence k ->
  Fraction (Unipol k)
generatingFunction recs =
  let den =
        runAdd
          (ifoldMap (\i ci -> Add $ ci .*. #x ^ fromIntegral (k - i)) coeffs)
          - 1
      ok = V.sum $
        V.generate (k - 1) $ \i ->
          sum (V.zipWith (*) (V.drop (i + 1) coeffs) inis)
            .*. #x ^ fromIntegral (k - 1 - i)
      num = ok - runAdd (ifoldMap (\i ci -> Add $ ci .*. #x ^ fromIntegral i) inis)
   in num F.% den
  where
    k = recurrenceSize recs
    coeffs = recCoefficients recs
    inis = initialValues recs

{- | Solves ternary linear recurrent sequence (e.g. Fibonacci).

>>> evalRandIO (solveTernaryRecurrence (1 :< 1 :< Nil) (0 :< 1 :< Nil))
((1 / 5) * 1 + (2 / 5) * 1 * Root(x^2 + x - 1)) * (n + 1 * 1) ^ 0 * (1 * 1 + 1 * 1 * Root(x^2 + x - 1)) ^ n + (((-1 / 5) * 1 + (-2 / 5) * 1 * Root(x^2 + x - 1)) * (n + 1 * 1) ^ 0 * (0 * 1 + (-1) * 1 * Root(x^2 + x - 1)) ^ n + 0 * 1) + 0
-}
solveTernaryRecurrence ::
  (MonadRandom m) =>
  -- | Recurrence coefficients
  Sized 2 Rational ->
  -- | Initial values
  Sized 2 Rational ->
  m (GeneralTerm Rational)
solveTernaryRecurrence coes iniVals = do
  let f = generatingFunction $ Recurrence coes iniVals
  PartialFraction {..} <- flip partialFractionDecomposition f $ \g -> do
    let (c, g') = clearDenom g
    (lc, facs) <- factorHensel g'
    let (Mult lc', fs') =
          IM.foldMapWithKey
            ( \d ->
                foldMap
                  ( \(mapCoeffUnipol (F.% 1) -> f0) ->
                      let lc0 = leadingCoeff f0
                          f' = monoize f0
                       in (Mult lc0, DL.singleton (f', fromIntegral d))
                  )
            )
            facs
    pure (fromInteger lc * lc' * (1 F.% c), NE.fromList $ DL.toList fs')
  pure $
    runAdd $
      foldMap
        ( \(h, powDens) ->
            if totalDegree' h <= 1
              then
                IM.foldMapWithKey
                  ( \n q ->
                      Add $
                        linearInverse (negate $ constantTerm h) (fromIntegral n) (constantTerm q)
                  )
                  powDens
              else -- Must be quadtraic and square-free as we expect ternary recurrence.

                let Just (_, q) = IM.lookupMin powDens
                 in Add $ unliftQuadInverse (q F.% h)
        )
        partialFracs

-- | Unsafe wrapper to treat 'DecidableUnits' as if it is a field.
newtype WrapDecidableUnits k = WrapDecidableUnits {runWrapDecidableUnits :: k}
  deriving newtype
    ( Eq
    , Ord
    , Hashable
    , Additive
    , Monoidal
    , Group
    , Multiplicative
    , Abelian
    , Semiring
    , Unital
    , Rig
    , Ring
    , DecidableZero
    , DecidableAssociates
    , DecidableUnits
    , Commutative
    , ZeroProductSemiring
    )

instance DecidableUnits k => Division (WrapDecidableUnits k) where
  recip = fromMaybe (error "WrapDecidableUnits: Inverting non-units!") . recipUnit

instance
  ( DecidableAssociates k
  , Ring k
  , DecidableZero k
  , DecidableUnits k
  ) =>
  Euclidean (WrapDecidableUnits k)

instance
  ( DecidableAssociates k
  , Ring k
  , DecidableZero k
  , DecidableUnits k
  ) =>
  PID (WrapDecidableUnits k)

instance
  ( DecidableAssociates k
  , Ring k
  , DecidableZero k
  , DecidableUnits k
  ) =>
  UFD (WrapDecidableUnits k)

instance
  ( DecidableAssociates k
  , Ring k
  , DecidableZero k
  , DecidableUnits k
  ) =>
  GCDDomain (WrapDecidableUnits k)

instance
  ( DecidableAssociates k
  , Ring k
  , DecidableZero k
  , DecidableUnits k
  ) =>
  UnitNormalForm (WrapDecidableUnits k)

instance
  ( DecidableAssociates k
  , Ring k
  , DecidableZero k
  , DecidableUnits k
  ) =>
  IntegralDomain (WrapDecidableUnits k)

deriving newtype instance
  LeftModule c k => LeftModule c (WrapDecidableUnits k)

deriving newtype instance
  RightModule c k => RightModule c (WrapDecidableUnits k)

unliftQuadInverse ::
  forall k.
  (CoeffRing k, Field k) =>
  -- | Formal fraction with quadratic denominator
  Fraction (Unipol k) ->
  GeneralTerm k
unliftQuadInverse f
  | degree (denominator f) /= Just 2 = error "Input numerator is not quadratic!"
  | otherwise =
    reifyQuotient (denominator f) $ \(den :: Proxy r) ->
      let root = WrapDecidableUnits $ quotientBy den #x
          g = mapCoeffUnipol (WrapDecidableUnits . quotientBy den . injectCoeff) $ denominator f
          h = mapCoeffUnipol (WrapDecidableUnits . quotientBy den . injectCoeff) $ numerator f
          rootg = #x - injectCoeff root
          (root'g, r) = g `divModUnipol` rootg
          PartialFraction {..} =
            partialFractionDecompositionWith h ((rootg, 1) :| [(root'g, 1)])
       in assert (isZero r) $
            unliftGeneralTerm $
              runAdd $
                foldMap
                  ( \(z, im) ->
                      let c = negate $ constantTerm z
                          num =
                            constantTerm $
                              snd $ fromJust $ IM.lookupMin im
                       in Add $ mapGTCoeff runWrapDecidableUnits $ linearInverse c 1 num
                  )
                  partialFracs

mapGTCoeff ::
  (CoeffRing c, CoeffRing d) => (c -> d) -> GeneralTerm c -> GeneralTerm d
mapGTCoeff f (Const x) = Const (f x)
mapGTCoeff f (a :+ b) = mapGTCoeff f a :+ mapGTCoeff f b
mapGTCoeff f (a :- b) = mapGTCoeff f a :- mapGTCoeff f b
mapGTCoeff f (a :* b) = mapGTCoeff f a :* mapGTCoeff f b
mapGTCoeff f (a :^ n) = mapGTCoeff f a :^ n
mapGTCoeff _ N = N
mapGTCoeff f (Sqrt a) = Sqrt $ mapGTCoeff f a
mapGTCoeff f (Root h) = Root $ mapCoeffUnipol f h

unliftGeneralTerm ::
  forall k s.
  (CoeffRing k, Reifies s (Unipol k)) =>
  GeneralTerm (Quotient s (Unipol k)) ->
  GeneralTerm k
unliftGeneralTerm (Const q) =
  let g = reflect (Proxy :: Proxy s)
   in substWith ((:*) . Const) (SV.singleton (Root g)) $ representative q
unliftGeneralTerm (a :+ b) = unliftGeneralTerm a :+ unliftGeneralTerm b
unliftGeneralTerm (a :- b) = unliftGeneralTerm a :- unliftGeneralTerm b
unliftGeneralTerm (a :* b) = unliftGeneralTerm a :* unliftGeneralTerm b
unliftGeneralTerm (a :^ b) = unliftGeneralTerm a :^ b
unliftGeneralTerm (Sqrt a) = Sqrt $ unliftGeneralTerm a
unliftGeneralTerm Root {} = error "Unlifting Root(...) not supported"
unliftGeneralTerm N = N

linearInverse ::
  (CoeffRing k, Field k) =>
  -- | alpha for X - alpha
  k ->
  -- | power
  Natural ->
  -- | coefficient
  k ->
  GeneralTerm k
linearInverse alpha k c =
  Const (c * negate (recip alpha) ^ k)
    :* ((N :+ Const one) :^ P (pred k))
    :* Const (recip alpha) :^ Np
