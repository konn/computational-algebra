{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Algebra.Ring.LinearRecurrentSequence where

import Algebra.Prelude.Core
import Algebra.Ring.Euclidean.Quotient (Quotient, quotientBy, reifyQuotient, representative)
import Algebra.Ring.Fraction.Decomp
import Algebra.Ring.Polynomial.Factorise (clearDenom, factorHensel)
import Algebra.Ring.Polynomial.Univariate
import Control.Exception (assert)
import Control.Lens (ifoldMap)
import Control.Monad.Random
import Control.Monad.Trans.Writer.CPS (Writer, runWriter, tell)
import qualified Data.DList as DL
import qualified Data.IntMap.Strict as IM
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE
import Data.Maybe
import Data.Monoid (Any (Any))
import Data.Reflection (Reifies (reflect))
import Data.Semigroup (Semigroup)
import qualified Data.Sized as S
import qualified Data.Sized as SV
import qualified Data.Vector as V
import qualified Numeric.Field.Fraction as F
import qualified Numeric.Ring.Class as AC
import Unsafe.Coerce (unsafeCoerce)

data Power = P Natural | Np
  deriving (Eq, Ord)

instance Show Power where
  showsPrec _ (P n) = shows n
  showsPrec _ Np = showString "n"

data GeneralTerm k where
  Const :: k -> GeneralTerm k
  N :: GeneralTerm k
  (:^) :: GeneralTerm k -> Power -> GeneralTerm k
  (:+) :: GeneralTerm k -> GeneralTerm k -> GeneralTerm k
  (:*) :: GeneralTerm k -> GeneralTerm k -> GeneralTerm k
  (:-) :: GeneralTerm k -> GeneralTerm k -> GeneralTerm k
  Lift ::
    Reifies s (Unipol k) =>
    Proxy s ->
    GeneralTerm (WrapDecidableUnits (Quotient s (Unipol k))) ->
    GeneralTerm k

deriving via Add (GeneralTerm k) instance Additive k => Semigroup (GeneralTerm k)

deriving via Add (GeneralTerm k) instance Rig k => Monoid (GeneralTerm k)

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

showsGTWith :: (CoeffRing k, Field k) => (Int -> k -> ShowSCoeff) -> Int -> GeneralTerm k -> ShowS
showsGTWith = loop
  where
    loop ::
      (CoeffRing a, Field a) =>
      (Int -> a -> ShowSCoeff) ->
      Int ->
      GeneralTerm a ->
      ShowS
    loop showsElt _ (Const a) = case showsElt 11 a of
      Vanished -> showString "0"
      i -> showsCoeffAsTerm i
    loop _ _ N = showString "n"
    loop showsElt d (gt' :^ po) =
      showParen (d > 8) $
        loop showsElt 11 gt' . showString " ^ " . showsPrec 8 po
    loop showsElt d (gt' :+ gt_a) =
      showParen (d > 6) $
        loop showsElt 6 gt'
          . showString " + "
          . loop showsElt 6 gt_a
    loop showsElt d (gt' :* gt_a) =
      showParen (d > 7) $
        loop showsElt 7 gt'
          . showString " * "
          . loop showsElt 7 gt_a
    loop showsElt d (gt' :- gt_a) =
      showParen (d > 6) $
        loop showsElt 6 gt'
          . showString " - "
          . loop showsElt 6 gt_a
    loop showsElt d (Lift (s :: Proxy s) gt') =
      let f = reflect s
       in loop
            ( \d' ->
                Positive
                  . showsPolynomialWith'
                    True
                    showsElt
                    ( SV.singleton $
                        "Root(" <> showPolynomialWith' True showsElt (SV.singleton "x") 10 f <> ")"
                    )
                    d'
                  . representative
                  . runWrapDecidableUnits
            )
            d
            gt'

instance (Show k, Field k, CoeffRing k, PrettyCoeff k) => Show (GeneralTerm k) where
  showsPrec = showsGTWith showsCoeff

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
    reduceGeneralTerm $
      foldMap
        ( \(h, powDens) ->
            if totalDegree' h <= 1
              then
                IM.foldMapWithKey
                  ( \n q ->
                      linearInverse (negate $ constantTerm h) (fromIntegral n) (constantTerm q)
                  )
                  powDens
              else -- Must be quadtraic and square-free as we expect ternary recurrence.

                let Just (_, q) = IM.lookupMin powDens
                 in unliftQuadInverse (q F.% h)
        )
        partialFracs

-- | Unsafe wrapper to treat 'DecidableUnits' as if it is a field.
newtype WrapDecidableUnits k = WrapDecidableUnits {runWrapDecidableUnits :: k}
  deriving newtype
    ( Eq
    , Ord
    , Show
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
    , PrettyCoeff
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
            Lift den $
              foldMap
                ( \(z, im) ->
                    let c = negate $ constantTerm z
                        num =
                          constantTerm $
                            snd $ fromJust $ IM.lookupMin im
                     in linearInverse c 1 num
                )
                partialFracs

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

type Rewriter = Writer Any

progress :: a -> Rewriter a
progress a = a <$ tell (Any True)

reduceGeneralTerm :: (Field k, CoeffRing k) => GeneralTerm k -> GeneralTerm k
reduceGeneralTerm = fixedPoint simplifyGeneralTerm

fixedPoint :: (a -> Rewriter a) -> a -> a
fixedPoint f = go
  where
    go x =
      let (x', Any reduced) = runWriter $ f x
       in if reduced then go x' else x

simplifyGeneralTerm ::
  (Field k, CoeffRing k) => GeneralTerm k -> Rewriter (GeneralTerm k)
simplifyGeneralTerm k@Const {} = pure k
simplifyGeneralTerm k@N = pure k
simplifyGeneralTerm (l :+ r) =
  ((,) <$> simplifyGeneralTerm l <*> simplifyGeneralTerm r) >>= \case
    (Const z, r') | isZero z -> progress r'
    (l', Const z) | isZero z -> progress l'
    (Const l', Const r') -> progress $ Const $ l' + r'
    (Const l', Lift s a) ->
      progress $
        Lift s $
          Const (WrapDecidableUnits $ quotientBy s $ injectCoeff l') :+ a
    (Lift s a, Const r') ->
      progress $
        Lift s $
          a :+ Const (WrapDecidableUnits $ quotientBy s $ injectCoeff r')
    (Lift s a, Lift s' b)
      | reflect s == reflect s' ->
        progress $ Lift s (a :+ unsafeCoerce b)
    (l', r') -> pure $ l' :+ r'
simplifyGeneralTerm (l :- r) =
  ((,) <$> simplifyGeneralTerm l <*> simplifyGeneralTerm r) >>= \case
    (l', Const z) | isZero z -> progress l'
    (Const l', Const r') -> progress $ Const $ l' - r'
    (Const l', Lift s a) ->
      progress $
        Lift s $
          Const (WrapDecidableUnits $ quotientBy s $ injectCoeff l') :- a
    (Lift s a, Const r') ->
      progress $
        Lift s $
          a :- Const (WrapDecidableUnits $ quotientBy s $ injectCoeff r')
    (Lift s a, Lift s' b)
      | reflect s == reflect s' ->
        progress $ Lift s (a :- unsafeCoerce b)
    (l', r') -> pure $ l' :+ r'
simplifyGeneralTerm (l :* r) =
  ((,) <$> simplifyGeneralTerm l <*> simplifyGeneralTerm r) >>= \case
    (Const z, r')
      | isZero z -> progress $ Const zero
      | z == one -> progress r'
    (l', Const z)
      | isZero z -> progress $ Const zero
      | z == one -> progress l'
    (Const l', Const r') -> progress $ Const $ l' * r'
    (Const l', Lift s a) ->
      progress $
        Lift s $
          Const (WrapDecidableUnits $ quotientBy s $ injectCoeff l') :* a
    (Lift s a, Const r') ->
      progress $
        Lift s $
          a :* Const (WrapDecidableUnits $ quotientBy s $ injectCoeff r')
    (Lift s a, Lift s' b)
      | reflect s == reflect s' ->
        progress $ Lift s (a :* unsafeCoerce b)
    (l', r') -> pure $ l' :* r'
simplifyGeneralTerm (l :^ p) = do
  lred <- simplifyGeneralTerm l
  case (lred, p) of
    (l'@(Const z), _)
      | z == one -> progress l'
    (Const z, P n) -> progress $ Const $ z ^ n
    (_, P 0) -> progress $ Const one
    (l', r') -> pure $ l' :^ r'
simplifyGeneralTerm (Lift p a) =
  simplifyGeneralTerm a >>= \case
    Const (WrapDecidableUnits a')
      | totalDegree' (representative a') < 1 ->
        progress $ Const $ constantTerm $ representative a'
    r -> pure $ Lift p r

{-

Solves fibonnaci sequence; i.e.  recurrent sequence defined by
a_{n + 2} = 1 a_n + 1 a_{n + 1}
a_0 = 0
a_1 = 1

>>> fib <- evalRandIO $ solveTernaryRecurrence (1 :< 1 :< Nil) (0 :< 1 :< Nil)
>>> evalGeneralTerm fib 12
144
-}
evalGeneralTerm ::
  (CoeffRing k, Field k) =>
  GeneralTerm k ->
  Natural ->
  GeneralTerm k
evalGeneralTerm f n = fixedPoint (substN >=> simplifyGeneralTerm) f
  where
    substN :: (CoeffRing f, Field f) => GeneralTerm f -> Rewriter (GeneralTerm f)
    substN N = progress $ Const $ fromNatural n
    substN k@Const {} = pure k
    substN (l :+ r) = (:+) <$> substN l <*> substN r
    substN (l :- r) = (:-) <$> substN l <*> substN r
    substN (l :* r) = (:*) <$> substN l <*> substN r
    substN (l :^ Np) = (:^ P n) <$> substN l
    substN (l :^ P k) = (:^ P k) <$> substN l
    substN (Lift p s) = Lift p <$> substN s
