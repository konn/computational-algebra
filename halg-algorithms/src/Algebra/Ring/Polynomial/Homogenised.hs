{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin Data.Singletons.TypeNats.Presburger #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

module Algebra.Ring.Polynomial.Homogenised (Homogenised, homogenise, unhomogenise, tryHomogenise, HomogOrder) where

import Algebra.Prelude.Core
import Algebra.Ring.Polynomial.Univariate
import Data.Foldable (toList)
import qualified Data.Map as M
import Data.MonoTraversable (osum)
import qualified Data.Sized.Builtin as SV
import Data.Type.Equality (gcastWith)
import Data.Type.Natural (IsPeano (succInj, succInj'))

newtype Homogenised poly = Homogenised (OrderedPolynomial (Unipol (Coefficient poly)) (MOrder poly) (Arity poly))

deriving instance IsOrderedPolynomial poly => Additive (Homogenised poly)

deriving instance IsOrderedPolynomial poly => Unital (Homogenised poly)

deriving instance IsOrderedPolynomial poly => LeftModule Natural (Homogenised poly)

deriving instance IsOrderedPolynomial poly => RightModule Natural (Homogenised poly)

deriving instance IsOrderedPolynomial poly => LeftModule Integer (Homogenised poly)

deriving instance IsOrderedPolynomial poly => RightModule Integer (Homogenised poly)

deriving instance IsOrderedPolynomial poly => Multiplicative (Homogenised poly)

deriving instance IsOrderedPolynomial poly => Monoidal (Homogenised poly)

deriving instance IsOrderedPolynomial poly => Group (Homogenised poly)

deriving instance IsOrderedPolynomial poly => Abelian (Homogenised poly)

deriving instance IsOrderedPolynomial poly => Commutative (Homogenised poly)

deriving instance IsOrderedPolynomial poly => Eq (Homogenised poly)

deriving instance IsOrderedPolynomial poly => DecidableZero (Homogenised poly)

deriving instance IsOrderedPolynomial poly => Semiring (Homogenised poly)

deriving instance IsOrderedPolynomial poly => Rig (Homogenised poly)

deriving instance IsOrderedPolynomial poly => Ring (Homogenised poly)

deriving instance IsOrderedPolynomial poly => Num (Homogenised poly)

instance
  (IsOrderedPolynomial poly, k ~ Coefficient poly) =>
  LeftModule (Scalar k) (Homogenised poly)
  where
  r .* Homogenised f = Homogenised $ mapCoeff' (r .*) f

instance
  (IsOrderedPolynomial poly, k ~ Coefficient poly) =>
  RightModule (Scalar k) (Homogenised poly)
  where
  Homogenised f *. r = Homogenised $ mapCoeff' (*. r) f

instance IsOrderedPolynomial poly => IsPolynomial (Homogenised poly) where
  type Coefficient (Homogenised poly) = Coefficient poly
  type Arity (Homogenised poly) = Arity poly + 1
  sArity _ = sing
  injectCoeff = Homogenised . injectCoeff . injectCoeff
  fromMonomial ((os :: USized k Int) :> o) =
    gcastWith (succInj (Refl :: k + 1 :~: Arity poly + 1)) $
      Homogenised $ fromMonomial (SV.singleton o) !* fromMonomial os
  fromMonomial _ = error "Cannot happen!"
  terms' (Homogenised f) =
    M.fromList
      [ (ml SV.++ mr, cf)
      | (ml, fpol) <- M.toList $ terms' f
      , (mr, cf) <- M.toList $ terms' fpol
      ]
  liftMap gen (Homogenised f) =
    withKnownNat (sing @1 %+ sing @(Arity poly)) $
      substWith
        ( \g alg ->
            alg * liftMapUnipol (const $ gen (maxBound :: Ordinal (Arity poly + 1))) g
        )
        (generate sing $ gen . inclusion)
        f

type HomogOrder n ord = ProductOrder n 1 ord Lex

instance IsOrderedPolynomial poly => IsOrderedPolynomial (Homogenised poly) where
  type MOrder (Homogenised poly) = HomogOrder (Arity poly) (MOrder poly)
  leadingTerm (Homogenised poly) =
    let (p, l) = leadingTerm poly
        (c, r) = leadingTerm p
     in (c, OrderedMonomial $ getMonomial l SV.++ getMonomial r)
  {-# INLINE leadingTerm #-}
  splitLeadingTerm (Homogenised poly) =
    let ((p, l), rest) = splitLeadingTerm poly
        ((c, r), grest) = splitLeadingTerm p
        g = toPolynomial (grest, l) + rest
     in ((c, OrderedMonomial $ getMonomial l SV.++ getMonomial r), Homogenised g)
  {-# INLINE splitLeadingTerm #-}

instance
  (IsOrderedPolynomial poly, PrettyCoeff (Coefficient poly)) =>
  Show (Homogenised poly)
  where
  showsPrec = showsPolynomialWith $ generate sing (\i -> "X_" ++ show (fromEnum i))

instance (IsOrderedPolynomial poly) => ZeroProductSemiring (Homogenised poly)

instance (Field (Coefficient poly), IsOrderedPolynomial poly) => UFD (Homogenised poly)

instance (Field (Coefficient poly), IsOrderedPolynomial poly) => PID (Homogenised poly)

instance
  (Field (Coefficient poly), IsOrderedPolynomial poly) =>
  Euclidean (Homogenised poly)
  where
  f0 `divide` g = step f0 zero
    where
      lm = leadingMonomial g
      step p quo
        | isZero p = (quo, p)
        | lm `divs` leadingMonomial p =
          let q = toPolynomial $ leadingTerm p `tryDiv` leadingTerm g
           in step (p - (q * g)) (quo + q)
        | otherwise = (quo, p)

  degree f
    | isZero f = Nothing
    | otherwise = Just $ fromIntegral $ totalDegree' f

instance (Field (Coefficient poly), IsOrderedPolynomial poly) => IntegralDomain (Homogenised poly)

instance (Field (Coefficient poly), IsOrderedPolynomial poly) => GCDDomain (Homogenised poly)

instance (Field (Coefficient poly), IsOrderedPolynomial poly) => UnitNormalForm (Homogenised poly) where
  splitUnit = splitUnitDefault

instance (Field (Coefficient poly), IsOrderedPolynomial poly) => DecidableUnits (Homogenised poly) where
  recipUnit = recipUnitDefault
  isUnit = isUnitDefault

instance (Field (Coefficient poly), IsOrderedPolynomial poly) => DecidableAssociates (Homogenised poly) where
  isAssociate = isAssociateDefault

homogenise :: IsOrderedPolynomial poly => poly -> Homogenised poly
homogenise p =
  let d = totalDegree' p
   in Homogenised $
        polynomial $
          M.mapWithKey (\k v -> toPolynomial (v, OrderedMonomial $ SV.singleton (d - totalDegree k))) $
            terms p

unhomogenise :: IsOrderedPolynomial poly => Homogenised poly -> poly
unhomogenise (Homogenised f) =
  convertPolynomial $
    mapCoeff (substWith (*) (SV.singleton one)) f

isHomogeneous ::
  IsOrderedPolynomial poly =>
  poly ->
  Bool
isHomogeneous poly =
  let degs = map osum $ toList $ monomials poly
   in and $ zipWith (==) degs (tail degs)

tryHomogenise :: IsOrderedPolynomial poly => poly -> Either poly (Homogenised poly)
tryHomogenise f
  | isHomogeneous f = Left f
  | otherwise = Right $ homogenise f
