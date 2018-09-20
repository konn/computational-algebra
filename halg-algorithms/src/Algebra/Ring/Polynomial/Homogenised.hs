{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving, TypeOperators                      #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver               #-}
module Algebra.Ring.Polynomial.Homogenised
       (Homogenised, homogenise, unhomogenise, tryHomogenise, HomogOrder) where
import           Algebra.Prelude.Core
import           Algebra.Ring.Polynomial.Univariate
import           Data.Foldable                      (toList)
import qualified Data.Map                           as M
import           Data.MonoTraversable               (osum)
import qualified Data.Sized.Builtin                 as SV

newtype Homogenised poly = Homogenised (Unipol poly)

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
instance (IsOrderedPolynomial poly, LeftModule (Scalar r) poly)
      => LeftModule (Scalar r) (Homogenised poly) where
  r .* Homogenised f = Homogenised $ mapCoeff' (r .*) f
instance (IsOrderedPolynomial poly, RightModule (Scalar r) poly)
      => RightModule (Scalar r) (Homogenised poly) where
   Homogenised f *. r = Homogenised $ mapCoeff' (*. r) f

instance IsOrderedPolynomial poly => IsPolynomial (Homogenised poly) where
  type Coefficient (Homogenised poly) = Coefficient poly
  type Arity (Homogenised poly) = Succ (Arity poly)
  sArity _ = sing
  injectCoeff = Homogenised . injectCoeff . injectCoeff
  fromMonomial ((os :: USized k Int) :> o) =
    let sn = sizedLength os
        sm = sing :: Sing (Arity poly)
    in withRefl (succInj' sn sm (Refl :: Succ k :~: Succ (Arity poly))) $
    Homogenised $ (fromMonomial os :: poly) .*. fromMonomial (SV.singleton o)
  fromMonomial _ = error "Cannot happen!"
  terms' (Homogenised f) =
    withRefl (plusComm (sArity f) sOne) $
    M.fromList
    [(mr SV.++ ml, cf)
    | (ml, fpol) <- M.toList $ terms' f
    , (mr, cf) <- M.toList $ terms' fpol
    ]
  liftMap gen (Homogenised f) =
    withKnownNat (sSucc $ sArity f) $
    withRefl (lneqToLT (sArity f) (sSucc (sArity f))  $ lneqSucc (sArity f)) $
    substWith (\g alg -> alg * liftMap (gen . inclusion) g) (singleton $ gen maxBound) f

type HomogOrder n ord = ProductOrder n 1 ord Lex

instance IsOrderedPolynomial poly => IsOrderedPolynomial (Homogenised poly) where
  type MOrder (Homogenised poly) = HomogOrder (Arity poly) (MOrder poly)
  leadingTerm poly =
    let dic = M.mapKeys OrderedMonomial $ terms' poly
    in if M.null dic then (zero, one) else swap $ M.findMax dic
  {-# INLINE leadingTerm #-}

instance (IsOrderedPolynomial poly, PrettyCoeff (Coefficient poly))
      => Show (Homogenised poly) where
  showsPrec = showsPolynomialWith $ generate sing (\i -> "X_" ++ show (fromEnum i))

instance (IsOrderedPolynomial poly) => ZeroProductSemiring (Homogenised poly)
instance (Field (Coefficient poly), IsOrderedPolynomial poly) => UFD (Homogenised poly)
instance (Field (Coefficient poly), IsOrderedPolynomial poly) => PID (Homogenised poly)
instance (Field (Coefficient poly), IsOrderedPolynomial poly)
       => Euclidean (Homogenised poly) where
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
      recap m@(OrderedMonomial m0) =
        OrderedMonomial $ m0 :> fromIntegral d - totalDegree m
  in polynomial $
     M.mapKeysMonotonic recap $
     terms p

unhomogenise :: IsOrderedPolynomial poly => Homogenised poly -> poly
unhomogenise (Homogenised f) =
  substWith (*) (SV.singleton one) f

isHomogeneous :: IsOrderedPolynomial poly
              => poly -> Bool
isHomogeneous poly =
  let degs = map osum $ toList $ monomials poly
  in and $ zipWith (==) degs (tail degs)

tryHomogenise :: IsOrderedPolynomial poly => poly -> Either poly (Homogenised poly)
tryHomogenise f | isHomogeneous f = Left f
                | otherwise = Right $ homogenise f
