{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, GADTs        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses          #-}
{-# LANGUAGE NoImplicitPrelude, ScopedTypeVariables, StandaloneDeriving #-}
{-# LANGUAGE TypeApplications, TypeFamilies, TypeOperators              #-}
{-# LANGUAGE UndecidableSuperClasses                                    #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}
module Algebra.Ring.Polynomial.Recursive
       (RecPoly, runRecPoly) where
import Algebra.Prelude

import           Control.Lens              (ifoldMap, (%~), _Unwrapping')
import qualified Data.Map                  as M
import           Data.Singletons.Prelude   (If, PEq (..), SEq (..))
import           Data.Type.Ordinal.Builtin
import qualified Numeric.Algebra           as NA
import qualified Prelude                   as P

data CheckZero n where
  EqZero :: CheckZero 0
  EqSucc :: ((Succ m :== 0) ~ 'False) => Sing m -> CheckZero (Succ m)

checkZero :: Sing n -> CheckZero n
checkZero n =
  case zeroOrSucc n of
    IsZero -> EqZero
    IsSucc m ->
      case sSucc m %:== Zero of
        SFalse -> EqSucc m
        STrue  -> error "Cannot happen!"

type AppS f g x (n :: Nat) = If (n :== 0) x (f (g (n-1)))
newtype RecPoly k n = RecPoly { runRecPoly_ :: AppS Unipol (RecPoly k) k n }

runRecPoly :: forall k n. KnownNat n
           => RecPoly k (Succ n) -> Unipol (RecPoly k n)
runRecPoly f =
  case checkZero (sing :: Sing (Succ n)) of
    EqSucc m ->
      case f of
        (RecPoly g) -> withKnownNat m g

instance (KnownNat n, CoeffRing k) => Additive (RecPoly k n) where
  RecPoly f + RecPoly g =
    case checkZero (sing :: Sing n) of
      EqZero -> RecPoly $ f + g
      EqSucc m -> withKnownNat m $ RecPoly $ f + g
  {-# INLINE (+) #-}

instance (KnownNat n, CoeffRing k) => Monoidal (RecPoly k n) where
  zero =
    case checkZero (sing :: Sing n) of
      EqZero -> RecPoly zero
      EqSucc m -> withKnownNat m $ RecPoly zero
  {-# INLINE zero #-}

instance (KnownNat n, CoeffRing k) => Abelian (RecPoly k n)
instance (KnownNat n, CoeffRing k) => Group (RecPoly k n) where
  RecPoly f - RecPoly g =
    case checkZero (sing :: Sing n) of
      EqZero -> RecPoly $ f - g
      EqSucc m -> withKnownNat m $ RecPoly $ f - g
  {-# INLINE (-) #-}

  negate (RecPoly f) =
    case checkZero (sing :: Sing n) of
      EqZero -> RecPoly $ negate f
      EqSucc m -> withKnownNat m $ RecPoly $ negate f
  {-# INLINE negate #-}

instance (KnownNat n, CoeffRing k) => LeftModule Natural (RecPoly k n) where
  n .* RecPoly g =
    case checkZero (sing :: Sing n) of
      EqZero -> RecPoly $ n .* g
      EqSucc m -> withKnownNat m $ RecPoly $ n .* g
  {-# INLINE (.*) #-}

instance (KnownNat n, CoeffRing k) => RightModule Natural (RecPoly k n) where
  RecPoly g *. n =
    case checkZero (sing :: Sing n) of
      EqZero -> RecPoly $ g *. n
      EqSucc m -> withKnownNat m $ RecPoly $ g *. n
  {-# INLINE (*.) #-}

instance (KnownNat n, CoeffRing k) => LeftModule Integer (RecPoly k n) where
  n .* RecPoly g =
    case checkZero (sing :: Sing n) of
      EqZero -> RecPoly $ n .* g
      EqSucc m -> withKnownNat m $ RecPoly $ n .* g
  {-# INLINE (.*) #-}

instance (KnownNat n, CoeffRing k) => RightModule Integer (RecPoly k n) where
  RecPoly g *. n =
    case checkZero (sing :: Sing n) of
      EqZero -> RecPoly $ g *. n
      EqSucc m -> withKnownNat m $ RecPoly $ g *. n
  {-# INLINE (*.) #-}

instance (KnownNat n, CoeffRing k) => Multiplicative (RecPoly k n) where
  RecPoly f * RecPoly g =
    case checkZero (sing :: Sing n) of
      EqZero -> RecPoly $ f + g
      EqSucc m -> withKnownNat m $ RecPoly $ f * g
  {-# INLINE (*) #-}

instance (KnownNat n, CoeffRing k) => LeftModule (Scalar k) (RecPoly k n) where
  Scalar n .* RecPoly g =
    case checkZero (sing :: Sing n) of
      EqZero -> RecPoly $ n * g
      EqSucc m ->
        withKnownNat m $ withRefl (predSucc m) $
        RecPoly $ mapCoeff' (Scalar n .*) g
  {-# INLINE (.*) #-}

instance (KnownNat n, CoeffRing k) => RightModule (Scalar k) (RecPoly k n) where
  RecPoly g *. Scalar n =
    case checkZero (sing :: Sing n) of
      EqZero -> RecPoly $ g * n
      EqSucc m ->
        withKnownNat m $ withRefl (predSucc m) $
        RecPoly $ mapCoeff' (*. Scalar n) g
  {-# INLINE (*.) #-}

instance (KnownNat n, CoeffRing k) => Unital (RecPoly k n) where
  one =
    case checkZero (sing :: Sing n) of
      EqZero   -> RecPoly one
      EqSucc m -> withKnownNat m $ RecPoly one
  {-# INLINE one #-}

instance (KnownNat n, CoeffRing k) => Commutative (RecPoly k n)
instance (KnownNat n, CoeffRing k) => Semiring (RecPoly k n)
instance (KnownNat n, CoeffRing k) => Rig (RecPoly k n) where
  fromNatural n =
    case checkZero (sing :: Sing n) of
      EqZero   -> RecPoly $ fromNatural n
      EqSucc m -> withKnownNat m $ RecPoly $ fromNatural n
  {-# INLINE fromNatural #-}

instance (KnownNat n, CoeffRing k) => Ring (RecPoly k n) where
  fromInteger n =
    case checkZero (sing :: Sing n) of
      EqZero   -> RecPoly $ NA.fromInteger n
      EqSucc m -> withKnownNat m $ RecPoly $ NA.fromInteger n
  {-# INLINE fromInteger #-}

instance (KnownNat n, CoeffRing k) => DecidableZero (RecPoly k n) where
  isZero (RecPoly n) =
    case checkZero (sing :: Sing n) of
      EqZero   -> isZero n
      EqSucc m -> withKnownNat m $ isZero n
  {-# INLINE isZero #-}

instance (KnownNat n, CoeffRing k) => Eq (RecPoly k n) where
  RecPoly f == RecPoly g =
    case checkZero (sing :: Sing n) of
      EqZero -> f == g
      EqSucc m ->
        withKnownNat m $ withRefl (predSucc m) $ f == g
  {-# INLINE (==) #-}


instance (KnownNat n, CoeffRing k) => IsPolynomial (RecPoly k n) where
  type Coefficient (RecPoly k n) = k
  type Arity       (RecPoly k n) = n
  sArity _ = sing
  var o =
    case checkZero (sing :: Sing n) of
      EqZero -> absurdOrd o
      EqSucc m ->
        withKnownNat m $ withRefl (predSucc m) $ case o of
        OS n -> RecPoly $ injectCoeff (var n)
        _    -> RecPoly $ var 0

  fromMonomial mon =
    case checkZero (sing :: Sing n) of
      EqZero   -> one
      EqSucc m ->
        withKnownNat m $
        case mon of
          n :< ls ->
            let len = sizedLength ls
            in withRefl (succInj' m len Refl) $
               RecPoly $ var 0 ^ fromIntegral n * injectCoeff (fromMonomial ls)
          _ -> one

  liftMap f (RecPoly g) =
    case checkZero (sing :: Sing n) of
      EqZero -> Scalar g .* one
      EqSucc m ->
        withKnownNat m $ withRefl (predSucc m) $
        substWith ((*) . liftMap (f . OS)) (singleton $ f 0) g


  injectCoeff k =
    case checkZero (sing :: Sing n) of
      EqZero -> RecPoly k
      EqSucc (m :: Sing m) ->
        withKnownNat m $ RecPoly $ injectCoeff (injectCoeff k :: RecPoly k m)

  terms' (RecPoly f) =
    case checkZero (sing :: Sing n) of
      EqZero   -> M.singleton (fromList sZero []) f
      EqSucc m ->
        withKnownNat m $ withRefl (predSucc m) $
        ifoldMap (M.mapKeys . (:<) . (sIndex 0)) $
        fmap terms' $ terms' f

instance (KnownNat n, CoeffRing r, PrettyCoeff r)
       => Show (RecPoly r n) where
  showsPrec =
    showsPolynomialWith $ generate sing (\i -> "X_" ++ show (fromEnum i))

instance (CoeffRing k, KnownNat n) => IsOrderedPolynomial (RecPoly k n) where
  type MOrder (RecPoly k n) = Lex
  leadingTerm (RecPoly u) =
    case checkZero (sing :: Sing n) of
      EqZero -> (u, one)
      EqSucc m ->
        withKnownNat m $
        let (k , OrderedMonomial ind) = leadingTerm u
            (c, OrderedMonomial ts) = leadingTerm k
        in withRefl (succInj' (sizedLength ind) m Refl) $ case ind of
          n :< NilL -> (c, OrderedMonomial $ n :< ts)
          _ -> error "bug in ghc"

instance (CoeffRing k, DecidableUnits k, KnownNat n) => DecidableUnits (RecPoly k n) where
  recipUnit = recipUnitDefault
  isUnit = isUnitDefault

instance (CoeffRing k, UnitNormalForm k, KnownNat n) => DecidableAssociates (RecPoly k n) where
  isAssociate = isAssociateDefault

instance (CoeffRing k, UnitNormalForm k, KnownNat n) => UnitNormalForm (RecPoly k n) where
  splitUnit = splitUnitDefault

instance (CoeffRing k, UnitNormalForm k, KnownNat n)
      => P.Num (RecPoly k n) where
  fromInteger = unwrapAlgebra . fromInteger
  (+) = (NA.+)
  (-) = (NA.-)
  negate = _Unwrapping' WrapAlgebra %~ P.negate
  (*) = (NA.*)
  abs = _Unwrapping' WrapAlgebra %~ P.abs
  signum = _Unwrapping' WrapAlgebra %~ P.signum
