{-# LANGUAGE CPP, ConstraintKinds, DataKinds, EmptyCase, FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving          #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE IncoherentInstances, KindSignatures, MultiParamTypeClasses    #-}
{-# LANGUAGE OverloadedLabels, PolyKinds, RankNTypes, ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving, TemplateHaskell, TypeFamilies, TypeInType #-}
{-# LANGUAGE TypeOperators, UndecidableInstances, UndecidableSuperClasses  #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Algebra.Ring.Polynomial.Labeled
       (IsUniqueList, LabPolynomial(..),
        LabPolynomial', LabUnipol,
        canonicalMap,
        canonicalMap',
        IsSubsetOf) where
import Algebra.Internal
import Algebra.Ring.Polynomial
import Algebra.Ring.Polynomial.Univariate
import Algebra.Scalar

import           AlgebraicPrelude
import           Control.Lens                 (each, (%~), (&))
import           Data.Function                (on)
import qualified Data.List                    as L
import           Data.Singletons.Prelude
import           Data.Singletons.Prelude.Enum (SEnum (..))
import           Data.Singletons.Prelude.List hiding (Group)
import qualified Data.Sized.Builtin           as S
import           Data.Type.Natural.Class      (IsPeano (..), sOne)
import           GHC.Exts                     (Constraint)
import           GHC.OverloadedLabels         (IsLabel (..))
import qualified Numeric.Algebra              as NA
import qualified Prelude                      as P
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 802
import qualified Data.Text as T
#endif

type family UniqueList' (x :: Symbol) (xs :: [Symbol]) :: Constraint where
  UniqueList' x '[] = ()
  UniqueList' x (x ': xs) = TypeError ('Text "The variable " ':<>: 'ShowType x ':<>: 'Text " occurs more than once!")
  UniqueList' x (y ': xs) = UniqueList' x xs

type family UniqueList (xs :: [Symbol]) :: Constraint where
  UniqueList '[] = ()
  UniqueList (x ': xs) = (UniqueList' x xs, UniqueList xs)

class    (UniqueList xs) => IsUniqueList (xs :: [Symbol])
instance (UniqueList xs) => IsUniqueList (xs :: [Symbol])

-- | This instance allows something like @#x :: LabPolynomial (OrderedPolynomial Integer Grevlex 3) '["x", "y", "z"]@.
instance (KnownSymbol symb,
          SingI vars,
          UniqueList vars,
          IsPolynomial poly,
          Wraps vars poly,
          Elem symb vars ~ 'True) => IsLabel symb (LabPolynomial poly vars) where
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 802
  fromLabel =
    let vs = map T.unpack $ fromSing (sing :: Sing vars)
        v  = symbolVal @symb Proxy
    in maybe (error "impossible!") (var . toEnum) $ L.elemIndex v vs
#else
  fromLabel k =
    let vs = fromSing (sing :: Sing vars)
        v    = symbolVal' k
    in maybe (error "impossible!") (var . toEnum) $ L.elemIndex v vs
#endif

data LabPolynomial poly (vars :: [Symbol]) where
  LabelPolynomial :: (IsUniqueList vars, Length vars ~ Arity poly)
                  => { unLabelPolynomial :: !poly }
                  -> LabPolynomial poly vars

-- | Convenient type-synonym for @'LabPlynomial'@ wrapping @'OrderedPolynomial'@
--   and @'Unipol'@.
type family LabPolynomial' r ord vars where
  LabPolynomial' r ord '[x] = LabPolynomial (Unipol r) '[x]
  LabPolynomial' r ord vars = LabPolynomial (OrderedPolynomial r ord (Length vars)) vars

-- | Convenient type-synonym for @'LabPlynomial'@ wrapping univariate polynomial @'Unipol'@.
type LabUnipol r sym = LabPolynomial (Unipol r) '[sym]

type Wraps vars poly = (IsUniqueList vars, Arity poly ~ Length vars)

instance (PrettyCoeff (Coefficient poly), IsOrderedPolynomial poly, SingI vars)
      => Show (LabPolynomial poly vars) where
  showsPrec d (LabelPolynomial f) =
    let svs   = sing :: Sing vars
        vs    =
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 802
          map T.unpack $ 
#endif

          fromSing svs
        vsVec = generate sing $ \i -> vs !! fromEnum i
    in showsPolynomialWith vsVec d f

instance (UniqueList vars, Arity poly ~ Length vars, P.Num poly)
      => P.Num (LabPolynomial poly vars) where
  fromInteger = LabelPolynomial . P.fromInteger
  LabelPolynomial f + LabelPolynomial g = LabelPolynomial $ f P.+ g
  LabelPolynomial f * LabelPolynomial g = LabelPolynomial $ f P.* g
  abs = LabelPolynomial . P.abs . unLabelPolynomial
  LabelPolynomial f - LabelPolynomial g = LabelPolynomial $ f P.- g
  negate = LabelPolynomial . P.negate . unLabelPolynomial
  signum = LabelPolynomial . P.signum . unLabelPolynomial

instance (Wraps vars poly, Additive poly) => Additive (LabPolynomial poly vars) where
  LabelPolynomial f + LabelPolynomial g = LabelPolynomial $ f + g
  {-# INLINE (+) #-}

instance (Wraps vars poly, Multiplicative poly) => Multiplicative (LabPolynomial poly vars) where
  LabelPolynomial f * LabelPolynomial g =
    LabelPolynomial $ f * g
  {-# INLINE (*) #-}

instance (Wraps vars poly, Abelian poly)     => Abelian (LabPolynomial poly vars)
instance (Wraps vars poly, Commutative poly) => Commutative (LabPolynomial poly vars)
instance (Wraps vars poly, Unital poly) => Unital (LabPolynomial poly vars) where
  one = LabelPolynomial one
  {-# INLINE one #-}

instance (Wraps vars poly, Group poly) => Group (LabPolynomial poly vars) where
  negate (LabelPolynomial f) = LabelPolynomial (negate f)
  {-# INLINE negate #-}

instance (Wraps vars poly, RightModule Natural poly) => RightModule Natural (LabPolynomial poly vars) where
  LabelPolynomial f *. a = LabelPolynomial $  f *. a
  {-# INLINE (*.) #-}

instance (Wraps vars poly, LeftModule Natural poly) => LeftModule Natural (LabPolynomial poly vars) where
  a .* LabelPolynomial f = LabelPolynomial $ a .* f
  {-# INLINE (.*) #-}

instance (Wraps vars poly, RightModule Integer poly) => RightModule Integer (LabPolynomial poly vars) where
  LabelPolynomial f *. a = LabelPolynomial $  f *. a
  {-# INLINE (*.) #-}

instance (Wraps vars poly, LeftModule Integer poly) => LeftModule Integer (LabPolynomial poly vars) where
  a .* LabelPolynomial f = LabelPolynomial $ a .* f
  {-# INLINE (.*) #-}

instance (Wraps vars poly, Monoidal poly) => Monoidal (LabPolynomial poly vars) where
  zero = LabelPolynomial zero
  {-# INLINE zero #-}

instance (Wraps vars poly, Semiring poly) => Semiring (LabPolynomial poly vars)
instance (Wraps vars poly, Rig poly) => Rig (LabPolynomial poly vars)
instance (Wraps vars poly, Ring poly) => Ring (LabPolynomial poly vars) where
  fromInteger n = LabelPolynomial (NA.fromInteger n :: poly)
  {-# INLINE fromInteger #-}

instance (Wraps vars poly, LeftModule (Scalar r) poly)  => LeftModule  (Scalar r) (LabPolynomial poly vars) where
  a .* LabelPolynomial f = LabelPolynomial $ a .* f
  {-# INLINE (.*) #-}

instance (Wraps vars poly, RightModule (Scalar r) poly) => RightModule (Scalar r) (LabPolynomial poly vars) where
  LabelPolynomial f *. a = LabelPolynomial $ f *. a
  {-# INLINE (*.) #-}

instance (Wraps vars poly, DecidableZero poly) => DecidableZero (LabPolynomial poly vars) where
  isZero = isZero . unLabelPolynomial

instance (Wraps vars poly, Eq poly) => Eq (LabPolynomial poly vars) where
  (==) = (==) `on` unLabelPolynomial
  (/=) = (/=) `on` unLabelPolynomial

instance (Wraps vars poly, Ord poly) => Ord (LabPolynomial poly vars) where
  compare = compare `on` unLabelPolynomial
  (<=) = (<=) `on` unLabelPolynomial
  (>=) = (>=) `on` unLabelPolynomial
  (<)  = (<) `on` unLabelPolynomial
  (>)  = (>) `on` unLabelPolynomial

instance (IsPolynomial poly, Wraps vars poly) => IsPolynomial (LabPolynomial poly vars) where
  type Coefficient (LabPolynomial poly vars) = Coefficient poly
  type Arity (LabPolynomial poly vars) = Arity poly

  liftMap mor = liftMap mor . unLabelPolynomial
  {-# INLINE liftMap #-}

  terms' = terms' . unLabelPolynomial
  {-# INLINE terms' #-}

  monomials = monomials . unLabelPolynomial
  {-# INLINE monomials #-}

  coeff' m = coeff' m . unLabelPolynomial
  {-# INLINE coeff' #-}

  constantTerm = constantTerm . unLabelPolynomial
  {-# INLINE constantTerm #-}

  sArity _ = sArity (Proxy :: Proxy poly)
  {-# INLINE sArity #-}

  arity _ = arity (Proxy :: Proxy poly)
  {-# INLINE arity #-}

  fromMonomial m = LabelPolynomial (fromMonomial m :: poly)
  {-# INLINE fromMonomial #-}

  toPolynomial' (r, deg) = LabelPolynomial (toPolynomial' (r, deg) :: poly)
  {-# INLINE toPolynomial' #-}

  polynomial' dic = LabelPolynomial (polynomial' dic :: poly)
  {-# INLINE polynomial' #-}

  totalDegree' = totalDegree' . unLabelPolynomial
  {-# INLINE totalDegree' #-}

instance (IsOrderedPolynomial poly, Wraps vars poly) => IsOrderedPolynomial (LabPolynomial poly vars) where
  type MOrder (LabPolynomial poly vars) = MOrder poly

  leadingTerm = leadingTerm . unLabelPolynomial
  {-# INLINE leadingTerm #-}

  leadingCoeff = leadingCoeff . unLabelPolynomial
  {-# INLINE leadingCoeff #-}

  fromOrderedMonomial m = LabelPolynomial (fromOrderedMonomial m :: poly)
  {-# INLINE fromOrderedMonomial #-}

  orderedMonomials = orderedMonomials . unLabelPolynomial
  {-# INLINE orderedMonomials #-}

  toPolynomial (r, deg) = LabelPolynomial (toPolynomial (r, deg) :: poly)
  {-# INLINE toPolynomial #-}

  polynomial dic = LabelPolynomial (polynomial dic :: poly)
  {-# INLINE polynomial #-}

  terms = terms . unLabelPolynomial
  {-# INLINE terms #-}

  coeff m = coeff m . unLabelPolynomial
  {-# INLINE coeff #-}

  m >* LabelPolynomial f = LabelPolynomial (m >* f)
  {-# INLINE (>*) #-}

  LabelPolynomial f *< m = LabelPolynomial (f *< m)
  {-# INLINE (*<) #-}

  diff n (LabelPolynomial f) = LabelPolynomial (diff n f)
  {-# INLINE diff #-}

  mapMonomialMonotonic f (LabelPolynomial g) = LabelPolynomial $ mapMonomialMonotonic  f g
  {-# INLINE mapMonomialMonotonic #-}

instance (IsPolynomial poly, Wraps vars poly) => Hashable (LabPolynomial poly vars) where
  hashWithSalt s = hashWithSalt s . unLabelPolynomial

class    (All (FlipSym0 @@ ElemSym0 @@ ys) xs ~ 'True) => IsSubsetOf (xs :: [a]) (ys :: [a]) where
  _suppress :: proxy xs -> proxy ys -> x -> x
  _suppress _ _ = id
instance (All (FlipSym0 @@ ElemSym0 @@ ys) xs ~ 'True) => IsSubsetOf (xs :: [a]) (ys :: [a])

instance (ZeroProductSemiring poly , Wraps vars poly) => ZeroProductSemiring (LabPolynomial poly vars)
instance (IntegralDomain poly , Wraps vars poly) => IntegralDomain (LabPolynomial poly vars) where
  divides = divides `on` unLabelPolynomial
  maybeQuot f g = LabelPolynomial <$> maybeQuot (unLabelPolynomial f) (unLabelPolynomial g)
instance (UFD poly , Wraps vars poly) => UFD (LabPolynomial poly vars)
instance (PID poly , Wraps vars poly) => PID (LabPolynomial poly vars) where
  egcd (LabelPolynomial f) (LabelPolynomial g) =
    egcd f g & each %~ LabelPolynomial
instance (GCDDomain poly , Wraps vars poly) => GCDDomain (LabPolynomial poly vars) where
  gcd f g = LabelPolynomial $ gcd (unLabelPolynomial f) (unLabelPolynomial g)
  reduceFraction f g =
    reduceFraction (unLabelPolynomial f) (unLabelPolynomial g)
    & each %~ LabelPolynomial
  lcm f g = LabelPolynomial $ lcm (unLabelPolynomial f) (unLabelPolynomial g)
instance (UnitNormalForm poly , Wraps vars poly) => UnitNormalForm (LabPolynomial poly vars) where
  splitUnit = (each %~ LabelPolynomial) . splitUnit . unLabelPolynomial
instance (DecidableUnits poly , Wraps vars poly) => DecidableUnits (LabPolynomial poly vars) where
  isUnit = isUnit . unLabelPolynomial
  recipUnit = fmap LabelPolynomial . recipUnit . unLabelPolynomial
  LabelPolynomial f ^? n = LabelPolynomial <$> (f ^? n)

instance (DecidableAssociates poly , Wraps vars poly)
      => DecidableAssociates (LabPolynomial poly vars) where
  isAssociate = isAssociate `on` unLabelPolynomial

instance (Euclidean poly , Wraps vars poly)
      => Euclidean (LabPolynomial poly vars) where
  degree = degree . unLabelPolynomial
  divide (LabelPolynomial f) (LabelPolynomial g) =
    divide f g & each %~ LabelPolynomial
  quot f g = LabelPolynomial $ quot (unLabelPolynomial f) (unLabelPolynomial g)
  rem f g = LabelPolynomial $ rem (unLabelPolynomial f) (unLabelPolynomial g)

-- | So unsafe! Don't expose it!
permute0 :: (SEq k) => SList (xs :: [k]) -> SList (ys :: [k]) -> Sized (Length xs) Integer
permute0 SNil _ = S.NilL
permute0 (SCons x xs) ys =
  case sElemIndex x ys of
    SJust n  ->
      let k = sLength xs
      in coerceLength (plusComm k sOne) $ withKnownNat (sSucc k) $
         withKnownNat k $ (fromIntegral (toNatural n) S.:< permute0 xs ys)
    SNothing -> error "oops, you called permute0 for non-subset..."

permute :: forall (xs :: [k])  ys. (IsSubsetOf xs ys , SEq k)
        => SList xs -> SList ys -> Sized (Length xs) Integer
permute = _suppress (Proxy :: Proxy xs) (Proxy :: Proxy ys) permute0

canonicalMap :: forall xs ys poly poly'.
                (SingI xs, SingI ys, IsSubsetOf xs ys,
                 Wraps xs poly, Wraps ys poly',
                 IsPolynomial poly, IsPolynomial poly',
                 Coefficient poly ~ Coefficient poly')
             => LabPolynomial poly xs -> LabPolynomial poly' ys
canonicalMap (LabelPolynomial f) =
  let sxs  = sing :: Sing xs
      sys  = sing :: Sing ys
      dics = permute sxs sys
      ords = enumOrdinal (sArity $ Just ans)
      mor o = var (ords !! fromInteger (dics S.%!! o)) :: poly'
      ans   = liftMap mor f
  in LabelPolynomial ans
{-# INLINE canonicalMap #-}

canonicalMap' :: (SingI xs, SingI ys, IsSubsetOf xs ys,
                 Wraps xs poly, Wraps ys poly',
                 IsPolynomial poly, IsPolynomial poly',
                 Coefficient poly ~ Coefficient poly')
              => proxy poly' -> proxy' ys -> LabPolynomial poly xs -> LabPolynomial poly' ys
canonicalMap' _ _ = canonicalMap
{-# INLINE canonicalMap' #-}
