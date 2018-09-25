{-# LANGUAGE CPP, ConstraintKinds, DataKinds, FlexibleContexts             #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving          #-}
{-# LANGUAGE IncoherentInstances, KindSignatures, MultiParamTypeClasses    #-}
{-# LANGUAGE OverloadedLabels, PatternSynonyms, PolyKinds, RankNTypes      #-}
{-# LANGUAGE RoleAnnotations, ScopedTypeVariables, TypeApplications        #-}
{-# LANGUAGE TypeFamilies, TypeInType, TypeOperators, UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses                                       #-}
module Algebra.Ring.Polynomial.Labeled
       (IsUniqueList, LabPolynomial(LabelPolynomial, unLabelPolynomial),
        LabPolynomial', LabUnipol, Wraps,
        canonicalMap,
        canonicalMap',
        renameVars, renameVars',
        IsSubsetOf) where
import Algebra.Internal
import Algebra.Ring.Polynomial
import Algebra.Ring.Polynomial.Univariate
import Algebra.Scalar

import           AlgebraicPrelude
import           Control.DeepSeq              (NFData)
import           Control.Lens                 (each, (%~), (&))
import qualified Data.Coerce                  as DC
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
        v  = symbolVal (Proxy :: Proxy symb)
    in maybe (error "impossible!") (var . toEnum) $ L.elemIndex v vs
#else
  fromLabel k =
    let vs = fromSing (sing :: Sing vars)
        v    = symbolVal' k
    in maybe (error "impossible!") (var . toEnum) $ L.elemIndex v vs
#endif

newtype LabPolynomial poly (vars :: [Symbol]) =
  LabelPolynomial_ { _unLabelPolynomial :: poly }
  deriving (NFData)
type role LabPolynomial representational nominal

{-# COMPLETE LabelPolynomial #-}
pattern LabelPolynomial :: Wraps vars poly => Wraps vars poly
                        => poly -> LabPolynomial poly vars
pattern LabelPolynomial { unLabelPolynomial } =
  LabelPolynomial_ unLabelPolynomial


-- | Convenient type-synonym for @'LabPlynomial'@ wrapping @'OrderedPolynomial'@
--   and @'Unipol'@.
type family LabPolynomial' r ord vars where
  LabPolynomial' r ord '[x] = LabPolynomial (Unipol r) '[x]
  LabPolynomial' r ord vars = LabPolynomial (OrderedPolynomial r ord (Length vars)) vars

-- | Convenient type-synonym for @'LabPlynomial'@ wrapping univariate polynomial @'Unipol'@.
type LabUnipol r sym = LabPolynomial (Unipol r) '[sym]

type Wraps vars poly = (IsUniqueList vars, Arity poly ~ Length vars)

instance (PrettyCoeff (Coefficient poly), IsOrderedPolynomial poly, Wraps vars poly, SingI vars)
      => Show (LabPolynomial poly vars) where
  showsPrec d (LabelPolynomial_ f) =
    let svs   = sing :: Sing vars
        vs    =
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 802
          map T.unpack $
#endif

          fromSing svs
        vsVec = generate sing $ \i -> vs !! fromEnum i
    in showsPolynomialWith vsVec d f

instance (Wraps vars poly, P.Num poly)
      => P.Num (LabPolynomial poly vars) where
  fromInteger = LabelPolynomial_ . P.fromInteger
  LabelPolynomial_ f + LabelPolynomial_ g = LabelPolynomial_ $ f P.+ g
  LabelPolynomial_ f * LabelPolynomial_ g = LabelPolynomial_ $ f P.* g
  abs = LabelPolynomial_ . P.abs . _unLabelPolynomial
  LabelPolynomial_ f - LabelPolynomial_ g = LabelPolynomial_ $ f P.- g
  negate = LabelPolynomial_ . P.negate . _unLabelPolynomial
  signum = LabelPolynomial_ . P.signum . _unLabelPolynomial

instance (Wraps vars poly, Additive poly) => Additive (LabPolynomial poly vars) where
  LabelPolynomial_ f + LabelPolynomial_ g = LabelPolynomial_ $ f + g
  {-# INLINE (+) #-}

instance (Wraps vars poly, Multiplicative poly) => Multiplicative (LabPolynomial poly vars) where
  LabelPolynomial_ f * LabelPolynomial_ g =
    LabelPolynomial_ $ f * g
  {-# INLINE (*) #-}

instance (Wraps vars poly, Abelian poly)     => Abelian (LabPolynomial poly vars)
instance (Wraps vars poly, Commutative poly) => Commutative (LabPolynomial poly vars)
instance (Wraps vars poly, Unital poly) => Unital (LabPolynomial poly vars) where
  one = LabelPolynomial_ one
  {-# INLINE one #-}

instance (Wraps vars poly, Group poly) => Group (LabPolynomial poly vars) where
  negate = DC.coerce @(poly -> poly) negate
  {-# INLINE negate #-}

instance (Wraps vars poly, RightModule Natural poly) => RightModule Natural (LabPolynomial poly vars) where
  LabelPolynomial_ f *. a = LabelPolynomial_ $  f *. a
  {-# INLINE (*.) #-}

instance (Wraps vars poly, LeftModule Natural poly) => LeftModule Natural (LabPolynomial poly vars) where
  a .* LabelPolynomial_ f = LabelPolynomial_ $ a .* f
  {-# INLINE (.*) #-}

instance (Wraps vars poly, RightModule Integer poly) => RightModule Integer (LabPolynomial poly vars) where
  LabelPolynomial_ f *. a = LabelPolynomial_ $  f *. a
  {-# INLINE (*.) #-}

instance (Wraps vars poly, LeftModule Integer poly) => LeftModule Integer (LabPolynomial poly vars) where
  a .* LabelPolynomial_ f = LabelPolynomial_ $ a .* f
  {-# INLINE (.*) #-}

instance (Wraps vars poly, Monoidal poly) => Monoidal (LabPolynomial poly vars) where
  zero = LabelPolynomial_ zero
  {-# INLINE zero #-}

instance (Wraps vars poly, Semiring poly) => Semiring (LabPolynomial poly vars)
instance (Wraps vars poly, Rig poly) => Rig (LabPolynomial poly vars)
instance (Wraps vars poly, Ring poly) => Ring (LabPolynomial poly vars) where
  fromInteger n = LabelPolynomial_ (NA.fromInteger n :: poly)
  {-# INLINE fromInteger #-}

instance (Wraps vars poly, LeftModule (Scalar r) poly)  => LeftModule  (Scalar r) (LabPolynomial poly vars) where
  a .* LabelPolynomial_ f = LabelPolynomial_ $ a .* f
  {-# INLINE (.*) #-}

instance (Wraps vars poly, RightModule (Scalar r) poly) => RightModule (Scalar r) (LabPolynomial poly vars) where
  LabelPolynomial_ f *. a = LabelPolynomial_ $ f *. a
  {-# INLINE (*.) #-}

instance (Wraps vars poly, DecidableZero poly) => DecidableZero (LabPolynomial poly vars) where
  isZero = isZero . _unLabelPolynomial

instance (Wraps vars poly, Eq poly) => Eq (LabPolynomial poly vars) where
  (==) = (==) `on` _unLabelPolynomial
  (/=) = (/=) `on` _unLabelPolynomial

instance (Wraps vars poly, Ord poly) => Ord (LabPolynomial poly vars) where
  compare = compare `on` _unLabelPolynomial
  (<=) = (<=) `on` _unLabelPolynomial
  (>=) = (>=) `on` _unLabelPolynomial
  (<)  = (<) `on` _unLabelPolynomial
  (>)  = (>) `on` _unLabelPolynomial

instance (IsPolynomial poly, Wraps vars poly) => IsPolynomial (LabPolynomial poly vars) where
  type Coefficient (LabPolynomial poly vars) = Coefficient poly
  type Arity (LabPolynomial poly vars) = Arity poly

  liftMap mor = liftMap mor . _unLabelPolynomial
  {-# INLINE liftMap #-}

  terms' = terms' . _unLabelPolynomial
  {-# INLINE terms' #-}

  monomials = monomials . _unLabelPolynomial
  {-# INLINE monomials #-}

  coeff' m = coeff' m . _unLabelPolynomial
  {-# INLINE coeff' #-}

  constantTerm = constantTerm . _unLabelPolynomial
  {-# INLINE constantTerm #-}

  sArity _ = sArity (Proxy :: Proxy poly)
  {-# INLINE sArity #-}

  arity _ = arity (Proxy :: Proxy poly)
  {-# INLINE arity #-}

  fromMonomial m = LabelPolynomial_ (fromMonomial m :: poly)
  {-# INLINE fromMonomial #-}

  toPolynomial' (r, deg) = LabelPolynomial_ (toPolynomial' (r, deg) :: poly)
  {-# INLINE toPolynomial' #-}

  polynomial' dic = LabelPolynomial_ (polynomial' dic :: poly)
  {-# INLINE polynomial' #-}

  totalDegree' = totalDegree' . _unLabelPolynomial
  {-# INLINE totalDegree' #-}

instance (IsOrderedPolynomial poly, Wraps vars poly) => IsOrderedPolynomial (LabPolynomial poly vars) where
  type MOrder (LabPolynomial poly vars) = MOrder poly

  leadingTerm = leadingTerm . _unLabelPolynomial
  {-# INLINE leadingTerm #-}

  leadingCoeff = leadingCoeff . _unLabelPolynomial
  {-# INLINE leadingCoeff #-}

  splitLeadingTerm = DC.coerce @(poly -> (Term poly, poly)) splitLeadingTerm
  {-# INLINE splitLeadingTerm #-}

  fromOrderedMonomial m = LabelPolynomial_ (fromOrderedMonomial m :: poly)
  {-# INLINE fromOrderedMonomial #-}

  orderedMonomials = orderedMonomials . _unLabelPolynomial
  {-# INLINE orderedMonomials #-}

  toPolynomial (r, deg) = LabelPolynomial_ (toPolynomial (r, deg) :: poly)
  {-# INLINE toPolynomial #-}

  polynomial dic = LabelPolynomial_ (polynomial dic :: poly)
  {-# INLINE polynomial #-}

  terms = terms . _unLabelPolynomial
  {-# INLINE terms #-}

  coeff m = coeff m . _unLabelPolynomial
  {-# INLINE coeff #-}

  m >* LabelPolynomial_ f = LabelPolynomial_ (m >* f)
  {-# INLINE (>*) #-}

  LabelPolynomial_ f *< m = LabelPolynomial_ (f *< m)
  {-# INLINE (*<) #-}

  diff n (LabelPolynomial_ f) = LabelPolynomial_ (diff n f)
  {-# INLINE diff #-}

  mapMonomialMonotonic f (LabelPolynomial_ g) = LabelPolynomial_ $ mapMonomialMonotonic  f g
  {-# INLINE mapMonomialMonotonic #-}

class    (All (FlipSym0 @@ ElemSym0 @@ ys) xs ~ 'True) => IsSubsetOf (xs :: [a]) (ys :: [a]) where
  _suppress :: proxy xs -> proxy ys -> x -> x
  _suppress _ _ = id
instance (All (FlipSym0 @@ ElemSym0 @@ ys) xs ~ 'True) => IsSubsetOf (xs :: [a]) (ys :: [a])

instance (ZeroProductSemiring poly , Wraps vars poly) => ZeroProductSemiring (LabPolynomial poly vars)
instance (IntegralDomain poly , Wraps vars poly) => IntegralDomain (LabPolynomial poly vars) where
  divides = divides `on` _unLabelPolynomial
  maybeQuot f g = LabelPolynomial_ <$> maybeQuot (_unLabelPolynomial f) (_unLabelPolynomial g)
instance (UFD poly , Wraps vars poly) => UFD (LabPolynomial poly vars)
instance (PID poly , Wraps vars poly) => PID (LabPolynomial poly vars) where
  egcd (LabelPolynomial_ f) (LabelPolynomial_ g) =
    egcd f g & each %~ LabelPolynomial_
instance (GCDDomain poly , Wraps vars poly) => GCDDomain (LabPolynomial poly vars) where
  gcd f g = LabelPolynomial_ $ gcd (_unLabelPolynomial f) (_unLabelPolynomial g)
  reduceFraction f g =
    reduceFraction (_unLabelPolynomial f) (_unLabelPolynomial g)
    & each %~ LabelPolynomial_
  lcm f g = LabelPolynomial_ $ lcm (_unLabelPolynomial f) (_unLabelPolynomial g)
instance (UnitNormalForm poly , Wraps vars poly) => UnitNormalForm (LabPolynomial poly vars) where
  splitUnit = (each %~ LabelPolynomial_) . splitUnit . _unLabelPolynomial
instance (DecidableUnits poly , Wraps vars poly) => DecidableUnits (LabPolynomial poly vars) where
  isUnit = isUnit . _unLabelPolynomial
  recipUnit = fmap LabelPolynomial_ . recipUnit . _unLabelPolynomial
  LabelPolynomial_ f ^? n = LabelPolynomial_ <$> (f ^? n)

instance (DecidableAssociates poly , Wraps vars poly)
      => DecidableAssociates (LabPolynomial poly vars) where
  isAssociate = isAssociate `on` _unLabelPolynomial

instance (Euclidean poly , Wraps vars poly)
      => Euclidean (LabPolynomial poly vars) where
  degree = degree . _unLabelPolynomial
  divide (LabelPolynomial_ f) (LabelPolynomial_ g) =
    divide f g & each %~ LabelPolynomial_
  quot f g = LabelPolynomial_ $ quot (_unLabelPolynomial f) (_unLabelPolynomial g)
  rem f g = LabelPolynomial_ $ rem (_unLabelPolynomial f) (_unLabelPolynomial g)

-- | So unsafe! Don't expose it!
permute0 :: (SEq k) => SList (xs :: [k]) -> SList (ys :: [k]) -> Sized (Length xs) Integer
permute0 SNil _ = S.NilL
permute0 (SCons x xs) ys =
  case sElemIndex x ys of
    SJust n  ->
      let k = sLength xs
      in coerceLength (plusComm k sOne) $ withKnownNat (sSucc k) $
         withKnownNat k (fromIntegral (toNatural n) S.:< permute0 xs ys)
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
canonicalMap (LabelPolynomial_ f) =
  let sxs  = sing :: Sing xs
      sys  = sing :: Sing ys
      dics = permute sxs sys
      ords = enumOrdinal (sArity $ Just ans)
      mor o = var (ords !! fromInteger (dics S.%!! o)) :: poly'
      ans   = liftMap mor f
  in LabelPolynomial_ ans
{-# INLINE canonicalMap #-}

canonicalMap' :: (SingI xs, SingI ys, IsSubsetOf xs ys,
                 Wraps xs poly, Wraps ys poly',
                 IsPolynomial poly, IsPolynomial poly',
                 Coefficient poly ~ Coefficient poly')
              => proxy poly' -> proxy' ys -> LabPolynomial poly xs -> LabPolynomial poly' ys
canonicalMap' _ _ = canonicalMap
{-# INLINE canonicalMap' #-}

renameVars :: (SingI ys, SingI xs, Length xs ~ Length ys, IsPolynomial poly)
           => LabPolynomial poly xs -> LabPolynomial poly ys
renameVars = DC.coerce
{-# INLINE renameVars #-}

renameVars' :: (SingI ys, SingI xs, Length xs ~ Length ys, IsPolynomial poly)
           => proxy ys -> LabPolynomial poly xs -> LabPolynomial poly ys
renameVars' _ = DC.coerce
{-# INLINE renameVars' #-}
