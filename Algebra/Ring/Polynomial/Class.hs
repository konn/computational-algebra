{-# LANGUAGE ConstraintKinds, DataKinds, DefaultSignatures              #-}
{-# LANGUAGE ExplicitNamespaces, FlexibleContexts, FlexibleInstances    #-}
{-# LANGUAGE GADTs, LiberalTypeSynonyms, MultiParamTypeClasses          #-}
{-# LANGUAGE NoImplicitPrelude, ParallelListComp, PolyKinds, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, TypeOperators           #-}
{-# LANGUAGE UndecidableInstances                                       #-}
-- | This module provides abstract classes for finitary polynomial types.
module Algebra.Ring.Polynomial.Class ( IsPolynomial(..), IsOrderedPolynomial(..)
                                     , CoeffRing, oneNorm, maxNorm, monoize,
                                       sPolynomial, pDivModPoly, content, pp,
                                       injectVars, vars
                                     ) where
import Algebra.Internal
import Algebra.Ring.Polynomial.Monomial
import Algebra.Scalar
import Algebra.Wrapped

import           Control.Arrow            (first)
import           Control.Lens             (folded, maximumOf)
import           Data.Foldable            (foldr, maximum)
import qualified Data.Foldable            as F
import qualified Data.HashSet             as HS
import qualified Data.Map.Strict          as M
import qualified Data.Set                 as S
import           Data.Singletons.Prelude  (SingKind (..))
import qualified Data.Sized.Builtin       as V
import           Data.Type.Ordinal        (Ordinal, enumOrdinal, inclusion)
import           GHC.TypeLits             (KnownNat, Nat)
import           Numeric.Algebra          (Additive (..), Commutative)
import           Numeric.Algebra          (Division (..), Field, Group (..))
import           Numeric.Algebra          (LeftModule (..), Module)
import           Numeric.Algebra          (Monoidal (..), Multiplicative (..))
import           Numeric.Algebra          (Ring (fromInteger), Unital (..), sum)
import           Numeric.Decidable.Zero   (DecidableZero (..))
import           Numeric.Domain.Euclidean (Euclidean, gcd, quot)
import           Numeric.Natural          (Natural)
import           Prelude                  (Eq (..), Int, Maybe (..), flip, fmap)
import           Prelude                  (fromIntegral, fst, map, maybe, not)
import           Prelude                  (otherwise, snd, uncurry, ($), (.))
import           Prelude                  ((<$>), (<*>))
import qualified Prelude                  as P

infixl 7 *<, >*, *|<, >|*

-- | Constraint synonym for rings that can be used as polynomial coefficient.
class    (DecidableZero r, Ring r, Commutative r, Eq r) => CoeffRing r
instance (DecidableZero r, Ring r, Commutative r, Eq r) => CoeffRing r

-- | Polynomial in terms of free associative commutative algebra generated
--   by n-elements.
--   To effectively compute all terms, we need @'monomials'@ in addition to
--   universality of free object.
class (CoeffRing (Coefficient poly), Eq poly, DecidableZero poly, KnownNat (Arity poly),
       Module (Scalar (Coefficient poly)) poly, Ring poly, Commutative poly)
   => IsPolynomial poly where
  {-# MINIMAL ((liftMap , monomials) | terms'), (sArity | sArity') , (fromMonomial | toPolynomial' | polynomial') #-}
  -- | Coefficient ring of polynomial type.
  type Coefficient poly :: *
  -- | Arity of polynomial type.
  type Arity poly :: Nat

  -- | Universal mapping for free algebra.
  --   This corresponds to the algebraic substitution operation.
  liftMap :: (Module (Scalar (Coefficient poly)) alg, Ring alg, Commutative alg)
           => (Ordinal (Arity poly) -> alg) -> poly -> alg
  liftMap mor f =
    sum [ Scalar r .* sum [ Scalar (fromInteger (P.fromIntegral i) :: Coefficient poly) .* mor o
                          | i <- V.toList (m :: Monomial (Arity poly)) :: [Int]
                          | o <- enumOrdinal (sArity (Nothing :: Maybe poly)) ]
        | (m, r) <- M.toList (terms' f) ]
  {-# INLINE liftMap #-}

  -- | A variant of @'liftMap'@, each value is given by @'Sized'@.
  subst :: (Ring alg, Commutative alg, Module (Scalar (Coefficient poly)) alg)
        => Sized (Arity poly) alg -> poly -> alg
  subst dic f = liftMap (dic V.%!!) f
  {-# INLINE subst #-}

  -- | Another variant of @'liftMap'@.
  --   This function relies on @'terms''@; if you have more efficient implementation,
  --   it is encouraged to override this method.
  substWith :: (Unital r, Monoidal m)
            => (Coefficient poly -> r -> m) -> Sized (Arity poly) r -> poly -> m
  substWith o pt poly = sum $ P.map (uncurry (flip o) . first extractPower) $ M.toList $ terms' poly
    where
      extractPower = F.foldr (*) one . V.zipWithSame pow pt .
                     V.map (P.fromIntegral :: Int -> Natural)
  {-# INLINE substWith #-}

  -- | Arity of given polynomial.
  sArity' :: poly -> SNat (Arity poly)
  sArity' = sArity . Just

  -- | Arity of given polynomial, using type proxy.
  sArity :: proxy poly -> SNat (Arity poly)
  sArity _ = sArity' (zero :: poly)
  {-# INLINE sArity #-}

  -- | Non-dependent version of arity.
  arity :: proxy poly -> P.Integer
  arity _pxy = fromSing (sArity' (zero :: poly))
  {-# INLINE arity #-}

  -- | Inject coefficient into polynomial.
  injectCoeff :: Coefficient poly -> poly
  injectCoeff r = Scalar r .* one
  {-# INLINE injectCoeff #-}

  -- | Inject coefficient into polynomial with result-type explicitly given.
  injectCoeff' :: proxy poly -> Coefficient poly -> poly
  injectCoeff' _ = injectCoeff
  {-# INLINE injectCoeff' #-}

  -- | @'monomials' f@ returns the finite set of all monomials appearing in @f@.
  monomials :: poly -> HS.HashSet (Monomial (Arity poly))
  monomials = HS.fromList . M.keys . terms'
  {-# INLINE monomials #-}

  -- | @'monomials' f@ returns the finite set of all terms appearing in @f@;
  --   Term is a finite map from monomials to non-zero coefficient.
  terms' :: poly -> M.Map (Monomial (Arity poly)) (Coefficient poly)
  terms' f = M.fromList [ (m, c)
                        | m <- HS.toList $ monomials f
                        , let c = coeff' m f
                        , not (isZero c)
                        ]
  {-# INLINE terms' #-}

  -- | @'coeff m f'@ returns the coefficient of monomial @m@ in polynomial @f@.
  coeff' :: Monomial (Arity poly) -> poly -> Coefficient poly
  coeff' m = runCoeff . liftMap (\i -> WrapCoeff $ fromInteger $ P.fromIntegral $ m V.%!! i)
  {-# INLINE coeff' #-}

  -- | Calculates constant coefficient.
  constantTerm :: poly -> Coefficient poly
  constantTerm = runCoeff . liftMap (\ _ -> WrapCoeff zero)
  {-# INLINE constantTerm #-}

  -- | Inject monic monomial.
  fromMonomial :: Monomial (Arity poly) -> poly
  fromMonomial m = toPolynomial' (one , m)
  {-# INLINE fromMonomial #-}

  -- | Inject coefficient with monomial.
  toPolynomial' :: (Coefficient poly, Monomial (Arity poly)) -> poly
  toPolynomial' (r, deg) = Scalar r .* fromMonomial deg
  {-# INLINE toPolynomial' #-}

  -- | Construct polynomial from the given finite mapping from monomials to coefficients.
  polynomial' :: M.Map (Monomial (Arity poly)) (Coefficient poly) -> poly
  polynomial' dic =
    sum [ toPolynomial' (r, deg) | (deg, r) <- M.toList dic ]
  {-# INLINE polynomial' #-}

  -- | Returns total degree.
  totalDegree' :: poly -> Natural
  totalDegree' = maybe 0 fromIntegral . maximumOf folded . HS.map P.sum . monomials
  {-# INLINE totalDegree' #-}

  -- | @'var' n@ returns a polynomial representing n-th variable.
  var :: Ordinal (Arity poly) -> poly
  var nth = fromMonomial $ varMonom (sArity' (zero :: poly)) nth
  {-# INLINE var #-}

  -- | Adjusting coefficients of each term.
  mapCoeff' :: (Coefficient poly -> Coefficient poly) -> poly -> poly
  mapCoeff' f = polynomial' . fmap f . terms'

  -- | @m '>|*' f@ multiplies polynomial @f@ by monomial @m@.
  (>|*) :: Monomial (Arity poly) -> poly -> poly
  m >|* f = toPolynomial' (one, m) * f

  -- | Flipped version of @('>|*')@
  (*|<) :: poly -> Monomial (Arity poly) -> poly
  (*|<) = flip (>|*)

{-# RULES
"liftMap/identity"   liftMap (\ x -> x) = (P.id :: poly -> poly)
"liftMap/identity-2" liftMap P.id = (P.id :: poly -> poly)
  #-}

-- | Class to lookup ordering from its (type-level) name.
class (IsMonomialOrder (Arity poly) (MOrder poly), IsPolynomial poly) => IsOrderedPolynomial poly where
  type MOrder poly :: *
  {-# MINIMAL leadingTerm | (leadingMonomial , leadingCoeff) #-}

  -- | A variant of @'coeff''@ which takes @'OrderedMonomial'@ instead of @'Monomial'@
  coeff :: OrderedMonomial (MOrder poly) (Arity poly) -> poly -> Coefficient poly
  coeff m = coeff' (getMonomial m)
  {-# INLINE coeff #-}

  -- | The default implementation  is not enough efficient.
  -- So it is strongly recomended to give explicit
  -- definition to @'terms'@.
  terms :: poly -> M.Map (OrderedMonomial (MOrder poly) (Arity poly)) (Coefficient poly)
  terms = M.mapKeys OrderedMonomial . terms'

  -- | Leading term with respect to its monomial ordering.
  leadingTerm :: poly -> (Coefficient poly, OrderedMonomial (MOrder poly) (Arity poly))
  leadingTerm = (,) <$> leadingCoeff <*> leadingMonomial
  {-# INLINE leadingTerm #-}

  -- | Leading monomial with respect to its monomial ordering.
  leadingMonomial :: poly -> OrderedMonomial (MOrder poly) (Arity poly)
  leadingMonomial = snd . leadingTerm
  {-# INLINE leadingMonomial #-}

  -- | Leading coefficient with respect to its monomial ordering.
  leadingCoeff :: poly -> Coefficient poly
  leadingCoeff = fst . leadingTerm
  {-# INLINE leadingCoeff #-}

  -- | The collection of all monomials in the given polynomial,
  --   with metadata of their ordering.
  orderedMonomials :: poly -> S.Set (OrderedMonomial (MOrder poly) (Arity poly))
  orderedMonomials = S.fromList . P.map OrderedMonomial . HS.toList . monomials
  {-# INLINE orderedMonomials #-}

  -- | A variant of @'fromMonomial'@ which takes @'OrderedMonomial'@ as argument.
  fromOrderedMonomial :: OrderedMonomial (MOrder poly) (Arity poly) -> poly
  fromOrderedMonomial = fromMonomial . getMonomial
  {-# INLINE fromOrderedMonomial #-}

  -- | A variant of @'toPolynomial''@ which takes @'OrderedMonomial'@ as argument.
  toPolynomial :: (Coefficient poly, OrderedMonomial (MOrder poly) (Arity poly)) -> poly
  toPolynomial (r, deg) = toPolynomial' (r, getMonomial deg)
  {-# INLINE toPolynomial #-}

  -- | A variant of @'polynomial''@ which takes @'OrderedMonomial'@ as argument.
  --
  --   The default implementation combines @'Data.Map.mapKeys'@ and @'polynomial''@,
  --   hence is not enough efficient. So it is strongly recomended to give explicit
  -- definition to @'polynomial'@.
  polynomial :: M.Map (OrderedMonomial (MOrder poly) (Arity poly)) (Coefficient poly)
             -> poly
  polynomial dic = polynomial' $ M.mapKeys getMonomial dic
  {-# INLINE polynomial #-}

  -- | A variant of @'(>|*)'@ which takes @'OrderedMonomial'@ as argument.
  (>*) :: OrderedMonomial (MOrder poly) (Arity poly) -> poly -> poly
  m >* f = toPolynomial (one, m) * f
  {-# INLINE (>*) #-}

  -- | Flipped version of (>*)
  (*<) :: poly -> OrderedMonomial (MOrder poly) (Arity poly) -> poly
  (*<) = flip (>*)
  {-# INLINE (*<) #-}


-- | 1-norm of given polynomial, taking sum of @'norm'@s of each coefficients.
oneNorm :: (IsPolynomial poly, Normed (Coefficient poly),
            Monoidal (Norm (Coefficient poly))) => poly -> Norm (Coefficient poly)
oneNorm = sum . P.map norm . F.toList . terms'
{-# INLINE oneNorm #-}

-- | Maximum norm of given polynomial, taking maximum of the @'norm'@s of each coefficients.
maxNorm :: (IsPolynomial poly, Normed (Coefficient poly)) => poly -> Norm (Coefficient poly)
maxNorm = maximum . map norm . F.toList . terms'
{-# INLINE maxNorm #-}

-- | Make the given polynomial monic.
--   If the given polynomial is zero, it returns as it is.
monoize :: (Field (Coefficient poly), IsOrderedPolynomial poly)
        => poly -> poly
monoize f | isZero f  = zero
          | otherwise = recip (leadingCoeff f) .*. f
{-# INLINE monoize #-}

-- | @'sPolynomial'@ calculates the S-Polynomial of given two polynomials.
sPolynomial :: (IsOrderedPolynomial poly, Field (Coefficient poly))
            => poly
            -> poly -> poly
sPolynomial f g =
    let h = (one, lcmMonomial (leadingMonomial f) (leadingMonomial g))
    in toPolynomial (h `tryDiv` leadingTerm f) * f - toPolynomial (h `tryDiv` leadingTerm g) * g

-- | @pDivModPoly f g@ calculates the pseudo quotient and reminder of @f@ by @g@.
pDivModPoly :: (k ~ Coefficient poly, Euclidean k, IsOrderedPolynomial poly)
            => poly -> poly
            -> (poly, poly)
f0 `pDivModPoly` g =
  step (injectCoeff (pow (leadingCoeff g) (P.fromIntegral $ totalDegree' f0 P.- totalDegree' g + 1 :: Natural)) * f0) zero
  where
    lm = leadingMonomial g
    step p quo
        | isZero p = (quo, p)
        | lm `divs` leadingMonomial p =
            let q   = toPolynomial $ (leadingCoeff p `quot` leadingCoeff g, leadingMonomial p / leadingMonomial g)
            in step (p - (q * g)) (quo + q)
        | otherwise = (quo, p)

-- | The content of a polynomial f is the @'gcd'@ of all its coefficients.
content :: (IsPolynomial poly, Euclidean (Coefficient poly)) => poly -> Coefficient poly
content = foldr gcd zero . terms'
{-# INLINE content #-}

-- | @'pp' f@ calculates the primitive part of given polynomial @f@,
--   namely @f / content(f)@.
pp :: (Euclidean (Coefficient poly), IsPolynomial poly) => poly -> poly
pp f = mapCoeff' (`quot` content f) f
{-# INLINE pp #-}

injectVars :: ((Arity r :<= Arity r') ~ 'P.True,
               IsPolynomial r,
               IsPolynomial r',
               Coefficient r ~ Coefficient r') => r -> r'
injectVars = liftMap (var . inclusion)
{-# INLINE [1] injectVars #-}
{-# RULES "injectVars/identity" injectVars = P.id #-}

vars :: forall poly. IsPolynomial poly => [poly]
vars = map var $ enumOrdinal (sArity (Nothing :: Maybe poly))
