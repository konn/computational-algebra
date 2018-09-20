{-# LANGUAGE BangPatterns, ConstraintKinds, DataKinds, ExplicitNamespaces  #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs                    #-}
{-# LANGUAGE LiberalTypeSynonyms, MultiParamTypeClasses, NoImplicitPrelude #-}
{-# LANGUAGE ParallelListComp, PolyKinds, RankNTypes, ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances             #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- | This module provides abstract classes for finitary polynomial types.
module Algebra.Ring.Polynomial.Class
       ( IsPolynomial(..), IsOrderedPolynomial(..)
       , Term, OMonom
       , substCoeff, liftMapCoeff
       , CoeffRing, oneNorm, maxNorm, monoize,
         sPolynomial, pDivModPoly, content, pp,
         injectVars, injectVarsAtEnd, injectVarsOffset, vars,
         PrettyCoeff(..), ShowSCoeff(..),
         showsCoeffAsTerm, showsCoeffWithOp,
         showsPolynomialWith, showsPolynomialWith',
         showPolynomialWith, showPolynomialWith',
         -- * Polynomial division
         divModPolynomial, divPolynomial, modPolynomial,
         -- * Conversion between polynomial types
         convertPolynomial, convertPolynomial', mapPolynomial,
         -- * Default instances
         isUnitDefault, recipUnitDefault, isAssociateDefault
       , splitUnitDefault
       ) where
import           Algebra.Internal
import           Algebra.Normed
import           Algebra.Ring.Polynomial.Monomial
import           Algebra.Scalar
import           AlgebraicPrelude
import           Control.Arrow                    ((***))
import           Control.Lens                     (Iso', folded, ifoldMap, iso,
                                                   ix, maximumOf, (%~),
                                                   _Wrapped)
import           Data.Foldable                    (foldr, maximum)
import qualified Data.Foldable                    as F
import qualified Data.HashSet                     as HS
import           Data.Int
import           Data.Kind                        (Type)
import qualified Data.List                        as L
import qualified Data.Map.Strict                  as M
import           Data.Maybe                       (catMaybes, fromJust,
                                                   fromMaybe)
import           Data.Monoid                      (First (..))
import           Data.MonoTraversable
import qualified Data.Ratio                       as R
import qualified Data.Set                         as S
import           Data.Singletons.Prelude          (SingKind (..))
import qualified Data.Sized.Builtin               as V
import           Data.Vector.Instances            ()
import           Data.Word
import           GHC.TypeLits                     (KnownNat, Nat)
import qualified Numeric.Algebra.Complex          as NA
import           Numeric.Decidable.Zero           (DecidableZero (..))
import           Numeric.Domain.Euclidean         (Euclidean, quot)
import           Numeric.Domain.GCD               (gcd)
import           Numeric.Field.Fraction           (Fraction)
import qualified Numeric.Field.Fraction           as NA
import           Numeric.Natural                  (Natural)
import qualified Numeric.Ring.Class               as NA
import qualified Prelude                          as P

infixl 7 *<, >*, *|<, >|*, !*

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
  type Coefficient poly :: Type
  -- | Arity of polynomial type.
  type Arity poly :: Nat

  -- | Universal mapping for free algebra.
  --   This corresponds to the algebraic substitution operation.
  liftMap :: (Module (Scalar (Coefficient poly)) alg, Ring alg, Commutative alg)
           => (Ordinal (Arity poly) -> alg) -> poly -> alg
  liftMap mor f =
    sum [ Scalar r .* sum [ Scalar (fromInteger' (P.fromIntegral i) :: Coefficient poly) .* mor o
                          | i <- otoList (m :: Monomial (Arity poly)) :: [Int]
                          | o <- enumOrdinal (sArity (Nothing :: Maybe poly)) ]
        | (m, r) <- M.toList (terms' f) ]
  {-# INLINE liftMap #-}

  -- | A variant of @'liftMap'@, each value is given by @'Sized'@.
  subst :: (Ring alg, Commutative alg, Module (Scalar (Coefficient poly)) alg)
        => Sized (Arity poly) alg -> poly -> alg
  subst dic = liftMap (dic V.%!!)
  {-# INLINE subst #-}

  -- | Another variant of @'liftMap'@.
  --   This function relies on @'terms''@; if you have more efficient implementation,
  --   it is encouraged to override this method.
  --
  --   Since 0.6.0.0
  substWith :: forall m. (Ring m)
            => (Coefficient poly -> m -> m) -> Sized (Arity poly) m -> poly -> m
  substWith o pt poly =
    runAdd $ ifoldMap ((Add .) . flip o . extractPower) $ terms' poly
    where
      extractPower :: Monomial (Arity poly) -> m
      extractPower = runMult . ifoldMapMonom (\k n -> Mult (pow (pt V.%!! k) (P.fromIntegral n)))
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
  arity _pxy = fromIntegral $ fromSing $ sArity' (zero :: poly)
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
  coeff' m = M.findWithDefault zero m . terms'
  {-# INLINE coeff' #-}

  -- | Calculates constant coefficient.
  constantTerm :: poly -> Coefficient poly
  constantTerm = runScalar . liftMap (\ _ -> Scalar zero)
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
  totalDegree' :: poly -> Int
  totalDegree' = fromMaybe 0 . maximumOf folded . HS.map osum . monomials
  {-# INLINE totalDegree' #-}

  -- | @'var' n@ returns a polynomial representing n-th variable.
  var :: Ordinal (Arity poly) -> poly
  var nth = fromMonomial $ varMonom (sArity' (zero :: poly)) nth

  -- | Adjusting coefficients of each term.
  mapCoeff' :: (Coefficient poly -> Coefficient poly) -> poly -> poly
  mapCoeff' f = polynomial' . fmap f . terms'

  -- | @m '>|*' f@ multiplies polynomial @f@ by monomial @m@.
  (>|*) :: Monomial (Arity poly) -> poly -> poly
  m >|* f = toPolynomial' (one, m) * f

  -- | Flipped version of @('>|*')@
  (*|<) :: poly -> Monomial (Arity poly) -> poly
  (*|<) = flip (>|*)

  (!*) :: Coefficient poly -> poly -> poly
  (!*) = (.*.)


  _Terms' :: Iso' poly (Map (Monomial (Arity poly)) (Coefficient poly))
  _Terms' = iso terms' polynomial'
  {-# INLINE _Terms' #-}

  mapMonomial :: (Monomial (Arity poly) -> Monomial (Arity poly)) -> poly -> poly
  mapMonomial tr  =
    _Terms' %~ M.mapKeysWith (+) tr
  {-# INLINE mapMonomial #-}

-- | Class to lookup ordering from its (type-level) name.
class (IsMonomialOrder (Arity poly) (MOrder poly), IsPolynomial poly) => IsOrderedPolynomial poly where
  type MOrder poly :: Type
  {-# MINIMAL leadingTerm | (leadingMonomial , leadingCoeff) #-}

  -- | A variant of @'coeff''@ which takes @'OrderedMonomial'@ instead of @'Monomial'@
  coeff :: OrderedMonomial (MOrder poly) (Arity poly) -> poly -> Coefficient poly
  coeff m = coeff' (getMonomial m)
  {-# INLINE coeff #-}

  -- | The default implementation  is not enough efficient.
  --   So it is strongly recomended to give explicit
  --   definition to @'terms'@.
  terms :: poly -> M.Map (OrderedMonomial (MOrder poly) (Arity poly)) (Coefficient poly)
  terms = defaultTerms

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

  -- | Splitting leading term, returning a pair of the leading term and the new polynomial
  --   with the leading term subtracted.
  splitLeadingTerm :: poly -> (Term poly, poly)
  splitLeadingTerm p =
    let t = leadingTerm p
    in (t, p - toPolynomial t)
  {-# INLINE splitLeadingTerm #-}

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
  (>*) m = mapMonomialMonotonic (m *)
  {-# INLINE (>*) #-}

  -- | Flipped version of (>*)
  (*<) :: poly -> OrderedMonomial (MOrder poly) (Arity poly) -> poly
  (*<) = flip (>*)
  {-# INLINE (*<) #-}

  _Terms :: Iso' poly (Map (OrderedMonomial (MOrder poly) (Arity poly)) (Coefficient poly))
  _Terms = iso terms polynomial
  {-# INLINE _Terms #-}

  -- | @diff n f@ partially diffrenciates @n@-th variable in the given polynomial @f@.
  --   The default implementation uses @'terms'@ and @'polynomial'@
  --   and is really naive; please consider overrideing for efficiency.
  diff :: Ordinal (Arity poly) -> poly -> poly
  diff n = _Terms %~ M.mapKeysWith (+) (_Wrapped.ix n %~ max 0 . pred)
                   . M.mapMaybeWithKey df
    where
      df m v =
        let p  = getMonomial m V.%!! n
            v' = NA.fromIntegral p * v
        in if p == 0 || isZero v'
           then Nothing
           else Just v'
  {-# INLINE diff #-}

  -- | Same as @'mapMonomial'@, but maping function is
  --   assumed to be strictly monotonic (i.e. @a < b@ implies @f a < f b@).
  mapMonomialMonotonic
    :: (OrderedMonomial (MOrder poly) (Arity poly) -> OrderedMonomial (MOrder poly) (Arity poly))
    -> poly -> poly
  mapMonomialMonotonic tr  =
    _Terms %~ M.mapKeysMonotonic tr
  {-# INLINE mapMonomialMonotonic #-}


type OMonom poly = OrderedMonomial (MOrder poly) (Arity poly)
type Term poly = (Coefficient poly, OMonom poly)

defaultTerms :: IsOrderedPolynomial poly
             => poly -> Map (OrderedMonomial (MOrder poly) (Arity poly)) (Coefficient poly)
defaultTerms = M.mapKeys OrderedMonomial . terms'
{-# NOINLINE [1] defaultTerms #-}

{-# RULES
 "polynomial/terms" forall (f :: IsOrderedPolynomial poly => poly).
   polynomial (defaultTerms f) = f
 #-}

liftMapCoeff :: IsPolynomial poly => (Ordinal (Arity poly) -> Coefficient poly) -> poly -> Coefficient poly
liftMapCoeff l = runScalar . liftMap (Scalar . l)
{-# INLINE liftMapCoeff #-}

substCoeff :: IsPolynomial poly => Sized (Arity poly) (Coefficient poly) -> poly -> Coefficient poly
substCoeff l = runScalar . subst (fmap Scalar l)
{-# INLINE substCoeff #-}

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
  let k = fromIntegral $ totalDegree' f0 :: Integer
      l = fromIntegral $ totalDegree' g  :: Integer
  in step (injectCoeff (pow (leadingCoeff g) (P.fromInteger (max 0 $ 1 + k - l) :: Natural)) * f0) zero
  where
    lm = leadingMonomial g
    step p quo
        | isZero p = (quo, p)
        | lm `divs` leadingMonomial p =
            let coe = leadingCoeff p `quot` leadingCoeff g
                mon = leadingMonomial p / leadingMonomial g
                q   = toPolynomial (coe, mon)
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

-- | See also @'injectVarsOffset'@ and @'injectVarsAtEnd'@.
injectVars :: ((Arity r <= Arity r') ~ 'P.True,
               IsPolynomial r,
               IsPolynomial r',
               Coefficient r ~ Coefficient r') => r -> r'
injectVars = liftMap (var . inclusion)
{-# INLINE [1] injectVars #-}
{-# RULES "injectVars/identity" injectVars = P.id #-}

-- | Similar to @'injectVars'@, but injects variables at the end of
--   the target polynomial ring.
--
--   See also @'injectVars'@ and @'injectVarsOffset'@.
injectVarsAtEnd :: forall r r'. ((Arity r <= Arity r') ~ 'P.True,
                    IsPolynomial r,
                    IsPolynomial r',
                    Coefficient r ~ Coefficient r') => r -> r'
injectVarsAtEnd =
  let sn = sArity (Nothing :: Maybe r)
      sm = sArity (Nothing :: Maybe r')
  in withRefl (minusPlus sm sn Witness) $ injectVarsOffset (sm %- sn)
{-# INLINE injectVarsAtEnd #-}

shift :: forall n m k. ((n + m <= k) ~ 'True , KnownNat m, KnownNat k) => Sing n -> Ordinal m -> Ordinal k
shift sn (OLt (sl :: Sing l)) =
  let sm = sing :: Sing m
      sk = sing :: Sing k
  in withRefl (lneqToLT sl sm Witness) $
     withWitness (lneqMonotoneR sn sl sm Witness) $
     withWitness (lneqLeqTrans (sn %+ sl) (sn %+ sm) sk Witness Witness) $
     OLt (sn %+ sl)
shift _ _ = error "Could not happen!"
{-# INLINE [1] shift #-}
{-# RULES
"shift/zero" forall (ns :: Sing 0).
  shift ns = inclusion
  #-}

lneqLeqTrans :: Sing (n :: Nat) -> Sing m -> Sing l
             -> IsTrue (n < m) -> IsTrue (m <= l) -> IsTrue (n < l)
lneqLeqTrans sn sm sl nLTm mLEl =
  withRefl (lneqSuccLeq sn sl) $
  withRefl (lneqSuccLeq sn sm) $
  leqTrans (sSucc sn) sm sl nLTm mLEl

lneqMonotoneR :: forall n m l. Sing (n :: Nat) -> Sing m -> Sing l
              -> IsTrue (m < l) -> IsTrue ((n + m) < (n + l))
lneqMonotoneR sn sm sl mLTl =
  withRefl (lneqSuccLeq sm sl) $
  withRefl (lneqSuccLeq (sn %+ sm) (sn %+ sl)) $
  withRefl (plusSuccR sn sm) $
  plusMonotoneR sn (sSucc sm) sl (mLTl :: IsTrue ((m + 1) <= l))

-- | Similar to @'injectVars'@, but @'injectVarsOffset' n f@
--   injects variables into the first but @n@ variables.
--
--   See also @'injectVars'@ and @'injectVarsAtEnd'@.
injectVarsOffset :: forall n r r' . ((n + Arity r <= Arity r') ~ 'P.True,
                  IsPolynomial r,
                  IsPolynomial r',
                  Coefficient r ~ Coefficient r') => Sing n -> r -> r'
injectVarsOffset sn = liftMap (var . shift sn)
{-# INLINE [1] injectVarsOffset #-}
{-# RULES
"injectVarsOffset eql" forall (sn :: Sing 0).
 injectVarsOffset sn = injectVars
 #-}

vars :: forall poly. IsPolynomial poly => [poly]
vars = map var $ enumOrdinal (sArity (Nothing :: Maybe poly))

-- | Coefficients which admits pretty-printing
class (P.Show r) => PrettyCoeff r where
  showsCoeff :: Int -> r -> ShowSCoeff
  showsCoeff d a = Positive (P.showsPrec d a)

defaultShowsOrdCoeff :: (P.Show r, Unital r, Group r, P.Ord r)
                     => Int -> r -> ShowSCoeff
defaultShowsOrdCoeff d r
  | r P.== negate one = Negative Nothing
  | r P.<  zero = Negative (Just $ P.showsPrec d (negate r))
  | r P.== zero = Vanished
  | r P.== one  = OneCoeff
  | otherwise   = Positive (P.showsPrec d r)

instance PrettyCoeff P.Integer where
  showsCoeff = defaultShowsOrdCoeff

instance PrettyCoeff Natural where
  showsCoeff d r
    | r == 0    = Vanished
    | otherwise = Positive (P.showsPrec d r)

instance PrettyCoeff P.Int where
  showsCoeff = defaultShowsOrdCoeff

instance PrettyCoeff Int64 where
  showsCoeff = defaultShowsOrdCoeff
instance PrettyCoeff Int16 where
  showsCoeff = defaultShowsOrdCoeff
instance PrettyCoeff Int32 where
  showsCoeff = defaultShowsOrdCoeff
instance PrettyCoeff Int8 where
  showsCoeff = defaultShowsOrdCoeff

instance PrettyCoeff Word64 where
  showsCoeff = defaultShowsOrdCoeff

instance PrettyCoeff Word16 where
  showsCoeff = defaultShowsOrdCoeff

instance PrettyCoeff Word32 where
  showsCoeff = defaultShowsOrdCoeff

instance PrettyCoeff Word8 where
  showsCoeff = defaultShowsOrdCoeff

instance (P.Integral a, PrettyCoeff a) => PrettyCoeff (R.Ratio a) where
  showsCoeff d r =
    if R.denominator r == 1
    then showsCoeff 10 (R.numerator r)
    else defaultShowsOrdCoeff d r

instance (PrettyCoeff r) => PrettyCoeff (NA.Complex r) where
  showsCoeff d (NA.Complex r i) =
    case (showsCoeff 10 r, showsCoeff 10 i) of
      (Vanished, Vanished)     -> Vanished
      (Vanished, Positive s)   -> Positive (s . P.showString " I")
      (Vanished, Negative s)   -> Negative (Just $ fromMaybe P.id s . P.showString " I")
      (Positive s, Vanished)   -> Positive s
      (Negative s, Vanished)   -> Negative s
      (s, t) ->
        Positive $ P.showParen (d P.> 10) $
        showsCoeffAsTerm s . showsCoeffWithOp t

instance {-# OVERLAPPING #-} PrettyCoeff (Fraction P.Integer) where
  showsCoeff d r =
      if NA.denominator r == one
      then showsCoeff d (NA.numerator r)
      else defaultShowsOrdCoeff d r

instance {-# OVERLAPS #-}
  (PrettyCoeff r, Eq r, Euclidean r) => PrettyCoeff (Fraction r) where
    showsCoeff d r =
      if NA.denominator r == one
      then showsCoeff d (NA.numerator r)
      else Positive (P.showsPrec d r)

-- | Pretty-printing conditional for coefficients.
--   Each returning @'P.ShowS'@ must not have any sign.
data ShowSCoeff = Negative (Maybe P.ShowS)
                | Vanished
                | OneCoeff
                | Positive P.ShowS

-- | ShowS coefficients as term.
--
-- @
-- showsCoeffAsTerm 'Vanished' "" = ""
-- showsCoeffAsTerm ('Negative' (shows "12")) "" = "-12"
-- showsCoeffAsTerm ('Positive' (shows "12")) "" = "12"
-- @
showsCoeffAsTerm :: ShowSCoeff -> P.ShowS
showsCoeffAsTerm Vanished     = P.id
showsCoeffAsTerm (Negative s) = P.showChar '-' . fromMaybe (P.showChar '1') s
showsCoeffAsTerm OneCoeff     = P.showChar '1'
showsCoeffAsTerm (Positive s) = s

-- | ShowS coefficients prefixed with infix operator.
--
-- @
-- (shows 12 . showsCoeffWithOp 'Vanished') "" = "12"
-- (shows 12 . showsCoeffWithOp ('Negative' (shows 34))) "" = "12 - 34"
-- (shows 12 . showsCoeffWithOp ('Positive' (shows 34))) "" = "12 + 34"
-- @
showsCoeffWithOp :: ShowSCoeff -> P.ShowS
showsCoeffWithOp Vanished = P.id
showsCoeffWithOp (Negative s) = P.showString " - " . fromMaybe (P.showChar '1') s
showsCoeffWithOp OneCoeff     = P.showString " + 1"
showsCoeffWithOp (Positive s) = P.showString " + " . s

showPolynomialWith :: (IsOrderedPolynomial poly, PrettyCoeff (Coefficient poly))
                    => Sized (Arity poly) P.String
                    -> Int
                    -> poly
                    -> P.String
showPolynomialWith vs i p = showsPolynomialWith vs i p ""

showPolynomialWith' :: (IsOrderedPolynomial poly)
                     => Bool
                     -> (Int -> Coefficient poly -> ShowSCoeff)
                     -> Sized (Arity poly) P.String
                     -> Int
                     -> poly
                     -> P.String
showPolynomialWith' b showsCoe vs i p = showsPolynomialWith' b showsCoe vs i p ""

showsPolynomialWith :: (IsOrderedPolynomial poly, PrettyCoeff (Coefficient poly))
                     => Sized (Arity poly) P.String
                     -> Int
                     -> poly
                     -> P.ShowS
showsPolynomialWith = showsPolynomialWith' True showsCoeff

showsPolynomialWith' :: (IsOrderedPolynomial poly)
                     => Bool
                        -- ^ Whether print multiplication as @*@ or not.
                     -> (Int -> Coefficient poly -> ShowSCoeff)
                        -- ^ Coefficient printer
                     -> Sized (Arity poly) P.String
                        -- ^ Variables
                     -> Int
                        -- ^ Precision
                     -> poly
                        -- ^ Polynomial
                     -> P.ShowS
showsPolynomialWith' showMult showsCoe vsVec d f = P.showParen (d P.> 10) $
  let tms  = map (showMonom *** showsCoe 10) $ M.toDescList $ terms f
  in case tms of
    [] -> P.showString "0"
    (mc : ts) -> P.foldr1 (.) $ showTermOnly mc : map showRestTerm ts
  where
    showTermOnly (Nothing, Vanished) = P.id
    showTermOnly (Nothing, s)        = showsCoeffAsTerm s
    showTermOnly (Just m, OneCoeff)  = m
    showTermOnly (Just m, Negative Nothing) = P.showChar '-' . m
    showTermOnly (Just _, Vanished)  = P.id
    showTermOnly (Just m, t)         = showsCoeffAsTerm t . P.showChar multSymb . m
    showRestTerm (Nothing, Vanished) = P.id
    showRestTerm (Nothing, s)        = showsCoeffWithOp s
    showRestTerm (Just m, OneCoeff)  = P.showString " + " . m
    showRestTerm (Just m, Negative Nothing)  = P.showString " - " . m
    showRestTerm (Just _, Vanished)  = P.id
    showRestTerm (Just m, t)         = showsCoeffWithOp t . P.showChar multSymb . m
    vs = F.toList vsVec
    multSymb | showMult  = '*'
             | otherwise = ' '
    showMonom m =
      let fs = catMaybes $ P.zipWith showFactor vs $ otoList $ getMonomial m
      in if P.null fs
         then Nothing
         else Just $ foldr (.) P.id $ L.intersperse (P.showChar multSymb) (map P.showString fs)
    showFactor _ 0 = Nothing
    showFactor v 1 = Just v
    showFactor v n = Just $ v P.++ "^" P.++ P.show n

-- | Calculate a polynomial quotient and remainder w.r.t. second argument.
divModPolynomial :: forall poly. (IsOrderedPolynomial poly, Field (Coefficient poly))
                 => poly -> [poly]
                 -> ([(poly, poly)], poly)
divModPolynomial f0 fs = loop f0 zero (P.zip (map splitLeadingTerm $ L.nub fs) (P.repeat zero))
  where
    loop p r dic
        | isZero p = (map (first $ \(lt, q) -> toPolynomial lt + q) dic, r)
        | otherwise =
            let (ltP, p') = splitLeadingTerm p
            in case L.break ((`divs` snd ltP) . snd . fst . fst) dic of
                 (_, []) -> loop p' (r + toPolynomial ltP) dic
                 (xs, ((ltG, g), old):ys) ->
                     let q = toPolynomial $ ltP `tryDiv` ltG
                         dic' = xs P.++ ((ltG, g), old + q) : ys
                     in loop (p' - (q * g)) r dic'
{-# INLINABLE [2] divModPolynomial #-}

-- | Remainder of given polynomial w.r.t. the second argument.
modPolynomial :: (IsOrderedPolynomial poly, Field (Coefficient poly), Functor t, Foldable t)
              => poly -> t poly -> poly
modPolynomial p rs0 = loop p zero
  where
    rs = map splitLeadingTerm rs0
    step r (ltQ, q) =  do
      let (ltR, r') = splitLeadingTerm r
          lt  = ltR `tryDiv` ltQ
      guard $ not (isZero r || isZero (fst ltQ)) && snd ltQ `divs` snd ltR
      return $ r' - toPolynomial lt * q
    loop !q !r
      | isZero q = r
      | otherwise =
          case getFirst $ foldMap (First . step q) rs of
            Just q' -> loop q' r
            Nothing ->
              let (lt, q') = splitLeadingTerm q
              in loop q' (r + toPolynomial lt)
{-# SPECIALISE
 modPolynomial :: (IsOrderedPolynomial poly, Field (Coefficient poly))
                => poly -> [poly] -> poly
 #-}

{-# RULES
"snd . divModPolynomial"
  (snd .) . divModPolynomial = modPolynomial
"snd . divModPolynomial p" forall p.
  snd . divModPolynomial p = modPolynomial p
"snd (divModPolynomial p qs)" forall p qs.
  snd (divModPolynomial p qs) = modPolynomial p qs
 #-}

-- | A Quotient of given polynomial w.r.t. the second argument.
divPolynomial :: (IsOrderedPolynomial poly, Field (Coefficient poly))
              => poly -> [poly] -> [(poly, poly)]
divPolynomial = (fst .) . divModPolynomial

infixl 7 `divPolynomial`
infixl 7 `modPolynomial`
infixl 7 `divModPolynomial`

isUnitDefault :: (DecidableUnits r, Coefficient poly ~ r, IsPolynomial poly)
              => poly -> Bool
isUnitDefault p = totalDegree' p == 0 && isUnit (constantTerm p)

recipUnitDefault :: (DecidableUnits r, Coefficient poly ~ r, IsPolynomial poly)
                 => poly -> Maybe poly
recipUnitDefault p
  | isUnitDefault p = fmap injectCoeff $ recipUnit $ constantTerm p
  | otherwise = Nothing

isAssociateDefault :: (UnitNormalForm r, Coefficient poly ~ r, IsOrderedPolynomial poly)
                 => poly -> poly -> Bool
isAssociateDefault p q =
  let up = fromJust $ recipUnit $ leadingUnit $ fst $ leadingTerm p
      uq = fromJust $ recipUnit $ leadingUnit $ fst $ leadingTerm q
  in (up !* q) == (uq !* p)

splitUnitDefault :: (UnitNormalForm r, Coefficient poly ~ r, IsOrderedPolynomial poly)
                 => poly -> (poly, poly)
splitUnitDefault f =
  let u = leadingUnit $ leadingCoeff f
      u' = fromJust $ recipUnit u
  in (injectCoeff u, u' !* f)


-- | Conversion between polynomials with the same monomial orderings,
--   coefficents and variables.
convertPolynomial :: ( IsOrderedPolynomial poly, IsOrderedPolynomial poly'
                     , Coefficient poly ~ Coefficient poly'
                     , MOrder poly ~ MOrder poly', Arity poly ~ Arity poly'
                     )
                  => poly -> poly'
convertPolynomial = polynomial . terms
{-# INLINE [3] convertPolynomial #-}
{-# RULES
"convertPolynomial id" [~3] convertPolynomial = id
  #-}

-- | Conversion between polynomials with the same monomial coefficents and variables.
convertPolynomial' :: ( IsOrderedPolynomial poly, IsOrderedPolynomial poly'
                      , Coefficient poly ~ Coefficient poly'
                      , Arity poly ~ Arity poly'
                      )
                   => poly -> poly'
convertPolynomial' = polynomial' . terms'
{-# INLINE [3] convertPolynomial' #-}
{-# RULES
"convertPolynomial' id" [~3] convertPolynomial' = id
  #-}

mapPolynomial :: (IsOrderedPolynomial poly, IsOrderedPolynomial poly')
              => (Coefficient poly -> Coefficient poly') -> (Ordinal (Arity poly) -> Ordinal (Arity poly'))
              -> poly -> poly'
mapPolynomial mapCoe injVar =
  substWith (\coe g -> mapCoe coe !* g) (generate sing (var . injVar))
{-# INLINE [3] mapPolynomial #-}
{-# RULES
"mapPolynomial/id" mapPolynomial id id = id
 #-}
