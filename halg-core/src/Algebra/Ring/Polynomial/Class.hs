{-# LANGUAGE ConstraintKinds, DataKinds, DefaultSignatures              #-}
{-# LANGUAGE ExplicitNamespaces, FlexibleContexts, FlexibleInstances    #-}
{-# LANGUAGE GADTs, LiberalTypeSynonyms, MultiParamTypeClasses          #-}
{-# LANGUAGE NoImplicitPrelude, ParallelListComp, PolyKinds, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, TypeOperators           #-}
{-# LANGUAGE UndecidableInstances                                       #-}
-- | This module provides abstract classes for finitary polynomial types.
module Algebra.Ring.Polynomial.Class
       ( IsPolynomial(..), IsOrderedPolynomial(..)
       , substCoeff, liftMapCoeff
       , CoeffRing, oneNorm, maxNorm, monoize,
         sPolynomial, pDivModPoly, content, pp,
         injectVars, vars,
         PrettyCoeff(..), ShowSCoeff(..),
         showsCoeffAsTerm, showsCoeffWithOp,
         showsPolynomialWith, showPolynomialWith,
         -- * Polynomial division
         divModPolynomial, divPolynomial, modPolynomial
         -- * Default instances
       , isUnitDefault, recipUnitDefault, isAssociateDefault
       , splitUnitDefault
       ) where
import Algebra.Internal
import Algebra.Normed
import Algebra.Ring.Polynomial.Monomial
import Algebra.Scalar

import           AlgebraicPrelude
import           Control.Arrow            ((***))
import           Control.Lens             (Iso', folded, ifoldMap, iso, ix,
                                           maximumOf, (%~), _Wrapped)
import           Data.Foldable            (foldr, maximum)
import qualified Data.Foldable            as F
import qualified Data.HashSet             as HS
import           Data.Int
import           Data.Kind                (Type)
import qualified Data.List                as L
import qualified Data.Map.Strict          as M
import           Data.Maybe               (catMaybes, fromJust, fromMaybe)
import qualified Data.Ratio               as R
import qualified Data.Set                 as S
import           Data.Singletons.Prelude  (SingKind (..))
import qualified Data.Sized.Builtin       as V
import           Data.Type.Ordinal        (Ordinal, enumOrdinal, inclusion)
import           Data.Word
import           GHC.TypeLits             (KnownNat, Nat)
import qualified Numeric.Algebra.Complex  as NA
import           Numeric.Decidable.Zero   (DecidableZero (..))
import           Numeric.Domain.Euclidean (Euclidean, quot)
import           Numeric.Domain.GCD       (gcd)
import           Numeric.Field.Fraction   (Fraction)
import qualified Numeric.Field.Fraction   as NA
import           Numeric.Natural          (Natural)
import qualified Numeric.Ring.Class       as NA
import qualified Prelude                  as P

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
  substWith o pt poly =
    runAdd $ ifoldMap ((Add .) . flip o . extractPower) $ terms' poly
    where
      extractPower = runMult . ifoldMap (\k -> Mult . pow (pt V.%!! k) . P.fromIntegral)
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
  totalDegree' :: poly -> Natural
  totalDegree' = maybe 0 fromIntegral . maximumOf folded . HS.map P.sum . monomials
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

liftMapCoeff :: IsPolynomial poly => (Ordinal (Arity poly) -> (Coefficient poly)) -> poly -> Coefficient poly
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

injectVars :: ((Arity r <= Arity r') ~ 'P.True,
               IsPolynomial r,
               IsPolynomial r',
               Coefficient r ~ Coefficient r') => r -> r'
injectVars = liftMap (var . inclusion)
{-# INLINE [1] injectVars #-}
{-# RULES "injectVars/identity" injectVars = P.id #-}

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

showPolynomialWith :: (IsPolynomial poly, PrettyCoeff (Coefficient poly))
                    => Sized (Arity poly) P.String
                    -> Int
                    -> poly
                    -> P.String
showPolynomialWith vs i p = showsPolynomialWith vs i p ""

showsPolynomialWith :: (IsPolynomial poly, PrettyCoeff (Coefficient poly))
                    => Sized (Arity poly) P.String
                    -> Int
                    -> poly
                    -> P.ShowS
showsPolynomialWith vsVec d f = P.showParen (d P.> 10) $
  let tms  = map (showMonom *** showsCoeff 10) $ M.toDescList $ terms' f
  in case tms of
    [] -> P.showString "0"
    (mc : ts) -> P.foldr1 (.) $
                 (showTermOnly mc) : map showRestTerm ts
  where
    showTermOnly (Nothing, Vanished) = P.id
    showTermOnly (Nothing, s)        = showsCoeffAsTerm s
    showTermOnly (Just m, OneCoeff)  = m
    showTermOnly (Just m, Negative Nothing) = P.showChar '-' . m
    showTermOnly (Just _, Vanished)  = P.id
    showTermOnly (Just m, t)         = showsCoeffAsTerm t . P.showChar ' ' . m
    showRestTerm (Nothing, Vanished) = P.id
    showRestTerm (Nothing, s)        = showsCoeffWithOp s
    showRestTerm (Just m, OneCoeff)  = P.showString " + " . m
    showRestTerm (Just m, Negative Nothing)  = P.showString " - " . m
    showRestTerm (Just _, Vanished)  = P.id
    showRestTerm (Just m, t)         = showsCoeffWithOp t . P.showChar ' ' . m
    vs = F.toList vsVec
    showMonom m =
      let fs = catMaybes $ P.zipWith showFactor vs $ F.toList m
      in if P.null fs
         then Nothing
         else Just $ foldr (.) P.id $ L.intersperse (P.showChar ' ') (map P.showString fs)
    showFactor _ 0 = Nothing
    showFactor v 1 = Just v
    showFactor v n = Just $ v P.++ "^" P.++ P.show n

-- | Calculate a polynomial quotient and remainder w.r.t. second argument.
divModPolynomial :: (IsOrderedPolynomial poly, Field (Coefficient poly))
                 => poly -> [poly]
                 -> ([(poly, poly)], poly)
divModPolynomial f0 fs = loop f0 zero (P.zip (L.nub fs) (P.repeat zero))
  where
    loop p r dic
        | isZero p = (dic, r)
        | otherwise =
            let ltP = toPolynomial $ leadingTerm p
            in case L.break ((`divs` leadingMonomial p) . leadingMonomial . fst) dic of
                 (_, []) -> loop (p - ltP) (r + ltP) dic
                 (xs, (g, old):ys) ->
                     let q = toPolynomial $ leadingTerm p `tryDiv` leadingTerm g
                         dic' = xs P.++ (g, old + q) : ys
                     in loop (p - (q * g)) r dic'
{-# INLINABLE divModPolynomial #-}

-- | Remainder of given polynomial w.r.t. the second argument.
modPolynomial :: (IsOrderedPolynomial poly, Field (Coefficient poly))
              => poly -> [poly] -> poly
modPolynomial = (snd .) . divModPolynomial

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
