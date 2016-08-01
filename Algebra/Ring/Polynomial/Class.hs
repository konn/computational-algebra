{-# LANGUAGE DataKinds, DefaultSignatures, ExplicitNamespaces              #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs                    #-}
{-# LANGUAGE LiberalTypeSynonyms, MultiParamTypeClasses, NoImplicitPrelude #-}
{-# LANGUAGE ParallelListComp, PolyKinds, RankNTypes, ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies, UndecidableInstances                            #-}
module Algebra.Ring.Polynomial.Class ( IsPolynomial(..), IsOrderedPolynomial(..)
                                     , CoeffRing
                                     ) where
import Algebra.Ring.Polynomial.Monomial
import Algebra.Scalar
import Algebra.Wrapped

import           Control.Applicative
import           Control.Arrow          (first)
import           Control.Lens
import qualified Data.HashMap.Strict    as HM
import qualified Data.HashSet           as HS
import qualified Data.Map.Strict        as M
import qualified Data.Set               as S
import           Data.Type.Natural      (Nat, SNat, sNatToInt)
import           Data.Type.Ordinal
import           Data.Vector.Sized      hiding (foldr, sum)
import qualified Data.Vector.Sized      as V
import           Numeric.Algebra
import           Numeric.Decidable.Zero
import           Prelude                hiding (Num (..), product, sum)
import qualified Prelude                as P

infixl 7 *<, >*, *|<, >|*

-- | Constraint synonym for rings that can be used as polynomial coefficient.
class    (DecidableZero r, Ring r, Commutative r, Eq r) => CoeffRing r
instance (DecidableZero r, Ring r, Commutative r, Eq r) => CoeffRing r

-- | Polynomial in terms of free associative commutative algebra generated
--   by n-elements.
--   To effectively compute all terms, we need @'monomials'@ in addition to
--   universality of free object.
class (CoeffRing (Coefficient poly),
       Module (Scalar (Coefficient poly)) poly, Ring poly, Commutative poly)
   => IsPolynomial poly where
  {-# MINIMAL ((liftMap , monomials) | terms'), (sArity | sArity') , (fromMonomial | toPolynomial' | polynomial') #-}
  type Coefficient poly :: *
  type Arity poly :: Nat

  -- | Universal mapping for free algebra.
  --   This corresponds to the algebraic substitution operation.
  liftMap :: (Module (Scalar (Coefficient poly)) alg, Ring alg, Commutative alg)
           => (Ordinal (Arity poly) -> alg) -> poly -> alg
  liftMap mor f =
    sum [ Scalar r .* sum [ Scalar (fromInteger (fromIntegral i) :: Coefficient poly) .* mor o
                          | i <- toList (m :: Monomial (Arity poly)) :: [Int]
                          | o <- enumOrdinal (sArity (Nothing :: Maybe poly)) ]
        | (m, r) <- HM.toList (terms' f) ]
  {-# INLINE liftMap #-}

  sArity' :: poly -> SNat (Arity poly)
  sArity' = sArity . Just

  subst :: (Ring alg, Commutative alg, Module (Scalar (Coefficient poly)) alg)
        => Vector alg (Arity poly) -> poly -> alg
  subst dic f = liftMap (dic V.%!!) f
  {-# INLINE subst #-}

  substWith :: (Unital r, Monoidal m)
            => (Coefficient poly -> r -> m) -> V.Vector r (Arity poly) -> poly -> m
  substWith o pt poly = sum $ P.map (uncurry (flip o) . first extractPower) $ HM.toList $ terms' poly
    where
      extractPower = V.foldr (*) one . V.zipWithSame pow pt .
                     V.map (P.fromIntegral :: Int -> Natural)
  {-# INLINE substWith #-}

  -- | @'monomials' f@ returns the finite set of all monomials appearing in @f@.
  monomials :: poly -> HS.HashSet (Monomial (Arity poly))
  monomials = HS.fromList . HM.keys . terms'
  {-# INLINE monomials #-}

  terms' :: poly -> HM.HashMap (Monomial (Arity poly)) (Coefficient poly)
  terms' f = HM.fromList [ (m, c)
                        | m <- HS.toList $ monomials f
                        , let c = coeff' m f
                        , not (isZero c)
                        ]
  {-# INLINE terms' #-}

  coeff' :: Monomial (Arity poly) -> poly -> Coefficient poly
  coeff' m = runCoeff . liftMap (\i -> WrapCoeff $ fromInteger $ fromIntegral $ m %!! i)
  {-# INLINE coeff' #-}

  constantTerm :: poly -> Coefficient poly
  constantTerm = runCoeff . liftMap (\ _ -> WrapCoeff zero)
  {-# INLINE constantTerm #-}

  sArity :: proxy poly -> SNat (Arity poly)
  sArity _ = sArity' (zero :: poly)
  {-# INLINE sArity #-}

  arity :: proxy poly -> Natural
  arity _pxy = sNatToInt (sArity' (zero :: poly))
  {-# INLINE arity #-}

  fromMonomial :: Monomial (Arity poly) -> poly
  fromMonomial m = toPolynomial' (one , m)
  {-# INLINE fromMonomial #-}

  toPolynomial' :: (Coefficient poly, Monomial (Arity poly)) -> poly
  toPolynomial' (r, deg) = Scalar r .* fromMonomial deg
  {-# INLINE toPolynomial' #-}

  polynomial' :: M.Map (Monomial (Arity poly)) (Coefficient poly) -> poly
  polynomial' dic =
    sum [ toPolynomial' (r, deg) | (deg, r) <- M.toList dic ]
  {-# INLINE polynomial' #-}

  totalDegree' :: poly -> Natural
  totalDegree' = maybe 0 fromIntegral . maximumOf folded . HS.map V.sum . monomials
  {-# INLINE totalDegree' #-}

  var :: Ordinal (Arity poly) -> poly
  var nth = fromMonomial $ varMonom (sArity' (zero :: poly)) nth
  {-# INLINE var #-}

  (>|*) :: Monomial (Arity poly) -> poly -> poly
  m >|* f = toPolynomial' (one, m) * f

  (*|<) :: poly -> Monomial (Arity poly) -> poly
  (*|<) = flip (>|*)

-- | Class to lookup ordering from its (type-level) name.
class (IsMonomialOrder (MOrder poly), IsPolynomial poly) => IsOrderedPolynomial poly where
  type MOrder poly :: *
  {-# MINIMAL leadingTerm | (leadingMonomial , leadingCoeff) #-}

  coeff :: OrderedMonomial (MOrder poly) (Arity poly) -> poly -> Coefficient poly
  coeff m = coeff' (getMonomial m)
  {-# INLINE coeff #-}

  -- | The default implementation  is not enough efficient.
  -- So it is strongly recomended to give explicit
  -- definition to @'terms'@.
  terms :: poly -> M.Map (OrderedMonomial (MOrder poly) (Arity poly)) (Coefficient poly)
  terms = M.fromList . P.map (first OrderedMonomial)  . HM.toList . terms'

  leadingTerm :: poly -> (Coefficient poly, OrderedMonomial (MOrder poly) (Arity poly))
  leadingTerm = (,) <$> leadingCoeff <*> leadingMonomial
  {-# INLINE leadingTerm #-}

  leadingMonomial :: poly -> OrderedMonomial (MOrder poly) (Arity poly)
  leadingMonomial = snd . leadingTerm
  {-# INLINE leadingMonomial #-}

  leadingCoeff :: poly -> Coefficient poly
  leadingCoeff = fst . leadingTerm
  {-# INLINE leadingCoeff #-}

  orderedMonomials :: poly -> S.Set (OrderedMonomial (MOrder poly) (Arity poly))
  orderedMonomials = S.fromList . P.map OrderedMonomial . HS.toList . monomials
  {-# INLINE orderedMonomials #-}


  fromOrderedMonomial :: OrderedMonomial (MOrder poly) (Arity poly) -> poly
  fromOrderedMonomial = fromMonomial . getMonomial
  {-# INLINE fromOrderedMonomial #-}

  toPolynomial :: (Coefficient poly, OrderedMonomial (MOrder poly) (Arity poly)) -> poly
  toPolynomial (r, deg) = toPolynomial' (r, getMonomial deg)
  {-# INLINE toPolynomial #-}

  -- | The default implementation combines @'Data.Map.mapKeys'@ and @'polynomial''@,
  --   hence is not enough efficient. So it is strongly recomended to give explicit
  -- definition to @'polynomial'@.
  polynomial :: M.Map (OrderedMonomial (MOrder poly) (Arity poly)) (Coefficient poly)
             -> poly
  polynomial dic = polynomial' $ M.mapKeys getMonomial dic
  {-# INLINE polynomial #-}

  (>*) :: OrderedMonomial (MOrder poly) (Arity poly) -> poly -> poly
  m >* f = toPolynomial (one, m) * f
  {-# INLINE (>*) #-}


  (*<) :: poly -> OrderedMonomial (MOrder poly) (Arity poly) -> poly
  (*<) = flip (>*)
  {-# INLINE (*<) #-}

