{-# LANGUAGE DataKinds, ExplicitNamespaces, FlexibleContexts, GADTs        #-}
{-# LANGUAGE LiberalTypeSynonyms, MultiParamTypeClasses, NoImplicitPrelude #-}
{-# LANGUAGE ParallelListComp, PolyKinds, RankNTypes, ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies                                                  #-}
module Algebra.Ring.Polynomial.Class ( IsPolynomial(..), IsOrderedPolynomial(..)
                                     , Monomial, OrderedMonomial(..)
                                     , IsOrder(..), IsMonomialOrder, MonomialOrder
                                     ) where
import           Algebra.Ring.Polynomial (Monomial)
import           Algebra.Scalar
import           Algebra.Wrapped
import           Control.Applicative
import           Control.Lens
import qualified Data.HashMap.Strict     as HM
import qualified Data.HashSet            as HS
import qualified Data.Map.Strict         as M
import           Data.Proxy
import           Data.Singletons.Prelude (SingI (..))
import           Data.Type.Natural       (Nat, SNat, sNatToInt)
import           Data.Type.Ordinal
import           Data.Vector.Sized       hiding (foldr, sum)
import qualified Data.Vector.Sized       as V
import           Numeric.Algebra
import           Numeric.Decidable.Zero
import           Prelude                 hiding (Num (..), product, sum)

-- | Polynomial in terms of free associative commutative algebra generated
--   by n-elements.
--   To effectively compute all terms, we need @'monomials'@ in addition to
--   universality of free object.
class (DecidableZero (Coefficient poly), SingI (Arity poly),
       Module (Scalar (Coefficient poly)) poly, Ring (Coefficient poly),
       Commutative (Coefficient poly), Ring poly, Commutative poly)
   => IsPolynomial poly where
  {-# MINIMAL ((liftMap , monomials) | terms) , (fromMonomial | toPolynomial' | polynomial') #-}
  type Coefficient poly :: *
  type Arity poly :: Nat

  -- | Universal mapping for free algebra.
  --   This corresponds to the algebraic substitution operation.
  liftMap :: (Module (Scalar (Coefficient poly)) alg, Ring alg, Commutative alg)
           => (Ordinal (Arity poly) -> alg) -> poly -> alg
  liftMap mor f =
    sum [ Scalar r .* sum [ Scalar (fromInteger (fromIntegral i) :: Coefficient poly) .* mor o
                          | i <- toList (m :: Monomial (Arity poly)) :: [Int]
                          | o <- enumOrdinal sing ]
        | (m, r) <- HM.toList (terms f) ]
  {-# INLINE liftMap #-}

  -- | @'monomials' f@ returns the finite set of all monomials appearing in @f@.
  monomials :: poly -> HS.HashSet (Monomial (Arity poly))
  monomials = HS.fromList . HM.keys . terms
  {-# INLINE monomials #-}

  terms :: poly -> HM.HashMap (Monomial (Arity poly)) (Coefficient poly)
  terms f = HM.fromList [ (m, c)
                        | m <- HS.toList $ monomials f
                        , let c = coeff m f
                        , not (isZero c)
                        ]
  {-# INLINE terms #-}

  coeff :: Monomial (Arity poly) -> poly -> Coefficient poly
  coeff m = runCoeff . liftMap (\i -> WrapCoeff $ fromInteger $ fromIntegral $ m %!! i)
  {-# INLINE coeff #-}

  constantTerm :: poly -> Coefficient poly
  constantTerm = runCoeff . liftMap (\ _ -> WrapCoeff zero)
  {-# INLINE constantTerm #-}

  sArity :: poly -> SNat (Arity poly)
  sArity _ = sing
  {-# INLINE sArity #-}

  arity :: poly -> Natural
  arity _ = sNatToInt (sing :: SNat (Arity poly))
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

  totalDegree :: poly -> Natural
  totalDegree = maybe 0 fromIntegral . maximumOf folded . HS.map V.sum . monomials
  {-# INLINE totalDegree #-}

-- | Class to lookup ordering from its (type-level) name.
class IsOrder (ordering :: *) where
  cmpMonomial :: Proxy ordering -> MonomialOrder

class IsOrder name => IsMonomialOrder name

type MonomialOrder = forall n. Monomial n -> Monomial n -> Ordering

newtype OrderedMonomial (ordering :: *) n = OrderedMonomial { getMonomial :: Monomial n }

class (IsMonomialOrder (MOrder poly), IsPolynomial poly) => IsOrderedPolynomial poly where
  type MOrder poly :: *

  leadingTerm :: poly -> (Coefficient poly, OrderedMonomial (MOrder poly) (Arity poly))
  leadingTerm = (,) <$> leadingCoeff <*> leadingMonomial
  {-# INLINE leadingTerm #-}

  leadingMonomial :: poly -> OrderedMonomial (MOrder poly) (Arity poly)
  leadingMonomial = snd . leadingTerm
  {-# INLINE leadingMonomial #-}

  leadingCoeff :: poly -> Coefficient poly
  leadingCoeff = fst . leadingTerm
  {-# INLINE leadingCoeff #-}

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
