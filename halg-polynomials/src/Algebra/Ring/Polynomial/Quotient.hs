{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts            #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving    #-}
{-# LANGUAGE MagicHash, MultiParamTypeClasses, PolyKinds, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TypeOperators  #-}
{-# LANGUAGE UndecidableInstances                                    #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Algebra.Ring.Polynomial.Quotient
       ( Quotient(), QIdeal(), reifyQuotient, modIdeal
       , modIdeal', quotRepr, withQuotient, vectorRep
       , genQuotVars, genQuotVars', gBasis', matRep0
       , standardMonomials, standardMonomials', matRepr'
       , reduce, multWithTable, multUnamb, isZeroDimensional
       )
       where
import Algebra.Algorithms.Groebner        (calcGroebnerBasis)
import Algebra.Internal
import Algebra.Prelude.Core
import Algebra.Ring.Polynomial.Univariate (Unipol)

import           Control.DeepSeq
import           Control.Lens         (folded, ifoldMap, minimumOf)
import qualified Data.Coerce          as C
import qualified Data.HashMap.Lazy    as HM
import           Data.Kind            (Type)
import qualified Data.Map             as Map
import qualified Data.Matrix          as M
import           Data.Monoid          (Sum (..))
import           Data.MonoTraversable (osum)
import           Data.Reflection
import           Data.Unamb           (unamb)
import qualified Data.Vector          as V
import qualified Numeric.Algebra      as NA
import qualified Prelude              as P

-- | The polynomial modulo the ideal indexed at the last type-parameter.
newtype Quotient poly ideal = Quotient { quotRepr_ :: poly }
                         deriving (Eq)

-- | Representative polynomial of given quotient polynomial.
quotRepr :: Quotient poly ideal -> poly
quotRepr = quotRepr_

data QIdeal poly = ZeroDimIdeal { _gBasis   :: ![poly]
                                , _vBasis   :: ![OrderedMonomial (MOrder poly) (Arity poly)]
                                , multTable :: Table poly
                                }
                 | QIdeal { _gBasis :: [poly]
                          }

instance NFData poly => NFData (Quotient poly ideal) where
  rnf (Quotient op) = rnf op

type Table poly = HM.HashMap
                     (OrderedMonomial (MOrder poly) (Arity poly),
                      OrderedMonomial (MOrder poly) (Arity poly))
                     poly

vectorRep :: forall poly ideal.
              (IsOrderedPolynomial poly, Reifies ideal (QIdeal poly))
           => Quotient poly ideal -> V.Vector (Coefficient poly)
vectorRep f =
  let ZeroDimIdeal _ base _ = reflect f
      mf = quotRepr f
  in V.fromList $ map (flip coeff mf) base
{-# SPECIALISE INLINE
   vectorRep :: (IsMonomialOrder n ord, CoeffRing r, KnownNat n,
                 Reifies ideal (QIdeal (OrderedPolynomial r ord n)))
             => Quotient (OrderedPolynomial r ord n) ideal -> V.Vector r
 #-}
{-# SPECIALISE INLINE
   vectorRep :: (CoeffRing r, Reifies ideal (QIdeal (Unipol r)))
             => Quotient (Unipol r) ideal -> V.Vector r
 #-}
{-# SPECIALISE INLINE
   vectorRep :: (IsMonomialOrder n ord, KnownNat n,
                 Reifies ideal (QIdeal (OrderedPolynomial Rational ord n)))
             => Quotient (OrderedPolynomial Rational ord n) ideal -> V.Vector Rational
 #-}
{-# SPECIALISE INLINE
   vectorRep :: (Reifies ideal (QIdeal (Unipol Rational)))
             => Quotient (Unipol Rational) ideal -> V.Vector Rational
 #-}
{-# INLINE vectorRep #-}

matRepr' :: forall poly ideal.
          (Field (Coefficient poly),
           Reifies ideal (QIdeal poly), IsOrderedPolynomial poly)
       => Quotient poly ideal -> M.Matrix (Coefficient poly)
matRepr' f =
  let ZeroDimIdeal _bs _ _ = reflect f
  in C.coerce $ getSum $
     ifoldMap
          (\t c ->
            Sum $ fmap (WrapAlgebra . (c *)) $ matRep0 (Proxy :: Proxy poly) (Proxy :: Proxy ideal) t)
          (terms (quotRepr_ f))
{-# SPECIALISE INLINE
   matRepr' :: (IsMonomialOrder n ord, CoeffRing r, KnownNat n, Field r,
                 Reifies ideal (QIdeal (OrderedPolynomial r ord n)))
             => Quotient (OrderedPolynomial r ord n) ideal -> M.Matrix r
 #-}
{-# SPECIALISE INLINE
   matRepr' :: (Field r, CoeffRing r, Reifies ideal (QIdeal (Unipol r)))
             => Quotient (Unipol r) ideal -> M.Matrix r
 #-}
{-# SPECIALISE INLINE
   matRepr' :: (IsMonomialOrder n ord, KnownNat n,
                 Reifies ideal (QIdeal (OrderedPolynomial Rational ord n)))
             => Quotient (OrderedPolynomial Rational ord n) ideal -> M.Matrix Rational
 #-}
{-# SPECIALISE INLINE
   matRepr' :: (Reifies ideal (QIdeal (Unipol Rational)))
             => Quotient (Unipol Rational) ideal -> M.Matrix Rational
 #-}
{-# INLINE matRepr' #-}

matRep0 :: forall poly ideal.
           (IsOrderedPolynomial poly, Field (Coefficient poly), Reifies ideal (QIdeal poly))
        => Proxy poly -> Proxy ideal -> OrderedMonomial (MOrder poly) (Arity poly) -> M.Matrix (Coefficient poly)
matRep0 _ pxy m =
  let ZeroDimIdeal _ bs table = reflect pxy
  in foldr (M.<|>) (M.fromList 0 0 [])
     [ M.colVector $ vectorRep $ modIdeal' pxy (HM.lookupDefault zero (m, b) table)
     | b <- bs  ]
{-# SPECIALISE INLINE
   matRep0 :: (IsMonomialOrder n ord, Field r, CoeffRing r, KnownNat n,
               Reifies ideal (QIdeal (OrderedPolynomial r ord n)))
             => Proxy (OrderedPolynomial r ord n) -> Proxy ideal -> OrderedMonomial ord n -> M.Matrix r
 #-}
{-# SPECIALISE INLINE
   matRep0 :: (CoeffRing r, Field r, Reifies ideal (QIdeal (Unipol r)))
             => Proxy (Unipol r) -> Proxy ideal -> OrderedMonomial Grevlex 1 -> M.Matrix r
 #-}
{-# SPECIALISE INLINE
   matRep0 :: (IsMonomialOrder n ord,KnownNat n,
               Reifies ideal (QIdeal (OrderedPolynomial Rational ord n)))
             => Proxy (OrderedPolynomial Rational ord n) -> Proxy ideal -> OrderedMonomial ord n -> M.Matrix Rational
 #-}
{-# SPECIALISE INLINE
   matRep0 :: (Reifies ideal (QIdeal (Unipol Rational)))
             => Proxy (Unipol Rational) -> Proxy ideal -> OrderedMonomial Grevlex 1 -> M.Matrix Rational
 #-}
{-# INLINE matRep0 #-}

multUnamb :: (IsOrderedPolynomial poly, Field (Coefficient poly),
              Reifies ideal (QIdeal poly))
          => Quotient poly ideal -> Quotient poly ideal
          -> Quotient poly ideal
multUnamb a b = unamb (a * b) (multWithTable a b)
{-# SPECIALISE INLINE
  multUnamb :: (CoeffRing r, IsMonomialOrder n ord, KnownNat n,
                Field r, Reifies ideal (QIdeal (OrderedPolynomial r ord n)))
            => Quotient (OrderedPolynomial r ord n) ideal
            -> Quotient (OrderedPolynomial r ord n) ideal
            -> Quotient (OrderedPolynomial r ord n) ideal
 #-}
{-# SPECIALISE INLINE
  multUnamb :: (CoeffRing r, Field r, Reifies ideal (QIdeal (Unipol r)))
            => Quotient (Unipol r) ideal
            -> Quotient (Unipol r) ideal
            -> Quotient (Unipol r) ideal
 #-}
{-# SPECIALISE INLINE
  multUnamb :: (IsMonomialOrder n ord, KnownNat n,
                Reifies ideal (QIdeal (OrderedPolynomial Rational ord n)))
            => Quotient (OrderedPolynomial Rational ord n) ideal
            -> Quotient (OrderedPolynomial Rational ord n) ideal
            -> Quotient (OrderedPolynomial Rational ord n) ideal
 #-}
{-# SPECIALISE INLINE
  multUnamb :: (Reifies ideal (QIdeal (Unipol Rational)))
            => Quotient (Unipol Rational) ideal
            -> Quotient (Unipol Rational) ideal
            -> Quotient (Unipol Rational) ideal
 #-}
{-# INLINE multUnamb #-}

multWithTable :: (IsOrderedPolynomial poly, Reifies ideal (QIdeal poly))
              => Quotient poly ideal -> Quotient poly ideal
              -> Quotient poly ideal
multWithTable f g =
  let qid = reflect f
      table = multTable qid
  in sum [ Quotient $ c .*. d .*. (HM.lookupDefault zero (l, r) table)
         | (l,c) <- Map.toList $ terms $ quotRepr_ f
         , (r,d) <- Map.toList $ terms $ quotRepr_ g
         ]

{-# SPECIALISE INLINE
 multWithTable :: (CoeffRing r, IsMonomialOrder n ord, KnownNat n,
                   Reifies ideal (QIdeal (OrderedPolynomial r ord n)))
               => Quotient (OrderedPolynomial r ord n) ideal
               -> Quotient (OrderedPolynomial r ord n) ideal
               -> Quotient (OrderedPolynomial r ord n) ideal
 #-}
{-# SPECIALISE INLINE
 multWithTable :: (CoeffRing r, Reifies ideal (QIdeal (Unipol r)))
               => Quotient (Unipol r) ideal
               -> Quotient (Unipol r) ideal
               -> Quotient (Unipol r) ideal
 #-}
{-# INLINE multWithTable #-}


instance Show poly => Show (Quotient poly ideal) where
  show (Quotient f) = show f

buildMultTable :: (IsOrderedPolynomial poly, Field (Coefficient poly))
               => [poly] -> [OrderedMonomial (MOrder poly) (Arity poly)] -> Table poly
buildMultTable bs ms =
    HM.fromList [ ((p, q), (toPolynomial (one, p) * toPolynomial (one, q)) `modPolynomial` bs)
               | p <- ms, q <- ms]
{-# SPECIALISE INLINE
  buildMultTable :: (IsMonomialOrder n ord, Field r, CoeffRing r, KnownNat n)
                 => [OrderedPolynomial r ord n]
                 -> [OrderedMonomial ord n]
                 -> Table (OrderedPolynomial r ord n)
 #-}
{-# SPECIALISE INLINE
  buildMultTable :: (Field r, CoeffRing r)
                 => [Unipol r]
                 -> [OrderedMonomial Grevlex 1]
                 -> Table (Unipol r)
 #-}

stdMonoms :: forall poly.
             (IsOrderedPolynomial poly, Field (Coefficient poly))
           => [poly] -> Maybe [OrderedMonomial (MOrder poly) (Arity poly)]
stdMonoms basis = do
  let lms = map leadingTerm basis
      dim = sing :: SNat (Arity poly)
      tests = zip (diag 1 0 dim) (diag 0 1 dim)
      mexp (val, test) = [ osum $ zipWithSame (*) val $ getMonomial lm0
                         | (c, lm0) <- lms, c /= zero
                         , let a = osum $ zipWithSame (*) (getMonomial lm0) test
                         , a == 0
                         ]
  degs <- mapM (minimumOf folded . mexp) tests
  return $ sort [ monom
                | ds0 <- mapM (enumFromTo 0) degs
                , let monom = OrderedMonomial $ fromList dim ds0
                , let ds = toPolynomial (one, monom)
                , ds `modPolynomial` basis == ds
                ]
{-# SPECIALISE
  stdMonoms :: (IsMonomialOrder n ord, Field r, CoeffRing r, KnownNat n)
            => [OrderedPolynomial r ord n]
            -> Maybe [OrderedMonomial ord n]
 #-}
{-# SPECIALISE
  stdMonoms :: (Field r, CoeffRing r)
            => [Unipol r]
            -> Maybe [OrderedMonomial Grevlex 1]
 #-}

diag :: Unbox a => a -> a -> SNat n -> [USized n a]
diag d z n = [ generate n (\j -> if i == j then d else z)
             | i <- enumOrdinal n
             ]
{-# INLINE diag #-}

-- | Find the standard monomials of the quotient ring for the zero-dimensional ideal,
--   which are form the basis of it as k-vector space.
standardMonomials' :: (IsOrderedPolynomial poly, Field (Coefficient poly),
                       Reifies ideal (QIdeal poly))
                   => Proxy ideal -> Maybe [Quotient poly ideal]
standardMonomials' pxy =
  case reflect pxy of
    ZeroDimIdeal _ vB _ -> Just $ map (modIdeal . toPolynomial . (,) one) vB
    _ -> Nothing
{-# SPECIALISE INLINE
  standardMonomials' :: (IsMonomialOrder n ord, CoeffRing r, KnownNat n, Field r,
                         Reifies ideal (QIdeal (OrderedPolynomial r ord n)))
                     => Proxy ideal -> Maybe [Quotient (OrderedPolynomial r ord n) ideal]
 #-}
{-# SPECIALISE INLINE
  standardMonomials' :: (CoeffRing r, Field r, Reifies ideal (QIdeal (Unipol r)))
                     => Proxy ideal -> Maybe [Quotient (Unipol r) ideal]
 #-}
{-# INLINE standardMonomials' #-}

standardMonomials :: forall poly ideal.
                     (IsOrderedPolynomial poly, Field (Coefficient poly),
                      Reifies ideal (QIdeal poly))
                  => Maybe [Quotient poly ideal]
standardMonomials = standardMonomials' (Proxy :: Proxy ideal)
{-# SPECIALISE INLINE
  standardMonomials :: (IsMonomialOrder n ord, CoeffRing r, KnownNat n, Field r,
                         Reifies ideal (QIdeal (OrderedPolynomial r ord n)))
                     => Maybe [Quotient (OrderedPolynomial r ord n) ideal]
 #-}
{-# SPECIALISE INLINE
  standardMonomials :: (CoeffRing r, Field r, Reifies ideal (QIdeal (Unipol r)))
                     => Maybe [Quotient (Unipol r) ideal]
 #-}
{-# INLINE standardMonomials #-}

genQuotVars' :: forall poly ideal.
                (IsOrderedPolynomial poly, Field (Coefficient poly),
                 Reifies ideal (QIdeal poly))
             => Proxy ideal -> [Quotient poly ideal]
genQuotVars' pxy = map (modIdeal' pxy) vars
{-# SPECIALISE INLINE
  genQuotVars' :: (IsMonomialOrder n ord, CoeffRing r, KnownNat n, Field r,
                   Reifies ideal (QIdeal (OrderedPolynomial r ord n)))
               => Proxy ideal -> [Quotient (OrderedPolynomial r ord n) ideal]
 #-}
{-# SPECIALISE INLINE
  genQuotVars' :: (CoeffRing r, Field r, Reifies ideal (QIdeal (Unipol r)))
               => Proxy ideal -> [Quotient (Unipol r) ideal]
 #-}
{-# INLINE genQuotVars' #-}

genQuotVars :: forall poly ideal. (IsOrderedPolynomial poly, Field (Coefficient poly),
                 Reifies ideal (QIdeal poly))
             => [Quotient poly ideal]
genQuotVars = genQuotVars' (Proxy :: Proxy ideal)

{-# SPECIALISE INLINE
  genQuotVars :: (IsMonomialOrder n ord, CoeffRing r, KnownNat n, Field r,
                  Reifies ideal (QIdeal (OrderedPolynomial r ord n)))
              => [Quotient (OrderedPolynomial r ord n) ideal]
 #-}
{-# SPECIALISE INLINE
  genQuotVars :: (CoeffRing r, Field r, Reifies ideal (QIdeal (Unipol r)))
              => [Quotient (Unipol r) ideal]
 #-}
{-# INLINE genQuotVars #-}

-- | Polynomial modulo ideal.
modIdeal :: forall poly ideal.
            (IsOrderedPolynomial poly, Field (Coefficient poly),
             Reifies ideal (QIdeal poly))
           => poly -> Quotient poly ideal
modIdeal = modIdeal' (Proxy :: Proxy ideal)

gBasis' :: (Reifies ideal (QIdeal poly))
        => Proxy ideal -> [poly]
gBasis' pxy = _gBasis (reflect pxy)
{-# SPECIALISE INLINE
  gBasis' :: (Reifies ideal (QIdeal (OrderedPolynomial r ord n)))
          => Proxy ideal -> [OrderedPolynomial r ord n]
 #-}
{-# SPECIALISE INLINE
  gBasis' :: (Reifies ideal (QIdeal (Unipol r)))
          => Proxy ideal -> [Unipol r]
 #-}
{-# INLINE gBasis' #-}

-- | Polynomial modulo ideal given by @Proxy@.
modIdeal' :: (IsOrderedPolynomial poly, Field (Coefficient poly),
              Reifies ideal (QIdeal poly))
          => Proxy ideal -> poly -> Quotient poly ideal
modIdeal' pxy f = Quotient $ f `modPolynomial` _gBasis (reflect pxy)
{-# SPECIALISE INLINE
  modIdeal' :: (IsMonomialOrder n ord, CoeffRing r, KnownNat n, Field r,
                Reifies ideal (QIdeal (OrderedPolynomial r ord n)))
            => Proxy ideal -> OrderedPolynomial r ord n
            -> Quotient (OrderedPolynomial r ord n) ideal
 #-}
{-# SPECIALISE INLINE
  modIdeal' :: (CoeffRing r, Field r,
                Reifies ideal (QIdeal (Unipol r)))
            => Proxy ideal -> Unipol r
            -> Quotient (Unipol r) ideal
 #-}
{-# INLINE modIdeal' #-}

buildQIdeal :: (IsOrderedPolynomial poly, Field (Coefficient poly))
            => Ideal poly -> QIdeal poly
buildQIdeal ideal =
    let bs = sortOn leadingMonomial $! calcGroebnerBasis ideal
    in case stdMonoms bs of
         Nothing -> QIdeal bs
         Just ms -> ZeroDimIdeal bs ms (buildMultTable bs ms)
{-# SPECIALISE INLINE
  buildQIdeal :: (IsMonomialOrder n ord, CoeffRing r, KnownNat n, Field r)
              => Ideal (OrderedPolynomial r ord n)
              -> QIdeal (OrderedPolynomial r ord n)
 #-}
{-# SPECIALISE INLINE
  buildQIdeal :: (CoeffRing r, Field r)
              => Ideal (Unipol r)
              -> QIdeal (Unipol r)
 #-}
{-# INLINE buildQIdeal #-}

-- | Reifies the ideal at the type-level. The ideal can be recovered with 'reflect'.
reifyQuotient :: (IsOrderedPolynomial poly, Field (Coefficient poly))
              => Ideal poly
              -> (forall (ideal :: Type). Reifies ideal (QIdeal poly) => Proxy ideal -> a)
              -> a
reifyQuotient ideal = reify (buildQIdeal ideal)
{-# INLINE reifyQuotient #-}

-- | Computes polynomial modulo ideal.
withQuotient :: (IsOrderedPolynomial poly, Field (Coefficient poly))
             => Ideal poly
             -> (forall (ideal :: Type). Reifies ideal (QIdeal poly) => Quotient poly ideal)
             -> poly
withQuotient ideal v = reifyQuotient ideal (quotRepr_ . asProxyOf v)
{-# INLINE withQuotient #-}

asProxyOf :: f s -> Proxy s -> f s
asProxyOf a _ = a
{-# INLINE asProxyOf #-}

deriving instance Additive poly => Additive (Quotient poly ideal)
deriving instance Monoidal poly => Monoidal (Quotient poly ideal)
deriving instance Group poly => Group (Quotient poly ideal)
deriving instance Abelian poly => Abelian (Quotient poly ideal)

instance Monoidal poly
      => LeftModule Natural (Quotient poly ideal) where
  r .* f = Quotient $ r .* quotRepr_ f
instance Monoidal poly
      => RightModule Natural (Quotient poly ideal) where
  f *. r = Quotient $ r .* quotRepr_ f
instance Group poly
      => LeftModule Integer (Quotient poly ideal) where
  r .* f = Quotient $ r .* quotRepr_ f
instance Group poly
      => RightModule Integer (Quotient poly ideal) where
  f *. r = Quotient $ r .* quotRepr_ f


instance (Field (Coefficient poly), IsOrderedPolynomial poly, Reifies ideal (QIdeal poly))
       => Multiplicative (Quotient poly ideal) where
  f * g = modIdeal $ quotRepr_ f * quotRepr_ g

instance (Field (Coefficient poly), IsOrderedPolynomial poly, Reifies ideal (QIdeal poly))
       => Semiring (Quotient poly ideal)
instance (Field (Coefficient poly), IsOrderedPolynomial poly, Reifies ideal (QIdeal poly))
      => Unital (Quotient poly ideal) where
  one   = modIdeal one
instance (Field (Coefficient poly), IsOrderedPolynomial poly,
          Reifies ideal (QIdeal poly))
      => Rig (Quotient poly ideal)
instance (Field (Coefficient poly),
          IsOrderedPolynomial poly,
          Reifies ideal (QIdeal poly))
      => Ring (Quotient poly ideal)
instance (r ~ (Coefficient poly), Field (Coefficient poly),
          IsOrderedPolynomial poly)
      => LeftModule (Scalar r) (Quotient poly ideal) where
  r .* f = Quotient $ r .* quotRepr_ f
instance (r ~ (Coefficient poly), IsOrderedPolynomial poly)
      => RightModule (Scalar r) (Quotient poly ideal) where
  f *. r = Quotient $ quotRepr_ f *. r

instance (Field (Coefficient poly), UnitNormalForm poly, IsOrderedPolynomial poly,
          Reifies ideal (QIdeal poly))
     =>  P.Num (Quotient poly ideal) where
  (+) = (NA.+)
  (*) = (NA.*)
  fromInteger = Quotient . unwrapAlgebra . P.fromInteger
  signum = Quotient . unwrapAlgebra . P.signum . WrapAlgebra . quotRepr_
  abs    = Quotient . unwrapAlgebra . P.abs . WrapAlgebra . quotRepr_
  negate = Quotient . unwrapAlgebra . P.negate . WrapAlgebra . quotRepr_

-- | Reduce polynomial modulo ideal.
reduce :: (IsOrderedPolynomial poly, Field (Coefficient poly))
       => poly -> Ideal poly -> poly
reduce f i = withQuotient i $ modIdeal f
{-# SPECIALISE INLINE
  reduce :: (IsMonomialOrder n ord, CoeffRing r, KnownNat n, Field r)
         => OrderedPolynomial r ord n
         -> Ideal (OrderedPolynomial r ord n)
         -> OrderedPolynomial r ord n
 #-}
{-# SPECIALISE INLINE
  reduce :: (CoeffRing r, Field r)
         => Unipol r
         -> Ideal (Unipol r)
         -> Unipol r
 #-}
{-# INLINE reduce #-}

isZeroDimensional :: (IsOrderedPolynomial poly, Field (Coefficient poly))
                  => [poly] -> Bool
isZeroDimensional ii = isJust $ stdMonoms $ calcGroebnerBasis $ toIdeal ii
{-# INLINE isZeroDimensional #-}
