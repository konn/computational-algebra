{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables   #-}
{-# LANGUAGE UndecidableInstances                                            #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Algebra.Ring.Polynomial.Quotient ( Quotient(), QIdeal(), reifyQuotient, modIdeal
                                        , modIdeal', quotRepr, withQuotient
                                        , genQuotVars, genQuotVars'
                                        , standardMonomials, standardMonomials'
                                        , reduce, multWithTable, multUnamb, isZeroDimensional) where
import           Algebra.Algorithms.Groebner
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Algebra.Scalar
import           Control.DeepSeq
import qualified Data.HashMap.Lazy           as M
import           Data.List                   (sortBy)
import           Data.Maybe
import           Data.Ord
import           Data.Proxy
import           Data.Reflection
import           Data.Type.Natural           hiding (one, zero)
import           Data.Unamb
import           Data.Vector.Sized           (Vector (..))
import qualified Data.Vector.Sized           as V
import           Numeric.Algebra
import qualified Numeric.Algebra             as NA
import           Prelude                     hiding (lex, negate, recip, sum,
                                              (*), (+), (-), (^), (^^))
import qualified Prelude                     as P

-- | The polynomial modulo the ideal indexed at the last type-parameter.
data Quotient r ord n ideal = Quotient { quotRepr_ :: OrderedPolynomial r ord n } deriving (Eq)

data QIdeal r ord n = ZeroDimIdeal { gBasis    :: ![OrderedPolynomial r ord n]
                                   , vBasis    :: [Monomial n]
                                   , multTable :: Table r ord n
                                   }
                    | QIdeal { gBasis :: [OrderedPolynomial r ord n]
                             }

instance NFData (OrderedPolynomial r ord n) => NFData (Quotient r ord n ideal) where
  rnf (Quotient op) = rnf op

type Table r ord n = M.HashMap (Monomial n, Monomial n) (OrderedPolynomial r ord n)



multUnamb :: (Reifies ideal (QIdeal r ord n), IsMonomialOrder ord, IsPolynomial r n, Field r)
          => Quotient r ord n ideal -> Quotient r ord n ideal
          -> Quotient r ord n ideal
multUnamb a b = unamb (a * b) (multUnamb a b)

multWithTable :: (Reifies ideal (QIdeal r ord n), IsMonomialOrder ord, IsPolynomial r n, Field r)
              => Quotient r ord n ideal -> Quotient r ord n ideal
              -> Quotient r ord n ideal
multWithTable f g =
  let qid = reflect f
      table = multTable qid
      basis = vBasis qid
  in sum [ Quotient $ coeff l (quotRepr f) .*. coeff r (quotRepr g) .*. (M.lookupDefault zero (l, r) table)
         | l <- basis, r <- basis ]

instance Show (OrderedPolynomial r ord n) => Show (Quotient r ord n ideal) where
  show (Quotient f) = show f

buildMultTable :: (IsMonomialOrder ord, IsPolynomial r n, Field r)
               => [OrderedPolynomial r ord n] -> [Monomial n] -> Table r ord n
buildMultTable bs ms =
    M.fromList [ ((p, q), (toPolynomial (one, p) * toPolynomial (one, q)) `modPolynomial` bs)
               | p <- ms, q <- ms]

stdMonoms :: forall r n ord. (IsMonomialOrder ord, IsPolynomial r n, Field r) => [OrderedPolynomial r ord n] -> Maybe [Monomial n]
stdMonoms basis = do
  let lms = map leadingTerm basis
      dim = sing :: SNat n
      tests = zip (diag 1 0 dim) (diag 0 1 dim)
      mexp (val, test) = [ V.foldr (+) 0 $ V.zipWith (*) val lm0
                         | (c, lm0) <- lms, c /= zero
                         , let a = V.foldr (+) 0 $ V.zipWith (*) lm0 test, a == 0
                         ]
  degs <- mapM (minimum' . mexp) tests
  return [ monom | ds0 <- sequence $ map (enumFromTo 0) degs
         , let monom = fromList dim ds0
         , let ds = toPolynomial (one, monom)
         , ds `modPolynomial` basis == ds]

-- | Find the standard monomials of the quotient ring for the zero-dimensional ideal,
--   which are form the basis of it as k-vector space.
standardMonomials' :: (Reifies ideal (QIdeal r ord n), IsPolynomial r n, Field r, IsMonomialOrder ord)
                   => Proxy ideal -> Maybe [Quotient r ord n ideal]
standardMonomials' pxy =
  case reflect pxy of
    ZeroDimIdeal _ vB _ -> Just $ map (modIdeal . toPolynomial . (,) one) vB
    _ -> Nothing

standardMonomials :: forall ord ideal r n. ( IsMonomialOrder ord
                                           , Reifies ideal (QIdeal r ord n)
                                           , IsPolynomial r n, Field r)
                  => Maybe [Quotient r ord n ideal]
standardMonomials = standardMonomials' (Proxy :: Proxy ideal)

genQuotVars' :: forall ord n ideal r. ( Reifies ideal (QIdeal r ord (S n))
                                      , IsMonomialOrder ord, IsPolynomial r (S n), Field r)
             => Proxy ideal -> [Quotient r ord (S n) ideal]
genQuotVars' pxy = map (modIdeal' pxy) $ genVars (sing :: SNat (S n))

genQuotVars :: forall ord n ideal r. (IsMonomialOrder ord, Reifies ideal (QIdeal r ord (S n))
                                     , IsPolynomial r (S n), Field r)
             => [Quotient r ord (S n) ideal]
genQuotVars = genQuotVars' (Proxy :: Proxy ideal)

minimum' :: Ord a => [a] -> Maybe a
minimum' [] = Nothing
minimum' xs = Just $ minimum xs

diag :: a -> a -> SNat n -> [V.Vector a n]
diag _ _ SZ = []
diag d _ (SS SZ) = [d :- Nil]
diag d z (SS n)  = (d :- V.unsafeFromList n (repeat z)) : map (z :-) (diag d z n)

-- | Polynomial modulo ideal.
modIdeal :: forall ord r n ideal. ( IsMonomialOrder ord, Reifies ideal (QIdeal r ord n)
                                  , IsPolynomial r n, Field r)
           => OrderedPolynomial r ord n -> Quotient r ord n ideal
modIdeal = modIdeal' (Proxy :: Proxy ideal)

-- | Polynomial modulo ideal given by @Proxy@.
modIdeal' :: (IsMonomialOrder ord, Reifies ideal (QIdeal r ord n), IsPolynomial r n, Field r)
          => Proxy ideal -> OrderedPolynomial r ord n -> Quotient r ord n ideal
modIdeal' pxy f = Quotient $ f `modPolynomial` gBasis (reflect pxy)

buildQIdeal :: (IsMonomialOrder ord, IsPolynomial r n, Field r)
            => Ideal (OrderedPolynomial r ord n) -> QIdeal r ord n
buildQIdeal ideal =
    let bs = sortBy (comparing leadingOrderedMonomial) $! calcGroebnerBasis ideal
    in case stdMonoms bs of
         Nothing -> QIdeal bs
         Just ms -> ZeroDimIdeal bs ms (buildMultTable bs ms)

-- | Reifies the ideal at the type-level. The ideal can be recovered with 'reflect'.
reifyQuotient :: (Field r, IsPolynomial r n, IsMonomialOrder ord)
              => Ideal (OrderedPolynomial r ord n)
              -> (forall ideal. Reifies ideal (QIdeal r ord n) => Proxy ideal -> a)
              -> a
reifyQuotient ideal = reify (buildQIdeal ideal)

-- | Computes polynomial modulo ideal.
withQuotient :: (Field r, IsPolynomial r n, IsMonomialOrder ord)
             => Ideal (OrderedPolynomial r ord n)
             -> (forall ideal. Reifies ideal (QIdeal r ord n) => Quotient r ord n ideal)
             -> OrderedPolynomial r ord n
withQuotient ideal v = reifyQuotient ideal (quotRepr_ . asProxyOf v)


asProxyOf :: f s -> Proxy s -> f s
asProxyOf a _ = a

-- | Representative polynomial of given quotient polynomial.
quotRepr :: Quotient r ord n ideal -> OrderedPolynomial r ord n
quotRepr = quotRepr_

instance (IsMonomialOrder ord, Reifies ideal (QIdeal r ord n), IsPolynomial r n, Field r) => Additive (Quotient r ord n ideal) where
  f + g = Quotient $ quotRepr_ f + quotRepr_ g
instance (IsMonomialOrder ord, Reifies ideal (QIdeal r ord n), IsPolynomial r n, Field r) => LeftModule Natural (Quotient r ord n ideal) where
  n .* f = Quotient $ n .* quotRepr_ f
instance (IsMonomialOrder ord, Reifies ideal (QIdeal r ord n), IsPolynomial r n, Field r) => RightModule Natural (Quotient r ord n ideal) where
  f *. n = Quotient $ quotRepr_ f *. n
instance (IsMonomialOrder ord, Reifies ideal (QIdeal r ord n), IsPolynomial r n, Field r) => Monoidal (Quotient r ord n ideal) where
  zero   = Quotient zero
instance (IsMonomialOrder ord, Reifies ideal (QIdeal r ord n), IsPolynomial r n, Field r) => LeftModule Integer (Quotient r ord n ideal) where
  n .* f = Quotient $ n .* quotRepr_ f
instance (IsMonomialOrder ord, Reifies ideal (QIdeal r ord n), IsPolynomial r n, Field r) => RightModule Integer (Quotient r ord n ideal) where
  f *. n = Quotient $ quotRepr_ f *. n
instance (IsMonomialOrder ord, Reifies ideal (QIdeal r ord n), IsPolynomial r n, Field r) => Group (Quotient r ord n ideal) where
  negate f = Quotient $ negate $ quotRepr_ f
  f - g    = Quotient $ quotRepr_ f - quotRepr_ g
instance (IsMonomialOrder ord, Reifies ideal (QIdeal r ord n), IsPolynomial r n, Field r) => Abelian (Quotient r ord n ideal) where
instance (IsMonomialOrder ord, Reifies ideal (QIdeal r ord n), IsPolynomial r n, Field r) => Multiplicative (Quotient r ord n ideal) where
  f * g = modIdeal $ quotRepr_ f * quotRepr_ g
instance (IsMonomialOrder ord, Reifies ideal (QIdeal r ord n), IsPolynomial r n, Field r) => Semiring (Quotient r ord n ideal) where
instance (IsMonomialOrder ord, Reifies ideal (QIdeal r ord n), IsPolynomial r n, Field r) => Unital (Quotient r ord n ideal) where
  one   = modIdeal one
instance (IsMonomialOrder ord, Reifies ideal (QIdeal r ord n), IsPolynomial r n, Field r) => Rig (Quotient r ord n ideal) where
instance (IsMonomialOrder ord, Reifies ideal (QIdeal r ord n), IsPolynomial r n, Field r) => Ring (Quotient r ord n ideal) where
instance (IsMonomialOrder ord, Reifies ideal (QIdeal r ord n), IsPolynomial r n, Field r) => LeftModule (Scalar r) (Quotient r ord n ideal) where
  r .* f = Quotient $ r .* quotRepr_ f
instance (IsMonomialOrder ord, Reifies ideal (QIdeal r ord n), IsPolynomial r n, Field r) => RightModule (Scalar r) (Quotient r ord n ideal) where
  f *. r = Quotient $ quotRepr_ f *. r

instance (IsMonomialOrder ord, Num r, Reifies ideal (QIdeal r ord n), IsPolynomial r n, Field r) => Num (Quotient r ord n ideal) where
  (+) = (NA.+)
  (*) = (NA.*)
  fromInteger = Quotient . P.fromInteger
  signum = Quotient . signum . quotRepr_
  abs    = id
  negate = Quotient . negate . quotRepr_

-- | Reduce polynomial modulo ideal.
reduce :: (Eq r, Division r, SingRep n, NoetherianRing r, IsMonomialOrder ord)
       => OrderedPolynomial r ord n -> Ideal (OrderedPolynomial r ord n) -> OrderedPolynomial r ord n
reduce f i = withQuotient i $ modIdeal f

isZeroDimensional :: (Eq r, Division r, SingRep n, NoetherianRing r, IsMonomialOrder ord) => [OrderedPolynomial r ord n] -> Bool
isZeroDimensional ii = isJust $ stdMonoms ii
