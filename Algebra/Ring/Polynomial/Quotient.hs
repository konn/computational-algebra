{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables   #-}
{-# LANGUAGE UndecidableInstances                                            #-}
module Algebra.Ring.Polynomial.Quotient ( Quotient(), reifyQuotient, modIdeal
                                        , modIdeal', quotRepr, withQuotient
                                        , genQuotVars, genQuotVars'
                                        , standardMonomials, standardMonomials') where
import           Algebra.Algorithms.Groebner
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Algebra.Scalar
import           Data.Proxy
import           Data.Reflection
import           Data.Type.Natural           hiding (one, zero)
import           Data.Vector.Sized           hiding (foldl, foldr, fromList,
                                              head, map, zipWith)
import qualified Data.Vector.Sized           as V
import           Numeric.Algebra
import qualified Numeric.Algebra             as NA
import           Prelude                     hiding (lex, negate, recip, sum,
                                              (*), (+), (-), (^), (^^))
import qualified Prelude                     as P

-- | The polynomial modulo the ideal indexed at the last type-parameter.
data Quotient r n ideal = Quotient { quotRepr_ :: Polynomial r n } deriving (Eq)

instance Show (Polynomial r n) => Show (Quotient r n ideal) where
  show (Quotient f) = show f

-- | Find the standard monomials of the quotient ring for the zero-dimensional ideal,
--   which are form the basis of it as k-vector space.
standardMonomials' :: (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r)
                   => Proxy ideal -> Maybe [Quotient r n ideal]
standardMonomials' pxy = do
    let basis = reflect pxy
        lms = map leadingMonomial basis
        dim = sLength $ head lms
        tests = zip (diag 1 0 dim) (diag 0 1 dim)
        mexp (val, test) = [ V.foldr (+) 0 $ V.zipWith (*) val lm0
                           | lm0 <- lms, let a = V.foldr (+) 0 $ V.zipWith (*) lm0 test, a == 0
                           ]
    degs <- mapM (minimum' . mexp) tests
    return [ Quotient ds | ds0 <- sequence $ map (enumFromTo 0) degs
           , let ds = toPolynomial (one, (fromList dim ds0))
           , ds `modPolynomial` basis == ds]

standardMonomials :: forall ideal r n. (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r)
                  => Maybe [Quotient r n ideal]
standardMonomials = standardMonomials' (Proxy :: Proxy ideal)

genQuotVars' :: forall n ideal r. (Reifies ideal [Polynomial r (S n)], IsPolynomial r (S n), Field r)
             => Proxy ideal -> [Quotient r (S n) ideal]
genQuotVars' pxy = map (modIdeal' pxy) $ genVars (sing :: SNat (S n))

genQuotVars :: forall n ideal r. (Reifies ideal [Polynomial r (S n)], IsPolynomial r (S n), Field r)
             => [Quotient r (S n) ideal]
genQuotVars = genQuotVars' (Proxy :: Proxy ideal)

minimum' :: Ord a => [a] -> Maybe a
minimum' [] = Nothing
minimum' xs = Just $ minimum xs

diag :: a -> a -> SNat n -> [V.Vector a n]
diag _ _ SZ = []
diag d _ (SS SZ) = [d :- Nil]
diag d z (SS n)  = (d :- V.unsafeFromList n (repeat z)) : map (z :-) (diag d z n)

-- | Polynomial modulo ideal.
modIdeal :: forall r n ideal. (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r)
           => Polynomial r n -> Quotient r n ideal
modIdeal = modIdeal' (Proxy :: Proxy ideal)

-- | Polynomial modulo ideal given by @Proxy@.
modIdeal' :: (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r)
          => Proxy ideal -> Polynomial r n -> Quotient r n ideal
modIdeal' pxy f = Quotient $ f `modPolynomial` reflect pxy

-- | Reifies the ideal at the type-level. The ideal can be recovered with 'reflect'.
reifyQuotient :: (Field r, IsPolynomial r n)
              => Ideal (Polynomial r n)
              -> (forall ideal. Reifies ideal [Polynomial r n] => Proxy ideal -> a)
              -> a
reifyQuotient ideal = reify (calcGroebnerBasis ideal)

-- | Computes polynomial modulo ideal.
withQuotient :: (Field r, IsPolynomial r n)
             => Ideal (Polynomial r n)
             -> (forall ideal. Reifies ideal [Polynomial r n] => Quotient r n ideal)
             -> Polynomial r n
withQuotient ideal v = reify (calcGroebnerBasis ideal) (quotRepr_ . asProxyOf v)

asProxyOf :: f s -> Proxy s -> f s
asProxyOf a _ = a

-- | Representative polynomial of given quotient polynomial.
quotRepr :: Quotient r n ideal -> Polynomial r n
quotRepr = quotRepr_

instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Additive (Quotient r n ideal) where
  f + g = Quotient $ quotRepr_ f + quotRepr_ g
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => LeftModule Natural (Quotient r n ideal) where
  n .* f = modIdeal $ n .* quotRepr_ f
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => RightModule Natural (Quotient r n ideal) where
  f *. n = modIdeal $ quotRepr_ f *. n
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Monoidal (Quotient r n ideal) where
  zero   = modIdeal zero
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => LeftModule Integer (Quotient r n ideal) where
  n .* f = modIdeal $ n .* quotRepr_ f
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => RightModule Integer (Quotient r n ideal) where
  f *. n = modIdeal $ quotRepr_ f *. n
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Group (Quotient r n ideal) where
  negate f = Quotient $ negate $ quotRepr_ f
  f - g    = Quotient $ quotRepr_ f - quotRepr_ g
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Abelian (Quotient r n ideal) where
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Multiplicative (Quotient r n ideal) where
  f * g = modIdeal $ quotRepr_ f * quotRepr_ g
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Semiring (Quotient r n ideal) where
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Unital (Quotient r n ideal) where
  one   = modIdeal one
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Rig (Quotient r n ideal) where
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Ring (Quotient r n ideal) where
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => LeftModule (Scalar r) (Quotient r n ideal) where
  r .* f = Quotient $ r .* quotRepr_ f
instance (Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => RightModule (Scalar r) (Quotient r n ideal) where
  f *. r = Quotient $ quotRepr_ f *. r

instance (Num r, Reifies ideal [Polynomial r n], IsPolynomial r n, Field r) => Num (Quotient r n ideal) where
  (+) = (NA.+)
  (*) = (NA.*)
  fromInteger = modIdeal . P.fromInteger
  signum = modIdeal . signum . quotRepr_
  abs    = id
  negate = modIdeal . negate . quotRepr_
