{-# LANGUAGE BangPatterns, CPP, DataKinds, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiWayIf, OverloadedLabels, ScopedTypeVariables        #-}
module Algebra.Field.RationalFunction
       ( RationalFunction
       , evalRationalFunctionOnField
       , evalRationalFunction
       , fromPolynomial
       , variable, diffRF, taylor, taylorCoeff
       )where
import           Algebra.Prelude.Core
import           Algebra.Ring.Polynomial.Univariate (Unipol)
import qualified Numeric.Field.Fraction             as NA

-- | Unary rational field over a field @k@.
--
--  With @OverloadedLabels@ extension, you can use @'IsLabel'@ instance
--  to write variable as @#x@; for example @1 / (#x - 2) ^ n@.
newtype RationalFunction k = RF (Fraction (Unipol k))
                             deriving (Eq, Ord, Num, Division, Semiring, Ring, Rig,
                                       Additive, Multiplicative, Unital,
                                       Monoidal, Commutative, Group, Abelian,
                                       LeftModule Integer, RightModule Integer,
                                       LeftModule Natural, RightModule Natural,
                                       GCDDomain, PID, UFD, Euclidean, IntegralDomain,
                                       ZeroProductSemiring, DecidableAssociates,
                                       DecidableUnits, DecidableZero, UnitNormalForm
                                      )

instance (CoeffRing k, PrettyCoeff k) => Show (RationalFunction k) where
  showsPrec d (RF r) = showParen (d > 10) $
    showsPrec 11 (numerator r) . showString " / " . showsPrec 11 (denominator r)

instance (Field k, Eq k) => IsLabel "x" (RationalFunction k) where
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 802
  fromLabel 
#else
  fromLabel _
#endif
    = RF (#x NA.% one)

evalRationalFunctionOnField :: (Eq k, Field k) => RationalFunction k -> k -> k
evalRationalFunctionOnField rat k =
  let d = evalRationalFunction rat k
  in numerator d / denominator d

fromPolynomial :: (IsOrderedPolynomial poly, Arity poly ~ 1, Field (Coefficient poly))
               => poly -> RationalFunction (Coefficient poly)
fromPolynomial = RF . (NA.% one) . polynomial' . terms'

variable :: (Eq k, Field k) => RationalFunction k
variable = #x

evalRationalFunction :: (GCDDomain r, CoeffRing r) => RationalFunction r -> r -> Fraction r
evalRationalFunction (RF rat) k =
  let p = liftMapCoeff (const k) $ numerator rat
      q = liftMapCoeff (const k) $ denominator rat
  in p NA.% q

-- | Formal differentiation
diffRF :: (Eq k, Field k) => RationalFunction k -> RationalFunction k
diffRF (RF pq) =
  let f = numerator pq
      g = denominator pq
  in RF $ (g * diff 0 f - diff 0 g * f) NA.% (g ^ 2)

-- | Formal Taylor expansion
taylor :: (Eq k, Field k) => RationalFunction k -> [k]
taylor = go 0 one
  where
    go !n !acc f =
      let acc' = acc / fromInteger' (n + 1)
      in evalRationalFunctionOnField f zero * acc : go (n + 1) acc' (diffRF f)

taylorCoeff :: (Eq k, Field k) => Int -> RationalFunction k -> k
taylorCoeff n rf =
    evalRationalFunctionOnField (foldr (.) id (replicate n diffRF) rf) zero
  / fromInteger' (product [1..toInteger n])
