{-# LANGUAGE GeneralizedNewtypeDeriving, PartialTypeSignatures           #-}
{-# LANGUAGE PatternSynonyms, RankNTypes, ScopedTypeVariables            #-}
{-# LANGUAGE StandaloneDeriving, TemplateHaskell, TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators, ViewPatterns                                 #-}
{-# OPTIONS_GHC -funbox-strict-fields -fplugin GHC.TypeLits.Presburger   #-}
module Algebra.Ring.Polynomial.Recursive
       {-(RecPoly, pattern RecPoly, toRecPoly, runRecPoly)-} where
import           Algebra.Prelude
import           Algebra.Algorithms.Groebner 
import           Control.Lens              ((&),both,ifoldMap, (%~), _Unwrapping')
import qualified Data.Map                  as M
import           Data.Type.Natural.Builtin
import qualified Numeric.Algebra as NA
import           Data.Type.Ordinal.Builtin
import qualified Data.Sized as SV
import qualified Numeric.Algebra           as A
import qualified Prelude                   as P

data RecPoly k n where
  RecPolyZ :: !k -> RecPoly k 0
  RecPolyS :: KnownNat n => !(Unipol (RecPoly k n)) -> RecPoly k (Succ n)

instance (CoeffRing k, KnownNat n) => Additive (RecPoly k n) where
  (RecPolyS f) + (RecPolyS g) = RecPolyS $ f + g
  (RecPolyZ f) + (RecPolyZ g) = RecPolyZ $ f + g
  _            + _            = error "Bug in GHC"
  {-# INLINE (+) #-}
      
instance (CoeffRing k, KnownNat n) => LeftModule Natural (RecPoly k n) where
  n .* RecPolyZ f = RecPolyZ $ n .* f
  n .* RecPolyS f = RecPolyS $ n .* f
  {-# INLINE (.*) #-}

instance (CoeffRing k, KnownNat n) => RightModule Natural (RecPoly k n) where
  RecPolyZ f *. n = RecPolyZ $ f *. n 
  RecPolyS f *. n = RecPolyS $ f *. n 
  {-# INLINE (*.) #-}

instance (CoeffRing k, KnownNat n) => LeftModule Integer (RecPoly k n) where
  n .* RecPolyZ f = RecPolyZ $ n .* f
  n .* RecPolyS f = RecPolyS $ n .* f
  {-# INLINE (.*) #-}

instance (CoeffRing k, KnownNat n) => RightModule Integer (RecPoly k n) where
  RecPolyZ f *. n = RecPolyZ $ f *. n 
  RecPolyS f *. n = RecPolyS $ f *. n 
  {-# INLINE (*.) #-}

instance (CoeffRing k, KnownNat n) => LeftModule (Scalar k) (RecPoly k n) where
  Scalar n .* RecPolyZ f = RecPolyZ $ n * f
  n        .* RecPolyS f = RecPolyS $ mapCoeff' (n .*) f
  {-# INLINE (.*) #-}

instance (CoeffRing k, KnownNat n) => RightModule (Scalar k) (RecPoly k n) where
  RecPolyZ f *. Scalar n = RecPolyZ $ f *  n
  RecPolyS f *. n        = RecPolyS $ mapCoeff' (*. n) f
  {-# INLINE (*.) #-}

instance (CoeffRing k, KnownNat n) => Monoidal (RecPoly k n) where
  zero = case sing :: Sing n of
      Zero -> RecPolyZ zero
      Succ n -> withKnownNat n $ RecPolyS zero
      _ -> error "Could not happen"
  {-# INLINE zero #-}

instance (CoeffRing k, KnownNat n) => DecidableZero (RecPoly k n) where
  isZero (RecPolyZ r) = isZero r
  isZero (RecPolyS f) = withKnownNat (sArity f) $ isZero f
  {-# INLINE isZero #-}

instance (CoeffRing k, KnownNat n) => Eq (RecPoly k n) where
  (RecPolyZ r) == (RecPolyZ q) = r == q
  (RecPolyS r) == (RecPolyS q) = r == q
  _ == _ = error "Cannot happen!"
  {-# INLINE (==) #-}

instance (CoeffRing k) => Multiplicative (RecPoly k n) where
  (RecPolyS f) * (RecPolyS g) = RecPolyS $ f * g
  (RecPolyZ f) * (RecPolyZ g) = RecPolyZ $ f * g
  _            * _            = error "Bug in GHC"
  {-# INLINE (*) #-}

instance (CoeffRing k) => Commutative (RecPoly k n)
instance (CoeffRing k, KnownNat n) => Group (RecPoly k n) where
  (RecPolyS f) - (RecPolyS g) = RecPolyS $ f - g
  (RecPolyZ f) - (RecPolyZ g) = RecPolyZ $ f - g
  _            - _            = error "Bug in GHC"
  {-# INLINE (-) #-}

  negate (RecPolyS f) = RecPolyS $ negate f
  negate (RecPolyZ f) = RecPolyZ $ negate f
  {-# INLINE negate #-}

instance (CoeffRing k, KnownNat n) => Ring (RecPoly k n) where
  fromInteger n = case sing :: Sing n of
    Zero -> RecPolyZ $ NA.fromInteger n
    Succ m -> withKnownNat m $ RecPolyS $ NA.fromInteger n
    _ -> error "Could not happen"
  {-# INLINE fromInteger #-}

instance (CoeffRing k, KnownNat n) => Rig (RecPoly k n) where
  fromNatural n = case sing :: Sing n of
      Zero -> RecPolyZ $ NA.fromNatural n
      Succ m -> withKnownNat m $ RecPolyS $ NA.fromNatural n
      _ -> error "Could not happen"
  {-# INLINE fromNatural #-}
  
instance (CoeffRing k, KnownNat n) => Semiring (RecPoly k n)
instance (CoeffRing k, KnownNat n) => Unital (RecPoly k n) where
  one =
    case sing :: Sing n of
      Zero -> RecPolyZ one
      Succ n -> withKnownNat n $ RecPolyS one
      _ -> error "Could not happen"
  {-# INLINE one #-}

instance (CoeffRing k, KnownNat n) => Abelian (RecPoly k n)
instance (CoeffRing k, KnownNat n) => IsPolynomial (RecPoly k n) where
  type Arity (RecPoly k n) = n
  type Coefficient (RecPoly k n) = k
  sArity _ = sing
  var o =
    case zeroOrSucc (sing :: Sing n) of
      IsZero   -> absurdOrd o
      IsSucc m -> withKnownNat m $ withSingI (sToPeano m) $ 
                  case o of
                    OS n -> RecPolyS $ injectCoeff (var n)
                    _    -> RecPolyS #x
  fromMonomial mon =
    case mon of
      n :< ls -> withKnownNat (SV.sLength ls) $ RecPolyS $ #x ^ fromIntegral n * injectCoeff (fromMonomial ls)
      _ -> one
  injectCoeff k =
    case zeroOrSucc (sing :: Sing n) of
      IsZero -> RecPolyZ k
      IsSucc (m :: SNat m) ->
        withKnownNat m $ RecPolyS $ injectCoeff (injectCoeff k :: RecPoly k m)
  terms' (RecPolyZ r) = M.singleton (fromList sZero []) r
  terms' (RecPolyS f) =
    ifoldMap (M.mapKeys . (:<) . (sIndex 0)) $
    fmap terms' $ terms' f
  liftMap _ (RecPolyZ q) = Scalar q .* one
  liftMap f (RecPolyS q) =
    substWith (\g r -> liftMap (f . OS) g * r) (singleton $ f 0) q

instance (CoeffRing k, KnownNat n) => ZeroProductSemiring (RecPoly k n)

instance (CoeffRing k, Field k) => Division (RecPoly k 0)  where
  recip (RecPolyZ r) = RecPolyZ $ recip r

instance (CoeffRing k, Field k) => PID (RecPoly k 0)
instance (CoeffRing k, Field k) => PID (RecPoly k 1)
instance (CoeffRing k, Field k, KnownNat n) => UFD (RecPoly k n)
instance (CoeffRing k, Field k, KnownNat n) => GCDDomain (RecPoly k n) where
  gcd f g = gcdPolynomial f g
  lcm f g = lcmPolynomial f g
instance (CoeffRing k, Field k, KnownNat n) => IntegralDomain (RecPoly k n) where
  f `divides` g = isZero $ f `modPolynomial` [g]
  maybeQuot f g =
    let ([q], r) = f `divModPolynomial` [g]
    in if isZero r then Just (snd q) else Nothing
instance (CoeffRing k, Field k) => Euclidean (RecPoly k 0)
instance (CoeffRing k, Field k) => Euclidean (RecPoly k 1) where
  degree f | isZero f = Nothing
           | otherwise = Just $ totalDegree' f
  divide (RecPolyS f) (RecPolyS g) =
    withRefl (succInj' (sing :: Sing 0) (sArity f) Refl) $
    divide f g & both %~ RecPolyS

instance (CoeffRing k, UnitNormalForm k, KnownNat n) => Num (RecPoly k n) where
  fromInteger = unwrapAlgebra . P.fromInteger
  (+) = (A.+)
  (-) = (A.-)
  negate = _Unwrapping' WrapAlgebra %~ P.negate
  (*) = (A.*)
  abs = _Unwrapping' WrapAlgebra %~ abs
  signum = _Unwrapping' WrapAlgebra %~ signum

instance (CoeffRing k, KnownNat n) => IsOrderedPolynomial (RecPoly k n) where
  type MOrder (RecPoly k n) = Lex
  leadingTerm (RecPolyZ r) = (r, one)
  leadingTerm (RecPolyS u) =
    let (k , OrderedMonomial ind) = leadingTerm u
        (c, OrderedMonomial ts) = leadingTerm k
    in case ind of
      n :< NilL -> (c, OrderedMonomial $ n :< ts)
      _ -> error "bug in ghc"

instance (CoeffRing k, DecidableUnits k, KnownNat n) => DecidableUnits (RecPoly k n) where
  recipUnit = recipUnitDefault
  isUnit = isUnitDefault

instance (CoeffRing k, UnitNormalForm k, KnownNat n) => DecidableAssociates (RecPoly k n) where
  isAssociate = isAssociateDefault

instance (CoeffRing k, UnitNormalForm k, KnownNat n) => UnitNormalForm (RecPoly k n) where
  splitUnit = splitUnitDefault

instance (KnownNat n, CoeffRing r, PrettyCoeff r)
       => Show (RecPoly r n) where
  showsPrec = showsPolynomialWith $ generate sing (\i -> "X_" ++ show (fromEnum i))
