{-# LANGUAGE GeneralizedNewtypeDeriving, PartialTypeSignatures           #-}
{-# LANGUAGE PatternSynonyms, RankNTypes, ScopedTypeVariables            #-}
{-# LANGUAGE StandaloneDeriving, TemplateHaskell, TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators, ViewPatterns                                 #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Algebra.Ring.Polynomial.Recursive
       (RecPoly, pattern RecPoly, toRecPoly, runRecPoly) where
import           Algebra.Prelude
import           Algebra.Algorithms.Groebner 
import           Control.Lens              ((&),both,ifoldMap, (%~), _Unwrapping')
import qualified Data.Coerce               as C
import qualified Data.Map                  as M
import qualified Data.Type.Natural         as PN
import           Data.Type.Natural.Builtin
import           Data.Type.Ordinal.Builtin
import qualified Data.Sized as SV
import qualified Numeric.Algebra           as A
import qualified Prelude                   as P

data family RecPoly' k (n :: PN.Nat)
newtype instance RecPoly' k 'PN.Z where
  RecPolyZ :: {runRecPolyZ :: k } -> RecPoly' k 'PN.Z

newtype instance RecPoly' k ('PN.S n) where
  RecPolyS :: {runRecPolyS :: Unipol (RecPoly' k n)} -> RecPoly' k ('PN.S n)

newtype RecPoly k (n :: Nat) = RecPoly_ { runRecPoly_ :: RecPoly' k (ToPeano n) }

type family UnwrapRecPoly k n where
  UnwrapRecPoly k 0 = k
  UnwrapRecPoly k n = Unipol (RecPoly k (n-1))

runRecPoly :: forall r n. (KnownNat n) => RecPoly r (Succ n) -> Unipol (RecPoly r n)
runRecPoly (RecPoly_ wf) =
  withRefl (toPeanoSuccCong  (sing :: SNat n)) $ C.coerce wf

toRecPoly :: forall r n. (CoeffRing r, KnownNat n) => Unipol (RecPoly r n) -> RecPoly r (Succ n)
toRecPoly =
  let sn = (sing :: SNat n)
  in withRefl (toPeanoSuccCong sn) $
     withSingI (sToPeano sn) $
     RecPoly_ . RecPolyS . mapCoeffUnipol C.coerce

pattern RecPoly :: forall r (n :: Nat). (CoeffRing r, KnownNat n)
                => KnownNat n
                => Unipol (RecPoly r n) -> RecPoly r (Succ n)
pattern RecPoly f <- (runRecPoly -> f) where
  RecPoly f = toRecPoly f

newtype Binary k n = Binary { runBinary :: RecPoly' k n -> RecPoly' k n -> RecPoly' k n }

eqlRecP :: forall k n. (CoeffRing k, SingI n) => RecPoly' k n -> RecPoly' k n -> Bool
eqlRecP = case zeroOrSucc (sing :: Sing n) of
  IsZero -> \ (RecPolyZ p) (RecPolyZ q) -> p == q
  IsSucc n -> withSingI n $ \(RecPolyS u) (RecPolyS v) -> u == v
{-# INLINE eqlRecP #-}

instance (CoeffRing k , SingI n) => Eq (RecPoly' k n) where
  (==) = eqlRecP

addRecP :: forall k n. (CoeffRing k, SingI n) => RecPoly' k n -> RecPoly' k n -> RecPoly' k n
addRecP = case zeroOrSucc (sing :: Sing n) of
  IsZero -> \ (RecPolyZ p) (RecPolyZ q) -> RecPolyZ (p + q)
  IsSucc n -> withSingI n $ \(RecPolyS u) (RecPolyS v) ->
      RecPolyS $ u + v

leftModNat :: forall k n. (CoeffRing k, SingI n) => Natural -> RecPoly' k n -> RecPoly' k n
leftModNat a = case zeroOrSucc (sing :: Sing n) of
  IsZero -> \ (RecPolyZ p) -> RecPolyZ (a .* p)
  IsSucc n -> withSingI n $ \(RecPolyS u) ->
      RecPolyS $ a .* u
{-# INLINE leftModNat #-}

leftModScalar :: forall k n. (CoeffRing k, SingI n) => Scalar k -> RecPoly' k n -> RecPoly' k n
leftModScalar a = case zeroOrSucc (sing :: Sing n) of
  IsZero -> \ (RecPolyZ p) -> RecPolyZ (runScalar a * p)
  IsSucc n -> withSingI n $ \(RecPolyS u) ->
      RecPolyS $ mapCoeff' (a .*) u
{-# INLINE leftModScalar #-}

rightModScalar :: forall k n. (CoeffRing k, SingI n) => RecPoly' k n -> Scalar k -> RecPoly' k n
rightModScalar = flip $ \ a -> case zeroOrSucc (sing :: Sing n) of
  IsZero -> \ (RecPolyZ p) -> RecPolyZ (p * runScalar a)
  IsSucc n -> withSingI n $ \(RecPolyS u) ->
      RecPolyS $ mapCoeff' (*. a) u
{-# INLINE rightModScalar #-}

rightModNat :: forall k n. (CoeffRing k, SingI n) => RecPoly' k n -> Natural -> RecPoly' k n
rightModNat = flip $ \a -> case zeroOrSucc (sing :: Sing n) of
  IsZero -> \ (RecPolyZ p) -> RecPolyZ (p *. a)
  IsSucc n -> withSingI n $ \(RecPolyS u) ->
      RecPolyS $ u *. a
{-# INLINE rightModNat #-}

leftModInt :: forall k n. (CoeffRing k, SingI n) => Integer -> RecPoly' k n -> RecPoly' k n
leftModInt a = case zeroOrSucc (sing :: Sing n) of
  IsZero -> \ (RecPolyZ p) -> RecPolyZ (a .* p)
  IsSucc n -> withSingI n $ \(RecPolyS u) ->
      RecPolyS $ a .* u
{-# INLINE leftModInt #-}

rightModInt :: forall k n. (CoeffRing k, SingI n) => RecPoly' k n -> Integer -> RecPoly' k n
rightModInt = flip $ \a -> case zeroOrSucc (sing :: Sing n) of
  IsZero -> \ (RecPolyZ p) -> RecPolyZ (p *. a)
  IsSucc n -> withSingI n $ \(RecPolyS u) ->
      RecPolyS $ u *. a
{-# INLINE rightModInt #-}

instance (CoeffRing k, SingI n) => Additive (RecPoly' k n) where
  (+) = addRecP
  {-# INLINE (+) #-}

isZeroP :: forall k n. (CoeffRing k, SingI n) => RecPoly' k n -> Bool
isZeroP u =
  case zeroOrSucc (sing :: Sing n) of
    IsZero -> case u of
      RecPolyZ r -> isZero r
    IsSucc m -> withSingI m $ case u of
     RecPolyS r -> isZero r
{-# INLINE isZeroP #-}

zeroP :: forall k n. (CoeffRing k, SingI n) => RecPoly' k n
zeroP =
  case zeroOrSucc (sing :: Sing n) of
    IsZero -> RecPolyZ zero
    IsSucc m -> withSingI m $ RecPolyS zero
{-# INLINE zeroP #-}

instance (CoeffRing k, SingI n) => Monoidal (RecPoly' k n) where
  zero = zeroP
  {-# INLINE zero #-}

instance (CoeffRing k, SingI n) => LeftModule Natural (RecPoly' k n) where
  (.*) = leftModNat
  {-# INLINE (.*) #-}

instance (CoeffRing k, SingI n) => RightModule Natural (RecPoly' k n) where
  (*.) = rightModNat
  {-# INLINE (*.) #-}

instance (CoeffRing k, SingI n) => LeftModule (Scalar k) (RecPoly' k n) where
  (.*) = leftModScalar
  {-# INLINE (.*) #-}

instance (CoeffRing k, SingI n) => RightModule (Scalar k) (RecPoly' k n) where
  (*.) = rightModScalar
  {-# INLINE (*.) #-}

instance (CoeffRing k, SingI n) => LeftModule Integer (RecPoly' k n) where
  (.*) = leftModInt
  {-# INLINE (.*) #-}

instance (CoeffRing k, SingI n) => RightModule Integer (RecPoly' k n) where
  (*.) = rightModInt
  {-# INLINE (*.) #-}

instance (CoeffRing k, SingI n) => DecidableZero (RecPoly' k n) where
  isZero = isZeroP
  {-# INLINE isZero #-}

instance (CoeffRing k, SingI n) => Abelian (RecPoly' k n)

minRecP :: forall k n. (CoeffRing k, SingI n) => RecPoly' k n -> RecPoly' k n -> RecPoly' k n
minRecP = case zeroOrSucc (sing :: Sing n) of
  IsZero -> \ (RecPolyZ p) (RecPolyZ q) -> RecPolyZ (p - q)
  IsSucc n -> withSingI n $ \(RecPolyS u) (RecPolyS v) ->
      RecPolyS $ u - v
{-# INLINE minRecP #-}

negRecP :: forall k n. (CoeffRing k, SingI n) => RecPoly' k n -> RecPoly' k n
negRecP = case zeroOrSucc (sing :: Sing n) of
  IsZero -> \ (RecPolyZ p) -> RecPolyZ (negate p)
  IsSucc n -> withSingI n $ \(RecPolyS u) ->
      RecPolyS $ negate u
{-# INLINE negRecP #-}

instance (CoeffRing k, SingI n) => Group (RecPoly' k n) where
  (-) = minRecP
  negate = negRecP

mulRecP :: forall k n. (CoeffRing k, SingI n) => RecPoly' k n -> RecPoly' k n -> RecPoly' k n
mulRecP = case zeroOrSucc (sing :: Sing n) of
  IsZero -> \ (RecPolyZ p) (RecPolyZ q) -> RecPolyZ (p * q)
  IsSucc n -> withSingI n $ \(RecPolyS u) (RecPolyS v) ->
      RecPolyS $ u * v
{-# INLINE mulRecP #-}

instance (CoeffRing k, SingI n) => Multiplicative (RecPoly' k n) where
  (*) = mulRecP

fromIntegerP :: forall k n. (CoeffRing k, SingI n) => Integer -> RecPoly' k n
fromIntegerP i =
  case zeroOrSucc (sing :: Sing n) of
    IsZero -> RecPolyZ $ A.fromInteger i
    IsSucc m -> withSingI m $ RecPolyS $ A.fromInteger i
{-# INLINE fromIntegerP #-}

fromNaturalP :: forall k n. (CoeffRing k, SingI n) => Natural -> RecPoly' k n
fromNaturalP i =
  case zeroOrSucc (sing :: Sing n) of
    IsZero -> RecPolyZ $ A.fromNatural i
    IsSucc m -> withSingI m $ RecPolyS $ A.fromNatural i
{-# INLINE fromNaturalP #-}

instance (CoeffRing k, SingI n) => Semiring (RecPoly' k n)
instance (CoeffRing k, SingI n) => Ring (RecPoly' k n) where
  fromInteger = fromIntegerP

instance (CoeffRing k, SingI n) => Rig (RecPoly' k n) where
  fromNatural = fromNaturalP

oneP :: forall k n. (CoeffRing k, SingI n) => RecPoly' k n
oneP =
  case zeroOrSucc (sing :: Sing n) of
    IsZero -> RecPolyZ one
    IsSucc m -> withSingI m $ RecPolyS one
{-# INLINE oneP #-}

instance (CoeffRing k, SingI n) => Unital (RecPoly' k n) where
  one = oneP
  {-# INLINE one #-}

instance (CoeffRing k, SingI n) => Commutative (RecPoly' k n)

instance (CoeffRing k, Field k) => Division (RecPoly' k 'PN.Z)  where
  recip (RecPolyZ k) = RecPolyZ $ recip k
  (RecPolyZ k) / (RecPolyZ l) = RecPolyZ $ k / l
  (RecPolyZ k) ^ n = RecPolyZ $ k A.^ n

instance (CoeffRing k, KnownNat n) => Additive (RecPoly k n) where
  (+) = withSingI (sToPeano (sing :: Sing n)) $ C.coerce addRecP

instance (CoeffRing k, KnownNat n) => Eq (RecPoly k n) where
  (==) = withSingI (sToPeano (sing :: Sing n)) $ C.coerce eqlRecP

instance (CoeffRing k, KnownNat n) => Monoidal (RecPoly k n) where
  zero = withSingI (sToPeano (sing :: Sing n)) $ C.coerce zeroP

instance (CoeffRing k, KnownNat n) => LeftModule Natural (RecPoly k n) where
  (.*) = withSingI (sToPeano (sing :: Sing n)) $ C.coerce leftModNat
  {-# INLINE (.*) #-}

instance (CoeffRing k, KnownNat n) => RightModule Natural (RecPoly k n) where
  (*.) = withSingI (sToPeano (sing :: Sing n)) $ C.coerce rightModNat
  {-# INLINE (*.) #-}

instance (CoeffRing k, KnownNat n) => LeftModule Integer (RecPoly k n) where
  (.*) = withSingI (sToPeano (sing :: Sing n)) $ C.coerce leftModInt
  {-# INLINE (.*) #-}

instance (CoeffRing k, KnownNat n) => RightModule Integer (RecPoly k n) where
  (*.) = withSingI (sToPeano (sing :: Sing n)) $ C.coerce rightModInt
  {-# INLINE (*.) #-}

instance (CoeffRing k, KnownNat n) => LeftModule (Scalar k) (RecPoly k n) where
  (.*) = withSingI (sToPeano (sing :: Sing n)) $ C.coerce leftModScalar
  {-# INLINE (.*) #-}

instance (CoeffRing k, KnownNat n) => RightModule (Scalar k) (RecPoly k n) where
  (*.) = withSingI (sToPeano (sing :: Sing n)) $ C.coerce rightModScalar
  {-# INLINE (*.) #-}

instance (CoeffRing k, KnownNat n) => DecidableZero (RecPoly k n) where
  isZero = withSingI (sToPeano (sing :: Sing n)) $ C.coerce isZeroP
  {-# INLINE isZero #-}

instance (CoeffRing k, KnownNat n) => Abelian (RecPoly k n)

instance (CoeffRing k, KnownNat n) => Group (RecPoly k n) where
  (-) = withSingI (sToPeano (sing :: Sing n)) $ C.coerce minRecP
  negate = withSingI (sToPeano (sing :: Sing n)) $ C.coerce negRecP


instance (CoeffRing k, KnownNat n) => Multiplicative (RecPoly k n) where
  (*) = withSingI (sToPeano (sing :: Sing n)) $ C.coerce mulRecP

instance (CoeffRing k, KnownNat n) => Semiring (RecPoly k n)
instance (CoeffRing k, KnownNat n) => Ring (RecPoly k n) where
  fromInteger = withSingI (sToPeano (sing :: Sing n)) $ C.coerce fromIntegerP

instance (CoeffRing k, KnownNat n) => Rig (RecPoly k n) where
  fromNatural = withSingI (sToPeano (sing :: Sing n)) $ C.coerce fromNaturalP

instance (CoeffRing k, KnownNat n) => Unital (RecPoly k n) where
  one = withSingI (sToPeano (sing :: Sing n)) $ C.coerce oneP
  {-# INLINE one #-}

instance (CoeffRing k, KnownNat n) => Commutative (RecPoly k n)

instance (CoeffRing k, KnownNat n) => ZeroProductSemiring (RecPoly k n)

instance (CoeffRing k, Field k) => Division (RecPoly k 0)  where
  recip = C.coerce (recip :: RecPoly' k 'PN.Z -> RecPoly' k 'PN.Z)

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
  divide f g = divide (runRecPoly f) (runRecPoly g) & both %~ RecPoly

instance (CoeffRing k, UnitNormalForm k, KnownNat n) => Num (RecPoly k n) where
  fromInteger = unwrapAlgebra . P.fromInteger
  (+) = (A.+)
  (-) = (A.-)
  negate = _Unwrapping' WrapAlgebra %~ P.negate
  (*) = (A.*)
  abs = _Unwrapping' WrapAlgebra %~ abs
  signum = _Unwrapping' WrapAlgebra %~ signum

instance (CoeffRing k, KnownNat n) => IsPolynomial (RecPoly k n) where
  type Coefficient (RecPoly k n) = k
  type Arity (RecPoly k n) = n
  sArity _ = sing
  var o =
    case zeroOrSucc (sing :: Sing n) of
      IsZero   -> absurdOrd o
      IsSucc m -> withKnownNat m $ withSingI (sToPeano m) $ 
                  case o of
                    OS n -> RecPoly $ injectCoeff (var n)
                    _    -> RecPoly #x
  fromMonomial mon =
    case mon of
      n :< ls -> withKnownNat (SV.sLength ls) $ RecPoly $ #x ^ fromIntegral n * injectCoeff (fromMonomial ls)
      _ -> one
  injectCoeff k =
    case zeroOrSucc (sing :: Sing n) of
      IsZero -> RecPoly_ $ RecPolyZ k
      IsSucc (m :: SNat m) ->
        withKnownNat m $ RecPoly $ injectCoeff (injectCoeff k :: RecPoly k m)
  terms' f =
    case zeroOrSucc (sing :: Sing n) of
      IsZero   -> M.fromList [(fromList sZero [], C.coerce $ runRecPoly_ f)]
      IsSucc m -> withKnownNat m $ ifoldMap (M.mapKeys . (:<) . (sIndex 0)) $
                  fmap terms' $ terms' $ runRecPoly f
  liftMap f (RecPoly_ p) =
    case zeroOrSucc (sing :: Sing n) of
      IsZero -> case p of  RecPolyZ q -> Scalar q .* one
      IsSucc (m :: Sing m) ->
        withKnownNat m $ withSingI (sToPeano m) $ withRefl (toPeanoSuccCong m) $
        case p of
          RecPolyS q -> substWith (\g r -> liftMap (f . OS) (RecPoly_ g) * r) (singleton $ f 0) q

instance (CoeffRing k, KnownNat n) => IsOrderedPolynomial (RecPoly k n) where
  type MOrder (RecPoly k n) = Lex
  leadingTerm f =
    case zeroOrSucc (sing :: SNat n) of
      IsZero -> (C.coerce f, one)
      IsSucc m ->
        withKnownNat m $ withSingI (sToPeano m) $ withRefl (toPeanoSuccCong m) $
        let u = runRecPolyS $ runRecPoly_ f
        in case leadingTerm u of
          (k, OrderedMonomial ind) ->
            let n = sIndex 0 ind
                (c, OrderedMonomial ts) = leadingTerm $ RecPoly_ k
            in (c, OrderedMonomial $ n :< ts)

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
