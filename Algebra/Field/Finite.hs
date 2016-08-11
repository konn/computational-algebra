{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances               #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses, PolyKinds #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, TypeFamilies                #-}
{-# LANGUAGE UndecidableInstances                                         #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Algebra.Field.Finite (F(), naturalRepr, reifyPrimeField, withPrimeField,
                             modNat, modNat', modRat, modRat', FiniteField(..), order) where
import Algebra.Algorithms.PrimeTest
import Algebra.Prelude               hiding (pow)
import Algebra.Ring.Polynomial.Class (PrettyCoeff (..), ShowSCoeff (..))

import           Control.DeepSeq                       (NFData (..))
import           Control.Monad.Random                  (uniform)
import           Control.Monad.Random                  (runRand)
import           Control.Monad.Random                  (Random (..))
import           Data.Maybe                            (fromMaybe)
import qualified Data.Ratio                            as R
import           Data.Reflection
import           GHC.TypeLits                          (KnownNat)
import           Numeric.Algebra                       (Field)
import           Numeric.Algebra                       (char)
import           Numeric.Algebra                       (Natural)
import qualified Numeric.Algebra                       as NA
import           Numeric.Algebra.Unital.UnitNormalForm
import           Numeric.Decidable.Associates
import           Numeric.Decidable.Units
import           Numeric.Decidable.Zero
import           Numeric.Domain.Integral
import           Numeric.Rig.Characteristic            (Characteristic)
import           Numeric.Semiring.ZeroProduct          (ZeroProductSemiring)
import qualified Prelude                               as P

-- | Prime field of characteristic @p@.
--   @p@ should be prime, and not statically checked.
newtype F (p :: k) = F { runF :: Integer }
                   deriving (NFData)

naturalRepr :: F p -> Integer
naturalRepr = runF

instance Reifies (p :: k) Integer => Show (F p) where
  showsPrec d n@(F p) = showsPrec d (p `rem` reflect n)

instance Reifies (p :: k) Integer => PrettyCoeff (F p) where
  showsCoeff d (F p) =
    if p == 0
    then Vanished
    else if p == 1
         then OneCoeff
         else Positive $ showsPrec d p

modNat :: Reifies (p :: k) Integer => Integer -> F p
modNat = modNat' Proxy
{-# INLINE modNat #-}

modNat' :: forall proxy (p :: k). Reifies p Integer =>  proxy (F p) -> Integer -> F p
modNat' _ i =
  let p = reflect (Proxy :: Proxy p)
  in F (i `rem` p)
{-# INLINE modNat' #-}

reifyPrimeField :: Integer -> (forall p. KnownNat p => Proxy (F p) -> a) -> a
reifyPrimeField p f = reifyNat p (\pxy -> f (proxyF pxy))

withPrimeField :: Integer -> (forall p. KnownNat p => F p) -> Integer
withPrimeField p f = reifyPrimeField p $ runF . asProxyTypeOf f

proxyF :: Proxy (a :: k) -> Proxy (F a)
proxyF Proxy = Proxy

-- instance Reifies p Int => Noetherian (F p)

instance Eq (F p) where
  F n == F m = n == m

instance Reifies p Integer => Normed (F p) where
  type Norm (F p) = Integer
  norm fp@(F p) = p where _ = reflect fp
  liftNorm = modNat

instance Reifies p Integer => P.Num (F p) where
  fromInteger n = modNat $ fromInteger n
  {-# INLINE fromInteger #-}

  F a + F b = modNat $ a + b
  {-# INLINE (+) #-}

  F a - F b = modNat $ a - b
  {-# INLINE (-) #-}

  negate c = modNat $ reflect c - runF c
  {-# INLINE negate #-}

  a * b = modNat $ runF a * runF b
  {-# INLINE (*) #-}

  abs = id
  signum (F n) = modNat $ P.signum n

pow :: (P.Integral a1, Reifies p Integer) => F p -> a1 -> F p
pow a n = modNat $ modPow (runF a) (reflect a) n

instance Reifies p Integer => NA.Additive (F p) where
  (+) = (P.+)

instance Reifies p Integer => NA.Multiplicative (F p) where
  (*) = (P.*)
  pow1p n p = pow n (p P.+ 1)

instance Reifies p Integer => NA.Monoidal (F p) where
  zero = 0

instance Reifies p Integer => NA.LeftModule Natural (F p) where
  n .* p = fromIntegral n * p

instance Reifies p Integer => NA.RightModule Natural (F p) where
  p *. n = fromIntegral n * p

instance Reifies p Integer => NA.LeftModule Integer (F p) where
  n .* p = fromIntegral n * p

instance Reifies p Integer => NA.RightModule Integer (F p) where
  p *. n = fromIntegral n * p

instance Reifies p Integer => NA.Group (F p) where
  (-) = (-)
  negate = negate

instance Reifies p Integer => NA.Abelian (F p)

instance Reifies p Integer => NA.Semiring (F p)

instance Reifies p Integer => NA.Rig (F p) where
  fromNatural = fromInteger . P.toInteger

instance Reifies p Integer => NA.Ring (F p) where
  fromInteger = fromInteger

instance Reifies p Integer => NA.DecidableZero (F p) where
  isZero (F p) = p == 0

instance Reifies p Integer => NA.Unital (F p) where
  one = 1
  pow = pow

instance Reifies p Integer => DecidableUnits (F p) where
  isUnit n = gcd (runF n) (reflect n) == 1
  recipUnit n =
    let p = fromIntegral $ reflect n
        (u,_,r) = head $ euclid p (fromIntegral $ runF n)
    in if u == 1 then Just $ modNat $ fromInteger $ r `rem` p else Nothing

instance (Reifies p Integer) => DecidableAssociates (F p) where
  isAssociate p n =
    (isZero p && isZero n) || (not (isZero p) && not (isZero n))
instance (Reifies p Integer) => UnitNormalForm (F p)
instance (Reifies p Integer) => IntegralDomain (F p)
instance (Reifies p Integer) => GCDDomain (F p)
instance (Reifies p Integer) => UFD (F p)
instance (Reifies p Integer) => PID (F p)
instance (Reifies p Integer) => ZeroProductSemiring (F p)
instance (Reifies p Integer) => Euclidean (F p)

instance Reifies p Integer => Division (F p) where
  recip = recip
  (/)   = (/)
  (^)   = pow

instance Reifies p Integer => P.Fractional (F p) where
  a / b = a * recip b
  fromRational r =
    modNat (fromInteger $ R.numerator r) * recip (modNat (fromInteger $ R.denominator r))
  recip = fromMaybe (error "recip: not unit") . recipUnit

instance Reifies p Integer => NA.Commutative (F p)

instance Reifies p Integer => NA.Characteristic (F p) where
  char _ = fromIntegral $ reflect (Proxy :: Proxy p)

class (Field k, Characteristic k) => FiniteField k where
  power :: proxy k -> Natural
  elements :: proxy k -> [k]

instance Reifies p Integer => FiniteField (F p) where
  power _ = 1
  elements p = map modNat [0.. fromIntegral (char p) - 1]

order :: FiniteField k => proxy k -> Natural
order p = char p ^ power p

instance Reifies p Integer => Random (F p) where
  random = runRand $ uniform (elements Proxy)
  randomR (a, b) = runRand $ uniform $ map modNat [naturalRepr a..naturalRepr b]

modRat :: FiniteField k => Proxy k -> Fraction Integer -> k
modRat _ q = NA.fromInteger (numerator q) NA./ NA.fromInteger (denominator q)

modRat' :: FiniteField k => Fraction Integer -> k
modRat' = modRat Proxy
