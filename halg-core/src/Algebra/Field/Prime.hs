{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | Prime fields
{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses, PolyKinds, RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
module Algebra.Field.Prime
       ( F(), naturalRepr, reifyPrimeField, withPrimeField
       , modNat, modNat', modRat, modRat'
       , FiniteField(..), order
       ) where
import Algebra.Arithmetic            (modPow)
import Algebra.Field.Finite
import Algebra.Normed
import Algebra.Ring.Polynomial.Class (PrettyCoeff (..), ShowSCoeff (..))

import           AlgebraicPrelude
import           Control.DeepSeq              (NFData (..))
import           Control.Monad.Random         (uniform)
import           Control.Monad.Random         (runRand)
import           Control.Monad.Random         (Random (..))
import qualified Data.Coerce                  as C
import           Data.Maybe                   (fromMaybe)
import           Data.Proxy                   (Proxy (..), asProxyTypeOf)
import qualified Data.Ratio                   as R
import           Data.Reflection              (Reifies (reflect), reifyNat)
import           GHC.Read
import           GHC.TypeLits                 (KnownNat)
import           Numeric.Algebra              (char)
import           Numeric.Algebra              (Natural)
import qualified Numeric.Algebra              as NA
import           Numeric.Semiring.ZeroProduct (ZeroProductSemiring)
import qualified Prelude                      as P

-- | Prime field of characteristic @p@.
--   @p@ should be prime, and not statically checked.
newtype F (p :: k) = F { runF :: Integer }
                   deriving (NFData)


instance Reifies p Integer => Read (F p) where
  readPrec = fromInteger <$> readPrec

modNat :: Reifies (p :: k) Integer => Integer -> F p
modNat = modNat' Proxy
{-# INLINE modNat #-}

modNat' :: forall proxy (p :: k). Reifies p Integer => proxy (F p) -> Integer -> F p
modNat' _ i =
  let p = reflect (Proxy :: Proxy p)
  in F (i `rem` p)
{-# INLINE modNat' #-}

reifyPrimeField :: Integer -> (forall p. KnownNat p => Proxy (F p) -> a) -> a
reifyPrimeField p f = reifyNat p (f . proxyF)

withPrimeField :: Integer -> (forall p. KnownNat p => F p) -> Integer
withPrimeField p f = reifyPrimeField p $ runF . asProxyTypeOf f

naturalRepr :: F p -> Integer
naturalRepr = runF

proxyF :: Proxy (a :: k) -> Proxy (F a)
proxyF Proxy = Proxy

instance Eq (F p) where
  F n == F m = n == m

instance Reifies p Integer => Normed (F p) where
  type Norm (F p) = Integer
  norm fp@(F p) = p where _ = reflect fp
  liftNorm = modNat

instance Reifies p Integer => P.Num (F p) where
  fromInteger = fromInteger'
  {-# INLINE fromInteger #-}

  (+) = C.coerce ((P.+) :: WrapAlgebra (F p) -> WrapAlgebra (F p) -> WrapAlgebra (F p))
  {-# INLINE (+) #-}

  (-) = C.coerce ((P.-) :: WrapAlgebra (F p) -> WrapAlgebra (F p) -> WrapAlgebra (F p))
  {-# INLINE (-) #-}

  negate = C.coerce (P.negate :: WrapAlgebra (F p) -> WrapAlgebra (F p))
  {-# INLINE negate #-}

  (*) = C.coerce ((P.*) :: WrapAlgebra (F p) -> WrapAlgebra (F p) -> WrapAlgebra (F p))
  {-# INLINE (*) #-}

  abs = id
  signum (F 0) = F 0
  signum (F _) = F 1

pows :: (P.Integral a1, Reifies p Integer) => F p -> a1 -> F p
pows a n = modNat $ modPow (runF a) (reflect a) (toInteger n)

instance Reifies p Integer => NA.Additive (F p) where
  F a + F b = modNat $ a + b
  {-# INLINE (+) #-}
  sinnum1p n (F k) = modNat $ (1 P.+ P.fromIntegral n) * k
  {-# INLINE sinnum1p #-}

instance Reifies p Integer => NA.Multiplicative (F p) where
  F a * F b = modNat $ a * b
  {-# INLINE (*) #-}

  pow1p n p = pows n (p P.+ 1)
  {-# INLINE pow1p #-}

instance Reifies p Integer => NA.Monoidal (F p) where
  zero = F 0
  {-# INLINE zero #-}
  sinnum n (F k) = modNat $ P.fromIntegral n * k
  {-# INLINE sinnum #-}

instance Reifies p Integer => NA.LeftModule Natural (F p) where
  n .* F p = modNat (n .* p)
  {-# INLINE (.*) #-}

instance Reifies p Integer => NA.RightModule Natural (F p) where
  F p *. n = modNat (p *. n)
  {-# INLINE (*.) #-}

instance Reifies p Integer => NA.LeftModule Integer (F p) where
  n .* F p = modNat (n * p)
  {-# INLINE (.*) #-}

instance Reifies p Integer => NA.RightModule Integer (F p) where
  F p *. n = modNat (p * n)
  {-# INLINE (*.) #-}

instance Reifies p Integer => NA.Group (F p) where
  F a - F b    = modNat $ a - b
  {-# INLINE (-) #-}

  negate (F a) = F (reflect (Proxy :: Proxy p) - a)
  {-# INLINE negate #-}

instance Reifies p Integer => NA.Abelian (F p)

instance Reifies p Integer => NA.Semiring (F p)

instance Reifies p Integer => NA.Rig (F p) where
  fromNatural = modNat . P.fromIntegral
  {-# INLINE fromNatural #-}

instance Reifies p Integer => NA.Ring (F p) where
  fromInteger = modNat
  {-# INLINE fromInteger #-}

instance Reifies p Integer => NA.DecidableZero (F p) where
  isZero (F p) = p == 0

instance Reifies p Integer => NA.Unital (F p) where
  one = F 1
  {-# INLINE one #-}
  pow = pows
  {-# INLINE pow #-}

instance Reifies p Integer => DecidableUnits (F p) where
  isUnit (F n) = n /= 0
  {-# INLINE isUnit #-}

  recipUnit n@(F k) =
    let p = fromIntegral $ reflect n
        (u,_,r) = head $ euclid p k
    in if u == 1 then Just $ modNat $ fromInteger $ r `rem` p else Nothing
  {-# INLINE recipUnit #-}

instance (Reifies p Integer) => DecidableAssociates (F p) where
  isAssociate p n =
    (isZero p && isZero n) || (not (isZero p) && not (isZero n))
  {-# INLINE isAssociate #-}

instance (Reifies p Integer) => UnitNormalForm (F p)
instance (Reifies p Integer) => IntegralDomain (F p)
instance (Reifies p Integer) => GCDDomain (F p)
instance (Reifies p Integer) => UFD (F p)
instance (Reifies p Integer) => PID (F p)
instance (Reifies p Integer) => ZeroProductSemiring (F p)
instance (Reifies p Integer) => Euclidean (F p)

instance Reifies p Integer => Division (F p) where
  recip = fromMaybe (error "recip: not unit") . recipUnit
  {-# INLINE recip #-}
  a / b =  a * recip b
  {-# INLINE (/) #-}
  (^)   = pows
  {-# INLINE (^) #-}

instance Reifies p Integer => P.Fractional (F p) where
  (/) = C.coerce ((P./) :: WrapAlgebra (F p) -> WrapAlgebra (F p) -> WrapAlgebra (F p))
  {-# INLINE (/) #-}

  fromRational r =
    modNat (R.numerator r) * recip (modNat $ R.denominator r)
  {-# INLINE fromRational #-}

  recip = C.coerce (P.recip :: WrapAlgebra (F p) -> WrapAlgebra (F p))
  {-# INLINE recip #-}

instance Reifies p Integer => NA.Commutative (F p)

instance Reifies p Integer => NA.Characteristic (F p) where
  char _ = fromIntegral $ reflect (Proxy :: Proxy p)
  {-# INLINE char #-}


instance Reifies (p :: k) Integer => Show (F p) where
  showsPrec d n@(F p) = showsPrec d (p `rem` reflect n)

instance Reifies (p :: k) Integer => PrettyCoeff (F p) where
  showsCoeff d (F p)
    | p == 0 = Vanished
    | p == 1 = OneCoeff
    | otherwise = Positive $ showsPrec d p

instance Reifies p P.Integer => FiniteField (F p) where
  power _ = 1
  {-# INLINE power #-}

  elements p = map modNat [0.. fromIntegral (char p) - 1]
  {-# INLINE elements #-}

instance Reifies p Integer => Random (F p) where
  random = runRand $ uniform (elements Proxy)
  {-# INLINE random #-}
  randomR (a, b) = runRand $ uniform $ map modNat [naturalRepr a..naturalRepr b]
  {-# INLINE randomR #-}

modRat :: FiniteField k => Proxy k -> Fraction Integer -> k
modRat _ q = NA.fromInteger (numerator q) NA./ NA.fromInteger (denominator q)
{-# INLINE modRat #-}

modRat' :: FiniteField k => Fraction Integer -> k
modRat' = modRat Proxy
{-# INLINE modRat' #-}
