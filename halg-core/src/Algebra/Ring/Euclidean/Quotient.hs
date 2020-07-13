{-# LANGUAGE DataKinds, GADTs, MultiParamTypeClasses, PolyKinds, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving                        #-}
-- | Quotient rings for eulidean domains.
--
--   See @Algebra.Ring.Polynomial.Quotient@ in @halg-polynomial@
--   for an ideal quotient rings of polynomial ring.
module Algebra.Ring.Euclidean.Quotient
  ( Quotient(), withQuotient, withIdealQuotient, quotient
  ) where
import Algebra.Ring.Ideal
import AlgebraicPrelude
import Data.Coerce        (coerce)
import Data.Kind          (Type)
import Data.Proxy
import Data.Reflection
import Numeric.Ring.Class as NA

newtype Quotient r a = Quotient { runQuotient :: a }
  deriving (Eq, Ord)

instance (Show a, Reifies r a) => Show (Quotient r a) where
  showsPrec d (Quotient a) = showParen (d > 10) $
    showsPrec 11 a . showString " (mod "
      . showsPrec 11 (reflect (Proxy :: Proxy r))
      . showChar '>'

liftBin
  :: forall r a.
      (Reifies r a, Euclidean a)
  => (a -> a -> a)
  -> Quotient r a -> Quotient r a -> Quotient r a
{-# INLINE liftBin #-}
liftBin = ((quotient .) .) . coerce

liftUnary
  :: forall r a.
      (Reifies r a, Euclidean a)
  => (a -> a)
  -> Quotient r a -> Quotient r a
{-# INLINE liftUnary #-}
liftUnary = (quotient .) . coerce

quotient
  :: forall r a. (Reifies r a, Euclidean a)
  => a -> Quotient r a
quotient = Quotient . rem' (reflect (Proxy :: Proxy r))

rem' :: Euclidean a => a -> a -> a
{-# INLINE rem' #-}
rem' a
  | isZero a = id
  | otherwise = (`rem` a)

instance (Euclidean a, Reifies r a) => DecidableZero (Quotient r a) where
  isZero (Quotient r) = isZero r

instance (Euclidean a, Reifies r a) => Additive (Quotient r a) where
  (+) = liftBin (+)
  {-# INLINE (+) #-}

instance (Euclidean a, LeftModule c a, Reifies r a)
      => LeftModule c (Quotient r a) where
  (.*) = \n -> liftUnary (n .*)
  {-# INLINE (.*) #-}

instance (Euclidean a, RightModule c a, Reifies r a)
      => RightModule c (Quotient r a) where
  (*.) = \p n -> liftUnary (*. n) p
  {-# INLINE (*.) #-}

instance (Euclidean a, Reifies r a)
      => Monoidal (Quotient r a) where
  zero = Quotient zero
  {-# INLINE zero #-}
  sumWith f = foldl' (\a b -> a + f b) zero
  {-# INLINE sumWith #-}

instance (Euclidean a, Reifies r a)
      => Abelian (Quotient r a)

instance (Euclidean a, Reifies r a)
      => Multiplicative (Quotient r a) where
  (*) = liftBin (*)
  {-# INLINE (*) #-}

instance (Euclidean a, Reifies r a)
      => Unital (Quotient r a) where
  one = quotient one
  {-# INLINE one #-}
  productWith f = foldl' (\a b -> a * f b) one
  {-# INLINE productWith #-}

instance (Euclidean a, Reifies r a)
      => Commutative (Quotient r a)

instance (Euclidean a, Reifies r a)
      => Semiring (Quotient r a)

instance (Euclidean a, Reifies r a)
      => Group (Quotient r a) where
  (-) = liftBin (-)
  {-# INLINE (-) #-}
  negate = liftUnary negate
  {-# INLINE negate #-}
  subtract = liftBin subtract
  {-# INLINE subtract #-}

instance (Euclidean a, Reifies r a)
  => Rig (Quotient r a) where
  fromNatural = quotient . fromNatural
  {-# INLINE fromNatural #-}

instance (Euclidean a, Reifies r a)
  => Ring (Quotient r a) where
  fromInteger = quotient . NA.fromInteger
  {-# INLINE fromInteger #-}

instance (Euclidean a, Reifies r a)
      => DecidableUnits (Quotient r a) where
  recipUnit = \(Quotient i) -> do
    guard $ not $ isZero i
    let p = reflect (Proxy :: Proxy r)
        (u, _, x) = egcd p i
    quotient . (*x) <$> recipUnit u
  {-# INLINE recipUnit #-}

withQuotient
  :: forall a. (Euclidean a)
  => a
  -> (forall (r :: Type). Reifies r a => Quotient r a)
  -> a
{-# INLINE withQuotient #-}
withQuotient q a =
  reify q $ \(Proxy :: Proxy r) ->
    runQuotient (a :: Quotient r a)

withIdealQuotient
  :: Euclidean a
  => Ideal a
  -> (forall (r :: Type). Reifies r a => Quotient r a)
  -> a
{-# INLINE withIdealQuotient #-}
withIdealQuotient is = withQuotient (foldl' gcd one is)
