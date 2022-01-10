{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

{- | Quotient rings for eulidean domains.

   See @Algebra.Ring.Polynomial.Quotient@ in @halg-polynomial@
   for an ideal quotient rings of polynomial ring.
-}
module Algebra.Ring.Euclidean.Quotient
  ( Quotient (),
    representative,
    withQuotient,
    reifyQuotient,
    reifyIdealQuotient,
    withIdealQuotient,
    quotient,
    quotientBy,
  )
where

import Algebra.Ring.Ideal
import Algebra.Ring.Polynomial.Class
import AlgebraicPrelude
import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.Proxy
import Data.Reflection
import Numeric.Ring.Class as NA

newtype Quotient r a = Quotient {runQuotient :: a}
  deriving (Eq, Ord)

representative :: Quotient r a -> a
representative = runQuotient

instance (Show a, Reifies r a) => Show (Quotient r a) where
  showsPrec d (Quotient a) =
    showParen (d > 10) $
      showsPrec 11 a . showString " (mod "
        . showsPrec 11 (reflect (Proxy :: Proxy r))
        . showChar ')'

instance (Show a, Reifies r a, DecidableZero a) => PrettyCoeff (Quotient r a) where
  showsCoeff _ (Quotient a)
    | isZero a = Vanished
    | otherwise =
      Positive $
        showParen True $
          showParen True (shows a) . showString " + " . showsPrec 11 (reflect (Proxy :: Proxy r))

liftBin ::
  forall r a.
  (Reifies r a, Euclidean a) =>
  (a -> a -> a) ->
  Quotient r a ->
  Quotient r a ->
  Quotient r a
{-# INLINE liftBin #-}
liftBin = ((quotient .) .) . coerce

liftUnary ::
  forall r a.
  (Reifies r a, Euclidean a) =>
  (a -> a) ->
  Quotient r a ->
  Quotient r a
{-# INLINE liftUnary #-}
liftUnary = (quotient .) . coerce

quotient ::
  forall r a.
  (Reifies r a, Euclidean a) =>
  a ->
  Quotient r a
quotient = Quotient . rem' (reflect (Proxy :: Proxy r))

quotientBy ::
  forall r a proxy.
  (Reifies r a, Euclidean a) =>
  proxy r ->
  a ->
  Quotient r a
quotientBy = const quotient

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

instance
  (Euclidean a, LeftModule c a, Reifies r a) =>
  LeftModule c (Quotient r a)
  where
  (.*) = \n -> liftUnary (n .*)
  {-# INLINE (.*) #-}

instance
  (Euclidean a, RightModule c a, Reifies r a) =>
  RightModule c (Quotient r a)
  where
  (*.) = \p n -> liftUnary (*. n) p
  {-# INLINE (*.) #-}

instance
  (Euclidean a, Reifies r a) =>
  Monoidal (Quotient r a)
  where
  zero = Quotient zero
  {-# INLINE zero #-}
  sumWith f = foldl' (\a b -> a + f b) zero
  {-# INLINE sumWith #-}

instance
  (Euclidean a, Reifies r a) =>
  Abelian (Quotient r a)

instance
  (Euclidean a, Reifies r a) =>
  Multiplicative (Quotient r a)
  where
  (*) = liftBin (*)
  {-# INLINE (*) #-}

instance
  (Euclidean a, Reifies r a) =>
  Unital (Quotient r a)
  where
  one = quotient one
  {-# INLINE one #-}
  productWith f = foldl' (\a b -> a * f b) one
  {-# INLINE productWith #-}

instance
  (Euclidean a, Reifies r a) =>
  Commutative (Quotient r a)

instance
  (Euclidean a, Reifies r a) =>
  Semiring (Quotient r a)

instance
  (Euclidean a, Reifies r a) =>
  Group (Quotient r a)
  where
  (-) = liftBin (-)
  {-# INLINE (-) #-}
  negate = liftUnary negate
  {-# INLINE negate #-}
  subtract = liftBin subtract
  {-# INLINE subtract #-}

instance
  (Euclidean a, Reifies r a) =>
  Rig (Quotient r a)
  where
  fromNatural = quotient . fromNatural
  {-# INLINE fromNatural #-}

instance
  (Euclidean a, Reifies r a) =>
  Ring (Quotient r a)
  where
  fromInteger = quotient . NA.fromInteger
  {-# INLINE fromInteger #-}

instance
  (Euclidean a, Reifies r a) =>
  DecidableUnits (Quotient r a)
  where
  recipUnit = \(Quotient i) -> do
    guard $ not $ isZero i
    let p = reflect (Proxy :: Proxy r)
        (u, _, x) = egcd p i
    quotient . (* x) <$> recipUnit u
  {-# INLINE recipUnit #-}

instance
  (Euclidean a, Reifies r a) =>
  DecidableAssociates (Quotient r a)
  where
  isAssociate (Quotient f) (Quotient g) =
    case prs f g of
      (x, a, b) : _
        | isZero (x `rem` reflect (Proxy :: Proxy r)) ->
          chkUnits a b
      (x, s', t') : (r, s, t) : _
        | isZero ((x `rem` reflect (Proxy :: Proxy r)) - one) ->
          chkUnits (s - r * s') (t - r * t')
      _ -> False
    where
      chkUnits a b =
        isUnit (quotient a :: Quotient r a)
          && isUnit (quotient b :: Quotient r a)

withQuotient ::
  forall a.
  (Euclidean a) =>
  a ->
  (forall (r :: Type). Reifies r a => Quotient r a) ->
  a
{-# INLINE withQuotient #-}
withQuotient q a =
  reify q $ \(Proxy :: Proxy r) ->
    runQuotient (a :: Quotient r a)

withIdealQuotient ::
  Euclidean a =>
  Ideal a ->
  (forall (r :: Type). Reifies r a => Quotient r a) ->
  a
{-# INLINE withIdealQuotient #-}
withIdealQuotient is = withQuotient (foldl' gcd one is)

reifyQuotient ::
  forall a r.
  (Euclidean a) =>
  a ->
  (forall (s :: Type). Reifies s a => Proxy s -> r) ->
  r
reifyQuotient = reify

reifyIdealQuotient ::
  forall a r.
  (Euclidean a) =>
  Ideal a ->
  (forall (s :: Type). Reifies s a => Proxy s -> r) ->
  r
reifyIdealQuotient is = reify (foldl' gcd one is)
