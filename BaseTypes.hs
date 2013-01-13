{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, PolyKinds, StandaloneDeriving  #-}
{-# LANGUAGE TypeFamilies, TypeOperators                           #-}
module BaseTypes where

data Nat = Z | S Nat
data Vector (n :: Nat) (a :: *) where
  Nil  :: Vector Z a
  (:-) :: a -> Vector n a -> Vector (S n) a

infixr 5 :-
deriving instance Show a => Show (Vector n a)

type family Min (n :: Nat) (m :: Nat) :: Nat
type instance Min Z Z     = Z
type instance Min Z (S n) = Z
type instance Min (S m) Z = Z
type instance Min (S n) (S m) = S (Min n m)

type family Max (n :: Nat) (m :: Nat) :: Nat
type instance Max Z Z     = Z
type instance Max Z (S n) = S n
type instance Max (S n) Z = S n
type instance Max (S n) (S m) = S (Max n m)

type Zero  = Z
type One   = S Z
type Two   = S (S Z)
type Three = S (S (S Z))

type SZero  = SNat Zero
type SOne   = SNat One
type STwo   = SNat Two
type SThree = SNat Three

sZero :: SZero
sZero = SZ

sOne :: SOne
sOne = SS sZero

sTwo :: STwo
sTwo = SS sOne

sThree :: SThree
sThree = SS sTwo

sMin :: SNat n -> SNat m -> SNat (Min n m)
sMin SZ     SZ     = SZ
sMin (SS _) SZ     = SZ
sMin SZ     (SS _) = SZ
sMin (SS n) (SS m) = SS (sMin n m)

sMax :: SNat n -> SNat m -> SNat (Max n m)
sMax SZ     SZ     = SZ
sMax (SS n) SZ     = SS n
sMax SZ     (SS n) = SS n
sMax (SS n) (SS m) = SS (sMax n m)

class Sing (n :: Nat) where
  sing :: SNat n

instance Sing Z where
  sing = SZ

instance Sing n => Sing (S n) where
  sing = SS sing

class (n :: Nat) :<= (m :: Nat)
instance Z :<= (n :: Nat)
instance (n :<= m) => S n :<= S m

data SNat (n :: Nat) where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

lengthV :: Vector n a -> Int
lengthV Nil       = 0
lengthV (_ :- xs) = 1 + lengthV xs

type family (n :: Nat) :+: (m :: Nat) :: Nat
type instance  Z   :+: n = n
type instance  S m :+: n = S (m :+: n)

appendV :: Vector n a -> Vector m a -> Vector (n :+: m) a
appendV (x :- xs) ys = x :- appendV xs ys
appendV Nil       ys = ys

foldrV :: (a -> b -> b) -> b -> Vector n a -> b
foldrV _ b Nil       = b
foldrV f a (x :- xs) = f x (foldrV f a xs)

foldlV :: (a -> b -> a) -> a -> Vector n b -> a
foldlV _ a Nil       = a
foldlV f a (b :- bs) = foldlV f (f a b) bs

singletonV :: a -> Vector (S Z) a
singletonV = (:- Nil)

zipWithV :: (a -> b -> c) -> Vector n a -> Vector n b -> Vector n c
zipWithV _ Nil Nil = Nil
zipWithV f (x :- xs) (y :- ys) = f x y :- zipWithV f xs ys
zipWithV _ _ _ = error "cannot happen"

toList :: Vector n a -> [a]
toList = foldrV (:) []

instance Eq (Vector Z a) where
  Nil == Nil = True

instance (Eq a, Eq (Vector n a)) => Eq (Vector (S n) a) where
  (x :- xs) == (y :- ys) = x == y && xs == ys


