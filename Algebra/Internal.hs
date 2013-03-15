{-# LANGUAGE RankNTypes, CPP #-}
{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, PolyKinds, StandaloneDeriving  #-}
{-# LANGUAGE TypeFamilies, TypeOperators                           #-}
module Algebra.Internal where
import Data.Proxy
#if __GLASGOW_HASKELL__ >= 760
import Data.Type.Monomorphic
#else
import Monomorphic
#endif

toProxy :: a -> Proxy a
toProxy _ = Proxy

data Nat = Z | S Nat
data Vector (a :: *) (n :: Nat)  where
  Nil  :: Vector a Z
  (:-) :: a -> Vector a n -> Vector a (S n)

infixr 5 :-
deriving instance Show a => Show (Vector a n)

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
instance Zero :<= n
instance (n :<= m) => S n :<= S m

data SNat (n :: Nat) where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

deriving instance Show (SNat n)

instance Monomorphicable SNat where
  type MonomorphicRep SNat = Int
  demote  (Monomorphic sn) = toInt sn
  promote n
      | n < 0     = error "negative integer!"
      | n == 0    = Monomorphic SZ
      | otherwise = withPolymorhic n $ \sn -> Monomorphic $ SS sn

instance Monomorphicable (Vector a) where
  type MonomorphicRep (Vector a) = [a]
  demote (Monomorphic vec) = toList vec
  promote [] = Monomorphic Nil
  promote (x:xs) =
    case promote xs of
      Monomorphic vec -> Monomorphic $ x :- vec

lengthV :: Vector a n -> Int
lengthV Nil       = 0
lengthV (_ :- xs) = 1 + lengthV xs

type family (n :: Nat) :+: (m :: Nat) :: Nat
type instance  Z   :+: n = n
type instance  S m :+: n = S (m :+: n)

(%+) :: SNat n -> SNat m -> SNat (n :+: m)
SZ   %+ n = n
SS n %+ m = SS (n %+ m)

appendV :: Vector a n -> Vector a m -> Vector a (n :+: m)
appendV (x :- xs) ys = x :- appendV xs ys
appendV Nil       ys = ys

foldrV :: (a -> b -> b) -> b -> Vector a n -> b
foldrV _ b Nil       = b
foldrV f a (x :- xs) = f x (foldrV f a xs)

foldlV :: (a -> b -> a) -> a -> Vector b n -> a
foldlV _ a Nil       = a
foldlV f a (b :- bs) = foldlV f (f a b) bs

singletonV :: a -> Vector a (S Z)
singletonV = (:- Nil)

zipWithV :: (a -> b -> c) -> Vector a n -> Vector b n -> Vector c n
zipWithV _ Nil Nil = Nil
zipWithV f (x :- xs) (y :- ys) = f x y :- zipWithV f xs ys
zipWithV _ _ _ = error "cannot happen"

toList :: Vector a n -> [a]
toList = foldrV (:) []

instance (Eq a) => Eq (Vector a n) where
  Nil == Nil = True
  (x :- xs) == (y :- ys) = x == y && xs == ys
  _ == _ = error "impossible!"

allV :: (a -> Bool) -> Vector a  n-> Bool
allV p = foldrV ((&&) . p) False

dropV :: SNat n -> Vector a (n :+: m) -> Vector a m
dropV n = snd . splitAtV n

toInt :: SNat n -> Int
toInt SZ     = 0
toInt (SS n) = 1 + toInt n

splitAtV :: SNat n -> Vector a (n :+: m) -> (Vector a n, Vector a m)
splitAtV SZ     xs        = (Nil, xs)
splitAtV (SS n) (x :- xs) =
  case splitAtV n xs of
    (xs', ys') -> (x :- xs', ys')
splitAtV _ _ = error "could not happen!"

sLengthV :: Vector a n -> SNat n
sLengthV Nil = SZ
sLengthV (_ :- xs) = sOne %+ sLengthV xs

mapV :: (a -> b) -> Vector a n -> Vector b n
mapV _ Nil       = Nil
mapV f (x :- xs) = f x :- mapV f xs

headV :: Vector a (S n) -> a
headV (x :- _) = x

tailV :: Vector a (S n) -> Vector a n
tailV (_ :- xs) = xs

data SingInstance a where
  SingInstance :: Sing a => SingInstance a

singInstance :: SNat n -> SingInstance n
singInstance SZ = SingInstance
singInstance (SS n) =
  case singInstance n of
    SingInstance -> SingInstance

data LeqInstance n m where
  LeqInstance :: (n :<= m) => LeqInstance n m

leqRefl :: SNat n -> LeqInstance n n
leqRefl SZ = LeqInstance
leqRefl (SS n) =
  case leqRefl n of
    LeqInstance -> LeqInstance

leqSucc :: SNat n -> LeqInstance n (S n)
leqSucc SZ = LeqInstance
leqSucc (SS n) =
    case leqSucc n of
      LeqInstance -> LeqInstance

