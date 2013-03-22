{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, PolyKinds, StandaloneDeriving  #-}
{-# LANGUAGE TypeFamilies, TypeOperators                           #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Algebra.Internal ( toProxy, Nat(..), SNat(..), Vector(..), Sing(..)
                        , SingInstance(..), singInstance, toInt
                        , Min, Max, sMin, sMax, sZ, sS, (:+:), (%+), (:-:), (%-)
                        , sZero, sOne, sTwo, sThree, Zero, One, Two, Three
                        , SZero, SOne, STwo, SThree
                        , lengthV, sLengthV, takeV, dropV, splitAtV, appendV
                        , foldrV, foldlV, singletonV, zipWithV, toList, allV
                        , mapV, headV, tailV
                        , Leq(..), (:<<=), (:<=), LeqInstance(..)
                        , LeqTrueInstance(..), boolToPropLeq, boolToClassLeq
                        , propToClassLeq, propToBoolLeq
                        , leqRefl, leqSucc, Eql(..), eqlRefl, eqlSymm
                        , eqlTrans, plusZR, plusZL, eqPreservesS, plusAssociative
                        , sAndPlusOne, plusCommutative, minusCongEq, minusNilpotent
                        , eqSuccMinus, plusMinusEqL, plusMinusEqR, plusLeqL, plusLeqR
                        , zAbsorbsMinR, zAbsorbsMinL, minLeqL, minLeqR, plusSR
                        , leqRhs, leqLhs, leqTrans, minComm, leqAnitsymmetric
                        , maxZL, maxComm, maxZR, maxLeqL, maxLeqR, plusMonotone
                        , module Monomorphic
                        ) where
import Data.Proxy
import Monomorphic

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

-- | The smart constructor for @SZ@.
sZ :: SNat Z
sZ = case singInstance SZ of
       SingInstance -> SZ

-- | The smart constructor for @SS n@.
sS :: SNat n -> SNat (S n)
sS n = case singInstance n of
         SingInstance -> SS n

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
      | otherwise = withPolymorhic (n - 1) $ \sn -> Monomorphic $ SS sn

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

type family (n :: Nat) :-: (m :: Nat) :: Nat
type instance n   :-: Z   = n
type instance Z   :-: m   = Z
type instance S n :-: S m = n :-: m

(%-) :: (m :<<= n) ~ True => SNat n -> SNat m -> SNat (n :-: m)
n   %- SZ    = n
SS n %- SS m = n %- m
_    %- _    = error "impossible!"

-- | Comparison function
type family   (n :: Nat) :<<= (m :: Nat) :: Bool
type instance Z   :<<= n   = True
type instance S n :<<= Z   = False
type instance S n :<<= S m = n :<<= m

-- | Comparison witness via GADTs.
data Leq (n :: Nat) (m :: Nat) where
  ZeroLeq     :: SNat m -> Leq Zero m
  SuccLeqSucc :: Leq n m -> Leq (S n) (S m)

data LeqInstance n m where
  LeqInstance :: (n :<= m) => LeqInstance n m

boolToPropLeq :: (n :<<= m) ~ True => SNat n -> SNat m -> Leq n m
boolToPropLeq SZ     m      = ZeroLeq m
boolToPropLeq (SS n) (SS m) = SuccLeqSucc $ boolToPropLeq n m
boolToPropLeq _      _      = error "impossible happend!"

boolToClassLeq :: (n :<<= m) ~ True => SNat n -> SNat m -> LeqInstance n m
boolToClassLeq SZ     _      = LeqInstance
boolToClassLeq (SS n) (SS m) =
  case boolToClassLeq n m of
    LeqInstance -> LeqInstance
boolToClassLeq _ _ = error "impossible!"

propToClassLeq :: Leq n m -> LeqInstance n m
propToClassLeq (ZeroLeq _) = LeqInstance
propToClassLeq (SuccLeqSucc leq) =
  case propToClassLeq leq of
    LeqInstance -> LeqInstance

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

allV :: (a -> Bool) -> Vector a  n -> Bool
allV p = foldrV ((&&) . p) False

dropV :: (n :<<= m) ~ True => SNat n -> Vector a m -> Vector a (m :-: n)
dropV n = snd . splitAtV n

takeV :: (n :<<= m) ~ True => SNat n -> Vector a m -> Vector a n
takeV n = fst . splitAtV n

toInt :: SNat n -> Int
toInt SZ     = 0
toInt (SS n) = 1 + toInt n

splitAtV :: (n :<<= m) ~ True
         => SNat n -> Vector a m -> (Vector a n, Vector a (m :-: n))
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

data Reason x y where
  Because :: SNat y -> Eql x y -> Reason x y

because :: SNat y -> Eql x y -> Reason x y
because = Because

infixl 4 ===, =~=
infix 5 `Because`
infix 5 `because`


(===) :: Eql x y -> Reason y z -> Eql x z
eq === (_ `Because` eq') = eqlTrans eq eq'

(=~=) :: Eql x y -> SNat y -> Eql x y
eq =~= _ = eq

start :: SNat a -> Eql a a
start = eqlRefl

definition, byDefinition :: Sing a => Eql a a
byDefinition = eqlRefl sing
definition = eqlRefl sing

admitted :: Reason x y
admitted = undefined
{-# WARNING admitted "There are some goals left yet unproven." #-}

infix 4 :=:
type a :=: b = Eql a b

cong' :: (SNat m -> SNat (f m)) -> a :=: b -> f a :=: f b
cong' _ Eql = Eql


leqRefl :: SNat n -> Leq n n
leqRefl SZ = ZeroLeq sZ
leqRefl (SS n) = SuccLeqSucc $ leqRefl n

leqSucc :: SNat n -> Leq n (S n)
leqSucc SZ = ZeroLeq sOne
leqSucc (SS n) = SuccLeqSucc $ leqSucc n

data Eql a b where
  Eql :: Eql a a

eqlRefl :: SNat a -> Eql a a
eqlRefl _ = Eql

eqlSymm :: Eql a b -> Eql b a
eqlSymm Eql = Eql

eqlTrans :: Eql a b -> Eql b c -> Eql a c
eqlTrans Eql Eql = Eql

plusZR :: SNat n -> Eql (n :+: Z) n
plusZR SZ     = Eql
plusZR (SS n) =
 start (sS n %+ sZ)
   =~= sS (n %+ sZ)
   === sS n          `because` cong' sS (plusZR n)

plusZL :: SNat n -> Eql (Z :+: n) n
plusZL _ = Eql

eqPreservesS :: Eql n m -> Eql (S n) (S m)
eqPreservesS Eql = Eql

plusAssociative :: SNat n -> SNat m -> SNat l
                -> Eql (n :+: (m :+: l)) ((n :+: m) :+: l)
plusAssociative SZ     _ _ = Eql
plusAssociative (SS n) m l =
  start (sS n %+ (m %+ l))
    =~= sS (n %+ (m %+ l))
    === sS ((n %+ m) %+ l)  `because` cong' sS (plusAssociative n m l)
    =~= sS (n %+ m) %+ l
    =~= (sS n %+ m) %+ l

sAndPlusOne :: SNat n -> Eql (S n) (n :+: One)
sAndPlusOne SZ = Eql
sAndPlusOne (SS n) =
  start (sS (sS n))
    === sS (n %+ sOne) `because` cong' sS (sAndPlusOne n)
    =~= sS n %+ sOne

plusCongL :: SNat n -> m :=: m' -> n :+: m :=: n :+: m'
plusCongL _ Eql = Eql

plusCongR :: SNat n -> m :=: m' -> m :+: n :=: m' :+: n
plusCongR _ Eql = Eql

plusCommutative :: SNat n -> SNat m -> Eql (n :+: m) (m :+: n)
plusCommutative SZ SZ     = Eql
plusCommutative SZ (SS m) =
  start (sZ %+ sS m)
    =~= sS m
    === sS (m %+ sZ) `because` cong' sS (plusCommutative SZ m)
    =~= sS m %+ sZ
plusCommutative (SS n) m =
  start (sS n %+ m)
    =~= sS (n %+ m)
    === sS (m %+ n)      `because` cong' sS (plusCommutative n m)
    === (m %+ n) %+ sOne `because` sAndPlusOne (m %+ n)
    === m %+ (n %+ sOne) `because` eqlSymm (plusAssociative m n sOne)
    === m %+ sS n        `because` plusCongL m (eqlSymm $ sAndPlusOne n)

minusCongEq :: Eql n m -> SNat l -> Eql (n :-: l) (m :-: l)
minusCongEq Eql _ = Eql

minusNilpotent :: SNat n -> Eql (n :-: n) Zero
minusNilpotent SZ = Eql
minusNilpotent (SS n) =
  case minusNilpotent n of
    Eql -> Eql

eqSuccMinus :: ((m :<<= n) ~ True)
            => SNat n -> SNat m -> Eql (S n :-: m) (S (n :-: m))
eqSuccMinus _ SZ     = Eql
eqSuccMinus (SS n) (SS m) = case eqSuccMinus n m of Eql -> Eql
eqSuccMinus _ _ = error "impossible!"

plusMinusEqL :: SNat n -> SNat m -> Eql ((n :+: m) :-: m) n
plusMinusEqL SZ     m = minusNilpotent m
plusMinusEqL (SS n) m =
  case propToBoolLeq (plusLeqR n m) of
    LeqTrueInstance -> eqlTrans (eqSuccMinus (n %+ m) m) (eqPreservesS $ plusMinusEqL n m)

plusMinusEqR :: SNat n -> SNat m -> Eql ((m :+: n) :-: m) n
plusMinusEqR n m = eqlTrans (minusCongEq (plusCommutative n m) m) (plusMinusEqL n m)

data LeqTrueInstance a b where
  LeqTrueInstance :: (a :<<= b) ~ True => LeqTrueInstance a b

propToBoolLeq :: Leq n m -> LeqTrueInstance n m
propToBoolLeq (ZeroLeq _) = LeqTrueInstance
propToBoolLeq (SuccLeqSucc leq) =
  case propToBoolLeq leq of
    LeqTrueInstance -> LeqTrueInstance


plusLeqL :: SNat n -> SNat m -> Leq n (n :+: m)
plusLeqL SZ     m = case plusZR m of Eql -> ZeroLeq m
plusLeqL (SS n) m = SuccLeqSucc $ plusLeqL n m

plusLeqR :: SNat n -> SNat m -> Leq m (n :+: m)
plusLeqR n m =
  case plusCommutative n m of
    Eql -> plusLeqL m n

zAbsorbsMinR :: SNat n -> Eql (Min n Z) Z
zAbsorbsMinR SZ     = Eql
zAbsorbsMinR (SS n) =
  case zAbsorbsMinR n of
    Eql -> Eql

zAbsorbsMinL :: SNat n -> Eql (Min Z n) Z
zAbsorbsMinL SZ     = Eql
zAbsorbsMinL (SS n) =
  case zAbsorbsMinL n of
    Eql -> Eql

minLeqL :: SNat n -> SNat m -> Leq (Min n m) n
minLeqL SZ m = case zAbsorbsMinL m of Eql -> ZeroLeq sZ
minLeqL n SZ = case zAbsorbsMinR n of Eql -> ZeroLeq n
minLeqL (SS n) (SS m) = SuccLeqSucc (minLeqL n m)

minLeqR :: SNat n -> SNat m -> Leq (Min n m) m
minLeqR n m = case minComm n m of Eql -> minLeqL m n

leqRhs :: Leq n m -> SNat m
leqRhs (ZeroLeq m) = m
leqRhs (SuccLeqSucc leq) = SS $ leqRhs leq

leqLhs :: Leq n m -> SNat n
leqLhs (ZeroLeq _) = SZ
leqLhs (SuccLeqSucc leq) = SS $ leqLhs leq

leqTrans :: Leq n m -> Leq m l -> Leq n l
leqTrans (ZeroLeq _) leq = ZeroLeq $ leqRhs leq
leqTrans (SuccLeqSucc nLeqm) (SuccLeqSucc mLeql) = SuccLeqSucc $ leqTrans nLeqm mLeql
leqTrans _ _ = error "impossible!"

minComm :: SNat n -> SNat m -> Eql (Min n m) (Min m n)
minComm SZ     SZ = Eql
minComm SZ     (SS _) = Eql
minComm (SS _) SZ = Eql
minComm (SS n) (SS m) = case minComm n m of Eql -> Eql

leqAnitsymmetric :: Leq n m -> Leq m n -> Eql n m
leqAnitsymmetric (ZeroLeq _) (ZeroLeq _) = Eql
leqAnitsymmetric (SuccLeqSucc leq1) (SuccLeqSucc leq2) = eqPreservesS $ leqAnitsymmetric leq1 leq2
leqAnitsymmetric _ _ = error "impossible"

maxZL :: SNat n -> Eql (Max Z n) n
maxZL SZ = Eql
maxZL (SS _) = Eql

maxComm :: SNat n -> SNat m -> Eql (Max n m) (Max m n)
maxComm SZ SZ = Eql
maxComm SZ (SS _) = Eql
maxComm (SS _) SZ = Eql
maxComm (SS n) (SS m) = case maxComm n m of Eql -> Eql

maxZR :: SNat n -> Eql (Max n Z) n
maxZR n = eqlTrans (maxComm n sZ) (maxZL n)

maxLeqL :: SNat n -> SNat m -> Leq n (Max n m)
maxLeqL SZ m = ZeroLeq (sMax sZ m)
maxLeqL n SZ = case maxZR n of
                 Eql -> leqRefl n
maxLeqL (SS n) (SS m) = SuccLeqSucc $ maxLeqL n m

maxLeqR :: SNat n -> SNat m -> Leq m (Max n m)
maxLeqR n m = case maxComm n m of
                Eql -> maxLeqL m n

plusSR :: SNat n -> SNat m -> Eql (S (n :+: m)) (n :+: S m)
plusSR n m =
  start (sS (n %+ m))
    === (n %+ m) %+ sOne `because` sAndPlusOne (n %+ m)
    === n %+ (m %+ sOne) `because` eqlSymm (plusAssociative n m sOne)
    === n %+ sS m        `because` plusCongL n (eqlSymm $ sAndPlusOne m)

plusMonotone :: Leq n m -> Leq l k -> Leq (n :+: l) (m :+: k)
plusMonotone (ZeroLeq m) (ZeroLeq k) = ZeroLeq (m %+ k)
plusMonotone (ZeroLeq m) (SuccLeqSucc leq) =
  case plusSR m (leqRhs leq) of
    Eql -> SuccLeqSucc $ plusMonotone (ZeroLeq m) leq
plusMonotone (SuccLeqSucc leq) leq' = SuccLeqSucc $ plusMonotone leq leq'

-- (m + S n) - m = S (m + n) - m
