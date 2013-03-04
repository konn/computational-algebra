{-# LANGUAGE DataKinds, ExistentialQuantification, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances             #-}
module NoetherianRing ( NoetherianRing(..), Ideal(..), (.*), addToIdeal, toIdeal, appendIdeal
                      , generators, filterIdeal, mapIdeal, principalIdeal) where
import BaseTypes
import Data.Complex
import Data.Function
import Data.Ord
import Data.Ratio

class Eq r => NoetherianRing r where
  -- ^ Noetherian ring R should satisfy following equations:
  -- * addition forms an abelian group:
  -- (A1) a .+. (b .+. c) == (a .+. b) .+. c
  -- (A2) a .+. zero == zero .+. a == zero
  -- (A3) a .+. neg a == neg a .+. a == zero
  -- (A4) a .+. b == b .+. a
  -- * multiplication forms a commutative monoid:
  -- (M1) a .*. (b .*. c) == (a .*. b) .*. c
  -- (M2) a .*. one == one .*. a
  -- (M3) a .*. b   == b .*. a
  -- * Distributive laws:
  -- (D1) a .*. (b .+. c) = (a .*. b) .+. (a .*. c)
  -- (D2) (a .+. b) .*. c = (a .*. c) .+. (b .*. c)
  -- And, in addition, every ideals of R should be finitely-generated.
  -- | Addition
  (.+.) :: r -> r -> r
  -- | Multiplication
  (.*.) :: r -> r -> r
  (.-.) :: r -> r -> r
  a .-. b = a .+. neg b
  -- | Additive inverse
  neg   :: r -> r
  -- | Multiplicative identity
  one   :: r
  -- | Additive identity
  zero  :: r

infixl 7 .*.
infixl 6 .+.
infixl 6 .-.

instance NoetherianRing Int where
  (.+.) = (+)
  (.*.) = (*)
  neg   = negate
  one   = 1
  zero  = 0

instance NoetherianRing Integer where
  (.+.) = (+)
  (.*.) = (*)
  neg   = negate
  one   = 1
  zero  = 0

instance NoetherianRing Double where
  (.+.) = (+)
  (.*.) = (*)
  neg   = negate
  one   = 1
  zero  = 0

instance NoetherianRing Float where
  (.+.) = (+)
  (.*.) = (*)
  neg   = negate
  one   = 1
  zero  = 0

instance Integral r => NoetherianRing (Ratio r) where
  (.+.) = (+)
  (.*.) = (*)
  neg   = negate
  one   = 1
  zero  = 0

instance RealFloat r => NoetherianRing (Complex r) where
  (.+.) = (+)
  (.*.) = (*)
  neg   = negate
  one   = 1
  zero  = 0

(.*) :: NoetherianRing r => r -> Ideal r -> Ideal r
c .* xs = mapIdeal (c .*.) xs

data Ideal r = forall n. Ideal (Vector r n)

instance Eq r => Eq (Ideal r) where
  (==) = (==) `on` generators

instance Ord r => Ord (Ideal r) where
  compare = comparing generators

instance Show r => Show (Ideal r) where
  show = show . generators

addToIdeal :: r -> Ideal r -> Ideal r
addToIdeal i (Ideal is) = Ideal (i :- is)

toIdeal :: NoetherianRing r => [r] -> Ideal r
toIdeal = foldr addToIdeal (Ideal Nil)

appendIdeal :: Ideal r -> Ideal r -> Ideal r
appendIdeal (Ideal is) (Ideal js) = Ideal (is `appendV` js)

generators :: Ideal r -> [r]
generators (Ideal is) = toList is

filterIdeal :: NoetherianRing r => (r -> Bool) -> Ideal r -> Ideal r
filterIdeal p (Ideal i) = foldrV (\h -> if p h then addToIdeal h else id) (toIdeal []) i

principalIdeal :: r -> Ideal r
principalIdeal = Ideal . singletonV

mapIdeal :: (r -> r') -> Ideal r -> Ideal r'
mapIdeal fun (Ideal xs) = Ideal $ mapV fun xs
