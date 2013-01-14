{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
module NoetherianRing (Ideal(..), NoetherianRing(..)) where
import Data.Complex
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

-- | An ideal of noehterian ring R.
newtype Ideal r = Ideal { generators :: [r] }
    deriving (Show, Eq, Ord)

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
