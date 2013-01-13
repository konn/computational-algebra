module Field ( Field(..), module NoetherianRing ) where
import Data.Complex
import Data.Ratio
import NoetherianRing

class NoetherianRing r => Field r where
  -- | Multiplicative inverse for the element (except zero).
  inv :: r -> r

instance Field Double where
  inv = recip

instance Field Float where
  inv = recip

instance Integral r => Field (Ratio r) where
  inv = recip

instance RealFloat r => Field (Complex r) where
  inv = recip
