{-# LANGUAGE DataKinds, ExistentialQuantification, FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances                                           #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Algebra.Ring.Noetherian ( NoetherianRing, Ideal(..), addToIdeal, toIdeal, appendIdeal
                               , generators, filterIdeal, mapIdeal, principalIdeal) where
import           Algebra.Internal
import           Data.Complex
import           Data.Function
import           Data.Ord
import           Data.Ratio
import           Numeric.Algebra
import           Prelude          hiding ((*), (+), (-), subtract, negate)
import qualified Prelude          as P

class (Commutative r, Ring r) => NoetherianRing r where

instance NoetherianRing Int where

instance NoetherianRing Integer where

instance (Commutative (Complex r), Ring (Complex r)) => NoetherianRing (Complex r) where
instance Integral n => NoetherianRing (Ratio n)

instance Division (Ratio Integer) where
  recip = P.recip
  (/)   = (P./)
  (\\)  = flip (P./)
  (^)   = (^^)

instance Integral n => Commutative (Ratio n)

instance Integral n => Ring (Ratio n) where
  fromInteger = P.fromInteger
instance Integral n => Rig (Ratio n) where
  fromNatural = P.fromInteger . toInteger
instance Integral n => Monoidal (Ratio n) where
  zero = 0
instance Integral n => LeftModule Natural (Ratio n) where
  n .* r = P.sum $ replicate (fromIntegral n) r

instance Integral n => RightModule Natural (Ratio n) where
  (*.) = flip (.*)

instance Integral n => Unital (Ratio n) where
  one = 1
  pow r n = r ^^ toInteger n
instance Integral n => Group (Ratio n) where
  negate = P.negate
  times n r = toInteger n .* r
  (-) = (P.-)
  subtract = P.subtract
instance Integral n => LeftModule Integer (Ratio n) where
  n .* r = fromIntegral n P.* r
instance Integral n => RightModule Integer (Ratio n) where
  r *. n = r P.* fromIntegral n
instance Integral n => Semiring (Ratio n)
instance Integral n => Additive (Ratio n) where
  (+) = (P.+)
  sinnum1p n r = fromIntegral (n P.+ 1) P.* r
instance Integral n => Abelian (Ratio n)
instance Integral n => Multiplicative (Ratio n) where
  (*) = (P.*)
  pow1p r n = r ^^ (n P.+ 1)

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
