{-# LANGUAGE DataKinds, ExistentialQuantification, FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances                                           #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Algebra.Ring.Noetherian ( NoetherianRing, Ideal(..), addToIdeal, toIdeal, appendIdeal
                               , generators, filterIdeal, mapIdeal, principalIdeal) where
import qualified Data.Complex            as C
import           Data.Function
import           Data.Ord
import           Data.Ratio
import           Data.Vector.Sized       (Vector (..))
import qualified Data.Vector.Sized       as V
import           Numeric.Algebra
import qualified Numeric.Algebra.Complex as NA
import           Prelude                 hiding (negate, subtract, (*), (+),
                                          (-))
import qualified Prelude                 as P

class (Commutative r, Ring r) => NoetherianRing r where

instance NoetherianRing Int where

instance NoetherianRing Integer where

instance (Commutative (NA.Complex r), Ring (NA.Complex r)) => NoetherianRing (NA.Complex r) where
instance (Commutative (C.Complex r), Ring (C.Complex r)) => NoetherianRing (C.Complex r) where
instance Integral n => NoetherianRing (Ratio n)

instance Integral n => InvolutiveMultiplication (Ratio n) where
  adjoint = id
instance Integral n => InvolutiveSemiring (Ratio n)

instance Integral n => TriviallyInvolutive (Ratio n)

instance (P.Num n) => P.Num (NA.Complex n) where
  abs = error "unimplemented"
  signum = error "unimplemented"
  fromInteger n = NA.Complex (P.fromInteger n) 0
  negate (NA.Complex x y) = NA.Complex (P.negate x) (P.negate y)
  NA.Complex x y + NA.Complex z w = NA.Complex (x P.+ y) (z P.+ w)
  NA.Complex x y * NA.Complex z w = NA.Complex (x P.* z P.- y P.* w) (x P.* w P.+ y P.* z)

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

instance Integral n => LeftModule (Ratio n) (Ratio n) where
    (.*) = (*)

instance Integral n => RightModule (Ratio n) (Ratio n) where
    (*.) = (*)

data Ideal r = forall n. Ideal (V.Vector r n)

instance Eq r => Eq (Ideal r) where
  (==) = (==) `on` generators

instance Ord r => Ord (Ideal r) where
  compare = comparing generators

instance Show r => Show (Ideal r) where
  show = show . generators

addToIdeal :: (Monoidal r, Eq r) => r -> Ideal r -> Ideal r
addToIdeal i (Ideal is)
    | i == zero = Ideal is
    | otherwise = Ideal (i :- is)

infixr `addToIdeal`

toIdeal :: (Eq r, NoetherianRing r) => [r] -> Ideal r
toIdeal = foldr addToIdeal (Ideal Nil)

appendIdeal :: Ideal r -> Ideal r -> Ideal r
appendIdeal (Ideal is) (Ideal js) = Ideal (is `V.append` js)

generators :: Ideal r -> [r]
generators (Ideal is) = V.toList is

filterIdeal :: (Eq r, NoetherianRing r) => (r -> Bool) -> Ideal r -> Ideal r
filterIdeal p (Ideal i) = V.foldr (\h -> if p h then addToIdeal h else id) (toIdeal []) i

principalIdeal :: r -> Ideal r
principalIdeal = Ideal . V.singleton

mapIdeal :: (r -> r') -> Ideal r -> Ideal r'
mapIdeal fun (Ideal xs) = Ideal $ V.map fun xs
