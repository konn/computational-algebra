{-# LANGUAGE ConstraintKinds, DataKinds, DefaultSignatures, FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving            #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction                #-}
{-# LANGUAGE OverloadedStrings, ParallelListComp, PolyKinds                  #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies, TypeSynonymInstances, UndecidableInstances        #-}
{-# OPTIONS_GHC -fwarn-name-shadowing #-}
module Algebra.Wrapped (WrappedField(..), Normed(..)) where
import           Algebra.Ring.Noetherian
import           Control.Lens
import           Data.Complex
import           Data.Ratio
import           Numeric.Algebra         hiding ((/), (<))
import qualified Numeric.Algebra         as NA
import           Prelude                 hiding (lex, negate, recip, sum, (*),
                                          (+), (-), (^), (^^))
import qualified Prelude                 as P

newtype WrappedField a = WrapField { unwrapField :: a
                                   } deriving (Read, Show, Eq, Ord)


makeWrapped ''WrappedField

deriving instance Commutative r => Commutative (WrappedField r)
deriving instance Ring r => Ring (WrappedField r)
deriving instance Additive r => Additive (WrappedField r)
deriving instance Multiplicative r => Multiplicative (WrappedField r)
deriving instance NoetherianRing r => NoetherianRing (WrappedField r)
deriving instance Unital r => Unital (WrappedField r)
deriving instance DecidableUnits r => DecidableUnits (WrappedField r)
deriving instance Division r => Division (WrappedField r)
deriving instance Semiring r => Semiring (WrappedField r)
deriving instance Abelian r => Abelian (WrappedField r)
deriving instance Rig r => Rig (WrappedField r)

instance LeftModule a r => LeftModule a (WrappedField r) where
  n .* WrapField r = WrapField $ n .* r

instance RightModule a r => RightModule a (WrappedField r) where
  WrapField r *. n = WrapField $ r *. n

deriving instance Monoidal r => Monoidal (WrappedField r)
deriving instance Group r => Group (WrappedField r)
deriving instance DecidableZero r => DecidableZero (WrappedField r)

class Additive (Norm a) => Normed a where
  type Norm a
  norm :: a -> Norm a
  liftNorm :: Norm a -> a

instance Normed a => Normed (WrappedField a) where
  type Norm (WrappedField a) = Norm a
  norm = norm . unwrapField
  liftNorm = WrapField . liftNorm

sq x = x*x

instance Normed Int where
  type Norm Int = Int
  norm = sq
  liftNorm = id

instance Normed Integer where
  type Norm Integer = Integer
  norm = sq
  liftNorm = id

instance Normed Rational where
  type Norm Rational = Rational
  norm = sq
  liftNorm = id

instance (Monoidal a, Normed a) => Normed (Complex a) where
  type Norm (Complex a) = Norm a
  norm (a :+ b) = norm a + norm b
  liftNorm = (:+ zero) . liftNorm

instance (Eq r, Division r, Group r, Ring r, Normed r)
         => Num (WrappedField r) where
  WrapField a + WrapField b = WrapField $ a + b
  WrapField a - WrapField b = WrapField $ a - b
  WrapField a * WrapField b = WrapField $ a * b
  negate = unwrapped %~ negate
  fromInteger = WrapField . NA.fromInteger
  abs n = liftNorm (norm n)
  signum n | abs n == zero = zero
           | otherwise = n NA./ abs n

instance (Normed r, Eq r, Ring r, Division r, Group r) => Fractional (WrappedField r) where
  WrapField a / WrapField b = WrapField $ a NA./ b
  recip (WrapField a) = WrapField $ NA.recip a
  fromRational q = WrapField $ NA.fromInteger (numerator q) NA./ NA.fromInteger (denominator q)
