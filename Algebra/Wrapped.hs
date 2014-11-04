{-# LANGUAGE ConstraintKinds, DataKinds, DefaultSignatures                  #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs                     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses              #-}
{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings, ParallelListComp #-}
{-# LANGUAGE PolyKinds, ScopedTypeVariables, StandaloneDeriving             #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, TypeSynonymInstances            #-}
{-# LANGUAGE UndecidableInstances                                           #-}
{-# OPTIONS_GHC -fwarn-name-shadowing #-}
module Algebra.Wrapped (WrappedField(..), Normed(..), fmapUnwrap, fmapWrap) where
import           Control.Lens
import           Data.Complex
import qualified Data.Ratio               as P
import           Numeric.Algebra          hiding ((/), (<))
import qualified Numeric.Algebra          as NA
import           Numeric.Domain.Euclidean (Euclidean)
import           Numeric.Field.Fraction   (Fraction, numerator, (%))
import           Numeric.Field.Fraction   (denominator)
import           Prelude                  hiding (lex, negate, recip, sum, (*),
                                           (+), (-), (^), (^^))
import qualified Prelude                  as P
import           Unsafe.Coerce

newtype WrappedField a = WrapField { unwrapField :: a
                                   } deriving (Read, Show, Eq, Ord)


makeWrapped ''WrappedField

deriving instance Commutative r => Commutative (WrappedField r)
deriving instance Ring r => Ring (WrappedField r)
deriving instance Additive r => Additive (WrappedField r)
deriving instance Multiplicative r => Multiplicative (WrappedField r)
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

class Ord (Norm a) => Normed a where
  type Norm a
  norm :: a -> Norm a
  liftNorm :: Norm a -> a

instance Normed a => Normed (WrappedField a) where
  type Norm (WrappedField a) = Norm a
  norm = norm . unwrapField
  liftNorm = WrapField . liftNorm

instance Normed Double where
  type Norm Double = Double
  norm a = abs a
  liftNorm = id

instance Normed Int where
  type Norm Int = Int
  norm = abs
  liftNorm = id

instance Normed Integer where
  type Norm Integer = Integer
  norm = abs
  liftNorm = id

instance (Ord (Norm d), Euclidean d, Euclidean (Norm d),
          Normed d, Multiplicative (Norm d)) =>  Normed (Fraction d) where
  type Norm (Fraction d) = Fraction (Norm d)
  norm f = norm (numerator f) % norm (denominator f)
  liftNorm f = liftNorm (numerator f) % liftNorm (denominator f)

instance (Monoidal a, Normed a, Additive (Norm a)) => Normed (Complex a) where
  type Norm (Complex a) = Norm a
  norm (a :+ b) = norm a + norm b
  liftNorm = (:+ zero) . liftNorm

instance (Eq r, Division r, Group r, Ring r, Normed r)
         => Num (WrappedField r) where
  WrapField a + WrapField b = WrapField $ a + b
  WrapField a - WrapField b = WrapField $ a - b
  WrapField a * WrapField b = WrapField $ a * b
  negate = _Unwrapping WrapField %~ negate
  fromInteger = WrapField . NA.fromInteger
  abs n = liftNorm (norm n)
  signum n | abs n == zero = zero
           | otherwise = n NA./ abs n

instance (Normed r, Eq r, Ring r, Division r, Group r) => Fractional (WrappedField r) where
  WrapField a / WrapField b = WrapField $ a NA./ b
  recip (WrapField a) = WrapField $ NA.recip a
  fromRational q = WrapField $ NA.fromInteger (P.numerator q) NA./ NA.fromInteger (P.denominator q)

fmapUnwrap :: Functor f => f (WrappedField r) -> f r
fmapUnwrap = unsafeCoerce

fmapWrap :: Functor f => f r -> f (WrappedField r)
fmapWrap = unsafeCoerce

{-# RULES
"fmap/unwrap" forall (x :: Functor f => f (WrappedField r)) . fmap unwrapField x = fmapUnwrap x
"fmap/wrap"   forall (x :: Functor f => f r) . fmap WrapField   x = fmapWrap x
  #-}
