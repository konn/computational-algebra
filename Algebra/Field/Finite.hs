{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Algebra.Field.Finite where
import Data.Type.Natural
import Data.Typeable
import Data.Proxy
import Data.Reflection hiding (Z(..))

newtype PField (n :: Nat) = PF Integer deriving (Eq)

instance Show (PField n) where
    showsPrec d (PF n) = showsPrec d n

instance Reifies Z Integer where
  reflect _ = 0

instance Reifies (n :: Nat) Integer => Reifies (S n) Integer where
  reflect (_ :: proxy (S n)) = reflect (Proxy :: Proxy n) + 1

instance Reifies n Integer => Num (PField n) where
  fromInteger n = PF $ n `mod` reflect (Proxy :: Proxy n)
  PF n + PF m   = PF $ fromInteger $ n + m
  PF n * PF m   = PF $ fromInteger $ n * m
  PF n - PF m   = PF $ fromInteger $ n - m
  negate (PF n) = PF $ fromInteger $ negate n
  abs a         = a
  signum _      = 1

char :: Reifies n Integer => PField n -> Integer
char = reflect
