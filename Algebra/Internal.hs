{-# LANGUAGE CPP, DataKinds, ExplicitNamespaces, FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances, GADTs, KindSignatures                      #-}
{-# LANGUAGE MultiParamTypeClasses, PatternSynonyms, PolyKinds, RankNTypes #-}
{-# LANGUAGE StandaloneDeriving, TypeFamilies, TypeOperators               #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Algebra.Internal
       (  (:~:)(..), gcastWith,
          module Data.Proxy, WrappedField(..)
       ,  module Algebra.Internal) where
import           Algebra.Instances            ()
import           Algebra.Wrapped
import           Control.Lens                 ((%~), _Unwrapping)
import           Data.Proxy
import           Data.Singletons
import           Data.Singletons.Prelude      as Algebra.Internal (PNum (..),
                                                                   SNum (..),
                                                                   SingI (..),
                                                                   SingKind (..),
                                                                   SomeSing (..),
                                                                   withSingI)
import           Data.Singletons.Prelude.Enum as Algebra.Internal (PEnum (..),
                                                                   SEnum (..))
import           Data.Singletons.TypeLits     as Algebra.Internal (KnownNat,
                                                                   withKnownNat)
import           Data.Sized.Builtin           as Algebra.Internal (pattern (:<),
                                                                   pattern (:>),
                                                                   pattern NilL,
                                                                   pattern NilR,
                                                                   sIndex,
                                                                   singleton,
                                                                   unsafeFromList,
                                                                   unsafeFromList',
                                                                   zipWithSame)
import qualified Data.Sized.Builtin           as S
import           Data.Sized.Flipped           (Flipped (..))
import           Data.Type.Equality           ((:~:) (..), gcastWith)
import           Data.Type.Natural.Class      as Algebra.Internal
import qualified Data.Vector                  as DV
import           GHC.TypeLits                 as Algebra.Internal
import           Proof.Equational             (coerce)
import           Proof.Propositional          as Algebra.Internal (IsTrue (..))

toProxy :: a -> Proxy a
toProxy _ = Proxy

type Vector a n = S.Sized DV.Vector n a
type Sized n a = S.Sized DV.Vector n a

coerceLength :: n :~: m -> Sized n a -> Sized m a
coerceLength eql = _Unwrapping Flipped %~ coerce eql

type SNat (n :: Nat) = Sing n

sizedLength :: Sized n a -> SNat n
sizedLength = S.sLength

generate :: SNat n -> (S.Ordinal n -> a) -> Sized n a
generate n f =
  withKnownNat n $
  S.unsafeToSized' $
  DV.generate (fromInteger $ fromSing n) (f . toEnum)
