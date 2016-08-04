{-# LANGUAGE CPP, DataKinds, EmptyDataDecls, ExplicitNamespaces            #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs, KindSignatures    #-}
{-# LANGUAGE MultiParamTypeClasses, PatternSynonyms, PolyKinds, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TypeFamilies         #-}
{-# LANGUAGE TypeOperators                                                 #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Algebra.Internal
       (  (:~:)(..), gcastWith,
          module Data.Proxy, WrappedField(..)
       ,  module Algebra.Internal) where
import           Algebra.Instances            ()
import           Algebra.Wrapped
import           Control.Lens                 ((%~), _Unwrapping)
import           Data.Proxy
import           Data.Singletons.Prelude      as Algebra.Internal (PNum (..),
                                                                   POrd (..),
                                                                   SNum (..),
                                                                   SOrd (..),
                                                                   Sing (SFalse, STrue),
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
import qualified Data.Sized.Flipped           as Flipped (Flipped (..))
import           Data.Type.Equality           ((:~:) (..), gcastWith)
import           Data.Type.Natural.Class      as Algebra.Internal
import qualified Data.Vector                  as DV
import           GHC.TypeLits                 as Algebra.Internal
import           Proof.Equational             (coerce)
import           Proof.Equational             as Algebra.Internal (because,
                                                                   coerce,
                                                                   start, (===),
                                                                   (=~=))
import           Proof.Propositional          as Algebra.Internal (IsTrue (..))

toProxy :: a -> Proxy a
toProxy _ = Proxy

type Vector a n = S.Sized DV.Vector n a
type Sized n a = S.Sized DV.Vector n a

coerceLength :: n :~: m -> Sized n a -> Sized m a
coerceLength eql = _Unwrapping Flipped.Flipped %~ coerce eql

type SNat (n :: Nat) = Sing n

sizedLength :: Sized n a -> SNat n
sizedLength = S.sLength

generate :: SNat n -> (S.Ordinal n -> a) -> Sized n a
generate n f =
  withKnownNat n $
  S.unsafeToSized' $
  DV.generate (fromInteger $ fromSing n) (f . toEnum)

padVecs :: forall a n m. a -> Sized n a -> Sized m a
        -> (SNat (Max n m), Sized (Max n m) a, Sized (Max n m) a)
padVecs d xs ys
  = let (n, m) = (S.sLength xs, S.sLength ys)
        l = sMax n m
    in case n %:<= m of
      STrue ->
        let maxISm = leqToMax n m Witness
            k      = m %:- n
            nPLUSk = start (n %:+ (m %:- n))
                       === m %:- n %:+ n `because` plusComm n (m %:- n)
                       === m `because` minusPlus m n Witness
                       === sMax n m `because` maxISm
        in (l,
            coerceLength nPLUSk (xs S.++ S.replicate k d),
            coerceLength maxISm ys)
      SFalse ->
        case notLeqToLeq n m of
          Witness ->
            let maxISn = geqToMax n m Witness
                mPLUSk :: m :+ (n :- m) :~: Max n m
                mPLUSk = start (m %:+ (n %:- m))
                           === n %:- m %:+ m `because` plusComm m (n %:- m)
                           === n             `because` minusPlus n m Witness
                           === sMax n m      `because` maxISn
            in (l,
                coerceLength maxISn xs,
                coerceLength mPLUSk $ ys S.++ S.replicate (n %:- m) d)

type family Flipped a :: Nat -> * where
  Flipped a = Flipped.Flipped DV.Vector a

pattern Flipped :: Sized n a -> Flipped a n
pattern Flipped xs = Flipped.Flipped xs

sNatToInt :: SNat n -> Int
sNatToInt = fromInteger . fromSing
