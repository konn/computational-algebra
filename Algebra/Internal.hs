{-# LANGUAGE CPP, DataKinds, EmptyDataDecls, ExplicitNamespaces            #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs, KindSignatures    #-}
{-# LANGUAGE MultiParamTypeClasses, PatternSynonyms, PolyKinds, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TypeFamilies         #-}
{-# LANGUAGE TypeOperators                                                 #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Algebra.Internal
       (  (:~:)(..), withRefl,
          module Data.Proxy,
          module Algebra.Internal) where
import           Algebra.Instances            ()

import AlgebraicPrelude
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
                                                                   sIndex,generate,
                                                                   singleton,
                                                                   unsafeFromList,
                                                                   unsafeFromList',
                                                                   zipWithSame)
import qualified Data.Sized.Builtin           as S
import qualified Data.Sized.Flipped           as Flipped (Flipped (..))
import           Data.Type.Equality           ((:~:) (..))
import           Data.Type.Natural.Class      as Algebra.Internal
import qualified Data.Type.Ordinal            as O
import qualified Data.Vector                  as DV
import           GHC.TypeLits                 as Algebra.Internal
import           Proof.Equational             (coerce, withRefl)
import           Proof.Equational             as Algebra.Internal (because,
                                                                   coerce,
                                                                   start, (===),
                                                                   (=~=))
import           Proof.Propositional          as Algebra.Internal (IsTrue (..),
                                                                   withWitness)
import qualified Data.Foldable as F
import qualified Data.Sequence as Seq
import Data.Kind (Type)

toProxy :: a -> Proxy a
toProxy _ = Proxy

type Sized n a = S.Sized DV.Vector n a
type Sized' n a = S.Sized Seq.Seq n a

coerceLength :: n :~: m -> S.Sized f n a -> S.Sized f m a
coerceLength eql = _Unwrapping Flipped.Flipped %~ coerce eql

type SNat (n :: Nat) = Sing n

sizedLength f = (S.sLength f)

padVecs :: forall a n m. a -> Sized' n a -> Sized' m a
        -> (SNat (Max n m), Sized' (Max n m) a, Sized' (Max n m) a)
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
      SFalse -> withWitness (notLeqToLeq n m) $
        let maxISn = geqToMax n m Witness
            mPLUSk :: m :+ (n :- m) :~: Max n m
            mPLUSk = start (m %:+ (n %:- m))
                       === n %:- m %:+ m `because` plusComm m (n %:- m)
                       === n             `because` minusPlus n m Witness
                       === sMax n m      `because` maxISn
        in (l,
            coerceLength maxISn xs,
            coerceLength mPLUSk $ ys S.++ S.replicate (n %:- m) d)

type family Flipped f a :: Nat -> Type where
  Flipped f a = Flipped.Flipped f a

pattern Flipped :: S.Sized f n a -> Flipped f a n
pattern Flipped xs = Flipped.Flipped xs


pattern OLt :: forall (t :: Nat). ()
            => forall (n1 :: Nat).
               ((n1 :< t) ~ 'True)
            => Sing n1 -> O.Ordinal t
pattern OLt n = O.OLt n

sNatToInt :: SNat n -> Int
sNatToInt = fromInteger . fromSing

instance Hashable a => Hashable (Seq.Seq a) where
  hashWithSalt d = hashWithSalt d . F.toList
