{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wincomplete-patterns -Wno-orphans #-}
{-# OPTIONS_GHC -fplugin Data.Type.Natural.Presburger.MinMaxSolver #-}

#if __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE NoStarIsType #-}
#endif

module Algebra.Internal
  ( (:~:) (..),
    withRefl,
    module Data.Proxy,
    module Algebra.Internal,
    module Data.Type.Ordinal,
  )
where

import Algebra.Instances ()
import AlgebraicPrelude
import Control.Lens (_Unwrapping)
import qualified Control.Lens as Lens
import qualified Data.Foldable as F
import Data.Kind (Type)
import Data.Proxy (KProxy (..), Proxy (..), asProxyTypeOf)
import qualified Data.Sequence as Seq
#if MIN_VERSION_singletons(3,0,0)
import Data.Singletons as Algebra.Internal
  ( Sing,
    SingI (..),
    SingKind (..),
    SomeSing (..),
    withSingI,
  )
import qualified GHC.TypeLits.Singletons as Sing
#else
import Data.Singletons.Prelude as Algebra.Internal
  ( Sing,
    SingI (..),
    SingKind (..),
    SomeSing (..),
    withSingI,
  )
import qualified Data.Singletons.TypeLits as Sing
#endif

import Data.Sized as Algebra.Internal
  ( generate,
    sIndex,
    singleton,
    unsafeFromList,
    unsafeFromList',
    zipWithSame,
    pattern Nil,
    pattern (:<),
    pattern (:>),
  )
import qualified Data.Sized as S
import qualified Data.Sized.Flipped as Flipped (Flipped (..))
import Data.Type.Equality ((:~:) (..))
import Data.Type.Natural as Algebra.Internal hiding ((%~))
import Data.Type.Natural.Lemma.Arithmetic (plusComm)
import Data.Type.Natural.Lemma.Order (geqToMax, leqToMax, minusPlus, notLeqToLeq)
import Data.Type.Ordinal
import qualified Data.Vector as DV
import qualified Data.Vector.Unboxed as UV
import Proof.Equational (coerce, withRefl)
import Proof.Equational as Algebra.Internal
  ( because,
    coerce,
    start,
    (===),
    (=~=),
  )
import Proof.Propositional as Algebra.Internal
  ( IsTrue (..),
    withWitness,
  )

toProxy :: a -> Proxy a
toProxy _ = Proxy

type USized n a = S.Sized UV.Vector n a

type Sized n a = S.Sized DV.Vector n a

type Sized' n a = S.Sized Seq.Seq n a

sNatToSingleton :: SNat n -> Sing n
sNatToSingleton sn = withKnownNat sn sing

singToSNat :: Sing n -> SNat n
singToSNat sn = Sing.withKnownNat sn sNat

coerceLength :: n :~: m -> S.Sized f n a -> S.Sized f m a
coerceLength eql = _Unwrapping Flipped.Flipped Lens.%~ coerce eql

sizedLength :: (KnownNat n, S.DomC f a) => S.Sized f n a -> SNat n
sizedLength = S.sLength

padVecs ::
  forall a n m.
  (Unbox a, KnownNat n, KnownNat m) =>
  a ->
  USized n a ->
  USized m a ->
  (SNat (Max n m), USized (Max n m) a, USized (Max n m) a)
padVecs d xs ys =
  let (n, m) = (S.sLength xs, S.sLength ys)
      l = sMax n m
   in case n %<=? m of
        STrue ->
          let maxISm = leqToMax n m Witness
              k = m %- n
              nPLUSk =
                start (n %+ (m %- n))
                  === m %- n %+ n `because` plusComm n (m %- n)
                  === m `because` minusPlus m n Witness
                  === sMax n m `because` maxISm
           in ( l
              , coerceLength nPLUSk (xs S.++ S.replicate k d)
              , coerceLength maxISm ys
              )
        SFalse ->
          withWitness (notLeqToLeq n m) $
            let maxISn = geqToMax n m Witness
                mPLUSk :: m + (n - m) :~: Max n m
                mPLUSk =
                  start (m %+ (n %- m))
                    === n %- m %+ m `because` plusComm m (n %- m)
                    === n `because` minusPlus n m Witness
                    === sMax n m `because` maxISn
             in ( l
                , coerceLength maxISn xs
                , coerceLength mPLUSk $ ys S.++ S.replicate (n %- m) d
                )

type family Flipped f a :: Nat -> Type where
  Flipped f a = Flipped.Flipped f a

pattern Flipped :: S.Sized f n a -> Flipped f a n
pattern Flipped xs = Flipped.Flipped xs

sNatToInt :: SNat n -> Int
sNatToInt = fromIntegral . toNatural

#if !MIN_VERSION_hashable(1,3,4)
instance Hashable a => Hashable (Seq.Seq a) where
  hashWithSalt d = hashWithSalt d . F.toList
#endif
