{-# LANGUAGE CPP, DataKinds, ExplicitNamespaces, FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances, GADTs, KindSignatures                      #-}
{-# LANGUAGE MultiParamTypeClasses, PatternSynonyms, PolyKinds, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, TypeOperators              #-}
{-# OPTIONS_GHC -Wincomplete-patterns -Wno-orphans #-}
module Algebra.Internal
       (  (:~:)(..), withRefl,
          module Data.Proxy,
          module Algebra.Internal,
          module Data.Type.Ordinal.Builtin) where
import Algebra.Instances ()

import           AlgebraicPrelude
import           Control.Lens                 ((%~), _Unwrapping)
import qualified Data.Foldable                as F
import           Data.Kind                    (Type)
import           Data.ListLike                (ListLike)
import           Data.Proxy
import qualified Data.Sequence                as Seq
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
                                                                   generate,
                                                                   sIndex,
                                                                   singleton,
                                                                   unsafeFromList,
                                                                   unsafeFromList',
                                                                   zipWithSame)
import qualified Data.Sized.Builtin           as S
import qualified Data.Sized.Flipped           as Flipped (Flipped (..))
import           Data.Type.Equality           ((:~:) (..))
import           Data.Type.Natural.Class      as Algebra.Internal hiding
                                                                   (fromNatural)
import           Data.Type.Ordinal.Builtin
import qualified Data.Vector                  as DV
import qualified Data.Vector.Unboxed          as UV
import           GHC.TypeLits                 as Algebra.Internal hiding
                                                                   (type (*),
                                                                   type (+),
                                                                   type (-),
                                                                   type (<=))
import           Proof.Equational             (coerce, withRefl)
import           Proof.Equational             as Algebra.Internal (because,
                                                                   coerce,
                                                                   start, (===),
                                                                   (=~=))
import           Proof.Propositional          as Algebra.Internal (IsTrue (..),
                                                                   withWitness)

toProxy :: a -> Proxy a
toProxy _ = Proxy

type USized n a = S.Sized UV.Vector n a
type Sized n a = S.Sized DV.Vector n a
type Sized' n a = S.Sized Seq.Seq n a

coerceLength :: n :~: m -> S.Sized f n a -> S.Sized f m a
coerceLength eql = _Unwrapping Flipped.Flipped %~ coerce eql

type SNat (n :: Nat) = Sing n

sizedLength :: ListLike (f a) a => S.Sized f n a -> Sing n
sizedLength = S.sLength

padVecs :: forall a n m. (Unbox a) => a -> USized n a -> USized m a
        -> (SNat (Max n m), USized (Max n m) a, USized (Max n m) a)
padVecs d xs ys
  = let (n, m) = (S.sLength xs, S.sLength ys)
        l = sMax n m
    in case n %<= m of
      STrue ->
        let maxISm = leqToMax n m Witness
            k      = m %- n
            nPLUSk = start (n %+ (m %- n))
                       === m %- n %+ n `because` plusComm n (m %- n)
                       === m `because` minusPlus m n Witness
                       === sMax n m `because` maxISm
        in (l,
            coerceLength nPLUSk (xs S.++ S.replicate k d),
            coerceLength maxISm ys)
      SFalse -> withWitness (notLeqToLeq n m) $
        let maxISn = geqToMax n m Witness
            mPLUSk :: m + (n - m) :~: Max n m
            mPLUSk = start (m %+ (n %- m))
                       === n %- m %+ m `because` plusComm m (n %- m)
                       === n             `because` minusPlus n m Witness
                       === sMax n m      `because` maxISn
        in (l,
            coerceLength maxISn xs,
            coerceLength mPLUSk $ ys S.++ S.replicate (n %- m) d)

type family Flipped f a :: Nat -> Type where
  Flipped f a = Flipped.Flipped f a

pattern Flipped :: S.Sized f n a -> Flipped f a n
pattern Flipped xs = Flipped.Flipped xs

sNatToInt :: SNat n -> Int
sNatToInt = fromIntegral . fromSing

instance Hashable a => Hashable (Seq.Seq a) where
  hashWithSalt d = hashWithSalt d . F.toList



