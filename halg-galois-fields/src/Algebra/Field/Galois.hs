#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 810
{-# LANGUAGE StandaloneKindSignatures #-}
#endif
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP, DataKinds, DerivingStrategies, FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving      #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction          #-}
{-# LANGUAGE ParallelListComp, PolyKinds, QuasiQuotes, RankNTypes      #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TypeApplications #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances         #-}
{-# LANGUAGE UndecidableSuperClasses                                   #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Algebra.Field.Galois
  ( GF'(), IsGF', modPoly, modVec,
    withIrreducible, linearRepGF, linearRepGF',
    reifyGF', generateIrreducible,
    withGF', GF, ConwayPolynomial(..),
    Conway, primitive, primitive', conway,
    conwayFile, addConwayPolynomials
  )  where
import Algebra.Field.Galois.Conway
import Algebra.Field.Prime
import Algebra.Instances ()
import Algebra.Internal
import Algebra.Prelude.Core               hiding (varX)
import Algebra.Ring.Polynomial.Univariate

import           Control.DeepSeq
import           Control.Lens         (imap)
import           Control.Monad.Loops  (iterateUntil)
import           Control.Monad.Random (MonadRandom, getRandom, runRand)
import           Control.Monad.Random (Random (..), getRandomR)
import           Data.Kind            (Type)
import qualified Data.Ratio           as Rat
import           Data.Reflection      (Reifies (..), reify)
import qualified Data.Sized.Builtin   as SV
import qualified Data.Sized.Builtin   as Sized
import qualified Data.Vector          as V
import qualified GHC.TypeLits         as TL
import qualified Numeric.Algebra      as NA
import qualified Prelude              as P
import Control.Subcategory (CZip, Dom)
import qualified Data.Vector.Primitive as Prim
import Data.Singletons.TH (sCases)
import qualified Data.Vector.Generic as G
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.Coerce as DC
import Control.Subcategory.Foldable (CFreeMonoid)
import Control.Subcategory.Foldable (CFoldable(call))
import Control.Subcategory (CTraversable(ctraverse))

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 810
type GFSized :: forall k. forall (p :: k) -> Type -> Type
#endif
type GFSized (p :: k) = Sized.Sized (GFSized' k p)

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 810
type GFSized' :: forall k (p :: k) -> Nat -> Type -> Nat
#endif
type family GFSized' k (p :: k) where
  GFSized' Nat p = GFSized_Aux (WORD_MAX_BOUND <=? p)
  GFSized' k p = V.Vector

type family GFSized_Aux a where
  GFSized_Aux 'True = V.Vector
  GFSized_Aux 'False = Prim.Vector

-- | Galois field of order @p^n@.
--   @f@ stands for the irreducible polynomial over @F_p@ of degree @n@.
newtype GF' p (n :: TL.Nat) (f :: Type) = GF' { runGF' :: GFSized p n (F p) }

deriving newtype instance
  NFData (F (p :: Type)) => NFData (GF' p n f)

instance
  (SingI (WORD_MAX_BOUND <=? p), NFData (F p)) => NFData (GF' p n f) 
  where
    rnf = 
      $(sCases ''Bool [|sing :: Sing (WORD_MAX_BOUND <=? p)|]
        [|rnf . runGF'|])


instance (IsPrimeChar (p :: Nat), SingI (WORD_MAX_BOUND <=? p))
  => Eq (GF' p n f) where
  (==) =
    $(sCases ''Bool [|sing :: Sing (WORD_MAX_BOUND <=? p)|]
        [|(==) `on` runGF'|])
deriving instance IsPrimeChar (p :: Type) => Eq (GF' p n f)

-- | Galois Field of order @p^n@. This uses conway polynomials
--   as canonical minimal polynomial and it should be known at
--   compile-time (i.e. @Reifies (Conway p n) (Unipol (F n))@
--   instances should be defined to use field operations).
type GF (p :: TL.Nat) n = GF' p n (Conway p n)

modPoly :: forall k (p :: k) n f. 
  ( KnownNat n, IsPrimeChar p,
    G.Vector (GFSized' k p) (F p),
    CFreeMonoid (GFSized' k p), 
    Dom (GFSized' k p) (F p)
  )
  => Unipol (F p) -> GF' p n f
modPoly = GF' . polyToVec

modVec :: SV.Sized (GFSized' k p) n (F p) -> GF' p n f
modVec = GF'


instance (IsGF' p n f, Show (F p))
  => Show (GF' p n f)  where
  showsPrec d (GF' (v SV.:< vs)) =
    if call isZero vs
    then showsPrec d v
    else showChar '<' . showString (showPolynomialWith (singleton "ξ") 0 $ vecToPoly $ v :< vs) . showChar '>'
  showsPrec _ _ = showString "0"

instance (IsGF' p n f) => PrettyCoeff (GF' p n f)

varX :: CoeffRing r => Unipol r
varX = var [od|0|]

vecToPoly :: (CoeffRing r, G.Vector v r)
          => Sized.Sized v n r -> Unipol r
vecToPoly v = sum $ imap (\i c -> injectCoeff c * varX^fromIntegral i)
  $ G.toList $ SV.unsized v

{-# SPECIALISE INLINE polyToVec
  :: forall n (p :: Nat). (KnownNat n, IsPrimeChar p)
  => Unipol (F p) -> SV.Sized V.Vector n (F p)
  #-}
{-# SPECIALISE INLINE polyToVec
  :: forall n (p :: Nat). 
    ( KnownNat n, IsPrimeChar p, Prim.Prim (F p)
    )
  => Unipol (F p) -> SV.Sized Prim.Vector n (F p)
  #-}
polyToVec :: forall n r v.
  (CoeffRing r, KnownNat n, G.Vector v r, CFreeMonoid v, Dom v r)
  => Unipol r -> SV.Sized v n r
polyToVec f =
  case zeroOrSucc (sing :: SNat n) of
    IsZero -> SV.empty
    IsSucc _ ->
      unsafeFromList'
        [ coeff (OrderedMonomial $ SV.singleton i) f
        | i <- [0..fromIntegral (fromSing (sing :: SNat n)) P.- 1]
        ]

mapSV
  :: forall f n a b.
    (CFreeMonoid f, Dom f a, Dom f b)
  => (a -> b) -> SV.Sized f n a -> SV.Sized f n b
{-# INLINE [1] mapSV #-}
mapSV = SV.map

{-# SPECIALISE mapSV
  :: (F p -> F p) -> Sized n (F p) -> Sized n (F p) #-}
{-# SPECIALISE mapSV
  :: Prim.Prim (F p)
  => (F p -> F p) -> SV.Sized Prim.Vector n (F p) -> SV.Sized Prim.Vector n (F p)
  #-}
{-# SPECIALISE mapSV
  :: (F 2 -> F 2) -> SV.Sized Prim.Vector n (F 2) -> SV.Sized Prim.Vector n (F 2)
  #-}
{-# SPECIALISE mapSV
  :: (F 3 -> F 3) -> SV.Sized Prim.Vector n (F 3) -> SV.Sized Prim.Vector n (F 3)
  #-}

zipWithSameSV
  :: forall f a b c n.
    ( CZip f, CFreeMonoid f, Dom f a, Dom f b, Dom f c
    )
  => (a -> b -> c) -> SV.Sized f n a -> SV.Sized f n b -> SV.Sized f n c
{-# INLINE [2] zipWithSameSV #-}
zipWithSameSV = SV.zipWithSame

zipWithFpPrim
  :: forall p n. Prim.Prim (F p) => 
    (F p -> F p -> F p)
  -> SV.Sized Prim.Vector n (F p)
  -> SV.Sized Prim.Vector n (F p)  
  -> SV.Sized Prim.Vector n (F p)
zipWithFpPrim = unsafeCoerce $ Prim.zipWith @(F p) @(F p) @(F p)

zipWithFpBoxed
  :: forall p n. 
    (F p -> F p -> F p)
  -> SV.Sized V.Vector n (F p)
  -> SV.Sized V.Vector n (F p)  
  -> SV.Sized V.Vector n (F p)
zipWithFpBoxed = unsafeCoerce $ V.zipWith @(F p) @(F p) @(F p)
{-# RULES
"zipWith/Fp/Boxed" [~2]
  zipWithSameSV = zipWithFpBoxed

"zipWith/Fp/Prim" [~2]
  forall (f :: Prim.Prim (F p) => F p -> F p -> F p).
  zipWithSameSV f = zipWithFpPrim f

"zipWith/Fp/Prim/F 2" [~2]
  zipWithSameSV = zipWithFpPrim @2

"zipWith/Fp/Prim/F 3" [~2]
  zipWithSameSV = zipWithFpPrim @3
  #-}

instance IsGF' p n f => Additive (GF' p n f)  where
  (+) = DC.coerce $ zipWithSameSV @(GFSized' _ p) @(F p) @(F p) @(F p) @n (+)
  {-# INLINE (+) #-}

instance (IsGF' p n f) => Monoidal (GF' p n f) where
  zero = GF' $ SV.replicate' zero

instance (IsGF' p n f) => LeftModule Natural (GF' p n f) where
  n .* GF' v = GF' $ mapSV (n .*) v

instance (IsGF' p n f) => RightModule Natural (GF' p n f) where
  GF' v *. n = GF' $ mapSV (*. n) v

instance (IsGF' p n f) => LeftModule Integer (GF' p n f) where
  n .* GF' v = GF' $ mapSV (n .*) v

instance (IsGF' p n f) => RightModule Integer (GF' p n f) where
  GF' v *. n = GF' $ mapSV (*. n) v

instance (IsGF' p n f) => Group (GF' p n f) where
  negate (GF' v) = GF' $ mapSV negate v
  GF' u - GF' v  = GF' $ zipWithSameSV (-) u v

instance (IsGF' p n f) => Abelian (GF' p n f)

instance (IsGF' p n f)
      => Multiplicative (GF' p n f) where
  GF' u * GF' v =
    let t = (vecToPoly u * vecToPoly v) `rem` reflect (Proxy :: Proxy f)
    in GF' $ polyToVec t

instance (IsGF' p n f) => Unital (GF' p n f) where
  one =
    case zeroOrSucc (sing :: SNat n) of
      IsZero   -> GF' NilL
      IsSucc k -> withKnownNat k $ GF' $ one :< SV.replicate' zero

instance (IsGF' p n f) => Semiring (GF' p n f)

instance (IsGF' p n f) => Rig (GF' p n f) where
  fromNatural n =
    case zeroOrSucc (sing :: SNat n) of
      IsZero -> GF' SV.empty
      IsSucc k -> withKnownNat k $ GF' $ fromNatural n :< SV.replicate' zero

instance (IsGF' p n f) => Commutative (GF' p n f)

instance (IsGF' p n f) => Ring (GF' p n f) where
  fromInteger n =
    case zeroOrSucc (sing :: SNat n) of
      IsZero   -> GF' NilL
      IsSucc k -> withKnownNat k $ GF' $ fromInteger n :< SV.replicate' zero

instance (IsGF' p n f) => DecidableZero (GF' p n f) where
  isZero (GF' sv) = call isZero sv

instance (IsGF' p n f) => DecidableUnits (GF' p n f) where
  isUnit (GF' sv) = not $ call isZero sv
  recipUnit a | isZero a = Nothing
              | otherwise = Just $ recip a

instance (IsGF' p n f)
      => Characteristic (GF' p n f) where
  char _ = char (Proxy :: Proxy (F p))

instance (IsGF' p n f)
      => Division (GF' p n f) where
  recip f =
    let p = reflect (Proxy :: Proxy f)
        (_,_,r) = P.head $ euclid p $ vecToPoly $ runGF' f
    in GF' $ polyToVec $ r `rem` p

instance (IsGF' p n f)
      => DecidableAssociates (GF' p n f) where
  isAssociate p n =
    (isZero p && isZero n) || (not (isZero p) && not (isZero n))
instance (IsGF' p n f)
      => ZeroProductSemiring (GF' p n f)
instance (IsGF' p n f)
      => UnitNormalForm (GF' p n f)
instance (IsGF' p n f)
      => IntegralDomain (GF' p n f)
instance (IsGF' p n f)
      => GCDDomain (GF' p n f)
instance (IsGF' p n f)
      => UFD (GF' p n f)
instance (IsGF' p n f)
      => PID (GF' p n f)
instance (IsGF' p n f)
      => Euclidean (GF' p n f)

instance (IsGF' p n f) => P.Num (GF' p n f) where
  (+) = (NA.+)
  (-) = (NA.-)
  negate = NA.negate
  (*) = (NA.*)
  fromInteger = NA.fromInteger
  abs = error "not defined"
  signum = error "not defined"

instance (IsGF' p n f) => P.Fractional (GF' p n f) where
  fromRational u = fromInteger (Rat.numerator u) / fromInteger (Rat.denominator u)
  (/) = (/)
  recip = recip

-- | @generateIrreducible p n@ generates irreducible polynomial over F_@p@ of degree @n@.
generateIrreducible :: (MonadRandom m, Random k, FiniteField k, Eq k)
                    => proxy k -> Natural -> m (Unipol k)
generateIrreducible p n =
  iterateUntil (\f -> all (\i -> one == gcd (varX^(order p^i) - varX) f ) [1.. n `div` 2]) $ do
    cs <- replicateM (fromIntegral n) getRandom
    let f = varX^n + sum [ injectCoeff c * (varX^i) | c <- cs | i <- [0..n P.- 1]]
    return f

withIrreducible
  :: forall p a.
    ( IsPrimeChar (p :: k),
      G.Vector (GFSized' k p) (F p),
      CFreeMonoid (GFSized' k p),
      CTraversable (GFSized' k p),
      Monoid (GFSized' k p (F p)),
      CZip (GFSized' k p),
      Dom (GFSized' k p) (F p)
    )
  => Unipol (F p)
  -> (forall f (n :: Nat). (IsGF' p n f) => Proxy (GF' p n f) -> a)
  -> a
withIrreducible r f =
  case toSing (fromIntegral $ totalDegree' r) of
    SomeSing sn ->
      withKnownNat sn $
      reify r (f . proxyGF' (Proxy :: Proxy (F p)) sn)

reifyGF'
  :: MonadRandom m 
  => Natural -> Natural
  -> (forall (p :: TL.Nat) (f :: Type) (n :: TL.Nat) . (IsGF' p n f)
                => Proxy (GF' p n f) -> a)
  -> m a
reifyGF' p n f = reifyPrimeField (P.toInteger p) $ \(pxy :: Proxy (F p)) -> do
  let sp = sing :: SNat p
  mpol <- generateIrreducible pxy n
  case toSing (fromIntegral n) of
    SomeSing (sn :: SNat n) ->
      let cond :: Sing (WORD_MAX_BOUND <=? p)
          cond = unsafeCoerce ((sing :: Sing WORD_MAX_BOUND) %<= sp) 
      in case cond of
        STrue -> withKnownNat sp
          $ withKnownNat sn
          $ return $ withIrreducible mpol f
        SFalse -> withKnownNat sp
          $ withKnownNat sn
          $ return $ withIrreducible mpol f

linearRepGF :: (IsGF' p n f) => GF' p n f -> V.Vector (F p)
linearRepGF = G.convert . SV.unsized . runGF'

linearRepGF' :: (IsGF' p n f) => GF' p n f -> V.Vector Integer
linearRepGF' = V.map naturalRepr . linearRepGF

withGF' :: MonadRandom m
        => Natural -> Natural
        -> (forall (p :: TL.Nat) f (n :: TL.Nat) . (IsGF' p n f)
            => GF' p n f)
        -> m (V.Vector Integer)
withGF' p n f = reifyGF' p n $ V.map naturalRepr . linearRepGF . asProxyTypeOf f

proxyGF' :: Proxy (F p) -> SNat n -> Proxy f -> Proxy (GF' p n f)
proxyGF' _ _ Proxy = Proxy

-- | Type-constraint synonym to work with Galois field.
class 
  ( KnownNat n, IsPrimeChar p, Reifies f (Unipol (F p)),
    G.Vector (GFSized' k p) (F p),
    CTraversable (GFSized' k p),
    CFreeMonoid (GFSized' k p),
    Monoid (GFSized' k p (F p)),
    CZip (GFSized' k p),
    Dom (GFSized' k p) (F p)
  )
  => IsGF' (p :: k) n f
instance
  ( KnownNat n, IsPrimeChar p, Reifies f (Unipol (F p)),
    G.Vector (GFSized' k p) (F p),
    CTraversable (GFSized' k p),
    CZip (GFSized' k p),
    CFreeMonoid (GFSized' k p),
    Dom (GFSized' k p) (F p),
    Monoid (GFSized' k p (F p))
  )
  => IsGF' (p :: k) n f


instance (KnownNat n, IsGF' p n f) => FiniteField (GF' p n f) where
  power _ = fromIntegral $ fromSing (sing :: SNat n)
  elements _ =
    let sn = sing :: SNat n
    in P.map (GF' . SV.unsafeToSized') $ ctraverse (const $ elements Proxy)
      $ SV.unsized
      $ SV.replicate sn (0 :: F p)

primitive' :: forall p n f. (IsGF' p n f, (n >= 1) ~ 'True) => GF' p n f
primitive' = withKnownNat (sSucc (sing :: SNat n)) $ GF' $ polyToVec $ var [od|0|]

primitive :: forall p n. (IsGF' p n (Conway p n), (n >= 1) ~ 'True) => GF p n
primitive = primitive'

-- | Conway polynomial (if definition is known).
conway :: forall p n. ConwayPolynomial p n
       => SNat p -> SNat n -> Unipol (F p)
conway = conwayPolynomial

instance IsGF' p n f => Random (GF' p n f) where
  random = runRand $
    GF' . hoistSized
    <$> ctraverse (const getRandom) (SV.replicate  @V.Vector(sing :: SNat n) (0 :: Int))
  randomR (GF' ls, GF' rs) = runRand $
    GF' . hoistSized <$> sequence 
      (zipWithSameSV (curry getRandomR) 
          (hoistSized @V.Vector ls)
          (hoistSized @V.Vector rs))

hoistSized
  :: forall g f n a. 
      ( G.Vector f a, G.Vector g a, KnownNat n,
        Dom f a, Dom g a
      )
  => SV.Sized f n a -> SV.Sized g n a
{-# INLINE hoistSized #-}
hoistSized = SV.unsafeToSized' . G.convert . SV.unsized
