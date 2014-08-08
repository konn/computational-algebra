{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, NoMonomorphismRestriction        #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables, TypeFamilies       #-}
{-# LANGUAGE UndecidableInstances                                           #-}
module Algebra.Field.Galois (GF0, modPoly, modVec, reifyGF0, withGF0,
                             GF', Conway, primitive, conway)  where
import           Algebra.Field.Finite
import           Algebra.Prelude
import           Algebra.Ring.Polynomial.Factorize
import           Control.Lens                      (imap)
import           Control.Monad.Random              (MonadRandom)
import           Data.Proxy
import qualified Data.Ratio                        as Rat
import           Data.Reflection
import           Data.Type.Monomorphic             (promote)
import           Data.Type.Monomorphic             (Monomorphic (..))
import           Data.Type.Natural                 hiding (one, promote, zero)
import qualified Data.Type.Natural                 as TN
import qualified Data.Vector                       as V
import           Data.Vector.Sized                 (Vector ((:-), Nil))
import qualified Data.Vector.Sized                 as SV
import           Numeric.Decidable.Units
import           Numeric.Decidable.Zero
import           Numeric.Semiring.Integral         (IntegralSemiring)
import           Prelude                           hiding (Fractional (..),
                                                    Num (..), quot, rem, sum,
                                                    (^))
import qualified Prelude                           as P

-- | Galois field of order @p^n@.
--   @f@ stands for the irreducible polynomial over @F_p@ of degree @n@.
data GF0 p n f = GF0 { runGF0 :: SV.Vector (F p) n } deriving (Eq)

modPoly :: (SingI n, Reifies p Natural) => Unipol (F p) -> GF0 p n f
modPoly = GF0 . polyToVec

modVec :: Vector (F p) n -> GF0 p n f
modVec = GF0

instance (Reifies p Natural, Show (F p), SingI n) => Show (GF0 p n f)  where
  showsPrec _ (GF0 Nil) = showString "0"
  showsPrec d (GF0 (v :- vs)) =
    if SV.all isZero vs
    then showsPrec d v
    else showChar '(' . shows (vecToPoly $ v :- vs) . showChar ')'

vecToPoly :: (SingI n, Ring r, DecidableZero r)
          => SV.Vector r n -> Unipol r
vecToPoly v = sum $ imap (\i c -> injectCoeff c * varX^fromIntegral i) $ SV.toList v

polyToVec :: forall n r. (Ring r, SingI n, DecidableZero r) => Unipol r -> SV.Vector r n
polyToVec f = SV.unsafeFromList' [ coeff (leadingMonomial $ (varX ^ i) `asTypeOf` f) f
                                 | i <- [0..sNatToInt (sing :: SNat n)]]

instance Reifies p Natural => Additive (GF0 p n f)  where
  GF0 v + GF0 u = GF0 $ SV.zipWithSame (+) v u

instance (Reifies p Natural, SingI n) => Monoidal (GF0 p n f) where
  zero = GF0 $ SV.replicate' zero

instance Reifies p Natural => LeftModule Natural (GF0 p n f) where
  n .* GF0 v = GF0 $ SV.map (n .*) v

instance Reifies p Natural => RightModule Natural (GF0 p n f) where
  GF0 v *. n = GF0 $ SV.map (*. n) v

instance Reifies p Natural => LeftModule Integer (GF0 p n f) where
  n .* GF0 v = GF0 $ SV.map (n .*) v

instance Reifies p Natural => RightModule Integer (GF0 p n f) where
  GF0 v *. n = GF0 $ SV.map (*. n) v

instance (SingI n, Reifies p Natural) => Group (GF0 p n f) where
  negate (GF0 v) = GF0 $ SV.map negate v
  GF0 u - GF0 v  = GF0 $ SV.zipWithSame (-) u v

instance (SingI n, Reifies p Natural) => Abelian (GF0 p n f)

instance (SingI n, Reifies f (Unipol (F p)), Reifies p Natural)
      => Multiplicative (GF0 p n f) where
  GF0 u * GF0 v =
    let t = (vecToPoly u * vecToPoly v) `rem` reflect (Proxy :: Proxy f)
    in GF0 $ polyToVec t

instance (SingI n, Reifies f (Unipol (F p)), Reifies p Natural) => Unital (GF0 p n f) where
  one =
    case sing :: SNat n of
      SZ -> GF0 Nil
      SS _ -> GF0 $ one :- SV.replicate' zero

instance (SingI n, Reifies f (Unipol (F p)), Reifies p Natural) => Semiring (GF0 p n f)

instance (SingI n, Reifies f (Unipol (F p)), Reifies p Natural) => Rig (GF0 p n f) where
  fromNatural n =
    case sing :: SNat n of
      SZ -> GF0 Nil
      SS _ -> GF0 $ fromNatural n :- SV.replicate' zero

instance (SingI n, Reifies f (Unipol (F p)), Reifies p Natural) => Commutative (GF0 p n f)

instance (SingI n, Reifies f (Unipol (F p)), Reifies p Natural) => Ring (GF0 p n f) where
  fromInteger n =
    case sing :: SNat n of
      SZ -> GF0 Nil
      SS _ -> GF0 $ fromInteger n :- SV.replicate' zero

instance (SingI n, Reifies p Natural) => DecidableZero (GF0 p n f) where
  isZero (GF0 sv) = SV.all isZero sv

instance (SingI n, Reifies p Natural, Reifies f (Unipol (F p))) => DecidableUnits (GF0 p n f) where
  isUnit (GF0 sv) = not $ SV.all isZero sv
  recipUnit a | isZero a = Nothing
              | otherwise = Just $ recip a

instance (Reifies p Natural, Reifies f (Unipol (F p)), SingI n)
      => Characteristic (GF0 p n f) where
  char _ = char (Proxy :: Proxy (F p))

instance (Reifies p Natural, Reifies f (Unipol (F p)), SingI n)
      => Division (GF0 p n f) where
  recip f = pow f (order (Proxy :: Proxy (GF0 p n f)) P.- 2)

instance (Reifies p Natural, Reifies f (Unipol (F p)), SingI n) => P.Num (GF0 p n f) where
  (+) = (+)
  (-) = (-)
  negate = negate
  (*) = (*)
  fromInteger = fromInteger
  abs = error "not defined"
  signum = error "not defined"

instance (Reifies p Natural, Reifies f (Unipol (F p)), SingI n) => P.Fractional (GF0 p n f) where
  fromRational u = fromInteger (Rat.numerator u) / fromInteger (Rat.denominator u)
  (/) = (/)
  recip = recip

reifyGF0 :: MonadRandom m => Natural -> Natural
         -> (forall (p :: *) (f :: *) (n :: Nat) . (Reifies p Natural, Reifies f (Unipol (F p)), SingI n)
             => Proxy (GF0 p n f) -> a)
         -> m a
reifyGF0 p n f = reifyPrimeField p $ \pxy -> do
  mpol <- generateIrreducible pxy n
  case promote (fromIntegral n) of
    Monomorphic sn ->
      case singInstance sn of
        TN.SingInstance -> return $ reify mpol (f . proxyGF0 pxy sn)

withGF0 :: MonadRandom m
        => Natural -> Natural
        -> (forall (p :: *) (f :: *) (n :: Nat) . (Reifies p Natural, Reifies f (Unipol (F p)), SingI n)
            => GF0 p n f)
        -> m (V.Vector Natural)
withGF0 p n f = reifyGF0 p n $ V.fromList . SV.toList . SV.map naturalRepr . runGF0 . asProxyTypeOf f

proxyGF0 :: Proxy (F p) -> SNat n -> Proxy f -> Proxy (GF0 p n f)
proxyGF0 _ _ = reproxy

type GF' p n = GF0 p n (Conway p n)

class (SingI n, Reifies p Natural, Reifies f (Unipol (F p))) => IsGF0 p n f
instance (SingI n, Reifies p Natural, Reifies f (Unipol (F p))) => IsGF0 p n f


instance (IsGF0 p n f) => IntegralSemiring (GF0 p n f)

instance IsGF0 p n f => FiniteField (GF0 p n f) where
  power _ = sNatToInt (sing :: SNat n)
  elements _ = map (GF0 . SV.unsafeFromList') $ sequence $
               replicate (sNatToInt (sing :: SNat n)) $ elements Proxy

primitive :: (IsGF0 p n f) => GF0 p (S n) f
primitive = GF0 $ polyToVec varX

-- | Phantom type for conway polynomials
data Conway p n

conway :: forall p n. (Reifies (Conway p n) (Unipol (F p)))
       => SNat p -> SNat n -> Unipol (F p)
conway _ _ = reflect (Proxy :: Proxy (Conway p n))

-- p = 2
instance Reifies (Conway Two One) (Unipol (F Two)) where
  reflect _ = varX + 1

instance Reifies (Conway Two Two) (Unipol (F Two)) where
  reflect _ = varX^2 + varX + 1

instance Reifies (Conway Two Three) (Unipol (F Two)) where
  reflect _ = varX^3 + varX + 1

instance Reifies (Conway Two Four) (Unipol (F Two)) where
  reflect _ = varX^4 + varX + 1

instance Reifies (Conway Two Five) (Unipol (F Two)) where
  reflect _ = varX^5 + varX^2 + 1

instance Reifies (Conway Two Six) (Unipol (F Two)) where
  reflect _ = varX^6 + varX^4 + varX^3 + varX + 1

instance Reifies (Conway Two Seven) (Unipol (F Two)) where
  reflect _ = varX^7 + varX + 1

instance Reifies (Conway Two Eight) (Unipol (F Two)) where
  reflect _ = varX^8 + varX^4 + varX^3 + varX^2 + 1

instance Reifies (Conway Two Nine) (Unipol (F Two)) where
  reflect _ = varX^9 + varX^4 + 1

instance Reifies (Conway Two Ten) (Unipol (F Two)) where
  reflect _ = varX^10 + varX^6 + varX^5 + varX^3 + varX^2 + varX + 1

-- p = 3
instance Reifies (Conway Three One) (Unipol (F Three)) where
  reflect _ = varX + 1

instance Reifies (Conway Three Two) (Unipol (F Three)) where
  reflect _ = varX^2 + 2*varX + 2

instance Reifies (Conway Three Three) (Unipol (F Three)) where
  reflect _ = varX^3 + 2*varX + 1

instance Reifies (Conway Three Four) (Unipol (F Three)) where
  reflect _ = varX^4 + 2*varX^3 + 2

instance Reifies (Conway Three Five) (Unipol (F Three)) where
  reflect _ = varX^5 + 2*varX + 1

instance Reifies (Conway Three Six) (Unipol (F Three)) where
  reflect _ = varX^6 + 2*varX^4 + varX^2 + 2*varX + 2

instance Reifies (Conway Three Seven) (Unipol (F Three)) where
  reflect _ = varX^7 + 2*varX^2 + 1

instance Reifies (Conway Three Eight) (Unipol (F Three)) where
  reflect _ = varX^8 + 2*varX^5 + varX^4 + 2*varX^2 + 2*varX^2 + 2

instance Reifies (Conway Three Nine) (Unipol (F Three)) where
  reflect _ = varX^9 + 2*varX^3 + 2*varX^2 + varX + 1

instance Reifies (Conway Three Ten) (Unipol (F Three)) where
  reflect _ = varX^10 + 2*varX^6 + 2*varX^5 + 2*varX^4 + varX + 2

-- p = 5
instance Reifies (Conway Five One) (Unipol (F Five)) where
  reflect _ = varX + 3

instance Reifies (Conway Five Two) (Unipol (F Five)) where
  reflect _ = varX^2 + 4*varX + 2

instance Reifies (Conway Five Three) (Unipol (F Five)) where
  reflect _ = varX^3 + 3*varX + 3

instance Reifies (Conway Five Four) (Unipol (F Five)) where
  reflect _ = varX^4 + 4*varX^2 + 4*varX + 2

instance Reifies (Conway Five Five) (Unipol (F Five)) where
  reflect _ = varX^5 + 4*varX + 3

instance Reifies (Conway Five Six) (Unipol (F Five)) where
  reflect _ = varX^4 + 4*varX^3 + varX^2 + 2

instance Reifies (Conway Five Seven) (Unipol (F Five)) where
  reflect _ = varX^7 + 3*varX + 3

instance Reifies (Conway Five Eight) (Unipol (F Five)) where
  reflect _ = varX^8 + varX^4 + 3*varX^2 + 4*varX + 2

instance Reifies (Conway Five Nine) (Unipol (F Five)) where
  reflect _ = varX^9 + 2*varX^3 + varX + 3

instance Reifies (Conway Five Ten) (Unipol (F Five)) where
  reflect _ = varX^10 + 3*varX^5 + 3*varX^4 + 2*varX^3 + 4*varX^2 + varX + 2

-- p = 7

instance Reifies (Conway Seven One) (Unipol (F Seven)) where
  reflect _ = varX + 4

instance Reifies (Conway Seven Two) (Unipol (F Seven)) where
  reflect _ = varX^2 + 6*varX + 3

instance Reifies (Conway Seven Three) (Unipol (F Seven)) where
  reflect _ = varX^3 + 6*varX^2 + 4

instance Reifies (Conway Seven Four) (Unipol (F Seven)) where
  reflect _ = varX^4 + 5*varX^2 + 4*varX + 3

instance Reifies (Conway Seven Five) (Unipol (F Seven)) where
  reflect _ = varX^5 + varX + 4

instance Reifies (Conway Seven Six) (Unipol (F Seven)) where
  reflect _ = varX^6 + varX^4 + 5*varX^3 + 4*varX^2 + 6*varX + 3

instance Reifies (Conway Seven Seven) (Unipol (F Seven)) where
  reflect _ = varX^7 + 6*varX + 4

instance Reifies (Conway Seven Eight) (Unipol (F Seven)) where
  reflect _ = varX^8 + 4*varX^3 + 6*varX^2 + 2*varX + 3

instance Reifies (Conway Seven Nine) (Unipol (F Seven)) where
  reflect _ = varX^9 + 6*varX^4 + varX^3 + 6*varX + 4

instance Reifies (Conway Seven Ten) (Unipol (F Seven)) where
  reflect _ = varX^10 + varX^6 + varX^5 + 4*varX^4 + varX^3 + 2*varX^2 + 3*varX + 3
