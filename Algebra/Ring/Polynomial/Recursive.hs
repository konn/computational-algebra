{-# LANGUAGE DataKinds, EmptyCase, GeneralizedNewtypeDeriving, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TemplateHaskell     #-}
{-# LANGUAGE TypeFamilyDependencies, TypeOperators                        #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Algebra.Ring.Polynomial.Recursive where
import           Algebra.Prelude
import           Algebra.Ring.Polynomial.Univariate
import           Control.Lens                       (each, (%~), (&))
import qualified Data.Coerce                        as C
import           Data.Constraint
import           Data.Type.Equality                 (sym)
import           Data.Type.Natural.Builtin
import qualified Prelude                            as P
import           Unsafe.Coerce                      (unsafeCoerce)

data NatView = ZZ | SS Nat


type family ViewNat n  where
  ViewNat 0 = 'ZZ
  ViewNat n = 'SS (n - 1)

-- sNatView :: SNat n -> SNatView (ViewNat n)
-- sNatView k =
--   case zeroOrSucc k of
--     IsZero   -> SZZ
--     IsSucc m -> SSS m

data instance Sing (n :: NatView) where
  SZZ :: Sing 'ZZ
  SSS :: Sing n -> Sing (SS n)

type SNatView (n :: NatView) = Sing n

type family RecPoly' r n where
  RecPoly' r 'ZZ     = r
  RecPoly' r ('SS k) = Unipol (RecPoly r k)


-- | @n@-variate polynomial with coefficient @r@, implemented as a nested univariate polynomials.
newtype RecPoly r (n :: Nat) = RecPoly { runRecPoly :: RecPoly' r (ViewNat n) }

-- deriving instance Eq a => RecPoly a n

-- withCoeffRing :: forall n r a. (KnownNat n, CoeffRing r)
--               => (CoeffRing (RecPoly' r n) => RecPoly r n -> a) -> RecPoly r n -> a
-- withCoeffRing f =
--   case coeffRing (Proxy :: Proxy r) (sing :: SNat n) of
--     Dict -> f
-- {-# INLINE withCoeffRing #-}

-- decUnits :: forall r n.
--             (CoeffRing r, DecidableUnits r)
--           => Proxy r -> Sing n -> Dict (DecidableUnits (RecPoly' r n))
-- decUnits _ Zero = Dict
-- decUnits pxy (Succ (k :: SNat k)) = withKnownNat k $
--   case decUnits pxy k of
--     Dict -> unsafeCoerce (Dict :: Dict (DecidableUnits (Unipol (RecPoly r k))))
--             -- Very sad, but trust me...
-- decUnits _ _ = error "GHC bug"
-- {-# INLINE decUnits #-}

-- withDecUnits :: forall n r a. (KnownNat n, DecidableUnits r, CoeffRing r)
--               => (DecidableUnits (RecPoly' r n) => RecPoly r n -> a) -> RecPoly r n -> a
-- withDecUnits f =
--   case decUnits (Proxy :: Proxy r) (sing :: SNat n) of
--     Dict -> f
-- {-# INLINE withDecUnits #-}

-- unitNF :: forall r n.
--             (CoeffRing r, UnitNormalForm r)
--           => Proxy r -> Sing n -> Dict (UnitNormalForm (RecPoly' r n))
-- unitNF _ Zero = Dict
-- unitNF pxy (Succ (k :: SNat k)) = withKnownNat k $
--   case unitNF pxy k of
--     Dict -> unsafeCoerce (Dict :: Dict (UnitNormalForm (Unipol (RecPoly r k))))
--             -- Very sad, but trust me...
-- unitNF _ _ = error "GHC bug"
-- {-# INLINE unitNF #-}

-- withUnitNF :: forall n r a. (KnownNat n, UnitNormalForm r, CoeffRing r)
--               => (UnitNormalForm (RecPoly' r n) => RecPoly r n -> a) -> RecPoly r n -> a
-- withUnitNF f =
--   case unitNF (Proxy :: Proxy r) (sing :: SNat n) of
--     Dict -> f
-- {-# INLINE withUnitNF #-}

-- instance (KnownNat n, CoeffRing r) => Eq (RecPoly r n) where
--   (==) = withCoeffRing $ \(RecPoly f) (RecPoly g) -> f == g
--   {-# INLINE (==) #-}

-- deriving instance (Show (RecPoly' r n)) => Show (RecPoly r n)
-- instance (Show (RecPoly' r n)) => PrettyCoeff (RecPoly r n) where
--   showsCoeff d = Positive . showsPrec d

-- instance (KnownNat n, CoeffRing r) => Additive (RecPoly r n) where
--   (+) = withCoeffRing $ \(RecPoly f) (RecPoly g) -> RecPoly $ f + g
--   {-# INLINE (+) #-}

-- instance (KnownNat n, CoeffRing r) => LeftModule Natural (RecPoly r n) where
--   (.*) = flip $ withCoeffRing $ \ (RecPoly f) n -> RecPoly (n .* f)
--   {-# INLINE (.*) #-}

-- instance (KnownNat n, CoeffRing r) => RightModule Natural (RecPoly r n) where
--   (*.) = withCoeffRing $ \(RecPoly r) n -> RecPoly (r *. n)
--   {-# INLINE (*.) #-}

-- instance (KnownNat n, CoeffRing r) => LeftModule (Scalar r) (RecPoly r n) where
--   (.*) = flip $ withCoeffRing $ \ (RecPoly f) n -> RecPoly (n .* f)
--   {-# INLINE (.*) #-}

-- instance (KnownNat n, CoeffRing r) => RightModule (Scalar r) (RecPoly r n) where
--   (*.) = withCoeffRing $ \(RecPoly r) n -> RecPoly (r *. n)
--   {-# INLINE (*.) #-}

-- instance (KnownNat n, CoeffRing r) => Monoidal (RecPoly r n) where
--   zero =
--     case coeffRing (Proxy :: Proxy r) (sing :: SNat n) of
--       Dict -> RecPoly zero
--   {-# INLINE zero #-}

-- instance (KnownNat n, CoeffRing r) => Abelian (RecPoly r n)

-- instance (KnownNat n, CoeffRing r) => DecidableZero (RecPoly r n) where
--   isZero = withCoeffRing $ isZero . runRecPoly
--   {-# INLINE isZero #-}

-- instance (KnownNat n, CoeffRing r) => Multiplicative (RecPoly r n) where
--   (*) = withCoeffRing $ \(RecPoly f) (RecPoly g) -> RecPoly $ f * g
--   {-# INLINE (*) #-}

-- instance (KnownNat n, CoeffRing r) => LeftModule Integer (RecPoly r n) where
--   (.*) = flip $ withCoeffRing $ \ (RecPoly f) n -> RecPoly (n .* f)
--   {-# INLINE (.*) #-}

-- instance (KnownNat n, CoeffRing r) => RightModule Integer (RecPoly r n) where
--   (*.) = withCoeffRing $ \(RecPoly r) n -> RecPoly (r *. n)
--   {-# INLINE (*.) #-}

-- instance (KnownNat n, CoeffRing r) => Commutative (RecPoly r n)
-- instance (KnownNat n, CoeffRing r) => Group (RecPoly r n) where
--   negate = withCoeffRing $ RecPoly . negate . runRecPoly
--   {-# INLINE negate #-}

-- instance (KnownNat n, CoeffRing r) => Unital (RecPoly r n) where
--   one =
--     case coeffRing (Proxy :: Proxy r) (sing :: SNat n) of
--       Dict -> RecPoly one
--   {-# INLINE one #-}

-- instance (KnownNat n, CoeffRing r) => Semiring (RecPoly r n)
-- instance (KnownNat n, CoeffRing r) => Rig (RecPoly r n)
-- instance (KnownNat n, CoeffRing r) => Ring (RecPoly r n)

-- instance (KnownNat n, CoeffRing r) => ZeroProductSemiring (RecPoly r n)
-- instance (DecidableUnits r, KnownNat n, CoeffRing r)
--       => DecidableUnits (RecPoly r n) where
--   isUnit = withDecUnits $ isUnit . runRecPoly
--   {-# INLINE isUnit #-}
--   recipUnit = withDecUnits $ fmap RecPoly . recipUnit . runRecPoly
--   {-# INLINE recipUnit #-}

-- instance (UnitNormalForm r, KnownNat n, CoeffRing r)
--       => DecidableAssociates (RecPoly r n) where
--   isAssociate = withUnitNF $ \(RecPoly p) (RecPoly q) -> isAssociate p q
--   {-# INLINE isAssociate #-}

-- instance (UnitNormalForm r, KnownNat n, CoeffRing r) => UnitNormalForm (RecPoly r n) where
--   splitUnit = withUnitNF $ \(RecPoly r) -> splitUnit r & each %~ RecPoly
--   {-# INLINE splitUnit #-}

-- instance (UnitNormalForm r,
--           KnownNat n, CoeffRing r)
--       => Num (RecPoly r n) where
--   (+) = C.coerce ((P.+) :: WrapAlgebra (RecPoly r n) -> WrapAlgebra (RecPoly r n) -> WrapAlgebra (RecPoly r n))
--   (*) = C.coerce ((P.*) :: WrapAlgebra (RecPoly r n) -> WrapAlgebra (RecPoly r n) -> WrapAlgebra (RecPoly r n))
--   (-) = C.coerce ((P.-) :: WrapAlgebra (RecPoly r n) -> WrapAlgebra (RecPoly r n) -> WrapAlgebra (RecPoly r n))
--   negate = C.coerce (P.negate :: WrapAlgebra (RecPoly r n) -> WrapAlgebra (RecPoly r n))
--   abs = C.coerce (P.abs :: WrapAlgebra (RecPoly r n) -> WrapAlgebra (RecPoly r n))
--   signum = C.coerce (P.signum :: WrapAlgebra (RecPoly r n) -> WrapAlgebra (RecPoly r n))
--   fromInteger = C.coerce (P.fromInteger :: Integer -> WrapAlgebra (RecPoly r n))

-- instance (KnownNat n, CoeffRing r) => IsPolynomial (RecPoly r n) where
--   type Coefficient (RecPoly r n) = r
--   type Arity (RecPoly r n) = n
