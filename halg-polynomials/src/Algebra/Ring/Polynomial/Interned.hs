{-# LANGUAGE GeneralizedNewtypeDeriving, ScopedTypeVariables #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Algebra.Ring.Polynomial.Interned (InternedPolynomial, internPolynomial, uninternPolynomial) where
import           Algebra.Prelude.Core
import           Algebra.Ring.Polynomial.Class ()
import           Data.Interned
import qualified Numeric.Algebra               as NA
import qualified Prelude                       as P

data InternedPolynomial poly = IP { polynomialId :: !Id
                                  , uninternPolynomial :: poly
                                  }

internPolynomial :: (Hashable poly, IsOrderedPolynomial poly) => poly -> InternedPolynomial poly
internPolynomial = intern
{-# INLINE internPolynomial #-}

instance Eq (InternedPolynomial poly) where
  (==) = (==) `on` polynomialId

instance Ord (InternedPolynomial poly) where
  compare = comparing polynomialId

instance Hashable poly => Hashable (InternedPolynomial poly) where
  hashWithSalt s (IP l r) = s `hashWithSalt` l `hashWithSalt` r

instance (IsOrderedPolynomial poly, Hashable poly) => Interned (InternedPolynomial poly) where
  type Uninterned (InternedPolynomial poly)     = poly
  newtype Description (InternedPolynomial poly) = DIP poly
    deriving (Hashable, Eq)
  describe = DIP
  identify = IP
  cacheWidth _ = 148600
  cache = ipCache

instance (IsOrderedPolynomial poly, Hashable poly) => Uninternable (InternedPolynomial poly) where
  unintern = uninternPolynomial

instance (P.Num poly, IsOrderedPolynomial poly, Hashable poly) => P.Num (InternedPolynomial poly) where
  fromInteger = intern . P.fromInteger
  IP _ f + IP _ g = intern $ f P.+ g
  IP _ f * IP _ g = intern $ f P.* g
  abs = intern . P.abs . unintern
  IP _ f - IP _ g = intern $ f P.- g
  negate = intern . P.negate . unintern
  signum = intern . P.signum . unintern

instance (Additive poly, IsOrderedPolynomial poly, Hashable poly) => Additive (InternedPolynomial poly) where
  IP _ f + IP _ g = intern $ f + g
  {-# INLINE (+) #-}

instance (Multiplicative poly, IsOrderedPolynomial poly, Hashable poly) => Multiplicative (InternedPolynomial poly) where
  IP _ f * IP _ g =
    intern $ f * g
  {-# INLINE (*) #-}

instance (Abelian poly, IsOrderedPolynomial poly, Hashable poly)     => Abelian (InternedPolynomial poly)
instance (Commutative poly, IsOrderedPolynomial poly, Hashable poly) => Commutative (InternedPolynomial poly)
instance (Unital poly, IsOrderedPolynomial poly, Hashable poly) => Unital (InternedPolynomial poly) where
  one = intern one
  {-# INLINE one #-}

instance (Group poly, IsOrderedPolynomial poly, Hashable poly) => Group (InternedPolynomial poly) where
  negate (IP _ f) = intern (negate f)
  {-# INLINE negate #-}

instance (RightModule Natural poly, IsOrderedPolynomial poly, Hashable poly) => RightModule Natural (InternedPolynomial poly) where
  IP _ f *. a = intern $  f *. a
  {-# INLINE (*.) #-}

instance (LeftModule Natural poly, IsOrderedPolynomial poly, Hashable poly) => LeftModule Natural (InternedPolynomial poly) where
  a .* IP _ f = intern $ a .* f
  {-# INLINE (.*) #-}

instance (RightModule Integer poly, IsOrderedPolynomial poly, Hashable poly) => RightModule Integer (InternedPolynomial poly) where
  IP _ f *. a = intern $  f *. a
  {-# INLINE (*.) #-}

instance (LeftModule Integer poly, IsOrderedPolynomial poly, Hashable poly) => LeftModule Integer (InternedPolynomial poly) where
  a .* IP _ f = intern $ a .* f
  {-# INLINE (.*) #-}

instance (Monoidal poly, IsOrderedPolynomial poly, Hashable poly) => Monoidal (InternedPolynomial poly) where
  zero = intern zero
  {-# INLINE zero #-}

instance (Semiring poly, IsOrderedPolynomial poly, Hashable poly) => Semiring (InternedPolynomial poly)
instance (Rig poly, IsOrderedPolynomial poly, Hashable poly) => Rig (InternedPolynomial poly)
instance (Ring poly, IsOrderedPolynomial poly, Hashable poly) => Ring (InternedPolynomial poly) where
  fromInteger n = intern (NA.fromInteger n :: poly)
  {-# INLINE fromInteger #-}

instance (LeftModule (Scalar r) poly, IsOrderedPolynomial poly, Hashable poly) => LeftModule  (Scalar r) (InternedPolynomial poly) where
  a .* IP _ f = intern $ a .* f
  {-# INLINE (.*) #-}

instance (RightModule (Scalar r) poly, IsOrderedPolynomial poly, Hashable poly) => RightModule (Scalar r) (InternedPolynomial poly) where
  IP _ f *. a = intern $ f *. a
  {-# INLINE (*.) #-}

instance (DecidableZero poly, IsOrderedPolynomial poly, Hashable poly) => DecidableZero (InternedPolynomial poly) where
  isZero = isZero . unintern

instance (IsPolynomial poly, IsOrderedPolynomial poly, Hashable poly) => IsPolynomial (InternedPolynomial poly) where
  type Coefficient (InternedPolynomial poly) = Coefficient poly
  type Arity (InternedPolynomial poly) = Arity poly

  liftMap mor = liftMap mor . unintern
  {-# INLINE liftMap #-}

  terms' = terms' . unintern
  {-# INLINE terms' #-}

  monomials = monomials . unintern
  {-# INLINE monomials #-}

  coeff' m = coeff' m . unintern
  {-# INLINE coeff' #-}

  constantTerm = constantTerm . unintern
  {-# INLINE constantTerm #-}

  sArity _ = sArity (Proxy :: Proxy poly)
  {-# INLINE sArity #-}

  arity _ = arity (Proxy :: Proxy poly)
  {-# INLINE arity #-}

  fromMonomial m = intern (fromMonomial m :: poly)
  {-# INLINE fromMonomial #-}

  toPolynomial' (r, deg) = intern (toPolynomial' (r, deg) :: poly)
  {-# INLINE toPolynomial' #-}

  polynomial' dic = intern (polynomial' dic :: poly)
  {-# INLINE polynomial' #-}

  totalDegree' = totalDegree' . unintern
  {-# INLINE totalDegree' #-}

instance (IsOrderedPolynomial poly, IsOrderedPolynomial poly, Hashable poly) => IsOrderedPolynomial (InternedPolynomial poly) where
  type MOrder (InternedPolynomial poly) = MOrder poly

  leadingTerm = leadingTerm . unintern
  {-# INLINE leadingTerm #-}

  leadingCoeff = leadingCoeff . unintern
  {-# INLINE leadingCoeff #-}

  fromOrderedMonomial m = intern (fromOrderedMonomial m :: poly)
  {-# INLINE fromOrderedMonomial #-}

  orderedMonomials = orderedMonomials . unintern
  {-# INLINE orderedMonomials #-}

  toPolynomial (r, deg) = intern (toPolynomial (r, deg) :: poly)
  {-# INLINE toPolynomial #-}

  polynomial dic = intern (polynomial dic :: poly)
  {-# INLINE polynomial #-}

  terms = terms . unintern
  {-# INLINE terms #-}

  coeff m = coeff m . unintern
  {-# INLINE coeff #-}

  m >* IP _ f = intern (m >* f)
  {-# INLINE (>*) #-}

  IP _ f *< m = intern (f *< m)
  {-# INLINE (*<) #-}

  diff n (IP _ f) = intern (diff n f)
  {-# INLINE diff #-}

  mapMonomialMonotonic f (IP _ g) = intern $ mapMonomialMonotonic  f g
  {-# INLINE mapMonomialMonotonic #-}

ipCache :: (IsOrderedPolynomial poly, Hashable poly) => Cache (InternedPolynomial poly)
ipCache = mkCache
{-# NOINLINE ipCache #-}
