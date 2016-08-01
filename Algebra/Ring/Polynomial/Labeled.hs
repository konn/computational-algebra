{-# LANGUAGE CPP, ConstraintKinds, DataKinds, FlexibleInstances, GADTs    #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses, PolyKinds, RankNTypes #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances, ScopedTypeVariables            #-}
module Algebra.Ring.Polynomial.Labeled
       (IsUniqueList, LabPolynomial(..),
        UniqueResult(..)) where
import           Algebra.Scalar
import           Algebra.Ring.Polynomial.Class
import           Data.Singletons.Prelude
import           Data.Type.Natural             (Nat (..))
import           Numeric.Algebra
import           Prelude                       hiding (Integral (..), Num (..),
                                                product, sum)
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 800
import GHC.TypeLits
#endif

data UniqueResult = Expected | VariableOccursTwice Symbol

type family UniqueList' (x :: Symbol) (xs :: [Symbol]) :: UniqueResult where
  UniqueList' x '[] = 'Expected
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 800
  UniqueList' x (x ': xs) = TypeError ('Text "The variable " :<>: 'Text x :<>: " occurs variables list twice!")
#else
  UniqueList' x (x ': xs) = 'VariableOccursTwice x
#endif
  UniqueList' x (y ': xs) = UniqueList' x xs

type family SumResult r r' where
  SumResult 'Expected 'Expected = 'Expected
  SumResult ('VariableOccursTwice x) 'Expected = 'VariableOccursTwice x
  SumResult 'Expected ('VariableOccursTwice x) = 'VariableOccursTwice x
  SumResult ('VariableOccursTwice x) ('VariableOccursTwice y) = 'VariableOccursTwice x

type family UniqueList (xs :: [Symbol]) :: UniqueResult where
  UniqueList '[] = 'Expected
  UniqueList (x ': xs) = SumResult (UniqueList' x xs) (UniqueList xs)

class    ('Expected ~ UniqueList xs) => IsUniqueList (xs :: [Symbol])
instance ('Expected ~ UniqueList xs) => IsUniqueList (xs :: [Symbol])


type family Length' (xs :: [a]) where
  Length' '[] = 'Z
  Length' (x ': xs) = 'S (Length' xs)

newtype LabPolynomial poly (vars :: [Symbol]) where
  LabelPolynomial :: { unLabelPolynomial :: (IsUniqueList vars, Length' vars ~ Arity poly)
                                       => poly }
                -> LabPolynomial poly vars

type Wraps vars poly = (IsUniqueList vars, Arity poly ~ Length' vars)

instance (Wraps vars poly, Additive poly) => Additive (LabPolynomial poly vars) where
  LabelPolynomial f + LabelPolynomial g = LabelPolynomial $ f + g
  {-# INLINE (+) #-}

instance (Wraps vars poly, Multiplicative poly) => Multiplicative (LabPolynomial poly vars) where
  LabelPolynomial f * LabelPolynomial g =
    LabelPolynomial $ f * g
  {-# INLINE (*) #-}

instance (Wraps vars poly, Abelian poly)     => Abelian (LabPolynomial poly vars)
instance (Wraps vars poly, Commutative poly) => Commutative (LabPolynomial poly vars)
instance (Wraps vars poly, Unital poly) => Unital (LabPolynomial poly vars) where
  one = LabelPolynomial one
  {-# INLINE one #-}

instance (Wraps vars poly, Group poly) => Group (LabPolynomial poly vars) where
  negate (LabelPolynomial f) = LabelPolynomial (negate f)
  {-# INLINE negate #-}

instance (Wraps vars poly, RightModule Natural poly) => RightModule Natural (LabPolynomial poly vars) where
  LabelPolynomial f *. a = LabelPolynomial $  f *. a
  {-# INLINE (*.) #-}

instance (Wraps vars poly, LeftModule Natural poly) => LeftModule Natural (LabPolynomial poly vars) where
  a .* LabelPolynomial f = LabelPolynomial $ a .* f
  {-# INLINE (.*) #-}

instance (Wraps vars poly, RightModule Integer poly) => RightModule Integer (LabPolynomial poly vars) where
  LabelPolynomial f *. a = LabelPolynomial $  f *. a
  {-# INLINE (*.) #-}

instance (Wraps vars poly, LeftModule Integer poly) => LeftModule Integer (LabPolynomial poly vars) where
  a .* LabelPolynomial f = LabelPolynomial $ a .* f
  {-# INLINE (.*) #-}

instance (Wraps vars poly, Monoidal poly) => Monoidal (LabPolynomial poly vars) where
  zero = LabelPolynomial zero
  {-# INLINE zero #-}

instance (Wraps vars poly, Semiring poly) => Semiring (LabPolynomial poly vars)
instance (Wraps vars poly, Rig poly) => Rig (LabPolynomial poly vars)
instance (Wraps vars poly, Ring poly) => Ring (LabPolynomial poly vars) where
  fromInteger n = LabelPolynomial (fromInteger n :: poly)
  {-# INLINE fromInteger #-}

instance (Wraps vars poly, LeftModule (Scalar r) poly)  => LeftModule  (Scalar r) (LabPolynomial poly vars) where
  a .* LabelPolynomial f = LabelPolynomial $ a .* f
  {-# INLINE (.*) #-}

instance (Wraps vars poly, RightModule (Scalar r) poly) => RightModule (Scalar r) (LabPolynomial poly vars) where
  LabelPolynomial f *. a = LabelPolynomial $ f *. a
  {-# INLINE (*.) #-}


instance (IsPolynomial poly, Wraps vars poly) => IsPolynomial (LabPolynomial poly vars) where
  type Coefficient (LabPolynomial poly vars) = Coefficient poly
  type Arity (LabPolynomial poly vars) = Arity poly

  liftMap mor = liftMap mor . unLabelPolynomial
  {-# INLINE liftMap #-}

  terms = terms . unLabelPolynomial
  {-# INLINE terms #-}

  monomials = monomials . unLabelPolynomial
  {-# INLINE monomials #-}

  coeff m = coeff m . unLabelPolynomial
  {-# INLINE coeff #-}

  constantTerm = constantTerm . unLabelPolynomial
  {-# INLINE constantTerm #-}

  sArity = sArity . unLabelPolynomial
  {-# INLINE sArity #-}

  arity = arity . unLabelPolynomial
  {-# INLINE arity #-}

  fromMonomial m = LabelPolynomial (fromMonomial m :: poly)
  {-# INLINE fromMonomial #-}

  toPolynomial' (r, deg) = LabelPolynomial (toPolynomial' (r, deg) :: poly)
  {-# INLINE toPolynomial' #-}

  polynomial' dic = LabelPolynomial (polynomial' dic :: poly)
  {-# INLINE polynomial' #-}

  totalDegree = totalDegree . unLabelPolynomial
  {-# INLINE totalDegree #-}

instance (IsOrderedPolynomial poly, Wraps vars poly) => IsOrderedPolynomial (LabPolynomial poly vars) where
  type MOrder (LabPolynomial poly vars) = MOrder poly

  leadingTerm = leadingTerm . unLabelPolynomial
  {-# INLINE leadingTerm #-}

  leadingCoeff = leadingCoeff . unLabelPolynomial
  {-# INLINE leadingCoeff #-}

  fromOrderedMonomial m = LabelPolynomial (fromOrderedMonomial m :: poly)
  {-# INLINE fromOrderedMonomial #-}

  toPolynomial (r, deg) = LabelPolynomial (toPolynomial (r, deg) :: poly)
  {-# INLINE toPolynomial #-}

  polynomial dic = LabelPolynomial (polynomial dic :: poly)
  {-# INLINE polynomial #-}
