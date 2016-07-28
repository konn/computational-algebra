{-# LANGUAGE DataKinds, ExplicitNamespaces, FlexibleContexts, GADTs     #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude, ParallelListComp #-}
{-# LANGUAGE PolyKinds, ScopedTypeVariables, TypeFamilies               #-}
module Algebra.Ring.Polynomial.Class where
import           Algebra.Ring.Polynomial (Monomial)
import           Algebra.Wrapped
import qualified Data.HashMap.Strict     as HM
import qualified Data.HashSet            as HS
import           Data.Proxy
import           Data.Singletons.Prelude (SingI (..))
import           Data.Type.Natural       (Nat, SNat, sNatToInt)
import           Data.Type.Ordinal
import           Data.Vector.Sized       hiding (foldr, sum)
import           Numeric.Algebra
import           Numeric.Decidable.Zero
import           Prelude                 (Int, fromIntegral, not, ($), (.))

-- | Polynomial in terms of free associative commutative algebra generated
--   by n-elements.
--   To effectively compute all terms, we need @'monomials'@ in addition to
--   universality of free object.
class (DecidableZero r, SingI n, Module r poly, Ring r, Commutative r, Ring poly, Commutative poly)
   => Polynomial r (n :: Nat) poly where
  {-# MINIMAL (liftMap , monomials) | terms #-}

  -- | Universal mapping for free algebra.
  --   This corresponds to the algebraic substitution operation.
  liftMap :: (Module r alg, Ring alg, Commutative alg)
           => proxy r -> (Ordinal n -> alg) -> poly -> alg
  liftMap pxy assign f =
    sum [ r .* sum [ (fromInteger (fromIntegral i) :: r) .* assign o
                   | i <- toList (m :: Monomial n) :: [Int]
                   | o <- enumOrdinal sing ]
        | (m, r) <- HM.toList (terms pxy f) ]

  -- | @'monomials' f@ returns the finite set of all monomials appearing in @f@.
  monomials :: proxy r -> poly -> HS.HashSet (Monomial n)
  monomials _ = HS.fromList . HM.keys . terms (Proxy :: Proxy r)

  terms :: proxy r -> poly -> HM.HashMap (Monomial n) r
  terms _ f = HM.fromList [ (m, c)
                          | m <- HS.toList $ monomials (Proxy :: Proxy r) f
                          , let c = coeff m f
                          , not (isZero c)
                          ]

  coeff :: Monomial n -> poly -> r
  coeff m = runCoeff . liftMap (Proxy :: Proxy r) (\i -> WrapCoeff $ fromInteger $ fromIntegral $ m %!! i)



  constantTerm :: poly -> r
  constantTerm = runCoeff . liftMap (Proxy :: Proxy r) (\ (_ :: Ordinal n) -> WrapCoeff zero)

  sArity :: poly -> SNat n
  sArity _ = sing

  arity :: poly -> Natural
  arity _ = sNatToInt (sing :: SNat n)
