{-# LANGUAGE CPP, DataKinds, ExplicitNamespaces, FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances, GADTs, MultiParamTypeClasses, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, TypeOperators, UndecidableInstances    #-}
module Algebra.Ring.Polynomial.Monomial.Test
       (arbitraryMonomialOfSum, arbitraryMonomial
       ) where
import           Algebra.Internal
import           Algebra.Ring.Polynomial.Monomial (Monomial,
                                                   OrderedMonomial (..))
import qualified Data.Sized.Builtin               as SV
import           GHC.TypeLits                     (KnownNat)
import           Prelude
import           Test.QuickCheck                  (Arbitrary, Gen, arbitrary,
                                                   arbitrarySizedBoundedIntegral,
                                                   arbitrarySizedBoundedIntegral,
                                                   vectorOf)
import qualified Test.QuickCheck                  as QC
import           Test.SmallCheck.Series           (Serial, cons0, newtypeCons,
                                                   series)
import qualified Test.SmallCheck.Series           as SC

instance (KnownNat n, Monad m) => Serial m (Monomial n) where
  series =
    case zeroOrSucc (sing :: SNat n) of
      IsZero   -> cons0 SV.empty
      IsSucc n -> withKnownNat n $ SV.cons <$> (SC.getNonNegative <$> series) <*> series

instance (Monad m, Serial m (Monomial n)) => Serial m (OrderedMonomial ord n) where
  series = newtypeCons OrderedMonomial

arbitraryMonomialOfSum :: SNat n -> Int -> Gen (Monomial n)
arbitraryMonomialOfSum n k =
  case zeroOrSucc n of
    IsZero | k == 0 -> QC.elements [SV.empty]
           | otherwise -> fail "Empty list with positive sum"
    IsSucc m -> withKnownNat m $ do
      l <- QC.elements [0..abs k]
      (l :<) <$> arbitraryMonomialOfSum m (abs k - l)

-- * Instances for QuickCheck.
instance KnownNat n => Arbitrary (Monomial n) where
  arbitrary = arbitraryMonomial

arbitraryMonomial :: forall n. KnownNat n => Gen (Monomial n)
arbitraryMonomial =  SV.unsafeFromList len . map abs <$>
  vectorOf (sNatToInt len) arbitrarySizedBoundedIntegral
    where
      len = sing :: SNat n

instance (KnownNat n) => Arbitrary (OrderedMonomial ord n) where
  arbitrary = OrderedMonomial <$> arbitrary
