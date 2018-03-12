{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs                   #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses            #-}
{-# LANGUAGE NoMonomorphismRestriction, ScopedTypeVariables, TypeFamilies #-}
{-# LANGUAGE UndecidableInstances                                         #-}
module Algebra.Ring.Polynomial.Test
       ( module Algebra.Ring.Polynomial.Monomial.Test
       , WrapPolynomial(..), arbitraryPolynomial, seriesPolynomial
       , HomogPoly(..), arbitraryHomogeneousPolynomial
       )
       where
import           Algebra.Internal                      (SNat, sing,
                                                        withKnownNat)
import           Algebra.Ring.Polynomial.Class         (Arity, Coefficient,
                                                        IsOrderedPolynomial,
                                                        polynomial)
import           Algebra.Ring.Polynomial.Monomial      (OrderedMonomial (..))
import           Algebra.Ring.Polynomial.Monomial.Test (arbitraryMonomialOfSum)
import qualified Data.Map                              as M
import           Prelude
import           Test.QuickCheck                       (Arbitrary (..), Gen,
                                                        elements, listOf1,
                                                        sized)
import           Test.SmallCheck.Series                (Serial (..), Series)

newtype WrapPolynomial polyn =
  WrapPolynomial { runWrapPolynomial :: polyn }
  deriving (Read, Show, Eq, Ord, Num)

instance (IsOrderedPolynomial poly, Arbitrary (Coefficient poly))
         => Arbitrary (WrapPolynomial poly) where
  arbitrary = WrapPolynomial . polynomial . M.fromList
              <$> listOf1 ((,) <$> arbitrary <*> arbitrary)

instance (Monad m, IsOrderedPolynomial poly, Serial m (Coefficient poly))
         => Serial m (WrapPolynomial poly) where
  series = WrapPolynomial . polynomial . M.fromList <$> series

arbitraryPolynomial :: (Arbitrary (Coefficient poly), IsOrderedPolynomial poly) => Gen poly
arbitraryPolynomial = runWrapPolynomial <$> arbitrary

seriesPolynomial :: (Serial m (Coefficient poly), IsOrderedPolynomial poly) => Series m poly
seriesPolynomial = runWrapPolynomial <$> series

newtype HomogPoly poly = HomogPoly { getHomogPoly :: poly }

instance (IsOrderedPolynomial poly, Arbitrary (Coefficient poly))
      => Arbitrary (HomogPoly poly) where
  arbitrary = sized $ \s -> do
    let sn = sing :: SNat (Arity poly)
    deg <- elements [0..s]
    HomogPoly . polynomial . M.fromList <$>
      listOf1 ((,) <$> (OrderedMonomial <$> arbitraryMonomialOfSum sn deg) <*> arbitrary)

arbitraryHomogeneousPolynomial :: (Arbitrary (Coefficient poly), IsOrderedPolynomial poly) => Gen poly
arbitraryHomogeneousPolynomial = getHomogPoly <$> arbitrary
