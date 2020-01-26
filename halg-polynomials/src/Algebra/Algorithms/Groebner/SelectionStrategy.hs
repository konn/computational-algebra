{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts                  #-}
{-# LANGUAGE FlexibleInstances, GADTs, MultiParamTypeClasses               #-}
{-# LANGUAGE NoImplicitPrelude, PolyKinds, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies, TypeOperators                                   #-}
module Algebra.Algorithms.Groebner.SelectionStrategy
  ( SelectionStrategy(..), calcWeight', GrevlexStrategy(..)
  , NormalStrategy(..), SugarStrategy(..), GradedStrategy(..)
  ) where
import Algebra.Internal
import Algebra.Prelude.Core

import qualified Data.Foldable as F
import qualified Data.Heap     as H
import           Data.Kind     (Type)
import           Data.Proxy    (Proxy (..))

-- | Calculate the weight of given polynomials w.r.t. the given strategy.
--   Buchberger's algorithm proccesses the pair with the most least weight first.
--   This function requires the @Ord@ instance for the weight; this constraint is not required
--   in the 'calcWeight' because of the ease of implementation. So use this function.
calcWeight' :: (SelectionStrategy (Arity poly) s, IsOrderedPolynomial poly)
            => s -> poly -> poly -> Weight (Arity poly) s (MOrder poly)
calcWeight' s = calcWeight (toProxy s)
{-# INLINE calcWeight' #-}

-- | Type-class for selection strategies in Buchberger's algorithm.
class SelectionStrategy n s where
  type Weight n s ord :: Type
  -- | Calculates the weight for the given pair of polynomial used for selection strategy.
  calcWeight :: (IsOrderedPolynomial poly, n ~ Arity poly)
             => Proxy s -> poly -> poly -> Weight n s (MOrder poly)

-- | Buchberger's normal selection strategy. This selects the pair with
--   the least LCM(LT(f), LT(g)) w.r.t. current monomial ordering.
data NormalStrategy = NormalStrategy deriving (Read, Show, Eq, Ord)

instance SelectionStrategy n NormalStrategy where
  type Weight n NormalStrategy ord = OrderedMonomial ord n
  calcWeight _ f g = lcmMonomial (leadingMonomial f)  (leadingMonomial g)
  {-# INLINE calcWeight #-}

-- | Choose the pair with the least LCM(LT(f), LT(g)) w.r.t. 'Grevlex' order.
data GrevlexStrategy = GrevlexStrategy deriving (Read, Show, Eq, Ord)

instance SelectionStrategy n GrevlexStrategy where
  type Weight n GrevlexStrategy ord = OrderedMonomial Grevlex n
  calcWeight _ f g = changeMonomialOrderProxy Proxy $
                     lcmMonomial (leadingMonomial f) (leadingMonomial g)
  {-# INLINE calcWeight #-}

data GradedStrategy = GradedStrategy deriving (Read, Show, Eq, Ord)

-- | Choose the pair with the least LCM(LT(f), LT(g)) w.r.t. graded current ordering.
instance SelectionStrategy n GradedStrategy where
  type Weight n GradedStrategy ord = OrderedMonomial (Graded ord) n
  calcWeight _ f g = changeMonomialOrderProxy Proxy $
                     lcmMonomial (leadingMonomial f)  (leadingMonomial g)
  {-# INLINE calcWeight #-}


-- | Sugar strategy. This chooses the pair with the least phantom homogenized degree and then break the tie with the given strategy (say @s@).
newtype SugarStrategy s = SugarStrategy s deriving (Read, Show, Eq, Ord)

instance SelectionStrategy n s => SelectionStrategy n (SugarStrategy s) where
  type Weight n (SugarStrategy s) ord = (Int, Weight n s ord)
  calcWeight (Proxy :: Proxy (SugarStrategy s)) f g = (sugar, calcWeight (Proxy :: Proxy s) f g)
    where
      deg' = maximum . map totalDegree . F.toList . orderedMonomials
      tsgr h = deg' h - totalDegree (leadingMonomial h)
      sugar = max (tsgr f) (tsgr g) + totalDegree (lcmMonomial (leadingMonomial f) (leadingMonomial g))
  {-# INLINE calcWeight #-}
