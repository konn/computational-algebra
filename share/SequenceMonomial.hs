{-# LANGUAGE ViewPatterns #-}
module SequenceMonomial where
import Data.Foldable
import Data.Monoid
import Data.Ord
import Data.Sequence
import Prelude       hiding (lex, sum)

type Monomial = Seq Int
type MonomialOrder = Monomial -> Monomial -> Ordering

totalDegree :: Monomial -> Int
totalDegree = sum
{-# INLINE totalDegree #-}

-- | Lexicographical order. This *is* a monomial order.
lex :: MonomialOrder
lex (viewl -> EmptyL) (viewl -> EmptyL) = EQ
lex (viewl -> x :< xs) (viewl -> y :< ys) = x `compare` y <> xs `lex` ys

-- | Reversed lexicographical order. This is *not* a monomial order.
revlex :: Monomial -> Monomial -> Ordering
revlex (viewr -> xs :> x) (viewr -> ys :> y) = y `compare` x <> xs `revlex` ys
revlex (viewr -> EmptyR) (viewr -> EmptyR) = EQ

-- | Convert ordering into graded one.
graded :: (Monomial -> Monomial -> Ordering) -> (Monomial -> Monomial -> Ordering)
graded cmp xs ys = comparing totalDegree xs ys <> cmp xs ys
{-# INLINE graded #-}
{-# RULES
"graded/grevlex" graded grevlex = grevlex
"graded/grlex"   graded grlex   = grlex
  #-}

-- | Graded lexicographical order. This *is* a monomial order.
grlex :: MonomialOrder
grlex = graded lex
{-# INLINE grlex #-}

-- | Graded reversed lexicographical order. This *is* a monomial order.
grevlex :: MonomialOrder
grevlex = graded revlex
{-# INLINE grevlex #-}

