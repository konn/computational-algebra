{-# LANGUAGE ViewPatterns #-}
module SequenceMonomial (Monomial(), MonomialOrder, length, viewl
                        , totalDegree, viewr, lex, graded, revlex, grlex, grevlex, fromList) where
import           Control.DeepSeq
import           Data.Foldable
import           Data.Monoid
import           Data.Ord
import           Data.Sequence   (Seq)
import qualified Data.Sequence   as S
import           Prelude         hiding (length, lex, sum)

length :: Monomial -> Int
length = S.length . getSeq

fromList :: [Int] -> Monomial
fromList xs = Monomial (S.fromList xs) (sum xs)

viewl :: Monomial -> ViewL
viewl (Monomial sq deg) =
  case S.viewl sq of
    S.EmptyL  -> EmptyL
    x S.:< xs -> x :< Monomial xs (deg - x)

viewr :: Monomial -> ViewR
viewr (Monomial sq deg) =
  case S.viewr sq of
    S.EmptyR  -> EmptyR
    xs S.:> x -> Monomial xs (deg - x) :> x

data ViewL = EmptyL | Int :< Monomial deriving (Read, Show, Eq, Ord)
data ViewR = EmptyR | Monomial :> Int deriving (Read, Show, Eq, Ord)

data Monomial = Monomial { getSeq      :: Seq Int
                         , totalDegree :: !Int
                         } deriving (Read, Show, Eq, Ord)

instance NFData Monomial where
  rnf (Monomial sq deg) = rnf sq `seq` rnf deg `seq` ()

type MonomialOrder = Monomial -> Monomial -> Ordering

-- | Lexicographical order. This *is* a monomial order.
lex :: MonomialOrder
lex (viewl -> EmptyL) (viewl -> EmptyL) = EQ
lex (viewl -> x :< xs) (viewl -> y :< ys) = x `compare` y <> xs `lex` ys
{-# INLINE lex #-}

-- | Reversed lexicographical order. This is *not* a monomial order.
revlex :: Monomial -> Monomial -> Ordering
revlex (viewr -> xs :> x) (viewr -> ys :> y) = y `compare` x <> xs `revlex` ys
revlex (viewr -> EmptyR) (viewr -> EmptyR) = EQ
{-# INLINE revlex #-}

-- | Convert ordering into graded one.
graded :: (Monomial -> Monomial -> Ordering) -> (Monomial -> Monomial -> Ordering)
graded cmp xs ys = comparing totalDegree xs ys <> cmp xs ys
{-# INLINE graded #-}

-- | Graded lexicographical order. This *is* a monomial order.
grlex :: MonomialOrder
grlex = graded lex
{-# INLINE grlex #-}

-- | Graded reversed lexicographical order. This *is* a monomial order.
grevlex :: MonomialOrder
grevlex = graded revlex
{-# INLINE grevlex #-}
