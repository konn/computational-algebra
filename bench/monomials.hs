{-# LANGUAGE ExistentialQuantification, ImpredicativeTypes, RankNTypes #-}
module Main where
import qualified Algebra.Ring.Polynomial            as P
import qualified Algebra.Ring.PolynomialAccumulated as PA
import           Control.Applicative
import           Control.DeepSeq
import           Control.Monad
import           Control.Parallel.Strategies
import           Criterion.Main
import           Data.Type.Monomorphic
import qualified SequenceMonomial                   as S
import           System.Random
import           Test.QuickCheck

data MonomPair = forall n. MonomPair { getMonoms :: !(P.Monomial n, P.Monomial n) }
data AMonomPair = forall n. AMonomPair { getAMonoms :: !(PA.Monomial n, PA.Monomial n) }

instance NFData MonomPair where
  rnf (MonomPair (n, m)) = rnf n `seq` rnf m `seq` ()

instance NFData AMonomPair where
  rnf (AMonomPair (n, m)) = rnf n `seq` rnf m `seq` ()

main :: IO ()
main = do
  as0 <- replicateM 5 genMonomial
  as <- return $!! (as0 `using` rdeepseq)
  defaultMain $ zipWith mkTestCase [1..] as

genMonomial :: IO (MonomPair, AMonomPair, (S.Monomial, S.Monomial))
genMonomial = do
  len <- abs <$> randomRIO (5, 20)
  liftM head . sample' $ do
    m <- map abs <$> vector len
    n <- map abs <$> vector len
    let mp = withPolymorhic len $ \sn -> MonomPair (P.fromList sn m, P.fromList sn n)
        amp = withPolymorhic len $ \sn -> AMonomPair (PA.fromList sn m, PA.fromList sn n)
    return (mp, amp, (S.fromList m, S.fromList n))

instance NFData Ordering where
  rnf EQ = ()
  rnf LT = ()
  rnf GT = ()

mkTestCase :: Int -> (MonomPair, AMonomPair, (S.Monomial, S.Monomial)) -> Benchmark
mkTestCase n (MonomPair m, AMonomPair am, m') =
    bgroup ("case-" ++ show n ++ "-len" ++ show len) $
           map subcase
                   [ ("lex", P.lex, PA.lex, S.lex)
                   , ("revlex", P.revlex, PA.revlex, S.revlex)
                   , ("grlex", P.grlex, PA.grlex, S.grlex)
                   , ("grevlex", P.grevlex, PA.grevlex, S.grevlex)
                   ]
  where
    len = S.length $ fst m'
    subcase :: (String, P.MonomialOrder, PA.MonomialOrder, S.MonomialOrder) -> Benchmark
    subcase (name, pol, apol, sq) =
        bgroup name [ bench "vector" $ nf (uncurry pol) m
                    , bench "accvec" $ nf (uncurry apol) am
                    , bench "sequence" $ nf (uncurry sq) m'
                    ]
