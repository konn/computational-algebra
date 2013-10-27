{-# LANGUAGE ImpredicativeTypes, RankNTypes, StandaloneDeriving #-}
module Main where
import qualified Algebra.Ring.Polynomial     as P
import           Control.Applicative
import           Control.DeepSeq
import           Control.Monad
import           Control.Monad
import           Control.Parallel.Strategies
import           Criterion.Main
import           Data.List                   (foldl')
import qualified Data.Sequence               as S
import           Data.Type.Monomorphic
import           Instances
import qualified SequenceMonomial            as S
import           System.Random
import           Test.QuickCheck

main :: IO ()
main = do
  as0 <- replicateM 10 genMonomial
  as <- return $!! (as0 `using` rdeepseq)
  defaultMain $ zipWith mkTestCase [1..] as


genMonomial :: IO ([Int], [Int])
genMonomial = do
  len <- abs <$> randomRIO (2, 15)
  liftM head . sample' $ do
    m <- map abs <$> vector len
    n <- map abs <$> vector len
    return (m, n)

instance NFData Ordering where
  rnf EQ = ()
  rnf LT = ()
  rnf GT = ()

mkTestCase :: Int -> ([Int], [Int]) -> Benchmark
mkTestCase n (m, m') =
    bgroup ("case-" ++ show n ++ "-len" ++ show len) $
           map subcase
                   [ ("lex", P.lex, S.lex)
                   , ("revlex", P.revlex, S.revlex)
                   , ("grlex", P.grlex, S.grlex)
                   , ("grevlex", P.grevlex, S.grevlex)
                   ]
  where
    len = length m
    subcase :: (String, P.MonomialOrder, S.MonomialOrder) -> Benchmark
    subcase (name, pol, sq) =
        bgroup name [ bench "vector" $ withPolymorhic len $ \sn ->
                          nf (pol (P.fromList sn m)) (P.fromList sn m')
                    , bench "sequence" $ nf (sq (S.fromList m)) (S.fromList m')
                    ]
