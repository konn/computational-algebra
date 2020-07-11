{-# LANGUAGE DataKinds, GADTs, LambdaCase, NoImplicitPrelude              #-}
{-# LANGUAGE OverloadedLabels, PolyKinds, TypeApplications, TypeOperators #-}
module Main where
import Algebra.Field.Prime
import Algebra.Prelude.Core
import Algebra.Ring.Polynomial.Factorise
import Algebra.Ring.Polynomial.Univariate
import Control.Exception                  (evaluate)
import Control.Monad.Random
import System.Environment

type Seed = Int
randomPoly
  :: (Random k, CoeffRing k)
  => Seed -> Proxy k -> Natural -> Unipol k
randomPoly _ _ 0 = one
randomPoly seed _ deg =
  sum $ zipWith (\i -> (#x^ i *) . injectCoeff) [deg, pred deg ..]
  $ one : withSeed seed (replicateM (fromIntegral deg) getRandom)

withSeed :: Seed -> Rand StdGen a -> a
withSeed = flip evalRand . mkStdGen

f2_rand_deg50 :: Unipol (F 2)
f2_rand_deg50 =
  randomPoly (-6593109385820112487) (Proxy @(F 2)) 100

f59_rand_deg50 :: Unipol (F 59)
f59_rand_deg50 =
  randomPoly (-3071815209415553516) Proxy 100

main :: IO ()
main = getArgs >>= \case
  ["2"]   -> void $ evaluate $ withSeed 6147031469590640211
                  $ factorise f2_rand_deg50
  ["59"]  -> void $ evaluate $ withSeed 7650165946084592722
                  $ factorise f59_rand_deg100
  ["2", "100"]   -> void $ evaluate $ withSeed 6147031469590640211
                  $ factorise f2_rand_deg100
  ["59", "100"]  -> void $ evaluate $ withSeed 7650165946084592722
                        $ factorise f59_rand_deg100
  _ -> error "Arguments must be one of 2 or 59"

f2_rand_deg100 :: Unipol (F 2)
f2_rand_deg100 =
  randomPoly 919154999066204904 (Proxy @(F 2)) 100

f59_rand_deg100 :: Unipol (F 59)
f59_rand_deg100 =
  randomPoly (-3354538193028255891) Proxy 100
