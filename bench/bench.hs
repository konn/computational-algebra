{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs            #-}
{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings, PolyKinds, QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell, UndecidableInstances, DataKinds, NoImplicitPrelude   #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
import Algebra.Algorithms.Groebner
import Algebra.Prelude
import Control.DeepSeq
import Control.Parallel.Strategies
import Data.Type.Natural
import Criterion.Main

i1, i2, i4 :: [OrderedPolynomial (Fraction Integer) Grevlex Three]
(i1, i2, i4) = ([x^2 + y^2 + z^2 - 1, x^2 + y^2 + z^2 - 2*x, 2*x -3*y - z],
                [x^2 * y - 2*x*y - 4*z - 1, z-y^2, x^3 - 4*z*y],
                [ z^5 + y^4 + x^3 - 1, z^3 + y^3 + x^2 - 1]
               )
  where
    [x,y,z] = genVars sThree

i3 :: [OrderedPolynomial Rational Grevlex Six]
i3 = [ 2 * s - a * y, b^2 - (x^2 + y^2), c^2 - ( (a-x) ^ 2 + y^2)]
  where
    [x,y,s,a,b,c] = genVars sSix

main :: IO ()
main = do
  defaultMain $ [ env (return $! toIdeal $ map (changeOrder Lex) i1) $ \ ~ideal ->
                   bgroup "lex01"
                   [ bench "simple" $ nf simpleBuchberger ideal
                   , bench "relprime" $ nf primeTestBuchberger ideal
                   , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy) ideal
                   , bench "syz+sugar" $ nf syzygyBuchberger  ideal
                   ]
                , env (return $! toIdeal $ map (changeOrder Grlex) i1) $ \ ~ideal ->
                   bgroup "grlex01"
                   [ bench "simple" $ nf simpleBuchberger ideal
                   , bench "relprime" $ nf primeTestBuchberger ideal
                   , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy) ideal
                   , bench "syz+sugar" $ nf syzygyBuchberger  ideal
                   ]
                , env (return $! toIdeal $ map (changeOrder Grevlex) i1) $ \ ~ideal ->
                   bgroup "grevlex01"
                   [ bench "simple" $ nf simpleBuchberger ideal
                   , bench "relprime" $ nf primeTestBuchberger ideal
                   , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy) ideal
                   , bench "syz+sugar" $ nf syzygyBuchberger  ideal
                   ]
                , env (return $! toIdeal $ map (changeOrder Grlex) i2) $ \ ~ideal ->
                   bgroup "grlex02"
                   [ bench "simple" $ nf simpleBuchberger ideal
                   , bench "relprime" $ nf primeTestBuchberger ideal
                   , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy) ideal
                   , bench "syz+sugar" $ nf syzygyBuchberger  ideal
                   ]
                , env (return $! toIdeal $ map (changeOrder Grevlex) i2) $ \ ~ideal ->
                   bgroup "grevlex02"
                   [ bench "simple" $ nf simpleBuchberger ideal
                   , bench "relprime" $ nf primeTestBuchberger ideal
                   , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy) ideal
                   , bench "syz+sugar" $ nf syzygyBuchberger  ideal
                     --    -- , bench "singular" $ nfIO (singularWith Grevlex ideal)
                   ]
                , env (return $! toIdeal $ map (changeOrder Lex) i3) $ \ ~ideal ->
                   bgroup "lex03"
                   [ bench "simple" $ nf simpleBuchberger ideal
                   , bench "relprime" $ nf primeTestBuchberger ideal
                   , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy) ideal
                   , bench "syz+sugar" $ nf syzygyBuchberger  ideal
                     --    -- , bench "singular" $ nfIO (singularWith Grevlex ideal)
                   ]
                , env (return $! toIdeal $ map (changeOrder Grlex) i3) $ \ ~ideal ->
                   bgroup "grlex03"
                   [ bench "simple" $ nf simpleBuchberger ideal
                   , bench "relprime" $ nf primeTestBuchberger ideal
                   , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy) ideal
                   , bench "syz+sugar" $ nf syzygyBuchberger  ideal
                     --    -- , bench "singular" $ nfIO (singularWith Grevlex ideal)
                   ]
                , env (return $! toIdeal $ map (changeOrder Grevlex) i3) $ \ ~ideal ->
                   bgroup "grevlex03"
                   [ bench "simple" $ nf simpleBuchberger ideal
                   , bench "relprime" $ nf primeTestBuchberger ideal
                   , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy) ideal
                   , bench "syz+sugar" $ nf syzygyBuchberger  ideal
                     --    -- , bench "singular" $ nfIO (singularWith Grevlex ideal)
                   ]
                , env (return $! toIdeal $ map (changeOrder Grlex) i4) $ \ ~ideal ->
                   bgroup "grlex04"
                   [ bench "simple" $ nf simpleBuchberger ideal
                   , bench "relprime" $ nf primeTestBuchberger ideal
                   , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy) ideal
                   , bench "syz+sugar" $ nf syzygyBuchberger  ideal
                     --    -- , bench "singular" $ nfIO (singularWith Grevlex ideal)
                   ]
                , env (return $! toIdeal $ map (changeOrder Grevlex) i4) $ \ ~ideal ->
                   bgroup "grevlex04"
                   [ bench "simple" $ nf simpleBuchberger ideal
                   , bench "relprime" $ nf primeTestBuchberger ideal
                   , bench "syzygy" $ nf (syzygyBuchbergerWithStrategy NormalStrategy) ideal
                   , bench "syz+sugar" $ nf syzygyBuchberger  ideal
                     --    -- , bench "singular" $ nfIO (singularWith Grevlex ideal)
                   ]
                ]
