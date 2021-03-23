{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans -Wall #-}

module Main where

import Algebra.Bridge.Singular
import Algebra.Field.Prime
import Algebra.Prelude.Core
import Cases
import Control.Monad (void)
import qualified Data.Text as T
import qualified Data.Vector.Unboxed as V
import Statistics.Resampling
import Statistics.Resampling.Bootstrap
import Statistics.Types
import qualified System.Random.MWC as Rand
import Prelude (read)

benchIdeal :: IsSingularPolynomial poly => Text -> Ideal poly -> IO Double
benchIdeal fun i =
  fmap ((/ 1000) . read . T.unpack) $
    singular $
      toProg fun i

toProg :: (SingularOrder (Arity poly) (MOrder poly), SingularCoeff (Coefficient poly), IsOrderedPolynomial poly) => Text -> Ideal poly -> Text
toProg fun i =
  let expr = funE fun [idealE' i]
   in prettySingular $ do
        directC "system(\"--ticks-per-sec\", 1000000)"
        void $ ringC "R" expr
        declOnlyC IdealT "G"
        directC "timer=1"
        directC "int t=rtimer"
        letC "G" expr
        directC "print(rtimer-t)"
        directC "exit"

analyse :: (IsSingularPolynomial poly) => String -> Text -> Ideal poly -> IO ()
analyse lab fun ideal = do
  gen <- Rand.create
  i2Gr <- V.replicateM 50 $ benchIdeal fun ideal
  res <- resample gen [Mean, StdDev] 1000 i2Gr
  let [Estimate mn (ConfInt lbmn ubmn _), Estimate dv _] =
        bootstrapBCA cl95 i2Gr res
  putStrLn lab
  mapM_
    (putStrLn . ('\t' :))
    [ "Mean:\t" ++ show mn ++ "(ms)"
    , "MeanLB:\t" ++ show lbmn
    , "MeanUB:\t" ++ show ubmn
    , "StdDev:\t" ++ show dv
    ]

runTestCases ::
  (IsMonomialOrder n o, KnownNat n) =>
  String ->
  Ideal (OrderedPolynomial Rational o n) ->
  IO ()
runTestCases lab i = do
  analyse (lab ++ " (Q, Lex, Sing(gr))") "groebner" $ fmap (changeOrder Lex) i
  analyse (lab ++ " (Q, Lex, Sing(sba))") "sba" $ fmap (changeOrder Lex) i
  analyse (lab ++ " (Q, Grevlex, Sing(gr))") "groebner" $ fmap (changeOrder Grevlex) i
  analyse (lab ++ " (Q, Grevlex, Sing(sba))") "sba" $ fmap (changeOrder Grevlex) i
  analyse (lab ++ " (F_65521, Lex, Sing(gr))") "groebner" $ fmap (mapCoeff ratToF . changeOrder Lex) i
  analyse (lab ++ " (F_65521, Lex, Sing(sba))") "sba" $ fmap (mapCoeff ratToF . changeOrder Lex) i
  analyse (lab ++ " (F_65521, Grevlex, Sing(gr))") "groebner" $ fmap (mapCoeff ratToF . changeOrder Grevlex) i
  analyse (lab ++ " (F_65521, Grevlex, Sing(sba))") "sba" $ fmap (mapCoeff ratToF . changeOrder Grevlex) i

main :: IO ()
main = do
  runTestCases "Cyclic-4" $ cyclic (sNat :: SNat 4)
  runTestCases "Cyclic-5" $ cyclic (sNat :: SNat 5)
  runTestCases "Cyclic-6" $ cyclic (sNat :: SNat 6)
  runTestCases "Katsura-5" $ katsura (sNat :: SNat 5)
  runTestCases "Katsura-6" $ katsura (sNat :: SNat 6)
  runTestCases "Katsura-7" $ katsura (sNat :: SNat 7)

ratToF :: Rational -> F 65521
ratToF = modRat'
