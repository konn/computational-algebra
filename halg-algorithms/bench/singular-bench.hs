{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction      #-}
{-# LANGUAGE OverloadedStrings, PolyKinds, TypeFamilies            #-}
{-# LANGUAGE UndecidableInstances                                  #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans -Wall #-}
module Main where
import           Algebra.Bridge.Singular
import           Algebra.Prelude.Core
import           Control.Monad                   (void)
import           Control.Parallel.Strategies
import qualified Data.Text                       as T
import qualified Data.Vector.Unboxed             as V
import           Numeric.Field.Fraction          (Fraction)
import           Prelude                         (read)
import           Statistics.Resampling
import           Statistics.Resampling.Bootstrap
import           Statistics.Types
import qualified System.Random.MWC               as Rand


i2 :: [OrderedPolynomial (Fraction Integer) Grevlex 5]
i2 =  [35 * y^4 - 30*x*y^2 - 210*y^2*z + 3*x^2 + 30*x*z - 105*z^2 +140*y*t - 21*u
      ,5*x*y^3 - 140*y^3*z - 3*x^2*y + 45*x*y*z - 420*y*z^2 + 210*y^2*t -25*x*t + 70*z*t + 126*y*u
      ]
     where [t,u,x,y,z] = vars

i3 :: [OrderedPolynomial (Fraction Integer) Grevlex 4]
i3 = [ x^31 - x^6 - x- y, x^8 - z, x^10 -t]
  where
    [t,x,y,z] = vars

i4 :: [OrderedPolynomial (Fraction Integer) Grevlex 4]
i4 = [ w+x+y+z, w*x+x*y+y*z+z*w, w*x*y + x*y*z + y*z*w + z*w*x, w*x*y*z - 1]
  where
    [x,y,z,w] = vars

benchIdeal :: IsSingularPolynomial poly => Text -> Ideal poly -> IO Double
benchIdeal fun i = fmap ((/1000) . read . T.unpack) $ singular $
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

analyse :: (SingularOrder (Arity poly) (MOrder poly), SingularCoeff (Coefficient poly), IsOrderedPolynomial poly) => String -> Text -> Ideal poly -> IO ()
analyse lab fun ideal = do
  gen <- Rand.create
  i2Gr <- V.replicateM 200 $ benchIdeal fun ideal
  res  <- resample gen [Mean, StdDev] 1000 i2Gr
  let [Estimate mn (ConfInt lbmn ubmn _) ,Estimate dv _]
        = bootstrapBCA cl95 i2Gr res
  putStrLn lab
  putStrLn $ unlines $ map ('\t':)
    ["Mean:\t" ++ show mn ++ "(ms)"
    ,"MeanLB:\t" ++ show lbmn
    ,"MeanUB:\t" ++ show ubmn
    ,"StdDev:\t" ++ show dv
    ]

runTestCases :: (IsMonomialOrder n o, SingularCoeff k, KnownNat n)
             => String -> Ideal (OrderedPolynomial k o n) -> IO ()
runTestCases lab i = do
  analyse (lab ++ " (Lex, Sing(gr))") "groebner" $ fmap (changeOrder Lex) i
  analyse (lab ++ " (Lex, Sing(sba))") "sba" $ fmap (changeOrder Lex) i
  analyse (lab ++ " (Grevlex, Sing(gr))") "groebner" $ fmap (changeOrder Grevlex) i
  analyse (lab ++ " (Grevlex, Sing(sba))") "groebner" $ fmap (changeOrder Grevlex) i

main :: IO ()
main = do
  ideal2 <- return $! (toIdeal i2 `using` rdeepseq)
  ideal3 <- return $! (toIdeal i3 `using` rdeepseq)
  ideal4 <- return $! (toIdeal i4 `using` rdeepseq)

  runTestCases "I1" ideal2
  runTestCases "Cyclic4" ideal4
  analyse "I3 (Grevlex, Sing(gr))" "groebner" ideal3
  analyse "I3 (Grevlex, Sing(sba))" "sba" ideal3
  -- analyse "groebner" ideal4
  -- analyse "sba" ideal4
  -- analyse "groebner" ideal3
  -- analyse "sba" ideal3
  -- defaultMainWith defaultConfig $
  --      mkTestCases (Left 1) ideal2
  --   ++ mkTestCases (Right "Cyclic-4") ideal4
  --   ++ [mkTC "grevlex03" ideal3]
