{-# LANGUAGE DataKinds, MonoLocalBinds, NoImplicitPrelude, OverloadedLabels #-}
{-# LANGUAGE TypeApplications                                               #-}
module Main where
import           Algebra.Field.Galois
import           Algebra.Field.Prime
import           Algebra.Prelude.Core
import           Algebra.Ring.Polynomial.Factorise
import           Algebra.Ring.Polynomial.Univariate
import           Control.DeepSeq                    (($!!))
import           Control.Monad.Random               (Random, getRandom,
                                                     mkStdGen, runRand)
import           Gauge
import qualified Prelude                            as P

withShown :: IsPolynomial a => a -> IO (a, String)
withShown f = pure (f, show $ totalDegree' f)

main :: IO ()
main = defaultMain
  [ bgroup "irreducible"
    [ bgroup "F 2"
      [ env (withShown $!! f0)
        $ \ ~(f, shown) ->
        bench shown $ nfAppIO factorise f
      | f0 <- [ f2_irred_deg2, f2_irred_deg3
              , f2_irred_deg4, f2_irred_deg5
              , f2_irred_deg20]
      ]
    , bgroup "F 59"
      [ env (withShown $!! f0)
        $ \ ~(f, shown) ->
        bench shown $ nfAppIO factorise f
      | f0 <- [f59_irred_deg2, f59_irred_deg3, f59_irred_deg4, f59_irred_deg5]
      ]
    , bgroup "F 12379"
      [ env (withShown $!! f0)
        $ \ ~(f, shown) ->
        bench shown $ nfAppIO factorise f
      | f0 <- [ f12379_irred_deg2, f12379_irred_deg3
              , f12379_irred_deg4, f12379_irred_deg5
              , f12379_irred_deg20]
      ]
    , bgroup "GF 2 5"
      [ env (withShown $!! f0)
        $ \ ~(f, shown) ->
        bench ("degree " ++ shown) $ nfAppIO factorise f
      | f0 <- [ gf2_5_irred_deg2, gf2_5_irred_deg3
              , gf2_5_irred_deg4, gf2_5_irred_deg5
              , gf_2_5_irred_deg20
              ]
      ]
    ]
  , bgroup "product of polynomials of degree one"
    [ bgroup "F 59"
      [ env (withShown $!! f0)
        $ \ ~(f, shown) ->
        bench ("factors " ++ shown) $ nfAppIO factorise f
      | f0 <- [ f59_degOnes_deg5, f59_degOnes_deg10
              , f59_degOnes_deg20, f59_degOnes_deg50
              , f59_degOnes_deg100
              ]
      ]
    , bgroup "F 12379"
      [ env (withShown $!! f0)
        $ \ ~(f, shown) ->
        bench ("factors " ++ shown) $ nfAppIO factorise f
      | f0 <- [ f12379_degOnes_deg5, f12379_degOnes_deg10
              , f12379_degOnes_deg20, f12379_degOnes_deg50
              , f12379_degOnes_deg100
              ]
      ]
    , bgroup "GF 2 5"
      [ env (withShown $!! f0)
        $ \ ~(f, shown) ->
        bench ("factors " ++ shown) $ nfAppIO factorise f
      | f0 <- [ gf_2_5_degOnes_deg5, gf_2_5_degOnes_deg10
              , gf_2_5_degOnes_deg20, gf_2_5_degOnes_deg50
              ]
      ]
    ]
  , bgroup "randomly generated polynomials"
    [ bgroup "F 2"
      [ env (withShown $!! f0)
        $ \ ~(f, shown) ->
        bench ("degree " ++ shown) $ nfAppIO factorise f
      | f0 <- [ f2_rand_deg5, f2_rand_deg10, f2_rand_deg50
              , f2_rand_deg100
              ]
      ]
    , bgroup "F 59"
      [ env (withShown $!! f0)
        $ \ ~(f, shown) ->
        bench ("degree " ++ shown) $ nfAppIO factorise f
      | f0 <- [ f59_rand_deg5, f59_rand_deg10, f59_rand_deg50
              --, f59_rand_deg100
              ]
      ]
    , bgroup "F 12379"
      [ env (withShown $!! f0)
        $ \ ~(f, shown) ->
        bench ("degree " ++ shown) $ nfAppIO factorise f
      | f0 <- [ f12379_rand_deg5, f12379_rand_deg10, f12379_rand_deg50
              -- , f12379_rand_deg100
              ]
      ]
    , bgroup "GF 2 5"
      [ env (withShown $!! f0)
        $ \ ~(f, shown) ->
        bench ("degree " ++ shown) $ nfAppIO factorise f
      | f0 <- [ gf_2_5_rand_deg5, gf_2_5_rand_deg10, gf_2_5_rand_deg25
              ]
      ]
    ]
  ]

f59_degOnes_deg5 :: Unipol (F 59)
f59_degOnes_deg5 =
  product $
  map ((#x -) . injectCoeff)
  [34,37,57,53,57]

f59_degOnes_deg10 :: Unipol (F 59)
f59_degOnes_deg10 =
  product $
  map ((#x -) . injectCoeff)
  [20,32,41,48,19,14,17,31,8,26]

f59_degOnes_deg20 :: Unipol (F 59)
f59_degOnes_deg20 =
  product $
  map ((#x -) . injectCoeff)
  [16,35,27,4,15,31,20,9,16
  ,50,4,26,22,5,35,27,49,20,17,25]

f59_degOnes_deg50 :: Unipol (F 59)
f59_degOnes_deg50 =
  product $
  map ((#x -) . injectCoeff)
  [42,2,20,51,7,28,12,40,55,11,14,18,58
  ,1,9,36,1,15,26,36,32,17,46,6,13,34
  ,18,38,57,48,28,31,47,42,34,51,29,12
  ,31,33,33,6,44,58,43,1,50,21,3,1]

f59_degOnes_deg100 :: Unipol (F 59)
f59_degOnes_deg100 =
  product $
  map ((#x -) . injectCoeff)
  [37,6,34,47,11,44,44,35,27,22,5
  ,13,45,32,4,11,51,20,45,4,5,0,34
  ,49,50,3,46,13,41,56,2,11,11,3,14
  ,3,58,55,18,27,4,8,44,28,28,37,7,9
  ,58,56,41,37,8,19,45,54,44,31,56
  ,57,43,37,2,7,5,38,54,15,44,22,8
  ,58,7,11,0,48,20,11,3,52,31
  ,34,37,23,56,12,3,23,42
  ,19,4,23,32,23,14,29,37,32,31,32]

f59_irred_deg5 :: Unipol (F 59)
f59_irred_deg5 = #x^5 + 30* #x^4 + 27* #x^3 + 34* #x^2 + 26 * #x + 24

f59_irred_deg4 :: Unipol (F 59)
f59_irred_deg4 = #x^4 + 18 * #x^3 + 43 * #x^2 + 36 * #x + 11

f59_irred_deg3 :: Unipol (F 59)
f59_irred_deg3 = #x^3 + 9 * #x^2 + 10 * #x + 8

f59_irred_deg2 :: Unipol (F 59)
f59_irred_deg2 = #x^2 + 9 * #x + 2

f2_irred_deg2 :: Unipol (F 2)
f2_irred_deg2 = #x^2 + #x + 1

f2_irred_deg3 :: Unipol (F 2)
f2_irred_deg3 = #x^3 + #x^2 + 1

f2_irred_deg4 :: Unipol (F 2)
f2_irred_deg4 = #x^4 + #x^3 + 1

f2_irred_deg5 :: Unipol (F 2)
f2_irred_deg5 = #x^5 + #x^2 + 1

f2_irred_deg20 :: Unipol (F 2)
f2_irred_deg20 = #x^20 + #x^19 + #x^18 + #x^16
  + #x^13 + #x^8 + #x^7 + #x^6 + #x^5 + #x^2 + 1

f12379_irred_deg2 :: Unipol (F 12379)
f12379_irred_deg2 = #x^2 + 7753 * #x + 11406

f12379_irred_deg3 :: Unipol (F 12379)
f12379_irred_deg3 = #x^3 + 6734 * #x^2 + 221 * #x + 3124

f12379_irred_deg4 :: Unipol (F 12379)
f12379_irred_deg4 = #x^4 + 3024 * #x^3 + 6716 * #x^2 + 7826 * #x + 6303

f12379_irred_deg5 :: Unipol (F 12379)
f12379_irred_deg5 =
  #x^5 + 193 * #x^4 + 2256 * #x^3 + 3007 * #x^2 + 5234 * #x + 3001

f12379_irred_deg20 :: Unipol (F 12379)
f12379_irred_deg20 =
  #x^20 + 10460 * #x^19 + 7985* #x^18
  + 8941* #x^17 + 8007* #x^16 + 4961* #x^15
  + 4154* #x^14 + 5864* #x^13 + 10728* #x^12
  + 11828* #x^11 + 3979* #x^10 + 3806* #x^9
  + 6807* #x^8 + 3149* #x^7 + 3619* #x^6
  + 9355* #x^5 + 4960* #x^4 + 10261* #x^3
  + 11610* #x^2 + 12096* #x + 57

f12379_degOnes_deg5 :: Unipol (F 12379)
f12379_degOnes_deg5 =
  product $
  map ((#x -) . injectCoeff)
  [6592,3672,10426,9372,7093]

f12379_degOnes_deg10 :: Unipol (F 12379)
f12379_degOnes_deg10 =
  product $
  map ((#x -) . injectCoeff)
  [7295,4732,3699,6237,3831
  ,10708,4559,1079,11333,8949]

f12379_degOnes_deg20 :: Unipol (F 12379)
f12379_degOnes_deg20 =
  product $
  map ((#x -) . injectCoeff)
  [6329,317,11644,3351,6836,6259,9115
  ,12117,79,7589,3239,4547,12042,3318
  ,1865,466,4556,4982,403,11080]

f12379_degOnes_deg50 :: Unipol (F 12379)
f12379_degOnes_deg50 =
  product $
  map ((#x -) . injectCoeff)
  [2525,8284,54,7210,3447,2451,1775
  ,317,10435,3850,3398,11908
  ,6977,9906,1720,2347,2550,4940,3843
  ,5446,8396,6733,11144,8292,8356,1102
  ,4497,10264,88,12089,11552,3311,2087,7031
  ,9972,453,12136,26,9621,6037,7973,3169
  ,4404,974,637,9449,7770,3541,661,3619]

f12379_degOnes_deg100 :: Unipol (F 12379)
f12379_degOnes_deg100 =
  product $
  map ((#x -) . injectCoeff)
  [10279,7373,1213,9736,4672,1952,12057
  ,4480,7490,4865,7316,7997,562,7515,8053
  ,11668,4193,11154,613,7185,643,7752,347
  ,11788,8753,1269,2951,6774,5045,2636,5568
  ,1194,1524,9944,8495,7030,7201,10395,11967
  ,1213,6376,8343,12113,8409,3653,12269,3811
  ,10374,11673,952,9786,7639,5907,2807
  ,12144,1404,585,8786,4389,2918,10196,4829
  ,274,8647,105,6404,4278,191,6735,7825,1076
  ,4871,396,2364,11228,4611,9196,6188,6154
  ,6800,5527,9505,6500,3269,12289,10801
  ,6691,765,1632,1242,3549,2496,6832
  ,11407,1785,8715,5135,2149,2119,7780]

gf_2_5_degOnes_deg5 :: Unipol (GF 2 5)
gf_2_5_degOnes_deg5 =
  product $
  map ((#x -) . injectCoeff)
  [ξ^4,ξ^4,ξ^3 + ξ^2 + ξ + 1,ξ^4 + ξ^3 + ξ^2 + ξ + 1,ξ^4 + ξ^3 + ξ^2 + ξ + 1]
  where ξ = primitive

gf_2_5_degOnes_deg10 :: Unipol (GF 2 5)
gf_2_5_degOnes_deg10 =
  product $
  map ((#x -) . injectCoeff)
  [ξ^4 + ξ^3 + ξ^2 + ξ,ξ^2 + 1
  ,ξ^3 + ξ + 1,ξ^4 + ξ^3 + ξ^2 + ξ + 1
  ,ξ^4 + ξ^2 + ξ,ξ^3 + ξ + 1
  ,ξ^4 + ξ^3 + ξ^2 + 1,ξ^2 + ξ + 1
  ,ξ^4 + ξ^3 + ξ + 1,ξ^4 + ξ^3]
  where ξ = primitive

gf_2_5_degOnes_deg20 :: Unipol (GF 2 5)
gf_2_5_degOnes_deg20 =
  product $
  map ((#x -) . injectCoeff)
  [ξ^4 + ξ^2 + ξ,ξ^3 + ξ + 1,1,ξ^2 + ξ,ξ^4 + 1
  ,ξ^3 + ξ,ξ^4 + ξ^3 + ξ^2 + ξ,ξ^4 + ξ^3 + ξ + 1
  ,ξ^4 + 1,ξ,ξ^3 + 1,ξ^3 + ξ,ξ^4 + ξ^3 + ξ^2 + 1
  ,ξ^4 + ξ^3 + ξ^2,ξ^3 + ξ^2 + 1,0,ξ^4 + ξ^2 + 1
  ,ξ,ξ^4 + ξ^3 + ξ^2
  ,ξ^3 + ξ^2 + ξ + 1]
  where ξ = primitive

gf_2_5_degOnes_deg50 :: Unipol (GF 2 5)
gf_2_5_degOnes_deg50 =
  product $
  map ((#x -) . injectCoeff)
  [ξ^4 + ξ^3 + ξ^2 + ξ,ξ^3 + ξ^2 + ξ
  ,ξ^4 + ξ^3 + ξ^2,ξ^3 + ξ^2 + ξ + 1
  ,ξ^4 + ξ^3 + 1,ξ^3 + ξ^2,ξ^2 + ξ + 1
  ,ξ^4,ξ,ξ^4 + ξ^3,ξ^4 + ξ,ξ^3 + ξ^2 + ξ + 1
  ,ξ^4 + ξ^2 + ξ,ξ^4 + ξ^3 + ξ^2 + 1
  ,ξ^4 + ξ + 1,ξ^3 + ξ^2 + ξ
  ,ξ^4 + 1,ξ^3,ξ,ξ^4 + 1,ξ^3 + ξ^2 + ξ + 1
  ,ξ^4 + ξ^2 + ξ + 1,ξ^3 + ξ + 1,ξ^2 + 1
  ,ξ^4 + ξ^3 + ξ,ξ^4,ξ^2 + 1,ξ^3 + ξ^2 + ξ
  ,ξ^4 + ξ^3 + ξ^2 + 1,ξ^4 + ξ^3 + ξ^2
  ,ξ^4 + ξ,1,ξ^4 + ξ^2 + 1,ξ^4 + ξ^3 + ξ^2 + ξ
  ,ξ^4 + 1,ξ^4 + ξ^2 + ξ,ξ^3 + ξ^2 + ξ + 1
  ,ξ^4 + ξ^3 + ξ^2 + ξ,ξ^2,ξ^3,ξ^4 + 1
  ,ξ,ξ^4 + ξ^3 + ξ^2,ξ^4 + ξ^2 + ξ
  ,ξ,ξ,ξ + 1,ξ^4 + ξ^2 + ξ + 1
  ,ξ^2 + ξ + 1,ξ^4 + ξ^3 + 1]
  where ξ = primitive

gf2_5_irred_deg2 :: Unipol (GF 2 5)
gf2_5_irred_deg2 =
  #x^2 + (ξ^3 + ξ + 1) .*. #x + injectCoeff(ξ^3 + ξ^2 + ξ)
  where ξ = primitive

gf2_5_irred_deg3 :: Unipol (GF 2 5)
gf2_5_irred_deg3 =
  #x^3 + (ξ^4 + ξ^2) .*. #x^2 + (ξ^4) .*. #x + injectCoeff (ξ^2 + ξ)
  where ξ = primitive

gf2_5_irred_deg4 :: Unipol (GF 2 5)
gf2_5_irred_deg4 =
  #x^4 + (ξ^4 + ξ^2 + ξ) .*. #x^3 + (ξ^3 + ξ + 1) .*. #x^2
  + (ξ^4 + ξ^3 + ξ + 1) .*. #x + injectCoeff (ξ^4 + ξ^3 + ξ^2 + ξ)
  where ξ = primitive

gf2_5_irred_deg5 :: Unipol (GF 2 5)
gf2_5_irred_deg5 =
  #x^5 + (ξ^4 + ξ^3 + ξ^2 + ξ + 1) .*. #x^4 + (ξ^2 + ξ) .*. #x^3
  + (ξ^4 + ξ^3 + ξ + 1) .*. #x^2
  + (ξ^4 + ξ^2 + ξ) .*. #x + injectCoeff (ξ^2 + ξ + 1)
  where ξ = primitive

gf_2_5_irred_deg20 :: Unipol (GF 2 5)
gf_2_5_irred_deg20 =
  #x^20 + (ξ^4 + ξ^2 + ξ + 1).*. #x^19
  + (ξ^4 + ξ^3 + ξ + 1).*. #x^18
  + (ξ^4 + ξ^3 + 1).*. #x^17
  + (ξ^3 + ξ^2 + ξ).*. #x^16
  + (ξ^3 + ξ^2 + ξ + 1).*. #x^15 + (ξ^4 + ξ^3 + ξ^2 + ξ).*. #x^14
  + (ξ^2).*. #x^13 + (ξ^3 + ξ^2 + ξ + 1).*. #x^12
  + (ξ^4).*. #x^11 + (ξ^3 + ξ^2 + ξ).*. #x^10 + (ξ^4 + ξ).*. #x^9
  + (ξ^3 + ξ + 1).*. #x^8 + (ξ^4 + ξ^3 + ξ^2).*. #x^7
  + (ξ^4 + ξ^2 + 1).*. #x^6 + (ξ^4 + ξ^3).*. #x^5
  + (ξ^4 + ξ^3).*. #x^4 + (ξ^3 + 1).*. #x^3
  + (ξ^2 + 1).*. #x^2 + (ξ^2 + ξ + 1).*. #x
  + injectCoeff (ξ^4 + ξ)
  where ξ = primitive

type Seed = Int

f2_rand_deg5 :: Unipol (F 2)
f2_rand_deg5 =
  randomPoly 9193548123270279377 (Proxy @(F 2)) 5

f2_rand_deg10 :: Unipol (F 2)
f2_rand_deg10 =
  randomPoly 5954035523357200167 (Proxy @(F 2)) 10

f2_rand_deg50 :: Unipol (F 2)
f2_rand_deg50 =
  randomPoly (-6593109385820112487) (Proxy @(F 2)) 50

f2_rand_deg100 :: Unipol (F 2)
f2_rand_deg100 =
  randomPoly 919154999066204904 (Proxy @(F 2)) 100


f59_rand_deg5 :: Unipol (F 59)
f59_rand_deg5 =
  randomPoly 7843141909975345566 Proxy 5

f59_rand_deg10 :: Unipol (F 59)
f59_rand_deg10 =
  randomPoly 6607270006669044249 Proxy 10

f59_rand_deg50 :: Unipol (F 59)
f59_rand_deg50 =
  randomPoly (-3071815209415553516) Proxy 50

f59_rand_deg100 :: Unipol (F 59)
f59_rand_deg100 =
  randomPoly (-3354538193028255891) Proxy 100

gf_2_5_rand_deg5 :: Unipol (GF 2 5)
gf_2_5_rand_deg5 =
  randomPoly (-8946568970836448319) Proxy 5

gf_2_5_rand_deg10 :: Unipol (GF 2 5)
gf_2_5_rand_deg10 =
  randomPoly (-3224523753560157840) Proxy 10

gf_2_5_rand_deg25 :: Unipol (GF 2 5)
gf_2_5_rand_deg25 =
  randomPoly (-4134444955663732920) Proxy 25

f12379_rand_deg5 :: Unipol (F 12379)
f12379_rand_deg5 =
  randomPoly 4786536651044932615 Proxy 5

f12379_rand_deg10 :: Unipol (F 12379)
f12379_rand_deg10 =
  randomPoly 4650728365858623837 Proxy 10

f12379_rand_deg50 :: Unipol (F 12379)
f12379_rand_deg50 =
  randomPoly 2422623739499307645 Proxy 50

f12379_rand_deg100 :: Unipol (F 12379)
f12379_rand_deg100 =
  randomPoly 7584500092059047952 Proxy 100


randomPoly
  :: (Random k, CoeffRing k)
  => Seed -> Proxy k -> Natural -> Unipol k
randomPoly _ _ 0 = one
randomPoly seed _ deg =
  sum $ zipWith (\i -> (#x^ i *) . injectCoeff) [deg, deg P.- 1 ..]
  $ one : fst (runRand (replicateM (fromIntegral deg) getRandom) (mkStdGen seed))
