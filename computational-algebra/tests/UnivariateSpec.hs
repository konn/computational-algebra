{-# LANGUAGE DataKinds, ExplicitNamespaces, GADTs, PatternSynonyms #-}
{-# OPTIONS_GHC -fno-warn-unused-imports -Wno-type-defaults #-}
module UnivariateSpec where
import           Algebra.Algorithms.Groebner
import           Algebra.Field.Finite
import           Algebra.Internal                   (pattern (:<), KnownNat,
                                                     pattern NilL, SNat)
import           Algebra.Ring.Polynomial            (OrderedPolynomial)
import           Algebra.Ring.Polynomial.Univariate
import           Control.Monad
import qualified Data.Foldable                      as F
import           Data.List                          (delete)
import qualified Data.Sized.Builtin                 as SV
import           Numeric.Decidable.Zero
import           Numeric.Field.Fraction             (Fraction)
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck
import           Utils

asGenListOf :: Gen [a] -> a -> Gen [a]
asGenListOf = const

toOP :: Unipol Integer -> OrderedPolynomial Integer Grevlex 1
toOP = injectVars

liftMult :: Unipol Integer -> Unipol Integer -> Unipol Integer
liftMult f g =
  let (f', g') = (toOP f, toOP g)
  in injectVars (f' * g')

spec :: Spec
spec = do
  describe "naiveMult" $ do
    prop "Works as expected" $ \f g ->
      (f `naiveMult` g) == (f `liftMult` g)
  describe "karatsuba" $ do
    prop "Works as expected" $ \f g ->
      (karatsuba f g) == (f `liftMult` g)
  describe "divModUnipolByMult" $ do
    prop "remainder has degree smaller than divisor" $ \f g ->
      (totalDegree' f > 0 && totalDegree' g > 0) ==>
      let (q, r) = divModUnipolByMult f (g :: Unipol (F 5))
      in totalDegree' r < totalDegree' g
    prop "divides correctly" $ \f g ->
      not (isZero g) ==>
      let (q, r) = divModUnipolByMult f (g :: Unipol (F 5))
      in q * g + r == f
    it "passes regression tests" $ do
      mapM_ (\((a,b),(c,d)) -> divModUnipolByMult a b `shouldBe` (c, d))
        divModUnipolCases
  describe "divModUnipol" $ do
    prop "remainder has degree smaller than divisor" $ \f g ->
      totalDegree' f > 0 && totalDegree' g > 0 ==>
      let (q, r) = divModUnipol f (g :: Unipol (F 5))
      in totalDegree' r < totalDegree' g
    prop "divides correctly" $ \f g ->
      not (isZero g) ==>
      let (q, r) = divModUnipol f (g :: Unipol (F 5))
      in q * g + r == f

divModUnipolCases :: [((Unipol (F 5), Unipol (F 5)), (Unipol (F 5), Unipol (F 5)))]
divModUnipolCases =
  [((3*x^57 + x^56 + x^55 + 2*x^52 + 2*x^51 + 4*x^50 + x^49 + 4*x^48 + 3*x^47 + 4*x^46 + 3*x^45 + 3*x^44 + 3*x^42 + 3*x^41 + x^40 + x^39 + 2*x^38 + 3*x^37 + x^36 + 2*x^35 + 4*x^34 + 3*x^33 + 4*x^32 + 3*x^31 + x^30 + 3*x^28 + x^26 + x^25 + 3*x^24 + x^22 + 4*x^21 + 3*x^20 + 2*x^19 + 4*x^18 + 4*x^17 + 2*x^16 + x^15 + 3*x^13 + 2*x^12 + x^11 + x^10 + 4*x^9 + 4*x^8 + 2*x^7 + x^6 + 2*x^5 + 4*x^4 + 2*x^3 + 2*x^2 + 3*x + 4, 3*x^19 +2*x^18 +4*x^17 +3*x^16 +4*x^13 +3*x^12 + x^11 +4*x^10 +2*x^8 +2*x^7 +2*x^6 +4*x^4 +2*x^3 +4*x^2 +3*x + 2),(x^38 +3*x^37 +2*x^36 +2*x^35 +3*x^34 +4*x^33 +4*x^32 +2*x^31 +2*x^30 +3*x^29 +2*x^28 +3*x^26 + x^25 + x^24 +3*x^23 +2*x^22 +2*x^20 +3*x^18 +2*x^17 +3*x^16 +4*x^15 + x^14 +4*x^13 +3*x^12 +2*x^11 +3*x^10 +2*x^9 +4*x^7 +3*x^5 +2*x^4 +3*x^3 +2*x^2 + x + 2,2*x^18 +4*x^17 +3*x^16 +2*x^15 +4*x^14 +4*x^12 +2*x^11 +4*x^10 +3*x^8 + x^6 +3*x^4 +2*x^3 +2*x^2))]
  where x = var 0
