{-# LANGUAGE DataKinds, ExplicitNamespaces, GADTs, NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings, PartialTypeSignatures, PatternSynonyms #-}
{-# LANGUAGE RankNTypes, TypeApplications                              #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module Algebra.Algorithms.Groebner.SignatureSpec where
import           Algebra.Algorithms.Groebner
import           Algebra.Algorithms.Groebner.Signature
import           Algebra.Bridge.Singular
import           Algebra.Internal                      (pattern (:<), KnownNat,
                                                        pattern NilL, SNat,
                                                        sSucc)
import           Algebra.Prelude.Core
import           Algebra.Ring.Ideal
import           Algebra.Ring.Polynomial
import           Algebra.Ring.Polynomial.Homogenised
import           Algebra.Ring.Polynomial.Labeled
import           Control.Monad
import qualified Data.Foldable                         as F
import           Data.List                             (delete)
import qualified Data.Sized.Builtin                    as SV
import qualified Data.Vector                           as V
import           Numeric.Field.Fraction                (Fraction)
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.HUnit.Lang
import           Test.QuickCheck
import           Utils


asGenListOf :: Gen [a] -> a -> Gen [a]
asGenListOf = const

newtype Calc
  = Calc { runCalc :: forall poly. (Field (Coefficient poly), IsOrderedPolynomial poly) => Ideal poly -> [poly] }

f5Calcs :: [(String, Calc)]
f5Calcs = [ ("f5", Calc f5)
          , ("f5With pot", Calc $ f5With (Proxy @POT))
          , ("f5With top", Calc $ f5With (Proxy @TOP))
          , ("f5With term-w-pot",
             Calc $ withTermWeights (Proxy @POT) (\pxy -> f5With pxy . toIdeal . V.toList) . V.fromList . generators)
          , ("f5With term-w-top",
             Calc $ withTermWeights (Proxy @TOP) (\pxy -> f5With pxy . toIdeal . V.toList) . V.fromList . generators)
          , ("f5With deg-w-pot",
             Calc $ withDegreeWeights (Proxy @POT) (\pxy -> f5With pxy . toIdeal . V.toList) . V.fromList . generators)
          , ("f5With deg-w-top",
             Calc $ withDegreeWeights (Proxy @TOP) (\pxy -> f5With pxy . toIdeal . V.toList) . V.fromList . generators)
          ]

spec :: Spec
spec = parallel $
  forM_ f5Calcs $ \(name, Calc calc) ->
    describe name $ modifyMaxSize (const 4) $ modifyMaxSuccess (const 25) $ do
      prop "passes S-test" $
        checkForArity [2..3] $ prop_passesSTest calc
      prop "passes S-test (regression)" $
        once $ conjoin [counterexample (show ideal) $ passesSTest calc ideal | SomeIdeal ideal <- regression]
      prop "includes the original ideal" $
        checkForArity [2..3] $ prop_groebnerDivsOrig calc
      prop "includes the original ideal (regression)" $ once $
        once $ conjoin [counterexample (show ideal) $ groebnerDivsOrig calc ideal | SomeIdeal ideal <- regression]
      prop "is included in the orignal ideal" $
        checkForArity [2..3] $ prop_groebnerIncluded calc
      prop "is included in the orignal ideal (regression)" $
        once $ conjoin [counterexample (show ideal) $ groebnerIncluded calc ideal | SomeIdeal ideal <- regression]

data SomeIdeal where
  SomeIdeal :: (Show poly, Field (Coefficient poly), IsSingularPolynomial poly) => [poly] -> SomeIdeal

type QQxy  = LabPolynomial' Rational Grevlex '["x", "y"]
type QQxyz = LabPolynomial' Rational Grevlex '["x", "y", "z"]

regression :: [SomeIdeal]
regression =
  [SomeIdeal @QQxyz [2* #x^2* #y* #z ^2 - (3 % 4) * #x^2* #y* #z
                    ,3* #x^3* #y^3* #z ^2 - 3* #x^2* #y^3* #z ^4
                    ,-3* #x^2* #z  + 2* #y^4* #z ^3 - (1 % 3)]
  ,SomeIdeal @QQxy  [-2* #x * #y ^2 - (2 % 3)* #y
                    ,-(1 % 3)* #x ^3* #y  - (1 % 3)* #x ^3 - 2* #y ^4
                    ,- #x ^3* #y ^4 + 2* #y ^4]
  ,SomeIdeal @QQxyz [(2 % 3)* #x ^4* #y ^4* #z ^4 - (1 % 3)* #x * #y * #z ^4
                    ,-(1 % 2)* #x ^3* #y ^3* #z  + 3* #x * #z ^3
                    ,-2* #x ^4* #y ^3* #z ^4 + 2* #x ^3* #y ^2* #z ^4 - 3* #x * #y ^2]
  ,SomeIdeal @QQxy  [2* #x ^4* #y  + (2 % 3)* #x ^3* #y ^2
                    ,(2 % 3)* #x ^3* #y ^4 + (3 % 4)* #x * #y ^2,-3* #y
                    ,(1 % 3)* #x ^2* #y  + (3 % 2)* #x * #y ^2
                    ,-3* #x ^4* #y ^2 - (1 % 3)* #x ^4 + 2* #x ^3* #y
                    ]
  ,SomeIdeal @QQxy  [(1 % 3)* #x
                    ,-(1 % 2)* #x^4* #y^3 - (3 % 4)* #x^2* #y^2 + (3 % 4)* #y^4
                    ,(2 % 3)* #x^2* #y^4 - 3* #x* #y + 3* #y
                    ,-(3 % 4)* #x^2* #y - (1 % 2)* #x* #y^4
                    ,-(2 % 3)* #x^4* #y^3 - 3
                    ]
  ,SomeIdeal @QQxyz [-(3 % 4)* #x ^3* #y ^2* #z + 3* #x ^2* #y ^3* #z^2 - (2 % 3)* #z^2
                    ,(3 % 4)* #x * #y ^2* #z - (1 % 3)* #x  - (2 % 5)* #y ^4* #z^2
                    ,(1 % 2)* #x ^4* #y ^4* #z^4 + (2 % 3)* #x * #y ^3* #z
                    ]
  ]

prop_passesSTest :: (Ideal (Polynomial Rational n) -> [Polynomial Rational n])
                 -> SNat n -> Property
prop_passesSTest calc sdim = withKnownNat sdim $
  forAll (sized $ \ size -> vectorOf size (polynomialOfArity sdim)) $ passesSTest calc

passesSTest :: (Field (Coefficient poly), IsOrderedPolynomial poly) => (Ideal poly -> [poly]) -> [poly] -> Bool
passesSTest calc ideal =
  let gs = calc $ toIdeal ideal
  in all (isZero . (`modPolynomial` gs)) [sPolynomial f g | f <- gs, g <- gs, f /= g]

prop_groebnerDivsOrig :: (Ideal (Polynomial Rational n) -> [Polynomial Rational n])
                      -> SNat n -> Property
prop_groebnerDivsOrig calc sdim = withKnownNat sdim $
  forAll (elements [3..5]) $ \count ->
  forAll (vectorOf count (polynomialOfArity sdim)) $ groebnerDivsOrig calc

groebnerDivsOrig :: (IsOrderedPolynomial r, Euclidean (Coefficient r), Division (Coefficient r), Foldable t)
                 => (Ideal r -> t r) -> [r] -> Bool
groebnerDivsOrig calc ideal =
  let gs = calc $ toIdeal ideal
  in all (isZero . (`modPolynomial` gs)) ideal

prop_groebnerIncluded :: (Ideal (Polynomial Rational n) -> [Polynomial Rational n])
                      -> SNat n -> Property
prop_groebnerIncluded calc sdim = withKnownNat sdim $
  forAll (elements [3..5]) $ \count ->
  forAll (vectorOf count (polynomialOfArity sdim)) $ groebnerIncluded calc

groebnerIncluded :: (IsSingularPolynomial r) => (Ideal r -> [r]) -> [r] -> IO ()
groebnerIncluded calc ideal = do
  let gs = calc $ toIdeal ideal
  is <- evalSingularIdealWith [] [] $
        funE "reduce" [idealE' $ toIdeal gs, funE "groebner" [idealE' $ toIdeal ideal]]
  if all isZero is
    then return ()
    else assertFailure "Non-zero element found"
