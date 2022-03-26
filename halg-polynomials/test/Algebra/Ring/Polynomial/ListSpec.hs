{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Algebra.Ring.Polynomial.ListSpec where

import Algebra.Field.Prime
import Algebra.Prelude.Core hiding ((===))
import Algebra.Ring.Euclidean.Quotient (Quotient)
import Algebra.Ring.Euclidean.Quotient.Test ()
import Algebra.Ring.Polynomial.List
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck
import Utils

test_algebra :: TestTree
test_algebra =
  testGroup
    "algebraic operations"
    [ testGroup
        "(+)"
        [ testProperty "satisfies identity law (Q)" $
            checkForTypeNat [1 .. 3] $ commutes @Rational (+)
        , testProperty "satisfies identity law (F 5)" $
            checkForTypeNat [1 .. 3] $ commutes @(F 5) (+)
        , testProperty "commutes (Q)" $
            checkForTypeNat [1 .. 3] $ identity @Rational zero (+)
        , testProperty "commutes (F 5)" $
            checkForTypeNat [1 .. 3] $ identity @(F 5) zero (+)
        , testProperty "coincides with OrderedPolynomial (Q)" $
            checkForTypeNat [1 .. 3] $ coincidesWithPolyBin @Rational (+)
        , testProperty "coincides with OrderedPolynomial (F 5)" $
            checkForTypeNat [1 .. 3] $ coincidesWithPolyBin @(F 5) (+)
        ]
    , testGroup
        "(*)"
        [ testProperty "satisfies identity law (Q)" $
            setSize 50 $
              checkForTypeNat [1 .. 3] $ commutes @Rational (*)
        , testProperty "satisfies identity law (F 5)" $
            setSize 50 $
              checkForTypeNat [1 .. 3] $ commutes @(F 5) (*)
        , testProperty "commutes (Q)" $
            checkForTypeNat [1 .. 3] $ identity @Rational one (*)
        , testProperty "commutes (F 5)" $
            checkForTypeNat [1 .. 3] $ identity @(F 5) one (*)
        , testProperty "coincides with OrderedPolynomial (Q)" $
            setSize 50 $
              checkForTypeNat [1 .. 3] $ coincidesWithPolyBin @Rational (*)
        , testProperty "coincides with OrderedPolynomial (F 5)" $
            setSize 50 $
              checkForTypeNat [1 .. 3] $ coincidesWithPolyBin @(F 5) (*)
        , testProperty "left distributes over + (Q)" $
            setSize 50 $
              checkForTypeNat [1 .. 3] $ \case
                (sdim :: SNat n) -> withKnownNat sdim $
                  property $ \f g h ->
                    let fgh = f * (g + h) :: ListPoly Rational Grevlex n
                        fgfh = f * g + f * h
                     in fgh === fgfh
        , testProperty "right distributes over + (Q)" $
            setSize 50 $
              checkForTypeNat [1 .. 3] $ \case
                (sdim :: SNat n) -> withKnownNat sdim $
                  property $ \f g h ->
                    let fgh = (f + g) * h :: ListPoly Rational Grevlex n
                        fhgh = f * h + g * h
                     in fgh === fhgh
        ]
    ]

coincidesWithPolyBin ::
  forall r n.
  (CoeffRing r, PrettyCoeff r, Arbitrary r) =>
  ( forall a.
    (IsOrderedPolynomial a, Coefficient a ~ r, Arity a ~ n) =>
    a ->
    a ->
    a
  ) ->
  SNat n ->
  Property
coincidesWithPolyBin bin sdim = withKnownNat sdim $
  property $ \f g ->
    let fgPol = bin f g :: Polynomial r n
        fgList = bin (fromPoly f) (fromPoly g)
     in fgList === fromPoly fgPol

fromPoly ::
  (CoeffRing r, KnownNat n, IsMonomialOrder n ord) =>
  OrderedPolynomial r ord n ->
  ListPoly r ord n
fromPoly = polynomial . terms

commutes ::
  forall r n.
  (CoeffRing r, PrettyCoeff r, Arbitrary r) =>
  (ListPoly r Grevlex n -> ListPoly r Grevlex n -> ListPoly r Grevlex n) ->
  SNat n ->
  Property
commutes op (sdim :: SNat n) = withKnownNat sdim $
  forAll (join (liftA2 (,)) arbitrary) $ \(f, g) ->
    op f g === op g f

identity ::
  forall r n.
  (CoeffRing r, PrettyCoeff r, Arbitrary r) =>
  ListPoly r Grevlex n ->
  (ListPoly r Grevlex n -> ListPoly r Grevlex n -> ListPoly r Grevlex n) ->
  SNat n ->
  Property
identity eps op (sdim :: SNat n) = withKnownNat sdim $
  forAll arbitrary $ \f ->
    op eps f === f .&&. op f eps === f

test_normalForm :: TestTree
test_normalForm =
  testGroup
    "normal form"
    [ testProperty "addition gives normal form (F 5)" $
        checkForTypeNat [1 .. 3] $ checkBinNF @(F 5) (+)
    , testProperty "addition gives normal form (Q)" $
        checkForTypeNat [1 .. 3] $ checkBinNF @Rational (+)
    , testProperty "subtraction gives normal form (F 5)" $
        checkForTypeNat [1 .. 3] $ checkBinNF @(F 5) (-)
    , testProperty "subtraction gives normal form (Q)" $
        checkForTypeNat [1 .. 3] $ checkBinNF @Rational (-)
    , testProperty "f - f is normal form (F 5)" $
        checkForTypeNat [1 .. 3] $ checkUnNF @(F 5) (join (-))
    , testProperty "f - f is normal form (Q)" $
        checkForTypeNat [1 .. 3] $ checkUnNF @Rational (join (-))
    , testProperty "f + f + f + f + f is normal form (F 5)" $
        checkForTypeNat [1 .. 3] $ checkUnNF @(F 5) (\f -> f + f + f + f + f)
    , testProperty "2 f * 3 g is normal form over Z/6Z" $
        checkForTypeNat [1 .. 3] $
          checkBinNF @(Quotient 6 Integer)
            ( \f g ->
                ((fromInteger' 2 :: Quotient 6 Integer) .*. f)
                  * ((fromInteger' 3 :: Quotient 6 Integer) .*. g)
            )
    , testProperty "multiplication gives normal form (F 5)" $
        setSize 50 $
          checkForTypeNat [1 .. 3] $ checkBinNF @(F 5) (*)
    , testProperty "multiplication gives normal form (Q)" $
        setSize 50 $
          checkForTypeNat [1 .. 3] $ checkBinNF @Rational (*)
    , testProperty "splitLeadingTerm gives normal form (F 5)" $
        checkForTypeNat [1 .. 3] $ checkUnNF @(F 5) (snd . splitLeadingTerm)
    ]

checkUnNF ::
  forall r n.
  (CoeffRing r, PrettyCoeff r, Arbitrary r) =>
  (ListPoly r Grevlex n -> ListPoly r Grevlex n) ->
  SNat n ->
  Property
checkUnNF op sdim =
  withKnownNat sdim $
    forAll arbitrary $ \f ->
      isNormalForm (op f)

checkBinNF ::
  forall r n.
  (CoeffRing r, PrettyCoeff r, Arbitrary r) =>
  (ListPoly r Grevlex n -> ListPoly r Grevlex n -> ListPoly r Grevlex n) ->
  SNat n ->
  Property
checkBinNF op sdim = withKnownNat sdim $
  forAll arbitrary $ \f g ->
    isNormalForm (op f g)
