{-# LANGUAGE ConstraintKinds, DeriveFunctor, FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving     #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude                 #-}
{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings             #-}
{-# LANGUAGE ScopedTypeVariables, TypeOperators, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances, UndecidableSuperClasses            #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Algebra.Bridge.Singular.Syntax
       ( SingularOrder(..)
       , SingularCoeff(..)
       , IsSingularPolynomial
       , SingularExpr(..)
       , RingSpec(..)
       , SingularLibrary
       , SingularOption
       , RingCoeffSpec(..)
       , toRingSpec
       , PrettySingular(..)
       , prettySingularPolynomial
       , funE, coeffE, polyE, binE, listE, idealE, idealE', verbE, varE
       , SingularCommand(..)
       , SingularType(..)
       , SingularProgramM(..)
       , SingularProgram
       , exprC, declOnlyC, declC, letC, idealC'
       , idealC, ringC, polyC, libC
       , optionC, printC, directC
       )
       where
import           Algebra.Field.Prime
import           Algebra.Internal
import           Algebra.Prelude.Core
import           Algebra.Ring.Polynomial.Parser
import           Control.Monad.Trans.Writer
import           Data.List                      ()
import qualified Data.Semigroup                 as Semi
import           Data.Text                      (Text)
import qualified Data.Text                      as T
import           Data.Type.Ordinal.Builtin
import qualified Prelude                        as P

type SingularLibrary = Text

class IsMonomialOrder n ord => SingularOrder n ord where
  singularOrder :: q n -> p ord -> Text

instance KnownNat n => SingularOrder n Lex where
  singularOrder _ _ = "lp"

instance KnownNat n => SingularOrder n Grevlex where
  singularOrder _ _ = "dp"

instance (SingularOrder n o1, SingularOrder m o2, KnownNat m, KnownNat n, (n + m) ~ k)
      => SingularOrder k (ProductOrder n m o1 o2) where
  singularOrder _ _ =
    let (sn, sm) = (sing :: Sing n, sing :: Sing m)
    in T.concat ["(", singularOrder sn (Proxy :: Proxy o1), "(", tshow (natVal sn), "),"
                , singularOrder sm (Proxy :: Proxy o2), "(", tshow (natVal sm), "))"]

class (PrettyCoeff r, CoeffRing r) => SingularCoeff r where
  parseSingularCoeff :: Parser r

  prettySingularCoeff :: Int -> r -> ShowSCoeff
  prettySingularCoeff = showsCoeff

  coeffType :: proxy r -> RingCoeffSpec

instance SingularCoeff Rational where
  parseSingularCoeff = rationalP

  coeffType _ = Char 0

  prettySingularCoeff _ = prettyRat


prettyRat :: Rational -> ShowSCoeff
prettyRat r
  | r == 0 = Vanished
  | r == 1 = OneCoeff
  | r == -1 = Negative Nothing
  | r <  0 = Negative $ Just $ showParen True $
             shows (abs $ numerator r) . showChar '/' . shows (abs $ denominator r)
  | otherwise = Positive $
                shows (abs $ numerator r) . showChar '/' . shows (abs $ denominator r)

instance SingularCoeff Integer where
  parseSingularCoeff = integerP

  coeffType _ = IntegerCoeff

instance KnownNat p => SingularCoeff (F p) where
  parseSingularCoeff = rationalP

  coeffType = Char . char

-- | Polynomial type which can be encoded to/decoded from singular polynomials.
type IsSingularPolynomial poly =
  (IsOrderedPolynomial poly, SingularCoeff (Coefficient poly), SingularOrder (Arity poly) (MOrder poly))

data SingularExpr poly where
  SingVar        :: Text -> SingularExpr poly
  SingFunction   :: Text -> [SingularExpr poly] -> SingularExpr poly
  SingInfix      :: SingularExpr poly -> Text -> SingularExpr poly -> SingularExpr poly
  SingList       :: [SingularExpr poly] -> SingularExpr poly
  SingIdeal      :: [SingularExpr poly] -> SingularExpr poly
  SingPolynomial :: poly -> SingularExpr poly
  SingCoeff      :: Coefficient poly -> SingularExpr poly
  SingVerbatim   :: Text -> SingularExpr poly
  SingRing       :: RingSpec -> SingularExpr poly

data RingCoeffSpec = RealCoeff
                   | ComplexCoeff
                   | IntegerCoeff
                   | Char Natural
                   deriving (Read, Show, Eq, Ord)

data RingSpec where
  RingSpec :: SingularOrder n ord
           => RingCoeffSpec
           -> Sing n
           -> proxy ord
           -> RingSpec

coeffProxy :: proxy poly -> Proxy (Coefficient poly)
coeffProxy _ = Proxy

morderProxy :: proxy poly -> Proxy (MOrder poly)
morderProxy _ = Proxy

toRingSpec :: IsSingularPolynomial poly => proxy poly -> RingSpec
toRingSpec pxy =
  RingSpec (coeffType $ coeffProxy pxy) (sArity pxy) (morderProxy pxy)

class PrettySingular a where
  prettySingular :: a -> Text

prettySingularPolynomial :: (IsSingularPolynomial poly)
                         => poly -> Text
prettySingularPolynomial =
  let vs = generate sing $ \i -> "x(" ++ show (ordToNatural i) ++ ")"
  in T.pack . showPolynomialWith' True prettySingularCoeff vs 5

instance IsSingularPolynomial poly
      => PrettySingular (SingularExpr poly) where
  prettySingular (SingFunction fun args) =
    T.concat [ fun, "("
             , T.intercalate " , " $ map prettySingular args
             , ")"
             ]
  prettySingular (SingPolynomial f) = prettySingularPolynomial f
  prettySingular (SingCoeff c) = T.pack $ showsCoeffAsTerm (prettySingularCoeff 5 c) ""
  prettySingular (SingVerbatim src) = src
  prettySingular (SingIdeal args) =
    T.concat ["ideal(", T.intercalate " , " $ map prettySingular args ,")"]
  prettySingular (SingList args) =
    T.concat ["list(", T.intercalate " , " $ map prettySingular args ,")"]
  prettySingular (SingInfix l t r) =
    T.concat ["((", prettySingular l, ") ", t, " (", prettySingular r, "))" ]
  prettySingular (SingRing r) = prettySingular r
  prettySingular (SingVar v) = v

instance PrettySingular RingCoeffSpec where
  prettySingular RealCoeff = "real"
  prettySingular ComplexCoeff = "complex"
  prettySingular IntegerCoeff = "integer"
  prettySingular (Char p)     = tshow p

instance PrettySingular RingSpec where
  prettySingular (RingSpec coe vs ord) =
    withKnownNat vs $
    T.concat ["(", prettySingular coe
             , "),(x(0..", tshow (natVal vs P.- 1), ")),"
             , singularOrder vs ord
             ]

instance Num (Coefficient poly) => Num (SingularExpr poly) where
  fromInteger = SingCoeff . P.fromInteger
  (+) = binE "+"
  (*) = binE "*"
  (-) = binE "-"
  abs x = funE "absValue" [x]
  signum = error "No signum!"

instance Multiplicative (SingularExpr poly) where
  (*) = binE "*"

instance Additive (SingularExpr poly) where
  (+) = binE "+"

instance Unital (Coefficient poly) => Unital (SingularExpr poly) where
  one = coeffE one

funE :: Text -> [SingularExpr poly] -> SingularExpr poly
funE = SingFunction

polyE :: poly -> SingularExpr poly
polyE = SingPolynomial

coeffE :: Coefficient poly -> SingularExpr poly
coeffE = SingCoeff

listE :: [SingularExpr poly] -> SingularExpr poly
listE = SingList

idealE' :: Ideal poly -> SingularExpr poly
idealE' = SingIdeal . map SingPolynomial . generators

idealE :: [SingularExpr poly] -> SingularExpr poly
idealE = SingIdeal

binE :: Text -> SingularExpr poly -> SingularExpr poly -> SingularExpr poly
binE op l = SingInfix l op

verbE :: Text -> SingularExpr poly
verbE = SingVerbatim

varE :: Text -> SingularExpr poly
varE = SingVar

data SingularType = IdealT
                  | IntT
                  | RingT
                  | PolyT
                  | OtherT Text
                    deriving (Read, Show, Eq, Ord)

data SingularCommand where
  SingExpr       :: IsSingularPolynomial poly
                 => SingularExpr poly -> SingularCommand
  SingDeclOnly   :: SingularType -> Text -> SingularCommand
  SingDeclAssign :: IsSingularPolynomial poly
                 => SingularType -> Text -> SingularExpr poly -> SingularCommand
  SingAssign     :: IsSingularPolynomial poly
                 => Text -> SingularExpr poly -> SingularCommand
  SingLibrary    :: Text -> SingularCommand
  SingVerbD      :: Text -> SingularCommand
  Directive      :: Text -> SingularCommand

newtype SingularProgramM a = SingularProgramM (Writer [SingularCommand] a)
                           deriving (Functor, Applicative, Monad)

type SingularProgram = SingularProgramM ()

instance Semi.Semigroup (SingularProgramM a) where
  (SingularProgramM l) <> (SingularProgramM r) = SingularProgramM $ l >> r

instance a ~ () => Monoid (SingularProgramM a) where
  mempty = SingularProgramM $ return ()
  mappend (SingularProgramM l) (SingularProgramM r) = SingularProgramM $ l >> r

instance PrettySingular SingularType where
  prettySingular IdealT     = "ideal"
  prettySingular IntT       = "int"
  prettySingular RingT      = "ring"
  prettySingular PolyT      = "poly"
  prettySingular (OtherT t) = t

instance PrettySingular SingularCommand where
  prettySingular = (<> ";") .  go
    where
      go (SingLibrary lib) = T.concat ["LIB", " \"", lib, "\""]
      go (SingVerbD t) = t
      go (Directive t) = t
      go (SingExpr expr) = prettySingular expr
      go (SingDeclOnly typ val) =
        T.unwords [prettySingular typ, val]
      go (SingDeclAssign typ val expr) =
        T.unwords [prettySingular typ, val, "=", prettySingular expr]
      go (SingAssign val expr) =
        T.unwords [val, "=", prettySingular expr]

instance a ~ () => PrettySingular (SingularProgramM a) where
  prettySingular (SingularProgramM act) =
    T.unlines $ map prettySingular $ execWriter act

exprC :: (IsSingularPolynomial poly) => SingularExpr poly -> SingularProgram
exprC = SingularProgramM . tell . pure . SingExpr

declOnlyC :: SingularType -> Text -> SingularProgram
declOnlyC type_ val = SingularProgramM $ tell [SingDeclOnly type_ val]

declC :: (IsSingularPolynomial poly)
      => SingularType -> Text -> SingularExpr poly -> SingularProgramM (SingularExpr poly)
declC type_ val expr = do
  SingularProgramM $ tell [SingDeclAssign type_ val expr]
  return $ varE val

letC :: (IsSingularPolynomial poly)
     => Text -> SingularExpr poly -> SingularProgram
letC val expr = SingularProgramM $ tell [SingAssign  val expr]

idealC' :: (IsSingularPolynomial poly)
        => Text -> Ideal poly -> SingularProgramM (SingularExpr poly)
idealC' val = declC IdealT val . idealE'

idealC :: (IsSingularPolynomial poly) => Text -> [SingularExpr poly] -> SingularProgramM (SingularExpr poly)
idealC val = declC IdealT val . idealE

ringC :: IsSingularPolynomial poly
      => Text -> proxy poly -> SingularProgramM (SingularExpr poly)
ringC val r = declC RingT val (SingRing $ toRingSpec r)

polyC :: (IsSingularPolynomial poly) => Text -> poly -> SingularProgramM (SingularExpr poly)
polyC val = declC PolyT val . polyE

libC :: Text -> SingularProgram
libC lib = SingularProgramM $ tell [SingLibrary lib]

directC :: Text -> SingularProgram
directC = SingularProgramM . tell . pure . Directive

optionC :: SingularOption -> SingularProgram
optionC t = SingularProgramM $ tell [SingVerbD ("option(" <> t <> ")")]

printC :: (IsSingularPolynomial poly) => SingularExpr poly -> SingularProgram
printC x = exprC $ funE "print" [x]

type SingularOption = Text
