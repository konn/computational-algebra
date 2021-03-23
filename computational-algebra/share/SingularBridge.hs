{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module SingularBridge (singIdealFun, singPolyFun) where

import Algebra.Internal
import Algebra.Ring.Ideal
import Algebra.Ring.Polynomial hiding (lex)
import Control.Applicative
import Data.Char
import Data.List
import Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.Text as T
import Numeric
import Numeric.Field.Fraction
import System.IO.Unsafe
import System.Process

class IsStrongMonomialOrder ord => SingularOrder ord where
  singularOrder :: p ord -> String

instance SingularOrder Lex where
  singularOrder _ = "lp"

instance SingularOrder Grevlex where
  singularOrder _ = "dp"

idealProgram ::
  forall ord n.
  (SingularOrder ord, KnownNat n) =>
  String ->
  Ideal (OrderedPolynomial (Fraction Integer) ord n) ->
  String
idealProgram fun ideal =
  withStrongMonomialOrder (Proxy :: Proxy ord) (sNat :: SNat n) $
    let vars = generate sing $ \i -> "x(" ++ show (fromEnum i) ++ ")"
        istr = intercalate ", " $ map (showPolynomialWith vars 5) $ generators ideal
     in (++ ";") $
          intercalate
            ";\n"
            [ "LIB \"primdec.lib\""
            , "LIB \"f5_library.lib\""
            , "ring R = 0,(x(0.." ++ show (sNatToInt (sNat :: SNat n) - 1) ++ "))," ++ singularOrder (Proxy :: Proxy ord)
            , "ideal I = " ++ istr
            , "option(redSB)"
            , "print(" ++ fun ++ "(I))"
            , "exit"
            ]

singular :: String -> IO String
singular code = readProcess "singular" ["-q"] code

readSingularIdeal ::
  (KnownNat n, IsStrongMonomialOrder ord) =>
  SNat n ->
  Proxy ord ->
  String ->
  [OrderedPolynomial (Fraction Integer) ord n]
readSingularIdeal n p (T.pack -> code) =
  mapMaybe (readSingularPoly n p . T.unpack) $ map (\a -> fromMaybe a $ T.stripSuffix "," a) $ T.lines code

readSingularPoly ::
  (KnownNat n, IsStrongMonomialOrder ord) =>
  SNat n ->
  Proxy ord ->
  String ->
  Maybe (OrderedPolynomial (Fraction Integer) ord n)
readSingularPoly n pxy code =
  withStrongMonomialOrder pxy n $
    case [p | (p, xs) <- readPoly code, all isSpace xs] of
      (p : _) -> Just p
      _ -> Nothing
  where
    readPoly st = do
      (t, rest) <- readTerm st
      readPoly' rest t

    readPoly' st acc =
      do
        ("+", st') <- lex st
        (t, rest) <- readTerm st'
        readPoly' rest (acc + t)
        <|> do
          ("-", st') <- lex st
          (t, rest) <- readTerm st'
          readPoly' rest (acc - t)
        <|> return (acc, st)

    readCoeff st = do
      (modify, st') <- do { ("-", roo) <- lex st; return (negate, roo) } <|> return (id, st)
      (num, rest) <- readDec st'
      (a, foo) <- lex rest
      case a of
        "/" -> do
          (den, rest') <- readDec foo
          return (injectCoeff $ modify $ num % den, rest')
        _ -> return (injectCoeff $ modify $ num % 1, rest)

    readTerm st = do
      (a, rest) <- readFactor st
      (ts, gomi) <- readTerm' rest
      return (product (a : ts), gomi)
    readTerm' st =
      do
        ("*", st') <- lex st
        (a, rest) <- readFactor st'
        (as, gomi) <- readTerm' rest
        return (a : as, gomi)
        <|> return ([], st)

    readFactor st = readCoeff st <|> readVar st

    readVar st = do
      ("x", '(' : rest) <- lex st
      (nstr, ')' : mpow) <- lex rest
      (nth, "") <- readDec nstr
      (power, gomi) <-
        do
          ("^", rst'') <- lex mpow
          (pow, gomi) <- readDec rst''
          return (pow :: Integer, gomi)
          <|> return (1, mpow)
      return (var (toEnum nth) ^ power, gomi)

singIdealFun ::
  forall ord n.
  (SingularOrder ord, KnownNat n) =>
  String ->
  Ideal (OrderedPolynomial (Fraction Integer) ord n) ->
  Ideal (OrderedPolynomial (Fraction Integer) ord n)
singIdealFun fun ideal =
  withStrongMonomialOrder (Proxy :: Proxy ord) (sNat :: SNat n) $
    unsafePerformIO $ do
      ans <- singular $ idealProgram fun ideal
      return $ toIdeal $ readSingularIdeal (sNat :: SNat n) (Proxy :: Proxy ord) ans

singPolyFun ::
  forall ord n.
  (SingularOrder ord, KnownNat n) =>
  String ->
  Ideal (OrderedPolynomial (Fraction Integer) ord n) ->
  OrderedPolynomial (Fraction Integer) ord n
singPolyFun fun ideal = unsafePerformIO $ do
  ans <- singular $ idealProgram fun ideal
  let Just p = readSingularPoly (sNat :: SNat n) (Proxy :: Proxy ord) ans
  return p
