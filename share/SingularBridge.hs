{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module SingularBridge (singIdealFun, singPolyFun) where
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial hiding (lex)
import           Control.Applicative
import           Data.Char
import           Data.List
import           Data.Proxy
import           Data.Ratio
import           Data.Singletons
import qualified Data.Text               as T
import           Data.Type.Natural
import           Numeric
import           System.IO.Unsafe
import           System.Process

class IsMonomialOrder ord => SingularOrder ord where
  singularOrder :: p ord -> String

instance SingularOrder Lex where
  singularOrder _ = "lp"

instance SingularOrder Grevlex where
  singularOrder _ = "dp"

idealProgram :: forall ord n. (SingularOrder ord, SingRep n)
             => String
             -> Ideal (OrderedPolynomial Rational ord n)
             -> String
idealProgram fun ideal =
  let vars = [(i, "x(" ++ show i ++ ")") | i <- [0.. sNatToInt (sing :: SNat n) - 1]]
      istr = intercalate ", " $ map (showPolynomialWith True vars showRational) $ generators ideal
  in (++";") $ intercalate ";\n"

     [ "LIB \"primdec.lib\""
     , "ring R = 0,(x(0.." ++ show (sNatToInt (sing :: SNat n) - 1) ++ "))," ++ singularOrder (Proxy :: Proxy ord)
     , "ideal I = " ++ istr
     , "option(redSB)"
     , "print(" ++ fun ++ "(std(I)))"
     , "exit"
     ]

singular :: String -> IO String
singular code = readProcess "singular" ["-q"] code

readSingularIdeal :: (SingRep n, IsMonomialOrder ord)
                  => SNat n -> Proxy ord -> String -> [OrderedPolynomial Rational ord n]
readSingularIdeal n p (T.pack -> code) =
  map (readSingularPoly n p  . T.unpack) $ T.splitOn ",\n" code

readSingularPoly :: (SingRep n, IsMonomialOrder ord)
                 => SNat n -> Proxy ord -> String -> OrderedPolynomial Rational ord n
readSingularPoly _ _ code =
  case [p | (p, xs) <- readPoly code, all isSpace xs] of
    [p] -> p
    _ -> error "Reading"
  where
    readPoly st =  do
      (t, rest) <- readTerm st
      readPoly' rest t

    readPoly' st  acc = do ("+", st') <- lex st
                           (t, rest) <- readTerm st'
                           readPoly' rest (acc + t)
                    <|> do ("-", st') <- lex st
                           (t, rest) <- readTerm st'
                           readPoly' rest (acc - t)
                    <|> return (acc, st)

    readCoeff st = do
      (modify, st') <- do { ("-", roo) <- lex st ; return (negate, roo) } <|> return (id, st)
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
    readTerm' st = do ("*", st') <- lex st
                      (a, rest) <- readFactor st'
                      (as, gomi) <- readTerm' rest
                      return (a: as, gomi)
                  <|> return ([], st)

    readFactor st = readCoeff st <|> readVar st

    readVar st  = do
            ("x", '(':rest) <- lex st
            (nstr, ')':mpow) <- lex rest
            (nth, "") <- readDec nstr
            (power, gomi) <- do ("^", rst'') <- lex mpow
                                (pow, gomi) <- readDec rst''
                                return (pow :: Integer, gomi)
                            <|> return (1, mpow)
            return (var (toEnum nth) ^ power, gomi)

singIdealFun :: forall ord n. (SingularOrder ord, SingRep n)
             => String -> Ideal (OrderedPolynomial Rational ord n) -> Ideal (OrderedPolynomial Rational ord n)
singIdealFun fun ideal = unsafePerformIO $ do
  ans <- singular $ idealProgram fun ideal
  return $ toIdeal $ readSingularIdeal (sing :: SNat n) (Proxy :: Proxy ord) ans

singPolyFun :: forall ord n. (SingularOrder ord, SingRep n)
            => String
            -> Ideal (OrderedPolynomial Rational ord n)
            -> OrderedPolynomial Rational ord n
singPolyFun fun ideal = unsafePerformIO $ do
  ans <- singular $ idealProgram fun ideal
  return $ readSingularPoly (sing :: SNat n) (Proxy :: Proxy ord) ans
