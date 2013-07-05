{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuasiQuotes #-}
module Algebra.Ring.Polynomial.Parser ( monomial, expression, variable, variableWithPower
                                      , number, integer, natural, parsePolyn) where
import           Algebra.Ring.Polynomial.Monomorphic
import           Control.Applicative                 hiding (many)
import qualified Data.Map                            as M
import           Data.Ratio
import qualified Numeric.Algebra as NA
import           Text.Peggy

[peggy|
expression :: Polynomial Rational
  = expr !.

letter :: Char
  = [a-zA-Z]

variable :: Variable
  = letter ('_' integer)? { Variable $1 (fromInteger <$> $2) }

variableWithPower :: (Variable, Integer)
  = variable "^" natural { ($1, $2) }
  / variable  { ($1, 1) }

expr :: Polynomial Rational
  = expr "+" term { $1 + $2 }
  / expr "-" term { $1 - $2 }
  / term

term :: Polynomial Rational
   = number space* monoms { injectCoeff $1 * $3 }
   / number { injectCoeff $1 }
   / monoms

monoms :: Polynomial Rational
  = monoms space * fact { $1 * $3 }
  / fact

fact :: Polynomial Rational
  = fact "^" natural { $1 ^ $2 }
  / "(" expr ")"
  / monomial { toPolyn [($1, 1)] }

monomial :: Monomial
  = variableWithPower+ { M.fromListWith (+) $1 }

number :: Rational
  = integer "/" integer { $1 % $2 }
  / integer '.' [0-9]+ { realToFrac (read (show $1 ++ '.' : $2) :: Double) }
  / integer { fromInteger $1 }

integer :: Integer
  = "-" natural { negate $1 }
  / natural

natural :: Integer
  = [1-9] [0-9]* { read ($1 : $2) }

|]

toPolyn :: [(Monomial, Ratio Integer)] -> Polynomial (Ratio Integer)
toPolyn = normalize . Polynomial . M.fromList

parsePolyn :: String -> Either ParseError (Polynomial Rational)
parsePolyn = parseString expression "polynomial"
