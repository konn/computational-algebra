{-# LANGUAGE FlexibleContexts, QuasiQuotes, TemplateHaskell #-}
module Algebra.Ring.Polynomial.Parser ( monomial, expression, variable, variableWithPower
                                      , number, integer, natural, parsePolyn) where
import           Algebra.Ring.Polynomial.Monomorphic
import           Control.Applicative                 hiding (many)
import qualified Data.Map                            as M
import           Numeric.Field.Fraction              (Fraction, (%))
import           Text.Peggy

[peggy|
expression :: Polynomial (Fraction Integer)
  = space* e:expr space*  !. { e }

letter :: Char
  = [a-zA-Z]

variable :: Variable
  = letter ('_' integer)? { Variable $1 (fromInteger <$> $2) }

variableWithPower :: (Variable, Integer)
  = variable "^" natural { ($1, $2) }
  / variable  { ($1, 1) }

expr :: Polynomial (Fraction Integer)
  = expr "+" term { $1 + $2 }
  / expr "-" term { $1 - $2 }
  / term

term :: Polynomial (Fraction Integer)
   = number space* monoms { injectCoeff $1 * $3 }
   / number { injectCoeff $1 }
   / monoms

monoms :: Polynomial (Fraction Integer)
  = monoms space * fact { $1 * $3 }
  / fact

fact :: Polynomial (Fraction Integer)
  = fact "^" natural { $1 ^ $2 }
  / "(" expr ")"
  / monomial { toPolyn [($1, 1)] }

monomial ::: Monomial
  = variableWithPower+ { M.fromListWith (+) $1 }

number :: (Fraction Integer)
  = integer "/" integer { $1 % $2 }
  / integer '.' [0-9]+ { (read (show $1 ++ $2) :: Integer) % toInteger (length $2) }
  / integer { fromInteger $1 }

integer :: Integer
  = "-" natural { negate $1 }
  / natural

natural :: Integer
  = [1-9] [0-9]* { read ($1 : $2) }

delimiter :: ()
  = [()^+] { () }
  / '-' ![0-9] {()}
|]

toPolyn :: [(Monomial, Fraction Integer)] -> Polynomial (Fraction Integer)
toPolyn = normalize . Polynomial . M.fromList

parsePolyn :: String -> Either ParseError (Polynomial (Fraction Integer))
parsePolyn = parseString expression "polynomial"
