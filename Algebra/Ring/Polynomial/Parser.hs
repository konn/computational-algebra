{-# LANGUAGE FlexibleContexts, QuasiQuotes, TemplateHaskell, TupleSections #-}
module Algebra.Ring.Polynomial.Parser
       ( monomial, expression, variable, variableWithPower
       , number, integer, natural, parsePolyn)
       where
import           Algebra.Ring.Polynomial.Monomorphic
import           Control.Applicative                 hiding (many)
import qualified Data.Map                            as M
import           Data.Monoid                         (mempty)
import qualified Data.Ratio                          as P
import           Numeric.Field.Fraction              (Fraction, (%))
import           Text.Trifecta

expression :: Parser (Polynomial (Fraction Integer))
expression  = spaces *> expr <* eof

expr :: Parser (Polynomial (Fraction Integer))
expr = chainl1 term ops
  where
    ops = (+) <$ symbolic '+'
      <|> (-) <$ symbolic '-'


term :: Parser (Polynomial (Fraction Integer))
term = (*) <$> (injectCoeff <$> number)
           <*  spaces
           <*> factor
   <|> injectCoeff <$> number
   <|> factor

factor :: Parser (Polynomial (Fraction Integer))
factor = toPolyn . (:[]) . (,1) <$> monomial
     <|> parens expr
     <|> (^) <$> factor <* symbolic '^' <*> natural

monomial :: Parser Monomial
monomial = M.fromListWith (+) <$> many variableWithPower

variableWithPower :: Parser (Variable, Integer)
variableWithPower =
      (,)  <$> variable <*> option 1 (symbolic '^' *> natural)

variable :: Parser Variable
variable = lexeme $ Variable <$> letter
                             <*> optional (fromInteger <$ char '_' <*> integer)

lexeme :: CharParsing f => f a -> f a
lexeme p = p <* spaces

number :: Parser (Fraction Integer)
number = try ((%) <$> integer <* symbolic '/' <*> integer)
     <|> either (%1) d2f <$> integerOrDouble

d2f :: Real a => a -> Fraction Integer
d2f d =
  let r = toRational d
  in P.numerator r % P.denominator r

toPolyn :: [(Monomial, Fraction Integer)] -> Polynomial (Fraction Integer)
toPolyn = normalize . Polynomial . M.fromList

parsePolyn :: String -> Either String (Polynomial (Fraction Integer))
parsePolyn = eithResult . parseString expression mempty

eithResult :: Result b -> Either String b
eithResult (Success a) = Right a
eithResult (Failure d) = Left $ show d
