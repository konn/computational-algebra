module Algebra.Ring.Polynomial.Parser where
import           Algebra.Ring.Polynomial.Monomorphic
import           Control.Applicative                 hiding (many)
import           Control.Arrow
import           Data.Char
import qualified Data.Map                            as M
import           Data.Maybe
import           Data.Ratio
import qualified Numeric.Algebra                     as NA
import           Text.Parsec                         hiding (optional, (<|>))
import           Text.Parsec.String

variable :: Parser Variable
variable = Variable <$> letter <*> optional (char '_' *> index)

variableWithPower :: Parser (Variable, Integer)
variableWithPower = (,) <$> lexeme variable <*> option 1 power
  where
    power = symbol '^' *> parseInt

index :: Parser Int
index = digitToInt <$> digit
    <|> read <$ symbol '{' <*> lexeme (many1 digit) <* symbol '}'

monomial :: Parser Monomial
monomial = M.fromList <$> many variableWithPower

term :: Parser (Monomial, Rational)
term = signed' $ try $ flip (,) <$> option 1 coefficient
                                <*> monomial
                   <|> flip (,) <$> number <*> pure M.empty

signed' p = do
  s <- optional sign
  (n, c) <- p
  return (n, fromMaybe 1 s * c)
  where
    sign = lexeme $ char '-' *> return (negate 1)
                <|> char '+' *> return 1


symbol :: Char -> Parser Char
symbol = lexeme . char

lexeme :: Parser a -> Parser a
lexeme p = p <* spaces

toPolyn = normalize . Polynomial . M.fromList

polyOp :: Parser (Polynomial Rational -> Polynomial Rational -> Polynomial Rational)
polyOp = (NA.-) <$ symbol '-'
    <|> (NA.+) <$ symbol '+'

expression :: Parser (Polynomial Rational)
expression =  (spaces *> (toPolyn <$> count 1 term) `chainl1` polyOp <* eof)

coefficient :: Parser Rational
coefficient = char '(' *> number <* char ')'
          <|> number

number :: Parser Rational
number = signed $
              try (toRational <$> parseDouble)
          <|> try (lexeme $ (%) <$> parseInt
                         <* symbol '/'
                         <*> parseInt)
          <|> toRational <$> parseInt

parseInt :: Parser Integer
parseInt = lexeme $ read <$> many1 digit

signed :: Num b => Parser b -> Parser b
signed p = do
  s <- optional sign
  n <- p
  return $ fromMaybe 1 s * n
  where
    sign = lexeme $ char '-' *> return (negate 1)
                <|> char '+' *> return 1

parseDouble :: Parser Double
parseDouble = lexeme $ do
  int <- many1 digit
  _ <- char '.'
  float <- many1 digit
  return $ read $ int ++ '.':float

parsePolyn :: String -> Either ParseError (Polynomial Rational)
parsePolyn = parse expression "polynomial"
