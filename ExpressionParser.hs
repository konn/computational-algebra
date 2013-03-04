module ExpressionParser where
import Control.Applicative
import Control.Arrow
import Data.Char
import Data.Ratio
import MonomorphicPolynomial
import Text.Parsec           hiding (optional, (<|>))
import Text.Parsec.String

variable :: Parser Variable
variable = Variable <$> letter <*> optional (char '_' *> index)

variableWithPower :: Parser (Variable, Integer)
variableWithPower = (,) <$> lexeme variable <*> option 1 power
  where
    power = symbol '^' *> parseInt

index :: Parser Int
index = digitToInt <$> digit
    <|> read <$ symbol '{' <*> lexeme (many1 digit) <* symbol '}'

monomial :: Parser [(Variable, Integer)]
monomial = many1 variableWithPower

term :: Parser (Rational, [(Variable, Integer)])
term = (,) <$> option 1 coefficient
           <*> monomial

symbol :: Char -> Parser Char
symbol = lexeme . char

lexeme :: Parser a -> Parser a
lexeme p = p <* spaces

polyOp :: Parser (Polyn -> Polyn -> Polyn)
polyOp = minusPolyn <$ symbol '-'
    <|> (++) <$ symbol '+'
  where
    minusPolyn xs ys = xs ++ map (first negate) ys

expression :: Parser [(Rational, [(Variable, Integer)])]
expression = spaces *> count 1 term `chainl1` polyOp <* eof

coefficient :: Parser Rational
coefficient = char '(' *> number <* char ')'
          <|> number

number :: Parser Rational
number = try (toRational <$> parseDouble)
          <|> try (lexeme $ (%) <$> parseInt
                         <* symbol '/'
                         <*> parseInt)
          <|> toRational <$> parseInt

parseInt :: Parser Integer
parseInt = lexeme $ read <$> many1 digit

parseDouble :: Parser Double
parseDouble = lexeme $ do
  int <- many1 digit
  _ <- char '.'
  float <- many1 digit
  return $ read $ int ++ '.':float

parsePolyn :: String -> Either ParseError Polyn
parsePolyn = parse expression "polynomial"
