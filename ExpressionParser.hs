module ExpressionParser where
import Control.Applicative   hiding (many)
import Control.Arrow
import Data.Char
import Data.Maybe
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
monomial = many variableWithPower

term :: Parser (Rational, [(Variable, Integer)])
term = signed' $ try $ (,) <$> option 1 coefficient
                           <*> monomial
                   <|> (,) <$> number <*> pure []

signed' p = do
  s <- optional sign
  (c, n) <- p
  return (fromMaybe 1 s * c, n)
  where
    sign = lexeme $ char '-' *> return (negate 1)
                <|> char '+' *> return 1


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

parsePolyn :: String -> Either ParseError Polyn
parsePolyn = parse expression "polynomial"
