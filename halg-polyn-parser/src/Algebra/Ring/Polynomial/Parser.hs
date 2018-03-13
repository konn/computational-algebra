{-# LANGUAGE CPP, DataKinds, FlexibleContexts, GADTs, KindSignatures       #-}
{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction                  #-}
{-# LANGUAGE OverloadedStrings, PartialTypeSignatures, ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies                                                  #-}
module Algebra.Ring.Polynomial.Parser
       ( unlabeldVarP, labeledVarP, polynomialP
       , rationalP, integerP
       , parsePolynomialWith
       , Parser , VariableParser
       )
       where
import           Algebra.Ring.Polynomial.Class
import           Algebra.Ring.Polynomial.Monomial
import           AlgebraicPrelude                 hiding (char)
import           Control.Arrow                    (left)
import qualified Data.Ratio                       as P
import           Data.Singletons.Prelude
import           Data.Singletons.Prelude.List
import qualified Data.Text                        as T
import           Data.Type.Ordinal.Builtin
import           Data.Void
import           GHC.TypeLits
import qualified Prelude                          as P
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer       as L
import           Text.Megaparsec.Expr

lexeme :: (MonadParsec e T.Text m) => m a -> m a
lexeme  = L.lexeme space

symbol :: (MonadParsec e T.Text m) => T.Text -> m T.Text
symbol = L.symbol space

type Parser = Parsec Void T.Text
type VariableParser n = Parser (Ordinal n)

unlabeldVarP :: (KnownNat n)
             => proxy n -> T.Text -> VariableParser n
unlabeldVarP pxy pfx = lexeme $ do
  i <- symbol pfx *> char '_' *> L.decimal
  case naturalToOrd i of
    Just o -> return o
    Nothing -> fail $ "Number " ++ show i ++ " is out of bound: " ++ show (natVal pxy)

fromSingList :: Sing (list :: [Symbol]) -> [T.Text]
#if MIN_VERSION_singletons(2,3,0)
fromSingList = fromSing
#else
fromSingList = map T.pack . fromSing
#endif

labeledVarP :: forall list.
               Sing (list :: [Symbol]) -> VariableParser (Length list)
labeledVarP slist =
  choice $ zipWith go (enumOrdinal $ sLength slist) $ fromSingList slist
  where
    go i v = i <$ symbol v

varPowP :: KnownNat n => VariableParser n -> Parser (OrderedMonomial ord n)
varPowP vp = lexeme $
  pow <$> (orderMonomial Proxy . varMonom sing <$> vp)
      <*> option (1 :: Natural) (symbol "^" *> L.decimal)

monomialP :: KnownNat n => VariableParser n -> Parser (OrderedMonomial ord n)
monomialP v =
  product <$> varPowP v `sepBy1` optional (symbol "*")

factorP :: (IsOrderedPolynomial poly)
        => proxy poly -> Parser (Coefficient poly) -> VariableParser (Arity poly) -> Parser poly
factorP _ coeffP varP = injectCoeff <$> lexeme coeffP
                    <|> fromOrderedMonomial <$> monomialP varP

binary :: MonadParsec e Text m => Text -> (a -> a -> a) -> Operator m a
binary  name f = InfixL  (f <$ symbol name)

prefix :: MonadParsec e Text m => Text -> (a -> a) -> Operator m a
prefix  name f = Prefix  (f <$ symbol name)

table :: (CoeffRing a, MonadParsec e Text m) => [[Operator m a]]
table = [ [ prefix "-" negate
          , prefix "+" id
          ]
        , [ binary "*" (*) ]
        , [ binary "+" (+) , binary "-" (-)]
        ]

polynomialP :: (IsOrderedPolynomial poly)
            => Parser (Coefficient poly) -> VariableParser (Arity poly) -> Parser poly
polynomialP coeffP varP = body
  where body = makeExprParser (factorP Proxy coeffP varP) table

rationalP :: Field k => Parser k
rationalP = fromRat . P.toRational <$> L.scientific

integerP :: Parser Integer
integerP = fromInteger' <$> L.decimal

fromRat :: Field k => P.Rational -> k
fromRat r = fromInteger' (P.numerator r) / fromInteger' (P.denominator r)

parsePolynomialWith :: (IsOrderedPolynomial poly)
                    => Parser (Coefficient poly) -> VariableParser (Arity poly)
                    -> T.Text
                    -> Either String poly
parsePolynomialWith coeffP varP =
  left parseErrorPretty . parse (space *> polynomialP coeffP varP <* eof) "input"
