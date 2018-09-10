{-# LANGUAGE ConstraintKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude                    #-}
{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings                #-}
{-# LANGUAGE ScopedTypeVariables, TypeSynonymInstances                   #-}
{-# LANGUAGE UndecidableInstances, UndecidableSuperClasses               #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Algebra.Bridge.Singular
       ( singular
       , readSingularPoly
       , readSingularIdeal
       , evalSingularWith, evalSingular
       , evalSingularIdealWith
       , evalSingularPolyWith
       , module Algebra.Bridge.Singular.Syntax
       ) where
import Algebra.Bridge.Singular.Syntax

import           Algebra.Prelude.Core
import           Algebra.Ring.Polynomial.Parser
import           Data.List                      ()
import           Data.Maybe                     (fromMaybe)
import           Data.Text                      (Text)
import qualified Data.Text                      as T
import           Data.Type.Ordinal.Builtin
import           System.Exit
import           System.Process.Text
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer     as L

symbol :: Text -> Parser Text
symbol = L.symbol space

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

parens :: Parser a -> Parser a
parens p = symbol "(" *> p <* symbol ")"

readProcess :: FilePath -> [String] -> Text -> IO Text
readProcess exe args input = do
  (ec, out, _) <- readProcessWithExitCode exe args input
  case ec of
    ExitSuccess -> return out
    _ -> fail $ "Process failed: " ++ unwords (exe : args)

singular :: Text -> IO Text
singular = readProcess "Singular" ["-q"]

readSingularIdeal :: (IsSingularPolynomial poly)
                  => proxy poly
                  -> Text
                  -> Maybe [poly]
readSingularIdeal p code =
  mapM (readSingularPoly p . (fromMaybe <*> T.stripSuffix ",")) $
  T.lines code

readSingularPoly :: (IsSingularPolynomial poly)
                 => proxy poly
                 -> Text
                 -> Maybe poly
readSingularPoly _ code =
  either (const Nothing) Just $ parsePolynomialWith parseSingularCoeff varP code
  where
    varP = do
      void $ symbol "x"
      i <- option 0 $ parens (lexeme L.decimal)
      case naturalToOrd i of
        Nothing -> fail "variable out of range"
        Just o  -> return o

evalSingularWith :: IsSingularPolynomial p
                 => [SingularLibrary]
                 -> [SingularOption]
                 -> SingularExpr p -> IO Text
evalSingularWith libs opts expr =
  singular $ prettySingular $ do
    mapM_ libC libs
    mapM_ optionC opts
    void $ ringC "R" expr
    printC expr
    directC "exit"

evalSingular :: IsSingularPolynomial p
             => SingularExpr p -> IO Text
evalSingular = evalSingularWith [] []

evalSingularIdealWith :: (IsSingularPolynomial r)
                      => [SingularLibrary]
                      -> [SingularOption]
                      -> SingularExpr r -> IO (Ideal r)
evalSingularIdealWith libs opts expr =
  maybe (fail "Parse failed") (return . toIdeal) . readSingularIdeal expr
  =<< evalSingularWith libs opts expr

evalSingularPolyWith :: (IsSingularPolynomial r)
                     => [SingularLibrary]
                     -> [SingularOption]
                     -> SingularExpr r -> IO r
evalSingularPolyWith libs opts expr =
  maybe (fail "Parse failed") return . readSingularPoly expr
    =<< evalSingularWith libs opts expr

