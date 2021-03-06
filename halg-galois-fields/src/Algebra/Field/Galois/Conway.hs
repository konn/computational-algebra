{-# LANGUAGE DataKinds, FlexibleInstances, LiberalTypeSynonyms            #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE MultiParamTypeClasses, TemplateHaskell, TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Algebra.Field.Galois.Conway
       (Conway,
        ConwayPolynomial(..),
        addConwayPolynomials,
        conwayFile) where
import Algebra.Field.Galois.Internal
import Algebra.Prelude.Core
import System.Directory
import Language.Haskell.TH           (runIO, DecsQ)

do dat <- tail . init . lines <$> runIO do
    fp : _ <- filterM doesFileExist 
      ["data/conway.txt", "halg-galois-fields/data/conway.txt"]
    readFile fp
   concat <$> mapM (buildInstance . head . parseLine) dat

-- | Macro to add Conway polynomials dictionary.
addConwayPolynomials :: [(Integer, Integer, [Integer])] -> DecsQ
addConwayPolynomials = fmap concat . mapM buildInstance

-- | Parse conway polynomial file and define instances for them.
--   File-format must be the same as
--   <http://www.math.rwth-aachen.de/~Frank.Luebeck/data/ConwayPol/index.html?LANG=en Lueback's file>.
conwayFile :: FilePath -> DecsQ
conwayFile fp = do
  dat <- tail . init . lines <$> runIO (readFile fp)
  addConwayPolynomials $ concatMap parseLine dat
