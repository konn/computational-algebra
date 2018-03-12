{-# LANGUAGE GADTs, OverloadedStrings, QuasiQuotes #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module SingularBench where
import           Algebra.Internal
import           Algebra.Ring.Polynomial (Coefficient (..), ProductOrder (..),
                                          WeightOrder (..), WeightProxy (..),
                                          showRational)
import           Control.Arrow
import           Data.List
import qualified Data.Map                as M
import           Data.Monoid
import           Data.Singletons
import           Data.Type.Natural
import           System.Process

formatPoly :: Polynomial (Fraction Integer) -> String
formatPoly (Polynomial dic) = intercalate "+" $
   map (uncurry formatTerm) $ M.toList dic

formatTerm :: M.Map Variable Integer -> (Fraction Integer) -> String
formatTerm k v
    | M.null k  = showCoeff $ showRational v
    | otherwise = concat ["(", showCoeff $ showRational v, ")*", formatMonom k]

showCoeff :: Coefficient -> String
showCoeff Zero = "0"
showCoeff (Negative str) = '-':str
showCoeff (Positive str) = str
showCoeff Eps = "1"

formatMonom :: Monomial -> String
formatMonom = intercalate "*" . map (uncurry (++) <<< show *** ('^':).show) . M.toList

formatIdeal :: [Polynomial (Fraction Integer)] -> String
formatIdeal = intercalate ", " . map formatPoly

class IsMonomialOrder ord => SingularRep ord where
  singularRep :: ord -> String

instance SingularRep Lex where
  singularRep _ = "lp"

instance SingularRep Grlex where
  singularRep _ = "Dp"

instance SingularRep Grevlex where
  singularRep _ = "dp"

instance (SingI n, SingularRep o1, SingularRep o2) => SingularRep (ProductOrder n o1 o2) where
  singularRep (ProductOrder n o1 o2) = concat ["(", singularRep o1, "(", show (sNatToInt n), "),"
                                              , singularRep o2, ")"
                                              ]

instance (ToWeightVector vec, SingularRep ord) => SingularRep (WeightOrder vec ord) where
  singularRep (WeightOrder vec ord) = concat ["(a(", init $ tail $ show $ tovec vec, "),"
                                             , singularRep ord, ")"
                                             ]
    where
      tovec :: WeightProxy v -> [Int]
      tovec NilWeight = []
      tovec (ConsWeight n ns) = sNatToInt n : tovec ns

type Ideal = [Polynomial (Fraction Integer)]

skeleton :: SingularRep ord => ord -> [Polynomial (Fraction Integer)] -> String
skeleton ord ideal =
    unlines [ "LIB \"poly.lib\";"
            , concat ["ring R = 0,("
                     ,intercalate "," (map show $ nub $ sort $ concatMap buildVarsList ideal)
                     , "),"
                     , singularRep ord, ";"]
            , "ideal I =" <> formatIdeal ideal <> ";"
            , "std(I);"
            , "quit;"
            ]
singularWith :: SingularRep ord => ord -> Ideal -> IO String
singularWith = (readProcess "singular" [] .) . skeleton

