{-# LANGUAGE FlexibleInstances, RecordWildCards, TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances                             #-}
{-# OPTIONS_GHC -fno-warn-orphans                             #-}
-- | This module provides less polymorphic interface to manipulate polynomials.
module MonomorphicPolynomial where
import           BaseTypes
import           Control.Arrow
import           Data.List
import qualified Data.Map      as M
import           Polynomial
import           Wrappers

data Variable = Variable { varName  :: Char
                         , varIndex :: Maybe Int
                         } deriving (Eq, Ord)

instance Show Variable where
  showsPrec _ v = showChar (varName v) . maybe id ((showChar '_' .) . shows) (varIndex v)

type Polyn = [(Rational, [(Variable, Integer)])]

buildVarsList :: Polyn -> [Variable]
buildVarsList = nub . sort . concatMap (map fst . snd)

encodeMonomList :: [Variable] -> [(Variable, Integer)] -> [Int]
encodeMonomList vars mono = map (maybe 0 fromInteger . flip lookup mono) vars

encodeMonomial :: [Variable] -> [(Variable, Integer)] -> Monomorphic (Vector Int)
encodeMonomial vars mono = promote $ encodeMonomList vars mono

encodePolynomial :: Polyn -> Monomorphic (Polynomial Rational)
encodePolynomial = promote . toPolynomialSetting

toPolynomialSetting :: Polyn -> PolynomialSetting
toPolynomialSetting p =
    PolySetting { polyn = p
                , dimension = promote $ length $ buildVarsList p
                }

data PolynomialSetting = PolySetting { dimension :: Monomorphic SNat
                                     , polyn     :: Polyn
                                     } deriving (Show)


instance Wrappable (Polynomial Rational) where
  type BasicType (Polynomial Rational) = PolynomialSetting
  promote PolySetting{..} =
    case dimension of
      Monomorphic dim ->
          case singInstance dim of
            SingInstance -> Monomorphic $ polynomial $ M.fromList (map ((OrderedMonomial . fromList dim . encodeMonomList vars . snd) &&& fst) polyn)
    where
      vars = buildVarsList polyn
  demote (Monomorphic f) =
      PolySetting { polyn = map (second $ toMonom . map toInteger . demote . Monomorphic) $ getTerms f
                  , dimension = Monomorphic $ sDegree f
                  }
    where
      toMonom = zip $ Variable 'X' Nothing : [Variable 'X' (Just i) | i <- [1..]]
