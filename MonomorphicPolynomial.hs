{-# LANGUAGE FlexibleInstances, PolyKinds, RecordWildCards, TypeFamilies #-}
{-# LANGUAGE TypeOperators, ViewPatterns                                 #-}
{-# OPTIONS_GHC -fno-warn-orphans                             #-}
-- | This module provides less polymorphic interface to manipulate polynomials.
module MonomorphicPolynomial where
import           Algorithms
import           BaseTypes
import           Control.Arrow
import           Data.List
import qualified Data.Map      as M
import           Data.Maybe
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

newtype (:.:) f g a = Compose { getComposed :: f (g a) }

uniformlyPromote :: [Polyn] -> Monomorphic (Ideal :.: Polynomial Rational)
uniformlyPromote ps  =
  case promote (length vars) of
    Monomorphic dim ->
      case singInstance dim of
        SingInstance -> Monomorphic $ Compose $ toIdeal $ map (polynomial . M.fromList . map (OrderedMonomial . fromList dim . encodeMonomList vars . snd &&& fst)) ps
  where
    vars = nub $ sort $ concatMap buildVarsList ps

instance Wrappable (Ideal :.: Polynomial Rational) where
  type BasicType (Ideal :.: Polynomial Rational) = [Polyn]
  promote = uniformlyPromote
  demote (Monomorphic (Compose (Ideal v))) = map (polyn . demote) $ map Monomorphic $ toList v

calcGroebnerBasis' :: [Polyn] -> [Polyn]
calcGroebnerBasis' (filter (any ((/= 0).fst)) -> []) = []
calcGroebnerBasis' j =
  case uniformlyPromote j of
    Monomorphic (Compose ideal) ->
      case ideal of
        Ideal vec ->
          case singInstance (sDegree (head $ toList vec)) of
            SingInstance -> map (renameVars vars . polyn . demote . Monomorphic) $ calcGroebnerBasis ideal
  where
    vars = nub $ sort $ concatMap buildVarsList j

promoteList :: [Polyn] -> Monomorphic ([] :.: Polynomial Rational)
promoteList ps =
  case promote (length vars) of
    Monomorphic dim ->
      case singInstance dim of
        SingInstance -> Monomorphic $ Compose $ map (polynomial . M.fromList . map (OrderedMonomial . fromList dim . encodeMonomList vars . snd &&& fst)) ps
  where
    vars = nub $ sort $ concatMap buildVarsList ps

isIdealMember' :: Polyn -> [Polyn] -> Bool
isIdealMember' f ideal =
  case promoteList (f:ideal) of
    Monomorphic (Compose (f':ideal')) ->
      case singInstance (sDegree f') of
        SingInstance -> isIdealMember f' (toIdeal ideal')
    _ -> error "impossible happend!"

renameVars :: [Variable] -> Polyn -> Polyn
renameVars vars = map (second $ map $ first ren)
  where
    ren v = fromMaybe v $ lookup v dic
    dic = zip (Variable 'X' Nothing : [Variable 'X' (Just i) | i <- [1..]]) vars

showPolyn :: Polyn -> String
showPolyn f =
  case encodePolynomial f of
    Monomorphic f' ->
        case singInstance (sDegree f') of
          SingInstance -> showPolynomialWithVars dic f'
  where
    dic = zip [1..] $ map show $ buildVarsList f
