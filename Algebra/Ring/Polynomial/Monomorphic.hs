{-# LANGUAGE DataKinds, FlexibleInstances, GADTs, PolyKinds, RecordWildCards #-}
{-# LANGUAGE TypeFamilies, TypeOperators                                     #-}
{-# OPTIONS_GHC -fno-warn-orphans                             #-}
module Algebra.Ring.Polynomial.Monomorphic where
import qualified Algebra.Algorithms.Groebner as Gr
import           Algebra.Internal
import           Algebra.Ring.Noetherian
import qualified Algebra.Ring.Polynomial     as Poly
import           Control.Arrow
import           Data.List
import qualified Data.Map                    as M
import           Data.Maybe
import           Monomorphic

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

encodePolynomial :: Polyn -> Monomorphic (Poly.Polynomial Rational)
encodePolynomial = promote . toPolynomialSetting

toPolynomialSetting :: Polyn -> PolynomialSetting
toPolynomialSetting p =
    PolySetting { polyn = p
                , dimension = promote $ length $ buildVarsList p
                }

data PolynomialSetting = PolySetting { dimension :: Monomorphic SNat
                                     , polyn     :: Polyn
                                     } deriving (Show)


instance Poly.IsMonomialOrder ord => Monomorphicable (Poly.OrderedPolynomial Rational ord) where
  type MonomorphicRep (Poly.OrderedPolynomial Rational ord) = PolynomialSetting
  promote PolySetting{..} =
    case dimension of
      Monomorphic dim ->
          case singInstance dim of
            SingInstance -> Monomorphic $ Poly.polynomial $ M.fromList (map ((Poly.OrderedMonomial . Poly.fromList dim . encodeMonomList vars . snd) &&& fst) polyn)
    where
      vars = buildVarsList polyn
  demote (Monomorphic f) =
      PolySetting { polyn = map (second $ toMonom . map toInteger . demote . Monomorphic) $ Poly.getTerms f
                  , dimension = Monomorphic $ Poly.sDegree f
                  }
    where
      toMonom = zip $ Variable 'X' Nothing : [Variable 'X' (Just i) | i <- [1..]]

uniformlyPromote :: Poly.IsMonomialOrder ord
                 => [Polyn] -> Monomorphic (Ideal :.: Poly.OrderedPolynomial Rational ord)
uniformlyPromote ps  =
  case promote (length vars) of
    Monomorphic dim ->
      case singInstance dim of
        SingInstance -> Monomorphic $ Comp $ toIdeal $ map (Poly.polynomial . M.fromList . map (Poly.OrderedMonomial . Poly.fromList dim . encodeMonomList vars . snd &&& fst)) ps
  where
    vars = nub $ sort $ concatMap buildVarsList ps

instance Poly.IsMonomialOrder ord => Monomorphicable (Ideal :.: Poly.OrderedPolynomial Rational ord) where
  type MonomorphicRep (Ideal :.: Poly.OrderedPolynomial Rational ord) = [Polyn]
  promote = uniformlyPromote
  demote (Monomorphic (Comp (Ideal v))) = map (polyn . demote . Monomorphic) $ toList v

promoteList :: Poly.IsMonomialOrder ord => [Polyn] -> Monomorphic ([] :.: Poly.OrderedPolynomial Rational ord)
promoteList ps =
  case promote (length vars) of
    Monomorphic dim ->
      case singInstance dim of
        SingInstance -> Monomorphic $ Comp $ map (Poly.polynomial . M.fromList . map (Poly.OrderedMonomial . Poly.fromList dim . encodeMonomList vars . snd &&& fst)) ps
  where
    vars = nub $ sort $ concatMap buildVarsList ps


{-
data Equal a b where
  Equal :: Equal a a

(%==) :: (a ~ b) => a -> b -> Equal a b
_ %== _ = Equal

thEliminationIdeal' :: Int -> [Polyn] -> [Polyn]
thEliminationIdeal' n [] = []
thEliminationIdeal' n ideal =
    let dim = length $ nub $ sort $ concatMap buildVarsList ideal
    in if n <= 0 || dim <= n
       then error "Degree error!"
       else case promoteList ideal of
              Monomorphic (Comp is@(f:_))->
                case singInstance (sDegree f) of
                  SingInstance ->
                      case promote n of
                        Monomorphic sn ->
                          case sDegree f %== (sn %+ sm) of
                            Equal -> demote $ Monomorphic $ Comp $ sn `thEliminationIdeal` toIdeal is
-}

renameVars :: [Variable] -> Polyn -> Polyn
renameVars vars = map (second $ map $ first ren)
  where
    ren v = fromMaybe v $ lookup v dic
    dic = zip (Variable 'X' Nothing : [Variable 'X' (Just i) | i <- [1..]]) vars

showPolyn :: Polyn -> String
showPolyn f =
  case encodePolynomial f of
    Monomorphic f' ->
        case singInstance (Poly.sDegree f') of
          SingInstance -> Poly.showPolynomialWithVars dic f'
  where
    dic = zip [1..] $ map show $ buildVarsList f
