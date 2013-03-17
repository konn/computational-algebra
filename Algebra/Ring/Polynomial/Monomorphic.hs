{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs           #-}
{-# LANGUAGE MultiParamTypeClasses, PolyKinds, RecordWildCards, TypeFamilies #-}
{-# LANGUAGE TypeOperators, ViewPatterns                                     #-}
{-# OPTIONS_GHC -fno-warn-orphans                             #-}
module Algebra.Ring.Polynomial.Monomorphic where
import           Algebra.Internal
import           Algebra.Ring.Noetherian
import qualified Algebra.Ring.Polynomial as Poly
import           Control.Arrow
import           Data.List
import qualified Data.Map                as M
import           Data.Maybe
import           Monomorphic
import qualified Numeric.Algebra         as NA

data Variable = Variable { varName  :: Char
                         , varIndex :: Maybe Int
                         } deriving (Eq, Ord)

instance Show Variable where
  showsPrec _ v = showChar (varName v) . maybe id ((showChar '_' .) . shows) (varIndex v)

type Monomial = M.Map Variable Integer

newtype Polynomial k = Polynomial { unPolynomial :: M.Map Monomial k }
    deriving (Eq, Ord, Show)

normalize :: (Eq k, NA.Monoidal k) => Polynomial k -> Polynomial k
normalize (Polynomial dic) =
  Polynomial $ M.filterWithKey (\k v -> v /= NA.zero || M.null k) $ M.mapKeysWith (NA.+) normalizeMonom dic

normalizeMonom :: Monomial -> Monomial
normalizeMonom = M.filter (/= 0)

instance (Eq r, NoetherianRing r) => NoetherianRing (Polynomial r)
instance (Eq r, NoetherianRing r) => NA.Commutative (Polynomial r)
instance (Eq r, NoetherianRing r) => NA.Multiplicative (Polynomial r) where
  Polynomial (M.toList -> d1) *  Polynomial (M.toList -> d2) =
    let dic = [ (M.unionWith (NA.+) a b, r NA.* r') | (a, r) <- d1, (b, r') <- d2 ]
    in normalize $ Polynomial $ M.fromListWith (NA.+) dic

instance (Eq r, NoetherianRing r) => NA.Ring (Polynomial r)
instance (Eq r, NoetherianRing r) => NA.Group (Polynomial r) where
  negate (Polynomial dic) = Polynomial $ fmap NA.negate dic
instance (Eq r, NoetherianRing r) => NA.Rig (Polynomial r)
instance (Eq r, NoetherianRing r) => NA.Unital (Polynomial r) where
  one = Polynomial $ M.singleton M.empty NA.one
instance (Eq r, NoetherianRing r) => NA.Monoidal (Polynomial r) where
  zero = Polynomial $ M.singleton M.empty NA.zero
instance (Eq r, NoetherianRing r) => NA.LeftModule NA.Natural (Polynomial r) where
  n .* Polynomial dic = Polynomial $ fmap (n NA..*) dic  
instance (Eq r, NoetherianRing r) => NA.RightModule NA.Natural (Polynomial r) where
  (*.) = flip (NA..*)
instance (Eq r, NoetherianRing r) => NA.LeftModule Integer (Polynomial r) where
  n .* Polynomial dic = Polynomial $ fmap (n NA..*) dic  
instance (Eq r, NoetherianRing r) => NA.RightModule Integer (Polynomial r) where
  (*.) = flip (NA..*)
instance (Eq r, NoetherianRing r) => NA.Semiring (Polynomial r)
instance (Eq r, NoetherianRing r) => NA.Abelian (Polynomial r)
instance (Eq r, NoetherianRing r) => NA.Additive (Polynomial r) where
  (Polynomial f) + (Polynomial g) = normalize $ Polynomial $ M.unionWith (NA.+) f g

buildVarsList :: Polynomial r -> [Variable]
buildVarsList = nub . sort . concatMap M.keys . M.keys . unPolynomial

encodeMonomList :: [Variable] -> [(Variable, Integer)] -> [Int]
encodeMonomList vars mono = map (maybe 0 fromInteger . flip lookup mono) vars

encodeMonomial :: [Variable] -> [(Variable, Integer)] -> Monomorphic (Vector Int)
encodeMonomial vars mono = promote $ encodeMonomList vars mono

encodePolynomial :: (Monomorphicable (Poly.Polynomial r), MonomorphicRep (Poly.Polynomial r) ~ PolynomialSetting r)
                 => Polynomial r -> Monomorphic (Poly.Polynomial r)
encodePolynomial = promote . toPolynomialSetting

toPolynomialSetting :: Polynomial r -> PolynomialSetting r
toPolynomialSetting p =
    PolySetting { polyn = p
                , dimension = promote $ length $ buildVarsList p
                }

data PolynomialSetting r = PolySetting { dimension :: Monomorphic SNat
                                       , polyn     :: Polynomial r
                                       } deriving (Show)


instance (Eq r, NoetherianRing r, Poly.IsMonomialOrder ord)
    => Monomorphicable (Poly.OrderedPolynomial r ord) where
  type MonomorphicRep (Poly.OrderedPolynomial r ord) = PolynomialSetting r
  promote PolySetting{..} =
    case dimension of
      Monomorphic dim ->
        case singInstance dim of
          SingInstance -> Monomorphic $ Poly.polynomial $ M.mapKeys (Poly.OrderedMonomial . Poly.fromList dim . encodeMonomList vars . M.toAscList) $ unPolynomial polyn
    where
      vars = buildVarsList polyn
  demote (Monomorphic f) =
      PolySetting { polyn = Polynomial $ M.fromList $
                              map (toMonom . map toInteger . demote . Monomorphic . snd &&& fst) $ Poly.getTerms f
                  , dimension = Monomorphic $ Poly.sDegree f
                  }
    where
      toMonom = M.fromList . zip (Variable 'X' Nothing : [Variable 'X' (Just i) | i <- [1..]])

uniformlyPromoteWithDim :: (Eq r, NoetherianRing r)
                        => Poly.IsMonomialOrder ord
                 => Int -> [Polynomial r] -> Monomorphic (Ideal :.: Poly.OrderedPolynomial r ord)
uniformlyPromoteWithDim d ps  =
  case promote d of
    Monomorphic dim ->
      case singInstance dim of
        SingInstance -> Monomorphic $ Comp $ toIdeal $ map (Poly.polynomial . M.mapKeys (Poly.OrderedMonomial . Poly.fromList dim . encodeMonomList vars . M.toAscList) . unPolynomial) ps
  where
    vars = nub $ sort $ concatMap buildVarsList ps

uniformlyPromote :: (Eq r, NoetherianRing r, Poly.IsMonomialOrder ord)
                 => [Polynomial r] -> Monomorphic (Ideal :.: Poly.OrderedPolynomial r ord)
uniformlyPromote ps  = uniformlyPromoteWithDim (length vars) ps
  where
    vars = nub $ sort $ concatMap buildVarsList ps

instance (NoetherianRing r, Eq r, Poly.IsMonomialOrder ord)
    => Monomorphicable (Ideal :.: Poly.OrderedPolynomial r ord) where
  type MonomorphicRep (Ideal :.: Poly.OrderedPolynomial r ord) = [Polynomial r]
  promote = uniformlyPromote
  demote (Monomorphic (Comp (Ideal v))) = map (polyn . demote . Monomorphic) $ toList v

promoteList :: (Eq r, NoetherianRing r, Poly.IsMonomialOrder ord)
            => [Polynomial r] -> Monomorphic ([] :.: Poly.OrderedPolynomial r ord)
promoteList ps = promoteListWithDim (length vars) ps
  where
    vars = nub $ sort $ concatMap buildVarsList ps

promoteListWithVarOrder :: (Eq r, NoetherianRing r, Poly.IsMonomialOrder ord)
                        => [Variable] -> [Polynomial r] -> Monomorphic ([] :.: Poly.OrderedPolynomial r ord)
promoteListWithVarOrder dic ps =
  case promote dim of
    Monomorphic sdim ->
      case singInstance sdim of
        SingInstance -> Monomorphic $ Comp $ map (Poly.polynomial . M.mapKeys (Poly.OrderedMonomial . Poly.fromList sdim . encodeMonomList vars . M.toAscList) . unPolynomial) ps
  where
    dim  = length vars
    vs0 = nub $ sort $ concatMap buildVarsList ps
    (incs, rest) = partition (`elem` dic) vs0
    vars = incs ++ rest

promoteListWithDim :: (NoetherianRing r, Eq r, Poly.IsMonomialOrder ord)
                   => Int -> [Polynomial r] -> Monomorphic ([] :.: Poly.OrderedPolynomial r ord)
promoteListWithDim dim ps =
  case promote dim of
    Monomorphic sdim ->
      case singInstance sdim of
        SingInstance -> Monomorphic $ Comp $ map (Poly.polynomial . M.mapKeys (Poly.OrderedMonomial . Poly.fromList sdim . encodeMonomList vars . M.toAscList) . unPolynomial) ps
  where
    vars = nub $ sort $ concatMap buildVarsList ps

{-
data Equal a b where
  Equal :: Equal a a

(%==) :: (a ~ b) => a -> b -> Equal a b
_ %== _ = Equal

thEliminationIdeal' :: Int -> [Polynomial] -> [Polynomial]
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

renameVars :: [Variable] -> Polynomial r -> Polynomial r
renameVars vars = Polynomial . M.mapKeys (M.mapKeys ren) . unPolynomial
  where
    ren v = fromMaybe v $ lookup v dic
    dic = zip (Variable 'X' Nothing : [Variable 'X' (Just i) | i <- [1..]]) vars

showPolynomial :: (Show r, Eq r, NoetherianRing r) => Polynomial r -> String
showPolynomial f =
  case encodePolynomial f of
    Monomorphic f' ->
        case singInstance (Poly.sDegree f') of
          SingInstance -> Poly.showPolynomialWithVars dic f'
  where
    dic = zip [1..] $ map show $ buildVarsList f

injectVar :: NA.Unital r => Variable -> Polynomial r
injectVar var = Polynomial $ M.singleton (M.singleton var 1) NA.one

