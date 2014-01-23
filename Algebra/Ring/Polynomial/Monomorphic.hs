{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs           #-}
{-# LANGUAGE MultiParamTypeClasses, PolyKinds, RecordWildCards, TypeFamilies #-}
{-# LANGUAGE TypeOperators, ViewPatterns, OverlappingInstances               #-}
{-# OPTIONS_GHC -fno-warn-orphans                             #-}
module Algebra.Ring.Polynomial.Monomorphic where
import           Algebra.Ring.Noetherian
import           Algebra.Scalar
import qualified Algebra.Ring.Polynomial as Poly
import           Control.Arrow
import           Data.List
import qualified Data.Map                as M
import           Data.Maybe
import Data.Type.Natural hiding (one, zero, promote, max)
import           Data.Type.Monomorphic
import qualified Numeric.Algebra         as NA
import qualified Numeric.Ring.Class      as NA
import           Data.Ratio
import qualified Data.Vector.Sized as V
import Control.Lens

data Variable = Variable { varName  :: Char
                         , varIndex :: Maybe Int
                         } deriving (Eq, Ord)

instance (Eq r, NoetherianRing r, Num r) => Num (Polynomial r) where
  fromInteger n = Polynomial $ M.singleton M.empty $ fromInteger n
  (+) = (NA.+)
  (*) = (NA.*)
  negate = NA.negate
  abs = id
  signum (normalize -> f)
                  | f == NA.zero = NA.zero
                  | otherwise    = NA.one

instance Show Variable where
  showsPrec _ v = showChar (varName v) . maybe id ((showChar '_' .) . shows) (varIndex v)

type Monomial = M.Map Variable Integer

newtype Polynomial k = Polynomial { unPolynomial :: M.Map Monomial k }
    deriving (Eq, Ord)

instance (NA.Monoidal r, Eq r) => Wrapped (M.Map Monomial r) (M.Map Monomial r') (Polynomial r) (Polynomial r') where
  wrapped = iso (normalize . Polynomial) unPolynomial

normalize :: (Eq k, NA.Monoidal k) => Polynomial k -> Polynomial k
normalize (Polynomial dic) =
  Polynomial $ M.filterWithKey (\k v -> v /= NA.zero || M.null k) $ M.mapKeysWith (NA.+) normalizeMonom dic

normalizeMonom :: Monomial -> Monomial
normalizeMonom = M.filter (/= 0)

instance (Eq r, NoetherianRing r) => NoetherianRing (Polynomial r)
instance (Eq r, NoetherianRing r) => NA.Commutative (Polynomial r)
instance (Eq r, NoetherianRing r) => NA.Multiplicative (Polynomial r) where
  Polynomial (M.toList -> d1) *  Polynomial (M.toList -> d2) =
    let dic = [ (M.unionWith (+) a b, r NA.* r') | (a, r) <- d1, (b, r') <- d2 ]
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

instance (NoetherianRing r, Eq r) => NA.LeftModule (Scalar r) (Polynomial r) where
  Scalar r .* Polynomial dic = normalize $ Polynomial $ fmap (r NA.*) dic
instance (NoetherianRing r, Eq r) => NA.RightModule (Scalar r) (Polynomial r) where
  Polynomial dic *. Scalar r = normalize $ Polynomial $ fmap (r NA.*) dic

buildVarsList :: Polynomial r -> [Variable]
buildVarsList = nub . sort . concatMap M.keys . M.keys . unPolynomial

encodeMonomList :: [Variable] -> Monomial -> [Int]
encodeMonomList vars mono = map (maybe 0 fromInteger . flip M.lookup mono) vars

encodeMonomial :: [Variable] -> Monomial -> Monomorphic (V.Vector Int)
encodeMonomial vars mono = promote $ encodeMonomList vars mono

encodePolynomial :: (Monomorphicable (Poly.Polynomial r))
                 => Polynomial r -> Monomorphic (Poly.Polynomial r)
encodePolynomial = promote . toPolynomialSetting

toPolynomialSetting :: Polynomial r -> PolynomialSetting r
toPolynomialSetting p =
    PolySetting { polyn = p
                , dimension = promote $ length $ buildVarsList p
                }

data PolynomialSetting r = PolySetting { dimension :: Monomorphic (Sing :: Nat -> *)
                                       , polyn     :: Polynomial r
                                       }

instance (Integral a, Show a) => Show (Polynomial (Ratio a)) where
  show = showRatPolynomial

instance (Eq r, NoetherianRing r, Show r) => Show (Polynomial r) where
  show = showPolynomial

instance (Eq r, NoetherianRing r, Poly.IsMonomialOrder ord)
    => Monomorphicable (Poly.OrderedPolynomial r ord) where
  type MonomorphicRep (Poly.OrderedPolynomial r ord) = PolynomialSetting r
  promote PolySetting{..} =
    case dimension of
      Monomorphic dim ->
        case singInstance dim of
          SingInstance -> Monomorphic $ Poly.polynomial $ M.mapKeys (Poly.OrderedMonomial . Poly.fromList dim . encodeMonomList vars) $ unPolynomial polyn
    where
      vars = buildVarsList polyn
  demote (Monomorphic f) =
      PolySetting { polyn = Polynomial $ M.fromList $
                              map (toMonom . map toInteger . demote . Monomorphic . Poly.getMonomial . snd &&& fst) $
                              Poly.getTerms f
                  , dimension = Monomorphic $ Poly.sArity f
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
        SingInstance -> Monomorphic $ Comp $ toIdeal $ map (Poly.polynomial . M.mapKeys (Poly.OrderedMonomial . Poly.fromList dim . encodeMonomList vars) . unPolynomial) ps
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
  demote (Monomorphic (Comp (Ideal v))) = map (polyn . demote . Monomorphic) $ V.toList v

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
        SingInstance -> Monomorphic $ Comp $ map (Poly.polynomial . M.mapKeys (Poly.OrderedMonomial . Poly.fromList sdim . encodeMonomList vars) . unPolynomial) ps
  where
    vs0 = nub $ sort $ concatMap buildVarsList ps
    (_, rest) = partition (`elem` dic) vs0
    vars = dic ++ rest
    dim  = length vars

promoteListWithDim :: (NoetherianRing r, Eq r, Poly.IsMonomialOrder ord)
                   => Int -> [Polynomial r] -> Monomorphic ([] :.: Poly.OrderedPolynomial r ord)
promoteListWithDim dim ps =
  case promote dim of
    Monomorphic sdim ->
      case singInstance sdim of
        SingInstance -> Monomorphic $ Comp $ map (Poly.polynomial . M.mapKeys (Poly.OrderedMonomial . Poly.fromList sdim . encodeMonomList vars) . unPolynomial) ps
  where
    vars = nub $ sort $ concatMap buildVarsList ps

renameVars :: [Variable] -> Polynomial r -> Polynomial r
renameVars vars = Polynomial . M.mapKeys (M.mapKeys ren) . unPolynomial
  where
    ren v = fromMaybe v $ lookup v dic
    dic = zip (Variable 'X' Nothing : [Variable 'X' (Just i) | i <- [1..]]) vars

showPolynomial :: (Show r, Eq r, NoetherianRing r) => Polynomial r -> String
showPolynomial f =
  case encodePolynomial f of
    Monomorphic f' ->
        case singInstance (Poly.sArity f') of
          SingInstance -> Poly.showPolynomialWithVars dic f'
  where
    dic = zip [1 :: Int ..] $ map show $ buildVarsList f

showRatPolynomial :: (Integral a, Show a) => Polynomial (Ratio a) -> String
showRatPolynomial f =
  case encodePolynomial f of
    Monomorphic f' ->
        case singInstance (Poly.sArity f') of
          SingInstance -> Poly.showPolynomialWith False dic Poly.showRational f'
  where
    dic = zip [1 :: Int ..] $ map show $ buildVarsList f

injectVar :: NA.Unital r => Variable -> Polynomial r
injectVar var = Polynomial $ M.singleton (M.singleton var 1) NA.one

injectCoeff :: r -> Polynomial r
injectCoeff c = Polynomial $ M.singleton M.empty c

subst :: (NA.Module r a, NA.Ring a, NA.Ring r) =>  M.Map Variable a -> Polynomial r -> a
subst assign poly = NA.sum $ map (uncurry (NA.*.) . first extractPower) $ M.toList $ unPolynomial poly
  where
    extractPower = NA.product . map (uncurry NA.pow) . map (flip (M.findWithDefault NA.zero) assign *** (fromInteger :: Integer -> NA.Natural)) . M.toList

diff :: (Eq r, NA.Ring r) => Variable -> Polynomial r -> Polynomial r
diff var = unwrapped %~ M.mapKeysWith (NA.+) (at var._Just %~ max 0 . pred)
                      . M.mapWithKey (\k v -> v NA.* NA.fromIntegral (M.findWithDefault NA.zero var k))
