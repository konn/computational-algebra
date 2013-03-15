{-# LANGUAGE FlexibleInstances, GADTs, PolyKinds, RecordWildCards #-}
{-# LANGUAGE TypeFamilies, TypeOperators, ViewPatterns            #-}
module Algebra.Algorithms.Groebner.Monomorphic where
import qualified Algebra.Algorithms.Groebner         as Gr
import           Algebra.Internal
import           Algebra.Ring.Noetherian
import qualified Algebra.Ring.Polynomial             as Poly
import           Algebra.Ring.Polynomial.Monomorphic
import           Data.List
import           Monomorphic

calcGroebnerBasis :: [Polyn] -> [Polyn]
calcGroebnerBasis (filter (any ((/= 0).fst)) -> []) = []
calcGroebnerBasis j =
  case uniformlyPromote j :: Monomorphic (Ideal :.: Poly.Polynomial Rational) of
    Monomorphic (Comp ideal) ->
      case ideal of
        Ideal vec ->
          case singInstance (Poly.sDegree (head $ toList vec)) of
            SingInstance -> map (renameVars vars . polyn . demote . Monomorphic) $ Gr.calcGroebnerBasis ideal
  where
    vars = nub $ sort $ concatMap buildVarsList j

isIdealMember :: Polyn -> [Polyn] -> Bool
isIdealMember f ideal =
  case promoteList (f:ideal) :: Monomorphic ([] :.: Poly.Polynomial Rational) of
    Monomorphic (Comp (f':ideal')) ->
      case singInstance (Poly.sDegree f') of
        SingInstance -> Gr.isIdealMember f' (toIdeal ideal')
    _ -> error "impossible happend!"
