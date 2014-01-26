{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, NoImplicitPrelude                 #-}
{-# LANGUAGE NoMonomorphismRestriction, ParallelListComp, RankNTypes         #-}
{-# LANGUAGE ScopedTypeVariables, TemplateHaskell, TypeFamilies              #-}
{-# LANGUAGE TypeOperators, ViewPatterns                                     #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Algebra.Algorithms.Faugere where
import           Algebra.Algorithms.Groebner
import           Algebra.Matrix              hiding (trace)
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Algebra.Wrapped
import           Control.Lens
import           Control.Monad
import           Data.Function
import           Data.List
import qualified Data.Matrix                 as DM
import           Data.Maybe
import qualified Data.Set                    as S
import           Data.Type.Natural           hiding (one, zero)
import qualified Data.Vector                 as V
import           Data.Vector.Sized           (Vector ((:-), Nil))
import qualified Data.Vector.Sized           as SV
import           Debug.Trace
import           Numeric.Algebra             hiding (sum, (<), (>), (\\))
import qualified Numeric.Algebra             as NA
import           Prelude                     hiding (Num (..), recip, subtract,
                                              (/), (^))
import           Prelude                     (Num ())

type Pair r ord n = (OrderedMonomial ord n, OrderedMonomial ord n, OrderedPolynomial r ord n, OrderedMonomial ord n, OrderedPolynomial r ord n)
type Strategy r ord n = [Pair r ord n] -> [Pair r ord n]

faugere4 :: (Normed r, Field r, Fractional r, IsMonomialOrder ord, IsPolynomial r n)
         => Strategy r ord n -> Ideal (OrderedPolynomial r ord n)
         -> Ideal (OrderedPolynomial r ord n)
faugere4 sel (generators -> fs) = go fs (nub [mkPair f g | f <- fs, g <- fs, f /= g])
  where
    go gs ps
      | null ps   = toIdeal gs
      | otherwise =
        let pd   = sel ps
            ps'  = ps \\ pd
            ls   = nub $ map leftP pd ++ map rightP pd
            fs'' = redF4 ls gs
            ps'' = concatMap (\h -> [mkPair h g | g <- gs]) fs''
            ps2  = nub $ ps' ++ ps''
        in go (gs ++ fs'') ps2

leftP, rightP :: Pair r ord n -> (OrderedMonomial ord n, OrderedPolynomial r ord n)
leftP  (_,t,f,_,_) = (t,f)
rightP (_,_,_,t,f) = (t,f)

degPair :: Pair r ord n -> Int
degPair = totalDegree . view _1

mkPair :: (IsPolynomial r n, IsMonomialOrder ord)
       => OrderedPolynomial r ord n -> OrderedPolynomial r ord n -> Pair r ord n
mkPair f g =
  let f0  = leadingMonomial f
      g0  = leadingMonomial g
      lij = lcmMonomial f0 g0
      ti  = lij / f0
      tj  = lij / g0
  in (lij, ti, f, tj, g)

redF4 :: (IsPolynomial r n, IsMonomialOrder ord, Field r, Normed r, Fractional r)
      => [(OrderedMonomial ord n, OrderedPolynomial r ord n)]
      -> [OrderedPolynomial r ord n]
      -> [OrderedPolynomial r ord n]
redF4 ls gs =
  let fs  = symbolicPP ls gs
      fs' = rowEchelon fs
  in [ f | f <- fs', not $ leadingMonomial f `elem` map leadingMonomial fs]

polysToMatrix :: (IsMonomialOrder ord, IsPolynomial r n, Num r)
          => [OrderedPolynomial r ord n] -> (DM.Matrix r, [OrderedMonomial ord n])
polysToMatrix fs =
  let ts  = nub $ sortBy (flip compare) $ concatMap monomials fs
  in (fromLists $ map (\f -> map (\t -> coeff t f) ts) fs, ts)

matToPolysWith :: (IsMonomialOrder ord, IsPolynomial r n, Num r)
            => [OrderedMonomial ord n] -> DM.Matrix r -> [OrderedPolynomial r ord n]
matToPolysWith ts mat =
  map (NA.sum . zipWith (flip $ curry toPolynomial) ts . V.toList) $ toRows mat

rowEchelon :: forall r ord n. (IsPolynomial r n, IsMonomialOrder ord, Field r, Num r, Normed r, Fractional r)
           => [OrderedPolynomial r ord n]
           -> [OrderedPolynomial r ord n]
rowEchelon fs =
  let (mf, ts) = polysToMatrix fs
      mf' = matToPolysWith ts $ fst $ gaussReduction mf
  in nub mf' \\ [0]

symbolicPP :: forall r ord n. (IsPolynomial r n, IsMonomialOrder ord, Field r, Num r, Normed r, Fractional r)
           => [(OrderedMonomial ord n, OrderedPolynomial r ord n)]
           -> [OrderedPolynomial r ord n] -> [OrderedPolynomial r ord n]
symbolicPP ls gs =
  let fs0 = map (\(t, f) -> toPolynomial (one, t) * f) ls
  in go fs0 (S.fromList $ map leadingMonomial fs0)
  where
    go fs done
      | S.fromList (concatMap monomials fs) == done = fs
      | otherwise =
        let m = head $ S.toList $ S.fromList (concatMap monomials fs) S.\\ done
            done' = S.insert m done
        in case find (\f -> leadingMonomial f `divs` m) gs of
          Just f -> let m' = m / leadingMonomial f
                    in go (toPolynomial (one, m') * f : fs) done'
          Nothing -> go fs done'

optimalStrategy :: Strategy r ord n
optimalStrategy ps =
  let d = minimum $ map degPair ps
  in filter ((==d) . degPair) ps
