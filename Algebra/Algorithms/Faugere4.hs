{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts                   #-}
{-# LANGUAGE FlexibleInstances, GADTs, MultiParamTypeClasses                #-}
{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction, ParallelListComp #-}
{-# LANGUAGE QuasiQuotes, RankNTypes, ScopedTypeVariables, TemplateHaskell  #-}
{-# LANGUAGE TupleSections, TypeFamilies, TypeOperators, ViewPatterns       #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Algebra.Algorithms.Faugere4 (
  -- * F_4 algorithms with various backends
  faugere4LM, faugere4, faugere4G, faugere4Modular,
  -- * Selection strategies
  optimalStrategy, sugarStrategy,
  -- * F_4 main algorithm
  faugere4Gen,
  -- * Examples
  cyclic)  where
import qualified Algebra.LinkedMatrix    as LM
import           Algebra.Matrix          hiding (trace)
import qualified Algebra.Repa            as Repa
import           Algebra.Ring.Ideal
import           Algebra.Ring.Polynomial
import           Algebra.Wrapped
import           Control.Arrow
import           Control.Monad.Identity
import           Control.Parallel
import qualified Data.Array.Repa         as Repa
import qualified Data.Array.Repa.Eval    as Repa
import           Data.Function
import qualified Data.HashMap.Strict     as HM
import qualified Data.HashSet            as S
import           Data.List
import           Data.Maybe
import           Data.Reflection         (Given (..), give)
import           Data.Type.Natural       hiding (one, zero)
import qualified Data.Vector             as V
import           Data.Vector.Sized       (Vector ((:-), Nil))
import qualified Data.Vector.Sized       as SV
import           Numeric.Algebra         hiding (sum, (<), (>), (\\))
import qualified Numeric.Algebra         as NA
import           Numeric.Decidable.Zero  (isZero)
import           Numeric.Field.Fraction  (Fraction)
import           Prelude                 (Num ())

import           Data.Proxy  (Proxy)
import qualified Debug.Trace as DT
import           Prelude     hiding (Num (..), recip, subtract, (/), (^))
import qualified Prelude     as P

-- * F_4 algorithm with various backends

-- | F_4 with general matrix.
faugere4G :: forall r ord mat n.
       (Normed r, Field r, IsMonomialOrder ord, IsPolynomial r n,
        Matrix mat, Elem mat r)
    => Proxy mat -> Strategy r ord n -> Ideal (OrderedPolynomial r ord n)
    -> Ideal (OrderedPolynomial r ord n)
faugere4G _ =
  faugere4Gen fromPs (fst . gaussReduction) toPs
  where
    toPs ts mat = map (NA.sum . zipWith (flip $ curry toPolynomial) ts . V.toList) $ toRows (mat :: mat r)
    fromPs fs =
      let ts  = nub $ sortBy (flip compare) $ concatMap monomials fs
      in (fromLists $ map (\f -> map (\t -> coeff t f) ts) fs, ts)

-- | F_4 using repa
faugere4 :: (Normed r, Field r, Fractional r, IsMonomialOrder ord, IsPolynomial r n,
             Repa.Elt r, Repa.Target (Repa.DefVec r) r, Repa.Source (Repa.DefVec r) r)
         => Strategy r ord n -> Ideal (OrderedPolynomial r ord n) -> Ideal (OrderedPolynomial r ord n)
faugere4 = faugere4Gen fromPs (fst . runIdentity . Repa.gaussReductionP) toPs
  where
    fromPs fs =
      let ts  = nub $ sortBy (flip compare) $ concatMap monomials fs
      in (Repa.fromLists $ map (\f -> map (\t -> coeff t f) ts) fs, ts)
    toPs ts mat =
      map (NA.sum . zipWith (flip $ curry toPolynomial) ts . V.toList) $ Repa.toRows mat

-- | F_4 with linked list based matrix with modified matrix construction
faugere4LM :: (Eq r, DecidableZero r, Field r, SingI n, IsMonomialOrder ord)
           => Strategy r ord n -> Ideal (OrderedPolynomial r ord n) -> Ideal (OrderedPolynomial r ord n)
faugere4LM =
  faugere4Gen fromPs (fst . LM.structuredGauss) toPs
  where
    toPs dic mat =
      V.toList $ LM.multWithVector (cmap injectCoeff mat) dic
    fromPs fs =
      let ts = nub $ sortBy (flip compare) $ concatMap monomials fs
          d0 = HM.fromList $ zip ts [0..]
      in (LM.fromList $ concat $ zipWith (\i f -> [ ((i, d0  HM.! t), c) | (c, t) <- getTerms f]) [0..] fs,
          V.fromList $ map (toPolynomial . (one,)) ts)

faugere4Modular :: (SingI n, IsMonomialOrder ord)
                => Strategy (Fraction Integer) ord n
                -> Ideal (OrderedPolynomial (Fraction Integer) ord n)
                -> Ideal (OrderedPolynomial (Fraction Integer) ord n)
faugere4Modular =
  faugere4Gen fromPs (fst . LM.triangulateModular) toPs
  where
    toPs dic mat =
      V.toList $ LM.multWithVector (cmap injectCoeff mat) dic
    fromPs fs =
      let ts = nub $ sortBy (flip compare) $ concatMap monomials fs
          d0 = HM.fromList $ zip ts [0..]
      in (LM.fromList $ concat $ zipWith (\i f -> [ ((i, d0  HM.! t), c) | (c, t) <- getTerms f]) [0..] fs,
          V.fromList $ map (toPolynomial . (one,)) ts)


-- ** Strategies
optimalStrategy :: Strategy r ord n
optimalStrategy ps =
  let d = minimum $ map degPair ps
  in filter ((==d) . degPair) ps

sugarStrategy :: (DecidableZero r, SingI n, IsOrder ord, Ring r) => Strategy r ord n
sugarStrategy ps =
  let d = minimum $ map calcSug ps
  in filter ((==d) . calcSug) ps

-- * F_4 Main Algorithm

-- | Generate F_4 algorithm with new backend
faugere4Gen :: (IsMonomialOrder ord, IsPolynomial r n)
            => ([OrderedPolynomial r ord n] -> (mat r, dic))
               -- ^ Convert list of polynomials to matrix and intermediate data.
            -> (mat r -> mat r)
               -- ^ Gaussian elimination
            -> (dic -> mat r -> [OrderedPolynomial r ord n])
               -- ^ Retrieve polynomials data
            -> Strategy r ord n -> Ideal (OrderedPolynomial r ord n)
            -> Ideal (OrderedPolynomial r ord n)
faugere4Gen fromPs gauss toPs sel (generators -> fs) = {-# SCC "F_4" #-}
  let (gs0, ps0) = foldl' (uncurry update) ([], []) fs
  in go gs0 ps0 []
  where
    go gs ps fds
      | null ps   = toIdeal gs
      | otherwise =
        let pd   = sel ps
            ps'  = ps \\ pd
            ls   = map leftP pd ++ map rightP pd
            (fdp, fd) = give (MatrixRepr fromPs gauss toPs) $ redF4 ls gs fds
            (gs2, ps2) = foldl' (uncurry update) (gs, ps') fdp
        in go gs2 ps2 (fd:fds)

data Pair r ord n = Pair { lcmPair    :: OrderedMonomial ord n
                         , leftMonom  :: OrderedMonomial ord n
                         , leftPoly   :: OrderedPolynomial r ord n
                         , rightMonom :: OrderedMonomial ord n
                         , rightPoly  :: OrderedPolynomial r ord n
                         } deriving (Show, Eq, Ord)
type Strategy r ord n = [Pair r ord n] -> [Pair r ord n]

leftP, rightP :: Pair r ord n -> (OrderedMonomial ord n, OrderedPolynomial r ord n)
leftP  = leftMonom &&& leftPoly
rightP = rightMonom &&& rightPoly

degPair :: Pair r ord n -> Int
degPair = totalDegree . lcmPair

mkPair :: (IsPolynomial r n, IsMonomialOrder ord)
       => OrderedPolynomial r ord n -> OrderedPolynomial r ord n -> Pair r ord n
mkPair f g =
  let f0  = leadingMonomial f
      g0  = leadingMonomial g
      lij = lcmMonomial f0 g0
      ti  = lij / f0
      tj  = lij / g0
  in Pair lij ti f tj g

calcSug :: (DecidableZero r, Ring r, SingI n, IsOrder ord) => Pair r ord n -> Int
calcSug p =
  let f = leftPoly p
      g = rightPoly p
      deg' = maximum . map (totalDegree . snd) . getTerms
      tsgr h = deg' h - totalDegree (leadingMonomial h)
      sugar = P.max (tsgr f) (tsgr g) + totalDegree (lcmMonomial (leadingMonomial f) (leadingMonomial g))
  in sugar

notDivs :: OrderedMonomial ord n -> OrderedMonomial ord n -> Bool
notDivs = (not .) . divs

update :: (IsPolynomial r n, IsMonomialOrder ord)
       => [OrderedPolynomial r ord n] -> [Pair r ord n] -> OrderedPolynomial r ord n
       -> ([OrderedPolynomial r ord n], [Pair r ord n])
update gs bs h = {-# SCC "update" #-}
  let cs = map (mkPair h) gs
      dsStep ds0 [] = ds0
      dsStep ds0 (p:cs0) =
        let cond1 = isRelativelyPrime (leadingMonomial $ leftPoly p) (leadingMonomial $ rightPoly p)
            cond2 = all (\q -> lcmPair q `notDivs` lcmPair p) cs0
                 && all (\q -> lcmPair q `notDivs` lcmPair p) ds0
        in if cond1 || cond2 then p:ds0 else ds0
      ds = foldl' dsStep [] $ init $ tails cs
      es = [ p
           | p <- ds
           , not $ isRelativelyPrime (leadingMonomial $ leftPoly p) (leadingMonomial $ rightPoly p)
           ]
      bs' = [p | p <- bs
               , let l = lcmPair p
               , or [leadingMonomial h `notDivs` lcmPair p
                    ,lcmMonomial (leadingMonomial $ leftPoly p) (leadingMonomial h) == l
                    ,lcmMonomial (leadingMonomial h) (leadingMonomial $ rightPoly p) == l
                    ]
               ]
      gs' = [g | g <- gs, leadingMonomial h `notDivs` leadingMonomial g ]
  in (es `par` bs' `par` gs') `pseq` (h : gs', bs' ++ es)

cyclic :: (SingI n)
       => SNat n -> Ideal (Polynomial (Fraction Integer) n)
cyclic sn =
  let vars = genVars sn
      cycs = tails $ cycle vars
      arity = sNatToInt sn
  in toIdeal $ NA.product vars - one : [ NA.sum $ map (NA.product . take i) $ take arity cycs | i <- [arity - 1,arity-2..1]]

divisors :: (SingI n, IsOrder ord) => OrderedMonomial ord n -> [OrderedMonomial ord n]
divisors t = [om
             | m <- sequenceSV (SV.map (enumFromTo 0) $ getMonomial t)
             , let om = OrderedMonomial m
             , om /= one
             ]

sequenceSV :: SV.Vector [a] n -> [SV.Vector a n]
sequenceSV Nil = [Nil]
sequenceSV (xs :- xss) = concatMap (\x -> map (x :-) $ sequenceSV xss) xs

data MatrixRepr r ord n where
  MatrixRepr :: ([OrderedPolynomial r ord n] -> (mat r, dic))
             -> (mat r -> mat r)
             -> (dic -> mat r -> [OrderedPolynomial r ord n])
             -> MatrixRepr r ord n

withMatRepr :: Given (MatrixRepr r ord n)
            => (forall mat dic. ([OrderedPolynomial r ord n] -> (mat r, dic))
                -> (mat r -> mat r)
                -> (dic -> mat r -> [OrderedPolynomial r ord n])
                -> a)
            -> a
withMatRepr f = case given of
  MatrixRepr fromPs gauss toPs -> f fromPs gauss toPs

simplify :: (Given (MatrixRepr r ord n),
             IsMonomialOrder ord, IsPolynomial r n, DecidableZero r)
         => [[OrderedPolynomial r ord n]]
         -> OrderedMonomial ord n -> OrderedPolynomial r ord n
         -> (OrderedMonomial ord n, OrderedPolynomial r ord n)
simplify fss t f = go $ divisors t
  where
    go []       = (t, f)
    go (u : us) =
      case find (u >* f `elem`) fss of
        Nothing -> go us
        Just fs ->
          let fs' = rowEchelon fs
              Just p = find (\g -> leadingMonomial g == leadingMonomial (u >* f)) fs'
          in if u /= t
             then simplify fss (t/u) p
             else (one, p)

rowEchelon :: (Given (MatrixRepr r ord n), Eq r,
               IsMonomialOrder ord, IsPolynomial r n, DecidableZero r)
           => [OrderedPolynomial r ord n]
           -> [OrderedPolynomial r ord n]
rowEchelon fs = withMatRepr $ \fromPolys gauss toPolys ->
  {-# SCC "rowEchelon" #-}
  let (mf, ts) = {-# SCC "buildMatrix" #-} fromPolys fs
      mf' = toPolys ts $ {-# SCC "eche/red" #-} gauss mf
  in filter (not . isZero) $ nub mf'

symbolicPP :: (Given (MatrixRepr r ord n), IsMonomialOrder ord, IsPolynomial r n, DecidableZero r)
           => [(OrderedMonomial ord n, OrderedPolynomial r ord n)]
           -> [OrderedPolynomial r ord n]
           -> [[OrderedPolynomial r ord n]]
           -> [OrderedPolynomial r ord n]
symbolicPP ls gs fss = {-# SCC "symbolicPP" #-}
  let fs0 = map mul ls
  in go fs0 (S.fromList $ concatMap monomials fs0) (S.fromList $ map leadingMonomial fs0)
  where
    mul = uncurry (>*) . uncurry (simplify fss)
    go fs ts done
      | S.null (ts `S.difference` done) = fs
      | otherwise =
        let m = head $ S.toList $ ts `S.difference` done
            done' = S.insert m done
            ts'   = S.delete m ts
        in case find (\f -> leadingMonomial f `divs` m) gs of
          Just f -> let m' = m / leadingMonomial f
                        f' = mul (m', f)
                        ts'' = S.fromList (monomials f') `S.difference` done'
                    in go (f' : fs) (ts' `S.union` ts'') done'
          Nothing -> go fs ts' done'

redF4 :: (Given (MatrixRepr r ord n), IsMonomialOrder ord, IsPolynomial r n)
      => [(OrderedMonomial ord n, OrderedPolynomial r ord n)]
      -> [OrderedPolynomial r ord n]
      -> [[OrderedPolynomial r ord n]]
      -> ([OrderedPolynomial r ord n], [OrderedPolynomial r ord n])
redF4 ls gs fss = {-# SCC "reduction" #-}
  let fs  = symbolicPP ls gs fss
      fs' = rowEchelon fs
  in ([ f | f <- fs', not $ leadingMonomial f `elem` map leadingMonomial fs], fs)

ideal3 :: Ideal (Polynomial (Fraction Integer) Three)
ideal3 = toIdeal [x^^^2 + y^^^2 + z^^^2 - 1, x^^^2 + y^^^2 + z^^^2 - 2*x, 2*x -3*y - z]
  where
    (^^^) :: (Unital r, Multiplicative r) => r -> Natural -> r
    (^^^) = pow
    [x,y,z] = genVars sThree
