{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE ConstraintKinds, DataKinds, ExplicitNamespaces              #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction            #-}
{-# LANGUAGE OverloadedStrings, ParallelListComp, PatternSynonyms        #-}
{-# LANGUAGE PolyKinds, ScopedTypeVariables, TypeFamilies, TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances                  #-}
-- | Algorithms for zero-dimensional ideals.
--
--   Since 0.4.0.0
module Algebra.Algorithms.ZeroDim
       ( -- * Root finding for zero-dimensional ideal
         solveM, solve', solveViaCompanion, solveLinear,
         -- * Radical computation
         radical, isRadical,
         -- * Converting monomial ordering to Lex using FGLM algorithm
         fglm, fglmMap,
         -- ** Internal helper function
         solveWith,  univPoly,
         reduction,
         matrixRep, subspMatrix,
         vectorRep
       ) where
import           Algebra.Algorithms.FGLM
import           Algebra.Algorithms.Groebner
import           Algebra.Instances                ()
import           Algebra.Internal                 hiding (OLt)
import qualified Algebra.Matrix                   as AM
import           Algebra.Prelude.Core
import           Algebra.Ring.Polynomial.Quotient

import           Control.Lens
import           Control.Monad.Loops   (whileM_)
import           Control.Monad.Random  hiding (next)
import           Control.Monad.Reader  (runReaderT)
import           Control.Monad.ST      (runST)
import           Data.Complex          (Complex (..), magnitude)
import           Data.Convertible      (Convertible, convert)
import qualified Data.Matrix           as M
import           Data.Maybe            (fromJust)
import           Data.Ord              (comparing)
import           Data.Reflection       (Reifies)
import qualified Data.Sized.Builtin    as SV
import           Data.STRef.Strict     (newSTRef)
import qualified Data.Vector           as V
import qualified Data.Vector.Mutable   as MV
import qualified Numeric.Algebra       as NA
import qualified Numeric.LinearAlgebra as LA
import qualified Prelude               as P
import           Proof.Propositional   (IsTrue (Witness))

-- | Finds complex approximate  roots of given zero-dimensional ideal,
--   using randomized altorithm.
--
--   See also @'solve''@ and @'solveViaCompanion'@.
solveM :: forall m r ord n.
          (Normed r, Ord r, MonadRandom m, Field r, CoeffRing r, KnownNat n,
           IsMonomialOrder n ord, Convertible r Double,
           (0 < n) ~ 'True)
       => Ideal (OrderedPolynomial r ord n)
       -> m [Sized n (Complex Double)]
solveM ideal = {-# SCC "solveM" #-}
  withKnownNat (sSucc (sing :: SNat n)) $
  reifyQuotient (radical ideal) $ \pxy ->
  case standardMonomials' pxy of
    Just bs -> step 10 (length bs)
    Nothing -> error "Given ideal is not zero-dimensional"
  where
    step bd len = {-# SCC "solveM/step" #-}do
      coeffs <- {-# SCC "solveM/coeff-gen" #-}
        replicateM (sNatToInt (sSucc (sing :: SNat n))) $ getRandomR (-bd, bd)
      let vars = one : SV.toList allVars
          f = sum $ zipWith (.*.) (map (NA.fromInteger :: Integer -> r) coeffs) vars
      case solveWith f ideal of
        Nothing -> step (bd*2) len
        Just sols -> return sols

-- | @solveWith f is@ finds complex approximate roots of the given zero-dimensional @n@-variate polynomial system @is@,
--   using the given relatively prime polynomial @f@.
solveWith :: forall r n ord. (DecidableZero r, Normed r, Ord r, Field r, CoeffRing r,
                              (0 < n) ~ 'True, IsMonomialOrder n ord,
                              KnownNat n, Convertible r Double)
          => OrderedPolynomial r ord n
          -> Ideal (OrderedPolynomial r ord n)
          -> Maybe [Sized n (Complex Double)]
solveWith f0 i0 = {-# SCC "solveWith" #-}
  withKnownNat (sSucc (sing :: SNat n)) $
  reifyQuotient (radical i0) $ \pxy ->
    let ideal = gBasis' pxy
        Just base = map (leadingMonomial . quotRepr) <$> standardMonomials' pxy
    in case {-# SCC "findOne" #-} elemIndex one base of
      Nothing -> Just []
      Just cind ->
        let f = modIdeal' pxy f0
            vars = sortBy (flip $ comparing snd) $
                   map (\on -> (on, leadingMonomial $ var on `asTypeOf` f0)) $
                   enumOrdinal $ sArity' f0
            inds = flip map vars $ second $ \b ->
              case findIndex (==b) base of
                Just ind -> Right ind
                Nothing  ->
                  let Just g = find ((==b) . leadingMonomial) ideal
                      r = leadingCoeff g
                      answer = mapCoeff toComplex $ injectCoeff (recip r) * (toPolynomial (leadingTerm g) - g)
                  in Left answer
            mf = AM.fromLists $ map (map toComplex) $ matrixRep f
            (_, evecs) = LA.eig $ LA.tr mf
            calc vec ={-# SCC "calc" #-}
              let c = vec LA.! cind
                  phi (idx, Right nth) acc = acc & ix idx .~ (vec LA.! nth) P./ c
                  phi (idx, Left g)    acc = acc & ix idx .~ substWith (*) acc g
              in if c == 0
                 then Nothing
                 else Just $ foldr ({-# SCC "rewrite-answer" #-} phi) (SV.replicate (sArity' f0) (error "indec!")) inds
        in sequence $ map calc $ LA.toColumns evecs

-- | @'solve'' err is@ finds numeric approximate root of the
--   given zero-dimensional polynomial system @is@,
--   with error <@err@.
--
--   See also @'solveViaCompanion'@ and @'solveM'@.
solve' :: forall r n ord.
          (Field r, CoeffRing r, KnownNat n, (0 < n) ~ 'True,
           IsMonomialOrder n ord, Convertible r Double)
       => Double
       -> Ideal (OrderedPolynomial r ord n)
       -> [Sized n (Complex Double)]
solve' err ideal =
  reifyQuotient ideal $ \ii ->
  if gBasis' ii == [one]
  then []
  else
    let vs = map (nub . LA.toList . LA.eigenvalues . AM.fromLists . map (map toComplex). matrixRep . modIdeal' ii) $
             SV.toList allVars
        mul p q = toComplex p * q
    in [ xs
       | xs0 <- sequence vs
       , let xs = SV.unsafeFromList' xs0
       , all ((< err) . magnitude . substWith mul xs) $ generators ideal
       ]
  where
    _ = Witness :: IsTrue (0 < n) -- Just to suppress "redundant constraint" warning

subspMatrix :: (Ord r, Field r, CoeffRing r, KnownNat n, IsMonomialOrder n ord)
            => Ordinal n -> Ideal (OrderedPolynomial r ord n) -> M.Matrix r
subspMatrix on ideal =
  let poly = univPoly on ideal
      v    = var on `asTypeOf` head (generators ideal)
      dim  = totalDegree' poly
      cfs  = [negate $ coeff (leadingMonomial $ pow v (j :: Natural)) poly | j <- [fromIntegral (dim - 1)]]
  in (M.fromLists [replicate (dim - 1) zero]
          M.<->
      fmap unwrapAlgebra (M.identity (dim - 1))) M.<|> M.colVector (V.fromList cfs)

-- | @'solveViaCompanion' err is@ finds numeric approximate root of the
--   given zero-dimensional polynomial system @is@,
--   with error <@err@.
--
--   See also @'solve''@ and @'solveM'@.
solveViaCompanion :: forall r ord n.
                     (Ord r, Field r, CoeffRing r, KnownNat n, IsMonomialOrder n ord, Convertible r Double)
                  => Double
                  -> Ideal (OrderedPolynomial r ord n)
                  -> [Sized n (Complex Double)]
solveViaCompanion err ideal =
  if calcGroebnerBasis ideal == [one]
  then []
  else
  let vs = map (nub . LA.toList . LA.eigenvalues . LA.fromLists . matToLists . fmap toComplex . flip subspMatrix ideal) $
           enumOrdinal (sing :: SNat n)
      mul p q = toComplex p * q
  in [ xs
     | xs0 <- sequence vs
     , let xs = SV.unsafeFromList' xs0
     , all ((< err) . magnitude . substWith mul xs) $ generators ideal
     ]

matToLists :: M.Matrix a -> [[a]]
matToLists mat = [ V.toList $ M.getRow i mat | i <- [1.. M.nrows mat] ]

matrixRep :: (DecidableZero t, Eq t, Field t, KnownNat n, IsMonomialOrder n order,
              Reifies ideal (QIdeal (OrderedPolynomial t order n)))
           => Quotient (OrderedPolynomial t order n) ideal -> [[t]]
matrixRep f = {-# SCC "matrixRep" #-}
  case standardMonomials of
    Just []    -> []
    Just bases ->
      let anss = map (quotRepr . (f *)) bases
      in transpose $ map (\a -> map (flip coeff a . leadingMonomial . quotRepr) bases) anss
    Nothing -> error "Not finite dimension"

toComplex :: Convertible a Double => a -> Complex Double
toComplex a = convert a :+ 0

-- | Calculates n-th reduction of f: @f `div` < f, ∂_{x_n} f >@.
reduction :: (CoeffRing r, KnownNat n, IsMonomialOrder n ord, Field r)
             => Ordinal n -> OrderedPolynomial r ord n -> OrderedPolynomial r ord n
reduction on f = {-# SCC "reduction" #-}
  let df = {-# SCC "differentiate" #-} diff on f
  in snd $ head $ f `divPolynomial` calcGroebnerBasis (toIdeal [f, df])

-- | Calculate the monic generator of k[X_0, ..., X_n] `intersect` k[X_i].
univPoly :: forall r ord n. (Ord r, Field r, CoeffRing r, KnownNat n, IsMonomialOrder n ord)
         => Ordinal n
         -> Ideal (OrderedPolynomial r ord n)
         -> OrderedPolynomial r ord n
univPoly nth ideal = {-# SCC "univPoly" #-}
  reifyQuotient ideal $ \pxy ->
  if gBasis' pxy == [one]
  then one
  else let x = var nth
           p0 : pows = [fmap WrapAlgebra $ vectorRep $ modIdeal' pxy (pow x i)
                       | i <- [0:: Natural ..]
                       | _ <- zero : fromJust (standardMonomials' pxy) ]
           step m ~(p : ps) = {-# SCC "univPoly/step" #-}
             case solveLinear m p of
               Nothing  -> {-# SCC "recur" #-} step ({-# SCC "consCol" #-}m M.<|> M.colVector p) ps
               Just ans ->
                 let cur = fromIntegral $ V.length ans :: Natural
                 in {-# SCC "buildRelation" #-}
                    pow x cur - sum (zipWith (.*.) (fmap unwrapAlgebra $ V.toList ans)
                                     [pow x i | i <- [0 :: Natural .. cur P.- 1]])
       in step (M.colVector p0) pows

-- | Solves linear system. If the given matrix is degenerate, this returns @Nothing@.
solveLinear :: (Ord r, P.Fractional r)
            => M.Matrix r
            -> V.Vector r
            -> Maybe (V.Vector r)
solveLinear mat vec = {-# SCC "solveLinear" #-}
  if ({-# SCC "uRank" #-} uRank u) < uRank u' || M.diagProd u == 0 || uRank u < M.ncols mat
  then Nothing
  else let ans = M.getCol 1 $ p P.* M.colVector vec
           lsol = {-# SCC "solveL" #-} solveL ans
           cfs = M.getCol 1 $ q P.* M.colVector ({-# SCC "solveU" #-} solveU lsol)
       in Just cfs
  where
    Just (u, l, p, q, _, _) = M.luDecomp' mat
    Just (u', _,_, _, _, _) = M.luDecomp' (mat M.<|> M.colVector vec)
    uRank = V.foldr (\a acc -> if a /= 0 then acc + 1 else acc) (0 :: Int) . M.getDiag
    solveL v = V.create $ do
      let stop = min (M.ncols l) (M.nrows l)
      mv <- MV.replicate (M.ncols l) 0
      forM_ [0..stop - 1] $ \i -> do
        MV.write mv i $ v V.! i
        forM_ [0,1..min (i-1) (M.ncols l - 1)] $ \j -> do
          a <- MV.read mv i
          b <- MV.read mv j
          MV.write mv i $ a P.- (l M.! (i + 1, j + 1)) P.* b
      return mv
    solveU v = V.create $ do
      let stop = min (M.ncols u) (M.nrows u)
      mv <- MV.replicate (M.ncols u) 0
      forM_ [stop - 1, stop - 2 .. 0] $ \ i -> do
        MV.write mv i $ v V.! i
        forM_ [i+1,i+2..M.ncols u-1] $ \j -> do
          a <- MV.read mv i
          b <- MV.read mv j
          MV.write mv i $ a P.- (u M.! (i+1, j+1)) P.* b
        a0 <- MV.read mv i
        MV.write mv i $ a0 P./ (u M.! (i+1, i+1))
      return mv

-- | Calculate the radical of the given zero-dimensional ideal.
radical :: forall r ord n . (Ord r, CoeffRing r,
                             KnownNat n, Field r, IsMonomialOrder  n ord)
        => Ideal (OrderedPolynomial r ord n) -> Ideal (OrderedPolynomial r ord n)
radical ideal = {-# SCC "radical" #-}
  let gens  = {-# SCC "calcGens" #-} map (\on -> reduction on $ univPoly on ideal) $ enumOrdinal (sing :: SNat n)
  in toIdeal $ calcGroebnerBasis $ toIdeal $ generators ideal ++ gens

-- | Test if the given zero-dimensional ideal is radical or not.
isRadical :: forall r ord n. (Ord r, CoeffRing r, KnownNat n,
                              (0 < n) ~ 'True,
                              Field r, IsMonomialOrder n ord)
          => Ideal (OrderedPolynomial r ord n) -> Bool
isRadical ideal =
  let gens  = map (\on -> reduction on $ univPoly on ideal) $
              enumOrdinal (sing :: SNat n)
  in all (`isIdealMember` ideal) gens
  where
    _ = Witness :: IsTrue (0 < n) -- Just to suppress "redundant constraint" warning

-- solve'' :: forall r ord n.
--            (Show r, Sparse.Eq0 r, Normed r, Ord r, Field r, CoeffRing r, KnownNat n,
--             IsMonomialOrder ord, Convertible r Double, (0 < n) ~ 'True)
--        => Double
--        -> Ideal (OrderedPolynomial r ord n)
--        -> [Sized n  (Complex Double)]
-- solve'' err ideal =
--   reifyQuotient (radical ideal) $ \ii ->
--   let gbs = gBasis' ii
--       lexBase = fst $ fglm $ toIdeal gbs
--       upoly = last lexBase
--       restVars = init $ SV.toList allVars
--       calcEigs = nub . LA.toList . LA.eigenvalues . AM.fromLists
--       lastEigs = calcEigs $ matToLists $ fmap toComplex $ fmapUnwrap
--                  (AM.companion maxBound $ mapCoeff WrapField upoly)
--   in if gbs == [one]
--      then []
--      else if length (lastEigs) == length (fromJust $ standardMonomials' ii)
--           then solveSpan (init lexBase) lastEigs
--           else chooseAnswer $
--                lastEigs : map (calcEigs . map (map toComplex) . matrixRep . modIdeal' ii)
--                               restVars
--   where
--     mul p q = toComplex p * q
--     solveSpan rest lastEigs =
--       let answers = map (\f -> toPolynomial (leadingTerm f) - f) rest
--           substEig eig = substWith (\d b -> toComplex d * b) $ SV.unsafeFromList' $ map (const zero) rest ++ [eig]
--       in [ SV.unsafeFromList' $ map (substEig eig) answers ++ [eig]
--          | eig <- lastEigs
--          ]
--     chooseAnswer vs =
--           [ xs
--             | xs0 <- sequence vs
--             , let xs = SV.unsafeFromList' xs0
--             , all ((<err) . magnitude . substWith mul xs) $ generators ideal
--             ]

-- * FGLM

-- | Calculate the Groebner basis w.r.t. lex ordering of the zero-dimensional ideal using FGLM algorithm.
--   If the given ideal is not zero-dimensional this function may diverge.
fglm :: (Ord r, KnownNat n, Field r,
         IsMonomialOrder n ord, (0 < n) ~ 'True)
     => Ideal (OrderedPolynomial r ord n)
     -> ([OrderedPolynomial r Lex n], [OrderedPolynomial r Lex n])
fglm ideal = reifyQuotient ideal $ \pxy ->
  fglmMap (vectorRep . modIdeal' pxy)

-- | Compute the kernel and image of the given linear map using generalized FGLM algorithm.
fglmMap :: forall k ord n. (Ord k, Field k, (0 < n) ~ 'True,
                            IsMonomialOrder n ord, CoeffRing k, KnownNat n)
        => (OrderedPolynomial k ord n -> V.Vector k)
        -- ^ Linear map from polynomial ring.
        -> ( [OrderedPolynomial k Lex n]
           , [OrderedPolynomial k Lex n]
           ) -- ^ The tuple of:
             --
             --     * lex-Groebner basis of the kernel of the given linear map.
             --
             --     * The vector basis of the image of the linear map.
fglmMap l = runST $ do
  env <- FGLMEnv l <$> newSTRef [] <*> newSTRef [] <*> newSTRef Nothing <*> newSTRef one
  flip runReaderT env $ do
    mainLoop
    whileM_ toContinue $ nextMonomial >> mainLoop
    (,) <$> look gLex <*> (map (changeOrder Lex) <$> look bLex)

mainLoop :: (DecidableZero r, Ord r,  KnownNat n, Field r, IsMonomialOrder n o)
         => Machine s r o n ()
mainLoop = do
  m <- look monomial
  let f = toPolynomial (one, changeMonomialOrderProxy Proxy m)
  lx <- image f
  bs <- mapM image =<< look bLex
  let mat  = foldr (M.<|>) (M.fromList 0 0 []) $ map (M.colVector . fmap WrapAlgebra) bs
      cond | null bs   = if V.all (== zero) lx
                         then Just $ V.replicate (length bs) 0
                         else Nothing
           | otherwise = solveLinear mat (fmap WrapAlgebra lx)
  case cond of
    Nothing -> do
      proced .== Nothing
      bLex @== (f : )
    Just cs -> do
      bps <- look bLex
      let g = changeOrder Lex $ f - sum (zipWith (.*.) (V.toList $ fmap unwrapAlgebra cs) bps)
      proced .== Just (changeOrder Lex f)
      gLex @== (g :)

toContinue :: forall s r o n.
              ((0 < n) ~ 'True, Ord r,
               KnownNat n, Field r)
           => Machine s r o n Bool
toContinue = do
  mans <- look proced
  case mans of
    Nothing -> return True
    Just g -> do
      let xLast = P.maximum allVars `asTypeOf` g
      return $ not $ leadingMonomial g `isPowerOf` leadingMonomial xLast
  where
    _ = Witness :: IsTrue (0 < n) -- Just to suppress "redundant constraint" warning

nextMonomial :: forall s r ord n.
                (CoeffRing r, KnownNat n) => Machine s r ord n ()
nextMonomial = do
  m <- look monomial
  gs <- map leadingMonomial <$> look gLex
  let next = fst $ maximumBy (comparing snd)
             [ (OrderedMonomial monom, fromEnum od)
             | od <- enumOrdinal (sing :: SNat n)
             , let monom = beta (getMonomial m) od
             , all (not . (`divs` OrderedMonomial monom)) gs
             ]
  monomial .== next

beta :: Monomial n -> Ordinal n -> Monomial n
beta xs o@(OLt k) =
  let n = sizedLength xs
  in withRefl (lneqSuccLeq k n) $
     withRefl (plusComm (n %- sSucc k) (sSucc k)) $
     withRefl (minusPlus n (sSucc k) Witness) $
     (SV.take (sSucc k) $ xs & ix o +~ 1) SV.++ SV.replicate (n %- sSucc k) 0
beta _ _ = error "beta: Bug in ghc!"
