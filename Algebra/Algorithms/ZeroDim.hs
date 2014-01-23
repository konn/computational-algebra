{-# LANGUAGE ConstraintKinds, DataKinds, DefaultSignatures, FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving            #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction                #-}
{-# LANGUAGE OverlappingInstances, OverloadedStrings, ParallelListComp       #-}
{-# LANGUAGE PolyKinds, ScopedTypeVariables, StandaloneDeriving              #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, TypeSynonymInstances             #-}
{-# LANGUAGE UndecidableInstances                                            #-}
{-# OPTIONS_GHC -fwarn-name-shadowing #-}
-- | Algorithms for zero-dimensional ideals.
module Algebra.Algorithms.ZeroDim (univPoly, radical, isRadical, solveWith,
                                   WrappedField(..), reduction, solveViaCompanion,
                                   solveM, solve', solve'', matrixRep, subspMatrix,
                                   vectorRep, solveLinear, fglm, fglmMap) where
import           Algebra.Algorithms.FGLM
import           Algebra.Algorithms.Groebner
import           Algebra.Instances                ()
import qualified Algebra.Matrix                   as AM
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Algebra.Ring.Polynomial.Quotient
import           Algebra.Scalar
import           Algebra.Wrapped
import           Control.Applicative
import           Control.Arrow
import           Control.Lens
import           Control.Monad
import           Control.Monad.Loops
import           Control.Monad.Random             hiding (next)
import           Control.Monad.Reader
import           Control.Monad.ST
import           Data.Complex
import           Data.Convertible
import           Data.List                        hiding (sum)
import qualified Data.Matrix                      as M
import           Data.Maybe
import           Data.Ord
import           Data.Proxy
import           Data.Reflection
import           Data.Singletons
import           Data.STRef
import           Data.Type.Natural                (Nat (..), SNat,
                                                   Sing (SS, SZ), sNatToInt)
import           Data.Type.Ordinal
import qualified Data.Vector                      as V
import qualified Data.Vector.Mutable              as MV
import           Data.Vector.Sized                (Vector ((:-), Nil))
import qualified Data.Vector.Sized                as SV
import           Debug.Trace
import           Numeric.Algebra                  hiding ((/), (<))
import qualified Numeric.Algebra                  as NA
import           Numeric.LinearAlgebra            ((@>))
import qualified Numeric.LinearAlgebra            as LA
import           Prelude                          hiding (lex, negate, recip,
                                                   sum, (*), (+), (-), (^),
                                                   (^^))
import qualified Prelude                          as P
import qualified Sparse.Matrix                    as Sparse

tr :: Show b => b -> b
tr = join traceShow

solveM :: forall m r ord n.
          (Normed r, Ord r, MonadRandom m, Field r, IsPolynomial r n, IsMonomialOrder ord,
           Convertible r Double)
       => Ideal (OrderedPolynomial r ord (S n))
       -> m [SV.Vector (Complex Double) (S n)]
solveM ideal = {-# SCC "solveM" #-} reifyQuotient (radical ideal) $ \pxy ->
  case standardMonomials' pxy of
    Just bs -> step 10 (length bs)
    Nothing -> error "Given ideal is not zero-dimensional"
  where
    step bd len = {-# SCC "solveM/step" #-}do
      coeffs <- {-# SCC "solveM/coeff-gen" #-}
        replicateM (sNatToInt (sing :: SNat ((S (S n))))) $ getRandomR (-bd, bd)
      let vars = one : SV.toList allVars
          f = sum $ zipWith (.*.) (map (NA.fromInteger :: Integer -> r) coeffs) vars
      case solveWith f ideal of
        Nothing -> step (bd*2) len
        Just sols -> return sols

solveWith :: (Normed r, Ord r, Field r, IsPolynomial r n, IsMonomialOrder ord, Convertible r Double)
          => OrderedPolynomial r ord (S n)
          -> Ideal (OrderedPolynomial r ord (S n))
          -> Maybe [SV.Vector (Complex Double) (S n)]
solveWith f0 i0 = {-# SCC "solveWith" #-}
  reifyQuotient (radical i0) $ \pxy ->
    let ideal = gBasis' pxy
        Just base = map (leadingMonomial . quotRepr) <$> standardMonomials' pxy
    in case {-# SCC "findOne" #-} elemIndex one base of
      Nothing -> Just []
      Just cind ->
        let f = modIdeal' pxy f0
            vars = sortBy (flip $ comparing snd) $
                   map (\on -> (on, leadingMonomial $ var on `asTypeOf` f0)) $
                   enumOrdinal $ sArity f0
            inds = flip map vars $ second $ \b ->
              case findIndex (==b) base of
                Just ind -> Right ind
                Nothing  ->
                  let Just g = find ((==b) . leadingMonomial) ideal
                      r = leadingCoeff g
                      answer = mapCoeff toComplex $ injectCoeff (recip r) * (toPolynomial (leadingTerm g) - g)
                  in Left answer
            mf = AM.fromLists $ map (map toComplex) $ matrixRep f
            (_, evecs) = LA.eig $ LA.ctrans mf
            calc vec ={-# SCC "calc" #-}
              let c = vec @> cind
                  phi (idx, Right nth) acc = acc & ix idx .~ (vec @> nth) / c
                  phi (idx, Left g)    acc = acc & ix idx .~ substWith (*) acc g
              in if c == 0
                 then Nothing
                 else Just $ foldr ({-# SCC "rewrite-answer" #-} phi) (SV.replicate (sArity f0) (error "indec!")) inds
        in sequence $ map calc $ LA.toColumns evecs

solve' :: (Field r, IsPolynomial r n, IsMonomialOrder ord, Convertible r Double)
       => Double
       -> Ideal (OrderedPolynomial r ord (S n))
       -> [SV.Vector (Complex Double) (S n)]
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
       , all ((<err) . magnitude . substWith mul xs) $ generators ideal
       ]

subspMatrix :: (Normed r, Ord r, Field r, IsPolynomial r n, IsMonomialOrder ord)
            => Ordinal n -> Ideal (OrderedPolynomial r ord n) -> M.Matrix r
subspMatrix on ideal =
  let poly = univPoly on ideal
      v    = var on `asTypeOf` head (generators ideal)
      dim  = totalDegree' poly
      cfs  = [negate $ coeff (leadingMonomial $ pow v (j :: Natural)) poly | j <- [0..fromIntegral (dim - 1)]]
  in (M.fromLists [replicate (dim - 1) zero]
          M.<->
      fmap unwrapField (M.identity (dim - 1))) M.<|> M.colVector (V.fromList cfs)

solveViaCompanion :: forall r ord n.
                     (Normed r, Ord r, Field r, IsPolynomial r n, IsMonomialOrder ord, Convertible r Double)
                  => Double
                  -> Ideal (OrderedPolynomial r ord n)
                  -> [SV.Vector (Complex Double) n]
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
     , all ((<err) . magnitude . substWith mul xs) $ generators ideal
     ]

matToLists :: M.Matrix a -> [[a]]
matToLists mat = [ V.toList $ M.getRow i mat | i <- [1.. M.nrows mat] ]

matrixRep :: (NoetherianRing t, Eq t, Field t, SingRep n, IsMonomialOrder order,
              Reifies ideal (QIdeal t order n))
           => Quotient t order n ideal -> [[t]]
matrixRep f = {-# SCC "matrixRep" #-}
  case standardMonomials of
    Just []    -> []
    Just bases ->
      let anss = map (quotRepr . (f *)) bases
      in transpose $ map (\a -> map (flip coeff a . leadingMonomial . quotRepr) bases) anss
    Nothing -> error "Not finite dimension"

toComplex :: Convertible a Double => a -> Complex Double
toComplex a = convert a :+ 0

reduction :: (IsPolynomial r n, IsMonomialOrder ord, Field r)
             => Ordinal n -> OrderedPolynomial r ord n -> OrderedPolynomial r ord n
reduction on f = {-# SCC "reduction" #-}
  let df = {-# SCC "differentiate" #-} diff on f
  in snd $ head $ f `divPolynomial` calcGroebnerBasis (toIdeal [f, df])

-- | Calculate the monic generator of k[X_0, ..., X_n] `intersect` k[X_i].
univPoly :: forall r ord n. (Ord r, Normed r, Field r, IsPolynomial r n, IsMonomialOrder ord)
         => Ordinal n
         -> Ideal (OrderedPolynomial r ord n)
         -> OrderedPolynomial r ord n
univPoly nth ideal = {-# SCC "univPoly" #-}
  reifyQuotient ideal $ \pxy ->
  if gBasis' pxy == [one]
  then one
  else let x = var nth
           p0 : pows = [fmap WrapField $ vectorRep $ modIdeal' pxy (pow x i)
                       | i <- [0:: Natural ..]
                       | _ <- zero : fromJust (standardMonomials' pxy) ]
           step m (p : ps) = {-# SCC "univPoly/step" #-}
             case solveLinear m p of
               Nothing  -> {-# SCC "recur" #-} step ({-# SCC "consCol" #-}m M.<|> M.colVector p) ps
               Just ans ->
                 let cur = fromIntegral $ V.length ans :: Natural
                 in {-# SCC "buildRelation" #-}
                    pow x cur - sum (zipWith (.*.) (map unwrapField $ V.toList ans)
                                     [pow x i | i <- [0 :: Natural .. cur P.- 1]])
       in step (M.colVector p0) pows

-- | Solves linear system. If the given matrix is degenerate, this returns @Nothing@.
solveLinear :: (Normed r, Ord r, Eq r, Fractional r)
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
    (u, l, p, q, _, _) = M.luDecomp' mat
    (u', _,_, _, _, _) = M.luDecomp' (mat M.<|> M.colVector vec)
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
radical :: forall r ord n . (Normed r, Ord r, IsPolynomial r n, Field r, IsMonomialOrder ord)
        => Ideal (OrderedPolynomial r ord n) -> Ideal (OrderedPolynomial r ord n)
radical ideal = {-# SCC "radical" #-}
  let gens  = {-# SCC "calcGens" #-} map (\on -> reduction on $ univPoly on ideal) $ enumOrdinal (sing :: SNat n)
  in toIdeal $ calcGroebnerBasis $ toIdeal $ generators ideal ++ gens

-- | Test if the given zero-dimensional ideal is radical or not.
isRadical :: forall r ord n. (Normed r, Ord r, IsPolynomial r n, Field r, IsMonomialOrder ord)
          => Ideal (OrderedPolynomial r ord (S n)) -> Bool
isRadical ideal =
  let gens  = map (\on -> reduction on $ univPoly on ideal) $ enumOrdinal (sing :: SNat (S n))
  in all (`isIdealMember` ideal) gens

solve'' :: forall r ord n.
           (Show r, Sparse.Eq0 r, Normed r, Ord r, Field r, IsPolynomial r n,
            IsMonomialOrder ord, Convertible r Double)
       => Double
       -> Ideal (OrderedPolynomial r ord (S n))
       -> [SV.Vector (Complex Double) (S n)]
solve'' err ideal =
  reifyQuotient (radical ideal) $ \ii ->
  let gbs = gBasis' ii
      lexBase = fst $ fglm $ toIdeal gbs
      upoly = last lexBase
      restVars = init $ SV.toList allVars
      calcEigs = nub . LA.toList . LA.eigenvalues . AM.fromLists
      lastEigs = calcEigs $ matToLists $ fmap (toComplex . unwrapField) $
                 (AM.companion maxBound $ mapCoeff WrapField upoly)
  in if gbs == [one]
     then []
     else if length (lastEigs) == length (fromJust $ standardMonomials' ii)
          then solveSpan (init lexBase) lastEigs
          else chooseAnswer $
               lastEigs : map (calcEigs . map (map toComplex) . matrixRep . modIdeal' ii)
                              restVars
  where
    mul p q = toComplex p * q
    solveSpan rest lastEigs =
      let answers = map (\f -> toPolynomial (leadingTerm f) - f) rest
          substEig eig = substWith (\d b -> toComplex d * b) $ SV.unsafeFromList' $ map (const zero) rest ++ [eig]
      in [ SV.unsafeFromList' $ map (substEig eig) answers ++ [eig]
         | eig <- lastEigs
         ]
    chooseAnswer vs =
          [ xs
            | xs0 <- sequence vs
            , let xs = SV.unsafeFromList' xs0
            , all ((<err) . magnitude . substWith mul xs) $ generators ideal
            ]

solveLinearNA :: (Ord b, Ring b, Division b, Normed b) => M.Matrix b -> V.Vector b -> Maybe (V.Vector b)
solveLinearNA m v = fmap unwrapField <$> solveLinear (fmap WrapField m) (fmap WrapField v)

toDM :: (AM.Matrix mat, AM.Elem mat a, AM.Elem M.Matrix a) => mat a -> M.Matrix a
toDM = AM.fromCols . AM.toCols

-- * FGLM

-- | Calculate the Groebner basis w.r.t. lex ordering of the zero-dimensional ideal using FGLM algorithm.
--   If the given ideal is not zero-dimensional this function may diverge.
fglm :: (Normed r, Ord r, SingRep n, Division r, NoetherianRing r, IsMonomialOrder ord)
     => Ideal (OrderedPolynomial r ord (S n))
     -> ([OrderedPolynomial r Lex (S n)], [OrderedPolynomial r Lex (S n)])
fglm ideal =
  let (gs, bs) = reifyQuotient ideal $ \pxy -> fglmMap (\f -> vectorRep $ modIdeal' pxy f)
  in (gs, bs)

-- | Compute the kernel and image of the given linear map using generalized FGLM algorithm.
fglmMap :: forall k ord n. (Normed k, Ord k, Field k, IsMonomialOrder ord, IsPolynomial k n)
        => (OrderedPolynomial k ord (S n) -> V.Vector k)
        -- ^ Linear map from polynomial ring.
        -> ( [OrderedPolynomial k Lex (S n)] -- ^ lex-Groebner basis of the kernel of the given linear map.
           , [OrderedPolynomial k Lex (S n)] -- ^ The vector basis of the image of the linear map.
           )
fglmMap l = runST $ do
  env <- FGLMEnv l <$> newSTRef [] <*> newSTRef [] <*> newSTRef Nothing <*> newSTRef one
  flip runReaderT env $ do
    mainLoop
    whileM_ toContinue $ nextMonomial >> mainLoop
    (,) <$> look gLex <*> (map (changeOrder Lex) <$> look bLex)

mainLoop :: (Ord r, Normed r, SingRep n, Division r, NoetherianRing r, IsOrder o)
         => Machine s r o n ()
mainLoop = do
  m <- look monomial
  let f = toPolynomial (one, changeMonomialOrderProxy Proxy m)
  lx <- image f
  bs <- mapM image =<< look bLex
  let mat  = foldr1 (M.<|>) $ map (M.colVector . fmap WrapField) bs
      cond | null bs   = if V.all (== zero) lx
                         then Just $ V.replicate (length bs) zero
                         else Nothing
           | otherwise = solveLinear mat (fmap WrapField lx)
  case cond of
    Nothing -> do
      proced .== Nothing
      bLex %== (f : )
    Just cs -> do
      bps <- look bLex
      let g = changeOrder Lex $ f - sum (zipWith (.*.) (V.toList $ fmap unwrapField cs) bps)
      proced .== Just (changeOrder Lex f)
      gLex %== (g :)

toContinue :: (Ord r, SingRep n, Division r, NoetherianRing r, IsOrder o)
           => Machine s r o (S n) Bool
toContinue = do
  mans <- look proced
  case mans of
    Nothing -> return True
    Just g -> do
      let xLast = SV.maximum allVars `asTypeOf` g
      return $ not $ leadingMonomial g `isPowerOf` leadingMonomial xLast

nextMonomial :: (Eq r, SingRep n, NoetherianRing r) => Machine s r ord n ()
nextMonomial = do
  m <- look monomial
  gs <- map leadingMonomial <$> look gLex
  let next = fst $ maximumBy (comparing snd)
             [ (OrderedMonomial monom, ordToInt od)
             | od <- [0..]
             , let monom = beta (getMonomial m) od
             , all (not . (`divs` OrderedMonomial monom)) gs
             ]
  monomial .== next

beta :: forall n. SingRep n => Monomial n -> Ordinal n -> Monomial n
beta (a :- _) OZ      =
  case sing :: SNat n of
    SS n -> case singInstance n of SingInstance -> (a + 1) :- SV.replicate' 0
    _   -> error "bugInGHC!"
beta (a :- as) (OS n) =
  case sing :: SNat n of
    SS k -> case singInstance k of SingInstance -> a :- beta as n
    _ -> error "bugInGHC"
beta Nil      _       = bugInGHC
