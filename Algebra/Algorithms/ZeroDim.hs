{-# LANGUAGE ConstraintKinds, DataKinds, DefaultSignatures, FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving            #-}
{-# LANGUAGE IncoherentInstances, MultiParamTypeClasses, TemplateHaskell     #-}
{-# LANGUAGE NoMonomorphismRestriction, OverlappingInstances                 #-}
{-# LANGUAGE OverloadedStrings, PolyKinds, ScopedTypeVariables, TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances, StandaloneDeriving  #-}
-- | Algorithms for zero-dimensional ideals.
module Algebra.Algorithms.ZeroDim (univPoly, radical, isRadical, solveWith, WrappedField(..),
                                   solveM, solve', matrixRep, vectorRep, solveLinear) where
import           Algebra.Algorithms.Groebner
import           Algebra.Instances                ()
import qualified Algebra.Linear                   as M
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Algebra.Ring.Polynomial.Quotient
import qualified Data.Vector.Generic.Mutable      as MV
import           Algebra.Scalar
import           Control.Applicative
import           Control.Arrow
import           Control.Lens                     hiding (coerce)
import           Control.Monad
import           Control.Monad.Random
import           Data.Complex
import           Data.List                        hiding (sum)
import           Data.Maybe
import           Data.Proxy
import           Data.Ord
import           Data.Ratio
import           Data.Reflection
import           Data.Singletons
import           Data.Type.Natural                (Nat (..), SNat,
                                                   sNatToInt, One)
import           Data.Type.Ordinal
import qualified Data.Vector                      as V
import qualified Data.Vector.Sized                as SV
import           Numeric.Algebra                  hiding ((/), (<))
import qualified Numeric.Algebra                  as NA
import           Numeric.LinearAlgebra            ((@>))
import qualified Numeric.LinearAlgebra            as LA
import           Prelude                          hiding (lex, negate, recip,
                                                   sum, (*), (+), (-), (^),
                                                   (^^))
import qualified Prelude                          as P

class Coercible a b where
  coerce :: a -> b

  default coerce :: (a ~ b) => a -> b
  coerce = id

instance Coercible Double Double
instance Coercible Int Int
instance Coercible Integer Integer
instance Coercible Float Float
instance Coercible (Complex a) (Complex a)
instance (Num b, Coercible a b) => Coercible a (Complex b) where
  coerce = (:+ 0) . coerce
instance Coercible Double Rational where
  coerce = toRational
instance Coercible Rational Double where
  coerce = fromRational
instance Coercible Float Rational where
  coerce = toRational
instance Coercible Rational Float where
  coerce = fromRational

newtype WrappedField a = WrapField { unwrapField :: a
                                   } deriving (Read, Show, Eq, Ord,
                                               Additive, Multiplicative,
                                               Unital, DecidableUnits, Division)

makeWrapped ''WrappedField

instance LeftModule a r => LeftModule a (WrappedField r) where
  n .* WrapField r = WrapField $ n .* r

instance RightModule a r => RightModule a (WrappedField r) where
  WrapField r *. n = WrapField $ r *. n

deriving instance Monoidal r => Monoidal (WrappedField r)
deriving instance Group r => Group (WrappedField r)
deriving instance DecidableZero r => DecidableZero (WrappedField r)

instance (Ord r, Group r, Ring r) => Num (WrappedField r) where
  WrapField a + WrapField b = WrapField $ a + b
  WrapField a - WrapField b = WrapField $ a - b
  WrapField a * WrapField b = WrapField $ a * b
  negate = unwrapped %~ negate
  fromInteger = WrapField . NA.fromInteger
  abs n = if n < zero then negate n else n
  signum _ = NA.one

instance (Ord r, Ring r, Division r, Group r) => Fractional (WrappedField r) where
  WrapField a / WrapField b = WrapField $ a NA./ b
  recip (WrapField a) = WrapField $ NA.recip a
  fromRational q = WrapField $ NA.fromInteger (numerator q) NA./ NA.fromInteger (denominator q)

solveM :: forall m r ord n. (Ord r, MonadRandom m, Field r, IsPolynomial r n, IsMonomialOrder ord,
                             Coercible r (Complex Double))
       => Ideal (OrderedPolynomial r ord (S n))
       -> m [SV.Vector (Complex Double) (S n)]
solveM ideal = reifyQuotient ideal $ \pxy ->
  case standardMonomials' pxy of
    Just bs -> step (length bs)
    Nothing -> error "Given ideal is not zero-dimensional"
  where
    step len = do
      coeffs <- replicateM (sNatToInt (sing :: SNat (S n))) getRandom
      let vars = SV.toList allVars
          f = sum $ zipWith (.*.) (map (NA.fromInteger :: Integer -> r) coeffs) vars
          sols = solveWith ideal f
      if length sols == len
        then return sols
        else step len

solve' :: (Field r, IsPolynomial r n, IsMonomialOrder ord, Coercible r Double)
       => Double
       -> Ideal (OrderedPolynomial r ord (S n))
       -> [SV.Vector (Complex Double) (S n)]
solve' err ideal =
  reifyQuotient ideal $ \ii ->
    let vs = map (LA.toList . LA.eigenvalues . LA.fromLists . map (map coerce') . matrixRep . modIdeal' ii) $
             SV.toList allVars
        mul p q = coerce p * q
    in [ xs
       | xs0 <- sequence vs
       , let xs = SV.unsafeFromList' xs0
       , all ((<err) . magnitude . substWith mul xs) $ generators ideal
       ]

solveWith :: (Ord r, Field r, IsPolynomial r n, IsMonomialOrder ord, Coercible r (Complex Double))
          => Ideal (OrderedPolynomial r ord (S n))
          -> OrderedPolynomial r ord (S n)
          -> [SV.Vector (Complex Double) (S n)]
solveWith i0 f0 =
  let ideal = generators $ radical i0
  in reifyQuotient (toIdeal ideal) $ \pxy ->
  let f = modIdeal' pxy f0
      vars = sortBy (comparing snd) $ zip (enumOrdinal $ sArity f0) $
             map leadingOrderedMonomial $ genVars (sArity f0) `asTypeOf` [f0]
      Just base = map (leadingOrderedMonomial . quotRepr) <$> standardMonomials' pxy
      inds = flip map vars $ second $ \b ->
        case findIndex (==b) base of
          Just ind -> Right ind
          Nothing  ->
            let Just g = find ((==b) . leadingOrderedMonomial) ideal
                r = leadingCoeff g
            in Left $ mapCoeff coerce $ injectCoeff (recip r) * (toPolynomial (leadingTerm g) - g)
      mf = LA.fromLists $ map (map coerce') $ matrixRep f
      Just cind = elemIndex one base
      (_, evecs) = LA.eig $ LA.ctrans mf
      calc vec =
        let c = vec @> cind
            phi (idx, Right nth) acc = acc & ix idx .~ ((vec @> nth) / c)
            phi (idx, Left g)    acc = acc & ix idx .~ substWith (*) acc g
        in foldr phi (SV.replicate (sArity f0) (error "indec!")) inds
  in map calc $ LA.toColumns evecs

matrixRep :: (NoetherianRing t, Eq t, Field t, SingRep n, IsMonomialOrder order,
              Reifies ideal (QIdeal t order n))
           => Quotient t order n ideal -> [[t]]
matrixRep f =
  case standardMonomials of
    Just bases ->
      let anss = map (quotRepr . (f *)) bases
      in transpose $ map (\a -> map (flip coeff a . leadingMonomial . quotRepr) bases) anss
    Nothing -> error "Not finite dimension"

coerce' :: Coercible a (Complex Double) => a -> Complex Double
coerce' a = coerce a

vectorRep :: forall r order ideal n.
              (Division r, IsPolynomial r n, IsMonomialOrder order, Reifies ideal (QIdeal r order n))
           => Quotient r order n ideal -> V.Vector r
vectorRep f =
  case standardMonomials' (Proxy :: Proxy ideal) of
    Just base -> let mf = quotRepr f
                 in V.fromList $ map (flip coeff mf . leadingMonomial . quotRepr) base
    Nothing -> error "dieeee"

reduction :: (IsPolynomial r n, IsMonomialOrder ord, Field r)
             => OrderedPolynomial r ord (S n) -> OrderedPolynomial r ord (S n)
reduction f =
  let df = diff 0 f
  in snd $ head $ f `divPolynomial` calcGroebnerBasis (toIdeal [f, df])

-- | Calculate the monic generator of k[X_0, ..., X_n] `intersect` k[X_i].
univPoly :: forall r ord n. (Ord r, Field r, IsPolynomial r n, IsMonomialOrder ord)
         => Ordinal n
         -> Ideal (OrderedPolynomial r ord n)
         -> OrderedPolynomial r ord n
univPoly nth ideal =
  reifyQuotient ideal $ \pxy ->
  let x = var nth
      p0 : pows = [fmap WrapField $ vectorRep $ modIdeal' pxy (pow x i) | i <- [0:: Natural ..] ]
      step m (p : ps) =
        case solveLinear m p of
          Nothing  -> step (m M.<|> M.colVector p) ps
          Just ans ->
            let cur = fromIntegral $ V.length ans :: Natural
            in pow x cur - sum (zipWith (.*.) (map unwrapField $ V.toList ans)
                                [pow x i | i <- [0 :: Natural .. cur P.- 1]])
  in step (M.colVector p0) pows

-- | Solve linear systems
solveLinear :: (Ord r, Fractional r)
            => M.Matrix r
            -> V.Vector r
            -> Maybe (V.Vector r)
solveLinear mat vec =
  if M.diagProd u == 0
  then Nothing 
  else let ans = M.getCol 1 $ p P.* M.colVector vec
       in let lsol = solveL ans
              cfs = M.getCol 1 $ q P.* M.colVector (solveU lsol)
              degenerate = V.all (== 0) cfs && V.any (/= 0) vec
              unsolvable = uRank < V.foldr (\a acc -> if a /= 0 then acc P.+ 1 else acc) 0 lsol
              unsolvable' = V.length cfs < V.length vec && V.any (/= 0) (V.drop (V.length cfs) ans)
          in if degenerate || unsolvable || unsolvable'
             then Nothing
             else Just cfs
  where
    (u, l, p, q, _, _) = M.luDecomp' mat
    uRank = V.foldr (\a acc -> if a /= 0 then acc P.+ 1 else acc) (0 :: Int) $ M.getDiag u
    solveL v = V.create $ do
      mv <- MV.replicate (M.ncols l) 0
      forM_ [0..M.ncols l - 1] $ \i -> do
        MV.write mv i $ v V.! i
        forM_ [0,1..i-1] $ \j -> do
          a <- MV.read mv i
          b <- MV.read mv j
          MV.write mv i $ a P.- (l M.! (i + 1, j + 1)) P.* b
      return mv
    solveU v = V.create $ do
      mv <- MV.replicate (M.ncols u) 0
      forM_ [M.ncols u - 1, M.ncols u - 2..0] $ \ i -> do
        MV.write mv i $ v V.! i
        forM_ [i+1,i+2..M.ncols u-1] $ \j -> do
          a <- MV.read mv i
          b <- MV.read mv j
          MV.write mv i $ a P.- (u M.! (i+1, j+1)) P.* b
        a0 <- MV.read mv i
        MV.write mv i $ a0 / (u M.! (i+1, i+1))
      return mv

-- | Calculate the radical of the given zero-dimensional ideal.
radical :: forall r ord n . (Ord r, IsPolynomial r n, Field r, IsMonomialOrder ord)
        => Ideal (OrderedPolynomial r ord (S n)) -> Ideal (OrderedPolynomial r ord (S n))
radical ideal =
  let gens  = map (reduction . flip univPoly ideal) $ enumOrdinal (sing :: SNat (S n))
  in toIdeal $ calcGroebnerBasis $ toIdeal $ generators ideal ++ gens

-- | Test if the given zero-dimensional ideal is radical or not.
isRadical :: forall r ord n. (Ord r, IsPolynomial r n, Field r, IsMonomialOrder ord)
          => Ideal (OrderedPolynomial r ord (S n)) -> Bool
isRadical ideal =
  let gens  = map (reduction . flip univPoly ideal) $ enumOrdinal (sing :: SNat (S n))
  in all (`isIdealMember` ideal) gens

testMat :: M.Matrix Rational
testMat = M.fromLists [[1,0,0]
                      ,[0,0,0]
                      ,[0,0,0]
                      ,[0,0,0]
                      ,[0,1,0]
                      ,[0,0,0]
                      ,[0,0,0]
                      ,[0,0,0]
                      ,[0,0,1]
                      ]

