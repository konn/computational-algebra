{-# LANGUAGE ConstraintKinds, DataKinds, DefaultSignatures, FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, GADTs, MultiParamTypeClasses                 #-}
{-# LANGUAGE NoMonomorphismRestriction, OverlappingInstances                 #-}
{-# LANGUAGE OverloadedStrings, PolyKinds, ScopedTypeVariables, TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances, IncoherentInstances #-}
-- | Algorithms for zero-dimensional ideals.
module Algebra.Algorithms.ZeroDim where
import           Algebra.Algorithms.Groebner
import           Algebra.Instances                ()
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Algebra.Ring.Polynomial.Quotient
import           Algebra.Scalar
import           Control.Applicative
import           Control.Arrow
import           Control.Lens                     hiding (coerce)
import           Control.Monad
import           Control.Monad.Random
import           Data.Complex
import           Data.List                        hiding (sum)
import           Data.Maybe
import           Data.Ord
import           Data.Ratio
import           Data.Reflection
import           Data.Singletons
import           Data.Type.Natural                (Nat (..), SNat,
                                                   Sing (SS, SZ), sNatToInt)
import qualified Data.Vector.Sized                as V
import           Numeric.Algebra                  hiding ((/), (<))
import qualified Numeric.Algebra                  as NA
import           Numeric.LinearAlgebra            hiding (Field, find, step)
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

solveM :: forall m r ord n. (MonadRandom m, Field r, IsPolynomial r n, IsMonomialOrder ord,
                             Coercible r (Complex Double), Show (OrderedPolynomial r ord (S n)))
       => Ideal (OrderedPolynomial r ord (S n))
       -> m [V.Vector (Complex Double) (S n)]
solveM ideal = reifyQuotient ideal $ \pxy -> 
  case standardMonomials' pxy of
    Just bs -> step (length bs)
    Nothing -> error "Given ideal is not zero-dimensional"
  where
    step len = do
      coeffs <- replicateM (sNatToInt (sing :: SNat (S n))) getRandom
      let vars = V.toList allVars
          f = sum $ zipWith (.*.) (map (NA.fromInteger :: Integer -> r) coeffs) vars
          sols = solveWith ideal f
      if length sols == len
        then return sols
        else step len

solve' :: (Field r, IsPolynomial r n, IsMonomialOrder ord, Coercible r Double)
       => Double
       -> Ideal (OrderedPolynomial r ord (S n))
       -> [V.Vector (Complex Double) (S n)]
solve' err ideal =
  reifyQuotient ideal $ \ii ->
    let vs = map (LA.toList . eigenvalues . fromLists . map (map coerce') . matrixRep . modIdeal' ii) $
             V.toList allVars
        mul p q = coerce p * q
    in [ xs
       | xs0 <- sequence vs
       , let xs = V.unsafeFromList' xs0
       , all ((<err) . magnitude . substWith mul xs) $ generators ideal
       ]


solveWith :: (Field r, IsPolynomial r n, IsMonomialOrder ord, Coercible r (Complex Double))
          => Ideal (OrderedPolynomial r ord (S n))
          -> OrderedPolynomial r ord (S n)
          -> [V.Vector (Complex Double) (S n)]
solveWith i0 f0 =
  let ideal = calcGroebnerBasis i0
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
      (_, evecs) = LA.eig $ ctrans mf
      calc vec =
        let c = vec @> cind
            phi (idx, Right nth) acc = acc & ix idx .~ ((vec @> nth) / c)
            phi (idx, Left g)    acc = acc & ix idx .~ substWith (*) acc g
        in foldr phi (V.replicate (sArity f0) (error "indec!")) inds
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

enumOrdinal :: SNat n -> [V.Ordinal n]
enumOrdinal SZ = []
enumOrdinal (SS n) = V.OZ : map V.OS (enumOrdinal n)

coerce' :: Coercible a (Complex Double) => a -> Complex Double
coerce' a = coerce a
