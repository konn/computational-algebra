{-# LANGUAGE BangPatterns, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction           #-}
module Main where
import           Algebra.Algorithms.Groebner
import           Algebra.Prelude
import           Control.Arrow               ((***))
import           Data.Singletons             (SingRep)
import           Data.Type.Natural           (One)
import           Data.Type.Ordinal           (Ordinal (..))
import           Data.Vector.Sized           (Vector (..))
import           GHC.Num                     (Num)
import           Numeric.Decidable.Zero      (isZero)
import qualified Numeric.Field.Fraction      as F
import           Numeric.Semiring.Integral   (IntegralSemiring)
import           Prelude                     (Show (..), filter)
import           Prelude                     (abs)
import qualified Prelude                     as P

data Algebraic = Algebraic { eqn      :: Polynomial Rational One
                           , interval :: Interval Rational
                           } deriving (Show)

instance Additive Algebraic where
  (+) = plusA

instance Group Algebraic where
  negate r = (-1 :: Integer) .* r

instance Monoidal Algebraic where
  zero = Algebraic varX (Interval 0 0)

instance LeftModule Natural Algebraic where
  (.*) n = (.*) $ P.toInteger n

instance RightModule Natural Algebraic where
  (*.) = flip (.*)

instance LeftModule Integer Algebraic where
  n .* Algebraic f int
   | n == 0 = Algebraic varX (Interval 0 0)
   | otherwise = Algebraic (subst' varX (injectCoeff (1 %% n) * varX) f) (scale (n %% 1) int)

instance LeftModule (Fraction Integer) Algebraic where
  q .* Algebraic f int
   | isZero q  = Algebraic varX (Interval 0 0)
   | otherwise = Algebraic (subst' varX (injectCoeff (recip q) * varX) f) (scale q int)

instance RightModule Integer Algebraic where
  (*.) = flip (.*)

instance RightModule (Fraction Integer) Algebraic where
  (*.) = flip (.*)

scale :: (Ord r, Multiplicative r, Monoidal r) => r -> Interval r -> Interval r
scale k (Interval l r)
  | k < zero  = Interval (k * r) (k * l)
  | otherwise = Interval (k * l) (k * r)

includes :: Ord a => Interval a -> Interval a -> Bool
Interval i j `includes` Interval i' j' = i <= i' && j' <= j

plusInt :: Group r => Interval r -> Interval r -> Interval r
plusInt (Interval l u) (Interval l' u') = Interval (l + l') (u + u')

rootSumPoly :: Polynomial Rational One -> Polynomial Rational One -> Polynomial Rational One
rootSumPoly f g = monoize $ sqFreePart $ presultant (liftP f) (substWith (.*.) (injectCoeff varX - varX :- Nil) $ liftP g)
  where
    liftP :: Polynomial Rational One -> Polynomial (Polynomial Rational One) One
    liftP = mapCoeff injectCoeff

sqFreePart :: (DecidableUnits r, Eq r, Domain r, DecidableZero r, Division r, Commutative r, IsMonomialOrder order)
           => OrderedPolynomial r order One -> OrderedPolynomial r order One
sqFreePart f = snd $ head $ f `divPolynomial` [gcd f (diff OZ f)]

plusA :: Algebraic -> Algebraic -> Algebraic
plusA (Algebraic f i0) (Algebraic g j0)
  | totalDegree' f == 1 && isZero (coeff one f) = Algebraic g j0
  | totalDegree' g == 1 && isZero (coeff one g) = Algebraic f i0
  | otherwise =
  let !fg = rootSumPoly f g
      sols = isolateRoots fg
      lens = map size sols
      sf = strum f
      sg = strum g
      (i', j') = until (\(i,j) -> all (size (plusInt i j) <) lens)
                            (improveWith sf *** improveWith sg)
                            (i0, j0)
      iij = i' `plusInt` j'
  in  Algebraic fg iij

rootMultPoly :: Polynomial Rational One -> Polynomial Rational One -> Polynomial Rational One
rootMultPoly f g =
  let ts@((_, lm):_) = getTerms g
      d = totalDegree lm
      g' = sum $  map (\(k, m) -> toPolynomial (injectCoeff k * varX^(P.fromIntegral $ totalDegree m),
                                                (OrderedMonomial $ d - totalDegree m :- Nil)) ) ts
  in monoize $ sqFreePart $ presultant (liftP f) g'
  where
    liftP :: Polynomial Rational One -> Polynomial (Polynomial Rational One) One
    liftP = mapCoeff injectCoeff

monoize :: (Ring r, DecidableZero r, Division r, SingRep n, IsOrder order)
        => OrderedPolynomial r order n -> OrderedPolynomial r order n
monoize f =
  let lc = leadingCoeff f
  in if isZero lc
     then zero
     else recip lc .*. f

strum :: Polynomial Rational One -> [Polynomial Rational One]
strum f = zipWith (*) (cycle [1,1,-1,-1]) $
          map (\(p,_,_) -> p * injectCoeff (recip $ abs (leadingCoeff p))) $
          reverse $ prs f (diff OZ f)

data Interval r = Interval { lower :: !r, upper :: !r } deriving (Eq, Ord)

size :: Group r => Interval r -> r
size (Interval l r) = r - l

instance Show r => Show (Interval r) where
  showsPrec _ (Interval l u) = showChar '(' . showsPrec 5 l . showString ", " . showsPrec 5 u . showChar ']'

bisect :: (Ring r, Division r) => Interval r -> (Interval r, Interval r)
bisect (Interval l u) =
  let mid = (l+u) / fromInteger 2
  in (Interval l mid, Interval mid u)

signChange :: (Ord a, Ring a, DecidableZero a) => [a] -> Int
signChange xs =
  let nzs = filter (not . isZero) xs
  in length $ filter (< zero) $ zipWith (*) nzs (tail nzs)

countRootsIn :: Polynomial Rational One -> Interval Rational -> Int
countRootsIn f ints = countChangeIn ints (strum f)

countChangeIn :: (Ord a, Ring a, DecidableZero a)
                 => Interval a -> [OrderedPolynomial a order One] -> Int
countChangeIn ints ss =
  signChangeAt (lower ints) ss - signChangeAt (upper ints) ss

signChangeAt :: (Ord a, Ring a, DecidableZero a) => a -> [OrderedPolynomial a order One] -> Int
signChangeAt a fs = signChange $ map (substWith (*) (a :- Nil)) fs

rootBound :: (IsMonomialOrder ord, Num r, Ord r, Ring r, Division r)
          => OrderedPolynomial r ord One -> r
rootBound f
  | totalDegree' f == 0 = 0
  | otherwise =
    let a:as = map fst $ getTerms f
    in 1 + maximum (map (abs . (/ a)) as)

isolateRoots :: Polynomial Rational One -> [Interval Rational]
isolateRoots f =
  let bd = rootBound f * 2
  in go (Interval (- bd) bd)
  where
    !ss = strum f
    go int =
      let rcount = countChangeIn int ss
      in if rcount == 0
         then []
         else if rcount  == 1
              then [int]
              else let (ls, us) = bisect int
                   in go ls ++ go us

improve :: Algebraic -> Algebraic
improve (Algebraic f int) = Algebraic f $ improveWith (strum f) int

improveWith :: (Ord a, Ring a, DecidableZero a, Division a)
            => [OrderedPolynomial a order One] -> Interval a -> Interval a
improveWith ss int =
  let (ls, us) = bisect int
  in if countChangeIn ls ss == 0 then us else ls

(%%) :: Euclidean d => d -> d -> Fraction d
(%%) = (F.%)

iterateImprove :: Rational -> Polynomial Rational One -> Interval Rational -> Interval Rational
iterateImprove eps f int0 =
  let ss = strum f
  in until (\int -> size int < eps) (improveWith ss) int0

fromFraction :: P.Fractional a => Fraction Integer -> a
fromFraction q = P.fromInteger (numerator q) P./ P.fromInteger (denominator q)

sample :: (Num r, Division r, Additive r) => Interval r -> r
sample (Interval l r) = (l+r)/2

presultant :: (Euclidean k, IsOrder ord) => OrderedPolynomial k ord One -> OrderedPolynomial k ord One -> k
presultant = go one one
  where
    go !res !acc h s
        | totalDegree' s > 0     =
          let (_, r)    = h `pDivModPoly` s
              res' = res * pow (negate one)
                           (P.fromIntegral $ totalDegree' h * totalDegree' s :: Natural)
                     * pow1p (leadingCoeff s) (P.fromIntegral $ totalDegree' h - totalDegree' r - 1 :: Natural)
              adj = pow (leadingCoeff s) (P.fromIntegral $ totalDegree' h - totalDegree' s + 1 :: Natural)
          in go res' (acc * adj) s r
        | isZero h || isZero s = zero
        | totalDegree' h > 0     = pow (leadingCoeff s) (P.fromIntegral $ totalDegree' h :: Natural) * res `quot` acc
        | otherwise              = res `quot` acc
