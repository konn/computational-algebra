{-# LANGUAGE BangPatterns, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction           #-}
module Main where
import           Algebra.Algorithms.Groebner
import           Algebra.Prelude             hiding (normalize)
import           Control.Arrow               ((***))
import           Data.Singletons             (SingRep)
import           Data.Type.Natural           (One)
import           Data.Type.Ordinal           (Ordinal (..))
import           Data.Vector.Sized           (Vector (..))
import           GHC.Num                     (Num)
import           Numeric.Decidable.Zero      (isZero)
import qualified Numeric.Field.Fraction      as F
import           Numeric.Semiring.Integral   (IntegralSemiring)
import           Prelude                     (Show (..), abs, filter)
import qualified Prelude                     as P

-- Invariants:
--   (1) eqn is square-free and does not have x as a factor
--   (2) strumseq is the standard strum sequence of eqn
--   (3) interval contains exactly one root of eqn
data Algebraic = Algebraic { eqn      :: Polynomial Rational One
                           , strumseq :: [Polynomial Rational One]
                           , interval :: Interval Rational
                           }
               | Rational !Rational
                 deriving (Show)

instance Additive Algebraic where
  (+) = plusA

instance Group Algebraic where
  negate r = (-1 :: Integer) .* r

instance Monoidal Algebraic where
  zero = Rational zero

instance LeftModule Natural Algebraic where
  (.*) n = (.*) $ P.toInteger n

instance RightModule Natural Algebraic where
  (*.) = flip (.*)

instance LeftModule Integer Algebraic where
  n .* Rational r = Rational (n .* r)
  n .* Algebraic f _ int
   | n == 0 = zero
   | otherwise = let f' = (subst' varX (injectCoeff (1 %% n) * varX) f)
                 in Algebraic f' (strum f') (scale (n %% 1) int)

instance LeftModule (Fraction Integer) Algebraic where
  q .* Rational r = Rational (q * r)
  q .* Algebraic f _ int
   | isZero q  = zero
   | otherwise = let f' = subst' varX (injectCoeff (recip q) * varX) f
                 in Algebraic f' (strum f') (scale q int)

instance RightModule Integer Algebraic where
  (*.) = flip (.*)

instance RightModule (Fraction Integer) Algebraic where
  (*.) = flip (.*)

instance Multiplicative Algebraic where
  (*) = multA

instance Eq Algebraic where
  Rational p      == Rational q = p == q
  Algebraic f _ i == Algebraic g _ j
    | not $ isZero $ resultant f g = False
    | otherwise =
        let sh = strum $ gcd f g
        in countChangeIn (i `intersect` j) sh == 1
  _ == _ = False

intersect :: (Num a, Ord a) => Interval a -> Interval a -> Interval a
intersect i j | disjoint i j = Interval 0 0
              | lower i <= lower j = Interval (lower j) (upper i)
              | lower j >  lower i = Interval (lower i) (upper j)
intersect _ _ = error "intersect"

instance Ord Algebraic where
  compare (Rational q) (Rational r) = compare q r
  compare (Rational q) (Algebraic f sf i) =
    let i' = until (not . (q `isIn`)) (improveWith sf) i
    in if q <= lower i'
       then LT
       else if isZero (f `modPolynomial` [varX - injectCoeff q])
            then EQ
            else GT
  compare a@(Algebraic _ _ _) b@(Rational _) = flipOrd $ compare b a
    where
      flipOrd EQ = EQ
      flipOrd LT = GT
      flipOrd GT = LT
  compare a@(Algebraic _ sf i) b@(Algebraic _ sg j)
    | a == b = EQ
    | otherwise =
    let (i', j') = until (uncurry disjoint) (improveWith sf *** improveWith sg) (i, j)
    in if upper i' <= lower j' then LT else  GT

disjoint :: Ord a => Interval a -> Interval a -> Bool
disjoint i j = upper i < lower j || upper j < lower i

instance Commutative Algebraic
instance Unital Algebraic where
  one = Rational one
instance Semiring Algebraic
instance Abelian Algebraic
instance Rig Algebraic
instance IntegralSemiring Algebraic
instance Division Algebraic where
  recip = recipA

scale :: (Ord r, Multiplicative r, Monoidal r) => r -> Interval r -> Interval r
scale k (Interval l r)
  | k < zero  = Interval (k * r) (k * l)
  | otherwise = Interval (k * l) (k * r)

includes :: Ord a => Interval a -> Interval a -> Bool
Interval i j `includes` Interval i' j' = i <= i' && j' <= j

plusInt :: Group r => Interval r -> Interval r -> Interval r
plusInt (Interval l u) (Interval l' u') = Interval (l + l') (u + u')

rootSumPoly :: Polynomial Rational One -> Polynomial Rational One -> Polynomial Rational One
rootSumPoly f g = normalize $ presultant (liftP f) (substWith (.*.) (injectCoeff varX - varX :- Nil) $ liftP g)
  where
    liftP :: Polynomial Rational One -> Polynomial (Polynomial Rational One) One
    liftP = mapCoeff injectCoeff

sqFreePart :: (DecidableUnits r, Eq r, Domain r, DecidableZero r, Division r, Commutative r, IsMonomialOrder order)
           => OrderedPolynomial r order One -> OrderedPolynomial r order One
sqFreePart f = snd $ head $ f `divPolynomial` [gcd f (diff OZ f)]


plusA :: Algebraic -> Algebraic -> Algebraic
plusA (Rational r) (Rational q) = Rational (r + q)
plusA a@(Algebraic _ _ _) b@(Rational _) = plusA b a
plusA (Rational r) (Algebraic f _ i)  =
  let f' = subst' varX (varX - injectCoeff r) f
  in Algebraic f' (strum f') (Interval (lower i + r) (upper i + r))
plusA a@(Algebraic f sf i0) b@(Algebraic g sg j0)
  | totalDegree' f == 1 && isZero (coeff one f) = Algebraic g sg j0
  | totalDegree' g == 1 && isZero (coeff one g) = Algebraic f sf i0
  | otherwise =
  let !fg = rootSumPoly f g
      iij = catcher plusInt fg a b
  in normA $ Algebraic fg (strum fg) iij

normA :: Algebraic -> Algebraic
normA (Rational a) = Rational a
normA (Algebraic f sf i)
  | substWith (*) (zero :- Nil) f == zero && zero `isIn` i = Rational zero
  | totalDegree' f == 1 = Rational $ negate $ coeff one f / leadingCoeff f
  | otherwise = Algebraic (shiftP f) sf i

isIn :: Ord a => a -> Interval a -> Bool
x `isIn` Interval i j = i < x && x <= j

algebraic :: Polynomial Rational One -> Interval Rational -> Algebraic
algebraic f i = Algebraic f (strum f) i

catcher :: (Interval Rational -> Interval Rational -> Interval Rational)
        -> OrderedPolynomial Rational Grevlex One -> Algebraic -> Algebraic -> Interval Rational
catcher app h (Algebraic _ sf i0) (Algebraic _ sg j0) =
  let lens = map size $ isolateRoots h
      (i', j') = until (\(i,j) -> all (size (app i j) <) lens)
                 (improveWith sf *** improveWith sg)
                 (i0, j0)
  in i' `app` j'
catcher _ _ _ _ = error "rational is impossible"

normalize :: (Eq r, Ring r, DecidableZero r, DecidableUnits r, Division r, Commutative r, IntegralSemiring r, IsMonomialOrder order) => OrderedPolynomial r order One -> OrderedPolynomial r order One
normalize = monoize . sqFreePart

shiftP :: (Domain r, Division r, Eq r, Commutative r, DecidableUnits r,
           DecidableZero r, IsMonomialOrder order)
       => OrderedPolynomial r order One -> OrderedPolynomial r order One
shiftP f | isZero (coeff one f) = f `quot` varX
         | otherwise = f

stabilize :: Algebraic -> Algebraic
stabilize r@(Rational _) = r
stabilize ar@(Algebraic f ss int)
  | lower int * upper int >= 0 = ar
  | otherwise =
    let lh = Interval (lower int) 0
        uh = Interval 0 (upper int)
    in Algebraic f ss $ if countChangeIn lh ss == 0 then uh else lh

rootMultPoly :: Polynomial Rational One -> Polynomial Rational One -> Polynomial Rational One
rootMultPoly f g =
  let ts@((_, lm):_) = getTerms g
      d = totalDegree lm
      g' = sum $  map (\(k, m) -> toPolynomial (injectCoeff k * varX^(P.fromIntegral $ totalDegree m),
                                                (OrderedMonomial $ d - totalDegree m :- Nil)) ) ts
  in normalize $ presultant (liftP f) g'
  where
    liftP :: Polynomial Rational One -> Polynomial (Polynomial Rational One) One
    liftP = mapCoeff injectCoeff

multInt :: (Num a, Ord a, Multiplicative a) => Interval a -> Interval a -> Interval a
multInt i j
  | lower i < 0  && lower j < 0 = Interval (upper i * upper j) (lower i * lower j)
  | lower i >= 0 && lower j < 0 = Interval (upper i * lower j) (lower i * upper j)
  | lower i < 0  && lower j >= 0 = Interval (upper j * lower i) (lower j * upper i)
  | lower i >= 0 && lower j >= 0 = Interval (lower j * lower i) (upper j * upper i)
multInt _ _ = error "multInt"

multA :: Algebraic -> Algebraic -> Algebraic
multA a b =
  let fg = rootMultPoly (eqn a) (eqn b)
      int = catcher multInt fg (stabilize a) (stabilize b)
  in Algebraic fg (strum fg) int

improveNonzero :: Algebraic -> Interval Rational
improveNonzero (Algebraic _ ss int0) = go int0
  where
    go int =
      let (lh, bh) = bisect int
      in if countChangeIn lh ss == 0
         then bh
         else go lh
improveNonzero _ = error "improveNonzero: Rational"

recipInt :: (Num r, Ord r, Division r) => Interval r -> Interval r
recipInt i | lower i < 0 = Interval (recip $ upper i) (recip $ lower i)
           | otherwise   = Interval (recip $ lower i) (recip $ upper i)

recipA :: Algebraic -> Algebraic
recipA a =
  let fi = rootRecipPoly (eqn a)
      sf = strum fi
      i0 = improveNonzero a
      lens = map size $ isolateRoots fi
      i'    = until (\i -> any (> size (recipInt i)) lens) (improveWith sf) i0
  in Algebraic fi (strum fi) $ recipInt i'

rootRecipPoly :: Polynomial Rational One -> Polynomial Rational One
rootRecipPoly f =
  let ts@((_, lm):_) = getTerms f
      d = totalDegree lm
      f' = sum $  map (\(k, m) -> toPolynomial (k, OrderedMonomial $ d - totalDegree m :- Nil) ) ts
  in normalize f'

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
improve (Algebraic f ss int) = Algebraic f ss $ improveWith ss int
improve a = a

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
