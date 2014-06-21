{-# LANGUAGE BangPatterns, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction           #-}
module Main where
import           Algebra.Algorithms.Groebner
import           Algebra.Prelude             hiding (normalize)
import           Control.Arrow               ((***))
import           Data.List                   (sortBy)
import           Data.Ord                    (comparing)
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
                           , strumseq :: [Polynomial Rational One]
                           , interval :: Interval Rational
                           } deriving (Show)

instance Additive Algebraic where
  (+) = plusA

instance Group Algebraic where
  negate r = (-1 :: Integer) .* r

instance Monoidal Algebraic where
  zero = Algebraic varX [varX, one] (Interval 0 0)

instance LeftModule Natural Algebraic where
  (.*) n = (.*) $ P.toInteger n

instance RightModule Natural Algebraic where
  (*.) = flip (.*)

instance LeftModule Integer Algebraic where
  n .* Algebraic f _ int
   | n == 0 = zero
   | otherwise = let f' = (subst' varX (injectCoeff (1 %% n) * varX) f)
                 in Algebraic f' (strum f') (scale (n %% 1) int)

instance LeftModule (Fraction Integer) Algebraic where
  q .* Algebraic f _ int
   | isZero q  = Algebraic varX [varX, one] (Interval 0 0)
   | otherwise = let f' = subst' varX (injectCoeff (recip q) * varX) f
                 in Algebraic f' (strum f') (scale q int)

instance RightModule Integer Algebraic where
  (*.) = flip (.*)

instance RightModule (Fraction Integer) Algebraic where
  (*.) = flip (.*)

instance Multiplicative Algebraic where
  (*) = multA

instance Eq Algebraic where
  Algebraic f _ i == Algebraic g _ j
    | not $ isZero $ resultant f g = False
    | otherwise =
        let sh = strum $ gcd f g
        in countChangeIn (i `intersect` j) sh == 1

intersect :: (Num a, Ord a) => Interval a -> Interval a -> Interval a
intersect i j | disjoint i j = Interval 0 0
              | lower i <= lower j = Interval (lower j) (upper i)
              | lower j >  lower i = Interval (lower i) (upper j)
intersect _ _ = error "intersect"

instance Ord Algebraic where
  compare a@(Algebraic f sf i) b@(Algebraic g sg j)
    | a == b = EQ
    | otherwise =
    let (i', j') = until (uncurry disjoint) (improveWith sf *** improveWith sg) (i, j)
    in if upper i' <= lower j' then LT else  GT

disjoint :: Ord a => Interval a -> Interval a -> Bool
disjoint i j = upper i < lower j || upper j < lower i

instance Commutative Algebraic
instance Unital Algebraic where
  one = Algebraic (varX - one) [varX - one, one] (Interval (2/1) (3/2))
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
plusA a@(Algebraic f sf i0) b@(Algebraic g sg j0)
  | totalDegree' f == 1 && isZero (coeff one f) = Algebraic g sg j0
  | totalDegree' g == 1 && isZero (coeff one g) = Algebraic f sf i0
  | otherwise =
  let !fg = rootSumPoly f g
      iij = catcher plusInt fg a b
  in normA $ Algebraic fg (strum fg) iij

normA :: Algebraic -> Algebraic
normA (Algebraic f sf i)
  | substWith (*) (zero :- Nil) f == zero && zero `isIn` i = Algebraic varX [varX, 1] (Interval zero zero)
  | otherwise = Algebraic (shiftP f) sf i

isIn :: Ord a => a -> Interval a -> Bool
x `isIn` Interval i j = i < x && x <= j

catcher :: (Interval Rational -> Interval Rational -> Interval Rational)
        -> OrderedPolynomial Rational Grevlex One -> Algebraic -> Algebraic -> Interval Rational
catcher app h (Algebraic f sf i0) (Algebraic g sg j0) =
  let lens = map size $ isolateRoots h
      (i', j') = until (\(i,j) -> all (size (app i j) <) lens)
                 (improveWith sf *** improveWith sg)
                 (i0, j0)
  in i' `app` j'

normalize :: (Eq r, Ring r, DecidableZero r, DecidableUnits r, Division r, Commutative r, IntegralSemiring r, IsMonomialOrder order) => OrderedPolynomial r order One -> OrderedPolynomial r order One
normalize = monoize . sqFreePart

shiftP :: (Domain r, Division r, Eq r, Commutative r, DecidableUnits r,
           DecidableZero r, IsMonomialOrder order)
       => OrderedPolynomial r order One -> OrderedPolynomial r order One
shiftP f | isZero (coeff one f) = f `quot` varX
         | otherwise = f

stabilize :: Algebraic -> Algebraic
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
improveNonzero (Algebraic f ss int0) = go int0
  where
    go int =
      let (lh, bh) = bisect int
      in if countChangeIn lh ss == 0
         then bh
         else go lh

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
