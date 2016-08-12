{-# LANGUAGE BangPatterns, DataKinds, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, NoImplicitPrelude              #-}
{-# LANGUAGE NoMonomorphismRestriction                                    #-}
module Main where
import           Algebra.Algorithms.Groebner
import           Algebra.Prelude                    hiding (intersect,
                                                     normalize)
import           Algebra.Ring.Polynomial.Univariate
import           Control.Arrow                      ((***))
import           Control.Lens                       (ifoldMap, ix, (*~),
                                                     _Wrapped)
import           Control.Monad.Random               (StdGen, newStdGen)
import           Control.Monad.Random               (random)
import           Control.Monad.Random               (Random)
import           Control.Monad.Random               (split)
import           Control.Monad.Random               (evalRand)
import           Control.Monad.Random               (Rand)
import qualified Data.Coerce                        as C
import           Data.IORef                         (IORef, atomicModifyIORef')
import           Data.IORef                         (newIORef)
import qualified Data.Ratio                         as R
import           Data.Tuple                         (swap)
import           GHC.Num                            (Num)
import           Math.NumberTheory.Powers
import           Numeric.Decidable.Zero             (isZero)
import           Numeric.Domain.GCD                 (gcd)
import qualified Numeric.Field.Fraction             as F
import           Numeric.Semiring.ZeroProduct       (ZeroProductSemiring)
import qualified Prelude                            as P
import           System.IO.Unsafe                   (unsafePerformIO)

randSrc :: IORef StdGen
randSrc = unsafePerformIO $ newIORef =<< newStdGen
{-# NOINLINE randSrc #-}

getRand :: Random a => IO a
getRand = atomicModifyIORef' randSrc (swap . random)
{-# INLINE getRand #-}

splitSrc :: IO StdGen
splitSrc = atomicModifyIORef' randSrc (swap . split)
{-# INLINE splitSrc #-}

doRand :: Rand StdGen b -> IO b
doRand act = do
  g <- splitSrc
  return $ evalRand act g

-- Invariants:
--   (1) eqn is square-free and does not have x as a factor
--   (2) strumseq is the standard strum sequence of eqn
--   (3) interval contains exactly one root of eqn
data Algebraic = Algebraic { eqn      :: Unipol Rational
                           , strumseq :: [Unipol Rational]
                           , interval :: Interval Rational
                           }
               | Rational !Rational
                 deriving (Show)

instance Additive Algebraic where
  (+) = plusA
  {-# INLINE (+) #-}

instance Group Algebraic where
  negate r = (-1 :: Integer) .* r
  {-# INLINE negate #-}

instance Monoidal Algebraic where
  zero = Rational zero
  {-# INLINE zero #-}

instance LeftModule Natural Algebraic where
  (.*) = (.*) . P.toInteger
  {-# INLINE (.*) #-}

instance RightModule Natural Algebraic where
  (*.) = flip (.*)
  {-# INLINE (*.) #-}

instance LeftModule Integer Algebraic where
  n .* Rational r = Rational (n .* r)
  n .* Algebraic f fs int
   | n == 0 = zero
   | otherwise =
      let factor = liftMap (const $ injectCoeff (1 F.% n) * var 0)
      in Algebraic (factor f) (map factor fs) (scale (n F.% 1) int)
  {-# INLINE (.*) #-}

instance LeftModule (Fraction Integer) Algebraic where
  q .* Rational r = Rational (q * r)
  q .* a = Rational q * a
  {-# INLINE (.*) #-}

instance RightModule Integer Algebraic where
  (*.) = flip (.*)

instance RightModule (Fraction Integer) Algebraic where
  (*.) = flip (.*)

instance Multiplicative Algebraic where
  (*) = multA

instance Eq Algebraic where
  Rational p      == Algebraic g _ j =
    isZero (runScalar $ liftMap (const $ Scalar p) g) && p `isIn` j
  Algebraic g _ j == Rational p =
    isZero (runScalar $ liftMap (const $ Scalar p) g) && p `isIn` j
  Rational p      == Rational q = p == q
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
  compare (Rational q) (Rational r) = compare q r
  compare (Rational q) (Algebraic f sf i) =
    let i' = until (not . (q `isIn`)) (improveWith sf) i
    in if q <= lower i'
       then LT
       else if isZero (f `modPolynomial` [var 0 - injectCoeff q])
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
instance Ring Algebraic
instance ZeroProductSemiring Algebraic
instance Division Algebraic where
  recip = recipA
instance DecidableZero Algebraic where
  isZero a = a == Rational 0

instance DecidableUnits Algebraic where
  isUnit r = r /= 0
  recipUnit r =
    if r == 0
    then Nothing
    else Just $ recipA r

instance DecidableAssociates Algebraic where
  isAssociate r r' =
    (isZero r && isZero r') || (not (isZero r) && not (isZero r'))

instance UnitNormalForm Algebraic where
  splitUnit x =
    if x == 0
    then (0, Rational 1)
    else if x < 0
         then (Rational (-1), negate x)
         else (Rational 1, x)

instance P.Num Algebraic where
  (+) = C.coerce ((P.+) :: WrapAlgebra Algebraic -> WrapAlgebra Algebraic -> WrapAlgebra Algebraic)
  {-# INLINE (+) #-}

  (-) = C.coerce ((P.-) :: WrapAlgebra Algebraic -> WrapAlgebra Algebraic -> WrapAlgebra Algebraic)
  {-# INLINE (-) #-}

  (*) = C.coerce ((P.*) :: WrapAlgebra Algebraic -> WrapAlgebra Algebraic -> WrapAlgebra Algebraic)
  {-# INLINE (*) #-}

  abs = C.coerce (P.abs :: WrapAlgebra Algebraic -> WrapAlgebra Algebraic)
  {-# INLINE abs #-}

  signum = C.coerce (P.signum :: WrapAlgebra Algebraic -> WrapAlgebra Algebraic)
  {-# INLINE signum #-}

  negate = C.coerce (P.negate :: WrapAlgebra Algebraic -> WrapAlgebra Algebraic)
  {-# INLINE negate #-}

  fromInteger = C.coerce (P.fromInteger :: Integer -> WrapAlgebra Algebraic)
  {-# INLINE fromInteger #-}

instance P.Fractional Algebraic where
  recip = recipA
  {-# INLINE recip #-}

  fromRational r = Rational (R.numerator r F.% R.denominator r)
  {-# INLINE fromRational #-}


scale :: (Ord r, Multiplicative r, Monoidal r) => r -> Interval r -> Interval r
scale k (Interval l r)
  | k < zero  = Interval (k * r) (k * l)
  | otherwise = Interval (k * l) (k * r)

includes :: Ord a => Interval a -> Interval a -> Bool
Interval i j `includes` Interval i' j' = i <= i' && j' <= j

plusInt :: Group r => Interval r -> Interval r -> Interval r
plusInt (Interval l u) (Interval l' u') = Interval (l + l') (u + u')

rootSumPoly :: Unipol Rational -> Unipol Rational -> Unipol Rational
rootSumPoly f g =
  normalize $ presultant (liftP f) $
  liftMap (const $ injectCoeff (var 0) - var 0) $ liftP g
  where
    liftP :: Unipol Rational -> Unipol (Unipol Rational)
    liftP = mapCoeffUnipol injectCoeff

sqFreePart :: (Eq r, Euclidean r, Division r)
           => Unipol r -> Unipol r
sqFreePart f = f `quot` gcd f (diff 0 f)

plusA :: Algebraic -> Algebraic -> Algebraic
plusA (Rational r) (Rational q) = Rational (r + q)
plusA a@(Algebraic _ _ _) b@(Rational _) = plusA b a
plusA (Rational r) (Algebraic f _ i)  =
  let f' = liftMap (const $ var 0 - injectCoeff r) f
  in Algebraic f' (strum f') (Interval (lower i + r) (upper i + r))
plusA a@(Algebraic f sf i0) b@(Algebraic g sg j0)
  | totalDegree' f == 1 && isZero (constantTerm f) = Algebraic g sg j0
  | totalDegree' g == 1 && isZero (constantTerm g) = Algebraic f sf i0
  | otherwise =
  let !fg = rootSumPoly f g
      iij = catcher plusInt fg a b
  in normA $ Algebraic fg (strum fg) iij

normA :: Algebraic -> Algebraic
normA (Rational a) = Rational a
normA (Algebraic f sf i)
  | isZero (constantTerm f) && zero `isIn` i = Rational zero
  | totalDegree' f == 1 = Rational $ negate $ coeff one f / leadingCoeff f
  | otherwise = Algebraic (shiftP f) sf i

isIn :: Ord a => a -> Interval a -> Bool
x `isIn` Interval i j = i < x && x <= j

algebraic :: Unipol Rational -> Interval Rational -> Algebraic
algebraic f i = Algebraic f (strum f) i

catcher :: (Interval Rational -> Interval Rational -> Interval Rational)
        -> Unipol Rational -> Algebraic -> Algebraic -> Interval Rational
catcher app h (Algebraic _ sf i0) (Algebraic _ sg j0) =
  let lens = map size $ isolateRoots h
      (i', j') = until (\(i,j) -> all (size (app i j) <) lens)
                 (improveWith sf *** improveWith sg)
                 (i0, j0)
  in i' `app` j'
catcher _ _ _ _ = error "rational is impossible"

normalize :: (Eq r, Euclidean r, Division r) => Unipol r -> Unipol r
normalize = monoize . sqFreePart

shiftP :: (Domain r, Division r, Eq r, Euclidean r)
       => Unipol r -> Unipol r
shiftP f | isZero (coeff one f) = f `quot` var 0
         | otherwise = f

stabilize :: Algebraic -> Algebraic
stabilize r@(Rational _) = r
stabilize ar@(Algebraic f ss int)
  | lower int * upper int >= 0 = ar
  | otherwise =
    let lh = Interval (lower int) 0
        uh = Interval 0 (upper int)
    in Algebraic f ss $ if countChangeIn lh ss == 0 then uh else lh

nthRoot :: Int -> Algebraic -> Maybe Algebraic
nthRoot 1 a = Just a
nthRoot n a
  | n < 0  = recipA <$> nthRoot (abs n) a
  | n == 0 = Nothing
  | even n && a < 0 = Nothing
  | otherwise =
    case a of
      Rational p ->
        Just $ either Rational (algebraic (var 0 ^ fromIntegral n - injectCoeff p)) $ nthRootRat n p
      Algebraic f _ range ->
        Just $ algebraic (mapMonomialMonotonic (_Wrapped.ix 0 *~ 2) f) (nthRootInterval n range)

nthRootRat :: Int -> Rational -> Either Rational (Interval Rational)
nthRootRat 1 r = Left r
nthRootRat 2 r =
  let (p, q) = (F.numerator r, F.denominator r)
      (isp, isq) = (integerSquareRoot p, integerSquareRoot q)
  in case  (exactSquareRoot p, exactSquareRoot q) of
    (Just p', Just q')  -> Left (p' F.% q')
    (mp', mq') -> Right $
                  Interval (fromMaybe isp mp' F.% fromMaybe (isq+1) mq')
                           (fromMaybe (isp+1) mp' F.% fromMaybe isq mq')
nthRootRat 3 r =
  let (p, q) = (F.numerator r, F.denominator r)
      (isp, isq) = (integerCubeRoot p, integerCubeRoot q)
  in case  (exactCubeRoot p, exactCubeRoot q) of
    (Just p', Just q')  -> Left (p' F.% q')
    (mp', mq') -> Right $
                  Interval (fromMaybe isp mp' F.% fromMaybe (isq+1) mq')
                           (fromMaybe (isp+1) mp' F.% fromMaybe isq mq')
nthRootRat 4 r =
  let (p, q) = (F.numerator r, F.denominator r)
      (isp, isq) = (integerFourthRoot p, integerFourthRoot q)
  in case  (exactFourthRoot p, exactFourthRoot q) of
    (Just p', Just q')  -> Left (p' F.% q')
    (mp', mq') -> Right $
                  Interval (fromMaybe isp mp' F.% fromMaybe (isq+1) mq')
                           (fromMaybe (isp+1) mp' F.% fromMaybe isq mq')
nthRootRat n r =
  let (p, q) = (F.numerator r, F.denominator r)
      (isp, isq) = (integerRoot n p, integerRoot n q)
  in case  (exactRoot n p, exactRoot n q) of
    (Just p', Just q')  -> Left (p' F.% q')
    (mp', mq') -> Right $
                  Interval (fromMaybe isp mp' F.% fromMaybe (isq+1) mq')
                           (fromMaybe (isp+1) mp' F.% fromMaybe isq mq')

nthRootRatCeil :: Int -> Rational -> Rational
nthRootRatCeil 1 r = r
nthRootRatCeil 2 r =
  let p = integerSquareRoot (F.numerator r) + 1
      q = integerSquareRoot (F.denominator r)
  in p F.% q
nthRootRatCeil 3 r =
  let p = integerCubeRoot (F.numerator r) + 1
      q = integerCubeRoot (F.denominator r)
  in p F.% q
nthRootRatCeil 4 r =
  let p = integerFourthRoot (F.numerator r) + 1
      q = integerFourthRoot (F.denominator r)
  in p F.% q
nthRootRatCeil n r =
  let p = integerRoot n (F.numerator r) + 1
      q = integerRoot n (F.denominator r)
  in p F.% q

nthRootRatFloor :: Int -> Rational -> Rational
nthRootRatFloor 1 r = r
nthRootRatFloor 2 r =
  let p = integerSquareRoot (F.numerator r)
      q = integerSquareRoot (F.denominator r) + 1
  in p F.% q
nthRootRatFloor 3 r =
  let p = integerCubeRoot (F.numerator r)
      q = integerCubeRoot (F.denominator r) + 1
  in p F.% q
nthRootRatFloor 4 r =
  let p = integerFourthRoot (F.numerator r)
      q = integerFourthRoot (F.denominator r) + 1
  in p F.% q
nthRootRatFloor n r =
  let p = integerRoot n (F.numerator r)
      q = integerRoot n (F.denominator r) + 1
  in p F.% q

nthRootInterval :: Int -> Interval Rational -> Interval Rational
nthRootInterval 0 _ = error "0-th root????????"
nthRootInterval 1 i = i
nthRootInterval n (Interval lb ub)
  | n < 0 = recipInt $ Interval (nthRootRatFloor (abs n) lb) (nthRootRatCeil (abs n) ub)
  | otherwise = Interval (nthRootRatFloor n lb) (nthRootRatCeil n ub)

rootMultPoly :: Unipol Rational -> Unipol Rational -> Unipol Rational
rootMultPoly f g =
  let ts = terms' g
      d = fromIntegral $ totalDegree' g
      g' = runAdd $ ifoldMap (\m k -> Add $ toPolynomial (injectCoeff k * var 0^(P.fromIntegral $ sum m),
                                                          (OrderedMonomial $ singleton $ d - sum m)) ) ts
  in normalize $ presultant (liftP f) g'
  where
    liftP :: Unipol Rational -> Unipol (Unipol Rational)
    liftP = mapCoeffUnipol injectCoeff

multInt :: (Num a, Ord a, Multiplicative a) => Interval a -> Interval a -> Interval a
multInt i j
  | lower i < 0  && lower j < 0 = Interval (upper i * upper j) (lower i * lower j)
  | lower i >= 0 && lower j < 0 = Interval (upper i * lower j) (lower i * upper j)
  | lower i < 0  && lower j >= 0 = Interval (upper j * lower i) (lower j * upper i)
  | lower i >= 0 && lower j >= 0 = Interval (lower j * lower i) (upper j * upper i)
multInt _ _ = error "multInt"

multA :: Algebraic -> Algebraic -> Algebraic
multA (Rational 0) _ = Rational 0
multA _ (Rational 0) = Rational 0
multA (Rational a) (Rational b) = Rational (a * b)
multA a@Rational{} b@Algebraic{} = multA b a
multA (Algebraic f sf i) (Rational a) =
  let factor = liftMap (const $ recip a .*. var 0)
  in Algebraic (factor f) (map factor sf) (scale a i)
multA a b =
  let fg = rootMultPoly (eqn a) (eqn b)
      int = catcher multInt fg (stabilize a) (stabilize b)
  in Algebraic fg (strum fg) int

defEqn :: Algebraic -> Unipol Rational
defEqn (Rational a) = var 0 - injectCoeff a
defEqn a@Algebraic{} = eqn a

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
recipA (Rational a) = Rational (recip a)
recipA a@Algebraic{} =
  let fi = rootRecipPoly (eqn a)
      sf = strum fi
      i0 = improveNonzero a
      ls = map size $ isolateRoots fi
      i' = until (\i -> any (> size (recipInt i)) ls) (improveWith sf) i0
  in Algebraic fi (strum fi) $ recipInt i'

rootRecipPoly :: Unipol Rational -> Unipol Rational
rootRecipPoly f =
  let ts = terms' f
      d = fromIntegral $ totalDegree' f
      f' = runAdd $ ifoldMap (\m k -> Add $ toPolynomial
                                      (k, OrderedMonomial $ singleton $ d - sum m) ) ts
  in normalize f'

strum :: Unipol Rational -> [Unipol Rational]
strum f = zipWith (*) (cycle [1,1,-1,-1]) $
          map (\(p,_,_) -> p * injectCoeff (recip $ abs (leadingCoeff p))) $
          reverse $ prs f (diff 0 f)

data Interval r = Interval { lower :: !r, upper :: !r } deriving (Eq, Ord)

size :: Group r => Interval r -> r
size (Interval l r) = r - l

instance Show r => Show (Interval r) where
  showsPrec _ (Interval l u) = showChar '(' . showsPrec 5 l . showString ", " . showsPrec 5 u . showChar ']'

bisect :: (Ring r, Division r) => Interval r -> (Interval r, Interval r)
bisect (Interval l u) =
  let mid = (l+u) / fromInteger' 2
  in (Interval l mid, Interval mid u)

signChange :: (Ord a, Ring a, DecidableZero a) => [a] -> Int
signChange xs =
  let nzs = filter (not . isZero) xs
  in length $ filter (< zero) $ zipWith (*) nzs (tail nzs)

countRootsIn :: Unipol Rational -> Interval Rational -> Int
countRootsIn f ints = countChangeIn ints (strum f)

countChangeIn :: (Ord a, CoeffRing a)
                 => Interval a -> [Unipol a] -> Int
countChangeIn ints ss =
  signChangeAt (lower ints) ss - signChangeAt (upper ints) ss

signChangeAt :: (Ord a, CoeffRing a) => a -> [Unipol a] -> Int
signChangeAt a fs = signChange $ map (runScalar . liftMap (const $ Scalar a)) fs

rootBound :: (Num r, Ord r, CoeffRing r, Division r, UnitNormalForm r)
          => Unipol r -> r
rootBound f
  | totalDegree' f == 0 = 0
  | otherwise =
    let a = leadingCoeff f
    in 1 + maximum (map (normaliseUnit . (/ a)) $ terms' f)

isolateRoots :: Unipol Rational -> [Interval Rational]
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

improveWith :: (Ord a, CoeffRing a, Division a)
            => [Unipol a] -> Interval a -> Interval a
improveWith ss int =
  let (ls, us) = bisect int
  in if countChangeIn ls ss == 0 then us else ls

iterateImprove :: Rational -> Unipol Rational -> Interval Rational -> Interval Rational
iterateImprove eps f =
  iterateImproveStrum eps (strum f)

iterateImproveStrum :: Rational -> [Unipol Rational] -> Interval Rational -> Interval Rational
iterateImproveStrum eps ss int0 =
  until (\int -> size int < eps) (improveWith ss) int0

fromFraction :: P.Fractional a => Fraction Integer -> a
fromFraction q = P.fromInteger (numerator q) P./ P.fromInteger (denominator q)

sample :: (Num r, Division r, Additive r) => Interval r -> r
sample (Interval l r) = (l+r)/2

presultant :: (Euclidean k, CoeffRing k)
           => Unipol k -> Unipol k -> k
presultant = go one one
  where
    go !res !acc h s
        | totalDegree' s > 0     =
          let (_, r)    = h `pDivModPoly` s
              res' = res * pow (negate one)
                           (P.fromIntegral $ totalDegree' h * totalDegree' s :: Natural)
                     * pow (leadingCoeff s) (P.fromIntegral $ totalDegree' h P.- totalDegree' r :: Natural)
              adj = pow (leadingCoeff s) (P.fromIntegral $ max 0 (1 + totalDegree' h P.- totalDegree' s  :: Natural))
          in go res' (acc * adj) s r
        | isZero h || isZero s = zero
        | totalDegree' h > 0     = pow (leadingCoeff s) (P.fromIntegral $ totalDegree' h :: Natural) * res `quot` acc
        | otherwise              = res `quot` acc

main :: IO ()
main = return ()

representative :: (Additive r, Division r, Num r) => Interval r -> r
representative (Interval l r) = (l + r) / 2

approximate :: Rational -> Algebraic -> Rational
approximate _   (Rational a) = a
approximate err (Algebraic _ ss int) =
  representative $ iterateImproveStrum err ss int
