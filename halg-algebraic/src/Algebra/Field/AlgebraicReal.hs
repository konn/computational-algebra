{-# LANGUAGE BangPatterns, DataKinds, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, NoImplicitPrelude              #-}
{-# LANGUAGE NoMonomorphismRestriction, OverloadedLabels                  #-}
-- | Algebraic Real Numbers for exact computation
--
--   Since 0.4.0.0
module Algebra.Field.AlgebraicReal
       ( Algebraic, algebraic,
         -- * Operations
         nthRoot, nthRoot',
         improve,
         approximate, approxFractional,
         -- * Equation solver
         realRoots, complexRoots,
         -- * Interval arithmetic
         Interval(..), representative,
         includes, intersect,
         -- * Internal utility functions
         strum, presultant, factors,
         realPartPoly,imagPartPoly, sqFreePart
       )
       where
import           Algebra.Prelude.Core               hiding (intersect,
                                                     normalize)
import           Algebra.Ring.Polynomial.Factorise  (clearDenom, factorHensel)
import           Algebra.Ring.Polynomial.Univariate
import           Control.Arrow                      ((***))
import           Control.Lens                       (each, ifoldMap, ix, (%~),
                                                     (&), (*~), _Wrapped)
import           Control.Monad.Random
import           Data.Bits
import qualified Data.Coerce                        as C
import qualified Data.IntMap                        as IM
import           Data.Maybe                         (fromJust)
import           Data.MonoTraversable
import qualified Data.Ratio                         as R
import qualified Data.Set                           as S
import qualified Data.Sized.Builtin                 as SV
import           GHC.Num                            (Num)
import           Math.NumberTheory.Powers
import           Numeric.Algebra.Complex            hiding (i)
import           Numeric.Decidable.Zero             (isZero)
import           Numeric.Domain.GCD                 (gcd)
import qualified Numeric.Field.Fraction             as F
import           Numeric.Semiring.ZeroProduct       (ZeroProductSemiring)
import qualified Prelude                            as P
import           System.Entropy                     (getEntropy)
import           System.IO.Unsafe                   (unsafePerformIO)

stdGenFromEntropy :: IO StdGen
stdGenFromEntropy = mkStdGen . ofoldr (\a -> (+) (fromEnum a) . (`shiftL` 8)) 0 <$>  getEntropy 8
{-# INLINE stdGenFromEntropy #-}

factors :: Unipol Rational -> [Unipol Rational]
factors f =
  let (a, p) = clearDenom f
  in concatMap (map (monoize . mapCoeffUnipol (F.%a)) . S.toList . snd) $
     IM.toList $ snd
         $ flip evalRand (unsafePerformIO stdGenFromEntropy)
         $ factorHensel p

-- | Algebraic real numbers, which can be expressed as a root
--   of a rational polynomial.
data Algebraic = Algebraic { eqn      :: Unipol Rational
                           , _strumseq :: [Unipol Rational]
                           , _interval :: Interval Rational
                           }
               | Rational !Rational
                 -- deriving (Show)
-- Invariants for constructor Algebraic:
--   (1) eqn must be monic and irreducible polynomial with degree > 1.
--   (2) strumseq is the standard strum sequence of eqn
--   (3) interval contains exactly one root of eqn

viewNthRoot :: Algebraic -> Maybe (Int, Rational)
viewNthRoot (Algebraic eq _ _) =
  let (lc, lm) = leadingTerm eq
  in if totalDegree' (eq - toPolynomial (lc, lm)) == 0
     then Just (getMonomial lm SV.%!! 0, negate $ constantTerm eq)
     else Nothing
viewNthRoot _ = Nothing

showsNthRoot ::  Int -> Rational -> ShowS
showsNthRoot  1 q = showsPrec 6 q
showsNthRoot  2 q = showChar '√' . showsPrec 6 q
showsNthRoot  n q = showsPrec 6 q . showString "^(1/" . shows n . showChar ')'


instance Show Algebraic where
  showsPrec d (Rational q) = showsPrec d q
  showsPrec d a@(Algebraic eq str int) = showParen (d > 11) $
    case viewNthRoot a of
      Nothing ->
        showString "Algebraic " . showsPrec 7 eq . showChar ' '
        . showsPrec 7 str . showChar ' '
        . showsPrec 7 int
      Just (nth, q)
        | a < 0     -> showParen (5 < d && d <= 11) $
                       showString "-" . showsNthRoot nth q
        | otherwise -> showsNthRoot nth q


negateA :: Algebraic -> Algebraic
negateA r = (-1 :: Integer) .* r
{-# INLINE [1] negateA #-}

minusA :: Algebraic -> Algebraic -> Algebraic
minusA a b = plusA a (negateA b)
{-# INLINE [1] minusA #-}

instance Additive Algebraic where
  (+) = plusA
  {-# INLINE (+) #-}

instance Group Algebraic where
  negate = negateA
  {-# INLINE negate #-}
  (-) = minusA
  {-# INLINE (-) #-}


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
  (.*) = multA . Rational . fromIntegral
  {-# INLINE (.*) #-}

instance LeftModule (Fraction Integer) Algebraic where
  (.*) = multA . Rational
  {-# INLINE (.*) #-}

instance RightModule Integer Algebraic where
  (*.) = flip (.*)
  {-# INLINE (*.) #-}

instance RightModule (Fraction Integer) Algebraic where
  (*.) = flip (.*)
  {-# INLINE (*.) #-}

instance Multiplicative Algebraic where
  (*) = multA
  {-# INLINE (*) #-}
  pow1p a = powA a . succ
  {-# INLINE pow1p #-}

instance LeftModule (Scalar (Fraction Integer)) Algebraic where
  (.*) = multA . Rational . runScalar
  {-# INLINE (.*) #-}

instance RightModule (Scalar (Fraction Integer)) Algebraic where
  (*.) = flip (.*)
  {-# INLINE (*.) #-}

instance Eq Algebraic where
  Rational p      == Algebraic g _ j =
    isZero (runScalar $ liftMap (const $ Scalar p) g) && p `isIn` j
  Algebraic g _ j == Rational p =
    isZero (runScalar $ liftMap (const $ Scalar p) g) && p `isIn` j
  Rational p      == Rational q = p == q
  Algebraic f ss i == Algebraic g _ j
    = monoize f ==  monoize g && countChangeIn (i `intersect` j) ss == 1

-- | Takes intersection of two intervals.
intersect :: (Monoidal a, Ord a) => Interval a -> Interval a -> Interval a
intersect i j | disjoint i j = Interval zero zero
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
  one = Rational 1
  {-# INLINE one #-}

instance Semiring Algebraic
instance Abelian Algebraic
instance Rig Algebraic
instance Ring Algebraic
instance ZeroProductSemiring Algebraic
instance Division Algebraic where
  recip = recipA
  {-# INLINE recip #-}

instance DecidableZero Algebraic where
  isZero (Rational 0) = True
  isZero _ = False
  {-# INLINE isZero #-}

instance DecidableUnits Algebraic where
  isUnit (Rational 0) = False
  isUnit _ = True
  {-# INLINE isUnit #-}

  recipUnit (Rational 0) = Nothing
  recipUnit r = Just $ recipA r

instance DecidableAssociates Algebraic where
  isAssociate (Rational 0) (Rational 0) = True
  isAssociate Algebraic{}  Algebraic{}  = True
  isAssociate _            _            = False
  {-# INLINE isAssociate #-}

instance UnitNormalForm Algebraic where
  splitUnit x =
    if x == 0
    then (0, Rational 1)
    else if x < 0
         then (Rational (-1), negate x)
         else (Rational 1, x)
  {-# INLINE splitUnit #-}

instance P.Num Algebraic where
  (+) = plusA
  {-# INLINE (+) #-}

  (-) = minusA
  {-# INLINE (-) #-}

  (*) = multA
  {-# INLINE (*) #-}

  abs = C.coerce (P.abs :: WrapAlgebra Algebraic -> WrapAlgebra Algebraic)
  {-# INLINE abs #-}

  signum = C.coerce (P.signum :: WrapAlgebra Algebraic -> WrapAlgebra Algebraic)
  {-# INLINE signum #-}

  negate = negateA
  {-# INLINE negate #-}

  fromInteger = Rational . fromInteger
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

-- | Test if the former interval includes the latter.
includes :: Ord a => Interval a -> Interval a -> Bool
Interval i j `includes` Interval i' j' = i <= i' && j' <= j
{-# INLINE includes #-}

instance Group r => Additive (Interval r) where
  (+) = plusInt
  {-# INLINE (+) #-}

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

{-# RULES
"minus-cancel" [~1] forall x.
  minusA x x = Rational 0
"plusminus/right" [~1] forall x (y :: Algebraic) .
  minusA (plusA x y) y = x
"plusminus/left" [~1] forall x (y :: Algebraic) .
  minusA (plusA x y) x = y
"plusminus/left" [~1] forall x (y :: Algebraic) .
  plusA x (minusA y x) = y
  #-}

plusA :: Algebraic -> Algebraic -> Algebraic
plusA (Rational r) (Rational q) = Rational (r + q)
plusA a@(Algebraic _ _ _) b@(Rational _) = plusA b a
plusA (Rational r) (Algebraic f _ i)  =
  let f' = liftMap (const $ var 0 - injectCoeff r) f
  in fromJust $ algebraic f' (Interval (lower i + r) (upper i + r))
plusA a@(Algebraic f _ _) b@(Algebraic g _ _) =
  let fg = rootSumPoly f g
      iij = catcher plusInt fg a b
  in fromJust $ algebraic fg iij
{-# INLINE [1] plusA #-}

isIn :: Ord a => a -> Interval a -> Bool
x `isIn` Interval i j = i < x && x <= j

-- | Smart constructor.
--   @'algebraic' f i@ represents the unique root of
--   rational polynomial @f@ in the interval @i@.
--   If no root is found, or more than one root belongs to
--   the given interval, returns @'Nothing'@.
algebraic :: Unipol Rational -> Interval Rational -> Maybe Algebraic
algebraic f i =
  let pss = [ (n, p, ss)
            | p <- factors $ sqFreePart f
            , let (n, ss) = countRootsIn p i
            , n > 0
            ]
  in case pss of
    [(1, p, ss)] ->
      Just $
      if totalDegree' p == 1
      then Rational $ negate $ constantTerm p
      else Algebraic p ss i
    _ -> Nothing

algebraic' :: Unipol Rational -> Interval Rational -> Algebraic
algebraic' p i =
  if totalDegree' p == 1
  then Rational $ negate $ constantTerm p
  else Algebraic p (strum p) i

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

stabilize :: Algebraic -> Algebraic
stabilize r@Rational{} = r
stabilize ar@(Algebraic f ss int)
  | lower int * upper int >= 0 = ar
  | otherwise =
    let lh = Interval (lower int) 0
        uh = Interval 0 (upper int)
    in Algebraic f ss $ if countChangeIn lh ss == 0 then uh else lh

-- | Unsafe version of @'nthRoot'@.
nthRoot' :: Int -> Algebraic -> Algebraic
nthRoot' n = fromJust . nthRoot n

-- | @nthRoot n r@ tries to computes n-th root of
--   the given algebraic real @r@.
--   It returns @'Nothing'@ if it's undefined.
--
--   See also @'nthRoot''@.
nthRoot :: Int -> Algebraic -> Maybe Algebraic
nthRoot 1 a = Just a
nthRoot n a
  | n < 0  = recipA <$> nthRoot (abs n) a
  | n == 0 = Nothing
  | even n && a < 0 = Nothing
  | otherwise =
    case a of
      Rational p ->
        either
          (Just . Rational)
          (algebraic (var 0 ^ fromIntegral n - injectCoeff p)) $
          nthRootRat n p
      Algebraic f _ range ->
         algebraic (mapMonomialMonotonic (_Wrapped.ix 0 *~ 2) f) (nthRootInterval n range)

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
  let ts = terms g
      d = totalDegree' g
      g' = runAdd $ ifoldMap loop ts
      loop m k =
        let deg = totalDegree m
        in Add $ toPolynomial (injectCoeff k * #x ^ P.fromIntegral deg,
                                OrderedMonomial $ singleton $ d - deg)
  in presultant (liftP f) g'
  where
    liftP :: Unipol Rational -> Unipol (Unipol Rational)
    liftP = mapCoeffUnipol injectCoeff

instance (Ord r, Multiplicative r, Monoidal r) => Multiplicative (Interval r) where
  (*) = multInt
  {-# INLINE (*) #-}

multInt :: (Monoidal a, Ord a, Multiplicative a) => Interval a -> Interval a -> Interval a
multInt i j
  | lower i <  zero && lower j <  zero = Interval (upper i * upper j) (lower i * lower j)
  | lower i >= zero && lower j <  zero = Interval (upper i * lower j) (lower i * upper j)
  | lower i <  zero && lower j >= zero = Interval (upper j * lower i) (lower j * upper i)
  | lower i >= zero && lower j >= zero = Interval (lower j * lower i) (upper j * upper i)
multInt _ _ = error "multInt"
{-# INLINABLE multInt #-}

multA :: Algebraic -> Algebraic -> Algebraic
multA (Rational 0) _ = Rational 0
multA _ (Rational 0) = Rational 0
multA (Rational a) (Rational b) = Rational (a * b)
multA a@Rational{} b@Algebraic{} = multA b a
multA (Algebraic f _ i) (Rational a) =
  let factor = monoize . liftMap (const $ recip a .*. var 0)
  in fromJust $ algebraic (factor f) (scale a i)
     -- ? Can't we use the strum sequence given beforehand?
multA a b =
  let fg = rootMultPoly (eqn a) (eqn b)
      int = catcher multInt fg (stabilize a) (stabilize b)
  in fromJust $ algebraic fg int

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
  in fromJust $ algebraic fi $ recipInt i'

rootRecipPoly :: Unipol Rational -> Unipol Rational
rootRecipPoly f =
  let ts = terms f
      d = totalDegree' f
  in runAdd $ ifoldMap (\m k -> Add $ toPolynomial
                                (k, OrderedMonomial $ singleton $ d - totalDegree m) ) ts

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

countRootsIn :: Unipol Rational -> Interval Rational -> (Int, [Unipol Rational])
countRootsIn f ints =
  let ss = strum f
  in (countChangeIn ints ss, ss)

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

-- | @'improve' r@ returns the same algebraic number,
--   but with more tighter bounds.
improve :: Algebraic -> Algebraic
improve (Algebraic f ss int) = Algebraic f ss $ improveWith ss int
improve a = a

improveWith :: (Ord a, CoeffRing a, Division a)
            => [Unipol a] -> Interval a -> Interval a
improveWith ss int =
  let (ls, us) = bisect int
  in if countChangeIn ls ss == 0 then us else ls

powA :: Integral a => Algebraic -> a -> Algebraic
powA r n | n < 0     = nthRoot' (abs $ fromIntegral n) r
         | n == 0    = Rational 1
         | otherwise = r ^ P.fromIntegral n
{-# INLINE powA #-}

iterateImproveStrum :: Rational -> [Unipol Rational] -> Interval Rational -> Interval Rational
iterateImproveStrum eps ss int0 =
  until (\int -> size int < eps) (improveWith ss) int0

fromFraction :: P.Fractional a => Fraction Integer -> a
fromFraction q = P.fromInteger (numerator q) P./ P.fromInteger (denominator q)

-- | Pseudo resultant. should we expose this?
presultant :: (Euclidean k, CoeffRing k)
           => Unipol k -> Unipol k -> k
presultant = go one one
  where
    go !res !acc h s
        | totalDegree' s > 0     =
          let (_, r)    = h `pDivModPoly` s
              (l, k, m) = (totalDegree' h, totalDegree' r, totalDegree' s)
              res' = res * powSign (l * m)
                         * pow (leadingCoeff s) (fromIntegral $ abs $ l - k)
              adj = pow (leadingCoeff s) (fromIntegral $ abs (1 + l - m))
          in go res' (acc * adj) s r
        | isZero h || isZero s = zero
        | totalDegree' h > 0     = pow (leadingCoeff s) (fromIntegral $ totalDegree' h) * res `quot` acc
        | otherwise              = res `quot` acc

powSign :: (Ring r, Integral n) => n -> r
powSign n | even n = one
          | otherwise = negate one
{-# INLINE powSign #-}

-- | @'realRoots' f@ finds all real roots of the rational polynomial @f@.
realRoots :: Unipol Rational -> [Algebraic]
realRoots = realRootsIrreducible . monoize <=< factors . sqFreePart

-- | Same as @'realRoots'@, but assumes that the given polynomial
--   is monic and irreducible.
realRootsIrreducible :: Unipol Rational -> [Algebraic]
realRootsIrreducible f =
  [ algebraic' f i
  | i <- isolateRoots f
  ]

instance InvolutiveMultiplication Algebraic where
  adjoint = id

instance TriviallyInvolutive Algebraic

-- | @'realRoots' f@ finds all complex roots of the rational polynomial @f@.
--
-- CAUTION: This function currently comes with really naive implementation.
-- Easy to explode.
complexRoots :: Unipol Rational -> [Complex Algebraic]
complexRoots = complexRoots' <=< factors . sqFreePart

complexRoots' :: Unipol Rational -> [Complex Algebraic]
complexRoots' f =
  let rp = realPartPoly f
      ip = imagPartPoly f
  in [ c
     | r <- realRoots rp
     , i <- realRoots ip
     , let c = Complex r i
     , liftMap (const $ c) f == Complex 0 0
     ]

realPartPoly :: Unipol Rational -> Unipol Rational
realPartPoly f =
  normalize $ liftMap (const $ 2 * var 0) $ rootSumPoly f f

imagPartPoly :: Unipol Rational -> Unipol Rational
imagPartPoly f =
  let bi = liftMap (const $ 2 * #x) $
           rootSumPoly f (liftMap (const $ negate $ var 0) f)
  in mapMonomialMonotonic (_Wrapped.ix 0 *~ 2) $
     liftMap (const $ negate #x) $
     rootMultPoly bi bi

-- | Choose representative element of the given interval.
representative :: (Additive r, Division r, Num r) => Interval r -> r
representative (Interval l r) = (l + r) / 2

-- | @'approximate' eps r@ returns rational number @r'@ close to @r@,
--   with @abs (r - r') < eps@.
approximate :: Rational -> Algebraic -> Rational
approximate _   (Rational a) = a
approximate err (Algebraic _ ss int) =
  representative $ iterateImproveStrum err ss int

-- | Same as @'approximate'@, but returns @'Fractional'@ value instead.
approxFractional :: Fractional r => Rational -> Algebraic -> r
approxFractional eps = fromFraction . approximate eps
