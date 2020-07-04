{-# LANGUAGE BangPatterns, DataKinds, FlexibleContexts, GADTs           #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude, OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings, PatternSynonyms, PolyKinds              #-}
{-# LANGUAGE ScopedTypeVariables, TupleSections, TypeApplications       #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Algebra.Ring.Polynomial.Factorise
  ( -- * Factorisation
    factorise, factorQBigPrime, factorHensel,
    isReducible,
    -- * Internal helper functions
    distinctDegFactor,
    equalDegreeSplitM, equalDegreeFactorM,
    henselStep, clearDenom,
    squareFreePart,
    yun, squareFreeDecompFiniteField
  ) where
import           Algebra.Arithmetic                 hiding (modPow)
import           Algebra.Field.Prime
import           Algebra.Prelude.Core
import           Algebra.Ring.Polynomial.Quotient
import           Algebra.Ring.Polynomial.Univariate
import           Control.Applicative                ((<|>))
import           Control.Arrow                      ((***), (<<<))
import           Control.Lens                       (both, ifoldl, (%~), (&))
import           Control.Monad                      (guard, replicateM)
import           Control.Monad                      (when)
import           Control.Monad.Loops                (iterateUntil, untilJust)
import           Control.Monad.Random               (MonadRandom, uniform)
import           Control.Monad.ST.Strict            (ST, runST)
import           Control.Monad.Trans                (lift)
import           Control.Monad.Trans.Loop           (continue, foreach, while)
import qualified Data.DList                         as DL
import           Data.IntMap                        (IntMap)
import qualified Data.IntMap.Strict                 as IM
import qualified Data.List                          as L
import           Data.Maybe                         (fromJust)
import           Data.Monoid                        (Sum (..))
import           Data.Monoid                        ((<>))
import           Data.Numbers.Primes                (primes)
import           Data.Proxy                         (Proxy (..))
import qualified Data.Set                           as S
import           Data.STRef.Strict                  (STRef, modifySTRef,
                                                     newSTRef)
import           Data.STRef.Strict                  (readSTRef, writeSTRef)
import qualified Data.Traversable                   as F
import qualified Data.Vector                        as V
import           Math.NumberTheory.Logarithms       (intLog2', integerLogBase')
import           Math.NumberTheory.Powers.Squares   (integerSquareRoot)
import qualified Math.NumberTheory.Primes           as PRIMES
import           Numeric.Decidable.Zero             (isZero)
import           Numeric.Domain.GCD                 (gcd, lcm)
import qualified Numeric.Field.Fraction             as F
import qualified Prelude                            as P

-- | @distinctDegFactor f@ computes the distinct-degree decomposition of the given
--   square-free polynomial over finite field @f@.
distinctDegFactor :: forall k. (Eq k, FiniteField k)
                  => Unipol k     -- ^ Square-free polynomial over finite field.
                  -> [(Natural, Unipol k)]   -- ^ Distinct-degree decomposition.
distinctDegFactor f0 = zip [1..] $ go id (var OZ :: Unipol k) f0 []
  where
    go gs h f =
      let h' = modPow h (order (Proxy :: Proxy k)) f
          g' = gcd (h' - var 0) f
          f' = f `quot` g'
          gs' = gs . (g' :)
      in if f' == one
         then gs'
         else go gs' h' f'

-- | @'modPow' f n g@ computes \(f^n \mod{g}\).
modPow :: (Field (Coefficient poly), IsOrderedPolynomial poly)
       => poly -> Natural -> poly -> poly
modPow a p f = withQuotient (principalIdeal f) $
               repeatedSquare (modIdeal a) p

traceCharTwo :: (Unital m, Monoidal m) => Natural -> m -> m
traceCharTwo m a = foldl' (+) zero $ take (fromIntegral m) $ iterate (\(!x) ->x*x) a

equalDegreeSplitM :: forall k m. (MonadRandom m, CoeffRing k,  FiniteField k)
                 => Unipol k
                 -> Natural
                 -> m (Maybe (Unipol k))
equalDegreeSplitM f d
  | n `mod` fromIntegral d /= 0 = return Nothing
  | otherwise = do
    let q = fromIntegral $ order (Proxy :: Proxy k)
        els = elements (Proxy :: Proxy k)
    e <- uniform [1..n P.- 1]
    cs <- replicateM (fromIntegral e) $ uniform els
    let a = var 0 ^ fromIntegral e +
            sum (zipWith (*) (map injectCoeff cs) [var 0 ^ l | l <-[0..]])
        g1 = gcd a f
    return $ (guard (g1 /= one) >> return g1)
         <|> do let b | charUnipol f == 2  =
                          withQuotient (principalIdeal f) $
                          traceCharTwo (powerUnipol f*d) (modIdeal a)
                      | otherwise = modPow a (pred (q^d) `div`2) f
                    g2 = gcd (b - one) f
                guard (g2 /= one && g2 /= f)
                return g2
  where n = totalDegree' f
equalDegreeFactorM :: (Eq k, FiniteField k, MonadRandom m)
                   => Unipol k -> Natural -> m [Unipol k]
equalDegreeFactorM f d = go f >>= \a -> return (a [])
  where
    go h
      | totalDegree' h == 0 = return id
      | fromIntegral (totalDegree' h) == d = return (h:)
      | otherwise = do
          g <- untilJust (equalDegreeSplitM h d)
          l <- go g
          r <- go (h `quot` g)
          return $ l . r

factorSquareFree :: (Eq k, FiniteField k, MonadRandom m)
                 => Unipol k -> m [Unipol k]
factorSquareFree f =
   concat <$> mapM (uncurry $ flip equalDegreeFactorM) (filter ((/= one) . snd) $ distinctDegFactor f)

squareFreePart :: (Eq k, FiniteField k)
               => Unipol k -> Unipol k
squareFreePart f =
  let !n = fromIntegral $ totalDegree' f
      u  = gcd f (diff 0 f)
      v  = f `quot` u
      f' = u `quot` gcd u (v ^ n)
  in if f' == one
     then v
     else v * squareFreePart (pthRoot f')

-- | Yun's method to compute square-free decomposition of
--   a univariate polynomial over field of characteristic \(0\).
--
--   Use 'squareFreeDecompFiniteField' for finite fields.
yun :: (CoeffRing r, Field r)
    => Unipol r -> IntMap (Unipol r)
yun f = let f' = diff OZ f
            u  = gcd f f'
        in go 1 IM.empty (f `quot` u) (f' `quot` u)
  where
    go !i dic v w =
      let t  = w - diff OZ v
          h  = gcd v t
          v' = v `quot` h
          w' = t `quot` h
          dic' = IM.insert i h dic
      in if v' == one
         then dic'
         else go (i+1) dic' v' w'

charUnipol :: forall r. Characteristic r => Unipol r -> Natural
charUnipol _ = char (Proxy :: Proxy r)

powerUnipol :: forall r. FiniteField r => Unipol r -> Natural
powerUnipol _ = power (Proxy :: Proxy r)

pthRoot :: forall r. (CoeffRing r, FiniteField r) => Unipol r -> Unipol r
pthRoot f =
  let !p = charUnipol f
      !q = order $ Proxy @r
      !s = q `div` p
  in sum  [ (a^s) .*. #x^i
          | (ip, a) <- IM.toList $ termsUnipol f
          , (i, 0) <- [fromIntegral ip `P.divMod` p]
          ]

-- | Square-free decomposition of polynomials over a finite field.
--
--   Use 'yun' for a polynomials over a field of characteristic zero.
squareFreeDecompFiniteField
  :: (Eq k, FiniteField k)
  => Unipol k -> IntMap (Unipol k)
squareFreeDecompFiniteField f =
  let dcmp = yun f
      f'   = ifoldl (\i u g -> u `quot` (g ^ fromIntegral i)) f dcmp
      p    = fromIntegral $ charUnipol f
  in if isZero (f' - one)
     then dcmp
     else IM.filter (not . isZero . subtract one) $
          IM.unionWith (*) dcmp $ IM.mapKeys (p*) $
          squareFreeDecompFiniteField $ pthRoot f'

-- | Factorise a polynomial over finite field using Cantor-Zassenhaus algorithm
factorise :: (MonadRandom m, CoeffRing k, FiniteField k)
          => Unipol k -> m [(Unipol k, Natural)]
factorise f0
  | isZero f0 = pure [(zero, 1)]
  | otherwise = do
  let f = monoize f0
      c = leadingCoeff f0
  monoFacts <- concat
    <$> mapM (\(r, h) -> map (,fromIntegral r) <$> factorSquareFree h) (IM.toList $  squareFreeDecompFiniteField f)
  pure $ if c == one
    then monoFacts
    else (injectCoeff c, 1) : monoFacts

clearDenom :: (CoeffRing a, Euclidean a)
           => Unipol (Fraction a) -> (a, Unipol a)
clearDenom f =
  let g = foldr (lcm . denominator) one $ terms' f
  in (g, mapCoeffUnipol (numerator . ((g F.% one)*)) f)

-- | Factorise the given integer-coefficient polynomial,
--   choosing a large enough prime.
factorQBigPrime :: (MonadRandom m)
               => Unipol Integer -> m (Integer, IntMap (Set (Unipol Integer)))
factorQBigPrime = wrapSQFFactor factorSqFreeQBP

-- | Factorise the given interger-coefficient polynomial by Hensel lifting.
factorHensel :: (MonadRandom m)
             => Unipol Integer -> m (Integer, IntMap (Set (Unipol Integer)))
factorHensel = wrapSQFFactor factorHenselSqFree

wrapSQFFactor :: (MonadRandom m)
              => (Unipol Integer -> m [Unipol Integer])
              -> Unipol Integer -> m (Integer, IntMap (Set (Unipol Integer)))
wrapSQFFactor fac f0
  | isZero f0 = pure (0, IM.empty)
  | totalDegree' f0 == 1 = pure (1, IM.singleton 1 $ S.singleton f0)
  | otherwise =  do
    let (g, c) = (pp f0, content f0)
    ts0 <- F.mapM (secondM fac . clearDenom) (yun $ monoize $ mapCoeffUnipol (F.% 1) g)
    let anss = IM.toList ts0
        k = c * leadingCoeff g `div` product (map (fst.snd) anss)
    return (k, IM.fromList $ map (second $ S.fromList . snd) anss)


secondM :: Functor f => (t -> f a) -> (t1, t) -> f (t1, a)
secondM f (a, b)= (a,) <$> f b

(<@>) :: (a -> b) -> STRef s a -> ST s b
(<@>) f r = f <$> readSTRef r

infixl 5 <@>

factorSqFreeQBP :: (MonadRandom m)
                => Unipol Integer -> m [Unipol Integer]
factorSqFreeQBP f
  | n == 1 = return [f]
  | otherwise = do
    p <- iterateUntil isSqFreeMod (uniform ps)
    reifyPrimeField p $ \fp -> do
      let fbar = mapCoeffUnipol (modNat' fp) f
      gvec <- V.fromList . concatMap (uncurry (flip replicate) <<< (normalizeMod p . mapCoeffUnipol naturalRepr) *** fromEnum)
              <$> factorise (monoize fbar)
      return $ runST $ do
        bb <- newSTRef b
        s  <- newSTRef 1
        ts <- newSTRef [0..V.length gvec - 1]
        gs <- newSTRef []
        f' <- newSTRef f
        while ((<=) <$> (2*) <@> s <*> length <@> ts) $ do
          ts0 <- lift $ readSTRef ts
          s0  <- lift $ readSTRef s
          b0  <- lift $ readSTRef bb
          foreach (comb s0 ts0) $ \ss -> do
            let delta = ts0 L.\\ ss
                g' = normalizeMod p $ b0 .*. product [ gvec V.! i | i <- ss]
                h' = normalizeMod p $ b0 .*. product [ gvec V.! i | i <- delta]
            when (oneNorm g' * oneNorm h' <= floor b') $ do
              lift $ lift $ do
                writeSTRef ts   delta
                modifySTRef gs (pp g' :)
                writeSTRef f' $ pp h'
                writeSTRef bb $ leadingCoeff $ pp h'
              lift continue
          lift $ modifySTRef s (+1)
        (:) <$> readSTRef f' <*> readSTRef gs
  where
    ps = takeWhile (< floor (4*b')) $ dropWhile (<= ceiling (2*b')) $ tail primes
    b = leadingCoeff f
    a = maxNorm f
    b' = P.product [ P.sqrt (fromIntegral n P.+ 1), 2 P.^^ n, fromIntegral a,  fromIntegral b]
         :: Double
    n = totalDegree' f
    isSqFreeMod :: Integer -> Bool
    isSqFreeMod p = reifyPrimeField p $ \fp ->
      let fbar = mapCoeffUnipol (modNat' fp) f
      in gcd fbar (diff OZ fbar) == one

factorHenselSqFree :: MonadRandom m
                   => Unipol Integer -> m [Unipol Integer]
factorHenselSqFree f =
  let lc = leadingCoeff f
      Just p = find isGoodPrime primes
      normF  = integerSquareRoot (getSum $ foldMap (Sum . (^2)) $ terms f) + 1
      power  = succ $ intLog2' $ integerLogBase' p $ normF * 2 ^ fromIntegral (totalDegree' f + 1)
  in reifyPrimeField p $ \fp -> do
  let lc' = modNat' fp lc
      f0 = mapCoeffUnipol ((/lc') . modNat' fp) f
  fps <- factorise f0
  let gs = multiHensel (fromIntegral p) power f $
           map (mapCoeffUnipol naturalRepr . fst) fps
  return $ loop (p^2^fromIntegral power) 1 (length gs) f gs []
  where
    lc = leadingCoeff f
    isGoodPrime p = reifyPrimeField p $ \fp ->
      lc `mod` p /= 0 && isSquareFree (mapCoeffUnipol (modNat' fp) f)
    loop pk !l m !h gs acc
      | fromIntegral (2 * l) > m =  if h == one then acc else h : acc
      | otherwise =
        let cands = [ (ss, g, q)
                    | ss <- comb l gs
                    , let g = normalizeMod pk $ lc .* product ss
                    , let (q, r) = pDivModPoly (lc .* h) g
                    , isZero r
                    , leadingCoeff q * leadingCoeff g == lc * leadingCoeff h
                    ]
        in case cands of
            [] -> loop pk (l + 1) m h gs acc
            ((ss, g, q) : _) ->
             let u = leadingCoeff g `div` content g
             in loop pk l m (mapCoeff' (`div` u) q) (gs L.\\ ss) (pp g : acc)

-- | Given that @f = gh (mod m)@ with @sg + th = 1 (mod m)@ and @leadingCoeff f@ isn't zero divisor mod m,
--   @henselStep m f g h s t@ calculates the unique (g', h', s', t') s.t.
--   @f = g' h' (mod m^2), g' = g (mod m), h' = h (mod m), s' = s (mod m), t' = t (mod m)@, @h'@ monic.
henselStep :: (Eq r, Euclidean r)
           => r        -- ^ modulus
           -> Unipol r
           -> Unipol r
           -> Unipol r
           -> Unipol r
           -> Unipol r
           -> (Unipol r, Unipol r, Unipol r, Unipol r)
henselStep m f g h s t =
  let modCoeff = mapCoeffUnipol (`rem` m^2)
      divModSq u v = mapCoeffUnipol (F.% one) u `divide` mapCoeffUnipol (F.% one) v
                     & both %~ mapCoeffUnipol (fromJust . modFraction (m^2))
      e = modCoeff $ f - g * h
      (q, r) = divModSq (s*e) h
      g' = modCoeff $ g + t * e + q * g
      h' = modCoeff $ h + r
      b  = modCoeff $ s*g' + t*h' - one
      (c, d) = divModSq (s*b) h'
      s' = modCoeff $ s - d
      t' = modCoeff $ t - t*b - c*g'
  in (g', h', s', t')

-- | Repeatedly applies hensel lifting for monics.
repeatHensel :: Integer -> Int
             -> Unipol Integer
             -> Unipol Integer -> Unipol Integer
             -> Unipol Integer -> Unipol Integer
             -> (Unipol Integer, Unipol Integer, Unipol Integer, Unipol Integer)
repeatHensel !m 0 _ g h s t = (normalizeMod m g, normalizeMod m h, s, t)
repeatHensel !m n f g h s t =
  let (g', h', s', t') = henselStep m f g h s t
  in repeatHensel (m ^ 2) (n - 1) f g' h' s' t'

-- | Monic hensel lifting for many factors.
multiHensel :: Natural          -- ^ prime @p@
            -> Int              -- ^ iteration count @k@.
            -> Unipol Integer   -- ^ original polynomial
            -> [Unipol Integer] -- ^ coprime factorisation mod @p@
            -> [Unipol Integer] -- ^ coprime factorisation mod @p^(2^k)@.
multiHensel p n f [_]    = [normalizeMod (fromNatural p^fromIntegral n) f]
multiHensel p n f [g, h] = reifyPrimeField (fromNatural p) $ \fp ->
  let (_, s0, t0) = head $
                    euclid
                      (mapCoeffUnipol (modNat' fp) g)
                      (mapCoeffUnipol (modNat' fp) h)
      (s, t) = (s0, t0) & both %~ mapCoeffUnipol naturalRepr
      (g', h', _, _) = repeatHensel (fromNatural p) n f g h s t
  in [g', h']
multiHensel p n f gs = reifyPrimeField (fromNatural p) $ \fp ->
  let (ls, rs) = splitAt (length gs `div` 2) gs
      (l, r) = (product ls, product rs)
      (_, s0, t0) = head $
                    euclid
                      (mapCoeffUnipol (modNat' fp) l)
                      (mapCoeffUnipol (modNat' fp) r)
      (s, t) = (s0, t0) & both %~ mapCoeffUnipol naturalRepr
      (fl, fr, _, _) = repeatHensel (fromNatural p) n f l r s t
  in multiHensel p n fl ls ++ multiHensel p n fr rs

recipMod :: (Euclidean a, Eq a) => a -> a -> Maybe a
recipMod m u =
  let (a, r, _) : _ = euclid u m
  in if a == one
     then Just r else Nothing

modFraction :: (Euclidean s, Eq s) => s -> Fraction s -> Maybe s
modFraction m d = ((numerator d `rem` m) *) <$> recipMod m (denominator d)

comb :: Int -> [a] -> [[a]]
comb = (DL.toList .) . go
  where
    go 0 [] = DL.singleton []
    go _ [] = DL.empty
    go k (x:xs) = DL.map (x :) (go (k - 1) xs) <> go k xs

normalizeMod :: Integer -> Unipol Integer -> Unipol Integer
normalizeMod p = mapCoeffUnipol (subtract half . (`mod` p) . (+ half))
  where half = p `div` 2

isSquareFree :: forall poly. (IsOrderedPolynomial poly, GCDDomain poly) => poly -> Bool
isSquareFree f = (f `gcd` diff 0 f) == one

-- | Reducibility test for univariate polynomials over finite fields.
isReducible
  :: forall k. (FiniteField k, Eq k)
  => Unipol k -> Bool
isReducible f
  | n == 0 = True
  | n == 1 = False
  | otherwise =
    let divisors = map (PRIMES.unPrime . fst) $ PRIMES.factorise n
        q = order $ Proxy @k
        xqn = modPow #x (q^n) f
              -- FIXME: Use the fast modular composition algorithm
              -- using Horner's rule
        test t =
          let b = modPow #x (q ^ (n `div` t)) f
              -- FIXME: Use the fast modular composition algorithm
              -- using Horner's rule
          in gcd (b - #x) f /= one
    in xqn /= #x || any test divisors
  where
    n = fromIntegral @_ @Natural $ totalDegree' f
