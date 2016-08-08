{-# LANGUAGE BangPatterns, DataKinds, FlexibleContexts, GADTs            #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude, OverloadedStrings #-}
{-# LANGUAGE ParallelListComp, PatternSynonyms, PolyKinds                #-}
{-# LANGUAGE ScopedTypeVariables, TupleSections, ViewPatterns            #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Algebra.Ring.Polynomial.Factorize
       (factorise, Unipol, distinctDegFactor,
        equalDegreeSplitM, equalDegreeFactorM,
        henselStep, multiHensel,
        squareFreePart, squareFreeDecomp,factorQBigPrime
       ) where
import           Algebra.Algorithms.PrimeTest     hiding (modPow)
import           Algebra.Field.Finite
import           Algebra.Prelude
import           Algebra.Ring.Polynomial.Quotient
import           Control.Applicative              ((<|>))
import           Control.Arrow                    ((***), (<<<))
import           Control.Lens                     (ifoldl)
import           Control.Lens                     ((%~), (&))
import           Control.Lens                     (both)
import           Control.Lens                     (each)
import           Control.Monad                    (guard, replicateM)
import           Control.Monad                    (when)
import           Control.Monad.Loops              (iterateUntil, untilJust)
import           Control.Monad.Random             (MonadRandom, uniform)
import           Control.Monad.ST.Strict          (ST, runST)
import           Control.Monad.Trans              (lift)
import           Control.Monad.Trans.Loop         (continue, foreach, while)
import qualified Data.DList                       as DL
import           Data.IntMap                      (IntMap)
import qualified Data.IntMap.Strict               as IM
import           Data.List                        (minimumBy)
import qualified Data.List                        as L
import           Data.Maybe                       (fromJust)
import           Data.Maybe                       (fromMaybe)
import           Data.Monoid                      ((<>))
import           Data.Numbers.Primes              (primes)
import           Data.Ord                         (comparing)
import           Data.Proxy                       (Proxy (..))
import qualified Data.Sized.Builtin               as SV
import           Data.STRef.Strict                (STRef, modifySTRef, newSTRef)
import           Data.STRef.Strict                (readSTRef, writeSTRef)
import qualified Data.Traversable                 as F
import           Data.Tuple                       (swap)
import           Data.Type.Ordinal                (pattern OZ)
import qualified Data.Vector                      as V
import           Debug.Trace                      (trace)
import           Debug.Trace                      (traceShow)
import           Numeric.Decidable.Zero           (isZero)
import           Numeric.Domain.GCD               (gcd, lcm)
import qualified Numeric.Field.Fraction           as F
import           Prelude                          (div, mod)
import qualified Prelude                          as P

type Unipol r = OrderedPolynomial r Grevlex 1

-- | @distinctDegFactor f@ computes the distinct-degree decomposition of the given
--   square-free polynomial over finite field @f@.
distinctDegFactor :: forall k. (Eq k, FiniteField k)
                  => Unipol k     -- ^ Square-free polynomial over finite field.
                  -> [(Natural, Unipol k)]   -- ^ Distinct-degree decomposition.
distinctDegFactor f0 = zip [1..] $ go id (var OZ :: Unipol k) f0 []
  where
    go gs h f =
      let h' = modPow h (order (Proxy :: Proxy k)) f
          g' = gcd (h' - varX) f
          f' = f `quot` g'
          gs' = gs . (g' :)
      in if f' == one
         then gs'
         else go gs' h' f'

modPow :: (CoeffRing r, Division r, Euclidean r, KnownNat n, IsMonomialOrder n ord)
       => OrderedPolynomial r ord n -> Natural -> OrderedPolynomial r ord n -> OrderedPolynomial r ord n
modPow a p f = withQuotient (principalIdeal f) $
               repeatedSquare (modIdeal a) p

traceCharTwo :: (Unital m, Monoidal m) => Natural -> m -> m
traceCharTwo m a = sum [ a ^ (2 ^ i) | i <- [0..pred m]]

equalDegreeSplitM :: forall k m. (MonadRandom m, CoeffRing k,  FiniteField k)
                 => Unipol k
                 -> Natural
                 -> m (Maybe (Unipol k))
equalDegreeSplitM f d
  | fromIntegral (totalDegree' f) `mod` d /= 0 = return Nothing
  | otherwise = do
    let q = fromIntegral $ order (Proxy :: Proxy k)
        n = totalDegree' f
        els = elements (Proxy :: Proxy k)
    e <- uniform [1..n P.- 1]
    cs <- replicateM (fromIntegral e) $ uniform els
    let a = varX ^ fromIntegral e +
            sum (zipWith (*) (map injectCoeff cs) [varX ^ l | l <-[0..]])
        g1 = gcd a f
    return $ (guard (g1 /= one) >> return g1)
         <|> do let b | charUnipol f == 2  = traceCharTwo (powerUnipol f*d) a
                      | otherwise = modPow a ((pred $ q^d)`div`2) f
                    g2 = gcd (b - one) f
                guard (g2 /= one && g2 /= f)
                return g2

equalDegreeFactorM :: (Eq k, FiniteField k, MonadRandom m)
                   => Unipol k -> Natural -> m [Unipol k]
equalDegreeFactorM f d = go f >>= \a -> return (a [])
  where
    go h | totalDegree' h == 0 = return id
         | otherwise =
           if fromIntegral (totalDegree' h) == d
           then return (h:)
           else do
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

pthRoot :: (CoeffRing r, Characteristic r) => Unipol r -> Unipol r
pthRoot f =
  let !p = charUnipol f
  in if p == 0
     then error "char R should be positive prime"
     else transformMonomial (SV.map (`P.div` fromIntegral p)) f

squareFreeDecomp :: (Eq k, Characteristic k, Field k)
                 => Unipol k -> IntMap (Unipol k)
squareFreeDecomp f =
  let dcmp = yun f
      f'   = ifoldl (\i u g -> u `quot` (g ^ fromIntegral i)) f dcmp
      p    = fromIntegral $ charUnipol f
  in if charUnipol f == 0
     then dcmp
     else if isZero (f' - one)
     then dcmp
     else IM.filter (not . isZero . subtract one) $
          IM.unionWith (*) dcmp $ IM.mapKeys (p*) $ squareFreeDecomp $ pthRoot f'

-- | Factorise a polynomial over finite field using Cantor-Zassenhaus algorithm
factorise :: (MonadRandom m, CoeffRing k, FiniteField k)
          => Unipol k -> m [(Unipol k, Natural)]
factorise f = do
  concat <$> mapM (\(r, h) -> map (,fromIntegral r) <$> factorSquareFree h) (IM.toList $  squareFreeDecomp f)

clearDenom :: (KnownNat n, CoeffRing a, Euclidean a)
           => Polynomial (Fraction a) n -> (a, Polynomial a n)
clearDenom f =
  let g = foldr (lcm . denominator . fst) one $ getTerms f
  in (g, mapCoeff (numerator . ((g F.% one)*)) f)

factorQBigPrime :: (MonadRandom m)
               => Unipol Integer -> m (Integer, [([Unipol Integer], Natural)])
factorQBigPrime f0 = do
  let (g, c) | leadingCoeff f0 < 0 = (- pp f0, - content f0)
             | otherwise = (pp f0, content f0)
  ts0 <- F.mapM (secondM factorSqFreeQBP . clearDenom) (squareFreeDecomp $ monoize $ mapCoeff (F.% 1) g)
  let anss = IM.toList ts0
      k = c * leadingCoeff g `div` product (map (fst.snd) anss)
  return $ (k, map (snd *** toEnum <<< swap) anss)

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
      let fbar = mapCoeff (modNat' fp) f
      gvec <- V.fromList . concatMap (uncurry (flip replicate) <<< (normalizeMod p . mapCoeff naturalRepr) *** fromEnum)
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
    b' = P.product [ sqrt (fromIntegral n P.+ 1), 2 P.^^ n, fromIntegral a,  fromIntegral b]
         :: Double
    n = totalDegree' f
    isSqFreeMod :: Integer -> Bool
    isSqFreeMod p = reifyPrimeField p $ \fp ->
      let fbar = mapCoeff (modNat' fp) f
      in gcd fbar (diff OZ fbar) == one

-- | Given that @f = gh (mod m)@ with @sg + th = 1 (mod m)@ and @leadingCoeff f@ isn't zero divisor mod m,
--   @henselStep m f g h s t@ calculates the unique (g', h', s', t') s.t.
--   @f = g' h' (mod m), g' = g (mod m), h' = h (mod m), s' = s (mod m), t' = t (mod m)@, @h'@ monic.
henselStep :: (Eq r, Euclidean r)
           => r        -- ^ modulus
           -> Unipol r
           -> Unipol r
           -> Unipol r
           -> Unipol r
           -> Unipol r
           -> (Unipol r, Unipol r, Unipol r, Unipol r)
henselStep m f g h s t =
  let modCoeff = mapCoeff (`rem` m^2)
      divModSq u v = mapCoeff (F.% one) u `divide` mapCoeff (F.% one) v
                     & both %~ mapCoeff (fromJust . modFraction (m^2))
      e = modCoeff $ f - g * h
      (q, r) = divModSq (s*e) h
      g' = modCoeff $ g + t * e + q * g
      h' = modCoeff $ h + r
      b  = modCoeff $ s*g' + t*h' - one
      (c, d) = divModSq (s*b) h'
      s' = modCoeff $ s - d
      t' = modCoeff $ t - t*b - c*g'
  in (g', h', s', t')

tr :: Show a => String -> a -> a
tr msg a = trace (msg ++ show a) a

multiHensel :: Integer -> Natural -> Unipol Integer -> [Unipol Integer] -> [Unipol Integer]
multiHensel p l f [_] =
  let u = fromMaybe (error $ "lc(f) = " ++ (show $ leadingCoeff f) ++ " is zero divisor mod p!") $
          recipMod (tr "p^l = " $ p^l) $ leadingCoeff f
  in [mapCoeff ((`rem` p^l).(*u)) $ f]
multiHensel p l f fs =
  let (as, bs) = splitAt k fs
      g0 = mapCoeff (`rem` p) $ leadingCoeff f .*. product as
      r = length fs
      k = r `div` 2
      d = floor $ logBase 2 (fromIntegral l)
      h0 = mapCoeff (`rem` p) $ product bs
      (a, s0, t0) : _ = reifyPrimeField p $ \fp ->
        map (each %~ mapCoeff naturalRepr) $ euclid (skim $ mapCoeff (modNat' fp) g0) (skim $ mapCoeff (modNat' fp) h0)
      (gd, hd, _, _) = foldl (\(s, t, g, h) j -> henselStep (p^2^j) f g h s t)
                         (s0, t0, mapCoeff (`rem` p) $ product as, h0)
                         [0..d P.- 1]
  in if a /= one
     then error $ concat ["(f, as, bs, g0, h0) = ", show (f, as, bs, g0, h0), " is not bezout coprime!"]
     else multiHensel p l (tr "gd = " gd) as ++ multiHensel p l (tr "hd = " hd) bs

skim :: Show b => b -> b
skim a = traceShow a a

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
normalizeMod p f = mapCoeff chooseHalf f
  where
    chooseHalf ((`rem` p) -> c) = minimumBy (comparing P.abs) [c, c - p]

