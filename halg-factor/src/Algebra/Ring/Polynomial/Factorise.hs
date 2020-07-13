{-# LANGUAGE BangPatterns, DataKinds, ExtendedDefaultRules          #-}
{-# LANGUAGE FlexibleContexts, GADTs, MultiParamTypeClasses         #-}
{-# LANGUAGE NoImplicitPrelude, OverloadedLabels, OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms, PolyKinds, ScopedTypeVariables        #-}
{-# LANGUAGE TupleSections, TypeApplications, ViewPatterns          #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Algebra.Ring.Polynomial.Factorise
  ( -- * Factorisation
    factorise, factorQBigPrime, factorHensel,
    isReducible,
    -- * Internal helper functions
    distinctDegFactor,
    equalDegreeSplitM, equalDegreeFactorM,
    henselStep, multiHensel, clearDenom,
    squareFreePart, pthRoot,
    yun, squareFreeDecompFiniteField
  ) where
import           Algebra.Arithmetic                 hiding (modPow)
import           Algebra.Field.Prime
import           Algebra.Prelude.Core
import           Algebra.Ring.Euclidean.Quotient
import           Algebra.Ring.Polynomial.Univariate
import           Control.Applicative                ((<|>))
import           Control.Arrow                      ((***), (<<<))
import           Control.Lens                       (both, ifoldMap, (%~), (&))
import           Control.Monad                      (guard, replicateM)
import           Control.Monad                      (when)
import           Control.Monad.Loops                (iterateUntil, untilJust)
import           Control.Monad.Random               (MonadRandom, Random,
                                                     getRandom, getRandomR,
                                                     uniform)
import           Control.Monad.ST.Strict            (ST, runST)
import           Control.Monad.Trans                (lift)
import           Control.Monad.Trans.Loop           (continue, foreach, while)
import qualified Data.DList                         as DL
import qualified Data.FMList                        as FML
import           Data.IntMap                        (IntMap)
import qualified Data.IntMap.Strict                 as IM
import qualified Data.List                          as L
import           Data.Maybe                         (fromJust)
import           Data.Monoid                        ((<>))
import           Data.Numbers.Primes                (primes)
import           Data.Proxy                         (Proxy (..))
import qualified Data.Set                           as S
import           Data.STRef.Strict                  (STRef, modifySTRef,
                                                     newSTRef)
import           Data.STRef.Strict                  (readSTRef, writeSTRef)
import qualified Data.Traversable                   as F
import qualified Data.Vector                        as V
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
modPow :: (Euclidean poly)
       => poly -> Natural -> poly -> poly
modPow a p f = withQuotient f $
  repeatedSquare (quotient a) p

traceCharTwo :: (Unital m, Monoidal m) => Natural -> m -> m
traceCharTwo m a = foldl' (+) zero $ take (fromIntegral m) $ iterate (\(!x) ->x*x) a

equalDegreeSplitM
  :: forall k m. (MonadRandom m, Random k, CoeffRing k,  FiniteField k)
  => Unipol k
  -> Natural
  -> m (Maybe (Unipol k))
equalDegreeSplitM f d
  | n `mod` fromIntegral d /= 0 = return Nothing
  | otherwise = do
    let q = fromIntegral $ order (Proxy :: Proxy k)
    e <- getRandomR (1, n P.- 1)
    cs <- replicateM (fromIntegral e) getRandom
    let a = var 0 ^ fromIntegral e +
            sum (zipWith (*) (map injectCoeff cs) [var 0 ^ l | l <-[0..]])
        g1 = gcd a f
    return $ (guard (g1 /= one) >> return g1)
         <|> do let b | charUnipol f == 2  =
                          withQuotient f $
                          traceCharTwo (powerUnipol f*d) (quotient a)
                      | otherwise = modPow a (pred (q^d) `div`2) f
                    g2 = gcd (b - one) f
                guard (g2 /= one && g2 /= f)
                return g2
  where n = totalDegree' f

equalDegreeFactorM :: (Eq k, FiniteField k, MonadRandom m, Random k)
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

factorSquareFree :: (Eq k, Random k, FiniteField k, MonadRandom m)
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
      h'   = runMult $ ifoldMap (\i g -> Mult $ g ^ fromIntegral i) dcmp
      fhInv = f `quot` h'
      p    = fromIntegral $ charUnipol f
      powers =
        IM.mapKeysMonotonic (p*) $
        squareFreeDecompFiniteField $ pthRoot fhInv
      ((pns, pnjs), js) =
        IM.mapAccumWithKey
            (\(ps', pnjs') j g0 ->
                let (g', pnjsps'') =
                      IM.mapAccum
                        (\g h ->
                          let u = g `gcd` h
                              h' = h `quot` u
                          in (g `quot` u, (u, h'))
                        )
                      g0 ps'
                    pnjs'' = IM.filter ((>0) . totalDegree')
                      $ IM.mapKeysMonotonic (+ j)
                      $ fst <$> pnjsps''
                    ps'' = IM.filter ((>0) . totalDegree')
                        $ snd <$> pnjsps''
                in (( ps'', pnjs' <> pnjs''), g')
            )
            (powers, IM.empty)
            $ fst (IM.split p dcmp)
  in if fst (IM.findMax dcmp) < p && fhInv == one
    then dcmp
    else IM.unions [IM.filter ((>0) . totalDegree') js, pnjs, pns]


newtype GCD a = GCD { runGCD :: a }

instance Euclidean a => P.Semigroup (GCD a) where
  (<>) = (GCD .) . (gcd `on` runGCD)
instance Euclidean a => Monoid (GCD a) where
  mappend = (<>)
  mempty = GCD zero

newtype LCM a = LCM { runLCM :: a }

instance Euclidean a => P.Semigroup (LCM a) where
  (<>) = (LCM .) . (lcm `on` runLCM)
instance Euclidean a => Monoid (LCM a) where
  mappend = (<>)
  mempty = LCM one

-- | Factorise a polynomial over finite field using Cantor-Zassenhaus algorithm
factorise :: (MonadRandom m, CoeffRing k, FiniteField k, Random k)
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

-- | Factorise the given primitive and square-freeinteger-coefficient polynomial,
--   choosing a large enough prime.
factorQBigPrime :: (MonadRandom m)
               => Unipol Integer -> m (Integer, IntMap (Set (Unipol Integer)))
factorQBigPrime = wrapSQFFactor factorSqFreeQBP

-- | Factorise the given
--   interger-coefficient polynomial by Hensel lifting.
factorHensel :: (MonadRandom m)
             => Unipol Integer -> m (Integer, IntMap (Set (Unipol Integer)))
factorHensel = wrapSQFFactor factorHenselSqFree

wrapSQFFactor :: (MonadRandom m)
              => (Unipol Integer -> m [Unipol Integer])
              -> Unipol Integer -> m (Integer, IntMap (Set (Unipol Integer)))
wrapSQFFactor fac f0
  | n == 0 = pure (leadingCoeff f0, IM.empty)
  | n == 1 = pure (1, IM.singleton 1 $ S.singleton f0)
  | otherwise =  do
    let (g, c) = (pp f0, content f0)
    ts0 <- F.mapM (secondM fac . clearDenom) (yun $ monoize $ mapCoeffUnipol (F.% 1) g)
    let anss = IM.toList ts0
        k = c * leadingCoeff g `div` product (map (fst.snd) anss)
    return (k, IM.fromList $ map (second $ S.fromList . snd) anss)
  where
    n = totalDegree' f0

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

factorHenselSqFree
  :: MonadRandom m
  => Unipol Integer -> m [Unipol Integer]
factorHenselSqFree f =
  let lc = leadingCoeff f
      Just p = find isGoodPrime primes
      power  = ceiling $ logBase (fromIntegral p) $ 2 * kB + 1
  in reifyPrimeField p $ \fp -> do
    let lc' = modNat' fp lc
        f0 = mapCoeffUnipol ((/lc') . modNat' fp) f
    fps <- map (normalizeMod p . mapCoeffUnipol naturalRepr . fst) <$> factorise f0
    let gs = V.fromList $ map (normalizeMod $ p ^ fromIntegral power)
            $ multiHensel (fromIntegral p) power f
              fps
        count = V.length gs
        alives = [0 .. count - 1]
    return $ loop (p P.^ power) alives count 1 f gs []
  where
    lc = leadingCoeff f
    kA = maxNorm f
    n = totalDegree' f
    kB :: Double
    kB = sqrt (fromIntegral n + 1) * 2 P.^ n * fromIntegral (kA * lc)
    isGoodPrime p = reifyPrimeField p $ \fp ->
      lc `mod` p /= 0 && isSquareFree (mapCoeffUnipol (modNat' fp) f)
    loop pk alives !count !l !h gs acc
      | 2 * l > count =
          if h == one then acc else h : acc
      | otherwise = go pk alives count l
          (combinations l alives) h (leadingCoeff h) gs acc
    go pk alives !count l [] f' _ pols acc = loop pk alives count (l + 1) f' pols acc
    go pk alives !count l ((gs, hs) : cands) f' b pols acc
      | oneNorm g * oneNorm h <= floor kB =
          loop pk hs (count - l) l (pp h) pols (pp g : acc)
      | otherwise = go pk alives count l cands f' b pols acc
      where
        g = normalizeMod pk $ b .* runMult (foldMap (Mult . V.unsafeIndex pols) gs)
        h = normalizeMod pk $ b .* runMult (foldMap (Mult . V.unsafeIndex pols) hs)

-- | Given that @f = gh (mod m)@ with @sg + th = 1 (mod m)@ and @leadingCoeff f@ isn't zero divisor mod m,
--   @henselStep m f g h s t@ calculates the unique (g', h', s', t') s.t.
--   @f = g' h' (mod m^2), g' = g (mod m), h' = h (mod m), s' = s (mod m), t' = t (mod m)@, @h'@ monic.
henselStep
  :: (Eq r, Euclidean r)
  => r        -- ^ modulus
  -> Unipol r
  -> Unipol r
  -> Unipol r
  -> Unipol r
  -> Unipol r
  -> (Unipol r, Unipol r, Unipol r, Unipol r)
henselStep m f g h s t =
  let modCoeff = mapCoeffUnipol (`rem` m^2)
      divModSq u v =
        mapCoeffUnipol (F.% one) u `divide` mapCoeffUnipol (F.% one) v
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
repeatHensel
  :: Integer -> Int
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
            -> [Unipol Integer] -- ^ monic coprime factorisation mod @p@
            -> [Unipol Integer] -- ^ coprime factorisation mod @p^(2^k)@.
{-# INLINE multiHensel #-}
multiHensel (toInteger -> p) n = \f -> DL.toList . go f . V.fromList
  where
    go f gs
      | len == 0 = DL.empty
      | len == 1 = DL.singleton $
          let q = p P.^ n
              (u,_,bInv) = egcd q (leadingCoeff f)
          in mapCoeffUnipol (`mod` q)
            $ (bInv `quot` u) .*. f
      | otherwise  = reifyPrimeField p $ \fp ->
        let k = len `div` 2
            d = ceilingLogBase2 n
            (ls, rs) = V.splitAt k gs
            (g0, h0) = (leadingCoeff f .*. product ls, product rs)
              & both %~ mapCoeffUnipol (`mod` p)
            (_, s0, t0) = egcd
              (mapCoeffUnipol (modNat' fp) g0)
              (mapCoeffUnipol (modNat' fp) h0)
            (s, t) = (s0, t0) & both %~ mapCoeffUnipol naturalRepr
            (g, h, _, _) = repeatHensel p d f g0 h0 s t
        in go g ls <> go h rs
      where len = V.length gs

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

combinations :: Int -> [Int] -> [([Int], [Int])]
combinations n = FML.toList . go n
  where
    go 0 xs  = FML.singleton ([], xs)
    go _ [] = FML.empty
    go k (x:xs) =
      let present = go (k - 1) xs
          absent = go k xs
      in fmap (first $ (:) x) present
        <> fmap (second $ (:) x) absent

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
