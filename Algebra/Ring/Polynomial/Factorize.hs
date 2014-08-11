{-# LANGUAGE BangPatterns, FlexibleContexts, MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude, OverloadedStrings, ParallelListComp #-}
{-# LANGUAGE PolyKinds, ScopedTypeVariables, TupleSections          #-}
module Algebra.Ring.Polynomial.Factorize (factorise, Unipol, distinctDegFactor,
                                          equalDegreeSplitM, equalDegreeFactorM,
                                          squareFreePart, squareFreeDecomp,
                                          generateIrreducible) where
import           Algebra.Algorithms.PrimeTest     hiding (modPow)
import           Algebra.Field.Finite
import           Algebra.Prelude
import           Algebra.Ring.Polynomial.Quotient
import           Control.Applicative              ((<$>), (<|>))
import           Control.Lens                     (ifoldl)
import           Control.Monad                    (guard, replicateM)
import           Control.Monad.Loops              (untilJust)
import           Control.Monad.Loops              (iterateUntil)
import           Control.Monad.Random             (MonadRandom, uniform)
import           Data.IntMap                      (IntMap)
import qualified Data.IntMap.Strict               as IM
import           Data.Proxy                       (Proxy (..))
import           Data.Type.Natural                hiding (one)
import           Data.Type.Ordinal                (Ordinal (..))
import qualified Data.Vector.Sized                as SV
import           Numeric.Decidable.Zero           (isZero)
import           Numeric.Semiring.Integral        (IntegralSemiring)
import           Prelude                          (div, mod, toInteger)
import qualified Prelude                          as P

type Unipol r = OrderedPolynomial r Grevlex One

-- | @distinctDegFactor f@ computes the distinct-degree decomposition of the given
--   square-free polynomial over finite field @f@.
distinctDegFactor :: forall k. (Eq k, DecidableUnits k, DecidableZero k,
                                IntegralSemiring k, FiniteField k)
                  => Unipol k     -- ^ Square-free polynomial over finite field.
                  -> [(Natural, Unipol k)]   -- ^ Distinct-degree decomposition.
distinctDegFactor f0 = zip [1..] $ go id varX f0 []
  where
    go gs h f =
      let h' = modPow h (order (Proxy :: Proxy k)) f
          g' = gcd (h' - varX) f
          f' = f `quot` g'
          gs' = gs . (g' :)
      in if f' == one
         then gs'
         else go gs' h' f'

modPow :: (Eq r, Ring r, DecidableZero r, Division r, Commutative r, SingI n, IsMonomialOrder ord)
       => OrderedPolynomial r ord n -> Natural -> OrderedPolynomial r ord n -> OrderedPolynomial r ord n
modPow a p f = withQuotient (principalIdeal f) $
               repeatedSquare (modIdeal a) p

traceCharTwo :: (Unital m, Monoidal m) => Natural -> m -> m
traceCharTwo m a = sum [ a ^ (2 ^ i) | i <- [0..pred m]]

equalDegreeSplitM :: forall k m. (MonadRandom m, Eq k, DecidableUnits k,
                                  DecidableZero k, IntegralSemiring k, FiniteField k)
                 => Unipol k
                 -> Natural
                 -> m (Maybe (Unipol k))
equalDegreeSplitM f d
  | fromIntegral (totalDegree' f) `mod` d /= 0 = return Nothing
  | otherwise = do
    let q = fromIntegral $ order (Proxy :: Proxy k)
        n = totalDegree' f
        els = elements (Proxy :: Proxy k)
    e <- uniform [1..n-1]
    cs <- replicateM e $ uniform els
    let a = varX ^ fromIntegral e +
            sum (zipWith (*) (map injectCoeff cs) [varX ^ l | l <-[0..]])
        g1 = gcd a f
    return $ (guard (g1 /= one) >> return g1)
         <|> do let b | charUnipol f == 2  = traceCharTwo (powerUnipol f*d) a
                      | otherwise = modPow a ((pred $ q^d)`div`2) f
                    g2 = gcd (b-one) f
                guard (g2 /= one && g2 /= f)
                return g2

equalDegreeFactorM :: (Eq k, DecidableUnits k, DecidableZero k,
                       IntegralSemiring k, FiniteField k, MonadRandom m)
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

factorSquareFree :: (Eq k, DecidableUnits k, DecidableZero k, IntegralSemiring k,
                     FiniteField k, MonadRandom m, Functor m)
                 => Unipol k -> m [Unipol k]
factorSquareFree f =
   concat <$> mapM (uncurry $ flip equalDegreeFactorM) (filter ((/= one) . snd) $ distinctDegFactor f)

squareFreePart :: (Eq k, DecidableUnits k, DecidableZero k, IntegralSemiring k, FiniteField k)
               => Unipol k -> Unipol k
squareFreePart f =
  let !n = fromIntegral $ totalDegree' f
      u  = gcd f (diff 0 f)
      v  = f `quot` u
      f' = u `quot` gcd u (v ^ n)
  in if f' == one
     then v
     else v * squareFreePart (pthRoot f')

yun :: (Ring r, Eq r, Field r, DecidableZero r, DecidableUnits r, IntegralSemiring r)
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
      in if isZero (v' - one)
         then dic'
         else go (i+1) dic' v' w'

charUnipol :: forall r. Characteristic r => Unipol r -> Natural
charUnipol _ = char (Proxy :: Proxy r)

powerUnipol :: forall r. FiniteField r => Unipol r -> Natural
powerUnipol _ = power (Proxy :: Proxy r)

pthRoot :: (DecidableZero r, Ring r, Characteristic r) => Unipol r -> Unipol r
pthRoot f =
  let !p = charUnipol f
  in if p == 0
     then error "char R should be positive prime"
     else transformMonomial (SV.map (`P.div` fromIntegral p)) f

squareFreeDecomp :: (IntegralSemiring k, DecidableUnits k, Eq k,
                     Characteristic k, Field k, DecidableZero k)
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
factorise :: (Functor m, MonadRandom m, Eq k, DecidableUnits k, DecidableZero k, IntegralSemiring k, FiniteField k)
          => Unipol k -> m [(Unipol k, Natural)]
factorise f = do
  concat <$> mapM (\(r, h) -> map (,fromIntegral r) <$> factorSquareFree h) (IM.toList $  squareFreeDecomp f)

-- | @generateIrreducible p n@ generates irreducible polynomial over F_@p@ of degree @n@.
generateIrreducible :: (DecidableZero k, MonadRandom m, FiniteField k,
                        IntegralSemiring k, DecidableUnits k, Eq k)
                    => proxy k -> Natural -> m (Unipol k)
generateIrreducible p n =
  iterateUntil (\f -> all (\i -> one == gcd (varX^(order p^i) - varX) f ) [1.. n `div` 2]) $ do
    cs <- replicateM (fromIntegral n) $ uniform (elements p)
    let f = varX^n + sum [ injectCoeff c * (varX^i) | c <- cs | i <- [0..]]
    return f
