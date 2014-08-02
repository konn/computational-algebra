{-# LANGUAGE BangPatterns, FlexibleContexts, MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude, OverloadedStrings, PolyKinds       #-}
{-# LANGUAGE ScopedTypeVariables                                   #-}
module Algebra.Ring.Polynomial.Factorize where
import           Algebra.Field.Finite
import           Algebra.Prelude
import           Algebra.Ring.Polynomial.Quotient
import           Control.Applicative              ((<|>))
import           Control.Applicative              ((<*>))
import           Control.Applicative              ((<$>))
import           Control.Monad                    (replicateM)
import           Control.Monad                    (guard)
import           Control.Monad.Loops              (untilJust)
import           Control.Monad.Random             (MonadRandom)
import           Control.Monad.Random             (uniform)
import           Data.Proxy                       (Proxy (..))
import           Data.Reflection                  (Reifies)
import           Data.Reflection                  (reflect)
import           Data.Type.Natural                hiding (one)
import           Data.Type.Ordinal                (Ordinal (..))
import qualified Data.Vector.Sized                as SV
import           Prelude                          (div)
import           Prelude                          (mod)
import           Prelude                          (toInteger)
import qualified Prelude                          as P

type Unipol r = OrderedPolynomial r Grevlex One

-- | @distinctDegFactor f@ computes the distinct-degree decomposition of the given
--   square-free polynomial over finite field @f@.
distinctDegFactor :: forall p. Reifies p Natural
                  => Unipol (F p)     -- ^ Square-free polynomial over finite field.
                  -> [(Natural, Unipol (F p))]   -- ^ Distinct-degree decomposition.
distinctDegFactor f0 = zip [1..] $ go id varX f0 []
  where
    go gs h f =
      let h' = modPow h (reflect (Proxy :: Proxy p)) f
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

binRep :: Natural -> [Natural]
binRep = flip go []
  where
    go 0 = id
    go k = go (k `div` 2) . ((k `mod` 2) :)

repeatedSquare :: Multiplicative r => r -> Natural -> r
repeatedSquare a n =
  let bits = tail $ binRep n
  in go a bits
  where
    go b []        = b
    go b (nk : ns) =
      go (if nk == 1 then (b*b*a) else b*b) ns

equalDegreeSplitM :: forall p m. (MonadRandom m, Reifies p Natural)
                 => Unipol (F p)
                 -> Natural
                 -> m (Maybe (Unipol (F p)))
equalDegreeSplitM f d
  | even (reflect (Proxy :: Proxy p)) = return Nothing
  | fromIntegral (totalDegree' f) `mod` d /= 0 = return Nothing
  | otherwise = do
    let q = reflect (Proxy :: Proxy p)
        n = totalDegree' f
        els = map withModulo [0..pred q]
    e <- uniform [1..n-1]
    c <- uniform $ tail els
    cs <- replicateM (e-1) $ uniform els
    let a = injectCoeff c * varX ^ fromIntegral e +
            sum (zipWith (*) (map injectCoeff (c:cs)) [varX ^ l | l <-[0..]])
            `asTypeOf` f
    let g1 = gcd a f
    return $ (guard (g1 /= one) >> return g1)
         <|> do let b = modPow a ((pred q^d)`div`2) f
                    g2 = gcd (b-1) f
                guard (g2 /= one && g2 /= f)
                return g2

equalDegreeFactorM :: (Reifies p Natural, MonadRandom m)
                   => Unipol (F p) -> Natural -> m [Unipol (F p)]
equalDegreeFactorM f d = go f >>= \a -> return (a [])
  where
    go h = do
      if fromIntegral (totalDegree' h) == d
        then return (h:)
        else do
        g <- untilJust (equalDegreeSplitM h d)
        l <- go g
        r <- go (f `quot` g)
        return $ l . r

factorSquareFree :: (Reifies p Natural, MonadRandom m, Functor m) => Unipol (F p) -> m [Unipol (F p)]
factorSquareFree f =
   concat <$> mapM (uncurry $ flip equalDegreeFactorM) (filter ((/= 1) . snd) $ distinctDegFactor f)



squareFreePart :: forall p. (Reifies p Natural) => Unipol (F p) -> Unipol (F p)
squareFreePart f =
  let !n = fromIntegral $ totalDegree' f
      u  = gcd f (diff 0 f)
      v  = f `quot` u
      p  = fromIntegral $ reflect (Proxy :: Proxy p)
      f' = u `quot` gcd u (v ^ n)
  in if f' == one
     then v
     else v * (squareFreePart $ transformMonomial (SV.map (`P.div` p)) f')

sqfSub :: forall p. (Reifies p Natural) => Unipol (F p) -> Unipol (F p)
sqfSub f =
  let !n = fromIntegral $ totalDegree' f
      u  = gcd f (diff 0 f)
      v  = f `quot` u
      p  = fromIntegral $ reflect (Proxy :: Proxy p)
      f' = u `quot` gcd u (v ^ n)
  in f'

