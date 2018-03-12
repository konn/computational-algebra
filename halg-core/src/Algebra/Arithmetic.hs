{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction #-}
module Algebra.Arithmetic
       (repeatedSquare, modPow, fermatTest, isPseudoPrime
       ) where
import           AlgebraicPrelude         hiding (div, mod)
import           Control.Lens             ((&), (+~), _1)
import           Control.Monad.Random     (MonadRandom, uniform)
import           Data.List                (elemIndex)
import           Numeric.Decidable.Zero   (isZero)
import           Numeric.Domain.Euclidean ()
import           Prelude                  (div, mod)
import qualified Prelude                  as P

data PrimeResult = Composite | ProbablyPrime | Prime
                 deriving (Read, Show, Eq, Ord)

-- | Calculates @n@-th power efficiently, using repeated square method.
repeatedSquare :: Multiplicative r => r -> Natural -> r
repeatedSquare a n =
  let bits = tail $ binRep n
  in foldl (\b nk -> if nk == 1 then b * b * a else b * b) a bits

binRep :: Natural -> [Natural]
binRep = flip go []
  where
    go 0 = id
    go k = go (k `div` 2) . ((k `mod` 2) :)

-- | Fermat-test for pseudo-primeness.
fermatTest :: MonadRandom m => Integer -> m PrimeResult
fermatTest 2 = return Prime
fermatTest n = do
  a <- uniform [2..n - 2]
  let b = modPow n (fromIntegral a) (fromIntegral $ n - 1 :: Natural)
  if b /= 1
    then return Composite
    else return ProbablyPrime

-- | @'modPow' x m p@ efficiently calculates @x ^ p `'mod'` m@.
modPow :: (P.Integral a, Euclidean r) => r -> r -> a -> r
modPow i p = go i one
  where
    go _ acc 0 = acc
    go b acc e = go ((b * b) `rem` p) (if e `mod` 2 == 1 then (acc * b) `rem` p else acc) (e `div` 2)

splitFactor :: Euclidean r => r -> r -> (Int, r)
splitFactor d n =
  let (q,r) = n `divide` d
  in if isZero q
     then (0, n)
     else splitFactor d r & _1 +~ 1

-- | @'isPseudoPrime' n@ tests if the given integer @n@ is pseudo prime.
--   It returns @'Left' p@ if @p < n@ divides @n@,
--   @'Right' 'True'@ if @n@ is pseudo-prime,
--   @'Right' 'False'@ if it is not pseudo-prime but no clue can be found.
isPseudoPrime :: MonadRandom m
              => Integer -> m (Either Integer Bool)
isPseudoPrime 2 = return $ Right True
isPseudoPrime 3 = return $ Right True
isPseudoPrime n = do
  a <- uniform [2..n P.- 2]
  let d = P.gcd a n
  return $ if d > 1
    then Left d
    else
    let (v, m) = splitFactor 2 (n-1)
        b0 = modPow n a m
        bs = take (v+1) $ iterate (\b -> b*b `mod` n) b0
    in if b0 == 1
       then Right True
       else case elemIndex 1 bs of
         Nothing -> Right False
         Just j ->
           let g = P.gcd (bs !! j - 1) n
           in if g == 1 || g == n then Right True else Left g

