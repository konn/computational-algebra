{-# LANGUAGE ConstraintKinds, FlexibleContexts, FlexibleInstances  #-}
{-# LANGUAGE NoImplicitPrelude, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module AlgebraicPrelude
       (module AlgebraicPrelude,
        -- * Old Prelude's Numeric type classes and functions, without confliction
        P.Num(),P.Integral(),P.toInteger, P.Fractional (),
        P.Floating(..), P.RealFrac(..), P.RealFloat(..), realToFrac
       ) where
import           BasicPrelude             as AlgebraicPrelude hiding
                                                               (Floating (..),
                                                               Fractional (..),
                                                               Integral (..),
                                                               Num (..),
                                                               Rational,
                                                               Real (..),
                                                               RealFloat (..),
                                                               RealFrac (..),
                                                               fromShow, gcd,
                                                               getArgs,
                                                               getContents,
                                                               getLine, id,
                                                               interact, lcm,
                                                               lines, product,
                                                               putStr, putStrLn,
                                                               read, readFile,
                                                               show, subtract,
                                                               sum, unlines,
                                                               unwords, words,
                                                               (.), (\\), (^),
                                                               (^^))
import qualified Data.Ratio               as P
import           Numeric.Algebra          as AlgebraicPrelude hiding
                                                               (Order (..),
                                                               fromInteger, (^))
import qualified Numeric.Algebra          as NA
import           Numeric.Domain.Class     as AlgebraicPrelude
import           Numeric.Domain.Euclidean as AlgebraicPrelude
import           Numeric.Domain.GCD       as AlgebraicPrelude
import           Numeric.Domain.PID       as AlgebraicPrelude
import           Numeric.Domain.UFD       as AlgebraicPrelude
import           Numeric.Field.Fraction   as AlgebraicPrelude
import           Prelude                  as AlgebraicPrelude (Show (..),
                                                               ceiling, div,
                                                               floor,
                                                               getContents,
                                                               getLine, id,
                                                               interact, lines,
                                                               mod, putStr,
                                                               putStrLn,
                                                               readFile, show,
                                                               unlines, unwords,
                                                               words, (.))
import qualified Prelude                  as P

type Rational = Fraction Integer

infixr 8 ^, ^^

class (Ord (Norm a)) => Normed a where
  type Norm a
  norm :: a -> Norm a
  liftNorm :: Norm a -> a

instance Normed Double where
  type Norm Double = Double
  norm a = P.abs a
  liftNorm = id

instance Normed Int where
  type Norm Int = Int
  norm = P.abs
  liftNorm = id

instance Normed Integer where
  type Norm Integer = Integer
  norm = P.abs
  liftNorm = id

instance (Ord (Norm d), Euclidean d, Euclidean (Norm d), Normed d)
     =>  Normed (Fraction d) where
  type Norm (Fraction d) = Fraction (Norm d)
  norm f = norm (numerator f) % norm (denominator f)
  liftNorm f = liftNorm (numerator f) % liftNorm (denominator f)


abs :: Normed a => a -> a
abs = liftNorm . norm

-- | Specialised version of @'pow'@ which takes @'Natural'@s as a power.
(^) :: Unital r => r -> Natural -> r
(^) = pow

-- | The original power function @('NA.^')@ of @algebra@
(^^) :: Division r => r -> Integer -> r
(^^) = (NA.^)

{-# RULES
"negate/Ring" forall (x :: Ring a => a).
  P.negate x = NA.negate x

"minus/Ring" forall (x :: Ring a => a) y.
  x P.- y = x NA.- y

 #-}

ifThenElse :: Bool -> a -> a -> a
ifThenElse p t f = if p then t else f

-- | To work with Num literals.
fromInteger :: P.Num r => Integer -> r
fromInteger = P.fromInteger
{-# INLINE [1] fromInteger #-}
{-# RULES
"fromInteger/Integer"
  fromInteger = id
  #-}

-- | @algebra@ package's original @'NA.fromInteger'@.
fromInteger' :: Ring r => Integer -> r
fromInteger' = NA.fromInteger

fromRational :: DivisionRing r => P.Rational -> r
fromRational r = NA.fromInteger (P.numerator r) / NA.fromInteger (P.denominator r)
{-# INLINE [1] fromRational #-}
{-# RULES
"fromRational/Rational" [~1]
  fromRational = id
  #-}
