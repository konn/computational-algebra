{-# LANGUAGE ConstraintKinds, FlexibleContexts, FlexibleInstances      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses         #-}
{-# LANGUAGE NoImplicitPrelude, NoRebindableSyntax, StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, UndecidableInstances       #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | This module provides drop-in replacement for @'Prelude'@ module in base package,
--   based on algebraic hierarchy provided by
--   <https://hackage.haskell.org/package/algebra algebra> package.
--   You can use this module with @NoImplicitPrelude@ language option.
--
--  This module implicitly exports following modules:
--
--      * "Numeric.Algebra" module, except
--
--          * @'NA.fromInteger'@:
--             this module exports Prelude's @'fromInteger'@ to make number literals
--             work properly.
--            For @'NA.fromInteger'@ from @algebra@ package, use @'fromInteger''@.
--
--          * @('NA.^')@ is renamed to @('^^')@, and @('^')@ is redefined as @'NA.pow'@.
--
--      * The module "Numeric.Algebra.Unital.UnitNormalForm", except for @'NA.normalize'@;
--      hence its name is too general, we export it as @'normaliseUnit'@.
--
--      * Following modules are exported as-is:
--
--            * "Numeric.Decidable.Associates"
--            * "Numeric.Decidable.Units"
--            * "Numeric.Decidable.Zero"
--            * "Numeric.Domain.Class"
--            * "Numeric.Domain.Euclidean"
--            * "Numeric.Domain.GCD"
--            * "Numeric.Domain.Integral"
--            * "Numeric.Domain.PID"
--            * "Numeric.Domain.UFD"
--            * "Numeric.Field.Fraction"
--            * "Numeric.Semiring.ZeroProduct"
--
--      * Non-numeric part of this module is almost same as "BasicPrelude".
--        But the following combinators are not generalized from "Prelude":
--
--          * @'String'@-specific functions: @'getArgs'@, @'getContents'@,
--          @'getLine'@, @'interact'@, @'putStr'@, @'putStrLn'@,
--          @'read'@, @'readFile'@, @'writeFile'@,  @'lines'@, @'unlines'@,
--          @'words'@ and @'unwords'@.
--
--          * @('.')@ is just a function composition; not a Categorical composition.

module AlgebraicPrelude
       (module AlgebraicPrelude,
        -- * Old Prelude's Numeric type classes and functions, without confliction
        P.Num(abs,signum),P.Integral(),P.toInteger, P.Real(..), P.Fractional (),
        P.Floating(..), P.RealFrac(..), P.RealFloat(..),
       ) where
import           BasicPrelude                          as AlgebraicPrelude hiding
                                                                            (Floating (..),
                                                                            Fractional (..),
                                                                            Integral (..),
                                                                            Num (..),
                                                                            Rational,
                                                                            Real (..),
                                                                            RealFloat (..),
                                                                            RealFrac (..),
                                                                            fromShow,
                                                                            gcd,
                                                                            getArgs,
                                                                            getContents,
                                                                            getLine,
                                                                            id,
                                                                            interact,
                                                                            lcm,
                                                                            lines,
                                                                            product,
                                                                            putStr,
                                                                            putStrLn,
                                                                            read,
                                                                            readFile,
                                                                            show,
                                                                            subtract,
                                                                            sum,
                                                                            unlines,
                                                                            unwords,
                                                                            words,
                                                                            writeFile,
                                                                            (.),
                                                                            (\\),
                                                                            (^),
                                                                            (^^))
import qualified Control.Lens.TH                       as L
import qualified Data.Ratio                            as P
import qualified Data.Semigroup                        as Semi
import           Foreign.Storable                      (Storable)
import           GHC.OverloadedLabels                  as AlgebraicPrelude
import           Numeric.Algebra                       as AlgebraicPrelude hiding
                                                                            (Order (..),
                                                                            fromInteger,
                                                                            (^))
import qualified Numeric.Algebra                       as NA
import           Numeric.Algebra.Unital.UnitNormalForm as AlgebraicPrelude hiding
                                                                            (normalize)
import qualified Numeric.Algebra.Unital.UnitNormalForm as NA
import           Numeric.Decidable.Associates          as AlgebraicPrelude
import           Numeric.Decidable.Units               as AlgebraicPrelude
import           Numeric.Decidable.Zero                as AlgebraicPrelude
import           Numeric.Domain.Class                  as AlgebraicPrelude
import           Numeric.Domain.Euclidean              as AlgebraicPrelude
import           Numeric.Domain.GCD                    as AlgebraicPrelude
import           Numeric.Domain.Integral               as AlgebraicPrelude
import           Numeric.Domain.PID                    as AlgebraicPrelude
import           Numeric.Domain.UFD                    as AlgebraicPrelude
import           Numeric.Field.Fraction                as AlgebraicPrelude
import           Numeric.Semiring.ZeroProduct          as AlgebraicPrelude
import           Prelude                               as AlgebraicPrelude (Num, Show (..),
                                                                            ceiling,
                                                                            div,
                                                                            floor,
                                                                            getContents,
                                                                            getLine,
                                                                            id,
                                                                            interact,
                                                                            lines,
                                                                            mod,
                                                                            putStr,
                                                                            putStrLn,
                                                                            readFile,
                                                                            show,
                                                                            unlines,
                                                                            unwords,
                                                                            words,
                                                                            writeFile,
                                                                            (.))
import qualified Prelude                               as P
-- * Basic types and renamed operations
-- | We use @'Fraction'@ instead of @'Ratio'@ for consistency.
type Rational = Fraction Integer

infixr 8 ^, ^^

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

normaliseUnit :: UnitNormalForm r => r -> r
normaliseUnit = NA.normalize

-- | Specialised version of @'pow'@ which takes @'Natural'@s as a power.
(^) :: Unital r => r -> Natural -> r
(^) = pow

-- | The original power function @('NA.^')@ of @algebra@
(^^) :: Division r => r -> Integer -> r
(^^) = (NA.^)

-- * Combinator to use with @RebindableSyntax@ extensions.
ifThenElse :: Bool -> a -> a -> a
ifThenElse p t f = if p then t else f

-- * Wrapper types for conversion between @'Num'@ family
--   and algebraic hierarchy provided by @algebra@.

-- | Wrapping Prelude's numerical types to treat with
--   @'Numeric.Algebra'@ hierachy.
--
--   For @'Field'@ or @'Euclidean'@ instances, see @'WrapIntegral'@ and @'WrapField'@.
--
--  __N.B.__ This type provides a mean to convert from @'Num'@s
--           to @'Ring'@s, but there is no guarantee that
--           @'WrapNum' a@ is actually ring.
--           For example, due to precision limitation,
--           @'WrapPreldue' 'Double'@ even fails to be semigroup!
--           For another simpler example, even though  @'Natural'@ comes
--           with @'Num'@ instance, but it doesn't support @'negate'@,
--           so it cannot be @'Group'@.
newtype WrapNum a = WrapNum { unwrapNum :: a }
                      deriving (Read, Show, Eq, Ord, P.Num, Storable)

instance (P.Num a) => Additive (WrapNum a) where
  WrapNum a + WrapNum b = WrapNum (a P.+ b)
  {-# INLINE (+) #-}
  sinnum1p n (WrapNum a) = WrapNum ((1 P.+ fromIntegral n) P.* a)
  {-# INLINE sinnum1p #-}

instance (P.Num a) => LeftModule Natural (WrapNum a) where
  n .* WrapNum r = WrapNum (P.fromIntegral n P.* r)
  {-# INLINE (.*) #-}

instance (P.Num a) => RightModule Natural (WrapNum a) where
  WrapNum r *. n = WrapNum (r P.* P.fromIntegral n)
  {-# INLINE (*.) #-}

instance (P.Num a) => Monoidal (WrapNum a) where
  zero = WrapNum (P.fromInteger 0)
  {-# INLINE zero #-}
  sinnum n (WrapNum a) = WrapNum (fromIntegral n P.* a)
  {-# INLINE sinnum #-}

instance (P.Num a) => LeftModule Integer (WrapNum a) where
  n .* WrapNum r = WrapNum (P.fromIntegral n P.* r)
  {-# INLINE (.*) #-}

instance (P.Num a) => RightModule Integer (WrapNum a) where
  WrapNum r *. n = WrapNum (r P.* P.fromIntegral n)
  {-# INLINE (*.) #-}

instance (P.Num a) => Group (WrapNum a) where
  negate (WrapNum a) = WrapNum $ P.negate a
  {-# INLINE negate #-}
  WrapNum a - WrapNum b = WrapNum (a P.- b)
  {-# INLINE (-) #-}
  subtract (WrapNum a) (WrapNum b) = WrapNum (P.subtract a b)
  {-# INLINE subtract #-}
  times n (WrapNum a) = WrapNum $ fromIntegral n P.* a
  {-# INLINE times #-}

instance (P.Num a) => Multiplicative (WrapNum a) where
  WrapNum p * WrapNum q = WrapNum (p P.* q)
  {-# INLINE (*) #-}
  pow1p (WrapNum p) n = WrapNum (p P.^ (n + 1))
  {-# INLINE pow1p #-}

instance (P.Num a) => Unital (WrapNum a) where
  one = WrapNum $ P.fromInteger 1
  {-# INLINE one #-}
  pow (WrapNum a) n = WrapNum $ a P.^ n
  {-# INLINE pow #-}

instance P.Num a => Abelian (WrapNum a)
instance P.Num a => Semiring (WrapNum a)
instance P.Num a => Rig (WrapNum a) where
  fromNatural = WrapNum . P.fromIntegral
  {-# INLINE fromNatural #-}
instance P.Num a => Ring (WrapNum a) where
  fromInteger = WrapNum . P.fromInteger
  {-# INLINE fromInteger #-}

instance P.Num a => Commutative (WrapNum a)

instance (P.Num a, Eq a) => DecidableZero (WrapNum a) where
  isZero (WrapNum a) = a == 0
  {-# INLINE isZero #-}

-- | Similar to @'WrapNum'@, but produces @'Field'@ instances from
--   @'Fractional'@s.
--
--   See also: @'WrapIntegral'@ and @'WrapNum'@.
newtype WrapFractional a = WrapFractional { unwrapFractional :: a }
  deriving (Read, Show, Eq, Ord, Num, Enum, P.Real, P.Fractional, Storable)

instance (P.Num a) => Additive (WrapFractional a) where
  WrapFractional a + WrapFractional b = WrapFractional (a P.+ b)
  {-# INLINE (+) #-}
  sinnum1p n (WrapFractional a) = WrapFractional ((1 P.+ fromIntegral n) P.* a)
  {-# INLINE sinnum1p #-}

instance (P.Num a) => LeftModule Natural (WrapFractional a) where
  n .* WrapFractional r = WrapFractional (P.fromIntegral n P.* r)
  {-# INLINE (.*) #-}

instance (P.Num a) => RightModule Natural (WrapFractional a) where
  WrapFractional r *. n = WrapFractional (r P.* P.fromIntegral n)
  {-# INLINE (*.) #-}

instance (P.Num a) => Monoidal (WrapFractional a) where
  zero = WrapFractional (P.fromInteger 0)
  {-# INLINE zero #-}
  sinnum n (WrapFractional a) = WrapFractional (fromIntegral n P.* a)
  {-# INLINE sinnum #-}

instance (P.Num a) => LeftModule Integer (WrapFractional a) where
  n .* WrapFractional r = WrapFractional (P.fromIntegral n P.* r)
  {-# INLINE (.*) #-}

instance (P.Num a) => RightModule Integer (WrapFractional a) where
  WrapFractional r *. n = WrapFractional (r P.* P.fromIntegral n)
  {-# INLINE (*.) #-}

instance (P.Num a) => Group (WrapFractional a) where
  negate (WrapFractional a) = WrapFractional $ P.negate a
  {-# INLINE negate #-}
  WrapFractional a - WrapFractional b = WrapFractional (a P.- b)
  {-# INLINE (-) #-}
  subtract (WrapFractional a) (WrapFractional b) = WrapFractional (P.subtract a b)
  {-# INLINE subtract #-}
  times n (WrapFractional a) = WrapFractional $ fromIntegral n P.* a
  {-# INLINE times #-}

instance (P.Num a) => Multiplicative (WrapFractional a) where
  WrapFractional p * WrapFractional q = WrapFractional (p P.* q)
  {-# INLINE (*) #-}
  pow1p (WrapFractional p) n = WrapFractional (p P.^ (n + 1))
  {-# INLINE pow1p #-}

instance (P.Num a) => Unital (WrapFractional a) where
  one = WrapFractional $ P.fromInteger 1
  {-# INLINE one #-}
  pow (WrapFractional a) n = WrapFractional $ a P.^ n
  {-# INLINE pow #-}

instance P.Num a => Abelian (WrapFractional a)
instance P.Num a => Semiring (WrapFractional a)
instance P.Num a => Rig (WrapFractional a) where
  fromNatural = WrapFractional . P.fromIntegral
  {-# INLINE fromNatural #-}
instance P.Num a => Ring (WrapFractional a) where
  fromInteger = WrapFractional . P.fromInteger
  {-# INLINE fromInteger #-}

instance P.Num a => Commutative (WrapFractional a)

instance (P.Num a, Eq a) => DecidableZero (WrapFractional a) where
  isZero (WrapFractional a) = a == 0
  {-# INLINE isZero #-}

instance P.Fractional a => Division (WrapFractional a) where
  recip = WrapFractional . P.recip . unwrapFractional
  {-# INLINE recip #-}
  WrapFractional a / WrapFractional b = WrapFractional $ a P./ b
  {-# INLINE (/) #-}
  WrapFractional a \\ WrapFractional b = WrapFractional $ P.recip a P.* b
  {-# INLINE (\\) #-}
  WrapFractional a ^ n = WrapFractional (a P.^^ n)
  {-# INLINE (^) #-}

instance (Eq a, P.Fractional a) => ZeroProductSemiring (WrapFractional a)
instance (Eq a, P.Fractional a) => DecidableUnits (WrapFractional a) where
  isUnit (WrapFractional r) = r /= 0
  {-# INLINE isUnit #-}

  recipUnit (WrapFractional r) =
    if r == 0
    then Nothing
    else Just (WrapFractional $ P.recip r)
  {-# INLINE recipUnit #-}

instance (Eq a, P.Fractional a) => DecidableAssociates (WrapFractional a) where
  isAssociate (WrapFractional a) (WrapFractional b) =
    (a == 0 && b == 0) || (a /= 0 && b /= 0)
  {-# INLINE isAssociate #-}

instance (Eq a, P.Fractional a) => UnitNormalForm (WrapFractional a)
instance (Eq a, P.Fractional a) => IntegralDomain (WrapFractional a)
instance (Eq a, P.Fractional a) => GCDDomain (WrapFractional a)
instance (Eq a, P.Fractional a) => Euclidean (WrapFractional a)
instance (Eq a, P.Fractional a) => PID (WrapFractional a)
instance (Eq a, P.Fractional a) => UFD (WrapFractional a)

-- | Similar to @'WrapNum'@, but produces @'Euclidean'@ instances from
--   @'Integral'@s.
--
--   See also: @'WrapFractional'@ and @'WrapNum'@.
newtype WrapIntegral a = WrapIntegral { unwrapIntegral :: a }
  deriving (Read, Show, Eq, Ord, P.Num, P.Real, P.Enum, P.Integral, Storable)

instance (P.Num a) => Additive (WrapIntegral a) where
  WrapIntegral a + WrapIntegral b = WrapIntegral (a P.+ b)
  {-# INLINE (+) #-}
  sinnum1p n (WrapIntegral a) = WrapIntegral ((1 P.+ fromIntegral n) P.* a)
  {-# INLINE sinnum1p #-}

instance (P.Num a) => LeftModule Natural (WrapIntegral a) where
  n .* WrapIntegral r = WrapIntegral (P.fromIntegral n P.* r)
  {-# INLINE (.*) #-}

instance (P.Num a) => RightModule Natural (WrapIntegral a) where
  WrapIntegral r *. n = WrapIntegral (r P.* P.fromIntegral n)
  {-# INLINE (*.) #-}

instance (P.Num a) => Monoidal (WrapIntegral a) where
  zero = WrapIntegral (P.fromInteger 0)
  {-# INLINE zero #-}
  sinnum n (WrapIntegral a) = WrapIntegral (fromIntegral n P.* a)
  {-# INLINE sinnum #-}

instance (P.Num a) => LeftModule Integer (WrapIntegral a) where
  n .* WrapIntegral r = WrapIntegral (P.fromIntegral n P.* r)
  {-# INLINE (.*) #-}

instance (P.Num a) => RightModule Integer (WrapIntegral a) where
  WrapIntegral r *. n = WrapIntegral (r P.* P.fromIntegral n)
  {-# INLINE (*.) #-}

instance (P.Num a) => Group (WrapIntegral a) where
  negate (WrapIntegral a) = WrapIntegral $ P.negate a
  {-# INLINE negate #-}
  WrapIntegral a - WrapIntegral b = WrapIntegral (a P.- b)
  {-# INLINE (-) #-}
  subtract (WrapIntegral a) (WrapIntegral b) = WrapIntegral (P.subtract a b)
  {-# INLINE subtract #-}
  times n (WrapIntegral a) = WrapIntegral $ fromIntegral n P.* a
  {-# INLINE times #-}

instance (P.Num a) => Multiplicative (WrapIntegral a) where
  WrapIntegral p * WrapIntegral q = WrapIntegral (p P.* q)
  {-# INLINE (*) #-}
  pow1p (WrapIntegral p) n = WrapIntegral (p P.^ (n + 1))
  {-# INLINE pow1p #-}

instance (P.Num a) => Unital (WrapIntegral a) where
  one = WrapIntegral $ P.fromInteger 1
  {-# INLINE one #-}
  pow (WrapIntegral a) n = WrapIntegral $ a P.^ n
  {-# INLINE pow #-}

instance P.Num a => Abelian (WrapIntegral a)
instance P.Num a => Semiring (WrapIntegral a)
instance P.Num a => Rig (WrapIntegral a) where
  fromNatural = WrapIntegral . P.fromIntegral
  {-# INLINE fromNatural #-}
instance P.Num a => Ring (WrapIntegral a) where
  fromInteger = WrapIntegral . P.fromInteger
  {-# INLINE fromInteger #-}

instance P.Num a => Commutative (WrapIntegral a)

instance (P.Num a, Eq a) => DecidableZero (WrapIntegral a) where
  isZero (WrapIntegral a) = a == 0
  {-# INLINE isZero #-}

instance (Eq a, P.Integral a) => ZeroProductSemiring (WrapIntegral a)
instance (Eq a, P.Integral a) => DecidableUnits (WrapIntegral a) where
  isUnit (WrapIntegral r) = r == 1 || r == P.negate 1
  {-# INLINE isUnit #-}

  recipUnit (WrapIntegral r) =
    if isUnit (WrapIntegral r)
    then Nothing
    else Just (WrapIntegral r)
  {-# INLINE recipUnit #-}

instance (Eq a, P.Integral a) => DecidableAssociates (WrapIntegral a) where
  isAssociate (WrapIntegral a) (WrapIntegral b) = P.abs a == P.abs b
  {-# INLINE isAssociate #-}

instance (Eq a, P.Integral a) => UnitNormalForm (WrapIntegral a) where
  splitUnit (WrapIntegral 0) = (WrapIntegral 1, WrapIntegral 0)
  splitUnit (WrapIntegral a) = (WrapIntegral $ P.signum a, WrapIntegral $ P.abs a)
  {-# INLINE splitUnit #-}

instance (Eq a, P.Integral a) => IntegralDomain (WrapIntegral a)
instance (Eq a, P.Integral a) => GCDDomain (WrapIntegral a) where
  gcd (WrapIntegral a) (WrapIntegral b) = WrapIntegral (P.gcd a b)
  {-# INLINE gcd #-}

  lcm (WrapIntegral a) (WrapIntegral b) = WrapIntegral (P.lcm a b)
  {-# INLINE lcm #-}

instance (Eq a, P.Integral a) => Euclidean (WrapIntegral a) where
  divide (WrapIntegral f) (WrapIntegral g) =
    let (q, r) = P.divMod f g
    in (WrapIntegral q, WrapIntegral r)
  {-# INLINE divide #-}
  degree (WrapIntegral 0) = Nothing
  degree (WrapIntegral a) = Just $ P.fromIntegral (P.abs a)
  {-# INLINE degree #-}

  quot (WrapIntegral a) (WrapIntegral b) = WrapIntegral $ P.div a b
  {-# INLINE quot #-}
  rem  (WrapIntegral a) (WrapIntegral b) = WrapIntegral $ P.mod a b
  {-# INLINE rem #-}

instance (Eq a, P.Integral a) => PID (WrapIntegral a)
instance (Eq a, P.Integral a) => UFD (WrapIntegral a)

-- | Turning types from @'Numeric.Algebra'@ into Prelude's Num instances.
--
--   N.B. Since @'Real'@'s @'toRational'@ constraint is too tight,
--        we won't provide the inverse of @'WrapIntegral'@ and
--        provide @'Fractional'@ instance only.
newtype WrapAlgebra a = WrapAlgebra { unwrapAlgebra :: a }
                      deriving ( Read, Show, Eq, Ord, Additive
                               , Unital, Multiplicative, Abelian
                               , Commutative, Semiring, Rig
                               , Ring, DecidableUnits, UnitNormalForm
                               , DecidableZero, Euclidean, Division
                               , PID , UFD, DecidableAssociates
                               , IntegralDomain, GCDDomain
                               , ZeroProductSemiring, Storable)

deriving instance LeftModule Natural a => LeftModule Natural (WrapAlgebra a)
deriving instance RightModule Natural a => RightModule Natural (WrapAlgebra a)
deriving instance LeftModule Integer a => LeftModule Integer (WrapAlgebra a)
deriving instance RightModule Integer a => RightModule Integer (WrapAlgebra a)
deriving instance Monoidal a => Monoidal (WrapAlgebra a)
deriving instance Group    a => Group    (WrapAlgebra a)

instance (Ring a, UnitNormalForm a) => P.Num (WrapAlgebra a) where
  WrapAlgebra a + WrapAlgebra b = WrapAlgebra $ a NA.+ b
  {-# INLINE (+) #-}
  WrapAlgebra a - WrapAlgebra b = WrapAlgebra $ a NA.- b
  {-# INLINE (-) #-}
  WrapAlgebra a * WrapAlgebra b = WrapAlgebra $ a NA.* b
  {-# INLINE (*) #-}
  fromInteger = WrapAlgebra . NA.fromInteger
  {-# INLINE fromInteger #-}
  signum = WrapAlgebra . leadingUnit . unwrapAlgebra
  {-# INLINE signum #-}
  abs    = WrapAlgebra . normaliseUnit . unwrapAlgebra
  {-# INLINE abs #-}
  negate = WrapAlgebra . negate . unwrapAlgebra
  {-# INLINE negate #-}

instance (DivisionRing a, UnitNormalForm a) => P.Fractional (WrapAlgebra a) where
  WrapAlgebra a / WrapAlgebra b = WrapAlgebra (a / b)
  {-# INLINE (/) #-}
  recip (WrapAlgebra a) = WrapAlgebra (recip a)
  {-# INLINE recip #-}
  fromRational = WrapAlgebra . fromRational
  {-# INLINE fromRational #-}

instance Euclidean a => P.Num (Fraction a) where
  {-# SPECIALISE instance P.Num (Fraction Integer) #-}
  (+) = (NA.+)
  (-) = (NA.-)
  negate = NA.negate
  (*) = (NA.*)
  fromInteger = NA.fromInteger
  abs = normaliseUnit
  signum = leadingUnit

instance Euclidean d => P.Fractional (Fraction d) where
  {-# SPECIALISE instance P.Fractional (Fraction Integer) #-}
  fromRational r = fromInteger' (P.numerator r) % fromInteger' (P.denominator r)
  recip = NA.recip
  (/) = (NA./)

-- | @'Monoid'@ instances for @'Additive'@s.
--   N.B. Unlike @'WrapNum'@, @'P.Num'@ instance is
--   just inhereted from the unwrapped data.
newtype Add a = Add { runAdd :: a }
              deriving (Read, Show, Eq, Ord, P.Num, Additive, Abelian, Storable)

deriving instance LeftModule Natural a => LeftModule Natural (Add a)
deriving instance RightModule Natural a => RightModule Natural (Add a)
deriving instance LeftModule Integer a => LeftModule Integer (Add a)
deriving instance RightModule Integer a => RightModule Integer (Add a)
deriving instance Monoidal a => Monoidal (Add a)


instance Additive a => Semi.Semigroup (Add a) where
  Add a <> Add b = Add (a NA.+ b)
  {-# INLINE (<>) #-}

  sconcat = Add . sum1 . map runAdd
  {-# INLINE sconcat #-}

  stimes n  = Add . sinnum1p (P.fromIntegral n P.- 1) . runAdd
  {-# INLINE stimes #-}

instance Monoidal a => Monoid (Add a) where
  mappend = (Semi.<>)
  {-# INLINE mappend #-}
  mempty = Add zero
  {-# INLINE mempty #-}
  mconcat = Add . sum . map runAdd
  {-# INLINE mconcat #-}

-- | @'Monoid'@ instances for @'Additive'@s.
--   N.B. Unlike @'WrapNum'@, @'P.Num'@ instance is
--   just inhereted from the unwrapped data.
newtype Mult a = Mult { runMult :: a }
              deriving (Read, Show, Eq, Ord, P.Num,
                        Multiplicative, Unital, Commutative, Storable)

instance Multiplicative a => Semi.Semigroup (Mult a) where
  Mult a <> Mult b = Mult (a NA.* b)
  {-# INLINE (<>) #-}

  sconcat = Mult . product1 . map runMult
  {-# INLINE sconcat #-}

  stimes n = Mult . flip pow1p (P.fromIntegral n P.- 1) . runMult
  {-# INLINE stimes #-}

instance Unital a => Monoid (Mult a) where
  mappend = (Semi.<>)
  {-# INLINE mappend #-}
  mempty = Mult one
  {-# INLINE mempty #-}
  mconcat = Mult . product . map runMult
  {-# INLINE mconcat #-}

L.makeWrapped ''WrapNum
L.makeWrapped ''WrapIntegral
L.makeWrapped ''WrapFractional
L.makeWrapped ''WrapAlgebra
L.makeWrapped ''Add
L.makeWrapped ''Mult

{-# ANN module "Hlint: ignore Redundant fromInteger" #-}
