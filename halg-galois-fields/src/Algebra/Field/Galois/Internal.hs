{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances              #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude                  #-}
{-# LANGUAGE NoMonomorphismRestriction, PolyKinds, ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell, UndecidableInstances                     #-}
module Algebra.Field.Galois.Internal
       (ConwayPolynomial(..),
        Conway,
        buildInstance,
        parseLine
       ) where
import           Algebra.Field.Prime
import           Algebra.Prelude.Core               hiding (lex, lift)
import           Algebra.Ring.Polynomial.Univariate (Unipol)
import           Data.Char                          (isDigit)
import           Data.Char                          (digitToInt)
import           Data.Reflection
import qualified GHC.TypeLits                       as TL
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax         (lift)
import           Numeric                            (readInt)
import           Prelude                            (lex)

-- | Type-class to provide the dictionary for Conway polynomials
class ConwayPolynomial (p :: TL.Nat) (n :: TL.Nat) where
  conwayPolynomial :: proxy p -> proxy n -> Unipol (F p)

-- | Empty tag to reify Conway polynomial to type-level
data Conway p n

-- instance  {-# OVERLAPPABLE #-} (KnownNat p, KnownNat n) => ConwayPolynomial p n where
--   conwayPolynomial _ _ = undefined

instance (ConwayPolynomial p n) => Reifies (Conway p n) (Unipol (F p)) where
  reflect _ = conwayPolynomial (Proxy :: Proxy p) (Proxy :: Proxy n)

parseLine :: String -> [(Integer, Integer, [Integer])]
parseLine ('[':xs) =
  [(p,n,poly) | (f, ',':rest) <- lex xs
              , (p, "") <- readInt 10 isDigit digitToInt f
              , (n, ',':ys) <- readInt 10 isDigit digitToInt rest
              , (poly, _)    <- readList ys
              ]
parseLine _ = []

plusOp :: ExpQ -> ExpQ -> ExpQ
plusOp e = infixApp e [| (+) |]

toPoly :: [Integer] -> ExpQ
toPoly as =
  foldl1 plusOp $
  zipWith (\i c -> [| injectCoeff (modNat $(litE $ integerL c)) * var 0 ^ $(lift i) |])
  [0 :: Integer ..] as

buildInstance :: (Integer, Integer, [Integer]) -> DecsQ
buildInstance (p,n,cs) =
  let tp = litT $ numTyLit p
      tn = litT $ numTyLit n
  in [d| instance {-# OVERLAPPING #-} ConwayPolynomial $tp $tn where
           conwayPolynomial _ _ = $(toPoly cs)
           {-# INLINE conwayPolynomial #-}
       |]
