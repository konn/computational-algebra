{-# LANGUAGE DataKinds, NoImplicitPrelude, NoMonomorphismRestriction, UndecidableInstances #-}
{-# LANGUAGE PolyKinds, TemplateHaskell, FlexibleInstances, MultiParamTypeClasses, EmptyDataDecls          #-}
module Algebra.Field.Galois.Internal (Conway(), buildInstance, parseLine) where
import Algebra.Field.Finite
import Algebra.Prelude            hiding (lex)
import Data.Char                  (isDigit)
import Data.Char                  (digitToInt)
import Data.Type.Natural
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (lift)
import Numeric                    (readInt)
import Prelude                    (lex)
import Data.Reflection (Reifies (..))

-- | Phantom type for conway polynomials
data Conway p n

parseLine :: String -> [(Integer, Integer, [Integer])]
parseLine ('[':xs) =
  [(p,n,poly) | (f, ',':rest) <- lex xs
              , (p, "") <- readInt 10 isDigit digitToInt f
              , (n, ',':ys) <- readInt 10 isDigit digitToInt rest
              , (poly, _)    <- readList ys
              ]
parseLine _ = []

toNatType :: Integer -> TypeQ
toNatType 0 = [t| Z |]
toNatType n = appT [t| S |] (toNatType $ n - 1)

plusOp :: ExpQ -> ExpQ -> ExpQ
plusOp e f = infixApp e [| (+) |] f

toPoly :: [Integer] -> ExpQ
toPoly as =
  foldl1 plusOp $ zipWith (\i c -> [| injectCoeff (modNat $(litE $ integerL c)) * varX ^ $(lift i) |]) [0 :: Integer ..] as

buildInstance :: (Integer, Integer, [Integer]) -> DecsQ
buildInstance (p,n,cs) =
  let tp = toNatType p
      tn = toNatType n
  in [d| instance Reifies (Conway $tp $tn)
                          (OrderedPolynomial (F $tp) Grevlex (S Z)) where
           reflect _ = $(toPoly cs)
           {-# INLINE reflect #-}
       |]
