{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude              #-}
{-# LANGUAGE NoMonomorphismRestriction, PolyKinds, TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances                                  #-}
module Algebra.Field.Galois.Internal (Conway(), buildInstance, parseLine) where
import           Algebra.Field.Finite
import           Algebra.Prelude            hiding (lex)
import           Data.Char                  (isDigit)
import           Data.Char                  (digitToInt)
import           Data.Reflection            (Reifies (..))
import qualified GHC.TypeLits               as TL
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax (lift)
import           Numeric                    (readInt)
import           Prelude                    (lex)

-- | Phantom type for conway polynomials
data Conway (p :: TL.Nat) (n :: TL.Nat)

parseLine :: String -> [(Integer, Integer, [Integer])]
parseLine ('[':xs) =
  [(p,n,poly) | (f, ',':rest) <- lex xs
              , (p, "") <- readInt 10 isDigit digitToInt f
              , (n, ',':ys) <- readInt 10 isDigit digitToInt rest
              , (poly, _)    <- readList ys
              ]
parseLine _ = []

plusOp :: ExpQ -> ExpQ -> ExpQ
plusOp e f = infixApp e [| (+) |] f

toPoly :: [Integer] -> ExpQ
toPoly as =
  foldl1 plusOp $ zipWith (\i c -> [| injectCoeff (modNat $(litE $ integerL c)) * varX ^ $(lift i) |]) [0 :: Integer ..] as

buildInstance :: (Integer, Integer, [Integer]) -> DecsQ
buildInstance (p,n,cs) =
  let tp = litT $ numTyLit p
      tn = litT $ numTyLit n
  in [d| instance Reifies (Conway $tp $tn)
                          (OrderedPolynomial (F $tp) Grevlex 1) where
           reflect _ = $(toPoly cs)
           {-# INLINE reflect #-}
       |]
