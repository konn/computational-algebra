{-# LANGUAGE BangPatterns, ScopedTypeVariables, ViewPatterns #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Algebra.Algorithms.Groebner.Signature (f5) where
import           Algebra.Prelude.Core         hiding (Vector)
import           Control.Lens                 hiding ((.=))
import           Control.Monad.Loops
import           Control.Monad.ST.Combinators
import           Control.Parallel.Strategies
import qualified Data.Coerce                  as DC
import qualified Data.Heap                    as H
import           Data.Maybe                   (fromJust)
import           Data.Monoid                  (First (..))
import           Data.Semigroup               hiding (First, getFirst, (<>))
import           Data.Tuple                   (swap)
import           Data.Vector                  (Vector)
import qualified Data.Vector                  as V
import qualified Data.Vector.Fusion.Bundle    as Bundle
import qualified Data.Vector.Generic          as GV

data Entry a b = Entry { priority :: !a
                       , payload :: !b
                       } deriving (Show)

instance Eq a => Eq (Entry a b) where
  (==) = (==) `on` priority
  {-# INLINE (==) #-}
  (/=) = (/=) `on` priority
  {-# INLINE (/=) #-}

instance Ord a => Ord (Entry a b) where
  compare = comparing priority

mkEntry :: (IsOrderedPolynomial poly)
        => Vector poly -> Entry (Signature poly) (Vector poly)
mkEntry = {-# SCC "mkEntry" #-} Entry <$> signature <*> id

f5 :: (IsOrderedPolynomial a, Field (Coefficient a))
   => Ideal a -> [a]
f5 ideal =
  let sideal = V.fromList $ generators ideal
  in map snd $ calcSignatureGB sideal

data P a b = P { get1 :: !a, get2 :: !b }

sec :: (b -> b') -> P a b -> P a b'
sec f (P a b) = P a (f b)
{-# INLINE sec #-}

{-# INLINE parMapMaybe #-}
parMapMaybe :: (a -> Maybe b) -> [a] -> [b]
parMapMaybe f = catMaybes . parMap rseq f

calcSignatureGB :: forall poly.
                   (Field (Coefficient poly), IsOrderedPolynomial poly)
                => V.Vector poly -> [(V.Vector poly, poly)]
calcSignatureGB side | null side = []
calcSignatureGB (V.map monoize -> sideal) = runST $ do
  let n = V.length sideal
  gs <- newSTRef []
  ps <- newSTRef $ H.fromList [ mkEntry $ basis n i | i <- [0..n-1]]
  syzs <- {-# SCC "initial_syzygy" #-}
          newSTRef
          [ mkEntry $
            V.zipWith (+)
              (V.map (negate (sideal V.! j) *) (basis n i))
              (V.map ((sideal V.! i) *) (basis n j))
          | j <- [0..n-1]
          , i <- [0..j-1]
          ]
  whileJust_ (H.viewMin <$!> readSTRef ps) $ \(Entry gSig g, ps') -> do
    ps .= ps'
    gs0 <- readSTRef gs
    ss0 <- readSTRef syzs
    unless ({-# SCC "standardCr" #-}standardCriterion gSig ss0 || any ((== gSig) . priority . get2) gs0) $ do
      let (h, ph) = reduceSignature sideal g gs0
          h' = {-# SCC "scaling" #-} V.map (* injectCoeff (recip $ leadingCoeff ph)) h
      if isZero ph
        then syzs .%= (mkEntry h : )
        else do
        let ph' = monoize ph
            lt  = leadTerm ph'
            adds = H.fromList $
                   parMapMaybe
                   (fmap mkEntry . flip regularSVector (P ph' h') . sec payload) gs0
        ps .%= H.union adds
        gs .%= (P ph' (mkEntry h') :)

  map (\(P p (Entry _ a)) -> (a, p)) <$> readSTRef gs


leadTerm :: IsOrderedPolynomial poly => poly -> Term poly
leadTerm = uncurry Term . swap . leadingTerm

data Term poly = Term { leadMonom :: !(OrderedMonomial (MOrder poly) (Arity poly))
                      , leadCoeff :: !(Coefficient poly)
                      }

regularSVector :: (IsOrderedPolynomial poly)
               => P poly (Vector poly)
               -> P poly (Vector poly)
               -> Maybe (Vector poly)
regularSVector (P pg g) (P ph h) =
  let ltg = leadTerm pg
      lth = leadTerm ph
      l = lcmMonomial (leadMonom ltg) (leadMonom lth)
      vl = V.map (l / leadMonom ltg >*) g
      vr = V.map (l / leadMonom lth >*) h
      ans = V.zipWith (-) vl vr
  in if signature vl /= signature vr
     then Just ans
     else Nothing

standardCriterion :: (IsOrderedPolynomial poly, Foldable t)
                  => Signature poly -> t (Entry (Signature poly) (Vector poly))
                  -> Bool
standardCriterion g = {-# SCC "standardCriterion" #-} any ((`divSig` g) . priority)

divSig :: IsOrderedPolynomial poly => Signature poly -> Signature poly -> Bool
divSig (Signature i _ c) (Signature j _ d) =
  {-# SCC "divSig" #-}
  i == j && c `divs` d

data Signature poly =
  Signature { _position :: {-# UNPACK #-} !Int
            , _sigCoeff :: Coefficient poly
            , _sigMonom :: OrderedMonomial (MOrder poly) (Arity poly)
            }

instance (Show (Coefficient poly), KnownNat (Arity poly)) => Show (Signature poly) where
  showsPrec _ (Signature pos coe m) =
    showChar '('  . shows coe . showChar ' ' . shows m . showChar ')' . showChar 'e' . shows pos

instance Eq (Signature poly) where
  Signature i _ m == Signature j _ n = i == j && n == m

instance IsOrderedPolynomial poly => Ord (Signature poly) where
  compare (Signature i _ m) (Signature j _ n) = compare i j <> compare m n

signature :: (IsOrderedPolynomial poly)
          => Vector poly
          -> Signature poly
signature = {-# SCC "signature" #-}
            fromJust . DC.coerce
          . ifoldMap (\i v -> Option $ do
                         let lt =  leadingTerm v
                         guard $ not $ isZero $ fst lt
                         return $ Max $ uncurry (Signature i) lt
                     )

basis :: (Monoidal a, Unital a) => Int -> Int -> Vector a
basis len i = V.generate len $ \j -> if i == j then one else zero

reduceSignature :: (IsOrderedPolynomial poly, Field (Coefficient poly), Foldable t)
                => Vector poly -> Vector poly
                -> t (P poly (Entry (Signature poly) (Vector poly)))
                -> (Vector poly, poly)
reduceSignature ideal g hs =
  fst $ flip (until (\((_, phiu), r) -> phiu == r)) ((g, phi g), zero) $ \((u, !phiu), r) ->
  let m = leadingTerm $ phiu - r
      tryCancel (P hi' (Entry _ hi)) = First $ do
        let fac = toPolynomial (m `tryDiv` leadingTerm hi')
            quo = V.map (fac *) hi
        guard $ (leadingMonomial hi' `divs` snd m) && (signature quo < signature u)
        return (quo, fac * hi')
  in case getFirst $ foldMap tryCancel hs of
    Nothing -> ((u, phiu), r + toPolynomial m)
    Just (d, phid)  -> ((V.zipWith (-) u d, phiu - phid), r)
  where
    phi = sumA . V.zipWith (*) ideal

toPair :: Term poly -> (Coefficient poly, OrderedMonomial (MOrder poly) (Arity poly))
toPair (Term m c) = (c, m)
{-# INLINE toPair #-}

sumA :: Monoidal c => Vector c -> c
sumA = Bundle.foldl' (+) zero . GV.stream
