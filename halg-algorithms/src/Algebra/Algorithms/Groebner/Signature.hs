{-# LANGUAGE BangPatterns, ScopedTypeVariables, ViewPatterns #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Algebra.Algorithms.Groebner.Signature (f5) where
import           Algebra.Prelude.Core         hiding (Vector)
import           Control.Arrow                (second)
import           Control.Lens                 hiding ((.=))
import           Control.Monad.Loops
import           Control.Monad.ST.Combinators
import qualified Data.Coerce                  as DC
import           Data.Heap                    (Entry (..))
import qualified Data.Heap                    as H
import           Data.Maybe                   (fromJust)
import           Data.Monoid                  (First (..))
import           Data.Semigroup               hiding (First, getFirst, (<>))
import           Data.Vector                  (Vector)
import qualified Data.Vector                  as V
import qualified Data.Vector.Fusion.Bundle    as Bundle
import qualified Data.Vector.Generic          as GV

mkEntry :: (IsOrderedPolynomial poly)
        => Vector poly -> Entry (Signature poly) (Vector poly)
mkEntry = {-# SCC "mkEntry" #-} Entry <$> signature <*> id

f5 :: (IsOrderedPolynomial a, Field (Coefficient a))
   => Ideal a -> [a]
f5 ideal =
  let sideal = V.fromList $ generators ideal
  in map snd $ calcSignatureGB sideal

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
  whileJust_ (H.viewMin <$> readSTRef ps) $ \(Entry gSig g, ps') -> do
    ps .= ps'
    gs0 <- readSTRef gs
    ss0 <- readSTRef syzs
    unless ({-# SCC "standardCr" #-}standardCriterion gSig ss0 || any ((== gSig) . priority . snd) gs0) $ do
      let (h, ph) = reduceSignature sideal g gs0
          h' = {-# SCC "scaling" #-} V.map (* injectCoeff (recip $ leadingCoeff ph)) h
      if isZero ph
        then syzs .%= (mkEntry h : )
        else do
        let adds = H.fromList $
                   mapMaybe
                   (fmap mkEntry . flip regularSVector (monoize ph, h') . second payload) gs0
        ps .%= H.union adds
        gs .%= ((monoize ph, mkEntry h') :)

  map (\ (p, Entry _ a) -> (a, p)) <$> readSTRef gs

regularSVector :: (IsOrderedPolynomial poly)
               => (poly, Vector poly)
               -> (poly, Vector poly)
               -> Maybe (Vector poly)
regularSVector (pg, g) (ph, h) = do
  let l = lcmMonomial (leadingMonomial pg) (leadingMonomial ph)
      vl = V.map (l / leadingMonomial pg >*) g
      vr = V.map (l / leadingMonomial ph >*) h
  guard $ signature vl /= signature vr
  return $ V.zipWith (-) vl vr

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
                -> t (poly, Entry (Signature poly) (Vector poly))
                -> (Vector poly, poly)
reduceSignature ideal g hs =
  fst $ flip (until (\((_, phiu), r) -> phiu == r)) ((g, phi g), zero) $ \((u, !phiu), r) ->
  let m = leadingTerm $ phiu - r
      tryCancel (hi', Entry _ hi) = First $ do
        let fac = toPolynomial (m `tryDiv` leadingTerm hi')
            quo = V.map (fac *) hi
        guard $ (leadingMonomial hi' `divs` snd m) && (signature quo < signature u)
        return (quo, fac * hi')
  in case getFirst $ foldMap tryCancel hs of
    Nothing -> ((u, phiu), r + toPolynomial m)
    Just (d, phid)  -> ((V.zipWith (-) u d, phiu - phid), r)
  where
    phi = sumA . V.zipWith (*) ideal

sumA :: Monoidal c => Vector c -> c
sumA = Bundle.foldl' (+) zero . GV.stream
