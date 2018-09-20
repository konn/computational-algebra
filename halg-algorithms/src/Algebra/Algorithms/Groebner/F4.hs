{-# LANGUAGE NoMonomorphismRestriction, PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms, ScopedTypeVariables             #-}
-- | Faugere's F4 algorithm
module Algebra.Algorithms.Groebner.F4
  (f4', f4, f4WithStrategy', f4WithStrategy, normalStrategy) where
import           Algebra.Matrix.DataMatrix    (DMatrix)
import           Algebra.Matrix.Generic
import           Algebra.Prelude.Core         hiding (Min)
import           Control.Lens                 hiding ((.=))
import           Control.Monad.Loops
import           Control.Monad.ST
import           Control.Monad.ST.Combinators
import qualified Data.Foldable                as F
import qualified Data.Heap                    as H
import           Data.Monoid                  (First (..))
import qualified Data.Set                     as S
import qualified Data.Vector                  as V
import qualified Data.Vector.Generic          as GV
import qualified Data.Vector.Mutable          as MV

-- | Selection strategy assigning each pair of polynomials of type @f@,
--   to some @'Ord'@ered rank @w@. F_4 Algorithm will take care of pairs
--   in ascending order in rank.
type Strategy f w = f -> f -> w

normalStrategy :: IsOrderedPolynomial poly => poly -> poly -> Int
normalStrategy = degPair

degPair :: (IsOrderedPolynomial poly) => poly -> poly -> Int
degPair f g = totalDegree $ lcmLeadingMonomial f g

lcmLeadingMonomial :: (IsOrderedPolynomial poly)
                   => poly -> poly -> OrderedMonomial (MOrder poly) (Arity poly)
lcmLeadingMonomial f g = lcmMonomial (leadingMonomial f) (leadingMonomial g)

viewMins :: Ord w => H.Heap w -> Maybe (H.Heap w, H.Heap w)
viewMins h = do
  (a, _) <- H.viewMin h
  return $ H.span (== a) h

f4 :: (Field (Coefficient poly), Num (Coefficient poly),
       IsOrderedPolynomial poly, Normed (Coefficient poly))
   => Ideal poly -> [poly]
f4 = f4' (Proxy :: Proxy DMatrix)

f4' ::(Normed (Coefficient poly),
       IsOrderedPolynomial poly,
       Field (Coefficient poly),
       Matrix mat (Coefficient poly))
    => proxy mat -> Ideal poly -> [poly]
f4' pxy = f4WithStrategy'  pxy normalStrategy

-- | Computes Gröbner Basis for the given ideal by F_4 algorithm, with specified
--   internal representation of matrix.
f4WithStrategy' :: (Normed (Coefficient poly),
                    Ord w, IsOrderedPolynomial poly,
                    Field (Coefficient poly),
                    Matrix mat (Coefficient poly))
                => proxy mat -> Strategy poly w -> Ideal poly -> [poly]
f4WithStrategy' mrep select ideal = runST $ do
  let is0 = V.fromList $ generators ideal
      buildHeap fs is =
        H.fromList [ H.Entry (select (fs V.! i) (fs V.! j)) (i, j)
                   | j <- is, i <- [0..j-1]
                   ]
  gs <- newSTRef =<< V.unsafeThaw is0
  bs <- newSTRef $ buildHeap is0 [0.. V.length is0 - 1]
  let cancel i j = do
        (fi, fj) <- (,) <$> gs %! i <*> gs %! j
        let l = lcmLeadingMonomial fi fj
        return $ map (\g -> monoize $ l / leadingMonomial g >* g) [fi, fj]
  whileJust_ (viewMins <$> readSTRef bs) $ \(cur, bs') -> do
    bs .= bs'
    g <- arrayToList gs
    ls <- concat <$> mapM (uncurry cancel . H.payload) (F.toList cur)
    let (labs, mat) = computeMatrix mrep ls g
        ms = mapMaybe (\xs -> getFirst $ ifoldMap (\i m -> First $
                                                    if isZero (xs GV.! i)
                                                    then Nothing
                                                    else Just m)
                        labs) $ toRows mat
        (red, _, _) = gaussReduction mat
        ps = filter (\f -> all (not . (`divs` leadingMonomial f)) ms) $
             decodeMatrix labs red
    unless (null ps) $ do
      g0 <- readSTRef gs
      let len0 = MV.length g0
          ps'  = V.fromList ps
          size  = V.length ps'
      mv' <- MV.unsafeGrow g0 size
      gs .= mv'
      MV.copy (MV.slice len0 size mv') =<< V.unsafeThaw ps'
      fs <- V.unsafeFreeze mv'
      bs .%= H.union (buildHeap fs [len0..len0 + size - 1])
  arrayToList gs

decodeMatrix :: (Matrix mat (Coefficient poly), IsOrderedPolynomial poly)
             => Vector (OMonom poly)
             -> mat (Coefficient poly)
             -> [poly]
decodeMatrix labs mat =
  filter (not . isZero) $
  map (GV.ifoldr (\j d c -> toPolynomial (d, labs V.! j) + c) zero) $
  toRows mat

-- | F_4 algorithm, using parallel array as an internal representation
f4WithStrategy :: (Field (Coefficient poly),
                   IsOrderedPolynomial poly,
                   Normed (Coefficient poly),
                   Num (Coefficient poly),
                   Ord w)
   => Strategy poly w -> Ideal poly -> [poly]
f4WithStrategy = f4WithStrategy' (Proxy :: Proxy DMatrix)

computeMatrix :: (IsOrderedPolynomial poly,
                  Field (Coefficient poly),
                  Matrix mat (Coefficient poly)
                 )
              => proxy mat -> [poly] -> [poly]
              -> (Vector (OrderedMonomial (MOrder poly) (Arity poly)), mat (Coefficient poly))
computeMatrix _ ls gs = runST $ do
  hs <- newSTRef ls
  done <- newSTRef $ S.fromList $ map leadingMonomial ls
  monHs <- newSTRef $ H.fromList $ map Down $ S.toList $
           foldMap (S.deleteMax . orderedMonomials) ls
  let ins f = do
        modifySTRef' hs (f:)
        del <- readSTRef done
        let ms = orderedMonomials f S.\\ del
        modifySTRef' monHs $ H.union $ H.fromList $ map Down $ S.toList ms
  whileJust_ (H.viewMin <$> readSTRef monHs) $ \(Down m, mHS') -> do
    monHs  .= mHS'
    done  .%= S.insert m
    forM_ (find ((`divs` m). leadingMonomial) gs) $ \g ->
      ins $ m / leadingMonomial g >* g
  labs <- V.fromList . S.toDescList <$> readSTRef done
  fs <- readSTRef hs
  let mat = fromRows $
            map (\f -> GV.generate (V.length labs) $ \i -> coeff (labs GV.! i) f) fs
  return (labs, mat)
