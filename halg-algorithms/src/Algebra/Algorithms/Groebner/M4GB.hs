{-# LANGUAGE BangPatterns, ScopedTypeVariables, StandaloneDeriving #-}
{-# LANGUAGE TupleSections, TypeApplications                       #-}
module Algebra.Algorithms.Groebner.M4GB (m4gb) where
import Algebra.Algorithms.Groebner.SelectionStrategy (SelectionStrategy)
import Algebra.Field.Finite
import Algebra.Prelude.Core                          hiding (Min)

import           Control.Arrow                (second)
import           Control.Monad.Loops          (whileJust_)
import           Control.Monad.ST.Combinators (newSTRef, readSTRef, runST,
                                               (.%=), (.=))
import qualified Data.Coerce                  as DC
import           Data.Entry                   (Entry (..))
import qualified Data.Foldable                as F
import           Data.Map.Strict              (Map)
import qualified Data.Map.Strict              as M
import           Data.Maybe                   (fromJust)
import           Data.MonoTraversable         (ofoldMap)
import           Data.Set                     (Set)
import qualified Data.Set                     as S

m4gb :: (IsOrderedPolynomial poly, FiniteField (Coefficient poly))
     => Ideal poly -> [poly]
m4gb i | isEmptyIdeal i = []
       | otherwise = runST $ do
  let (ell, msIni, psIni) = foldr step (S.empty, emptyPS, S.empty) i
      step f (l, m, p) =
        let (m', f') = mulFullReduce l m one f
        in updateReduce l m' p f'
  ls <- newSTRef ell
  ms <- newSTRef msIni
  ps <- newSTRef psIni
  let pop = do
        ps1 <- readSTRef ps
        forM (S.minView ps1) $ \(a, ps') -> do
          ps .= ps'
          return a
  whileJust_ pop $ \(lmf, lmg) -> do
    (ltf, tailF) <- fromMaybe (error "F lacks ps") . lookupPS lmf <$> readSTRef ms
    (ltg, tailG) <- fromMaybe (error "G lacks ps") . lookupPS lmg <$> readSTRef ms
    let u = lcmMonomial lmf lmg
    ls0 <- readSTRef ls
    ms0 <- readSTRef ms
    let (ms1, h1) = mulFullReduce ls0 ms0 ((one, u) `tryDiv` ltf) tailF
        (ms2, h2) = mulFullReduce ls0 ms1 ((one, u) `tryDiv` ltg) tailG
        h = h1 - h2
    ms .= ms2
    unless (isZero h) $ do
      ps0 <- readSTRef ps
      let (ls', ms', ps') = updateReduce ls0 ms2 ps0 h
      ls .= ls'
      ms .= ms'
      ps .= ps'
  ms0 <- readSTRef ms
  ls0 <- readSTRef ls
  return $ polynomialsPS $ focusLeadMonomPS ls0 ms0

-- | A set of polynomials, ordered by leading polynomials
newtype PolySet poly =
    PS { runPolySet :: Map (OMonom poly) (Coefficient poly, poly) }
deriving instance IsOrderedPolynomial poly => Eq   (PolySet poly)

focusLeadMonomPS :: IsOrderedPolynomial poly
                 => Set (OMonom poly) -> PolySet poly -> PolySet poly
focusLeadMonomPS hs (PS dic) =
  PS $ M.restrictKeys dic hs

splittedPolynomialsPS :: IsOrderedPolynomial poly
                      => PolySet poly
                      -> [(Term poly, poly)]
splittedPolynomialsPS =
  map (\(lmf, (lcf, tailF)) -> ((lcf, lmf), tailF)) . M.toList . runPolySet

polynomialsPS :: IsOrderedPolynomial poly
              => PolySet poly
              -> [poly]
polynomialsPS =
  map (\(lmf, (lcf, tailF)) -> toPolynomial (lcf, lmf) + tailF) . M.toList . runPolySet

unionPS :: forall poly. IsOrderedPolynomial poly
        => PolySet poly -> PolySet poly -> PolySet poly
unionPS =
    DC.coerce
      @(Map (OMonom poly) (Coefficient poly, poly)
        -> Map (OMonom poly) (Coefficient poly, poly)
        -> Map (OMonom poly) (Coefficient poly, poly))
      M.union
{-# INLINE unionPS #-}

insertPS :: forall poly. IsOrderedPolynomial poly
         => poly -> PolySet poly -> PolySet poly
insertPS f =
  DC.coerce @(Map (OMonom poly) (Coefficient poly, poly)
              -> Map (OMonom poly) (Coefficient poly, poly)) $
  let ((lc, lm), f') = splitLeadingTerm f
  in M.insert lm (lc, f')
{-# INLINE insertPS #-}

emptyPS :: PolySet poly
emptyPS = PS M.empty
{-# INLINE emptyPS #-}

singletonPS :: IsOrderedPolynomial poly => poly -> PolySet poly
singletonPS f =
  let ((lc,lm), f') = splitLeadingTerm f
  in PS $ M.singleton lm (lc, f')
{-# INLINE singletonPS #-}

lookupPS :: IsOrderedPolynomial poly
         => OMonom poly -> PolySet poly -> Maybe (Term poly, poly)
lookupPS m =
  fmap (\(c, f) -> ((c,m), f)) . M.lookup m . runPolySet
{-# INLINE lookupPS #-}

lookupMaxPS :: IsOrderedPolynomial poly
            => PolySet poly -> Maybe (Term poly, poly)
lookupMaxPS =
  fmap (\(m, (lc, f)) -> ((lc, m), f)) . M.lookupMax . runPolySet
{-# INLINE lookupMaxPS #-}

maxViewPS :: IsOrderedPolynomial poly
          => PolySet poly -> Maybe (Term poly, poly, PolySet poly)
maxViewPS =
  fmap (\((m, (lc, f)),dic) -> ((lc, m), f, PS dic)) . M.maxViewWithKey . runPolySet
{-# INLINE maxViewPS #-}
leadingMonomialsPS :: IsOrderedPolynomial poly
                   => PolySet poly -> Set (OMonom poly)
leadingMonomialsPS = M.keysSet . runPolySet
{-# INLINE leadingMonomialsPS #-}

mapPS :: IsOrderedPolynomial poly
      => (poly -> poly) -> PolySet poly -> PolySet poly
mapPS f = PS . M.map (second f) . runPolySet
{-# INLINE mapPS #-}

monomialsPS :: IsOrderedPolynomial poly
            => PolySet poly -> Set (OMonom poly)
monomialsPS (PS dic) =
  M.keysSet dic `S.union` ofoldMap (orderedMonomials . snd) dic

tailMonomialsPS  :: IsOrderedPolynomial poly
                 => PolySet poly -> Set (OMonom poly)
tailMonomialsPS = ofoldMap (orderedMonomials . snd) . runPolySet
{-# INLINE tailMonomialsPS #-}

updateReduce :: (IsOrderedPolynomial poly, Field (Coefficient poly))
             => Set (OMonom poly)
             -> PolySet poly
             -> Set (OMonom poly, OMonom poly)
             -> poly
             -> (Set (OMonom poly), PolySet poly, Set (OMonom poly, OMonom poly))
updateReduce ell ms0 ps f = runST $ do
  hsPos <- newSTRef $ singletonPS $ monoize f
           -- Hs divisible by lmf
  hsNeg <- newSTRef   emptyPS
           -- Hs NOT divisible by lmf
  ms <- newSTRef ms0
  let (ltf@(_, lmf), tailF) = splitLeadingTerm f
  let pop = do
        h <- readSTRef hsPos
        m <- readSTRef ms
        let (_, p, cands0) =
              S.splitMember lmf $
              tailMonomialsPS (m `unionPS` h) S.\\ leadingMonomialsPS h
            cands = S.filter (lmf `divs`) $ if p then S.insert lmf cands0 else cands0
        return $ S.lookupMax cands
      {-# INLINE pop #-}
  whileJust_ pop $ \u -> do
    em <- readSTRef ms
    let (ms', h) = mulFullReduce ell em ((one, u) / ltf) tailF
        h' = fromOrderedMonomial u + h
    ms .= ms'
    if lmf `divs`  leadingMonomial h'
    then hsPos .%= insertPS h'
    else hsNeg .%= insertPS h'
  hs <- newSTRef =<< (unionPS <$> readSTRef hsPos <*> readSTRef hsNeg)
        -- FIXME: hs must be a heap, instead of dictionary?
  let pickMinH = do
        hs' <- readSTRef hs
        forM (maxViewPS hs') $ \(lth, tailH, s) -> do
          hs .= s
          return (lth, tailH)
  whileJust_ pickMinH $ \(lt@(_,lmh), tailH) -> do
    let h = toPolynomial lt + tailH
    hs .%= mapPS (\tlg -> tlg - coeff lmh tlg !* h)
    ms .%= mapPS (\tlg -> tlg - coeff lmh tlg !* h)
  let (ell', ps') = update ell ps lmf
  ms' <- readSTRef ms
  return (ell', ms', ps')

update :: (IsMonomialOrder n ord, KnownNat n)
       => Set (OrderedMonomial ord n) -> Set (OrderedMonomial ord n, OrderedMonomial ord n) -> OrderedMonomial ord n
       -> (Set (OrderedMonomial ord n), Set (OrderedMonomial ord n, OrderedMonomial ord n))
update ell ps m =
  let (half, p, _) = S.splitMember m ell
      check n = lcmMonomial m n /= m * n
  in if p || F.any (`divs` m) half
  then (ell, ps)
  else (S.insert m ell, ps `S.union` S.map (m,) (S.filter check ell))

mulFullReduce :: (IsOrderedPolynomial poly, Field (Coefficient poly))
              => Set (OMonom poly)
              -> PolySet poly
              -> Term poly
              -> poly
              -> (PolySet poly, poly)
mulFullReduce ls ms0 t f =
  M.foldrWithKey step (ms0, zero) (terms f)
  where
    step m0 c0 (!ms, !h) =
      let s = (c0, m0)
          r = t * s
      in if isJust (findDivisor (snd r) ls)
      then
        let (ms', (ltg, rsg)) = getReductor ls ms r
        in (ms', h - toPolynomial (r `tryDiv` ltg) * rsg)
      else (ms, h + toPolynomial r)

getReductor :: (IsOrderedPolynomial poly, Field (Coefficient poly))
            => Set (OMonom poly)
            -> PolySet poly
            -> Term poly
            -> (PolySet poly, (Term poly, poly))
getReductor ell ms r@(_, lm) =
  case lookupPS lm ms of
    Just h -> (ms, h)
    Nothing ->
      let Just t = findDivisor lm ell
          (r', rest) = fromMaybe (error "getReductor: t absent in PS of m") $! lookupPS t ms
          (m', h) = mulFullReduce ell ms (r `tryDiv` r') rest
          h' = toPolynomial r + h
      in (insertPS h' m', splitLeadingTerm h')

findDivisor :: (KnownNat n, IsMonomialOrder n ord)
            => OrderedMonomial ord n
            -> Set (OrderedMonomial ord n)
            -> Maybe (OrderedMonomial ord n)
findDivisor m ms =
  let (lh, there, _) = S.splitMember m ms
  in if there
  then Just m
  else F.find (`divs` m) lh
