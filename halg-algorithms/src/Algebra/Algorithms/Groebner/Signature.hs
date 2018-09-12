{-# LANGUAGE BangPatterns, DataKinds, KindSignatures, PolyKinds        #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TypeApplications #-}
{-# LANGUAGE TypeInType, ViewPatterns                                  #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
-- | Signature-based Groebner basis algorithms, such as Faugère's \(F_5\).
--
--   You can import "Algebra.Algorithms.Groebner.Signature.Rules" to
--   replace every occurence of @'Algebra.Algorithms.Groebner.calcGroebnerBasis'@ with @'f5'@;
--   but its effect is pervasive, you should not import in the /library-site/.
module Algebra.Algorithms.Groebner.Signature
  ( -- * Algorithms
    f5, f5With, calcSignatureGB, calcSignatureGBWith,
    -- * Classes
    ModuleOrdering(..), POT(..), TOP(..),
    DegreeWeighted(..), TermWeighted(..),
    DegreeWeightedPOT,DegreeWeightedTOP,
    TermWeightedPOT, TermWeightedTOP,
    -- * References
    -- $refs
  ) where
import           Algebra.Prelude.Core         hiding (Vector)
import qualified Control.Foldl                as Fl
import           Control.Monad.Loops          (whileJust_)
import           Control.Monad.ST.Combinators (ST, STRef, modifySTRef',
                                               newSTRef, readSTRef, runST,
                                               writeSTRef, (.%=))
import qualified Data.Coerce                  as DC
import qualified Data.Heap                    as H
import           Data.Kind                    (Type)
import           Data.Monoid                  (First (..))
import           Data.Reflection              (Reifies (..), reify)
import qualified Data.Set                     as Set
import qualified Data.Vector                  as V
import qualified Data.Vector.Mutable          as MV

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

-- | Calculates a Gröbner basis of a given ideal using
--   the signature-based algorithm as described in [Gao-Iv-Wang](#gao-iv-wang).
--
--   This is the fastest implementation in this library so far.
f5 :: (IsOrderedPolynomial a, Field (Coefficient a))
   => Ideal a -> [a]
f5 ideal = let sideal = V.fromList $ generators ideal
  in V.toList $ V.map snd $ calcSignatureGB sideal
{-# INLINE f5 #-}

f5With :: forall ord a pxy. (IsOrderedPolynomial a, Field (Coefficient a), ModuleOrdering a ord)
       => pxy ord -> Ideal a -> [a]
f5With pxy ideal = let sideal = V.fromList $ generators ideal
  in V.toList $ V.map snd $ calcSignatureGBWith pxy sideal
{-# INLINE f5With #-}

calcSignatureGB :: forall poly.
                   (Field (Coefficient poly), IsOrderedPolynomial poly)
                => V.Vector poly -> V.Vector (Signature poly, poly)
calcSignatureGB gs =
  reify gs $ \(_ :: Proxy (gs :: Type)) -> calcSignatureGBWith (Proxy @(TermWeightedPOT gs)) gs
{-# INLINE CONLIKE calcSignatureGB #-}

class ModuleOrdering poly ord where
  cmpModule :: proxy ord -> Signature poly -> Signature poly -> Ordering

data POT = POT deriving (Read, Show, Eq, Ord)

instance IsOrderedPolynomial poly => ModuleOrdering poly POT where
  cmpModule _ (Signature i m) (Signature j n) = compare i j <> compare m n
  {-# INLINE cmpModule #-}

data TOP = TOP deriving (Read, Show, Eq, Ord)

instance IsOrderedPolynomial poly => ModuleOrdering poly TOP where
  cmpModule _ (Signature i m) (Signature j n) = compare m n <> compare i j
  {-# INLINE cmpModule #-}

data WeightedPOT (gs :: k) = WeightedPOT
  deriving (Read, Show, Eq, Ord)

type DegreeWeightedPOT gs = DegreeWeighted gs POT
type DegreeWeightedTOP gs = DegreeWeighted gs TOP
type TermWeightedPOT gs   = TermWeighted gs POT
type TermWeightedTOP gs   = TermWeighted gs TOP

newtype DegreeWeighted (gs :: k) ord = DegreeWeighted ord
newtype TermWeighted (gs :: k) ord = TermWeighted ord

instance (ModuleOrdering poly ord, IsOrderedPolynomial poly, Reifies (gs :: k) (V.Vector poly))
      => ModuleOrdering poly (DegreeWeighted gs ord) where
  cmpModule _ l@(Signature i t) r@(Signature j u) =
    let gs = reflect (Proxy :: Proxy gs) :: V.Vector poly
    in compare
         (totalDegree t + fromIntegral (totalDegree' (gs V.! i)))
         (totalDegree u + fromIntegral (totalDegree' (gs V.! j)))
      <> cmpModule (Proxy @ord) l r
  {-# INLINE cmpModule #-}

instance (ModuleOrdering poly ord, IsOrderedPolynomial poly, Reifies (gs :: k) (V.Vector poly))
      => ModuleOrdering poly (TermWeighted gs ord) where
  cmpModule _ l@(Signature i t) r@(Signature j u) =
    let gs = reflect (Proxy :: Proxy gs) :: V.Vector poly
    in compare
         (t * leadingMonomial (gs V.! i))
         (u * leadingMonomial (gs V.! j))
       <> cmpModule (Proxy @ord) l r
  {-# INLINE cmpModule #-}

data ModuleElement ord poly = ME { syzSign :: !(WithModOrd ord poly)
                                 , _polElem :: !poly
                                 }
                            deriving (Eq)

data JPair poly = JPair { _jpTerm  :: !(OMonom poly)
                        , _jpIndex :: !Int
                        }
deriving instance KnownNat (Arity poly) => Show (JPair poly)
deriving instance KnownNat (Arity poly) => Eq (JPair poly)

type OMonom p = OrderedMonomial (MOrder p) (Arity p)

class Multiplicative c => Action c a where
  (.*!) :: c -> a -> a

infixl 7 .*!

instance {-# OVERLAPPING #-} (Arity poly ~ k, MOrder poly ~ ord, IsOrderedPolynomial poly) =>
         Action (OrderedMonomial ord k) (ModuleElement mord poly) where
  m .*! ME u v = ME (WithModOrd $ m .*! runWithModOrd u) (m >* v)
  {-# INLINE (.*!) #-}

instance {-# OVERLAPPING #-} (Arity poly ~ k, MOrder poly ~ ord, IsOrderedPolynomial poly) =>
         Action (OrderedMonomial ord k) (Signature poly) where
  m .*! Signature i f = Signature i (m * f)
  {-# INLINE (.*!) #-}

instance {-# OVERLAPPING #-} (Arity poly ~ k, MOrder poly ~ ord, IsOrderedPolynomial poly) =>
         Action (OrderedMonomial ord k) (WithModOrd mord poly) where
  (.*!) = DC.coerce @(OrderedMonomial ord k -> Signature poly -> Signature poly) (.*!)
  {-# INLINE (.*!) #-}

-- | Calculates a Groebner basis for a given ideal, and a set of leading monomials of
--   Groebner basis of the associated syzygy module, as described in [Gao-Iv-Wang](#gao-iv-wang).
calcSignatureGBWith :: forall pxy ord poly.
                       (Field (Coefficient poly), ModuleOrdering poly ord, IsOrderedPolynomial poly)
                    => pxy ord -> V.Vector poly -> V.Vector (Signature poly, poly)
calcSignatureGBWith _ side | all isZero side = V.empty
calcSignatureGBWith _ (V.map monoize . V.filter (not . isZero) -> sideal) = runST $ do
  let n = V.length sideal
      mods0 = V.generate n basis
      preGs = V.zipWith ME mods0 sideal
      preHs = Set.fromList [ WithModOrd @ord (Signature @poly j lm)
                           | j <- [0..n - 1]
                           , i <- [0..j - 1]
                           , let lm = leadingMonomial (sideal V.! i)
                           ]
  gs <- newSTRef =<< V.unsafeThaw preGs
  hs <- newSTRef preHs
  let preDecode :: JPair poly -> ModuleElement ord poly
      preDecode (JPair m i) = m .*! (preGs V.! i)
      {-# INLINE preDecode #-}
  jprs <- newSTRef $ H.fromList $
          Fl.fold Fl.nub
          [ Entry sig jpr
          | j <- [0..n - 1]
          , i <- [0..j - 1]
          , let qi = preGs V.! i
          , let qj = preGs V.! j
          , (sig, jpr) <- maybeToList $ jPair (i, qi) (j, qj)
          , let me = preDecode jpr
          , not $ any (`covers` me) preGs || any ((`covers` me) . sigToElem . runWithModOrd) preHs
          ]
  whileJust_ (H.viewMin <$> readSTRef jprs) $ \(Entry (WithModOrd sig) (JPair m0 i0), jprs') -> do
    writeSTRef jprs jprs'
    curGs <- V.unsafeFreeze =<< readSTRef gs
    hs0   <- readSTRef hs
    let me = m0 .*! (curGs V.! i0)
        next = any (`covers` me) curGs || any ((`sigDivs` sig) . runWithModOrd) hs0
    unless next $ do
      let me'@(ME t v) = reduceModuleElement me curGs
      if isZero v
        then modifySTRef' hs $ Set.insert t
        else do
        let k = V.length curGs
            decodeJpr :: JPair poly -> ModuleElement ord poly
            decodeJpr (JPair m i) | i == k = m .*! me'
                                  | otherwise = m .*! (curGs V.! i)
            {-# INLINE decodeJpr #-}
            syzs = V.foldl' (flip Set.insert) Set.empty $
                   V.mapMaybe (DC.coerce . syzME me') curGs
        hs .%= (`Set.union` syzs)
        curHs <- readSTRef hs
        let newJprs = Fl.fold Fl.nub $
                      V.filter (\(Entry sg jp) ->
                                   not $
                                   any (`covers` decodeJpr jp) curGs ||
                                   any ((`sigDivs` runWithModOrd sg) . runWithModOrd) curHs) $
                      V.imapMaybe (curry $ fmap (uncurry Entry) . jPair (k, me')) curGs
        jprs .%= flip H.union (H.fromList newJprs)
        append gs me'
  V.map (\(ME u v) -> (runWithModOrd u, v)) <$> (V.unsafeFreeze =<< readSTRef gs)

append :: STRef s (MV.MVector s a) -> a -> ST s ()
append mv a = do
  g <- readSTRef mv
  let n = MV.length g
  g' <- MV.unsafeGrow g 1
  MV.write g' n a
  writeSTRef mv g'
{-# INLINE append #-}

newtype WithModOrd ord poly = WithModOrd { runWithModOrd :: Signature poly }
  deriving (Eq)

instance ModuleOrdering poly ord => Ord (WithModOrd ord poly) where
  compare = DC.coerce $ cmpModule @poly @ord Proxy
  {-# INLINE compare #-}

jPair :: forall ord poly.
         (IsOrderedPolynomial poly, Field (Coefficient poly), ModuleOrdering poly ord)
      => (Int, ModuleElement ord poly)
      -> (Int, ModuleElement ord poly)
      -> Maybe (WithModOrd ord poly, JPair poly)
jPair (i, p1@(ME u1 v1)) (j, p2@(ME u2 v2)) = do
  let (lc1, lm1) = leadingTerm v1
      (lc2, lm2) = leadingTerm v2
      t = lcmMonomial lm1 lm2
      t1 = t / lm1
      t2 = t / lm2
  let jSig1 = t1 .*! u1
  let jSig2 = t2 .*! u2
  if jSig1 >= jSig2
    then loop i jSig1 (lc1 / lc2) t1 p1 t2 p2
    else loop j jSig2 (lc2 / lc1) t2 p2 t1 p1
  where
    {-# INLINE loop #-}
    loop k sig c t1 w1 t2 w2 = do
      sgn <- cancelModuleElement (t1 .*! w1) (Just c) (t2 .*! w2)
      guard $ sig == syzSign sgn
      return (sig, JPair t1 k)
{-# INLINE jPair #-}

data Signature poly =
  Signature { _sigPos :: {-# UNPACK #-} !Int
            , sigMonom :: !(OrderedMonomial (MOrder poly) (Arity poly))
            }

instance (Show (Coefficient poly), KnownNat (Arity poly)) => Show (Signature poly) where
  showsPrec _ (Signature pos m) =
    showChar '('  . showChar ' ' . shows m . showChar ')' . showChar 'e' . shows pos

instance Eq (Signature poly) where
  Signature i m == Signature j n = i == j && n == m

-- instance (IsOrderedPolynomial poly, ModuleOrdering (Arity poly) ord) => Ord (Signature poly) where
--   compare (Signature i m) (Signature j n) = cmpModule (Proxy @ord) (i,m) (j,n)

basis :: IsOrderedPolynomial a => Int -> WithModOrd ord a
basis i = WithModOrd $ Signature i one
{-# INLINE basis #-}

reduceModuleElement :: (IsOrderedPolynomial poly, ModuleOrdering poly ord,
                        Field (Coefficient poly), Functor t, Foldable t)
                    => ModuleElement ord poly -> t (ModuleElement ord poly)
                    -> ModuleElement ord poly
reduceModuleElement p qs = loop p
  where
    loop !r =
      case getFirst $ foldMap (First . regularTopReduce r) qs of
        Nothing -> r
        Just r' -> loop r'
{-# INLINE reduceModuleElement #-}

regularTopReduce :: forall poly ord.
                    (IsOrderedPolynomial poly, Field (Coefficient poly), ModuleOrdering poly ord)
                 => ModuleElement ord poly -> ModuleElement ord poly
                 -> Maybe (ModuleElement ord poly)
regularTopReduce p1@(ME u1 v1) p2@(ME u2 v2) = do
  guard $ not (isZero v2 || isZero v1) && leadingMonomial v2 `divs` leadingMonomial v1
  let (c, t) = tryDiv (leadingTerm v1) (leadingTerm v2)
  guard $ (t .*! u2) <= u1
  p <- cancelModuleElement p1 (Just c) (t .*! p2)
  guard $ syzSign p == syzSign p1
  return p

cancelModuleElement :: forall ord poly.
                       (ModuleOrdering poly ord,
                        Field (Coefficient poly), IsOrderedPolynomial poly)
                    => ModuleElement ord poly
                    -> Maybe (Coefficient poly)
                    -> ModuleElement ord poly -> Maybe (ModuleElement ord poly)
cancelModuleElement (ME u1 v1) mc (ME u2 v2) =
  let c = fromMaybe one mc
      v' = v1 - c .*. v2
  in case compare u1 u2 of
    LT -> do
      guard $ not $ isZero c
      return $ ME u2 (recip c .*. v')
    GT -> return $ ME u1 v'
    EQ -> do
      guard $ c /= one
      return $ ME u1 (recip (one - c) .*. v')
{-# INLINE cancelModuleElement #-}

syzME :: (Field (Coefficient poly), IsOrderedPolynomial poly, ModuleOrdering poly ord)
      => ModuleElement ord poly -> ModuleElement ord poly -> Maybe (WithModOrd ord poly)
syzME (ME u1 v1) (ME u2 v2) =
  let (u1', u2') = (leadingMonomial v2 .*! u1, leadingMonomial v1 .*! u2)
  in case compare u1' u2' of
    LT -> Just u2'
    GT -> Just u1'
    EQ -> do
      guard $ leadingCoeff v1 /= leadingCoeff v2
      return u1'
{-# INLINE syzME #-}

sigDivs :: IsOrderedPolynomial poly => Signature poly -> Signature poly -> Bool
sigDivs (Signature i n) (Signature j m) = i == j && n `divs` m
{-# INLINE sigDivs #-}

covers :: (IsOrderedPolynomial poly)
       => ModuleElement ord poly -> ModuleElement ord poly -> Bool
covers (ME (WithModOrd sig2) v2) (ME (WithModOrd sig1) v1) = fromMaybe False $ do
  let t = sigMonom sig1 / sigMonom sig2
  return $ sig2 `sigDivs` sig1 && (isZero v2 || t * leadingMonomial v2 < leadingMonomial v1)
{-# INLINE covers #-}

sigToElem :: IsOrderedPolynomial poly => Signature poly -> ModuleElement ord poly
sigToElem sig = ME (WithModOrd sig) (fromOrderedMonomial $ sigMonom sig)
{-# INLINE sigToElem #-}

{- $refs
  * J.-C. Faugère, __A new efficient algorithm for computing Gröbner bases without reduction to zero ( \(F_5\) )__, 2014. DOI: [10.1145/780506.780516](https://doi.org/10.1145/780506.780516).

  * C. Eder and J.-C. Faugère, __A survey on signature-based Gröbner basis computations__, 2015. arXiv: <https://arxiv.org/abs/1404.1774>.

  * D. Cox, J. Little, and D. O'Shea, __Additional Gröbner Basis Algorithms__, Chapter 10 in /Ideals, Variaeties and Algorithms/, 4th ed, Springer, 2015.

  * #gao-iv-wang#S. Gao, F. V. Iv, and M. Wang, __A new framework for computing Gröbner bases__, 2016. DOI: [10.1090/mcom/2969](https://dx.doi.org/10.1090/mcom/2969).
-}
