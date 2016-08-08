{-# LANGUAGE ConstraintKinds, DataKinds, EmptyCase, FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances, GADTs, MultiParamTypeClasses                #-}
{-# LANGUAGE NoImplicitPrelude, ParallelListComp, PolyKinds, RankNTypes     #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, TypeOperators, ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Algebra.Algorithms.Groebner
       (
       -- * Groebner basis
         isGroebnerBasis
       , calcGroebnerBasis, calcGroebnerBasisWith
       , calcGroebnerBasisWithStrategy
       , buchberger, syzygyBuchberger
       , simpleBuchberger, primeTestBuchberger
       , reduceMinimalGroebnerBasis, minimizeGroebnerBasis
       -- ** Selection Strategies
       , syzygyBuchbergerWithStrategy
       , SelectionStrategy(..), calcWeight', GrevlexStrategy(..)
       , NormalStrategy(..), SugarStrategy(..), GradedStrategy(..)
       -- * Ideal operations
       , isIdealMember, intersection, thEliminationIdeal, thEliminationIdealWith
       , unsafeThEliminationIdealWith
       , quotIdeal, quotByPrincipalIdeal
       , saturationIdeal, saturationByPrincipalIdeal
       -- * Resultant
       , resultant, hasCommonFactor
       , lcmPolynomial, gcdPolynomial
       ) where
import           Algebra.Internal
import           Algebra.Ring.Ideal
import qualified Data.Map as M
import Control.Lens (_Wrapped, (&),  (%~))
import           Algebra.Ring.Polynomial
import           Control.Applicative
import           Control.Monad
import           Control.Monad.Loops
import           Control.Monad.ST
import qualified Data.Foldable                as H
import           Data.Function
import qualified Data.Heap                    as H
import           Data.List
import           Data.Maybe
import           Data.Singletons.Prelude      (POrd (..), SEq (..), SOrd (..))
import           Data.Singletons.Prelude      (Sing (SFalse, STrue), withSingI)
import           Data.Singletons.Prelude.List (Length, Replicate, Sing (SCons))
import           Data.Singletons.Prelude.List (sLength, sReplicate)
import           Data.Sized.Builtin           (toList)
import qualified Data.Sized.Builtin           as V
import           Data.STRef
import           Numeric.Algebra              hiding ((<), (>))
import           Numeric.Decidable.Zero
import           Prelude                      hiding (Num (..), recip, subtract,
                                               (^))
import qualified Prelude                      as P
import           Proof.Equational

-- | Test if the given ideal is Groebner basis, using Buchberger criteria and relatively primeness.
isGroebnerBasis :: (IsOrderedPolynomial poly, Field (Coefficient poly))
                => Ideal poly -> Bool
isGroebnerBasis (nub . generators -> ideal) = all check $ combinations ideal
  where
    check (f, g) =
      let (t, u) = (leadingMonomial f , leadingMonomial g)
      in t*u == lcmMonomial t u || sPolynomial f g `modPolynomial` ideal == zero

-- | The Naive buchberger's algorithm to calculate Groebner basis for the given ideal.
simpleBuchberger :: (Field (Coefficient poly), IsOrderedPolynomial poly)
                 => Ideal poly -> [poly]
simpleBuchberger ideal =
  let gs = nub $ generators ideal
  in fst $ until (null . snd) (\(ggs, acc) -> let cur = nub $ ggs ++ acc in
                                              (cur, calc cur)) (gs, calc gs)
  where
    calc acc = [ q | f <- acc, g <- acc
               , let q = sPolynomial f g `modPolynomial` acc, q /= zero
               ]

-- | Buchberger's algorithm slightly improved by discarding relatively prime pair.
primeTestBuchberger :: (Field (Coefficient poly), IsOrderedPolynomial poly)
                    => Ideal poly -> [poly]
primeTestBuchberger ideal =
  let gs = nub $ generators ideal
  in fst $ until (null . snd) (\(ggs, acc) -> let cur = nub $ ggs ++ acc in
                                              (cur, calc cur)) (gs, calc gs)
  where
    calc acc = [ q | f <- acc, g <- acc, f /= g
               , let f0 = leadingMonomial f, let g0 = leadingMonomial g
               , lcmMonomial f0 g0 /= f0 * g0
               , let q = sPolynomial f g `modPolynomial` acc, q /= zero
               ]

(.=) :: STRef s a -> a -> ST s ()
x .= v = writeSTRef x v

(%=) :: STRef s a -> (a -> a) -> ST s ()
x %= f = modifySTRef x f

combinations :: [a] -> [(a, a)]
combinations xs = concat $ zipWith (map . (,)) xs $ drop 1 $ tails xs
{-# INLINE combinations #-}

-- | Calculate Groebner basis applying (modified) Buchberger's algorithm.
-- This function is same as 'syzygyBuchberger'.
buchberger :: (Field (Coefficient poly), IsOrderedPolynomial poly)
           => Ideal poly -> [poly]
buchberger = syzygyBuchberger

-- | Buchberger's algorithm greately improved using the syzygy theory with the sugar strategy.
-- Utilizing priority queues, this function reduces division complexity and comparison time.
-- If you don't have strong reason to avoid this function, this function is recommended to use.
syzygyBuchberger :: (Field (Coefficient poly), IsOrderedPolynomial poly)
                    => Ideal poly -> [poly]
syzygyBuchberger = syzygyBuchbergerWithStrategy (SugarStrategy NormalStrategy)
{-# INLINE syzygyBuchberger #-}

-- | apply buchberger's algorithm using given selection strategy.
syzygyBuchbergerWithStrategy :: (Field (Coefficient poly), IsOrderedPolynomial poly,
                                 SelectionStrategy (Arity poly) strategy,
                                 Ord (Weight (Arity poly) strategy (MOrder poly)))
                    => strategy -> Ideal poly -> [poly]
syzygyBuchbergerWithStrategy strategy ideal = runST $ do
  let gens = zip [1..] $ filter (/= zero) $ generators ideal
  gs <- newSTRef $ H.fromList [H.Entry (leadingMonomial g) g | (_, g) <- gens]
  b  <- newSTRef $ H.fromList [H.Entry (calcWeight' strategy f g, j) (f, g) | ((_, f), (j, g)) <- combinations gens]
  len <- newSTRef (genericLength gens :: Integer)
  whileM_ (not . H.null <$> readSTRef b) $ do
    Just (H.Entry _ (f, g), rest) <-  H.viewMin <$> readSTRef b
    gs0 <- readSTRef gs
    b .= rest
    let f0 = leadingMonomial f
        g0 = leadingMonomial g
        l  = lcmMonomial f0 g0
        redundant = H.any (\(H.Entry _ h) -> (h `notElem` [f, g])
                                  && (all (\k -> H.all ((/=k) . H.payload) rest)
                                                     [(f, h), (g, h), (h, f), (h, g)])
                                  && leadingMonomial h `divs` l) gs0
    when (l /= f0 * g0 && not redundant) $ do
      len0 <- readSTRef len
      let qs = (H.toList gs0)
          s = sPolynomial f g `modPolynomial` map H.payload qs
      when (s /= zero) $ do
        b %= H.union (H.fromList [H.Entry (calcWeight' strategy q s, j) (q, s) | H.Entry _ q <- qs | j <- [len0+1..]])
        gs %= H.insert (H.Entry (leadingMonomial s) s)
        len %= (*2)
  map H.payload . H.toList <$> readSTRef gs
{-# SPECIALISE
 syzygyBuchbergerWithStrategy :: (Field k, CoeffRing k,
                                 SelectionStrategy n strategy, KnownNat n,
                                 Ord (Weight n strategy Grevlex))
                    => strategy -> Ideal (OrderedPolynomial k Grevlex n) -> [OrderedPolynomial k Grevlex n]
 #-}

{-# SPECIALISE
 syzygyBuchbergerWithStrategy :: (Field k, CoeffRing k, IsMonomialOrder n ord,
                                 SelectionStrategy n strategy, KnownNat n,
                                 Ord (Weight n strategy ord))
                    => strategy -> Ideal (OrderedPolynomial k ord n) -> [OrderedPolynomial k ord n]
 #-}

-- | Calculate the weight of given polynomials w.r.t. the given strategy.
-- Buchberger's algorithm proccesses the pair with the most least weight first.
-- This function requires the @Ord@ instance for the weight; this constraint is not required
-- in the 'calcWeight' because of the ease of implementation. So use this function.
calcWeight' :: (SelectionStrategy (Arity poly) s, IsOrderedPolynomial poly)
            => s -> poly -> poly -> Weight (Arity poly) s (MOrder poly)
calcWeight' s = calcWeight (toProxy s)
{-# INLINE calcWeight' #-}

-- | Type-class for selection strategies in Buchberger's algorithm.
class SelectionStrategy n s where
  type Weight n s ord :: *
  calcWeight :: (IsOrderedPolynomial poly, n ~ Arity poly)
             => Proxy s -> poly -> poly -> Weight n s (MOrder poly)

-- | Buchberger's normal selection strategy. This selects the pair with
-- the least LCM(LT(f), LT(g)) w.r.t. current monomial ordering.
data NormalStrategy = NormalStrategy deriving (Read, Show, Eq, Ord)

instance SelectionStrategy n NormalStrategy where
  type Weight n NormalStrategy ord = OrderedMonomial ord n
  calcWeight _ f g = lcmMonomial (leadingMonomial f)  (leadingMonomial g)
  {-# INLINE calcWeight #-}

-- | Choose the pair with the least LCM(LT(f), LT(g)) w.r.t. 'Grevlex' order.
data GrevlexStrategy = GrevlexStrategy deriving (Read, Show, Eq, Ord)

instance SelectionStrategy n GrevlexStrategy where
  type Weight n GrevlexStrategy ord = OrderedMonomial Grevlex n
  calcWeight _ f g = changeMonomialOrderProxy Proxy $
                     lcmMonomial (leadingMonomial f) (leadingMonomial g)
  {-# INLINE calcWeight #-}

data GradedStrategy = GradedStrategy deriving (Read, Show, Eq, Ord)

-- | Choose the pair with the least LCM(LT(f), LT(g)) w.r.t. graded current ordering.
instance SelectionStrategy n GradedStrategy where
  type Weight n GradedStrategy ord = OrderedMonomial (Graded ord) n
  calcWeight _ f g = changeMonomialOrderProxy Proxy $
                     lcmMonomial (leadingMonomial f)  (leadingMonomial g)
  {-# INLINE calcWeight #-}


-- | Sugar strategy. This chooses the pair with the least phantom homogenized degree and then break the tie with the given strategy (say @s@).
data SugarStrategy s = SugarStrategy s deriving (Read, Show, Eq, Ord)

instance SelectionStrategy n s => SelectionStrategy n (SugarStrategy s) where
  type Weight n (SugarStrategy s) ord = (Int, Weight n s ord)
  calcWeight (Proxy :: Proxy (SugarStrategy s)) f g = (sugar, calcWeight (Proxy :: Proxy s) f g)
    where
      deg' = maximum . map totalDegree . H.toList . orderedMonomials
      tsgr h = deg' h - totalDegree (leadingMonomial h)
      sugar = max (tsgr f) (tsgr g) + totalDegree (lcmMonomial (leadingMonomial f) (leadingMonomial g))
  {-# INLINE calcWeight #-}


minimizeGroebnerBasis :: (Field (Coefficient poly), IsOrderedPolynomial poly)
                      => [poly] -> [poly]
minimizeGroebnerBasis bs = runST $ do
  left  <- newSTRef $ map monoize $ filter (/= zero) bs
  right <- newSTRef []
  whileM_ (not . null <$> readSTRef left) $ do
    f : xs <- readSTRef left
    writeSTRef left xs
    ys     <- readSTRef right
    unless (any (\g -> leadingMonomial g `divs` leadingMonomial f) xs
         || any (\g -> leadingMonomial g `divs` leadingMonomial f) ys) $
      writeSTRef right (f : ys)
  readSTRef right

-- | Reduce minimum Groebner basis into reduced Groebner basis.
reduceMinimalGroebnerBasis :: (Field (Coefficient poly), IsOrderedPolynomial poly)
                           => [poly] -> [poly]
reduceMinimalGroebnerBasis bs = runST $ do
  left  <- newSTRef bs
  right <- newSTRef []
  whileM_ (not . null <$> readSTRef left) $ do
    f : xs <- readSTRef left
    writeSTRef left xs
    ys     <- readSTRef right
    let q = f `modPolynomial` (xs ++ ys)
    if q == zero then writeSTRef right ys else writeSTRef right (q : ys)
  readSTRef right

-- | Caliculating reduced Groebner basis of the given ideal w.r.t. the specified monomial order.
calcGroebnerBasisWith :: (IsOrderedPolynomial poly,
                          Field (Coefficient poly),
                          IsMonomialOrder (Arity poly) order)
                      => order -> Ideal poly
                      -> [OrderedPolynomial (Coefficient poly) order (Arity poly)]
calcGroebnerBasisWith _ord = calcGroebnerBasis . mapIdeal injectVars
{-# INLINE [1] calcGroebnerBasisWith #-}
{-# RULES
"calcGroebnerBasisWith/sameOrderPolyn" [~1] forall x.
  calcGroebnerBasisWith x = calcGroebnerBasis
  #-}

-- | Caliculating reduced Groebner basis of the given ideal w.r.t. the specified monomial order.
calcGroebnerBasisWithStrategy :: (Field (Coefficient poly), IsOrderedPolynomial poly
                                 , SelectionStrategy (Arity poly) strategy
                                 , Ord (Weight (Arity poly) strategy (MOrder poly)))
                      => strategy -> Ideal poly -> [poly]
calcGroebnerBasisWithStrategy strategy =
  reduceMinimalGroebnerBasis . minimizeGroebnerBasis . syzygyBuchbergerWithStrategy strategy

-- | Caliculating reduced Groebner basis of the given ideal.
calcGroebnerBasis :: (Field (Coefficient poly), IsOrderedPolynomial poly)
                  => Ideal poly -> [poly]
calcGroebnerBasis = reduceMinimalGroebnerBasis . minimizeGroebnerBasis . syzygyBuchberger

-- | Test if the given polynomial is the member of the ideal.
isIdealMember :: (Field (Coefficient poly), IsOrderedPolynomial poly)
              => poly -> Ideal poly -> Bool
isIdealMember f ideal = groebnerTest f (calcGroebnerBasis ideal)

-- | Test if the given polynomial can be divided by the given polynomials.
groebnerTest :: (Field (Coefficient poly), IsOrderedPolynomial poly)
             => poly -> [poly] -> Bool
groebnerTest f fs = f `modPolynomial` fs == zero

newtype LengthReplicate n =
  LengthReplicate { runLengthReplicate :: forall x. Sing (x :: Nat)
                                       -> Length (Replicate n x) :~: n }

lengthReplicate :: SNat n -> SNat x -> Length (Replicate n x) :~: n
lengthReplicate = runLengthReplicate . induction base step
  where
    base :: LengthReplicate 0
    base = LengthReplicate $ const Refl

    step :: SNat n -> LengthReplicate n -> LengthReplicate (Succ n)
    step n (LengthReplicate ih) = LengthReplicate $ \x ->
      case (n %:+ sOne) %:== sZero of
        SFalse ->
          start (sLength (sReplicate (sSucc n) x))
            =~= sLength (SCons x (sReplicate (sSucc n %:- sOne) x))
            =~= sOne %:+ sLength (sReplicate (sSucc n %:- sOne) x)
            === sSucc (sLength (sReplicate (sSucc n %:- sOne) x))
                `because` sym (succAndPlusOneL (sLength (sReplicate (sSucc n %:- sOne) x)))
            === sSucc (sLength (sReplicate (n %:+ sOne %:- sOne) x))
                `because` succCong (lengthCong (replicateCong (minusCongL (succAndPlusOneR n) sOne) x))
            === sSucc (sLength (sReplicate n x))
                `because` succCong (lengthCong (replicateCong (plusMinus n sOne) x))
            === sSucc n `because` succCong (ih x)
        STrue -> case sCompare (n %:+ sOne) sZero of {}

lengthCong :: a :~: b -> Length a :~: Length b
lengthCong Refl = Refl

replicateCong :: a :~: b -> Sing x -> Replicate a x :~: Replicate b x
replicateCong Refl _ = Refl

-- | Calculate n-th elimination ideal using 'WeightedEliminationOrder' ordering.
thEliminationIdeal :: forall poly n.
                      ( IsMonomialOrder (Arity poly - n) (MOrder poly),
                        Field (Coefficient poly),
                        IsOrderedPolynomial poly,
                        (n :<= Arity poly) ~ 'True)
                   => SNat n
                   -> Ideal poly
                   -> Ideal (OrderedPolynomial (Coefficient poly) (MOrder poly) (Arity poly :-. n))
thEliminationIdeal n = withSingI (sOnes n) $
  withRefl (lengthReplicate n sOne) $
  withKnownNat n $
  withKnownNat ((sing :: SNat (Arity poly)) %:-. n) $
  mapIdeal (changeOrderProxy Proxy) . thEliminationIdealWith (weightedEliminationOrder n) n

-- | Calculate n-th elimination ideal using the specified n-th elimination type order.
thEliminationIdealWith :: ( IsOrderedPolynomial poly,
                            m ~ Arity poly,
                            k ~ Coefficient poly, Field k,
                            KnownNat (m :-. n), (n :<= m) ~ 'True,
                            EliminationType m n ord)
                   => ord
                   -> SNat n
                   -> Ideal poly
                   -> Ideal (OrderedPolynomial k Grevlex (m :-. n))
thEliminationIdealWith = unsafeThEliminationIdealWith

-- | Calculate n-th elimination ideal using the specified n-th elimination type order.
-- This function should be used carefully because it does not check whether the given ordering is
-- n-th elimintion type or not.
unsafeThEliminationIdealWith :: ( IsOrderedPolynomial poly,
                                  m ~ Arity poly,
                                  k ~ Coefficient poly,
                                  Field k,
                                  IsMonomialOrder m ord,
                                  KnownNat (m :-. n), (n :<= m) ~ 'True)
                             => ord
                             -> SNat n
                             -> Ideal poly
                             -> Ideal (OrderedPolynomial k Grevlex (m :-. n))
unsafeThEliminationIdealWith ord n ideal =
  withKnownNat n $ toIdeal $ [ f & _Wrapped %~ M.mapKeys (orderMonomial Nothing . V.drop n . getMonomial)
                             | f <- calcGroebnerBasisWith ord ideal
                             , all (all (== 0) . V.takeAtMost n . getMonomial . snd) $ getTerms f
                             ]

-- | An intersection ideal of given ideals (using 'WeightedEliminationOrder').
intersection :: forall poly k.
                ( IsMonomialOrder (k + Arity poly) (MOrder poly),
                  Field (Coefficient poly), IsOrderedPolynomial poly)
             => Vector (Ideal poly) k
             -> Ideal poly
intersection idsv@(_ :< _) =
    let sk = sizedLength idsv
        sn = sing :: SNat (Arity poly)
    in withSingI (sOnes sk) $ withKnownNat (sk %:+ sn) $
    let ts  = take (fromIntegral $ fromSing sk) vars
        inj :: poly -> OrderedPolynomial (Coefficient poly) (MOrder poly) (k + Arity poly)
        inj = transformMonomial (V.append $ V.replicate sk 0) .  injectVars
        tis = zipWith (\ideal t -> mapIdeal ((t *) . inj) ideal) (toList idsv) ts
        j = foldr appendIdeal (principalIdeal (one - foldr (+) zero ts)) tis
    in withRefl (plusMinus' sk sn) $
       withWitness (plusLeqL sk sn) $
       mapIdeal injectVars $ 
       coerce (cong Proxy $ minusCongL (plusComm sk sn) sk `trans` plusMinus sn sk) $
        thEliminationIdeal sk j
intersection _ = Ideal $ singleton one

-- | Ideal quotient by a principal ideals.
quotByPrincipalIdeal :: (IsMonomialOrder (2 + Arity poly) (MOrder poly),
                         Field (Coefficient poly), IsOrderedPolynomial poly)
                     => Ideal poly
                     -> poly
                     -> Ideal poly
quotByPrincipalIdeal i g =
    case intersection (i :< (Ideal $ singleton g) :< NilL) of
      Ideal gs -> Ideal $ V.map (snd . head . (`divPolynomial` [g])) gs

-- | Ideal quotient by the given ideal.
quotIdeal :: forall poly l.
             (IsOrderedPolynomial poly, Field (Coefficient poly),
              IsMonomialOrder (l + Arity poly) (MOrder poly),
              IsMonomialOrder (2 + Arity poly) (MOrder poly))
          => Ideal poly
          -> Vector poly l
          -> Ideal poly
quotIdeal i g =
  withKnownNat (sizedLength g) $
  withKnownNat (sizedLength g %:+ sArity g) $
  intersection $ V.map (i `quotByPrincipalIdeal`) g

-- | Saturation by a principal ideal.
saturationByPrincipalIdeal :: forall poly.
                              (IsOrderedPolynomial poly, Field (Coefficient poly),
                               IsMonomialOrder  (1 + Arity poly) (MOrder poly))
                           => Ideal poly
                           -> poly
                           -> Ideal poly
saturationByPrincipalIdeal is g =
  let n = sArity' g
      remap :: poly -> OrderedPolynomial (Coefficient poly) (MOrder poly) (1 + Arity poly)
      remap = shiftR sOne . injectVars
  in withKnownNat (sOne %:+ n) $
     withRefl (plusMinus' sOne n) $ withRefl (plusComm n sOne) $
     withWitness (leqStep sOne (sOne %:+ n) n Refl) $
     withWitness (lneqZero n) $
     mapIdeal injectVars $
     thEliminationIdeal sOne $
     addToIdeal (one - (remap g * varX)) $
     mapIdeal remap is

-- | Saturation ideal
saturationIdeal :: forall poly l.
                   (Field (Coefficient poly),
                    IsOrderedPolynomial poly,
                    IsMonomialOrder (l + Arity poly) (MOrder poly),
                    IsMonomialOrder (1 + Arity poly) (MOrder poly))
                => Ideal poly
                -> Vector poly l
                -> Ideal poly
saturationIdeal i g =
  withKnownNat (sizedLength g) $
  withKnownNat (sizedLength g %:+ sArity g) $
  intersection $ V.map (i `saturationByPrincipalIdeal`) g

-- | Calculate resultant for given two unary polynomimals.
resultant :: forall poly.
             (Field (Coefficient poly),
              IsOrderedPolynomial poly,
              Arity poly ~ 1)
          => poly
          -> poly
          -> (Coefficient poly)
resultant = go one
  where
    go res h s
        | totalDegree' s > 0     =
          let r    = h `modPolynomial` [s]
              res' = res * negate one ^ (totalDegree' h * totalDegree' s)
                     * (leadingCoeff s) ^ (totalDegree' h P.- totalDegree' r)
          in go res' s r
        | isZero h || isZero s = zero
        | totalDegree' h > 0     = (leadingCoeff s ^ totalDegree' h) * res
        | otherwise              = res

    _ = Refl :: Arity poly :~: 1
        -- to suppress "redundant" warning for univariate constraint.

-- | Determine whether two polynomials have a common factor with positive degree using resultant.
hasCommonFactor :: (Field (Coefficient poly),
                    IsOrderedPolynomial poly,
                    Arity poly ~ 1)
                => poly
                -> poly
                -> Bool
hasCommonFactor f g = isZero $ resultant f g

lcmPolynomial :: forall poly.
                 (Field (Coefficient poly),
                  IsOrderedPolynomial poly,
                  IsMonomialOrder (2 + Arity poly) (MOrder poly))
              => poly
              -> poly
              -> poly
lcmPolynomial f g = head $ generators $ intersection (principalIdeal f :< principalIdeal g :< NilL)

gcdPolynomial :: (Field (Coefficient poly),
                  IsOrderedPolynomial poly,
                  IsMonomialOrder (2 + Arity poly) (MOrder poly))
              => poly
              -> poly
              -> poly
gcdPolynomial f g = snd $ head $ f * g `divPolynomial` [lcmPolynomial f g]

