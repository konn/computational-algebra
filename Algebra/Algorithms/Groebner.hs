{-# LANGUAGE ConstraintKinds, DataKinds, EmptyCase, FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances, GADTs, MultiParamTypeClasses            #-}
{-# LANGUAGE NoImplicitPrelude, ParallelListComp, PolyKinds, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, TemplateHaskell, TypeFamilies         #-}
{-# LANGUAGE TypeOperators, ViewPatterns                                #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Algebra.Algorithms.Groebner
       (
       -- * Polynomial division
         divModPolynomial, divPolynomial, modPolynomial
       , lcmPolynomial, gcdPolynomial
       -- * Groebner basis
       , isGroebnerBasis
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
       ) where
import           Algebra.Internal
import           Algebra.Ring.Ideal
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
import           Data.Singletons.Prelude      (Sing (SFalse, STrue))
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

-- | Calculate a polynomial quotient and remainder w.r.t. second argument.
divModPolynomial :: (IsOrderedPolynomial poly, Field (Coefficient poly))
                 => poly -> [poly]
                 -> ([(poly, poly)], poly)
divModPolynomial f0 fs = loop f0 zero (zip (nub fs) (repeat zero))
  where
    loop p r dic
        | isZero p = (dic, r)
        | otherwise =
            let ltP = toPolynomial $ leadingTerm p
            in case break ((`divs` leadingMonomial p) . leadingMonomial . fst) dic of
                 (_, []) -> loop (p - ltP) (r + ltP) dic
                 (xs, (g, old):ys) ->
                     let q = toPolynomial $ leadingTerm p `tryDiv` leadingTerm g
                         dic' = xs ++ (g, old + q) : ys
                     in loop (p - (q * g)) r dic'
{-# INLINABLE divModPolynomial #-}

-- | Remainder of given polynomial w.r.t. the second argument.
modPolynomial :: (IsOrderedPolynomial poly, Field (Coefficient poly))
              => poly -> [poly] -> poly
modPolynomial = (snd .) . divModPolynomial

-- | A Quotient of given polynomial w.r.t. the second argument.
divPolynomial :: (IsOrderedPolynomial poly, Field (Coefficient poly))
              => poly -> [poly] -> [(poly, poly)]
divPolynomial = (fst .) . divModPolynomial

infixl 7 `divPolynomial`
infixl 7 `modPolynomial`
infixl 7 `divModPolynomial`

-- | Test if the given ideal is Groebner basis, using Buchberger criteria and relatively primeness.
isGroebnerBasis :: (IsOrderedPolynomial poly, Field (Coefficient poly))
                => Ideal poly -> Bool
isGroebnerBasis (nub . generators -> ideal) = all check $ combinations ideal
  where
    check (f, g) =
      let (t, u) = (leadingMonomial f , leadingMonomial g)
      in t*u == lcmMonomial t u || sPolynomial f g `modPolynomial` ideal == zero

-- | The Naive buchberger's algorithm to calculate Groebner basis for the given ideal.
simpleBuchberger :: (Field k, CoeffRing k, KnownNat n, IsMonomialOrder n order)
                 => Ideal (OrderedPolynomial k order n) -> [OrderedPolynomial k order n]
simpleBuchberger ideal =
  let gs = nub $ generators ideal
  in fst $ until (null . snd) (\(ggs, acc) -> let cur = nub $ ggs ++ acc in
                                              (cur, calc cur)) (gs, calc gs)
  where
    calc acc = [ q | f <- acc, g <- acc
               , let q = sPolynomial f g `modPolynomial` acc, q /= zero
               ]

-- | Buchberger's algorithm slightly improved by discarding relatively prime pair.
primeTestBuchberger :: (Field r, CoeffRing r, KnownNat n, IsMonomialOrder n order)
                    => Ideal (OrderedPolynomial r order n) -> [OrderedPolynomial r order n]
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
buchberger :: (Field r, CoeffRing r, KnownNat n, IsMonomialOrder n order)
           => Ideal (OrderedPolynomial r order n) -> [OrderedPolynomial r order n]
buchberger = syzygyBuchberger

-- | Buchberger's algorithm greately improved using the syzygy theory with the sugar strategy.
-- Utilizing priority queues, this function reduces division complexity and comparison time.
-- If you don't have strong reason to avoid this function, this function is recommended to use.
syzygyBuchberger :: (Field r, CoeffRing r, KnownNat n, IsMonomialOrder n order)
                    => Ideal (OrderedPolynomial r order n) -> [OrderedPolynomial r order n]
syzygyBuchberger = syzygyBuchbergerWithStrategy (SugarStrategy NormalStrategy)
{-# INLINE syzygyBuchberger #-}

-- | apply buchberger's algorithm using given selection strategy.
syzygyBuchbergerWithStrategy :: (Field r, CoeffRing r, KnownNat n,
                                 IsMonomialOrder n order, SelectionStrategy n strategy
                        , Ord (Weight n strategy order))
                    => strategy -> Ideal (OrderedPolynomial r order n) -> [OrderedPolynomial r order n]
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


-- | Calculate the weight of given polynomials w.r.t. the given strategy.
-- Buchberger's algorithm proccesses the pair with the most least weight first.
-- This function requires the @Ord@ instance for the weight; this constraint is not required
-- in the 'calcWeight' because of the ease of implementation. So use this function.
calcWeight' :: (SelectionStrategy n s, CoeffRing r, KnownNat n, IsMonomialOrder n ord)
            => s -> OrderedPolynomial r ord n -> OrderedPolynomial r ord n -> Weight n s ord
calcWeight' s = calcWeight (toProxy s)
{-# INLINE calcWeight' #-}

-- | Type-class for selection strategies in Buchberger's algorithm.
class SelectionStrategy n s where
  type Weight n s ord :: *
  calcWeight :: (CoeffRing r, KnownNat n, IsMonomialOrder n ord)
             => Proxy s -> OrderedPolynomial r ord n -> OrderedPolynomial r ord n -> Weight n s ord

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
      deg' = maximum . map (totalDegree . snd) . getTerms
      tsgr h = deg' h - totalDegree (leadingMonomial h)
      sugar = max (tsgr f) (tsgr g) + totalDegree (lcmMonomial (leadingMonomial f) (leadingMonomial g))
  {-# INLINE calcWeight #-}


minimizeGroebnerBasis :: (Field k, CoeffRing k, KnownNat n, IsMonomialOrder n order)
                      => [OrderedPolynomial k order n] -> [OrderedPolynomial k order n]
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
reduceMinimalGroebnerBasis :: (Field k, CoeffRing k, KnownNat n, IsMonomialOrder n order)
                           => [OrderedPolynomial k order n] -> [OrderedPolynomial k order n]
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
calcGroebnerBasisWith :: (Field k, CoeffRing k, KnownNat n, IsMonomialOrder n order, IsMonomialOrder n order')
                      => order -> Ideal (OrderedPolynomial k order' n) -> [OrderedPolynomial k order n]
calcGroebnerBasisWith ord i = calcGroebnerBasis $  mapIdeal (changeOrder ord) i

-- | Caliculating reduced Groebner basis of the given ideal w.r.t. the specified monomial order.
calcGroebnerBasisWithStrategy :: (Field k, CoeffRing k, KnownNat n, IsMonomialOrder n order
                                 , SelectionStrategy n strategy, Ord (Weight n strategy order))
                      => strategy -> Ideal (OrderedPolynomial k order n) -> [OrderedPolynomial k order n]
calcGroebnerBasisWithStrategy strategy =
  reduceMinimalGroebnerBasis . minimizeGroebnerBasis . syzygyBuchbergerWithStrategy strategy

-- | Caliculating reduced Groebner basis of the given ideal.
calcGroebnerBasis :: (Field k, CoeffRing k, KnownNat n, IsMonomialOrder n order)
                  => Ideal (OrderedPolynomial k order n) -> [OrderedPolynomial k order n]
calcGroebnerBasis = reduceMinimalGroebnerBasis . minimizeGroebnerBasis . syzygyBuchberger

-- | Test if the given polynomial is the member of the ideal.
isIdealMember :: (CoeffRing k, KnownNat n, Field k, IsMonomialOrder n o)
              => OrderedPolynomial k o n -> Ideal (OrderedPolynomial k o n) -> Bool
isIdealMember f ideal = groebnerTest f (calcGroebnerBasis ideal)

-- | Test if the given polynomial can be divided by the given polynomials.
groebnerTest :: (CoeffRing k, KnownNat n, Field k, IsMonomialOrder n order)
             => OrderedPolynomial k order n -> [OrderedPolynomial k order n] -> Bool
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
thEliminationIdeal :: forall n m ord k.
                      ( IsMonomialOrder (m - n) ord,
                        IsMonomialOrder m ord, Field k, CoeffRing k, KnownNat m
                      , (n :<= m) ~ 'True)
                   => SNat n
                   -> Ideal (OrderedPolynomial k ord m)
                   -> Ideal (OrderedPolynomial k ord (m :-. n))
thEliminationIdeal n = withSingI (sOnes n) $
  gcastWith (lengthReplicate n sOne) $
  withKnownNat n $
  withKnownNat ((sing :: SNat m) %:-. n) $
  mapIdeal (changeOrderProxy Proxy) . thEliminationIdealWith (weightedEliminationOrder n) n

-- | Calculate n-th elimination ideal using the specified n-th elimination type order.
thEliminationIdealWith :: ( Field k, CoeffRing k,
                            KnownNat (m :-. n), (n :<= m) ~ 'True,
                            EliminationType m n ord, IsMonomialOrder m ord',
                            IsMonomialOrder (m :-. n) ord)
                   => ord
                   -> SNat n
                   -> Ideal (OrderedPolynomial k ord' m)
                   -> Ideal (OrderedPolynomial k ord (m :-. n))
thEliminationIdealWith ord n ideal =
  withKnownNat n $ toIdeal $ [ transformMonomial (V.drop n) f
                             | f <- calcGroebnerBasisWith ord ideal
                             , all (all (== 0) . V.takeAtMost n . getMonomial . snd) $ getTerms f
                             ]

-- | Calculate n-th elimination ideal using the specified n-th elimination type order.
-- This function should be used carefully because it does not check whether the given ordering is
-- n-th elimintion type or not.
unsafeThEliminationIdealWith :: ( IsMonomialOrder (m :-. n) ord, Field k,
                                  IsMonomialOrder m ord,
                                  CoeffRing k, KnownNat m, KnownNat (m :-. n)
                                , (n :<= m) ~ 'True, IsMonomialOrder m ord')
                             => ord
                             -> SNat n
                             -> Ideal (OrderedPolynomial k ord' m)
                             -> Ideal (OrderedPolynomial k ord (m :-. n))
unsafeThEliminationIdealWith ord n ideal =
   withKnownNat n $ toIdeal $ [ transformMonomial (V.drop n) f
                                 | f <- calcGroebnerBasisWith ord ideal
                                 , all (all (== 0) . V.take n . getMonomial . snd) $ getTerms f
                                 ]

-- | An intersection ideal of given ideals (using 'WeightedEliminationOrder').
intersection :: forall r k n ord.
                ( IsMonomialOrder (k + n) ord, Field r, CoeffRing r, KnownNat n
                , IsMonomialOrder n ord)
             => Vector (Ideal (OrderedPolynomial r ord n)) k
             -> Ideal (OrderedPolynomial r ord n)
intersection idsv@(_ :< _) =
    let sk = sizedLength idsv
        sn = sing :: SNat n
    in withSingI (sOnes sk) $ withKnownNat (sk %:+ sn) $
    let ts  = take (fromIntegral $ fromSing sk) $ genVars (sk %:+ sn)
        tis = zipWith (\ideal t -> mapIdeal ((t *) . shiftR sk) ideal) (toList idsv) ts
        j = foldr appendIdeal (principalIdeal (one - foldr (+) zero ts)) tis
    in gcastWith (plusMinus' sk sn) $ case plusLeqL sk sn of
      Witness -> coerce (cong Proxy $ minusCongL (plusComm sk sn) sk `trans` plusMinus sn sk) $
                 thEliminationIdeal sk j
intersection _ = Ideal $ singleton one

-- | Ideal quotient by a principal ideals.
quotByPrincipalIdeal :: (Field k, CoeffRing k, KnownNat n,
                         IsMonomialOrder n ord, IsMonomialOrder (2 + n) ord)
                     => Ideal (OrderedPolynomial k ord n)
                     -> OrderedPolynomial k ord n
                     -> Ideal (OrderedPolynomial k ord n)
quotByPrincipalIdeal i g =
    case intersection (i :< (Ideal $ singleton g) :< NilL) of
      Ideal gs -> Ideal $ V.map (snd . head . (`divPolynomial` [g])) gs

-- | Ideal quotient by the given ideal.
quotIdeal :: forall k ord n l.
             (CoeffRing k, KnownNat n, Field k,
              IsMonomialOrder (l + n) ord,
              IsMonomialOrder (2 + n) ord,
              IsMonomialOrder n ord)
          => Ideal (OrderedPolynomial k ord n)
          -> Vector (OrderedPolynomial k ord n) l
          -> Ideal (OrderedPolynomial k ord n)
quotIdeal i g =
  withKnownNat (sizedLength g) $
  withKnownNat (sizedLength g %:+ (sing :: SNat n)) $
  intersection $ V.map (i `quotByPrincipalIdeal`) g

-- | Saturation by a principal ideal.
saturationByPrincipalIdeal :: forall k n ord.
                              (Field k, CoeffRing k, KnownNat n,
                               IsMonomialOrder n ord, IsMonomialOrder  (n + 1) ord)
                           => Ideal (OrderedPolynomial k ord n)
                           -> OrderedPolynomial k ord n -> Ideal (OrderedPolynomial k ord n)
saturationByPrincipalIdeal is g =
  let n = sing :: SNat n
  in withKnownNat (sOne %:+ n) $
     gcastWith (plusMinus' sOne n) $ gcastWith (plusComm n sOne) $
     case (leqStep sOne (sOne %:+ n) n Refl, lneqZero n) of
        (Witness, Witness) ->
          thEliminationIdeal sOne $
          addToIdeal (one - (castPolynomial g * varX)) (mapIdeal (shiftR sOne) is)

-- | Saturation ideal
saturationIdeal :: forall k ord n l. (CoeffRing k, KnownNat n, Field k,
                                      IsMonomialOrder n ord,
                                      IsMonomialOrder (l + n) ord,
                                      IsMonomialOrder (n + 1) ord)
                => Ideal (OrderedPolynomial k ord n)
                -> Vector (OrderedPolynomial k ord n) l
                -> Ideal (OrderedPolynomial k ord n)
saturationIdeal i g =
  withKnownNat (sizedLength g) $
  withKnownNat (sizedLength g %:+ (sing :: SNat n)) $
  intersection $ V.map (i `saturationByPrincipalIdeal`) g

-- | Calculate resultant for given two unary polynomimals.
resultant :: forall k ord . (Eq k, Field k, DecidableZero k, IsMonomialOrder 1 ord)
          => OrderedPolynomial k ord 1
          -> OrderedPolynomial k ord 1
          -> k
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


-- | Determine whether two polynomials have a common factor with positive degree using resultant.
hasCommonFactor :: forall k ord . (Eq k, Field k, DecidableZero k, IsMonomialOrder 1 ord)
                => OrderedPolynomial k ord 1
                -> OrderedPolynomial k ord 1
                -> Bool
hasCommonFactor f g = isZero $ resultant f g

lcmPolynomial :: forall k ord n. (CoeffRing k, KnownNat n, Field k,
                                  IsMonomialOrder n ord,
                                  IsMonomialOrder (2 + n) ord)
              => OrderedPolynomial k ord n
              -> OrderedPolynomial k ord n
              -> OrderedPolynomial k ord n
lcmPolynomial f g = head $ generators $ intersection (principalIdeal f :< principalIdeal g :< NilL)

gcdPolynomial :: (CoeffRing r, KnownNat n, Field r, IsMonomialOrder n order,
                 IsMonomialOrder (2 + n) order)
              => OrderedPolynomial r order n -> OrderedPolynomial r order n
              -> OrderedPolynomial r order n
gcdPolynomial f g = snd $ head $ f * g `divPolynomial` [lcmPolynomial f g]

