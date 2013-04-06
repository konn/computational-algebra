{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, NoImplicitPrelude                 #-}
{-# LANGUAGE ParallelListComp, RankNTypes, ScopedTypeVariables               #-}
{-# LANGUAGE StandaloneDeriving, TemplateHaskell, TypeFamilies               #-}
{-# LANGUAGE TypeOperators                                                   #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Algebra.Algorithms.Groebner (
                                   -- * Polynomial division
                                     divModPolynomial, divPolynomial, modPolynomial
                                   -- * Groebner basis
                                   , calcGroebnerBasis, calcGroebnerBasisWith, calcGroebnerBasisWithStrategy
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
                                   ) where
import           Algebra.Internal
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Control.Applicative
import           Control.Monad
import           Control.Monad.Loops
import           Control.Monad.ST
import qualified Data.Foldable           as H
import           Data.Function
import qualified Data.Heap               as H
import           Data.List
import           Data.Proxy
import           Data.STRef
import           Numeric.Algebra
import           Prelude                 hiding (Num (..), recip)

-- | Calculate a polynomial quotient and remainder w.r.t. second argument.
divModPolynomial :: (IsMonomialOrder order, IsPolynomial r n, Field r)
                  => OrderedPolynomial r order n -> [OrderedPolynomial r order n] -> ([(OrderedPolynomial r order n, OrderedPolynomial r order n)], OrderedPolynomial r order n)
divModPolynomial f0 fs = loop f0 zero (zip (nub fs) (repeat zero))
  where
    loop p r dic
        | p == zero = (dic, r)
        | otherwise =
            let ltP = toPolynomial $ leadingTerm p
            in case break ((`divs` leadingMonomial p) . leadingMonomial . fst) dic of
                 (_, []) -> loop (p - ltP) (r + ltP) dic
                 (xs, (g, old):ys) ->
                     let q = toPolynomial $ leadingTerm p `tryDiv` leadingTerm g
                         dic' = xs ++ (g, old + q) : ys
                     in loop (p - (q * g)) r dic'

-- | Remainder of given polynomial w.r.t. the second argument.
modPolynomial :: (IsPolynomial r n, Field r, IsMonomialOrder order)
              => OrderedPolynomial r order n
              -> [OrderedPolynomial r order n]
              -> OrderedPolynomial r order n
modPolynomial = (snd .) . divModPolynomial

-- | A Quotient of given polynomial w.r.t. the second argument.
divPolynomial :: (IsPolynomial r n, Field r, IsMonomialOrder order)
              => OrderedPolynomial r order n
              -> [OrderedPolynomial r order n]
              -> [(OrderedPolynomial r order n, OrderedPolynomial r order n)]
divPolynomial = (fst .) . divModPolynomial

infixl 7 `divPolynomial`
infixl 7 `modPolynomial`
infixl 7 `divModPolynomial`

-- | The Naive buchberger's algorithm to calculate Groebner basis for the given ideal.
simpleBuchberger :: (Field k, IsPolynomial k n, IsMonomialOrder order)
                 => Ideal (OrderedPolynomial k order n) -> [OrderedPolynomial k order n]
simpleBuchberger ideal =
  let gs = nub $ generators ideal
  in fst $ until (null . snd) (\(ggs, acc) -> let cur = nub $ ggs ++ acc in
                                              (cur, calc cur)) (gs, calc gs)
  where
    calc acc = [ q | f <- acc, g <- acc, f /= g
               , let q = sPolynomial f g `modPolynomial` acc, q /= zero
               ]

-- | Buchberger's algorithm slightly improved by discarding relatively prime pair.
primeTestBuchberger :: (Field r, IsPolynomial r n, IsMonomialOrder order)
                    => Ideal (OrderedPolynomial r order n) -> [OrderedPolynomial r order n]
primeTestBuchberger ideal =
  let gs = nub $ generators ideal
  in fst $ until (null . snd) (\(ggs, acc) -> let cur = nub $ ggs ++ acc in
                                              (cur, calc cur)) (gs, calc gs)
  where
    calc acc = [ q | f <- acc, g <- acc, f /= g
               , let f0 = leadingMonomial f, let g0 = leadingMonomial g
               , lcmMonomial f0 g0 /= zipWithV (+) f0 g0
               , let q = sPolynomial f g `modPolynomial` acc, q /= zero
               ]

(.=) :: STRef s a -> a -> ST s ()
x .= v = writeSTRef x v

(%=) :: STRef s a -> (a -> a) -> ST s ()
x %= f = modifySTRef x f

padVec :: a -> Vector a n -> Vector a m -> (Vector a (Max n m), Vector a (Max n m))
padVec _   Nil Nil = (Nil, Nil)
padVec def (x :- xs) (y :- ys) =
  case padVec def xs ys of
    (xs', ys') -> (x :- xs', y :- ys')
padVec def (x :- xs) Nil =
  case padVec def xs Nil of
    (xs', ys') -> case maxZR (sLengthV xs) of
                    Eql -> (x :- xs', def :- ys')
padVec def Nil (y :- ys) =
  case padVec def Nil ys of
    (xs', ys') -> case maxZL (sLengthV ys) of
                    Eql -> (def :- xs', y :- ys')

combinations :: [a] -> [(a, a)]
combinations xs = concat $ zipWith (map . (,)) xs $ drop 1 $ tails xs

-- | Calculate Groebner basis applying (modified) Buchberger's algorithm.
-- This function is same as 'syzygyBuchberger'.
buchberger :: (Field r, IsPolynomial r n, IsMonomialOrder order)
           => Ideal (OrderedPolynomial r order n) -> [OrderedPolynomial r order n]
buchberger = syzygyBuchberger

-- | Buchberger's algorithm greately improved using the syzygy theory with the sugar strategy.
-- Utilizing priority queues, this function reduces division complexity and comparison time.
-- If you don't have strong reason to avoid this function, this function is recommended to use.
syzygyBuchberger :: (Field r, IsPolynomial r n, IsMonomialOrder order)
                    => Ideal (OrderedPolynomial r order n) -> [OrderedPolynomial r order n]
syzygyBuchberger = syzygyBuchbergerWithStrategy (SugarStrategy NormalStrategy)

(=@=) :: Vector Int n -> Vector Int m -> Bool
Nil       =@= Nil       = True
(x :- xs) =@= (y :- ys) = x == y && xs =@= ys
Nil       =@= (0 :- ys) = Nil =@= ys
(0 :- xs) =@= Nil       = xs  =@= Nil
_         =@= _         = False

instance Eq (Monomorphic (OrderedMonomial ord)) where
  Monomorphic xs == Monomorphic ys = getMonomial xs =@= getMonomial ys

instance IsMonomialOrder ord => Ord (Monomorphic (OrderedMonomial ord)) where
  compare (Monomorphic (OrderedMonomial m)) (Monomorphic (OrderedMonomial m')) =
      let (mm, mm') = padVec 0 m m'
      in cmpMonomial (Proxy :: Proxy ord) mm mm'

-- | apply buchberger's algorithm using given selection strategy.
syzygyBuchbergerWithStrategy :: ( Field r, IsPolynomial r n, IsMonomialOrder order, SelectionStrategy strategy
                        , Ord (Weight strategy order))
                    => strategy -> Ideal (OrderedPolynomial r order n) -> [OrderedPolynomial r order n]
syzygyBuchbergerWithStrategy strategy ideal = runST $ do
  let gens = zip [1..] $ generators ideal
  gs <- newSTRef $ H.fromList [H.Entry (leadingOrderedMonomial g) g | (_, g) <- gens]
  b  <- newSTRef $ H.fromList $ [H.Entry (calcWeight' strategy f g, j) (f, g) | ((_, f), (j, g)) <- combinations gens]
  len <- newSTRef (genericLength gens :: Integer)
  whileM_ (not . H.null <$> readSTRef b) $ do
    Just (H.Entry _ (f, g), rest) <-  H.viewMin <$> readSTRef b
    gs0 <- readSTRef gs
    b .= rest
    let f0 = leadingMonomial f
        g0 = leadingMonomial g
        l  = lcmMonomial f0 g0
        redundant = H.any (\(H.Entry _ h) -> (h `notElem` [f, g])
                                  && (all (\k -> H.any ((==k) . H.payload) rest)
                                                     [(f, h), (g, h), (h, f), (h, g)])
                                  && leadingMonomial h `divs` l) gs0
    when (l /= zipWithV (+) f0 g0 && not redundant) $ do
      len0 <- readSTRef len
      let qs = (H.toList gs0)
          s = sPolynomial f g `modPolynomial` map H.payload qs
      when (s /= zero) $ do
        b %= H.union (H.fromList [H.Entry (calcWeight' strategy q s, j) (q, s) | H.Entry _ q <- qs | j <- [len0+1..]])
        gs %= H.insert (H.Entry (leadingOrderedMonomial s) s)
        len %= (*2)
  map H.payload . H.toList <$> readSTRef gs

-- | Calculate the weight of given polynomials w.r.t. the given strategy.
-- Buchberger's algorithm proccesses the pair with the most least weight first.
-- This function requires the @Ord@ instance for the weight; this constraint is not required
-- in the 'calcWeight' because of the ease of implementation. So use this function.
calcWeight' :: (SelectionStrategy s, IsPolynomial r n, IsMonomialOrder ord, Ord (Weight s ord))
            => s -> OrderedPolynomial r ord n -> OrderedPolynomial r ord n -> Weight s ord
calcWeight' s = calcWeight (toProxy s)

-- | Type-class for selection strategies in Buchberger's algorithm.
class SelectionStrategy s where
  type Weight s ord :: *
  calcWeight :: (IsPolynomial r n, IsMonomialOrder ord)
             => Proxy s -> OrderedPolynomial r ord n -> OrderedPolynomial r ord n -> Weight s ord

-- | Buchberger's normal selection strategy. This selects the pair with
-- the least LCM(LT(f), LT(g)) w.r.t. current monomial ordering.
data NormalStrategy = NormalStrategy deriving (Read, Show, Eq, Ord)

instance SelectionStrategy NormalStrategy where
  type Weight NormalStrategy ord = Monomorphic (OrderedMonomial ord)
  calcWeight _ f g = Monomorphic $
    OrderedMonomial (lcmMonomial (leadingMonomial f)  (leadingMonomial g))
                                 `asTypeOf` leadingOrderedMonomial f

-- | Choose the pair with the least LCM(LT(f), LT(g)) w.r.t. 'Grevlex' order.
data GrevlexStrategy = GrevlexStrategy deriving (Read, Show, Eq, Ord)

instance SelectionStrategy GrevlexStrategy where
  type Weight GrevlexStrategy ord = Monomorphic (OrderedMonomial Grevlex)
  calcWeight _ f g = Monomorphic $ OrderedMonomial $ lcmMonomial (leadingMonomial f) (leadingMonomial g)

data GradedStrategy = GradedStrategy deriving (Read, Show, Eq, Ord)

-- | Choose the pair with the least LCM(LT(f), LT(g)) w.r.t. graded current ordering.
instance SelectionStrategy GradedStrategy where
  type Weight GradedStrategy ord = Monomorphic (OrderedMonomial (Graded ord))
  calcWeight _ f g = Monomorphic $ OrderedMonomial (lcmMonomial (leadingMonomial f)  (leadingMonomial g))

-- | Sugar strategy. This chooses the pair with the least phantom homogenized degree and then break the tie with the given strategy (say @s@).
data SugarStrategy s = SugarStrategy s deriving (Read, Show, Eq, Ord)

instance SelectionStrategy s => SelectionStrategy (SugarStrategy s) where
  type Weight (SugarStrategy s) ord = (Int, Weight s ord)
  calcWeight (Proxy :: Proxy (SugarStrategy s)) f g = (sugar, calcWeight (Proxy :: Proxy s) f g)
    where
      deg' = maximum . map (totalDegree . snd) . getTerms
      tsgr h = deg' h - totalDegree (leadingMonomial h)
      sugar = max (tsgr f) (tsgr g) + totalDegree (lcmMonomial (leadingMonomial f) (leadingMonomial g))

-- | Minimize the given groebner basis.
minimizeGroebnerBasis :: (Field k, IsPolynomial k n, IsMonomialOrder order)
                      => [OrderedPolynomial k order n] -> [OrderedPolynomial k order n]
minimizeGroebnerBasis = foldr step []
  where
    step x xs =  injectCoeff (recip $ leadingCoeff x) * x : filter (not . (leadingMonomial x `divs`) . leadingMonomial) xs

-- | Reduce minimum Groebner basis into reduced Groebner basis.
reduceMinimalGroebnerBasis :: (Field k, IsPolynomial k n, IsMonomialOrder order)
                           => [OrderedPolynomial k order n] -> [OrderedPolynomial k order n]
reduceMinimalGroebnerBasis bs = filter (/= zero) $  map red bs
  where
    red x = x `modPolynomial` delete x bs

-- | Caliculating reduced Groebner basis of the given ideal w.r.t. the specified monomial order.
calcGroebnerBasisWith :: (Field k, IsPolynomial k n, IsMonomialOrder order, IsMonomialOrder order')
                      => order -> Ideal (OrderedPolynomial k order' n) -> [OrderedPolynomial k order n]
calcGroebnerBasisWith ord i = calcGroebnerBasis $  mapIdeal (changeOrder ord) i

-- | Caliculating reduced Groebner basis of the given ideal w.r.t. the specified monomial order.
calcGroebnerBasisWithStrategy :: ( Field k, IsPolynomial k n, IsMonomialOrder order
                                 , SelectionStrategy strategy, Ord (Weight strategy order))
                      => strategy -> Ideal (OrderedPolynomial k order n) -> [OrderedPolynomial k order n]
calcGroebnerBasisWithStrategy strategy =
  reduceMinimalGroebnerBasis . minimizeGroebnerBasis . syzygyBuchbergerWithStrategy strategy

-- | Caliculating reduced Groebner basis of the given ideal.
calcGroebnerBasis :: (Field k, IsPolynomial k n, IsMonomialOrder order)
                  => Ideal (OrderedPolynomial k order n) -> [OrderedPolynomial k order n]
calcGroebnerBasis = reduceMinimalGroebnerBasis . minimizeGroebnerBasis . syzygyBuchberger

-- | Test if the given polynomial is the member of the ideal.
isIdealMember :: (IsPolynomial k n, Field k, IsMonomialOrder o)
              => OrderedPolynomial k o n -> Ideal (OrderedPolynomial k o n) -> Bool
isIdealMember f ideal = groebnerTest f (calcGroebnerBasis ideal)

-- | Test if the given polynomial can be divided by the given polynomials.
groebnerTest :: (IsPolynomial k n, Field k, IsMonomialOrder order)
             => OrderedPolynomial k order n -> [OrderedPolynomial k order n] -> Bool
groebnerTest f fs = f `modPolynomial` fs == zero

-- | Calculate n-th elimination ideal using 'WeightedEliminationOrder' ordering.
thEliminationIdeal :: ( IsMonomialOrder ord, Field k, IsPolynomial k m, IsPolynomial k (m :-: n)
                      , (n :<<= m) ~ True)
                   => SNat n
                   -> Ideal (OrderedPolynomial k ord m)
                   -> Ideal (OrderedPolynomial k ord (m :-: n))
thEliminationIdeal n =
    case singInstance n of
      SingInstance ->
          mapIdeal (changeOrderProxy Proxy) . thEliminationIdealWith (weightedEliminationOrder n) n

-- | Calculate n-th elimination ideal using the specified n-th elimination type order.
thEliminationIdealWith :: ( IsMonomialOrder ord, Field k, IsPolynomial k m, IsPolynomial k (m :-: n)
                      , (n :<<= m) ~ True, EliminationType n ord, IsMonomialOrder ord')
                   => ord
                   -> SNat n
                   -> Ideal (OrderedPolynomial k ord' m)
                   -> Ideal (OrderedPolynomial k ord (m :-: n))
thEliminationIdealWith ord n ideal =
    case singInstance n of
      SingInstance ->  toIdeal $ [ transformMonomial (dropV n) f
                                 | f <- calcGroebnerBasisWith ord ideal
                                 , all (all (== 0) . take (toInt n) . toList . snd) $ getTerms f
                                 ]

-- | Calculate n-th elimination ideal using the specified n-th elimination type order.
-- This function should be used carefully because it does not check whether the given ordering is
-- n-th elimintion type or not.
unsafeThEliminationIdealWith :: ( IsMonomialOrder ord, Field k, IsPolynomial k m, IsPolynomial k (m :-: n)
                                , (n :<<= m) ~ True, IsMonomialOrder ord')
                             => ord
                             -> SNat n
                             -> Ideal (OrderedPolynomial k ord' m)
                             -> Ideal (OrderedPolynomial k ord (m :-: n))
unsafeThEliminationIdealWith ord n ideal =
    case singInstance n of
      SingInstance ->  toIdeal $ [ transformMonomial (dropV n) f
                                 | f <- calcGroebnerBasisWith ord ideal
                                 , all (all (== 0) . take (toInt n) . toList . snd) $ getTerms f
                                 ]

-- | An intersection ideal of given ideals (using 'WeightedEliminationOrder').
intersection :: forall r k n ord.
                ( IsMonomialOrder ord, Field r, IsPolynomial r k, IsPolynomial r n
                , IsPolynomial r (k :+: n)
                )
             => Vector (Ideal (OrderedPolynomial r ord n)) k
             -> Ideal (OrderedPolynomial r ord n)
intersection Nil = Ideal $ singletonV one
intersection idsv@(_ :- _) =
    let sk = sLengthV idsv
        sn = sing :: SNat n
        ts  = genVars (sk %+ sn)
        tis = zipWith (\ideal t -> mapIdeal ((t *) . shiftR sk) ideal) (toList idsv) ts
        j = foldr appendIdeal (principalIdeal (one - foldr (+) zero ts)) tis
    in case plusMinusEqR sn sk of
         Eql -> case propToBoolLeq (plusLeqL sk sn) of
                  LeqTrueInstance -> thEliminationIdeal sk j

-- | Ideal quotient by a principal ideals.
quotByPrincipalIdeal :: (Field k, IsPolynomial k n, IsMonomialOrder ord)
                     => Ideal (OrderedPolynomial k ord n)
                     -> OrderedPolynomial k ord n
                     -> Ideal (OrderedPolynomial k ord n)
quotByPrincipalIdeal i g =
    case intersection (i :- (Ideal $ singletonV g) :- Nil) of
      Ideal gs -> Ideal $ mapV (snd . head . (`divPolynomial` [g])) gs

-- | Ideal quotient by the given ideal.
quotIdeal :: forall k ord n. (IsPolynomial k n, Field k, IsMonomialOrder ord)
          => Ideal (OrderedPolynomial k ord n)
          -> Ideal (OrderedPolynomial k ord n)
          -> Ideal (OrderedPolynomial k ord n)
quotIdeal i (Ideal g) =
  case singInstance (sLengthV g) of
    SingInstance ->
        case singInstance (sLengthV g %+ (sing :: SNat n)) of
          SingInstance -> intersection $ mapV (i `quotByPrincipalIdeal`) g

-- | Saturation by a principal ideal.
saturationByPrincipalIdeal :: (Field k, IsPolynomial k n, IsMonomialOrder ord)
                           => Ideal (OrderedPolynomial k ord n)
                           -> OrderedPolynomial k ord n -> Ideal (OrderedPolynomial k ord n)
saturationByPrincipalIdeal is g =
  case propToClassLeq $ leqSucc (sDegree g) of
    LeqInstance -> thEliminationIdeal sOne $ addToIdeal (one - (castPolynomial g * var sOne)) (mapIdeal (shiftR sOne) is)

-- | Saturation ideal
saturationIdeal :: forall k ord n. (IsPolynomial k n, Field k, IsMonomialOrder ord)
                => Ideal (OrderedPolynomial k ord n)
                -> Ideal (OrderedPolynomial k ord n)
                -> Ideal (OrderedPolynomial k ord n)
saturationIdeal i (Ideal g) =
  case singInstance (sLengthV g) of
    SingInstance ->
        case singInstance (sLengthV g %+ (sing :: SNat n)) of
          SingInstance -> intersection $ mapV (i `saturationByPrincipalIdeal`) g

