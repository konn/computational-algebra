{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, GADTs             #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude, ParallelListComp      #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, TemplateHaskell, TypeOperators #-}
module Algebra.Algorithms.Groebner (
                                   -- * Polynomial division
                                     divModPolynomial, divPolynomial, modPolynomial
                                   -- * Groebner basis
                                   , calcGroebnerBasis, calcGroebnerBasisWith
                                   , buchberger, syzygyBuchberger, simpleBuchberger, primeTestBuchberger
                                   , reduceMinimalGroebnerBasis, minimizeGroebnerBasis
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

combinations :: [a] -> [(a, a)]
combinations xs = concat $ zipWith (map . (,)) xs $ drop 1 $ tails xs

-- | Calculate Groebner basis applying (modified) Buchberger's algorithm.
-- This function is same as 'syzygyBuchberger'.
buchberger :: (Field r, IsPolynomial r n, IsMonomialOrder order)
           => Ideal (OrderedPolynomial r order n) -> [OrderedPolynomial r order n]
buchberger = syzygyBuchberger

-- | Buchberger's algorithm greately improved using the syzygy theory.
-- Utilizing priority queues, this function reduces division complexity and comparison time.
-- If you don't have strong reason to avoid this function, this function is recommended to use.
syzygyBuchberger :: (Field r, IsPolynomial r n, IsMonomialOrder order)
                    => Ideal (OrderedPolynomial r order n) -> [OrderedPolynomial r order n]
syzygyBuchberger ideal = runST $ do
  let gens = generators ideal
      lcmm = lcmMonomial `on` leadingMonomial
  gs <- newSTRef $ H.fromList [H.Entry (leadingMonomial g) g | g <- gens]
  b  <- newSTRef $ H.fromList $ [H.Entry (lcmm f g) (f, g) | (f, g) <- combinations gens]
  whileM_ (not . H.null <$> readSTRef b) $ do
    Just (H.Entry _ (f, g), rest) <- H.viewMin <$> readSTRef b
    gs0 <- readSTRef gs
    b .= rest
    let f0 = leadingMonomial f
        g0 = leadingMonomial g
        l = lcmMonomial f0 g0
        redundant = H.any (\(H.Entry _ h) -> h `notElem` [f, g]
                                  && all (\k -> H.any ((==k) . H.payload) rest) [(f, h), (g, h), (h, f), (h, g)]
                                  && leadingMonomial h `divs` l) gs0
    when (l /= zipWithV (+) f0 g0 && not redundant) $ do
          let qs = (H.toList gs0)
              s = sPolynomial f g `modPolynomial` map H.payload qs
          when (s /= zero) $ do
            b %= H.union (H.fromList [H.Entry (lcmm q s) (q, s) | H.Entry _ q <- qs])
            gs %= H.insert (H.Entry (leadingMonomial s) s)
  map H.payload . H.toList <$> readSTRef gs

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
calcGroebnerBasisWith ord i = calcGroebnerBasis $ mapIdeal (changeOrder ord) i

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

-- | Calculate n-th elimination ideal using 'Lex' ordering.
thEliminationIdeal :: ( IsMonomialOrder ord, Field k, IsPolynomial k m, IsPolynomial k (m :-: n)
                      , (n :<<= m) ~ True)
                   => SNat n
                   -> Ideal (OrderedPolynomial k ord m)
                   -> Ideal (OrderedPolynomial k Lex (m :-: n))
thEliminationIdeal n = case singInstance n of SingInstance -> thEliminationIdealWith Lex n

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


-- | An intersection ideal of given ideals.
intersection :: forall r k n ord.
                ( IsMonomialOrder ord, Field r, IsPolynomial r k, IsPolynomial r n
                , IsPolynomial r (k :+: n)
                )
             => Vector (Ideal (OrderedPolynomial r ord n)) k
             -> Ideal (OrderedPolynomial r Lex n)
intersection Nil = Ideal $ singletonV one
intersection idsv@(_ :- _) =
    let sk = sLengthV idsv
        sn = sing :: SNat n
        ts  = genVars (sk %+ sn)
        tis = zipWith (\ideal t -> mapIdeal ((t *) . shiftR sk) ideal) (toList idsv) ts
        j = foldr appendIdeal (principalIdeal (one - foldr (+) zero ts)) tis
    in case plusMinusEqR sn sk of
         Eql -> case propToBoolLeq (plusLeqL sk sn) of
                  LeqTrueInstance -> sk `thEliminationIdeal` j

-- | Ideal quotient by a principal ideals.
quotByPrincipalIdeal :: (Field k, IsPolynomial k n, IsMonomialOrder ord)
                     => Ideal (OrderedPolynomial k ord n)
                     -> OrderedPolynomial k ord n
                     -> Ideal (OrderedPolynomial k Lex n)
quotByPrincipalIdeal i g =
    case intersection (i :- (Ideal $ singletonV g) :- Nil) of
      Ideal gs -> Ideal $ mapV (snd . head . (`divPolynomial` [changeOrder Lex g])) gs

-- | Ideal quotient by the given ideal.
quotIdeal :: forall k ord n. (IsPolynomial k n, Field k, IsMonomialOrder ord)
          => Ideal (OrderedPolynomial k ord n)
          -> Ideal (OrderedPolynomial k ord n)
          -> Ideal (OrderedPolynomial k Lex n)
quotIdeal i (Ideal g) =
  case singInstance (sLengthV g) of
    SingInstance ->
        case singInstance (sLengthV g %+ (sing :: SNat n)) of
          SingInstance -> intersection $ mapV (i `quotByPrincipalIdeal`) g

-- | Saturation by a principal ideal.
saturationByPrincipalIdeal :: (Field k, IsPolynomial k n, IsMonomialOrder ord)
                           => Ideal (OrderedPolynomial k ord n)
                           -> OrderedPolynomial k ord n -> Ideal (OrderedPolynomial k Lex n)
saturationByPrincipalIdeal is g =
  case propToClassLeq $ leqSucc (sDegree g) of
    LeqInstance -> sOne `thEliminationIdeal` addToIdeal (one - (castPolynomial g * var sOne)) (mapIdeal (shiftR sOne) is)

-- | Saturation ideal
saturationIdeal :: forall k ord n. (IsPolynomial k n, Field k, IsMonomialOrder ord)
                => Ideal (OrderedPolynomial k ord n)
                -> Ideal (OrderedPolynomial k ord n)
                -> Ideal (OrderedPolynomial k Lex n)
saturationIdeal i (Ideal g) =
  case singInstance (sLengthV g) of
    SingInstance ->
        case singInstance (sLengthV g %+ (sing :: SNat n)) of
          SingInstance -> intersection $ mapV (i `saturationByPrincipalIdeal`) g

