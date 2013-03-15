{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, GADTs        #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude, ParallelListComp #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, TypeOperators             #-}
module Algebra.Algorithms.Groebner where
import Algebra.Internal
import Algebra.Ring.Noetherian
import Algebra.Ring.Polynomial
import Data.List
import Numeric.Algebra
import Prelude                 hiding (Num (..), recip)

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

modPolynomial :: (IsPolynomial r n, Field r, IsMonomialOrder order)
              => OrderedPolynomial r order n
              -> [OrderedPolynomial r order n]
              -> OrderedPolynomial r order n
modPolynomial = (snd .) . divModPolynomial

divPolynomial :: (IsPolynomial r n, Field r, IsMonomialOrder order)
              => OrderedPolynomial r order n
              -> [OrderedPolynomial r order n]
              -> [(OrderedPolynomial r order n, OrderedPolynomial r order n)]
divPolynomial = (fst .) . divModPolynomial

infixl 7 `divPolynomial`
infixl 7 `modPolynomial`
infixl 7 `divModPolynomial`

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

minimizeGroebnerBasis :: (Field k, IsPolynomial k n, IsMonomialOrder order)
                      => [OrderedPolynomial k order n] -> [OrderedPolynomial k order n]
minimizeGroebnerBasis = foldr step []
  where
    step x xs =  injectCoeff (recip $ leadingCoeff x) * x : filter (not . (leadingMonomial x `divs`) . leadingMonomial) xs

reduceMinimalGroebnerBasis :: (Field k, IsPolynomial k n, IsMonomialOrder order)
                    => [OrderedPolynomial k order n] -> [OrderedPolynomial k order n]
reduceMinimalGroebnerBasis bs = filter (/= zero) $  map red bs
  where
    red x = x `modPolynomial` delete x bs

calcGroebnerBasisWith :: (Field k, IsPolynomial k n, IsMonomialOrder order, IsMonomialOrder order')
                      => order -> Ideal (OrderedPolynomial k order' n) -> [OrderedPolynomial k order n]
calcGroebnerBasisWith order i = calcGroebnerBasis $ mapIdeal (changeOrder order) i

calcGroebnerBasis :: (Field k, IsPolynomial k n, IsMonomialOrder order)
                  => Ideal (OrderedPolynomial k order n) -> [OrderedPolynomial k order n]
calcGroebnerBasis = reduceMinimalGroebnerBasis . minimizeGroebnerBasis . simpleBuchberger

isIdealMember :: (IsPolynomial k n, Field k, IsMonomialOrder o)
              => OrderedPolynomial k o n -> Ideal (OrderedPolynomial k o n) -> Bool
isIdealMember f ideal = groebnerTest f (calcGroebnerBasis ideal)

groebnerTest :: (IsPolynomial k n, Field k, IsMonomialOrder order)
             => OrderedPolynomial k order n -> [OrderedPolynomial k order n] -> Bool
groebnerTest f fs = f `modPolynomial` fs == zero


thEliminationIdeal :: ( IsMonomialOrder ord, Field k, IsPolynomial k m, IsPolynomial k (n :+: m)
                       )
                   => SNat n
                   -> Ideal (OrderedPolynomial k ord (n :+: m))
                   -> Ideal (OrderedPolynomial k Lex m)
thEliminationIdeal n ideal =
    toIdeal $ [transformMonomial (dropV n) f | f <- calcGroebnerBasisWith Lex ideal
               , all (all (== 0) . take (toInt n) . toList . snd) $ getTerms f
               ]

-- | An intersection ideal of given ideals.
intersection :: forall r k n ord.
                ( IsMonomialOrder ord, Field r, IsPolynomial r k, IsPolynomial r n
                , IsPolynomial r (k :+: n)
                )
             => Vector (Ideal (OrderedPolynomial r ord n)) k -> Ideal (OrderedPolynomial r Lex n)
intersection Nil = Ideal $ singletonV one
intersection idsv@(_ :- _) =
    let sk = sLengthV idsv
        sn = sing :: SNat n
        ts  = genVars (sk %+ sn)
        tis = zipWith (\ideal t -> mapIdeal ((t *) . shiftR sk) ideal) (toList idsv) ts
        j = foldr appendIdeal (principalIdeal (one - foldr (+) zero ts)) tis
    in sk `thEliminationIdeal` j

-- | Ideal quotient by a principal ideals.
quotByPrincipalIdeal :: (Field k, IsPolynomial k n, IsMonomialOrder ord)
                     => Ideal (OrderedPolynomial k ord n)
                     -> OrderedPolynomial k ord n
                     -> Ideal (OrderedPolynomial k Lex n)
quotByPrincipalIdeal i g =
    case intersection (i :- (Ideal $ singletonV g) :- Nil) of
      Ideal gs -> Ideal $ mapV (snd . head . (`divPolynomial` [changeOrder Lex g])) gs

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
  case leqSucc (sDegree g) of
    LeqInstance -> sOne `thEliminationIdeal` addToIdeal (one - (castPolynomial g * var sOne)) (mapIdeal (shiftR sOne) is)

saturationIdeal :: forall k ord n. (IsPolynomial k n, Field k, IsMonomialOrder ord)
                => Ideal (OrderedPolynomial k ord n)
                -> Ideal (OrderedPolynomial k ord n)
                -> Ideal (OrderedPolynomial k Lex n)
saturationIdeal i (Ideal g) =
  case singInstance (sLengthV g) of
    SingInstance ->
        case singInstance (sLengthV g %+ (sing :: SNat n)) of
          SingInstance -> intersection $ mapV (i `saturationByPrincipalIdeal`) g
