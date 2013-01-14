{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts     #-}
{-# LANGUAGE MultiParamTypeClasses, RankNTypes, TypeOperators #-}
module Algorithms where
import Data.List
import Polynomial

x, y, a, b, c, s, f, f1, f2 :: Polynomial Rational (S (S (S Three)))
x = var sOne
y = var sTwo
f = x^2 * y + x * y^2 + y^2
f1 = x * y - 1
f2 = y^2 - 1

a = var sThree
b = var (SS sThree)
c = var (SS (SS sThree))
s = var (SS (SS (SS sThree)))

divModPolynomial :: (IsMonomialOrder order, IsPolynomial r n, Field r)
                  => OrderedPolynomial r order n -> [OrderedPolynomial r order n] -> ([(OrderedPolynomial r order n, OrderedPolynomial r order n)], OrderedPolynomial r order n)
divModPolynomial f0 fs = loop f0 zero (zip (nub fs) (repeat zero))
  where
    loop p r dic
        | p == zero = (dic, r)
        | otherwise =
            let ltP = toPolynomial $ leadingTerm p
            in case break ((`divs` leadingMonomial p) . leadingMonomial . fst) dic of
                 (_, []) -> loop (p .-. ltP) (r .+. ltP) dic
                 (xs, (g, old):ys) ->
                     let q = toPolynomial $ leadingTerm p `tryDiv` leadingTerm g
                         dic' = xs ++ (g, old .+. q) : ys
                     in loop (p .-. (q .*. g)) r dic'

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
    step x xs =  injectCoeff (inv $ leadingCoeff x) .*. x : filter (not . (leadingMonomial x `divs`) . leadingMonomial) xs

reduceMinimalGroebnerBasis :: (Field k, IsPolynomial k n, IsMonomialOrder order)
                    => [OrderedPolynomial k order n] -> [OrderedPolynomial k order n]
reduceMinimalGroebnerBasis bs = filter (/= zero) $  map red bs
  where
    red x = x `modPolynomial` delete x bs

calcGroebnerBasisWith :: (Field k, IsPolynomial k n, IsMonomialOrder order, IsMonomialOrder order', n :<= n)
                      => order -> Ideal (OrderedPolynomial k order' n) -> [OrderedPolynomial k order n]
calcGroebnerBasisWith order (Ideal gs) = calcGroebnerBasis $ Ideal $ map (changeOrder order) gs

calcGroebnerBasis :: (Field k, IsPolynomial k n, IsMonomialOrder order)
                  => Ideal (OrderedPolynomial k order n) -> [OrderedPolynomial k order n]
calcGroebnerBasis = reduceMinimalGroebnerBasis . minimizeGroebnerBasis . simpleBuchberger

isIdealMember :: (IsPolynomial k n, Field k, IsMonomialOrder o)
              => OrderedPolynomial k o n -> Ideal (OrderedPolynomial k o n) -> Bool
isIdealMember f ideal = groebnerTest f (calcGroebnerBasis ideal)

groebnerTest :: (IsPolynomial k n, Field k, IsMonomialOrder order)
             => OrderedPolynomial k order n -> [OrderedPolynomial k order n] -> Bool
groebnerTest f fs = f `modPolynomial` fs == zero


thEliminationIdeal :: (IsPolynomial k (n :+: m), Field k, IsMonomialOrder order, ((n :+:m) :<= (n :+: m)))
                   => SNat n
                   -> Ideal (OrderedPolynomial k order (n :+: m))
                   -> Ideal (OrderedPolynomial k Lex (n :+: m))
n `thEliminationIdeal` ideal = Ideal [f | f <- calcGroebnerBasisWith Lex ideal
                                        , all (all (== 0) . take (toInt n) . toList . snd) $ getTerms f
                                     ]
