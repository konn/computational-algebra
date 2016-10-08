{-# LANGUAGE ConstraintKinds, ExistentialQuantification, FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances, IncoherentInstances, MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction, PolyKinds       #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances, ViewPatterns      #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
-- | Provides general framework for signature-based algorithms
module Algebra.Algorithms.Signature where
import           Algebra.Algorithms.Groebner
import           Algebra.Prelude.Core        hiding (mapMaybe, singleton,
                                              uncons)
import           Control.Applicative         ((<|>))
import           Control.Arrow               (second, (&&&), (>>>))
import qualified Data.Foldable               as F
import           Data.Heap                   (Entry (..), uncons)
import qualified Data.Heap                   as H
import           Data.IntMap.Strict          (IntMap, mapMaybe, mergeWithKey)
import           Data.IntMap.Strict          (singleton)
import qualified Data.IntMap.Strict          as IM
import           Data.List                   (tails)
import           Data.List                   (sort)
import           Data.Monoid                 ((<>))
import           Data.Reflection             (Given)
import           Data.Reflection             (given)
import           Data.Reflection             (give)
import qualified Data.Set                    as S
import           Debug.Trace
import           Numeric.Decidable.Zero      (isZero)

tr :: Show a => String -> a -> a
tr str a = trace (str ++ " " ++ show a) a

type PolynomialModule r ord n = IntMap (OrderedPolynomial r ord n)

data SomeModuleOrder ord n =
  forall mord. ModuleOrdering mord => SomeModuleOrder (mord ord n)

instance (DecidableZero a, Additive a) => Additive (IntMap a) where
  (+) = mergeWithKey
        (\_ a b -> let c = a + b in if isZero c then Nothing else Just c) id id
  {-# INLINE (+) #-}


instance (DecidableZero a, Semiring a) => LeftModule a (IntMap a) where
  (.*) a = mapMaybe (\d -> let c = a*d in if isZero c then Nothing else Just c)
  {-# INLINE (.*) #-}

instance (DecidableZero a, Semiring a) => RightModule a (IntMap a) where
  m *. a = mapMaybe (\d -> let c = d*a in if isZero c then Nothing else Just c) m
  {-# INLINE (*.) #-}

instance DecidableZero a => DecidableZero (IntMap a) where
  isZero m = IM.null m || F.all isZero m
  {-# INLINE isZero #-}

instance (LeftModule Integer a, DecidableZero a, Additive a) => LeftModule Integer (IntMap a) where
  i .* m = mapMaybe (\d -> let c = i .* d in if isZero c then Nothing else Just c) m

instance (RightModule Integer a, DecidableZero a, Additive a) => RightModule Integer (IntMap a) where
  m *. i = mapMaybe (\d -> let c = d *. i in if isZero c then Nothing else Just c) m

instance (LeftModule Natural a, DecidableZero a, Additive a) => LeftModule Natural (IntMap a) where
  i .* m = mapMaybe (\d -> let c = i .* d in if isZero c then Nothing else Just c) m

instance (RightModule Natural a, DecidableZero a, Additive a) => RightModule Natural (IntMap a) where
  m *. i = mapMaybe (\d -> let c = d *. i in if isZero c then Nothing else Just c) m

instance (KnownNat n, IsMonomialOrder n ord, Given (SomeModuleOrder ord n)) => Ord (Signature ord n) where
  compare =
    case given :: SomeModuleOrder ord n of
      SomeModuleOrder mord -> compareSignature mord

instance (DecidableZero a, Additive a) => Monoidal (IntMap a) where
  zero = IM.empty

instance (DecidableZero a, Group a) => Group (IntMap a) where
  negate = IM.map negate

injectModuleTerm :: (KnownNat n, CoeffRing a, IsMonomialOrder n ord)
                 => Signature ord n -> IntMap (OrderedPolynomial a ord n)
injectModuleTerm = generator &&& monomial >>> second (curry toPolynomial one) >>> uncurry singleton

mlt :: (Given (SomeModuleOrder ord n), KnownNat n, CoeffRing r, IsMonomialOrder n ord)
    => PolynomialModule r ord n -> Signature ord n
mlt m | IM.null m = error "zero module element"
      | otherwise = maximum $ concatMap (\(i, p) -> map (Signature i) $ S.toList $ orderedMonomials p) $ IM.toList $ m

data Signature ord n = Signature { generator :: Int
                                 , monomial  :: OrderedMonomial ord n
                                 } deriving (Show, Eq)

data LabeledPoly r ord n = LabPoly { signature :: Signature ord n
                                   , poly      :: OrderedPolynomial r ord n
                                   } deriving (Eq)

deriving instance (KnownNat n, Show (OrderedPolynomial r ord n))
               => Show (LabeledPoly r ord n)

class ModuleOrdering sord where
  compareSignature :: (KnownNat n, IsMonomialOrder n ord)
                   => sord ord n -> Signature ord n -> Signature ord n -> Ordering

-- | Preferring the module position
data POT ord n = POT

instance ModuleOrdering POT where
  compareSignature _ (Signature i t) (Signature j u) = compare i j <> compare t u

-- | Schreyer ordering
data Schreyer ord n = Schreyer [OrderedMonomial ord n]

instance ModuleOrdering Schreyer where
  compareSignature (Schreyer ms) (Signature i t) (Signature j u) =
    compare (t * (ms !! i)) (u * (ms !! j)) <> compare i j

lm :: (CoeffRing r, KnownNat n, IsMonomialOrder n order)
   => LabeledPoly r order n -> OrderedMonomial order n
lm = leadingMonomial . poly

lc :: (KnownNat n, CoeffRing r, IsMonomialOrder n order)
   => LabeledPoly r order n -> r
lc = leadingCoeff . poly

(@*) :: (CoeffRing r, KnownNat n, IsMonomialOrder n order)
     => OrderedMonomial order n -> IntMap (OrderedPolynomial r order n) -> IntMap (OrderedPolynomial r order n)
m @* pm = IM.map (\ k -> toPolynomial (one, m) * k) pm

sLabPoly :: forall r ord n. (Given (SomeModuleOrder ord n), CoeffRing r,
                             KnownNat n, IsMonomialOrder n ord)
         => LabeledPoly r ord n -> LabeledPoly r ord n -> LabeledPoly r ord n
sLabPoly f g =
  let uf = lcmMonomial (lm f) (lm g) / lm f
      ug = lcmMonomial (lm f) (lm g) / lm g
      sf = injectModuleTerm (signature f) :: PolynomialModule r ord n
      sg = injectModuleTerm (signature g)
      spol = toPolynomial (lc g, uf) * poly f - toPolynomial (lc f, ug) * poly g
      omega = mlt $ uf @* sf - ug @* sg
  in LabPoly omega spol

-- | Naive, signature-based Groebner basis computation
calcGBWithSignature :: (ModuleOrdering mord, IsMonomialOrder n ord, Field r, Ord r, CoeffRing r, KnownNat n)
                    => mord ord n
                    -> Ideal (OrderedPolynomial r ord n)
                    -> Ideal (OrderedPolynomial r ord n)
calcGBWithSignature mord (map monoize . filter (not . isZero) . generators -> is)
  | null is   = toIdeal [zero]
  | otherwise = toIdeal $ sort $ reduceMinimalGroebnerBasis $ minimizeGroebnerBasis $ give (SomeModuleOrder mord) $
    let gs0 = zipWith LabPoly (map (flip Signature one) [0..]) is
        ps0 = H.fromList [ Entry (signature s) (gi, gj)
                         | (gj:rest) <- tails gs0, gi <- rest
                         , let s = sLabPoly gi gj
                         , not $ isZero $ poly s]
    in go ps0 gs0
  where
    go ps gs =
      case uncons ps of
        Nothing -> map poly gs
        Just (Entry _ (f, g), ps') ->
          let r = sLabPoly f g
          in if not (isZero $  poly r) && not (notRedundant gs r)
             then
               let ps'' = H.fromList [Entry (signature s) (r, h)
                                     | h <- gs
                                     , let s = sLabPoly r h
                                     , not $ isZero $ poly s
                                     , not $ nonMinimal r h
                                     ]
               in go (H.union ps' ps'') (gs ++ [r])
             else go ps' gs

nonMinimal :: (Given (SomeModuleOrder ord n), KnownNat n
              , CoeffRing r, IsMonomialOrder n ord)
           => LabeledPoly r ord n -> LabeledPoly r ord n -> Bool
nonMinimal f g =
  signature (sLabPoly f g) < max (uf |* signature f) (ug |* signature g)
  where
    uf = lcmMonomial (lm f) (lm g) / lm f
    ug = lcmMonomial (lm f) (lm g) / lm g

(|*) :: OrderedMonomial ord n -> Signature ord n -> Signature ord n
u |* Signature i t = Signature i (u*t)

notRedundant :: (KnownNat n, CoeffRing r, IsMonomialOrder n ord)
                => [LabeledPoly r ord n] -> LabeledPoly r ord n -> Bool
notRedundant gs f = any (\ h -> (signature h `divsSiv` signature f) && (lm h `divs` lm f)) gs

divsSiv :: Signature ord n -> Signature ord n -> Bool
divsSiv (Signature i t) (Signature j u) = i == j && t `divs` u

sigSafeRed :: forall r ord n. (Given (SomeModuleOrder ord n), CoeffRing r,
                               KnownNat n, Field r, IsMonomialOrder n ord)
           => [LabeledPoly r ord n] -> LabeledPoly r ord n -> LabeledPoly r ord n
sigSafeRed gs f = go f
  where
    go r =
      case crit r of
        Nothing -> r
        Just p -> go p
    crit r = foldr (<|>) Nothing $ flip map gs $ \ g ->
      let c = lc r / lc g
          t = lm r / lm g
          r' = poly r - toPolynomial (c,t) * poly g
          sr = injectModuleTerm $ signature r :: PolynomialModule r ord n
          s' = mlt $ sr - injectModuleTerm (t |* signature g)
      in if lm g `divs` lm r && t |* signature g < signature r
         then Just (LabPoly s' r')
         else Nothing

infixl 7 *?
(*?) :: (CoeffRing r, KnownNat n, IsMonomialOrder n ord)
     => (r, OrderedMonomial ord n) -> LabeledPoly r ord n -> LabeledPoly r ord n
(c, t) *? (LabPoly s f) = LabPoly (t |* s) (toPolynomial (c, t) * f)
