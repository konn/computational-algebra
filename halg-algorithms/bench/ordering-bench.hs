{-# LANGUAGE BangPatterns, DataKinds, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, NoImplicitPrelude              #-}
{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings, PolyKinds      #-}
{-# LANGUAGE TypeFamilies, UndecidableInstances, ViewPatterns             #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans -Wall #-}
module Main where
import           Algebra.Algorithms.Groebner
import           Algebra.Algorithms.Groebner.Signature
import           Algebra.Internal
import           Algebra.Prelude.Core
import           Control.Foldl                         (Fold)
import qualified Control.Foldl                         as Fl
import           Control.Lens                          (_1, _2)
import           Data.Monoid                           (Dual (..))
import           Data.Sequence                         (Seq ((:|>), Empty))
import qualified Data.Sequence                         as Seq
import           Data.Sized.Builtin                    (unsized)
import           Gauge.Main
import           Gauge.Types

type Comparer = Fold (Int, Int) Ordering

gradeF :: Comparer
gradeF = compare <$> Fl.handles _1 Fl.sum <*> Fl.handles _2 Fl.sum
{-# INLINE gradeF #-}

revlexF :: Comparer
revlexF = Fl.foldMap (Dual . uncurry (flip compare)) getDual
{-# INLINE revlexF #-}

data FoldlGrevlex = FoldlGrevlex

instance SingI n => IsOrder n FoldlGrevlex where
  cmpMonomial _ (unsized -> m) (unsized -> n) =
    Fl.fold  ((<>) <$> gradeF <*> revlexF) $ Seq.zip m n
  {-# INLINE cmpMonomial #-}

instance SingI n => IsMonomialOrder n FoldlGrevlex

grevlexHW :: Seq Int -> Seq Int -> Int -> Int -> Ordering -> Ordering
grevlexHW (as :|> a) (bs :|> b)  !accl !accr EQ =
  grevlexHW as bs (accl + a) (accr + b) $ compare b a
grevlexHW as bs !accl !accr cmp = compare (sum as + accl) (sum bs + accr) <> cmp

data HandWrittenGrevlex = HandWrittenGrevlex

instance SingI n => IsOrder n HandWrittenGrevlex where
  cmpMonomial _ (unsized -> m) (unsized -> n) = grevlexHW m n 0 0 EQ
  {-# INLINE cmpMonomial #-}

instance SingI n => IsMonomialOrder n HandWrittenGrevlex


i2G :: [OrderedPolynomial (Fraction Integer) Grevlex 5]
i2G =  [35 * y^4 - 30*x*y^2 - 210*y^2*z + 3*x^2 + 30*x*z - 105*z^2 +140*y*t - 21*u
       ,5*x*y^3 - 140*y^3*z - 3*x^2*y + 45*x*y*z - 420*y*z^2 + 210*y^2*t -25*x*t + 70*z*t + 126*y*u
       ]
     where [t,u,x,y,z] = vars

i2FlG :: [OrderedPolynomial (Fraction Integer) FoldlGrevlex 5]
i2FlG =
  [35 * y^4 - 30*x*y^2 - 210*y^2*z + 3*x^2 + 30*x*z - 105*z^2 +140*y*t - 21*u
  ,5*x*y^3 - 140*y^3*z - 3*x^2*y + 45*x*y*z - 420*y*z^2 + 210*y^2*t -25*x*t + 70*z*t + 126*y*u
  ]
  where [t,u,x,y,z] = vars

i2HWG :: [OrderedPolynomial (Fraction Integer) HandWrittenGrevlex 5]
i2HWG =
  [35 * y^4 - 30*x*y^2 - 210*y^2*z + 3*x^2 + 30*x*z - 105*z^2 +140*y*t - 21*u
  ,5*x*y^3 - 140*y^3*z - 3*x^2*y + 45*x*y*z - 420*y*z^2 + 210*y^2*t -25*x*t + 70*z*t + 126*y*u
  ]
  where [t,u,x,y,z] = vars


mkTC :: (IsMonomialOrder n ord, KnownNat n) => String -> Ideal (OrderedPolynomial (Fraction Integer) ord n) -> Benchmark
mkTC name i =
  env (return i) $ \ideal ->
  bgroup name [ bench "calcGroebnerBasis" $ nf calcGroebnerBasis ideal
              , bench "F5" $ nf f5 ideal
              ]

main :: IO ()
main =

  defaultMainWith defaultConfig
    [ mkTC "default" $ toIdeal i2G
    , mkTC "foldl" $ toIdeal i2FlG
    , mkTC "hand" $ toIdeal i2HWG
    ]

