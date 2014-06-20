{-# LANGUAGE DataKinds, ExistentialQuantification, FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, GADTs, MultiParamTypeClasses        #-}
{-# LANGUAGE NoMonomorphismRestriction, PolyKinds, QuasiQuotes      #-}
{-# LANGUAGE TemplateHaskell, UndecidableInstances                  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-| High-level interface for polynomial operations. -}
module Algebra.Ring.Polynomial.HighLevel where
import           Algebra.Algorithms.Groebner
import           Algebra.Ring.Polynomial     hiding (grevlex, grlex, lex)
import           Control.Lens
import           Control.Monad.Indexed
import           Control.Monad.Indexed.State
import           Data.Default
import           Data.Fixed
import           Data.List
import           Data.Proxy
import           Data.Singletons             (SingI, SingInstance (..),
                                              singInstance)
import           Data.Type.Natural           (Nat (..))
import           Data.Vector.Sized           (Vector (..))
import qualified Data.Vector.Sized           as V
import           Language.Haskell.IndexedDo
import           Numeric.Algebra
import           Numeric.Algebra.Complex
import           Numeric.Decidable.Units
import           Numeric.Decidable.Zero
import           Prelude                     hiding (negate, (*), (+), (-), (/),
                                              (^), (^^))

rational :: Proxy (Fraction Integer)
rational = Proxy

complexified :: Proxy a -> Proxy (Complex (Fraction Integer))
complexified = reproxy

double :: Proxy Double
double = Proxy

float :: Proxy Float
float = Proxy

pico :: Proxy Pico
pico = Proxy

nano :: Proxy Nano
nano = Proxy

unComplexify :: Proxy (Complex k) -> Proxy k
unComplexify _ = Proxy

data RingData k ord n = Ring { _coefficient :: Proxy k
                             , _variables   :: Vector String n
                             , _ordering    :: Proxy ord
                             , _qIdeal      :: Maybe (Ideal (OrderedPolynomial k ord n))
                             }

instance SingI n => Default (RingData k ord n) where
  def = Ring Proxy (V.unsafeFromList' [ "X_" ++ show i |  i <- [1..] ]) Proxy Nothing

class HasName a where
  name :: Proxy a -> String

toProxy :: a -> Proxy a
toProxy _ = Proxy

name' :: HasName a => a -> String
name' = name . toProxy

instance HasName Grevlex where
  name _ = "grevlex"

instance HasName Lex where
  name _ = "lex"

instance HasName Grlex where
  name _ = "grlex"

instance HasName (Fraction Integer) where
  name _ = "QQ"

instance (Ring r, DecidableUnits r, Commutative r) => DecidableUnits (Complex r) where
  recipUnit r =
    case recipUnit (realPart r * realPart r + imagPart r * imagPart r) of
      Nothing -> Nothing
      Just iv -> Just $ Complex (iv * realPart r) (negate $ iv * imagPart r)

instance DecidableZero r => DecidableZero (Complex r) where
  isZero (Complex r im) = isZero r && isZero im

instance HasName k => HasName (Complex k) where
  name cx = name (unComplexify cx) ++ "(i)"

instance ( IsOrder ord, DecidableZero k, DecidableUnits k
         , SingI n, HasName ord, HasName k, Show k) => Show (RingData k ord n) where
  show (Ring field vs ord mideal) = maybe id (\j -> (++ ("/" ++ showIdeal j))) mideal ringS
    where
      ringS = concat [name field, "[", intercalate "," $ V.toList vs , "] (", name ord, ")"]
      vdic = zip [1..] $ V.toList vs :: [(Int, String)]
      showIdeal ideal = concat ["(", intercalate "," $ map (showPolynomialWithVars vdic) $ generators ideal, ")"]

makeLenses ''RingData

data Environment k ord n = Env { _baseRing :: RingData k ord n } deriving (Show)

makeLenses ''Environment

ring :: IxMonadState m
     => RingData k1 ord1 n1
     -> m (Environment k ord n) (Environment k1 ord1 n1) (RingData k1 ord1 n1)
ring r = [ido| do
  imodify $ baseRing .~ r
  ireturn r
  |]

qring :: ( Eq k, DecidableZero k, DecidableUnits k, Division k, SingI n
         , IsMonomialOrder ord, IxMonadState m)
      => Ideal (OrderedPolynomial k ord n) -> m (Environment k ord n) (Environment k ord n) (Environment k ord n)
qring ideal = [ido| do
  imodify ((baseRing.qIdeal) ?~ toIdeal (calcGroebnerBasis ideal))
  iget
 |]

vars :: (DecidableZero k, DecidableUnits k, IsOrder o, IxMonadState m)
     => m (Environment k1 ord (S n)) (Environment k1 ord (S n)) [OrderedPolynomial k o (S n)]
vars = [ido| do
  vs <- igets (_variables . _baseRing)
  let len = V.sLength vs
  ireturn $ case singInstance len of SingInstance -> genVars len
 |]

qq :: Proxy (Fraction Integer)
qq = rational

(^^) :: Unital r => r -> Natural -> r
(^^) = pow

test01 = [ido| do
  qxyz <- ring $ Ring rational ("x" :- "y" :- "z" :- Nil) grevlex Nothing
  [x,y,z] <- vars
  qxyzi <- qring $ toIdeal [x^^2 + 1]
  ireturn $ x ^^ 2
 |]

lex :: Proxy Lex
lex = Proxy

grlex :: Proxy Grlex
grlex = Proxy

grevlex :: Proxy Grevlex
grevlex = Proxy
