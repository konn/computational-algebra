{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, NoImplicitPrelude                 #-}
{-# LANGUAGE NoMonomorphismRestriction, ScopedTypeVariables, TemplateHaskell #-}
module Algebra.Algorithms.FGLM where
import           Algebra.Algorithms.ZeroDim
import           Algebra.Internal
import qualified Algebra.Linear                   as M
import           Algebra.Ring.Noetherian
import           Algebra.Ring.Polynomial
import           Algebra.Ring.Polynomial.Quotient
import           Algebra.Scalar
import           Control.Applicative
import           Control.Lens
import           Control.Monad
import           Control.Monad.Loops
import           Control.Monad.Loops
import           Control.Monad.Reader
import           Control.Monad.ST
import qualified Data.Foldable                    as H
import           Data.Function
import qualified Data.Heap                        as H
import           Data.List                        hiding (sum)
import           Data.Maybe
import           Data.Ord
import           Data.STRef
import           Data.Type.Monomorphic
import           Data.Type.Natural                hiding (max, one, zero)
import           Data.Type.Ordinal
import qualified Data.Vector                      as V
import           Data.Vector.Sized                (Vector (..), sLength,
                                                   singleton, toList)
import qualified Data.Vector.Sized                as VS
import           Numeric.Algebra                  hiding ((>))
import           Prelude                          hiding (Num (..), recip, sum,
                                                   (^))
import           Proof.Equational


data FGLMEnv s r ord n = FGLMEnv { _lMap     :: OrderedPolynomial r ord n -> V.Vector r
                                 , _gLex     :: STRef s [OrderedPolynomial r Lex n]
                                 , _bLex     :: STRef s [OrderedPolynomial r ord n]
                                 , _proced   :: STRef s (Maybe (OrderedPolynomial r Lex n))
                                 , _monomial :: STRef s (OrderedMonomial Lex n)
                                 }

makeLenses ''FGLMEnv

type Machine s r ord n = ReaderT (FGLMEnv s r ord n) (ST s)

look :: Getting (STRef s b) (FGLMEnv s r ord n) (STRef s b) -> Machine s r ord n b
look = lift . readSTRef <=< view

(.==) :: (MonadTrans t, MonadReader s (t (ST s1))) => Getting (STRef s1 a) s (STRef s1 a) -> a -> t (ST s1) ()
v .== a = do
  ref <- view v
  lift $ writeSTRef ref a

(%==) :: (MonadTrans t, MonadReader s (t (ST s1))) => Getting (STRef s1 a) s (STRef s1 a) -> (a -> a) -> t (ST s1) ()
v %== f = do
  ref <- view v
  lift $ modifySTRef' ref f


image :: (Functor f, MonadReader (FGLMEnv s r ord n) f) => OrderedPolynomial r ord n -> f (V.Vector r)
image a = views lMap ($ a)

fglm :: (Ord r, SingRep n, Division r, NoetherianRing r, IsMonomialOrder ord)
     => Ideal (OrderedPolynomial r ord (S n))
     -> ([OrderedPolynomial r Lex (S n)], [OrderedPolynomial r Lex (S n)], OrderedMonomial Lex (S n))
fglm ideal = reifyQuotient ideal $ \pxy ->
  let (gs, bs, ms) = fglmMap (\f -> vectorRep $ modIdeal' pxy f)
      Just stds = map (changeOrder Lex . quotRepr) <$> standardMonomials' pxy
  in (gs, map (sum . zipWith (flip (.*.)) stds . V.toList) bs, ms)

fglmMap :: forall k ord n. (Ord k, Field k, IsMonomialOrder ord, IsPolynomial k n)
        => (OrderedPolynomial k ord (S n) -> V.Vector k)
        -- ^ Linear map from polynomial ring.
        -> ([OrderedPolynomial k Lex (S n)], [V.Vector k], OrderedMonomial Lex (S n))
        -- ^ Tuple of Groebner basis w.r.t. lex ordering and basis of the image space.
fglmMap l = runST $ do
  env <- FGLMEnv l <$> newSTRef [] <*> newSTRef [] <*> newSTRef Nothing <*> newSTRef one
  flip runReaderT env $ do
    mainLoop
    whileM_ toContinue $ nextMonomial >> mainLoop
    (,,) <$> look gLex <*> (mapM image =<< look bLex) <*> look monomial

mainLoop :: (Ord r, SingRep n, Division r, NoetherianRing r, IsOrder o)
         => Machine s r o n ()
mainLoop = do
  m <- look monomial
  let f = toPolynomial (one, getMonomial m)
  lx <- image f
  bs <- mapM image =<< look bLex
  let mat  = foldl1 (M.<|>) $ map (M.colVector . fmap WrapField) bs
      cond | null bs   = if V.all (== zero) lx
                         then Just $ V.replicate (length bs) zero
                         else Nothing
           | otherwise = solveLinear mat (fmap WrapField lx)
  case cond of
    Nothing -> bLex %== (f :)
    Just cs -> do
      bps <- look bLex
      let g = changeOrder Lex $ f - sum (zipWith (.*.) (V.toList $ fmap unwrapField cs) bps)
      proced .== Just g
      gLex %== (++ [g])

toContinue :: (Ord r, SingRep n, Division r, NoetherianRing r, IsOrder o)
           => Machine s r o (S n) Bool
toContinue = do
  mans <- look proced
  case mans of
    Nothing -> return True
    Just g -> do
      let xLast = VS.maximum allVars `asTypeOf` g
      return $ not $ leadingMonomial g `isPowerOf` leadingMonomial xLast

nextMonomial :: (Eq r, SingRep n, NoetherianRing r) => Machine s r ord n ()
nextMonomial = do
  m <- look monomial
  gs <- map leadingMonomial <$> look gLex
  let next = fst $ maximumBy (comparing snd)
             [ (OrderedMonomial monom `asTypeOf` m, ordToInt od)
             | od <- [0..]
             , let monom = beta (getMonomial m) od
             , all (not . (`divs` monom)) gs
             ]
  monomial .== next

beta :: forall n. SingRep n => Monomial n -> Ordinal n -> Monomial n
beta (a :- _) OZ     =
  case sing :: SNat n of
    SS n -> case singInstance n of SingInstance -> (a + 1) :- VS.replicate' 0
    _   -> error "bugInGHC!"
beta (a :- as) (OS n) =
  case sing :: SNat n of
    SS k -> case singInstance k of SingInstance -> a :- beta as n
    _ -> error "bugInGHC"

isPowerOf :: Monomial n -> Monomial n -> Bool
n `isPowerOf` m =
  case VS.sFindIndices (> 0) m of
    [ind] -> totalDegree n == VS.sIndex ind n
    _     -> False
