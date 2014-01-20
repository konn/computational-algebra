{-# LANGUAGE ConstraintKinds, FlexibleContexts, MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude, TemplateHaskell                       #-}
module Algebra.Algorithms.FGLM (FGLMEnv(..), lMap, gLex, bLex, proced,
                                monomial, look, (.==), (%==), image, Machine(..)) where
import           Algebra.Ring.Polynomial
import           Control.Lens
import           Control.Monad
import           Control.Monad.Reader
import           Control.Monad.ST
import           Data.Function
import           Data.Maybe
import           Data.STRef
import qualified Data.Vector             as V
import           Prelude                 hiding (Num (..), recip, (^))

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

infix 4 .==, %==

image :: (Functor f, MonadReader (FGLMEnv s r ord n) f) => OrderedPolynomial r ord n -> f (V.Vector r)
image a = views lMap ($ a)
