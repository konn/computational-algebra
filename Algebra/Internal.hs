{-# LANGUAGE CPP, DataKinds, FlexibleContexts, FlexibleInstances, GADTs   #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses, PolyKinds, RankNTypes #-}
{-# LANGUAGE StandaloneDeriving, TypeFamilies, TypeOperators              #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Algebra.Internal ( toProxy, module Data.Proxy, WrappedField(..)
                        , withSingI) where
import Algebra.Instances ()
import Algebra.Wrapped
import Data.Proxy
import Data.Singletons
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 708
import Data.Type.Natural (SNat)

withSingI :: SNat a -> t -> t
withSingI n f = case singInstance n of
  SingInstance -> f
#endif

toProxy :: a -> Proxy a
toProxy _ = Proxy

