{-# LANGUAGE CPP, DataKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, PolyKinds, RankNTypes               #-}
{-# LANGUAGE StandaloneDeriving, TypeFamilies, TypeOperators            #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Algebra.Internal ( toProxy, module Data.Proxy, WrappedField(..)
                        , withSingI) where
import Algebra.Instances ()
import Algebra.Wrapped
import Data.Proxy
import Data.Singletons

toProxy :: a -> Proxy a
toProxy _ = Proxy

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 708
withSingI :: S.Sing n -> (S.SingI n => r) -> r
withSingI n f = case singInstance n of
  SingInstance -> f
#endif
