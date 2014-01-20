{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs            #-}
{-# LANGUAGE MultiParamTypeClasses, PolyKinds, RankNTypes, StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies, TypeOperators                                      #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Algebra.Internal ( toProxy, module Data.Proxy, WrappedField(..)
                        ) where
import Algebra.Instances ()
import Algebra.Wrapped
import Data.Proxy

toProxy :: a -> Proxy a
toProxy _ = Proxy
