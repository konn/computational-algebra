{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module HspecSmallCheck where
import           Control.Applicative
import           Data.IORef
import           Test.Hspec.Core
import           Test.SmallCheck
import           Test.SmallCheck.Drivers

property :: Testable IO a => a -> Property IO
property = test

instance Example (Property IO) where
  evaluateExample p c _ = do
    counter <- newIORef 0
    let hook _ = do
          modifyIORef counter succ
          n <- readIORef counter
          paramsReportProgress c (n, 0)
    maybe Success (Fail . ppFailure) <$> smallCheckWithHook (paramsSmallCheckDepth c) hook p
