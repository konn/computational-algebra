{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Instances where

import Data.Binary
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Hashable (Hashable)

{- newtype BibTeX = BibTeX {runBibTeX :: [Citeproc.Reference Text]}
  deriving (Show, Typeable)

instance Writable BibTeX where
  write _ _ = return ()
 -}
instance (Eq k, Hashable k, Binary k, Binary v) => Binary (HashMap k v) where
  put = put . HM.toList
  get = HM.fromList <$> get
