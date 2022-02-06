{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Instances (BibTeX (..)) where

import Citeproc hiding (Citation)
import Data.Binary
import Data.Data
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Hashable (Hashable)
import Data.Text (Text)
import Hakyll.Core.Writable

newtype BibTeX = BibTeX {runBibTeX :: [Citeproc.Reference Text]}
  deriving (Show, Typeable)

instance Writable BibTeX where
  write _ _ = return ()

instance (Eq k, Hashable k, Binary k, Binary v) => Binary (HashMap k v) where
  put = put . HM.toList
  get = HM.fromList <$> get
