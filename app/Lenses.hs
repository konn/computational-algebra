{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Lenses where

import Control.Lens
import Data.Text (Text)
import Hakyll.Core.Configuration
import Language.Haskell.TH hiding (Inline (..))
import Text.Pandoc.Definition

flip makeLensesWith ''Configuration $
  underscoreFields & lensField .~ \_ _ name -> [TopName $ mkName $ '_' : nameBase name]

newtype MonoidFun a w = MonoidFun {runMonoidArr :: a -> w}
  deriving newtype (Semigroup, Monoid, Functor)

makePrisms ''MonoidFun
makeWrapped ''MonoidFun
makePrisms ''Inline
makePrisms ''Block
makeFields ''Inline
makeFields ''Block

imgOrLink :: Traversal' Inline (Attr, [Inline], Target)
imgOrLink = failing _Link _Image

linkUrl :: Traversal' Inline Text
linkUrl = imgOrLink . _3 . _1
