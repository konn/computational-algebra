{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Settings where

import Control.Applicative (empty)
import Control.Arrow (first)
import Data.Binary (Binary (..))
import qualified Data.ByteString.Lazy as LBS
import Data.Default (Default (..))
import Data.Either (fromRight)
import Data.Foldable (toList)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.String (fromString)
import qualified Data.Text as T
import Data.Typeable (Typeable)
import Data.Yaml
import qualified Data.Yaml as Y
import GHC.Generics (Generic)
import Hakyll (Rules, cached, compile, getResourceLBS, match)
import Hakyll.Core.Writable (Writable (..))
import Instances ()

data SiteTree = SiteTree
  { title :: T.Text
  , children :: HashMap FilePath SiteTree
  }
  deriving (Show, Eq, Generic, Typeable)

instance Binary SiteTree

instance Writable SiteTree where
  write _ _ = return ()

instance FromJSON SiteTree where
  parseJSON (String txt) = pure $ SiteTree txt HM.empty
  parseJSON (Object dic)
    | [(name, chs)] <- HM.toList dic = SiteTree <$> pure name <*> HM.unions <$> parseJSON chs
  parseJSON _ = empty

instance Default SiteTree where
  def = SiteTree "Computational Algebra in Haskell" HM.empty

walkTree :: [FilePath] -> SiteTree -> [(FilePath, T.Text)]
walkTree [] (SiteTree t _) = [("/", t)]
walkTree (x : xs) (SiteTree t chs) =
  ("/", t) :
  case HM.lookup x chs of
    Nothing -> []
    Just st' -> map (first (("/" <> x) <>)) (walkTree xs st')

data Scheme = Scheme
  { prefix :: T.Text
  , postfix :: Maybe T.Text
  }
  deriving
    ( Typeable
    , Read
    , Show
    , Eq
    , Ord
    , Generic
    )

instance FromJSON Scheme

instance Binary Scheme

instance ToJSON Scheme

instance Writable Scheme where
  write _ _ = return ()

newtype Schemes = Schemes
  { getSchemes :: HashMap T.Text Scheme
  }
  deriving
    ( Typeable
    , Show
    , Eq
    , Generic
    , FromJSON
    , ToJSON
    , Binary
    )

instance Default Schemes where
  def = Schemes HM.empty

instance Writable Schemes where
  write _ _ = return ()

setting ::
  (Writable a, FromJSON a, Binary a, Typeable a) =>
  String ->
  a ->
  Rules ()
setting name d = match (fromString $ "config/" <> name <> ".yml") $
  compile $
    cached name $ do
      fmap (fromRight d . Y.decodeEither' . LBS.toStrict) <$> getResourceLBS

newtype NavBar = NavBar {runNavBar :: [(T.Text, String)]}
  deriving (Typeable, Generic, Binary)

instance Writable NavBar where
  write _ _ = return ()

instance FromJSON NavBar where
  parseJSON (Array vs) = NavBar <$> mapM p (toList vs)
    where
      p (Object d) | [(k, v)] <- HM.toList d = (,) k <$> parseJSON v
      p _ = empty
  parseJSON _ = empty

instance Default NavBar where
  def = NavBar [("Home", "/")]
