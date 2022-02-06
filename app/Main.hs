{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module Main where

import Control.Applicative
import Control.Exception (SomeException, handle)
import Control.Lens hiding (setting)
import Control.Monad (guard, (<=<))
import Control.Monad.Error.Class
import Control.Monad.IO.Class
import Control.Monad.Trans.Maybe
import Data.Default
import Data.Foldable
import Data.Maybe
import Data.Monoid
import Data.String (fromString)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Time.Format
import Data.Time.LocalTime
import Hakyll hiding (renderTags)
import Lenses
import Settings
import System.Directory
import System.Exit (ExitCode (..))
import System.FilePath (FilePath, isAbsolute, joinPath, splitDirectories, takeDirectory, (</>))
import System.Process (callProcess, readProcess)
import Text.HTML.TagSoup
import Text.Pandoc hiding (getZonedTime)
import Text.Pandoc.Highlighting (pygments, styleToCss)
import Prelude hiding (FilePath)

default (Text)

algpacks :: [String]
algpacks =
  [ "docs/algebra-*"
  , "docs/algebraic-prelude-*"
  , "docs/computational-algebra-*"
  , "docs/halg-*"
  , "docs/type-natural*"
  , "docs/sized*"
  ]

alghtmls :: Pattern
alghtmls =
  foldr1 (.||.) [fromGlob $ p ++ "/**.html" | p <- algpacks]

algCopies :: Pattern
algCopies =
  foldr1 (.||.) [fromGlob $ p ++ "/**." ++ ext | p <- algpacks, ext <- exts]
  where
    exts = ["css", "js", "gif", "png", "jpg", "svg"]

main :: IO ()
main = hakyllWith conf $ do
  setting "schemes" (def :: Schemes)
  match (alghtmls .||. "docs/index.html" .||. "docs/doc-index.html") $ do
    route idRoute
    compile $
      fmap (fmap T.unpack)
        . haddockExternal
        =<< relativizeUrls
        =<< getResourceString
  match ("katex/**" .&&. complement "**.md") $
    route idRoute >> compile copyFileCompiler
  match "templates/**" $
    compile templateCompiler
  match "params.json" $ do
    route idRoute
    compile copyFileCompiler
  create ["stylesheets/syntax.css"] $ do
    route idRoute
    compile $ makeItem (styleToCss pygments)
  match (algCopies .||. "**.js" .||. "**.css" .||. "**.json") $ do
    route idRoute
    compile copyFileCompiler
  match "index.md" $ do
    route $ setExtension "html"
    compile $
      pandocCompilerWithTransformM
        defaultHakyllReaderOptions
        writerOpts
        procSchemes
        <&> fmap demoteHeaders
        >>= loadAndApplyTemplate "templates/default.html" myCtx
        >>= relativizeUrls
        >>= withItemBody (unixFilter "node" ["javascripts/prerender.js"])
  return ()

myCtx :: Hakyll.Context String
myCtx =
  mconcat
    [ defaultContext
    , field "toc" tocField
    ]

tocField :: Item String -> Compiler String
tocField i = do
  pan <-
    either (throwError . lines . show) return $
      runPure $
        writeHtml5String tocOpts =<< readHtml readerOpts (T.pack $ itemBody i)
  return $ T.unpack pan

readerOpts :: ReaderOptions
readerOpts =
  defaultHakyllReaderOptions
    { readerStandalone = True
    , readerExtensions =
        enableExtension Ext_raw_html pandocExtensions
    }

writerOpts :: WriterOptions
writerOpts =
  defaultHakyllWriterOptions
    { writerHTMLMathMethod = MathJax mathJaxCDN
    , writerTOCDepth = 2
    , writerTableOfContents = True
    , writerExtensions = enableExtension Ext_raw_html pandocExtensions
    , writerHighlightStyle = Just pygments
    }
  where
    mathJaxCDN = "https://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-MML-AM_CHTML"

tocOpts :: WriterOptions
tocOpts =
  writerOpts
    { writerTemplate =
        either (error . show) Just $
          runPure $ compileDefaultTemplate "$toc$"
    , writerTOCDepth = 4
    , writerTableOfContents = True
    , writerSectionDivs = True
    , writerHighlightStyle = Just pygments
    }

excluded :: [String]
excluded = ["app", "sites.cabal", "TAGS", "stack.yaml"]

testIgnore :: String -> Bool
testIgnore fp =
  fp `elem` excluded || ignoreFile def fp

deploy :: Configuration -> IO ExitCode
deploy cnf = handle (const @_ @SomeException $ pure $ ExitFailure 1) $ do
  dest <- makeAbsolute $ destinationDirectory cnf
  createDirectoryIfMissing True dest
  msgZ <- withCurrentDirectory dest $ do
    timeStamp <- formatTime defaultTimeLocale "%c" <$> liftIO getZonedTime
    let msg = "Updated (" ++ timeStamp ++ ")"
        msgOpt = "-m" <> msg
    callProcess "git" ["add", "."]
    callProcess "git" ["commit", "-a", msgOpt, "--edit"]
    callProcess "git" ["push", "-f", "github", "gh-pages"]
    readProcess "git" ["log", "HEAD", "--format=%s", "-n1"] ""
  callProcess "git" ["add", "."]
  callProcess "git" $ ["commit", "-m"] ++ take 1 (lines msgZ)
  callProcess "git" ["push", "github", "gh-pages-devel"]
  return ExitSuccess

conf :: Configuration
conf =
  def
    { deploySite = deploy
    , destinationDirectory = "_site"
    , ignoreFile = testIgnore
    , previewPort = 8898
    }

procSchemes :: Pandoc -> Compiler Pandoc
procSchemes = bottomUpM (procSchemes0 <=< unsafeCompiler . procDoc)

procDoc :: MonadIO m => Inline -> m Inline
procDoc inl
  | Just pth <- T.stripPrefix "doc:" =<< (inl ^? linkUrl) = do
    let (url, frag) = splitFragment pth
        pat =
          foldr1 (.||.) $
            map (fromGlob . (++ ('/' : T.unpack url))) algpacks
        chk fp = pat `matches` fromString fp
    liftIO (listDirectoryRecursiveWhen chk "docs") >>= \case
      Nothing -> return inl
      Just a -> return $ inl & linkUrl .~ (T.pack a <> frag)
procDoc inl = return inl

listDirectoryRecursiveWhen :: (FilePath -> Bool) -> FilePath -> IO (Maybe FilePath)
listDirectoryRecursiveWhen chk = runMaybeT . loop
  where
    loop fp = do
      isDir <- liftIO $ doesDirectoryExist fp
      isFile <- liftIO $ doesFileExist fp
      if isDir
        then do
          chs <- liftIO $ listDirectory fp
          asum $ map (loop . (fp </>)) chs
        else
          if isFile
            then guard (chk fp) >> pure fp
            else empty

procSchemes0 :: Inline -> Compiler Inline
procSchemes0 inl =
  case inl ^? linkUrl of
    Nothing -> return inl
    Just url -> do
      Schemes dic <- loadBody "config/schemes.yml"
      let url' =
            fromMaybe url $
              asum $
                imap
                  ( \k v ->
                      sandwitched (prefix v) (fromMaybe "" $ postfix v)
                        <$> T.stripPrefix (k <> ":") url
                  )
                  dic
      return $ inl & linkUrl .~ url'
  where
    sandwitched s e t = s <> t <> e

walkPath :: FilePath -> FilePath -> T.Text
walkPath par child
  | isAbsolute child = T.pack child
  | otherwise = T.pack $ go (splitDirectories child) (reverse $ splitDirectories par)
  where
    go [] pts = joinPath $ reverse pts
    go ("../" : chs) (r : rs)
      | isDirectory r = go chs rs
      | otherwise = go ("../" : chs) rs
    go ("./" : chs) rs = go chs rs
    go (ch : chs) rs = go chs (ch : rs)

-- (r : rs')
--   | isDirectory r -> go chs (ch : r : rs')
--   | otherwise -> go chs (ch : rs')

isDirectory :: FilePath -> Bool
isDirectory ch = "/" `T.isSuffixOf` T.pack ch

splitFragment :: Text -> (Text, Text)
splitFragment txt =
  case T.breakOnEnd "#" txt of
    (l, r)
      | T.null l -> (l, r)
      | otherwise -> (T.init l, T.cons (T.last l) r)

haddockExternal :: Item FilePath -> Compiler (Item Text)
haddockExternal i = do
  Just fp <- getRoute $ itemIdentifier i
  mapM (fmap renderTags . mapM (rewriter $ T.pack fp) . parseTags . T.pack) i
  where
    rewriter fp t@(TagOpen "a" atts)
      | Just ref <- lookup "href" atts
        , not ("://" `T.isInfixOf` ref)
        , (targ, frag) <- splitFragment ref
        , not $ T.null targ =
        unsafeCompiler $ do
          let targFP = walkPath (takeDirectory $ T.unpack fp) $ T.unpack targ
          let (pkg, rest) = T.breakOn "/" $ fromJust $ T.stripPrefix "docs/" targFP
          known <- doesFileExist $ T.unpack targFP
          if known && foldr1 (.||.) (map fromGlob algpacks) `matches` fromString (T.unpack ("docs/" <> pkg))
            then return t
            else do
              let href =
                    T.concat
                      [ "https://hackage.haskell.org/package/"
                      , pkg
                      , "/docs"
                      , rest
                      , frag
                      ]
              return $
                TagOpen "a" $ ("href", href) : filter ((/= "href") . fst) atts
    rewriter _ t = return t
