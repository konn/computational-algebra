{-# LANGUAGE ExtendedDefaultRules, FlexibleContexts, LambdaCase #-}
{-# LANGUAGE OverloadedStrings                                  #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Main where
import Lenses
import Settings

import           Control.Lens              hiding (setting)
import           Control.Monad             ((<=<))
import           Control.Monad.Error.Class
import           Control.Monad.IO.Class
import           Data.Default
import           Data.Foldable
import           Data.Maybe
import           Data.Monoid
import           Data.String               (fromString)
import           Data.Text                 (Text)
import qualified Data.Text                 as T
import           Data.Time.Format
import           Data.Time.LocalTime
import           Filesystem.Path
import qualified Filesystem.Path.CurrentOS as FS
import           Hakyll                    hiding (renderTags)
import           Prelude                   hiding (FilePath)
import           Shelly
import           System.Exit               (ExitCode (..))
import           Text.HTML.TagSoup
import           Text.Pandoc               hiding (getZonedTime)
import           Text.Pandoc.Highlighting  (pygments, styleToCss)

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
  foldr1 (.||.) [ fromGlob $ p ++ "/**.html" | p <- algpacks]

algCopies :: Pattern
algCopies =
  foldr1 (.||.) [ fromGlob $ p ++ "/**." ++ ext | p <- algpacks, ext <- exts]
  where
    exts = ["css", "js", "gif", "png", "jpg", "svg"]

main :: IO ()
main = hakyllWith conf $ do
  setting "schemes" (def :: Schemes)
  match (alghtmls .||. "docs/index.html" .||. "docs/doc-index.html") $ do
    route idRoute
    compile $
      haddockExternal =<< relativizeUrls =<< getResourceString
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
  mconcat [ defaultContext
          , field "toc" tocField
          ]

tocField :: Item String -> Compiler String
tocField i = do
  pan <- either (throwError . lines . show) return $
         runPure $
         writeHtml5String tocOpts =<< readHtml readerOpts (T.pack $ itemBody i)
  return $ T.unpack pan

readerOpts :: ReaderOptions
readerOpts =
  defaultHakyllReaderOptions { readerStandalone = True
                             , readerExtensions =
                               enableExtension Ext_raw_html pandocExtensions
                             }

writerOpts :: WriterOptions
writerOpts =
  defaultHakyllWriterOptions
  { writerHTMLMathMethod = MathJax mathJaxCDN
  , writerTOCDepth = 2
  , writerTableOfContents  = True
  , writerExtensions = enableExtension Ext_raw_html pandocExtensions
  , writerHighlightStyle  = Just pygments
  }
  where
    mathJaxCDN = "https://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-MML-AM_CHTML"

tocOpts :: WriterOptions
tocOpts =
  writerOpts { writerTemplate = Just "$toc$"
             , writerTOCDepth = 4
             , writerTableOfContents  = True
             , writerSectionDivs = True
             , writerHighlightStyle  = Just pygments
             }

excluded :: [String]
excluded = ["app", "sites.cabal", "TAGS", "stack.yaml"]

testIgnore :: String -> Bool
testIgnore fp =
  fp `elem` excluded || ignoreFile def fp

deploy :: Configuration -> IO ExitCode
deploy cnf = shelly $ handleany_sh (const $ return $ ExitFailure 1) $ do
  dest <- canonicalize $ fromText $ T.pack $ destinationDirectory cnf
  mkdir_p dest
  cd dest
  timeStamp <- formatTime defaultTimeLocale "%c" <$> liftIO getZonedTime
  let msg = "Updated (" ++ timeStamp ++  ")"
      msgOpt = "-m" <> T.pack msg
  cd dest
  run_ "git" ["add", "."]
  run_ "git" ["commit", "-a", msgOpt, "--edit"]
  run_ "git" ["push", "-f", "origin", "gh-pages"]
  msgZ <- cmd "git" "log" "HEAD" "--format=%s" "-n1"
  cd ".."
  run_ "git" ["add", "."]
  run_ "git" $ ["commit", "-m"] ++ take 1 (T.lines msgZ)
  run_ "git"   ["push", "origin", "gh-pages-devel"]
  return ExitSuccess

conf :: Configuration
conf = def { deploySite = deploy
           , destinationDirectory = "_site"
           , ignoreFile = testIgnore
           , previewPort = 8898
           }

procSchemes :: Pandoc -> Compiler Pandoc
procSchemes = bottomUpM (procSchemes0 <=< unsafeCompiler . procDoc)

procDoc :: MonadIO m => Inline -> m Inline
procDoc inl
  | Just pth <- T.stripPrefix "doc:" . T.pack =<< (inl ^? linkUrl)
  = shelly $
    let (url, frag) = splitFragment pth
        pat = foldr1 (.||.) $
              map (fromGlob .  (++ ('/':T.unpack url))) algpacks
        chk fp = return $ pat `matches` fromString (FS.encodeString fp)
    in findWhen chk "docs" >>= \case
    [] -> return inl
    (a : _) -> return $ inl & linkUrl .~ (FS.encodeString a ++ T.unpack frag)
procDoc inl = return inl

procSchemes0 :: Inline -> Compiler Inline
procSchemes0 inl =
  case inl ^? linkUrl of
    Nothing -> return inl
    Just url -> do
      Schemes dic <- loadBody "config/schemes.yml"
      let url' = maybe url T.unpack $ asum $
                 imap (\k v -> fmap (sandwitched (prefix v) (fromMaybe "" $ postfix v)) $
                               T.stripPrefix (k <> ":") $ T.pack url)
                 dic
      return $ inl & linkUrl .~ url'
  where
    sandwitched s e t = s <> t <> e

walkPath :: FilePath -> FilePath -> T.Text
walkPath par child
  | absolute child = FS.encode child
  | otherwise = go (splitDirectories child) (reverse $ splitDirectories par)
  where
    go []            pts      = T.concat $ map FS.encode $ reverse pts
    go ("../" : chs) (r : rs)
      |  isDirectory r = go chs rs
      | otherwise = go ("../" : chs) rs
    go ("./" : chs) rs        = go chs rs
    go (ch : chs) rs = go chs (ch : rs)
        -- (r : rs')
        --   | isDirectory r -> go chs (ch : r : rs')
        --   | otherwise -> go chs (ch : rs')

isDirectory :: FilePath -> Bool
isDirectory ch = "/" `T.isSuffixOf` FS.encode ch

splitFragment :: Text -> (Text, Text)
splitFragment txt =
  case T.breakOnEnd "#" txt of
    (l, r) | T.null l -> (l, r)
           | otherwise ->  (T.init l, T.cons (T.last l) r)

haddockExternal :: Item String -> Compiler (Item String)
haddockExternal i = do
  Just fp <- getRoute $ itemIdentifier i
  mapM (fmap (T.unpack . renderTags) . mapM (rewriter $ FS.decodeString fp) . parseTags . T.pack)  i
  where
    rewriter fp t@(TagOpen "a" atts)
      | Just ref <- lookup "href" atts
      , not ("://" `T.isInfixOf` ref)
      , (targ, frag) <- splitFragment ref
      , not $ T.null targ
      = unsafeCompiler $ shelly $ do
        let targFP = walkPath (directory fp) (FS.decode targ)
        let (pkg, rest) = T.breakOn "/" $ fromJust $ T.stripPrefix "docs/" targFP
        known <- test_e $ FS.decode targFP
        if known && foldr1 (.||.) (map fromGlob algpacks) `matches` fromString (T.unpack ("docs/" <> pkg))
          then return t
          else do
          let href = T.concat ["https://hackage.haskell.org/package/", pkg
                              ,"/docs", rest, frag]
          return $
            TagOpen "a" $ ("href", href) : filter ((/= "href") . fst) atts
    rewriter _ t = return t
