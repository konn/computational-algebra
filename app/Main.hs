{-# LANGUAGE ExtendedDefaultRules, FlexibleContexts, OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Main where
import Lenses
import Settings

import           Control.Lens              hiding (setting)
import           Control.Monad.Error.Class
import           Control.Monad.IO.Class
import           Data.Default
import           Data.Foldable
import           Data.Maybe
import           Data.Monoid
import           Data.Text                 (Text)
import qualified Data.Text                 as T
import           Data.Time.Format
import           Data.Time.LocalTime
import           Hakyll                    hiding (renderTags)
import           Shelly
import           System.Exit               (ExitCode (..))
import           Text.HTML.TagSoup
import           Text.Pandoc

default (Text)

algpacks :: [String]
algpacks =
  ["docs/algebra-*"
  , "docs/algebraic-prelude-*"
  , "docs/computational-algebra-*"
  , "docs/halg-*"]

alghtmls :: Pattern
alghtmls =
  foldr1 (.||.) $ [ fromGlob $ p ++ "/**.html" | p <- algpacks]

algCopies :: Pattern
algCopies =
  foldr1 (.||.) $ [ fromGlob $ p ++ "/**." ++ ext | p <- algpacks, ext <- exts]
  where
    exts = ["css", "js", "gif", "png", "jpg", "svg"]

main :: IO ()
main = hakyllWith conf $ do
  setting "schemes" (def :: Schemes)
  match alghtmls $ do
    route idRoute
    compile $
      getResourceString >>= withItemBody (fmap T.unpack . unsafeCompiler . procHaddock . T.pack)
  match ("katex/**" .&&. complement "**.md") $
    route idRoute >> compile copyFileCompiler
  match "templates/**" $
    compile templateCompiler
  match "params.json" $ do
    route idRoute
    compile copyFileCompiler
  match algCopies $ do
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
  pan <- either (throwError . lines . show) return $ readHtml readerOpts $ itemBody i
  return $ writeHtmlString tocOpts pan

readerOpts :: ReaderOptions
readerOpts =
  defaultHakyllReaderOptions { readerStandalone = True
                             , readerParseRaw = True
                             }

writerOpts :: WriterOptions
writerOpts =
  defaultHakyllWriterOptions
  { writerHTMLMathMethod = MathJax mathJaxCDN
  , writerTOCDepth = 2
  , writerTableOfContents  = True
  , writerHtml5 = True
  }
  where
    mathJaxCDN = "https://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-MML-AM_CHTML"

tocOpts :: WriterOptions
tocOpts =
  writerOpts { writerTemplate = Just "$toc$"
             , writerTOCDepth = 4
             , writerTableOfContents  = True
             , writerHtml5 = True
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
  isGit <- test_d ".git"
  timeStamp <- formatTime defaultTimeLocale "%c" <$> liftIO getZonedTime
  let msg = "Updated (" ++ timeStamp ++  ")"
      msgOpt = "-m" <> T.pack msg
  unless isGit $ withTmpDir $ \tdir -> do
    cd tdir
    run_ "git" ["init"]
    run_ "git" ["remote", "add", "origin", "git@github.com:konn/computational-algebra.git"]
    run_ "git" ["fetch", "origin", "gh-pages", "--depth=1"]
    run_ "git" ["checkout", "gh-pages"]
    mv (tdir </> ".git") dest
  cd dest
  run_ "git" ["add", "."]
  run_ "git" ["commit", "-a", msgOpt, "--edit"]
  run_ "git" ["push", "origin", "gh-pages"]
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
procSchemes = bottomUpM procSchemes0

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

procHaddock :: Text -> IO Text
procHaddock  = fmap renderTags . mapM rewriter . parseTags
  where
    rewriter (TagOpen "a" atts)
      | Just ref <- T.stripPrefix "../" =<< lookup "href" atts
      = do let (pkg, rest) = T.breakOn "/" ref
           known <- shelly $ test_e $ "docs" </> pkg
           let href | known = ref
                    | otherwise = T.concat ["https://hackage.haskell.org/package/", pkg
                                           ,"/docs", rest]
           return $ TagOpen "a" $ ("href", href): filter ((/= "href") . fst) atts
    rewriter t = return t


