{-# LANGUAGE ExtendedDefaultRules, OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Main where
import           Data.Default
import           Data.Monoid
import           Data.Text           (Text)
import qualified Data.Text           as T
import           Data.Time.Format
import           Data.Time.LocalTime
import           Hakyll
import           Shelly
import           System.Exit         (ExitCode (..))

default (Text)

main :: IO ()
main = hakyllWith conf $ do
  match "templates/**" $
    compile templateCompiler
  match "params.json" $ do
    route idRoute
    compile copyFileCompiler
  match ("**.css" .||. "**.js" .||. "**.png" .||. "**.jpg" .||. "**.svg" .||. "**.html") $ do
    route idRoute
    compile copyFileCompiler
  match "index.md" $ do
    route $ setExtension "html"
    compile $ do
      pandocCompiler
        >>= return . fmap (demoteHeaders . demoteHeaders)
        >>= loadAndApplyTemplate "templates/default.html" defaultContext
        >>= relativizeUrls
  return ()

excluded :: [String]
excluded = ["src", "sites.cabal", "TAGS", "stack.yaml"]

testIgnore :: String -> Bool
testIgnore fp =
  fp `elem` excluded || ignoreFile def fp

deploy :: Configuration -> IO ExitCode
deploy cnf = shelly $ handleany_sh (const $ return $ ExitFailure 1)  $do
  dest <- canonicalize $ fromText $ T.pack $ destinationDirectory cnf
  mkdir_p dest
  cd dest
  isGit <- test_d ".git"
  timeStamp <- formatTime defaultTimeLocale "%c" <$> liftIO getZonedTime
  let msg = "Updated (" ++ timeStamp ++  ")"
      msgOpt =  ("-m\"" <> T.pack msg <> "\"")
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
  msgZ <- cmd "git" "log" "HEAD~1" "--format=%s"
  run_ "git" ["push", "origin", "gh-pages"]
  cd ".."
  run_ "git" ["add", "."]
  run_ "git" ["commit", "-m", msgZ]
  run_ "git" ["push", "origin", "gh-pages-devel"]
  return ExitSuccess

conf :: Configuration
conf = def { deploySite = deploy
           , destinationDirectory = "_site"
           , ignoreFile = testIgnore
           , previewPort = 8898
           }