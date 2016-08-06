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


deploy :: Configuration -> IO ExitCode
deploy cnf = shelly $ handleany_sh (const $ return $ ExitFailure 1)  $do
  let dest = fromText $ T.pack $ destinationDirectory cnf
  mkdir_p dest
  cd dest
  isGit <- test_d ".git"
  timeStamp <- formatTime defaultTimeLocale "%c" <$> liftIO getZonedTime
  let msg = "Updated (" ++ timeStamp ++  ")"
  if isGit
  then do
    () <- cmd "git" "add" "."
    run_ "git" ["commit", "-a", ("-m\"" <> T.pack msg <> "\"")]
  else do
    () <- cmd "git" "init"
    () <- cmd "git" "add" "."
    () <- cmd "git" "commit" "-mtemporary"
    () <- cmd "git" "branch" "-m" "gh-pages-tmp"
    () <- cmd "git" "remote" "add" "origin" "git@github.com:konn/computational-algebra.git"
    () <- cmd "git" "pull" "origin" "gh-pages" "--depth=1"
    () <- cmd "git" "checkout" "gh-pages"
    run_ "git" ["merge", "--edit", "gh-pages-tmp"]
  return ExitSuccess

conf :: Configuration
conf = def { deploySite = deploy
           , destinationDirectory = "_site"
           }

main :: IO ()
main = hakyllWith conf $ do
  
  return ()
