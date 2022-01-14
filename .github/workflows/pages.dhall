let lib = ./lib.dhall

let GHA = lib.GHA

let global-stack-cache =
      { base-key = "document-global-stack"
      , path = "~/.stack"
      , key-files = [ [ "'package.yaml'", "'**/*.cabal'", "'stack.yaml'" ] ]
      }

let local-stack-cache =
      { base-key = "document-local-stack"
      , path = "**/.stack-work"
      , key-files =
        [ [ "'package.yaml'", "'**/*.cabal'", "'stack.yaml'" ]
        , [ "'**/*.hs'" ]
        ]
      }

let download-id = "download-docs"

let docGhcVersion = "8.10.7"

in  GHA.Workflow::{
    , name = "Update Documentation"
    , on = GHA.On::{ push = Some GHA.Push::{ branches = Some [ "master" ] } }
    , jobs = toMap
        { document = GHA.Job::{
          , runs-on = GHA.types.RunsOn.`ubuntu-20.04`
          , name = Some "Generate and Upload Sites"
          , steps =
            [ GHA.steps.actions/checkout
              with `with` = Some (toMap { ref = "gh-pages-devel" })
            , lib.action/cache global-stack-cache
            , lib.action/cache local-stack-cache
            , GHA.steps.actions/setup-haskell
                GHA.actions/HaskellSetup::{
                , enable-stack = Some True
                , stack-version = Some "2.7.3"
                }
            , lib.action/run
                { name = "Build static site generator"
                , run = "stack build --fast"
                }
            , GHA.Step::{
              , uses = Some "actions/download-artifact@v2"
              , id = Some download-id
              , `with` = Some (toMap (lib.docs-artifact-for docGhcVersion))
              }
            , lib.action/run
                { name = "Generate static site"
                , run = "stack exec -- site build"
                }
            , GHA.Step::{
              , name = Some "Deploy GitHub Pages"
              , uses = Some "peaceiris/actions-gh-pages@v3"
              , `with` = Some
                  ( toMap
                      { github_token = "\${{ secrets.GITHUB_TOKEN }}"
                      , publish_dir = "./_site"
                      }
                  )
              }
            ]
          }
        }
    }
