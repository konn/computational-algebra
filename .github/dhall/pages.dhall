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

let docGhcVersion = "8.10.7"

let docs-artifact = lib.docs-artifact-for docGhcVersion

let docs-zip = "docs.zip"

in  { name = "Update Documentation"
    , on.workflow_run
      =
      { workflows = [ "Build" ]
      , types = [ "completed" ]
      , branches = [ "master" ]
      }
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
              , name = Some "download artifacts"
              , uses = Some "actions/github-script@v5"
              , `with` = Some
                  ( toMap
                      { script =
                          ''
                          let allArtifacts = await github.rest.actions.listWorkflowRunArtifacts({
                            owner: context.repo.owner,
                            repo: context.repo.repo,
                            run_id: context.payload.workflow_run.id,
                          });
                          let matchArtifact = allArtifacts.data.artifacts.filter((artifact) => {
                            return artifact.name == "${docs-artifact.name}"
                          })[0];
                          let download = await github.rest.actions.downloadArtifact({
                            owner: context.repo.owner,
                            repo: context.repo.repo,
                            artifact_id: matchArtifact.id,
                            archive_format: 'zip',
                          });
                          let fs = require('fs');
                          fs.writeFileSync(`''${process.env.GITHUB_WORKSPACE}/${docs-zip}`, Buffer.from(download.data));
                          ''
                      }
                  )
              }
            , lib.action/run
                { name = "Extract artifacts"
                , run = "unzip ${docs-zip} -d ./docs"
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
