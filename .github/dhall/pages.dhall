let lib =
      ./lib.dhall
        sha256:91b944152fcbeba7e2303bce839d8685d2feaf7f6decc91a48fe55f34601afaa

let GHA = lib.GHA

let docGhcVersion = "8.10.7"

let pages-artifact = lib.pages-artifact-for docGhcVersion

let pages-zip = "pages.zip"

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
            [ GHA.Step::{
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
                            return artifact.name == "${pages-artifact.name}"
                          })[0];
                          let download = await github.rest.actions.downloadArtifact({
                            owner: context.repo.owner,
                            repo: context.repo.repo,
                            artifact_id: matchArtifact.id,
                            archive_format: 'zip',
                          });
                          let fs = require('fs');
                          fs.writeFileSync(`''${process.env.GITHUB_WORKSPACE}/${pages-zip}`, Buffer.from(download.data));
                          ''
                      }
                  )
              }
            , lib.action/run
                { name = "Extract artifacts"
                , run = "unzip ${pages-zip} -d ./_site"
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
