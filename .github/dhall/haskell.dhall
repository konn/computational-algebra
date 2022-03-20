let lib =
      ./lib.dhall
        sha256:91b944152fcbeba7e2303bce839d8685d2feaf7f6decc91a48fe55f34601afaa

let Data/List =
      https://raw.githubusercontent.com/dhall-lang/dhall-lang/v21.1.0/Prelude/List/package.dhall
        sha256:11081c23436cb9c5fa60d53416e62845071990b43b3c48973cb2f19f5d5adbee

let GHA = lib.GHA

let ghc = lib.ghc

let versions =
      [ (ghc "8.10.7")
        with generate-page = True
      , ghc "9.0.2"
      , lib.ghcHead "9.2.2"
      ]

let ghcHeaders = lib.makeGhcHeader versions

let docsGhcs =
      Data/List.filter
        lib.GHCVersion.Type
        (\(ver : lib.GHCVersion.Type) -> ver.generate-page)
        versions

let test-bins-artifact =
      { name = "test-artifacts-\${{ matrix.ghc }}", path = "test-bins/" }

let global-stack-cache
    : lib.CacheSetup
    = { base-key = "\${{runner.os}}-build-global-stack-\${{matrix.ghc}}"
      , key-files =
        [ [ "'**/package.yaml'", "'**/*.cabal'" ]
        , [ "format('{0}', env.STACK_YAML)" ]
        ]
      , path = "~/.stack"
      }

let local-stack-cache
    : lib.CacheSetup
    = { base-key = "\${{runner.os}}-build-local-stack-\${{matrix.ghc}}"
      , key-files =
        [ [ "'**/package.yaml'", "'**/*.cabal'" ]
        , [ "format('{0}', env.STACK_YAML)" ]
        , [ "'**/*.hs'", "'**/*.lhs'" ]
        ]
      , path = "**/.stack-work"
      }

let docs-artifact = lib.docs-artifact-for "\${{matrix.ghc}}"

let site-bin-artifact = { name = "site-bin-artifact", path = "site-bin" }

let global-site-stack-cache =
      { base-key = "document-global-stack"
      , path = "~/.stack"
      , key-files = [ [ "'package.yaml'", "'**/*.cabal'", "'stack.yaml'" ] ]
      }

let local-site-stack-cache =
      { base-key = "document-local-stack"
      , path = "**/.stack-work"
      , key-files =
        [ [ "'package.yaml'", "'**/*.cabal'", "'stack.yaml'" ]
        , [ "'**/*.hs'" ]
        ]
      }

in  { on =
      { pull_request = {=}
      , push = toMap { branches = [ "master" ] }
      , schedule = [ { cron = "00 13 * * *" } ]
      }
    , name = "Build"
    , jobs.build
      =
            ghcHeaders
        /\  { name = "Build ${lib.current-ghc}"
            , steps =
              [ GHA.steps.actions/checkout
              , lib.action/cache global-stack-cache
              , lib.action/cache local-stack-cache
              , lib.action/run
                  { name = "Build"
                  , run =
                      "stack build --test --no-run-tests --haddock --no-haddock-deps"
                  }
              , lib.action/run
                  { name = "Collect docs"
                  , run =
                      "cp -r \$(stack path --local-doc-root) ${docs-artifact.path}"
                  }
              , lib.action/run
                  { name = "Collect test exes"
                  , run =
                      ''
                      mkdir -p "${test-bins-artifact.path}"
                      stack ide targets 2>&1 | grep :test: | while read i; do
                        PACK=$(echo "$i" | cut -d':' -f1);
                        EXE=$(echo "$i" | cut -d':' -f3);
                        cp "''${PACK}/$(stack path --dist-dir)/build/''${EXE}/''${EXE}" "${test-bins-artifact.path}";
                      done
                      ''
                  }
              , lib.action/upload test-bins-artifact
              , lib.action/upload docs-artifact
              ]
            }
    , jobs.build-site-generator
      = GHA.Job::{
      , name = Some "Build Site Generator"
      , runs-on = GHA.types.RunsOn.`ubuntu-20.04`
      , steps =
        [ GHA.steps.actions/checkout
          with `with` = Some (toMap { ref = "gh-pages-devel" })
        , lib.action/cache global-site-stack-cache
        , lib.action/cache local-site-stack-cache
        , GHA.steps.actions/setup-haskell
            GHA.actions/HaskellSetup::{
            , enable-stack = Some True
            , stack-version = Some "2.7.3"
            , ghc-version = Some "8.10.7"
            }
        , lib.action/run
            { name = "Build static site generator", run = "stack build --fast" }
        , lib.action/run
            { name = "Collect bins"
            , run =
                ''
                mkdir -p "${site-bin-artifact.path}"
                cp "$(stack path --dist-dir)/build/site/site" "${site-bin-artifact.path}"
                ''
            }
        , lib.action/upload site-bin-artifact
        ]
      }
    , jobs.test
      =
            ghcHeaders
        /\  { needs = [ "build" ]
            , name = "Test ${lib.current-ghc}"
            , steps =
              [ GHA.steps.actions/checkout
              , GHA.Step::{
                , uses = Some "actions/download-artifact@v2"
                , id = Some "test-bins"
                , `with` = Some (toMap test-bins-artifact)
                }
              , lib.action/run
                  { name = "Run all tests"
                  , run =
                      let dl-path =
                            "\${{steps.test-bins.outputs.download-path}}"

                      in  ''
                          ls "${dl-path}"
                          stack ide targets 2>&1 | grep :test: | while read i; do
                            TEST_EXE=$(echo "$i" | cut -d':' -f3)
                            echo "Testing: ''${TEST_EXE}"
                            chmod +x "${dl-path}/''${TEST_EXE}"
                            "${dl-path}/''${TEST_EXE}" +RTS -N
                          done
                          ''
                  }
              ]
            }
    , jobs.build-pages
      =
        let site-bin-id = "site-bin"

        let docs-id = "docs"

        in      ( (lib.makeGhcHeader docsGhcs)
                  with container = None Text
                  with env.STACK_YAML = None Text
                )
            /\  { needs = [ "build", "build-site-generator" ]
                , name = "Build GitHub Pages for ${lib.current-ghc}"
                , steps =
                  [ GHA.steps.actions/checkout
                    with `with` = Some (toMap { ref = "gh-pages-devel" })
                  , lib.action/cache
                      { base-key = "\${{runner.os}}-site-${lib.current-ghc}"
                      , key-files =
                        [ [ "'index.md'"
                          , "'stylesheets/**/*'"
                          , "'templates/**/*'"
                          , "'katex/**/*'"
                          , "'javascripts/**/*'"
                          , "'images/**/*'"
                          ]
                        ]
                      , path = "_cache"
                      }
                  , lib.action/run
                      { name = "Installs dependency (node)"
                      , run = "npm install jsdom"
                      }
                  , GHA.Step::{
                    , uses = Some "actions/download-artifact@v2"
                    , id = Some docs-id
                    , `with` = Some (toMap docs-artifact)
                    }
                  , lib.action/run
                      { name = "Place document in correct place"
                      , run =
                          let dl-path =
                                "\${{steps.${docs-id}.outputs.download-path}}"

                          in  ''
                              if [ "${dl-path}" != "$(pwd)/docs" ]; then
                                cp -r ${dl-path} ./docs;
                              fi
                              ''
                      }
                  , GHA.Step::{
                    , uses = Some "actions/download-artifact@v2"
                    , id = Some site-bin-id
                    , name = Some "Download site generator"
                    , `with` = Some (toMap site-bin-artifact)
                    }
                  , lib.action/run
                      { name = "Locate bin"
                      , run =
                          ''
                          cp -r ''${{steps.${site-bin-id}.outputs.download-path}}/site ./
                          chmod +x ./site
                          ''
                      }
                  , lib.action/run
                      { name = "Generate static site", run = "./site build" }
                  , lib.action/upload (lib.pages-artifact-for lib.current-ghc)
                  ]
                }
    }
