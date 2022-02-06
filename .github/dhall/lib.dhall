let GHA =
      https://raw.githubusercontent.com/regadas/github-actions-dhall/master/package.dhall
        sha256:53da2310a2e009556455a73684b997c3bd53192637ac3c77562c30e3815f5f23

let Data/List =
      https://raw.githubusercontent.com/dhall-lang/dhall-lang/v21.1.0/Prelude/List/package.dhall
        sha256:11081c23436cb9c5fa60d53416e62845071990b43b3c48973cb2f19f5d5adbee

let Data/Bool =
      https://raw.githubusercontent.com/dhall-lang/dhall-lang/v21.1.0/Prelude/Bool/package.dhall
        sha256:7ee950e7c2142be5923f76d00263e536b71d96cb9c190d7743c1679501ddeb0a

let T =
      https://raw.githubusercontent.com/dhall-lang/dhall-lang/v21.1.0/Prelude/Text/package.dhall
        sha256:79b671a70ac459b799a53bbb8a383cc8b81b40421745c54bf0fb1143168cbd6f

let GHCVersion =
      { Type = { version : Text, allow-failure : Bool, generate-page : Bool }
      , default.allow-failure = False
      , default.generate-page = False
      }

let ghc = \(ver : Text) -> GHCVersion::{ version = ver }

let ghcHead =
      \(ver : Text) -> GHCVersion::{ version = ver, allow-failure = True }

let CacheSetup = { base-key : Text, key-files : List (List Text), path : Text }

let hashFiles =
      \(files : List Text) ->
        let args = T.concatSep "," files in "\${{ hashFiles(${args}) }}"

let cache-components =
      \(cfg : CacheSetup) ->
          [ cfg.base-key ]
        # Data/List.map (List Text) Text hashFiles cfg.key-files

let init =
      \(a : Type) ->
      \(comps : List a) ->
        Data/List.reverse a (Data/List.drop 1 a (Data/List.reverse a comps))

let action/cache =
      \(cfg : CacheSetup) ->
        let key-comps = cache-components cfg

        let restores =
              Data/List.drop
                1
                Text
                ( Data/List.map
                    (List Text)
                    Text
                    (\(t : List Text) -> T.concatSep "-" t ++ "-")
                    ( Data/List.iterate
                        (Data/List.length Text key-comps)
                        (List Text)
                        (init Text)
                        key-comps
                    )
                )

        in  GHA.Step::{
            , name = Some "Cache ${cfg.path}"
            , uses = Some "actions/cache@v2"
            , `with` = Some
                ( toMap
                    { path = cfg.path
                    , key = T.concatSep "-" key-comps
                    , restore-keys = T.concatSep "\n" restores
                    }
                )
            }

let makeGhcHeader =
      \(versions : List GHCVersion.Type) ->
        { continue-on-error = "\${{matrix.isHead}}"
        , env.STACK_YAML = "stack-\${{matrix.ghc}}.yaml"
        , container = "ghcr.io/konn/computational-algebra/gha:0.7"
        , runs-on = "ubuntu-latest"
        , strategy =
          { matrix =
            { ghc =
                Data/List.map
                  GHCVersion.Type
                  Text
                  (\(ghc : GHCVersion.Type) -> ghc.version)
                  ( Data/List.filter
                      GHCVersion.Type
                      (\(x : GHCVersion.Type) -> Data/Bool.not x.allow-failure)
                      versions
                  )
            , isHead = [ False ]
            , include =
                Data/List.map
                  GHCVersion.Type
                  { ghc : Text, isHead : Bool }
                  ( \(ghc : GHCVersion.Type) ->
                      { ghc = ghc.version, isHead = True }
                  )
                  ( Data/List.filter
                      GHCVersion.Type
                      (\(ghc : GHCVersion.Type) -> ghc.allow-failure)
                      versions
                  )
            }
          , fail-fast = False
          }
        }

let action/upload =
      \(cfg : { path : Text, name : Text }) ->
        GHA.Step::{
        , uses = Some "actions/upload-artifact@v2.2.3"
        , name = Some "Upload ${cfg.name}"
        , `with` = Some (toMap cfg)
        }

let action/run =
      \(cfg : { name : Text, run : Text }) ->
        GHA.Step::{ name = Some cfg.name, run = Some cfg.run }

let docs-artifact-for =
      \(ver : Text) -> { name = "doc-artifacts-${ver}", path = "docs/" }

let pages-artifact-for =
      \(ver : Text) -> { name = "pages-artifacts-${ver}", path = "_site/" }

let current-ghc = "\${{matrix.ghc}}"

in  { GHA
    , GHCVersion
    , makeGhcHeader
    , CacheSetup
    , ghc
    , ghcHead
    , action/cache
    , action/upload
    , action/run
    , docs-artifact-for
    , pages-artifact-for
    , current-ghc
    }
