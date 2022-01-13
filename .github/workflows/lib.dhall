let GHA =
      https://raw.githubusercontent.com/regadas/github-actions-dhall/master/package.dhall

let Data/List =
      https://raw.githubusercontent.com/dhall-lang/dhall-lang/v21.1.0/Prelude/List/package.dhall

let Data/Bool =
      https://raw.githubusercontent.com/dhall-lang/dhall-lang/v21.1.0/Prelude/Bool/package.dhall

let T =
      https://raw.githubusercontent.com/dhall-lang/dhall-lang/v21.1.0/Prelude/Text/package.dhall

let GHCVersion =
      { Type = { version : Text, allow-failure : Bool }
      , default.allow-failure = False
      }

let ghc = \(ver : Text) -> GHCVersion::{ version = ver }

let ghcHead =
      \(ver : Text) -> GHCVersion::{ version = ver, allow-failure = True }

let CacheSetup = { base-key : Text, key-files : List (List Text), path : Text }

let hashFiles =
      \(files : List Text) ->
        let args = T.concatMapSep "," Text (\(fp : Text) -> "\"${fp}\"") files

        in  "hashFiles(${args})"

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
            , isHead = [ "false" ]
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

in  { GHA
    , GHCVersion
    , makeGhcHeader
    , CacheSetup
    , ghc
    , ghcHead
    , action/cache
    , action/upload
    , action/run
    }
