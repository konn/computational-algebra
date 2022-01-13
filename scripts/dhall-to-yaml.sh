#!/usr/bin/env bash

if type -P dhall-to-yaml-ng >/dev/null; then
  DHALL_TO_YAML="dhall-to-yaml-ng"
else
  if type -P docker >/dev/null; then
    DHALL_TO_YAML="docker run --rm dhallhaskell/dhall-yaml dhall-to-yaml-ng"
  else
    echo "No dhall-to-yaml-ng or docker found. aborting..."
    exit 1
  fi
fi

YAML_NAME="${1/.dhall/.yml}"
NEW="$("${DHALL_TO_YAML}" --file "$1" --generated-comment)"
if diff <(echo "${NEW}") <(cat "${YAML_NAME}") >/dev/null ; then
  echo "OK"
else
  echo "${NEW}" >"${YAML_NAME}"
fi
