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

GITHUB_DIR=".github"
WORKFLOWS="${GITHUB_DIR}/workflows"
DHALLS="${GITHUB_DIR}/dhall"

for BASE in haskell pages build-site-generator; do
  YAML_PATH="${WORKFLOWS}/${BASE}.yml"
  DHALL_PATH="${DHALLS}/${BASE}.dhall"
  NEW="$("${DHALL_TO_YAML}" --file "${DHALL_PATH}" --generated-comment)"
  if diff <(echo "${NEW}") <(cat "${YAML_PATH}") >/dev/null ; then
    echo "${BASE}: OK"
  else
    echo "${NEW}" >"${YAML_PATH}"
  fi
done
