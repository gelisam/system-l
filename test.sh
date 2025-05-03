#!/bin/bash
set -e

clear

if [ -f "$1" ]; then
  idris2 \
    --source-dir src \
    --output-dir build \
    --check "$1"
else
  for FILE in $(find src -name '*.idr'); do
    idris2 \
      --source-dir src \
      --output-dir build \
      --check "$FILE"
  done
fi

idris2 \
  --source-dir src \
  --output-dir build \
  -o runtests src/main.idr
./build/runtests
