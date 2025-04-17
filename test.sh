#!/bin/bash
set -e

clear
for FILE in $(find src -name '*.idr'); do
  idris2 \
    --source-dir src \
    --output-dir build \
    --check "$FILE"
done

idris2 \
  --source-dir src \
  --output-dir build \
  -o runtests src/main.idr
./build/runtests
