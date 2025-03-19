#!/bin/bash
set -e

clear
for FILE in src/*.idr; do
  idris2 \
    --source-dir src \
    --output-dir build \
    --check "$FILE"
done
