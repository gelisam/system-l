#!/bin/bash
set -e

clear
idris2 \
  --source-dir src \
  --output-dir build \
  --exec main src/main.idr
