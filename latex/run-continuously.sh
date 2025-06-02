#!/bin/bash
set -e

./run.sh "$@"
fswatcher --throttle 300 \
  --path syntax.tex \
  --path rules.tex \
  --path example-swap.tex \
  --path example-swap-simplified.tex \
  --path example-curry.tex \
  -- ./run.sh "$@"
