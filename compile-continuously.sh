#!/bin/bash
set -e

./compile.sh "$@"
fswatcher --path src --throttle=300 -- ./compile.sh "$@"
