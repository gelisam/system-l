#!/bin/bash
set -e

fswatcher --path toy.idr --path UnionFind.idr --throttle=300 -- ./compile.sh
