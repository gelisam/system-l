#!/bin/bash
set -e

fswatcher --path toy.idr --path UnionFind.idr --path ExceptT.idr --throttle=300 -- ./compile.sh
