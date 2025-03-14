#!/bin/bash
set -e

fswatcher --path toy.idr --throttle=300 -- ./compile.sh
