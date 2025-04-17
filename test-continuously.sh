#!/bin/bash
set -e

./test.sh
fswatcher --path src --throttle=300 -- ./test.sh
