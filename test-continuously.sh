#!/bin/bash
set -e

fswatcher --path src --throttle=300 -- ./test.sh
