#!/bin/sh
# Generate a Lean 4 game file from a grid on stdin.
#
#   Usage:  scripts/gen.sh < scripts/easy1 > Games/MyGame.lean
#
# The grid is nine lines of nine integers, 0 for an empty cell.
set -e
cd "$(dirname "$0")"
if [ ! -x gen ] || [ gen.cpp -nt gen ]; then
    c++ -O2 -std=c++17 -o gen gen.cpp
fi
./gen
