#!/bin/bash
# Build the interval-dump tools (not timing tools; the campaign's timed binaries are not rebuilt).
set -euo pipefail
cd "$(dirname "$0")/../../../.."
B=Dsc/export/c_harness/build; S=Dsc/export/c_harness/interval_dump
cc -O2 -I/opt/homebrew/include $S/pari_dump.c -L/opt/homebrew/lib -lpari-gmp-tls -o $B/pari_dump
clang++ -std=c++20 -O2 -D_MP_GMP -w -I/opt/homebrew/opt/gmp/include -Ithird_party/z3_snapshot_20260612/src \
  -Ithird_party/root_isolators/msolve/src -Ithird_party/root_isolators/libpoly_nosqf/include \
  -I/opt/homebrew/opt/flint/include $S/lib_dump.cpp third_party/z3_snapshot_20260612/build/libz3.a \
  third_party/root_isolators/msolve/src/usolve/.libs/libusolve.a \
  third_party/root_isolators/msolve/src/neogb/.libs/libneogb.a \
  third_party/root_isolators/libpoly_nosqf/build/src/libpoly.a \
  -L/opt/homebrew/opt/gmp/lib -lgmpxx -lgmp -L/opt/homebrew/opt/flint/lib -lflint \
  -L/opt/homebrew/opt/mpfr/lib -lmpfr -o $B/lib_dump
clang++ -std=c++17 -O2 -w -I/opt/homebrew/include $S/cgal_dump.cpp -L/opt/homebrew/lib -lgmpxx -lgmp -lmpfr -o $B/cgal_dump
