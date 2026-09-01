#!/usr/bin/env bash
# PGO training workload for release builds (invoked by release.yml).
#
# Exercises the instrumented `rossi` binary over the in-repo example models
# so the optimized rebuild can consume the collected profile. Measurements
# from 2026-08-22 showed a profile trained on these examples performs within
# a few percent of one trained on the full external model corpus.
#
# Usage: scripts/pgo-train.sh <path-to-instrumented-rossi>
# Must run from the repository root. Individual training commands ignore
# failures on purpose: several examples validate with findings (non-zero
# exit), and the profile data is written either way.
set -eu

BIN="$1"
EX="crates/rossi/examples"
OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT

# Fail fast if the binary is missing or cannot run at all.
"$BIN" --version >/dev/null

for f in "$EX"/*.eventb "$EX"/*.zip "$EX"/*.txt; do
  "$BIN" validate -c "$f" >/dev/null 2>&1 || true
done
"$BIN" validate -c "$EX" >/dev/null 2>&1 || true
"$BIN" validate -c -f json "$EX/base-model.eventb" >/dev/null 2>&1 || true
"$BIN" validate -c -f sarif "$EX/base-model.eventb" >/dev/null 2>&1 || true
"$BIN" validate - <"$EX/base-model.eventb" >/dev/null 2>&1 || true
"$BIN" fmt --check "$EX" >/dev/null 2>&1 || true
"$BIN" fmt --check "$EX/base-model.eventb" >/dev/null 2>&1 || true

"$BIN" build "$EX/base-model.zip" -o "$OUT/base-model.regen.zip" >/dev/null 2>&1 || true
"$BIN" build "$EX/file-system.zip" -o "$OUT/file-system.regen.zip" >/dev/null 2>&1 || true
"$BIN" build "$EX/cars-on-bridge.zip" -o "$OUT/cars-on-bridge.regen.zip" >/dev/null 2>&1 || true

for z in "$EX"/*.zip; do
  "$BIN" prove "$z" >/dev/null 2>&1 || true
  "$BIN" prove --replay "$z" >/dev/null 2>&1 || true
done

"$BIN" import "$EX/cars-on-bridge.zip" -o "$OUT/cars" >/dev/null 2>&1 || true
"$BIN" export "$OUT/cars" -o "$OUT/cars.zip" >/dev/null 2>&1 || true
