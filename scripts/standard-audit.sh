#!/bin/sh
# standard-audit.sh — every matrix in the generated table must be a STANDARD
# Bashicu matrix, checked against the reference implementation (yaBMS `bms -s`).
#
# Why this exists: at v0.1.82 the Bachmann-Howard row was found to carry a
# NON-STANDARD matrix, (0,0)(1,1)(2,1)(3,2).  It had passed every check in the
# repository, because none of them asked about standard form.  A non-standard
# matrix is not a notation of the system at all, so any value attached to it is
# meaningless -- the reference implementation's own image for it was a non-standard Buchholz term.
#
# Usage:   scripts/standard-audit.sh [path-to-yaBMS-c-dir]
# Exit 0 if every row is standard, 1 otherwise (suitable for CI).
#
# yaBMS: https://github.com/koteitan/yaBMS  (build with `make` in its c/ dir)

set -e
root=$(cd "$(dirname "$0")/.." && pwd)
table="$root/table/table-r1.md"
bmsdir=${1:-"$HOME/proofs/yaBMS/c"}
bms="$bmsdir/bms"

if [ ! -x "$bms" ]; then
  echo "standard-audit: yaBMS CLI not found at $bms" >&2
  echo "  pass its directory as the first argument, or build it with 'make'" >&2
  exit 2
fi
if [ ! -f "$table" ]; then
  echo "standard-audit: generated table not found at $table" >&2
  exit 2
fi

# The first column of each table row is the matrix, in `(a,b)(c,d)...` form,
# possibly wrapped in a markdown link.  The empty matrix is written (空).
mats=$(grep -oP '^\| \[?`\K\([0-9,()]*\)(?=`)' "$table" || true)
n=0
bad=0
for m in $mats; do
  n=$((n + 1))
  r=$("$bms" -s "$m" 2>&1 | tail -1)
  if [ "$r" != "1" ]; then
    echo "NON-STANDARD: $m  (bms -s => $r)"
    bad=$((bad + 1))
  fi
done

echo "standard-audit: $n rows checked, $bad non-standard"
[ "$bad" -eq 0 ] || exit 1
