#!/usr/bin/env bash
# crosscheck.sh — Lean の BMS 実装 (BM4) を yaBMS の C 実装と突き合わせる
#
# 使い方:
#   YABMS=/path/to/yaBMS/c/bms scripts/crosscheck.sh
#
# yaBMS: https://github.com/koteitan/yaBMS  (cd c && make で bms を作る)
#
# 種行列から展開を DEPTH 段たどり、各段で
#   - 展開結果 (expand)      が C と一致するか
#   - 比較     (cmp, 展開結果 < 元) が C と一致するか
# を検査する。
set -u
cd "$(dirname "$0")/.."

YABMS=${YABMS:-}
if [ -z "$YABMS" ] || [ ! -x "$YABMS" ]; then
  echo "error: set YABMS to the yaBMS c/bms binary" >&2
  echo "  (build: git clone https://github.com/koteitan/yaBMS && cd yaBMS/c && make)" >&2
  exit 2
fi

( cd lean && lake build bmscli ) >/dev/null 2>&1 || { echo "error: lake build bmscli failed" >&2; exit 2; }
BMSCLI="lean/.lake/build/bin/bmscli"

SEEDS=(
  "(0)(1)(2)"
  "(0,0)(1,1)(2,2)"
  "(0,0)(1,1)(2,0)"
  "(0,0,0)(1,1,1)(2,2,2)"
  "(0,0,0)(1,1,1)(2,1,1)(3,1,0)"
  "(0,0,0)(1,1,1)(2,1,0)(1,1,1)"
  "(0,0,0,0)(1,1,1,1)(2,2,1,0)"
)
DEPTH=${DEPTH:-8}
MAXCOL=${MAXCOL:-40}

cmds=$(mktemp); expected=$(mktemp); actual=$(mktemp)
trap 'rm -f "$cmds" "$expected" "$actual"' EXIT

ncase=0
for seed in "${SEEDS[@]}"; do
  m="$seed"
  n=0
  for _ in $(seq "$DEPTH"); do
    n=$(( (n % 3) + 1 ))          # コピー数 n は 1,2,3 を巡回
    r=$("$YABMS" "${m}[${n}]")
    echo "expand $m $n" >> "$cmds"; echo "$r" >> "$expected"; ncase=$((ncase+1))
    if [ -z "$r" ]; then break; fi
    c=$("$YABMS" -c "$r" "$m")
    echo "cmp $r $m" >> "$cmds"; echo "$c" >> "$expected"; ncase=$((ncase+1))
    cols=${r//[^(]/}
    if [ "${#cols}" -gt "$MAXCOL" ]; then break; fi
    m="$r"
  done
done

"$BMSCLI" < "$cmds" > "$actual"

if diff -u "$expected" "$actual" >/dev/null; then
  echo "crosscheck OK: $ncase cases"
else
  echo "crosscheck FAILED:"
  paste -d'|' "$cmds" "$expected" "$actual" | awk -F'|' '$2 != $3 {print "cmd: "$1"\n  C   : "$2"\n  Lean: "$3}' | head -60
  exit 1
fi
