#!/bin/sh
# refimpl-audit.sh — 表の 2 行行列を P進大好きbot 氏のペア数列停止性証明の
# 変換写像 (naruyoko 氏実装、pss2bp CLI) と突き合わせる。
#
# これは「絶対較正」の検査である: 表内部の検査 (E1/E2/E3i) は自己整合な圧縮を
# 原理的に検出できないことが v0.1.41 の較正事故で実証された。2 行領域では本
# スクリプトの出力が値の基準となる。3 行以上には参照実装が存在しないため、
# 意味証明書 (plan/README.md の新ドクトリン) のみが値を保証する。
#
# usage: PSS2BP=~/proofs/pss2bp/pss2bp.js scripts/refimpl-audit.sh
#   (pss2bp: https://github.com/koteitan ラの ローカルツール。CI では実行不可のため
#    出力を table/refimpl-audit-*.txt として commit し、レビュー時に再生成・diff する)
set -e
PSS2BP=${PSS2BP:-$HOME/proofs/pss2bp/pss2bp.js}
cd "$(dirname "$0")/.."
python3 - <<'PYEOF' | node "$PSS2BP"
import re
src = open('lean/Rows/TM.lean').read()
ms = re.findall(r'\{ m := (\[\[.*?\]\]),', src, re.S)
for m in ms:
    cols = re.findall(r'\[(\d+),(\d+)\]', m)
    if cols:
        print(''.join(f'({a},{b})' for a, b in cols))
PYEOF
