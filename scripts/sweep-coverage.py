#!/usr/bin/env python3
"""sweep-coverage.py — 公理掃引が本当に全部を見ているかを検査する。

`lean/scripts/axiom_sweep.lean` は環境を歩くので、**名前を言い当てられずに宣言を
取りこぼすことはない**。しかし **import していないモジュールは環境に無い**ので、
まるごと見えない。これは名前の取りこぼしより静かで、掃引の出力は「3269 件走査、
sorryAx 0」と正常に見える。

実際に起きた (2026-08-12): `Evidence/SqV.lean` はどのモジュールからも import されて
おらず、`lake build` はビルドしていた (lakefile がディレクトリを拾うため) のに、
掃引は一度も見ていなかった。数学の入ったモジュールが丸ごと未測定だった。

この script は `lean/` 以下の全モジュールを、掃引の import 集合から辿れるかで分類する。
辿れないものがあれば exit 1。

    python3 scripts/sweep-coverage.py [--self-test]

**除外していいもの**は `EXEMPT` に理由付きで書く。黙って除外しない — 除外は主張である。
"""
import os
import re
import sys

SWEEP = "lean/scripts/axiom_sweep.lean"

# 掃引の対象外でよいもの。それぞれ理由を書くこと。
EXEMPT = {
    "lakefile": "ビルド定義。宣言を持たない",
    "Main": "gentable の実行ファイル。定理を持たない",
    "Test": "テストの束ねファイル。ライブラリの主張ではない",
}
EXEMPT_PREFIX = {
    "Test.": "テスト。ライブラリの主張ではない",
}


def modules(root="lean"):
    """→ {モジュール名: [import されているモジュール名]}"""
    out = {}
    for dirpath, _dirs, files in os.walk(root):
        if ".lake" in dirpath:
            continue
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dirpath, f)
            rel = os.path.relpath(p, root)
            if rel.startswith("scripts" + os.sep):
                continue
            name = rel[:-5].replace(os.sep, ".")
            src = open(p, encoding="utf-8", errors="replace").read()
            out[name] = re.findall(r"^import\s+([A-Za-z_][\w.]*)", src, re.M)
    return out


def sweep_roots(path=SWEEP):
    src = open(path, encoding="utf-8", errors="replace").read()
    return [m for m in re.findall(r"^import\s+([A-Za-z_][\w.]*)", src, re.M)
            if not m.startswith("Lean")]


def reachable(mods, roots):
    seen, stack = set(), list(roots)
    while stack:
        m = stack.pop()
        if m in seen or m not in mods:
            continue
        seen.add(m)
        stack.extend(mods[m])
    return seen


def exempt(name):
    if name in EXEMPT:
        return EXEMPT[name]
    for pre, why in EXEMPT_PREFIX.items():
        if name.startswith(pre):
            return why
    return None


def run(mods, roots):
    seen = reachable(mods, roots)
    missing, skipped = [], []
    for name in sorted(mods):
        if name in seen:
            continue
        why = exempt(name)
        (skipped if why else missing).append((name, why))
    return seen, missing, skipped


def self_test():
    """両側。届かないものを見つけること、届くものを黙って通すこと。"""
    fails = 0
    good = {"A": ["B"], "B": [], "Main": [], "Test.X": []}
    _s, miss, skip = run(good, ["A"])
    if miss:
        print(f"FAIL 全部届くはずが {miss}")
        fails += 1
    if len(skip) != 2:
        print(f"FAIL 除外は 2 件のはずが {skip}")
        fails += 1

    bad = dict(good, Orphan=[])
    _s, miss, _k = run(bad, ["A"])
    if [m for m, _ in miss] != ["Orphan"]:
        print(f"FAIL 孤立モジュールを検出できていない: {miss}")
        fails += 1

    # 実際に起きた形: 孤児が別の孤児を import していても、根から届かなければ両方漏れる
    bad2 = dict(good, Orphan=["Helper"], Helper=[])
    _s, miss, _k = run(bad2, ["A"])
    if sorted(m for m, _ in miss) != ["Helper", "Orphan"]:
        print(f"FAIL 孤立の連鎖を検出できていない: {miss}")
        fails += 1

    if fails:
        print("sweep-coverage 自己試験: 上に失敗あり")
        return False
    print("sweep-coverage 自己試験: 4/4 (全到達・除外・孤児 1 件・孤児の連鎖)")
    return True


def main():
    if "--self-test" in sys.argv:
        return 0 if self_test() else 1
    if not self_test():
        return 1
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
    os.chdir(root)
    if not os.path.exists(SWEEP):
        print(f"見つからない: {SWEEP}", file=sys.stderr)
        return 2
    mods = modules()
    roots = sweep_roots()
    seen, missing, skipped = run(mods, roots)
    print(f"掃引の根       : {' '.join(roots)}")
    print(f"lean/ のモジュール: {len(mods)}")
    print(f"  到達可能      : {len(seen & set(mods))}")
    print(f"  除外          : {len(skipped)}")
    for name, why in skipped:
        print(f"      {name}  ({why})")
    if missing:
        print(f"  **未測定**    : {len(missing)}")
        for name, _ in missing:
            print(f"      {name}")
        print("\n掃引はこれらを一度も見ていない。ライブラリの根から import するか、"
              "理由を付けて EXEMPT に入れること。")
        return 1
    print("  未測定        : 0")
    return 0


if __name__ == "__main__":
    sys.exit(main())
