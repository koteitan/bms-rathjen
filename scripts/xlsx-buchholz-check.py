#!/usr/bin/env python3
"""xlsx-buchholz-check.py — 外部スプレッドシートの Buchholz 列を機械で測る。

`scripts/external-check.py` は Rathjen 列 (綴りの正規化まで) を見る。こちらは
**Buchholz 列**を見る。Buchholz 側はこのリポジトリに検証済みの実装があるので、
綴りの比較ではなく**項として**測れる:

  1. 単調性  — 各シート内で隣り合う値が Buchholz 順序で真に増加するか
  2. 標準形  — 各値が `BT.isStd` (naruyoko `isStandardBuchholz` の移植) を満たすか
  3. 突き合わせ — `Trans.Recal.oRB` (BMS→Buchholz) の像と一致するか

3 つとも Lean 側で計算する。この script は xlsx を読んで **Lean ファイルを書く**
だけで、判定はしない。使い方:

    python3 scripts/xlsx-buchholz-check.py --xlsx <path/to/BMS-vs-Rathjens-OCF.xlsx> \
        --out /tmp/xlsxchk.lean
    cd lean && lake env lean /tmp/xlsxchk.lean

出力される Lean ファイルは自分で**陽性対照**を持つ。3 つの検査それぞれに、
必ず引っかかるはずの細工を 1 件ずつ与えて発火させる。これが無いと「違反 0」が
「検査が正しい」なのか「検査が何も見ていない」なのか区別できない (constitutions C0)。

xlsx はリポジトリには取り込まない (資料は外部に置き、`--xlsx` で場所を渡す)。

2026-08-12 (HEAD c26cfd0) に測った結果:
  entries 402 / 単調性違反 0 / 非標準 2 / oRB 不一致 6
  非標準の 2 件はシート「(0,0)(1,1)(2,2)(3,3) まで」の B28 と B35。
  oRB 不一致 6 件のうち 4 件はシート「(0,0)(1,1) まで」の 1 列行列で、
  差はちょうど 1 — `oR = (1+·) ∘ dict ∘ oRB` の (1+·) の分であって誤りではない。
  残る 2 件は上記の非標準セルそのもの。
  シート「まで」の ψ_ω (超限添字) は `BT` が Nat 添字なので測れない。飛ばした件数を
  必ず印字する。黙って落とすと「全部測った」に見えてしまう。
"""
import argparse
import html
import json
import os
import re
import sys
import zipfile


class Bad(Exception):
    """Buchholz 列のセルが読めなかった。"""


# --------------------------------------------------------------------------
# xlsx


def read_xlsx(path):
    """→ {シート番号: [(行番号, A列, B列, C列), ...]}, {シート番号: シート名}"""
    z = zipfile.ZipFile(path)
    ss = z.read("xl/sharedStrings.xml").decode("utf-8")
    strs = [
        html.unescape("".join(re.findall(r"<t[^>]*>(.*?)</t>", si, re.S)))
        for si in re.findall(r"<si>(.*?)</si>", ss, re.S)
    ]
    wb = z.read("xl/workbook.xml").decode("utf-8")
    names = {}
    for i, m in enumerate(re.finditer(r'<sheet [^>]*name="([^"]+)"', wb), start=1):
        names[i] = m.group(1)
    out = {}
    for n in names:
        sh = z.read(f"xl/worksheets/sheet{n}.xml").decode("utf-8")
        rows = []
        for rm in re.finditer(r'<row[^>]*r="(\d+)"[^>]*>(.*?)</row>', sh, re.S):
            cells = {}
            for cm in re.finditer(r'<c r="([A-Z]+)\d+"([^>]*)>(.*?)</c>', rm.group(2), re.S):
                v = re.search(r"<v>(.*?)</v>", cm.group(3), re.S)
                if not v:
                    continue
                val = v.group(1)
                if 't="s"' in cm.group(2):
                    val = strs[int(val)]
                cells[cm.group(1)] = html.unescape(val)
            a = cells.get("A", "")
            if a.startswith("("):
                rows.append((int(rm.group(1)), a, cells.get("B", ""), cells.get("C", "")))
        out[n] = rows
    return out, names


# --------------------------------------------------------------------------
# Buchholz 列 → Lean の `BT` リテラル
#
# 文法:  term := factor ('+' factor)*
#        factor := 'ψ_' 数字+ '(' term ')' | '0' | 'ω'
# 和は右結合 (`BT.toL`/`ofL` の並びに合わせる)。


def parse(s):
    i = 0

    def peek():
        return s[i] if i < len(s) else ""

    def term():
        nonlocal i
        parts = [factor()]
        while peek() == "+":
            i += 1
            parts.append(factor())
        t = parts[-1]
        for p in reversed(parts[:-1]):
            t = f"(.sum {p} {t})"
        return t

    def factor():
        nonlocal i
        if peek() == "0":
            i += 1
            return ".zero"
        if peek() == "ω":                      # Buchholz の ω は ψ_0(ψ_0(0))
            i += 1
            return "(.D 0 (.D 0 .zero))"
        if s.startswith("ψ_", i):
            i += 2
            j = i
            while i < len(s) and s[i].isdigit():
                i += 1
            if j == i:
                raise Bad(f"添字が数字でない (位置 {j}): {s[j:j+3]!r}")
            u = s[j:i]
            if peek() != "(":
                raise Bad(f"( が無い (位置 {i})")
            i += 1
            a = term()
            if peek() != ")":
                raise Bad(f"括弧が閉じていない (位置 {i})")
            i += 1
            return f"(.D {u} {a})"
        raise Bad(f"読めない字 {s[i:i+4]!r} (位置 {i})")

    t = term()
    if i != len(s):
        raise Bad(f"末尾が余った: {s[i:]!r}")
    return t


# --------------------------------------------------------------------------
# 生成される Lean の後半 (判定はすべてここ)

TAIL = r"""
partial def btStr : BT → String
  | .zero => "0"
  | .D u a => "psi_" ++ toString u ++ "(" ++ btStr a ++ ")"
  | .sum a b => btStr a ++ "+" ++ btStr b

/-- 同一シート内で隣り合う値は真に増加していなければならない。 -/
def monoViolations (rs : List Row) : List String :=
  (rs.zip rs.tail).filterMap fun ((n₁, r₁, m₁, t₁), (n₂, r₂, _, t₂)) =>
    if n₁ ≠ n₂ then none
    else if BT.lt t₁ t₂ then none
    else some s!"sheet{n₁} rows {r₁}->{r₂}: NOT < ({m₁})"

/-- どの値も標準形の Buchholz 項でなければならない。 -/
def stdViolations (rs : List Row) : List String :=
  rs.filterMap fun (n, r, m, t) =>
    if BT.isStd t then none else some s!"sheet{n} row {r}: NOT standard ({m})"

/-- このリポジトリ自身の読み取りと一致しなければならない。 -/
def oRBViolations (rs : List Row) : List String :=
  rs.filterMap fun (n, r, m, t) =>
    match BMS.parseMatrix m with
    | none => some s!"sheet{n} row {r}: matrix does not parse ({m})"
    | some mm =>
      match Trans.Recal.oRB mm with
      | none => some s!"sheet{n} row {r}: oRB = none ({m})"
      | some u => if u == t then none
                  else some s!"sheet{n} row {r} ({m}): sheet {btStr t} | oRB {btStr u}"

/-! ### 陽性対照 — 3 つの検査それぞれが、細工した欠陥で必ず発火すること。
    片側だけでは「常に赤を返す検査」と区別が付かないので、無欠陥の行で
    黙ることも同時に確かめる (constitutions C0)。 -/

def ctlGood : Row := (9, 0, "(0,0)(1,1)(2,2)", .D 0 (.D 2 .zero))
def ctlMono : List Row := [(9, 1, "(0,0)", .D 0 (.D 2 .zero)), (9, 2, "(0,0)", .D 0 .zero)]
def ctlStd  : List Row := [(9, 1, "(0,0)", .sum (.D 0 .zero) (.D 2 .zero))]
def ctlORB  : List Row := [(9, 1, "(0,0)(1,1)(2,2)", .D 0 .zero)]

#eval s!"control fires (must be 1 1 1): {(monoViolations ctlMono).length} {(stdViolations ctlStd).length} {(oRBViolations ctlORB).length}"
#eval s!"control quiet (must be 0 0 0): {(monoViolations [ctlGood]).length} {(stdViolations [ctlGood]).length} {(oRBViolations [ctlGood]).length}"

/-! ### 測定 -/

#eval s!"entries: {rows.length}"
#eval s!"monotonicity violations: {(monoViolations rows).length}"
#eval (monoViolations rows)
#eval s!"standard-form violations: {(stdViolations rows).length}"
#eval (stdViolations rows)
#eval s!"oRB disagreements: {(oRBViolations rows).length}"
#eval (oRBViolations rows)
"""


def emit(entries, out):
    with open(out, "w") as f:
        f.write("import BMS\nimport Trans.Recal\n\nopen Trans Trans.Dict\n\n")
        f.write("abbrev Row := Nat × Nat × String × BT\n\n")
        f.write("def rows : List Row := [\n")
        f.write(",\n".join(f'  ({n}, {r}, "{a}", {bt})' for n, r, a, bt in entries))
        f.write("\n]\n")
        f.write(TAIL)


# --------------------------------------------------------------------------
# 自己試験 — 通すべきものを通し、弾くべきものを弾くこと。両側が要る。


def self_test():
    ok = [
        ("0", ".zero"),
        ("ψ_0(0)", "(.D 0 .zero)"),
        ("ψ_0(ψ_2(0))", "(.D 0 (.D 2 .zero))"),
        ("ψ_0(0)+ψ_0(0)", "(.sum (.D 0 .zero) (.D 0 .zero))"),
        ("ψ_0(0)+ψ_0(0)+ψ_0(0)",
         "(.sum (.D 0 .zero) (.sum (.D 0 .zero) (.D 0 .zero)))"),
        ("ω", "(.D 0 (.D 0 .zero))"),
    ]
    # 弾くべきもの。ψ_ω は「読めない」ではなく「この BT では表せない」で弾く —
    # 黙って ψ_0 などに丸めると、測っていない行を測ったことにしてしまう。
    bad = ["ψ_0(0", "ψ_0(0))", "ψ_ω(0)", "ψ_0(0)+", "x", "", "ψ_(0)"]
    fails = 0
    for src, want in ok:
        try:
            got = parse(src)
        except Bad as e:
            print(f"FAIL 受理すべき {src!r}: {e}")
            fails += 1
            continue
        if got != want:
            print(f"FAIL 形 {src!r}: {got} != {want}")
            fails += 1
    for src in bad:
        try:
            parse(src)
        except Bad:
            continue
        print(f"FAIL 弾くべき {src!r}: 通ってしまった")
        fails += 1
    if fails:
        print("xlsx-buchholz-check 自己試験: 上に失敗あり")
        return False
    print(f"xlsx-buchholz-check 自己試験: 受理 {len(ok)}/{len(ok)}、棄却 {len(bad)}/{len(bad)}")
    return True


# --------------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--xlsx", help="BMS-vs-Rathjens-OCF.xlsx の場所 (既定なし)")
    ap.add_argument("--out", default="/tmp/xlsxchk.lean", help="書き出す Lean ファイル")
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()

    if a.self_test:
        return 0 if self_test() else 1
    if not a.xlsx:
        ap.error("--xlsx が要る (資料はリポジトリの外に置くので既定値を持たない)")
    if not os.path.exists(a.xlsx):
        print(f"見つからない: {a.xlsx}", file=sys.stderr)
        return 2
    if not self_test():
        return 1

    sheets, names = read_xlsx(a.xlsx)
    entries, skipped = [], []
    for n in sorted(sheets):
        for r, mat, b, _c in sheets[n]:
            if not b:
                skipped.append((n, r, mat, "B 列が空"))
                continue
            try:
                entries.append((n, r, mat, parse(b)))
            except Bad as e:
                skipped.append((n, r, mat, f"{b}  <-- {e}"))
    emit(entries, a.out)

    print(f"xlsx: {a.xlsx}")
    for n in sorted(sheets):
        print(f"  sheet{n} 「{names[n]}」: {len(sheets[n])} 行")
    print(f"測れる行: {len(entries)}   飛ばした行: {len(skipped)}")
    bykind = {}
    for _n, _r, _m, why in skipped:
        k = "B 列が空" if why == "B 列が空" else ("ψ_ω (超限添字)" if "ψ_ω" in why else "その他")
        bykind[k] = bykind.get(k, 0) + 1
    for k, v in sorted(bykind.items()):
        print(f"    飛ばした内訳: {k} {v} 件")
    print(f"書き出した: {a.out}")
    print(f"次に:  cd lean && lake env lean {a.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
