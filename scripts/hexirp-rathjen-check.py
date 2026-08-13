#!/usr/bin/env python3
"""Hexirp 氏の BMS4↔OCF 対応表と、このリポジトリの `Trans.oR` を突き合わせる。

**なぜあるか。** 表の値のうち、単一の翻訳 `oR` からしか来ていないものを、外部の独立な
資料と突き合わせるため。2026-08-13 にこの突き合わせを一度その場限りのスクリプトで行い、
**辞書を誤って表の 3 行を「誤り」と報告した** (`lean/Evidence/SqV.lean` §K3.20 で撤回)。
正しい辞書では 17 行中 17 行が一致する。書き捨てた道具は毎回同じ穴を作る
(plan/constitutions.md C8) ので、辞書ごとここに固定する。

**資料はリポジトリに入れない。** CC BY-SA 3.0 であり、出典が正でローカルの控えは複製に
すぎない。ディレクトリを渡して読む。無ければ理由を表示して飛ばす。

  Hexirp「バシク行列システム４と全部盛りオクフ・ベータの対応」
      <https://googology.fandom.com/ja/wiki/ユーザー:Hexirp/執筆した記事の一覧> から辿る
      高さ 2 が 2272 行、高さ 3 が 2627 行。ライセンス CC BY-SA 3.0 (Fandom)。

      **行き先は Rathjen の 𝔗(M) ではなく「全部盛り」の OCF である。** 題名がそう言って
      いる。だから `W(x)` が訳せないのは翻訳の穴ではなく**系の違い**で、先方の側に
      Ω 階層があり 𝔗(M) には無い、というだけのことである。当方が突き合わせているのは
      両者が重なる Veblen 断片に限られる。
      (ローカルの控えの `<title>` は「バシク行列システムとRathjenの弱マーロのpsiの対応」
      という別の題名を持つ。古い版か作業用の題名と思われる。正は上の題名。)

  python3 scripts/hexirp-rathjen-check.py --papers <資料を置いたディレクトリ> --out /tmp/hx.lean
  cd lean && leanman check -C $PWD --backend lean /tmp/hx.lean
  python3 scripts/hexirp-rathjen-check.py --self-test

**辞書。** 先方と当方は記法が違う。10 例を手で確かめて決めた対応は

    先方 phi(a,b) = 当方 phiNF(1+a, b)     先方 w(x) = 当方 phiNF(0, 1+x)   (w(0) = ω)
    先方 W(0)    = 当方 Z 0 = Ω            psi・+・0 は字面どおり
    先方 W(x), x≠0                          **訳せない** (下記)

**`phiNF` であって `phi` ではない。** 当方の φ̄ は不動点を飛ばし、先方の φ は飛ばさない。
先方の φ(0,ε₀+1) と当方の φ̄(0,ε₀) は**同じもの**である (`phiNF 0 (ε₀+1) = φ̄(0,ε₀)`)。
生の `phi` で組むと差が全部「食い違い」に化ける。

**`W(x)` は `x = 0` のときしか訳せない。** 先方の `W(k)` は $Ω_{1+k}$ だが、
$Ω_2 = χ_0(1)$ は 𝔗(M) に項を持たない ([R91] §2 が χ を α ↦ χ_α(0) に潰しているため。
`plan/chi-2ary.md`)。当方の `Z 1` は χ_1(0) = I で別の順序数なので、`Z (tr x)` と訳すと
黙って誤った項を作る。2026-08-13 まで実際そうしていた。今は例外にして数に出す。

だから **`--veblen-only` を既定にし、
両辺が `CNV` の行だけを数える**。断片の外は辞書が未検証で、そこの不一致は食い違いでは
なく「比較していない」である。この区別を落とさないために、出力は必ず両方を印字する。

**`NfOK` を辞書の傍証に使ってはならない。** `NfOK` は基本列の組み立て定理の側条件であって
正規形の述語ではない。2026-08-13 の誤報はこれを取り違えたことから出た。辞書の傍証は
「当方の表と一致するか」であり、`--out` の出力の最後の 2 行がそれである。

**測定 (2026-08-13、高さ 2 の 1249 行)。**

    Veblen 断片 390 行     oR 一致 379、食い違い 11
    断片の外 859 行        辞書が未検証なので数えない
    当方の表 41 行         一致 20、食い違い 21

**表側の 21 は `(0,0)(1,1)(2,2)` から始まり、既知の `dict` の Ω₂ 問題である**
(`lean/Trans/Dict.lean` §5)。当方は ψ_{Z0}(Z1)、先方は ψ_{Z0}(φ̄(1,Ω))。一致数 20/41 は
§5 が「`reg` を `Z 1` にした場合」として記録した数と同じで、新しい情報ではない。

**断片内の 11 のうち 2 件は先方の誤りで、それは先方の表だけで決まる。** 一致率では
どちらが正しいかは決まらないので、BMS の順序で並べ直して隣接対の狭義単調性を両側に
当てる (下の `sorted`/`adj`)。結果:

    先方が単調でない対 2      oR が単調でない対 0
    先方が潰す対       2      oR が潰す対       0
    相異なる値  先方 388 / 390、oR 390 / 390     対照 (逆向き) 389/389 で総崩れ

つまり先方は隣り合う 2 対に同じ項を与えている。正しい表記の写像は単射なので、そこは
先方の誤りである。**残り 9 件は未決** — 双方とも単調かつ単射で、一致率も内部整合性も
これ以上は分けない。展開と基本列で当てる試験も書いたが 0/0 で分かれなかった。これは
E3 の添字が行ごとに違うという既知の事実 (`fsN` に一律のずらしを当てるな) の現れであって、
どちらかの証拠ではない。
"""
import argparse
import html
import os
import re
import sys

CANON = "https://googology.fandom.com/ja/wiki/ユーザー:Hexirp/執筆した記事の一覧"


# --- 先方の項の構文解析 -----------------------------------------------------

def parse_term(s):
    """`phi(0,w(0))+1` のような文字列を木にする。数は ('n', k)、和は ('+', [..])。"""
    s = s.replace(" ", "")
    pos = 0

    def peek():
        return s[pos] if pos < len(s) else ""

    def term():
        nonlocal pos
        parts = [atom()]
        while peek() == "+":
            pos += 1
            parts.append(atom())
        return parts[0] if len(parts) == 1 else ("+", parts)

    def atom():
        nonlocal pos
        m = re.match(r"(psi|phi|w|W)\(", s[pos:])
        if m:
            f = m.group(1)
            pos += len(f) + 1
            args = [term()]
            while peek() == ",":
                pos += 1
                args.append(term())
            if peek() != ")":
                raise ValueError(f"閉じ括弧が無い: {s}")
            pos += 1
            return (f, args)
        m = re.match(r"\d+", s[pos:])
        if m:
            pos += len(m.group(0))
            return ("n", int(m.group(0)))
        raise ValueError(f"読めない: {s} @{pos}")

    t = term()
    if pos != len(s):
        raise ValueError(f"末尾が余る: {s} @{pos}")
    return t


def finite(t):
    """有限の値なら整数、そうでなければ None。`1+x` の吸収の判定に要る。"""
    if t[0] == "n":
        return t[1]
    if t[0] == "+":
        v = 0
        for p in t[1]:
            f = finite(p)
            if f is None:
                return None
            v += f
        return v
    return None


def one_plus(t):
    """`1+t`。有限なら数え上げ、先頭の加算成分が無限ならそのまま。"""
    f = finite(t)
    if f is not None:
        return ("n", f + 1)
    if t[0] == "+":
        return ("+", [one_plus(t[1][0])] + t[1][1:])
    return t


def to_lean(t):
    """当方の `TM.Term` の式に変換する。辞書はモジュール先頭の docstring のとおり。"""
    if t[0] == "n":
        return "TM.Term.zero" if t[1] == 0 else f"(TM.Term.ofNat {t[1]})"
    if t[0] == "+":
        r = to_lean(t[1][-1])
        for p in reversed(t[1][:-1]):
            r = f"(TM.Term.add {to_lean(p)} {r})"
        return r
    f, a = t
    # `phiNF` であって `phi` ではない。**ここが辞書の要**である。
    # 当方の φ̄ は [R91] 2.6(vi) の「不動点を数え直す」版で、不動点を飛ばす。先方の φ は
    # 飛ばさない。だから先方の φ(0,ε₀+1) と当方の φ̄(0,ε₀) は同じものである。橋渡しは
    # リポジトリ自身の `phiNF` がやってくれる: `phiNF 0 (ε₀+1) = φ̄(0,ε₀)`。
    # 生の `phi` で組むと、この差が全部「食い違い」に化ける。2026-08-13 に一度そうして
    # 表の 3 行を誤って「誤り」と報告した。`scripts/external-check.py` の冒頭に同じ罠が
    # 書いてあり (97/98 の誤検出)、読まずに踏んだ。
    if f == "w":
        return f"(TM.Term.phiNF TM.Term.zero {to_lean(one_plus(a[0]))})"
    if f == "phi":
        return f"(TM.Term.phiNF {to_lean(one_plus(a[0]))} {to_lean(a[1])})"
    if f == "psi":
        return f"(TM.Term.psi {to_lean(a[0])} {to_lean(a[1])})"
    if f == "W":
        # **W(x) は x = 0 のときしか訳せない。** 先方の W(k) は Ω_{1+k} で、
        # Ω₂ = χ_0(1) は 𝔗(M) に無い ([R91] §2 は χ を α ↦ χ_α(0) に潰している。
        # plan/chi-2ary.md)。当方の `Z 1` は χ_1(0) = I であって Ω₂ ではないので、
        # `Z (tr x)` と訳すと**別の順序数を黙って作る**。訳せないものは訳さない。
        if a[0] == ("n", 0):
            return "(TM.Term.Z TM.Term.zero)"
        raise ValueError("W(x) with x != 0 has no 𝔗(M) term (Omega_2 is not expressible)")
    raise ValueError(f"知らない関数記号: {f}")


def to_matrix(ms):
    cols = re.findall(r"\((\d+(?:,\d+)*)\)", ms)
    return "[" + ", ".join("[" + c + "]" for c in cols) + "]", len(cols[0].split(","))


# --- 資料の読み取り ---------------------------------------------------------

def read_pairs(path):
    """`(0,0)(1,1) = phi(0,0)` の行を拾う。壊れた行は数えて報告する。"""
    src = open(path, encoding="utf-8", errors="replace").read()
    ok, bad = [], 0
    for line in re.split(r"<br>", src):
        line = html.unescape(re.sub(r"<[^>]+>", "", line)).strip()
        for m in re.finditer(r"((?:\(\d+(?:,\d+)*\))+)\s*=\s*(.+)$", line):
            try:
                mat, h = to_matrix(m.group(1))
                ok.append((h, mat, to_lean(parse_term(m.group(2).strip())), m.group(2).strip()))
            except Exception:
                bad += 1
    return ok, bad


# --- Lean の出力 ------------------------------------------------------------

HEAD = """-- 生成物: scripts/hexirp-rathjen-check.py
-- 出典: Hexirp「バシク行列システム４と全部盛りオクフ・ベータの対応」CC BY-SA 3.0
--   {url}
-- 資料そのものはリポジトリに入れない。ここにあるのは当方の記法へ翻訳した対だけである。
import Rows.TM
import Evidence.SqV
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
namespace HexirpCheck
"""

TAIL = """
def rows : List (BMS.Matrix × TM.Term) := {chunks}

#eval s!"行 {{rows.length}}"

-- 辞書が検証済みの断片だけを数える (docstring 参照)。外側は「比較していない」。
def vebl : List (BMS.Matrix × TM.Term) := rows.filter fun p => Evidence.WF.CNV p.2
#eval s!"Veblen 断片 {{vebl.length}} 行:  oR 一致 {{vebl.countP fun p => Trans.oR p.1 == some p.2}}"
#eval s!"断片の外 {{rows.length - vebl.length}} 行: 辞書が未検証なので数えない"

-- 陽性対照: 目標を歪めれば一致は消えなければならない。
#eval s!"対照 目標を t+t に歪める: {{vebl.countP fun p => Trans.oR p.1 == some (TM.Term.add p.2 p.2)}}"
-- 陰性対照: 一つの行列を全部の目標に当てても当たってはならない。
#eval s!"対照 固定した行列を全目標に: {{vebl.countP fun p => Trans.oR [[9,9]] == some p.2}}"

/-! ## 食い違いを裁く道具: 単調性と単射性

食い違ったとき「どちらが正しいか」は一致率では決まらない。**BMS の順序で並べ直し、
隣接対で狭義単調かを両側について見る。** 正しい BMS → 順序数 の写像は単調な単射だから、
自分の順序と矛盾する側が誤っている。隣接対で足りるのは 𝔗(M) の順序が推移的だからである。

`NfOK` は使わない。あれは基本列の組み立て定理の側条件であって正規形の述語ではなく、
2026-08-13 の誤報 (`Evidence/SqV.lean` §K3.20) はそれを取り違えたことから出た。 -/

def sorted : List (BMS.Matrix × TM.Term) :=
  vebl.mergeSort (fun p q => BMS.cmpM p.1 q.1 != Ordering.gt)
def adj : List ((BMS.Matrix × TM.Term) × (BMS.Matrix × TM.Term)) :=
  (sorted.zip sorted.tail).filter fun c => BMS.cmpM c.1.1 c.2.1 == Ordering.lt

#eval s!"隣接対 {{adj.length}}"
#eval s!"  先方が単調でない対 {{adj.countP fun c => !(TM.Term.lt c.1.2 c.2.2)}}" ++
      s!"   oR が単調でない対 {{adj.countP fun c => match Trans.oR c.1.1, Trans.oR c.2.1 with
        | some u, some v => !(TM.Term.lt u v) | _, _ => true}}"
#eval s!"  先方が潰す対 {{adj.countP fun c => c.1.2 == c.2.2}}" ++
      s!"   oR が潰す対 {{adj.countP fun c => Trans.oR c.1.1 == Trans.oR c.2.1}}"
#eval s!"  相異なる値: 先方 {{(vebl.map (·.2)).eraseDups.length}}" ++
      s!"   oR {{(vebl.filterMap fun p => Trans.oR p.1).eraseDups.length}}   (行数 {{vebl.length}})"
-- CTRL 並べ替えが効いていること: 逆向きに見れば総崩れになる
#eval s!"対照 逆向きに見た先方: {{adj.countP fun c => !(TM.Term.lt c.2.2 c.1.2)}} / {{adj.length}}"
#eval (adj.filter fun c => !(TM.Term.lt c.1.2 c.2.2)).map fun c =>
  (c.1.1, c.1.2.toStr, c.2.1, c.2.2.toStr, (Trans.oR c.2.1).map (·.toStr))

-- 当方の表との突き合わせ。辞書が訳せなかった行は先方の側に無いので、ここに来た行は
-- すべて W(0) しか使っていない = 辞書が検証済みの範囲である。CNV で絞る必要はもう無い。
def ours : List (BMS.Matrix × TM.Term) := Rows.rows.map fun r => (r.m, r.t)
def cmp : List (BMS.Matrix × TM.Term × TM.Term) := ours.filterMap fun p =>
  match rows.find? fun q => q.1 == p.1 with
  | some q => some (p.1, p.2, q.2)
  | none => none
#eval s!"当方の表 {{ours.length}} 行中、断片内で比較できるもの {{cmp.length}}"
#eval s!"  一致 {{cmp.countP fun c => c.2.1 == c.2.2}}   食い違い {{cmp.countP fun c => !(c.2.1 == c.2.2)}}"
#eval (cmp.filter fun c => !(c.2.1 == c.2.2)).map fun c => (c.1, c.2.1.toStr, c.2.2.toStr)

end HexirpCheck
"""


def emit(rows, out, height):
    sel = [r for r in rows if r[0] == height]
    if not sel:
        raise SystemExit(f"高さ {height} の行が無い")
    body, names = [], []
    for i in range(0, len(sel), 150):
        names.append(f"c{i}")
        body.append(f"def c{i} : List (BMS.Matrix × TM.Term) := [")
        body.append(",\n".join(f"  ({m}, {t})" for _, m, t, _ in sel[i:i + 150]))
        body.append("]")
    with open(out, "w", encoding="utf-8") as f:
        f.write(HEAD.format(url=CANON))
        f.write("\n".join(body))
        f.write(TAIL.format(chunks=" ++ ".join(names)))
    return len(sel)


# --- 自己試験 (constitution C0) --------------------------------------------

def self_test():
    """捕まえるはずのものを与えて発火させ、正常な対照で沈黙させる。
    片側だけでは、常に「一致」と言う検査器と区別がつかない。"""
    fails = []

    # 1. 辞書の要: phi は 1 ずらし、w は ω 始まり。ここを間違えると全部ずれる。
    if to_lean(parse_term("phi(0,0)")) != "(TM.Term.phiNF (TM.Term.ofNat 1) TM.Term.zero)":
        fails.append("phi(0,0) の 1 ずらしが効いていない")
    if to_lean(parse_term("w(0)")) != "(TM.Term.phiNF TM.Term.zero (TM.Term.ofNat 1))":
        fails.append("w(0) が ω になっていない")
    # 不動点飛ばしの橋渡し: 生の phi で組んでいたら、ここが phi のまま残る
    if "TM.Term.phi " in to_lean(parse_term("phi(0,phi(0,0)+1)")):
        fails.append("phiNF ではなく生の phi で組んでいる (不動点飛ばしを潰す)")
    # 2. 1+x の吸収: 先頭が無限なら増えない、有限なら増える。
    if finite(parse_term("1+1+1")) != 3:
        fails.append("有限判定が壊れている")
    if finite(parse_term("w(0)")) is not None:
        fails.append("w(0) を有限と判定した")
    if to_lean(one_plus(parse_term("phi(0,0)+1"))) != to_lean(parse_term("phi(0,0)+1")):
        fails.append("先頭が無限なのに 1+ が吸収されなかった")
    if to_lean(one_plus(parse_term("1+1"))) != to_lean(parse_term("3")):
        fails.append("有限の 1+ が数え上げられていない")
    # 3. 行列の読み取りと高さ
    m, h = to_matrix("(0,0)(1,1)(2,1)")
    if m != "[[0,0], [1,1], [2,1]]" or h != 2:
        fails.append(f"行列の読み取り: {m} 高さ {h}")
    m, h = to_matrix("(0,0,0)(1,1,1)")
    if h != 3:
        fails.append("高さ 3 を 3 と読めていない")
    # 4. 壊れた行は黙って落とさず、数に出る
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".html", delete=False, encoding="utf-8") as f:
        f.write("(0,0)(1,1) = phi(0,0)<br>(0,0)(1,0) = zzz(<br>")
        p = f.name
    ok, bad = read_pairs(p)
    os.unlink(p)
    if len(ok) != 1 or bad != 1:
        fails.append(f"壊れた行の計上: ok={len(ok)} bad={bad} (1 と 1 のはず)")
    # 5. W(0) は訳せ、W(x≠0) は拒否されること。ここが緩むと Ω₂ が I に化ける
    if to_lean(parse_term("W(0)")) != "(TM.Term.Z TM.Term.zero)":
        fails.append("W(0) が Z 0 になっていない")
    try:
        to_lean(parse_term("W(1)"))
        fails.append("W(1) を訳してしまった (Omega_2 は 𝔗(M) に無い)")
    except ValueError:
        pass
    # 6. 対照: 知らない記号は例外になる (黙って通さない)
    try:
        to_lean(parse_term("Q(0)"))
        fails.append("知らない記号 Q が素通りした")
    except Exception:
        pass

    for f in fails:
        print("  失敗:", f)
    print(f"hexirp-rathjen-check 自己試験: 失敗 {len(set(fails))}" if fails
          else "hexirp-rathjen-check 自己試験: 6/6 (辞書・吸収・行列・壊れた行・W の拒否・未知記号)")
    return 1 if fails else 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--papers", default=os.path.expanduser("~/proofs/papers"))
    ap.add_argument("--out")
    ap.add_argument("--height", type=int, default=2)
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    if a.self_test:
        return self_test()

    p = os.path.join(a.papers, "hexirp", "bashicu-rathjen.html")
    if not os.path.exists(p):
        print(f"[飛ばす] 資料が無い: {p}")
        print(f"  出典: {CANON}")
        print("  資料は著作物 (CC BY-SA 3.0) なのでリポジトリには入れない。")
        return 0
    rows, bad = read_pairs(p)
    hs = {}
    for r in rows:
        hs[r[0]] = hs.get(r[0], 0) + 1
    print(f"読んだ対 {len(rows)} (高さ別 {hs});  翻訳できなかった行 {bad}")
    if not a.out:
        print("  --out を渡すと Lean の検査ファイルを書く")
        return 0
    n = emit(rows, a.out, a.height)
    print(f"高さ {a.height} の {n} 行を {a.out} に書いた")
    print(f"  cd lean && leanman check -C $PWD --backend lean {a.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
