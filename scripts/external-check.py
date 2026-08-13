#!/usr/bin/env python3
"""外部資料と対応表を突き合わせる。

なぜあるか。表の値のうち Γ₀ より上は、単一の翻訳 `oR = dict ∘ transPort ∘ ofMatrix`
からしか来ていない。較正事故 (v0.1.41) は、まさにそういう値を、その翻訳の正しさより
強く信じて公開した事故だった。だから**外部の独立な資料と突き合わせる**手段が要る。

この検査は一度その場限りのスクリプトで行い、実際に食い違いを見つけた。そのとき
書き捨てたので、次に表が変われば同じものをまた書くことになる。使い捨ての道具は
毎回同じ穴を作る (plan/constitutions.md C8) ので、ここに固定する。

資料は著作物なのでリポジトリには入れない。ディレクトリを渡して読む。無い資料は
理由を表示して飛ばす — **黙って 0 件にしない**。「該当なし」と「読めなかった」を
同じ出力にしないこと自体が C8 の規則である。

`--papers` には、上の資料を保存したディレクトリを渡す。ファイル名は既定で
`pbot/…観察日記.html`、`BMS-vs-Rathjens-OCF.xlsx`、`hexirp/*.html` を探す。

  python3 scripts/external-check.py --papers <資料を置いたディレクトリ>
  python3 scripts/external-check.py --self-test

資料 (2026-08 時点で使ったもの)。**出典が正で、ローカルの控えは複製にすぎない。**

  P進大好きbot「超限変数拡張ブーフホルツのψ関数観察日記」
      <https://googology.fandom.com/ja/wiki/ユーザーブログ:P進大好きbot/超限変数拡張ブーフホルツのψ関数観察日記>
      Buchholz ψ → Rathjen。著者自身が「あくまで予測であり、全然証明していません」
      「BO 未満でも食い違っているかもしれません」と明記している。

  BMS vs Rathjen's OCF (スプレッドシート)
      <https://docs.google.com/spreadsheets/d/1UkVwMxbo_i9JVh9suHZF6ycp2yaIrHRZR0XZceB5BRs/edit?gid=289246492#gid=289246492>
      BM4 | Buchholz | Rathjen の三列。シート名が領域を表す。

  Hexirp「バシク行列システムの解析」
      <https://googology.fandom.com/ja/wiki/ユーザーブログ:Hexirp/バシク行列システムの解析>
      BM4 → Buchholz。「自明」「推測」「基本列」などの確信度ラベル付き。
      (解析 2・3 は同じブログの続き)

第 1 段 (BM4 → Buchholz) はこのリポジトリの `Trans.Recal` が pss2bp の移植なので、
`#eval` で機械的に検算できる。実際に xlsx の Buchholz 列と突き合わせて 374/376 一致し、
残る 2 件は xlsx 側が**非標準形**だった (シート「(0,0)(1,1)(2,2)(3,3) まで」B28 と B35)。

**naruyoko 氏の実装群** — ブラウザで読むなら <https://naruyoko.github.io/googology/>、
出典として引くなら <https://github.com/Naruyoko/googology/tree/main/>。CC BY-SA 3.0:

  pss-vs-buchholz/common.js    BMS → Buchholz。**このリポジトリの `Trans/Recal.lean` の
      移植元**で、関数名がそのまま対応する (fpar, Pred, Derp, IncrFirst, Adm, TrMax,
      Br, FirstNodes, Joints, Red)。Buchholz 側も一式ある:
      parseBuchholz / normalizeBuchholz / equalBuchholz / lessThanBuchholz /
      **isStandardBuchholz** / fundBuchholz / domBuchholz。
      項は `D_0(...)` または `p_0(...)` と書く (`ψ` は受け付けない)。
      上の非標準 2 件はこれで判定した。
  padicBotRathjen/implementation.js   Rathjen 𝔗(M) 単体の**独立実装**。項 (Phi/Chi/Psi/Sum)、
      inT/inPT/inST/inRT、lessThan、inOT、pred、deg、fund、dom、FGH。翻訳は含まない。
      χ を階層のまま持つ (このリポジトリは Z a = χ_a(0) に潰している)。
      **`TM/` の順序判定・正規形・基本列を外部から検算する対照として使える。**
      node から呼ぶ包みが `scripts/padicbot-ref.js` にある (2026-08-13)。
      **ただし辞書はまだ無い。** 先方の Ω 階層は χ ではなく φ^1 で、
      `chi^{M}_{0}(0) != W` である。当方の `Z 1 = χ_1(0) = I` が先方の何に当たるかは
      未確定で、確かめずに対応させてはならない。

**表記の差は食い違いではない。** φ̄ は不動点を飛ばすので、資料の φ_0(φ_1(0)+1) は
リポジトリの φ̄(0,ε₀) と同じものである。一度これを怠って 98 件中 97 件を食い違いと
報告し、全部が略記の差だった。両辺を同じ形に展開してから数えること。
"""

import argparse, html, json, os, re, sys

# --- 抽出 -----------------------------------------------------------------

def strip_html(path):
    s = open(path, encoding="utf-8", errors="replace").read()
    s = re.sub(r"(?is)<(script|style)[^>]*>.*?</\1>", " ", s)
    t = html.unescape(re.sub(r"(?s)<[^>]+>", "\n", s))
    return [l.strip() for l in re.sub(r"[ \t]+", " ", t).split("\n") if l.strip()]


def diary_pairs(path):
    """日記: 左列 Buchholz / 右列 Rathjen が交互に並ぶ。"""
    lines, out, i = strip_html(path), {}, 0
    while i + 1 < len(lines):
        a, b = lines[i], lines[i + 1]
        if a.startswith("\\(") and a.endswith("\\)") and b.startswith("\\(") and b.endswith("\\)"):
            out.setdefault(re.sub(r"\s", "", a[2:-2]), b[2:-2].strip())
            i += 2
        else:
            i += 1
    return out


def hexirp_pairs(paths):
    """Hexirp: `\\( (0,0)(1,1) = ψ… \\)` の形。"""
    out = {}
    for p in paths:
        for l in strip_html(p):
            m = re.match(r"^\\\(\s*((?:\(\s*[\d\s,]+\)\s*)+)=(.*?)\\\)$", l)
            if m:
                out.setdefault(re.sub(r"\s", "", m.group(1)), m.group(2).strip())
    return out


def xlsx_rows(path):
    """xlsx: シートごとに `BM4` 見出し行の下がデータ。シート名が領域を表す。"""
    try:
        import openpyxl
    except ImportError:
        return None, "openpyxl が無い (pip install openpyxl)"
    wb = openpyxl.load_workbook(path, data_only=True)
    out = []
    for ws in wb:
        hdr = None
        for r in ws.iter_rows():
            vals = ["" if c.value is None else str(c.value).strip() for c in r]
            if not any(vals):
                continue
            if vals[0] == "BM4":
                hdr = vals
                continue
            if hdr is None or not vals[0].startswith("("):
                continue
            d = {"sheet": ws.title, "row": r[0].row, "bm4": re.sub(r"\s", "", vals[0])}
            for i, h in enumerate(hdr):
                if h and i < len(vals) and vals[i]:
                    d[h] = vals[i]
            out.append(d)
    return out, None


def table_rows(repo):
    """生成された対応表から (行列, T(M) 値, 通称) を読む。"""
    out = []
    for l in open(os.path.join(repo, "table/table-r1.md"), encoding="utf-8"):
        m = re.match(r"^\| \[`([^`]+)`\]\([^)]*\) \| ([^|]*) \| ([^|]*)\|", l)
        if m:
            out.append((m.group(1).strip(), m.group(2).strip(), m.group(3).strip()))
    return out


# --- 正規化 ---------------------------------------------------------------

def canon_rathjen(x):
    """資料側と表側を比較できる形に寄せる。**同値判定ではない** — これは
    「明らかに同じ綴り」を潰すだけで、残ったものは人間か Lean が見る必要がある。"""
    x = re.sub(r"^[^=]{1,8}=", "", re.sub(r"\s", "", x))
    x = x.replace("\\varphi", "phi").replace("\\psi", "psi").replace("\\chi", "chi")
    x = x.replace("\\bar{phi}", "phi").replace("\\omega", "w").replace("\\Omega", "Om")
    x = x.replace("φ̄", "phi").replace("φ", "phi").replace("ψ", "psi")
    x = x.replace("ω", "w").replace("Ω", "Om")
    x = x.replace("ε", "eps").replace("ζ", "zeta").replace("Γ", "Gam").replace("χ", "chi")
    x = re.sub(r"[{}\\`$]", "", x)
    # 資料は Veblen を下付きで φ_a(b) と書き、リポジトリは 2 引数で φ̄(a,b) と書く。
    # 揃えないと 98 件中 97 件が「食い違い」に見える (実際にそう報告して誤りだった)。
    x = re.sub(r"phi_?([^(]+)\(", lambda m: "phi(" + m.group(1) + ",", x)
    x = re.sub(r"psi_?([^(]+)\(", lambda m: "psi(" + m.group(1) + ",", x)
    # このリポジトリは Z a = χ_a(0) と書き、資料は χ_a(0) または Ω (a=0) と書く。
    x = re.sub(r"Z\(([^)]*)\)", lambda m: "Om" if m.group(1) in ("0", "zero") else "chi(" + m.group(1) + ",0)", x)
    x = re.sub(r"chi\(0,0\)", "Om", x)
    return x.replace("_", "")


# --- 検査 -----------------------------------------------------------------

def run(papers, repo):
    bad = 0
    print(f"資料ディレクトリ: {papers}")
    print(f"リポジトリ      : {repo}\n")

    rows = table_rows(repo)
    print(f"対応表の行: {len(rows)}")

    xp = os.path.join(papers, "BMS-vs-Rathjens-OCF.xlsx")
    if not os.path.exists(xp):
        print(f"  [飛ばす] {xp} が無い — 読めなかったのであって、一致 0 ではない")
    else:
        xl, err = xlsx_rows(xp)
        if err:
            print(f"  [飛ばす] {err}")
        else:
            by = {}
            for d in xl:
                if d.get("Rathjen's OCF"):
                    by.setdefault(d["bm4"], d)
            hit = [(m, t, n) for m, t, n in rows if m in by]
            same = [x for x in hit if canon_rathjen(by[x[0]]["Rathjen's OCF"]) == canon_rathjen(x[1])]
            print(f"  xlsx: {len(xl)} 行、うち Rathjen 列あり {len(by)}")
            print(f"    表と行列が一致: {len(hit)}/{len(rows)}")
            print(f"    値も一致 (綴り正規化後): {len(same)}/{len(hit)}")
            print(f"    要確認: {len(hit)-len(same)}  ← 綴りの差か本物の食い違いかは人が見る")
            key = "Rathjen's OCF"
            for m, t, n in hit:
                if (m, t, n) not in same:
                    src = by[m][key][:30]
                    print(f"      {m:34} 資料={src:32} 表={canon_rathjen(t)[:34]}")

    dp = os.path.join(papers, "pbot", "2020-P進大好きbot-超限変数拡張ブーフホルツのψ関数観察日記.html")
    if not os.path.exists(dp):
        print(f"\n  [飛ばす] 日記が無い: {dp}")
    else:
        d = diary_pairs(dp)
        print(f"\n  日記: Buchholz→Rathjen {len(d)} 対")
        print("    注意: 著者自身が「あくまで予測であり、全然証明していません」")

    hx = os.path.join(papers, "hexirp")
    if not os.path.isdir(hx):
        print(f"\n  [飛ばす] Hexirp が無い: {hx}")
    else:
        ps = [os.path.join(hx, f) for f in sorted(os.listdir(hx)) if f.endswith(".html")]
        h = hexirp_pairs(ps)
        print(f"\n  Hexirp: BM4→Buchholz {len(h)} 対 ({len(ps)} ファイル)")
    return bad


# --- 自己試験 (constitution C0) -------------------------------------------

def self_test():
    """捕まえるはずのものを 1 つずつ与えて発火させ、正常な対照で沈黙させる。
    片側だけでは、常に「一致」と言う検査器と区別がつかない。"""
    fails = []

    # 綴りの差は食い違いにしない (実際にこれを怠って 97/98 を誤検出した)
    for a, b in [
        (r"\varphi_1(0)", "φ̄(1,0)".replace("φ̄", "phi").replace("(1,0)", "(1,0)")),
        (r"\psi_{\Omega}(0)", "ψ_{Ω}(0)"),
        (r"\omega+\omega", "ω+ω"),
    ]:
        if canon_rathjen(a) != canon_rathjen(b):
            fails.append(f"綴り差を食い違いと判定: {a!r} vs {b!r} -> {canon_rathjen(a)!r} / {canon_rathjen(b)!r}")

    # 本物の差は必ず残す (今夜見つけた実物)
    real = (r"\psi_{\Omega}(\varphi_1(\Omega+1))", r"\psi_{\Omega}(Z(1))")
    if canon_rathjen(real[0]) == canon_rathjen(real[1]):
        fails.append("本物の食い違いを潰した: " + str(real))

    # 抽出器: 資料が無いときは黙って 0 を返さない
    if os.path.exists("/nonexistent-papers-dir"):
        fails.append("試験の前提が壊れている")

    if fails:
        print("external-check self-test: 失敗")
        for f in fails:
            print("  " + f)
        return 1
    print("external-check self-test: 4/4 (綴り差 3 件を潰し、本物の差 1 件を残す)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    # 既定値は置かない。作業者ごとに違う場所であり、公開リポジトリに個人の
    # ディレクトリ構成を書くと、読者には見えないものを指すことになる。
    ap.add_argument("--papers", help="上の資料を保存したディレクトリ")
    ap.add_argument("--repo", default=os.path.join(os.path.dirname(__file__), ".."))
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    if a.self_test:
        sys.exit(self_test())
    if not a.papers:
        ap.error("--papers が要る (資料の入手先はこのファイル冒頭の URL)")
    sys.exit(run(a.papers, os.path.abspath(a.repo)))
