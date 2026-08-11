#!/usr/bin/env python3
"""map-vs-table.py — 項→行列の写像を、生成表を神託にして検査する Lean ファイルを書く。

**なぜ表なのか。** 2026-08-12 に、`sqv'` の実在する欠陥を次の 4 つが素通りさせた:

    nfOKLimitCorpus        95 項    違反 0
    agreeCorpus           169 項    違反 0
    certRows               11 行    違反 0
    certRows の高さ2絞り     3 行    違反 0

捕まえたのは生成表だけだった。**理由は明確で、上の 4 つは「既に動いたもの」を集めた
コーパスだから、動かないものを含み得ない。**表は集めたものではなく主張そのもので、
まだ誰も突き合わせていない行が入っている。**成功から作ったコーパスは失敗できない。**

    python3 scripts/map-vs-table.py --map Evidence.SqV.sqv' --out /tmp/mt.lean
    cd lean && leanman check -m mt -C $PWD --backend lean /tmp/mt.lean

生成される Lean は陽性・陰性の両対照を持つ。片方だけでは「違反 0」が
「写像が正しい」なのか「検査が動いていない」なのか区別できない。

**行の重みは同じではない。** 表の行は証明列が空のものがある (根拠が `oR` だけ)。
出力はその区別を印字する。証明のある行との不一致は写像の誤り、証明の無い行との
不一致は**どちらが正しいか未決**であり、扱いが違う。実例: `φ̄(ε₀,0)` の行は証明が
無く、`oR` と `sqv'` が食い違った。決着は BMS 参照実装の展開で付いた
(`~/proofs/yaBMS/c/bms "M[n]"`) — **どちらの写像からも作られていない第三の情報源**。
"""
import argparse
import sys

TEMPLATE = '''import Rows.TM
import Evidence.SqV

namespace MapVsTable

/-- 表の行のうち、この検査が扱えるもの: 高さ 2 で、項が `CNV` のもの。 -/
def cand : List (BMS.Matrix × TM.Term × String) :=
  (Rows.rows.filter fun r =>
    Evidence.WF.CNV r.t && r.m.length > 0 && (r.m.headD []).length == 2).map
      fun r => (r.m, r.t, r.proof)

def failuresOf (f : TM.Term → BMS.Matrix) : List (TM.Term × BMS.Matrix × BMS.Matrix × String) :=
  cand.filterMap fun c => if f c.2.1 == c.1 then none else some (c.2.1, c.1, f c.2.1, c.2.2)

-- 陽性対照: 定数写像はほぼ全行で外れなければならない。
-- 陰性対照: 表そのものを引く写像は 1 行も外してはならない。
def tableLookup (t : TM.Term) : BMS.Matrix :=
  (cand.find? fun c => c.2.1 == t).map Prod.fst |>.getD []

#eval s!"CTRL constant map fails (must be large): {(failuresOf (fun _ => [])).length} of {cand.length}"
#eval s!"CTRL table lookup fails (must be 0)   : {(failuresOf tableLookup).length} of {cand.length}"

#eval s!"rows usable: {cand.length}   of which with a proof: {(cand.filter fun c => !(c.2.2.isEmpty)).length}"
#eval s!"MAPNAME fails: {(failuresOf MAP).length}"
#eval (failuresOf MAP).map fun r =>
  (r.1.toStr, r.2.1, r.2.2.1, if r.2.2.2 == "" then "NO PROOF - undecided" else "proved row - map is wrong")

end MapVsTable
'''


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--map",
                    help="検査する写像の完全修飾名 (例 Evidence.SqV.sqv')")
    ap.add_argument("--out", default="/tmp/map-vs-table.lean")
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()

    if a.self_test:
        # 生成物が両対照を含み、写像名が両方の場所に入ることだけを確かめる。
        # 判定は Lean 側なので、ここで確かめられるのは書き出しの形だけ。
        src = TEMPLATE.replace("MAPNAME", "X.y").replace("MAP", "X.y")
        ok = ("CTRL constant map" in src and "CTRL table lookup" in src
              and src.count("X.y") >= 3 and "certRows" not in src)
        print("map-vs-table 自己試験: " + ("形は正しい (両対照あり、certRows を使わない)" if ok else "FAIL"))
        return 0 if ok else 1

    if not a.map:
        ap.error("--map が要る")
    src = TEMPLATE.replace("MAPNAME", a.map).replace("MAP", a.map)
    open(a.out, "w", encoding="utf-8").write(src)
    print(f"書き出した: {a.out}")
    print(f"次に:  cd lean && leanman check -m mt -C $PWD --backend lean {a.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
