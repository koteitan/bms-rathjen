import Evidence.RegionNext9
import Rows

/-
Evidence/RegionNext10.lean — THE WORK TREE'S THREE OPEN ITEMS, ROUND ONE (§147-)

Split point: `RegionNext9` closed at §146.  `import Rows` is new here — §147 adjudicates
against `Rows.Selected`'s family proofs, which the RegionNext chain never needed before.
-/

namespace Evidence.Region

open BMS

/-! ## §147 THE NINE ROWS WHERE `Trans.oR` AND HEXIRP'S TABLE DISAGREE — ALL NINE OURS

`table/findings.md` の「Hexirp 氏の対応表との差分」が残していた 9 行を、今日ふたたび
資料から生成し直して裁く。9 行のうち 8 行は 2026-08-13〜15 に決着していた。**残る 1 行
(先方の 326 行目) は「E3 では決められない」として未決のまま置かれていた。この file は
その 1 行を決める。**

## 辞書 — これを間違えて 2026-08-13 に 3 行を誤って「誤り」と報告した

撤回の記録は `table/findings.md` にある。同じ穴を二度掘らないために、辞書と、それを
どう立てたかをここに書く。

```
先方 phi(a,b)  =  当方 phiNF (1+a) b
先方 w(x)      =  当方 phiNF 0 (1+x)          w(0) = ω
先方 W(0)      =  当方 Z 0 = Ω
先方 W(x), x≠0 =  訳せない
```

**`phiNF` であって `phi` ではない。** 当方の φ̄ は [Rathjen, 1991] 2.6(vi) の不動点を
飛ばす版で、先方の φ は飛ばさない。先方の `phi(0,e(0)+1)` と当方の φ̄(0,ε₀) は同じもの
である。生の `phi` で組むと記法の差が全部「食い違い」に化ける。2026-08-13 の誤報は
これだった。**`Z (tr x)` で `W(x≠0)` を訳してもならない** — Ω₂ = χ₀(1) は 𝔗(M) に項を
持たず、`Z 1` は χ₁(0) = I という別の順序数だからである。

**どう立てたか。** 辞書は `scripts/hexirp-rathjen-check.py` の中にあり、その自己試験
6/6 が今日通っている (辞書の 1 ずらし・`1+x` の吸収・行列の読み取り・壊れた行の計上・
`W(x≠0)` の拒否・未知記号の拒否)。傍証は「当方の表と一致するか」であって `NfOK` では
ない。今日の再生成は 1249 対を読み、Veblen 断片 390 行で `oR` と 379 行一致した。
下の §1 は、そうして今日生成した 9 行の項が、repo が既に持っている定数と**同じ**で
あることを確かめる。

## 測った数 (今日、2026-08-21)

```
読んだ対 1249 (高さ 2)     訳せなかった行 3700
Veblen 断片 390 行         oR 一致 379、食い違い 11
断片の外 859 行            辞書が未検証なので数えない
当方の表 60 行             先方の表にあるもの 50、うち断片内 26 (一致 17、食い違い 9)
                           残る 24 は `Z 1` の行で、辞書が未検証 = 比較していない
先方が単調でない対 2       oR が単調でない対 0
先方が潰す対 2             oR が潰す対 0
対照 (逆向きに見る) 389/389 が壊れる = 試験は生きている
```

食い違う 11 のうち 2 件は先方の表だけで決まる (同じ値を隣り合う 2 行に与えている)。
残る 9 件がこの file の対象で、**9 件とも Γ₀ より下**にある。§137 の `Z 1` の欠陥とは
別の話である。
-/

section
open TM Term BMS Trans Rows Rows.Selected


open TM Term BMS Trans Rows Rows.Selected

/-! ### §147.1 THE NINE ROWS, REGENERATED TODAY AND FROZEN

下の 9 つの窓は、今日 `scripts/hexirp-rathjen-check.py --papers ~/proofs/papers` が
資料から作った項をそのまま写したものである。各窓は先方の表の 5 行 — 食い違う行と、
その前後 2 行ずつ。行番号は先方の高さ 2 の部分を 0 起点で数えたもの。 -/

def w145 : List (BMS.Matrix × Term) := [
  ([[0,0], [1,1], [2,0], [1,1], [1,0], [2,1], [3,0]], (TM.Term.phiNF TM.Term.zero (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF TM.Term.zero (TM.Term.ofNat 1)) (TM.Term.ofNat 1))) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF TM.Term.zero (TM.Term.ofNat 1)))))),
  ([[0,0], [1,1], [2,0], [1,1], [1,0], [2,1], [3,0], [1,0]], (TM.Term.phiNF TM.Term.zero (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF TM.Term.zero (TM.Term.ofNat 1)) (TM.Term.ofNat 1))) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF TM.Term.zero (TM.Term.ofNat 1))) (TM.Term.ofNat 1))))),
  ([[0,0], [1,1], [2,0], [1,1], [1,0], [2,1], [3,0], [1,0], [2,1]], (TM.Term.phiNF TM.Term.zero (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF TM.Term.zero (TM.Term.ofNat 1)) (TM.Term.ofNat 1))) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF TM.Term.zero (TM.Term.ofNat 1))) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.ofNat 1)))))),
  ([[0,0], [1,1], [2,0], [1,1], [1,0], [2,1], [3,0], [1,0], [2,1], [3,0]], (TM.Term.phiNF TM.Term.zero (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF TM.Term.zero (TM.Term.ofNat 1)) (TM.Term.ofNat 1))) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF TM.Term.zero (TM.Term.ofNat 1))) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF TM.Term.zero (TM.Term.ofNat 1))))))),
  ([[0,0], [1,1], [2,0], [1,1], [1,0], [2,1], [3,0], [2,0]], (TM.Term.phiNF TM.Term.zero (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF TM.Term.zero (TM.Term.ofNat 1)) (TM.Term.ofNat 1))) (TM.Term.phiNF TM.Term.zero (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF TM.Term.zero (TM.Term.ofNat 1))) (TM.Term.ofNat 1))))))]

def w248 : List (BMS.Matrix × Term) := [
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.ofNat 1))))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [1,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.ofNat 1))) (TM.Term.ofNat 1)))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [1,1], [2,0]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.ofNat 1))) (TM.Term.phiNF (TM.Term.ofNat 1) TM.Term.zero)))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [1,1], [2,0], [3,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.ofNat 1))) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.ofNat 1))))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [1,1], [2,0], [3,1], [4,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.ofNat 1))) (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero))))]

def w249 : List (BMS.Matrix × Term) := [
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [1,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.ofNat 1))) (TM.Term.ofNat 1)))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [1,1], [2,0]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.ofNat 1))) (TM.Term.phiNF (TM.Term.ofNat 1) TM.Term.zero)))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [1,1], [2,0], [3,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.ofNat 1))) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.ofNat 1))))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [1,1], [2,0], [3,1], [4,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.ofNat 1))) (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero)))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [1,1], [2,0], [3,1], [4,1], [3,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.ofNat 1))) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.ofNat 1))))))]

def w265 : List (BMS.Matrix × Term) := [
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [4,0], [5,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.phiNF (TM.Term.ofNat 1) TM.Term.zero))))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [4,0], [5,1], [6,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero))))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [4,0], [5,1], [6,1], [5,0]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF TM.Term.zero (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.ofNat 1)))))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [4,0], [5,1], [6,1], [5,0], [6,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF TM.Term.zero (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.phiNF (TM.Term.ofNat 1) TM.Term.zero)))))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [4,0], [5,1], [6,1], [5,0], [6,1], [7,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF TM.Term.zero (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero))))))]

def w266 : List (BMS.Matrix × Term) := [
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [4,0], [5,1], [6,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero))))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [4,0], [5,1], [6,1], [5,0]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF TM.Term.zero (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.ofNat 1)))))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [4,0], [5,1], [6,1], [5,0], [6,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF TM.Term.zero (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.phiNF (TM.Term.ofNat 1) TM.Term.zero)))))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [4,0], [5,1], [6,1], [5,0], [6,1], [7,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF TM.Term.zero (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero)))))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [4,0], [5,1], [6,1], [5,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.ofNat 1))))))]

def w267 : List (BMS.Matrix × Term) := [
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [4,0], [5,1], [6,1], [5,0]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF TM.Term.zero (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.ofNat 1)))))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [4,0], [5,1], [6,1], [5,0], [6,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF TM.Term.zero (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.phiNF (TM.Term.ofNat 1) TM.Term.zero)))))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [4,0], [5,1], [6,1], [5,0], [6,1], [7,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF TM.Term.zero (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero)))))),
  ([[0,0], [1,1], [2,1], [1,1], [2,0], [3,1], [4,1], [3,1], [4,0], [5,1], [6,1], [5,1]], (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.phiNF (TM.Term.ofNat 1) (TM.Term.add (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero) (TM.Term.ofNat 1)))))),
  ([[0,0], [1,1], [2,1], [1,1], [2,1]], (TM.Term.phiNF (TM.Term.ofNat 2) (TM.Term.ofNat 1)))]

def w326 : List (BMS.Matrix × Term) := [
  ([[0,0], [1,1], [2,1], [2,1], [1,1], [2,1], [2,1], [1,1], [2,1], [2,1]], (TM.Term.phiNF (TM.Term.ofNat 3) (TM.Term.add (TM.Term.ofNat 1) (TM.Term.ofNat 1)))),
  ([[0,0], [1,1], [2,1], [2,1], [2,0]], (TM.Term.phiNF (TM.Term.ofNat 3) (TM.Term.phiNF TM.Term.zero (TM.Term.ofNat 1)))),
  ([[0,0], [1,1], [2,1], [2,1], [2,0], [1,1]], (TM.Term.phiNF (TM.Term.ofNat 3) (TM.Term.phiNF (TM.Term.ofNat 1) TM.Term.zero))),
  ([[0,0], [1,1], [2,1], [2,1], [2,0], [1,1], [2,1]], (TM.Term.phiNF (TM.Term.ofNat 3) (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero))),
  ([[0,0], [1,1], [2,1], [2,1], [2,0], [1,1], [2,1], [2,1]], (TM.Term.phiNF (TM.Term.ofNat 3) (TM.Term.phiNF (TM.Term.ofNat 3) TM.Term.zero)))]

def w327 : List (BMS.Matrix × Term) := [
  ([[0,0], [1,1], [2,1], [2,1], [2,0]], (TM.Term.phiNF (TM.Term.ofNat 3) (TM.Term.phiNF TM.Term.zero (TM.Term.ofNat 1)))),
  ([[0,0], [1,1], [2,1], [2,1], [2,0], [1,1]], (TM.Term.phiNF (TM.Term.ofNat 3) (TM.Term.phiNF (TM.Term.ofNat 1) TM.Term.zero))),
  ([[0,0], [1,1], [2,1], [2,1], [2,0], [1,1], [2,1]], (TM.Term.phiNF (TM.Term.ofNat 3) (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero))),
  ([[0,0], [1,1], [2,1], [2,1], [2,0], [1,1], [2,1], [2,1]], (TM.Term.phiNF (TM.Term.ofNat 3) (TM.Term.phiNF (TM.Term.ofNat 3) TM.Term.zero))),
  ([[0,0], [1,1], [2,1], [2,1], [2,1]], (TM.Term.phiNF (TM.Term.ofNat 4) TM.Term.zero))]

def w328 : List (BMS.Matrix × Term) := [
  ([[0,0], [1,1], [2,1], [2,1], [2,0], [1,1]], (TM.Term.phiNF (TM.Term.ofNat 3) (TM.Term.phiNF (TM.Term.ofNat 1) TM.Term.zero))),
  ([[0,0], [1,1], [2,1], [2,1], [2,0], [1,1], [2,1]], (TM.Term.phiNF (TM.Term.ofNat 3) (TM.Term.phiNF (TM.Term.ofNat 2) TM.Term.zero))),
  ([[0,0], [1,1], [2,1], [2,1], [2,0], [1,1], [2,1], [2,1]], (TM.Term.phiNF (TM.Term.ofNat 3) (TM.Term.phiNF (TM.Term.ofNat 3) TM.Term.zero))),
  ([[0,0], [1,1], [2,1], [2,1], [2,1]], (TM.Term.phiNF (TM.Term.ofNat 4) TM.Term.zero)),
  ([[0,0], [1,1], [2,1], [3,0]], (TM.Term.phiNF (TM.Term.phiNF TM.Term.zero (TM.Term.ofNat 1)) TM.Term.zero))]

/-- 9 つの窓。 -/
def wins : List (List (BMS.Matrix × Term)) :=
  [w145, w248, w249, w265, w266, w267, w326, w327, w328]

/-- 各窓の真ん中が食い違う行である。 -/
def mid (w : List (BMS.Matrix × Term)) : BMS.Matrix × Term :=
  (w.drop 2).headD ([], TM.Term.zero)

/-- 食い違う 9 行 — 行列・当方の値・先方の値。当方の値は `Rows.rows` の値である。 -/
def nine : List (BMS.Matrix × Term × Term) :=
  [(F1.M, F1.t, F1.tHex), (F2a.M, F2a.t, F2a.tHex), (F2b.M, F2b.t, F2b.tHex),
   (F3a.M, F3a.t, F3a.tHex), (F3b.M, F3b.t, F3b.tHex), (F3c.M, F3c.t, F3c.tHex),
   (G9.M, G9.t, Fam4.h326), (G10.M, G10.t, Fam4.h327), (Fam4.M328, Fam4.t328, Fam4.h328)]

-- **今日の再生成が repo の定数と一致する。** これが辞書の傍証である。
#guard wins.map (fun w => (mid w).1) == nine.map (·.1)
#guard wins.map (fun w => (mid w).2) == nine.map (·.2.2)
#guard G11.M == Fam4.M328 && G11.t == Fam4.t328

/-! ### §147.2 THE DISAGREEMENT ITSELF, FROZEN -/

-- 当方の値は表の行そのもの (E1 は `Trans.oR`)
#guard nine.all fun r => Trans.oR r.1 == some r.2.1
#guard nine.all fun r => Rows.rows.any fun x => x.m == r.1 && x.t == r.2.1
-- 先方の値も 𝔗(M) の極限の項である。型や系の違いではない
#guard nine.all fun r => inT r.2.2 && kindT r.2.2 == KindT.isLim
#guard nine.all fun r => !(r.2.1 == r.2.2)
-- 9 行とも Γ₀ より下 (§137 の `Z 1` の欠陥とは別の領域)
#guard nine.all fun r => lt r.2.1 (psi (Z zero) zero) && lt r.2.2 (psi (Z zero) zero)
-- 向き: 6 行は当方が小、3 行 (族 3) は先方が小
#guard (nine.countP fun r => lt r.2.1 r.2.2) == 6
#guard (nine.countP fun r => lt r.2.2 r.2.1) == 3
#guard (nine.map fun r => lt r.2.1 r.2.2)
     == [true,true,true,false,false,false,true,true,true]

/-! **`Trans.o?` は第二の意見にならない。** repo には翻訳が 2 つある (`Trans.oR` =
`dict ∘ transPort ∘ ofMatrix` と、対の側の `Trans.o?`)。`o?` は族 1〜3 の 6 行では
`oR` と同じ値を出すが、族 4 の 3 行では**どちらの側とも違う値**を出す。表 60 行のうち
33 行で表の値と違う。`Rows/Selected.lean` 自身が「届かないか、届いても撤回領域で
誤った値を返す」と書いているとおりで、**独立な確認には使えない**。数だけ固定する。 -/

#guard (nine.take 6).all fun r => Trans.o? r.1 == some r.2.1
#guard (nine.drop 6).all fun r => Trans.o? r.1 != some r.2.1
#guard (Rows.rows.filter fun r => Trans.o? r.m != some r.t).length == 33
#guard Rows.rows.length == 60

/-! ### §147.3 THE ORDER TEST, APPLIED TO EACH ROW — IT REFUTES NEITHER SIDE

決めた道具は「BMS の順序で並べ、隣接対の狭義単調性と単射性を両側に当てる」である。
390 行の断片全体では先方に単調でない対 2・潰す対 2 が出て、そこは先方の誤りだった。
**同じ道具を 9 行それぞれの近傍に当てると、どちらの側も破れない。**
これは「決められなかった」の中身であって、どちらかの証拠ではない。隣接対で足りるのは
𝔗(M) の順序が推移的だからで、窓の中に何かが隠れることはない。 -/

def adjOf (w : List (BMS.Matrix × Term)) : List ((BMS.Matrix × Term) × (BMS.Matrix × Term)) :=
  w.zip w.tail

-- 窓は BMS の順序で狭義に増えている (先方の表の並びが順序であることの確認)
#guard wins.all fun w => (adjOf w).all fun c => BMS.cmpM c.1.1 c.2.1 == Ordering.lt
-- 先方の値は窓の中で狭義単調・単射
#guard wins.all fun w => (adjOf w).all fun c => lt c.1.2 c.2.2
-- 当方の値も窓の中で狭義単調・単射
#guard wins.all fun w => (adjOf w).all fun c =>
  match Trans.oR c.1.1, Trans.oR c.2.1 with
  | some u, some v => lt u v
  | _, _ => false
-- CTRL 逆向きに見れば両側とも総崩れになる (= 試験が効いている)
#guard wins.all fun w => (adjOf w).all fun c => !(lt c.2.2 c.1.2)
#guard wins.all fun w => (adjOf w).all fun c =>
  match Trans.oR c.1.1, Trans.oR c.2.1 with
  | some u, some v => !(lt v u)
  | _, _ => false
-- CTRL 潰す対はどちらの側にも無い
#guard wins.all fun w => (adjOf w).all fun c => !(c.1.2 == c.2.2)

/-! ### §147.4 THE TEST THAT DOES DECIDE — THE MATRIX'S OWN EXPANSION

正しい写像では、極限の行列の値はその展開の値の上限である。だから
**掲載値が「自分の展開の値の上限」より真に上にあれば、その値は大きすぎる**
(§137/§139 が当方の 5 行を反証したときと同じ形)。逆に**展開の値のどれかが掲載値
以上なら、その値は小さすぎる** — こちらは上限の話が要らず、単調性だけで済む。

どちらの向きも、当方の**行列の値**ではなく**展開の値**に乗っている。展開の値は 9 行
すべてで全 n の定理がある (下の `eight_rows_e3` と `Rows.Selected.G9.oR_M`)。 -/

-- 当方の値は 9 行すべてで展開の値の上限である
#guard nine.all fun r => (List.range 8).all fun n =>
  match Trans.oR (BMS.expand r.1 n) with | some v => lt v r.2.1 | none => false
-- 先方の値が上限なのは 6 行だけ。族 3 の 3 行では上限ですらない
#guard (nine.map fun r => (List.range 8).all fun n =>
  match Trans.oR (BMS.expand r.1 n) with | some v => lt v r.2.2 | none => false)
     == [true,true,true,false,false,false,true,true,true]
-- 族 3: 先方の値以上になる展開の番号
#guard (nine.map fun r => (List.range 8).findIdx? fun n =>
  match Trans.oR (BMS.expand r.1 n) with | some v => le r.2.2 v | none => false)
     == [none,none,none,some 1,some 0,some 0,none,none,none]
-- CTRL 展開の値は狭義に増えている (上限の話が空でないこと)
#guard nine.all fun r => (List.range 7).all fun n =>
  match Trans.oR (BMS.expand r.1 n), Trans.oR (BMS.expand r.1 (n+1)) with
  | some u, some v => lt u v
  | _, _ => false

/-! ### 族 3 の 3 行 — 先方の値は自分の行列の展開の値より下である

上限の議論が要らない形。`M[n] < M` なのだから、正しい写像では
`値(M[n]) < 値(M)` でなければならない。**先方の 266 の値は 265 の行列の値より下、
先方の 267 の値は 266 の行列の値より下、先方の 265 の値は 265 の 1 番目の展開の値より
下**である。3 つとも 265〜267 の行列の間の関係で閉じている。 -/

#guard BMS.expand F3b.M 0 == F3a.M
#guard BMS.expand F3c.M 0 == F3b.M
#guard lt F3b.tHex F3a.t && lt F3c.tHex F3b.t
-- 265 の 1 番目の展開の値は、**先方が 267 に与えている値そのもの**である
#guard Trans.oR (BMS.expand F3a.M 1) == some F3c.tHex
#guard lt F3a.tHex F3c.tHex

/-! ### 8 行は E3 が決めていた — 全 n の定理

E3 (`o(M[n]) = fsN(t, k(n))`) は行ごとに添字が違う。6 行は `Rows/Selected.lean`、
2 行は `Rows/G10.lean`・`Rows/G11.lean` にある。ここではその 8 本を 1 か所に束ねて、
今日の再生成した対と結び付ける。 -/

theorem eight_rows_e3 :
    (∀ n, Trans.o? (BMS.expand F1.M n) = some (fsN F1.t (n+1)))
  ∧ (∀ n, Trans.o? (BMS.expand F2a.M n) = some (fsN F2a.t (n+1)))
  ∧ (∀ n, Trans.o? (BMS.expand F2b.M n) = some (fsN F2b.t (n+2)))
  ∧ (∀ n, Trans.o? (BMS.expand F3a.M (n+1)) = some (fsN F3a.t (n+2)))
  ∧ (∀ n, Trans.o? (BMS.expand F3b.M n) = some (fsN F3b.t (n+1)))
  ∧ (∀ n, Trans.o? (BMS.expand F3c.M n) = some (fsN F3c.t (n+1)))
  ∧ (∀ n, Trans.oR (BMS.expand G10.M n) = some (fsN G10.t (n+1)))
  ∧ (∀ n, Trans.oR (BMS.expand G11.M n) = some (fsN G11.t (n+1))) :=
  ⟨F1.e3, F2a.e3, F2b.e3, F3a.e3, F3b.e3, F3c.e3, G10.oR_M, G11.oR_M⟩

-- 族 1〜3 の E3 は `o?` で書かれている。その 6 行の展開の上では `o?` と `oR` は同じ値で、
-- だから E3 は E1 と同じ翻訳について語っている。族 4 の 3 行は `oR` で書かれた定理
-- (`G9.oR_M`・`G10.oR_M`・`G11.oR_M`) なので `o?` は要らない — 実際そこでは食い違う
#guard (nine.take 6).all fun r => (List.range 8).all fun n =>
  Trans.o? (BMS.expand r.1 n) == Trans.oR (BMS.expand r.1 n)
#guard (nine.drop 6).all fun r => (List.range 8).all fun n =>
  Trans.o? (BMS.expand r.1 n) != Trans.oR (BMS.expand r.1 n)
-- 先方の値はどのずらしでも E3 を満たさない
#guard nine.all fun r => (List.range 12).all fun k =>
  (List.range 6).any fun n => !(Trans.oR (BMS.expand r.1 n) == some (fsN r.2.2 (n+k)))
-- CTRL 同じ探索を当方の値に当てると、族 4 の 326 を除いて当たる
#guard (nine.map fun r => (List.range 12).any fun k =>
  (List.range 6).all fun n => Trans.oR (BMS.expand r.1 n) == some (fsN r.2.1 (n+k)))
     == [true,true,true,false,true,true,false,true,true]

/-! ### §147.5 THE ROW `findings.md` LEFT OPEN — HEXIRP'S 326th

`table/findings.md` の族 4 は「327 と 328 は決着。**326 は未決**」で終わっている。
理由は E3 の試験が**両側を外す**からで、この行の展開の値は標準基本列ではなく
閉じた形 `fA` だからである。乗らないことは誤りの証拠ではないので、この試験は
何も分けなかった。

**上限の議論なら分ける。** 決着に要るのは E3 ではなく「当方の値が展開の値の上限で
あること」だけで、それはこの行では定理になる。

```
325 (0,0)(1,1)(2,1)(2,1)(2,0)        両側とも φ̄(3,ω)      (一致)
326 (0,0)(1,1)(2,1)(2,1)(2,0)(1,1)   当方 ε_{φ̄(3,ω)+1}    先方 φ̄(3,ε₀)
```

`326[0]` は **325 の行列そのもの**で、そこは両側が一致している。 -/

-- 326 の 0 番目の展開は 325 の行列で、その値は両側が一致している行の値である
#guard BMS.expand G9.M 0 == [[0,0],[1,1],[2,1],[2,1],[2,0]]
#guard Trans.oR (BMS.expand G9.M 0) == some Bph
#guard (mid w326).1 == G9.M
#guard G11.M == Fam4.M328 && G11.t == Fam4.t328

/-- `G9Dict.I` は `φ̄(0,·)` の塔で、底は `φ̄(3,ω)⊕φ̄(3,ω)`。塔はどの段も
    `φ̄(1,φ̄(3,ω))` の下にある。`lt_phi_zero_one` (2.3.13(i)) を段ごとに使うだけ。 -/
theorem lt_I_t326 : ∀ n, lt (G9Dict.I n) (phi TM.Term.one Bph) = true
  | 0 => by decide
  | n+1 => by
      show lt (phi zero (G9Dict.I n)) (phi TM.Term.one Bph) = true
      rw [lt_phi_zero_one]
      exact lt_I_t326 n

/-- **当方の値は展開の値の上限である。全 n の定理、仮定ゼロ。** -/
theorem lt_fA_t326 : ∀ n, lt (fA n) G9.t = true
  | 0 => by decide
  | n+1 => by
      rw [G9Dict.fA_eq_F]
      exact lt_I_t326 (n+1)

/-- 展開の値の列は狭義に増える。 -/
theorem fA_mono326 (n : Nat) : lt (fA n) (fA (n+1)) = true := by
  rw [G9Dict.fA_eq_F, G9Dict.fA_eq_F]
  cases n with
  | zero => exact G9Dict.B_lt_I_succ 0
  | succ m => exact G9Dict.I_lt_I_succ (m+1)

/-- **326 行目の裁定。仮定ゼロ。**

    `oR` は展開の値を全 n で決めており (`G9.oR_M`)、その列は狭義に増え、
    **当方の値がその上限**である。先方の値はその上限より真に上にある。したがって
    先方の値はこの行列の展開の値の上限ではない — §137/§139 が当方の 5 行を
    反証したときと同じ形で、今度は先方の側に出る。

    これは「当方の値が上限**である**」ことまでしか言わない。「当方の値が**最小の**
    上限である」(共終性) はここでは要らないし、証明もしていない。 -/
theorem row326_gap :
    Trans.oR G9.M = some G9.t
  ∧ (∀ n, Trans.oR (BMS.expand G9.M n) = some (fA n))
  ∧ (∀ n, lt (fA n) (fA (n+1)) = true)
  ∧ (∀ n, lt (fA n) G9.t = true)
  ∧ lt G9.t Fam4.h326 = true
  ∧ inT Fam4.h326 = true :=
  ⟨rfl, G9.oR_M, fA_mono326, lt_fA_t326, by decide, by decide⟩

-- CTRL 逆向きは成り立たない (試験が空回りしていないこと)
#guard !(lt Fam4.h326 G9.t)
-- CTRL 同じ形を「一致している行」325 に当てると、隙間が無い
#guard Trans.oR [[0,0],[1,1],[2,1],[2,1],[2,0]] == some Bph && !(lt Bph Bph)


/-! ### 族 4 の 3 行の展開の値を、外部に渡した形のまま固定する

下の独立実装による裏取りには、展開の値の列を**先方の記法で手で書いて**渡した。
その列がこの repo の定理どおりであることをここで閉じておく。手で書いたのは
「φ̄(0,·) の塔、底 φ̄(3,ω)⊕φ̄(3,ω)」「φ̄(1,·) の反復、底 φ̄(3,ω)⊕1」
「φ̄(2,·) の反復、底 φ̄(3,ω)⊕1」の 3 本である。 -/

theorem fam4_expansion_values :
    (∀ n, Trans.oR (BMS.expand G9.M n) = some (fA n))
  ∧ (∀ n, fA (n+1) = iterPhiAt zero (plus Bph Bph) (n+1))
  ∧ (∀ n, Trans.oR (BMS.expand G10.M n)
            = some (iterPhiAt TM.Term.one (plus Bph TM.Term.one) (n+1)))
  ∧ (∀ n, Trans.oR (BMS.expand G11.M n)
            = some (iterPhiAt (ofNat 2) (plus Bph TM.Term.one) (n+1))) :=
  ⟨G9.oR_M, fun _ => rfl,
   fun n => (G10.oR_M n).trans (by rw [G10.fs_raw]),
   fun n => (G11.oR_M n).trans (by rw [G11.fs_raw])⟩

/-! ### 独立実装による裏取り (測定であって証明ではない)

naruyoko 氏の `padicBotRathjen` (𝔗(M) の独立実装、CC BY-SA 3.0) の `fund` で
同じことを外から測った。手順と数は `table/findings.md` に置く。要点だけ:

```
326  fund(先方の値, 1) = φ₃(ω) = 展開の 0 番目の値
     展開の値 n ≤ 12 は全部 fund(先方の値, 2) = φ₃(ω^ω) より真に下
     fund(当方の値, i) と展開の値は互いに共終 (i ≤ 10, n ≤ 12)
327  展開の値 k ≤ 9 は全部 fund(先方の値, 1) より真に下
     fund(当方の値, i) と展開の値は互いに共終 (i ≤ 8, k ≤ 9)
328  同上
CTRL 逆向きに見ると 3 行とも壊れる
```

つまり外部の実装でも、BMS の展開は先方の値に共終ではなく、当方の値には共終である。
**族 4 の 3 行とも同じ形**で、326 だけが特別なのではない。 -/

#print axioms row326_gap
#print axioms fam4_expansion_values
#print axioms lt_fA_t326
#print axioms eight_rows_e3


end

/-! ## §148 NO ROUTE BELOW ROUTE (a) — THE OBSTRUCTION TO REPAIRING `reg` IS A THEOREM

§143 prototyped `plan/chi-2ary.md`'s route (b) and watched it break; its diagnosis blamed
keeping `collapse 1` compositional.  §148 shows the truth is worse and simpler:
`gapW148` proves 𝔗(M) has NO term strictly between the ψ₁-tower's images and `φ̄(1,Ω)`, and
`noSlot148` turns that into: ANY map `BT → Term` that is monotone on standard terms, lands in
𝔗(M), sends the level-1 tower where §69 proved it must go, and keeps `Ω₂`'s image at or below
`φ̄(1,Ω)`, is contradictory.  Compositional or not.  So route (b) and every variant of it is
closed, and `plan/chi-2ary.md`'s rejected route (a) — the 2-ary χ — is the only route left. -/

open TM TM.Term
open Trans.Dict (BT dict collapse reg sub1)
open Evidence.WF

/-! ## §148.1 ORDER TOOLS AT `W139 = φ̄(1,Ω)` -/


/-! ### tools -/

theorem lt_omg_W148 (x : Term) : lt (omg x) W139 = false := by
  rw [lt_eq_ltF_succ]; rfl

theorem lt_Z_one148 (b : Term) : lt (Z b) TM.Term.one = false := by
  rw [lt_eq_ltF_succ]
  show (((Z b : Term) == zero) || ((Z b : Term) == zero)
        || ltF (2 * ((Z b).deg + (TM.Term.one).deg) + 7) (Z b) zero
        || ltF (2 * ((Z b).deg + (TM.Term.one).deg) + 7) (Z b) zero) = false
  rw [ltF_right_zero]; rfl

theorem lt_phi_one148 (c d : Term) : lt (phi c d) TM.Term.one = false := by
  rw [lt_eq_ltF_succ]
  show (if ((phi c d : Term) == TM.Term.one) = true then false
        else if (c == (zero : Term)) = true then
          ltF (2 * ((phi c d).deg + (TM.Term.one).deg) + 7) d zero
        else if ltF (2 * ((phi c d).deg + (TM.Term.one).deg) + 7) c zero = true then
          ltF (2 * ((phi c d).deg + (TM.Term.one).deg) + 7) d TM.Term.one
        else ((phi c d : Term) == zero
              || ltF (2 * ((phi c d).deg + (TM.Term.one).deg) + 7) (phi c d) zero)) = false
  rw [ltF_right_zero, ltF_right_zero, ltF_right_zero]
  by_cases h : ((phi c d : Term) == TM.Term.one) = true
  · rw [if_pos h]
  · rw [if_neg h]
    by_cases h2 : (c == (zero : Term)) = true
    · rw [if_pos h2]
    · rw [if_neg h2, if_neg (fun hc => Bool.noConfusion hc)]; rfl

theorem lt_omg_one148 (x : Term) : lt (omg x) TM.Term.one = false := by
  rw [lt_eq_ltF_succ]; rfl

/-- `lt t 1 = true` は `t = 0` に限る (𝔗(M) の項で)。 -/
theorem lt_one_zero148 : ∀ (n : Nat) (t : Term), t.deg ≤ n → inT t = true →
    lt t TM.Term.one = true → t = zero
  | 0, t, h, _, _ => absurd h (by have := deg_pos t; omega)
  | n + 1, t, h, hi, hl => by
    cases t with
    | zero => rfl
    | M => exact absurd hl (by rw [show lt M TM.Term.one = false from rfl]; exact Bool.noConfusion)
    | omg x => exact absurd hl (by rw [lt_omg_one148]; exact Bool.noConfusion)
    | phi c d => exact absurd hl (by rw [lt_phi_one148]; exact Bool.noConfusion)
    | psi k a => exact absurd hl (by rw [lt_psi_one139]; exact Bool.noConfusion)
    | Z b => exact absurd hl (by rw [lt_Z_one148]; exact Bool.noConfusion)
    | add p q =>
      exfalso
      rw [lt_add_ap102 p q (show isAP TM.Term.one = true from rfl)] at hl
      obtain ⟨hap, hip, _, _⟩ := inT_add hi
      have hdp : p.deg ≤ n := by
        have h1 := deg_pos q
        have h2 : (add p q).deg = 1 + p.deg + q.deg := rfl
        omega
      rw [lt_one_zero148 n p hdp hip hl] at hap
      exact Bool.noConfusion hap

/-- `lt (φ̄ a b) W139` の 13(iii) 枝。 -/
theorem lt_phi_W_hi148 {a b : Term} (h1 : (a == TM.Term.one) = false)
    (h2 : lt a TM.Term.one = false) :
    lt (phi a b) W139 = lt (phi a b) (Z zero) := by
  have hne : ((phi a b : Term) == W139) = false := by
    show ((phi a b : Term) == phi TM.Term.one (Z zero)) = false
    cases hq : ((phi a b : Term) == phi TM.Term.one (Z zero)) with
    | false => rfl
    | true =>
      exfalso
      have he : (phi a b : Term) = phi TM.Term.one (Z zero) := of_decide_eq_true hq
      injection he with ha _
      rw [ha] at h1
      exact Bool.noConfusion (h1.symm.trans (beq_self_eq_true _))
  have h2' : ltF (2 * ((phi a b).deg + (W139).deg) + 7) a TM.Term.one = false := by
    rw [← lt_eq_ltF a TM.Term.one _ (by
      show a.deg + (TM.Term.one).deg ≤ 2 * ((1 + a.deg + b.deg) + (W139).deg) + 7
      show a.deg + 3 ≤ 2 * ((1 + a.deg + b.deg) + 6) + 7
      omega)]
    exact h2
  rw [lt_eq_ltF_succ]
  show (if ((phi a b : Term) == W139) = true then false
        else if (a == TM.Term.one) = true then
          ltF (2 * ((phi a b).deg + (W139).deg) + 7) b (Z zero)
        else if ltF (2 * ((phi a b).deg + (W139).deg) + 7) a TM.Term.one = true then
          ltF (2 * ((phi a b).deg + (W139).deg) + 7) b W139
        else ((phi a b : Term) == Z zero
              || ltF (2 * ((phi a b).deg + (W139).deg) + 7) (phi a b) (Z zero))) = _
  rw [if_neg (by rw [hne]; exact Bool.noConfusion),
    if_neg (by rw [h1]; exact Bool.noConfusion),
    if_neg (by rw [h2']; exact Bool.noConfusion),
    show ((phi a b : Term) == Z zero) = false from rfl, Bool.false_or]
  exact (lt_eq_ltF (phi a b) (Z zero) _ (by
    show (1 + a.deg + b.deg) + (1 + (zero : Term).deg)
      ≤ 2 * ((1 + a.deg + b.deg) + (W139).deg) + 7
    show (1 + a.deg + b.deg) + (1 + 1) ≤ 2 * ((1 + a.deg + b.deg) + 6) + 7
    omega)).symm

/-- `lt (Z b) W139 = true` は `b = 0` に限る。 -/
theorem lt_Z_W148 : ∀ {b : Term}, lt (Z b) W139 = true → b = zero := by
  intro b h
  cases hq : ((Z b : Term) == Z zero) with
  | true =>
    have he : (Z b : Term) = Z zero := of_decide_eq_true hq
    injection he
  | false =>
    exfalso
    rw [lt_eq_ltF_succ] at h
    rw [show ltF (2 * ((Z b).deg + (W139).deg) + 7 + 1) (Z b) W139
          = (((Z b : Term) == TM.Term.one) || ((Z b : Term) == Z zero)
             || ltF (2 * ((Z b).deg + (W139).deg) + 7) (Z b) TM.Term.one
             || ltF (2 * ((Z b).deg + (W139).deg) + 7) (Z b) (Z zero)) from rfl,
      show ((Z b : Term) == TM.Term.one) = false from rfl, hq,
      show ltF (2 * ((Z b).deg + (W139).deg) + 7) (Z b) TM.Term.one
          = lt (Z b) TM.Term.one from (lt_eq_ltF (Z b) TM.Term.one _ (by
            show (1 + b.deg) + 3 ≤ 2 * ((1 + b.deg) + 6) + 7
            omega)).symm,
      lt_Z_one148 b,
      show ltF (2 * ((Z b).deg + (W139).deg) + 7) (Z b) (Z zero)
          = lt (Z b) (Z zero) from (lt_eq_ltF (Z b) (Z zero) _ (by
            show (1 + b.deg) + (1 + 1) ≤ 2 * ((1 + b.deg) + 6) + 7
            omega)).symm,
      lt_Z_Om102 b] at h
    exact Bool.noConfusion h

/-! ### §148.2 THE GAP IS EMPTY — 𝔗(M) has no term between the ψ₁-tower and `φ̄(1,Ω)` -/

/-- **主補題。**  `inT` な項が `W139 = φ̄(1,Ω)` より下なら、`TW` の塔のどれかより真に下。
    仮説なし。`TW` は §69.4b の `TW 0 = Ω⊕Ω`, `TW (j+1) = φ̄(0, TW j)`。 -/
theorem gapW148 : ∀ (n : Nat) (t : Term), t.deg ≤ n → inT t = true →
    lt t W139 = true → ∃ j, lt t (TW (j + 1)) = true
  | 0, t, h, _, _ => absurd h (by have := deg_pos t; omega)
  | n + 1, t, h, hi, hl => by
    cases t with
    | zero => exact ⟨0, rfl⟩
    | M => exact absurd hl (by rw [show lt M W139 = false from rfl]; exact Bool.noConfusion)
    | omg x => exact absurd hl (by rw [lt_omg_W148]; exact Bool.noConfusion)
    | Z b =>
      have hb : b = zero := lt_Z_W148 hl
      subst hb
      exact ⟨0, rfl⟩
    | psi k a =>
      have hl' : lt (psi k a) (phi TM.Term.one (Z zero)) = true := hl
      rw [lt_psi_phi_eq102 k a TM.Term.one (Z zero),
        show ((psi k a : Term) == TM.Term.one) = false from rfl,
        show ((psi k a : Term) == Z zero) = false from rfl,
        lt_psi_one139 k a, Bool.false_or, Bool.false_or, Bool.false_or] at hl'
      exact ⟨0, lt_trans_inT hi (show inT (Z zero) = true from rfl) (inT_TW 1) hl'
        (show lt (Z zero) (TW 1) = true from rfl)⟩
    | add p q =>
      rw [lt_add_ap102 p q (show isAP W139 = true from rfl)] at hl
      obtain ⟨_, hip, _, _⟩ := inT_add hi
      have hdq := deg_pos q
      have hde : (add p q).deg = 1 + p.deg + q.deg := rfl
      obtain ⟨j, hj⟩ := gapW148 n p (by omega) hip hl
      exact ⟨j, by rw [lt_add_ap102 p q (show isAP (TW (j + 1)) = true from rfl)]; exact hj⟩
    | phi a b =>
      obtain ⟨hia, hib⟩ := inT_phi hi
      have hda := deg_pos a
      have hdb := deg_pos b
      have hde : (phi a b).deg = 1 + a.deg + b.deg := rfl
      rcases lt_trichotomy_inT hia (show inT TM.Term.one = true from rfl) with
        ⟨hlt, _, _⟩ | ⟨_, heq, _⟩ | ⟨hf, hne, _⟩
      · have ha0 : a = zero := lt_one_zero148 n a (by omega) hia hlt
        subst ha0
        have hl' : lt b W139 = true := by
          show lt b (phi TM.Term.one (Z zero)) = true
          rw [← lt_phi_zero_one b (Z zero)]; exact hl
        obtain ⟨j, hj⟩ := gapW148 n b (by omega) hib hl'
        refine ⟨j + 1, ?_⟩
        show lt (phi zero b) (phi zero (TW (j + 1))) = true
        rw [lt_phi_same139]; exact hj
      · subst heq
        have hl' : lt b (Z zero) = true := by
          rw [← lt_phi_same139 TM.Term.one b (Z zero)]; exact hl
        have h1 : lt (phi TM.Term.one b) (Z zero) = true := by
          rw [lt_phi_Z103, show lt TM.Term.one (Z zero) = true from rfl, hl']; rfl
        exact ⟨0, lt_trans_inT hi (show inT (Z zero) = true from rfl) (inT_TW 1) h1
          (show lt (Z zero) (TW 1) = true from rfl)⟩
      · have hne' : (a == TM.Term.one) = false := by
          cases hq : ((a : Term) == TM.Term.one) with
          | false => rfl
          | true => exact absurd (of_decide_eq_true hq) hne
        rw [lt_phi_W_hi148 hne' hf] at hl
        exact ⟨0, lt_trans_inT hi (show inT (Z zero) = true from rfl) (inT_TW 1) hl
          (show lt (Z zero) (TW 1) = true from rfl)⟩

/-- 使いやすい形。 -/
theorem gapW147' {t : Term} (hi : inT t = true) (hl : lt t W139 = true) :
    ∃ j, lt t (TW (j + 1)) = true := gapW148 t.deg t (Nat.le_refl _) hi hl


/-! ## §148.2 THE BUCHHOLZ SIDE -/


/-! ### §148.2 The Buchholz side -/

theorem size_psiTow148 : ∀ m, BT.size (psiTow m) = m + 1
  | 0 => rfl
  | m + 1 => by
      show 1 + BT.size (psiTow m) = m + 1 + 1
      rw [size_psiTow148 m]
      omega

/-- 塔の項は段が違えば別の項。`==` の側で言う (BT の `BEq` は導出されたもの)。 -/
theorem psiTow_ne148 : ∀ (k d : Nat), (psiTow k == psiTow (d + k + 1)) = false
  | 0, d => rfl
  | k + 1, d => by
      show ((1 == 1) && (psiTow k == psiTow (d + k + 1))) = false
      rw [psiTow_ne148 k d]
      rfl

theorem btltL_psiTow148 : ∀ (k d f : Nat), k + 2 ≤ f →
    BT.ltL f (BT.toL (psiTow k)) (BT.toL (psiTow (d + k + 1))) = true
  | 0, d, f, hf => by
      cases f with
      | zero => exact absurd hf (by omega)
      | succ g => rfl
  | k + 1, d, f, hf => by
      cases f with
      | zero => exact absurd hf (by omega)
      | succ g =>
        show (if 1 < 1 then true else if 1 < 1 then false
              else if (psiTow k == psiTow (d + k + 1)) = true then BT.ltL g [] []
              else BT.ltL g (BT.toL (psiTow k)) (BT.toL (psiTow (d + k + 1)))) = true
        rw [if_neg (by omega), if_neg (by omega),
          if_neg (by rw [psiTow_ne148 k d]; exact Bool.noConfusion)]
        exact btltL_psiTow148 k d g (by omega)

theorem btlt_psiTow148 (k d : Nat) : BT.lt (psiTow k) (psiTow (d + k + 1)) = true := by
  show BT.ltL (BT.size (psiTow k) + BT.size (psiTow (d + k + 1)) + 2)
    (BT.toL (psiTow k)) (BT.toL (psiTow (d + k + 1))) = true
  exact btltL_psiTow148 k d _ (by rw [size_psiTow148, size_psiTow148]; omega)

theorem gb_psiTow148 : ∀ m, (BT.GB 1 (psiTow m)).all (fun e => BT.lt e (psiTow m)) = true
  | 0 => rfl
  | m + 1 => by
    have hgb : BT.GB 1 (psiTow (m + 1)) = psiTow m :: BT.GB 1 (psiTow m) := rfl
    have hstep : BT.lt (psiTow m) (psiTow (m + 1)) = true := by
      have hx := btlt_psiTow148 m 0
      rw [Nat.zero_add] at hx
      exact hx
    rw [hgb, List.all_eq_true]
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · rw [h]; exact hstep
    · exact lt_trans83 ((List.all_eq_true.mp (gb_psiTow148 m)) x h) hstep

theorem isStd_psiTow148 : ∀ m, BT.isStd (psiTow m) = true
  | 0 => rfl
  | m + 1 => by
    show (BT.isStd (psiTow m) && (BT.GB 1 (psiTow m)).all (fun e => BT.lt e (psiTow m))) = true
    rw [isStd_psiTow148 m, gb_psiTow148 m]; rfl

theorem isStd_Om2_148 : BT.isStd (BT.Om 2) = true := rfl
theorem isStd_D1Om2_148 : BT.isStd (BT.D 1 (BT.Om 2)) = true := rfl

/-- `ψ₁(x)` は Buchholz の順序でつねに `Ω₂` の下。 -/
theorem btlt_D1_Om2_148 (x : BT) : BT.lt (BT.D 1 x) (BT.Om 2) = true := by
  show BT.ltL (BT.size (BT.D 1 x) + BT.size (BT.Om 2) + 2)
    (BT.toL (BT.D 1 x)) (BT.toL (BT.Om 2)) = true
  rw [show BT.size (BT.D 1 x) + BT.size (BT.Om 2) + 2 = (BT.size x + 4) + 1 from by
    show (1 + BT.size x) + (1 + 1) + 2 = BT.size x + 4 + 1; omega]
  rfl

/-- 段 1 以下の塔はどれも `ψ₁(Ω₂)` の下。 -/
theorem btlt_psiTow_D1Om2_148 (m : Nat) :
    BT.lt (psiTow (m + 2)) (BT.D 1 (BT.Om 2)) = true := by
  show BT.ltL (BT.size (psiTow (m + 2)) + BT.size (BT.D 1 (BT.Om 2)) + 2)
    (BT.toL (psiTow (m + 2))) (BT.toL (BT.D 1 (BT.Om 2))) = true
  rw [show BT.size (psiTow (m + 2)) + BT.size (BT.D 1 (BT.Om 2)) + 2
        = (BT.size (psiTow (m + 1)) + 4) + 2 from by
      rw [show BT.size (psiTow (m + 2)) = 1 + BT.size (psiTow (m + 1)) from rfl]
      show 1 + BT.size (psiTow (m + 1)) + (1 + (1 + 1)) + 2 = _; omega]
  rfl


/-! ## §148.3 THE MAIN THEOREM — THE SLOT FOR `ψ₁(Ω₂)` DOES NOT EXIST -/

theorem inT_W148 : inT W139 = true := rfl

/-- **§148 の主定理。**  段 1 以下の塔を今の `dict` のまま残し、標準な項の上で
    Buchholz の順序を保つ写像は、`Ω₂` の像を `φ̄(1,Ω)` 以下に置けない。
    **compositional かどうかは一切問うていない** — route (b) も route (c) も
    「`ψ₁` の節をどう書くか」の話なので、どちらもこの定理の下にある。 -/
theorem noSlot148 (f : BT → Term)
    (hinT : ∀ x, BT.isStd x = true → inT (f x) = true)
    (hmono : ∀ x y, BT.isStd x = true → BT.isStd y = true →
        BT.lt x y = true → lt (f x) (f y) = true)
    (hlvl1 : ∀ m, f (psiTow (m + 2)) = TW (m + 1))
    (hOm2 : le (f (BT.Om 2)) W139 = true) : False := by
  have hgT : inT (f (BT.D 1 (BT.Om 2))) = true := hinT _ isStd_D1Om2_148
  have hOT : inT (f (BT.Om 2)) = true := hinT _ isStd_Om2_148
  have h1 : lt (f (BT.D 1 (BT.Om 2))) (f (BT.Om 2)) = true :=
    hmono _ _ isStd_D1Om2_148 isStd_Om2_148 (btlt_D1_Om2_148 (BT.Om 2))
  have hgW : lt (f (BT.D 1 (BT.Om 2))) W139 = true := by
    have hOm2' : ((f (BT.Om 2) == W139) || lt (f (BT.Om 2)) W139) = true := hOm2
    rcases (Bool.or_eq_true _ _).mp hOm2' with he | hlt
    · have hE : f (BT.Om 2) = W139 := of_decide_eq_true he
      rw [← hE]; exact h1
    · exact lt_trans_inT hgT hOT inT_W148 h1 hlt
  obtain ⟨j, hj⟩ := gapW147' hgT hgW
  have h2 : lt (TW (j + 1)) (f (BT.D 1 (BT.Om 2))) = true := by
    have hx := hmono (psiTow (j + 2)) (BT.D 1 (BT.Om 2)) (isStd_psiTow148 _) isStd_D1Om2_148
      (btlt_psiTow_D1Om2_148 j)
    rw [hlvl1 j] at hx
    exact hx
  rw [lt_asymm_inT (inT_TW (j + 1)) hgT h2] at hj
  exact Bool.noConfusion hj

/-- 同じことを正の形で。`Ω₂` の像は `φ̄(1,Ω)` より**真に上**でなければならない。 -/
theorem OmTwo_gt_W148 (f : BT → Term)
    (hinT : ∀ x, BT.isStd x = true → inT (f x) = true)
    (hmono : ∀ x y, BT.isStd x = true → BT.isStd y = true →
        BT.lt x y = true → lt (f x) (f y) = true)
    (hlvl1 : ∀ m, f (psiTow (m + 2)) = TW (m + 1)) :
    lt W139 (f (BT.Om 2)) = true := by
  rcases lt_trichotomy_inT inT_W148 (hinT _ isStd_Om2_148) with
    ⟨h1, _, _⟩ | ⟨_, h2, _⟩ | ⟨_, _, h3⟩
  · exact h1
  · exact absurd (noSlot148 f hinT hmono hlvl1
      (by rw [← h2]; show ((W139 == W139) || lt W139 W139) = true; rfl)) (fun h => h)
  · exact absurd (noSlot148 f hinT hmono hlvl1
      (by show ((f (BT.Om 2) == W139) || lt (f (BT.Om 2)) W139) = true
          rw [h3]; exact Bool.or_true _)) (fun h => h)

/-! ### §148.3.1 何が奪われるか — `collapse 0` の側 -/

/-- §140 が行 37 に名指した値は、ちょうど `φ̄(1,Ω)` の `collapse 0` である。 -/
theorem collapse0_W148 : collapse 0 W139 = corr37_140 := rfl

/-- 今の `dict` は `hlvl1` を満たす (§139 の定理そのもの)。 -/
theorem dict_hlvl1_148 : ∀ m, dict (psiTow (m + 2)) = TW (m + 1) := dict_psiTow139

/-- そして `hOm2` を外すことで `noSlot148` を逃れている。`dict (Ω₂) = Z 1` は
    `φ̄(1,Ω)` より真に上。 -/
theorem dict_Om2_148 : dict (BT.Om 2) = Z TM.Term.one := rfl
theorem dict_Om2_gt_W148 : lt W139 (dict (BT.Om 2)) = true := rfl
theorem dict_Om2_not_le_W148 : le (dict (BT.Om 2)) W139 = false := rfl

/-- route (b) の `dictB143` は逆に `hOm2` を満たす — だから `hmono` を外すしかない。
    §143 の `collision143` はその外し方の一つ。 -/
theorem dictB143_Om2_148 : dictB143 (BT.Om 2) = W139 := rfl
theorem dictB143_le_W148 : le (dictB143 (BT.Om 2)) W139 = true := rfl

/-! ## §148.4 `dictC148` — ROUTE (c) PROTOTYPED

`dict` との違いは 2 節。`u ≥ 2` は route (b) と同じ規則、`D 1 a` で `a` が段 1 以下で
ないときだけ `collapse 1` を呼ばずに `nch` を使う。**`nch` が route (c) の自由度そのもの**
であり、`noSlot148` はどの `nch` でも駄目だと言っている。下はその測定版。 -/

def dC148 (nch : Term → Term) (rg : Nat → Term) : Nat → BT → Term
  | 0, _ => zero
  | fuel + 1, t =>
    (((rle143 (BT.toL t)).map fun p =>
        match p.1 with
        | .D u a =>
          if u = 0 then
            (List.replicate p.2 (collV143 rg 0 (dC148 nch rg fuel a))).foldr plus zero
          else if u = 1 then
            (if btLe72 1 a then
              (List.replicate p.2 (collV143 rg 1 (dC148 nch rg fuel a))).foldr plus zero
             else
              (List.replicate p.2 (nch (dC148 nch rg fuel a))).foldr plus zero)
          else
            phi (TM.Term.ofNat (u - 1))
              (plus (Z zero) (plus (sub1 (omegaNF (dC148 nch rg fuel a)))
                (TM.Term.ofNat (p.2 - 1))))
        | _ => zero).foldr plus zero)

def dictC148 (nch : Term → Term) (t : BT) : Term := dC148 nch reg (BT.size t + 1) t

/-- `nch` の候補。`nchId148` は route (b) そのもの (§143 の `dictB143` と同じ挙動)。 -/
def nchId148   : Term → Term := fun x => x
def nchPhi0148 : Term → Term := fun x => phi zero x
def nchDrop148 : Term → Term := fun x => match x with | phi _ y => phi zero y | _ => x
def nchArg148  : Term → Term := fun x => match x with | phi _ y => y | _ => x
def nchColl148 : Term → Term := fun x => collV143 reg 1 x
def nchOm148   : Term → Term := fun x => omegaNF (plus (Z zero) x)
def nchTW148   : Term → Term := fun _ => TW 5
def nchSum148  : Term → Term := fun x => plus x x

def nchs148 : List (Term → Term) :=
  [nchId148, nchPhi0148, nchDrop148, nchArg148, nchColl148, nchOm148, nchTW148, nchSum148]

/-- route (c) の既定版。`nchDrop148` は `φ̄(1,Ω) ↦ φ̄(0,Ω)` で、`W139` の下に落ちる
    唯一の自然な候補 — それでも塔に負ける。 -/
def dictCd148 : BT → Term := dictC148 nchDrop148
def oRC148 (m : BMS.Matrix) : Option Term :=
  if m.isEmpty then some TM.Term.zero
  else (Trans.Recal.oRB m).map (fun t => TM.Term.plus TM.Term.one (dictCd148 t))

/-! ### §148.4.1 測定 — どの `nch` も駄目で、駄目になり方はちょうど 2 通り

**すべて 8 個の `nch` について。**  段 1 以下の塔はどれも動かさず (行 1)、`Ω₂` の像は
どれも `φ̄(1,Ω)` (行 2)、行 37 の値はどれも §140 の値 (行 9)。そこまでは全部通る。
壊れるのは `ψ₁(Ω₂)` の席で、しかも**排他的に**壊れる:

    `lt (f (ψ₁Ω₂)) W139`     false false TRUE TRUE false false TRUE false
    塔の全段より上か           TRUE  TRUE  false false TRUE  TRUE  false TRUE

**片方が真なら他方は偽** — これが `gapW148` の測定版である。`W139` の下に入れた 3 つは
塔に負け (`nchDrop148`/`nchArg148` は添字 0 で即、`nchTW148` は添字 4 で)、
塔の上に置いた 5 つは `W139` の下に入らない (うち 3 つは `Ω₂` と同じ項になる)。 -/

#guard nchs148.length == 8
/-! 段 1 以下は 8 つとも今の `dict` のまま (`m ≤ 10`)。 -/
#guard (nchs148.map fun f =>
  ((List.range 11).all fun m => dictC148 f (psiTow (m + 2)) == TW (m + 1)))
  == List.replicate 8 true
/-! `Ω₂` の像は 8 つとも `φ̄(1,Ω)` (route (b) の要求)。 -/
#guard (nchs148.map fun f => (dictC148 f (BT.Om 2) == W139)) == List.replicate 8 true
/-! 行 37 の値は 8 つとも §140 の値。 -/
#guard (nchs148.map fun f => (dictC148 f (BT.D 0 (BT.Om 2)) == corr37_140))
  == List.replicate 8 true
/-! 像は 8 つとも 𝔗(M) の項。 -/
#guard (nchs148.map fun f => inT (dictC148 f (BT.D 1 (BT.Om 2)))) == List.replicate 8 true
/-! **席の条件その 1** — `W139` より真に下か。 -/
#guard (nchs148.map fun f => lt (dictC148 f (BT.D 1 (BT.Om 2))) W139)
  == [false, false, true, true, false, false, true, false]
/-! **席の条件その 2** — 塔の全段より真に上か。**1 と排他的**。 -/
#guard (nchs148.map fun f =>
  ((List.range 13).all fun j => lt (TW (j + 1)) (dictC148 f (BT.D 1 (BT.Om 2)))))
  == [true, true, false, false, true, true, false, true]
/-! 塔に負ける最初の添字。 -/
#guard (nchs148.map fun f =>
  ((List.range 13).filter fun j =>
    !(lt (TW (j + 1)) (dictC148 f (BT.D 1 (BT.Om 2))))).head?)
  == [none, none, some 0, some 0, none, none, some 4, none]
/-! `Ω₂` と同じ項になるのは 3 つ (§143 の `collision143` はその 1 つ)。 -/
#guard (nchs148.map fun f => (dictC148 f (BT.Om 2) == dictC148 f (BT.D 1 (BT.Om 2))))
  == [true, false, false, false, true, true, false, false]

/-! ### §148.4.2 既定版 `dictCd148` を §143 と同じ物差しで測る

`nchDrop148` (`φ̄(1,Ω) ↦ φ̄(0,Ω)`) は「`W139` の下に入る」側の代表。`dictB143` との比較:

    測るもの                       `dict`      `dictB143` (§143)   `dictCd148` (route c)
    allStd108 9992 個の一致          9992            9992                9992
    allStd143 11577 個の一致        11577             486                 325
    11577 個のうち `inT`            11577           11576               11565
    (A) アンカー 28 個                 28              19                  19
    順序の反転 lvl2/cD/cS           0/0/0     672/284/1993       454/175/1163
    単射の破れ lvl2/cD/cS           0/0/0        40/4/26            48/14/6
    表 60 行が昇順                    yes            yes                 **NO**

**route (c) は route (b) より悪い。**  反転の数は減るが、表そのものが昇順でなくなる。 -/

#guard allStd108.length == 9992
#guard (allStd108.countP fun z => dictCd148 z == dict z) == 9992
#guard allStd143.length == 11577
#guard (allStd143.countP fun z => btLe72 1 z) == 325
#guard (allStd143.countP fun z => dictCd148 z == dict z) == 325
#guard (allStd143.countP fun z => inT (dictCd148 z)) == 11565
#guard anchorsA143.length == 28
#guard (anchorsA143.countP fun p => dictCd148 p.1 == p.2) == 19
#guard (cntBad143 dictCd148 lvl2_143, cntBad143 dictCd148 cD143, cntBad143 dictCd148 cS143)
       == (454, 175, 1163)
#guard (cntInj143 dictCd148 lvl2_143, cntInj143 dictCd148 cD143, cntInj143 dictCd148 cS143)
       == (48, 14, 6)
#guard (cntBad143 dict lvl2_143, cntBad143 dict cD143, cntBad143 dict cS143) == (0, 0, 0)
#guard Rows.rows.length == 60
#guard (Rows.rows.countP fun r => (oRC148 r.m) == some r.t) == 37
#guard (Rows.rows.countP fun r => ((oRC148 r.m).map inT).getD false) == 60
/-! **表が昇順でなくなる。**  `dictB143` はここは通っていた。 -/
#guard ((Rows.rows.map fun r => ((oRC148 r.m).getD zero)).zip
        (Rows.rows.map fun r => ((oRC148 r.m).getD zero)).tail).all (fun p => lt p.1 p.2)
       == false

/-! ## §148.5 THE SLOT, MEASURED OVER §143's CANDIDATE POOL

`gapW148` は定理なので以下は根拠ではなく受領である。ただし最後の 2 行は違う —
そこは `collapse 0` の単調性を測っており、それは証明していない。 -/

/-- 「`ψ₁(Ω₂)` の席」の条件: `W139` より真に下で、塔の全段より真に上。 -/
def slotOK148 (x : Term) : Bool :=
  lt x W139 && (List.range 13).all fun j => lt (TW (j + 1)) x

#guard cands143.length == 18549
/-! **席は 1 つも無い。**  18549 個の候補のうち 0 個。 -/
#guard (cands143.countP fun x => slotOK148 x) == 0
/-! 走査は空振りではない — `W139` の下の候補は 3870 個ある。 -/
#guard (cands143.countP fun x => inT x && lt x W139) == 3870
/-! 行 37 の値を出す引数は 14 個 (§143.6.3 の再測)。そのどれも席ではない。 -/
#guard (cands143.countP fun x => collapse 0 x == corr37_140) == 14
#guard (cands143.countP fun x => collapse 0 x == corr37_140 && slotOK148 x) == 0

/-! **測定 — 行 37 は上がるしかない。**  `OmTwo_gt_W148` は `f (Ω₂)` が `φ̄(1,Ω)` より
真に上だと言う。`W139` より真に上の候補 14677 個のどれをとっても `collapse 0` は §140 の
行 37 の値を真に超える。例外 0 件。**`collapse 0` の単調性は証明していない**ので、
これは測定である。 -/
#guard (cands143.countP fun x => inT x && lt W139 x) == 14677
#guard (cands143.countP fun x => inT x && lt W139 x && !(lt corr37_140 (collapse 0 x))) == 0

/-! ## §148.6 THE ONE ESCAPE LEFT BELOW ROUTE (a), AND WHAT IT COSTS

`noSlot148` has four hypotheses.  `hinT` and `hmono` are what a dictionary IS.  `hOm2` is
what §140's row 37 asks for.  That leaves exactly one place to give: **`hlvl1` — re-map the
level-≤1 fragment itself**, compressing `ψ₁`'s whole range into a proper initial segment of
`(Ω, φ̄(1,Ω))` so that a slot opens above it.

That is not route (b) and not route (c); it rewrites `collapse 1`, hence every value the
level-≤1 fragment produces.  The price is measured here: **37 of the 60 published rows have a
level-≤1 Buchholz preimage**, and the first row that does not is index 37 — the very row the
repair is for.  The 19 `Trans/Dict.lean` (A) anchors that route (b) and route (c) both keep
(§143.3.3) are level-≤1 too.  So the escape costs the whole published table below row 37 and
every anchor that pins it, to buy one row.

Route (a) — widening `Term` so `Ω₂ = χ₀(1)` is nameable — is the only route that opens a slot
without moving the level-≤1 fragment, because it adds terms to the target rather than
re-shuffling the ones there. -/

#guard (Rows.rows.countP fun r => match Trans.Recal.oRB r.m with
        | some b => btLe72 1 b
        | none => r.m.isEmpty) == 37
#guard ((Rows.rows.zipIdx.filter fun p => match Trans.Recal.oRB p.1.m with
        | some b => !(btLe72 1 b)
        | none => false).map (·.2)).take 5 == [37, 38, 39, 40, 41]
#guard (anchorsA143.take 19).all (fun p => btLe72 1 p.1)
#guard (Rows.rows.countP fun r => (Trans.oR r.m) == some r.t) == 60

/-! ## §149 THE SECOND GATE: `XMono145` IS NOT A ROUTE, IT IS A CONSEQUENCE -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- §129 の `dictFacts129` は `private` なので同じものを組み直す。 -/
theorem dictFacts149 (Hp : PsiIdxOKStd172) {a : BT}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hsA : BT.isStd (BT.D 0 a) = true) :
    inT (dict a) = true ∧ lt (dict a) M = true ∧ PsiIdxOK 0 (dict a) := by
  have hba := (btLe72_D 1 0 a hbA).2
  have hia := inT_dict_of_std172 Hp a hba (isStd_of_D hsA)
  exact ⟨hia.1, hia.2, Hp 0 a (by omega) hba hsA⟩

/-- **§149.1 — `hiMono_rt1_129` の逆。**  最後の一歩の指数が等しいのに第二引数が
    増えないなら、`ψ₀` の値も増えない。仮定は第一の門だけで、`hi a < hi b` は要らない。 -/
theorem notLt_of_sameExp149 (Hp : PsiIdxOKStd172) {a b : BT}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hbB : btLe72 1 (BT.D 0 b) = true)
    (hsA : BT.isStd (BT.D 0 a) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (hWa : le (reg 1) (dict a) = true) (hWb : le (reg 1) (dict b) = true)
    (hfa : lastFire92 (dict a) = false) (hfb : lastFire92 (dict b) = false)
    (hse : sameExp145 a b = true) (hxo : xok145 a b = false) :
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = false := by
  obtain ⟨hia, hlaM, hpa⟩ := dictFacts149 Hp hbA hsA
  obtain ⟨hib, hlbM, hpb⟩ := dictFacts149 Hp hbB hsB
  rw [collapse0_hi89 (dict a) hia hlaM hpa hWa, collapse0_hi89 (dict b) hib hlbM hpb hWb]
  cases hla : lastStep129 (dict a) with
  | none =>
      have : sameExp145 a b = false := by unfold sameExp145; rw [hla]
      rw [this] at hse; exact Bool.noConfusion hse
  | some pa =>
      cases hlb : lastStep129 (dict b) with
      | none =>
          have : sameExp145 a b = false := by unfold sameExp145; rw [hla, hlb]
          rw [this] at hse; exact Bool.noConfusion hse
      | some pb =>
          have heq : sameExp145 a b = (pa.1 == pb.1) := by unfold sameExp145; rw [hla, hlb]
          rw [heq] at hse
          have hA : pa.1 = pb.1 := eq_of_beq hse
          have hxe : xok145 a b = lt pa.2 pb.2 := by unfold xok145; rw [hla, hlb]
          rw [hxe] at hxo
          have ha2 : accW89 (dict a) = phiNF pa.1 pa.2 := accW89_last129 hfa (by rw [hla])
          have hb2 : accW89 (dict b) = phiNF pa.1 pb.2 := by
            rw [hA]; exact accW89_last129 hfb (by rw [hlb])
          obtain ⟨hAf, hXf⟩ := lastStep_inT129 hia hlaM hpa
            (show lastStep129 (dict a) = some (pa.1, pa.2) from by rw [hla])
          obtain ⟨_, hYf⟩ := lastStep_inT129 hib hlbM hpb
            (show lastStep129 (dict b) = some (pb.1, pb.2) from by rw [hlb])
          rw [ha2, hb2]
          rcases lt_trichotomy_inT hXf.1 hYf.1 with h | h | h
          · rw [h.1] at hxo; exact Bool.noConfusion hxo
          · rw [h.2.1, lt_irrefl]
          · exact lt_asymm_inT (inT_phiNF hAf.1 hYf.1 hAf.2 hYf.2)
              (inT_phiNF hAf.1 hXf.1 hAf.2 hXf.2)
              (phiMono129 pa.1 pb.2 pa.2 hAf.1 hAf.2 hYf.1 hYf.2 hXf.1 hXf.2 h.2.2)

/-- **§149.2 — 第二の門は `XMono145` を含む。**  第一の門のもとで
    `HiMono89` から `XMono145` が出る。**つまり `XMono145` は「道」ではなく「帰結」**で、
    それを反証すれば二つの門が同時に倒れる。 -/
theorem xmono145_of_hiMono149 (Hp : PsiIdxOKStd172) (HM : HiMono89) : XMono145 := by
  intro a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hse
  cases hxo : xok145 a b with
  | true => rfl
  | false =>
      exfalso
      have h1 := HM a b hbA hbB hsA hsB hWa hWb hlt
      rw [notLt_of_sameExp149 Hp hbA hbB hsA hsB hWa hWb hfa hfb hse hxo] at h1
      exact Bool.noConfusion h1

/-- **§149.3 — 反証すれば二つの門が同時に倒れる。** -/
theorem gates_false_of_not_xmono149 (H : ¬ XMono145) : ¬ (PsiIdxOKStd172 ∧ HiMono89) :=
  fun ⟨Hp, HM⟩ => H (xmono145_of_hiMono149 Hp HM)

/-- **§149.4 — `VebRest129` からも `XMono145` が出る。**  同じ指数の組は、`closed129` が
    閉じるなら `hiMono_closed129` が、閉じないなら残る条項そのものが結論を渡す。 -/
theorem xmono145_of_vebRest129_149 (Hp : PsiIdxOKStd172) (H : VebRest129) : XMono145 := by
  intro a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hse
  cases hxo : xok145 a b with
  | true => rfl
  | false =>
      exfalso
      have hcon : lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true := by
        cases hcl : closed129 a b with
        | true => exact hiMono_closed129 Hp hbA hbB hsA hsB hWa hWb hfa hfb hcl
        | false => exact H a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hcl
      rw [notLt_of_sameExp149 Hp hbA hbB hsA hsB hWa hWb hfa hfb hse hxo] at hcon
      exact Bool.noConfusion hcon

/-- **§149.5 — 残る条項に同じ指数の組は一つも無い。**  `VebRest129` が成り立つなら、
    `closed129` が閉じない組の最後の指数は必ず食い違う。§145.6 の分割の片側は
    「別の道」ではなく**空**である。 -/
theorem noSameExpResid149 (Hp : PsiIdxOKStd172) (H : VebRest129) {a b : BT}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hbB : btLe72 1 (BT.D 0 b) = true)
    (hsA : BT.isStd (BT.D 0 a) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (hWa : le (reg 1) (dict a) = true) (hWb : le (reg 1) (dict b) = true)
    (hfa : lastFire92 (dict a) = false) (hfb : lastFire92 (dict b) = false)
    (hlt : lt (hiW89 (dict a)) (hiW89 (dict b)) = true) (hcl : closed129 a b = false) :
    sameExp145 a b = false := by
  cases hse : sameExp145 a b with
  | false => rfl
  | true =>
      exfalso
      have hx := xmono145_of_vebRest129_149 Hp H a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hse
      have hr : closed129 a b = true := by
        unfold closed129
        rw [rt1_of_145 hse hx]
        cases closed117 a b <;> rfl
      rw [hr] at hcl
      exact Bool.noConfusion hcl

/-- **§149.6 — §145.6 の分割は同値である。**  第一の門のもとで
    `VebRest129 ↔ XMono145 ∧ VebRestDiff145`。§145.6 は「⟸」だけだった。 -/
theorem vebRest129_iff149 (Hp : PsiIdxOKStd172) :
    VebRest129 ↔ (XMono145 ∧ VebRestDiff145) :=
  ⟨fun H => ⟨xmono145_of_vebRest129_149 Hp H, vebRestDiff143_of129 H⟩,
   fun ⟨H1, H2⟩ => vebRest129_of_xmono145 H1 H2⟩

#print axioms xmono145_of_vebRest129_149
#print axioms noSameExpResid149
#print axioms vebRest129_iff149

/-! ### §149.7 違う指数の半分は片側だけ -/

/-- 既定の枝は `φ̄` の形か `A` そのもの — どちらも `B < A` なら不動点の形。 -/
theorem fixSh_phiNFdefault149 {A B X : Term} (hB : lt B A = true) :
    FixSh129 B (phiNFdefault A X) := by
  unfold phiNFdefault
  split
  · rename_i hh
    exact Or.inl ⟨((Bool.and_eq_true _ _).mp hh).2, hB⟩
  · exact Or.inr ⟨A, X, rfl, hB⟩

/-- **§149.7 の芯 — `φ̄(A,X)` は `B < A` のどの `φ̄(B,·)` から見ても不動点の形。**
    `phiNF` の枝をぜんぶ見る。 -/
theorem fixSh_phiNF149 {A B X : Term} (hiA : inT A = true) (hiB : inT B = true)
    (hiX : inT X = true) (hB : lt B A = true) : FixSh129 B (phiNF A X) := by
  by_cases hfx : FixSh129 A X
  · rw [phiNF_fixSh129 hfx]
    rcases hfx with ⟨hsc, hlt⟩ | ⟨d, e, he, hlt⟩
    · exact Or.inl ⟨hsc, lt_trans_inT hiB hiA hiX hB hlt⟩
    · subst he
      exact Or.inr ⟨d, e, rfl, lt_trans_inT hiB hiA (inT_phi hiX).1 hB hlt⟩
  · rw [phiNF_notFix129 hfx]
    cases hs : splitFin X with
    | mk g m =>
      by_cases hm : m ≥ 1
      · by_cases hfg : FixSh129 A g
        · rw [phiNFsucc_val129 hs hm hfg]
          exact Or.inr ⟨A, plus g (ofNat (m - 1)), rfl, hB⟩
        · rw [phiNFsucc_def129 hs hfg]; exact fixSh_phiNFdefault149 hB
      · rw [phiNFsucc_lo129 hs hm]; exact fixSh_phiNFdefault149 hB

/-- `B < A` なら `φ̄(B, φ̄(A,X)) = φ̄(A,X)`。 -/
theorem phiNF_absorb149 {A B X : Term} (hiA : inT A = true) (hiB : inT B = true)
    (hiX : inT X = true) (hB : lt B A = true) : phiNF B (phiNF A X) = phiNF A X :=
  phiNF_fixSh129 (fixSh_phiNF149 hiA hiB hiX hB)

/-- 対の列が空でなければ最後の一歩はある。 -/
theorem lastStep_some149 {y : Term} (hy : inT y = true) (hW : le (reg 1) y = true) :
    ∃ p, lastStep129 y = some p := by
  have h := wcnf_fst_ne_nil81 hy hW
  cases hr : (wcnf (reg 1) (toList y)).1.reverse with
  | nil =>
      exfalso
      apply h
      have h2 := congrArg List.reverse hr
      rw [List.reverse_reverse] at h2
      exact h2
  | cons ac r =>
      cases hv : (r.reverse.foldl (stepF (reg 1) (baseOf 0))
              ((none : Option Term), (none : Option Term))).2 with
      | none =>
          refine ⟨(ac.1, plus (baseOf 0) (sub1 ac.2)), ?_⟩
          unfold lastStep129; rw [hr]; dsimp only; rw [hv]
      | some v =>
          refine ⟨(ac.1, plus v ac.2), ?_⟩
          unfold lastStep129; rw [hr]; dsimp only; rw [hv]

/-- 最後の一歩の指数が `a` の側で狭義に**大きい**か。 -/
def expDown149 (a b : BT) : Bool :=
  match lastStep129 (dict a), lastStep129 (dict b) with
  | some pa, some pb => lt pb.1 pa.1
  | _, _ => false

/-- 最後の一歩の指数が `a` の側で狭義に**小さい**か。 -/
def expUp149 (a b : BT) : Bool :=
  match lastStep129 (dict a), lastStep129 (dict b) with
  | some pa, some pb => lt pa.1 pb.1
  | _, _ => false

/-- **§149.7 の主定理 — `hiMono_rt2_129` の逆。**  最後の指数が `a` の側で大きく、
    経路 2 が閉じないなら `ψ₀` の値は増えない。`hi a < hi b` は使わない。 -/
theorem notLt_of_expDown149 (Hp : PsiIdxOKStd172) {a b : BT}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hbB : btLe72 1 (BT.D 0 b) = true)
    (hsA : BT.isStd (BT.D 0 a) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (hWa : le (reg 1) (dict a) = true) (hWb : le (reg 1) (dict b) = true)
    (hfa : lastFire92 (dict a) = false) (hfb : lastFire92 (dict b) = false)
    (hrt2 : rt2_129 a b = false) (hd : expDown149 a b = true) :
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = false := by
  obtain ⟨hia, hlaM, hpa⟩ := dictFacts149 Hp hbA hsA
  obtain ⟨hib, hlbM, hpb⟩ := dictFacts149 Hp hbB hsB
  rw [collapse0_hi89 (dict a) hia hlaM hpa hWa, collapse0_hi89 (dict b) hib hlbM hpb hWb]
  cases hla : lastStep129 (dict a) with
  | none =>
      exfalso
      have he : expDown149 a b = false := by unfold expDown149; rw [hla]
      rw [he] at hd; exact Bool.noConfusion hd
  | some pa =>
      cases hlb : lastStep129 (dict b) with
      | none =>
          exfalso
          have he : expDown149 a b = false := by unfold expDown149; rw [hla, hlb]
          rw [he] at hd; exact Bool.noConfusion hd
      | some pb =>
          have hdd : lt pb.1 pa.1 = true := by
            have he : expDown149 a b = lt pb.1 pa.1 := by unfold expDown149; rw [hla, hlb]
            rw [he] at hd; exact hd
          have hr : rt2_129 a b = lt (accW89 (dict a)) pb.2 := by unfold rt2_129; rw [hlb]
          rw [hr] at hrt2
          have ha2 : accW89 (dict a) = phiNF pa.1 pa.2 := accW89_last129 hfa (by rw [hla])
          have hb2 : accW89 (dict b) = phiNF pb.1 pb.2 := accW89_last129 hfb (by rw [hlb])
          obtain ⟨hAf, hXf⟩ := lastStep_inT129 hia hlaM hpa
            (show lastStep129 (dict a) = some (pa.1, pa.2) from by rw [hla])
          obtain ⟨hBf, hYf⟩ := lastStep_inT129 hib hlbM hpb
            (show lastStep129 (dict b) = some (pb.1, pb.2) from by rw [hlb])
          obtain ⟨hTi, hTW, _, _, _⟩ := accW89_facts (dict a) hia hlaM hpa hWa
          have hTM : lt (accW89 (dict a)) M = true :=
            lt_trans_inT hTi (inT_reg 1) inT_M hTW (ltM_reg 1)
          obtain ⟨hUi, _, _, _, _⟩ := accW89_facts (dict b) hib hlbM hpb hWb
          have habs : phiNF pb.1 (accW89 (dict a)) = accW89 (dict a) := by
            rw [ha2]; exact phiNF_absorb149 hAf.1 hBf.1 hXf.1 hdd
          have hfin : le (accW89 (dict b)) (accW89 (dict a)) = true := by
            rw [hb2, ← habs]
            rcases lt_trichotomy_inT hYf.1 hTi with h | h | h
            · exact le_of_lt (phiMono129 pb.1 pb.2 (accW89 (dict a))
                hBf.1 hBf.2 hYf.1 hYf.2 hTi hTM h.1)
            · rw [h.2.1]; exact le_self _
            · exfalso; rw [h.2.2] at hrt2; exact Bool.noConfusion hrt2
          rcases (Bool.or_eq_true _ _).mp hfin with he | hl
          · rw [eq_of_beq he, lt_irrefl]
          · exact lt_asymm_inT hUi hTi hl

/-! ### §149.8 三つに割れて、うち二つは必要条件 -/

/-- 残る条項に、最後の指数が `a` の側で狭義に大きい組は無い。 -/
def NoDownResid149 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lastFire92 (dict a) = false → lastFire92 (dict b) = false →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    closed129 a b = false → expDown149 a b = false

/-- 残る条項の、最後の指数が `a` の側で狭義に小さい半分。 -/
def VebRestUp149 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lastFire92 (dict a) = false → lastFire92 (dict b) = false →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    closed129 a b = false → expUp149 a b = true →
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true

theorem noDownResid_of_vebRest129_149 (Hp : PsiIdxOKStd172) (H : VebRest129) :
    NoDownResid149 := by
  intro a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hcl
  cases hd : expDown149 a b with
  | false => rfl
  | true =>
      exfalso
      have hsplit := Bool.or_eq_false_iff.mp
        (show ((closed117 a b || rt1_129 a b) || rt2_129 a b) = false from hcl)
      have h1 := H a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hcl
      rw [notLt_of_expDown149 Hp hbA hbB hsA hsB hWa hWb hfa hfb hsplit.2 hd] at h1
      exact Bool.noConfusion h1

theorem vebRestUp_of_vebRest129_149 (H : VebRest129) : VebRestUp149 :=
  fun a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hcl _ =>
    H a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hcl

/-- **§149.8 の主定理 — 三つ揃えば残る条項になる。** -/
theorem vebRest129_of_three149 (Hp : PsiIdxOKStd172) (H1 : XMono145) (H2 : NoDownResid149)
    (H3 : VebRestUp149) : VebRest129 := by
  intro a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hcl
  obtain ⟨hia, hlaM, hpa⟩ := dictFacts149 Hp hbA hsA
  obtain ⟨hib, hlbM, hpb⟩ := dictFacts149 Hp hbB hsB
  refine H3 a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hcl ?_
  have hsplit := Bool.or_eq_false_iff.mp
    (show ((closed117 a b || rt1_129 a b) || rt2_129 a b) = false from hcl)
  have hrt1 : rt1_129 a b = false := (Bool.or_eq_false_iff.mp hsplit.1).2
  have hd := H2 a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hcl
  have hse : sameExp145 a b = false := by
    cases hs : sameExp145 a b with
    | false => rfl
    | true =>
        exfalso
        have hx := H1 a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hs
        rw [rt1_of_145 hs hx] at hrt1
        exact Bool.noConfusion hrt1
  obtain ⟨pa, hla⟩ := lastStep_some149 hia hWa
  obtain ⟨pb, hlb⟩ := lastStep_some149 hib hWb
  have hseq : (pa.1 == pb.1) = false := by
    have he : sameExp145 a b = (pa.1 == pb.1) := by unfold sameExp145; rw [hla, hlb]
    rw [he] at hse; exact hse
  have hdd : lt pb.1 pa.1 = false := by
    have he : expDown149 a b = lt pb.1 pa.1 := by unfold expDown149; rw [hla, hlb]
    rw [he] at hd; exact hd
  have hup : expUp149 a b = lt pa.1 pb.1 := by unfold expUp149; rw [hla, hlb]
  rw [hup]
  obtain ⟨hAf, _⟩ := lastStep_inT129 hia hlaM hpa
    (show lastStep129 (dict a) = some (pa.1, pa.2) from by rw [hla])
  obtain ⟨hBf, _⟩ := lastStep_inT129 hib hlbM hpb
    (show lastStep129 (dict b) = some (pb.1, pb.2) from by rw [hlb])
  rcases lt_trichotomy_inT hAf.1 hBf.1 with h | h | h
  · exact h.1
  · exfalso; simp [h.2.1] at hseq
  · exfalso; rw [h.2.2] at hdd; exact Bool.noConfusion hdd

/-- **§149.8 の同値。**  第一の門のもとで、残る条項はちょうど三つに割れる。 -/
theorem vebRest129_iff3_149 (Hp : PsiIdxOKStd172) :
    VebRest129 ↔ (XMono145 ∧ NoDownResid149 ∧ VebRestUp149) :=
  ⟨fun H => ⟨xmono145_of_vebRest129_149 Hp H, noDownResid_of_vebRest129_149 Hp H,
             vebRestUp_of_vebRest129_149 H⟩,
   fun ⟨H1, H2, H3⟩ => vebRest129_of_three149 Hp H1 H2 H3⟩

#print axioms phiNF_absorb149
#print axioms lastStep_some149
#print axioms notLt_of_expDown149
#print axioms vebRest129_iff3_149

/-! ### §149.9 第四の経路 — 指数が上がる側は `φ̄` の吸収で閉じる -/

/-- **経路 3** — `a` の最後の指数が `b` の側より狭義に小さく、`a` の最後の一歩の
    第二引数が `b` の値より下。`closed117` の探索は要らない。 -/
def rt3_149 (a b : BT) : Bool :=
  match lastStep129 (dict a), lastStep129 (dict b) with
  | some pa, some pb => lt pa.1 pb.1 && lt pa.2 (accW89 (dict b))
  | _, _ => false

/-- **§149.9 の主定理 — 経路 3 が閉じる。** -/
theorem hiMono_rt3_149 (Hp : PsiIdxOKStd172) {a b : BT}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hbB : btLe72 1 (BT.D 0 b) = true)
    (hsA : BT.isStd (BT.D 0 a) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (hWa : le (reg 1) (dict a) = true) (hWb : le (reg 1) (dict b) = true)
    (hfa : lastFire92 (dict a) = false) (hfb : lastFire92 (dict b) = false)
    (h : rt3_149 a b = true) :
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true := by
  obtain ⟨hia, hlaM, hpa⟩ := dictFacts149 Hp hbA hsA
  obtain ⟨hib, hlbM, hpb⟩ := dictFacts149 Hp hbB hsB
  rw [collapse0_hi89 (dict a) hia hlaM hpa hWa, collapse0_hi89 (dict b) hib hlbM hpb hWb]
  cases hla : lastStep129 (dict a) with
  | none =>
      exfalso
      have he : rt3_149 a b = false := by unfold rt3_149; rw [hla]
      rw [he] at h; exact Bool.noConfusion h
  | some pa =>
      cases hlb : lastStep129 (dict b) with
      | none =>
          exfalso
          have he : rt3_149 a b = false := by unfold rt3_149; rw [hla, hlb]
          rw [he] at h; exact Bool.noConfusion h
      | some pb =>
          have he : rt3_149 a b = (lt pa.1 pb.1 && lt pa.2 (accW89 (dict b))) := by
            unfold rt3_149; rw [hla, hlb]
          rw [he] at h
          obtain ⟨hup, hx3⟩ := (Bool.and_eq_true _ _).mp h
          have ha2 : accW89 (dict a) = phiNF pa.1 pa.2 := accW89_last129 hfa (by rw [hla])
          have hb2 : accW89 (dict b) = phiNF pb.1 pb.2 := accW89_last129 hfb (by rw [hlb])
          obtain ⟨hAf, hXf⟩ := lastStep_inT129 hia hlaM hpa
            (show lastStep129 (dict a) = some (pa.1, pa.2) from by rw [hla])
          obtain ⟨hBf, hYf⟩ := lastStep_inT129 hib hlbM hpb
            (show lastStep129 (dict b) = some (pb.1, pb.2) from by rw [hlb])
          obtain ⟨hUi, hUW, _, _, _⟩ := accW89_facts (dict b) hib hlbM hpb hWb
          have hUM : lt (accW89 (dict b)) M = true :=
            lt_trans_inT hUi (inT_reg 1) inT_M hUW (ltM_reg 1)
          have habs : phiNF pa.1 (accW89 (dict b)) = accW89 (dict b) := by
            rw [hb2]; exact phiNF_absorb149 hBf.1 hAf.1 hYf.1 hup
          have hstep := phiMono129 pa.1 pa.2 (accW89 (dict b))
            hAf.1 hAf.2 hXf.1 hXf.2 hUi hUM hx3
          rw [habs] at hstep
          rw [ha2]; exact hstep

/-- **§149.9 の逆 — 指数が上がる側では経路 3 は必要でもある。** -/
theorem notLt_of_expUp149 (Hp : PsiIdxOKStd172) {a b : BT}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hbB : btLe72 1 (BT.D 0 b) = true)
    (hsA : BT.isStd (BT.D 0 a) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (hWa : le (reg 1) (dict a) = true) (hWb : le (reg 1) (dict b) = true)
    (hfa : lastFire92 (dict a) = false) (hfb : lastFire92 (dict b) = false)
    (hup : expUp149 a b = true) (h : rt3_149 a b = false) :
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = false := by
  obtain ⟨hia, hlaM, hpa⟩ := dictFacts149 Hp hbA hsA
  obtain ⟨hib, hlbM, hpb⟩ := dictFacts149 Hp hbB hsB
  rw [collapse0_hi89 (dict a) hia hlaM hpa hWa, collapse0_hi89 (dict b) hib hlbM hpb hWb]
  cases hla : lastStep129 (dict a) with
  | none =>
      exfalso
      have he : expUp149 a b = false := by unfold expUp149; rw [hla]
      rw [he] at hup; exact Bool.noConfusion hup
  | some pa =>
      cases hlb : lastStep129 (dict b) with
      | none =>
          exfalso
          have he : expUp149 a b = false := by unfold expUp149; rw [hla, hlb]
          rw [he] at hup; exact Bool.noConfusion hup
      | some pb =>
          have heu : expUp149 a b = lt pa.1 pb.1 := by unfold expUp149; rw [hla, hlb]
          rw [heu] at hup
          have he : rt3_149 a b = (lt pa.1 pb.1 && lt pa.2 (accW89 (dict b))) := by
            unfold rt3_149; rw [hla, hlb]
          rw [he, hup, Bool.true_and] at h
          have ha2 : accW89 (dict a) = phiNF pa.1 pa.2 := accW89_last129 hfa (by rw [hla])
          obtain ⟨hAf, hXf⟩ := lastStep_inT129 hia hlaM hpa
            (show lastStep129 (dict a) = some (pa.1, pa.2) from by rw [hla])
          obtain ⟨hTi, _, _, _, _⟩ := accW89_facts (dict a) hia hlaM hpa hWa
          obtain ⟨hUi, hUW, hUap, hUE, _⟩ := accW89_facts (dict b) hib hlbM hpb hWb
          have hUM : lt (accW89 (dict b)) M = true :=
            lt_trans_inT hUi (inT_reg 1) inT_M hUW (ltM_reg 1)
          have h1U : lt TM.Term.one (accW89 (dict b)) = true :=
            lt_of_lt_of_le3 (show FragR TM.Term.one = true from rfl)
              (inT_le_fragR _ inT_E81) (inT_le_fragR _ hUi)
              (show lt TM.Term.one E081 = true from rfl) hUE
          have hle : le (accW89 (dict b)) pa.2 = true := by
            rcases lt_trichotomy_inT hXf.1 hUi with h2 | h2 | h2
            · rw [h2.1] at h; exact Bool.noConfusion h
            · rw [h2.2.1]; exact le_self _
            · exact le_of_lt h2.2.2
          have hfin : le (accW89 (dict b)) (accW89 (dict a)) = true := by
            rw [ha2]
            exact le_phiNF_ge117 hUi hUap h1U hUM hAf.1 hAf.2 hXf.1 hXf.2 hle
          rcases (Bool.or_eq_true _ _).mp hfin with hq | hl
          · rw [eq_of_beq hq, lt_irrefl]
          · exact lt_asymm_inT hUi hTi hl

/-! ### §149.10 判定器 — 第二の門の非発火半分は `ψ₀` 抜きで決まる -/

/-- **三本の経路。**  §117 の探索も `collapse` も要らない。 -/
def decide149 (a b : BT) : Bool := rt1_129 a b || rt2_129 a b || rt3_149 a b

/-- **§149.10 の主定理 — `decide149` は結論そのものである。**  第一の門のもとで、
    最後の対が発火しない適格な組では `ψ₀(hi a) < ψ₀(hi b)` は `decide149` と**等しい**。
    `hi a < hi b` は使わない。 -/
theorem hiMono_eq_decide149 (Hp : PsiIdxOKStd172) {a b : BT}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hbB : btLe72 1 (BT.D 0 b) = true)
    (hsA : BT.isStd (BT.D 0 a) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (hWa : le (reg 1) (dict a) = true) (hWb : le (reg 1) (dict b) = true)
    (hfa : lastFire92 (dict a) = false) (hfb : lastFire92 (dict b) = false) :
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = decide149 a b := by
  obtain ⟨hia, hlaM, hpa⟩ := dictFacts149 Hp hbA hsA
  obtain ⟨hib, hlbM, hpb⟩ := dictFacts149 Hp hbB hsB
  cases hdec : decide149 a b with
  | true =>
      rcases (Bool.or_eq_true _ _).mp hdec with h1 | h3
      · rcases (Bool.or_eq_true _ _).mp h1 with hr1 | hr2
        · exact hiMono_rt1_129 Hp hbA hbB hsA hsB hWa hWb hfa hfb hr1
        · exact hiMono_rt2_129 Hp hbA hbB hsA hsB hWa hWb hfb hr2
      · exact hiMono_rt3_149 Hp hbA hbB hsA hsB hWa hWb hfa hfb h3
  | false =>
      have hsp := Bool.or_eq_false_iff.mp
        (show ((rt1_129 a b || rt2_129 a b) || rt3_149 a b) = false from hdec)
      have hr1 : rt1_129 a b = false := (Bool.or_eq_false_iff.mp hsp.1).1
      have hr2 : rt2_129 a b = false := (Bool.or_eq_false_iff.mp hsp.1).2
      have hr3 : rt3_149 a b = false := hsp.2
      obtain ⟨pa, hla⟩ := lastStep_some149 hia hWa
      obtain ⟨pb, hlb⟩ := lastStep_some149 hib hWb
      obtain ⟨hAf, _⟩ := lastStep_inT129 hia hlaM hpa
        (show lastStep129 (dict a) = some (pa.1, pa.2) from by rw [hla])
      obtain ⟨hBf, _⟩ := lastStep_inT129 hib hlbM hpb
        (show lastStep129 (dict b) = some (pb.1, pb.2) from by rw [hlb])
      rcases lt_trichotomy_inT hAf.1 hBf.1 with h | h | h
      · refine notLt_of_expUp149 Hp hbA hbB hsA hsB hWa hWb hfa hfb ?_ hr3
        show expUp149 a b = true
        have he : expUp149 a b = lt pa.1 pb.1 := by unfold expUp149; rw [hla, hlb]
        rw [he]; exact h.1
      · refine notLt_of_sameExp149 Hp hbA hbB hsA hsB hWa hWb hfa hfb ?_ ?_
        · have he : sameExp145 a b = (pa.1 == pb.1) := by unfold sameExp145; rw [hla, hlb]
          rw [he, h.2.1]; exact beq_self_eq_true _
        · have he : xok145 a b = lt pa.2 pb.2 := by unfold xok145; rw [hla, hlb]
          have he2 : rt1_129 a b = ((pa.1 == pb.1) && lt pa.2 pb.2) := by
            unfold rt1_129; rw [hla, hlb]
          rw [he2, h.2.1, beq_self_eq_true, Bool.true_and] at hr1
          rw [he]; exact hr1
      · refine notLt_of_expDown149 Hp hbA hbB hsA hsB hWa hWb hfa hfb hr2 ?_
        have he : expDown149 a b = lt pb.1 pa.1 := by unfold expDown149; rw [hla, hlb]
        rw [he]; exact h.2.2

/-- **§149.10 の系 — 第二の門の非発火半分は `ψ₀` 抜きの一文になる。** -/
def HiMonoDec149 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lastFire92 (dict a) = false → lastFire92 (dict b) = false →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true → decide149 a b = true

/-- `VebRest117` は `HiMonoDec149` から出る — `closed129` も `closed117` も経由しない。 -/
theorem vebRest117_of_dec149 (Hp : PsiIdxOKStd172) (H : HiMonoDec149) : VebRest117 := by
  intro a b hbA hbB hsA hsB hWa hWb hfa hfb hlt _
  rw [hiMono_eq_decide149 Hp hbA hbB hsA hsB hWa hWb hfa hfb]
  exact H a b hbA hbB hsA hsB hWa hWb hfa hfb hlt

/-- 逆向き — `VebRest117` があれば判定器は必ず当たる。**分割ではなく同値。** -/
theorem dec147_of_vebRest117 (Hp : PsiIdxOKStd172) (H : VebRest117) : HiMonoDec149 := by
  intro a b hbA hbB hsA hsB hWa hWb hfa hfb hlt
  rw [← hiMono_eq_decide149 Hp hbA hbB hsA hsB hWa hWb hfa hfb]
  cases hc : closed117 a b with
  | true => exact hiMono_closed117 Hp hbA hbB hsA hsB hWa hWb hc
  | false => exact H a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hc

#print axioms hiMono_rt3_149
#print axioms notLt_of_expUp149
#print axioms hiMono_eq_decide149
#print axioms vebRest117_of_dec149

/-- **§149.11 — 第二の門ぜんぶを `ψ₀` 抜きの一文に架け替える。**  §120 の他の二本
    (`IdxLeMix109`・`VebIngF114`) はそのまま。 -/
theorem hiMono_of_dec149 (Hp : PsiIdxOKStd172) (HB : IdxLeMix109) (H1 : VebIngF114)
    (H : HiMonoDec149) : HiMono89 :=
  hiMono_of_three120 Hp HB H1 (vebRest117_of_dec149 Hp H)

/-- **逆向き — 判定器の条項は第二の門の帰結。**  だから反証すれば門が倒れる。 -/
theorem dec147_of_hiMono149 (Hp : PsiIdxOKStd172) (HM : HiMono89) : HiMonoDec149 := by
  intro a b hbA hbB hsA hsB hWa hWb hfa hfb hlt
  rw [← hiMono_eq_decide149 Hp hbA hbB hsA hsB hWa hWb hfa hfb]
  exact HM a b hbA hbB hsA hsB hWa hWb hlt

/-- **§149.11 の系 — 判定器を外す組が一つ出れば二つの門が同時に倒れる。** -/
theorem gates_false_of_not_dec149 (H : ¬ HiMonoDec149) : ¬ (PsiIdxOKStd172 ∧ HiMono89) :=
  fun ⟨Hp, HM⟩ => H (dec147_of_hiMono149 Hp HM)

#print axioms hiMono_of_dec149
#print axioms dec147_of_hiMono149

#print axioms notLt_of_sameExp149
#print axioms xmono145_of_hiMono149
#print axioms gates_false_of_not_xmono149

end

/-! ## §149.12 MEASUREMENT (frozen) — an attack on `XMono145`, now that it is a CONSEQUENCE

§149.2 makes `XMono145` a consequence of the two gates, so a single counterexample voids
every conditional theorem in `RegionNext3`-`RegionNext9`.  This section builds the family the
mechanism of §101/§133 asks for — a left term whose LAST base-`Ω₁` coefficient is smuggled
through a `ψ₀` node, against a right term with a taller prefix — and counts.

`pw149 k` is `Ω₁^(k+1)` (coefficient 1); `cp149 k e` is `Ω₁^(k+1)·ω^(ψ₀ e)`, i.e. the
same power with a coefficient of any size hidden inside one `ψ₀` node.  `epool149` walks the
`ψ₀` argument up to the ceiling `K`-standardness allows. -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

def sm149 : List BT → BT
  | [] => BT.zero
  | [x] => x
  | x :: r => BT.sum x (sm149 r)
def w0149 : BT := BT.D 1 BT.zero
def pw149 (k : Nat) : BT :=
  if k == 0 then w0149 else BT.D 1 (sm149 (List.replicate k w0149))
def cp149 (k : Nat) (e : BT) : BT :=
  if k == 0 then BT.D 1 (BT.D 0 e)
  else BT.D 1 (sm149 (List.replicate k w0149 ++ [BT.D 0 e]))

/-- `XMono145` の仮定をぜんぶ満たすか。 -/
def qual149 (a : BT) : Bool :=
  btLe72 1 (BT.D 0 a) && BT.isStd (BT.D 0 a) && le (reg 1) (dict a) && !(lastFire92 (dict a))
/-- 左辺の `K` 標準性だけを外した版 — §101 の対はここに居る。対照群。 -/
def qualNoK149 (a : BT) : Bool :=
  btLe72 1 (BT.D 0 a) && BT.isStd a && le (reg 1) (dict a) && !(lastFire92 (dict a))

def dt149 (a : BT) : Term × Option (Term × Term) := (hiW89 (dict a), lastStep129 (dict a))
def sameE149 (x y : Term × Option (Term × Term)) : Bool :=
  match x.2, y.2 with | some pa, some pb => pa.1 == pb.1 | _, _ => false
def xokd149 (x y : Term × Option (Term × Term)) : Bool :=
  match x.2, y.2 with | some pa, some pb => lt pa.2 pb.2 | _, _ => false

/-- (組の総数, `hi a < hi b` の組, そのうち最後の指数が等しい組, そのうち結論を外す組) -/
def cen149 (L R : List BT) : Nat × Nat × Nat × Nat :=
  let D := L.map dt149
  let E := R.map dt149
  let prs := D.flatMap (fun x => E.map (fun y => (x, y)))
  let fire := prs.filter (fun q => lt q.1.1 q.2.1)
  (prs.length, fire.length, fire.countP (fun q => sameE149 q.1 q.2),
   fire.countP (fun q => sameE149 q.1 q.2 && !(xokd149 q.1 q.2)))

def epool149 : List BT :=
  (List.range 5).map pw149 ++
  ((List.range 4).flatMap fun k => (List.range 4).map fun m =>
      sm149 (List.replicate (m+1) (pw149 (k+1)))) ++
  ((List.range 4).flatMap fun k => (List.range 4).map fun j =>
      sm149 [pw149 (k+1), pw149 j]) ++
  ((List.range 4).flatMap fun k => (List.range 3).flatMap fun m => (List.range 3).map fun j =>
      sm149 (List.replicate (m+1) (pw149 (k+1)) ++ [cp149 j BT.zero])) ++
  ((List.range 3).flatMap fun k => (List.range 3).flatMap fun m => (List.range 3).map fun j =>
      sm149 (List.replicate (m+1) (pw149 (k+1)) ++ [cp149 j (pw149 k)]))

/-- 二段の形 — `Ω₁^(k+1)·m ⊕ Ω₁^(j+1)·ω^(ψ₀ e)`。 -/
def fam2_149 : List BT :=
  ((List.range 4).flatMap fun k => (List.range 4).flatMap fun m =>
     (List.range 4).flatMap fun j => epool149.map fun e =>
        sm149 (List.replicate (m+1) (pw149 (k+1)) ++ [cp149 j e]))

/-- 三段の形 — 途中の歩を増やして、不動点で潰れる余地を作る。 -/
def fam3_149 : List BT :=
  ((List.range 3).flatMap fun k => (List.range 3).flatMap fun m =>
     (List.range 3).flatMap fun i => (List.range 3).flatMap fun j =>
       (List.range 8).map fun t =>
        sm149 (List.replicate (m+1) (pw149 (k+2)) ++ [pw149 (i+1)]
               ++ [cp149 j (epool149.getD t BT.zero)]))

/-! **母集団。**  7048 本、大きさ **114 記号**まで。§133.4 の 41、§145.5 の 75 を越える。 -/

#guard (epool149.length, fam2_149.length, fam3_149.length,
        ((fam2_149 ++ fam3_149).map BT.size).foldl max 0) == (100, 6400, 648, 114)

#guard ((fam2_149.filter qual149).length, (fam3_149.filter qual149).length,
        (fam2_149.filter qualNoK149).length) == (2095, 324, 3160)

/-! **`XMono145` はここでも一度も外れない。**  両辺が `K` 標準な 2419 本から
2,976,981 組が前提を満たし、そのうち **710,042 組**で最後の指数が等しく、
**そのぜんぶで `X_a < X_b`**。 -/

#guard cen149 (fam2_149.filter qual149) (fam2_149.filter qual149)
  == (4389025, 2193247, 585278, 0)
#guard cen149 (fam3_149.filter qual149) ((fam2_149 ++ fam3_149).filter qual149)
  == (783756, 458480, 124764, 0)

/-! **対照 — 掃きは空虚ではない。**  同じ族で左辺の `K` 標準性だけを外すと、
同じ指数の 1,120,316 組のうち **191,113 組が結論を外す**。担いでいるのは
その条項ひとつだけ、という §133 の言い分がこの大きさでも出る。 -/

#guard cen149 (fam2_149.filter qualNoK149) (fam2_149.filter qual149)
  == (6620200, 4099011, 1120316, 191113)

end

/-! ### §149.11 the decider sweep, run once and not frozen

`decide149` と実計算 `lt (ψ₀(hi a)) (ψ₀(hi b))` の突き合わせは別走行 (`m147d.lean`、
exit 0、53 分) で行い、**ここに凍結しない** — この掃きを `#guard` にすると毎回の
ビルドが 53 分延びる。数字: 106868 対で不一致 0 (`stdTab130` 8 の全対 77284 + 対角族
`dpool` 29584)。門の検査 `gateCen` は 4 母集団 (`dpool`+冪 178 項、`fm145` 90117 項の
うち 1111、`fam2/fam3/dpool` 2591、`stdTab130 13`+`pool136`+`famPool132` 16064 項) で
義務 0 破れ、最大 122 記号。file は当セッションの保管庫にある。 -/

/-! ## §150 THE 2-ARY χ, PROTOTYPED — CONSERVATIVITY IS A THEOREM AND THE COLLISIONS ARE GONE

`plan/chi-2ary.md`'s route (a), which §148 proved is the only route.  `Term2` carries
`Z2 a b` = χ_a(b); `lt2` implements [Rathjen 1990] 3.14 for χ-χ and computes κ⁻ through the
second argument; `inT2` adds 5.1(i)'s formation condition.  `lt_emb` proves the embedding
`Z a ↦ Z2 a 0` preserves and reflects the order — the migration cannot change any existing
order fact.  `dict2` with `reg2 (u+1) = χ_0(u)` is compositional (`dict2_sum` is `rfl`
again), agrees with `dict` under the renaming on every population tried, and §143's
collisions are refuted by `decide`.  Migration cost, measured: three clauses of `lt`, one
conjunct of `inT`, `kminus`'s successor clause, one case per `Z`-splitting lemma. -/

/-! ### §150.1 `Term2` — 𝔗₂(M): the term algebra with the 2-ary χ restored -/

/-- 𝔗(M) の項型の写しで、`Z` だけ 2 引数 (`Z2 a b` = χ_a(b))。ほかの構成子は
    `TM.Term` と同じ。`Z2 a TM0` が旧 `Z a` に当たる。 -/
inductive Term2 where
  | zero
  | M
  | add (a b : Term2)
  | omg (a : Term2)
  | phi (a b : Term2)
  | psi (k a : Term2)
  | Z2 (a b : Term2)
deriving DecidableEq, Repr

/-- 記号数 (燃料の上界)。`TM.Term.deg` の写し。 -/
def Term2.deg : Term2 → Nat
  | zero => 1
  | M => 1
  | add a b => 1 + a.deg + b.deg
  | omg a => 1 + a.deg
  | phi a b => 1 + a.deg + b.deg
  | psi k a => 1 + k.deg + a.deg
  | Z2 a b => 1 + a.deg + b.deg

def Term2.isAP : Term2 → Bool
  | zero => false
  | add _ _ => false
  | _ => true

def Term2.isSC : Term2 → Bool
  | M => true
  | psi _ _ => true
  | Z2 _ _ => true
  | _ => false

def Term2.isR : Term2 → Bool
  | Z2 _ _ => true
  | _ => false

def Term2.toList : Term2 → List Term2
  | zero => []
  | add a b => a :: toList b
  | t => [t]

def Term2.ofList : List Term2 → Term2
  | [] => zero
  | [a] => a
  | a :: rest => add a (ofList rest)

def Term2.one : Term2 := phi zero zero

/-- 後続 t = s+1 の s (後続でなければ引数のまま)。`TM.FS.predT` の形。 -/
def Term2.pred (d : Term2) : Term2 :=
  let l := toList d
  if l.getLast? == some one then ofList l.dropLast else d

mutual

/-- α* ([R91] 2.2 の写し; χ 項は SC なので `Z2` 節は恒等)。 -/
def Term2.starF : Nat → Term2 → Term2
  | 0, _ => zero
  | fuel + 1, t =>
    match t with
    | zero => zero
    | M => zero
    | add a b =>
      let x := starF fuel a
      let y := starF fuel b
      if ltF fuel x y then y else x
    | omg a => starF fuel a
    | phi a b =>
      let x := starF fuel a
      let y := starF fuel b
      if ltF fuel x y then y else x
    | psi k a => psi k a
    | Z2 a b => Z2 a b

/-- 順序の判定。[R91] 2.3 の写しに、χ–χ を [R90] 3.14 に差し替え、ψ–χ の π⁻ を
    第 2 引数対応 ((χ_γ(0))⁻ = γ*, (χ_γ(δ+1))⁻ = χ_γ(δ)) にしたもの。
    φ̄–χ は 2.3.4/2.3.5 のまま (χ_γ(δ) ∈ SC)。 -/
def Term2.ltF : Nat → Term2 → Term2 → Bool
  | 0, _, _ => false
  | fuel + 1, s, t =>
    if s == t then false else
    match s, t with
    | zero, _ => true
    | _, zero => false
    | add a b, add c d => if a == c then ltF fuel b d else ltF fuel a c
    | add a _, t' => ltF fuel a t'
    | s', add c _ => s' == c || ltF fuel s' c
    | M, omg _ => true
    | M, _ => false
    | omg _, M => false
    | _, M => true
    | omg g, omg d => ltF fuel g d
    | omg _, _ => false
    | _, omg _ => true
    | phi a b, phi c d =>
      if a == c then ltF fuel b d
      else if ltF fuel a c then ltF fuel b (phi c d)
      else phi a b == d || ltF fuel (phi a b) d
    | phi a b, t' => ltF fuel a t' && ltF fuel b t'
    | s', phi c d => s' == c || s' == d || ltF fuel s' c || ltF fuel s' d
    | psi k a, psi p b =>
      if k == p then ltF fuel a b
      else if ltF fuel k p then ltF fuel k (psi p b)
      else ltF fuel (psi k a) p
    | psi k a, Z2 c d =>
      if k == Z2 c d || ltF fuel k (Z2 c d) then true
      else
        let dm := if d == zero then starF fuel c else Z2 c (pred d)
        psi k a == dm || ltF fuel (psi k a) dm
    | Z2 c d, psi k a =>
      if k == Z2 c d || ltF fuel k (Z2 c d) then false
      else
        let dm := if d == zero then starF fuel c else Z2 c (pred d)
        ltF fuel dm (psi k a)
    | Z2 a b, Z2 c d =>
      if a == c then ltF fuel b d
      else if ltF fuel a c then
        (b == zero || ltF fuel b (Z2 c d)) && ltF fuel (starF fuel a) (Z2 c d)
      else
        (!(d == zero) && (Z2 a b == d || ltF fuel (Z2 a b) d))
          || (Z2 a b == starF fuel c || ltF fuel (Z2 a b) (starF fuel c))

end

def Term2.fuelOf (s t : Term2) : Nat := 2 * (s.deg + t.deg) + 8

/-- s < t -/
def Term2.lt (s t : Term2) : Bool := ltF (fuelOf s t) s t

/-- s ≤ t -/
def Term2.le (s t : Term2) : Bool := s == t || lt s t

/-- α* -/
def Term2.star (t : Term2) : Term2 := starF (2 * t.deg + 8) t

/-- κ⁻。**2 引数化で本当に新しい唯一の節**: (χ_γ(δ+1))⁻ = χ_γ(δ)。
    (χ_γ(0))⁻ = γ* は [R91] 2.3 の写し。 -/
def Term2.kminus : Term2 → Term2
  | Z2 c d => if d == zero then star c else Z2 c (pred d)
  | _ => zero

/-- K_κ ([R91] 2.2 の写し; `Z2` は両引数に潜るだけ — 2.2(vii) の形のまま)。 -/
def Term2.Kset (k : Term2) : Term2 → List Term2
  | zero => []
  | M => []
  | add a b => Kset k a ++ Kset k b
  | omg a => Kset k a
  | phi a b => Kset k a ++ Kset k b
  | psi p b =>
    if le (psi p b) (kminus k) then []
    else if lt p k then Kset k p
    else b :: (Kset k p ++ Kset k b)
  | Z2 a b => Kset k a ++ Kset k b

/-- 第 2 引数が後続か ([R90] 5.1(i) の「β+1」)。 -/
def Term2.isSucc (b : Term2) : Bool := (toList b).getLast? == some one

/-- 形成条件 ([R91] 2.1 の写し + [R90] 5.1(i): `Z2` の第 2 引数は 0 か後続)。 -/
def Term2.inT : Term2 → Bool
  | zero => true
  | M => true
  | add a b =>
    a.isAP && inT a && inT b &&
    (match b with
     | add c _ => le c a
     | _ => b.isAP && le b a)
  | omg a => inT a && lt M a
  | phi a b => inT a && inT b && lt a M && lt b M
  | psi k a =>
    k.isR && inT k && inT a && lt a M && (Kset k a).all (fun x => lt x a)
  | Z2 a b => inT a && inT b && lt b M && (b == zero || isSucc b)

/-! ### Normal operations ([R91] 2.6 and the `Trans/Dict.lean` §2 helpers, ported) -/

def Term2.plus (s t : Term2) : Term2 :=
  match toList t with
  | [] => s
  | b1 :: _ => ofList ((toList s).filter (fun a => le b1 a) ++ toList t)

def Term2.omega : Term2 := phi zero one

def Term2.ofNat : Nat → Term2
  | 0 => zero
  | n + 1 => plus (ofNat n) one

def Term2.splitFin (b : Term2) : Term2 × Nat :=
  let l := toList b
  let m := (l.reverse.takeWhile (· == one)).length
  (ofList (l.take (l.length - m)), m)

def Term2.phiNFdefault (a b : Term2) : Term2 :=
  if b == zero && a.isSC then a
  else phi a b

def Term2.phiNFsucc (a b : Term2) : Term2 :=
  let (g, m) := splitFin b
  if m ≥ 1 then
    let down := plus g (ofNat (m - 1))
    match g with
    | phi d _ => if lt a d then phi a down else phiNFdefault a b
    | _ => if g.isSC && lt a g then phi a down else phiNFdefault a b
  else phiNFdefault a b

def Term2.phiNF (a b : Term2) : Term2 :=
  if b.isSC && lt a b then b
  else
    match b with
    | phi c _ => if lt a c then b else phiNFsucc a b
    | _ => phiNFsucc a b

def Term2.omegaNF (a : Term2) : Term2 :=
  if lt M a then omg a
  else if a == M then M
  else phiNF zero a

def Term2.isFP (a g : Term2) : Bool :=
  (g.isSC && lt a g) ||
  (match g with
   | phi c _ => lt a c
   | _ => false)

def Term2.phiShifted (a b : Term2) : Bool :=
  isFP a (splitFin b).1 || (b == zero && a.isSC)

def Term2.logOm : Term2 → Term2
  | phi zero b => if phiShifted zero b then plus b one else b
  | t => t

def Term2.subAP (w h : Term2) : Term2 :=
  match toList h with
  | [] => zero
  | p :: rest => if p == w then ofList rest else h

def Term2.divAP (w p : Term2) : Term2 := omegaNF (subAP w (logOm p))

def Term2.mulL (w y : Term2) : Term2 :=
  ofList ((toList y).map (fun p => omegaNF (plus w (logOm p))))

def Term2.sub1 (c : Term2) : Term2 :=
  match toList c with
  | [] => zero
  | p :: rest => if p == one then ofList rest else c

def Term2.wcnf (w : Term2) : List Term2 → List (Term2 × Term2) × Term2
  | [] => ([], zero)
  | p :: rest =>
    if lt p w then ([], ofList (p :: rest))
    else
      let g := logOm p
      let l := toList g
      let a := ofList ((l.filter (fun q => !lt q w)).map (divAP w))
      let c := omegaNF (ofList (l.filter (fun q => lt q w)))
      match wcnf w rest with
      | ((a', c') :: ps, tl) =>
        if a == a' then ((a, plus c c') :: ps, tl) else ((a, c) :: (a', c') :: ps, tl)
      | ([], tl) => ([(a, c)], tl)

/-! ### §150.2 THE EMBEDDING AND CONSERVATIVITY — A THEOREM, NOT A SWEEP

`emb` is the literal reading `Z a ↦ χ_a(0)`.  `consv_aux` proves, by one induction on
the fuel, that `ltF`/`starF` and their `Term2` counterparts make EXACTLY the same
recursive calls on emb-images — 3.14 at β = δ = 0 IS 2.3.15, and the 2-ary π⁻ at
δ = 0 IS δ*.  `lt_emb` then removes the fuel with the Term-side `ltF_stable` only;
no `Term2`-side stability is needed. -/

section
open TM (Term)
open TM.Term
open Evidence.WF

/-- 字義通りの埋め込み: `Z a ↦ χ_a(0)`。 -/
def emb : Term → Term2
  | .zero => .zero
  | .M => .M
  | .add a b => .add (emb a) (emb b)
  | .omg a => .omg (emb a)
  | .phi a b => .phi (emb a) (emb b)
  | .psi k a => .psi (emb k) (emb a)
  | .Z a => .Z2 (emb a) .zero

/-- `emb` の引き込み (単射性のため)。 -/
def unemb : Term2 → Term
  | .zero => .zero
  | .M => .M
  | .add a b => .add (unemb a) (unemb b)
  | .omg a => .omg (unemb a)
  | .phi a b => .phi (unemb a) (unemb b)
  | .psi k a => .psi (unemb k) (unemb a)
  | .Z2 a _ => .Z (unemb a)

theorem unemb_emb : ∀ t : Term, unemb (emb t) = t
  | .zero => rfl
  | .M => rfl
  | .add a b => by
      show TM.Term.add (unemb (emb a)) (unemb (emb b)) = TM.Term.add a b
      rw [unemb_emb a, unemb_emb b]
  | .omg a => by
      show TM.Term.omg (unemb (emb a)) = TM.Term.omg a
      rw [unemb_emb a]
  | .phi a b => by
      show TM.Term.phi (unemb (emb a)) (unemb (emb b)) = TM.Term.phi a b
      rw [unemb_emb a, unemb_emb b]
  | .psi k a => by
      show TM.Term.psi (unemb (emb k)) (unemb (emb a)) = TM.Term.psi k a
      rw [unemb_emb k, unemb_emb a]
  | .Z a => by
      show TM.Term.Z (unemb (emb a)) = TM.Term.Z a
      rw [unemb_emb a]

theorem emb_inj {s t : Term} (h : emb s = emb t) : s = t := by
  have h2 := congrArg unemb h
  rwa [unemb_emb, unemb_emb] at h2

theorem emb_beq (s t : Term) : (emb s == emb t) = (s == t) := by
  cases hq : s == t with
  | true =>
    have h : s = t := of_decide_eq_true hq
    subst h
    exact beq_self_eq_true _
  | false =>
    cases hq2 : (emb s == emb t) with
    | false => rfl
    | true =>
      exfalso
      have h : s = t := emb_inj (of_decide_eq_true hq2)
      subst h
      exact Bool.noConfusion (hq.symm.trans (beq_self_eq_true _))

/-- **主補題 (保存性)。**  同じ燃料で `ltF` と `Term2.ltF` は emb 像の上で一致し、
    `starF` は emb と可換。3.14 の β = δ = 0 退化と π⁻ の δ = 0 退化を、
    節ごとの照合で言う。 -/
private theorem consv_aux : ∀ (f : Nat),
    (∀ (s t : Term), TM.Term.ltF f s t = Term2.ltF f (emb s) (emb t)) ∧
    (∀ (t : Term), Term2.starF f (emb t) = emb (TM.Term.starF f t))
  | 0 => ⟨fun _ _ => rfl, fun _ => rfl⟩
  | f + 1 => by
    obtain ⟨R, RS⟩ := consv_aux f
    constructor
    · intro s t
      cases s with
      | zero => cases t <;> rfl
      | M =>
        cases t with
        | zero => rfl
        | M => rfl
        | omg y => rfl
        | phi c d => rfl
        | psi p c => rfl
        | Z c => rfl
        | add c d =>
          show ((M : Term) == c || TM.Term.ltF f M c)
              = ((emb M == emb c) || Term2.ltF f (emb M) (emb c))
          rw [emb_beq M c, ← R M c]
      | add a b =>
        cases t with
        | zero => rfl
        | M => exact R a M
        | omg y => exact R a (omg y)
        | phi c d => exact R a (phi c d)
        | psi p c => exact R a (psi p c)
        | Z c => exact R a (Z c)
        | add c d =>
          show (if ((add a b : Term) == add c d) = true then false
                else if (a == c) = true then TM.Term.ltF f b d else TM.Term.ltF f a c)
              = (if (emb (add a b) == emb (add c d)) = true then false
                 else if (emb a == emb c) = true then Term2.ltF f (emb b) (emb d)
                 else Term2.ltF f (emb a) (emb c))
          rw [emb_beq (add a b) (add c d), emb_beq a c, ← R b d, ← R a c]
      | omg x =>
        cases t with
        | zero => rfl
        | M => rfl
        | phi c d => rfl
        | psi p c => rfl
        | Z c => rfl
        | add c d =>
          show ((omg x : Term) == c || TM.Term.ltF f (omg x) c)
              = ((emb (omg x) == emb c) || Term2.ltF f (emb (omg x)) (emb c))
          rw [emb_beq (omg x) c, ← R (omg x) c]
        | omg y =>
          show (if ((omg x : Term) == omg y) = true then false else TM.Term.ltF f x y)
              = (if (emb (omg x) == emb (omg y)) = true then false
                 else Term2.ltF f (emb x) (emb y))
          rw [emb_beq (omg x) (omg y), ← R x y]
      | phi a b =>
        cases t with
        | zero => rfl
        | M => rfl
        | omg y => rfl
        | add c d =>
          show ((phi a b : Term) == c || TM.Term.ltF f (phi a b) c)
              = ((emb (phi a b) == emb c) || Term2.ltF f (emb (phi a b)) (emb c))
          rw [emb_beq (phi a b) c, ← R (phi a b) c]
        | phi c d =>
          show (if ((phi a b : Term) == phi c d) = true then false
                else if (a == c) = true then TM.Term.ltF f b d
                else if TM.Term.ltF f a c = true then TM.Term.ltF f b (phi c d)
                else ((phi a b : Term) == d || TM.Term.ltF f (phi a b) d))
              = (if (emb (phi a b) == emb (phi c d)) = true then false
                 else if (emb a == emb c) = true then Term2.ltF f (emb b) (emb d)
                 else if Term2.ltF f (emb a) (emb c) = true then
                   Term2.ltF f (emb b) (emb (phi c d))
                 else ((emb (phi a b) == emb d) || Term2.ltF f (emb (phi a b)) (emb d)))
          rw [emb_beq (phi a b) (phi c d), emb_beq a c, emb_beq (phi a b) d,
              ← R b d, ← R a c, ← R b (phi c d), ← R (phi a b) d]
        | psi p c =>
          show (TM.Term.ltF f a (psi p c) && TM.Term.ltF f b (psi p c))
              = (Term2.ltF f (emb a) (emb (psi p c)) && Term2.ltF f (emb b) (emb (psi p c)))
          rw [← R a (psi p c), ← R b (psi p c)]
        | Z c =>
          show (TM.Term.ltF f a (Z c) && TM.Term.ltF f b (Z c))
              = (Term2.ltF f (emb a) (emb (Z c)) && Term2.ltF f (emb b) (emb (Z c)))
          rw [← R a (Z c), ← R b (Z c)]
      | psi k a =>
        cases t with
        | zero => rfl
        | M => rfl
        | omg y => rfl
        | add c d =>
          show ((psi k a : Term) == c || TM.Term.ltF f (psi k a) c)
              = ((emb (psi k a) == emb c) || Term2.ltF f (emb (psi k a)) (emb c))
          rw [emb_beq (psi k a) c, ← R (psi k a) c]
        | phi c d =>
          show ((psi k a : Term) == c || (psi k a : Term) == d
                || TM.Term.ltF f (psi k a) c || TM.Term.ltF f (psi k a) d)
              = ((emb (psi k a) == emb c) || (emb (psi k a) == emb d)
                 || Term2.ltF f (emb (psi k a)) (emb c) || Term2.ltF f (emb (psi k a)) (emb d))
          rw [emb_beq (psi k a) c, emb_beq (psi k a) d, ← R (psi k a) c, ← R (psi k a) d]
        | psi p b =>
          show (if ((psi k a : Term) == psi p b) = true then false
                else if (k == p) = true then TM.Term.ltF f a b
                else if TM.Term.ltF f k p = true then TM.Term.ltF f k (psi p b)
                else TM.Term.ltF f (psi k a) p)
              = (if (emb (psi k a) == emb (psi p b)) = true then false
                 else if (emb k == emb p) = true then Term2.ltF f (emb a) (emb b)
                 else if Term2.ltF f (emb k) (emb p) = true then
                   Term2.ltF f (emb k) (emb (psi p b))
                 else Term2.ltF f (emb (psi k a)) (emb p))
          rw [emb_beq (psi k a) (psi p b), emb_beq k p,
              ← R a b, ← R k p, ← R k (psi p b), ← R (psi k a) p]
        | Z d =>
          show (if ((psi k a : Term) == Z d) = true then false
                else if ((k == Z d) || TM.Term.ltF f k (Z d)) = true then true
                else ((psi k a : Term) == TM.Term.starF f d
                      || TM.Term.ltF f (psi k a) (TM.Term.starF f d)))
              = (if (emb (psi k a) == emb (Z d)) = true then false
                 else if ((emb k == emb (Z d)) || Term2.ltF f (emb k) (emb (Z d))) = true then
                   true
                 else ((emb (psi k a) == Term2.starF f (emb d))
                       || Term2.ltF f (emb (psi k a)) (Term2.starF f (emb d))))
          rw [RS d, emb_beq (psi k a) (Z d), emb_beq k (Z d),
              emb_beq (psi k a) (TM.Term.starF f d),
              ← R k (Z d), ← R (psi k a) (TM.Term.starF f d)]
      | Z e =>
        cases t with
        | zero => rfl
        | M => rfl
        | omg y => rfl
        | add c d =>
          show ((Z e : Term) == c || TM.Term.ltF f (Z e) c)
              = ((emb (Z e) == emb c) || Term2.ltF f (emb (Z e)) (emb c))
          rw [emb_beq (Z e) c, ← R (Z e) c]
        | phi c d =>
          show ((Z e : Term) == c || (Z e : Term) == d
                || TM.Term.ltF f (Z e) c || TM.Term.ltF f (Z e) d)
              = ((emb (Z e) == emb c) || (emb (Z e) == emb d)
                 || Term2.ltF f (emb (Z e)) (emb c) || Term2.ltF f (emb (Z e)) (emb d))
          rw [emb_beq (Z e) c, emb_beq (Z e) d, ← R (Z e) c, ← R (Z e) d]
        | psi p b =>
          show (if ((Z e : Term) == psi p b) = true then false
                else if ((p == Z e) || TM.Term.ltF f p (Z e)) = true then false
                else TM.Term.ltF f (TM.Term.starF f e) (psi p b))
              = (if (emb (Z e) == emb (psi p b)) = true then false
                 else if ((emb p == emb (Z e)) || Term2.ltF f (emb p) (emb (Z e))) = true then
                   false
                 else Term2.ltF f (Term2.starF f (emb e)) (emb (psi p b)))
          rw [RS e, emb_beq (Z e) (psi p b), emb_beq p (Z e),
              ← R p (Z e), ← R (TM.Term.starF f e) (psi p b)]
        | Z b =>
          by_cases he : e = b
          · subst he
            show (if ((Z e : Term) == Z e) = true then false
                  else if TM.Term.ltF f e e = true then
                    TM.Term.ltF f (TM.Term.starF f e) (Z e)
                  else ((Z e : Term) == TM.Term.starF f e
                        || TM.Term.ltF f (Z e) (TM.Term.starF f e)))
                = (if (emb (Z e) == emb (Z e)) = true then false
                   else if (emb e == emb e) = true then Term2.ltF f (emb zero) (emb zero)
                   else if Term2.ltF f (emb e) (emb e) = true then
                     Term2.ltF f (Term2.starF f (emb e)) (emb (Z e))
                   else ((emb (Z e) == Term2.starF f (emb e))
                         || Term2.ltF f (emb (Z e)) (Term2.starF f (emb e))))
            rw [show ((Z e : Term) == Z e) = true from beq_self_eq_true _,
                show (emb (Z e) == emb (Z e)) = true from beq_self_eq_true _]
            rfl
          · have hbe : (e == b) = false := by
              cases hq : e == b with
              | false => rfl
              | true => exact absurd (of_decide_eq_true hq) he
            have hbe2 : (emb e == emb b) = false := by rw [emb_beq]; exact hbe
            show (if ((Z e : Term) == Z b) = true then false
                  else if TM.Term.ltF f e b = true then
                    TM.Term.ltF f (TM.Term.starF f e) (Z b)
                  else ((Z e : Term) == TM.Term.starF f b
                        || TM.Term.ltF f (Z e) (TM.Term.starF f b)))
                = (if (emb (Z e) == emb (Z b)) = true then false
                   else if (emb e == emb b) = true then Term2.ltF f (emb zero) (emb zero)
                   else if Term2.ltF f (emb e) (emb b) = true then
                     Term2.ltF f (Term2.starF f (emb e)) (emb (Z b))
                   else ((emb (Z e) == Term2.starF f (emb b))
                         || Term2.ltF f (emb (Z e)) (Term2.starF f (emb b))))
            rw [hbe2, RS e, RS b, emb_beq (Z e) (Z b),
                emb_beq (Z e) (TM.Term.starF f b),
                ← R e b, ← R (TM.Term.starF f e) (Z b), ← R (Z e) (TM.Term.starF f b)]
            rfl
    · intro t
      cases t with
      | zero => rfl
      | M => rfl
      | psi k a => rfl
      | Z a => rfl
      | omg a =>
        show Term2.starF f (emb a) = emb (TM.Term.starF f a)
        exact RS a
      | add a b =>
        show (if Term2.ltF f (Term2.starF f (emb a)) (Term2.starF f (emb b)) = true
              then Term2.starF f (emb b) else Term2.starF f (emb a))
            = emb (if TM.Term.ltF f (TM.Term.starF f a) (TM.Term.starF f b) = true
                   then TM.Term.starF f b else TM.Term.starF f a)
        rw [RS a, RS b, ← R (TM.Term.starF f a) (TM.Term.starF f b)]
        cases TM.Term.ltF f (TM.Term.starF f a) (TM.Term.starF f b) <;> rfl
      | phi a b =>
        show (if Term2.ltF f (Term2.starF f (emb a)) (Term2.starF f (emb b)) = true
              then Term2.starF f (emb b) else Term2.starF f (emb a))
            = emb (if TM.Term.ltF f (TM.Term.starF f a) (TM.Term.starF f b) = true
                   then TM.Term.starF f b else TM.Term.starF f a)
        rw [RS a, RS b, ← R (TM.Term.starF f a) (TM.Term.starF f b)]
        cases TM.Term.ltF f (TM.Term.starF f a) (TM.Term.starF f b) <;> rfl

theorem ltF_emb (f : Nat) (s t : Term) :
    TM.Term.ltF f s t = Term2.ltF f (emb s) (emb t) := (consv_aux f).1 s t

theorem starF_emb (f : Nat) (t : Term) :
    Term2.starF f (emb t) = emb (TM.Term.starF f t) := (consv_aux f).2 t

theorem deg_le_emb : ∀ t : Term, t.deg ≤ (emb t).deg
  | .zero => Nat.le_refl _
  | .M => Nat.le_refl _
  | .add a b => by
      have h1 := deg_le_emb a; have h2 := deg_le_emb b
      show 1 + a.deg + b.deg ≤ 1 + (emb a).deg + (emb b).deg
      omega
  | .omg a => by
      have h1 := deg_le_emb a
      show 1 + a.deg ≤ 1 + (emb a).deg
      omega
  | .phi a b => by
      have h1 := deg_le_emb a; have h2 := deg_le_emb b
      show 1 + a.deg + b.deg ≤ 1 + (emb a).deg + (emb b).deg
      omega
  | .psi k a => by
      have h1 := deg_le_emb k; have h2 := deg_le_emb a
      show 1 + k.deg + a.deg ≤ 1 + (emb k).deg + (emb a).deg
      omega
  | .Z a => by
      have h1 := deg_le_emb a
      show 1 + a.deg ≤ 1 + (emb a).deg + 1
      omega

/-- **§150 の保存性定理 (証明)。**  `lt` は `emb` を通して 3.14 実装と一致する。
    3.14 は 2.3.15 の一般化であって置き換えではない — chi-2ary.md の注意が定理になった。 -/
theorem lt_emb (s t : Term) : TM.Term.lt s t = Term2.lt (emb s) (emb t) := by
  have hf : s.deg + t.deg ≤ 2 * ((emb s).deg + (emb t).deg) + 8 := by
    have h1 := deg_le_emb s; have h2 := deg_le_emb t; omega
  rw [lt_eq_ltF s t _ hf, ltF_emb]
  rfl

theorem le_emb (s t : Term) : TM.Term.le s t = Term2.le (emb s) (emb t) := by
  show (s == t || TM.Term.lt s t) = (emb s == emb t || Term2.lt (emb s) (emb t))
  rw [emb_beq, lt_emb]

theorem star_emb (t : Term) : Term2.star (emb t) = emb (TM.Term.star t) := by
  show Term2.starF (2 * (emb t).deg + 8) (emb t) = emb (TM.Term.starF (2 * t.deg + 8) t)
  rw [starF_emb]
  rw [starF_stable t (2 * (emb t).deg + 8) (2 * t.deg + 8)
      (by have := deg_le_emb t; omega) (by omega)]

end

/-! ### §150.3 `dict2` — THE COMPOSITIONAL DICTIONARY, REPAIRED AT `reg`

The ONLY change against `Trans/Dict.lean` is `reg`:

    reg  (u+1) = Z (ofNat u)          -- χ_u(0): wrong for u ≥ 1 (Z 1 = I ≠ Ω₂)
    reg2 (u+1) = Z2 zero (ofNat u)    -- χ_0(u) = Ω_{u+1}: the honest name

`collapse2` and `dict2` are verbatim ports; `dict2_sum` is `rfl` again — the
compositionality route (b) had to give up (`dictB143_sum_fails`). -/

section
open Trans.Dict (BT dict collapse reg)

/-- **修理の核。**  Ω_{u+1} = χ_0(u)。1 引数の `reg` は χ_u(0) に送っていた。 -/
def reg2 : Nat → Term2
  | 0 => Term2.zero
  | u + 1 => Term2.Z2 Term2.zero (Term2.ofNat u)

/-- Buchholz の ψ_u ([R91] 値)。`Trans.Dict.collapse` の写しで、`reg` が `reg2` な
    だけ。u = 1 の枝が出す ψ の添字も `reg2 2` = Ω₂ = χ_0(1) になる (旧: `Z 1` = I)。 -/
def collapse2 (u : Nat) (x : Term2) : Term2 :=
  let w := reg2 (u + 1)
  let b := reg2 u
  let base : Term2 := if u == 0 then Term2.zero else Term2.plus b Term2.one
  let pr := Term2.wcnf w (Term2.toList x)
  let st := pr.1.foldl (init := ((none : Option Term2), (none : Option Term2)))
    fun s ac =>
      let a := ac.1
      let c := ac.2
      if Term2.le w a then
        let e := Term2.mulL w (Term2.subAP w a)
        let d := Term2.mulL e c
        let i := match s.1 with
          | none => Term2.sub1 d
          | some i0 => Term2.plus i0 d
        (some i, some (Term2.psi w i))
      else
        let bse := match s.2 with | none => base | some v => v
        let cc := match s.2 with | none => Term2.sub1 c | some _ => c
        (s.1, some (Term2.phiNF a (Term2.plus bse cc)))
  Term2.omegaNF (Term2.plus b (Term2.plus (st.2.getD Term2.zero) pr.2))

/-- **修理された辞書 — 完全に compositional。** -/
def dict2 : BT → Term2
  | .zero => Term2.zero
  | .D u a => collapse2 u (dict2 a)
  | .sum a b => Term2.plus (dict2 a) (dict2 b)

/-- `Trans.oR` の写し (`1 ⊕ ·` の約束もそのまま)。 -/
def oR2 (m : BMS.Matrix) : Option Term2 :=
  if m.isEmpty then some Term2.zero
  else (Trans.Recal.oRB m).map (fun t => Term2.plus Term2.one (dict2 t))

/-- 数詞 (1 の和で 0 でない) か。 -/
def isNum150 : TM.Term → Bool
  | .zero => false
  | t => (TM.Term.toList t).all (· == TM.Term.one)

/-- **Ω 補正つき読み替え** (`emb` の対照)。表と `dict` の `Z (数詞 u)` (u ≥ 1) は
    Ω_{u+1} の誤記なので χ_0(u) へ; それ以外は `emb` と同じ。dict の像に現れる `Z` の
    引数は数詞だけなので、この 1 節が「誤記の訂正」全体である。 -/
def renOm : TM.Term → Term2
  | .zero => Term2.zero
  | .M => Term2.M
  | .add a b => Term2.add (renOm a) (renOm b)
  | .omg a => Term2.omg (renOm a)
  | .phi a b => Term2.phi (renOm a) (renOm b)
  | .psi k a => Term2.psi (renOm k) (renOm a)
  | .Z a => if isNum150 a then Term2.Z2 Term2.zero (renOm a) else Term2.Z2 (renOm a) Term2.zero

/-! ### Clause-level shape: compositionality is back -/

theorem dict2_zero : dict2 .zero = Term2.zero := rfl

theorem dict2_D (u : Nat) (a : BT) : dict2 (.D u a) = collapse2 u (dict2 a) := rfl

/-- **`dict_sum` が戻る。**  route (b) はこれを失った (`dictB143_sum_fails`)。 -/
theorem dict2_sum (a b : BT) : dict2 (.sum a b) = Term2.plus (dict2 a) (dict2 b) := rfl

/-- Ω₂ の像は χ_0(1) — 名前が存在する。 -/
theorem dict2_Om2_150 : dict2 (BT.Om 2) = reg2 2 := rfl

theorem dict2_Om3_150 : dict2 (BT.Om 3) = reg2 3 := rfl

end

/-! ### §150.4 MEASUREMENTS (測定) — the §143 pools, re-run against `dict2`

Everything below is measurement (#guard) unless stated as a theorem.  Headline, against
§143's route (b) (`dictB143`) and §148.4's route (c) (`dictCd148`):

    measured                         `dict`     `dictB143`     `dictCd148`   `dict2` (§150)
    allStd108 9992: = emb ∘ dict      (id)        9992*          9992*          9992
    allStd143 11577: inT             11577        11576          11565         11577
    (A) anchors 28                      28           19             19            28 (renOm)
    order breaks lvl2/cD/cS          0/0/0   672/284/1993    454/175/1163      0/0/0
    injectivity breaks lvl2/cD/cS    0/0/0      40/4/26         48/14/6        0/0/0
    samp143 313²: breaks / inj         0/0     14476/16             —            0/0
    table 60 rows asc./distinct/inT    yes          yes             NO           yes
    dict_sum (compositionality)        rfl        FALSE             —            rfl
    ψ₁(Ω₂) vs Ω₂ collision (§143.6)     —          YES             YES          none

    (* for dictB143/dictCd148 the 9992 reads "agrees with dict"; here it is the
       stronger "equals emb ∘ dict", term for term.)

**`dict2 = renOm ∘ dict` on ALL of allStd143 (11577/11577) and on all 60 table rows.**
On these populations the entire semantic content of the migration is the renaming
`Z (numeral u) ↦ χ_0(u)` — the correction of the misnomer — while every arithmetic
step of `collapse` commutes with it.  The five broken rows keep their published SHAPE
under the honest names; §140's externally validated candidates, read through `renOm`
(their untouched `Z 1` summands are the same misnomer), sit strictly BELOW the `dict2`
values, exactly as they sit below the published values in 𝔗(M).  **No value is
changed** — §140's caveat stands; what the migration buys is that the value question
becomes POSABLE: `Ω₂` has a name, and `ψ_Ω(χ_0(1))` and `ψ_Ω(φ̄(1,Ω))` are different
terms in the right order, instead of one of them being unwritable. -/

section
open TM TM.Term
open Trans.Dict (BT dict collapse reg)

/-- 順序保存の破れの数 (§143 の `cntBad143` と同じ物差し; 像は前計算)。 -/
def cnt2Bad (l : List BT) : Nat :=
  let li := l.map (fun a => (a, dict2 a))
  (li.flatMap fun a => li.map fun b =>
    BT.lt a.1 b.1 == Term2.lt a.2 b.2).countP (· == false)

/-- 単射の破れの数。 -/
def cnt2Inj (l : List BT) : Nat :=
  let li := l.map (fun a => (a, dict2 a))
  (li.flatMap fun a => li.map fun b =>
    (a.1 == b.1) == (a.2 == b.2)).countP (· == false)

/-! ### §150.4.1 The new names, in the right order (proof) -/

/-- **Ω < Ω₂ < Ω₃ < I、そして φ̄(1,Ω) < Ω₂。**  𝔗(M) が言えなかった並びが項として言える。
    3.14 の場合 2 (α = γ, β < δ) と場合 1 (α < γ) がそれぞれ Ω 階層と I を並べる。 -/
theorem omegaChain150 :
    Term2.lt (reg2 1) (reg2 2) = true ∧ Term2.lt (reg2 2) (reg2 3) = true ∧
    Term2.lt (reg2 3) (emb (Z one)) = true ∧ Term2.lt (emb W139) (reg2 2) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! 形成規則: Ω 階層は inT2、極限の第 2 引数 (χ_0(ω)) は満たさない ([R90] 5.1(i))。 -/
#guard Term2.inT (reg2 1) && Term2.inT (reg2 2) && Term2.inT (reg2 3) && Term2.inT (reg2 4)
#guard Term2.inT (Term2.Z2 Term2.zero Term2.omega) == false

/-! ### §150.4.2 Level ≤ 1 is untouched, term for term (測定) -/

#guard allStd108.length == 9992
#guard (allStd108.countP fun z => dict2 z == emb (dict z)) == 9992

/-! `hlvl1` (§148 の第 3 仮定) は emb を通してそのまま: 塔は動かない。 -/
#guard (List.range 11).all fun m => dict2 (psiTow (m + 2)) == emb (TW (m + 1))

/-! ### §150.4.3 The wider population: inT everywhere, and `dict2 = renOm ∘ dict` (測定) -/

#guard allStd143.length == 11577
#guard (allStd143.countP fun z => Term2.inT (dict2 z)) == 11577
#guard (allStd143.countP fun z => dict2 z == renOm (dict z)) == 11577
/-! `dictB143` が inT を外した 1 個 (`bad143`) も通る。 -/
#guard Term2.inT (dict2 bad143)

/-! ### §150.4.4 Order preservation and injectivity — the §143 pools (測定)

`dictB143` は 672/284/1993 の反転と 40/4/26 の単射破れ、抜き取り 313² では 14476/16。
`dict2` は全部 0。 -/

#guard (lvl2_143.length, cD143.length, cS143.length) == (112, 54, 149)
#guard (cnt2Bad lvl2_143, cnt2Bad cD143, cnt2Bad cS143) == (0, 0, 0)
#guard (cnt2Inj lvl2_143, cnt2Inj cD143, cnt2Inj cS143) == (0, 0, 0)
#guard samp143.length == 313
#guard (cnt2Bad samp143, cnt2Inj samp143) == (0, 0)

/-! ### §150.4.5 The 28 anchors of `Trans/Dict.lean` (測定)

route (b)/(c) は 19 で止まった。`dict2` は renOm 読みで 28/28 — 動く 9 個は
ちょうど `Ω₂` を含む 9 個で、その差は誤記の訂正そのものである。 -/

#guard anchorsA143.length == 28
#guard (anchorsA143.countP fun p => dict2 p.1 == renOm p.2) == 28
#guard (anchorsA143.countP fun p => dict2 p.1 == emb p.2) == 19
#guard (anchorsA143.take 19).all fun p => dict2 p.1 == emb p.2

/-! ### §150.4.6 The published table (測定 + rfl)

60 行すべてで `oR2 = renOm ∘ oR`: 表は誤記の訂正だけを受け、昇順・相異・inT を保つ。
段 1 以下の 37 行 (添字 0–36) は emb のまま、38 行目以降は 1 行も emb では合わない
(全部 `Ω₂`/`Ω₃` の誤記を含む)。 -/

#guard Rows.rows.length == 60
#guard (Rows.rows.countP fun r => (oR2 r.m) == ((Trans.oR r.m).map renOm)) == 60
#guard ((Rows.rows.take 37).countP fun r => (oR2 r.m) == ((Trans.oR r.m).map emb)) == 37
#guard ((Rows.rows.drop 37).countP fun r => (oR2 r.m) == ((Trans.oR r.m).map emb)) == 0
#guard (Rows.rows.countP fun r => ((oR2 r.m).map Term2.inT).getD false) == 60
#guard (let vs := Rows.rows.map (fun r => (oR2 r.m).getD Term2.zero);
        (vs.zip vs.tail).all fun p => Term2.lt p.1 p.2)
#guard (Rows.rows.map (fun r => (oR2 r.m).getD Term2.zero)).eraseDups.length == 60

/-- 行 37 の値: `ψ_Ω(χ_0(1)) = ψ_{Ω}(Ω₂)` — 正直な名前 (旧 `ψ_Ω(Z 1)` の訂正)。 -/
theorem row37_150 : oR2 [[0,0],[1,1],[2,2]] = some (Term2.psi (reg2 1) (reg2 2)) := rfl

set_option maxHeartbeats 4000000 in
/-- 5 つの壊れた行の `oR2` は掲載値の `renOm` ちょうど。形は変えず、名前だけ直る。 -/
theorem rows5_renOm_150 :
    oR2 [[0,0],[1,1],[2,2]] = (Trans.oR [[0,0],[1,1],[2,2]]).map renOm ∧
    oR2 [[0,0],[1,1],[2,2],[2,0],[3,1],[4,2]]
      = (Trans.oR [[0,0],[1,1],[2,2],[2,0],[3,1],[4,2]]).map renOm ∧
    oR2 [[0,0],[1,1],[2,2],[2,2]] = (Trans.oR [[0,0],[1,1],[2,2],[2,2]]).map renOm ∧
    oR2 [[0,0],[1,1],[2,2],[2,2],[2,2]]
      = (Trans.oR [[0,0],[1,1],[2,2],[2,2],[2,2]]).map renOm ∧
    oR2 [[0,0],[1,1],[2,2],[3,0],[4,1],[5,2]]
      = (Trans.oR [[0,0],[1,1],[2,2],[3,0],[4,1],[5,2]]).map renOm :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! #### §150.4.6.1 The five rows against §140's candidates (測定)

候補の中の手つかずの `Z 1` も Ω₂ の誤記なので、候補は `renOm` で読む (`emb` だと
χ_1(0) = I になって比較にならない; 行 37 の候補は Z を含まず renOm = emb)。
5 行とも `renOm 候補 < dict2 の値 < emb 掲載値`: 値の問題 (§139/§140) はそのまま残り、
ただし両端が同じ型の別の項として書けるようになった。 -/

#guard renOm corr37_140 == emb corr37_140
#guard Term2.inT (renOm corr37_140) && Term2.inT (renOm corr47_140)
    && Term2.inT (renOm corr52_140) && Term2.inT (renOm corr53_140)
    && Term2.inT (renOm corr58_140)
#guard Term2.lt (renOm corr37_140) ((oR2 [[0,0],[1,1],[2,2]]).getD Term2.zero)
#guard Term2.lt ((oR2 [[0,0],[1,1],[2,2]]).getD Term2.zero)
         (emb ((Trans.oR [[0,0],[1,1],[2,2]]).getD zero))
#guard Term2.lt (renOm corr47_140) ((oR2 [[0,0],[1,1],[2,2],[2,0],[3,1],[4,2]]).getD Term2.zero)
#guard Term2.lt ((oR2 [[0,0],[1,1],[2,2],[2,0],[3,1],[4,2]]).getD Term2.zero)
         (emb ((Trans.oR [[0,0],[1,1],[2,2],[2,0],[3,1],[4,2]]).getD zero))
#guard Term2.lt (renOm corr52_140) ((oR2 [[0,0],[1,1],[2,2],[2,2]]).getD Term2.zero)
#guard Term2.lt ((oR2 [[0,0],[1,1],[2,2],[2,2]]).getD Term2.zero)
         (emb ((Trans.oR [[0,0],[1,1],[2,2],[2,2]]).getD zero))
#guard Term2.lt (renOm corr53_140) ((oR2 [[0,0],[1,1],[2,2],[2,2],[2,2]]).getD Term2.zero)
#guard Term2.lt ((oR2 [[0,0],[1,1],[2,2],[2,2],[2,2]]).getD Term2.zero)
         (emb ((Trans.oR [[0,0],[1,1],[2,2],[2,2],[2,2]]).getD zero))
#guard Term2.lt (renOm corr58_140) ((oR2 [[0,0],[1,1],[2,2],[3,0],[4,1],[5,2]]).getD Term2.zero)
#guard Term2.lt ((oR2 [[0,0],[1,1],[2,2],[3,0],[4,1],[5,2]]).getD Term2.zero)
         (emb ((Trans.oR [[0,0],[1,1],[2,2],[3,0],[4,1],[5,2]]).getD zero))

/-- §140 が行 37 に名指した値は 2 引数側でも `φ̄(1,Ω)` の `collapse2 0`
    (`collapse0_W148` の 2 引数版)。 -/
theorem collapse2_W150 : collapse2 0 (emb W139) = emb corr37_140 := rfl

/-! ### §150.4.7 §143.6's obstruction is gone (proof) -/

set_option maxHeartbeats 4000000 in
/-- **衝突は消えた。**  `Ω₂` と `ψ₁(Ω₂)` の像は別の項 (§143 の `collision143` の否定)。 -/
theorem collision150_gone : dict2 om2_143 ≠ dict2 psi1om2_143 := by decide

/-- `ψ₁(Ω₂)` の像はちょうど `φ̄(1,Ω)` = ε_{Ω+1} — Buchholz の値 ψ₁(Ω₂) = ε_{Ω+1} どおり。
    route (b) はこの項を `Ω₂` の像に使ってしまい衝突した; ここでは `Ω₂ ↦ χ_0(1)` なので
    衝突しない。 -/
theorem psi1om2_150 : dict2 (BT.D 1 (BT.Om 2)) = emb W139 := rfl

set_option maxHeartbeats 4000000 in
/-- **反転も消えた。**  `ψ₁(Ω₂⊕1) < Ω₂` が像でも成り立つ (§143 の `inversion143` の否定)。 -/
theorem inversion150_gone : Term2.lt (dict2 psi1om2s_143) (dict2 om2_143) = true := by decide

set_option maxHeartbeats 4000000 in
/-- **吸和も消えた** (§143 の `absorb143` の否定)。表の行 43–50 の形は保たれる。 -/
theorem absorb150_gone : dict2 (.sum om2_143 psi1om2s_143) ≠ dict2 psi1om2s_143 := by decide

set_option maxHeartbeats 4000000 in
/-- 1 段上 (`Ω₃` 対 `ψ₁(Ω₃)`) も同様 (§143 の `collision143_up` の否定)。 -/
theorem collision150_up_gone : dict2 (BT.Om 3) ≠ dict2 (BT.D 1 (BT.Om 3)) := by decide

#guard Term2.lt (dict2 psi1om2_143) (dict2 om2_143)

/-! ### §150.4.8 The §148 pinch point (測定)

`noSlot148` の 4 仮定のうち `dict2` は `hinT`・`hmono`・`hlvl1` を保ち (上の測定)、
`hOm2` を**正当に**外す: `Ω₂` の像 χ_0(1) は `φ̄(1,Ω)` より真に上の**新しい**項である。
`OmTwo_gt_W148` が任意の写像に要求した「真に上」が、既存の項を潰さずに満たされる —
これが §148.6 の言う「route (a) だけが席を新設できる」の実測である。 -/

#guard Term2.lt (emb W139) (dict2 (BT.Om 2))
#guard Term2.lt (dict2 (BT.D 1 (BT.Om 2))) (dict2 (BT.Om 2))

/-! ### §150.4.9 Conservativity, re-measured beside the proof (測定; 定理は `lt_emb`) -/

#guard (let li := lvl2_143.map (fun z => (dict z, emb (dict z)));
        (li.flatMap fun a => li.map fun b =>
          lt a.1 b.1 == Term2.lt a.2 b.2).countP (· == false)) == 0

/-! ### §150.4.10 What `K_κ` and `*` need (chi-2ary.md step 4) — measured shapes

`*` は形を変えない (χ 項は SC、2.2(v) の恒等のまま)。`K_κ` は第 2 引数への再帰だけ
(2.2(vii) の形のまま)。**本当に新しいのは κ⁻ 1 節**: (χ_γ(δ+1))⁻ = χ_γ(δ)。 -/

#guard Term2.kminus (reg2 2) == reg2 1
#guard Term2.kminus (reg2 3) == reg2 2
#guard Term2.kminus (Term2.Z2 Term2.one Term2.zero) == Term2.star Term2.one
#guard Term2.Kset (reg2 1) (Term2.Z2 Term2.zero
         (Term2.plus (Term2.psi (reg2 1) Term2.zero) Term2.one)) == [Term2.zero]
#guard Term2.star (reg2 2) == reg2 2

/-- [R90] 3.15 の γ = 0 枝 (μ < δ) は 𝔗(M) の φ̄ には当たらない実例:
    φ̄(1,0) = ε₀ < Ω = χ_0(0) は真 (μ < δ = 0 は偽)。3.15 は χ_0 で閉じた μ
    (捨てた Φ 項) の規則で、φ̄–χ は 2.3.4/2.3.5 のままが正しい。 -/
theorem phi_chi_150 : Term2.lt (Term2.phi Term2.one Term2.zero) (reg2 1) = true := rfl

end

/-! ## §151 `XMono145` DID NOT BREAK — AND IT REDUCES TO A FOLD-LOCAL, `ψ₀`-FREE RESIDUAL

The attack families reach the corners §149's census could not (125 symbols, the `bad136`
shape, infinite exponents and coefficient sums); 0 counterexamples, and the control that
drops left K-standardness still fails in the thousands.  On the proof side `tailDec151`
decides the last fold step's comparison from the pair lists alone, `xok_of_tailDec151`
shows it suffices, and `xmono145_of_tailOK151` re-hangs `XMono145` on `TailOK151` — no
`collapse`, no `φ̄`, no `hi`. -/

/-! ### §151.1 The tail decider and its sufficiency -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 最後の対そのもの。 -/
def lastAC151 (y : Term) : Option (Term × Term) :=
  match (wcnf (reg 1) (toList y)).1.reverse with
  | [] => none
  | ac :: _ => some ac

/-- 最後の一歩の直前までの畳み込みの値。 -/
def prevV151 (y : Term) : Option Term :=
  match (wcnf (reg 1) (toList y)).1.reverse with
  | [] => none
  | _ :: r => (r.reverse.foldl (stepF (reg 1) (baseOf 0))
      ((none : Option Term), (none : Option Term))).2

/-- 条項 (i) — 接頭辞の値が等しく、最後の係数が狭義に増える。 -/
def tail1_151 : Option Term → Option Term → Option (Term × Term) →
    Option (Term × Term) → Bool
  | none, none, some ca, some cb => lt (sub1 ca.2) (sub1 cb.2)
  | some v, some v', some ca, some cb => (v == v') && lt ca.2 cb.2
  | _, _, _, _ => false

/-- 条項 (ii) — 左の X が右の接頭辞の値より下。 -/
def tail2_151 : Option (Term × Term) → Option Term → Bool
  | some pa, some v' => lt pa.2 v'
  | _, _ => false

def tailDec151 (a b : BT) : Bool :=
  tail1_151 (prevV151 (dict a)) (prevV151 (dict b))
      (lastAC151 (dict a)) (lastAC151 (dict b))
  || tail2_151 (lastStep129 (dict a)) (prevV151 (dict b))

theorem dictFacts151 (Hp : PsiIdxOKStd172) {a : BT}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hsA : BT.isStd (BT.D 0 a) = true) :
    inT (dict a) = true ∧ lt (dict a) M = true ∧ PsiIdxOK 0 (dict a) := by
  have hba := (btLe72_D 1 0 a hbA).2
  have hia := inT_dict_of_std172 Hp a hba (isStd_of_D hsA)
  exact ⟨hia.1, hia.2, Hp 0 a (by omega) hba hsA⟩

/-- 最後の対が無ければ接頭辞の値も無い。 -/
theorem prevV_none_of_lastAC_none151 {y : Term} (h : lastAC151 y = none) :
    prevV151 y = none := by
  unfold lastAC151 at h
  unfold prevV151
  cases hr : (wcnf (reg 1) (toList y)).1.reverse with
  | nil => rfl
  | cons ac r => rw [hr] at h; dsimp only at h; exact absurd h (by simp)

/-- `lastStep129` を接頭辞の値と最後の対で書いたもの — 値が無い側。 -/
theorem lastStep_prev_none151 {y : Term} {ac : Term × Term}
    (hac : lastAC151 y = some ac) (hpv : prevV151 y = none) :
    lastStep129 y = some (ac.1, plus (baseOf 0) (sub1 ac.2)) := by
  unfold lastAC151 at hac
  unfold prevV151 at hpv
  unfold lastStep129
  cases hr : (wcnf (reg 1) (toList y)).1.reverse with
  | nil => rw [hr] at hac; dsimp only at hac; exact absurd hac (by simp)
  | cons ac0 r =>
      rw [hr] at hac hpv
      dsimp only at hac hpv ⊢
      obtain rfl : ac0 = ac := Option.some.inj hac
      rw [hpv]

/-- `lastStep129` を接頭辞の値と最後の対で書いたもの — 値が有る側。 -/
theorem lastStep_prev_some151 {y : Term} {ac : Term × Term} {v : Term}
    (hac : lastAC151 y = some ac) (hpv : prevV151 y = some v) :
    lastStep129 y = some (ac.1, plus v ac.2) := by
  unfold lastAC151 at hac
  unfold prevV151 at hpv
  unfold lastStep129
  cases hr : (wcnf (reg 1) (toList y)).1.reverse with
  | nil => rw [hr] at hac; dsimp only at hac; exact absurd hac (by simp)
  | cons ac0 r =>
      rw [hr] at hac hpv
      dsimp only at hac hpv ⊢
      obtain rfl : ac0 = ac := Option.some.inj hac
      rw [hpv]

/-- 最後の対の成分は 𝔗(M) の項で、係数は `Ω₁` より下。 -/
theorem lastAC_facts151 {y : Term} (hy : inT y = true) (hly : lt y M = true)
    {ac : Term × Term} (hac : lastAC151 y = some ac) :
    inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 (reg 1) = true := by
  unfold lastAC151 at hac
  cases hr : (wcnf (reg 1) (toList y)).1.reverse with
  | nil => rw [hr] at hac; dsimp only at hac; exact absurd hac (by simp)
  | cons ac0 r =>
      rw [hr] at hac
      dsimp only at hac
      obtain rfl : ac0 = ac := Option.some.inj hac
      have hsplit : r.reverse ++ [ac0] = (wcnf (reg 1) (toList y)).1 := by
        have h2 := congrArg List.reverse hr
        rw [List.reverse_reverse, List.reverse_cons] at h2
        exact h2.symm
      obtain ⟨hc, hd⟩ := inT_toList y hy
      obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1)
        (show (reg 1).isSC = true from rfl) (toList y) hc hd (ltM_toList y hy hly)
      have hWp := wcnf_W79 (toList y) hc
      have hmem : ac0 ∈ (wcnf (reg 1) (toList y)).1 := by
        rw [← hsplit]; exact List.mem_append_right _ (List.Mem.head _)
      have h1 := hallOK ac0 hmem
      have h2 := hWp.2 ac0 hmem
      exact ⟨h1.1, h1.2.1, h1.2.2.1, h2.2⟩

/-- **接頭辞の畳み込みの値の性質。**  §81 の不変量をそのまま接頭辞に当てる。 -/
theorem prevV_facts151 {y : Term} (hy : inT y = true) (hly : lt y M = true)
    (Hp : PsiIdxOK 0 y) {v : Term} (hv : prevV151 y = some v) :
    inT v = true ∧ lt v (reg 1) = true ∧ v.isAP = true ∧ le E081 v = true := by
  unfold prevV151 at hv
  cases hr : (wcnf (reg 1) (toList y)).1.reverse with
  | nil => rw [hr] at hv; dsimp only at hv; exact absurd hv (by simp)
  | cons ac r =>
      rw [hr] at hv
      dsimp only at hv
      have hsplit : r.reverse ++ [ac] = (wcnf (reg 1) (toList y)).1 := by
        have h2 := congrArg List.reverse hr
        rw [List.reverse_reverse, List.reverse_cons] at h2
        exact h2.symm
      obtain ⟨hc, hd⟩ := inT_toList y hy
      obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1)
        (show (reg 1).isSC = true from rfl) (toList y) hc hd (ltM_toList y hy hly)
      have hWp := wcnf_W79 (toList y) hc
      have hNZ := wcnf_NZ81 (toList y) hc
      have hinit : StE81 ((none : Option Term), (none : Option Term)) := by
        intro z hz; cases hz
      have hst := foldE81 r.reverse (none, none) hinit
        (fun z hz => hallOK z (by rw [← hsplit]; exact List.mem_append_left _ hz))
        (fun z hz => (hWp.2 z (by rw [← hsplit]; exact List.mem_append_left _ hz)).2)
        (fun z hz => hNZ z (by rw [← hsplit]; exact List.mem_append_left _ hz))
        (fun p hp hf => Hp p (by
          rw [← hsplit, scanSt_append109]
          exact List.mem_append_left _ hp) hf)
      exact hst v hv

/-- **条項 (i)、値が無い側。**  両辺とも一対だけのとき、`1 ⊖` した係数の比較が
    そのまま X の比較。 -/
theorem xok_noPrev151 {a b : BT} {ca cb : Term × Term}
    (hia : inT (dict a) = true) (hlaM : lt (dict a) M = true)
    (hib : inT (dict b) = true) (hlbM : lt (dict b) M = true)
    (hva : prevV151 (dict a) = none) (hvb : prevV151 (dict b) = none)
    (haca : lastAC151 (dict a) = some ca) (hacb : lastAC151 (dict b) = some cb)
    (h : lt (sub1 ca.2) (sub1 cb.2) = true) : xok145 a b = true := by
  have hLa := lastStep_prev_none151 haca hva
  have hLb := lastStep_prev_none151 hacb hvb
  have he : xok145 a b
      = lt (plus (baseOf 0) (sub1 ca.2)) (plus (baseOf 0) (sub1 cb.2)) := by
    unfold xok145; rw [hLa, hLb]
  rw [he]
  have hca := lastAC_facts151 hia hlaM haca
  have hcb := lastAC_facts151 hib hlbM hacb
  exact plus_smono_right_inT79 (baseOf 0) (inT_baseOf 0) _ _
    (inT_sub1 hca.2.2.1) (inT_sub1 hcb.2.2.1) h

/-- **条項 (i)、値が有る側。**  接頭辞の値が同じなら、最後の係数の比較が
    そのまま X の比較 — `plus` の狭義単調性 (§79)。 -/
theorem xok_samePrev151 (Hp : PsiIdxOKStd172) {a b : BT} {v : Term} {ca cb : Term × Term}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hsA : BT.isStd (BT.D 0 a) = true)
    (hva : prevV151 (dict a) = some v) (hvb : prevV151 (dict b) = some v)
    (haca : lastAC151 (dict a) = some ca) (hacb : lastAC151 (dict b) = some cb)
    (hib : inT (dict b) = true) (hlbM : lt (dict b) M = true)
    (h : lt ca.2 cb.2 = true) : xok145 a b = true := by
  obtain ⟨hia, hlaM, hpa⟩ := dictFacts151 Hp hbA hsA
  have hLa := lastStep_prev_some151 haca hva
  have hLb := lastStep_prev_some151 hacb hvb
  have he : xok145 a b = lt (plus v ca.2) (plus v cb.2) := by
    unfold xok145; rw [hLa, hLb]
  rw [he]
  have hca := lastAC_facts151 hia hlaM haca
  have hcb := lastAC_facts151 hib hlbM hacb
  obtain ⟨hiv, _, _, _⟩ := prevV_facts151 hia hlaM hpa hva
  exact plus_smono_right_inT79 v hiv _ _ hca.2.2.1 hcb.2.2.1 h

/-- **条項 (ii)。**  左の X が右の接頭辞の値より下なら、右の X はその値以上
    (値は加法主要) だから X の比較が出る。 -/
theorem xok_prevDom151 (Hp : PsiIdxOKStd172) {a b : BT} {pa : Term × Term} {v' : Term}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hsA : BT.isStd (BT.D 0 a) = true)
    (hbB : btLe72 1 (BT.D 0 b) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (hla : lastStep129 (dict a) = some pa)
    (hvb : prevV151 (dict b) = some v')
    (h : lt pa.2 v' = true) : xok145 a b = true := by
  obtain ⟨hia, hlaM, hpa2⟩ := dictFacts151 Hp hbA hsA
  obtain ⟨hib, hlbM, hpb⟩ := dictFacts151 Hp hbB hsB
  cases hacb : lastAC151 (dict b) with
  | none =>
      rw [prevV_none_of_lastAC_none151 hacb] at hvb
      exact absurd hvb (by simp)
  | some cb =>
      have hLb := lastStep_prev_some151 hacb hvb
      have he : xok145 a b = lt pa.2 (plus v' cb.2) := by
        unfold xok145; rw [hla, hLb]
      rw [he]
      obtain ⟨hiv, _, hvap, _⟩ := prevV_facts151 hib hlbM hpb hvb
      have hcb := lastAC_facts151 hib hlbM hacb
      obtain ⟨_, hXf⟩ := lastStep_inT129 hia hlaM hpa2
        (show lastStep129 (dict a) = some (pa.1, pa.2) from by rw [hla])
      have hle : le v' (plus v' cb.2) = true := le_self_plus_ap81 hiv hvap hcb.2.2.1
      exact lt_of_lt_of_le3 (inT_le_fragR _ hXf.1) (inT_le_fragR _ hiv)
        (inT_le_fragR _ (inT_plus hiv hcb.2.2.1)) h hle

/-- **§151 の主定理 — 判定器は結論を導く。**  第一の門のもとで、`tailDec151` が
    立つ適格な組では `X_a < X_b`。`hi a < hi b` も指数の一致も要らない。 -/
theorem xok_of_tailDec151 (Hp : PsiIdxOKStd172) {a b : BT}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hbB : btLe72 1 (BT.D 0 b) = true)
    (hsA : BT.isStd (BT.D 0 a) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (h : tailDec151 a b = true) : xok145 a b = true := by
  obtain ⟨hia, hlaM, hpa⟩ := dictFacts151 Hp hbA hsA
  obtain ⟨hib, hlbM, hpb⟩ := dictFacts151 Hp hbB hsB
  rcases (Bool.or_eq_true _ _).mp h with h1 | h2
  · cases hva : prevV151 (dict a) with
    | none =>
        cases hvb : prevV151 (dict b) with
        | none =>
            cases haca : lastAC151 (dict a) with
            | none => rw [hva, hvb, haca] at h1; exact Bool.noConfusion h1
            | some ca =>
                cases hacb : lastAC151 (dict b) with
                | none => rw [hva, hvb, haca, hacb] at h1; exact Bool.noConfusion h1
                | some cb =>
                    rw [hva, hvb, haca, hacb] at h1
                    exact xok_noPrev151 hia hlaM hib hlbM hva hvb haca hacb h1
        | some v' =>
            rw [hva, hvb] at h1
            cases haca : lastAC151 (dict a) with
            | none => rw [haca] at h1; exact Bool.noConfusion h1
            | some ca =>
                cases hacb : lastAC151 (dict b) with
                | none => rw [haca, hacb] at h1; exact Bool.noConfusion h1
                | some cb => rw [haca, hacb] at h1; exact Bool.noConfusion h1
    | some v =>
        cases hvb : prevV151 (dict b) with
        | none =>
            rw [hva, hvb] at h1
            cases haca : lastAC151 (dict a) with
            | none => rw [haca] at h1; exact Bool.noConfusion h1
            | some ca =>
                cases hacb : lastAC151 (dict b) with
                | none => rw [haca, hacb] at h1; exact Bool.noConfusion h1
                | some cb => rw [haca, hacb] at h1; exact Bool.noConfusion h1
        | some v' =>
            cases haca : lastAC151 (dict a) with
            | none => rw [hva, hvb, haca] at h1; exact Bool.noConfusion h1
            | some ca =>
                cases hacb : lastAC151 (dict b) with
                | none => rw [hva, hvb, haca, hacb] at h1; exact Bool.noConfusion h1
                | some cb =>
                    rw [hva, hvb, haca, hacb] at h1
                    have h1' : ((v == v') && lt ca.2 cb.2) = true := h1
                    obtain ⟨hq, hcc⟩ := (Bool.and_eq_true _ _).mp h1'
                    rw [show v' = v from (eq_of_beq hq).symm] at hvb
                    exact xok_samePrev151 Hp hbA hsA hva hvb haca hacb hib hlbM hcc
  · cases hla : lastStep129 (dict a) with
    | none =>
        cases hvb : prevV151 (dict b) with
        | none => rw [hla, hvb] at h2; exact Bool.noConfusion h2
        | some v' => rw [hla, hvb] at h2; exact Bool.noConfusion h2
    | some pa =>
        cases hvb : prevV151 (dict b) with
        | none => rw [hla, hvb] at h2; exact Bool.noConfusion h2
        | some v' =>
            rw [hla, hvb] at h2
            exact xok_prevDom151 Hp hbA hsA hbB hsB hla hvb h2

/-- **名前つきの残り — `TailOK151`。**  適格で最後の指数が等しく `hi` が増える組では、
    判定器のどちらかの条項が立つ、という ψ₀ 抜き・畳み込みだけの一文。 -/
def TailOK151 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lastFire92 (dict a) = false → lastFire92 (dict b) = false →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    sameExp145 a b = true → tailDec151 a b = true

/-- **§151 の橋 — `XMono145` は `TailOK151` から出る。** -/
theorem xmono145_of_tailOK151 (Hp : PsiIdxOKStd172) (H : TailOK151) : XMono145 :=
  fun a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hse =>
    xok_of_tailDec151 Hp hbA hbB hsA hsB
      (H a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hse)

#print axioms xok_of_tailDec151
#print axioms xmono145_of_tailOK151

/-! ### §151.3 MEASUREMENT (frozen) — the attack, and the coverage of the decider

母集団は §149 の census が届かなかった四つの角に向けて組んだもの。行の読み方は
各 census の docstring の通り。**どの行でも `XMono145` は外れない。** -/

def sm151 : List BT → BT
  | [] => BT.zero
  | [x] => x
  | x :: r => BT.sum x (sm151 r)
def w151 : BT := BT.D 1 BT.zero
/-- `Ω₁^(k+1)`。 -/
def pw151 (k : Nat) : BT :=
  if k == 0 then w151 else BT.D 1 (sm151 (List.replicate k w151))
/-- `Ω₁^(k+1)·ω^(ψ₀e)` — 係数を `ψ₀` の節ひとつに隠した冪。 -/
def cp151 (k : Nat) (e : BT) : BT :=
  if k == 0 then BT.D 1 (BT.D 0 e)
  else BT.D 1 (sm151 (List.replicate k w151 ++ [BT.D 0 e]))
/-- `Ω₁^(k+1)·ω^(ψ₀e ⊕ ψ₀f)` — 係数の和。 -/
def cp2_151 (k : Nat) (e f : BT) : BT :=
  BT.D 1 (sm151 (List.replicate k w151 ++ [BT.D 0 e, BT.D 0 f]))
/-- `ψ₁` の塔 — 底 `Ω₁` の指数が `Ω₁` 以上になり、発火する接頭辞を作る。 -/
def tw151 (n : Nat) : BT := nst132 n BT.zero
/-- `Ω₁^(ω^(ψ₀x))` — 無限の指数、係数 1。 -/
def ip151 (x : BT) : BT := BT.D 1 (BT.D 1 (BT.D 0 x))
/-- `Ω₁^(ω^(ψ₀x))·ω^(ψ₀f)` — 無限の指数に係数を隠す。 -/
def ic151 (x f : BT) : BT := BT.D 1 (sm151 [BT.D 1 (BT.D 0 x), BT.D 0 f])
/-- `Ω₁^(ω^(ψ₀x) ⊕ ω^(ψ₀x'))·ω^(ψ₀f)` — 和の指数。 -/
def ips151 (x x' f : BT) : BT :=
  BT.D 1 (sm151 [BT.D 1 (BT.D 0 x), BT.D 1 (BT.D 0 x'), BT.D 0 f])
/-- `Ω₁^(ω^(ψ₀x) ⊕ k)·ω^(ψ₀f)` — 無限と有限の混じった指数。 -/
def imx151 (x : BT) (k : Nat) (f : BT) : BT :=
  BT.D 1 (sm151 ([BT.D 1 (BT.D 0 x)] ++ List.replicate k w151 ++ [BT.D 0 f]))

/-- `XMono145` の仮定をぜんぶ満たすか。 -/
def qual151 (a : BT) : Bool :=
  btLe72 1 (BT.D 0 a) && BT.isStd (BT.D 0 a) && le (reg 1) (dict a)
    && !(lastFire92 (dict a))
/-- 対照 — 左辺の `K` 標準性だけを Buchholz 標準性に緩めたもの。 -/
def qualNoK151 (a : BT) : Bool :=
  btLe72 1 (BT.D 0 a) && BT.isStd a && le (reg 1) (dict a) && !(lastFire92 (dict a))

def eps151 : List BT :=
  [BT.zero, BT.one, w151, BT.D 1 w151, sm151 [w151, w151], BT.D 1 (BT.D 0 BT.zero)]
def bump151 (e : BT) : BT := BT.add e BT.one

/-- 族 A の塔 — 尾の `ψ₀` の引数を `K` 標準性の天井まで反復で押し上げる。 -/
def itA151 (j k : Nat) (e : BT) : Nat → BT
  | 0 => sm151 [cp151 j e, cp151 k BT.zero]
  | n+1 => sm151 [cp151 j e, cp151 k (itA151 j k e n)]

/-- **族 A** — 対 1 の係数が無限で、辞書式の判定が対 1 で決まり、尾が天井。
    最後の塊は対照 (尾の引数が項自身を越える — `K` 標準でない)。 -/
def poolA151 : List BT :=
  (([1, 2, 3, 4].flatMap fun j => (List.range j).flatMap fun k => eps151.flatMap fun e =>
      (List.range 4).map fun n => itA151 j k e n)) ++
  ([1, 2, 3, 4].flatMap fun j => (List.range j).flatMap fun k => eps151.flatMap fun e =>
      [sm151 [cp151 j (bump151 e), pw151 k],
       sm151 [cp151 j e, pw151 j, pw151 k],
       sm151 [cp151 j e, pw151 k],
       sm151 [cp151 j (BT.add e w151), pw151 k],
       sm151 [cp2_151 j e e, pw151 k]]) ++
  ([2, 3, 4].flatMap fun j => (List.range (j-1)).flatMap fun k => eps151.flatMap fun e =>
      (List.range (j-k-1)).map fun i =>
        sm151 [cp151 j e, pw151 (k+i+1), pw151 k]) ++
  ([1, 2, 3].flatMap fun j => (List.range j).flatMap fun k => eps151.map fun e =>
      sm151 [cp151 j e, cp151 k (sm151 [cp151 j (bump151 e), pw151 k])])

/-- 族 C の塔 — 発火する接頭辞つきで尾を反復。 -/
def itC151 (n k : Nat) : Nat → BT
  | 0 => sm151 [tw151 n, cp151 k BT.zero]
  | m+1 => sm151 [tw151 n, cp151 k (itC151 n k m)]

/-- **族 C** — 発火する `ψ₁` の塔の接頭辞 + 発火しない最後の対 (`bad136` の形)。 -/
def poolC151 : List BT :=
  (([3, 4, 5, 6].flatMap fun n => [0, 1, 2].flatMap fun k =>
      (List.range 4).map fun m => itC151 n k m)) ++
  ([3, 4, 5, 6].flatMap fun n => [0, 1, 2].flatMap fun k =>
      [sm151 [tw151 n, pw151 k],
       sm151 [tw151 n, tw151 n, pw151 k],
       sm151 [tw151 (n+1), pw151 k],
       sm151 [tw151 n, pw151 (k+1), pw151 k],
       sm151 [tw151 n, cp151 k (BT.sum (tw151 n) (tw151 (n-1)))],
       sm151 [tw151 n, cp151 k (tw151 n)],
       sm151 [tw151 n, tw151 (n-1), pw151 k],
       sm151 [tw151 n, cp151 k (sm151 [tw151 n, tw151 n])]])

/-- 族 D の塔 — 無限の指数の係数を反復で押し上げる。 -/
def itD151 (x : BT) : Nat → BT
  | 0 => ip151 x
  | m+1 => ic151 x (itD151 x m)
def xs151 : List BT := [BT.zero, BT.one, w151, sm151 [w151, w151], BT.D 1 w151]

/-- **族 D** — 無限の指数 `ω^(ψ₀x)`、和・混合の指数、塔の接頭辞との併用。
    最後の塊は対照の意図で置いたが 5 本とも壊す組を作らなかった (下の census 参照)。 -/
def poolD151 : List BT :=
  (xs151.flatMap fun x => (List.range 5).map fun m => itD151 x m) ++
  (xs151.flatMap fun x => xs151.flatMap fun x' =>
     [sm151 [ip151 x', ip151 x], sm151 [ic151 x' BT.zero, ip151 x]]) ++
  (xs151.flatMap fun x =>
     [sm151 [ip151 x, pw151 0], sm151 [ip151 x, pw151 1],
      sm151 [tw151 4, ip151 x], sm151 [tw151 4, ic151 x (tw151 4)],
      BT.D 1 (sm151 [BT.D 1 (BT.D 0 x), BT.D 0 x, BT.D 0 x]),
      sm151 [ic151 x (ip151 x), ip151 x],
      sm151 [ic151 x (itD151 x 2), ip151 x]]) ++
  (xs151.flatMap fun x => xs151.flatMap fun x' =>
     [ips151 x x' BT.zero, ips151 x x' w151, imx151 x 1 BT.zero, imx151 x 2 BT.zero,
      imx151 x 1 (bump151 x'), sm151 [ips151 x x' BT.zero, pw151 0],
      sm151 [imx151 x 2 BT.zero, imx151 x 1 BT.zero]]) ++
  (xs151.map fun x => ic151 x (ip151 (bump151 x)))

/-- **族 E** — 係数の和と係数の接頭辞の判定。最後の塊は対照。 -/
def poolE151 : List BT :=
  ([1, 2].flatMap fun j => eps151.flatMap fun e => eps151.flatMap fun f =>
     [sm151 [cp2_151 j e f, pw151 0],
      sm151 [cp2_151 j e (bump151 f), pw151 0],
      sm151 [cp151 j e, pw151 0],
      sm151 [cp2_151 j e f, cp151 0 (sm151 [cp2_151 j e f, pw151 0])],
      sm151 [cp2_151 j e f, cp151 0 (cp2_151 j e f)]]) ++
  ([1, 2].flatMap fun j => eps151.map fun e =>
     sm151 [cp151 j e, cp151 0 (sm151 [cp2_151 j e e, pw151 0])])

def poolM151 : List BT := poolA151 ++ poolC151 ++ poolD151 ++ poolE151

abbrev Q151 := (Term × Option (Term × Term)) × (Option Term × Option (Term × Term))
def dq151 (a : BT) : Q151 :=
  let y := dict a
  ((hiW89 y, lastStep129 y), (prevV151 y, lastAC151 y))
def sameQ151 (x y : Q151) : Bool :=
  match x.1.2, y.1.2 with | some pa, some pb => pa.1 == pb.1 | _, _ => false
def xokQ151 (x y : Q151) : Bool :=
  match x.1.2, y.1.2 with | some pa, some pb => lt pa.2 pb.2 | _, _ => false
def d1Q151 (x y : Q151) : Bool := tail1_151 x.2.1 y.2.1 x.2.2 y.2.2
def d2Q151 (x y : Q151) : Bool := tail2_151 x.1.2 y.2.1

/-- (同じ指数の義務, 条項 (i) が立つ組, 条項 (ii) が立つ組,
     どちらも立たないが結論は成る組, どちらも立たず結論も外す組 = `XMono145` の反例)。 -/
def cov151 (L : List BT) : Nat × Nat × Nat × Nat × Nat :=
  let D := (L.filter qual151).map dq151
  D.foldl (fun (acc : Nat × Nat × Nat × Nat × Nat) x =>
      D.foldl (fun (r : Nat × Nat × Nat × Nat × Nat) y =>
        if lt x.1.1 y.1.1 && sameQ151 x y then
          let d1 := d1Q151 x y
          let d2 := d2Q151 x y
          let dec := d1 || d2
          (r.1 + 1, r.2.1 + (if d1 then 1 else 0), r.2.2.1 + (if d2 then 1 else 0),
           r.2.2.2.1 + (if !dec && xokQ151 x y then 1 else 0),
           r.2.2.2.2 + (if !dec && !(xokQ151 x y) then 1 else 0))
        else r) acc) (0, 0, 0, 0, 0)

/-- 全順序対での健全性の照合 — (判定器が立つ組, 立つのに `X` が増えない組)。
    後者が 1 でもあれば `xok_of_tailDec151` と食い違い、第一の残る仮定が倒れる。 -/
def snd151 (L : List BT) : Nat × Nat :=
  let D := (L.filter qual151).map dq151
  D.foldl (fun (acc : Nat × Nat) x =>
      D.foldl (fun (r : Nat × Nat) y =>
        let dec := d1Q151 x y || d2Q151 x y
        (r.1 + (if dec then 1 else 0),
         r.2 + (if dec && !(xokQ151 x y) then 1 else 0))) acc) (0, 0)

/-- 対照の census — 左辺だけ `K` 標準性を外す。
    (左の母集団, 同じ指数の義務, 結論を外す組)。 -/
def cenNoK151 (L : List BT) : Nat × Nat × Nat :=
  let D := (L.filter qualNoK151).map dq151
  let E := (L.filter qual151).map dq151
  let r := D.foldl (fun (acc : Nat × Nat) x =>
      E.foldl (fun (r : Nat × Nat) y =>
        if lt x.1.1 y.1.1 && sameQ151 x y then
          (r.1 + 1, if xokQ151 x y then r.2 else r.2 + 1)
        else r) acc) (0, 0)
  ((L.filter qualNoK151).length, r.1, r.2)

/-! **母集団の大きさ。**  (全体, 適格, `K` 抜きで適格)。混ぜた池は 125 記号まで。 -/

#guard (poolA151.length, (poolA151.filter qual151).length,
        (poolA151.filter qualNoK151).length) == (636, 590, 626)
#guard (poolC151.length, (poolC151.filter qual151).length,
        (poolC151.filter qualNoK151).length) == (144, 121, 143)
#guard (poolD151.length, (poolD151.filter qual151).length,
        (poolD151.filter qualNoK151).length) == (290, 235, 240)
#guard (poolE151.length, (poolE151.filter qual151).length,
        (poolE151.filter qualNoK151).length) == (372, 228, 240)
#guard ((poolM151.map BT.size).foldl max 0) == 125

/-! **攻めの結果 — `XMono145` はどの族でも外れない。**  五列目が反例の数。
四つの族どうしを混ぜた 181695 の義務でも 0。しかも二つの条項がすべての義務を
拾っている (四列目も 0)。 -/

#guard cov151 poolA151 == (53768, 720, 53048, 0, 0)
#guard cov151 poolC151 == (2370, 244, 2126, 0, 0)
#guard cov151 poolD151 == (1260, 420, 840, 0, 0)
#guard cov151 poolE151 == (25688, 146, 25542, 0, 0)
#guard cov151 poolM151 == (181695, 1842, 179853, 0, 0)

/-! **全数の掃き — 大きさ 13 まで。**  6548370 の義務を二つの条項がちょうど
分割する (2080773 + 4467597、重なりも漏れも 0)。条項 (i) の組では接頭辞の値が
等しいから条項 (ii) は立ち得ない — 分割は定義から従う。 -/

#guard cov151 ((stdTab130 12).flatten) == (6548370, 2080773, 4467597, 0, 0)

/-! **健全性の照合。**  判定器が立つ全順序対で `X` は必ず増える —
`xok_of_tailDec151` の言う通り。混ぜた池で 659509 組、全数の掃きで 20327346 組。 -/

#guard snd151 poolM151 == (659509, 0)
#guard snd151 ((stdTab130 12).flatten) == (20327346, 0)

/-! **対照 — 掃きは空虚ではない。**  左辺の `K` 標準性だけを外すと A/C/E で
144/31/156 組が結論を外す。担いでいるのはその条項ひとつ (§133 の言い分のまま)。
D の対照 5 本は壊す組を作らなかった — 無限の指数の角で `K` 標準性を外して壊す形は
この族には無い、というのがこの行の中身である。 -/

#guard cenNoK151 poolA151 == (626, 58700, 144)
#guard cenNoK151 poolC151 == (143, 2756, 31)
#guard cenNoK151 poolD151 == (240, 1290, 0)
#guard cenNoK151 poolE151 == (240, 27238, 156)

/-! **§101 の near-miss は判定器も外す。**  `tailDec151` が偽で `xok145` も偽 —
十分条件の対偶と食い違わない。§81 の対も同じ。 -/

#guard (tailDec151 bothBadA101 bothBadB101, xok145 bothBadA101 bothBadB101,
        tailDec151 cexA89 cexB89) == (false, false, false)

end

/-! ## §152 THE FIRST GATE'S TOWER RESIDUAL: §136'S SHAPE SENTENCE IS A THEOREM AT
       EVERY HEIGHT, AND THE TWO BOUNDARIES COINCIDE

Nothing in the project is edited.  Every definition below lives beside the library
under a new name.

§136 closed its route (b) with one sentence: at the minimal residual term the escaping
element `y` and the emitted index `i` are THE SAME TOWER SHAPE except that `i` has
`ψ_{Ω₁}(y)` where `y` has `Ω₁`.  §152 formalises that sentence over the whole
two-parameter family `famB132 m k = ψ₁^m(ψ₀(ψ₁^k 0))` — §130/§132's home of every
counterexample to the ungated first clause — and proves BOTH sides of it, for ALL
heights, where §132.5/§136.4/§145.5 had measured `m, k < 10`.

WHAT IS PROVED, UNCONDITIONALLY (no `PsiIdxOKStd172`, no `HiMono89`, no `sorry`,
no `native_decide`; `#print axioms` at the end shows `[propext, Quot.sound]`).

  §152.1   **The ω-tower on 𝔗(M) and its strict monotonicity** (`twT152`,
           `twT152_smono`) — §79.2's `lt_omegaNF_inT79` iterated to any height, the
           tool the closing note of §136 asked for.

  §152.3   **The residual tower `UW152 s m = ω^ω^…^(Ω₁ ⊕ s)`** and its complete
           base-`Ω₁` scan, mirroring §139's `TWG139` cluster: one digit, exponent
           the next level down, coefficient `1`, and the emitted index is THE TOWER
           ITSELF (`wcnf_UW152`, `idx_UW152`).  This is §136's route (b) — the
           decomposition read off the shape — carried to the end on the residual's
           own family.

  §152.4   **Closed forms.**  `dict (famB132 (m+1) (k+3)) = UW152 (sd152 (k+3)) m`
           (`dict_famB152`), `dict (ψ₁^{j+2} 0) = TW (j+1)` (`dict_bT152`, §139),
           and the seed values: `sd152 (j+4) = ψ_{Ω₁}(TW (j+3))` (`sd_psi152`),
           `sd152 3 = ψ_{Ω₁}(0)`, `sd152 0/1/2 = 1 / φ̄(1,0) / φ̄(2,0)`.

  §152.5   **The K-sets.**  `K_{Ω₁}` of the `UW` tower is the seed's `K` alone
           (`Kset_UW152`); for `k ≥ 4` that is exactly `[TW (k-1)]`
           (`Kset_sd_psi152`) — the escaping element is the inner tower, nothing else.

  §152.6   **The shape comparison, both directions.**  Same tower shape, the bottoms
           decide: `TW a < UW152 s b` iff the `y`-tower is not higher —
           `lt_TW_UW152 : a ≤ b → TW a < UW s b` and
           `lt_TW_UW_false152 : b < a → ¬(TW a < UW s b)` (for `Ω₁ ≤ s` shapes the
           first, `s < Ω₁`-seeds the second).  And the sandwich
           `lt_UW_TW152 : TW b < UW152 s b < TW (b+1)` — **the emitted index sits
           strictly between tower stages**, which is WHY the boundary is `k ≤ m`.

  §152.7   **The first clause's step on the family, both sides.**
           `ksetStepOK_famB152 : 3 ≤ k → k ≤ m → KsetStepOK 0 (dict (famB132 m k))`;
           `not_ksetStepOK_famB152 : 3 ≤ m → m < k → ¬ KsetStepOK 0 (dict …)` —
           §130's `min130` (`m = 3, k = 4`) generalised to the whole wedge: the
           tower shapes really do diverge there, at every height.

  §152.8   **The small seeds** (`k ≤ 2`): the seed's `K` is empty, so the step is a
           theorem for EVERY `m` (`famB_small_gate152`, via a `K`-emptiness induction
           `nst_kempty152` that §73.4's unconditional level-1 clause powers).

  §152.9   **The standardness boundary, the direction the residual needs:**
           `m < k → BT.isStd (ψ₀ (famB132 m k)) = false` (`not_std_famB152`) — the
           escaping tower `ψ₁^k 0` sits in `G(a,0)` but not below `a`
           (`bT_not_lt_famB152`, fuel-uniform).  Hence the family's per-term gate:
           **`famB_no_refute152 : BT.isStd (ψ₀ (famB132 m k)) → KsetStepOK 0 (dict …)`**
           and `gateStd87_famB152 : GateStd87 (famB132 m k)`, the exact shape §87's
           size induction consumes; `psiIdxOK_famB152` packages it as 2.1(vi), and
           `firstFire_famB152` as §145.4's `FirstFire145` — the H1 obligation of
           `psiIdxOKStd172_of_first145`, discharged on the family.

  §152.12  **The boundary is exact:** `std_boundary152 :
           BT.isStd (ψ₀ (famB132 m k)) = decide (k ≤ m)` for ALL `m, k` (the
           standard side via `isStd_famB152` and the `G`-set characterisation), and
           the capstone **`boundary_coincide152` : at firing heights (`3 ≤ m`) the
           first clause's step is EQUIVALENT to `K`-standardness** on the family.
           The two frozen boundaries of §132.5 do not merely fail to cross — they
           are the same line, provably, at every height.

WHAT IS MEASURED, NOT PROVED (§152.13): the §132.5 deciders re-run on `m, k < 12`
(the frozen tables stopped at 9) against the boundary formulas; the closed forms and
seed values recomputed by the kernel; the `(y, idx)` pairs of §145.5's obligation
counter re-checked on samples; and one new probe — seeds that are SUMS of towers,
`ψ₁^m(ψ₀(ψ₁^k 0 ⊕ ψ₁^j 0))`, 343 shapes — where no standard term escapes either.

WHAT IS **NOT** CLAIMED.  `PsiIdxOKStd172` itself is neither proved nor refuted:
the residual's general term can carry several digits, coefficients above `1`, and
seeds whose `K` holds more than one element, and none of that is covered here —
`stepOK_UW152` states the general single-digit lemma (any seed `s < Ω₁`, any
height, gate reduced to the seed's `K`-bound), and what remains beyond it is the
multi-digit plumbing of §136.1's bundle.  What IS closed: the family that produced
every known counterexample candidate can never produce one — at any height, not
just the measured ones — because the diverging wedge is exactly the non-standard
wedge.
-/


section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §152.1 The ω-tower on 𝔗(M) and its strict monotonicity -/

/-- `ω` の塔。`twT152 n t = ω^ω^…^t` (`ω^·` を `n` 回)。 -/
def twT152 : Nat → Term → Term
  | 0, t => t
  | n+1, t => omegaNF (twT152 n t)

theorem twT152_add (a b : Nat) (t : Term) :
    twT152 a (twT152 b t) = twT152 (a + b) t := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
      rw [Nat.succ_add]
      show omegaNF (twT152 a (twT152 b t)) = omegaNF (twT152 (a + b) t)
      rw [ih]

theorem inT_twT152 (n : Nat) {t : Term} (ht : inT t = true) :
    inT (twT152 n t) = true := by
  induction n with
  | zero => exact ht
  | succ n ih => exact inT_omegaNF ih

theorem ltM_twT152 (n : Nat) {t : Term} (ht : inT t = true) (hl : lt t M = true) :
    lt (twT152 n t) M = true := by
  induction n with
  | zero => exact hl
  | succ n ih => exact ltM_omegaNF (inT_twT152 n ht) ih

/-- **塔は底について狭義単調。**  §79.2 の `lt_omegaNF_inT79` を段の数だけ重ねる。 -/
theorem twT152_smono (n : Nat) {x y : Term} (hx : inT x = true) (hy : inT y = true)
    (h : lt x y = true) : lt (twT152 n x) (twT152 n y) = true := by
  induction n with
  | zero => exact h
  | succ n ih => exact lt_omegaNF_inT79 (inT_twT152 n hx) (inT_twT152 n hy) ih

/-- 塔の頭は `Ω₁` より上に居続ける — 底が `Ω₁` より真に上なら。 -/
theorem lt_reg1_twT152 (n : Nat) {t : Term} (ht : inT t = true)
    (h : lt (reg 1) t = true) : lt (reg 1) (twT152 (n+1) t) = true := by
  induction n with
  | zero =>
      have h1 : lt (omegaNF (reg 1)) (omegaNF t) = true :=
        lt_omegaNF_inT79 (inT_reg 1) ht h
      rwa [omegaNF_reg1_79] at h1
  | succ n ih =>
      have h1 : lt (omegaNF (reg 1)) (omegaNF (twT152 (n+1) t)) = true :=
        lt_omegaNF_inT79 (inT_reg 1) (inT_twT152 (n+1) ht) ih
      rwa [omegaNF_reg1_79] at h1

end

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §152.2 Small facts about the base and the levels -/

/-- `ω^0 = 1`。 -/
theorem omegaNF_zero152 : omegaNF zero = one := by decide

/-- `Ω₁ ≤ 1` は成り立たない。 -/
theorem not_le_reg1_one152 : le (reg 1) one = false := by decide

/-- `Ω₁ < Ω₁ ⊕ ρ` — `ρ ≠ 0` なら狭義。 -/
theorem lt_reg1_plus152 {r : Term} (hr : inT r = true) (hne : r ≠ zero) :
    lt (reg 1) (plus (reg 1) r) = true := by
  have h0 : lt (plus (reg 1) zero) (plus (reg 1) r) = true :=
    plus_smono_right_inT79 (reg 1) (inT_reg 1) zero r inT_zero hr (lt_zero_left hne)
  rwa [plus_nil rfl] at h0

/-- `Ω₁ < ω^(Ω₁ ⊕ ρ)`。 -/
theorem lt_reg1_omegaNF_plus152 {r : Term} (hr : inT r = true) (hne : r ≠ zero) :
    lt (reg 1) (omegaNF (plus (reg 1) r)) = true := by
  have h1 : lt (omegaNF (reg 1)) (omegaNF (plus (reg 1) r)) = true :=
    lt_omegaNF_inT79 (inT_reg 1) (inT_plus (inT_reg 1) hr) (lt_reg1_plus152 hr hne)
  rwa [omegaNF_reg1_79] at h1

/-- 頭が `Ω₁` の和は具象の `add`。 -/
theorem plus_reg1_ap152 {r : Term} (hap : r.isAP = true) (hle : le r (reg 1) = true) :
    plus (reg 1) r = add (reg 1) r := by
  rw [plus_cons66 (toList_isAP81 hap),
    show toList (reg 1) = [Z zero] from rfl,
    List.filter_cons_of_pos (by exact hle)]
  rfl

/-- `K_{Ω₁}(ψ_{Ω₁}(X)) = X :: K_{Ω₁}(X)`。 -/
theorem Kset_psi_reg152 (X : Term) :
    Kset (reg 1) (psi (Z zero) X) = X :: Kset (reg 1) X := by
  show (if le (psi (Z zero) X) (kminus (reg 1)) then []
        else if lt (Z zero) (reg 1) then Kset (reg 1) (Z zero)
        else X :: (Kset (reg 1) (Z zero) ++ Kset (reg 1) X)) = _
  rw [show le (psi (Z zero) X) (kminus (reg 1)) = false from by
      show ((psi (Z zero) X == zero) || lt (psi (Z zero) X) zero) = false
      rw [lt_zero_right]
      rfl,
    if_neg (by exact Bool.noConfusion),
    show lt (Z zero) (reg 1) = false from lt_irrefl _,
    if_neg (by exact Bool.noConfusion)]
  rfl

/-- `add` は `ω^·` の不動点の形をしていない。 -/
theorem isFP_add152 (a b : Term) : isFP zero (add a b) = false := by
  show (((add a b).isSC && lt zero (add a b)) || false) = false
  rw [show (add a b).isSC = false from rfl]
  rfl

/-- `φ̄0` の項も不動点の形をしていない。 -/
theorem isFP_phi0_152 (c : Term) : isFP zero (phi zero c) = false := by
  show (((phi zero c).isSC && lt zero (phi zero c)) || lt zero zero) = false
  rw [show (phi zero c).isSC = false from rfl,
    show lt (zero : Term) zero = false from lt_irrefl zero]
  rfl

/-- 単独の AP で `1` でない項の `splitFin` は自明。 -/
theorem splitFin_ap152 {x : Term} (hap : x.isAP = true) (hne : (x == one) = false) :
    splitFin x = (x, 0) := by
  show (ofList ((toList x).take ((toList x).length -
      ((toList x).reverse.takeWhile (· == one)).length)),
    ((toList x).reverse.takeWhile (· == one)).length) = _
  rw [toList_isAP81 hap,
    show ([x].reverse : List Term) = [x] from rfl,
    show ([x].takeWhile (· == one) : List Term) = [] from by
      rw [List.takeWhile_cons, hne]
      rfl]
  rfl

/-- 単独の AP で `1` でない項の `dnArg` は恒等。 -/
theorem dnArg_ap152 {x : Term} (hap : x.isAP = true) (hne : (x == one) = false) :
    dnArg x = x := by
  rw [dnArg_eq104, splitFin_ap152 hap hne]
  rw [if_neg (by intro hc; omega)]

/-- **`ω^·` の形 — `M` 未満で不動点でも `1` の裾でもなければ `φ̄0` を被せるだけ。** -/
theorem omegaNF_shape152 {x : Term} (hM : lt M x = false) (hMne : (x == M) = false)
    (hfp : isFP zero x = false) (hdn : dnArg x = x) :
    omegaNF x = phi zero x := by
  show (if lt M x then omg x else if x == M then M else phiNF zero x) = _
  rw [hM, if_neg (by exact Bool.noConfusion), hMne, if_neg (by exact Bool.noConfusion),
    phiNF_zero_eq104, hfp, if_neg (by exact Bool.noConfusion), hdn]

end

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §152.3 The residual tower `UW152` over a seed `s < Ω₁`, and its scan

`UW152 s m = ω^ω^…^(Ω₁ ⊕ s)` — the `dict`-image of `ψ₁^{m+1}(ψ₀ e)` when `dict (ψ₀ e) = s`.
The cluster mirrors §139's `TWG139` machinery. -/

/-- `Ω₁ ⊕ s` の上に積んだ φ̄0 の塔。 -/
def UW152 (s : Term) : Nat → Term
  | 0 => phi zero (add (Z zero) s)
  | m + 1 => phi zero (UW152 s m)

theorem deg_UW152 (s : Term) : ∀ (j : Nat), (UW152 s j).deg = 2 * j + 5 + s.deg
  | 0 => by show 1 + 1 + (1 + (1 + 1) + s.deg) = 2 * 0 + 5 + s.deg; omega
  | j + 1 => by
      show 1 + 1 + (UW152 s j).deg = 2 * (j + 1) + 5 + s.deg
      rw [deg_UW152 s j]
      omega

theorem beq_UW_zero152 (s : Term) : ∀ (j : Nat), ((UW152 s j : Term) == zero) = false
  | 0 => rfl
  | _ + 1 => rfl

theorem ne_zero_UW152 (s : Term) (j : Nat) : UW152 s j ≠ zero := by
  intro hc
  have h := beq_UW_zero152 s j
  rw [hc] at h
  simp at h

theorem beq_UW_one152 (s : Term) : ∀ (j : Nat), ((UW152 s j : Term) == TM.Term.one) = false
  | 0 => rfl
  | j + 1 => by
      refine beq_eq_false_iff_ne.mpr ?_
      intro hc
      have hc2 : phi zero (UW152 s j) = phi zero zero := hc
      injection hc2 with h1 h2
      exact ne_zero_UW152 s j h2

theorem beq_UWs_one152 (s : Term) (j : Nat) :
    ((phi zero (UW152 s j) : Term) == TM.Term.one) = false := beq_UW_one152 s (j + 1)

theorem beq_UW_Om152 (s : Term) : ∀ (j : Nat), ((UW152 s j : Term) == Z zero) = false
  | 0 => rfl
  | _ + 1 => rfl

theorem beq_Om_UW152 (s : Term) : ∀ (j : Nat), ((Z zero : Term) == UW152 s j) = false
  | 0 => rfl
  | _ + 1 => rfl

/-- `Ω₁ < ω^…^(Ω₁ ⊕ s)` — 燃料の下ごしらえ。 -/
theorem ltF_Om_UW152 (s : Term) :
    ∀ (j f : Nat), j + 3 ≤ f → ltF f (Z zero) (UW152 s j) = true
  | _, 0, hh => absurd hh (by omega)
  | 0, g + 1, hg => by
      show (((Z zero : Term) == zero) || ((Z zero : Term) == add (Z zero) s)
            || ltF g (Z zero) zero || ltF g (Z zero) (add (Z zero) s)) = true
      rw [show ltF g (Z zero) (add (Z zero) s) = true from by
        cases g with
        | zero => omega
        | succ g' =>
            show (((Z zero : Term) == Z zero) || ltF g' (Z zero) (Z zero)) = true
            rfl]
      simp
  | j + 1, g + 1, hg => by
      show (((Z zero : Term) == zero) || ((Z zero : Term) == UW152 s j)
            || ltF g (Z zero) zero || ltF g (Z zero) (UW152 s j)) = true
      rw [ltF_Om_UW152 s j g (by omega)]
      simp

theorem lt_Om_UW152 (s : Term) (j : Nat) : lt (Z zero) (UW152 s j) = true := by
  rw [lt_eq_ltF (Z zero) (UW152 s j) (2 * ((Z zero : Term).deg + (UW152 s j).deg) + 8)
    (by omega)]
  exact ltF_Om_UW152 s j _ (by rw [deg_UW152 s j]; show j + 3 ≤ 2 * (2 + (2 * j + 5 + s.deg)) + 8; omega)

theorem le_reg1_UW152 (s : Term) (j : Nat) : le (reg 1) (UW152 s j) = true := by
  show (((Z zero : Term) == UW152 s j) || lt (Z zero) (UW152 s j)) = true
  rw [lt_Om_UW152 s j]
  exact Bool.or_true _

/-- 塔は `Ω₁` の下に居ない。 -/
theorem lt_UW_reg1_152 {s : Term} (hlt : lt s (reg 1) = true) :
    ∀ (j : Nat), lt (UW152 s j) (reg 1) = false
  | 0 => by
      show lt (phi zero (add (Z zero) s)) (reg 1) = false
      rw [lt_phi_reg1_100,
        show lt (add (Z zero) s) (reg 1) = false from by
          rw [lt_add_nsum (by intro hc; exact Term.noConfusion hc) rfl]
          show lt (Z zero) (Z zero) = false
          exact lt_irrefl _]
      exact Bool.and_false _
  | j + 1 => by
      show lt (phi zero (UW152 s j)) (reg 1) = false
      rw [lt_phi_reg1_100, lt_UW_reg1_152 hlt j]
      exact Bool.and_false _

theorem le_UW_reg1_152 {s : Term} (hlt : lt s (reg 1) = true) (j : Nat) :
    le (UW152 s j) (reg 1) = false := by
  show (((UW152 s j : Term) == Z zero) || lt (UW152 s j) (Z zero)) = false
  rw [beq_UW_Om152 s j, show lt (UW152 s j) (Z zero) = false from lt_UW_reg1_152 hlt j]
  rfl

theorem phiShifted_UW152 (s : Term) : ∀ (j : Nat), phiShifted zero (UW152 s j) = false
  | 0 => phiShifted_phi0_135 (show ((phi zero (add (Z zero) s) : Term) == TM.Term.one) = false from rfl)
  | j + 1 => phiShifted_phi0_135 (beq_UWs_one152 s j)

theorem logOm_UW152 (s : Term) (j : Nat) : logOm (UW152 s (j + 1)) = UW152 s j :=
  logOm_phi0_135 (phiShifted_UW152 s j)

theorem omegaNF_UW152 (s : Term) : ∀ (j : Nat), omegaNF (UW152 s j) = UW152 s (j + 1)
  | 0 => omegaNF_phi0_135 (show ((phi zero (add (Z zero) s) : Term) == TM.Term.one) = false from rfl)
  | j + 1 => omegaNF_phi0_135 (beq_UWs_one152 s j)

theorem subAP_UW152 (s : Term) : ∀ (j : Nat), subAP (reg 1) (UW152 s j) = UW152 s j
  | 0 => rfl
  | _ + 1 => rfl

theorem plus_Om1_UW152 {s : Term} (hlt : lt s (reg 1) = true) (j : Nat) :
    plus (reg 1) (UW152 s j) = UW152 s j := by
  cases j with
  | zero =>
      show ofList (List.filter (fun a => le (phi zero (add (Z zero) s)) a) [Z zero]
        ++ [phi zero (add (Z zero) s)]) = _
      rw [show List.filter (fun a => le (phi zero (add (Z zero) s)) a) [Z zero] = [] from by
        show (match le (phi zero (add (Z zero) s)) (Z zero) with
              | true => Z zero
                  :: List.filter (fun a => le (phi zero (add (Z zero) s)) a) []
              | false => List.filter (fun a => le (phi zero (add (Z zero) s)) a) []) = []
        rw [show le (phi zero (add (Z zero) s)) (Z zero) = false from le_UW_reg1_152 hlt 0]
        rfl]
      rfl
  | succ j =>
      show ofList (List.filter (fun a => le (phi zero (UW152 s j)) a) [Z zero]
        ++ [phi zero (UW152 s j)]) = _
      rw [show List.filter (fun a => le (phi zero (UW152 s j)) a) [Z zero] = [] from by
        show (match le (phi zero (UW152 s j)) (Z zero) with
              | true => Z zero :: List.filter (fun a => le (phi zero (UW152 s j)) a) []
              | false => List.filter (fun a => le (phi zero (UW152 s j)) a) []) = []
        rw [show le (phi zero (UW152 s j)) (Z zero) = false from le_UW_reg1_152 hlt (j + 1)]
        rfl]
      rfl

theorem mulL_Om1_UW152 {s : Term} (hlt : lt s (reg 1) = true) (j : Nat) :
    mulL (reg 1) (UW152 s (j + 1)) = UW152 s (j + 1) := by
  show ofList [omegaNF (plus (reg 1) (logOm (UW152 s (j + 1))))] = _
  rw [logOm_UW152 s j, plus_Om1_UW152 hlt j, omegaNF_UW152 s j]
  rfl

theorem mulL_UW_one152 (s : Term) (j : Nat) :
    mulL (UW152 s j) TM.Term.one = UW152 s (j + 1) := by
  show ofList [omegaNF (plus (UW152 s j) (logOm TM.Term.one))] = _
  rw [show logOm TM.Term.one = zero from rfl,
    show plus (UW152 s j) zero = UW152 s j from rfl, omegaNF_UW152 s j]
  rfl

theorem sub1_UW152 (s : Term) (j : Nat) : sub1 (UW152 s j) = UW152 s j := by
  cases j with
  | zero =>
      show (match toList (UW152 s 0) with
            | [] => zero
            | p :: rest => if p == TM.Term.one then ofList rest else UW152 s 0) = _
      show (if (UW152 s 0 : Term) == TM.Term.one then ofList [] else UW152 s 0) = _
      rw [show ((UW152 s 0 : Term) == TM.Term.one) = false from rfl]
      rfl
  | succ j =>
      show (match toList (UW152 s (j + 1)) with
            | [] => zero
            | p :: rest => if p == TM.Term.one then ofList rest else UW152 s (j + 1)) = _
      show (if (UW152 s (j + 1) : Term) == TM.Term.one then ofList [] else UW152 s (j + 1)) = _
      rw [beq_UW_one152 s (j + 1)]
      rfl

theorem filter_ge_UW152 {s : Term} (hlt : lt s (reg 1) = true) (j : Nat) :
    List.filter (fun q => !lt q (reg 1)) [UW152 s j] = [UW152 s j] := by
  show (match (!lt (UW152 s j) (reg 1)) with
        | true => UW152 s j :: List.filter (fun q => !lt q (reg 1)) []
        | false => List.filter (fun q => !lt q (reg 1)) []) = _
  rw [lt_UW_reg1_152 hlt j]
  rfl

theorem filter_lt_UW152 {s : Term} (hlt : lt s (reg 1) = true) (j : Nat) :
    List.filter (fun q => lt q (reg 1)) [UW152 s j] = [] := by
  show (match (lt (UW152 s j) (reg 1)) with
        | true => UW152 s j :: List.filter (fun q => lt q (reg 1)) []
        | false => List.filter (fun q => lt q (reg 1)) []) = _
  rw [lt_UW_reg1_152 hlt j]
  rfl

/-- **発火する段の `wcnf` — 桁は一つ、指数は一段下の塔。** -/
theorem wA_UW152 {s : Term} (hlt : lt s (reg 1) = true) (j : Nat) :
    wA (reg 1) (UW152 s (j + 2)) = UW152 s (j + 1) := by
  show ofList (List.map (divAP (reg 1)) (List.filter (fun q => !lt q (reg 1))
    (toList (logOm (UW152 s (j + 2)))))) = _
  rw [logOm_UW152 s (j + 1),
    show toList (UW152 s (j + 1)) = [UW152 s (j + 1)] from rfl,
    filter_ge_UW152 hlt (j + 1)]
  show ofList [divAP (reg 1) (UW152 s (j + 1))] = _
  show ofList [omegaNF (subAP (reg 1) (logOm (UW152 s (j + 1))))] = _
  rw [logOm_UW152 s j, subAP_UW152 s j, omegaNF_UW152 s j]
  rfl

theorem wC_UW152 {s : Term} (hlt : lt s (reg 1) = true) (j : Nat) :
    wC (reg 1) (UW152 s (j + 2)) = TM.Term.one := by
  show omegaNF (ofList (List.filter (fun q => lt q (reg 1))
    (toList (logOm (UW152 s (j + 2)))))) = _
  rw [logOm_UW152 s (j + 1),
    show toList (UW152 s (j + 1)) = [UW152 s (j + 1)] from rfl,
    filter_lt_UW152 hlt (j + 1)]
  exact omegaNF_zero135

theorem wcnf_UW152 {s : Term} (hlt : lt s (reg 1) = true) (j : Nat) :
    wcnf (reg 1) [UW152 s (j + 2)] = ([(UW152 s (j + 1), TM.Term.one)], zero) := by
  rw [wcnf_cons_ge (lt_UW_reg1_152 hlt (j + 2))]
  show ([(wA (reg 1) (UW152 s (j + 2)), wC (reg 1) (UW152 s (j + 2)))], zero) = _
  rw [wA_UW152 hlt j, wC_UW152 hlt j]

/-- **発火する段の吐く指数は塔そのもの。** -/
theorem idx_UW152 {s : Term} (hlt : lt s (reg 1) = true) (j : Nat) :
    idxOf (reg 1) ((none : Option Term), (none : Option Term))
      (UW152 s (j + 1), TM.Term.one) = UW152 s (j + 2) := by
  show sub1 (mulL (mulL (reg 1) (subAP (reg 1) (UW152 s (j + 1)))) TM.Term.one) = _
  rw [subAP_UW152 s (j + 1), mulL_Om1_UW152 hlt j, mulL_UW_one152 s (j + 1),
    sub1_UW152 s (j + 2)]
end

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §152.4 Closed forms: the family's dict-images are exactly the towers -/

theorem nst_psiTow152 : ∀ (k : Nat), nst132 k BT.zero = psiTow k
  | 0 => rfl
  | k + 1 => congrArg (BT.D 1) (nst_psiTow152 k)

/-- `ψ₀` の引数の塔の値。§139 の `dict_psiTow139` を `nst132` の言葉で。 -/
theorem dict_bT152 (j : Nat) : dict (nst132 (j + 2) BT.zero) = TW (j + 1) := by
  rw [nst_psiTow152 (j + 2)]
  exact dict_psiTow139 j

/-- 種 — `dict (ψ₀(ψ₁^k 0))`。 -/
def sd152 (k : Nat) : Term := dict (BT.D 0 (nst132 k BT.zero))

theorem sd0_152 : sd152 0 = TM.Term.one := by decide
theorem sd1_152 : sd152 1 = phi TM.Term.one zero := by decide
theorem sd2_152 : sd152 2 = phi (add TM.Term.one TM.Term.one) zero := by decide
theorem sd3_152 : sd152 3 = psi (Z zero) zero := by decide

/-- **`k ≥ 4` の種は `ψ_{Ω₁}(塔)` そのもの。**  §139 の `collapse0_TW139`。 -/
theorem sd_psi152 (j : Nat) : sd152 (j + 4) = psi (Z zero) (TW (j + 3)) := by
  show dict (BT.D 0 (nst132 (j + 4) BT.zero)) = _
  rw [Trans.Dict.dict_D, nst_psiTow152 (j + 4), dict_psiTow139 (j + 2)]
  exact collapse0_TW139 j

/-- `k ≥ 3` の種の資料 — AP・`1` でない・`Ω₁` より下・`Ω₂` より下。 -/
theorem sd_facts152 : ∀ (k : Nat), (sd152 (k + 3)).isAP = true
    ∧ ((sd152 (k + 3) : Term) == TM.Term.one) = false
    ∧ lt (sd152 (k + 3)) (reg 1) = true
    ∧ lt (sd152 (k + 3)) (reg 2) = true
    ∧ lt (Z zero) (sd152 (k + 3)) = false
  | 0 => by
      rw [sd3_152]
      exact ⟨rfl, rfl, lt_psiOm_reg1_139 zero,
        lt_psiOm_Om2_139 zero, lt_Om_psi141 zero⟩
  | j + 1 => by
      rw [show j + 1 + 3 = j + 4 from rfl, sd_psi152 j]
      exact ⟨rfl, rfl, lt_psiOm_reg1_139 (TW (j + 3)),
        lt_psiOm_Om2_139 (TW (j + 3)), lt_Om_psi141 (TW (j + 3))⟩

/-- `⊕` の形では `splitFin` は動かない — 種は `1` でないので。 -/
theorem splitFin_addOm152 {s : Term} (hap : s.isAP = true) (hone : (s == TM.Term.one) = false) :
    splitFin (add (Z zero) s) = (add (Z zero) s, 0) := by
  show (ofList ((Z zero :: toList s).take ((Z zero :: toList s).length
          - ((Z zero :: toList s).reverse.takeWhile (· == TM.Term.one)).length)),
        ((Z zero :: toList s).reverse.takeWhile (· == TM.Term.one)).length) = _
  rw [toList_isAP81 hap,
    show ([Z zero, s].reverse : List Term) = [s, Z zero] from rfl,
    show List.takeWhile (· == TM.Term.one) [s, Z zero] = [] from by
      rw [List.takeWhile_cons, hone]
      rfl]
  rfl

theorem omegaNF_addOm152 {s : Term} (hap : s.isAP = true) (hone : (s == TM.Term.one) = false) :
    omegaNF (add (Z zero) s) = phi zero (add (Z zero) s) := by
  show (if lt M (add (Z zero) s) = true then omg (add (Z zero) s)
        else if ((add (Z zero) s : Term) == M) = true then M
        else phiNF zero (add (Z zero) s)) = _
  rw [if_neg (by rw [show lt M (add (Z zero) s) = false from ltF_M_addOm135 s _]
                 exact Bool.noConfusion),
    if_neg (by intro hc; exact Bool.noConfusion hc)]
  show phiNFsucc zero (add (Z zero) s) = _
  unfold phiNFsucc
  rw [splitFin_addOm152 hap hone]
  rfl

/-- **底 — `ψ₁(ψ₀ e)` の値は `ω^(Ω₁ ⊕ s)`。** -/
theorem collapse1_seed152 {s : Term} (hap : s.isAP = true) (hone : (s == TM.Term.one) = false)
    (hlt : lt s (reg 1) = true) (hlt2 : lt s (reg 2) = true) :
    collapse 1 s = phi zero (add (Z zero) s) := by
  show omegaNF (plus (reg 1) (plus
    (((wcnf (reg 2) (toList s)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 2) (baseOf 1))).2.getD zero)
    ((wcnf (reg 2) (toList s)).2))) = _
  rw [toList_isAP81 hap, wcnf_cons_lt hlt2]
  show omegaNF (plus (reg 1) (plus zero (ofList [s]))) = _
  rw [show (ofList [s] : Term) = s from rfl, plus_zero_left hap,
    plus_reg1_ap152 hap (le_of_lt hlt)]
  exact omegaNF_addOm152 hap hone

/-- 段の上がり — `ψ₁` を一枚被せる。 -/
theorem collapse1_UW152 {s : Term} (hlt : lt s (reg 1) = true) (j : Nat) :
    collapse 1 (UW152 s j) = UW152 s (j + 1) := by
  have hW2 : ∀ i, lt (UW152 s i) (Z TM.Term.one) = true := by
    intro i
    induction i with
    | zero =>
        show lt (phi zero (add (Z zero) s)) (Z TM.Term.one) = true
        rw [lt_phi_Z103,
          show lt (add (Z zero) s) (Z TM.Term.one) = true from by
            rw [lt_add_nsum (by intro hc; exact Term.noConfusion hc) rfl]
            exact lt_Om_Om2_139,
          lt_zero_left (by intro hc; exact Term.noConfusion hc)]
        rfl
    | succ i ih =>
        show lt (phi zero (UW152 s i)) (Z TM.Term.one) = true
        rw [lt_phi_Z103, ih, lt_zero_left (by intro hc; exact Term.noConfusion hc)]
        rfl
  cases j with
  | zero =>
      exact collapse1_phi0_139 (show ((phi zero (add (Z zero) s) : Term) == TM.Term.one) = false from rfl)
        (hW2 0) (le_UW_reg1_152 hlt 0)
  | succ j =>
      exact collapse1_phi0_139 (beq_UWs_one152 s j) (hW2 (j + 1)) (le_UW_reg1_152 hlt (j + 1))

/-- **閉じた形 — 族の像は塔そのもの。**  `dict (ψ₁^{m+1}(ψ₀(ψ₁^{k+3} 0))) = UW152 (種) m`。 -/
theorem dict_famB152 (k : Nat) : ∀ (m : Nat),
    dict (famB132 (m + 1) (k + 3)) = UW152 (sd152 (k + 3)) m
  | 0 => by
      obtain ⟨hap, hone, hlt, hlt2, _⟩ := sd_facts152 k
      show collapse 1 (dict (nst132 0 (BT.D 0 (nst132 (k + 3) BT.zero)))) = _
      show collapse 1 (sd152 (k + 3)) = _
      exact collapse1_seed152 hap hone hlt hlt2
  | m + 1 => by
      obtain ⟨_, _, hlt, _, _⟩ := sd_facts152 k
      show collapse 1 (dict (famB132 (m + 1) (k + 3))) = _
      rw [dict_famB152 k m]
      exact collapse1_UW152 hlt m

end

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §152.5 The K-sets of the towers -/

/-- `ψ₁` の塔の `K_{Ω₁}` は空。 -/
theorem Kset_TW152 : ∀ (j : Nat), Kset (reg 1) (TW j) = []
  | 0 => rfl
  | j + 1 => Kset_TW152 j

/-- **`UW` の塔の `K_{Ω₁}` は種の `K_{Ω₁}` そのもの。** -/
theorem Kset_UW152 (s : Term) : ∀ (j : Nat), Kset (reg 1) (UW152 s j) = Kset (reg 1) s
  | 0 => rfl
  | j + 1 => Kset_UW152 s j

/-- `k = 3` の種の `K` は `{0}`。 -/
theorem Kset_sd3_152 : Kset (reg 1) (sd152 3) = [zero] := by
  rw [sd3_152, Kset_psi_reg152]
  rfl

/-- **`k ≥ 4` の種の `K` は逃げる元ひとつ — 塔 `TW (j+3)` そのもの。** -/
theorem Kset_sd_psi152 (j : Nat) : Kset (reg 1) (sd152 (j + 4)) = [TW (j + 3)] := by
  rw [sd_psi152 j, Kset_psi_reg152, Kset_TW152 (j + 3)]

/-! ### §152.6 The tower-shape comparison, both directions

`y = TW (k-1) = ω^…^(Ω₁ ⊕ Ω₁)` (`k-1` layers), `i = UW152 s (m-1) = ω^…^(Ω₁ ⊕ s)`
(`m` layers) with `s = ψ_{Ω₁}(y) < Ω₁`.  At equal heights the bottoms decide —
`Ω₁ ⊕ s < Ω₁ ⊕ Ω₁` — so `y < i` iff the `y`-tower is strictly lower: `k ≤ m`. -/

theorem nsum_UW152 (s : Term) : ∀ (j : Nat), NSum (UW152 s j) = true
  | 0 => rfl
  | _ + 1 => rfl

/-- **標準の側 — 低い塔は高い塔より下。** `a ≤ b` なら `TW a < UW b`。 -/
theorem lt_TW_UW152 (s : Term) : ∀ (a b : Nat), a ≤ b → lt (TW a) (UW152 s b) = true
  | 0, b, _ => by
      show lt (add (Z zero) (Z zero)) (UW152 s b) = true
      rw [lt_add_nsum (ne_zero_UW152 s b) (nsum_UW152 s b)]
      exact lt_Om_UW152 s b
  | a + 1, 0, h => absurd h (by omega)
  | a + 1, b + 1, h => by
      show lt (phi zero (TW a)) (phi zero (UW152 s b)) = true
      rw [lt_phi_same139]
      exact lt_TW_UW152 s a b (by omega)

/-- `φ̄`-の頭は `⊕` の頭とだけ比べる (2.3.11 の右側)。 -/
theorem lt_phi_add152 (a b c d : Term) :
    lt (phi a b) (add c d) = (((phi a b : Term) == c) || lt (phi a b) c) := by
  rw [lt_eq_ltF_succ, ltF_succ_phi_add,
    show ltF (2 * ((phi a b).deg + (add c d).deg) + 7) (phi a b) c = lt (phi a b) c from
      (lt_eq_ltF (phi a b) c _ (by
        show (1 + a.deg + b.deg) + c.deg
          ≤ 2 * ((1 + a.deg + b.deg) + (1 + c.deg + d.deg)) + 7
        omega)).symm]

/-- 塔は底 `Ω₁ ⊕ s` より下に居ない — `s` が `Ω₁` より下なら。 -/
theorem lt_TW_addOm152 {s : Term} (hOms : lt (Z zero) s = false) :
    ∀ (a : Nat), lt (TW a) (add (Z zero) s) = false
  | 0 => by
      show lt (add (Z zero) (Z zero)) (add (Z zero) s) = false
      rw [lt_add_same139]
      exact hOms
  | a + 1 => by
      show lt (phi zero (TW a)) (add (Z zero) s) = false
      rw [lt_phi_add152,
        show ((phi zero (TW a) : Term) == Z zero) = false from rfl,
        show lt (phi zero (TW a)) (Z zero) = false from lt_TW_Om138' (a + 1)]
      rfl

/-- **発散の側 — 高い塔は低い塔より下に居ない。** `b < a` なら `TW a < UW b` は成り立たない。 -/
theorem lt_TW_UW_false152 {s : Term} (hOms : lt (Z zero) s = false) :
    ∀ (b a : Nat), b < a → lt (TW a) (UW152 s b) = false
  | 0, 0, h => absurd h (by omega)
  | 0, a + 1, _ => by
      show lt (phi zero (TW a)) (phi zero (add (Z zero) s)) = false
      rw [lt_phi_same139]
      exact lt_TW_addOm152 hOms a
  | b + 1, 0, h => absurd h (by omega)
  | b + 1, a + 1, h => by
      show lt (phi zero (TW a)) (phi zero (UW152 s b)) = false
      rw [lt_phi_same139]
      exact lt_TW_UW_false152 hOms b a (by omega)

end

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §152.7 The gate on the family, both sides -/

/-- **一段ぶんの門 — 種の `K` の元がみな塔より下なら、その段の義務はぜんぶ済む。** -/
theorem stepOK_UW152 {s : Term} (hlt : lt s (reg 1) = true) (j : Nat)
    (H : ∀ y ∈ Kset (reg 1) s, lt y (UW152 s (j + 2)) = true) :
    KsetStepOK 0 (UW152 s (j + 2)) := by
  intro p hp hle
  replace hp : p ∈ scanSt (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
      (wcnf (reg 1) [UW152 s (j + 2)]).1 := hp
  rw [wcnf_UW152 hlt j] at hp
  replace hp : p = (((none : Option Term), (none : Option Term)),
      (UW152 s (j + 1), TM.Term.one)) := List.mem_singleton.mp hp
  subst hp
  constructor
  · intro i0 hi0
    have hi0x : (none : Option Term) = some i0 := hi0
    cases hi0x
  · intro y hy
    show lt y (idxOf (reg 1) ((none : Option Term), (none : Option Term))
      (UW152 s (j + 1), TM.Term.one)) = true
    rw [idx_UW152 hlt j]
    rcases hy with h | h
    · rw [show (((none : Option Term), (none : Option Term)),
          (UW152 s (j + 1), TM.Term.one)).2.1 = UW152 s (j + 1) from rfl,
        Kset_UW152 s (j + 1)] at h
      exact H y h
    · rw [show (((none : Option Term), (none : Option Term)),
          (UW152 s (j + 1), TM.Term.one)).2.2 = TM.Term.one from rfl] at h
      exact absurd h (by intro hc; cases hc)

/-- **第一の門は族の標準側の全域で成り立つ (`3 ≤ k ≤ m`)。**  逃げる元は
    `y = TW (k-1)` ひとつ (`k = 3` では `0`)、指数は `UW152 s (m-1)`、そして
    低い塔は高い塔より下 (`lt_TW_UW152`)。 -/
theorem ksetStepOK_famB152 {m k : Nat} (h3 : 3 ≤ k) (hkm : k ≤ m) :
    KsetStepOK 0 (dict (famB132 m k)) := by
  obtain ⟨kk, rfl⟩ : ∃ kk, k = kk + 3 := ⟨k - 3, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, m = (kk + d) + 3 := ⟨m - (kk + 3), by omega⟩
  obtain ⟨hap, hone, hlt, hlt2, hOms⟩ := sd_facts152 kk
  rw [show kk + d + 3 = (kk + d + 2) + 1 from rfl, dict_famB152 kk (kk + d + 2)]
  refine stepOK_UW152 hlt (kk + d) ?_
  intro y hy
  cases kk with
  | zero =>
      rw [Kset_sd3_152] at hy
      replace hy : y = zero := List.mem_singleton.mp hy
      subst hy
      exact lt_zero_left (ne_zero_UW152 _ _)
  | succ j =>
      rw [show j + 1 + 3 = j + 4 from rfl, Kset_sd_psi152 j] at hy
      replace hy : y = TW (j + 3) := List.mem_singleton.mp hy
      subst hy
      exact lt_TW_UW152 _ (j + 3) (j + 1 + d + 2) (by omega)

/-- **発散の側 — `3 ≤ m < k` では門の一歩は成り立たない。**  逃げる元 `y = TW (k-1)`
    が指数 `UW152 s (m-1)` より下に居ない (`lt_TW_UW_false152`)。§130 の `min130`
    (`m = 3, k = 4`) を全ての高さに広げたもの。 -/
theorem not_ksetStepOK_famB152 {m k : Nat} (h3 : 3 ≤ m) (hmk : m < k) :
    ¬ KsetStepOK 0 (dict (famB132 m k)) := by
  obtain ⟨mm, rfl⟩ : ∃ mm, m = mm + 3 := ⟨m - 3, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, k = (mm + d + 1) + 3 := ⟨k - (mm + 4), by omega⟩
  obtain ⟨hap, hone, hlt, hlt2, hOms⟩ := sd_facts152 (mm + d + 1)
  intro H
  rw [show mm + 3 = (mm + 2) + 1 from rfl, dict_famB152 (mm + d + 1) (mm + 2)] at H
  have hp : (((none : Option Term), (none : Option Term)),
      (UW152 (sd152 (mm + d + 1 + 3)) (mm + 1), TM.Term.one))
      ∈ scanSt (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (wcnf (reg 1) [UW152 (sd152 (mm + d + 1 + 3)) (mm + 2)]).1 := by
    rw [wcnf_UW152 hlt (mm)]
    exact List.Mem.head _
  have hstep := (H _ hp (le_reg1_UW152 _ (mm + 1))).2 (TW (mm + d + 3)) (Or.inl (by
    show TW (mm + d + 3) ∈ Kset (reg 1) (UW152 (sd152 (mm + d + 1 + 3)) (mm + 1))
    rw [Kset_UW152, show mm + d + 1 + 3 = mm + d + 4 from rfl, Kset_sd_psi152 (mm + d)]
    exact List.Mem.head _))
  rw [show idxOf (reg (0 + 1)) (((none : Option Term), (none : Option Term)))
        (UW152 (sd152 (mm + d + 1 + 3)) (mm + 1), TM.Term.one)
      = UW152 (sd152 (mm + d + 1 + 3)) (mm + 2) from idx_UW152 hlt (mm),
    lt_TW_UW_false152 hOms (mm + 2) (mm + d + 3) (by omega)] at hstep
  exact Bool.noConfusion hstep

end

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §152.8 The small seeds (`k ≤ 2`), and `inT` along the family -/

theorem btLe_nst152 {w : BT} (hb : btLe72 1 w = true) :
    ∀ (m : Nat), btLe72 1 (nst132 m w) = true
  | 0 => hb
  | m + 1 => by
      show (decide (1 ≤ 1) && btLe72 1 (nst132 m w)) = true
      rw [btLe_nst152 hb m]
      rfl

/-- `inT` と `< M` は塔を上がっても保たれる — §73.4 の門は段 1 では無条件なので。 -/
theorem nst_inT152 {w : BT} (hb : btLe72 1 w = true)
    (h0 : inT (dict w) = true ∧ lt (dict w) M = true) :
    ∀ (m : Nat), inT (dict (nst132 m w)) = true ∧ lt (dict (nst132 m w)) M = true
  | 0 => h0
  | m + 1 => by
      have ih := nst_inT152 hb h0 m
      have hbm := btLe_nst152 hb m
      show inT (dict (BT.D 1 (nst132 m w))) = true ∧ lt (dict (BT.D 1 (nst132 m w))) M = true
      rw [Trans.Dict.dict_D]
      exact inT_collapse_gap3 1 (dict (nst132 m w)) ih.1 ih.2
        (psiIdxOK_of_stepOK 1 (dict (nst132 m w)) ih.1 ih.2
          (ksetStepOK_one73 (nst132 m w) hbm))

/-- 種の `K` が空なら、塔のどの段の `K` も空。 -/
theorem nst_kempty152 {w : BT} (hb : btLe72 1 w = true)
    (h0 : inT (dict w) = true ∧ lt (dict w) M = true)
    (hK : ∀ y, y ∈ Kset (reg 1) (dict w) → False) :
    ∀ (m : Nat), ∀ y, y ∈ Kset (reg 1) (dict (nst132 m w)) → False
  | 0 => hK
  | m + 1 => by
      intro y hy
      have ih := nst_kempty152 hb h0 hK m
      have hbm := btLe_nst152 hb m
      rw [show dict (nst132 (m + 1) w) = dict (BT.D 1 (nst132 m w)) from rfl,
        dict_D1_inT145 (nst132 m w) hbm (nst_inT152 hb h0 m).1] at hy
      rcases mem_Kset_plus (mem_Kset_omegaNF hy) with h1 | h1
      · exact mem_Kset_reg 1 h1
      · exact ih y h1

/-- `K` が空なら門の一歩は無条件。 -/
theorem stepOK_of_kempty152 {x : Term}
    (hK : ∀ y, y ∈ Kset (reg 1) x → False) : KsetStepOK 0 x := by
  refine ksetStepOK_of_bigNil132 0 x (fun y hy => ?_)
  obtain ⟨q, hq, hyq⟩ := (mem_KsetL_iff _ _ _).mp hy
  refine hK y ?_
  rw [Kset_eq_KsetL]
  exact (mem_KsetL_iff _ _ _).mpr ⟨q, bigPart_sub _ _ _ hq, hyq⟩

/-- `ψ₁` の裸の塔の門 — `K` が空だから。 -/
theorem stepOK_TW152 (j : Nat) : KsetStepOK 0 (TW j) :=
  stepOK_of_kempty152 (fun y hy => by rw [Kset_TW152 j] at hy; cases hy)

/-- `k ≤ 2` の族の門 — 種の `K` が空だから、どの `m` でも。 -/
theorem famB_small_gate152 {k : Nat}
    (hb : btLe72 1 (BT.D 0 (nst132 k BT.zero)) = true)
    (h1 : inT (sd152 k) = true) (h2 : lt (sd152 k) M = true)
    (hKe : Kset (reg 1) (sd152 k) = []) (m : Nat) :
    KsetStepOK 0 (dict (famB132 m k)) := by
  refine stepOK_of_kempty152 (nst_kempty152 hb ⟨h1, h2⟩ ?_ m)
  intro y hy
  have hy2 : y ∈ Kset (reg 1) (sd152 k) := hy
  rw [hKe] at hy2
  cases hy2

theorem ksetStepOK_famB0_152 (m : Nat) : KsetStepOK 0 (dict (famB132 m 0)) :=
  famB_small_gate152 (by decide) (by decide) (by decide) (by decide) m

theorem ksetStepOK_famB1_152 (m : Nat) : KsetStepOK 0 (dict (famB132 m 1)) :=
  famB_small_gate152 (by decide) (by decide) (by decide) (by decide) m

theorem ksetStepOK_famB2_152 (m : Nat) : KsetStepOK 0 (dict (famB132 m 2)) :=
  famB_small_gate152 (by decide) (by decide) (by decide) (by decide) m

end

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §152.9 The standardness boundary, the direction the gate needs

`m < k` breaks `BT.isStd (ψ₀ (famB132 m k))`: the tower `ψ₁^k 0` sits in `G(a,0)` but
not below `a`.  With §152.7 this closes the circle: **the wedge where the gate's step
fails is entirely outside the standard region, at every height.** -/

theorem noD0_bT152 : ∀ (k : Nat), noD0145 (nst132 k BT.zero) = true
  | 0 => rfl
  | k + 1 => by
      show (!((1 : Nat) == 0) && noD0145 (nst132 k BT.zero)) = true
      rw [noD0_bT152 k]
      rfl

theorem noD0_famB152 : ∀ (i k : Nat), noD0145 (famB132 i k) = false
  | 0, k => rfl
  | i + 1, k => by
      show (!((1 : Nat) == 0) && noD0145 (famB132 i k)) = false
      rw [noD0_famB152 i k]
      rfl

/-- 添字 0 の節の有無が違えば `==` は偽 — `BT` の構造的 `BEq` を直接下る。 -/
theorem beq_noD0_152 : ∀ (a b : BT), noD0145 a = true → noD0145 b = false →
    (a == b) = false
  | BT.zero, BT.zero, _, h2 => absurd h2 (by intro hc; exact Bool.noConfusion hc)
  | BT.zero, BT.D _ _, _, _ => rfl
  | BT.zero, BT.sum _ _, _, _ => rfl
  | BT.D _ _, BT.zero, _, _ => rfl
  | BT.D _ _, BT.sum _ _, _, _ => rfl
  | BT.sum _ _, BT.zero, _, _ => rfl
  | BT.sum _ _, BT.D _ _, _, _ => rfl
  | BT.D u x, BT.D v y, h1, h2 => by
      show ((u == v) && (x == y)) = false
      cases huv : (u == v) with
      | false => rfl
      | true =>
          have hv : u = v := eq_of_beq huv
          subst hv
          obtain ⟨hu0, hx⟩ := noD0143_D h1
          have hu : ((u == 0) : Bool) = false := by
            cases hc : ((u == 0) : Bool) with
            | false => rfl
            | true => exact absurd (eq_of_beq hc) hu0
          have hy : noD0145 y = false := by
            have h2' : (!(u == 0) && noD0145 y) = false := h2
            rw [hu] at h2'
            exact h2'
          rw [beq_noD0_152 x y hx hy]
          rfl
  | BT.sum x y, BT.sum p q, h1, h2 => by
      show ((x == p) && (y == q)) = false
      obtain ⟨hx, hy⟩ := noD0143_sum h1
      have h2' : (noD0145 p && noD0145 q) = false := h2
      rcases Bool.and_eq_false_iff.mp h2' with hp | hq
      · rw [beq_noD0_152 x p hx hp]
        rfl
      · rw [beq_noD0_152 y q hy hq]
        exact Bool.and_false _

theorem beq_bT_famB152 (j i k : Nat) : (nst132 j BT.zero == famB132 i k) = false :=
  beq_noD0_152 _ _ (noD0_bT152 j) (noD0_famB152 i k)

/-- **`m < k` では塔は族の項より下に居ない** — 燃料に依らず。 -/
theorem ltL_bT_famB_false152 (k : Nat) : ∀ (f : Nat), ∀ (j i : Nat), i ≤ j →
    BT.ltL f (BT.toL (nst132 (j + 1) BT.zero)) (BT.toL (famB132 i k)) = false
  | 0, _, _, _ => rfl
  | f + 1, j, 0, _ => by
      show (if (1 : Nat) < 0 then true else if (0 : Nat) < 1 then false
            else if nst132 j BT.zero == nst132 k BT.zero then BT.ltL f [] []
            else BT.ltL f (BT.toL (nst132 j BT.zero)) (BT.toL (nst132 k BT.zero))) = false
      rw [if_neg (by omega), if_pos (by omega)]
  | f + 1, j, i + 1, h => by
      obtain ⟨jj, rfl⟩ : ∃ jj, j = jj + 1 := ⟨j - 1, by omega⟩
      show (if (1 : Nat) < 1 then true else if (1 : Nat) < 1 then false
            else if nst132 (jj + 1) BT.zero == famB132 i k then BT.ltL f [] []
            else BT.ltL f (BT.toL (nst132 (jj + 1) BT.zero)) (BT.toL (famB132 i k))) = false
      rw [if_neg (by omega), if_neg (by omega),
        if_neg (by
          rw [beq_bT_famB152 (jj + 1) i k]
          exact Bool.noConfusion)]
      exact ltL_bT_famB_false152 k f jj i (by omega)

theorem bT_not_lt_famB152 {m k : Nat} (h : m < k) :
    BT.lt (nst132 k BT.zero) (famB132 m k) = false := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact ltL_bT_famB_false152 (j + 1) _ j m (by omega)

theorem bT_mem_GB152 (k : Nat) : ∀ (m : Nat), nst132 k BT.zero ∈ BT.GB 0 (famB132 m k)
  | 0 => by
      show nst132 k BT.zero
        ∈ (if 0 ≤ 0 then nst132 k BT.zero :: BT.GB 0 (nst132 k BT.zero) else [])
      rw [if_pos (by omega)]
      exact List.Mem.head _
  | m + 1 => by
      show nst132 k BT.zero
        ∈ (if 0 ≤ 1 then famB132 m k :: BT.GB 0 (famB132 m k) else [])
      rw [if_pos (by omega)]
      exact List.Mem.tail _ (bT_mem_GB152 k m)

/-- **`m < k` の族は `K` 標準でない。**  §132.5 の凍った境界の、この向きの半分。 -/
theorem not_std_famB152 {m k : Nat} (hmk : m < k) :
    BT.isStd (BT.D 0 (famB132 m k)) = false := by
  cases hs : BT.isStd (BT.D 0 (famB132 m k)) with
  | false => rfl
  | true =>
      exfalso
      have h0 : (BT.isStd (famB132 m k)
          && (BT.GB 0 (famB132 m k)).all (fun e => BT.lt e (famB132 m k))) = true := hs
      have h2 := List.all_eq_true.mp ((Bool.and_eq_true _ _).mp h0).2 _ (bT_mem_GB152 k m)
      rw [bT_not_lt_famB152 hmk] at h2
      exact Bool.noConfusion h2

/-- **主定理 — 族は第一の門をどの高さでも反証できない。**  `K` 標準なら門の一歩は定理。 -/
theorem famB_no_refute152 (m k : Nat) (hs : BT.isStd (BT.D 0 (famB132 m k)) = true) :
    KsetStepOK 0 (dict (famB132 m k)) := by
  by_cases hk : k ≤ 2
  · have hcase : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hcase with rfl | rfl | rfl
    · exact ksetStepOK_famB0_152 m
    · exact ksetStepOK_famB1_152 m
    · exact ksetStepOK_famB2_152 m
  · have h3 : 3 ≤ k := by omega
    have hkm : k ≤ m := by
      rcases Nat.lt_or_ge m k with h | h
      · exfalso
        rw [not_std_famB152 h] at hs
        exact Bool.noConfusion hs
      · omega
    exact ksetStepOK_famB152 h3 hkm

end

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §152.10 The sandwich, the per-term gate, and `PsiIdxOK` -/

/-- **吐かれる指数は塔の段の間に真に挟まる。**  `UW152 s b < TW (b+1)` —
    底の比較 `Ω₁ ⊕ s < Ω₁ ⊕ Ω₁` がそのまま上まで持ち上がる。`lt_TW_UW152` の
    `TW b < UW152 s b` と合わせて `TW b < UW152 s b < TW (b+1)`。 -/
theorem lt_UW_TW152 {s : Term} (hlt : lt s (reg 1) = true) :
    ∀ (b : Nat), lt (UW152 s b) (TW (b + 1)) = true
  | 0 => by
      show lt (phi zero (add (Z zero) s)) (phi zero (add (Z zero) (Z zero))) = true
      rw [lt_phi_same139, lt_add_same139]
      exact hlt
  | b + 1 => by
      show lt (phi zero (UW152 s b)) (phi zero (TW (b + 1))) = true
      rw [lt_phi_same139]
      exact lt_UW_TW152 hlt b

/-- **一項ぶんの門、§87 の帰納法が消費する形。** -/
theorem gateStd87_famB152 (m k : Nat) : GateStd87 (famB132 m k) :=
  fun _ hs => famB_no_refute152 m k hs

/-- 種は 𝔗(M) の中で `M` より下 — `k ≥ 4` は §139 の頭の形から、`k ≤ 3` は計算から。 -/
theorem inT_sd152 : ∀ (k : Nat), inT (sd152 k) = true ∧ lt (sd152 k) M = true
  | 0 => ⟨by decide, by decide⟩
  | 1 => ⟨by decide, by decide⟩
  | 2 => ⟨by decide, by decide⟩
  | 3 => ⟨by decide, by decide⟩
  | j + 4 => by
      have hbT : btLe72 1 (nst132 (j + 4) BT.zero) = true :=
        btLe_nst152 (by decide) (j + 4)
      have hin := inT_dict_noD0145 (nst132 (j + 4) BT.zero) hbT (noD0_bT152 (j + 4))
      have hstep : KsetStepOK 0 (dict (nst132 (j + 4) BT.zero)) := by
        rw [dict_bT152 (j + 2)]
        exact stepOK_TW152 (j + 3)
      show inT (dict (BT.D 0 (nst132 (j + 4) BT.zero))) = true
        ∧ lt (dict (BT.D 0 (nst132 (j + 4) BT.zero))) M = true
      rw [Trans.Dict.dict_D]
      exact inT_collapse_gap3 0 (dict (nst132 (j + 4) BT.zero)) hin.1 hin.2
        (psiIdxOK_of_stepOK 0 (dict (nst132 (j + 4) BT.zero)) hin.1 hin.2 hstep)

theorem btLe_famB152 (m k : Nat) : btLe72 1 (famB132 m k) = true :=
  btLe_nst152 (show btLe72 1 (BT.D 0 (nst132 k BT.zero)) = true from by
    show (decide (0 ≤ 1) && btLe72 1 (nst132 k BT.zero)) = true
    rw [btLe_nst152 (by decide) k]
    rfl) m

theorem inT_dict_famB152 (m k : Nat) :
    inT (dict (famB132 m k)) = true ∧ lt (dict (famB132 m k)) M = true :=
  nst_inT152 (show btLe72 1 (BT.D 0 (nst132 k BT.zero)) = true from by
    show (decide (0 ≤ 1) && btLe72 1 (nst132 k BT.zero)) = true
    rw [btLe_nst152 (by decide) k]
    rfl) (inT_sd152 k) m

/-- **2.1(vi) の条項そのもの、族の標準側の全域で。** -/
theorem psiIdxOK_famB152 (m k : Nat) (hs : BT.isStd (BT.D 0 (famB132 m k)) = true) :
    PsiIdxOK 0 (dict (famB132 m k)) :=
  psiIdxOK_of_stepOK 0 (dict (famB132 m k)) (inT_dict_famB152 m k).1
    (inT_dict_famB152 m k).2 (famB_no_refute152 m k hs)

end

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §152.11 The `BT`-side comparisons, the true direction -/

theorem beq_bT_bT152 : ∀ (j k : Nat), j ≠ k →
    (nst132 j BT.zero == nst132 k BT.zero) = false
  | 0, 0, h => absurd rfl h
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, _ => rfl
  | j + 1, k + 1, h => by
      show (nst132 j BT.zero == nst132 k BT.zero) = false
      exact beq_bT_bT152 j k (by omega)

theorem beq_famB_famB152 : ∀ (j m k : Nat), j ≠ m →
    (famB132 j k == famB132 m k) = false
  | 0, 0, _, h => absurd rfl h
  | 0, _ + 1, _, _ => rfl
  | _ + 1, 0, _, _ => rfl
  | j + 1, m + 1, k, h => by
      show (famB132 j k == famB132 m k) = false
      exact beq_famB_famB152 j m k (by omega)

theorem ltL_bT_bT_true152 : ∀ (f j k : Nat), j < k → j + 1 ≤ f →
    BT.ltL f (BT.toL (nst132 j BT.zero)) (BT.toL (nst132 k BT.zero)) = true
  | 0, _, _, _, hf => absurd hf (by omega)
  | f + 1, 0, k, hk, _ => by
      obtain ⟨kk, rfl⟩ : ∃ kk, k = kk + 1 := ⟨k - 1, by omega⟩
      rfl
  | f + 1, j + 1, k, hk, hf => by
      obtain ⟨kk, rfl⟩ : ∃ kk, k = kk + 1 := ⟨k - 1, by omega⟩
      show (if (1 : Nat) < 1 then true else if (1 : Nat) < 1 then false
            else if nst132 j BT.zero == nst132 kk BT.zero then BT.ltL f [] []
            else BT.ltL f (BT.toL (nst132 j BT.zero)) (BT.toL (nst132 kk BT.zero))) = true
      rw [if_neg (by omega), if_neg (by omega),
        if_neg (by
          rw [beq_bT_bT152 j kk (by omega)]
          exact Bool.noConfusion)]
      exact ltL_bT_bT_true152 f j kk (by omega) (by omega)

theorem ltL_bT_famB_true152 (k : Nat) : ∀ (f j i : Nat), j ≤ i → j + 1 ≤ f →
    BT.ltL f (BT.toL (nst132 j BT.zero)) (BT.toL (famB132 i k)) = true
  | 0, _, _, _, hf => absurd hf (by omega)
  | f + 1, 0, 0, _, _ => rfl
  | f + 1, 0, _ + 1, _, _ => rfl
  | f + 1, j + 1, i, hj, hf => by
      obtain ⟨ii, rfl⟩ : ∃ ii, i = ii + 1 := ⟨i - 1, by omega⟩
      show (if (1 : Nat) < 1 then true else if (1 : Nat) < 1 then false
            else if nst132 j BT.zero == famB132 ii k then BT.ltL f [] []
            else BT.ltL f (BT.toL (nst132 j BT.zero)) (BT.toL (famB132 ii k))) = true
      rw [if_neg (by omega), if_neg (by omega),
        if_neg (by
          rw [beq_bT_famB152 j ii k]
          exact Bool.noConfusion)]
      exact ltL_bT_famB_true152 k f j ii (by omega) (by omega)

theorem ltL_famB_famB_true152 (k : Nat) : ∀ (f j m : Nat), j < m → j + 1 ≤ f →
    BT.ltL f (BT.toL (famB132 j k)) (BT.toL (famB132 m k)) = true
  | 0, _, _, _, hf => absurd hf (by omega)
  | f + 1, 0, m, hm, _ => by
      obtain ⟨mm, rfl⟩ : ∃ mm, m = mm + 1 := ⟨m - 1, by omega⟩
      show (if (0 : Nat) < 1 then true else if (1 : Nat) < 0 then false
            else if BT.D 0 (nst132 k BT.zero) == famB132 mm k then BT.ltL f [] []
            else BT.ltL f (BT.toL (BT.D 0 (nst132 k BT.zero))) (BT.toL (famB132 mm k))) = true
      rw [if_pos (by omega)]
  | f + 1, j + 1, m, hm, hf => by
      obtain ⟨mm, rfl⟩ : ∃ mm, m = mm + 1 := ⟨m - 1, by omega⟩
      show (if (1 : Nat) < 1 then true else if (1 : Nat) < 1 then false
            else if famB132 j k == famB132 mm k then BT.ltL f [] []
            else BT.ltL f (BT.toL (famB132 j k)) (BT.toL (famB132 mm k))) = true
      rw [if_neg (by omega), if_neg (by omega),
        if_neg (by
          rw [beq_famB_famB152 j mm k (by omega)]
          exact Bool.noConfusion)]
      exact ltL_famB_famB_true152 k f j mm (by omega) (by omega)

theorem size_bT152 : ∀ (k : Nat), BT.size (nst132 k BT.zero) = k + 1
  | 0 => rfl
  | k + 1 => by
      show 1 + BT.size (nst132 k BT.zero) = k + 1 + 1
      rw [size_bT152 k]
      omega

theorem size_famB152 (k : Nat) : ∀ (m : Nat), BT.size (famB132 m k) = m + k + 2
  | 0 => by
      show 1 + BT.size (nst132 k BT.zero) = 0 + k + 2
      rw [size_bT152 k]
      omega
  | m + 1 => by
      show 1 + BT.size (famB132 m k) = m + 1 + k + 2
      rw [size_famB152 k m]
      omega

theorem lt_bT_bT152 {j k : Nat} (h : j < k) :
    BT.lt (nst132 j BT.zero) (nst132 k BT.zero) = true := by
  show BT.ltL (BT.size (nst132 j BT.zero) + BT.size (nst132 k BT.zero) + 2) _ _ = true
  exact ltL_bT_bT_true152 _ j k h (by rw [size_bT152 j, size_bT152 k]; omega)

theorem lt_bT_famB152 {i m : Nat} (k : Nat) (h : i ≤ m) :
    BT.lt (nst132 i BT.zero) (famB132 m k) = true := by
  show BT.ltL (BT.size (nst132 i BT.zero) + BT.size (famB132 m k) + 2) _ _ = true
  exact ltL_bT_famB_true152 k _ i m h (by rw [size_bT152 i, size_famB152 k m]; omega)

theorem lt_famB_famB152 {j m : Nat} (k : Nat) (h : j < m) :
    BT.lt (famB132 j k) (famB132 m k) = true := by
  show BT.ltL (BT.size (famB132 j k) + BT.size (famB132 m k) + 2) _ _ = true
  exact ltL_famB_famB_true152 k _ j m h (by rw [size_famB152 k j, size_famB152 k m]; omega)

end

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §152.12 The standardness boundary is exactly `k ≤ m` -/

theorem mem_GB1_bT152 : ∀ (k : Nat), ∀ e ∈ BT.GB 1 (nst132 k BT.zero),
    ∃ i, i < k ∧ e = nst132 i BT.zero
  | 0 => by intro e h; cases h
  | k + 1 => by
      intro e h
      have h2 : e ∈ (if 1 ≤ 1 then nst132 k BT.zero :: BT.GB 1 (nst132 k BT.zero) else []) := h
      rw [if_pos (by omega)] at h2
      rcases List.mem_cons.mp h2 with h3 | h3
      · exact ⟨k, by omega, h3⟩
      · obtain ⟨i, hi, he⟩ := mem_GB1_bT152 k e h3
        exact ⟨i, by omega, he⟩

theorem mem_GB0_bT152 : ∀ (k : Nat), ∀ e ∈ BT.GB 0 (nst132 k BT.zero),
    ∃ i, i < k ∧ e = nst132 i BT.zero
  | 0 => by intro e h; cases h
  | k + 1 => by
      intro e h
      have h2 : e ∈ (if 0 ≤ 1 then nst132 k BT.zero :: BT.GB 0 (nst132 k BT.zero) else []) := h
      rw [if_pos (by omega)] at h2
      rcases List.mem_cons.mp h2 with h3 | h3
      · exact ⟨k, by omega, h3⟩
      · obtain ⟨i, hi, he⟩ := mem_GB0_bT152 k e h3
        exact ⟨i, by omega, he⟩

theorem mem_GB1_famB152 (k : Nat) : ∀ (m : Nat), ∀ e ∈ BT.GB 1 (famB132 m k),
    ∃ j, j < m ∧ e = famB132 j k
  | 0 => by
      intro e h
      have h2 : e ∈ (if 1 ≤ 0 then nst132 k BT.zero :: BT.GB 1 (nst132 k BT.zero) else []) := h
      rw [if_neg (by omega)] at h2
      cases h2
  | m + 1 => by
      intro e h
      have h2 : e ∈ (if 1 ≤ 1 then famB132 m k :: BT.GB 1 (famB132 m k) else []) := h
      rw [if_pos (by omega)] at h2
      rcases List.mem_cons.mp h2 with h3 | h3
      · exact ⟨m, by omega, h3⟩
      · obtain ⟨j, hj, he⟩ := mem_GB1_famB152 k m e h3
        exact ⟨j, by omega, he⟩

theorem mem_GB0_famB152 (k : Nat) : ∀ (m : Nat), ∀ e ∈ BT.GB 0 (famB132 m k),
    (∃ j, j < m ∧ e = famB132 j k) ∨ (∃ i, i ≤ k ∧ e = nst132 i BT.zero)
  | 0 => by
      intro e h
      have h2 : e ∈ (if 0 ≤ 0 then nst132 k BT.zero :: BT.GB 0 (nst132 k BT.zero) else []) := h
      rw [if_pos (by omega)] at h2
      rcases List.mem_cons.mp h2 with h3 | h3
      · exact Or.inr ⟨k, by omega, h3⟩
      · obtain ⟨i, hi, he⟩ := mem_GB0_bT152 k e h3
        exact Or.inr ⟨i, by omega, he⟩
  | m + 1 => by
      intro e h
      have h2 : e ∈ (if 0 ≤ 1 then famB132 m k :: BT.GB 0 (famB132 m k) else []) := h
      rw [if_pos (by omega)] at h2
      rcases List.mem_cons.mp h2 with h3 | h3
      · exact Or.inl ⟨m, by omega, h3⟩
      · rcases mem_GB0_famB152 k m e h3 with ⟨j, hj, he⟩ | hr
        · exact Or.inl ⟨j, by omega, he⟩
        · exact Or.inr hr

/-- 裸の塔は標準。 -/
theorem isStd_bT152 : ∀ (k : Nat), BT.isStd (nst132 k BT.zero) = true
  | 0 => rfl
  | k + 1 => by
      show (BT.isStd (nst132 k BT.zero)
        && (BT.GB 1 (nst132 k BT.zero)).all (fun e => BT.lt e (nst132 k BT.zero))) = true
      rw [isStd_bT152 k, List.all_eq_true.mpr (fun e he => by
        obtain ⟨i, hi, rfl⟩ := mem_GB1_bT152 k e he
        exact lt_bT_bT152 hi)]
      rfl

/-- **族の項そのものはどの `(m, k)` でも標準。**  §132.5 の `raw132` の側の前提。 -/
theorem isStd_famB152 (k : Nat) : ∀ (m : Nat), BT.isStd (famB132 m k) = true
  | 0 => by
      show (BT.isStd (nst132 k BT.zero)
        && (BT.GB 0 (nst132 k BT.zero)).all (fun e => BT.lt e (nst132 k BT.zero))) = true
      rw [isStd_bT152 k, List.all_eq_true.mpr (fun e he => by
        obtain ⟨i, hi, rfl⟩ := mem_GB0_bT152 k e he
        exact lt_bT_bT152 hi)]
      rfl
  | m + 1 => by
      show (BT.isStd (famB132 m k)
        && (BT.GB 1 (famB132 m k)).all (fun e => BT.lt e (famB132 m k))) = true
      rw [isStd_famB152 k m, List.all_eq_true.mpr (fun e he => by
        obtain ⟨j, hj, rfl⟩ := mem_GB1_famB152 k m e he
        exact lt_famB_famB152 k hj)]
      rfl

/-- **`k ≤ m` では `ψ₀(famB)` は `K` 標準。** -/
theorem isStd_D0_famB152 {m k : Nat} (hkm : k ≤ m) :
    BT.isStd (BT.D 0 (famB132 m k)) = true := by
  show (BT.isStd (famB132 m k)
    && (BT.GB 0 (famB132 m k)).all (fun e => BT.lt e (famB132 m k))) = true
  rw [isStd_famB152 k m, List.all_eq_true.mpr (fun e he => by
    rcases mem_GB0_famB152 k m e he with ⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩
    · exact lt_famB_famB152 k hj
    · exact lt_bT_famB152 k (by omega))]
  rfl

/-- **§132.5 の凍った境界そのもの、全ての `(m, k)` で。**  `K` 標準性は `k ≤ m` と同値。 -/
theorem std_boundary152 (m k : Nat) :
    BT.isStd (BT.D 0 (famB132 m k)) = decide (k ≤ m) := by
  rcases Nat.lt_or_ge m k with h | h
  · rw [not_std_famB152 h, decide_eq_false (by omega)]
  · rw [isStd_D0_famB152 h, decide_eq_true (by omega)]

/-- **主定理 — 二つの境界は一致する。**  発火する高さ (`3 ≤ m`) では、族の門の一歩は
    `K` 標準性とちょうど同値。門が一歩を満たさない項は正確に標準領域の外に居る。 -/
theorem boundary_coincide152 (m k : Nat) (h3 : 3 ≤ m) :
    KsetStepOK 0 (dict (famB132 m k)) ↔ BT.isStd (BT.D 0 (famB132 m k)) = true := by
  constructor
  · intro H
    rcases Nat.lt_or_ge m k with h | h
    · exact absurd H (not_ksetStepOK_famB152 h3 h)
    · exact isStd_D0_famB152 h
  · exact famB_no_refute152 m k

end

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§145.4 の H1 の義務、族の上で。**  `K` 標準な族の項は最初に発火する歩の義務を満たす —
    `psiIdxOKStd172_of_first145` の H1 が族に要る中身はこれで、族からはもう反例が出ない。 -/
theorem firstFire_famB152 (m k : Nat) (hs : BT.isStd (BT.D 0 (famB132 m k)) = true) :
    FirstFire145 (famB132 m k) :=
  fun p hp _ hle y hy => (famB_no_refute152 m k hs p hp hle).2 y hy

end

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §152.13 Measurement (frozen) — the theorems against the populations' deciders

Everything below is measurement, not proof: the §132.5 deciders re-run on the family,
on a range wider than any frozen before (`m, k < 12`; §132.5 stopped at 9), and the
closed forms re-computed by the kernel. -/

/-! §132.5 の角はそのまま。 -/
#guard famB132 3 4 == min130

/-! 境界の凍結 — `K` 標準性は `k ≤ m`、門の一歩は `k ≤ m ∨ m < 3`、
    §132.5 の `bad132`/`raw132` も広い範囲でそのまま。 -/
#guard (List.range 12).all fun m => (List.range 12).all fun k =>
  (BT.isStd (BT.D 0 (famB132 m k)) == decide (k ≤ m))
  && (stepOKb 0 (dict (famB132 m k)) == (decide (k ≤ m) || decide (m < 3)))
  && (bad132 (famB132 m k) == false)
  && (raw132 (famB132 m k) == decide (3 ≤ m ∧ m < k))

/-! 閉じた形の照合 — `dict` の値は本当に `UW152` の塔。 -/
#guard (List.range 6).all fun m => (List.range 6).all fun kk =>
  dict (famB132 (m + 1) (kk + 3)) == UW152 (sd152 (kk + 3)) m

/-! 種の照合。 -/
#guard (List.range 5).all fun j => sd152 (j + 4) == psi (Z zero) (TW (j + 3))
#guard (List.range 7).all fun j => dict (nst132 (j + 2) BT.zero) == TW (j + 1)

/-! 逃げる元と指数の照合 — 発火する歩は一つ、材料は `(TW (k-1), 1)`、指数は塔そのもの。 -/
#guard (pys145 (famB132 4 4)).map (fun q => (q.2, idxOf (reg 1) q.1.1 q.1.2))
  == [(TW 3, UW152 (sd152 4) 3)]
#guard (pys145 (famB132 3 5)).map (fun q => (q.2, idxOf (reg 1) q.1.1 q.1.2))
  == [(TW 4, UW152 (sd152 5) 2)]
#guard (pys145 (famB132 5 4)).map (fun q => (q.2, idxOf (reg 1) q.1.1 q.1.2))
  == [(TW 3, UW152 (sd152 4) 4)]

/-! ### Axioms — no `sorryAx`, no `native_decide` -/

#print axioms twT152_smono
#print axioms dict_famB152
#print axioms lt_TW_UW152
#print axioms lt_TW_UW_false152
#print axioms lt_UW_TW152
#print axioms ksetStepOK_famB152
#print axioms not_ksetStepOK_famB152
#print axioms famB_no_refute152
#print axioms psiIdxOK_famB152
#print axioms std_boundary152
#print axioms boundary_coincide152
#print axioms firstFire_famB152

/-! 新しい突つき — 種を塔の和にした族でも、門を外す標準項は出ない (測定)。 -/
#guard (List.range 7).all fun m => (List.range 7).all fun k => (List.range (k + 1)).all fun j =>
  !(bad132 (nst132 m (BT.D 0 (BT.sum (nst132 k BT.zero) (nst132 j BT.zero)))))

end
/-! ## §153 WHICH SIDE IS WRONG AT `tGap107` — `vOf` OVERSHOOTS, THREE ARBITERS AGREE
# §153a  The §134 fork at `tGap107` is DECIDED: `vOf` overshoots; the expansion values stand

Verdict (three independent arbiters, none previously asked this question, all agree):
the value of the matrix `(0,0)(1,1)(2,1)(3,1)(1,1)(2,1)(3,0)(4,1)(5,1)(6,1)` is
`φ̄(Γ₀,0)` (the ordinal φ_{Γ₀}(1)) — the sup of the expansion values — and NOT
`vOf tGap107 = φ̄(Γ₀,Γ₀⊕1)` (the ordinal φ_{Γ₀}(Γ₀+1)).

What this file freezes in Lean (all `decide`, gate-free):

* `oRB` (the port of naruyoko's `Trans`) sends the matrix to exactly `bTowG98 1`
  = ψ₀(Ω^Ω ⊕ Ω^Γ₀), a STANDARD Buchholz term, and sends the first expansions to
  ψ₀(Ω^Ω ⊕ Ω^(g n)) where `g` is precisely the canonical Γ₀-approximating tower
  (g 0 = ψ₀(Ω²), g (n+1) = ψ₀(Ω^(g n)); n ≤ 8 measured externally, n ≤ 1 frozen
  here — kernel reduction of the port grows too fast beyond 12 columns).  So in
  Buchholz's own system the matrix IS the limit of its expansion:
  sup_n ψ₀(Ω^Ω ⊕ Ω^(g n)) = ψ₀(Ω^Ω ⊕ Ω^Γ₀).
* ψ₀(Ω^Ω ⊕ Ω^Γ₀) denotes φ_{Γ₀}(1):  ψ₀(Ω^Ω ⊕ Ω^γ) = φ_γ(Γ₀+1) on the whole
  chain below (measured), and sup_{γ→Γ₀} φ_γ(Γ₀+1) = φ_{Γ₀}(1) by the Veblen
  fs rule φ_λ(1)[n] = φ_{λ[n]}(φ_λ(0)+1); the map α ↦ φ_α(Γ₀+1) is NOT
  continuous at α = Γ₀, and continuing it across that point is exactly the
  step `dict` gets wrong.
* The vOf-side ordinal φ_{Γ₀}(Γ₀+1) has its own standard Buchholz term
  (`highB153`), STRICTLY ABOVE `bTowG98 1`, whose canonical matrix strictly
  EXTENDS the witness matrix by ten more columns; φ_{Γ₀}(2) (`midB153`) sits
  strictly between, on the 16-column extension.  Both canonical matrices are
  produced identically by §85's `bInv85` (frozen below) and by naruyoko's
  independent `TransRev` (measured).  So reading `vOf`'s value into the
  10-column matrix would break the order of the correspondence.
* Hexirp's table (バシク行列システムとRathjenの弱マーロのpsiの対応) gives the
  10-column matrix the value `phi(psi(W(0),0),1)` and the 16-column matrix
  `phi(psi(W(0),0),1+1)`.  Translated by the repository's validated dictionary
  (`phiNF (1+a) b`, `scripts/hexirp-rathjen-check.py`), both land STRICTLY
  BELOW `vOf tGap107` — the second is an order violation against `vOf`, since
  its matrix strictly extends the witness matrix.  These rows contain `psi`,
  so they sit outside the `CNV` fragment §147 counted: this comparison is new.

Cofinality note: `¬ LimCofS1` (§135) is untouched either way; this file settles
which SIDE of the §134 fork was wrong, not the (already unconditional) verdict.
The corrected value of `tGap107` is the term `rawT94 0 = phi (psi (Z zero) zero) zero`.
-/
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
open Trans.Dict (BT)
open TM.Term

/-! ### §153.1 The Buchholz side (arbiter: Buchholz's own system, through the validated port) -/

/-- 展開の値の Buchholz 側の指数の塔。`g 0 = ψ₀(Ω²)`、`g (n+1) = ψ₀(Ω^(g n))`。
    これは Γ₀ の正準近似列である。 -/
def gT153 : Nat → BT
  | 0 => .D 0 (.D 1 (.D 1 .zero))
  | n + 1 => .D 0 (.D 1 (.D 1 (gT153 n)))

/-- 展開 n 段目の Buchholz 値 `ψ₀(Ω^Ω ⊕ Ω^(g n))`。 -/
def eV153 (n : Nat) : BT := .D 0 (.sum bOO94 (.D 1 (.D 1 (gT153 n))))

/-- `Γ₀ = ψ₀(Ω^Ω)` の Buchholz 項。 -/
def g0B153 : BT := .D 0 bOO94

/-- `φ_{Γ₀}(2)` の Buchholz 項 `ψ₀(Ω^Ω ⊕ Ω^Γ₀ ⊕ Ω^Γ₀)`。 -/
def midB153 : BT :=
  .D 0 (.sum bOO94 (.sum (.D 1 (.D 1 g0B153)) (.D 1 (.D 1 g0B153))))

/-- `vOf` 側の主張 `φ_{Γ₀}(Γ₀+1)` の Buchholz 項
    `ψ₀(Ω^Ω ⊕ Ω^Γ₀·Γ₀ ⊕ Ω^Γ₀)` (`Ω^Γ₀·Γ₀ = ψ₁(ψ₁(Γ₀) ⊕ Γ₀)`)。 -/
def highB153 : BT :=
  .D 0 (.sum bOO94 (.sum (.D 1 (.sum (.D 1 g0B153) g0B153)) (.D 1 (.D 1 g0B153))))

/-- `φ_{Γ₀}(2)` の正準行列 — 証人行列を 6 列延長する 16 列
    (naruyoko の `TransRev` の実測と下の `bInv85` が同じものを出す)。 -/
def midMat153 : BMS.Matrix :=
  [[0,0],[1,1],[2,1],[3,1],[1,1],[2,1],[3,0],[4,1],[5,1],[6,1],
   [1,1],[2,1],[3,0],[4,1],[5,1],[6,1]]

/-- `φ_{Γ₀}(Γ₀+1)` の正準行列 — 証人行列を 10 列延長する 20 列 (同上)。 -/
def highMat153 : BMS.Matrix :=
  [[0,0],[1,1],[2,1],[3,1],[1,1],[2,1],[3,0],[4,1],[5,1],[6,1],
   [2,0],[3,1],[4,1],[5,1],[1,1],[2,1],[3,0],[4,1],[5,1],[6,1]]

/-- **行列の Buchholz 値は `bTowG98 1` そのもの。** -/
theorem oRB_tGap153 : Trans.Recal.oRB (matB tGap107 0) = some (bTowG98 1) := by decide

/-- **展開 0 段目の Buchholz 値は `ψ₀(Ω^Ω ⊕ Ω^(g 0))`。** -/
theorem oRB_fs0_153 : Trans.Recal.oRB (matB (fsB tGap107 0) 0) = some (eV153 0) := by decide

set_option maxHeartbeats 20000000 in
/-- **展開 1 段目も塔に乗る。**  (2 段目以降は移植の核簡約が育ちすぎるため
    外部測定 n ≤ 8 に置く。値の側の全 n は `closedFS134_135` が既に定理。) -/
theorem oRB_fs1_153 : Trans.Recal.oRB (matB (fsB tGap107 1) 0) = some (eV153 1) := by decide

/-- **鎖は狭義増加で、全段が行列の値より真に下、全段が標準。** -/
theorem chain153 :
    ((List.range 8).all fun n =>
      BT.lt (eV153 n) (eV153 (n + 1)) && BT.lt (eV153 n) (bTowG98 1)
        && BT.isStd (eV153 n)) = true := by decide

/-- **`bTowG98 1 < midB153 < highB153`、三つとも標準。**
    `vOf` の主張する順序数は行列の Buchholz 値より真に上にある。 -/
theorem order153 :
    (BT.isStd (bTowG98 1) && BT.isStd midB153 && BT.isStd highB153
      && BT.lt (bTowG98 1) midB153 && BT.lt midB153 highB153) = true := by decide

/-- **`φ_{Γ₀}(2)` の正準行列は証人行列を真に延長する 16 列。**
    §85 の逆訳が naruyoko の `TransRev` の実測と同じ行列を出す。 -/
theorem binv_mid153 : matB (bInv85 midB153) 0 = midMat153 := by decide

/-- **`φ_{Γ₀}(Γ₀+1)` の正準行列は 20 列。** 同上。 -/
theorem binv_high153 : matB (bInv85 highB153) 0 = highMat153 := by decide

/-- **頭の `Ω^Ω` を外した綴りは標準でない。**  `ψ₀(Ω^Γ₀)` も `ψ₀(Ω^Γ₀ ⊕ Ω^Γ₀)` も
    Buchholz の標準形でない — `Γ₀` の指数は前に `Ω^Ω` の加数を要る。 -/
theorem nonstd153 :
    (BT.isStd (.D 0 (.D 1 (.D 1 g0B153)))
      || BT.isStd (.D 0 (.sum (.D 1 (.D 1 g0B153)) (.D 1 (.D 1 g0B153))))) = false := by
  decide

/-! ### §153.2 The Hexirp side (arbiter: the external table, through the validated dictionary) -/

/-- Hexirp 氏の表の証人行列の行 `phi(psi(W(0),0),1)` を、検証済みの辞書
    (`phiNF (1+a) b`) で当方の項にしたもの。 -/
def hexM153 : TM.Term := phiNF (psi (Z zero) zero) (ofNat 1)

/-- 同じく 16 列の行列の行 `phi(psi(W(0),0),1+1)` の訳。 -/
def hexMmid153 : TM.Term := phiNF (psi (Z zero) zero) (ofNat 2)

/-- **辞書の橋が作る綴りを釘で留める。** `φ̄(Γ₀,1)`・`φ̄(Γ₀,2)`。
    (`φ̄(Γ₀,0)` と `φ̄(Γ₀,1)` が同じ順序数 `φ_{Γ₀}(1)` を表すのは §127.8 の記録済みの穴。
    どちらの読みでも下の不等式は成り立つ。) -/
theorem hex_spelling153 :
    hexM153 = phi (psi (Z zero) zero) one
      ∧ hexMmid153 = phi (psi (Z zero) zero) (ofNat 2) :=
  ⟨by decide, by decide⟩

/-- **Hexirp 氏の値は、どの綴りでも `vOf tGap107` より真に下。**
    3 番目が順序の破れである: `vOf` が 10 列の行列に付ける値は、
    先方が 16 列の行列 (真に長い) に付ける値より真に上にある。 -/
theorem hex_lt_vOf153 :
    (lt (rawT94 0) (vOf tGap107) && lt hexM153 (vOf tGap107)
      && lt hexMmid153 (vOf tGap107)) = true := by decide

/-- **綴りの列は当方の順序で整列している。**
    `φ̄(Γ₀,0) < φ̄(Γ₀,1) < φ̄(Γ₀,2) < vOf tGap107`。 -/
theorem hex_chain153 :
    (lt (rawT94 0) hexM153 && lt hexM153 hexMmid153
      && lt hexMmid153 (vOf tGap107)) = true := by decide

/-! ### §153.3 What is already green and completes the picture

`noReach135`: every expansion value is strictly below `rawT94 0 = φ̄(Γ₀,0)`.
`lt_s_vOf127`: `φ̄(Γ₀,0) < vOf tGap107`.  With §1 and §2 above:

    expansion values  <  φ̄(Γ₀,0)  ≡  value of the matrix (all three arbiters)
                                   <  vOf tGap107  (which belongs to the 20-column matrix)
-/

#print axioms oRB_tGap153
#print axioms oRB_fs0_153
#print axioms oRB_fs1_153
#print axioms chain153
#print axioms order153
#print axioms binv_mid153
#print axioms binv_high153
#print axioms nonstd153
#print axioms hex_spelling153
#print axioms hex_lt_vOf153
#print axioms hex_chain153

/-! ## §154 `TailOK151` REDUCES TO THE MID-LIST DOMINATION `Dom154`

The trichotomy the reduction rests on, proven as a list lemma (`transport154`):
`hi a < hi b` forces the two `wcnf` pair lists into "a common prefix, then the
left side ends, or the head pairs strictly drop in the (exponent, coefficient)
lexicographic order".  Instantiated under equal last exponents:

  * divergence at both last pairs  → clause (i) of `tailDec151` (PROVEN here);
  * the left list a proper prefix  → impossible — the strict descent of the
    merged exponents (`wcnf_descP154`, new) contradicts `sameExp145`;
  * divergence before a last pair  → the named residual `Dom154`, and its
    divergence shape is forced (`domShape154`): the left tail is nonempty or
    the exponent strictly drops.

`tailOK151_of_dom154 (Hp : PsiIdxOKStd172) (HD : Dom154) : TailOK151` is the
bridge; `xmono145_of_dom154` chains it to §151's.  `Dom154` needs the left
`K`-standardness in an essential way — §151's control (`cenNoK151`) breaks
clause (ii) in 144/31/156 pairs once it is dropped — and no Term-side carrier
of the `G₀`-condition exists yet; that is the remaining wall. -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- `subAP` を成分列で書いたもの。 -/
theorem subAP_eq154 {w g b : Term} {s : List Term} (hl : toList g = b :: s) :
    subAP w g = if b == w then ofList s else g := by
  show (match toList g with
        | [] => zero
        | p :: rest => if p == w then ofList rest else g) = _
  rw [hl]

/-- **`· ⊖ Ω₁` は、頭の成分が `Ω₁` 以上の項の上で狭義単調。** -/
theorem subAP_smono154 {x y : Term} (hig : inT x = true) (hih : inT y = true)
    {bg bh : Term} {sg sh : List Term}
    (hlg : toList x = bg :: sg) (hlh : toList y = bh :: sh)
    (hbg : lt bg (reg 1) = false) (hbh : lt bh (reg 1) = false)
    (hxy : lt x y = true) :
    lt (subAP (reg 1) x) (subAP (reg 1) y) = true := by
  have hcg := (inT_toList x hig).1
  have hdg := (inT_toList x hig).2
  have hch := (inT_toList y hih).1
  have hdh := (inT_toList y hih).2
  rw [hlg] at hcg hdg
  rw [hlh] at hch hdh
  obtain ⟨⟨_, hibg⟩, hcsg⟩ := inTL_cons.mp hcg
  obtain ⟨⟨_, hibh⟩, hcsh⟩ := inTL_cons.mp hch
  have hisg : inT (ofList sg) = true := inT_ofList sg hcsg (descL_tail hdg)
  have hish : inT (ofList sh) = true := inT_ofList sh hcsh (descL_tail hdh)
  rw [subAP_eq154 hlg, subAP_eq154 hlh]
  by_cases hqg : (bg == (reg 1 : Term)) = true
  · rw [if_pos hqg]
    by_cases hqh : (bh == (reg 1 : Term)) = true
    · -- both heads are exactly Ω₁ — peel them
      rw [if_pos hqh]
      have hbb : bh = bg := by rw [eq_of_beq hqg, eq_of_beq hqh]
      refine lt_hd_eq_inv89 hig hih hlg (by rw [hlh, hbb]) hisg hish
        (toList_ofList89 hcsg) (toList_ofList89 hcsh) hxy
    · -- left head is Ω₁, right head is strictly above it
      rw [if_neg hqh]
      have hWh : lt (reg 1) bh = true := by
        rcases (Bool.or_eq_true _ _).mp (le_reg1_of_not_lt89 hibh hbh) with he | hl2
        · exfalso
          have hb2 : (bh == (reg 1 : Term)) = true := by
            rw [← eq_of_beq he]; exact beq_self_eq_true _
          rw [hb2] at hqh; exact hqh rfl
        · exact hl2
      have hne : y ≠ zero := by
        intro hc
        rw [hc] at hlh
        exact List.cons_ne_nil bh sh (by rw [← hlh]; rfl)
      cases hsg : sg with
      | nil => exact lt_zero_left hne
      | cons c cs =>
          subst hsg
          have hic : inT c = true := (inTL_cons.mp hcsg).1.2
          have hcW : le c bg = true :=
            descL_bound_inT (c :: cs) bg hibg hcsg hdg c (List.Mem.head _)
          have hcbh : lt c bh = true := by
            refine lt_of_le_of_lt3 (inT_le_fragR c hic) (inT_le_fragR bg hibg)
              (inT_le_fragR bh hibh) hcW ?_
            rw [eq_of_beq hqg]; exact hWh
          exact lt_of_hd_lt hisg hih (toList_ofList89 hcsg) hlh hcbh
  · rw [if_neg hqg]
    by_cases hqh : (bh == (reg 1 : Term)) = true
    · -- impossible: x < y forces bg ≤ bh = Ω₁ ≤ bg, so bg = Ω₁
      exfalso
      have hgle : le bg bh = true := hd_mono_inT hig hih hlg hlh (le_of_lt hxy)
      have hgW : le bg (reg 1) = true := by rw [← eq_of_beq hqh]; exact hgle
      rcases (Bool.or_eq_true _ _).mp hgW with he | hl2
      · rw [he] at hqg; exact hqg rfl
      · rw [hl2] at hbg; exact Bool.noConfusion hbg
    · rw [if_neg hqh]; exact hxy

/-- **`divAP Ω₁` は `Ω₁` 以上の加法主要項の上で狭義単調。** -/
theorem divAP_smono154 {p q : Term}
    (hap : p.isAP = true) (hip : inT p = true) (hpM : lt p M = true)
    (hpw : lt p (reg 1) = false)
    (haq : q.isAP = true) (hiq : inT q = true) (hqM : lt q M = true)
    (hqw : lt q (reg 1) = false)
    (h : lt p q = true) : lt (divAP (reg 1) p) (divAP (reg 1) q) = true := by
  obtain ⟨bp, sp, hlp, hbp⟩ := hd_logOm109 (isSC_reg_succ 0) (inT_reg 1)
    (show (reg 1 : Term).isAP = true from rfl) hap hip hpw
  obtain ⟨bq, sq, hlq, hbq⟩ := hd_logOm109 (isSC_reg_succ 0) (inT_reg 1)
    (show (reg 1 : Term).isAP = true from rfl) haq hiq hqw
  have hg : lt (logOm p) (logOm q) = true := logOm_smono110 hip hap hpM hiq haq hqM h
  show lt (omegaNF (subAP (reg 1) (logOm p))) (omegaNF (subAP (reg 1) (logOm q))) = true
  exact lt_omegaNF_inT79 (inT_subAP (inT_logOm hip)) (inT_subAP (inT_logOm hiq))
    (subAP_smono154 (inT_logOm hip) (inT_logOm hiq) hlp hlq hbp hbq hg)

/-- 割った成分列は 𝔗(M) の成分の条件を満たす。 -/
theorem inTL_mapDiv154 (H : List Term) (hc : inTL H = true) :
    inTL (H.map (divAP (reg 1))) = true := by
  show (H.map (divAP (reg 1))).all _ = true
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨q, hq, hxe⟩ := List.mem_map.mp hx
  have hiq : inT q = true :=
    ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hc q hq)).2
  rw [← hxe]
  show ((divAP (reg 1) q).isAP && inT (divAP (reg 1) q)) = true
  rw [isAP_divAP, inT_divAP hiq]
  rfl

/-- 割った成分列は降順のまま。 -/
theorem descL_mapDiv154 : ∀ (H : List Term), inTL H = true → descL H = true →
    (∀ p ∈ H, lt p (reg 1) = false) → descL (H.map (divAP (reg 1))) = true := by
  intro H
  induction H with
  | nil => intro _ _ _; rfl
  | cons p t ih =>
    intro hc hd hW
    obtain ⟨⟨hap, hip⟩, hct⟩ := inTL_cons.mp hc
    cases t with
    | nil => rfl
    | cons q t' =>
        obtain ⟨⟨haq, hiq⟩, _⟩ := inTL_cons.mp hct
        obtain ⟨hqp, hdt⟩ := descL_cons.mp hd
        have hih := ih hct hdt (fun z hz => hW z (List.Mem.tail _ hz))
        refine descL_cons.mpr ⟨?_, hih⟩
        exact divAP_mono109 (isSC_reg_succ 0) (inT_reg 1) haq hiq
          (hW q (List.Mem.tail _ (List.Mem.head _))) hap hip hqp

/-- **割り算は成分列の比較を保つ。** -/
theorem mapDiv_smono154 : ∀ (H1 H2 : List Term), inTL H1 = true → inTL H2 = true →
    descL H1 = true → descL H2 = true →
    (∀ p ∈ H1, lt p (reg 1) = false) → (∀ p ∈ H2, lt p (reg 1) = false) →
    (∀ p ∈ H1, lt p M = true) → (∀ p ∈ H2, lt p M = true) →
    lt (ofList H1) (ofList H2) = true →
    lt (ofList (H1.map (divAP (reg 1)))) (ofList (H2.map (divAP (reg 1)))) = true := by
  intro H1
  induction H1 with
  | nil =>
    intro H2 _ hc2 _ _ _ _ _ _ h
    cases H2 with
    | nil =>
        exfalso
        rw [show ofList ([] : List Term) = zero from rfl, lt_irrefl] at h
        exact Bool.noConfusion h
    | cons q t2 =>
        refine lt_zero_left ?_
        refine ofList_ne_zero81 _ (List.cons_ne_nil _ _) ?_
        intro z hz
        obtain ⟨r, _, hze⟩ := List.mem_map.mp hz
        rw [← hze]
        exact isAP_divAP _ _
  | cons p t1 ih =>
    intro H2 hc1 hc2 hd1 hd2 hW1 hW2 hM1 hM2 h
    cases H2 with
    | nil =>
        exfalso
        rw [show ofList ([] : List Term) = zero from rfl, lt_zero_right] at h
        exact Bool.noConfusion h
    | cons q t2 =>
        obtain ⟨⟨hap, hip⟩, hct1⟩ := inTL_cons.mp hc1
        obtain ⟨⟨haq, hiq⟩, hct2⟩ := inTL_cons.mp hc2
        have hi1 : inT (ofList (p :: t1)) = true := inT_ofList _ hc1 hd1
        have hi2 : inT (ofList (q :: t2)) = true := inT_ofList _ hc2 hd2
        have hcm1 : inTL ((p :: t1).map (divAP (reg 1))) = true := inTL_mapDiv154 _ hc1
        have hcm2 : inTL ((q :: t2).map (divAP (reg 1))) = true := inTL_mapDiv154 _ hc2
        have hdm1 : descL ((p :: t1).map (divAP (reg 1))) = true :=
          descL_mapDiv154 _ hc1 hd1 hW1
        have hdm2 : descL ((q :: t2).map (divAP (reg 1))) = true :=
          descL_mapDiv154 _ hc2 hd2 hW2
        have him1 : inT (ofList ((p :: t1).map (divAP (reg 1)))) = true :=
          inT_ofList _ hcm1 hdm1
        have him2 : inT (ofList ((q :: t2).map (divAP (reg 1)))) = true :=
          inT_ofList _ hcm2 hdm2
        rcases lt_trichotomy_inT hip hiq with hpq | hpq | hpq
        · -- heads strictly compare — divAP is strictly monotone on them
          refine lt_of_hd_lt him1 him2 (toList_ofList89 hcm1) (toList_ofList89 hcm2) ?_
          exact divAP_smono154 hap hip (hM1 p (List.Mem.head _)) (hW1 p (List.Mem.head _))
            haq hiq (hM2 q (List.Mem.head _)) (hW2 q (List.Mem.head _)) hpq.1
        · -- equal heads — peel and use the induction hypothesis
          have hpe : p = q := hpq.2.1
          subst hpe
          have hit1 : inT (ofList t1) = true := inT_ofList t1 hct1 (descL_tail hd1)
          have hit2 : inT (ofList t2) = true := inT_ofList t2 hct2 (descL_tail hd2)
          have hrec : lt (ofList t1) (ofList t2) = true :=
            lt_hd_eq_inv89 hi1 hi2 (toList_ofList89 hc1) (toList_ofList89 hc2)
              hit1 hit2 (toList_ofList89 hct1) (toList_ofList89 hct2) h
          have hIH := ih t2 hct1 hct2 (descL_tail hd1) (descL_tail hd2)
            (fun z hz => hW1 z (List.Mem.tail _ hz)) (fun z hz => hW2 z (List.Mem.tail _ hz))
            (fun z hz => hM1 z (List.Mem.tail _ hz)) (fun z hz => hM2 z (List.Mem.tail _ hz))
            hrec
          exact lt_of_hd_eq77 him1 him2 (toList_ofList89 hcm1) (toList_ofList89 hcm2) hIH
        · -- reversed heads contradict the hypothesis
          exfalso
          have h2 : lt (ofList (q :: t2)) (ofList (p :: t1)) = true :=
            lt_of_hd_lt hi2 hi1 (toList_ofList89 hc2) (toList_ofList89 hc1) hpq.2.2
          rw [lt_asymm_inT hi1 hi2 h] at h2
          exact Bool.noConfusion h2

/-- **§154 の要 — 成分は (指数, 係数) の辞書式で比べる。**
    `Ω₁` 以上の加法主要成分 `p < q` は、`wA` が狭義に増えるか、`wA` が一致して
    `wC` が狭義に増えるかのどちらか。 -/
theorem compLex154 {p q : Term}
    (hap : p.isAP = true) (hip : inT p = true) (hpM : lt p M = true)
    (_hpw : lt p (reg 1) = false)
    (haq : q.isAP = true) (hiq : inT q = true) (hqM : lt q M = true)
    (_hqw : lt q (reg 1) = false)
    (h : lt p q = true) :
    lt (wA (reg 1) p) (wA (reg 1) q) = true
      ∨ (wA (reg 1) p = wA (reg 1) q ∧ lt (wC (reg 1) p) (wC (reg 1) q) = true) := by
  have hgp : inT (logOm p) = true := inT_logOm hip
  have hgq : inT (logOm q) = true := inT_logOm hiq
  have hg : lt (logOm p) (logOm q) = true := logOm_smono110 hip hap hpM hiq haq hqM h
  by_cases he : hiW89 (logOm p) = hiW89 (logOm q)
  · -- same high part: the exponents agree and the low parts carry the comparison
    right
    constructor
    · show ofList (((toList (logOm p)).filter (fun z => !lt z (reg 1))).map (divAP (reg 1)))
        = ofList (((toList (logOm q)).filter (fun z => !lt z (reg 1))).map (divAP (reg 1)))
      rw [← toList_hiW89 hgp, ← toList_hiW89 hgq, he]
    · have hlo : lt (loW89 (logOm p)) (loW89 (logOm q)) = true :=
        lo_lt_of_lt89 hgp hgq he hg
      show lt (omegaNF (ofList ((toList (logOm p)).filter (fun z => lt z (reg 1)))))
        (omegaNF (ofList ((toList (logOm q)).filter (fun z => lt z (reg 1))))) = true
      exact lt_omegaNF_inT79 (inT_loW89 hgp) (inT_loW89 hgq) hlo
  · -- the high parts separate: the exponents strictly compare
    left
    have hhi : lt (hiW89 (logOm p)) (hiW89 (logOm q)) = true := lt_hi89 hgp hgq hg he
    have hcp := (inT_toList _ hgp).1
    have hdp := (inT_toList _ hgp).2
    have hcq := (inT_toList _ hgq).1
    have hdq := (inT_toList _ hgq).2
    have hfp : inTL ((toList (logOm p)).filter (fun z => !lt z (reg 1))) = true :=
      inTL_filter _ hcp
    have hfq : inTL ((toList (logOm q)).filter (fun z => !lt z (reg 1))) = true :=
      inTL_filter _ hcq
    have hkey := mapDiv_smono154
      ((toList (logOm p)).filter (fun z => !lt z (reg 1)))
      ((toList (logOm q)).filter (fun z => !lt z (reg 1)))
      hfp hfq (descL_filter_inT _ hcp hdp _) (descL_filter_inT _ hcq hdq _)
      (by
        intro z hz
        have h2 := (List.mem_filter.mp hz).2
        cases hlz : lt z (reg 1) with
        | false => rfl
        | true => rw [hlz] at h2; exact Bool.noConfusion h2)
      (by
        intro z hz
        have h2 := (List.mem_filter.mp hz).2
        cases hlz : lt z (reg 1) with
        | false => rfl
        | true => rw [hlz] at h2; exact Bool.noConfusion h2)
      (fun z hz => ltM_toList _ hgp (ltM_logOm hip hpM) z (List.mem_filter.mp hz).1)
      (fun z hz => ltM_toList _ hgq (ltM_logOm hiq hqM) z (List.mem_filter.mp hz).1)
      (by rw [← toList_hiW89 hgp, ← toList_hiW89 hgq,
              inT_ofList_toList _ (inT_hiW89 hgp), inT_ofList_toList _ (inT_hiW89 hgq)]
          exact hhi)
    exact hkey

/-- `wA` は広義単調。 -/
theorem wA_mono154 {p q : Term}
    (hap : p.isAP = true) (hip : inT p = true) (hpM : lt p M = true)
    (hpw : lt p (reg 1) = false)
    (haq : q.isAP = true) (hiq : inT q = true) (hqM : lt q M = true)
    (hqw : lt q (reg 1) = false)
    (h : le p q = true) : le (wA (reg 1) p) (wA (reg 1) q) = true := by
  rcases (Bool.or_eq_true _ _).mp h with he | hl
  · rw [eq_of_beq he]
    exact le_self _
  · rcases compLex154 hap hip hpM hpw haq hiq hqM hqw hl with h1 | h1
    · exact le_of_lt h1
    · rw [h1.1]
      exact le_self _

/-- 加法主要な的の下では、成分はどれも的の下。 -/
theorem comp_lt_ap154 {x t c : Term} (hx : inT x = true) (hit : inT t = true)
    (hat : t.isAP = true) (h : lt x t = true) (hc : c ∈ toList x) : lt c t = true := by
  cases hlx : toList x with
  | nil => rw [hlx] at hc; cases hc
  | cons b s =>
      rw [hlx] at hc
      have hcb := (inT_toList x hx).1
      have hdb := (inT_toList x hx).2
      rw [hlx] at hcb hdb
      obtain ⟨⟨_, hib⟩, hcs⟩ := inTL_cons.mp hcb
      have hbt : lt b t = true := by
        rw [← inT_ofList_toList x hx, hlx, lt_ofList_nsum hat] at h
        exact h
      rcases List.mem_cons.mp hc with h1 | h1
      · rw [h1]; exact hbt
      · have hic : inT c = true :=
          ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcs c h1)).2
        have hcb2 : le c b = true := descL_bound_inT s b hib hcs hdb c h1
        exact lt_of_le_of_lt3 (inT_le_fragR c hic) (inT_le_fragR b hib)
          (inT_le_fragR t hit) hcb2 hbt

/-- **加法主要な的は和で閉じる** — `x, y < t` なら `x ⊕ y < t`。 -/
theorem apClose154 {x y t : Term} (hx : inT x = true) (hy : inT y = true)
    (hit : inT t = true) (hat : t.isAP = true)
    (h1 : lt x t = true) (h2 : lt y t = true) : lt (plus x y) t = true := by
  cases hly : toList y with
  | nil => rw [plus_nil hly]; exact h1
  | cons b1 r =>
      rw [plus_eq (s := x) hly]
      cases hf : (toList x).filter (fun z => le b1 z) with
      | nil =>
          rw [List.nil_append, inT_ofList_toList y hy]
          exact h2
      | cons c cs =>
          rw [List.cons_append, lt_ofList_nsum hat]
          refine comp_lt_ap154 hx hit hat h1 ?_
          have : c ∈ (toList x).filter (fun z => le b1 z) := by
            rw [hf]; exact List.Mem.head _
          exact (List.mem_filter.mp this).1

/-- **有界の頭 — 全成分が `q` より下の並びの `wcnf` の頭の対は、`q` の対より辞書式で下。** -/
theorem headLex154 {q : Term}
    (haq : q.isAP = true) (hiq : inT q = true) (hqM : lt q M = true)
    (hqw : lt q (reg 1) = false) :
    ∀ (L : List Term), inTL L = true → descL L = true → (∀ z ∈ L, lt z M = true) →
    (∀ z ∈ L, lt z q = true) →
    ∀ B D ps, (wcnf (reg 1) L).1 = (B, D) :: ps →
    lt B (wA (reg 1) q) = true
      ∨ (B = wA (reg 1) q ∧ lt D (wC (reg 1) q) = true) := by
  intro L
  induction L with
  | nil =>
      intro _ _ _ _ B D ps hW
      exact absurd (show ([] : List (Term × Term)) = (B, D) :: ps from hW) (by simp)
  | cons p rest ih =>
      intro hc hd hm hallq B D ps hW
      obtain ⟨⟨hap, hip⟩, hcr⟩ := inTL_cons.mp hc
      have hdr := descL_tail hd
      have hmr : ∀ z ∈ rest, lt z M = true := fun z hz => hm z (List.Mem.tail p hz)
      have hallqr : ∀ z ∈ rest, lt z q = true := fun z hz => hallq z (List.Mem.tail p hz)
      by_cases hlp : lt p (reg 1) = true
      · rw [wcnf_cons_lt hlp] at hW
        exact absurd (show ([] : List (Term × Term)) = (B, D) :: ps from hW) (by simp)
      · have hlp' : lt p (reg 1) = false := bool_false hlp
        have hLex := compLex154 hap hip (hm p (List.Mem.head _)) hlp'
          haq hiq hqM hqw (hallq p (List.Mem.head _))
        rw [wcnf_cons_ge hlp'] at hW
        cases hr : wcnf (reg 1) rest with
        | mk fst snd =>
          rw [hr] at hW
          cases fst with
          | nil =>
              have hW' : [((wA (reg 1) p, wC (reg 1) p) : Term × Term)]
                  = (B, D) :: ps := hW
              injection hW' with h1 _
              injection h1 with hB hD
              rw [← hB, ← hD]
              exact hLex
          | cons ac0 ps' =>
              cases ac0 with
              | mk a' c' =>
                have hW' : (if (wA (reg 1) p == a') = true
                    then (((wA (reg 1) p, plus (wC (reg 1) p) c') :: ps',
                            snd) : List (Term × Term) × Term)
                    else ((wA (reg 1) p, wC (reg 1) p) :: (a', c') :: ps', snd)).1
                    = (B, D) :: ps := hW
                by_cases heq : (wA (reg 1) p == a') = true
                · rw [if_pos heq] at hW'
                  have hW'' : ((wA (reg 1) p, plus (wC (reg 1) p) c') : Term × Term) :: ps'
                      = (B, D) :: ps := hW'
                  injection hW'' with h1 _
                  injection h1 with hB hD
                  rcases hLex with hL | hL
                  · left; rw [← hB]; exact hL
                  · right
                    refine ⟨by rw [← hB]; exact hL.1, ?_⟩
                    have hIH := ih hcr hdr hmr hallqr a' c' ps' (by rw [hr])
                    have ha'p : a' = wA (reg 1) p := (eq_of_beq heq).symm
                    have hic' : inT c' = true := by
                      obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0)
                        rest hcr hdr hmr
                      exact (hallOK (a', c') (by rw [hr]; exact List.Mem.head _)).2.2.1
                    rcases hIH with hI | hI
                    · exfalso
                      rw [ha'p, hL.1, lt_irrefl] at hI
                      exact Bool.noConfusion hI
                    · rw [← hD]
                      exact apClose154 (inT_wC hip) hic' (inT_wC hiq)
                        (isAP_omegaNF _) hL.2 hI.2
                · rw [if_neg heq] at hW'
                  have hW'' : ((wA (reg 1) p, wC (reg 1) p) : Term × Term)
                      :: (a', c') :: ps' = (B, D) :: ps := hW'
                  injection hW'' with h1 _
                  injection h1 with hB hD
                  rw [← hB, ← hD]
                  exact hLex

/-- **対リストの辞書式の分岐。**  共通の前置き `R` の後、左が尽きて右が残るか、
    先頭の対が (指数, 係数) の辞書式で狭義に下がるかのどちらか。 -/
def PLex154 (L1 L2 : List (Term × Term)) : Prop :=
  ∃ R S1 S2, L1 = R ++ S1 ∧ L2 = R ++ S2 ∧
    ((S1 = [] ∧ S2 ≠ []) ∨
     (∃ x t1 y t2, S1 = x :: t1 ∧ S2 = y :: t2 ∧
        (lt x.1 y.1 = true ∨ (x.1 = y.1 ∧ lt x.2 y.2 = true))))

/-- **§154 の運搬定理 — 項の比較は対リストの辞書式の分岐を強いる。**
    `Ω₁` 以上の成分列の比較 (`hi` の比較) は、`wcnf` の対リストの上では
    「共通の前置き + 左が尽きる/先頭の対が辞書式で下がる」の形になる。 -/
theorem transport154 : ∀ (H1 H2 : List Term), inTL H1 = true → inTL H2 = true →
    descL H1 = true → descL H2 = true →
    (∀ p ∈ H1, lt p (reg 1) = false) → (∀ p ∈ H2, lt p (reg 1) = false) →
    (∀ p ∈ H1, lt p M = true) → (∀ p ∈ H2, lt p M = true) →
    lt (ofList H1) (ofList H2) = true →
    PLex154 (wcnf (reg 1) H1).1 (wcnf (reg 1) H2).1 := by
  intro H1
  induction H1 with
  | nil =>
      intro H2 _ hc2 _ hd2 _ hW2 _ hM2 h
      cases H2 with
      | nil =>
          exfalso
          rw [show ofList ([] : List Term) = zero from rfl, lt_irrefl] at h
          exact Bool.noConfusion h
      | cons q t2 =>
          obtain ⟨c, ps, hP2⟩ := wcnfFstHd109 (w := reg 1) t2 (hW2 q (List.Mem.head _))
          refine ⟨[], [], (wA (reg 1) q, c) :: ps, rfl, by rw [hP2]; rfl, ?_⟩
          exact Or.inl ⟨rfl, List.cons_ne_nil _ _⟩
  | cons p t1 ih =>
      intro H2 hc1 hc2 hd1 hd2 hW1 hW2 hM1 hM2 h
      cases H2 with
      | nil =>
          exfalso
          rw [show ofList ([] : List Term) = zero from rfl, lt_zero_right] at h
          exact Bool.noConfusion h
      | cons q t2 =>
          obtain ⟨⟨hap, hip⟩, hct1⟩ := inTL_cons.mp hc1
          obtain ⟨⟨haq, hiq⟩, hct2⟩ := inTL_cons.mp hc2
          have hpw : lt p (reg 1) = false := hW1 p (List.Mem.head _)
          have hqw : lt q (reg 1) = false := hW2 q (List.Mem.head _)
          have hpM : lt p M = true := hM1 p (List.Mem.head _)
          have hqM : lt q M = true := hM2 q (List.Mem.head _)
          have hi1 : inT (ofList (p :: t1)) = true := inT_ofList _ hc1 hd1
          have hi2 : inT (ofList (q :: t2)) = true := inT_ofList _ hc2 hd2
          have hdt1 := descL_tail hd1
          have hdt2 := descL_tail hd2
          have hmt1 : ∀ z ∈ t1, lt z M = true := fun z hz => hM1 z (List.Mem.tail _ hz)
          have hmt2 : ∀ z ∈ t2, lt z M = true := fun z hz => hM2 z (List.Mem.tail _ hz)
          have hwt1 : ∀ z ∈ t1, lt z (reg 1) = false :=
            fun z hz => hW1 z (List.Mem.tail _ hz)
          have hwt2 : ∀ z ∈ t2, lt z (reg 1) = false :=
            fun z hz => hW2 z (List.Mem.tail _ hz)
          obtain ⟨_, hOK1⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) t1 hct1 hdt1 hmt1
          obtain ⟨_, hOK2⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) t2 hct2 hdt2 hmt2
          rcases lt_trichotomy_inT hip hiq with hpq | hpq | hpq
          · -- head divergence: p < q — the whole left list sits below q
            have hAll : ∀ z ∈ p :: t1, lt z q = true := by
              intro z hz
              rcases List.mem_cons.mp hz with h1 | h1
              · rw [h1]; exact hpq.1
              · have hiz : inT z = true :=
                  ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hct1 z h1)).2
                exact lt_of_le_of_lt3 (inT_le_fragR z hiz) (inT_le_fragR p hip)
                  (inT_le_fragR q hiq) (descL_bound_inT t1 p hip hct1 hd1 z h1) hpq.1
            obtain ⟨D, ps1, hP1⟩ := wcnfFstHd109 (w := reg 1) t1 hpw
            have hHL := headLex154 haq hiq hqM hqw (p :: t1) hc1 hd1 hM1 hAll
              (wA (reg 1) p) D ps1 hP1
            obtain ⟨_, hOKfull1⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0)
              (p :: t1) hc1 hd1 hM1
            have hiD : inT D = true :=
              (hOKfull1 _ (by rw [hP1]; exact List.Mem.head _)).2.2.1
            -- the head of the right pair list is (wA q, D2) with wC q ≤ D2
            cases hr2 : wcnf (reg 1) t2 with
            | mk fst2 snd2 =>
              cases fst2 with
              | nil =>
                  have hP2 : (wcnf (reg 1) (q :: t2)).1
                      = [(wA (reg 1) q, wC (reg 1) q)] := by
                    rw [wcnf_cons_ge hqw, hr2]
                  refine ⟨[], (wA (reg 1) p, D) :: ps1, [(wA (reg 1) q, wC (reg 1) q)],
                    by rw [hP1]; rfl, by rw [hP2]; rfl, Or.inr ?_⟩
                  refine ⟨(wA (reg 1) p, D), ps1, (wA (reg 1) q, wC (reg 1) q), [],
                    rfl, rfl, ?_⟩
                  rcases hHL with h1 | h1
                  · exact Or.inl h1
                  · exact Or.inr ⟨h1.1, h1.2⟩
              | cons ac2 ps2 =>
                  by_cases hme : (wA (reg 1) q == ac2.1) = true
                  · have hP2 : (wcnf (reg 1) (q :: t2)).1
                        = (wA (reg 1) q, plus (wC (reg 1) q) ac2.2) :: ps2 := by
                      rw [wcnf_cons_ge hqw, hr2]
                      show ((if (wA (reg 1) q == ac2.1) = true
                          then ((wA (reg 1) q, plus (wC (reg 1) q) ac2.2) :: ps2, snd2)
                          else ((wA (reg 1) q, wC (reg 1) q) :: (ac2.1, ac2.2) :: ps2,
                                snd2)) : List (Term × Term) × Term).1 = _
                      rw [if_pos hme]
                    have hiac2 : inT ac2.2 = true :=
                      (hOK2 ac2 (by rw [hr2]; exact List.Mem.head _)).2.2.1
                    have hle2 : le (wC (reg 1) q) (plus (wC (reg 1) q) ac2.2) = true :=
                      le_self_plus_ap81 (inT_wC hiq) (isAP_omegaNF _) hiac2
                    refine ⟨[], (wA (reg 1) p, D) :: ps1,
                      (wA (reg 1) q, plus (wC (reg 1) q) ac2.2) :: ps2,
                      by rw [hP1]; rfl, by rw [hP2]; rfl, Or.inr ?_⟩
                    refine ⟨(wA (reg 1) p, D), ps1,
                      (wA (reg 1) q, plus (wC (reg 1) q) ac2.2), ps2, rfl, rfl, ?_⟩
                    rcases hHL with h1 | h1
                    · exact Or.inl h1
                    · refine Or.inr ⟨h1.1, ?_⟩
                      exact lt_of_lt_of_le3 (inT_le_fragR D hiD)
                        (inT_le_fragR _ (inT_wC hiq))
                        (inT_le_fragR _ (inT_plus (inT_wC hiq) hiac2)) h1.2 hle2
                  · have hP2 : (wcnf (reg 1) (q :: t2)).1
                        = (wA (reg 1) q, wC (reg 1) q) :: ac2 :: ps2 := by
                      rw [wcnf_cons_ge hqw, hr2]
                      show ((if (wA (reg 1) q == ac2.1) = true
                          then ((wA (reg 1) q, plus (wC (reg 1) q) ac2.2) :: ps2, snd2)
                          else ((wA (reg 1) q, wC (reg 1) q) :: (ac2.1, ac2.2) :: ps2,
                                snd2)) : List (Term × Term) × Term).1 = _
                      rw [if_neg hme]
                    refine ⟨[], (wA (reg 1) p, D) :: ps1,
                      (wA (reg 1) q, wC (reg 1) q) :: ac2 :: ps2,
                      by rw [hP1]; rfl, by rw [hP2]; rfl, Or.inr ?_⟩
                    refine ⟨(wA (reg 1) p, D), ps1,
                      (wA (reg 1) q, wC (reg 1) q), ac2 :: ps2, rfl, rfl, ?_⟩
                    rcases hHL with h1 | h1
                    · exact Or.inl h1
                    · exact Or.inr ⟨h1.1, h1.2⟩
          · -- equal heads: peel and lift the inner divergence through the merge
            have hpe : p = q := hpq.2.1
            subst hpe
            have hit1 : inT (ofList t1) = true := inT_ofList t1 hct1 hdt1
            have hit2 : inT (ofList t2) = true := inT_ofList t2 hct2 hdt2
            have hrec : lt (ofList t1) (ofList t2) = true :=
              lt_hd_eq_inv89 hi1 hi2 (toList_ofList89 hc1) (toList_ofList89 hc2)
                hit1 hit2 (toList_ofList89 hct1) (toList_ofList89 hct2) h
            have hIH := ih t2 hct1 hct2 hdt1 hdt2 hwt1 hwt2 hmt1 hmt2 hrec
            obtain ⟨R, S1, S2, e1, e2, hbr⟩ := hIH
            cases hr1 : wcnf (reg 1) t1 with
            | mk fst1 snd1 =>
              cases hr2 : wcnf (reg 1) t2 with
              | mk fst2 snd2 =>
                rw [hr1] at e1
                rw [hr2] at e2
                have e1' : fst1 = R ++ S1 := e1
                have e2' : fst2 = R ++ S2 := e2
                subst e1'
                subst e2'
                cases R with
                | cons ac R' =>
                    by_cases hme : (wA (reg 1) p == ac.1) = true
                    · have hP1 : (wcnf (reg 1) (p :: t1)).1
                          = (wA (reg 1) p, plus (wC (reg 1) p) ac.2) :: (R' ++ S1) := by
                        rw [wcnf_cons_ge hpw, hr1]
                        show ((if (wA (reg 1) p == ac.1) = true
                            then ((wA (reg 1) p, plus (wC (reg 1) p) ac.2) :: (R' ++ S1),
                                  snd1)
                            else ((wA (reg 1) p, wC (reg 1) p) :: (ac.1, ac.2)
                                  :: (R' ++ S1), snd1)) : List (Term × Term) × Term).1 = _
                        rw [if_pos hme]
                      have hP2 : (wcnf (reg 1) (p :: t2)).1
                          = (wA (reg 1) p, plus (wC (reg 1) p) ac.2) :: (R' ++ S2) := by
                        rw [wcnf_cons_ge hpw, hr2]
                        show ((if (wA (reg 1) p == ac.1) = true
                            then ((wA (reg 1) p, plus (wC (reg 1) p) ac.2) :: (R' ++ S2),
                                  snd2)
                            else ((wA (reg 1) p, wC (reg 1) p) :: (ac.1, ac.2)
                                  :: (R' ++ S2), snd2)) : List (Term × Term) × Term).1 = _
                        rw [if_pos hme]
                      exact ⟨(wA (reg 1) p, plus (wC (reg 1) p) ac.2) :: R', S1, S2,
                        by rw [hP1]; rfl, by rw [hP2]; rfl, hbr⟩
                    · have hP1 : (wcnf (reg 1) (p :: t1)).1
                          = (wA (reg 1) p, wC (reg 1) p) :: ac :: (R' ++ S1) := by
                        rw [wcnf_cons_ge hpw, hr1]
                        show ((if (wA (reg 1) p == ac.1) = true
                            then ((wA (reg 1) p, plus (wC (reg 1) p) ac.2) :: (R' ++ S1),
                                  snd1)
                            else ((wA (reg 1) p, wC (reg 1) p) :: (ac.1, ac.2)
                                  :: (R' ++ S1), snd1)) : List (Term × Term) × Term).1 = _
                        rw [if_neg hme]
                      have hP2 : (wcnf (reg 1) (p :: t2)).1
                          = (wA (reg 1) p, wC (reg 1) p) :: ac :: (R' ++ S2) := by
                        rw [wcnf_cons_ge hpw, hr2]
                        show ((if (wA (reg 1) p == ac.1) = true
                            then ((wA (reg 1) p, plus (wC (reg 1) p) ac.2) :: (R' ++ S2),
                                  snd2)
                            else ((wA (reg 1) p, wC (reg 1) p) :: (ac.1, ac.2)
                                  :: (R' ++ S2), snd2)) : List (Term × Term) × Term).1 = _
                        rw [if_neg hme]
                      exact ⟨(wA (reg 1) p, wC (reg 1) p) :: ac :: R', S1, S2,
                        by rw [hP1]; rfl, by rw [hP2]; rfl, hbr⟩
                | nil =>
                  rw [List.nil_append] at hr1 hr2
                  rcases hbr with ⟨hS1nil, hS2ne⟩ | ⟨x, tx, y, ty, hSx, hSy, hdiv⟩
                  · -- left tail has no pairs; the right tail's head either merges or not
                    subst hS1nil
                    have hP1 : (wcnf (reg 1) (p :: t1)).1
                        = [(wA (reg 1) p, wC (reg 1) p)] := by
                      rw [wcnf_cons_ge hpw, hr1]
                    cases hS2 : S2 with
                    | nil => exact absurd hS2 hS2ne
                    | cons ac2 ps2 =>
                        subst hS2
                        by_cases hme : (wA (reg 1) p == ac2.1) = true
                        · have hP2 : (wcnf (reg 1) (p :: t2)).1
                              = (wA (reg 1) p, plus (wC (reg 1) p) ac2.2) :: ps2 := by
                            rw [wcnf_cons_ge hpw, hr2]
                            show ((if (wA (reg 1) p == ac2.1) = true
                                then ((wA (reg 1) p, plus (wC (reg 1) p) ac2.2) :: ps2,
                                      snd2)
                                else ((wA (reg 1) p, wC (reg 1) p) :: (ac2.1, ac2.2)
                                      :: ps2, snd2)) : List (Term × Term) × Term).1 = _
                            rw [if_pos hme]
                          have hiac2 : inT ac2.2 = true :=
                            (hOK2 ac2 (by rw [hr2]; exact List.Mem.head _)).2.2.1
                          have hnz2 : ac2.2 ≠ zero :=
                            wcnf_cnz109 (inT_reg 1) (isSC_reg_succ 0) t2 hct2 hdt2 hmt2
                              ac2 (by rw [hr2]; exact List.Mem.head _)
                          refine ⟨[], [(wA (reg 1) p, wC (reg 1) p)],
                            (wA (reg 1) p, plus (wC (reg 1) p) ac2.2) :: ps2,
                            by rw [hP1]; rfl, by rw [hP2]; rfl, Or.inr ?_⟩
                          refine ⟨(wA (reg 1) p, wC (reg 1) p), [],
                            (wA (reg 1) p, plus (wC (reg 1) p) ac2.2), ps2, rfl, rfl, ?_⟩
                          refine Or.inr ⟨rfl, ?_⟩
                          exact lt_self_plus109 (inT_wC hip) (isAP_omegaNF _) hiac2 hnz2
                        · have hP2 : (wcnf (reg 1) (p :: t2)).1
                              = (wA (reg 1) p, wC (reg 1) p) :: ac2 :: ps2 := by
                            rw [wcnf_cons_ge hpw, hr2]
                            show ((if (wA (reg 1) p == ac2.1) = true
                                then ((wA (reg 1) p, plus (wC (reg 1) p) ac2.2) :: ps2,
                                      snd2)
                                else ((wA (reg 1) p, wC (reg 1) p) :: (ac2.1, ac2.2)
                                      :: ps2, snd2)) : List (Term × Term) × Term).1 = _
                            rw [if_neg hme]
                          exact ⟨[(wA (reg 1) p, wC (reg 1) p)], [], ac2 :: ps2,
                            by rw [hP1]; rfl, by rw [hP2]; rfl,
                            Or.inl ⟨rfl, List.cons_ne_nil _ _⟩⟩
                  · -- the tails diverge at their heads
                    subst hSx
                    subst hSy
                    rcases hdiv with hexp | hcoef
                    · -- exponent divergence x.1 < y.1
                      by_cases hmx : (wA (reg 1) p == x.1) = true
                      · -- impossible: y.1 ≤ wA p = x.1 < y.1
                        exfalso
                        obtain ⟨q2, rest2, ht2e, hq2w, hy1⟩ :=
                          wcnf_fst_cons109 (w := reg 1) t2 y ty (by rw [hr2])
                        have hiq2 : inT q2 = true := by
                          have := hct2
                          rw [ht2e] at this
                          exact (inTL_cons.mp this).1.2
                        have haq2 : q2.isAP = true := by
                          have := hct2
                          rw [ht2e] at this
                          exact (inTL_cons.mp this).1.1
                        have hq2p : le q2 p = true := by
                          have := hd2
                          rw [ht2e] at this
                          exact (descL_cons.mp this).1
                        have hq2M : lt q2 M = true := by
                          refine hmt2 q2 ?_
                          rw [ht2e]; exact List.Mem.head _
                        have hyA : le y.1 (wA (reg 1) p) = true := by
                          rw [hy1]
                          exact wA_mono154 haq2 hiq2 hq2M hq2w hap hip hpM hpw hq2p
                        have hx1 : lt (wA (reg 1) p) y.1 = true := by
                          rw [eq_of_beq hmx]; exact hexp
                        have hiy1 : inT y.1 = true :=
                          (hOK2 y (by rw [hr2]; exact List.Mem.head _)).1
                        have hiwAp : inT (wA (reg 1) p) = true :=
                          inT_wA109 (inT_reg 1) (isSC_reg_succ 0) hip
                        have : lt (wA (reg 1) p) (wA (reg 1) p) = true :=
                          lt_of_lt_of_le3 (inT_le_fragR _ hiwAp) (inT_le_fragR _ hiy1)
                            (inT_le_fragR _ hiwAp) hx1 hyA
                        rw [lt_irrefl] at this
                        exact Bool.noConfusion this
                      · by_cases hmy : (wA (reg 1) p == y.1) = true
                        · -- the right head merges, the left does not
                          have hP1 : (wcnf (reg 1) (p :: t1)).1
                              = (wA (reg 1) p, wC (reg 1) p) :: x :: tx := by
                            rw [wcnf_cons_ge hpw, hr1]
                            show ((if (wA (reg 1) p == x.1) = true
                                then ((wA (reg 1) p, plus (wC (reg 1) p) x.2) :: tx, snd1)
                                else ((wA (reg 1) p, wC (reg 1) p) :: (x.1, x.2)
                                      :: tx, snd1)) : List (Term × Term) × Term).1 = _
                            rw [if_neg hmx]
                          have hP2 : (wcnf (reg 1) (p :: t2)).1
                              = (wA (reg 1) p, plus (wC (reg 1) p) y.2) :: ty := by
                            rw [wcnf_cons_ge hpw, hr2]
                            show ((if (wA (reg 1) p == y.1) = true
                                then ((wA (reg 1) p, plus (wC (reg 1) p) y.2) :: ty, snd2)
                                else ((wA (reg 1) p, wC (reg 1) p) :: (y.1, y.2)
                                      :: ty, snd2)) : List (Term × Term) × Term).1 = _
                            rw [if_pos hmy]
                          have hiy2 : inT y.2 = true :=
                            (hOK2 y (by rw [hr2]; exact List.Mem.head _)).2.2.1
                          have hnz2 : y.2 ≠ zero :=
                            wcnf_cnz109 (inT_reg 1) (isSC_reg_succ 0) t2 hct2 hdt2 hmt2
                              y (by rw [hr2]; exact List.Mem.head _)
                          refine ⟨[], (wA (reg 1) p, wC (reg 1) p) :: x :: tx,
                            (wA (reg 1) p, plus (wC (reg 1) p) y.2) :: ty,
                            by rw [hP1]; rfl, by rw [hP2]; rfl, Or.inr ?_⟩
                          refine ⟨(wA (reg 1) p, wC (reg 1) p), x :: tx,
                            (wA (reg 1) p, plus (wC (reg 1) p) y.2), ty, rfl, rfl, ?_⟩
                          refine Or.inr ⟨rfl, ?_⟩
                          exact lt_self_plus109 (inT_wC hip) (isAP_omegaNF _) hiy2 hnz2
                        · -- neither head merges
                          have hP1 : (wcnf (reg 1) (p :: t1)).1
                              = (wA (reg 1) p, wC (reg 1) p) :: x :: tx := by
                            rw [wcnf_cons_ge hpw, hr1]
                            show ((if (wA (reg 1) p == x.1) = true
                                then ((wA (reg 1) p, plus (wC (reg 1) p) x.2) :: tx, snd1)
                                else ((wA (reg 1) p, wC (reg 1) p) :: (x.1, x.2)
                                      :: tx, snd1)) : List (Term × Term) × Term).1 = _
                            rw [if_neg hmx]
                          have hP2 : (wcnf (reg 1) (p :: t2)).1
                              = (wA (reg 1) p, wC (reg 1) p) :: y :: ty := by
                            rw [wcnf_cons_ge hpw, hr2]
                            show ((if (wA (reg 1) p == y.1) = true
                                then ((wA (reg 1) p, plus (wC (reg 1) p) y.2) :: ty, snd2)
                                else ((wA (reg 1) p, wC (reg 1) p) :: (y.1, y.2)
                                      :: ty, snd2)) : List (Term × Term) × Term).1 = _
                            rw [if_neg hmy]
                          exact ⟨[(wA (reg 1) p, wC (reg 1) p)], x :: tx, y :: ty,
                            by rw [hP1]; rfl, by rw [hP2]; rfl,
                            Or.inr ⟨x, tx, y, ty, rfl, rfl, Or.inl hexp⟩⟩
                    · -- coefficient divergence: x.1 = y.1, x.2 < y.2
                      obtain ⟨hxy1, hxy2⟩ := hcoef
                      by_cases hmx : (wA (reg 1) p == x.1) = true
                      · have hmy : (wA (reg 1) p == y.1) = true := by
                          rw [← hxy1]; exact hmx
                        have hP1 : (wcnf (reg 1) (p :: t1)).1
                            = (wA (reg 1) p, plus (wC (reg 1) p) x.2) :: tx := by
                          rw [wcnf_cons_ge hpw, hr1]
                          show ((if (wA (reg 1) p == x.1) = true
                              then ((wA (reg 1) p, plus (wC (reg 1) p) x.2) :: tx, snd1)
                              else ((wA (reg 1) p, wC (reg 1) p) :: (x.1, x.2)
                                    :: tx, snd1)) : List (Term × Term) × Term).1 = _
                          rw [if_pos hmx]
                        have hP2 : (wcnf (reg 1) (p :: t2)).1
                            = (wA (reg 1) p, plus (wC (reg 1) p) y.2) :: ty := by
                          rw [wcnf_cons_ge hpw, hr2]
                          show ((if (wA (reg 1) p == y.1) = true
                              then ((wA (reg 1) p, plus (wC (reg 1) p) y.2) :: ty, snd2)
                              else ((wA (reg 1) p, wC (reg 1) p) :: (y.1, y.2)
                                    :: ty, snd2)) : List (Term × Term) × Term).1 = _
                          rw [if_pos hmy]
                        have hix2 : inT x.2 = true :=
                          (hOK1 x (by rw [hr1]; exact List.Mem.head _)).2.2.1
                        have hiy2 : inT y.2 = true :=
                          (hOK2 y (by rw [hr2]; exact List.Mem.head _)).2.2.1
                        refine ⟨[], (wA (reg 1) p, plus (wC (reg 1) p) x.2) :: tx,
                          (wA (reg 1) p, plus (wC (reg 1) p) y.2) :: ty,
                          by rw [hP1]; rfl, by rw [hP2]; rfl, Or.inr ?_⟩
                        refine ⟨(wA (reg 1) p, plus (wC (reg 1) p) x.2), tx,
                          (wA (reg 1) p, plus (wC (reg 1) p) y.2), ty, rfl, rfl, ?_⟩
                        refine Or.inr ⟨rfl, ?_⟩
                        exact plus_smono_right_inT79 (wC (reg 1) p) (inT_wC hip)
                          x.2 y.2 hix2 hiy2 hxy2
                      · have hmy : (wA (reg 1) p == y.1) = false := by
                          rw [← hxy1]; exact bool_false hmx
                        have hP1 : (wcnf (reg 1) (p :: t1)).1
                            = (wA (reg 1) p, wC (reg 1) p) :: x :: tx := by
                          rw [wcnf_cons_ge hpw, hr1]
                          show ((if (wA (reg 1) p == x.1) = true
                              then ((wA (reg 1) p, plus (wC (reg 1) p) x.2) :: tx, snd1)
                              else ((wA (reg 1) p, wC (reg 1) p) :: (x.1, x.2)
                                    :: tx, snd1)) : List (Term × Term) × Term).1 = _
                          rw [if_neg hmx]
                        have hP2 : (wcnf (reg 1) (p :: t2)).1
                            = (wA (reg 1) p, wC (reg 1) p) :: y :: ty := by
                          rw [wcnf_cons_ge hpw, hr2]
                          show ((if (wA (reg 1) p == y.1) = true
                              then ((wA (reg 1) p, plus (wC (reg 1) p) y.2) :: ty, snd2)
                              else ((wA (reg 1) p, wC (reg 1) p) :: (y.1, y.2)
                                    :: ty, snd2)) : List (Term × Term) × Term).1 = _
                          rw [if_neg (by rw [hmy]; exact Bool.noConfusion)]
                        exact ⟨[(wA (reg 1) p, wC (reg 1) p)], x :: tx, y :: ty,
                          by rw [hP1]; rfl, by rw [hP2]; rfl,
                          Or.inr ⟨x, tx, y, ty, rfl, rfl, Or.inr ⟨hxy1, hxy2⟩⟩⟩
          · -- reversed heads contradict the hypothesis
            exfalso
            have h2 : lt (ofList (q :: t2)) (ofList (p :: t1)) = true :=
              lt_of_hd_lt hi2 hi1 (toList_ofList89 hc2) (toList_ofList89 hc1) hpq.2.2
            rw [lt_asymm_inT hi1 hi2 h] at h2
            exact Bool.noConfusion h2

/-- **`1 ⊖` は 0 でない項の上で狭義単調。** -/
theorem sub1_smono154 {c c' : Term} (hic : inT c = true) (hic' : inT c' = true)
    (hnz : c ≠ zero) (h : lt c c' = true) : lt (sub1 c) (sub1 c') = true := by
  cases hlc : toList c with
  | nil => exact absurd (toList_eq_nil c hlc) hnz
  | cons b r =>
      cases hlc' : toList c' with
      | nil =>
          exfalso
          rw [toList_eq_nil c' hlc', lt_zero_right] at h
          exact Bool.noConfusion h
      | cons b' r' =>
          have hcb := (inT_toList c hic).1
          have hdb := (inT_toList c hic).2
          have hcb' := (inT_toList c' hic').1
          have hdb' := (inT_toList c' hic').2
          rw [hlc] at hcb hdb
          rw [hlc'] at hcb' hdb'
          obtain ⟨⟨hab, hib⟩, hcr⟩ := inTL_cons.mp hcb
          obtain ⟨⟨hab', hib'⟩, hcr'⟩ := inTL_cons.mp hcb'
          have hir : inT (ofList r) = true := inT_ofList r hcr (descL_tail hdb)
          have hir' : inT (ofList r') = true := inT_ofList r' hcr' (descL_tail hdb')
          rw [show sub1 c = subAP TM.Term.one c from rfl,
            show sub1 c' = subAP TM.Term.one c' from rfl,
            subAP_eq154 hlc, subAP_eq154 hlc']
          by_cases hq : (b == TM.Term.one) = true
          · rw [if_pos hq]
            by_cases hq' : (b' == TM.Term.one) = true
            · -- both heads are 1 — peel them
              rw [if_pos hq']
              have hbb : b' = b := by rw [eq_of_beq hq, eq_of_beq hq']
              exact lt_hd_eq_inv89 hic hic' hlc (by rw [hlc', hbb]) hir hir'
                (toList_ofList89 hcr) (toList_ofList89 hcr') h
            · -- left head is 1, the right head is strictly above 1
              rw [if_neg hq']
              have h1b' : lt TM.Term.one b' = true := by
                rcases lt_trichotomy_inT inT_one hib' with h2 | h2 | h2
                · exact h2.1
                · exfalso
                  have : (b' == TM.Term.one) = true := by
                    rw [← h2.2.1]; exact beq_self_eq_true _
                  rw [this] at hq'; exact hq' rfl
                · exfalso
                  have hz : b' = zero :=
                    lt_one_zero148 b'.deg b' (Nat.le_refl _) hib' h2.2.2
                  rw [hz] at hab'
                  exact Bool.noConfusion hab'
              have hcne : c' ≠ zero := by
                intro hz
                rw [hz] at hlc'
                exact List.cons_ne_nil b' r' (by rw [← hlc']; rfl)
              cases hr : r with
              | nil => exact lt_zero_left hcne
              | cons d r2 =>
                  subst hr
                  have hid : inT d = true := (inTL_cons.mp hcr).1.2
                  have hd1 : le d b = true :=
                    descL_bound_inT (d :: r2) b hib hcr hdb d (List.Mem.head _)
                  have hdb2 : lt d b' = true := by
                    refine lt_of_le_of_lt3 (inT_le_fragR d hid) (inT_le_fragR b hib)
                      (inT_le_fragR b' hib') hd1 ?_
                    rw [eq_of_beq hq]; exact h1b'
                  exact lt_of_hd_lt hir hic' (toList_ofList89 hcr) hlc' hdb2
          · rw [if_neg hq]
            by_cases hq' : (b' == TM.Term.one) = true
            · -- impossible: c < c' forces b ≤ b' = 1, so b = 1
              exfalso
              have hble : le b b' = true := hd_mono_inT hic hic' hlc hlc' (le_of_lt h)
              rcases (Bool.or_eq_true _ _).mp hble with he | hl2
              · rw [eq_of_beq he] at hq
                rw [hq'] at hq
                exact hq rfl
              · have hb1 : lt b TM.Term.one = true := by
                  rw [← eq_of_beq hq']; exact hl2
                have hz : b = zero := lt_one_zero148 b.deg b (Nat.le_refl _) hib hb1
                rw [hz] at hab
                exact Bool.noConfusion hab
            · rw [if_neg hq']; exact h

/-- 前置きを削っても真の降順は残る。 -/
theorem descP_suffix154 : ∀ (l1 l2 : List (Term × Term)),
    descP118 (l1 ++ l2) → descP118 l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 h; exact h
  | cons a l1' ih => intro l2 h; exact ih l2 (descP_tail118 h)

/-- 真の降順のもとで、後ろの指数は頭の指数より狭義に下。 -/
theorem descP_bound154 : ∀ (l : List (Term × Term)) (a : Term × Term),
    (∀ w ∈ a :: l, inT w.1 = true) → descP118 (a :: l) →
    ∀ z ∈ l, lt z.1 a.1 = true := by
  intro l
  induction l with
  | nil => intro a _ _ z hz; cases hz
  | cons b r ih =>
      intro a hin hd z hz
      obtain ⟨hba, hbr⟩ := hd
      rcases List.mem_cons.mp hz with h1 | h1
      · rw [h1]; exact hba
      · have hzb : lt z.1 b.1 = true :=
          ih b (fun w hw => hin w (List.Mem.tail _ hw)) hbr z h1
        exact lt_trans_inT (hin z (List.Mem.tail _ (List.Mem.tail _ h1)))
          (hin b (List.Mem.tail _ (List.Mem.head _)))
          (hin a (List.Mem.head _)) hzb hba

/-- **`wcnf` の指数の列は真の降順。**  併合が隣り合う同指数をすべて呑むから。 -/
theorem wcnf_descP154 : ∀ (L : List Term), inTL L = true → descL L = true →
    (∀ z ∈ L, lt z M = true) → descP118 (wcnf (reg 1) L).1 := by
  intro L
  induction L with
  | nil => intro _ _ _; trivial
  | cons p rest ih =>
      intro hc hd hm
      obtain ⟨⟨hap, hip⟩, hcr⟩ := inTL_cons.mp hc
      have hdr := descL_tail hd
      have hmr : ∀ z ∈ rest, lt z M = true := fun z hz => hm z (List.Mem.tail p hz)
      by_cases hlp : lt p (reg 1) = true
      · rw [wcnf_cons_lt hlp]
        trivial
      · have hlp' : lt p (reg 1) = false := bool_false hlp
        have hIH := ih hcr hdr hmr
        cases hr : wcnf (reg 1) rest with
        | mk fst snd =>
          have hIH' : descP118 fst := by rw [hr] at hIH; exact hIH
          cases fst with
          | nil =>
              have hP : (wcnf (reg 1) (p :: rest)).1 = [(wA (reg 1) p, wC (reg 1) p)] := by
                rw [wcnf_cons_ge hlp', hr]
              rw [hP]
              trivial
          | cons ac' ps =>
              by_cases hme : (wA (reg 1) p == ac'.1) = true
              · have hP : (wcnf (reg 1) (p :: rest)).1
                    = (wA (reg 1) p, plus (wC (reg 1) p) ac'.2) :: ps := by
                  rw [wcnf_cons_ge hlp', hr]
                  show ((if (wA (reg 1) p == ac'.1) = true
                      then ((wA (reg 1) p, plus (wC (reg 1) p) ac'.2) :: ps, snd)
                      else ((wA (reg 1) p, wC (reg 1) p) :: (ac'.1, ac'.2) :: ps,
                            snd)) : List (Term × Term) × Term).1 = _
                  rw [if_pos hme]
                rw [hP]
                cases ps with
                | nil => trivial
                | cons b r =>
                    refine ⟨?_, hIH'.2⟩
                    show lt b.1 (wA (reg 1) p) = true
                    rw [eq_of_beq hme]
                    exact hIH'.1
              · have hP : (wcnf (reg 1) (p :: rest)).1
                    = (wA (reg 1) p, wC (reg 1) p) :: ac' :: ps := by
                  rw [wcnf_cons_ge hlp', hr]
                  show ((if (wA (reg 1) p == ac'.1) = true
                      then ((wA (reg 1) p, plus (wC (reg 1) p) ac'.2) :: ps, snd)
                      else ((wA (reg 1) p, wC (reg 1) p) :: (ac'.1, ac'.2) :: ps,
                            snd)) : List (Term × Term) × Term).1 = _
                  rw [if_neg hme]
                rw [hP]
                obtain ⟨q, rest', hre, hqw, hac1⟩ :=
                  wcnf_fst_cons109 (w := reg 1) rest ac' ps (by rw [hr])
                have hiq : inT q = true := by
                  have := hcr
                  rw [hre] at this
                  exact (inTL_cons.mp this).1.2
                have haq : q.isAP = true := by
                  have := hcr
                  rw [hre] at this
                  exact (inTL_cons.mp this).1.1
                have hqM : lt q M = true := by
                  refine hmr q ?_
                  rw [hre]; exact List.Mem.head _
                have hqp : le q p = true := by
                  have := hd
                  rw [hre] at this
                  exact (descL_cons.mp this).1
                have hAle : le (wA (reg 1) q) (wA (reg 1) p) = true :=
                  wA_mono154 haq hiq hqM hqw hap hip (hm p (List.Mem.head _)) hlp' hqp
                have hAlt : lt ac'.1 (wA (reg 1) p) = true := by
                  rw [hac1]
                  rcases (Bool.or_eq_true _ _).mp hAle with he | hl2
                  · exfalso
                    have : (wA (reg 1) p == ac'.1) = true := by
                      rw [hac1, ← eq_of_beq he]
                      exact beq_self_eq_true _
                    rw [this] at hme
                    exact hme rfl
                  · exact hl2
                exact ⟨hAlt, hIH'⟩

/-- 最後の一歩の指数は最後の対の指数そのもの。 -/
theorem lastStep_fst154 {y : Term} {ca pa : Term × Term}
    (hac : lastAC151 y = some ca) (hls : lastStep129 y = some pa) : pa.1 = ca.1 := by
  cases hpv : prevV151 y with
  | none =>
      rw [lastStep_prev_none151 hac hpv] at hls
      rw [← Option.some.inj hls]
  | some v =>
      rw [lastStep_prev_some151 hac hpv] at hls
      rw [← Option.some.inj hls]

/-- **§154 の残り — 途中で割れる組の支配。**  適格で最後の指数が等しく `hi` が増え、
    対リストが最後の対より前で割れる (共通の前置き `R` の直後、どちらかの側に
    まだ対が残る) とき、条項 (ii) が立つ — 左の `X` は右の接頭辞の値より下。
    §151 の測定では全数の掃き (13 記号、6548370 義務) の 4467597 組がここに乗り、
    外れは 0。 -/
def Dom154 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lastFire92 (dict a) = false → lastFire92 (dict b) = false →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    sameExp145 a b = true →
    ∀ (R : List (Term × Term)) (x : Term × Term) (tx : List (Term × Term))
      (y : Term × Term) (ty : List (Term × Term)),
      (wcnf (reg 1) (toList (dict a))).1 = R ++ x :: tx →
      (wcnf (reg 1) (toList (dict b))).1 = R ++ y :: ty →
      (tx ≠ [] ∨ ty ≠ []) →
      (lt x.1 y.1 = true ∨ (x.1 = y.1 ∧ lt x.2 y.2 = true)) →
      tail2_151 (lastStep129 (dict a)) (prevV151 (dict b)) = true

/-- **§154 の主定理 — `TailOK151` は `Dom154` に還る。**  運搬定理が対リストを
    「共通の前置き + 分岐」に割り、最後の対どうしで割れる組は条項 (i) が閉じ、
    前置きで尽きる組は指数の真の降順と最後の指数の一致が両立しない。残るのは
    途中で割れる組 — それが `Dom154` である。 -/
theorem tailOK151_of_dom154 (Hp : PsiIdxOKStd172) (HD : Dom154) : TailOK151 := by
  intro a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hse
  obtain ⟨hia, hlaM, hpa⟩ := dictFacts151 Hp hbA hsA
  obtain ⟨hib, hlbM, hpb⟩ := dictFacts151 Hp hbB hsB
  have hcLa := (inT_toList _ hia).1
  have hdLa := (inT_toList _ hia).2
  have hcLb := (inT_toList _ hib).1
  have hdLb := (inT_toList _ hib).2
  have hmLa : ∀ z ∈ toList (dict a), lt z M = true := ltM_toList _ hia hlaM
  have hmLb : ∀ z ∈ toList (dict b), lt z M = true := ltM_toList _ hib hlbM
  obtain ⟨_, hOKa⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0)
    (toList (dict a)) hcLa hdLa hmLa
  obtain ⟨_, hOKb⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0)
    (toList (dict b)) hcLb hdLb hmLb
  cases hrevA : (wcnf (reg 1) (toList (dict a))).1.reverse with
  | nil =>
      exfalso
      have hln : lastStep129 (dict a) = none := by unfold lastStep129; rw [hrevA]
      have hf : sameExp145 a b = false := by unfold sameExp145; rw [hln]
      rw [hf] at hse
      exact Bool.noConfusion hse
  | cons ca ra =>
  cases hrevB : (wcnf (reg 1) (toList (dict b))).1.reverse with
  | nil =>
      exfalso
      have hln : lastStep129 (dict b) = none := by unfold lastStep129; rw [hrevB]
      have hf : sameExp145 a b = false := by
        unfold sameExp145
        rw [hln]
        cases lastStep129 (dict a) <;> rfl
      rw [hf] at hse
      exact Bool.noConfusion hse
  | cons cb rb =>
  have hacA : lastAC151 (dict a) = some ca := by unfold lastAC151; rw [hrevA]
  have hacB : lastAC151 (dict b) = some cb := by unfold lastAC151; rw [hrevB]
  have hmemA : ca ∈ (wcnf (reg 1) (toList (dict a))).1 :=
    List.mem_reverse.mp (by rw [hrevA]; exact List.Mem.head _)
  have hmemB : cb ∈ (wcnf (reg 1) (toList (dict b))).1 :=
    List.mem_reverse.mp (by rw [hrevB]; exact List.Mem.head _)
  obtain ⟨Xa, hlsA⟩ : ∃ X, lastStep129 (dict a) = some (ca.1, X) := by
    cases hpv : prevV151 (dict a) with
    | none => exact ⟨_, lastStep_prev_none151 hacA hpv⟩
    | some v => exact ⟨_, lastStep_prev_some151 hacA hpv⟩
  obtain ⟨Xb, hlsB⟩ : ∃ X, lastStep129 (dict b) = some (cb.1, X) := by
    cases hpv : prevV151 (dict b) with
    | none => exact ⟨_, lastStep_prev_none151 hacB hpv⟩
    | some v => exact ⟨_, lastStep_prev_some151 hacB hpv⟩
  have hexpEq : ca.1 = cb.1 := by
    have he : sameExp145 a b = ((ca.1 : Term) == cb.1) := by
      unfold sameExp145; rw [hlsA, hlsB]
    rw [he] at hse
    exact eq_of_beq hse
  have hlt' : lt (ofList (toList (hiW89 (dict a))))
      (ofList (toList (hiW89 (dict b)))) = true := by
    rw [inT_ofList_toList _ (inT_hiW89 hia), inT_ofList_toList _ (inT_hiW89 hib)]
    exact hlt
  have hPL := transport154 (toList (hiW89 (dict a))) (toList (hiW89 (dict b)))
    (inT_toList _ (inT_hiW89 hia)).1 (inT_toList _ (inT_hiW89 hib)).1
    (inT_toList _ (inT_hiW89 hia)).2 (inT_toList _ (inT_hiW89 hib)).2
    (hiW89_ge89 hia) (hiW89_ge89 hib)
    (fun z hz => by
      rw [toList_hiW89 hia] at hz
      exact hmLa z (List.mem_filter.mp hz).1)
    (fun z hz => by
      rw [toList_hiW89 hib] at hz
      exact hmLb z (List.mem_filter.mp hz).1)
    hlt'
  rw [wcnfFst_hiW101 hia, wcnfFst_hiW101 hib] at hPL
  obtain ⟨R, S1, S2, e1, e2, hbr⟩ := hPL
  rcases hbr with ⟨hS1nil, hS2ne⟩ | ⟨x, tx, yb, ty, hSx, hSy, hdiv⟩
  · -- 前置きで尽きる側 — 指数の真の降順と最後の指数の一致が両立しない
    exfalso
    subst hS1nil
    rw [List.append_nil] at e1
    have hRrev : R.reverse = ca :: ra := by rw [← e1]; exact hrevA
    have hRe : R = ra.reverse ++ [ca] := by
      have h2 := congrArg List.reverse hRrev
      rw [List.reverse_reverse, List.reverse_cons] at h2
      exact h2
    have hdP : descP118 ((wcnf (reg 1) (toList (dict b))).1) :=
      wcnf_descP154 _ hcLb hdLb hmLb
    rw [e2, hRe, List.append_assoc] at hdP
    have hdP2 : descP118 (ca :: S2) := descP_suffix154 _ _ hdP
    cases hS2r : S2.reverse with
    | nil =>
        refine hS2ne ?_
        rw [← List.reverse_reverse S2, hS2r]
        rfl
    | cons cb2 rb2 =>
        have hcb2mem : cb2 ∈ S2 :=
          List.mem_reverse.mp (by rw [hS2r]; exact List.Mem.head _)
        have hrevB2 : (wcnf (reg 1) (toList (dict b))).1.reverse
            = cb2 :: (rb2 ++ R.reverse) := by
          rw [e2, List.reverse_append, hS2r]
          rfl
        have hcbe : cb = cb2 := by
          have h2 := hrevB.symm.trans hrevB2
          injection h2 with h3 _
        have hIn : ∀ w ∈ ca :: S2, inT w.1 = true := by
          intro w hw
          rcases List.mem_cons.mp hw with h1 | h1
          · rw [h1]
            refine (hOKb ca ?_).1
            rw [e2, hRe]
            exact List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _))
          · refine (hOKb w ?_).1
            rw [e2]
            exact List.mem_append_right _ h1
        have hlast : lt cb2.1 ca.1 = true := descP_bound154 S2 ca hIn hdP2 cb2 hcb2mem
        rw [← hcbe, hexpEq, lt_irrefl] at hlast
        exact Bool.noConfusion hlast
  · subst hSx
    subst hSy
    by_cases hboth : tx = [] ∧ ty = []
    · -- 最後の対どうしで割れる — 条項 (i)
      obtain ⟨htx, hty⟩ := hboth
      subst htx
      subst hty
      have hrevA2 : (wcnf (reg 1) (toList (dict a))).1.reverse = x :: R.reverse := by
        rw [e1, List.reverse_append]
        rfl
      have hrevB2 : (wcnf (reg 1) (toList (dict b))).1.reverse = yb :: R.reverse := by
        rw [e2, List.reverse_append]
        rfl
      have hxa : ca = x ∧ ra = R.reverse := by
        have h2 := hrevA.symm.trans hrevA2
        injection h2 with h3 h4
        exact ⟨h3, h4⟩
      have hyb : cb = yb ∧ rb = R.reverse := by
        have h2 := hrevB.symm.trans hrevB2
        injection h2 with h3 h4
        exact ⟨h3, h4⟩
      rcases hdiv with hexp | ⟨hE, hC⟩
      · exfalso
        rw [← hxa.1, ← hyb.1, ← hexpEq, lt_irrefl] at hexp
        exact Bool.noConfusion hexp
      · have hCc : lt ca.2 cb.2 = true := by rw [hxa.1, hyb.1]; exact hC
        have hpva : prevV151 (dict a)
            = ((R.reverse).reverse.foldl (stepF (reg 1) (baseOf 0))
               ((none : Option Term), (none : Option Term))).2 := by
          unfold prevV151
          rw [hrevA2]
        have hpvb : prevV151 (dict b)
            = ((R.reverse).reverse.foldl (stepF (reg 1) (baseOf 0))
               ((none : Option Term), (none : Option Term))).2 := by
          unfold prevV151
          rw [hrevB2]
        have hPVeq : prevV151 (dict a) = prevV151 (dict b) := by rw [hpva, hpvb]
        have hia2 : inT ca.2 = true := (hOKa ca hmemA).2.2.1
        have hib2 : inT cb.2 = true := (hOKb cb hmemB).2.2.1
        cases hpv : prevV151 (dict a) with
        | none =>
            have hpvB : prevV151 (dict b) = none := by rw [← hPVeq]; exact hpv
            have hnz : ca.2 ≠ zero :=
              wcnf_cnz109 (inT_reg 1) (isSC_reg_succ 0) _ hcLa hdLa hmLa ca hmemA
            have hsub : lt (sub1 ca.2) (sub1 cb.2) = true :=
              sub1_smono154 hia2 hib2 hnz hCc
            show (tail1_151 (prevV151 (dict a)) (prevV151 (dict b)) (lastAC151 (dict a))
                (lastAC151 (dict b))
              || tail2_151 (lastStep129 (dict a)) (prevV151 (dict b))) = true
            rw [hpv, hpvB, hacA, hacB]
            show (lt (sub1 ca.2) (sub1 cb.2)
              || tail2_151 (lastStep129 (dict a)) none) = true
            rw [hsub]
            rfl
        | some v =>
            have hpvB : prevV151 (dict b) = some v := by rw [← hPVeq]; exact hpv
            show (tail1_151 (prevV151 (dict a)) (prevV151 (dict b)) (lastAC151 (dict a))
                (lastAC151 (dict b))
              || tail2_151 (lastStep129 (dict a)) (prevV151 (dict b))) = true
            rw [hpv, hpvB, hacA, hacB]
            show (((v == v) && lt ca.2 cb.2)
              || tail2_151 (lastStep129 (dict a)) (some v)) = true
            rw [beq_self_eq_true, hCc]
            rfl
    · -- 途中で割れる — `Dom154` が受け取る
      have hor : tx ≠ [] ∨ ty ≠ [] := by
        by_cases htx : tx = []
        · right
          intro hty
          exact hboth ⟨htx, hty⟩
        · left
          exact htx
      have hdom := HD a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hse
        R x tx yb ty e1 e2 hor hdiv
      show (tail1_151 (prevV151 (dict a)) (prevV151 (dict b)) (lastAC151 (dict a))
          (lastAC151 (dict b))
        || tail2_151 (lastStep129 (dict a)) (prevV151 (dict b))) = true
      rw [hdom]
      exact Bool.or_true _

#print axioms tailOK151_of_dom154

/-- **系 — 第二の門の同指数の半分は `Dom154` に還る。** -/
theorem xmono145_of_dom154 (Hp : PsiIdxOKStd172) (HD : Dom154) : XMono145 :=
  xmono145_of_tailOK151 Hp (tailOK151_of_dom154 Hp HD)

#print axioms xmono145_of_dom154

/-! ### §154 MEASUREMENT — the trichotomy on the frozen pools

運搬定理の言う三分岐を §151 の母集団の上で数える。読み方は
(退化した形, 最後の対どうしの割れ, そのうち条項 (i) が外れる数,
 途中の割れ = `Dom154` の義務, そのうち条項 (ii) が外れる数,
 割れの向きが辞書式で下がらない数)。定理の言う通りなら 1・3・5・6 列目は 0。 -/

/-- 共通の前置きを剥がす。 -/
def stripPre154 : List (Term × Term) → List (Term × Term) →
    (List (Term × Term) × List (Term × Term))
  | x :: t1, y :: t2 => if x == y then stripPre154 t1 t2 else (x :: t1, y :: t2)
  | l1, l2 => (l1, l2)

def dq154 (a : BT) : Q151 × List (Term × Term) :=
  (dq151 a, (wcnf (reg 1) (toList (dict a))).1)

def cnt154 (L : List BT) : Nat × Nat × Nat × Nat × Nat × Nat :=
  let D := (L.filter qual151).map dq154
  D.foldl (fun (acc : Nat × Nat × Nat × Nat × Nat × Nat) x =>
      D.foldl (fun (r : Nat × Nat × Nat × Nat × Nat × Nat) y =>
        if lt x.1.1.1 y.1.1.1 && sameQ151 x.1 y.1 then
          match stripPre154 x.2 y.2 with
          | (xx :: t1, yy :: t2) =>
              let lex := lt xx.1 yy.1 || ((xx.1 == yy.1) && lt xx.2 yy.2)
              if t1.isEmpty && t2.isEmpty then
                (r.1, r.2.1 + 1, r.2.2.1 + (if d1Q151 x.1 y.1 then 0 else 1),
                 r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2 + (if lex then 0 else 1))
              else
                (r.1, r.2.1, r.2.2.1,
                 r.2.2.2.1 + 1, r.2.2.2.2.1 + (if d2Q151 x.1 y.1 then 0 else 1),
                 r.2.2.2.2.2 + (if lex then 0 else 1))
          | _ => (r.1 + 1, r.2)
        else r) acc) (0, 0, 0, 0, 0, 0)

/-! 三分岐の実測 — §151 の条項の分割と一致する。二列目 (最後の対どうしの割れ) は
§151 の条項 (i) の列そのもの、四列目 (途中の割れ = `Dom154` の義務) は条項 (ii) の
列そのもの。退化した形・条項の外れ・辞書式で下がらない割れは 0。 -/

#guard cnt154 poolD151 == (0, 420, 0, 840, 0, 0)
#guard cnt154 poolC151 == (0, 244, 0, 2126, 0, 0)
#guard cnt154 poolE151 == (0, 146, 0, 25542, 0, 0)
#guard cnt154 poolA151 == (0, 720, 0, 53048, 0, 0)

/-- **`Dom154` の割れの形は強いられている。**  途中の割れが `a` の最後の対で
    起きる (`tx = []`) なら、指数の一致 (`x.1 = y.1`) はあり得ない — 右の列の
    真の降順と最後の指数の一致が両立しないから。残る `Dom154` の中身は
    「`tx ≠ []`か、指数が狭義に下がる割れ」だけである。 -/
theorem domShape154 (Hp : PsiIdxOKStd172) {a b : BT}
    (hbB : btLe72 1 (BT.D 0 b) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (hse : sameExp145 a b = true)
    {R : List (Term × Term)} {x : Term × Term} {y : Term × Term}
    {ty : List (Term × Term)}
    (e1 : (wcnf (reg 1) (toList (dict a))).1 = R ++ [x])
    (e2 : (wcnf (reg 1) (toList (dict b))).1 = R ++ y :: ty)
    (hty : ty ≠ [])
    (hE : x.1 = y.1) : False := by
  obtain ⟨hib, hlbM, hpb⟩ := dictFacts151 Hp hbB hsB
  have hcLb := (inT_toList _ hib).1
  have hdLb := (inT_toList _ hib).2
  have hmLb : ∀ z ∈ toList (dict b), lt z M = true := ltM_toList _ hib hlbM
  obtain ⟨_, hOKb⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0)
    (toList (dict b)) hcLb hdLb hmLb
  -- a's last pair is x
  have hrevA : (wcnf (reg 1) (toList (dict a))).1.reverse = x :: R.reverse := by
    rw [e1, List.reverse_append]
    rfl
  have hacA : lastAC151 (dict a) = some x := by unfold lastAC151; rw [hrevA]
  obtain ⟨Xa, hlsA⟩ : ∃ X, lastStep129 (dict a) = some (x.1, X) := by
    cases hpv : prevV151 (dict a) with
    | none => exact ⟨_, lastStep_prev_none151 hacA hpv⟩
    | some v => exact ⟨_, lastStep_prev_some151 hacA hpv⟩
  -- b's last pair cb sits inside ty
  cases htyr : ty.reverse with
  | nil =>
      refine hty ?_
      rw [← List.reverse_reverse ty, htyr]
      rfl
  | cons cb tyr =>
      have hcbmem : cb ∈ ty := List.mem_reverse.mp (by rw [htyr]; exact List.Mem.head _)
      have hrevB : (wcnf (reg 1) (toList (dict b))).1.reverse
          = cb :: (tyr ++ [y] ++ R.reverse) := by
        rw [e2, List.reverse_append, List.reverse_cons, htyr]
        rfl
      have hacB : lastAC151 (dict b) = some cb := by unfold lastAC151; rw [hrevB]
      obtain ⟨Xb, hlsB⟩ : ∃ X, lastStep129 (dict b) = some (cb.1, X) := by
        cases hpv : prevV151 (dict b) with
        | none => exact ⟨_, lastStep_prev_none151 hacB hpv⟩
        | some v => exact ⟨_, lastStep_prev_some151 hacB hpv⟩
      -- equal last exponents name cb's exponent
      have hexpEq : x.1 = cb.1 := by
        have he : sameExp145 a b = ((x.1 : Term) == cb.1) := by
          unfold sameExp145; rw [hlsA, hlsB]
        rw [he] at hse
        exact eq_of_beq hse
      -- strict descent inside b's pair list refutes it
      have hdP : descP118 ((wcnf (reg 1) (toList (dict b))).1) :=
        wcnf_descP154 _ hcLb hdLb hmLb
      rw [e2] at hdP
      have hdP2 : descP118 (y :: ty) := descP_suffix154 _ _ hdP
      have hIn : ∀ w ∈ y :: ty, inT w.1 = true := by
        intro w hw
        refine (hOKb w ?_).1
        rw [e2]
        exact List.mem_append_right _ hw
      have hlast : lt cb.1 y.1 = true := descP_bound154 ty y hIn hdP2 cb hcbmem
      rw [← hexpEq, ← hE, lt_irrefl] at hlast
      exact Bool.noConfusion hlast

#print axioms domShape154

end

/-!
# §155 THE FIRST GATE: MULTI-DIGIT PLUMBING BEYOND §152's famB

§152 closed the famB family (single digit, coefficient 1, singleton K) at every
height.  This file widens the proved class in the three directions §152 named:

  §155.1  Two towers over ARBITRARY seeds compared: at equal height the bottoms
          decide (`lt_UW_UW_same155`, an equality), across heights the higher
          tower wins in both directions (`lt_UW_UW_lt155`, `lt_UW_UW_false155`).

  §155.2  `collapse 0` of the general tower is `ψ_{Ω₁}` of it (`collapse0_UW155`)
          — §139's `collapse0_TW139` for every seed `s < Ω₁`.

  §155.3  The NESTED family `famC155 m k j = ψ₁^m(ψ₀(ψ₁^k(ψ₀(ψ₁^j 0))))`, whose
          seed's `K_{Ω₁}` has TWO elements.  Closed forms, the gate's step on the
          wedge `k ≤ m ∧ j ≤ m` (`ksetStepOK_famC155`), both refutation sides
          (`not_ksetStepOK_famC_k155` / `_j155`), the exact step boundary
          (`stepOK_iff_famC155`), the standardness contrapositives, and the
          per-term gate `famC_no_refute155` + `firstFire_famC155`.
          NOTE: the step boundary (`k ≤ m ∧ j ≤ m`) is strictly WIDER than the
          standardness boundary (`j ≤ k ≤ m`, measured §155.6) — the two lines
          coincide on famB but NOT on famC; standardness stays inside the gate.

  §155.4  The COEFFICIENT family `famE155 j = ψ₁(ψ₁²0 ⊕ ψ₀(ψ₁^j 0))`: its dict
          image fires with digit `(Ω₁, C)` where `C = ψ_{Ω₁}(…) ≠ 1` and
          `A ⊖ Ω₁ = 0`, so the emitted index sits BELOW `Ω₁` while the escaping
          element sits above — the step genuinely has no arithmetic way out
          (`not_ksetStepOK_famE155`, all j ≥ 4).  Standardness breaks in exact
          sync (`not_std_famE155`), and the standard member j = 3 satisfies the
          step (`stepOK_famE3_155`): `famE_no_refute155`.

  §155.5  MULTI-DIGIT `wcnf`: sums of famB terms.  The self-sum merges into ONE
          digit with coefficient 2 (`ksetStepOK_famBsum2_155`), the cross sum
          keeps TWO firing digits and the second step's obligations discharge
          against the accumulated index (`ksetStepOK_famB_sum155`).

  §155.6  Measurement (frozen): closed forms re-checked by the kernel, the famC
          and famE boundaries frozen on ranges, the H1 residual counted on the
          frozen pools, and pool membership of the new families.
-/

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §155.1 Two towers over arbitrary seeds -/

/-- **同じ高さの塔の比較は底の比較 (等式)。**  §152.6 は片側の不等式だけだった。 -/
theorem lt_UW_UW_same155 (s t : Term) : ∀ j : Nat,
    lt (UW152 s j) (UW152 t j) = lt s t
  | 0 => by
      show lt (phi zero (add (Z zero) s)) (phi zero (add (Z zero) t)) = _
      rw [lt_phi_same139, lt_add_same139]
  | j + 1 => by
      show lt (phi zero (UW152 s j)) (phi zero (UW152 t j)) = _
      rw [lt_phi_same139]
      exact lt_UW_UW_same155 s t j

/-- **低い塔は高い塔より下 — 種がどちらも任意でも。** -/
theorem lt_UW_UW_lt155 (s t : Term) : ∀ a b : Nat, a < b →
    lt (UW152 s a) (UW152 t b) = true
  | 0, 0, h => absurd h (by omega)
  | 0, b + 1, _ => by
      show lt (phi zero (add (Z zero) s)) (phi zero (UW152 t b)) = true
      rw [lt_phi_same139, lt_add_nsum (ne_zero_UW152 t b) (nsum_UW152 t b)]
      exact lt_Om_UW152 t b
  | a + 1, 0, h => absurd h (by omega)
  | a + 1, b + 1, h => by
      show lt (phi zero (UW152 s a)) (phi zero (UW152 t b)) = true
      rw [lt_phi_same139]
      exact lt_UW_UW_lt155 s t a b (by omega)

/-- `Ω₁` より下の種の塔は底 `Ω₁ ⊕ t` より下に居ない。 -/
theorem lt_UW_addOm155 {s : Term} (hlt : lt s (reg 1) = true) (t : Term) (a : Nat) :
    lt (UW152 s a) (add (Z zero) t) = false := by
  rw [lt_nsum_add100 (ne_zero_UW152 s a) (nsum_UW152 s a)]
  exact le_UW_reg1_152 hlt a

/-- **発散の側 — 高い塔は低い塔より下に居ない、種がどちらも任意でも。**
    左の種だけ `Ω₁` より下であればよい。 -/
theorem lt_UW_UW_false155 {s : Term} (hlt : lt s (reg 1) = true) (t : Term) :
    ∀ b a : Nat, b < a → lt (UW152 s a) (UW152 t b) = false
  | 0, 0, h => absurd h (by omega)
  | 0, a + 1, _ => by
      show lt (phi zero (UW152 s a)) (phi zero (add (Z zero) t)) = false
      rw [lt_phi_same139]
      exact lt_UW_addOm155 hlt t a
  | b + 1, 0, h => absurd h (by omega)
  | b + 1, a + 1, h => by
      show lt (phi zero (UW152 s a)) (phi zero (UW152 t b)) = false
      rw [lt_phi_same139]
      exact lt_UW_UW_false155 hlt t b a (by omega)

/-- 高さの違う塔は項として等しくない。 -/
theorem UW_ne155 (s t : Term) : ∀ a b : Nat, a < b → UW152 s a ≠ UW152 t b
  | 0, 0, h => absurd h (by omega)
  | _ + 1, 0, h => absurd h (by omega)
  | 0, b + 1, _ => by
      intro hc
      have hc2 : phi zero (add (Z zero) s) = phi zero (UW152 t b) := hc
      injection hc2 with _ h2
      cases b with
      | zero => exact Term.noConfusion h2
      | succ b' => exact Term.noConfusion h2
  | a + 1, b + 1, h => by
      intro hc
      have hc2 : phi zero (UW152 s a) = phi zero (UW152 t b) := hc
      injection hc2 with _ h2
      exact UW_ne155 s t a b (by omega) h2

theorem beq_UW_ne155 (s t : Term) {a b : Nat} (h : a < b) :
    ((UW152 s a : Term) == UW152 t b) = false :=
  beq_eq_false_iff_ne.mpr (UW_ne155 s t a b h)

end

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §155.2 `collapse 0` of the general tower, and the nested family's closed forms -/

/-- **一般の塔の頭。**  `collapse 0 (UW152 s (j+2)) = ψ_{Ω₁}(UW152 s (j+2))` —
    §139.6 の `collapse0_TW139` を任意の種 `s < Ω₁` へ。 -/
theorem collapse0_UW155 {s : Term} (hlt : lt s (reg 1) = true) :
    ∀ j : Nat, collapse 0 (UW152 s (j + 2)) = psi (Z zero) (UW152 s (j + 2))
  | 0 =>
      collapse0_tower139 (X := add (Z zero) s)
        (beq_UW_one152 s 0) (beq_UW_one152 s 1) (beq_UW_one152 s 2)
        (le_UW_reg1_152 hlt 0) (lt_UW_reg1_152 hlt 1) (le_reg1_UW152 s 1)
        (lt_UW_reg1_152 hlt 2)
  | j + 1 =>
      collapse0_tower139 (X := UW152 s j)
        (beq_UW_one152 s (j + 1)) (beq_UW_one152 s (j + 2)) (beq_UW_one152 s (j + 3))
        (le_UW_reg1_152 hlt (j + 1)) (lt_UW_reg1_152 hlt (j + 2))
        (le_reg1_UW152 s (j + 2)) (lt_UW_reg1_152 hlt (j + 3))

/-- 入れ子の族。`famC155 m k j = ψ₁^m(ψ₀(ψ₁^k(ψ₀(ψ₁^j 0))))`。 -/
def famC155 (m k j : Nat) : BT := nst132 m (BT.D 0 (famB132 k j))

/-- 入れ子の種の閉じた形 — `ψ_{Ω₁}(UW152 (sd152 j) (k-1))`。 -/
def sdC155 (kk jj : Nat) : Term := psi (Z zero) (UW152 (sd152 (jj + 3)) (kk + 2))

/-- 入れ子の種は `Ω₁` より下。 -/
theorem lt_sdC_reg1_155 (kk jj : Nat) : lt (sdC155 kk jj) (reg 1) = true :=
  lt_psiOm_reg1_139 _

/-- `Ω₁` は入れ子の種より下に居ない。 -/
theorem lt_Om_sdC_155 (kk jj : Nat) : lt (Z zero) (sdC155 kk jj) = false :=
  lt_Om_psi141 _

/-- **入れ子の種の値。**  `dict (ψ₀(famB (k+3) (j+3))) = ψ_{Ω₁}(内の塔)`。 -/
theorem sdC_eq155 (kk jj : Nat) :
    dict (BT.D 0 (famB132 (kk + 3) (jj + 3))) = sdC155 kk jj := by
  obtain ⟨_, _, hlt, _, _⟩ := sd_facts152 jj
  rw [Trans.Dict.dict_D, dict_famB152 jj (kk + 2)]
  exact collapse0_UW155 hlt kk

/-- **閉じた形 — 入れ子の族の像も塔。**  §152.4 の `dict_famB152` の一段深い形。 -/
theorem dict_famC155 (kk jj : Nat) : ∀ m : Nat,
    dict (famC155 (m + 1) (kk + 3) (jj + 3)) = UW152 (sdC155 kk jj) m
  | 0 => by
      show collapse 1 (dict (BT.D 0 (famB132 (kk + 3) (jj + 3)))) = _
      rw [sdC_eq155 kk jj]
      exact collapse1_seed152 rfl rfl (lt_psiOm_reg1_139 _) (lt_psiOm_Om2_139 _)
  | m + 1 => by
      show collapse 1 (dict (famC155 (m + 1) (kk + 3) (jj + 3))) = _
      rw [dict_famC155 kk jj m]
      exact collapse1_UW152 (lt_psiOm_reg1_139 _) m

/-- **入れ子の種の `K_{Ω₁}` は二元 — 内の塔と、その種の逃げる元。** -/
theorem Kset_sdC155 (kk jj : Nat) :
    Kset (reg 1) (sdC155 kk jj)
      = UW152 (sd152 (jj + 3)) (kk + 2) :: Kset (reg 1) (sd152 (jj + 3)) := by
  show Kset (reg 1) (psi (Z zero) (UW152 (sd152 (jj + 3)) (kk + 2))) = _
  rw [Kset_psi_reg152, Kset_UW152]

/-- 種同士の比較 — 内の入れ子が正しい向き (`j ≤ k`) なら内の種は外の種より下。 -/
theorem lt_sd_sdC155 (kk jj : Nat) (h : jj ≤ kk) :
    lt (sd152 (jj + 3)) (sdC155 kk jj) = true := by
  cases jj with
  | zero =>
      show lt (sd152 3) (psi (Z zero) (UW152 (sd152 3) (kk + 2))) = true
      rw [sd3_152, lt_psi_same]
      exact lt_zero_left (ne_zero_UW152 _ _)
  | succ jp =>
      show lt (sd152 (jp + 4)) (psi (Z zero) (UW152 (sd152 (jp + 4)) (kk + 2))) = true
      rw [sd_psi152 jp, lt_psi_same]
      exact lt_TW_UW152 _ (jp + 3) (kk + 2) (by omega)

/-! ### §155.3 The gate on the nested family, both sides -/

/-- **第一の門の一歩は `k ≤ m ∧ j ≤ m` の全域で成り立つ。**  逃げる元は二つ —
    内の塔 `UW152 s₁ (k-1)` は高さ比較 (`k < m`) か種の比較 (`k = m`、そこで
    `j ≤ k` が要るが `j ≤ m = k` から出る) で、内の種の元 `TW (j-1)` は
    高さ比較 (`j ≤ m`) で、どちらも指数 `UW152 sdC (m-1)` より下。 -/
theorem ksetStepOK_famC155 {m k j : Nat} (h3k : 3 ≤ k) (h3j : 3 ≤ j)
    (hkm : k ≤ m) (hjm : j ≤ m) : KsetStepOK 0 (dict (famC155 m k j)) := by
  obtain ⟨kk, rfl⟩ : ∃ kk, k = kk + 3 := ⟨k - 3, by omega⟩
  obtain ⟨jj, rfl⟩ : ∃ jj, j = jj + 3 := ⟨j - 3, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, m = (kk + d) + 3 := ⟨m - (kk + 3), by omega⟩
  rw [show kk + d + 3 = (kk + d + 2) + 1 from rfl, dict_famC155 kk jj (kk + d + 2)]
  refine stepOK_UW152 (lt_sdC_reg1_155 kk jj) (kk + d) ?_
  intro y hy
  rw [Kset_sdC155 kk jj] at hy
  rcases List.mem_cons.mp hy with h1 | h1
  · subst h1
    cases d with
    | zero =>
        show lt (UW152 (sd152 (jj + 3)) (kk + 2)) (UW152 (sdC155 kk jj) (kk + 2)) = true
        rw [lt_UW_UW_same155 (sd152 (jj + 3)) (sdC155 kk jj) (kk + 2)]
        exact lt_sd_sdC155 kk jj (by omega)
    | succ d' =>
        exact lt_UW_UW_lt155 _ _ _ _ (by omega)
  · cases jj with
    | zero =>
        rw [Kset_sd3_152] at h1
        rw [List.mem_singleton.mp h1]
        exact lt_zero_left (ne_zero_UW152 _ _)
    | succ jp =>
        rw [show jp + 1 + 3 = jp + 4 from rfl, Kset_sd_psi152 jp] at h1
        rw [List.mem_singleton.mp h1]
        exact lt_TW_UW152 _ (jp + 3) (kk + d + 2) (by omega)

/-- **発散の側 1 — `m < k` では一歩は成り立たない。**  内の塔が指数より高い。 -/
theorem not_ksetStepOK_famC_k155 {m k j : Nat} (h3m : 3 ≤ m) (h3j : 3 ≤ j) (hmk : m < k) :
    ¬ KsetStepOK 0 (dict (famC155 m k j)) := by
  obtain ⟨jj, rfl⟩ : ∃ jj, j = jj + 3 := ⟨j - 3, by omega⟩
  obtain ⟨mm, rfl⟩ : ∃ mm, m = mm + 3 := ⟨m - 3, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, k = (mm + e + 1) + 3 := ⟨k - (mm + 4), by omega⟩
  intro H
  rw [show mm + 3 = (mm + 2) + 1 from rfl, dict_famC155 (mm + e + 1) jj (mm + 2)] at H
  have hp : (((none : Option Term), (none : Option Term)),
      (UW152 (sdC155 (mm + e + 1) jj) (mm + 1), TM.Term.one))
      ∈ scanSt (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (wcnf (reg 1) [UW152 (sdC155 (mm + e + 1) jj) (mm + 2)]).1 := by
    rw [wcnf_UW152 (lt_sdC_reg1_155 (mm + e + 1) jj) mm]
    exact List.Mem.head _
  have hstep := (H _ hp (le_reg1_UW152 _ (mm + 1))).2
    (UW152 (sd152 (jj + 3)) (mm + e + 3)) (Or.inl (by
      show UW152 (sd152 (jj + 3)) (mm + e + 3)
        ∈ Kset (reg 1) (UW152 (sdC155 (mm + e + 1) jj) (mm + 1))
      rw [Kset_UW152, Kset_sdC155 (mm + e + 1) jj]
      exact List.Mem.head _))
  rw [show idxOf (reg (0 + 1)) (((none : Option Term), (none : Option Term)))
        (UW152 (sdC155 (mm + e + 1) jj) (mm + 1), TM.Term.one)
      = UW152 (sdC155 (mm + e + 1) jj) (mm + 2)
      from idx_UW152 (lt_sdC_reg1_155 (mm + e + 1) jj) mm,
    lt_UW_UW_false155 (sd_facts152 jj).2.2.1 _ (mm + 2) (mm + e + 3) (by omega)] at hstep
  exact Bool.noConfusion hstep

/-- **発散の側 2 — `m < j` でも一歩は成り立たない。**  内の種の元 `TW (j-1)` が
    指数より高い。`k` と `m` の関係には依らない。 -/
theorem not_ksetStepOK_famC_j155 {m k j : Nat} (h3m : 3 ≤ m) (h3k : 3 ≤ k) (hmj : m < j) :
    ¬ KsetStepOK 0 (dict (famC155 m k j)) := by
  obtain ⟨kk, rfl⟩ : ∃ kk, k = kk + 3 := ⟨k - 3, by omega⟩
  obtain ⟨mm, rfl⟩ : ∃ mm, m = mm + 3 := ⟨m - 3, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, j = (mm + e + 1) + 3 := ⟨j - (mm + 4), by omega⟩
  intro H
  rw [show mm + 3 = (mm + 2) + 1 from rfl, dict_famC155 kk (mm + e + 1) (mm + 2)] at H
  have hp : (((none : Option Term), (none : Option Term)),
      (UW152 (sdC155 kk (mm + e + 1)) (mm + 1), TM.Term.one))
      ∈ scanSt (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (wcnf (reg 1) [UW152 (sdC155 kk (mm + e + 1)) (mm + 2)]).1 := by
    rw [wcnf_UW152 (lt_sdC_reg1_155 kk (mm + e + 1)) mm]
    exact List.Mem.head _
  have hstep := (H _ hp (le_reg1_UW152 _ (mm + 1))).2
    (TW (mm + e + 3)) (Or.inl (by
      show TW (mm + e + 3) ∈ Kset (reg 1) (UW152 (sdC155 kk (mm + e + 1)) (mm + 1))
      rw [Kset_UW152, Kset_sdC155 kk (mm + e + 1),
        show mm + e + 1 + 3 = mm + e + 4 from rfl, Kset_sd_psi152 (mm + e)]
      exact List.Mem.tail _ (List.Mem.head _)))
  rw [show idxOf (reg (0 + 1)) (((none : Option Term), (none : Option Term)))
        (UW152 (sdC155 kk (mm + e + 1)) (mm + 1), TM.Term.one)
      = UW152 (sdC155 kk (mm + e + 1)) (mm + 2)
      from idx_UW152 (lt_sdC_reg1_155 kk (mm + e + 1)) mm,
    lt_TW_UW_false152 (lt_Om_sdC_155 kk (mm + e + 1)) (mm + 2) (mm + e + 3)
      (by omega)] at hstep
  exact Bool.noConfusion hstep

/-- **入れ子の族の一歩の正確な境界 — `k ≤ m ∧ j ≤ m`。**  §152.7 の famB の境界
    (`k ≤ m`) の一段深い形。標準性の境界 (`j ≤ k ≤ m`、§155.6 で凍結) より真に広い。 -/
theorem stepOK_iff_famC155 {m k j : Nat} (h3m : 3 ≤ m) (h3k : 3 ≤ k) (h3j : 3 ≤ j) :
    KsetStepOK 0 (dict (famC155 m k j)) ↔ (k ≤ m ∧ j ≤ m) := by
  constructor
  · intro H
    constructor
    · rcases Nat.lt_or_ge m k with h | h
      · exact absurd H (not_ksetStepOK_famC_k155 h3m h3j h)
      · omega
    · rcases Nat.lt_or_ge m j with h | h
      · exact absurd H (not_ksetStepOK_famC_j155 h3m h3k h)
      · omega
  · intro h
    exact ksetStepOK_famC155 h3k h3j h.1 h.2

end

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §155.3b Standardness pins the nested family inside the gate -/

/-- 一般化した比較の否定 — `ψ₁` の塔 (底は任意) は、それより低い
    `ψ₁^i(ψ₀ w)` 形の項より下に居ない。§152.9 の `ltL_bT_famB_false152` の一般形。 -/
theorem ltL_nst_nstD0_false155 (x w : BT) : ∀ (f : Nat), ∀ (jn i : Nat), i ≤ jn →
    BT.ltL f (BT.toL (nst132 (jn + 1) x)) (BT.toL (nst132 i (BT.D 0 w))) = false
  | 0, _, _, _ => rfl
  | f + 1, jn, 0, _ => by
      show (if (1 : Nat) < 0 then true else if (0 : Nat) < 1 then false
            else if nst132 jn x == w then BT.ltL f [] []
            else BT.ltL f (BT.toL (nst132 jn x)) (BT.toL w)) = false
      rw [if_neg (by omega), if_pos (by omega)]
  | f + 1, jn, i + 1, h => by
      obtain ⟨jq, rfl⟩ : ∃ jq, jn = jq + 1 := ⟨jn - 1, by omega⟩
      show (if (1 : Nat) < 1 then true else if (1 : Nat) < 1 then false
            else if nst132 (jq + 1) x == nst132 i (BT.D 0 w) then BT.ltL f [] []
            else BT.ltL f (BT.toL (nst132 (jq + 1) x))
              (BT.toL (nst132 i (BT.D 0 w)))) = false
      rw [if_neg (by omega), if_neg (by omega)]
      cases hbeq : (nst132 (jq + 1) x == nst132 i (BT.D 0 w)) with
      | true =>
          rw [if_pos rfl]
          cases f with
          | zero => rfl
          | succ f => rfl
      | false =>
          rw [if_neg (fun hc => Bool.noConfusion hc)]
          exact ltL_nst_nstD0_false155 x w f jq i (by omega)

/-- `m < j` では内の裸の塔は族の項より下に居ない。 -/
theorem bT_not_lt_famC155 {m j : Nat} (k : Nat) (h : m < j) :
    BT.lt (nst132 j BT.zero) (famC155 m k j) = false := by
  obtain ⟨jj, rfl⟩ : ∃ jj, j = jj + 1 := ⟨j - 1, by omega⟩
  exact ltL_nst_nstD0_false155 BT.zero (famB132 k (jj + 1)) _ jj m (by omega)

/-- `m < k` では中の famB は族の項より下に居ない。 -/
theorem famB_not_lt_famC155 {m k : Nat} (j : Nat) (hk : 1 ≤ k) (h : m < k) :
    BT.lt (famB132 k j) (famC155 m k j) = false := by
  obtain ⟨kk, rfl⟩ : ∃ kk, k = kk + 1 := ⟨k - 1, by omega⟩
  exact ltL_nst_nstD0_false155 (BT.D 0 (nst132 j BT.zero)) (famB132 (kk + 1) j)
    _ kk m (by omega)

theorem famB_mem_GB_famC155 (k j : Nat) : ∀ m : Nat,
    famB132 k j ∈ BT.GB 0 (famC155 m k j)
  | 0 => by
      show famB132 k j
        ∈ (if 0 ≤ 0 then famB132 k j :: BT.GB 0 (famB132 k j) else [])
      rw [if_pos (by omega)]
      exact List.Mem.head _
  | m + 1 => by
      show famB132 k j
        ∈ (if 0 ≤ 1 then famC155 m k j :: BT.GB 0 (famC155 m k j) else [])
      rw [if_pos (by omega)]
      exact List.Mem.tail _ (famB_mem_GB_famC155 k j m)

theorem bT_mem_GB_famC155 (k j : Nat) : ∀ m : Nat,
    nst132 j BT.zero ∈ BT.GB 0 (famC155 m k j)
  | 0 => by
      show nst132 j BT.zero
        ∈ (if 0 ≤ 0 then famB132 k j :: BT.GB 0 (famB132 k j) else [])
      rw [if_pos (by omega)]
      exact List.Mem.tail _ (bT_mem_GB152 j k)
  | m + 1 => by
      show nst132 j BT.zero
        ∈ (if 0 ≤ 1 then famC155 m k j :: BT.GB 0 (famC155 m k j) else [])
      rw [if_pos (by omega)]
      exact List.Mem.tail _ (bT_mem_GB_famC155 k j m)

/-- **`m < k` の入れ子は `K` 標準でない。** -/
theorem not_std_famC_k155 {m k j : Nat} (hk : 1 ≤ k) (hmk : m < k) :
    BT.isStd (BT.D 0 (famC155 m k j)) = false := by
  cases hs : BT.isStd (BT.D 0 (famC155 m k j)) with
  | false => rfl
  | true =>
      exfalso
      have h0 : (BT.isStd (famC155 m k j)
          && (BT.GB 0 (famC155 m k j)).all (fun e => BT.lt e (famC155 m k j))) = true := hs
      have h2 := List.all_eq_true.mp ((Bool.and_eq_true _ _).mp h0).2 _
        (famB_mem_GB_famC155 k j m)
      rw [famB_not_lt_famC155 j hk hmk] at h2
      exact Bool.noConfusion h2

/-- **`m < j` の入れ子も `K` 標準でない。** -/
theorem not_std_famC_j155 {m k j : Nat} (hmj : m < j) :
    BT.isStd (BT.D 0 (famC155 m k j)) = false := by
  cases hs : BT.isStd (BT.D 0 (famC155 m k j)) with
  | false => rfl
  | true =>
      exfalso
      have h0 : (BT.isStd (famC155 m k j)
          && (BT.GB 0 (famC155 m k j)).all (fun e => BT.lt e (famC155 m k j))) = true := hs
      have h2 := List.all_eq_true.mp ((Bool.and_eq_true _ _).mp h0).2 _
        (bT_mem_GB_famC155 k j m)
      rw [bT_not_lt_famC155 k hmj] at h2
      exact Bool.noConfusion h2

/-- **主定理 — 入れ子の族は第一の門をどの高さ・どの深さでも反証できない。**
    `K` 標準なら `k ≤ m` と `j ≤ m` が出て、門の一歩は定理になる。 -/
theorem famC_no_refute155 {m k j : Nat} (h3k : 3 ≤ k) (h3j : 3 ≤ j)
    (hs : BT.isStd (BT.D 0 (famC155 m k j)) = true) :
    KsetStepOK 0 (dict (famC155 m k j)) := by
  have hkm : k ≤ m := by
    rcases Nat.lt_or_ge m k with h | h
    · rw [not_std_famC_k155 (by omega) h] at hs
      exact Bool.noConfusion hs
    · omega
  have hjm : j ≤ m := by
    rcases Nat.lt_or_ge m j with h | h
    · rw [not_std_famC_j155 h] at hs
      exact Bool.noConfusion hs
    · omega
  exact ksetStepOK_famC155 h3k h3j hkm hjm

/-- 一項ぶんの門、§87 の帰納法が消費する形。 -/
theorem gateStd87_famC155 (m k j : Nat) (h3k : 3 ≤ k) (h3j : 3 ≤ j) :
    GateStd87 (famC155 m k j) :=
  fun _ hs => famC_no_refute155 h3k h3j hs

/-- **§145.4 の H1 の義務、入れ子の族の上で。** -/
theorem firstFire_famC155 (m k j : Nat) (h3k : 3 ≤ k) (h3j : 3 ≤ j)
    (hs : BT.isStd (BT.D 0 (famC155 m k j)) = true) : FirstFire145 (famC155 m k j) :=
  fun p hp _ hle y hy => (famC_no_refute155 h3k h3j hs p hp hle).2 y hy

/-- 標準性は再帰的 — 入れ子の内側の `ψ₀` の標準性が取り出せる。 -/
theorem isStd_inner_famC155 {k j : Nat} : ∀ m : Nat,
    BT.isStd (famC155 m k j) = true → BT.isStd (BT.D 0 (famB132 k j)) = true
  | 0, h => h
  | m + 1, h => isStd_inner_famC155 m (isStd_of_D h)

/-- **2.1(vi) の条項そのもの、入れ子の族の標準側の全域で。** -/
theorem psiIdxOK_famC155 {m k j : Nat} (h3k : 3 ≤ k) (h3j : 3 ≤ j)
    (hs : BT.isStd (BT.D 0 (famC155 m k j)) = true) :
    PsiIdxOK 0 (dict (famC155 m k j)) := by
  have hsi : BT.isStd (BT.D 0 (famB132 k j)) = true :=
    isStd_inner_famC155 m (isStd_of_D hs)
  have hb : btLe72 1 (BT.D 0 (famB132 k j)) = true := by
    show (decide (0 ≤ 1) && btLe72 1 (famB132 k j)) = true
    rw [btLe_famB152 k j]
    rfl
  have h0 : inT (dict (BT.D 0 (famB132 k j))) = true
      ∧ lt (dict (BT.D 0 (famB132 k j))) M = true := by
    rw [Trans.Dict.dict_D]
    exact inT_collapse_gap3 0 (dict (famB132 k j)) (inT_dict_famB152 k j).1
      (inT_dict_famB152 k j).2
      (psiIdxOK_of_stepOK 0 _ (inT_dict_famB152 k j).1 (inT_dict_famB152 k j).2
        (famB_no_refute152 k j hsi))
  have hin := nst_inT152 hb h0 m
  exact psiIdxOK_of_stepOK 0 _ hin.1 hin.2 (famC_no_refute155 h3k h3j hs)

end

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §155.4 The coefficient family: digit `(Ω₁, ψ_{Ω₁}(…))`, `A ⊖ Ω₁ = 0`

`famE155 j = ψ₁(ψ₁²0 ⊕ ψ₀(ψ₁^j 0))`.  Its dict image is `ω^(TW 1 ⊕ s)` with
`s = sd152 j < Ω₁`: the single wcnf digit is `(Ω₁, s)` — coefficient ≠ 1 and
`subAP Ω₁ A = 0`, the corner every §136 exemption leaves.  The emitted index is
`s` itself, BELOW `Ω₁`, while for `j ≥ 4` the escaping element `TW (j-1)` sits
above `Ω₁` — the step genuinely has no way out, and standardness breaks in sync. -/

/-- 係数の族。`famE155 j = ψ₁(ψ₁²0 ⊕ ψ₀(ψ₁^j 0))` — **§130 が名指しした
    `famA132` そのもの** (`famE_eq_famA155`)。§132.5 はこの族の境界を `k < 9` の
    測定で凍結した。ここでは全ての高さで証明する。 -/
def famE155 (j : Nat) : BT :=
  BT.D 1 (BT.sum (nst132 2 BT.zero) (BT.D 0 (nst132 j BT.zero)))

/-- §130 の `famA132` との同一視 — 定義そのまま。 -/
theorem famE_eq_famA155 (j : Nat) : famE155 j = famA132 j := rfl

/-- 種は `ψ_{Ω₁}` の形。 -/
theorem sd_psi_form155 : ∀ jj : Nat, ∃ X : Term, sd152 (jj + 3) = psi (Z zero) X
  | 0 => ⟨zero, sd3_152⟩
  | jp + 1 => ⟨TW (jp + 3), by
      rw [show jp + 1 + 3 = jp + 4 from rfl]
      exact sd_psi152 jp⟩

/-- `ψ_{Ω₁}(X)` は `TW` の塔のどの段 (`a ≥ 1`) よりも下。 -/
theorem lt_psiOm_TW155 (X : Term) : ∀ a : Nat, lt (psi (Z zero) X) (TW (a + 1)) = true
  | 0 => by
      show lt (psi (Z zero) X) (phi zero (TW 0)) = true
      rw [lt_psi_phi_eq102,
        show lt (psi (Z zero) X) (TW 0) = true from by
          show lt (psi (Z zero) X) (add (Z zero) (Z zero)) = true
          rw [lt_nsum_add100 (show (psi (Z zero) X : Term) ≠ zero from by
                intro hc; exact Term.noConfusion hc) rfl]
          show ((psi (Z zero) X == Z zero) || lt (psi (Z zero) X) (Z zero)) = true
          rw [show lt (psi (Z zero) X) (Z zero) = true from lt_psiOm_reg1_139 X]
          exact Bool.or_true _,
        Bool.or_true]
  | a + 1 => by
      show lt (psi (Z zero) X) (phi zero (TW (a + 1))) = true
      rw [lt_psi_phi_eq102, lt_psiOm_TW155 X a, Bool.or_true]

/-- 逆向き — 塔は `ψ_{Ω₁}(X)` より下に居ない。 -/
theorem lt_TW_psi155 (X : Term) : ∀ a : Nat, lt (TW a) (psi (Z zero) X) = false
  | 0 => by
      show lt (add (Z zero) (Z zero)) (psi (Z zero) X) = false
      rw [lt_add_psi102]
      exact lt_Om_psi141 X
  | a + 1 => by
      show lt (phi zero (TW a)) (psi (Z zero) X) = false
      rw [lt_phi_psi103, lt_TW_psi155 X a]
      exact Bool.and_false _

theorem splitFin_add_psi155 (p X : Term) :
    splitFin (add p (psi (Z zero) X)) = (add p (psi (Z zero) X), 0) := by
  show (ofList ((p :: toList (psi (Z zero) X)).take
          ((p :: toList (psi (Z zero) X)).length
            - ((p :: toList (psi (Z zero) X)).reverse.takeWhile (· == TM.Term.one)).length)),
        ((p :: toList (psi (Z zero) X)).reverse.takeWhile (· == TM.Term.one)).length) = _
  rw [show toList (psi (Z zero) X) = [psi (Z zero) X] from rfl,
    show ([p, psi (Z zero) X].reverse : List Term) = [psi (Z zero) X, p] from rfl,
    show List.takeWhile (· == TM.Term.one) [psi (Z zero) X, p] = [] from by
      rw [List.takeWhile_cons,
        show ((psi (Z zero) X : Term) == TM.Term.one) = false from rfl]
      rfl]
  rfl

theorem phiShifted_add_psi155 (p X : Term) :
    phiShifted zero (add p (psi (Z zero) X)) = false := by
  show (isFP zero (splitFin (add p (psi (Z zero) X))).1
        || (((add p (psi (Z zero) X) : Term) == zero) && (zero : Term).isSC)) = false
  rw [splitFin_add_psi155 p X, isFP_add152]
  rfl

theorem le_psiOm_TW1_155 (X : Term) : le (psi (Z zero) X) (TW 1) = true := by
  show ((psi (Z zero) X == TW 1) || lt (psi (Z zero) X) (TW 1)) = true
  rw [lt_psiOm_TW155 X 0]
  exact Bool.or_true _

theorem plus_TW1_psi155 (X : Term) :
    plus (TW 1) (psi (Z zero) X) = add (TW 1) (psi (Z zero) X) := by
  rw [plus_cons66 (show toList (psi (Z zero) X) = [psi (Z zero) X] from rfl),
    show toList (TW 1) = [TW 1] from rfl,
    List.filter_cons_of_pos (by exact le_psiOm_TW1_155 X)]
  rfl

/-- **底の値 — `ψ₁(TW 1 ⊕ ψ_{Ω₁}X) = ω^(TW 1 ⊕ ψ_{Ω₁}X)`。** -/
theorem collapse1_TW1_psi155 (X : Term) :
    collapse 1 (add (TW 1) (psi (Z zero) X))
      = phi zero (add (TW 1) (psi (Z zero) X)) := by
  show omegaNF (plus (reg 1) (plus
    (((wcnf (reg 2) (toList (add (TW 1) (psi (Z zero) X)))).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 2) (baseOf 1))).2.getD zero)
    ((wcnf (reg 2) (toList (add (TW 1) (psi (Z zero) X)))).2))) = _
  rw [show toList (add (TW 1) (psi (Z zero) X)) = [TW 1, psi (Z zero) X] from rfl,
    wcnf_cons_lt (lt_TW_reg2_139 1)]
  show omegaNF (plus (reg 1) (plus zero (ofList [TW 1, psi (Z zero) X]))) = _
  rw [show (ofList [TW 1, psi (Z zero) X] : Term) = add (TW 1) (psi (Z zero) X) from rfl,
    show plus zero (add (TW 1) (psi (Z zero) X)) = add (TW 1) (psi (Z zero) X) from rfl,
    show plus (reg 1) (add (TW 1) (psi (Z zero) X)) = add (TW 1) (psi (Z zero) X) from by
      show ofList (List.filter (fun a => le (TW 1) a) [Z zero]
        ++ [TW 1, psi (Z zero) X]) = _
      rw [show List.filter (fun a => le (TW 1) a) [Z zero] = [] from by
        show (match le (TW 1) (Z zero) with
              | true => Z zero :: List.filter (fun a => le (TW 1) a) []
              | false => List.filter (fun a => le (TW 1) a) []) = []
        rw [show le (TW 1) (Z zero) = false from le_TW_reg1_139 1]
        rfl]
      rfl]
  exact omegaNF_add_psi139 (ltF_M_add139 (fun f => ltF_M_phi135 zero (TW 0) f) rfl X)

/-- **閉じた形 — 係数の族の像。**  `dict (famE155 j) = ω^(TW 1 ⊕ sd152 j)`。 -/
theorem dict_famE155 (jj : Nat) :
    dict (famE155 (jj + 3)) = phi zero (add (TW 1) (sd152 (jj + 3))) := by
  obtain ⟨X, hX⟩ := sd_psi_form155 jj
  show collapse 1 (dict (BT.sum (nst132 2 BT.zero) (BT.D 0 (nst132 (jj + 3) BT.zero)))) = _
  rw [Trans.Dict.dict_sum,
    show dict (nst132 2 BT.zero) = TW 1 from dict_bT152 0,
    show dict (BT.D 0 (nst132 (jj + 3) BT.zero)) = sd152 (jj + 3) from rfl, hX,
    plus_TW1_psi155 X]
  exact collapse1_TW1_psi155 X

theorem lt_E_reg1_155 (X : Term) :
    lt (phi zero (add (TW 1) (psi (Z zero) X))) (reg 1) = false := by
  rw [lt_phi_reg1_100,
    show lt (add (TW 1) (psi (Z zero) X)) (reg 1) = false from by
      rw [lt_add_nsum (show (reg 1 : Term) ≠ zero from by
            intro hc; exact Term.noConfusion hc) rfl]
      exact lt_TW_reg1_139 1]
  exact Bool.and_false _

/-- 発火する桁の指数の側 — `A = Ω₁` そのもの。 -/
theorem wA_famE155 (X : Term) :
    wA (reg 1) (phi zero (add (TW 1) (psi (Z zero) X))) = Z zero := by
  show ofList (List.map (divAP (reg 1)) (List.filter (fun q => !lt q (reg 1))
    (toList (logOm (phi zero (add (TW 1) (psi (Z zero) X))))))) = _
  rw [logOm_phi0_135 (phiShifted_add_psi155 (TW 1) X),
    show toList (add (TW 1) (psi (Z zero) X)) = [TW 1, psi (Z zero) X] from rfl,
    show List.filter (fun q => !lt q (reg 1)) [TW 1, psi (Z zero) X] = [TW 1] from by
      rw [List.filter_cons_of_pos (by
            show (!lt (TW 1) (reg 1)) = true
            rw [lt_TW_reg1_139 1]
            rfl),
        List.filter_cons_of_neg (by
            intro hc
            rw [lt_psiOm_reg1_139 X] at hc
            exact Bool.noConfusion hc)]
      rfl]
  show divAP (reg 1) (TW 1) = _
  show omegaNF (subAP (reg 1) (logOm (TW 1))) = _
  rw [show logOm (TW 1) = TW 0 from logOm_phi0_135 (show phiShifted zero (TW 0) = false from rfl),
    show subAP (reg 1) (TW 0) = Z zero from by
      show (if ((Z zero : Term) == reg 1) = true then ofList [Z zero] else TW 0) = _
      rw [if_pos (by rfl)]
      rfl]
  exact omegaNF_Z139 zero

/-- 発火する桁の係数の側 — `C = ψ_{Ω₁}(X) ≠ 1`。 -/
theorem wC_famE155 (X : Term) :
    wC (reg 1) (phi zero (add (TW 1) (psi (Z zero) X))) = psi (Z zero) X := by
  show omegaNF (ofList (List.filter (fun q => lt q (reg 1))
    (toList (logOm (phi zero (add (TW 1) (psi (Z zero) X))))))) = _
  rw [logOm_phi0_135 (phiShifted_add_psi155 (TW 1) X),
    show toList (add (TW 1) (psi (Z zero) X)) = [TW 1, psi (Z zero) X] from rfl,
    show List.filter (fun q => lt q (reg 1)) [TW 1, psi (Z zero) X]
        = [psi (Z zero) X] from by
      rw [List.filter_cons_of_neg (by
            intro hc
            rw [lt_TW_reg1_139 1] at hc
            exact Bool.noConfusion hc),
        List.filter_cons_of_pos (by exact lt_psiOm_reg1_139 X)]
      rfl]
  show omegaNF (psi (Z zero) X) = _
  exact omegaNF_psi139 (Z zero) X

/-- **係数の族の `wcnf` — 桁は一つ、`(Ω₁, ψ_{Ω₁}X)`。** -/
theorem wcnf_famE155 (X : Term) :
    wcnf (reg 1) [phi zero (add (TW 1) (psi (Z zero) X))]
      = ([((Z zero : Term), psi (Z zero) X)], zero) := by
  rw [wcnf_cons_ge (lt_E_reg1_155 X)]
  show ([(wA (reg 1) (phi zero (add (TW 1) (psi (Z zero) X))),
         wC (reg 1) (phi zero (add (TW 1) (psi (Z zero) X))))], zero) = _
  rw [wA_famE155 X, wC_famE155 X]

/-- **吐かれる指数は係数から来る `ψ_{Ω₁}X` そのもの — `Ω₁` より下。** -/
theorem idx_famE155 (X : Term) :
    idxOf (reg 1) ((none : Option Term), (none : Option Term))
        ((Z zero : Term), psi (Z zero) X)
      = psi (Z zero) X := by
  show sub1 (mulL (mulL (reg 1) (subAP (reg 1) (Z zero))) (psi (Z zero) X)) = _
  rw [show subAP (reg 1) (Z zero) = zero from by
      show (if ((Z zero : Term) == reg 1) = true then ofList [] else Z zero) = _
      rw [if_pos (by rfl)]
      rfl,
    show mulL (reg 1) zero = zero from rfl]
  show sub1 (ofList [omegaNF (plus zero (logOm (psi (Z zero) X)))]) = _
  rw [show logOm (psi (Z zero) X) = psi (Z zero) X from rfl,
    show plus zero (psi (Z zero) X) = psi (Z zero) X from rfl,
    omegaNF_psi139 (Z zero) X]
  show (if ((psi (Z zero) X : Term) == TM.Term.one) = true then ofList []
        else psi (Z zero) X) = _
  rw [if_neg (by intro hc; exact Bool.noConfusion hc)]

/-- **主定理 — `j ≥ 4` の係数の族では門の一歩は成り立たない。**  逃げる元
    `TW (j-1) ≥ Ω₁` に対し指数は `ψ_{Ω₁}(TW (j-1)) < Ω₁`。算術のどの免除も
    届かない形 — `A ⊖ Ω₁ = 0` かつ係数の `K` が空でない。 -/
theorem not_ksetStepOK_famE155 (jj : Nat) :
    ¬ KsetStepOK 0 (dict (famE155 (jj + 4))) := by
  intro H
  have hd : dict (famE155 (jj + 4))
      = phi zero (add (TW 1) (psi (Z zero) (TW (jj + 3)))) := by
    have h := dict_famE155 (jj + 1)
    rw [show jj + 1 + 3 = jj + 4 from rfl, sd_psi152 jj] at h
    exact h
  rw [hd] at H
  have hp : (((none : Option Term), (none : Option Term)),
      ((Z zero : Term), psi (Z zero) (TW (jj + 3))))
      ∈ scanSt (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (wcnf (reg 1)
          (toList (phi zero (add (TW 1) (psi (Z zero) (TW (jj + 3))))))).1 := by
    rw [show toList (phi zero (add (TW 1) (psi (Z zero) (TW (jj + 3)))))
          = [phi zero (add (TW 1) (psi (Z zero) (TW (jj + 3))))] from rfl,
      wcnf_famE155 (TW (jj + 3))]
    exact List.Mem.head _
  have hstep := (H _ hp (by rfl)).2 (TW (jj + 3)) (Or.inr (by
      show TW (jj + 3) ∈ Kset (reg 1) (psi (Z zero) (TW (jj + 3)))
      rw [Kset_psi_reg152, Kset_TW152]
      exact List.Mem.head _))
  rw [show idxOf (reg (0 + 1)) (((none : Option Term), (none : Option Term)))
        ((Z zero : Term), psi (Z zero) (TW (jj + 3))) = psi (Z zero) (TW (jj + 3))
      from idx_famE155 (TW (jj + 3)),
    lt_TW_psi155 (TW (jj + 3)) (jj + 3)] at hstep
  exact Bool.noConfusion hstep

/-! §155.4b Standardness breaks in exact sync on the coefficient family -/

theorem ltL_bT_bT_false155 : ∀ (f a b : Nat), b ≤ a →
    BT.ltL f (BT.toL (nst132 a BT.zero)) (BT.toL (nst132 b BT.zero)) = false
  | 0, _, _, _ => rfl
  | _ + 1, 0, 0, _ => rfl
  | _ + 1, _ + 1, 0, _ => rfl
  | _ + 1, 0, _ + 1, h => absurd h (by omega)
  | f + 1, a + 1, b + 1, h => by
      show (if (1 : Nat) < 1 then true else if (1 : Nat) < 1 then false
            else if nst132 a BT.zero == nst132 b BT.zero then BT.ltL f [] []
            else BT.ltL f (BT.toL (nst132 a BT.zero)) (BT.toL (nst132 b BT.zero))) = false
      rw [if_neg (by omega), if_neg (by omega)]
      cases hbeq : (nst132 a BT.zero == nst132 b BT.zero) with
      | true =>
          rw [if_pos rfl]
          cases f with
          | zero => rfl
          | succ f => rfl
      | false =>
          rw [if_neg (fun hc => Bool.noConfusion hc)]
          exact ltL_bT_bT_false155 f a b (by omega)

theorem ltL_aux_famE155 : ∀ (f jj : Nat),
    BT.ltL f [nst132 (jj + 3) BT.zero]
      [nst132 2 BT.zero, BT.D 0 (nst132 (jj + 4) BT.zero)] = false
  | 0, _ => rfl
  | f + 1, jj => by
      show (if (1 : Nat) < 1 then true else if (1 : Nat) < 1 then false
            else if nst132 (jj + 2) BT.zero == nst132 1 BT.zero
              then BT.ltL f [] [BT.D 0 (nst132 (jj + 4) BT.zero)]
            else BT.ltL f (BT.toL (nst132 (jj + 2) BT.zero))
              (BT.toL (nst132 1 BT.zero))) = false
      rw [if_neg (by omega), if_neg (by omega),
        if_neg (by rw [beq_bT_bT152 (jj + 2) 1 (by omega)]; exact Bool.noConfusion)]
      exact ltL_bT_bT_false155 f (jj + 2) 1 (by omega)

theorem ltL_bT_famE_false155 : ∀ (f jj : Nat),
    BT.ltL f (BT.toL (nst132 (jj + 4) BT.zero)) (BT.toL (famE155 (jj + 4))) = false
  | 0, _ => rfl
  | f + 1, jj => by
      show (if (1 : Nat) < 1 then true else if (1 : Nat) < 1 then false
            else if nst132 (jj + 3) BT.zero
                == BT.sum (nst132 2 BT.zero) (BT.D 0 (nst132 (jj + 4) BT.zero))
              then BT.ltL f [] []
            else BT.ltL f (BT.toL (nst132 (jj + 3) BT.zero))
              (BT.toL (BT.sum (nst132 2 BT.zero)
                (BT.D 0 (nst132 (jj + 4) BT.zero))))) = false
      rw [if_neg (by omega), if_neg (by omega),
        if_neg (fun hc => Bool.noConfusion hc)]
      exact ltL_aux_famE155 f jj

theorem bT_mem_GB_famE155 (j : Nat) : nst132 j BT.zero ∈ BT.GB 0 (famE155 j) := by
  show nst132 j BT.zero
    ∈ (if 0 ≤ 1 then
        BT.sum (nst132 2 BT.zero) (BT.D 0 (nst132 j BT.zero))
          :: BT.GB 0 (BT.sum (nst132 2 BT.zero) (BT.D 0 (nst132 j BT.zero)))
       else [])
  rw [if_pos (by omega)]
  refine List.Mem.tail _ ?_
  show nst132 j BT.zero
    ∈ BT.GB 0 (nst132 2 BT.zero) ++ BT.GB 0 (BT.D 0 (nst132 j BT.zero))
  refine List.mem_append.mpr (Or.inr ?_)
  show nst132 j BT.zero
    ∈ (if 0 ≤ 0 then nst132 j BT.zero :: BT.GB 0 (nst132 j BT.zero) else [])
  rw [if_pos (by omega)]
  exact List.Mem.head _

/-- **`j ≥ 4` の係数の族は `K` 標準でない。**  内の裸の塔が項全体より下に居ない。 -/
theorem not_std_famE155 (jj : Nat) :
    BT.isStd (BT.D 0 (famE155 (jj + 4))) = false := by
  cases hs : BT.isStd (BT.D 0 (famE155 (jj + 4))) with
  | false => rfl
  | true =>
      exfalso
      have h0 : (BT.isStd (famE155 (jj + 4))
          && (BT.GB 0 (famE155 (jj + 4))).all
              (fun e => BT.lt e (famE155 (jj + 4)))) = true := hs
      have h2 := List.all_eq_true.mp ((Bool.and_eq_true _ _).mp h0).2 _
        (bT_mem_GB_famE155 (jj + 4))
      rw [show BT.lt (nst132 (jj + 4) BT.zero) (famE155 (jj + 4)) = false from
        ltL_bT_famE_false155 _ jj] at h2
      exact Bool.noConfusion h2

/-- 標準な唯一の発火形 `j = 3` — そこでは逃げる元は `0` で、一歩は成り立つ (計算)。 -/
theorem stepOK_famE3_155 : KsetStepOK 0 (dict (famE155 3)) :=
  ksetStepOK_of_b (by decide)

theorem isStd_D0_famE3_155 : BT.isStd (BT.D 0 (famE155 3)) = true := by decide

/-- **係数の族の門と標準性はちょうど同値 (`j ≥ 3`)。**  §152.12 の famB の一致が
    係数 ≠ 1・`A ⊖ Ω₁ = 0` の角でも成り立つ。 -/
theorem stepOK_iff_famE155 {j : Nat} (h3 : 3 ≤ j) :
    KsetStepOK 0 (dict (famE155 j)) ↔ BT.isStd (BT.D 0 (famE155 j)) = true := by
  obtain ⟨jj, rfl⟩ : ∃ jj, j = jj + 3 := ⟨j - 3, by omega⟩
  cases jj with
  | zero => exact ⟨fun _ => isStd_D0_famE3_155, fun _ => stepOK_famE3_155⟩
  | succ jp =>
      constructor
      · intro H
        exact absurd H (by
          rw [show jp + 1 + 3 = jp + 4 from rfl]
          exact not_ksetStepOK_famE155 jp)
      · intro hs
        exfalso
        rw [show jp + 1 + 3 = jp + 4 from rfl, not_std_famE155 jp] at hs
        exact Bool.noConfusion hs

/-- **主定理 — 係数の族は第一の門を反証できない。**  `K` 標準なら一歩は成り立つ。 -/
theorem famE_no_refute155 {j : Nat} (h3 : 3 ≤ j)
    (hs : BT.isStd (BT.D 0 (famE155 j)) = true) :
    KsetStepOK 0 (dict (famE155 j)) := (stepOK_iff_famE155 h3).mpr hs

/-- **§145.4 の H1 の義務、係数の族の上で。** -/
theorem firstFire_famE155 (j : Nat) (h3 : 3 ≤ j)
    (hs : BT.isStd (BT.D 0 (famE155 j)) = true) : FirstFire145 (famE155 j) :=
  fun p hp _ hle y hy => (famE_no_refute155 h3 hs p hp hle).2 y hy

end

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §155.5 Multi-digit `wcnf`: sums of famB terms

The self-sum `famB ⊕ famB` MERGES into one digit with coefficient `2 = 1 ⊕ 1` —
the `mulL e c, c > 1` case.  The cross sum `famB m k ⊕ famB m' k'` (`m' < m`)
keeps TWO firing digits; the second step's obligations discharge against the
accumulated index `i₀ ⊕ Δ₂`. -/

theorem plus_UW_self155 (s : Term) (j : Nat) :
    plus (UW152 s (j + 2)) (UW152 s (j + 2))
      = add (UW152 s (j + 2)) (UW152 s (j + 2)) := by
  rw [plus_cons66 (show toList (UW152 s (j + 2)) = [UW152 s (j + 2)] from rfl),
    show toList (UW152 s (j + 2)) = [UW152 s (j + 2)] from rfl,
    List.filter_cons_of_pos (by
      show ((UW152 s (j + 2) == UW152 s (j + 2))
            || lt (UW152 s (j + 2)) (UW152 s (j + 2))) = true
      rw [beq_self_eq_true]
      rfl)]
  rfl

/-- **併合 — 同じ塔の和の `wcnf` は桁一つ、係数 `2`。** -/
theorem wcnf_famBsum2_155 {s : Term} (hlt : lt s (reg 1) = true) (j : Nat) :
    wcnf (reg 1) [UW152 s (j + 2), UW152 s (j + 2)]
      = ([(UW152 s (j + 1), add TM.Term.one TM.Term.one)], zero) := by
  rw [wcnf_cons_ge (lt_UW_reg1_152 hlt (j + 2)), wcnf_UW152 hlt j]
  show (if (wA (reg 1) (UW152 s (j + 2)) == UW152 s (j + 1)) = true
        then ((wA (reg 1) (UW152 s (j + 2)),
               plus (wC (reg 1) (UW152 s (j + 2))) TM.Term.one) :: [], zero)
        else ((wA (reg 1) (UW152 s (j + 2)), wC (reg 1) (UW152 s (j + 2)))
              :: (UW152 s (j + 1), TM.Term.one) :: [], zero)) = _
  rw [wA_UW152 hlt j, wC_UW152 hlt j, if_pos (beq_self_eq_true _),
    show plus TM.Term.one TM.Term.one = add TM.Term.one TM.Term.one from rfl]

/-- **係数 `2` の吐く指数 — `mulL` が係数の成分ごとに塔を作り、`⊕` で並ぶ。** -/
theorem idx_famBsum2_155 {s : Term} (hlt : lt s (reg 1) = true) (j : Nat) :
    idxOf (reg 1) ((none : Option Term), (none : Option Term))
        (UW152 s (j + 1), add TM.Term.one TM.Term.one)
      = add (UW152 s (j + 2)) (UW152 s (j + 2)) := by
  show sub1 (mulL (mulL (reg 1) (subAP (reg 1) (UW152 s (j + 1))))
    (add TM.Term.one TM.Term.one)) = _
  rw [subAP_UW152 s (j + 1), mulL_Om1_UW152 hlt j]
  show sub1 (ofList [omegaNF (plus (UW152 s (j + 1)) (logOm TM.Term.one)),
                     omegaNF (plus (UW152 s (j + 1)) (logOm TM.Term.one))]) = _
  rw [show logOm TM.Term.one = zero from rfl,
    show plus (UW152 s (j + 1)) zero = UW152 s (j + 1) from rfl,
    omegaNF_UW152 s (j + 1)]
  show (if ((UW152 s (j + 2) : Term) == TM.Term.one) = true
        then ofList (toList (UW152 s (j + 2)))
        else add (UW152 s (j + 2)) (UW152 s (j + 2))) = _
  rw [if_neg (by rw [beq_UW_one152 s (j + 2)]; exact Bool.noConfusion)]

/-- **一段ぶんの門、係数 `2` の形。**  種の `K` の元がみな指数 (塔の対) より下なら済む。 -/
theorem stepOK_famBsum2_155 {s : Term} (hlt : lt s (reg 1) = true) (j : Nat)
    (H : ∀ y ∈ Kset (reg 1) s,
      lt y (add (UW152 s (j + 2)) (UW152 s (j + 2))) = true) :
    KsetStepOK 0 (add (UW152 s (j + 2)) (UW152 s (j + 2))) := by
  intro p hp hle
  replace hp : p ∈ scanSt (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
      (wcnf (reg 1) [UW152 s (j + 2), UW152 s (j + 2)]).1 := hp
  rw [wcnf_famBsum2_155 hlt j] at hp
  replace hp : p = (((none : Option Term), (none : Option Term)),
      (UW152 s (j + 1), add TM.Term.one TM.Term.one)) := List.mem_singleton.mp hp
  subst hp
  constructor
  · intro i0 hi0
    have hi0x : (none : Option Term) = some i0 := hi0
    cases hi0x
  · intro y hy
    show lt y (idxOf (reg 1) ((none : Option Term), (none : Option Term))
      (UW152 s (j + 1), add TM.Term.one TM.Term.one)) = true
    rw [idx_famBsum2_155 hlt j]
    rcases hy with h | h
    · rw [show (((none : Option Term), (none : Option Term)),
          (UW152 s (j + 1), add TM.Term.one TM.Term.one)).2.1 = UW152 s (j + 1) from rfl,
        Kset_UW152 s (j + 1)] at h
      exact H y h
    · rw [show (((none : Option Term), (none : Option Term)),
          (UW152 s (j + 1), add TM.Term.one TM.Term.one)).2.2
            = add TM.Term.one TM.Term.one from rfl] at h
      exact absurd h (by intro hc; cases hc)

/-- **併合の族の門 — `famB ⊕ famB` は標準側の全域で一歩を満たす。** -/
theorem ksetStepOK_famBsum2_155 {m k : Nat} (h3 : 3 ≤ k) (hkm : k ≤ m) :
    KsetStepOK 0 (dict (BT.sum (famB132 m k) (famB132 m k))) := by
  obtain ⟨kk, rfl⟩ : ∃ kk, k = kk + 3 := ⟨k - 3, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, m = (kk + d) + 3 := ⟨m - (kk + 3), by omega⟩
  obtain ⟨_, _, hlt, _, _⟩ := sd_facts152 kk
  rw [Trans.Dict.dict_sum,
    show kk + d + 3 = (kk + d + 2) + 1 from rfl,
    dict_famB152 kk (kk + d + 2),
    plus_UW_self155 (sd152 (kk + 3)) (kk + d)]
  refine stepOK_famBsum2_155 hlt (kk + d) ?_
  intro y hy
  cases kk with
  | zero =>
      rw [Kset_sd3_152] at hy
      rw [List.mem_singleton.mp hy]
      exact lt_zero_left (by intro hc; exact Term.noConfusion hc)
  | succ jp =>
      rw [show jp + 1 + 3 = jp + 4 from rfl, Kset_sd_psi152 jp] at hy
      rw [List.mem_singleton.mp hy]
      rw [lt_nsum_add100 (show (TW (jp + 3) : Term) ≠ zero from by
            intro hc; exact Term.noConfusion hc) rfl]
      show ((TW (jp + 3) == UW152 (sd152 (jp + 1 + 3)) (jp + 1 + d + 2))
            || lt (TW (jp + 3)) (UW152 (sd152 (jp + 1 + 3)) (jp + 1 + d + 2))) = true
      rw [lt_TW_UW152 _ (jp + 3) (jp + 1 + d + 2) (by omega)]
      exact Bool.or_true _

/-! §155.5b The cross sum: two firing digits -/

theorem beq_UW_ne155' (s t : Term) {a b : Nat} (h : b < a) :
    ((UW152 s a : Term) == UW152 t b) = false :=
  beq_eq_false_iff_ne.mpr (fun hc => UW_ne155 t s b a h hc.symm)

/-- **二桁の `wcnf` — 高さの違う塔の和は併合されない。** -/
theorem wcnf_famBsumX_155 {s t : Term} (hs : lt s (reg 1) = true)
    (ht : lt t (reg 1) = true) {a b : Nat} (hab : b < a) :
    wcnf (reg 1) [UW152 s (a + 2), UW152 t (b + 2)]
      = ([(UW152 s (a + 1), TM.Term.one), (UW152 t (b + 1), TM.Term.one)], zero) := by
  rw [wcnf_cons_ge (lt_UW_reg1_152 hs (a + 2)), wcnf_UW152 ht b]
  show (if (wA (reg 1) (UW152 s (a + 2)) == UW152 t (b + 1)) = true
        then ((wA (reg 1) (UW152 s (a + 2)),
               plus (wC (reg 1) (UW152 s (a + 2))) TM.Term.one) :: [], zero)
        else ((wA (reg 1) (UW152 s (a + 2)), wC (reg 1) (UW152 s (a + 2)))
              :: (UW152 t (b + 1), TM.Term.one) :: [], zero)) = _
  rw [wA_UW152 hs a, wC_UW152 hs a,
    if_neg (by
      rw [beq_UW_ne155' s t (show b + 1 < a + 1 by omega)]
      exact Bool.noConfusion)]

/-- 最初の発火の一歩の後の状態。 -/
theorem stepF_fire155 {s : Term} (hlt : lt s (reg 1) = true) (j : Nat) :
    stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (UW152 s (j + 1), TM.Term.one)
      = (some (UW152 s (j + 2)), some (psi (reg 1) (UW152 s (j + 2)))) := by
  show (if le (reg 1) (UW152 s (j + 1)) = true
        then (some (idxOf (reg 1) ((none : Option Term), (none : Option Term))
                (UW152 s (j + 1), TM.Term.one)),
              some (psi (reg 1) (idxOf (reg 1) ((none : Option Term), (none : Option Term))
                (UW152 s (j + 1), TM.Term.one))))
        else ((none : Option Term),
              some (phiNF (UW152 s (j + 1)) (plus (baseOf 0) (sub1 TM.Term.one))))) = _
  rw [if_pos (le_reg1_UW152 s (j + 1)), idx_UW152 hlt j]

/-- 二歩目の吐く指数 — 直前の指数に塔を足す。 -/
theorem idx2_155 {t : Term} (ht : lt t (reg 1) = true) (i0 : Term) (s2 : Option Term)
    (b : Nat) :
    idxOf (reg 1) (some i0, s2) (UW152 t (b + 1), TM.Term.one)
      = plus i0 (UW152 t (b + 2)) := by
  show plus i0 (mulL (mulL (reg 1) (subAP (reg 1) (UW152 t (b + 1)))) TM.Term.one) = _
  rw [subAP_UW152 t (b + 1), mulL_Om1_UW152 ht b, mulL_UW_one152 t (b + 1)]

theorem plus_UW_UW155 {s t : Term} (a b : Nat) (h : b < a) :
    plus (UW152 s (a + 2)) (UW152 t (b + 2))
      = add (UW152 s (a + 2)) (UW152 t (b + 2)) := by
  rw [plus_cons66 (show toList (UW152 t (b + 2)) = [UW152 t (b + 2)] from rfl),
    show toList (UW152 s (a + 2)) = [UW152 s (a + 2)] from rfl,
    List.filter_cons_of_pos (by
      show ((UW152 t (b + 2) == UW152 s (a + 2))
            || lt (UW152 t (b + 2)) (UW152 s (a + 2))) = true
      rw [lt_UW_UW_lt155 t s (b + 2) (a + 2) (by omega)]
      exact Bool.or_true _)]
  rfl

/-- **一段ぶんの門、二桁の形。**  一歩目は種 `s` の `K` の塔の義務、二歩目は
    直前の指数の `K` (= `K s`) と種 `t` の `K` の義務 — どれも指数の和より下なら済む。 -/
theorem stepOK_famBsumX_155 {s t : Term} (hs : lt s (reg 1) = true)
    (ht : lt t (reg 1) = true) {a b : Nat} (hab : b < a)
    (H1 : ∀ y ∈ Kset (reg 1) s, lt y (UW152 s (a + 2)) = true)
    (H1' : ∀ y ∈ Kset (reg 1) s,
      lt y (add (UW152 s (a + 2)) (UW152 t (b + 2))) = true)
    (H2' : ∀ y ∈ Kset (reg 1) t,
      lt y (add (UW152 s (a + 2)) (UW152 t (b + 2))) = true) :
    KsetStepOK 0 (add (UW152 s (a + 2)) (UW152 t (b + 2))) := by
  intro p hp hle
  replace hp : p ∈ scanSt (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
      (wcnf (reg 1) [UW152 s (a + 2), UW152 t (b + 2)]).1 := hp
  rw [wcnf_famBsumX_155 hs ht hab] at hp
  replace hp : p ∈ [(((none : Option Term), (none : Option Term)),
        (UW152 s (a + 1), TM.Term.one)),
      (stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (UW152 s (a + 1), TM.Term.one), (UW152 t (b + 1), TM.Term.one))] := hp
  rw [stepF_fire155 hs a] at hp
  rcases List.mem_cons.mp hp with h1 | h1
  · subst h1
    constructor
    · intro i0 hi0
      have hi0x : (none : Option Term) = some i0 := hi0
      cases hi0x
    · intro y hy
      show lt y (idxOf (reg 1) ((none : Option Term), (none : Option Term))
        (UW152 s (a + 1), TM.Term.one)) = true
      rw [idx_UW152 hs a]
      rcases hy with h | h
      · rw [show (((none : Option Term), (none : Option Term)),
            (UW152 s (a + 1), TM.Term.one)).2.1 = UW152 s (a + 1) from rfl,
          Kset_UW152 s (a + 1)] at h
        exact H1 y h
      · rw [show (((none : Option Term), (none : Option Term)),
            (UW152 s (a + 1), TM.Term.one)).2.2 = TM.Term.one from rfl] at h
        exact absurd h (by intro hc; cases hc)
  · replace h1 : p = ((some (UW152 s (a + 2)),
        some (psi (reg 1) (UW152 s (a + 2)))), (UW152 t (b + 1), TM.Term.one)) :=
      List.mem_singleton.mp h1
    subst h1
    constructor
    · intro i0 hi0 y hy
      have hi0e : i0 = UW152 s (a + 2) := by
        have hx : some (UW152 s (a + 2)) = some i0 := hi0
        injection hx with hx2
        exact hx2.symm
      subst hi0e
      rw [Kset_UW152 s (a + 2)] at hy
      show lt y (idxOf (reg 1) (some (UW152 s (a + 2)),
        some (psi (reg 1) (UW152 s (a + 2)))) (UW152 t (b + 1), TM.Term.one)) = true
      rw [idx2_155 ht (UW152 s (a + 2)) _ b, plus_UW_UW155 a b hab]
      exact H1' y hy
    · intro y hy
      show lt y (idxOf (reg 1) (some (UW152 s (a + 2)),
        some (psi (reg 1) (UW152 s (a + 2)))) (UW152 t (b + 1), TM.Term.one)) = true
      rw [idx2_155 ht (UW152 s (a + 2)) _ b, plus_UW_UW155 a b hab]
      rcases hy with h | h
      · rw [show ((some (UW152 s (a + 2)), some (psi (reg 1) (UW152 s (a + 2)))),
            (UW152 t (b + 1), TM.Term.one)).2.1 = UW152 t (b + 1) from rfl,
          Kset_UW152 t (b + 1)] at h
        exact H2' y h
      · rw [show ((some (UW152 s (a + 2)), some (psi (reg 1) (UW152 s (a + 2)))),
            (UW152 t (b + 1), TM.Term.one)).2.2 = TM.Term.one from rfl] at h
        exact absurd h (by intro hc; cases hc)

/-- **二桁の族の門 — `famB m k ⊕ famB m' k'` (`m' < m`) は標準側の全域で一歩を満たす。** -/
theorem ksetStepOK_famB_sum155 {m k m' k' : Nat} (h3 : 3 ≤ k) (hkm : k ≤ m)
    (h3' : 3 ≤ k') (hk'm' : k' ≤ m') (hm'm : m' < m) :
    KsetStepOK 0 (dict (BT.sum (famB132 m k) (famB132 m' k'))) := by
  obtain ⟨kk, rfl⟩ : ∃ kk, k = kk + 3 := ⟨k - 3, by omega⟩
  obtain ⟨kq, rfl⟩ : ∃ kq, k' = kq + 3 := ⟨k' - 3, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, m = (kk + d) + 3 := ⟨m - (kk + 3), by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, m' = (kq + e) + 3 := ⟨m' - (kq + 3), by omega⟩
  obtain ⟨_, _, hs, _, _⟩ := sd_facts152 kk
  obtain ⟨_, _, ht, _, _⟩ := sd_facts152 kq
  have hab : kq + e < kk + d := by omega
  rw [Trans.Dict.dict_sum,
    show kk + d + 3 = (kk + d + 2) + 1 from rfl,
    show kq + e + 3 = (kq + e + 2) + 1 from rfl,
    dict_famB152 kk (kk + d + 2), dict_famB152 kq (kq + e + 2),
    plus_UW_UW155 (kk + d) (kq + e) hab]
  refine stepOK_famBsumX_155 hs ht hab ?_ ?_ ?_
  · intro y hy
    cases kk with
    | zero =>
        rw [Kset_sd3_152] at hy
        rw [List.mem_singleton.mp hy]
        exact lt_zero_left (ne_zero_UW152 _ _)
    | succ jp =>
        rw [show jp + 1 + 3 = jp + 4 from rfl, Kset_sd_psi152 jp] at hy
        rw [List.mem_singleton.mp hy]
        exact lt_TW_UW152 _ (jp + 3) (jp + 1 + d + 2) (by omega)
  · intro y hy
    cases kk with
    | zero =>
        rw [Kset_sd3_152] at hy
        rw [List.mem_singleton.mp hy]
        exact lt_zero_left (by intro hc; exact Term.noConfusion hc)
    | succ jp =>
        rw [show jp + 1 + 3 = jp + 4 from rfl, Kset_sd_psi152 jp] at hy
        rw [List.mem_singleton.mp hy]
        rw [lt_nsum_add100 (show (TW (jp + 3) : Term) ≠ zero from by
              intro hc; exact Term.noConfusion hc) rfl]
        show ((TW (jp + 3) == UW152 (sd152 (jp + 1 + 3)) (jp + 1 + d + 2))
              || lt (TW (jp + 3)) (UW152 (sd152 (jp + 1 + 3)) (jp + 1 + d + 2))) = true
        rw [lt_TW_UW152 _ (jp + 3) (jp + 1 + d + 2) (by omega)]
        exact Bool.or_true _
  · intro y hy
    cases kq with
    | zero =>
        rw [Kset_sd3_152] at hy
        rw [List.mem_singleton.mp hy]
        exact lt_zero_left (by intro hc; exact Term.noConfusion hc)
    | succ jp =>
        rw [show jp + 1 + 3 = jp + 4 from rfl, Kset_sd_psi152 jp] at hy
        rw [List.mem_singleton.mp hy]
        rw [lt_nsum_add100 (show (TW (jp + 3) : Term) ≠ zero from by
              intro hc; exact Term.noConfusion hc) rfl]
        show ((TW (jp + 3) == UW152 (sd152 (kk + 3)) (kk + d + 2))
              || lt (TW (jp + 3)) (UW152 (sd152 (kk + 3)) (kk + d + 2))) = true
        rw [lt_TW_UW152 _ (jp + 3) (kk + d + 2) (by omega)]
        exact Bool.or_true _

/-- 一項ぶんの門と H1 の義務、和の族の上で。 -/
theorem gateStd87_famBsum2_155 (m k : Nat) (h3 : 3 ≤ k) (hkm : k ≤ m) :
    GateStd87 (BT.sum (famB132 m k) (famB132 m k)) :=
  fun _ _ => ksetStepOK_famBsum2_155 h3 hkm

theorem gateStd87_famB_sum155 (m k m' k' : Nat) (h3 : 3 ≤ k) (hkm : k ≤ m)
    (h3' : 3 ≤ k') (hk'm' : k' ≤ m') (hm'm : m' < m) :
    GateStd87 (BT.sum (famB132 m k) (famB132 m' k')) :=
  fun _ _ => ksetStepOK_famB_sum155 h3 hkm h3' hk'm' hm'm

theorem firstFire_famBsum2_155 (m k : Nat) (h3 : 3 ≤ k) (hkm : k ≤ m) :
    FirstFire145 (BT.sum (famB132 m k) (famB132 m k)) :=
  fun p hp _ hle y hy => (ksetStepOK_famBsum2_155 h3 hkm p hp hle).2 y hy

theorem firstFire_famB_sum155 (m k m' k' : Nat) (h3 : 3 ≤ k) (hkm : k ≤ m)
    (h3' : 3 ≤ k') (hk'm' : k' ≤ m') (hm'm : m' < m) :
    FirstFire145 (BT.sum (famB132 m k) (famB132 m' k')) :=
  fun p hp _ hle y hy => (ksetStepOK_famB_sum155 h3 hkm h3' hk'm' hm'm p hp hle).2 y hy

end

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §155.6 Measurement (frozen) — the theorems against the kernel and the pools

Everything below is measurement, not proof. -/

/-! famC の閉じた形の照合 — `dict` の値は本当に入れ子の種の塔。 -/
#guard (List.range 3).all fun m => (List.range 2).all fun kk => (List.range 2).all fun jj =>
  dict (famC155 (m + 1) (kk + 3) (jj + 3)) == UW152 (sdC155 kk jj) m

/-! **famC の二つの境界の凍結 (`3 ≤ m, k, j < 9`)。**  一歩は `k ≤ m ∧ j ≤ m`
    (証明済みの iff と一致)、標準性は `j ≤ k ∧ k ≤ m`。門の一歩の領域は標準領域より
    真に広い — `j > k` の楔では一歩は立つが標準性は立たない。 -/
#guard (List.range 6).all fun m0 => (List.range 6).all fun k0 => (List.range 6).all fun j0 =>
  (stepOKb 0 (dict (famC155 (m0 + 3) (k0 + 3) (j0 + 3)))
      == (decide (k0 ≤ m0) && decide (j0 ≤ m0)))
  && (BT.isStd (BT.D 0 (famC155 (m0 + 3) (k0 + 3) (j0 + 3)))
      == (decide (j0 ≤ k0) && decide (k0 ≤ m0)))

/-! famE の閉じた形と境界の凍結 — 一歩も標準性も `j = 3` だけ (発火形 `j ≥ 3` の中で)。 -/
#guard (List.range 6).all fun jj =>
  dict (famE155 (jj + 3)) == phi zero (add (TW 1) (sd152 (jj + 3)))
#guard (List.range 7).all fun j0 =>
  (stepOKb 0 (dict (famE155 (j0 + 3))) == decide (j0 == 0))
  && (BT.isStd (BT.D 0 (famE155 (j0 + 3))) == decide (j0 == 0))

/-! 和の族の照合 — 併合 (係数 2) も二桁も、定理の領域で一歩の判定器は真。 -/
#guard (List.range 4).all fun k0 => (List.range 3).all fun d =>
  stepOKb 0 (dict (BT.sum (famB132 (k0 + 3 + d) (k0 + 3)) (famB132 (k0 + 3 + d) (k0 + 3))))
#guard (List.range 3).all fun k0 => (List.range 3).all fun d =>
  stepOKb 0 (dict (BT.sum (famB132 (k0 + 4 + d) (k0 + 3)) (famB132 (k0 + 3) (k0 + 3))))

/-! **母集団との重なり。**  famC は §132.5 の famPool132 の第二の族そのもの
    (`m, k, j < 8`)、famE は famPool132 の第一の族 (`m = 1, p = 2`) と §145.5 の
    fm145 (`j ≤ 6`) に居る。famC は fm145 に居ない — 入れ子の深さ 2 は §145.5 の
    掃きの外。凍結済みの掃きは低い高さだけ、定理は全ての高さ。 -/
#guard famPool132.contains (famC155 4 4 4)
#guard famPool132.contains (famE155 4)
#guard fm145.contains (famE155 4)
#guard fm145.contains (famE155 6)
#guard !(fm145.contains (famC155 4 4 4))

/-! **H1 の残る母集団は凍結済みの母集団の上で空。**  §145.4 の H1 が義務を課すのは
    `hotb136 = true` かつ `laterHotb145 = false` の `K` 標準な項だけ — その形は
    §132.5 の famPool132 にも §136.4 の pool136 にも §145.5 の fm145 にも 0 本。 -/
#guard (famPool132.filter (fun a => btLe72 1 a && !btLe72 0 a && BT.isStd (BT.D 0 a)
    && !(fireK132 a).isEmpty && hotb136 a && !hiPure145 a && !laterHotb145 a)).length == 0
#guard (pool136.filter (fun a => btLe72 1 a && !btLe72 0 a && BT.isStd (BT.D 0 a)
    && !(fireK132 a).isEmpty && hotb136 a && !hiPure145 a && !laterHotb145 a)).length == 0
#guard (fm145.filter (fun a => resid136 a && hotb136 a && !hiPure145 a
    && !laterHotb145 a)).length == 0

/-! ### §155.7 What fraction of the §132 residual the PROVED classes are

Shape deciders for the classes closed at every height by §152 + §155:
pure towers, famB, famC (nested), famE (= famA132), and famB ⊕ famB. -/

def isTow155 : BT → Bool
  | BT.zero => true
  | BT.D 1 a => isTow155 a
  | _ => false

def isFamB155 : BT → Bool
  | BT.D 1 a => isFamB155 a
  | BT.D 0 a => isTow155 a
  | _ => false

def isFamC155 : BT → Bool
  | BT.D 1 a => isFamC155 a
  | BT.D 0 a => isFamB155 a
  | _ => false

def isFamE155 : BT → Bool
  | BT.D 1 (BT.sum x (BT.D 0 y)) => (x == nst132 2 BT.zero) && isTow155 y
  | _ => false

def isSumBB155 : BT → Bool
  | BT.sum x y => isFamB155 x && isFamB155 y
  | _ => false

def covered155 (a : BT) : Bool :=
  isTow155 a || isFamB155 a || isFamC155 a || isFamE155 a || isSumBB155 a

/-! **被覆の凍結。**  §132 の残り (`resid136`) のうち、証明済みの形の類に文字通り
    入っている本数:
    famPool132 (2455 本): famB 391 + famC 80 + famE 1 + famB⊕famB 32 = **504 本 (20.5%)**。
    pool136 (925 本): **0 本** — pool136 は混合の和 (裸の塔 ⊕ famB、famB ⊕ 裸の塔、
    和の種) だけで組んであり、まだ証明の類の外。
    fm145 (3371 本): **15 本**。
    残る形の名: 混合の塔の和と、種が和の `ψ₀` — §155.5 の `stepOK_famBsumX_155` の
    種を `Ω₁` (裸の塔) と和に広げるのが次の一歩。 -/
#guard (famPool132.filter resid136).length == 2455
#guard ((famPool132.filter resid136).countP isFamB155,
        (famPool132.filter resid136).countP isFamC155,
        (famPool132.filter resid136).countP isFamE155,
        (famPool132.filter resid136).countP isSumBB155,
        (famPool132.filter resid136).countP covered155) == (391, 80, 1, 32, 504)
#guard (pool136.filter resid136).length == 925
#guard ((pool136.filter resid136).countP covered155) == 0
#guard (fm145.filter resid136).length == 3371
#guard ((fm145.filter resid136).countP covered155) == 15

/-! ### Axioms — no `sorryAx`, no `native_decide` -/

#print axioms lt_UW_UW_same155
#print axioms lt_UW_UW_lt155
#print axioms lt_UW_UW_false155
#print axioms collapse0_UW155
#print axioms dict_famC155
#print axioms ksetStepOK_famC155
#print axioms not_ksetStepOK_famC_k155
#print axioms not_ksetStepOK_famC_j155
#print axioms stepOK_iff_famC155
#print axioms famC_no_refute155
#print axioms firstFire_famC155
#print axioms psiIdxOK_famC155
#print axioms dict_famE155
#print axioms not_ksetStepOK_famE155
#print axioms not_std_famE155
#print axioms stepOK_iff_famE155
#print axioms famE_no_refute155
#print axioms firstFire_famE155
#print axioms ksetStepOK_famBsum2_155
#print axioms ksetStepOK_famB_sum155
#print axioms firstFire_famBsum2_155
#print axioms firstFire_famB_sum155

end



/-!
# §156 THE FIRST GATE: the cross sum with an ARBITRARY second seed, and sum-seed towers

§155.5 closed the cross sum `famB m k ⊕ famB m' k'` — both summands towers over
famB seeds (`sd152 k < Ω₁`).  This file widens it in the two directions §155.7
named as the residual:

  §156.1  Seed-free plumbing: every §152.3 `wcnf`/`idxOf` lemma about the tower
          `UW152 s j` holds for an ARBITRARY seed `s` — including `s = Ω₁`,
          whose tower is `TW` (`TW (j+1) = UW152 Ω₁ j`).  The hypothesis
          `lt s Ω₁ = true` was never load-bearing.

  §156.2  Order/equality tools: seed-injectivity of the towers, `le` on `TW`.

  §156.3  The GENERAL cross sum `UW152 s (a+2) ⊕ UW152 t (b+2)`: two firing
          digits for any two seeds (equal heights allowed when the seeds
          differ), and the step lemma `stepOK_sumX156` whose obligations are
          only the K-sets of the two seeds.

  §156.4  MIXED sums at the BT level, both orders:
          `famB m k ⊕ ψ₁^p 0` (`3 ≤ k ≤ m`, `1 ≤ p ≤ m`, the low towers
          `p ≤ 3` by their own small digits — `(1,1)`, `(1⊕1,1)` do not fire,
          `(Ω₁,1)` fires into the accumulated index) and
          `ψ₁^p 0 ⊕ famB m k` (`3 ≤ k`, `3 ≤ m < p`, `k ≤ p` — the escaping
          element discharges against the HEAD tower's index).

  §156.5  SUM-SEED towers `famD156 m k j = ψ₁^m(ψ₀(ψ₁^k 0 ⊕ ψ₁^j 0))`:
          the seed's closed forms in all five regimes
          (`j = k` merges to coefficient 2; `4 ≤ j < k` two firing digits;
          `j = 3` fires as `(Ω₁,1)` and the value drops to `ψ_{Ω₁}(tower ⊕ 1)`;
          `j ∈ {1,2}` do not fire and the value is `φ̄(j, ψ_{Ω₁}(tower))`),
          the tower over each seed, and the step on `3 ≤ k ≤ m`, `1 ≤ j ≤ k` —
          exactly the residual range (frozen below).

  §156.6  Measurement (frozen): the resid boundaries of the three families,
          kernel re-checks of the closed forms, pool membership, and the new
          coverage counts on `famPool132` / `pool136` / `fm145`.
-/


section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §156.1 Seed-free plumbing for the tower `UW152 s j` -/

/-- 塔は `Ω₁` より下に居ない — 種がどれでも。§152.3 の `lt_UW_reg1_152` から
    仮定 `s < Ω₁` を外したもの。底 `Ω₁ ⊕ s` の頭が `Ω₁` なので種は見えない。 -/
theorem lt_UW_reg1_156 (s : Term) : ∀ j : Nat, lt (UW152 s j) (reg 1) = false
  | 0 => by
      show lt (phi zero (add (Z zero) s)) (reg 1) = false
      rw [lt_phi_reg1_100,
        show lt (add (Z zero) s) (reg 1) = false from by
          rw [lt_add_nsum (show (reg 1 : Term) ≠ zero from by
                intro hc; exact Term.noConfusion hc) rfl]
          show lt (Z zero) (Z zero) = false
          exact lt_irrefl _]
      exact Bool.and_false _
  | j + 1 => by
      show lt (phi zero (UW152 s j)) (reg 1) = false
      rw [lt_phi_reg1_100, lt_UW_reg1_156 s j]
      exact Bool.and_false _

theorem le_UW_reg1_156 (s : Term) (j : Nat) : le (UW152 s j) (reg 1) = false := by
  show (((UW152 s j : Term) == Z zero) || lt (UW152 s j) (Z zero)) = false
  rw [beq_UW_Om152 s j, show lt (UW152 s j) (Z zero) = false from lt_UW_reg1_156 s j]
  rfl

theorem plus_Om1_UW156 (s : Term) (j : Nat) :
    plus (reg 1) (UW152 s j) = UW152 s j := by
  cases j with
  | zero =>
      show ofList (List.filter (fun a => le (phi zero (add (Z zero) s)) a) [Z zero]
        ++ [phi zero (add (Z zero) s)]) = _
      rw [show List.filter (fun a => le (phi zero (add (Z zero) s)) a) [Z zero] = [] from by
        show (match le (phi zero (add (Z zero) s)) (Z zero) with
              | true => Z zero
                  :: List.filter (fun a => le (phi zero (add (Z zero) s)) a) []
              | false => List.filter (fun a => le (phi zero (add (Z zero) s)) a) []) = []
        rw [show le (phi zero (add (Z zero) s)) (Z zero) = false from le_UW_reg1_156 s 0]
        rfl]
      rfl
  | succ j =>
      show ofList (List.filter (fun a => le (phi zero (UW152 s j)) a) [Z zero]
        ++ [phi zero (UW152 s j)]) = _
      rw [show List.filter (fun a => le (phi zero (UW152 s j)) a) [Z zero] = [] from by
        show (match le (phi zero (UW152 s j)) (Z zero) with
              | true => Z zero :: List.filter (fun a => le (phi zero (UW152 s j)) a) []
              | false => List.filter (fun a => le (phi zero (UW152 s j)) a) []) = []
        rw [show le (phi zero (UW152 s j)) (Z zero) = false from le_UW_reg1_156 s (j + 1)]
        rfl]
      rfl

theorem mulL_Om1_UW156 (s : Term) (j : Nat) :
    mulL (reg 1) (UW152 s (j + 1)) = UW152 s (j + 1) := by
  show ofList [omegaNF (plus (reg 1) (logOm (UW152 s (j + 1))))] = _
  rw [logOm_UW152 s j, plus_Om1_UW156 s j, omegaNF_UW152 s j]
  rfl

theorem filter_ge_UW156 (s : Term) (j : Nat) :
    List.filter (fun q => !lt q (reg 1)) [UW152 s j] = [UW152 s j] := by
  show (match (!lt (UW152 s j) (reg 1)) with
        | true => UW152 s j :: List.filter (fun q => !lt q (reg 1)) []
        | false => List.filter (fun q => !lt q (reg 1)) []) = _
  rw [lt_UW_reg1_156 s j]
  rfl

theorem filter_lt_UW156 (s : Term) (j : Nat) :
    List.filter (fun q => lt q (reg 1)) [UW152 s j] = [] := by
  show (match (lt (UW152 s j) (reg 1)) with
        | true => UW152 s j :: List.filter (fun q => lt q (reg 1)) []
        | false => List.filter (fun q => lt q (reg 1)) []) = _
  rw [lt_UW_reg1_156 s j]
  rfl

/-- **発火する段の `wcnf` — 桁一つ、指数は一段下の塔。種は任意。** -/
theorem wA_UW156 (s : Term) (j : Nat) :
    wA (reg 1) (UW152 s (j + 2)) = UW152 s (j + 1) := by
  show ofList (List.map (divAP (reg 1)) (List.filter (fun q => !lt q (reg 1))
    (toList (logOm (UW152 s (j + 2)))))) = _
  rw [logOm_UW152 s (j + 1),
    show toList (UW152 s (j + 1)) = [UW152 s (j + 1)] from rfl,
    filter_ge_UW156 s (j + 1)]
  show ofList [divAP (reg 1) (UW152 s (j + 1))] = _
  show ofList [omegaNF (subAP (reg 1) (logOm (UW152 s (j + 1))))] = _
  rw [logOm_UW152 s j, subAP_UW152 s j, omegaNF_UW152 s j]
  rfl

theorem wC_UW156 (s : Term) (j : Nat) :
    wC (reg 1) (UW152 s (j + 2)) = TM.Term.one := by
  show omegaNF (ofList (List.filter (fun q => lt q (reg 1))
    (toList (logOm (UW152 s (j + 2)))))) = _
  rw [logOm_UW152 s (j + 1),
    show toList (UW152 s (j + 1)) = [UW152 s (j + 1)] from rfl,
    filter_lt_UW156 s (j + 1)]
  exact omegaNF_zero135

theorem wcnf_UW156 (s : Term) (j : Nat) :
    wcnf (reg 1) [UW152 s (j + 2)] = ([(UW152 s (j + 1), TM.Term.one)], zero) := by
  rw [wcnf_cons_ge (lt_UW_reg1_156 s (j + 2))]
  show ([(wA (reg 1) (UW152 s (j + 2)), wC (reg 1) (UW152 s (j + 2)))], zero) = _
  rw [wA_UW156 s j, wC_UW156 s j]

theorem idx_UW156 (s : Term) (j : Nat) :
    idxOf (reg 1) ((none : Option Term), (none : Option Term))
      (UW152 s (j + 1), TM.Term.one) = UW152 s (j + 2) := by
  show sub1 (mulL (mulL (reg 1) (subAP (reg 1) (UW152 s (j + 1)))) TM.Term.one) = _
  rw [subAP_UW152 s (j + 1), mulL_Om1_UW156 s j, mulL_UW_one152 s (j + 1),
    sub1_UW152 s (j + 2)]

/-- 最初の発火の一歩の後の状態 — 種は任意。 -/
theorem stepF_fire156 (s : Term) (j : Nat) :
    stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (UW152 s (j + 1), TM.Term.one)
      = (some (UW152 s (j + 2)), some (psi (reg 1) (UW152 s (j + 2)))) := by
  show (if le (reg 1) (UW152 s (j + 1)) = true
        then (some (idxOf (reg 1) ((none : Option Term), (none : Option Term))
                (UW152 s (j + 1), TM.Term.one)),
              some (psi (reg 1) (idxOf (reg 1) ((none : Option Term), (none : Option Term))
                (UW152 s (j + 1), TM.Term.one))))
        else ((none : Option Term),
              some (phiNF (UW152 s (j + 1)) (plus (baseOf 0) (sub1 TM.Term.one))))) = _
  rw [if_pos (le_reg1_UW152 s (j + 1)), idx_UW156 s j]

/-- 二歩目の吐く指数 — 直前の指数に塔を足す。種は任意。 -/
theorem idx2_156 (t : Term) (i0 : Term) (s2 : Option Term) (b : Nat) :
    idxOf (reg 1) (some i0, s2) (UW152 t (b + 1), TM.Term.one)
      = plus i0 (UW152 t (b + 2)) := by
  show plus i0 (mulL (mulL (reg 1) (subAP (reg 1) (UW152 t (b + 1)))) TM.Term.one) = _
  rw [subAP_UW152 t (b + 1), mulL_Om1_UW156 t b, mulL_UW_one152 t (b + 1)]

/-! ### §156.2 `TW` is the tower over `Ω₁`; seed-injectivity; order tools -/

/-- `TW (j+1) = UW152 Ω₁ j` — 裸の塔は種 `Ω₁` の `UW` の塔。 -/
theorem TW_UW156 : ∀ j : Nat, TW (j + 1) = UW152 (Z zero) j
  | 0 => rfl
  | j + 1 => congrArg (phi zero) (TW_UW156 j)

/-- 同じ高さの塔が等しければ種も等しい。 -/
theorem UW_seed_ne156 {s t : Term} (h : s ≠ t) : ∀ j : Nat, UW152 s j ≠ UW152 t j
  | 0 => fun hc => by
      have hc2 : phi zero (add (Z zero) s) = phi zero (add (Z zero) t) := hc
      injection hc2 with _ h2
      injection h2 with _ h3
      exact h h3
  | j + 1 => fun hc => by
      have hc2 : phi zero (UW152 s j) = phi zero (UW152 t j) := hc
      injection hc2 with _ h2
      exact UW_seed_ne156 h j h2

theorem beq_UW_seed156 {s t : Term} (h : s ≠ t) (j : Nat) :
    ((UW152 s j : Term) == UW152 t j) = false :=
  beq_eq_false_iff_ne.mpr (UW_seed_ne156 h j)

theorem le_self156 (x : Term) : le x x = true := by
  show ((x == x) || lt x x) = true
  rw [beq_self_eq_true]
  rfl

/-- `a ≤ b` なら `TW a ≤ TW b` (`b ≥ 1`)。 -/
theorem le_TW_TW156 {a b : Nat} (h : a ≤ b) (hb : 1 ≤ b) :
    le (TW a) (TW b) = true := by
  rcases Nat.eq_or_lt_of_le h with rfl | hlt
  · exact le_self156 _
  · obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    show (((TW a : Term) == TW (c + 1)) || lt (TW a) (TW (c + 1))) = true
    rw [TW_UW156 c, lt_TW_UW152 (Z zero) a c (by omega)]
    exact Bool.or_true _

theorem lt_one_UW156 (s : Term) (j : Nat) : lt TM.Term.one (UW152 s j) = true := by
  cases j with
  | zero =>
      show lt (phi zero zero) (phi zero (add (Z zero) s)) = true
      rw [lt_phi_same139]
      exact lt_zero_left (by intro hc; exact Term.noConfusion hc)
  | succ j =>
      show lt (phi zero zero) (phi zero (UW152 s j)) = true
      rw [lt_phi_same139]
      exact lt_zero_left (ne_zero_UW152 s j)

theorem Kset_Om156 : Kset (reg 1) (Z zero) = [] := rfl

/-! ### §156.3 The general cross sum: `plus`, `wcnf`, the step -/

theorem plus_UW_UW156 {s t : Term} {a b : Nat}
    (h : le (UW152 t b) (UW152 s a) = true) :
    plus (UW152 s a) (UW152 t b) = add (UW152 s a) (UW152 t b) := by
  rw [plus_cons66 (show toList (UW152 t b) = [UW152 t b] from by cases b <;> rfl),
    show toList (UW152 s a) = [UW152 s a] from by cases a <;> rfl,
    List.filter_cons_of_pos (by exact h)]
  rfl

theorem plus_UW_one156 (s : Term) (j : Nat) :
    plus (UW152 s j) TM.Term.one = add (UW152 s j) TM.Term.one := by
  rw [plus_cons66 (show toList (TM.Term.one : Term) = [TM.Term.one] from rfl),
    show toList (UW152 s j) = [UW152 s j] from by cases j <;> rfl,
    List.filter_cons_of_pos (by
      show ((TM.Term.one == UW152 s j) || lt TM.Term.one (UW152 s j)) = true
      rw [lt_one_UW156 s j]
      exact Bool.or_true _)]
  rfl

theorem plus_UW_Om156 (s : Term) (a : Nat) :
    plus (UW152 s a) (Z zero) = add (UW152 s a) (Z zero) := by
  rw [plus_cons66 (show toList (Z zero : Term) = [Z zero] from rfl),
    show toList (UW152 s a) = [UW152 s a] from by cases a <;> rfl,
    List.filter_cons_of_pos (by exact le_reg1_UW152 s a)]
  rfl

theorem plus_UW_TW156 {s : Term} {a c : Nat}
    (h : le (TW (c + 1)) (UW152 s a) = true) :
    plus (UW152 s a) (TW (c + 1)) = add (UW152 s a) (TW (c + 1)) := by
  rw [plus_cons66 (show toList (TW (c + 1)) = [TW (c + 1)] from rfl),
    show toList (UW152 s a) = [UW152 s a] from by cases a <;> rfl,
    List.filter_cons_of_pos (by exact h)]
  rfl

/-- **二桁の `wcnf`、種は両方とも任意。**  桁が併合されない条件は指数の不等だけ —
    高さが違うか、同じ高さで種が違うか。 -/
theorem wcnf_sumX156 (s t : Term) {a b : Nat}
    (hne : ((UW152 s (a + 1) : Term) == UW152 t (b + 1)) = false) :
    wcnf (reg 1) [UW152 s (a + 2), UW152 t (b + 2)]
      = ([(UW152 s (a + 1), TM.Term.one), (UW152 t (b + 1), TM.Term.one)], zero) := by
  rw [wcnf_cons_ge (lt_UW_reg1_156 s (a + 2)), wcnf_UW156 t b]
  show (if (wA (reg 1) (UW152 s (a + 2)) == UW152 t (b + 1)) = true
        then ((wA (reg 1) (UW152 s (a + 2)),
               plus (wC (reg 1) (UW152 s (a + 2))) TM.Term.one) :: [], zero)
        else ((wA (reg 1) (UW152 s (a + 2)), wC (reg 1) (UW152 s (a + 2)))
              :: (UW152 t (b + 1), TM.Term.one) :: [], zero)) = _
  rw [wA_UW156 s a, wC_UW156 s a, if_neg (by rw [hne]; exact Bool.noConfusion)]

/-- **§155.5b の主定理の一般形 — 二桁の一段ぶんの門、種は両方とも任意。**
    `ksetStepOK_famB_sum155` の第二の種を famB の種から任意の種に広げたもの。
    高さが同じでも種が違えばよい (`hne`)。 -/
theorem stepOK_sumX156 (s t : Term) {a b : Nat}
    (hne : ((UW152 s (a + 1) : Term) == UW152 t (b + 1)) = false)
    (hle : le (UW152 t (b + 2)) (UW152 s (a + 2)) = true)
    (H1 : ∀ y ∈ Kset (reg 1) s, lt y (UW152 s (a + 2)) = true)
    (H1' : ∀ y ∈ Kset (reg 1) s,
      lt y (add (UW152 s (a + 2)) (UW152 t (b + 2))) = true)
    (H2' : ∀ y ∈ Kset (reg 1) t,
      lt y (add (UW152 s (a + 2)) (UW152 t (b + 2))) = true) :
    KsetStepOK 0 (add (UW152 s (a + 2)) (UW152 t (b + 2))) := by
  intro p hp hle2
  replace hp : p ∈ scanSt (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
      (wcnf (reg 1) [UW152 s (a + 2), UW152 t (b + 2)]).1 := hp
  rw [wcnf_sumX156 s t hne] at hp
  replace hp : p ∈ [(((none : Option Term), (none : Option Term)),
        (UW152 s (a + 1), TM.Term.one)),
      (stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (UW152 s (a + 1), TM.Term.one), (UW152 t (b + 1), TM.Term.one))] := hp
  rw [stepF_fire156 s a] at hp
  rcases List.mem_cons.mp hp with h1 | h1
  · subst h1
    constructor
    · intro i0 hi0
      have hi0x : (none : Option Term) = some i0 := hi0
      cases hi0x
    · intro y hy
      show lt y (idxOf (reg 1) ((none : Option Term), (none : Option Term))
        (UW152 s (a + 1), TM.Term.one)) = true
      rw [idx_UW156 s a]
      rcases hy with h | h
      · rw [show (((none : Option Term), (none : Option Term)),
            (UW152 s (a + 1), TM.Term.one)).2.1 = UW152 s (a + 1) from rfl,
          Kset_UW152 s (a + 1)] at h
        exact H1 y h
      · rw [show (((none : Option Term), (none : Option Term)),
            (UW152 s (a + 1), TM.Term.one)).2.2 = TM.Term.one from rfl] at h
        exact absurd h (by intro hc; cases hc)
  · replace h1 : p = ((some (UW152 s (a + 2)),
        some (psi (reg 1) (UW152 s (a + 2)))), (UW152 t (b + 1), TM.Term.one)) :=
      List.mem_singleton.mp h1
    subst h1
    constructor
    · intro i0 hi0 y hy
      have hi0e : i0 = UW152 s (a + 2) := by
        have hx : some (UW152 s (a + 2)) = some i0 := hi0
        injection hx with hx2
        exact hx2.symm
      subst hi0e
      rw [Kset_UW152 s (a + 2)] at hy
      show lt y (idxOf (reg 1) (some (UW152 s (a + 2)),
        some (psi (reg 1) (UW152 s (a + 2)))) (UW152 t (b + 1), TM.Term.one)) = true
      rw [idx2_156 t (UW152 s (a + 2)) _ b, plus_UW_UW156 hle]
      exact H1' y hy
    · intro y hy
      show lt y (idxOf (reg 1) (some (UW152 s (a + 2)),
        some (psi (reg 1) (UW152 s (a + 2)))) (UW152 t (b + 1), TM.Term.one)) = true
      rw [idx2_156 t (UW152 s (a + 2)) _ b, plus_UW_UW156 hle]
      rcases hy with h | h
      · rw [show ((some (UW152 s (a + 2)), some (psi (reg 1) (UW152 s (a + 2)))),
            (UW152 t (b + 1), TM.Term.one)).2.1 = UW152 t (b + 1) from rfl,
          Kset_UW152 t (b + 1)] at h
        exact H2' y h
      · rw [show ((some (UW152 s (a + 2)), some (psi (reg 1) (UW152 s (a + 2)))),
            (UW152 t (b + 1), TM.Term.one)).2.2 = TM.Term.one from rfl] at h
        exact absurd h (by intro hc; cases hc)

/-! ### §156.4 Mixed sums at the BT level, both orders

The low towers `ψ₁^p 0` (`p ≤ 3`) have their own small digits: `dict (ψ₁ 0) = Ω₁`
gives the digit `(1,1)`, `TW 1` gives `(1⊕1,1)` — neither fires — and `TW 2`
gives `(Ω₁,1)`, which FIRES and its obligations discharge against the
accumulated index `i₀ ⊕ 1`. -/

theorem wcnf_UW_Om156 (s : Term) (a : Nat) :
    wcnf (reg 1) [UW152 s (a + 2), Z zero]
      = ([(UW152 s (a + 1), TM.Term.one), (TM.Term.one, TM.Term.one)], zero) := by
  rw [wcnf_cons_ge (lt_UW_reg1_156 s (a + 2)),
    show wcnf (reg 1) [Z zero]
      = ([((TM.Term.one : Term), TM.Term.one)], zero) from by decide]
  show (if (wA (reg 1) (UW152 s (a + 2)) == TM.Term.one) = true
        then ((wA (reg 1) (UW152 s (a + 2)),
               plus (wC (reg 1) (UW152 s (a + 2))) TM.Term.one) :: [], zero)
        else ((wA (reg 1) (UW152 s (a + 2)), wC (reg 1) (UW152 s (a + 2)))
              :: (TM.Term.one, TM.Term.one) :: [], zero)) = _
  rw [wA_UW156 s a, wC_UW156 s a,
    if_neg (by rw [beq_UW_one152 s (a + 1)]; exact Bool.noConfusion)]

theorem wcnf_UW_TW1_156 (s : Term) (a : Nat) :
    wcnf (reg 1) [UW152 s (a + 2), TW 1]
      = ([(UW152 s (a + 1), TM.Term.one),
          (add TM.Term.one TM.Term.one, TM.Term.one)], zero) := by
  rw [wcnf_cons_ge (lt_UW_reg1_156 s (a + 2)),
    show wcnf (reg 1) [TW 1]
      = ([((add TM.Term.one TM.Term.one : Term), TM.Term.one)], zero) from by decide]
  show (if (wA (reg 1) (UW152 s (a + 2)) == add TM.Term.one TM.Term.one) = true
        then ((wA (reg 1) (UW152 s (a + 2)),
               plus (wC (reg 1) (UW152 s (a + 2))) TM.Term.one) :: [], zero)
        else ((wA (reg 1) (UW152 s (a + 2)), wC (reg 1) (UW152 s (a + 2)))
              :: (add TM.Term.one TM.Term.one, TM.Term.one) :: [], zero)) = _
  rw [wA_UW156 s a, wC_UW156 s a,
    if_neg (by intro hc; exact Bool.noConfusion hc)]

theorem wcnf_UW_TW2_156 (s : Term) (a : Nat) :
    wcnf (reg 1) [UW152 s (a + 2), TW 2]
      = ([(UW152 s (a + 1), TM.Term.one), (Z zero, TM.Term.one)], zero) := by
  rw [wcnf_cons_ge (lt_UW_reg1_156 s (a + 2)),
    show wcnf (reg 1) [TW 2]
      = ([((Z zero : Term), TM.Term.one)], zero) from by decide]
  show (if (wA (reg 1) (UW152 s (a + 2)) == Z zero) = true
        then ((wA (reg 1) (UW152 s (a + 2)),
               plus (wC (reg 1) (UW152 s (a + 2))) TM.Term.one) :: [], zero)
        else ((wA (reg 1) (UW152 s (a + 2)), wC (reg 1) (UW152 s (a + 2)))
              :: (Z zero, TM.Term.one) :: [], zero)) = _
  rw [wA_UW156 s a, wC_UW156 s a,
    if_neg (by rw [beq_UW_Om152 s (a + 1)]; exact Bool.noConfusion)]

/-- `(Ω₁, 1)` の桁の吐く指数 — 直前の指数に `1` を足すだけ。 -/
theorem idxOm156 (i0 : Term) (s2 : Option Term) :
    idxOf (reg 1) (some i0, s2) ((Z zero : Term), TM.Term.one)
      = plus i0 TM.Term.one := by
  show plus i0 (mulL (mulL (reg 1) (subAP (reg 1) (Z zero))) TM.Term.one) = _
  rw [show mulL (mulL (reg 1) (subAP (reg 1) (Z zero))) TM.Term.one
        = TM.Term.one from by decide]

/-- **一段ぶんの門、`famB ⊕ Ω₁` の形。**  第二の桁 `(1,1)` は発火しない。 -/
theorem stepOK_UW_Om156 (s : Term) (a : Nat)
    (H1 : ∀ y ∈ Kset (reg 1) s, lt y (UW152 s (a + 2)) = true) :
    KsetStepOK 0 (add (UW152 s (a + 2)) (Z zero)) := by
  intro p hp hle2
  replace hp : p ∈ scanSt (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
      (wcnf (reg 1) [UW152 s (a + 2), Z zero]).1 := hp
  rw [wcnf_UW_Om156 s a] at hp
  replace hp : p ∈ [(((none : Option Term), (none : Option Term)),
        (UW152 s (a + 1), TM.Term.one)),
      (stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (UW152 s (a + 1), TM.Term.one), ((TM.Term.one : Term), TM.Term.one))] := hp
  rcases List.mem_cons.mp hp with h1 | h1
  · subst h1
    constructor
    · intro i0 hi0
      have hi0x : (none : Option Term) = some i0 := hi0
      cases hi0x
    · intro y hy
      show lt y (idxOf (reg 1) ((none : Option Term), (none : Option Term))
        (UW152 s (a + 1), TM.Term.one)) = true
      rw [idx_UW156 s a]
      rcases hy with h | h
      · rw [show (((none : Option Term), (none : Option Term)),
            (UW152 s (a + 1), TM.Term.one)).2.1 = UW152 s (a + 1) from rfl,
          Kset_UW152 s (a + 1)] at h
        exact H1 y h
      · rw [show (((none : Option Term), (none : Option Term)),
            (UW152 s (a + 1), TM.Term.one)).2.2 = TM.Term.one from rfl] at h
        exact absurd h (by intro hc; cases hc)
  · replace h1 : p = (stepF (reg 1) (baseOf 0)
        ((none : Option Term), (none : Option Term)) (UW152 s (a + 1), TM.Term.one),
        ((TM.Term.one : Term), TM.Term.one)) := List.mem_singleton.mp h1
    subst h1
    have hle3 : le (reg 1) TM.Term.one = true := hle2
    exact absurd hle3 (by decide)

/-- **一段ぶんの門、`famB ⊕ TW 1` の形。**  第二の桁 `(1⊕1,1)` は発火しない。 -/
theorem stepOK_UW_TW1_156 (s : Term) (a : Nat)
    (H1 : ∀ y ∈ Kset (reg 1) s, lt y (UW152 s (a + 2)) = true) :
    KsetStepOK 0 (add (UW152 s (a + 2)) (TW 1)) := by
  intro p hp hle2
  replace hp : p ∈ scanSt (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
      (wcnf (reg 1) [UW152 s (a + 2), TW 1]).1 := hp
  rw [wcnf_UW_TW1_156 s a] at hp
  replace hp : p ∈ [(((none : Option Term), (none : Option Term)),
        (UW152 s (a + 1), TM.Term.one)),
      (stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (UW152 s (a + 1), TM.Term.one),
       ((add TM.Term.one TM.Term.one : Term), TM.Term.one))] := hp
  rcases List.mem_cons.mp hp with h1 | h1
  · subst h1
    constructor
    · intro i0 hi0
      have hi0x : (none : Option Term) = some i0 := hi0
      cases hi0x
    · intro y hy
      show lt y (idxOf (reg 1) ((none : Option Term), (none : Option Term))
        (UW152 s (a + 1), TM.Term.one)) = true
      rw [idx_UW156 s a]
      rcases hy with h | h
      · rw [show (((none : Option Term), (none : Option Term)),
            (UW152 s (a + 1), TM.Term.one)).2.1 = UW152 s (a + 1) from rfl,
          Kset_UW152 s (a + 1)] at h
        exact H1 y h
      · rw [show (((none : Option Term), (none : Option Term)),
            (UW152 s (a + 1), TM.Term.one)).2.2 = TM.Term.one from rfl] at h
        exact absurd h (by intro hc; cases hc)
  · replace h1 : p = (stepF (reg 1) (baseOf 0)
        ((none : Option Term), (none : Option Term)) (UW152 s (a + 1), TM.Term.one),
        ((add TM.Term.one TM.Term.one : Term), TM.Term.one)) := List.mem_singleton.mp h1
    subst h1
    have hle3 : le (reg 1) (add TM.Term.one TM.Term.one) = true := hle2
    exact absurd hle3 (by decide)

/-- **一段ぶんの門、`famB ⊕ TW 2` の形。**  第二の桁 `(Ω₁,1)` は発火し、
    義務は直前の指数 `i₀ ⊕ 1` に対して済む。 -/
theorem stepOK_UW_TW2_156 (s : Term) (a : Nat)
    (H1 : ∀ y ∈ Kset (reg 1) s, lt y (UW152 s (a + 2)) = true)
    (H2 : ∀ y ∈ Kset (reg 1) s, lt y (add (UW152 s (a + 2)) TM.Term.one) = true) :
    KsetStepOK 0 (add (UW152 s (a + 2)) (TW 2)) := by
  intro p hp hle2
  replace hp : p ∈ scanSt (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
      (wcnf (reg 1) [UW152 s (a + 2), TW 2]).1 := hp
  rw [wcnf_UW_TW2_156 s a] at hp
  replace hp : p ∈ [(((none : Option Term), (none : Option Term)),
        (UW152 s (a + 1), TM.Term.one)),
      (stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (UW152 s (a + 1), TM.Term.one), ((Z zero : Term), TM.Term.one))] := hp
  rw [stepF_fire156 s a] at hp
  rcases List.mem_cons.mp hp with h1 | h1
  · subst h1
    constructor
    · intro i0 hi0
      have hi0x : (none : Option Term) = some i0 := hi0
      cases hi0x
    · intro y hy
      show lt y (idxOf (reg 1) ((none : Option Term), (none : Option Term))
        (UW152 s (a + 1), TM.Term.one)) = true
      rw [idx_UW156 s a]
      rcases hy with h | h
      · rw [show (((none : Option Term), (none : Option Term)),
            (UW152 s (a + 1), TM.Term.one)).2.1 = UW152 s (a + 1) from rfl,
          Kset_UW152 s (a + 1)] at h
        exact H1 y h
      · rw [show (((none : Option Term), (none : Option Term)),
            (UW152 s (a + 1), TM.Term.one)).2.2 = TM.Term.one from rfl] at h
        exact absurd h (by intro hc; cases hc)
  · replace h1 : p = ((some (UW152 s (a + 2)),
        some (psi (reg 1) (UW152 s (a + 2)))), ((Z zero : Term), TM.Term.one)) :=
      List.mem_singleton.mp h1
    subst h1
    constructor
    · intro i0 hi0 y hy
      have hi0e : i0 = UW152 s (a + 2) := by
        have hx : some (UW152 s (a + 2)) = some i0 := hi0
        injection hx with hx2
        exact hx2.symm
      subst hi0e
      rw [Kset_UW152 s (a + 2)] at hy
      show lt y (idxOf (reg 1) (some (UW152 s (a + 2)),
        some (psi (reg 1) (UW152 s (a + 2)))) ((Z zero : Term), TM.Term.one)) = true
      rw [idxOm156 (UW152 s (a + 2)) _, plus_UW_one156 s (a + 2)]
      exact H2 y hy
    · intro y hy
      rcases hy with h | h
      · rw [show ((some (UW152 s (a + 2)), some (psi (reg 1) (UW152 s (a + 2)))),
            ((Z zero : Term), TM.Term.one)).2.1 = Z zero from rfl] at h
        exact absurd h (by intro hc; cases hc)
      · rw [show ((some (UW152 s (a + 2)), some (psi (reg 1) (UW152 s (a + 2)))),
            ((Z zero : Term), TM.Term.one)).2.2 = TM.Term.one from rfl] at h
        exact absurd h (by intro hc; cases hc)

/-- 種の `K` の元は種の塔より下 (`K` の元の高さ以上の高さで)。famB152 の義務の共通形。 -/
theorem Ksd_lt_UW156 (kk : Nat) (t : Term) (c : Nat) (hc : kk + 2 ≤ c) :
    ∀ y ∈ Kset (reg 1) (sd152 (kk + 3)), lt y (UW152 t c) = true := by
  intro y hy
  cases kk with
  | zero =>
      rw [Kset_sd3_152] at hy
      rw [List.mem_singleton.mp hy]
      exact lt_zero_left (ne_zero_UW152 _ _)
  | succ jp =>
      rw [show jp + 1 + 3 = jp + 4 from rfl, Kset_sd_psi152 jp] at hy
      rw [List.mem_singleton.mp hy]
      exact lt_TW_UW152 _ (jp + 3) c (by omega)

/-- 種の `K` の元は、頭が塔の和よりも下。 -/
theorem Ksd_lt_add156 (kk : Nat) (t : Term) (c : Nat) (hc : kk + 2 ≤ c) (R : Term) :
    ∀ y ∈ Kset (reg 1) (sd152 (kk + 3)), lt y (add (UW152 t c) R) = true := by
  intro y hy
  cases kk with
  | zero =>
      rw [Kset_sd3_152] at hy
      rw [List.mem_singleton.mp hy]
      exact lt_zero_left (by intro hc2; exact Term.noConfusion hc2)
  | succ jp =>
      rw [show jp + 1 + 3 = jp + 4 from rfl, Kset_sd_psi152 jp] at hy
      rw [List.mem_singleton.mp hy]
      rw [lt_nsum_add100 (show (TW (jp + 3) : Term) ≠ zero from by
            intro hc2; exact Term.noConfusion hc2) rfl]
      exact le_of_lt (lt_TW_UW152 _ (jp + 3) c (by omega))

/-- 同じく、頭が `Ω₁` の種の塔 (= `TW`) の和 — 等しい高さも `le` で許す。 -/
theorem Ksd_le_addTW156 (kk : Nat) (c : Nat) (hc : kk + 2 ≤ c + 1) (R : Term) :
    ∀ y ∈ Kset (reg 1) (sd152 (kk + 3)),
      lt y (add (UW152 (Z zero) c) R) = true := by
  intro y hy
  cases kk with
  | zero =>
      rw [Kset_sd3_152] at hy
      rw [List.mem_singleton.mp hy]
      exact lt_zero_left (by intro hc2; exact Term.noConfusion hc2)
  | succ jp =>
      rw [show jp + 1 + 3 = jp + 4 from rfl, Kset_sd_psi152 jp] at hy
      rw [List.mem_singleton.mp hy]
      rw [lt_nsum_add100 (show (TW (jp + 3) : Term) ≠ zero from by
            intro hc2; exact Term.noConfusion hc2) rfl,
        ← TW_UW156 c]
      exact le_TW_TW156 (by omega) (by omega)

/-- **主定理 1 — `famB m k ⊕ ψ₁^p 0` は `3 ≤ k ≤ m`、`1 ≤ p ≤ m` の全域で
    第一の門の一歩を満たす。**  §132.5 の測定した resid の範囲そのもの。 -/
theorem ksetStepOK_famB_tow156 {m k p : Nat} (h3 : 3 ≤ k) (hkm : k ≤ m)
    (h1p : 1 ≤ p) (hpm : p ≤ m) :
    KsetStepOK 0 (dict (BT.sum (famB132 m k) (nst132 p BT.zero))) := by
  obtain ⟨kk, rfl⟩ : ∃ kk, k = kk + 3 := ⟨k - 3, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, m = (kk + d) + 3 := ⟨m - (kk + 3), by omega⟩
  rw [Trans.Dict.dict_sum, show kk + d + 3 = (kk + d + 2) + 1 from rfl,
    dict_famB152 kk (kk + d + 2)]
  cases p with
  | zero => exact absurd h1p (by omega)
  | succ p0 =>
    cases p0 with
    | zero =>
        rw [show dict (nst132 1 BT.zero) = Z zero from by decide,
          plus_UW_Om156 (sd152 (kk + 3)) (kk + d + 2)]
        exact stepOK_UW_Om156 _ (kk + d) (Ksd_lt_UW156 kk _ (kk + d + 2) (by omega))
    | succ p1 =>
      cases p1 with
      | zero =>
          rw [show dict (nst132 2 BT.zero) = TW 1 from dict_bT152 0,
            plus_UW_TW156 (c := 0)
              (le_of_lt (lt_TW_UW152 (sd152 (kk + 3)) 1 (kk + d + 2) (by omega)))]
          exact stepOK_UW_TW1_156 _ (kk + d) (Ksd_lt_UW156 kk _ (kk + d + 2) (by omega))
      | succ p2 =>
        cases p2 with
        | zero =>
            rw [show dict (nst132 3 BT.zero) = TW 2 from dict_bT152 1,
              plus_UW_TW156 (c := 1)
                (le_of_lt (lt_TW_UW152 (sd152 (kk + 3)) 2 (kk + d + 2) (by omega)))]
            exact stepOK_UW_TW2_156 _ (kk + d)
              (Ksd_lt_UW156 kk _ (kk + d + 2) (by omega))
              (Ksd_lt_add156 kk _ (kk + d + 2) (by omega) TM.Term.one)
        | succ p3 =>
            -- p = p3 + 4 ≤ m
            have hOrd : le (UW152 (Z zero) (p3 + 2))
                (UW152 (sd152 (kk + 3)) (kk + d + 2)) = true :=
              le_of_lt (lt_UW_UW_lt155 (Z zero) (sd152 (kk + 3)) (p3 + 2) (kk + d + 2)
                (by omega))
            rw [show dict (nst132 (p3 + 4) BT.zero) = TW (p3 + 3) from dict_bT152 (p3 + 2),
              show (TW (p3 + 3) : Term) = UW152 (Z zero) (p3 + 2) from TW_UW156 (p3 + 2),
              plus_UW_UW156 hOrd]
            refine stepOK_sumX156 (sd152 (kk + 3)) (Z zero)
              (beq_UW_ne155' _ _ (show p3 + 1 < kk + d + 1 by omega)) hOrd
              (Ksd_lt_UW156 kk _ (kk + d + 2) (by omega))
              (Ksd_lt_add156 kk _ (kk + d + 2) (by omega) _) ?_
            intro y hy
            cases hy

/-- **主定理 2 — `ψ₁^p 0 ⊕ famB m k` は `3 ≤ k`、`3 ≤ m < p`、`k ≤ p` の全域で
    第一の門の一歩を満たす。**  famB の側は単独では標準でない `k > m` も含む —
    逃げる元 `TW (k-1)` は頭の塔の積んだ指数に対して済む。 -/
theorem ksetStepOK_tow_famB156 {p m k : Nat} (h3k : 3 ≤ k) (h3m : 3 ≤ m)
    (hmp : m < p) (hkp : k ≤ p) :
    KsetStepOK 0 (dict (BT.sum (nst132 p BT.zero) (famB132 m k))) := by
  obtain ⟨kk, rfl⟩ : ∃ kk, k = kk + 3 := ⟨k - 3, by omega⟩
  obtain ⟨mm, rfl⟩ : ∃ mm, m = mm + 3 := ⟨m - 3, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, p = (mm + e) + 4 := ⟨p - (mm + 4), by omega⟩
  have hle2 : le (UW152 (sd152 (kk + 3)) (mm + 2))
      (UW152 (Z zero) (mm + e + 2)) = true := by
    cases e with
    | zero =>
        refine le_of_lt ?_
        show lt (UW152 (sd152 (kk + 3)) (mm + 2)) (UW152 (Z zero) (mm + 2)) = true
        rw [lt_UW_UW_same155]
        exact (sd_facts152 kk).2.2.1
    | succ e' =>
        exact le_of_lt (lt_UW_UW_lt155 _ _ _ _ (by omega))
  have hne : ((UW152 (Z zero) (mm + e + 1) : Term)
      == UW152 (sd152 (kk + 3)) (mm + 1)) = false := by
    cases e with
    | zero =>
        show ((UW152 (Z zero) (mm + 1) : Term)
          == UW152 (sd152 (kk + 3)) (mm + 1)) = false
        refine beq_UW_seed156 ?_ (mm + 1)
        obtain ⟨X, hX⟩ := sd_psi_form155 kk
        rw [hX]
        intro hc
        exact Term.noConfusion hc
    | succ e' =>
        exact beq_UW_ne155' _ _ (show mm + 1 < mm + (e' + 1) + 1 by omega)
  rw [Trans.Dict.dict_sum, show mm + 3 = (mm + 2) + 1 from rfl,
    dict_famB152 kk (mm + 2),
    show dict (nst132 ((mm + e) + 4) BT.zero) = TW ((mm + e) + 3) from
      dict_bT152 ((mm + e) + 2),
    show (TW ((mm + e) + 3) : Term) = UW152 (Z zero) ((mm + e) + 2) from
      TW_UW156 ((mm + e) + 2),
    plus_UW_UW156 hle2]
  refine stepOK_sumX156 (Z zero) (sd152 (kk + 3)) hne hle2 ?_ ?_ ?_
  · intro y hy
    cases hy
  · intro y hy
    cases hy
  · exact Ksd_le_addTW156 kk (mm + e + 2) (by omega) _

/-! 一項ぶんの門と最初の発火の義務、混合の和の族の上で。 -/

theorem gateStd87_famB_tow156 (m k p : Nat) (h3 : 3 ≤ k) (hkm : k ≤ m)
    (h1p : 1 ≤ p) (hpm : p ≤ m) :
    GateStd87 (BT.sum (famB132 m k) (nst132 p BT.zero)) :=
  fun _ _ => ksetStepOK_famB_tow156 h3 hkm h1p hpm

theorem gateStd87_tow_famB156 (p m k : Nat) (h3k : 3 ≤ k) (h3m : 3 ≤ m)
    (hmp : m < p) (hkp : k ≤ p) :
    GateStd87 (BT.sum (nst132 p BT.zero) (famB132 m k)) :=
  fun _ _ => ksetStepOK_tow_famB156 h3k h3m hmp hkp

theorem firstFire_famB_tow156 (m k p : Nat) (h3 : 3 ≤ k) (hkm : k ≤ m)
    (h1p : 1 ≤ p) (hpm : p ≤ m) :
    FirstFire145 (BT.sum (famB132 m k) (nst132 p BT.zero)) :=
  fun q hq _ hle y hy => (ksetStepOK_famB_tow156 h3 hkm h1p hpm q hq hle).2 y hy

theorem firstFire_tow_famB156 (p m k : Nat) (h3k : 3 ≤ k) (h3m : 3 ≤ m)
    (hmp : m < p) (hkp : k ≤ p) :
    FirstFire145 (BT.sum (nst132 p BT.zero) (famB132 m k)) :=
  fun q hq _ hle y hy => (ksetStepOK_tow_famB156 h3k h3m hmp hkp q hq hle).2 y hy

/-! ### §156.5a `collapse 0` of the tower sums — the seed values of the sum-seed family -/

theorem wcnf_sum2_156 (s : Term) (j : Nat) :
    wcnf (reg 1) [UW152 s (j + 2), UW152 s (j + 2)]
      = ([(UW152 s (j + 1), add TM.Term.one TM.Term.one)], zero) := by
  rw [wcnf_cons_ge (lt_UW_reg1_156 s (j + 2)), wcnf_UW156 s j]
  show (if (wA (reg 1) (UW152 s (j + 2)) == UW152 s (j + 1)) = true
        then ((wA (reg 1) (UW152 s (j + 2)),
               plus (wC (reg 1) (UW152 s (j + 2))) TM.Term.one) :: [], zero)
        else ((wA (reg 1) (UW152 s (j + 2)), wC (reg 1) (UW152 s (j + 2)))
              :: (UW152 s (j + 1), TM.Term.one) :: [], zero)) = _
  rw [wA_UW156 s j, wC_UW156 s j, if_pos (beq_self_eq_true _),
    show plus TM.Term.one TM.Term.one = add TM.Term.one TM.Term.one from rfl]

theorem idx_sum2_156 (s : Term) (j : Nat) :
    idxOf (reg 1) ((none : Option Term), (none : Option Term))
        (UW152 s (j + 1), add TM.Term.one TM.Term.one)
      = add (UW152 s (j + 2)) (UW152 s (j + 2)) := by
  show sub1 (mulL (mulL (reg 1) (subAP (reg 1) (UW152 s (j + 1))))
    (add TM.Term.one TM.Term.one)) = _
  rw [subAP_UW152 s (j + 1), mulL_Om1_UW156 s j]
  show sub1 (ofList [omegaNF (plus (UW152 s (j + 1)) (logOm TM.Term.one)),
                     omegaNF (plus (UW152 s (j + 1)) (logOm TM.Term.one))]) = _
  rw [show logOm TM.Term.one = zero from rfl,
    show plus (UW152 s (j + 1)) zero = UW152 s (j + 1) from rfl,
    omegaNF_UW152 s (j + 1)]
  show (if ((UW152 s (j + 2) : Term) == TM.Term.one) = true
        then ofList (toList (UW152 s (j + 2)))
        else add (UW152 s (j + 2)) (UW152 s (j + 2))) = _
  rw [if_neg (by rw [beq_UW_one152 s (j + 2)]; exact Bool.noConfusion)]

theorem stepF_fire2_156 (s : Term) (j : Nat) :
    stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (UW152 s (j + 1), add TM.Term.one TM.Term.one)
      = (some (add (UW152 s (j + 2)) (UW152 s (j + 2))),
         some (psi (reg 1) (add (UW152 s (j + 2)) (UW152 s (j + 2))))) := by
  show (if le (reg 1) (UW152 s (j + 1)) = true
        then (some (idxOf (reg 1) ((none : Option Term), (none : Option Term))
                (UW152 s (j + 1), add TM.Term.one TM.Term.one)),
              some (psi (reg 1) (idxOf (reg 1) ((none : Option Term), (none : Option Term))
                (UW152 s (j + 1), add TM.Term.one TM.Term.one))))
        else ((none : Option Term),
              some (phiNF (UW152 s (j + 1))
                (plus (baseOf 0) (sub1 (add TM.Term.one TM.Term.one)))))) = _
  rw [if_pos (le_reg1_UW152 s (j + 1)), idx_sum2_156 s j]

/-- **併合の側 — 等しい塔の和の `ψ₀` は `ψ_{Ω₁}(和)` そのもの。** -/
theorem collapse0_sum2_156 (s : Term) (j : Nat) :
    collapse 0 (add (UW152 s (j + 2)) (UW152 s (j + 2)))
      = psi (Z zero) (add (UW152 s (j + 2)) (UW152 s (j + 2))) := by
  rw [collapse_eq,
    show toList (add (UW152 s (j + 2)) (UW152 s (j + 2)))
      = [UW152 s (j + 2), UW152 s (j + 2)] from rfl,
    wcnf_sum2_156 s j]
  show omegaNF (plus (reg 0) (plus
    ((stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (UW152 s (j + 1), add TM.Term.one TM.Term.one)).2.getD zero) zero)) = _
  rw [stepF_fire2_156 s j]
  exact omegaNF_psi139 _ _

/-- **二桁の側 — 順に発火し、指数が積もる。** `ψ₀(塔 ⊕ 塔) = ψ_{Ω₁}(塔 ⊕ 塔)`。 -/
theorem collapse0_sumX156 (s t : Term) {a b : Nat}
    (hne : ((UW152 s (a + 1) : Term) == UW152 t (b + 1)) = false)
    (hle : le (UW152 t (b + 2)) (UW152 s (a + 2)) = true) :
    collapse 0 (add (UW152 s (a + 2)) (UW152 t (b + 2)))
      = psi (Z zero) (add (UW152 s (a + 2)) (UW152 t (b + 2))) := by
  rw [collapse_eq,
    show toList (add (UW152 s (a + 2)) (UW152 t (b + 2)))
      = [UW152 s (a + 2), UW152 t (b + 2)] from rfl,
    wcnf_sumX156 s t hne]
  show omegaNF (plus (reg 0) (plus
    ((stepF (reg 1) (baseOf 0)
        (stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
          (UW152 s (a + 1), TM.Term.one))
        (UW152 t (b + 1), TM.Term.one)).2.getD zero) zero)) = _
  rw [stepF_fire156 s a,
    show stepF (reg 1) (baseOf 0)
        (some (UW152 s (a + 2)), some (psi (reg 1) (UW152 s (a + 2))))
        (UW152 t (b + 1), TM.Term.one)
      = (some (add (UW152 s (a + 2)) (UW152 t (b + 2))),
         some (psi (reg 1) (add (UW152 s (a + 2)) (UW152 t (b + 2))))) from by
      show (if le (reg 1) (UW152 t (b + 1)) = true
            then (some (idxOf (reg 1) (some (UW152 s (a + 2)),
                    some (psi (reg 1) (UW152 s (a + 2))))
                    (UW152 t (b + 1), TM.Term.one)),
                  some (psi (reg 1) (idxOf (reg 1) (some (UW152 s (a + 2)),
                    some (psi (reg 1) (UW152 s (a + 2))))
                    (UW152 t (b + 1), TM.Term.one))))
            else (some (UW152 s (a + 2)),
                  some (phiNF (UW152 t (b + 1))
                    (plus (psi (reg 1) (UW152 s (a + 2))) TM.Term.one)))) = _
      rw [if_pos (le_reg1_UW152 t (b + 1)), idx2_156 t (UW152 s (a + 2)) _ b,
        plus_UW_UW156 hle]]
  exact omegaNF_psi139 _ _

/-! 発火しない桁の一歩と、その `φ̄` の正規形。 -/

theorem stepF_nofire156 {A : Term} (hA : le (reg 1) A = false)
    (i0 v C : Term) :
    stepF (reg 1) (baseOf 0) (some i0, some v) (A, C)
      = (some i0, some (phiNF A (plus v C))) := by
  show (if le (reg 1) A = true
        then (some (idxOf (reg 1) (some i0, some v) (A, C)),
              some (psi (reg 1) (idxOf (reg 1) (some i0, some v) (A, C))))
        else (some i0, some (phiNF A (plus v C)))) = _
  rw [if_neg (by rw [hA]; exact Bool.noConfusion)]

theorem lt_one_psi156 (k c : Term) : lt TM.Term.one (psi k c) = true := by
  show lt (phi zero zero) (psi k c) = true
  rw [lt_phi_psi103, lt_zero_left (show (psi k c : Term) ≠ zero from by
    intro hc; exact Term.noConfusion hc)]
  rfl

theorem lt_two_psi156 (k c : Term) :
    lt (add TM.Term.one TM.Term.one) (psi k c) = true := by
  rw [lt_add_nsum (show (psi k c : Term) ≠ zero from by
        intro hc; exact Term.noConfusion hc) rfl]
  exact lt_one_psi156 k c

theorem plus_psi_one156 (k c : Term) :
    plus (psi k c) TM.Term.one = add (psi k c) TM.Term.one := by
  rw [plus_cons66 (show toList (TM.Term.one : Term) = [TM.Term.one] from rfl),
    show toList (psi k c) = [psi k c] from rfl,
    List.filter_cons_of_pos (by
      show ((TM.Term.one == psi k c) || lt TM.Term.one (psi k c)) = true
      rw [lt_one_psi156 k c]
      exact Bool.or_true _)]
  rfl

/-- `φ̄ a (ψ ⊕ 1)` は一段降りて `φ̄ a ψ` — `ψ` は `a`-不動点の形なので。 -/
theorem phiNF_add_psi_one156 (a k c : Term) (h : lt a (psi k c) = true) :
    phiNF a (add (psi k c) TM.Term.one) = phi a (psi k c) := by
  show (if ((add (psi k c) TM.Term.one).isSC
          && lt a (add (psi k c) TM.Term.one)) = true
        then add (psi k c) TM.Term.one
        else phiNFsucc a (add (psi k c) TM.Term.one)) = _
  rw [if_neg (by intro hc; exact Bool.noConfusion hc)]
  show (if lt a (psi k c) = true
        then phi a (psi k c)
        else phiNFdefault a (add (psi k c) TM.Term.one)) = _
  rw [if_pos h]

/-- `ω^(φ̄ c b) = φ̄ c b` — 第 1 引数が `0` より上なら `ω`-不動点。 -/
theorem omegaNF_phiC156 {c : Term} (hzc : lt zero c = true) (b : Term) :
    omegaNF (phi c b) = phi c b := by
  show (if lt M (phi c b) = true then omg (phi c b)
        else if ((phi c b : Term) == M) = true then M
        else phiNF zero (phi c b)) = _
  rw [if_neg (by
        rw [show lt M (phi c b) = false from by
          show ltF (fuelOf M (phi c b)) M (phi c b) = false
          exact ltF_M_phi135 c b _]
        exact Bool.noConfusion),
    if_neg (show ¬(((phi c b : Term) == M) = true) from by
        intro hc; exact Bool.noConfusion hc)]
  show (if ((phi c b).isSC && lt zero (phi c b)) = true then phi c b
        else if lt zero c = true then phi c b
        else phiNFsucc zero (phi c b)) = _
  rw [if_neg (by intro hc; exact Bool.noConfusion hc), if_pos hzc]

/-- **`j = 3` の側 — `ψ₀(塔 ⊕ TW 2) = ψ_{Ω₁}(塔 ⊕ 1)`。**  `(Ω₁,1)` の桁が発火し、
    指数は `1` だけ積む。 -/
theorem collapse0_UW_TW2_156 (s : Term) (a : Nat) :
    collapse 0 (add (UW152 s (a + 2)) (TW 2))
      = psi (Z zero) (add (UW152 s (a + 2)) TM.Term.one) := by
  rw [collapse_eq,
    show toList (add (UW152 s (a + 2)) (TW 2)) = [UW152 s (a + 2), TW 2] from rfl,
    wcnf_UW_TW2_156 s a]
  show omegaNF (plus (reg 0) (plus
    ((stepF (reg 1) (baseOf 0)
        (stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
          (UW152 s (a + 1), TM.Term.one))
        ((Z zero : Term), TM.Term.one)).2.getD zero) zero)) = _
  rw [stepF_fire156 s a,
    show stepF (reg 1) (baseOf 0)
        (some (UW152 s (a + 2)), some (psi (reg 1) (UW152 s (a + 2))))
        ((Z zero : Term), TM.Term.one)
      = (some (add (UW152 s (a + 2)) TM.Term.one),
         some (psi (reg 1) (add (UW152 s (a + 2)) TM.Term.one))) from by
      show (if le (reg 1) (Z zero) = true
            then (some (idxOf (reg 1) (some (UW152 s (a + 2)),
                    some (psi (reg 1) (UW152 s (a + 2))))
                    ((Z zero : Term), TM.Term.one)),
                  some (psi (reg 1) (idxOf (reg 1) (some (UW152 s (a + 2)),
                    some (psi (reg 1) (UW152 s (a + 2))))
                    ((Z zero : Term), TM.Term.one))))
            else (some (UW152 s (a + 2)),
                  some (phiNF (Z zero)
                    (plus (psi (reg 1) (UW152 s (a + 2))) TM.Term.one)))) = _
      rw [if_pos (show le (reg 1) (Z zero) = true from by decide),
        idxOm156 (UW152 s (a + 2)) _, plus_UW_one156 s (a + 2)]]
  exact omegaNF_psi139 _ _

/-- **`j = 2` の側 — `ψ₀(塔 ⊕ TW 1) = φ̄(2, ψ_{Ω₁}(塔))`。**  `(1⊕1,1)` は発火せず、
    `φ̄` の枝が動く。 -/
theorem collapse0_UW_TW1_156 (s : Term) (a : Nat) :
    collapse 0 (add (UW152 s (a + 2)) (TW 1))
      = phi (add TM.Term.one TM.Term.one) (psi (Z zero) (UW152 s (a + 2))) := by
  rw [collapse_eq,
    show toList (add (UW152 s (a + 2)) (TW 1)) = [UW152 s (a + 2), TW 1] from rfl,
    wcnf_UW_TW1_156 s a]
  show omegaNF (plus (reg 0) (plus
    ((stepF (reg 1) (baseOf 0)
        (stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
          (UW152 s (a + 1), TM.Term.one))
        ((add TM.Term.one TM.Term.one : Term), TM.Term.one)).2.getD zero) zero)) = _
  rw [stepF_fire156 s a,
    stepF_nofire156 (A := add TM.Term.one TM.Term.one) (by decide)
      (UW152 s (a + 2)) (psi (reg 1) (UW152 s (a + 2))) TM.Term.one,
    plus_psi_one156 (reg 1) (UW152 s (a + 2)),
    phiNF_add_psi_one156 (add TM.Term.one TM.Term.one) (reg 1) (UW152 s (a + 2))
      (lt_two_psi156 (reg 1) (UW152 s (a + 2)))]
  exact omegaNF_phiC156
    (lt_zero_left (by intro hc; exact Term.noConfusion hc)) _

/-- **`j = 1` の側 — `ψ₀(塔 ⊕ Ω₁) = φ̄(1, ψ_{Ω₁}(塔))`。**  `(1,1)` は発火しない。 -/
theorem collapse0_UW_Om156 (s : Term) (a : Nat) :
    collapse 0 (add (UW152 s (a + 2)) (Z zero))
      = phi TM.Term.one (psi (Z zero) (UW152 s (a + 2))) := by
  rw [collapse_eq,
    show toList (add (UW152 s (a + 2)) (Z zero)) = [UW152 s (a + 2), Z zero] from rfl,
    wcnf_UW_Om156 s a]
  show omegaNF (plus (reg 0) (plus
    ((stepF (reg 1) (baseOf 0)
        (stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
          (UW152 s (a + 1), TM.Term.one))
        ((TM.Term.one : Term), TM.Term.one)).2.getD zero) zero)) = _
  rw [stepF_fire156 s a,
    stepF_nofire156 (A := TM.Term.one) (by decide)
      (UW152 s (a + 2)) (psi (reg 1) (UW152 s (a + 2))) TM.Term.one,
    plus_psi_one156 (reg 1) (UW152 s (a + 2)),
    phiNF_add_psi_one156 TM.Term.one (reg 1) (UW152 s (a + 2))
      (lt_one_psi156 (reg 1) (UW152 s (a + 2)))]
  exact omegaNF_phiC156
    (lt_zero_left (by intro hc; exact Term.noConfusion hc)) _

/-! ### §156.5b The sum-seed family: dict closed forms and the gate -/

/-- 和の種の族。`famD156 m k j = ψ₁^m(ψ₀(ψ₁^k 0 ⊕ ψ₁^j 0))` — famPool132 の第六の族。 -/
def famD156 (m k j : Nat) : BT :=
  nst132 m (BT.D 0 (BT.sum (nst132 k BT.zero) (nst132 j BT.zero)))

theorem lt_psiOm_reg2_156 (A : Term) : lt (psi (Z zero) A) (reg 2) = true := by
  show lt (psi (Z zero) A) (Z TM.Term.one) = true
  exact lt_psiOm_Om2_139 A

theorem lt_phiPsi_reg1_156 {c : Term} (hc : lt c (reg 1) = true) (X : Term) :
    lt (phi c (psi (Z zero) X)) (reg 1) = true := by
  rw [lt_phi_reg1_100, hc, lt_psiOm_reg1_139 X]
  rfl

theorem lt_phiPsi_reg2_156 {c : Term} (hc : lt c (Z TM.Term.one) = true) (X : Term) :
    lt (phi c (psi (Z zero) X)) (reg 2) = true := by
  show lt (phi c (psi (Z zero) X)) (Z TM.Term.one) = true
  rw [lt_phi_Z103, hc, lt_psiOm_Om2_139 X]
  rfl

/-- 種 `S < Ω₁` の上の `ψ₁` の塔 — `dict (ψ₁^{m+1} W) = UW152 S m`、`dict W = S` なら。 -/
theorem dict_nstD0_156 {S : Term} (hap : S.isAP = true)
    (hone : ((S : Term) == TM.Term.one) = false)
    (hlt : lt S (reg 1) = true) (hlt2 : lt S (reg 2) = true)
    {W : BT} (hW : dict W = S) : ∀ m : Nat, dict (nst132 (m + 1) W) = UW152 S m
  | 0 => by
      show collapse 1 (dict (nst132 0 W)) = _
      show collapse 1 (dict W) = _
      rw [hW]
      exact collapse1_seed152 hap hone hlt hlt2
  | m + 1 => by
      show collapse 1 (dict (nst132 (m + 1) W)) = _
      rw [dict_nstD0_156 hap hone hlt hlt2 hW m]
      exact collapse1_UW152 hlt m

/-! 種の値 — 五つの領域の閉じた形。`4 ≤ j < k`、`j = k`、`j = 3`、`j = 2`、`j = 1`、
    そして `k = 3` の三つの具象。 -/

theorem dictD0_sum_lt156 (kk jj : Nat) (hjk : jj < kk) :
    dict (BT.D 0 (BT.sum (nst132 (kk + 4) BT.zero) (nst132 (jj + 4) BT.zero)))
      = psi (Z zero) (add (UW152 (Z zero) (kk + 2)) (UW152 (Z zero) (jj + 2))) := by
  rw [Trans.Dict.dict_D, Trans.Dict.dict_sum,
    show dict (nst132 (kk + 4) BT.zero) = TW (kk + 3) from dict_bT152 (kk + 2),
    show dict (nst132 (jj + 4) BT.zero) = TW (jj + 3) from dict_bT152 (jj + 2),
    show (TW (kk + 3) : Term) = UW152 (Z zero) (kk + 2) from TW_UW156 (kk + 2),
    show (TW (jj + 3) : Term) = UW152 (Z zero) (jj + 2) from TW_UW156 (jj + 2),
    plus_UW_UW156 (le_of_lt (lt_UW_UW_lt155 (Z zero) (Z zero) (jj + 2) (kk + 2)
      (by omega)))]
  exact collapse0_sumX156 (Z zero) (Z zero)
    (beq_UW_ne155' _ _ (show jj + 1 < kk + 1 by omega))
    (le_of_lt (lt_UW_UW_lt155 _ _ _ _ (by omega)))

theorem dictD0_sum_eq156 (kk : Nat) :
    dict (BT.D 0 (BT.sum (nst132 (kk + 4) BT.zero) (nst132 (kk + 4) BT.zero)))
      = psi (Z zero) (add (UW152 (Z zero) (kk + 2)) (UW152 (Z zero) (kk + 2))) := by
  rw [Trans.Dict.dict_D, Trans.Dict.dict_sum,
    show dict (nst132 (kk + 4) BT.zero) = TW (kk + 3) from dict_bT152 (kk + 2),
    show (TW (kk + 3) : Term) = UW152 (Z zero) (kk + 2) from TW_UW156 (kk + 2),
    plus_UW_UW156 (le_self156 (UW152 (Z zero) (kk + 2)))]
  exact collapse0_sum2_156 (Z zero) kk

theorem dictD0_sum_j3_156 (kk : Nat) :
    dict (BT.D 0 (BT.sum (nst132 (kk + 4) BT.zero) (nst132 3 BT.zero)))
      = psi (Z zero) (add (UW152 (Z zero) (kk + 2)) TM.Term.one) := by
  rw [Trans.Dict.dict_D, Trans.Dict.dict_sum,
    show dict (nst132 (kk + 4) BT.zero) = TW (kk + 3) from dict_bT152 (kk + 2),
    show dict (nst132 3 BT.zero) = TW 2 from dict_bT152 1,
    show (TW (kk + 3) : Term) = UW152 (Z zero) (kk + 2) from TW_UW156 (kk + 2),
    plus_UW_TW156 (c := 1)
      (le_of_lt (lt_TW_UW152 (Z zero) 2 (kk + 2) (by omega)))]
  exact collapse0_UW_TW2_156 (Z zero) kk

theorem dictD0_sum_j2_156 (kk : Nat) :
    dict (BT.D 0 (BT.sum (nst132 (kk + 4) BT.zero) (nst132 2 BT.zero)))
      = phi (add TM.Term.one TM.Term.one) (psi (Z zero) (UW152 (Z zero) (kk + 2))) := by
  rw [Trans.Dict.dict_D, Trans.Dict.dict_sum,
    show dict (nst132 (kk + 4) BT.zero) = TW (kk + 3) from dict_bT152 (kk + 2),
    show dict (nst132 2 BT.zero) = TW 1 from dict_bT152 0,
    show (TW (kk + 3) : Term) = UW152 (Z zero) (kk + 2) from TW_UW156 (kk + 2),
    plus_UW_TW156 (c := 0)
      (le_of_lt (lt_TW_UW152 (Z zero) 1 (kk + 2) (by omega)))]
  exact collapse0_UW_TW1_156 (Z zero) kk

theorem dictD0_sum_j1_156 (kk : Nat) :
    dict (BT.D 0 (BT.sum (nst132 (kk + 4) BT.zero) (nst132 1 BT.zero)))
      = phi TM.Term.one (psi (Z zero) (UW152 (Z zero) (kk + 2))) := by
  rw [Trans.Dict.dict_D, Trans.Dict.dict_sum,
    show dict (nst132 (kk + 4) BT.zero) = TW (kk + 3) from dict_bT152 (kk + 2),
    show dict (nst132 1 BT.zero) = Z zero from by decide,
    show (TW (kk + 3) : Term) = UW152 (Z zero) (kk + 2) from TW_UW156 (kk + 2),
    plus_UW_Om156 (Z zero) (kk + 2)]
  exact collapse0_UW_Om156 (Z zero) kk

theorem dictD0_33_156 :
    dict (BT.D 0 (BT.sum (nst132 3 BT.zero) (nst132 3 BT.zero)))
      = psi (Z zero) TM.Term.one := by decide

theorem dictD0_32_156 :
    dict (BT.D 0 (BT.sum (nst132 3 BT.zero) (nst132 2 BT.zero)))
      = phi (add TM.Term.one TM.Term.one) (psi (Z zero) zero) := by decide

theorem dictD0_31_156 :
    dict (BT.D 0 (BT.sum (nst132 3 BT.zero) (nst132 1 BT.zero)))
      = phi TM.Term.one (psi (Z zero) zero) := by decide

/-- **主定理 3 — 和の種の塔 `famD156 m k j` は `3 ≤ k ≤ m`、`1 ≤ j ≤ k` の全域で
    第一の門の一歩を満たす。**  §132.5 の測定した resid の範囲そのもの。
    どの領域でも種の `K` は一元で、その元の頭は内の高い塔 — `k ≤ m` で外の塔より下。 -/
theorem ksetStepOK_famD156 {m k j : Nat} (h3k : 3 ≤ k) (hkm : k ≤ m)
    (h1j : 1 ≤ j) (hjk : j ≤ k) : KsetStepOK 0 (dict (famD156 m k j)) := by
  obtain ⟨mm, rfl⟩ : ∃ mm, m = mm + 3 := ⟨m - 3, by omega⟩
  obtain ⟨kq, rfl⟩ : ∃ kq, k = kq + 3 := ⟨k - 3, by omega⟩
  show KsetStepOK 0 (dict (nst132 ((mm + 2) + 1)
    (BT.D 0 (BT.sum (nst132 (kq + 3) BT.zero) (nst132 j BT.zero)))))
  cases kq with
  | zero =>
      -- k = 3, j ∈ {1, 2, 3}
      cases j with
      | zero => exact absurd h1j (by omega)
      | succ j0 =>
        cases j0 with
        | zero =>
            rw [dict_nstD0_156 rfl rfl
              (lt_phiPsi_reg1_156 (by decide) zero)
              (lt_phiPsi_reg2_156 (by decide) zero) dictD0_31_156 (mm + 2)]
            refine stepOK_UW152 (lt_phiPsi_reg1_156 (by decide) zero) mm ?_
            intro y hy
            replace hy : y ∈ Kset (reg 1) (psi (Z zero) zero) := hy
            rw [Kset_psi_reg152] at hy
            replace hy : y ∈ [(zero : Term)] := hy
            rw [List.mem_singleton.mp hy]
            exact lt_zero_left (ne_zero_UW152 _ _)
        | succ j1 =>
          cases j1 with
          | zero =>
              rw [dict_nstD0_156 rfl rfl
                (lt_phiPsi_reg1_156 (by decide) zero)
                (lt_phiPsi_reg2_156 (by decide) zero) dictD0_32_156 (mm + 2)]
              refine stepOK_UW152 (lt_phiPsi_reg1_156 (by decide) zero) mm ?_
              intro y hy
              replace hy : y ∈ Kset (reg 1) (psi (Z zero) zero) := hy
              rw [Kset_psi_reg152] at hy
              replace hy : y ∈ [(zero : Term)] := hy
              rw [List.mem_singleton.mp hy]
              exact lt_zero_left (ne_zero_UW152 _ _)
          | succ j2 =>
              -- j = j2 + 3 ≤ 3, so j2 = 0
              obtain rfl : j2 = 0 := by omega
              rw [dict_nstD0_156 rfl rfl
                (lt_psiOm_reg1_139 TM.Term.one)
                (lt_psiOm_reg2_156 TM.Term.one) dictD0_33_156 (mm + 2)]
              refine stepOK_UW152 (lt_psiOm_reg1_139 TM.Term.one) mm ?_
              intro y hy
              rw [Kset_psi_reg152] at hy
              replace hy : y ∈ [TM.Term.one] := hy
              rw [List.mem_singleton.mp hy]
              exact lt_one_UW156 _ _
  | succ kk =>
      -- k = kk + 4
      have hkm2 : kk + 2 < mm + 2 := by omega
      cases j with
      | zero => exact absurd h1j (by omega)
      | succ j0 =>
        cases j0 with
        | zero =>
            -- j = 1
            rw [dict_nstD0_156 rfl rfl
              (lt_phiPsi_reg1_156 (by decide) _)
              (lt_phiPsi_reg2_156 (by decide) _) (dictD0_sum_j1_156 kk) (mm + 2)]
            refine stepOK_UW152 (lt_phiPsi_reg1_156 (by decide) _) mm ?_
            intro y hy
            replace hy : y ∈ Kset (reg 1) (psi (Z zero) (UW152 (Z zero) (kk + 2))) := hy
            rw [Kset_psi_reg152, Kset_UW152] at hy
            replace hy : y ∈ [UW152 (Z zero) (kk + 2)] := hy
            rw [List.mem_singleton.mp hy]
            exact lt_UW_UW_lt155 _ _ _ _ hkm2
        | succ j1 =>
          cases j1 with
          | zero =>
              -- j = 2
              rw [dict_nstD0_156 rfl rfl
                (lt_phiPsi_reg1_156 (by decide) _)
                (lt_phiPsi_reg2_156 (by decide) _) (dictD0_sum_j2_156 kk) (mm + 2)]
              refine stepOK_UW152 (lt_phiPsi_reg1_156 (by decide) _) mm ?_
              intro y hy
              replace hy : y ∈ Kset (reg 1) (psi (Z zero) (UW152 (Z zero) (kk + 2))) := hy
              rw [Kset_psi_reg152, Kset_UW152] at hy
              replace hy : y ∈ [UW152 (Z zero) (kk + 2)] := hy
              rw [List.mem_singleton.mp hy]
              exact lt_UW_UW_lt155 _ _ _ _ hkm2
          | succ j2 =>
            cases j2 with
            | zero =>
                -- j = 3
                rw [dict_nstD0_156 rfl rfl
                  (lt_psiOm_reg1_139 _) (lt_psiOm_reg2_156 _)
                  (dictD0_sum_j3_156 kk) (mm + 2)]
                refine stepOK_UW152 (lt_psiOm_reg1_139 _) mm ?_
                intro y hy
                rw [Kset_psi_reg152] at hy
                replace hy : y ∈ (add (UW152 (Z zero) (kk + 2)) TM.Term.one)
                    :: (Kset (reg 1) (UW152 (Z zero) (kk + 2))
                        ++ Kset (reg 1) TM.Term.one) := hy
                rw [Kset_UW152] at hy
                replace hy : y ∈ [add (UW152 (Z zero) (kk + 2)) TM.Term.one] := hy
                rw [List.mem_singleton.mp hy,
                  lt_add_nsum (ne_zero_UW152 _ _) (nsum_UW152 _ _)]
                exact lt_UW_UW_lt155 _ _ _ _ hkm2
            | succ jj =>
                -- j = jj + 4 ≤ k = kk + 4
                rcases Nat.eq_or_lt_of_le (show jj ≤ kk by omega) with rfl | hlt3
                · -- j = k: the merged coefficient-2 seed
                  rw [dict_nstD0_156 rfl rfl
                    (lt_psiOm_reg1_139 _) (lt_psiOm_reg2_156 _)
                    (dictD0_sum_eq156 jj) (mm + 2)]
                  refine stepOK_UW152 (lt_psiOm_reg1_139 _) mm ?_
                  intro y hy
                  rw [Kset_psi_reg152] at hy
                  replace hy : y ∈ (add (UW152 (Z zero) (jj + 2)) (UW152 (Z zero) (jj + 2)))
                      :: (Kset (reg 1) (UW152 (Z zero) (jj + 2))
                          ++ Kset (reg 1) (UW152 (Z zero) (jj + 2))) := hy
                  rw [Kset_UW152] at hy
                  replace hy : y ∈ [add (UW152 (Z zero) (jj + 2)) (UW152 (Z zero) (jj + 2))]
                    := hy
                  rw [List.mem_singleton.mp hy,
                    lt_add_nsum (ne_zero_UW152 _ _) (nsum_UW152 _ _)]
                  exact lt_UW_UW_lt155 _ _ _ _ (by omega)
                · -- 4 ≤ j < k: the two-digit seed
                  rw [dict_nstD0_156 rfl rfl
                    (lt_psiOm_reg1_139 _) (lt_psiOm_reg2_156 _)
                    (dictD0_sum_lt156 kk jj hlt3) (mm + 2)]
                  refine stepOK_UW152 (lt_psiOm_reg1_139 _) mm ?_
                  intro y hy
                  rw [Kset_psi_reg152] at hy
                  replace hy : y ∈ (add (UW152 (Z zero) (kk + 2)) (UW152 (Z zero) (jj + 2)))
                      :: (Kset (reg 1) (UW152 (Z zero) (kk + 2))
                          ++ Kset (reg 1) (UW152 (Z zero) (jj + 2))) := hy
                  rw [Kset_UW152 (Z zero) (kk + 2), Kset_UW152 (Z zero) (jj + 2)] at hy
                  replace hy : y ∈ [add (UW152 (Z zero) (kk + 2)) (UW152 (Z zero) (jj + 2))]
                    := hy
                  rw [List.mem_singleton.mp hy,
                    lt_add_nsum (ne_zero_UW152 _ _) (nsum_UW152 _ _)]
                  exact lt_UW_UW_lt155 _ _ _ _ hkm2

theorem gateStd87_famD156 (m k j : Nat) (h3k : 3 ≤ k) (hkm : k ≤ m)
    (h1j : 1 ≤ j) (hjk : j ≤ k) : GateStd87 (famD156 m k j) :=
  fun _ _ => ksetStepOK_famD156 h3k hkm h1j hjk

theorem firstFire_famD156 (m k j : Nat) (h3k : 3 ≤ k) (hkm : k ≤ m)
    (h1j : 1 ≤ j) (hjk : j ≤ k) : FirstFire145 (famD156 m k j) :=
  fun q hq _ hle y hy => (ksetStepOK_famD156 h3k hkm h1j hjk q hq hle).2 y hy

/-! ### §156.6 Measurement (frozen) — everything below is measurement, not proof -/

/-- 混合の和の判定器 — 裸の塔と famB の和、どちらの順でも。 -/
def isMixTB156 : BT → Bool
  | BT.sum x y => (isTow155 x && isFamB155 y) || (isFamB155 x && isTow155 y)
  | _ => false

/-- 和の種の塔の判定器 — `ψ₀` の引数が裸の塔の和。 -/
def isSumSeed156 : BT → Bool
  | BT.D 1 a => isSumSeed156 a
  | BT.D 0 (BT.sum x y) => isTow155 x && isTow155 y
  | _ => false

/-- §152+§155 の類に §156 の二類を足した被覆判定器。 -/
def covered156 (a : BT) : Bool := covered155 a || isMixTB156 a || isSumSeed156 a

/-! **resid の境界の凍結 (`m, k, p, j < 7`)。**  三つの族の §132 の残る母集団は
    ちょうど定理の領域: `famB m k ⊕ ψ₁^p 0` は `3 ≤ k ≤ m ∧ 1 ≤ p ≤ m`、
    `ψ₁^p 0 ⊕ famB m k` は `3 ≤ k ∧ 3 ≤ m < p ∧ k ≤ p` (famB は単独では標準でない
    `k > m` も入る)、`famD156 m k j` は `3 ≤ k ≤ m ∧ 1 ≤ j ≤ k`。 -/

#guard (List.range 7).all fun m => (List.range 7).all fun k => (List.range 7).all fun p =>
  resid136 (BT.sum (famB132 m k) (nst132 p BT.zero))
    == (decide (3 ≤ k) && decide (k ≤ m) && decide (1 ≤ p) && decide (p ≤ m))

#guard (List.range 7).all fun m => (List.range 7).all fun k => (List.range 7).all fun p =>
  resid136 (BT.sum (nst132 p BT.zero) (famB132 m k))
    == (decide (3 ≤ k) && decide (3 ≤ m) && decide (m < p) && decide (k ≤ p))

#guard (List.range 7).all fun m => (List.range 7).all fun k => (List.range 7).all fun j =>
  resid136 (famD156 m k j)
    == (decide (3 ≤ k) && decide (k ≤ m) && decide (1 ≤ j) && decide (j ≤ k))

/-! **定理の領域で一歩の判定器は真 (`< 7` で凍結)。** -/

#guard (List.range 7).all fun m => (List.range 7).all fun k => (List.range 7).all fun p =>
  !(decide (3 ≤ k) && decide (k ≤ m) && decide (1 ≤ p) && decide (p ≤ m))
  || stepOKb 0 (dict (BT.sum (famB132 m k) (nst132 p BT.zero)))

#guard (List.range 7).all fun m => (List.range 7).all fun k => (List.range 7).all fun p =>
  !(decide (3 ≤ k) && decide (3 ≤ m) && decide (m < p) && decide (k ≤ p))
  || stepOKb 0 (dict (BT.sum (nst132 p BT.zero) (famB132 m k)))

#guard (List.range 7).all fun m => (List.range 7).all fun k => (List.range 7).all fun j =>
  !(decide (3 ≤ k) && decide (k ≤ m) && decide (1 ≤ j) && decide (j ≤ k))
  || stepOKb 0 (dict (famD156 m k j))

/-! **閉じた形の照合 — `dict` の値は本当に定理の言う形。** -/

#guard dict (BT.sum (famB132 5 4) (nst132 3 BT.zero)) == add (UW152 (sd152 4) 4) (TW 2)
#guard dict (BT.sum (famB132 5 4) (nst132 1 BT.zero)) == add (UW152 (sd152 4) 4) (Z zero)
#guard dict (BT.sum (nst132 6 BT.zero) (famB132 5 4)) == add (TW 5) (UW152 (sd152 4) 4)
#guard dict (famD156 4 4 4) == UW152 (psi (Z zero) (add (TW 3) (TW 3))) 3
#guard dict (famD156 5 5 4) == UW152 (psi (Z zero) (add (TW 4) (TW 3))) 4
#guard dict (famD156 4 4 3) == UW152 (psi (Z zero) (add (TW 3) TM.Term.one)) 3
#guard dict (famD156 4 4 2)
  == UW152 (phi (add TM.Term.one TM.Term.one) (psi (Z zero) (TW 3))) 3
#guard dict (famD156 4 4 1) == UW152 (phi TM.Term.one (psi (Z zero) (TW 3))) 3
#guard dict (famD156 4 3 3) == UW152 (psi (Z zero) TM.Term.one) 3
#guard dict (famD156 4 3 2)
  == UW152 (phi (add TM.Term.one TM.Term.one) (psi (Z zero) zero)) 3
#guard dict (famD156 4 3 1) == UW152 (phi TM.Term.one (psi (Z zero) zero)) 3

/-! **母集団との重なり。**  famD156 は famPool132 の第六の族そのもの、混合の和は
    pool136 の第一・第二の族に居る。 -/

#guard famPool132.contains (famD156 4 4 2)
#guard famPool132.contains (famD156 7 5 3)
#guard pool136.contains (BT.sum (nst132 4 BT.zero) (famB132 3 3))
#guard pool136.contains (BT.sum (famB132 3 3) (nst132 2 BT.zero))
#guard fm145.contains (BT.sum (nst132 4 BT.zero) (famB132 3 3))

/-! **被覆の凍結。**  §132 の残り (`resid136`) のうち、証明済みの形の類に文字通り
    入っている本数:
    famPool132 (2455 本): §155.7 の 504 に和の種の塔 65 が加わり **569 本 (23.2%)**。
    混合の和は famPool132 では全て `ψ₁` に包まれた形 (`ψ₁^m(塔 ⊕ ψ₀ ...)`) で現れ、
    頂点の和としては現れない — その類はここでは動かない。
    pool136 (925 本): 頂点の混合の和 70 本が新たに入り **0 → 70 本 (7.6%)**。
    fm145 (3371 本): 混合の和 25 + 和の種 26 で **15 → 66 本 (2.0%)**。
    残る形の名: `ψ₁` に包まれた混合の和 — 底が `塔 ⊕ ψ₀(…)` の φ̄0 の塔。その
    `wcnf` の桁は `(塔, ψ_{Ω₁}(…))` — 係数が `1` でない famE155 の形の一般化 —
    が §156 の外に残る次の一歩。 -/

#guard (famPool132.filter resid136).length == 2455
#guard ((famPool132.filter resid136).countP isMixTB156) == 0
#guard ((famPool132.filter resid136).countP isSumSeed156) == 65
#guard ((famPool132.filter resid136).countP covered156) == 569
#guard (pool136.filter resid136).length == 925
#guard ((pool136.filter resid136).countP isMixTB156) == 70
#guard ((pool136.filter resid136).countP isSumSeed156) == 0
#guard ((pool136.filter resid136).countP covered156) == 70
#guard (fm145.filter resid136).length == 3371
#guard ((fm145.filter resid136).countP isMixTB156) == 25
#guard ((fm145.filter resid136).countP isSumSeed156) == 26
#guard ((fm145.filter resid136).countP covered156) == 66

/-! ### Axioms — no `sorryAx`, no `native_decide` -/

#print axioms lt_UW_reg1_156
#print axioms wcnf_UW156
#print axioms idx_UW156
#print axioms stepF_fire156
#print axioms idx2_156
#print axioms TW_UW156
#print axioms beq_UW_seed156
#print axioms wcnf_sumX156
#print axioms stepOK_sumX156
#print axioms stepOK_UW_Om156
#print axioms stepOK_UW_TW1_156
#print axioms stepOK_UW_TW2_156
#print axioms ksetStepOK_famB_tow156
#print axioms ksetStepOK_tow_famB156
#print axioms gateStd87_famB_tow156
#print axioms gateStd87_tow_famB156
#print axioms firstFire_famB_tow156
#print axioms firstFire_tow_famB156
#print axioms collapse0_sum2_156
#print axioms collapse0_sumX156
#print axioms collapse0_UW_TW2_156
#print axioms collapse0_UW_TW1_156
#print axioms collapse0_UW_Om156
#print axioms dictD0_sum_lt156
#print axioms dictD0_sum_eq156
#print axioms dictD0_sum_j3_156
#print axioms dictD0_sum_j2_156
#print axioms dictD0_sum_j1_156
#print axioms dict_nstD0_156
#print axioms ksetStepOK_famD156
#print axioms gateStd87_famD156
#print axioms firstFire_famD156

end




/-! # §157 `Dom154` REDUCED TO THE STANDARDNESS CARRIERS `Subord157 ∧ ExpSubR157`

The assembly: every arithmetic ingredient of the mid-list domination is proven here
(the walk along `a`'s Veblen suffix, the fired-index domination, the fold growth on
`b`'s side, the vacuous `ty = []` case), on top of the library's §110/§112/§117/§120/§129
toolboxes.  What remains hypothetical is exactly the sweep-separated standardness
carrier pair (`Subord157`, `ExpSubR157`). -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-! ## §157.1 The closures and the carriers -/

/-- Terms subordinate to the bound `w`, with `φ̄`-exponents capped by `A`.
    Wellformedness is carried in the constructors. -/
inductive Sub157 (A w : Term) : Term → Prop where
  | ofLe : ∀ {t : Term}, inT t = true → lt t M = true → le t w = true → Sub157 A w t
  | ofPhi : ∀ {α ξ : Term}, inT α = true → lt α M = true → le α A = true →
      Sub157 A w ξ → Sub157 A w (TM.Term.phi α ξ)
  | ofPlus : ∀ {p q : Term}, Sub157 A w p → Sub157 A w q → Sub157 A w (plus p q)

/-- The recursive (uncapped) closure — for exponents. -/
inductive SubR157 (w : Term) : Term → Prop where
  | ofLe : ∀ {t : Term}, inT t = true → lt t M = true → le t w = true → SubR157 w t
  | ofPhi : ∀ {α ξ : Term}, SubR157 w α → SubR157 w ξ → SubR157 w (TM.Term.phi α ξ)
  | ofPlus : ∀ {p q : Term}, SubR157 w p → SubR157 w q → SubR157 w (plus p q)

/-- Fold value of a pair-list prefix, defaulting to `one` on the empty prefix. -/
def wVal157 (P : List (Term × Term)) : Term :=
  ((P.foldl (stepF (reg 1) (baseOf 0))
    ((none : Option Term), (none : Option Term))).2).getD TM.Term.one

/-- **The standardness carrier** (assumed): every Veblen pair's coefficient in the
    `wcnf` list of a standard image is subordinate to the fold value of its own
    prefix, with `φ̄`-exponents capped by its own exponent. -/
def Subord157 : Prop :=
  ∀ a : BT, btLe72 1 (BT.D 0 a) = true → BT.isStd (BT.D 0 a) = true →
    ∀ (P S : List (Term × Term)) (ac : Term × Term),
      (wcnf (reg 1) (toList (dict a))).1 = P ++ ac :: S →
      le (reg 1) ac.1 = false →
      Sub157 ac.1 (wVal157 P) ac.2

/-- **The exponent carrier** (assumed): every Veblen pair's exponent is recursively
    subordinate to the fold value of its own prefix. -/
def ExpSubR157 : Prop :=
  ∀ a : BT, btLe72 1 (BT.D 0 a) = true → BT.isStd (BT.D 0 a) = true →
    ∀ (P S : List (Term × Term)) (ac : Term × Term),
      (wcnf (reg 1) (toList (dict a))).1 = P ++ ac :: S →
      le (reg 1) ac.1 = false →
      SubR157 (wVal157 P) ac.1

/-! ## §157.2 Wellformedness of closure members -/

theorem sub157_inT {A w t : Term} (h : Sub157 A w t) : inT t = true ∧ lt t M = true := by
  induction h with
  | ofLe hit hltM _ => exact ⟨hit, hltM⟩
  | ofPhi hiα hαM _ _ ih =>
      refine ⟨?_, lt_phi_M _ _⟩
      show (_ && _ && _ && _) = true
      rw [hiα, ih.1, hαM, ih.2]
      rfl
  | ofPlus _ _ ihp ihq =>
      exact ⟨inT_plus ihp.1 ihq.1, lt_plus_M ihp.1 ihq.1 ihp.2 ihq.2⟩

theorem subR157_inT {w t : Term} (h : SubR157 w t) : inT t = true ∧ lt t M = true := by
  induction h with
  | ofLe hit hltM _ => exact ⟨hit, hltM⟩
  | ofPhi _ _ ihα ihξ =>
      refine ⟨?_, lt_phi_M _ _⟩
      show (_ && _ && _ && _) = true
      rw [ihα.1, ihξ.1, ihα.2, ihξ.2]
      rfl
  | ofPlus _ _ ihp ihq =>
      exact ⟨inT_plus ihp.1 ihq.1, lt_plus_M ihp.1 ihq.1 ihp.2 ihq.2⟩

/-! ## §157.3 Closures below a target -/

/-- Small helper: nonzero terms are at least `one`. -/
theorem le_one157 {c : Term} (hc : inT c = true) (hz : c ≠ zero) :
    le TM.Term.one c = true := by
  cases hlt : lt c TM.Term.one with
  | true => exact absurd (below_one c hc _ hlt) hz
  | false =>
      exact le_of_not_lt3 (inT_le_fragR _ hc) (show FragR TM.Term.one = true from rfl) hlt

/-- The capped closure stays below an additively principal target `T`, given the
    bound `w < T`, the cap `A < B`, and closure of `T` under `φ̄` with first
    argument below `B`. -/
theorem subLt157 {A w t T B : Term} (hs : Sub157 A w t)
    (hiT : inT T = true) (hTap : T.isAP = true)
    (hiA : inT A = true) (hiB : inT B = true) (hAB : lt A B = true)
    (hiw : inT w = true) (hw : lt w T = true)
    (hraw : ∀ α ξ : Term, inT α = true → lt α M = true → inT ξ = true → lt ξ M = true →
      lt α B = true → lt ξ T = true → lt (phi α ξ) T = true) :
    lt t T = true := by
  have hfT : FragR T = true := inT_le_fragR _ hiT
  have hTz : T ≠ zero := by
    intro hc
    rw [hc, lt_zero_right] at hw
    exact Bool.noConfusion hw
  induction hs with
  | ofLe hit _ hle =>
      exact lt_of_le_of_lt3 (inT_le_fragR _ hit) (inT_le_fragR _ hiw) hfT hle hw
  | @ofPhi α ξ hiα hαM hαA hξ ih =>
      have hξf := sub157_inT hξ
      have hαB : lt α B = true :=
        lt_of_le_of_lt3 (inT_le_fragR _ hiα) (inT_le_fragR _ hiA) (inT_le_fragR _ hiB)
          hαA hAB
      exact hraw α ξ hiα hαM hξf.1 hξf.2 hαB ih
  | @ofPlus p q hp hq ihp ihq =>
      exact lt_plus_ap114 hTap hTz hfT (sub157_inT hp).1 (sub157_inT hq).1 ihp ihq

/-- The recursive closure stays below an additively principal target `T` closed
    under `φ̄` with both arguments below `T`. -/
theorem subRLt157 {w t T : Term} (hs : SubR157 w t)
    (hiT : inT T = true) (hTap : T.isAP = true)
    (hiw : inT w = true) (hw : lt w T = true)
    (hraw : ∀ α ξ : Term, inT α = true → lt α M = true → inT ξ = true → lt ξ M = true →
      lt α T = true → lt ξ T = true → lt (phi α ξ) T = true) :
    lt t T = true := by
  have hfT : FragR T = true := inT_le_fragR _ hiT
  have hTz : T ≠ zero := by
    intro hc
    rw [hc, lt_zero_right] at hw
    exact Bool.noConfusion hw
  induction hs with
  | ofLe hit _ hle =>
      exact lt_of_le_of_lt3 (inT_le_fragR _ hit) (inT_le_fragR _ hiw) hfT hle hw
  | @ofPhi α ξ hα hξ ihα ihξ =>
      have hαf := subR157_inT hα
      have hξf := subR157_inT hξ
      exact hraw α ξ hαf.1 hαf.2 hξf.1 hξf.2 ihα ihξ
  | @ofPlus p q hp hq ihp ihq =>
      exact lt_plus_ap114 hTap hTz hfT (subR157_inT hp).1 (subR157_inT hq).1 ihp ihq

/-! ## §157.4 The `φ̄`-target dispatchers -/

theorem inT_phi_facts157 {a b : Term} (h : inT (TM.Term.phi a b) = true) :
    inT a = true ∧ inT b = true ∧ lt a M = true ∧ lt b M = true := by
  have h4 : (inT a && inT b && lt a M && lt b M) = true := h
  obtain ⟨h3, hbM⟩ := (Bool.and_eq_true _ _).mp h4
  obtain ⟨h2, haM⟩ := (Bool.and_eq_true _ _).mp h3
  obtain ⟨hia, hib⟩ := (Bool.and_eq_true _ _).mp h2
  exact ⟨hia, hib, haM, hbM⟩

/-- `isFP` decides `FixSh129`. -/
theorem isFP_iff157 (A g : Term) : isFP A g = true ↔ FixSh129 A g := by
  constructor
  · intro h
    rcases (Bool.or_eq_true _ _).mp h with h1 | h2
    · obtain ⟨hsc, hlt⟩ := (Bool.and_eq_true _ _).mp h1
      exact Or.inl ⟨hsc, hlt⟩
    · cases g with
      | phi c d => exact Or.inr ⟨c, d, rfl, h2⟩
      | zero => exact Bool.noConfusion h2
      | M => exact Bool.noConfusion h2
      | omg x => exact Bool.noConfusion h2
      | add x y => exact Bool.noConfusion h2
      | psi k c => exact Bool.noConfusion h2
      | Z x => exact Bool.noConfusion h2
  · intro h
    rcases h with ⟨hsc, hlt⟩ | ⟨d, e, he, hlt⟩
    · exact (Bool.or_eq_true _ _).mpr (Or.inl ((Bool.and_eq_true _ _).mpr ⟨hsc, hlt⟩))
    · subst he
      exact (Bool.or_eq_true _ _).mpr (Or.inr hlt)

theorem phiNFdefault_shape157 (B δ : Term) :
    (phiNFdefault B δ = B ∧ B.isSC = true ∧ δ = zero)
  ∨ phiNFdefault B δ = TM.Term.phi B δ := by
  unfold phiNFdefault
  by_cases hd : (δ == zero && B.isSC) = true
  · rw [if_pos hd]
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hd
    exact Or.inl ⟨rfl, h2, eq_of_beq h1⟩
  · rw [if_neg hd]
    exact Or.inr rfl

/-- The five branch shapes of `phiNF B δ`. -/
theorem phiNF_shape157 (B δ : Term) :
    (phiNF B δ = δ ∧ δ.isSC = true ∧ lt B δ = true)
  ∨ (∃ c d, δ = TM.Term.phi c d ∧ lt B c = true ∧ phiNF B δ = δ)
  ∨ (∃ g m, splitFin δ = (g, m) ∧ m ≥ 1
      ∧ phiNF B δ = TM.Term.phi B (plus g (ofNat (m-1))))
  ∨ (phiNF B δ = B ∧ B.isSC = true ∧ δ = zero)
  ∨ (phiNF B δ = TM.Term.phi B δ) := by
  by_cases hfp : isFP B δ = true
  · rcases (isFP_iff157 B δ).mp hfp with ⟨hsc, hlt⟩ | ⟨c, d, he, hlt⟩
    · exact Or.inl ⟨phiNF_fixSh129 (Or.inl ⟨hsc, hlt⟩), hsc, hlt⟩
    · exact Or.inr (Or.inl ⟨c, d, he, hlt,
        phiNF_fixSh129 (Or.inr ⟨c, d, he, hlt⟩)⟩)
  · have hnf : ¬ FixSh129 B δ := fun hc => hfp ((isFP_iff157 B δ).mpr hc)
    have he1 : phiNF B δ = phiNFsucc B δ := phiNF_notFix129 hnf
    cases hsp : splitFin δ with
    | mk g m =>
      by_cases hm : m ≥ 1
      · by_cases hg : isFP B g = true
        · exact Or.inr (Or.inr (Or.inl ⟨g, m, rfl, hm, by
            rw [he1]; exact phiNFsucc_val129 hsp hm ((isFP_iff157 B g).mp hg)⟩))
        · have hd : phiNFsucc B δ = phiNFdefault B δ :=
            phiNFsucc_def129 hsp (fun hc => hg ((isFP_iff157 B g).mpr hc))
          rcases phiNFdefault_shape157 B δ with ⟨h1, h2, h3⟩ | h1
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [he1, hd]; exact h1, h2, h3⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [he1, hd]; exact h1))))
      · have hd : phiNFsucc B δ = phiNFdefault B δ := phiNFsucc_lo129 hsp hm
        rcases phiNFdefault_shape157 B δ with ⟨h1, h2, h3⟩ | h1
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [he1, hd]; exact h1, h2, h3⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [he1, hd]; exact h1))))

/-- A strongly critical term below `Ω₁` is a `ψ`-term. -/
theorem sc_shape157 {t : Term} (hsc : t.isSC = true) (hW : lt t (reg 1) = true) :
    ∃ k c, t = psi k c := by
  cases t with
  | M => rw [lt_M_reg1_false100] at hW; exact Bool.noConfusion hW
  | Z d => rw [lt_Z_reg1_false100] at hW; exact Bool.noConfusion hW
  | psi k c => exact ⟨k, c, rfl⟩
  | zero => exact Bool.noConfusion hsc
  | omg x => exact Bool.noConfusion hsc
  | add x y => exact Bool.noConfusion hsc
  | phi x y => exact Bool.noConfusion hsc

/-- **Raw `φ̄` below a `phiNF`-target** — first argument below `B`, second below
    the target. -/
theorem lt_phi_vTgt157 {B δ p q : Term} (hiB : inT B = true) (hiδ : inT δ = true)
    (hip : inT p = true) (hiq : inT q = true)
    (hTW : lt (phiNF B δ) (reg 1) = true)
    (hpB : lt p B = true) (hq : lt q (phiNF B δ) = true) :
    lt (phi p q) (phiNF B δ) = true := by
  rcases phiNF_shape157 B δ with ⟨he, hsc, hBδ⟩ | ⟨c, d, hδe, hBc, he⟩
    | ⟨g, m, hsp, hm, he⟩ | ⟨he, hsc, _⟩ | he
  · rw [he] at hq hTW ⊢
    obtain ⟨k, c, hk⟩ := sc_shape157 hsc hTW
    subst hk
    exact lt_phi_psi_of (lt_trans_inT hip hiB hiδ hpB hBδ) hq
  · rw [he] at hq ⊢
    subst hδe
    have hic : inT c = true := (inT_phi_facts157 hiδ).1
    rw [lt_phi_vT117 (lt_trans_inT hip hiB hic hpB hBc)]
    exact hq
  · rw [he] at hq ⊢
    rw [lt_phi_vT117 hpB]
    exact hq
  · rw [he] at hq hTW ⊢
    obtain ⟨k, c, hk⟩ := sc_shape157 hsc hTW
    subst hk
    exact lt_phi_psi_of hpB hq
  · rw [he] at hq ⊢
    rw [lt_phi_vT117 hpB]
    exact hq

/-- **`φ̄`-normalisation below a `phiNF`-target** — exponent below `B`, argument
    below the target. -/
theorem lt_phiNF_vTgt157 {B δ a X : Term} (hiB : inT B = true) (hBM : lt B M = true)
    (hiδ : inT δ = true) (hδM : lt δ M = true)
    (hia : inT a = true) (haM : lt a M = true) (hiX : inT X = true)
    (hT1 : lt TM.Term.one (phiNF B δ) = true) (hTW : lt (phiNF B δ) (reg 1) = true)
    (haB : lt a B = true) (hX : lt X (phiNF B δ) = true) :
    lt (phiNF a X) (phiNF B δ) = true := by
  rcases phiNF_shape157 B δ with ⟨he, hsc, hBδ⟩ | ⟨c, d, hδe, hBc, he⟩
    | ⟨g, m, hsp, hm, he⟩ | ⟨he, hsc, _⟩ | he
  · rw [he] at hX hTW ⊢
    obtain ⟨k, c, hk⟩ := sc_shape157 hsc hTW
    subst hk
    exact lt_phiNF_psi114 (inT_le_fragR _ hiδ) hiX
      (lt_trans_inT hia hiB hiδ haB hBδ) hX
  · rw [he] at hX hT1 ⊢
    subst hδe
    obtain ⟨hic, hid, hcM, hdM⟩ := inT_phi_facts157 hiδ
    exact lt_phiNF_vT117 hic hid hcM hdM hia haM hiX hT1
      (lt_trans_inT hia hiB hic haB hBc) hX
  · rw [he] at hX hT1 ⊢
    have hig : inT g = true := by
      have h0 := inT_splitFin hiδ; rw [hsp] at h0; exact h0
    have hgM : lt g M = true := by
      have h0 := ltM_splitFin hiδ hδM; rw [hsp] at h0; exact h0
    exact lt_phiNF_vT117 hiB (inT_plus hig (inT_ofNat _)) hBM
      (lt_plus_M hig (inT_ofNat _) hgM (ltM_ofNat _)) hia haM hiX hT1 haB hX
  · rw [he] at hX hTW ⊢
    obtain ⟨k, c, hk⟩ := sc_shape157 hsc hTW
    subst hk
    exact lt_phiNF_psi114 (inT_le_fragR _ hiB) hiX haB hX
  · rw [he] at hX hT1 ⊢
    exact lt_phiNF_vT117 hiB hiδ hBM hδM hia haM hiX hT1 haB hX

/-! ## §157.5 List and fold plumbing -/

theorem leW_false157 {A : Term} (hiA : inT A = true) (h : lt A (reg 1) = true) :
    le (reg 1) A = false := by
  cases hle : le (reg 1) A with
  | false => rfl
  | true =>
      exfalso
      have h2 : lt A A = true := lt_of_lt_of_le3 (inT_le_fragR _ hiA)
        (inT_le_fragR _ (inT_reg 1)) (inT_le_fragR _ hiA) h hle
      rw [lt_irrefl] at h2
      exact Bool.noConfusion h2

/-- Strict descent survives dropping a prefix: elements of the prefix strictly
    dominate the divergence pair's exponent. -/
theorem descP_cross157 : ∀ (P : List (Term × Term)) (q : Term × Term)
    (S : List (Term × Term)), descP118 (P ++ q :: S) →
    (∀ w ∈ P ++ q :: S, inT w.1 = true) →
    ∀ z ∈ P, lt q.1 z.1 = true := by
  intro P
  induction P with
  | nil => intro q S _ _ z hz; cases hz
  | cons a P' ih =>
      intro q S hd hin z hz
      have hd' : descP118 (a :: (P' ++ q :: S)) := hd
      rcases List.mem_cons.mp hz with h1 | h1
      · rw [h1]
        exact descP_bound154 (P' ++ q :: S) a hin hd' q
          (List.mem_append_right _ (List.Mem.head _))
      · exact ih q S (descP_tail118 hd')
          (fun w hw => hin w (List.Mem.tail _ hw)) z h1

/-- A strictly descending pair list splits into a fired prefix and a Veblen tail. -/
theorem splitFV157 : ∀ (l : List (Term × Term)), descP118 l →
    (∀ z ∈ l, inT z.1 = true) →
    ∃ F V, l = F ++ V ∧ (∀ z ∈ F, le (reg 1) z.1 = true)
      ∧ (∀ z ∈ V, le (reg 1) z.1 = false) := by
  intro l
  induction l with
  | nil => exact fun _ _ => ⟨[], [], rfl, fun z hz => absurd hz (List.not_mem_nil),
      fun z hz => absurd hz (List.not_mem_nil)⟩
  | cons a l' ih =>
      intro hd hin
      by_cases hf : le (reg 1) a.1 = true
      · obtain ⟨F', V', he, hF, hV⟩ := ih (descP_tail118 hd)
          (fun z hz => hin z (List.Mem.tail _ hz))
        refine ⟨a :: F', V', by rw [he]; rfl, ?_, hV⟩
        intro z hz
        rcases List.mem_cons.mp hz with h1 | h1
        · rw [h1]; exact hf
        · exact hF z h1
      · refine ⟨[], a :: l', rfl, fun z hz => absurd hz (List.not_mem_nil), ?_⟩
        intro z hz
        have haW : lt a.1 (reg 1) = true :=
          ltW_of_leW_false128 (hin a (List.Mem.head _)) (bool_false hf)
        rcases List.mem_cons.mp hz with h1 | h1
        · rw [h1]; exact bool_false hf
        · have hz1 : lt z.1 a.1 = true :=
            descP_bound154 l' a hin hd z h1
          exact leW_false157 (hin z (List.Mem.tail _ h1))
            (lt_trans_inT (hin z (List.Mem.tail _ h1)) (hin a (List.Mem.head _))
              (inT_reg 1) hz1 haW)

/-- `prevV151`/`lastAC151` read off a last-pair split. -/
theorem prevV_split157 {y : Term} {Q : List (Term × Term)} {ca : Term × Term}
    (h : (wcnf (reg 1) (toList y)).1 = Q ++ [ca]) :
    prevV151 y = (Q.foldl (stepF (reg 1) (baseOf 0))
      ((none : Option Term), (none : Option Term))).2 ∧ lastAC151 y = some ca := by
  have hrev : (wcnf (reg 1) (toList y)).1.reverse = ca :: Q.reverse := by
    rw [h, List.reverse_append]
    rfl
  unfold prevV151 lastAC151
  rw [hrev]
  dsimp only
  rw [List.reverse_reverse]
  exact ⟨rfl, rfl⟩

/-- `StE81` holds after folding any prefix of the `wcnf` pair list. -/
theorem stE81_pre157 {y : Term} (hy : inT y = true) (hly : lt y M = true)
    (Hp : PsiIdxOK 0 y) (P S : List (Term × Term))
    (hsplit : (wcnf (reg 1) (toList y)).1 = P ++ S) :
    StE81 (P.foldl (stepF (reg 1) (baseOf 0))
      ((none : Option Term), (none : Option Term))) := by
  obtain ⟨hc, hd⟩ := inT_toList y hy
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList y) hc hd
    (ltM_toList y hy hly)
  have hWp := wcnf_W79 (toList y) hc
  have hNZ := wcnf_NZ81 (toList y) hc
  have hinit : StE81 ((none : Option Term), (none : Option Term)) := by
    intro z hz; cases hz
  exact foldE81 P (none, none) hinit
    (fun z hz => hallOK z (by rw [hsplit]; exact List.mem_append_left _ hz))
    (fun z hz => (hWp.2 z (by rw [hsplit]; exact List.mem_append_left _ hz)).2)
    (fun z hz => hNZ z (by rw [hsplit]; exact List.mem_append_left _ hz))
    (fun p hp hf => Hp p (by
      rw [hsplit, scanSt_append109]
      exact List.mem_append_left _ hp) hf)

/-- Fired coherence: the value is `ψ_{Ω₁}` of the index, preserved by fired steps
    from the empty state. -/
def Coh157 (s : Option Term × Option Term) : Prop :=
  s.2 = Option.map (psi (reg 1)) s.1

theorem coh_fold157 : ∀ (l : List (Term × Term)) (s : Option Term × Option Term),
    (∀ z ∈ l, le (reg 1) z.1 = true) → Coh157 s →
    Coh157 (l.foldl (stepF (reg 1) (baseOf 0)) s) := by
  intro l
  induction l with
  | nil => intro s _ h; exact h
  | cons ac t ih =>
      intro s hall _
      refine ih _ (fun z hz => hall z (List.Mem.tail _ hz)) ?_
      have hf : le (reg 1) ac.1 = true := hall ac (List.Mem.head _)
      show (stepF (reg 1) (baseOf 0) s ac).2
        = Option.map (psi (reg 1)) (stepF (reg 1) (baseOf 0) s ac).1
      rw [stepF_snd_fire88 hf, stepF_fst, if_pos hf]
      rfl

/-! ## §157.6 The walk along a Veblen suffix -/

theorem foldl_snoc157 (P : List (Term × Term)) (ac : Term × Term)
    (s : Option Term × Option Term) :
    (P ++ [ac]).foldl (stepF (reg 1) (baseOf 0)) s
      = stepF (reg 1) (baseOf 0) (P.foldl (stepF (reg 1) (baseOf 0)) s) ac := by
  rw [List.foldl_append]
  rfl

theorem wVal_facts157 {y : Term} (hy : inT y = true) (hly : lt y M = true)
    (Hp : PsiIdxOK 0 y) (P S : List (Term × Term))
    (hsplit : (wcnf (reg 1) (toList y)).1 = P ++ S) :
    inT (wVal157 P) = true ∧ lt (wVal157 P) (reg 1) = true := by
  have hst := stE81_pre157 hy hly Hp P S hsplit
  unfold wVal157
  cases hs2 : (P.foldl (stepF (reg 1) (baseOf 0))
      ((none : Option Term), (none : Option Term))).2 with
  | none => exact ⟨inT_one, lt_one_W79⟩
  | some v =>
      obtain ⟨hiv, hvW, _, _⟩ := hst v hs2
      exact ⟨hiv, hvW⟩

/-- **The walk.**  Along a Veblen sublist of the pair list, if every pair's
    coefficient is subordinate (`HSub`), every exponent is below the cap `B`
    (`hexp`), and the target `T` is additively principal and closed under the
    `φ̄`-steps with exponents below `B`, then the fold value stays strictly
    below `T`. -/
theorem walk157 {u : Term} (hu : inT u = true) (huM : lt u M = true)
    (Hpu : PsiIdxOK 0 u)
    {T B : Term} (hiT : inT T = true) (hTap : T.isAP = true) (hiB : inT B = true)
    (HSub : ∀ P S ac, (wcnf (reg 1) (toList u)).1 = P ++ ac :: S →
        le (reg 1) ac.1 = false → Sub157 ac.1 (wVal157 P) ac.2)
    (S0 : List (Term × Term))
    (hstep : ∀ a X, inT a = true → lt a M = true → inT X = true → lt X M = true →
        lt a B = true → lt X T = true → lt (phiNF a X) T = true)
    (hraw : ∀ α ξ : Term, inT α = true → lt α M = true → inT ξ = true → lt ξ M = true →
        lt α B = true → lt ξ T = true → lt (phi α ξ) T = true)
    (hexp : ∀ P S ac, (wcnf (reg 1) (toList u)).1 = P ++ ac :: S → ac ∈ S0 →
        le (reg 1) ac.1 = false → lt (wVal157 P) T = true → lt ac.1 B = true) :
    ∀ (S P S2 : List (Term × Term)),
      (wcnf (reg 1) (toList u)).1 = P ++ (S ++ S2) →
      (∀ z ∈ S, z ∈ S0) →
      (∀ z ∈ S, le (reg 1) z.1 = false) →
      lt (wVal157 P) T = true →
      lt (wVal157 (P ++ S)) T = true := by
  intro S
  induction S with
  | nil =>
      intro P S2 _ _ _ hvP
      rw [List.append_nil]
      exact hvP
  | cons ac S' ih =>
      intro P S2 hsplit hS0 hVeb hvP
      have hsplit' : (wcnf (reg 1) (toList u)).1 = P ++ ac :: (S' ++ S2) := hsplit
      obtain ⟨hc, hd⟩ := inT_toList u hu
      obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList u) hc hd
        (ltM_toList u hu huM)
      have hmem : ac ∈ (wcnf (reg 1) (toList u)).1 := by
        rw [hsplit']
        exact List.mem_append_right _ (List.Mem.head _)
      obtain ⟨hi1, h1M, hi2, h2M⟩ := hallOK ac hmem
      have hf : le (reg 1) ac.1 = false := hVeb ac (List.Mem.head _)
      have hAB : lt ac.1 B = true :=
        hexp P (S' ++ S2) ac hsplit' (hS0 ac (List.Mem.head _)) hf hvP
      obtain ⟨hiw, hwW⟩ := wVal_facts157 hu huM Hpu P (ac :: (S' ++ S2)) hsplit'
      have hsub : Sub157 ac.1 (wVal157 P) ac.2 := HSub P (S' ++ S2) ac hsplit' hf
      have hC : lt ac.2 T = true := subLt157 hsub hiT hTap hi1 hiB hAB hiw hvP hraw
      have hfT : FragR T = true := inT_le_fragR _ hiT
      have hTz : T ≠ zero := by
        intro hcc
        rw [hcc, lt_zero_right] at hvP
        exact Bool.noConfusion hvP
      have hst := stE81_pre157 hu huM Hpu P (ac :: (S' ++ S2)) hsplit'
      have hv' : lt (wVal157 (P ++ [ac])) T = true := by
        cases hs2 : (P.foldl (stepF (reg 1) (baseOf 0))
            ((none : Option Term), (none : Option Term))).2 with
        | none =>
            have hv2 : ((P ++ [ac]).foldl (stepF (reg 1) (baseOf 0))
                ((none : Option Term), (none : Option Term))).2
                = some (phiNF ac.1 (plus (baseOf 0) (sub1 ac.2))) := by
              rw [foldl_snoc157, stepF_snd_veb88 hf, hs2]
            have hwv : wVal157 (P ++ [ac])
                = phiNF ac.1 (plus (baseOf 0) (sub1 ac.2)) := by
              unfold wVal157
              rw [hv2]
              rfl
            rw [hwv]
            have harg : lt (plus (baseOf 0) (sub1 ac.2)) T = true :=
              lt_plus_ap114 hTap hTz hfT (inT_baseOf 0) (inT_sub1 hi2)
                (show lt (baseOf 0) T = true from lt_zero_left hTz)
                (lt_of_le_of_lt3 (inT_le_fragR _ (inT_sub1 hi2)) (inT_le_fragR _ hi2)
                  hfT (le_sub1_self75 hi2) hC)
            exact hstep ac.1 _ hi1 h1M (inT_plus (inT_baseOf 0) (inT_sub1 hi2))
              (lt_plus_M (inT_baseOf 0) (inT_sub1 hi2) (ltM_baseOf 0)
                (ltM_sub1 hi2 h2M)) hAB harg
        | some v =>
            obtain ⟨hiv, hvW, _, _⟩ := hst v hs2
            have hvM : lt v M = true := ltM_of_ltW79 hiv hvW
            have hveq : wVal157 P = v := by
              unfold wVal157
              rw [hs2]
              rfl
            have hv2 : ((P ++ [ac]).foldl (stepF (reg 1) (baseOf 0))
                ((none : Option Term), (none : Option Term))).2
                = some (phiNF ac.1 (plus v ac.2)) := by
              rw [foldl_snoc157, stepF_snd_veb88 hf, hs2]
            have hwv : wVal157 (P ++ [ac]) = phiNF ac.1 (plus v ac.2) := by
              unfold wVal157
              rw [hv2]
              rfl
            rw [hwv]
            have hvT : lt v T = true := by
              rw [← hveq]
              exact hvP
            have harg : lt (plus v ac.2) T = true :=
              lt_plus_ap114 hTap hTz hfT hiv hi2 hvT hC
            exact hstep ac.1 _ hi1 h1M (inT_plus hiv hi2)
              (lt_plus_M hiv hi2 hvM h2M) hAB harg
      have hsplit2 : (wcnf (reg 1) (toList u)).1 = (P ++ [ac]) ++ (S' ++ S2) := by
        rw [hsplit', List.append_assoc, List.singleton_append]
      have hrec := ih (P ++ [ac]) S2 hsplit2
        (fun z hz => hS0 z (List.Mem.tail _ hz))
        (fun z hz => hVeb z (List.Mem.tail _ hz)) hv'
      rw [show P ++ ac :: S' = (P ++ [ac]) ++ S' from by
        rw [List.append_assoc, List.singleton_append]]
      exact hrec

/-! ## §157.7 Fold growth on the right side -/

theorem descP_prefix157 : ∀ (l1 l2 : List (Term × Term)),
    descP118 (l1 ++ l2) → descP118 l1 := by
  intro l1
  induction l1 with
  | nil => intro _ _; trivial
  | cons a t ih =>
      intro l2 h
      cases t with
      | nil => trivial
      | cons b r =>
          exact ⟨(h : descP118 (a :: b :: (r ++ l2))).1, ih l2 (h : descP118 (a :: b :: (r ++ l2))).2⟩

theorem lt_one_E81_157 : lt TM.Term.one E081 = true := by decide

theorem le_psi_mono157 {i j : Term} (h : le i j = true) :
    le (psi (reg 1) i) (psi (reg 1) j) = true := by
  rcases (Bool.or_eq_true _ _).mp h with he | hl
  · rw [eq_of_beq he]
    exact Evidence.WF.le_self _
  · have hne : psi (reg 1) i ≠ psi (reg 1) j := by
      intro hc
      injection hc with _ h2
      rw [h2, lt_irrefl] at hl
      exact Bool.noConfusion hl
    refine le_of_lt ?_
    rw [lt_psi_psi100 hne, if_pos rfl]
    exact hl

theorem lt_psi_smono157 {i j : Term} (h : lt i j = true) :
    lt (psi (reg 1) i) (psi (reg 1) j) = true := by
  have hne : psi (reg 1) i ≠ psi (reg 1) j := by
    intro hc
    injection hc with _ h2
    rw [h2, lt_irrefl] at h
    exact Bool.noConfusion h
  rw [lt_psi_psi100 hne, if_pos rfl]
  exact h

theorem le_self_plus157 {i d : Term} (hi : inT i = true) (hd : inT d = true) :
    le i (plus i d) = true := by
  have h := plus_mono_right_inT i hi zero d inT_zero hd (le_zero_left _)
  rwa [plus_nil (show toList (zero : Term) = [] from rfl)] at h

theorem lt_self_plus157 {i d : Term} (hi : inT i = true) (hd : inT d = true)
    (hz : d ≠ zero) : lt i (plus i d) = true := by
  have h1 : lt i (plus i TM.Term.one) = true := lt_self_plus_one_inT i hi
  have h2 : le (plus i TM.Term.one) (plus i d) = true :=
    plus_mono_right_inT i hi TM.Term.one d inT_one hd (le_one157 hd hz)
  exact lt_of_lt_of_le3 (inT_le_fragR _ hi) (inT_le_fragR _ (inT_plus hi inT_one))
    (inT_le_fragR _ (inT_plus hi hd)) h1 h2

/-- **The right side never falls back.**  From the state right after the
    divergence step `y`, folding any further pairs short of the last one keeps
    the value at least `T`. -/
theorem tLe157 {u : Term} (hu : inT u = true) (huM : lt u M = true)
    (Hpu : PsiIdxOK 0 u) {R ty' : List (Term × Term)} {y cb : Term × Term}
    (hsplit : (wcnf (reg 1) (toList u)).1 = R ++ y :: (ty' ++ [cb]))
    {T : Term}
    (hT2 : ((R ++ [y]).foldl (stepF (reg 1) (baseOf 0))
        ((none : Option Term), (none : Option Term))).2 = some T) :
    ∃ v', ((R ++ y :: ty').foldl (stepF (reg 1) (baseOf 0))
        ((none : Option Term), (none : Option Term))).2 = some v' ∧ le T v' = true := by
  obtain ⟨hc, hd⟩ := inT_toList u hu
  have hmL := ltM_toList u hu huM
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList u) hc hd hmL
  have hsplit1 : (wcnf (reg 1) (toList u)).1 = (R ++ [y]) ++ (ty' ++ [cb]) := by
    rw [hsplit, List.append_assoc, List.singleton_append]
  -- T's facts
  have hstE := stE81_pre157 hu huM Hpu (R ++ [y]) (ty' ++ [cb]) hsplit1
  obtain ⟨hiT, hTW, hTap, hTE⟩ := hstE T hT2
  have h1T : lt TM.Term.one T = true :=
    lt_of_lt_of_le3 (show FragR TM.Term.one = true from rfl) (inT_le_fragR _ inT_E81)
      (inT_le_fragR _ hiT) lt_one_E81_157 hTE
  have hTM : lt T M = true := ltM_of_ltW79 hiT hTW
  -- descent and the fired/Veblen split of ty'
  have hdP : descP118 ((wcnf (reg 1) (toList u)).1) := wcnf_descP154 _ hc hd hmL
  have hdPt : descP118 (ty' ++ [cb]) := by
    rw [hsplit1] at hdP
    exact descP_suffix154 _ _ hdP
  have hdty : descP118 ty' := descP_prefix157 _ _ hdPt
  have hmemty : ∀ z ∈ ty', z ∈ (wcnf (reg 1) (toList u)).1 := by
    intro z hz
    rw [hsplit1]
    exact List.mem_append_right _ (List.mem_append_left _ hz)
  obtain ⟨F, V, hFV, hF, hV⟩ := splitFV157 ty' hdty
    (fun z hz => (hallOK z (hmemty z hz)).1)
  -- the value after the fired block dominates T
  have hsplit2 : (wcnf (reg 1) (toList u)).1 = ((R ++ [y]) ++ F) ++ (V ++ [cb]) := by
    have hassoc : ((R ++ [y]) ++ F) ++ (V ++ [cb])
        = (R ++ [y]) ++ ((F ++ V) ++ [cb]) := by
      simp only [List.append_assoc]
    rw [hsplit1, hFV, hassoc]
  obtain ⟨v2, hs22, hTv2⟩ : ∃ v2,
      (((R ++ [y]) ++ F).foldl (stepF (reg 1) (baseOf 0))
        ((none : Option Term), (none : Option Term))).2 = some v2 ∧ le T v2 = true := by
    cases F with
    | nil =>
        rw [List.append_nil]
        exact ⟨T, hT2, Evidence.WF.le_self T⟩
    | cons f F'' =>
        -- the head of the fired block sits in `ty'`, so `y` fires and so does all of `R`
        have hfmem : f ∈ ty' := by
          rw [hFV]
          exact List.mem_append_left _ (List.Mem.head _)
        have hfW : le (reg 1) f.1 = true := hF f (List.Mem.head _)
        have hdPy : descP118 (y :: (ty' ++ [cb])) := by
          rw [hsplit] at hdP
          exact descP_suffix154 _ _ hdP
        have hinY : ∀ w ∈ y :: (ty' ++ [cb]), inT w.1 = true := by
          intro w hw
          refine (hallOK w ?_).1
          rw [hsplit]
          exact List.mem_append_right _ hw
        have hfy : lt f.1 y.1 = true :=
          descP_bound154 (ty' ++ [cb]) y hinY hdPy f (List.mem_append_left _ hfmem)
        have hyW : le (reg 1) y.1 = true := by
          refine le_of_lt ?_
          exact lt_of_le_of_lt3 (inT_le_fragR _ (inT_reg 1))
            (inT_le_fragR _ (hallOK f (hmemty f hfmem)).1)
            (inT_le_fragR _ (hinY y (List.Mem.head _))) hfW hfy
        have hRfire : ∀ z ∈ R, le (reg 1) z.1 = true := by
          intro z hz
          have hyz : lt y.1 z.1 = true := by
            refine descP_cross157 R y (ty' ++ [cb]) ?_ ?_ z hz
            · rw [← hsplit]
              exact hdP
            · intro w hw
              refine (hallOK w ?_).1
              rw [hsplit]
              exact hw
          refine le_of_lt ?_
          refine lt_of_le_of_lt3 (inT_le_fragR _ (inT_reg 1))
            (inT_le_fragR _ (hinY y (List.Mem.head _)))
            (inT_le_fragR _ ?_) hyW hyz
          refine (hallOK z ?_).1
          rw [hsplit]
          exact List.mem_append_left _ hz
        have hRyfire : ∀ z ∈ R ++ [y], le (reg 1) z.1 = true := by
          intro z hz
          rcases List.mem_append.mp hz with h1 | h1
          · exact hRfire z h1
          · rcases List.mem_cons.mp h1 with h2 | h2
            · rw [h2]; exact hyW
            · cases h2
        -- coherence of both states
        have hcoh1 : Coh157 ((R ++ [y]).foldl (stepF (reg 1) (baseOf 0))
            ((none : Option Term), (none : Option Term))) :=
          coh_fold157 _ _ hRyfire rfl
        obtain ⟨i1, hs11⟩ : ∃ i1, ((R ++ [y]).foldl (stepF (reg 1) (baseOf 0))
            ((none : Option Term), (none : Option Term))).1 = some i1 := by
          cases hs1c : ((R ++ [y]).foldl (stepF (reg 1) (baseOf 0))
              ((none : Option Term), (none : Option Term))).1 with
          | none =>
              exfalso
              have h2 := hcoh1
              unfold Coh157 at h2
              rw [hs1c, hT2] at h2
              have h3 : (some T : Option Term) = none := h2
              exact Option.some_ne_none T h3
          | some i1 => exact ⟨i1, rfl⟩
        have hTpsi : T = psi (reg 1) i1 := by
          have h2 := hcoh1
          unfold Coh157 at h2
          rw [hs11, hT2] at h2
          have h3 : (some T : Option Term) = some (psi (reg 1) i1) := h2
          exact Option.some.inj h3
        -- StInv at the (R ++ [y]) prefix, for `inT i1`
        obtain ⟨hstInv1, _⟩ := preSt_inv129 hu huM Hpu (R ++ [y]) (ty' ++ [cb]) hsplit1.symm
        have hi1 : inT i1 = true := (hstInv1.1 i1 hs11).1
        -- fold the fired block with `foldSome120`
        have hinF : ∀ z ∈ (f :: F''), inT z.1 = true ∧ inT z.2 = true := by
          intro z hz
          have h2 := hallOK z (by
            rw [hsplit1]
            refine List.mem_append_right _ (List.mem_append_left _ ?_)
            rw [hFV]
            exact List.mem_append_left _ hz)
          exact ⟨h2.1, h2.2.2.1⟩
        have hs1eta : ((R ++ [y]).foldl (stepF (reg 1) (baseOf 0))
            ((none : Option Term), (none : Option Term)))
            = (some i1, ((R ++ [y]).foldl (stepF (reg 1) (baseOf 0))
                ((none : Option Term), (none : Option Term))).2) := by
          rw [← hs11]
        have hidx2 : (((R ++ [y]) ++ (f :: F'')).foldl (stepF (reg 1) (baseOf 0))
            ((none : Option Term), (none : Option Term))).1
            = some (plus i1 (sumDD112 (reg 1) (f :: F''))) := by
          rw [List.foldl_append, hs1eta]
          exact foldSome120 (inT_reg 1) (f :: F'') hinF hF i1 _ hi1
        have hcoh2 : Coh157 (((R ++ [y]) ++ (f :: F'')).foldl (stepF (reg 1) (baseOf 0))
            ((none : Option Term), (none : Option Term))) := by
          refine coh_fold157 _ _ ?_ rfl
          intro z hz
          rcases List.mem_append.mp hz with h1 | h1
          · exact hRyfire z h1
          · exact hF z h1
        have hs22 : (((R ++ [y]) ++ (f :: F'')).foldl (stepF (reg 1) (baseOf 0))
            ((none : Option Term), (none : Option Term))).2
            = some (psi (reg 1) (plus i1 (sumDD112 (reg 1) (f :: F'')))) := by
          have h2 := hcoh2
          unfold Coh157 at h2
          rw [hidx2] at h2
          exact h2
        refine ⟨psi (reg 1) (plus i1 (sumDD112 (reg 1) (f :: F''))), hs22, ?_⟩
        rw [hTpsi]
        refine le_psi_mono157 ?_
        exact le_self_plus157 hi1 (inT_sumDD112 (inT_reg 1) _ hinF)
  -- Veblen tail: the value never drops below `T`
  obtain ⟨hstInv2, _⟩ := preSt_inv129 hu huM Hpu ((R ++ [y]) ++ F) (V ++ [cb]) hsplit2.symm
  have hap2 : ApV117 (((R ++ [y]) ++ F).foldl (stepF (reg 1) (baseOf 0))
      ((none : Option Term), (none : Option Term))) :=
    apV117_fold _ _ apV117_none
  have hallV : ∀ ac ∈ V, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true
      ∧ lt ac.2 M = true := by
    intro ac hac
    refine hallOK ac ?_
    rw [hsplit2]
    exact List.mem_append_right _ (List.mem_append_left _ hac)
  have hmain := geV117_fold hiT hTap h1T hTM V _ hstInv2 hap2 ⟨v2, hs22, hTv2⟩ hallV hV
  obtain ⟨v', hv'2, hTv'⟩ := hmain
  refine ⟨v', ?_, hTv'⟩
  have heq : R ++ y :: ty' = ((R ++ [y]) ++ F) ++ V := by
    rw [List.append_assoc, List.append_assoc, List.singleton_append, hFV]
  rw [heq, List.foldl_append]
  exact hv'2

/-! ## §157.8 Sums of `Ω₁`-multiples absorb small tails -/

theorem hd_le157 {l c : Term} {r : List Term} (hil : inT l = true)
    (h : toList l = c :: r) : le c l = true := by
  cases r with
  | nil =>
      have hle : l = c := by
        rw [← inT_ofList_toList l hil, h]
        rfl
      rw [hle]
      exact Evidence.WF.le_self c
  | cons b t =>
      have hle : l = add c (ofList (b :: t)) := by
        rw [← inT_ofList_toList l hil, h]
        rfl
      rw [hle]
      exact le_left_add97 (by rw [← hle]; exact hil)

/-- Anything `< Ω₁` sits below a nonzero sum of `≥ Ω₁` components. -/
theorem lt_big_of_ltW157 {v l : Term} (hiv : inT v = true) (hil : inT l = true)
    (hv : ∀ c ∈ toList v, le (reg 1) c = true) (hlW : lt l (reg 1) = true)
    (hvz : v ≠ zero) : lt l v = true := by
  cases hL : toList l with
  | nil =>
      rw [toList_eq_nil l hL]
      exact lt_zero_left hvz
  | cons b1 r =>
      cases hV : toList v with
      | nil => exact absurd (toList_eq_nil v hV) hvz
      | cons d V' =>
          have hib1 : inT b1 = true := inTL_inT hil b1 (by rw [hL]; exact List.Mem.head _)
          have hid : inT d = true := inTL_inT hiv d (by rw [hV]; exact List.Mem.head _)
          have hb1l : le b1 l = true := hd_le157 hil hL
          have hb1W : lt b1 (reg 1) = true :=
            lt_of_le_of_lt3 (inT_le_fragR _ hib1) (inT_le_fragR _ hil)
              (inT_le_fragR _ (inT_reg 1)) hb1l hlW
          have hb1d : lt b1 d = true :=
            lt_of_lt_of_le3 (inT_le_fragR _ hib1) (inT_le_fragR _ (inT_reg 1))
              (inT_le_fragR _ hid) hb1W (hv d (by rw [hV]; exact List.Mem.head _))
          exact lt_of_hd_lt hil hiv hL hV hb1d

/-- Appending a `< Ω₁` term to a sum of `≥ Ω₁` components is plain concatenation. -/
theorem plus_big_toList157 {u l : Term} (hiu : inT u = true) (hil : inT l = true)
    (hu : ∀ c ∈ toList u, le (reg 1) c = true) (hlW : lt l (reg 1) = true) :
    plus u l = ofList (toList u ++ toList l) := by
  cases hL : toList l with
  | nil =>
      rw [plus_nil hL, List.append_nil, inT_ofList_toList u hiu]
  | cons b1 rest =>
      show (match toList l with
            | [] => u
            | b1 :: _ => ofList ((toList u).filter (fun a => le b1 a) ++ toList l)) = _
      rw [hL]
      dsimp only
      have hib1 : inT b1 = true := inTL_inT hil b1 (by rw [hL]; exact List.Mem.head _)
      have hb1l : le b1 l = true := hd_le157 hil hL
      have hb1W : lt b1 (reg 1) = true :=
        lt_of_le_of_lt3 (inT_le_fragR _ hib1) (inT_le_fragR _ hil)
          (inT_le_fragR _ (inT_reg 1)) hb1l hlW
      have hfilt : (toList u).filter (fun a => le b1 a) = toList u := by
        refine List.filter_eq_self.mpr ?_
        intro a ha
        have hia : inT a = true := inTL_inT hiu a ha
        exact le_of_lt (lt_of_lt_of_le3 (inT_le_fragR _ hib1)
          (inT_le_fragR _ (inT_reg 1)) (inT_le_fragR _ hia) hb1W (hu a ha))
      rw [hfilt]

/-- **Absorption**: if `u < v` and both are sums of `≥ Ω₁` components, adding
    any `< Ω₁` tail to `u` keeps it below `v`. -/
theorem plus_lt_big157 : ∀ (n : Nat) (u v l : Term), (toList u).length ≤ n →
    inT u = true → inT v = true → inT l = true →
    (∀ c ∈ toList u, le (reg 1) c = true) → (∀ c ∈ toList v, le (reg 1) c = true) →
    lt l (reg 1) = true → lt u v = true → lt (plus u l) v = true := by
  intro n
  induction n with
  | zero =>
      intro u v l hn hiu hiv hil hu hv hlW huv
      cases hU : toList u with
      | nil =>
          rw [toList_eq_nil u hU, plus_zero_left_inT hil]
          have hvz : v ≠ zero := by
            intro hc
            rw [hc, lt_zero_right] at huv
            exact Bool.noConfusion huv
          exact lt_big_of_ltW157 hiv hil hv hlW hvz
      | cons c U' =>
          exfalso
          rw [hU] at hn
          simp at hn
  | succ n ih =>
      intro u v l hn hiu hiv hil hu hv hlW huv
      cases hU : toList u with
      | nil =>
          rw [toList_eq_nil u hU, plus_zero_left_inT hil]
          have hvz : v ≠ zero := by
            intro hc
            rw [hc, lt_zero_right] at huv
            exact Bool.noConfusion huv
          exact lt_big_of_ltW157 hiv hil hv hlW hvz
      | cons c U' =>
          have hvz : v ≠ zero := by
            intro hc
            rw [hc, lt_zero_right] at huv
            exact Bool.noConfusion huv
          cases hV : toList v with
          | nil => exact absurd (toList_eq_nil v hV) hvz
          | cons d V' =>
              have hic : inT c = true := inTL_inT hiu c (by rw [hU]; exact List.Mem.head _)
              have hid : inT d = true := inTL_inT hiv d (by rw [hV]; exact List.Mem.head _)
              -- shared plumbing
              have hcu := (inT_toList u hiu).1
              have hdu := (inT_toList u hiu).2
              have hcl := (inT_toList l hil).1
              have hplTL : plus u l = ofList (toList u ++ toList l) :=
                plus_big_toList157 hiu hil hu hlW
              have hLL : inTL (toList u ++ toList l) = true := inTL_append89 hcu hcl
              have hplt : toList (plus u l) = c :: (U' ++ toList l) := by
                rw [hplTL, toList_ofList89 hLL, hU]
                rfl
              by_cases hcd : (c == d) = true
              · have hceq : c = d := eq_of_beq hcd
                rw [← hceq] at hV
                -- tails
                have hcU' : inTL U' = true := by
                  have h2 := hcu
                  rw [hU] at h2
                  exact (inTL_cons.mp h2).2
                have hdU' : descL U' = true := by
                  have h2 := hdu
                  rw [hU] at h2
                  exact descL_tail h2
                have hcV' : inTL V' = true := by
                  have h2 := (inT_toList v hiv).1
                  rw [hV] at h2
                  exact (inTL_cons.mp h2).2
                have hdV' : descL V' = true := by
                  have h2 := (inT_toList v hiv).2
                  rw [hV] at h2
                  exact descL_tail h2
                have hiu' : inT (ofList U') = true := inT_ofList U' hcU' hdU'
                have hiv' : inT (ofList V') = true := inT_ofList V' hcV' hdV'
                have htu' : toList (ofList U') = U' := toList_ofList89 hcU'
                have htv' : toList (ofList V') = V' := toList_ofList89 hcV'
                have htails : lt (ofList U') (ofList V') = true :=
                  lt_hd_eq_inv89 hiu hiv hU hV hiu' hiv' htu' htv' huv
                have hlen : (toList (ofList U')).length ≤ n := by
                  rw [htu']
                  rw [hU, List.length_cons] at hn
                  omega
                have hu' : ∀ x ∈ toList (ofList U'), le (reg 1) x = true := by
                  intro x hx
                  rw [htu'] at hx
                  exact hu x (by rw [hU]; exact List.Mem.tail _ hx)
                have hv' : ∀ x ∈ toList (ofList V'), le (reg 1) x = true := by
                  intro x hx
                  rw [htv'] at hx
                  exact hv x (by rw [hV]; exact List.Mem.tail _ hx)
                have hrec : lt (plus (ofList U') l) (ofList V') = true :=
                  ih (ofList U') (ofList V') l hlen hiu' hiv' hil hu' hv' hlW htails
                have hrebuild : plus (ofList U') l = ofList (U' ++ toList l) := by
                  have h2 := plus_big_toList157 hiu' hil hu' hlW
                  rw [htu'] at h2
                  exact h2
                exact lt_of_hd_eq77 (inT_plus hiu hil) hiv hplt hV
                  (by rw [← hrebuild]; exact hrec)
              · by_cases hlt : lt c d = true
                · exact lt_of_hd_lt (inT_plus hiu hil) hiv hplt hV hlt
                · exfalso
                  have hled : le c d = false := by
                    show ((c == d) || lt c d) = false
                    rw [bool_false (fun hcc => hcd hcc), bool_false (fun hcc => hlt hcc)]
                    rfl
                  have hdc : lt d c = true := lt_of_not_le_inT hic hid hled
                  have hvu : lt v u = true := lt_of_hd_lt hiv hiu hV hU hdc
                  rw [lt_asymm_inT hiv hiu hvu] at huv
                  exact Bool.noConfusion huv

/-! ## §157.9 Fired-index domination -/

theorem le_omegaNF157 {x y : Term} (hx : inT x = true) (hy : inT y = true)
    (h : le x y = true) : le (omegaNF x) (omegaNF y) = true := by
  rcases (Bool.or_eq_true _ _).mp h with he | hl
  · rw [eq_of_beq he]
    exact Evidence.WF.le_self _
  · exact le_of_lt (lt_omegaNF_inT79 hx hy hl)

theorem comp_le157 {t p : Term} (hit : inT t = true) (hp : p ∈ toList t) :
    le p t = true := by
  cases hL : toList t with
  | nil => rw [hL] at hp; cases hp
  | cons c r =>
      have hp2 : p ∈ c :: r := by rw [← hL]; exact hp
      have hcle : le c t = true := hd_le157 hit hL
      have hcu := (inT_toList t hit).1
      have hdu := (inT_toList t hit).2
      rw [hL] at hcu hdu
      have hic : inT c = true := (inTL_cons.mp hcu).1.2
      rcases List.mem_cons.mp hp2 with h1 | h1
      · rw [h1]; exact hcle
      · have hple : le p c = true :=
          descL_bound_inT r c hic (inTL_cons.mp hcu).2 hdu p h1
        have hip : inT p = true := inTL_inT hit p hp
        exact le_trans3 (inT_le_fragR _ hip) (inT_le_fragR _ hic)
          (inT_le_fragR _ hit) hple hcle

/-- A fired exponent has a `≥ Ω₁` head component. -/
theorem fired_head157 {A : Term} (hiA : inT A = true) (hW : le (reg 1) A = true) :
    ∃ b s, toList A = b :: s ∧ lt b (reg 1) = false := by
  cases hL : toList A with
  | nil =>
      exfalso
      have hz : A = zero := toList_eq_nil A hL
      rw [hz] at hW
      exact Term.noConfusion (reg1_eq100.symm.trans (le_zero_eq116 hW))
  | cons b s =>
      have hib : inT b = true := inTL_inT hiA b (by rw [hL]; exact List.Mem.head _)
      have hle : le (reg 1) b = true :=
        le_hd_of_le_ap117 (inT_reg 1) (show (reg 1 : Term).isAP = true from rfl) hiA hL hW
      exact ⟨b, s, rfl, lt_false_of_le120 (inT_reg 1) hib hle⟩

theorem inTL_map_omegaNF157 {s : Term} (his : inT s = true) :
    inTL ((toList s).map (fun p => omegaNF (plus (reg 1) (logOm p)))) = true := by
  show (((toList s).map _).all _) = true
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hx
  have hip : inT p = true := inTL_inT his p hp
  have h1 : inT (omegaNF (plus (reg 1) (logOm p))) = true :=
    inT_omegaNF (inT_plus (inT_reg 1) (inT_logOm hip))
  rw [← hpe]
  show ((omegaNF (plus (reg 1) (logOm p))).isAP && inT (omegaNF (plus (reg 1) (logOm p)))) = true
  rw [isAP_omegaNF, h1]
  rfl

/-- Every component of `Ω₁·s` is `≥ Ω₁`. -/
theorem mulLW_comp_ge157 {s : Term} (his : inT s = true) {c : Term}
    (hc : c ∈ toList (mulL (reg 1) s)) : le (reg 1) c = true := by
  have hTL : toList (mulL (reg 1) s)
      = (toList s).map (fun p => omegaNF (plus (reg 1) (logOm p))) := by
    show toList (ofList _) = _
    exact toList_ofList89 (inTL_map_omegaNF157 his)
  rw [hTL] at hc
  obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hc
  have hip : inT p = true := inTL_inT his p hp
  have hle : le (reg 1) (plus (reg 1) (logOm p)) = true :=
    le_self_plus157 (inT_reg 1) (inT_logOm hip)
  have h3 : le (omegaNF (reg 1)) (omegaNF (plus (reg 1) (logOm p))) = true :=
    le_omegaNF157 (inT_reg 1) (inT_plus (inT_reg 1) (inT_logOm hip)) hle
  rw [omegaNF_reg1_80] at h3
  rw [← hpe]
  exact h3

/-- **The exponent absorption**: `Ω₁·(z₁ ⊖ Ω₁) ⊕ l < Ω₁·(y₁ ⊖ Ω₁)` for fired
    `z₁ < y₁` and any `l < Ω₁`. -/
theorem expLt157 {z1 y1 l : Term} (hiz : inT z1 = true) (hzM : lt z1 M = true)
    (hiy : inT y1 = true) (hyM : lt y1 M = true)
    (hzW : le (reg 1) z1 = true) (hyW : le (reg 1) y1 = true)
    (hzy : lt z1 y1 = true)
    (hil : inT l = true) (hlW : lt l (reg 1) = true) :
    lt (plus (mulL (reg 1) (subAP (reg 1) z1)) l)
      (mulL (reg 1) (subAP (reg 1) y1)) = true := by
  obtain ⟨bz, sz, hLz, hbz⟩ := fired_head157 hiz hzW
  obtain ⟨by_, sy, hLy, hby⟩ := fired_head157 hiy hyW
  have hs : lt (subAP (reg 1) z1) (subAP (reg 1) y1) = true :=
    subAP_smono154 hiz hiy hLz hLy hbz hby hzy
  have hE : lt (mulL (reg 1) (subAP (reg 1) z1))
      (mulL (reg 1) (subAP (reg 1) y1)) = true :=
    mulL_smono_right110 (inT_reg 1) (inT_subAP hiz) (inT_subAP hiy)
      (ltM_subAP hiz hzM) (ltM_subAP hiy hyM) hs
  exact plus_lt_big157 ((toList (mulL (reg 1) (subAP (reg 1) z1))).length) _ _ _
    (Nat.le_refl _) (inT_mulL mulDescInT (inT_reg 1) (inT_subAP hiz))
    (inT_mulL mulDescInT (inT_reg 1) (inT_subAP hiy)) hil
    (fun c hc => mulLW_comp_ge157 (inT_subAP hiz) hc)
    (fun c hc => mulLW_comp_ge157 (inT_subAP hiy) hc) hlW hE

/-- One fired pair's `Δ` with exponent below `y₁` sits below `ω^{Ω₁·(y₁ ⊖ Ω₁)}`. -/
theorem dd_lt_omegaE157 {ac : Term × Term} {y1 : Term}
    (hi1 : inT ac.1 = true) (h1M : lt ac.1 M = true)
    (hi2 : inT ac.2 = true) (h2M : lt ac.2 M = true) (h2W : lt ac.2 (reg 1) = true)
    (hiy : inT y1 = true) (hyM : lt y1 M = true)
    (hacW : le (reg 1) ac.1 = true) (hyW : le (reg 1) y1 = true)
    (hlt : lt ac.1 y1 = true) :
    lt (ddOf75 (reg 1) ac) (omegaNF (mulL (reg 1) (subAP (reg 1) y1))) = true := by
  have hiEz : inT (mulL (reg 1) (subAP (reg 1) ac.1)) = true :=
    inT_mulL mulDescInT (inT_reg 1) (inT_subAP hi1)
  have hiEy : inT (mulL (reg 1) (subAP (reg 1) y1)) = true :=
    inT_mulL mulDescInT (inT_reg 1) (inT_subAP hiy)
  have hTLd : ddOf75 (reg 1) ac
      = ofList ((toList ac.2).map (fun p =>
          omegaNF (plus (mulL (reg 1) (subAP (reg 1) ac.1)) (logOm p)))) := rfl
  rw [hTLd]
  refine lt_ofList_ap114 (isAP_omegaNF _) (ne_zero_of_isAP (isAP_omegaNF _)) _ ?_
  intro c hc
  obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hc
  rw [← hpe]
  have hip : inT p = true := inTL_inT hi2 p hp
  have hpAP : p.isAP = true := inTL_isAP hi2 p hp
  have hpM : lt p M = true := ltM_toList ac.2 hi2 h2M p hp
  have hpW : lt p (reg 1) = true :=
    lt_of_le_of_lt3 (inT_le_fragR _ hip) (inT_le_fragR _ hi2)
      (inT_le_fragR _ (inT_reg 1)) (comp_le157 hi2 hp) h2W
  have hlog : lt (logOm p) (reg 1) = true := ltW_logOm106 hip hpAP hpM hpW
  have hexp := expLt157 hi1 h1M hiy hyM hacW hyW hlt (inT_logOm hip) hlog
  exact lt_omegaNF_inT79 (inT_plus hiEz (inT_logOm hip)) hiEy hexp

theorem mulL_one157 (E : Term) : mulL E TM.Term.one = omegaNF E := by
  show ofList [omegaNF (plus E (logOm TM.Term.one))] = omegaNF E
  rw [show logOm TM.Term.one = zero from rfl,
    plus_nil (show toList (zero : Term) = [] from rfl)]
  rfl

theorem sumDD_lt_ap157 {S : Term} (hSap : S.isAP = true) (hSz : S ≠ zero)
    (hfS : FragR S = true) :
    ∀ (F : List (Term × Term)),
      (∀ z ∈ F, inT z.1 = true ∧ inT z.2 = true) →
      (∀ z ∈ F, lt (ddOf75 (reg 1) z) S = true) →
      lt (sumDD112 (reg 1) F) S = true
  | [], _, _ => lt_zero_left hSz
  | z :: F', hin, hlt => by
      rw [sumDD_cons112]
      exact lt_plus_ap114 hSap hSz hfS
        (inT_ddOf75 (inT_reg 1) (hin z (List.Mem.head _)).1 (hin z (List.Mem.head _)).2)
        (inT_sumDD112 (inT_reg 1) F' (fun a ha => hin a (List.Mem.tail _ ha)))
        (hlt z (List.Mem.head _))
        (sumDD_lt_ap157 hSap hSz hfS F' (fun a ha => hin a (List.Mem.tail _ ha))
          (fun a ha => hlt a (List.Mem.tail _ ha)))

/-- **Δ-sum domination.**  A lexicographically smaller fired head followed by a
    strictly smaller fired tail accumulates less than the single bigger pair. -/
theorem sumDD_lt157 {x y : Term × Term} {F : List (Term × Term)}
    (hix1 : inT x.1 = true) (hx1M : lt x.1 M = true)
    (hix2 : inT x.2 = true) (hx2M : lt x.2 M = true) (hx2W : lt x.2 (reg 1) = true)
    (hiy1 : inT y.1 = true) (hy1M : lt y.1 M = true)
    (hiy2 : inT y.2 = true) (hy2M : lt y.2 M = true) (hy2z : y.2 ≠ zero)
    (hxW : le (reg 1) x.1 = true) (hyW : le (reg 1) y.1 = true)
    (hinF : ∀ z ∈ F, inT z.1 = true ∧ lt z.1 M = true ∧ inT z.2 = true
      ∧ lt z.2 M = true ∧ lt z.2 (reg 1) = true)
    (hFW : ∀ z ∈ F, le (reg 1) z.1 = true)
    (hFx : ∀ z ∈ F, lt z.1 x.1 = true)
    (hdiv : lt x.1 y.1 = true ∨ (x.1 = y.1 ∧ lt x.2 y.2 = true)) :
    lt (sumDD112 (reg 1) (x :: F)) (ddOf75 (reg 1) y) = true := by
  have hiDy : inT (ddOf75 (reg 1) y) = true := inT_ddOf75 (inT_reg 1) hiy1 hiy2
  rcases hdiv with hlt | ⟨heq, hC⟩
  · -- strict exponent drop: everything sits below ω^{Ω₁·(y₁ ⊖ Ω₁)} ≤ Δ_y
    have hiEy : inT (mulL (reg 1) (subAP (reg 1) y.1)) = true :=
      inT_mulL mulDescInT (inT_reg 1) (inT_subAP hiy1)
    have hbound : ∀ z ∈ (x :: F),
        lt (ddOf75 (reg 1) z) (omegaNF (mulL (reg 1) (subAP (reg 1) y.1))) = true := by
      intro z hz
      rcases List.mem_cons.mp hz with h1 | h1
      · rw [h1]
        exact dd_lt_omegaE157 hix1 hx1M hix2 hx2M hx2W hiy1 hy1M hxW hyW hlt
      · obtain ⟨hz1, hz1M, hz2, hz2M, hz2W⟩ := hinF z h1
        exact dd_lt_omegaE157 hz1 hz1M hz2 hz2M hz2W hiy1 hy1M (hFW z h1) hyW
          (lt_trans_inT hz1 hix1 hiy1 (hFx z h1) hlt)
    have hin' : ∀ z ∈ (x :: F), inT z.1 = true ∧ inT z.2 = true := by
      intro z hz
      rcases List.mem_cons.mp hz with h1 | h1
      · rw [h1]; exact ⟨hix1, hix2⟩
      · exact ⟨(hinF z h1).1, (hinF z h1).2.2.1⟩
    have hsum := sumDD_lt_ap157 (isAP_omegaNF _)
      (ne_zero_of_isAP (isAP_omegaNF _))
      (inT_le_fragR _ (inT_omegaNF hiEy)) (x :: F) hin' hbound
    have hle2 : le (omegaNF (mulL (reg 1) (subAP (reg 1) y.1)))
        (ddOf75 (reg 1) y) = true := by
      have h2 : le (mulL (mulL (reg 1) (subAP (reg 1) y.1)) TM.Term.one)
          (mulL (mulL (reg 1) (subAP (reg 1) y.1)) y.2) = true :=
        le_mulL_mono115 hiEy inT_one hiy2 lt_one_M hy2M (le_one157 hiy2 hy2z)
      rw [mulL_one157] at h2
      exact h2
    exact lt_of_lt_of_le3
      (inT_le_fragR _ (inT_sumDD112 (inT_reg 1) _ hin'))
      (inT_le_fragR _ (inT_omegaNF hiEy)) (inT_le_fragR _ hiDy) hsum hle2
  · -- equal exponents, coefficient drop
    have hiE : inT (mulL (reg 1) (subAP (reg 1) x.1)) = true :=
      inT_mulL mulDescInT (inT_reg 1) (inT_subAP hix1)
    have hEeq : subAP (reg 1) x.1 = subAP (reg 1) y.1 := by rw [heq]
    have hplus1 : le (plus x.2 TM.Term.one) y.2 = true := by
      rw [plus_one_eq_succT_inT hix2]
      exact le_succT_of_lt_inT x.2 hix2 y.2 hiy2 hC
    cases F with
    | nil =>
        rw [sumDD_cons112, show sumDD112 (reg 1) [] = zero from rfl,
          plus_nil (show toList (zero : Term) = [] from rfl)]
        show lt (mulL (mulL (reg 1) (subAP (reg 1) x.1)) x.2) (ddOf75 (reg 1) y) = true
        rw [hEeq]
        exact mulL_smono_right110
          (inT_mulL mulDescInT (inT_reg 1) (inT_subAP hiy1)) hix2 hiy2 hx2M hy2M hC
    | cons f F'' =>
        rw [sumDD_cons112]
        have hinF' : ∀ z ∈ (f :: F''), inT z.1 = true ∧ inT z.2 = true :=
          fun z hz => ⟨(hinF z hz).1, (hinF z hz).2.2.1⟩
        have hboundF : ∀ z ∈ (f :: F''),
            lt (ddOf75 (reg 1) z) (omegaNF (mulL (reg 1) (subAP (reg 1) x.1))) = true := by
          intro z hz
          obtain ⟨hz1, hz1M, hz2, hz2M, hz2W⟩ := hinF z hz
          exact dd_lt_omegaE157 hz1 hz1M hz2 hz2M hz2W hix1 hx1M (hFW z hz) hxW (hFx z hz)
        have hsumF := sumDD_lt_ap157 (isAP_omegaNF _)
          (ne_zero_of_isAP (isAP_omegaNF _))
          (inT_le_fragR _ (inT_omegaNF hiE)) (f :: F'') hinF' hboundF
        have hiDx : inT (ddOf75 (reg 1) x) = true := inT_ddOf75 (inT_reg 1) hix1 hix2
        have hstep1 : lt (plus (ddOf75 (reg 1) x) (sumDD112 (reg 1) (f :: F'')))
            (plus (ddOf75 (reg 1) x)
              (omegaNF (mulL (reg 1) (subAP (reg 1) x.1)))) = true :=
          plus_smono_right_inT79 _ hiDx _ _
            (inT_sumDD112 (inT_reg 1) _ hinF') (inT_omegaNF hiE) hsumF
        have hstep2 : plus (ddOf75 (reg 1) x)
              (omegaNF (mulL (reg 1) (subAP (reg 1) x.1)))
            = mulL (mulL (reg 1) (subAP (reg 1) x.1)) (plus x.2 TM.Term.one) := by
          rw [mulL_distrib112 hiE hix2 inT_one hx2M lt_one_M, mulL_one157]
          rfl
        have hstep3 : le (mulL (mulL (reg 1) (subAP (reg 1) x.1)) (plus x.2 TM.Term.one))
            (ddOf75 (reg 1) y) = true := by
          show le (mulL (mulL (reg 1) (subAP (reg 1) x.1)) (plus x.2 TM.Term.one))
            (mulL (mulL (reg 1) (subAP (reg 1) y.1)) y.2) = true
          rw [← hEeq]
          exact le_mulL_mono115 hiE (inT_plus hix2 inT_one) hiy2
            (lt_plus_M hix2 inT_one hx2M lt_one_M) hy2M hplus1
        rw [hstep2] at hstep1
        exact lt_of_lt_of_le3
          (inT_le_fragR _ (inT_plus hiDx (inT_sumDD112 (inT_reg 1) _ hinF')))
          (inT_le_fragR _ (inT_mulL mulDescInT hiE (inT_plus hix2 inT_one)))
          (inT_le_fragR _ hiDy) hstep1 hstep3

/-- **The index after `a`'s fired block is below the index of `b`'s step `y`.** -/
theorem idxLt157 {sR : Option Term × Option Term} {x y : Term × Term}
    {F : List (Term × Term)}
    (hix1 : inT x.1 = true) (hx1M : lt x.1 M = true)
    (hix2 : inT x.2 = true) (hx2M : lt x.2 M = true) (hx2W : lt x.2 (reg 1) = true)
    (hx2z : x.2 ≠ zero)
    (hiy1 : inT y.1 = true) (hy1M : lt y.1 M = true)
    (hiy2 : inT y.2 = true) (hy2M : lt y.2 M = true) (hy2z : y.2 ≠ zero)
    (hxW : le (reg 1) x.1 = true) (hyW : le (reg 1) y.1 = true)
    (hinF : ∀ z ∈ F, inT z.1 = true ∧ lt z.1 M = true ∧ inT z.2 = true
      ∧ lt z.2 M = true ∧ lt z.2 (reg 1) = true)
    (hFW : ∀ z ∈ F, le (reg 1) z.1 = true)
    (hFx : ∀ z ∈ F, lt z.1 x.1 = true)
    (hdiv : lt x.1 y.1 = true ∨ (x.1 = y.1 ∧ lt x.2 y.2 = true))
    (hsR : sR = ((none : Option Term), (none : Option Term))
      ∨ ∃ i0, sR.1 = some i0 ∧ inT i0 = true) :
    ∃ ia, ((x :: F).foldl (stepF (reg 1) (baseOf 0)) sR).1 = some ia
      ∧ lt ia (idxOf (reg 1) sR y) = true := by
  have hinFx : ∀ z ∈ (x :: F), inT z.1 = true ∧ inT z.2 = true := by
    intro z hz
    rcases List.mem_cons.mp hz with h1 | h1
    · rw [h1]; exact ⟨hix1, hix2⟩
    · exact ⟨(hinF z h1).1, (hinF z h1).2.2.1⟩
  have hfireFx : ∀ z ∈ (x :: F), le (reg 1) z.1 = true := by
    intro z hz
    rcases List.mem_cons.mp hz with h1 | h1
    · rw [h1]; exact hxW
    · exact hFW z h1
  have hcore : lt (sumDD112 (reg 1) (x :: F)) (ddOf75 (reg 1) y) = true :=
    sumDD_lt157 hix1 hx1M hix2 hx2M hx2W hiy1 hy1M hiy2 hy2M hy2z hxW hyW
      hinF hFW hFx hdiv
  have hiSum : inT (sumDD112 (reg 1) (x :: F)) = true :=
    inT_sumDD112 (inT_reg 1) _ hinFx
  have hiDy : inT (ddOf75 (reg 1) y) = true := inT_ddOf75 (inT_reg 1) hiy1 hiy2
  have hiDx : inT (ddOf75 (reg 1) x) = true := inT_ddOf75 (inT_reg 1) hix1 hix2
  have hiSumF : inT (sumDD112 (reg 1) F) = true :=
    inT_sumDD112 (inT_reg 1) _ (fun z hz => hinFx z (List.Mem.tail _ hz))
  rcases hsR with hnone | ⟨i0, hs1, hi0⟩
  · -- no index yet: pay the `⊖ 1` and reflect through `1 ⊕ ·`
    subst hnone
    have hfold := foldNone120 (base := baseOf 0) (inT_reg 1) x F hinFx hfireFx
    refine ⟨plus (sub1 (ddOf75 (reg 1) x)) (sumDD112 (reg 1) F), hfold, ?_⟩
    rw [idxOf_none112 rfl]
    -- 1 ⊕ (Δ_x ⊖ 1) = Δ_x  and  1 ⊕ (Δ_y ⊖ 1) = Δ_y
    have hD1x : lt (ddOf75 (reg 1) x) TM.Term.one = false := by
      cases hcc : lt (ddOf75 (reg 1) x) TM.Term.one with
      | false => rfl
      | true => exact absurd (below_one _ hiDx _ hcc) (ddOf_ne_zero84 hx2z)
    have hD1y : lt (ddOf75 (reg 1) y) TM.Term.one = false := by
      cases hcc : lt (ddOf75 (reg 1) y) TM.Term.one with
      | false => rfl
      | true => exact absurd (below_one _ hiDy _ hcc) (ddOf_ne_zero84 hy2z)
    have h1x : plus TM.Term.one (sub1 (ddOf75 (reg 1) x)) = ddOf75 (reg 1) x := by
      rw [sub1_eq_subAP112]
      exact plus_subAP112 inT_one rfl hiDx hD1x
    have h1y : plus TM.Term.one (sub1 (ddOf75 (reg 1) y)) = ddOf75 (reg 1) y := by
      rw [sub1_eq_subAP112]
      exact plus_subAP112 inT_one rfl hiDy hD1y
    have ha1 : plus TM.Term.one (plus (sub1 (ddOf75 (reg 1) x)) (sumDD112 (reg 1) F))
        = sumDD112 (reg 1) (x :: F) := by
      rw [← plus_assoc_inT TM.Term.one (sub1 (ddOf75 (reg 1) x)) (sumDD112 (reg 1) F)
          inT_one (inT_sub1 hiDx) hiSumF, h1x, sumDD_cons112]
    cases hcc : lt (plus (sub1 (ddOf75 (reg 1) x)) (sumDD112 (reg 1) F))
        (sub1 (ddOf75 (reg 1) y)) with
    | true => rfl
    | false =>
        exfalso
        have hle : le (sub1 (ddOf75 (reg 1) y))
            (plus (sub1 (ddOf75 (reg 1) x)) (sumDD112 (reg 1) F)) = true :=
          le_of_not_lt3 (inT_le_fragR _ (inT_plus (inT_sub1 hiDx) hiSumF))
            (inT_le_fragR _ (inT_sub1 hiDy)) hcc
        have h2 := plus_mono_right_inT TM.Term.one inT_one _ _ (inT_sub1 hiDy)
          (inT_plus (inT_sub1 hiDx) hiSumF) hle
        rw [h1y, ha1] at h2
        have h3 := lt_of_lt_of_le3 (inT_le_fragR _ hiSum) (inT_le_fragR _ hiDy)
          (inT_le_fragR _ hiSum) hcore h2
        rw [lt_irrefl] at h3
        exact Bool.noConfusion h3
  · -- an index is present: add on both sides
    have hseta : sR = (some i0, sR.2) := by rw [← hs1]
    have hfold : ((x :: F).foldl (stepF (reg 1) (baseOf 0)) sR).1
        = some (plus i0 (sumDD112 (reg 1) (x :: F))) := by
      rw [hseta]
      exact foldSome120 (inT_reg 1) (x :: F) hinFx hfireFx i0 _ hi0
    refine ⟨plus i0 (sumDD112 (reg 1) (x :: F)), hfold, ?_⟩
    rw [idxOf_some112 hs1]
    exact plus_smono_right_inT79 i0 hi0 _ _ hiSum hiDy hcore

/-! ## §157.10 The two vacuous corners -/

/-- The right list cannot end at the divergence pair while the left tail goes on. -/
theorem tyNil157 (Hp : PsiIdxOKStd172) {a b : BT}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hsA : BT.isStd (BT.D 0 a) = true)
    (hbB : btLe72 1 (BT.D 0 b) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (hse : sameExp145 a b = true)
    {R : List (Term × Term)} {x : Term × Term} {tx : List (Term × Term)}
    {y : Term × Term}
    (e1 : (wcnf (reg 1) (toList (dict a))).1 = R ++ x :: tx)
    (e2 : (wcnf (reg 1) (toList (dict b))).1 = R ++ [y])
    (htx : tx ≠ [])
    (hdiv : lt x.1 y.1 = true ∨ (x.1 = y.1 ∧ lt x.2 y.2 = true)) : False := by
  obtain ⟨hia, hlaM, hpa⟩ := dictFacts151 Hp hbA hsA
  obtain ⟨hib, hlbM, hpb⟩ := dictFacts151 Hp hbB hsB
  obtain ⟨hc, hd⟩ := inT_toList _ hia
  have hmL := ltM_toList _ hia hlaM
  obtain ⟨_, hOKa⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList (dict a)) hc hd hmL
  obtain ⟨hcb, hdb⟩ := inT_toList _ hib
  have hmLb := ltM_toList _ hib hlbM
  obtain ⟨_, hOKb⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList (dict b)) hcb hdb hmLb
  have hdPa := wcnf_descP154 _ hc hd hmL
  cases htxr : tx.reverse with
  | nil =>
      refine htx ?_
      rw [← List.reverse_reverse tx, htxr]
      rfl
  | cons ca txr =>
      have htxe : tx = txr.reverse ++ [ca] := by
        rw [← List.reverse_reverse tx, htxr, List.reverse_cons]
      have hQa : (wcnf (reg 1) (toList (dict a))).1
          = (R ++ x :: txr.reverse) ++ [ca] := by
        rw [e1, htxe, List.append_assoc, List.cons_append]
      obtain ⟨hpva, haca⟩ := prevV_split157 hQa
      obtain ⟨Xa, hlsa⟩ : ∃ X, lastStep129 (dict a) = some (ca.1, X) := by
        cases hpv : prevV151 (dict a) with
        | none => exact ⟨_, lastStep_prev_none151 haca hpv⟩
        | some v => exact ⟨_, lastStep_prev_some151 haca hpv⟩
      obtain ⟨hpvb, hacb⟩ := prevV_split157 e2
      obtain ⟨Xb, hlsb⟩ : ∃ X, lastStep129 (dict b) = some (y.1, X) := by
        cases hpv : prevV151 (dict b) with
        | none => exact ⟨_, lastStep_prev_none151 hacb hpv⟩
        | some v => exact ⟨_, lastStep_prev_some151 hacb hpv⟩
      have hexpEq : ca.1 = y.1 := by
        have he : sameExp145 a b = ((ca.1 : Term) == y.1) := by
          unfold sameExp145
          rw [hlsa, hlsb]
        rw [he] at hse
        exact eq_of_beq hse
      have hdX : descP118 (x :: tx) := by
        rw [e1] at hdPa
        exact descP_suffix154 _ _ hdPa
      have hinX : ∀ w ∈ x :: tx, inT w.1 = true := by
        intro w hw
        refine (hOKa w ?_).1
        rw [e1]
        exact List.mem_append_right _ hw
      have hcatx : ca ∈ tx := by
        rw [htxe]
        exact List.mem_append_right _ (List.Mem.head _)
      have hlast : lt ca.1 x.1 = true := descP_bound154 tx x hinX hdX ca hcatx
      have hxy : le x.1 y.1 = true := by
        rcases hdiv with h | ⟨h, _⟩
        · exact le_of_lt h
        · rw [h]
          exact Evidence.WF.le_self _
      have hix1 : inT x.1 = true := hinX x (List.Mem.head _)
      have hica1 : inT ca.1 = true := hinX ca (List.Mem.tail _ hcatx)
      have hiy1 : inT y.1 = true := by
        refine (hOKb y ?_).1
        rw [e2]
        exact List.mem_append_right _ (List.Mem.head _)
      have hcon : lt ca.1 y.1 = true :=
        lt_of_lt_of_le3 (inT_le_fragR _ hica1) (inT_le_fragR _ hix1)
          (inT_le_fragR _ hiy1) hlast hxy
      rw [← hexpEq, lt_irrefl] at hcon
      exact Bool.noConfusion hcon

/-- The left list cannot end at the divergence pair with equal exponents while
    the right tail goes on. -/
theorem txNil157 (Hp : PsiIdxOKStd172) {a b : BT}
    (hbB : btLe72 1 (BT.D 0 b) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    {R : List (Term × Term)} {x y cb : Term × Term} {ty' : List (Term × Term)}
    (hse : sameExp145 a b = true)
    (e1 : (wcnf (reg 1) (toList (dict a))).1 = R ++ [x])
    (e2 : (wcnf (reg 1) (toList (dict b))).1 = (R ++ y :: ty') ++ [cb])
    (hE : x.1 = y.1) : False := by
  obtain ⟨hib, hlbM, hpb⟩ := dictFacts151 Hp hbB hsB
  obtain ⟨hcb, hdb⟩ := inT_toList _ hib
  have hmLb := ltM_toList _ hib hlbM
  obtain ⟨_, hOKb⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList (dict b)) hcb hdb hmLb
  have hdPb := wcnf_descP154 _ hcb hdb hmLb
  obtain ⟨hpva, haca⟩ := prevV_split157 e1
  obtain ⟨Xa, hlsa⟩ : ∃ X, lastStep129 (dict a) = some (x.1, X) := by
    cases hpv : prevV151 (dict a) with
    | none => exact ⟨_, lastStep_prev_none151 haca hpv⟩
    | some v => exact ⟨_, lastStep_prev_some151 haca hpv⟩
  obtain ⟨hpvb, hacb⟩ := prevV_split157 e2
  obtain ⟨Xb, hlsb⟩ : ∃ X, lastStep129 (dict b) = some (cb.1, X) := by
    cases hpv : prevV151 (dict b) with
    | none => exact ⟨_, lastStep_prev_none151 hacb hpv⟩
    | some v => exact ⟨_, lastStep_prev_some151 hacb hpv⟩
  have hexpEq : x.1 = cb.1 := by
    have he : sameExp145 a b = ((x.1 : Term) == cb.1) := by
      unfold sameExp145
      rw [hlsa, hlsb]
    rw [he] at hse
    exact eq_of_beq hse
  have e2b : (wcnf (reg 1) (toList (dict b))).1 = R ++ y :: (ty' ++ [cb]) := by
    rw [e2, List.append_assoc, List.cons_append]
  have hdY : descP118 (y :: (ty' ++ [cb])) := by
    rw [e2b] at hdPb
    exact descP_suffix154 _ _ hdPb
  have hinY : ∀ w ∈ y :: (ty' ++ [cb]), inT w.1 = true := by
    intro w hw
    refine (hOKb w ?_).1
    rw [e2b]
    exact List.mem_append_right _ hw
  have hcbm : cb ∈ ty' ++ [cb] := List.mem_append_right _ (List.Mem.head _)
  have hlast : lt cb.1 y.1 = true := descP_bound154 (ty' ++ [cb]) y hinY hdY cb hcbm
  rw [← hexpEq, ← hE, lt_irrefl] at hlast
  exact Bool.noConfusion hlast

/-! ## §157.11 The left side, packaged -/

/-- **The left tail stays below the target.**  From `lt (wVal157 P0) T` along an
    all-Veblen suffix `S0` whose exponents stay below the cap `B`, the argument
    of the fold's last step is `< T`. -/
theorem leftLt157 {u : Term} (hu : inT u = true) (huM : lt u M = true)
    (Hpu : PsiIdxOK 0 u)
    (HSub : ∀ P S ac, (wcnf (reg 1) (toList u)).1 = P ++ ac :: S →
        le (reg 1) ac.1 = false → Sub157 ac.1 (wVal157 P) ac.2)
    {T B : Term} (hiT : inT T = true) (hTap : T.isAP = true) (hiB : inT B = true)
    (hstep : ∀ a X, inT a = true → lt a M = true → inT X = true → lt X M = true →
        lt a B = true → lt X T = true → lt (phiNF a X) T = true)
    (hraw : ∀ α ξ : Term, inT α = true → lt α M = true → inT ξ = true → lt ξ M = true →
        lt α B = true → lt ξ T = true → lt (phi α ξ) T = true)
    (P0 S0 : List (Term × Term))
    (hsplit0 : (wcnf (reg 1) (toList u)).1 = P0 ++ S0)
    (hS0V : ∀ z ∈ S0, le (reg 1) z.1 = false)
    (hS0ne : S0 ≠ [])
    (hexp : ∀ P S ac, (wcnf (reg 1) (toList u)).1 = P ++ ac :: S → ac ∈ S0 →
        le (reg 1) ac.1 = false → lt (wVal157 P) T = true → lt ac.1 B = true)
    (hv0 : lt (wVal157 P0) T = true) :
    ∃ pa, lastStep129 u = some pa ∧ lt pa.2 T = true := by
  have hfT : FragR T = true := inT_le_fragR _ hiT
  have hTz : T ≠ zero := by
    intro hcc
    rw [hcc, lt_zero_right] at hv0
    exact Bool.noConfusion hv0
  obtain ⟨hc, hd⟩ := inT_toList u hu
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList u) hc hd
    (ltM_toList u hu huM)
  cases hrev : S0.reverse with
  | nil =>
      exfalso
      refine hS0ne ?_
      rw [← List.reverse_reverse S0, hrev]
      rfl
  | cons ca S0r =>
      have hS0e : S0 = S0r.reverse ++ [ca] := by
        rw [← List.reverse_reverse S0, hrev, List.reverse_cons]
      have hQa : (wcnf (reg 1) (toList u)).1 = (P0 ++ S0r.reverse) ++ [ca] := by
        rw [hsplit0, hS0e, ← List.append_assoc]
      have hcaS0 : ca ∈ S0 := by
        rw [hS0e]
        exact List.mem_append_right _ (List.Mem.head _)
      have hfca : le (reg 1) ca.1 = false := hS0V ca hcaS0
      have hwalk : lt (wVal157 (P0 ++ S0r.reverse)) T = true := by
        refine walk157 hu huM Hpu hiT hTap hiB HSub S0 hstep hraw hexp
          S0r.reverse P0 [ca] ?_ ?_ ?_ hv0
        · rw [hsplit0, hS0e]
        · intro z hz
          rw [hS0e]
          exact List.mem_append_left _ hz
        · intro z hz
          exact hS0V z (by rw [hS0e]; exact List.mem_append_left _ hz)
      have hsplitca : (wcnf (reg 1) (toList u)).1
          = (P0 ++ S0r.reverse) ++ ca :: [] := hQa
      have hACa : lt ca.1 B = true := hexp _ _ ca hsplitca hcaS0 hfca hwalk
      have hmemca : ca ∈ (wcnf (reg 1) (toList u)).1 := by
        rw [hQa]
        exact List.mem_append_right _ (List.Mem.head _)
      obtain ⟨hica1, hca1M, hica2, hca2M⟩ := hallOK ca hmemca
      obtain ⟨hiw, hwW⟩ := wVal_facts157 hu huM Hpu (P0 ++ S0r.reverse) [ca] hQa
      have hCa : lt ca.2 T = true :=
        subLt157 (HSub _ _ ca hsplitca hfca) hiT hTap hica1 hiB hACa hiw hwalk hraw
      obtain ⟨hpva, haca⟩ := prevV_split157 hQa
      cases hpv : prevV151 u with
      | none =>
          refine ⟨_, lastStep_prev_none151 haca hpv, ?_⟩
          show lt (plus (baseOf 0) (sub1 ca.2)) T = true
          exact lt_plus_ap114 hTap hTz hfT (inT_baseOf 0) (inT_sub1 hica2)
            (show lt (baseOf 0) T = true from lt_zero_left hTz)
            (lt_of_le_of_lt3 (inT_le_fragR _ (inT_sub1 hica2)) (inT_le_fragR _ hica2)
              hfT (le_sub1_self75 hica2) hCa)
      | some va =>
          refine ⟨_, lastStep_prev_some151 haca hpv, ?_⟩
          show lt (plus va ca.2) T = true
          have h2 : ((P0 ++ S0r.reverse).foldl (stepF (reg 1) (baseOf 0))
              ((none : Option Term), (none : Option Term))).2 = some va := by
            rw [← hpva]
            exact hpv
          have hva : wVal157 (P0 ++ S0r.reverse) = va := by
            unfold wVal157
            rw [h2]
            rfl
          have hvaT : lt va T = true := by
            rw [← hva]
            exact hwalk
          have hiva : inT va = true := by
            rw [← hva]
            exact hiw
          exact lt_plus_ap114 hTap hTz hfT hiva hica2 hvaT hCa

/-! ## §157.12 THE ASSEMBLY — `Dom154` from the carriers -/

/-- **§157 MAIN.**  The mid-list domination follows from the two standardness
    carriers: every arithmetic ingredient is a theorem. -/
theorem dom154_of_carriers157 (Hp : PsiIdxOKStd172) (HS : Subord157)
    (HE : ExpSubR157) : Dom154 := by
  intro a b hbA hbB hsA hsB hWa hWb hfa hfb hltH hse R x tx y ty e1 e2 hor hdiv
  obtain ⟨hia, hlaM, hpa⟩ := dictFacts151 Hp hbA hsA
  obtain ⟨hib, hlbM, hpb⟩ := dictFacts151 Hp hbB hsB
  obtain ⟨hca, hda⟩ := inT_toList _ hia
  obtain ⟨hcb, hdb⟩ := inT_toList _ hib
  have hmLa := ltM_toList _ hia hlaM
  have hmLb := ltM_toList _ hib hlbM
  obtain ⟨_, hOKa⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList (dict a)) hca hda hmLa
  obtain ⟨_, hOKb⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList (dict b)) hcb hdb hmLb
  have hWpa := wcnf_W79 (toList (dict a)) hca
  have hWpb := wcnf_W79 (toList (dict b)) hcb
  have hNZa := wcnf_cnz109 (inT_reg 1) (isSC_reg_succ 0) (toList (dict a)) hca hda hmLa
  have hNZb := wcnf_cnz109 (inT_reg 1) (isSC_reg_succ 0) (toList (dict b)) hcb hdb hmLb
  have hdPa := wcnf_descP154 (toList (dict a)) hca hda hmLa
  have hdPb := wcnf_descP154 (toList (dict b)) hcb hdb hmLb
  have HSa := HS a hbA hsA
  have HEa := HE a hbA hsA
  have hmemXa : x ∈ (wcnf (reg 1) (toList (dict a))).1 := by
    rw [e1]
    exact List.mem_append_right _ (List.Mem.head _)
  have hmemYb : y ∈ (wcnf (reg 1) (toList (dict b))).1 := by
    rw [e2]
    exact List.mem_append_right _ (List.Mem.head _)
  obtain ⟨hix1, hx1M, hix2, hx2M⟩ := hOKa x hmemXa
  obtain ⟨hiy1, hy1M, hiy2, hy2M⟩ := hOKb y hmemYb
  have hx2W : lt x.2 (reg 1) = true := (hWpa.2 x hmemXa).2
  have hy2W : lt y.2 (reg 1) = true := (hWpb.2 y hmemYb).2
  have hx2z : x.2 ≠ zero := hNZa x hmemXa
  have hy2z : y.2 ≠ zero := hNZb y hmemYb
  have hdXa : descP118 (x :: tx) := by
    have h2 := hdPa
    rw [e1] at h2
    exact descP_suffix154 _ _ h2
  have hinXa : ∀ w ∈ x :: tx, inT w.1 = true := by
    intro w hw
    refine (hOKa w ?_).1
    rw [e1]
    exact List.mem_append_right _ hw
  -- `ty = []` is vacuous
  cases ty with
  | nil =>
      exfalso
      have htx : tx ≠ [] := by
        rcases hor with h | h
        · exact h
        · exact absurd rfl h
      exact tyNil157 Hp hbA hsA hbB hsB hse e1 e2 htx hdiv
  | cons ty0 tyr =>
  -- write `ty = ty' ++ [cb]`
  cases htyR : (ty0 :: tyr).reverse with
  | nil =>
      exfalso
      have h2 := congrArg List.length htyR
      rw [List.length_reverse] at h2
      exact absurd h2 (by simp)
  | cons cb tyr' =>
  have hty' : ty0 :: tyr = tyr'.reverse ++ [cb] := by
    rw [← List.reverse_reverse (ty0 :: tyr), htyR, List.reverse_cons]
  have e2' : (wcnf (reg 1) (toList (dict b))).1
      = R ++ y :: (tyr'.reverse ++ [cb]) := by
    rw [e2, hty']
  have e2s : (wcnf (reg 1) (toList (dict b))).1
      = (R ++ [y]) ++ (tyr'.reverse ++ [cb]) := by
    rw [e2', List.append_assoc, List.singleton_append]
  -- the divergence-step value `T` on the right
  cases hT2 : ((R ++ [y]).foldl (stepF (reg 1) (baseOf 0))
      ((none : Option Term), (none : Option Term))).2 with
  | none =>
      exfalso
      have hne : (R ++ [y] : List (Term × Term)) ≠ [] := by
        cases R with
        | nil => exact List.cons_ne_nil _ _
        | cons r0 R' => exact List.cons_ne_nil _ _
      exact fold_some81 (R ++ [y]) _ hne hT2
  | some T =>
  have hstE := stE81_pre157 hib hlbM hpb (R ++ [y]) (tyr'.reverse ++ [cb]) e2s
  obtain ⟨hiT, hTW, hTap, hTE⟩ := hstE T hT2
  have h1T : lt TM.Term.one T = true :=
    lt_of_lt_of_le3 (show FragR TM.Term.one = true from rfl) (inT_le_fragR _ inT_E81)
      (inT_le_fragR _ hiT) lt_one_E81_157 hTE
  have hTM : lt T M = true := ltM_of_ltW79 hiT hTW
  have hfT : FragR T = true := inT_le_fragR _ hiT
  have hTz : T ≠ zero := by
    intro hcc
    rw [hcc, lt_zero_right] at h1T
    exact Bool.noConfusion h1T
  -- `T ≤ v'` on the right
  obtain ⟨v'b, hv'2, hTv'⟩ := tLe157 hib hlbM hpb e2' hT2
  have hQb : (wcnf (reg 1) (toList (dict b))).1
      = (R ++ y :: tyr'.reverse) ++ [cb] := by
    rw [e2', List.append_assoc, List.cons_append]
  obtain ⟨hpvb, hacb⟩ := prevV_split157 hQb
  have hpvB : prevV151 (dict b) = some v'b := by
    rw [hpvb]
    exact hv'2
  have hstE2 := stE81_pre157 hib hlbM hpb (R ++ y :: tyr'.reverse) [cb] hQb
  obtain ⟨hiv', hv'W, _, _⟩ := hstE2 v'b hv'2
  -- the ψ-target closures (shared by the two fired-`y` regions)
  have hpsiPack : ∀ (i : Term), T = psi (reg 1) i →
      (∀ a' X, inT a' = true → lt a' M = true → inT X = true → lt X M = true →
        lt a' T = true → lt X T = true → lt (phiNF a' X) T = true)
      ∧ (∀ α ξ : Term, inT α = true → lt α M = true → inT ξ = true → lt ξ M = true →
        lt α T = true → lt ξ T = true → lt (phi α ξ) T = true) := by
    intro i hTeq
    constructor
    · intro a' X hia' haM' hiX' hXM' haB hXT
      rw [hTeq] at haB hXT ⊢
      exact lt_phiNF_psi114 (by rw [← hTeq]; exact hfT) hiX' haB hXT
    · intro α ξ _ _ _ _ hαB hξT
      rw [hTeq] at hαB hξT ⊢
      exact lt_phi_psi_of hαB hξT
  -- close the goal from the left-side bound
  have hclose : (∃ pa, lastStep129 (dict a) = some pa ∧ lt pa.2 T = true) →
      tail2_151 (lastStep129 (dict a)) (prevV151 (dict b)) = true := by
    rintro ⟨pa, hls, hpaT⟩
    have hXai := (lastStep_inT129 hia hlaM hpa
      (show lastStep129 (dict a) = some (pa.1, pa.2) from hls)).2.1
    rw [hls, hpvB]
    show lt pa.2 v'b = true
    exact lt_of_lt_of_le3 (inT_le_fragR _ hXai) hfT (inT_le_fragR _ hiv') hpaT hTv'
  cases hxf : le (reg 1) x.1 with
  | false =>
      -- `x` Veblen: the whole left suffix is Veblen
      have hxVW : lt x.1 (reg 1) = true := ltW_of_leW_false128 hix1 hxf
      have hXV : ∀ z ∈ x :: tx, le (reg 1) z.1 = false := by
        intro z hz
        rcases List.mem_cons.mp hz with h1 | h1
        · rw [h1]
          exact hxf
        · exact leW_false157 (hinXa z (List.Mem.tail _ h1))
            (lt_trans_inT (hinXa z (List.Mem.tail _ h1)) hix1 (inT_reg 1)
              (descP_bound154 tx x hinXa hdXa z h1) hxVW)
      cases hyf : le (reg 1) y.1 with
      | true =>
          -- ψ-target, walk from `R` over the whole Veblen suffix
          have hTeq : T = psi (reg 1)
              (idxOf (reg 1) (R.foldl (stepF (reg 1) (baseOf 0))
                ((none : Option Term), (none : Option Term))) y) := by
            have h2 : ((R ++ [y]).foldl (stepF (reg 1) (baseOf 0))
                ((none : Option Term), (none : Option Term))).2
                = some (psi (reg 1) (idxOf (reg 1)
                    (R.foldl (stepF (reg 1) (baseOf 0))
                      ((none : Option Term), (none : Option Term))) y)) := by
              rw [foldl_snoc157, stepF_snd_fire88 hyf]
            exact Option.some.inj (hT2.symm.trans h2)
          obtain ⟨hstepψ, hrawψ⟩ := hpsiPack _ hTeq
          have hexpψ : ∀ P S ac, (wcnf (reg 1) (toList (dict a))).1 = P ++ ac :: S →
              ac ∈ (x :: tx) → le (reg 1) ac.1 = false → lt (wVal157 P) T = true →
              lt ac.1 T = true := by
            intro P S ac hspl _ hf hvP
            exact subRLt157 (HEa P S ac hspl hf) hiT hTap
              (wVal_facts157 hia hlaM hpa P (ac :: S) hspl).1 hvP hrawψ
          -- start value
          have hv0 : lt (wVal157 R) T = true := by
            cases hsR2 : (R.foldl (stepF (reg 1) (baseOf 0))
                ((none : Option Term), (none : Option Term))).2 with
            | none =>
                have hwR : wVal157 R = TM.Term.one := by
                  unfold wVal157
                  rw [hsR2]
                  rfl
                rw [hwR]
                exact h1T
            | some vRv =>
                -- `R` is all fired (from `b`'s descent above `y`)
                have hRfireb : ∀ z ∈ R, le (reg 1) z.1 = true := by
                  intro z hz
                  have hyz : lt y.1 z.1 = true := by
                    refine descP_cross157 R y (tyr'.reverse ++ [cb]) ?_ ?_ z hz
                    · have h2 := hdPb
                      rw [e2'] at h2
                      exact h2
                    · intro w hw
                      refine (hOKb w ?_).1
                      rw [e2']
                      exact hw
                  refine le_of_lt ?_
                  refine lt_of_le_of_lt3 (inT_le_fragR _ (inT_reg 1))
                    (inT_le_fragR _ hiy1) (inT_le_fragR _ ?_) hyf hyz
                  refine (hOKb z ?_).1
                  rw [e2']
                  exact List.mem_append_left _ hz
                have hcohR : Coh157 (R.foldl (stepF (reg 1) (baseOf 0))
                    ((none : Option Term), (none : Option Term))) :=
                  coh_fold157 R _ hRfireb rfl
                cases hsR1 : (R.foldl (stepF (reg 1) (baseOf 0))
                    ((none : Option Term), (none : Option Term))).1 with
                | none =>
                    exfalso
                    have h3 := hcohR
                    unfold Coh157 at h3
                    rw [hsR1, hsR2] at h3
                    have h4 : (some vRv : Option Term) = none := h3
                    exact Option.some_ne_none vRv h4
                | some iR =>
                    have h3 := hcohR
                    unfold Coh157 at h3
                    rw [hsR1, hsR2] at h3
                    have hvRpsi : vRv = psi (reg 1) iR :=
                      Option.some.inj (h3 : (some vRv : Option Term) = some (psi (reg 1) iR))
                    obtain ⟨hstRb, _⟩ := preSt_inv129 hib hlbM hpb R
                      (y :: (tyr'.reverse ++ [cb])) e2'.symm
                    have hiiR : inT iR = true := (hstRb.1 iR hsR1).1
                    have hwR : wVal157 R = vRv := by
                      unfold wVal157
                      rw [hsR2]
                      rfl
                    have hidx : idxOf (reg 1) (R.foldl (stepF (reg 1) (baseOf 0))
                        ((none : Option Term), (none : Option Term))) y
                        = plus iR (ddOf75 (reg 1) y) := idxOf_some112 hsR1
                    have hlt2 : lt iR (idxOf (reg 1) (R.foldl (stepF (reg 1) (baseOf 0))
                        ((none : Option Term), (none : Option Term))) y) = true := by
                      rw [hidx]
                      exact lt_self_plus157 hiiR (inT_ddOf75 (inT_reg 1) hiy1 hiy2)
                        (ddOf_ne_zero84 hy2z)
                    rw [hwR, hTeq, hvRpsi]
                    exact lt_psi_smono157 hlt2
          refine hclose (leftLt157 hia hlaM hpa HSa hiT hTap hiT hstepψ hrawψ
            R (x :: tx) e1 hXV (List.cons_ne_nil x tx) hexpψ hv0)
      | false =>
          -- φ̄-target with exponent `y.1`
          have hyVW : lt y.1 (reg 1) = true := ltW_of_leW_false128 hiy1 hyf
          cases hsR2 : (R.foldl (stepF (reg 1) (baseOf 0))
              ((none : Option Term), (none : Option Term))).2 with
          | none =>
              have hTeq : T = phiNF y.1 (plus (baseOf 0) (sub1 y.2)) := by
                have h2 : ((R ++ [y]).foldl (stepF (reg 1) (baseOf 0))
                    ((none : Option Term), (none : Option Term))).2
                    = some (phiNF y.1 (plus (baseOf 0) (sub1 y.2))) := by
                  rw [foldl_snoc157, stepF_snd_veb88 hyf, hsR2]
                exact Option.some.inj (hT2.symm.trans h2)
              have hiδ : inT (plus (baseOf 0) (sub1 y.2)) = true :=
                inT_plus (inT_baseOf 0) (inT_sub1 hiy2)
              have hδM : lt (plus (baseOf 0) (sub1 y.2)) M = true :=
                lt_plus_M (inT_baseOf 0) (inT_sub1 hiy2) (ltM_baseOf 0)
                  (ltM_sub1 hiy2 hy2M)
              have h1T' : lt TM.Term.one (phiNF y.1 (plus (baseOf 0) (sub1 y.2))) = true := by
                rw [← hTeq]
                exact h1T
              have hTW' : lt (phiNF y.1 (plus (baseOf 0) (sub1 y.2))) (reg 1) = true := by
                rw [← hTeq]
                exact hTW
              have hstepφ : ∀ a' X, inT a' = true → lt a' M = true → inT X = true →
                  lt X M = true → lt a' y.1 = true → lt X T = true →
                  lt (phiNF a' X) T = true := by
                intro a' X hia' haM' hiX' hXM' haB hXT
                rw [hTeq] at hXT ⊢
                exact lt_phiNF_vTgt157 hiy1 hy1M hiδ hδM hia' haM' hiX' h1T' hTW' haB hXT
              have hrawφ : ∀ α ξ : Term, inT α = true → lt α M = true → inT ξ = true →
                  lt ξ M = true → lt α y.1 = true → lt ξ T = true →
                  lt (phi α ξ) T = true := by
                intro α ξ hiα hαM hiξ hξM hαB hξT
                rw [hTeq] at hξT ⊢
                exact lt_phi_vTgt157 hiy1 hiδ hiα hiξ hTW' hαB hξT
              have hwR : wVal157 R = TM.Term.one := by
                unfold wVal157
                rw [hsR2]
                rfl
              rcases hdiv with hxlty | ⟨hxeqy, hxlty2⟩
              · -- strict exponent drop at the divergence
                have hexpφ : ∀ P S ac, (wcnf (reg 1) (toList (dict a))).1 = P ++ ac :: S →
                    ac ∈ (x :: tx) → le (reg 1) ac.1 = false → lt (wVal157 P) T = true →
                    lt ac.1 y.1 = true := by
                  intro P S ac _ hmem _ _
                  rcases List.mem_cons.mp hmem with h1 | h1
                  · rw [h1]
                    exact hxlty
                  · exact lt_trans_inT (hinXa ac (List.Mem.tail _ h1)) hix1 hiy1
                      (descP_bound154 tx x hinXa hdXa ac h1) hxlty
                have hv0 : lt (wVal157 R) T = true := by
                  rw [hwR]
                  exact h1T
                refine hclose (leftLt157 hia hlaM hpa HSa hiT hTap hiy1 hstepφ hrawφ
                  R (x :: tx) e1 hXV (List.cons_ne_nil x tx) hexpφ hv0)
              · -- equal exponents: the first step is `phiMono129`
                have htxne : tx ≠ [] := by
                  intro hcc
                  subst hcc
                  exact txNil157 Hp hbB hsB hse e1 hQb hxeqy
                have hexpφ : ∀ P S ac, (wcnf (reg 1) (toList (dict a))).1 = P ++ ac :: S →
                    ac ∈ tx → le (reg 1) ac.1 = false → lt (wVal157 P) T = true →
                    lt ac.1 y.1 = true := by
                  intro P S ac _ hmem _ _
                  rw [← hxeqy]
                  exact descP_bound154 tx x hinXa hdXa ac hmem
                have hsplit0 : (wcnf (reg 1) (toList (dict a))).1 = (R ++ [x]) ++ tx := by
                  rw [e1, List.append_assoc, List.singleton_append]
                have hVx : wVal157 (R ++ [x])
                    = phiNF x.1 (plus (baseOf 0) (sub1 x.2)) := by
                  unfold wVal157
                  rw [foldl_snoc157, stepF_snd_veb88 hxf, hsR2]
                  rfl
                have hargs : lt (plus (baseOf 0) (sub1 x.2))
                    (plus (baseOf 0) (sub1 y.2)) = true :=
                  plus_smono_right_inT79 (baseOf 0) (inT_baseOf 0) _ _
                    (inT_sub1 hix2) (inT_sub1 hiy2)
                    (sub1_smono154 hix2 hiy2 hx2z hxlty2)
                have hv0 : lt (wVal157 (R ++ [x])) T = true := by
                  rw [hVx, hTeq, hxeqy]
                  exact phiMono129 y.1 _ _ hiy1 hy1M
                    (inT_plus (inT_baseOf 0) (inT_sub1 hix2))
                    (lt_plus_M (inT_baseOf 0) (inT_sub1 hix2) (ltM_baseOf 0)
                      (ltM_sub1 hix2 hx2M))
                    hiδ hδM hargs
                refine hclose (leftLt157 hia hlaM hpa HSa hiT hTap hiy1 hstepφ hrawφ
                  (R ++ [x]) tx hsplit0 (fun z hz => hXV z (List.Mem.tail _ hz))
                  htxne hexpφ hv0)
          | some vR =>
              obtain ⟨hivR, hvRW, hvRap, hvRE⟩ :=
                (stE81_pre157 hib hlbM hpb R (y :: (tyr'.reverse ++ [cb])) e2') vR hsR2
              have hvRM : lt vR M = true := ltM_of_ltW79 hivR hvRW
              have hTeq : T = phiNF y.1 (plus vR y.2) := by
                have h2 : ((R ++ [y]).foldl (stepF (reg 1) (baseOf 0))
                    ((none : Option Term), (none : Option Term))).2
                    = some (phiNF y.1 (plus vR y.2)) := by
                  rw [foldl_snoc157, stepF_snd_veb88 hyf, hsR2]
                exact Option.some.inj (hT2.symm.trans h2)
              have hiδ : inT (plus vR y.2) = true := inT_plus hivR hiy2
              have hδM : lt (plus vR y.2) M = true := lt_plus_M hivR hiy2 hvRM hy2M
              have h1T' : lt TM.Term.one (phiNF y.1 (plus vR y.2)) = true := by
                rw [← hTeq]
                exact h1T
              have hTW' : lt (phiNF y.1 (plus vR y.2)) (reg 1) = true := by
                rw [← hTeq]
                exact hTW
              have hstepφ : ∀ a' X, inT a' = true → lt a' M = true → inT X = true →
                  lt X M = true → lt a' y.1 = true → lt X T = true →
                  lt (phiNF a' X) T = true := by
                intro a' X hia' haM' hiX' hXM' haB hXT
                rw [hTeq] at hXT ⊢
                exact lt_phiNF_vTgt157 hiy1 hy1M hiδ hδM hia' haM' hiX' h1T' hTW' haB hXT
              have hrawφ : ∀ α ξ : Term, inT α = true → lt α M = true → inT ξ = true →
                  lt ξ M = true → lt α y.1 = true → lt ξ T = true →
                  lt (phi α ξ) T = true := by
                intro α ξ hiα hαM hiξ hξM hαB hξT
                rw [hTeq] at hξT ⊢
                exact lt_phi_vTgt157 hiy1 hiδ hiα hiξ hTW' hαB hξT
              have hwR : wVal157 R = vR := by
                unfold wVal157
                rw [hsR2]
                rfl
              have hvRT : lt vR T = true := by
                rw [hTeq]
                exact phiInfl129 y.1 vR (plus vR y.2) hiy1 hy1M hivR hvRM hiδ hδM
                  (lt_self_plus157 hivR hiy2 hy2z)
              rcases hdiv with hxlty | ⟨hxeqy, hxlty2⟩
              · have hexpφ : ∀ P S ac, (wcnf (reg 1) (toList (dict a))).1 = P ++ ac :: S →
                    ac ∈ (x :: tx) → le (reg 1) ac.1 = false → lt (wVal157 P) T = true →
                    lt ac.1 y.1 = true := by
                  intro P S ac _ hmem _ _
                  rcases List.mem_cons.mp hmem with h1 | h1
                  · rw [h1]
                    exact hxlty
                  · exact lt_trans_inT (hinXa ac (List.Mem.tail _ h1)) hix1 hiy1
                      (descP_bound154 tx x hinXa hdXa ac h1) hxlty
                have hv0 : lt (wVal157 R) T = true := by
                  rw [hwR]
                  exact hvRT
                refine hclose (leftLt157 hia hlaM hpa HSa hiT hTap hiy1 hstepφ hrawφ
                  R (x :: tx) e1 hXV (List.cons_ne_nil x tx) hexpφ hv0)
              · have htxne : tx ≠ [] := by
                  intro hcc
                  subst hcc
                  exact txNil157 Hp hbB hsB hse e1 hQb hxeqy
                have hexpφ : ∀ P S ac, (wcnf (reg 1) (toList (dict a))).1 = P ++ ac :: S →
                    ac ∈ tx → le (reg 1) ac.1 = false → lt (wVal157 P) T = true →
                    lt ac.1 y.1 = true := by
                  intro P S ac _ hmem _ _
                  rw [← hxeqy]
                  exact descP_bound154 tx x hinXa hdXa ac hmem
                have hsplit0 : (wcnf (reg 1) (toList (dict a))).1 = (R ++ [x]) ++ tx := by
                  rw [e1, List.append_assoc, List.singleton_append]
                have hVx : wVal157 (R ++ [x]) = phiNF x.1 (plus vR x.2) := by
                  unfold wVal157
                  rw [foldl_snoc157, stepF_snd_veb88 hxf, hsR2]
                  rfl
                have hargs : lt (plus vR x.2) (plus vR y.2) = true :=
                  plus_smono_right_inT79 vR hivR _ _ hix2 hiy2 hxlty2
                have hv0 : lt (wVal157 (R ++ [x])) T = true := by
                  rw [hVx, hTeq, hxeqy]
                  exact phiMono129 y.1 _ _ hiy1 hy1M (inT_plus hivR hix2)
                    (lt_plus_M hivR hix2 hvRM hx2M) hiδ hδM hargs
                refine hclose (leftLt157 hia hlaM hpa HSa hiT hTap hiy1 hstepφ hrawφ
                  (R ++ [x]) tx hsplit0 (fun z hz => hXV z (List.Mem.tail _ hz))
                  htxne hexpφ hv0)
  | true =>
      -- `x` fires, hence `y` fires; `R` is all fired
      have hyf : le (reg 1) y.1 = true := by
        rcases hdiv with h | ⟨h, _⟩
        · exact le_of_lt (lt_of_le_of_lt3 (inT_le_fragR _ (inT_reg 1))
            (inT_le_fragR _ hix1) (inT_le_fragR _ hiy1) hxf h)
        · rw [← h]
          exact hxf
      have hTeq : T = psi (reg 1)
          (idxOf (reg 1) (R.foldl (stepF (reg 1) (baseOf 0))
            ((none : Option Term), (none : Option Term))) y) := by
        have h2 : ((R ++ [y]).foldl (stepF (reg 1) (baseOf 0))
            ((none : Option Term), (none : Option Term))).2
            = some (psi (reg 1) (idxOf (reg 1)
                (R.foldl (stepF (reg 1) (baseOf 0))
                  ((none : Option Term), (none : Option Term))) y)) := by
          rw [foldl_snoc157, stepF_snd_fire88 hyf]
        exact Option.some.inj (hT2.symm.trans h2)
      obtain ⟨hstepψ, hrawψ⟩ := hpsiPack _ hTeq
      have hRfire : ∀ z ∈ R, le (reg 1) z.1 = true := by
        intro z hz
        have hxz : lt x.1 z.1 = true := by
          refine descP_cross157 R x tx ?_ ?_ z hz
          · have h2 := hdPa
            rw [e1] at h2
            exact h2
          · intro w hw
            refine (hOKa w ?_).1
            rw [e1]
            exact hw
        refine le_of_lt ?_
        refine lt_of_le_of_lt3 (inT_le_fragR _ (inT_reg 1)) (inT_le_fragR _ hix1)
          (inT_le_fragR _ ?_) hxf hxz
        refine (hOKa z ?_).1
        rw [e1]
        exact List.mem_append_left _ hz
      obtain ⟨Fa, Va, hFVa, hFaW, hVaV⟩ := splitFV157 tx (descP_tail118 hdXa)
        (fun z hz => hinXa z (List.Mem.tail _ hz))
      have hVane : Va ≠ [] := by
        intro hcc
        rw [hcc, List.append_nil] at hFVa
        cases hrevA : (wcnf (reg 1) (toList (dict a))).1.reverse with
        | nil =>
            have h2 := congrArg List.length hrevA
            rw [List.length_reverse, e1, List.length_append] at h2
            simp at h2
        | cons ca ra =>
            have hcaM : ca ∈ (wcnf (reg 1) (toList (dict a))).1 :=
              List.mem_reverse.mp (by rw [hrevA]; exact List.Mem.head _)
            have hlf := hfa
            unfold lastFire92 at hlf
            rw [hrevA] at hlf
            have hlf2 : le (reg 1) ca.1 = false := hlf
            rw [e1] at hcaM
            rcases List.mem_append.mp hcaM with h1 | h1
            · rw [hRfire ca h1] at hlf2
              exact Bool.noConfusion hlf2
            · rcases List.mem_cons.mp h1 with h2 | h2
              · rw [h2, hxf] at hlf2
                exact Bool.noConfusion hlf2
              · rw [hFVa] at h2
                rw [hFaW ca h2] at hlf2
                exact Bool.noConfusion hlf2
      have hsplitF : (wcnf (reg 1) (toList (dict a))).1 = (R ++ x :: Fa) ++ Va := by
        rw [e1, hFVa, List.append_assoc, List.cons_append]
      have hP0fire : ∀ z ∈ R ++ x :: Fa, le (reg 1) z.1 = true := by
        intro z hz
        rcases List.mem_append.mp hz with h1 | h1
        · exact hRfire z h1
        · rcases List.mem_cons.mp h1 with h2 | h2
          · rw [h2]
            exact hxf
          · exact hFaW z h2
      have hinFa : ∀ z ∈ Fa, inT z.1 = true ∧ lt z.1 M = true ∧ inT z.2 = true
          ∧ lt z.2 M = true ∧ lt z.2 (reg 1) = true := by
        intro z hz
        have hmz : z ∈ (wcnf (reg 1) (toList (dict a))).1 := by
          rw [e1, hFVa]
          exact List.mem_append_right _ (List.Mem.tail _ (List.mem_append_left _ hz))
        obtain ⟨h1, h2, h3, h4⟩ := hOKa z hmz
        exact ⟨h1, h2, h3, h4, (hWpa.2 z hmz).2⟩
      have hFax : ∀ z ∈ Fa, lt z.1 x.1 = true := by
        intro z hz
        exact descP_bound154 tx x hinXa hdXa z (by rw [hFVa]; exact List.mem_append_left _ hz)
      have hcohR : Coh157 (R.foldl (stepF (reg 1) (baseOf 0))
          ((none : Option Term), (none : Option Term))) :=
        coh_fold157 R _ hRfire rfl
      -- the shared state after `R`
      have hsR : (R.foldl (stepF (reg 1) (baseOf 0))
            ((none : Option Term), (none : Option Term)))
          = ((none : Option Term), (none : Option Term))
          ∨ ∃ i0, (R.foldl (stepF (reg 1) (baseOf 0))
              ((none : Option Term), (none : Option Term))).1 = some i0
            ∧ inT i0 = true := by
        cases hsR1 : (R.foldl (stepF (reg 1) (baseOf 0))
            ((none : Option Term), (none : Option Term))).1 with
        | none =>
            refine Or.inl ?_
            have h3 := hcohR
            unfold Coh157 at h3
            rw [hsR1] at h3
            have h4 : (R.foldl (stepF (reg 1) (baseOf 0))
                ((none : Option Term), (none : Option Term))).2 = none := h3
            have h5 : (R.foldl (stepF (reg 1) (baseOf 0))
                  ((none : Option Term), (none : Option Term)))
                = ((R.foldl (stepF (reg 1) (baseOf 0))
                    ((none : Option Term), (none : Option Term))).1,
                   (R.foldl (stepF (reg 1) (baseOf 0))
                    ((none : Option Term), (none : Option Term))).2) := rfl
            rw [hsR1, h4] at h5
            exact h5
        | some i0 =>
            obtain ⟨hstRa, _⟩ := preSt_inv129 hia hlaM hpa R (x :: tx) e1.symm
            exact Or.inr ⟨i0, rfl, (hstRa.1 i0 hsR1).1⟩
      obtain ⟨ia, hfoldia, hialt⟩ := idxLt157 hix1 hx1M hix2 hx2M hx2W hx2z
        hiy1 hy1M hiy2 hy2M hy2z hxf hyf hinFa hFaW hFax hdiv hsR
      have hidxP0 : ((R ++ x :: Fa).foldl (stepF (reg 1) (baseOf 0))
          ((none : Option Term), (none : Option Term))).1 = some ia := by
        rw [List.foldl_append]
        exact hfoldia
      have hcohP0 : Coh157 ((R ++ x :: Fa).foldl (stepF (reg 1) (baseOf 0))
          ((none : Option Term), (none : Option Term))) :=
        coh_fold157 _ _ hP0fire rfl
      have hvalP0 : ((R ++ x :: Fa).foldl (stepF (reg 1) (baseOf 0))
          ((none : Option Term), (none : Option Term))).2 = some (psi (reg 1) ia) := by
        have h3 := hcohP0
        unfold Coh157 at h3
        rw [hidxP0] at h3
        exact h3
      have hwP0 : wVal157 (R ++ x :: Fa) = psi (reg 1) ia := by
        unfold wVal157
        rw [hvalP0]
        rfl
      have hv0 : lt (wVal157 (R ++ x :: Fa)) T = true := by
        rw [hwP0, hTeq]
        exact lt_psi_smono157 hialt
      have hexpψ2 : ∀ P S ac, (wcnf (reg 1) (toList (dict a))).1 = P ++ ac :: S →
          ac ∈ Va → le (reg 1) ac.1 = false → lt (wVal157 P) T = true →
          lt ac.1 T = true := by
        intro P S ac hspl _ hf hvP
        exact subRLt157 (HEa P S ac hspl hf) hiT hTap
          (wVal_facts157 hia hlaM hpa P (ac :: S) hspl).1 hvP hrawψ
      refine hclose (leftLt157 hia hlaM hpa HSa hiT hTap hiT hstepψ hrawψ
        (R ++ x :: Fa) Va hsplitF hVaV hVane hexpψ2 hv0)

/-- Chained to the library consumer: `TailOK151` from the carriers. -/
theorem tailOK151_of_carriers157 (Hp : PsiIdxOKStd172) (HS : Subord157)
    (HE : ExpSubR157) : TailOK151 :=
  tailOK151_of_dom154 Hp (dom154_of_carriers157 Hp HS HE)

/-- And `XMono145` — the second gate's equal-exponent half — from the carriers. -/
theorem xmono145_of_carriers157 (Hp : PsiIdxOKStd172) (HS : Subord157)
    (HE : ExpSubR157) : XMono145 :=
  xmono145_of_dom154 Hp (dom154_of_carriers157 Hp HS HE)

/-! ## §157.13 WHAT REMAINS

`Dom154` now rests on `Subord157 ∧ ExpSubR157` alone — the sweep-separated
standardness carriers (scout-sweep6/8: 0 failures on all 2135 standard Veblen
pairs of the §151 pools; `Subord157` fails on 70/118 pairs once left
`K`-standardness is dropped).  Their proof needs the `dict`/`collapse`-level
structure induction (§128's `vebArgs` machinery is the entry point): the
`ψ_{Ω₁}`-pieces of a Veblen coefficient must be bounded by the fold value of
the pair's own prefix, which is exactly the Term-side carrier of the
`G₀`-condition this project has circled since §133.

The `Classical.choice` in the axiom prints below is inherited from the
read-only library (`wA_mono154` → `wcnf_descP154`, `phiNF_le_phi129` →
`phiMono129`, `lt_self_plus_one_inT`); this file introduces no new axiom and
no classical reasoning of its own. -/

#print axioms dom154_of_carriers157
#print axioms tailOK151_of_carriers157
#print axioms xmono145_of_carriers157

end

end Evidence.Region
