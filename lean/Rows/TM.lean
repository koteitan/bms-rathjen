/-
Rows/TM.lean — 対応表の行データベース (R1: BMS × T(M))

方針 (plan/README.md):
  - 表の唯一の情報源はこのファイル。table/r1-tm.md は gentable で生成する。
  - 掲載するのは機械検査を通った行だけ。行ごとの検査は本ファイル末尾の
    #guard で行い、ビルドが通ること = 全行検証済みを意味する。

列の意味:
  hasO : 翻訳関数 o がこの行列で定義され、o(M) = t が成立する (E1)。
         o の定義域全体はコーパス上の checkAll
         (E2 順序埋め込み + E3 相互共終) で検査済み (Test/TransTest.lean)。
  ev   : その他のエビデンス。"bisim6" = 深さ 6 の厳密双模倣
         (展開列と基本列が添字 +1 のずれを除いて一致する領域で有効)。
-/
import Trans.TM
import Evidence.Check
import Evidence.Bisim

namespace Rows

open BMS (Matrix)
open TM (Term)
open TM.Term

/-- 対応表の 1 行 -/
structure Row where
  m : Matrix          -- BMS 行列
  t : Term            -- T(M) 項
  name : String       -- 通称 (MathJax)
  hasO : Bool := false -- o の値の一致 (E1) が成立
  ev : String := ""   -- その他のエビデンス
  note : String := ""

/-- 項が自然数 n (1 = φ̄00 の n 個の和) なら n を返す -/
def natOf? (t : Term) : Option Nat :=
  match t with
  | .zero => some 0
  | _ =>
    let l := toList t
    if l.all (· == one) then some l.length else none

/-- Term → MathJax (表の表示用) -/
def tex (t : Term) : String :=
  match natOf? t with
  | some n => toString n
  | none =>
    match t with
    | .zero => "0"
    | .M => "M"
    | .add a b => tex a ++ "+" ++ tex b
    | .omg a => "\\bar{\\omega}^{" ++ tex a ++ "}"
    | .phi a b =>
      if t == omega then "\\omega"
      else "\\bar{\\varphi}(" ++ tex a ++ "," ++ tex b ++ ")"
    | .psi k a => "\\psi_{" ++ tex k ++ "}(" ++ tex a ++ ")"
    | .Z a => if a == Term.zero then "\\Omega" else "Z(" ++ tex a ++ ")"
  termination_by sizeOf t
  decreasing_by all_goals simp_wf <;> omega

/-- ε₀ = φ̄10 -/
def e0 : Term := phi one zero

/-- 対応表の行 (上から昇順) -/
def rows : List Row := [
  { m := [], t := zero, name := "0", hasO := true, ev := "bisim6", note := "空行列" },
  { m := [[0]], t := one, name := "1", hasO := true, ev := "bisim6" },
  { m := [[0],[0]], t := ofNat 2, name := "2", hasO := true, ev := "bisim6" },
  { m := [[0],[1]], t := omega, name := "\\omega", hasO := true, ev := "bisim6" },
  { m := [[0],[1],[0],[1]], t := add omega omega, name := "\\omega\\cdot 2", hasO := true, ev := "bisim6" },
  { m := [[0],[1],[1]], t := phi zero (ofNat 2), name := "\\omega^2", hasO := true, ev := "bisim6" },
  { m := [[0],[1],[2]], t := phi zero omega, name := "\\omega^\\omega", hasO := true, ev := "bisim6" },
  { m := [[0],[1],[2],[3]], t := phi zero (phi zero omega),
    name := "\\omega^{\\omega^\\omega}", hasO := true, ev := "bisim6" },
  { m := [[0,0],[1,1]], t := e0, name := "\\varepsilon_0", ev := "bisim6",
    note := "2 行の最初の極限" },
  { m := [[0,0],[1,1],[1,0]], t := phi zero e0,
    name := "\\omega^{\\varepsilon_0+1}", ev := "bisim6" }
]

/-! ## 行ごとの機械検査 (ビルドが通ること = 全行検証済み) -/

-- E1: hasO の行はすべて o の値が一致する
#guard rows.all fun r => !r.hasO || Trans.o? r.m == some r.t

-- 双模倣 (深さ 6): 全行
#guard rows.all fun r => Evidence.bisim 6 r.m r.t 3

-- 表の整列: BMS 順・T(M) 順の両方で昇順 (E2 のインスタンス)
#guard (rows.zip rows.tail).all fun (a, b) => BMS.cmpM a.m b.m == .lt
#guard (rows.zip rows.tail).all fun (a, b) => lt a.t b.t

-- 全項が形成条件を満たす
#guard rows.all fun r => inT r.t

/-! ## 表の生成 -/

/-- table/r1-tm.md の中身を生成する -/
def genTable : String :=
  let header :=
"# BMS × Rathjen T(M) 対応表 (R1)

<!-- このファイルは `lean/` の `lake exe gentable` による生成物。手編集しないこと。 -->

順序数表記と見做した BMS (活性化関数を任意化し `[n]` なしで扱う) と、
Rathjen の表記系 $T(M)$ (Rathjen, *Proof-theoretic analysis of KPM*,
Arch. Math. Logic 30 (1991), §2) の対応表。
**機械検査を通った行のみ**を掲載する。検査の設計は
[plan/README.md](../plan/README.md) を参照。

エビデンス凡例:

- **$o$ 列**: ✅ = 翻訳関数 $o$ がこの行列で定義され $o(M) = t$ が成立 (E1)。
  $o$ の定義域全体ではコーパス検査 (E2 順序埋め込み・E3 相互共終) 済み。
- **その他のエビデンス**: bisim6 = 深さ 6 の双模倣
  (展開列と基本列が一致する領域で有効)。

| BMS | $T(M)$ | 通称 | $o$ | その他のエビデンス | 備考 |
|---|---|---|---|---|---|
"
  let body := String.join <| rows.map fun r =>
    let bms := if r.m.isEmpty then "(空)" else BMS.showMatrix r.m
    "| `" ++ bms ++ "` | $" ++ tex r.t ++ "$ | $" ++ r.name ++ "$ | " ++
      (if r.hasO then "✅" else "") ++ " | " ++ r.ev ++ " | " ++ r.note ++ " |\n"
  header ++ body

end Rows
