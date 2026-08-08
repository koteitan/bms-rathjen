/-
Rows/TM.lean — the row database of the correspondence table (R1: BMS × T(M))

Policy (see plan/README.md):
  - This file is the single source of truth for the table; table/r1-tm.md is
    generated from it by `gentable`.
  - Only rows that pass the machine checks are listed.  The per-row checks are the
    `#guard`s in the middle of this file, so a successful build means every listed
    row has been verified.

Meaning of the columns:
  hasO : the translation `o` is defined on this matrix and o(M) = t holds (E1).
         The whole domain of `o` is additionally checked over a corpus by
         `checkAll` (E2 order embedding + E3 mutual cofinality), see
         Test/TransTest.lean.
  ev   : the remaining, weaker evidence.  "bisim6" = strict bisimulation to depth 6
         (valid in the region where the expansions and the fundamental sequences
         agree up to the index shift of one).

The generated table itself is written in Japanese, since it is the user-facing
document of this repository; only the comments here are in English.
-/
import Trans.TM
import Evidence.Check
import Evidence.Bisim

namespace Rows

open BMS (Matrix)
open TM (Term)
open TM.Term

/-- One row of the correspondence table. -/
structure Row where
  m : Matrix           -- the BMS matrix
  t : Term             -- the T(M) term
  name : String        -- common name (MathJax)
  hasO : Bool := false -- o(M) = t holds (E1)
  ev : String := ""    -- the remaining, weaker evidence
  note : String := ""

/-- If the term is a natural number n (a sum of n copies of 1 = φ̄00), return n. -/
def natOf? (t : Term) : Option Nat :=
  match t with
  | .zero => some 0
  | _ =>
    let l := toList t
    if l.all (· == one) then some l.length else none

/-- Term → MathJax (for display in the table). -/
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

/-- The rows of the table, in increasing order. -/
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

/-! ## Per-row machine checks (a successful build means every row is verified) -/

-- E1: every row marked `hasO` really has the matching value of `o`
#guard rows.all fun r => !r.hasO || Trans.o? r.m == some r.t

-- bisimulation to depth 6: all rows
#guard rows.all fun r => Evidence.bisim 6 r.m r.t 3

-- the table is sorted, in the BMS order and in the T(M) order alike (an instance of E2)
#guard (rows.zip rows.tail).all fun (a, b) => BMS.cmpM a.m b.m == .lt
#guard (rows.zip rows.tail).all fun (a, b) => lt a.t b.t

-- every term satisfies the formation conditions
#guard rows.all fun r => inT r.t

/-! ## Table generation -/

/-- Evidence name → the file that defines it
    (path relative to table/, as resolved by GitHub). -/
def evLink : String → String
  | "bisim6" => "../lean/Evidence/Bisim.lean"
  | _ => ""

/-- Turn a label into a link (left alone when the path is empty). -/
def linked (label path : String) : String :=
  if path == "" then label else "[" ++ label ++ "](" ++ path ++ ")"

/-- The contents of table/r1-tm.md. -/
def genTable : String :=
  let header :=
"# BMS × Rathjen T(M) 対応表 (R1)

<!-- このファイルは `lean/` の `lake exe gentable` による生成物。手編集しないこと。 -->

順序数表記と見做した BMS (活性化関数を任意化し `[n]` なしで扱う) と、
Rathjen の表記系 $`T(M)`$ (Rathjen, *Proof-theoretic analysis of KPM*,
Arch. Math. Logic 30 (1991), §2) の対応表。
**機械検査を通った行のみ**を掲載する。検査の設計は
[plan/README.md](../plan/README.md) を参照。

エビデンス凡例:

- **$`o`$ 列**: ✅ = 翻訳関数 $`o`$ ([定義](../lean/Trans/TM.lean)) がこの行列で定義され
  $`o(M) = t`$ が成立 (E1)。$`o`$ の定義域全体では
  [コーパス検査](../lean/Evidence/Check.lean) (E2 順序埋め込み・E3 相互共終) 済み。
- **その他の弱いエビデンス**: [bisim6](../lean/Evidence/Bisim.lean) = 深さ 6 の双模倣
  (展開列と基本列が一致する領域で有効)。

実装:
[行 DB と行ごとの検査](../lean/Rows/TM.lean) ·
[BMS の展開](../lean/BMS/Expand.lean) ·
[T(M) の項](../lean/TM/Terms.lean) ·
[T(M) の順序](../lean/TM/Order.lean) ·
[基本列](../lean/TM/FS.lean)

| BMS | $`T(M)`$ | 通称 | $`o`$ | その他の弱いエビデンス | 備考 |
|---|---|---|---|---|---|
"
  let body := String.join <| rows.map fun r =>
    let bms := if r.m.isEmpty then "(空)" else BMS.showMatrix r.m
    "| `" ++ bms ++ "` | $`" ++ tex r.t ++ "`$ | $`" ++ r.name ++ "`$ | " ++
      (if r.hasO then linked "✅" "../lean/Trans/TM.lean" else "") ++ " | " ++
      linked r.ev (evLink r.ev) ++ " | " ++ r.note ++ " |\n"
  header ++ body

end Rows
