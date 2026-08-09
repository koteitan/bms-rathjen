/-
Rows/TM.lean — the row database of the correspondence table (R1: BMS × T(M))

Policy (see plan/README.md):
  - This file is the single source of truth for the table; table/r1-tm.md is
    generated from it by `gentable`.
  - Only rows that pass the machine checks are listed.  The per-row checks are the
    `#guard`s in the middle of this file, so a successful build means every listed
    row has been verified.

Meaning of the columns:
  proof : the namespace of Rows/Proofs.lean that proves E3 for this row, i.e.
          `∀ n, o (M[n]) = t[n+1]`.  This is the actual claim of the row, proved
          for every n — the only column that is a proof rather than a check.
  hasO  : the translation `o` is defined on this matrix and o(M) = t holds (E1).
          The whole domain of `o` is additionally checked over a corpus by
          `checkAll` (E2 order embedding + E3 mutual cofinality), see
          Test/TransTest.lean.
  ev    : the remaining, weaker evidence.  "bisim6" = strict bisimulation to depth 6
          (valid in the region where the expansions and the fundamental sequences
          agree up to the index shift of one).
`hasO` and `ev` are finite computations; only `proof` covers all n.

The generated table itself is written in Japanese, since it is the user-facing
document of this repository; only the comments here are in English.
-/
import Trans.TM
import Trans.Pair
import Trans.StageC
import Evidence.Check
import Evidence.Bisim

namespace Rows

open BMS (Matrix)
open TM (Term)
open TM.Term

/-- Version of the table (the repository version of the /commitbump workflow).
    Bump this together with every commit; gentable renders it into the header. -/
def version : String := "v0.1.42"

/-- One row of the correspondence table. -/
structure Row where
  m : Matrix           -- the BMS matrix
  t : Term             -- the T(M) term
  name : String        -- common name (MathJax)
  proof : String := "" -- namespace of the E3 proof in Rows/Proofs.lean ("" = none yet)
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
  { m := [], t := zero, name := "0", proof := "«(empty)»", hasO := true, ev := "bisim6",
    note := "空行列" },
  { m := [[0]], t := one, name := "1", proof := "«(0)»", hasO := true, ev := "bisim6" },
  { m := [[0],[0]], t := ofNat 2, name := "2", proof := "«(0)(0)»", hasO := true, ev := "bisim6" },
  { m := [[0],[1]], t := omega, name := "\\omega", proof := "«(0)(1)»", hasO := true,
    ev := "bisim6" },
  { m := [[0],[1],[0],[1]], t := add omega omega, name := "\\omega\\cdot 2",
    proof := "«(0)(1)(0)(1)»", hasO := true, ev := "bisim6" },
  { m := [[0],[1],[1]], t := phi zero (ofNat 2), name := "\\omega^2",
    proof := "«(0)(1)(1)»", hasO := true, ev := "bisim6" },
  { m := [[0],[1],[2]], t := phi zero omega, name := "\\omega^\\omega",
    proof := "«(0)(1)(2)»", hasO := true, ev := "bisim6" },
  { m := [[0],[1],[2],[3]], t := phi zero (phi zero omega),
    name := "\\omega^{\\omega^\\omega}", proof := "«(0)(1)(2)(3)»", hasO := true,
    ev := "bisim6" },
  { m := [[0,0],[1,1]], t := e0, name := "\\varepsilon_0", proof := "R1",
    hasO := true, ev := "bisim6", note := "2 行の最初の極限" },
  { m := [[0,0],[1,1],[0,0]], t := add e0 one, name := "\\varepsilon_0+1",
    proof := "«(0,0)(1,1)(0,0)»", hasO := true },
  { m := [[0,0],[1,1],[1,0]], t := phi zero e0,
    name := "\\omega^{\\varepsilon_0+1}", proof := "R2", hasO := true, ev := "bisim6" },
  { m := [[0,0],[1,1],[1,1]], t := phi one one, name := "\\varepsilon_1", proof := "R3",
    hasO := true },
  { m := [[0,0],[1,1],[2,0]], t := phi one omega, name := "\\varepsilon_\\omega",
    proof := "R4", hasO := true },
  { m := [[0,0],[1,1],[2,0],[0,0]], t := add (phi one omega) one,
    name := "\\varepsilon_\\omega+1", proof := "«(0,0)(1,1)(2,0)(0,0)»", hasO := true },
  { m := [[0,0],[1,1],[2,0],[2,0]], t := phi one (phi zero (ofNat 2)),
    name := "\\varepsilon_{\\omega^2}", proof := "«(0,0)(1,1)(2,0)(2,0)»", hasO := true },
  { m := [[0,0],[1,1],[2,0],[3,0]], t := phi one (phi zero omega),
    name := "\\varepsilon_{\\omega^\\omega}", proof := "«(0,0)(1,1)(2,0)(3,0)»",
    hasO := true },
  { m := [[0,0],[1,1],[2,0],[3,1]], t := phi one e0,
    name := "\\varepsilon_{\\varepsilon_0}", proof := "R5", hasO := true },
  { m := [[0,0],[1,1],[2,1]], t := phi (ofNat 2) zero, name := "\\zeta_0",
    proof := "R6", hasO := true },
  { m := [[0,0],[1,1],[2,1],[0,0]], t := add (phi (ofNat 2) zero) one,
    name := "\\zeta_0+1", proof := "«(0,0)(1,1)(2,1)(0,0)»", hasO := true },
  { m := [[0,0],[1,1],[2,1],[1,0]], t := phi zero (phi (ofNat 2) zero),
    name := "\\omega^{\\zeta_0+1}", proof := "«(0,0)(1,1)(2,1)(1,0)»", hasO := true },
  { m := [[0,0],[1,1],[2,1],[1,1]], t := phi one (phi (ofNat 2) zero),
    name := "\\varepsilon_{\\zeta_0+1}", proof := "«(0,0)(1,1)(2,1)(1,1)»", hasO := true }
  -- WITHDRAWN (v0.1.42): every row from (0,0)(1,1)(2,1)(2,0) upward — 7 proof-column
  -- rows and the 23 Stage-C rows — was removed after the calibration audit: the
  -- oracle (p-bot's PSS termination translation, computed by pss-proof's PSS.Trans
  -- and pss2bp) refutes their values ((2,1)(2,0) = zeta_omega, (2,1)(2,1) = phi(3,0),
  -- (2,1)(3,1) = Gamma_0, (2,2) = psi_0(Omega_2), ...).  The o?-level theorems remain
  -- in Rows/Proofs*.lean and Evidence/StageB.lean but their semantic readings were
  -- wrong: o? compresses from (2,1)(2,0) upward (appended full-ladder copies read as
  -- additive epsilon-steps instead of Omega-weight jumps).  The audit record is
  -- table/oracle-audit-2026-08-09.txt; the rebuild plan is plan/README.md.
]

/-! ## Per-row machine checks (a successful build means every row is verified) -/

-- E1: every row marked `hasO` really has the matching value of `o`
#guard rows.all fun r => !r.hasO || Trans.o? r.m == some r.t

-- bisimulation to depth 6: exactly the rows that claim it
-- (beyond ε₀ the expansions and the fs are different cofinal sequences,
--  so bisim is only claimed where it holds)
#guard rows.all fun r => r.ev != "bisim6" || Evidence.bisim 6 r.m r.t 3

-- the table is sorted, in the BMS order and in the T(M) order alike (an instance of E2)
#guard (rows.zip rows.tail).all fun (a, b) => BMS.cmpM a.m b.m == .lt
#guard (rows.zip rows.tail).all fun (a, b) => lt a.t b.t

-- rows whose evidence is the Stage-C candidate translation match its value
-- (oStageC? is corpus-checked in Trans/StageC.lean but not yet merged into o?,
--  pending the frontier documented there)
#guard rows.all fun r => r.ev != "oStageC" || Trans.oStageC? r.m == some r.t

-- every term satisfies the formation conditions
#guard rows.all fun r => inT r.t

/-- A region row: asserts a claim about a whole FAMILY of matrices — an interval
    of standard matrices, or a parameterized family — rather than about one matrix.
    Rendered between the ordinary rows, just before the first row whose term
    reaches `boundT`.
    `proof` names a theorem in the file `proofFile` once the general theorem for
    the region is integrated; until then it stays "" and no checkmark is shown. -/
structure RegionRow where
  bms : String         -- display text for the BMS cell
  tm : String          -- display math for the T(M) cell
  nm : String          -- display math for the common-name cell
  boundT : Term        -- exclusive upper bound of the region (insertion point)
  proof : String := "" -- theorem name in `proofFile` ("" = pending)
  proofFile : String := "Evidence/StageA.lean"  -- file of the theorem, relative to lean/
  plainCells : Bool := false -- render tm/nm as plain text (for case-split umbrella rows)
  evLabel : String := ""
  evPath : String := ""
  note : String := ""

/-- The regions covered (or to be covered) by general theorems. -/
def regions : List RegionRow := [
  { bms := "<(0,0)(1,1)",
    tm := "\\lt\\bar{\\varphi}(1,0)",
    nm := "\\lt\\varepsilon_0",
    boundT := e0,
    proof := "e3_general",
    evLabel := "checkAll",
    evPath := "../lean/Test/TransTest.lean",
    note := "区間の全標準行列 (stdSeq) の E3 を一般定理で一括証明" }
  -- WITHDRAWN (v0.1.42): the nine family/umbrella region rows (F1/F2/F3/F4/F5/F6/F7,
  -- successor family, E1 umbrella) were removed with the calibration audit — their
  -- o?-internal theorems are true but the displayed values are miscalibrated from
  -- a >= 2..3 on.  They return with the recalibrated translation.
]

/-! ## Table generation -/

/-- Evidence name → the file that defines it
    (path relative to table/, as resolved by GitHub). -/
def evLink : String → String
  | "bisim6" => "../lean/Evidence/Bisim.lean"
  | "oStageC" => "../lean/Trans/StageC.lean"
  | _ => ""

/-- The matrix literal of a row, spelled exactly as it appears in the source of
    `rows` above.  `gentable` looks this up in this very file to turn each table
    row into a link to the line that defines it. -/
def rowKey (r : Row) : String :=
  "m := [" ++ String.intercalate "," (r.m.map fun c =>
    "[" ++ String.intercalate "," (c.map toString) ++ "]") ++ "]"

/-- Turn a label into a link (left alone when the path is empty). -/
def linked (label path : String) : String :=
  if path == "" then label else "[" ++ label ++ "](" ++ path ++ ")"

/-- Render one region row. -/
def regionLine (regionProofLine : String → String → Option Nat) (g : RegionRow) : String :=
  -- v0.1.41: checkmarks suspended table-wide pending the recalibration
  -- (a systematic miscalibration of o was found from (0,0)(1,1)(2,1)(2,0) upward)
  let proofCell := ""
  let _ := regionProofLine
  let cell (s : String) : String :=
    if g.plainCells || s == "" then s else "$`" ++ s ++ "`$"
  "| **" ++ g.bms ++ "** | " ++ cell g.tm ++ " | " ++ cell g.nm ++ " | " ++
    proofCell ++ " | " ++ linked g.evLabel g.evPath ++ " | " ++ g.note ++ " |\n"

/-- The contents of table/r1-tm.md.
    `lineOf` maps the key of a row (see `rowKey`) to the line of Rows/TM.lean that
    defines it, `proofLine` maps a proof namespace to the file (path relative to
    lean/) and line of the row-proof file that declares it (Rows/Proofs.lean or
    Rows/ProofsB.lean), and `regionProofLine` maps a region proof file and theorem
    name to the line in that file; `gentable` supplies all three by reading those
    files. -/
def genTable (lineOf : String → Option Nat) (proofLine : String → Option (String × Nat))
    (regionProofLine : String → String → Option Nat) : String :=
  let header :=
"# BMS × Rathjen T(M) 対応表 (R1)

<!-- このファイルは `lean/` の `lake exe gentable` による生成物。手編集しないこと。 -->

バージョン: " ++ version ++ "

> **⚠ 警告 (v0.1.41)**: 本表の翻訳 $`o`$ に系統的な較正誤りが発見されたため、
> **証明列 (✅) を全行から一時撤去した**。BMS 順で `(0,0)(1,1)(2,1)(2,0)` 以上の行の
> $`T(M)`$ 値と通称は**誤っている**
> (例: 真の値は $`(0,0)(1,1)(2,1)(2,0) = \\zeta_\\omega`$、
> $`(0,0)(1,1)(2,1)(3,1) = \\Gamma_0`$、$`(0,0)(1,1)(2,2) = \\psi_0(\\Omega_2)`$ —
> P進大好きbot 氏のペア数列停止性証明の変換写像による)。
> それ未満の行は変換写像と一致することを確認済み。表は再構築中。

順序数表記と見做した BMS (活性化関数を任意化し `[n]` なしで扱う) と、
Rathjen の表記系 $`T(M)`$ (Rathjen, *Proof-theoretic analysis of KPM*,
Arch. Math. Logic 30 (1991), §2) の対応表。検査の設計は
[plan/README.md](../plan/README.md) を参照。

エビデンス凡例:

- **証明列**: 一時撤去中 (上記警告を参照)。従来の ✅ は「o?-値についての
  Lean 定理」を意味していたが、o? 自身の較正誤りにより行の意味論
  (行列の順序数 = 表記の値) は保証されないことが判明した。
- **その他の弱いエビデンス** (いずれも有限個の $`n`$ の計算検査であり、
  **較正誤りを検出できない**ことが今回実証された):
  - $`o`$ = 翻訳関数がこの行列で定義され $`o(M) = t`$ が成立 (E1)。
  - bisim6 = 深さ 6 の双模倣 (展開列と基本列が一致する領域で有効)。
  - oStageC = Stage C の候補翻訳 oStageC? の値の一致。

## 対応表

| BMS | $`T(M)`$ | 通称 | 証明 | その他の弱いエビデンス | 備考 |
|---|---|---|---|---|---|
"
  let rowStr (r : Row) : String :=
    let bms := if r.m.isEmpty then "(空)" else BMS.showMatrix r.m
    -- the BMS cell links to the line of Rows/TM.lean that defines this row
    let bmsCell :=
      match lineOf (rowKey r) with
      | some n => "[`" ++ bms ++ "`](../lean/Rows/TM.lean#L" ++ toString n ++ ")"
      | none => "`" ++ bms ++ "`"
    -- v0.1.41: checkmarks suspended table-wide pending the recalibration
    let proofCell := ""
    let _ := proofLine
    -- the weak-evidence column lists o and bisim6, each linked separately
    let weak := String.intercalate "+"
      (((if r.hasO then [linked "o" "../lean/Trans/TM.lean"] else []) ++
        (if r.ev == "" then [] else [linked r.ev (evLink r.ev)])))
    "| " ++ bmsCell ++ " | $`" ++ tex r.t ++ "`$ | $`" ++ r.name ++ "`$ | " ++
      proofCell ++ " | " ++ weak ++ " | " ++ r.note ++ " |\n"
  -- interleave: emit a region row just before the first row whose term reaches its bound
  let step (st : List RegionRow × String) (r : Row) : List RegionRow × String :=
    let (gs, acc) := st
    let due := gs.filter (fun g => le g.boundT r.t)
    let rest := gs.filter (fun g => !(le g.boundT r.t))
    (rest, acc ++ String.join (due.map (regionLine regionProofLine)) ++ rowStr r)
  let (gsLeft, body) := rows.foldl step (regions, "")
  let body := body ++ String.join (gsLeft.map (regionLine regionProofLine))
  let footer :=
"
## 実装

[行 DB と行ごとの検査](../lean/Rows/TM.lean) ·
[BMS の展開](../lean/BMS/Expand.lean) ·
[T(M) の項](../lean/TM/Terms.lean) ·
[T(M) の順序](../lean/TM/Order.lean) ·
[基本列](../lean/TM/FS.lean)
"
  header ++ body ++ footer

end Rows
