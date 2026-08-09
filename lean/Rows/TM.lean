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
def version : String := "v0.1.28"

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
  { m := [[0,0],[1,1],[2,0],[3,1]], t := phi one e0,
    name := "\\varepsilon_{\\varepsilon_0}", proof := "R5", hasO := true },
  { m := [[0,0],[1,1],[2,1]], t := phi (ofNat 2) zero, name := "\\zeta_0",
    proof := "R6", hasO := true },
  { m := [[0,0],[1,1],[2,1],[0,0]], t := add (phi (ofNat 2) zero) one,
    name := "\\zeta_0+1", proof := "«(0,0)(1,1)(2,1)(0,0)»", hasO := true },
  { m := [[0,0],[1,1],[2,1],[1,0]], t := phi zero (phi (ofNat 2) zero),
    name := "\\omega^{\\zeta_0+1}", proof := "«(0,0)(1,1)(2,1)(1,0)»", hasO := true },
  { m := [[0,0],[1,1],[2,1],[1,1]], t := phi one (phi (ofNat 2) zero),
    name := "\\varepsilon_{\\zeta_0+1}", proof := "«(0,0)(1,1)(2,1)(1,1)»", hasO := true },
  { m := [[0,0],[1,1],[2,1],[2,0]], t := phi one (phi zero (phi (ofNat 2) zero)),
    name := "\\varepsilon_{\\zeta_0\\cdot\\omega}", proof := "«(0,0)(1,1)(2,1)(2,0)»",
    hasO := true },
  { m := [[0,0],[1,1],[2,1],[2,1]], t := phi (ofNat 2) one, name := "\\zeta_1",
    proof := "R7", hasO := true },
  { m := [[0,0],[1,1],[2,1],[3,0]], t := phi (ofNat 2) omega, name := "\\zeta_\\omega",
    proof := "R8", hasO := true },
  { m := [[0,0],[1,1],[2,1],[3,1]], t := phi (ofNat 3) zero,
    name := "\\bar{\\varphi}(3,0)", proof := "R9", hasO := true },
  { m := [[0,0],[1,1],[2,1],[3,1],[0,0]], t := add (phi (ofNat 3) zero) one,
    name := "\\bar{\\varphi}(3,0)+1", proof := "«(0,0)(1,1)(2,1)(3,1)(0,0)»", hasO := true },
  { m := [[0,0],[1,1],[2,1],[3,1],[1,0]], t := phi zero (phi (ofNat 3) zero),
    name := "\\omega^{\\bar{\\varphi}(3,0)+1}", proof := "«(0,0)(1,1)(2,1)(3,1)(1,0)»",
    hasO := true },
  { m := [[0,0],[1,1],[2,2]], t := phi omega zero,
    name := "\\bar{\\varphi}(\\omega,0)", ev := "oStageC",
    note := "行 1 に 2 が現れる最初の行。この行より上の候補行は v0.1.22 の監査で撤回・再導出中" },
  { m := [[0,0],[1,1],[2,2],[1,1]], t := phi one (phi omega zero),
    name := "\\varepsilon_{\\bar{\\varphi}(\\omega,0)+1}", ev := "oStageC" }
  -- The former candidate rows above (2,2)(1,1) — (2,2)(2,1) .. phi-bar(omega^2,0) — were
  -- WITHDRAWN in v0.1.22: the psi-session audit machine-refuted (2,2)(2,1) = phi-bar(2,W)
  -- outright (E2 witnesses in Trans/StageC.lean) and left every value >= the
  -- (2,2)(2,0)-cascade shift-suspect (the committed diagonal rows carried the values of
  -- their first re-derivation members).  They return with re-derived values; the record
  -- of the refutation and the forced ladder is Trans/StageC.lean, header sections 1-5.
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
    note := "区間の全標準行列 (stdSeq) の E3 を一般定理で一括証明" },
  { bms := "(0,0)(1,1)…(a,1), a≥1",
    tm := "\\bar{\\varphi}(a,0)",
    nm := "\\varepsilon_0,\\ \\zeta_0,\\ \\bar{\\varphi}(3,0),\\ldots",
    boundT := phi omega zero,
    proof := "e3_F1family",
    proofFile := "Evidence/StageB.lean",
    note := "1 パラメータ族 (対角線) の一括証明。a=1,2,3 が表の ε₀, ζ₀, φ̄(3,0) 行、族の sup が φ̄(ω,0)" },
  { bms := "(0,0)(1,1)…(a,1)(0,0), a≥1",
    tm := "\\bar{\\varphi}(a,0)+1",
    nm := "\\varepsilon_0+1,\\ \\zeta_0+1,\\ldots",
    boundT := phi omega zero,
    proof := "esucc_M4z",
    proofFile := "Evidence/StageB.lean",
    note := "後続行の 1 パラメータ族 (E1 と後続則を全ての a で証明)" },
  { bms := "(0,0)(1,1)…(a,1)(1,0), a≥1",
    tm := "\\bar{\\varphi}(0,\\bar{\\varphi}(a,0))",
    nm := "\\omega^{\\varepsilon_0+1},\\ \\omega^{\\zeta_0+1},\\ldots",
    boundT := phi omega zero,
    proof := "e3_F4bfamily",
    proofFile := "Evidence/StageB.lean",
    note := "1 パラメータ族の一括証明。a=1 が表の ω^(ε₀+1) 行" },
  { bms := "(0,0)(1,1)…(a,1)(b,0), 2≤b≤a",
    tm := "\\bar{\\varphi}(b{-}1,\\bar{\\varphi}(0,\\bar{\\varphi}(a,0)))",
    nm := "\\varepsilon_{\\zeta_0\\cdot\\omega},\\ldots",
    boundT := phi omega zero,
    proof := "e3_F4cfamily",
    proofFile := "Evidence/StageB.lean",
    note := "2 パラメータ族の一括証明。これで梯子+1列 (r=0) の全ケースが証明済み" },
  { bms := "(0,0)(1,1)…(a,1)(b,1), 1≤b<a",
    tm := "\\bar{\\varphi}(b,\\bar{\\varphi}(a,0))",
    nm := "\\varepsilon_{\\zeta_0+1},\\ldots",
    boundT := phi omega zero,
    proof := "e3_F4afamily",
    proofFile := "Evidence/StageB.lean",
    note := "2 パラメータ族の一括証明。これで梯子+1列の全 7 ケース (F4) が完全証明" },
  { bms := "(0,0)(1,1)…(a,1)(a,1), a≥1",
    tm := "\\bar{\\varphi}(a,1)",
    nm := "\\varepsilon_1,\\ \\zeta_1,\\ \\bar{\\varphi}(3,1),\\ldots",
    boundT := phi omega zero,
    proof := "e3_F3family",
    proofFile := "Evidence/StageB.lean",
    note := "1 パラメータ族の一括証明。a=1,2 の ε₁, ζ₁ 行は定理としてインスタンス化" },
  { bms := "(0,0)(1,1)…(a,1)(a+1,0), a≥1",
    tm := "\\bar{\\varphi}(a,\\omega)",
    nm := "\\varepsilon_\\omega,\\ \\zeta_\\omega,\\ \\bar{\\varphi}(3,\\omega),\\ldots",
    boundT := phi omega zero,
    proof := "e3_family",
    proofFile := "Evidence/StageB.lean",
    note := "1 パラメータ族の一括証明。a=1,2 が表の ε_ω, ζ_ω 行、a≥3 は表の先へ無限に続く" }
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
  let proofCell :=
    if g.proof == "" then ""
    else match regionProofLine g.proofFile ("theorem " ++ g.proof) with
      | some n => "[✅](../lean/" ++ g.proofFile ++ "#L" ++ toString n ++ ")"
      | none => ""
  "| **" ++ g.bms ++ "** | $`" ++ g.tm ++ "`$ | $`" ++ g.nm ++ "`$ | " ++
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

順序数表記と見做した BMS (活性化関数を任意化し `[n]` なしで扱う) と、
Rathjen の表記系 $`T(M)`$ (Rathjen, *Proof-theoretic analysis of KPM*,
Arch. Math. Logic 30 (1991), §2) の対応表。
**機械検査を通った行のみ**を掲載する。検査の設計は
[plan/README.md](../plan/README.md) を参照。

エビデンス凡例:

- **証明列**: ✅ = その行の主張が **任意の $`n`$ について** Lean で証明済み
  (リンク先がその証明)。極限行は E3: 1 行領域では等式
  $`\\forall n.\\ o(M[n]) = t[n{+}1]`$、Stage B 以降では展開値の閉形式と
  相互共終 (両列が互いに追い越し合う witness 付き)。
  後続行は $`\\forall n.\\ o(M[n]) = t-1`$、零行は $`o(M) = t`$。
  表で唯一、検査ではなく証明である列。
- **太字の区間行**: 個別の行列ではなく**区間内の全標準行列**への主張。
  ✅ が付けば区間まるごと一般定理で証明済み (それまでは弱いエビデンスのみ)。
- **その他の弱いエビデンス** (いずれも有限個の $`n`$ の計算検査):
  - $`o`$ = 翻訳関数がこの行列で定義され $`o(M) = t`$ が成立 (E1)。
    $`o`$ の定義域全体では [コーパス検査](../lean/Evidence/Check.lean)
    (E2 順序埋め込み・E3 相互共終) 済み。
  - bisim6 = 深さ 6 の双模倣 (展開列と基本列が一致する領域で有効)。
  - oStageC = Stage C の候補翻訳 oStageC? の値の一致。コーパス検査済みだが、
    上位領域に未解決の設計問題が残るため $`o`$ への統合は保留中。

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
    -- the proof column links to the row's proof namespace (Proofs.lean or ProofsB.lean)
    let proofCell :=
      if r.proof == "" then ""
      else match proofLine ("namespace " ++ r.proof) with
        | some (path, n) => "[✅](../lean/" ++ path ++ "#L" ++ toString n ++ ")"
        | none => ""
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
