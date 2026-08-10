/-
Rows/TM.lean — the row database of the correspondence table (R1: BMS × T(M))

Policy (see plan/README.md):
  - This file is the single source of truth for the table; table/table-r1.md is
    generated from it by `gentable`.
  - Only rows that pass the machine checks are listed.  The per-row checks are the
    `#guard`s in the middle of this file, so a successful build means every listed
    row has been verified.

Meaning of the columns:
  proof : the namespace of Rows/Proofs.lean that proves E3 for this row, i.e.
          `∀ n, o (M[n]) = t[k(n)]` for that row's own index k.  This is the
          actual claim of the row, proved for every n — the only column that is
          a proof rather than a check.
          THE INDEX IS PER-ROW, NOT `n+1`.  This comment used to say `t[n+1]`;
          measured over the nine E3 proofs, four are `n+1`, one is `n+2` (R5),
          two are plain `n` (R4 = ε_ω, R8) and two use a bespoke `oval`.  Read
          the row's own `e3_val` before comparing anything against `fsN`;
          applying `+1` uniformly makes `fsN` look wrong above ε₀ when it is not.
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
import Evidence.Cert
import Trans.Recal

namespace Rows

open BMS (Matrix)
open TM (Term)
open TM.Term

/-- Version of the table (the repository version of the /commitbump workflow).
    Bump this together with every commit; gentable renders it into the header. -/
def version : String := "v0.2.3"

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
    name := "\\varepsilon_{\\zeta_0+1}", proof := "«(0,0)(1,1)(2,1)(1,1)»", hasO := true },
  -- The rows below were withdrawn in v0.1.42 (the o? calibration failure; see
  -- table/oracle-audit-2026-08-09.txt and plan/README.md) and RESTORED in v0.1.48
  -- with the oracle-calibrated values of oR = dict ∘ TransPort (Trans/Recal.lean,
  -- candidate tier, gated by the oR #guard below).  Terms were machine-extracted
  -- from oR, never hand-derived.
  { m := [[0,0],[1,1],[2,1],[2,0]],
    t := phi (add (phi zero zero) (phi zero zero)) (phi zero (phi zero zero)),
    name := "\\zeta_\\omega", ev := "oR", note := "旧値 ε_{ζ₀·ω} を訂正 (較正事故)" },
  { m := [[0,0],[1,1],[2,1],[2,1]],
    t := phi (add (phi zero zero) (add (phi zero zero) (phi zero zero))) zero,
    name := "\\bar{\\varphi}(3,0)", ev := "oR", note := "旧値 ζ₁ を訂正 (較正事故の初検出行)" },
  { m := [[0,0],[1,1],[2,1],[3,0]], t := phi (phi zero (phi zero zero)) zero,
    name := "\\bar{\\varphi}(\\omega,0)", ev := "oR", note := "旧値 ζ_ω を訂正" },
  { m := [[0,0],[1,1],[2,1],[3,0],[4,1]], t := phi (phi (phi zero zero) zero) zero,
    name := "\\bar{\\varphi}(\\varepsilon_0,0)", ev := "oR", note := "旧値 ζ_{ε₀} を訂正" },
  { m := [[0,0],[1,1],[2,1],[3,1]], t := psi (Z zero) zero,
    name := "\\Gamma_0", ev := "oR",
    note := "ψ 項の初登場。旧値 φ̄(3,0) を訂正" },
  { m := [[0,0],[1,1],[2,1],[3,1],[0,0]], t := add (psi (Z zero) zero) (phi zero zero),
    name := "\\Gamma_0+1", ev := "oR" },
  { m := [[0,0],[1,1],[2,1],[3,1],[1,0]], t := phi zero (psi (Z zero) zero),
    name := "\\omega^{\\Gamma_0+1}", ev := "oR" },
  -- WITHDRAWN v0.1.82: the Bachmann–Howard row was listed as
  --   (0,0)(1,1)(2,1)(3,2)  ↦  ψ_{Z0}(φ̄(1,Ω))
  -- but that MATRIX IS NOT STANDARD.  Two independent implementations agree:
  -- yaBMS `./bms -s` returns 0, and naruyoko's `isStandardPair` returns false.
  -- Its oracle image `D_0 D_1 D_1 D_2 0` is not a standard Buchholz term either,
  -- so the oR value carried no meaning for it.  It was the only non-standard
  -- matrix among the 51 rows (see scripts/standard-audit.sh, which now checks
  -- every row against the reference implementation).  Re-add the row when the
  -- STANDARD matrix for the Bachmann–Howard ordinal has been identified by the
  -- oracle rather than by hand.
  { m := [[0,0],[1,1],[2,2]], t := psi (Z zero) (Z (phi zero zero)),
    name := "\\psi_0(\\Omega_2)", ev := "oR",
    note := "行 1 に 2 が現れる最初の行。旧値 φ̄(ω,0) を訂正" },
  { m := [[0,0],[1,1],[2,2],[1,1]],
    t := phi (phi zero zero) (psi (Z zero) (Z (phi zero zero))),
    name := "\\varepsilon_{\\psi_0(\\Omega_2)+1}", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[1,1],[2,1]],
    t := phi (add (phi zero zero) (phi zero zero)) (psi (Z zero) (Z (phi zero zero))),
    name := "\\zeta_{\\psi_0(\\Omega_2)+1}", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[1,1],[2,1],[3,1]],
    t := psi (Z zero) (add (Z (phi zero zero)) (phi zero zero)),
    name := "\\Gamma_{\\psi_0(\\Omega_2)+1}", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[1,1],[2,2]],
    t := psi (Z zero) (add (Z (phi zero zero)) (phi (phi zero zero) (Z zero))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2))", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[1,1],[2,2],[1,1],[2,2]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (add (phi (phi zero zero) (Z zero)) (phi (phi zero zero) (Z zero)))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2)\\cdot 2)", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[2,0]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (phi zero (phi (phi zero zero) (Z zero)))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2+1))", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[2,0],[2,0]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (phi zero (add (phi (phi zero zero) (Z zero)) (phi zero zero)))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2+2))", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[2,0],[3,0]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (phi zero (add (phi (phi zero zero) (Z zero)) (phi zero (phi zero zero))))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2+\\omega))", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[2,0],[3,1]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (phi zero (add (phi (phi zero zero) (Z zero)) (phi (phi zero zero) zero)))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2+\\varepsilon_0))", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[2,0],[3,1],[4,2]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (phi zero (add (phi (phi zero zero) (Z zero))
        (psi (Z zero) (Z (phi zero zero)))))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2+\\psi_0(\\Omega_2)))", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[2,1]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (phi zero (add (phi (phi zero zero) (Z zero)) (Z zero)))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2+\\Omega_1))", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[2,1],[2,1]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (phi zero (add (phi (phi zero zero) (Z zero)) (add (Z zero) (Z zero))))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2+\\Omega_1\\cdot 2))", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[2,1],[3,1]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (phi zero (add (phi (phi zero zero) (Z zero))
        (phi zero (add (Z zero) (Z zero)))))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2+\\psi_1(\\Omega_1)))", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[2,1],[3,2]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (phi zero (add (phi (phi zero zero) (Z zero))
        (phi (phi zero zero) (Z zero))))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2+\\psi_1(\\Omega_2)))", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[2,2]],
    t := psi (Z zero) (add (Z (phi zero zero)) (Z (phi zero zero))),
    name := "\\psi_0(\\Omega_2\\cdot 2)", ev := "oR", note := "旧値 φ̄(ω²,0) を訂正" },
  { m := [[0,0],[1,1],[2,2],[2,2],[2,2]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (add (Z (phi zero zero)) (Z (phi zero zero)))),
    name := "\\psi_0(\\Omega_2\\cdot 3)", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[3,0]],
    t := psi (Z zero) (phi zero (Z (phi zero zero))),
    name := "\\psi_0(\\psi_2(1))", ev := "oR", note := "旧値 φ̄(ω^ω,0) を訂正" },
  { m := [[0,0],[1,1],[2,2],[3,0],[3,0]],
    t := psi (Z zero) (phi zero (add (Z (phi zero zero)) (phi zero zero))),
    name := "\\psi_0(\\psi_2(2))", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[3,0],[4,0]],
    t := psi (Z zero) (phi zero (add (Z (phi zero zero)) (phi zero (phi zero zero)))),
    name := "\\psi_0(\\psi_2(\\omega))", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[3,0],[4,1]],
    t := psi (Z zero) (phi zero (add (Z (phi zero zero)) (phi (phi zero zero) zero))),
    name := "\\psi_0(\\psi_2(\\varepsilon_0))", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[3,0],[4,1],[5,2]],
    t := psi (Z zero) (phi zero (add (Z (phi zero zero))
      (psi (Z zero) (Z (phi zero zero))))),
    name := "\\psi_0(\\psi_2(\\psi_0(\\Omega_2)))", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[3,1]],
    t := psi (Z zero) (phi zero (add (Z (phi zero zero)) (Z zero))),
    name := "\\psi_0(\\psi_2(\\Omega_1))", ev := "oR" }
]

/-! ## Per-row machine checks (a successful build means every row is verified) -/

-- E1: every row marked `hasO` really has the matching value of `o`
#guard rows.all fun r => !r.hasO || Trans.o? r.m == some r.t

-- G2 (v0.1.47): every row matches the oracle-calibrated reading oR = dict ∘ TransPort
-- (candidate-tier calibration, but a mandatory consistency gate: re-introducing a
--  miscalibrated value — e.g. the historical ζ₁ row — turns the build red here)
#guard rows.all fun r => Trans.oR r.m == some r.t

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
  | "oR" => "../lean/Trans/Recal.lean"
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

/-- The contents of table/table-r1.md.
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
Arch. Math. Logic 30 (1991), §2) の対応。

**証明列 ✅ の意味は下の [エビデンス](#エビデンス) を、設計の手順と失敗の記録は
[plan/](../plan/) を参照。**

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
    -- v0.1.43: the proof column is computed from the semantic-certificate
    -- registry (Evidence/Cert.lean) — a mark can no longer be declared by hand
    let proofCell :=
      if Evidence.Cert.certRows.any (fun p => p.1 == r.m && p.2 == r.t) then
        "[✅](../lean/Evidence/Cert.lean)"
      else ""
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
# エビデンス

対応表の 1 行 $`(M, t)`$ が主張していることを、**主張の強い順**に並べる。
`E.` は行についての命題、`P.` はその補助命題、`D.` は定義。
**証明済みかどうかは各節に明記する** — 表に載っていることと証明されていることは
別である。

- [E.otype — 行の主張そのもの](#eotype--行の主張そのもの)
- [E.certified — ✅ の実体](#ecertified--✅-の実体)
- [E.cofinal — 展開と基本列の相互共終](#ecofinal--展開と基本列の相互共終)
- [E.ground — 各表記系だけの構造](#eground--各表記系だけの構造)
- [E.embed — 順序埋め込み](#eembed--順序埋め込み)
- [E.trans — 単一アルゴリズムの出力であること](#etrans--単一アルゴリズムの出力であること)
- [証明書の強さと、その限界](#証明書の強さとその限界)
- [定義](#定義)

## E.otype — 行の主張そのもの

$`<_B`$ を BMS の順序、$`<_T`$ を $`\\mathfrak{T}(M)`$ の順序、$`\\mathrm{Std}`$ を
標準形、$`\\mathrm{NF}`$ を正規形とする。$`<_T`$ の $`\\mathrm{NF}`$ 上への制限が
整礎であるという仮定を $`\\mathrm{wf}`$ と書く。**行 $`(M,t)`$ の主張は**:

```math
\\mathrm{wf} \\;\\Longrightarrow\\;
\\mathrm{otype}\\bigl(\\{\\,N : \\mathrm{Std}(N),\\ N <_B M \\,\\},\\ <_B\\bigr)
\\;=\\;
\\mathrm{otype}\\bigl(\\{\\, s \\in \\mathrm{NF} : s <_T t \\,\\},\\ <_T\\bigr)
```

$`\\mathrm{otype}(X, <)`$ は**順序型** — 整列順序集合 $`(X, <)`$ と順序同型な
順序数のこと。$`\\mathrm{otype}`$ が定義できるのは $`<`$ が $`X`$ 上で整礎な
全順序のときだけで、$`\\mathrm{wf}`$ の仮定はそのためにある。例:

```math
\\mathrm{otype}(\\{0,1,2\\},\\ <) = 3,
\\qquad
\\mathrm{otype}(\\mathbb{N},\\ <) = \\omega,
\\qquad
\\mathrm{otype}(\\{\\,s : s <_T \\varepsilon_0\\,\\},\\ <_T) = \\varepsilon_0
```

つまり左辺は「$`M`$ より小さい標準形行列を全部集めたときの長さ」であり、
それが**行列 $`M`$ の表す順序数の定義**である。右辺は同じことを項の側でしたもの。
**この 2 つが等しいというのが「$`M`$ と $`t`$ が対応する」の意味である。**

外部の順序数論に「$`M`$ の値」を尋ねるのではなく、**両側の下方集合の長さが
一致する**と言うだけなので、$`o`$ のような翻訳写像に一切依存しない。

**状態: 未証明。** mathlib (順序型) が要り、$`\\mathrm{wf}`$ は仮定として切り出す
(紙の上では Rathjen 1994 の整列証明として既知)。以下の E は、これを支えるため、
あるいはこれを迂回して同じことを言うために立てられている。

## E.certified — ✅ の実体

$`\\mathrm{otype}`$ を直接扱う代わりに、**展開の再帰だけ**で同じことを述べたもの:

```math
\\mathrm{Certified}\\;M\\;t
```

$`o`$ にも順序型にも言及せず、$`M`$ の展開木を根から $`[\\,]`$ / $`0`$ まで降りる
導出の存在を要求する ([D.Certified](#dcertified))。**表の ✅ 列はこれが存在する行
にだけ機械的に付く。**

**状態: 11 行で証明済み。** 較正事故のあと、$`o`$ に言及しない形へ移した結果である
— $`o`$ を含む主張は $`o`$ が誤っていれば道連れになる。

## E.cofinal — 展開と基本列の相互共終

BMS の展開列と $`\\mathfrak{T}(M)`$ の基本列は、**同じ順序数への異なる共終列**に
なり得る (例: $`\\varepsilon_1`$ へ BMS は
$`\\varepsilon_0, \\varepsilon_0^2, \\varepsilon_0^{\\varepsilon_0},\\dots`$ で登り、
標準の基本列は $`\\varepsilon_0{+}1, \\omega^{\\varepsilon_0+1},\\dots`$ で登る)。
そこで等式ではなく相互共終で立てる。行 $`(M,t)`$ について:

```math
\\forall n.\\ o(M[n]) <_T t,
\\qquad
\\forall n\\,\\exists k.\\ o(M[n]) <_T t[k],
\\qquad
\\forall k\\,\\exists n.\\ t[k] <_T o(M[n])
```

両側が互いに追い越し合えば上限は一致するので、**$`M`$ と $`t`$ が同じ極限を指す**。
$`\\varepsilon_0`$ 以下では添字ずれを除いた等式 $`o(M[n]) = o(M)[n{+}1]`$ が
そのまま成り立つ。

**状態: 行ごとに証明済みのものがある。** ただし添字のずれは**行ごとに違う** —
測定では $`n{+}1`$ が 4 行、$`n{+}2`$ が 1 行、$`n`$ が 2 行、専用が 2 行。
一様な $`{+}1`$ は誤り。

## E.ground — 各表記系だけの構造

E 群が $`o`$ に言及するのに対し、これは**片側だけ**の性質で、対応表が正しいか
否かに依らず各表記系が持つべき土台である。

$`\\mathfrak{T}(M)`$ 側 — 極限の正規形 $`t`$ と任意の $`s \\in \\mathrm{NF}`$:

```math
t[n] <_T t,
\\qquad
s <_T t \\implies \\exists n.\\ s <_T t[n]
```

BMS 側 — 標準形の $`M, N`$:

```math
M[n] <_B M,
\\qquad
N <_B M \\implies \\exists n.\\ N <_B M[n]
```

**状態: 部分的。** $`\\mathfrak{T}(M)`$ 側の共終性は証明書の中で行ごとに使われている。

## E.embed — 順序埋め込み

標準形の $`M, N`$ について:

```math
o(M) \\in \\mathrm{NF},
\\qquad
M <_B N \\iff o(M) <_T o(N)
```

**状態: 一般形は未証明。** 順序は決定可能なので、個別のペアは計算で即検査できる。

## E.trans — 単一アルゴリズムの出力であること

```math
o(M) = t
```

**これ自体は $`o`$ の正しさを主張しない。**「全行が 1 つの $`o`$ から機械的に出た」
ことだけを言う。**較正事故はこの検査を全行で通ったまま起きた** — 両辺を同じ写像で
計算する検査は、写像の系統的な誤りを原理的に検出できない。

**状態: 全行で機械検査済み (弱いエビデンス)。**

## 証明書の強さと、その限界

E.certified がこの行について言えることの範囲を、定理として:

**一意性** — 導出に現れる値がすべて $`\\mathfrak{T}(M)`$ の項である証明書の範囲では、
この行は $`t`$ 以外の値を取り得ない。上下いずれの側も排除されている。

```math
\\forall u.\\;\\;\\mathrm{CertifiedIn}\\;\\mathrm{DomI}\\;M\\;u \\;\\Longrightarrow\\; u = t
```

**上限 (無条件)** — 値が $`\\mathfrak{T}(M)`$ の外に出るものも含め、いかなる証明書も
$`\\omega^{t+1}`$ 以上を与えない。$`\\mathrm{DomI}`$ の仮定が無いことに注意。

```math
\\forall u.\\;\\;\\mathrm{Certified}\\;M\\;u \\;\\Longrightarrow\\; \\bar\\varphi(0,\\,t+1) \\not\\le u
```

**ε₀ 行の鋭い上限** — この行では $`\\varepsilon_0`$ の直上から塞がれている。

```math
\\forall u.\\;\\; \\varepsilon_0 < u \\;\\Longrightarrow\\;
\\neg\\,\\mathrm{Certified}\\;[(0,0)(1,1)]\\;u
```

**まだ排除できていないこと** — $`t`$ より**下**の値が、$`\\mathfrak{T}(M)`$ の外へ出る
部分値を経由して認証される可能性:

```math
\\exists u.\\;\\; u < t \\;\\wedge\\; \\mathrm{Certified}\\;M\\;u
\\;\\wedge\\; \\neg\\,\\mathrm{CertifiedIn}\\;\\mathrm{DomI}\\;M\\;u \\;\\;?
```

上側は無条件に塞がっているので**残る穴は片側のみ**。P.undershoot_reduction により
葉 1 枚に還元済み:

> **P.T** $`a \\le b \\to b \\le c \\to a \\le c`$ — 中間項 $`b`$ が
> $`\\mathrm{Frag2}`$、**両端点は任意**

P.T は**真だが、このリポジトリの手法では証明できない**。真であること: 1010 項の
掃引で反例 0、結論を反転した陽性対照は 3628 万回発火。証明できないこと: 辞書式
帰納法が両端点の第 1 引数の比較可能性を消費するが、それは $`\\mathrm{Frag2}`$ の
外で偽 (P.frag2_stops_at_psi)。端点に $`\\mathrm{inT}`$ を課せば証明できるが、
**開いている場合は $`\\mathrm{inT}`$ でない場合**なので適用できない。

## その他の弱いエビデンス

有限個の $`n`$ の計算検査であり、**較正誤りを検出できない**ことが実証されている。

| 記号 | 意味 |
|---|---|
| `o` | E.trans がこの行で成立 |
| `oR` | オラクル較正済みの候補値 (P進大好きbot 氏の変換写像の Lean 移植)。全行一致をビルド時 `#guard` で強制 |
| `bisim6` | 深さ 6 の双模倣 |
| `oStageC` | Stage C の候補翻訳の値の一致 |

# 定義

## D.Certified

$`\\mathrm{Certified}\\;M\\;t`$ は帰納的述語で、導入規則は 3 つ:

```math
\\frac{}{\\mathrm{Certified}\\;[\\,]\\;0}
\\qquad
\\frac{\\mathrm{kind}\\,M = \\mathrm{succ}
\\qquad \\forall n.\\;\\mathrm{Certified}\\;(M[n])\\;t}
{\\mathrm{Certified}\\;M\\;(t+1)}
```

```math
\\frac{\\mathrm{kind}\\,M = \\mathrm{lim}
\\quad \\forall n.\\;\\mathrm{Certified}\\;(M[n])\\;(f_n)
\\quad \\forall n.\\;f_n < t
\\quad \\forall n.\\;f_n < f_{n+1}
\\quad \\forall s \\in \\mathfrak{T}(M).\\;s < t \\to \\exists n.\\;s \\le f_n}
{\\mathrm{Certified}\\;M\\;t}
```

極限規則の 5 前提のうち**同一性を述べるのは
$`\\forall n.\\;\\mathrm{Certified}\\;(M[n])\\;(f_n)`$ の 1 つだけ**で、残る 4 つは
列 $`f`$ の性質である。**性質をいくつ検査しても値は決まらない**
([plan/constitutions.md](../plan/constitutions.md) C2)。較正事故はここを取り違えた。
$`f`$ は**パラメータ**であって、特定の基本列に合わせる必要はない。

## D.CertifiedIn / D.DomI

```math
\\mathrm{DomI}(t) \\;:\\equiv\\; t \\in \\mathfrak{T}(M)
```

$`\\mathrm{Certified}`$ は認証される値に制約を課さないので、生の項の上では
$`\\mathfrak{T}(M)`$ の項でない値も認証されうる (P.cert_not_single_valued):

```math
\\mathrm{Certified}\\;[(0)(1)]\\;\\omega
\\qquad\\text{かつ}\\qquad
\\mathrm{Certified}\\;[(0)(1)]\\;(1+M)
```

$`\\mathrm{CertifiedIn}\\;\\mathrm{Dom}`$ は**導出に現れる値すべて**が
$`\\mathrm{Dom}`$ に属することを要求する版。E.certified の一意性が
$`\\mathrm{DomI}`$ を要求するのは、この一価性の破れを塞ぐためである。

# 実装

[行 DB と行ごとの検査](../lean/Rows/TM.lean) ·
[BMS の展開](../lean/BMS/Expand.lean) ·
[T(M) の項](../lean/TM/Terms.lean) ·
[T(M) の順序](../lean/TM/Order.lean) ·
[基本列](../lean/TM/FS.lean) ·
[証明書](../lean/Evidence/Cert.lean)
"
  header ++ body ++ footer

end Rows
