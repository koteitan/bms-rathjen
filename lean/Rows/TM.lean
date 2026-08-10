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
def version : String := "v0.2.1"

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

対応表の各行 $`(M, t)`$ について、レジストリ
$`\\mathrm{certRows}`$ に登録された行が満たす命題。名前は Lean の識別子で、
`E.` は表の主張を支える定理、`P.` はその補助命題、`D.` は定義。実装は
[`lean/Evidence/Cert.lean`](../lean/Evidence/Cert.lean)。

- [E.certIn_rows_inT — 登録の条件 (ゲート)](#ecertin_rows_int--登録の条件-ゲート)
- [E.certRows_unique_gate — 一意性](#ecertrows_unique_gate--一意性)
- [E.certRows_no_overshoot — 上限 (無条件)](#ecertrows_no_overshoot--上限-無条件)
- [E.no_cert_above_eps0 — ε₀ 行の鋭い上限](#eno_cert_above_eps0--ε₀-行の鋭い上限)
- [まだ排除できていないこと](#まだ排除できていないこと)
- [その他の弱いエビデンス](#その他の弱いエビデンス)
- [定義](#定義): [D.Certified](#dcertified--行列が項を表すこと) ·
  [D.CertifiedIn / D.DomI](#dcertifiedin--ddomi--値の側を-tm-に閉じ込めたもの) ·
  [D.certRows](#dcertrows--レジストリ)

## E.certIn_rows_inT — 登録の条件 (ゲート)

```math
\\forall (M,t) \\in \\mathrm{certRows}.\\;\\; \\mathrm{CertifiedIn}\\;\\mathrm{DomI}\\;M\\;t
```

登録されたすべての行が、**導出に現れる値がすべて $`\\mathfrak{T}(M)`$ の項である**
証明書を持つ。これがレジストリのゲートであり、これを満たさない行は登録できない。
$`\\mathrm{certRows}`$ を拡張してこの証明を拡張しなければビルドが壊れる。

証明列 ✅ はこのゲートから機械的に付与されるもので、手で書くことはできない。

## E.certRows_unique_gate — 一意性

```math
\\forall (M,t) \\in \\mathrm{certRows}.\\;\\forall u.\\;\\;
\\mathrm{CertifiedIn}\\;\\mathrm{DomI}\\;M\\;u \\;\\Longrightarrow\\; u = t
```

ゲートが要求する範囲の証明書 — 値が遺伝的に $`\\mathfrak{T}(M)`$ の項であるもの —
では、**登録値以外の値は取り得ない**。上下いずれの側も排除されている。
登録の条件 (E.certIn_rows_inT) と一意性の条件が**同じ $`\\mathrm{DomI}`$**
であることに注意。

## E.certRows_no_overshoot — 上限 (無条件)

```math
\\forall (M,t) \\in \\mathrm{certRows}.\\;\\forall u.\\;\\;
\\mathrm{Certified}\\;M\\;u \\;\\Longrightarrow\\; \\bar\\varphi(0,\\,t+1) \\not\\le u
```

値が $`\\mathfrak{T}(M)`$ の外に出るものも含め、**いかなる**証明書も
$`\\bar\\varphi(0, t+1) = \\omega^{t+1}`$ 以上の値を与えない。
$`\\mathrm{DomI}`$ の仮定が無いことに注意 — これは無条件である。

## E.no_cert_above_eps0 — ε₀ 行の鋭い上限

```math
\\forall u.\\;\\; \\varepsilon_0 < u \\;\\Longrightarrow\\;
\\neg\\,\\mathrm{Certified}\\;[(0,0)(1,1)]\\;u
```

ε₀ の行では、**ε₀ より上の値は一切認証され得ない**。E.certRows_no_overshoot が
$`\\omega^{t+1}`$ 以上を塞ぐのに対し、この行では $`t`$ の直上から塞がれている。

## まだ排除できていないこと

登録値より**下**の値が、$`\\mathfrak{T}(M)`$ の外へ出る部分値を経由して
認証される可能性 (ゲートを通らない証明書):

```math
\\exists u.\\;\\; u < t \\;\\wedge\\; \\mathrm{Certified}\\;M\\;u
\\;\\wedge\\; \\neg\\,\\mathrm{CertifiedIn}\\;\\mathrm{DomI}\\;M\\;u \\;\\;?
```

上側は E.certRows_no_overshoot により無条件に塞がっているので、**残る穴は片側のみ**。

P.undershoot_reduction により、この穴は葉 1 枚に還元済み:

> **P.T** $`a \\le b \\;\\to\\; b \\le c \\;\\to\\; a \\le c`$ — 中間項 $`b`$ が
> $`\\mathrm{Frag2}`$、**両端点は任意**

P.T は**真だが、このリポジトリの手法では証明できない**。真であること: 7 構成子に
わたる 1010 項の掃引で反例 0、結論を反転した陽性対照は 3628 万回発火する。
証明できないこと: 辞書式帰納法が両端点の第 1 引数の比較可能性を消費するが、それは
$`\\mathrm{Frag2}`$ の外で偽である (P.frag2_stops_at_psi)。端点に $`\\mathrm{inT}`$
を課せば証明できるが、**開いている場合は $`\\mathrm{inT}`$ でない場合**なので
適用できない。

## その他の弱いエビデンス

いずれも有限個の $`n`$ の計算検査であり、**較正誤りを検出できない**ことが
実証されている。表の主張ではなく候補ティアである。

| 記号 | 意味 |
|---|---|
| `o` | 翻訳関数がこの行列で定義され $`o(M) = t`$ |
| `oR` | オラクル較正済みの候補値 (P進大好きbot 氏の変換写像の Lean 移植)。全行一致をビルド時 `#guard` で強制 |
| `bisim6` | 深さ 6 の双模倣 |
| `oStageC` | Stage C の候補翻訳の値の一致 |

# 定義

## D.Certified — 行列が項を表すこと

$`\\mathrm{Certified}\\;M\\;t`$ は「行列 $`M`$ が項 $`t`$ を表す」ことを、
外部の意味論を使わず**展開の再帰だけ**で述べた帰納的述語。導入規則は 3 つ:

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

帰納型なので、$`\\mathrm{Certified}\\;M\\;t`$ を持つとは
**$`M`$ の展開木を根から降りて $`[\\,]`$ / $`0`$ に至る導出が実在する**ということ。
整礎性は前提していない。

極限規則の 5 前提のうち**同一性を述べるのは
$`\\forall n.\\;\\mathrm{Certified}\\;(M[n])\\;(f_n)`$ の 1 つだけ**で、
残る 4 つは列 $`f`$ の性質である。**性質をいくつ検査しても値は決まらない**
([plan/constitutions.md](../plan/constitutions.md) C2)。較正事故はここを
取り違えて起きた。$`f`$ は**パラメータ**であって、特定の基本列に合わせる必要はない。

## D.CertifiedIn / D.DomI — 値の側を $`\\mathfrak{T}(M)`$ に閉じ込めたもの

```math
\\mathrm{DomI}(t) \\;:\\equiv\\; t \\in \\mathfrak{T}(M)
```

$`\\mathrm{Certified}`$ は認証される値に制約を課さないので、生の項の上では
$`\\mathfrak{T}(M)`$ の項でない値も認証されうる。実例 (P.cert_not_single_valued):

```math
\\mathrm{Certified}\\;[(0)(1)]\\;\\omega
\\qquad\\text{かつ}\\qquad
\\mathrm{Certified}\\;[(0)(1)]\\;(1+M)
```

$`\\mathrm{CertifiedIn}\\;\\mathrm{Dom}`$ は**導出に現れる値すべて**が
$`\\mathrm{Dom}`$ に属することを要求する版。ゲート (E.certIn_rows_inT) が
$`\\mathrm{DomI}`$ を要求するのは、この一価性の破れを塞ぐためである。

## D.certRows — レジストリ

登録された $`(M, t)`$ の対のリスト。**✅ はこのリストへの登録から機械的に付与される**。
E.certIn_rows_inT がその登録条件であり、リストを伸ばすには証明を伸ばすしかない。

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
