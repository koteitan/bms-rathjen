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
import Evidence.Cert
import Trans.Recal

namespace Rows

open BMS (Matrix)
open TM (Term)
open TM.Term

/-- Version of the table (the repository version of the /commitbump workflow).
    Bump this together with every commit; gentable renders it into the header. -/
def version : String := "v0.1.80"

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
  { m := [[0,0],[1,1],[2,1],[3,2]], t := psi (Z zero) (phi (phi zero zero) (Z zero)),
    name := "\\psi_0(\\varepsilon_{\\Omega+1})", ev := "oR",
    note := "Bachmann–Howard 順序数" },
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

> **⚠ 較正事故の記録 (v0.1.41–v0.1.48)**: 旧翻訳 $`o`$ は
> `(0,0)(1,1)(2,1)(2,0)` 以上で系統的に誤った値を与えていた
> (旧 ✅ 付き行を含む。経緯は [plan/README.md](../plan/README.md) の
> 「較正事故」節)。現在の表の全行は、P進大好きbot 氏のペア数列停止性証明の
> 変換写像 (の Lean 移植 oR) と一致することが**ビルド時 #guard で強制**されている。
> 証明列 (✅) は意味証明書 (SemanticCert) の存在する行のみに機械付与され、
> oR 由来の値は**予想ティア** (オラクル較正済み・意味論の証明は未了) である。

順序数表記と見做した BMS (活性化関数を任意化し `[n]` なしで扱う) と、
Rathjen の表記系 $`T(M)`$ (Rathjen, *Proof-theoretic analysis of KPM*,
Arch. Math. Logic 30 (1991), §2) の対応表。検査の設計は
[plan/README.md](../plan/README.md) を参照。

エビデンス凡例:

- **証明列**: ✅ = [意味証明書](../lean/Evidence/Cert.lean) `Certified M t`
  (行列の値が t であることの、展開閉包全体を含む閉じた帰納) が Lean に存在する行。
  ビルドが証明書レジストリから機械的に付与し、手で宣言することはできない。
  旧来の「o?-値についての定理」ベースの ✅ は較正事故により撤去した (警告参照)。

  ✅ が主張することとしないこと (v0.1.80 時点、すべて定理):

  1. **登録の条件**: この行は、内部に現れる値がすべて $`T(M)`$ の項である
     証明書 (`CertifiedIn DomI`) を持つ。これがレジストリのゲートであり、
     これを満たさない行は登録できない (`certIn_rows_inT`)。
  2. **一意性**: そのような証明書のうち、値が φ̄ 断片に留まるもの
     (ψ・Z を含まないもの) の範囲では、登録値以外の値は取り得ない
     (`certRows_unique_guarded`)。
  3. **上限**: 値が $`T(M)`$ の外に出るものも含め、**いかなる**証明書も、
     登録値より上の値 — 具体的には ω^(値+1) 以上 — を与えない
     (`certRows_no_overshoot`)。ε₀ の行はさらに鋭く、ε₀ より上の値は
     一切認証され得ない (`no_cert_above_eps0`)。

  **まだ排除できていないもの**: 登録値より**下**の値が、$`T(M)`$ の外の
  部分値を経由して認証される可能性。これは証明書の値を経由する推移律を
  要するため、ψ/Z 領域の順序理論 (Stage 3b) 待ちである。

  なお 1 の守りが必要なことは定理で示されている: `cert_not_single_valued`
  により `(0)(1)` は ω と 1+M の両方の証明書を持つ (1+M は $`T(M)`$ の項では
  ない)。守りなしの証明書は一価でなく、これは P進大好きbot 氏の命題10 の
  条件 (a) が (b)(c)(d) から従わないことの具体例でもある。
- **その他の弱いエビデンス** (いずれも有限個の $`n`$ の計算検査であり、
  **較正誤りを検出できない**ことが今回実証された):
  - $`o`$ = 翻訳関数がこの行列で定義され $`o(M) = t`$ が成立 (E1)。
  - oR = オラクル較正済み候補値: P進大好きbot 氏のペア数列停止性証明の
    変換写像の Lean 移植 (oR = dict∘TransPort) の値と一致 (予想ティア)。
    全行が oR と一致することはビルド時 #guard で強制される。
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
## 実装

[行 DB と行ごとの検査](../lean/Rows/TM.lean) ·
[BMS の展開](../lean/BMS/Expand.lean) ·
[T(M) の項](../lean/TM/Terms.lean) ·
[T(M) の順序](../lean/TM/Order.lean) ·
[基本列](../lean/TM/FS.lean)
"
  header ++ body ++ footer

end Rows
