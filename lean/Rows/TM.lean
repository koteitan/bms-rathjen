/-
Rows/TM.lean — the row database of the correspondence table (R1: BMS × T(M))

Policy (see plan/README.md):
  - This file is the single source of truth for the table; table/table-r1.md is
    generated from it by `gentable`.
  - Only rows that pass the machine checks are listed.  The per-row checks are the
    `#guard`s in the middle of this file, so a successful build means every listed
    row has been verified.

THE RENDERED TABLE HAS SIX COLUMNS AND NO MORE — see plan/spec.md, which is the
spec this generator answers to.  The proof column is ✅ or empty; everything that is
a PREMISE of ✅ rather than ✅ itself goes to the weak-evidence column.

Fields, and where each one surfaces:
  m, t  : the two sides of the row.  `t` also decides the Buchholz cell — at and above
          `buchCut` it is recomputed from `m` by `oRB` (the pss2bp port), below it the
          row's own `name` is used.  See `buchOf` for why the cut is there.
  name  : the common name (ε₀, ζ₀, Γ₀, ω^ω).  Rendered only below `buchCut`.
  proof : the namespace that proves E.fs for this row, i.e.
          `∀ n, oR (M[n]) = fsN t (k n)` for that row's own index k.  Rendered as the
          fₙ mark IN THE WEAK-EVIDENCE COLUMN — it is a premise of ✅, not ✅.
          THE INDEX IS PER-ROW, NOT `n+1`.  This comment used to say `t[n+1]`;
          measured over the nine E3 proofs, four are `n+1`, one is `n+2` (R5),
          two are plain `n` (R4 = ε_ω, R8) and two use a bespoke `oval`.  Read
          the row's own `e3_val` before comparing anything against `fsN`;
          applying `+1` uniformly makes `fsN` look wrong above ε₀ when it is not.
  hasO  : the translation `o` is defined on this matrix and o(M) = t holds.
          The whole domain of `o` is additionally checked over a corpus by
          `checkAll`, see Test/TransTest.lean.
  ev    : the remaining, weaker evidence.  "bisim6" = strict bisimulation to depth 6
          (valid in the region where the expansions and the fundamental sequences
          agree up to the index shift of one).  `oR` was removed from this field on
          2026-08-14: the 𝔗(M) column IS `oR`'s output, so listing it as evidence for
          itself adds nothing (plan/constitutions.md C1).
`hasO` and `ev` are finite computations; only `proof` covers all n.
The ✅ column is not a field at all — it is looked up in `Evidence.Cert.certRows`, so
it cannot be written by hand.

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
def version : String := "v0.7.27"

/-- One row of the correspondence table. -/
structure Row where
  m : Matrix           -- the BMS matrix
  t : Term             -- the T(M) term
  name : String        -- common name (MathJax)
  proof : String := "" -- key of the E3 proof; resolved to a file+line by gentable and
                       -- rendered as the E3 mark.  Searched in Rows/Proofs.lean,
                       -- Rows/ProofsB.lean, Rows/Selected.lean, Rows/G3.lean, Rows/G4.lean,
                       -- Rows/G5.lean, Rows/G6.lean, Rows/G7.lean, Rows/G8.lean, Rows/G9.lean,
                       -- in that order.
                       -- ("" = no all-n proof yet.)  A key that resolves to nothing
                       -- prints no mark, so a renamed namespace loses the mark
                       -- instead of lying about it.
  hasO : Bool := false -- o(M) = t holds (E1)
  ev : String := ""    -- the remaining, weaker evidence
  note : String := ""
  /-- Why this row is on the E-proof shortlist ("" = not on it).  Starts with the side
      the phase change belongs to: **M** BMS, **T** 𝔗(M), **B** Buchholz, **D** disputed
      against an external table.  Chosen by hand, not exhaustively.
      NOT RENDERED (plan/spec.md fixes the table at six columns).  It is the selector of
      `Rows.Selected.selected`, and the reason for each choice is kept here rather than
      in prose so that the shortlist and its justification cannot drift apart. -/
  sel : String := ""

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
    ev := "bisim6",
    sel := "**M** 1 行行列で成分が増える最初。**T** φ̄ の第 2 引数が 0 でなくなる最初" },
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
    hasO := true, ev := "bisim6", note := "2 行の最初の極限",
    sel := "**M** 2 行の最初。**T** φ̄ の第 1 引数が 0 でなくなる最初。**B** Ω₁ の最初" },
  { m := [[0,0],[1,1],[0,0]], t := add e0 one, name := "\\varepsilon_0+1",
    proof := "«(0,0)(1,1)(0,0)»", hasO := true },
  { m := [[0,0],[1,1],[1,0]], t := phi zero e0,
    name := "\\omega^{\\varepsilon_0+1}", proof := "R2", hasO := true, ev := "bisim6",
    sel := "**T** φ̄ が不動点を飛ばす最初 (φ̄(0,ε₀) は ε₀ ではない)" },
  { m := [[0,0],[1,1],[1,1]], t := phi one one, name := "\\varepsilon_1", proof := "R3",
    hasO := true },
  { m := [[0,0],[1,1],[2,0]], t := phi one omega, name := "\\varepsilon_\\omega",
    proof := "R4", hasO := true,
    sel := "**M** 0 行目が 2 になる最初" },
  { m := [[0,0],[1,1],[2,0],[0,0]], t := add (phi one omega) one,
    name := "\\varepsilon_\\omega+1", proof := "«(0,0)(1,1)(2,0)(0,0)»", hasO := true },
  -- 食い違い行 (diff.md 族 1)。値は oR から機械抽出。
  { m := [[0,0],[1,1],[2,0],[1,1],[1,0],[2,1],[3,0],[1,0],[2,1]],
    t := phi zero (add (phi (phi zero zero) (add (phi zero (phi zero zero)) (phi zero zero)))
      (add (phi (phi zero zero) (phi zero (phi zero zero))) (phi (phi zero zero) zero))),
    name := "\\bar{\\varphi}(0,\\bar{\\varphi}(1,\\omega+1)+\\bar{\\varphi}(1,\\omega)+\\bar{\\varphi}(1,0))",
    proof := "namespace F1", note := "外部の表と食い違うが決着済み。当方が正しい ([diff.md](diff.md) 族 1)",
    sel := "**D** 外部の表と食い違う 9 行の 1 つ" },
  { m := [[0,0],[1,1],[2,0],[2,0]], t := phi one (phi zero (ofNat 2)),
    name := "\\varepsilon_{\\omega^2}", proof := "«(0,0)(1,1)(2,0)(2,0)»", hasO := true },
  { m := [[0,0],[1,1],[2,0],[3,0]], t := phi one (phi zero omega),
    name := "\\varepsilon_{\\omega^\\omega}", proof := "«(0,0)(1,1)(2,0)(3,0)»",
    hasO := true },
  { m := [[0,0],[1,1],[2,0],[3,1]], t := phi one e0,
    name := "\\varepsilon_{\\varepsilon_0}", proof := "R5", hasO := true },
  { m := [[0,0],[1,1],[2,1]], t := phi (ofNat 2) zero, name := "\\zeta_0",
    proof := "R6", hasO := true,
    sel := "**M** (2,1) の最初。**B** ψ₁ が入れ子になる最初" },
  { m := [[0,0],[1,1],[2,1],[0,0]], t := add (phi (ofNat 2) zero) one,
    name := "\\zeta_0+1", proof := "«(0,0)(1,1)(2,1)(0,0)»", hasO := true },
  { m := [[0,0],[1,1],[2,1],[1,0]], t := phi zero (phi (ofNat 2) zero),
    name := "\\omega^{\\zeta_0+1}", proof := "«(0,0)(1,1)(2,1)(1,0)»", hasO := true },
  { m := [[0,0],[1,1],[2,1],[1,1]], t := phi one (phi (ofNat 2) zero),
    name := "\\varepsilon_{\\zeta_0+1}", proof := "«(0,0)(1,1)(2,1)(1,1)»", hasO := true },
  -- 食い違い行 (diff.md 族 2、2 行)。族 2 は 1 段ずれで、先方の 1 行目の値が oR の
  -- 2 行目の値に一致する。値は oR から機械抽出。
  { m := [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[1,1],[2,0]],
    t := phi (phi zero zero) (add (phi (phi zero zero)
      (phi (add (phi zero zero) (phi zero zero)) zero)) (phi zero (phi zero zero))),
    name := "\\bar{\\varphi}(1,\\bar{\\varphi}(1,\\bar{\\varphi}(2,0))+\\omega)",
    proof := "namespace F2a", note := "外部の表と食い違うが決着済み。当方が正しい ([diff.md](diff.md) 族 2)",
    sel := "**D** 外部の表と食い違う 9 行の 1 つ" },
  { m := [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[1,1],[2,0],[3,1]],
    t := phi (phi zero zero) (add (phi (phi zero zero)
      (phi (add (phi zero zero) (phi zero zero)) zero)) (phi (phi zero zero) zero)),
    name := "\\bar{\\varphi}(1,\\bar{\\varphi}(1,\\bar{\\varphi}(2,0))+\\bar{\\varphi}(1,0))",
    proof := "namespace F2b", note := "外部の表と食い違うが決着済み。当方が正しい ([diff.md](diff.md) 族 2)",
    sel := "**D** 外部の表と食い違う 9 行の 1 つ" },
  -- 食い違い行 (diff.md 族 3、3 行)。ここだけ当方の値が先方より大きい。3 行とも決着済み。
  { m := [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[4,0],[5,1],[6,1],[5,0]],
    t := phi (phi zero zero) (phi (phi zero zero) (phi zero (phi zero
      (phi (add (phi zero zero) (phi zero zero)) zero)))),
    name := "\\bar{\\varphi}(1,\\bar{\\varphi}(1,\\bar{\\varphi}(0,\\bar{\\varphi}(0,\\bar{\\varphi}(2,0)))))",
    proof := "namespace F3a", note := "外部の表と食い違うが決着済み。当方が正しい ([diff.md](diff.md) 族 3)",
    sel := "**D** 外部の表と食い違う 9 行の 1 つ。当方が大きい側" },
  { m := [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[4,0],[5,1],[6,1],[5,0],[6,1]],
    t := phi (phi zero zero) (phi (phi zero zero) (phi zero (phi zero
      (add (phi (add (phi zero zero) (phi zero zero)) zero) (phi (phi zero zero) zero))))),
    name := "\\bar{\\varphi}(1,\\bar{\\varphi}(1,\\bar{\\varphi}(0,\\bar{\\varphi}(0,\\bar{\\varphi}(2,0)+\\bar{\\varphi}(1,0)))))",
    proof := "namespace F3b", note := "外部の表と食い違うが決着済み。当方が正しい ([diff.md](diff.md) 族 3)",
    sel := "**D** 外部の表と食い違う 9 行の 1 つ。当方が大きい側" },
  { m := [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[4,0],[5,1],[6,1],[5,0],[6,1],[7,1]],
    t := phi (phi zero zero) (phi (phi zero zero) (phi zero (phi zero
      (add (phi (add (phi zero zero) (phi zero zero)) zero)
        (phi (add (phi zero zero) (phi zero zero)) zero))))),
    name := "\\bar{\\varphi}(1,\\bar{\\varphi}(1,\\bar{\\varphi}(0,\\bar{\\varphi}(0,\\bar{\\varphi}(2,0)+\\bar{\\varphi}(2,0)))))",
    proof := "namespace F3c", note := "外部の表と食い違うが決着済み。当方が正しい ([diff.md](diff.md) 族 3)",
    sel := "**D** 外部の表と食い違う 9 行の 1 つ。当方が大きい側" },
  -- The rows below were withdrawn in v0.1.42 (the o? calibration failure; see
  -- table/refimpl-audit-2026-08-09.txt and plan/README.md) and RESTORED in v0.1.48
  -- with the reference-calibrated values of oR = dict ∘ TransPort (Trans/Recal.lean,
  -- candidate tier, gated by the oR #guard below).  Terms were machine-extracted
  -- from oR, never hand-derived.
  { m := [[0,0],[1,1],[2,1],[2,0]],
    t := phi (add (phi zero zero) (phi zero zero)) (phi zero (phi zero zero)),
    name := "\\zeta_\\omega", note := "旧値 ε_{ζ₀·ω} を訂正 (較正事故)" },
  { m := [[0,0],[1,1],[2,1],[2,1]],
    t := phi (add (phi zero zero) (add (phi zero zero) (phi zero zero))) zero,
    name := "\\bar{\\varphi}(3,0)", note := "旧値 ζ₁ を訂正 (較正事故の初検出行)" },
  -- 食い違い行 (diff.md 族 4、3 行)。φ̄(3,ω) の直上をどう数えるかで割れている。
  { m := [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1]],
    t := phi (phi zero zero) (phi (add (phi zero zero) (add (phi zero zero) (phi zero zero)))
      (phi zero (phi zero zero))),
    name := "\\bar{\\varphi}(1,\\bar{\\varphi}(3,\\omega))",
    proof := "namespace G9", note := "外部の表と食い違う ([diff.md](diff.md) 族 4)",
    sel := "**D** 外部の表と食い違う 9 行の 1 つ" },
  { m := [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1],[2,1]],
    t := phi (add (phi zero zero) (phi zero zero))
      (phi (add (phi zero zero) (add (phi zero zero) (phi zero zero)))
        (phi zero (phi zero zero))),
    name := "\\bar{\\varphi}(2,\\bar{\\varphi}(3,\\omega))",
    proof := "namespace G10", note := "外部の表と食い違う ([diff.md](diff.md) 族 4)",
    sel := "**D** 外部の表と食い違う 9 行の 1 つ" },
  { m := [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1],[2,1],[2,1]],
    t := phi (add (phi zero zero) (add (phi zero zero) (phi zero zero)))
      (add (phi zero (phi zero zero)) (phi zero zero)),
    name := "\\bar{\\varphi}(3,\\omega+1)",
    note := "外部の表と食い違う ([diff.md](diff.md) 族 4)",
    sel := "**D** 外部の表と食い違う 9 行の 1 つ" },
  { m := [[0,0],[1,1],[2,1],[3,0]], t := phi (phi zero (phi zero zero)) zero,
    name := "\\bar{\\varphi}(\\omega,0)", proof := "namespace G1",
    note := "旧値 ζ_ω を訂正",
    sel := "**T** φ̄ の第 1 引数が数字でなくなる最初" },
  { m := [[0,0],[1,1],[2,1],[3,0],[4,1]], t := phi (phi (phi zero zero) zero) zero,
    name := "\\bar{\\varphi}(\\varepsilon_0,0)", proof := "namespace G3",
    note := "旧値 ζ_{ε₀} を訂正",
    sel := "**T** φ̄ の第 1 引数が ε 数になる最初" },
  { m := [[0,0],[1,1],[2,1],[3,1]], t := psi (Z zero) zero,
    name := "\\Gamma_0", proof := "namespace G7",
    note := "ψ 項の初登場。旧値 φ̄(3,0) を訂正",
    sel := "**M** (3,1) の最初。**T** ψ の最初。**B** ψ₁ の 3 重入れ子の最初" },
  { m := [[0,0],[1,1],[2,1],[3,1],[0,0]], t := add (psi (Z zero) zero) (phi zero zero),
    name := "\\Gamma_0+1" },
  { m := [[0,0],[1,1],[2,1],[3,1],[1,0]], t := phi zero (psi (Z zero) zero),
    name := "\\omega^{\\Gamma_0+1}" },
  -- WITHDRAWN v0.1.82: the Bachmann–Howard row was listed as
  --   (0,0)(1,1)(2,1)(3,2)  ↦  ψ_{Z0}(φ̄(1,Ω))
  -- but that MATRIX IS NOT STANDARD.  Two independent implementations agree:
  -- yaBMS `./bms -s` returns 0, and naruyoko's `isStandardPair` returns false.
  -- Its reference implementation image `D_0 D_1 D_1 D_2 0` is not a standard Buchholz term either,
  -- so the oR value carried no meaning for it.  It was the only non-standard
  -- matrix among the 51 rows (see scripts/standard-audit.sh, which now checks
  -- every row against the reference implementation).  Re-add the row when the
  -- STANDARD matrix for the Bachmann–Howard ordinal has been identified by the
  -- reference implementation rather than by hand.
  { m := [[0,0],[1,1],[2,2]], t := psi (Z zero) (Z (phi zero zero)),
    name := "\\psi_0(\\Omega_2)", proof := "namespace G4",
    note := "行 1 に 2 が現れる最初の行。旧値 φ̄(ω,0) を訂正",
    sel := "**M** 1 行目に 2 が現れる最初。**T** Z の最初。**B** Ω₂ の最初" },
  { m := [[0,0],[1,1],[2,2],[1,1]],
    t := phi (phi zero zero) (psi (Z zero) (Z (phi zero zero))),
    name := "\\varepsilon_{\\psi_0(\\Omega_2)+1}" },
  { m := [[0,0],[1,1],[2,2],[1,1],[2,1]],
    t := phi (add (phi zero zero) (phi zero zero)) (psi (Z zero) (Z (phi zero zero))),
    name := "\\zeta_{\\psi_0(\\Omega_2)+1}" },
  { m := [[0,0],[1,1],[2,2],[1,1],[2,1],[3,1]],
    t := psi (Z zero) (add (Z (phi zero zero)) (phi zero zero)),
    name := "\\Gamma_{\\psi_0(\\Omega_2)+1}",
    sel := "**T** ψ の引数に Z と和が同居する最初" },
  { m := [[0,0],[1,1],[2,2],[1,1],[2,2]],
    t := psi (Z zero) (add (Z (phi zero zero)) (phi (phi zero zero) (Z zero))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2))", proof := "namespace G5",
    sel := "**T** Ω が φ̄ の引数に現れる最初。**B** ψ₁ の引数に Ω₂ が入る最初" },
  { m := [[0,0],[1,1],[2,2],[1,1],[2,2],[1,1],[2,2]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (add (phi (phi zero zero) (Z zero)) (phi (phi zero zero) (Z zero)))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2)\\cdot 2)" },
  { m := [[0,0],[1,1],[2,2],[2,0]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (phi zero (phi (phi zero zero) (Z zero)))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2+1))" },
  { m := [[0,0],[1,1],[2,2],[2,0],[2,0]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (phi zero (add (phi (phi zero zero) (Z zero)) (phi zero zero)))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2+2))" },
  { m := [[0,0],[1,1],[2,2],[2,0],[3,0]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (phi zero (add (phi (phi zero zero) (Z zero)) (phi zero (phi zero zero))))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2+\\omega))" },
  { m := [[0,0],[1,1],[2,2],[2,0],[3,1]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (phi zero (add (phi (phi zero zero) (Z zero)) (phi (phi zero zero) zero)))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2+\\varepsilon_0))" },
  { m := [[0,0],[1,1],[2,2],[2,0],[3,1],[4,2]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (phi zero (add (phi (phi zero zero) (Z zero))
        (psi (Z zero) (Z (phi zero zero)))))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2+\\psi_0(\\Omega_2)))" },
  { m := [[0,0],[1,1],[2,2],[2,1]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (phi zero (add (phi (phi zero zero) (Z zero)) (Z zero)))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2+\\Omega_1))" },
  { m := [[0,0],[1,1],[2,2],[2,1],[2,1]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (phi zero (add (phi (phi zero zero) (Z zero)) (add (Z zero) (Z zero))))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2+\\Omega_1\\cdot 2))" },
  { m := [[0,0],[1,1],[2,2],[2,1],[3,1]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (phi zero (add (phi (phi zero zero) (Z zero))
        (phi zero (add (Z zero) (Z zero)))))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2+\\psi_1(\\Omega_1)))" },
  { m := [[0,0],[1,1],[2,2],[2,1],[3,2]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (phi zero (add (phi (phi zero zero) (Z zero))
        (phi (phi zero zero) (Z zero))))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2+\\psi_1(\\Omega_2)))" },
  { m := [[0,0],[1,1],[2,2],[2,2]],
    t := psi (Z zero) (add (Z (phi zero zero)) (Z (phi zero zero))),
    name := "\\psi_0(\\Omega_2\\cdot 2)", proof := "namespace G6",
    note := "旧値 φ̄(ω²,0) を訂正",
    sel := "**B** ψ₀ の引数が和になる最初" },
  { m := [[0,0],[1,1],[2,2],[2,2],[2,2]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (add (Z (phi zero zero)) (Z (phi zero zero)))),
    name := "\\psi_0(\\Omega_2\\cdot 3)" },
  { m := [[0,0],[1,1],[2,2],[3,0]],
    t := psi (Z zero) (phi zero (Z (phi zero zero))),
    name := "\\psi_0(\\psi_2(1))", proof := "namespace G2",
    note := "旧値 φ̄(ω^ω,0) を訂正",
    sel := "**M** (2,2) の後に (3,0) が来る最初。**T** Z が ω 冪の中に入る最初" },
  { m := [[0,0],[1,1],[2,2],[3,0],[3,0]],
    t := psi (Z zero) (phi zero (add (Z (phi zero zero)) (phi zero zero))),
    name := "\\psi_0(\\psi_2(2))" },
  { m := [[0,0],[1,1],[2,2],[3,0],[4,0]],
    t := psi (Z zero) (phi zero (add (Z (phi zero zero)) (phi zero (phi zero zero)))),
    name := "\\psi_0(\\psi_2(\\omega))" },
  { m := [[0,0],[1,1],[2,2],[3,0],[4,1]],
    t := psi (Z zero) (phi zero (add (Z (phi zero zero)) (phi (phi zero zero) zero))),
    name := "\\psi_0(\\psi_2(\\varepsilon_0))" },
  { m := [[0,0],[1,1],[2,2],[3,0],[4,1],[5,2]],
    t := psi (Z zero) (phi zero (add (Z (phi zero zero))
      (psi (Z zero) (Z (phi zero zero))))),
    name := "\\psi_0(\\psi_2(\\psi_0(\\Omega_2)))" },
  { m := [[0,0],[1,1],[2,2],[3,1]],
    t := psi (Z zero) (phi zero (add (Z (phi zero zero)) (Z zero))),
    name := "\\psi_0(\\psi_2(\\Omega_1))", proof := "namespace G8",
    sel := "**B** ψ₂ の引数に Ω₁ が入る最初。表の最上行" }
]

/-! ## Per-row machine checks (a successful build means every row is verified) -/

-- E1: every row marked `hasO` really has the matching value of `o`
#guard rows.all fun r => !r.hasO || Trans.o? r.m == some r.t

-- G2 (v0.1.47): every row matches the reference-calibrated reading oR = dict ∘ TransPort
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
    note := "区間の全標準行列 (stdSeq) について、展開の値を一般定理で一括証明" }
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

/-! ### The Buchholz column

`Trans.Recal.oRB` is the Buchholz side of the reader — the port of p-adic-lover-bot's
translation, whose output is verbatim `pss2bp --raw` (checked wholesale in
`Trans/Recal.lean` §5B).  So the Buchholz column is not a second hand-written column: it
is computed from the matrix, by the same route the audit checks.

TWO THINGS THE PRINTER MUST NOT DO.  `oRB` is the term BEFORE `oR`'s `1 + ·`
adjustment, so on the finite rows it is off by one (the row worth `2` reads
`ψ_0(0) = 1`); and below `ψ_0(Ω_2)` the familiar names (ε₀, ζ₀, Γ₀, ω^ω) say more to a
reader than a five-deep ψ nest does.  Both are handled by the same cut: the computed
form is used at and above `ψ_0(Ω_2)`, the row's own `name` below it. -/

/-- A Buchholz term as MathJax, in the ψ form: `D u a` is `ψ_u(a)`. -/
def bhTex : Trans.Dict.BT → String
  | .zero => "0"
  | .D u a => "\\psi_{" ++ toString u ++ "}(" ++ bhTex a ++ ")"
  | .sum a b => bhTex a ++ "+" ++ bhTex b

/-- The first row at which the Buchholz column switches to the computed ψ form:
    `ψ_Ω(Z 1)`, the 𝔗(M) side of Buchholz's `ψ_0(Ω_2)`. -/
def buchCut : Term := psi (Z zero) (Z one)

/-- The Buchholz cell of a row: computed from the matrix at and above `buchCut`,
    the row's own common name below it, empty when the reader does not apply. -/
def buchOf (r : Row) : String :=
  if le buchCut r.t then
    match Trans.Recal.oRB r.m with
    | some b => bhTex b
    | none => ""
  else r.name

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
Rathjen の表記系 $`\\mathfrak{T}(M)`$ (Rathjen, *Proof-theoretic analysis of KPM*,
Arch. Math. Logic 30 (1991), §2) の対応。

**証明列の ✅ は[証明の仕様](#証明の仕様)の E.cert が Lean の定理であることを意味する。**
それ以外の印は ✅ の材料であって ✅ ではない。**印はすべてビルドが計算して付ける**
(手で書けない)。

- 作り方・作業手順・資料の場所 — [plan/README.md](../plan/README.md)
- 表を読むとき・書くときの原則 (注意書き) — [plan/constitutions.md](../plan/constitutions.md)
- この表自身の仕様 — [plan/spec.md](../plan/spec.md)
- 外部の対応表との差分 — [diff.md](diff.md)
- 本筋から外した補足 — [misc.md](misc.md)

## 列の意味

| 列 | 中身 |
|---|---|
| BMS | 行列。リンク先は行の定義 |
| $`\\mathfrak{T}(M)`$ | Rathjen R1 の項 ([D.TM](#dtm)) |
| Buchholz | Buchholz の $`\\mathrm{OT}_B`$ での値。$`\\psi_0(\\Omega_2)`$ 以上は変換写像 (pss2bp) の出力そのもの、それ未満は通称 |
| 証明 | ✅ = [E.cert](#ecert) が定理。空欄 = まだ |
| その他の弱いエビデンス | ✅ の材料。[一覧](#その他の弱いエビデンス) |
| 備考 | その行に固有のこと |

## 対応表

| BMS | $`\\mathfrak{T}(M)`$ | Buchholz | 証明 | その他の弱いエビデンス | 備考 |
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
    -- registry (Evidence/Cert.lean) — a mark can no longer be declared by hand.
    -- It is ✅ or nothing: the column answers one question only, "is E.cert proved".
    let proofCell :=
      if Evidence.Cert.certRows.any (fun p => p.1 == r.m && p.2 == r.t) then
        "[✅](../lean/Evidence/Cert.lean)"
      else ""
    -- fₙ: the value of every expansion is known in closed form, for all n.  It is a
    -- premise of ✅ and not ✅ itself, so it belongs in the weak-evidence column.  The
    -- link is resolved by reading the proof files, so a key that no longer occurs
    -- there prints nothing rather than an unbacked mark.
    let fnCell :=
      if r.proof == "" then [] else
        match proofLine r.proof with
        | some (f, n) => ["[fₙ](../lean/" ++ f ++ "#L" ++ toString n ++ ")"]
        | none => []
    let weak := String.intercalate "+"
      (fnCell ++
       (if r.hasO then [linked "o" "../lean/Trans/TM.lean"] else []) ++
       (if r.ev == "" then [] else [linked r.ev (evLink r.ev)]))
    let buch := buchOf r
    "| " ++ bmsCell ++ " | $`" ++ tex r.t ++ "`$ | " ++
      (if buch == "" then "" else "$`" ++ buch ++ "`$") ++ " | " ++
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
# 証明の仕様

対応表の 1 行 $`(M, t)`$ の証明列に ✅ が付く条件は、これただ 1 つである。

## E.cert

```math
\\mathrm{Certified}(M, t)
```

# 定義

## D.Certified

$`\\mathrm{Certified}`$ は行列とその値の 2 項関係である。

```math
\\mathrm{Certified} \\;\\subseteq\\; \\mathcal{M} \\times \\mathfrak{T}(M)
```

**次の 3 規則で閉じた最小の関係**として定める。

### D.Certified.zero

```math
\\mathrm{Certified}([\\;], 0)
```

### D.Certified.succ

```math
\\begin{aligned}
&\\mathrm{kind}(M) = \\text{後続} \\cr
\\land\\;\\;&\\forall n \\in \\mathbb{N}.\\; \\mathrm{Certified}(M[n], t) \\cr
\\land\\;\\;&t+1 \\in \\mathfrak{T}(M) \\cr
\\longrightarrow\\;\\;&\\mathrm{Certified}(M, t+1)
\\end{aligned}
```

### D.Certified.lim

$`f : \\mathbb{N} \\to \\mathcal{T}`$ について:

```math
\\begin{aligned}
&\\mathrm{kind}(M) = \\text{極限} \\cr
\\land\\;\\;&t \\in \\mathfrak{T}(M) \\cr
\\land\\;\\;&\\forall n.\\; \\mathrm{Certified}(M[n], f_n) \\cr
\\land\\;\\;&\\forall n.\\; f_n \\lt t \\cr
\\land\\;\\;&\\forall n.\\; f_n \\lt f_{n+1} \\cr
\\land\\;\\;&\\forall s \\in \\mathfrak{T}(M).\\; s \\lt t \\;\\to\\; \\exists n.\\; s \\le f_n \\cr
\\longrightarrow\\;\\;&\\mathrm{Certified}(M, t)
\\end{aligned}
```

$`\\lt`$ は $`\\mathfrak{T}(M)`$ の線形順序 ([Rathjen, 1991] 2.3)。

## D.TM

$`\\mathfrak{T}(M) \\subseteq \\mathcal{T}`$ は、**次の規則で閉じた最小の部分集合**
である ([Rathjen, 1991] 2.1)。

```math
\\frac{}{0 \\in \\mathfrak{T}(M)}
\\qquad
\\frac{}{M \\in \\mathfrak{T}(M)}
\\qquad
\\frac{\\alpha \\in \\mathfrak{T}(M) \\quad M < \\alpha}
{\\bar\\omega^{\\alpha} \\in \\mathfrak{T}(M)}
\\qquad
\\frac{\\alpha \\in \\mathfrak{T}(M)}{Z(\\alpha) \\in \\mathfrak{T}(M)}
```

```math
\\frac{\\alpha, \\beta \\in \\mathfrak{T}(M) \\quad \\alpha, \\beta < M}
{\\bar\\varphi(\\alpha, \\beta) \\in \\mathfrak{T}(M)}
\\qquad
\\frac{\\kappa, \\alpha \\in \\mathfrak{T}(M) \\quad \\kappa \\in R
\\quad \\alpha < M \\quad K_\\kappa(\\alpha) < \\alpha}
{\\psi_\\kappa(\\alpha) \\in \\mathfrak{T}(M)}
```

```math
\\frac{\\alpha_1, \\dots, \\alpha_n \\in AP \\quad n \\ge 2
\\quad \\alpha_n \\le \\dots \\le \\alpha_1}
{\\alpha_1 \\oplus \\dots \\oplus \\alpha_n \\in \\mathfrak{T}(M)}
```

$`AP`$ は加法的主要、$`SC`$ は強クリティカル、$`R`$ は正則:

```math
AP = \\{M\\} \\cup \\{\\bar\\omega^\\alpha\\} \\cup \\{\\bar\\varphi(\\alpha,\\beta)\\} \\cup SC,
\\qquad
SC = \\{M\\} \\cup \\{\\psi_\\kappa(\\alpha)\\} \\cup \\{Z(\\alpha)\\},
\\qquad
R = \\{Z(\\alpha)\\}
```


## D.Term

**Rathjen の項**の全体 $`\\mathcal{T}`$ を、次の文法が生成する式の集合とする。
形成条件は課さない — 課したものが [D.TM](#dtm) である。

```math
\\alpha, \\beta \\;::=\\;
0 \\;\\mid\\; M \\;\\mid\\; \\alpha \\oplus \\beta \\;\\mid\\;
\\bar\\omega^{\\alpha} \\;\\mid\\; \\bar\\varphi(\\alpha, \\beta) \\;\\mid\\;
\\psi_{\\alpha}(\\beta) \\;\\mid\\; Z(\\alpha)
```

$`M`$ は最小の弱 Mahlo 基数を表す定数である。

## D.Matrix

**行列**の全体 $`\\mathcal{M}`$。列は自然数の有限列、行列は列の有限列である。

```math
\\mathcal{M} \\;=\\; \\bigl(\\mathbb{N}^{\\ast}\\bigr)^{\\ast}
```

$`X^{\\ast}`$ は $`X`$ の有限列全体を表す。列の本数も列の高さも固定しない。
高さを揃える必要も無い。対応表の行はすべて高さ 2 以下の列からなる。

## D.expand

$`M[n]`$ は行列 $`M`$ の $`n`$ 番目の展開、$`\\mathrm{kind}(M)`$ は行の種別である。

```math
\\cdot[\\cdot] \\;:\\; \\mathcal{M} \\times \\mathbb{N} \\to \\mathcal{M}
\\qquad\\qquad
\\mathrm{kind} \\;:\\; \\mathcal{M} \\to
\\{\\text{空}, \\text{後続}, \\text{極限}\\}
```

規則は BM4 の展開規則そのもので、
[koteitan「バシク行列の数式的定義」](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Koteitan/%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E3%81%AE%E6%95%B0%E5%BC%8F%E7%9A%84%E5%AE%9A%E7%BE%A9)
に従う。実装は [BMS/Expand.lean](../lean/BMS/Expand.lean)。

# その他の弱いエビデンス

いずれも ✅ の材料であって ✅ ではない。$`f_n`$ 以外は有限個の計算検査であり、
較正誤りを検出できない。

| 記号 | 意味 | 全ての $`n`$? |
|---|---|---|
| $`f_n`$ | [E.fs](misc.md#efs) が Lean の定理 | はい |
| `o` | 翻訳関数がこの行列で定義され $`o(M) = t`$ (両辺を同じ写像で計算するので較正誤りは検出できない) | いいえ |
| `bisim6` | 深さ 6 の双模倣 | いいえ |
| `checkAll` | 区間の全標準行列についての一般定理 | はい (区間全体) |

**印はビルドが計算する。** ✅ は証明書レジストリから、$`f_n`$ は行が指す名前空間を
証明ファイルから探して付ける。名前空間を消したり改名したりすると印そのものが消えるので、
実体の無い印は残らない。

# 値についての注意

**$`\\psi_\\Omega(Z(1))`$ 以上の行の値は外部資料と食い違っており、まだ決着していない。**
BMS `(0,0)(1,1)(2,2)` の Buchholz 値 $`\\psi_0(\\psi_2(0))`$ には 3 者が一致するが、
そこから $`\\mathfrak{T}(M)`$ へ訳す段で割れる:

```math
\\text{当方} \\;\\longmapsto\\; \\psi_\\Omega(Z(1)) \\qquad
\\text{資料} \\;\\longmapsto\\; \\psi_\\Omega(\\bar\\varphi(1, \\Omega+1))
```

**根は型にある** ([D.TM](#dtm))。$`Z(1)`$ は $`\\Omega_2`$ ではなく $`I`$ で、
$`\\Omega_2 = \\chi_0(1)`$ は現在の型では書けない。直すには項型を変える必要がある。

**✅ の付いた行は影響を受けない。** ✅ は [E.cert](#ecert) から来ており、
翻訳関数を一度も通らないからである。

外部の対応表との差分は [diff.md](diff.md) に、再実行手順は
[scripts/external-check.py](../scripts/external-check.py) にある。

# 実装

[行 DB と行ごとの検査](../lean/Rows/TM.lean) ·
[BMS の展開](../lean/BMS/Expand.lean) ·
[T(M) の項](../lean/TM/Terms.lean) ·
[T(M) の順序](../lean/TM/Order.lean) ·
[基本列](../lean/TM/FS.lean) ·
[証明書](../lean/Evidence/Cert.lean)
"
  header ++ body ++ footer

/-! ## GATE 5 — no row may sit at a position where `fsN` is meaningless (2026-08-13)

`fsN` is the Nat-indexed fundamental sequence and is only defined where the cofinality is
countable.  Outside that it does not fail loudly: over a 110-term corpus, 27 terms have
uncountable cofinality and `fsN · 3` returns a plausible-looking term for 24 of them
(`φ̄(Ω,0)` has cofinality `Ω` and `fsN · 3 = φ̄(0,Ω)`).  So a row placed there would carry
an E3 statement about a sequence that means nothing, and nothing would say so.

This became live on 2026-08-13: fixing `cofT`'s ψ clause (`ψ_{Z δ}(α)` for `δ` a limit has
cofinality `cof δ`, not `ω`) enlarged the set of such positions.  No current row is
affected — the guard below passes — but it passes as a check rather than as luck.
-/
#guard rows.all fun r =>
  match TM.Term.kindT r.t with
  | .isLim => TM.Term.cofT r.t == TM.Term.omega
  | _ => true
-- CTRL the predicate is reachable: such terms exist and the check would fire on them
#guard !(TM.Term.cofT (TM.Term.psi (TM.Term.Z (TM.Term.Z TM.Term.zero)) TM.Term.zero)
         == TM.Term.omega)

/-! ## The "GATE 4" that was here on 2026-08-13 is WITHDRAWN — see `Evidence/SqV.lean` §K3.20

It claimed four rows carried a non-normal-form term and that three of them were wrong.  It
rested on reading `Evidence.WF.NfOK` as "the term is in normal form".  It is not: its own
docstring calls it a "recursion-local, decidable replacement for the global `Hnf` premise of
`asm_generalB`", and `phiLocalNfOK a b` is vacuous unless `b` is itself a `φ̄` term AND a
`kindV` limit.  It is a side condition for the fundamental-sequence assembly, not a
well-formedness check on terms, and `NfOK t = false` says nothing about the row.

The three rows are right.  `φ̄` here is [Rathjen, 1991] 2.6(vi), which **re-counts fixed points**, so
`φ̄(0,ε₀)` is not `ω^ε₀`; the row's own `name` field says `\omega^{\varepsilon_0+1}`, and
`Term.fsN (φ̄(0,ε₀))` is `0, ε₀, ε₀·2, ε₀·3 …`, matching `oR (expand (0,0)(1,1)(1,0) n)`
term for term.  An independent third-party table agrees with all 17 comparable rows once
the dictionary goes through `phiNF` rather than raw `phi`.

`scripts/external-check.py` opens with exactly this warning, including that neglecting it
once produced 97 spurious disagreements out of 98.  It was not read.
-/

end Rows
