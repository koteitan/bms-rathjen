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
def version : String := "v0.5.0"

/-- One row of the correspondence table. -/
structure Row where
  m : Matrix           -- the BMS matrix
  t : Term             -- the T(M) term
  name : String        -- common name (MathJax)
  proof : String := "" -- namespace of the E3 proof in Rows/Proofs.lean ("" = none yet)
  hasO : Bool := false -- o(M) = t holds (E1)
  ev : String := ""    -- the remaining, weaker evidence
  note : String := ""
  /-- Why this row is on the E-proof shortlist ("" = not on it).  Starts with the side
      the phase change belongs to: **M** BMS, **T** 𝔗(M), **B** Buchholz, **D** disputed
      against an external table.  Chosen by hand, not exhaustively — see the section
      "E 証明の対象行" of the generated table. -/
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
    ev := "oR", note := "外部の表と食い違う ([diff.md](../diff.md) 族 1)",
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
    ev := "oR", note := "外部の表と食い違う ([diff.md](../diff.md) 族 2)",
    sel := "**D** 外部の表と食い違う 9 行の 1 つ" },
  { m := [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[1,1],[2,0],[3,1]],
    t := phi (phi zero zero) (add (phi (phi zero zero)
      (phi (add (phi zero zero) (phi zero zero)) zero)) (phi (phi zero zero) zero)),
    name := "\\bar{\\varphi}(1,\\bar{\\varphi}(1,\\bar{\\varphi}(2,0))+\\bar{\\varphi}(1,0))",
    ev := "oR", note := "外部の表と食い違う ([diff.md](../diff.md) 族 2)",
    sel := "**D** 外部の表と食い違う 9 行の 1 つ" },
  -- 食い違い行 (diff.md 族 3、3 行)。ここだけ当方の値が先方より大きい。
  { m := [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[4,0],[5,1],[6,1],[5,0]],
    t := phi (phi zero zero) (phi (phi zero zero) (phi zero (phi zero
      (phi (add (phi zero zero) (phi zero zero)) zero)))),
    name := "\\bar{\\varphi}(1,\\bar{\\varphi}(1,\\bar{\\varphi}(0,\\bar{\\varphi}(0,\\bar{\\varphi}(2,0)))))",
    ev := "oR", note := "外部の表と食い違う ([diff.md](../diff.md) 族 3)",
    sel := "**D** 外部の表と食い違う 9 行の 1 つ。当方が大きい側" },
  { m := [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[4,0],[5,1],[6,1],[5,0],[6,1]],
    t := phi (phi zero zero) (phi (phi zero zero) (phi zero (phi zero
      (add (phi (add (phi zero zero) (phi zero zero)) zero) (phi (phi zero zero) zero))))),
    name := "\\bar{\\varphi}(1,\\bar{\\varphi}(1,\\bar{\\varphi}(0,\\bar{\\varphi}(0,\\bar{\\varphi}(2,0)+\\bar{\\varphi}(1,0)))))",
    ev := "oR", note := "外部の表と食い違う ([diff.md](../diff.md) 族 3)",
    sel := "**D** 外部の表と食い違う 9 行の 1 つ。当方が大きい側" },
  { m := [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[4,0],[5,1],[6,1],[5,0],[6,1],[7,1]],
    t := phi (phi zero zero) (phi (phi zero zero) (phi zero (phi zero
      (add (phi (add (phi zero zero) (phi zero zero)) zero)
        (phi (add (phi zero zero) (phi zero zero)) zero))))),
    name := "\\bar{\\varphi}(1,\\bar{\\varphi}(1,\\bar{\\varphi}(0,\\bar{\\varphi}(0,\\bar{\\varphi}(2,0)+\\bar{\\varphi}(2,0)))))",
    ev := "oR", note := "外部の表と食い違う ([diff.md](../diff.md) 族 3)",
    sel := "**D** 外部の表と食い違う 9 行の 1 つ。当方が大きい側" },
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
  -- 食い違い行 (diff.md 族 4、3 行)。φ̄(3,ω) の直上をどう数えるかで割れている。
  { m := [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1]],
    t := phi (phi zero zero) (phi (add (phi zero zero) (add (phi zero zero) (phi zero zero)))
      (phi zero (phi zero zero))),
    name := "\\bar{\\varphi}(1,\\bar{\\varphi}(3,\\omega))",
    ev := "oR", note := "外部の表と食い違う ([diff.md](../diff.md) 族 4)",
    sel := "**D** 外部の表と食い違う 9 行の 1 つ" },
  { m := [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1],[2,1]],
    t := phi (add (phi zero zero) (phi zero zero))
      (phi (add (phi zero zero) (add (phi zero zero) (phi zero zero)))
        (phi zero (phi zero zero))),
    name := "\\bar{\\varphi}(2,\\bar{\\varphi}(3,\\omega))",
    ev := "oR", note := "外部の表と食い違う ([diff.md](../diff.md) 族 4)",
    sel := "**D** 外部の表と食い違う 9 行の 1 つ" },
  { m := [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1],[2,1],[2,1]],
    t := phi (add (phi zero zero) (add (phi zero zero) (phi zero zero)))
      (add (phi zero (phi zero zero)) (phi zero zero)),
    name := "\\bar{\\varphi}(3,\\omega+1)",
    ev := "oR", note := "外部の表と食い違う ([diff.md](../diff.md) 族 4)",
    sel := "**D** 外部の表と食い違う 9 行の 1 つ" },
  { m := [[0,0],[1,1],[2,1],[3,0]], t := phi (phi zero (phi zero zero)) zero,
    name := "\\bar{\\varphi}(\\omega,0)", ev := "oR", note := "旧値 ζ_ω を訂正",
    sel := "**T** φ̄ の第 1 引数が数字でなくなる最初" },
  { m := [[0,0],[1,1],[2,1],[3,0],[4,1]], t := phi (phi (phi zero zero) zero) zero,
    name := "\\bar{\\varphi}(\\varepsilon_0,0)", ev := "oR", note := "旧値 ζ_{ε₀} を訂正",
    sel := "**T** φ̄ の第 1 引数が ε 数になる最初" },
  { m := [[0,0],[1,1],[2,1],[3,1]], t := psi (Z zero) zero,
    name := "\\Gamma_0", ev := "oR",
    note := "ψ 項の初登場。旧値 φ̄(3,0) を訂正",
    sel := "**M** (3,1) の最初。**T** ψ の最初。**B** ψ₁ の 3 重入れ子の最初" },
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
    note := "行 1 に 2 が現れる最初の行。旧値 φ̄(ω,0) を訂正",
    sel := "**M** 1 行目に 2 が現れる最初。**T** Z の最初。**B** Ω₂ の最初" },
  { m := [[0,0],[1,1],[2,2],[1,1]],
    t := phi (phi zero zero) (psi (Z zero) (Z (phi zero zero))),
    name := "\\varepsilon_{\\psi_0(\\Omega_2)+1}", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[1,1],[2,1]],
    t := phi (add (phi zero zero) (phi zero zero)) (psi (Z zero) (Z (phi zero zero))),
    name := "\\zeta_{\\psi_0(\\Omega_2)+1}", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[1,1],[2,1],[3,1]],
    t := psi (Z zero) (add (Z (phi zero zero)) (phi zero zero)),
    name := "\\Gamma_{\\psi_0(\\Omega_2)+1}", ev := "oR",
    sel := "**T** ψ の引数に Z と和が同居する最初" },
  { m := [[0,0],[1,1],[2,2],[1,1],[2,2]],
    t := psi (Z zero) (add (Z (phi zero zero)) (phi (phi zero zero) (Z zero))),
    name := "\\psi_0(\\Omega_2+\\psi_1(\\Omega_2))", ev := "oR",
    sel := "**T** Ω が φ̄ の引数に現れる最初。**B** ψ₁ の引数に Ω₂ が入る最初" },
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
    name := "\\psi_0(\\Omega_2\\cdot 2)", ev := "oR", note := "旧値 φ̄(ω²,0) を訂正",
    sel := "**B** ψ₀ の引数が和になる最初" },
  { m := [[0,0],[1,1],[2,2],[2,2],[2,2]],
    t := psi (Z zero) (add (Z (phi zero zero))
      (add (Z (phi zero zero)) (Z (phi zero zero)))),
    name := "\\psi_0(\\Omega_2\\cdot 3)", ev := "oR" },
  { m := [[0,0],[1,1],[2,2],[3,0]],
    t := psi (Z zero) (phi zero (Z (phi zero zero))),
    name := "\\psi_0(\\psi_2(1))", ev := "oR", note := "旧値 φ̄(ω^ω,0) を訂正",
    sel := "**M** (2,2) の後に (3,0) が来る最初。**T** Z が ω 冪の中に入る最初" },
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
    name := "\\psi_0(\\psi_2(\\Omega_1))", ev := "oR",
    sel := "**B** ψ₂ の引数に Ω₁ が入る最初。表の最上行" }
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
    proofCell ++ " | " ++ linked g.evLabel g.evPath ++ " | " ++ g.note ++ " |  |\n"

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

**証明列 ✅ の意味は下の [エビデンス](#エビデンス) を、設計の手順と失敗の記録は
[plan/](../plan/) を参照。**

## 対応表

| BMS | $`\\mathfrak{T}(M)`$ | 通称 | 証明 | その他の弱いエビデンス | 備考 | [E 対象](#e-証明の対象行) |
|---|---|---|---|---|---|---|
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
      proofCell ++ " | " ++ weak ++ " | " ++ r.note ++ " | " ++ r.sel ++ " |\n"
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

対応表の 1 行 $`(M, t)`$ について、**Lean の定理として存在するもの**だけを挙げる。
`E.` は行についての定理、`P.` はその補助命題、`D.` は定義。
Lean に無いもの — 順序型による主定理、順序埋め込みの一般形、各表記系の構造定理 —
は目標であってエビデンスではないので、ここには書かず
[plan/README.md](../plan/README.md) にある。

- [E 証明の対象行](#e-証明の対象行)
- [E.zero / E.succ / E.lim — ✅ の実体](#ezero--esucc--elim---の実体)
  - [✅ が検査していないもの](#-が検査していないもの)
- [E.cofinal (展開と基本列の相互共終)](#ecofinal-展開と基本列の相互共終)
- [証明書の強さと、その限界](#証明書の強さとその限界)
- [その他の弱いエビデンス](#その他の弱いエビデンス)
- [**Γ₀ より上の行について — 値を信用しないこと**](#γ₀-より上の行について--値を信用しないこと)
- [定義](#定義): [D.TM](#dtm-mathfraktm) · [D.CertifiedIn / D.DomI](#dcertifiedin--ddomi)

## E 証明の対象行

全 60 行の E を証明するのは大きすぎるので、**手で選んだ 23 行から始める**。網羅ではない。
選定の基準は「相が変わるところ」— これまで出てこなかった構成子が初めて現れる行、
違う変数を使い始める行 — と、外部の表と食い違う行である。表の一番右の列にその理由を
書いてある。印は相が属する側を表す。

| 印 | 側 | 何を見ているか |
|---|---|---|
| **M** | BMS | 行列の形。行数、成分が取る値、初めて現れる列の型 |
| **T** | $`\\mathfrak{T}(M)`$ | 項の構成子。$`\\bar\\varphi`$ の引数の種類、$`\\psi`$、$`Z`$、$`\\Omega`$ |
| **B** | Buchholz $`\\mathrm{OT}_B`$ | $`\\psi_u`$ の添字 $`u`$、入れ子、引数が和になるところ |
| **D** | — | 外部の表と食い違う 9 行。値そのものが未決 ([diff.md](../diff.md)) |

**D の 9 行は他と性格が違う。** ほかの印は「ここが証明できれば周りも同じ理屈で通る」
という意味だが、D は「どちらが正しいか分かっていない」という意味である。9 行はすべて
Veblen 断片にあるので $`\\psi`$・$`Z`$ の領域には入らない。決着に要るのは行ごとの
添字を固定した上での

```math
\\mathrm{oR}\\,(M[n]) = \\mathrm{fsN}\\,(\\mathrm{oR}\\,M)\\,n
```

で、これは ✅ の行が満たしている E3 そのものである。

**選定は手作業で、網羅を主張しない。** 相の変わり目を機械で数え上げれば、ここに無い行も
出てくる。ここにあるのは「まずこれだけやれば、各側の主要な段差を一度は通る」という
出発点である。

## E.zero / E.succ / E.lim — ✅ の実体

**表の ✅ 列は $`\\mathrm{Certified}\\;M\\;t`$ が存在する行にだけ機械的に付く。**
$`\\mathrm{Certified}`$ は帰納的述語で、**行の $`\\mathrm{kind}`$ によってどの規則が
適用されるかが決まる**。

### E.zero

空行列の行。前提は無く、無条件に成り立つ。

```math
\\mathrm{Certified}\\;[\\,]\\;0
```

### E.succ

```math
\\begin{aligned}
&\\mathrm{kind}\\,M = \\mathrm{succ} \\;\\Longrightarrow \\cr
&\\quad \\Bigl[\\; \\mathrm{Certified}\\;M\\;u \\;\\Longleftrightarrow\\;
   \\exists t.\\; u = t+1 \\cr
&\\qquad\\qquad\\quad \\land\\; \\forall n.\\;\\mathrm{Certified}\\;(M[n])\\;t \\;\\Bigr]
\\end{aligned}
```

すべての展開が同じ $`t`$ を認証するなら、この行は $`t+1`$。

### E.lim

```math
\\begin{aligned}
&\\mathrm{kind}\\,M = \\mathrm{lim} \\;\\Longrightarrow \\cr
&\\quad \\Bigl[\\; \\mathrm{Certified}\\;M\\;t \\;\\Longleftrightarrow\\;
   \\exists f : \\mathbb{N} \\to \\mathfrak{T}(M).\\;
   \\forall n.\\;\\mathrm{Certified}\\;(M[n])\\;(f_n) \\cr
&\\qquad\\qquad\\quad \\land\\; \\forall n.\\;f_n < t \\cr
&\\qquad\\qquad\\quad \\land\\; \\forall n.\\;f_n < f_{n+1} \\cr
&\\qquad\\qquad\\quad \\land\\; \\forall s \\in \\mathfrak{T}(M).\\;s < t \\to \\exists n.\\;s \\le f_n \\;\\Bigr]
\\end{aligned}
```

**$`f`$ は $`\\exists`$ で束縛された列である** — $`\\mathbb{N}`$ の各点に
$`\\mathfrak{T}(M)`$ の項を 1 つ与える写像であり、どこかに定義された特定の列ではない。
**表を読むときに $`f`$ の定義を探す必要はない。無いのが正しく、行ごとに証明が
自分で 1 つ選んで与える。**

**ただし選べるのは見かけだけである。** 4 つの連言のうち
**$`f_n`$ が何であるかを言うのは第 1 のものだけ**で、残る 3 つは
「$`t`$ 未満」「増加」「$`t`$ に共終」という $`f`$ の**性質**を述べるにすぎない。
そして性質は列を 1 つに絞らない。

実例を挙げる。$`\\varepsilon_1`$ の行で基本列の候補を 3 つ立て、**3 つとも**
各添字で増加・$`\\varepsilon_1`$ 未満・共終であることを実測で確認した。
それでも正しい列はその 3 つのどれでもなく、**第 4 のもの**

```math
\\varepsilon_0,\\quad \\omega^{\\varepsilon_0 \\cdot 2},\\quad
\\omega^{\\omega^{\\varepsilon_0 \\cdot 2}},\\quad \\dots
```

だった。**性質をいくつ確かめても列は決まらない**
([plan/constitutions.md](../plan/constitutions.md) C2)。

決めるのは第 1 の連言である。$`f_n`$ は $`M[n]`$ が認証した値**そのもの**でなければ
ならないので、$`f`$ を選んでいるのは**行列**であって $`\\mathfrak{T}(M)`$ 側の都合ではない。
だから $`f`$ が $`\\mathfrak{T}(M)`$ の標準基本列と一致する必要はどこにも無い。

### ✅ が検査していないもの

第 5 前提 $`\\forall s \\in \\mathfrak{T}(M).\\;s \\lt t \\to \\exists n.\\;s \\le f_n`$ は
**$`f`$ が $`t`$ に共終**だと言っている。これと第 2・第 3 前提から
$`\\sup_n f_n = t`$ が出る。**$`\\mathfrak{T}(M)`$ 側の共終性は証明の中にある。**

言っていないのは BMS 側である:

```math
\\sup_n |M[n]| = |M|
```

これが無いと $`\\sup_n f_n = t`$ から $`|M| = t`$ へ渡れない。そして本リポジトリに
$`|M[n]| \\lt |M|`$ も展開列の共終性も**補題として存在しない**。BMS を順序数表記として
読むとき極限行の値が展開の上限であることは**読み方の定義**であって、定理ではないからである。
✅ はこの読み方を仮定した上で $`\\mathfrak{T}(M)`$ 側を尽くしている。

なお下の E.cofinal は**この穴を埋めるものではない**。あちらは
$`\\mathfrak{T}(M)`$ の**標準基本列**と展開列の関係であり、$`f`$ は標準基本列である
必要がないので、E.cofinal を確かめても ✅ の根拠は増えない。両者は別の主張である
(詳細は [plan/README.md の E3 節](../plan/README.md#e3-展開と基本列の整合--本体のエビデンス))。

## E.cofinal (展開と基本列の相互共終)

$`\\mathfrak{T}(M)`$ の**標準基本列**と BMS の展開列を突き合わせる形の証拠。
✅ の無い行のためのもので、**✅ の根拠ではない** — ✅ が要る共終性は
$`\\mathrm{Certified}`$ の第 4 連言として既に、しかも $`o`$ に触れない形で入っている。

この形をなぜ等式ではなく相互共終で立てるのか、等式で立てると何を取り違えるのかは
**設計の話なので** [plan/README.md の E3 節](../plan/README.md#e3-展開と基本列の整合--本体のエビデンス)
にある。

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

## その他の弱いエビデンス

いずれも有限個の計算検査であり、較正誤りを検出できない。順序埋め込みも corpus 上の
`Evidence.Check.checkE2` という計算検査としてのみ存在し、定理ではないのでここに置く。

| 記号 | 意味 |
|---|---|
| `o` | 翻訳関数がこの行列で定義され $`o(M) = t`$ (両辺を同じ写像で計算するので較正誤りは検出できない) |
| `oR` | オラクル較正済みの候補値。**2 段の合成**で、定義域は BMS の 2 行断片 (下記)。全行一致をビルド時 `#guard` で強制 |
| `bisim6` | 深さ 6 の双模倣 |
| `oStageC` | Stage C の候補翻訳の値の一致 |

### `oR` が何の合成なのか

`oR` は変換写像そのものではなく、**2 段の合成**である。

```math
\\mathrm{BMS}\\ \\xrightarrow{\\ \\text{oracle}\\ }\\ \\mathrm{OT}_B
\\ \\xrightarrow{\\ \\mathrm{dict}\\ }\\ \\mathfrak{T}(M)
```

1 段目が P進大好きbot 氏の変換写像 (PSS 停止性証明のもの、naruyoko 氏の実装) で、
その行き先は **Buchholz の表記系 $`\\mathrm{OT}_B`$** — $`D_u a = \\psi_u(a)`$
(Buchholz 1986) であって、Rathjen の $`\\mathfrak{T}(M)`$ ではない。
2 段目 `dict` がこのリポジトリの用意する辞書である。像への順序同型で値を保つ**という
主張**だが、**それは定理ではなく測定**である。

**$`D_u`$ は Rathjen の $`\\psi_{\\Omega_{u+1}}`$ ではない。** 土台が違う:

| | Veblen 関数 | $`\\psi`$ の始まり |
|---|---|---|
| Buchholz $`\\mathrm{OT}_B`$ | 持たない。Veblen 階層は $`D_0`$ の引数の中の $`\\Omega`$ 冪として符号化される | — |
| Rathjen $`\\mathfrak{T}(M)`$ | 2 変数 $`\\bar\\varphi`$ が $`(0,M)`$ 全体で原始的 | Veblen が止まる所から。$`\\psi_{Z0}(0) = \\Gamma_0`$ |

だから `dict` は名前の付け替えではなく、**本物の翻訳**である。

**定義域は BMS の 2 行断片**である — 各列の高さが 2 以下で、行列が空でないもの。
その外では `oR` は `none` を返す。表の行はすべてこの範囲に収まる。
**表がこの断片の外へ伸びることは、いまの `oR` ではできない。**

## Γ₀ より上の行について — 値を信用しないこと

**この節の内容は 2026-08-12 に判明したもので、当該行の値はまだ直っていない。**

`(0,0)(1,1)(2,2)` 以上の行の値は `oR = (1+\\cdot) \\circ \\mathrm{dict} \\circ \\mathrm{oRB}`
から来ている。この `dict` について、次が証明されている (`lean/Trans/Dict.lean` §4)。

**外部資料と食い違う。** BMS `(0,0)(1,1)(2,2)` の Buchholz 値 $`\\psi_0(\\psi_2(0))`$ には
3 者が一致している (このリポジトリの pss2bp 移植、Hexirp 氏の解析、スプレッドシート)。
食い違うのはそこから $`\\mathfrak{T}(M)`$ へ翻訳する段だけである。

```math
\\mathrm{dict} \\;\\longmapsto\\; \\psi_\\Omega(Z(1)) \\qquad
\\text{資料} \\;\\longmapsto\\; \\psi_\\Omega(\\bar\\varphi(1, \\Omega+1))
```

両方とも正規形で、等しくなく、資料の値のほうが真に小さい (3 本とも `decide` で証明済み)。
資料側には $`\\mathfrak{T}(M)`$ を直接与える 3 つ目の独立な資料が加わり
(Hexirp 氏の BMS↔Rathjen 対応表、`scripts/hexirp-rathjen-check.py` で再実行できる)、
そこでも同じ $`\\psi_\\Omega(\\bar\\varphi(1, \\Omega+1))`$ である。
資料はいずれも未証明なので**どちらが正しいかはここでは決まらない**が、
`dict` 側に立つ資料は 1 つも無い。

**ここには「`dict` は順序を保存しないので翻訳として失格」と書いてあったが、取り消した
(2026-08-12)。** 反例の母集団を外部の標準形判定器で作っており、その判定器に
コールバックの引数取り違えのバグがあった。正しい判定器で作り直した母集団
(標準形 3193 個、順序対 5096028 組) では**順序反転は 0 件**である。詳細と、
誤って通っていた 3 項を固定した陰性対照は `Trans/Dict.lean` §4 にある。

**根はもっと深い。** [`lean/TM/Terms.lean`](../lean/TM/Terms.lean) はこのリポジトリの
$`\\chi`$ を `Z a = χ_a(0)` と 1 引数に潰している。しかし原典では $`\\chi`$ は 2 引数で、
**第 2 引数が $`\\Omega`$ 階層を枚挙する**:

```math
\\chi_0(\\alpha) = \\Omega_{1+\\alpha}, \\qquad
\\chi_1(0) = I \\;(\\text{最小の弱到達不能基数})
```

つまり `Z 1` は $`\\Omega_2`$ ではなく $`I`$ であり、
**$`\\Omega_2 = \\chi_0(1)`$ は現在の型では書けない**。
当該の行はその $`\\Omega_2`$ が要る領域にある。値を直すには型を変える必要があり、
それは $`\\mathfrak{T}(M)`$ の項型とその上のすべてに波及するので、まだ着手していない。

**したがって、これらの行の値は資料と食い違ったままであり、信用してはいけない。**
✅ の付いた行は影響を受けない —
✅ は `Certified` から来ており、読み手を一度も通らないからである。

外部資料との突き合わせは [`scripts/external-check.py`](../scripts/external-check.py) で再実行できる。

# 定義

## D.TM ($`\\mathfrak{T}(M)`$)

$`M`$ は最小の弱 Mahlo 基数。$`\\mathfrak{T}(M)`$ は**次の規則で閉じた最小の項集合**
(Rathjen 1991 §2.1):

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
\\quad \\alpha < M \\quad K_\\kappa \\alpha < \\alpha}
{\\psi_\\kappa(\\alpha) \\in \\mathfrak{T}(M)}
```

```math
\\frac{\\alpha_1, \\dots, \\alpha_n \\in AP \\quad n \\ge 2
\\quad \\alpha_n \\le \\dots \\le \\alpha_1}
{\\alpha_1 \\oplus \\dots \\oplus \\alpha_n \\in \\mathfrak{T}(M)}
```

ここで $`AP`$ は加法的主要な項、$`SC`$ は強クリティカルな項、$`R`$ は正則:

```math
AP = \\{M\\} \\cup \\{\\bar\\omega^\\alpha\\} \\cup \\{\\bar\\varphi(\\alpha,\\beta)\\} \\cup SC,
\\qquad
SC = \\{M\\} \\cup \\{\\psi_\\kappa\\alpha\\} \\cup \\{Z\\alpha\\},
\\qquad
R = \\{Z\\alpha\\}
```

$`\\oplus`$ の条件 (成分が $`AP`$、降順) が一意な正規形を与える。

**$`\\bar\\varphi`$ は $`\\omega^\\cdot`$ の不動点を飛ばして数える。**
$`\\bar\\varphi(0,\\beta)`$ は最初の不動点未満では $`\\omega^\\beta`$ だが、

```math
\\bar\\varphi(0, \\varepsilon_0) = \\omega^{\\varepsilon_0 + 1} \\ne \\varepsilon_0
```

**不動点の下では 2 つの読みが一致するので、そこだけで較正した関数・コーパス・読者は
上で静かに誤る。**

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

The three rows are right.  `φ̄` here is [R91] 2.6(vi), which **re-counts fixed points**, so
`φ̄(0,ε₀)` is not `ω^ε₀`; the row's own `name` field says `\omega^{\varepsilon_0+1}`, and
`Term.fsN (φ̄(0,ε₀))` is `0, ε₀, ε₀·2, ε₀·3 …`, matching `oR (expand (0,0)(1,1)(1,0) n)`
term for term.  An independent third-party table agrees with all 17 comparable rows once
the dictionary goes through `phiNF` rather than raw `phi`.

`scripts/external-check.py` opens with exactly this warning, including that neglecting it
once produced 97 spurious disagreements out of 98.  It was not read.
-/

end Rows
