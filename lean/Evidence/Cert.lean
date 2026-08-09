/-
Evidence/Cert.lean — semantic certificates (the v0.1.42 doctrine)

The calibration failure (see plan/README.md, 較正事故) showed that theorems about
the translation o? alone cannot carry the table's semantic claim "the ordinal of
M is (the value of) t": o? was self-consistently compressed from
(0,0)(1,1)(2,1)(2,0) upward and every finite check passed.

This file defines the object that CAN carry the claim: `Certified M t`, the
closed semantic induction itself, following the framework of P進大好きbot,
「変換写像による解析」 (命題5: on a tree with the zero/successor/limit trichotomy,
the ordinal of a term is forced by 0 / +1 / sup along the fundamental sequences).

  * `zero`: the empty matrix has value 0.
  * `succ`: a successor matrix (constant expansion) has value (predecessor)+1 —
    the successor law is what excludes normal-function recalibrations, so the
    calibration is pinned to the identity once the ground and limits are fixed.
  * `lim`: a limit matrix has value t if its expansions are certified with
    values that form a strictly increasing sequence below t that is COFINAL in t
    (every s < t is overtaken).  The cofinality premise quantifies over ALL
    terms s, so a compressed assignment cannot be certified: below a compressed
    t there is a term never overtaken.

A derivation of `Certified M t` therefore contains certificates for the entire
expansion closure of M — "islands" (rows whose expansions leave the proven
region, the mechanism of the calibration failure) are impossible by
construction.  What remains conditional is only the BMS side's well-foundedness
and the target notation's own correctness ([R91]), exactly as the plan's
conditional main theorem MT always stated.

The table's proof column is driven by `certRows` + `certRows_ok`: gentable marks
a row exactly when its (matrix, term) pair is registered here, and the single
theorem `certRows_ok` forces every registered pair to carry a derivation.
Labels are computed from certificates, never declared.

NEGATIVE CONTROL (the review exercise for the definition itself; keep current):
the one place Lean cannot check is whether THIS definition captures the
semantics.  The standing control: try to certify `(0)(1) ↦ ω+5`.  With the
cofinality premise as written (`∀ s < t, ∃ n, s ≤ fs' n`) the attempt fails at
`s = ω+3`: no `fs' n = ofNat n` overtakes it.  If someone edits the premise and
the attempt STARTS to succeed (e.g. the flipped `∃ n, fs' n ≤ s` accepts it),
the definition is broken.  The definitive machine version of this control is
the planned meta-theorem `cert_sound` (plan/README.md): with the premises as
hypotheses, a wrong premise makes its limit case unprovable.

Scope of the conditional hypotheses (2026-08-09, per koteitan): BMS
well-foundedness is needed only on the region the table covers, and there it is
a THEOREM, not a hypothesis — once o is proven injective and order-preserving
on a certified region, well-foundedness transfers from the T(M) segment
(命題7(4) of the framework; the T(M) segment's own well-orderedness comes from
the Buchholz dictionary + pss-proof's syntactic well-foundedness, or from a
Lean-internal embedding into mathlib ordinals).
-/
import Trans.TM
import TM.FS

namespace Evidence.Cert

open BMS (Matrix)
open TM (Term)
open TM.Term

/-- The value of `M` is `t`: the closed semantic induction.  See the header. -/
inductive Certified : Matrix → Term → Prop
  | zero : Certified [] Term.zero
  | succ {M : Matrix} {t : Term} :
      BMS.kind M = .succ →
      (∀ n, Certified (BMS.expand M n) t) →
      Certified M (plus t one)
  | lim {M : Matrix} {t : Term} (fs' : Nat → Term) :
      BMS.kind M = .lim →
      (∀ n, Certified (BMS.expand M n) (fs' n)) →
      (∀ n, lt (fs' n) t = true) →
      (∀ n, lt (fs' n) (fs' (n + 1)) = true) →
      (∀ s, lt s t = true → ∃ n, le s (fs' n) = true) →
      Certified M t

/-! ## The first certificates (finite values; the pipeline demonstrator)

The genuinely hard derivations — a limit certificate contains certificates for
every expansion — are the rebuild's work, region by region.  The finite rows
below exercise the whole pipeline (derivation → registry → table mark). -/

theorem cert_empty : Certified [] Term.zero := .zero

private theorem expand_one (n : Nat) : BMS.expand [[0]] n = [] := rfl

private theorem expand_two (n : Nat) : BMS.expand [[0], [0]] n = [[0]] := rfl

theorem cert_one : Certified [[0]] one :=
  .succ rfl (fun n => expand_one n ▸ Certified.zero)

theorem cert_two : Certified [[0], [0]] (ofNat 2) :=
  .succ rfl (fun n => expand_two n ▸ cert_one)

/-! ## The registry

gentable marks ✅ exactly on the rows listed here; `certRows_ok` is the gate. -/

/-- The registered certified rows. -/
def certRows : List (Matrix × Term) :=
  [([], Term.zero), ([[0]], one), ([[0], [0]], ofNat 2)]

/-- Every registered pair carries a derivation.  Extending `certRows` without
    extending this proof breaks the build — the label cannot outrun the
    certificates. -/
theorem certRows_ok : ∀ p ∈ certRows, Certified p.1 p.2 := by
  intro p hp
  simp only [certRows, List.mem_cons] at hp
  rcases hp with h | h | h | h
  · rw [h]; exact cert_empty
  · rw [h]; exact cert_one
  · rw [h]; exact cert_two
  · cases h

end Evidence.Cert
