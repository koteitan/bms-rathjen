import Trans.TM
import TM.FS
import Trans.Recal
import Evidence.StageA
import Evidence.WF
/-
Evidence/Cert.lean — semantic certificates (the v0.1.42 doctrine)

(The imports are on the first lines: the kimina server used to verify this file
mis-splits a snippet whose `import` is preceded by a comment.)

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
    (every term s < t is overtaken).  The cofinality premise quantifies over ALL
    terms of 𝔗(M), so a compressed assignment cannot be certified: below a
    compressed t there is a term never overtaken.

A derivation of `Certified M t` therefore contains certificates for the entire
expansion closure of M — "islands" (rows whose expansions leave the proven
region, the mechanism of the calibration failure) are impossible by
construction.  What remains conditional is only the BMS side's well-foundedness
and the target notation's own correctness ([Rathjen, 1991]), exactly as the plan's
conditional main theorem MT always stated.

The table's proof column is driven by `certRows` + `certRows_ok`: gentable marks
a row exactly when its (matrix, term) pair is registered here, and the single
theorem `certRows_ok` forces every registered pair to carry a derivation.
Labels are computed from certificates, never declared.

DEFINITION CHANGE (2026-08-09, certificate lane).  The cofinality premise now
reads `∀ s, inT s = true → lt s t = true → ∃ n, le s (fs' n) = true`: the
quantifier ranges over the TERMS OF 𝔗(M) ([Rathjen, 1991] 2.1, the predicate `inT` of
TM/NF.lean), not over all inhabitants of the free inductive type `Term`.

  Why.  Without the guard the `lim` constructor is VACUOUS — not merely hard to
  use, but unusable for every limit row.  `lt` compares a formal sum by its head
  component alone (clause 2.3.10, `| add a _, t' => ltF fuel a t'`), which is
  correct only when the components descend, i.e. exactly on `inT` terms.  The
  ill-formed term `1 + M` (rejected by `inT`: M ≰ 1) therefore satisfies
  `lt (add one M) omega = true` while `le (add one M) (ofNat n) = false` for
  every n, so ω can never be certified; `phi zero (add one M)` does the same to
  ω^ω, and the same trick blocks every limit whose fundamental sequence is not
  eventually above every junk head.  (Checked by `#guard` in §8.)

  What is NOT weakened.  The standing negative control below still refutes: its
  witness ω+3 = `plus omega (ofNat 3)` satisfies `inT`, so a compressed
  assignment is still caught by a genuine term of the notation system.

NEGATIVE CONTROL (the review exercise for the definition itself; keep current):
the one place Lean cannot check is whether THIS definition captures the
semantics.  The standing control: try to certify `(0)(1) ↦ ω+5`.  With the
cofinality premise as written (`∀ s ∈ 𝔗(M), s < t → ∃ n, s ≤ fs' n`) the attempt
fails at `s = ω+3`: no `fs' n = ofNat n` overtakes it, and `inT (ω+3) = true`.
If someone edits the premise and the attempt STARTS to succeed (e.g. the flipped
`∃ n, fs' n ≤ s` accepts it), the definition is broken.  The definitive machine
version of this control is the planned meta-theorem `cert_sound`
(plan/README.md): with the premises as hypotheses, a wrong premise makes its
limit case unprovable.

Scope of the conditional hypotheses (2026-08-09, per koteitan): BMS
well-foundedness is needed only on the region the table covers, and there it is
a THEOREM, not a hypothesis — once o is proven injective and order-preserving
on a certified region, well-foundedness transfers from the T(M) segment
(命題7(4) of the framework; the T(M) segment's own well-orderedness comes from
the Buchholz dictionary + pss-proof's syntactic well-foundedness, or from a
Lean-internal embedding into mathlib ordinals).
-/

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
      (∀ s, inT s = true → lt s t = true → ∃ n, le s (fs' n) = true) →
      Certified M t

/-! ## §1 A local toolkit for the decidable order of 𝔗(M)

`lt` is `ltF` at a fixed amount of fuel, so an order statement is proved in the
form "for every sufficiently large fuel" and a *hypothesis* `ltF f s t = true` is
consumed with `f` universally quantified.

These lemmas duplicate `Rows/ProofsB.lean §1` and the `ofNat` facts of
`Rows/ProofsB.lean §7` / `Evidence/StageB.lean §3`.  The duplication is forced:
`Rows/TM.lean` imports THIS file (the registry drives the table), so importing
`Rows.ProofsB` here would close an import cycle. -/

private theorem ltF_irrefl (f : Nat) (x : Term) : ltF f x x = false := by
  cases f with
  | zero => rfl
  | succ g =>
    show (if (x == x) = true then false else _) = false
    simp

private theorem ne_of_ltF {f : Nat} {x y : Term} (h : ltF f x y = true) : x ≠ y := by
  intro hc
  subst hc
  rw [ltF_irrefl] at h
  exact Bool.noConfusion h

private theorem ltF_zero {f : Nat} (hf : 1 ≤ f) {t : Term} (h : t ≠ zero) :
    ltF f zero t = true := by
  cases f with
  | zero => omega
  | succ g => cases t <;> first | (exact absurd rfl h) | rfl

private theorem ltF_lt_zero (f : Nat) (a : Term) : ltF f a zero = false := by
  cases f with
  | zero => rfl
  | succ g => cases a <;> rfl

private theorem lt_of_ltF {x y : Term} {N : Nat} (h : ∀ f, N ≤ f → ltF f x y = true)
    (hN : N ≤ 2 * (x.deg + y.deg) + 8) : lt x y = true := h _ hN

/-! ### Destructuring the formation conditions `inT` ([Rathjen, 1991] 2.1) -/

private theorem isAP_ne_zero {a : Term} (h : a.isAP = true) : a ≠ zero := by
  intro hc; rw [hc] at h; exact Bool.noConfusion h

private theorem inT_add {a b : Term} (h : inT (add a b) = true) :
    a.isAP = true ∧ inT a = true ∧ inT b = true := by
  simp only [inT, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

private theorem inT_phi {a b : Term} (h : inT (phi a b) = true) :
    inT a = true ∧ inT b = true := by
  simp only [inT, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2⟩

/-- In a sum of 𝔗(M) the tail is never `0` (its head must be additively principal). -/
private theorem inT_add_ne_zero : ∀ {a b : Term}, inT (add a b) = true → b ≠ zero
  | _, zero, h => by simp only [inT, Bool.and_eq_true] at h; exact absurd h.2 (by simp [isAP])
  | _, add _ _, _ => by intro hc; exact Term.noConfusion hc
  | _, M, _ => by intro hc; exact Term.noConfusion hc
  | _, omg _, _ => by intro hc; exact Term.noConfusion hc
  | _, phi _ _, _ => by intro hc; exact Term.noConfusion hc
  | _, psi _ _, _ => by intro hc; exact Term.noConfusion hc
  | _, Z _, _ => by intro hc; exact Term.noConfusion hc

/-- The components of a sum of 𝔗(M) descend: the head of the tail is at most the head. -/
private theorem inT_add_head_le : ∀ {a b : Term}, inT (add a b) = true →
    le ((toList b).headD zero) a = true
  | _, zero, h => by simp only [inT, Bool.and_eq_true] at h; exact absurd h.2 (by simp [isAP])
  | _, add _ _, h => by simp only [inT, Bool.and_eq_true] at h; exact h.2
  | _, M, h => by simp only [inT, Bool.and_eq_true] at h; exact h.2.2
  | _, omg _, h => by simp only [inT, Bool.and_eq_true] at h; exact h.2.2
  | _, phi _ _, h => by simp only [inT, Bool.and_eq_true] at h; exact h.2.2
  | _, psi _ _, h => by simp only [inT, Bool.and_eq_true] at h; exact h.2.2
  | _, Z _, h => by simp only [inT, Bool.and_eq_true] at h; exact h.2.2

/-! ### Nothing but `0` lies below `1`

This is where the formation conditions are indispensable: `lt` decides a sum by
its head component alone, so the junk term `1 + M` would otherwise be below `1`'s
successors without being below any of them. -/

private theorem ltF_one_false : ∀ (f : Nat) (x : Term), inT x = true → x ≠ zero →
    ltF f x one = false
  | 0, _, _, _ => rfl
  | f + 1, x, hx, hne => by
    cases x with
    | zero => exact absurd rfl hne
    | M => rfl
    | add a b =>
      obtain ⟨hap, ha, _⟩ := inT_add hx
      show ltF f a one = false
      exact ltF_one_false f a ha (isAP_ne_zero hap)
    | omg a => rfl
    | phi a b =>
      simp only [ltF]
      cases hxo : ((phi a b) == one) with
      | true => simp
      | false =>
        simp only [Bool.false_eq_true, if_false]
        show (if (a == zero) = true then ltF f b zero
              else if ltF f a zero = true then ltF f b (phi zero zero)
              else ((phi a b == zero) || ltF f (phi a b) zero)) = false
        rw [ltF_lt_zero, ltF_lt_zero]
        simp [ltF_lt_zero]
    | psi k a =>
      show ((psi k a == zero) || (psi k a == zero) || ltF f (psi k a) zero
            || ltF f (psi k a) zero) = false
      simp [ltF_lt_zero]
    | Z a =>
      show ((Z a == zero) || (Z a == zero) || ltF f (Z a) zero || ltF f (Z a) zero) = false
      simp [ltF_lt_zero]

private theorem lt_one_false {x : Term} (hx : inT x = true) (hne : x ≠ zero) :
    lt x one = false := ltF_one_false _ x hx hne

private theorem le_one_eq {x : Term} (hx : inT x = true) (hne : x ≠ zero)
    (h : le x one = true) : x = one := by
  simp only [TM.Term.le, lt_one_false hx hne, Bool.or_false, beq_iff_eq] at h
  exact h

private theorem eq_zero_of_ltF_one {f : Nat} {b : Term} (hb : inT b = true)
    (h : ltF f b one = true) : b = zero := by
  cases b <;> first
    | rfl
    | exact absurd h (by
        rw [ltF_one_false f _ hb (by intro hc; exact Term.noConfusion hc)]; simp)

/-! ### The finite terms `ofNat n` -/

private theorem filter_le_one : ∀ n,
    (List.replicate n one).filter (fun a => le one a) = List.replicate n one
  | 0 => rfl
  | n + 1 => by
    show (one :: List.replicate n one).filter _ = _
    rw [List.filter_cons_of_pos (by rfl), filter_le_one n]
    rfl

private theorem toList_ofNat : ∀ n, toList (ofNat n) = List.replicate n one
  | 0 => rfl
  | n + 1 => by
    show toList (plus (ofNat n) one) = List.replicate (n + 1) one
    unfold plus
    rw [show toList (one : Term) = [one] from rfl]
    show toList (ofList ((toList (ofNat n)).filter (fun a => le one a) ++ [one])) = _
    rw [toList_ofNat n, filter_le_one n, ← List.replicate_succ']
    exact toList_ofList (fun x hx => by rw [List.eq_of_mem_replicate hx]; rfl)

private theorem ofNat_rep : ∀ n, ofNat n = ofList (List.replicate n one)
  | 0 => rfl
  | n + 1 => by
    show plus (ofNat n) one = ofList (List.replicate (n+1) one)
    unfold plus
    rw [show toList (one : Term) = [one] from rfl]
    show ofList ((toList (ofNat n)).filter (fun a => le one a) ++ [one]) = _
    rw [toList_ofNat n, filter_le_one n, ← List.replicate_succ']

private theorem ofNat_shape : ∀ n, ofNat (n + 2) = add one (ofNat (n + 1)) := by
  intro n
  rw [ofNat_rep (n+2), ofNat_rep (n+1)]
  show ofList (one :: List.replicate (n+1) one) = add one (ofList (List.replicate (n+1) one))
  rw [List.replicate_succ]
  rfl

private theorem ofNat_inj {i j : Nat} (h : ofNat i = ofNat j) : i = j := by
  have h1 := congrArg toList h
  rw [toList_ofNat, toList_ofNat] at h1
  have h2 := congrArg List.length h1
  simpa using h2

private theorem ofNat_ne_zero : ∀ m, (ofNat (m + 1) : Term) ≠ zero
  | 0 => by intro hc; exact Term.noConfusion hc
  | m + 1 => by rw [ofNat_shape m]; intro hc; exact Term.noConfusion hc

private theorem deg_ofNat : ∀ n, n ≤ (ofNat n).deg
  | 0 => by simp [ofNat, deg]
  | 1 => by show (1:Nat) ≤ 3; omega
  | n + 2 => by
    rw [ofNat_shape n]
    show n + 2 ≤ 1 + (one : Term).deg + (ofNat (n+1)).deg
    have := deg_ofNat (n+1)
    show n + 2 ≤ 1 + 3 + (ofNat (n+1)).deg
    omega

private theorem ltF_ofNat_succ : ∀ (n f : Nat), n + 2 ≤ f →
    ltF f (ofNat n) (ofNat (n + 1)) = true
  | 0, f, hf => ltF_zero (by omega) (by intro hc; exact Term.noConfusion hc)
  | 1, f, hf => by
    cases f with
    | zero => omega
    | succ g => rfl
  | n + 2, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      rw [ofNat_shape n, ofNat_shape (n+1)]
      show (if (add one (ofNat (n+1)) == add one (ofNat (n+2))) = true then false
            else if ((one : Term) == one) = true then ltF g (ofNat (n+1)) (ofNat (n+2))
                 else ltF g one one) = true
      have hne : ltF g (ofNat (n+1)) (ofNat (n+2)) = true := ltF_ofNat_succ (n+1) g (by omega)
      rw [show ((add one (ofNat (n+1)) == add one (ofNat (n+2))) = false) from by
        simp [ne_of_ltF hne]]
      simp [hne]

private theorem lt_ofNat_succ (n : Nat) : lt (ofNat n) (ofNat (n + 1)) = true := by
  refine lt_of_ltF (N := n + 2) (fun f hf => ltF_ofNat_succ n f hf) ?_
  have h1 := deg_ofNat n
  show n + 2 ≤ 2 * ((ofNat n).deg + (ofNat (n+1)).deg) + 8
  omega

private theorem ltF_one_omega : ∀ f, 2 ≤ f → ltF f one omega = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g =>
    show (if ((one : Term) == omega) = true then false
          else if ((zero : Term) == zero) = true then ltF g zero one else ltF g zero zero) = true
    simp only [show (((one : Term)) == omega) = false from rfl, Bool.false_eq_true, if_false,
      beq_self_eq_true, if_true]
    exact ltF_zero (by omega) (by intro hc; exact Term.noConfusion hc)

private theorem ltF_ofNat_omega : ∀ (n f : Nat), 3 ≤ f → ltF f (ofNat n) omega = true
  | 0, f, hf => ltF_zero (by omega) (by intro hc; exact Term.noConfusion hc)
  | 1, f, hf => ltF_one_omega f (by omega)
  | n + 2, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      rw [ofNat_shape n]
      show (if (add one (ofNat (n+1)) == omega) = true then false else ltF g one omega) = true
      simp only [show ((add one (ofNat (n+1)) == omega) = false) from rfl,
        Bool.false_eq_true, if_false]
      exact ltF_one_omega g (by omega)

private theorem lt_ofNat_omega (n : Nat) : lt (ofNat n) omega = true := by
  refine lt_of_ltF (N := 3) (fun f hf => ltF_ofNat_omega n f hf) ?_
  show 3 ≤ 2 * ((ofNat n).deg + (omega : Term).deg) + 8
  omega

/-! ## §2 The finite region: the whole column-of-zeros family at once

`(0)(0)…(0)` with k columns is a successor matrix whose expansion drops the last
column, so `Certified` follows by induction on k.  This subsumes the first three
hand-made certificates. -/

private theorem rep_last (c : BMS.Col) (k : Nat) :
    (List.replicate (k + 1) c).getLast? = some c := by
  rw [List.replicate_succ']
  exact List.getLast?_concat

private theorem rep_dropLast (c : BMS.Col) (k : Nat) :
    (List.replicate (k + 1) c).dropLast = List.replicate k c := by
  rw [List.replicate_succ']
  exact List.dropLast_concat

/-- The matrix `(0)(0)…(0)` with `k` columns. -/
def zeros (k : Nat) : Matrix := List.replicate k [0]

private theorem kind_zeros (k : Nat) : BMS.kind (zeros (k + 1)) = .succ := by
  show (match (List.replicate (k+1) ([0] : BMS.Col)).getLast? with
        | none => BMS.Kind.zero
        | some L => match BMS.lnz L with
          | none => BMS.Kind.succ
          | some _ => BMS.Kind.lim) = _
  rw [rep_last]
  rfl

private theorem expand_zeros (k n : Nat) : BMS.expand (zeros (k + 1)) n = zeros k := by
  have hexp : BMS.expand? (zeros (k+1)) n = some ((zeros (k+1)).dropLast) := by
    simp only [zeros, BMS.expand?, rep_last, Option.bind_eq_bind, Option.bind_some,
      show BMS.lnz ([0] : BMS.Col) = none from rfl, Option.pure_def]
  show (BMS.expand? (zeros (k+1)) n).getD [] = _
  rw [hexp]
  show (zeros (k+1)).dropLast = zeros k
  exact rep_dropLast _ k

/-- **The finite region, in general.**  `(0)…(0)` with `k` columns has value `k`. -/
theorem cert_zeros : ∀ k, Certified (zeros k) (ofNat k)
  | 0 => .zero
  | k + 1 => .succ (kind_zeros k) (fun n => (expand_zeros k n) ▸ cert_zeros k)

theorem cert_empty : Certified [] Term.zero := .zero

theorem cert_one : Certified [[0]] one := cert_zeros 1

theorem cert_two : Certified [[0], [0]] (ofNat 2) := cert_zeros 2

/-! ## §3 ω — the first limit certificate

L1 (the cofinality obligation) for `t = ω`: the terms of 𝔗(M) below ω are
exactly the natural numbers, so the expansion values `1, 2, 3, …` overtake every
one of them.  The quantifier is over ALL terms of the notation system, not over
values of the translation — that is the point of the doctrine. -/

/-- Every term of 𝔗(M) whose head component is at most `1` is a natural number. -/
private theorem tail_ofNat : ∀ (b : Term), inT b = true → b ≠ zero →
    le ((toList b).headD zero) one = true → ∃ j, b = ofNat (j + 1)
  | zero, _, hne, _ => absurd rfl hne
  | add c d, h, _, hle => by
    obtain ⟨hap, hc, hd⟩ := inT_add h
    rw [show (toList (add c d)).headD zero = c from rfl] at hle
    have hc1 : c = one := le_one_eq hc (isAP_ne_zero hap) hle
    have hdhead : le ((toList d).headD zero) c = true := inT_add_head_le h
    rw [hc1] at hdhead
    obtain ⟨j, hj⟩ := tail_ofNat d hd (inT_add_ne_zero h) hdhead
    exact ⟨j + 1, by rw [hc1, hj, ofNat_shape j]⟩
  | M, h, hne, hle => ⟨0, le_one_eq h hne hle⟩
  | omg _, h, hne, hle => ⟨0, le_one_eq h hne hle⟩
  | phi _ _, h, hne, hle => ⟨0, le_one_eq h hne hle⟩
  | psi _ _, h, hne, hle => ⟨0, le_one_eq h hne hle⟩
  | Z _, h, hne, hle => ⟨0, le_one_eq h hne hle⟩

/-- **L1 for ω.**  Every term of 𝔗(M) below ω is a natural number.  Stated with
    the fuel universally quantified, so that the hypothesis can be consumed at
    whatever fuel the recursive call of `ltF` supplies. -/
theorem below_omega : ∀ (f : Nat) (s : Term), inT s = true → ltF f s omega = true →
    ∃ k, s = ofNat k
  | 0, s, _, h => by exact absurd h (by rw [show ltF 0 s omega = false from rfl]; simp)
  | f + 1, s, hs, h => by
    cases s with
    | zero => exact ⟨0, rfl⟩
    | M =>
      rw [show ltF (f+1) M omega = false from Evidence.StageA.ltF_M_phi (f+1) zero one] at h
      exact Bool.noConfusion h
    | omg a =>
      rw [show ltF (f+1) (omg a) omega = false from rfl] at h
      exact Bool.noConfusion h
    | psi k a =>
      rw [show ltF (f+1) (psi k a) omega
            = ((psi k a == zero) || (psi k a == one) || ltF f (psi k a) zero
               || ltF f (psi k a) one) from rfl,
          show ((psi k a == zero) : Bool) = false from rfl,
          show ((psi k a == one) : Bool) = false from rfl,
          ltF_lt_zero,
          ltF_one_false f (psi k a) hs (by intro hc; exact Term.noConfusion hc)] at h
      simp at h
    | Z a =>
      rw [show ltF (f+1) (Z a) omega
            = ((Z a == zero) || (Z a == one) || ltF f (Z a) zero || ltF f (Z a) one) from rfl,
          show ((Z a == zero) : Bool) = false from rfl,
          show ((Z a == one) : Bool) = false from rfl,
          ltF_lt_zero,
          ltF_one_false f (Z a) hs (by intro hc; exact Term.noConfusion hc)] at h
      simp at h
    | add a b =>
      obtain ⟨hap, ha, hb⟩ := inT_add hs
      have h' : ltF f a omega = true := h
      obtain ⟨k, hk⟩ := below_omega f a ha h'
      subst hk
      have hone : (ofNat k) = one := by
        match k with
        | 0 => exact absurd hap (by decide)
        | 1 => rfl
        | (m + 2) => rw [ofNat_shape m] at hap; exact absurd hap (by simp [isAP])
      have hhead : le ((toList b).headD zero) (ofNat k) = true := inT_add_head_le hs
      rw [hone] at hhead
      obtain ⟨j, hj⟩ := tail_ofNat b hb (inT_add_ne_zero hs) hhead
      exact ⟨j + 2, by rw [hone, hj, ofNat_shape j]⟩
    | phi a b =>
      obtain ⟨ha, hb⟩ := inT_phi hs
      have hpne : phi a b ≠ zero := by intro hc; exact Term.noConfusion hc
      cases hxo : ((phi a b) == omega) with
      | true =>
        have heq : phi a b = omega := by simpa using hxo
        rw [heq, ltF_irrefl] at h
        exact Bool.noConfusion h
      | false =>
        have h2 : (if (a == zero) = true then ltF f b one
                   else if ltF f a zero = true then ltF f b (phi zero one)
                   else ((phi a b == one) || ltF f (phi a b) one)) = true := by
          rw [show ltF (f+1) (phi a b) omega
                = (if ((phi a b) == omega) = true then false
                   else if (a == zero) = true then ltF f b one
                   else if ltF f a zero = true then ltF f b (phi zero one)
                   else ((phi a b == one) || ltF f (phi a b) one) : Bool) from rfl,
              hxo] at h
          simpa using h
        cases haz : (a == zero) with
        | true =>
          rw [haz] at h2
          simp only [if_true] at h2
          have haz' : a = zero := by simpa using haz
          exact ⟨1, by rw [haz', eq_zero_of_ltF_one hb h2]; rfl⟩
        | false =>
          rw [haz] at h2
          simp only [Bool.false_eq_true, if_false, ltF_lt_zero,
            ltF_one_false f (phi a b) hs hpne, Bool.or_false] at h2
          exact ⟨1, by simpa using h2⟩

/-- The cofinality clause for ω, in the form the `lim` constructor consumes. -/
private theorem cofinal_omega (s : Term) (hs : inT s = true) (h : lt s omega = true) :
    ∃ n, le s (ofNat (n + 1)) = true := by
  obtain ⟨k, hk⟩ := below_omega _ s hs h
  cases k with
  | zero => exact ⟨0, by rw [hk]; rfl⟩
  | succ j => exact ⟨j, by rw [hk]; simp [TM.Term.le]⟩

private theorem flatten_const : ∀ (m : Nat) (c : BMS.Col),
    ((List.range m).map (fun _ => ([c] : Matrix))).flatten = List.replicate m c
  | 0, _ => rfl
  | m + 1, c => by
    rw [List.range_succ, List.map_append, List.flatten_append, flatten_const m c,
      List.replicate_succ']
    rfl

/-- The BM4 expansion of `(0)(1)`: all ascension amounts vanish, so the rule is
    "copy the bad part `n+1` times" and the result is `(0)…(0)` with `n+1`
    columns. -/
private theorem expand_omega (n : Nat) : BMS.expand ([[0], [1]] : Matrix) n = zeros (n + 1) := by
  rw [show BMS.expand ([[0], [1]] : Matrix) n
        = ((List.range (n+1)).map (fun _ => ([[0]] : Matrix))).flatten from rfl]
  exact flatten_const (n + 1) [0]

/-- **The first limit certificate.**  `(0)(1)` has value ω. -/
theorem cert_omega : Certified [[0], [1]] omega :=
  .lim (fun n => ofNat (n + 1)) rfl
    (fun n => by rw [expand_omega n]; exact cert_zeros (n + 1))
    (fun n => lt_ofNat_omega (n + 1))
    (fun n => lt_ofNat_succ (n + 1))
    cofinal_omega

/-! ## §4 ω·2 — a limit whose expansions are again limits

`(0)(1)(0)(1)[n] = (0)(1)(0)…(0)`, so the expansion values are `ω + (n+1)`.  Each
of them is a successor chain that terminates at `cert_omega`, so the derivation
tree of `cert_omega2` contains the whole expansion closure of ω·2 — including
the limit node ω sitting under every branch. -/

/-- `ω + k`, as a formal sum. -/
def wp (k : Nat) : Term := ofList (omega :: List.replicate k one)

private theorem wp_shape : ∀ k, wp (k + 1) = add omega (ofNat (k + 1)) := by
  intro k
  rw [ofNat_rep (k+1)]
  show ofList (omega :: List.replicate (k+1) one) = add omega (ofList (List.replicate (k+1) one))
  rw [List.replicate_succ]
  rfl

private theorem toList_wp (k : Nat) : toList (wp k) = omega :: List.replicate k one := by
  refine toList_ofList (fun x hx => ?_)
  rcases List.mem_cons.mp hx with h | h
  · rw [h]; rfl
  · rw [List.eq_of_mem_replicate h]; rfl

/-- The successor step on the ω-block: `(ω + k) + 1 = ω + (k+1)`. -/
private theorem plus_wp_one (k : Nat) : plus (wp k) one = wp (k + 1) := by
  unfold plus
  rw [show toList (one : Term) = [one] from rfl]
  show ofList ((toList (wp k)).filter (fun a => le one a) ++ [one]) = wp (k+1)
  rw [toList_wp k]
  show ofList ((omega :: List.replicate k one).filter (fun a => le one a) ++ [one]) = _
  rw [List.filter_cons_of_pos (show le one omega = true from rfl), filter_le_one k,
    List.cons_append, ← List.replicate_succ']
  rfl

/-- The matrix `(0)(1)(0)…(0)` with `k` trailing zero columns. -/
def omp (k : Nat) : Matrix := [[0], [1]] ++ zeros k

private theorem omp_succ (k : Nat) : omp (k + 1) = omp k ++ [[0]] := by
  show [[0], [1]] ++ List.replicate (k+1) [0] = ([[0], [1]] ++ List.replicate k [0]) ++ [[0]]
  rw [List.replicate_succ', ← List.append_assoc]

private theorem kind_omp (k : Nat) : BMS.kind (omp (k + 1)) = .succ := by
  show (match (omp (k+1)).getLast? with
        | none => BMS.Kind.zero
        | some L => match BMS.lnz L with
          | none => BMS.Kind.succ
          | some _ => BMS.Kind.lim) = _
  rw [omp_succ k, List.getLast?_concat]
  rfl

private theorem expand_omp (k n : Nat) : BMS.expand (omp (k + 1)) n = omp k := by
  have hL : (omp (k+1)).getLast? = some [0] := by rw [omp_succ k]; exact List.getLast?_concat
  have hexp : BMS.expand? (omp (k+1)) n = some ((omp (k+1)).dropLast) := by
    simp only [BMS.expand?, hL, Option.bind_eq_bind, Option.bind_some,
      show BMS.lnz ([0] : BMS.Col) = none from rfl, Option.pure_def]
  show (BMS.expand? (omp (k+1)) n).getD [] = _
  rw [hexp]
  show (omp (k+1)).dropLast = omp k
  rw [omp_succ k]
  exact List.dropLast_concat

/-- The ω-block family: `(0)(1)(0)…(0)` with `k` zeros has value `ω + k`. -/
theorem cert_wp : ∀ k, Certified (omp k) (wp k)
  | 0 => cert_omega
  | k + 1 => by
    rw [← plus_wp_one k]
    exact .succ (kind_omp k) (fun n => by rw [expand_omp k n]; exact cert_wp k)

/-! ### The order facts for the ω-block -/

private theorem ltF_add_same {f : Nat} {a x y : Term} (h : ltF f x y = true) :
    ltF (f + 1) (add a x) (add a y) = true := by
  have hne : (add a x == add a y) = false := by simp [ne_of_ltF h]
  show (if (add a x == add a y) = true then false else _) = true
  rw [hne]
  simp only [Bool.false_eq_true, if_false]
  show (if (a == a) = true then ltF f x y else _) = true
  simp [h]

private theorem lt_add_same_of {a x y : Term} {N : Nat} (h : ∀ f, N ≤ f → ltF f x y = true)
    (hN : N + 1 ≤ 2 * ((add a x).deg + (add a y).deg) + 8) :
    lt (add a x) (add a y) = true := by
  refine lt_of_ltF (N := N + 1) (fun f hf => ?_) hN
  cases f with
  | zero => omega
  | succ g => exact ltF_add_same (h g (by omega))

private theorem lt_wp_omega2 (n : Nat) : lt (wp (n + 1)) (add omega omega) = true := by
  rw [wp_shape n]
  refine lt_add_same_of (N := 3) (fun f hf => ltF_ofNat_omega (n+1) f hf) ?_
  show 3 + 1 ≤ 2 * ((add omega (ofNat (n+1))).deg + (add omega omega).deg) + 8
  omega

private theorem lt_wp_succ (n : Nat) : lt (wp (n + 1)) (wp (n + 2)) = true := by
  rw [wp_shape n, wp_shape (n+1)]
  refine lt_add_same_of (N := n + 3) (fun f hf => ltF_ofNat_succ (n+1) f hf) ?_
  have h1 := deg_ofNat (n+1)
  show n + 3 + 1 ≤ 2 * ((1 + (omega : Term).deg + (ofNat (n+1)).deg)
    + (1 + (omega : Term).deg + (ofNat (n+2)).deg)) + 8
  show n + 3 + 1 ≤ 2 * ((1 + 5 + (ofNat (n+1)).deg) + (1 + 5 + (ofNat (n+2)).deg)) + 8
  omega

private theorem wp_ne_zero (m : Nat) : wp (m + 1) ≠ zero := by
  rw [wp_shape m]; intro hc; exact Term.noConfusion hc

private theorem ltF_ofNat_wp : ∀ (k m f : Nat), 4 ≤ f → ltF f (ofNat k) (wp (m + 1)) = true
  | 0, m, f, hf => ltF_zero (by omega) (wp_ne_zero m)
  | 1, m, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      rw [wp_shape m]
      show (((one : Term) == omega) || ltF g one omega) = true
      simp only [show (((one : Term)) == omega) = false from rfl, Bool.false_or]
      exact ltF_one_omega g (by omega)
  | k + 2, m, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      rw [ofNat_shape k, wp_shape m]
      show (if ((one : Term) == omega) = true then ltF g (ofNat (k+1)) (ofNat (m+1))
            else ltF g one omega) = true
      simp only [show (((one : Term)) == omega) = false from rfl, Bool.false_eq_true, if_false]
      exact ltF_one_omega g (by omega)

private theorem le_ofNat_wp (k m : Nat) : le (ofNat k) (wp (m + 1)) = true := by
  have h : lt (ofNat k) (wp (m+1)) = true :=
    lt_of_ltF (N := 4) (fun f hf => ltF_ofNat_wp k m f hf) (by omega)
  simp [TM.Term.le, h]

/-- **L1 for ω·2.**  Every term of 𝔗(M) below ω·2 is a natural number or `ω + k`. -/
theorem below_omega2 : ∀ (f : Nat) (s : Term), inT s = true →
    ltF f s (add omega omega) = true → (∃ k, s = ofNat k) ∨ (∃ k, s = wp k)
  | 0, s, _, h => by
    exact absurd h (by rw [show ltF 0 s (add omega omega) = false from rfl]; simp)
  | f + 1, s, hs, h => by
    -- the head-only clause 2.3.11 for a non-sum `x`, shared by five constructors
    have key : ∀ (x : Term), inT x = true → ((x == omega) || ltF f x omega) = true →
        (∃ k, x = ofNat k) ∨ (∃ k, x = wp k) := by
      intro x hx hh
      cases hxo : (x == omega) with
      | true => exact Or.inr ⟨0, by simpa using hxo⟩
      | false =>
        rw [hxo] at hh
        simp only [Bool.false_or] at hh
        exact Or.inl (below_omega f x hx hh)
    cases s with
    | zero => exact Or.inl ⟨0, rfl⟩
    | M => exact key M hs h
    | omg a => exact key (omg a) hs h
    | phi a b => exact key (phi a b) hs h
    | psi k a => exact key (psi k a) hs h
    | Z a => exact key (Z a) hs h
    | add a b =>
      obtain ⟨hap, ha, hb⟩ := inT_add hs
      cases hxo : ((add a b) == add omega omega) with
      | true =>
        have heq : add a b = add omega omega := by simpa using hxo
        rw [heq, ltF_irrefl] at h
        exact Bool.noConfusion h
      | false =>
        have h2 : (if (a == omega) = true then ltF f b omega else ltF f a omega) = true := by
          rw [show ltF (f+1) (add a b) (add omega omega)
                = (if ((add a b) == add omega omega) = true then false
                   else if (a == omega) = true then ltF f b omega
                   else ltF f a omega : Bool) from rfl, hxo] at h
          simpa using h
        cases haz : (a == omega) with
        | true =>
          rw [haz] at h2
          simp only [if_true] at h2
          have haz' : a = omega := by simpa using haz
          obtain ⟨j, hj⟩ := below_omega f b hb h2
          cases j with
          | zero => exact absurd hj (by rw [show (ofNat 0 : Term) = zero from rfl];
                                        exact inT_add_ne_zero hs)
          | succ j' => exact Or.inr ⟨j' + 1, by rw [haz', hj, wp_shape j']⟩
        | false =>
          rw [haz] at h2
          simp only [Bool.false_eq_true, if_false] at h2
          obtain ⟨k, hk⟩ := below_omega f a ha h2
          subst hk
          have hone : (ofNat k) = one := by
            match k with
            | 0 => exact absurd hap (by decide)
            | 1 => rfl
            | (m + 2) => rw [ofNat_shape m] at hap; exact absurd hap (by simp [isAP])
          have hhead : le ((toList b).headD zero) (ofNat k) = true := inT_add_head_le hs
          rw [hone] at hhead
          obtain ⟨j, hj⟩ := tail_ofNat b hb (inT_add_ne_zero hs) hhead
          exact Or.inl ⟨j + 2, by rw [hone, hj, ofNat_shape j]⟩

private theorem cofinal_omega2 (s : Term) (hs : inT s = true) (h : lt s (add omega omega) = true) :
    ∃ n, le s (wp (n + 1)) = true := by
  rcases below_omega2 _ s hs h with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨0, by rw [hk]; exact le_ofNat_wp k 0⟩
  · cases k with
    | zero => exact ⟨0, by rw [hk]; rfl⟩
    | succ j => exact ⟨j, by rw [hk]; simp [TM.Term.le]⟩

private theorem expand_omega2 (n : Nat) :
    BMS.expand ([[0], [1], [0], [1]] : Matrix) n = omp (n + 1) := by
  rw [show BMS.expand ([[0], [1], [0], [1]] : Matrix) n
        = [[0], [1]] ++ ((List.range (n+1)).map (fun _ => ([[0]] : Matrix))).flatten from rfl,
    flatten_const]
  rfl

/-- `(0)(1)(0)(1)` has value ω·2. -/
theorem cert_omega2 : Certified [[0], [1], [0], [1]] (add omega omega) :=
  .lim (fun n => wp (n + 1)) rfl
    (fun n => by rw [expand_omega2 n]; exact cert_wp (n + 1))
    lt_wp_omega2
    lt_wp_succ
    cofinal_omega2

/-! ## §5 ω² — the ω-block family and the first exponent step

`ω²[n] = ω·(n+1)` and `(ω·(m+1))[n] = ω·m + (n+1)`, so the whole region below ω²
is one family `cert_wm m k : Certified (wmM m k) (wm m k)` for the value `ω·m+k`,
proved by recursion on `m` with an inner recursion on `k`; ω² is the limit over
it.  §4's `wp`/`omp` are the case `m = 1`. -/

/-! ### Lexicographic comparison of formal sums

Two general clauses of [Rathjen, 1991] 2.3 do all the work below: a sum is compared with a
non-sum by its head (2.3.10/2.3.11), and two sums are compared componentwise
(2.3.16).  `x.isAP` is needed exactly where a one-component sum `ofList [x]`
collapses to `x`. -/

private theorem ofList_cons {a : Term} : ∀ {l : List Term}, l ≠ [] →
    ofList (a :: l) = add a (ofList l)
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

private theorem ltF_to_add {f : Nat} {x c d : Term} (hx : x.isAP = true)
    (h : ((x == c) || ltF f x c) = true) : ltF (f + 1) x (add c d) = true := by
  cases x with
  | zero => simp [isAP] at hx
  | add _ _ => simp [isAP] at hx
  | M => exact h
  | omg _ => exact h
  | phi _ _ => exact h
  | psi _ _ => exact h
  | Z _ => exact h

private theorem ltF_add_to {f : Nat} {a b y : Term} (hy : y.isAP = true)
    (h : ltF f a y = true) : ltF (f + 1) (add a b) y = true := by
  cases y with
  | zero => simp [isAP] at hy
  | add _ _ => simp [isAP] at hy
  | M => exact h
  | omg _ => exact h
  | phi _ _ => exact h
  | psi _ _ => exact h
  | Z _ => exact h

/-- Two sums that first differ at one component: the component decides. -/
private theorem ltF_ofList_head : ∀ (p : List Term) (x y : Term) (r r' : List Term) (N : Nat),
    x.isAP = true → y.isAP = true → (∀ g, N ≤ g → ltF g x y = true) →
    ∀ f, p.length + N + 1 ≤ f → ltF f (ofList (p ++ x :: r)) (ofList (p ++ y :: r')) = true
  | [], x, y, r, r', N, hx, hy, hxy, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      have hg : ltF g x y = true := hxy g (by simp at hf; omega)
      cases r with
      | nil =>
        cases r' with
        | nil => exact hxy (g+1) (by simp at hf; omega)
        | cons z r'' =>
          show ltF (g+1) x (add y (ofList (z :: r''))) = true
          exact ltF_to_add hx (by rw [hg]; simp)
      | cons w r'' =>
        cases r' with
        | nil =>
          show ltF (g+1) (add x (ofList (w :: r''))) y = true
          exact ltF_add_to hy hg
        | cons z r''' =>
          have hne : x ≠ y := ne_of_ltF hg
          have hne2 : (add x (ofList (w :: r'')) == add y (ofList (z :: r'''))) = false := by
            simp [hne]
          show (if (add x (ofList (w :: r'')) == add y (ofList (z :: r'''))) = true then false
                else if (x == y) = true then ltF g (ofList (w :: r'')) (ofList (z :: r'''))
                else ltF g x y) = true
          rw [hne2, show (x == y) = false from by simp [hne]]
          simpa using hg
  | a :: p', x, y, r, r', N, hx, hy, hxy, f, hf => by
    cases f with
    | zero => simp at hf
    | succ g =>
      rw [List.cons_append, ofList_cons (by simp), List.cons_append, ofList_cons (by simp)]
      refine ltF_add_same (ltF_ofList_head p' x y r r' N hx hy hxy g ?_)
      simp only [List.length_cons] at hf
      omega

/-- A sum is below any of its proper extensions (the shorter prefix is smaller). -/
private theorem ltF_ofList_prefix : ∀ (p : List Term) (y : Term) (r' : List Term),
    p ≠ [] → (∀ z ∈ p, z.isAP = true) →
    ∀ f, p.length + 1 ≤ f → ltF f (ofList p) (ofList (p ++ y :: r')) = true
  | [], _, _, h, _, _, _ => absurd rfl h
  | [a], y, r', _, hap, f, hf => by
    cases f with
    | zero => simp at hf
    | succ g =>
      show ltF (g+1) a (add a (ofList (y :: r'))) = true
      exact ltF_to_add (hap a (by simp)) (by simp)
  | a :: b :: p', y, r', _, hap, f, hf => by
    cases f with
    | zero => simp at hf
    | succ g =>
      show ltF (g+1) (add a (ofList (b :: p')))
        (add a (ofList (b :: (p' ++ y :: r')))) = true
      refine ltF_add_same (ltF_ofList_prefix (b :: p') y r' (by simp)
        (fun z hz => hap z (List.mem_cons_of_mem a hz)) g ?_)
      simp only [List.length_cons] at hf ⊢
      omega

/-! ### The terms `ω·m + k` -/

/-- `ω·m + k`. -/
def wm (m k : Nat) : Term := ofList (List.replicate m omega ++ List.replicate k one)

private theorem wm_isAP (m k : Nat) : ∀ z ∈ List.replicate m omega ++ List.replicate k one,
    z.isAP = true := by
  intro z hz
  rcases List.mem_append.mp hz with h | h
  · rw [List.eq_of_mem_replicate h]; rfl
  · rw [List.eq_of_mem_replicate h]; rfl

private theorem wm_zero_k (k : Nat) : wm 0 k = ofNat k := by
  show ofList ([] ++ List.replicate k one) = _
  rw [List.nil_append, ← ofNat_rep]

private theorem wm_one_zero : wm 1 0 = omega := rfl

private theorem wm_cons (m k : Nat) (h : m + k ≠ 0) : wm (m + 1) k = add omega (wm m k) := by
  show ofList (List.replicate (m+1) omega ++ List.replicate k one) = _
  rw [List.replicate_succ, List.cons_append]
  refine ofList_cons ?_
  cases m with
  | zero =>
    cases k with
    | zero => omega
    | succ j => simp [List.replicate_succ]
  | succ i => simp [List.replicate_succ]

private theorem wm_ne_zero (m k : Nat) (h : m + k ≠ 0) : wm m k ≠ zero := by
  cases m with
  | zero =>
    cases k with
    | zero => omega
    | succ j => rw [wm_zero_k]; exact ofNat_ne_zero j
  | succ i =>
    cases i with
    | zero =>
      cases k with
      | zero => rw [wm_one_zero]; intro hc; exact Term.noConfusion hc
      | succ j => rw [wm_cons 0 (j+1) (by omega)]; intro hc; exact Term.noConfusion hc
    | succ i' => rw [wm_cons (i'+1) k (by omega)]; intro hc; exact Term.noConfusion hc

private theorem deg_wm : ∀ (i k : Nat), i + k ≤ (wm i k).deg
  | 0, k => by rw [wm_zero_k]; have := deg_ofNat k; omega
  | i + 1, k => by
    cases i with
    | zero =>
      cases k with
      | zero => rw [wm_one_zero]; show (1:Nat) ≤ 5; omega
      | succ j =>
        rw [wm_cons 0 (j+1) (by omega)]
        have := deg_wm 0 (j+1)
        show 0 + 1 + (j+1) ≤ 1 + (omega : Term).deg + (wm 0 (j+1)).deg
        omega
    | succ i' =>
      rw [wm_cons (i'+1) k (by omega)]
      have := deg_wm (i'+1) k
      show i' + 1 + 1 + k ≤ 1 + (omega : Term).deg + (wm (i'+1) k).deg
      omega

/-- Increasing the number of ω-blocks increases the value. -/
private theorem lt_wm_step (i d k l : Nat) : lt (wm i k) (wm (i + d + 1) l) = true := by
  have hsplit : List.replicate (i + d + 1) omega ++ List.replicate l one
      = List.replicate i omega ++ omega :: (List.replicate d omega ++ List.replicate l one) := by
    rw [show i + d + 1 = i + (d + 1) from rfl, ← List.replicate_append_replicate,
      List.replicate_succ,
      List.append_assoc, List.cons_append]
  refine lt_of_ltF (N := i + k + 3) (fun f hf => ?_) ?_
  · cases k with
    | zero =>
      cases i with
      | zero =>
        show ltF f zero (wm (0 + d + 1) l) = true
        exact ltF_zero (by omega) (wm_ne_zero (0 + d + 1) l (by omega))
      | succ i' =>
        show ltF f (ofList (List.replicate (i'+1) omega ++ List.replicate 0 one))
          (ofList (List.replicate (i'+1 + d + 1) omega ++ List.replicate l one)) = true
        rw [hsplit, show (List.replicate (i'+1) omega ++ List.replicate 0 one)
              = List.replicate (i'+1) omega from by simp]
        refine ltF_ofList_prefix (List.replicate (i'+1) omega) omega
          (List.replicate d omega ++ List.replicate l one) (by simp)
          (fun z hz => by rw [List.eq_of_mem_replicate hz]; rfl) f ?_
        rw [List.length_replicate]
        omega
    | succ k' =>
      show ltF f (ofList (List.replicate i omega ++ List.replicate (k'+1) one))
        (ofList (List.replicate (i + d + 1) omega ++ List.replicate l one)) = true
      rw [hsplit, List.replicate_succ]
      refine ltF_ofList_head (List.replicate i omega) one omega (List.replicate k' one)
        (List.replicate d omega ++ List.replicate l one) 2 rfl rfl
        (fun g hg => ltF_one_omega g hg) f ?_
      rw [List.length_replicate]
      omega
  · have := deg_wm i k
    omega

/-- More finite units, same ω-blocks: the value increases. -/
private theorem lt_wm_tail (i k d : Nat) : lt (wm i k) (wm i (k + d + 1)) = true := by
  have hsplit : List.replicate i omega ++ List.replicate (k + d + 1) one
      = (List.replicate i omega ++ List.replicate k one) ++ one :: List.replicate d one := by
    rw [show k + d + 1 = k + (d + 1) from rfl, ← List.replicate_append_replicate,
      List.replicate_succ,
      List.append_assoc]
  refine lt_of_ltF (N := i + k + 2) (fun f hf => ?_) ?_
  · cases hik : (i + k) with
    | zero =>
      have hi : i = 0 := by omega
      have hk : k = 0 := by omega
      subst hi; subst hk
      show ltF f zero (wm 0 (0 + d + 1)) = true
      exact ltF_zero (by omega) (wm_ne_zero 0 (0 + d + 1) (by omega))
    | succ _ =>
      show ltF f (ofList (List.replicate i omega ++ List.replicate k one))
        (ofList (List.replicate i omega ++ List.replicate (k + d + 1) one)) = true
      rw [hsplit]
      refine ltF_ofList_prefix (List.replicate i omega ++ List.replicate k one) one
        (List.replicate d one) ?_ (wm_isAP i k) f ?_
      · intro hc
        exact wm_ne_zero i k (by omega) (show ofList _ = zero by rw [hc]; rfl)
      · rw [List.length_append, List.length_replicate, List.length_replicate]
        omega
  · have := deg_wm i k
    omega

/-! ### Classification: the terms of 𝔗(M) below ω·m and below ω²

The same shape as `below_omega`, one exponent level up.  `below_wm` says that a
term below ω·(m+1) is some ω·i + k with i ≤ m; `below_omega_sq` says that a term
below ω² is some ω·m + k at all. -/

private theorem wm_isAP_cases : ∀ (i k : Nat), (wm i k).isAP = true →
    (i = 1 ∧ k = 0) ∨ (i = 0 ∧ k = 1)
  | 0, 0, h => absurd h (by decide)
  | 0, 1, _ => Or.inr ⟨rfl, rfl⟩
  | 0, k + 2, h => by rw [wm_zero_k, ofNat_shape k] at h; exact absurd h (by simp [isAP])
  | 1, 0, _ => Or.inl ⟨rfl, rfl⟩
  | 1, k + 1, h => by rw [wm_cons 0 (k+1) (by omega)] at h; exact absurd h (by simp [isAP])
  | i + 2, k, h => by rw [wm_cons (i+1) k (by omega)] at h; exact absurd h (by simp [isAP])

private theorem ofNat_isAP_one {j : Nat} (hap : (ofNat j).isAP = true) : ofNat j = one := by
  match j with
  | 0 => exact absurd hap (by decide)
  | 1 => rfl
  | (m + 2) => rw [ofNat_shape m] at hap; exact absurd hap (by simp [isAP])

private theorem ap_below_omega_le (b : Term) (hb : inT b = true)
    (hle : le b omega = true) : ∃ i k, b = wm i k := by
  cases hco : (b == omega) with
  | true => exact ⟨1, 0, by rw [show b = omega from by simpa using hco, wm_one_zero]⟩
  | false =>
    have hlt : lt b omega = true := by
      simp only [TM.Term.le, hco, Bool.false_or] at hle
      exact hle
    obtain ⟨k, hk⟩ := below_omega _ b hb hlt
    exact ⟨0, k, by rw [hk, wm_zero_k]⟩

/-- A term of 𝔗(M) whose head component is at most ω is an `ω·i + k`. -/
private theorem tail_wm : ∀ (b : Term), inT b = true → b ≠ zero →
    le ((toList b).headD zero) omega = true → ∃ i k, b = wm i k
  | zero, _, hne, _ => absurd rfl hne
  | add c d, h, _, hle => by
    obtain ⟨hap, hc, hd⟩ := inT_add h
    rw [show (toList (add c d)).headD zero = c from rfl] at hle
    have hdne : d ≠ zero := inT_add_ne_zero h
    have hdhead : le ((toList d).headD zero) c = true := inT_add_head_le h
    cases hco : (c == omega) with
    | true =>
      have hc1 : c = omega := by simpa using hco
      rw [hc1] at hdhead
      obtain ⟨i, k, hik⟩ := tail_wm d hd hdne hdhead
      have hik0 : i + k ≠ 0 := by
        intro hz
        exact hdne (by rw [hik, show i = 0 from by omega, show k = 0 from by omega]; rfl)
      exact ⟨i + 1, k, by rw [hc1, hik, wm_cons i k hik0]⟩
    | false =>
      have hlt : lt c omega = true := by
        simp only [TM.Term.le, hco, Bool.false_or] at hle
        exact hle
      obtain ⟨j, hj⟩ := below_omega _ c hc hlt
      have hc1 : c = one := by rw [hj]; exact ofNat_isAP_one (by rw [← hj]; exact hap)
      rw [hc1] at hdhead
      obtain ⟨t, ht⟩ := tail_ofNat d hd hdne hdhead
      exact ⟨0, t + 2, by rw [hc1, ht, wm_zero_k, ofNat_shape t]⟩
  | M, h, _, hle => ap_below_omega_le M h hle
  | omg a, h, _, hle => ap_below_omega_le (omg a) h hle
  | phi a b, h, _, hle => ap_below_omega_le (phi a b) h hle
  | psi a b, h, _, hle => ap_below_omega_le (psi a b) h hle
  | Z a, h, _, hle => ap_below_omega_le (Z a) h hle

/-- **L1 for ω·(m+1).** -/
theorem below_wm : ∀ (f : Nat) (m : Nat) (s : Term), inT s = true →
    ltF f s (wm (m + 1) 0) = true → ∃ i k, i ≤ m ∧ s = wm i k
  | 0, m, s, _, h => by
    exact absurd h (by rw [show ltF 0 s (wm (m+1) 0) = false from rfl]; simp)
  | f + 1, 0, s, hs, h => by
    rw [wm_one_zero] at h
    obtain ⟨k, hk⟩ := below_omega (f+1) s hs h
    exact ⟨0, k, by omega, by rw [hk, wm_zero_k]⟩
  | f + 1, m + 1, s, hs, h => by
    rw [wm_cons (m+1) 0 (by omega)] at h
    have key : ∀ (x : Term), inT x = true → ((x == omega) || ltF f x omega) = true →
        ∃ i k, i ≤ m + 1 ∧ x = wm i k := by
      intro x hx hh
      cases hxo : (x == omega) with
      | true => exact ⟨1, 0, by omega, by rw [show x = omega from by simpa using hxo, wm_one_zero]⟩
      | false =>
        rw [hxo] at hh
        simp only [Bool.false_or] at hh
        obtain ⟨k, hk⟩ := below_omega f x hx hh
        exact ⟨0, k, by omega, by rw [hk, wm_zero_k]⟩
    cases s with
    | zero => exact ⟨0, 0, by omega, rfl⟩
    | M => exact key M hs h
    | omg a => exact key (omg a) hs h
    | phi a b => exact key (phi a b) hs h
    | psi k a => exact key (psi k a) hs h
    | Z a => exact key (Z a) hs h
    | add a b =>
      obtain ⟨hap, ha, hb⟩ := inT_add hs
      cases hxo : ((add a b) == add omega (wm (m+1) 0)) with
      | true =>
        have heq : add a b = add omega (wm (m+1) 0) := by simpa using hxo
        rw [heq, ltF_irrefl] at h
        exact Bool.noConfusion h
      | false =>
        have h2 : (if (a == omega) = true then ltF f b (wm (m+1) 0)
                   else ltF f a omega) = true := by
          rw [show ltF (f+1) (add a b) (add omega (wm (m+1) 0))
                = (if ((add a b) == add omega (wm (m+1) 0)) = true then false
                   else if (a == omega) = true then ltF f b (wm (m+1) 0)
                   else ltF f a omega : Bool) from rfl, hxo] at h
          simpa using h
        cases haz : (a == omega) with
        | true =>
          rw [haz] at h2
          simp only [if_true] at h2
          have haz' : a = omega := by simpa using haz
          obtain ⟨i, k, hi, hik⟩ := below_wm f m b hb h2
          have hik0 : i + k ≠ 0 := by
            intro hz
            exact inT_add_ne_zero hs
              (by rw [hik, show i = 0 from by omega, show k = 0 from by omega]; rfl)
          exact ⟨i + 1, k, by omega, by rw [haz', hik, wm_cons i k hik0]⟩
        | false =>
          rw [haz] at h2
          simp only [Bool.false_eq_true, if_false] at h2
          obtain ⟨j, hj⟩ := below_omega f a ha h2
          have hone : a = one := by rw [hj]; exact ofNat_isAP_one (by rw [← hj]; exact hap)
          have hhead : le ((toList b).headD zero) a = true := inT_add_head_le hs
          rw [hone] at hhead
          obtain ⟨t, ht⟩ := tail_ofNat b hb (inT_add_ne_zero hs) hhead
          exact ⟨0, t + 2, by omega, by rw [hone, ht, wm_zero_k, ofNat_shape t]⟩

private theorem below_two : ∀ (f : Nat) (b : Term), inT b = true →
    ltF f b (ofNat 2) = true → b = zero ∨ b = one
  | 0, b, _, h => by exact absurd h (by rw [show ltF 0 b (ofNat 2) = false from rfl]; simp)
  | f + 1, b, hb, h => by
    have key : ∀ (x : Term), inT x = true → ((x == one) || ltF f x one) = true →
        x = zero ∨ x = one := by
      intro x hx hh
      cases hxo : (x == one) with
      | true => exact Or.inr (by simpa using hxo)
      | false =>
        rw [hxo] at hh
        simp only [Bool.false_or] at hh
        exact Or.inl (eq_zero_of_ltF_one hx hh)
    cases b with
    | zero => exact Or.inl rfl
    | M => exact key M hb h
    | omg a => exact key (omg a) hb h
    | phi a c => exact key (phi a c) hb h
    | psi a c => exact key (psi a c) hb h
    | Z a => exact key (Z a) hb h
    | add x y =>
      obtain ⟨hap, hx, hy⟩ := inT_add hb
      cases hxo : ((add x y) == ofNat 2) with
      | true =>
        have heq : add x y = ofNat 2 := by simpa using hxo
        rw [heq, ltF_irrefl] at h
        exact Bool.noConfusion h
      | false =>
        have h2 : (if (x == one) = true then ltF f y one else ltF f x one) = true := by
          rw [show ltF (f+1) (add x y) (ofNat 2)
                = (if ((add x y) == ofNat 2) = true then false
                   else if (x == one) = true then ltF f y one
                   else ltF f x one : Bool) from rfl, hxo] at h
          simpa using h
        cases hx1 : (x == one) with
        | true =>
          rw [hx1] at h2
          simp only [if_true] at h2
          exact absurd (eq_zero_of_ltF_one hy h2) (inT_add_ne_zero hb)
        | false =>
          rw [hx1] at h2
          simp only [Bool.false_eq_true, if_false] at h2
          exact absurd (eq_zero_of_ltF_one hx h2) (isAP_ne_zero hap)

/-- **L1 for ω².**  Every term of 𝔗(M) below ω² is some `ω·m + k`. -/
theorem below_omega_sq : ∀ (f : Nat) (s : Term), inT s = true →
    ltF f s (phi zero (ofNat 2)) = true → ∃ m k, s = wm m k
  | 0, s, _, h => by
    exact absurd h (by rw [show ltF 0 s (phi zero (ofNat 2)) = false from rfl]; simp)
  | f + 1, s, hs, h => by
    cases s with
    | zero => exact ⟨0, 0, rfl⟩
    | M =>
      rw [Evidence.StageA.ltF_M_phi] at h
      exact Bool.noConfusion h
    | omg a =>
      rw [show ltF (f+1) (omg a) (phi zero (ofNat 2)) = false from rfl] at h
      exact Bool.noConfusion h
    | psi k a =>
      have h2 : ((psi k a == zero) || (psi k a == ofNat 2) || ltF f (psi k a) zero
                 || ltF f (psi k a) (ofNat 2)) = true := h
      rw [show ((psi k a == zero) : Bool) = false from rfl,
        show ((psi k a == ofNat 2) : Bool) = false from rfl, ltF_lt_zero] at h2
      simp only [Bool.or_false, Bool.false_or] at h2
      rcases below_two f (psi k a) hs h2 with hc | hc <;>
        exact absurd hc (by intro hh; exact Term.noConfusion hh)
    | Z a =>
      have h2 : ((Z a == zero) || (Z a == ofNat 2) || ltF f (Z a) zero
                 || ltF f (Z a) (ofNat 2)) = true := h
      rw [show ((Z a == zero) : Bool) = false from rfl,
        show ((Z a == ofNat 2) : Bool) = false from rfl, ltF_lt_zero] at h2
      simp only [Bool.or_false, Bool.false_or] at h2
      rcases below_two f (Z a) hs h2 with hc | hc <;>
        exact absurd hc (by intro hh; exact Term.noConfusion hh)
    | phi a b =>
      obtain ⟨ha, hb⟩ := inT_phi hs
      cases hxo : ((phi a b) == phi zero (ofNat 2)) with
      | true =>
        have heq : phi a b = phi zero (ofNat 2) := by simpa using hxo
        rw [heq, ltF_irrefl] at h
        exact Bool.noConfusion h
      | false =>
        have h2 : (if (a == zero) = true then ltF f b (ofNat 2)
                   else if ltF f a zero = true then ltF f b (phi zero (ofNat 2))
                   else ((phi a b == ofNat 2) || ltF f (phi a b) (ofNat 2))) = true := by
          rw [show ltF (f+1) (phi a b) (phi zero (ofNat 2))
                = (if ((phi a b) == phi zero (ofNat 2)) = true then false
                   else if (a == zero) = true then ltF f b (ofNat 2)
                   else if ltF f a zero = true then ltF f b (phi zero (ofNat 2))
                   else ((phi a b == ofNat 2) || ltF f (phi a b) (ofNat 2)) : Bool) from rfl,
              hxo] at h
          simpa using h
        cases haz : (a == zero) with
        | true =>
          rw [haz] at h2
          simp only [if_true] at h2
          have haz' : a = zero := by simpa using haz
          rcases below_two f b hb h2 with hbz | hbo
          · exact ⟨0, 1, by rw [haz', hbz]; rfl⟩
          · exact ⟨1, 0, by rw [haz', hbo]; rfl⟩
        | false =>
          rw [haz] at h2
          simp only [Bool.false_eq_true, if_false, ltF_lt_zero,
            show ((phi a b == ofNat 2) : Bool) = false from rfl, Bool.false_or] at h2
          rcases below_two f (phi a b) hs h2 with hc | hc
          · exact absurd hc (by intro hh; exact Term.noConfusion hh)
          · exact ⟨0, 1, hc⟩
    | add a b =>
      obtain ⟨hap, ha, hb⟩ := inT_add hs
      have h2 : ltF f a (phi zero (ofNat 2)) = true := h
      obtain ⟨i, k, hik⟩ := below_omega_sq f a ha h2
      subst hik
      have hhead : le ((toList b).headD zero) (wm i k) = true := inT_add_head_le hs
      rcases wm_isAP_cases i k hap with ⟨hi, hk⟩ | ⟨hi, hk⟩
      · subst hi; subst hk
        rw [wm_one_zero] at hhead
        obtain ⟨i', k', hik'⟩ := tail_wm b hb (inT_add_ne_zero hs) hhead
        have hik0 : i' + k' ≠ 0 := by
          intro hz
          exact inT_add_ne_zero hs
            (by rw [hik', show i' = 0 from by omega, show k' = 0 from by omega]; rfl)
        exact ⟨i' + 1, k', by rw [wm_one_zero, hik', wm_cons i' k' hik0]⟩
      · subst hi; subst hk
        rw [show wm 0 1 = one from rfl] at hhead
        obtain ⟨t, ht⟩ := tail_ofNat b hb (inT_add_ne_zero hs) hhead
        exact ⟨0, t + 2, by rw [show wm 0 1 = one from rfl, ht, wm_zero_k, ofNat_shape t]⟩

/-! ### The successor step and the matrices -/

private theorem filter_le_one_omega : ∀ m,
    (List.replicate m omega).filter (fun a => le one a) = List.replicate m omega
  | 0 => rfl
  | m + 1 => by
    show (omega :: List.replicate m omega).filter _ = _
    rw [List.filter_cons_of_pos (show le one omega = true from rfl), filter_le_one_omega m]
    rfl

private theorem plus_wm_one (m k : Nat) : plus (wm m k) one = wm m (k + 1) := by
  show plus (ofList (List.replicate m omega ++ List.replicate k one)) one = _
  unfold plus
  rw [show toList (one : Term) = [one] from rfl]
  show ofList ((toList (ofList (List.replicate m omega ++ List.replicate k one))).filter
      (fun a => le one a) ++ [one]) = wm m (k+1)
  rw [toList_ofList (wm_isAP m k), List.filter_append, filter_le_one_omega m, filter_le_one k,
    List.append_assoc, ← List.replicate_succ']
  rfl

private theorem repL_append (B : List Nat) : ∀ k, StageA.repL B k ++ B = StageA.repL B (k + 1)
  | 0 => by show [] ++ B = B ++ []; simp
  | k + 1 => by
    show (B ++ StageA.repL B k) ++ B = B ++ StageA.repL B (k + 1)
    rw [List.append_assoc, repL_append B k]

private theorem repL_single (a : Nat) : ∀ k, StageA.repL [a] k = List.replicate k a
  | 0 => rfl
  | k + 1 => by
    show [a] ++ StageA.repL [a] k = List.replicate (k+1) a
    rw [repL_single a k]
    rfl

private theorem oneRow_replicate (k : Nat) : StageA.oneRow (List.replicate k 0) = zeros k := by
  show (List.replicate k 0).map (fun a => [a]) = List.replicate k [0]
  rw [List.map_replicate]

/-- The matrix `(0)(1)…(0)(1)(0)…(0)` — `m` copies of the ω-block, `k` trailing zeros. -/
def wmM (m k : Nat) : Matrix := Trans.repM [[0], [1]] m ++ zeros k

private theorem wmM_zero_k (m : Nat) : wmM m 0 = Trans.repM [[0], [1]] m := by
  show Trans.repM [[0], [1]] m ++ List.replicate 0 [0] = _
  rw [List.replicate_zero, List.append_nil]

private theorem wmM_succ (m k : Nat) : wmM m (k + 1) = wmM m k ++ [[0]] := by
  show Trans.repM [[0], [1]] m ++ List.replicate (k+1) [0]
      = (Trans.repM [[0], [1]] m ++ List.replicate k [0]) ++ [[0]]
  rw [List.replicate_succ', ← List.append_assoc]

private theorem kind_wmM_succ (m k : Nat) : BMS.kind (wmM m (k + 1)) = .succ := by
  show (match (wmM m (k+1)).getLast? with
        | none => BMS.Kind.zero
        | some L => match BMS.lnz L with
          | none => BMS.Kind.succ
          | some _ => BMS.Kind.lim) = _
  rw [wmM_succ m k, List.getLast?_concat]
  rfl

private theorem expand_wmM_succ (m k n : Nat) : BMS.expand (wmM m (k + 1)) n = wmM m k := by
  have hL : (wmM m (k+1)).getLast? = some [0] := by
    rw [wmM_succ m k]; exact List.getLast?_concat
  have hexp : BMS.expand? (wmM m (k+1)) n = some ((wmM m (k+1)).dropLast) := by
    simp only [BMS.expand?, hL, Option.bind_eq_bind, Option.bind_some,
      show BMS.lnz ([0] : BMS.Col) = none from rfl, Option.pure_def]
  show (BMS.expand? (wmM m (k+1)) n).getD [] = _
  rw [hexp]
  show (wmM m (k+1)).dropLast = wmM m k
  rw [wmM_succ m k]
  exact List.dropLast_concat

private theorem wmM_lim_eq (m : Nat) :
    wmM (m + 1) 0 = StageA.oneRow ((StageA.repL [0, 1] m ++ [0]) ++ [1]) := by
  rw [wmM_zero_k, List.append_assoc,
    show ([0] ++ [1] : List Nat) = [0, 1] from rfl, repL_append [0, 1] m,
    StageA.oneRow_repL]
  rfl

private theorem kind_wmM_lim (m : Nat) : BMS.kind (wmM (m + 1) 0) = .lim := by
  have hL : (wmM (m+1) 0).getLast? = some [1] := by
    rw [wmM_lim_eq m, StageA.oneRow_append]
    exact List.getLast?_concat
  show (match (wmM (m+1) 0).getLast? with
        | none => BMS.Kind.zero
        | some L => match BMS.lnz L with
          | none => BMS.Kind.succ
          | some _ => BMS.Kind.lim) = _
  rw [hL]
  rfl

/-- `(ω·(m+1))[n] = ω·m + (n+1)`: the BM4 rule copies the last `(0)` block. -/
private theorem expand_wmM_lim (m n : Nat) : BMS.expand (wmM (m + 1) 0) n = wmM m (n + 1) := by
  have hexp := StageA.expand_oneRow (A := StageA.repL [0, 1] m) (B := [0]) (c := 1) (b0 := 0)
    (B' := []) rfl (by omega) (by intro x hx; simp at hx) (by omega) n
  show (BMS.expand? (wmM (m+1) 0) n).getD [] = _
  rw [wmM_lim_eq m, hexp]
  show StageA.oneRow (StageA.repL [0, 1] m ++ StageA.repL [0] (n+1)) = wmM m (n+1)
  rw [repL_single, StageA.oneRow_append, StageA.oneRow_repL, oneRow_replicate]
  rfl

/-! ### The certificate family -/

theorem cert_wm : ∀ (m k : Nat), Certified (wmM m k) (wm m k)
  | 0, k => by
    show Certified (zeros k) (wm 0 k)
    rw [wm_zero_k]
    exact cert_zeros k
  | m + 1, 0 => by
    refine .lim (fun n => wm m (n + 1)) (kind_wmM_lim m)
      (fun n => by rw [expand_wmM_lim m n]; exact cert_wm m (n + 1))
      (fun n => lt_wm_step m 0 (n + 1) 0)
      (fun n => lt_wm_tail m (n + 1) 0)
      (fun s hs h => ?_)
    obtain ⟨i, k, hi, hk⟩ := below_wm _ m s hs h
    rcases Nat.lt_or_ge i m with hlt | hge
    · exact ⟨0, by rw [hk, ← show i + (m - i - 1) + 1 = m from by omega]; simp [TM.Term.le,
        lt_wm_step i (m - i - 1) k 1]⟩
    · have him : i = m := by omega
      subst him
      cases k with
      | zero => exact ⟨0, by rw [hk]; simp [TM.Term.le, lt_wm_tail i 0 0]⟩
      | succ j => exact ⟨j, by rw [hk]; simp [TM.Term.le]⟩
  | m + 1, k + 1 => by
    rw [← plus_wm_one (m+1) k]
    exact .succ (kind_wmM_succ (m+1) k)
      (fun n => by rw [expand_wmM_succ (m+1) k n]; exact cert_wm (m+1) k)
  termination_by m k => (m, k)

/-! ### ω² -/

private theorem ltF_phi_same {f : Nat} {a x y : Term} (h : ltF f x y = true) :
    ltF (f + 1) (phi a x) (phi a y) = true := by
  have hne : (phi a x == phi a y) = false := by simp [ne_of_ltF h]
  show (if (phi a x == phi a y) = true then false else _) = true
  rw [hne]
  simp only [Bool.false_eq_true, if_false]
  show (if (a == a) = true then ltF f x y else _) = true
  simp [h]

private theorem ltF_omega_sq : ∀ f, 4 ≤ f → ltF f omega (phi zero (ofNat 2)) = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g => exact ltF_phi_same (ltF_ofNat_succ 1 g (by omega))

private theorem ltF_wm_omega_sq : ∀ (n f : Nat), n + 5 ≤ f →
    ltF f (wm (n + 1) 0) (phi zero (ofNat 2)) = true
  | 0, f, hf => by rw [wm_one_zero]; exact ltF_omega_sq f (by omega)
  | n + 1, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      rw [wm_cons (n+1) 0 (by omega)]
      exact ltF_add_to rfl (ltF_omega_sq g (by omega))

private theorem lt_wm_omega_sq (n : Nat) : lt (wm (n + 1) 0) (phi zero (ofNat 2)) = true := by
  refine lt_of_ltF (N := n + 5) (fun f hf => ltF_wm_omega_sq n f hf) ?_
  have := deg_wm (n+1) 0
  show n + 5 ≤ 2 * ((wm (n+1) 0).deg + (phi zero (ofNat 2)).deg) + 8
  omega

private theorem expand_omega_sq (n : Nat) :
    BMS.expand ([[0], [1], [1]] : Matrix) n = wmM (n + 1) 0 := by
  have hexp := StageA.expand_oneRow (A := ([] : List Nat)) (B := [0, 1]) (c := 1) (b0 := 0)
    (B' := [1]) rfl (by omega) (by intro x hx; simp at hx; omega) (by omega) n
  show (BMS.expand? ([[0], [1], [1]] : Matrix) n).getD [] = _
  rw [show ([[0], [1], [1]] : Matrix)
        = StageA.oneRow ((([] : List Nat) ++ [0, 1]) ++ [1]) from rfl, hexp]
  show StageA.oneRow (([] : List Nat) ++ StageA.repL [0, 1] (n+1)) = wmM (n+1) 0
  rw [List.nil_append, StageA.oneRow_repL, wmM_zero_k]
  rfl

/-- `(0)(1)(1)` has value ω². -/
theorem cert_omega_sq : Certified [[0], [1], [1]] (phi zero (ofNat 2)) := by
  refine .lim (fun n => wm (n + 1) 0) rfl
    (fun n => by rw [expand_omega_sq n]; exact cert_wm (n + 1) 0)
    lt_wm_omega_sq
    (fun n => lt_wm_step (n + 1) 0 0 0)
    (fun s hs h => ?_)
  obtain ⟨m, k, hk⟩ := below_omega_sq _ s hs h
  exact ⟨m, by rw [hk]; simp [TM.Term.le, lt_wm_step m 0 k 0]⟩

/-! ### The route from here to ω^ω (design note — route (a) is now EXECUTED)

STATUS (2026-08-09, certificate lane gen 2).  Route (a) below is carried out
in §5.7: `cert_pre` is the prefix induction verbatim (outer structural
induction on the level, inner `Nat` induction on the coefficient),
`cert_wv` its closed form, `cert_omega_pow` the row `(0)(1)(2)`.  The
prediction "no new well-foundedness" held: `Evidence/WF.lean`'s `LexLt` is
NOT used.  The prediction "the cost is generalising the region machinery"
also held — `below_pw` / `tail_pw` / `below_pre` / `cof_pre` are that cost,
and they are the bulk of §5.7.

The families above stop at ω².  What blocks the next rows is NOT the same thing
in each case, and the difference decides the roadmap:

  * ω^ω, ω^(ω^ω), … : reachable with NO new well-foundedness.  `cert_wm`'s
    recursion is the lexicographic one on `(m, k)` — the count of ω-blocks, then
    of units.  A term below ω^(k+1) is `ω^k·c + β` with `β < ω^k`, so the same
    recursion at level k is lexicographic on a (k+1)-tuple of counts, which is
    not uniform in k.  The uniform form carries the earlier levels as a PREFIX
    PARAMETER instead:

      A k : ∀ (prefix P whose components are all ≥ ω^k, already certified),
              ∀ β < ω^k, Certified (matrix of P+β) (P+β)

    `A 0` is the hypothesis on P; `A (k+1)` follows from `A k` by ordinary
    induction on the coefficient c, the limit node `P + ω^k·(c+1)` taking its
    expansions from the c-step with the extended prefix `P + ω^k·c`.  So the
    induction is structural in k with an inner `Nat` induction — no `Acc`, no
    multiset ordering.  The cost is generalising the region machinery: the
    classification below ω^k (the `below_*` family), the block encoding
    `ω^j ↦ 0 :: List.replicate j 1`, and prefix-relative expansion lemmas from
    `StageA.expand_oneRow`.  §5's `ltF_ofList_head` / `ltF_ofList_prefix` are
    already stated for arbitrary sums and carry over unchanged.

  * ε₀ : genuinely blocked.  Its expansions are the ω-towers, whose exponents
    are themselves unbounded terms, so no fixed level k bounds the region and
    the prefix induction above has nothing to recurse on.  That case needs
    well-foundedness of the T(M) order on the CNF segment (the classical
    `Acc (ω^a + b)` argument), which in this repo would additionally need
    transitivity of `lt` — not proved anywhere yet.

An earlier report from this lane said ω^ω needed the Hydra/multiset ordering;
that was too pessimistic — only ε₀ needs the well-foundedness stage. -/

/-! ### Scaffolding for the ω^ω stage (definitions + design evidence only)

HAND-OFF NOTE.  Nothing below is proved about certificates; this is the
representation the next lane should build on, together with the computations
that show it is the right one.  Picking the representation wrong is the
expensive mistake in this development (see how much of §4/§5 is shape lemmas),
so it is pinned and machine-checked here before anyone invests in proofs.

A term of the CNF segment below ω^ω is a count vector `cs = [c_k, …, c_0]`,
read as `ω^k·c_k + … + ω^0·c_0`; the level of an entry is the length of what
follows it.  `wv` is its value, `wvM` its matrix, `wvSeq` the one-row sequence
in between.  The `#guard`s below check, by computation:

  * `oPr (wvM cs) = wv cs` — the encoding agrees with the translation;
  * `wv [c₁, c₀] = wm c₁ c₀` — it literally generalises §5's certified family,
    so the ω²-and-below work is the `k ≤ 1` case and nothing is re-done;
  * `expand (0)(1)(2) n = wvM [1,0,…,0]` — the expansions of ω^ω are exactly the
    ω^(n+1) of this family, which is what makes it the right index set.

ALL FIVE ITEMS OF THIS HAND-OFF ARE NOW DISCHARGED IN §5.7 (2026-08-09):

  1. Shape lemmas — as `pwv_cons` / `toList_pwv` / `deg_pwv_len` / `deg_pwv_mem`
     / `plus_pwv_one`, stated on the EXPONENT LIST `expOf cs` rather than on the
     count vector, because every proof decomposes a term as PREFIX ++ REST and
     concatenation is not an operation on count vectors.  `wv_eq` / `wvM_eq`
     bridge the two, so the definitions pinned here stay the interface.
  2. The expansion lemmas — `kind_pwM_succ` / `expand_pwM_succ` and
     `kind_pwM_lim` / `expand_pwM_lim`.  They are prefix-relative for free:
     `StageA.expand_oneRow` puts NO condition on its prefix `A`.
  3. The classification — `below_pw` (recursion on `(level, fuel)`), with its
     companion `tail_pw` for the tail of a sum, and the prefix-relative
     `below_pre` / `cof_pre`.  The prediction that `ltF_ofList_head` /
     `ltF_ofList_prefix` cover every comparison was right; what they do NOT
     cover, and what had to be added, is the analysis of `ofNat`
     (`ltF_ofNat_lt` / `ltF_ofNat_ge` / `below_ofNat`).
  4. `cert_wv : ∀ cs, Certified (wvM cs) (wv cs)` — by the PREFIX route.  The
     vector/`LexLt` route was not needed: the prefix induction has no
     termination obligation at all, and the order work it avoids is nil.
  5. `cert_omega_pow : Certified [[0],[1],[2]] (phi zero omega)`, registered.

COVERED AS OF §5.8–§5.15 (2026-08-09), by a second layer built exactly as
predicted here: the row `(0)(1)(2)(3)`
(ω^(ω^ω)).  Its expansions are
`ω^(ω^(n+1))` — checked: `expand (0)(1)(2)(3) 1 = (0)(1)(2)(2)`, value
`ω^(ω^2)` — whose exponents are themselves ω^k, not naturals, so they are NOT in
this family.  That row needs one more layer, with the exponents drawn from this
one; the construction iterates, and each finite level of nesting is another
instance of the same pattern.  ε₀ is where the iteration itself has to be
internalised, which is the well-foundedness stage. -/

/-- The block of a one-row sequence whose value is `ω^j`. -/
def blockOf (j : Nat) : List Nat := 0 :: List.replicate j 1

/-- The one-row sequence of the count vector `cs = [c_k, …, c_0]`. -/
def wvSeq : List Nat → List Nat
  | [] => []
  | c :: cs => Evidence.StageA.repL (blockOf cs.length) c ++ wvSeq cs

/-- The components of `ω^k·c_k + … + ω^0·c_0`, in descending order. -/
def wvList : List Nat → List Term
  | [] => []
  | c :: cs => List.replicate c (phi zero (ofNat cs.length)) ++ wvList cs

/-- The value of the count vector. -/
def wv (cs : List Nat) : Term := ofList (wvList cs)

/-- The matrix of the count vector. -/
def wvM (cs : List Nat) : Matrix := Evidence.StageA.oneRow (wvSeq cs)

-- the encoding agrees with the translation
#guard Trans.oPr (wvM [1, 0, 0]) == wv [1, 0, 0]
#guard Trans.oPr (wvM [2, 1, 3]) == wv [2, 1, 3]
#guard Trans.oPr (wvM [0, 4, 2]) == wv [0, 4, 2]
#guard Trans.oPr (wvM [1, 0, 0, 0]) == wv [1, 0, 0, 0]
#guard wv [1, 0, 0] == phi zero (ofNat 2)
-- it generalises the certified family of §5 (`k ≤ 1`)
#guard wv [3, 2] == wm 3 2
#guard wv [0, 5] == wm 0 5
-- the expansions of ω^ω are exactly this family
#guard BMS.expand ([[0], [1], [2]] : Matrix) 2 == wvM [1, 0, 0, 0]
#guard Trans.oPr [[0], [1], [2]] == phi zero omega
-- …and the next row up leaves it (its exponents are ω^k, not naturals)
#guard BMS.expand ([[0], [1], [2], [3]] : Matrix) 1 == ([[0], [1], [2], [2]] : Matrix)


/-! ## §5.7 ω^ω — the whole CNF region below ω^ω, certified

The plan of this section, in one line: classify (`below_pw`), compare
(`lt_pwv_repl`, `lt_pwv_step`, `lt_pwv_more`), expand (`expand_pwM_*`), then run
the prefix induction (`cert_pre`).

Two things are worth flagging to a reader who checks this section against §5.

  * NOTHING here propagates an order HYPOTHESIS into an order CONCLUSION.  `lt`
    is `ltF` at one fixed amount of fuel, and when this section was written
    there was no fuel-monotonicity lemma, so `ltF f x y = true` at the fuel the
    caller happens to supply could not be re-used at the fuel the goal happens
    to want.  Every proof therefore CLASSIFIES its term into a canonical `pwv e`
    first and then RE-DERIVES the comparison from scratch with its own fuel
    budget — the same discipline §5 uses (`below_wm` then `lt_wm_step`).
    `Evidence.WF.ltF_mono` (proved afterwards, and now imported) LIFTS this
    restriction: see `pwLt_of_lt` below for the entry point.  The proofs here
    were not rewritten to use it — they are green and mutation-controlled as
    they stand — but a future simplification pass should start there.
  * The cofinality clause is proved ONCE, prefix-relatively (`cof_pre`), for
    every limit node of the family at the same time.  It quantifies over ALL
    `inT` terms, as the doctrine requires; `below_pre` is the analysis that
    makes that quantifier tractable. -/
/-! ### The exponent-list layer

The count vector `cs` is the right *index set* (it is total: every list of counts
names a term), but every proof below decomposes a term as PREFIX ++ REST, and
concatenation is not an operation on count vectors.  So the working
representation is the list of EXPONENTS in descending order, `expOf cs`, and the
count vector is recovered at the very end. -/

/-- ω^k. -/
def pw (k : Nat) : Term := phi zero (ofNat k)

/-- The value of a list of exponents: `ω^{e₁} ⊕ … ⊕ ω^{eᵣ}`. -/
def pwv (e : List Nat) : Term := ofList (e.map pw)

/-- The one-row sequence of a list of exponents. -/
def pwSeq (e : List Nat) : List Nat := (e.map blockOf).flatten

/-- The matrix of a list of exponents. -/
def pwM (e : List Nat) : Matrix := StageA.oneRow (pwSeq e)

/-- The exponents of a count vector, in descending order: the entry `c` at level
    `cs.length` contributes `c` copies of that level. -/
def expOf : List Nat → List Nat
  | [] => []
  | c :: cs => List.replicate c cs.length ++ expOf cs

private theorem repL_flatten (B : List Nat) : ∀ c, StageA.repL B c = (List.replicate c B).flatten
  | 0 => rfl
  | c + 1 => by
    show B ++ StageA.repL B c = _
    rw [repL_flatten B c, List.replicate_succ]
    rfl

private theorem pwSeq_append (e e' : List Nat) : pwSeq (e ++ e') = pwSeq e ++ pwSeq e' := by
  show ((e ++ e').map blockOf).flatten = _
  rw [List.map_append, List.flatten_append]
  rfl

private theorem pwSeq_replicate (j c : Nat) :
    pwSeq (List.replicate c j) = StageA.repL (blockOf j) c := by
  show ((List.replicate c j).map blockOf).flatten = _
  rw [List.map_replicate, repL_flatten]

private theorem pwM_append (e e' : List Nat) :
    pwM (e ++ e') = pwM e ++ StageA.oneRow (pwSeq e') := by
  show StageA.oneRow (pwSeq (e ++ e')) = _
  rw [pwSeq_append, StageA.oneRow_append]
  rfl

/-! ### The bridge to the count vector -/

theorem wvList_eq : ∀ cs, wvList cs = (expOf cs).map pw
  | [] => rfl
  | c :: cs => by
    show List.replicate c (phi zero (ofNat cs.length)) ++ wvList cs
        = (List.replicate c cs.length ++ expOf cs).map pw
    rw [List.map_append, List.map_replicate, wvList_eq cs]
    rfl

theorem wvSeq_eq : ∀ cs, wvSeq cs = pwSeq (expOf cs)
  | [] => rfl
  | c :: cs => by
    show StageA.repL (blockOf cs.length) c ++ wvSeq cs
        = pwSeq (List.replicate c cs.length ++ expOf cs)
    rw [pwSeq_append, wvSeq_eq cs, pwSeq_replicate]

/-- The value of a count vector is the value of its exponent list. -/
theorem wv_eq (cs : List Nat) : wv cs = pwv (expOf cs) := by
  show ofList (wvList cs) = ofList ((expOf cs).map pw)
  rw [wvList_eq]

/-- The matrix of a count vector is the matrix of its exponent list. -/
theorem wvM_eq (cs : List Nat) : wvM cs = pwM (expOf cs) := by
  show StageA.oneRow (wvSeq cs) = StageA.oneRow (pwSeq (expOf cs))
  rw [wvSeq_eq]

/-- Every exponent of `expOf cs` is below the level of the head. -/
private theorem expOf_lt : ∀ (cs : List Nat), ∀ x ∈ expOf cs, x < cs.length
  | [], x, hx => by simp [expOf] at hx
  | c :: cs, x, hx => by
    rcases List.mem_append.mp hx with h | h
    · rw [List.eq_of_mem_replicate h]; simp
    · have := expOf_lt cs x h
      simp only [List.length_cons]
      omega

private theorem expOf_replicate_zero : ∀ j, expOf (List.replicate j 0) = []
  | 0 => rfl
  | j + 1 => by
    show List.replicate 0 (List.replicate j 0).length ++ expOf (List.replicate j 0) = []
    rw [expOf_replicate_zero j]
    rfl

/-- The vector that names `ω^j·(c+1)`: it is the one the limit step produces. -/
private theorem expOf_step (c j : Nat) :
    expOf (c :: List.replicate j 0) = List.replicate c j := by
  show List.replicate c (List.replicate j 0).length ++ expOf (List.replicate j 0) = _
  rw [expOf_replicate_zero j, List.length_replicate, List.append_nil]

/-! ### Order facts for `ofNat` and `ω^k`

`ltF_ofNat_succ` of §1 is the special case `m = i+1` of `ltF_ofNat_lt`; the
converse direction `ltF_ofNat_ge` is what turns a classification hypothesis into
a bound on the exponent. -/

private theorem ltF_ofNat_one : ∀ (i f : Nat), 1 ≤ i → ltF f (ofNat i) one = false
  | 0, _, h => by omega
  | 1, f, _ => ltF_irrefl f one
  | i + 2, f, _ => by
    cases f with
    | zero => rfl
    | succ g =>
      rw [ofNat_shape i]
      show (if (add one (ofNat (i+1)) == one) = true then false else ltF g one one) = false
      rw [show ((add one (ofNat (i+1)) == one) : Bool) = false from rfl]
      simp only [Bool.false_eq_true, if_false]
      exact ltF_irrefl g one

private theorem ltF_ofNat_ge : ∀ (m i f : Nat), m ≤ i → ltF f (ofNat i) (ofNat m) = false
  | 0, i, f, _ => ltF_lt_zero f (ofNat i)
  | 1, i, f, h => ltF_ofNat_one i f h
  | m + 2, i, f, h => by
    cases f with
    | zero => rfl
    | succ g =>
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
      have hrec : ltF g (ofNat (i'+1)) (ofNat (m+1)) = false :=
        ltF_ofNat_ge (m+1) (i'+1) g (by omega)
      rw [ofNat_shape i', ofNat_shape m]
      show (if (add one (ofNat (i'+1)) == add one (ofNat (m+1))) = true then false
            else if ((one : Term) == one) = true then ltF g (ofNat (i'+1)) (ofNat (m+1))
                 else ltF g one one) = false
      cases hbe : ((add one (ofNat (i'+1)) == add one (ofNat (m+1))) : Bool) with
      | true => simp
      | false => simp [hrec]

private theorem ltF_ofNat_lt : ∀ (i m f : Nat), i < m → i + 2 ≤ f →
    ltF f (ofNat i) (ofNat m) = true
  | 0, m, f, hlt, hf => by
    refine ltF_zero (by omega) ?_
    cases m with
    | zero => omega
    | succ j => exact ofNat_ne_zero j
  | 1, m, f, hlt, hf => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    cases f with
    | zero => omega
    | succ g =>
      rw [ofNat_shape m']
      show (if ((one : Term) == add one (ofNat (m'+1))) = true then false
            else (((one : Term) == one) || ltF g one one)) = true
      rw [show (((one : Term) == add one (ofNat (m'+1))) : Bool) = false from rfl]
      simp
  | i + 2, m, f, hlt, hf => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
    cases f with
    | zero => omega
    | succ g =>
      have hrec : ltF g (ofNat (i+1)) (ofNat (m'+2)) = true :=
        ltF_ofNat_lt (i+1) (m'+2) g (by omega) (by omega)
      rw [ofNat_shape i, ofNat_shape (m'+1)]
      show (if (add one (ofNat (i+1)) == add one (ofNat (m'+2))) = true then false
            else if ((one : Term) == one) = true then ltF g (ofNat (i+1)) (ofNat (m'+2))
                 else ltF g one one) = true
      rw [show ((add one (ofNat (i+1)) == add one (ofNat (m'+2))) : Bool) = false from by
        simp [ne_of_ltF hrec]]
      simp [hrec]

private theorem lt_ofNat_lt {i m : Nat} (h : i < m) : lt (ofNat i) (ofNat m) = true := by
  refine lt_of_ltF (N := i + 2) (fun f hf => ltF_ofNat_lt i m f h hf) ?_
  have := deg_ofNat i
  show i + 2 ≤ 2 * ((ofNat i).deg + (ofNat m).deg) + 8
  omega

private theorem pw_isAP (k : Nat) : (pw k).isAP = true := rfl

private theorem pw_ne_zero (k : Nat) : pw k ≠ zero := by intro hc; exact Term.noConfusion hc

private theorem ltF_pw_lt {i m : Nat} (h : i < m) : ∀ f, i + 3 ≤ f → ltF f (pw i) (pw m) = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g => exact ltF_phi_same (ltF_ofNat_lt i m g h (by omega))

private theorem lt_pw_lt {i m : Nat} (h : i < m) : lt (pw i) (pw m) = true := by
  refine lt_of_ltF (N := i + 3) (ltF_pw_lt h) ?_
  have := deg_ofNat i
  show i + 3 ≤ 2 * ((phi zero (ofNat i)).deg + (phi zero (ofNat m)).deg) + 8
  show i + 3 ≤ 2 * ((1 + (zero : Term).deg + (ofNat i).deg)
    + (1 + (zero : Term).deg + (ofNat m).deg)) + 8
  show i + 3 ≤ 2 * ((1 + 1 + (ofNat i).deg) + (1 + 1 + (ofNat m).deg)) + 8
  omega

private theorem le_one_pw : ∀ k, le one (pw k) = true
  | 0 => rfl
  | k + 1 => by
    have h : lt (pw 0) (pw (k+1)) = true := lt_pw_lt (by omega)
    show ((one == pw (k+1)) || lt one (pw (k+1))) = true
    rw [show lt one (pw (k+1)) = true from h]
    simp

/-- **Nothing but a natural number lies below a natural number.**  Generalises
    `below_two`; the formation conditions are what exclude the junk sums. -/
private theorem below_ofNat : ∀ (m f : Nat) (s : Term), inT s = true →
    ltF f s (ofNat m) = true → ∃ i, s = ofNat i
  | 0, f, s, _, h => by
    exact absurd h (by rw [show (ofNat 0 : Term) = zero from rfl, ltF_lt_zero]; simp)
  | 1, f, s, hs, h => ⟨0, eq_zero_of_ltF_one hs h⟩
  | m + 2, f, s, hs, h => by
    cases f with
    | zero => exact absurd h (by rw [show ltF 0 s (ofNat (m+2)) = false from rfl]; simp)
    | succ g =>
      rw [ofNat_shape m] at h
      have key : ∀ (x : Term), inT x = true → ((x == one) || ltF g x one) = true →
          ∃ i, x = ofNat i := by
        intro x hx hh
        cases hxo : (x == one) with
        | true => exact ⟨1, by simpa using hxo⟩
        | false =>
          rw [hxo] at hh
          simp only [Bool.false_or] at hh
          exact ⟨0, eq_zero_of_ltF_one hx hh⟩
      cases s with
      | zero => exact ⟨0, rfl⟩
      | M => exact key M hs h
      | omg a => exact key (omg a) hs h
      | phi a b => exact key (phi a b) hs h
      | psi a b => exact key (psi a b) hs h
      | Z a => exact key (Z a) hs h
      | add a b =>
        obtain ⟨hap, ha, hb⟩ := inT_add hs
        cases hxo : ((add a b) == add one (ofNat (m+1))) with
        | true =>
          exact ⟨m + 2, by
            rw [show add a b = add one (ofNat (m+1)) from by simpa using hxo, ofNat_shape m]⟩
        | false =>
          have h2 : (if (a == one) = true then ltF g b (ofNat (m+1)) else ltF g a one) = true := by
            rw [show ltF (g+1) (add a b) (add one (ofNat (m+1)))
                  = (if ((add a b) == add one (ofNat (m+1))) = true then false
                     else if (a == one) = true then ltF g b (ofNat (m+1))
                     else ltF g a one : Bool) from rfl, hxo] at h
            simpa using h
          cases haz : (a == one) with
          | true =>
            have ha1 : a = one := by simpa using haz
            rw [haz] at h2
            simp only [if_true] at h2
            obtain ⟨i, hi⟩ := below_ofNat (m+1) g b hb h2
            cases i with
            | zero => exact absurd hi (inT_add_ne_zero hs)
            | succ i' => exact ⟨i' + 2, by rw [ha1, hi, ofNat_shape i']⟩
          | false =>
            rw [haz] at h2
            simp only [Bool.false_eq_true, if_false] at h2
            exact absurd (eq_zero_of_ltF_one ha h2) (isAP_ne_zero hap)

/-! ### Shape lemmas for `pwv` -/

private theorem pwv_nil : pwv [] = zero := rfl

private theorem pwv_single (k : Nat) : pwv [k] = pw k := rfl

private theorem pwv_cons {k : Nat} {e : List Nat} (h : e ≠ []) :
    pwv (k :: e) = add (pw k) (pwv e) := by
  show ofList (pw k :: e.map pw) = add (pw k) (ofList (e.map pw))
  refine ofList_cons ?_
  cases e with
  | nil => exact absurd rfl h
  | cons _ _ => simp

private theorem pwv_isAP : ∀ (e : List Nat), (pwv e).isAP = true → ∃ k, e = [k]
  | [], h => by rw [show pwv [] = zero from rfl] at h; exact absurd h (by simp [isAP])
  | [k], _ => ⟨k, rfl⟩
  | k :: k' :: r, h => by
    rw [pwv_cons (by simp)] at h
    exact absurd h (by simp [isAP])

private theorem toList_pwv (e : List Nat) : toList (pwv e) = e.map pw :=
  toList_ofList (fun x hx => by
    obtain ⟨k, _, hk⟩ := List.mem_map.mp hx
    rw [← hk]; exact pw_isAP k)

private theorem ofNat_cases : ∀ k,
    (ofNat k = zero) ∨ (ofNat k = one) ∨ (∃ j, ofNat k = add one (ofNat j))
  | 0 => Or.inl rfl
  | 1 => Or.inr (Or.inl rfl)
  | k + 2 => Or.inr (Or.inr ⟨k + 1, ofNat_shape k⟩)

private theorem psi_ne_ofNat (p a : Term) : ∀ i, psi p a ≠ ofNat i := by
  intro i hc
  rcases ofNat_cases i with h | h | ⟨j, h⟩ <;> rw [h] at hc <;> exact Term.noConfusion hc

private theorem Z_ne_ofNat (a : Term) : ∀ i, Z a ≠ ofNat i := by
  intro i hc
  rcases ofNat_cases i with h | h | ⟨j, h⟩ <;> rw [h] at hc <;> exact Term.noConfusion hc

/-! ### Classification: the terms of 𝔗(M) below ω^k

`below_pw` is the analogue of `below_omega` / `below_omega_sq` with the level as
a parameter, and `tail_pw` its companion for the tail of a sum (the analogue of
`tail_ofNat` / `tail_wm`).  The two are stratified by the level: `tail_pw` at
bound `K` takes the classification at levels `≤ K` as a hypothesis, and
`below_pw` at level `k` only ever calls it at a level `< k`. -/

private theorem tail_pw (K : Nat)
    (hK : ∀ (k : Nat), k ≤ K → ∀ (f : Nat) (s : Term), inT s = true → ltF f s (pw k) = true →
            ∃ e, (∀ x ∈ e, x < k) ∧ s = pwv e) :
    ∀ (b : Term), inT b = true → b ≠ zero → ∀ (k : Nat), k ≤ K →
      le ((toList b).headD zero) (pw k) = true →
      ∃ e, e ≠ [] ∧ (∀ x ∈ e, x ≤ k) ∧ b = pwv e
  | zero, _, hne, _, _, _ => absurd rfl hne
  | add c d, h, _, k, hk, hle => by
    obtain ⟨hap, hc, hd⟩ := inT_add h
    rw [show (toList (add c d)).headD zero = c from rfl] at hle
    have hdne : d ≠ zero := inT_add_ne_zero h
    have hdhead : le ((toList d).headD zero) c = true := inT_add_head_le h
    cases hco : (c == pw k) with
    | true =>
      have hck : c = pw k := by simpa using hco
      rw [hck] at hdhead
      obtain ⟨eb, hbne, hbb, hbeq⟩ := tail_pw K hK d hd hdne k hk hdhead
      exact ⟨k :: eb, by simp, by
        intro x hx
        rcases List.mem_cons.mp hx with h' | h'
        · omega
        · exact hbb x h', by rw [hck, hbeq, pwv_cons hbne]⟩
    | false =>
      have hlt : lt c (pw k) = true := by
        simp only [TM.Term.le, hco, Bool.false_or] at hle
        exact hle
      obtain ⟨ec, hec, hceq⟩ := hK k hk _ c hc hlt
      obtain ⟨i, rfl⟩ := pwv_isAP ec (by rw [← hceq]; exact hap)
      have hik : i < k := hec i (by simp)
      rw [show pwv [i] = pw i from rfl] at hceq
      rw [hceq] at hdhead
      obtain ⟨eb, hbne, hbb, hbeq⟩ := tail_pw K hK d hd hdne i (by omega) hdhead
      exact ⟨i :: eb, by simp, by
        intro x hx
        rcases List.mem_cons.mp hx with h' | h'
        · omega
        · have := hbb x h'; omega, by rw [hceq, hbeq, pwv_cons hbne]⟩
  | M, _, _, k, _, hle => by
    rw [show (toList (M : Term)).headD zero = M from rfl] at hle
    simp only [TM.Term.le, show ((M : Term) == pw k) = false from rfl, Bool.false_or,
      show lt M (pw k) = false from Evidence.StageA.ltF_M_phi _ zero (ofNat k)] at hle
    exact Bool.noConfusion hle
  | omg a, _, _, k, _, hle => by
    rw [show (toList (omg a)).headD zero = omg a from rfl] at hle
    simp only [TM.Term.le, show ((omg a) == pw k) = false from rfl, Bool.false_or,
      show lt (omg a) (pw k) = false from rfl] at hle
    exact Bool.noConfusion hle
  | phi c d, h, _, k, hk, hle => by
    rw [show (toList (phi c d)).headD zero = phi c d from rfl] at hle
    cases hco : ((phi c d) == pw k) with
    | true => exact ⟨[k], by simp, by intro x hx; simp at hx; omega, by simpa using hco⟩
    | false =>
      have hlt : lt (phi c d) (pw k) = true := by
        simp only [TM.Term.le, hco, Bool.false_or] at hle
        exact hle
      obtain ⟨ec, hec, hceq⟩ := hK k hk _ (phi c d) h hlt
      obtain ⟨i, rfl⟩ := pwv_isAP ec (by rw [← hceq]; rfl)
      exact ⟨[i], by simp, by intro x hx; simp at hx; have := hec i (by simp); omega, hceq⟩
  | psi p a, h, _, k, hk, hle => by
    rw [show (toList (psi p a)).headD zero = psi p a from rfl] at hle
    cases hco : ((psi p a) == pw k) with
    | true => exact absurd (by simpa using hco : psi p a = pw k) (by intro hc; exact Term.noConfusion hc)
    | false =>
      have hlt : lt (psi p a) (pw k) = true := by
        simp only [TM.Term.le, hco, Bool.false_or] at hle
        exact hle
      obtain ⟨ec, hec, hceq⟩ := hK k hk _ (psi p a) h hlt
      obtain ⟨i, rfl⟩ := pwv_isAP ec (by rw [← hceq]; rfl)
      exact absurd hceq (by intro hc; exact Term.noConfusion hc)
  | Z a, h, _, k, hk, hle => by
    rw [show (toList (Z a)).headD zero = Z a from rfl] at hle
    cases hco : ((Z a) == pw k) with
    | true => exact absurd (by simpa using hco : Z a = pw k) (by intro hc; exact Term.noConfusion hc)
    | false =>
      have hlt : lt (Z a) (pw k) = true := by
        simp only [TM.Term.le, hco, Bool.false_or] at hle
        exact hle
      obtain ⟨ec, hec, hceq⟩ := hK k hk _ (Z a) h hlt
      obtain ⟨i, rfl⟩ := pwv_isAP ec (by rw [← hceq]; rfl)
      exact absurd hceq (by intro hc; exact Term.noConfusion hc)

/-- **L1 at level k.**  Every term of 𝔗(M) below ω^k is a formal sum of `ω^{eᵢ}`
    with every exponent `eᵢ < k`.  Recursion on `(k, fuel)`: the fuel drops when
    the head of a sum is peeled, the level drops when the tail is handed to
    `tail_pw`. -/
theorem below_pw : ∀ (k f : Nat) (s : Term), inT s = true → ltF f s (pw k) = true →
    ∃ e, (∀ x ∈ e, x < k) ∧ s = pwv e
  | k, 0, s, _, h => by
    exact absurd h (by rw [show ltF 0 s (pw k) = false from rfl]; simp)
  | k, f + 1, s, hs, h => by
    cases s with
    | zero => exact ⟨[], by simp, rfl⟩
    | M =>
      rw [show ltF (f+1) M (pw k) = false from Evidence.StageA.ltF_M_phi (f+1) zero (ofNat k)] at h
      exact Bool.noConfusion h
    | omg a =>
      rw [show ltF (f+1) (omg a) (pw k) = false from rfl] at h
      exact Bool.noConfusion h
    | psi p a =>
      have h2 : ((psi p a == zero) || (psi p a == ofNat k) || ltF f (psi p a) zero
                 || ltF f (psi p a) (ofNat k)) = true := h
      rw [show ((psi p a == zero) : Bool) = false from rfl,
        show ((psi p a == ofNat k) : Bool) = false from by
          cases hb : ((psi p a) == ofNat k) with
          | true => exact absurd (by simpa using hb) (psi_ne_ofNat p a k)
          | false => rfl,
        ltF_lt_zero] at h2
      simp only [Bool.or_false, Bool.false_or] at h2
      obtain ⟨i, hi⟩ := below_ofNat k f (psi p a) hs h2
      exact absurd hi (psi_ne_ofNat p a i)
    | Z a =>
      have h2 : ((Z a == zero) || (Z a == ofNat k) || ltF f (Z a) zero
                 || ltF f (Z a) (ofNat k)) = true := h
      rw [show ((Z a == zero) : Bool) = false from rfl,
        show ((Z a == ofNat k) : Bool) = false from by
          cases hb : ((Z a) == ofNat k) with
          | true => exact absurd (by simpa using hb) (Z_ne_ofNat a k)
          | false => rfl,
        ltF_lt_zero] at h2
      simp only [Bool.or_false, Bool.false_or] at h2
      obtain ⟨i, hi⟩ := below_ofNat k f (Z a) hs h2
      exact absurd hi (Z_ne_ofNat a i)
    | phi a b =>
      obtain ⟨ha, hb⟩ := inT_phi hs
      cases hxo : ((phi a b) == pw k) with
      | true =>
        have heq : phi a b = pw k := by simpa using hxo
        rw [heq, ltF_irrefl] at h
        exact Bool.noConfusion h
      | false =>
        have h2 : (if (a == zero) = true then ltF f b (ofNat k)
                   else if ltF f a zero = true then ltF f b (phi zero (ofNat k))
                   else ((phi a b == ofNat k) || ltF f (phi a b) (ofNat k))) = true := by
          rw [show ltF (f+1) (phi a b) (pw k)
                = (if ((phi a b) == pw k) = true then false
                   else if (a == zero) = true then ltF f b (ofNat k)
                   else if ltF f a zero = true then ltF f b (phi zero (ofNat k))
                   else ((phi a b == ofNat k) || ltF f (phi a b) (ofNat k)) : Bool) from rfl,
              hxo] at h
          simpa using h
        cases haz : (a == zero) with
        | true =>
          have haz' : a = zero := by simpa using haz
          rw [haz] at h2
          simp only [if_true] at h2
          obtain ⟨i, hi⟩ := below_ofNat k f b hb h2
          have hik : i < k := by
            rcases Nat.lt_or_ge i k with hlt | hge
            · exact hlt
            · rw [hi, ltF_ofNat_ge k i f hge] at h2
              exact Bool.noConfusion h2
          exact ⟨[i], by intro x hx; simp at hx; omega, by rw [haz', hi]; rfl⟩
        | false =>
          rw [haz] at h2
          simp only [Bool.false_eq_true, if_false, ltF_lt_zero] at h2
          have hphi : ∀ i, phi a b ≠ ofNat i := by
            intro i hcon
            rcases ofNat_cases i with hz | ho | ⟨j, hj⟩
            · rw [hz] at hcon; exact Term.noConfusion hcon
            · have hcon' : phi a b = phi zero zero := by rw [ho] at hcon; exact hcon
              injection hcon' with h1 _
              rw [h1] at haz
              simp at haz
            · rw [hj] at hcon; exact Term.noConfusion hcon
          cases hbe : ((phi a b == ofNat k) : Bool) with
          | true => exact absurd (by simpa using hbe) (hphi k)
          | false =>
            rw [hbe] at h2
            simp only [Bool.false_or] at h2
            obtain ⟨i, hi⟩ := below_ofNat k f (phi a b) hs h2
            exact absurd hi (hphi i)
    | add a b =>
      obtain ⟨hap, ha, hb⟩ := inT_add hs
      have h2 : ltF f a (pw k) = true := h
      obtain ⟨ea, hea, haa⟩ := below_pw k f a ha h2
      obtain ⟨i, rfl⟩ := pwv_isAP ea (by rw [← haa]; exact hap)
      have hik : i < k := hea i (by simp)
      rw [show pwv [i] = pw i from rfl] at haa
      have hhead : le ((toList b).headD zero) a = true := inT_add_head_le hs
      rw [haa] at hhead
      obtain ⟨eb, hbne, hbb, hbeq⟩ :=
        tail_pw i (fun k' hk' f' s' hs' h' => below_pw k' f' s' hs' h') b hb
          (inT_add_ne_zero hs) i (Nat.le_refl i) hhead
      refine ⟨i :: eb, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with h' | h'
        · omega
        · have := hbb x h'; omega
      · rw [haa, hbeq, pwv_cons hbne]
  termination_by k f => (k, f)

/-! ### Degrees, and the fuel budget

Every order statement is proved in the "for all sufficiently large fuel" form and
consumed at the default fuel `2*(deg+deg)+8`, so each family needs a lower bound
on its degree.  These three are all that the ω^k region uses. -/

private theorem deg_pos : ∀ (t : Term), 1 ≤ t.deg
  | zero => by show 1 ≤ 1; omega
  | M => by show 1 ≤ 1; omega
  | add a b => by show 1 ≤ 1 + a.deg + b.deg; omega
  | omg a => by show 1 ≤ 1 + a.deg; omega
  | phi a b => by show 1 ≤ 1 + a.deg + b.deg; omega
  | psi a b => by show 1 ≤ 1 + a.deg + b.deg; omega
  | Z a => by show 1 ≤ 1 + a.deg; omega

private theorem deg_pw (k : Nat) : k + 2 ≤ (pw k).deg := by
  have := deg_ofNat k
  show k + 2 ≤ 1 + (zero : Term).deg + (ofNat k).deg
  show k + 2 ≤ 1 + 1 + (ofNat k).deg
  omega

private theorem deg_ofList_len : ∀ (l : List Term), l.length ≤ (ofList l).deg
  | [] => by show 0 ≤ _; omega
  | [a] => by show 1 ≤ a.deg; exact deg_pos a
  | a :: b :: r => by
    have h1 := deg_ofList_len (b :: r)
    have h2 := deg_pos a
    show (b :: r).length + 1 ≤ 1 + a.deg + (ofList (b :: r)).deg
    omega

private theorem deg_ofList_mem : ∀ (l : List Term) (x : Term), x ∈ l → x.deg ≤ (ofList l).deg
  | [], x, hx => by simp at hx
  | [a], x, hx => by
    have : x = a := by simpa using hx
    rw [this]
    show a.deg ≤ a.deg
    omega
  | a :: b :: r, x, hx => by
    rcases List.mem_cons.mp hx with h | h
    · rw [h]; show a.deg ≤ 1 + a.deg + (ofList (b :: r)).deg; omega
    · have := deg_ofList_mem (b :: r) x h
      show x.deg ≤ 1 + a.deg + (ofList (b :: r)).deg
      omega

private theorem deg_pwv_len (e : List Nat) : e.length ≤ (pwv e).deg := by
  have h := deg_ofList_len (e.map pw)
  simpa using h

private theorem deg_pwv_mem {e : List Nat} {x : Nat} (h : x ∈ e) : x + 2 ≤ (pwv e).deg := by
  have h1 : (pw x).deg ≤ (pwv e).deg :=
    deg_ofList_mem (e.map pw) (pw x) (List.mem_map_of_mem h)
  have h2 := deg_pw x
  omega

private theorem pwv_ne_zero : ∀ (l : List Nat), l ≠ [] → pwv l ≠ zero
  | [], h => absurd rfl h
  | [k], _ => by rw [show pwv [k] = pw k from rfl]; exact pw_ne_zero k
  | k :: k' :: r, _ => by rw [pwv_cons (by simp)]; intro hc; exact Term.noConfusion hc

/-- **The pointwise bound.**  A sum of `|e|` components each at most `ω^j` is
    strictly below `ω^j·(|e|+1)`, and this stays true under any prefix — the
    prefix parameter is what makes the induction go through. -/
private theorem lt_pwv_repl : ∀ (e : List Nat) (j : Nat), (∀ x ∈ e, x ≤ j) → ∀ (P : List Term),
    (∀ z ∈ P, z.isAP = true) → ∀ f, P.length + e.length + j + 4 ≤ f →
    ltF f (ofList (P ++ e.map pw))
      (ofList (P ++ (List.replicate (e.length + 1) j).map pw)) = true
  | [], j, _, P, hP, f, hf => by
    cases P with
    | nil =>
      show ltF f (ofList ([] : List Term)) (ofList [pw j]) = true
      refine ltF_zero ?_ (pw_ne_zero j)
      simp only [List.length_nil] at hf
      omega
    | cons z Q =>
      show ltF f (ofList ((z :: Q) ++ ([] : List Term))) (ofList ((z :: Q) ++ [pw j])) = true
      rw [List.append_nil]
      refine ltF_ofList_prefix (z :: Q) (pw j) [] (by simp) hP f ?_
      simp only [List.length_cons, List.length_nil] at hf ⊢
      omega
  | x :: r, j, hxr, P, hP, f, hf => by
    rcases Nat.lt_or_ge x j with hlt | hge
    · have hrhs : (List.replicate ((x :: r).length + 1) j).map pw
          = pw j :: (List.replicate (r.length + 1) j).map pw := by
        show (List.replicate (r.length + 1 + 1) j).map pw = _
        rw [List.replicate_succ]
        rfl
      rw [hrhs]
      show ltF f (ofList (P ++ pw x :: r.map pw))
        (ofList (P ++ pw j :: (List.replicate (r.length + 1) j).map pw)) = true
      refine ltF_ofList_head P (pw x) (pw j) (r.map pw)
        ((List.replicate (r.length + 1) j).map pw) (x + 3) (pw_isAP x) (pw_isAP j)
        (fun g hg => ltF_pw_lt hlt g hg) f ?_
      simp only [List.length_cons] at hf
      omega
    · have hxj : x = j := by have := hxr x (by simp); omega
      subst hxj
      have hIH := lt_pwv_repl r x (fun y hy => hxr y (by simp [hy])) (P ++ [pw x])
        (by
          intro z hz
          rcases List.mem_append.mp hz with h | h
          · exact hP z h
          · have : z = pw x := by simpa using h
            rw [this]; exact pw_isAP x)
        f (by simp only [List.length_append, List.length_cons, List.length_nil] at hf ⊢; omega)
      rw [List.append_assoc, List.append_assoc] at hIH
      show ltF f (ofList (P ++ pw x :: r.map pw))
        (ofList (P ++ (List.replicate (r.length + 1 + 1) x).map pw)) = true
      rw [List.replicate_succ]
      exact hIH

private theorem ltF_omg_phi : ∀ (f : Nat) (a c d : Term), ltF f (omg a) (phi c d) = false
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl

/-- **L1 relative to a prefix.**  A term of 𝔗(M) below `ω^{p₁}+…+ω^{pᵣ}+ω^{j+1}`
    either has the whole prefix `p` in front of a rest bounded by `ω^j`, or it
    already differs from `p` inside `p`, and then it is below EVERY extension of
    `p` — which is the only thing the cofinality clause needs of it. -/
private theorem below_pre : ∀ (f : Nat) (p : List Nat) (j : Nat) (s : Term), inT s = true →
    ltF f s (pwv (p ++ [j])) = true →
    (∃ e, (∀ x ∈ e, x < j) ∧ s = pwv (p ++ e)) ∨
    (∀ g, 2 * s.deg + 2 ≤ g → ∀ t : List Nat, t ≠ [] → ltF g s (pwv (p ++ t)) = true)
  | 0, p, j, s, _, h => by
    exact absurd h (by rw [show ltF 0 s (pwv (p ++ [j])) = false from rfl]; simp)
  | f + 1, [], j, s, hs, h => by
    obtain ⟨e, he, hse⟩ := below_pw j (f + 1) s hs h
    exact Or.inl ⟨e, he, by rw [hse]; rfl⟩
  | f + 1, x :: p', j, s, hs, h => by
    have htgt : pwv ((x :: p') ++ [j]) = add (pw x) (pwv (p' ++ [j])) :=
      pwv_cons (by simp)
    have hext : ∀ t : List Nat, t ≠ [] →
        pwv ((x :: p') ++ t) = add (pw x) (pwv (p' ++ t)) := by
      intro t ht
      refine pwv_cons ?_
      intro hc
      exact ht (List.append_eq_nil_iff.mp hc).2
    rw [htgt] at h
    -- the head-only clause 2.3.11, shared by the five non-sum constructors
    cases s with
    | zero =>
      refine Or.inr (fun g hg t ht => ?_)
      have hg4 : 4 ≤ g := hg
      refine ltF_zero (by omega) ?_
      rw [hext t ht]
      intro hc; exact Term.noConfusion hc
    | M =>
      have h2 : (((M : Term) == pw x) || ltF f M (pw x)) = true := h
      rw [show (((M : Term) == pw x) : Bool) = false from rfl,
        show ltF f M (pw x) = false from Evidence.StageA.ltF_M_phi f zero (ofNat x)] at h2
      exact Bool.noConfusion h2
    | omg a =>
      have h2 : ((omg a == pw x) || ltF f (omg a) (pw x)) = true := h
      rw [show ((omg a == pw x) : Bool) = false from rfl,
        show ltF f (omg a) (pw x) = false from ltF_omg_phi f a zero (ofNat x)] at h2
      exact Bool.noConfusion h2
    | psi q a =>
      have h2 : ((psi q a == pw x) || ltF f (psi q a) (pw x)) = true := h
      rw [show ((psi q a == pw x) : Bool) = false from rfl] at h2
      simp only [Bool.false_or] at h2
      obtain ⟨e, _, heq⟩ := below_pw x f (psi q a) hs h2
      obtain ⟨y, rfl⟩ := pwv_isAP e (by rw [← heq]; rfl)
      exact absurd heq (by intro hc; exact Term.noConfusion hc)
    | Z a =>
      have h2 : ((Z a == pw x) || ltF f (Z a) (pw x)) = true := h
      rw [show ((Z a == pw x) : Bool) = false from rfl] at h2
      simp only [Bool.false_or] at h2
      obtain ⟨e, _, heq⟩ := below_pw x f (Z a) hs h2
      obtain ⟨y, rfl⟩ := pwv_isAP e (by rw [← heq]; rfl)
      exact absurd heq (by intro hc; exact Term.noConfusion hc)
    | phi a b =>
      have h2 : ((phi a b == pw x) || ltF f (phi a b) (pw x)) = true := h
      cases hxo : ((phi a b == pw x) : Bool) with
      | true =>
        have hax : phi a b = pw x := by simpa using hxo
        cases p' with
        | nil => exact Or.inl ⟨[], by simp, by rw [hax]; rfl⟩
        | cons z q =>
          refine Or.inr (fun g hg t ht => ?_)
          rw [hext t ht, hax]
          cases g with
          | zero => have := deg_pos (pw x); omega
          | succ g' => exact ltF_to_add (pw_isAP x) (by simp)
      | false =>
        rw [hxo] at h2
        simp only [Bool.false_or] at h2
        obtain ⟨e, he, heq⟩ := below_pw x f (phi a b) hs h2
        obtain ⟨y, rfl⟩ := pwv_isAP e (by rw [← heq]; rfl)
        have hyx : y < x := he y (by simp)
        have hdy : y + 2 ≤ (phi a b).deg := by rw [show phi a b = pw y from heq]; exact deg_pw y
        refine Or.inr (fun g hg t ht => ?_)
        rw [hext t ht, show phi a b = pw y from heq]
        cases g with
        | zero => omega
        | succ g' =>
          refine ltF_to_add (pw_isAP y) ?_
          rw [ltF_pw_lt hyx g' (by omega)]
          simp
    | add a b =>
      obtain ⟨hap, ha, hb⟩ := inT_add hs
      cases hxo : ((add a b) == add (pw x) (pwv (p' ++ [j]))) with
      | true =>
        have heq : add a b = add (pw x) (pwv (p' ++ [j])) := by simpa using hxo
        rw [heq, ltF_irrefl] at h
        exact Bool.noConfusion h
      | false =>
        have h2 : (if (a == pw x) = true then ltF f b (pwv (p' ++ [j]))
                   else ltF f a (pw x)) = true := by
          rw [show ltF (f+1) (add a b) (add (pw x) (pwv (p' ++ [j])))
                = (if ((add a b) == add (pw x) (pwv (p' ++ [j]))) = true then false
                   else if (a == pw x) = true then ltF f b (pwv (p' ++ [j]))
                   else ltF f a (pw x) : Bool) from rfl, hxo] at h
          simpa using h
        cases haz : (a == pw x) with
        | true =>
          have hax : a = pw x := by simpa using haz
          rw [haz] at h2
          simp only [if_true] at h2
          rcases below_pre f p' j b hb h2 with ⟨e, he, hbe⟩ | hb'
          · refine Or.inl ⟨e, he, ?_⟩
            have hne : p' ++ e ≠ [] := by
              intro hc
              exact inT_add_ne_zero hs (by rw [hbe, hc]; rfl)
            rw [hax, hbe, ← pwv_cons hne]
            rfl
          · refine Or.inr (fun g hg t ht => ?_)
            have hdb : (add a b).deg = 1 + a.deg + b.deg := rfl
            have hda : 2 ≤ a.deg := by rw [hax]; have := deg_pw x; omega
            rw [hext t ht, hax]
            cases g with
            | zero => omega
            | succ g' =>
              exact ltF_add_same (hb' g' (by omega) t ht)
        | false =>
          rw [haz] at h2
          simp only [Bool.false_eq_true, if_false] at h2
          obtain ⟨ea, hea, haeq⟩ := below_pw x f a ha h2
          obtain ⟨y, rfl⟩ := pwv_isAP ea (by rw [← haeq]; exact hap)
          have hyx : y < x := hea y (by simp)
          have hay : a = pw y := haeq
          have hhead : le ((toList b).headD zero) a = true := inT_add_head_le hs
          rw [hay] at hhead
          obtain ⟨eb, hbne, hbb, hbeq⟩ :=
            tail_pw y (fun k' hk' f' s' hs' h' => below_pw k' f' s' hs' h') b hb
              (inT_add_ne_zero hs) y (Nat.le_refl y) hhead
          have hdy : y + 2 ≤ (add a b).deg := by
            have h1 : a.deg ≤ (add a b).deg := by show a.deg ≤ 1 + a.deg + b.deg; omega
            have h2' : y + 2 ≤ a.deg := by rw [hay]; exact deg_pw y
            omega
          refine Or.inr (fun g hg t ht => ?_)
          rw [hext t ht, hay, hbeq]
          have hpt : p' ++ t ≠ [] := by
            intro hc; exact ht (List.append_eq_nil_iff.mp hc).2
          rw [show add (pw y) (pwv eb) = ofList ([] ++ pw y :: eb.map pw) from
                (pwv_cons hbne).symm,
            show add (pw x) (pwv (p' ++ t)) = ofList ([] ++ pw x :: (p' ++ t).map pw) from
                (pwv_cons hpt).symm]
          refine ltF_ofList_head [] (pw y) (pw x) (eb.map pw) ((p' ++ t).map pw) (y + 3)
            (pw_isAP y) (pw_isAP x) (fun g' hg' => ltF_pw_lt hyx g' hg') g ?_
          simp only [List.length_nil]
          omega

/-- **The cofinality clause of the whole region, once.**  Every term of 𝔗(M)
    below `P + ω^{j+1}` is overtaken by some `P + ω^j·(n+1)`. -/
private theorem cof_pre (p : List Nat) (j : Nat) (s : Term) (hs : inT s = true)
    (h : lt s (pwv (p ++ [j + 1])) = true) :
    ∃ n, le s (pwv (p ++ List.replicate (n + 1) j)) = true := by
  have hP : ∀ z ∈ p.map pw, z.isAP = true := by
    intro z hz
    obtain ⟨k, _, hk⟩ := List.mem_map.mp hz
    rw [← hk]; exact pw_isAP k
  rcases below_pre _ p (j + 1) s hs h with ⟨e, he0, hse⟩ | h'
  · have he : ∀ x ∈ e, x ≤ j := fun x hx => by have := he0 x hx; omega
    refine ⟨e.length, ?_⟩
    have hsplit : ∀ (q : List Nat), pwv (p ++ q) = ofList (p.map pw ++ q.map pw) := by
      intro q
      show ofList ((p ++ q).map pw) = _
      rw [List.map_append]
    have hlt : lt s (pwv (p ++ List.replicate (e.length + 1) j)) = true := by
      refine lt_of_ltF (N := p.length + e.length + j + 4) (fun f hf => ?_) ?_
      · rw [hse, hsplit e, hsplit (List.replicate (e.length + 1) j)]
        exact lt_pwv_repl e j he (p.map pw) hP f (by simp only [List.length_map]; exact hf)
      · have h1 : p.length + e.length ≤ s.deg := by
          rw [hse]
          have h := deg_pwv_len (p ++ e)
          simpa using h
        have h2 : j + 2 ≤ (pwv (p ++ List.replicate (e.length + 1) j)).deg :=
          deg_pwv_mem (List.mem_append_right p (List.mem_replicate.mpr ⟨by omega, rfl⟩))
        omega
    simp [TM.Term.le, hlt]
  · refine ⟨0, ?_⟩
    have hlt : lt s (pwv (p ++ [j])) = true := by
      refine h' _ ?_ [j] (by simp)
      show 2 * s.deg + 2 ≤ 2 * (s.deg + (pwv (p ++ [j])).deg) + 8
      omega
    show ((s == pwv (p ++ List.replicate 1 j)) || lt s (pwv (p ++ List.replicate 1 j))) = true
    rw [show List.replicate 1 j = [j] from rfl, hlt]
    simp

/-! ### The matrices and the expansion

`A` is unconstrained in `StageA.expand_oneRow`: only the last block matters for
the BM4 rule.  That is what makes every lemma here prefix-relative for free. -/

private theorem blockOf_succ (j : Nat) : blockOf (j + 1) = blockOf j ++ [1] := by
  show 0 :: List.replicate (j+1) 1 = (0 :: List.replicate j 1) ++ [1]
  rw [List.replicate_succ']
  rfl

private theorem pwSeq_single (k : Nat) : pwSeq [k] = blockOf k := by
  show ((List.map blockOf [k]).flatten) = _
  simp

private theorem pwSeq_snoc (e : List Nat) (k : Nat) : pwSeq (e ++ [k]) = pwSeq e ++ blockOf k := by
  rw [pwSeq_append, pwSeq_single]

private theorem pwM_snoc_zero (e : List Nat) : pwM (e ++ [0]) = pwM e ++ [[0]] := by
  show StageA.oneRow (pwSeq (e ++ [0])) = _
  rw [pwSeq_snoc, show blockOf 0 = [0] from rfl, StageA.oneRow_append]
  rfl

private theorem kind_pwM_succ (e : List Nat) : BMS.kind (pwM (e ++ [0])) = .succ := by
  show (match (pwM (e ++ [0])).getLast? with
        | none => BMS.Kind.zero
        | some L => match BMS.lnz L with
          | none => BMS.Kind.succ
          | some _ => BMS.Kind.lim) = _
  rw [pwM_snoc_zero, List.getLast?_concat]
  rfl

private theorem expand_pwM_succ (e : List Nat) (n : Nat) :
    BMS.expand (pwM (e ++ [0])) n = pwM e := by
  have hL : (pwM (e ++ [0])).getLast? = some [0] := by
    rw [pwM_snoc_zero]; exact List.getLast?_concat
  have hexp : BMS.expand? (pwM (e ++ [0])) n = some ((pwM (e ++ [0])).dropLast) := by
    simp only [BMS.expand?, hL, Option.bind_eq_bind, Option.bind_some,
      show BMS.lnz ([0] : BMS.Col) = none from rfl, Option.pure_def]
  show (BMS.expand? (pwM (e ++ [0])) n).getD [] = _
  rw [hexp]
  show (pwM (e ++ [0])).dropLast = pwM e
  rw [pwM_snoc_zero]
  exact List.dropLast_concat

private theorem pwM_snoc_lim (e : List Nat) (j : Nat) :
    pwM (e ++ [j + 1]) = StageA.oneRow ((pwSeq e ++ blockOf j) ++ [1]) := by
  show StageA.oneRow (pwSeq (e ++ [j+1])) = _
  rw [pwSeq_snoc, blockOf_succ, List.append_assoc]

private theorem kind_pwM_lim (e : List Nat) (j : Nat) : BMS.kind (pwM (e ++ [j + 1])) = .lim := by
  have hL : (pwM (e ++ [j+1])).getLast? = some [1] := by
    rw [pwM_snoc_lim, StageA.oneRow_append]
    exact List.getLast?_concat
  show (match (pwM (e ++ [j+1])).getLast? with
        | none => BMS.Kind.zero
        | some L => match BMS.lnz L with
          | none => BMS.Kind.succ
          | some _ => BMS.Kind.lim) = _
  rw [hL]
  rfl

/-- `(P + ω^{j+1})[n] = P + ω^j·(n+1)`: the BM4 rule copies the last block. -/
private theorem expand_pwM_lim (e : List Nat) (j n : Nat) :
    BMS.expand (pwM (e ++ [j + 1])) n = pwM (e ++ List.replicate (n + 1) j) := by
  have hexp := StageA.expand_oneRow (A := pwSeq e) (B := blockOf j) (c := 1) (b0 := 0)
    (B' := List.replicate j 1) rfl (by omega)
    (by intro x hx; have := List.eq_of_mem_replicate hx; omega) (by omega) n
  show (BMS.expand? (pwM (e ++ [j+1])) n).getD [] = _
  rw [pwM_snoc_lim, hexp]
  show StageA.oneRow (pwSeq e ++ StageA.repL (blockOf j) (n+1)) = pwM (e ++ List.replicate (n+1) j)
  rw [← pwSeq_replicate, ← pwSeq_append]
  rfl

/-! ### The successor step on values, and the two strict-increase facts -/

private theorem filter_le_one_pw : ∀ (l : List Nat),
    (l.map pw).filter (fun a => le one a) = l.map pw
  | [] => rfl
  | k :: r => by
    show (pw k :: r.map pw).filter _ = _
    rw [List.filter_cons_of_pos (le_one_pw k), filter_le_one_pw r]
    rfl

private theorem plus_pwv_one (e : List Nat) : plus (pwv e) one = pwv (e ++ [0]) := by
  unfold plus
  rw [show toList (one : Term) = [one] from rfl]
  show ofList ((toList (pwv e)).filter (fun a => le one a) ++ [one]) = pwv (e ++ [0])
  rw [toList_pwv, filter_le_one_pw]
  show ofList (e.map pw ++ [pw 0]) = ofList ((e ++ [0]).map pw)
  rw [List.map_append]
  rfl

private theorem pw_map_isAP (q : List Nat) : ∀ z ∈ q.map pw, z.isAP = true := by
  intro z hz
  obtain ⟨k, _, hk⟩ := List.mem_map.mp hz
  rw [← hk]; exact pw_isAP k

/-- `P + ω^j·(n+1) < P + ω^{j+1}`. -/
private theorem lt_pwv_step (p : List Nat) (j n : Nat) :
    lt (pwv (p ++ List.replicate (n + 1) j)) (pwv (p ++ [j + 1])) = true := by
  have hsplit : ∀ (q : List Nat), pwv (p ++ q) = ofList (p.map pw ++ q.map pw) := by
    intro q
    show ofList ((p ++ q).map pw) = _
    rw [List.map_append]
  refine lt_of_ltF (N := p.length + j + 4) (fun f hf => ?_) ?_
  · rw [hsplit, hsplit]
    rw [show (List.replicate (n+1) j).map pw = pw j :: (List.replicate n j).map pw from by
          rw [List.replicate_succ]; rfl,
      show ([j+1] : List Nat).map pw = pw (j+1) :: ([] : List Term) from rfl]
    refine ltF_ofList_head (p.map pw) (pw j) (pw (j+1)) ((List.replicate n j).map pw) []
      (j + 3) (pw_isAP j) (pw_isAP (j+1)) (fun g hg => ltF_pw_lt (by omega) g hg) f ?_
    simp only [List.length_map]
    omega
  · have h2 : j + 3 ≤ (pwv (p ++ [j+1])).deg :=
      deg_pwv_mem (List.mem_append_right p (by simp))
    have h1 : p.length ≤ (pwv (p ++ List.replicate (n+1) j)).deg := by
      have h := deg_pwv_len (p ++ List.replicate (n+1) j)
      simp only [List.length_append, List.length_replicate] at h
      omega
    omega

/-- `P + ω^j·(n+1) < P + ω^j·(n+2)`. -/
private theorem lt_pwv_more (p : List Nat) (j n : Nat) :
    lt (pwv (p ++ List.replicate (n + 1) j)) (pwv (p ++ List.replicate (n + 2) j)) = true := by
  have hsplit : ∀ (q : List Nat), pwv (p ++ q) = ofList (p.map pw ++ q.map pw) := by
    intro q
    show ofList ((p ++ q).map pw) = _
    rw [List.map_append]
  refine lt_of_ltF (N := p.length + n + 2) (fun f hf => ?_) ?_
  · rw [hsplit, hsplit]
    rw [show (List.replicate (n+2) j).map pw
          = (List.replicate (n+1) j).map pw ++ pw j :: ([] : List Term) from by
          rw [show n + 2 = (n+1) + 1 from rfl, List.replicate_succ', List.map_append]
          rfl,
      ← List.append_assoc]
    refine ltF_ofList_prefix (p.map pw ++ (List.replicate (n+1) j).map pw) (pw j) [] ?_ ?_ f ?_
    · intro hc
      have hlen := congrArg List.length hc
      simp only [List.length_append, List.length_map, List.length_replicate,
        List.length_nil] at hlen
      omega
    · intro z hz
      rcases List.mem_append.mp hz with h | h
      · exact pw_map_isAP p z h
      · exact pw_map_isAP (List.replicate (n+1) j) z h
    · simp only [List.length_append, List.length_map, List.length_replicate]
      omega
  · have h1 : p.length + (n + 1) ≤ (pwv (p ++ List.replicate (n+1) j)).deg := by
      have h := deg_pwv_len (p ++ List.replicate (n+1) j)
      simp only [List.length_append, List.length_replicate] at h
      omega
    omega

/-! ### The certificate family below ω^ω

The prefix induction of the design note, verbatim: OUTER structural induction on
the level `k` (the length of the count vector), INNER `Nat` induction on the
coefficient `c`.  No `Acc`, no multiset ordering — `Evidence/WF.lean`'s `LexLt`
is not needed for this region.  The side condition `∀ x ∈ p, k ≤ x` is not used
by any step; it is kept because it is what confines the family to the DESCENDING
(hence genuine, `inT`) exponent lists, and dropping it would let the statement
range over junk terms `ofList` builds out of an ascending list. -/

private theorem cert_pre : ∀ (k : Nat) (v : List Nat), v.length = k → ∀ (p : List Nat),
    (∀ x ∈ p, k ≤ x) → Certified (pwM p) (pwv p) →
    Certified (pwM (p ++ expOf v)) (pwv (p ++ expOf v))
  | 0, v, hv, p, _, hp => by
    cases v with
    | cons a t => simp at hv
    | nil =>
      show Certified (pwM (p ++ [])) (pwv (p ++ []))
      rw [List.append_nil]
      exact hp
  | k + 1, v, hv, p, hpk, hp => by
    have IH : ∀ (v' : List Nat), v'.length = k → ∀ (p' : List Nat),
        (∀ x ∈ p', k ≤ x) → Certified (pwM p') (pwv p') →
        Certified (pwM (p' ++ expOf v')) (pwv (p' ++ expOf v')) :=
      fun v' hv' p' h1 h2 => cert_pre k v' hv' p' h1 h2
    cases v with
    | nil => simp at hv
    | cons c r =>
      have hr : r.length = k := by simp only [List.length_cons] at hv; omega
      have hpre : ∀ (c' : Nat), ∀ x ∈ p ++ List.replicate c' k, k ≤ x := by
        intro c' x hx
        rcases List.mem_append.mp hx with h | h
        · have := hpk x h; omega
        · have := List.eq_of_mem_replicate h; omega
      have step : ∀ (c' : Nat),
          Certified (pwM (p ++ List.replicate c' k)) (pwv (p ++ List.replicate c' k)) := by
        intro c'
        induction c' with
        | zero =>
          rw [List.replicate_zero, List.append_nil]
          exact hp
        | succ c'' ih =>
          rw [show p ++ List.replicate (c'' + 1) k = (p ++ List.replicate c'' k) ++ [k] from by
                rw [List.replicate_succ', ← List.append_assoc]]
          cases k with
          | zero =>
            rw [← plus_pwv_one]
            exact .succ (kind_pwM_succ _) (fun n => by rw [expand_pwM_succ]; exact ih)
          | succ j =>
            refine .lim
              (fun n => pwv ((p ++ List.replicate c'' (j + 1)) ++ List.replicate (n + 1) j))
              (kind_pwM_lim _ j) (fun n => ?_) (fun n => lt_pwv_step _ j n)
              (fun n => lt_pwv_more _ j n) (fun s hs h => cof_pre _ j s hs h)
            rw [expand_pwM_lim]
            have hcert := IH ((n + 1) :: List.replicate j 0) (by simp)
              (p ++ List.replicate c'' (j + 1)) (hpre c'') ih
            rw [expOf_step] at hcert
            exact hcert
      have hexp : expOf (c :: r) = List.replicate c k ++ expOf r := by
        show List.replicate c r.length ++ expOf r = _
        rw [hr]
      rw [hexp, ← List.append_assoc]
      exact IH r hr (p ++ List.replicate c k) (hpre c) (step c)

/-- **The whole CNF region below ω^ω, certified.**  Every count vector
    `cs = [c_k, …, c_0]` gets a derivation for `ω^k·c_k + … + ω^0·c_0`. -/
theorem cert_wv (cs : List Nat) : Certified (wvM cs) (wv cs) := by
  rw [wvM_eq, wv_eq]
  have h := cert_pre cs.length cs rfl [] (by simp) (show Certified (pwM []) (pwv []) from .zero)
  rw [List.nil_append] at h
  exact h

/-! ### ω^ω

The row `(0)(1)(2)`.  Its expansions are `(0)(1)…(1)` with `n+1` ones, i.e. the
count vectors `[1,0,…,0]`, so the whole fundamental sequence is inside the family
just certified; what is left is the classification below ω^ω. -/

/-- A sum of components each at most `ω^k` is below `ω^{k+1}`. -/
private theorem lt_pwv_pw : ∀ (e : List Nat) (k : Nat), (∀ x ∈ e, x ≤ k) →
    lt (pwv e) (pw (k + 1)) = true
  | [], k, _ => by
    refine lt_of_ltF (N := 1) (fun f hf => ltF_zero hf (pw_ne_zero (k+1))) ?_
    omega
  | [y], k, hy => by
    have hyk : y < k + 1 := by have := hy y (by simp); omega
    exact lt_pw_lt hyk
  | y :: z :: r, k, hy => by
    have hyk : y < k + 1 := by have := hy y (by simp); omega
    rw [pwv_cons (by simp)]
    refine lt_of_ltF (N := y + 4) (fun f hf => ?_) ?_
    · cases f with
      | zero => omega
      | succ g => exact ltF_add_to (pw_isAP (k+1)) (ltF_pw_lt hyk g (by omega))
    · have h1 : y + 2 ≤ (pw y).deg := deg_pw y
      show y + 4 ≤ 2 * ((1 + (pw y).deg + (pwv (z :: r)).deg) + (pw (k+1)).deg) + 8
      omega

/-- **L1 for ω^ω.**  Every term of 𝔗(M) below ω^ω is a sum of `ω^{eᵢ}` with all
    exponents bounded by one natural number. -/
private theorem below_pw_omega : ∀ (f : Nat) (s : Term), inT s = true →
    ltF f s (phi zero omega) = true → ∃ (e : List Nat) (k : Nat), (∀ x ∈ e, x ≤ k) ∧ s = pwv e
  | 0, s, _, h => by
    exact absurd h (by rw [show ltF 0 s (phi zero omega) = false from rfl]; simp)
  | f + 1, s, hs, h => by
    cases s with
    | zero => exact ⟨[], 0, by simp, rfl⟩
    | M =>
      rw [Evidence.StageA.ltF_M_phi] at h
      exact Bool.noConfusion h
    | omg a =>
      rw [show ltF (f+1) (omg a) (phi zero omega) = false from rfl] at h
      exact Bool.noConfusion h
    | psi q a =>
      have h2 : ((psi q a == zero) || (psi q a == omega) || ltF f (psi q a) zero
                 || ltF f (psi q a) omega) = true := h
      rw [show ((psi q a == zero) : Bool) = false from rfl,
        show ((psi q a == omega) : Bool) = false from rfl, ltF_lt_zero] at h2
      simp only [Bool.or_false, Bool.false_or] at h2
      obtain ⟨i, hi⟩ := below_omega f (psi q a) hs h2
      exact absurd hi (psi_ne_ofNat q a i)
    | Z a =>
      have h2 : ((Z a == zero) || (Z a == omega) || ltF f (Z a) zero
                 || ltF f (Z a) omega) = true := h
      rw [show ((Z a == zero) : Bool) = false from rfl,
        show ((Z a == omega) : Bool) = false from rfl, ltF_lt_zero] at h2
      simp only [Bool.or_false, Bool.false_or] at h2
      obtain ⟨i, hi⟩ := below_omega f (Z a) hs h2
      exact absurd hi (Z_ne_ofNat a i)
    | phi a b =>
      obtain ⟨ha, hb⟩ := inT_phi hs
      cases hxo : ((phi a b) == phi zero omega) with
      | true =>
        have heq : phi a b = phi zero omega := by simpa using hxo
        rw [heq, ltF_irrefl] at h
        exact Bool.noConfusion h
      | false =>
        have h2 : (if (a == zero) = true then ltF f b omega
                   else if ltF f a zero = true then ltF f b (phi zero omega)
                   else ((phi a b == omega) || ltF f (phi a b) omega)) = true := by
          rw [show ltF (f+1) (phi a b) (phi zero omega)
                = (if ((phi a b) == phi zero omega) = true then false
                   else if (a == zero) = true then ltF f b omega
                   else if ltF f a zero = true then ltF f b (phi zero omega)
                   else ((phi a b == omega) || ltF f (phi a b) omega) : Bool) from rfl,
              hxo] at h
          simpa using h
        cases haz : (a == zero) with
        | true =>
          have haz' : a = zero := by simpa using haz
          rw [haz] at h2
          simp only [if_true] at h2
          obtain ⟨i, hi⟩ := below_omega f b hb h2
          exact ⟨[i], i, by intro x hx; simp at hx; omega, by rw [haz', hi]; rfl⟩
        | false =>
          rw [haz] at h2
          simp only [Bool.false_eq_true, if_false, ltF_lt_zero] at h2
          have hphi : ∀ i, phi a b ≠ ofNat i := by
            intro i hcon
            rcases ofNat_cases i with hz | ho | ⟨j, hj⟩
            · rw [hz] at hcon; exact Term.noConfusion hcon
            · have hcon' : phi a b = phi zero zero := by rw [ho] at hcon; exact hcon
              injection hcon' with h1 _
              rw [h1] at haz
              simp at haz
            · rw [hj] at hcon; exact Term.noConfusion hcon
          cases hbe : ((phi a b == omega) : Bool) with
          | true =>
            have hcon0 : phi a b = omega := by simpa using hbe
            have hcon : phi a b = phi zero one := hcon0
            injection hcon with h1 _
            rw [h1] at haz
            simp at haz
          | false =>
            rw [hbe] at h2
            simp only [Bool.false_or] at h2
            obtain ⟨i, hi⟩ := below_omega f (phi a b) hs h2
            exact absurd hi (hphi i)
    | add a b =>
      obtain ⟨hap, ha, hb⟩ := inT_add hs
      have h2 : ltF f a (phi zero omega) = true := h
      obtain ⟨ea, k, hea, haa⟩ := below_pw_omega f a ha h2
      obtain ⟨y, rfl⟩ := pwv_isAP ea (by rw [← haa]; exact hap)
      have hyk : y ≤ k := hea y (by simp)
      have hay : a = pw y := haa
      have hhead : le ((toList b).headD zero) a = true := inT_add_head_le hs
      rw [hay] at hhead
      obtain ⟨eb, hbne, hbb, hbeq⟩ :=
        tail_pw y (fun k' hk' f' s' hs' h' => below_pw k' f' s' hs' h') b hb
          (inT_add_ne_zero hs) y (Nat.le_refl y) hhead
      refine ⟨y :: eb, k, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with h' | h'
        · omega
        · have := hbb x h'; omega
      · rw [hay, hbeq, pwv_cons hbne]

/-- `(0)(1)(2)[n] = (0)(1)…(1)` with `n+1` ones. -/
private theorem expand_omega_pow (n : Nat) :
    BMS.expand ([[0], [1], [2]] : Matrix) n = pwM [n + 1] := by
  have hexp := StageA.expand_oneRow (A := [0]) (B := [1]) (c := 2) (b0 := 1)
    (B' := []) rfl (by omega) (by intro x hx; simp at hx) (by omega) n
  show (BMS.expand? ([[0], [1], [2]] : Matrix) n).getD [] = _
  rw [show ([[0], [1], [2]] : Matrix) = StageA.oneRow ((([0] : List Nat) ++ [1]) ++ [2]) from rfl,
    hexp]
  show StageA.oneRow ([0] ++ StageA.repL [1] (n+1)) = pwM [n+1]
  rw [repL_single]
  show StageA.oneRow (0 :: List.replicate (n+1) 1) = StageA.oneRow (pwSeq [n+1])
  rw [pwSeq_single]
  rfl

/-- **ω^ω.**  `(0)(1)(2)` has value ω^ω. -/
theorem cert_omega_pow : Certified [[0], [1], [2]] (phi zero omega) := by
  refine .lim (fun n => pw (n + 1)) rfl (fun n => ?_) (fun n => ?_)
    (fun n => lt_pw_lt (by omega)) (fun s hs h => ?_)
  · rw [expand_omega_pow n]
    have hc := cert_wv (1 :: List.replicate (n + 1) 0)
    rw [wvM_eq, wv_eq, expOf_step] at hc
    exact hc
  · refine lt_of_ltF (N := n + 4) (fun f hf => ?_) ?_
    · cases f with
      | zero => omega
      | succ g => exact ltF_phi_same (ltF_ofNat_omega (n + 1) g (by omega))
    · have := deg_ofNat (n + 1)
      show n + 4 ≤ 2 * ((1 + (zero : Term).deg + (ofNat (n+1)).deg) + (phi zero omega).deg) + 8
      show n + 4 ≤ 2 * ((1 + 1 + (ofNat (n+1)).deg) + (phi zero omega).deg) + 8
      omega
  · obtain ⟨e, k, he, hse⟩ := below_pw_omega _ s hs h
    exact ⟨k, by rw [hse]; simp [TM.Term.le, lt_pwv_pw e k he]⟩

/-! ### The negative control for the ω^ω row

The same review exercise as §7, one level up.  `cert_omega_pow` uses
`fs' n = ω^(n+1)` — forced, those ARE the values of the expansions of `(0)(1)(2)`
— so an attempt to certify a COMPRESSED value for the same matrix has to
discharge the cofinality clause with the same `fs'`.  For ω^ω·2 it is refutable,
and the witness is the genuine term ω^ω. -/

private theorem ltF_omega_ofNat : ∀ (m f : Nat), ltF f omega (ofNat m) = false
  | 0, f => by rw [show (ofNat 0 : Term) = zero from rfl]; exact ltF_lt_zero f omega
  | 1, f => ltF_one_false f omega (by decide) (by intro hc; exact Term.noConfusion hc)
  | m + 2, f => by
    cases f with
    | zero => rfl
    | succ g =>
      rw [ofNat_shape m]
      show (if ((omega : Term) == add one (ofNat (m+1))) = true then false
            else (((omega : Term) == one) || ltF g omega one)) = false
      rw [show (((omega : Term) == add one (ofNat (m+1))) : Bool) = false from rfl,
        show (((omega : Term) == one) : Bool) = false from rfl]
      simp only [Bool.false_eq_true, if_false, Bool.false_or]
      exact ltF_one_false g omega (by decide) (by intro hc; exact Term.noConfusion hc)

private theorem omega_ne_ofNat : ∀ i, (omega : Term) ≠ ofNat i := by
  intro i hc
  rcases ofNat_cases i with h | h | ⟨j, h⟩ <;> rw [h] at hc
  · exact Term.noConfusion hc
  · injection hc with _ h2
    exact Term.noConfusion h2
  · exact Term.noConfusion hc

private theorem ltF_phi_zero_false {f : Nat} {x y : Term} (h : ltF f x y = false)
    (hne : (phi zero x == phi zero y) = false) : ltF (f + 1) (phi zero x) (phi zero y) = false := by
  show (if (phi zero x == phi zero y) = true then false else _) = false
  rw [hne]
  simp only [Bool.false_eq_true, if_false]
  show (if ((zero : Term) == zero) = true then ltF f x y else _) = false
  simp [h]

/-- No `ω^(n+1)` overtakes ω^ω. -/
private theorem le_omega_pow_pw (n : Nat) : le (phi zero omega) (pw (n + 1)) = false := by
  have hne : ((phi zero omega == phi zero (ofNat (n+1))) : Bool) = false := by
    cases hb : ((phi zero omega == phi zero (ofNat (n+1))) : Bool) with
    | true =>
      have heq : phi zero omega = phi zero (ofNat (n+1)) := by simpa using hb
      injection heq with _ h2
      exact absurd h2 (omega_ne_ofNat (n+1))
    | false => rfl
  have hlt : lt (phi zero omega) (pw (n + 1)) = false :=
    ltF_phi_zero_false (ltF_omega_ofNat (n+1) _) hne
  show ((phi zero omega == phi zero (ofNat (n+1)))
        || lt (phi zero omega) (phi zero (ofNat (n+1)))) = false
  rw [hne, show lt (phi zero omega) (phi zero (ofNat (n+1))) = false from hlt]
  rfl

/-- **The negative control for ω^ω, machine-checked.**  The cofinality clause
    that a certificate `Certified [[0],[1],[2]] (ω^ω·2)` would need — with the
    expansion values `fs' n = ω^(n+1)` of `cert_omega_pow`, which are forced by
    `cert_wv` — is FALSE: the term ω^ω of 𝔗(M) is below ω^ω·2 and is overtaken
    by no `fs' n`. -/
theorem neg_control_omega_pow_times_two :
    ¬ (∀ s, inT s = true → lt s (add (phi zero omega) (phi zero omega)) = true →
        ∃ n, le s (pw (n + 1)) = true) := by
  intro hcof
  obtain ⟨n, hn⟩ := hcof (phi zero omega) (by decide) (by decide)
  rw [le_omega_pow_pw n] at hn
  exact Bool.noConfusion hn

/-! ### Evidence for the ω^ω layer -/

-- the exponent-list layer agrees with the translation, like the count vector does
#guard Trans.oPr (pwM [3, 1]) == pwv [3, 1]
#guard Trans.oPr (pwM [0, 0, 0]) == pwv [0, 0, 0]
#guard pwM [1] == ([[0], [1]] : Matrix)
#guard pwv [1] == omega
-- the certified values really are terms of 𝔗(M) (the family stays inside `inT`)
#guard inT (wv [2, 1, 3]) = true
#guard inT (wv [1, 0, 0]) = true
#guard inT (phi zero omega) = true
-- the fundamental sequence of the new row, as `cert_omega_pow` uses it
#guard BMS.expand ([[0], [1], [2]] : Matrix) 3 == pwM [4]
#guard Trans.oPr (pwM [4]) == pw 4

/-! ## §5.8 Towards ω^(ω^ω): the second layer

The region below ω^(ω^ω) is the CNF sums whose EXPONENTS are the terms of §5.7:
`qv E` for a list `E` of level-1 exponent lists.  Everything below is the level-1
development read one level up, through `StageA.mkBlock`, which is the sequence
operation `s ↦ 0 :: s.map (·+1)` implementing `α ↦ ω^α` on the BMS side.

`PwLt` packages a level-1 comparison together with a fuel budget that survives
being wrapped in `ω^·`; it is the interface between the two layers, and the
reason it is needed is the one recorded at the head of §5.7 — there is no
fuel-monotonicity lemma, so a comparison must be carried as a statement about
ALL sufficiently large fuel, never as a single `lt … = true`. -/

/-- `ω^{α}` for a level-1 exponent list. -/
def qw (e : List Nat) : Term := phi zero (pwv e)

/-- The value of a list of level-1 exponents. -/
def qv (E : List (List Nat)) : Term := ofList (E.map qw)

/-- The one-row sequence of a list of level-1 exponents. -/
def qSeq (E : List (List Nat)) : List Nat := (E.map (fun e => StageA.mkBlock (pwSeq e))).flatten

/-- The matrix of a list of level-1 exponents. -/
def qM (E : List (List Nat)) : Matrix := StageA.oneRow (qSeq E)

-- the second layer agrees with the translation, as the first one does
#guard Trans.oPr (qM [[1], [0]]) == qv [[1], [0]]
#guard Trans.oPr (qM [[2, 0], [1]]) == qv [[2, 0], [1]]
#guard Trans.oPr (qM [[1, 1, 0], [0], []]) == qv [[1, 1, 0], [0], []]
#guard qM [[1]] == ([[0], [1], [2]] : Matrix)
#guard qv [[1]] == phi zero omega
-- the row (0)(1)(2)(3) is the LIMIT of this layer, not a member of it
#guard Trans.oPr ([[0], [1], [2], [3]] : Matrix) == phi zero (phi zero omega)
#guard BMS.expand ([[0], [1], [2], [3]] : Matrix) 2 == qM [[3]]
-- the three node kinds, and the two limit steps
#guard BMS.kind (qM [[1, 0], []]) == BMS.Kind.succ
#guard BMS.kind (qM [[1, 0]]) == BMS.Kind.lim
#guard BMS.kind (qM [[1, 1]]) == BMS.Kind.lim
#guard BMS.expand (qM [[1, 0]]) 2 == qM [[1], [1], [1]]
#guard BMS.expand (qM [[1, 1]]) 2 == qM [[1, 0, 0, 0]]
#guard BMS.expand (qM [[2], [1, 0]]) 2 == qM [[2], [1], [1], [1]]
#guard BMS.expand (qM [[2], []]) 3 == qM [[2]]

/-! ### Level-1 comparisons with a fuel budget that survives `ω^·` -/

/-- `pwv a < pwv b`, as a statement about every sufficiently large fuel. -/
def PwLt (a b : List Nat) : Prop :=
  ∀ f, (pwv a).deg + (pwv b).deg + 4 ≤ f → ltF f (pwv a) (pwv b) = true

private theorem lt_of_pwLt {a b : List Nat} (h : PwLt a b) : lt (pwv a) (pwv b) = true :=
  h _ (by show (pwv a).deg + (pwv b).deg + 4 ≤ 2 * ((pwv a).deg + (pwv b).deg) + 8; omega)

/-- The converse, by `Evidence.WF.ltF_mono`.  Before that lemma existed this
    direction was unavailable and every `PwLt` had to be BUILT in the ∀-fuel form
    (which is why `pwLt_head` / `pwLt_ext` exist); with it, a single `lt`
    computation suffices.  Kept as the documented entry point for anyone
    simplifying §5.7–§5.15 now that the import is in place. -/
theorem pwLt_of_lt {a b : List Nat} (h : lt (pwv a) (pwv b) = true) : PwLt a b := fun f hf =>
  Evidence.WF.ltF_mono
    (by show (pwv a).deg + (pwv b).deg ≤ 2 * ((pwv a).deg + (pwv b).deg) + 8; omega)
    (by omega) h

private theorem pwLt_zero {b : List Nat} (hb : b ≠ []) : PwLt [] b := by
  intro f hf
  exact ltF_zero (by have := deg_pos (pwv b); omega) (pwv_ne_zero b hb)

private theorem pwLt_ext (p : List Nat) (y : Nat) (r : List Nat) (hp : p ≠ []) :
    PwLt p (p ++ y :: r) := by
  intro f hf
  have hd : p.length ≤ (pwv p).deg := deg_pwv_len p
  show ltF f (ofList (p.map pw)) (ofList ((p ++ y :: r).map pw)) = true
  rw [List.map_append]
  refine ltF_ofList_prefix (p.map pw) (pw y) (r.map pw) (by
    intro hc
    have hl := congrArg List.length hc
    simp only [List.length_map, List.length_nil] at hl
    exact hp (by cases p with | nil => rfl | cons _ _ => simp at hl)) (pw_map_isAP p) f ?_
  simp only [List.length_map]
  omega

private theorem pwLt_head (p : List Nat) (x y : Nat) (r r' : List Nat) (hxy : x < y) :
    PwLt (p ++ x :: r) (p ++ y :: r') := by
  intro f hf
  have h1 : p.length + 1 ≤ (pwv (p ++ x :: r)).deg := by
    have h := deg_pwv_len (p ++ x :: r)
    simp only [List.length_append, List.length_cons] at h
    omega
  have h2 : x + 2 ≤ (pwv (p ++ x :: r)).deg :=
    deg_pwv_mem (List.mem_append_right p (by simp))
  have h3 : y + 2 ≤ (pwv (p ++ y :: r')).deg :=
    deg_pwv_mem (List.mem_append_right p (by simp))
  show ltF f (ofList ((p ++ x :: r).map pw)) (ofList ((p ++ y :: r').map pw)) = true
  rw [List.map_append, List.map_append]
  refine ltF_ofList_head (p.map pw) (pw x) (pw y) (r.map pw) (r'.map pw) (x + 3)
    (pw_isAP x) (pw_isAP y) (fun g hg => ltF_pw_lt hxy g hg) f ?_
  simp only [List.length_map]
  omega

/-- The bridge between the layers: a level-1 comparison, wrapped in `ω^·`. -/
private theorem ltF_qw_of_pwLt {a b : List Nat} (h : PwLt a b) :
    ∀ f, (qw a).deg + (qw b).deg + 4 ≤ f → ltF f (qw a) (qw b) = true := by
  intro f hf
  have hda : (qw a).deg = 2 + (pwv a).deg := by
    show 1 + (zero : Term).deg + (pwv a).deg = _
    show 1 + 1 + (pwv a).deg = _
    omega
  have hdb : (qw b).deg = 2 + (pwv b).deg := by
    show 1 + (zero : Term).deg + (pwv b).deg = _
    show 1 + 1 + (pwv b).deg = _
    omega
  cases f with
  | zero => have := deg_pos (qw a); omega
  | succ g => exact ltF_phi_same (h g (by omega))

private theorem lt_qw_of_pwLt {a b : List Nat} (h : PwLt a b) : lt (qw a) (qw b) = true :=
  ltF_qw_of_pwLt h _
    (by show (qw a).deg + (qw b).deg + 4 ≤ 2 * ((qw a).deg + (qw b).deg) + 8; omega)

/-! ### Shape lemmas for the second layer -/

private theorem qw_isAP (e : List Nat) : (qw e).isAP = true := rfl

private theorem qw_ne_zero (e : List Nat) : qw e ≠ zero := by intro hc; exact Term.noConfusion hc

private theorem qv_nil : qv [] = zero := rfl

private theorem qv_single (e : List Nat) : qv [e] = qw e := rfl

private theorem qv_cons {e : List Nat} {E : List (List Nat)} (h : E ≠ []) :
    qv (e :: E) = add (qw e) (qv E) := by
  show ofList (qw e :: E.map qw) = add (qw e) (ofList (E.map qw))
  refine ofList_cons ?_
  cases E with
  | nil => exact absurd rfl h
  | cons _ _ => simp

private theorem qw_map_isAP (E : List (List Nat)) : ∀ z ∈ E.map qw, z.isAP = true := by
  intro z hz
  obtain ⟨e, _, he⟩ := List.mem_map.mp hz
  rw [← he]; exact qw_isAP e

private theorem toList_qv (E : List (List Nat)) : toList (qv E) = E.map qw :=
  toList_ofList (qw_map_isAP E)

private theorem qv_isAP : ∀ (E : List (List Nat)), (qv E).isAP = true → ∃ e, E = [e]
  | [], h => by rw [show qv [] = zero from rfl] at h; exact absurd h (by simp [isAP])
  | [e], _ => ⟨e, rfl⟩
  | e :: e' :: r, h => by
    rw [qv_cons (by simp)] at h
    exact absurd h (by simp [isAP])

private theorem qv_ne_zero : ∀ (E : List (List Nat)), E ≠ [] → qv E ≠ zero
  | [], h => absurd rfl h
  | [e], _ => by rw [show qv [e] = qw e from rfl]; exact qw_ne_zero e
  | e :: e' :: r, _ => by rw [qv_cons (by simp)]; intro hc; exact Term.noConfusion hc

private theorem deg_qw (e : List Nat) : (pwv e).deg + 2 ≤ (qw e).deg := by
  show (pwv e).deg + 2 ≤ 1 + (zero : Term).deg + (pwv e).deg
  show (pwv e).deg + 2 ≤ 1 + 1 + (pwv e).deg
  omega

private theorem deg_qv_len (E : List (List Nat)) : E.length ≤ (qv E).deg := by
  have h := deg_ofList_len (E.map qw)
  simpa using h

private theorem deg_qv_mem {E : List (List Nat)} {e : List Nat} (h : e ∈ E) :
    (qw e).deg ≤ (qv E).deg :=
  deg_ofList_mem (E.map qw) (qw e) (List.mem_map_of_mem h)

private theorem le_one_qw : ∀ (e : List Nat), le one (qw e) = true
  | [] => rfl
  | k :: r => by
    have h : lt one (qw (k :: r)) = true := by
      refine lt_of_ltF (N := 2) (fun f hf => ?_) (by omega)
      cases f with
      | zero => omega
      | succ g =>
        exact ltF_phi_same (ltF_zero (by omega) (pwv_ne_zero (k :: r) (by simp)))
    show ((one == qw (k :: r)) || lt one (qw (k :: r))) = true
    rw [h]
    simp

private theorem filter_le_one_qw : ∀ (E : List (List Nat)),
    (E.map qw).filter (fun a => le one a) = E.map qw
  | [] => rfl
  | e :: r => by
    show (qw e :: r.map qw).filter _ = _
    rw [List.filter_cons_of_pos (le_one_qw e), filter_le_one_qw r]
    rfl

private theorem plus_qv_one (E : List (List Nat)) : plus (qv E) one = qv (E ++ [[]]) := by
  unfold plus
  rw [show toList (one : Term) = [one] from rfl]
  show ofList ((toList (qv E)).filter (fun a => le one a) ++ [one]) = qv (E ++ [[]])
  rw [toList_qv, filter_le_one_qw]
  show ofList (E.map qw ++ [qw []]) = ofList ((E ++ [[]]).map qw)
  rw [List.map_append]
  rfl

/-! ### The matrices of the second layer, and the three node kinds

`mkBlock s = 0 :: s.map (·+1)` is `α ↦ ω^α` on the BMS side, so the last block of
`qM (E ++ [e])` is the level-1 sequence of `e` shifted up by one.  Its last entry
therefore decides the node kind: `e = []` gives the column `(0)` (successor);
`e` ending in `0` gives `(1)`; `e` ending in `k+1` gives `(2)`. -/

private theorem mkBlock_append (s t : List Nat) :
    StageA.mkBlock (s ++ t) = StageA.mkBlock s ++ t.map (· + 1) := by
  show 0 :: (s ++ t).map (· + 1) = (0 :: s.map (· + 1)) ++ t.map (· + 1)
  rw [List.map_append]
  rfl

private theorem repL_map_succ (B : List Nat) : ∀ m,
    (StageA.repL B m).map (· + 1) = StageA.repL (B.map (· + 1)) m
  | 0 => rfl
  | m + 1 => by
    show (B ++ StageA.repL B m).map (· + 1) = B.map (· + 1) ++ StageA.repL (B.map (· + 1)) m
    rw [List.map_append, repL_map_succ B m]

private theorem blockOf_map_succ (k : Nat) :
    (blockOf k).map (· + 1) = 1 :: List.replicate k 2 := by
  show (0 :: (List.replicate k 1)).map (· + 1) = _
  rw [List.map_cons, List.map_replicate]

private theorem qSeq_append (E E' : List (List Nat)) :
    qSeq (E ++ E') = qSeq E ++ qSeq E' := by
  show ((E ++ E').map _).flatten = _
  rw [List.map_append, List.flatten_append]
  rfl

private theorem qSeq_single (e : List Nat) : qSeq [e] = StageA.mkBlock (pwSeq e) := by
  show ((List.map _ [e]).flatten) = _
  simp

private theorem qSeq_snoc (E : List (List Nat)) (e : List Nat) :
    qSeq (E ++ [e]) = qSeq E ++ StageA.mkBlock (pwSeq e) := by
  rw [qSeq_append, qSeq_single]

private theorem qSeq_replicate (e : List Nat) : ∀ c,
    qSeq (List.replicate c e) = StageA.repL (StageA.mkBlock (pwSeq e)) c
  | 0 => rfl
  | c + 1 => by
    rw [List.replicate_succ, show (e :: List.replicate c e) = [e] ++ List.replicate c e from rfl,
      qSeq_append, qSeq_single, qSeq_replicate e c]
    rfl

/-! #### Node 1: the exponent `0` — a successor -/

private theorem qM_snoc_zero (E : List (List Nat)) : qM (E ++ [[]]) = qM E ++ [[0]] := by
  show StageA.oneRow (qSeq (E ++ [[]])) = _
  rw [qSeq_snoc, show StageA.mkBlock (pwSeq ([] : List Nat)) = [0] from rfl,
    StageA.oneRow_append]
  rfl

private theorem kind_qM_succ (E : List (List Nat)) : BMS.kind (qM (E ++ [[]])) = .succ := by
  show (match (qM (E ++ [[]])).getLast? with
        | none => BMS.Kind.zero
        | some L => match BMS.lnz L with
          | none => BMS.Kind.succ
          | some _ => BMS.Kind.lim) = _
  rw [qM_snoc_zero, List.getLast?_concat]
  rfl

private theorem expand_qM_succ (E : List (List Nat)) (n : Nat) :
    BMS.expand (qM (E ++ [[]])) n = qM E := by
  have hL : (qM (E ++ [[]])).getLast? = some [0] := by
    rw [qM_snoc_zero]; exact List.getLast?_concat
  have hexp : BMS.expand? (qM (E ++ [[]])) n = some ((qM (E ++ [[]])).dropLast) := by
    simp only [BMS.expand?, hL, Option.bind_eq_bind, Option.bind_some,
      show BMS.lnz ([0] : BMS.Col) = none from rfl, Option.pure_def]
  show (BMS.expand? (qM (E ++ [[]])) n).getD [] = _
  rw [hexp]
  show (qM (E ++ [[]])).dropLast = qM E
  rw [qM_snoc_zero]
  exact List.dropLast_concat

/-! #### Node 2: a successor exponent `β+1` — a limit, expansions `ω^β·(n+1)` -/

private theorem qM_snoc_sexp (E : List (List Nat)) (e : List Nat) :
    qM (E ++ [e ++ [0]]) = StageA.oneRow ((qSeq E ++ StageA.mkBlock (pwSeq e)) ++ [1]) := by
  show StageA.oneRow (qSeq (E ++ [e ++ [0]])) = _
  rw [qSeq_snoc, pwSeq_snoc, show blockOf 0 = [0] from rfl, mkBlock_append,
    show ([0] : List Nat).map (· + 1) = [1] from rfl, List.append_assoc]

private theorem kind_qM_sexp (E : List (List Nat)) (e : List Nat) :
    BMS.kind (qM (E ++ [e ++ [0]])) = .lim := by
  have hL : (qM (E ++ [e ++ [0]])).getLast? = some [1] := by
    rw [qM_snoc_sexp, StageA.oneRow_append]
    exact List.getLast?_concat
  show (match (qM (E ++ [e ++ [0]])).getLast? with
        | none => BMS.Kind.zero
        | some L => match BMS.lnz L with
          | none => BMS.Kind.succ
          | some _ => BMS.Kind.lim) = _
  rw [hL]
  rfl

private theorem expand_qM_sexp (E : List (List Nat)) (e : List Nat) (n : Nat) :
    BMS.expand (qM (E ++ [e ++ [0]])) n = qM (E ++ List.replicate (n + 1) e) := by
  have hexp := StageA.expand_oneRow (A := qSeq E) (B := StageA.mkBlock (pwSeq e)) (c := 1)
    (b0 := 0) (B' := (pwSeq e).map (· + 1)) rfl (by omega)
    (by
      intro x hx
      obtain ⟨y, _, hy⟩ := List.mem_map.mp hx
      omega)
    (by omega) n
  show (BMS.expand? (qM (E ++ [e ++ [0]])) n).getD [] = _
  rw [qM_snoc_sexp, hexp]
  show StageA.oneRow (qSeq E ++ StageA.repL (StageA.mkBlock (pwSeq e)) (n+1))
      = qM (E ++ List.replicate (n+1) e)
  rw [← qSeq_replicate, ← qSeq_append]
  rfl

/-! #### Node 3: a limit exponent — a limit, expansions `ω^{β[n]}` (ONE copy) -/

private theorem qM_snoc_lexp (E : List (List Nat)) (e : List Nat) (k : Nat) :
    qM (E ++ [e ++ [k + 1]])
      = StageA.oneRow (((qSeq E ++ StageA.mkBlock (pwSeq e)) ++ (1 :: List.replicate k 2))
          ++ [2]) := by
  show StageA.oneRow (qSeq (E ++ [e ++ [k+1]])) = _
  rw [qSeq_snoc, pwSeq_snoc, blockOf_succ, ← List.append_assoc, mkBlock_append,
    show ([1] : List Nat).map (· + 1) = [2] from rfl, mkBlock_append, blockOf_map_succ]
  simp only [List.append_assoc]

private theorem kind_qM_lexp (E : List (List Nat)) (e : List Nat) (k : Nat) :
    BMS.kind (qM (E ++ [e ++ [k + 1]])) = .lim := by
  have hL : (qM (E ++ [e ++ [k+1]])).getLast? = some [2] := by
    rw [qM_snoc_lexp, StageA.oneRow_append]
    exact List.getLast?_concat
  show (match (qM (E ++ [e ++ [k+1]])).getLast? with
        | none => BMS.Kind.zero
        | some L => match BMS.lnz L with
          | none => BMS.Kind.succ
          | some _ => BMS.Kind.lim) = _
  rw [hL]
  rfl

private theorem expand_qM_lexp (E : List (List Nat)) (e : List Nat) (k n : Nat) :
    BMS.expand (qM (E ++ [e ++ [k + 1]])) n = qM (E ++ [e ++ List.replicate (n + 1) k]) := by
  have hexp := StageA.expand_oneRow (A := qSeq E ++ StageA.mkBlock (pwSeq e))
    (B := 1 :: List.replicate k 2) (c := 2) (b0 := 1) (B' := List.replicate k 2) rfl (by omega)
    (by intro x hx; have := List.eq_of_mem_replicate hx; omega) (by omega) n
  show (BMS.expand? (qM (E ++ [e ++ [k+1]])) n).getD [] = _
  rw [qM_snoc_lexp, hexp]
  show StageA.oneRow ((qSeq E ++ StageA.mkBlock (pwSeq e))
        ++ StageA.repL (1 :: List.replicate k 2) (n+1))
      = qM (E ++ [e ++ List.replicate (n+1) k])
  show _ = StageA.oneRow (qSeq (E ++ [e ++ List.replicate (n+1) k]))
  rw [qSeq_snoc, pwSeq_append, pwSeq_replicate, mkBlock_append, repL_map_succ, blockOf_map_succ]
  simp only [List.append_assoc]

/-! ### Status of the second layer, and the obstacle (2026-08-09, certificate lane)

WHAT IS PROVED ABOVE.  The representation, pinned by `#guard` against
`Trans.oPr` exactly as the count vector of §5.6 was; the interface `PwLt`
between the layers; all shape lemmas; and — the part that is usually the
expensive one — the COMPLETE node analysis:

    node                     kind      expansion
    E ++ [[]]                succ      E                       `expand_qM_succ`
    E ++ [e ++ [0]]          lim       E ++ (n+1) copies of e   `expand_qM_sexp`
    E ++ [e ++ [k+1]]        lim       E ++ [e ++ (n+1)·k]      `expand_qM_lexp`

so the BMS side of ω^(ω^ω) is finished and machine-checked.  What is missing is
the 𝔗(M) side: the classification of the terms below `qw b`, and with it the
cofinality clauses.

THE OBSTACLE, precisely.  At level 1 the classification recursion
(`below_pw`/`tail_pw`) peels the components of a sum and updates the bound to the
current head; to put the pieces back together it needs

    component ≤ head  and  head ≤ bound   ⟹   component ≤ bound.

At level 1 the bound is a NATURAL NUMBER (the exponent), so this step is `omega`
and costs nothing.  At level 2 the bound is a TERM (a level-1 value), and the
step is exactly TRANSITIVITY OF `lt` ON THE TERMS OF 𝔗(M) — the theorem this
repository does not have.  Every route around it that I tried reintroduces it:

  * carrying only the head's bound and re-deriving the rest from `inT` moves the
    transitivity into the pointwise comparison, where it reappears as
    "a_i ≤ a_1 and a_1 ≤ β ⟹ a_i ≤ β";
  * a bespoke lexicographic relation `LexNat` on `List Nat` with its own
    transitivity proof works, but then `PwLt ↔ LexNat` has to be proved in BOTH
    directions, and the hard direction IS the missing classification.

So ω^(ω^ω) is blocked on the SAME theorem as ε₀ and as `cert_sound`, namely
transitivity of `lt` on `inT` terms plus its inversion lemmas.  That is not a
guess: it is where this section stopped.

RESOLVED, AND THE ROW IS DONE (§5.9–§5.15 below, same day).  The obstacle turned
out not to need the general theory at all: on the ω^ω region the 𝔗(M) order
coincides with the LEXICOGRAPHIC order on exponent lists (`lexNat_of_pwLt` /
`pwLt_of_lexNat`), and that order is transitive structurally, so `pwLt_trans` /
`pwLe_trans` supply exactly the missing step.  With it, §5.10 classifies the
terms below `ω^{pwv b}`, §5.12 discharges the cofinality clause at both kinds of
limit node, §5.14 runs the certificate recursion, and §5.15 registers
`cert_omega_pow_pow : Certified [[0],[1],[2],[3]] (phi zero (phi zero omega))`.
The list of four items below is therefore a record of what was needed, not of
what is missing — all four were done, except that `below_lvl1` (item 1) is what
`below_pre` with `p ≠ []` (item 3) turned out to be needed for, and item 2's
`cof_pre_F` was not needed after all (`lexNat_of_ltF` re-derives a comparison at
any fuel, which is what the ∀-fuel form was wanted for).

The GENERAL transitivity of `lt` is still open and is still what ε₀ and
`cert_sound` need; its feasibility map is in `Evidence/WF.lean` §6, and its
prerequisite `ltF_stable` is proved there.

WHAT THE NEXT LANE NEEDS, on top of transitivity:

  1. `below_lvl1 : ∀ f b s, inT s = true → ltF f s (pwv b) = true → ∃ a, s = pwv a`
     — a standalone induction on the fuel, no lex data; needed to refute the
     `psi`/`Z` cases and to name the AP components at level 2.
  2. `cof_pre_F` — `cof_pre` restated with the conclusion `∀ g ≥ N, ltF g s … `
     instead of `le s … = true`.  The proof already produces the strong form
     (both of its branches are STRICT and fuel-uniform); only the statement and
     the two fuel bounds change.  It is needed because a level-2 comparison
     wraps a level-1 comparison in `ω^·`, which shifts the fuel.
  3. `below_pre` with `p ≠ []` added to its second disjunct, so that the branch
     can be instantiated at `t = []` (giving `s < pwv p`, not merely
     `s < pwv (p ++ t)` for nonempty `t`).  Every branch of the present proof
     already establishes it; only the statement changes.
  4. Then `below_q` / `tail_q` / `below_pre2` / `cof_pre2` mirror §5.7, and the
     certificate recursion is: OUTER well-founded recursion on the level-1 count
     vector under `Evidence.WF.LexLt` — whose two step lemmas `lexLt_succ_step`
     and `lexLt_lim_step` are EXACTLY the two limit steps in the table above, so
     `Evidence/WF.lean` finally earns its keep here — with an INNER structural
     recursion on the level-2 rest.  No `Acc` is needed at level 1; it is needed
     at level 2, and WF.lean is the reason it is available. -/

/-! ### §5.9 The level-1 order IS the lexicographic order, and it is TRANSITIVE

This is the step §5.8 stopped at, obtained without any of the general order
theory: on the terms `pwv e` of the ω^ω region the 𝔗(M) order coincides with the
lexicographic order on the exponent lists, and THAT order is transitive by a
three-line structural induction.  So `PwLt` is transitive, which is exactly the
"component ≤ head and head ≤ bound ⟹ component ≤ bound" step the level-2
classification needs.

Nothing here depends on `Evidence/WF.lean` §5: `ltF_ofList_head` and
`ltF_ofList_prefix` are already stated for all sufficiently large fuel, and the
converse direction consumes its hypothesis at whatever fuel it is given. -/

/-- The lexicographic order on exponent lists: a proper prefix is smaller
    (`nil`), otherwise the first difference decides (`head`), otherwise recurse
    (`tail`).  This is the shape `ltF_ofList_prefix` / `ltF_ofList_head` prove. -/
inductive LexNat : List Nat → List Nat → Prop
  | nil {y : Nat} {r : List Nat} : LexNat [] (y :: r)
  | head {x y : Nat} {r r' : List Nat} (h : x < y) : LexNat (x :: r) (y :: r')
  | tail {x : Nat} {r r' : List Nat} (h : LexNat r r') : LexNat (x :: r) (x :: r')

theorem lexNat_ne_nil : ∀ {a b : List Nat}, LexNat a b → b ≠ []
  | _, _, .nil => by simp
  | _, _, .head _ => by simp
  | _, _, .tail _ => by simp

/-- **Transitivity, on the nose.** -/
theorem lexNat_trans : ∀ {a b c : List Nat}, LexNat a b → LexNat b c → LexNat a c := by
  intro a b c h1
  induction h1 generalizing c with
  | nil =>
    intro h2
    cases h2 with
    | head _ => exact .nil
    | tail _ => exact .nil
  | @head x y r r' hxy =>
    intro h2
    cases h2 with
    | head hyz => exact .head (by omega)
    | tail _ => exact .head hxy
  | @tail x r r' _ ih =>
    intro h2
    cases h2 with
    | head hxz => exact .head hxz
    | tail h' => exact .tail (ih h')

/-! #### The two directions -/

private theorem ltF_pw_reduce (f x y : Nat) :
    ltF (f + 1) (pw x) (pw y)
      = (if (pw x == pw y) = true then false else ltF f (ofNat x) (ofNat y)) := rfl

private theorem ltF_pw_ge : ∀ (y x f : Nat), y ≤ x → ltF f (pw x) (pw y) = false
  | _, _, 0, _ => rfl
  | y, x, f + 1, h => by
    rw [ltF_pw_reduce]
    cases hbe : ((pw x == pw y) : Bool) with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, if_false]
      exact ltF_ofNat_ge y x f h

private theorem lt_of_ltF_pw {f x y : Nat} (h : ltF f (pw x) (pw y) = true) : x < y := by
  rcases Nat.lt_or_ge x y with hlt | hge
  · exact hlt
  · rw [ltF_pw_ge y x f hge] at h
    exact Bool.noConfusion h

private theorem pw_inj {x y : Nat} (h : pw x = pw y) : x = y := by
  have h1 : ofNat x = ofNat y := by injection h with _ h2
  exact ofNat_inj h1

/-- Lex-below implies below. -/
theorem pwLt_of_lexNat : ∀ {a b : List Nat}, LexNat a b → PwLt a b
  | _, _, .nil => pwLt_zero (by simp)
  | _, _, @LexNat.head x y r r' h => pwLt_head [] x y r r' h
  | _, _, @LexNat.tail x r r' h => by
    cases r with
    | nil =>
      cases r' with
      | nil => exact absurd rfl (lexNat_ne_nil h)
      | cons z r'' => exact pwLt_ext [x] z r'' (by simp)
    | cons w r₁ =>
      cases r' with
      | nil => exact absurd rfl (lexNat_ne_nil h)
      | cons z r₂ =>
        have IH := pwLt_of_lexNat h
        intro f hf
        have hda : pwv (x :: w :: r₁) = add (pw x) (pwv (w :: r₁)) := pwv_cons (by simp)
        have hdb : pwv (x :: z :: r₂) = add (pw x) (pwv (z :: r₂)) := pwv_cons (by simp)
        rw [hda, hdb] at hf ⊢
        have hd1 : (add (pw x) (pwv (w :: r₁))).deg = 1 + (pw x).deg + (pwv (w :: r₁)).deg := rfl
        have hd2 : (add (pw x) (pwv (z :: r₂))).deg = 1 + (pw x).deg + (pwv (z :: r₂)).deg := rfl
        have hdp := deg_pw x
        cases f with
        | zero => omega
        | succ g => exact ltF_add_same (IH g (by omega))

/-- Below implies lex-below: the converse, consuming the fuel it is given. -/
theorem lexNat_of_ltF : ∀ (f : Nat) (a b : List Nat), ltF f (pwv a) (pwv b) = true → LexNat a b
  | 0, a, b, h => by
    exact absurd h (by rw [show ltF 0 (pwv a) (pwv b) = false from rfl]; simp)
  | f + 1, a, b, h => by
    cases a with
    | nil =>
      cases b with
      | nil =>
        rw [show pwv ([] : List Nat) = zero from rfl, ltF_irrefl] at h
        exact Bool.noConfusion h
      | cons y r => exact .nil
    | cons x r =>
      cases b with
      | nil =>
        rw [show pwv ([] : List Nat) = zero from rfl, ltF_lt_zero] at h
        exact Bool.noConfusion h
      | cons y r' =>
        cases r with
        | nil =>
          cases r' with
          | nil =>
            rw [show pwv [x] = pw x from rfl, show pwv [y] = pw y from rfl] at h
            exact .head (lt_of_ltF_pw h)
          | cons z r₂ =>
            rw [show pwv [x] = pw x from rfl, pwv_cons (show (z :: r₂) ≠ [] by simp)] at h
            have h2 : ((pw x == pw y) || ltF f (pw x) (pw y)) = true := h
            cases hbe : ((pw x == pw y) : Bool) with
            | true =>
              have hxy : x = y := pw_inj (by simpa using hbe)
              rw [hxy]
              exact .tail .nil
            | false =>
              rw [hbe] at h2
              simp only [Bool.false_or] at h2
              exact .head (lt_of_ltF_pw h2)
        | cons w r₁ =>
          cases r' with
          | nil =>
            rw [pwv_cons (show (w :: r₁) ≠ [] by simp), show pwv [y] = pw y from rfl] at h
            have h2 : ltF f (pw x) (pw y) = true := h
            exact .head (lt_of_ltF_pw h2)
          | cons z r₂ =>
            rw [pwv_cons (show (w :: r₁) ≠ [] by simp),
              pwv_cons (show (z :: r₂) ≠ [] by simp)] at h
            cases hbe : ((add (pw x) (pwv (w :: r₁)) == add (pw y) (pwv (z :: r₂))) : Bool) with
            | true =>
              have heq : add (pw x) (pwv (w :: r₁)) = add (pw y) (pwv (z :: r₂)) := by
                simpa using hbe
              rw [heq, ltF_irrefl] at h
              exact Bool.noConfusion h
            | false =>
              have h2 : (if (pw x == pw y) = true then ltF f (pwv (w :: r₁)) (pwv (z :: r₂))
                         else ltF f (pw x) (pw y)) = true := by
                rw [show ltF (f+1) (add (pw x) (pwv (w :: r₁))) (add (pw y) (pwv (z :: r₂)))
                      = (if (add (pw x) (pwv (w :: r₁)) == add (pw y) (pwv (z :: r₂))) = true
                         then false
                         else if (pw x == pw y) = true
                              then ltF f (pwv (w :: r₁)) (pwv (z :: r₂))
                              else ltF f (pw x) (pw y) : Bool) from rfl, hbe] at h
                simpa using h
              cases hxy : ((pw x == pw y) : Bool) with
              | true =>
                rw [hxy] at h2
                simp only [if_true] at h2
                have hx : x = y := pw_inj (by simpa using hxy)
                rw [hx]
                exact .tail (lexNat_of_ltF f (w :: r₁) (z :: r₂) h2)
              | false =>
                rw [hxy] at h2
                simp only [Bool.false_eq_true, if_false] at h2
                exact .head (lt_of_ltF_pw h2)

theorem lexNat_of_pwLt {a b : List Nat} (h : PwLt a b) : LexNat a b :=
  lexNat_of_ltF _ a b (h _ (Nat.le_refl _))

/-- **Transitivity of the level-1 order.**  The step the level-2 classification
    of §5.8 is missing, and the reason the ω^ω layer needed no such theorem: at
    level 1 the bound is a natural number and the step is `omega`. -/
theorem pwLt_trans {a b c : List Nat} (h1 : PwLt a b) (h2 : PwLt b c) : PwLt a c :=
  pwLt_of_lexNat (lexNat_trans (lexNat_of_pwLt h1) (lexNat_of_pwLt h2))

/-- The `≤` form, which is what the classification actually consumes. -/
def PwLe (a b : List Nat) : Prop := pwv a = pwv b ∨ PwLt a b

theorem pwLe_trans {a b c : List Nat} (h1 : PwLe a b) (h2 : PwLe b c) : PwLe a c := by
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exact Or.inl (h1.trans h2)
    · refine Or.inr (fun f hf => ?_)
      rw [h1]
      exact h2 f (by rw [h1] at hf; exact hf)
  · rcases h2 with h2 | h2
    · refine Or.inr (fun f hf => ?_)
      rw [← h2]
      exact h1 f (by rw [← h2] at hf; exact hf)
    · exact Or.inr (pwLt_trans h1 h2)

/-! ### §5.10 Classification below `ω^{pwv b}` — the level-2 analysis

`lexNat_of_ltF` is what makes this possible without a fuel-monotonicity lemma:
it turns a comparison established at ONE fuel into the fuel-free `LexNat`, from
which `pwLt_of_lexNat` re-derives the comparison at any fuel.  For terms of the
ω^ω region it does exactly the job `Evidence.WF.ltF_mono` does in general. -/

/-- Everything of 𝔗(M) below a level-1 value is a level-1 value. -/
private theorem below_lvl1 : ∀ (f : Nat) (b : List Nat) (s : Term), inT s = true →
    ltF f s (pwv b) = true → ∃ a, s = pwv a
  | 0, b, s, _, h => by
    exact absurd h (by rw [show ltF 0 s (pwv b) = false from rfl]; simp)
  | f + 1, b, s, hs, h => by
    cases b with
    | nil =>
      rw [show pwv ([] : List Nat) = zero from rfl, ltF_lt_zero] at h
      exact Bool.noConfusion h
    | cons y r =>
      cases r with
      | nil =>
        obtain ⟨e, _, he⟩ := below_pw y (f + 1) s hs h
        exact ⟨e, he⟩
      | cons z r' =>
        rw [pwv_cons (show (z :: r') ≠ [] by simp)] at h
        have key : ∀ (x : Term), inT x = true →
            ((x == pw y) || ltF f x (pw y)) = true → ∃ a, x = pwv a := by
          intro x hx hh
          cases hxo : (x == pw y) with
          | true => exact ⟨[y], by simpa using hxo⟩
          | false =>
            rw [hxo] at hh
            simp only [Bool.false_or] at hh
            obtain ⟨e, _, he⟩ := below_pw y f x hx hh
            exact ⟨e, he⟩
        cases s with
        | zero => exact ⟨[], rfl⟩
        | M => exact key M hs h
        | omg a => exact key (omg a) hs h
        | phi a c => exact key (phi a c) hs h
        | psi a c => exact key (psi a c) hs h
        | Z a => exact key (Z a) hs h
        | add a c =>
          obtain ⟨hap, ha, hc⟩ := inT_add hs
          cases hxo : ((add a c) == add (pw y) (pwv (z :: r'))) with
          | true =>
            refine ⟨y :: z :: r', ?_⟩
            rw [show add a c = add (pw y) (pwv (z :: r')) from by simpa using hxo,
              pwv_cons (show (z :: r') ≠ [] by simp)]
          | false =>
            have h2 : (if (a == pw y) = true then ltF f c (pwv (z :: r'))
                       else ltF f a (pw y)) = true := by
              rw [show ltF (f+1) (add a c) (add (pw y) (pwv (z :: r')))
                    = (if ((add a c) == add (pw y) (pwv (z :: r'))) = true then false
                       else if (a == pw y) = true then ltF f c (pwv (z :: r'))
                       else ltF f a (pw y) : Bool) from rfl, hxo] at h
              simpa using h
            cases haz : (a == pw y) with
            | true =>
              have hay : a = pw y := by simpa using haz
              rw [haz] at h2
              simp only [if_true] at h2
              obtain ⟨ec, hec⟩ := below_lvl1 f (z :: r') c hc h2
              have hne : ec ≠ [] := by
                intro hc0
                exact inT_add_ne_zero hs (by rw [hec, hc0]; rfl)
              exact ⟨y :: ec, by rw [hay, hec, pwv_cons hne]⟩
            | false =>
              rw [haz] at h2
              simp only [Bool.false_eq_true, if_false] at h2
              obtain ⟨ea, hea, haa⟩ := below_pw y f a ha h2
              obtain ⟨i, rfl⟩ := pwv_isAP ea (by rw [← haa]; exact hap)
              have hai : a = pw i := haa
              have hhead : le ((toList c).headD zero) a = true := inT_add_head_le hs
              rw [hai] at hhead
              obtain ⟨ec, hne, _, hec⟩ :=
                tail_pw i (fun k' hk' f' s' hs' h' => below_pw k' f' s' hs' h') c hc
                  (inT_add_ne_zero hs) i (Nat.le_refl i) hhead
              exact ⟨i :: ec, by rw [hai, hec, pwv_cons hne]⟩

private theorem pwv_ne_psi (a c : Term) : ∀ (b : List Nat), psi a c ≠ pwv b
  | [] => by intro hc0; exact Term.noConfusion hc0
  | [k] => by intro hc0; exact Term.noConfusion hc0
  | k :: k' :: r => by rw [pwv_cons (by simp)]; intro hc0; exact Term.noConfusion hc0

private theorem pwv_ne_Z (a : Term) : ∀ (b : List Nat), Z a ≠ pwv b
  | [] => by intro hc0; exact Term.noConfusion hc0
  | [k] => by intro hc0; exact Term.noConfusion hc0
  | k :: k' :: r => by rw [pwv_cons (by simp)]; intro hc0; exact Term.noConfusion hc0

private theorem beq_pwv_false_of_ne {x : Term} {b : List Nat} (h : x ≠ pwv b) :
    (x == pwv b) = false := by
  cases hb : (x == pwv b) with
  | true => exact absurd (by simpa using hb) h
  | false => rfl

private theorem pwv_eq_phi : ∀ (b : List Nat) (c d : Term), pwv b = phi c d → c = zero
  | [], c, d, h => by exact Term.noConfusion h
  | [k], c, d, h => by
    have h' : phi zero (ofNat k) = phi c d := h
    injection h' with h1 _
    exact h1.symm
  | k :: k' :: r, c, d, h => by
    rw [pwv_cons (by simp)] at h
    exact Term.noConfusion h

private theorem pwLt_of_pwLe_pwLt {a b c : List Nat} (h1 : PwLe a b) (h2 : PwLt b c) :
    PwLt a c := by
  rcases h1 with h1 | h1
  · intro f hf
    rw [h1]
    exact h2 f (by rw [h1] at hf; exact hf)
  · exact pwLt_trans h1 h2

/-- An additively principal term below `ω^{pwv b}` is an `ω^{pwv e}` with
    `e` lex-below `b`.  No recursion: this is where `below_lvl1` and
    `lexNat_of_ltF` do the work. -/
private theorem ap_below_qw : ∀ (f : Nat) (b : List Nat) (x : Term), inT x = true →
    x.isAP = true → ltF f x (qw b) = true → ∃ e, PwLt e b ∧ x = qw e
  | 0, b, x, _, _, h => by
    exact absurd h (by rw [show ltF 0 x (qw b) = false from rfl]; simp)
  | f + 1, b, x, hx, hap, h => by
    cases x with
    | zero => exact absurd hap (by simp [isAP])
    | add _ _ => exact absurd hap (by simp [isAP])
    | M =>
      rw [show ltF (f+1) M (qw b) = false from Evidence.StageA.ltF_M_phi (f+1) zero (pwv b)] at h
      exact Bool.noConfusion h
    | omg a =>
      rw [show ltF (f+1) (omg a) (qw b) = false from ltF_omg_phi (f+1) a zero (pwv b)] at h
      exact Bool.noConfusion h
    | psi p a =>
      have h2 : ((psi p a == zero) || (psi p a == pwv b) || ltF f (psi p a) zero
                 || ltF f (psi p a) (pwv b)) = true := h
      rw [show ((psi p a == zero) : Bool) = false from rfl,
        beq_pwv_false_of_ne (pwv_ne_psi p a b), ltF_lt_zero] at h2
      simp only [Bool.or_false, Bool.false_or] at h2
      obtain ⟨a', ha'⟩ := below_lvl1 f b (psi p a) hx h2
      exact absurd ha' (pwv_ne_psi p a a')
    | Z a =>
      have h2 : ((Z a == zero) || (Z a == pwv b) || ltF f (Z a) zero
                 || ltF f (Z a) (pwv b)) = true := h
      rw [show ((Z a == zero) : Bool) = false from rfl,
        beq_pwv_false_of_ne (pwv_ne_Z a b), ltF_lt_zero] at h2
      simp only [Bool.or_false, Bool.false_or] at h2
      obtain ⟨a', ha'⟩ := below_lvl1 f b (Z a) hx h2
      exact absurd ha' (pwv_ne_Z a a')
    | phi c d =>
      obtain ⟨hc, hd⟩ := inT_phi hx
      cases hxo : ((phi c d) == qw b) with
      | true =>
        have heq : phi c d = qw b := by simpa using hxo
        rw [heq, ltF_irrefl] at h
        exact Bool.noConfusion h
      | false =>
        have h2 : (if (c == zero) = true then ltF f d (pwv b)
                   else if ltF f c zero = true then ltF f d (phi zero (pwv b))
                   else ((phi c d == pwv b) || ltF f (phi c d) (pwv b))) = true := by
          rw [show ltF (f+1) (phi c d) (qw b)
                = (if ((phi c d) == qw b) = true then false
                   else if (c == zero) = true then ltF f d (pwv b)
                   else if ltF f c zero = true then ltF f d (phi zero (pwv b))
                   else ((phi c d == pwv b) || ltF f (phi c d) (pwv b)) : Bool) from rfl,
              hxo] at h
          simpa using h
        cases hcz : (c == zero) with
        | true =>
          have hcz' : c = zero := by simpa using hcz
          rw [hcz] at h2
          simp only [if_true] at h2
          obtain ⟨a', ha'⟩ := below_lvl1 f b d hd h2
          rw [ha'] at h2
          exact ⟨a', pwLt_of_lexNat (lexNat_of_ltF f a' b h2), by rw [hcz', ha']; rfl⟩
        | false =>
          rw [hcz] at h2
          simp only [Bool.false_eq_true, if_false, ltF_lt_zero] at h2
          have hcontra : ∀ (a' : List Nat), phi c d ≠ pwv a' := by
            intro a' hc0
            have := pwv_eq_phi a' c d hc0.symm
            rw [this] at hcz
            simp at hcz
          cases hbe : ((phi c d == pwv b) : Bool) with
          | true => exact absurd (by simpa using hbe) (hcontra b)
          | false =>
            rw [hbe] at h2
            simp only [Bool.false_or] at h2
            obtain ⟨a', ha'⟩ := below_lvl1 f b (phi c d) hx h2
            exact absurd ha' (hcontra a')

private theorem qkey (x : Term) (hx : inT x = true) (hap : x.isAP = true) (b : List Nat)
    (hle : le x (qw b) = true) : ∃ F, F ≠ [] ∧ (∀ e ∈ F, PwLe e b) ∧ x = qv F := by
  cases hco : (x == qw b) with
  | true =>
    exact ⟨[b], by simp, by intro e he; simp at he; rw [he]; exact Or.inl rfl,
      by simpa using hco⟩
  | false =>
    have hlt : lt x (qw b) = true := by
      simp only [TM.Term.le, hco, Bool.false_or] at hle
      exact hle
    obtain ⟨e, he, hxe⟩ := ap_below_qw _ b x hx hap hlt
    exact ⟨[e], by simp, by intro y hy; simp at hy; rw [hy]; exact Or.inr he, hxe⟩

/-- The tail of a sum whose head is at most `ω^{pwv b}`: the level-2 companion
    of `tail_pw`.  `pwLe_trans` — i.e. transitivity of the level-1 order — is
    what makes the bound survive being lowered at each component. -/
private theorem tail_q : ∀ (c : Term), inT c = true → c ≠ zero → ∀ (b : List Nat),
    le ((toList c).headD zero) (qw b) = true →
    ∃ F, F ≠ [] ∧ (∀ e ∈ F, PwLe e b) ∧ c = qv F
  | zero, _, hne, _, _ => absurd rfl hne
  | M, h, _, b, hle => qkey M h rfl b hle
  | omg a, h, _, b, hle => qkey (omg a) h rfl b hle
  | phi a d, h, _, b, hle => qkey (phi a d) h rfl b hle
  | psi a d, h, _, b, hle => qkey (psi a d) h rfl b hle
  | Z a, h, _, b, hle => qkey (Z a) h rfl b hle
  | add d e, h, _, b, hle => by
    obtain ⟨hap, hd, he⟩ := inT_add h
    rw [show (toList (add d e)).headD zero = d from rfl] at hle
    have hene : e ≠ zero := inT_add_ne_zero h
    have hehead : le ((toList e).headD zero) d = true := inT_add_head_le h
    cases hco : (d == qw b) with
    | true =>
      have hdb : d = qw b := by simpa using hco
      rw [hdb] at hehead
      obtain ⟨F, hF, hFb, hFe⟩ := tail_q e he hene b hehead
      refine ⟨b :: F, by simp, ?_, by rw [hdb, hFe, qv_cons hF]⟩
      intro y hy
      rcases List.mem_cons.mp hy with h' | h'
      · rw [h']; exact Or.inl rfl
      · exact hFb y h'
    | false =>
      have hlt : lt d (qw b) = true := by
        simp only [TM.Term.le, hco, Bool.false_or] at hle
        exact hle
      obtain ⟨b'', hb'', hdb⟩ := ap_below_qw _ b d hd hap hlt
      rw [hdb] at hehead
      obtain ⟨F, hF, hFb, hFe⟩ := tail_q e he hene b'' hehead
      refine ⟨b'' :: F, by simp, ?_, by rw [hdb, hFe, qv_cons hF]⟩
      intro y hy
      rcases List.mem_cons.mp hy with h' | h'
      · rw [h']; exact Or.inr hb''
      · exact pwLe_trans (hFb y h') (Or.inr hb'')

/-- **L2 at bound `b`.**  Every term of 𝔗(M) below `ω^{pwv b}` is a formal sum of
    `ω^{pwv eᵢ}` with every exponent lex-below `b`. -/
private theorem below_q (f : Nat) (b : List Nat) (s : Term) (hs : inT s = true)
    (h : ltF f s (qw b) = true) : ∃ F, (∀ e ∈ F, PwLt e b) ∧ s = qv F := by
  cases s with
  | zero => exact ⟨[], by simp, rfl⟩
  | M =>
    obtain ⟨e, he, hxe⟩ := ap_below_qw f b M hs rfl h
    exact ⟨[e], by intro y hy; simp at hy; rw [hy]; exact he, hxe⟩
  | omg a =>
    obtain ⟨e, he, hxe⟩ := ap_below_qw f b (omg a) hs rfl h
    exact ⟨[e], by intro y hy; simp at hy; rw [hy]; exact he, hxe⟩
  | phi a d =>
    obtain ⟨e, he, hxe⟩ := ap_below_qw f b (phi a d) hs rfl h
    exact ⟨[e], by intro y hy; simp at hy; rw [hy]; exact he, hxe⟩
  | psi a d =>
    obtain ⟨e, he, hxe⟩ := ap_below_qw f b (psi a d) hs rfl h
    exact ⟨[e], by intro y hy; simp at hy; rw [hy]; exact he, hxe⟩
  | Z a =>
    obtain ⟨e, he, hxe⟩ := ap_below_qw f b (Z a) hs rfl h
    exact ⟨[e], by intro y hy; simp at hy; rw [hy]; exact he, hxe⟩
  | add a c =>
    obtain ⟨hap, ha, hc⟩ := inT_add hs
    cases f with
    | zero => exact absurd h (by rw [show ltF 0 (add a c) (qw b) = false from rfl]; simp)
    | succ f' =>
      have h2 : ltF f' a (qw b) = true := h
      obtain ⟨b'', hb'', hab⟩ := ap_below_qw f' b a ha hap h2
      have hhead : le ((toList c).headD zero) a = true := inT_add_head_le hs
      rw [hab] at hhead
      obtain ⟨F, hF, hFb, hFc⟩ := tail_q c hc (inT_add_ne_zero hs) b'' hhead
      refine ⟨b'' :: F, ?_, by rw [hab, hFc, qv_cons hF]⟩
      intro y hy
      rcases List.mem_cons.mp hy with h' | h'
      · rw [h']; exact hb''
      · exact pwLt_of_pwLe_pwLt (hFb y h') hb''

/-! ### §5.11 Level-2 comparisons -/

/-- `qv A < qv B`, with a fuel budget that fits under the default fuel. -/
def QLt (A B : List (List Nat)) : Prop :=
  ∀ f, 2 * ((qv A).deg + (qv B).deg) + 4 ≤ f → ltF f (qv A) (qv B) = true

private theorem lt_of_qLt {A B : List (List Nat)} (h : QLt A B) : lt (qv A) (qv B) = true :=
  h _ (by show 2 * ((qv A).deg + (qv B).deg) + 4 ≤ 2 * ((qv A).deg + (qv B).deg) + 8; omega)

private theorem qLt_zero {B : List (List Nat)} (hB : B ≠ []) : QLt [] B := by
  intro f hf
  have := deg_pos (qv B)
  exact ltF_zero (by omega) (qv_ne_zero B hB)

private theorem qLt_ext (P : List (List Nat)) (y : List Nat) (R : List (List Nat))
    (hP : P ≠ []) : QLt P (P ++ y :: R) := by
  intro f hf
  have hd : P.length ≤ (qv P).deg := deg_qv_len P
  show ltF f (ofList (P.map qw)) (ofList ((P ++ y :: R).map qw)) = true
  rw [List.map_append]
  refine ltF_ofList_prefix (P.map qw) (qw y) (R.map qw) (by
    intro hc
    have hl := congrArg List.length hc
    simp only [List.length_map, List.length_nil] at hl
    exact hP (by cases P with | nil => rfl | cons _ _ => simp at hl)) (qw_map_isAP P) f ?_
  simp only [List.length_map]
  omega

private theorem qLt_head (P : List (List Nat)) (x y : List Nat) (R R' : List (List Nat))
    (hxy : PwLt x y) : QLt (P ++ x :: R) (P ++ y :: R') := by
  intro f hf
  have h1 : P.length + 1 ≤ (qv (P ++ x :: R)).deg := by
    have h := deg_qv_len (P ++ x :: R)
    simp only [List.length_append, List.length_cons] at h
    omega
  have h2 : (qw x).deg ≤ (qv (P ++ x :: R)).deg :=
    deg_qv_mem (List.mem_append_right P (by simp))
  have h3 : (qw y).deg ≤ (qv (P ++ y :: R')).deg :=
    deg_qv_mem (List.mem_append_right P (by simp))
  show ltF f (ofList ((P ++ x :: R).map qw)) (ofList ((P ++ y :: R').map qw)) = true
  rw [List.map_append, List.map_append]
  refine ltF_ofList_head (P.map qw) (qw x) (qw y) (R.map qw) (R'.map qw)
    ((qw x).deg + (qw y).deg + 4) (qw_isAP x) (qw_isAP y)
    (fun g hg => ltF_qw_of_pwLt hxy g hg) f ?_
  simp only [List.length_map]
  omega

/-- Two exponent lists with the same value give the same `ω^·`. -/
private theorem qw_congr {x e : List Nat} (h : pwv x = pwv e) : qw x = qw e := by
  show phi zero (pwv x) = phi zero (pwv e)
  rw [h]

/-- **The level-2 pointwise bound.**  A sum of `|F|` components each at most
    `ω^{pwv e}` is strictly below `ω^{pwv e}·(|F|+1)`, under any prefix. -/
private theorem lt_qv_repl : ∀ (F : List (List Nat)) (e : List Nat), (∀ x ∈ F, PwLe x e) →
    ∀ (P : List Term), (∀ z ∈ P, z.isAP = true) → ∀ f,
    2 * ((ofList (P ++ F.map qw)).deg
        + (ofList (P ++ (List.replicate (F.length + 1) e).map qw)).deg) + 4 ≤ f →
    ltF f (ofList (P ++ F.map qw))
      (ofList (P ++ (List.replicate (F.length + 1) e).map qw)) = true
  | [], e, _, P, hP, f, hf => by
    cases P with
    | nil =>
      show ltF f (ofList ([] : List Term)) (ofList [qw e]) = true
      refine ltF_zero ?_ (qw_ne_zero e)
      have := deg_pos (qw e)
      simp only [List.nil_append] at hf
      omega
    | cons z Q =>
      show ltF f (ofList ((z :: Q) ++ ([] : List Term))) (ofList ((z :: Q) ++ [qw e])) = true
      rw [List.append_nil]
      have hd : (z :: Q).length ≤ (ofList (z :: Q)).deg := deg_ofList_len (z :: Q)
      refine ltF_ofList_prefix (z :: Q) (qw e) [] (by simp) hP f ?_
      simp only [List.map_nil, List.append_nil, List.length_nil] at hf
      omega
  | x :: R, e, hF, P, hP, f, hf => by
    have hrhs : (List.replicate ((x :: R).length + 1) e).map qw
        = qw e :: (List.replicate (R.length + 1) e).map qw := by
      show (List.replicate (R.length + 1 + 1) e).map qw = _
      rw [List.replicate_succ]
      rfl
    rw [hrhs] at hf ⊢
    have h1 : P.length + 1 ≤ (ofList (P ++ (x :: R).map qw)).deg := by
      have h := deg_ofList_len (P ++ (x :: R).map qw)
      simp only [List.length_append, List.length_map, List.length_cons] at h
      omega
    have h2 : (qw x).deg ≤ (ofList (P ++ (x :: R).map qw)).deg :=
      deg_ofList_mem _ _ (List.mem_append_right P (by simp))
    have h3 : (qw e).deg
        ≤ (ofList (P ++ qw e :: (List.replicate (R.length + 1) e).map qw)).deg :=
      deg_ofList_mem _ _ (List.mem_append_right P (by simp))
    rcases hF x (by simp) with heq | hlt
    · have hx : qw x = qw e := qw_congr heq
      rw [show ((x :: R).map qw) = qw x :: R.map qw from rfl, hx] at hf ⊢
      have hIH := lt_qv_repl R e (fun y hy => hF y (by simp [hy])) (P ++ [qw e])
        (by
          intro z hz
          rcases List.mem_append.mp hz with h | h
          · exact hP z h
          · have hz' : z = qw e := by simpa using h
            rw [hz']; exact qw_isAP e)
        f (by rw [List.append_assoc, List.append_assoc]; exact hf)
      rw [List.append_assoc, List.append_assoc] at hIH
      exact hIH
    · show ltF f (ofList (P ++ qw x :: R.map qw))
        (ofList (P ++ qw e :: (List.replicate (R.length + 1) e).map qw)) = true
      refine ltF_ofList_head P (qw x) (qw e) (R.map qw)
        ((List.replicate (R.length + 1) e).map qw) ((qw x).deg + (qw e).deg + 4)
        (qw_isAP x) (qw_isAP e) (fun g hg => ltF_qw_of_pwLt hlt g hg) f ?_
      omega

/-! ### §5.12 The level-2 cofinality clause -/

private theorem inT_qv_mem : ∀ (F : List (List Nat)), inT (qv F) = true →
    ∀ e ∈ F, inT (pwv e) = true
  | [], _, e, he => by simp at he
  | [x], h, e, he => by
    have hx : e = x := by simpa using he
    rw [hx, show qv [x] = phi zero (pwv x) from rfl] at *
    exact (inT_phi h).2
  | x :: y :: r, h, e, he => by
    rw [qv_cons (show (y :: r) ≠ [] by simp)] at h
    obtain ⟨_, hqw, htl⟩ := inT_add h
    rcases List.mem_cons.mp he with h' | h'
    · rw [h']
      exact (inT_phi hqw).2
    · exact inT_qv_mem (y :: r) htl e h'

/-- Below `β+1` means at most `β`, on the nose. -/
private theorem lexNat_snoc_zero : ∀ (e x : List Nat), LexNat x (e ++ [0]) → x = e ∨ LexNat x e
  | [], x, h => by
    cases h with
    | nil => exact Or.inl rfl
    | head hy => omega
    | tail h' => exact absurd rfl (lexNat_ne_nil h')
  | z :: e', x, h => by
    cases h with
    | @nil y r => exact Or.inr .nil
    | @head y w r r' hyz => exact Or.inr (.head hyz)
    | @tail w r r' h' =>
      rcases lexNat_snoc_zero e' r h' with heq | hlt
      · exact Or.inl (by rw [heq])
      · exact Or.inr (.tail hlt)

private theorem pwLe_of_pwLt_snoc_zero {x e : List Nat} (h : PwLt x (e ++ [0])) : PwLe x e := by
  rcases lexNat_snoc_zero e x (lexNat_of_pwLt h) with heq | hlt
  · exact Or.inl (by rw [heq])
  · exact Or.inr (pwLt_of_lexNat hlt)

/-- **L2 relative to a prefix.**  The level-2 analogue of `below_pre`.  The
    threshold of the second disjunct mentions the target because a level-2
    comparison of components costs the degrees of BOTH components. -/
private theorem below_pre2 : ∀ (f : Nat) (P : List (List Nat)) (b : List Nat) (s : Term),
    inT s = true → ltF f s (qv (P ++ [b])) = true →
    (∃ F, (∀ e ∈ F, PwLt e b) ∧ s = qv (P ++ F)) ∨
    (∀ (T : List (List Nat)), T ≠ [] → ∀ g,
      2 * (s.deg + (qv (P ++ T)).deg) + 4 ≤ g → ltF g s (qv (P ++ T)) = true)
  | 0, P, b, s, _, h => by
    exact absurd h (by rw [show ltF 0 s (qv (P ++ [b])) = false from rfl]; simp)
  | f + 1, [], b, s, hs, h => by
    obtain ⟨F, hF, hse⟩ := below_q (f + 1) b s hs h
    exact Or.inl ⟨F, hF, by rw [hse]; rfl⟩
  | f + 1, x :: P', b, s, hs, h => by
    have htgt : qv ((x :: P') ++ [b]) = add (qw x) (qv (P' ++ [b])) := qv_cons (by simp)
    have hext : ∀ T : List (List Nat), T ≠ [] →
        qv ((x :: P') ++ T) = add (qw x) (qv (P' ++ T)) := by
      intro T hT
      refine qv_cons ?_
      intro hc
      exact hT (List.append_eq_nil_iff.mp hc).2
    rw [htgt] at h
    cases s with
    | zero =>
      refine Or.inr (fun T hT g hg => ?_)
      have := deg_pos (qv ((x :: P') ++ T))
      refine ltF_zero (by omega) ?_
      rw [hext T hT]
      intro hc; exact Term.noConfusion hc
    | M =>
      have h2 : (((M : Term) == qw x) || ltF f M (qw x)) = true := h
      rw [show (((M : Term) == qw x) : Bool) = false from rfl,
        show ltF f M (qw x) = false from Evidence.StageA.ltF_M_phi f zero (pwv x)] at h2
      exact Bool.noConfusion h2
    | omg a =>
      have h2 : ((omg a == qw x) || ltF f (omg a) (qw x)) = true := h
      rw [show ((omg a == qw x) : Bool) = false from rfl,
        show ltF f (omg a) (qw x) = false from ltF_omg_phi f a zero (pwv x)] at h2
      exact Bool.noConfusion h2
    | psi q a =>
      have h2 : ((psi q a == qw x) || ltF f (psi q a) (qw x)) = true := h
      rw [show ((psi q a == qw x) : Bool) = false from rfl] at h2
      simp only [Bool.false_or] at h2
      obtain ⟨e, _, heq⟩ := ap_below_qw f x (psi q a) hs rfl h2
      exact absurd heq (by intro hc; exact Term.noConfusion hc)
    | Z a =>
      have h2 : ((Z a == qw x) || ltF f (Z a) (qw x)) = true := h
      rw [show ((Z a == qw x) : Bool) = false from rfl] at h2
      simp only [Bool.false_or] at h2
      obtain ⟨e, _, heq⟩ := ap_below_qw f x (Z a) hs rfl h2
      exact absurd heq (by intro hc; exact Term.noConfusion hc)
    | phi a d =>
      have h2 : ((phi a d == qw x) || ltF f (phi a d) (qw x)) = true := h
      cases hxo : ((phi a d == qw x) : Bool) with
      | true =>
        have hax : phi a d = qw x := by simpa using hxo
        cases P' with
        | nil => exact Or.inl ⟨[], by simp, by rw [hax]; rfl⟩
        | cons z q =>
          refine Or.inr (fun T hT g hg => ?_)
          rw [hext T hT, hax]
          have hd1 : (qw x).deg ≤ (add (qw x) (qv ((z :: q) ++ T))).deg := by
            show (qw x).deg ≤ 1 + (qw x).deg + (qv ((z :: q) ++ T)).deg
            omega
          rw [hext T hT, hax] at hg
          cases g with
          | zero => have := deg_pos (qw x); omega
          | succ g' => exact ltF_to_add (qw_isAP x) (by simp)
      | false =>
        rw [hxo] at h2
        simp only [Bool.false_or] at h2
        obtain ⟨y, hy, heq⟩ := ap_below_qw f x (phi a d) hs rfl h2
        refine Or.inr (fun T hT g hg => ?_)
        rw [hext T hT, heq]
        rw [hext T hT, heq] at hg
        have hd2 : (qw x).deg ≤ (add (qw x) (qv (P' ++ T))).deg := by
          show (qw x).deg ≤ 1 + (qw x).deg + (qv (P' ++ T)).deg
          omega
        have hp1 := deg_pos (qw y)
        have hp2 := deg_pos (qw x)
        cases g with
        | zero => omega
        | succ g' =>
          refine ltF_to_add (qw_isAP y) ?_
          rw [ltF_qw_of_pwLt hy g' (by omega)]
          simp
    | add a c =>
      obtain ⟨hap, ha, hc⟩ := inT_add hs
      cases hxo : ((add a c) == add (qw x) (qv (P' ++ [b]))) with
      | true =>
        have heq : add a c = add (qw x) (qv (P' ++ [b])) := by simpa using hxo
        rw [heq, ltF_irrefl] at h
        exact Bool.noConfusion h
      | false =>
        have h2 : (if (a == qw x) = true then ltF f c (qv (P' ++ [b]))
                   else ltF f a (qw x)) = true := by
          rw [show ltF (f+1) (add a c) (add (qw x) (qv (P' ++ [b])))
                = (if ((add a c) == add (qw x) (qv (P' ++ [b]))) = true then false
                   else if (a == qw x) = true then ltF f c (qv (P' ++ [b]))
                   else ltF f a (qw x) : Bool) from rfl, hxo] at h
          simpa using h
        cases haz : (a == qw x) with
        | true =>
          have hax : a = qw x := by simpa using haz
          rw [haz] at h2
          simp only [if_true] at h2
          rcases below_pre2 f P' b c hc h2 with ⟨F, hF, hce⟩ | hc'
          · refine Or.inl ⟨F, hF, ?_⟩
            have hne : P' ++ F ≠ [] := by
              intro hc0
              exact inT_add_ne_zero hs (by rw [hce, hc0]; rfl)
            rw [hax, hce, ← qv_cons hne]
            rfl
          · refine Or.inr (fun T hT g hg => ?_)
            have hda : 2 ≤ (qw x).deg := by
              have := deg_pos (pwv x)
              have := deg_qw x
              omega
            rw [hext T hT, hax]
            rw [hext T hT, hax] at hg
            have hs1 : (add (qw x) c).deg = 1 + (qw x).deg + c.deg := rfl
            have hs2 : (add (qw x) (qv (P' ++ T))).deg
                = 1 + (qw x).deg + (qv (P' ++ T)).deg := rfl
            cases g with
            | zero => omega
            | succ g' => exact ltF_add_same (hc' T hT g' (by omega))
        | false =>
          rw [haz] at h2
          simp only [Bool.false_eq_true, if_false] at h2
          obtain ⟨y, hy, hay⟩ := ap_below_qw f x a ha hap h2
          have hhead : le ((toList c).headD zero) a = true := inT_add_head_le hs
          rw [hay] at hhead
          obtain ⟨F, hFne, hFb, hFc⟩ := tail_q c hc (inT_add_ne_zero hs) y hhead
          refine Or.inr (fun T hT g hg => ?_)
          have hpt : P' ++ T ≠ [] := by
            intro hc0; exact hT (List.append_eq_nil_iff.mp hc0).2
          rw [hext T hT, hay, hFc]
          rw [hext T hT, hay, hFc] at hg
          have hd1 : (qw y).deg ≤ (add (qw y) (qv F)).deg := by
            show (qw y).deg ≤ 1 + (qw y).deg + (qv F).deg
            omega
          have hd2 : (qw x).deg ≤ (add (qw x) (qv (P' ++ T))).deg := by
            show (qw x).deg ≤ 1 + (qw x).deg + (qv (P' ++ T)).deg
            omega
          rw [show add (qw y) (qv F) = ofList ([] ++ qw y :: F.map qw) from (qv_cons hFne).symm,
            show add (qw x) (qv (P' ++ T)) = ofList ([] ++ qw x :: (P' ++ T).map qw) from
              (qv_cons hpt).symm]
          have hp1 := deg_pos (qw y)
          have hp2 := deg_pos (qw x)
          refine ltF_ofList_head [] (qw y) (qw x) (F.map qw) ((P' ++ T).map qw)
            ((qw y).deg + (qw x).deg + 4) (qw_isAP y) (qw_isAP x)
            (fun g' hg' => ltF_qw_of_pwLt hy g' hg') g ?_
          simp only [List.length_nil]
          omega

/-- **Cofinality at a successor-exponent node.**  Every term of 𝔗(M) below
    `Q + ω^{β+1}` is overtaken by some `Q + ω^β·(n+1)`. -/
private theorem cof_q_succ (P : List (List Nat)) (e : List Nat) (s : Term) (hs : inT s = true)
    (h : lt s (qv (P ++ [e ++ [0]])) = true) :
    ∃ n, le s (qv (P ++ List.replicate (n + 1) e)) = true := by
  have hsplit : ∀ (Q : List (List Nat)), qv (P ++ Q) = ofList (P.map qw ++ Q.map qw) := by
    intro Q
    show ofList ((P ++ Q).map qw) = _
    rw [List.map_append]
  rcases below_pre2 _ P (e ++ [0]) s hs h with ⟨F, hF, hse⟩ | h'
  · refine ⟨F.length, ?_⟩
    have hPle : ∀ x ∈ F, PwLe x e := fun x hx => pwLe_of_pwLt_snoc_zero (hF x hx)
    have hlt : lt s (qv (P ++ List.replicate (F.length + 1) e)) = true := by
      refine lt_of_ltF (N := 2 * ((qv (P ++ F)).deg
        + (qv (P ++ List.replicate (F.length + 1) e)).deg) + 4) (fun f hf => ?_) ?_
      · rw [hse, hsplit F, hsplit (List.replicate (F.length + 1) e)]
        refine lt_qv_repl F e hPle (P.map qw) (qw_map_isAP P) f ?_
        rw [hsplit F, hsplit (List.replicate (F.length + 1) e)] at hf
        exact hf
      · rw [hse]
        omega
    simp [TM.Term.le, hlt]
  · refine ⟨0, ?_⟩
    have hlt : lt s (qv (P ++ [e])) = true := h' [e] (by simp) _
      (by show 2 * (s.deg + (qv (P ++ [e])).deg) + 4 ≤ 2 * (s.deg + (qv (P ++ [e])).deg) + 8
          omega)
    show ((s == qv (P ++ List.replicate 1 e)) || lt s (qv (P ++ List.replicate 1 e))) = true
    rw [show List.replicate 1 e = [e] from rfl, hlt]
    simp

/-- **Cofinality at a limit-exponent node.**  Every term of 𝔗(M) below `Q + ω^β`
    with `β` a limit is overtaken by some `Q + ω^{β[n]}` — ONE copy, because at a
    limit exponent the whole block is replaced. -/
private theorem cof_q_lim (P : List (List Nat)) (e : List Nat) (k : Nat) (s : Term)
    (hs : inT s = true) (h : lt s (qv (P ++ [e ++ [k + 1]])) = true) :
    ∃ n, le s (qv (P ++ [e ++ List.replicate (n + 1) k])) = true := by
  rcases below_pre2 _ P (e ++ [k + 1]) s hs h with ⟨F, hF, hse⟩ | h'
  · cases F with
    | nil =>
      refine ⟨0, ?_⟩
      have hlt : lt s (qv (P ++ [e ++ [k]])) = true := by
        rw [hse, List.append_nil]
        cases P with
        | nil => exact lt_of_qLt (qLt_zero (by simp))
        | cons z Q => exact lt_of_qLt (qLt_ext (z :: Q) (e ++ [k]) [] (by simp))
      simp [TM.Term.le, hlt]
    | cons x F' =>
      have hinT : inT (pwv x) = true :=
        inT_qv_mem (P ++ x :: F') (by rw [← hse]; exact hs) x
          (List.mem_append_right P (by simp))
      have hx := hF x (by simp)
      obtain ⟨n, hn⟩ := cof_pre e k (pwv x) hinT (lt_of_pwLt hx)
      have hstep : PwLt (e ++ List.replicate (n + 1) k) (e ++ List.replicate (n + 2) k) := by
        rw [show e ++ List.replicate (n + 2) k = (e ++ List.replicate (n + 1) k) ++ [k] from by
          rw [show n + 2 = (n + 1) + 1 from rfl, List.replicate_succ', ← List.append_assoc]]
        refine pwLt_ext (e ++ List.replicate (n + 1) k) k [] ?_
        intro hc
        have hl := congrArg List.length hc
        simp only [List.length_append, List.length_replicate, List.length_nil] at hl
        omega
      have hsplit2 : (pwv x == pwv (e ++ List.replicate (n + 1) k)) = true
          ∨ lt (pwv x) (pwv (e ++ List.replicate (n + 1) k)) = true := by
        simp only [TM.Term.le] at hn
        cases hb : (pwv x == pwv (e ++ List.replicate (n + 1) k)) with
        | true => exact Or.inl rfl
        | false =>
          rw [hb] at hn
          simp only [Bool.false_or] at hn
          exact Or.inr hn
      have hxlt : PwLt x (e ++ List.replicate (n + 2) k) := by
        rcases hsplit2 with heq | hlt2
        · exact pwLt_of_pwLe_pwLt (Or.inl (by simpa using heq)) hstep
        · exact pwLt_of_pwLe_pwLt (Or.inr (pwLt_of_lexNat (lexNat_of_ltF _ _ _ hlt2))) hstep
      refine ⟨n + 1, ?_⟩
      have hlt : lt s (qv (P ++ [e ++ List.replicate (n + 2) k])) = true := by
        rw [hse]
        exact lt_of_qLt (qLt_head P x (e ++ List.replicate (n + 2) k) F' [] hxlt)
      simp [TM.Term.le, hlt]
  · refine ⟨0, ?_⟩
    have hlt : lt s (qv (P ++ [e ++ [k]])) = true :=
      h' [e ++ [k]] (by simp) _
        (by show 2 * (s.deg + (qv (P ++ [e ++ [k]])).deg) + 4
                ≤ 2 * (s.deg + (qv (P ++ [e ++ [k]])).deg) + 8
            omega)
    simp [TM.Term.le, hlt]

/-! ### §5.13 The descent on count vectors

The level-2 certificate recursion descends on the level-1 EXPONENT, and that
descent is not structural (a limit exponent is replaced by a LONGER list).  The
count vector is where it becomes structural-in-disguise: both BM4 steps agree on
a prefix and strictly drop the next entry, i.e. they are instances of `lexLt_at`.

`Evidence/WF.lean` §1–§3 supplies exactly this: the length-preserving
lexicographic order `LexLt` on count vectors, its well-foundedness, and the step
lemma `lexLt_at` ("agree on a prefix, drop at the next entry") of which BOTH BM4
steps are instances.  That file was written for this use and is imported here.
The instance `Evidence.WF`'s `WellFoundedRelation (List Nat)` is `scoped`, so
importing does NOT change how Lean discharges termination anywhere else in this
file — the references below are explicit. -/

/-! #### How `expOf` sees the two steps -/

private theorem expOf_eq_nil : ∀ (v : List Nat), expOf v = [] → v = List.replicate v.length 0
  | [], _ => rfl
  | c :: cs, h => by
    have h' : List.replicate c cs.length ++ expOf cs = [] := h
    have hc : c = 0 := by
      cases c with
      | zero => rfl
      | succ c' => simp [List.replicate_succ] at h'
    have hcs : expOf cs = [] := by
      rw [hc] at h'
      simpa using h'
    rw [hc, expOf_eq_nil cs hcs]
    simp [List.replicate_succ]

private theorem expOf_split : ∀ (v : List Nat), expOf v = [] ∨
    ∃ (u : List Nat) (c j : Nat), v = u ++ (c + 1) :: List.replicate j 0
  | [] => Or.inl rfl
  | a :: v' => by
    rcases expOf_split v' with h | ⟨u, c, j, hu⟩
    · cases a with
      | zero =>
        left
        show List.replicate 0 v'.length ++ expOf v' = []
        simpa using h
      | succ c' =>
        right
        refine ⟨[], c', v'.length, ?_⟩
        rw [show v' = List.replicate v'.length 0 from expOf_eq_nil v' h]
        simp
    · exact Or.inr ⟨a :: u, c, j, by rw [hu]; rfl⟩

private theorem expOf_snoc_pos : ∀ (u : List Nat) (c j : Nat),
    expOf (u ++ (c + 1) :: List.replicate j 0)
      = expOf (u ++ c :: List.replicate j 0) ++ [j]
  | [], c, j => by
    show List.replicate (c+1) (List.replicate j 0).length ++ expOf (List.replicate j 0)
        = (List.replicate c (List.replicate j 0).length ++ expOf (List.replicate j 0)) ++ [j]
    rw [expOf_replicate_zero, List.length_replicate, List.append_nil, List.append_nil,
      List.replicate_succ']
  | a :: u', c, j => by
    show List.replicate a (u' ++ (c+1) :: List.replicate j 0).length
          ++ expOf (u' ++ (c+1) :: List.replicate j 0)
        = (List.replicate a (u' ++ c :: List.replicate j 0).length
          ++ expOf (u' ++ c :: List.replicate j 0)) ++ [j]
    rw [expOf_snoc_pos u' c j, List.append_assoc]
    simp

private theorem expOf_tail_zero : ∀ (u : List Nat) (c m j : Nat),
    expOf (u ++ c :: m :: List.replicate j 0)
      = expOf (u ++ c :: 0 :: List.replicate j 0) ++ List.replicate m j
  | [], c, m, j => by
    show List.replicate c (m :: List.replicate j 0).length
          ++ expOf (m :: List.replicate j 0)
        = (List.replicate c ((0 : Nat) :: List.replicate j 0).length
          ++ expOf ((0 : Nat) :: List.replicate j 0)) ++ List.replicate m j
    show List.replicate c (m :: List.replicate j 0).length
          ++ (List.replicate m (List.replicate j 0).length ++ expOf (List.replicate j 0))
        = (List.replicate c ((0 : Nat) :: List.replicate j 0).length
          ++ (List.replicate 0 (List.replicate j 0).length ++ expOf (List.replicate j 0)))
          ++ List.replicate m j
    rw [expOf_replicate_zero, List.length_replicate]
    simp
  | a :: u', c, m, j => by
    show List.replicate a (u' ++ c :: m :: List.replicate j 0).length
          ++ expOf (u' ++ c :: m :: List.replicate j 0)
        = (List.replicate a (u' ++ c :: (0 : Nat) :: List.replicate j 0).length
          ++ expOf (u' ++ c :: (0 : Nat) :: List.replicate j 0)) ++ List.replicate m j
    rw [expOf_tail_zero u' c m j, List.append_assoc]
    simp

private theorem pwLt_snoc (e : List Nat) (k : Nat) : PwLt e (e ++ [k]) := by
  cases e with
  | nil => exact pwLt_zero (by simp)
  | cons a r => exact pwLt_ext (a :: r) k [] (by simp)

/-! ### §5.14 The certificate family below ω^(ω^ω)

One component at a time, by well-founded recursion on the count vector of its
exponent: the successor-exponent step drops the level-0 entry, the
limit-exponent step drops the entry at level `j` and fills level `j-1` — the two
instances of `lexLt_at`, exactly as `Evidence/WF.lean` predicted. -/

private theorem cert_q_one : ∀ (v : List Nat) (Q : List (List Nat)),
    Certified (qM Q) (qv Q) → Certified (qM (Q ++ [expOf v])) (qv (Q ++ [expOf v])) := by
  intro v
  refine Evidence.WF.lexLt_wf.induction (C := fun w => ∀ (Q : List (List Nat)),
    Certified (qM Q) (qv Q) → Certified (qM (Q ++ [expOf w])) (qv (Q ++ [expOf w]))) v ?_
  intro v IH Q hQ
  rcases expOf_split v with hnil | ⟨u, c, j, rfl⟩
  · rw [hnil, ← plus_qv_one]
    exact .succ (kind_qM_succ Q) (fun n => by rw [expand_qM_succ]; exact hQ)
  · rw [expOf_snoc_pos u c j]
    cases j with
    | zero =>
      have hv : Evidence.WF.LexLt (u ++ [c]) (u ++ [c + 1]) :=
          Evidence.WF.lexLt_at u (by omega) rfl
      have hfam : ∀ m, Certified (qM (Q ++ List.replicate m (expOf (u ++ [c]))))
          (qv (Q ++ List.replicate m (expOf (u ++ [c])))) := by
        intro m
        induction m with
        | zero => rw [List.replicate_zero, List.append_nil]; exact hQ
        | succ m' ih =>
          rw [show Q ++ List.replicate (m' + 1) (expOf (u ++ [c]))
                = (Q ++ List.replicate m' (expOf (u ++ [c]))) ++ [expOf (u ++ [c])] from by
              rw [List.replicate_succ', ← List.append_assoc]]
          exact IH (u ++ [c]) hv _ ih
      refine .lim (fun n => qv (Q ++ List.replicate (n + 1) (expOf (u ++ [c]))))
        (kind_qM_sexp Q (expOf (u ++ [c]))) (fun n => ?_) (fun n => ?_) (fun n => ?_)
        (fun s hs h => cof_q_succ Q (expOf (u ++ [c])) s hs h)
      · rw [expand_qM_sexp]
        exact hfam (n + 1)
      · refine lt_of_qLt ?_
        rw [show List.replicate (n + 1) (expOf (u ++ [c]))
              = expOf (u ++ [c]) :: List.replicate n (expOf (u ++ [c])) from
            List.replicate_succ]
        exact qLt_head Q (expOf (u ++ [c])) (expOf (u ++ [c]) ++ [0])
          (List.replicate n (expOf (u ++ [c]))) [] (pwLt_snoc _ 0)
      · refine lt_of_qLt ?_
        rw [show Q ++ List.replicate (n + 1 + 1) (expOf (u ++ [c]))
              = (Q ++ List.replicate (n + 1) (expOf (u ++ [c]))) ++ [expOf (u ++ [c])] from by
            rw [List.replicate_succ', ← List.append_assoc]]
        refine qLt_ext (Q ++ List.replicate (n + 1) (expOf (u ++ [c]))) (expOf (u ++ [c])) [] ?_
        intro hc0
        have hl := congrArg List.length hc0
        simp only [List.length_append, List.length_replicate, List.length_nil] at hl
        omega
    | succ k =>
      have hstep : ∀ n : Nat,
          expOf (u ++ c :: (n + 1) :: List.replicate k 0)
            = expOf (u ++ c :: List.replicate (k + 1) 0) ++ List.replicate (n + 1) k := by
        intro n
        rw [expOf_tail_zero u c (n + 1) k,
          show List.replicate (k + 1) (0 : Nat) = 0 :: List.replicate k 0 from
            List.replicate_succ]
      refine .lim
        (fun n => qv (Q ++ [expOf (u ++ c :: List.replicate (k + 1) 0)
          ++ List.replicate (n + 1) k]))
        (kind_qM_lexp Q (expOf (u ++ c :: List.replicate (k + 1) 0)) k)
        (fun n => ?_) (fun n => ?_) (fun n => ?_)
        (fun s hs h => cof_q_lim Q (expOf (u ++ c :: List.replicate (k + 1) 0)) k s hs h)
      · show Certified
          (BMS.expand (qM (Q ++ [expOf (u ++ c :: List.replicate (k + 1) 0) ++ [k + 1]])) n)
          (qv (Q ++ [expOf (u ++ c :: List.replicate (k + 1) 0) ++ List.replicate (n + 1) k]))
        rw [expand_qM_lexp, ← hstep n]
        refine IH (u ++ c :: (n + 1) :: List.replicate k 0) ?_ Q hQ
        rw [show u ++ (c + 1) :: List.replicate (k + 1) 0
              = u ++ (c + 1) :: 0 :: List.replicate k 0 from by
            rw [show List.replicate (k + 1) (0 : Nat) = 0 :: List.replicate k 0 from
              List.replicate_succ]]
        exact Evidence.WF.lexLt_at u (by omega) (by simp)
      · refine lt_of_qLt ?_
        rw [show expOf (u ++ c :: List.replicate (k + 1) 0) ++ List.replicate (n + 1) k
              = expOf (u ++ c :: List.replicate (k + 1) 0) ++ k :: List.replicate n k from by
            rw [show List.replicate (n + 1) k = k :: List.replicate n k from
              List.replicate_succ]]
        exact qLt_head Q _ _ [] []
          (pwLt_head (expOf (u ++ c :: List.replicate (k + 1) 0)) k (k + 1)
            (List.replicate n k) [] (by omega))
      · refine lt_of_qLt ?_
        refine qLt_head Q _ _ [] [] ?_
        rw [show expOf (u ++ c :: List.replicate (k + 1) 0) ++ List.replicate (n + 1 + 1) k
              = (expOf (u ++ c :: List.replicate (k + 1) 0) ++ List.replicate (n + 1) k) ++ [k]
            from by
              rw [show List.replicate (n + 1 + 1) k = List.replicate (n + 1) k ++ [k] from
                List.replicate_succ', ← List.append_assoc]]
        exact pwLt_snoc _ k

/-- **The region below ω^(ω^ω), certified.** -/
theorem cert_q : ∀ (V : List (List Nat)) (Q : List (List Nat)),
    Certified (qM Q) (qv Q) → Certified (qM (Q ++ V.map expOf)) (qv (Q ++ V.map expOf))
  | [], Q, hQ => by
    show Certified (qM (Q ++ [])) (qv (Q ++ []))
    rw [List.append_nil]
    exact hQ
  | v :: V', Q, hQ => by
    show Certified (qM (Q ++ (expOf v :: V'.map expOf))) (qv (Q ++ (expOf v :: V'.map expOf)))
    rw [show Q ++ (expOf v :: V'.map expOf) = (Q ++ [expOf v]) ++ V'.map expOf from by
      rw [List.append_assoc]; rfl]
    exact cert_q V' (Q ++ [expOf v]) (cert_q_one v Q hQ)

/-! ### §5.15 ω^(ω^ω) — the row `(0)(1)(2)(3)` -/

private theorem pwLt_of_bound {e : List Nat} {k : Nat} (h : ∀ x ∈ e, x ≤ k) : PwLt e [k + 1] := by
  cases e with
  | nil => exact pwLt_of_lexNat .nil
  | cons y r =>
    refine pwLt_of_lexNat (.head ?_)
    have := h y (by simp)
    omega

/-- **L2 for ω^(ω^ω).** -/
private theorem below_q_omega : ∀ (f : Nat) (s : Term), inT s = true →
    ltF f s (phi zero (phi zero omega)) = true →
    ∃ (F : List (List Nat)) (k : Nat), (∀ e ∈ F, PwLt e [k + 1]) ∧ s = qv F
  | 0, s, _, h => by
    exact absurd h (by rw [show ltF 0 s (phi zero (phi zero omega)) = false from rfl]; simp)
  | f + 1, s, hs, h => by
    cases s with
    | zero => exact ⟨[], 0, by simp, rfl⟩
    | M =>
      rw [Evidence.StageA.ltF_M_phi] at h
      exact Bool.noConfusion h
    | omg a =>
      rw [show ltF (f+1) (omg a) (phi zero (phi zero omega)) = false from rfl] at h
      exact Bool.noConfusion h
    | psi q a =>
      have h2 : ((psi q a == zero) || (psi q a == phi zero omega) || ltF f (psi q a) zero
                 || ltF f (psi q a) (phi zero omega)) = true := h
      rw [show ((psi q a == zero) : Bool) = false from rfl,
        show ((psi q a == phi zero omega) : Bool) = false from rfl, ltF_lt_zero] at h2
      simp only [Bool.or_false, Bool.false_or] at h2
      obtain ⟨e, _, _, he⟩ := below_pw_omega f (psi q a) hs h2
      exact absurd he (pwv_ne_psi q a e)
    | Z a =>
      have h2 : ((Z a == zero) || (Z a == phi zero omega) || ltF f (Z a) zero
                 || ltF f (Z a) (phi zero omega)) = true := h
      rw [show ((Z a == zero) : Bool) = false from rfl,
        show ((Z a == phi zero omega) : Bool) = false from rfl, ltF_lt_zero] at h2
      simp only [Bool.or_false, Bool.false_or] at h2
      obtain ⟨e, _, _, he⟩ := below_pw_omega f (Z a) hs h2
      exact absurd he (pwv_ne_Z a e)
    | phi a b =>
      obtain ⟨ha, hb⟩ := inT_phi hs
      cases hxo : ((phi a b) == phi zero (phi zero omega)) with
      | true =>
        have heq : phi a b = phi zero (phi zero omega) := by simpa using hxo
        rw [heq, ltF_irrefl] at h
        exact Bool.noConfusion h
      | false =>
        have h2 : (if (a == zero) = true then ltF f b (phi zero omega)
                   else if ltF f a zero = true then ltF f b (phi zero (phi zero omega))
                   else ((phi a b == phi zero omega) || ltF f (phi a b) (phi zero omega)))
            = true := by
          rw [show ltF (f+1) (phi a b) (phi zero (phi zero omega))
                = (if ((phi a b) == phi zero (phi zero omega)) = true then false
                   else if (a == zero) = true then ltF f b (phi zero omega)
                   else if ltF f a zero = true then ltF f b (phi zero (phi zero omega))
                   else ((phi a b == phi zero omega)
                     || ltF f (phi a b) (phi zero omega)) : Bool) from rfl, hxo] at h
          simpa using h
        cases haz : (a == zero) with
        | true =>
          have haz' : a = zero := by simpa using haz
          rw [haz] at h2
          simp only [if_true] at h2
          obtain ⟨e, k, hek, hbe⟩ := below_pw_omega f b hb h2
          exact ⟨[e], k, by
            intro y hy
            simp at hy
            rw [hy]
            exact pwLt_of_bound hek, by rw [haz', hbe]; rfl⟩
        | false =>
          rw [haz] at h2
          simp only [Bool.false_eq_true, if_false, ltF_lt_zero] at h2
          have hcontra : ∀ (a' : List Nat), phi a b ≠ pwv a' := by
            intro a' hc0
            have := pwv_eq_phi a' a b hc0.symm
            rw [this] at haz
            simp at haz
          cases hbe : ((phi a b == phi zero omega) : Bool) with
          | true =>
            have hc1 : phi a b = phi zero omega := by simpa using hbe
            have : a = zero := by injection hc1 with h1 _
            rw [this] at haz
            simp at haz
          | false =>
            rw [hbe] at h2
            simp only [Bool.false_or] at h2
            obtain ⟨e, _, _, he⟩ := below_pw_omega f (phi a b) hs h2
            exact absurd he (hcontra e)
    | add a c =>
      obtain ⟨hap, ha, hc⟩ := inT_add hs
      have h2 : ltF f a (phi zero (phi zero omega)) = true := h
      obtain ⟨Fa, k, hFa, haa⟩ := below_q_omega f a ha h2
      obtain ⟨e, rfl⟩ := qv_isAP Fa (by rw [← haa]; exact hap)
      have hae : a = qw e := haa
      have hek : PwLt e [k + 1] := hFa e (by simp)
      have hhead : le ((toList c).headD zero) a = true := inT_add_head_le hs
      rw [hae] at hhead
      obtain ⟨F, hFne, hFb, hFc⟩ := tail_q c hc (inT_add_ne_zero hs) e hhead
      refine ⟨e :: F, k, ?_, by rw [hae, hFc, qv_cons hFne]⟩
      intro y hy
      rcases List.mem_cons.mp hy with h' | h'
      · rw [h']; exact hek
      · exact pwLt_of_pwLe_pwLt (hFb y h') hek

private theorem expand_omega_pow_pow (n : Nat) :
    BMS.expand ([[0], [1], [2], [3]] : Matrix) n = qM [[n + 1]] := by
  have hexp := StageA.expand_oneRow (A := [0, 1]) (B := [2]) (c := 3) (b0 := 2)
    (B' := []) rfl (by omega) (by intro x hx; simp at hx) (by omega) n
  show (BMS.expand? ([[0], [1], [2], [3]] : Matrix) n).getD [] = _
  rw [show ([[0], [1], [2], [3]] : Matrix)
        = StageA.oneRow ((([0, 1] : List Nat) ++ [2]) ++ [3]) from rfl, hexp]
  show StageA.oneRow ([0, 1] ++ StageA.repL [2] (n + 1)) = StageA.oneRow (qSeq [[n + 1]])
  rw [repL_single, qSeq_single, pwSeq_single,
    show StageA.mkBlock (blockOf (n + 1)) = 0 :: (blockOf (n + 1)).map (· + 1) from rfl,
    blockOf_map_succ]
  rfl

/-- **ω^(ω^ω).**  `(0)(1)(2)(3)` has value ω^(ω^ω). -/
theorem cert_omega_pow_pow : Certified [[0], [1], [2], [3]] (phi zero (phi zero omega)) := by
  refine .lim (fun n => qv [[n + 1]]) rfl (fun n => ?_) (fun n => ?_) (fun n => ?_)
    (fun s hs h => ?_)
  · rw [expand_omega_pow_pow n]
    have hc := cert_q [1 :: List.replicate (n + 1) 0] []
      (show Certified (qM []) (qv []) from .zero)
    rw [List.nil_append,
      show ([1 :: List.replicate (n + 1) 0].map expOf) = [[n + 1]] from by
        show [expOf (1 :: List.replicate (n + 1) 0)] = _
        rw [expOf_step]
        rfl] at hc
    exact hc
  · refine lt_of_ltF (N := n + 6) (fun g hg => ?_) ?_
    · cases g with
      | zero => omega
      | succ g1 =>
        refine ltF_phi_same ?_
        cases g1 with
        | zero => omega
        | succ g2 => exact ltF_phi_same (ltF_ofNat_omega (n + 1) g2 (by omega))
    · have := deg_ofNat (n + 1)
      show n + 6 ≤ 2 * ((qv [[n+1]]).deg + (phi zero (phi zero omega)).deg) + 8
      show n + 6 ≤ 2 * ((1 + 1 + (1 + 1 + (ofNat (n+1)).deg))
        + (phi zero (phi zero omega)).deg) + 8
      omega
  · exact lt_qw_of_pwLt (pwLt_of_lexNat (.head (by omega)))
  · obtain ⟨F, k, hF, hse⟩ := below_q_omega _ s hs h
    refine ⟨k, ?_⟩
    cases F with
    | nil =>
      rw [hse]
      show ((qv ([] : List (List Nat)) == qv [[k+1]]) || lt (qv []) (qv [[k+1]])) = true
      rw [show lt (qv ([] : List (List Nat))) (qv [[k+1]]) = true from
        lt_of_qLt (qLt_zero (by simp))]
      simp
    | cons e F' =>
      have hlt : lt (qv (e :: F')) (qv [[k + 1]]) = true :=
        lt_of_qLt (qLt_head [] e [k + 1] F' [] (hF e (by simp)))
      rw [hse]
      simp [TM.Term.le, hlt]

/-! ### The negative control for the ω^(ω^ω) row -/

private theorem beq_phi_zero_false {x y : Term} (h : x ≠ y) :
    ((phi zero x == phi zero y) : Bool) = false := by
  cases hb : ((phi zero x == phi zero y) : Bool) with
  | true =>
    have heq : phi zero x = phi zero y := by simpa using hb
    injection heq with _ h2
    exact absurd h2 h
  | false => rfl

private theorem omega_pw_ne (n : Nat) : (phi zero omega : Term) ≠ phi zero (ofNat (n + 1)) := by
  intro hc
  injection hc with _ h2
  exact omega_ne_ofNat (n + 1) h2

private theorem qw_omega_ne (n : Nat) :
    (phi zero (phi zero omega) : Term) ≠ phi zero (phi zero (ofNat (n + 1))) := by
  intro hc
  injection hc with _ h2
  exact omega_pw_ne n h2

private theorem ltF_omega_pw : ∀ (n f : Nat), ltF f (phi zero omega) (pw (n + 1)) = false
  | _, 0 => rfl
  | n, f + 1 =>
    ltF_phi_zero_false (ltF_omega_ofNat (n + 1) f) (beq_phi_zero_false (omega_ne_ofNat (n + 1)))

private theorem ltF_qw_omega : ∀ (n f : Nat),
    ltF f (phi zero (phi zero omega)) (qv [[n + 1]]) = false
  | _, 0 => rfl
  | n, f + 1 => ltF_phi_zero_false (ltF_omega_pw n f) (beq_phi_zero_false (omega_pw_ne n))

/-- No `ω^(ω^(n+1))` overtakes ω^(ω^ω). -/
private theorem le_qw_omega (n : Nat) :
    le (phi zero (phi zero omega)) (qv [[n + 1]]) = false := by
  show ((phi zero (phi zero omega) == qv [[n + 1]])
        || lt (phi zero (phi zero omega)) (qv [[n + 1]])) = false
  rw [show ((phi zero (phi zero omega) == qv [[n + 1]]) : Bool) = false from
      beq_phi_zero_false (omega_pw_ne n),
    show lt (phi zero (phi zero omega)) (qv [[n + 1]]) = false from ltF_qw_omega n _]
  rfl

/-- **The negative control for ω^(ω^ω), machine-checked.**  With the expansion
    values `fs' n = ω^(ω^(n+1))` of `cert_omega_pow_pow`, which are forced by
    `cert_q`, the cofinality clause for the compressed value ω^(ω^ω)·2 is FALSE:
    the term ω^(ω^ω) of 𝔗(M) is below it and is overtaken by no `fs' n`. -/
theorem neg_control_omega_pow_pow_times_two :
    ¬ (∀ s, inT s = true →
        lt s (add (phi zero (phi zero omega)) (phi zero (phi zero omega))) = true →
        ∃ n, le s (qv [[n + 1]]) = true) := by
  intro hcof
  obtain ⟨n, hn⟩ := hcof (phi zero (phi zero omega)) (by decide) (by decide)
  rw [le_qw_omega n] at hn
  exact Bool.noConfusion hn

/-! ### Evidence for the ω^(ω^ω) layer -/

#guard Trans.oPr (qM [[2], [1, 0], []]) == qv [[2], [1, 0], []]
#guard inT (qv [[2], [1, 0], []]) = true
#guard inT (phi zero (phi zero omega)) = true
#guard BMS.expand ([[0], [1], [2], [3]] : Matrix) 3 == qM [[4]]
#guard Trans.oPr (qM [[4]]) == qv [[4]]
#guard qv [[4]] == phi zero (phi zero (ofNat 4))
-- the count-vector descent of §5.14, as the recursion uses it
#guard expOf [1, 0, 0] == [2]
#guard expOf [0, 2, 1] == [1, 1, 0]
#guard BMS.expand (qM [expOf [1, 0, 0]]) 1 == qM [expOf [0, 2, 0]]
/-! ## §7 The negative control, as a theorem

The standing control of the header — "try to certify `(0)(1) ↦ ω+5`" — is no
longer only a comment.  `cert_omega` uses `fs' n = ofNat (n+1)` (forced: those
ARE the values of the expansions of `(0)(1)`, certified in §2), so an attempt to
certify ω+5 for the same matrix has to discharge the cofinality clause with the
same `fs'`.  That clause is refutable, and the refutation is machine-checked
below: the witness is the genuine term ω+3.

If a future edit of the `lim` premise makes `neg_control_omega_plus_five`
unprovable (e.g. the flipped `∃ n, fs' n ≤ s`), the definition is broken. -/

private theorem plus_omega_ofNat (k : Nat) : plus omega (ofNat k) = wm 1 k := by
  show plus omega (ofNat k) = ofList (List.replicate 1 omega ++ List.replicate k one)
  unfold plus
  cases k with
  | zero => rfl
  | succ j =>
    rw [toList_ofNat (j+1), List.replicate_succ]
    show ofList ((toList omega).filter (fun a => le one a) ++ one :: List.replicate j one) = _
    rw [show toList omega = [omega] from rfl,
      List.filter_cons_of_pos (show le one omega = true from rfl)]
    rfl

private theorem ltF_omega3_ofNat : ∀ (n f : Nat),
    ltF f (add omega (ofNat 3)) (ofNat (n + 1)) = false
  | _, 0 => rfl
  | 0, f + 1 => by
    show (if (add omega (ofNat 3) == ofNat 1) = true then false else ltF f omega (ofNat 1)) = false
    rw [show ((add omega (ofNat 3) == ofNat 1) : Bool) = false from rfl]
    simp only [Bool.false_eq_true, if_false]
    exact ltF_one_false f omega (by decide) (by intro hc; exact Term.noConfusion hc)
  | n + 1, f + 1 => by
    rw [ofNat_shape n]
    show (if (add omega (ofNat 3) == add one (ofNat (n+1))) = true then false
          else if ((omega : Term) == one) = true then ltF f (ofNat 3) (ofNat (n+1))
          else ltF f omega one) = false
    rw [show ((add omega (ofNat 3) == add one (ofNat (n+1))) : Bool) = false from rfl,
      show (((omega : Term) == one) : Bool) = false from rfl]
    simp only [Bool.false_eq_true, if_false]
    exact ltF_one_false f omega (by decide) (by intro hc; exact Term.noConfusion hc)

/-- No finite term overtakes ω+3. -/
private theorem le_omega3_ofNat (n : Nat) : le (plus omega (ofNat 3)) (ofNat (n + 1)) = false := by
  rw [plus_omega_ofNat 3, wm_cons 0 3 (by omega), wm_zero_k]
  show ((add omega (ofNat 3) == ofNat (n+1)) || lt (add omega (ofNat 3)) (ofNat (n+1))) = false
  rw [show lt (add omega (ofNat 3)) (ofNat (n+1)) = false from ltF_omega3_ofNat n _]
  cases n with
  | zero => rfl
  | succ m => rw [ofNat_shape m]; rfl

/-- **The negative control, machine-checked.**  The cofinality clause that a
    certificate `Certified [[0],[1]] (ω+5)` would need — with the expansion
    values `fs' n = ofNat (n+1)` of `cert_omega`, which are forced by §2 — is
    FALSE: the term ω+3 of 𝔗(M) is below ω+5 and is overtaken by no `fs' n`. -/
theorem neg_control_omega_plus_five :
    ¬ (∀ s, inT s = true → lt s (plus omega (ofNat 5)) = true →
        ∃ n, le s (ofNat (n + 1)) = true) := by
  intro hcof
  obtain ⟨n, hn⟩ := hcof (plus omega (ofNat 3)) (by decide) (by decide)
  rw [le_omega3_ofNat n] at hn
  exact Bool.noConfusion hn

/-! ## §8 The junk-term computations behind the DEFINITION CHANGE


`1 + M` is not a term of 𝔗(M), yet the head-only comparison of formal sums puts
it below ω while no finite term overtakes it.  Without `inT` in the cofinality
premise these three lines make the `lim` constructor unusable for ω. -/

#guard lt (add one M) omega = true
#guard inT (add one M) = false
#guard (List.range 40).all (fun n => le (add one M) (ofNat n) == false)

-- the same for ω^ω, with the junk hidden inside the exponent
#guard lt (phi zero (add one M)) (phi zero omega) = true
#guard inT (phi zero (add one M)) = false
#guard (List.range 40).all (fun n => le (phi zero (add one M)) (phi zero (ofNat n)) == false)

-- the negative control's witness ω+3 IS a term of 𝔗(M), so the control survives
#guard inT (plus omega (ofNat 3)) = true
#guard lt (plus omega (ofNat 3)) (plus omega (ofNat 5)) = true
#guard (List.range 40).all (fun n => le (plus omega (ofNat 3)) (ofNat n) == false)

/-! ## §9 THE ε₀ ROW `(0,0)(1,1)` — the BMS side, and the map to `cert_eps0`
    (certificate lane, 2026-08-09)

STATUS.  The 𝔗(M) side of this row is DONE, in `Evidence/WF.lean`: §9 there proves
the three order premises of `Certified.lim` for the ω-towers (`lt_tower_eps0`,
`lt_tower_step`, and the cofinality clause `cof_eps0`), and §11–§14 prove all four
premises for EVERY CNF limit below ε₀ at once (`Evidence.WF.lim_clauses`, with the
sequence `Evidence.WF.fsC`).  This section supplies the BMS side of the row itself
and states exactly what is still missing.

BUILD NOTE.  `Evidence/WF.lean` grew from 1635 to ~3650 lines in this lane, so
until someone runs `lake build` a snippet of THIS file still sees the old
`Evidence.WF` olean.  Everything below is therefore written to depend only on
`BMS/` and `Trans/`, and no name from WF.lean §9–§14 is used yet.  Wiring
`cert_eps0` to `Evidence.WF.cof_eps0` is the first thing to do after the build.

THE ROW.  `BMS.kind (0,0)(1,1) = .lim` and

    (0,0)(1,1)[n] = (0,0)(1,0)(2,0)…(n,0) = `towerM n`

(`expand_eps0_row`, proved below — the ascension amount Δ₀ = 1 lands in the copied
column, Δ₁ = 0, which is why the second row stays zero).  Its values are the
ω-TOWERS: `o? (towerM n) = 1, ω, ω^ω, ω^(ω^ω), …` (the `#guard`s below check the
first four against the terms of the already-certified rows).  So the certificate is

    cert_eps0 : Certified [[0,0],[1,1]] (phi one zero)
      := .lim Evidence.WF.tower rfl  ⟨A⟩  Evidence.WF.lt_tower_eps0
             Evidence.WF.lt_tower_step  (fun s hs h => Evidence.WF.cof_eps0 s hs h)

and the ONLY missing premise is ⟨A⟩ : `∀ n, Certified (towerM n) (tower n)`.

WHAT ⟨A⟩ NEEDS (Stage 2c — the honest frontier of this lane).

  1. THE PAD IS INERT.  `towerM n` is the one-row matrix `(0)(1)…(n)` with a
     second row of zeros, and the BM4 rule ignores that row: `lnz [a,0] = lnz [a]`,
     `parent` at rows ≥ 1 is `none` (every entry there is 0, so the filter is
     empty), and `delta M r 0 y = 0` for every `y` because the lowest nonzero row
     is `t = 0` and `delta` is `0` unless `y < t`.  Hence
         BMS.kind (pad M) = BMS.kind M      and      BMS.expand (pad M) n = pad (BMS.expand M n)
     for one-row `M`, and therefore `Certified M t → Certified (pad M) t` by a
     one-screen induction on the derivation.  MEASURED on the whole tower family;
     the `#guard`s below keep a sample.  This is needed because §2–§5.15's
     certificates are for the UNPADDED matrices — `cert_omega_pow` gives
     `Certified [[0],[1],[2]] ω^ω`, not `Certified (towerM 2) ω^ω`.

  2. THE ONE-ROW CERTIFICATE FAMILY, i.e. `Certified (oneRow s) (oV s)` for every
     `stdSeq s`, by well-founded recursion on `Evidence.WF.acc_cn` /
     `Evidence.WF.wf_RCn`.  The expansion identity it runs on is already inside
     `Evidence/StageA.lean`'s `e3_general` — its proof establishes
         BMS.expand (oneRow s) n = oneRow (A ++ repL B (n+1))   and
         oV (A ++ repL B (n+1)) = fsN (oV s) (n+1)
     for the decomposition `s = A ++ B ++ [c]` produced by `core`.  Two gaps
     remain: `stdSeq` is not known to be PRESERVED by the expansion (needed to
     re-enter the recursion), and `fsN` has to be matched to `Evidence.WF.fsC`
     (MEASURED equal on the CNF segment with the index shift `fsC t n = fsN t (n+1)`;
     alternatively skip `fsN` entirely, since `Certified.lim` takes an arbitrary
     `fs'` and WF.lean §14 gives all four clauses for `fsC` directly).
     Levels 0–3 of the family already exist concretely (§2, §3, §5.7, §5.15), so
     the recursion only has to reproduce them uniformly.

  3. THE PER-ROW NEGATIVE CONTROL for ε₀, in the style of §7 and of
     `Evidence.WF.cof_eps0_needs_inT`: an attempt to certify ε₀·2 or ε₀+ω for
     `(0,0)(1,1)` must be refuted by a genuine witness of 𝔗(M).  With `fs' = tower`
     forced by 1 above, the witness is any term below the compressed value that no
     tower overtakes — e.g. ε₀ itself for ε₀·2.

WHAT HAPPENED TO 1 AND 2 (updated 2026-08-15).  Both landed and this header was
left describing them as open, which is worth correcting rather than leaving for a
reader to discover.

  * ITEM 1 is §10's `padRow` and its computation lemmas (`ent_padRow`,
    `parent_padRow`, `expand_padRow`) — the pad is inert, proved, not measured.
  * ITEM 2 is §13's `certIn_sq`: `CertifiedIn DomF (oneRow (sq t)) t` for every
    CNF `t`, by well-founded recursion.  The `stdSeq`-preservation gap named above
    DISSOLVED rather than closed — `sq_decomp` produces the decomposition
    `StageA.expand_oneRow` asks for at every CNF limit, with no standardness
    predicate to propagate (§10's header).  The `fsN`/`fsC` gap dissolved the same
    way: `Certified.lim` takes an arbitrary `fs'`, so §14's clauses for `fsC` are
    used directly and `fsN` is never mentioned.
  * §23 then made that recursion's SHAPE reusable, and `certIn_sq_via_region`
    rebuilds item 2 as one instance of it.

  * ITEM 3 LANDED TOO, and an earlier revision of this note said otherwise.  §13.1's
    `neg_control_eps0_times_two` is the control this item asks for, with ε₀ as the
    witness, and §15.8's `neg_control_eps0_times_two_strong` is strictly stronger:
    `¬ Certified [[0,0],[1,1]] (ε₀·2)` with no instantiation assumed at all.

SO NOTHING IN THIS LIST IS OPEN.  What is open is the SAME THREE ITEMS FOR A ROW
THAT IS NOT YET REGISTERED — a certificate needs its family (§23's `Reg` and the
three supplies), and a negative control needs the certificate first, since §6.1's
`certRows_unique_gate` and §15.10's `certRows_no_overshoot` deliver it for free
once a row is registered.  That is where `table/diff.md`'s family 4 meets this
lane: the 326th disputed row cannot be decided by the expansion-sequence test
(neither value lies on `fsN`), so it waits on the certificate, not on a new idea
about controls. -/

/-- `(0)(1)…(n)` with a second row of zeros: the n-th expansion of the ε₀ row. -/
def towerM (n : Nat) : Matrix := (List.range (n + 1)).map (fun a => [a, 0])

private theorem flatten_map_singleton {α : Type} (f : α → List Nat) :
    ∀ (l : List α), ((l.map (fun a => [f a])).flatten) = l.map f
  | [] => rfl
  | a :: t => by
    show [f a] ++ ((t.map (fun x => [f x])).flatten) = f a :: t.map f
    rw [flatten_map_singleton f t]
    rfl

/-- The ε₀ row is a limit row. -/
theorem kind_eps0_row : BMS.kind [[0, 0], [1, 1]] = .lim := rfl

/-- **The BMS side of the ε₀ row, in closed form.** -/
theorem expand_eps0_row (n : Nat) : BMS.expand [[0, 0], [1, 1]] n = towerM n := by
  show (BMS.expand? [[0, 0], [1, 1]] n).getD [] = towerM n
  rw [show BMS.expand? [[0, 0], [1, 1]] n
      = some (((List.range (n + 1)).map (fun a => [[0 + a * 1 * 1, 0 + a * 0 * 1]])).flatten)
      from rfl]
  show ((List.range (n + 1)).map (fun a => [[0 + a * 1 * 1, 0 + a * 0 * 1]])).flatten = towerM n
  rw [show (fun (a : Nat) => [[0 + a * 1 * 1, 0 + a * 0 * 1]])
        = (fun (a : Nat) => [((fun (b : Nat) => [b, 0]) a)]) from by
      funext a; simp]
  rw [flatten_map_singleton]
  rfl

/-! ### §9.1 Evidence for the map above -/

-- the values of the expansions are the towers: the first four are the terms of the
-- rows already certified in §2, §3, §5.7 and §5.15
#guard Trans.oR (towerM 0) == some one
#guard Trans.oR (towerM 1) == some omega
#guard Trans.oR (towerM 2) == some (phi zero omega)
#guard Trans.oR (towerM 3) == some (phi zero (phi zero omega))

-- and the unpadded rows that ARE certified carry the same values, which is what
-- the pad transfer of item 1 has to turn into a `Certified`
#guard Trans.oR [[0], [1], [2]] == Trans.oR (towerM 2)
#guard Trans.oR [[0], [1], [2], [3]] == Trans.oR (towerM 3)

-- the pad is inert, on the whole tower family and on their expansions
#guard (List.range 5).all (fun n => BMS.kind (towerM n) == BMS.kind (StageA.oneRow (List.range (n+1))))
#guard (List.range 4).all (fun n => (List.range 4).all (fun k =>
         BMS.expand (towerM n) k == (BMS.expand (StageA.oneRow (List.range (n+1))) k).map (· ++ [0])))

/-! ## §10 The CNF sequence map, and the expansion identity  (STAGE 2c)

`sq t` is the one-row BM4 sequence of a Cantor normal form: `0` goes to the empty
sequence, a formal sum concatenates, and `ω^β` becomes a BLOCK — a `0` followed by
`sq β` with every entry raised by one.  It is the inverse of `Evidence/StageA`'s
`oV` on the region we need, but nothing below depends on that: the whole section
speaks about `sq` directly.

NO STANDARDNESS PREDICATE.  `StageA.expand_oneRow` asks only for the syntactic
decomposition `s = (A ++ B) ++ [c]` with `B = b0 :: B'`, `b0 < c` and `c ≤ x` for
every `x ∈ B'` — not for `stdSeq`.  `sq_decomp` produces exactly that
decomposition for every CNF limit, by induction on the term, and reads off the
same induction that `A ++ B·(n+1) = sq (fsC t n)`.  So the expansion identity
comes out with no invariant to propagate, which is what makes Stage 2c a section
rather than a project.  (The same phenomenon is visible in the Isabelle PrSS
development koteitan pointed at: its `omap` is total on raw sequences and its
termination proof carries no standardness predicate either.)

THE THREE CASES of `sq_decomp` mirror the three cases of `fsC` exactly:

  ξ ⊕ ρ      the decomposition of `ρ` with `sq ξ` glued onto its `A`
  ω^(β+1)    A = [], B = `sq (ω^β)`, c = 1 — the bad part is the whole block, and
             `n+1` copies of it are `sq (ω^β·(n+1))`
  ω^β, β lim the decomposition of `β` with every entry raised by one and a `0`
             prefixed — the bad root moves right by exactly one place -/

open Evidence.WF (CN kindC predC fsC repAdd)

/-- The one-row BM4 sequence of a CNF term. -/
def sq : Term → List Nat
  | zero => []
  | add u v => sq u ++ sq v
  | phi _ b => 0 :: (sq b).map (· + 1)
  | _ => []

theorem sq_add (u v : Term) : sq (add u v) = sq u ++ sq v := rfl
theorem sq_phi (a b : Term) : sq (phi a b) = 0 :: (sq b).map (· + 1) := rfl
theorem sq_one : sq one = [0] := rfl

theorem sq_repAdd (w : Term) : ∀ n, sq (repAdd w n) = StageA.repL (sq w) (n + 1)
  | 0 => by
    show sq w = sq w ++ StageA.repL (sq w) 0
    rw [show StageA.repL (sq w) 0 = [] from rfl, List.append_nil]
  | n + 1 => by
    show sq w ++ sq (repAdd w n) = sq w ++ StageA.repL (sq w) (n + 1)
    rw [sq_repAdd w n]

/-- A CNF successor's sequence ends in a `0`, and dropping it is the predecessor. -/
theorem sq_predC : ∀ (b : Term), CN b = true → kindC b = true →
    sq b = sq (predC b) ++ [0] := by
  intro b
  induction b with
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | zero => intro _ hk; exact Bool.noConfusion hk
  | phi x y _ _ =>
    intro hcn hk
    have hy : y = zero := by
      have hh : (y == zero) = true := hk
      simpa using hh
    subst hy
    rfl
  | add u v _ ihv =>
    intro hcn hk
    obtain ⟨_, _, hcnv, _⟩ := Evidence.WF.cn_add hcn
    have hkv : kindC v = true := hk
    show sq u ++ sq v = sq (if (v == one) = true then u else add u (predC v)) ++ [0]
    by_cases hv : (v == one) = true
    · rw [if_pos hv]
      have hveq : v = one := by simpa using hv
      rw [hveq]
      rfl
    · rw [if_neg hv]
      show sq u ++ sq v = (sq u ++ sq (predC v)) ++ [0]
      rw [ihv hcnv hkv, List.append_assoc]

/-- **The decomposition `StageA.expand_oneRow` asks for, for every CNF limit.** -/
theorem sq_decomp : ∀ (t : Term), CN t = true → kindC t = false → t ≠ zero →
    ∃ (A B : List Nat) (c b0 : Nat) (B' : List Nat),
      sq t = (A ++ B) ++ [c] ∧ B = b0 :: B' ∧ b0 < c ∧ (∀ x ∈ B', c ≤ x) ∧ c ≠ 0
        ∧ ∀ n, A ++ StageA.repL B (n + 1) = sq (fsC t n) := by
  intro t
  induction t with
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | zero => intro _ _ hz; exact absurd rfl hz
  | phi x b _ ihb =>
    intro hcn hk _
    have hx : x = zero := (Evidence.WF.cn_phi hcn).1
    have hcnb : CN b = true := (Evidence.WF.cn_phi hcn).2
    subst hx
    have hy : (b == zero) = false := hk
    have hbz : b ≠ zero := by intro h; rw [h] at hy; exact Bool.noConfusion hy
    by_cases hkb : kindC b = true
    · refine ⟨[], 0 :: (sq (predC b)).map (· + 1), 1, 0, (sq (predC b)).map (· + 1),
        ?_, rfl, by omega, ?_, by omega, ?_⟩
      · show 0 :: (sq b).map (· + 1) = ([] ++ (0 :: (sq (predC b)).map (· + 1))) ++ [1]
        rw [sq_predC b hcnb hkb]
        simp
      · intro y hy'
        obtain ⟨z, _, hz⟩ := List.mem_map.mp hy'
        omega
      · intro n
        rw [Evidence.WF.fsC_phi_succ hy hkb, sq_repAdd]
        show [] ++ StageA.repL (0 :: (sq (predC b)).map (· + 1)) (n + 1)
            = StageA.repL (0 :: (sq (predC b)).map (· + 1)) (n + 1)
        rw [List.nil_append]
    · have hkb' : kindC b = false := by simpa using hkb
      obtain ⟨A, B, c, b0, B', h1, h2, h3, h4, h5, h6⟩ := ihb hcnb hkb' hbz
      refine ⟨0 :: A.map (· + 1), B.map (· + 1), c + 1, b0 + 1, B'.map (· + 1),
        ?_, ?_, by omega, ?_, by omega, ?_⟩
      · show 0 :: (sq b).map (· + 1)
            = ((0 :: A.map (· + 1)) ++ B.map (· + 1)) ++ [c + 1]
        rw [h1]
        simp
      · rw [h2]; rfl
      · intro y hy'
        obtain ⟨z, hz, hzy⟩ := List.mem_map.mp hy'
        have := h4 z hz
        omega
      · intro n
        rw [Evidence.WF.fsC_phi_lim hy hkb']
        show (0 :: A.map (· + 1)) ++ StageA.repL (B.map (· + 1)) (n + 1)
            = 0 :: (sq (fsC b n)).map (· + 1)
        rw [← StageA.repL_map, ← h6 n, List.map_append]
        rfl
  | add u v _ ihv =>
    intro hcn hk _
    obtain ⟨_, _, hcnv, hdesc⟩ := Evidence.WF.cn_add hcn
    have hkv : kindC v = false := hk
    have hvz : v ≠ zero := by intro h; rw [h] at hdesc; exact Bool.noConfusion hdesc
    obtain ⟨A, B, c, b0, B', h1, h2, h3, h4, h5, h6⟩ := ihv hcnv hkv hvz
    refine ⟨sq u ++ A, B, c, b0, B', ?_, h2, h3, h4, h5, ?_⟩
    · show sq u ++ sq v = ((sq u ++ A) ++ B) ++ [c]
      rw [h1, List.append_assoc, List.append_assoc, List.append_assoc]
    · intro n
      show (sq u ++ A) ++ StageA.repL B (n + 1) = sq u ++ sq (fsC v n)
      rw [← h6 n, List.append_assoc]

/-! ### §10.1 The BM4 side of a CNF term -/

theorem getLast?_oneRow_concat (s : List Nat) (c : Nat) :
    (StageA.oneRow (s ++ [c])).getLast? = some [c] := by
  rw [StageA.oneRow_append]
  exact List.getLast?_concat

/-- **The expansion of a CNF LIMIT is the sequence of its fundamental sequence.** -/
theorem expand_sq (t : Term) (hcn : CN t = true) (hk : kindC t = false) (hz : t ≠ zero)
    (n : Nat) :
    BMS.expand? (StageA.oneRow (sq t)) n = some (StageA.oneRow (sq (fsC t n))) := by
  obtain ⟨A, B, c, b0, B', h1, h2, h3, h4, h5, h6⟩ := sq_decomp t hcn hk hz
  rw [h1, StageA.expand_oneRow h2 h3 h4 h5 n, h6]

theorem kind_sq_lim (t : Term) (hcn : CN t = true) (hk : kindC t = false) (hz : t ≠ zero) :
    BMS.kind (StageA.oneRow (sq t)) = .lim := by
  obtain ⟨A, B, c, b0, B', h1, h2, h3, h4, h5, _⟩ := sq_decomp t hcn hk hz
  show (match (StageA.oneRow (sq t)).getLast? with
        | none => BMS.Kind.zero
        | some L => match BMS.lnz L with | none => BMS.Kind.succ | some _ => BMS.Kind.lim)
      = BMS.Kind.lim
  rw [h1, getLast?_oneRow_concat]
  cases c with
  | zero => exact absurd rfl h5
  | succ k => rfl

/-- **The expansion of a CNF SUCCESSOR drops the trailing `0`.** -/
theorem expand_sq_succ (t : Term) (hcn : CN t = true) (hk : kindC t = true) (n : Nat) :
    BMS.expand? (StageA.oneRow (sq t)) n = some (StageA.oneRow (sq (predC t))) := by
  have hsq := sq_predC t hcn hk
  have hL : (StageA.oneRow (sq t)).getLast? = some [0] := by
    rw [hsq]; exact getLast?_oneRow_concat _ _
  have hdl : (StageA.oneRow (sq t)).dropLast = StageA.oneRow (sq (predC t)) := by
    rw [hsq, StageA.oneRow_append]
    show (StageA.oneRow (sq (predC t)) ++ [[0]]).dropLast = StageA.oneRow (sq (predC t))
    exact List.dropLast_concat
  show (do
    let L ← (StageA.oneRow (sq t)).getLast?
    match BMS.lnz L with
    | none => pure (StageA.oneRow (sq t)).dropLast
    | some t' => _) = _
  simp only [hL, Option.bind_eq_bind, Option.bind_some,
    show BMS.lnz ([0] : List Nat) = none from rfl, Option.pure_def]
  rw [hdl]

theorem kind_sq_succ (t : Term) (hcn : CN t = true) (hk : kindC t = true) :
    BMS.kind (StageA.oneRow (sq t)) = .succ := by
  have hsq := sq_predC t hcn hk
  show (match (StageA.oneRow (sq t)).getLast? with
        | none => BMS.Kind.zero
        | some L => match BMS.lnz L with | none => BMS.Kind.succ | some _ => BMS.Kind.lim)
      = BMS.Kind.succ
  rw [hsq, getLast?_oneRow_concat]
  rfl

/-! ## §11 THE CNF CERTIFICATE FAMILY  (STAGE 2c, completed)

    cert_sq : ∀ t, CN t = true → Certified (StageA.oneRow (sq t)) t

Every Cantor normal form below ε₀ carries a certificate, by well-founded recursion
on `Evidence.WF.acc_cn`.  The three constructors of `Certified` line up with the
three cases of `Evidence.WF.kindC`:

  * `t = 0`      — `sq 0 = []`, the empty matrix, `Certified.zero`.
  * `t` successor — `kind_sq_succ` + `expand_sq_succ` + the recursion at `predC t`
    (below `t` by `Evidence.WF.lt_predC`), and `plus_predC` turns the `plus (predC t) 1`
    that `Certified.succ` produces back into `t`.
  * `t` limit     — `kind_sq_lim` + `expand_sq` + the recursion at `fsC t n` (below
    `t` by `Evidence.WF.lt_fsC`), with all four order premises supplied verbatim by
    `Evidence.WF.lim_clauses`.

This is the theorem the whole lane was for: it subsumes §2's `cert_zeros`, §3's
`cert_omega`, §5's `cert_wm`, §5.7's `cert_wv` and §5.14's `cert_q` — those are its
instances at levels 0–3 — and, unlike them, it is not bounded by a level. -/

/-- `1 ≤ ω^β` for every `β`. -/
theorem le_one_pow (e : Term) : le one (phi zero e) = true := by
  by_cases hz : e = zero
  · subst hz; exact Evidence.WF.le_self _
  · show ((one == phi zero e) || lt one (phi zero e)) = true
    rw [show lt one (phi zero e) = lt zero e from Evidence.WF.lt_pow zero e,
      show lt zero e = true from
        Evidence.WF.ltF_left_zero (by show 1 ≤ 2 * ((zero : Term).deg + e.deg) + 8; omega) hz]
    exact Bool.or_true _

/-- The components of a Cantor normal form are all `≥ 1`. -/
theorem le_one_of_mem_cn : ∀ (s : Term), CN s = true → ∀ a ∈ toList s, le one a = true := by
  intro s
  induction s with
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | zero => intro _ a ha; exact absurd ha (by simp [toList])
  | phi x y _ _ =>
    intro hcn a ha
    have hx : x = zero := (Evidence.WF.cn_phi hcn).1
    subst hx
    have : a = phi zero y := by
      have : a ∈ [phi zero y] := ha
      simpa using this
    subst this
    exact le_one_pow y
  | add u v _ ihv =>
    intro hcn a ha
    obtain ⟨hpow, hcnu, hcnv, _⟩ := Evidence.WF.cn_add hcn
    obtain ⟨e, he⟩ := Evidence.WF.eq_pow_of_isPow hpow
    subst he
    rcases List.mem_cons.mp ha with h | h
    · subst h; exact le_one_pow e
    · exact ihv hcnv a h

/-- `Certified.succ` produces `plus (predC t) 1`; on a CNF successor that IS `t`. -/
theorem plus_predC : ∀ (t : Term), CN t = true → kindC t = true → plus (predC t) one = t := by
  intro t
  induction t with
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | zero => intro _ hk; exact Bool.noConfusion hk
  | phi x y _ _ =>
    intro hcn hk
    have hx : x = zero := (Evidence.WF.cn_phi hcn).1
    have hy : y = zero := by
      have hh : (y == zero) = true := hk
      simpa using hh
    subst hx; subst hy
    rfl
  | add u v _ ihv =>
    intro hcn hk
    obtain ⟨hpow, hcnu, hcnv, _⟩ := Evidence.WF.cn_add hcn
    obtain ⟨e, he⟩ := Evidence.WF.eq_pow_of_isPow hpow
    subst he
    have hkv : kindC v = true := hk
    show plus (if (v == one) = true then phi zero e else add (phi zero e) (predC v)) one
        = add (phi zero e) v
    by_cases hv : (v == one) = true
    · rw [if_pos hv]
      have hveq : v = one := by simpa using hv
      subst hveq
      show ofList (([phi zero e] : List Term).filter (fun a => le one a) ++ [one]) = _
      rw [List.filter_cons_of_pos (le_one_pow e)]
      rfl
    · rw [if_neg hv]
      show ofList (((phi zero e :: toList (predC v)).filter (fun a => le one a)) ++ [one])
          = add (phi zero e) v
      rw [List.filter_cons_of_pos (le_one_pow e), List.cons_append,
        ofList_cons (by simp)]
      show add (phi zero e) (ofList ((toList (predC v)).filter (fun a => le one a) ++ [one])) = _
      rw [show ofList ((toList (predC v)).filter (fun a => le one a) ++ [one])
            = plus (predC v) one from rfl, ihv hcnv hkv]

/-- **THE CNF CERTIFICATE FAMILY.** -/
theorem cert_sq : ∀ (t : Term), CN t = true → Certified (StageA.oneRow (sq t)) t := by
  have key : ∀ (t : Term), Acc Evidence.WF.RC t → CN t = true →
      Certified (StageA.oneRow (sq t)) t := by
    intro t ht
    induction ht with
    | intro t _ ih =>
      intro hcn
      by_cases hz : t = zero
      · subst hz; exact Certified.zero
      by_cases hk : kindC t = true
      · have hcnp : CN (predC t) = true := Evidence.WF.cn_predC t hcn hk
        have hltp : lt (predC t) t = true := Evidence.WF.lt_predC t hcn hk
        have hpred : Certified (StageA.oneRow (sq (predC t))) (predC t) :=
          ih (predC t) ⟨hcnp, hltp⟩ hcnp
        have hres : Certified (StageA.oneRow (sq t)) (plus (predC t) one) :=
          Certified.succ (kind_sq_succ t hcn hk) (fun n => by
            show Certified ((BMS.expand? (StageA.oneRow (sq t)) n).getD []) (predC t)
            rw [expand_sq_succ t hcn hk n]
            exact hpred)
        rw [plus_predC t hcn hk] at hres
        exact hres
      · have hk' : kindC t = false := by simpa using hk
        obtain ⟨hcnfs, hltfs, hstep, hcof⟩ := Evidence.WF.lim_clauses t hcn hk' hz
        refine Certified.lim (fsC t) (kind_sq_lim t hcn hk' hz) (fun n => ?_) hltfs hstep hcof
        show Certified ((BMS.expand? (StageA.oneRow (sq t)) n).getD []) (fsC t n)
        rw [expand_sq t hcn hk' hz n]
        exact ih (fsC t n) ⟨hcnfs n, hltfs n⟩ (hcnfs n)
  intro t hcn
  exact key t (Evidence.WF.acc_cn t hcn) hcn

/-! ## §12 THE ZERO-PADDED ROW — the pad is inert  (STAGE 2c)

The ε₀ row expands to the ZERO-PADDED matrices `(0,0)(1,0)…(n,0)`, not to the
one-row `(0)(1)…(n)` that §11 certifies, so the family has to be transported
across the pad.  It transports because the BM4 rule never looks at the second row:

  * `BMS.lnz [a,0] = BMS.lnz [a]` — the lowest NONZERO row of a padded column is
    still row 0 (or the column is all zero in both cases);
  * `BMS.parent` at row 0 reads only row-0 entries, so it is literally the same
    computation (`parent_padRow`);
  * the ascension amount vanishes: with the lowest nonzero row `t = 0`,
    `BMS.delta M r 0 y = 0` for EVERY `y` (`StageA.delta_zero`), so the padded
    entries are copied unchanged and the second row stays zero.

`expand_padRow` is therefore `StageA.expand_oneRow` with the block height raised
from 1 to 2, and it needs the same hypotheses and no others. -/

/-- The one-row matrix `s` with a second row of zeros. -/
def padRow (s : List Nat) : Matrix := s.map (fun a => [a, 0])

theorem padRow_append (u v : List Nat) : padRow (u ++ v) = padRow u ++ padRow v := by
  simp [padRow]

theorem length_padRow (s : List Nat) : (padRow s).length = s.length := List.length_map _

theorem ent_padRow : ∀ (s : List Nat) (p : Nat), BMS.ent (padRow s) p 0 = s.getD p 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | a :: t, p + 1 => by
    have h1 : BMS.ent (padRow (a :: t)) (p + 1) 0 = BMS.ent (padRow t) p 0 := by
      show ((([a, 0] : List Nat) :: padRow t).getD (p + 1) []).getD 0 0
          = ((padRow t).getD p []).getD 0 0
      simp
    rw [h1, ent_padRow t p, List.getD_cons_succ]

theorem ent_padRow_one : ∀ (s : List Nat) (p : Nat), BMS.ent (padRow s) p 1 = 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | a :: t, p + 1 => by
    have h1 : BMS.ent (padRow (a :: t)) (p + 1) 1 = BMS.ent (padRow t) p 1 := by
      show ((([a, 0] : List Nat) :: padRow t).getD (p + 1) []).getD 1 0
          = ((padRow t).getD p []).getD 1 0
      simp
    rw [h1, ent_padRow_one t p]

theorem padRow_repL (B : List Nat) : ∀ k, padRow (StageA.repL B k) = Trans.repM (padRow B) k
  | 0 => rfl
  | k + 1 => by
    show padRow (B ++ StageA.repL B k) = padRow B ++ Trans.repM (padRow B) k
    rw [padRow_append, padRow_repL B k]

/-- The bad root is computed from row 0 alone, so the pad does not move it. -/
theorem parent_padRow (s : List Nat) (x : Nat) :
    BMS.parent (padRow s) 0 x = BMS.parent (StageA.oneRow s) 0 x := by
  show ((List.range x).filter
      (fun p => decide (BMS.ent (padRow s) p 0 < BMS.ent (padRow s) x 0))).max?
    = ((List.range x).filter
      (fun p => decide (BMS.ent (StageA.oneRow s) p 0
        < BMS.ent (StageA.oneRow s) x 0))).max?
  simp only [ent_padRow, StageA.ent_oneRow]

/-- **`StageA.expand_oneRow` for the padded row.** -/
theorem expand_padRow {A B : List Nat} {c b0 : Nat} {B' : List Nat}
    (hB : B = b0 :: B') (hb0 : b0 < c) (hrest : ∀ x ∈ B', c ≤ x) (hc : c ≠ 0) (n : Nat) :
    BMS.expand? (padRow ((A ++ B) ++ [c])) n = some (padRow (A ++ StageA.repL B (n + 1))) := by
  have hBlen : B.length = B'.length + 1 := by rw [hB]; simp
  have hL : (padRow ((A ++ B) ++ [c])).getLast? = some [c, 0] := by
    rw [padRow_append]
    exact List.getLast?_concat
  have hlnz : BMS.lnz [c, 0] = some 0 := by
    cases c with
    | zero => exact absurd rfl hc
    | succ k => rfl
  have hlength : (padRow ((A ++ B) ++ [c])).length = (StageA.oneRow ((A ++ B) ++ [c])).length := by
    rw [length_padRow, StageA.length_oneRow]
  have hpar : BMS.parent (padRow ((A ++ B) ++ [c])) 0
      ((padRow ((A ++ B) ++ [c])).length - 1) = some A.length := by
    rw [hlength, parent_padRow]
    exact StageA.parent_oneRow hB hb0 hrest
  have hlen : (padRow ((A ++ B) ++ [c])).length - 1 - A.length = B.length := by
    rw [length_padRow, List.length_append, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega
  have htake : List.take A.length (padRow ((A ++ B) ++ [c])) = padRow A := by
    rw [List.append_assoc, padRow_append, ← length_padRow A]
    exact List.take_left
  have hgd : ∀ x, x < B.length → ((A ++ B) ++ [c]).getD (A.length + x) 0 = B.getD x 0 := by
    intro x hx
    rw [StageA.getD_append_lt (A ++ B) [c] (A.length + x) (by rw [List.length_append]; omega),
        StageA.getD_append_ge A B (A.length + x) (by omega)]
    congr 1
    omega
  have hblk : List.map (fun x => List.map
        (fun y => BMS.ent (padRow ((A ++ B) ++ [c])) (A.length + x) y)
        (List.range ([c, 0] : List Nat).length)) (List.range B.length) = padRow B := by
    have h1 : ∀ x ∈ List.range B.length,
        List.map (fun y => BMS.ent (padRow ((A ++ B) ++ [c])) (A.length + x) y)
          (List.range ([c, 0] : List Nat).length) = [B.getD x 0, 0] := by
      intro x hx
      have hx' : x < B.length := List.mem_range.mp hx
      show [BMS.ent (padRow ((A ++ B) ++ [c])) (A.length + x) 0,
            BMS.ent (padRow ((A ++ B) ++ [c])) (A.length + x) 1] = [B.getD x 0, 0]
      rw [ent_padRow, ent_padRow_one, hgd x hx']
    rw [List.map_congr_left h1]
    show (List.range B.length).map (fun x => [B.getD x 0, 0]) = B.map (fun a => [a, 0])
    calc (List.range B.length).map (fun x => [B.getD x 0, 0])
        = ((List.range B.length).map (fun x => B.getD x 0)).map (fun a => [a, 0]) := by
          rw [List.map_map]; rfl
      _ = (B.take B.length).map (fun a => [a, 0]) := by
          rw [StageA.range_map_getD B.length B (Nat.le_refl _)]
      _ = B.map (fun a => [a, 0]) := by rw [List.take_length]
  simp only [BMS.expand?, hL, Option.bind_eq_bind, Option.bind_some, hlnz, hpar, Option.pure_def,
    StageA.delta_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
  rw [hlen, htake, hblk, Trans.flat_range, ← padRow_repL, ← padRow_append]

/-! ### §12.1 The padded CNF family -/

theorem getLast?_padRow_concat (s : List Nat) (c : Nat) :
    (padRow (s ++ [c])).getLast? = some [c, 0] := by
  rw [padRow_append]
  exact List.getLast?_concat

theorem expand_padSq (t : Term) (hcn : CN t = true) (hk : kindC t = false) (hz : t ≠ zero)
    (n : Nat) :
    BMS.expand? (padRow (sq t)) n = some (padRow (sq (fsC t n))) := by
  obtain ⟨A, B, c, b0, B', h1, h2, h3, h4, h5, h6⟩ := sq_decomp t hcn hk hz
  rw [h1, expand_padRow h2 h3 h4 h5 n, h6]

theorem kind_padSq_lim (t : Term) (hcn : CN t = true) (hk : kindC t = false) (hz : t ≠ zero) :
    BMS.kind (padRow (sq t)) = .lim := by
  obtain ⟨A, B, c, b0, B', h1, h2, h3, h4, h5, _⟩ := sq_decomp t hcn hk hz
  show (match (padRow (sq t)).getLast? with
        | none => BMS.Kind.zero
        | some L => match BMS.lnz L with | none => BMS.Kind.succ | some _ => BMS.Kind.lim)
      = BMS.Kind.lim
  rw [h1, getLast?_padRow_concat]
  cases c with
  | zero => exact absurd rfl h5
  | succ k => rfl

theorem expand_padSq_succ (t : Term) (hcn : CN t = true) (hk : kindC t = true) (n : Nat) :
    BMS.expand? (padRow (sq t)) n = some (padRow (sq (predC t))) := by
  have hsq := sq_predC t hcn hk
  have hL : (padRow (sq t)).getLast? = some [0, 0] := by
    rw [hsq]; exact getLast?_padRow_concat _ _
  have hdl : (padRow (sq t)).dropLast = padRow (sq (predC t)) := by
    rw [hsq, padRow_append]
    show (padRow (sq (predC t)) ++ [[0, 0]]).dropLast = padRow (sq (predC t))
    exact List.dropLast_concat
  show (do
    let L ← (padRow (sq t)).getLast?
    match BMS.lnz L with
    | none => pure (padRow (sq t)).dropLast
    | some t' => _) = _
  simp only [hL, Option.bind_eq_bind, Option.bind_some,
    show BMS.lnz ([0, 0] : List Nat) = none from rfl, Option.pure_def]
  rw [hdl]

theorem kind_padSq_succ (t : Term) (hcn : CN t = true) (hk : kindC t = true) :
    BMS.kind (padRow (sq t)) = .succ := by
  have hsq := sq_predC t hcn hk
  show (match (padRow (sq t)).getLast? with
        | none => BMS.Kind.zero
        | some L => match BMS.lnz L with | none => BMS.Kind.succ | some _ => BMS.Kind.lim)
      = BMS.Kind.succ
  rw [hsq, getLast?_padRow_concat]
  rfl

/-- **The padded CNF certificate family** — `cert_sq` transported across the pad. -/
theorem cert_padSq : ∀ (t : Term), CN t = true → Certified (padRow (sq t)) t := by
  have key : ∀ (t : Term), Acc Evidence.WF.RC t → CN t = true →
      Certified (padRow (sq t)) t := by
    intro t ht
    induction ht with
    | intro t _ ih =>
      intro hcn
      by_cases hz : t = zero
      · subst hz; exact Certified.zero
      by_cases hk : kindC t = true
      · have hcnp : CN (predC t) = true := Evidence.WF.cn_predC t hcn hk
        have hltp : lt (predC t) t = true := Evidence.WF.lt_predC t hcn hk
        have hpred : Certified (padRow (sq (predC t))) (predC t) :=
          ih (predC t) ⟨hcnp, hltp⟩ hcnp
        have hres : Certified (padRow (sq t)) (plus (predC t) one) :=
          Certified.succ (kind_padSq_succ t hcn hk) (fun n => by
            show Certified ((BMS.expand? (padRow (sq t)) n).getD []) (predC t)
            rw [expand_padSq_succ t hcn hk n]
            exact hpred)
        rw [plus_predC t hcn hk] at hres
        exact hres
      · have hk' : kindC t = false := by simpa using hk
        obtain ⟨hcnfs, hltfs, hstep, hcof⟩ := Evidence.WF.lim_clauses t hcn hk' hz
        refine Certified.lim (fsC t) (kind_padSq_lim t hcn hk' hz) (fun n => ?_) hltfs hstep hcof
        show Certified ((BMS.expand? (padRow (sq t)) n).getD []) (fsC t n)
        rw [expand_padSq t hcn hk' hz n]
        exact ih (fsC t n) ⟨hcnfs n, hltfs n⟩ (hcnfs n)
  intro t hcn
  exact key t (Evidence.WF.acc_cn t hcn) hcn

/-! ## §13 ε₀ — THE ROW `(0,0)(1,1)`  (STAGE 3)

The first TWO-ROW row of the table with a real checkmark, and the first row whose
value is not in the one-row region.

    cert_eps0 : Certified [[0,0],[1,1]] (φ̄10)

Everything it needs is now a theorem:

  `kind_eps0_row`                 (§9)   the row is a limit row
  `expand_eps0_row`               (§9)   its expansions are the padded towers
  `cert_padSq` + `sq_tower`       (§12)  each of those is certified, with value `tower n`
  `Evidence.WF.lt_tower_eps0`     (WF §9) the towers are below ε₀
  `Evidence.WF.lt_tower_step`     (WF §9) they increase
  `Evidence.WF.cof_eps0`          (WF §9) they are COFINAL among the terms of 𝔗(M) below ε₀

The last one is the only premise that is not a computation, and it is the one that
makes the certificate a semantic claim rather than a bookkeeping identity. -/

theorem sq_tower : ∀ n, sq (Evidence.WF.tower n) = List.range (n + 1)
  | 0 => rfl
  | n + 1 => by
    have h : List.range (n + 1 + 1) = 0 :: (List.range (n + 1)).map Nat.succ :=
      List.range_succ_eq_map
    show 0 :: (sq (Evidence.WF.tower n)).map (· + 1) = List.range (n + 1 + 1)
    rw [h, sq_tower n]

theorem towerM_eq (n : Nat) : towerM n = padRow (sq (Evidence.WF.tower n)) := by
  rw [sq_tower n]
  rfl

/-- Every expansion of the ε₀ row is certified, with the ω-tower as its value. -/
theorem cert_tower (n : Nat) : Certified (towerM n) (Evidence.WF.tower n) := by
  rw [towerM_eq n]
  exact cert_padSq _ (Evidence.WF.cn_tower n)

/-- **ε₀.**  The row `(0,0)(1,1)` of the table, certified. -/
theorem cert_eps0 : Certified [[0, 0], [1, 1]] (phi one zero) := by
  refine Certified.lim Evidence.WF.tower kind_eps0_row (fun n => ?_)
    Evidence.WF.lt_tower_eps0 Evidence.WF.lt_tower_step Evidence.WF.cof_eps0
  show Certified ((BMS.expand? [[0, 0], [1, 1]] n).getD []) (Evidence.WF.tower n)
  rw [show (BMS.expand? [[0, 0], [1, 1]] n).getD [] = towerM n from expand_eps0_row n]
  exact cert_tower n

/-! ### §13.1 The negative control for the ε₀ row

The expansion MATRICES are forced (`expand_eps0_row` is a closed form for all n),
and `cert_tower` certifies each of them at value `tower n`.  An attempt to certify
a COMPRESSED value for `(0,0)(1,1)` — say ε₀·2 — that discharges the cofinality
clause with these values `fs' = tower` is refuted here: the witness is ε₀ itself —
a term of 𝔗(M), below ε₀·2, that no tower overtakes (clause 2.3.13(iii) sends
`φ̄10 ≤ δ` down the tower's exponent and never fires).  This is the §7 control
transposed to the new row, and — like `Evidence.WF.cof_eps0_needs_inT` — it is a
kernel-checked theorem, not a `#guard`.

CAVEAT (audit 2026-08-09): `Certified` has no value-uniqueness theorem yet, so
nothing in Lean forces a hypothetical wrong certificate to instantiate `fs'` with
`tower`; this control refutes exactly that instantiation, not
`¬ Certified [[0,0],[1,1]] (ε₀·2)` itself.  Closing that gap — uniqueness of the
certified value among `inT` terms — is the planned `cert_sound` meta-theorem
(plan/README.md).

CAVEAT DISCHARGED, for this row and upwards (certificate lane, same day):
§15's `neg_control_eps0_times_two_strong` is `¬ Certified [[0,0],[1,1]] (ε₀·2)`
itself, with no assumption on the competing certificate at all — and it is the
instance `u = ε₀·2` of `no_cert_above_eps0`, which refutes EVERY value above ε₀.
The theorem below is kept because it is the control at the level of the CLAUSE
(it is what a broken `lim` premise would make unprovable), and because §15's proof
consumes it in spirit: the witness there is again ε₀ itself. -/

theorem ltF_eps0_tower : ∀ (n f : Nat), ltF f (phi one zero) (Evidence.WF.tower n) = false := by
  intro n
  induction n with
  | zero =>
    intro f
    cases f with
    | zero => rfl
    | succ g =>
      show (if ((phi one zero) == one) = true then false
            else if ((one : Term) == zero) = true then ltF g zero zero
            else if ltF g one zero = true then ltF g zero one
            else (((phi one zero) == zero) || ltF g (phi one zero) zero)) = false
      rw [if_neg (by intro hc; exact Bool.noConfusion hc),
        if_neg (by intro hc; exact Bool.noConfusion hc), ltF_lt_zero]
      simp only [Bool.false_eq_true, if_false]
      rw [ltF_lt_zero]
      rfl
  | succ n ih =>
    intro f
    cases f with
    | zero => rfl
    | succ g =>
      show (if ((phi one zero) == Evidence.WF.tower (n + 1)) = true then false
            else if ((one : Term) == zero) = true then ltF g zero (Evidence.WF.tower n)
            else if ltF g one zero = true then ltF g zero (Evidence.WF.tower (n + 1))
            else (((phi one zero) == Evidence.WF.tower n)
                  || ltF g (phi one zero) (Evidence.WF.tower n))) = false
      rw [if_neg (by intro hc; exact Bool.noConfusion hc),
        if_neg (by intro hc; exact Bool.noConfusion hc), ltF_lt_zero]
      simp only [Bool.false_eq_true, if_false]
      rw [ih g, show ((phi one zero == Evidence.WF.tower n) : Bool) = false from by
        cases n <;> rfl]
      rfl

/-- No tower overtakes ε₀. -/
theorem le_eps0_tower (n : Nat) : le (phi one zero) (Evidence.WF.tower n) = false := by
  show ((phi one zero == Evidence.WF.tower n) || lt (phi one zero) (Evidence.WF.tower n)) = false
  rw [show lt (phi one zero) (Evidence.WF.tower n) = false from ltF_eps0_tower n _,
    show ((phi one zero == Evidence.WF.tower n) : Bool) = false from by cases n <;> rfl]
  rfl

/-- **The negative control for the ε₀ row, machine-checked.**  The cofinality
    clause that a certificate `Certified [[0,0],[1,1]] (ε₀·2)` would need — when
    instantiated with the expansion values `fs' n = tower n` that `cert_tower`
    provides — is FALSE: ε₀ is a term of 𝔗(M) below ε₀·2 that no `fs' n`
    overtakes.  (Value-uniqueness making this the only instantiation is the
    planned `cert_sound` meta-theorem; see the §13.1 header.) -/
theorem neg_control_eps0_times_two :
    ¬ (∀ s, inT s = true → lt s (add (phi one zero) (phi one zero)) = true →
        ∃ n, le s (Evidence.WF.tower n) = true) := by
  intro hcof
  obtain ⟨n, hn⟩ := hcof (phi one zero) (by decide) (by decide)
  rw [le_eps0_tower n] at hn
  exact Bool.noConfusion hn

/-! ### §13.2 Evidence -/

#guard BMS.kind [[0, 0], [1, 1]] == BMS.Kind.lim
#guard (List.range 5).all (fun n => BMS.expand [[0, 0], [1, 1]] n == towerM n)
#guard inT (phi one zero) == true
#guard lt (phi one zero) (add (phi one zero) (phi one zero)) == true
#guard (List.range 12).all (fun n => le (phi one zero) (Evidence.WF.tower n) == false)

/-! ## §14 UNIQUENESS OF THE CERTIFIED VALUE  (`cert_sound`, part 1)
    (certificate lane, 2026-08-09)

THE GAP THIS CLOSES, AND THE ONE IT DOES NOT.  Until now `Certified M t` was an
EXISTENCE statement: the table's ✅ said "this value fits", not "this value and no
other".  §13.1's caveat is exactly that.  This section proves single-valuedness —
but the honest statement needs one restriction, and the restriction is forced:

  **`Certified` is NOT single-valued on the raw type `Term`.**  §8's junk term
  `1 + M` is below ω and above every finite term, so `Certified [[0],[1]] (add one M)`
  discharges all four `lim` clauses with the very same `fs' n = ofNat (n+1)` that
  `cert_omega` uses (the cofinality clause quantifies over `inT` terms, and the
  only ones below `1 + M` are `0` and `1`).  See `junk_omega_row` in §14.5 — it is
  a THEOREM, not a `#guard`.  So no theorem of the form
  `Certified M t → Certified M u → t = u` can be true, and design input 2 of
  plan/README.md ("quantify over `inT` terms, not raw terms") is not a stylistic
  preference: it is the difference between a true and a false statement.

WHERE THE `inT` GUARD HAS TO SIT.  The obvious repair — hypothesise `inT t` and
`inT u` on the two top values — is NOT enough: the `lim` case compares `t` with `u`
through the two expansion families, and the induction hypothesis is about the
values of the SUB-derivations, which the constructors do not constrain at all.  So
the guard has to hold ALL THE WAY DOWN.  Rather than change `Certified` (that would
invalidate every certificate in this file), §14.1 defines the guarded predicate
`CertifiedIn Dom` — the same three clauses with `Dom` demanded of every value —
together with the forgetful map `certifiedIn_forget : CertifiedIn Dom M t → Certified M t`.
`CertifiedIn` is a NEW definition; `Certified` is untouched.

WHAT EACH HYPOTHESIS OF `cert_unique_in` IS FOR (the audit trail asked for):

  `hdz`   `Dom 0`         — only to give `Dom (fs' k)` when the k-th expansion is
                            certified by the `zero` constructor (which carries no
                            `Dom`, its value being forced).
  `hinT`  `Dom a → inT a` — consumed EXACTLY TWICE, and only in the `lim` case: to
                            feed `t` to `u`'s cofinality clause and `u` to `t`'s.
                            This is the `inT` guard of design input 2.
  `hcomp` comparability   — `lim` case only: it turns "neither is below the other"
                            into `t = u`.
  `hlelt` `≤ ∘ <  ⊆  <`   — `lim` case only: with `lt_irrefl` it converts
                            `t ≤ fs' k` (from cofinality) and `fs' k < t` (from the
                            boundedness clause) into `t < t`.
  NOTHING                 — the `zero` and `succ` cases consume no order fact at
                            all.  `zero`: both values are `0` because `kind [] = .zero`
                            excludes the other two constructors.  `succ`: `BMS.kind M`
                            is a FUNCTION of `M`, so both derivations end in the same
                            constructor, and the induction hypothesis at the 0-th
                            expansion gives `t' = u'`, hence `plus t' 1 = plus u' 1`
                            — no injectivity of `plus` is needed.

§14.3 discharges the four hypotheses on `Dom = DomF := Frag2 ∧ inT`, where §8.2 of
`Evidence/WF.lean` proves comparability and `≤∘<⊆<` with NO `inT` needed, and §14.4
shows the region is not empty: the whole CNF family, and with it the ε₀ row, carries
GUARDED certificates, so `certIn_eps0_unique` reads

    every `DomF`-guarded certificate of `(0,0)(1,1)` has value ε₀ — and no other.

WHERE THIS SITS IN THE LITERATURE (added 2026-08-09, after koteitan identified it).
This section and §15 are the Lean instance of condition (a) of P進大好きbot's
命題10, 「変換写像による解析」.  The correspondence with that article is exact:

    (b) cof = 0 case                   ↔  `Certified.zero`
    (c) cof = 1 case                   ↔  `Certified.succ` (value `plus t' 1`)
    (d) cof = ω case                   ↔  `Certified.lim` (increasing, bounded, cofinal)
    (e) dom = min(cof, 2)              ↔  the `BMS.kind` trichotomy
    (a) Trans restricted to the standard forms is a BIJECTION onto an ordinal
                                       ↔  NOTHING, before this section

He records that for Bashicu matrices (b)(c)(d) are easy while (a) is 極めて困難,
and that injectivity is normally reduced to UNIQUENESS OF A NORMAL-FORM
REPRESENTATION.  §15.9's `cert_not_single_valued` is a machine-checked
demonstration that (b)(c)(d) really do not imply (a) — the ω row satisfies all
three with two different values — and `DomF` is exactly that prescribed reduction
to normal forms.  These theorems are therefore not extra rigour: they are the
condition the literature flags as the hard one.

WHAT IS STILL OPEN (updated 2026-08-09, after Stage 3b landed in `Evidence/WF.lean`
§8.5).  Uniqueness is now discharged on `DomI` (§14.3a) — the registry gate's own
guard — so the open set has shrunk to exactly one shape: A CERTIFICATE THAT FAILS
THE GATE, i.e. one whose values leave 𝔗(M) somewhere below the top, could still in
principle carry a value BELOW the registered one.  Two things are worth knowing
about that remainder rather than leaving a reader to guess:

  * §15's ceiling covers exactly those certificates FROM ABOVE, unconditionally, so
    the gap is one-sided.
  * The mixed-transitivity lemma the ψ/Z lane proved on this lane's request
    (`Evidence.WF.lt_of_le_of_lt_mixed`) does NOT close it, and it is worth saying
    why instead of letting the name suggest otherwise: that lemma requires `inT` on
    the MIDDLE term, and the middle term in the missing step is exactly a value that
    is not in 𝔗(M).  Its hypothesis fails precisely where it would be used.  Closing
    the last shape needs transitivity with a genuinely unconstrained middle, which
    the ψ/Z lane reports as swept without counterexample but NOT proved. -/

/-! ### §14.1 Guarded certificates -/

/-- `Certified` with every certified value in `Dom`.  The `zero` clause needs no
    guard: its value is forced.  `Certified` itself is untouched — see the §14 header. -/
inductive CertifiedIn (Dom : Term → Prop) : Matrix → Term → Prop
  | zero : CertifiedIn Dom [] Term.zero
  | succ {M : Matrix} {t : Term} :
      BMS.kind M = .succ →
      (∀ n, CertifiedIn Dom (BMS.expand M n) t) →
      Dom (plus t one) →
      CertifiedIn Dom M (plus t one)
  | lim {M : Matrix} {t : Term} (fs' : Nat → Term) :
      BMS.kind M = .lim →
      (∀ n, CertifiedIn Dom (BMS.expand M n) (fs' n)) →
      (∀ n, lt (fs' n) t = true) →
      (∀ n, lt (fs' n) (fs' (n + 1)) = true) →
      (∀ s, inT s = true → lt s t = true → ∃ n, le s (fs' n) = true) →
      Dom t →
      CertifiedIn Dom M t

/-- A guarded certificate is a certificate: nothing is gained by the guard except
    the guard itself. -/
theorem certifiedIn_forget {Dom : Term → Prop} :
    ∀ {M : Matrix} {t : Term}, CertifiedIn Dom M t → Certified M t := by
  intro M t h
  induction h with
  | zero => exact Certified.zero
  | succ hk _ _ ih => exact Certified.succ hk ih
  | lim fs hk _ hlt hstep hcof _ ih => exact Certified.lim fs hk ih hlt hstep hcof

/-- The guard can always be WEAKENED.  This is what makes the choice of guard a
    late decision rather than an early one: a certificate guarded by `DomF`
    (`Frag2 ∧ inT`, where the order theory lives today) is in particular guarded by
    `DomI` (`inT` alone, what the doctrine asks for and what will still make sense
    when the table reaches the `ψ`/`Z` rows, whose values are NOT in `Frag2`). -/
theorem certifiedIn_mono {Dom Dom' : Term → Prop} (himp : ∀ t, Dom t → Dom' t) :
    ∀ {M : Matrix} {t : Term}, CertifiedIn Dom M t → CertifiedIn Dom' M t := by
  intro M t h
  induction h with
  | zero => exact CertifiedIn.zero
  | succ hk _ hd ih => exact CertifiedIn.succ hk ih (himp _ hd)
  | lim fs hk _ hlt hstep hcof hd ih => exact CertifiedIn.lim fs hk ih hlt hstep hcof (himp _ hd)

/-- The empty matrix is a zero row — this is what makes the `zero` case of the
    uniqueness induction, and the two constructor-clash cases, go through. -/
theorem kind_nil : BMS.kind ([] : Matrix) = .zero := rfl

theorem dom_of_certifiedIn {Dom : Term → Prop} (hdz : Dom Term.zero) :
    ∀ {M : Matrix} {t : Term}, CertifiedIn Dom M t → Dom t := by
  intro M t h
  cases h with
  | zero => exact hdz
  | succ _ _ hd => exact hd
  | lim _ _ _ _ _ _ hd => exact hd

/-! ### §14.2 THE UNIQUENESS THEOREM, abstract in the order facts -/

/-- **`Certified` is single-valued on `Dom`.**  See the §14 header for what each
    hypothesis is consumed by; `hinT`, `hcomp` and `hlelt` are used ONLY in the
    `lim` case, and `hdz` only to produce `Dom` for a sub-value certified by `zero`. -/
theorem cert_unique_in {Dom : Term → Prop}
    (hdz : Dom Term.zero)
    (hinT : ∀ {a : Term}, Dom a → inT a = true)
    (hcomp : ∀ {a b : Term}, Dom a → Dom b → lt a b = true ∨ a = b ∨ lt b a = true)
    (hlelt : ∀ {a b c : Term}, Dom a → Dom b → Dom c →
        le a b = true → lt b c = true → lt a c = true) :
    ∀ {M : Matrix} {t : Term}, CertifiedIn Dom M t →
      ∀ {u : Term}, CertifiedIn Dom M u → t = u := by
  intro M t h
  induction h with
  | zero =>
    intro u h2
    cases h2 with
    | zero => rfl
    | succ hk _ _ => rw [kind_nil] at hk; exact absurd hk (by simp)
    | lim _ hk _ _ _ _ _ => rw [kind_nil] at hk; exact absurd hk (by simp)
  | @succ M t hk _ _ ih =>
    intro u h2
    cases h2 with
    | zero => rw [kind_nil] at hk; exact absurd hk (by simp)
    | succ _ hall2 _ => rw [ih 0 (hall2 0)]
    | lim _ hk2 _ _ _ _ _ => rw [hk] at hk2; exact absurd hk2 (by simp)
  | @lim M t fs' hk hall hlt hstep hcof hd ih =>
    intro u h2
    cases h2 with
    | zero => rw [kind_nil] at hk; exact absurd hk (by simp)
    | succ hk2 _ _ => rw [hk] at hk2; exact absurd hk2 (by simp)
    | @lim _ u fs'' hk2 hall2 hlt2 hstep2 hcof2 hd2 =>
      -- the two families agree pointwise: the induction hypothesis at each expansion
      have heq : ∀ n, fs' n = fs'' n := fun n => ih n (hall2 n)
      rcases hcomp hd hd2 with h | h | h
      · -- t < u : u's cofinality clause overtakes t at some k, but fs' k < t
        obtain ⟨k, hk'⟩ := hcof2 t (hinT hd) h
        rw [← heq k] at hk'
        have : lt t t = true :=
          hlelt hd (dom_of_certifiedIn hdz (hall k)) hd hk' (hlt k)
        rw [Evidence.WF.lt_irrefl] at this
        exact absurd this (by simp)
      · exact h
      · -- u < t : symmetric, through t's cofinality clause
        obtain ⟨k, hk'⟩ := hcof u (hinT hd2) h
        have hlt' : lt (fs' k) u = true := by rw [heq k]; exact hlt2 k
        have : lt u u = true :=
          hlelt hd2 (dom_of_certifiedIn hdz (hall k)) hd2 hk' hlt'
        rw [Evidence.WF.lt_irrefl] at this
        exact absurd this (by simp)

/-! ### §14.3 The discharge on `Frag2`

`Evidence/WF.lean` §8.2 proves comparability and `≤∘<⊆<` on `Frag2` — the φ̄-fragment
extended by `M` and `ω̄^·` — with NO `inT` hypothesis, so the only thing `DomF` adds
to `Frag2` is the `inT` guard that `hinT` needs.  This is the widest region today's
order theory supports: §8.2's MUTANT 2 (`frag2_stops_at_psi`) records that `ψ` is
exactly where the fragment stops. -/

/-- The concrete guard: the fragment carrying a linear order, plus the formation
    conditions of 𝔗(M). -/
def DomF (t : Term) : Prop := Evidence.WF.Frag2 t = true ∧ inT t = true

/-- The guard the DOCTRINE asks for (plan/README.md design input 2): the values are
    TERMS OF 𝔗(M), nothing more.  Uniqueness is not available on it yet — that needs
    a linear order on the values, i.e. `ψ`/`Z` order theory — but a registry gate
    stated with `DomI` keeps its meaning for every future row.  See §6.1. -/
def DomI (t : Term) : Prop := inT t = true

theorem domF_le_domI : ∀ (t : Term), DomF t → DomI t := fun _ h => h.2

/-! #### §14.3a THE DISCHARGE ON `DomI` — Stage 3b closes the undershoot
    (certificate lane, 2026-08-09, after `Evidence/WF.lean` §8.5)

When §14 was written the order theory reached only `Frag2`, so uniqueness had to be
discharged on `DomF = Frag2 ∧ inT`: a competing certificate was excluded only if its
values avoided `ψ` and `Z` as well as being terms of 𝔗(M).  `Evidence.WF.lt_trichotomy_inT`
now gives a strict LINEAR ORDER on 𝔗(M) itself, so the discharge runs on `DomI` — the
registry gate's own guard (§6) — and the theorem covers every certificate the registry
accepts, ψ/Z rows included.

THIS CLOSES THE UNDERSHOOT HALF that the §15 header named as open.  Uniqueness is
symmetric: the `lim` case refutes `lt t u` and `lt u t` by the same two lines, so ONE
comparability fact settles values above and below at once.  What §15 adds on top is
the UNGUARDED ceiling — certificates that fail the gate, where no comparability is
available at all.  `cert_unique_frag2` is now a corollary through `certifiedIn_mono`. -/

/-- **Single-valuedness on `DomI`** — the guard the registry gate uses: every value
    in the derivation is a term of 𝔗(M), nothing more.  All three order facts come
    from `Evidence/WF.lean` §8.5.4, which needs no fragment hypothesis. -/
theorem cert_unique_inT {M : Matrix} {t u : Term}
    (h1 : CertifiedIn DomI M t) (h2 : CertifiedIn DomI M u) : t = u :=
  cert_unique_in (Dom := DomI) rfl (fun h => h)
    (fun ha hb => Evidence.WF.lt_comparable_inT ha hb)
    (fun ha hb hc => Evidence.WF.lt_of_le_of_lt3 (Evidence.WF.inT_le_fragR _ ha)
      (Evidence.WF.inT_le_fragR _ hb) (Evidence.WF.inT_le_fragR _ hc)) h1 h2

/-- **Single-valuedness, unconditionally, on `DomF`** — now the `certifiedIn_mono`
    image of `cert_unique_inT`.  Kept verbatim: its statement is what §14.3's mutant
    discussion and the table legend were written against. -/
theorem cert_unique_frag2 {M : Matrix} {t u : Term}
    (h1 : CertifiedIn DomF M t) (h2 : CertifiedIn DomF M u) : t = u :=
  cert_unique_inT (certifiedIn_mono domF_le_domI h1) (certifiedIn_mono domF_le_domI h2)

/-! ### §14.4 The region is not empty: the CNF family is guarded

`cert_padSq` re-proved with the guard.  The only new obligation is `DomF` of each
value, and every value in that induction is a Cantor normal form: `Frag2` by
`frag_of_cn` + `frag_le_frag2`, and `inT` by `inT_of_cn` below (the formation
conditions 2.1(iii)/(v) are literally what `CN` demands, plus `β < M`, which holds
of every CNF term because a `φ̄` and a `⊕`-head are below `M` by clauses 2.3.2/2.3.10). -/

theorem ltF_cn_M : ∀ (t : Term), CN t = true → ∀ f, t.deg ≤ f → ltF f t M = true := by
  intro t
  induction t with
  | zero => intro _ f hf; cases f with | zero => simp [Term.deg] at hf | succ g => rfl
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | phi a b _ _ =>
    intro _ f hf
    cases f with
    | zero => simp [Term.deg] at hf
    | succ g => rfl
  | add a b iha _ =>
    intro hcn f hf
    obtain ⟨_, hca, _, _⟩ := Evidence.WF.cn_add hcn
    cases f with
    | zero => simp [Term.deg] at hf
    | succ g =>
      have hg : a.deg ≤ g := by
        have : (add a b).deg = 1 + a.deg + b.deg := rfl
        omega
      show (if (add a b == M) = true then false else ltF g a M) = true
      rw [show ((add a b == M) : Bool) = false from rfl]
      simpa using iha hca g hg

theorem lt_cn_M (t : Term) (h : CN t = true) : lt t M = true := by
  rw [Evidence.WF.lt_eq_ltF t M (t.deg + M.deg) (Nat.le_refl _)]
  exact ltF_cn_M t h _ (by omega)

/-- Every Cantor normal form satisfies the formation conditions of 𝔗(M). -/
theorem inT_of_cn : ∀ (t : Term), CN t = true → inT t = true := by
  intro t
  induction t with
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | zero => intro _; rfl
  | phi a b _ ihb =>
    intro hcn
    obtain ⟨ha, hb⟩ := Evidence.WF.cn_phi hcn
    subst ha
    show (inT zero && inT b && lt zero M && lt b M) = true
    rw [ihb hb, lt_cn_M b hb, show inT zero = true from rfl,
      show lt zero M = true from by
        rw [Evidence.WF.lt_eq_ltF zero M ((zero : Term).deg + M.deg) (Nat.le_refl _)]; rfl]
    rfl
  | add a b iha ihb =>
    intro hcn
    obtain ⟨hpow, hca, hcb, hhd⟩ := Evidence.WF.cn_add hcn
    obtain ⟨e, he⟩ := Evidence.WF.eq_pow_of_isPow hpow
    have hap : isAP a = true := by rw [he]; rfl
    cases b with
    | zero => exact Bool.noConfusion hhd
    | add c d =>
      show (isAP a && inT a && inT (add c d) && le c a) = true
      rw [hap, iha hca, ihb hcb, show le c a = true from hhd]; rfl
    | M => exact Bool.noConfusion hcb
    | omg _ => exact Bool.noConfusion hcb
    | psi _ _ => exact Bool.noConfusion hcb
    | Z _ => exact Bool.noConfusion hcb
    | phi x y =>
      have hx : x = zero := (Evidence.WF.cn_phi hcb).1
      subst hx
      show (isAP a && inT a && inT (phi zero y) && (isAP (phi zero y) && le (phi zero y) a)) = true
      rw [hap, iha hca, ihb hcb, show isAP (phi zero y) = true from rfl,
        show le (phi zero y) a = true from hhd]
      rfl

theorem domF_of_cn (t : Term) (h : CN t = true) : DomF t :=
  ⟨Evidence.WF.frag_le_frag2 t (Evidence.WF.frag_of_cn t h), inT_of_cn t h⟩

/-- **The padded CNF family, guarded** — `cert_padSq` with `DomF` at every value. -/
theorem certIn_padSq : ∀ (t : Term), CN t = true → CertifiedIn DomF (padRow (sq t)) t := by
  have key : ∀ (t : Term), Acc Evidence.WF.RC t → CN t = true →
      CertifiedIn DomF (padRow (sq t)) t := by
    intro t ht
    induction ht with
    | intro t _ ih =>
      intro hcn
      by_cases hz : t = zero
      · subst hz; exact CertifiedIn.zero
      by_cases hk : kindC t = true
      · have hcnp : CN (predC t) = true := Evidence.WF.cn_predC t hcn hk
        have hltp : lt (predC t) t = true := Evidence.WF.lt_predC t hcn hk
        have hpred : CertifiedIn DomF (padRow (sq (predC t))) (predC t) :=
          ih (predC t) ⟨hcnp, hltp⟩ hcnp
        have hres : CertifiedIn DomF (padRow (sq t)) (plus (predC t) one) :=
          CertifiedIn.succ (kind_padSq_succ t hcn hk) (fun n => by
            show CertifiedIn DomF ((BMS.expand? (padRow (sq t)) n).getD []) (predC t)
            rw [expand_padSq_succ t hcn hk n]
            exact hpred)
            (by rw [plus_predC t hcn hk]; exact domF_of_cn t hcn)
        rw [plus_predC t hcn hk] at hres
        exact hres
      · have hk' : kindC t = false := by simpa using hk
        obtain ⟨hcnfs, hltfs, hstep, hcof⟩ := Evidence.WF.lim_clauses t hcn hk' hz
        refine CertifiedIn.lim (fsC t) (kind_padSq_lim t hcn hk' hz) (fun n => ?_) hltfs hstep hcof
          (domF_of_cn t hcn)
        show CertifiedIn DomF ((BMS.expand? (padRow (sq t)) n).getD []) (fsC t n)
        rw [expand_padSq t hcn hk' hz n]
        exact ih (fsC t n) ⟨hcnfs n, hltfs n⟩ (hcnfs n)
  intro t hcn
  exact key t (Evidence.WF.acc_cn t hcn) hcn

theorem certIn_tower (n : Nat) : CertifiedIn DomF (towerM n) (Evidence.WF.tower n) := by
  rw [towerM_eq n]
  exact certIn_padSq _ (Evidence.WF.cn_tower n)

/-- **ε₀, guarded.**  `cert_eps0` with `DomF` at every value. -/
theorem certIn_eps0 : CertifiedIn DomF [[0, 0], [1, 1]] (phi one zero) := by
  refine CertifiedIn.lim Evidence.WF.tower kind_eps0_row (fun n => ?_)
    Evidence.WF.lt_tower_eps0 Evidence.WF.lt_tower_step Evidence.WF.cof_eps0 ⟨rfl, by decide⟩
  show CertifiedIn DomF ((BMS.expand? [[0, 0], [1, 1]] n).getD []) (Evidence.WF.tower n)
  rw [show (BMS.expand? [[0, 0], [1, 1]] n).getD [] = towerM n from expand_eps0_row n]
  exact certIn_tower n

/-- **THE ε₀ ROW HAS ONE GUARDED VALUE.**  Every certificate of `(0,0)(1,1)` whose
    values are terms of 𝔗(M) — the registry gate's condition — carries the value ε₀.
    (Stated on `DomF` when §14 was written; `DomI` since §14.3a, which is strictly
    stronger and is the guard the gate actually imposes.  The `DomF` case is the
    `certifiedIn_mono` image.) -/
theorem certIn_eps0_unique (u : Term) (h : CertifiedIn DomI [[0, 0], [1, 1]] u) :
    u = phi one zero :=
  (cert_unique_inT (certifiedIn_mono domF_le_domI certIn_eps0) h).symm

/-! ### §14.5 EVERY REGISTERED ROW, not just ε₀

`certIn_padSq` is the guarded family for the PADDED rows; the registry's other
eight rows are the unpadded one-row matrices of §11, so they need `cert_sq` with
the guard as well.  It is the same proof again — the only new obligation is `DomF`
of each value, and every value in that recursion is a Cantor normal form.

With both families, every matrix in `certRows` carries a GUARDED certificate, and
`cert_unique_frag2` turns each of them into a uniqueness statement.  That is the
table-level reading of §14: a ✅ in the proof column now means "this value and no
other" for every competing certificate that stays inside 𝔗(M) ∩ `Frag2`.  The two
registry theorems (`certIn_rows`, `certRows_unique_guarded`) live in §6.1, after
`certRows` itself — this section only supplies the family they run on. -/

/-- **The CNF family, guarded** — `cert_sq` with `DomF` at every value. -/
theorem certIn_sq : ∀ (t : Term), CN t = true →
    CertifiedIn DomF (StageA.oneRow (sq t)) t := by
  have key : ∀ (t : Term), Acc Evidence.WF.RC t → CN t = true →
      CertifiedIn DomF (StageA.oneRow (sq t)) t := by
    intro t ht
    induction ht with
    | intro t _ ih =>
      intro hcn
      by_cases hz : t = zero
      · subst hz; exact CertifiedIn.zero
      by_cases hk : kindC t = true
      · have hcnp : CN (predC t) = true := Evidence.WF.cn_predC t hcn hk
        have hltp : lt (predC t) t = true := Evidence.WF.lt_predC t hcn hk
        have hpred : CertifiedIn DomF (StageA.oneRow (sq (predC t))) (predC t) :=
          ih (predC t) ⟨hcnp, hltp⟩ hcnp
        have hres : CertifiedIn DomF (StageA.oneRow (sq t)) (plus (predC t) one) :=
          CertifiedIn.succ (kind_sq_succ t hcn hk) (fun n => by
            show CertifiedIn DomF ((BMS.expand? (StageA.oneRow (sq t)) n).getD []) (predC t)
            rw [expand_sq_succ t hcn hk n]
            exact hpred)
            (by rw [plus_predC t hcn hk]; exact domF_of_cn t hcn)
        rw [plus_predC t hcn hk] at hres
        exact hres
      · have hk' : kindC t = false := by simpa using hk
        obtain ⟨hcnfs, hltfs, hstep, hcof⟩ := Evidence.WF.lim_clauses t hcn hk' hz
        refine CertifiedIn.lim (fsC t) (kind_sq_lim t hcn hk' hz) (fun n => ?_) hltfs hstep hcof
          (domF_of_cn t hcn)
        show CertifiedIn DomF ((BMS.expand? (StageA.oneRow (sq t)) n).getD []) (fsC t n)
        rw [expand_sq t hcn hk' hz n]
        exact ih (fsC t n) ⟨hcnfs n, hltfs n⟩ (hcnfs n)
  intro t hcn
  exact key t (Evidence.WF.acc_cn t hcn) hcn

/-! ## §15 NO CERTIFICATE OVERSHOOTS  (`cert_sound`, part 2)
    (certificate lane, 2026-08-09)

§14 makes `Certified` single-valued on GUARDED certificates.  This section proves
the half of unqualified single-valuedness that today's order theory can reach, and
it is the half the table's ✅ needs most:

    no_cert_above_eps0 : ∀ u, lt ε₀ u = true → ¬ Certified [[0,0],[1,1]] u

— no hypothesis on `u` beyond being above ε₀, and NO hypothesis whatsoever on the
values inside the hypothetical certificate.  §15.10 generalises it off the ε₀ row:
`no_cert_above_pow` / `no_cert_above_pow_one` refute every value above `ω^t` for
EVERY limit row of the certified region, and `certRows_no_overshoot` states the
uniform consequence for the registry.  §13.1's caveat ("this control refutes
that instantiation, not `¬ Certified [[0,0],[1,1]] (ε₀·2)` itself") is thereby
retired for everything at or above ε₀·2; the ε₀ row's ✅ now means "this value, and
nothing bigger, whatever certificate you bring".

WHY ONLY THE UPPER HALF, HONESTLY.  Refuting a value BELOW ε₀ needs a lower bound
on the certified values of the expansions, i.e. a step
`s ≤ fs n` and `fs n < v`  ⟹  `s < v`, which chains THROUGH `fs n` — a value the
inductive does not constrain, so possibly junk carrying `ψ`/`Z`, where no
transitivity is available (WF §8.2 stops at `ψ`; that is Stage 3b).  The upper half
avoids this completely, and that is the design of the whole section:

    THE PROBE DISCIPLINE (a reusable technique, not a trick for this row).  Every
    statement below has the form `le s v = false` with the junk value `v` on the
    RIGHT.  The term `s` on the left is always one the PROOF chooses (`ω^(t+1)`,
    `ω^t`, ε₀ — all Cantor normal forms or ε₀), and the only order facts consumed
    relate two such chosen terms, inside `Frag`, where §7 of WF gives transitivity,
    asymmetry and comparability with no `inT`.  Nothing is ever chained through a
    certified value.  Any argument that has to bound what a certificate can do, in
    a region where the order theory does not yet cover every term, can be built
    this way: put the unconstrained object on the side of the relation that the
    decision procedure reads LAST, and quantify over probes you supply yourself.

    WHAT HAPPENED TO THE OTHER HALF (updated 2026-08-09, after Stage 3b).  This
    header used to record the missing lemma as

        le s x = true → lt x v = true → lt s v = true       (s, v in Frag2; x ARBITRARY)

    Stage 3b then delivered something better for the case that matters:
    `Evidence.WF.lt_trichotomy_inT`, a strict LINEAR ORDER on 𝔗(M) itself.  With it,
    §14.3a discharges uniqueness on `DomI`, and since uniqueness is symmetric that
    settles the undershoot AND the overshoot in one line — FOR CERTIFICATES THAT
    PASS THE GATE.  So the scope of this section changed: §15 is no longer "the half
    that is reachable", it is what survives for certificates that FAIL the gate,
    where the values leave 𝔗(M) and no comparability is available at all.

    The lemma quoted above is still missing, and the ψ/Z lane's `lt_of_le_of_lt_mixed`
    is NOT it: that lemma asks for `inT` on the middle term, and the middle term in
    the missing step is exactly a value outside 𝔗(M).  What §15 gives the fragment
    lane for free, in case it helps them attack the unconstrained version: a
    certified value of this region is never `ψ`-, `Z`-, `M`- or `ω̄`-headed, because
    every such term is above every `φ̄` term, so the probe `ω^(t+1)` would be `≤` it,
    which `no_overshoot` forbids.

THE INVARIANT (`no_overshoot_ceiling`, §15.7.2).  Given a region — a relation
`Reg M X` reading "`M` is a region matrix with bound-parameter `X`" whose parameters
are Veblen-fragment terms and whose expansions have STRICTLY SMALLER parameters — no
term of 𝔗(M) ∩ `Frag` that is additively principal and `≥ ω^(X+1)` is `≤` any value
certified for a region matrix.  The three cases:

  zero  `v = 0`, and no principal `s` is `≤ 0`.  Region-free.
  succ  `v = plus v' 1`.  `plus` filters out the components below `1`, so `v` has
        the SAME leftmost component as `v'` (`hd_plus_one`, via `cert_hd`), and a
        principal `s` compares with a sum only through that component
        (`le_ap_hd`) — so `le s v` and `le s v'` are the SAME Bool, and the
        induction hypothesis at the (constant) expansion closes the case.  The
        bound moves down with the parameter, by `le_bnd_of_lt_cnv`.
  lim   `v` carries a family `fs`.  If `s < v`, `v`'s own cofinality clause hands
        back a `k` with `s ≤ fs k`, and the induction hypothesis at `k` — whose
        bound `ω^(Y+1)` is `≤ ω^X ≤ s` for the smaller parameter `Y`
        (`le_bnd_of_lt_cnv`, i.e. `Evidence.WF.le_plus_one_of_lt_cnv`, WITH NO
        LIMIT HYPOTHESIS) — says exactly `le s (fs k) = false`.  If instead
        `s = v`, the same argument runs with the probe `ω^X`, which is STRICTLY
        below `ω^(X+1) ≤ v`.

  `no_overshoot` / `no_overshoot_one` (the CNF rows, §15.8) and `no_overshoot_fam`
  (Row A's ε₀-prefixed region, §19.2) are instances; neither runs an induction.

`cert_hd` (the shape lemma the succ case needs) is proved for `Certified` itself,
junk and all: the `lim` case gets it from `fs 1 ≠ 0` and the descent lemma
`hd_zero_of_lt`, which reads the clauses of `lt` and chains through nothing. -/

/-! ### §15.1 Clause bodies at a general additively principal term -/


theorem ltF_succ_ap_add (f : Nat) : ∀ {s : Term}, isAP s = true → ∀ (c d : Term),
    ltF (f + 1) s (add c d) = ((s == c) || ltF f s c)
  | zero, h, _, _ => Bool.noConfusion h
  | add _ _, h, _, _ => Bool.noConfusion h
  | M, _, _, _ => rfl
  | omg _, _, _, _ => rfl
  | phi _ _, _, _, _ => rfl
  | psi _ _, _, _, _ => rfl
  | Z _, _, _, _ => rfl

theorem ltF_succ_add_ap (f : Nat) (a b : Term) : ∀ {t : Term}, isAP t = true →
    ltF (f + 1) (add a b) t = ltF f a t
  | zero, h => Bool.noConfusion h
  | add _ _, h => Bool.noConfusion h
  | M, _ => rfl
  | omg _, _ => rfl
  | phi _ _, _ => rfl
  | psi _ _, _ => rfl
  | Z _, _ => rfl

theorem lt_ap_add {s : Term} (hs : isAP s = true) (c d : Term) : lt s (add c d) = le s c := by
  have hd := Evidence.WF.deg_pos d
  show ltF (fuelOf s (add c d)) s (add c d) = _
  rw [show fuelOf s (add c d) = (2 * (s.deg + (add c d).deg) + 7) + 1 from by
      show 2 * (s.deg + (add c d).deg) + 8 = _; omega,
    ltF_succ_ap_add _ hs c d]
  rw [show ltF (2 * (s.deg + (add c d).deg) + 7) s c = lt s c from
    (Evidence.WF.lt_eq_ltF s c _
      (by show s.deg + c.deg ≤ 2 * (s.deg + (1 + c.deg + d.deg)) + 7; omega)).symm]
  rfl

theorem le_ap_add {s : Term} (hs : isAP s = true) (c d : Term) : le s (add c d) = le s c := by
  show ((s == add c d) || lt s (add c d)) = _
  rw [lt_ap_add hs c d, show ((s == add c d) : Bool) = false from by
    cases s <;> first | exact Bool.noConfusion hs | rfl]
  rfl

theorem lt_add_ap (a b : Term) {t : Term} (ht : isAP t = true) : lt (add a b) t = lt a t := by
  have hb := Evidence.WF.deg_pos b
  show ltF (fuelOf (add a b) t) (add a b) t = _
  rw [show fuelOf (add a b) t = (2 * ((add a b).deg + t.deg) + 7) + 1 from by
      show 2 * ((add a b).deg + t.deg) + 8 = _; omega,
    ltF_succ_add_ap _ a b ht]
  exact (Evidence.WF.lt_eq_ltF a t _
    (by show a.deg + t.deg ≤ 2 * ((1 + a.deg + b.deg) + t.deg) + 7; omega)).symm

/-! ### §15.2 `1` is below every additively principal term -/

theorem ltF_succ_one_ap (f : Nat) (hf : 1 ≤ f) : ∀ {h : Term}, isAP h = true → h ≠ one →
    ltF (f + 1) one h = true := by
  intro h hap hne
  cases f with
  | zero => omega
  | succ g =>
    cases h with
    | zero => exact Bool.noConfusion hap
    | add _ _ => exact Bool.noConfusion hap
    | M => rfl
    | omg _ => rfl
    | psi k a =>
      show (if (one == psi k a) = true then false else (ltF (g + 1) zero (psi k a) &&
        ltF (g + 1) zero (psi k a))) = true
      rfl
    | Z a =>
      show (if (one == Z a) = true then false else (ltF (g + 1) zero (Z a) &&
        ltF (g + 1) zero (Z a))) = true
      rfl
    | phi c d =>
      show (if (one == phi c d) = true then false else
        (if (zero == c) = true then ltF (g + 1) zero d
         else if ltF (g + 1) zero c = true then ltF (g + 1) zero (phi c d)
         else (one == d) || ltF (g + 1) one d)) = true
      rw [show ((one == phi c d) : Bool) = false from by
        simp only [one, beq_eq_false_iff_ne, ne_eq]
        intro hc; injection hc with h1 h2; exact hne (by rw [← h1, ← h2]; rfl)]
      simp only [Bool.false_eq_true, if_false]
      by_cases hc : c = zero
      · subst hc
        rw [if_pos (show (((zero : Term) == zero) : Bool) = true from rfl)]
        have hd : d ≠ zero := by
          intro hdz; subst hdz; exact hne rfl
        cases d with
        | zero => exact absurd rfl hd
        | add _ _ => rfl
        | M => rfl
        | omg _ => rfl
        | phi _ _ => rfl
        | psi _ _ => rfl
        | Z _ => rfl
      · rw [if_neg (by simp only [beq_iff_eq]; exact fun hcc => hc hcc.symm)]
        rw [if_pos (by cases c with
          | zero => exact absurd rfl hc
          | add _ _ => rfl | M => rfl | omg _ => rfl | phi _ _ => rfl
          | psi _ _ => rfl | Z _ => rfl)]
        rfl

theorem le_one_ap {h : Term} (hap : isAP h = true) : le one h = true := by
  by_cases hne : h = one
  · subst hne; exact Evidence.WF.le_self one
  · show ((one == h) || lt one h) = true
    rw [show lt one h = true from by
      show ltF (fuelOf one h) one h = true
      have hh := Evidence.WF.deg_pos h
      rw [show fuelOf one h = (2 * ((one : Term).deg + h.deg) + 7) + 1 from by
        show 2 * ((one : Term).deg + h.deg) + 8 = _; omega]
      exact ltF_succ_one_ap _ (by omega) hap hne]
    exact Bool.or_true _

/-! ### §15.3 The leftmost component, and the descent lemma -/

/-- The leftmost non-`⊕` component of a formal sum. -/
def hd : Term → Term
  | add a _ => hd a
  | t => t

theorem hd_add (a b : Term) : hd (add a b) = hd a := rfl

theorem isAP_hd : ∀ (t : Term), hd t ≠ zero → isAP (hd t) = true
  | zero, h => absurd rfl h
  | M, _ => rfl
  | omg _, _ => rfl
  | phi _ _, _ => rfl
  | psi _ _, _ => rfl
  | Z _, _ => rfl
  | add a _, h => by rw [hd_add] at h ⊢; exact isAP_hd a h

/-- A principal term compares with a sum through the sum's leftmost component. -/
theorem le_ap_hd {s : Term} (hs : isAP s = true) : ∀ (v : Term), le s v = le s (hd v)
  | zero => rfl
  | M => rfl
  | omg _ => rfl
  | phi _ _ => rfl
  | psi _ _ => rfl
  | Z _ => rfl
  | add c d => by rw [hd_add, le_ap_add hs c d]; exact le_ap_hd hs c

/-- **The descent lemma.**  If anything is below `v` and `v`'s leftmost component is
    `0`, then that thing's leftmost component is `0` too.  Junk on the right is fine:
    the proof never chains through a term, it only reads clauses. -/
theorem hd_zero_of_lt : ∀ (v x : Term), lt x v = true → hd v = zero → hd x = zero
  | zero, x, h, _ => by
    rw [show lt x zero = false from Evidence.WF.ltF_right_zero _ x] at h
    exact Bool.noConfusion h
  | M, _, _, h => Term.noConfusion h
  | omg _, _, _, h => Term.noConfusion h
  | phi _ _, _, _, h => Term.noConfusion h
  | psi _ _, _, _, h => Term.noConfusion h
  | Z _, _, _, h => Term.noConfusion h
  | add c d, x, hlt, hz => by
    rw [hd_add] at hz
    by_cases hx : isAP x = true
    · rw [lt_ap_add hx c d] at hlt
      simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at hlt
      rcases hlt with rfl | h
      · exact hz
      · exact hd_zero_of_lt c x h hz
    · cases x with
      | zero => rfl
      | M => exact absurd rfl hx
      | omg _ => exact absurd rfl hx
      | phi _ _ => exact absurd rfl hx
      | psi _ _ => exact absurd rfl hx
      | Z _ => exact absurd rfl hx
      | add a b =>
        rw [hd_add]
        by_cases hab : add a b = add c d
        · injection hab with h1 _; rw [h1]; exact hz
        · rw [Evidence.WF.lt_add_add hab] at hlt
          by_cases hac : a = c
          · rw [hac]; exact hz
          · rw [if_neg hac] at hlt
            exact hd_zero_of_lt c a hlt hz

/-! ### §15.4 `t + 1` on Cantor normal forms -/

open Evidence.WF (isPow hdLe hdOf CNV)

theorem ofListCons {a : Term} : ∀ {l : List Term}, l ≠ [] → ofList (a :: l) = add a (ofList l)
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

theorem plus_one_eq (s : Term) :
    plus s one = ofList ((toList s).filter (fun a => le one a) ++ [one]) := rfl

theorem plus_one_ap {a : Term} (hap : isAP a = true) (h1 : le one a = true) :
    plus a one = add a one := by
  rw [plus_one_eq, TM.Term.toList_of_isAP hap, List.filter_cons_of_pos h1]
  rfl

theorem plus_one_add {a b : Term} (h1 : le one a = true) :
    plus (add a b) one = add a (plus b one) := by
  rw [plus_one_eq, plus_one_eq]
  show ofList (((a :: toList b).filter (fun x => le one x)) ++ [one]) = _
  rw [List.filter_cons_of_pos h1, List.cons_append, ofListCons (by simp)]

theorem hd_of_isAP : ∀ {a : Term}, isAP a = true → hd a = a
  | zero, h => Bool.noConfusion h
  | add _ _, h => Bool.noConfusion h
  | M, _ => rfl
  | omg _, _ => rfl
  | phi _ _, _ => rfl
  | psi _ _, _ => rfl
  | Z _, _ => rfl

theorem hd_hdOf : ∀ (v : Term), hd (hdOf v) = hd v
  | zero => rfl
  | M => rfl
  | omg _ => rfl
  | phi _ _ => rfl
  | psi _ _ => rfl
  | Z _ => rfl
  | add _ _ => rfl

/-- **The shape of `v + 1`**: `plus` filters out the components below `1`, so as
    soon as `v`'s leftmost component is `≥ 1` the head survives and `v+1` is a sum
    with the SAME head component.  True of junk `v` as well — no `inT` anywhere. -/
theorem plus_one_shape : ∀ {v : Term}, le one (hd v) = true →
    ∃ b, plus v one = add (hdOf v) b := by
  intro v
  cases v with
  | zero => intro h; exact absurd h (by decide)
  | M => intro h; exact ⟨one, plus_one_ap rfl h⟩
  | omg _ => intro h; exact ⟨one, plus_one_ap rfl h⟩
  | phi _ _ => intro h; exact ⟨one, plus_one_ap rfl h⟩
  | psi _ _ => intro h; exact ⟨one, plus_one_ap rfl h⟩
  | Z _ => intro h; exact ⟨one, plus_one_ap rfl h⟩
  | add c d =>
    intro h
    have hc : le one c = true := by
      rw [le_ap_hd (show isAP one = true from rfl) c]; exact h
    exact ⟨plus d one, plus_one_add hc⟩

theorem hd_plus_one {v : Term} (h : le one (hd v) = true) : hd (plus v one) = hd v := by
  obtain ⟨b, he⟩ := plus_one_shape h
  rw [he, hd_add, hd_hdOf]

theorem plus_one_ne_one {v : Term} (h : le one (hd v) = true) : plus v one ≠ one := by
  obtain ⟨b, he⟩ := plus_one_shape h
  rw [he]; intro hc; exact Term.noConfusion hc

theorem le_one_hd_cn : ∀ (t : Term), CN t = true → t ≠ zero → le one (hd t) = true := by
  intro t
  induction t with
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | zero => intro _ h; exact absurd rfl h
  | phi x y _ _ =>
    intro hcn _
    have hx : x = zero := (Evidence.WF.cn_phi hcn).1
    subst hx
    exact le_one_pow y
  | add a b iha _ =>
    intro hcn _
    obtain ⟨hpow, hca, _, _⟩ := Evidence.WF.cn_add hcn
    obtain ⟨e, he⟩ := Evidence.WF.eq_pow_of_isPow hpow
    rw [hd_add, he, hd_of_isAP (show isAP (phi zero e) = true from rfl)]
    exact le_one_pow e

/-- `t+1` on a CNF term: still a CNF term, a successor, with predecessor `t`. -/
theorem plus_one_cn : ∀ (t : Term), CN t = true →
    CN (plus t one) = true ∧ kindC (plus t one) = true ∧ predC (plus t one) = t := by
  intro t
  induction t with
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | zero => intro _; exact ⟨rfl, rfl, rfl⟩
  | phi x y _ _ =>
    intro hcn
    have hx : x = zero := (Evidence.WF.cn_phi hcn).1
    subst hx
    rw [plus_one_ap rfl (le_one_pow y)]
    refine ⟨?_, rfl, rfl⟩
    show (isPow (phi zero y) && CN (phi zero y) && CN one && hdLe one (phi zero y)) = true
    rw [show isPow (phi zero y) = true from rfl, hcn, show CN one = true from rfl,
      show hdLe one (phi zero y) = le one (phi zero y) from rfl, le_one_pow y]
    rfl
  | add a b _ ihb =>
    intro hcn
    obtain ⟨hpow, hca, hcb, hhd⟩ := Evidence.WF.cn_add hcn
    obtain ⟨e, he⟩ := Evidence.WF.eq_pow_of_isPow hpow
    have h1a : le one a = true := by rw [he]; exact le_one_pow e
    obtain ⟨ihcn, ihk, ihp⟩ := ihb hcb
    have hb0 : b ≠ zero := by intro hz; rw [hz] at hhd; exact Bool.noConfusion hhd
    have h1b : le one (hd b) = true := le_one_hd_cn b hcb hb0
    obtain ⟨w, hw⟩ := plus_one_shape h1b
    have hhdb : hdLe (plus b one) a = true := by
      rw [Evidence.WF.hdLe_eq _ a (by rw [hw]; intro hc; exact Term.noConfusion hc),
        hw, show hdOf (add (hdOf b) w) = hdOf b from rfl,
        ← Evidence.WF.hdLe_eq b a hb0]
      exact hhd
    rw [plus_one_add h1a]
    refine ⟨?_, ihk, ?_⟩
    · show (isPow a && CN a && CN (plus b one) && hdLe (plus b one) a) = true
      rw [hpow, hca, ihcn, hhdb]; rfl
    · show (if (plus b one == one) = true then a else add a (predC (plus b one))) = add a b
      rw [if_neg (by simp only [beq_iff_eq]; exact plus_one_ne_one h1b), ihp]

theorem le_self_plus_one : ∀ (t : Term), CN t = true → le t (plus t one) = true := by
  intro t
  induction t with
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | zero => intro _; rfl
  | phi x y _ _ =>
    intro hcn
    have hx : x = zero := (Evidence.WF.cn_phi hcn).1
    subst hx
    rw [plus_one_ap rfl (le_one_pow y), le_ap_add rfl]
    exact Evidence.WF.le_self _
  | add a b _ ihb =>
    intro hcn
    obtain ⟨hpow, _, hcb, _⟩ := Evidence.WF.cn_add hcn
    obtain ⟨e, he⟩ := Evidence.WF.eq_pow_of_isPow hpow
    rw [plus_one_add (show le one a = true from by rw [he]; exact le_one_pow e)]
    exact Evidence.WF.le_add_tail (ihb hcb)

/-- **A limit absorbs `+1`**: below a CNF limit there is room for a successor. -/
theorem le_plus_one_of_lt_lim {a t : Term} (hca : CN a = true) (hct : CN t = true)
    (hk : kindC t = false) (hlt : lt a t = true) : le (plus a one) t = true := by
  obtain ⟨hcn1, hk1, hp1⟩ := plus_one_cn a hca
  have hfa : Evidence.WF.Frag a = true := Evidence.WF.frag_of_cn a hca
  have hft : Evidence.WF.Frag t = true := Evidence.WF.frag_of_cn t hct
  have hf1 : Evidence.WF.Frag (plus a one) = true :=
    Evidence.WF.frag_plus hfa Evidence.WF.frag_one
  rcases Evidence.WF.lt_comparable hf1 hft with h | h | h
  · show ((plus a one == t) || lt (plus a one) t) = true
    rw [h]; exact Bool.or_true _
  · rw [h] at hk1; rw [hk1] at hk; exact Bool.noConfusion hk
  · have hle : le t a = true := by
      have := Evidence.WF.le_predC_of_lt (plus a one) hcn1 hk1 t (inT_of_cn t hct) h
      rwa [hp1] at this
    have hcon : lt t t = true := Evidence.WF.lt_of_le_of_lt hft hfa hft hle hlt
    rw [Evidence.WF.lt_irrefl] at hcon
    exact Bool.noConfusion hcon

/-! ### §15.5 The shape of a certified value -/

theorem plus_one_ne_zero (v : Term) : plus v one ≠ zero := by
  rw [plus_one_eq]
  cases h : (toList v).filter (fun a => le one a) with
  | nil => intro hc; exact Term.noConfusion hc
  | cons a l => rw [List.cons_append, ofListCons (by simp)]; intro hc; exact Term.noConfusion hc

/-- **Every certified value has a nonzero leftmost component** (or is `0`).
    `zero`: forced.  `succ`: `plus · 1` filters the `< 1` components away, so the
    head it produces is `≥ 1` whatever it started from.  `lim`: `fs 1` is nonzero
    (it is above `fs 0`), its leftmost component is nonzero by the induction
    hypothesis, and `hd_zero_of_lt` carries that up to `v`. -/
theorem cert_hd : ∀ {N : Matrix} {v : Term}, Certified N v → v = zero ∨ hd v ≠ zero := by
  intro N v h
  induction h with
  | zero => exact Or.inl rfl
  | @succ M t hk hall ih =>
    refine Or.inr ?_
    rcases ih 0 with hz | hz
    · rw [hz]
      show hd one ≠ zero
      intro hc; exact Term.noConfusion hc
    · rw [hd_plus_one (le_one_ap (isAP_hd t hz))]
      exact hz
  | @lim M v fs hk hall hlt hstep hcof ih =>
    refine Or.inr ?_
    have h1 : fs 1 ≠ zero := by
      intro hc
      have := hstep 0
      rw [hc, show lt (fs 0) zero = false from Evidence.WF.ltF_right_zero _ _] at this
      exact Bool.noConfusion this
    have h2 : hd (fs 1) ≠ zero := by
      rcases ih 1 with hz | hz
      · exact absurd hz h1
      · exact hz
    intro hz
    exact h2 (hd_zero_of_lt v (fs 1) (hlt 1) hz)

/-! ### §15.6 The region, and its three kinds -/

theorem sq_eq_nil : ∀ (t : Term), CN t = true → sq t = [] → t = zero := by
  intro t
  cases t with
  | zero => intro _ _; rfl
  | M => intro h; exact Bool.noConfusion h
  | omg _ => intro h; exact Bool.noConfusion h
  | psi _ _ => intro h; exact Bool.noConfusion h
  | Z _ => intro h; exact Bool.noConfusion h
  | phi x y => intro _ h; rw [sq_phi] at h; exact absurd h (by simp)
  | add u v =>
    intro hcn h
    obtain ⟨hpow, _, _, _⟩ := Evidence.WF.cn_add hcn
    obtain ⟨e, he⟩ := Evidence.WF.eq_pow_of_isPow hpow
    subst he
    rw [sq_add, sq_phi] at h
    exact absurd h (by simp)

theorem kindC_of_kind_succ {t : Term} (hcn : CN t = true)
    (hk : BMS.kind (padRow (sq t)) = .succ) : kindC t = true := by
  by_cases hz : t = zero
  · subst hz
    rw [show sq (zero : Term) = [] from rfl, show padRow [] = ([] : BMS.Matrix) from rfl,
      show BMS.kind ([] : BMS.Matrix) = .zero from rfl] at hk
    exact absurd hk (by simp)
  by_cases hkc : kindC t = true
  · exact hkc
  · have hk' : kindC t = false := by simpa using hkc
    rw [kind_padSq_lim t hcn hk' hz] at hk
    exact absurd hk (by simp)

theorem kindC_of_kind_lim {t : Term} (hcn : CN t = true)
    (hk : BMS.kind (padRow (sq t)) = .lim) : kindC t = false ∧ t ≠ zero := by
  by_cases hz : t = zero
  · subst hz
    rw [show sq (zero : Term) = [] from rfl, show padRow [] = ([] : BMS.Matrix) from rfl,
      show BMS.kind ([] : BMS.Matrix) = .zero from rfl] at hk
    exact absurd hk (by simp)
  by_cases hkc : kindC t = true
  · rw [kind_padSq_succ t hcn hkc] at hk
    exact absurd hk (by simp)
  · exact ⟨by simpa using hkc, hz⟩

/-! ### §15.7 THE CEILING: no certificate overshoots its bound

ONE induction BOUNDS a certificate in this file, and it is `no_overshoot_ceiling`
below; §15.8's CNF rows and §19's ε₀-prefixed family are instances of it, and neither
runs an induction of its own.  (The file's other inductions on the inductive are not
bounds: `cert_hd` reads a certified value's shape, and §14's three run on
`CertifiedIn` for uniqueness.)

WHAT THE CEILING ACTUALLY NEEDS FROM A REGION (§15.7.2).  A region is a relation
`Reg M X`, read "`M` is a region matrix whose bound-parameter is `X`", and the whole
interface is three facts:

    hcnv   the parameters are Veblen-fragment terms
    hsucc  if `kind M = .succ`, the 0-th expansion is again a region matrix, and its
           parameter is STRICTLY BELOW `X`
    hlim   if `kind M = .lim`, the same for every expansion

Nothing is asked at `kind M = .zero`: `Certified.zero` pins the value to `0` and no
additively principal probe is `≤ 0`, so that case is region-free.

WHAT THIS COST, AND WHAT IT BOUGHT — the four hypotheses of the old §15.7 interface
(kept below as `no_overshoot_of`, now a corollary) were

    hRsucc/hRlim   the kind of `R t` reads off `kindC t`
    hRes/hRel      the expansions of `R t` are the `R` of `predC t` / `fsC t n`

and every one of them names CNF-region machinery.  That machinery is not available
above the CNF region, and `kindC` is not merely unavailable but WRONG there: it
branches on the second Veblen argument alone, so `kindC ε₀ = true` — it calls ε₀ a
successor (§19's trap, `#guard`ed in WF §15.3).  An interface stated with `kindC`
therefore could not have been discharged on Row A's region at all.

THE POINT IS THAT THE CEILING NEVER NEEDED THE CLASSIFIER.  `kindC`/`predC`/`fsC`
are how the CNF region PRODUCES a strictly smaller parameter; the induction consumes
only the decrease.  Four hypotheses collapse to three, and none of the three mentions
a classifier, a predecessor operation or a fundamental sequence.

A SECOND CONJUNCT WENT THE SAME WAY, and it is worth recording because it was
load-bearing until an hour ago.  The old `lim` case closed with
`le_plus_one_of_lt_lim`, which asks that `t` be a LIMIT; the ceiling closes with
`Evidence.WF.le_plus_one_of_lt_cnv`, which does not.  So "t is a limit" was a
hypothesis the CNF region handed over for free — `hRlim` had already produced it —
and it was never needed.  Both are the same shape: a check that is free in a region
because the region degenerates it, and that must be PAID FOR outside.  Asking that
question at each hypothesis is what made the interface discharge on two regions
instead of one. -/

theorem cn_pow {t : Term} (h : CN t = true) : CN (phi zero t) = true := by
  show (((zero : Term) == zero) && CN t) = true; rw [h]; rfl

theorem frag_pow_cn {t : Term} (h : CN t = true) : Evidence.WF.Frag (phi zero t) = true :=
  Evidence.WF.frag_omegaPow (Evidence.WF.frag_of_cn t h)

theorem frag_bnd {t : Term} (h : CN t = true) :
    Evidence.WF.Frag (phi zero (plus t one)) = true :=
  Evidence.WF.frag_omegaPow (Evidence.WF.frag_plus (Evidence.WF.frag_of_cn t h)
    Evidence.WF.frag_one)

theorem le_pow_bnd {t : Term} (h : CN t = true) :
    le (phi zero t) (phi zero (plus t one)) = true :=
  Evidence.WF.le_pow (le_self_plus_one t h)

theorem le_pow_one_false {X : Term} (hX : X ≠ zero) : le (phi zero X) one = false := by
  show ((phi zero X == one) || lt (phi zero X) (phi zero zero)) = false
  rw [Evidence.WF.lt_pow, show lt X zero = false from Evidence.WF.ltF_right_zero _ X,
    show ((phi zero X == one) : Bool) = false from by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro hc; injection hc with _ h2; exact hX h2]
  rfl

theorem not_le_one {s t : Term} (hin : inT s = true) (hap : isAP s = true)
    (hb : le (phi zero (plus t one)) s = true) : le s one = false := by
  show ((s == one) || lt s one) = false
  rw [show lt s one = false from by
      cases h : lt s one with
      | false => rfl
      | true =>
        have hz := Evidence.WF.below_one s hin _ h
        rw [hz] at hap; exact Bool.noConfusion hap,
    show ((s == one) : Bool) = false from by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro hc
      rw [hc, le_pow_one_false (plus_one_ne_zero t)] at hb
      exact Bool.noConfusion hb]
  rfl

/-! #### §15.7.1 The bound arithmetic on the Veblen fragment

`ω^(X+1)` has to be a legitimate probe for a parameter `X` that is no longer a Cantor
normal form, so §15.4's `le_self_plus_one` (CN only) needs a `CNV` twin, and the six
one-liners after it are the probe's `Frag` / `inT` / order receipts.  These were §19's
private lemmas about `famV k c`; they are stated here about an arbitrary `CNV` term,
which is all §19 ever used them at. -/

/-- Every `CNV` term other than `0` has an additively principal leftmost component. -/
theorem le_one_hd_cnv : ∀ (t : Term), CNV t = true → t ≠ zero → le one (hd t) = true := by
  intro t
  induction t with
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | zero => intro _ h; exact absurd rfl h
  | phi x y _ _ => intro _ _; exact le_one_ap (show isAP (phi x y) = true from rfl)
  | add a b iha _ =>
    intro hcnv _
    obtain ⟨hap, hca, _, _⟩ := Evidence.WF.cnv_add hcnv
    rw [hd_add, hd_of_isAP hap]
    exact le_one_ap hap

/-- **`x ≤ x+1` on the Veblen fragment** — §15.4's `le_self_plus_one` off the CNF
    region.  The `add` step needs `CNV`'s own descending condition to know the tail
    is nonzero. -/
theorem le_self_plus_one_cnv : ∀ (t : Term), CNV t = true → le t (plus t one) = true := by
  intro t
  induction t with
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | zero => intro _; rfl
  | phi x y _ _ =>
    intro _
    rw [show plus (phi x y) one = add (phi x y) one from
      plus_one_ap rfl (le_one_ap (show isAP (phi x y) = true from rfl)), le_ap_add rfl]
    exact Evidence.WF.le_self _
  | add a b _ ihb =>
    intro hcnv
    obtain ⟨hap, _, hcb, hdb⟩ := Evidence.WF.cnv_add hcnv
    have hb0 : b ≠ zero := by
      intro hz; rw [hz] at hdb; exact Bool.noConfusion hdb
    rw [plus_one_add (le_one_ap hap)]
    exact Evidence.WF.le_add_tail (ihb hcb)

theorem hdOf_plus_one {b : Term} (h : le one (hd b) = true) :
    hdOf (plus b one) = hdOf b := by
  obtain ⟨w, hw⟩ := plus_one_shape h
  rw [hw]; rfl

/-- `t+1` stays in the Veblen fragment. -/
theorem cnv_plus_one : ∀ (t : Term), CNV t = true → CNV (plus t one) = true := by
  intro t
  induction t with
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | zero => intro _; rfl
  | phi x y _ _ =>
    intro hcnv
    rw [plus_one_ap rfl (le_one_ap (show isAP (phi x y) = true from rfl))]
    show (isAP (phi x y) && CNV (phi x y) && CNV one && Evidence.WF.hdLe one (phi x y)) = true
    rw [show isAP (phi x y) = true from rfl, hcnv, show CNV one = true from rfl,
      show Evidence.WF.hdLe one (phi x y) = le one (phi x y) from rfl,
      le_one_ap (show isAP (phi x y) = true from rfl)]
    rfl
  | add a b _ ihb =>
    intro hcnv
    obtain ⟨hap, hca, hcb, hdb⟩ := Evidence.WF.cnv_add hcnv
    have hb0 : b ≠ zero := by intro hz; rw [hz] at hdb; exact Bool.noConfusion hdb
    have h1b : le one (hd b) = true := le_one_hd_cnv b hcb hb0
    rw [plus_one_add (le_one_ap hap)]
    show (isAP a && CNV a && CNV (plus b one) && Evidence.WF.hdLe (plus b one) a) = true
    rw [hap, hca, ihb hcb,
      Evidence.WF.hdLe_eq _ a (plus_one_ne_zero b), hdOf_plus_one h1b,
      ← Evidence.WF.hdLe_eq b a hb0, hdb]
    rfl

theorem plus_one_ne_self : ∀ (t : Term), CNV t = true → t ≠ plus t one := by
  intro t
  induction t with
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | zero => intro _ h; exact TM.Term.noConfusion h
  | phi x y _ _ =>
    intro _
    rw [plus_one_ap rfl (le_one_ap (show isAP (phi x y) = true from rfl))]
    intro h; exact TM.Term.noConfusion h
  | add a b _ ihb =>
    intro hcnv
    obtain ⟨hap, _, hcb, hdb⟩ := Evidence.WF.cnv_add hcnv
    rw [plus_one_add (le_one_ap hap)]
    intro h
    injection h with _ h2
    exact ihb hcb h2

/-- `x < x+1` on the Veblen fragment. -/
theorem lt_self_plus_one_cnv (t : Term) (hcnv : CNV t = true) :
    lt t (plus t one) = true := by
  have hle := le_self_plus_one_cnv t hcnv
  simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at hle
  rcases hle with h | h
  · exact absurd h (plus_one_ne_self t hcnv)
  · exact h

theorem frag_pow_cnv {X : Term} (h : CNV X = true) : Evidence.WF.Frag (phi zero X) = true :=
  Evidence.WF.frag_omegaPow (Evidence.WF.frag_of_cnv _ h)

theorem frag_bnd_cnv {X : Term} (h : CNV X = true) :
    Evidence.WF.Frag (phi zero (plus X one)) = true :=
  Evidence.WF.frag_omegaPow (Evidence.WF.frag_of_cnv _ (cnv_plus_one _ h))

theorem inT_pow_cnv {X : Term} (h : CNV X = true) : inT (phi zero X) = true :=
  Evidence.WF.inT_of_cnv _ (by show (CNV zero && CNV X) = true; rw [h]; rfl)

theorem le_pow_bnd_cnv {X : Term} (h : CNV X = true) :
    le (phi zero X) (phi zero (plus X one)) = true :=
  Evidence.WF.le_pow (le_self_plus_one_cnv _ h)

theorem lt_pow_bnd_cnv {X : Term} (h : CNV X = true) :
    lt (phi zero X) (phi zero (plus X one)) = true := by
  rw [Evidence.WF.lt_pow]; exact lt_self_plus_one_cnv _ h

/-- The bound at a sub-parameter is below the bound at the parameter, whenever the
    sub-parameter is below.  This is the ONE place the ceiling's induction moves
    between two bounds, and `Evidence.WF.le_plus_one_of_lt_cnv` — which arrived
    WITHOUT the limit hypothesis the certificate lane asked for — is why it needs no
    kind classification of either parameter. -/
theorem le_bnd_of_lt_cnv {x y : Term} (hx : CNV x = true) (hy : CNV y = true)
    (h : lt x y = true) : le (phi zero (plus x one)) (phi zero y) = true :=
  Evidence.WF.le_pow (Evidence.WF.le_plus_one_of_lt_cnv hx hy h)

/-! #### §15.7.2 THE CEILING -/

/-- **NO CERTIFICATE OVERSHOOTS ITS BOUND** — the file's only induction on
    `Certified`, abstract in the region.

    `Reg M X` reads "`M` is a region matrix whose bound-parameter is `X`".  The three
    hypotheses are all the proof knows: the parameters are Veblen-fragment terms, and
    an expansion of a region matrix of nonzero kind is again a region matrix, with a
    STRICTLY SMALLER parameter.  Then every value certified for a region matrix —
    junk values included, with no `inT` and no fragment hypothesis on the value — is
    escaped by every term of 𝔗(M) ∩ `Frag` that is additively principal and at least
    `ω^(X+1)`.

    Nothing is required at `kind M = .zero`, and nothing anywhere is required about
    HOW the smaller parameter is found: no kind classifier, no predecessor operation,
    no fundamental sequence.  Those are how a particular region produces the decrease
    (§15.7.3 uses `kindC`/`predC`/`fsC`; §19 uses the family's own order facts), and
    the induction consumes only the decrease itself.

    The proof never chains through a certified value: junk appears only on the RIGHT
    of `le s v`, the probe `s` on the left is always one the proof chooses, and the
    only order facts used are between such probes (all inside `Frag`, §7 of WF). -/
theorem no_overshoot_ceiling (Reg : BMS.Matrix → Term → Prop)
    (hcnv : ∀ (M : BMS.Matrix) (X : Term), Reg M X → CNV X = true)
    (hsucc : ∀ (M : BMS.Matrix) (X : Term), Reg M X → BMS.kind M = .succ →
      ∃ Y, Reg (BMS.expand M 0) Y ∧ lt Y X = true)
    (hlim : ∀ (M : BMS.Matrix) (X : Term), Reg M X → BMS.kind M = .lim → ∀ (n : Nat),
      ∃ Y, Reg (BMS.expand M n) Y ∧ lt Y X = true) :
    ∀ {N : BMS.Matrix} {v : Term}, Certified N v →
    ∀ (X : Term), Reg N X →
      ∀ (s : Term), inT s = true → Evidence.WF.Frag s = true → isAP s = true →
        le (phi zero (plus X one)) s = true → le s v = false := by
  intro N v h
  induction h with
  | zero =>
    intro X _ s _ _ hap _
    show ((s == zero) || lt s zero) = false
    rw [show lt s zero = false from Evidence.WF.ltF_right_zero _ s,
      show ((s == zero) : Bool) = false from by
        cases s <;> first | exact Bool.noConfusion hap | rfl]
    rfl
  | @succ M w hk hall ih =>
    intro X hreg s hin hfr hap hb
    obtain ⟨Y, hregY, hltY⟩ := hsucc M X hreg hk
    have hcX : CNV X = true := hcnv M X hreg
    have hcY : CNV Y = true := hcnv _ Y hregY
    have hbY : le (phi zero (plus Y one)) s = true :=
      Evidence.WF.le_trans (frag_bnd_cnv hcY) (frag_bnd_cnv hcX) hfr
        (Evidence.WF.le_trans (frag_bnd_cnv hcY) (frag_pow_cnv hcX) (frag_bnd_cnv hcX)
          (le_bnd_of_lt_cnv hcY hcX hltY) (le_pow_bnd_cnv hcX)) hb
    have hiv : le s w = false := ih 0 Y hregY s hin hfr hap hbY
    rcases cert_hd (hall 0) with hzw | hzw
    · rw [hzw, show plus (zero : Term) one = one from rfl]
      exact not_le_one hin hap hb
    · rw [le_ap_hd hap (plus w one), hd_plus_one (le_one_ap (isAP_hd w hzw)),
        ← le_ap_hd hap w]
      exact hiv
  | @lim M v fs hk hall hlt hstep hcof ih =>
    intro X hreg s hin hfr hap hb
    have hcX : CNV X = true := hcnv M X hreg
    have key : ∀ (s' : Term), inT s' = true → Evidence.WF.Frag s' = true → isAP s' = true →
        le (phi zero X) s' = true → ∀ (n : Nat), le s' (fs n) = false := by
      intro s' hin' hfr' hap' hb' n
      obtain ⟨Y, hregY, hltY⟩ := hlim M X hreg hk n
      have hcY : CNV Y = true := hcnv _ Y hregY
      exact ih n Y hregY s' hin' hfr' hap'
        (Evidence.WF.le_trans (frag_bnd_cnv hcY) (frag_pow_cnv hcX) hfr'
          (le_bnd_of_lt_cnv hcY hcX hltY) hb')
    have hbt : le (phi zero X) s = true :=
      Evidence.WF.le_trans (frag_pow_cnv hcX) (frag_bnd_cnv hcX) hfr (le_pow_bnd_cnv hcX) hb
    cases hlev : le s v with
    | false => rfl
    | true =>
      exfalso
      simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at hlev
      rcases hlev with rfl | hlts
      · have hltv : lt (phi zero X) s = true :=
          Evidence.WF.lt_of_lt_of_le (frag_pow_cnv hcX) (frag_bnd_cnv hcX) hfr
            (lt_pow_bnd_cnv hcX) hb
        obtain ⟨n, hn⟩ := hcof (phi zero X) (inT_pow_cnv hcX) hltv
        rw [key (phi zero X) (inT_pow_cnv hcX) (frag_pow_cnv hcX) rfl
          (Evidence.WF.le_self _) n] at hn
        exact Bool.noConfusion hn
      · obtain ⟨n, hn⟩ := hcof s hin hlts
        rw [key s hin hfr hap hbt n] at hn
        exact Bool.noConfusion hn

/-! #### §15.7.3 The CNF region, as an instance -/

/-- **NO CERTIFICATE OF A CNF REGION OVERSHOOTS ITS BOUND** — the statement this
    section had before the ceiling existed, now derived from it.  `R` assigns a
    matrix to every Cantor normal form, and the four hypotheses say the kind of `R t`
    reads off `kindC t` and the expansions of `R t` are the `R` of `predC t` /
    `fsC t n`.

    Discharging the ceiling's interface from them is the whole proof, and it is where
    the CNF region's degeneracies are spent: `predC t + 1 = t` gives the successor
    step's decrease, `Evidence.WF.lim_clauses` gives the limit step's, and the
    limit-hypothesis conjunct that `hRlim` supplies is DISCARDED — §15.7's header
    records why that is the interesting half of the exchange. -/
theorem no_overshoot_of (R : Term → BMS.Matrix)
    (hRsucc : ∀ (t : Term), CN t = true → BMS.kind (R t) = .succ → kindC t = true)
    (hRlim : ∀ (t : Term), CN t = true → BMS.kind (R t) = .lim → kindC t = false ∧ t ≠ zero)
    (hRes : ∀ (t : Term), CN t = true → kindC t = true → ∀ n, BMS.expand (R t) n = R (predC t))
    (hRel : ∀ (t : Term), CN t = true → kindC t = false → t ≠ zero → ∀ n,
        BMS.expand (R t) n = R (fsC t n)) :
    ∀ {N : BMS.Matrix} {v : Term}, Certified N v →
    ∀ (t : Term), CN t = true → N = R t →
      ∀ (s : Term), inT s = true → Evidence.WF.Frag s = true → isAP s = true →
        le (phi zero (plus t one)) s = true → le s v = false := by
  intro N v hc t hcn hN
  refine no_overshoot_ceiling (fun M X => CN X = true ∧ M = R X) ?_ ?_ ?_ hc t ⟨hcn, hN⟩
  · intro M X hr
    exact Evidence.WF.cnv_of_cn X hr.1
  · intro M X hr hk
    obtain ⟨h, hM⟩ := hr
    subst hM
    have hkc := hRsucc X h hk
    have hcp : CN (predC X) = true := Evidence.WF.cn_predC X h hkc
    refine ⟨predC X, ⟨hcp, hRes X h hkc 0⟩, ?_⟩
    have hlt : lt (predC X) (plus (predC X) one) = true :=
      lt_self_plus_one_cnv _ (Evidence.WF.cnv_of_cn _ hcp)
    rwa [plus_predC X h hkc] at hlt
  · intro M X hr hk n
    obtain ⟨h, hM⟩ := hr
    subst hM
    obtain ⟨hkc, hz⟩ := hRlim X h hk
    obtain ⟨hcnfs, hltfs, _, _⟩ := Evidence.WF.lim_clauses X h hkc hz
    exact ⟨fsC X n, ⟨hcnfs n, hRel X h hkc hz n⟩, hltfs n⟩


/-- The two regions this file certifies: the PADDED rows (`cert_padSq`, the ε₀
    row's expansions) and the unpadded one-row matrices (`cert_sq`, eight of the
    nine registered rows).  Same invariant, same proof — only the four region facts
    of §11/§12 change. -/
theorem no_overshoot : ∀ {N : BMS.Matrix} {v : Term}, Certified N v →
    ∀ (t : Term), CN t = true → N = padRow (sq t) →
      ∀ (s : Term), inT s = true → Evidence.WF.Frag s = true → isAP s = true →
        le (phi zero (plus t one)) s = true → le s v = false :=
  no_overshoot_of (fun t => padRow (sq t))
    (fun _ hcn hk => kindC_of_kind_succ hcn hk)
    (fun _ hcn hk => kindC_of_kind_lim hcn hk)
    (fun t hcn hkc n => by
      show (BMS.expand? (padRow (sq t)) n).getD [] = _
      rw [expand_padSq_succ t hcn hkc n]; rfl)
    (fun t hcn hkc hz n => by
      show (BMS.expand? (padRow (sq t)) n).getD [] = _
      rw [expand_padSq t hcn hkc hz n]; rfl)

theorem kindC_of_kind_succ_one {t : Term} (hcn : CN t = true)
    (hk : BMS.kind (StageA.oneRow (sq t)) = .succ) : kindC t = true := by
  by_cases hz : t = zero
  · subst hz
    rw [show sq (zero : Term) = [] from rfl,
      show StageA.oneRow [] = ([] : BMS.Matrix) from rfl,
      show BMS.kind ([] : BMS.Matrix) = .zero from rfl] at hk
    exact absurd hk (by simp)
  by_cases hkc : kindC t = true
  · exact hkc
  · have hk' : kindC t = false := by simpa using hkc
    rw [kind_sq_lim t hcn hk' hz] at hk
    exact absurd hk (by simp)

theorem kindC_of_kind_lim_one {t : Term} (hcn : CN t = true)
    (hk : BMS.kind (StageA.oneRow (sq t)) = .lim) : kindC t = false ∧ t ≠ zero := by
  by_cases hz : t = zero
  · subst hz
    rw [show sq (zero : Term) = [] from rfl,
      show StageA.oneRow [] = ([] : BMS.Matrix) from rfl,
      show BMS.kind ([] : BMS.Matrix) = .zero from rfl] at hk
    exact absurd hk (by simp)
  by_cases hkc : kindC t = true
  · rw [kind_sq_succ t hcn hkc] at hk
    exact absurd hk (by simp)
  · exact ⟨by simpa using hkc, hz⟩

/-- The same invariant on the UNPADDED rows — the eight registered rows of §11. -/
theorem no_overshoot_one : ∀ {N : BMS.Matrix} {v : Term}, Certified N v →
    ∀ (t : Term), CN t = true → N = StageA.oneRow (sq t) →
      ∀ (s : Term), inT s = true → Evidence.WF.Frag s = true → isAP s = true →
        le (phi zero (plus t one)) s = true → le s v = false :=
  no_overshoot_of (fun t => StageA.oneRow (sq t))
    (fun _ hcn hk => kindC_of_kind_succ_one hcn hk)
    (fun _ hcn hk => kindC_of_kind_lim_one hcn hk)
    (fun t hcn hkc n => by
      show (BMS.expand? (StageA.oneRow (sq t)) n).getD [] = _
      rw [expand_sq_succ t hcn hkc n]; rfl)
    (fun t hcn hkc hz n => by
      show (BMS.expand? (StageA.oneRow (sq t)) n).getD [] = _
      rw [expand_sq t hcn hkc hz n]; rfl)

/-! ### §15.8 Cashing it in on the ε₀ row -/

theorem lt_hdOf_phi : ∀ (a p q : Term), lt a (phi p q) = lt (hdOf a) (phi p q)
  | zero, _, _ => rfl
  | M, _, _ => rfl
  | omg _, _, _ => rfl
  | phi _ _, _, _ => rfl
  | psi _ _, _, _ => rfl
  | Z _, _, _ => rfl
  | add c d, p, q => by rw [Evidence.WF.lt_add_phi]; rfl

theorem lt_plus_one_phi {a p q : Term} (h1 : le one (hd a) = true)
    (h : lt a (phi p q) = true) : lt (plus a one) (phi p q) = true := by
  obtain ⟨b, hb⟩ := plus_one_shape h1
  rw [hb, Evidence.WF.lt_add_phi, ← lt_hdOf_phi]
  exact h

theorem lt_pow_of_lt_eps0 {X : Term} (h : lt X (phi one zero) = true) :
    lt (phi zero X) (phi one zero) = true := by
  have hX := Evidence.WF.deg_pos X
  show ltF (fuelOf (phi zero X) (phi one zero)) (phi zero X) (phi one zero) = true
  rw [show fuelOf (phi zero X) (phi one zero)
        = (2 * ((phi zero X).deg + (phi one zero).deg) + 7) + 1 from by
      show 2 * ((phi zero X).deg + (phi one zero).deg) + 8 = _; omega]
  show (if (phi zero X == phi one zero) = true then false else
    if ((zero : Term) == one) = true then _
    else if ltF (2 * ((phi zero X).deg + (phi one zero).deg) + 7) zero one = true
      then ltF (2 * ((phi zero X).deg + (phi one zero).deg) + 7) X (phi one zero)
      else _) = true
  rw [show ((phi zero X == phi one zero) : Bool) = false from by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro hc; injection hc with h1 _; exact Term.noConfusion h1,
    show (((zero : Term) == one) : Bool) = false from rfl,
    show ltF (2 * ((phi zero X).deg + (phi one zero).deg) + 7) (zero : Term) one = true from rfl]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [← Evidence.WF.lt_eq_ltF X (phi one zero) _
    (by show X.deg + (phi one zero).deg ≤ 2 * ((1 + 1 + X.deg) + (phi one zero).deg) + 7; omega)]
  exact h

/-- **No certified value of the k-th expansion of the ε₀ row reaches ε₀.** -/
theorem le_eps0_towerM (k : Nat) (v : Term) (h : Certified (towerM k) v) :
    le (phi one zero) v = false := by
  refine no_overshoot h (Evidence.WF.tower k) (Evidence.WF.cn_tower k) (towerM_eq k)
    (phi one zero) (by decide) rfl rfl ?_
  show ((phi zero (plus (Evidence.WF.tower k) one) == phi one zero) ||
    lt (phi zero (plus (Evidence.WF.tower k) one)) (phi one zero)) = true
  rw [show lt (phi zero (plus (Evidence.WF.tower k) one)) (phi one zero) = true from
    lt_pow_of_lt_eps0 (lt_plus_one_phi
      (le_one_hd_cn _ (Evidence.WF.cn_tower k) (Evidence.WF.tower_ne_zero k))
      (Evidence.WF.lt_tower_eps0 k))]
  exact Bool.or_true _

/-- **THE ε₀ ROW ADMITS NO VALUE ABOVE ε₀.**  No hypothesis on `u` beyond being
    above ε₀, and none at all on the values inside the hypothetical certificate. -/
theorem no_cert_above_eps0 (u : Term) (hu : lt (phi one zero) u = true) :
    ¬ Certified [[0, 0], [1, 1]] u := by
  intro h
  cases h with
  | succ hk _ => rw [kind_eps0_row] at hk; exact absurd hk (by simp)
  | lim fs hk hall hlt hstep hcof =>
    obtain ⟨k, hk2⟩ := hcof (phi one zero) (by decide) hu
    have hc : Certified (towerM k) (fs k) := by
      have hx := hall k
      rwa [show BMS.expand [[0, 0], [1, 1]] k = towerM k from expand_eps0_row k] at hx
    rw [le_eps0_towerM k (fs k) hc] at hk2
    exact Bool.noConfusion hk2

/-- **The ε₀·2 negative control, as a genuine non-certifiability theorem.** -/
theorem neg_control_eps0_times_two_strong :
    ¬ Certified [[0, 0], [1, 1]] (add (phi one zero) (phi one zero)) :=
  no_cert_above_eps0 _ (by decide)


/-! ### §15.10 THE REGISTRY, READ AS AN UPPER BOUND

§14.5/§6.1 give uniqueness for GUARDED certificates on every registered row.  Here
is what survives with no guard at all: no certificate whatsoever — junk values at
every level allowed — carries a value that reaches `ω^(value+1)`.  For the ε₀ row
§15.8 says much more (nothing above ε₀ at all), because ε₀ is closed under `ω^·`;
for the eight CNF rows the bound `ω^(t+1)` is what the invariant of §15.7 gives,
and sharpening it below `ω^t` would need the undershoot half (see the §15 header). -/

/-- Inversion at a limit row: any certificate of a limit matrix hands back the four
    `lim` clauses.  (`cases` on `Certified` with the matrix a variable.) -/
theorem certified_lim_inv {N : BMS.Matrix} {v : Term} (h : Certified N v)
    (hk : BMS.kind N = .lim) :
    ∃ fs : Nat → Term, (∀ n, Certified (BMS.expand N n) (fs n)) ∧ (∀ n, lt (fs n) v = true) ∧
      (∀ n, lt (fs n) (fs (n + 1)) = true) ∧
      (∀ s, inT s = true → lt s v = true → ∃ n, le s (fs n) = true) := by
  cases h with
  | zero => rw [kind_nil] at hk; exact absurd hk (by simp)
  | succ hk2 _ => rw [hk2] at hk; exact absurd hk (by simp)
  | lim fs _ hall hlt hstep hcof => exact ⟨fs, hall, hlt, hstep, hcof⟩

/-- **No certified value of the one-row matrix of `t` reaches `ω^(t+1)`.**  The
    invariant of §15.7 with the bound itself as the probe. -/
theorem cert_below_bound_one (t : Term) (hcn : CN t = true) (v : Term)
    (h : Certified (StageA.oneRow (sq t)) v) : le (phi zero (plus t one)) v = false :=
  no_overshoot_one h t hcn rfl (phi zero (plus t one))
    (inT_of_cn _ (cn_pow (plus_one_cn t hcn).1)) (frag_bnd hcn) rfl (Evidence.WF.le_self _)

/-- The same for the padded rows. -/
theorem cert_below_bound_padSq (t : Term) (hcn : CN t = true) (v : Term)
    (h : Certified (padRow (sq t)) v) : le (phi zero (plus t one)) v = false :=
  no_overshoot h t hcn rfl (phi zero (plus t one))
    (inT_of_cn _ (cn_pow (plus_one_cn t hcn).1)) (frag_bnd hcn) rfl (Evidence.WF.le_self _)

theorem lt_eps0_bnd : lt (phi one zero) (phi zero (plus (phi one zero) one)) = true := by decide

/-- The ε₀ row, whose matrix is not of the form `oneRow (sq t)`: its expansions are
    the padded towers, and the two sub-cases are `le_eps0_towerM` (via §15.7 with the
    probe `ω^(ε₀+1)`, which dominates every `ω^(tower k + 1)`) and §15.8. -/
theorem cert_eps0_row_ceiling {s : Term} (hin : inT s = true)
    (hfr : Evidence.WF.Frag s = true) (hap : isAP s = true)
    (hb : le (phi zero (plus (phi one zero) one)) s = true)
    (v : Term) (h : Certified [[0, 0], [1, 1]] v) : le s v = false := by
  obtain ⟨fs, hall, _, _, hcof⟩ := certified_lim_inv h kind_eps0_row
  have heps : lt (phi one zero) s = true :=
    Evidence.WF.lt_of_lt_of_le (show Evidence.WF.Frag (phi one zero) = true from rfl)
      (show Evidence.WF.Frag (phi zero (plus (phi one zero) one)) = true from rfl) hfr
      lt_eps0_bnd hb
  have heps' : le (phi one zero) s = true := by
    show ((phi one zero == s) || lt (phi one zero) s) = true
    rw [heps]; exact Bool.or_true _
  cases hlev : le s v with
  | false => rfl
  | true =>
    exfalso
    simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at hlev
    rcases hlev with rfl | hlt
    · exact no_cert_above_eps0 _ heps h
    · obtain ⟨k, hk2⟩ := hcof s hin hlt
      have hc : Certified (towerM k) (fs k) := by
        have hx := hall k
        rwa [show BMS.expand [[0, 0], [1, 1]] k = towerM k from expand_eps0_row k] at hx
      rw [no_overshoot hc (Evidence.WF.tower k) (Evidence.WF.cn_tower k) (towerM_eq k)
        s hin hfr hap
        (Evidence.WF.le_trans (frag_bnd (Evidence.WF.cn_tower k))
          (show Evidence.WF.Frag (phi one zero) = true from rfl) hfr
          (show le (phi zero (plus (Evidence.WF.tower k) one)) (phi one zero) = true from by
            show ((phi zero (plus (Evidence.WF.tower k) one) == phi one zero) ||
              lt (phi zero (plus (Evidence.WF.tower k) one)) (phi one zero)) = true
            rw [show lt (phi zero (plus (Evidence.WF.tower k) one)) (phi one zero) = true from
              lt_pow_of_lt_eps0 (lt_plus_one_phi
                (le_one_hd_cn _ (Evidence.WF.cn_tower k) (Evidence.WF.tower_ne_zero k))
                (Evidence.WF.lt_tower_eps0 k))]
            exact Bool.or_true _)
          heps')] at hk2
      exact Bool.noConfusion hk2

/-- The ε₀ row's ceiling at the standard probe — the statement §15.10 published. -/
theorem cert_below_bound_eps0 (v : Term) (h : Certified [[0, 0], [1, 1]] v) :
    le (phi zero (plus (phi one zero) one)) v = false :=
  cert_eps0_row_ceiling (by decide) rfl rfl (Evidence.WF.le_self _) v h

/-- Inversion at a successor matrix, the companion of `certified_lim_inv`. -/
theorem certified_succ_inv {N : BMS.Matrix} {v : Term} (h : Certified N v)
    (hk : BMS.kind N = .succ) :
    ∃ w, v = plus w one ∧ ∀ n, Certified (BMS.expand N n) w := by
  cases h with
  | zero => rw [kind_nil] at hk; exact absurd hk (by simp)
  | succ _ hall => exact ⟨_, rfl, hall⟩
  | lim _ hk2 _ _ _ _ => rw [hk2] at hk; exact absurd hk (by simp)

/-- **A ceiling transports across a successor row.**  `plus w 1` has the SAME
    leftmost component as `w` (§15.5), and a principal probe reads only that
    (`le_ap_hd`), so a bound on the row below is a bound on the row.  This is the
    §15.7 succ-step, packaged for the successor rows of §16. -/
theorem cert_below_bound_succ {N N' : BMS.Matrix} (hk : BMS.kind N = .succ)
    (hexp : BMS.expand N 0 = N') {s : Term} (hap : isAP s = true) (hs1 : le s one = false)
    (hbase : ∀ w, Certified N' w → le s w = false) :
    ∀ u, Certified N u → le s u = false := by
  intro u h
  obtain ⟨w, hu, hall⟩ := certified_succ_inv h hk
  subst hu
  have hw : Certified N' w := by rw [← hexp]; exact hall 0
  rcases cert_hd hw with hz | hz
  · rw [hz, show plus (zero : Term) one = one from rfl]; exact hs1
  · rw [le_ap_hd hap (plus w one), hd_plus_one (le_one_ap (isAP_hd w hz)), ← le_ap_hd hap w]
    exact hbase w hw

/-- **NOTHING ABOVE `ω^t` IS CERTIFIABLE FOR A LIMIT ROW OF THE REGION**, abstractly
    in the region: the row's own cofinality clause hands the probe `ω^t` down to one
    expansion, where §15.7's invariant forbids it (the sub-bound `ω^(fsC t k + 1)` is
    `≤ ω^t`, the limit absorbing the `+1`).  No hypothesis on `u` beyond being above
    `ω^t`, and none at all on the values inside the hypothetical certificate. -/
theorem no_cert_above_pow_gen (R : Term → BMS.Matrix)
    (hov : ∀ {N : BMS.Matrix} {v : Term}, Certified N v →
      ∀ (t : Term), CN t = true → N = R t →
        ∀ (s : Term), inT s = true → Evidence.WF.Frag s = true → isAP s = true →
          le (phi zero (plus t one)) s = true → le s v = false)
    (hRel : ∀ (t : Term), CN t = true → kindC t = false → t ≠ zero → ∀ n,
        BMS.expand (R t) n = R (fsC t n))
    (t : Term) (hcn : CN t = true) (hk : kindC t = false) (hz : t ≠ zero)
    (hkind : BMS.kind (R t) = .lim) (u : Term) (hu : lt (phi zero t) u = true) :
    ¬ Certified (R t) u := by
  intro h
  obtain ⟨fs, hall, _, _, hcof⟩ := certified_lim_inv h hkind
  obtain ⟨hcnfs, hltfs, _, _⟩ := Evidence.WF.lim_clauses t hcn hk hz
  obtain ⟨k, hk2⟩ := hcof (phi zero t) (inT_of_cn _ (cn_pow hcn)) hu
  have hc : Certified (R (fsC t k)) (fs k) := by rw [← hRel t hcn hk hz k]; exact hall k
  rw [hov hc (fsC t k) (hcnfs k) rfl (phi zero t) (inT_of_cn _ (cn_pow hcn))
    (frag_pow_cn hcn) rfl
    (Evidence.WF.le_pow (le_plus_one_of_lt_lim (hcnfs k) hcn hk (hltfs k)))] at hk2
  exact Bool.noConfusion hk2

/-- The padded limit rows (the ε₀ row's expansions are of this shape). -/
theorem no_cert_above_pow (t : Term) (hcn : CN t = true) (hk : kindC t = false) (hz : t ≠ zero)
    (u : Term) (hu : lt (phi zero t) u = true) : ¬ Certified (padRow (sq t)) u :=
  no_cert_above_pow_gen (fun t => padRow (sq t)) no_overshoot
    (fun t hcn hkc hz n => by
      show (BMS.expand? (padRow (sq t)) n).getD [] = _
      rw [expand_padSq t hcn hkc hz n]; rfl)
    t hcn hk hz (kind_padSq_lim t hcn hk hz) u hu

/-- The unpadded limit rows — five of the registered rows (ω, ω·2, ω², ω^ω, ω^(ω^ω)). -/
theorem no_cert_above_pow_one (t : Term) (hcn : CN t = true) (hk : kindC t = false)
    (hz : t ≠ zero) (u : Term) (hu : lt (phi zero t) u = true) :
    ¬ Certified (StageA.oneRow (sq t)) u :=
  no_cert_above_pow_gen (fun t => StageA.oneRow (sq t)) no_overshoot_one
    (fun t hcn hkc hz n => by
      show (BMS.expand? (StageA.oneRow (sq t)) n).getD [] = _
      rw [expand_sq t hcn hkc hz n]; rfl)
    t hcn hk hz (kind_sq_lim t hcn hk hz) u hu

/-- Sample: the ω row admits no value above ω^ω, with no hypothesis on the
    competing certificate.  Every CNF limit row of the registry is this instance. -/
theorem no_cert_above_omega_pow (u : Term) (hu : lt (phi zero omega) u = true) :
    ¬ Certified [[0], [1]] u :=
  no_cert_above_pow_one omega (by decide) (by decide)
    (by intro hc; exact Term.noConfusion hc) u hu

/-! ### §15.9 THE MUTANT: why §14's guard is not decoration

`Certified` is NOT single-valued on the raw type `Term`, and the witness is §8's
junk term at the ω row.  `1 + M` is not a term of 𝔗(M) (`M ≰ 1`, so 2.1(iii)
fails), but the head-only comparison of formal sums puts every finite term below
it and nothing else of 𝔗(M) below it — so the four `lim` clauses hold with the
SAME expansion values `fs' n = n+1` that `cert_omega` uses, and the ω row carries
two certified values, ω and `1 + M`.

This is the mutant for §14: delete the `Dom` guard from `cert_unique_in` and the
theorem becomes FALSE, by `cert_not_single_valued` below.  It is also the machine
version of design input 2 of plan/README.md ("quantify over `inT` terms"), and it
is why §14 guards the values ALL THE WAY DOWN rather than only at the top: the
same junk can sit at any expansion of any row. -/

private theorem ofNat_ne_M : ∀ n, ofNat (n + 1) ≠ M
  | 0 => by intro hc; exact Term.noConfusion hc
  | n + 1 => by rw [ofNat_shape n]; intro hc; exact Term.noConfusion hc

private theorem lt_ofNat_M : ∀ n, lt (ofNat n) M = true
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by rw [ofNat_shape n, lt_add_ap one (ofNat (n + 1)) rfl]; rfl

private theorem lt_ofNat_junk : ∀ n, lt (ofNat (n + 1)) (add one M) = true
  | 0 => rfl
  | n + 1 => by
    rw [ofNat_shape n,
      Evidence.WF.lt_add_add (by
        intro hc; injection hc with _ h2; exact ofNat_ne_M n h2),
      if_pos rfl]
    exact lt_ofNat_M (n + 1)

/-- The cofinality clause for the junk value `1 + M`: the terms of 𝔗(M) below it
    are exactly the finite ones, because a sum is compared by its head and nothing
    of 𝔗(M) is strictly between `0` and `1`. -/
private theorem cofinal_junk (s : Term) (hs : inT s = true) (h : lt s (add one M) = true) :
    ∃ n, le s (ofNat (n + 1)) = true := by
  by_cases hz : s = zero
  · exact ⟨0, by rw [hz]; rfl⟩
  · have hhead : le ((toList s).headD zero) one = true := by
      by_cases hap : isAP s = true
      · rw [TM.Term.toList_of_isAP hap]
        show le s one = true
        rw [lt_ap_add hap one M] at h
        exact h
      · cases s with
        | zero => exact absurd rfl hz
        | M => exact absurd rfl hap
        | omg _ => exact absurd rfl hap
        | phi _ _ => exact absurd rfl hap
        | psi _ _ => exact absurd rfl hap
        | Z _ => exact absurd rfl hap
        | add a b =>
          obtain ⟨hapa, hina, _⟩ := inT_add hs
          by_cases hone : a = one
          · show le a one = true
            rw [hone]; exact Evidence.WF.le_self one
          · exfalso
            rw [Evidence.WF.lt_add_add (by
                intro hc; injection hc with h1 _; exact hone h1), if_neg hone] at h
            rw [Evidence.WF.below_one a hina _ h] at hapa
            exact Bool.noConfusion hapa
    obtain ⟨j, hj⟩ := tail_ofNat s hs hz hhead
    exact ⟨j, by rw [hj]; exact Evidence.WF.le_self _⟩

/-- **The junk certificate.**  `(0)(1)` carries the value `1 + M` as well as ω. -/
theorem junk_omega_row : Certified [[0], [1]] (add one M) :=
  .lim (fun n => ofNat (n + 1)) rfl
    (fun n => by rw [expand_omega n]; exact cert_zeros (n + 1))
    lt_ofNat_junk
    (fun n => lt_ofNat_succ (n + 1))
    cofinal_junk

/-- The junk value fails the formation conditions — this is exactly what `DomF`
    excludes, and `cert_omega` is the guarded one (`certIn_padSq` at `ω`). -/
theorem junk_not_inT : inT (add one M) = false := rfl

/-- **`Certified` IS NOT SINGLE-VALUED ON RAW TERMS.**  Hence no theorem of the
    form `Certified M t → Certified M u → t = u` is true, and §14's guard (or some
    other restriction to 𝔗(M)) is forced, not stylistic. -/
theorem cert_not_single_valued :
    Certified [[0], [1]] omega ∧ Certified [[0], [1]] (add one M) ∧ omega ≠ add one M :=
  ⟨cert_omega, junk_omega_row, by intro hc; exact Term.noConfusion hc⟩

/-! ## §16 SCOPING THE VEBLEN-REGION ROWS  (measurement, 2026-08-09)

The ✅ frontier is ε₀.  The next twelve rows of the table are all Veblen-region
values (φ̄ only, no ψ/Z), and this section records what they actually cost, MEASURED
with `#eval` on `BMS.expand` rather than argued.  Everything below is a `#guard`
except `certIn_eps0_succ`, which is the one row that is free today.

THE THREE KINDS.  Of the twelve, three are SUCCESSOR rows and nine are LIMIT rows:

    succ : (0,0)(1,1)(0,0) = ε₀+1     (0,0)(1,1)(2,0)(0,0) = ε_ω+1
           (0,0)(1,1)(2,1)(0,0) = ζ₀+1
    lim  : the other nine

and each successor row's expansion is CONSTANT and equal to the row below it —
`(0,0)(1,1)(0,0)[n] = (0,0)(1,1)` for every n, and likewise for the other two.  So
every successor row is `Certified.succ` applied to the row below, at a cost of four
lines.  `certIn_eps0_succ` below is that, for the one whose predecessor is already
certified; the other two come free the moment ε_ω and ζ₀ are done.

WHERE THE ONE-ROW MACHINERY STOPS.  `cert_eps0` worked because the ε₀ row expands to
`towerM n = padRow (sq (tower n))` — PADDED ONE-ROW matrices, which §10–§12 consume.
The limit rows leave that region immediately:

    (0,0)(1,1)(1,1)[n] = (0,0)(1,1), (0,0)(1,1)(1,0)(2,1), (0,0)(1,1)(1,0)(2,1)(2,0)(3,1), …

Columns like `(2,1)` have a nonzero SECOND row, which `padRow` (second row identically
zero) cannot produce.  MEASURED on the ε₁ row: its expansion closure to depth 3
(sampling n ≤ 2) contains 30 distinct matrices, of which only 8 are padded one-row;
the other 22 are outside everything this file can currently certify.  So the obstacle
is not a missing lemma, it is a missing REGION: a term-to-matrix map for the Veblen
region with its own decomposition and expansion identity, in the §10–§12 idiom.

THE TRAP IN THE TERM COLUMN, worth stating before anyone writes these certificates.
For `(0,0)(1,1)(1,0)` the row DB carries the term `φ̄0(φ̄10)` while the table's ordinal
column reads `ω^(ε₀+1)`.  Those are NOT the same object read two ways: as TERMS,
`φ̄0(φ̄10) < φ̄0(ε₀+1)` (`#guard` below).  The certificate machinery accepts the DB's
term and REFUTES the other one: the row's expansions are the matrices ε₀·(n+1), and
no ε₀·(n+1) overtakes `φ̄0(φ̄10)`, which is an `inT` term strictly below `φ̄0(ε₀+1)` —
that is exactly the shape of §7's and §13.1's negative controls.  The ordinal column
is the ORDER-TYPE reading (the segment below `φ̄0(φ̄10)` has order type ε₀·ω =
ω^(ε₀+1)), so the table is coherent; but a certificate written against the ordinal
column instead of the term column cannot close, and "fixing" it by adjusting the
fundamental sequence until it does is precisely the 較正事故 mechanism. -/

/-! ### §16.1 The measurements -/

-- the three successor rows, and the constancy of their expansions
#guard BMS.kind [[0, 0], [1, 1], [0, 0]] == BMS.Kind.succ
#guard BMS.kind [[0, 0], [1, 1], [2, 0], [0, 0]] == BMS.Kind.succ
#guard BMS.kind [[0, 0], [1, 1], [2, 1], [0, 0]] == BMS.Kind.succ
#guard (List.range 4).all (fun n => BMS.expand [[0, 0], [1, 1], [0, 0]] n == [[0, 0], [1, 1]])
#guard (List.range 4).all (fun n =>
  BMS.expand [[0, 0], [1, 1], [2, 0], [0, 0]] n == [[0, 0], [1, 1], [2, 0]])
#guard (List.range 4).all (fun n =>
  BMS.expand [[0, 0], [1, 1], [2, 1], [0, 0]] n == [[0, 0], [1, 1], [2, 1]])

-- the nine limit rows really are limit rows
#guard [[[0,0],[1,1],[1,0]], [[0,0],[1,1],[1,1]], [[0,0],[1,1],[2,0]],
        [[0,0],[1,1],[2,0],[2,0]], [[0,0],[1,1],[2,0],[3,0]], [[0,0],[1,1],[2,0],[3,1]],
        [[0,0],[1,1],[2,1]], [[0,0],[1,1],[2,1],[1,0]], [[0,0],[1,1],[2,1],[1,1]]].all
  (fun m => BMS.kind m == BMS.Kind.lim)

-- the ε₁ row leaves the padded one-row region at the first step
#guard BMS.expand [[0, 0], [1, 1], [1, 1]] 1 == [[0, 0], [1, 1], [1, 0], [2, 1]]
#guard !((BMS.expand [[0, 0], [1, 1], [1, 1]] 1).all (fun c => c.getD 1 0 == 0))

-- the ω^(ε₀+1) row: its expansions are the matrices ε₀·(n+1) …
#guard (List.range 3).all (fun n =>
  BMS.expand [[0, 0], [1, 1], [1, 0]] n == (List.replicate (n + 1) [[0, 0], [1, 1]]).flatten)
-- … and the term column's value, not the ordinal column's, is the one they can certify
#guard lt (phi zero (phi one zero)) (phi zero (plus (phi one zero) one)) == true
#guard inT (phi zero (phi one zero)) == true
#guard (List.range 6).all (fun k =>
  le (phi zero (phi one zero)) (Evidence.WF.repAdd (phi one zero) k) == false)

/-! ### §16.2 The one row that is free today

`(0,0)(1,1)(0,0)` expands constantly to the ε₀ row, so it is `CertifiedIn.succ`
applied to `certIn_eps0`.  Built GUARDED (`DomI`) so that registering it would give
uniqueness and the ceiling with no further work — registration itself is a table
change and is left to the coordinator: it is one entry in `certRows` and one branch
in `certIn_rows`. -/

theorem certIn_eps0_succ_F :
    CertifiedIn DomF [[0, 0], [1, 1], [0, 0]] (plus (phi one zero) one) :=
  CertifiedIn.succ rfl
    (fun n => by
      show CertifiedIn DomF ((BMS.expand? [[0, 0], [1, 1], [0, 0]] n).getD [])
        (phi one zero)
      exact certIn_eps0)
    ⟨rfl, by decide⟩

theorem certIn_eps0_succ :
    CertifiedIn DomI [[0, 0], [1, 1], [0, 0]] (plus (phi one zero) one) :=
  certifiedIn_mono domF_le_domI certIn_eps0_succ_F

/-- The unguarded form, for symmetry with §13's `cert_eps0`. -/
theorem cert_eps0_succ : Certified [[0, 0], [1, 1], [0, 0]] (plus (phi one zero) one) :=
  certifiedIn_forget certIn_eps0_succ

/-! ### §16.3 THE DIVERGENCE SWEEP — how many rows carry a collapsing term
    (asked for by the coordinator after the `(0,0)(1,1)(1,0)` finding)

The trap of the §16 header is not a one-off.  Its criterion is exact and already in
the codebase: `TM.Term.isFP a g` ([Rathjen, 1991] 2.6(vi)) decides whether `g` is an
a-fixed-point shape, i.e. whether `φ̄ag` COLLAPSES to `g` under the Veblen rules —
`φ̄0(φ̄10) = ω^(ε₀) = ε₀` is the instance the ε₀ campaign ran into.  A term of the row
database is at risk exactly when some subterm `φ̄ab` of it satisfies `isFP a b`.

SWEPT over all 51 rows of `Rows.rows` (run from a snippet importing `Rows.TM`, which
cannot be done from this file — `Rows.TM` imports it):

    51  rows total
    18  carry a subterm `φ̄ab` with `isFP a b = true`   ← the divergence shape
     1  more is flagged by `phiShifted` only  (ψ₀(ψ₂(2)), (0,0)(1,1)(2,2)(3,0)(3,0))
     0  rows carry a term failing `inT`                 ← every DB term is a term of 𝔗(M)

Of the TWELVE Veblen-region rows this lane is scoping, THREE are flagged, and they
are exactly the three whose name has a successor exponent:

    ω^(ε₀+1)    (0,0)(1,1)(1,0)          DB term  φ̄0(φ̄10)
    ω^(ζ₀+1)    (0,0)(1,1)(2,1)(1,0)     DB term  φ̄0(φ̄20)
    ε_{ζ₀+1}    (0,0)(1,1)(2,1)(1,1)     DB term  φ̄1(φ̄20)

WHAT THIS MEANS FOR THE CAMPAIGN.  Nothing in the table is wrong — the ordinal column
is the ORDER-TYPE reading and the term column is the term — but for these three rows a
certificate must be written against the TERM, and the term suggested by the ordinal
column is refutable (the §16 header shows the refutation for the first).  For the
remaining fifteen flagged rows, all of them beyond ζ₀, the same care will be needed
when their turn comes.

IT ALSO PRICES A PIECE OF THE CAMPAIGN.  A normal-form predicate for the Veblen
region (the analogue of `CN`) must EXCLUDE collapsing terms, or the term-to-matrix map
is not injective and the certificate family cannot be built by recursion on it.  `CN`
never had to say this: at base level the condition degenerates to `isPow`, which is why
§10–§13 could stay as short as they are. -/

#guard TM.Term.isFP zero (phi one zero) == true
#guard TM.Term.isFP zero (phi (ofNat 2) zero) == true
#guard TM.Term.isFP one (phi (ofNat 2) zero) == true
-- and the shape that is NOT flagged: an ordinary CNF exponent
#guard TM.Term.isFP zero (phi zero omega) == false

/-! ### §16.4 THE ENCODING IS NOT "APPEND = APPLY `φ̄1·`"  (measurement, 2026-08-10)

Written down because the natural guess is wrong and costs an hour to discover.  A
Veblen-region term-to-matrix map (`sqv`, the coordinator's route) will be read off
the data; here is the part of the data that REFUTES the obvious recursion
"emit a ladder for `a`, then a shifted encoding of `b`".  All of it is the ORACLE
run on matrices of the repository's own expansion closure, `F(a,b)` for `φ̄ab`.  (The
guards below were switched from `Trans.o?` to `Trans.oR` on 2026-08-10: `o?` is the
RETRACTED pre-calibration reader and is wrong above ζ₀ — see `Evidence/SqV.lean` §1.1.
Every matrix here was audited and the two reference implementations agree on all of them, so no datum
changed; the instrument did.):

    F(1,0)      = ε₀        ↦ (0,0)(1,1)
    F(1,1)      = ε₁        ↦ (0,0)(1,1)(1,1)          a REPEAT at the same depth
    F(1,2)      = ε₂        ↦ (0,0)(1,1)(1,1)(1,1)
    F(1,ω)      = ε_ω       ↦ (0,0)(1,1)(2,0)          ONE column for the subscript
    F(1,ω^ω)    = ε_{ω^ω}   ↦ (0,0)(1,1)(2,0)(3,0)
    F(1,F(1,0)) = ε_{ε₀}    ↦ (0,0)(1,1)(2,0)(3,1)
    F(1,F(2,0))             ↦ (0,0)(1,1)(2,1)(1,1)
    F(2,0)      = ζ₀        ↦ (0,0)(1,1)(2,1)
    F(3,0)                  ↦ (0,0)(1,1)(2,1)(2,1)
    F(ω,0)                  ↦ (0,0)(1,1)(2,1)(3,0)
    F(F(1,0),0)             ↦ (0,0)(1,1)(2,1)(3,0)(4,1)

THE REFUTATION IS IN LINES 7 AND 6.  Appending `(1,1)` to the matrix of `x` yields
the matrix of `F(1,x)` when `x = ζ₀` — line 7 is line 8 with `(1,1)` appended — but
NOT when `x = ε₀`: appending `(1,1)` to `(0,0)(1,1)` gives `(0,0)(1,1)(1,1)`, which
is ε₁ = F(1,1), while F(1,ε₀) is the different matrix of line 6.  So "append the
ε-marker" is not "apply `φ̄1·`", and no rule of the form
`sqv (φ̄ a b) = ladder a ++ shift (sqv b)` reproduces both lines at once.

(The reason is visible once stated: `F(1,F(2,0))` is a COLLAPSING term — `isFP 1 (φ̄20)`
holds, §16.3 — so it is one of the seven non-normal-form values in the closure, and the
encoding treats it as the matrix of ζ₀ with one more ε-step rather than as a fresh
subscript.  Whatever `sqv` is, it must be total on such terms: 7 of the 414 matrices in
the twelve rows' closure carry one, and one of the seven is the row ε_{ζ₀+1} itself.)

Eleven examples under-determine the map; a few hundred would not.  The instrument for
generating them is the surveys' `t2m` (dictionary-inverse plus a compositional
encoder), which is CANDIDATE TIER: it may say what matrix `sqv` should produce, and it
must never appear in a certificate's justification — `sqv` has to be PROVED to produce
that matrix, by `sqv_decomp` in the idiom of §10's `sq_decomp`. -/

#guard Trans.oR [[0, 0], [1, 1], [1, 1]] == Trans.oR ([[0, 0], [1, 1]] ++ [[1, 1]])
#guard !(Trans.oR [[0, 0], [1, 1], [2, 0], [3, 1]] == Trans.oR ([[0, 0], [1, 1]] ++ [[1, 1]]))
#guard Trans.oR [[0, 0], [1, 1], [2, 1], [1, 1]] == Trans.oR ([[0, 0], [1, 1], [2, 1]] ++ [[1, 1]])

/-! ### §16.5 WHAT 273 `t2m` PAIRS SAY  (measurement, 2026-08-10)

`t2m` (the surveys' candidate-tier map: dictionary inverse followed by the
compositional Buchholz-side encoder `enc`) was run over a generated corpus of 273
Veblen-region terms — `φ̄ a b` for `a ∈ {0,1,2,3,ω,ε₀,ζ₀}` against thirteen `b`, plus
all 169 sums of those thirteen.  Every term produced a matrix: 0 failures.  Three
things the corpus settles, and one it refutes.

SETTLED 1 — THE SUM CLAUSE, on about a hundred real pairs rather than one sample:

    ζ₀ ⊕ ε₀        ↦ (0,0)(1,1)(2,1)(0,0)(1,1)          = sqv ζ₀ ++ sqv ε₀
    ε₀ ⊕ 1         ↦ (0,0)(1,1)(0,0)
    ε₀ ⊕ ω^ω       ↦ (0,0)(1,1)(0,0)(1,0)(2,0)
    ε₁ ⊕ ε₀ ⊕ 1    ↦ (0,0)(1,1)(1,1)(0,0)(1,1)(0,0)

CONCATENATION, with no shift and no adjustment — which is exactly the clause §17
proves the BMS side of, and is why that section is worth having whatever else `sqv`
turns out to be.

SETTLED 2 — the base case `a = 0` on non-fixed-point arguments IS `padRow ∘ sq`:
`φ̄(0,1) ↦ (0,0)(1,0)`, `φ̄(0,2) ↦ (0,0)(1,0)(1,0)`, `φ̄(0,ω) ↦ (0,0)(1,0)(2,0)`.

SETTLED 3 — the COLLAPSING case has its own clause, and it is uniform in `a`:
when `isFP a b` holds (§16.3's criterion), the matrix is `sqv b` with ONE column
appended, the column depending only on `a`:

    φ̄(0,ε₀) ↦ (0,0)(1,1)(1,0)          = sqv ε₀ ++ (1,0)
    φ̄(0,ε₁) ↦ (0,0)(1,1)(1,1)(1,0)     = sqv ε₁ ++ (1,0)
    φ̄(0,ζ₀) ↦ (0,0)(1,1)(2,1)(1,0)     = sqv ζ₀ ++ (1,0)
    φ̄(1,ζ₀) ↦ (0,0)(1,1)(2,1)(1,1)     = sqv ζ₀ ++ (1,1)

This is what §16.4's table was seeing: `φ̄(1,ζ₀)` is the collapsing clause, `φ̄(1,ε₀)`
is not (`isFP 1 (φ̄10)` is FALSE — `1 < 1` fails), so they are governed by different
clauses and no single "append the marker" rule covers both.

REFUTED — a three-clause recursion on T(M) SYNTAX of the shape
`sqv (φ̄ 0 b) = (0,0) :: shift₁ (sqv b)` for non-collapsing `b`.  Counterexample from
the corpus: `φ̄(0, ε₀·2) ↦ (0,0)(1,1)(1,0)(2,1)`, whereas that clause predicts
`(0,0) ++ shift₁ (sqv (ε₀·2)) = (0,0)(1,0)(2,1)(1,0)(2,1)`.  `ε₀·2` is a sum, so
`isFP` is false and the collapsing clause does not apply either.

WHAT THAT MEANS FOR THE ROUTE.  `enc` is compositional in BUCHHOLZ-TREE coordinates,
not in `φ̄` coordinates; the ε-LEVEL of a subterm, which the tree carries explicitly,
is what the `φ̄` view has to reconstruct — and the two refutations above are both
places where it fails to.  So a T(M)-side `sqv` is either (i) a recursion carrying a
level parameter, with the `isFP` split as a genuine third clause, or (ii) a
dictionary `Term ↔ BT` proved correct, with `sqv := ofCols ∘ enc ∘ dict`.  That is a
design decision, and it should be made against this corpus rather than against
eleven examples — which is how the first attempt went wrong. -/

#guard Trans.oR [[0, 0], [1, 1], [2, 1], [0, 0], [1, 1]]
  == (do let a ← Trans.oR [[0, 0], [1, 1], [2, 1]]; let b ← Trans.oR [[0, 0], [1, 1]];
         pure (plus a b))
#guard Trans.oR [[0, 0], [1, 1], [0, 0], [1, 0], [2, 0]]
  == (do let a ← Trans.oR [[0, 0], [1, 1]]; let b ← Trans.oR [[0, 0], [1, 0], [2, 0]];
         pure (plus a b))
#guard TM.Term.isFP zero (phi one zero) == true
#guard TM.Term.isFP one (phi one zero) == false

/-! ## §17 THE SUM CLAUSE — concatenation of matrices  (Group A / `sqv`, STARTED)
    (certificate lane, 2026-08-10)

The coordinator's route for the Veblen region is a direct term-to-matrix map `sqv`
built on the `sq` skeleton, whose SUM CLAUSE concatenates.  This section is that
clause's BMS side, which is what the ε₀·k family (`ω^(ε₀+1)`, the first genuinely
new limit row) needs and what any `sqv` will consume.  It is STARTED, not finished:
what is proved is the index bookkeeping; what remains is named at the end.

THE FACT, MEASURED FIRST (35 pairs `(A,B)`, `n ≤ 3`, `#guard` samples below):

    BMS.expand (A ++ B) n = A ++ BMS.expand B n        (locality)
    BMS.kind (A ++ B) = BMS.kind B
    o? (A ++ B) = plus (o? A) (o? B)                   (values add)

for every `A` and every `B` whose FIRST COLUMN IS A ROOT COLUMN `(0,0)`.  The side
condition is not decoration — with `A = (0,0)(1,1)` and `B = (2,0)` locality fails
outright (`(A ++ B)` is the ε_ω row, whose expansions climb the ε-ladder, while
`A ++ B[n]` is constant).  Every matrix in `sq`'s image, and every matrix the
scoping data shows for the Veblen rows, starts with `(0,0)`, so the condition is
exactly "B is a block in its own right".

WHY IT IS TRUE, and what the remaining proof has to do.  `expand?` reads the last
column, takes its lowest nonzero row `t`, finds the bad root `parent M t (X-1)`, and
repeats the segment from there.  `parent` at row 0 is the MAXIMUM earlier column with
a strictly smaller row-0 entry; B's first column has entry 0 in every row, so
whenever the entry at `x` is positive that column is a candidate, and being the
maximum the search can never prefer anything in `A`; and when the entry is 0 there is
no candidate at all (entries are naturals), so the answer is `none` on both sides.
The same argument lifts to row `y+1` through `iterParent`.  Hence the whole
computation — bad root, `delta`, `ascends`, `take` — happens inside `B` with every
index shifted by `A.length`.

WHAT IS PROVED HERE: the shift lemmas for `ent` (`ent_append`, `ent_append_left`),
which is what every step of that argument is stated against.
WHAT REMAINS: `parent (A ++ B) y x = (parent B y (x - A.length)).map (· + A.length)`
and its `iterParent` companion, then `expand?_append`.  The `parent` step needs a
`List.max?`-over-`filter`-over-`range` split lemma (`List.range_add` exists; the
`max?`-over-append lemma does not and must be proved), and the `iterParent` step needs
that a chain which terminates within one fuel bound gives the same list at a larger
one — the two fuels differ by `A.length`.  Estimated 200–300 lines; it is the only
BMS-side obligation of the sum clause, and it is independent of what `sqv` turns out
to be, because the clause is `sqv (u ⊕ v) = sqv u ++ sqv v` whatever the other two
clauses do. -/

/-! ### §17.1 The measurements -/

-- locality, on the ε₀ row and its multiples, against padded CNF blocks
#guard (List.range 4).all (fun n =>
  BMS.expand ([[0, 0], [1, 1]] ++ [[0, 0], [1, 0], [2, 0]]) n
    == [[0, 0], [1, 1]] ++ BMS.expand [[0, 0], [1, 0], [2, 0]] n)
#guard (List.range 4).all (fun n =>
  BMS.expand ([[0, 0], [1, 1], [0, 0], [1, 1]] ++ [[0, 0], [1, 1]]) n
    == [[0, 0], [1, 1], [0, 0], [1, 1]] ++ BMS.expand [[0, 0], [1, 1]] n)
#guard (List.range 4).all (fun n =>
  BMS.expand ([[0, 0], [1, 1], [2, 1]] ++ [[0, 0], [1, 0]]) n
    == [[0, 0], [1, 1], [2, 1]] ++ BMS.expand [[0, 0], [1, 0]] n)
-- the kind is read off the tail block
#guard BMS.kind ([[0, 0], [1, 1]] ++ [[0, 0], [1, 0]]) == BMS.kind [[0, 0], [1, 0]]
#guard BMS.kind ([[0, 0], [1, 1]] ++ [[0, 0], [0, 0]]) == BMS.kind [[0, 0], [0, 0]]
-- and the side condition is load-bearing: a non-root first column breaks locality
#guard !(BMS.expand ([[0, 0], [1, 1]] ++ [[2, 0]]) 1 == [[0, 0], [1, 1]] ++ BMS.expand [[2, 0]] 1)

/-! ### §17.2 The shift lemmas -/

theorem getD_append_right {α : Type} (A B : List α) (j : Nat) (d : α)
    (h : A.length ≤ j) : (A ++ B).getD j d = B.getD (j - A.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- Past the prefix, an entry of `A ++ B` is an entry of `B`. -/
theorem ent_append (A B : BMS.Matrix) (j y : Nat) (h : A.length ≤ j) :
    BMS.ent (A ++ B) j y = BMS.ent B (j - A.length) y := by
  show ((A ++ B).getD j []).getD y 0 = _
  rw [getD_append_right A B j [] h]
  rfl

/-- **The bad root never leaves the tail block, at row 0.**  `parent` at row 0 is the
    MAXIMUM earlier column with a strictly smaller entry.  `B`'s first column has entry
    `0`, so it is a candidate whenever the entry at `x` is positive — and being the
    maximum, the search can never prefer a column of `A`; when the entry at `x` is `0`
    there is no candidate at all, entries being naturals, and both sides are `none`.
    No hypothesis on `A`, and none on `B` beyond its first entry. -/
theorem parent_zero_append (A B : BMS.Matrix) (hroot : BMS.ent B 0 0 = 0) (x : Nat)
    (hx : A.length ≤ x) :
    BMS.parent (A ++ B) 0 x = (BMS.parent B 0 (x - A.length)).map (· + A.length) := by
  have hex : BMS.ent (A ++ B) x 0 = BMS.ent B (x - A.length) 0 := ent_append A B x 0 hx
  show ((List.range x).filter
      (fun p => decide (BMS.ent (A ++ B) p 0 < BMS.ent (A ++ B) x 0))).max?
    = (((List.range (x - A.length)).filter
        (fun p => decide (BMS.ent B p 0 < BMS.ent B (x - A.length) 0))).max?).map (· + A.length)
  rw [hex]
  cases hB : (((List.range (x - A.length)).filter
      (fun p => decide (BMS.ent B p 0 < BMS.ent B (x - A.length) 0))).max?) with
  | none =>
    have hemp := List.max?_eq_none_iff.mp hB
    have he0 : BMS.ent B (x - A.length) 0 = 0 := by
      cases he : BMS.ent B (x - A.length) 0 with
      | zero => rfl
      | succ m =>
        exfalso
        cases hk : x - A.length with
        | zero => rw [hk, hroot] at he; exact Nat.noConfusion he
        | succ j =>
          have hmem : (0 : Nat) ∈ (List.range (x - A.length)).filter
              (fun p => decide (BMS.ent B p 0 < BMS.ent B (x - A.length) 0)) := by
            rw [List.mem_filter, List.mem_range]
            refine ⟨by omega, ?_⟩
            simp only [hroot, he, decide_eq_true_eq]
            omega
          rw [hemp] at hmem
          exact absurd hmem (by simp)
    have hnil : ∀ (l : List Nat),
        l.filter (fun p => decide (BMS.ent (A ++ B) p 0 < BMS.ent B (x - A.length) 0)) = [] := by
      intro l
      induction l with
      | nil => rfl
      | cons a tl ih => rw [List.filter_cons_of_neg (by simp [he0]), ih]
    rw [hnil (List.range x)]
    rfl
  | some r =>
    rw [List.max?_eq_some_iff] at hB
    obtain ⟨hmem, hmax⟩ := hB
    rw [List.mem_filter, List.mem_range] at hmem
    show ((List.range x).filter
        (fun p => decide (BMS.ent (A ++ B) p 0 < BMS.ent B (x - A.length) 0))).max?
      = some (r + A.length)
    apply List.max?_eq_some_iff.mpr
    constructor
    · rw [List.mem_filter, List.mem_range]
      refine ⟨by omega, ?_⟩
      rw [ent_append A B (r + A.length) 0 (by omega),
        show r + A.length - A.length = r from by omega]
      exact hmem.2
    · intro b hb
      rw [List.mem_filter, List.mem_range] at hb
      by_cases hbL : A.length ≤ b
      · have hmm := hmax (b - A.length) (by
          rw [List.mem_filter, List.mem_range]
          refine ⟨by omega, ?_⟩
          rw [← ent_append A B b 0 hbL]
          exact hb.2)
        omega
      · omega

/-- Inside the prefix, an entry of `A ++ B` is an entry of `A`. -/
theorem ent_append_left (A B : BMS.Matrix) (j y : Nat) (h : j < A.length) :
    BMS.ent (A ++ B) j y = BMS.ent A j y := by
  show ((A ++ B).getD j []).getD y 0 = _
  rw [show (A ++ B).getD j [] = A.getD j [] from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]]
  rfl

/-! ### §17.3 The bad root never leaves the tail block — the general row

The row-0 case is `parent_zero_append`.  For row `y+1` the search runs over
`iterParent (parent M y) x x`, so two things have to be shown: the CHAIN shifts (by
the induction hypothesis, since every step lands in `B`), and the two computations
agree DESPITE DIFFERENT FUEL — `iterParent` is called with the absolute index, which
differs by `A.length` between `A ++ B` and `B`.  `iterParent_shift` handles both at
once: it is stated for an arbitrary shift-conjugate pair of parent functions and any
two fuels that are large enough, with "large enough" supplied by the fact that a
parent is strictly smaller than its child (`parent_lt`). -/

theorem iterParent_nil {f : Nat → Option Nat} {fuel x : Nat} (h : f x = none) :
    BMS.iterParent f fuel x = [] := by
  cases fuel with
  | zero => rfl
  | succ g => show (match f x with | none => [] | some p => p :: BMS.iterParent f g p) = []
              rw [h]

theorem iterParent_cons {f : Nat → Option Nat} {fuel x q : Nat} (h : f x = some q) :
    BMS.iterParent f (fuel + 1) x = q :: BMS.iterParent f fuel q := by
  show (match f x with | none => [] | some p => p :: BMS.iterParent f fuel p) = _
  rw [h]

theorem iterParent_lt {f : Nat → Option Nat} (hdec : ∀ z w, f z = some w → w < z) :
    ∀ (fuel x p : Nat), p ∈ BMS.iterParent f fuel x → p < x := by
  intro fuel
  induction fuel with
  | zero => intro x p hp; exact absurd hp (by simp [BMS.iterParent])
  | succ g ih =>
    intro x p hp
    cases hfx : f x with
    | none => rw [iterParent_nil hfx] at hp; exact absurd hp (by simp)
    | some q =>
      rw [iterParent_cons hfx] at hp
      rcases List.mem_cons.mp hp with h | h
      · rw [h]; exact hdec x q hfx
      · exact Nat.lt_trans (ih q p h) (hdec x q hfx)

theorem map_add_max? (L : Nat) : ∀ (l : List Nat), (l.map (· + L)).max? = l.max?.map (· + L) := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons, List.max?_cons, List.max?_cons, ih]
    cases t.max? with
    | none => rfl
    | some m => show some (max (a + L) (m + L)) = some (max a m + L)
                rw [Nat.add_max_add_right]

theorem filter_map_add (L : Nat) (P : Nat → Bool) : ∀ (l : List Nat),
    (l.map (· + L)).filter P = (l.filter (fun p => P (p + L))).map (· + L) := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons]
    by_cases h : P (a + L)
    · rw [List.filter_cons_of_pos h, List.filter_cons_of_pos (by exact h), List.map_cons, ih]
    · rw [List.filter_cons_of_neg h, List.filter_cons_of_neg (by exact h), ih]

theorem iterParent_shift {f g : Nat → Option Nat} {L : Nat}
    (hfg : ∀ z, L ≤ z → f z = (g (z - L)).map (· + L))
    (hdecg : ∀ z w, g z = some w → w < z) :
    ∀ (fuel fuel' k : Nat), k ≤ fuel → k ≤ fuel' →
      BMS.iterParent f fuel (k + L) = (BMS.iterParent g fuel' k).map (· + L) := by
  intro fuel
  induction fuel with
  | zero =>
    intro fuel' k hk _
    have hk0 : k = 0 := by omega
    subst hk0
    have hg0 : g 0 = none := by
      cases h : g 0 with
      | none => rfl
      | some w => exact absurd (hdecg 0 w h) (by omega)
    rw [iterParent_nil hg0]
    rfl
  | succ F ih =>
    intro fuel' k hk hk'
    cases hgk : g k with
    | none =>
      have : f (k + L) = none := by rw [hfg (k + L) (by omega), show k + L - L = k from by omega, hgk]; rfl
      rw [iterParent_nil this, iterParent_nil hgk]
      rfl
    | some w =>
      have hw : w < k := hdecg k w hgk
      have hf : f (k + L) = some (w + L) := by
        rw [hfg (k + L) (by omega), show k + L - L = k from by omega, hgk]; rfl
      cases fuel' with
      | zero => omega
      | succ F' =>
        rw [iterParent_cons hf, iterParent_cons hgk, List.map_cons,
          show w + L = w + L from rfl]
        congr 1
        exact ih F' w (by omega) (by omega)

theorem parent_lt : ∀ (M : Matrix) (y x r : Nat), BMS.parent M y x = some r → r < x := by
  intro M y
  induction y with
  | zero =>
    intro x r h
    have h' : (((List.range x).filter
        (fun p => decide (BMS.ent M p 0 < BMS.ent M x 0))).max?) = some r := h
    obtain ⟨hmem, _⟩ := List.max?_eq_some_iff.mp h'
    rw [List.mem_filter, List.mem_range] at hmem
    exact hmem.1
  | succ y ih =>
    intro x r h
    have h' : (((BMS.iterParent (BMS.parent M y) x x).filter
        (fun p => decide (BMS.ent M p (y + 1) < BMS.ent M x (y + 1)))).max?) = some r := h
    obtain ⟨hmem, _⟩ := List.max?_eq_some_iff.mp h'
    rw [List.mem_filter] at hmem
    exact iterParent_lt (fun z w hw => ih z w hw) x x r hmem.1

/-- A parent is strictly to the left of its child, at every row. -/
theorem parent_append_gen (A B : Matrix)
    (h0 : ∀ x, A.length ≤ x →
      BMS.parent (A ++ B) 0 x = (BMS.parent B 0 (x - A.length)).map (· + A.length)) :
    ∀ (y x : Nat), A.length ≤ x →
      BMS.parent (A ++ B) y x = (BMS.parent B y (x - A.length)).map (· + A.length) := by
  intro y
  induction y with
  | zero => intro x hx; exact h0 x hx
  | succ y ih =>
    intro x hx
    have hiter : BMS.iterParent (BMS.parent (A ++ B) y) x x
        = (BMS.iterParent (BMS.parent B y) (x - A.length) (x - A.length)).map (· + A.length) := by
      have hs := iterParent_shift (f := BMS.parent (A ++ B) y) (g := BMS.parent B y) (L := A.length)
        (fun z hz => ih z hz) (fun z w hw => parent_lt B y z w hw)
        x (x - A.length) (x - A.length) (by omega) (by omega)
      rw [show x - A.length + A.length = x from by omega] at hs
      exact hs
    have hpred : (fun p => decide (BMS.ent (A ++ B) (p + A.length) (y + 1) < BMS.ent (A ++ B) x (y + 1)))
        = (fun p => decide (BMS.ent B p (y + 1) < BMS.ent B (x - A.length) (y + 1))) := by
      funext p
      rw [ent_append A B (p + A.length) (y + 1) (by omega),
        show p + A.length - A.length = p from by omega, ent_append A B x (y + 1) hx]
    show ((BMS.iterParent (BMS.parent (A ++ B) y) x x).filter
        (fun p => decide (BMS.ent (A ++ B) p (y + 1) < BMS.ent (A ++ B) x (y + 1)))).max? = _
    rw [hiter, filter_map_add, hpred, map_add_max?]
    rfl


/-- **The bad root never leaves the tail block, at every row.** -/
theorem parent_append (A B : BMS.Matrix) (hroot : ∀ y, BMS.ent B 0 y = 0) (y x : Nat)
    (hx : A.length ≤ x) :
    BMS.parent (A ++ B) y x = (BMS.parent B y (x - A.length)).map (· + A.length) :=
  parent_append_gen A B (fun z hz => parent_zero_append A B (hroot 0) z hz) y x hx

/-! ### §17.4 THE LOCALITY THEOREM

Everything above assembles: the last column of `A ++ B` is `B`'s, the bad root is
`B`'s shifted (§17.3), and therefore so are `delta`, `ascends` and the blocks.  The
only hypotheses are that `B` is nonempty and that its FIRST COLUMN IS ZERO — the root
column, `#guard`ed as load-bearing in §17.1. -/

theorem contains_map_add (L r : Nat) : ∀ (l : List Nat),
    (l.map (· + L)).contains (r + L) = l.contains r := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons, List.contains_cons, List.contains_cons, ih,
      show ((r + L == a + L) : Bool) = (r == a) from by
        cases h : (r == a) with
        | true => have hh : r = a := by simpa using h
                  simp [hh]
        | false => have hh : r ≠ a := by simpa using h
                   simp [hh]]

theorem ascends_append {A B : Matrix} {L : Nat} (hL : L = A.length)
    (hpar : ∀ (y x : Nat), A.length ≤ x →
      BMS.parent (A ++ B) y x = (BMS.parent B y (x - A.length)).map (· + A.length))
    (r j y : Nat) :
    BMS.ascends (A ++ B) (r + L) (j + L) y = BMS.ascends B r j y := by
  subst hL
  have hchain : BMS.iterParent (BMS.parent (A ++ B) y) (j + A.length) (j + A.length)
      = (BMS.iterParent (BMS.parent B y) j j).map (· + A.length) :=
    iterParent_shift (f := BMS.parent (A ++ B) y) (g := BMS.parent B y) (L := A.length)
      (fun z hz => hpar y z hz) (fun z w hw => parent_lt B y z w hw)
      (j + A.length) j j (by omega) (by omega)
  show ((j + A.length == r + A.length) ||
      (BMS.iterParent (BMS.parent (A ++ B) y) (j + A.length) (j + A.length)).contains (r + A.length))
    = ((j == r) || (BMS.iterParent (BMS.parent B y) j j).contains r)
  rw [hchain, contains_map_add, show ((j + A.length == r + A.length) : Bool) = (j == r) from by
    cases h : (j == r) with
    | true => have : j = r := by simpa using h
              simp [this]
    | false => have : j ≠ r := by simpa using h
               simp [this]]

theorem delta_append {A B : Matrix} (hB : B ≠ []) (r t y : Nat) :
    BMS.delta (A ++ B) (r + A.length) t y = BMS.delta B r t y := by
  have hBpos : 0 < B.length := List.length_pos_iff.mpr hB
  show (if y < t then BMS.ent (A ++ B) ((A ++ B).length - 1) y - BMS.ent (A ++ B) (r + A.length) y else 0)
     = (if y < t then BMS.ent B (B.length - 1) y - BMS.ent B r y else 0)
  rw [ent_append A B ((A ++ B).length - 1) y (by rw [List.length_append]; omega),
    ent_append A B (r + A.length) y (by omega),
    show (A ++ B).length - 1 - A.length = B.length - 1 from by rw [List.length_append]; omega,
    show r + A.length - A.length = r from by omega]

theorem expand?_append (A B : Matrix) (hB : B ≠ [])
    (hpar : ∀ (y x : Nat), A.length ≤ x →
      BMS.parent (A ++ B) y x = (BMS.parent B y (x - A.length)).map (· + A.length)) (n : Nat) :
    BMS.expand? (A ++ B) n = (BMS.expand? B n).map (fun m => A ++ m) := by
  have hBpos : 0 < B.length := List.length_pos_iff.mpr hB
  cases hL : B.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hL) hB
  | some L =>
    have hLA : (A ++ B).getLast? = some L := by rw [List.getLast?_append, hL]; rfl
    simp only [BMS.expand?, hLA, hL, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    cases hlnz : BMS.lnz L with
    | none =>
      simp only [Option.map_some]
      rw [List.dropLast_append_of_ne_nil hB]
    | some t =>
      dsimp only
      have hidx : A.length ≤ (A ++ B).length - 1 := by rw [List.length_append]; omega
      rw [hpar t ((A ++ B).length - 1) hidx,
        show (A ++ B).length - 1 - A.length = B.length - 1 from by
          rw [List.length_append]; omega]
      cases hr : BMS.parent B t (B.length - 1) with
      | none => rfl
      | some r =>
        simp only [Option.map_some, Option.bind_some]
        congr 1
        rw [show r + A.length = A.length + r from by omega, List.take_length_add_append]
        rw [List.append_assoc]
        congr 1
        rw [show (A ++ B).length - 1 - (A.length + r) = B.length - 1 - r from by
          rw [List.length_append]; omega]
        refine congrArg (fun z => List.take r B ++ z) ?_
        refine congrArg List.flatten (List.map_congr_left ?_)
        intro a _
        refine List.map_congr_left ?_
        intro x _
        refine List.map_congr_left ?_
        intro y _
        rw [show A.length + r + x = (r + x) + A.length from by omega,
          ent_append A B ((r + x) + A.length) y (by omega),
          show (r + x) + A.length - A.length = r + x from by omega,
          show A.length + r = r + A.length from by omega,
          delta_append hB r t y,
          ascends_append (A := A) (B := B) rfl hpar r (r + x) y]

/-- **LOCALITY.**  A matrix with a root column expands inside itself: the prefix is
    inert.  This is the BMS side of the sum clause `sqv (u ⊕ v) = sqv u ++ sqv v`,
    confirmed on ~100 `t2m` pairs in §16.5 and needed by every certificate family that
    concatenates blocks — the ε₀·k family of Group A, and `ω^(ζ₀+1)` after it with ζ₀
    for ε₀, which is why nothing here mentions ε₀. -/
theorem expand?_append_root (A B : Matrix) (hB : B ≠ []) (hroot : ∀ y, BMS.ent B 0 y = 0)
    (n : Nat) : BMS.expand? (A ++ B) n = (BMS.expand? B n).map (fun m => A ++ m) :=
  expand?_append A B hB (fun y x hx => parent_append A B hroot y x hx) n

/-- The total form, on the branch where the tail block expands. -/
theorem expand_append_root (A B : Matrix) (hB : B ≠ []) (hroot : ∀ y, BMS.ent B 0 y = 0)
    (n : Nat) {m : Matrix} (hm : BMS.expand? B n = some m) :
    BMS.expand (A ++ B) n = A ++ m := by
  show (BMS.expand? (A ++ B) n).getD [] = _
  rw [expand?_append_root A B hB hroot n, hm]
  rfl

/-- The kind is read off the tail block. -/
theorem kind_append (A B : Matrix) (hB : B ≠ []) : BMS.kind (A ++ B) = BMS.kind B := by
  cases hL : B.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hL) hB
  | some L =>
    show (match (A ++ B).getLast? with
          | none => BMS.Kind.zero
          | some L => match BMS.lnz L with
            | none => BMS.Kind.succ
            | some _ => BMS.Kind.lim) = _
    rw [show (A ++ B).getLast? = some L from by rw [List.getLast?_append, hL]; rfl]
    show (match BMS.lnz L with
          | none => BMS.Kind.succ
          | some _ => BMS.Kind.lim) = BMS.kind B
    show _ = (match B.getLast? with
              | none => BMS.Kind.zero
              | some L => match BMS.lnz L with
                | none => BMS.Kind.succ
                | some _ => BMS.Kind.lim)
    rw [hL]

/-! ## §18 ROW A — `ω^(ε₀+1)` = `(0,0)(1,1)(1,0)`, THE BMS SIDE  (2026-08-10)

The first LIMIT row above ε₀.  Its 𝔗(M) side is `Evidence.WF.lim_clauses_rowA`
(WF §15.4): the four `Certified.lim` premises for the DATABASE term `φ̄0(ε₀)` — not
the ordinal column's `ω^(ε₀+1)`, §16.4's trap — with the sequence `fsA n = ε₀·(n+1)`.
This section supplies the BMS side, and it is complete:

  `eps0M k`         the matrix of ε₀·(k+1): the ε₀ row repeated `k+1` times
  `eps0M_root`      its first column is a root column — the hypothesis §17 needs
  `kind_eps0M`      it is a limit row, by `kind_append` and induction
  `expand_eps0M_succ`  its expansions are `(0,0)(1,1) ++ (the previous one's)`, by §17.4
  `expand_rowA`     THE ROW'S EXPANSION IDENTITY, for every `n`

`expand_rowA` is the interesting one and it is a computation, not an induction: the
row's last column is `(1,0)`, so `t = 0`, so `delta` is `0` at every row — the
ascension amount VANISHES — and the bad part `(0,0)(1,1)` is copied `n+1` times
unchanged.  §16.1 `#guard`s the first three values; this proves all of them.

WHAT IS STILL MISSING, and it is 𝔗(M)-side, so it is a REQUEST not a gap here: the
row's certificate needs `CertifiedIn DomI (eps0M n) (fsA n)` for every `n`, i.e. the
INTERMEDIATE values ε₀·(k+1) each need their own four premises, with the sequence
`n ↦ ε₀·k ⊕ tower n` (the value of `eps0M (k-1) ++ towerM n`, which is what
`expand_eps0M_succ` produces).  In bundled form that is one lemma:

    from the four premises for `v` with sequence `g`, the four premises for `u ⊕ v`
    with sequence `fun n => plus u (g n)`

whose only hard clause is cofinality — every `inT` term below `u ⊕ v` is overtaken by
some `u ⊕ g n`.  With that, Row A closes by `CertifiedIn.lim` and the registry gains
its eleventh row. -/

/-- The matrix of ε₀·(k+1): the ε₀ row repeated `k+1` times. -/
def eps0M (k : Nat) : Matrix := (List.replicate (k + 1) [[0, 0], [1, 1]]).flatten

theorem eps0M_zero : eps0M 0 = [[0, 0], [1, 1]] := rfl

theorem eps0M_succ (k : Nat) : eps0M (k + 1) = [[0, 0], [1, 1]] ++ eps0M k := by
  show (List.replicate (k + 2) [[0, 0], [1, 1]]).flatten = _
  rw [List.replicate_succ]
  rfl

theorem eps0M_ne_nil (k : Nat) : eps0M k ≠ [] := by
  cases k with
  | zero => simp [eps0M]
  | succ j => rw [eps0M_succ]; simp

theorem eps0M_root (k : Nat) : ∀ y, BMS.ent (eps0M k) 0 y = 0 := by
  intro y
  have h : eps0M k = [[0, 0]] ++ ((eps0M k).drop 1) := by
    cases k with
    | zero => rfl
    | succ j => rw [eps0M_succ]; rfl
  show ((eps0M k).getD 0 []).getD y 0 = 0
  rw [h]
  show (([0, 0] : List Nat)).getD y 0 = 0
  cases y with
  | zero => rfl
  | succ m => cases m with | zero => rfl | succ p => rfl

theorem kind_eps0M (k : Nat) : BMS.kind (eps0M k) = .lim := by
  induction k with
  | zero => rfl
  | succ j ih => rw [eps0M_succ, kind_append _ _ (eps0M_ne_nil j)]; exact ih

theorem expand_eps0M_succ (k n : Nat) :
    BMS.expand? (eps0M (k + 1)) n = (BMS.expand? (eps0M k) n).map (fun m => [[0, 0], [1, 1]] ++ m) := by
  rw [eps0M_succ]
  exact expand?_append_root _ _ (eps0M_ne_nil k) (eps0M_root k) n

theorem map_const_flatten : ∀ (m : Nat) (B : Matrix),
    ((List.range m).map (fun _ => B)).flatten = (List.replicate m B).flatten := by
  intro m B
  induction m with
  | zero => rfl
  | succ j ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, ih, List.replicate_succ',
      List.flatten_append]
    rfl

/-- **The row `(0,0)(1,1)(1,0)` expands to the ε₀·(n+1) matrices.**  The ascension
    amount vanishes (`t = 0`, so `delta` is `0` at every row), so the bad part
    `(0,0)(1,1)` is copied `n+1` times unchanged. -/
theorem expand_rowA (n : Nat) : BMS.expand? [[0, 0], [1, 1], [1, 0]] n = some (eps0M n) := by
  have hblk : ∀ (a : Nat), ((List.range 2).map (fun x =>
      (List.range 2).map (fun y =>
        BMS.ent [[0, 0], [1, 1], [1, 0]] (0 + x) y +
          a * BMS.delta [[0, 0], [1, 1], [1, 0]] 0 0 y *
            (if BMS.ascends [[0, 0], [1, 1], [1, 0]] 0 (0 + x) y then 1 else 0))))
      = ([[0, 0], [1, 1]] : Matrix) := by
    intro a; rfl
  show some (([[0, 0], [1, 1], [1, 0]] : Matrix).take 0 ++
      ((List.range (n + 1)).map (fun a =>
        (List.range 2).map (fun x =>
          (List.range 2).map (fun y =>
            BMS.ent [[0, 0], [1, 1], [1, 0]] (0 + x) y +
              a * BMS.delta [[0, 0], [1, 1], [1, 0]] 0 0 y *
                (if BMS.ascends [[0, 0], [1, 1], [1, 0]] 0 (0 + x) y then 1 else 0))))).flatten)
    = some (eps0M n)
  rw [List.map_congr_left (l := List.range (n + 1))
      (g := fun _ => ([[0, 0], [1, 1]] : Matrix)) (fun a _ => hblk a),
    map_const_flatten]
  rfl

/-! ### §18.1 THE ε₀-PREFIXED FAMILY — what Row A's certificate runs on

`lim_clauses_fsA` (WF §15.11.2) supplies the 𝔗(M) premises at every intermediate
value ε₀·(k+1), with the sequence `fsAin k = sumSeq eps0T tower k` — RIGHT-NESTED,
`ε₀ ⊕ (ε₀ ⊕ … ⊕ tower n)`, which is a different TERM from `add (repAdd ε₀ (k-1)) (tower n)`
even though it is the same ordinal (that lane's §15.11 `#guard`s both shapes; the
wrong one is green on all four order clauses and fails only against the matrix).

So the certificate cannot be built row by row: `eps0M k`'s expansions are
`(0,0)(1,1) ++ (eps0M (k-1))'s expansions`, and THOSE are `k` copies of the ε₀ row
followed by a padded CNF row.  The family the recursion actually closes over is

    famM k c = (k copies of the ε₀ row) ++ padRow (sq c)     for `CN c`

with value `sumSeq eps0T (fun _ => c) k`-shaped, i.e. `ε₀ ⊕ (… ⊕ c)`.  §17.4's
locality theorem is what makes its expansions computable: the ε₀ blocks are inert,
so `famM k c` expands by expanding `padRow (sq c)`, which is §11–§12's business.
This subsection is that family's BMS side; the certificate itself is the next step
and needs, besides these, only `lim_clauses_sum_iter` for the limit clause and a
`plus`-associativity step for the successor clause. -/

theorem sq_head_zero : ∀ (c : TM.Term), CN c = true → ∀ a t, sq c = a :: t → a = 0 := by
  intro c
  induction c with
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | zero => intro _ a t h; exact absurd h (by simp [sq])
  | phi x y _ _ =>
    intro hcn a t h
    rw [sq_phi] at h
    injection h with h1 _
    exact h1.symm
  | add u v ihu _ =>
    intro hcn a t h
    obtain ⟨hpow, hcu, _, _⟩ := Evidence.WF.cn_add hcn
    obtain ⟨e, he⟩ := Evidence.WF.eq_pow_of_isPow hpow
    subst he
    rw [sq_add, sq_phi, List.cons_append] at h
    injection h with h1 _
    exact h1.symm

/-- `k` copies of the ε₀ row. -/
def epsBlocks (k : Nat) : Matrix := (List.replicate k [[0, 0], [1, 1]]).flatten

theorem epsBlocks_succ (k : Nat) : epsBlocks (k + 1) = [[0, 0], [1, 1]] ++ epsBlocks k := by
  show (List.replicate (k + 1) [[0, 0], [1, 1]]).flatten = _
  rw [List.replicate_succ]; rfl

/-- The family: `k` copies of the ε₀ row, then the padded CNF row of `c`. -/
def famM (k : Nat) (c : TM.Term) : Matrix := epsBlocks k ++ padRow (sq c)

theorem famM_zero (c : TM.Term) : famM 0 c = padRow (sq c) := rfl

theorem famM_succ (k : Nat) (c : TM.Term) :
    famM (k + 1) c = [[0, 0], [1, 1]] ++ famM k c := by
  show epsBlocks (k + 1) ++ padRow (sq c) = _
  rw [epsBlocks_succ, List.append_assoc]
  rfl

theorem famM_root (k : Nat) (c : TM.Term) (hcn : CN c = true) (hc : sq c ≠ []) : ∀ y, BMS.ent (famM k c) 0 y = 0 := by
  intro y
  cases k with
  | succ j =>
    show ((famM (j+1) c).getD 0 []).getD y 0 = 0
    rw [famM_succ]
    show (([0, 0] : List Nat)).getD y 0 = 0
    cases y with
    | zero => rfl
    | succ m => cases m with | zero => rfl | succ p => rfl
  | zero =>
    show ((padRow (sq c)).getD 0 []).getD y 0 = 0
    cases h : sq c with
    | nil => exact absurd h hc
    | cons a t =>
      show (([a, 0] : List Nat)).getD y 0 = 0
      cases y with
      | zero => show a = 0; exact sq_head_zero c hcn a t h
      | succ m => cases m with | zero => rfl | succ p => rfl

theorem famM_ne_nil (k : Nat) (c : TM.Term) (hc : sq c ≠ []) : famM k c ≠ [] := by
  cases k with
  | succ j => rw [famM_succ]; simp
  | zero =>
    show padRow (sq c) ≠ []
    cases h : sq c with
    | nil => exact absurd h hc
    | cons a t => simp [padRow]

/-! ### §18.2 THE FAMILY'S VALUE, and the successor step

`famV k c` is the value of `famM k c`: `k` copies of ε₀ in front of `c`, RIGHT-NESTED,
matching `Evidence.WF.sumSeq` (the shape that lane's §15.11 warns is the only correct
one — the left-nested `add (repAdd ε₀ (k-1)) c` is the same ordinal, a different term,
and green on all four order clauses).  `sumSeq_famV` is the bridge: their sequence IS
this family's value, so their clause bundles apply verbatim.

`famV` has to special-case `c = 0`, and the reason is not bookkeeping: `add ε₀ 0` is
NOT a term of 𝔗(M) (2.1(iii) needs the tail additively principal), so the nesting
must stop at `repAdd ε₀ (k-1)` rather than nest through zero.  That is the same
formation condition the whole file turns on, showing up in a definition for once.

`plus_famV_one` is the SUCCESSOR case of the certificate recursion: appending `1`
commutes with the ε₀-prefix, including through the `c = 0` boundary.

WHAT REMAINS FOR THE ELEVENTH ✅, with no further input needed from the WF lane:
  * the recursion `certIn_fam : ∀ k c, CN c → CertifiedIn DomI (famM k c) (famV k c)`,
    which is LEXICOGRAPHIC on `(k, c)` — at `c = 0` with `k ≥ 1` it recurses to
    `(k-1, tower n)`, since `epsBlocks (k+1) = epsBlocks k ++ (the ε₀ row)` and the
    LAST block is what expands;
  * its limit case needs `lim_clauses_sum` ITERATED over a general `c` — NOT
    `lim_clauses_sum_iter`, which iterates at `v = repAdd u k` and so serves only the
    `c = 0` case.  The iteration is an induction on `k` whose step needs
    `hdLe (famV j c) ε₀`, immediate because `famV j c` has head ε₀ for `j ≥ 1`;
  * two small facts about the CNF region I have not needed before: `CN c → CNV c`,
    and `hdLe c ε₀` for CN `c` (every CNF head is an ω-power below ε₀).
Then `certIn_rowA` is `CertifiedIn.lim fsA` over `expand_rowA`, and registration is
the §16.2 pattern. -/

open Evidence.WF (eps0T CNV)

/-- The value of `famM k c`: `k` copies of ε₀ in front of `c`, right-nested. -/
def famV : Nat → TM.Term → TM.Term
  | 0, c => c
  | k + 1, TM.Term.zero => repAdd eps0T k
  | k + 1, c => add eps0T (famV k c)

theorem famV_zero (c : TM.Term) : famV 0 c = c := rfl

theorem famV_succ_ne (k : Nat) {c : TM.Term} (hc : c ≠ zero) :
    famV (k + 1) c = add eps0T (famV k c) := by
  cases c with
  | zero => exact absurd rfl hc
  | M => rfl | omg _ => rfl | phi _ _ => rfl | psi _ _ => rfl | Z _ => rfl
  | add _ _ => rfl

theorem famV_zero_arg (k : Nat) : famV (k + 1) zero = repAdd eps0T k := rfl

theorem famV_ne_zero : ∀ (k : Nat) {c : TM.Term}, c ≠ zero → famV k c ≠ zero := by
  intro k
  induction k with
  | zero => intro c hc; exact hc
  | succ j ih =>
    intro c hc
    rw [famV_succ_ne j hc]
    intro h; exact TM.Term.noConfusion h

theorem plus_repAdd_one : ∀ (j : Nat), plus (repAdd eps0T j) one = famV (j + 1) one := by
  intro j
  induction j with
  | zero => rfl
  | succ i ih =>
    show plus (add eps0T (repAdd eps0T i)) one = _
    rw [plus_one_add (le_one_ap (show isAP eps0T = true from rfl)), ih,
      famV_succ_ne (i + 1) (show (one : TM.Term) ≠ zero from by intro h; exact TM.Term.noConfusion h)]

/-- The successor step: appending `1` commutes with the ε₀-prefix. -/
theorem plus_famV_one : ∀ (k : Nat) (p : TM.Term),
    plus (famV k p) one = famV k (plus p one) := by
  intro k
  induction k with
  | zero => intro p; rfl
  | succ j ih =>
    intro p
    by_cases hp : p = zero
    · subst hp
      rw [famV_zero_arg j, show plus (zero : TM.Term) one = one from rfl]
      exact plus_repAdd_one j
    · rw [famV_succ_ne j hp, plus_one_add (le_one_ap (show isAP eps0T = true from rfl)), ih p,
        famV_succ_ne j (plus_one_ne_zero p)]

/-- The bridge to `Evidence.WF.sumSeq`: the lane's sequence IS the family's value. -/
theorem sumSeq_famV : ∀ (k : Nat) (g : Nat → TM.Term), (∀ n, g n ≠ zero) → ∀ n,
    Evidence.WF.sumSeq eps0T g k n = famV k (g n) := by
  intro k
  induction k with
  | zero => intro g _ n; rfl
  | succ j ih =>
    intro g hg n
    show add eps0T (Evidence.WF.sumSeq eps0T g j n) = _
    rw [ih g hg n, famV_succ_ne j (hg n)]

/-! ### §18.3 THE CERTIFICATE RECURSION, against the WF §15.13 interface

`certIn_fam_of` is the whole recursion for the family, and it is LEXICOGRAPHIC on
`(k, c)` as §18.2 explains: outer induction on `k`, inner on `Acc RC c`, with the
`c = 0` case recursing to `(k-1, tower n)` because `epsBlocks (k+1)` expands in its
LAST block.  Its three cases use, in order, `certIn_padSq` (k = 0), `lim_clauses_fsA`
(c = 0), `plus_famV_one` + `plus_predC` (successor) and the `hsum` interface (limit);
the matrices come from §17.4's locality theorem throughout.

IT IS STATED AGAINST AN INTERFACE, in the idiom of `no_overshoot_of` and
`parent_append_gen`: `hdom`/`hdomz` are the `CNV` facts about the family's values and
`hsum` is `Evidence.WF.lim_clauses_sum_iter_gen` transported along `famV`.  All three
exist in WF §15.13 as of tonight; this file's copy of the oleans predates them, so the
instantiation — and with it `certIn_rowA` and the eleventh ✅ — is one rebuild away.

THE ROW IS THEREFORE NOT YET CERTIFIED, and nothing here should be read as saying it
is: `certIn_fam_of` is a conditional theorem, not a certificate, and no registry entry
cites it. -/

theorem sq_ne_nil {c : TM.Term} (hcn : CN c = true) (hz : c ≠ zero) : sq c ≠ [] := by
  intro h; exact hz (sq_eq_nil c hcn h)

theorem padRow_ne_nil {c : TM.Term} (hcn : CN c = true) (hz : c ≠ zero) : padRow (sq c) ≠ [] := by
  cases h : sq c with
  | nil => exact absurd h (sq_ne_nil hcn hz)
  | cons a t => simp [padRow]

theorem famM_eq (k : Nat) (c : TM.Term) : famM k c = epsBlocks k ++ padRow (sq c) := rfl

theorem epsBlocks_succ_right (k : Nat) :
    epsBlocks (k + 1) = epsBlocks k ++ [[0, 0], [1, 1]] := by
  show (List.replicate (k + 1) [[0, 0], [1, 1]]).flatten = _
  rw [List.replicate_succ']
  show (List.replicate k [[0,0],[1,1]] ++ [[[0,0],[1,1]]]).flatten = _
  rw [List.flatten_append]
  rfl

theorem famM_zero_arg (k : Nat) : famM k zero = epsBlocks k := by
  show epsBlocks k ++ padRow (sq zero) = _
  show epsBlocks k ++ ([] : Matrix) = _
  rw [List.append_nil]

theorem expand?_eps0_row (n : Nat) :
    BMS.expand? ([[0, 0], [1, 1]] : Matrix) n = some (towerM n) := by
  rw [show BMS.expand? [[0, 0], [1, 1]] n
      = some (((List.range (n + 1)).map (fun a => [[0 + a * 1 * 1, 0 + a * 0 * 1]])).flatten)
      from rfl]
  congr 1
  show ((List.range (n + 1)).map (fun a => [[0 + a * 1 * 1, 0 + a * 0 * 1]])).flatten = towerM n
  rw [show (fun (a : Nat) => [[0 + a * 1 * 1, 0 + a * 0 * 1]])
        = (fun (a : Nat) => [((fun (b : Nat) => [b, 0]) a)]) from by
      funext a; simp]
  rw [flatten_map_singleton]
  rfl

theorem eps0row_root : ∀ y, BMS.ent ([[0, 0], [1, 1]] : Matrix) 0 y = 0 := by
  intro y
  show (([0, 0] : List Nat)).getD y 0 = 0
  cases y with
  | zero => rfl
  | succ m => cases m with | zero => rfl | succ p => rfl

/-- The certificate family, modulo the two 𝔗(M)-side facts that WF §15.13 supplies:
    `hsum` is `lim_clauses_sum_iter_gen` transported along `famV`, and `hdom` is
    `CNV (famV k c)` (which needs `hdLe c ε₀`). -/
theorem certIn_fam_of
    (hdom : ∀ (k : Nat) (c : TM.Term), CN c = true → c ≠ zero → CNV (famV k c) = true)
    (hdomz : ∀ (k : Nat), CNV (repAdd eps0T k) = true)
    (hsum : ∀ (k : Nat) (c : TM.Term) (g : Nat → TM.Term), CN c = true → c ≠ zero →
      (∀ n, CN (g n) = true) → (∀ n, lt (g n) c = true) → (∀ n, lt (g n) (g (n + 1)) = true) →
      (∀ s, inT s = true → lt s c = true → ∃ n, le s (g n) = true) → (∀ n, g n ≠ zero) →
      (∀ n, lt (famV k (g n)) (famV k c) = true)
        ∧ (∀ n, lt (famV k (g n)) (famV k (g (n + 1))) = true)
        ∧ (∀ s, inT s = true → lt s (famV k c) = true → ∃ n, le s (famV k (g n)) = true)) :
    ∀ (k : Nat) (c : TM.Term), CN c = true → CertifiedIn DomI (famM k c) (famV k c) := by
  intro k
  induction k with
  | zero =>
    intro c hcn
    show CertifiedIn DomI (epsBlocks 0 ++ padRow (sq c)) c
    show CertifiedIn DomI (padRow (sq c)) c
    exact certifiedIn_mono domF_le_domI (certIn_padSq c hcn)
  | succ j ihk =>
    have key : ∀ (c : TM.Term), Acc Evidence.WF.RC c → CN c = true →
        CertifiedIn DomI (famM (j + 1) c) (famV (j + 1) c) := by
      intro c hacc
      induction hacc with
      | intro c _ ihc =>
        intro hcn
        by_cases hz : c = zero
        · subst hz
          obtain ⟨_, hlt, hstep, hcof⟩ := Evidence.WF.lim_clauses_fsA j
          rw [famM_zero_arg, epsBlocks_succ_right, famV_zero_arg]
          refine CertifiedIn.lim (fun n => famV j (Evidence.WF.tower n)) ?_ ?_ ?_ ?_ ?_ ?_
          · exact kind_append _ _ (by simp)
          · intro n
            show CertifiedIn DomI ((BMS.expand? (epsBlocks j ++ [[0,0],[1,1]]) n).getD [])
              (famV j (Evidence.WF.tower n))
            rw [expand?_append_root _ _ (by simp) eps0row_root n,
              show BMS.expand? ([[0,0],[1,1]] : Matrix) n = some (towerM n) from expand?_eps0_row n]
            show CertifiedIn DomI (epsBlocks j ++ towerM n) _
            rw [towerM_eq n]
            exact ihk _ (Evidence.WF.cn_tower n)
          · intro n
            show lt (famV j (Evidence.WF.tower n)) (repAdd eps0T j) = true
            rw [← sumSeq_famV j Evidence.WF.tower Evidence.WF.tower_ne_zero n]
            exact hlt n
          · intro n
            show lt (famV j (Evidence.WF.tower n)) (famV j (Evidence.WF.tower (n+1))) = true
            rw [← sumSeq_famV j Evidence.WF.tower Evidence.WF.tower_ne_zero n,
              ← sumSeq_famV j Evidence.WF.tower Evidence.WF.tower_ne_zero (n+1)]
            exact hstep n
          · intro s hin hlts
            obtain ⟨n, hn⟩ := hcof s hin hlts
            refine ⟨n, ?_⟩
            show le s (famV j (Evidence.WF.tower n)) = true
            rw [← sumSeq_famV j Evidence.WF.tower Evidence.WF.tower_ne_zero n]
            exact hn
          · show inT (repAdd eps0T j) = true
            exact Evidence.WF.inT_of_cnv _ (hdomz j)
        · by_cases hk : kindC c = true
          · have hcnp : CN (predC c) = true := Evidence.WF.cn_predC c hcn hk
            have hres : CertifiedIn DomI (famM (j+1) c) (plus (famV (j+1) (predC c)) one) := by
              refine CertifiedIn.succ ?_ ?_ ?_
              · rw [famM_eq]
                exact (kind_append _ _ (padRow_ne_nil hcn hz)).trans (kind_padSq_succ c hcn hk)
              · intro n
                show CertifiedIn DomI ((BMS.expand? (famM (j+1) c) n).getD []) _
                rw [famM_eq, expand?_append_root _ _ (padRow_ne_nil hcn hz)
                  (fun y => famM_root 0 c hcn (sq_ne_nil hcn hz) y) n,
                  expand_padSq_succ c hcn hk n]
                exact ihc (predC c) ⟨hcnp, Evidence.WF.lt_predC c hcn hk⟩ hcnp
              · rw [plus_famV_one, plus_predC c hcn hk]
                show inT (famV (j+1) c) = true
                exact Evidence.WF.inT_of_cnv _ (hdom (j+1) c hcn hz)
            rw [plus_famV_one, plus_predC c hcn hk] at hres
            exact hres
          · have hk' : kindC c = false := by simpa using hk
            obtain ⟨hcnfs, hltfs, hstepfs, hcoffs⟩ := Evidence.WF.lim_clauses c hcn hk' hz
            obtain ⟨s1, s2, s3⟩ := hsum (j+1) c (fsC c) hcn hz hcnfs hltfs hstepfs hcoffs
              (fun n => Evidence.WF.fsC_ne_zero c hcn hk' hz n)
            refine CertifiedIn.lim (fun n => famV (j+1) (fsC c n)) ?_ ?_ s1 s2 s3 ?_
            · rw [famM_eq]
              exact (kind_append _ _ (padRow_ne_nil hcn hz)).trans (kind_padSq_lim c hcn hk' hz)
            · intro n
              show CertifiedIn DomI ((BMS.expand? (famM (j+1) c) n).getD []) _
              rw [famM_eq, expand?_append_root _ _ (padRow_ne_nil hcn hz)
                (fun y => famM_root 0 c hcn (sq_ne_nil hcn hz) y) n,
                expand_padSq c hcn hk' hz n]
              exact ihc (fsC c n) ⟨hcnfs n, hltfs n⟩ (hcnfs n)
            · show inT (famV (j+1) c) = true
              exact Evidence.WF.inT_of_cnv _ (hdom (j+1) c hcn hz)
    intro c hcn
    exact key c (Evidence.WF.acc_cn c hcn) hcn

/-! ### §18.4 ROW A, CERTIFIED

`certIn_fam_of`'s three hypotheses, discharged from `Evidence/WF.lean` §15.13:
`cnv_repPre` and `cnv_repAdd` for the values, `lim_clauses_sum_iter_gen` transported
along `famV_eq_repPre` for the limit clause.  Then the row itself: its expansions are
the `eps0M n` (`expand_rowA`, §18), which are `famM (n+1) 0`, and its four premises
are `lim_clauses_rowA`.

    certIn_rowA : CertifiedIn DomI [[0,0],[1,1],[1,0]] (φ̄0(ε₀))

— the first LIMIT row above ε₀, and the first row whose certificate needed a family
that the CNF machinery could not express.  It is built GUARDED, as the registry gate
requires; `cert_rowA` is its image under `certifiedIn_forget`. -/

theorem famV_eq_repPre : ∀ (k : Nat) {c : TM.Term}, c ≠ zero →
    famV k c = Evidence.WF.repPre eps0T c k
  | 0, _, _ => rfl
  | k + 1, c, hc => by
    rw [famV_succ_ne k hc, famV_eq_repPre k hc]
    rfl

/-- **THE FAMILY, unconditionally.**  `certIn_fam_of`'s three hypotheses, discharged
    from `Evidence/WF.lean` §15.13. -/
theorem certIn_fam (k : Nat) (c : TM.Term) (hcn : CN c = true) :
    CertifiedIn DomI (famM k c) (famV k c) := by
  refine certIn_fam_of ?_ ?_ ?_ k c hcn
  · intro k c hcn hz
    rw [famV_eq_repPre k hz]
    exact Evidence.WF.cnv_repPre Evidence.WF.cnv_eps0T rfl (Evidence.WF.cnv_of_cn c hcn)
      (Evidence.WF.hdLe_cn_eps0T c hcn hz) k
  · intro k
    exact Evidence.WF.cnv_repAdd Evidence.WF.cnv_eps0T k
  · intro k c g hcn hz hg1 hg2 hg3 hg4 hgz
    obtain ⟨_, b2, b3, b4⟩ := Evidence.WF.lim_clauses_sum_iter_gen g Evidence.WF.cnv_eps0T rfl
      (Evidence.WF.cnv_of_cn c hcn) (Evidence.WF.hdLe_cn_eps0T c hcn hz)
      (fun n => Evidence.WF.cnv_of_cn _ (hg1 n)) hg2 hg3 hg4 hgz k
    refine ⟨?_, ?_, ?_⟩
    · intro n
      have := b2 n
      rwa [Evidence.WF.sumSeq_repPre, ← famV_eq_repPre k (hgz n),
        ← famV_eq_repPre k hz] at this
    · intro n
      have := b3 n
      rwa [Evidence.WF.sumSeq_repPre, Evidence.WF.sumSeq_repPre,
        ← famV_eq_repPre k (hgz n), ← famV_eq_repPre k (hgz (n+1))] at this
    · intro s hin hlts
      have hlt' : lt s (Evidence.WF.repPre eps0T c k) = true := by
        rwa [← famV_eq_repPre k hz]
      obtain ⟨n, hn⟩ := b4 s hin hlt'
      refine ⟨n, ?_⟩
      rwa [Evidence.WF.sumSeq_repPre, ← famV_eq_repPre k (hgz n)] at hn

/-- **ROW A: `(0,0)(1,1)(1,0)` = `φ̄0(ε₀)`, CERTIFIED.**  The first LIMIT row above ε₀. -/
theorem certIn_rowA : CertifiedIn DomI [[0, 0], [1, 1], [1, 0]] Evidence.WF.rowA := by
  obtain ⟨_, hlt, hstep, hcof⟩ := Evidence.WF.lim_clauses_rowA
  refine CertifiedIn.lim Evidence.WF.fsA rfl ?_ hlt hstep hcof ?_
  · intro n
    show CertifiedIn DomI ((BMS.expand? [[0, 0], [1, 1], [1, 0]] n).getD [])
      (Evidence.WF.fsA n)
    rw [expand_rowA n]
    show CertifiedIn DomI (eps0M n) (Evidence.WF.fsA n)
    rw [show eps0M n = famM (n + 1) zero from (famM_zero_arg (n + 1)).symm,
      show Evidence.WF.fsA n = famV (n + 1) zero from rfl]
    exact certIn_fam (n + 1) zero rfl
  · show inT Evidence.WF.rowA = true
    exact Evidence.WF.inT_of_cnv _ Evidence.WF.cnv_rowA

theorem cert_rowA : Certified [[0, 0], [1, 1], [1, 0]] Evidence.WF.rowA :=
  certifiedIn_forget certIn_rowA

/-! ## §19 THE ε₀-PREFIXED REGION MEETS THE CEILING  (2026-08-10)

Registering Row A obliges `certRows_no_overshoot` at the new row: no good principal
probe `≥ ω^(famV k c + 1)` is `≤` any value certified for `famM k c`.  §15.7's
`no_overshoot_of` cannot be instantiated for it — its bound is tied to the region
parameter `c` while the value here is `famV k c`; at `c = 0` the bound would read `ω`
and the value is ε₀·(k+1), so the invariant is FALSE in that form.  That is not a gap
in the ε₀-prefixed region; it is `no_overshoot_of` stating a CNF accident (parameter =
bound) as if it were part of the invariant.

So this section does not rebuild the induction.  It discharges §15.7.2's interface,
which asks only that the family's parameters are `CNV` and that each expansion's
parameter is STRICTLY BELOW.  Three facts do it:

  `kind_famM`      the kind of a family matrix, in THREE cases
  `lt_famV_fsC`    at a LIMIT parameter, `famV k (fsC c n) < famV k c`
  `lt_famV_tower`  at the `c = 0` parameter, `famV k (tower n) < ε₀·(k+1)`

plus `cnv_famV'` for the `CNV` side.  The last two are about the FAMILY, not about a
certificate: a certificate's own `lim` clauses bound ITS sequence, whereas the ceiling
compares the PARAMETERS of two region matrices.

WHAT THE CEILING SAVED HERE.  Before the generalisation this section needed a fourth
fact — "a CNV limit absorbs `+1`", `lt a v → CNV v → v a limit → le (plus a one) v` —
because the old `lim` step closed through `le_plus_one_of_lt_lim`, whose CN version
carries a limit hypothesis.  The WF lane delivered `le_plus_one_of_lt_cnv` WITHOUT
that hypothesis, which is what lets §15.7.2 avoid classifying a parameter's kind at
all.  That matters more than one saved lemma, because of the trap it sidesteps:
`kindC` IS WRONG ON CNV VALUES.  It branches on the second Veblen argument alone, so
`kindC (φ̄10) = true` — it calls ε₀ a SUCCESSOR, and likewise every ε and every ζ (WF
§15.3 `#guard`s exactly this).  Any interface that had classified the VALUES would
have been unstatable here.  `kind_famM` below does use `kindC`, and legitimately: only
on the CN parameter `c`, which is where `kindC` is correct. -/

/-- **NEGATIVE CONTROL FOR THE INTERFACE CHANGE.**  The header above says
    `no_overshoot_of` cannot be instantiated on this region.  That is not a remark
    about what was hard to prove: its CONCLUSION is FALSE here, and the witness is the
    ε₀ row itself, which is `famM 1 0`.

    Read with the region parameter as the bound — the CNF interface's shape — the
    invariant at `c = 0` would say that every good principal probe `≥ ω^(0+1) = ω`
    escapes every value certified for `famM 1 0`.  The probe `ω` qualifies on all
    three side conditions, the certificate is `cert_eps0`, and `ω ≤ ε₀`.

    The LAST conjunct is the one that keeps this from being a problem: under §19.2's
    bound `ω^(ε₀+1)` the same probe is excluded.  So what is refuted is the shape
    "parameter = bound", not the invariant — and the reason the ceiling could drop it
    is that `Reg M X` carries the bound separately from whatever indexes the region. -/
theorem bound_is_not_the_parameter :
    famM 1 zero = [[0, 0], [1, 1]] ∧ famV 1 zero = eps0T ∧
    Certified (famM 1 zero) (famV 1 zero) ∧
    (inT omega = true ∧ Evidence.WF.Frag omega = true ∧ isAP omega = true) ∧
    le (phi zero (plus (zero : TM.Term) one)) omega = true ∧
    le omega (famV 1 zero) = true ∧
    le (phi zero (plus (famV 1 zero) one)) omega = false :=
  ⟨rfl, rfl, cert_eps0, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- **The kind of a family matrix, in THREE cases.**  `c = 0` splits by `k`:
    `famM 0 0` is the empty matrix and `famM (k+1) 0` is a limit row (the ε₀ blocks).
    `kindC` appears here ONLY on the CN parameter `c`, where it is correct; it must
    NOT be used on the family's VALUES, which are CNV — WF §15.3 records that
    `kindC (φ̄10) = true`, i.e. it calls ε₀ a successor. -/
theorem kind_famM (k : Nat) (c : TM.Term) (hcn : CN c = true) :
    (BMS.kind (famM k c) = .zero ∧ k = 0 ∧ c = zero)
  ∨ (BMS.kind (famM k c) = .succ ∧ c ≠ zero ∧ kindC c = true)
  ∨ (BMS.kind (famM k c) = .lim ∧ ((c = zero ∧ k ≠ 0) ∨ (c ≠ zero ∧ kindC c = false))) := by
  by_cases hz : c = zero
  · subst hz
    rw [famM_zero_arg]
    cases k with
    | zero => exact Or.inl ⟨rfl, rfl, rfl⟩
    | succ j =>
      refine Or.inr (Or.inr ⟨?_, Or.inl ⟨rfl, by omega⟩⟩)
      rw [epsBlocks_succ_right]
      exact kind_append _ _ (by simp)
  · have hne : padRow (sq c) ≠ [] := padRow_ne_nil hcn hz
    by_cases hk : kindC c = true
    · refine Or.inr (Or.inl ⟨?_, hz, hk⟩)
      rw [famM_eq]
      exact (kind_append _ _ hne).trans (kind_padSq_succ c hcn hk)
    · have hk' : kindC c = false := by simpa using hk
      refine Or.inr (Or.inr ⟨?_, Or.inr ⟨hz, hk'⟩⟩)
      rw [famM_eq]
      exact (kind_append _ _ hne).trans (kind_padSq_lim c hcn hk' hz)

/-! ### §19.1 The family's own order facts

The three facts the ceiling asks for.  Note what is NOT here any more: the bound
arithmetic (`x ≤ x+1`, `t+1` stays in the fragment, the `Frag`/`inT` receipts for the
probe `ω^(X+1)`) used to live in this section stated about `famV k c`, and it now
lives in §15.7.1 stated about an arbitrary `CNV` term — which is all this section ever
used it at.  A region section should contain what is true of the REGION. -/

/-- The family's values are Veblen-fragment terms. -/
theorem cnv_famV (k : Nat) (c : TM.Term) (hcn : CN c = true) (hz : c ≠ zero) :
    CNV (famV k c) = true := by
  rw [famV_eq_repPre k hz]
  exact Evidence.WF.cnv_repPre Evidence.WF.cnv_eps0T rfl (Evidence.WF.cnv_of_cn c hcn)
    (Evidence.WF.hdLe_cn_eps0T c hcn hz) k

/-- The family's own order fact at a LIMIT parameter: the value of the `n`-th
    expansion is below the value.  (The certificate's own clauses say this for ITS
    sequence; this says it for the FAMILY, which is what the ceiling's bound needs.) -/
theorem lt_famV_fsC (k : Nat) (c : TM.Term) (hcn : CN c = true) (hz : c ≠ zero)
    (hk : kindC c = false) (n : Nat) : lt (famV k (fsC c n)) (famV k c) = true := by
  obtain ⟨hcnfs, hltfs, hstepfs, hcoffs⟩ := Evidence.WF.lim_clauses c hcn hk hz
  obtain ⟨_, b2, _, _⟩ := Evidence.WF.lim_clauses_sum_iter_gen (fsC c) Evidence.WF.cnv_eps0T rfl
    (Evidence.WF.cnv_of_cn c hcn) (Evidence.WF.hdLe_cn_eps0T c hcn hz)
    (fun n => Evidence.WF.cnv_of_cn _ (hcnfs n)) hltfs hstepfs hcoffs
    (fun n => Evidence.WF.fsC_ne_zero c hcn hk hz n) k
  have := b2 n
  rwa [Evidence.WF.sumSeq_repPre, ← famV_eq_repPre k (Evidence.WF.fsC_ne_zero c hcn hk hz n),
    ← famV_eq_repPre k hz] at this

/-- The same at the `c = 0` parameter, where the expansions are the towers. -/
theorem lt_famV_tower (k n : Nat) : lt (famV k (Evidence.WF.tower n)) (repAdd eps0T k) = true := by
  obtain ⟨_, b2, _, _⟩ := Evidence.WF.lim_clauses_fsA k
  have := b2 n
  rwa [show Evidence.WF.fsAin k n = famV k (Evidence.WF.tower n) from
    sumSeq_famV k Evidence.WF.tower Evidence.WF.tower_ne_zero n] at this

/-! ### §19.2 THE DISCHARGE

`Reg M X := ∃ k c, CN c ∧ M = famM k c ∧ X = famV k c`, and the three expansion
identities that make it a region.  The `lim` clause splits in two, by `kind_famM`: the
ε₀-block rows (`c = 0`, `k ≥ 1`), whose expansions are `famM (k-1) (tower n)`, and the
CNF-limit rows, whose expansions are `famM k (fsC c n)`.  The probe discipline is
§15.7.2's and is not restated here — no value certified for a family matrix is
mentioned by any lemma in this section. -/

theorem cnv_famV' (k : Nat) (c : TM.Term) (hcn : CN c = true) : CNV (famV k c) = true := by
  by_cases hz : c = zero
  · subst hz
    cases k with
    | zero => rfl
    | succ j => rw [famV_zero_arg]; exact Evidence.WF.cnv_repAdd Evidence.WF.cnv_eps0T j
  · exact cnv_famV k c hcn hz

/-- At a successor parameter the family steps down in the CNF argument. -/
theorem expand_famM_succ (k : Nat) (c : TM.Term) (hcn : CN c = true) (hzc : c ≠ zero)
    (hkc : kindC c = true) : BMS.expand (famM k c) 0 = famM k (predC c) := by
  rw [famM_eq]
  show (BMS.expand? (epsBlocks k ++ padRow (sq c)) 0).getD [] = _
  rw [expand?_append_root _ _ (padRow_ne_nil hcn hzc)
    (fun y => famM_root 0 c hcn (sq_ne_nil hcn hzc) y) 0, expand_padSq_succ c hcn hkc 0]
  rfl

/-- At a CNF-limit parameter the family follows `fsC`. -/
theorem expand_famM_lim (k : Nat) (c : TM.Term) (hcn : CN c = true) (hzc : c ≠ zero)
    (hkc : kindC c = false) (n : Nat) : BMS.expand (famM k c) n = famM k (fsC c n) := by
  rw [famM_eq]
  show (BMS.expand? (epsBlocks k ++ padRow (sq c)) n).getD [] = _
  rw [expand?_append_root _ _ (padRow_ne_nil hcn hzc)
    (fun y => famM_root 0 c hcn (sq_ne_nil hcn hzc) y) n, expand_padSq c hcn hkc hzc n]
  rfl

/-- At the `c = 0` parameter an ε₀ BLOCK is consumed and the CNF argument becomes a
    tower — the one step that moves the family's first index. -/
theorem expand_famM_block (j n : Nat) :
    BMS.expand (famM (j + 1) zero) n = famM j (Evidence.WF.tower n) := by
  rw [famM_zero_arg, epsBlocks_succ_right]
  show (BMS.expand? (epsBlocks j ++ [[0, 0], [1, 1]]) n).getD [] = _
  rw [expand?_append_root _ _ (by simp) eps0row_root n, expand?_eps0_row n]
  show epsBlocks j ++ towerM n = _
  rw [towerM_eq n]
  rfl

/-- **THE CEILING FOR THE ε₀-PREFIXED REGION** — §15.7.2 at this region.  No
    induction: the statement is `no_overshoot_ceiling` with `Reg` instantiated, and
    the proof is the three interface facts. -/
theorem no_overshoot_fam : ∀ {N : Matrix} {v : TM.Term}, Certified N v →
    ∀ (k : Nat) (c : TM.Term), CN c = true → N = famM k c →
      ∀ (s : TM.Term), inT s = true → Evidence.WF.Frag s = true → isAP s = true →
        le (phi zero (plus (famV k c) one)) s = true → le s v = false := by
  intro N v hc k c hcn hN
  refine no_overshoot_ceiling
    (fun M X => ∃ (k : Nat) (c : TM.Term), CN c = true ∧ M = famM k c ∧ X = famV k c)
    ?_ ?_ ?_ hc (famV k c) ⟨k, c, hcn, hN, rfl⟩
  · intro M X hr
    obtain ⟨k, c, hcn, _, hX⟩ := hr
    rw [hX]; exact cnv_famV' k c hcn
  · intro M X hr hkm
    obtain ⟨k, c, hcn, hM, hX⟩ := hr
    subst hM; subst hX
    have hcase : c ≠ zero ∧ kindC c = true := by
      rcases kind_famM k c hcn with ⟨hz, _, _⟩ | ⟨_, hne, hkc⟩ | ⟨hl, _⟩
      · rw [hz] at hkm; exact absurd hkm (by simp)
      · exact ⟨hne, hkc⟩
      · rw [hl] at hkm; exact absurd hkm (by simp)
    obtain ⟨hzc, hkc⟩ := hcase
    have hcnp : CN (predC c) = true := Evidence.WF.cn_predC c hcn hkc
    refine ⟨famV k (predC c),
      ⟨k, predC c, hcnp, expand_famM_succ k c hcn hzc hkc, rfl⟩, ?_⟩
    rw [show famV k c = plus (famV k (predC c)) one from by
      rw [plus_famV_one, plus_predC c hcn hkc]]
    exact lt_self_plus_one_cnv _ (cnv_famV' k (predC c) hcnp)
  · intro M X hr hkm n
    obtain ⟨k, c, hcn, hM, hX⟩ := hr
    subst hM; subst hX
    have hcase : (c = zero ∧ k ≠ 0) ∨ (c ≠ zero ∧ kindC c = false) := by
      rcases kind_famM k c hcn with ⟨hz, _, _⟩ | ⟨hs, _, _⟩ | ⟨_, hd⟩
      · rw [hz] at hkm; exact absurd hkm (by simp)
      · rw [hs] at hkm; exact absurd hkm (by simp)
      · exact hd
    rcases hcase with ⟨hz, hk0⟩ | ⟨hzc, hkc⟩
    · subst hz
      cases k with
      | zero => exact absurd rfl hk0
      | succ j =>
        refine ⟨famV j (Evidence.WF.tower n),
          ⟨j, Evidence.WF.tower n, Evidence.WF.cn_tower n, expand_famM_block j n, rfl⟩, ?_⟩
        rw [famV_zero_arg]
        exact lt_famV_tower j n
    · obtain ⟨hcnfs, _, _, _⟩ := Evidence.WF.lim_clauses c hcn hkc hzc
      exact ⟨famV k (fsC c n),
        ⟨k, fsC c n, hcnfs n, expand_famM_lim k c hcn hzc hkc n, rfl⟩,
        lt_famV_fsC k c hcn hzc hkc n⟩

/-! ## §20 THE ε-LADDER  (the (B)-shaped rows, STARTED)

Row A's certificate covers the ε₀-prefixed region.  The next four rows are the
ε-hierarchy, and the WF lane's measurement is that they are ONE LADDER rather than
four rows: ζ₀'s level 1 IS the ε_{ε₀} row, whose level 1 IS the ε_{ω^ω} row, whose
level 1 IS the ε_{ω²} row, and all three (C) rows' level 0 IS the ε_ω row.  So the
right shape here is one family parameterised by ladder position — the same move
`famM k c` made one level down — with the rows as instances.

MEASURED FIRST (`#guard`s below):

    epsM k = (0,0)(1,1) ++ (1,1)^k          has value  φ̄(1,k) = ε_k
    (0,0)(1,1)(2,0)[n] = epsM n             the ε_ω row expands to the ε-hierarchy ITSELF
    epsM 1 [n] = ε₀, ω^(ε₀·2), ω^(ω^(ε₀·2)), …   a TOWER over ε₀·2, not over ε₀

The third line is why the ladder is not uniform: the ε_ω row's expansions are the
ladder's own rungs, but each RUNG's expansions leave the ladder for a tower family
one level down.  `expand_epsOmega` below is the first of those identities, and it is
the same computation as Row A's: the last column is `(2,0)`, so `t = 0`, the ascension
vanishes, and the bad part `(1,1)` is copied `n+1` times after the root.

TWO ROUTING TRAPS from the WF lane, recorded before anyone writes the branch table:
`φ̄1(ω)` is NOT the ε-limit branch, and that ω exception recurs at `φ̄(a,ω)` for every
`a`.  Its cause is measured: `fsC ω n = ofNat (n+1)`, a 1-BASED sequence index against
the matrix's 0-based one.  A branch table that routes on shape alone will mis-route
exactly there. -/

/-! ### §20.1 PAIRING THE WF BUNDLES AGAINST THE MATRICES

The WF lane's clause bundles are 𝔗(M)-side: they say what sequence a term's four
premises are proved for, and NOTHING about whether that sequence is the one this
row's matrix expands to.  The identity premise `∀ n, Certified (expand M n) (fs' n)`
is where a wrong pairing must fail — but it fails at proof time, after the work.
These are the cheap pre-checks, and they are MEASUREMENTS (`Trans.oR` is candidate
tier and appears in no justification here — and it is `oR`, not the retracted `o?`;
see `Evidence/SqV.lean` §1.1).

They also CONFIRM veblen2's routing trap 1 from the matrix side: the ε_ω row's n-th
expansion has value `ε_n` (0-based), so the bundle's `fsEW n = φ̄1(ofNat n)` pairs and
the `fsC`-based routing `φ̄1(fsC ω n) = ε_{n+1}` does NOT.  Their trap was derived from
`fsC`'s off-by-one; this is the same fact seen from the expansion, and `expand_epsOmega`
below turns the matrix half of it into a theorem. -/

#guard (List.range 5).all (fun n =>
  Trans.oR (BMS.expand [[0, 0], [1, 1], [2, 0]] n) == some (Evidence.WF.fsEW n))
#guard (List.range 5).all (fun n =>
  !(Trans.oR (BMS.expand [[0, 0], [1, 1], [2, 0]] n)
      == some (phi one (Evidence.WF.fsC omega n))))
#guard (List.range 4).all (fun n =>
  Trans.oR (BMS.expand [[0, 0], [1, 1], [1, 1]] n) == some (Evidence.WF.fsEsucc 0 n))

/-- The matrix of ε_k: the ε₀ row with `k` further ε-steps at depth 1. -/
def epsM (k : Nat) : Matrix := [[0, 0], [1, 1]] ++ (List.replicate k [[1, 1]]).flatten

theorem epsM_zero : epsM 0 = [[0, 0], [1, 1]] := rfl

theorem map_const_flatten2 : ∀ (m : Nat) (B : Matrix),
    ((List.range m).map (fun _ => B)).flatten = (List.replicate m B).flatten := by
  intro m B
  induction m with
  | zero => rfl
  | succ j ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, ih, List.replicate_succ',
      List.flatten_append]
    rfl

/-- **The ε_ω row expands to the ε-hierarchy itself.**  Its last column is `(2,0)`,
    so `t = 0` and the ascension vanishes exactly as in Row A; the bad part is the
    single column `(1,1)`, copied `n+1` times after the root. -/
theorem expand_epsOmega (n : Nat) :
    BMS.expand? [[0, 0], [1, 1], [2, 0]] n = some (epsM n) := by
  have hblk : ∀ (a : Nat), ((List.range 1).map (fun x =>
      (List.range 2).map (fun y =>
        BMS.ent [[0, 0], [1, 1], [2, 0]] (1 + x) y +
          a * BMS.delta [[0, 0], [1, 1], [2, 0]] 1 0 y *
            (if BMS.ascends [[0, 0], [1, 1], [2, 0]] 1 (1 + x) y then 1 else 0))))
      = ([[1, 1]] : Matrix) := by
    intro a; rfl
  show some (([[0, 0], [1, 1], [2, 0]] : Matrix).take 1 ++
      ((List.range (n + 1)).map (fun a =>
        (List.range 1).map (fun x =>
          (List.range 2).map (fun y =>
            BMS.ent [[0, 0], [1, 1], [2, 0]] (1 + x) y +
              a * BMS.delta [[0, 0], [1, 1], [2, 0]] 1 0 y *
                (if BMS.ascends [[0, 0], [1, 1], [2, 0]] 1 (1 + x) y then 1 else 0))))).flatten)
    = some (epsM n)
  rw [List.map_congr_left (l := List.range (n + 1))
      (g := fun _ => ([[1, 1]] : Matrix)) (fun a _ => hblk a),
    map_const_flatten2]
  rfl

/-! ### §20.2 THE RUNGS, MEASURED AT THREE LEVELS

§20 records that each rung's expansions LEAVE the ladder — `epsM 1`'s tower over ε₀·2.
One rung does not determine the family: "tower over ε₀·2", "tower over ε_k·2" and
"tower over `famV`'s value at that rung" all agree at k = 1 and disagree above it, and
reading the closed form off k = 1 is deriving it from one data point.  So it was
measured at k = 1, 2, 3 before anything was designed:

  THE CLOSED FORM IS `tower over ε_k·2` — which is exactly the WF lane's own `fsEsucc k`:
      o? (expand (epsM (k+1)) n) = fsEsucc k n            k ≤ 2, n ≤ 3
  AND THE ONE-LEVEL GENERALISATION IS REFUTED:
      the same with `fsEsucc 0` for every k holds at k = 0 and FAILS at k = 1 and 2.

The second `#guard` is the one worth having.  A check that only confirms the surviving
candidate cannot say that the others were excluded — and here the excluded candidate is
the one a reader would most naturally have written down.  It reports the outcome PER k
rather than negating the universal: `!all` would also have passed if the failure were at
k = 2 alone, which is a weaker statement than the paragraph above makes.  A section whose
point is that guards must exclude should hold itself to that.

So the family under the ladder is ε_k-PREFIXED, not ε₀-prefixed: `no_overshoot_fam`
(§19.2) does not cover the (B) rows, and the ceiling has to generalise along the same
index.  That is now a measurement rather than the guess §20 left open.

RETRACTED (§20.3, immediately below).  The last paragraph is WRONG: measuring the rungs
fixed their sequence but said nothing about the closure, and the closure shows the family
is not ε_k-prefixed at all — it is the TAIL that widens, not the prefix.  The paragraph is
kept rather than deleted because it is the conclusion a reader arrives at from Row A, and
its refutation is worth more standing next to it than gone. -/

#guard (List.range 3).all (fun k => (List.range 4).all (fun n =>
  Trans.oR (BMS.expand (epsM (k + 1)) n) == some (Evidence.WF.fsEsucc k n)))
#guard ((List.range 3).map (fun k => (List.range 4).all (fun n =>
  Trans.oR (BMS.expand (epsM (k + 1)) n) == some (Evidence.WF.fsEsucc 0 n))))
    == [true, false, false]

/-- The expansion closure to depth 3, sampling `n ≤ 2` — a measurement helper. -/
def clo3 (m : BMS.Matrix) : List BMS.Matrix :=
  Nat.rec [m] (fun _ acc =>
    (acc ++ acc.flatMap (fun x => (List.range 3).map (BMS.expand x))).eraseDups) 3

/-! ### §20.3 THE TAIL WIDENS — why the (B) rows are NOT an ε_k-prefixed family

§20.2 fixed the rungs' closed form.  The natural next design — `famM` with the ε-BLOCK
COUNT as a second index, i.e. the ε₀-prefixed region generalising to an ε_k-prefixed one
— is REFUTED by the closure, and it is worth recording because it is the design a reader
arrives at from Row A:

    ε₁'s expansion closure to depth 3 is 30 matrices
      18 are `famM`-shaped   (ε₀ blocks followed by a padded CNF row)
      12 are NOT             e.g. (0,0)(1,1)(1,0)(2,1),  (0,0)(1,1)(1,0)(2,1)(2,0)(3,1)

The twelve are the ε₀ row followed by columns carrying second-row 1 at depth ≥ 2, and
their values are ω^(ε₀·2), ω^(ω^(ε₀·2)), … — CNF-over-ε₀ terms.  Those are `padRow (sq c)`
for NO `CN c`, because `sq` is defined on the CNF region and these exponents contain ε₀.

SO IT IS THE TAIL THAT WIDENS, NOT THE PREFIX.  The (B) family is "blocks followed by a
tail over the VEBLEN region", and encoding that tail is exactly `Evidence/SqV.lean`'s job.
A rung index does not reach the defect, which is why no amount of measuring rungs would
have exposed it — §20.2's measurements were necessary and not sufficient.

CONSEQUENCE FOR THE CEILING, DISCHARGED (2026-08-10).  This paragraph used to read
"the generalised ceiling WILL subsume `no_overshoot_fam` … it cannot be built before
the tail encoding exists".  The first half happened and the second half was wrong.
`no_overshoot_ceiling` (§15.7.2) is built, Row A's ✅ rests on it, and so do the CNF
rows: there is now one induction on `Certified` in this file instead of two.

The tail encoding was not needed because the ceiling does not encode anything.  It
asks a region for a strictly smaller PARAMETER at each expansion, and never asks what
the parameter looks like — so `sqv`'s job is not a precondition of the ceiling, it is a
precondition of DISCHARGING the ceiling on the (B) rows.  What §20.3 measures is
exactly that remaining half: the twelve non-`famM` matrices are the region this file
cannot yet name, and naming a region is all that is left.

**THE REGION IS NOW NAMED** (2026-08-16), in `Evidence/Region.lean`.  It is not a `famM`
with a wider tail and it is not a `φ̄` recursion: in BUCHHOLZ-TREE coordinates the whole
closure is `ψ₀(ξ)` for `ξ < Ω·ω`, summed — width-two matrices read as a forest by their
row-0 entries, with `(d,0)` a `ψ₀` node at depth `d` and `(d,1)` an `Ω`.  §16.5 said `enc`
is compositional in those coordinates and not in `φ̄` ones; that is exactly why the twelve
resisted naming here.  `Evidence.Region.expand_mat` is the closure theorem

    BMS.expand? (mat t 0) n = some (mat (fs t n) 0)

for every top-level index, with NO hypothesis on normal form and none on the prefix, and
`Evidence/RegionV.lean` carries the value `sumVal`, Buchholz's normal form, and the
measurements for the three supplies.  ONE region carries TWO rows: ε₁'s row is
`mat (ps nil (omPow 2)) 0`, and `epsM k` — §20's ladder rung, the ε_ω row's k-th expansion
by `expand_epsOmega` — is `mat (ps nil (omPow (k+1))) 0`.

STATE OF THE THREE SUPPLIES (RegionV).  `Hzero`, `Hsucc` and `Hclosed` are all THEOREMS
now (§12 and §13), and the value is always `CNV` (§11, via `Evidence/CNVOps.lean`).
`Hclosed`'s last case, `CaseThree`, closed on 2026-08-16 and is not an order fact but a
LENGTH fact: the fixed-point condition `a ∈ C₀(a)` makes `b` a prefix of `c` in the only
hard case, and `ψ₀(c)[0]` is a prefix of `ψ₀(c)` that is no shorter than `c`, so the tail
of `c` cannot overshoot it (`Evidence/CmpM.lean`'s `cmpM_le_of_len`).  Neither the
descending condition nor the value is used.

`Hlim` is what remains, and §14 has now REDUCED it to ONE hole.  `fs` acts on the last
summand, so the value of an expansion is the untouched prefix plus the sequence member —
which needed `sumVal (app r s) = sumVal r ⊕ sumVal s`, hence associativity of `plus`, which
the repo did not have and now does (`Evidence/CNVOps.lean` §19).  The prefix half is also
proved (§23's `lim_clauses_prefix`: a fixed prefix on the left preserves all four clauses,
with NO side condition), on top of a new layer — §20 reads the term order off the component
list, which is what lets `plus`, a list operation, be reasoned about at all.

What is left is `ArgLim`: the four clauses for ONE principal term `ω^(argVal a)` and its
sequence `fsP a n`.  Three cases, one per case of `fsP`, and `Evidence/WF.lean`'s
`lim_clauses_repAdd` / `lim_clauses_phi_arg` / `lim_clauses_fsGen` are aimed at exactly
those three. -/

#guard ((clo3 [[0, 0], [1, 1], [1, 1]]).length, ((clo3 [[0, 0], [1, 1], [1, 1]]).filter
  (fun m => (List.range 6).any (fun k =>
    m.take (2 * k) == (List.replicate k [[0, 0], [1, 1]]).flatten &&
    (m.drop (2 * k)).all (fun c => c.getD 1 0 == 0)))).length) == (30, 18)

/-! ## §6 The registry

gentable marks ✅ exactly on the rows listed here; the GATE is `certIn_rows_inT`.

MOVED TO THE END OF THE FILE (certificate lane, 2026-08-09).  It used to sit
between §5.15 and §7, but the ε₀ row's certificate is built in §13 and Lean needs
it in scope before the gate can cite it.  Registry and gate stay together;
nothing outside this file depends on their position.

THE GATE IS NOW GUARDED (certificate lane, 2026-08-09, approved by the coordinator).
It used to be `certRows_ok`, i.e. plain `Certified`, and §15.9's
`cert_not_single_valued` shows what that lets through: `Certified` is satisfied by
values that are not terms of 𝔗(M) at all (the ω row also certifies `1 + M`), so a
row could in principle be registered on the strength of a derivation whose values
wander outside the notation system.  The gate is therefore

    certIn_rows_inT : ∀ p ∈ certRows, CertifiedIn DomI p.1 p.2

with `DomI t := inT t = true` — the values are TERMS OF 𝔗(M), all the way down.
That is plan/README.md's design input 2 enforced at the level where the ✅ is
computed, and it is strictly stronger than the old gate: `certRows_ok` is now its
image under `certifiedIn_forget`, so every consumer of the old statement is
unaffected.

WHAT THE GATE BUYS (2026-08-09, after Stage 3b).  Since `Evidence/WF.lean` §8.5
gives a strict linear order on 𝔗(M), the gate's own guard is now enough for
UNIQUENESS: `certRows_unique_gate` (§6.1) says a registered row's value is the only
value ANY gate-passing certificate can carry — above or below.  Registration and
uniqueness therefore ask for exactly the same thing, which is the property one wants
of a gate.

WHY `DomI` AND NOT `DomF`.  `DomF = Frag2 ∧ inT` is the guard uniqueness is
discharged on today (§14.3), but `Frag2` EXCLUDES `ψ` and `Z` — the shapes the
whole T(M) table is aiming at.  A `DomF` gate would refuse the first `ψ` row (Γ₀)
for a reason that has nothing to do with whether its certificate is sound: it
would look like rigour and act as a wall in front of the target.  So the gate asks
only for membership in 𝔗(M), which every legitimate future row can satisfy, and
UNIQUENESS stays a separate, per-region theorem (`certRows_unique_guarded` on
`DomF` today, wider as the order theory widens, with `certifiedIn_mono` bridging
the two). -/

/-- The registered certified rows. -/
def certRows : List (Matrix × Term) :=
  [([], Term.zero), ([[0]], one), ([[0], [0]], ofNat 2), ([[0], [1]], omega),
   ([[0], [1], [0], [1]], add omega omega), ([[0], [1], [1]], phi zero (ofNat 2)),
   ([[0], [1], [2]], phi zero omega),
   ([[0], [1], [2], [3]], phi zero (phi zero omega)),
   ([[0, 0], [1, 1]], phi one zero),
   ([[0, 0], [1, 1], [0, 0]], plus (phi one zero) one),
   ([[0, 0], [1, 1], [1, 0]], Evidence.WF.rowA)]

/-- **THE GATE.**  Every registered pair carries a derivation whose values are all
    terms of 𝔗(M).  Extending `certRows` without extending this proof breaks the
    build — the label cannot outrun the certificates, and (since v0.1.80) it cannot
    outrun the formation conditions either. -/
theorem certIn_rows_inT : ∀ p ∈ certRows, CertifiedIn DomI p.1 p.2 := by
  intro p hp
  simp only [certRows, List.mem_cons] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h
  · rw [h]; exact CertifiedIn.zero
  · rw [h]; exact certifiedIn_mono domF_le_domI (certIn_sq one (by decide))
  · rw [h]; exact certifiedIn_mono domF_le_domI (certIn_sq (ofNat 2) (by decide))
  · rw [h]; exact certifiedIn_mono domF_le_domI (certIn_sq omega (by decide))
  · rw [h]; exact certifiedIn_mono domF_le_domI (certIn_sq (add omega omega) (by decide))
  · rw [h]; exact certifiedIn_mono domF_le_domI (certIn_sq (phi zero (ofNat 2)) (by decide))
  · rw [h]; exact certifiedIn_mono domF_le_domI (certIn_sq (phi zero omega) (by decide))
  · rw [h]
    exact certifiedIn_mono domF_le_domI (certIn_sq (phi zero (phi zero omega)) (by decide))
  · rw [h]; exact certifiedIn_mono domF_le_domI certIn_eps0
  · rw [h]; exact certifiedIn_mono domF_le_domI certIn_eps0_succ_F
  · rw [h]; exact certIn_rowA
  · cases h

/-- The old gate, now a COROLLARY of the guarded one: forget the guard.  Kept
    verbatim so that every consumer of the previous statement is unaffected. -/
theorem certRows_ok : ∀ p ∈ certRows, Certified p.1 p.2 :=
  fun p hp => certifiedIn_forget (certIn_rows_inT p hp)

/-! ### §6.1 The registry, read as uniqueness and as a ceiling (certificate lane) -/

/-- **THE TABLE'S ✅, READ AS UNIQUENESS — at the gate's own guard.**  For every
    registered row, ANY certificate that passes the gate (values hereditarily in
    𝔗(M)) carries the registered value and no other.  With `certRows_no_overshoot`
    below, this is the pair that makes the ✅ a claim about the VALUE: nothing else
    is certifiable at gate quality, and nothing above it is certifiable at all. -/
theorem certRows_unique_gate :
    ∀ p ∈ certRows, ∀ (u : Term), CertifiedIn DomI p.1 u → u = p.2 :=
  fun p hp _ h => (cert_unique_inT (certIn_rows_inT p hp) h).symm

/-- The `DomF` form, kept verbatim (the legend was written against it): a corollary
    of `certRows_unique_gate`, since a `DomF`-guarded certificate is `DomI`-guarded. -/
theorem certRows_unique_guarded :
    ∀ p ∈ certRows, ∀ (u : Term), CertifiedIn DomF p.1 u → u = p.2 :=
  fun p hp u h => certRows_unique_gate p hp u (certifiedIn_mono domF_le_domI h)


/-- **THE TABLE'S ✅, READ AS AN UPPER BOUND.**  For every registered row, NO
    certificate at all — no guard, junk values allowed at every level — carries a
    value that reaches `ω^(value+1)`.  §15.8 says much more for the ε₀ row (nothing
    above ε₀ at all); the two together are what makes the ✅ column a claim about
    the VALUE rather than about one derivation. -/
theorem certRows_no_overshoot : ∀ p ∈ certRows, ∀ (u : Term), Certified p.1 u →
    le (phi zero (plus p.2 one)) u = false := by
  intro p hp u h
  simp only [certRows, List.mem_cons] at hp
  rcases hp with e | e | e | e | e | e | e | e | e | e | e | e
  · subst e; exact cert_below_bound_one zero (by decide) u h
  · subst e; exact cert_below_bound_one one (by decide) u h
  · subst e; exact cert_below_bound_one (ofNat 2) (by decide) u h
  · subst e; exact cert_below_bound_one omega (by decide) u h
  · subst e; exact cert_below_bound_one (add omega omega) (by decide) u h
  · subst e; exact cert_below_bound_one (phi zero (ofNat 2)) (by decide) u h
  · subst e; exact cert_below_bound_one (phi zero omega) (by decide) u h
  · subst e; exact cert_below_bound_one (phi zero (phi zero omega)) (by decide) u h
  · subst e; exact cert_below_bound_eps0 u h
  · -- the ε₀+1 row: a SUCCESSOR row, so §15.10's transport carries the ε₀ row's
    -- ceiling across it, at the probe `ω^((ε₀+1)+1)`
    subst e
    show le (phi zero (plus (plus (phi one zero) one) one)) u = false
    have hone : le one (phi one zero) = true := le_one_ap rfl
    have hval : plus (plus (phi one zero) one) one = add (phi one zero) (add one one) := by
      rw [plus_one_ap (show isAP (phi one zero) = true from rfl) hone,
        plus_one_add hone, plus_one_ap (show isAP one = true from rfl) (le_one_ap rfl)]
    have hne : add (phi one zero) one ≠ add (phi one zero) (add one one) := by
      intro hc; injection hc with _ h2; exact Term.noConfusion h2
    have hlt1 : lt (add (phi one zero) one) (add (phi one zero) (add one one)) = true := by
      rw [Evidence.WF.lt_add_add hne, if_pos rfl,
        lt_ap_add (show isAP one = true from rfl) one one]
      exact Evidence.WF.le_self one
    have hbnd : le (phi zero (plus (phi one zero) one))
        (phi zero (add (phi one zero) (add one one))) = true := by
      show ((phi zero (plus (phi one zero) one) == phi zero (add (phi one zero) (add one one)))
        || lt (phi zero (plus (phi one zero) one))
             (phi zero (add (phi one zero) (add one one)))) = true
      rw [plus_one_ap (show isAP (phi one zero) = true from rfl) hone, Evidence.WF.lt_pow, hlt1]
      exact Bool.or_true _
    rw [hval]
    refine cert_below_bound_succ (N' := [[0, 0], [1, 1]]) rfl rfl rfl ?_ ?_ u h
    · exact le_pow_one_false (by intro hc; exact Term.noConfusion hc)
    · intro w hw
      exact cert_eps0_row_ceiling (by decide) rfl rfl hbnd w hw
  · -- Row A: the ceiling for the ε₀-prefixed region (§19.2), at each expansion
    subst e
    show le (phi zero (plus Evidence.WF.rowA one)) u = false
    have hceil : ∀ (n : Nat) (w : Term), Certified (eps0M n) w →
        ∀ (s : Term), inT s = true → Evidence.WF.Frag s = true → isAP s = true →
          le (phi zero (plus (Evidence.WF.fsA n) one)) s = true → le s w = false := by
      intro n w hw s hin hfr hap hbb
      exact no_overshoot_fam hw (n + 1) zero rfl (famM_zero_arg (n + 1)).symm s hin hfr hap hbb
    obtain ⟨fs, hall, _, _, hcof⟩ :=
      certified_lim_inv h (show BMS.kind [[0, 0], [1, 1], [1, 0]] = .lim from rfl)
    have hcert : ∀ n, Certified (eps0M n) (fs n) := by
      intro n
      have hx := hall n
      rwa [show BMS.expand [[0, 0], [1, 1], [1, 0]] n = eps0M n from by
        show (BMS.expand? [[0, 0], [1, 1], [1, 0]] n).getD [] = _
        rw [expand_rowA n]; rfl] at hx
    have hbound : ∀ (n : Nat) (X : Term), CNV X = true → le Evidence.WF.rowA X = true →
        le (phi zero (plus (Evidence.WF.fsA n) one)) (phi zero X) = true := by
      intro n X hcx hlex
      refine Evidence.WF.le_pow (Evidence.WF.le_trans
        (Evidence.WF.frag_of_cnv _ (cnv_plus_one _ (Evidence.WF.cnv_repAdd
          Evidence.WF.cnv_eps0T n)))
        (Evidence.WF.frag_of_cnv _ Evidence.WF.cnv_rowA)
        (Evidence.WF.frag_of_cnv _ hcx) ?_ hlex)
      exact Evidence.WF.le_plus_one_of_lt_cnv
        (Evidence.WF.cnv_repAdd Evidence.WF.cnv_eps0T n) Evidence.WF.cnv_rowA
        ((Evidence.WF.lim_clauses_rowA).2.1 n)
    cases hlev : le (phi zero (plus Evidence.WF.rowA one)) u with
    | false => rfl
    | true =>
      exfalso
      simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at hlev
      rcases hlev with rfl | hlt
      · -- u = ω^(rowA+1): probe with ω^rowA, strictly below it
        have hltu : lt (phi zero Evidence.WF.rowA)
            (phi zero (plus Evidence.WF.rowA one)) = true := by
          rw [Evidence.WF.lt_pow]
          exact lt_self_plus_one_cnv _ Evidence.WF.cnv_rowA
        obtain ⟨n, hn⟩ := hcof (phi zero Evidence.WF.rowA)
          (Evidence.WF.inT_of_cnv _ (by
            show (CNV zero && CNV Evidence.WF.rowA) = true
            rw [Evidence.WF.cnv_rowA]; rfl)) hltu
        rw [hceil n (fs n) (hcert n) _ (Evidence.WF.inT_of_cnv _ (by
            show (CNV zero && CNV Evidence.WF.rowA) = true
            rw [Evidence.WF.cnv_rowA]; rfl))
          (Evidence.WF.frag_omegaPow (Evidence.WF.frag_of_cnv _ Evidence.WF.cnv_rowA)) rfl
          (hbound n Evidence.WF.rowA Evidence.WF.cnv_rowA (Evidence.WF.le_self _))] at hn
        exact Bool.noConfusion hn
      · obtain ⟨n, hn⟩ := hcof (phi zero (plus Evidence.WF.rowA one))
          (Evidence.WF.inT_of_cnv _ (by
            show (CNV zero && CNV (plus Evidence.WF.rowA one)) = true
            rw [cnv_plus_one _ Evidence.WF.cnv_rowA]; rfl)) hlt
        rw [hceil n (fs n) (hcert n) _ (Evidence.WF.inT_of_cnv _ (by
            show (CNV zero && CNV (plus Evidence.WF.rowA one)) = true
            rw [cnv_plus_one _ Evidence.WF.cnv_rowA]; rfl))
          (Evidence.WF.frag_omegaPow (Evidence.WF.frag_of_cnv _
            (cnv_plus_one _ Evidence.WF.cnv_rowA))) rfl
          (hbound n (plus Evidence.WF.rowA one) (cnv_plus_one _ Evidence.WF.cnv_rowA)
            (le_self_plus_one_cnv _ Evidence.WF.cnv_rowA))] at hn
        exact Bool.noConfusion hn
  · cases e

/-! ### §20.1 TWO MORE ROW EXPANSION IDENTITIES — `ε_{ω²}` and `ε_{ω^ω}`

Same skeleton as `expand_rowA` and `expand_epsOmega`: an `hblk` closed by `intro a; rfl`, then a
`show` of `take k ++ (range (n+1)).map …`.  **They differ only in the take index, the block width
and the constant block** — 0/`[[0,0],[1,1]]`, 1/`[[1,1]]`, 1/`[[1,1],[2,0]]`, 2/`[[2,0]]` for the
four rows respectively.

**FOUR OF THE FIVE VEBLEN ROWS ARE THIS SHAPE AND `ε_{ε₀}` IS NOT.**  Its expansions are
`(0,0)(1,1) ++ (2,0),(3,0),(4,0),…` — **the block GROWS with the index instead of repeating**, so a
lemma over a CONSTANT block cannot express it.  That is the same structure that made `ε_{ε₀}` the
first row needing an induction on `n` in `Evidence/SqV.lean` §21, now visible on the MATRIX side:
the term side and the matrix side agree about which row is different.

**Both statements were `#guard`ed against the encoder before being proved** (in `SqV.lean`, where
`sqv'` lives — this file cannot cite it, so the check lives there and the record lives here): the
identity held at `n < 5` on both rows.  A wrong matrix in a `rfl`-shaped computational identity
builds green, so the check is not optional. -/

theorem expand_epsOmegaSq (n : Nat) :
    BMS.expand? [[0, 0], [1, 1], [2, 0], [2, 0]] n
      = some ([[0, 0]] ++ (List.replicate (n + 1) ([[1, 1], [2, 0]] : Matrix)).flatten) := by
  have hblk : ∀ (a : Nat), ((List.range 2).map (fun x =>
      (List.range 2).map (fun y =>
        BMS.ent [[0, 0], [1, 1], [2, 0], [2, 0]] (1 + x) y +
          a * BMS.delta [[0, 0], [1, 1], [2, 0], [2, 0]] 1 0 y *
            (if BMS.ascends [[0, 0], [1, 1], [2, 0], [2, 0]] 1 (1 + x) y then 1 else 0))))
      = ([[1, 1], [2, 0]] : Matrix) := by
    intro a; rfl
  show some (([[0, 0], [1, 1], [2, 0], [2, 0]] : Matrix).take 1 ++
      ((List.range (n + 1)).map (fun a =>
        (List.range 2).map (fun x =>
          (List.range 2).map (fun y =>
            BMS.ent [[0, 0], [1, 1], [2, 0], [2, 0]] (1 + x) y +
              a * BMS.delta [[0, 0], [1, 1], [2, 0], [2, 0]] 1 0 y *
                (if BMS.ascends [[0, 0], [1, 1], [2, 0], [2, 0]] 1 (1 + x) y then 1 else 0))))).flatten)
    = _
  rw [List.map_congr_left (l := List.range (n + 1))
      (g := fun _ => ([[1, 1], [2, 0]] : Matrix)) (fun a _ => hblk a),
    map_const_flatten]
  rfl

theorem expand_epsOmegaOmega (n : Nat) :
    BMS.expand? [[0, 0], [1, 1], [2, 0], [3, 0]] n
      = some ([[0, 0], [1, 1]] ++ (List.replicate (n + 1) ([[2, 0]] : Matrix)).flatten) := by
  have hblk : ∀ (a : Nat), ((List.range 1).map (fun x =>
      (List.range 2).map (fun y =>
        BMS.ent [[0, 0], [1, 1], [2, 0], [3, 0]] (2 + x) y +
          a * BMS.delta [[0, 0], [1, 1], [2, 0], [3, 0]] 2 0 y *
            (if BMS.ascends [[0, 0], [1, 1], [2, 0], [3, 0]] 2 (2 + x) y then 1 else 0))))
      = ([[2, 0]] : Matrix) := by
    intro a; rfl
  show some (([[0, 0], [1, 1], [2, 0], [3, 0]] : Matrix).take 2 ++
      ((List.range (n + 1)).map (fun a =>
        (List.range 1).map (fun x =>
          (List.range 2).map (fun y =>
            BMS.ent [[0, 0], [1, 1], [2, 0], [3, 0]] (2 + x) y +
              a * BMS.delta [[0, 0], [1, 1], [2, 0], [3, 0]] 2 0 y *
                (if BMS.ascends [[0, 0], [1, 1], [2, 0], [3, 0]] 2 (2 + x) y then 1 else 0))))).flatten)
    = _
  rw [List.map_congr_left (l := List.range (n + 1))
      (g := fun _ => ([[2, 0]] : Matrix)) (fun a _ => hblk a),
    map_const_flatten]
  rfl

#guard (List.range 6).all (fun n =>
  BMS.expand [[0, 0], [1, 1], [2, 0], [2, 0]] n
    == [[0, 0]] ++ (List.replicate (n + 1) ([[1, 1], [2, 0]] : Matrix)).flatten)
#guard (List.range 6).all (fun n =>
  BMS.expand [[0, 0], [1, 1], [2, 0], [3, 0]] n
    == [[0, 0], [1, 1]] ++ (List.replicate (n + 1) ([[2, 0]] : Matrix)).flatten)

/-! ### §20.2 `ε_{ε₀}`'s EXPANSION IDENTITY — THE ROW WHOSE BLOCK GROWS

The other four Veblen rows are `take k ++ (n+1) copies of a CONSTANT block`.  This one is not, and
the structural reason is ONE NUMBER: `expand?` sets `t := lnz (M.getLast?)`, and `delta M r t y` is
`if y < t then … else 0`.

    row              last row   lnz   delta      block
    ω^(ε₀+1)         [1,0]       0    ≡ 0        constant
    ε_ω              [2,0]       0    ≡ 0        constant
    ε_{ω²}           [2,0]       0    ≡ 0        constant
    ε_{ω^ω}          [3,0]       0    ≡ 0        constant
    ε_{ε₀}           [3,1]       1    ≠ 0        GROWS

**`t = 0` ⟺ constant block, exactly.**  "The block grows" and "the last row's last nonzero column
is not 0" are ONE fact, not two.  So the constant-block route — `hblk : ∀ a, … = <const>` then
`map_congr_left` + `map_const_flatten` — cannot be reused, and `flatten_map_singleton` is the lemma
for singleton blocks instead.

**THE ERROR THAT COST A SESSION WAS `delta`'s THIRD ARGUMENT, NOT THE ROOT OR THE HEIGHT.**  Root 2
and height 1 were inferred correctly from the neighbours; `delta … 2 0 y` was copied from them and
should be `delta … 2 1 y`.  **The four neighbours all happen to have `t = 0`, so the copied `0` was
invisible** — and it is invisible precisely because `t = 0` is what makes their blocks constant.
The one parameter that differs is the one that explains why they differ.

**AND THE TWO SIDES AGREE ABOUT WHICH ROW IS DIFFERENT, EACH FOR ITS OWN REASON.**

    matrix side   (List.range (n+1)).map (fun a => [2 + a, 0])
    term side     `ladderCols 2 (n+1)` = (List.range (n+1)).map (fun i => (i + 2, 0))

the same expression up to `Col2` versus `List Nat`.  `Evidence/SqV.lean` §21 found this row odd
because the BLOCK's own encoding grows with `n`; the matrix side finds it odd because `lnz` of its
last row is nonzero.  **Compare `SqV.lean` §23, where "it is a tower" is true of the ordinals and
FALSE of the matrices.**  The correspondence sometimes transfers a shape and sometimes does not,
and one example of each is the minimum honest presentation.

`2 + a`, not `a + 2`: the entry is `ent M 2 0 + a * delta M 2 1 0 * 1` with `ent M 2 0 = 2`, so the
`a` lands on the right and `rfl` cares. -/

theorem expand_epsEps0 (n : Nat) :
    BMS.expand? [[0, 0], [1, 1], [2, 0], [3, 1]] n
      = some ([[0, 0], [1, 1]] ++ ((List.range (n + 1)).map (fun a => [2 + a, 0]))) := by
  have hblk : ∀ (a : Nat), ((List.range 1).map (fun x =>
      (List.range 2).map (fun y =>
        BMS.ent [[0, 0], [1, 1], [2, 0], [3, 1]] (2 + x) y +
          a * BMS.delta [[0, 0], [1, 1], [2, 0], [3, 1]] 2 1 y *
            (if BMS.ascends [[0, 0], [1, 1], [2, 0], [3, 1]] 2 (2 + x) y then 1 else 0))))
      = ([[2 + a, 0]] : Matrix) := by
    -- CHOICE-FREE ON PURPOSE.  `simp [BMS.ent, BMS.delta, BMS.ascends, …]` closes this too and
    -- costs one `Classical.choice` in the whole theorem; `rfl`, an explicit `show` of the reduced
    -- block and a fully-listed `simp only` all fail.  What works is to `change` to the two
    -- entries written out, rewrite each atom by a `show … from rfl`, and leave `simp only` nothing
    -- but arithmetic.  Do not "simplify" this back — the axiom set is the reason it is long.
    intro a
    change [[
      BMS.ent [[0, 0], [1, 1], [2, 0], [3, 1]] 2 0 +
        a * BMS.delta [[0, 0], [1, 1], [2, 0], [3, 1]] 2 1 0 *
          (if BMS.ascends [[0, 0], [1, 1], [2, 0], [3, 1]] 2 2 0 then 1 else 0),
      BMS.ent [[0, 0], [1, 1], [2, 0], [3, 1]] 2 1 +
        a * BMS.delta [[0, 0], [1, 1], [2, 0], [3, 1]] 2 1 1 *
          (if BMS.ascends [[0, 0], [1, 1], [2, 0], [3, 1]] 2 2 1 then 1 else 0)
    ]] = [[2 + a, 0]]
    rw [show BMS.ent [[0, 0], [1, 1], [2, 0], [3, 1]] 2 0 = 2 from rfl,
      show BMS.delta [[0, 0], [1, 1], [2, 0], [3, 1]] 2 1 0 = 1 from rfl,
      show BMS.ascends [[0, 0], [1, 1], [2, 0], [3, 1]] 2 2 0 = true from rfl,
      show BMS.ent [[0, 0], [1, 1], [2, 0], [3, 1]] 2 1 = 0 from rfl,
      show BMS.delta [[0, 0], [1, 1], [2, 0], [3, 1]] 2 1 1 = 0 from rfl]
    simp only [if_true, Nat.mul_one, Nat.mul_zero, Nat.zero_mul, Nat.zero_add]
  have hflat (l : List Nat) :
      ((l.map (fun a => ([[2 + a, 0]] : Matrix))).flatten) = l.map (fun a => [2 + a, 0]) := by
    induction l with
    | nil => rfl
    | cons a t ih =>
        show [([2 + a, 0] : List Nat)] ++ ((t.map (fun x => ([[2 + x, 0]] : Matrix))).flatten) =
          [2 + a, 0] :: t.map (fun x => [2 + x, 0])
        rw [ih]; rfl
  show some (([[0, 0], [1, 1], [2, 0], [3, 1]] : Matrix).take 2 ++
      ((List.range (n + 1)).map (fun a =>
        (List.range 1).map (fun x =>
          (List.range 2).map (fun y =>
            BMS.ent [[0, 0], [1, 1], [2, 0], [3, 1]] (2 + x) y +
              a * BMS.delta [[0, 0], [1, 1], [2, 0], [3, 1]] 2 1 y *
                (if BMS.ascends [[0, 0], [1, 1], [2, 0], [3, 1]] 2 (2 + x) y then 1 else 0))))).flatten)
    = _
  rw [List.map_congr_left (l := List.range (n + 1))
      (g := fun a => ([[2 + a, 0]] : Matrix)) (fun a _ => hblk a), hflat]
  rfl

#guard (List.range 6).all (fun n =>
  BMS.expand [[0, 0], [1, 1], [2, 0], [3, 1]] n
    == [[0, 0], [1, 1]] ++ ((List.range (n + 1)).map (fun a => [2 + a, 0])))
-- `t = 0` iff the block is constant: the four constant rows and the one that grows
#guard (BMS.lnz [1, 0] == some 0) && (BMS.lnz [2, 0] == some 0) && (BMS.lnz [3, 0] == some 0)
#guard BMS.lnz [3, 1] == some 1

/-! ## §21 THE RUNG FAMILY — `expand?` FOR EVERY `epsM (k+1)`, NOT ONE ROW AT A TIME

§20 records that the ε_ω row's expansions are the ladder's own rungs, but that **each RUNG's
expansions leave the ladder** for a tower family one level down, and that is why
`Certified (epsM n) (fsEW n)` does NOT reduce to `Certified (epsM (n-1)) …`.  `Evidence/SqV.lean`
§23 names `cert_epsN` as the one obligation `cert_epsOmega` still carries, and the certificate
lane's scout found the rungs' expansions are a **two-column-per-step family** that is neither
`towerM` (one column per step) nor `famM` (alternating) — so no existing certificate family
reaches it.

**THIS SECTION SUPPLIES THE EXPANSION HALF OF THAT FAMILY, FOR ALL `k` AND ALL `n`.**  Measured
first, as always:

    expand (epsM 1) n : [[0,0],[1,1]] · +[1,0],[2,1] · +[2,0],[3,1] · …
    expand (epsM 2) n : [[0,0],[1,1],[1,1]] · +[1,0],[2,1],[2,1] · …
    expand (epsM 3) n : [[0,0],[1,1],[1,1],[1,1]] · +[1,0],[2,1],[2,1],[2,1] · …

so block `j` is one row `[j+1,0]` then `k+1` copies of `[j+2,1]`.  The `#guard` below checks the
family against `BMS.expand` at 20 points before anything is proved about it — a `rfl`-shaped
computational identity is exactly where a wrong matrix builds green.

**`t = lnz [1,1] = 1` HERE, NOT 0.**  §20.2's `t = 0 ⟺ constant block` is why the five
single-row identities could use a constant-block template and this one cannot: `delta` is not
identically zero, so the blocks grow, and `hblk` needs an induction rather than a `change` to a
literal.

Choice-free on purpose, like `expand_epsEps0`: `simp [BMS.ent, BMS.delta, BMS.ascends, …]` would
close several of these steps and cost a `Classical.choice` each time.

**WHAT THIS DOES NOT GIVE.**  It is the EXPANSION half only.  `cert_epsN` also needs the order
clauses and `kind`, and then the certificates of the rungs' own expansions — which is the tower
family one level down that §20 warns about.  This removes one obstruction from that section; it
does not close it.
-/

def rungBlock (k j : Nat) : BMS.Matrix :=
  [j + 1, 0] :: List.replicate (k + 1) [j + 2, 1]

def rungM (k n : Nat) : BMS.Matrix :=
  Evidence.Cert.epsM k ++ ((List.range n).map (rungBlock k)).flatten

#guard (List.range 4).all (fun k => (List.range 5).all (fun n =>
  BMS.expand (Evidence.Cert.epsM (k + 1)) n == rungM k n))

private theorem flatten_replicate_singleton (k : Nat) (c : BMS.Col) :
    (List.replicate k [c]).flatten = List.replicate k c := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, List.flatten_cons, ih]
      rw [show k + 1 = Nat.succ k from by omega, List.replicate_succ]
      rfl

private theorem epsM_eq_replicate (k : Nat) :
    Evidence.Cert.epsM k = [([0, 0] : BMS.Col)] ++ List.replicate (k + 1) [1, 1] := by
  unfold Evidence.Cert.epsM
  rw [flatten_replicate_singleton]
  rfl

private def epsRep (q : Nat) : BMS.Matrix :=
  ([0, 0] : BMS.Col) :: List.replicate q [1, 1]

private theorem epsM_eq_epsRep (k : Nat) :
    Evidence.Cert.epsM k = epsRep (k + 1) := epsM_eq_replicate k

private theorem length_epsRep (q : Nat) : (epsRep q).length = q + 1 := by
  unfold epsRep
  rw [List.length_cons, List.length_replicate]

private theorem ent_epsRep_succ (q i y : Nat) (hi : i < q) :
    BMS.ent (epsRep q) (i + 1) y = ([1, 1] : BMS.Col).getD y 0 := by
  have hget : (List.replicate q ([1, 1] : BMS.Col)).getD i [] = [1, 1] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt hi]
    rfl
  unfold epsRep BMS.ent
  rw [List.getD_cons_succ, hget]

private theorem filter_epsRep_lt_one (q i : Nat) (hi : i < q) :
    (List.range (i + 1)).filter
      (fun p => decide (BMS.ent (epsRep q) p 0 < 1)) = [0] := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [List.range_succ, List.filter_append, ih (by omega)]
      rw [List.filter_cons]
      rw [show BMS.ent (epsRep q) (i + 1) 0 = 1 from
        ent_epsRep_succ q i 0 (by omega)]
      rfl

private theorem parent_epsRep_zero (q i : Nat) (hi : i < q) :
    BMS.parent (epsRep q) 0 (i + 1) = some 0 := by
  show ((List.range (i + 1)).filter (fun p =>
    decide (BMS.ent (epsRep q) p 0 < BMS.ent (epsRep q) (i + 1) 0))).max? = some 0
  rw [show BMS.ent (epsRep q) (i + 1) 0 = 1 from ent_epsRep_succ q i 0 hi,
    filter_epsRep_lt_one q i hi]
  rfl

private theorem parent_epsRep_one (k : Nat) :
    BMS.parent (epsRep (k + 2)) 1 (k + 2) = some 0 := by
  have hp : BMS.parent (epsRep (k + 2)) 0 (k + 2) = some 0 := by
    rw [show k + 2 = (k + 1) + 1 from by omega]
    exact parent_epsRep_zero (k + 2) (k + 1) (by omega)
  have hp0 : BMS.parent (epsRep (k + 2)) 0 0 = none := rfl
  show ((BMS.iterParent (BMS.parent (epsRep (k + 2)) 0) (k + 2) (k + 2)).filter
    (fun p => decide (BMS.ent (epsRep (k + 2)) p 1 <
      BMS.ent (epsRep (k + 2)) (k + 2) 1))).max? = some 0
  rw [show BMS.iterParent (BMS.parent (epsRep (k + 2)) 0) (k + 2) (k + 2) =
      0 :: BMS.iterParent (BMS.parent (epsRep (k + 2)) 0) (k + 1) 0 from
        Evidence.Cert.iterParent_cons hp,
    Evidence.Cert.iterParent_nil hp0,
    List.filter_cons,
    show BMS.ent (epsRep (k + 2)) 0 1 = 0 from rfl,
    show BMS.ent (epsRep (k + 2)) (k + 2) 1 = 1 from by
      rw [show k + 2 = (k + 1) + 1 from by omega]
      exact ent_epsRep_succ (k + 2) (k + 1) 1 (by omega)]
  rfl

private theorem getLast_epsRep (q : Nat) :
    (epsRep (q + 1)).getLast? = some [1, 1] := by
  unfold epsRep
  rw [List.replicate_succ']
  change (([0, 0] :: List.replicate q [1, 1]) ++ [[1, 1]]).getLast? = some [1, 1]
  exact List.getLast?_concat

private theorem delta_epsRep_zero (k : Nat) :
    BMS.delta (epsRep (k + 2)) 0 1 0 = 1 := by
  show (if 0 < 1 then
      BMS.ent (epsRep (k + 2)) ((epsRep (k + 2)).length - 1) 0 -
        BMS.ent (epsRep (k + 2)) 0 0 else 0) = 1
  rw [if_pos (by omega),
    show (epsRep (k + 2)).length - 1 = k + 2 from by rw [length_epsRep]; omega,
    show k + 2 = (k + 1) + 1 from by omega,
    ent_epsRep_succ (k + 2) (k + 1) 0 (by omega)]
  rfl

private theorem ascends_epsRep_zero (q j : Nat) (hj : j < q) :
    BMS.ascends (epsRep q) 0 j 0 = true := by
  cases j with
  | zero => rfl
  | succ i =>
      have hp : BMS.parent (epsRep q) 0 (i + 1) = some 0 :=
        parent_epsRep_zero q i (by omega)
      show ((i + 1 == 0) ||
        (BMS.iterParent (BMS.parent (epsRep q) 0) (i + 1) (i + 1)).contains 0) = true
      rw [show BMS.iterParent (BMS.parent (epsRep q) 0) (i + 1) (i + 1) =
        0 :: BMS.iterParent (BMS.parent (epsRep q) 0) i 0 from
          Evidence.Cert.iterParent_cons hp]
      rfl

private def rawRungBlock (k a : Nat) : BMS.Matrix :=
  (List.range (k + 2)).map (fun x =>
    (List.range 2).map (fun y =>
      BMS.ent (epsRep (k + 2)) (0 + x) y +
        a * BMS.delta (epsRep (k + 2)) 0 1 y *
          (if BMS.ascends (epsRep (k + 2)) 0 (0 + x) y then 1 else 0)))

private theorem rawRungBlock_eq (k a : Nat) :
    rawRungBlock k a =
      ([a, 0] : BMS.Col) :: List.replicate (k + 1) [a + 1, 1] := by
  have hrow0 : (List.range 2).map (fun y =>
      BMS.ent (epsRep (k + 2)) (0 + 0) y +
        a * BMS.delta (epsRep (k + 2)) 0 1 y *
          (if BMS.ascends (epsRep (k + 2)) 0 (0 + 0) y then 1 else 0)) =
      ([a, 0] : BMS.Col) := by
    change [
      BMS.ent (epsRep (k + 2)) 0 0 +
        a * BMS.delta (epsRep (k + 2)) 0 1 0 *
          (if BMS.ascends (epsRep (k + 2)) 0 0 0 then 1 else 0),
      BMS.ent (epsRep (k + 2)) 0 1 +
        a * BMS.delta (epsRep (k + 2)) 0 1 1 *
          (if BMS.ascends (epsRep (k + 2)) 0 0 1 then 1 else 0)] = [a, 0]
    rw [show BMS.ent (epsRep (k + 2)) 0 0 = 0 from rfl,
      delta_epsRep_zero k,
      show BMS.ascends (epsRep (k + 2)) 0 0 0 = true from rfl,
      show BMS.ent (epsRep (k + 2)) 0 1 = 0 from rfl,
      show BMS.delta (epsRep (k + 2)) 0 1 1 = 0 from rfl]
    simp only [if_true, Nat.mul_one, Nat.mul_zero, Nat.zero_mul, Nat.zero_add]
  have hrowSucc : ∀ i, i < k + 1 → (List.range 2).map (fun y =>
      BMS.ent (epsRep (k + 2)) (0 + (i + 1)) y +
        a * BMS.delta (epsRep (k + 2)) 0 1 y *
          (if BMS.ascends (epsRep (k + 2)) 0 (0 + (i + 1)) y then 1 else 0)) =
      ([a + 1, 1] : BMS.Col) := by
    intro i hi
    rw [Nat.zero_add]
    change [
      BMS.ent (epsRep (k + 2)) (i + 1) 0 +
        a * BMS.delta (epsRep (k + 2)) 0 1 0 *
          (if BMS.ascends (epsRep (k + 2)) 0 (i + 1) 0 then 1 else 0),
      BMS.ent (epsRep (k + 2)) (i + 1) 1 +
        a * BMS.delta (epsRep (k + 2)) 0 1 1 *
          (if BMS.ascends (epsRep (k + 2)) 0 (i + 1) 1 then 1 else 0)] = [a + 1, 1]
    rw [show BMS.ent (epsRep (k + 2)) (i + 1) 0 = 1 from
        ent_epsRep_succ (k + 2) i 0 (by omega),
      delta_epsRep_zero k,
      show BMS.ascends (epsRep (k + 2)) 0 (i + 1) 0 = true from
        ascends_epsRep_zero (k + 2) (i + 1) (by omega),
      show BMS.ent (epsRep (k + 2)) (i + 1) 1 = 1 from
        ent_epsRep_succ (k + 2) i 1 (by omega),
      show BMS.delta (epsRep (k + 2)) 0 1 1 = 0 from rfl]
    simp only [if_true, Nat.mul_one, Nat.mul_zero, Nat.zero_mul, Nat.add_comm]
  unfold rawRungBlock
  rw [show List.range (k + 2) = 0 :: (List.range (k + 1)).map Nat.succ from
      List.range_succ_eq_map,
    List.map_cons, hrow0, List.map_map]
  rw [List.map_congr_left (l := List.range (k + 1))
    (g := fun _ => ([a + 1, 1] : BMS.Col)) (fun i hi => by
      exact hrowSucc i (by simpa using List.mem_range.mp hi)),
    List.map_const', List.length_range]

private theorem expand_epsRep (k n : Nat) :
    BMS.expand? (epsRep (k + 2)) n =
      some (((List.range (n + 1)).map (rawRungBlock k)).flatten) := by
  simp only [BMS.expand?, getLast_epsRep (k + 1), Option.bind_eq_bind,
    Option.bind_some, show BMS.lnz ([1, 1] : BMS.Col) = some 1 from rfl,
    length_epsRep, Nat.add_sub_cancel, parent_epsRep_one, Option.pure_def,
    Nat.sub_zero, List.take_zero, List.nil_append]
  rfl

private theorem rawRungBlock_zero (k : Nat) :
    rawRungBlock k 0 = Evidence.Cert.epsM k := by
  rw [rawRungBlock_eq, epsM_eq_epsRep]
  rfl

private theorem rawRungBlock_succ (k j : Nat) :
    rawRungBlock k (j + 1) = rungBlock k j := by
  rw [rawRungBlock_eq]
  rfl

private theorem flatten_rawRungBlocks (k n : Nat) :
    ((List.range (n + 1)).map (rawRungBlock k)).flatten = rungM k n := by
  unfold rungM
  rw [List.range_succ_eq_map, List.map_cons, List.flatten_cons,
    rawRungBlock_zero, List.map_map]
  rw [List.map_congr_left (l := List.range n)
    (f := rawRungBlock k ∘ Nat.succ) (g := rungBlock k)
    (fun j _ => rawRungBlock_succ k j)]

theorem expand_epsM_succ (k n : Nat) :
    BMS.expand? (Evidence.Cert.epsM (k + 1)) n = some (rungM k n) := by
  rw [epsM_eq_epsRep, show (k + 1) + 1 = k + 2 from by omega,
    expand_epsRep, flatten_rawRungBlocks]

theorem rungM_zero (k : Nat) : rungM k 0 = Evidence.Cert.epsM k := by
  unfold rungM
  change Evidence.Cert.epsM k ++ [] = Evidence.Cert.epsM k
  exact List.append_nil _

theorem expand_epsM_succ_total (k n : Nat) :
    BMS.expand (Evidence.Cert.epsM (k + 1)) n = rungM k n := by
  show (BMS.expand? (Evidence.Cert.epsM (k + 1)) n).getD [] = rungM k n
  rw [expand_epsM_succ]
  rfl

/-! ### §21.1 THE ORDINAL SIDE — the closed form is `fsEsucc`, and the blocker is a READER BRIDGE

`table/rung-sequence-2026-08-10.txt` refuted the obvious candidate: `oR` of the rungs' expansions
is NOT `fsC` of the row's term (true only at `n = 0`).  Measured against the WF lane's own
`fsEsucc` instead, it holds everywhere tested — **eleventh time in this project that the ancestor
already existed**, and §20.2 already named `fsEsucc` as the closed form for `k = 1, 2, 3` without
anyone connecting it to `rungM`.

**WHAT BLOCKS THE THEOREM IS NOT THE ORDINAL MATHEMATICS.**  `oR_rungM` reduces, via
`expand_epsM_succ_total` and `Rows.ProofsB.R3.e3_val`, to

    Trans.oR (BMS.expand R3.m0 n) = Trans.o? (BMS.expand R3.m0 n)

and `Trans/Recal.lean` contains **no symbolic bridge from the recalibrated `oR` to the retracted
`o?`**.  The row lemmas prove the `o?` reading; the certificate side speaks `oR`.  A bridge would
have to be stated only where the two agree — `o?` is wrong at and above `(0,0)(1,1)(2,1)(2,0)` —
so this is a real piece of work and not a rewrite.

**RESOLVED IN §21.8 for k = 0.** `oR_rungM_zero (n) : Trans.oR (rungM 0 n) = some (fsEsucc 0 n)`
is now a theorem for every `n`, so the `#guard` below is no longer the only thing standing at
k = 0.  It stays as the measurement for k = 1, 2, 3, which remain unproved: §21.3–§21.8 build
the ladder for the k = 0 family only, and nothing there is parameterised in `k`.

What made it possible was not a bridge from `oR` to the retracted `o?` — route (a) and route (b)
are still closed exactly as §21.2 says.  It was building the reader's own equational layer from
the bottom (`ofMatrix`, `transPort`, `dict`) and inducting along `runAux`'s recursion rather
than along the way the family is constructed.
-/

#guard (List.range 4).all fun k => (List.range 6).all fun n =>
  Trans.oR (rungM k n) == some (Evidence.WF.fsEsucc k n)

/-! ### §21.2 WHY `oR_rungM` CANNOT BE PROVED TODAY BY EITHER ROUTE — a structural fact about `Trans`

§21.1 leaves `Trans.oR (rungM k n) = some (fsEsucc k n)` measured at 24 points and unproved.
Both available routes were tried and both are closed, for DIFFERENT reasons, and the second one is
a fact about this project rather than about this theorem.

**ROUTE (a), through the row lemmas, is closed because the readers are not related.**  The
`Rows/` facts are proved in `Trans.o?`; unfolding lands on `oR M = o? M`, and `Trans/Recal.lean`
exports no bridge.  Worse, `o?` is RETRACTED: `lean/scripts/reader_agreement.lean` measures 607
matrices and finds **11 that are strictly BELOW the boundary this repo documents and already
disagree** — so a bridge stated at the documented boundary would be false, and any bridge at all
would inherit a known-wrong function into the path the ✅ marks depend on.

**ROUTE (b), directly in `oR`, is closed because `oR` HAS NO EQUATIONAL API AT ALL.**  Counted:

    file                 theorems   #guards
    Trans/Recal.lean            0        24
    Trans/Dict.lean             0        44
    Trans/Pair.lean             0        23
    Trans/StageC.lean           0        83
    Trans/Lemmas.lean           8         0

`oR = (1 + ·) ∘ dict ∘ transPort ∘ ofMatrix` is a pipeline of whole-matrix computations, and
**every `oR` fact in this repository is a `#guard` or a `decide` at a concrete matrix.**  There is
no equation for `oR (M ++ block)`, so there is nothing to induct on — which is exactly what an
`∀ n` statement needs.  The base case `oR (rungM 0 0) = some (fsEsucc 0 0)` is `rfl`; the step has
no lemma to take.

**THIS IS NOT A GAP IN A PROOF, IT IS A MISSING LAYER.**  `oR` is a VALIDATED COMPUTATION — 174
`#guard`s across `Trans/`, a reference-implementation table, negative controls — and validation at points is not an
API.  Anything quantified over `n` on the `oR` side is blocked until `Trans/Recal.lean` grows
equation lemmas, and that is a piece of work whose size is set by `ofMatrix`/`transPort`/`dict`,
not by any ordinal question.

The pieces that DO exist and survive this: `expand_epsM_succ` (all `k`, all `n`), `rungM_zero`,
`rungM_succ`, the `n = 0` reading, and §21.1's measurement.  The ordinal side is settled; the
reader side is where this line stops.
-/

theorem rungM_succ (k n : Nat) :
    rungM k (n + 1) = rungM k n ++ rungBlock k n := by
  simp [rungM, List.range_succ]

theorem oR_rungM_zero_base :
    Trans.oR (rungM 0 0) = some (Evidence.WF.fsEsucc 0 0) := rfl

/-! ## §22 THE BLOCK FAMILY — `expand_rowA` GENERALISED TO AN ARBITRARY BLOCK

`expand_rowA` says `expand? ([[0,0],[1,1]] ++ [[1,0]]) n` is that block repeated
`n+1` times.  Measured (`table/nfok-reach-2026-08-10.txt`), the row `ω^(ζ₀+1)` has
**exactly the same shape one level up**: `[[0,0],[1,1],[2,1]] ++ [[1,0]]`, expanding to
its own 3-row block repeated.  So the theorem generalises over the block.

    expand_blockRow (B) (hB : B ≠ []) (hWF : BMS.WF 2 B)
      (hzero : ent B 0 0 = 0)
      (hpos : ∀ i, 0 < i → i < B.length → 0 < ent B i 0) (n) :
      expand? (B ++ [[1,0]]) n = some (blockM B n)

The three conditions on `B` were **found by measurement, not guessed**: `blockWorks`
(does the identity hold) and `blockShape` (do the conditions hold) agree on all 3615
sample blocks, `#guard`ed below.

**AND THE CONSUMER TEST IS PART OF THE DELIVERABLE.**  `inst_rowA` and `inst_zeta`
discharge the hypotheses at the two concrete blocks this was built for.  They are
here because a hypothesis a caller cannot discharge is a hypothesis that makes the
theorem unusable — this file has published a vacuous theorem once already (WF §15.37)
and the only instrument that detects that is a consumer.  Note the discharges are
written out longhand: this project has NO MATHLIB, so `fin_cases` / `interval_cases`
do not exist and `BMS.WF 2 B` has no `Decidable` instance, so `by decide` does not
apply to it either.
-/

def blockM (B : Matrix) (n : Nat) : Matrix :=
  (List.replicate (n + 1) B).flatten

/-- The bounded expansion identity used for measurement. -/
def blockWorks (B : Matrix) : Bool :=
  (List.range 5).all fun n =>
    BMS.expand? (B ++ [[1, 0]]) n == some (blockM B n)

/-- The structural condition suggested by the measurements. -/
def blockShape : Matrix → Bool
  | [] => false
  | c :: cs =>
      c.length == 2 && c.getD 0 0 == 0 &&
        cs.all (fun d => d.length == 2 && decide (0 < d.getD 0 0))

/-! The two requested controls, checked before the proof. -/

#guard blockWorks [[0, 0], [1, 1]]
#guard (List.range 5).all (fun n =>
  blockM [[0, 0], [1, 1]] n == Evidence.Cert.eps0M n)
#guard blockWorks [[0, 0], [1, 1], [2, 1]]

/-! Search all blocks of length 1--3 whose columns have length 0--3 and entries
    in `{0,1}`.  On all 3,615 blocks, the expansion identity agrees exactly with
    `blockShape`: every column has height two, the first bottom entry is zero,
    and all later bottom entries are positive. -/

def sampleCols : List (List Nat) :=
  [[]] ++
  (List.range 2).map (fun a => [a]) ++
  (List.range 2).flatMap (fun a => (List.range 2).map (fun b => [a, b])) ++
  (List.range 2).flatMap (fun a => (List.range 2).flatMap (fun b =>
    (List.range 2).map (fun c => [a, b, c])))

def sampleBlocks : List Matrix :=
  sampleCols.map (fun a => [a]) ++
  sampleCols.flatMap (fun a => sampleCols.map (fun b => [a, b])) ++
  sampleCols.flatMap (fun a => sampleCols.flatMap (fun b =>
    sampleCols.map (fun c => [a, b, c])))

#guard sampleBlocks.length == 3615
#guard sampleBlocks.all (fun B => blockWorks B == blockShape B)

private theorem range_map_getD_self {α : Type} [Inhabited α] (l : List α) :
    (List.range l.length).map (fun i => l.getD i default) = l := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem hi₂]
    rfl

private theorem rebuild_two_rows (B : Matrix) (hWF : BMS.WF 2 B) :
    (List.range B.length).map (fun x =>
      (List.range 2).map (fun y => BMS.ent B x y)) = B := by
  calc
    (List.range B.length).map (fun x =>
        (List.range 2).map (fun y => BMS.ent B x y))
      = (List.range B.length).map (fun x => B.getD x []) := by
          apply List.map_congr_left
          intro x hx
          have hxl : x < B.length := List.mem_range.mp hx
          have hxget : B.getD x [] = B[x] := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hxl]
            rfl
          have hc : (B.getD x []).length = 2 := by
            rw [hxget]
            exact hWF B[x] (List.getElem_mem hxl)
          show (List.range 2).map (fun y => (B.getD x []).getD y 0) = B.getD x []
          rw [Evidence.StageA.range_map_getD 2 (B.getD x []) (by omega)]
          apply List.take_of_length_le
          omega
    _ = B := range_map_getD_self B

/-- Once the bad root is column zero, a well-formed two-row block is copied
    unchanged because the final column `[1,0]` has `t = 0`. -/
private theorem expand_blockRow_of_parent (B : Matrix) (hWF : BMS.WF 2 B)
    (hpar : BMS.parent (B ++ [[1, 0]]) 0 B.length = some 0) (n : Nat) :
    BMS.expand? (B ++ [[1, 0]]) n = some (blockM B n) := by
  have hblk : ∀ a : Nat,
      (List.range B.length).map (fun x =>
        (List.range 2).map (fun y =>
          BMS.ent (B ++ [[1, 0]]) x y +
            a * BMS.delta (B ++ [[1, 0]]) 0 0 y *
              (if BMS.ascends (B ++ [[1, 0]]) 0 x y then 1 else 0))) = B := by
    intro a
    have hmap : (List.range B.length).map (fun x =>
        (List.range 2).map (fun y =>
          BMS.ent (B ++ [[1, 0]]) x y +
            a * BMS.delta (B ++ [[1, 0]]) 0 0 y *
              (if BMS.ascends (B ++ [[1, 0]]) 0 x y then 1 else 0))) =
        (List.range B.length).map (fun x =>
          (List.range 2).map (fun y => BMS.ent B x y)) := by
      apply List.map_congr_left
      intro x hx
      apply List.map_congr_left
      intro y _
      have hxl : x < B.length := List.mem_range.mp hx
      simp only [BMS.delta, Nat.not_lt_zero, if_false, Nat.mul_zero, Nat.zero_mul,
        Nat.add_zero]
      unfold BMS.ent
      have hget : (B ++ [[1, 0]]).getD x [] = B.getD x [] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hxl]
      rw [hget]
    rw [hmap]
    exact rebuild_two_rows B hWF
  have hlast : (B ++ [[1, 0]]).getLast? = some [1, 0] := by simp
  simp only [BMS.expand?, hlast, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rw [show BMS.lnz [1, 0] = some 0 from rfl]
  simp only
  have hlen : (B ++ [[1, 0]]).length - 1 = B.length := by simp
  rw [hlen, hpar]
  simp only [Option.bind_some, List.take_zero, List.nil_append, Nat.zero_add, Nat.sub_zero,
    List.length_cons, List.length_nil]
  rw [List.map_congr_left (l := List.range (n + 1))
      (g := fun _ => B) (fun a _ => hblk a), Evidence.Cert.map_const_flatten]
  rfl

private theorem ent_append_left_blk (B C : Matrix) (x y : Nat) (hx : x < B.length) :
    BMS.ent (B ++ C) x y = BMS.ent B x y := by
  unfold BMS.ent
  have hget : (B ++ C).getD x [] = B.getD x [] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hx]
  rw [hget]

private theorem parent_blockRow_zero (B : Matrix) (hB : B ≠ [])
    (hzero : BMS.ent B 0 0 = 0)
    (hpos : ∀ i, 0 < i → i < B.length → 0 < BMS.ent B i 0) :
    BMS.parent (B ++ [[1, 0]]) 0 B.length = some 0 := by
  have hlen : 0 < B.length := List.length_pos_iff.mpr hB
  have hlast : BMS.ent (B ++ [[1, 0]]) B.length 0 = 1 := by
    rw [Evidence.Cert.ent_append B [[1, 0]] B.length 0 (Nat.le_refl _)]
    simp [BMS.ent]
  show ((List.range B.length).filter (fun p => decide
    (BMS.ent (B ++ [[1, 0]]) p 0 < BMS.ent (B ++ [[1, 0]]) B.length 0))).max? = some 0
  rw [Evidence.StageA.max?_filter_range]
  apply Evidence.StageA.lastSome_spec _ B.length 0 hlen
  · have hfirst : BMS.ent (B ++ [[1, 0]]) 0 0 = 0 := by
      rw [ent_append_left_blk B [[1, 0]] 0 0 hlen, hzero]
    simp [hfirst, hlast]
  · intro q hq hqB
    have hqent : BMS.ent (B ++ [[1, 0]]) q 0 = BMS.ent B q 0 :=
      ent_append_left_blk B [[1, 0]] q 0 hqB
    have hqpos := hpos q hq hqB
    simp [hqent, hlast]
    omega

/-- A block whose columns have height two and whose row 0 has its unique zero
    at the first column is copied `n + 1` times when `[1,0]` is appended. -/
theorem expand_blockRow (B : Matrix) (hB : B ≠ []) (hWF : BMS.WF 2 B)
    (hzero : BMS.ent B 0 0 = 0)
    (hpos : ∀ i, 0 < i → i < B.length → 0 < BMS.ent B i 0) (n : Nat) :
    BMS.expand? (B ++ [[1, 0]]) n = some (blockM B n) :=
  expand_blockRow_of_parent B hWF (parent_blockRow_zero B hB hzero hpos) n

#print axioms expand_blockRow


-- COORDINATOR CHECK: the two instances this was built for.
theorem inst_rowA (n : Nat) : BMS.expand? ([[0,0],[1,1]] ++ [[1,0]]) n
    = some (blockM [[0,0],[1,1]] n) :=
  expand_blockRow [[0,0],[1,1]] (by simp)
    (by intro c hc; simp at hc; rcases hc with h|h <;> subst h <;> rfl)
    (by rfl)
    (by intro i h1 h2
        match i, h1, h2 with
        | 1, _, _ => decide) n
theorem inst_zeta (n : Nat) : BMS.expand? ([[0,0],[1,1],[2,1]] ++ [[1,0]]) n
    = some (blockM [[0,0],[1,1],[2,1]] n) :=
  expand_blockRow [[0,0],[1,1],[2,1]] (by simp)
    (by intro c hc; simp at hc; rcases hc with h|h|h <;> subst h <;> rfl)
    (by rfl)
    (by intro i h1 h2
        match i, h1, h2 with
        | 1, _, _ => decide
        | 2, _, _ => decide) n
#print axioms inst_rowA
#print axioms inst_zeta

/-! ### §21.3 A THIRD ROUTE TO `oR_rungM`: build the reader chain link by link

§21.2 closed both routes that go *around* the reader.  This section takes the reader apart
instead.  `Trans.oR` is a composition of three stages, so for `k = 0` the target factors into
four links:

    rungM 0 n  --ofMatrix-->  rungPS n  --transPort-->  rungBT n  --dict-->  fsEsucc 0 n

Each link is a statement about an *open* `n`, which is exactly what `#guard` cannot give and
what §21.1's 24-point measurement was standing in for.

**LINK 1 IS NOW A THEOREM** (`ofMatrix_rungM_zero`).  It goes through `Trans.Recal.ofMatrix_append`
and `rungM_succ` by induction — the append lemma was proved precisely so that a family defined by
appending blocks could be read symbolically, and this is its first consumer.

**LINKS 2 AND 3 ARE STILL MEASUREMENTS, AND BOTH WERE ATTEMPTED.**  The `#guard`s below record
them.  The equational layers they need now exist (`Trans.Recal.transPort_eq_runAux`, and
`Trans.Dict.dict_zero` / `dict_D` / `dict_sum`), so the obstacle is no longer the absence of
anything to rewrite with — but neither link is a tactic away, and it is worth writing down why so
the next attempt does not rediscover it.

**LINK 2: THE APPEND ROUTE IS CLOSED, BUT LINK 2 ITSELF IS NOT.**  This paragraph said "link 2
is closed" for one commit; that was too strong, and the correction is the useful part.  What is
closed is the route through `++`.  `runAux`'s OWN recursion descends by
`predP M = if M.length == 1 then M else M.dropLast` — one pair at a time, off the END — and an
induction along THAT is a different proof with no append lemma in it.  Measured:

    predP (rungPS (n+1))  =  rungPS n ++ [(n+1, 0)]
    rungPS (n+1)          =  rungPS n ++ [(n+1, 0), (n+2, 1)]

So `rungPS` steps by TWO pairs while the recursion steps by ONE: the family is simply too coarse
to sit on the recursion, and the repair is a one-pair-at-a-time ladder `L` with `rungPS n = L (2n+1)`
and `predP (L (m+1)) = L m`.  Then the induction hypothesis is literally the recursive call's
argument, and the memo table threads the way the recursion already threads it instead of having to
be quantified over.  NOT YET ATTEMPTED.

The rest of this paragraph is why the append route specifically is dead, and it stays true:
`runAux` DOES NOT DECOMPOSE OVER `++`.
The obvious plan was an append lemma for `runAux` carrying an arbitrary incoming state, plus fuel
monotonicity.  The fuel half is now proved (`Trans.Recal.transFuel_append` /`maxE_append`:
`transFuel (p ++ q) = 40 + 6*(|p| + |q| + max (maxE p) (maxE q))`).  The append half cannot be
written, for two structural reasons:

  - every structural test in `runAux` — `fpar`, `adm`, `predP` — is made on the WHOLE list, so a
    run on `p ++ q` never contains a run on `p`;
  - the recursion threads a MEMO TABLE, so each call's result depends on what the preceding calls
    put there.  "Arbitrary incoming state" is therefore not a parameter one can quantify over
    innocently — the state is the memo table, and it is exactly what carries the dependence.

An "append" statement CAN be written and proved by `rfl`, but only by keeping `let M := p ++ q`
inside the right-hand side; it names the body rather than decomposing it, and is worth nothing to
the induction.  That was measured, not assumed.  So link 2 is not a harder version of link 1 — the
lemma the route needs does not exist, and a fourth attempt should not be commissioned.

**LINK 3 — `collapse` is a normaliser, not a constructor.**  `Trans.Dict.collapse` runs `wcnf`,
folds, and then `omegaNF`, so `dict (rungBT n)` and `fsEsucc 0 n` are NOT definitionally equal at
any index and no amount of `rw` with the three `dict` clauses closes the gap.  Three independent
attempts all ended by unfolding `collapse` into its `wcnf`/`foldl` machinery and dying on `whnf`
heartbeats.  Closing link 3 needs an equational law for `collapse 0 (plus (Z zero) ·)` at the
shapes that occur here — i.e. a theory of the normaliser, which does not exist yet.

Two conjectures were measured and BOTH ARE FALSE; they are recorded so nobody spends time on them:

    collapse 0 (plus (collapse 1 zero) y)  =  phi zero y        -- false
    fsEsucc 0 (n+1)                        =  phi zero (fsEsucc 0 n)   -- false, breaks at n = 0

The second fails because of `fsGen`: `fsEsucc 0 0 = epsN 0` while `fsEsucc 0 (n+1) =
iterPhi zero (add (epsN 0) (epsN 0)) (n+1)`, so the ordinal side steps by `phi zero` only from
n ≥ 1 and the 0 → 1 step changes shape.  An induction stated against `iterPhi` directly avoids
that discontinuity; one stated against `fsEsucc` does not.

Also measured: `collapse 1 zero = Z zero`, and the base case agrees —
`dict (rungBT 0) = fsEsucc 0 0 = phi (phi zero zero) zero`.

Nothing on this route needs the retracted `o?`, which is why it is open at all where (a) and (b)
are closed.  But "open" here means *not refuted*, not *nearly done*.

`rungPS` and `rungBT` are the closed forms of the two intermediate stages — read off the
measurement, in the same way `fsEsucc` was read off the ordinal side in §21.1. -/

/-- The parser stage of the reader, on the `k = 0` rung family. -/
def rungPS : Nat → Trans.Recal.PS
  | 0 => [(0, 0), (1, 1)]
  | n + 1 => rungPS n ++ [(((n + 1 : Nat) : Int), 0), (((n + 2 : Nat) : Int), 1)]

#guard (List.range 8).all fun n =>
  Trans.Recal.ofMatrix (rungM 0 n) == some (rungPS n)

theorem ofMatrix_rungM_zero (n : Nat) :
    Trans.Recal.ofMatrix (rungM 0 n) = some (rungPS n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rungM_succ, Trans.Recal.ofMatrix_append]
    have hM : (rungM 0 n).isEmpty = false := by rfl
    simp [Trans.Recal.ofMatrixAppendRhs, hM, rungBlock, rungPS, ih]
    rfl

#print axioms ofMatrix_rungM_zero

/-- The Buchholz stage of the reader, on the `k = 0` rung family. -/
def rungBT : Nat → Trans.Dict.BT
  | 0 => .D 0 (.D 1 .zero)
  | n + 1 => .D 0 (.sum (.D 1 .zero) (rungBT n))

-- Link 2, unproved: `transPort_rungPS`.
#guard (List.range 8).all fun n =>
  Trans.Recal.transPort ((Trans.Recal.ofMatrix (rungM 0 n)).getD []) == rungBT n

-- Link 3, unproved: `dict_rungBT`.
#guard (List.range 8).all fun n =>
  Trans.Dict.dict (rungBT n) == Evidence.WF.fsEsucc 0 n


/-! ### §21.4 THE LADDER — the reader's structural functions, decided for every index

§21.3's link 2 stalled because `rungPS` steps by TWO pairs while `runAux`'s own recursion
(`predP M = if M.length == 1 then M else M.dropLast`) steps by ONE.  The family was too coarse to
sit on the recursion.  `L` is the one-pair-at-a-time refinement: `rungPS n = L (2*n+1)`, and
`predP (L (m+1)) = L m`, so an induction along `L` IS an induction along the recursion and the
memo table threads the way the recursion already threads it -- which is exactly what the append
route could never have.

What this section gives is the layer under that induction: `gp0`, `gp1`, `fpar`, `isAnc`,
`isPrincipalP`, `isAdm` and `adm` COMPUTED on `L m` for every `m`.  On the append route none of
these could be stated at all.

**STILL OPEN, and named:** `transPort_LBT (m : Nat) : transPort (L m) = LBT m` (measured at 13
points by the `#guard` below).  `transPort_rungPS_of_L` isolates the rest of the chain against it,
so the goal is one lemma away rather than a route away.  The first missing control-flow fact is
`redP (L m) = L m`, which needs a fuel-parametric induction for `red` including the shifted tail
its principal-reduction branch builds.

AXIOMS.  All of these were `Classical.choice`-dirty when first written and are now
`[propext, Quot.sound]`.  The cause was tactics, not mathematics, in TWO shapes: `omega` closing a
NON-arithmetic goal (the recorded pattern -- fixed by `rw [if_neg (by omega), ...]` or
`intro h; exact absurd h (by omega)`, keeping `omega` on arithmetic subgoals), and -- new --
`simp only [beq_self_eq_true, if_true]` on an `if`, fixed by `rw [if_pos (by rfl)]`.  Not one
statement changed.  Do not shorten these back; see plan/constitutions.md 失敗形 2 の七番目.
-/

section Ladder
open Trans.Recal
open Trans.Dict




/-- The prefix of length `m + 1` of the one-pair-at-a-time rung ladder. -/
def L (m : Nat) : Trans.Recal.PS :=
  (List.range (m + 1)).map fun k =>
    ((((k + 1) / 2 : Nat) : Int), ((k % 2 : Nat) : Int))

#guard L 1 == [(0, 0), (1, 1)]
#guard (List.range 12).all fun n => rungPS n == L (2 * n + 1)
#guard (List.range 12).all fun m => predP (L (m + 1)) == L m

theorem L_one : L 1 = [(0, 0), (1, 1)] := rfl

theorem predP_L_zero : predP (L 0) = L 0 := rfl

theorem L_succ (m : Nat) :
    L (m + 1) = L m ++
      [((((m + 2) / 2 : Nat) : Int), (((m + 1) % 2 : Nat) : Int))] := by
  simp [L, List.range_succ, Nat.add_assoc]
  omega

theorem predP_L_succ (m : Nat) : predP (L (m + 1)) = L m := by
  rw [L_succ]
  simp [predP, L]

theorem rungPS_eq_L (n : Nat) : rungPS n = L (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rungPS, ih]
    have hL :
        L (2 * (n + 1) + 1) =
          L (2 * n + 1) ++
            [(((n + 1 : Nat) : Int), 0), (((n + 2 : Nat) : Int), 1)] := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 2) + 1 by omega]
      rw [L_succ (2 * n + 2), L_succ (2 * n + 1)]
      simp only [List.append_assoc, List.singleton_append]
      have hp0 :
          (((((2 * n + 3) / 2 : Nat) : Int), (((2 * n + 2) % 2 : Nat) : Int))) =
            (((n + 1 : Nat) : Int), 0) := by
        have hd : (2 * n + 3) / 2 = n + 1 := by omega
        have hm : (2 * n + 2) % 2 = 0 := by omega
        rw [hd, hm]
        simp
      have hp1 :
          (((((2 * n + 4) / 2 : Nat) : Int), (((2 * n + 3) % 2 : Nat) : Int))) =
            (((n + 2 : Nat) : Int), 1) := by
        have hd : (2 * n + 4) / 2 = n + 2 := by omega
        have hm : (2 * n + 3) % 2 = 1 := by omega
        rw [hd, hm]
        simp
      rw [hp0, hp1]
    exact hL.symm

#guard (List.range 8).all fun n =>
  Trans.Recal.transPort (rungPS n) == rungBT n

private def halfBT : Nat → Trans.Dict.BT
  | 0 => .D 0 .zero
  | n + 1 => .D 0 (.sum (.D 1 .zero) (halfBT n))

/-- Closed form of the reader on every prefix of the ladder. -/
def LBT : Nat → Trans.Dict.BT
  | 0 => .zero
  | m + 1 =>
      if m % 2 = 0 then rungBT (m / 2) else halfBT ((m + 1) / 2)

#guard (List.range 13).all fun m => transPort (L m) == LBT m

theorem LBT_two_mul_add_one (n : Nat) : LBT (2 * n + 1) = rungBT n := by
  simp [LBT]

@[simp] theorem length_L (m : Nat) : (L m).length = m + 1 := by
  simp [L]

theorem gp0_L (m k : Nat) (h : k ≤ m) :
    gp0 (L m) (k : Int) = (((k + 1) / 2 : Nat) : Int) := by
  have hk : k < m + 1 := by omega
  have hk0 : ¬ (k : Int) < 0 := by simp
  simp [gp0, L, hk, hk0]

theorem gp1_L (m k : Nat) (h : k ≤ m) :
    gp1 (L m) (k : Int) = ((k % 2 : Nat) : Int) := by
  have hk : k < m + 1 := by omega
  have hk0 : ¬ (k : Int) < 0 := by simp
  simp [gp1, L, hk, hk0]

theorem fpar_L_odd (m n : Nat) (h : 2 * n + 1 ≤ m) :
    fpar (L m) 0 (2 * n + 1 : Nat) 0 = (2 * n : Nat) := by
  have h0 : 2 * n ≤ m := by omega
  have gt : gp0 (L m) (2 * n + 1 : Nat) = (n + 1 : Nat) := by
    simpa only [show (2 * n + 2) / 2 = n + 1 by omega] using
      gp0_L m (2 * n + 1) h
  have gc : gp0 (L m) (2 * n : Nat) = (n : Nat) := by
    simpa only [show (2 * n + 1) / 2 = n by omega] using
      gp0_L m (2 * n) h0
  unfold fpar
  rw [if_neg]
  · rw [if_pos (by rfl)]
    rw [show (L m).length + 1 = (m + 1) + 1 by simp]
    simp only [fpar0Aux]
    have hj : ((2 * n + 1 : Nat) : Int) - 1 = ((2 * n : Nat) : Int) := by
      omega
    rw [hj, gt, gc]
    simp
    rw [if_neg (by omega), if_pos (by omega)]
  · simp [lenI]
    constructor <;> omega

theorem fpar_L_even (m n : Nat) (h : 2 * n + 2 ≤ m) :
    fpar (L m) 0 (2 * n + 2 : Nat) 0 = (2 * n : Nat) := by
  have h0 : 2 * n ≤ m := by omega
  have h1 : 2 * n + 1 ≤ m := by omega
  have gt : gp0 (L m) (2 * n + 2 : Nat) = (n + 1 : Nat) := by
    simpa only [show (2 * n + 3) / 2 = n + 1 by omega] using
      gp0_L m (2 * n + 2) h
  have gc1 : gp0 (L m) (2 * n + 1 : Nat) = (n + 1 : Nat) := by
    simpa only [show (2 * n + 2) / 2 = n + 1 by omega] using
      gp0_L m (2 * n + 1) h1
  have gc0 : gp0 (L m) (2 * n : Nat) = (n : Nat) := by
    simpa only [show (2 * n + 1) / 2 = n by omega] using
      gp0_L m (2 * n) h0
  unfold fpar
  rw [if_neg]
  · rw [if_pos (by rfl)]
    rw [show (L m).length + 1 = (m + 1) + 1 by simp]
    simp only [fpar0Aux]
    have hj1 : ((2 * n + 2 : Nat) : Int) - 1 = ((2 * n + 1 : Nat) : Int) := by
      omega
    rw [hj1, gt, gc1]
    have hj0 : ((2 * n + 1 : Nat) : Int) - 1 = ((2 * n : Nat) : Int) := by
      omega
    rw [hj0, gc0]
    simp
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  · simp [lenI]
    constructor <;> omega

private def parN (k : Nat) : Nat :=
  if k % 2 = 1 then k - 1 else k - 2

theorem fpar_L_pos (m k : Nat) (hk0 : 0 < k) (hk : k ≤ m) :
    fpar (L m) 0 (k : Int) 0 = (parN k : Nat) := by
  unfold parN
  split
  · rename_i hodd
    have heq : k = 2 * (k / 2) + 1 := by omega
    rw [heq] at hk ⊢
    simpa using fpar_L_odd m (k / 2) hk
  · rename_i hnodd
    have heven : k % 2 = 0 := by omega
    have heq : k = 2 * ((k - 2) / 2) + 2 := by omega
    rw [heq] at hk ⊢
    simpa using fpar_L_even m ((k - 2) / 2) hk

theorem parN_lt (k : Nat) (h : 0 < k) : parN k < k := by
  unfold parN
  split <;> omega

theorem isAncAux_L (k : Nat) : ∀ (m f : Nat),
    k ≤ m → k < f → isAncAux f (L m) 0 (k : Int) 0 = true := by
  refine Nat.strongRecOn (motive := fun k => ∀ (m f : Nat),
    k ≤ m → k < f → isAncAux f (L m) 0 (k : Int) 0 = true) k ?_
  intro k ih m f hkm hkf
  cases f with
  | zero => exact (Nat.not_lt_zero k hkf).elim
  | succ f =>
    unfold isAncAux
    by_cases hk0 : k = 0
    · subst k
      rw [if_pos (by rfl)]
    · have hkpos : 0 < k := by omega
      have hp := fpar_L_pos m k hkpos hkm
      have h0k : (0 : Int) ≠ (k : Int) := by omega
      rw [show ((0 : Int) == (k : Int)) = false by simp [h0k]]
      rw [hp]
      have hpn : ((parN k : Nat) : Int) ≠ -1 := by omega
      simp [hpn]
      have hpk : parN k < k := parN_lt k hkpos
      apply ih (parN k)
      · exact hpk
      · exact Nat.le_trans (Nat.le_of_lt hpk) hkm
      · omega

theorem isAnc_L (m k : Nat) (hk : k ≤ m) :
    isAnc (L m) 0 (k : Int) 0 = true := by
  unfold isAnc
  rw [if_neg]
  · have h := isAncAux_L k m (m + 2) hk (by omega)
    simpa using h
  · simp [lenI]

theorem isPrincipalP_L_succ (m : Nat) : isPrincipalP (L (m + 1)) = true := by
  have ha := isAnc_L (m + 1) (m + 1) (by omega)
  have ha' : isAnc (L (m + 1)) 0 ((m : Int) + 1) 0 = true := by
    simpa using ha
  unfold isPrincipalP isZeroP
  simp [lenI, ha']

theorem fpar1_L_even_prev (m n : Nat) (h : 2 * n + 2 ≤ m) :
    fpar (L m) 1 (2 * n + 2 : Nat) (2 * n + 1 : Nat) = -1 := by
  have h1 : 2 * n + 1 ≤ m := by omega
  have gt : gp0 (L m) (2 * n + 2 : Nat) = (n + 1 : Nat) := by
    simpa only [show (2 * n + 3) / 2 = n + 1 by omega] using
      gp0_L m (2 * n + 2) h
  have gc1 : gp0 (L m) (2 * n + 1 : Nat) = (n + 1 : Nat) := by
    simpa only [show (2 * n + 2) / 2 = n + 1 by omega] using
      gp0_L m (2 * n + 1) h1
  have hrow0 :
      fpar0 (L m) (2 * n + 2 : Nat) (2 * n + 1 : Nat) = -1 := by
    unfold fpar0
    rw [if_neg]
    · rw [show (L m).length + 1 = (m + 1) + 1 by simp]
      simp only [fpar0Aux]
      have hj1 : ((2 * n + 2 : Nat) : Int) - 1 = ((2 * n + 1 : Nat) : Int) := by
        omega
      rw [hj1, gt, gc1]
      have hj0 : ((2 * n + 1 : Nat) : Int) - 1 = ((2 * n : Nat) : Int) := by
        omega
      rw [hj0]
      simp
      intro hbad
      exact absurd hbad (by omega)
    · simp [lenI]
      constructor <;> omega
  unfold fpar
  rw [if_neg]
  · simp only [OfNat.ofNat]
    rw [show (L m).length + 1 = (m + 1) + 1 by simp]
    simp only [fpar1Aux]
    rw [hrow0]
    simp
    intro hbad
    exact absurd hbad (by omega)
  · simp [lenI]
    constructor <;> omega

theorem isAdm_L_even (m n : Nat) (h : 2 * n ≤ m) :
    isAdm (L m) (2 * n : Nat) = true := by
  cases n with
  | zero =>
    have hlen_eq : lenI (L m) = (m + 1 : Nat) := by simp [lenI]
    have hlen : 0 ≤ lenI (L m) := by rw [hlen_eq]; omega
    simp [isAdm, isUnadmitted, isParentP, hlen]
  | succ n =>
    have hp := fpar1_L_even_prev m n (by omega)
    have hparent :
        isParentP (L m) 1 (2 * n + 2 : Nat) (2 * n + 1 : Nat) = false := by
      unfold isParentP
      rw [hp]
      simp [lenI]
      omega
    unfold isAdm isUnadmitted
    rw [show (2 * (n + 1) : Nat) = 2 * n + 2 by omega]
    have hprev : ((2 * n + 2 : Nat) : Int) - 1 = ((2 * n + 1 : Nat) : Int) := by
      omega
    rw [hprev, hparent]
    simp [lenI]
    omega

theorem adm_L_even (m n : Nat) (h : 2 * n ≤ m) :
    adm (L m) (2 * n : Nat) = (2 * n : Nat) := by
  have ha := isAdm_L_even m n h
  unfold adm
  rw [show (L m).length + 2 = (m + 1) + 2 by simp]
  simp only [admAux]
  rw [if_neg (by omega)]
  rw [show isAdm (L m) (2 * n : Nat) = true from ha]
  rfl

/- Step 2 remains open at exactly:

    theorem transPort_LBT (m : Nat) : transPort (L m) = LBT m

The first missing control-flow lemma is `redP (L m) = L m`.  Proving it
requires a fuel-parametric induction for `red`, including the shifted tail
that its principal reduction branch constructs.
-/

/-- Step 3, isolated from the still-open reader lemma of Step 2. -/
theorem transPort_rungPS_of_L
    (hL : ∀ m, transPort (L m) = LBT m) (n : Nat) :
    transPort (rungPS n) = rungBT n := by
  rw [rungPS_eq_L, hL, LBT_two_mul_add_one]

end Ladder


/-! ### §21.5 `redP` IS THE IDENTITY ON THE LADDER — §21.4's named blocker, closed

§21.4 left link 2 one lemma away and named the first thing missing:
`redP (L m) = L m`, needing an induction for `red` along the ladder rather than along the way
`L` is built.  That is this section, and `redP_L` is now a theorem for every `m`.

`redP` is where `transPort` decides what it is looking at, so an induction on `runAux` could not
start without it.  Everything under it here — `trMax`, `ppair`, `brF`, `firstNodes`, `joints`,
`fAnc` and the `incrFirst` versions of each — is the reduction machinery COMPUTED on `L m`, and
none of it was statable on the append route.

**STILL OPEN, unchanged and still one lemma:** `transPort_LBT (m) : transPort (L m) = LBT m`
(measured at 13 points in §21.4).  `transPort_rungPS_of_L` consumes it and finishes the chain, so
closing it turns §21.1's 24-point measurement into a theorem for every `n`.

AXIOMS.  All 40 are `[propext, Quot.sound]`.  Twelve of them — `redP_L` included — carried
`Classical.choice` when first written, and every one was cleaned by rewriting the PROOF only: 40
statements diffed before and after, zero differences.  Second time in this file's history that the
whole dirty set turned out to be tactics rather than mathematics.  Do not shorten these proofs
back; see plan/constitutions.md 失敗形 2 の七番目 for why the obvious debugging method
(tracing dependencies) cannot find this, and plan/worker-spec.md for the two known sources.
-/

section Ladder2
open Trans.Recal
open Trans.Dict
#guard (List.range 40).all fun m => redP (L m) == L m

theorem L_add_two (m : Nat) :
    L (m + 2) = L 1 ++ incrFirst (L m) 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, L_succ (m + 2), ih]
    rw [show m + 1 = m + 1 by rfl, L_succ m]
    simp only [incrFirst, List.map_append, List.map_singleton,
      List.append_assoc]
    congr 1
    have hm : (m + 1) % 2 = (m + 3) % 2 := by omega
    simp [hm]
    omega

theorem fpar0_L_one_zero (m : Nat) :
    fpar0 (L (m + 2)) 1 0 = 0 := by
  have g00 := gp0_L (m + 2) 0 (by omega)
  have g01 := gp0_L (m + 2) 1 (by omega)
  simp at g00 g01
  unfold fpar0
  rw [if_neg (by simp [lenI]; omega)]
  simp only [fpar0Aux]
  rw [if_neg (by omega)]
  rw [show (1 : Int) - 1 = 0 by omega]
  rw [g01, g00, if_pos (by omega)]

theorem fpar1_L_one_zero (m : Nat) :
    fpar (L (m + 2)) 1 1 0 = 0 := by
  have g10 := gp1_L (m + 2) 0 (by omega)
  have g11 := gp1_L (m + 2) 1 (by omega)
  simp at g10 g11
  unfold fpar
  rw [if_neg (by simp [lenI]; omega)]
  rw [if_neg (by decide)]
  simp only [fpar1Aux]
  rw [fpar0_L_one_zero, if_neg (by omega), g10, g11,
    if_pos (by omega)]

theorem isParentP_L_one_zero (m : Nat) :
    isParentP (L (m + 2)) 1 1 0 = true := by
  have hlen : (0 : Int) < lenI (L (m + 2)) := by
    simp [lenI]
    omega
  unfold isParentP
  rw [fpar1_L_one_zero]
  rw [show decide ((0 : Int) ≤ 0) = true by rfl]
  rw [show decide ((0 : Int) < lenI (L (m + 2))) = true by
    simp [hlen]]
  rfl

theorem isParentP_L_two_one (m : Nat) :
    isParentP (L (m + 2)) 1 2 1 = false := by
  have hp := fpar1_L_even_prev (m + 2) 0 (by omega)
  have hp' : fpar (L (m + 2)) 1 2 1 = -1 := by simpa using hp
  unfold isParentP
  rw [hp']
  simp [lenI]

theorem trMax_L_add_two (m : Nat) : trMax (L (m + 2)) = 1 := by
  unfold trMax
  simp only [trMaxAux]
  rw [if_neg (by simp [lenI]; omega)]
  rw [show (0 : Int) + 1 = 1 by omega]
  rw [isParentP_L_one_zero]
  simp only [Bool.not_true]
  rw [if_neg (by decide)]
  rw [length_L]
  simp only [trMaxAux]
  rw [if_neg (by simp [lenI]; omega)]
  rw [show (1 : Int) + 1 = 2 by omega]
  rw [isParentP_L_two_one]
  rfl

theorem fpar_zero_zero (M : PS) : fpar M 0 0 0 = -1 := by
  unfold fpar
  by_cases hbad : (0 : Int) < 0 ∨ (0 : Int) ≥ lenI M
  · rw [if_pos hbad]
  · rw [if_neg hbad]
    rw [if_pos (by rfl)]
    simp only [fpar0Aux]
    rw [if_pos (by omega)]

theorem fpar0Aux_eq_neg_one_of_lt
    (f : Nat) (M : PS) (tgt j : Int)
    (h : fpar0Aux f M tgt j 0 < 0) :
    fpar0Aux f M tgt j 0 = -1 := by
  induction f generalizing j with
  | zero => rfl
  | succ f ih =>
    simp only [fpar0Aux] at h ⊢
    split
    · rfl
    · rename_i hj
      split
      · rename_i hfound
        simp [hj, hfound] at h
      · rename_i hfound
        simp [hj, hfound] at h ⊢
        exact ih (j - 1) h

theorem fpar_row0_eq_neg_one_of_lt
    (M : PS) (j : Int) (h : fpar M 0 j 0 < 0) :
    fpar M 0 j 0 = -1 := by
  unfold fpar at h ⊢
  by_cases hv : j < 0 ∨ j ≥ lenI M
  · rw [if_pos hv] at h ⊢
  · rw [if_neg hv] at h ⊢
    rw [if_pos (by decide)] at h ⊢
    exact fpar0Aux_eq_neg_one_of_lt _ _ _ _ h

theorem gp0_incrFirst_of_valid
    (M : PS) (a j : Int) (hj0 : 0 ≤ j) (hj : j.toNat < M.length) :
    gp0 (incrFirst M a) j = gp0 M j + a := by
  unfold gp0 incrFirst
  rw [if_neg (by omega), if_neg (by omega)]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_map]
  have he : M[j.toNat]? = some M[j.toNat] :=
    List.getElem?_eq_getElem hj
  rw [he]
  simp

theorem fpar0Aux_incrFirst
    (f : Nat) (M : PS) (a tgt j k : Int)
    (hk : 0 ≤ k) (hj : j < lenI M) :
    fpar0Aux f (incrFirst M a) (tgt + a) j k =
      fpar0Aux f M tgt j k := by
  induction f generalizing j with
  | zero => rfl
  | succ f ih =>
    simp only [fpar0Aux]
    by_cases hstop : j < k
    · rw [if_pos hstop, if_pos hstop]
    · rw [if_neg hstop, if_neg hstop]
      have hj0 : 0 ≤ j := by omega
      have hjnat : j.toNat < M.length := by
        simp [lenI] at hj
        omega
      rw [gp0_incrFirst_of_valid M a j hj0 hjnat]
      by_cases hfound : gp0 M j < tgt
      · rw [if_pos (by omega), if_pos hfound]
      · rw [if_neg (by omega), if_neg hfound]
        exact ih (j - 1) (by omega)

theorem fpar_row0_incrFirst
    (M : PS) (a j k : Int) (hk : 0 ≤ k)
    (hj0 : 0 ≤ j) (hj : j < lenI M) :
    fpar (incrFirst M a) 0 j k = fpar M 0 j k := by
  have hlen : lenI (incrFirst M a) = lenI M := by
    simp [lenI, incrFirst]
  have hjnat : j.toNat < M.length := by
    simp [lenI] at hj
    omega
  have hgp := gp0_incrFirst_of_valid M a j hj0 hjnat
  unfold fpar
  rw [hlen]
  rw [if_neg (by omega), if_pos (by decide)]
  rw [if_neg (by omega), if_pos (by decide)]
  rw [hgp]
  rw [show (incrFirst M a).length = M.length by simp [incrFirst]]
  exact fpar0Aux_incrFirst _ _ _ _ _ _ hk (by omega)

def ladderParent (k : Nat) : Nat :=
  if k % 2 = 1 then k - 1 else k - 2

theorem fpar_L_pos_ladderParent
    (m k : Nat) (hk0 : 0 < k) (hk : k ≤ m) :
    fpar (L m) 0 (k : Int) 0 = (ladderParent k : Nat) := by
  unfold ladderParent
  split
  · rename_i hodd
    have heq : k = 2 * (k / 2) + 1 := by omega
    rw [heq] at hk ⊢
    simpa using fpar_L_odd m (k / 2) hk
  · rename_i hnodd
    have heven : k % 2 = 0 := by omega
    have heq : k = 2 * ((k - 2) / 2) + 2 := by omega
    rw [heq] at hk ⊢
    simpa using fpar_L_even m ((k - 2) / 2) hk

theorem ladderParent_lt (k : Nat) (h : 0 < k) : ladderParent k < k := by
  unfold ladderParent
  split <;> omega

theorem isAncAux_incrFirst_L (a : Int) (k : Nat) : ∀ (m f : Nat),
    k ≤ m → k < f →
      isAncAux f (incrFirst (L m) a) 0 (k : Int) 0 = true := by
  refine Nat.strongRecOn (motive := fun k => ∀ (m f : Nat),
    k ≤ m → k < f →
      isAncAux f (incrFirst (L m) a) 0 (k : Int) 0 = true) k ?_
  intro k ih m f hkm hkf
  cases f with
  | zero => exact (Nat.not_lt_zero k hkf).elim
  | succ f =>
    unfold isAncAux
    by_cases hk0 : k = 0
    · subst k
      rw [if_pos (by rfl)]
    · have hkpos : 0 < k := by omega
      have hp := fpar_L_pos_ladderParent m k hkpos hkm
      have hps :
          fpar (incrFirst (L m) a) 0 (k : Int) 0 =
            (ladderParent k : Nat) := by
        rw [fpar_row0_incrFirst]
        · exact hp
        · omega
        · omega
        · simp [lenI]
          omega
      have h0k : (0 : Int) ≠ (k : Int) := by omega
      rw [show ((0 : Int) == (k : Int)) = false by simp [h0k]]
      rw [hps]
      have hpn : ((ladderParent k : Nat) : Int) ≠ -1 := by omega
      simp [hpn]
      have hpk : ladderParent k < k := ladderParent_lt k hkpos
      apply ih (ladderParent k)
      · exact hpk
      · exact Nat.le_trans (Nat.le_of_lt hpk) hkm
      · omega

theorem isAnc_incrFirst_L (a : Int) (m k : Nat) (hk : k ≤ m) :
    isAnc (incrFirst (L m) a) 0 (k : Int) 0 = true := by
  unfold isAnc
  rw [if_neg]
  · have h := isAncAux_incrFirst_L a k m (m + 2) hk (by omega)
    rw [show (incrFirst (L m) a).length = m + 1 by
      simp [incrFirst]]
    exact h
  · simp [lenI, incrFirst]

theorem fAncAux_incrFirst_L_getLast (a : Int) (k : Nat) :
    ∀ (m f : Nat) (acc : List Int),
      k ≤ m → k < f → acc.getLast? = some (k : Int) →
      (fAncAux f (incrFirst (L m) a) 0 (k : Int) 0 acc).getLast? =
        some 0 := by
  refine Nat.strongRecOn (motive := fun k =>
    ∀ (m f : Nat) (acc : List Int),
      k ≤ m → k < f → acc.getLast? = some (k : Int) →
      (fAncAux f (incrFirst (L m) a) 0 (k : Int) 0 acc).getLast? =
        some 0) k ?_
  intro k ih m f acc hkm hkf hlast
  cases f with
  | zero => exact (Nat.not_lt_zero k hkf).elim
  | succ f =>
    unfold fAncAux
    by_cases hk0 : k = 0
    · subst k
      rw [show ((0 : Nat) : Int) = 0 by rfl]
      rw [fpar_zero_zero]
      rw [if_neg (by omega)]
      exact hlast
    · have hkpos : 0 < k := by omega
      have hp := fpar_L_pos_ladderParent m k hkpos hkm
      have hps :
          fpar (incrFirst (L m) a) 0 (k : Int) 0 =
            (ladderParent k : Nat) := by
        rw [fpar_row0_incrFirst]
        · exact hp
        · omega
        · omega
        · simp [lenI]
          omega
      rw [hps]
      rw [if_pos (by omega)]
      have hpk : ladderParent k < k := ladderParent_lt k hkpos
      apply ih (ladderParent k)
      · exact hpk
      · exact Nat.le_trans (Nat.le_of_lt hpk) hkm
      · omega
      · simp

theorem fAnc_incrFirst_L_getLast (a : Int) (m : Nat) :
    (fAnc (incrFirst (L m) a) 0 (m : Int) 0).getLast? = some 0 := by
  unfold fAnc
  rw [if_neg]
  · rw [show (incrFirst (L m) a).length = m + 1 by
      simp [incrFirst]]
    exact fAncAux_incrFirst_L_getLast a m m (m + 2) [(m : Int)]
      (Nat.le_refl m) (by omega) (by simp)
  · simp [lenI, incrFirst]
    omega

theorem drop_two_L_add_two (m : Nat) :
    (L (m + 2)).drop 2 = incrFirst (L m) 1 := by
  rw [L_add_two]
  simp [L]

theorem slice_incrFirst_L_full (a : Int) (m : Nat) :
    slice (incrFirst (L m) a) 0 ((m + 1 : Nat) : Int) =
      incrFirst (L m) a := by
  unfold slice
  rw [show (0 : Int).toNat = 0 by rfl]
  simp only [List.drop_zero]
  rw [show (((m + 1 : Nat) : Int) - 0).toNat = m + 1 by omega]
  rw [show m + 1 = (incrFirst (L m) a).length by simp [incrFirst]]
  simp

theorem ppair_incrFirst_L (a : Int) (m : Nat) :
    ppair (incrFirst (L m) a) = [incrFirst (L m) a] := by
  unfold ppair
  rw [show (incrFirst (L m) a).length = m + 1 by simp [incrFirst]]
  simp only [ppairAux]
  rw [show lenI (incrFirst (L m) a) - 1 = (m : Int) by
    simp [lenI, incrFirst]]
  rw [if_neg (by omega)]
  rw [fAnc_incrFirst_L_getLast]
  simp only [Option.getD_some]
  rw [show (0 : Int) - 1 = -1 by omega]
  rw [if_pos (by omega)]
  rw [show (m : Int) + 1 = ((m + 1 : Nat) : Int) by omega]
  rw [slice_incrFirst_L_full]

theorem brF_L_add_two (m : Nat) :
    brF (L (m + 2)) = [incrFirst (L m) 1] := by
  unfold brF
  rw [trMax_L_add_two]
  rw [show ((1 : Int) + 1).toNat = 2 by rfl]
  rw [drop_two_L_add_two]
  exact ppair_incrFirst_L 1 m

theorem firstNodes_L_add_two (m : Nat) :
    firstNodes (L (m + 2)) = [2, ((m + 3 : Nat) : Int)] := by
  unfold firstNodes
  rw [brF_L_add_two, trMax_L_add_two]
  simp [idxSum, incrFirst]
  omega

theorem joints_L_add_two (m : Nat) : joints (L (m + 2)) = [0] := by
  unfold joints
  rw [firstNodes_L_add_two]
  have hp := fpar_L_even (m + 2) 0 (by omega)
  have hp' : fpar (L (m + 2)) 0 2 0 = 0 := by simpa using hp
  change [fpar (L (m + 2)) 0 2 0] = [0]
  rw [hp']

theorem incrFirst_one_neg_one (M : PS) :
    incrFirst (incrFirst M 1) (-1) = M := by
  simp only [incrFirst, List.map_map]
  induction M with
  | nil => rfl
  | cons c M ih =>
    rw [List.map_cons, ih]
    congr 1
    cases c
    simp
    omega

theorem gp0_incrFirst_L_zero (m : Nat) :
    gp0 (incrFirst (L m) 1) 0 = 1 := by
  rw [gp0_incrFirst_of_valid]
  · have h := gp0_L m 0 (by omega)
    simp at h
    rw [h]
    omega
  · omega
  · simp

theorem gp1_incrFirst_L_zero (m : Nat) :
    gp1 (incrFirst (L m) 1) 0 = 0 := by
  simp [gp1, incrFirst, L]

theorem isZeroP_incrFirst_L_succ (m : Nat) :
    isZeroP (incrFirst (L (m + 1)) 1) = false := by
  unfold isZeroP
  simp [incrFirst]

theorem isPrincipalP_incrFirst_L_succ (m : Nat) :
    isPrincipalP (incrFirst (L (m + 1)) 1) = true := by
  have ha := isAnc_incrFirst_L 1 (m + 1) (m + 1) (by omega)
  have ha' :
      isAnc (incrFirst (L (m + 1)) 1) 0
        (lenI (incrFirst (L (m + 1)) 1) - 1) 0 = true := by
    rw [show lenI (incrFirst (L (m + 1)) 1) - 1 =
      ((m + 1 : Nat) : Int) by
      simp [lenI, incrFirst]]
    exact ha
  unfold isPrincipalP
  rw [isZeroP_incrFirst_L_succ, ha']
  rfl

theorem red_L_zero (f : Nat) : red f (L 0) = L 0 := by
  cases f <;> rfl

theorem red_succ_incrFirst_L (f m : Nat) :
    red (f + 1) (incrFirst (L m) 1) = red f (L m) := by
  cases m with
  | zero =>
    rw [show incrFirst (L 0) 1 = [(1, 0)] by rfl]
    conv =>
      lhs
      rw [red]
    rw [if_pos (by rfl)]
    exact (red_L_zero f).symm
  | succ m =>
    conv =>
      lhs
      rw [red]
    rw [isZeroP_incrFirst_L_succ]
    rw [if_neg (by decide)]
    rw [isPrincipalP_incrFirst_L_succ]
    rw [if_pos (by decide)]
    rw [gp0_incrFirst_L_zero, gp1_incrFirst_L_zero]
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
    rw [show -(1 : Int) = -1 by rfl]
    rw [incrFirst_one_neg_one]

theorem isZeroP_L_add_two (m : Nat) : isZeroP (L (m + 2)) = false := by
  unfold isZeroP
  rw [length_L]
  rw [show (m + 2 + 1 == 1) = false by simp]
  rfl

theorem isPrincipalP_L_add_two (m : Nat) :
    isPrincipalP (L (m + 2)) = true := by
  rw [show m + 2 = (m + 1) + 1 by omega]
  exact isPrincipalP_L_succ (m + 1)

theorem gp0_L_zero (m : Nat) : gp0 (L m) 0 = 0 := by
  have h := gp0_L m 0 (by omega)
  simpa using h

theorem gp1_L_zero (m : Nat) : gp1 (L m) 0 = 0 := by
  have h := gp1_L m 0 (by omega)
  simpa using h

theorem cons_derp_incrFirst_L (m : Nat) :
    (1, 0) :: derp (incrFirst (L m) 1) = incrFirst (L m) 1 := by
  unfold derp incrFirst L
  rw [show m + 1 = 1 + m by omega, List.range_add]
  simp [List.map_map]

theorem red_add_two_L (f m : Nat) :
    red (f + 2) (L (m + 2)) =
      L 1 ++ incrFirst (red f (L m)) 1 := by
  conv =>
    lhs
    rw [red]
  rw [isZeroP_L_add_two]
  rw [if_neg (by decide)]
  rw [isPrincipalP_L_add_two]
  rw [if_pos (by decide)]
  rw [gp0_L_zero, gp1_L_zero]
  rw [if_pos (by decide)]
  rw [show lenI (L (m + 2)) - 1 = ((m + 2 : Nat) : Int) by
    simp [lenI]]
  rw [trMax_L_add_two]
  rw [if_neg (by simp; omega)]
  rw [brF_L_add_two, firstNodes_L_add_two, joints_L_add_two]
  simp only [List.length_cons, List.length_nil]
  rw [show List.range 1 = [0] by rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  dsimp only [List.getD]
  have hbr : (([incrFirst (L m) 1] : List PS)[0]?.getD []) =
      incrFirst (L m) 1 := by rfl
  simp only [hbr]
  rw [gp1_incrFirst_L_zero]
  rw [if_pos (by rfl)]
  rw [show (([0] : List Int)[0]?.getD 0) = 0 by rfl]
  change jjSeq 0 1 ++
      incrFirst (red (f + 1)
        ((1, 0) :: derp (incrFirst (L m) 1))) 1 =
    L 1 ++ incrFirst (red f (L m)) 1
  rw [cons_derp_incrFirst_L, red_succ_incrFirst_L]
  rfl

theorem red_L_one (f : Nat) : red f (L 1) = L 1 := by
  cases f <;> rfl

theorem red_two_mul_L (f m : Nat) : red (2 * f) (L m) = L m := by
  induction f generalizing m with
  | zero => rfl
  | succ f ih =>
    cases m with
    | zero => exact red_L_zero (2 * (f + 1))
    | succ m =>
      cases m with
      | zero => exact red_L_one (2 * (f + 1))
      | succ m =>
        rw [show 2 * (f + 1) = 2 * f + 2 by omega]
        rw [show m + 1 + 1 = m + 2 by omega]
        rw [red_add_two_L, ih]
        exact (L_add_two m).symm

theorem redP_L (m : Nat) : redP (L m) = L m := by
  unfold redP
  rw [show redFuel (L m) =
      2 * (20 + 2 * ((L m).length + maxE (L m))) by
    unfold redFuel
    omega]
  exact red_two_mul_L _ m

end Ladder2


/-! ### §21.6 THE CHAIN IS CLOSED — `transPort` on the ladder, and therefore on the rungs

§21.5 left exactly one lemma open on the `transPort` link.  This section proves it:
`transPort_rungPS` at the end is `∀ n`.  So of the four links

    rungM 0 n --ofMatrix--> rungPS n --transPort--> rungBT n --dict--> fsEsucc 0 n
         [1] theorem            [2] THEOREM (here)        [3] STILL OPEN

link 1 (§21.3 `ofMatrix_rungM_zero`) and link 2 (here) are theorems, and **link 3 is not**.
`dict_rungBT : dict (rungBT n) = fsEsucc 0 n` remains a `#guard` at 8 points, for the reason
§21.3 records: `Trans.Dict.collapse` is a NORMALISER (`wcnf`, `foldl`, `omegaNF`), so the two
sides are never definitionally equal and the three `dict` clauses cannot close the gap.  Three
attempts died there.  **§21.1's `oR (rungM k n) = fsEsucc k n` is therefore still a
measurement, not a theorem** — this section removes the second obstruction, not the last one.

WHY THIS ONE WORKED WHERE FOUR ATTEMPTS DID NOT.  The obstruction was never the fuel —
that was measured and turned out to be a non-issue on this family (see §21.4).  It was the
MEMO TABLE: `runAux` threads it, so a run is not determined by its list argument alone, and
that is exactly why no append lemma can exist (§21.3).  The move here is to stop treating the
memo as an obstacle and give it an INVARIANT: `Sound tbl` says every entry the table already
holds agrees with `spec`.  Carrying `Sound` through the induction turns the thing that killed
the append route into the thing that makes this induction go.  `step_odd`, `hit_case` and
`zero_case` are its three branches, and `runAux_L_main` is the induction itself, generalised
over fuel, request and table.

`W` is the Buchholz-side value as one `Nat`-indexed family, `spec` is the reader's specified
output including the request parameter, and `m_lt_transFuel` supplies the fuel bound that
`runAux_L_main` needs — the only place fuel appears at all.

AXIOMS.  Every theorem here is `[propext, Quot.sound]` or axiom-free; 7 of the 65 depend on
no axiom whatsoever.  No `Classical.choice`, no `native_decide`, no `sorry`.  Measured on the
submission before transplant, and again after.

PROVENANCE.  Written by a claude-opus-5 worker, against the same brief given simultaneously
to a codex worker; both reached the target with identical axiom cleanliness.  This submission
was taken for three reasons: it closes the chain to `transPort_rungPS` rather than stopping at
`transPort_LBT`; it names the memo invariant instead of only satisfying it; and it is
documented.  The comparison is recorded in `table/model-comparison-2026-08-11.txt`, including
what it does not establish.
-/

section Ladder3
open Trans.Recal
open Trans.Dict
/-! ## 1. The Buchholz side of the ladder, as one Nat-indexed family -/

/-- `W k` is the value the reader takes on `L k` for `k ≥ 1`, extended by `W 0 = D_0 0`
    (which is the value of the *marked* reader at the bottom of an even ladder). -/
def W : Nat → BT
  | 0 => .D 0 .zero
  | 1 => .D 0 (.D 1 .zero)
  | k + 2 => .D 0 (.sum (.D 1 .zero) (W k))

/-- The value of the marked reader below an odd ladder. -/
def V : BT := .D 1 .zero

#guard (List.range 13).all fun m => (m == 0) || (LBT m == W m)

theorem W_add_two (k : Nat) : W (k + 2) = .D 0 (.sum (.D 1 .zero) (W k)) := rfl

/-! ### `LBT` is `W` -/

theorem LBT_step (m : Nat) (h : 1 ≤ m) :
    LBT (m + 2) = .D 0 ((BT.D 1 BT.zero).sum (LBT m)) := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · obtain ⟨p, hp⟩ : ∃ p, m = 2 * p + 2 := ⟨(m - 2) / 2, by omega⟩
    subst hp
    simp only [LBT]
    rw [if_neg (by omega), if_neg (by omega)]
    rw [show (2 * p + 3 + 1) / 2 = (2 * p + 1 + 1) / 2 + 1 by omega]
    rfl
  · obtain ⟨n, hn⟩ : ∃ n, m = 2 * n + 1 := ⟨m / 2, by omega⟩
    subst hn
    simp only [LBT]
    rw [if_pos (by omega), if_pos (by omega)]
    rw [show (2 * n + 2) / 2 = 2 * n / 2 + 1 by omega]
    rfl

theorem LBT_W (m : Nat) : LBT (m + 1) = W (m + 1) := by
  refine Nat.strongRecOn (motive := fun m => LBT (m + 1) = W (m + 1)) m ?_
  clear m
  intro m ih
  match m with
  | 0 => rfl
  | 1 => rfl
  | k + 2 =>
    rw [show k + 2 + 1 = (k + 1) + 2 by omega, LBT_step (k + 1) (by omega), ih k (by omega)]
    rfl

/-! ### Structure of `W` under `toL`, `size`, `replMark`, `isMarkedB` -/

theorem toL_W (k : Nat) : (W k).toL = [W k] := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

theorem size_W (k : Nat) : k + 2 ≤ BT.size (W k) := by
  refine Nat.strongRecOn (motive := fun k => k + 2 ≤ BT.size (W k)) k ?_
  clear k
  intro k ih
  match k with
  | 0 => decide
  | 1 => decide
  | j + 2 =>
    have h := ih j (by omega)
    have hs : BT.size (W (j + 2)) = 1 + (1 + BT.size (BT.D 1 BT.zero) + BT.size (W j)) := rfl
    have h2 : BT.size (BT.D 1 BT.zero) = 2 := rfl
    omega

theorem beq_Dsum_W0 (x : BT) : (BT.D 0 ((BT.D 1 BT.zero).sum x) == W 0) = false := rfl
theorem beq_Dsum_W1 (x : BT) : (BT.D 0 ((BT.D 1 BT.zero).sum x) == W 1) = false := rfl

/-- One rung of `replMark` down an even `W`. -/
theorem replMark_W_even (n : Nat) : ∀ f : Nat, 2 * n + 2 ≤ f →
    replMark f (W (2 * n)) (W 0) (W 1) = some (W (2 * n + 1)) := by
  induction n with
  | zero =>
    intro f hf
    match f with
    | 0 => exact absurd hf (by omega)
    | f + 1 => rfl
  | succ n ih =>
    intro f hf
    match f with
    | 0 => exact absurd hf (by omega)
    | 1 => exact absurd hf (by omega)
    | f + 2 =>
      have hstep := ih f (by omega)
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, W_add_two]
      show ((replMark (f + 1) (BT.sum (BT.D 1 BT.zero) (W (2 * n))) (W 0) (W 1)).map
        (fun aa => BT.D 0 aa)) = _
      show ((match (BT.toL (BT.sum (BT.D 1 BT.zero) (W (2 * n)))).getLast? with
        | none => none
        | some last => (replMark f last (W 0) (W 1)).map
            (fun ll => BT.ofL ((BT.toL (BT.sum (BT.D 1 BT.zero) (W (2 * n)))).dropLast ++ [ll]))).map
        (fun aa => BT.D 0 aa)) = _
      rw [show BT.toL (BT.sum (BT.D 1 BT.zero) (W (2 * n))) = [BT.D 1 BT.zero, W (2 * n)] by
        show [BT.D 1 BT.zero] ++ BT.toL (W (2 * n)) = _
        rw [toL_W]; rfl]
      show (Option.map (fun aa => BT.D 0 aa)
              (Option.map (fun ll => BT.ofL ([BT.D 1 BT.zero] ++ [ll]))
                (replMark f (W (2 * n)) (W 0) (W 1)))) = _
      rw [hstep]
      rfl

/-- One rung of `replMark` down an odd `W`. -/
theorem replMark_W_odd (n : Nat) : ∀ f : Nat, 2 * n + 3 ≤ f →
    replMark f (W (2 * n + 1)) (W 1) (W 2) = some (W (2 * n + 2)) := by
  induction n with
  | zero =>
    intro f hf
    match f with
    | 0 => exact absurd hf (by omega)
    | f + 1 => rfl
  | succ n ih =>
    intro f hf
    match f with
    | 0 => exact absurd hf (by omega)
    | 1 => exact absurd hf (by omega)
    | f + 2 =>
      have hstep := ih f (by omega)
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, W_add_two]
      show ((replMark (f + 1) (BT.sum (BT.D 1 BT.zero) (W (2 * n + 1))) (W 1) (W 2)).map
        (fun aa => BT.D 0 aa)) = _
      show ((match (BT.toL (BT.sum (BT.D 1 BT.zero) (W (2 * n + 1)))).getLast? with
        | none => none
        | some last => (replMark f last (W 1) (W 2)).map
            (fun ll => BT.ofL
              ((BT.toL (BT.sum (BT.D 1 BT.zero) (W (2 * n + 1)))).dropLast ++ [ll]))).map
        (fun aa => BT.D 0 aa)) = _
      rw [show BT.toL (BT.sum (BT.D 1 BT.zero) (W (2 * n + 1))) = [BT.D 1 BT.zero, W (2 * n + 1)] by
        show [BT.D 1 BT.zero] ++ BT.toL (W (2 * n + 1)) = _
        rw [toL_W]; rfl]
      show (Option.map (fun aa => BT.D 0 aa)
              (Option.map (fun ll => BT.ofL ([BT.D 1 BT.zero] ++ [ll]))
                (replMark f (W (2 * n + 1)) (W 1) (W 2)))) = _
      rw [hstep]
      rfl

theorem isMarkedBAux_W_even (n : Nat) : ∀ f : Nat, 2 * n + 2 ≤ f →
    isMarkedBAux f (some (W (2 * n))) (W 0) = true := by
  induction n with
  | zero =>
    intro f hf
    match f with
    | 0 => exact absurd hf (by omega)
    | f + 1 => rfl
  | succ n ih =>
    intro f hf
    match f with
    | 0 => exact absurd hf (by omega)
    | 1 => exact absurd hf (by omega)
    | f + 2 =>
      have hstep := ih f (by omega)
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, W_add_two]
      simp only [isMarkedBAux]
      rw [beq_Dsum_W0, if_neg (by simp)]
      rw [show nextMarkedB (BT.D 0 (BT.sum (BT.D 1 BT.zero) (W (2 * n))))
            = some (BT.sum (BT.D 1 BT.zero) (W (2 * n))) from rfl]
      simp only [isMarkedBAux]
      rw [show (BT.sum (BT.D 1 BT.zero) (W (2 * n)) == W 0) = false from rfl, if_neg (by simp)]
      rw [show nextMarkedB (BT.sum (BT.D 1 BT.zero) (W (2 * n))) = some (W (2 * n)) by
        show (BT.toL (BT.sum (BT.D 1 BT.zero) (W (2 * n)))).getLast? = _
        rw [show BT.toL (BT.sum (BT.D 1 BT.zero) (W (2 * n))) = [BT.D 1 BT.zero, W (2 * n)] by
          show [BT.D 1 BT.zero] ++ BT.toL (W (2 * n)) = _
          rw [toL_W]; rfl]
        rfl]
      exact hstep

theorem isMarkedBAux_W_odd (n : Nat) : ∀ f : Nat, 2 * n + 3 ≤ f →
    isMarkedBAux f (some (W (2 * n + 1))) (W 1) = true := by
  induction n with
  | zero =>
    intro f hf
    match f with
    | 0 => exact absurd hf (by omega)
    | f + 1 => rfl
  | succ n ih =>
    intro f hf
    match f with
    | 0 => exact absurd hf (by omega)
    | 1 => exact absurd hf (by omega)
    | f + 2 =>
      have hstep := ih f (by omega)
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, W_add_two]
      simp only [isMarkedBAux]
      rw [beq_Dsum_W1, if_neg (by simp)]
      rw [show nextMarkedB (BT.D 0 (BT.sum (BT.D 1 BT.zero) (W (2 * n + 1))))
            = some (BT.sum (BT.D 1 BT.zero) (W (2 * n + 1))) from rfl]
      simp only [isMarkedBAux]
      rw [show (BT.sum (BT.D 1 BT.zero) (W (2 * n + 1)) == W 1) = false from rfl, if_neg (by simp)]
      rw [show nextMarkedB (BT.sum (BT.D 1 BT.zero) (W (2 * n + 1))) = some (W (2 * n + 1)) by
        show (BT.toL (BT.sum (BT.D 1 BT.zero) (W (2 * n + 1)))).getLast? = _
        rw [show BT.toL (BT.sum (BT.D 1 BT.zero) (W (2 * n + 1)))
              = [BT.D 1 BT.zero, W (2 * n + 1)] by
          show [BT.D 1 BT.zero] ++ BT.toL (W (2 * n + 1)) = _
          rw [toL_W]; rfl]
        rfl]
      exact hstep

theorem isMarkedB_W_even (n : Nat) : isMarkedB (W (2 * n)) (W 0) = true := by
  unfold isMarkedB
  exact isMarkedBAux_W_even n _ (by have := size_W (2 * n); omega)

theorem isMarkedB_W_odd (n : Nat) : isMarkedB (W (2 * n + 1)) (W 1) = true := by
  unfold isMarkedB
  exact isMarkedBAux_W_odd n _ (by have := size_W (2 * n + 1); omega)

theorem isMarkedB_V_W_one : isMarkedB V (W 1) = false := by decide

/-! ## 2. The specification: value of `Trans`/`Mark` on every rung of the ladder -/

/-- The value of `Mark q` on `L m` once the mark has fallen off the bottom. -/
def Wbot (m : Nat) : BT := if m % 2 = 0 then W 0 else V

/-- `Mark q` on `L m`: the mark `q` drops the ladder by `2 * ((q+1)/2)` rungs. -/
def specM (m q : Nat) : BT :=
  if m = 0 then BT.zero
  else if 2 * ((q + 1) / 2) ≤ m then W (m - 2 * ((q + 1) / 2))
  else Wbot m

/-- `Trans` (`req = none`) and `Mark q` (`req = some q`) on `L m`. -/
def spec (m : Nat) (req : Option Nat) : BT := specM m (req.getD 0)

-- the specification is the measured value, at every rung and every mark reachable
#guard (List.range 11).all fun m =>
  (Id.run ((runAux (transFuel (L m) + 60) (L m) none).run' []) == spec m none) &&
  ((List.range (m + 4)).all fun q =>
    Id.run ((runAux (transFuel (L m) + 60) (L m) (some (q : Int))).run' []) == spec m (some q))

theorem spec_none (m : Nat) : spec m none = specM m 0 := rfl
theorem spec_some (m q : Nat) : spec m (some q) = specM m q := rfl

theorem specM_zero (q : Nat) : specM 0 q = BT.zero := by simp [specM]

theorem specM_pos_zero (m : Nat) (h : 1 ≤ m) : specM m 0 = W m := by
  unfold specM
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1

/-! ## 3. Control flow of the reader on the ladder -/

theorem mrun_bind (x : MM BT) (k : BT → MM BT) (s : Memo) :
    (x >>= k).run s = (k (x.run s).1).run (x.run s).2 := rfl

theorem mrun_get (k : Memo → MM BT) (s : Memo) :
    ((get : MM Memo) >>= k).run s = (k s).run s := rfl

theorem isReducedP_L (m : Nat) : isReducedP (L m) = true := by
  unfold isReducedP
  rw [redP_L]
  exact beq_iff_eq.mpr rfl

theorem lenI_L (m : Nat) : lenI (L m) = (m : Int) + 1 := by
  simp [lenI]

theorem lenI_L_sub_one (m : Nat) : lenI (L m) - 1 = (m : Int) := by
  rw [lenI_L]; omega

theorem gp1_L_top (m : Nat) : gp1 (L m) (m : Int) = ((m % 2 : Nat) : Int) :=
  gp1_L m m (Nat.le_refl m)

theorem runAux_L_zero_run (f : Nat) (rq : Option Int) (tbl : Memo) :
    (runAux (f + 1) (L 0) rq).run tbl
      = match tbl.find? (fun p => p.1 == (L 0, rq)) with
        | some p => (p.2, tbl)
        | none => (BT.zero, ((L 0, rq), BT.zero) :: tbl) := by
  simp only [runAux]
  rw [mrun_get]
  cases hfind : tbl.find? (fun p => p.1 == (L 0, rq)) with
  | none =>
    rw [if_neg (by simp [isReducedP_L])]
    rw [if_pos (by decide)]
    rw [if_pos (by decide)]
    rfl
  | some p => rfl

/-! ## 4. The memo table -/

/-- The requests the reader ever makes on the ladder are non-negative. -/
def cast? (r : Option Nat) : Option Int := r.map (fun q : Nat => (q : Int))

theorem cast?_none : cast? none = none := rfl
theorem cast?_some (q : Nat) : cast? (some q) = some (q : Int) := rfl

/-- A memo table is sound when every entry keyed on the ladder holds the specified value. -/
def Sound (tbl : Memo) : Prop :=
  ∀ p ∈ tbl, ∀ (k : Nat) (r : Option Nat), p.1 = (L k, cast? r) → p.2 = spec k r

theorem Sound_nil : Sound [] := by
  intro p hp
  exact absurd hp (by simp)

theorem L_inj {m k : Nat} (h : L m = L k) : m = k := by
  have h2 := congrArg List.length h
  rw [length_L, length_L] at h2
  omega

theorem cast?_inj {r1 r2 : Option Nat} (h : cast? r1 = cast? r2) : r1 = r2 := by
  cases r1 with
  | none =>
    cases r2 with
    | none => rfl
    | some b => exact absurd h (by simp [cast?])
  | some a =>
    cases r2 with
    | none => exact absurd h (by simp [cast?])
    | some b =>
      have h1 : ((a : Nat) : Int) = ((b : Nat) : Int) := Option.some.inj h
      have h2 : a = b := by omega
      rw [h2]

theorem Sound_cons (tbl : Memo) (hs : Sound tbl) (m : Nat) (req : Option Nat) (v : BT)
    (hv : v = spec m req) : Sound (((L m, cast? req), v) :: tbl) := by
  intro p hp k r hk
  rcases List.mem_cons.mp hp with h | h
  · subst h
    have hk' : (L m, cast? req) = (L k, cast? r) := hk
    have hm : m = k := L_inj (congrArg Prod.fst hk')
    have hr : req = r := cast?_inj (congrArg Prod.snd hk')
    subst hm
    subst hr
    exact hv
  · exact hs p h k r hk

theorem Sound_find (tbl : Memo) (hs : Sound tbl) (m : Nat) (req : Option Nat)
    (p : (PS × Option Int) × BT)
    (h : tbl.find? (fun q => q.1 == (L m, cast? req)) = some p) : p.2 = spec m req := by
  have hmem : p ∈ tbl := List.mem_of_find?_eq_some h
  have hb := List.find?_some h
  simp only [] at hb
  exact hs p hmem m req (eq_of_beq hb)

/-! ## 5. Arithmetic of the specification -/

theorem specM_lt (m q : Nat) (h1 : 1 ≤ m) (h2 : 2 * ((q + 1) / 2) ≤ m) :
    specM m q = W (m - 2 * ((q + 1) / 2)) := by
  unfold specM
  rw [if_neg (by omega), if_pos h2]

theorem specM_ge_bot (m q : Nat) (h1 : 1 ≤ m) (h2 : m < 2 * ((q + 1) / 2)) :
    specM m q = Wbot m := by
  unfold specM
  rw [if_neg (by omega), if_neg (by omega)]

theorem specM_c1_even (n : Nat) : specM (2 * n + 1) (2 * n) = W 1 := by
  rw [specM_lt (2 * n + 1) (2 * n) (by omega) (by omega)]
  congr 1
  omega

theorem specM_c1_odd (n : Nat) : specM (2 * n + 2) (2 * n + 2) = W 0 := by
  rw [specM_lt (2 * n + 2) (2 * n + 2) (by omega) (by omega)]
  congr 1
  omega

theorem specM_even_ge (n q : Nat) (h : 2 * n + 1 ≤ q) : specM (2 * n + 2) q = W 0 := by
  by_cases hc : 2 * ((q + 1) / 2) ≤ 2 * n + 2
  · rw [specM_lt (2 * n + 2) q (by omega) hc]
    congr 1
    omega
  · rw [specM_ge_bot (2 * n + 2) q (by omega) (by omega)]
    unfold Wbot
    rw [if_pos (by omega)]

theorem specM_odd_ge (n q : Nat) (h : 2 * n + 3 ≤ q) : specM (2 * n + 3) q = V := by
  rw [specM_ge_bot (2 * n + 3) q (by omega) (by omega)]
  unfold Wbot
  rw [if_neg (by omega)]

theorem spec_one_succ (q : Nat) : spec 1 (some (q + 1)) = V := by
  rw [spec_some, specM_ge_bot 1 (q + 1) (by omega) (by omega)]
  unfold Wbot
  rw [if_neg (by omega)]

theorem spec_pos_none (m : Nat) (h : 1 ≤ m) : spec m none = W m := by
  rw [spec_none, specM_pos_zero m h]

theorem beq_W_zero (j : Nat) : (W j == BT.zero) = false := by
  match j with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-! ## 6. The reader's decisions on `L m`, computed -/

theorem gp1_L_even (n : Nat) : gp1 (L (2 * n + 2)) ((2 * n + 2 : Nat) : Int) = 0 := by
  have h := gp1_L (2 * n + 2) (2 * n + 2) (Nat.le_refl _)
  rw [show (2 * n + 2) % 2 = 0 by omega] at h
  simpa using h

theorem gp1_L_oddv (n : Nat) : gp1 (L (2 * n + 3)) ((2 * n + 3 : Nat) : Int) = 1 := by
  have h := gp1_L (2 * n + 3) (2 * n + 3) (Nat.le_refl _)
  rw [show (2 * n + 3) % 2 = 1 by omega] at h
  simpa using h

theorem gp1_L_odd_j0 (n : Nat) : gp1 (L (2 * n + 3)) ((2 * n + 2 : Nat) : Int) = 0 := by
  have h := gp1_L (2 * n + 3) (2 * n + 2) (by omega)
  rw [show (2 * n + 2) % 2 = 0 by omega] at h
  simpa using h

theorem fpar_even_top (n : Nat) :
    fpar (L (2 * n + 2)) 0 ((2 * n + 2 : Nat) : Int) 0 = ((2 * n : Nat) : Int) :=
  fpar_L_even (2 * n + 2) n (Nat.le_refl _)

theorem fpar_odd_top (n : Nat) :
    fpar (L (2 * n + 3)) 0 ((2 * n + 3 : Nat) : Int) 0 = ((2 * n + 2 : Nat) : Int) := by
  have h := fpar_L_odd (2 * n + 3) (n + 1) (by omega)
  rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega, show 2 * (n + 1) = 2 * n + 2 by omega] at h
  exact h

theorem adm_even_j0 (n : Nat) :
    adm (L (2 * n + 2)) ((2 * n : Nat) : Int) = ((2 * n : Nat) : Int) :=
  adm_L_even (2 * n + 2) n (by omega)

theorem adm_odd_j0 (n : Nat) :
    adm (L (2 * n + 3)) ((2 * n + 2 : Nat) : Int) = ((2 * n + 2 : Nat) : Int) := by
  have h := adm_L_even (2 * n + 3) (n + 1) (by omega)
  rw [show 2 * (n + 1) = 2 * n + 2 by omega] at h
  exact h

theorem ty_even (n : Nat) :
    transTypeMain (L (2 * n + 2)) ((2 * n : Nat) : Int) ((2 * n + 2 : Nat) : Int) = 1 := by
  unfold transTypeMain
  rw [gp1_L_even n, if_pos (by rfl)]
  rw [isAdm_L_even (2 * n + 2) n (by omega), if_pos (by rfl)]

theorem ty_odd (n : Nat) :
    transTypeMain (L (2 * n + 3)) ((2 * n + 2 : Nat) : Int) ((2 * n + 3 : Nat) : Int) = 6 := by
  unfold transTypeMain
  rw [gp1_L_oddv n, gp1_L_odd_j0 n]
  rw [if_neg (by decide)]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]

theorem mkC2_even (n : Nat) :
    mkC2 (L (2 * n + 2)) ((2 * n : Nat) : Int) ((2 * n + 2 : Nat) : Int) 1 (W 1) = W 2 := by
  show BT.D 0 (bplus (BT.D 1 BT.zero)
    (BT.D (gp1 (L (2 * n + 2)) ((2 * n + 2 : Nat) : Int)).toNat BT.zero)) = W 2
  rw [gp1_L_even n]
  rfl

theorem mkC2_odd (n : Nat) :
    mkC2 (L (2 * n + 3)) ((2 * n + 2 : Nat) : Int) ((2 * n + 3 : Nat) : Int) 6 (W 0) = W 1 := by
  show BT.D 0 (BT.D (gp1 (L (2 * n + 3)) ((2 * n + 3 : Nat) : Int)).toNat BT.zero) = W 1
  rw [gp1_L_oddv n]
  rfl

/-! ## 7. One rung of the recursion -/

theorem runAux_hit (f m : Nat) (rq : Option Int) (tbl : Memo)
    (p : (PS × Option Int) × BT)
    (hfind : tbl.find? (fun x => x.1 == (L m, rq)) = some p) :
    (runAux (f + 1) (L m) rq).run tbl = (p.2, tbl) := by
  simp only [runAux]
  rw [mrun_get, hfind]
  rfl

theorem step_one (f : Nat) (req : Option Nat) (tbl : Memo) (hs : Sound tbl)
    (ih : ∀ (r : Option Nat) (t : Memo), Sound t →
      ((runAux f (L 0) (cast? r)).run t).1 = spec 0 r ∧
      Sound ((runAux f (L 0) (cast? r)).run t).2)
    (hfind : tbl.find? (fun p => p.1 == (L 1, cast? req)) = none) :
    ((runAux (f + 1) (L 1) (cast? req)).run tbl).1 = spec 1 req ∧
    Sound ((runAux (f + 1) (L 1) (cast? req)).run tbl).2 := by
  have h1 := ih none tbl hs
  rw [cast?_none, show spec 0 none = BT.zero from rfl] at h1
  simp only [runAux]
  rw [mrun_get, hfind]
  rw [if_neg (by simp [isReducedP_L])]
  rw [if_neg (by decide)]
  rw [if_neg (by rw [show isPrincipalP (L 1) = true from isPrincipalP_L_succ 0]; simp)]
  rw [show predP (L 1) = L 0 from predP_L_succ 0]
  rw [mrun_bind, h1.1]
  rw [if_pos (by rfl)]
  rw [show gp1 (L 1) (lenI (L 1) - 1) = 1 from by decide]
  cases req with
  | none =>
    rw [cast?_none, spec_pos_none 1 (by omega)]
    exact ⟨rfl, Sound_cons _ h1.2 1 none (W 1) (spec_pos_none 1 (by omega)).symm⟩
  | some q =>
    rw [cast?_some]
    cases q with
    | zero =>
      have hv : spec 1 (some 0) = W 1 := by rw [spec_some, specM_pos_zero 1 (by omega)]
      rw [hv]
      exact ⟨rfl, Sound_cons _ h1.2 1 (some 0) (W 1) hv.symm⟩
    | succ q =>
      rw [spec_one_succ q]
      exact ⟨rfl, Sound_cons _ h1.2 1 (some (q + 1)) V (spec_one_succ q).symm⟩

theorem step_even (f n : Nat) (req : Option Nat) (tbl : Memo) (hs : Sound tbl)
    (ih : ∀ (r : Option Nat) (t : Memo), Sound t →
      ((runAux f (L (2 * n + 1)) (cast? r)).run t).1 = spec (2 * n + 1) r ∧
      Sound ((runAux f (L (2 * n + 1)) (cast? r)).run t).2)
    (hfind : tbl.find? (fun p => p.1 == (L (2 * n + 2), cast? req)) = none) :
    ((runAux (f + 1) (L (2 * n + 2)) (cast? req)).run tbl).1 = spec (2 * n + 2) req ∧
    Sound ((runAux (f + 1) (L (2 * n + 2)) (cast? req)).run tbl).2 := by
  have h1 := ih none tbl hs
  rw [cast?_none, spec_pos_none (2 * n + 1) (by omega)] at h1
  have h2 := ih (some (2 * n)) _ h1.2
  rw [cast?_some, spec_some, specM_c1_even n] at h2
  simp only [runAux]
  rw [mrun_get, hfind]
  rw [if_neg (by simp [isReducedP_L])]
  rw [if_neg (by rw [lenI_L_sub_one]; simp only [beq_iff_eq]; omega)]
  rw [if_neg (by
    rw [show isPrincipalP (L (2 * n + 2)) = true from isPrincipalP_L_succ (2 * n + 1)]; simp)]
  rw [show predP (L (2 * n + 2)) = L (2 * n + 1) from predP_L_succ (2 * n + 1)]
  rw [mrun_bind, h1.1, beq_W_zero, if_neg (by simp)]
  rw [lenI_L_sub_one, fpar_even_top n, adm_even_j0 n, ty_even n]
  rw [mrun_bind, h2.1, mkC2_even n]
  cases req with
  | none =>
    have hfuel : 2 * n + 3 ≤ BT.size (W (2 * n + 1)) + (BT.size (W 1) + BT.size (W 2) + 4) := by
      have := size_W (2 * n + 1); omega
    rw [replMark_W_odd n _ hfuel]
    have hv : spec (2 * n + 2) none = W (2 * n + 2) := spec_pos_none _ (by omega)
    rw [hv]
    exact ⟨rfl, Sound_cons _ h2.2 (2 * n + 2) none (W (2 * n + 2)) hv.symm⟩
  | some q =>
    rw [cast?_some]
    dsimp only
    by_cases hq : q ≤ 2 * n
    · have h3 := ih (some q) _ h2.2
      rw [cast?_some, spec_some, specM_lt (2 * n + 1) q (by omega) (by omega),
        show 2 * n + 1 - 2 * ((q + 1) / 2) = 2 * (n - (q + 1) / 2) + 1 by omega] at h3
      rw [if_pos (show ((q : Nat) : Int) < ((2 * n + 2 : Nat) : Int) by omega)]
      rw [mrun_bind, h3.1]
      rw [isMarkedB_W_odd (n - (q + 1) / 2), if_pos (by rfl)]
      have hfuel : 2 * (n - (q + 1) / 2) + 3 ≤
          BT.size (W (2 * (n - (q + 1) / 2) + 1)) + (BT.size (W 1) + BT.size (W 2) + 4) := by
        have := size_W (2 * (n - (q + 1) / 2) + 1); omega
      rw [replMark_W_odd (n - (q + 1) / 2) _ hfuel]
      have hv : spec (2 * n + 2) (some q) = W (2 * (n - (q + 1) / 2) + 2) := by
        rw [spec_some, specM_lt (2 * n + 2) q (by omega) (by omega)]
        congr 1
        omega
      rw [hv]
      exact ⟨rfl, Sound_cons _ h3.2 (2 * n + 2) (some q) _ hv.symm⟩
    · by_cases hq2 : q = 2 * n + 1
      · subst hq2
        have h3 := ih (some (2 * n + 1)) _ h2.2
        rw [cast?_some, spec_some, specM_ge_bot (2 * n + 1) (2 * n + 1) (by omega) (by omega),
          show Wbot (2 * n + 1) = V from by unfold Wbot; rw [if_neg (by omega)]] at h3
        rw [if_pos (show ((2 * n + 1 : Nat) : Int) < ((2 * n + 2 : Nat) : Int) by omega)]
        rw [mrun_bind, h3.1]
        rw [isMarkedB_V_W_one, if_neg (by simp)]
        rw [gp1_L_even n]
        have hv : spec (2 * n + 2) (some (2 * n + 1)) = W 0 := by
          rw [spec_some]; exact specM_even_ge n (2 * n + 1) (by omega)
        rw [hv]
        exact ⟨rfl, Sound_cons _ h3.2 (2 * n + 2) (some (2 * n + 1)) (W 0) hv.symm⟩
      · rw [if_neg (show ¬(((q : Nat) : Int) < ((2 * n + 2 : Nat) : Int)) by omega)]
        rw [gp1_L_even n]
        have hv : spec (2 * n + 2) (some q) = W 0 := by
          rw [spec_some]; exact specM_even_ge n q (by omega)
        rw [hv]
        exact ⟨rfl, Sound_cons _ h2.2 (2 * n + 2) (some q) (W 0) hv.symm⟩

theorem replMark_W_evenN (k : Nat) (hk : k % 2 = 0) (f : Nat) (hf : k + 2 ≤ f) :
    replMark f (W k) (W 0) (W 1) = some (W (k + 1)) := by
  obtain ⟨j, hj⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
  subst hj
  exact replMark_W_even j f hf

theorem isMarkedB_W_evenN (k : Nat) (hk : k % 2 = 0) : isMarkedB (W k) (W 0) = true := by
  obtain ⟨j, hj⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
  subst hj
  exact isMarkedB_W_even j

theorem step_odd (f n : Nat) (req : Option Nat) (tbl : Memo) (hs : Sound tbl)
    (ih : ∀ (r : Option Nat) (t : Memo), Sound t →
      ((runAux f (L (2 * n + 2)) (cast? r)).run t).1 = spec (2 * n + 2) r ∧
      Sound ((runAux f (L (2 * n + 2)) (cast? r)).run t).2)
    (hfind : tbl.find? (fun p => p.1 == (L (2 * n + 3), cast? req)) = none) :
    ((runAux (f + 1) (L (2 * n + 3)) (cast? req)).run tbl).1 = spec (2 * n + 3) req ∧
    Sound ((runAux (f + 1) (L (2 * n + 3)) (cast? req)).run tbl).2 := by
  have h1 := ih none tbl hs
  rw [cast?_none, spec_pos_none (2 * n + 2) (by omega)] at h1
  have h2 := ih (some (2 * n + 2)) _ h1.2
  rw [cast?_some, spec_some, specM_c1_odd n] at h2
  simp only [runAux]
  rw [mrun_get, hfind]
  rw [if_neg (by simp [isReducedP_L])]
  rw [if_neg (by rw [lenI_L_sub_one]; simp only [beq_iff_eq]; omega)]
  rw [if_neg (by
    rw [show isPrincipalP (L (2 * n + 3)) = true from isPrincipalP_L_succ (2 * n + 2)]; simp)]
  rw [show predP (L (2 * n + 3)) = L (2 * n + 2) from predP_L_succ (2 * n + 2)]
  rw [mrun_bind, h1.1, beq_W_zero, if_neg (by simp)]
  rw [lenI_L_sub_one, fpar_odd_top n, adm_odd_j0 n, ty_odd n]
  rw [mrun_bind, h2.1, mkC2_odd n]
  cases req with
  | none =>
    have hfuel : 2 * n + 2 + 2 ≤
        BT.size (W (2 * n + 2)) + (BT.size (W 0) + BT.size (W 1) + 4) := by
      have := size_W (2 * n + 2); omega
    rw [replMark_W_evenN (2 * n + 2) (by omega) _ hfuel]
    have hv : spec (2 * n + 3) none = W (2 * n + 3) := spec_pos_none _ (by omega)
    rw [hv]
    exact ⟨rfl, Sound_cons _ h2.2 (2 * n + 3) none (W (2 * n + 2 + 1)) (by rw [hv])⟩
  | some q =>
    rw [cast?_some]
    dsimp only
    by_cases hq : q ≤ 2 * n + 2
    · have h3 := ih (some q) _ h2.2
      rw [cast?_some, spec_some, specM_lt (2 * n + 2) q (by omega) (by omega)] at h3
      rw [if_pos (show ((q : Nat) : Int) < ((2 * n + 3 : Nat) : Int) by omega)]
      rw [mrun_bind, h3.1]
      rw [isMarkedB_W_evenN (2 * n + 2 - 2 * ((q + 1) / 2)) (by omega), if_pos (by rfl)]
      have hfuel : 2 * n + 2 - 2 * ((q + 1) / 2) + 2 ≤
          BT.size (W (2 * n + 2 - 2 * ((q + 1) / 2))) + (BT.size (W 0) + BT.size (W 1) + 4) := by
        have := size_W (2 * n + 2 - 2 * ((q + 1) / 2)); omega
      rw [replMark_W_evenN (2 * n + 2 - 2 * ((q + 1) / 2)) (by omega) _ hfuel]
      have hv : spec (2 * n + 3) (some q) = W (2 * n + 2 - 2 * ((q + 1) / 2) + 1) := by
        rw [spec_some, specM_lt (2 * n + 3) q (by omega) (by omega)]
        congr 1
        omega
      rw [hv]
      exact ⟨rfl, Sound_cons _ h3.2 (2 * n + 3) (some q) _ hv.symm⟩
    · rw [if_neg (show ¬(((q : Nat) : Int) < ((2 * n + 3 : Nat) : Int)) by omega)]
      rw [gp1_L_oddv n]
      have hv : spec (2 * n + 3) (some q) = V := by
        rw [spec_some]; exact specM_odd_ge n q (by omega)
      rw [hv]
      exact ⟨rfl, Sound_cons _ h2.2 (2 * n + 3) (some q) V hv.symm⟩

/-! ## 8. The induction along the ladder -/

theorem hit_case (f m : Nat) (req : Option Nat) (tbl : Memo) (hs : Sound tbl)
    (p : (PS × Option Int) × BT)
    (hfind : tbl.find? (fun x => x.1 == (L m, cast? req)) = some p) :
    ((runAux (f + 1) (L m) (cast? req)).run tbl).1 = spec m req ∧
    Sound ((runAux (f + 1) (L m) (cast? req)).run tbl).2 := by
  rw [runAux_hit f m (cast? req) tbl p hfind]
  exact ⟨Sound_find tbl hs m req p hfind, hs⟩

theorem zero_case (f : Nat) (req : Option Nat) (tbl : Memo) (hs : Sound tbl)
    (hfind : tbl.find? (fun p => p.1 == (L 0, cast? req)) = none) :
    ((runAux (f + 1) (L 0) (cast? req)).run tbl).1 = spec 0 req ∧
    Sound ((runAux (f + 1) (L 0) (cast? req)).run tbl).2 := by
  rw [runAux_L_zero_run, hfind]
  have hv : (BT.zero : BT) = spec 0 req := by
    rw [spec]
    unfold specM
    rw [if_pos (by rfl)]
  exact ⟨hv, Sound_cons tbl hs 0 req BT.zero hv⟩

/-- The reader on every rung of the ladder, for every mark, with any sound memo table
    and any fuel deep enough for the descent. -/
theorem runAux_L_main : ∀ (f m : Nat), m < f → ∀ (req : Option Nat) (tbl : Memo), Sound tbl →
    ((runAux f (L m) (cast? req)).run tbl).1 = spec m req ∧
    Sound ((runAux f (L m) (cast? req)).run tbl).2 := by
  intro f
  induction f with
  | zero => intro m hm; exact absurd hm (by omega)
  | succ f ih =>
    intro m hm req tbl hs
    match m, hm with
    | 0, _ =>
      cases hfind : tbl.find? (fun p => p.1 == (L 0, cast? req)) with
      | some p => exact hit_case f 0 req tbl hs p hfind
      | none => exact zero_case f req tbl hs hfind
    | 1, hm =>
      cases hfind : tbl.find? (fun p => p.1 == (L 1, cast? req)) with
      | some p => exact hit_case f 1 req tbl hs p hfind
      | none => exact step_one f req tbl hs (fun r t ht => ih 0 (by omega) r t ht) hfind
    | (k + 2), hm =>
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · obtain ⟨n, hn⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
        subst hn
        cases hfind : tbl.find? (fun p => p.1 == (L (2 * n + 2), cast? req)) with
        | some p => exact hit_case f (2 * n + 2) req tbl hs p hfind
        | none =>
          exact step_even f n req tbl hs (fun r t ht => ih (2 * n + 1) (by omega) r t ht) hfind
      · obtain ⟨n, hn⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
        subst hn
        cases hfind : tbl.find? (fun p => p.1 == (L (2 * n + 1 + 2), cast? req)) with
        | some p => exact hit_case f (2 * n + 1 + 2) req tbl hs p hfind
        | none =>
          exact step_odd f n req tbl hs (fun r t ht => ih (2 * n + 2) (by omega) r t ht) hfind

theorem m_lt_transFuel (m : Nat) : m < transFuel (L m) := by
  unfold transFuel
  rw [length_L]
  omega

theorem transPort_L (m : Nat) : transPort (L m) = spec m none := by
  have h := runAux_L_main (transFuel (L m)) m (m_lt_transFuel m) none [] Sound_nil
  rw [cast?_none] at h
  exact h.1

/-! ## 9. The target -/

theorem transPort_LBT (m : Nat) : transPort (L m) = LBT m := by
  rw [transPort_L m]
  cases m with
  | zero => rfl
  | succ k => rw [spec_pos_none (k + 1) (by omega), LBT_W k]

/-- §21.1's 24-point measurement, as a theorem for every `n`. -/
theorem transPort_rungPS (n : Nat) : transPort (rungPS n) = rungBT n :=
  transPort_rungPS_of_L transPort_LBT n

/-! ## 10. Axioms -/

end Ladder3


/-! ### §21.7 LINK 3, AND THE CHAIN IS CLOSED

    rungM 0 n --ofMatrix--> rungPS n --transPort--> rungBT n --dict--> fsEsucc 0 n
         [1] §21.3            [2] §21.6              [3] HERE

`dict_rungBT` is the last one.  All four links are now theorems for every `n`.

WHY THREE ATTEMPTS FAILED BEFORE THIS ONE.  They were looking for an UNCONDITIONAL
equational law for `collapse`, and there is none — `collapse` is a normaliser (`wcnf`, `foldl`,
`omegaNF`), so it obeys different laws on different shapes.  Measured over 14 terms spanning the
boundary, `TM.Term.le (epsN 0) x` predicts the law exactly (5 false, 9 true, zero disagreements):

    le (epsN 0) x = true   ⟹  collapse 0 (plus (Z zero) (phi zero x)) = phi zero (phi zero x)
    le (epsN 0) x = false  ⟹  it FAILS   (at zero, 1, 3, ω, ω^ω)

`collapse_step_bounded` is that law with its side conditions, and the rest is discharging them
along the family — where every argument is `≥ epsN 0` because the family starts at `epsN 0 + epsN 0`.

THE SAME MOVE AS §21.6, TWICE IN A ROW.  There the obstacle was the memo table and the answer
was to give it an invariant (`Sound`) instead of fighting it; here the obstacle is `collapse`'s
normalisation and the answer is to give it a side condition instead of demanding it hold
everywhere.  **When a normaliser refuses to satisfy an equation, ask what it preserves, not
what it equals.**

Two conjectures refuted on the way, recorded so they are not retried:

    collapse 0 (plus (collapse 1 zero) y) = phi zero y
    fsEsucc 0 (n+1) = phi zero (fsEsucc 0 n)         -- breaks at n = 0 because of `fsGen`

The induction is stated against `iterPhi` (`dict_rungBT_iterPhi`), not against `fsEsucc`; stating
it against `fsEsucc` forces a case split at 0 → 1 and an earlier attempt blew up in that branch.

AXIOMS.  All five theorems `[propext, Quot.sound]`.  No `Classical.choice`, no `native_decide`,
no `sorry`.
-/

section Link3
open Trans.Recal
open Trans.Dict
private def collapseStepInput (x : TM.Term) : TM.Term :=
  collapse 0 (TM.Term.plus (TM.Term.Z TM.Term.zero) (TM.Term.phi TM.Term.zero x))

private def collapseStepOutput (x : TM.Term) : TM.Term :=
  TM.Term.phi TM.Term.zero (TM.Term.phi TM.Term.zero x)

private def collapseStepTest (x : TM.Term) : Bool :=
  TM.Term.le (Evidence.WF.epsN 0) x &&
    (collapseStepInput x == collapseStepOutput x)

private def collapseStepCorpus : List TM.Term :=
  [ TM.Term.zero
  , TM.Term.one
  , TM.Term.ofNat 3
  , TM.Term.omega
  , TM.Term.phi TM.Term.zero TM.Term.omega
  , Evidence.WF.epsN 0
  , TM.Term.add (Evidence.WF.epsN 0) (Evidence.WF.epsN 0)
  , TM.Term.phi TM.Term.zero (Evidence.WF.epsN 0)
  , Evidence.WF.iterPhi TM.Term.zero
      (TM.Term.add (Evidence.WF.epsN 0) (Evidence.WF.epsN 0)) 3
  , TM.Term.Z TM.Term.zero
  , TM.Term.M
  , TM.Term.omg (TM.Term.Z TM.Term.zero)
  ]

#eval collapseStepCorpus.map fun x =>
  (TM.Term.le (Evidence.WF.epsN 0) x,
    collapseStepInput x == collapseStepOutput x)

#guard TM.Term.le (Evidence.WF.epsN 0) (TM.Term.Z TM.Term.zero) == true
#guard collapseStepInput (TM.Term.Z TM.Term.zero) !=
  collapseStepOutput (TM.Term.Z TM.Term.zero)

#eval (collapseStepInput (TM.Term.Z TM.Term.zero)).toStr
#eval (collapseStepOutput (TM.Term.Z TM.Term.zero)).toStr

#guard (collapseStepCorpus.take 5).all fun x =>
  !TM.Term.le (Evidence.WF.epsN 0) x &&
    !(collapseStepInput x == collapseStepOutput x)

#guard ((collapseStepCorpus.drop 5).take 4).all fun x => collapseStepTest x

#guard (collapseStepCorpus.drop 9).all fun x =>
  TM.Term.le (Evidence.WF.epsN 0) x &&
    !(collapseStepInput x == collapseStepOutput x)

theorem collapse_step_bounded (x : TM.Term)
    (hcn : Evidence.WF.CNV x = true)
    (hx : TM.Term.le (Evidence.WF.epsN 0) x = true)
    (hz : TM.Term.lt (TM.Term.phi TM.Term.zero x) (TM.Term.Z TM.Term.zero) = true) :
    collapse 0 (TM.Term.plus (TM.Term.Z TM.Term.zero) (TM.Term.phi TM.Term.zero x))
      = TM.Term.phi TM.Term.zero (TM.Term.phi TM.Term.zero x) := by
  have hx0 : x ≠ TM.Term.zero := by
    intro h
    subst x
    have hepsZero :
        TM.Term.le (Evidence.WF.epsN 0) TM.Term.zero = false := by decide
    rw [hepsZero] at hx
    exact Bool.noConfusion hx
  have hxback : TM.Term.lt x (Evidence.WF.epsN 0) = false := by
    simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with heq | hlt
    · rw [← heq]
      exact Evidence.WF.lt_irrefl _
    · exact Evidence.WF.lt_asymm
        (Evidence.WF.frag_of_cnv _ (Evidence.WF.cnv_epsN 0))
        (Evidence.WF.frag_of_cnv _ hcn) hlt
  have hphiEps :
      TM.Term.lt (TM.Term.phi TM.Term.zero x) (Evidence.WF.epsN 0) = false := by
    show TM.Term.lt (TM.Term.phi TM.Term.zero x)
      (TM.Term.phi TM.Term.one TM.Term.zero) = false
    rw [Evidence.WF.lt_phi_phi
      (by intro h; injection h with h0 _; exact TM.Term.noConfusion h0),
      if_neg (by intro h; exact TM.Term.noConfusion h), if_pos (by decide)]
    simpa [Evidence.WF.epsN] using hxback
  have hlePhiEps :
      TM.Term.le (TM.Term.phi TM.Term.zero x) (Evidence.WF.epsN 0) = false := by
    unfold TM.Term.le
    rw [hphiEps, Bool.or_false]
    exact beq_eq_false_iff_ne.mpr (by
      intro h
      change TM.Term.phi TM.Term.zero x = TM.Term.phi TM.Term.one TM.Term.zero at h
      injection h with h0 _
      exact TM.Term.noConfusion h0)
  have hlePhiZ :
      TM.Term.le (TM.Term.phi TM.Term.zero x) (TM.Term.Z TM.Term.zero) = true :=
    Evidence.WF.le_of_lt hz
  have hplus :
      TM.Term.plus (TM.Term.Z TM.Term.zero) (TM.Term.phi TM.Term.zero x) =
        TM.Term.add (TM.Term.Z TM.Term.zero) (TM.Term.phi TM.Term.zero x) := by
    unfold TM.Term.plus
    simp only [TM.Term.toList, List.filter_cons, hlePhiZ,
      if_true, List.filter_nil]
    rfl
  have hwcnf :
      wcnf (TM.Term.Z TM.Term.zero)
          [TM.Term.Z TM.Term.zero, TM.Term.phi TM.Term.zero x] =
        ([(TM.Term.one, TM.Term.one)], TM.Term.phi TM.Term.zero x) := by
    have hzz :
        TM.Term.lt (TM.Term.Z TM.Term.zero) (TM.Term.Z TM.Term.zero) = false :=
      Evidence.WF.lt_irrefl _
    have hdiv :
        divAP (TM.Term.Z TM.Term.zero) (TM.Term.Z TM.Term.zero) = TM.Term.one := by
      decide
    have htail :
        wcnf (TM.Term.Z TM.Term.zero) [TM.Term.phi TM.Term.zero x] =
          ([], TM.Term.phi TM.Term.zero x) := by
      rw [wcnf, if_pos hz]
      rfl
    rw [wcnf, if_neg (by rw [hzz]; exact Bool.noConfusion)]
    simp only [logOm, TM.Term.toList, hzz, Bool.not_false,
      if_true, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil,
      hdiv, TM.Term.ofList, htail]
    rfl
  have hplusDrop :
      TM.Term.plus (Evidence.WF.epsN 0) (TM.Term.phi TM.Term.zero x) =
        TM.Term.phi TM.Term.zero x := by
    have hlePhiEps' :
        TM.Term.le (TM.Term.phi TM.Term.zero x)
          (TM.Term.phi TM.Term.one TM.Term.zero) = false := by
      simpa [Evidence.WF.epsN] using hlePhiEps
    unfold TM.Term.plus
    simp only [Evidence.WF.epsN, TM.Term.ofNat, TM.Term.toList, List.filter_cons,
      hlePhiEps', List.filter_nil]
    rfl
  have hleZOne :
      TM.Term.le (TM.Term.Z TM.Term.zero) TM.Term.one = false := by decide
  have hsub1One : sub1 TM.Term.one = TM.Term.zero := by decide
  have hphiNFOne :
      TM.Term.phiNF TM.Term.one TM.Term.zero = Evidence.WF.epsN 0 := by decide
  have hsplit :
      TM.Term.splitFin (TM.Term.phi TM.Term.zero x) =
        (TM.Term.phi TM.Term.zero x, 0) := by
    have hneOne :
        (TM.Term.phi TM.Term.zero x == TM.Term.one) = false := by
      simp only [TM.Term.one, beq_eq_false_iff_ne]
      intro h
      injection h with _ hxz
      exact hx0 hxz
    simp [TM.Term.splitFin, TM.Term.toList, TM.Term.ofList, hneOne]
  have hphiNFArg :
      TM.Term.phiNF TM.Term.zero (TM.Term.phi TM.Term.zero x) =
        TM.Term.phi TM.Term.zero (TM.Term.phi TM.Term.zero x) := by
    unfold TM.Term.phiNF
    simp only [TM.Term.isSC, Bool.false_and, Bool.false_eq_true, if_false,
      Evidence.WF.lt_irrefl]
    unfold TM.Term.phiNFsucc
    rw [hsplit]
    unfold TM.Term.phiNFdefault
    rfl
  have homegaPhi :
      TM.Term.omegaNF (TM.Term.phi TM.Term.zero x) =
        TM.Term.phi TM.Term.zero (TM.Term.phi TM.Term.zero x) := by
    unfold TM.Term.omegaNF
    have hM :
        TM.Term.lt TM.Term.M (TM.Term.phi TM.Term.zero x) = false := by rfl
    rw [if_neg (by rw [hM]; exact Bool.noConfusion)]
    rw [if_neg (by intro h; exact TM.Term.noConfusion (beq_iff_eq.mp h))]
    exact hphiNFArg
  unfold collapse
  simp only [reg, TM.Term.ofNat, hplus, TM.Term.toList, hwcnf]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [if_neg (by rw [hleZOne]; exact Bool.noConfusion)]
  rw [if_pos (by rfl)]
  rw [hsub1One, TM.Term.plus_zero, hphiNFOne]
  change TM.Term.omegaNF
    (TM.Term.plus TM.Term.zero
      (TM.Term.plus (Evidence.WF.epsN 0) (TM.Term.phi TM.Term.zero x))) = _
  rw [hplusDrop]
  rw [show TM.Term.plus TM.Term.zero (TM.Term.phi TM.Term.zero x) =
    TM.Term.phi TM.Term.zero x from rfl]
  exact homegaPhi


theorem le_eps0_iterPhi (n : Nat) :
    TM.Term.le (Evidence.WF.epsN 0)
      (Evidence.WF.iterPhi TM.Term.zero
        (TM.Term.add (Evidence.WF.epsN 0) (Evidence.WF.epsN 0)) n) = true := by
  have hcnBase :
      Evidence.WF.CNV
        (TM.Term.add (Evidence.WF.epsN 0) (Evidence.WF.epsN 0)) = true := by
    show ((Evidence.WF.epsN 0).isAP &&
      Evidence.WF.CNV (Evidence.WF.epsN 0) &&
      Evidence.WF.CNV (Evidence.WF.epsN 0) &&
      Evidence.WF.hdLe (Evidence.WF.epsN 0) (Evidence.WF.epsN 0)) = true
    rw [Evidence.WF.cnv_epsN, Evidence.WF.hdLe_of_isAP (by rfl),
      Evidence.WF.le_self]
    rfl
  induction n with
  | zero =>
      change TM.Term.le (Evidence.WF.epsN 0)
        (TM.Term.add (Evidence.WF.epsN 0) (Evidence.WF.epsN 0)) = true
      refine Evidence.WF.le_of_lt ?_
      rw [Evidence.WF.lt_atom_add (s := Evidence.WF.epsN 0) rfl]
      exact Evidence.WF.le_self _
  | succ n ih =>
      refine Evidence.WF.le_of_lt (Evidence.WF.lt_phi_of_le
        (Evidence.WF.cnv_epsN 0)
        (Evidence.WF.cnv_iterPhi rfl hcnBase n) ih)


theorem iterPhi_step_below_Z (n : Nat) :
    TM.Term.lt
      (TM.Term.phi TM.Term.zero
        (Evidence.WF.iterPhi TM.Term.zero
          (TM.Term.add (Evidence.WF.epsN 0) (Evidence.WF.epsN 0)) n))
      (TM.Term.Z TM.Term.zero) = true := by
  let x := Evidence.WF.iterPhi TM.Term.zero
    (TM.Term.add (Evidence.WF.epsN 0) (Evidence.WF.epsN 0)) n
  have hxcn : Evidence.WF.CNV x = true := by
    have hbase :
        Evidence.WF.CNV
          (TM.Term.add (Evidence.WF.epsN 0) (Evidence.WF.epsN 0)) = true := by
      show ((Evidence.WF.epsN 0).isAP &&
        Evidence.WF.CNV (Evidence.WF.epsN 0) &&
        Evidence.WF.CNV (Evidence.WF.epsN 0) &&
        Evidence.WF.hdLe (Evidence.WF.epsN 0) (Evidence.WF.epsN 0)) = true
      rw [Evidence.WF.cnv_epsN, Evidence.WF.hdLe_of_isAP (by rfl),
        Evidence.WF.le_self]
      rfl
    exact Evidence.WF.cnv_iterPhi rfl hbase n
  have hphi :
      TM.Term.lt (TM.Term.phi TM.Term.zero x) (Evidence.WF.epsN 1) = true := by
    exact (Evidence.WF.lim_clauses_epsSucc 0).2.1 (n + 1)
  exact Evidence.WF.lt_trans_inT
    (Evidence.WF.inT_of_cnv _ (by
      show (Evidence.WF.CNV TM.Term.zero && Evidence.WF.CNV x) = true
      rw [hxcn]
      rfl))
    (Evidence.WF.inT_of_cnv _ (Evidence.WF.cnv_epsN 1))
    (by rfl) hphi (by decide)


theorem dict_rungBT_iterPhi (n : Nat) :
    Trans.Dict.dict (rungBT (n + 1)) =
      Evidence.WF.iterPhi TM.Term.zero
        (TM.Term.add (Evidence.WF.epsN 0) (Evidence.WF.epsN 0)) (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [rungBT, Trans.Dict.dict_D, Trans.Dict.dict_sum,
        Trans.Dict.dict_D, Trans.Dict.dict_zero]
      rw [show collapse 1 TM.Term.zero = TM.Term.Z TM.Term.zero from by decide]
      rw [ih]
      change collapse 0
        (TM.Term.plus (TM.Term.Z TM.Term.zero)
          (TM.Term.phi TM.Term.zero
            (Evidence.WF.iterPhi TM.Term.zero
              (TM.Term.add (Evidence.WF.epsN 0) (Evidence.WF.epsN 0)) n))) =
        TM.Term.phi TM.Term.zero
          (TM.Term.phi TM.Term.zero
            (Evidence.WF.iterPhi TM.Term.zero
              (TM.Term.add (Evidence.WF.epsN 0) (Evidence.WF.epsN 0)) n))
      have hbase :
          Evidence.WF.CNV
            (TM.Term.add (Evidence.WF.epsN 0) (Evidence.WF.epsN 0)) = true := by
        show ((Evidence.WF.epsN 0).isAP &&
          Evidence.WF.CNV (Evidence.WF.epsN 0) &&
          Evidence.WF.CNV (Evidence.WF.epsN 0) &&
          Evidence.WF.hdLe (Evidence.WF.epsN 0) (Evidence.WF.epsN 0)) = true
        rw [Evidence.WF.cnv_epsN, Evidence.WF.hdLe_of_isAP (by rfl),
          Evidence.WF.le_self]
        rfl
      have hcnIter :
          Evidence.WF.CNV
            (Evidence.WF.iterPhi TM.Term.zero
              (TM.Term.add (Evidence.WF.epsN 0) (Evidence.WF.epsN 0)) n) = true :=
        Evidence.WF.cnv_iterPhi (u := TM.Term.zero)
          (base := TM.Term.add (Evidence.WF.epsN 0) (Evidence.WF.epsN 0))
          rfl hbase n
      exact collapse_step_bounded
        (Evidence.WF.iterPhi TM.Term.zero
          (TM.Term.add (Evidence.WF.epsN 0) (Evidence.WF.epsN 0)) n)
        hcnIter (le_eps0_iterPhi n) (iterPhi_step_below_Z n)


theorem dict_rungBT (n : Nat) :
    Trans.Dict.dict (rungBT n) = Evidence.WF.fsEsucc 0 n := by
  cases n with
  | zero => decide
  | succ n =>
      exact dict_rungBT_iterPhi n

end Link3


/-! ### §21.8 THE CHAIN, COMPOSED — §21.1's measurement is now a theorem

    Trans.oR (rungM 0 n) = some (fsEsucc 0 n)     for every n

§21.1 carried this as a 24-point `#guard` and said what blocked it: `Trans/Recal.lean` had
174 `#guard`s and ZERO theorems, so no `∀ n` fact about the reader was provable at all.  That
was a missing LAYER, not a gap in a proof.  The layer now exists, and this is the first
statement quantified over an infinite family that the reader satisfies as a theorem.

The four links (§21.3 `ofMatrix_rungM_zero`, §21.6 `transPort_rungPS`, §21.7 `dict_rungBT`)
compose here.  Two small facts were still needed and are proved above:

  * `rungM_ne_empty` — to take `oR`'s non-empty branch (axiom-free);
  * `one_plus_fsEsucc` — `oR` prepends `1 +`, and it is ABSORBED on this family.
    `one_plus_phi` is the general form: `plus one (phi a b) = phi a b` whenever
    `le (phi a b) one = false`, which holds here because every value is at least ε₀
    (`fsEsucc_not_le_one`).

WHAT THIS DOES **NOT** DO.  It puts no ✅ on any row.  ✅ comes from `Certified`, which never
mentions a reader — that separation is the calibration accident's doctrine and it is
deliberate.  What this buys is evidence about the INSTRUMENT: 23 of the table's 51 rows carry
values that exist only because `oR` produced them, and until now `oR` was backed by
measurement at points and nothing else.  One infinite family is now backed by a proof.

AXIOMS.  `[propext, Quot.sound]` or less throughout; `rungM_ne_empty` depends on no axiom at
all.  No `Classical.choice`, no `native_decide`, no `sorry`.
-/

section Composed
open Trans.Recal
open Trans.Dict
theorem one_plus_phi (a b : TM.Term)
    (h : TM.Term.le (TM.Term.phi a b) TM.Term.one = false) :
    TM.Term.plus TM.Term.one (TM.Term.phi a b) = TM.Term.phi a b := by
  unfold TM.Term.plus
  change TM.Term.ofList
    (([TM.Term.one].filter (fun x => TM.Term.le (TM.Term.phi a b) x)) ++
      [TM.Term.phi a b]) = TM.Term.phi a b
  rw [List.filter_cons_of_neg (by
    intro ht
    rw [h] at ht
    exact Bool.noConfusion ht)]
  rfl

#guard TM.Term.plus TM.Term.one (TM.Term.phi TM.Term.zero TM.Term.one) ==
  TM.Term.phi TM.Term.zero TM.Term.one

theorem fsEsucc_not_le_one (n : Nat) :
    TM.Term.le (Evidence.WF.fsEsucc 0 n) TM.Term.one = false := by
  cases n with
  | zero => decide
  | succ n =>
      apply le_pow_one_false
      intro hzero
      have hle := le_eps0_iterPhi n
      rw [hzero] at hle
      exact Bool.noConfusion hle

#guard (List.range 8).all fun n =>
  TM.Term.le (Evidence.WF.fsEsucc 0 n) TM.Term.one == false

theorem one_plus_fsEsucc (n : Nat) :
    TM.Term.plus TM.Term.one (Evidence.WF.fsEsucc 0 n) =
      Evidence.WF.fsEsucc 0 n := by
  cases n with
  | zero =>
      exact one_plus_phi TM.Term.one TM.Term.zero (fsEsucc_not_le_one 0)
  | succ n =>
      exact one_plus_phi TM.Term.zero
        (Evidence.WF.iterPhi TM.Term.zero
          (TM.Term.add (Evidence.WF.epsN 0) (Evidence.WF.epsN 0)) n)
        (fsEsucc_not_le_one (n + 1))

#guard (List.range 8).all fun n =>
  TM.Term.plus TM.Term.one (Evidence.WF.fsEsucc 0 n) == Evidence.WF.fsEsucc 0 n

theorem rungM_ne_empty (n : Nat) : (rungM 0 n).isEmpty = false := by
  rfl

#guard (List.range 6).all fun n => (rungM 0 n).isEmpty == false

theorem oR_rungM_zero (n : Nat) :
    Trans.oR (rungM 0 n) = some (Evidence.WF.fsEsucc 0 n) := by
  unfold Trans.oR Trans.Recal.oR
  rw [if_neg (by
    intro h
    rw [rungM_ne_empty] at h
    exact Bool.noConfusion h)]
  unfold Trans.Recal.oRB
  rw [ofMatrix_rungM_zero]
  change some (TM.Term.plus TM.Term.one
    (Trans.Dict.dict (Trans.Recal.transPort (rungPS n)))) =
      some (Evidence.WF.fsEsucc 0 n)
  rw [transPort_rungPS, dict_rungBT, one_plus_fsEsucc]

#guard (List.range 24).all fun n =>
  Trans.oR (rungM 0 n) == some (Evidence.WF.fsEsucc 0 n)

end Composed

/-! ## §23 THE REGION RECURSION — one certificate for a FAMILY, not one per row

§16 priced the twelve Veblen-region rows and concluded that the obstacle "is not a missing
lemma, it is a missing REGION".  This section supplies the region's SHAPE.  §13's
`certIn_sq` already had it, written by hand for the CNF one-row family; `certIn_region`
below is that proof with the family and the valuation made parameters, so a new family
costs its three supplies and nothing else.

WHAT A CALLER OWES.  A predicate `Reg` on matrices closed under `BMS.expand`, a valuation
`Val`, and one supply per kind:

    zero   the value of a kind-zero matrix is `0`
    succ   the value is `u ⊕ 1`, every expansion has value `u`, and `u < t` in 𝔗(M)
    lim    a sequence `f` with `Val (S[n]) (f n)` and the four `Certified.lim` clauses

THE RECURSION IS ON THE VALUE, NOT ON THE MATRIX.  §15.25's `acc_cnv_inT` gives
`Acc RT t` for every `CNV` term, and `RT x y = inT x ∧ lt x y` is exactly the obligation
each supply already discharges.  Two arithmetic measures died on this file's own recursion
(`deg` at `omLog`, `tdepth` at `predOr`); the order needs no arithmetic at all.

WHAT IS STILL OWED, AND IT IS ONE THING.  The `lim` supply's fourth clause — cofinality of
the ROW'S OWN sequence.  `Evidence/WF.lean` §15.39's `limClauses_transfer` reduces it to a
DOMINATION against any sequence the WF file already handles, and §15.38's `asm_generalB'`
supplies those for the whole Veblen fragment once its `Hsucc` hypothesis is discharged.

MEASUREMENTS THAT SCOPE IT (2026-08-15, over `Rows.selected`; run from a snippet importing
`Rows.G10`, which cannot be done from this file):

    23  selected rows, ALL of kind `lim`                     — no successor row is selected
    16  have a `CNV` value            7 do not (the ψ/Z rows) — those need Stage 3b
     0  rows whose expansion closure (depth 2) leaves `oR` undefined
     0  rows whose expansion values fail to be strictly increasing and below the value

and on the ε₁ row specifically, `oR (expand [[0,0],[1,1],[1,1]] n) = some (fsE1 n)` AT
SHIFT 0 — so `lim_clauses_eps1` is already the row's own sequence and its `hdom` is
`le_self`.  `fsN` matches that row at no shift, which is why the transfer exists.

**NO SELECTED ROW IS ONE STEP FROM THE CERTIFIED REGION** (2026-08-15), which is §16's
finding with a number on it.  Testing each selected row's four depth-1 expansions for the
shape `padRow (sq t)` with `CN t` — the region §10–§13 certify:

    ε₀ row            0 of 4 outside      (and it is already registered)
    every other row   4 of 4 outside

So the gate is not one lemma away for any row, and `certIn_region` cannot be instantiated
by reusing `certIn_sq`'s family.  What a row needs is ITS OWN `Reg`: a family of matrices
closed under `BMS.expand` with a closed description, which is the same kind of object the
`G`-family ladders are on the reader side.  §16 called this a missing REGION; the number
above says how far away it is.

A SEPARATE MEASUREMENT, worth recording because §15.3 refuted the natural guess for a
DIFFERENT function: over a 121-term corpus of `CNV` limits built from the row values, their
subterms and their `fsN` iterates (100 `φ̄`-shaped, 21 `⊕`-shaped), `TM.fsN` is `CNV`,
strictly below, and strictly increasing with **0 violations** to `n ≤ 6`.  §15.3's
counterexample is to a hand-rolled `fsV`, not to `fsN`. -/

open Evidence.WF (RT acc_cnv_inT cnv_of_cn cn_predC lt_predC cn_fsC lim_clauses inT_of_cnv)

/-- 種別 0 の行列は空行列だけ。`CertifiedIn.zero` が `[]` を要求するので要る。 -/
theorem eq_nil_of_kind_zero (S : Matrix) (h : BMS.kind S = .zero) : S = [] := by
  cases hs : S.getLast? with
  | none =>
    cases hS : S with
    | nil => rfl
    | cons a l =>
      rw [hS] at hs
      simp at hs
  | some L =>
    exfalso
    have h' : BMS.kind S
        = (match BMS.lnz L with
           | none => BMS.Kind.succ
           | some _ => BMS.Kind.lim) := by
      show (match S.getLast? with
        | none => BMS.Kind.zero
        | some L => match BMS.lnz L with
          | none => BMS.Kind.succ
          | some _ => BMS.Kind.lim) = _
      rw [hs]
    rw [h'] at h
    cases hL : BMS.lnz L with
    | none => rw [hL] at h; exact BMS.Kind.noConfusion h
    | some _ => rw [hL] at h; exact BMS.Kind.noConfusion h

/-- **領域の再帰。** `Reg` は展開で閉じた行列の族、`Val` はその上の値付け。種別ごとの
    供給を与えると、族のすべての行列が **ゲートと同じ `DomI` 付きの** 証明書を持つ。 -/
theorem certIn_region {Reg : Matrix → Prop} {Val : Matrix → Term → Prop}
    (Hclosed : ∀ S, Reg S → ∀ n, Reg (BMS.expand S n))
    (Hzero : ∀ S t, Reg S → Val S t → BMS.kind S = .zero → t = TM.Term.zero)
    (Hsucc : ∀ S t, Reg S → Val S t → BMS.kind S = .succ →
        ∃ u, t = plus u TM.Term.one ∧ inT t = true ∧ inT u = true ∧ lt u t = true
             ∧ ∀ n, Val (BMS.expand S n) u)
    (Hlim : ∀ S t, Reg S → Val S t → BMS.kind S = .lim →
        ∃ f : Nat → Term, inT t = true
          ∧ (∀ n, Val (BMS.expand S n) (f n))
          ∧ (∀ n, inT (f n) = true)
          ∧ (∀ n, lt (f n) t = true)
          ∧ (∀ n, lt (f n) (f (n+1)) = true)
          ∧ (∀ s, inT s = true → lt s t = true → ∃ n, le s (f n) = true)) :
    ∀ t, Acc RT t → ∀ S, Reg S → Val S t → CertifiedIn DomI S t := by
  intro t ht
  induction ht with
  | intro t _ ih =>
    intro S hreg hval
    cases hk : BMS.kind S with
    | zero =>
      have hS : S = [] := eq_nil_of_kind_zero S hk
      have h0 : t = TM.Term.zero := Hzero S t hreg hval hk
      rw [hS, h0]
      exact CertifiedIn.zero
    | succ =>
      obtain ⟨u, hu, hint, hinu, hltu, hexp⟩ := Hsucc S t hreg hval hk
      subst hu
      exact CertifiedIn.succ hk
        (fun n => ih u ⟨hinu, hltu⟩ (BMS.expand S n) (Hclosed S hreg n) (hexp n)) hint
    | lim =>
      obtain ⟨f, hint, hexp, hinf, hltf, hstep, hcof⟩ := Hlim S t hreg hval hk
      exact CertifiedIn.lim f hk
        (fun n => ih (f n) ⟨hinf n, hltf n⟩ (BMS.expand S n) (Hclosed S hreg n) (hexp n))
        hltf hstep hcof hint

/-- 値が `CNV` なら停止性は `Evidence/WF.lean` §15.1 から来る。 -/
theorem certIn_region_cnv {Reg : Matrix → Prop} {Val : Matrix → Term → Prop}
    (Hclosed : ∀ S, Reg S → ∀ n, Reg (BMS.expand S n))
    (Hzero : ∀ S t, Reg S → Val S t → BMS.kind S = .zero → t = TM.Term.zero)
    (Hsucc : ∀ S t, Reg S → Val S t → BMS.kind S = .succ →
        ∃ u, t = plus u TM.Term.one ∧ inT t = true ∧ inT u = true ∧ lt u t = true
             ∧ ∀ n, Val (BMS.expand S n) u)
    (Hlim : ∀ S t, Reg S → Val S t → BMS.kind S = .lim →
        ∃ f : Nat → Term, inT t = true
          ∧ (∀ n, Val (BMS.expand S n) (f n))
          ∧ (∀ n, inT (f n) = true)
          ∧ (∀ n, lt (f n) t = true)
          ∧ (∀ n, lt (f n) (f (n+1)) = true)
          ∧ (∀ s, inT s = true → lt s t = true → ∃ n, le s (f n) = true)) :
    ∀ t, CNV t = true → ∀ S, Reg S → Val S t → CertifiedIn DomI S t :=
  fun t hcnv => certIn_region Hclosed Hzero Hsucc Hlim t (acc_cnv_inT t hcnv)

/-! ### §23.1 THE CONSUMER — §13's `certIn_sq`, rebuilt as ONE INSTANCE

A theorem whose hypotheses cannot be met compiles exactly like a useful one; `Evidence/WF.lean`
§15.37 records three of this repo's own that did, for weeks.  So the abstraction is applied
to a family that exists.  `certIn_sq_via_region` runs all three branches and lands on `DomI`
directly, where §13's version lands on `DomF` and needs `certifiedIn_mono` afterwards. -/

/-- CNF 一行行列の族。 -/
def RegSq (S : Matrix) : Prop := ∃ t, CN t = true ∧ S = Evidence.StageA.oneRow (sq t)
/-- その上の値付け。 -/
def ValSq (S : Matrix) (t : Term) : Prop := CN t = true ∧ S = Evidence.StageA.oneRow (sq t)

theorem eq_zero_of_beq {u : Term} (h : (u == TM.Term.zero) = true) : u = TM.Term.zero :=
  eq_of_beq h

theorem ne_zero_of_beq {u : Term} (h : (u == TM.Term.zero) = false) : u ≠ TM.Term.zero := by
  intro hc; subst hc; exact Bool.noConfusion h

theorem regSq_closed : ∀ S, RegSq S → ∀ n, RegSq (BMS.expand S n) := by
  rintro S ⟨t, hcn, rfl⟩ n
  cases hbz : (t == TM.Term.zero) with
  | true =>
    have hz : t = TM.Term.zero := eq_zero_of_beq hbz
    subst hz
    exact ⟨TM.Term.zero, rfl, by rfl⟩
  | false =>
    have hz : t ≠ TM.Term.zero := ne_zero_of_beq hbz
    cases hk : kindC t with
    | true =>
      refine ⟨predC t, cn_predC t hcn hk, ?_⟩
      show (BMS.expand? (Evidence.StageA.oneRow (sq t)) n).getD [] = _
      rw [expand_sq_succ t hcn hk n]
      rfl
    | false =>
      refine ⟨fsC t n, cn_fsC t hcn hk hz n, ?_⟩
      show (BMS.expand? (Evidence.StageA.oneRow (sq t)) n).getD [] = _
      rw [expand_sq t hcn hk hz n]
      rfl

/-- 空行列の種別は 0 なので、`sq 0` の行は後続でも極限でもない。 -/
theorem kind_sq_zero :
    BMS.kind (Evidence.StageA.oneRow (sq TM.Term.zero)) = BMS.Kind.zero := rfl

/-- **消費者。** §13 の `certIn_sq` を `certIn_region` の 1 つの実例として作り直す。 -/
theorem certIn_sq_via_region : ∀ (t : Term), CN t = true →
    CertifiedIn DomI (Evidence.StageA.oneRow (sq t)) t := by
  intro t hcn
  refine certIn_region_cnv (Val := ValSq) regSq_closed ?_ ?_ ?_ t (cnv_of_cn t hcn)
    (Evidence.StageA.oneRow (sq t)) ⟨t, hcn, rfl⟩ ⟨hcn, rfl⟩
  · rintro S u _ ⟨hcnu, rfl⟩ hk
    cases hbz : (u == TM.Term.zero) with
    | true => exact eq_zero_of_beq hbz
    | false =>
      exfalso
      have hz : u ≠ TM.Term.zero := ne_zero_of_beq hbz
      cases hku : kindC u with
      | true => rw [kind_sq_succ u hcnu hku] at hk; exact BMS.Kind.noConfusion hk
      | false => rw [kind_sq_lim u hcnu hku hz] at hk; exact BMS.Kind.noConfusion hk
  · rintro S u _ ⟨hcnu, rfl⟩ hk
    cases hbz : (u == TM.Term.zero) with
    | true =>
      exfalso
      have hz : u = TM.Term.zero := eq_zero_of_beq hbz
      subst hz
      rw [kind_sq_zero] at hk
      exact BMS.Kind.noConfusion hk
    | false =>
      have hz : u ≠ TM.Term.zero := ne_zero_of_beq hbz
      cases hku : kindC u with
      | true =>
        refine ⟨predC u, (plus_predC u hcnu hku).symm, inT_of_cn _ hcnu,
          inT_of_cn _ (cn_predC u hcnu hku), lt_predC u hcnu hku, fun n => ?_⟩
        refine ⟨cn_predC u hcnu hku, ?_⟩
        show (BMS.expand? (Evidence.StageA.oneRow (sq u)) n).getD [] = _
        rw [expand_sq_succ u hcnu hku n]
        rfl
      | false =>
        exfalso
        rw [kind_sq_lim u hcnu hku hz] at hk
        exact BMS.Kind.noConfusion hk
  · rintro S u _ ⟨hcnu, rfl⟩ hk
    cases hbz : (u == TM.Term.zero) with
    | true =>
      exfalso
      have hz : u = TM.Term.zero := eq_zero_of_beq hbz
      subst hz
      rw [kind_sq_zero] at hk
      exact BMS.Kind.noConfusion hk
    | false =>
      have hz : u ≠ TM.Term.zero := ne_zero_of_beq hbz
      cases hku : kindC u with
      | true =>
        exfalso
        rw [kind_sq_succ u hcnu hku] at hk
        exact BMS.Kind.noConfusion hk
      | false =>
        obtain ⟨hcnfs, hltfs, hstep, hcof⟩ := lim_clauses u hcnu hku hz
        exact ⟨fsC u, inT_of_cn _ hcnu,
          (fun n => ⟨cn_fsC u hcnu hku hz n, by
            show (BMS.expand? (Evidence.StageA.oneRow (sq u)) n).getD [] = _
            rw [expand_sq u hcnu hku hz n]
            rfl⟩),
          (fun n => inT_of_cn _ (cn_fsC u hcnu hku hz n)), hltfs, hstep, hcof⟩

end Evidence.Cert
