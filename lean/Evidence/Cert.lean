import Trans.TM
import TM.FS
import Evidence.StageA
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
and the target notation's own correctness ([R91]), exactly as the plan's
conditional main theorem MT always stated.

The table's proof column is driven by `certRows` + `certRows_ok`: gentable marks
a row exactly when its (matrix, term) pair is registered here, and the single
theorem `certRows_ok` forces every registered pair to carry a derivation.
Labels are computed from certificates, never declared.

DEFINITION CHANGE (2026-08-09, certificate lane).  The cofinality premise now
reads `∀ s, inT s = true → lt s t = true → ∃ n, le s (fs' n) = true`: the
quantifier ranges over the TERMS OF 𝔗(M) ([R91] 2.1, the predicate `inT` of
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

/-! ### Destructuring the formation conditions `inT` ([R91] 2.1) -/

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

Two general clauses of [R91] 2.3 do all the work below: a sum is compared with a
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

/-! ### The route from here to ω^ω (design note, nothing proved below)

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

WHAT REMAINS, in dependency order:

  1. Shape lemmas for `wv`/`wvSeq` (the analogues of `wm_cons`, `wm_zero_k`,
     `deg_wm`, `plus_wm_one`).  §5's are the template; expect this to be the
     bulk of the line count.
  2. The expansion lemmas, prefix-relative, over `StageA.expand_oneRow`:
     successor step (drop a unit) and limit step at level j>0 (one `ω^j` becomes
     `n+1` copies of `ω^(j-1)`).  `expand_wmM_lim` is the template.
  3. The classification `below_wv` at level k — the analogue of `below_wm`,
     recursion on the fuel with the level as a parameter.  §5's
     `ltF_ofList_head`/`ltF_ofList_prefix` already cover every order comparison
     needed and are stated for arbitrary sums, so no new order theory is
     required.
  4. `cert_wv : ∀ cs, Certified (wvM cs) (wv cs)`.  Two routes, both open:
     the prefix induction of the note above (no `Acc`), or termination by
     `Evidence.WF.lexLt_at` + `Evidence.WF.lexLt_wf` (`open Evidence.WF` — the
     `WellFoundedRelation` instance there is `scoped` on purpose).  The vector
     route is the shorter statement now that WF.lean exists.
  5. `cert_omega_pow : Certified [[0],[1],[2]] (phi zero omega)` as the limit
     over `cert_wv [1,0,…,0]`.

NOT covered by this layer: the row `(0)(1)(2)(3)` (ω^(ω^ω)).  Its expansions are
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

/-! ## §6 The registry

gentable marks ✅ exactly on the rows listed here; `certRows_ok` is the gate. -/

/-- The registered certified rows. -/
def certRows : List (Matrix × Term) :=
  [([], Term.zero), ([[0]], one), ([[0], [0]], ofNat 2), ([[0], [1]], omega),
   ([[0], [1], [0], [1]], add omega omega), ([[0], [1], [1]], phi zero (ofNat 2))]

/-- Every registered pair carries a derivation.  Extending `certRows` without
    extending this proof breaks the build — the label cannot outrun the
    certificates. -/
theorem certRows_ok : ∀ p ∈ certRows, Certified p.1 p.2 := by
  intro p hp
  simp only [certRows, List.mem_cons] at hp
  rcases hp with h | h | h | h | h | h | h
  · rw [h]; exact cert_empty
  · rw [h]; exact cert_one
  · rw [h]; exact cert_two
  · rw [h]; exact cert_omega
  · rw [h]; exact cert_omega2
  · rw [h]; exact cert_omega_sq
  · cases h

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

end Evidence.Cert
