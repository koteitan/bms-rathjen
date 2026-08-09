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
  eventually above every junk head.  (Checked by `#guard` in §5.)

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

/-! ## §4 The registry

gentable marks ✅ exactly on the rows listed here; `certRows_ok` is the gate. -/

/-- The registered certified rows. -/
def certRows : List (Matrix × Term) :=
  [([], Term.zero), ([[0]], one), ([[0], [0]], ofNat 2), ([[0], [1]], omega)]

/-- Every registered pair carries a derivation.  Extending `certRows` without
    extending this proof breaks the build — the label cannot outrun the
    certificates. -/
theorem certRows_ok : ∀ p ∈ certRows, Certified p.1 p.2 := by
  intro p hp
  simp only [certRows, List.mem_cons] at hp
  rcases hp with h | h | h | h | h
  · rw [h]; exact cert_empty
  · rw [h]; exact cert_one
  · rw [h]; exact cert_two
  · rw [h]; exact cert_omega
  · cases h

/-! ## §5 The junk-term computations behind the DEFINITION CHANGE

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
