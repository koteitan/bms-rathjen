import Rows.TM
import Evidence.StageA
/-
Rows/ProofsB.lean — per-row proofs for the Stage B fragment (Trans/Pair.lean)

(The imports are on the first lines: the kimina server mis-splits a snippet whose
`import` is preceded by a comment.)

Beyond ε₀ the BM4 expansion of a matrix and the fundamental sequence of its term
are in general DIFFERENT cofinal sequences of the same ordinal, so E3 cannot be an
equality of sequences.  The claim proved per row is the mutual-cofinality form of
plan/README.md, with explicit witness functions:

  (a) ∀ n, o?(M[n]) = some (oval n)   and   ∀ n, lt (oval n) t
  (b) ∀ n, lt (oval n) (fsN t (kw n))          -- the expansions are overtaken by the fs
  (c) ∀ k, lt (fsN t (k+1)) (oval (nw k))      -- the fs is overtaken by the expansions

packaged per row as the single theorem `e3` (§10, §13–§18).

ALL NINE STAGE-B ROWS OF Rows/TM.lean ARE PROVED:

  §  ns  matrix                  term            oval n              kw n   nw k
  ---------------------------------------------------------------------------------
  §8  R1 (0,0)(1,1)              φ̄(1,0) = ε₀     fsN t (n+1)         n+2    k+1
  §15 R2 (0,0)(1,1)(1,0)         φ̄(0,ε₀)         fsN t (n+1)         n+2    k+1
  §17 R3 (0,0)(1,1)(1,1)         φ̄(1,1) = ε₁     ε₀ / towP0 (n-1)    n+1    k+1
  §13 R4 (0,0)(1,1)(2,0)         φ̄(1,ω) = ε_ω    fsN t n             n+1    k+2
  §9  R5 (0,0)(1,1)(2,0)(3,1)    φ̄(1,ε₀)         fsN t (n+2)         n+3    k
  §6  R6 (0,0)(1,1)(2,1)         φ̄(2,0) = ζ₀     fsN t (n+1)         n+2    k+1
  §18 R7 (0,0)(1,1)(2,1)(2,1)    φ̄(2,1) = ζ₁     ζ₀ / etowR0 (n-1)   n+1    k+1
  §14 R8 (0,0)(1,1)(2,1)(3,0)    φ̄(2,ω) = ζ_ω    fsN t n             n+1    k+2
  §7  R9 (0,0)(1,1)(2,1)(3,1)    φ̄(3,0)          fsN t (n+1)         n+2    k+1

FINDING (recorded in v0.1.10 and now proved for every row): the index shift of the
repository convention (`o(M[n]) ↔ t[n+1]`) is NOT uniform on Stage B.  R5 runs two
steps ahead; R4 and R8 run one step BEHIND (`o(M[n]) = t[n]`); and R3 and R7 are the
two rows where the expansion and the fundamental sequence are genuinely different
cofinal sequences, so no shift makes them equal (§19 checks this by computation):

  R3: expansions are the ω-tower over ω^{ε₀·2}, the fs is the ω-tower over ω^{ε₀+1};
  R7: expansions are the ε-tower over φ̄(1,ω^{ζ₀·2}), the fs is the ε-tower over φ̄(1,ζ₀).

Method.  §1–§2 give order tools for the fuelled decision procedure `ltF` and the
`φ_a`-iteration families `iterT a m`.  §3 unfolds `oLAux` on single-block column
sequences.  §4 puts a BM4 expansion `((List.range (n+1)).map bad).flatten` into the
front-recursive form `frep`, the direction in which `oLAux` recurses.  §5 computes
`fsN (φ̄ a 0)`.  §12 handles a run of `(0,1)` columns: `blocksP` gives one block per
column and `oLAux` folds `phiStep`, whose value at level k is `φ̄(k, m)`; this needs
`toList (ofNat n) = replicate n 1`, `splitFin (ofNat n) = (0,n)` and `logPhi` on
`φ̄(k, ofNat i)`.  §16 gives the ω-tower over a fixed base used by R3 (and R7 has its
ε-tower analogue inside its namespace).

References: [Rathjen, 1991] = M. Rathjen, "Proof-theoretic analysis of KPM", Arch. Math.
Logic 30 (1991) 377–403.
-/

namespace Rows.ProofsB

open BMS (Matrix)
open TM (Term)
open TM.Term
open Trans

/-! ## §1 Tools for the decidable order of 𝔗(M)

`lt` is `ltF` at a fixed amount of fuel, so every order lemma about a family of
terms is proved in the form "for every sufficiently large fuel"; the final `lt`
statement then follows from a degree bound. -/

theorem ltF_irrefl (f : Nat) (x : Term) : ltF f x x = false := by
  cases f with
  | zero => rfl
  | succ g =>
    show (if (x == x) = true then false else _) = false
    simp

theorem ne_of_ltF {f : Nat} {x y : Term} (h : ltF f x y = true) : x ≠ y := by
  intro hc
  subst hc
  rw [ltF_irrefl] at h
  exact Bool.noConfusion h

theorem ltF_zero {f : Nat} (hf : 1 ≤ f) {t : Term} (h : t ≠ zero) : ltF f zero t = true := by
  cases f with
  | zero => omega
  | succ g => cases t <;> first | (exact absurd rfl h) | rfl

theorem ltF_phi_same {f : Nat} {a x y : Term} (h : ltF f x y = true) :
    ltF (f + 1) (phi a x) (phi a y) = true := by
  have hne : (phi a x == phi a y) = false := by
    simp [ne_of_ltF h]
  show (if (phi a x == phi a y) = true then false else _) = true
  rw [hne]
  simp only [Bool.false_eq_true, if_false]
  show (if (a == a) = true then ltF f x y else _) = true
  simp [h]

theorem ltF_phi_fst {f : Nat} {a c x d : Term} (hac : (a == c) = false)
    (h1 : ltF f a c = true) (h2 : ltF f x (phi c d) = true) :
    ltF (f + 1) (phi a x) (phi c d) = true := by
  have hac' : a ≠ c := by simpa using hac
  have hne : (phi a x == phi c d) = false := by simp [hac']
  show (if (phi a x == phi c d) = true then false else _) = true
  rw [hne]
  simp only [Bool.false_eq_true, if_false]
  show (if (a == c) = true then _ else if ltF f a c = true then ltF f x (phi c d) else _) = true
  rw [hac]
  simp only [Bool.false_eq_true, if_false]
  rw [h1]
  simp [h2]

theorem lt_irrefl (a : Term) : lt a a = false := ltF_irrefl _ a

/-! ## §2 The `φ̄`-iteration families

`iterT a m` is the m-fold iterate of `φ_a` at 0: `0, φ̄a0, φ̄a(φ̄a0), …`.  For
`a = 0, 1, 2` these are the ω-, ε- and ζ-towers that both sides of E3 climb. -/

theorem phiNFdefault_phi {a x : Term} (ha : a.isSC = false) : phiNFdefault a x = phi a x := by
  unfold phiNFdefault
  rw [ha]
  simp

theorem phiNF_zero_arg {a : Term} (ha : a.isSC = false) : phiNF a zero = phi a zero := by
  have h : phiNF a zero = phiNFdefault a zero := rfl
  rw [h, phiNFdefault_phi ha]

theorem ltF_lt_zero (f : Nat) (a : Term) : ltF f a zero = false := by
  cases f with
  | zero => rfl
  | succ g => cases a <;> rfl

theorem lt_lt_zero (a : Term) : lt a zero = false := ltF_lt_zero _ a

theorem phiNF_one_arg {a : Term} (ha : a.isSC = false) : phiNF a one = phi a one := by
  show phiNF a (phi zero zero) = phi a (phi zero zero)
  unfold phiNF
  simp only [isSC, Bool.false_and, Bool.false_eq_true, if_false, lt_lt_zero]
  unfold phiNFsucc
  rw [show splitFin (phi zero zero : Term) = (zero, 1) from rfl]
  show (if ((zero : Term).isSC && lt a zero) = true then phi a (plus zero (ofNat 0))
        else phiNFdefault a (phi zero zero)) = phi a (phi zero zero)
  simp only [isSC, Bool.false_and, Bool.false_eq_true, if_false]
  exact phiNFdefault_phi ha

/-- On the terms occurring here `phiNF` is the raw constructor: `φ_a(φ̄cx) = φ̄a(φ̄cx)`
    as soon as `φ̄cx` is not a `φ_a`-fixed point (`¬ a < c`). -/
theorem phiNF_phi_gen {a c z : Term} (ha : a.isSC = false) (hac : lt a c = false) :
    phiNF a (phi c z) = phi a (phi c z) := by
  by_cases hone : (phi c z == one) = true
  · have h1 : c = zero ∧ z = zero := by simpa [one] using hone
    obtain ⟨hc0, hz0⟩ := h1
    subst hc0; subst hz0
    exact phiNF_one_arg ha
  · have hone' : (phi c z == one) = false := by simpa using hone
    have hsp : splitFin (phi c z) = (phi c z, 0) := by
      simp [splitFin, toList, ofList, hone']
    unfold phiNF
    simp only [isSC, Bool.false_and, Bool.false_eq_true, if_false, hac]
    unfold phiNFsucc
    rw [hsp]
    show phiNFdefault a (phi c z) = phi a (phi c z)
    exact phiNFdefault_phi ha

theorem phiNF_phi_arg {a z : Term} (ha : a.isSC = false) :
    phiNF a (phi a z) = phi a (phi a z) := phiNF_phi_gen ha (lt_irrefl a)

/-- The `m`-fold iterate of `φ_a` at 0. -/
def iterT (a : Term) : Nat → Term
  | 0 => zero
  | m + 1 => phiNF a (iterT a m)

theorem iterT_succ {a : Term} (ha : a.isSC = false) : ∀ m, iterT a (m + 1) = phi a (iterT a m)
  | 0 => phiNF_zero_arg ha
  | m + 1 => by
    show phiNF a (iterT a (m + 1)) = phi a (iterT a (m + 1))
    rw [iterT_succ ha m]
    exact phiNF_phi_arg ha

theorem iterT_ne_zero {a : Term} (ha : a.isSC = false) (m : Nat) : iterT a (m + 1) ≠ zero := by
  rw [iterT_succ ha]; intro hc; exact Term.noConfusion hc

theorem deg_iterT {a : Term} (ha : a.isSC = false) : ∀ m, m ≤ (iterT a m).deg
  | 0 => by simp [iterT, deg]
  | m + 1 => by
    rw [iterT_succ ha]
    show m + 1 ≤ 1 + a.deg + (iterT a m).deg
    have := deg_iterT ha m
    omega

theorem ltF_iterT_succ {a : Term} (ha : a.isSC = false) :
    ∀ (m f : Nat), m + 1 ≤ f → ltF f (iterT a m) (iterT a (m + 1)) = true
  | 0, f, hf => by
    rw [iterT_succ ha]
    exact ltF_zero (by omega) (by intro hh; exact Term.noConfusion hh)
  | m + 1, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      have ih := ltF_iterT_succ ha m g (by omega)
      rw [iterT_succ ha (m + 1), iterT_succ ha m]
      rw [iterT_succ ha m] at ih
      exact ltF_phi_same ih

theorem lt_iterT_succ {a : Term} (ha : a.isSC = false) (m : Nat) :
    lt (iterT a m) (iterT a (m + 1)) = true := by
  show ltF (fuelOf (iterT a m) (iterT a (m + 1))) (iterT a m) (iterT a (m + 1)) = true
  refine ltF_iterT_succ ha m _ ?_
  show m + 1 ≤ 2 * ((iterT a m).deg + (iterT a (m + 1)).deg) + 8
  have := deg_iterT ha m
  omega

theorem ltF_iterT_bound {a c : Term} (ha : a.isSC = false) (hac : (a == c) = false)
    (hlt : ∀ f, 2 ≤ f → ltF f a c = true) :
    ∀ (m f : Nat), m + 2 ≤ f → ltF f (iterT a m) (phi c zero) = true
  | 0, f, hf => ltF_zero (by omega) (by intro hh; exact Term.noConfusion hh)
  | m + 1, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      rw [iterT_succ ha m]
      exact ltF_phi_fst hac (hlt g (by omega)) (ltF_iterT_bound ha hac hlt m g (by omega))

theorem lt_iterT_bound {a c : Term} (ha : a.isSC = false) (hac : (a == c) = false)
    (hlt : ∀ f, 2 ≤ f → ltF f a c = true) (m : Nat) :
    lt (iterT a m) (phi c zero) = true := by
  show ltF (fuelOf (iterT a m) (phi c zero)) (iterT a m) (phi c zero) = true
  refine ltF_iterT_bound ha hac hlt m _ ?_
  show m + 2 ≤ 2 * ((iterT a m).deg + (phi c zero).deg) + 8
  have := deg_iterT ha m
  omega

/-! ### The three concrete levels used by the table -/

theorem isSC_zero : (zero : Term).isSC = false := rfl
theorem isSC_one : (one : Term).isSC = false := rfl
theorem isSC_two : (ofNat 2).isSC = false := rfl

theorem ltF_zero_one : ∀ f, 2 ≤ f → ltF f zero one = true :=
  fun _ hf => ltF_zero (by omega) (by intro hh; exact Term.noConfusion hh)

theorem ltF_one_two : ∀ f, 2 ≤ f → ltF f one (ofNat 2) = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g => rfl

theorem ltF_two_three : ∀ f, 2 ≤ f → ltF f (ofNat 2) (ofNat 3) = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g => cases g with
    | zero => omega
    | succ h => rfl


/-! ## §3 Unfolding `oLAux` on single-block column sequences

All Stage-B expansions except the one of `(0,0)(1,1)(1,0)` are single blocks:
only their first column has row-0 entry 0. -/

theorem isAP_of_isSC {b : Term} (h : b.isSC = true) : b.isAP = true := by
  cases b <;> first | rfl | simp [isSC] at h

theorem isAP_phiNF (a b : Term) : (phiNF a b).isAP = true := by
  unfold phiNF phiNFsucc phiNFdefault
  split
  · rename_i h
    exact isAP_of_isSC (by simp at h; exact h.1)
  · repeat' split
    all_goals first
      | rfl
      | (apply isAP_of_isSC; simp_all)

theorem isAP_omegaNF (t : Term) : (omegaNF t).isAP = true := by
  unfold omegaNF
  split
  · rfl
  · split
    · rfl
    · exact isAP_phiNF zero t

theorem plus_zero_left {X : Term} (h : X.isAP = true) : plus zero X = X := by
  unfold plus
  rw [toList_of_isAP h]
  rfl

theorem lt_M_phi (a b : Term) : lt M (phi a b) = false := Evidence.StageA.ltF_M_phi _ a b

theorem lt_zero_ne {a : Term} (h : a ≠ zero) : lt zero a = true := by
  refine ltF_zero ?_ h
  show 1 ≤ 2 * ((zero : Term).deg + a.deg) + 8
  omega

theorem omegaNF_phi_ne_zero {a x : Term} (ha : a ≠ zero) : omegaNF (phi a x) = phi a x := by
  unfold omegaNF
  rw [lt_M_phi]
  simp only [Bool.false_eq_true, if_false]
  show (if ((phi a x == M) = true) then M else phiNF zero (phi a x)) = phi a x
  simp only [show ((phi a x == M) = false) from rfl, Bool.false_eq_true, if_false]
  unfold phiNF
  simp only [isSC, Bool.false_and, Bool.false_eq_true, if_false, lt_zero_ne ha, if_true]

theorem omegaNF_iterT {a : Term} (ha : a.isSC = false) (hz : a ≠ zero) (m : Nat) :
    omegaNF (iterT a (m + 1)) = iterT a (m + 1) := by
  rw [iterT_succ ha]
  exact omegaNF_phi_ne_zero hz

theorem logPhi_zero (k : Term) : Trans.Pair.logPhi k zero = none := rfl

theorem phiStep_zero (k v : Term) :
    Trans.Pair.phiStep k zero v
      = phiNF k (if (v == zero) = true then zero else omegaNF v) := by
  unfold Trans.Pair.phiStep
  rw [logPhi_zero]
  cases h : (v == zero) <;> simp

theorem blocksP_single (c : BMS.Col) :
    ∀ (t : List BMS.Col), (∀ x ∈ t, Trans.Pair.r0 x ≠ 0) →
      Trans.Pair.blocksP (c :: t) = [c :: t]
  | [], _ => rfl
  | b :: t, h => by
    have hb : Trans.Pair.r0 b ≠ 0 := h b (by simp)
    have ih : Trans.Pair.blocksP (b :: t) = [b :: t] :=
      blocksP_single b t (fun x hx => h x (List.mem_cons_of_mem b hx))
    show (match Trans.Pair.blocksP (b :: t), (b :: t).head? with
          | acc, some hd =>
            if Trans.Pair.r0 hd == 0 then [c] :: acc else (c :: acc.headD []) :: acc.tail
          | _, none => [[c]]) = [c :: b :: t]
    rw [ih]
    simp [hb]

/-- The defining equation of `oLAux` at positive fuel (no recursive unfolding). -/
theorem oLAux_cons (fuel k : Nat) (s : List BMS.Col) :
    Trans.Pair.oLAux (fuel + 1) k s
      = (Trans.Pair.blocksP s).foldl (init := zero) (fun acc b =>
          match b with
          | [] => acc
          | c :: t =>
            if Trans.Pair.r1 c == 0 then
              plus acc (omegaNF (Trans.Pair.oLAux fuel 1 (Trans.Pair.decP t)))
            else
              Trans.Pair.phiStep (ofNat k) acc
                (Trans.Pair.oLAux fuel (k + 1) (Trans.Pair.decP t))) := rfl

theorem oLAux_single (fuel k : Nat) (c : BMS.Col) (t : List BMS.Col)
    (h : ∀ x ∈ t, Trans.Pair.r0 x ≠ 0) :
    Trans.Pair.oLAux (fuel + 1) k (c :: t)
      = (if (Trans.Pair.r1 c == 0) = true then
           plus zero (omegaNF (Trans.Pair.oLAux fuel 1 (Trans.Pair.decP t)))
         else Trans.Pair.phiStep (ofNat k) zero (Trans.Pair.oLAux fuel (k + 1)
                (Trans.Pair.decP t))) := by
  rw [oLAux_cons, blocksP_single c t h]
  rfl

theorem oLAux_nil (fuel k : Nat) : Trans.Pair.oLAux fuel k [] = zero := by
  cases fuel <;> rfl


/-! ## §4 The shape of a BM4 expansion in the one-row-below-top fragment

Every Stage-B expansion is `((List.range (n+1)).map bad).flatten` for a bad-block
function `bad` that shifts its row-0 entries by a fixed `step` per copy.  `frep`
is the same list, but built from the front, which is the direction in which
`oLAux` recurses. -/

/-- `f o ++ f (o+step) ++ … ` with `m` blocks. -/
def frep (f : Nat → Matrix) (step : Nat) (o : Nat) : Nat → Matrix
  | 0 => []
  | m + 1 => f o ++ frep f step (o + step) m

theorem flat_frep (f : Nat → Matrix) (step : Nat) : ∀ (m o : Nat),
    ((List.range m).map (fun a => f (step * a + o))).flatten = frep f step o m
  | 0, _ => rfl
  | m + 1, o => by
    rw [List.range_succ_eq_map, List.map_cons, List.flatten_cons, List.map_map]
    have h1 : ((fun a => f (step * a + o)) ∘ Nat.succ) = (fun a => f (step * a + (o + step))) := by
      funext a
      show f (step * (a + 1) + o) = f (step * a + (o + step))
      congr 1
      rw [Nat.mul_succ]
      omega
    rw [h1, flat_frep f step m (o + step)]
    show f (step * 0 + o) ++ frep f step (o + step) m = f o ++ frep f step (o + step) m
    congr 2
    omega

theorem decP_append (u v : List BMS.Col) :
    Trans.Pair.decP (u ++ v) = Trans.Pair.decP u ++ Trans.Pair.decP v := List.map_append

theorem decP_frep {f : Nat → Matrix} {step : Nat}
    (hf : ∀ o, Trans.Pair.decP (f (o + 1)) = f o) :
    ∀ (m o : Nat), Trans.Pair.decP (frep f step (o + 1) m) = frep f step o m
  | 0, _ => rfl
  | m + 1, o => by
    show Trans.Pair.decP (f (o + 1) ++ frep f step (o + 1 + step) m)
        = f o ++ frep f step (o + step) m
    rw [decP_append, hf o]
    congr 1
    have h : o + 1 + step = (o + step) + 1 := by omega
    rw [h, decP_frep hf m (o + step)]

theorem r0_frep {f : Nat → Matrix} {step : Nat}
    (hf : ∀ o, 1 ≤ o → ∀ c ∈ f o, Trans.Pair.r0 c ≠ 0) :
    ∀ (m o : Nat), 1 ≤ o → ∀ c ∈ frep f step o m, Trans.Pair.r0 c ≠ 0
  | 0, _, _, _, hc => by simp [frep] at hc
  | m + 1, o, ho, c, hc => by
    have hc' : c ∈ f o ++ frep f step (o + step) m := hc
    rcases List.mem_append.mp hc' with h | h
    · exact hf o ho c h
    · exact r0_frep hf m (o + step) (by omega) c h

theorem inFrag_append (u v : Matrix) :
    Trans.Pair.inFrag (u ++ v) = (Trans.Pair.inFrag u && Trans.Pair.inFrag v) := List.all_append

theorem inFrag_frep {f : Nat → Matrix} {step : Nat} (hf : ∀ o, Trans.Pair.inFrag (f o) = true) :
    ∀ (m o : Nat), Trans.Pair.inFrag (frep f step o m) = true
  | 0, _ => rfl
  | m + 1, o => by
    show Trans.Pair.inFrag (f o ++ frep f step (o + step) m) = true
    rw [inFrag_append, hf o, inFrag_frep hf m (o + step)]
    rfl

theorem onlyRow0_append (u v : Matrix) :
    onlyRow0 (u ++ v) = (onlyRow0 u && onlyRow0 v) := List.all_append

/-- `o?` on a matrix of the Stage-B fragment that is not row-1-trivial. -/
theorem o?_pair {m : Matrix} (h1 : onlyRow0 m = false) (h2 : Trans.Pair.inFrag m = true) :
    o? m = some (Trans.Pair.oLAux (m.length + 1) 1 m) := by
  show (if onlyRow0 m = true then some (oPr m) else oPair? m) = _
  rw [h1]
  simp only [Bool.false_eq_true, if_false]
  show (if Trans.Pair.inFrag m = true then
      some (if onlyRow0 m = true then oPr m else Trans.Pair.oLAux (m.length + 1) 1 m)
    else none) = _
  rw [h2, h1]
  simp


/-! ## §5 Fundamental sequences of `φ̄(a,0)` for a successor `a`

`fsN (φ̄ a 0) n` is the n-fold iterate of `φ_{a-1}` at 0, i.e. `iterT (predT a) n`. -/

theorem ofNat_one : ofNat 1 = one := rfl

theorem iterPhiAt_zero (c : Term) : ∀ n, iterPhiAt c zero n = iterT c n
  | 0 => rfl
  | m + 1 => by
    show phiNF c (iterPhiAt c zero m) = phiNF c (iterT c m)
    rw [iterPhiAt_zero c m]

theorem phiShifted_zero_arg {a : Term} (ha : a.isSC = false) : phiShifted a zero = false := by
  unfold phiShifted
  rw [show (splitFin (zero : Term)).1 = zero from rfl]
  unfold isFP
  simp [isSC]
  exact ha

theorem fsN_phi_zero {a : Term} (ha : a.isSC = false) (hk : kindT a = KindT.isSucc) (n : Nat) :
    fsN (phi a zero) n = iterT (predT a) n := by
  rw [fsN]
  simp only [phiShifted_zero_arg ha, hk, Bool.false_or,
    show (kindT (zero : Term) == KindT.isSucc) = false from rfl,
    show (kindT (zero : Term) == KindT.isLim) = false from rfl,
    Bool.false_eq_true, if_false]
  exact iterPhiAt_zero _ n


theorem phiNF_collapse {a c x : Term} (h : lt a c = true) : phiNF a (phi c x) = phi c x := by
  unfold phiNF
  simp only [isSC, Bool.false_and, Bool.false_eq_true, if_false, h, if_true]

theorem omegaNF_phi (a x : Term) : omegaNF (phi a x) = phiNF zero (phi a x) := by
  unfold omegaNF
  rw [lt_M_phi]
  simp only [Bool.false_eq_true, if_false]
  show (if ((phi a x == M) = true) then M else phiNF zero (phi a x)) = phiNF zero (phi a x)
  simp only [show ((phi a x == M) = false) from rfl, Bool.false_eq_true, if_false]


theorem phiStep_iterT {a : Term} (ha : a.isSC = false) (hz : a ≠ zero) :
    ∀ m, Trans.Pair.phiStep a zero (iterT a m) = iterT a (m + 1)
  | 0 => by rw [phiStep_zero]; simp; rfl
  | m + 1 => by
    rw [phiStep_zero]
    have hne : (iterT a (m + 1) == zero) = false := by
      simp [iterT_ne_zero ha m]
    rw [hne]
    simp only [Bool.false_eq_true, if_false, omegaNF_iterT ha hz m]
    rfl

/-! ## §6 Row `(0,0)(1,1)(2,1)` = ζ₀ = φ̄(2,0)

`M[n] = (0,0)(1,1)(2,0)(3,1)…(2n,0)(2n+1,1)`, whose value is the (n+1)-st ε-tower
`φ_1^{n+1}(0)`; the fundamental sequence of ζ₀ is the same tower, so E3 holds here
as a plain equality. -/

namespace R6

def m0 : Matrix := [[0,0],[1,1],[2,1]]
def t0 : Term := phi (ofNat 2) zero
def blk (o : Nat) : Matrix := [[o,0],[o+1,1]]

theorem raw_eq (a : Nat) :
    ([[0 + a*2*1, 0 + a*0*1], [1 + a*2*1, 1 + a*0*1]] : Matrix) = blk (2 * a + 0) := by
  show ([[0 + a*2*1, 0 + a*0*1], [1 + a*2*1, 1 + a*0*1]] : Matrix)
      = [[2*a+0, 0], [2*a+0+1, 1]]
  have h1 : 0 + a*2*1 = 2*a+0 := by omega
  have h2 : 0 + a*0*1 = 0 := by omega
  have h3 : 1 + a*2*1 = 2*a+0+1 := by omega
  have h4 : 1 + a*0*1 = 1 := by omega
  rw [h1, h2, h3, h4]

theorem expand_eq (n : Nat) : BMS.expand? m0 n = some (frep blk 2 0 (n+1)) := by
  have h : BMS.expand? m0 n
      = some (((List.range (n+1)).map
          (fun a => ([[0 + a*2*1, 0 + a*0*1], [1 + a*2*1, 1 + a*0*1]] : Matrix))).flatten) := rfl
  rw [h, List.map_congr_left (fun a _ => raw_eq a), flat_frep]

theorem blk_decP (o : Nat) : Trans.Pair.decP (blk (o+1)) = blk o := by
  show ([[o+1-1, 0], [o+1+1-1, 1]] : Matrix) = [[o, 0], [o+1, 1]]
  have h1 : o+1-1 = o := by omega
  have h2 : o+1+1-1 = o+1 := by omega
  rw [h1, h2]

theorem blk_r0 (o : Nat) (ho : 1 ≤ o) : ∀ c ∈ blk o, Trans.Pair.r0 c ≠ 0 := by
  intro c hc
  rcases List.mem_cons.mp hc with h | h
  · subst h; show o ≠ 0; omega
  · rcases List.mem_cons.mp h with h | h
    · subst h; show o+1 ≠ 0; omega
    · simp at h

theorem blk_inFrag (o : Nat) : Trans.Pair.inFrag (blk o) = true := rfl

theorem frep_len : ∀ (m o : Nat), (frep blk 2 o m).length = 2*m
  | 0, _ => rfl
  | m+1, o => by
    show ((blk o) ++ frep blk 2 (o+2) m).length = 2*(m+1)
    rw [List.length_append, frep_len m (o+2)]
    show 2 + 2*m = 2*(m+1)
    omega

/-- The value of the n-th expansion: the (n+1)-st ε-tower. -/
theorem val : ∀ (m fuel k : Nat), 2*m + 3 ≤ fuel →
    Trans.Pair.oLAux fuel k (frep blk 2 0 (m+1)) = iterT one (m+1)
  | m, fuel, k, hf => by
    cases fuel with
    | zero => omega
    | succ g =>
      cases g with
      | zero => omega
      | succ h =>
        have hE : frep blk 2 0 (m+1)
            = ([0,0] : BMS.Col) :: (([1,1] : BMS.Col) :: frep blk 2 2 m) := rfl
        have ht : ∀ c ∈ (([1,1] : BMS.Col) :: frep blk 2 2 m), Trans.Pair.r0 c ≠ 0 := by
          intro c hc
          rcases List.mem_cons.mp hc with h1 | h1
          · subst h1; show (1:Nat) ≠ 0; omega
          · exact r0_frep blk_r0 m 2 (by omega) c h1
        rw [hE, oLAux_single (h+1) k [0,0] _ ht]
        show plus zero (omegaNF (Trans.Pair.oLAux (h+1) 1
          (Trans.Pair.decP (([1,1] : BMS.Col) :: frep blk 2 2 m)))) = iterT one (m+1)
        have hd : Trans.Pair.decP (([1,1] : BMS.Col) :: frep blk 2 2 m)
            = ([0,1] : BMS.Col) :: frep blk 2 1 m := by
          show ([0,1] : BMS.Col) :: Trans.Pair.decP (frep blk 2 2 m) = _
          rw [decP_frep blk_decP m 1]
        rw [hd, oLAux_single h 1 [0,1] _ (r0_frep blk_r0 m 1 (by omega))]
        show plus zero (omegaNF (Trans.Pair.phiStep (ofNat 1) zero
          (Trans.Pair.oLAux h 2 (Trans.Pair.decP (frep blk 2 1 m))))) = iterT one (m+1)
        rw [decP_frep blk_decP m 0, ofNat_one]
        have hinner : Trans.Pair.oLAux h 2 (frep blk 2 0 m) = iterT one m := by
          cases m with
          | zero => exact oLAux_nil h 2
          | succ m' => exact val m' h 2 (by omega)
        rw [hinner, phiStep_iterT isSC_one (by intro hc; exact Term.noConfusion hc) m,
          omegaNF_iterT isSC_one (by intro hc; exact Term.noConfusion hc) m,
          plus_zero_left (by rw [iterT_succ isSC_one]; rfl)]

theorem onlyRow0_E (m : Nat) : onlyRow0 (frep blk 2 0 (m+1)) = false := by
  show onlyRow0 (blk 0 ++ frep blk 2 2 m) = false
  rw [onlyRow0_append]
  rfl

theorem fs_t (k : Nat) : fsN t0 k = iterT one k := by
  show fsN (phi (ofNat 2) zero) k = _
  rw [fsN_phi_zero isSC_two (show kindT (ofNat 2) = KindT.isSucc from rfl) k]
  rfl

/-- **E3, part (a)**: closed form of the n-th expansion, which here coincides with
    the fundamental sequence of ζ₀ at n+1. -/
theorem e3_val (n : Nat) : o? (BMS.expand m0 n) = some (fsN t0 (n+1)) := by
  have hE : BMS.expand m0 n = frep blk 2 0 (n+1) := by
    show (BMS.expand? m0 n).getD [] = _
    rw [expand_eq]; rfl
  rw [hE, o?_pair (onlyRow0_E n) (inFrag_frep blk_inFrag (n+1) 0), frep_len (n+1) 0,
    val n (2*(n+1)+1) 1 (by omega), fs_t]

/-- **E3, part (a)**: every expansion stays below the term. -/
theorem e3_lt (n : Nat) : lt (fsN t0 (n+1)) t0 = true := by
  rw [fs_t]
  exact lt_iterT_bound isSC_one (by rfl) ltF_one_two (n+1)

/-- **E3, part (b)** with witness `k := n+2`. -/
theorem e3_over (n : Nat) : lt (fsN t0 (n+1)) (fsN t0 (n+2)) = true := by
  rw [fs_t, fs_t]
  exact lt_iterT_succ isSC_one (n+1)

/-- **E3, part (c)** with witness `n := k+1`. -/
theorem e3_under (k : Nat) : lt (fsN t0 (k+1)) (fsN t0 ((k+1)+1)) = true := e3_over k

end R6



/-! ## §7 Row `(0,0)(1,1)(2,1)(3,1)` = φ̄(3,0)

`M[n] = (0,0)(1,1)(2,1)(3,0)(4,1)(5,1)…`, whose value is the (n+1)-st ζ-tower
`φ_2^{n+1}(0)` — again exactly `fsN (φ̄(3,0)) (n+1)`. -/

namespace R9

def m0 : Matrix := [[0,0],[1,1],[2,1],[3,1]]
def t0 : Term := phi (ofNat 3) zero
def blk (o : Nat) : Matrix := [[o,0],[o+1,1],[o+2,1]]

theorem raw_eq (a : Nat) :
    ([[0 + a*3*1, 0 + a*0*1], [1 + a*3*1, 1 + a*0*1], [2 + a*3*1, 1 + a*0*1]] : Matrix)
      = blk (3 * a + 0) := by
  show _ = ([[3*a+0, 0], [3*a+0+1, 1], [3*a+0+2, 1]] : Matrix)
  have h1 : 0 + a*3*1 = 3*a+0 := by omega
  have h2 : 0 + a*0*1 = 0 := by omega
  have h3 : 1 + a*3*1 = 3*a+0+1 := by omega
  have h4 : 1 + a*0*1 = 1 := by omega
  have h5 : 2 + a*3*1 = 3*a+0+2 := by omega
  rw [h1, h2, h3, h4, h5]

theorem expand_eq (n : Nat) : BMS.expand? m0 n = some (frep blk 3 0 (n+1)) := by
  have h : BMS.expand? m0 n
      = some (((List.range (n+1)).map
          (fun a => ([[0 + a*3*1, 0 + a*0*1], [1 + a*3*1, 1 + a*0*1],
                     [2 + a*3*1, 1 + a*0*1]] : Matrix))).flatten) := rfl
  rw [h, List.map_congr_left (fun a _ => raw_eq a), flat_frep]

theorem blk_decP (o : Nat) : Trans.Pair.decP (blk (o+1)) = blk o := by
  show ([[o+1-1, 0], [o+1+1-1, 1], [o+1+2-1, 1]] : Matrix) = [[o, 0], [o+1, 1], [o+2, 1]]
  have h1 : o+1-1 = o := by omega
  have h2 : o+1+1-1 = o+1 := by omega
  have h3 : o+1+2-1 = o+2 := by omega
  rw [h1, h2, h3]

theorem blk_r0 (o : Nat) (ho : 1 ≤ o) : ∀ c ∈ blk o, Trans.Pair.r0 c ≠ 0 := by
  intro c hc
  rcases List.mem_cons.mp hc with h | h
  · subst h; show o ≠ 0; omega
  · rcases List.mem_cons.mp h with h | h
    · subst h; show o+1 ≠ 0; omega
    · rcases List.mem_cons.mp h with h | h
      · subst h; show o+2 ≠ 0; omega
      · simp at h

theorem blk_inFrag (o : Nat) : Trans.Pair.inFrag (blk o) = true := rfl

theorem frep_len : ∀ (m o : Nat), (frep blk 3 o m).length = 3*m
  | 0, _ => rfl
  | m+1, o => by
    show ((blk o) ++ frep blk 3 (o+3) m).length = 3*(m+1)
    rw [List.length_append, frep_len m (o+3)]
    show 3 + 3*m = 3*(m+1)
    omega

theorem lt_one_two : lt one (ofNat 2) = true := by decide

theorem val : ∀ (m fuel k : Nat), 3*m + 4 ≤ fuel →
    Trans.Pair.oLAux fuel k (frep blk 3 0 (m+1)) = iterT (ofNat 2) (m+1)
  | m, fuel, k, hf => by
    cases fuel with
    | zero => omega
    | succ g =>
      cases g with
      | zero => omega
      | succ h =>
        cases h with
        | zero => omega
        | succ i =>
          have hE : frep blk 3 0 (m+1)
              = ([0,0] : BMS.Col) :: (([1,1] : BMS.Col) :: (([2,1] : BMS.Col)
                  :: frep blk 3 3 m)) := rfl
          have ht : ∀ c ∈ (([1,1] : BMS.Col) :: (([2,1] : BMS.Col) :: frep blk 3 3 m)),
              Trans.Pair.r0 c ≠ 0 := by
            intro c hc
            rcases List.mem_cons.mp hc with h1 | h1
            · subst h1; show (1:Nat) ≠ 0; omega
            · rcases List.mem_cons.mp h1 with h2 | h2
              · subst h2; show (2:Nat) ≠ 0; omega
              · exact r0_frep blk_r0 m 3 (by omega) c h2
          rw [hE, oLAux_single (i+2) k [0,0] _ ht]
          show plus zero (omegaNF (Trans.Pair.oLAux (i+2) 1
            (Trans.Pair.decP (([1,1] : BMS.Col) :: (([2,1] : BMS.Col)
              :: frep blk 3 3 m))))) = iterT (ofNat 2) (m+1)
          have hd1 : Trans.Pair.decP (([1,1] : BMS.Col) :: (([2,1] : BMS.Col)
              :: frep blk 3 3 m))
              = ([0,1] : BMS.Col) :: (([1,1] : BMS.Col) :: frep blk 3 2 m) := by
            show ([0,1] : BMS.Col) :: (([1,1] : BMS.Col)
              :: Trans.Pair.decP (frep blk 3 3 m)) = _
            rw [decP_frep blk_decP m 2]
          have ht1 : ∀ c ∈ (([1,1] : BMS.Col) :: frep blk 3 2 m), Trans.Pair.r0 c ≠ 0 := by
            intro c hc
            rcases List.mem_cons.mp hc with h1 | h1
            · subst h1; show (1:Nat) ≠ 0; omega
            · exact r0_frep blk_r0 m 2 (by omega) c h1
          rw [hd1, oLAux_single (i+1) 1 [0,1] _ ht1]
          show plus zero (omegaNF (Trans.Pair.phiStep (ofNat 1) zero
            (Trans.Pair.oLAux (i+1) 2 (Trans.Pair.decP (([1,1] : BMS.Col)
              :: frep blk 3 2 m))))) = iterT (ofNat 2) (m+1)
          have hd2 : Trans.Pair.decP (([1,1] : BMS.Col) :: frep blk 3 2 m)
              = ([0,1] : BMS.Col) :: frep blk 3 1 m := by
            show ([0,1] : BMS.Col) :: Trans.Pair.decP (frep blk 3 2 m) = _
            rw [decP_frep blk_decP m 1]
          rw [hd2, oLAux_single i 2 [0,1] _ (r0_frep blk_r0 m 1 (by omega))]
          show plus zero (omegaNF (Trans.Pair.phiStep (ofNat 1) zero
            (Trans.Pair.phiStep (ofNat 2) zero (Trans.Pair.oLAux i 3
              (Trans.Pair.decP (frep blk 3 1 m)))))) = iterT (ofNat 2) (m+1)
          rw [decP_frep blk_decP m 0]
          have hinner : Trans.Pair.oLAux i 3 (frep blk 3 0 m) = iterT (ofNat 2) m := by
            cases m with
            | zero => exact oLAux_nil i 3
            | succ m' => exact val m' i 3 (by omega)
          have hne : (ofNat 2 : Term) ≠ zero := by intro hc; exact Term.noConfusion hc
          rw [hinner, phiStep_iterT isSC_two hne m, ofNat_one]
          rw [phiStep_zero, iterT_succ isSC_two m]
          have hz : ((phi (ofNat 2) (iterT (ofNat 2) m) == zero) = false) := rfl
          rw [hz]
          simp only [Bool.false_eq_true, if_false]
          rw [omegaNF_phi_ne_zero hne, phiNF_collapse lt_one_two,
            omegaNF_phi_ne_zero hne, plus_zero_left rfl]

theorem onlyRow0_E (m : Nat) : onlyRow0 (frep blk 3 0 (m+1)) = false := by
  show onlyRow0 (blk 0 ++ frep blk 3 3 m) = false
  rw [onlyRow0_append]
  rfl

theorem fs_t (k : Nat) : fsN t0 k = iterT (ofNat 2) k := by
  show fsN (phi (ofNat 3) zero) k = _
  rw [fsN_phi_zero (show (ofNat 3 : Term).isSC = false from rfl)
    (show kindT (ofNat 3) = KindT.isSucc from rfl) k]
  rfl

theorem e3_val (n : Nat) : o? (BMS.expand m0 n) = some (fsN t0 (n+1)) := by
  have hE : BMS.expand m0 n = frep blk 3 0 (n+1) := by
    show (BMS.expand? m0 n).getD [] = _
    rw [expand_eq]; rfl
  rw [hE, o?_pair (onlyRow0_E n) (inFrag_frep blk_inFrag (n+1) 0), frep_len (n+1) 0,
    val n (3*(n+1)+1) 1 (by omega), fs_t]

theorem e3_lt (n : Nat) : lt (fsN t0 (n+1)) t0 = true := by
  rw [fs_t]
  exact lt_iterT_bound isSC_two (by rfl) ltF_two_three (n+1)

theorem e3_over (n : Nat) : lt (fsN t0 (n+1)) (fsN t0 (n+2)) = true := by
  rw [fs_t, fs_t]
  exact lt_iterT_succ isSC_two (n+1)

theorem e3_under (k : Nat) : lt (fsN t0 (k+1)) (fsN t0 ((k+1)+1)) = true := e3_over k

end R9


/-! ## §8 Row `(0,0)(1,1)` = ε₀ = φ̄(1,0)

`M[n] = (0,0)(1,0)(2,0)…(n,0)` is row-1-trivial, so its value is Stage A's `oPr`
of the primitive sequence `0 1 2 … n`, i.e. the ω-tower of height n+1, which is
exactly `fsN ε₀ (n+1)`. -/

namespace R1

def m0 : Matrix := [[0,0],[1,1]]
def t0 : Term := phi one zero
def blk (o : Nat) : Matrix := [[o,0]]

/-- The primitive sequence `o, o+1, …, o+m`. -/
def sq (o : Nat) : Nat → List Nat
  | 0 => [o]
  | m + 1 => o :: sq (o + 1) m

theorem raw_eq (a : Nat) : ([[0 + a*1*1, 0 + a*0*1]] : Matrix) = blk (1 * a + 0) := by
  show ([[0 + a*1*1, 0 + a*0*1]] : Matrix) = [[1*a+0, 0]]
  have h1 : 0 + a*1*1 = 1*a+0 := by omega
  have h2 : 0 + a*0*1 = 0 := by omega
  rw [h1, h2]

theorem expand_eq (n : Nat) : BMS.expand? m0 n = some (frep blk 1 0 (n+1)) := by
  have h : BMS.expand? m0 n
      = some (((List.range (n+1)).map
          (fun a => ([[0 + a*1*1, 0 + a*0*1]] : Matrix))).flatten) := rfl
  rw [h, List.map_congr_left (fun a _ => raw_eq a), flat_frep]

theorem row0_frep : ∀ (m o : Nat), row0 (frep blk 1 o (m+1)) = sq o m
  | 0, o => rfl
  | m + 1, o => by
    show o :: row0 (frep blk 1 (o+1) (m+1)) = o :: sq (o+1) m
    rw [row0_frep m (o+1)]

theorem onlyRow0_frep : ∀ (m o : Nat), onlyRow0 (frep blk 1 o m) = true
  | 0, _ => rfl
  | m + 1, o => by
    show onlyRow0 (blk o ++ frep blk 1 (o+1) m) = true
    rw [onlyRow0_append, onlyRow0_frep m (o+1)]
    rfl

theorem frep_len : ∀ (m o : Nat), (frep blk 1 o m).length = m
  | 0, _ => rfl
  | m + 1, o => by
    show ((blk o) ++ frep blk 1 (o+1) m).length = m + 1
    rw [List.length_append, frep_len m (o+1)]
    show 1 + m = m + 1
    omega

theorem sq_ge : ∀ (m o : Nat), ∀ x ∈ sq o m, o ≤ x
  | 0, o, x, hx => by
    have : x = o := by simpa [sq] using hx
    omega
  | m + 1, o, x, hx => by
    rcases List.mem_cons.mp hx with h | h
    · omega
    · have := sq_ge m (o+1) x h
      omega

theorem map_pred_sq : ∀ (m o : Nat), (sq (o+1) m).map (· - 1) = sq o m
  | 0, o => by
    show [o+1-1] = [o]
    have : o+1-1 = o := by omega
    rw [this]
  | m + 1, o => by
    show (o+1-1) :: (sq (o+1+1) m).map (· - 1) = o :: sq (o+1) m
    have h1 : o+1-1 = o := by omega
    rw [h1, map_pred_sq m (o+1)]

theorem dec_sq (m : Nat) : Evidence.StageA.dec (sq 0 (m+1)) = sq 0 m := by
  show ((0 :: sq 1 m).drop 1).map (· - 1) = sq 0 m
  exact map_pred_sq m 0

theorem blocks0_sq : ∀ (m : Nat), blocks0 (sq 0 m) = [sq 0 m]
  | 0 => rfl
  | m + 1 => by
    show blocks0 (0 :: sq 1 m) = [0 :: sq 1 m]
    exact blocks0_single 0 (sq 1 m) (fun x hx => by have := sq_ge m 1 x hx; omega)

theorem oV_sq : ∀ (m : Nat), Evidence.StageA.oV (sq 0 m) = iterT zero (m+1)
  | 0 => by
    rw [Evidence.StageA.oV_eq, blocks0_sq 0]
    show plus (omegaNF (Evidence.StageA.oV (Evidence.StageA.dec [0]))) zero = iterT zero 1
    rw [show Evidence.StageA.dec [0] = ([] : List Nat) from rfl, Evidence.StageA.oV_nil,
      plus_zero]
    rfl
  | m + 1 => by
    rw [Evidence.StageA.oV_eq, blocks0_sq (m+1)]
    show plus (omegaNF (Evidence.StageA.oV (Evidence.StageA.dec (sq 0 (m+1))))) zero
        = iterT zero (m+2)
    rw [dec_sq m, plus_zero, oV_sq m, iterT_succ isSC_zero m, omegaNF_phi,
      phiNF_phi_arg isSC_zero]
    show phi zero (phi zero (iterT zero m)) = iterT zero (m+2)
    rw [iterT_succ isSC_zero (m+1), iterT_succ isSC_zero m]

theorem fs_t (k : Nat) : fsN t0 k = iterT zero k := by
  show fsN (phi one zero) k = _
  rw [fsN_phi_zero isSC_one (show kindT one = KindT.isSucc from rfl) k]
  rfl

theorem e3_val (n : Nat) : o? (BMS.expand m0 n) = some (fsN t0 (n+1)) := by
  have hE : BMS.expand m0 n = frep blk 1 0 (n+1) := by
    show (BMS.expand? m0 n).getD [] = _
    rw [expand_eq]; rfl
  rw [hE]
  show (if onlyRow0 (frep blk 1 0 (n+1)) = true then some (oPr (frep blk 1 0 (n+1)))
        else oPair? (frep blk 1 0 (n+1))) = _
  rw [onlyRow0_frep (n+1) 0]
  simp only [if_true]
  rw [Evidence.StageA.oPr_eq, row0_frep n 0, oV_sq n, fs_t]

theorem e3_lt (n : Nat) : lt (fsN t0 (n+1)) t0 = true := by
  rw [fs_t]
  exact lt_iterT_bound isSC_zero (by rfl) ltF_zero_one (n+1)

theorem e3_over (n : Nat) : lt (fsN t0 (n+1)) (fsN t0 (n+2)) = true := by
  rw [fs_t, fs_t]
  exact lt_iterT_succ isSC_zero (n+1)

theorem e3_under (k : Nat) : lt (fsN t0 (k+1)) (fsN t0 ((k+1)+1)) = true := e3_over k

end R1


/-! ## §9 Row `(0,0)(1,1)(2,0)(3,1)` = ε_{ε₀} = φ̄(1,ε₀)

`M[n] = (0,0)(1,1)(2,0)(3,0)…(n+2,0)`, whose value is `φ̄(1, ω-tower of height n+2)`.
Here the expansion runs two steps ahead of the fundamental sequence:
`o(M[n]) = fsN (φ̄(1,ε₀)) (n+2)`. -/

theorem lt_of_ltF {x y : Term} {N : Nat} (h : ∀ f, N ≤ f → ltF f x y = true)
    (hN : N ≤ 2 * (x.deg + y.deg) + 8) : lt x y = true := h _ hN

theorem fsN_phi_lim {a b : Term} (hs : phiShifted a b = false) (hk : kindT b = KindT.isLim)
    (n : Nat) : fsN (phi a b) n = phiNF a (fsN b n) := by
  rw [fsN]
  simp only [hs, hk, Bool.false_or,
    show (KindT.isLim == KindT.isSucc) = false from rfl,
    show (KindT.isLim == KindT.isLim) = true from rfl,
    Bool.false_eq_true, if_false, if_true]

theorem omegaNF_iterT_zero (m : Nat) : omegaNF (iterT zero (m+1)) = iterT zero (m+2) := by
  rw [iterT_succ isSC_zero m, omegaNF_phi, phiNF_phi_arg isSC_zero]
  rw [iterT_succ isSC_zero (m+1), iterT_succ isSC_zero m]

theorem phiNF_one_iterT_zero : ∀ k, phiNF one (iterT zero k) = phi one (iterT zero k)
  | 0 => phiNF_zero_arg isSC_one
  | k + 1 => by
    rw [iterT_succ isSC_zero k]
    exact phiNF_phi_gen isSC_one (lt_lt_zero one)

theorem lt_phi_iterT_bound {a c : Term} (ha : a.isSC = false) (hac : (a == c) = false)
    (hlt : ∀ f, 2 ≤ f → ltF f a c = true) (d : Term) (m : Nat) :
    lt (phi d (iterT a m)) (phi d (phi c zero)) = true := by
  refine lt_of_ltF (N := m + 3) (fun f hf => ?_) ?_
  · cases f with
    | zero => omega
    | succ g => exact ltF_phi_same (ltF_iterT_bound ha hac hlt m g (by omega))
  · show m + 3 ≤ 2 * ((phi d (iterT a m)).deg + (phi d (phi c zero)).deg) + 8
    have := deg_iterT ha m
    show m + 3 ≤ 2 * ((1 + d.deg + (iterT a m).deg) + (1 + d.deg + (1 + c.deg + 1))) + 8
    omega

theorem lt_phi_iterT_succ {a : Term} (ha : a.isSC = false) (d : Term) (m : Nat) :
    lt (phi d (iterT a m)) (phi d (iterT a (m+1))) = true := by
  refine lt_of_ltF (N := m + 2) (fun f hf => ?_) ?_
  · cases f with
    | zero => omega
    | succ g => exact ltF_phi_same (ltF_iterT_succ ha m g (by omega))
  · show m + 2 ≤ 2 * ((phi d (iterT a m)).deg + (phi d (iterT a (m+1))).deg) + 8
    have := deg_iterT ha m
    show m + 2 ≤ 2 * ((1 + d.deg + (iterT a m).deg) + (1 + d.deg + (iterT a (m+1)).deg)) + 8
    omega

/-! ### The pure ω-tower read by `oLAux` -/

theorem blkA_decP (o : Nat) : Trans.Pair.decP (R1.blk (o+1)) = R1.blk o := by
  show ([[o+1-1, 0]] : Matrix) = [[o, 0]]
  have h1 : o+1-1 = o := by omega
  rw [h1]

theorem blkA_r0 (o : Nat) (ho : 1 ≤ o) : ∀ c ∈ R1.blk o, Trans.Pair.r0 c ≠ 0 := by
  intro c hc
  rcases List.mem_cons.mp hc with h | h
  · subst h; show o ≠ 0; omega
  · simp at h

theorem blkA_inFrag (o : Nat) : Trans.Pair.inFrag (R1.blk o) = true := rfl

theorem valTower : ∀ (m fuel k : Nat), m + 2 ≤ fuel →
    Trans.Pair.oLAux fuel k (frep R1.blk 1 0 (m+1)) = iterT zero (m+1)
  | m, fuel, k, hf => by
    cases fuel with
    | zero => omega
    | succ g =>
      have hE : frep R1.blk 1 0 (m+1) = ([0,0] : BMS.Col) :: frep R1.blk 1 1 m := rfl
      rw [hE, oLAux_single g k [0,0] _ (r0_frep blkA_r0 m 1 (by omega))]
      show plus zero (omegaNF (Trans.Pair.oLAux g 1
        (Trans.Pair.decP (frep R1.blk 1 1 m)))) = iterT zero (m+1)
      rw [decP_frep blkA_decP m 0]
      cases m with
      | zero =>
        rw [show frep R1.blk 1 0 0 = ([] : Matrix) from rfl, oLAux_nil g 1]
        show plus zero (omegaNF zero) = iterT zero 1
        rw [plus_zero_left (show (omegaNF zero).isAP = true from rfl)]
        rfl
      | succ m' =>
        rw [valTower m' g 1 (by omega), omegaNF_iterT_zero m',
          plus_zero_left (by rw [iterT_succ isSC_zero (m'+1)]; rfl)]

namespace R5

def m0 : Matrix := [[0,0],[1,1],[2,0],[3,1]]
def t0 : Term := phi one (phi one zero)

theorem raw_eq (a : Nat) : ([[2 + a*1*1, 0 + a*0*1]] : Matrix) = R1.blk (1 * a + 2) := by
  show ([[2 + a*1*1, 0 + a*0*1]] : Matrix) = [[1*a+2, 0]]
  have h1 : 2 + a*1*1 = 1*a+2 := by omega
  have h2 : 0 + a*0*1 = 0 := by omega
  rw [h1, h2]

theorem expand_eq (n : Nat) :
    BMS.expand? m0 n = some ([[0,0],[1,1]] ++ frep R1.blk 1 2 (n+1)) := by
  have h : BMS.expand? m0 n
      = some ([[0,0],[1,1]] ++ ((List.range (n+1)).map
          (fun a => ([[2 + a*1*1, 0 + a*0*1]] : Matrix))).flatten) := rfl
  rw [h, List.map_congr_left (fun a _ => raw_eq a), flat_frep]

theorem val : ∀ (n fuel k : Nat), n + 4 ≤ fuel →
    Trans.Pair.oLAux fuel k ([[0,0],[1,1]] ++ frep R1.blk 1 2 (n+1))
      = phi one (iterT zero (n+2)) := by
  intro n fuel k hf
  cases fuel with
  | zero => omega
  | succ g =>
    cases g with
    | zero => omega
    | succ i =>
      have hE : ([[0,0],[1,1]] ++ frep R1.blk 1 2 (n+1))
          = ([0,0] : BMS.Col) :: (([1,1] : BMS.Col) :: frep R1.blk 1 2 (n+1)) := rfl
      have ht : ∀ c ∈ (([1,1] : BMS.Col) :: frep R1.blk 1 2 (n+1)),
          Trans.Pair.r0 c ≠ 0 := by
        intro c hc
        rcases List.mem_cons.mp hc with h1 | h1
        · subst h1; show (1:Nat) ≠ 0; omega
        · exact r0_frep blkA_r0 (n+1) 2 (by omega) c h1
      rw [hE, oLAux_single (i+1) k [0,0] _ ht]
      show plus zero (omegaNF (Trans.Pair.oLAux (i+1) 1
        (Trans.Pair.decP (([1,1] : BMS.Col) :: frep R1.blk 1 2 (n+1)))))
          = phi one (iterT zero (n+2))
      have hd : Trans.Pair.decP (([1,1] : BMS.Col) :: frep R1.blk 1 2 (n+1))
          = ([0,1] : BMS.Col) :: frep R1.blk 1 1 (n+1) := by
        show ([0,1] : BMS.Col) :: Trans.Pair.decP (frep R1.blk 1 2 (n+1)) = _
        rw [decP_frep blkA_decP (n+1) 1]
      rw [hd, oLAux_single i 1 [0,1] _ (r0_frep blkA_r0 (n+1) 1 (by omega))]
      show plus zero (omegaNF (Trans.Pair.phiStep (ofNat 1) zero
        (Trans.Pair.oLAux i 2 (Trans.Pair.decP (frep R1.blk 1 1 (n+1))))))
          = phi one (iterT zero (n+2))
      rw [decP_frep blkA_decP (n+1) 0, valTower n i 2 (by omega), ofNat_one, phiStep_zero,
        show ((iterT zero (n+1) == zero) = false) from by
          rw [iterT_succ isSC_zero n]; rfl]
      simp only [Bool.false_eq_true, if_false]
      rw [omegaNF_iterT_zero n, phiNF_one_iterT_zero (n+2), omegaNF_phi_ne_zero
        (show (one : Term) ≠ zero from by intro hc; exact Term.noConfusion hc),
        plus_zero_left rfl]

theorem onlyRow0_E (n : Nat) : onlyRow0 ([[0,0],[1,1]] ++ frep R1.blk 1 2 (n+1)) = false := by
  rw [onlyRow0_append]
  rfl

theorem len_E (n : Nat) : ([[0,0],[1,1]] ++ frep R1.blk 1 2 (n+1)).length = n + 3 := by
  rw [List.length_append, R1.frep_len (n+1) 2]
  show 2 + (n+1) = n + 3
  omega

theorem fs_t (k : Nat) : fsN t0 k = phi one (iterT zero k) := by
  show fsN (phi one (phi one zero)) k = _
  rw [fsN_phi_lim (show phiShifted one (phi one zero) = false from rfl)
    (show kindT (phi one zero) = KindT.isLim from rfl) k]
  rw [show fsN (phi one zero) k = iterT zero k from R1.fs_t k]
  exact phiNF_one_iterT_zero k

/-- **E3, part (a)**: the n-th expansion equals the fundamental sequence at n+2. -/
theorem e3_val (n : Nat) : o? (BMS.expand m0 n) = some (fsN t0 (n+2)) := by
  have hE : BMS.expand m0 n = [[0,0],[1,1]] ++ frep R1.blk 1 2 (n+1) := by
    show (BMS.expand? m0 n).getD [] = _
    rw [expand_eq]; rfl
  have hfr : Trans.Pair.inFrag ([[0,0],[1,1]] ++ frep R1.blk 1 2 (n+1)) = true := by
    rw [inFrag_append, inFrag_frep blkA_inFrag (n+1) 2]
    rfl
  rw [hE, o?_pair (onlyRow0_E n) hfr, len_E, val n (n+3+1) 1 (by omega), fs_t]

theorem e3_lt (n : Nat) : lt (fsN t0 (n+2)) t0 = true := by
  rw [fs_t]
  exact lt_phi_iterT_bound isSC_zero (by rfl) ltF_zero_one one (n+2)

/-- **E3, part (b)** with witness `k := n+3`. -/
theorem e3_over (n : Nat) : lt (fsN t0 (n+2)) (fsN t0 (n+3)) = true := by
  rw [fs_t, fs_t]
  exact lt_phi_iterT_succ isSC_zero one (n+2)

/-- **E3, part (c)** with witness `n := k`. -/
theorem e3_under (k : Nat) : lt (fsN t0 (k+1)) (fsN t0 (k+2)) = true := by
  rw [fs_t, fs_t]
  exact lt_phi_iterT_succ isSC_zero one (k+1)

end R5


/-! ## §10 The four rows, packaged in the mutual-cofinality form of plan/README.md

For each row, `oval n` is the (proved) closed form of `o?(M[n])`, `kw` is the
witness function of (b) and `nw` that of (c). -/

namespace R1
def oval (n : Nat) : Term := fsN t0 (n + 1)
theorem e3 :
    (∀ n, o? (BMS.expand m0 n) = some (oval n))
    ∧ (∀ n, lt (oval n) t0 = true)
    ∧ (∀ n, lt (oval n) (fsN t0 (n + 2)) = true)
    ∧ (∀ k, lt (fsN t0 (k + 1)) (oval (k + 1)) = true) :=
  ⟨e3_val, e3_lt, e3_over, fun k => e3_under k⟩
end R1

namespace R5
def oval (n : Nat) : Term := fsN t0 (n + 2)
theorem e3 :
    (∀ n, o? (BMS.expand m0 n) = some (oval n))
    ∧ (∀ n, lt (oval n) t0 = true)
    ∧ (∀ n, lt (oval n) (fsN t0 (n + 3)) = true)
    ∧ (∀ k, lt (fsN t0 (k + 1)) (oval k) = true) :=
  ⟨e3_val, e3_lt, e3_over, fun k => e3_under k⟩
end R5

namespace R6
def oval (n : Nat) : Term := fsN t0 (n + 1)
theorem e3 :
    (∀ n, o? (BMS.expand m0 n) = some (oval n))
    ∧ (∀ n, lt (oval n) t0 = true)
    ∧ (∀ n, lt (oval n) (fsN t0 (n + 2)) = true)
    ∧ (∀ k, lt (fsN t0 (k + 1)) (oval (k + 1)) = true) :=
  ⟨e3_val, e3_lt, e3_over, fun k => e3_under k⟩
end R6

namespace R9
def oval (n : Nat) : Term := fsN t0 (n + 1)
theorem e3 :
    (∀ n, o? (BMS.expand m0 n) = some (oval n))
    ∧ (∀ n, lt (oval n) t0 = true)
    ∧ (∀ n, lt (oval n) (fsN t0 (n + 2)) = true)
    ∧ (∀ k, lt (fsN t0 (k + 1)) (oval (k + 1)) = true) :=
  ⟨e3_val, e3_lt, e3_over, fun k => e3_under k⟩
end R9

/-! ## §11 Sanity checks (finite instances of the proved statements) -/

#guard (List.range 6).all fun n => o? (BMS.expand R1.m0 n) == some (fsN R1.t0 (n + 1))
#guard (List.range 6).all fun n => o? (BMS.expand R5.m0 n) == some (fsN R5.t0 (n + 2))
#guard (List.range 6).all fun n => o? (BMS.expand R6.m0 n) == some (fsN R6.t0 (n + 1))
#guard (List.range 6).all fun n => o? (BMS.expand R9.m0 n) == some (fsN R9.t0 (n + 1))

-- the rows are E1 rows of Rows/TM.lean
#guard o? R1.m0 == some R1.t0
#guard o? R5.m0 == some R5.t0
#guard o? R6.m0 == some R6.t0
#guard o? R9.m0 == some R9.t0

/-! ## §12 Runs of `(0,1)` columns

The five remaining Stage-B rows all contain a run of columns `(0,1)`, on which
`blocksP` produces one block per column and `oLAux` folds an accumulator with
`phiStep`.  The value of such a run at level `k` is `φ̄(k, m)` for `m` the number
of columns, which needs the shape of `ofNat` under `splitFin` and `logPhi`. -/

theorem filter_le_one : ∀ n,
    (List.replicate n one).filter (fun a => le one a) = List.replicate n one
  | 0 => rfl
  | n + 1 => by
    show (List.filter (fun a => le one a) (one :: List.replicate n one)) = _
    rw [List.filter_cons, show le one one = true from rfl]
    simp only [if_true]
    rw [filter_le_one n]
    rfl

theorem takeWhile_replicate_one : ∀ n,
    (List.replicate n one).takeWhile (fun a => a == one) = List.replicate n one
  | 0 => rfl
  | n + 1 => by
    show (List.takeWhile (fun a => a == one) (one :: List.replicate n one)) = _
    rw [List.takeWhile_cons, show ((one : Term) == one) = true from rfl]
    simp only [if_true]
    rw [takeWhile_replicate_one n]
    rfl

theorem toList_ofNat : ∀ n, toList (ofNat n) = List.replicate n one
  | 0 => rfl
  | n + 1 => by
    show toList (plus (ofNat n) one) = List.replicate (n + 1) one
    unfold plus
    rw [show toList (one : Term) = [one] from rfl]
    show toList (ofList ((toList (ofNat n)).filter (fun a => le one a) ++ [one])) = _
    rw [toList_ofNat n, filter_le_one n, ← List.replicate_succ']
    exact toList_ofList (fun x hx => by rw [List.eq_of_mem_replicate hx]; rfl)

theorem splitFin_ofNat (n : Nat) : splitFin (ofNat n) = (zero, n) := by
  show (ofList ((toList (ofNat n)).take
        ((toList (ofNat n)).length - ((toList (ofNat n)).reverse.takeWhile (fun a => a == one)).length)),
      ((toList (ofNat n)).reverse.takeWhile (fun a => a == one)).length) = (zero, n)
  rw [toList_ofNat n, List.reverse_replicate, takeWhile_replicate_one n]
  simp [ofList]

theorem mulNat_one_ofNat : ∀ n, mulNat one n = ofNat n
  | 0 => rfl
  | n + 1 => by
    show ofList (List.replicate (n + 1) one) = plus (ofNat n) one
    unfold plus
    rw [show toList (one : Term) = [one] from rfl]
    show _ = ofList ((toList (ofNat n)).filter (fun a => le one a) ++ [one])
    rw [toList_ofNat n, filter_le_one n, ← List.replicate_succ']

theorem isSC_ofNat : ∀ n, (ofNat n).isSC = false
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    rw [← mulNat_one_ofNat]
    show (ofList (List.replicate (n + 2) one)).isSC = false
    rfl

theorem phiShifted_of_splitFin_zero {a b : Term} (ha : a.isSC = false)
    (h : (splitFin b).1 = zero) : phiShifted a b = false := by
  unfold phiShifted
  rw [h]
  unfold isFP
  rw [ha]
  simp [isSC]

theorem phiShifted_ofNat {a : Term} (ha : a.isSC = false) (n : Nat) :
    phiShifted a (ofNat n) = false :=
  phiShifted_of_splitFin_zero ha (by rw [splitFin_ofNat])

/-- `phiNF a` is the raw constructor on the finite terms `ofNat n`. -/
theorem phiNF_ofNat {a : Term} (ha : a.isSC = false) (n : Nat) :
    phiNF a (ofNat n) = phi a (ofNat n) := by
  cases n with
  | zero => exact phiNF_zero_arg ha
  | succ m =>
    cases m with
    | zero => exact phiNF_one_arg ha
    | succ j =>
      have hshape : ofNat (j + 2) = add one (ofNat (j + 1)) := by
        rw [← mulNat_one_ofNat, ← mulNat_one_ofNat]
        show ofList (List.replicate (j + 2) one) = add one (ofList (List.replicate (j + 1) one))
        rfl
      have hsp : splitFin (ofNat (j + 2)) = (zero, j + 2) := splitFin_ofNat (j + 2)
      rw [hshape] at hsp ⊢
      unfold phiNF
      simp only [isSC, Bool.false_and, Bool.false_eq_true, if_false]
      unfold phiNFsucc
      rw [hsp]
      show (if ((zero : Term).isSC && lt a zero) = true then phi a (plus zero (ofNat (j+2-1)))
            else phiNFdefault a (add one (ofNat (j+1)))) = phi a (add one (ofNat (j+1)))
      simp only [isSC, Bool.false_and, Bool.false_eq_true, if_false]
      exact phiNFdefault_phi ha

theorem logPhi_phi_ofNat (j i : Nat) :
    Trans.Pair.logPhi (ofNat j) (phi (ofNat j) (ofNat i)) = some (ofNat i) := by
  show (if ((ofNat j : Term) == ofNat j) = true then
      some (if phiShifted (ofNat j) (ofNat i) then plus (ofNat i) one else ofNat i)
    else _) = _
  rw [show (((ofNat j : Term)) == ofNat j) = true from beq_self_eq_true _]
  simp only [if_true, phiShifted_ofNat (isSC_ofNat j) i, Bool.false_eq_true, if_false]

/-- One `(0,1)` column at level `j` raises the last Veblen argument by one. -/
theorem phiStep_succ (j i : Nat) :
    Trans.Pair.phiStep (ofNat j) (phi (ofNat j) (ofNat i)) zero = phi (ofNat j) (ofNat (i + 1)) := by
  unfold Trans.Pair.phiStep
  rw [logPhi_phi_ofNat j i]
  show phiNF (ofNat j) (plus (ofNat i) one) = _
  rw [show plus (ofNat i) one = ofNat (i + 1) from rfl]
  exact phiNF_ofNat (isSC_ofNat j) (i + 1)

theorem phiStep_start (j : Nat) :
    Trans.Pair.phiStep (ofNat j) zero zero = phi (ofNat j) (ofNat 0) := by
  rw [phiStep_zero]
  simp only [show ((zero : Term) == zero) = true from rfl, if_true]
  exact phiNF_zero_arg (isSC_ofNat j)


/-- `k` copies of the column `(0,1)`, `(1,1)`, `(2,1)`. -/
def zs (k : Nat) : Matrix := List.replicate k ([0,1] : BMS.Col)
def ones (k : Nat) : Matrix := List.replicate k ([1,1] : BMS.Col)
def twos (k : Nat) : Matrix := List.replicate k ([2,1] : BMS.Col)

theorem decP_ones (k : Nat) : Trans.Pair.decP (ones k) = zs k := by
  show (List.replicate k ([1,1] : BMS.Col)).map _ = _
  rw [List.map_replicate]
  rfl

theorem decP_twos (k : Nat) : Trans.Pair.decP (twos k) = ones k := by
  show (List.replicate k ([2,1] : BMS.Col)).map _ = _
  rw [List.map_replicate]
  rfl

theorem blocksP_cons_zero (c h : BMS.Col) (t : List BMS.Col) (hz : Trans.Pair.r0 h = 0) :
    Trans.Pair.blocksP (c :: h :: t) = [c] :: Trans.Pair.blocksP (h :: t) := by
  show (if Trans.Pair.r0 h == 0 then [c] :: Trans.Pair.blocksP (h :: t)
        else (c :: (Trans.Pair.blocksP (h :: t)).headD []) ::
          (Trans.Pair.blocksP (h :: t)).tail) = _
  rw [show (Trans.Pair.r0 h == 0) = true from by rw [hz]; rfl]
  rfl

theorem blocksP_cons_nz (c h : BMS.Col) (t : List BMS.Col) (hz : Trans.Pair.r0 h ≠ 0) :
    Trans.Pair.blocksP (c :: h :: t)
      = (c :: (Trans.Pair.blocksP (h :: t)).headD []) :: (Trans.Pair.blocksP (h :: t)).tail := by
  show (match Trans.Pair.blocksP (h :: t), (h :: t).head? with
        | acc, some hh =>
          if Trans.Pair.r0 hh == 0 then [c] :: acc else (c :: acc.headD []) :: acc.tail
        | _, none => [[c]]) = _
  simp [hz]

theorem blocksP_zs : ∀ k, Trans.Pair.blocksP (zs (k+1)) = List.replicate (k+1) ([[0,1]] : Matrix)
  | 0 => rfl
  | k + 1 => by
    show Trans.Pair.blocksP (([0,1] : BMS.Col) :: (([0,1] : BMS.Col) :: zs k)) = _
    rw [blocksP_cons_zero [0,1] [0,1] (zs k) rfl]
    show ([[0,1]] : Matrix) :: Trans.Pair.blocksP (zs (k+1)) = _
    rw [blocksP_zs k]
    rfl

/-- The fold step of `oLAux` at fuel `g` and level `k`, named for rewriting. -/
def zsF (g k : Nat) (acc : Term) (b : Matrix) : Term :=
  match b with
  | [] => acc
  | c :: t =>
    if Trans.Pair.r1 c == 0 then plus acc (omegaNF (Trans.Pair.oLAux g 1 (Trans.Pair.decP t)))
    else Trans.Pair.phiStep (ofNat k) acc (Trans.Pair.oLAux g (k + 1) (Trans.Pair.decP t))

theorem oLAux_cons' (g k : Nat) (s : List BMS.Col) :
    Trans.Pair.oLAux (g + 1) k s = (Trans.Pair.blocksP s).foldl (zsF g k) zero := rfl

theorem zsF_step (g k : Nat) (acc : Term) :
    zsF g k acc [[0,1]] = Trans.Pair.phiStep (ofNat k) acc zero := by
  show Trans.Pair.phiStep (ofNat k) acc (Trans.Pair.oLAux g (k + 1) (Trans.Pair.decP [])) = _
  rw [show Trans.Pair.decP ([] : List BMS.Col) = [] from rfl, oLAux_nil]

theorem foldl_zs (g k : Nat) : ∀ (m i : Nat),
    (List.replicate m ([[0,1]] : Matrix)).foldl (zsF g k) (phi (ofNat k) (ofNat i))
      = phi (ofNat k) (ofNat (i + m))
  | 0, _ => rfl
  | m + 1, i => by
    rw [List.replicate_succ, List.foldl_cons, zsF_step, phiStep_succ, foldl_zs g k m (i+1)]
    congr 2
    omega

/-- A run of `m+1` columns `(0,1)` read at level `k` is `φ̄(k, m)`. -/
theorem oLAux_zs (m fuel k : Nat) (hf : 1 ≤ fuel) :
    Trans.Pair.oLAux fuel k (zs (m+1)) = phi (ofNat k) (ofNat m) := by
  cases fuel with
  | zero => omega
  | succ g =>
    rw [oLAux_cons', blocksP_zs m, List.replicate_succ, List.foldl_cons, zsF_step,
      phiStep_start, foldl_zs g k m 0]
    congr 2
    omega


/-! ### Order facts about the finite terms `ofNat n` -/

theorem ofNat_shape : ∀ n, ofNat (n+2) = add one (ofNat (n+1)) := by
  intro n
  rw [← mulNat_one_ofNat, ← mulNat_one_ofNat]
  show ofList (List.replicate (n+2) one) = add one (ofList (List.replicate (n+1) one))
  rfl

theorem deg_ofNat : ∀ n, n ≤ (ofNat n).deg
  | 0 => by simp [ofNat, deg]
  | 1 => by rw [ofNat_one]; show (1:Nat) ≤ 3; omega
  | n + 2 => by
    rw [ofNat_shape n]
    show n + 2 ≤ 1 + (one : Term).deg + (ofNat (n+1)).deg
    have := deg_ofNat (n+1)
    show n + 2 ≤ 1 + 3 + (ofNat (n+1)).deg
    omega

theorem ltF_ofNat_succ : ∀ (n f : Nat), n + 2 ≤ f → ltF f (ofNat n) (ofNat (n+1)) = true
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
      have hne : ltF g (ofNat (n+1)) (ofNat (n+2)) = true := by
        have := ltF_ofNat_succ (n+1) g (by omega)
        exact this
      rw [show ((add one (ofNat (n+1)) == add one (ofNat (n+2))) = false) from by
        simp [ne_of_ltF hne]]
      simp [hne]

theorem ltF_one_omega : ∀ f, 2 ≤ f → ltF f one omega = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g =>
    show (if ((one : Term) == omega) = true then false
          else if ((zero : Term) == zero) = true then ltF g zero one else ltF g zero zero) = true
    simp only [show (((one : Term)) == omega) = false from rfl, Bool.false_eq_true, if_false,
      beq_self_eq_true, if_true]
    exact ltF_zero (by omega) (by intro hc; exact Term.noConfusion hc)

theorem ltF_ofNat_omega : ∀ (n f : Nat), 3 ≤ f → ltF f (ofNat n) omega = true
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

theorem lt_phi_same_of {a x y : Term} {N : Nat} (h : ∀ f, N ≤ f → ltF f x y = true)
    (hN : N + 1 ≤ 2 * ((phi a x).deg + (phi a y).deg) + 8) : lt (phi a x) (phi a y) = true := by
  refine lt_of_ltF (N := N + 1) (fun f hf => ?_) hN
  cases f with
  | zero => omega
  | succ g => exact ltF_phi_same (h g (by omega))

/-! ### The two "one step behind" rows: a constant `(0,1)`-run at level 1 resp. 2 -/

theorem inFrag_cons (c : BMS.Col) (l : Matrix) :
    Trans.Pair.inFrag (c :: l)
      = ((decide (c.length ≤ 2) && decide (Trans.Pair.r1 c ≤ 1)) && Trans.Pair.inFrag l) :=
  List.all_cons

theorem onlyRow0_cons (c : BMS.Col) (l : Matrix) :
    onlyRow0 (c :: l) = ((c.drop 1).all (· == 0) && onlyRow0 l) := List.all_cons

theorem inFrag_ones : ∀ k, Trans.Pair.inFrag (ones k) = true
  | 0 => rfl
  | k + 1 => by
    show Trans.Pair.inFrag (([1,1] : BMS.Col) :: ones k) = true
    rw [inFrag_cons, inFrag_ones k]
    rfl

theorem inFrag_twos : ∀ k, Trans.Pair.inFrag (twos k) = true
  | 0 => rfl
  | k + 1 => by
    show Trans.Pair.inFrag (([2,1] : BMS.Col) :: twos k) = true
    rw [inFrag_cons, inFrag_twos k]
    rfl

theorem onlyRow0_ones (k : Nat) : onlyRow0 (ones (k+1)) = false := by
  show onlyRow0 (([1,1] : BMS.Col) :: ones k) = false
  rw [onlyRow0_cons]
  rfl

theorem r0_ones (k : Nat) : ∀ c ∈ ones k, Trans.Pair.r0 c ≠ 0 := by
  intro c hc
  rw [List.eq_of_mem_replicate hc]
  show (1 : Nat) ≠ 0
  omega

theorem r0_twos (k : Nat) : ∀ c ∈ twos k, Trans.Pair.r0 c ≠ 0 := by
  intro c hc
  rw [List.eq_of_mem_replicate hc]
  show (2 : Nat) ≠ 0
  omega

theorem repM_ones : ∀ k, repM ([[1,1]] : Matrix) k = ones k
  | 0 => rfl
  | k + 1 => by
    show ([1,1] : BMS.Col) :: repM ([[1,1]] : Matrix) k = ones (k+1)
    rw [repM_ones k]
    rfl

theorem repM_twos : ∀ k, repM ([[2,1]] : Matrix) k = twos k
  | 0 => rfl
  | k + 1 => by
    show ([2,1] : BMS.Col) :: repM ([[2,1]] : Matrix) k = twos (k+1)
    rw [repM_twos k]
    rfl

theorem fs_omega' (k : Nat) : fsN omega k = ofNat k := by
  have h : fsN (phi zero one) k = mulNat one k := by rw [fsN]; rfl
  show fsN (phi zero one) k = ofNat k
  rw [h, mulNat_one_ofNat]


/-! ## §13 Row `(0,0)(1,1)(2,0)` = ε_ω = φ̄(1,ω)

`M[n] = (0,0)(1,1)^{n+1}`, value `φ̄(1,n)`.  Here the expansion runs one step
BEHIND the fundamental sequence: `o(M[n]) = fsN t n`. -/

namespace R4

def m0 : Matrix := [[0,0],[1,1],[2,0]]
def t0 : Term := phi one omega

theorem raw_eq (a : Nat) : ([[1 + a*0*1, 1 + a*0*1]] : Matrix) = [[1,1]] := by
  have h1 : 1 + a*0*1 = 1 := by omega
  rw [h1]

theorem expand_eq (n : Nat) : BMS.expand? m0 n = some ([[0,0]] ++ ones (n+1)) := by
  have h : BMS.expand? m0 n
      = some ([[0,0]] ++ ((List.range (n+1)).map
          (fun a => ([[1 + a*0*1, 1 + a*0*1]] : Matrix))).flatten) := rfl
  rw [h, List.map_congr_left (fun a _ => raw_eq a), flat_range, repM_ones]

theorem val (n fuel k : Nat) (hf : 2 ≤ fuel) :
    Trans.Pair.oLAux fuel k ([[0,0]] ++ ones (n+1)) = phi one (ofNat n) := by
  cases fuel with
  | zero => omega
  | succ g =>
    have hE : ([[0,0]] ++ ones (n+1)) = ([0,0] : BMS.Col) :: ones (n+1) := rfl
    rw [hE, oLAux_single g k [0,0] _ (r0_ones (n+1))]
    show plus zero (omegaNF (Trans.Pair.oLAux g 1 (Trans.Pair.decP (ones (n+1)))))
        = phi one (ofNat n)
    rw [decP_ones, oLAux_zs n g 1 (by omega), ofNat_one,
      omegaNF_phi_ne_zero (show (one : Term) ≠ zero from by intro hc; exact Term.noConfusion hc),
      plus_zero_left rfl]

theorem onlyRow0_E (n : Nat) : onlyRow0 ([[0,0]] ++ ones (n+1)) = false := by
  show onlyRow0 (([0,0] : BMS.Col) :: ones (n+1)) = false
  rw [onlyRow0_cons, onlyRow0_ones n]
  rfl

theorem inFrag_E (n : Nat) : Trans.Pair.inFrag ([[0,0]] ++ ones (n+1)) = true := by
  show Trans.Pair.inFrag (([0,0] : BMS.Col) :: ones (n+1)) = true
  rw [inFrag_cons, inFrag_ones (n+1)]
  rfl

theorem len_E (n : Nat) : ([[0,0]] ++ ones (n+1)).length = n + 2 := by
  show (([0,0] : BMS.Col) :: ones (n+1)).length = n + 2
  simp [ones]

theorem fs_t (k : Nat) : fsN t0 k = phi one (ofNat k) := by
  show fsN (phi one omega) k = _
  rw [fsN_phi_lim (show phiShifted one omega = false from rfl)
    (show kindT omega = KindT.isLim from rfl) k, fs_omega' k]
  exact phiNF_ofNat isSC_one k

/-- **E3, part (a)**: the n-th expansion is the fundamental sequence at n (one behind). -/
theorem e3_val (n : Nat) : o? (BMS.expand m0 n) = some (fsN t0 n) := by
  have hE : BMS.expand m0 n = [[0,0]] ++ ones (n+1) := by
    show (BMS.expand? m0 n).getD [] = _
    rw [expand_eq]; rfl
  rw [hE, o?_pair (onlyRow0_E n) (inFrag_E n), len_E, val n (n+2+1) 1 (by omega), fs_t]

theorem e3_lt (n : Nat) : lt (fsN t0 n) t0 = true := by
  rw [fs_t]
  show lt (phi one (ofNat n)) (phi one omega) = true
  refine lt_phi_same_of (N := 3) (fun f hf => ltF_ofNat_omega n f hf) ?_
  show 3 + 1 ≤ 2 * ((phi one (ofNat n)).deg + (phi one omega).deg) + 8
  omega

/-- **E3, part (b)** with witness `k := n+1`. -/
theorem e3_over (n : Nat) : lt (fsN t0 n) (fsN t0 (n+1)) = true := by
  rw [fs_t, fs_t]
  refine lt_phi_same_of (N := n+2) (fun f hf => ltF_ofNat_succ n f hf) ?_
  have h1 := deg_ofNat n
  show n + 2 + 1 ≤ 2 * ((1 + (one : Term).deg + (ofNat n).deg)
    + (1 + (one : Term).deg + (ofNat (n+1)).deg)) + 8
  omega

/-- **E3, part (c)** with witness `n := k+2`. -/
theorem e3_under (k : Nat) : lt (fsN t0 (k+1)) (fsN t0 (k+2)) = true := e3_over (k+1)

def oval (n : Nat) : Term := fsN t0 n

theorem e3 :
    (∀ n, o? (BMS.expand m0 n) = some (oval n))
    ∧ (∀ n, lt (oval n) t0 = true)
    ∧ (∀ n, lt (oval n) (fsN t0 (n + 1)) = true)
    ∧ (∀ k, lt (fsN t0 (k + 1)) (oval (k + 2)) = true) :=
  ⟨e3_val, e3_lt, e3_over, fun k => e3_under k⟩

end R4

/-! ## §14 Row `(0,0)(1,1)(2,1)(3,0)` = ζ_ω = φ̄(2,ω)

`M[n] = (0,0)(1,1)(2,1)^{n+1}`, value `φ̄(2,n)`; again one step behind. -/

namespace R8

def m0 : Matrix := [[0,0],[1,1],[2,1],[3,0]]
def t0 : Term := phi (ofNat 2) omega

theorem raw_eq (a : Nat) : ([[2 + a*0*1, 1 + a*0*1]] : Matrix) = [[2,1]] := by
  have h1 : 2 + a*0*1 = 2 := by omega
  have h2 : 1 + a*0*1 = 1 := by omega
  rw [h1, h2]

theorem expand_eq (n : Nat) : BMS.expand? m0 n = some ([[0,0],[1,1]] ++ twos (n+1)) := by
  have h : BMS.expand? m0 n
      = some ([[0,0],[1,1]] ++ ((List.range (n+1)).map
          (fun a => ([[2 + a*0*1, 1 + a*0*1]] : Matrix))).flatten) := rfl
  rw [h, List.map_congr_left (fun a _ => raw_eq a), flat_range, repM_twos]

theorem val (n fuel k : Nat) (hf : 3 ≤ fuel) :
    Trans.Pair.oLAux fuel k ([[0,0],[1,1]] ++ twos (n+1)) = phi (ofNat 2) (ofNat n) := by
  cases fuel with
  | zero => omega
  | succ g =>
    cases g with
    | zero => omega
    | succ i =>
      have hE : ([[0,0],[1,1]] ++ twos (n+1))
          = ([0,0] : BMS.Col) :: (([1,1] : BMS.Col) :: twos (n+1)) := rfl
      have ht : ∀ c ∈ (([1,1] : BMS.Col) :: twos (n+1)), Trans.Pair.r0 c ≠ 0 := by
        intro c hc
        rcases List.mem_cons.mp hc with h1 | h1
        · subst h1; show (1:Nat) ≠ 0; omega
        · exact r0_twos (n+1) c h1
      rw [hE, oLAux_single (i+1) k [0,0] _ ht]
      show plus zero (omegaNF (Trans.Pair.oLAux (i+1) 1
        (Trans.Pair.decP (([1,1] : BMS.Col) :: twos (n+1))))) = phi (ofNat 2) (ofNat n)
      have hd : Trans.Pair.decP (([1,1] : BMS.Col) :: twos (n+1))
          = ([0,1] : BMS.Col) :: ones (n+1) := by
        show ([0,1] : BMS.Col) :: Trans.Pair.decP (twos (n+1)) = _
        rw [decP_twos]
      rw [hd, oLAux_single i 1 [0,1] _ (r0_ones (n+1))]
      show plus zero (omegaNF (Trans.Pair.phiStep (ofNat 1) zero
        (Trans.Pair.oLAux i 2 (Trans.Pair.decP (ones (n+1)))))) = phi (ofNat 2) (ofNat n)
      rw [decP_ones, oLAux_zs n i 2 (by omega), ofNat_one, phiStep_zero,
        show ((phi (ofNat 2) (ofNat n) == zero) = false) from rfl]
      simp only [Bool.false_eq_true, if_false]
      have hne2 : (ofNat 2 : Term) ≠ zero := by intro hc; exact Term.noConfusion hc
      rw [omegaNF_phi_ne_zero hne2, phiNF_collapse R9.lt_one_two,
        omegaNF_phi_ne_zero hne2, plus_zero_left rfl]

theorem onlyRow0_E (n : Nat) : onlyRow0 ([[0,0],[1,1]] ++ twos (n+1)) = false := by
  rw [onlyRow0_append]
  rfl

theorem inFrag_E (n : Nat) : Trans.Pair.inFrag ([[0,0],[1,1]] ++ twos (n+1)) = true := by
  rw [inFrag_append, inFrag_twos (n+1)]
  rfl

theorem len_E (n : Nat) : ([[0,0],[1,1]] ++ twos (n+1)).length = n + 3 := by
  rw [List.length_append]
  simp [twos]
  omega

theorem fs_t (k : Nat) : fsN t0 k = phi (ofNat 2) (ofNat k) := by
  show fsN (phi (ofNat 2) omega) k = _
  rw [fsN_phi_lim (show phiShifted (ofNat 2) omega = false from rfl)
    (show kindT omega = KindT.isLim from rfl) k, fs_omega' k]
  exact phiNF_ofNat isSC_two k

theorem e3_val (n : Nat) : o? (BMS.expand m0 n) = some (fsN t0 n) := by
  have hE : BMS.expand m0 n = [[0,0],[1,1]] ++ twos (n+1) := by
    show (BMS.expand? m0 n).getD [] = _
    rw [expand_eq]; rfl
  rw [hE, o?_pair (onlyRow0_E n) (inFrag_E n), len_E, val n (n+3+1) 1 (by omega), fs_t]

theorem e3_lt (n : Nat) : lt (fsN t0 n) t0 = true := by
  rw [fs_t]
  show lt (phi (ofNat 2) (ofNat n)) (phi (ofNat 2) omega) = true
  refine lt_phi_same_of (N := 3) (fun f hf => ltF_ofNat_omega n f hf) ?_
  show 3 + 1 ≤ 2 * ((phi (ofNat 2) (ofNat n)).deg + (phi (ofNat 2) omega).deg) + 8
  omega

theorem e3_over (n : Nat) : lt (fsN t0 n) (fsN t0 (n+1)) = true := by
  rw [fs_t, fs_t]
  refine lt_phi_same_of (N := n+2) (fun f hf => ltF_ofNat_succ n f hf) ?_
  have h1 := deg_ofNat n
  show n + 2 + 1 ≤ 2 * ((1 + (ofNat 2 : Term).deg + (ofNat n).deg)
    + (1 + (ofNat 2 : Term).deg + (ofNat (n+1)).deg)) + 8
  omega

theorem e3_under (k : Nat) : lt (fsN t0 (k+1)) (fsN t0 (k+2)) = true := e3_over (k+1)

def oval (n : Nat) : Term := fsN t0 n

theorem e3 :
    (∀ n, o? (BMS.expand m0 n) = some (oval n))
    ∧ (∀ n, lt (oval n) t0 = true)
    ∧ (∀ n, lt (oval n) (fsN t0 (n + 1)) = true)
    ∧ (∀ k, lt (fsN t0 (k + 1)) (oval (k + 2)) = true) :=
  ⟨e3_val, e3_lt, e3_over, fun k => e3_under k⟩

end R8


/-! ## §15 Row `(0,0)(1,1)(1,0)` = ω^{ε₀+1} = φ̄(0,ε₀)

`M[n] = ((0,0)(1,1))^{n+1}`: n+1 blocks, each contributing a summand ε₀, so the
value is `ε₀·(n+1) = fsN (φ̄(0,ε₀)) (n+1)`. -/

/-- `k` copies of the two-column block `(0,0)(1,1)`. -/
def pairs : Nat → Matrix
  | 0 => []
  | k + 1 => ([0,0] : BMS.Col) :: (([1,1] : BMS.Col) :: pairs k)

theorem repM_pairs : ∀ k, repM ([[0,0],[1,1]] : Matrix) k = pairs k
  | 0 => rfl
  | k + 1 => by
    show ([0,0] : BMS.Col) :: (([1,1] : BMS.Col) :: repM ([[0,0],[1,1]] : Matrix) k) = pairs (k+1)
    rw [repM_pairs k]
    rfl

theorem blocksP_pairs : ∀ k,
    Trans.Pair.blocksP (pairs k) = List.replicate k ([[0,0],[1,1]] : Matrix)
  | 0 => rfl
  | k + 1 => by
    have hinner : Trans.Pair.blocksP (([1,1] : BMS.Col) :: pairs k)
        = ([[1,1]] : Matrix) :: Trans.Pair.blocksP (pairs k) := by
      cases k with
      | zero => rfl
      | succ j => exact blocksP_cons_zero [1,1] [0,0] (([1,1] : BMS.Col) :: pairs j) rfl
    show Trans.Pair.blocksP (([0,0] : BMS.Col) :: (([1,1] : BMS.Col) :: pairs k)) = _
    rw [blocksP_cons_nz [0,0] [1,1] (pairs k) (by show (1:Nat) ≠ 0; omega), hinner,
      blocksP_pairs k]
    rfl

theorem filter_le_self (a : Term) : ∀ i,
    (List.replicate i a).filter (fun x => le a x) = List.replicate i a
  | 0 => rfl
  | i + 1 => by
    show (List.filter (fun x => le a x) (a :: List.replicate i a)) = _
    rw [List.filter_cons, Evidence.StageA.le_self a]
    simp only [if_true]
    rw [filter_le_self a i]
    rfl

theorem toList_mulNat {a : Term} (ha : a.isAP = true) (i : Nat) :
    toList (mulNat a i) = List.replicate i a :=
  toList_ofList (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact ha)

theorem plus_mulNat {a : Term} (ha : a.isAP = true) (i : Nat) :
    plus (mulNat a i) a = mulNat a (i+1) := by
  unfold plus
  rw [toList_of_isAP ha]
  show ofList ((toList (mulNat a i)).filter (fun x => le a x) ++ [a]) = mulNat a (i+1)
  rw [toList_mulNat ha i, filter_le_self a i, ← List.replicate_succ']
  rfl

theorem zsF_pair (g k : Nat) (hg : 1 ≤ g) (acc : Term) :
    zsF g k acc [[0,0],[1,1]] = plus acc (phi one zero) := by
  show plus acc (omegaNF (Trans.Pair.oLAux g 1 (Trans.Pair.decP [[1,1]]))) = _
  rw [show Trans.Pair.decP ([[1,1]] : Matrix) = zs 1 from rfl, oLAux_zs 0 g 1 hg, ofNat_one,
    omegaNF_phi_ne_zero (show (one : Term) ≠ zero from by intro hc; exact Term.noConfusion hc)]
  rfl

theorem isAP_e0 : (phi one zero).isAP = true := rfl

theorem foldl_pairs (g k : Nat) (hg : 1 ≤ g) : ∀ (m i : Nat),
    (List.replicate m ([[0,0],[1,1]] : Matrix)).foldl (zsF g k) (mulNat (phi one zero) i)
      = mulNat (phi one zero) (i + m)
  | 0, _ => rfl
  | m + 1, i => by
    rw [List.replicate_succ, List.foldl_cons, zsF_pair g k hg, plus_mulNat isAP_e0 i,
      foldl_pairs g k hg m (i+1)]
    congr 1
    omega

theorem oLAux_pairs (m fuel k : Nat) (hf : 2 ≤ fuel) :
    Trans.Pair.oLAux fuel k (pairs m) = mulNat (phi one zero) m := by
  cases fuel with
  | zero => omega
  | succ g =>
    rw [oLAux_cons', blocksP_pairs m]
    have h := foldl_pairs g k (by omega) m 0
    rw [show mulNat (phi one zero) 0 = zero from rfl] at h
    rw [h]
    congr 1
    omega

namespace R2

def m0 : Matrix := [[0,0],[1,1],[1,0]]
def t0 : Term := phi zero (phi one zero)

theorem raw_eq (a : Nat) :
    ([[0 + a*0*1, 0 + a*0*1], [1 + a*0*1, 1 + a*0*1]] : Matrix) = [[0,0],[1,1]] := by
  have h1 : 0 + a*0*1 = 0 := by omega
  have h2 : 1 + a*0*1 = 1 := by omega
  rw [h1, h2]

theorem expand_eq (n : Nat) : BMS.expand? m0 n = some (pairs (n+1)) := by
  have h : BMS.expand? m0 n
      = some (((List.range (n+1)).map
          (fun a => ([[0 + a*0*1, 0 + a*0*1], [1 + a*0*1, 1 + a*0*1]] : Matrix))).flatten) := rfl
  rw [h, List.map_congr_left (fun a _ => raw_eq a), flat_range, repM_pairs]

theorem onlyRow0_pairs (n : Nat) : onlyRow0 (pairs (n+1)) = false := by
  show onlyRow0 (([0,0] : BMS.Col) :: (([1,1] : BMS.Col) :: pairs n)) = false
  rw [onlyRow0_cons, onlyRow0_cons]
  rfl

theorem inFrag_pairs : ∀ k, Trans.Pair.inFrag (pairs k) = true
  | 0 => rfl
  | k + 1 => by
    show Trans.Pair.inFrag (([0,0] : BMS.Col) :: (([1,1] : BMS.Col) :: pairs k)) = true
    rw [inFrag_cons, inFrag_cons, inFrag_pairs k]
    rfl

theorem len_pairs : ∀ k, (pairs k).length = 2 * k
  | 0 => rfl
  | k + 1 => by
    show (([0,0] : BMS.Col) :: (([1,1] : BMS.Col) :: pairs k)).length = 2 * (k+1)
    rw [List.length_cons, List.length_cons, len_pairs k]
    omega

theorem fs_t (k : Nat) : fsN t0 k = mulNat (phi one zero) k := by
  show fsN (phi zero (phi one zero)) k = _
  rw [fsN]
  simp only [show phiShifted zero (phi one zero) = true from rfl, Bool.true_or, if_true]
  show mulNat (omegaNF (phi one zero)) k = mulNat (phi one zero) k
  rw [omegaNF_phi_ne_zero (show (one : Term) ≠ zero from by intro hc; exact Term.noConfusion hc)]

theorem e3_val (n : Nat) : o? (BMS.expand m0 n) = some (fsN t0 (n+1)) := by
  have hE : BMS.expand m0 n = pairs (n+1) := by
    show (BMS.expand? m0 n).getD [] = _
    rw [expand_eq]; rfl
  rw [hE, o?_pair (onlyRow0_pairs n) (inFrag_pairs (n+1)), len_pairs,
    oLAux_pairs (n+1) (2*(n+1)+1) 1 (by omega), fs_t]

end R2


theorem mulNat_one_eq (a : Term) : mulNat a 1 = a := rfl

theorem mulNat_succ2 (a : Term) (k : Nat) : mulNat a (k+2) = add a (mulNat a (k+1)) := rfl

theorem deg_mulNat_e0 : ∀ k, k ≤ (mulNat (phi one zero) k).deg
  | 0 => by show (0:Nat) ≤ 1; omega
  | 1 => by rw [mulNat_one_eq]; show (1:Nat) ≤ 5; omega
  | k + 2 => by
    rw [mulNat_succ2]
    show k + 2 ≤ 1 + 5 + (mulNat (phi one zero) (k+1)).deg
    have := deg_mulNat_e0 (k+1)
    omega

theorem ltF_e0_pow (g : Nat) : ltF (g+1) (phi one zero) (phi zero (phi one zero)) = true := by
  show (if ((phi one zero : Term) == phi zero (phi one zero)) = true then false
        else if ((one : Term) == zero) = true then ltF g zero (phi one zero)
        else if ltF g one zero = true then ltF g zero (phi zero (phi one zero))
        else ((phi one zero : Term) == phi one zero) || ltF g (phi one zero) (phi one zero)) = true
  simp [ltF_lt_zero]
  exact Or.inl (by intro hc; exact Term.noConfusion hc)

theorem ltF_mulNat_e0_pow : ∀ (k f : Nat), 2 ≤ f →
    ltF f (mulNat (phi one zero) k) (phi zero (phi one zero)) = true
  | 0, f, hf => ltF_zero (by omega) (by intro hc; exact Term.noConfusion hc)
  | 1, f, hf => by
    cases f with
    | zero => omega
    | succ g => exact ltF_e0_pow g
  | k + 2, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      rw [mulNat_succ2]
      show (if (add (phi one zero) (mulNat (phi one zero) (k+1)) == phi zero (phi one zero)) = true
            then false else ltF g (phi one zero) (phi zero (phi one zero))) = true
      simp only [show ((add (phi one zero) (mulNat (phi one zero) (k+1))
          == phi zero (phi one zero)) = false) from rfl, Bool.false_eq_true, if_false]
      cases g with
      | zero => omega
      | succ h => exact ltF_e0_pow h

theorem ltF_mulNat_succ : ∀ (k f : Nat), k + 2 ≤ f →
    ltF f (mulNat (phi one zero) (k+1)) (mulNat (phi one zero) (k+2)) = true
  | 0, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      rw [mulNat_one_eq, mulNat_succ2, mulNat_one_eq]
      show (if ((phi one zero : Term) == add (phi one zero) (phi one zero)) = true then false
            else ((phi one zero : Term) == phi one zero)
              || ltF g (phi one zero) (phi one zero)) = true
      simp
  | k + 1, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      have ih := ltF_mulNat_succ k g (by omega)
      rw [mulNat_succ2, mulNat_succ2]
      show (if (add (phi one zero) (mulNat (phi one zero) (k+1))
              == add (phi one zero) (mulNat (phi one zero) (k+2))) = true then false
            else if ((phi one zero : Term) == phi one zero) = true then
              ltF g (mulNat (phi one zero) (k+1)) (mulNat (phi one zero) (k+2))
            else ltF g (phi one zero) (phi one zero)) = true
      rw [show ((add (phi one zero) (mulNat (phi one zero) (k+1))
          == add (phi one zero) (mulNat (phi one zero) (k+2))) = false) from by
        simp [ne_of_ltF ih]]
      simp [ih]

namespace R2

theorem e3_lt (n : Nat) : lt (fsN t0 (n+1)) t0 = true := by
  rw [fs_t]
  show lt (mulNat (phi one zero) (n+1)) (phi zero (phi one zero)) = true
  refine lt_of_ltF (N := 2) (fun f hf => ltF_mulNat_e0_pow (n+1) f hf) ?_
  show 2 ≤ 2 * ((mulNat (phi one zero) (n+1)).deg + (phi zero (phi one zero)).deg) + 8
  omega

/-- **E3, part (b)** with witness `k := n+2`. -/
theorem e3_over (n : Nat) : lt (fsN t0 (n+1)) (fsN t0 (n+2)) = true := by
  rw [fs_t, fs_t]
  refine lt_of_ltF (N := n+2) (fun f hf => ltF_mulNat_succ n f hf) ?_
  have h1 := deg_mulNat_e0 (n+1)
  show n + 2 ≤ 2 * ((mulNat (phi one zero) (n+1)).deg
    + (mulNat (phi one zero) (n+2)).deg) + 8
  omega

/-- **E3, part (c)** with witness `n := k+1`. -/
theorem e3_under (k : Nat) : lt (fsN t0 (k+1)) (fsN t0 (k+2)) = true := e3_over k

def oval (n : Nat) : Term := fsN t0 (n + 1)

theorem e3 :
    (∀ n, o? (BMS.expand m0 n) = some (oval n))
    ∧ (∀ n, lt (oval n) t0 = true)
    ∧ (∀ n, lt (oval n) (fsN t0 (n + 2)) = true)
    ∧ (∀ k, lt (fsN t0 (k + 1)) (oval (k + 1)) = true) :=
  ⟨e3_val, e3_lt, e3_over, fun k => e3_under k⟩

end R2


/-! ## §16 `ω`-towers over a fixed base

Rows `(0,0)(1,1)(1,1)` and `(0,0)(1,1)(2,1)(2,1)` are the two Stage-B rows whose
expansions and fundamental sequences are genuinely different cofinal sequences:
both are towers `φ̄0(φ̄0(…))` but over different bases. -/

def tow (b : Term) : Nat → Term
  | 0 => b
  | j + 1 => phi zero (tow b j)

theorem tow_phi (b : Term) : ∀ j, tow (phi zero b) j = tow b (j+1)
  | 0 => rfl
  | j + 1 => by
    show phi zero (tow (phi zero b) j) = phi zero (tow b (j+1))
    rw [tow_phi b j]

theorem tow_shape (z : Term) : ∀ j, ∃ y, tow (phi zero z) j = phi zero y
  | 0 => ⟨z, rfl⟩
  | j + 1 => ⟨tow (phi zero z) j, rfl⟩

theorem omegaNF_tow (z : Term) (j : Nat) :
    omegaNF (tow (phi zero z) j) = tow (phi zero z) (j+1) := by
  obtain ⟨y, hy⟩ := tow_shape z j
  rw [hy, omegaNF_phi, phiNF_phi_arg isSC_zero, ← hy]
  rfl

theorem deg_tow (b : Term) : ∀ j, j ≤ (tow b j).deg
  | 0 => by show (0:Nat) ≤ b.deg; omega
  | j + 1 => by
    show j + 1 ≤ 1 + (zero : Term).deg + (tow b j).deg
    have := deg_tow b j
    omega

theorem ltF_tow_mono {x y : Term} {N : Nat} (h : ∀ f, N ≤ f → ltF f x y = true) :
    ∀ (j f : Nat), N + j ≤ f → ltF f (tow x j) (tow y j) = true
  | 0, f, hf => h f (by omega)
  | j + 1, f, hf => by
    cases f with
    | zero => omega
    | succ g => exact ltF_phi_same (ltF_tow_mono h j g (by omega))

theorem plus_drop {a Y : Term} (ha : a.isAP = true) (hY : Y.isAP = true) (h : le Y a = false) :
    plus a Y = Y := by
  unfold plus
  rw [toList_of_isAP hY]
  show ofList ((toList a).filter (fun x => le Y x) ++ [Y]) = Y
  rw [toList_of_isAP ha]
  show ofList ((match le Y a with | true => [a] | false => []) ++ [Y]) = Y
  rw [h]
  rfl

/-! ## §17 Row `(0,0)(1,1)(1,1)` = ε₁ = φ̄(1,1) -/

namespace R3

def m0 : Matrix := [[0,0],[1,1],[1,1]]
def t0 : Term := phi one one
def e0 : Term := phi one zero
/-- Base of the expansion tower: `ω^{ε₀·2}`. -/
def P0 : Term := phi zero (add e0 e0)
/-- Base of the fundamental-sequence tower: `ω^{ε₀+1}`. -/
def Q0 : Term := phi zero e0

theorem raw_eq (a : Nat) :
    ([[0 + a*1*1, 0 + a*0*1], [1 + a*1*1, 1 + a*0*1]] : Matrix) = R6.blk (1 * a + 0) := by
  show _ = ([[1*a+0, 0], [1*a+0+1, 1]] : Matrix)
  have h1 : 0 + a*1*1 = 1*a+0 := by omega
  have h2 : 0 + a*0*1 = 0 := by omega
  have h3 : 1 + a*1*1 = 1*a+0+1 := by omega
  have h4 : 1 + a*0*1 = 1 := by omega
  rw [h1, h2, h3, h4]

theorem expand_eq (n : Nat) : BMS.expand? m0 n = some (frep R6.blk 1 0 (n+1)) := by
  have h : BMS.expand? m0 n
      = some (((List.range (n+1)).map
          (fun a => ([[0 + a*1*1, 0 + a*0*1], [1 + a*1*1, 1 + a*0*1]] : Matrix))).flatten) := rfl
  rw [h, List.map_congr_left (fun a _ => raw_eq a), flat_frep]

/-- The accumulated value of the inner `(0,1)`-headed reading. -/
def W : Nat → Term
  | 0 => e0
  | m + 1 => plus e0 (omegaNF (W m))

theorem valW : ∀ (m fuel : Nat), m + 2 ≤ fuel →
    Trans.Pair.oLAux fuel 1 (([0,1] : BMS.Col) :: frep R6.blk 1 0 m) = W m
  | 0, fuel, hf => by
    show Trans.Pair.oLAux fuel 1 (zs 1) = W 0
    rw [oLAux_zs 0 fuel 1 (by omega), ofNat_one]
    rfl
  | m + 1, fuel, hf => by
    cases fuel with
    | zero => omega
    | succ g =>
      have hE : (([0,1] : BMS.Col) :: frep R6.blk 1 0 (m+1))
          = ([0,1] : BMS.Col) :: (([0,0] : BMS.Col)
              :: (([1,1] : BMS.Col) :: frep R6.blk 1 1 m)) := rfl
      have hb : Trans.Pair.blocksP (([0,1] : BMS.Col) :: frep R6.blk 1 0 (m+1))
          = ([[0,1]] : Matrix) :: [(([0,0] : BMS.Col)
              :: (([1,1] : BMS.Col) :: frep R6.blk 1 1 m))] := by
        rw [hE, blocksP_cons_zero [0,1] [0,0] _ rfl]
        have ht : ∀ c ∈ (([1,1] : BMS.Col) :: frep R6.blk 1 1 m), Trans.Pair.r0 c ≠ 0 := by
          intro c hc
          rcases List.mem_cons.mp hc with h1 | h1
          · subst h1; show (1:Nat) ≠ 0; omega
          · exact r0_frep R6.blk_r0 m 1 (by omega) c h1
        rw [blocksP_single [0,0] _ ht]
      rw [oLAux_cons', hb]
      show zsF g 1 (zsF g 1 zero [[0,1]]) (([0,0] : BMS.Col)
        :: (([1,1] : BMS.Col) :: frep R6.blk 1 1 m)) = W (m+1)
      rw [zsF_step, phiStep_start, ofNat_one]
      show plus (phi one (ofNat 0)) (omegaNF (Trans.Pair.oLAux g 1
        (Trans.Pair.decP (([1,1] : BMS.Col) :: frep R6.blk 1 1 m)))) = W (m+1)
      have hd : Trans.Pair.decP (([1,1] : BMS.Col) :: frep R6.blk 1 1 m)
          = ([0,1] : BMS.Col) :: frep R6.blk 1 0 m := by
        show ([0,1] : BMS.Col) :: Trans.Pair.decP (frep R6.blk 1 1 m) = _
        rw [decP_frep R6.blk_decP m 0]
      rw [hd, valW m g (by omega)]
      rfl

theorem val (n fuel k : Nat) (hf : n + 3 ≤ fuel) :
    Trans.Pair.oLAux fuel k (frep R6.blk 1 0 (n+1)) = omegaNF (W n) := by
  cases fuel with
  | zero => omega
  | succ g =>
    have hE : frep R6.blk 1 0 (n+1)
        = ([0,0] : BMS.Col) :: (([1,1] : BMS.Col) :: frep R6.blk 1 1 n) := rfl
    have ht : ∀ c ∈ (([1,1] : BMS.Col) :: frep R6.blk 1 1 n), Trans.Pair.r0 c ≠ 0 := by
      intro c hc
      rcases List.mem_cons.mp hc with h1 | h1
      · subst h1; show (1:Nat) ≠ 0; omega
      · exact r0_frep R6.blk_r0 n 1 (by omega) c h1
    rw [hE, oLAux_single g k [0,0] _ ht]
    show plus zero (omegaNF (Trans.Pair.oLAux g 1
      (Trans.Pair.decP (([1,1] : BMS.Col) :: frep R6.blk 1 1 n)))) = omegaNF (W n)
    have hd : Trans.Pair.decP (([1,1] : BMS.Col) :: frep R6.blk 1 1 n)
        = ([0,1] : BMS.Col) :: frep R6.blk 1 0 n := by
      show ([0,1] : BMS.Col) :: Trans.Pair.decP (frep R6.blk 1 1 n) = _
      rw [decP_frep R6.blk_decP n 0]
    rw [hd, valW n g (by omega), plus_zero_left (isAP_omegaNF (W n))]

/-! ### Closed form of `W` -/

theorem W_one : W 1 = add e0 e0 := by decide

theorem ltF_add_e0_ne : ∀ g, ltF g (add e0 e0) e0 = false
  | 0 => rfl
  | g + 1 => by
    show (if ((add e0 e0 : Term) == e0) = true then false else ltF g e0 e0) = false
    simp only [show (((add e0 e0 : Term)) == e0) = false from rfl, Bool.false_eq_true, if_false]
    exact ltF_irrefl g e0

theorem ltF_tow_not_lt : ∀ (f j : Nat), ltF f (tow P0 j) e0 = false
  | 0, _ => rfl
  | f + 1, 0 => by
    show (if ((phi zero (add e0 e0) : Term) == e0) = true then false
          else if ((zero : Term) == one) = true then ltF f (add e0 e0) zero
          else if ltF f zero one = true then ltF f (add e0 e0) e0
          else ((phi zero (add e0 e0) : Term) == zero)
            || ltF f (phi zero (add e0 e0)) zero) = false
    simp only [show (((phi zero (add e0 e0) : Term)) == e0) = false from rfl,
      show (((zero : Term)) == one) = false from rfl, Bool.false_eq_true, if_false]
    cases hlt : ltF f zero one with
    | true => simp only [if_true]; exact ltF_add_e0_ne f
    | false =>
      simp only [Bool.false_eq_true, if_false,
        show (((phi zero (add e0 e0) : Term)) == zero) = false from rfl, Bool.false_or]
      exact ltF_lt_zero f _
  | f + 1, j + 1 => by
    show (if ((phi zero (tow P0 j) : Term) == e0) = true then false
          else if ((zero : Term) == one) = true then ltF f (tow P0 j) zero
          else if ltF f zero one = true then ltF f (tow P0 j) e0
          else ((phi zero (tow P0 j) : Term) == zero)
            || ltF f (phi zero (tow P0 j)) zero) = false
    simp only [show (((phi zero (tow P0 j) : Term)) == e0) = false from rfl,
      show (((zero : Term)) == one) = false from rfl, Bool.false_eq_true, if_false]
    cases hlt : ltF f zero one with
    | true => simp only [if_true]; exact ltF_tow_not_lt f j
    | false =>
      simp only [Bool.false_eq_true, if_false,
        show (((phi zero (tow P0 j) : Term)) == zero) = false from rfl, Bool.false_or]
      exact ltF_lt_zero f _

theorem le_tow_e0 (j : Nat) : le (tow P0 j) e0 = false := by
  show ((tow P0 j == e0) || lt (tow P0 j) e0) = false
  rw [show ((tow P0 j == e0) = false) from by cases j <;> rfl]
  simp only [Bool.false_or]
  exact ltF_tow_not_lt _ j

theorem W_succ2 : ∀ m, W (m+2) = tow P0 m
  | 0 => by
    show plus e0 (omegaNF (W 1)) = P0
    rw [W_one]
    decide
  | m + 1 => by
    show plus e0 (omegaNF (W (m+2))) = tow P0 (m+1)
    rw [W_succ2 m]
    show plus e0 (omegaNF (tow (phi zero (add e0 e0)) m)) = tow P0 (m+1)
    rw [omegaNF_tow (add e0 e0) m]
    exact plus_drop rfl (by cases m <;> rfl) (le_tow_e0 (m+1))

/-- Closed form of the value of the n-th expansion. -/
def oval : Nat → Term
  | 0 => e0
  | n + 1 => tow P0 n

theorem oval_eq : ∀ n, omegaNF (W n) = oval n
  | 0 => by decide
  | 1 => by rw [W_one]; decide
  | m + 2 => by
    rw [W_succ2 m]
    show omegaNF (tow (phi zero (add e0 e0)) m) = tow P0 (m+1)
    rw [omegaNF_tow (add e0 e0) m]
    rfl

theorem onlyRow0_E (n : Nat) : onlyRow0 (frep R6.blk 1 0 (n+1)) = false := by
  show onlyRow0 (R6.blk 0 ++ frep R6.blk 1 1 n) = false
  rw [onlyRow0_append]
  rfl

theorem frep_len : ∀ (m o : Nat), (frep R6.blk 1 o m).length = 2*m
  | 0, _ => rfl
  | m + 1, o => by
    show ((R6.blk o) ++ frep R6.blk 1 (o+1) m).length = 2*(m+1)
    rw [List.length_append, frep_len m (o+1)]
    show 2 + 2*m = 2*(m+1)
    omega

theorem e3_val (n : Nat) : o? (BMS.expand m0 n) = some (oval n) := by
  have hE : BMS.expand m0 n = frep R6.blk 1 0 (n+1) := by
    show (BMS.expand? m0 n).getD [] = _
    rw [expand_eq]; rfl
  rw [hE, o?_pair (onlyRow0_E n) (inFrag_frep R6.blk_inFrag (n+1) 0), frep_len (n+1) 0,
    val n (2*(n+1)+1) 1 (by omega), oval_eq]

/-! ### The fundamental sequence of ε₁ -/

theorem fs_raw (k : Nat) : fsN t0 k = iterPhiAt zero (plus e0 one) k := by
  show fsN (phi one one) k = _
  rw [fsN]
  simp only [show phiShifted one one = false from rfl, Bool.false_or,
    show (kindT (one : Term) == KindT.isSucc) = true from rfl, if_true]
  rfl

theorem fs_t : ∀ k, fsN t0 (k+1) = tow Q0 k
  | 0 => by rw [fs_raw]; decide
  | k + 1 => by
    have h1 : fsN t0 (k+2) = phiNF zero (fsN t0 (k+1)) := by
      rw [fs_raw, fs_raw]; rfl
    rw [h1, fs_t k]
    obtain ⟨y, hy⟩ := tow_shape e0 k
    show phiNF zero (tow (phi zero e0) k) = tow (phi zero e0) (k+1)
    rw [hy, phiNF_phi_arg isSC_zero, ← hy]
    rfl

/-! ### The order facts -/

theorem ltF_e0_t0 : ∀ f, 2 ≤ f → ltF f e0 t0 = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ i =>
    exact ltF_phi_same (ltF_zero (by omega) (by intro hc; exact Term.noConfusion hc))

theorem ltF_add_e0_t0 : ∀ f, 3 ≤ f → ltF f (add e0 e0) t0 = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ h =>
    show (if ((add e0 e0 : Term) == t0) = true then false else ltF h e0 t0) = true
    simp only [show (((add e0 e0 : Term)) == t0) = false from rfl, Bool.false_eq_true, if_false]
    exact ltF_e0_t0 h (by omega)

theorem ltF_tow_P0_t0 : ∀ (m f : Nat), m + 4 ≤ f → ltF f (tow P0 m) t0 = true
  | 0, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      exact ltF_phi_fst (show (((zero : Term)) == one) = false from rfl)
        (ltF_zero (by omega) (by intro hc; exact Term.noConfusion hc))
        (ltF_add_e0_t0 g (by omega))
  | m + 1, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      exact ltF_phi_fst (show (((zero : Term)) == one) = false from rfl)
        (ltF_zero (by omega) (by intro hc; exact Term.noConfusion hc))
        (ltF_tow_P0_t0 m g (by omega))

theorem ltF_add_e0_Q0 : ∀ f, 2 ≤ f → ltF f (add e0 e0) Q0 = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ h =>
    show (if ((add e0 e0 : Term) == Q0) = true then false else ltF h e0 Q0) = true
    simp only [show (((add e0 e0 : Term)) == Q0) = false from rfl, Bool.false_eq_true, if_false]
    cases h with
    | zero => omega
    | succ i => exact ltF_e0_pow i

theorem ltF_P0_towQ0 : ∀ f, 3 ≤ f → ltF f P0 (phi zero Q0) = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g => exact ltF_phi_same (ltF_add_e0_Q0 g (by omega))

theorem ltF_e0_add : ∀ f, 1 ≤ f → ltF f e0 (add e0 e0) = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g =>
    show (if ((e0 : Term) == add e0 e0) = true then false
          else ((e0 : Term) == e0) || ltF g e0 e0) = true
    simp
    intro hc
    exact Term.noConfusion hc

theorem ltF_Q0_P0 : ∀ f, 2 ≤ f → ltF f Q0 P0 = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g => exact ltF_phi_same (ltF_e0_add g (by omega))

theorem e3_lt : ∀ n, lt (oval n) t0 = true
  | 0 => by
    refine lt_of_ltF (N := 2) (fun f hf => ltF_e0_t0 f hf) ?_
    show 2 ≤ 2 * ((e0 : Term).deg + (t0 : Term).deg) + 8
    omega
  | n + 1 => by
    show lt (tow P0 n) t0 = true
    refine lt_of_ltF (N := n + 4) (fun f hf => ltF_tow_P0_t0 n f hf) ?_
    have h1 := deg_tow P0 n
    show n + 4 ≤ 2 * ((tow P0 n).deg + (t0 : Term).deg) + 8
    omega

/-- **E3, part (b)** with witness `k := n+1`. -/
theorem e3_over : ∀ n, lt (oval n) (fsN t0 (n+1)) = true
  | 0 => by
    rw [fs_t 0]
    show lt e0 Q0 = true
    refine lt_of_ltF (N := 1) (fun f hf => ?_) ?_
    · cases f with
      | zero => omega
      | succ g => exact ltF_e0_pow g
    · show 1 ≤ 2 * ((e0 : Term).deg + (Q0 : Term).deg) + 8
      omega
  | n + 1 => by
    rw [fs_t (n+1)]
    show lt (tow P0 n) (tow Q0 (n+1)) = true
    rw [← tow_phi Q0 n]
    refine lt_of_ltF (N := 3 + n)
      (fun f hf => ltF_tow_mono (fun g hg => ltF_P0_towQ0 g hg) n f hf) ?_
    have h1 := deg_tow P0 n
    show 3 + n ≤ 2 * ((tow P0 n).deg + (tow (phi zero Q0) n).deg) + 8
    omega

/-- **E3, part (c)** with witness `n := k+1`. -/
theorem e3_under (k : Nat) : lt (fsN t0 (k+1)) (oval (k+1)) = true := by
  rw [fs_t k]
  show lt (tow Q0 k) (tow P0 k) = true
  refine lt_of_ltF (N := 2 + k)
    (fun f hf => ltF_tow_mono (fun g hg => ltF_Q0_P0 g hg) k f hf) ?_
  have h1 := deg_tow Q0 k
  show 2 + k ≤ 2 * ((tow Q0 k).deg + (tow P0 k).deg) + 8
  omega

theorem e3 :
    (∀ n, o? (BMS.expand m0 n) = some (oval n))
    ∧ (∀ n, lt (oval n) t0 = true)
    ∧ (∀ n, lt (oval n) (fsN t0 (n + 1)) = true)
    ∧ (∀ k, lt (fsN t0 (k + 1)) (oval (k + 1)) = true) :=
  ⟨e3_val, e3_lt, e3_over, e3_under⟩

end R3


theorem ltF_phi_snd {f : Nat} {a b c d : Term} (hac : (a == c) = false) (h1 : ltF f a c = false)
    (h2 : ltF f (phi a b) d = true) : ltF (f + 1) (phi a b) (phi c d) = true := by
  have hac' : a ≠ c := by simpa using hac
  have hne : (phi a b == phi c d) = false := by simp [hac']
  show (if (phi a b == phi c d) = true then false else _) = true
  rw [hne]
  simp only [Bool.false_eq_true, if_false]
  show (if (a == c) = true then _ else if ltF f a c = true then _
        else ((phi a b == d) || ltF f (phi a b) d)) = true
  rw [hac, h1]
  simp [h2]

theorem ltF_phi_eq {f : Nat} {a b c d : Term} (hac : (a == c) = false) (h1 : ltF f a c = false)
    (h2 : (phi a b == d) = true) : ltF (f + 1) (phi a b) (phi c d) = true := by
  have hac' : a ≠ c := by simpa using hac
  have hne : (phi a b == phi c d) = false := by simp [hac']
  show (if (phi a b == phi c d) = true then false else _) = true
  rw [hne]
  simp only [Bool.false_eq_true, if_false]
  show (if (a == c) = true then _ else if ltF f a c = true then _
        else ((phi a b == d) || ltF f (phi a b) d)) = true
  rw [hac, h1]
  simp [h2]

theorem ltF_ofNat2_one : ∀ f, ltF f (ofNat 2) one = false
  | 0 => rfl
  | f + 1 => by
    show (if ((ofNat 2 : Term) == one) = true then false else ltF f one one) = false
    simp only [show (((ofNat 2 : Term)) == one) = false from rfl, Bool.false_eq_true, if_false]
    exact ltF_irrefl f one

/-! ## §18 Row `(0,0)(1,1)(2,1)(2,1)` = ζ₁ = φ̄(2,1) -/

namespace R7

def m0 : Matrix := [[0,0],[1,1],[2,1],[2,1]]
def t0 : Term := phi (ofNat 2) one
def z0 : Term := phi (ofNat 2) zero
/-- Base of the expansion tower: `φ̄(1, ω^{ζ₀·2})`. -/
def R0 : Term := phi one (phi zero (add z0 z0))
/-- Base of the fundamental-sequence tower: `φ̄(1, ζ₀)`. -/
def S0 : Term := phi one z0

/-- The ε-tower `φ̄1(φ̄1(…))` over a base. -/
def etow (b : Term) : Nat → Term
  | 0 => b
  | j + 1 => phi one (etow b j)

theorem etow_phi (b : Term) : ∀ j, etow (phi one b) j = etow b (j+1)
  | 0 => rfl
  | j + 1 => by
    show phi one (etow (phi one b) j) = phi one (etow b (j+1))
    rw [etow_phi b j]

theorem etow_shape (z : Term) : ∀ j, ∃ y, etow (phi one z) j = phi one y
  | 0 => ⟨z, rfl⟩
  | j + 1 => ⟨etow (phi one z) j, rfl⟩

theorem deg_etow (b : Term) : ∀ j, j ≤ (etow b j).deg
  | 0 => by show (0:Nat) ≤ b.deg; omega
  | j + 1 => by
    show j + 1 ≤ 1 + (one : Term).deg + (etow b j).deg
    have := deg_etow b j
    omega

theorem ltF_etow_mono {x y : Term} {N : Nat} (h : ∀ f, N ≤ f → ltF f x y = true) :
    ∀ (j f : Nat), N + j ≤ f → ltF f (etow x j) (etow y j) = true
  | 0, f, hf => h f (by omega)
  | j + 1, f, hf => by
    cases f with
    | zero => omega
    | succ g => exact ltF_phi_same (ltF_etow_mono h j g (by omega))

theorem raw_eq (a : Nat) :
    ([[0 + a*2*1, 0 + a*0*1], [1 + a*2*1, 1 + a*0*1], [2 + a*2*1, 1 + a*0*1]] : Matrix)
      = R9.blk (2 * a + 0) := by
  show _ = ([[2*a+0, 0], [2*a+0+1, 1], [2*a+0+2, 1]] : Matrix)
  have h1 : 0 + a*2*1 = 2*a+0 := by omega
  have h2 : 0 + a*0*1 = 0 := by omega
  have h3 : 1 + a*2*1 = 2*a+0+1 := by omega
  have h4 : 1 + a*0*1 = 1 := by omega
  have h5 : 2 + a*2*1 = 2*a+0+2 := by omega
  rw [h1, h2, h3, h4, h5]

theorem expand_eq (n : Nat) : BMS.expand? m0 n = some (frep R9.blk 2 0 (n+1)) := by
  have h : BMS.expand? m0 n
      = some (((List.range (n+1)).map
          (fun a => ([[0 + a*2*1, 0 + a*0*1], [1 + a*2*1, 1 + a*0*1],
                     [2 + a*2*1, 1 + a*0*1]] : Matrix))).flatten) := rfl
  rw [h, List.map_congr_left (fun a _ => raw_eq a), flat_frep]

def W : Nat → Term
  | 0 => z0
  | m + 1 => plus z0 (omegaNF (Trans.Pair.phiStep one zero (W m)))

theorem hd1 (o m : Nat) :
    Trans.Pair.decP (([1,1] : BMS.Col) :: (([2,1] : BMS.Col) :: frep R9.blk 2 (o+2) m))
      = ([0,1] : BMS.Col) :: (([1,1] : BMS.Col) :: frep R9.blk 2 (o+1) m) := by
  show ([0,1] : BMS.Col) :: (([1,1] : BMS.Col) :: Trans.Pair.decP (frep R9.blk 2 (o+2) m)) = _
  rw [decP_frep R9.blk_decP m (o+1)]

theorem hd2 (o m : Nat) :
    Trans.Pair.decP (([1,1] : BMS.Col) :: frep R9.blk 2 (o+1) m)
      = ([0,1] : BMS.Col) :: frep R9.blk 2 o m := by
  show ([0,1] : BMS.Col) :: Trans.Pair.decP (frep R9.blk 2 (o+1) m) = _
  rw [decP_frep R9.blk_decP m o]

theorem ht1 (m : Nat) : ∀ c ∈ (([1,1] : BMS.Col) :: frep R9.blk 2 1 m), Trans.Pair.r0 c ≠ 0 := by
  intro c hc
  rcases List.mem_cons.mp hc with h1 | h1
  · subst h1; show (1:Nat) ≠ 0; omega
  · exact r0_frep R9.blk_r0 m 1 (by omega) c h1

/-- The inner reading, at level 2, of `(0,1)` followed by the expansion tail. -/
theorem valV : ∀ (m fuel : Nat), 2*m + 2 ≤ fuel →
    Trans.Pair.oLAux fuel 2 (([0,1] : BMS.Col) :: frep R9.blk 2 0 m) = W m
  | 0, fuel, hf => by
    show Trans.Pair.oLAux fuel 2 (zs 1) = W 0
    rw [oLAux_zs 0 fuel 2 (by omega)]
    rfl
  | m + 1, fuel, hf => by
    cases fuel with
    | zero => omega
    | succ g =>
      cases g with
      | zero => omega
      | succ h =>
        have hE : (([0,1] : BMS.Col) :: frep R9.blk 2 0 (m+1))
            = ([0,1] : BMS.Col) :: (([0,0] : BMS.Col) :: (([1,1] : BMS.Col)
                :: (([2,1] : BMS.Col) :: frep R9.blk 2 2 m))) := rfl
        have htB : ∀ c ∈ (([1,1] : BMS.Col) :: (([2,1] : BMS.Col) :: frep R9.blk 2 2 m)),
            Trans.Pair.r0 c ≠ 0 := by
          intro c hc
          rcases List.mem_cons.mp hc with h1 | h1
          · subst h1; show (1:Nat) ≠ 0; omega
          · rcases List.mem_cons.mp h1 with h2 | h2
            · subst h2; show (2:Nat) ≠ 0; omega
            · exact r0_frep R9.blk_r0 m 2 (by omega) c h2
        have hb : Trans.Pair.blocksP (([0,1] : BMS.Col) :: frep R9.blk 2 0 (m+1))
            = ([[0,1]] : Matrix) :: [(([0,0] : BMS.Col) :: (([1,1] : BMS.Col)
                :: (([2,1] : BMS.Col) :: frep R9.blk 2 2 m)))] := by
          rw [hE, blocksP_cons_zero [0,1] [0,0] _ rfl, blocksP_single [0,0] _ htB]
        rw [oLAux_cons', hb]
        show zsF (h+1) 2 (zsF (h+1) 2 zero [[0,1]]) (([0,0] : BMS.Col) :: (([1,1] : BMS.Col)
          :: (([2,1] : BMS.Col) :: frep R9.blk 2 2 m))) = W (m+1)
        rw [zsF_step, phiStep_start]
        show plus (phi (ofNat 2) (ofNat 0)) (omegaNF (Trans.Pair.oLAux (h+1) 1
          (Trans.Pair.decP (([1,1] : BMS.Col) :: (([2,1] : BMS.Col)
            :: frep R9.blk 2 2 m))))) = W (m+1)
        rw [hd1 0 m, oLAux_single h 1 [0,1] _ (ht1 m)]
        show plus (phi (ofNat 2) (ofNat 0)) (omegaNF (Trans.Pair.phiStep (ofNat 1) zero
          (Trans.Pair.oLAux h 2 (Trans.Pair.decP (([1,1] : BMS.Col)
            :: frep R9.blk 2 1 m))))) = W (m+1)
        rw [hd2 0 m, valV m h (by omega), ofNat_one]
        rfl

theorem val (n fuel k : Nat) (hf : 2*n + 4 ≤ fuel) :
    Trans.Pair.oLAux fuel k (frep R9.blk 2 0 (n+1))
      = omegaNF (Trans.Pair.phiStep one zero (W n)) := by
  cases fuel with
  | zero => omega
  | succ g =>
    cases g with
    | zero => omega
    | succ i =>
      have hE : frep R9.blk 2 0 (n+1)
          = ([0,0] : BMS.Col) :: (([1,1] : BMS.Col) :: (([2,1] : BMS.Col)
              :: frep R9.blk 2 2 n)) := rfl
      have htB : ∀ c ∈ (([1,1] : BMS.Col) :: (([2,1] : BMS.Col) :: frep R9.blk 2 2 n)),
          Trans.Pair.r0 c ≠ 0 := by
        intro c hc
        rcases List.mem_cons.mp hc with h1 | h1
        · subst h1; show (1:Nat) ≠ 0; omega
        · rcases List.mem_cons.mp h1 with h2 | h2
          · subst h2; show (2:Nat) ≠ 0; omega
          · exact r0_frep R9.blk_r0 n 2 (by omega) c h2
      rw [hE, oLAux_single (i+1) k [0,0] _ htB]
      show plus zero (omegaNF (Trans.Pair.oLAux (i+1) 1
        (Trans.Pair.decP (([1,1] : BMS.Col) :: (([2,1] : BMS.Col)
          :: frep R9.blk 2 2 n))))) = _
      rw [hd1 0 n, oLAux_single i 1 [0,1] _ (ht1 n)]
      show plus zero (omegaNF (Trans.Pair.phiStep (ofNat 1) zero
        (Trans.Pair.oLAux i 2 (Trans.Pair.decP (([1,1] : BMS.Col)
          :: frep R9.blk 2 1 n))))) = _
      rw [hd2 0 n, valV n i (by omega), ofNat_one,
        plus_zero_left (isAP_omegaNF (Trans.Pair.phiStep one zero (W n)))]

/-! ### Closed form of the value -/

theorem one_ne_zero' : (one : Term) ≠ zero := by intro hc; exact Term.noConfusion hc

theorem etow_R0_shape : ∀ j, ∃ y, etow R0 j = phi one y
  | 0 => ⟨phi zero (add z0 z0), rfl⟩
  | j + 1 => ⟨etow R0 j, rfl⟩

theorem omegaNF_etow_R0 (j : Nat) : omegaNF (etow R0 j) = etow R0 j := by
  obtain ⟨y, hy⟩ := etow_R0_shape j
  rw [hy, omegaNF_phi_ne_zero one_ne_zero']

theorem phiStep_etow_R0 (j : Nat) :
    Trans.Pair.phiStep one zero (etow R0 j) = etow R0 (j+1) := by
  rw [phiStep_zero]
  obtain ⟨y, hy⟩ := etow_R0_shape j
  rw [show ((etow R0 j == zero) = false) from by rw [hy]; rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [omegaNF_etow_R0 j, hy, phiNF_phi_arg isSC_one, ← hy]
  rfl

theorem ltF_add_z0_z0 : ∀ f, ltF f (add z0 z0) z0 = false
  | 0 => rfl
  | f + 1 => by
    show (if ((add z0 z0 : Term) == z0) = true then false else ltF f z0 z0) = false
    simp only [show (((add z0 z0 : Term)) == z0) = false from rfl, Bool.false_eq_true, if_false]
    exact ltF_irrefl f z0

theorem ltF_pz_not_lt : ∀ f, ltF f (phi zero (add z0 z0)) z0 = false
  | 0 => rfl
  | f + 1 => by
    show (if ((phi zero (add z0 z0) : Term) == z0) = true then false
          else if ((zero : Term) == ofNat 2) = true then ltF f (add z0 z0) zero
          else if ltF f zero (ofNat 2) = true then ltF f (add z0 z0) z0
          else ((phi zero (add z0 z0) : Term) == zero)
            || ltF f (phi zero (add z0 z0)) zero) = false
    simp only [show (((phi zero (add z0 z0) : Term)) == z0) = false from rfl,
      show (((zero : Term)) == ofNat 2) = false from rfl, Bool.false_eq_true, if_false]
    cases hlt : ltF f zero (ofNat 2) with
    | true => simp only [if_true]; exact ltF_add_z0_z0 f
    | false =>
      simp only [Bool.false_eq_true, if_false,
        show (((phi zero (add z0 z0) : Term)) == zero) = false from rfl, Bool.false_or]
      exact ltF_lt_zero f _

theorem ltF_etow_not_lt : ∀ (f j : Nat), ltF f (etow R0 j) z0 = false
  | 0, _ => rfl
  | f + 1, 0 => by
    show (if ((phi one (phi zero (add z0 z0)) : Term) == z0) = true then false
          else if ((one : Term) == ofNat 2) = true then ltF f (phi zero (add z0 z0)) zero
          else if ltF f one (ofNat 2) = true then ltF f (phi zero (add z0 z0)) z0
          else ((phi one (phi zero (add z0 z0)) : Term) == zero)
            || ltF f (phi one (phi zero (add z0 z0))) zero) = false
    simp only [show (((phi one (phi zero (add z0 z0)) : Term)) == z0) = false from rfl,
      show (((one : Term)) == ofNat 2) = false from rfl, Bool.false_eq_true, if_false]
    cases hlt : ltF f one (ofNat 2) with
    | true => simp only [if_true]; exact ltF_pz_not_lt f
    | false =>
      simp only [Bool.false_eq_true, if_false,
        show (((phi one (phi zero (add z0 z0)) : Term)) == zero) = false from rfl, Bool.false_or]
      exact ltF_lt_zero f _
  | f + 1, j + 1 => by
    show (if ((phi one (etow R0 j) : Term) == z0) = true then false
          else if ((one : Term) == ofNat 2) = true then ltF f (etow R0 j) zero
          else if ltF f one (ofNat 2) = true then ltF f (etow R0 j) z0
          else ((phi one (etow R0 j) : Term) == zero)
            || ltF f (phi one (etow R0 j)) zero) = false
    simp only [show (((phi one (etow R0 j) : Term)) == z0) = false from rfl,
      show (((one : Term)) == ofNat 2) = false from rfl, Bool.false_eq_true, if_false]
    cases hlt : ltF f one (ofNat 2) with
    | true => simp only [if_true]; exact ltF_etow_not_lt f j
    | false =>
      simp only [Bool.false_eq_true, if_false,
        show (((phi one (etow R0 j) : Term)) == zero) = false from rfl, Bool.false_or]
      exact ltF_lt_zero f _

theorem le_etow_z0 (j : Nat) : le (etow R0 j) z0 = false := by
  show ((etow R0 j == z0) || lt (etow R0 j) z0) = false
  rw [show ((etow R0 j == z0) = false) from by cases j <;> rfl]
  simp only [Bool.false_or]
  exact ltF_etow_not_lt _ j

theorem W_succ2 : ∀ m, W (m+2) = etow R0 m
  | 0 => by decide
  | m + 1 => by
    show plus z0 (omegaNF (Trans.Pair.phiStep one zero (W (m+2)))) = etow R0 (m+1)
    rw [W_succ2 m, phiStep_etow_R0 m, omegaNF_etow_R0 (m+1)]
    exact plus_drop rfl (by obtain ⟨y, hy⟩ := etow_R0_shape (m+1); rw [hy]; rfl)
      (le_etow_z0 (m+1))

def oval : Nat → Term
  | 0 => z0
  | n + 1 => etow R0 n

theorem oval_eq : ∀ n, omegaNF (Trans.Pair.phiStep one zero (W n)) = oval n
  | 0 => by decide
  | 1 => by decide
  | m + 2 => by
    rw [W_succ2 m, phiStep_etow_R0 m, omegaNF_etow_R0 (m+1)]
    rfl

theorem onlyRow0_E (n : Nat) : onlyRow0 (frep R9.blk 2 0 (n+1)) = false := by
  show onlyRow0 (R9.blk 0 ++ frep R9.blk 2 2 n) = false
  rw [onlyRow0_append]
  rfl

theorem frep_len : ∀ (m o : Nat), (frep R9.blk 2 o m).length = 3*m
  | 0, _ => rfl
  | m + 1, o => by
    show ((R9.blk o) ++ frep R9.blk 2 (o+2) m).length = 3*(m+1)
    rw [List.length_append, frep_len m (o+2)]
    show 3 + 3*m = 3*(m+1)
    omega

theorem e3_val (n : Nat) : o? (BMS.expand m0 n) = some (oval n) := by
  have hE : BMS.expand m0 n = frep R9.blk 2 0 (n+1) := by
    show (BMS.expand? m0 n).getD [] = _
    rw [expand_eq]; rfl
  rw [hE, o?_pair (onlyRow0_E n) (inFrag_frep R9.blk_inFrag (n+1) 0), frep_len (n+1) 0,
    val n (3*(n+1)+1) 1 (by omega), oval_eq]

/-! ### The fundamental sequence of ζ₁ -/

theorem fs_raw (k : Nat) : fsN t0 k = iterPhiAt one (plus z0 one) k := by
  show fsN (phi (ofNat 2) one) k = _
  rw [fsN]
  simp only [show phiShifted (ofNat 2) one = false from rfl, Bool.false_or,
    show (kindT (one : Term) == KindT.isSucc) = true from rfl, if_true]
  rfl

theorem fs_t : ∀ k, fsN t0 (k+1) = etow S0 k
  | 0 => by rw [fs_raw]; decide
  | k + 1 => by
    have h1 : fsN t0 (k+2) = phiNF one (fsN t0 (k+1)) := by
      rw [fs_raw, fs_raw]; rfl
    rw [h1, fs_t k]
    obtain ⟨y, hy⟩ := etow_shape z0 k
    show phiNF one (etow (phi one z0) k) = etow (phi one z0) (k+1)
    rw [hy, phiNF_phi_arg isSC_one, ← hy]
    rfl

/-! ### The order facts -/

theorem ltF_z0_t0 : ∀ f, 2 ≤ f → ltF f z0 t0 = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ i => exact ltF_phi_same (ltF_zero (by omega) one_ne_zero')

theorem ltF_add_z0_t0 : ∀ f, 3 ≤ f → ltF f (add z0 z0) t0 = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ h =>
    show (if ((add z0 z0 : Term) == t0) = true then false else ltF h z0 t0) = true
    simp only [show (((add z0 z0 : Term)) == t0) = false from rfl, Bool.false_eq_true, if_false]
    exact ltF_z0_t0 h (by omega)

theorem ltF_pz_t0 : ∀ f, 4 ≤ f → ltF f (phi zero (add z0 z0)) t0 = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g =>
    exact ltF_phi_fst (show (((zero : Term)) == ofNat 2) = false from rfl)
      (ltF_zero (by omega) (by intro hc; exact Term.noConfusion hc))
      (ltF_add_z0_t0 g (by omega))

theorem ltF_etow_t0 : ∀ (j f : Nat), j + 5 ≤ f → ltF f (etow R0 j) t0 = true
  | 0, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      exact ltF_phi_fst (show (((one : Term)) == ofNat 2) = false from rfl)
        (ltF_one_two g (by omega)) (ltF_pz_t0 g (by omega))
  | j + 1, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      exact ltF_phi_fst (show (((one : Term)) == ofNat 2) = false from rfl)
        (ltF_one_two g (by omega)) (ltF_etow_t0 j g (by omega))

theorem ltF_z0_S0 : ∀ f, 1 ≤ f → ltF f z0 S0 = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g =>
    exact ltF_phi_eq (show (((ofNat 2 : Term)) == one) = false from rfl)
      (ltF_ofNat2_one g) (show ((z0 : Term) == z0) = true from rfl)

theorem ltF_add_z0_S0 : ∀ f, 2 ≤ f → ltF f (add z0 z0) S0 = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ h =>
    show (if ((add z0 z0 : Term) == S0) = true then false else ltF h z0 S0) = true
    simp only [show (((add z0 z0 : Term)) == S0) = false from rfl, Bool.false_eq_true, if_false]
    exact ltF_z0_S0 h (by omega)

theorem ltF_R0_phiS0 : ∀ f, 4 ≤ f → ltF f R0 (phi one S0) = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g =>
    refine ltF_phi_same ?_
    cases g with
    | zero => omega
    | succ h =>
      exact ltF_phi_fst (show (((zero : Term)) == one) = false from rfl)
        (ltF_zero (by omega) one_ne_zero') (ltF_add_z0_S0 h (by omega))

theorem ltF_z0_add : ∀ f, 1 ≤ f → ltF f z0 (add z0 z0) = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g =>
    show (if ((z0 : Term) == add z0 z0) = true then false
          else ((z0 : Term) == z0) || ltF g z0 z0) = true
    simp
    intro hc
    exact Term.noConfusion hc

theorem ltF_S0_R0 : ∀ f, 3 ≤ f → ltF f S0 R0 = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g =>
    refine ltF_phi_same ?_
    cases g with
    | zero => omega
    | succ h =>
      exact ltF_phi_snd (show (((ofNat 2 : Term)) == zero) = false from rfl)
        (ltF_lt_zero h (ofNat 2)) (ltF_z0_add h (by omega))

theorem e3_lt : ∀ n, lt (oval n) t0 = true
  | 0 => by
    refine lt_of_ltF (N := 2) (fun f hf => ltF_z0_t0 f hf) ?_
    show 2 ≤ 2 * ((z0 : Term).deg + (t0 : Term).deg) + 8
    omega
  | n + 1 => by
    show lt (etow R0 n) t0 = true
    refine lt_of_ltF (N := n + 5) (fun f hf => ltF_etow_t0 n f hf) ?_
    have h1 := deg_etow R0 n
    show n + 5 ≤ 2 * ((etow R0 n).deg + (t0 : Term).deg) + 8
    omega

/-- **E3, part (b)** with witness `k := n+1`. -/
theorem e3_over : ∀ n, lt (oval n) (fsN t0 (n+1)) = true
  | 0 => by
    rw [fs_t 0]
    show lt z0 S0 = true
    refine lt_of_ltF (N := 1) (fun f hf => ltF_z0_S0 f hf) ?_
    show 1 ≤ 2 * ((z0 : Term).deg + (S0 : Term).deg) + 8
    omega
  | n + 1 => by
    rw [fs_t (n+1)]
    show lt (etow R0 n) (etow S0 (n+1)) = true
    rw [← etow_phi S0 n]
    refine lt_of_ltF (N := 4 + n)
      (fun f hf => ltF_etow_mono (fun g hg => ltF_R0_phiS0 g hg) n f hf) ?_
    have h1 := deg_etow R0 n
    show 4 + n ≤ 2 * ((etow R0 n).deg + (etow (phi one S0) n).deg) + 8
    omega

/-- **E3, part (c)** with witness `n := k+1`. -/
theorem e3_under (k : Nat) : lt (fsN t0 (k+1)) (oval (k+1)) = true := by
  rw [fs_t k]
  show lt (etow S0 k) (etow R0 k) = true
  refine lt_of_ltF (N := 3 + k)
    (fun f hf => ltF_etow_mono (fun g hg => ltF_S0_R0 g hg) k f hf) ?_
  have h1 := deg_etow S0 k
  show 3 + k ≤ 2 * ((etow S0 k).deg + (etow R0 k).deg) + 8
  omega

theorem e3 :
    (∀ n, o? (BMS.expand m0 n) = some (oval n))
    ∧ (∀ n, lt (oval n) t0 = true)
    ∧ (∀ n, lt (oval n) (fsN t0 (n + 1)) = true)
    ∧ (∀ k, lt (fsN t0 (k + 1)) (oval (k + 1)) = true) :=
  ⟨e3_val, e3_lt, e3_over, e3_under⟩

end R7


/-! ## §19 The remaining five rows, packaged, and the sanity checks for all nine -/

#guard o? R2.m0 == some R2.t0
#guard o? R3.m0 == some R3.t0
#guard o? R4.m0 == some R4.t0
#guard o? R7.m0 == some R7.t0
#guard o? R8.m0 == some R8.t0

#guard (List.range 6).all fun n => o? (BMS.expand R2.m0 n) == some (fsN R2.t0 (n + 1))
#guard (List.range 6).all fun n => o? (BMS.expand R3.m0 n) == some (R3.oval n)
#guard (List.range 6).all fun n => o? (BMS.expand R4.m0 n) == some (fsN R4.t0 n)
#guard (List.range 6).all fun n => o? (BMS.expand R7.m0 n) == some (R7.oval n)
#guard (List.range 6).all fun n => o? (BMS.expand R8.m0 n) == some (fsN R8.t0 n)

-- the two rows whose expansions and fundamental sequences are genuinely different
-- cofinal sequences: the closed forms really do differ from every `fsN` value
#guard (List.range 5).all fun n =>
  (List.range 8).all fun k => R3.oval (n + 1) != fsN R3.t0 (k + 1)
#guard (List.range 5).all fun n =>
  (List.range 8).all fun k => R7.oval (n + 1) != fsN R7.t0 (k + 1)


end Rows.ProofsB
