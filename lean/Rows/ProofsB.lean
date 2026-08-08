import Rows.TM
import Evidence.StageA
/-
Rows/ProofsB.lean — per-row proofs for the Stage B fragment (Trans/Pair.lean)

(The imports are on the first lines: the kimina server mis-splits a snippet whose
`import` is preceded by a comment.)

Beyond ε₀ the BM4 expansion of a matrix and the fundamental sequence of its term
are in general DIFFERENT cofinal sequences of the same ordinal, so E3 cannot be an
equality of sequences.  The claim proved per row is the mutual-cofinality form of
plan/README.md, with explicit witness functions (§10):

  (a) ∀ n, o?(M[n]) = some (oval n)   and   ∀ n, lt (oval n) t
  (b) ∀ n, lt (oval n) (fsN t (kw n))          -- the expansions are overtaken by the fs
  (c) ∀ k, lt (fsN t (k+1)) (oval (nw k))      -- the fs is overtaken by the expansions

ROWS PROVED (4 of the 9 Stage-B rows of Rows/TM.lean).  For all four the two
sequences happen to coincide, so the closed form of `oval` is itself a value of
`fsN`, and the equality (stronger than (a)) is what is proved:

  §8  R1  (0,0)(1,1)           = ε₀ = φ̄(1,0)      o?(M[n]) = fsN t (n+1)
  §9  R5  (0,0)(1,1)(2,0)(3,1) = ε_{ε₀} = φ̄(1,ε₀)  o?(M[n]) = fsN t (n+2)
  §6  R6  (0,0)(1,1)(2,1)      = ζ₀ = φ̄(2,0)      o?(M[n]) = fsN t (n+1)
  §7  R9  (0,0)(1,1)(2,1)(3,1) = φ̄(3,0)           o?(M[n]) = fsN t (n+1)

FINDING: the index shift of the repository convention (`o(M[n]) ↔ t[n+1]`) is NOT
uniform on Stage B.  R5 runs two steps ahead, and the rows (0,0)(1,1)(2,0) and
(0,0)(1,1)(2,1)(3,0) run one step BEHIND (`o(M[n]) = t[n]`); §11 records the last
two as finite checks only.  Mutual cofinality is of course unaffected.

NOT PROVED HERE (see the report): (0,0)(1,1)(1,0), (0,0)(1,1)(1,1),
(0,0)(1,1)(2,0), (0,0)(1,1)(2,1)(2,1), (0,0)(1,1)(2,1)(3,0).  All five need
machinery this file does not build: the multi-block `foldl` of `oLAux` over a run
of `(0,1)` columns, together with `splitFin (ofNat n) = (0, n)` and the value of
`logPhi` on `φ̄(k, ofNat i)`.

Method.  §1–§2 give order tools for the fuelled decision procedure `ltF` and the
`φ_a`-iteration families `iterT a m` (the ω-, ε- and ζ-towers).  §3 unfolds
`oLAux` on single-block column sequences.  §4 puts a BM4 expansion
`((List.range (n+1)).map bad).flatten` into the front-recursive form `frep`, which
is the direction in which `oLAux` recurses.  §5 computes `fsN (φ̄ a 0)`.

References: [R91] = M. Rathjen, "Proof-theoretic analysis of KPM", Arch. Math.
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

-- the four rows are E1 rows of Rows/TM.lean
#guard o? R1.m0 == some R1.t0
#guard o? R5.m0 == some R5.t0
#guard o? R6.m0 == some R6.t0
#guard o? R9.m0 == some R9.t0

-- the index shift is NOT uniform across the Stage-B rows: for R5 the expansion runs
-- two steps ahead of the fundamental sequence, and for the two rows below it runs
-- one step BEHIND (o(M[n]) = t[n], not t[n+1]) — these two are not proved here.
#guard (List.range 6).all fun n =>
  o? (BMS.expand [[0,0],[1,1],[2,0]] n) == some (fsN (phi one omega) n)
#guard (List.range 6).all fun n =>
  o? (BMS.expand [[0,0],[1,1],[2,1],[3,0]] n) == some (fsN (phi (ofNat 2) omega) n)


end Rows.ProofsB
