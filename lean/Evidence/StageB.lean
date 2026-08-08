import Rows.ProofsB
/-
Evidence/StageB.lean — parameterized FAMILY theorems for the Stage B region

(Imports first: the kimina server mis-splits a snippet whose `import` is preceded
by a comment.)

FEASIBILITY MAP (read this before extending the file).

The Stage-A region supported one theorem for the whole region (`Evidence/StageA.lean`,
`e3_general`) because there both sides are equal sequences: `o(M[n]) = t[n+1]` for
every standard one-row matrix.  On Stage B that is false, and in three different
ways, as the nine rows of `Rows/ProofsB.lean` show:

  * `(0,0)(1,1)`, `(0,0)(1,1)(1,0)`, `(0,0)(1,1)(2,1)`, `(0,0)(1,1)(2,1)(3,1)`
      — equality at the repository shift, `o(M[n]) = t[n+1]`;
  * `(0,0)(1,1)(2,0)(3,1)` — equality at shift +2;
  * `(0,0)(1,1)(2,0)`, `(0,0)(1,1)(2,1)(3,0)` — equality at shift 0 (one behind);
  * `(0,0)(1,1)(1,1)`, `(0,0)(1,1)(2,1)(2,1)` — NO shift works: the expansions
      climb an ω- (resp. ε-) tower over a strictly larger base than the tower the
      fundamental sequence climbs.

So a single uniform Stage-B statement cannot be an equality with a fixed shift.  The
only statement shape that survives the whole region is the 4-part mutual-cofinality
package (below), whose witness functions `kw`, `nw` absorb the shift; that is the
shape used for every family here and for every row of `Rows/ProofsB.lean`.

  (a) ∀ n, o?(M[n]) = some (oval n)   and   ∀ n, lt (oval n) t
  (b) ∀ n, lt (oval n) (fsN t (kw n))
  (c) ∀ k, lt (fsN t (k+1)) (oval (nw k))

The second obstacle is on the BMS side.  In Stage A every ascension amount vanishes
(`t = 0` there), so the expansion is always "copy the bad part n+1 times" and one
lemma covered the region.  On Stage B the lowest nonzero row of the last column is 0
or 1, and in the `t = 1` case the bad blocks are shifted by `a·Δ₀` per copy, with Δ₀
depending on the matrix; moreover the bad root is computed by `parent M 1 (X-1)`,
i.e. through `iterParent`, so it is no longer a single `max?` over a range.  For a
matrix with a symbolic parameter this must be proved, not computed.

WHAT THIS FILE PROVES (families, each for ALL a ≥ 1, i.e. infinitely many matrices
beyond the table):

  §3  F2 : (0,0)(1,1)…(a,1)(a+1,0)  =  φ̄(a,ω)      o?(M[n]) = fsN t n      (shift 0)
      instances: a = 1 is Rows.ProofsB.R4, a = 2 is Rows.ProofsB.R8.

FRONTIER (not proved here):
  * F1 : (0,0)(1,1)…(a,1) = φ̄(a,0) — value side is the same induction as F2, but the
    BMS side needs `parent M 1 (X-1)` through `iterParent` (Δ₀ = a ≠ 0).
  * F3 : (0,0)(1,1)…(a,1)(a,1) = φ̄(a,1) — the "no shift works" family (R3, R7).
  * A genuinely region-wide theorem additionally needs a 2-row standardness
    invariant and an invariant carried on the `oLAux` accumulator (`logPhi k acc`
    defined and `acc` a φ_k-value), since the Stage-B value function is an
    accumulator fold, not a plain sum.  No relation to `BMS.Standard` is claimed
    anywhere in this file.

References: [R91] = M. Rathjen, "Proof-theoretic analysis of KPM", Arch. Math.
Logic 30 (1991) 377–403.
-/

namespace Evidence.StageB

open BMS (Matrix)
open TM (Term)
open TM.Term
open Trans
open Rows.ProofsB

/-! ## §1 The ladder shapes -/

/-- `p` columns `(o,1) (o+1,1) … (o+p-1,1)`. -/
def ups (o : Nat) : Nat → Matrix
  | 0 => []
  | p + 1 => [o,1] :: ups (o+1) p

/-- `ups o p` closed off by the row-1-zero column `(o+p, 0)`. -/
def tailU (o p : Nat) : Matrix := ups o p ++ [[o+p, 0]]

/-- `k` copies of the column `(q,1)`. -/
def runq (q k : Nat) : Matrix := List.replicate k ([q,1] : BMS.Col)

theorem tailU_succ (o p : Nat) : tailU o (p+1) = ([o,1] : BMS.Col) :: tailU (o+1) p := by
  show (([o,1] : BMS.Col) :: ups (o+1) p) ++ [[o+(p+1), 0]]
      = ([o,1] : BMS.Col) :: (ups (o+1) p ++ [[(o+1)+p, 0]])
  have h : o + (p+1) = (o+1) + p := by omega
  rw [h]
  rfl

theorem ups_len : ∀ (p o : Nat), (ups o p).length = p
  | 0, _ => rfl
  | p + 1, o => by
    show (ups (o+1) p).length + 1 = p + 1
    rw [ups_len p (o+1)]

theorem ups_take : ∀ (p j o : Nat), j ≤ p → (ups o p).take j = ups o j
  | _, 0, _, _ => rfl
  | 0, j+1, _, h => by omega
  | p + 1, j + 1, o, h => by
    show ([o,1] : BMS.Col) :: (ups (o+1) p).take j = ([o,1] : BMS.Col) :: ups (o+1) j
    rw [ups_take p j (o+1) (by omega)]

theorem decP_ups : ∀ (p o : Nat), Trans.Pair.decP (ups (o+1) p) = ups o p
  | 0, _ => rfl
  | p + 1, o => by
    show ([o+1-1, 1] : BMS.Col) :: Trans.Pair.decP (ups (o+1+1) p) = ([o,1] : BMS.Col) :: ups (o+1) p
    have h : o + 1 - 1 = o := by omega
    rw [h, decP_ups p (o+1)]

theorem decP_runq (q k : Nat) : Trans.Pair.decP (runq (q+1) k) = runq q k := by
  show (List.replicate k ([q+1,1] : BMS.Col)).map _ = _
  rw [List.map_replicate]
  have h : q + 1 - 1 = q := by omega
  show List.replicate k ([q+1-1, 1] : BMS.Col) = _
  rw [h]
  rfl

theorem r0_ups : ∀ (p o : Nat), 1 ≤ o → ∀ c ∈ ups o p, Trans.Pair.r0 c ≠ 0
  | 0, _, _, _, hc => by simp [ups] at hc
  | p + 1, o, ho, c, hc => by
    rcases List.mem_cons.mp hc with h | h
    · subst h; show o ≠ 0; omega
    · exact r0_ups p (o+1) (by omega) c h

theorem r0_runq (q k : Nat) (hq : 1 ≤ q) : ∀ c ∈ runq q k, Trans.Pair.r0 c ≠ 0 := by
  intro c hc
  rw [List.eq_of_mem_replicate hc]
  show q ≠ 0
  omega

theorem inFrag_ups : ∀ (p o : Nat), Trans.Pair.inFrag (ups o p) = true
  | 0, _ => rfl
  | p + 1, o => by
    show Trans.Pair.inFrag (([o,1] : BMS.Col) :: ups (o+1) p) = true
    rw [inFrag_cons, inFrag_ups p (o+1)]
    rfl

theorem inFrag_runq : ∀ (k q : Nat), Trans.Pair.inFrag (runq q k) = true
  | 0, _ => rfl
  | k + 1, q => by
    show Trans.Pair.inFrag (([q,1] : BMS.Col) :: runq q k) = true
    rw [inFrag_cons, inFrag_runq k q]
    rfl

/-! ## §2 The family F2 : `(0,0)(1,1)…(a,1)(a+1,0)` — the BM4 expansion

Writing `a = q+1`, the last column has row-1 entry 0, so `t = 0`, every ascension
amount vanishes and the expansion is the plain "copy the bad part n+1 times" rule
with bad part the single column `(a,1)`. -/

def M2 (q : Nat) : Matrix := ([0,0] : BMS.Col) :: tailU 1 (q+1)

def EB (q n : Nat) : Matrix := ([0,0] : BMS.Col) :: (ups 1 q ++ runq (q+1) (n+1))

theorem ent_tailU0 : ∀ (p o x : Nat), x ≤ p → BMS.ent (tailU o p) x 0 = o + x
  | 0, o, x, h => by
    have hx : x = 0 := by omega
    subst hx
    show BMS.ent ([[o+0, 0]] : Matrix) 0 0 = o + 0
    rfl
  | p + 1, o, 0, _ => by
    rw [tailU_succ]
    rfl
  | p + 1, o, x + 1, h => by
    rw [tailU_succ]
    have h1 : BMS.ent (([o,1] : BMS.Col) :: tailU (o+1) p) (x+1) 0
        = BMS.ent (tailU (o+1) p) x 0 := by
      show ((([o,1] : BMS.Col) :: tailU (o+1) p).getD (x+1) []).getD 0 0
          = ((tailU (o+1) p).getD x []).getD 0 0
      rw [List.getD_cons_succ]
    rw [h1, ent_tailU0 p (o+1) x (by omega)]
    omega

theorem ent_tailU1 : ∀ (p o x : Nat), x < p → BMS.ent (tailU o p) x 1 = 1
  | 0, _, _, h => by omega
  | p + 1, o, 0, _ => by rw [tailU_succ]; rfl
  | p + 1, o, x + 1, h => by
    rw [tailU_succ]
    have h1 : BMS.ent (([o,1] : BMS.Col) :: tailU (o+1) p) (x+1) 1
        = BMS.ent (tailU (o+1) p) x 1 := by
      show ((([o,1] : BMS.Col) :: tailU (o+1) p).getD (x+1) []).getD 1 0
          = ((tailU (o+1) p).getD x []).getD 1 0
      rw [List.getD_cons_succ]
    rw [h1, ent_tailU1 p (o+1) x (by omega)]

theorem ent_M2_0 (q x : Nat) (h : x ≤ q + 2) : BMS.ent (M2 q) x 0 = x := by
  cases x with
  | zero => rfl
  | succ y =>
    have h1 : BMS.ent (M2 q) (y+1) 0 = BMS.ent (tailU 1 (q+1)) y 0 := by
      show ((([0,0] : BMS.Col) :: tailU 1 (q+1)).getD (y+1) []).getD 0 0
          = ((tailU 1 (q+1)).getD y []).getD 0 0
      rw [List.getD_cons_succ]
    rw [h1, ent_tailU0 (q+1) 1 y (by omega)]
    omega

theorem ent_M2_1 (q : Nat) : BMS.ent (M2 q) (q+1) 1 = 1 := by
  have h1 : BMS.ent (M2 q) (q+1) 1 = BMS.ent (tailU 1 (q+1)) q 1 := by
    show ((([0,0] : BMS.Col) :: tailU 1 (q+1)).getD (q+1) []).getD 1 0
        = ((tailU 1 (q+1)).getD q []).getD 1 0
    rw [List.getD_cons_succ]
  rw [h1, ent_tailU1 (q+1) 1 q (by omega)]

theorem len_tailU (p o : Nat) : (tailU o p).length = p + 1 := by
  show (ups o p ++ [[o+p, 0]]).length = p + 1
  rw [List.length_append, ups_len]
  rfl

theorem len_M2 (q : Nat) : (M2 q).length = q + 3 := by
  show (tailU 1 (q+1)).length + 1 = q + 3
  rw [len_tailU]

theorem getLast_M2 (q : Nat) : (M2 q).getLast? = some ([q+2, 0] : BMS.Col) := by
  show (([0,0] : BMS.Col) :: (ups 1 (q+1) ++ [[1+(q+1), 0]])).getLast? = _
  rw [show (([0,0] : BMS.Col) :: (ups 1 (q+1) ++ [[1+(q+1), 0]]))
      = ((([0,0] : BMS.Col) :: ups 1 (q+1)) ++ [[1+(q+1), 0]]) from rfl,
    List.getLast?_concat]
  have h : 1 + (q+1) = q + 2 := by omega
  rw [h]

theorem take_M2 (q : Nat) : (M2 q).take (q+1) = ([0,0] : BMS.Col) :: ups 1 q := by
  show ([0,0] : BMS.Col) :: (tailU 1 (q+1)).take q = _
  show ([0,0] : BMS.Col) :: (ups 1 (q+1) ++ [[1+(q+1), 0]]).take q = _
  rw [List.take_append_of_le_length (by rw [ups_len]; omega), ups_take (q+1) q 1 (by omega)]

theorem lnz_last (q : Nat) : BMS.lnz ([q+2, 0] : BMS.Col) = some 0 := by
  show (((List.range 2).filter (fun y => decide (([q+2,0] : BMS.Col).getD y 0 > 0))).max?) = some 0
  show (([0,1] : List Nat).filter (fun y => decide (([q+2,0] : BMS.Col).getD y 0 > 0))).max? = some 0
  have h : (decide ((([q+2,0] : BMS.Col).getD 0 0) > 0)) = true := by
    show (decide ((q+2 : Nat) > 0)) = true
    exact decide_eq_true (by omega)
  rw [List.filter_cons, h]
  rfl

theorem parent_M2 (q : Nat) : BMS.parent (M2 q) 0 ((M2 q).length - 1) = some (q+1) := by
  rw [len_M2]
  show (((List.range (q+2)).filter
      (fun p => decide (BMS.ent (M2 q) p 0 < BMS.ent (M2 q) (q+3-1) 0))).max?) = some (q+1)
  rw [Evidence.StageA.max?_filter_range]
  refine Evidence.StageA.lastSome_spec _ (q+2) (q+1) (by omega) ?_ ?_
  · rw [ent_M2_0 q (q+1) (by omega), show q+3-1 = q+2 from by omega, ent_M2_0 q (q+2) (by omega)]
    exact decide_eq_true (by omega)
  · intro r h1 h2
    omega

theorem repM_runq : ∀ (k q : Nat), repM ([[q,1]] : Matrix) k = runq q k
  | 0, _ => rfl
  | k + 1, q => by
    show ([q,1] : BMS.Col) :: repM ([[q,1]] : Matrix) k = runq q (k+1)
    rw [repM_runq k q]
    rfl

theorem expand_M2 (q n : Nat) : BMS.expand? (M2 q) n = some (EB q n) := by
  have hlen1 : (M2 q).length - 1 - (q+1) = 1 := by rw [len_M2]; omega
  simp only [BMS.expand?, getLast_M2, Option.bind_eq_bind, Option.bind_some, lnz_last,
    parent_M2, Option.pure_def, Evidence.StageA.delta_zero, Nat.mul_zero, Nat.zero_mul,
    Nat.add_zero, hlen1]
  have hbad : ∀ a : Nat,
      (List.map (fun x => List.map (fun y => BMS.ent (M2 q) (q+1+x) y)
        (List.range ([q+2, 0] : BMS.Col).length)) (List.range 1)) = ([[q+1, 1]] : Matrix) := by
    intro a
    show [List.map (fun y => BMS.ent (M2 q) (q+1+0) y) (List.range 2)] = ([[q+1, 1]] : Matrix)
    show [[BMS.ent (M2 q) (q+1+0) 0, BMS.ent (M2 q) (q+1+0) 1]] = ([[q+1, 1]] : Matrix)
    rw [show q+1+0 = q+1 from rfl, ent_M2_0 q (q+1) (by omega), ent_M2_1 q]
  rw [List.map_congr_left (fun a _ => hbad a), flat_range, repM_runq, take_M2]
  rfl


/-! ## §3 The family F2 — the value, the fundamental sequence, and the package -/

theorem ofNat_inj {i j : Nat} (h : ofNat i = ofNat j) : i = j := by
  have h1 := congrArg toList h
  rw [toList_ofNat, toList_ofNat] at h1
  have h2 := congrArg List.length h1
  simpa using h2

theorem ofNat_bne {i j : Nat} (h : i ≠ j) : (ofNat i == ofNat j) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro hc
  exact h (ofNat_inj hc)

theorem ofNat_ne_zero : ∀ m, (ofNat (m+1) : Term) ≠ zero
  | 0 => by intro hc; exact Term.noConfusion hc
  | m + 1 => by rw [ofNat_shape m]; intro hc; exact Term.noConfusion hc

theorem ltF_ofNat_mono : ∀ (i j f : Nat), i < j → i + 2 ≤ f → ltF f (ofNat i) (ofNat j) = true
  | 0, j, f, hij, hf => by
    refine ltF_zero (by omega) ?_
    cases j with
    | zero => omega
    | succ m => exact ofNat_ne_zero m
  | 1, j, f, hij, hf => by
    obtain ⟨m, hm⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
    subst hm
    cases f with
    | zero => omega
    | succ g =>
      rw [ofNat_shape m, ofNat_one]
      show (if ((one : Term) == add one (ofNat (m+1))) = true then false
            else ((one : Term) == one) || ltF g one one) = true
      simp
      intro hc
      exact Term.noConfusion hc
  | i + 2, j, f, hij, hf => by
    obtain ⟨m, hm⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
    subst hm
    cases f with
    | zero => omega
    | succ g =>
      have ih := ltF_ofNat_mono (i+1) (m+1) g (by omega) (by omega)
      rw [ofNat_shape i, ofNat_shape m]
      show (if (add one (ofNat (i+1)) == add one (ofNat (m+1))) = true then false
            else if ((one : Term) == one) = true then ltF g (ofNat (i+1)) (ofNat (m+1))
            else ltF g one one) = true
      rw [show ((add one (ofNat (i+1)) == add one (ofNat (m+1))) = false) from by
        simp
        intro hc
        exact (show i+1 ≠ m+1 from by omega) (ofNat_inj hc)]
      simp [ih]

theorem lt_ofNat_mono {i j : Nat} (h : i < j) : lt (ofNat i) (ofNat j) = true := by
  refine Rows.ProofsB.lt_of_ltF (N := i + 2) (fun f hf => ltF_ofNat_mono i j f h hf) ?_
  have h1 := deg_ofNat i
  show i + 2 ≤ 2 * ((ofNat i).deg + (ofNat j).deg) + 8
  omega

theorem phiShifted_omega {a : Term} (ha : a.isSC = false) : phiShifted a omega = false := by
  show phiShifted a (phi zero one) = false
  unfold phiShifted
  rw [show (splitFin (phi zero one : Term)).1 = phi zero one from rfl]
  unfold isFP
  rw [ha]
  simp [isSC, lt_lt_zero]

/-- A descending run of `(0,1)`-heads over a `(q,1)`-run: value `φ̄(j+q, n)`. -/
theorem oLAux_G2 : ∀ (q j fuel n : Nat), q + 1 ≤ fuel →
    Trans.Pair.oLAux fuel j (ups 0 q ++ runq q (n+1)) = phi (ofNat (j+q)) (ofNat n)
  | 0, j, fuel, n, hf => by
    show Trans.Pair.oLAux fuel j (runq 0 (n+1)) = _
    rw [show runq 0 (n+1) = zs (n+1) from rfl, oLAux_zs n fuel j (by omega)]
    rfl
  | q + 1, j, fuel, n, hf => by
    cases fuel with
    | zero => omega
    | succ g =>
      have hE : (ups 0 (q+1) ++ runq (q+1) (n+1))
          = ([0,1] : BMS.Col) :: (ups 1 q ++ runq (q+1) (n+1)) := rfl
      have ht : ∀ c ∈ (ups 1 q ++ runq (q+1) (n+1)), Trans.Pair.r0 c ≠ 0 := by
        intro c hc
        rcases List.mem_append.mp hc with h1 | h1
        · exact r0_ups q 1 (by omega) c h1
        · exact r0_runq (q+1) (n+1) (by omega) c h1
      have hd : Trans.Pair.decP (ups 1 q ++ runq (q+1) (n+1)) = ups 0 q ++ runq q (n+1) := by
        rw [decP_append, decP_ups, decP_runq]
      rw [hE, oLAux_single g j [0,1] _ ht]
      show Trans.Pair.phiStep (ofNat j) zero (Trans.Pair.oLAux g (j+1)
        (Trans.Pair.decP (ups 1 q ++ runq (q+1) (n+1)))) = _
      rw [hd, oLAux_G2 q (j+1) g n (by omega), phiStep_zero,
        show ((phi (ofNat (j+1+q)) (ofNat n) == zero) = false) from rfl]
      simp only [Bool.false_eq_true, if_false]
      rw [omegaNF_phi_ne_zero (by
          rw [show j+1+q = (j+q)+1 from by omega]; exact ofNat_ne_zero (j+q)),
        phiNF_collapse (lt_ofNat_mono (show j < j+1+q from by omega))]
      congr 2
      omega

theorem oLAux_EB (q n fuel k : Nat) (hf : q + 2 ≤ fuel) :
    Trans.Pair.oLAux fuel k (EB q n) = phi (ofNat (q+1)) (ofNat n) := by
  cases fuel with
  | zero => omega
  | succ g =>
    have ht : ∀ c ∈ (ups 1 q ++ runq (q+1) (n+1)), Trans.Pair.r0 c ≠ 0 := by
      intro c hc
      rcases List.mem_append.mp hc with h1 | h1
      · exact r0_ups q 1 (by omega) c h1
      · exact r0_runq (q+1) (n+1) (by omega) c h1
    have hd : Trans.Pair.decP (ups 1 q ++ runq (q+1) (n+1)) = ups 0 q ++ runq q (n+1) := by
      rw [decP_append, decP_ups, decP_runq]
    show Trans.Pair.oLAux (g+1) k (([0,0] : BMS.Col) :: (ups 1 q ++ runq (q+1) (n+1))) = _
    rw [oLAux_single g k [0,0] _ ht]
    show plus zero (omegaNF (Trans.Pair.oLAux g 1
      (Trans.Pair.decP (ups 1 q ++ runq (q+1) (n+1))))) = _
    rw [hd, oLAux_G2 q 1 g n (by omega),
      omegaNF_phi_ne_zero (by rw [show 1+q = q+1 from by omega]; exact ofNat_ne_zero q),
      plus_zero_left rfl]
    congr 2
    omega

theorem onlyRow0_runq (q k : Nat) : onlyRow0 (runq q (k+1)) = false := by
  show onlyRow0 (([q,1] : BMS.Col) :: runq q k) = false
  rw [onlyRow0_cons]
  rfl

theorem onlyRow0_EB (q n : Nat) : onlyRow0 (EB q n) = false := by
  show onlyRow0 (([0,0] : BMS.Col) :: (ups 1 q ++ runq (q+1) (n+1))) = false
  rw [onlyRow0_cons, onlyRow0_append, onlyRow0_runq]
  simp

theorem inFrag_EB (q n : Nat) : Trans.Pair.inFrag (EB q n) = true := by
  show Trans.Pair.inFrag (([0,0] : BMS.Col) :: (ups 1 q ++ runq (q+1) (n+1))) = true
  rw [inFrag_cons, inFrag_append, inFrag_ups q 1, inFrag_runq (n+1) (q+1)]
  rfl

theorem len_EB (q n : Nat) : (EB q n).length = q + n + 2 := by
  show (ups 1 q ++ runq (q+1) (n+1)).length + 1 = q + n + 2
  rw [List.length_append, ups_len]
  show q + (List.replicate (n+1) ([q+1,1] : BMS.Col)).length + 1 = q + n + 2
  rw [List.length_replicate]
  omega

/-- The term of the family: `φ̄(a,ω)` with `a = q+1`. -/
def t0 (q : Nat) : Term := phi (ofNat (q+1)) omega

theorem fs_t (q k : Nat) : fsN (t0 q) k = phi (ofNat (q+1)) (ofNat k) := by
  show fsN (phi (ofNat (q+1)) omega) k = _
  rw [fsN_phi_lim (phiShifted_omega (isSC_ofNat (q+1)))
    (show kindT omega = KindT.isLim from rfl) k, fs_omega' k]
  exact phiNF_ofNat (isSC_ofNat (q+1)) k

/-- The closed form of the n-th expansion: the fundamental sequence at n (shift 0). -/
def oval (q n : Nat) : Term := fsN (t0 q) n

theorem e3_val (q n : Nat) : o? (BMS.expand (M2 q) n) = some (oval q n) := by
  have hE : BMS.expand (M2 q) n = EB q n := by
    show (BMS.expand? (M2 q) n).getD [] = _
    rw [expand_M2]; rfl
  show o? (BMS.expand (M2 q) n) = some (fsN (t0 q) n)
  rw [hE, o?_pair (onlyRow0_EB q n) (inFrag_EB q n), len_EB,
    oLAux_EB q n (q+n+2+1) 1 (by omega), fs_t]

theorem e3_lt (q n : Nat) : lt (oval q n) (t0 q) = true := by
  show lt (fsN (t0 q) n) (t0 q) = true
  rw [fs_t]
  show lt (phi (ofNat (q+1)) (ofNat n)) (phi (ofNat (q+1)) omega) = true
  refine Rows.ProofsB.lt_phi_same_of (N := 3) (fun f hf => ltF_ofNat_omega n f hf) ?_
  show 3 + 1 ≤ 2 * ((phi (ofNat (q+1)) (ofNat n)).deg + (phi (ofNat (q+1)) omega).deg) + 8
  omega

/-- **(b)** with witness `k := n+1`. -/
theorem e3_over (q n : Nat) : lt (oval q n) (fsN (t0 q) (n+1)) = true := by
  show lt (fsN (t0 q) n) (fsN (t0 q) (n+1)) = true
  rw [fs_t, fs_t]
  refine Rows.ProofsB.lt_phi_same_of (N := n+2) (fun f hf => ltF_ofNat_succ n f hf) ?_
  have h1 := deg_ofNat n
  show n + 2 + 1 ≤ 2 * ((1 + (ofNat (q+1) : Term).deg + (ofNat n).deg)
    + (1 + (ofNat (q+1) : Term).deg + (ofNat (n+1)).deg)) + 8
  omega

/-- **(c)** with witness `n := k+2`. -/
theorem e3_under (q k : Nat) : lt (fsN (t0 q) (k+1)) (oval q (k+2)) = true := e3_over q (k+1)

/-- **E3 for the whole family**, for every `a = q+1 ≥ 1`.
    (Named `e3_family`, not `e3`: the table's link resolution finds the first
    line containing "theorem <name>", which must not match `e3_val` etc.) -/
theorem e3_family (q : Nat) :
    (∀ n, o? (BMS.expand (M2 q) n) = some (oval q n))
    ∧ (∀ n, lt (oval q n) (t0 q) = true)
    ∧ (∀ n, lt (oval q n) (fsN (t0 q) (n + 1)) = true)
    ∧ (∀ k, lt (fsN (t0 q) (k + 1)) (oval q (k + 2)) = true) :=
  ⟨e3_val q, e3_lt q, e3_over q, e3_under q⟩

/-! ### The two table rows are instances -/

theorem m2_zero : M2 0 = Rows.ProofsB.R4.m0 := rfl
theorem m2_one : M2 1 = Rows.ProofsB.R8.m0 := rfl
theorem t0_zero : t0 0 = Rows.ProofsB.R4.t0 := rfl
theorem t0_one : t0 1 = Rows.ProofsB.R8.t0 := rfl

example (n : Nat) : o? (BMS.expand Rows.ProofsB.R4.m0 n) = some (fsN Rows.ProofsB.R4.t0 n) :=
  e3_val 0 n

example (n : Nat) : o? (BMS.expand Rows.ProofsB.R8.m0 n) = some (fsN Rows.ProofsB.R8.t0 n) :=
  e3_val 1 n

/-- The family goes strictly beyond the table: `a = 3, 4, …` are new rows. -/
example (n : Nat) :
    o? (BMS.expand [[0,0],[1,1],[2,1],[3,1],[4,0]] n)
      = some (fsN (phi (ofNat 3) omega) n) := e3_val 2 n

#guard (List.range 4).all fun q => (List.range 4).all fun n =>
  Trans.o? (BMS.expand (M2 q) n) == some (fsN (t0 q) n)
#guard (List.range 5).all fun q => Trans.o? (M2 q) == some (t0 q)


end Evidence.StageB
