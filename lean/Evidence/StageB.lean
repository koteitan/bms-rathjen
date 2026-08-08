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

  §3  F2 : (0,0)(1,1)…(a,1)(a+1,0)  =  φ̄(a,ω)   o?(M[n]) = fsN t n      (shift 0)
      `e3_family`; a = 1 is Rows.ProofsB.R4, a = 2 is Rows.ProofsB.R8.
  §5  F1 : (0,0)(1,1)…(a,1)         =  φ̄(a,0)   o?(M[n]) = fsN t (n+1)  (shift +1)
      `e3_F1family`; a = 1, 2, 3 are Rows.ProofsB.R1, R6, R9.

F1 needs the genuinely new machinery of §4: its last column has row-1 entry 1, so
`t = 1`, `Δ₀ = a ≠ 0`, and the bad root is `parent M 1 (X-1)`, which runs through
`iterParent` over the row-0 parent chain.  §4 proves that chain is `downFrom` and
that filtering it by "row-1 entry < 1" leaves exactly the column 0, for a symbolic
parameter.  §5 then computes the value with `chainP` (the `a-1` nested `phiStep`s
that the descending `(0,1)`-heads produce, of which only the innermost survives —
`chainP_collapse`).

FRONTIER (not proved here):
  * F3 : (0,0)(1,1)…(a,1)(a,1) = φ̄(a,1) — the "no shift works" family (R3, R7).
    Its BMS side is now unblocked (same §4 machinery: bad root 0, Δ₀ = a, bad block
    `lad a`), and its value side is the same `chainP` chain; what is still missing is
    (i) the accumulator recursion `V(m+1) = plus (φ̄(a,0)) (ω^(chainP 1 (a-1) (V m)))`
    with its `plus_drop` side conditions in symbolic `a`, (ii) the base of the
    expansion tower `φ̄(a-1, ω^{φ̄(a,0)·2})`, which degenerates at a = 1 (the chain is
    empty, so the base is `ω^{ε₀·2}` with no outer `φ̄(a-1,·)`) and therefore needs a
    case split, and (iii) the two-base tower comparison (expansion base vs fs base
    `φ̄(a-1, φ̄(a,0))`) generalized in `a`.
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


/-! ## §4 The bad root at row 1 (the machinery F1 and F3 need)

When the last column of a Stage-B matrix has row-1 entry 1, the bad root is
`parent M 1 (X-1)`, which runs through `iterParent` over the row-0 parent chain.
On a matrix whose row 0 is `0 1 2 … ` the chain is the descending list `downFrom`,
and filtering it by "row-1 entry < 1" leaves exactly the column 0. -/

/-- `[x-1, x-2, …, 0]`. -/
def downFrom : Nat → List Nat
  | 0 => []
  | x + 1 => x :: downFrom x

theorem mem_downFrom_zero : ∀ x, 1 ≤ x → 0 ∈ downFrom x
  | 0, h => by omega
  | 1, _ => by show (0:Nat) ∈ [0]; simp
  | x + 2, _ => by
    show (0:Nat) ∈ (x+1) :: downFrom (x+1)
    exact List.mem_cons_of_mem _ (mem_downFrom_zero (x+1) (by omega))

theorem iterParent_desc {f : Nat → Option Nat} {B : Nat}
    (h : ∀ x, 1 ≤ x → x ≤ B → f x = some (x-1)) (h0 : f 0 = none) :
    ∀ (fuel x : Nat), x ≤ fuel → x ≤ B → BMS.iterParent f fuel x = downFrom x
  | 0, x, hx, _ => by
    have hx0 : x = 0 := by omega
    subst hx0
    rfl
  | fuel + 1, 0, _, _ => by
    show (match f 0 with | none => [] | some p => p :: BMS.iterParent f fuel p) = downFrom 0
    rw [h0]
    rfl
  | fuel + 1, x + 1, hx, hB => by
    show (match f (x+1) with | none => [] | some p => p :: BMS.iterParent f fuel p) = downFrom (x+1)
    rw [h (x+1) (by omega) hB]
    show (x + 1 - 1) :: BMS.iterParent f fuel (x+1-1) = x :: downFrom x
    have hs : x + 1 - 1 = x := by omega
    rw [hs, iterParent_desc h h0 fuel x (by omega) (by omega)]

theorem filter_downFrom {P : Nat → Bool} (h0 : P 0 = true) :
    ∀ (x : Nat), (∀ p, 1 ≤ p → p ≤ x → P p = false) → (downFrom (x+1)).filter P = [0]
  | 0, _ => by
    show (List.filter P [0]) = [0]
    rw [List.filter_cons, h0]
    rfl
  | x + 1, hp => by
    show (List.filter P ((x+1) :: downFrom (x+1))) = [0]
    rw [List.filter_cons, hp (x+1) (by omega) (by omega)]
    simp only [Bool.false_eq_true, if_false]
    exact filter_downFrom h0 x (fun p hq1 hq2 => hp p hq1 (by omega))

/-! ## §5 The family F1 : `(0,0)(1,1)…(a,1)` = `φ̄(a,0)`

Writing `a = q+1`, the last column has row-1 entry 1, so `t = 1`, `Δ₀ = a` and the
bad blocks are the ladder `lad q` shifted by `a` per copy. -/

/-- The ladder block `(o,0)(o+1,1)…(o+p,1)` (`p+1` columns). -/
def lad (p o : Nat) : Matrix := ([o,0] : BMS.Col) :: ups (o+1) p

/-- `M1 q = (0,0)(1,1)…(q+1,1)`, i.e. `a = q+1`. -/
def M1 (q : Nat) : Matrix := lad (q+1) 0

theorem ups_range : ∀ (p o : Nat), ups o p = (List.range p).map (fun i => ([o+i, 1] : BMS.Col))
  | 0, _ => rfl
  | p + 1, o => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    show ([o,1] : BMS.Col) :: ups (o+1) p = ([o+0, 1] : BMS.Col) :: _
    have h1 : ((fun i => ([o+i, 1] : BMS.Col)) ∘ Nat.succ) = (fun i => ([(o+1)+i, 1] : BMS.Col)) := by
      funext i
      show ([o+(i+1), 1] : BMS.Col) = ([(o+1)+i, 1] : BMS.Col)
      have : o + (i+1) = (o+1) + i := by omega
      rw [this]
    rw [h1, ← ups_range p (o+1)]
    rfl

theorem ent_ups0 : ∀ (p o x : Nat), x < p → BMS.ent (ups o p) x 0 = o + x
  | 0, _, _, h => by omega
  | p + 1, o, 0, _ => rfl
  | p + 1, o, x + 1, h => by
    have h1 : BMS.ent (ups o (p+1)) (x+1) 0 = BMS.ent (ups (o+1) p) x 0 := by
      show ((([o,1] : BMS.Col) :: ups (o+1) p).getD (x+1) []).getD 0 0
          = ((ups (o+1) p).getD x []).getD 0 0
      rw [List.getD_cons_succ]
    rw [h1, ent_ups0 p (o+1) x (by omega)]
    omega

theorem ent_ups1 : ∀ (p o x : Nat), x < p → BMS.ent (ups o p) x 1 = 1
  | 0, _, _, h => by omega
  | p + 1, o, 0, _ => rfl
  | p + 1, o, x + 1, h => by
    have h1 : BMS.ent (ups o (p+1)) (x+1) 1 = BMS.ent (ups (o+1) p) x 1 := by
      show ((([o,1] : BMS.Col) :: ups (o+1) p).getD (x+1) []).getD 1 0
          = ((ups (o+1) p).getD x []).getD 1 0
      rw [List.getD_cons_succ]
    rw [h1, ent_ups1 p (o+1) x (by omega)]

theorem ent_M1_0 (q x : Nat) (h : x ≤ q+1) : BMS.ent (M1 q) x 0 = x := by
  cases x with
  | zero => rfl
  | succ y =>
    have h1 : BMS.ent (M1 q) (y+1) 0 = BMS.ent (ups 1 (q+1)) y 0 := by
      show ((([0,0] : BMS.Col) :: ups 1 (q+1)).getD (y+1) []).getD 0 0
          = ((ups 1 (q+1)).getD y []).getD 0 0
      rw [List.getD_cons_succ]
    rw [h1, ent_ups0 (q+1) 1 y (by omega)]
    omega

theorem ent_M1_1_zero (q : Nat) : BMS.ent (M1 q) 0 1 = 0 := rfl

theorem ent_M1_1 (q x : Nat) (h1 : 1 ≤ x) (h2 : x ≤ q+1) : BMS.ent (M1 q) x 1 = 1 := by
  cases x with
  | zero => omega
  | succ y =>
    have h3 : BMS.ent (M1 q) (y+1) 1 = BMS.ent (ups 1 (q+1)) y 1 := by
      show ((([0,0] : BMS.Col) :: ups 1 (q+1)).getD (y+1) []).getD 1 0
          = ((ups 1 (q+1)).getD y []).getD 1 0
      rw [List.getD_cons_succ]
    rw [h3, ent_ups1 (q+1) 1 y (by omega)]

theorem len_M1 (q : Nat) : (M1 q).length = q + 2 := by
  show (ups 1 (q+1)).length + 1 = q + 2
  rw [ups_len]

theorem parent0_M1 (q x : Nat) (h1 : 1 ≤ x) (h2 : x ≤ q+1) :
    BMS.parent (M1 q) 0 x = some (x-1) := by
  show (((List.range x).filter
      (fun p => decide (BMS.ent (M1 q) p 0 < BMS.ent (M1 q) x 0))).max?) = some (x-1)
  rw [Evidence.StageA.max?_filter_range]
  refine Evidence.StageA.lastSome_spec _ x (x-1) (by omega) ?_ ?_
  · rw [ent_M1_0 q (x-1) (by omega), ent_M1_0 q x (by omega)]
    exact decide_eq_true (by omega)
  · intro r hr1 hr2
    omega

theorem parent0_M1_zero (q : Nat) : BMS.parent (M1 q) 0 0 = none := rfl

theorem parent1_M1 (q x : Nat) (h1 : 1 ≤ x) (h2 : x ≤ q+1) :
    BMS.parent (M1 q) 1 x = some 0 := by
  obtain ⟨y, hy⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  subst hy
  have hchain : BMS.iterParent (BMS.parent (M1 q) 0) (y+1) (y+1) = downFrom (y+1) :=
    iterParent_desc (fun z hz1 hz2 => parent0_M1 q z hz1 (by omega)) (parent0_M1_zero q)
      (y+1) (y+1) (by omega) (by omega)
  have hP0 : (decide (BMS.ent (M1 q) 0 1 < 1)) = true := by
    rw [ent_M1_1_zero]
    exact decide_eq_true (by omega)
  have hPp : ∀ p, 1 ≤ p → p ≤ y → (decide (BMS.ent (M1 q) p 1 < 1)) = false := by
    intro p hp1 hp2
    rw [ent_M1_1 q p hp1 (by omega)]
    exact decide_eq_false (by omega)
  show (((BMS.iterParent (BMS.parent (M1 q) 0) (y+1) (y+1)).filter
      (fun p => decide (BMS.ent (M1 q) p 1 < BMS.ent (M1 q) (y+1) 1))).max?) = some 0
  rw [hchain, ent_M1_1 q (y+1) h1 h2,
    filter_downFrom (P := fun p => decide (BMS.ent (M1 q) p 1 < 1)) hP0 y hPp]
  rfl


/-! ### The nested `phiStep` chain -/

/-- `p` nested `phiStep`s at levels `j, j+1, …, j+p-1` (the innermost is level `j+p-1`). -/
def chainP (j : Nat) : Nat → Term → Term
  | 0, v => v
  | p + 1, v => Trans.Pair.phiStep (ofNat j) zero (chainP (j+1) p v)

theorem chainP_add : ∀ (p1 p2 j : Nat) (v : Term),
    chainP j (p1 + p2) v = chainP j p1 (chainP (j + p1) p2 v)
  | 0, p2, j, v => by
    rw [Nat.zero_add, Nat.add_zero]
    rfl
  | p1 + 1, p2, j, v => by
    rw [show p1 + 1 + p2 = (p1 + p2) + 1 from by omega]
    show Trans.Pair.phiStep (ofNat j) zero (chainP (j+1) (p1+p2) v)
        = chainP j (p1+1) (chainP (j + (p1+1)) p2 v)
    rw [chainP_add p1 p2 (j+1) v, show j + (p1+1) = (j+1) + p1 from by omega]
    rfl

theorem chainP_collapse : ∀ (p j c : Nat) (x : Term), j + p ≤ c →
    chainP j p (phi (ofNat c) x) = phi (ofNat c) x
  | 0, _, _, _, _ => rfl
  | p + 1, j, c, x, h => by
    show Trans.Pair.phiStep (ofNat j) zero (chainP (j+1) p (phi (ofNat c) x)) = _
    rw [chainP_collapse p (j+1) c x (by omega), phiStep_zero,
      show ((phi (ofNat c) x == zero) = false) from rfl]
    simp only [Bool.false_eq_true, if_false]
    rw [omegaNF_phi_ne_zero (by
        obtain ⟨d, hd⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
        rw [hd]; exact ofNat_ne_zero d),
      phiNF_collapse (lt_ofNat_mono (show j < c from by omega))]

/-! ### The ladder block and its expansion family -/

theorem decP_lad (q o : Nat) : Trans.Pair.decP (lad q (o+1)) = lad q o := by
  show ([o+1-1, 0] : BMS.Col) :: Trans.Pair.decP (ups (o+1+1) q) = ([o,0] : BMS.Col) :: ups (o+1) q
  have h : o + 1 - 1 = o := by omega
  rw [h, decP_ups q (o+1)]

theorem r0_lad (q o : Nat) (ho : 1 ≤ o) : ∀ c ∈ lad q o, Trans.Pair.r0 c ≠ 0 := by
  intro c hc
  rcases List.mem_cons.mp hc with h | h
  · subst h; show o ≠ 0; omega
  · exact r0_ups q (o+1) (by omega) c h

theorem inFrag_lad (q o : Nat) : Trans.Pair.inFrag (lad q o) = true := by
  show Trans.Pair.inFrag (([o,0] : BMS.Col) :: ups (o+1) q) = true
  rw [inFrag_cons, inFrag_ups q (o+1)]
  rfl

theorem len_lad (q o : Nat) : (lad q o).length = q + 1 := by
  show (ups (o+1) q).length + 1 = q + 1
  rw [ups_len]

theorem len_frep_lad : ∀ (m q o : Nat), (frep (lad q) (q+1) o m).length = (q+1) * m
  | 0, _, _ => rfl
  | m + 1, q, o => by
    show ((lad q o) ++ frep (lad q) (q+1) (o+(q+1)) m).length = (q+1) * (m+1)
    rw [List.length_append, len_lad, len_frep_lad m q (o+(q+1)), Nat.mul_succ]
    omega

theorem frep_lad_cons (q m : Nat) :
    frep (lad q) (q+1) 0 (m+1) = ([0,0] : BMS.Col) :: (ups 1 q ++ frep (lad q) (q+1) (q+1) m) := by
  show (lad q 0) ++ frep (lad q) (q+1) (0+(q+1)) m = _
  rw [show (0:Nat) + (q+1) = q+1 from by omega]
  rfl

/-- The value of the inner descending chain over the ladder expansion. -/
theorem oLAux_chain {q m : Nat} {v : Term} {N : Nat}
    (hv : ∀ fuel j, N ≤ fuel → Trans.Pair.oLAux fuel j (frep (lad q) (q+1) 0 m) = v) :
    ∀ (p j fuel : Nat), N + p ≤ fuel →
      Trans.Pair.oLAux fuel j (ups 0 p ++ frep (lad q) (q+1) p m) = chainP j p v
  | 0, j, fuel, hf => by
    show Trans.Pair.oLAux fuel j (frep (lad q) (q+1) 0 m) = v
    exact hv fuel j (by omega)
  | p + 1, j, fuel, hf => by
    cases fuel with
    | zero => omega
    | succ g =>
      have ht : ∀ c ∈ (ups 1 p ++ frep (lad q) (q+1) (p+1) m), Trans.Pair.r0 c ≠ 0 := by
        intro c hc
        rcases List.mem_append.mp hc with h1 | h1
        · exact r0_ups p 1 (by omega) c h1
        · exact r0_frep (fun o ho => r0_lad q o ho) m (p+1) (by omega) c h1
      have hd : Trans.Pair.decP (ups 1 p ++ frep (lad q) (q+1) (p+1) m)
          = ups 0 p ++ frep (lad q) (q+1) p m := by
        rw [decP_append, decP_ups, decP_frep (fun o => decP_lad q o) m p]
      show Trans.Pair.oLAux (g+1) j (([0,1] : BMS.Col)
        :: (ups 1 p ++ frep (lad q) (q+1) (p+1) m)) = chainP j (p+1) v
      rw [oLAux_single g j [0,1] _ ht]
      show Trans.Pair.phiStep (ofNat j) zero (Trans.Pair.oLAux g (j+1)
        (Trans.Pair.decP (ups 1 p ++ frep (lad q) (q+1) (p+1) m))) = chainP j (p+1) v
      rw [hd, oLAux_chain hv p (j+1) g (by omega)]
      rfl

/-- Closed form of `oLAux` on the F1 expansion family: the `m`-th `φ_q`-tower. -/
theorem valE1 : ∀ (m q fuel k : Nat), (q+1) * m + 1 ≤ fuel →
    Trans.Pair.oLAux fuel k (frep (lad q) (q+1) 0 m) = iterT (ofNat q) m
  | 0, _, fuel, k, _ => oLAux_nil fuel k
  | m + 1, q, fuel, k, hf => by
    have hmul : (q+1) * (m+1) = (q+1) * m + q + 1 := by rw [Nat.mul_succ]; omega
    cases fuel with
    | zero => omega
    | succ g =>
      have ht : ∀ c ∈ (ups 1 q ++ frep (lad q) (q+1) (q+1) m), Trans.Pair.r0 c ≠ 0 := by
        intro c hc
        rcases List.mem_append.mp hc with h1 | h1
        · exact r0_ups q 1 (by omega) c h1
        · exact r0_frep (fun o ho => r0_lad q o ho) m (q+1) (by omega) c h1
      have hd : Trans.Pair.decP (ups 1 q ++ frep (lad q) (q+1) (q+1) m)
          = ups 0 q ++ frep (lad q) (q+1) q m := by
        rw [decP_append, decP_ups, decP_frep (fun o => decP_lad q o) m q]
      have hv : ∀ fuel' j, (q+1) * m + 1 ≤ fuel' →
          Trans.Pair.oLAux fuel' j (frep (lad q) (q+1) 0 m) = iterT (ofNat q) m :=
        fun fuel' j hf' => valE1 m q fuel' j hf'
      rw [frep_lad_cons, oLAux_single g k [0,0] _ ht]
      show plus zero (omegaNF (Trans.Pair.oLAux g 1
        (Trans.Pair.decP (ups 1 q ++ frep (lad q) (q+1) (q+1) m)))) = _
      rw [hd, oLAux_chain hv q 1 g (by omega)]
      cases q with
      | zero =>
        show plus zero (omegaNF (iterT zero m)) = iterT zero (m+1)
        cases m with
        | zero =>
          show plus zero (omegaNF zero) = iterT zero 1
          rw [plus_zero_left (isAP_omegaNF zero)]
          rfl
        | succ m' =>
          rw [omegaNF_iterT_zero m', plus_zero_left (by rw [iterT_succ isSC_zero (m'+1)]; rfl)]
      | succ q' =>
        have hne : (ofNat (q'+1) : Term) ≠ zero := ofNat_ne_zero q'
        have hsc : (ofNat (q'+1) : Term).isSC = false := isSC_ofNat (q'+1)
        rw [chainP_add q' 1 1 (iterT (ofNat (q'+1)) m)]
        show plus zero (omegaNF (chainP 1 q'
          (Trans.Pair.phiStep (ofNat (1+q')) zero (iterT (ofNat (q'+1)) m)))) = _
        rw [show (1 + q') = (q' + 1) from by omega, phiStep_iterT hsc hne m,
          iterT_succ hsc m, chainP_collapse q' 1 (q'+1) (iterT (ofNat (q'+1)) m) (by omega),
          omegaNF_phi_ne_zero hne, plus_zero_left rfl, ← iterT_succ hsc m]


/-! ### The BM4 expansion of the F1 family -/

theorem iterParent_zero {f : Nat → Option Nat} (h0 : f 0 = none) :
    ∀ fuel, BMS.iterParent f fuel 0 = []
  | 0 => rfl
  | fuel + 1 => by
    show (match f 0 with | none => [] | some p => p :: BMS.iterParent f fuel p) = []
    rw [h0]

theorem parent1_M1_zero (q : Nat) : BMS.parent (M1 q) 1 0 = none := rfl

theorem iterParent1_M1 (q j : Nat) (h1 : 1 ≤ j) (h2 : j ≤ q+1) :
    BMS.iterParent (BMS.parent (M1 q) 1) j j = [0] := by
  obtain ⟨y, hy⟩ : ∃ y, j = y + 1 := ⟨j - 1, by omega⟩
  subst hy
  show (match BMS.parent (M1 q) 1 (y+1) with
        | none => [] | some p => p :: BMS.iterParent (BMS.parent (M1 q) 1) y p) = [0]
  rw [parent1_M1 q (y+1) h1 h2]
  show (0:Nat) :: BMS.iterParent (BMS.parent (M1 q) 1) y 0 = [0]
  rw [iterParent_zero (parent1_M1_zero q) y]

theorem contains_downFrom_zero : ∀ x, 1 ≤ x → (downFrom x).contains 0 = true
  | 0, h => by omega
  | 1, _ => rfl
  | x + 2, _ => by
    show (match ((0:Nat) == (x+1)) with
          | true => true | false => List.elem 0 (downFrom (x+1))) = true
    rw [show ((0:Nat) == (x+1)) = false from rfl]
    exact contains_downFrom_zero (x+1) (by omega)

theorem ascends_M1 (q j y : Nat) (hj : j ≤ q+1) (hy : y ≤ 1) :
    BMS.ascends (M1 q) 0 j y = true := by
  cases j with
  | zero => rfl
  | succ j' =>
    show ((j'+1 == 0) || ((BMS.iterParent (BMS.parent (M1 q) y) (j'+1) (j'+1)).contains 0)) = true
    rw [show ((j'+1 == 0)) = false from rfl]
    simp only [Bool.false_or]
    cases y with
    | zero =>
      rw [iterParent_desc (fun z hz1 hz2 => parent0_M1 q z hz1 (by omega)) (parent0_M1_zero q)
        (j'+1) (j'+1) (by omega) (by omega)]
      exact contains_downFrom_zero (j'+1) (by omega)
    | succ y' =>
      have hy1 : y' = 0 := by omega
      subst hy1
      rw [iterParent1_M1 q (j'+1) (by omega) (by omega)]
      rfl

theorem delta_M1_0 (q : Nat) : BMS.delta (M1 q) 0 1 0 = q+1 := by
  show (if 0 < 1 then BMS.ent (M1 q) ((M1 q).length - 1) 0 - BMS.ent (M1 q) 0 0 else 0) = q+1
  rw [if_pos (by omega), len_M1, show q + 2 - 1 = q + 1 from by omega,
    ent_M1_0 q (q+1) (by omega)]
  rfl

theorem delta_M1_1 (q : Nat) : BMS.delta (M1 q) 0 1 1 = 0 := by
  show (if 1 < 1 then BMS.ent (M1 q) ((M1 q).length - 1) 1 - BMS.ent (M1 q) 0 1 else 0) = 0
  rw [if_neg (by omega)]

theorem getLast_ups : ∀ (p o : Nat), (ups o (p+1)).getLast? = some ([o+p, 1] : BMS.Col)
  | 0, o => by
    show (([o,1] : BMS.Col) :: ups (o+1) 0).getLast? = _
    rfl
  | p + 1, o => by
    show (([o,1] : BMS.Col) :: ups (o+1) (p+1)).getLast? = some ([o+(p+1), 1] : BMS.Col)
    rw [show (([o,1] : BMS.Col) :: ups (o+1) (p+1))
        = ([[o,1]] : Matrix) ++ ups (o+1) (p+1) from rfl,
      Evidence.StageA.getLast?_append_right _ _ (by
        show ups (o+1) (p+1) ≠ []
        intro hc
        have := congrArg List.length hc
        rw [ups_len] at this
        simp at this),
      getLast_ups p (o+1), show (o+1)+p = o+(p+1) from by omega]

theorem getLast_M1 (q : Nat) : (M1 q).getLast? = some ([q+1, 1] : BMS.Col) := by
  show (([0,0] : BMS.Col) :: ups 1 (q+1)).getLast? = _
  rw [show (([0,0] : BMS.Col) :: ups 1 (q+1)) = ([[0,0]] : Matrix) ++ ups 1 (q+1) from rfl,
    Evidence.StageA.getLast?_append_right _ _ (by
      show ups 1 (q+1) ≠ []
      intro hc
      have := congrArg List.length hc
      rw [ups_len] at this
      simp at this),
    getLast_ups q 1, show (1:Nat)+q = q+1 from by omega]

theorem lnz_M1 (q : Nat) : BMS.lnz ([q+1, 1] : BMS.Col) = some 1 := by
  show (((List.range 2).filter (fun y => decide (([q+1,1] : BMS.Col).getD y 0 > 0))).max?) = some 1
  have h0 : (decide ((([q+1,1] : BMS.Col).getD 0 0) > 0)) = true := by
    show (decide ((q+1 : Nat) > 0)) = true
    exact decide_eq_true (by omega)
  show ((([0,1] : List Nat).filter (fun y => decide (([q+1,1] : BMS.Col).getD y 0 > 0))).max?)
      = some 1
  rw [List.filter_cons, h0]
  rfl

theorem expand_M1 (q n : Nat) : BMS.expand? (M1 q) n = some (frep (lad q) (q+1) 0 (n+1)) := by
  have hpar : BMS.parent (M1 q) 1 ((M1 q).length - 1) = some 0 := by
    rw [len_M1, show q + 2 - 1 = q + 1 from by omega]
    exact parent1_M1 q (q+1) (by omega) (by omega)
  have hlen1 : (M1 q).length - 1 - 0 = q + 1 := by rw [len_M1]; omega
  have hmap : ∀ (o : Nat),
      (List.range (q+1)).map (fun x => ([x + o, BMS.ent (M1 q) x 1] : BMS.Col)) = lad q o := by
    intro o
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    show ([0 + o, BMS.ent (M1 q) 0 1] : BMS.Col) :: _ = ([o,0] : BMS.Col) :: ups (o+1) q
    rw [show (0:Nat)+o = o from by omega, ent_M1_1_zero, ups_range q (o+1)]
    congr 1
    refine List.map_congr_left ?_
    intro i hi
    have hi' : i < q := List.mem_range.mp hi
    show ([(i+1) + o, BMS.ent (M1 q) (i+1) 1] : BMS.Col) = ([(o+1)+i, 1] : BMS.Col)
    rw [ent_M1_1 q (i+1) (by omega) (by omega), show (i+1)+o = (o+1)+i from by omega]
  have hbad : ∀ (c : Nat), (List.range (q+1)).map (fun x =>
      (List.range ([q+1,1] : BMS.Col).length).map (fun y => BMS.ent (M1 q) (0+x) y
        + c * BMS.delta (M1 q) 0 1 y
          * (if BMS.ascends (M1 q) 0 (0+x) y = true then 1 else 0)))
      = lad q ((q+1)*c + 0) := by
    intro c
    have hinner : ∀ x ∈ List.range (q+1),
        (List.range ([q+1,1] : BMS.Col).length).map (fun y => BMS.ent (M1 q) (0+x) y
          + c * BMS.delta (M1 q) 0 1 y
            * (if BMS.ascends (M1 q) 0 (0+x) y = true then 1 else 0))
        = ([x + ((q+1)*c + 0), BMS.ent (M1 q) x 1] : BMS.Col) := by
      intro x hx
      have hx' : x < q+1 := List.mem_range.mp hx
      show [BMS.ent (M1 q) (0+x) 0 + c * BMS.delta (M1 q) 0 1 0
              * (if BMS.ascends (M1 q) 0 (0+x) 0 = true then 1 else 0),
            BMS.ent (M1 q) (0+x) 1 + c * BMS.delta (M1 q) 0 1 1
              * (if BMS.ascends (M1 q) 0 (0+x) 1 = true then 1 else 0)] = _
      rw [show (0:Nat)+x = x from by omega, delta_M1_0, delta_M1_1,
        ascends_M1 q x 0 (by omega) (by omega), ascends_M1 q x 1 (by omega) (by omega),
        ent_M1_0 q x (by omega)]
      simp only [if_true, Nat.mul_one, Nat.mul_zero, Nat.add_zero]
      rw [show x + c * (q+1) = x + ((q+1)*c + 0) from by rw [Nat.mul_comm]; omega]
      rfl
    rw [List.map_congr_left hinner, hmap ((q+1)*c + 0)]
  simp only [BMS.expand?, getLast_M1, Option.bind_eq_bind, Option.bind_some, lnz_M1, hpar,
    Option.pure_def, hlen1]
  rw [List.map_congr_left (fun c _ => hbad c), flat_frep]
  rfl


/-! ### The F1 package -/

theorem onlyRow0_ups : ∀ (p o : Nat), onlyRow0 (ups o (p+1)) = false
  | _, o => by
    show onlyRow0 (([o,1] : BMS.Col) :: _) = false
    rw [onlyRow0_cons]
    rfl

theorem onlyRow0_E1 (q n : Nat) : onlyRow0 (frep (lad (q+1)) (q+2) 0 (n+1)) = false := by
  rw [frep_lad_cons]
  show onlyRow0 (([0,0] : BMS.Col) :: (ups 1 (q+1) ++ frep (lad (q+1)) (q+2) (q+2) n)) = false
  rw [onlyRow0_cons, onlyRow0_append, onlyRow0_ups q 1]
  rfl

theorem getLast_replicate_one : ∀ q, (List.replicate (q+1) (one : Term)).getLast? = some one
  | 0 => rfl
  | q + 1 => by
    show ((one : Term) :: List.replicate (q+1) one).getLast? = some one
    rw [show ((one : Term) :: List.replicate (q+1) one)
        = ([one] : List Term) ++ List.replicate (q+1) one from rfl,
      Evidence.StageA.getLast?_append_right _ _ (by
        intro hc
        have := congrArg List.length hc
        simp at this),
      getLast_replicate_one q]

theorem kindT_ofNat_succ (q : Nat) : kindT (ofNat (q+1)) = KindT.isSucc := by
  rw [Evidence.StageA.kindT_ne_zero (ofNat_ne_zero q), toList_ofNat, getLast_replicate_one q]
  rfl

theorem predT_ofNat_succ (q : Nat) : predT (ofNat (q+1)) = ofNat q := by
  rw [Evidence.StageA.predT_eq (by rw [toList_ofNat, getLast_replicate_one q]; rfl),
    toList_ofNat,
    show (List.replicate (q+1) (one : Term)).dropLast = List.replicate q one from by
      rw [List.replicate_succ', List.dropLast_concat],
    ← mulNat_one_ofNat]
  rfl

/-- The term of the family: `φ̄(a,0)` with `a = q+1`. -/
def t1 (q : Nat) : Term := phi (ofNat (q+1)) zero

/-- The closed form of the n-th expansion: the fundamental sequence at n+1. -/
def oval1 (q n : Nat) : Term := fsN (t1 q) (n+1)

theorem fs_t1 (q k : Nat) : fsN (t1 q) k = iterT (ofNat q) k := by
  show fsN (phi (ofNat (q+1)) zero) k = _
  rw [fsN_phi_zero (isSC_ofNat (q+1)) (kindT_ofNat_succ q) k, predT_ofNat_succ q]

theorem e3_val1 (q n : Nat) : o? (BMS.expand (M1 q) n) = some (oval1 q n) := by
  cases q with
  | zero => exact Rows.ProofsB.R1.e3_val n
  | succ q' =>
    have hE : BMS.expand (M1 (q'+1)) n = frep (lad (q'+1)) (q'+2) 0 (n+1) := by
      show (BMS.expand? (M1 (q'+1)) n).getD [] = _
      rw [expand_M1]; rfl
    show o? (BMS.expand (M1 (q'+1)) n) = some (fsN (t1 (q'+1)) (n+1))
    rw [hE, o?_pair (onlyRow0_E1 q' n) (inFrag_frep (fun o => inFrag_lad (q'+1) o) (n+1) 0),
      len_frep_lad (n+1) (q'+1) 0, valE1 (n+1) (q'+1) _ 1 (by omega), fs_t1]

theorem ltF_iterT_bound' {a c : Term} {N : Nat} (ha : a.isSC = false) (hac : (a == c) = false)
    (hlt : ∀ f, N ≤ f → ltF f a c = true) :
    ∀ (m f : Nat), N + m + 1 ≤ f → ltF f (iterT a m) (phi c zero) = true
  | 0, f, hf => ltF_zero (by omega) (by intro hh; exact Term.noConfusion hh)
  | m + 1, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      rw [iterT_succ ha m]
      exact ltF_phi_fst hac (hlt g (by omega)) (ltF_iterT_bound' ha hac hlt m g (by omega))

theorem e3_lt1 (q n : Nat) : lt (oval1 q n) (t1 q) = true := by
  show lt (fsN (t1 q) (n+1)) (t1 q) = true
  rw [fs_t1]
  show lt (iterT (ofNat q) (n+1)) (phi (ofNat (q+1)) zero) = true
  refine Rows.ProofsB.lt_of_ltF (N := (q+2) + (n+1) + 1)
    (fun f hf => ltF_iterT_bound' (isSC_ofNat q) (ofNat_bne (by omega))
      (fun f' hf' => ltF_ofNat_mono q (q+1) f' (by omega) (by omega)) (n+1) f hf) ?_
  have h1 := deg_iterT (isSC_ofNat q) (n+1)
  have h2 := deg_ofNat (q+1)
  show (q+2) + (n+1) + 1
      ≤ 2 * ((iterT (ofNat q) (n+1)).deg + (1 + (ofNat (q+1)).deg + (zero : Term).deg)) + 8
  omega

/-- **(b)** with witness `k := n+2`. -/
theorem e3_over1 (q n : Nat) : lt (oval1 q n) (fsN (t1 q) (n+2)) = true := by
  show lt (fsN (t1 q) (n+1)) (fsN (t1 q) (n+2)) = true
  rw [fs_t1, fs_t1]
  exact lt_iterT_succ (isSC_ofNat q) (n+1)

/-- **(c)** with witness `n := k+1`. -/
theorem e3_under1 (q k : Nat) : lt (fsN (t1 q) (k+1)) (oval1 q (k+1)) = true := by
  show lt (fsN (t1 q) (k+1)) (fsN (t1 q) (k+2)) = true
  rw [fs_t1, fs_t1]
  exact lt_iterT_succ (isSC_ofNat q) (k+1)

/-- **E3 for the F1 family**, for every `a = q+1 ≥ 1`: `(0,0)(1,1)…(a,1) = φ̄(a,0)`. -/
theorem e3_F1family (q : Nat) :
    (∀ n, o? (BMS.expand (M1 q) n) = some (oval1 q n))
    ∧ (∀ n, lt (oval1 q n) (t1 q) = true)
    ∧ (∀ n, lt (oval1 q n) (fsN (t1 q) (n + 2)) = true)
    ∧ (∀ k, lt (fsN (t1 q) (k + 1)) (oval1 q (k + 1)) = true) :=
  ⟨e3_val1 q, e3_lt1 q, e3_over1 q, e3_under1 q⟩

/-! ### The three table rows are instances -/

theorem m1_zero : M1 0 = Rows.ProofsB.R1.m0 := rfl
theorem m1_one : M1 1 = Rows.ProofsB.R6.m0 := rfl
theorem m1_two : M1 2 = Rows.ProofsB.R9.m0 := rfl
theorem t1_zero : t1 0 = Rows.ProofsB.R1.t0 := rfl
theorem t1_one : t1 1 = Rows.ProofsB.R6.t0 := rfl
theorem t1_two : t1 2 = Rows.ProofsB.R9.t0 := rfl

example (n : Nat) : o? (BMS.expand Rows.ProofsB.R1.m0 n)
    = some (fsN Rows.ProofsB.R1.t0 (n+1)) := e3_val1 0 n
example (n : Nat) : o? (BMS.expand Rows.ProofsB.R6.m0 n)
    = some (fsN Rows.ProofsB.R6.t0 (n+1)) := e3_val1 1 n
example (n : Nat) : o? (BMS.expand Rows.ProofsB.R9.m0 n)
    = some (fsN Rows.ProofsB.R9.t0 (n+1)) := e3_val1 2 n

/-- Beyond the table: `a = 4`, i.e. `(0,0)(1,1)(2,1)(3,1)(4,1) = φ̄(4,0)`. -/
example (n : Nat) : o? (BMS.expand [[0,0],[1,1],[2,1],[3,1],[4,1]] n)
    = some (fsN (phi (ofNat 4) zero) (n+1)) := e3_val1 3 n

#guard (List.range 4).all fun q => (List.range 4).all fun n =>
  Trans.o? (BMS.expand (M1 q) n) == some (fsN (t1 q) (n+1))
#guard (List.range 5).all fun q => Trans.o? (M1 q) == some (t1 q)


end Evidence.StageB
