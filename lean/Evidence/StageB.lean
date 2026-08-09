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
  §6–7 F3 : (0,0)(1,1)…(a,1)(a,1)   =  φ̄(a,1)   NO shift exists — the full 4-part
      package, witnesses kw n = n+1, nw k = k+1.
      `e3_F3family`; a = 1 is Rows.ProofsB.R3, a = 2 is Rows.ProofsB.R7.

F1 needs the genuinely new machinery of §4: its last column has row-1 entry 1, so
`t = 1`, `Δ₀ = a ≠ 0`, and the bad root is `parent M 1 (X-1)`, which runs through
`iterParent` over the row-0 parent chain.  §4 proves that chain is `downFrom` and
that filtering it by "row-1 entry < 1" leaves exactly the column 0, for a symbolic
parameter.  §5 then computes the value with `chainP` (the `a-1` nested `phiStep`s
that the descending `(0,1)`-heads produce, of which only the innermost survives —
`chainP_collapse`).

F3 : (0,0)(1,1)…(a,1)(a,1) = φ̄(a,1)  (§6 the BMS side, §7 the 𝔗(M) side;
R3 at a = 1, R7 at a = 2) — PROVED for symbolic a = q+1, `e3_F3family`.

  This is the family where the expansion and the fundamental sequence are genuinely
  different cofinal sequences: both climb the `φ_q`-tower, but over different bases,

      expansions            `bse  q = φ̄(q, xbase q)`,  `xbase q = φ̄(a,0)·2`   (q = 0)
                                                                 `ω^(φ̄(a,0)·2)` (q ≥ 1)
      fundamental sequence  `sbse q = φ̄(q, φ̄(a,0))`               and `sbse q < bse q`,

  so no index shift makes them equal and only the 4-part package survives:
      oval3 q 0 = φ̄(a,0),   oval3 q (n+1) = twr q n  (the `φ_q`-tower over `bse q`),
      fsN (φ̄(a,1)) (k+1)   = the same tower over `sbse q`.

  BMS side (§6):
    `expand_M3` — the whole BM4 expansion.  Bad root 0 via §4; Δ₀ = a; the bad part
      is the FULL ladder `lad (q+1)` while the step is only `q+1`, so consecutive
      copies overlap in one column.  That overlap is why the expansion contains
      interior row-0 zeros and hence why F3 is the no-shift family.
    `oLAux_chainV` — the descending `(0,1)`-chain lemma, indexed by the FINAL level.
    `valV3` — the accumulator recursion
        VV q 0 = φ̄(a,0),   VV q (m+1) = φ̄(a,0) + ω^(chainP 1 q (VV q m)).
    `valE3` / `o?_expand_M3` — o?(M3 q [n]) = some (ω^(chainP 1 q (VV q n))).

  𝔗(M) side (§7), in dependency order:
    (A) `step_zt`      omegaNF (chainP 1 q (zt q)) = zt q
    (B) `VV_one`       VV q 1 = add (zt q) (zt q)          (via `plus_self`)
    (C) `step_add_zt`  omegaNF (chainP 1 q (add (zt q) (zt q))) = bse q   -- case split
    (D) `step_twr`     omegaNF (chainP 1 q (twr q j)) = twr q (j+1)       -- case split
    (E) `le_twr_zt` (through `ltF_twr_not`), hence `VV_succ2 : VV q (m+2) = twr q m`
        by `plus_drop`; this closes part (a) as `oval3_eq` / `e3_val3`
    (F) `fs_t3`        fsN (φ̄(a,1)) (k+1) = twB q (sbse q) k
    (G) the `ltF` base comparisons and the tower monotonicity `ltF_twB_mono`,
        giving `e3_lt3`, `e3_over3`, `e3_under3`.
  `oval3_zero` / `oval3_one` prove that the value functions of R3 and R7 are literally
  the q = 0 and q = 1 instances of `oval3`, and `#guard`s check every part against
  computation for q < 4, n < 5.

  FOUR FACTS THAT DECIDE THE SHAPE OF §6–§7 (each was a wrong turn first):
    * `oLAux_chainV` CANNOT be stated with a level-independent hypothesis the way
      F1's `oLAux_chain` is: F1's inner matrix starts with `(0,0)` (r1 = 0 resets the
      level), F3's starts with `(0,1)`, so its value genuinely depends on the level.
      The version here carries `j + p = L` and requires the hypothesis only at `L`.
    * In (C)/(D) the innermost `phiStep` is at level q and its argument is a
      `φ̄(ofNat q, ·)`, so it WRAPS (`phiNF_phi_arg`) — it does not collapse; only the
      OUTER q-1 steps collapse (`chainP_collapse` with j + p = 1 + (q-1) = q ≤ q).
      Getting this backwards is the natural mistake.
    * The tower step is `φ̄(ofNat q, ·)` uniformly, but for q = 0 it is supplied by
      the outer `ω^` (`omegaNF = phiNF zero` there) and for q ≥ 1 by the innermost
      `phiStep`; that is exactly why `xbase` needs the case split — at q = 0 the
      chain is empty, so the base is `φ̄(0, φ̄(a,0)·2)` with no extra `φ̄(0,·)` layer.
    * (F) at k = 0: `iterPhiAt (ofNat q) (plus (zt q) one) 1 = φ̄(ofNat q, zt q)` goes
      through the `phiNFsucc` "down" branch (`splitFin (zt q + 1) = (zt q, 1)`,
      `down = zt q`, taken because `lt (ofNat q) (ofNat (q+1))`).  R3/R7 discharged
      the corresponding step with `decide` on closed terms; for symbolic q it is the
      bespoke lemma `phiNF_zt_one`, the one step with no reusable analogue here.
    Fuel accounting is tight, not slack: `valV3`/`valE3` need `(q+2)*m + 1` and the
    matrix supplies exactly `(q+2)*(n+1) + 1 = length + 1`.
  Templates: R3 (`tow`, `W`, `ltF_tow_not_lt`, `W_succ2`) and R7 (`etow`, `VV`,
  `ltF_etow_not_lt`, `W_succ2`) in Rows/ProofsB.lean are the q = 0 and q = 1 cases of
  exactly (A)–(G); §7 is those two developments generalized in `q`.

FRONTIER (not proved here) — §8 is the feasibility map, read it before extending:
  * A genuinely region-wide theorem additionally needs a 2-row standardness
    invariant and an invariant carried on the `oLAux` accumulator (`logPhi k acc`
    defined and `acc` a φ_k-value), since the Stage-B value function is an
    accumulator fold, not a plain sum.  No relation to `BMS.Standard` is claimed
    anywhere in this file.
  * §8 measures both.  Its main finding is NEGATIVE: the Stage-A predicate `stdSeq`
    does not lift — a `stdPair` built the same way is false, not merely unproved
    (§8.2, with the counterexamples `#guard`ed there).  The accumulator invariant
    above is confirmed, and the missing prerequisite is a fuel-free `oLAux`
    (§8.3).  §8.5 names the recommended next target, the family
    `(0,0)(1,1)…(a,1)(b,r)` with its closed forms already `#guard`ed.

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


/-! ## §6 The family F3 : `(0,0)(1,1)…(a,1)(a,1)` = `φ̄(a,1)` — the BM4 expansion

Writing `a = q+1`, this is `M1 q` with its last column repeated.  The last column
still has row-1 entry 1, so `t = 1` and §4 applies; the bad root is again 0, but the
bad part is now the WHOLE ladder `lad (q+1)` while the step is only `q+1`, so the
copies overlap in one column — which is what makes the block structure of the
expansion contain interior row-0 zeros. -/

def M3 (q : Nat) : Matrix := M1 q ++ [[q+1, 1]]

theorem getD_append_lt' {α : Type _} (l r : List α) (p : Nat) (h : p < l.length) (d : α) :
    (l ++ r).getD p d = l.getD p d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_ge' {α : Type _} (l r : List α) (p : Nat) (h : l.length ≤ p) (d : α) :
    (l ++ r).getD p d = r.getD (p - l.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem len_M3 (q : Nat) : (M3 q).length = q + 3 := by
  show ((M1 q) ++ [[q+1,1]]).length = q + 3
  rw [List.length_append, len_M1]
  rfl

theorem ent_M3_lt (q x y : Nat) (h : x < q + 2) : BMS.ent (M3 q) x y = BMS.ent (M1 q) x y := by
  show (((M1 q ++ [[q+1,1]]).getD x []).getD y 0) = (((M1 q).getD x []).getD y 0)
  rw [getD_append_lt' _ _ x (by rw [len_M1]; omega)]

theorem ent_M3_top0 (q : Nat) : BMS.ent (M3 q) (q+2) 0 = q + 1 := by
  show (((M1 q ++ [[q+1,1]]).getD (q+2) []).getD 0 0) = q + 1
  rw [getD_append_ge' _ _ (q+2) (by rw [len_M1]; omega), len_M1,
    show q + 2 - (q+2) = 0 from by omega]
  rfl

theorem ent_M3_top1 (q : Nat) : BMS.ent (M3 q) (q+2) 1 = 1 := by
  show (((M1 q ++ [[q+1,1]]).getD (q+2) []).getD 1 0) = 1
  rw [getD_append_ge' _ _ (q+2) (by rw [len_M1]; omega), len_M1,
    show q + 2 - (q+2) = 0 from by omega]
  rfl


theorem ent_M3_0 (q x : Nat) (h : x ≤ q+1) : BMS.ent (M3 q) x 0 = x := by
  rw [ent_M3_lt q x 0 (by omega), ent_M1_0 q x h]

theorem ent_M3_1_zero (q : Nat) : BMS.ent (M3 q) 0 1 = 0 := by
  rw [ent_M3_lt q 0 1 (by omega), ent_M1_1_zero]

theorem ent_M3_1 (q x : Nat) (h1 : 1 ≤ x) (h2 : x ≤ q+1) : BMS.ent (M3 q) x 1 = 1 := by
  rw [ent_M3_lt q x 1 (by omega), ent_M1_1 q x h1 h2]

theorem parent0_M3 (q x : Nat) (h1 : 1 ≤ x) (h2 : x ≤ q+1) :
    BMS.parent (M3 q) 0 x = some (x-1) := by
  show (((List.range x).filter
      (fun p => decide (BMS.ent (M3 q) p 0 < BMS.ent (M3 q) x 0))).max?) = some (x-1)
  rw [Evidence.StageA.max?_filter_range]
  refine Evidence.StageA.lastSome_spec _ x (x-1) (by omega) ?_ ?_
  · rw [ent_M3_0 q (x-1) (by omega), ent_M3_0 q x (by omega)]
    exact decide_eq_true (by omega)
  · intro r hr1 hr2
    omega

theorem parent0_M3_zero (q : Nat) : BMS.parent (M3 q) 0 0 = none := rfl

theorem parent0_M3_top (q : Nat) : BMS.parent (M3 q) 0 (q+2) = some q := by
  show (((List.range (q+2)).filter
      (fun p => decide (BMS.ent (M3 q) p 0 < BMS.ent (M3 q) (q+2) 0))).max?) = some q
  rw [Evidence.StageA.max?_filter_range, ent_M3_top0]
  refine Evidence.StageA.lastSome_spec _ (q+2) q (by omega) ?_ ?_
  · rw [ent_M3_0 q q (by omega)]
    exact decide_eq_true (by omega)
  · intro r hr1 hr2
    have hr : r = q + 1 := by omega
    subst hr
    rw [ent_M3_0 q (q+1) (by omega)]
    exact decide_eq_false (by omega)

theorem chain_M3_top (q : Nat) :
    BMS.iterParent (BMS.parent (M3 q) 0) (q+2) (q+2) = downFrom (q+1) := by
  show (match BMS.parent (M3 q) 0 (q+2) with
        | none => [] | some p => p :: BMS.iterParent (BMS.parent (M3 q) 0) (q+1) p)
      = downFrom (q+1)
  rw [parent0_M3_top q]
  show q :: BMS.iterParent (BMS.parent (M3 q) 0) (q+1) q = downFrom (q+1)
  rw [iterParent_desc (fun z hz1 hz2 => parent0_M3 q z hz1 (by omega)) (parent0_M3_zero q)
    (q+1) q (by omega) (by omega)]
  rfl

theorem parent1_M3 (q j : Nat) (h1 : 1 ≤ j) (h2 : j ≤ q+1) :
    BMS.parent (M3 q) 1 j = some 0 := by
  obtain ⟨y, hy⟩ : ∃ y, j = y + 1 := ⟨j - 1, by omega⟩
  subst hy
  have hchain : BMS.iterParent (BMS.parent (M3 q) 0) (y+1) (y+1) = downFrom (y+1) :=
    iterParent_desc (fun z hz1 hz2 => parent0_M3 q z hz1 (by omega)) (parent0_M3_zero q)
      (y+1) (y+1) (by omega) (by omega)
  have hP0 : (decide (BMS.ent (M3 q) 0 1 < 1)) = true := by
    rw [ent_M3_1_zero]
    exact decide_eq_true (by omega)
  have hPp : ∀ p, 1 ≤ p → p ≤ y → (decide (BMS.ent (M3 q) p 1 < 1)) = false := by
    intro p hp1 hp2
    rw [ent_M3_1 q p hp1 (by omega)]
    exact decide_eq_false (by omega)
  show (((BMS.iterParent (BMS.parent (M3 q) 0) (y+1) (y+1)).filter
      (fun p => decide (BMS.ent (M3 q) p 1 < BMS.ent (M3 q) (y+1) 1))).max?) = some 0
  rw [hchain, ent_M3_1 q (y+1) h1 h2,
    filter_downFrom (P := fun p => decide (BMS.ent (M3 q) p 1 < 1)) hP0 y hPp]
  rfl

theorem parent1_M3_top (q : Nat) : BMS.parent (M3 q) 1 (q+2) = some 0 := by
  have hP0 : (decide (BMS.ent (M3 q) 0 1 < 1)) = true := by
    rw [ent_M3_1_zero]
    exact decide_eq_true (by omega)
  have hPp : ∀ p, 1 ≤ p → p ≤ q → (decide (BMS.ent (M3 q) p 1 < 1)) = false := by
    intro p hp1 hp2
    rw [ent_M3_1 q p hp1 (by omega)]
    exact decide_eq_false (by omega)
  show (((BMS.iterParent (BMS.parent (M3 q) 0) (q+2) (q+2)).filter
      (fun p => decide (BMS.ent (M3 q) p 1 < BMS.ent (M3 q) (q+2) 1))).max?) = some 0
  rw [chain_M3_top q, ent_M3_top1,
    filter_downFrom (P := fun p => decide (BMS.ent (M3 q) p 1 < 1)) hP0 q hPp]
  rfl

theorem parent1_M3_zero (q : Nat) : BMS.parent (M3 q) 1 0 = none := rfl

theorem ascends_M3 (q j y : Nat) (hj : j ≤ q+1) (hy : y ≤ 1) :
    BMS.ascends (M3 q) 0 j y = true := by
  cases j with
  | zero => rfl
  | succ j' =>
    show ((j'+1 == 0) || ((BMS.iterParent (BMS.parent (M3 q) y) (j'+1) (j'+1)).contains 0)) = true
    rw [show ((j'+1 == 0)) = false from rfl]
    simp only [Bool.false_or]
    cases y with
    | zero =>
      rw [iterParent_desc (fun z hz1 hz2 => parent0_M3 q z hz1 (by omega)) (parent0_M3_zero q)
        (j'+1) (j'+1) (by omega) (by omega)]
      exact contains_downFrom_zero (j'+1) (by omega)
    | succ y' =>
      have hy1 : y' = 0 := by omega
      subst hy1
      show ((BMS.iterParent (BMS.parent (M3 q) 1) (j'+1) (j'+1)).contains 0) = true
      rw [show BMS.iterParent (BMS.parent (M3 q) 1) (j'+1) (j'+1) = [0] from by
        show (match BMS.parent (M3 q) 1 (j'+1) with
              | none => [] | some p => p :: BMS.iterParent (BMS.parent (M3 q) 1) j' p) = [0]
        rw [parent1_M3 q (j'+1) (by omega) (by omega)]
        show (0:Nat) :: BMS.iterParent (BMS.parent (M3 q) 1) j' 0 = [0]
        rw [iterParent_zero (parent1_M3_zero q) j']]
      rfl

theorem delta_M3_0 (q : Nat) : BMS.delta (M3 q) 0 1 0 = q+1 := by
  show (if 0 < 1 then BMS.ent (M3 q) ((M3 q).length - 1) 0 - BMS.ent (M3 q) 0 0 else 0) = q+1
  rw [if_pos (by omega), len_M3, show q + 3 - 1 = q + 2 from by omega, ent_M3_top0,
    ent_M3_0 q 0 (by omega)]
  omega

theorem delta_M3_1 (q : Nat) : BMS.delta (M3 q) 0 1 1 = 0 := by
  show (if 1 < 1 then BMS.ent (M3 q) ((M3 q).length - 1) 1 - BMS.ent (M3 q) 0 1 else 0) = 0
  rw [if_neg (by omega)]

theorem getLast_M3 (q : Nat) : (M3 q).getLast? = some ([q+1, 1] : BMS.Col) :=
  List.getLast?_concat

theorem expand_M3 (q n : Nat) :
    BMS.expand? (M3 q) n = some (frep (lad (q+1)) (q+1) 0 (n+1)) := by
  have hpar : BMS.parent (M3 q) 1 ((M3 q).length - 1) = some 0 := by
    rw [len_M3, show q + 3 - 1 = q + 2 from by omega]
    exact parent1_M3_top q
  have hlen1 : (M3 q).length - 1 - 0 = q + 2 := by rw [len_M3]; omega
  have hmap : ∀ (o : Nat),
      (List.range (q+2)).map (fun x => ([x + o, BMS.ent (M3 q) x 1] : BMS.Col))
        = lad (q+1) o := by
    intro o
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    show ([0 + o, BMS.ent (M3 q) 0 1] : BMS.Col) :: _ = ([o,0] : BMS.Col) :: ups (o+1) (q+1)
    rw [show (0:Nat)+o = o from by omega, ent_M3_1_zero, ups_range (q+1) (o+1)]
    congr 1
    refine List.map_congr_left ?_
    intro i hi
    have hi' : i < q+1 := List.mem_range.mp hi
    show ([(i+1) + o, BMS.ent (M3 q) (i+1) 1] : BMS.Col) = ([(o+1)+i, 1] : BMS.Col)
    rw [ent_M3_1 q (i+1) (by omega) (by omega), show (i+1)+o = (o+1)+i from by omega]
  have hbad : ∀ (c : Nat), (List.range (q+2)).map (fun x =>
      (List.range ([q+1,1] : BMS.Col).length).map (fun y => BMS.ent (M3 q) (0+x) y
        + c * BMS.delta (M3 q) 0 1 y
          * (if BMS.ascends (M3 q) 0 (0+x) y = true then 1 else 0)))
      = lad (q+1) ((q+1)*c + 0) := by
    intro c
    have hinner : ∀ x ∈ List.range (q+2),
        (List.range ([q+1,1] : BMS.Col).length).map (fun y => BMS.ent (M3 q) (0+x) y
          + c * BMS.delta (M3 q) 0 1 y
            * (if BMS.ascends (M3 q) 0 (0+x) y = true then 1 else 0))
        = ([x + ((q+1)*c + 0), BMS.ent (M3 q) x 1] : BMS.Col) := by
      intro x hx
      have hx' : x < q+2 := List.mem_range.mp hx
      show [BMS.ent (M3 q) (0+x) 0 + c * BMS.delta (M3 q) 0 1 0
              * (if BMS.ascends (M3 q) 0 (0+x) 0 = true then 1 else 0),
            BMS.ent (M3 q) (0+x) 1 + c * BMS.delta (M3 q) 0 1 1
              * (if BMS.ascends (M3 q) 0 (0+x) 1 = true then 1 else 0)] = _
      rw [show (0:Nat)+x = x from by omega, delta_M3_0, delta_M3_1,
        ascends_M3 q x 0 (by omega) (by omega), ascends_M3 q x 1 (by omega) (by omega),
        ent_M3_0 q x (by omega)]
      simp only [if_true, Nat.mul_one, Nat.mul_zero, Nat.add_zero]
      rw [show x + c * (q+1) = x + ((q+1)*c + 0) from by rw [Nat.mul_comm]; omega]
      rfl
    rw [List.map_congr_left hinner, hmap ((q+1)*c + 0)]
  simp only [BMS.expand?, getLast_M3, Option.bind_eq_bind, Option.bind_some, lnz_M1, hpar,
    Option.pure_def, hlen1]
  rw [List.map_congr_left (fun c _ => hbad c), flat_frep]
  rfl


/-! ### F3, value side: the accumulator recursion

The F3 expansion is `frep (lad (q+1)) (q+1) 0 (n+1)`; because the copies overlap in
one column, stripping the leading `(0,0)` and `q` further `(0,1)`-heads lands on
`(0,1) :: frep (lad (q+1)) (q+1) 0 n`, whose `blocksP` has TWO blocks — this is the
accumulator recursion that makes F3 a no-shift family. -/

theorem oLAux_chainV {B : Nat → Matrix} {step m : Nat} {v : Term} {N L : Nat}
    (hdec : ∀ o, Trans.Pair.decP (B (o+1)) = B o)
    (hr0 : ∀ o, 1 ≤ o → ∀ c ∈ B o, Trans.Pair.r0 c ≠ 0)
    (hv : ∀ fuel, N ≤ fuel →
      Trans.Pair.oLAux fuel L (([0,1] : BMS.Col) :: frep B step 0 m) = v) :
    ∀ (p j fuel : Nat), j + p = L → N + p ≤ fuel →
      Trans.Pair.oLAux fuel j (ups 0 (p+1) ++ frep B step p m) = chainP j p v
  | 0, j, fuel, hjp, hf => by
    show Trans.Pair.oLAux fuel j (([0,1] : BMS.Col) :: frep B step 0 m) = v
    rw [show j = L from by omega]
    exact hv fuel (by omega)
  | p + 1, j, fuel, hjp, hf => by
    cases fuel with
    | zero => omega
    | succ g =>
      have ht : ∀ c ∈ (ups 1 (p+1) ++ frep B step (p+1) m), Trans.Pair.r0 c ≠ 0 := by
        intro c hc
        rcases List.mem_append.mp hc with h1 | h1
        · exact r0_ups (p+1) 1 (by omega) c h1
        · exact r0_frep hr0 m (p+1) (by omega) c h1
      have hd : Trans.Pair.decP (ups 1 (p+1) ++ frep B step (p+1) m)
          = ups 0 (p+1) ++ frep B step p m := by
        rw [decP_append, decP_ups, decP_frep hdec m p]
      show Trans.Pair.oLAux (g+1) j (([0,1] : BMS.Col)
        :: (ups 1 (p+1) ++ frep B step (p+1) m)) = chainP j (p+1) v
      rw [oLAux_single g j [0,1] _ ht]
      show Trans.Pair.phiStep (ofNat j) zero (Trans.Pair.oLAux g (j+1)
        (Trans.Pair.decP (ups 1 (p+1) ++ frep B step (p+1) m))) = chainP j (p+1) v
      rw [hd, oLAux_chainV hdec hr0 hv p (j+1) g (by omega) (by omega)]
      rfl

/-- `φ̄(a,0)` with `a = q+1`. -/
def zt (q : Nat) : Term := phi (ofNat (q+1)) zero

/-- The accumulator of the F3 reading. -/
def VV (q : Nat) : Nat → Term
  | 0 => zt q
  | m + 1 => plus (zt q) (omegaNF (chainP 1 q (VV q m)))

theorem frep_lad_cons' (p q m : Nat) :
    frep (lad p) (q+1) 0 (m+1) = ([0,0] : BMS.Col) :: (ups 1 p ++ frep (lad p) (q+1) (q+1) m) := by
  show (lad p 0) ++ frep (lad p) (q+1) (0+(q+1)) m = _
  rw [show (0:Nat) + (q+1) = q+1 from by omega]
  rfl

theorem valV3 : ∀ (m q fuel : Nat), (q+2) * m + 1 ≤ fuel →
    Trans.Pair.oLAux fuel (q+1) (([0,1] : BMS.Col) :: frep (lad (q+1)) (q+1) 0 m) = VV q m
  | 0, q, fuel, hf => by
    show Trans.Pair.oLAux fuel (q+1) (zs 1) = VV q 0
    rw [oLAux_zs 0 fuel (q+1) (by omega)]
    rfl
  | m + 1, q, fuel, hf => by
    have hmul : (q+2) * (m+1) = (q+2) * m + q + 2 := by rw [Nat.mul_succ]; omega
    cases fuel with
    | zero => omega
    | succ g =>
      have htB : ∀ c ∈ (ups 1 (q+1) ++ frep (lad (q+1)) (q+1) (q+1) m),
          Trans.Pair.r0 c ≠ 0 := by
        intro c hc
        rcases List.mem_append.mp hc with h1 | h1
        · exact r0_ups (q+1) 1 (by omega) c h1
        · exact r0_frep (fun o ho => r0_lad (q+1) o ho) m (q+1) (by omega) c h1
      have hb : Trans.Pair.blocksP (([0,1] : BMS.Col) :: frep (lad (q+1)) (q+1) 0 (m+1))
          = ([[0,1]] : Matrix) :: [(([0,0] : BMS.Col)
              :: (ups 1 (q+1) ++ frep (lad (q+1)) (q+1) (q+1) m))] := by
        rw [frep_lad_cons' (q+1) q m, blocksP_cons_zero [0,1] [0,0] _ rfl,
          blocksP_single [0,0] _ htB]
      have hd : Trans.Pair.decP (ups 1 (q+1) ++ frep (lad (q+1)) (q+1) (q+1) m)
          = ups 0 (q+1) ++ frep (lad (q+1)) (q+1) q m := by
        rw [decP_append, decP_ups, decP_frep (fun o => decP_lad (q+1) o) m q]
      have hv : ∀ fuel', (q+2) * m + 1 ≤ fuel' →
          Trans.Pair.oLAux fuel' (q+1) (([0,1] : BMS.Col) :: frep (lad (q+1)) (q+1) 0 m)
            = VV q m := fun fuel' hf' => valV3 m q fuel' hf'
      rw [oLAux_cons', hb]
      show zsF g (q+1) (zsF g (q+1) zero [[0,1]]) (([0,0] : BMS.Col)
        :: (ups 1 (q+1) ++ frep (lad (q+1)) (q+1) (q+1) m)) = VV q (m+1)
      rw [zsF_step, phiStep_start]
      show plus (phi (ofNat (q+1)) (ofNat 0)) (omegaNF (Trans.Pair.oLAux g 1
        (Trans.Pair.decP (ups 1 (q+1) ++ frep (lad (q+1)) (q+1) (q+1) m)))) = VV q (m+1)
      rw [hd, oLAux_chainV (fun o => decP_lad (q+1) o) (fun o ho => r0_lad (q+1) o ho) hv
        q 1 g (by omega) (by omega)]
      rfl


theorem len_frep_gen {B : Nat → Matrix} {w : Nat} (hB : ∀ o, (B o).length = w) :
    ∀ (m step o : Nat), (frep B step o m).length = w * m
  | 0, _, _ => by
    show (([] : Matrix)).length = w * 0
    simp
  | m + 1, step, o => by
    show ((B o) ++ frep B step (o+step) m).length = w * (m+1)
    rw [List.length_append, hB o, len_frep_gen hB m step (o+step), Nat.mul_succ]
    omega

/-- The value of the n-th F3 expansion, in terms of the accumulator `VV`. -/
theorem valE3 (n q fuel k : Nat) (hf : (q+2) * (n+1) + 1 ≤ fuel) :
    Trans.Pair.oLAux fuel k (frep (lad (q+1)) (q+1) 0 (n+1))
      = omegaNF (chainP 1 q (VV q n)) := by
  have hmul : (q+2) * (n+1) = (q+2) * n + q + 2 := by rw [Nat.mul_succ]; omega
  cases fuel with
  | zero => omega
  | succ g =>
    have htB : ∀ c ∈ (ups 1 (q+1) ++ frep (lad (q+1)) (q+1) (q+1) n),
        Trans.Pair.r0 c ≠ 0 := by
      intro c hc
      rcases List.mem_append.mp hc with h1 | h1
      · exact r0_ups (q+1) 1 (by omega) c h1
      · exact r0_frep (fun o ho => r0_lad (q+1) o ho) n (q+1) (by omega) c h1
    have hd : Trans.Pair.decP (ups 1 (q+1) ++ frep (lad (q+1)) (q+1) (q+1) n)
        = ups 0 (q+1) ++ frep (lad (q+1)) (q+1) q n := by
      rw [decP_append, decP_ups, decP_frep (fun o => decP_lad (q+1) o) n q]
    have hv : ∀ fuel', (q+2) * n + 1 ≤ fuel' →
        Trans.Pair.oLAux fuel' (q+1) (([0,1] : BMS.Col) :: frep (lad (q+1)) (q+1) 0 n)
          = VV q n := fun fuel' hf' => valV3 n q fuel' hf'
    rw [frep_lad_cons' (q+1) q n, oLAux_single g k [0,0] _ htB]
    show plus zero (omegaNF (Trans.Pair.oLAux g 1
      (Trans.Pair.decP (ups 1 (q+1) ++ frep (lad (q+1)) (q+1) (q+1) n)))) = _
    rw [hd, oLAux_chainV (fun o => decP_lad (q+1) o) (fun o ho => r0_lad (q+1) o ho) hv
      q 1 g (by omega) (by omega), plus_zero_left (isAP_omegaNF _)]

/-- The F3 expansion in `o?` form (still stated through the accumulator `VV`). -/
theorem o?_expand_M3 (q n : Nat) :
    o? (BMS.expand (M3 q) n) = some (omegaNF (chainP 1 q (VV q n))) := by
  have hE : BMS.expand (M3 q) n = frep (lad (q+1)) (q+1) 0 (n+1) := by
    show (BMS.expand? (M3 q) n).getD [] = _
    rw [expand_M3]; rfl
  have honly : onlyRow0 (frep (lad (q+1)) (q+1) 0 (n+1)) = false := by
    rw [frep_lad_cons' (q+1) q n]
    show onlyRow0 (([0,0] : BMS.Col)
      :: (ups 1 (q+1) ++ frep (lad (q+1)) (q+1) (q+1) n)) = false
    rw [onlyRow0_cons, onlyRow0_append, onlyRow0_ups q 1]
    rfl
  rw [hE, o?_pair honly (inFrag_frep (fun o => inFrag_lad (q+1) o) (n+1) 0),
    len_frep_gen (fun o => len_lad (q+1) o) (n+1) (q+1) 0,
    valE3 n q _ 1 (by rw [show q + 1 + 1 = q + 2 from by omega]; omega)]

-- the closed forms of §6 agree with computation on small instances
#guard (List.range 3).all fun q => (List.range 4).all fun n =>
  Trans.o? (BMS.expand (M3 q) n) == some (omegaNF (chainP 1 q (VV q n)))
#guard (List.range 4).all fun q =>
  Trans.o? (M3 q) == some (phi (ofNat (q+1)) one)
#guard M3 0 == Rows.ProofsB.R3.m0 && M3 1 == Rows.ProofsB.R7.m0



/-! ## §7 The family F3 — the term side: the tower, its base, the fundamental
       sequence, and the package

The two towers of F3.  Both sides climb `φ_q`, but over different bases:

  expansions            `bse  q = φ̄(q, xbase q)`,  `xbase q = φ̄(a,0)·2` (q = 0)
                                                             `ω^(φ̄(a,0)·2)` (q ≥ 1)
  fundamental sequence  `sbse q = φ̄(q, φ̄(a,0))`

and `bse q > sbse q`, which is why no index shift can make the two sequences equal
and why the statement has to be the 4-part package. -/


def xbase (q : Nat) : Term :=
  match q with
  | 0 => add (zt 0) (zt 0)
  | q' + 1 => phi zero (add (zt (q'+1)) (zt (q'+1)))

def bse (q : Nat) : Term := phi (ofNat q) (xbase q)
def sbse (q : Nat) : Term := phi (ofNat q) (zt q)

def twB (q : Nat) (b : Term) : Nat → Term
  | 0 => b
  | j + 1 => phi (ofNat q) (twB q b j)

def twr (q j : Nat) : Term := twB q (bse q) j

theorem twr_zero (q : Nat) : twr q 0 = bse q := rfl
theorem twr_succ (q j : Nat) : twr q (j+1) = phi (ofNat q) (twr q j) := rfl

theorem twB_shape (q : Nat) {b y : Term} (hb : b = phi (ofNat q) y) :
    ∀ j, ∃ z, twB q b j = phi (ofNat q) z
  | 0 => ⟨y, hb⟩
  | j + 1 => ⟨twB q b j, rfl⟩

theorem twr_shape (q j : Nat) : ∃ z, twr q j = phi (ofNat q) z := twB_shape q rfl j

theorem sbse_shape (q j : Nat) : ∃ z, twB q (sbse q) j = phi (ofNat q) z := twB_shape q rfl j

theorem isAP_twr (q j : Nat) : (twr q j).isAP = true := by cases j <;> rfl

theorem twB_phi (q : Nat) (b : Term) : ∀ j, twB q (phi (ofNat q) b) j = twB q b (j+1)
  | 0 => rfl
  | j + 1 => by
    show phi (ofNat q) (twB q (phi (ofNat q) b) j) = phi (ofNat q) (twB q b (j+1))
    rw [twB_phi q b j]

theorem deg_twB (q : Nat) (b : Term) : ∀ j, j ≤ (twB q b j).deg
  | 0 => by show (0:Nat) ≤ b.deg; omega
  | j + 1 => by
    show j + 1 ≤ 1 + (ofNat q).deg + (twB q b j).deg
    have := deg_twB q b j
    omega

theorem deg_twr (q j : Nat) : j ≤ (twr q j).deg := deg_twB q (bse q) j

/-! ### Small term facts -/

theorem zero_bne_ofNat (q : Nat) : ((zero : Term) == ofNat (q+1)) = false := by
  simpa using (ofNat_ne_zero q).symm

theorem zt_bne_one (q : Nat) : ((zt q : Term) == one) = false := by
  show (phi (ofNat (q+1)) zero == phi zero zero) = false
  simp [ofNat_ne_zero q]

theorem plus_self {a : Term} (ha : a.isAP = true) : plus a a = add a a := by
  unfold plus
  rw [toList_of_isAP ha]
  show ofList ((match le a a with | true => [a] | false => []) ++ [a]) = add a a
  rw [show le a a = true from by simp [le]]
  rfl

theorem ltF_M_add_phi (f : Nat) (a b c : Term) : ltF f M (add (phi a b) c) = false := by
  cases f with
  | zero => rfl
  | succ g =>
    show ((M : Term) == phi a b || ltF g M (phi a b)) = false
    rw [Evidence.StageA.ltF_M_phi]
    rfl

theorem splitFin_add_pair {x y : Term} (hy : y.isAP = true) (h1 : (y == one) = false) :
    splitFin (add x y) = (add x y, 0) := by
  have hl : toList (add x y) = [x, y] := by
    show x :: toList y = [x, y]
    rw [toList_of_isAP hy]
  unfold splitFin
  simp only [hl]
  simp [h1, ofList]

theorem phiNF_add_pair {a x y : Term} (ha : a.isSC = false) (hy : y.isAP = true)
    (h1 : (y == one) = false) : phiNF a (add x y) = phi a (add x y) := by
  unfold phiNF
  simp only [isSC, Bool.false_and, Bool.false_eq_true, if_false]
  show phiNFsucc a (add x y) = phi a (add x y)
  unfold phiNFsucc
  rw [splitFin_add_pair hy h1]
  show phiNFdefault a (add x y) = phi a (add x y)
  exact phiNFdefault_phi ha

theorem omegaNF_add_zt (q : Nat) :
    omegaNF (add (zt q) (zt q)) = phi zero (add (zt q) (zt q)) := by
  rw [omegaNF_of_le_M (show lt M (add (zt q) (zt q)) = false from
      ltF_M_add_phi _ (ofNat (q+1)) zero (zt q))]
  exact phiNF_add_pair isSC_zero rfl (zt_bne_one q)

/-! ### (A)–(D): the accumulator steps -/

/-- **(A)** the chain collapses onto `φ̄(a,0)` and `ω^` leaves it alone. -/
theorem step_zt (q : Nat) : omegaNF (chainP 1 q (zt q)) = zt q := by
  rw [show chainP 1 q (zt q) = zt q from
    chainP_collapse q 1 (q+1) zero (by omega)]
  exact omegaNF_phi_ne_zero (ofNat_ne_zero q)

/-- **(B)** the first accumulator value is `φ̄(a,0)·2`. -/
theorem VV_one (q : Nat) : VV q 1 = add (zt q) (zt q) := by
  show plus (zt q) (omegaNF (chainP 1 q (VV q 0))) = add (zt q) (zt q)
  rw [show VV q 0 = zt q from rfl, step_zt q, plus_self (show (zt q).isAP = true from rfl)]

/-- **(C)** the next accumulator value is the base of the tower.
    The case split on `q` is forced: at `q = 0` the chain is empty and the outer
    `ω^` supplies the `φ̄(0,·)` layer; for `q ≥ 1` the innermost `phiStep` (level `q`)
    wraps and the outer `ω^` is the identity. -/
theorem step_add_zt (q : Nat) : omegaNF (chainP 1 q (add (zt q) (zt q))) = bse q := by
  cases q with
  | zero =>
    show omegaNF (add (zt 0) (zt 0)) = phi (ofNat 0) (xbase 0)
    rw [omegaNF_add_zt 0]
    rfl
  | succ q' =>
    have hstep : chainP (1+q') 1 (add (zt (q'+1)) (zt (q'+1))) = bse (q'+1) := by
      show Trans.Pair.phiStep (ofNat (1+q')) zero (add (zt (q'+1)) (zt (q'+1))) = _
      rw [phiStep_zero, show ((add (zt (q'+1)) (zt (q'+1)) : Term) == zero) = false from rfl]
      simp only [Bool.false_eq_true, if_false]
      rw [omegaNF_add_zt (q'+1), show 1 + q' = q' + 1 from by omega]
      exact phiNF_phi_gen (isSC_ofNat (q'+1)) (lt_lt_zero (ofNat (q'+1)))
    rw [chainP_add q' 1 1 (add (zt (q'+1)) (zt (q'+1))), hstep,
      show bse (q'+1) = phi (ofNat (q'+1)) (xbase (q'+1)) from rfl,
      chainP_collapse q' 1 (q'+1) (xbase (q'+1)) (by omega)]
    exact omegaNF_phi_ne_zero (ofNat_ne_zero q')

/-- **(D)** one more accumulator step climbs one storey of the tower. -/
theorem step_twr (q j : Nat) : omegaNF (chainP 1 q (twr q j)) = twr q (j+1) := by
  cases q with
  | zero =>
    obtain ⟨y, hy⟩ := twr_shape 0 j
    show omegaNF (twr 0 j) = phi (ofNat 0) (twr 0 j)
    rw [hy]
    show omegaNF (phi zero y) = phi zero (phi zero y)
    rw [omegaNF_phi, phiNF_phi_arg isSC_zero]
  | succ q' =>
    obtain ⟨y, hy⟩ := twr_shape (q'+1) j
    have hstep : chainP (1+q') 1 (twr (q'+1) j) = twr (q'+1) (j+1) := by
      show Trans.Pair.phiStep (ofNat (1+q')) zero (twr (q'+1) j) = _
      rw [phiStep_zero, show ((twr (q'+1) j : Term) == zero) = false from by rw [hy]; rfl]
      simp only [Bool.false_eq_true, if_false]
      rw [hy, omegaNF_phi_ne_zero (ofNat_ne_zero q'),
        show 1 + q' = q' + 1 from by omega, phiNF_phi_arg (isSC_ofNat (q'+1)), ← hy]
      rfl
    rw [chainP_add q' 1 1 (twr (q'+1) j), hstep, twr_succ,
      chainP_collapse q' 1 (q'+1) (twr (q'+1) j) (by omega)]
    exact omegaNF_phi_ne_zero (ofNat_ne_zero q')

/-! ### (E): the tower never falls back below `φ̄(a,0)`, so the sum drops -/

/-- The step of clause 2.3.13(iii) against `φ̄(a,0)`: a `φ̄` whose first argument is
    not `a` and does not exceed `a` cannot be `< φ̄(a,0)`. -/
theorem ltF_phi_not_zt {q f : Nat} {a b : Term} (hac : (a == ofNat (q+1)) = false)
    (h1 : ltF f b (zt q) = false) : ltF (f+1) (phi a b) (zt q) = false := by
  have hac' : a ≠ ofNat (q+1) := by simpa using hac
  have hne : ((phi a b : Term) == zt q) = false := by
    show ((phi a b : Term) == phi (ofNat (q+1)) zero) = false
    simp [hac']
  show (if ((phi a b : Term) == zt q) = true then false else _) = false
  rw [hne]
  simp only [Bool.false_eq_true, if_false]
  show (if (a == ofNat (q+1)) = true then ltF f b zero
        else if ltF f a (ofNat (q+1)) = true then ltF f b (phi (ofNat (q+1)) zero)
        else (((phi a b : Term) == zero) || ltF f (phi a b) zero)) = false
  rw [hac]
  simp only [Bool.false_eq_true, if_false]
  cases hlt : ltF f a (ofNat (q+1)) with
  | true => simpa using h1
  | false =>
    simp only [Bool.false_eq_true, if_false,
      show (((phi a b : Term)) == zero) = false from rfl, Bool.false_or]
    exact ltF_lt_zero f _

theorem ltF_add_zt_not (q : Nat) : ∀ f, ltF f (add (zt q) (zt q)) (zt q) = false
  | 0 => rfl
  | f + 1 => by
    show (if ((add (zt q) (zt q) : Term) == zt q) = true then false
          else ltF f (zt q) (zt q)) = false
    simp only [show ((add (zt q) (zt q) : Term) == zt q) = false from rfl,
      Bool.false_eq_true, if_false]
    exact ltF_irrefl f (zt q)

theorem ltF_xbase_not (q : Nat) : ∀ f, ltF f (xbase q) (zt q) = false
  | 0 => rfl
  | f + 1 => by
    cases q with
    | zero => exact ltF_add_zt_not 0 (f+1)
    | succ q' =>
      show ltF (f+1) (phi zero (add (zt (q'+1)) (zt (q'+1)))) (zt (q'+1)) = false
      exact ltF_phi_not_zt (zero_bne_ofNat (q'+1)) (ltF_add_zt_not (q'+1) f)

theorem ltF_twr_not (q : Nat) : ∀ (f j : Nat), ltF f (twr q j) (zt q) = false
  | 0, _ => rfl
  | f + 1, 0 => by
    show ltF (f+1) (phi (ofNat q) (xbase q)) (zt q) = false
    exact ltF_phi_not_zt (ofNat_bne (by omega)) (ltF_xbase_not q f)
  | f + 1, j + 1 => by
    show ltF (f+1) (phi (ofNat q) (twr q j)) (zt q) = false
    exact ltF_phi_not_zt (ofNat_bne (by omega)) (ltF_twr_not q f j)

theorem twr_bne_zt (q j : Nat) : ((twr q j : Term) == zt q) = false := by
  obtain ⟨y, hy⟩ := twr_shape q j
  rw [hy]
  show ((phi (ofNat q) y : Term) == phi (ofNat (q+1)) zero) = false
  have hne : (ofNat q : Term) ≠ ofNat (q+1) := by
    intro h; have := ofNat_inj h; omega
  simp [hne]

/-- **(E)** -/
theorem le_twr_zt (q j : Nat) : le (twr q j) (zt q) = false := by
  show (((twr q j : Term) == zt q) || lt (twr q j) (zt q)) = false
  rw [twr_bne_zt q j]
  simp only [Bool.false_or]
  exact ltF_twr_not q _ j

theorem VV_succ2 : ∀ (q m : Nat), VV q (m+2) = twr q m
  | q, 0 => by
    show plus (zt q) (omegaNF (chainP 1 q (VV q 1))) = twr q 0
    rw [VV_one q, step_add_zt q]
    exact plus_drop rfl (isAP_twr q 0) (le_twr_zt q 0)
  | q, m + 1 => by
    show plus (zt q) (omegaNF (chainP 1 q (VV q (m+2)))) = twr q (m+1)
    rw [VV_succ2 q m, step_twr q m]
    exact plus_drop rfl (isAP_twr q (m+1)) (le_twr_zt q (m+1))

/-! ### The closed form of the value of the n-th expansion -/

/-- `oval3 q 0 = φ̄(a,0)`; afterwards the `φ_q`-tower over `bse q`. -/
def oval3 (q : Nat) : Nat → Term
  | 0 => zt q
  | n + 1 => twr q n

theorem oval3_eq : ∀ (q n : Nat), omegaNF (chainP 1 q (VV q n)) = oval3 q n
  | q, 0 => step_zt q
  | q, 1 => by rw [VV_one q]; exact step_add_zt q
  | q, m + 2 => by rw [VV_succ2 q m]; exact step_twr q m

/-- **E3, part (a)** for the F3 family. -/
theorem e3_val3 (q n : Nat) : o? (BMS.expand (M3 q) n) = some (oval3 q n) := by
  rw [o?_expand_M3 q n, oval3_eq q n]

/-! ### (F): the fundamental sequence of `φ̄(a,1)` -/

def t3 (q : Nat) : Term := phi (ofNat (q+1)) one

theorem fs_raw3 (q k : Nat) : fsN (t3 q) k = iterPhiAt (ofNat q) (plus (zt q) one) k := by
  show fsN (phi (ofNat (q+1)) one) k = _
  rw [fsN]
  simp only [phiShifted_of_splitFin_zero (isSC_ofNat (q+1))
      (show (splitFin (one : Term)).1 = zero from rfl), Bool.false_or,
    show (kindT (one : Term) == KindT.isSucc) = true from rfl, if_true]
  simp only [Bool.false_eq_true, if_false, show predT (one : Term) = zero from rfl,
    kindT_ofNat_succ q, predT_ofNat_succ q, phiNF_zero_arg (isSC_ofNat (q+1))]
  rfl

theorem ltF_one_zt (q : Nat) : ∀ f, 2 ≤ f → ltF f one (zt q) = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g =>
    show ltF (g+1) (phi zero zero) (phi (ofNat (q+1)) zero) = true
    exact ltF_phi_fst (zero_bne_ofNat q)
      (ltF_zero (by omega) (ofNat_ne_zero q))
      (ltF_zero (by omega) (by intro hc; exact Term.noConfusion hc))

theorem le_one_zt (q : Nat) : le one (zt q) = true := by
  show (((one : Term) == zt q) || lt one (zt q)) = true
  rw [show lt one (zt q) = true from
    lt_of_ltF (N := 2) (fun f hf => ltF_one_zt q f hf) (by
      show 2 ≤ 2 * ((one : Term).deg + (zt q).deg) + 8
      omega)]
  simp

theorem plus_zt_one (q : Nat) : plus (zt q) one = add (zt q) one := by
  unfold plus
  show ofList ((match le one (zt q) with | true => [zt q] | false => []) ++ [one])
      = add (zt q) one
  rw [le_one_zt q]
  rfl

theorem splitFin_add_one {x : Term} (h : (x == one) = false) : splitFin (add x one) = (x, 1) := by
  have hl : toList (add x one) = [x, one] := rfl
  unfold splitFin
  simp only [hl]
  simp [h, ofList]

/-- The one step with no analogue elsewhere in the file: the "down" branch of
    `phiNFsucc`.  `φ_q(φ̄(a,0) + 1) = φ̄(q, φ̄(a,0))` because `φ̄(a,0)` is a
    `φ_q`-fixed-point shape (`q < a = q+1`). -/
theorem phiNF_zt_one (q : Nat) : phiNF (ofNat q) (plus (zt q) one) = sbse q := by
  rw [plus_zt_one q]
  unfold phiNF
  simp only [isSC, Bool.false_and, Bool.false_eq_true, if_false]
  show phiNFsucc (ofNat q) (add (zt q) one) = sbse q
  unfold phiNFsucc
  rw [splitFin_add_one (zt_bne_one q)]
  show (match (phi (ofNat (q+1)) zero : Term) with
        | phi d _ => if lt (ofNat q) d = true then phi (ofNat q) (plus (zt q) (ofNat (1-1)))
                     else phiNFdefault (ofNat q) (add (zt q) one)
        | _ => if ((zt q).isSC && lt (ofNat q) (zt q)) = true
               then phi (ofNat q) (plus (zt q) (ofNat (1-1)))
               else phiNFdefault (ofNat q) (add (zt q) one)) = sbse q
  simp only [lt_ofNat_mono (show q < q + 1 from by omega), if_true]
  rfl

/-- **(F)** the fundamental sequence of `φ̄(a,1)` is the `φ_q`-tower over `φ̄(q,φ̄(a,0))`. -/
theorem fs_t3 (q : Nat) : ∀ k, fsN (t3 q) (k+1) = twB q (sbse q) k
  | 0 => by
    rw [fs_raw3 q 1]
    show phiNF (ofNat q) (plus (zt q) one) = twB q (sbse q) 0
    exact phiNF_zt_one q
  | k + 1 => by
    obtain ⟨y, hy⟩ := sbse_shape q k
    rw [fs_raw3 q (k+2)]
    show phiNF (ofNat q) (iterPhiAt (ofNat q) (plus (zt q) one) (k+1)) = twB q (sbse q) (k+1)
    rw [← fs_raw3 q (k+1), fs_t3 q k, hy]
    show phiNF (ofNat q) (phi (ofNat q) y) = phi (ofNat q) (twB q (sbse q) k)
    rw [phiNF_phi_arg (isSC_ofNat q), ← hy]

/-! ### (G): the order facts -/

/-- The finite terms are linearly ordered by their index: no `ofNat i` is below a
    smaller (or equal) one.  Needed for clause 2.3.13(iii). -/
theorem ltF_ofNat_not : ∀ (f i j : Nat), j ≤ i → ltF f (ofNat i) (ofNat j) = false
  | 0, _, _, _ => rfl
  | f + 1, i, j, h => by
    match i, j, h with
    | i, 0, _ => exact ltF_lt_zero (f+1) (ofNat i)
    | 0, _+1, h => exact absurd h (by omega)
    | 1, 1, _ => exact ltF_irrefl (f+1) (ofNat 1)
    | 1, _+2, h => exact absurd h (by omega)
    | i'+2, 1, _ =>
      rw [ofNat_shape i', ofNat_one]
      show (if ((add one (ofNat (i'+1)) : Term) == one) = true then false
            else ltF f one one) = false
      simp only [show ((add one (ofNat (i'+1)) : Term) == one) = false from rfl,
        Bool.false_eq_true, if_false]
      exact ltF_irrefl f one
    | i'+2, j'+2, h =>
      rw [ofNat_shape i', ofNat_shape j']
      cases hb : ((add one (ofNat (i'+1)) : Term) == add one (ofNat (j'+1))) with
      | true =>
        show (if ((add one (ofNat (i'+1)) : Term) == add one (ofNat (j'+1))) = true
              then false else _) = false
        rw [hb]
        rfl
      | false =>
        show (if ((add one (ofNat (i'+1)) : Term) == add one (ofNat (j'+1))) = true
              then false
              else if ((one : Term) == one) = true then ltF f (ofNat (i'+1)) (ofNat (j'+1))
                   else ltF f one one) = false
        rw [hb]
        simp only [Bool.false_eq_true, if_false, beq_self_eq_true, if_true]
        exact ltF_ofNat_not f (i'+1) (j'+1) (by omega)

theorem ltF_twB_mono {q : Nat} {x y : Term} {N : Nat} (h : ∀ f, N ≤ f → ltF f x y = true) :
    ∀ (j f : Nat), N + j ≤ f → ltF f (twB q x j) (twB q y j) = true
  | 0, f, hf => h f (by omega)
  | j + 1, f, hf => by
    cases f with
    | zero => omega
    | succ g => exact ltF_phi_same (ltF_twB_mono h j g (by omega))

/-! #### The expansion values are below `φ̄(a,1)` -/

theorem ltF_zt_t3 (q : Nat) : ∀ f, 2 ≤ f → ltF f (zt q) (t3 q) = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g =>
    exact ltF_phi_same (ltF_zero (by omega) (by intro hc; exact Term.noConfusion hc))

theorem ltF_add_t3 (q : Nat) : ∀ f, 3 ≤ f → ltF f (add (zt q) (zt q)) (t3 q) = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g =>
    show (if ((add (zt q) (zt q) : Term) == t3 q) = true then false
          else ltF g (zt q) (t3 q)) = true
    simp only [show ((add (zt q) (zt q) : Term) == t3 q) = false from rfl,
      Bool.false_eq_true, if_false]
    exact ltF_zt_t3 q g (by omega)

theorem ltF_xbase_t3 (q : Nat) : ∀ f, 4 ≤ f → ltF f (xbase q) (t3 q) = true := by
  intro f hf
  cases q with
  | zero => exact ltF_add_t3 0 f (by omega)
  | succ q' =>
    cases f with
    | zero => omega
    | succ g =>
      show ltF (g+1) (phi zero (add (zt (q'+1)) (zt (q'+1)))) (phi (ofNat (q'+2)) one) = true
      exact ltF_phi_fst (zero_bne_ofNat (q'+1)) (ltF_zero (by omega) (ofNat_ne_zero (q'+1)))
        (ltF_add_t3 (q'+1) g (by omega))

theorem ltF_twr_t3 (q : Nat) : ∀ (j f : Nat), q + j + 5 ≤ f → ltF f (twr q j) (t3 q) = true
  | 0, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      show ltF (g+1) (phi (ofNat q) (xbase q)) (phi (ofNat (q+1)) one) = true
      exact ltF_phi_fst (ofNat_bne (by omega))
        (ltF_ofNat_mono q (q+1) g (by omega) (by omega)) (ltF_xbase_t3 q g (by omega))
  | j + 1, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      show ltF (g+1) (phi (ofNat q) (twr q j)) (phi (ofNat (q+1)) one) = true
      exact ltF_phi_fst (ofNat_bne (by omega))
        (ltF_ofNat_mono q (q+1) g (by omega) (by omega)) (ltF_twr_t3 q j g (by omega))

/-- **E3, part (b)**: every expansion value is `< φ̄(a,1)`. -/
theorem e3_lt3 (q : Nat) : ∀ n, lt (oval3 q n) (t3 q) = true
  | 0 => by
    refine lt_of_ltF (N := 2) (fun f hf => ltF_zt_t3 q f hf) ?_
    show 2 ≤ 2 * ((zt q).deg + (1 + (ofNat (q+1)).deg + (one : Term).deg)) + 8
    omega
  | n + 1 => by
    show lt (twr q n) (t3 q) = true
    refine lt_of_ltF (N := q + n + 5) (fun f hf => ltF_twr_t3 q n f hf) ?_
    have h1 := deg_twr q n
    have h2 := deg_ofNat (q+1)
    show q + n + 5 ≤ 2 * ((twr q n).deg + (1 + (ofNat (q+1)).deg + (one : Term).deg)) + 8
    omega

/-! #### The expansion tower against the fundamental-sequence tower -/

theorem ltF_zt_sbse (q : Nat) : ∀ f, 1 ≤ f → ltF f (zt q) (sbse q) = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g =>
    show ltF (g+1) (phi (ofNat (q+1)) zero) (phi (ofNat q) (zt q)) = true
    exact ltF_phi_eq (ofNat_bne (by omega)) (ltF_ofNat_not g (q+1) q (by omega))
      (show ((phi (ofNat (q+1)) zero : Term) == zt q) = true from beq_self_eq_true _)

theorem ltF_add_sbse (q : Nat) : ∀ f, 2 ≤ f → ltF f (add (zt q) (zt q)) (sbse q) = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g =>
    show (if ((add (zt q) (zt q) : Term) == sbse q) = true then false
          else ltF g (zt q) (sbse q)) = true
    simp only [show ((add (zt q) (zt q) : Term) == sbse q) = false from rfl,
      Bool.false_eq_true, if_false]
    exact ltF_zt_sbse q g (by omega)

theorem ltF_xbase_sbse (q : Nat) : ∀ f, 3 ≤ f → ltF f (xbase q) (sbse q) = true := by
  intro f hf
  cases q with
  | zero => exact ltF_add_sbse 0 f (by omega)
  | succ q' =>
    cases f with
    | zero => omega
    | succ g =>
      show ltF (g+1) (phi zero (add (zt (q'+1)) (zt (q'+1))))
        (phi (ofNat (q'+1)) (zt (q'+1))) = true
      exact ltF_phi_fst (zero_bne_ofNat q') (ltF_zero (by omega) (ofNat_ne_zero q'))
        (ltF_add_sbse (q'+1) g (by omega))

theorem ltF_bse_phisbse (q : Nat) :
    ∀ f, 4 ≤ f → ltF f (bse q) (phi (ofNat q) (sbse q)) = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g => exact ltF_phi_same (ltF_xbase_sbse q g (by omega))

theorem ltF_zt_add_zt (q f : Nat) : ltF (f+1) (zt q) (add (zt q) (zt q)) = true := by
  show (if ((zt q : Term) == add (zt q) (zt q)) = true then false
        else (((zt q : Term) == zt q) || ltF f (zt q) (zt q))) = true
  simp only [show ((zt q : Term) == add (zt q) (zt q)) = false from rfl,
    Bool.false_eq_true, if_false]
  simp

theorem ltF_zt_xbase (q : Nat) : ∀ f, 2 ≤ f → ltF f (zt q) (xbase q) = true := by
  intro f hf
  cases q with
  | zero =>
    cases f with
    | zero => omega
    | succ g => exact ltF_zt_add_zt 0 g
  | succ q' =>
    cases f with
    | zero => omega
    | succ g =>
      show ltF (g+1) (phi (ofNat (q'+2)) zero)
        (phi zero (add (zt (q'+1)) (zt (q'+1)))) = true
      refine ltF_phi_snd (show ((ofNat (q'+2) : Term) == zero) = false from by
          simpa using ofNat_ne_zero (q'+1))
        (ltF_lt_zero g (ofNat (q'+2))) ?_
      cases g with
      | zero => omega
      | succ h => exact ltF_zt_add_zt (q'+1) h

theorem ltF_sbse_bse (q : Nat) : ∀ f, 3 ≤ f → ltF f (sbse q) (bse q) = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g => exact ltF_phi_same (ltF_zt_xbase q g (by omega))

/-- **E3, part (c)** with witness `k := n+1`: the fundamental sequence overtakes. -/
theorem e3_over3 (q : Nat) : ∀ n, lt (oval3 q n) (fsN (t3 q) (n+1)) = true
  | 0 => by
    rw [fs_t3 q 0]
    show lt (zt q) (sbse q) = true
    refine lt_of_ltF (N := 1) (fun f hf => ltF_zt_sbse q f hf) ?_
    show 1 ≤ 2 * ((zt q).deg + (sbse q).deg) + 8
    omega
  | n + 1 => by
    rw [fs_t3 q (n+1), ← twB_phi q (sbse q) n]
    show lt (twB q (bse q) n) (twB q (phi (ofNat q) (sbse q)) n) = true
    refine lt_of_ltF (N := 4 + n)
      (fun f hf => ltF_twB_mono (fun g hg => ltF_bse_phisbse q g hg) n f hf) ?_
    have h1 := deg_twB q (bse q) n
    show 4 + n ≤ 2 * ((twB q (bse q) n).deg + (twB q (phi (ofNat q) (sbse q)) n).deg) + 8
    omega

/-- **E3, part (d)** with witness `n := k+1`: the expansions overtake back. -/
theorem e3_under3 (q k : Nat) : lt (fsN (t3 q) (k+1)) (oval3 q (k+1)) = true := by
  rw [fs_t3 q k]
  show lt (twB q (sbse q) k) (twB q (bse q) k) = true
  refine lt_of_ltF (N := 3 + k)
    (fun f hf => ltF_twB_mono (fun g hg => ltF_sbse_bse q g hg) k f hf) ?_
  have h1 := deg_twB q (sbse q) k
  show 3 + k ≤ 2 * ((twB q (sbse q) k).deg + (twB q (bse q) k).deg) + 8
  omega

/-- **E3 for the F3 family**, for every `a = q+1 ≥ 1`:
    `(0,0)(1,1)…(a,1)(a,1) = φ̄(a,1)`, in the 4-part mutual-cofinality form with
    witnesses `kw n = n+1`, `nw k = k+1`. -/
theorem e3_F3family (q : Nat) :
    (∀ n, o? (BMS.expand (M3 q) n) = some (oval3 q n))
    ∧ (∀ n, lt (oval3 q n) (t3 q) = true)
    ∧ (∀ n, lt (oval3 q n) (fsN (t3 q) (n + 1)) = true)
    ∧ (∀ k, lt (fsN (t3 q) (k + 1)) (oval3 q (k + 1)) = true) :=
  ⟨e3_val3 q, e3_lt3 q, e3_over3 q, e3_under3 q⟩

/-- The same package with the term written out. -/
example (q : Nat) :
    (∀ n, o? (BMS.expand (M3 q) n) = some (oval3 q n))
    ∧ (∀ n, lt (oval3 q n) (phi (ofNat (q+1)) one) = true)
    ∧ (∀ n, lt (oval3 q n) (fsN (phi (ofNat (q+1)) one) (n + 1)) = true)
    ∧ (∀ k, lt (fsN (phi (ofNat (q+1)) one) (k + 1)) (oval3 q (k + 1)) = true) :=
  e3_F3family q

/-! ### The two table rows are instances -/

theorem m3_zero : M3 0 = Rows.ProofsB.R3.m0 := rfl
theorem m3_one : M3 1 = Rows.ProofsB.R7.m0 := rfl
theorem t3_zero : t3 0 = Rows.ProofsB.R3.t0 := rfl
theorem t3_one : t3 1 = Rows.ProofsB.R7.t0 := rfl
theorem bse_zero : bse 0 = Rows.ProofsB.R3.P0 := rfl
theorem bse_one : bse 1 = Rows.ProofsB.R7.R0 := rfl
theorem sbse_zero : sbse 0 = Rows.ProofsB.R3.Q0 := rfl
theorem sbse_one : sbse 1 = Rows.ProofsB.R7.S0 := rfl

theorem twB_zero_tow (b : Term) : ∀ j, twB 0 b j = Rows.ProofsB.tow b j
  | 0 => rfl
  | j + 1 => by
    show phi (ofNat 0) (twB 0 b j) = phi zero (Rows.ProofsB.tow b j)
    rw [twB_zero_tow b j]
    rfl

theorem twB_one_etow (b : Term) : ∀ j, twB 1 b j = Rows.ProofsB.R7.etow b j
  | 0 => rfl
  | j + 1 => by
    show phi (ofNat 1) (twB 1 b j) = phi one (Rows.ProofsB.R7.etow b j)
    rw [twB_one_etow b j]
    rfl

/-- `q = 0` is exactly row R3 (`ε₁`), value function included. -/
theorem oval3_zero : ∀ n, oval3 0 n = Rows.ProofsB.R3.oval n
  | 0 => rfl
  | n + 1 => twB_zero_tow (bse 0) n

/-- `q = 1` is exactly row R7 (`ζ₁`), value function included. -/
theorem oval3_one : ∀ n, oval3 1 n = Rows.ProofsB.R7.oval n
  | 0 => rfl
  | n + 1 => twB_one_etow (bse 1) n

example (n : Nat) : o? (BMS.expand Rows.ProofsB.R3.m0 n) = some (Rows.ProofsB.R3.oval n) := by
  rw [← oval3_zero n]; exact e3_val3 0 n
example (n : Nat) : o? (BMS.expand Rows.ProofsB.R7.m0 n) = some (Rows.ProofsB.R7.oval n) := by
  rw [← oval3_one n]; exact e3_val3 1 n

/-- The family goes strictly beyond the table: `a = 3`, i.e.
    `(0,0)(1,1)(2,1)(3,1)(3,1) = φ̄(3,1)`. -/
example (n : Nat) : o? (BMS.expand [[0,0],[1,1],[2,1],[3,1],[3,1]] n) = some (oval3 2 n) :=
  e3_val3 2 n
example (n : Nat) : lt (oval3 2 n) (phi (ofNat 3) one) = true := e3_lt3 2 n
example (n : Nat) : lt (oval3 2 n) (fsN (phi (ofNat 3) one) (n+1)) = true := e3_over3 2 n
example (k : Nat) : lt (fsN (phi (ofNat 3) one) (k+1)) (oval3 2 (k+1)) = true := e3_under3 2 k

-- the closed forms of §7 agree with computation on small instances
#guard (List.range 4).all fun q => (List.range 5).all fun n =>
  Trans.o? (BMS.expand (M3 q) n) == some (oval3 q n)
#guard (List.range 4).all fun q => Trans.o? (M3 q) == some (t3 q)
#guard (List.range 4).all fun q => (List.range 5).all fun k =>
  fsN (t3 q) (k+1) == twB q (sbse q) k
#guard (List.range 4).all fun q => (List.range 5).all fun n =>
  lt (oval3 q n) (t3 q) && lt (oval3 q n) (fsN (t3 q) (n+1))
#guard (List.range 4).all fun q => (List.range 5).all fun k =>
  lt (fsN (t3 q) (k+1)) (oval3 q (k+1))
#guard (List.range 4).all fun q => (List.range 4).all fun m => VV q (m+2) == twr q m


/-! ## §8 FEASIBILITY MAP — a region-wide Stage-B theorem (assessment, no proofs)

This section is a MAP, not mathematics.  It records what one theorem covering ALL
standard 2-row matrices below `(0,0)(1,1)(2,2)` (row-1 entries ≤ 1) would require,
measured against the machinery of §1–§7, and it names the largest target that is
actually reachable next.  The `#guard`s at the end are the machine-checked part of
the assessment; the standardness verdicts come from the yaBMS BM4 reference
implementation (`c/bms -s`, <https://github.com/koteitan/yaBMS>), which is the same
evidence standard `Evidence/StageA.lean` uses for `stdSeq`.

RECOMMENDATION (details in §8.6): do NOT attempt the region theorem yet.  Its
blocking problem is not the length of the proof but the hypothesis: the Stage-A
style standardness predicate does not lift (§8.2, measured).  The largest honest
target is F4 of §8.5 — the "ladder + one column" family, whose closed forms are
pinned by `#guard` below.

### §8.1 What the region contains

Window: every 2-row matrix whose first column is `(0,0)`, with row-0 entries < 4,
row-1 entries < 2 and length ≤ 5 — 4681 matrices.

  4681  matrices in the window
   153  standard (yaBMS)
   107  of those are limits (`BMS.kind = lim`; the 46 successors need an `esucc`
        statement, not E3 — cf. `Evidence.StageA.esucc_general`)
     8  are literal instances of the three families proved here (F1/F2/F3)

  the 107 limits split as
    18  row-1-all-zero          — Stage A's region (`e3_general`), modulo a bridge
                                  between `oneRow s` and a 2-row matrix with row 1
                                  identically zero, which is not proved anywhere
    17  ladder, or ladder + one column   (the F1/F2/F3 instances and the F4 gap)
    72  neither — of which 35 are "ladder + two columns" and 37 need three or more.

The window truncates every family at a = 3 and length 5, so these are shape
statistics, not a measure of the (infinite) region.

### §8.2 Q1 — the standardness invariant.  MAIN FINDING, and it is negative

`stdSeq` (StageA §6) = "starts with 0" + "every block is `stdSeq` after `dec`" +
`descB (blockVals s)`, i.e. a syntactic recursion plus ONE semantic condition:
the block values descend weakly (Cantor normal form).  The obvious lift was tried
and measured over the whole 4681-matrix window.

Three syntactic conditions, each NECESSARY (0 false negatives over the window):

  C1  every column after the first with row-0 entry 0 has row-1 entry 0
      (accepts 2801, 2648 false positives)
  C2  row 0 grows by at most 1: `r0 (x+1) ≤ r0 x + 1`
      (accepts 793, 640 false positives)
  C3  `r1 x ≤ r1 (P₀ x) + 1`, and `r1 x = 0` when x has no row-0 parent
      (accepts 2801, 2648 false positives)

  C1 ∧ C2 ∧ C3 accepts 449 of 4681: still 296 false positives, 0 false negatives.

Adding the Stage-A-style value condition — "no absorption": a `(0,0)`-block's
summand `ω^v` must be ≤ the last component of the accumulator, and at a
`(0,1)`-block at level k the accumulator must be 0 or a φ_k-value (a raw `φ̄(c,·)`
with `ofNat k ≤ c`, which is exactly what makes `logPhi (ofNat k) acc` total) —
brings the count to 227 accepted, 75 false positives, and INTRODUCES A FALSE
NEGATIVE:

  `(0,0)(1,1)(1,0)(2,1)(2,0)` is standard (yaBMS = 1) but its inner fold absorbs:
  the `(1,1)` column contributes ε₀ = `φ̄(1,0)`, and the next block contributes
  `ω^(ε₀+1) = φ̄(0,φ̄(1,0))`, which swallows it (`plus` drops the smaller summand).
  Its value is `φ̄(0,φ̄(0,φ̄(1,0)))` — the ε₀ is nowhere in it, yet the column is
  required for the parent structure of the columns after it.

So the Stage-A intuition "standard = the value is in normal form" is not merely
unproved on Stage B, it is FALSE.  The reason is structural and worth stating:

  * below ε₀ neither `ω^·` nor `φ_k` has a fixed point inside the region, so
    "the value is in CNF" and "the matrix is irredundant" coincide — that is why
    `stdSeq` works at all;
  * on Stage B both have fixed points inside the region.  Hence (a) different
    matrices can carry the same value — `o?((0,0)(1,0)(2,1)) = o?((0,0)(1,1))
    = φ̄(1,0)`, and the first of the two is non-standard (yaBMS = 0) although it
    passes C1–C3 and every value condition tried; and (b) a standard matrix may
    contain columns that contribute nothing to the value (the false negative
    above).  A predicate that only looks at the value cannot see either.

  Positive by-product, measured: `o?` IS injective on the 153 standard matrices of
  the window.  So the failure is entirely about which matrices are standard, not
  about the translation.

What this leaves for a region-wide theorem:

  (i)  take `BMS.Standard` (reachability, `BMS/Standard.lean`) as the hypothesis
       and induct on the reachability derivation.  Then "expand? preserves the
       invariant" is free — it is the definition — and the whole difficulty moves
       to the value side (§8.3).  This is also what yaBMS itself does: `isstd`
       builds the diagonal ancestor of the input and re-expands towards it, i.e.
       it decides reachability, not a local predicate.
  (ii) find a genuine ancestor-structure predicate.  C1–C3 are a start (necessary,
       0 false negatives over 4681) but 296/4528 of the non-standard matrices in
       the window survive them; closing that gap is a BMS research question, not a
       Lean question, and this repo has no candidate for it.

  Either way the hypothesis is NOT a `stdSeq`-shaped `stdPair`, and writing one
  would be writing something false.

### §8.3 Q2 — the accumulator invariant, and the shape of the statement

Prerequisite that did not exist when this map was written: `oLAux` had no fuel-free
form.  Every value lemma in §2–§7 carries an explicit fuel budget (`(q+2)*m + 1`,
`(q+1)*m + 1`, …) threaded by hand from the matrix length; a region-wide induction
cannot carry those.  StageA solved the same problem once with `oPrAux_fuel` + `oV`
(`oV s = oPrAux (s.length+1) s`).  DONE — §9 below proves the analogue
(`oLAux_fuel`, `oLV`, `oLV_eq`, `oLAux_eq_oLV`); the measurement that suggested it
is still guarded below.

The invariant the value recursion needs is the one the F3 hand-off note guessed:
at every `(0,1)`-block at level k the accumulator is 0 or a φ_k-value.  Measured
true over the whole standard corpus.  It is exactly what makes `logPhi (ofNat k)
acc` total and makes `phiStep` a genuine successor step rather than a collapse.

Does the §7 tower machinery generalize to it?  Partly, and the split is sharp:

  * `twB`, `twB_phi`, `deg_twB`, `ltF_twB_mono` are base- and level-generic
    already and will be reused verbatim — every Stage-B fundamental sequence at a
    successor level is such a tower.
  * `bse`/`xbase`/`sbse`, and `zt`/`VV`, are closed forms of ONE family and do not
    generalize at all.  For an arbitrary standard matrix the tower base is
    "whatever the accumulator was", which has no closed form.

  CONSEQUENCE FOR THE GOAL STATEMENT.  A region-wide theorem cannot have
  "per-matrix closed forms": there is no schema to write them in.  What it can
  have is the package stated relative to `o?` itself,

      ∀ n, lt (o?(M[n])) (o? M)
    ∧ ∀ n, ∃ k, lt (o?(M[n])) (fsN (o? M) (k+1))
    ∧ ∀ k, ∃ n, lt (fsN (o? M) (k+1)) (o?(M[n]))

  i.e. `Evidence.checkE3i` made universal.  Note the existential witnesses: the
  shifts are NOT uniform over the region (F2 uses kw n = n+1, nw k = k+2; F1 uses
  n+2, k+1; F3 uses n+1, k+1; row R5 of Rows/ProofsB uses n+3, k), so either the
  witnesses are existential or the statement carries a witness function computed
  from the matrix.  Part (a) of the package degenerates to `o?` being defined on
  the expansion — a domain-closure statement, not a value statement.

### §8.4 Q3 — inventory: what is already matrix-generic

Generic, usable as-is for any shape (≈ 500 of the ≈ 1960 lines of §1–§7):

  §1  `ups`/`tailU`/`runq` and their `len`/`take`/`decP`/`r0`/`inFrag` lemmas
  §3  `ofNat_inj`, `ofNat_bne`, `ofNat_ne_zero`, `ltF_ofNat_mono`, `lt_ofNat_mono`
  §4  ALL of it — `downFrom`, `iterParent_desc`, `filter_downFrom`: the bad root at
      row 1 for a symbolic parameter.  This is the only part of the BMS side that
      is already general.
  §5  `chainP`, `chainP_add`, `chainP_collapse`, `iterParent_zero`,
      `kindT_ofNat_succ`, `predT_ofNat_succ`, `ltF_iterT_bound'`
  §6  `oLAux_chainV` (already stated for an arbitrary block function `B`),
      `len_frep_gen`, `getD_append_lt'`/`_ge'`
  §7  `twB` + its five lemmas, `ltF_ofNat_not`, `plus_self`, `splitFin_add_pair`,
      `phiNF_add_pair`, `splitFin_add_one`, `ltF_M_add_phi`, `zero_bne_ofNat`
  plus, from Rows/ProofsB: `frep`/`flat_frep`/`decP_frep`/`r0_frep`/`inFrag_frep`,
      `blocksP_*`, `oLAux_single`, `oLAux_cons'`, `oLAux_zs`, `o?_pair`,
      `plus_drop`, `lt_of_ltF`, `ltF_phi_same`/`_fst`/`_snd`/`_eq`.

Family-shape-specific, re-proved from scratch for each of M1/M2/M3 (≈ 1460 lines,
of which the BMS-side expansion computation alone — `ent_*`, `parent*_*`,
`ascends_*`, `delta_*`, `lnz_*`, `getLast_*`, `expand_*` — is ≈ 830 lines, ≈ 42%
of §1–§7):

  §2  the M2 expansion;  §5  the M1 expansion + `oLAux_chain` + `valE1`;
  §6  the M3 expansion + `valV3`/`valE3`;  §3/§5/§7 the per-term-shape `fsN`
  computations (`fs_t`, `fs_t1`, `fs_t3`) and `ltF` comparison chains.

  So: the single biggest new piece of work for ANY route is doing the BM4
  expansion once, symbolically, for an arbitrary matrix of the fragment — bad root
  (§4 covers the row-1 case), Δ₀, the ascension matrix, and the `frep` shape of the
  result.  Nothing in §2/§5/§6 can be reused for that; only §4 can.

### §8.5 Q4 — the recommended intermediate: F4, "ladder + one column"

    M1 q ++ [[b, r]]      (a = q+1, the ladder `(0,0)(1,1)…(a,1)` plus one column)

Every such matrix with `b ≥ 1`, and `(b,r) = (0,0)`, is standard (yaBMS, checked
for a = 1..6 and all b ≤ a+1); `(0,1)` is excluded by C1.  Measured closed forms,
writing `Z = φ̄(a,0) = zt q` (all `#guard`ed below for a ≤ 6):

    r = 0,  b = 0        Z + 1                    successor — `expand?` drops the
                                                  column; an `esucc`-style claim
    r = 0,  b = 1        φ̄(0, Z)                  R2 is the a = 1 instance
    r = 0,  2 ≤ b ≤ a    φ̄(b-1, φ̄(0, Z))          (0,0)(1,1)(2,1)(2,0) is a = b = 2
    r = 0,  b = a+1      φ̄(a, ω)                  = F2, PROVED (`e3_family`)
    r = 1,  1 ≤ b < a    φ̄(b, Z)                  no table row yet; smallest is
                                                  (0,0)(1,1)(2,1)(3,1)(1,1), a = 3
    r = 1,  b = a        φ̄(a, 1)                  = F3, PROVED (`e3_F3family`)
    r = 1,  b = a+1      φ̄(a+1, 0)                = F1 at a+1, PROVED

So F4 is F1 ∪ F2 ∪ F3 plus exactly three new limit cases and one successor case,
in a single two-parameter statement.  It would take the table from 7 covered rows
to 8 (R2 joins) and, more to the point, would be the first Stage-B theorem whose
value is not a fixed closed form but a function of a second parameter.

Why it is the right size: the three new cases all have the same BMS-side shape as
F2/F3 (bad root by §4, one `frep` of a ladder block), and their terms are one or
two `φ̄` layers over `Z` — the `chainP`/`twB` machinery already covers the term
side.  STATUS: §10 proves the BMS side of the whole `r = 1` column in one lemma
(`expand_M4`, which subsumes `expand_M3` and `expand_M1`), E1 for the ladder
(`o?_M1`), and the `b = 0` successor case complete (`o?_M4z`, `esucc_M4z`); the
value side of case A (`r = 1`, `1 ≤ b < a`) and of `r = 0`, `2 ≤ b ≤ a` is still open,
see the note at the end of §10.  Case B (`r = 0`, `b = 1`) is DONE — `e3_F4bfamily`,
with R2 as its `a = 1` instance.  Cost estimate, calibrated on F3 (one case, one session, with all machinery
already present): 2–3 sessions.  The natural continuation, "ladder + two columns",
covers 35 of the 72 uncovered limits in the window and is the next unit after that.

### §8.6 Recommendation

  Full region theorem  — NOT tractable now, and the blocker is the hypothesis, not
    the proof length: §8.2 shows there is no `stdSeq`-shaped predicate to hypothesize
    (it is false, not merely unproved), and the only sound alternative,
    `BMS.Standard` by reachability induction, additionally needs the symbolic BM4
    expansion of §8.4 (≈ the largest single piece of work in the file) and a
    statement shape without closed forms (§8.3).  Estimate: 6+ sessions, with one
    genuine research risk (the value invariant under an arbitrary expansion step).

  Intermediate family-union  — RECOMMENDED: F4 of §8.5, 2–3 sessions, no research
    risk, closed forms already machine-checked below.

  Cheap prerequisite, worth doing first in either case (~40 lines, no risk):
    `oLAux_fuel` + `oLV`, the fuel-free value function of §8.3.  DONE in §9.

Nothing in this section is proved; the `#guard`s below fix the three factual claims
the assessment rests on (the redundancy phenomenon, the absorbing standard matrix,
and the F4 closed forms), so that a later session can re-check them without rerunning
yaBMS. -/

-- §8.2  two different matrices, one value: the redundancy phenomenon.  yaBMS says
-- (0,0)(1,0)(2,1) is NOT standard and (0,0)(1,1) is, yet both translate to φ̄(1,0).
#guard o? [[0,0],[1,0],[2,1]] == o? [[0,0],[1,1]]
#guard o? [[0,0],[1,1]] == some (phi one zero)

-- §8.2  the false negative: (0,0)(1,1)(1,0)(2,1)(2,0) is standard (yaBMS) and its
-- value has lost the ε₀ that the (1,1) column contributed — the fold absorbs.
#guard o? [[0,0],[1,1],[1,0]] == some (phi zero (phi one zero))
#guard o? [[0,0],[1,1],[1,0],[2,1],[2,0]] == some (phi zero (phi zero (phi one zero)))

-- §8.3  `oLAux` is constant in the fuel above the length, over the expansion fan of
-- the boundary matrix (the evidence for the missing `oLAux_fuel`).
#guard (Evidence.corpus [[0,0],[1,1],[2,2]] 3 3).all fun m => (List.range 3).all fun k =>
  Trans.Pair.oLAux (m.length + 1) (k+1) m == Trans.Pair.oLAux (3 * m.length + 7) (k+1) m

-- §8.5  the conjectured closed forms of F4, for a = q+1 ≤ 6 and every 1 ≤ b ≤ a+1
#guard (List.range 6).all fun q => (List.range (q+2)).all fun i =>
  let b := i+1
  let Z : Term := phi (ofNat (q+1)) zero
  Trans.o? (M1 q ++ [[b,0]]) == some
    (if b == q+2 then phi (ofNat (q+1)) omega
     else if b == 1 then phi zero Z
     else phi (ofNat (b-1)) (phi zero Z))
#guard (List.range 6).all fun q => (List.range (q+2)).all fun i =>
  let b := i+1
  let Z : Term := phi (ofNat (q+1)) zero
  Trans.o? (M1 q ++ [[b,1]]) == some
    (if b == q+2 then phi (ofNat (q+2)) zero
     else if b == q+1 then phi (ofNat (q+1)) one
     else phi (ofNat b) Z)
#guard (List.range 6).all fun q =>
  Trans.o? (M1 q ++ [[0,0]]) == some (plus (phi (ofNat (q+1)) zero) one)


/-! ## §9 The fuel-free value function `oLV` (the prerequisite named in §8.3)

`Trans.Pair.oLAux` carries recursion fuel, and every value lemma of §2–§7 threads an
explicit budget by hand (`(q+2)*m + 1`, `(q+1)*m + 1`, …) from the length of the
matrix.  As in the one-row region (`Evidence.StageA.oPrAux_fuel` / `oV`), the fuel
stops mattering as soon as it reaches the length of the sequence, so on that range
`oLAux` is a genuine function `oLV` of the level and the sequence, with a recursion
equation free of fuel.  `oLAux_eq_oLV` converts any fuelled statement of this file
into the fuel-free form.

The two ingredients the one-row development already had and this one did not:
`blocksP` flattens back to its input (so a block is never longer than the sequence),
and the `oLAux` fold is a `foldl` rather than a `map`+`foldr`, so the congruence step
needs `foldl_congrP` instead of `List.map_congr_left`. -/

theorem headD_append_tail_flattenP (l : List (List BMS.Col)) :
    l.headD [] ++ l.tail.flatten = l.flatten := by
  cases l <;> rfl

theorem blocksP_flatten : ∀ s : List BMS.Col, (Trans.Pair.blocksP s).flatten = s
  | [] => rfl
  | c :: rest => by
    cases rest with
    | nil => rfl
    | cons h t =>
      by_cases hy : Trans.Pair.r0 h = 0
      · rw [blocksP_cons_zero c h t hy]
        show c :: (Trans.Pair.blocksP (h :: t)).flatten = c :: h :: t
        rw [blocksP_flatten (h :: t)]
      · rw [blocksP_cons_nz c h t hy]
        show (c :: (Trans.Pair.blocksP (h :: t)).headD [])
            ++ (Trans.Pair.blocksP (h :: t)).tail.flatten = c :: h :: t
        rw [List.cons_append, headD_append_tail_flattenP, blocksP_flatten (h :: t)]

theorem length_le_of_mem_flattenP :
    ∀ (l : List (List BMS.Col)) (b : List BMS.Col), b ∈ l → b.length ≤ l.flatten.length
  | [], _, h => absurd h (by simp)
  | c :: l', b, h => by
    rcases List.mem_cons.mp h with h | h
    · subst h
      show b.length ≤ (b ++ l'.flatten).length
      rw [List.length_append]
      omega
    · have := length_le_of_mem_flattenP l' b h
      show b.length ≤ (c ++ l'.flatten).length
      rw [List.length_append]
      omega

theorem blocksP_length_le {s b : List BMS.Col} (h : b ∈ Trans.Pair.blocksP s) :
    b.length ≤ s.length := by
  have := length_le_of_mem_flattenP (Trans.Pair.blocksP s) b h
  rwa [blocksP_flatten] at this

theorem decP_length (t : List BMS.Col) : (Trans.Pair.decP t).length = t.length :=
  List.length_map _

theorem foldl_congrP {α β : Type _} (f g : β → α → β) : ∀ (l : List α) (init : β),
    (∀ acc a, a ∈ l → f acc a = g acc a) → l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | a :: t, init, h => by
    show t.foldl f (f init a) = t.foldl g (g init a)
    rw [h init a (List.Mem.head _)]
    exact foldl_congrP f g t (g init a) (fun acc x hx => h acc x (List.mem_cons_of_mem a hx))

theorem oLAux_fuel : ∀ (f g k : Nat) (s : List BMS.Col), s.length ≤ f → s.length ≤ g →
    Trans.Pair.oLAux f k s = Trans.Pair.oLAux g k s
  | 0, g, k, s, hf, _ => by
    have hs : s = [] := by
      cases s with
      | nil => rfl
      | cons a t => simp at hf
    subst hs
    rw [oLAux_nil, oLAux_nil]
  | f + 1, 0, k, s, _, hg => by
    have hs : s = [] := by
      cases s with
      | nil => rfl
      | cons a t => simp at hg
    subst hs
    rw [oLAux_nil, oLAux_nil]
  | f + 1, g + 1, k, s, hf, hg => by
    rw [oLAux_cons', oLAux_cons']
    refine foldl_congrP _ _ _ _ ?_
    intro acc b hb
    have hbl : b.length ≤ s.length := blocksP_length_le hb
    cases b with
    | nil => rfl
    | cons c t =>
      have h1 : (Trans.Pair.decP t).length ≤ f := by
        rw [decP_length]; simp at hf hbl ⊢; omega
      have h2 : (Trans.Pair.decP t).length ≤ g := by
        rw [decP_length]; simp at hg hbl ⊢; omega
      show (if Trans.Pair.r1 c == 0 then
              plus acc (omegaNF (Trans.Pair.oLAux f 1 (Trans.Pair.decP t)))
            else Trans.Pair.phiStep (ofNat k) acc (Trans.Pair.oLAux f (k+1) (Trans.Pair.decP t)))
          = (if Trans.Pair.r1 c == 0 then
              plus acc (omegaNF (Trans.Pair.oLAux g 1 (Trans.Pair.decP t)))
            else Trans.Pair.phiStep (ofNat k) acc (Trans.Pair.oLAux g (k+1) (Trans.Pair.decP t)))
      rw [oLAux_fuel f g 1 (Trans.Pair.decP t) h1 h2,
        oLAux_fuel f g (k+1) (Trans.Pair.decP t) h1 h2]

/-- The value of a column sequence at level `k`, with the fuel fixed to a
    sufficient amount: the 2-row analogue of `Evidence.StageA.oV`. -/
def oLV (k : Nat) (s : List BMS.Col) : Term := Trans.Pair.oLAux (s.length + 1) k s

theorem oLAux_eq_oLV {f k : Nat} {s : List BMS.Col} (hf : s.length ≤ f) :
    Trans.Pair.oLAux f k s = oLV k s := oLAux_fuel f (s.length + 1) k s hf (by omega)

theorem oLV_nil (k : Nat) : oLV k [] = zero := rfl

/-- The recursion equation of `oLV`, free of fuel. -/
theorem oLV_eq (k : Nat) (s : List BMS.Col) :
    oLV k s = (Trans.Pair.blocksP s).foldl (init := zero) (fun acc b =>
      match b with
      | [] => acc
      | c :: t =>
        if Trans.Pair.r1 c == 0 then plus acc (omegaNF (oLV 1 (Trans.Pair.decP t)))
        else Trans.Pair.phiStep (ofNat k) acc (oLV (k+1) (Trans.Pair.decP t))) := by
  show Trans.Pair.oLAux (s.length + 1) k s = _
  rw [oLAux_cons']
  refine foldl_congrP _ _ _ _ ?_
  intro acc b hb
  have hbl : b.length ≤ s.length := blocksP_length_le hb
  cases b with
  | nil => rfl
  | cons c t =>
    have h1 : (Trans.Pair.decP t).length ≤ s.length := by
      rw [decP_length]; simp at hbl ⊢; omega
    show (if Trans.Pair.r1 c == 0 then
            plus acc (omegaNF (Trans.Pair.oLAux s.length 1 (Trans.Pair.decP t)))
          else Trans.Pair.phiStep (ofNat k) acc
            (Trans.Pair.oLAux s.length (k+1) (Trans.Pair.decP t))) = _
    rw [oLAux_eq_oLV h1, oLAux_eq_oLV h1]

/-- `o?` on the Stage-B fragment, in fuel-free form. -/
theorem o?_oLV {m : Matrix} (h1 : onlyRow0 m = false) (h2 : Trans.Pair.inFrag m = true) :
    o? m = some (oLV 1 m) := o?_pair h1 h2

#guard (Evidence.corpus [[0,0],[1,1],[2,2]] 3 3).all fun m => (List.range 3).all fun k =>
  oLV (k+1) m == Trans.Pair.oLAux (3 * m.length + 7) (k+1) m
#guard (List.range 4).all fun q => (List.range 4).all fun n =>
  Trans.o? (BMS.expand (M3 q) n) == some (oLV 1 (BMS.expand (M3 q) n))


/-! ## §10 F4 : `(0,0)(1,1)…(a,1)(b,r)` — the "ladder + one column" family (§8.5)

The BMS side of the whole `r = 1` column of the §8.5 case table, in ONE lemma
(`expand_M4`): for every `1 ≤ b ≤ a+1` the bad root is 0 (via §4), Δ₀ = b, and the
expansion is the ladder block `lad (q+1)` repeated with step `b`,

    expand? (M1 q ++ [[b,1]]) n = some (frep (lad (q+1)) b 0 (n+1)).

`b = a` is `expand_M3` and `b = a+1` is `expand_M1` at `q+1` (`M4_M3`, `M4_top`), so
this subsumes the BMS side of F3 and of F1.  What is still missing for the packaged
E3 of the new cases is the VALUE side; see the note at the end of the section. -/

/-- `M4 q b = (0,0)(1,1)…(a,1)(b,1)` with `a = q+1`; the intended range is `1 ≤ b ≤ a+1`. -/
def M4 (q b : Nat) : Matrix := M1 q ++ [[b, 1]]

theorem len_M4 (q b : Nat) : (M4 q b).length = q + 3 := by
  show ((M1 q) ++ [[b,1]]).length = q + 3
  rw [List.length_append, len_M1]
  rfl

theorem ent_M4_lt (q b x y : Nat) (h : x < q + 2) : BMS.ent (M4 q b) x y = BMS.ent (M1 q) x y := by
  show (((M1 q ++ [[b,1]]).getD x []).getD y 0) = (((M1 q).getD x []).getD y 0)
  rw [getD_append_lt' _ _ x (by rw [len_M1]; omega)]

theorem ent_M4_top0 (q b : Nat) : BMS.ent (M4 q b) (q+2) 0 = b := by
  show (((M1 q ++ [[b,1]]).getD (q+2) []).getD 0 0) = b
  rw [getD_append_ge' _ _ (q+2) (by rw [len_M1]; omega), len_M1,
    show q + 2 - (q+2) = 0 from by omega]
  rfl

theorem ent_M4_top1 (q b : Nat) : BMS.ent (M4 q b) (q+2) 1 = 1 := by
  show (((M1 q ++ [[b,1]]).getD (q+2) []).getD 1 0) = 1
  rw [getD_append_ge' _ _ (q+2) (by rw [len_M1]; omega), len_M1,
    show q + 2 - (q+2) = 0 from by omega]
  rfl

theorem ent_M4_0 (q b x : Nat) (h : x ≤ q+1) : BMS.ent (M4 q b) x 0 = x := by
  rw [ent_M4_lt q b x 0 (by omega), ent_M1_0 q x h]

theorem ent_M4_1_zero (q b : Nat) : BMS.ent (M4 q b) 0 1 = 0 := by
  rw [ent_M4_lt q b 0 1 (by omega), ent_M1_1_zero]

theorem ent_M4_1 (q b x : Nat) (h1 : 1 ≤ x) (h2 : x ≤ q+1) : BMS.ent (M4 q b) x 1 = 1 := by
  rw [ent_M4_lt q b x 1 (by omega), ent_M1_1 q x h1 h2]

theorem parent0_M4 (q b x : Nat) (h1 : 1 ≤ x) (h2 : x ≤ q+1) :
    BMS.parent (M4 q b) 0 x = some (x-1) := by
  show (((List.range x).filter
      (fun p => decide (BMS.ent (M4 q b) p 0 < BMS.ent (M4 q b) x 0))).max?) = some (x-1)
  rw [Evidence.StageA.max?_filter_range]
  refine Evidence.StageA.lastSome_spec _ x (x-1) (by omega) ?_ ?_
  · rw [ent_M4_0 q b (x-1) (by omega), ent_M4_0 q b x (by omega)]
    exact decide_eq_true (by omega)
  · intro r hr1 hr2
    omega

theorem parent0_M4_zero (q b : Nat) : BMS.parent (M4 q b) 0 0 = none := rfl

theorem parent0_M4_top (q b : Nat) (h1 : 1 ≤ b) (h2 : b ≤ q+2) :
    BMS.parent (M4 q b) 0 (q+2) = some (b-1) := by
  show (((List.range (q+2)).filter
      (fun p => decide (BMS.ent (M4 q b) p 0 < BMS.ent (M4 q b) (q+2) 0))).max?) = some (b-1)
  rw [Evidence.StageA.max?_filter_range, ent_M4_top0]
  refine Evidence.StageA.lastSome_spec _ (q+2) (b-1) (by omega) ?_ ?_
  · rw [ent_M4_0 q b (b-1) (by omega)]
    exact decide_eq_true (by omega)
  · intro r hr1 hr2
    rw [ent_M4_0 q b r (by omega)]
    exact decide_eq_false (by omega)

theorem chain_M4_top (q b : Nat) (h1 : 1 ≤ b) (h2 : b ≤ q+2) :
    BMS.iterParent (BMS.parent (M4 q b) 0) (q+2) (q+2) = downFrom b := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  show (match BMS.parent (M4 q (b'+1)) 0 (q+2) with
        | none => [] | some p => p :: BMS.iterParent (BMS.parent (M4 q (b'+1)) 0) (q+1) p)
      = downFrom (b'+1)
  rw [parent0_M4_top q (b'+1) (by omega) (by omega)]
  show (b'+1-1) :: BMS.iterParent (BMS.parent (M4 q (b'+1)) 0) (q+1) (b'+1-1) = downFrom (b'+1)
  rw [show b'+1-1 = b' from by omega,
    iterParent_desc (fun z hz1 hz2 => parent0_M4 q (b'+1) z hz1 (by omega))
      (parent0_M4_zero q (b'+1)) (q+1) b' (by omega) (by omega)]
  rfl

theorem parent1_M4 (q b j : Nat) (h1 : 1 ≤ j) (h2 : j ≤ q+1) :
    BMS.parent (M4 q b) 1 j = some 0 := by
  obtain ⟨y, hy⟩ : ∃ y, j = y + 1 := ⟨j - 1, by omega⟩
  subst hy
  have hchain : BMS.iterParent (BMS.parent (M4 q b) 0) (y+1) (y+1) = downFrom (y+1) :=
    iterParent_desc (fun z hz1 hz2 => parent0_M4 q b z hz1 (by omega)) (parent0_M4_zero q b)
      (y+1) (y+1) (by omega) (by omega)
  have hP0 : (decide (BMS.ent (M4 q b) 0 1 < 1)) = true := by
    rw [ent_M4_1_zero]
    exact decide_eq_true (by omega)
  have hPp : ∀ p, 1 ≤ p → p ≤ y → (decide (BMS.ent (M4 q b) p 1 < 1)) = false := by
    intro p hp1 hp2
    rw [ent_M4_1 q b p hp1 (by omega)]
    exact decide_eq_false (by omega)
  show (((BMS.iterParent (BMS.parent (M4 q b) 0) (y+1) (y+1)).filter
      (fun p => decide (BMS.ent (M4 q b) p 1 < BMS.ent (M4 q b) (y+1) 1))).max?) = some 0
  rw [hchain, ent_M4_1 q b (y+1) h1 h2,
    filter_downFrom (P := fun p => decide (BMS.ent (M4 q b) p 1 < 1)) hP0 y hPp]
  rfl

theorem parent1_M4_top (q b : Nat) (h1 : 1 ≤ b) (h2 : b ≤ q+2) :
    BMS.parent (M4 q b) 1 (q+2) = some 0 := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hP0 : (decide (BMS.ent (M4 q (b'+1)) 0 1 < 1)) = true := by
    rw [ent_M4_1_zero]
    exact decide_eq_true (by omega)
  have hPp : ∀ p, 1 ≤ p → p ≤ b' → (decide (BMS.ent (M4 q (b'+1)) p 1 < 1)) = false := by
    intro p hp1 hp2
    rw [ent_M4_1 q (b'+1) p hp1 (by omega)]
    exact decide_eq_false (by omega)
  show (((BMS.iterParent (BMS.parent (M4 q (b'+1)) 0) (q+2) (q+2)).filter
      (fun p => decide (BMS.ent (M4 q (b'+1)) p 1 < BMS.ent (M4 q (b'+1)) (q+2) 1))).max?)
      = some 0
  rw [chain_M4_top q (b'+1) (by omega) (by omega), ent_M4_top1,
    filter_downFrom (P := fun p => decide (BMS.ent (M4 q (b'+1)) p 1 < 1)) hP0 b' hPp]
  rfl

theorem parent1_M4_zero (q b : Nat) : BMS.parent (M4 q b) 1 0 = none := rfl

theorem ascends_M4 (q b j y : Nat) (hj : j ≤ q+1) (hy : y ≤ 1) :
    BMS.ascends (M4 q b) 0 j y = true := by
  cases j with
  | zero => rfl
  | succ j' =>
    show ((j'+1 == 0)
      || ((BMS.iterParent (BMS.parent (M4 q b) y) (j'+1) (j'+1)).contains 0)) = true
    rw [show ((j'+1 == 0)) = false from rfl]
    simp only [Bool.false_or]
    cases y with
    | zero =>
      rw [iterParent_desc (fun z hz1 hz2 => parent0_M4 q b z hz1 (by omega))
        (parent0_M4_zero q b) (j'+1) (j'+1) (by omega) (by omega)]
      exact contains_downFrom_zero (j'+1) (by omega)
    | succ y' =>
      have hy1 : y' = 0 := by omega
      subst hy1
      show ((BMS.iterParent (BMS.parent (M4 q b) 1) (j'+1) (j'+1)).contains 0) = true
      rw [show BMS.iterParent (BMS.parent (M4 q b) 1) (j'+1) (j'+1) = [0] from by
        show (match BMS.parent (M4 q b) 1 (j'+1) with
              | none => [] | some p => p :: BMS.iterParent (BMS.parent (M4 q b) 1) j' p) = [0]
        rw [parent1_M4 q b (j'+1) (by omega) (by omega)]
        show (0:Nat) :: BMS.iterParent (BMS.parent (M4 q b) 1) j' 0 = [0]
        rw [iterParent_zero (parent1_M4_zero q b) j']]
      rfl

theorem delta_M4_0 (q b : Nat) : BMS.delta (M4 q b) 0 1 0 = b := by
  show (if 0 < 1 then BMS.ent (M4 q b) ((M4 q b).length - 1) 0 - BMS.ent (M4 q b) 0 0 else 0) = b
  rw [if_pos (by omega), len_M4, show q + 3 - 1 = q + 2 from by omega, ent_M4_top0,
    ent_M4_0 q b 0 (by omega)]
  omega

theorem delta_M4_1 (q b : Nat) : BMS.delta (M4 q b) 0 1 1 = 0 := by
  show (if 1 < 1 then BMS.ent (M4 q b) ((M4 q b).length - 1) 1 - BMS.ent (M4 q b) 0 1 else 0) = 0
  rw [if_neg (by omega)]

theorem getLast_M4 (q b : Nat) : (M4 q b).getLast? = some ([b, 1] : BMS.Col) :=
  List.getLast?_concat

theorem lnz_col1 (b : Nat) (hb : 1 ≤ b) : BMS.lnz ([b, 1] : BMS.Col) = some 1 := by
  show (((List.range 2).filter (fun y => decide (([b,1] : BMS.Col).getD y 0 > 0))).max?) = some 1
  have h0 : (decide ((([b,1] : BMS.Col).getD 0 0) > 0)) = true := by
    show (decide ((b : Nat) > 0)) = true
    exact decide_eq_true (by omega)
  show ((([0,1] : List Nat).filter (fun y => decide (([b,1] : BMS.Col).getD y 0 > 0))).max?)
      = some 1
  rw [List.filter_cons, h0]
  rfl

/-- **The unified r = 1 expansion.**  For `1 ≤ b ≤ a+1` the copies are the full ladder
    block `lad (q+1)` shifted by `b` per copy.  `b = a` is `expand_M3`, `b = a+1` is
    `expand_M1` at `q+1`. -/
theorem expand_M4 (q b n : Nat) (h1 : 1 ≤ b) (h2 : b ≤ q+2) :
    BMS.expand? (M4 q b) n = some (frep (lad (q+1)) b 0 (n+1)) := by
  have hpar : BMS.parent (M4 q b) 1 ((M4 q b).length - 1) = some 0 := by
    rw [len_M4, show q + 3 - 1 = q + 2 from by omega]
    exact parent1_M4_top q b h1 h2
  have hlen1 : (M4 q b).length - 1 - 0 = q + 2 := by rw [len_M4]; omega
  have hmap : ∀ (o : Nat),
      (List.range (q+2)).map (fun x => ([x + o, BMS.ent (M4 q b) x 1] : BMS.Col))
        = lad (q+1) o := by
    intro o
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    show ([0 + o, BMS.ent (M4 q b) 0 1] : BMS.Col) :: _ = ([o,0] : BMS.Col) :: ups (o+1) (q+1)
    rw [show (0:Nat)+o = o from by omega, ent_M4_1_zero, ups_range (q+1) (o+1)]
    congr 1
    refine List.map_congr_left ?_
    intro i hi
    have hi' : i < q+1 := List.mem_range.mp hi
    show ([(i+1) + o, BMS.ent (M4 q b) (i+1) 1] : BMS.Col) = ([(o+1)+i, 1] : BMS.Col)
    rw [ent_M4_1 q b (i+1) (by omega) (by omega), show (i+1)+o = (o+1)+i from by omega]
  have hbad : ∀ (c : Nat), (List.range (q+2)).map (fun x =>
      (List.range ([b,1] : BMS.Col).length).map (fun y => BMS.ent (M4 q b) (0+x) y
        + c * BMS.delta (M4 q b) 0 1 y
          * (if BMS.ascends (M4 q b) 0 (0+x) y = true then 1 else 0)))
      = lad (q+1) (b*c + 0) := by
    intro c
    have hinner : ∀ x ∈ List.range (q+2),
        (List.range ([b,1] : BMS.Col).length).map (fun y => BMS.ent (M4 q b) (0+x) y
          + c * BMS.delta (M4 q b) 0 1 y
            * (if BMS.ascends (M4 q b) 0 (0+x) y = true then 1 else 0))
        = ([x + (b*c + 0), BMS.ent (M4 q b) x 1] : BMS.Col) := by
      intro x hx
      have hx' : x < q+2 := List.mem_range.mp hx
      show [BMS.ent (M4 q b) (0+x) 0 + c * BMS.delta (M4 q b) 0 1 0
              * (if BMS.ascends (M4 q b) 0 (0+x) 0 = true then 1 else 0),
            BMS.ent (M4 q b) (0+x) 1 + c * BMS.delta (M4 q b) 0 1 1
              * (if BMS.ascends (M4 q b) 0 (0+x) 1 = true then 1 else 0)] = _
      rw [show (0:Nat)+x = x from by omega, delta_M4_0, delta_M4_1,
        ascends_M4 q b x 0 (by omega) (by omega), ascends_M4 q b x 1 (by omega) (by omega),
        ent_M4_0 q b x (by omega)]
      simp only [if_true, Nat.mul_one, Nat.mul_zero, Nat.add_zero]
      rw [show x + c * b = x + (b*c + 0) from by rw [Nat.mul_comm]; omega]
      rfl
    rw [List.map_congr_left hinner, hmap (b*c + 0)]
  simp only [BMS.expand?, getLast_M4, Option.bind_eq_bind, Option.bind_some, lnz_col1 b h1, hpar,
    Option.pure_def, hlen1]
  rw [List.map_congr_left (fun c _ => hbad c), flat_frep]
  rfl

/-- the two proved families are the top two instances -/
theorem ups_snoc (o p : Nat) : ups o (p+1) = ups o p ++ [([o+p, 1] : BMS.Col)] := by
  rw [ups_range (p+1) o, ups_range p o, List.range_succ, List.map_append]
  rfl

theorem M4_top (q : Nat) : M4 q (q+2) = M1 (q+1) := by
  show M1 q ++ [[q+2,1]] = lad (q+2) 0
  show (([0,0] : BMS.Col) :: ups 1 (q+1)) ++ [[q+2,1]] = ([0,0] : BMS.Col) :: ups 1 (q+2)
  rw [List.cons_append, ups_snoc 1 (q+1), show (1:Nat)+(q+1) = q+2 from by omega]

theorem M4_M3 (q : Nat) : M4 q (q+1) = M3 q := rfl

#guard (List.range 4).all fun q => (List.range 4).all fun i =>
  (List.range 3).all fun n =>
    BMS.expand? (M4 q (i+1)) n == if i+1 ≤ q+2 then some (frep (lad (q+1)) (i+1) 0 (n+1))
                                  else BMS.expand? (M4 q (i+1)) n

/-! ### E1 for the ladder, and the successor case `b = 0` -/

/-- A pure descending `(0,1)`-chain: `p+1` columns read at level `j`. -/
theorem oLAux_ups : ∀ (p j fuel : Nat), p + 1 ≤ fuel →
    Trans.Pair.oLAux fuel j (ups 0 (p+1)) = chainP j p (phi (ofNat (j+p)) zero)
  | 0, j, fuel, hf => by
    show Trans.Pair.oLAux fuel j (zs 1) = phi (ofNat (j+0)) zero
    rw [oLAux_zs 0 fuel j (by omega)]
    rfl
  | p + 1, j, fuel, hf => by
    cases fuel with
    | zero => omega
    | succ g =>
      have ht : ∀ c ∈ ups 1 (p+1), Trans.Pair.r0 c ≠ 0 := r0_ups (p+1) 1 (by omega)
      show Trans.Pair.oLAux (g+1) j (([0,1] : BMS.Col) :: ups 1 (p+1)) = _
      rw [oLAux_single g j [0,1] _ ht]
      show Trans.Pair.phiStep (ofNat j) zero
        (Trans.Pair.oLAux g (j+1) (Trans.Pair.decP (ups 1 (p+1)))) = _
      rw [decP_ups (p+1) 0, oLAux_ups p (j+1) g (by omega),
        show j + 1 + p = j + (p+1) from by omega]
      rfl

theorem onlyRow0_M1 (q : Nat) : onlyRow0 (M1 q) = false := by
  show onlyRow0 (([0,0] : BMS.Col) :: ups 1 (q+1)) = false
  rw [onlyRow0_cons, onlyRow0_ups q 1]
  rfl

/-- **E1 for the F1 family**: `o((0,0)(1,1)…(a,1)) = φ̄(a,0)`, for every `a = q+1 ≥ 1`
    (until now only `#guard`ed). -/
theorem o?_M1 (q : Nat) : o? (M1 q) = some (zt q) := by
  have ht : ∀ c ∈ ups 1 (q+1), Trans.Pair.r0 c ≠ 0 := r0_ups (q+1) 1 (by omega)
  rw [o?_pair (onlyRow0_M1 q) (inFrag_lad (q+1) 0), len_M1]
  show some (Trans.Pair.oLAux (q+2+1) 1 (([0,0] : BMS.Col) :: ups 1 (q+1))) = _
  rw [oLAux_single (q+2) 1 [0,0] _ ht]
  show some (plus zero (omegaNF (Trans.Pair.oLAux (q+2) 1
    (Trans.Pair.decP (ups 1 (q+1)))))) = _
  rw [decP_ups (q+1) 0, oLAux_ups q 1 (q+2) (by omega),
    show chainP 1 q (phi (ofNat (1+q)) zero) = zt q from by
      rw [show (1:Nat)+q = q+1 from by omega]
      exact chainP_collapse q 1 (q+1) zero (by omega),
    show omegaNF (zt q) = zt q from omegaNF_phi_ne_zero (ofNat_ne_zero q),
    plus_zero_left (show (zt q).isAP = true from rfl)]

/-- The successor case of the family: `(0,0)(1,1)…(a,1)(0,0)`. -/
def M4z (q : Nat) : Matrix := M1 q ++ [[0,0]]

theorem len_M4z (q : Nat) : (M4z q).length = q + 3 := by
  show ((M1 q) ++ [[0,0]]).length = q + 3
  rw [List.length_append, len_M1]
  rfl

theorem getLast_M4z (q : Nat) : (M4z q).getLast? = some ([0,0] : BMS.Col) :=
  List.getLast?_concat

theorem lnz_zero_col : BMS.lnz ([0,0] : BMS.Col) = none := rfl

/-- `expand?` drops the last column: this row is a successor. -/
theorem expand_M4z (q n : Nat) : BMS.expand? (M4z q) n = some (M1 q) := by
  have hdl : (M4z q).dropLast = M1 q := by
    show (M1 q ++ [[0,0]]).dropLast = M1 q
    rw [List.dropLast_concat]
  simp only [BMS.expand?, getLast_M4z, Option.bind_eq_bind, Option.bind_some, lnz_zero_col,
    Option.pure_def, hdl]

theorem onlyRow0_M4z (q : Nat) : onlyRow0 (M4z q) = false := by
  show onlyRow0 (M1 q ++ [[0,0]]) = false
  rw [onlyRow0_append, onlyRow0_M1 q]
  rfl

theorem inFrag_M4z (q : Nat) : Trans.Pair.inFrag (M4z q) = true := by
  show Trans.Pair.inFrag (M1 q ++ [[0,0]]) = true
  rw [inFrag_append, show Trans.Pair.inFrag (M1 q) = true from inFrag_lad (q+1) 0]
  rfl


theorem blocksP_ne_nil {s : List BMS.Col} (h : s ≠ []) : Trans.Pair.blocksP s ≠ [] := by
  intro hc
  apply h
  have hf := blocksP_flatten s
  rw [hc] at hf
  exact hf.symm

/-- Appending a `(0,0)` column appends one block: the `blocksP` analogue of
    `Evidence.StageA.blocks0_append` in the only case the successor rows need. -/
theorem blocksP_append_zero : ∀ (u : List BMS.Col), u ≠ [] →
    Trans.Pair.blocksP (u ++ [([0,0] : BMS.Col)])
      = Trans.Pair.blocksP u ++ [[([0,0] : BMS.Col)]]
  | [], h => absurd rfl h
  | [c], _ => rfl
  | c :: h :: t, _ => by
    have ih := blocksP_append_zero (h :: t) (by simp)
    by_cases hz : Trans.Pair.r0 h = 0
    · show Trans.Pair.blocksP (c :: (h :: (t ++ [[0,0]]))) = _
      rw [blocksP_cons_zero c h (t ++ [[0,0]]) hz]
      show ([c] : List BMS.Col) :: Trans.Pair.blocksP ((h :: t) ++ [([0,0] : BMS.Col)]) = _
      rw [ih, blocksP_cons_zero c h t hz]
      rfl
    · show Trans.Pair.blocksP (c :: (h :: (t ++ [[0,0]]))) = _
      rw [blocksP_cons_nz c h (t ++ [[0,0]]) hz]
      show (c :: (Trans.Pair.blocksP ((h :: t) ++ [([0,0] : BMS.Col)])).headD [])
          :: (Trans.Pair.blocksP ((h :: t) ++ [([0,0] : BMS.Col)])).tail = _
      rw [ih, blocksP_cons_nz c h t hz]
      cases hL : Trans.Pair.blocksP (h :: t) with
      | nil => exact absurd hL (blocksP_ne_nil (by simp))
      | cons b1 rest => rfl

/-- **E1 for the successor case**: `o((0,0)(1,1)…(a,1)(0,0)) = φ̄(a,0) + 1`. -/
theorem o?_M4z (q : Nat) : o? (M4z q) = some (plus (zt q) one) := by
  have ht : ∀ c ∈ ups 1 (q+1), Trans.Pair.r0 c ≠ 0 := r0_ups (q+1) 1 (by omega)
  have hb : Trans.Pair.blocksP (M4z q)
      = [([0,0] : BMS.Col) :: ups 1 (q+1)] ++ [[([0,0] : BMS.Col)]] := by
    show Trans.Pair.blocksP (M1 q ++ [([0,0] : BMS.Col)]) = _
    rw [blocksP_append_zero (M1 q) (by
      intro hc
      have := congrArg List.length hc
      rw [len_M1] at this
      simp at this)]
    show Trans.Pair.blocksP (([0,0] : BMS.Col) :: ups 1 (q+1)) ++ _ = _
    rw [blocksP_single [0,0] _ ht]
  rw [o?_pair (onlyRow0_M4z q) (inFrag_M4z q), len_M4z]
  show some (Trans.Pair.oLAux (q+3+1) 1 (M4z q)) = _
  rw [oLAux_cons', hb]
  show some (zsF (q+3) 1 (zsF (q+3) 1 zero (([0,0] : BMS.Col) :: ups 1 (q+1)))
    [[0,0]]) = _
  rw [show zsF (q+3) 1 zero (([0,0] : BMS.Col) :: ups 1 (q+1)) = zt q from by
      show plus zero (omegaNF (Trans.Pair.oLAux (q+3) 1
        (Trans.Pair.decP (ups 1 (q+1))))) = zt q
      rw [decP_ups (q+1) 0, oLAux_ups q 1 (q+3) (by omega),
        show chainP 1 q (phi (ofNat (1+q)) zero) = zt q from by
          rw [show (1:Nat)+q = q+1 from by omega]
          exact chainP_collapse q 1 (q+1) zero (by omega),
        show omegaNF (zt q) = zt q from omegaNF_phi_ne_zero (ofNat_ne_zero q),
        plus_zero_left (show (zt q).isAP = true from rfl)]]
  show some (plus (zt q) (omegaNF (Trans.Pair.oLAux (q+3) 1 (Trans.Pair.decP [])))) = _
  rfl

/-- The successor rule for the `b = 0` case: the expansion lands on the predecessor. -/
theorem esucc_M4z (q n : Nat) : o? (BMS.expand (M4z q) n) = some (predT (plus (zt q) one)) := by
  have hE : BMS.expand (M4z q) n = M1 q := by
    show (BMS.expand? (M4z q) n).getD [] = _
    rw [expand_M4z]; rfl
  have hp : predT (plus (zt q) one) = zt q := by
    rw [plus_zt_one q]
    show (if ((toList (add (zt q) one)).getLast? == some one) = true
          then ofList (toList (add (zt q) one)).dropLast else zero) = zt q
    rw [show toList (add (zt q) one) = [zt q, one] from rfl]
    rfl
  rw [hE, hp, o?_M1]



/-- The `blocksP` analogue of `Evidence.StageA.blocks0_append`: a new block starts
    exactly where a row-0-zero column starts. -/
theorem blocksP_append : ∀ (u v : List BMS.Col),
    (v = [] ∨ ∃ c t, v = c :: t ∧ Trans.Pair.r0 c = 0) →
      Trans.Pair.blocksP (u ++ v) = Trans.Pair.blocksP u ++ Trans.Pair.blocksP v
  | [], _, _ => rfl
  | [c], v, h => by
    rcases h with h | ⟨d, t, hv, hd⟩
    · subst h; rfl
    · subst hv
      show Trans.Pair.blocksP (c :: (d :: t)) = _
      rw [blocksP_cons_zero c d t hd]
      rfl
  | c :: d :: u', v, h => by
    have ih : Trans.Pair.blocksP (d :: (u' ++ v))
        = Trans.Pair.blocksP (d :: u') ++ Trans.Pair.blocksP v := blocksP_append (d :: u') v h
    by_cases hz : Trans.Pair.r0 d = 0
    · show Trans.Pair.blocksP (c :: (d :: (u' ++ v)))
          = Trans.Pair.blocksP (c :: (d :: u')) ++ Trans.Pair.blocksP v
      rw [blocksP_cons_zero c d (u' ++ v) hz, ih, blocksP_cons_zero c d u' hz]
      rfl
    · show Trans.Pair.blocksP (c :: (d :: (u' ++ v)))
          = Trans.Pair.blocksP (c :: (d :: u')) ++ Trans.Pair.blocksP v
      rw [blocksP_cons_nz c d (u' ++ v) hz, ih, blocksP_cons_nz c d u' hz]
      cases hL : Trans.Pair.blocksP (d :: u') with
      | nil => exact absurd hL (blocksP_ne_nil (by simp))
      | cons b1 rest => rfl

/-! ### F4, case B : `r = 0`, `b = 1` — `(0,0)(1,1)…(a,1)(1,0)` = `φ̄(0,φ̄(a,0))`

Here the last column's lowest nonzero row is row 0, so `t = 0` and EVERY ascension
amount vanishes: the expansion is the plain Stage-A-style "copy the bad part `n+1`
times", and the bad root is 0, so the copies are the whole ladder.  The value is
`φ̄(a,0)·(n+1)` and the fundamental sequence of the term is `φ̄(a,0)·n`, so this case
is a shift-1 EQUALITY family (the F1/F2 statement shape), not a 4-part package.
`a = 1` is `Rows.ProofsB.R2`. -/

theorem ent_app_lt (q : Nat) (col : BMS.Col) (x y : Nat) (h : x < q + 2) :
    BMS.ent (M1 q ++ [col]) x y = BMS.ent (M1 q) x y := by
  show (((M1 q ++ [col]).getD x []).getD y 0) = (((M1 q).getD x []).getD y 0)
  rw [getD_append_lt' _ _ x (by rw [len_M1]; omega)]

theorem ent_app_top (q : Nat) (col : BMS.Col) (y : Nat) :
    BMS.ent (M1 q ++ [col]) (q+2) y = col.getD y 0 := by
  show (((M1 q ++ [col]).getD (q+2) []).getD y 0) = col.getD y 0
  rw [getD_append_ge' _ _ (q+2) (by rw [len_M1]; omega), len_M1,
    show q + 2 - (q+2) = 0 from by omega]
  rfl

/-- Case B of the family: `(0,0)(1,1)…(a,1)(1,0)`. -/
def M4b (q : Nat) : Matrix := M1 q ++ [[1,0]]

theorem len_M4b (q : Nat) : (M4b q).length = q + 3 := by
  show ((M1 q) ++ [[1,0]]).length = q + 3
  rw [List.length_append, len_M1]
  rfl

theorem getLast_M4b (q : Nat) : (M4b q).getLast? = some ([1,0] : BMS.Col) :=
  List.getLast?_concat

theorem lnz_one_zero : BMS.lnz ([1,0] : BMS.Col) = some 0 := rfl

theorem ent_M4b_0 (q x : Nat) (h : x ≤ q+1) : BMS.ent (M4b q) x 0 = x := by
  rw [show BMS.ent (M4b q) x 0 = BMS.ent (M1 q ++ [[1,0]]) x 0 from rfl,
    ent_app_lt q [1,0] x 0 (by omega), ent_M1_0 q x h]

theorem ent_M4b_1_zero (q : Nat) : BMS.ent (M4b q) 0 1 = 0 := by
  rw [show BMS.ent (M4b q) 0 1 = BMS.ent (M1 q ++ [[1,0]]) 0 1 from rfl,
    ent_app_lt q [1,0] 0 1 (by omega), ent_M1_1_zero]

theorem ent_M4b_1 (q x : Nat) (h1 : 1 ≤ x) (h2 : x ≤ q+1) : BMS.ent (M4b q) x 1 = 1 := by
  rw [show BMS.ent (M4b q) x 1 = BMS.ent (M1 q ++ [[1,0]]) x 1 from rfl,
    ent_app_lt q [1,0] x 1 (by omega), ent_M1_1 q x h1 h2]

theorem ent_M4b_top0 (q : Nat) : BMS.ent (M4b q) (q+2) 0 = 1 := by
  rw [show BMS.ent (M4b q) (q+2) 0 = BMS.ent (M1 q ++ [[1,0]]) (q+2) 0 from rfl,
    ent_app_top q [1,0] 0]
  rfl

theorem parent0_M4b_top (q : Nat) : BMS.parent (M4b q) 0 (q+2) = some 0 := by
  show (((List.range (q+2)).filter
      (fun p => decide (BMS.ent (M4b q) p 0 < BMS.ent (M4b q) (q+2) 0))).max?) = some 0
  rw [Evidence.StageA.max?_filter_range, ent_M4b_top0]
  refine Evidence.StageA.lastSome_spec _ (q+2) 0 (by omega) ?_ ?_
  · rw [ent_M4b_0 q 0 (by omega)]
    exact decide_eq_true (by omega)
  · intro r hr1 hr2
    rw [ent_M4b_0 q r (by omega)]
    exact decide_eq_false (by omega)

theorem delta_M4b (q y : Nat) : BMS.delta (M4b q) 0 0 y = 0 := by
  show (if y < 0 then BMS.ent (M4b q) ((M4b q).length - 1) y - BMS.ent (M4b q) 0 y else 0) = 0
  rw [if_neg (by omega)]

/-- **The case-B expansion**: the whole ladder, copied `n+1` times. -/
theorem expand_M4b (q n : Nat) : BMS.expand? (M4b q) n = some (repM (M1 q) (n+1)) := by
  have hpar : BMS.parent (M4b q) 0 ((M4b q).length - 1) = some 0 := by
    rw [len_M4b, show q + 3 - 1 = q + 2 from by omega]
    exact parent0_M4b_top q
  have hlen1 : (M4b q).length - 1 - 0 = q + 2 := by rw [len_M4b]; omega
  have hbad : ∀ (c : Nat), (List.range (q+2)).map (fun x =>
      (List.range ([1,0] : BMS.Col).length).map (fun y => BMS.ent (M4b q) (0+x) y
        + c * BMS.delta (M4b q) 0 0 y
          * (if BMS.ascends (M4b q) 0 (0+x) y = true then 1 else 0)))
      = M1 q := by
    intro c
    have hinner : ∀ x ∈ List.range (q+2),
        (List.range ([1,0] : BMS.Col).length).map (fun y => BMS.ent (M4b q) (0+x) y
          + c * BMS.delta (M4b q) 0 0 y
            * (if BMS.ascends (M4b q) 0 (0+x) y = true then 1 else 0))
        = ([x, BMS.ent (M4b q) x 1] : BMS.Col) := by
      intro x hx
      have hx' : x < q+2 := List.mem_range.mp hx
      show [BMS.ent (M4b q) (0+x) 0 + c * BMS.delta (M4b q) 0 0 0
              * (if BMS.ascends (M4b q) 0 (0+x) 0 = true then 1 else 0),
            BMS.ent (M4b q) (0+x) 1 + c * BMS.delta (M4b q) 0 0 1
              * (if BMS.ascends (M4b q) 0 (0+x) 1 = true then 1 else 0)] = _
      rw [show (0:Nat)+x = x from by omega, delta_M4b q 0, delta_M4b q 1,
        ent_M4b_0 q x (by omega)]
      simp
    rw [List.map_congr_left hinner, List.range_succ_eq_map, List.map_cons, List.map_map]
    show ([0, BMS.ent (M4b q) 0 1] : BMS.Col) :: _ = ([0,0] : BMS.Col) :: ups 1 (q+1)
    rw [ent_M4b_1_zero, ups_range (q+1) 1]
    congr 1
    refine List.map_congr_left ?_
    intro i hi
    have hi' : i < q+1 := List.mem_range.mp hi
    show ([i+1, BMS.ent (M4b q) (i+1) 1] : BMS.Col) = ([1+i, 1] : BMS.Col)
    rw [ent_M4b_1 q (i+1) (by omega) (by omega), show i+1 = 1+i from by omega]
  simp only [BMS.expand?, getLast_M4b, Option.bind_eq_bind, Option.bind_some, lnz_one_zero, hpar,
    Option.pure_def, hlen1]
  rw [List.map_congr_left (fun c _ => hbad c), flat_range]
  rfl

/-! #### the value of the case-B expansion -/

theorem blocksP_repM_M1 : ∀ (q m : Nat),
    Trans.Pair.blocksP (repM (M1 q) m) = List.replicate m (M1 q)
  | _, 0 => rfl
  | q, m + 1 => by
    have ht : ∀ c ∈ ups 1 (q+1), Trans.Pair.r0 c ≠ 0 := r0_ups (q+1) 1 (by omega)
    show Trans.Pair.blocksP (M1 q ++ repM (M1 q) m) = _
    rw [blocksP_append (M1 q) (repM (M1 q) m) (by
        cases m with
        | zero => exact Or.inl rfl
        | succ j => exact Or.inr ⟨[0,0], (ups 1 (q+1) ++ repM (M1 q) j), rfl, rfl⟩),
      show Trans.Pair.blocksP (M1 q) = [M1 q] from blocksP_single [0,0] _ ht,
      blocksP_repM_M1 q m]
    rfl

theorem zsF_M1 (q g k : Nat) (hg : q + 1 ≤ g) (acc : Term) :
    zsF g k acc (M1 q) = plus acc (zt q) := by
  have ht : ∀ c ∈ ups 1 (q+1), Trans.Pair.r0 c ≠ 0 := r0_ups (q+1) 1 (by omega)
  show plus acc (omegaNF (Trans.Pair.oLAux g 1 (Trans.Pair.decP (ups 1 (q+1))))) = _
  rw [decP_ups (q+1) 0, oLAux_ups q 1 g hg,
    show chainP 1 q (phi (ofNat (1+q)) zero) = zt q from by
      rw [show (1:Nat)+q = q+1 from by omega]
      exact chainP_collapse q 1 (q+1) zero (by omega),
    show omegaNF (zt q) = zt q from omegaNF_phi_ne_zero (ofNat_ne_zero q)]

theorem foldl_repM_M1 (q g k : Nat) (hg : q + 1 ≤ g) : ∀ (m i : Nat),
    (List.replicate m (M1 q)).foldl (zsF g k) (mulNat (zt q) i) = mulNat (zt q) (i + m)
  | 0, i => by rw [List.replicate_zero, List.foldl_nil, Nat.add_zero]
  | m + 1, i => by
    rw [List.replicate_succ, List.foldl_cons, zsF_M1 q g k hg,
      plus_mulNat (show (zt q).isAP = true from rfl) i, foldl_repM_M1 q g k hg m (i+1)]
    congr 1
    omega

theorem oLAux_repM_M1 (q m fuel k : Nat) (hf : q + 2 ≤ fuel) :
    Trans.Pair.oLAux fuel k (repM (M1 q) m) = mulNat (zt q) m := by
  cases fuel with
  | zero => omega
  | succ g =>
    rw [oLAux_cons', blocksP_repM_M1 q m]
    have h := foldl_repM_M1 q g k (by omega) m 0
    rw [show mulNat (zt q) 0 = zero from rfl] at h
    rw [h]
    congr 1
    omega

/-! #### the term, its fundamental sequence, and the package -/

/-- The term of case B: `φ̄(0, φ̄(a,0))` (= `ω^(φ̄(a,0)+1)`). -/
def t4b (q : Nat) : Term := phi zero (zt q)

theorem splitFin_phi_ne_one {x y : Term} (h : ((phi x y : Term) == one) = false) :
    splitFin (phi x y) = (phi x y, 0) := by
  simp [splitFin, toList, ofList, h]

theorem phiShifted_zero_zt (q : Nat) : phiShifted zero (zt q) = true := by
  show (isFP zero (splitFin (phi (ofNat (q+1)) zero)).1
        || (((phi (ofNat (q+1)) zero : Term) == zero) && (zero : Term).isSC)) = true
  rw [splitFin_phi_ne_one (zt_bne_one q)]
  show ((((phi (ofNat (q+1)) zero : Term).isSC && lt zero (phi (ofNat (q+1)) zero))
        || lt zero (ofNat (q+1))) || _) = true
  rw [show lt zero (ofNat (q+1)) = true from lt_zero_ne (ofNat_ne_zero q)]
  simp

theorem fs_t4b (q k : Nat) : fsN (t4b q) k = mulNat (zt q) k := by
  show fsN (phi zero (zt q)) k = _
  rw [fsN]
  simp only [phiShifted_zero_zt q, Bool.true_or, if_true]
  show mulNat (omegaNF (zt q)) k = mulNat (zt q) k
  rw [show omegaNF (zt q) = zt q from omegaNF_phi_ne_zero (ofNat_ne_zero q)]

theorem onlyRow0_repM_M1 (q n : Nat) : onlyRow0 (repM (M1 q) (n+1)) = false := by
  show onlyRow0 (M1 q ++ repM (M1 q) n) = false
  rw [onlyRow0_append, onlyRow0_M1 q]
  rfl

theorem inFrag_repM_M1 : ∀ (q m : Nat), Trans.Pair.inFrag (repM (M1 q) m) = true
  | _, 0 => rfl
  | q, m + 1 => by
    show Trans.Pair.inFrag (M1 q ++ repM (M1 q) m) = true
    rw [inFrag_append, show Trans.Pair.inFrag (M1 q) = true from inFrag_lad (q+1) 0,
      inFrag_repM_M1 q m]
    rfl

theorem len_repM_M1 : ∀ (q m : Nat), (repM (M1 q) m).length = (q+2) * m
  | _, 0 => rfl
  | q, m + 1 => by
    show (M1 q ++ repM (M1 q) m).length = (q+2) * (m+1)
    rw [List.length_append, len_M1, len_repM_M1 q m, Nat.mul_succ]
    omega

/-- **E3 for case B**, as an equality at the repository shift. -/
theorem e3_val4b (q n : Nat) : o? (BMS.expand (M4b q) n) = some (fsN (t4b q) (n+1)) := by
  have hE : BMS.expand (M4b q) n = repM (M1 q) (n+1) := by
    show (BMS.expand? (M4b q) n).getD [] = _
    rw [expand_M4b]; rfl
  rw [hE, o?_pair (onlyRow0_repM_M1 q n) (inFrag_repM_M1 q (n+1)), len_repM_M1,
    oLAux_repM_M1 q (n+1) _ 1 (by
      have : (q+2) * 1 ≤ (q+2) * (n+1) := Nat.mul_le_mul_left (q+2) (by omega)
      omega),
    fs_t4b]

/-! #### the order facts of case B -/

theorem deg_mulNat_zt (q : Nat) : ∀ k, k ≤ (mulNat (zt q) k).deg
  | 0 => by show (0:Nat) ≤ 1; omega
  | 1 => by
    rw [mulNat_one_eq]
    show (1:Nat) ≤ 1 + (ofNat (q+1)).deg + (zero : Term).deg
    omega
  | k + 2 => by
    rw [mulNat_succ2]
    show k + 2 ≤ 1 + (1 + (ofNat (q+1)).deg + (zero : Term).deg) + (mulNat (zt q) (k+1)).deg
    have := deg_mulNat_zt q (k+1)
    omega

theorem ltF_zt_t4b (q : Nat) : ∀ f, 1 ≤ f → ltF f (zt q) (t4b q) = true := by
  intro f hf
  cases f with
  | zero => omega
  | succ g =>
    show ltF (g+1) (phi (ofNat (q+1)) zero) (phi zero (zt q)) = true
    exact ltF_phi_eq (show ((ofNat (q+1) : Term) == zero) = false from by
        simpa using ofNat_ne_zero q)
      (ltF_lt_zero g (ofNat (q+1)))
      (show ((phi (ofNat (q+1)) zero : Term) == zt q) = true from beq_self_eq_true _)

theorem ltF_mulNat_zt_t4b (q : Nat) : ∀ (k f : Nat), 2 ≤ f →
    ltF f (mulNat (zt q) k) (t4b q) = true
  | 0, f, hf => ltF_zero (by omega) (by intro hc; exact Term.noConfusion hc)
  | 1, f, hf => by
    rw [mulNat_one_eq]
    exact ltF_zt_t4b q f (by omega)
  | k + 2, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      rw [mulNat_succ2]
      show (if ((add (zt q) (mulNat (zt q) (k+1)) : Term) == t4b q) = true then false
            else ltF g (zt q) (t4b q)) = true
      simp only [show ((add (zt q) (mulNat (zt q) (k+1)) : Term) == t4b q) = false from rfl,
        Bool.false_eq_true, if_false]
      exact ltF_zt_t4b q g (by omega)

theorem ltF_mulNat_zt_succ (q : Nat) : ∀ (k f : Nat), k + 2 ≤ f →
    ltF f (mulNat (zt q) (k+1)) (mulNat (zt q) (k+2)) = true
  | 0, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      rw [mulNat_one_eq, mulNat_succ2, mulNat_one_eq]
      show (if ((zt q : Term) == add (zt q) (zt q)) = true then false
            else ((zt q : Term) == zt q) || ltF g (zt q) (zt q)) = true
      simp only [show ((zt q : Term) == add (zt q) (zt q)) = false from rfl,
        Bool.false_eq_true, if_false, beq_self_eq_true, Bool.true_or]
  | k + 1, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      have ih := ltF_mulNat_zt_succ q k g (by omega)
      rw [mulNat_succ2, mulNat_succ2]
      show (if ((add (zt q) (mulNat (zt q) (k+1)) : Term)
              == add (zt q) (mulNat (zt q) (k+2))) = true then false
            else if ((zt q : Term) == zt q) = true then
              ltF g (mulNat (zt q) (k+1)) (mulNat (zt q) (k+2))
            else ltF g (zt q) (zt q)) = true
      rw [show (((add (zt q) (mulNat (zt q) (k+1)) : Term)
          == add (zt q) (mulNat (zt q) (k+2))) = false) from by simp [ne_of_ltF ih]]
      simp [ih]

theorem e3_lt4b (q n : Nat) : lt (fsN (t4b q) (n+1)) (t4b q) = true := by
  rw [fs_t4b]
  refine lt_of_ltF (N := 2) (fun f hf => ltF_mulNat_zt_t4b q (n+1) f hf) ?_
  show 2 ≤ 2 * ((mulNat (zt q) (n+1)).deg + (t4b q).deg) + 8
  omega

/-- **(b)** with witness `k := n+2`. -/
theorem e3_over4b (q n : Nat) : lt (fsN (t4b q) (n+1)) (fsN (t4b q) (n+2)) = true := by
  rw [fs_t4b, fs_t4b]
  refine lt_of_ltF (N := n+2) (fun f hf => ltF_mulNat_zt_succ q n f hf) ?_
  have h1 := deg_mulNat_zt q (n+1)
  show n + 2 ≤ 2 * ((mulNat (zt q) (n+1)).deg + (mulNat (zt q) (n+2)).deg) + 8
  omega

/-- The closed form of the n-th expansion: the fundamental sequence at n+1 (shift +1). -/
def oval4b (q n : Nat) : Term := fsN (t4b q) (n+1)

/-- **E3 for the F4 case-B family**, for every `a = q+1 ≥ 1`:
    `(0,0)(1,1)…(a,1)(1,0) = φ̄(0,φ̄(a,0))`. -/
theorem e3_F4bfamily (q : Nat) :
    (∀ n, o? (BMS.expand (M4b q) n) = some (oval4b q n))
    ∧ (∀ n, lt (oval4b q n) (t4b q) = true)
    ∧ (∀ n, lt (oval4b q n) (fsN (t4b q) (n + 2)) = true)
    ∧ (∀ k, lt (fsN (t4b q) (k + 1)) (oval4b q (k + 1)) = true) :=
  ⟨e3_val4b q, e3_lt4b q, e3_over4b q, fun k => e3_over4b q k⟩

/-! #### R2 is the instance `a = 1` -/

theorem m4b_zero : M4b 0 = Rows.ProofsB.R2.m0 := rfl
theorem t4b_zero : t4b 0 = Rows.ProofsB.R2.t0 := rfl

example (n : Nat) : o? (BMS.expand Rows.ProofsB.R2.m0 n)
    = some (fsN Rows.ProofsB.R2.t0 (n+1)) := e3_val4b 0 n

/-- Beyond the table: `a = 2`, i.e. `(0,0)(1,1)(2,1)(1,0) = φ̄(0,ζ₀)`. -/
example (n : Nat) : o? (BMS.expand [[0,0],[1,1],[2,1],[1,0]] n)
    = some (fsN (phi zero (phi (ofNat 2) zero)) (n+1)) := e3_val4b 1 n

#guard (List.range 4).all fun q => (List.range 4).all fun n =>
  Trans.o? (BMS.expand (M4b q) n) == some (fsN (t4b q) (n+1))
#guard (List.range 5).all fun q => Trans.o? (M4b q) == some (t4b q)

/-! ### What is still missing for F4 (the value side)

`r = 1`, `1 ≤ b < a` (the new limit case).  `expand_M4` above gives the BMS side.
The value, measured for `a ≤ 4` and `n ≤ 3`, is EXACTLY the §7 development with the
tower level `q` replaced by `k = b-1` and the SAME base `zt q = φ̄(a,0)`:

    oval 0 = φ̄(a,0),  oval (n+1) = the φ_k-tower over `φ̄(k, xb)`,
    xb = φ̄(a,0)·2  (k = 0),   ω^(φ̄(a,0)·2)  (k ≥ 1)

so F3 is the instance `k = q`, and `xbase`/`bse`/`twr` generalize by adding the level
as a parameter.  The fundamental sequence is the same tower over `φ̄(k, φ̄(a,0))` —
§7's `sbse q` is again the `k = q` instance — so `fs_t3` generalizes verbatim; only
the TERM differs (`φ̄(b, φ̄(a,0))` for `b < a` against `φ̄(a,1)` for `b = a`), and its
`fsN` goes through the `phiShifted = true` branch, unlike `t3`.

What is genuinely new, and the reason this case is not finished here: `oLAux_chainV`
(§6) requires the `frep` offset to equal the length of the `ups` prefix minus one.
With step `b < q+1` the descending `(0,1)`-chain runs out of `frep` offset BEFORE it
runs out of `ups` columns — after `b-1` steps the state is `ups 0 (q-b+2) ++ frep … 0 m`
with `q-b+2 ≥ 2`, not `(0,1) :: frep … 0 m` — so the leading block is no longer a
single column and `oLAux_chainV`/`valV3` need a real generalization in the step, not a
re-instantiation.

`r = 0`, `2 ≤ b ≤ a`.  (`b = 1` is DONE — case B above; `b = a+1` is F2, §2–§3; `b = 0`
is the successor case above.)  Here the last column's lowest nonzero row is row 0, so
`t = 0` and EVERY ascension amount vanishes: the expansion is the plain Stage-A-style
"copy the bad part `n+1` times", with bad root `b-1`, good part `(M1 q).take (b-1)` and
bad part the ladder columns `b-1 … a` — the case-B proof is the `b = 1` instance of
exactly that, where the good part is empty and the bad part is the whole ladder, so
`expand_M4b` generalizes by carrying `b`.  Measured values for `2 ≤ b ≤ a`:
`φ̄(b-1, φ̄(0,φ̄(a,0)))`, i.e. one `φ̄(b-1,·)` layer over the case-B term. -/

-- §10 checks
#guard (List.range 4).all fun q => (List.range 4).all fun i =>
  (List.range 3).all fun n =>
    !(decide (i + 1 ≤ q + 2))
      || (BMS.expand? (M4 q (i+1)) n == some (frep (lad (q+1)) (i+1) 0 (n+1)))
#guard (List.range 5).all fun q => Trans.o? (M1 q) == some (zt q)
#guard (List.range 5).all fun q => Trans.o? (M4z q) == some (plus (zt q) one)
#guard (List.range 4).all fun q => (List.range 4).all fun n =>
  Trans.o? (BMS.expand (M4z q) n) == some (zt q)
#guard (List.range 4).all fun q => M4 q (q+1) == M3 q && M4 q (q+2) == M1 (q+1)

end Evidence.StageB
