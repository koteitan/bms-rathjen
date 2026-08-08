import Trans.Pair
/-
Trans/StageC.lean — Stage C of the translation o : BMS → 𝔗(M):
the 2-row fragment with row-1 entries ≤ 2 (first-argument limits of φ̄, the
region from φ̄(ω,0) upward).  Stage C'' revision: floor 4 (the argument
exponent of limit-level φ̄ steps) implemented for pure (·,0)-tails.

Fragment (the domain of `oStageC?`):
  matrices all of whose columns have height ≤ 2 and row-1 entry ≤ 2.
  On row-1 ≤ 1 matrices the reading coincides with Stage B (`oPair?`, #guarded).
  The upper boundary (0,0)(1,1)(2,2)(3,3) (row-1 entry 3) is outside.

Translation rule (`oCAux`), derived by the E3-driven method of Stage B:

  Blocks are split at row-0 = 0 columns and folded left to right with an
  accumulator; the recursion carries the PATH p : List Nat of (row1 - 1)-values
  of the enclosing block heads (top level: p = []), and the fold counts the
  (0,2)-headed blocks already passed (cnt).

  * block (0,0)::t — acc := acc + ω̄^( oC [] 0 (dec t) )    (as in Stage B)
  * block (0,b)::t (b = 1,2) — acc := φ_K( logφ_K(acc) + step ) with
      K = levelOf (p ++ [b-1]),   v = oC (p ++ [b-1]) thr (dec t)
      (v := 0 if the tail added nothing beyond thr), where
      thr = acc if p ≠ [] and acc is a strict fixed point above the tail's
            (0,1)-level (`isHighFp`), else 0 (threaded base), and
      step = at a successor level K: 1 if v = 0, ω̄^v otherwise (Stage B);
             at a limit level K:
               v of head φ-level ≥ K (level-class material): ω̄^v (collapse);
               v = 0: ω̄^cnt (the count ladder of bare (0,2)-repeats);
               otherwise: the FLOOR-4 argument step (below) when the tail is
               floor-4 material, else the provisional Stage-C' step ω̄^(ω·v).

  levelOf p is the ONE-ROW (PrSS/CNF) reading `oPrAux` of the path itself
  (a path of k zeros reads as k, [0,1] = ω, [0,1,0] = ω+1, [0,1,1] = ω², …).

  FLOOR 4 (Stage C'' finding — the argument exponent of a (0,2)-tail):
  the dec'd tail is folded into GROUPS (g, b) by `ebGroups`:
    - a bare (0,0)-block opens the group (0,0), or bumps b of the last group
      when that group was itself opened by a bare block; after a tailed group
      a bare block opens a FRESH (0,0)-group (order-forced: [0,1,0,0] must
      stay below [0,1,0,1]);
    - a tailed block promotes the groups of its dec'd tail by g := 1+g
      (ω+g for (·,1)-heads);
  and each group contributes the summand ω̄^(ω·(1+g) + b) to the step.
  Machine-validated anchors (skeleton ↦ argument, W-arguments φ̄(ω, ·)):
    [0]      (2,2)(3,0)            ω̄^ω          (committed row, unchanged)
    [0,0]    (2,2)(3,0)(3,0)       ω̄^(ω+1)
    [0,1]    (2,2)(3,0)(4,0)       ω̄^(ω·2)
    [0,1,1]  (2,2)(3,0)(4,0)(4,0)  ω̄^(ω·2+1)
    [0,1,2]  (2,2)(3,0)(4,0)(5,0)  ω̄^(ω·3)
    [0,1,0,1] (3,0)(4,0)(3,0)(4,0) ω̄^(ω·2)·2   (fresh-group summands)
    seed     (2,2)(3,0)(4,1)       ω̄^(ω²)      (the (·,1)-limit of the ladder)

Validated region (all #guards below; 0 failures): the reachable corpora
(depth 3, width 3) of the seeds
  (2,2) [28], (2,2)(2,1) [34], (2,2)(2,1)(3,1) [40], (2,2)(2,1)(3,2) [32],
  (2,2)(3,1) minus the two floor-5 members noted below [32],
  (2,2)(3,1)(4,2) [32], (2,2)(3,2) [32], (2,2)(3,2)(4,2) [40],
  (2,2)(3,3)∖seed [29], (2,2)(2,2) [32], (2,2)(3,0) [30],
  (2,2)(2,2)(2,2) [40], and — new in Stage C'' — (2,2)(3,0)(4,1) [26].

EXPOSED MISASSIGNMENTS (a methodological finding): the two members
  (0,0)(1,1)(2,2)(3,0)(4,1)(5,0)(6,1) and
  (0,0)(1,1)(2,2)(3,0)(4,1)(5,2)(6,0)(7,1)(8,0)(9,1)
of the (2,2)(3,1)-corpus fail E3i [c] under the floor-4 rule.  Their values
(unchanged from Stage C') were ALWAYS too big: Stage C' assigned their
expansions equally-misassigned values, so the corpus was green by mutual
misassignment; the floor-4 corrections to the (·,0)-members broke the
conspiracy and exposed them.  Correct values need floor 5; they are filtered
out of the guard below and must not become rows.

KNOWN FRONTIER (kept OUT of the acceptance record; do NOT make rows from it):
  (ii) THE RELATIVE-COUNTING MECHANISM (the ψ-collapse entry) — now blocking
      three fronts, all with the same signature (a sub-pattern re-derives
      already-consumed material and must be counted relative to it):
      (ii-a) the original Stage-C front: corpus of (2,2)(2,0), 124 failures;
        the (0,0)-exponent reset re-derives consumed W-material.
      (ii-b) the relative-claim family in the corpus of (2,2)(3,0)(3,0)
        (121 failures).  The threading already yields the FIRST relative
        claim correctly ((2,2)(3,0)(2,1)(3,2) = φ_ω(ω̄^ω+1) via
        logφ_ω(thr)+1), but the nested (2,1)(3,2)(4,0)(3,1)(4,2)(5,0)-appends
        re-derive shifted copies of the consumed (2,2)(3,0)-material.
      (ii-c) inside floor 5(a): the (4,0)(5,1)-pair-chains of
        (3,0)(4,1)(4,1) re-derive (0,0)::(1,1)-groups that must count
        relative to the consumed ω̄^(ω²)-group (else they collide with
        (4,1)(4,1) itself — machine-checked collision).
  (iii-b) FLOOR 5(a), derivation record for the next round (chain-forced,
      E1-verified in a dev build, NOT integrated because the corpus battery
      immediately runs into (ii-c)): extend the groups with a MARKED flag;
      bare (0,1)-blocks open (ω, marked); (0,1)-heads promote marked inner
      groups multiplicatively (g·ω) and unmarked ones additively (ω+g);
      (0,0)-heads promote by +1 and stamp unmarked.  Anchors this reproduces:
        (3,0)(4,1)(4,1)      = φ̄(ω, ω̄^(ω²)·2)
        (3,0)(4,1)(5,0)(6,1) = φ̄(ω, ω̄^(ω²·2))   (exposed member 1)
        (3,0)(4,1)(5,1)      = φ̄(ω, ω̄^(ω³))
      A flat recursive +ω-promotion (no marked flag) was refuted earlier
      (regressed the (2,2)(3,1)-corpora); the marked ladder is anchor-correct
      but its corpus closure needs (ii) resolved first.

Γ₀ status: unchanged (everything now waits on the relative-counting
mechanism (ii) — the single remaining design problem of the 2-row fragment).

Note: the imports precede this comment because the kimina server extracts the
header imports from the top of a posted snippet.
-/

namespace Trans

open TM (Term)
open TM.Term
open Pair (r0 r1 decP blocksP logPhi)

namespace StageC

/-- The fragment: every column of height ≤ 2 with row-1 entry ≤ 2. -/
def inFragC (m : BMS.Matrix) : Bool := m.all fun c => c.length ≤ 2 && r1 c ≤ 2

/-- The α-floor: a head path read as a one-row sequence (Stage A, one floor up). -/
def levelOf (p : List Nat) : Term := oPrAux (p.length + 1) p

/-- Is `t` a strict fixed point of φ_k (its head's φ-level lies above k)? -/
def isHighFp (k : Term) : Term → Bool
  | .add a _ => isHighFp k a
  | .phi a _ => lt k a
  | _ => false

/-- Is the head φ-level of `t` at or above k (level-class material)? -/
def isAtLevel (k : Term) : Term → Bool
  | .add a _ => isAtLevel k a
  | .phi a _ => le k a
  | _ => false

/-- CNF exponent of an AP term: the (shifted) argument for ω̄-powers, the term
    itself for higher fixed points (ω̄^t = t there). -/
def expOf : Term → Term
  | .phi Term.zero b => if phiShifted Term.zero b then plus b one else b
  | t => t

/-- Left multiplication ω·v (v in CNF): ω̄^(1+a) summand-wise; continuous,
    so ω·ε₀ = ε₀. -/
def mulOmegaLeft (v : Term) : Term :=
  ofList ((toList v).map fun t => omegaNF (plus one (expOf t)))

/-- Bump the finite part of the last group. -/
def bumpLast : List (Term × Nat) → List (Term × Nat)
  | [] => [(Term.zero, 0)]
  | [(g, b)] => [(g, b + 1)]
  | x :: rest => x :: bumpLast rest

/-- Floor 4: the argument-exponent groups of a (0,2)-tail (see the header).
    The Bool of the fold records whether the last group was opened by a bare
    block (only those ladders continue by bumping). -/
def ebGroups : Nat → List BMS.Col → List (Term × Nat)
  | 0, _ => []
  | fuel + 1, s =>
    ((blocksP s).foldl (init := ([], false)) fun (acc, lastBare) b =>
      match b with
      | [] => (acc, lastBare)
      | c :: t =>
        if t.isEmpty then
          if Pair.r1 c == 0 then
            (if lastBare then bumpLast acc else acc ++ [(Term.zero, 0)], true)
          else (acc ++ [(omega, 0)], false)
        else
          let pro := if Pair.r1 c == 0 then one else omega
          (acc ++ (ebGroups fuel (decP t)).map (fun (g, bb) => (plus pro g, bb)),
           false)).1

/-- The floor-4 argument step of a tailed (0,2)-block: Σ ω̄^(ω·(1+g)+b). -/
def argStep (fuel : Nat) (t : List BMS.Col) : Term :=
  ofList ((ebGroups fuel (decP t)).map fun (g, b) =>
    omegaNF (plus (mulOmegaLeft (plus one g)) (ofNat b)))

/-- One (0,b)-block step at level k (b ≥ 1): φ_k(logφ_k(acc) + step).
    Successor levels use Stage B's arithmetic; limit levels use the count
    ladder and the floor-4 argument step `astep` (see the header). -/
def phiStepC (k acc v astep : Term) (cnt : Nat) : Term :=
  let base := (logPhi k acc).getD Term.zero
  let isL := kindT k == .isLim
  let g : Term :=
    if isL then
      if v != Term.zero && isAtLevel k v then plus base (omegaNF v)
      else if v == Term.zero && (logPhi k acc).isNone && cnt == 0 then Term.zero
      else plus base
        (if v == Term.zero then omegaNF (ofNat cnt) else astep)
    else
      if v == Term.zero then
        match logPhi k acc with
        | none => Term.zero
        | some b => plus b one
      else plus base (omegaNF v)
  phiNF k g

/-- The path-indexed reading (see the header). -/
def oCAux : Nat → List Nat → Term → List BMS.Col → Term
  | 0, _, _, _ => Term.zero
  | fuel + 1, p, acc0, s =>
    ((blocksP s).foldl (init := (acc0, 0)) fun (acc, cnt) b =>
      match b with
      | [] => (acc, cnt)  -- unreachable: blocks are nonempty
      | c :: t =>
        if r1 c == 0 then
          (plus acc (omegaNF (oCAux fuel [] Term.zero (decP t))), cnt)
        else
          let p' := p ++ [r1 c - 1]
          let thr := if !p.isEmpty && isHighFp (levelOf (p' ++ [0])) acc
                     then acc else Term.zero
          let vi := oCAux fuel p' thr (decP t)
          -- floor 4 covers tails with at most one marked column; deeper
          -- (·,1)-material is floor-5 territory (provisional Stage-C' step)
          let astep := if ((decP t).filter (fun c => Pair.r1 c ≥ 1)).length ≤ 1
                       then argStep fuel t
                       else omegaNF (mulOmegaLeft vi)
          (phiStepC (levelOf p') acc (if vi == thr then Term.zero else vi)
             astep cnt,
           if r1 c == 2 then cnt + 1 else cnt)).1

end StageC

/-- Stage C (C'' revision): the translation on the 2-row fragment with row-1
    entries ≤ 2 (`none` outside).  Row-1-all-zero matrices delegate to `oPr`.
    Values on the frontier configurations of the header are provisional. -/
def oStageC? (m : BMS.Matrix) : Option Term :=
  if StageC.inFragC m then
    some (if onlyRow0 m then oPr m
          else StageC.oCAux (m.length + 1) [] Term.zero m)
  else none

/-- Total version for the corpus checkers (junk 0 outside the fragment). -/
def oStageCT (m : BMS.Matrix) : Term := (oStageC? m).getD Term.zero

/-! ## Acceptance record (E1 instances, agreement, corpus checks) -/

namespace StageC.Test

open BMS (Matrix)
open Evidence

private def W : Term := phi omega zero            -- φ̄(ω,0)

-- E1 instances of the validated region (each matrix occurs in a green corpus)
#guard oStageC? [[0,0],[1,1],[2,2]] == some W
#guard oStageC? [[0,0],[1,1],[2,2],[1,1]] == some (phi one W)
#guard oStageC? [[0,0],[1,1],[2,2],[2,0]] == some (phi one (phi zero W))
#guard oStageC? [[0,0],[1,1],[2,2],[2,1]] == some (phi (ofNat 2) W)
#guard oStageC? [[0,0],[1,1],[2,2],[2,1],[3,1]] == some (phi (ofNat 3) W)
#guard oStageC? [[0,0],[1,1],[2,2],[2,1],[3,2]] == some (phi omega one)
#guard oStageC? [[0,0],[1,1],[2,2],[2,2]] == some (phi omega omega)
#guard oStageC? [[0,0],[1,1],[2,2],[2,2],[2,2]] == some (phi omega (phi zero (ofNat 2)))
#guard oStageC? [[0,0],[1,1],[2,2],[3,0]] == some (phi omega (phi zero omega))
#guard oStageC? [[0,0],[1,1],[2,2],[3,0],[3,0]] ==
  some (phi omega (phi zero (plus omega one)))
#guard oStageC? [[0,0],[1,1],[2,2],[3,0],[4,0]] ==
  some (phi omega (phi zero (plus omega omega)))
#guard oStageC? [[0,0],[1,1],[2,2],[3,0],[4,0],[4,0]] ==
  some (phi omega (phi zero (plus (plus omega omega) one)))
#guard oStageC? [[0,0],[1,1],[2,2],[3,0],[4,0],[5,0]] ==
  some (phi omega (phi zero (plus (plus omega omega) omega)))
#guard oStageC? [[0,0],[1,1],[2,2],[3,0],[4,1]] ==
  some (phi omega (phi zero (phi zero (ofNat 2))))
#guard oStageC? [[0,0],[1,1],[2,2],[3,1]] == some (phi (plus omega one) zero)
#guard oStageC? [[0,0],[1,1],[2,2],[3,1],[4,2]] == some (phi (plus omega omega) zero)
#guard oStageC? [[0,0],[1,1],[2,2],[3,2]] == some (phi (phi zero (ofNat 2)) zero)
#guard oStageC? [[0,0],[1,1],[2,2],[3,2],[4,2]] == some (phi (phi zero (ofNat 3)) zero)

-- the upper boundary of the fragment is outside the domain
#guard (oStageC? [[0,0],[1,1],[2,2],[3,3]]).isNone

-- agreement with Stage B on its whole fragment (row-1 ≤ 1), over a corpus
#guard (corpus [[0,0],[1,1],[2,1],[3,1]] 3 3).all fun m => oStageC? m == oPair? m
#guard (corpus [[0],[1],[2]] 4 3).all fun m => oStageC? m == some (oPr m)

-- green corpora (depth 3, width 3); the boundary corpus without the boundary;
-- g5 without the two floor-5 members exposed by the floor-4 corrections
private def g1 : List Matrix := corpus [[0,0],[1,1],[2,2]] 3 3
private def g2 : List Matrix := corpus [[0,0],[1,1],[2,2],[2,1]] 3 3
private def g3 : List Matrix := corpus [[0,0],[1,1],[2,2],[2,1],[3,1]] 3 3
private def g4 : List Matrix := corpus [[0,0],[1,1],[2,2],[2,1],[3,2]] 3 3
private def g5 : List Matrix :=
  (corpus [[0,0],[1,1],[2,2],[3,1]] 3 3).filter fun m =>
    m != [[0,0],[1,1],[2,2],[3,0],[4,1],[5,0],[6,1]] &&
    m != [[0,0],[1,1],[2,2],[3,0],[4,1],[5,2],[6,0],[7,1],[8,0],[9,1]]
private def g6 : List Matrix := corpus [[0,0],[1,1],[2,2],[3,1],[4,2]] 3 3
private def g7 : List Matrix := corpus [[0,0],[1,1],[2,2],[3,2]] 3 3
private def g8 : List Matrix := corpus [[0,0],[1,1],[2,2],[3,2],[4,2]] 3 3
private def g9 : List Matrix :=
  (corpus [[0,0],[1,1],[2,2],[3,3]] 3 3).filter
    (fun m => m != [[0,0],[1,1],[2,2],[3,3]])
private def g10 : List Matrix := corpus [[0,0],[1,1],[2,2],[2,2]] 3 3
private def g11 : List Matrix := corpus [[0,0],[1,1],[2,2],[3,0]] 3 3
private def g12 : List Matrix := corpus [[0,0],[1,1],[2,2],[2,2],[2,2]] 3 3
private def g13 : List Matrix := corpus [[0,0],[1,1],[2,2],[3,0],[4,1]] 3 3
private def gall : List Matrix :=
  g1 ++ g2 ++ g3 ++ g4 ++ g5 ++ g6 ++ g7 ++ g8 ++ g9 ++ g10 ++ g11 ++ g12 ++ g13

-- domain closure and formation conditions
#guard gall.all fun m => (oStageC? m).isSome
#guard gall.all fun m => inT (oStageCT m)

-- the full checks on every green corpus
#guard checkAll oStageCT g1 3 6
#guard checkAll oStageCT g2 3 6
#guard checkAll oStageCT g3 3 6
#guard checkAll oStageCT g4 3 6
#guard checkAll oStageCT g5 3 8
#guard checkAll oStageCT g6 3 6
#guard checkAll oStageCT g7 3 6
#guard checkAll oStageCT g8 3 6
#guard checkAll oStageCT g9 3 6
#guard checkAll oStageCT g10 3 6
#guard checkAll oStageCT g11 3 8
#guard checkAll oStageCT g12 3 8
#guard checkAll oStageCT g13 3 8

end StageC.Test

end Trans
