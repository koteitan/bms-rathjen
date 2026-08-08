import Trans.Pair
/-
Trans/StageC.lean — Stage C of the translation o : BMS → 𝔗(M):
into the 2-row fragment with row-1 entries ≤ 2 (first-argument limits of φ̄,
the region from φ̄(ω,0) upward), with an honestly documented frontier.

Fragment (the domain of `oStageC?`):
  matrices all of whose columns have height ≤ 2 and row-1 entry ≤ 2.
  On row-1 ≤ 1 matrices the reading coincides with Stage B (`oPair?`, #guarded).
  The upper boundary (0,0)(1,1)(2,2)(3,3) (row-1 entry 3) is outside; by the
  α-floor reading below it corresponds to φ̄(ω^ω, 0) (conjecture, see Findings).

Translation rule (`oCAux`), derived by the same E3-driven method as Stage B:

  Blocks are split at row-0 = 0 columns and folded left to right with an
  accumulator; the recursion carries the PATH p : List Nat of (row1 - 1)-values
  of the enclosing block heads (top level: p = []).

  * block (0,0)::t — acc := acc + ω̄^( oC [] 0 (dec t) )    (as in Stage B)
  * block (0,b)::t (b = 1,2) — acc := φ_K( logφ_K(acc) + step ) with
      K    = levelOf (p ++ [b-1]),
      v    = oC (p ++ [b-1]) thr (dec t),  v := 0 if the tail added nothing,
      step = 1 if v = 0, ω̄^v otherwise, and
      thr  = acc if p ≠ [] and acc is a strict fixed point above the tail's
             (0,1)-level (`isHighFp`), else 0 — the tail is then read on top of
             the inherited base (threading).

  levelOf p is the ONE-ROW (PrSS/CNF) reading `oPrAux` of the path itself: the
  first Veblen argument is the Stage-A translation of the head skeleton, one
  floor up.  This subsumes Stage B (a path of k zeros reads as k) and gives
    [0,1] = ω, [0,1,0] = ω+1, [0,1,0,1] = ω·2, [0,1,1] = ω², [0,1,1,1] = ω³.

  Sample values (each #guarded below AND corpus-validated, W := φ̄(ω,0)):
    (0,0)(1,1)(2,2)          = φ̄(ω,0) = W      (α-tower diagonal)
    (0,0)(1,1)(2,2)(1,1)     = φ̄(1,W)          (= ε_{W+1})
    (0,0)(1,1)(2,2)(2,0)     = φ̄(1,φ̄(0,W))    (= ε_{W·ω})
    (0,0)(1,1)(2,2)(2,1)     = φ̄(2,W)          (= φ₂(W+1))
    (0,0)(1,1)(2,2)(2,1)(3,1) = φ̄(3,W)
    (0,0)(1,1)(2,2)(2,1)(3,2) = φ̄(ω,1)
    (0,0)(1,1)(2,2)(3,0)     = φ̄(ω,ω)
    (0,0)(1,1)(2,2)(3,1)     = φ̄(ω+1,0)
    (0,0)(1,1)(2,2)(3,1)(4,2) = φ̄(ω·2,0)
    (0,0)(1,1)(2,2)(3,2)     = φ̄(ω²,0)
    (0,0)(1,1)(2,2)(3,2)(4,2) = φ̄(ω³,0)

Validated region (all #guards below; 0 failures):
  the reachable corpora (depth 3, width 3) of the seeds
    (0,0)(1,1)(2,2)                       [28]
    (0,0)(1,1)(2,2)(2,1)                  [34]
    (0,0)(1,1)(2,2)(2,1)(3,1)             [40]
    (0,0)(1,1)(2,2)(2,1)(3,2)             [32]
    (0,0)(1,1)(2,2)(3,1)                  [34]
    (0,0)(1,1)(2,2)(3,1)(4,2)             [32]
    (0,0)(1,1)(2,2)(3,2)                  [32]
    (0,0)(1,1)(2,2)(3,2)(4,2)             [40]
    (0,0)(1,1)(2,2)(3,3) minus the seed   [29]
  under checkKind/checkSucc/checkE2/checkE3i, plus (dev record, not in the
  guards) the depth-4 corpora of (2,2), (2,2)(3,2) and (2,2)(3,3)∖seed
  (62/85/76 matrices), all with 0 failures.

KNOWN FRONTIER (defective, kept OUT of the acceptance record; values there are
provisional — do NOT add table rows from it):
  (i) a (0,2)-headed block following a nonzero accumulator of its own fold —
      the "(2,2)(2,2)-repeat".  oCAux gives (0,0)(1,1)(2,2)(2,2) = φ̄(ω,1),
      which collides with (0,0)(1,1)(2,2)(2,1)(3,2) (checkE2 fails in the
      corpus of (2,2)(2,2); 22 failures).  The expansion sups suggest the
      repeat step at a limit level is larger than +1 (φ̄(ω,ω)-like), but a
      plain limit-step rule broke the validated (2,2)(3,0)-family, so the
      correct rule is still open.
  (ii) at the top-level fold (p = []), a (0,1)-block with nonempty tail whose
      dec-tail starts with a (0,1)-head, following a φ_ω-class accumulator —
      e.g. (0,0)(1,1)(2,2)(1,1)(2,1) (corpus of (2,2)(2,0): 124 failures).
      Here the un-threaded reading is too small, but threading breaks the
      validated [C_ω][C_ω]-chains: the same dichotomy as (i), one floor down.
  Both families are exactly the configurations where an inherited accumulator
  and a same-or-lower-level tail compete; resolving them is the entry ticket
  to the ψ-region and is left to Stage C'.

Findings on Γ₀ (= ψ_Ω(0), the mission's item 2):
  Γ₀ is NOT below (0,0)(1,1)(2,2)(3,3).  The α-floor of a 2-row matrix is the
  one-row PrSS of its (row1-1)-skeleton, so first arguments below the boundary
  stay below ω^ω ((3,3)-corpus validation above), and more generally 2-row
  α-floors read below ε₀.  The candidates (2,2)(2,2) and (2,2)(3,2) proposed
  in the mission are φ̄(ω,1)-provisional and φ̄(ω²,0)-validated respectively —
  both far below Γ₀.  ψ enters only after the frontier (i)/(ii) is resolved.

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

/-- One (0,b)-block step at level k (b ≥ 1): φ_k(logφ_k(acc) + step),
    step = 1 for an empty tail and ω̄^v otherwise (Stage B's `phiStep`,
    shared here so the two stages provably agree on the common fragment). -/
def phiStepC (k acc v : Term) : Term :=
  let g : Term :=
    if v == Term.zero then
      match logPhi k acc with
      | none => Term.zero
      | some b => plus b one
    else plus ((logPhi k acc).getD Term.zero) (omegaNF v)
  phiNF k g

/-- The path-indexed reading (see the header). -/
def oCAux : Nat → List Nat → Term → List BMS.Col → Term
  | 0, _, _, _ => Term.zero
  | fuel + 1, p, acc0, s =>
    (blocksP s).foldl (init := acc0) fun acc b =>
      match b with
      | [] => acc  -- unreachable: blocks are nonempty
      | c :: t =>
        if r1 c == 0 then
          plus acc (omegaNF (oCAux fuel [] Term.zero (decP t)))
        else
          let p' := p ++ [r1 c - 1]
          let thr := if !p.isEmpty && isHighFp (levelOf (p' ++ [0])) acc
                     then acc else Term.zero
          let vi := oCAux fuel p' thr (decP t)
          phiStepC (levelOf p') acc (if vi == thr then Term.zero else vi)

end StageC

/-- Stage C: the translation on the 2-row fragment with row-1 entries ≤ 2
    (`none` outside).  Row-1-all-zero matrices delegate to `oPr`.  The values
    on the frontier configurations (i)/(ii) of the header are provisional. -/
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
#guard oStageC? [[0,0],[1,1],[2,2],[3,0]] == some (phi omega omega)
#guard oStageC? [[0,0],[1,1],[2,2],[3,1]] == some (phi (plus omega one) zero)
#guard oStageC? [[0,0],[1,1],[2,2],[3,1],[4,2]] == some (phi (plus omega omega) zero)
#guard oStageC? [[0,0],[1,1],[2,2],[3,2]] == some (phi (phi zero (ofNat 2)) zero)
#guard oStageC? [[0,0],[1,1],[2,2],[3,2],[4,2]] == some (phi (phi zero (ofNat 3)) zero)

-- the upper boundary of the fragment is outside the domain
#guard (oStageC? [[0,0],[1,1],[2,2],[3,3]]).isNone

-- agreement with Stage B on its whole fragment (row-1 ≤ 1), over a corpus
#guard (corpus [[0,0],[1,1],[2,1],[3,1]] 3 3).all fun m => oStageC? m == oPair? m
#guard (corpus [[0],[1],[2]] 4 3).all fun m => oStageC? m == some (oPr m)

-- green corpora (depth 3, width 3); the boundary corpus without the boundary
private def g1 : List Matrix := corpus [[0,0],[1,1],[2,2]] 3 3
private def g2 : List Matrix := corpus [[0,0],[1,1],[2,2],[2,1]] 3 3
private def g3 : List Matrix := corpus [[0,0],[1,1],[2,2],[2,1],[3,1]] 3 3
private def g4 : List Matrix := corpus [[0,0],[1,1],[2,2],[2,1],[3,2]] 3 3
private def g5 : List Matrix := corpus [[0,0],[1,1],[2,2],[3,1]] 3 3
private def g6 : List Matrix := corpus [[0,0],[1,1],[2,2],[3,1],[4,2]] 3 3
private def g7 : List Matrix := corpus [[0,0],[1,1],[2,2],[3,2]] 3 3
private def g8 : List Matrix := corpus [[0,0],[1,1],[2,2],[3,2],[4,2]] 3 3
private def g9 : List Matrix :=
  (corpus [[0,0],[1,1],[2,2],[3,3]] 3 3).filter
    (fun m => m != [[0,0],[1,1],[2,2],[3,3]])
private def gall : List Matrix := g1 ++ g2 ++ g3 ++ g4 ++ g5 ++ g6 ++ g7 ++ g8 ++ g9

-- domain closure and formation conditions
#guard gall.all fun m => (oStageC? m).isSome
#guard gall.all fun m => inT (oStageCT m)

-- the full checks on every green corpus
#guard checkAll oStageCT g1 3 6
#guard checkAll oStageCT g2 3 6
#guard checkAll oStageCT g3 3 6
#guard checkAll oStageCT g4 3 6
#guard checkAll oStageCT g5 3 6
#guard checkAll oStageCT g6 3 6
#guard checkAll oStageCT g7 3 6
#guard checkAll oStageCT g8 3 6
#guard checkAll oStageCT g9 3 6

end StageC.Test

end Trans
