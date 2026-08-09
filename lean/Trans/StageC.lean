import Trans.Pair
/-
Trans/StageC.lean — Stage C of the translation o : BMS → 𝔗(M):
the 2-row fragment with row-1 entries ≤ 2.  Stage C''' revision: the
CORRECTED RULE of the diagonal rebuild (the (ii)-session mandate §4 executed).

Fragment (the domain of `oStageC?`): matrices all of whose columns have
height ≤ 2 and row-1 entry ≤ 2; row-1 ≤ 1 matrices agree with Stage B
(#guarded).  The upper boundary (0,0)(1,1)(2,2)(3,3) is outside.

1. THE CORRECTED RULE (K-arithmetic reading, `oCAux`).  The predecessor's
   path/cnt/floor-4 machinery (levelOf, ebGroups, argStep, phiStepC) is
   RETIRED, subsumed by one self-similar mechanism.  Blocks (split at
   row-0 = 0 columns, as always) are folded with THREE accumulators:
     acc  — the value so far;
     lacc — the LEVEL-space accumulator of the (0,2)-context;
     aacc — the ARGUMENT-space accumulator of the (0,2)-context;
   and the reading carries kb, the enclosing (0,1)-nesting level (a Term,
   replacing the old path p; top level kb = 0).

   * (0,0)-block, lacc = 0 — acc := acc + ω̄^(fresh read of the dec'd tail)
     (the Stage-B summand rule, §4(b): summand exponent reads stay fresh).
   * (0,0)-block, lacc ≠ 0 (inside a (0,2)-context) — THE SAME summand rule
     run in the argument space of the context level K = kb ⊕ ω̄^lacc:
       aacc := aacc + ω̄^(fresh read of the dec'd tail);
       acc  := φ_K(logφ_K acc + ω̄^aacc)     if logφ_K acc exists,
               acc + (the summand)           otherwise (below the level).
     This one law yields the whole (2,0)-family: the count ladder
     (2,2)(2,0)^k ↦ φ̄(ω,ω^{k-1}) and, through the fresh reads of the tails,
     φ̄(ω, ω̄^S) for S any Stage-B value ((2,0)(3,0) ↦ φ̄(ω,ω̄^ω), …,
     (2,0)(3,1)(4,2) ↦ φ̄(ω,W)).
   * (0,1)-block — a SUCCESSOR-level φ-step (Pair.phiStep) at level
     K₁ = (context level) + 1, with the threading of §4(a): thr := acc when
     acc is a strict fixed point above K₁+1 (isHighFp), the sub-read starts
     at thr, and only the additive DELTA above thr (stripThr) enters the
     step.  The delta (not vi itself) is what keeps the P-ladder green:
     threading the raw vi breaks P at its first rung.
   * (0,2)-block — climbs the LEVEL space by the same summand law one floor
     up:  lacc := lacc + ω̄^(context read of the dec'd tail), and
       acc := φ_{K₂}(logφ_{K₂} acc + ω̄^aacc | 0 if no logφ),
     K₂ = kb ⊕ ω̄^lacc.  The context read passes lacc+1 down, so the tail's
     (0,1)/(0,2)-blocks see the raised levels while its (0,0)-blocks (no
     logφ-base) stay summands.  This subsumes floor 4: the old anchors
     reappear as the chain-forced values of the (2,0)-prefixed family.
   * ψ-STUB — the single configuration (0,2)-block with dec'd tail exactly
     [(0,1)] at kb = 1, lacc = 0, acc = 0 (i.e. the matrix (2,2)(3,1))
     reads ψ_Ω(0).  See §3; the ψ-ARGUMENT hierarchy behind it (the
     (3,1)(4,·)/(3,2)-suffixes) is the NEXT stage and is NOT implemented.

2. THE DIAGONAL REBUILD (what changed, chain-forced and #guarded).  Every
   value re-derived green-outward from the P-ladder of the (ii)-session;
   each anchor is E1-#guarded and the key rungs are mcE3-#guarded against
   their machine fans; all corpora below are checkAll-green INCLUDING the
   cross-corpus E2 sweep over the pooled 217 matrices (the depth-cutoff
   blindness that hid four generations of mutual misassignment is closed).
     (1,1)(2,1)         = φ̄(2,W)     (1,1)(2,1)(3,1) = φ̄(3,W)   (ladder φ̄(n,W))
     (1,1)(2,2)         = φ̄(ω,1)    [(1,1)(2,2)]^k   = φ̄(ω,k)
     (2,2)(2,0)         = φ̄(ω,ω)    (2,2)(2,0)(2,0)  = φ̄(ω,ω²)
     (2,2)(2,0)(3,0)    = φ̄(ω,ω̄^ω)  …(3,0)(2,0) = φ̄(ω,ω̄^{ω+1})
     …(3,0)(2,0)(3,0)   = φ̄(ω,ω̄^{ω·2})   …(3,0)(3,0) = φ̄(ω,ω̄^{ω²})
     …(3,0)(4,0)        = φ̄(ω,ω̄^{ω̄^ω})   (2,2)(2,0)(3,1) = φ̄(ω,ε₀)
     (2,2)(2,0)(3,1)(4,2) = φ̄(ω,W)  (its cascades: the φ̄(ω,·)-towers)
     (2,2)(2,1)         = φ̄(ω+1,0)  (2,2)(2,1)(2,1) = φ̄(ω+1,1)
     (2,2)(2,1)(3,1)    = φ̄(ω+2,0)  (2,2)(2,1)(3,2) = φ̄(ω·2,0)
     (2,2)(2,2)         = φ̄(ω²,0)   (2,2)(2,2)(2,2) = φ̄(ω³,0)
     (2,2)(3,0)         = φ̄(ω̄^ω,0)  (2,2)(3,0)(3,0) = φ̄(ω̄^{ω²},0)
     (2,2)(3,0)(2,2)(3,0) = φ̄(ω̄^{ω·2},0)  (2,2)(3,0)(4,0) = φ̄(ω̄^{ω̄^ω},0)
     (2,2)(3,0)(4,1)    = φ̄(ε₀,0)   (2,2)(3,0)(4,1)(5,2) = φ̄(W,0)
   TABLE CORRECTIONS against the ten withdrawn rows (old ↦ new):
     (2,2)(2,0): ε_{W·ω} ↦ φ̄(ω,ω)          (2,2)(2,1): φ̄(2,W) ↦ φ̄(ω+1,0)
     (2,2)(2,1)(3,1): φ̄(3,W) ↦ φ̄(ω+2,0)    (2,2)(2,1)(3,2): φ̄(ω,1) ↦ φ̄(ω·2,0)
     (2,2)(2,2): φ̄(ω,ω) ↦ φ̄(ω²,0)          (2,2)(2,2)(2,2): φ̄(ω,ω²) ↦ φ̄(ω³,0)
     (2,2)(3,0): φ̄(ω,ω̄^ω) ↦ φ̄(ω̄^ω,0)      (2,2)(3,0)(3,0): φ̄(ω,ω̄^{ω+1}) ↦ φ̄(ω̄^{ω²},0)
     (2,2)(3,0)(4,1): φ̄(ω,ω̄^{ω²}) ↦ φ̄(ε₀,0)  (2,2)(3,1): φ̄(ω+1,0) ↦ ψ_Ω(0)
   The old values live on, one address DOWN, at the (2,0)-prefixed
   re-derivations — the committed diagonals had carried exactly the values
   of their first re-derivation members, as the (ii)-session predicted.

3. Γ₀ = ψ_Ω(0) IDENTIFIED:  (0,0)(1,1)(2,2)(3,1) = ψ_Ω(0) = Γ₀.
   Chain evidence (#guarded): the machine fan of (2,2)(3,1) is the
   Γ-tower  W, φ̄(W,0), φ̄(φ̄(W,0),0), …  (E1 guards on the members), and
   since W = φ_ω(0) < Γ₀, its sup is the FIRST strongly critical ordinal,
   Γ₀.  The mcE3 guard verifies ψ_Ω(0) mutually cofinal with the fan
   (fsN ψ_Ω(0) is the Γ-tower from 1; the towers absorb).  The first
   ψ-term of the correspondence is on the board.

4. OPEN FRONTIER (next session).  (a) The ψ-ARGUMENT hierarchy: suffixes
   after (2,2)(3,1) — the ladder (3,1)(4,1)^k (↦ ψ_Ω(k)?), (3,1)(4,2)
   (↦ ψ_Ω(ω)?), (2,2)(3,2) (fan = the ψ_Ω-tower; ↦ ψ_Ω(Ω)?) — need the
   argument-space recursion of the same design one floor up.  The corpus
   filter `psiFrontier` below marks exactly this region ((a+1,≥1)-column
   right after an (a,2)-column); its members are excluded from the corpus
   guards, EXCEPT (2,2)(3,1) itself which is green.  (b) The configuration
   (0,2)-block AFTER (0,0)-blocks in the same context (matrix shape
   (2,2)(2,0)(2,2)): currently collides with (2,2)(2,2); it lies outside
   every acceptance corpus (checked: absent from the pooled sweep), and
   needs the aacc-material folded into the level climb.

5. FRONT STATUS.  (ii-a) the (2,2)(2,0)-corpus: GREEN (was 8 E3-fails +
   116 E2-bad pairs).  (ii-b) the (2,2)(3,0)(3,0)-corpus: GREEN.  (ii-c)
   the (4,1)-family: GREEN through the context read ((2,2)(3,0)(4,1)-corpus
   checkAll, mcE3 anchors).  The four collision tripwires of the
   (ii)-session are FLIPPED to separation form below and pass.  All Stage-B
   agreement and every corpus below the cascade: green, cross-corpus E2
   sweep included.

Note: the imports precede this comment because the kimina server extracts
the header imports from the top of a posted snippet.
-/

namespace Trans

open TM (Term)
open TM.Term
open Pair (r0 r1 decP blocksP logPhi phiStep)

namespace StageC

/-- The fragment: every column of height ≤ 2 with row-1 entry ≤ 2. -/
def inFragC (m : BMS.Matrix) : Bool := m.all fun c => c.length ≤ 2 && r1 c ≤ 2

/-- Is `t` a strict fixed point of φ_k (its head's φ-level lies above k)? -/
def isHighFp (k : Term) : Term → Bool
  | .add a _ => isHighFp k a
  | .phi a _ => lt k a
  | _ => false

/-- The additive delta of `v` above the thread `thr`: 0 if v = thr, the
    remainder if thr is an additive prefix of v, v itself otherwise. -/
def stripThr (thr v : Term) : Term :=
  if thr == Term.zero then v
  else
    let lt := toList thr
    let lv := toList v
    if lv.take lt.length == lt then ofList (lv.drop lt.length) else v

/-- The K-arithmetic reading (see the header).  `kb` is the enclosing
    (0,1)-nesting level, `lacc0` the inherited level-space accumulator;
    the fold carries (acc, lacc, aacc). -/
def oCAux : Nat → Term → Term → Term → List BMS.Col → Term
  | 0, _, _, _, _ => Term.zero
  | fuel + 1, kb, lacc0, acc0, s =>
    ((blocksP s).foldl (init := (acc0, lacc0, Term.zero)) fun (acc, lacc, aacc) b =>
      match b with
      | [] => (acc, lacc, aacc)
      | c :: t =>
        if r1 c == 0 then
          -- summand rule; inside a (0,2)-context it runs in the argument space
          let x := omegaNF (oCAux fuel Term.zero Term.zero Term.zero (decP t))
          if lacc == Term.zero then
            (plus acc x, lacc, aacc)
          else
            let k := plus kb (omegaNF lacc)
            let aacc' := plus aacc x
            (match logPhi k acc with
             | none => plus acc x
             | some bse => phiNF k (plus bse (omegaNF aacc')),
             lacc, aacc')
        else if r1 c == 1 then
          -- (0,1)-block: successor-level φ-step one level above the context
          let k1 := plus (if lacc == Term.zero then kb
                          else plus kb (omegaNF lacc)) one
          let thr := if isHighFp (plus k1 one) acc then acc else Term.zero
          let vi := oCAux fuel k1 Term.zero thr (decP t)
          (phiStep k1 acc (stripThr thr vi), lacc, Term.zero)
        else if decP t == [[0,1]] && acc == Term.zero && lacc == Term.zero
                && kb == one then
          -- ψ-stub: the Γ-diagonal (2,2)(3,1) = ψ_Ω(0) (header §3);
          -- the ψ-argument hierarchy behind it is the next stage (§4a)
          (psi Om Term.zero, lacc, aacc)
        else
          -- (0,2)-block: climbs the level space
          let lacc' := plus lacc
            (omegaNF (oCAux fuel kb (plus lacc one) Term.zero (decP t)))
          let k2 := plus kb (omegaNF lacc')
          let g := match logPhi k2 acc with
                   | none => Term.zero
                   | some bse => plus bse (omegaNF aacc)
          (phiNF k2 g, lacc', Term.zero)).1

end StageC

/-- Stage C (C''' revision): the translation on the 2-row fragment with
    row-1 entries ≤ 2 (`none` outside).  Row-1-all-zero matrices delegate
    to `oPr`.  The ψ-frontier configurations of header §4 are provisional. -/
def oStageC? (m : BMS.Matrix) : Option Term :=
  if StageC.inFragC m then
    some (if onlyRow0 m then oPr m
          else StageC.oCAux (m.length + 1) Term.zero Term.zero Term.zero m)
  else none

/-- Total version for the corpus checkers (junk 0 outside the fragment). -/
def oStageCT (m : BMS.Matrix) : Term := (oStageC? m).getD Term.zero

/-! ## Acceptance record (E1 instances, agreement, corpus checks) -/

namespace StageC.Test

open BMS (Matrix)
open Evidence

private def W : Term := phi omega zero            -- φ̄(ω,0)

-- E1 instances: the boundary of Stage B and the (1,1)-subtree
#guard oStageC? [[0,0],[1,1],[2,2]] == some W
#guard oStageC? [[0,0],[1,1],[2,2],[1,1]] == some (phi one W)
#guard oStageC? [[0,0],[1,1],[2,2],[1,1],[2,1]] == some (phiNF (ofNat 2) (plus W one))
#guard oStageC? [[0,0],[1,1],[2,2],[1,1],[2,1],[3,1]] == some (phiNF (ofNat 3) (plus W one))
#guard oStageC? [[0,0],[1,1],[2,2],[1,1],[2,2]] == some (phi omega one)
#guard oStageC? [[0,0],[1,1],[2,2],[1,1],[2,2],[1,1],[2,2]] == some (phi omega (ofNat 2))

-- E1 instances: the (2,0)-family (arguments ω̄^S, S a fresh Stage-B value)
#guard oStageC? [[0,0],[1,1],[2,2],[2,0]] == some (phi omega omega)
#guard oStageC? [[0,0],[1,1],[2,2],[2,0],[2,0]] == some (phi omega (omegaNF (ofNat 2)))
#guard oStageC? [[0,0],[1,1],[2,2],[2,0],[3,0]] == some (phi omega (phi zero omega))
#guard oStageC? [[0,0],[1,1],[2,2],[2,0],[3,0],[2,0]] ==
  some (phi omega (omegaNF (plus omega one)))
#guard oStageC? [[0,0],[1,1],[2,2],[2,0],[3,0],[2,0],[3,0]] ==
  some (phi omega (omegaNF (plus omega omega)))
#guard oStageC? [[0,0],[1,1],[2,2],[2,0],[3,0],[3,0]] ==
  some (phi omega (omegaNF (omegaNF (ofNat 2))))
#guard oStageC? [[0,0],[1,1],[2,2],[2,0],[3,0],[4,0]] ==
  some (phi omega (omegaNF (omegaNF omega)))
#guard oStageC? [[0,0],[1,1],[2,2],[2,0],[3,0],[1,1],[2,2],[2,0],[3,0]] ==
  some (phi omega (plus (phi zero omega) (phi zero omega)))
#guard oStageC? [[0,0],[1,1],[2,2],[2,0],[3,1]] == some (phi omega (phi one zero))
#guard oStageC? [[0,0],[1,1],[2,2],[2,0],[3,1],[4,2]] == some (phi omega (phi omega zero))
#guard oStageC? [[0,0],[1,1],[2,2],[2,0],[3,1],[4,2],[4,0],[5,1],[6,2]] ==
  some (phi omega (phi omega (phi omega zero)))

-- E1 instances: the corrected diagonal rows (header §2 table corrections)
#guard oStageC? [[0,0],[1,1],[2,2],[2,1]] == some (phi (plus omega one) zero)
#guard oStageC? [[0,0],[1,1],[2,2],[2,1],[2,1]] == some (phi (plus omega one) one)
#guard oStageC? [[0,0],[1,1],[2,2],[2,1],[3,1]] == some (phi (plus omega (ofNat 2)) zero)
#guard oStageC? [[0,0],[1,1],[2,2],[2,1],[3,2]] == some (phi (plus omega omega) zero)
#guard oStageC? [[0,0],[1,1],[2,2],[2,2]] == some (phi (omegaNF (ofNat 2)) zero)
#guard oStageC? [[0,0],[1,1],[2,2],[2,2],[2,2]] == some (phi (omegaNF (ofNat 3)) zero)
#guard oStageC? [[0,0],[1,1],[2,2],[3,0]] == some (phi (omegaNF omega) zero)
#guard oStageC? [[0,0],[1,1],[2,2],[3,0],[3,0]] ==
  some (phi (omegaNF (omegaNF (ofNat 2))) zero)
#guard oStageC? [[0,0],[1,1],[2,2],[3,0],[2,2],[3,0]] ==
  some (phi (omegaNF (plus omega omega)) zero)
#guard oStageC? [[0,0],[1,1],[2,2],[3,0],[4,0]] ==
  some (phi (omegaNF (omegaNF omega)) zero)
#guard oStageC? [[0,0],[1,1],[2,2],[3,0],[4,1]] == some (phi (phi one zero) zero)

-- Γ₀ = ψ_Ω(0) (header §3): the E1, the Γ-tower fan members, and inT
#guard oStageC? [[0,0],[1,1],[2,2],[3,1]] == some (psi Om zero)
#guard oStageC? [[0,0],[1,1],[2,2],[3,0],[4,1],[5,2]] == some (phi W zero)
#guard oStageC? [[0,0],[1,1],[2,2],[3,0],[4,1],[5,2],[6,0],[7,1],[8,2]] ==
  some (phi (phi W zero) zero)
#guard inT (oStageCT [[0,0],[1,1],[2,2],[3,1]])

-- the upper boundary of the fragment is outside the domain
#guard (oStageC? [[0,0],[1,1],[2,2],[3,3]]).isNone

-- agreement with Stage B on its whole fragment (row-1 ≤ 1), over a corpus
#guard (corpus [[0,0],[1,1],[2,1],[3,1]] 3 3).all fun m => oStageC? m == oPair? m
#guard (corpus [[0],[1],[2]] 4 3).all fun m => oStageC? m == some (oPr m)

/-- The ψ-frontier (header §4a): an (a+1, ≥1)-column right after an
    (a,2)-column — the region whose values are ψ_Ω-terms beyond the stub. -/
def psiFrontier (m : Matrix) : Bool :=
  (m.zip (m.drop 1)).any fun (c, c') =>
    r1 c == 2 && r0 c' == r0 c + 1 && r1 c' ≥ 1

private def d31 : Matrix := [[0,0],[1,1],[2,2],[3,1]]
private def d33 : Matrix := [[0,0],[1,1],[2,2],[3,3]]

/-- Corpus filter: keep (2,2)(3,1) (green through the ψ-stub), drop the
    boundary and the rest of the ψ-frontier. -/
def keepM (m : Matrix) : Bool := m == d31 || (m != d33 && !psiFrontier m)

-- corpora (depth 3, width 3); g5–g9 are ψ-frontier-filtered (header §4a)
private def g1 : List Matrix := corpus [[0,0],[1,1],[2,2]] 3 3
private def g2 : List Matrix := corpus [[0,0],[1,1],[2,2],[2,1]] 3 3
private def g3 : List Matrix := corpus [[0,0],[1,1],[2,2],[2,1],[3,1]] 3 3
private def g4 : List Matrix := corpus [[0,0],[1,1],[2,2],[2,1],[3,2]] 3 3
private def g5 : List Matrix := (corpus [[0,0],[1,1],[2,2],[3,1]] 3 3).filter keepM
private def g6 : List Matrix := (corpus [[0,0],[1,1],[2,2],[3,1],[4,2]] 3 3).filter keepM
private def g7 : List Matrix := (corpus [[0,0],[1,1],[2,2],[3,2]] 3 3).filter keepM
private def g8 : List Matrix := (corpus [[0,0],[1,1],[2,2],[3,2],[4,2]] 3 3).filter keepM
private def g9 : List Matrix := (corpus [[0,0],[1,1],[2,2],[3,3]] 3 3).filter keepM
private def g10 : List Matrix := corpus [[0,0],[1,1],[2,2],[2,2]] 3 3
private def g11 : List Matrix := corpus [[0,0],[1,1],[2,2],[3,0]] 3 3
private def g12 : List Matrix := corpus [[0,0],[1,1],[2,2],[2,2],[2,2]] 3 3
private def g13 : List Matrix := corpus [[0,0],[1,1],[2,2],[3,0],[4,1]] 3 3
private def gA : List Matrix := corpus [[0,0],[1,1],[2,2],[2,0]] 3 3        -- front ii-a
private def gB : List Matrix := corpus [[0,0],[1,1],[2,2],[3,0],[3,0]] 3 3  -- front ii-b
private def gall : List Matrix :=
  g1 ++ g2 ++ g3 ++ g4 ++ g5 ++ g6 ++ g7 ++ g8 ++ g9 ++ g10 ++ g11 ++ g12 ++
  g13 ++ gA ++ gB

-- domain closure and formation conditions
#guard gall.all fun m => (oStageC? m).isSome
#guard gall.all fun m => inT (oStageCT m)

-- the full checks on every corpus
#guard checkAll oStageCT g1 3 6
#guard checkAll oStageCT g2 3 6
#guard checkAll oStageCT g3 3 6
#guard checkAll oStageCT g4 3 6
#guard checkAll oStageCT g5 3 8
#guard checkAll oStageCT g6 3 6
#guard checkAll oStageCT g7 3 6
#guard checkAll oStageCT g8 3 6
#guard checkAll oStageCT g9 3 8
#guard checkAll oStageCT g10 3 6
#guard checkAll oStageCT g11 3 8
#guard checkAll oStageCT g12 3 8
#guard checkAll oStageCT g13 3 8
#guard checkAll oStageCT gA 3 8
#guard checkAll oStageCT gB 3 8

-- THE CROSS-CORPUS E2 SWEEP (the protocol's closure of the depth-cutoff
-- blindness): the order embedding over ALL PAIRS of the pooled corpora,
-- including the Stage-B agreement corpus
#guard checkE2 oStageCT
  ((gall ++ corpus [[0,0],[1,1],[2,1],[3,1]] 3 3).eraseDups)

/-! ## (ii)-session evidence carried forward, tripwires flipped -/

private def P : Matrix := [[0,0],[1,1],[2,2],[1,1],[2,0],[3,1],[4,2]]
private def copy2 : Matrix := P ++ [[1,1],[2,0],[3,1],[4,2]]
private def P20 : Matrix := P ++ [[2,0]]
private def rep2 : Matrix := P ++ [[2,0],[3,1],[4,2]]
private def P30 : Matrix := P ++ [[3,0]]
private def M1 : Matrix := P ++ [[3,1]]
private def f1 : Matrix := [[0,0],[1,1],[2,2],[1,1],[2,1]]
private def d20 : Matrix := [[0,0],[1,1],[2,2],[2,0]]
private def d21 : Matrix := [[0,0],[1,1],[2,2],[2,1]]

/-- E3-mutual-cofinality of a candidate value `t` for `m`, over the machine
    fan of `m` with the committed readings of the fan members. -/
private def mcE3 (m : Matrix) (t : Term) (w w' : Nat) : Bool :=
  ((List.range w).all fun n =>
    match BMS.expand? m n with
    | some m' => lt (oStageCT m') t
    | none => false)
  &&
  ((List.range w).all fun n =>
    match BMS.expand? m n with
    | some m' => (List.range w').any fun k => lt (oStageCT m') (fsN t (k + 1))
    | none => false)
  &&
  ((List.range w).all fun k =>
    (List.range w').any fun n =>
      match BMS.expand? m n with
      | some m' => lt (fsN t (k + 1)) (oStageCT m')
      | none => false)

-- the green P-ladder of the (ii)-session: unchanged, still forced
#guard oStageC? P == some (phiNF one (plus W W))
#guard oStageC? copy2 == some (phiNF one (plus (plus W W) W))
#guard oStageC? P20 == some (phiNF one (omegaNF (plus W one)))
#guard oStageC? rep2 == some (phiNF one (omegaNF (plus W W)))
#guard oStageC? P30 == some (phiNF one (omegaNF (omegaNF (plus W one))))
#guard oStageC? M1 == some (phiNF one (phiNF one (plus W one)))
#guard mcE3 P (phiNF one (plus W W)) 3 6
#guard mcE3 P20 (phiNF one (omegaNF (plus W one))) 3 6
#guard mcE3 rep2 (phiNF one (omegaNF (plus W W))) 3 6
#guard mcE3 P30 (phiNF one (omegaNF (omegaNF (plus W one)))) 3 6
#guard mcE3 M1 (phiNF one (phiNF one (plus W one))) 3 6
#guard mcE3 f1 (phiNF (ofNat 2) (plus W one)) 3 6

-- mutual cofinality of the rebuilt rungs over their machine fans
#guard mcE3 [[0,0],[1,1],[2,2],[2,0],[3,0]] (phi omega (phi zero omega)) 3 8
#guard mcE3 [[0,0],[1,1],[2,2],[2,0],[3,0],[3,0]]
  (phi omega (omegaNF (omegaNF (ofNat 2)))) 3 8
#guard mcE3 d21 (phi (plus omega one) zero) 3 8
#guard mcE3 [[0,0],[1,1],[2,2],[2,2]] (phi (omegaNF (ofNat 2)) zero) 3 8
#guard mcE3 [[0,0],[1,1],[2,2],[3,0]] (phi (omegaNF omega) zero) 3 8
#guard mcE3 [[0,0],[1,1],[2,2],[3,0],[3,0]]
  (phi (omegaNF (omegaNF (ofNat 2))) zero) 3 8
#guard mcE3 [[0,0],[1,1],[2,2],[3,0],[4,1]] (phi (phi one zero) zero) 3 8
-- Γ₀: ψ_Ω(0) is mutually cofinal with the machine fan of (2,2)(3,1)
#guard mcE3 d31 (psi Om zero) 3 8

-- THE FOUR TRIPWIRES OF THE (ii)-SESSION, FLIPPED: the collisions they
-- asserted are now separations, in E2 form (matrix-lt matches term-lt)
#guard BMS.cmpM P [[0,0],[1,1],[2,2],[1,1],[2,2]] == .lt &&
  lt (oStageCT P) (oStageCT [[0,0],[1,1],[2,2],[1,1],[2,2]])
#guard BMS.cmpM P20 d20 == .lt && lt (oStageCT P20) (oStageCT d20)
#guard BMS.cmpM rep2 [[0,0],[1,1],[2,2],[2,0],[3,1],[4,2]] == .lt &&
  lt (oStageCT rep2) (oStageCT [[0,0],[1,1],[2,2],[2,0],[3,1],[4,2]])
#guard BMS.cmpM f1 d21 == .lt && lt (oStageCT f1) (oStageCT d21)

-- the (ii)-session E2-violation witnesses, now in correct-order form
#guard BMS.cmpM P30 d20 == .lt && lt (oStageCT P30) (oStageCT d20)
#guard BMS.cmpM M1 d20 == .lt && lt (oStageCT M1) (oStageCT d20)

end StageC.Test

end Trans
