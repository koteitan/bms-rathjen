import Rows.ProofsB
import BMS.Order
import BMS.Standard

open BMS (Matrix)
open TM.Term

/-!
# `scripts/reader_agreement.lean` — WHERE `Trans.oR` AND `Trans.o?` ACTUALLY AGREE

Not part of the build.  Run with `leanman check --backend lean -C <project> scripts/reader_agreement.lean`.

## Why this exists

`Trans.o?` is the RETRACTED translation and `Trans.oR` the recalibrated one.  The `Rows/` lemmas
are proved in `o?`; `Evidence/Cert.lean` speaks `oR`; **no symbolic lemma relates them**, and that
gap is what blocks `oR_rungM` (see `Cert` §21.1 and `table/rung-sequence-2026-08-10.txt`).

## RESULT — measured 2026-08-10, corpus of 607 distinct matrices

    agree 255 · disagree 352

    predicate                          trueAgree  trueDisagree  falseAgree  falseDisagree
    width < 4                                 20             1         235            351
    no second entry > 1                      255            86           0            266
    < (0,0)(1,1)(2,1)(2,0)                   255            11           0            341
    both of the previous two                 255            11           0            341
    < (0,0)(1,1)(2,1)(1,1)(2,1)              255             0           0            352

`trueDisagree = 0` and `falseAgree = 0` is a perfect separator, and only the last is one.

**AND THE ORDER CUT ALONE CANNOT SUPPORT A THEOREM.**  `Matrix = List (List Nat)` admits
malformed heights: `[[0], [1,0,0]]` is BELOW the loop boundary and the two readers still disagree
on it, because the recalibrated reader rejects its height-three column while `o?`'s one-row
fallback accepts it.  So the bridge's hypothesis needs a well-formedness conjunct as well as the
order cut — `bridgeRegionB` below, which also separates perfectly on the corpus.

**THE RETRACTION BOUNDARY RECORDED ELSEWHERE IN THIS REPO IS TOO HIGH.**  Several files say `o?`
is wrong "at and above `(0,0)(1,1)(2,1)(2,0)`".  Measured, **11 matrices STRICTLY BELOW that
matrix already disagree**, and the first one is the loop-back matrix
`(0,0)(1,1)(2,1)(1,1)(2,1)`.  A bridge stated at the recorded boundary would be FALSE.

Standardness does not separate: the yaBMS `bms -s` reference classified all 607 as standard,
giving `(255, 352, 0, 0)`.  `BMS.Standard` is a reachability `Prop` with no decision procedure in
this project, which is why that check had to go through the reference executable.

## Controls

`#guard !agrees boundary` and `#guard !agrees loopBoundary` — both fire.  A separating predicate
measured on a corpus where the two never disagree would be worth nothing.
-/


namespace ReaderBridge

/-!
The measured corpus is deliberately assembled only from project-owned data:

* all 51 matrices in `Rows.rows`;
* `epsM k` and `eps0M k` for `k < 8`;
* `towerM k` for `k < 10`;
* `famM k c` for `k < 6`, with `c` drawn from zero, one, omega, eps0T,
  `tower j` for `j < 6`, and `epsN j` for `j < 4`;
* `rungM k n` for `k < 6`, `n < 8`;
* two levels of closure of the table rows under `BMS.expand` at arguments 0..3.

The raw sources are deduplicated at the end.  Thus `corpus.length`, rather than
the sum of those deliberately overlapping families, is the denominator below.
-/

def rowSeeds : List Matrix := Rows.rows.map (fun r => r.m)

def expandFan (xs : List Matrix) : List Matrix :=
  xs.flatMap fun M => (List.range 4).map (BMS.expand M)

def rowLevel1 : List Matrix := expandFan rowSeeds
def rowLevel2 : List Matrix := expandFan rowLevel1

def familyTerms : List TM.Term :=
  ([zero, one, omega, Evidence.WF.eps0T] ++
    (List.range 6).map Evidence.WF.tower ++
    (List.range 4).map Evidence.WF.epsN).eraseDups

def familySeeds : List Matrix :=
  (List.range 8).map Evidence.Cert.epsM ++
  (List.range 8).map Evidence.Cert.eps0M ++
  (List.range 10).map Evidence.Cert.towerM ++
  (List.range 6).flatMap (fun k => familyTerms.map (Evidence.Cert.famM k)) ++
  (List.range 6).flatMap (fun k =>
    (List.range 8).map (Evidence.Cert.rungM k))

def corpus : List Matrix :=
  (rowSeeds ++ rowLevel1 ++ rowLevel2 ++ familySeeds).eraseDups

def agrees (M : Matrix) : Bool := Trans.oR M == Trans.o? M

structure Confusion where
  trueAgree : Nat
  trueDisagree : Nat
  falseAgree : Nat
  falseDisagree : Nat
deriving Repr

def confusion (p : Matrix → Bool) : Confusion :=
  corpus.foldl (init := ⟨0, 0, 0, 0⟩) fun s M =>
    match p M, agrees M with
    | true, true => { s with trueAgree := s.trueAgree + 1 }
    | true, false => { s with trueDisagree := s.trueDisagree + 1 }
    | false, true => { s with falseAgree := s.falseAgree + 1 }
    | false, false => { s with falseDisagree := s.falseDisagree + 1 }

/-! A width-only reading of the withdrawal boundary: fewer than four columns. -/
def shortWidth (M : Matrix) : Bool := decide (M.length < 4)

/-! No column has a second entry greater than one. -/
def secondLeOne (M : Matrix) : Bool :=
  M.all fun c => decide (c.getD 1 0 ≤ 1)

def boundary : Matrix := [[0,0], [1,1], [2,1], [2,0]]
def belowBoundary (M : Matrix) : Bool := BMS.cmpM M boundary == .lt

/-!
The first loop-back matrix observed among the below-boundary disagreements.
-/
def loopBoundary : Matrix := [[0,0], [1,1], [2,1], [1,1], [2,1]]
def belowLoopBoundary (M : Matrix) : Bool := BMS.cmpM M loopBoundary == .lt

def bridgeRegionB (M : Matrix) : Bool :=
  belowLoopBoundary M && Trans.Pair.inFrag M

def BridgeRegion (M : Matrix) : Prop :=
  BMS.ltB M loopBoundary ∧ Trans.Pair.inFrag M = true

#eval rowSeeds.length
#eval rowLevel1.length
#eval rowLevel2.length
#eval familyTerms.length
#eval familySeeds.length
#eval corpus.length
#eval corpus.countP agrees
#eval corpus.countP (fun M => !agrees M)
#eval confusion shortWidth
#eval confusion secondLeOne
#eval confusion belowBoundary
#eval confusion (fun M => belowBoundary M && secondLeOne M)
#eval confusion belowLoopBoundary
#eval confusion bridgeRegionB

/-! Positive control: the historical first withdrawal-boundary matrix. -/
#guard !agrees boundary
#guard !agrees loopBoundary
#eval Trans.oR loopBoundary
#eval Trans.o? loopBoundary

/-!
The bare order cut cannot support a theorem over the raw `Matrix = List (List
Nat)` type: malformed heights are admitted by the type.  This diagnostic is not
part of the project-owned corpus; it audits the quantifier in the proposed
general theorem.  It is below the loop boundary but the recalibrated reader
rejects its height-three column while `o?`'s one-row fallback accepts it.
-/
def malformedHeight : Matrix := [[0], [1,0,0]]
#guard belowLoopBoundary malformedHeight
#guard !agrees malformedHeight

/-! Guard the candidate's separating power on this stated corpus before proofs. -/
#guard corpus.all fun M => belowLoopBoundary M == agrees M
#guard corpus.all fun M => bridgeRegionB M == agrees M

/-!
Proposed bridge.  Unfolding reaches an algorithm-equivalence obligation for
which `Trans/Recal.lean` exports no lemma; the temporary failed proof is retained
only while recording the exact obstruction and is removed from the green file.
-/
-- THE OBSTRUCTION, KEPT AS A RECORD AND NOT AS A PROOF.  Unfolding reaches an
-- algorithm-equivalence obligation for which `Trans/Recal.lean` exports no lemma:
--
--   theorem oR_eq_o?_of_bridgeRegion {M : Matrix} (h : BridgeRegion M) :
--       Trans.oR M = Trans.o? M := by
--     rcases h with ⟨hbelow, hfrag⟩
--     unfold Trans.oR Trans.Recal.oR Trans.o?      -- <- unsolved goals from here

/-!
`BMS.Standard` is a reachability `Prop`, not a decision procedure, and this
project has no `BMS.isStandard`.  The repository's own standardness audit uses
the yaBMS `bms -s` reference executable.  Running it over an export of exactly
this corpus classified all 607 matrices as standard, giving confusion counts
`(trueAgree,trueDisagree,falseAgree,falseDisagree) = (255,352,0,0)`.
-/

end ReaderBridge
