import Trans.TM
import Evidence.Check
/-
Trans/Pair.lean — Stage B of the translation o : BMS → 𝔗(M):
the 2-row fragment with row-1 entries ≤ 1 (the binary-Veblen region below φ̄(ω,0))

Fragment (the domain of `oPair?`):
  matrices all of whose columns have height ≤ 2 and row-1 entry ≤ 1.
  Its standard part is bounded above by (0,0)(1,1)(2,2), which is outside
  ((0,0)(1,1)(2,2)[n] = (0,0)(1,1)(2,1)(3,1)…(n+1,1) climbs the φ̄(n,0), so the
  bound itself corresponds to φ̄(ω,0) — first term of Stage C).
  Matrices whose rows below row 0 are all zero are delegated to Stage A's `oPr`
  (`oLAux` computes the same values there; the delegation keeps E1 rows stable).

Translation rule (derived from the BM4 expansion behaviour, not from community
tables; every clause below was forced by E3-style sup-reasoning on machine
expansions and then validated by the corpus checks recorded at the bottom):

  A sequence of columns is split into blocks just before each column with
  row-0 entry 0 (`blocksP`, the 2-row analogue of `blocks0`).  The blocks are
  folded left to right into an accumulator `acc` (starting at 0); the reading
  carries a φ-level k (top level: k = 1):

  * block (0,0)::t  —  acc := acc + ω̄^( oL 1 (dec t) )
      a CNF summand, exactly as in the 1-row region; its exponent is read at
      level 1 again (a row-1 = 0 column restarts the value hierarchy);
  * block (0,1)::t  —  acc := φ_k( logφ_k(acc) + step ),   [normalized φ = phiNF]
      where v := oL (k+1) (dec t) is the tail read one level up,
      step := 1 if v = 0, ω̄^v otherwise, and logφ_k(acc) is the largest β with
      φ_k(β) ≤ acc (dropped when acc < φ_k(0)).

  `dec t` decrements row 0 and keeps row 1 (`decP`).  Row-1 = 1 columns hence
  drive the (first) Veblen argument — each nesting depth of (0,1)-heads raises
  the φ-level by one — while row-1 = 0 columns build ω-power/CNF structure.

  Sample values (all machine-checked below):
    (0,0)(1,1)           = φ̄(1,0)      = ε₀
    (0,0)(1,1)(1,0)      = φ̄(0,ε₀)     = ω^{ε₀+1}
    (0,0)(1,1)(1,1)      = φ̄(1,1)      = ε₁
    (0,0)(1,1)(2,0)      = φ̄(1,ω)      = ε_ω
    (0,0)(1,1)(2,0)(3,1) = φ̄(1,ε₀)     = ε_{ε₀}
    (0,0)(1,1)(2,1)      = φ̄(2,0)      = ζ₀
    (0,0)(1,1)(2,1)(2,1) = φ̄(2,1)      = ζ₁
    (0,0)(1,1)(2,1)(2,0) = φ̄(1,ω̄^{ζ₀+1}) = ε_{ζ₀·ω}
    (0,0)(1,1)(2,1)(3,0) = φ̄(2,ω)      = ζ_ω
    (0,0)(1,1)(2,1)(3,1) = φ̄(3,0)

Design rationale for `logPhi`/`phiStep` (why an accumulator):
  repeated (0,1)-blocks at one level step the last Veblen argument
  ((1,1)(1,1) → ε₁), and the step size is dictated by mutual cofinality with
  the BM4 expansions: e.g. (0,0)(1,1)(2,1)(2,0)[n] appends (1,1)(2,1)-pairs,
  whose values ε_{ζ₀·2}, ε_{ζ₀·3}, … force step = ω̄^v (not "next fixed point").
  `plus` absorbs `logφ_k(acc)` when ω̄^v dominates, and `phiNF` collapses
  φ_k(γ) to γ when γ is already a higher fixed point — both are needed for the
  order embedding (checkE2) to hold across the corpus.

Index convention (as everywhere in this repo): o(M[n]) corresponds to (o M)[n+1].
Beyond ε₀ the expansions and the fundamental sequences are different cofinal
sequences of the same ordinal, so the acceptance test is checkE3i (mutual
cofinality), not equality of sequences — see Evidence/Check.lean.

Acceptance record (see the #guards at the bottom; additionally checked during
development with depth-5/width-3 corpora from (0,0)(1,1)(2,2) and
(0,0)(1,1)(2,1) and a depth-4/width-4 corpus from (0,0)(1,1)(2,1)(3,1) —
133/142/275 matrices — with E3 windows w = 4, w' = 10: no failures).

Note: the imports precede this comment because the kimina server extracts the
header imports from the top of a posted snippet (a leading module comment makes
it mis-split the header and warm workers then reject the import).
-/

namespace Trans

open TM (Term)
open TM.Term

namespace Pair

/-- Row-0 entry of a column. -/
def r0 (c : BMS.Col) : Nat := c.getD 0 0

/-- Row-1 entry of a column. -/
def r1 (c : BMS.Col) : Nat := c.getD 1 0

/-- The fragment: every column of height ≤ 2 with row-1 entry ≤ 1. -/
def inFrag (m : BMS.Matrix) : Bool := m.all fun c => c.length ≤ 2 && r1 c ≤ 1

/-- Decrement row 0, keep row 1 (applied to the tail of a block). -/
def decP (s : List BMS.Col) : List BMS.Col := s.map fun c => [r0 c - 1, r1 c]

/-- Split just before each column whose row-0 entry is 0
    (the 2-row analogue of `blocks0`). -/
def blocksP : List BMS.Col → List (List BMS.Col)
  | [] => []
  | c :: rest =>
    match blocksP rest, rest.head? with
    | acc, some h => if r0 h == 0 then [c] :: acc else (c :: acc.headD []) :: acc.tail
    | _, none => [[c]]

/-- logφ_k: the largest β with φ_k(β) ≤ t, `none` when t < φ_k(0).
    A raw term φ̄ a b denotes φ_a(b°) with b° = b+1 iff `phiShifted a b`
    ([Rathjen, 1991] 2.7), whence the shift in the a = k case; for a > k the term is a
    φ_k-fixed point and is its own logarithm; for a < k and for sums the
    logarithm is decided by the argument resp. the head component. -/
def logPhi (k : Term) : Term → Option Term
  | .add a _ => logPhi k a
  | .phi a b =>
    if a == k then some (if phiShifted a b then plus b one else b)
    else if lt k a then some (.phi a b)
    else logPhi k b
  | _ => none

/-- One (0,1)-block at φ-level k: φ_k(logφ_k(acc) + step) with step = 1 for an
    empty tail and ω̄^v otherwise (`phiNF` collapses when the argument is
    already a higher fixed point). -/
def phiStep (k acc v : Term) : Term :=
  let g : Term :=
    match logPhi k acc, v == Term.zero with
    | none, true => Term.zero
    | none, false => omegaNF v
    | some b, true => plus b one
    | some b, false => plus b (omegaNF v)
  phiNF k g

/-- The level-indexed reading of a 2-row column sequence (see the header).
    `fuel` bounds the recursion depth; every recursive call is on a strictly
    shorter sequence, so `length + 1` suffices at the top. -/
def oLAux : Nat → Nat → List BMS.Col → Term
  | 0, _, _ => Term.zero
  | fuel + 1, k, s =>
    (blocksP s).foldl (init := Term.zero) fun acc b =>
      match b with
      | [] => acc  -- unreachable: blocks are nonempty
      | c :: t =>
        if r1 c == 0 then
          plus acc (omegaNF (oLAux fuel 1 (decP t)))
        else
          phiStep (ofNat k) acc (oLAux fuel (k + 1) (decP t))

end Pair

/-- Stage B: the translation on the 2-row fragment with row-1 entries ≤ 1
    (`none` outside).  On row-1-all-zero matrices it delegates to Stage A's
    `oPr` (with which `oLAux` agrees there — see the #guards). -/
def oPair? (m : BMS.Matrix) : Option Term :=
  if Pair.inFrag m then
    some (if onlyRow0 m then oPr m else Pair.oLAux (m.length + 1) 1 m)
  else none

/-- Total version of `oPair?` for the corpus checkers (junk 0 outside the
    fragment; the domain-closure #guards ensure the junk is never consulted). -/
def oPairT (m : BMS.Matrix) : Term := (oPair? m).getD Term.zero

/-- The translation, as a partial function; its domain grows stage by stage
    (Stage A: `oPr` on one-row-effective matrices; Stage B: `oPair?`).
    Outside the domain it is `none`. -/
def o? (m : BMS.Matrix) : Option Term :=
  if onlyRow0 m then some (oPr m) else oPair? m

/-! ## Acceptance record (E1 instances, domain closure, corpus checks)

The corpora are the reachable sets of Evidence/Check.lean; `checkAll` is
checkKind + checkSucc + checkE2 (order embedding over all pairs) + checkE3i
(E3 in mutual-cofinality form).  A successful build re-verifies everything. -/

namespace Pair.Test

open BMS (Matrix)
open Evidence

/-- ε₀ = φ̄10, ζ₀ = φ̄20 -/
private def e0 : Term := phi one zero
private def z0 : Term := phi (ofNat 2) zero

-- E1 instances: the table rows this stage supports (matrix ↦ term)
#guard oPair? [[0,0],[1,1]] == some e0                              -- ε₀
#guard oPair? [[0,0],[1,1],[1,0]] == some (phi zero e0)             -- ω^{ε₀+1}
#guard oPair? [[0,0],[1,1],[1,1]] == some (phi one one)             -- ε₁
#guard oPair? [[0,0],[1,1],[1,1],[1,0]] == some (phi zero (phi one one))
#guard oPair? [[0,0],[1,1],[2,0]] == some (phi one omega)           -- ε_ω
#guard oPair? [[0,0],[1,1],[2,0],[3,1]] == some (phi one e0)        -- ε_{ε₀}
#guard oPair? [[0,0],[1,1],[2,1]] == some z0                        -- ζ₀
#guard oPair? [[0,0],[1,1],[2,1],[2,1]] == some (phi (ofNat 2) one) -- ζ₁
#guard oPair? [[0,0],[1,1],[2,1],[3,0]] == some (phi (ofNat 2) omega) -- ζ_ω
#guard oPair? [[0,0],[1,1],[2,1],[3,1]] == some (phi (ofNat 3) zero)  -- φ(3,0)

-- the upper boundary of the fragment is outside the domain
#guard (oPair? [[0,0],[1,1],[2,2]]).isNone

-- corpora: reachable sets from the Stage-B seeds (depth 3, width 3), plus the
-- reachable set of the boundary matrix (0,0)(1,1)(2,2) without the boundary
-- itself (its whole expansion fan lies inside the fragment)
private def c1 : List Matrix := corpus [[0,0],[1,1],[1,1]] 3 3
private def c2 : List Matrix := corpus [[0,0],[1,1],[2,0]] 3 3
private def c3 : List Matrix := corpus [[0,0],[1,1],[2,1]] 3 3
private def c4 : List Matrix := corpus [[0,0],[1,1],[2,1],[3,1]] 3 3
private def c5 : List Matrix :=
  (corpus [[0,0],[1,1],[2,2]] 4 3).filter (fun m => m != [[0,0],[1,1],[2,2]])
private def call : List Matrix := c1 ++ c2 ++ c3 ++ c4 ++ c5

-- the corpora stay inside the fragment (so `oPairT` never returns junk there)
#guard call.all fun m => (oPair? m).isSome

-- every produced term satisfies the formation conditions of 𝔗(M)
#guard call.all fun m => inT (oPairT m)

-- Stage-A agreement: on row-1-all-zero matrices oLAux computes oPr's values
-- (so the delegation in `oPair?` is a no-op, kept for E1 stability)
#guard (call.filter onlyRow0).all fun m =>
  Pair.oLAux (m.length + 1) 1 m == oPr m
#guard (corpus [[0],[1],[2]] 4 3).all fun m => o? m == some (oPr m)

-- the full checks: kind preservation, predecessor matching, E2 order
-- embedding over all pairs, and E3 in mutual-cofinality form
#guard checkAll oPairT c1 3 6
#guard checkAll oPairT c2 3 6
#guard checkAll oPairT c3 3 6
#guard checkAll oPairT c4 3 6
#guard checkAll oPairT c5 3 8

end Pair.Test

end Trans
