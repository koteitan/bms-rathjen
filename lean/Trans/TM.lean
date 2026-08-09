/-
Trans/TM.lean — the translation o : BMS → 𝔗(M), built up in stages

Policy: the conjectured correspondences found in the community tables
(BM4-Analysis and the like) are not reliable on the large side, so `o` is defined
starting from the small region and extended stage by stage, each stage being
validated by computational checks of E3 (expansion vs fundamental sequence) —
see Evidence/Check.lean and Evidence/Bisim.lean.

Index convention: the BMS expansion M[n] lays down the copies B(0)…B(n), i.e.
n+1 of them, so the index is typically shifted by one against the T(M) side:
    o(M[n])  corresponds to  (o M)[n+1]

BUT THE SHIFT IS NOT UNIFORM ACROSS ROWS, and this comment used to claim it was.
Measured over the nine E3 proofs in Rows/Proofs.lean and Rows/ProofsB.lean
(2026-08-10): four state `fsN t0 (n+1)`, one states `(n+2)` (R5), TWO state plain
`n` (R4 = ε_ω, R8), and two use a bespoke `oval`.  So `+1` is the common case and
not the convention; each row's E3 theorem states its own index and that statement
is the authority.

Do NOT apply `+1` uniformly when measuring against `fsN` — it produces mass
disagreement that reads as "fsN is wrong above ε₀", and fsN is not wrong.  At
ε_ω, `fsN (φ̄(1,ω)) n` agrees with the WF lane's calibrated `fsEW n` exactly, at
shift 0.  The non-uniformity is the same phenomenon Evidence/WF.lean §15.22
records for core (C) and table/index-shift-2026-08-10.txt measures: the index is
matrix-determined and no property of the term computes it.

Current domain:
  Stage A: the one-row-effective region (all rows below row 0 are zero),
           i.e. the CNF region below ε₀.
-/
import BMS
import TM

namespace Trans

open TM (Term)
open TM.Term

/-- Row 0 (the top row) of a matrix, as a sequence. -/
def row0 (M : BMS.Matrix) : List Nat := M.map (·.getD 0 0)

/-- Is every row below row 0 zero (i.e. only row 0 is effective)? -/
def onlyRow0 (M : BMS.Matrix) : Bool :=
  M.all fun c => (c.drop 1).all (· == 0)

/-- Split into blocks just before each 0:
    (0,1,2,0,1) → [[0,1,2],[0,1]].  A standard one-row sequence is a run of
    blocks each starting with 0. -/
def blocks0 : List Nat → List (List Nat)
  | [] => []
  | x :: rest =>
    match blocks0 rest, rest.head? with
    | acc, some h => if h == 0 then [x] :: acc else (x :: acc.headD []) :: acc.tail
    | _, none => [[x]]

/-- A primitive sequence (one row) as a CNF term:
    o(blocks) = Σ_i ω^{o(block i with its leading 0 removed and all entries decremented)}. -/
def oPrAux : Nat → List Nat → Term
  | 0, _ => zero
  | fuel + 1, s =>
    if s.isEmpty then zero
    else
      let bs := blocks0 s
      (bs.map fun b =>
        omegaNF (oPrAux fuel ((b.drop 1).map (· - 1)))).foldr plus zero

/-- Stage A: translation of one-row-effective matrices. -/
def oPr (M : BMS.Matrix) : Term := oPrAux (M.length + 1) (row0 M)

-- The dispatcher `o?` lives in Trans/Pair.lean (Stage B): it delegates
-- one-row-effective matrices to `oPr` and the 2-row fragment with row-1
-- entries ≤ 1 to `oPair?`.

end Trans
