/-
Evidence/Bisim.lean — the bisimulation checker (a computational form of E3)

The claim "the matrix M and the term t denote the same ordinal" is checked
directly, without going through `o`:
  - the kinds (zero / successor / limit) agree,
  - for successors, the predecessors correspond,
  - for limits, M[n] corresponds to t[n+1] for every n < width,
recursively down to depth `fuel`.

Index convention (see Trans/TM.lean): the BMS expansion M[n] lays down n+1 copies,
so the T(M) side is compared at t[n+1].

This is a finite-depth check and is no substitute for a per-row E3 lemma (∀n), but
it is a sensitive filter against wrong correspondences while `o` is being designed.
Depth d and width w check on the order of w^d pairs.
-/
import BMS
import TM

namespace Evidence

open BMS (Matrix)
open TM (Term)
open TM.Term

/-- Finite-depth bisimulation check between M and t. -/
def bisim (fuel : Nat) (M : Matrix) (t : Term) (width : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 =>
    match BMS.kind M, kindT t with
    | .zero, .isZero => true
    | .succ, .isSucc =>
      -- successor: compare the predecessors (on the BMS side the last column is
      -- simply dropped, so the copy count is irrelevant)
      (match BMS.expand? M 0 with
       | some M' => bisim fuel M' (predT t) width
       | none => false)
    | .lim, .isLim =>
      (List.range width).all fun n =>
        match BMS.expand? M n with
        | some M' => bisim fuel M' (fsN t (n + 1)) width
        | none => false
    | _, _ => false

/-- Default parameters (depth 5, width 3). -/
def bisim5 (M : Matrix) (t : Term) : Bool := bisim 5 M t 3

/-!
## Why cross-system value comparison was rejected (kept as a record)

An earlier attempt (`eqv`) checked "val(M) = val(t)" directly, by mutual
cofinality between the expansion of the matrix and the fundamental sequence of the
term.  With finite fuel it ran out before reaching a contradiction, so it also
accepted wrong pairs (for instance the matrix for ε₁ against the term for ε₂):
comparing a matrix with a term is only possible by tracking expansions deeply.

Correspondence is therefore checked through `o`, inside the decidable order of
T(M) (Evidence/Check.lean):
  - instances of E2: order embedding over a corpus;
  - E3 in mutual-cofinality form: the sequence o(M[n]) and the sequence
    fsN (o M) overtake each other.
The strict bisimulation above remains useful as a checker in the region where the
fundamental sequences coincide with the BMS expansions (the CNF region).
-/

end Evidence
