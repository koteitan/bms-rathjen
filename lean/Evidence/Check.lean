/-
Evidence/Check.lean — exhaustive checks over the domain of `o`
(instance checkers for E1 / E2 / E3)

Over a corpus (a finite set of matrices reachable by expansion) on which `o` is
defined, everything is checked inside the decidable order of the T(M) side:

  checkKind : `o` preserves the classification zero / successor / limit
  checkSucc : for successors, o(pred M) = pred (o M)
  checkE2   : order embedding, ltB M N ↔ o M <_T o N (all pairs)
  checkE3i  : for a limit M,
                (a) o(M[n]) < o(M)
                (b) ∀n ∃k. o(M[n]) < (o M)[k]   (the expansions are overtaken by the fs)
                (c) ∀k ∃n. (o M)[k] < o(M[n])   (the fs is overtaken by the expansions)
              — E3 in mutual-cofinality form.  If (b) and (c) both hold, the two
              sequences have the same supremum.

The BMS expansions and the fundamental sequences may be different cofinal sequences
for one and the same ordinal (an ε₀-tower versus an ω-tower for ε₁), which is why
E3 is stated in this mutual-cofinality form rather than as an equation.
-/
import BMS
import TM
import Trans.TM

namespace Evidence

open BMS (Matrix)
open TM (Term)
open TM.Term

/-- One round of expansions (width w). -/
def stepAll (w : Nat) (ms : List Matrix) : List Matrix :=
  ms.flatMap fun m => (List.range w).filterMap fun n => BMS.expand? m n

/-- The corpus reachable from `seed` within depth d and width w (duplicates removed). -/
def corpus (seed : Matrix) (d w : Nat) : List Matrix :=
  (List.range d).foldl (fun acc _ => (acc ++ stepAll w acc).eraseDups) [seed]

/-- Preservation of the classification. -/
def checkKind (o : Matrix → Term) (c : List Matrix) : Bool :=
  c.all fun m =>
    match BMS.kind m, kindT (o m) with
    | .zero, .isZero => true
    | .succ, .isSucc => true
    | .lim, .isLim => true
    | _, _ => false

/-- Correspondence of predecessors at successors. -/
def checkSucc (o : Matrix → Term) (c : List Matrix) : Bool :=
  c.all fun m =>
    BMS.kind m != .succ ||
    (match BMS.expand? m 0 with
     | some m' => o m' == predT (o m)
     | none => false)

/-- Instances of E2: the order embedding, over all pairs of the corpus. -/
def checkE2 (o : Matrix → Term) (c : List Matrix) : Bool :=
  c.all fun m1 => c.all fun m2 =>
    (BMS.cmpM m1 m2 == .lt) == lt (o m1) (o m2)

/-- E3 in mutual-cofinality form (width w, search width w' for the overtaking index). -/
def checkE3i (o : Matrix → Term) (c : List Matrix) (w w' : Nat) : Bool :=
  c.all fun m =>
    BMS.kind m != .lim ||
    (let t := o m
     ((List.range w).all fun n =>
       match BMS.expand? m n with
       | some m' => lt (o m') t
       | none => false)
     &&
     ((List.range w).all fun n =>
       match BMS.expand? m n with
       | some m' => (List.range w').any fun k => lt (o m') (fsN t (k + 1))
       | none => false)
     &&
     ((List.range w).all fun k =>
       (List.range w').any fun n =>
         match BMS.expand? m n with
         | some m' => lt (fsN t (k + 1)) (o m')
         | none => false))

/-- Run all of the checks. -/
def checkAll (o : Matrix → Term) (c : List Matrix) (w w' : Nat) : Bool :=
  checkKind o c && checkSucc o c && checkE2 o c && checkE3i o c w w'

end Evidence
