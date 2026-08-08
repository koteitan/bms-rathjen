/-
BMS/Standard.lean — standard form as reachability from the initial matrix

A matrix is standard when it is obtained from (0,...,0)(1,...,1) of height `h`
by finitely many expansions (with an arbitrary copy count `n` at each step).

Rows of the table carry an explicit witness (the list of copy counts); evaluating
`reachBy` on that witness (by `decide`) checks standardness by computation.
-/
import BMS.Expand

namespace BMS

/-- `N` is reachable from `M` by expansions. -/
inductive Reach : Matrix → Matrix → Prop
  | refl (M : Matrix) : Reach M M
  | step {M N N' : Matrix} (n : Nat) :
      Reach M N → expand? N n = some N' → Reach M N'

theorem Reach.trans {A B C : Matrix} (hab : Reach A B) (hbc : Reach B C) :
    Reach A C := by
  induction hbc with
  | refl => exact hab
  | step n _ he ih => exact Reach.step n ih he

/-- Standard form at height `h`: reachable from the initial matrix. -/
def Standard (h : Nat) (M : Matrix) : Prop := Reach (init h) M

/-- Witness evaluator: follow an expansion path (the copy count of each step). -/
def reachBy (M : Matrix) : List Nat → Option Matrix
  | [] => some M
  | n :: ns =>
    match expand? M n with
    | none => none
    | some N => reachBy N ns

/-- Soundness of the witness: a successful `reachBy` yields `Reach`. -/
theorem reachBy_sound {M N : Matrix} {path : List Nat}
    (h : reachBy M path = some N) : Reach M N := by
  induction path generalizing M with
  | nil =>
    simp only [reachBy, Option.some.injEq] at h
    exact h ▸ Reach.refl M
  | cons n ns ih =>
    rw [reachBy] at h
    match he : expand? M n with
    | none => rw [he] at h; exact absurd h (by simp)
    | some M' =>
      rw [he] at h
      exact (Reach.step n (Reach.refl M) he).trans (ih h)

end BMS
