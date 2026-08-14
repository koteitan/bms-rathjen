/-
TM/Lemmas.lean — basic algebraic lemmas about the term operations

These are the building blocks the per-row E3 proofs (Rows/Proofs.lean) rely on.
They are about the encoding of formal sums (`toList` / `ofList` / `plus`) and
about the normal operations, not about ordinals, so they hold for every row and
are proved once here.
-/
import TM.FS

namespace TM
namespace Term

/-! ## Formal sums -/

/-- An additively principal term is its own one-element sum. -/
theorem toList_of_isAP {a : Term} (h : a.isAP = true) : toList a = [a] := by
  cases a <;> first | rfl | simp [isAP] at h

/-- `ofList` is a right inverse of `toList` on lists of additively principal terms. -/
theorem toList_ofList : ∀ {l : List Term}, (∀ x ∈ l, x.isAP = true) → toList (ofList l) = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    cases t with
    | nil => exact toList_of_isAP (h a (by simp))
    | cons b u =>
      show a :: toList (ofList (b :: u)) = a :: b :: u
      rw [ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem isAP_omega : omega.isAP = true := rfl
theorem isAP_one : one.isAP = true := rfl

/-- a + a·k = a·(k+1): prepending one more summand to a sum of copies of `a`. -/
theorem mulNat_succ {a : Term} (ha : a.isAP = true) (k : Nat) :
    plus a (mulNat a k) = mulNat a (k + 1) := by
  cases k with
  | zero => rfl
  | succ m =>
    show plus a (ofList (List.replicate (m + 1) a)) = ofList (List.replicate (m + 2) a)
    have hall : ∀ x ∈ List.replicate (m + 1) a, x.isAP = true := by
      intro x hx
      rw [List.eq_of_mem_replicate hx]; exact ha
    show (match toList (ofList (List.replicate (m + 1) a)) with
          | [] => a
          | b1 :: _ => ofList ((toList a).filter (fun y => le b1 y) ++
                               toList (ofList (List.replicate (m + 1) a))))
         = ofList (List.replicate (m + 2) a)
    rw [toList_ofList hall, toList_of_isAP ha, List.replicate_succ]
    have hle : le a a = true := by simp [le]
    show ofList ((match le a a with | true => [a] | false => []) ++ a :: List.replicate m a)
       = ofList (List.replicate (m + 2) a)
    rw [hle]
    rfl

/-- Adding zero on the right leaves a sum unchanged. -/
theorem plus_zero (s : Term) : plus s zero = s := rfl

/-! ## Bridging `omegaNF` and `phiNF` -/

/-- Nothing strongly critical exceeds M. -/
theorem lt_M_of_isSC {b : Term} (h : b.isSC = true) : lt M b = false := by
  cases b <;> first | rfl | simp [isSC] at h

/-- A normalized Veblen value never exceeds M: every branch of `phiNF` returns
    either a `φ̄` term, or one of its (strongly critical) arguments. -/
theorem lt_M_phiNF (a b : Term) : lt M (phiNF a b) = false := by
  unfold phiNF phiNFsucc phiNFdefault
  split
  · rename_i h
    exact lt_M_of_isSC (by simp at h; exact h.1)
  · repeat' split
    all_goals first
      | rfl
      | (apply lt_M_of_isSC; simp_all)

/-- Below M, `ω^·` is the normalized Veblen function at 0 ([Rathjen, 1991] 2.6(vii)). -/
theorem omegaNF_of_le_M {X : Term} (h : lt M X = false) : omegaNF X = phiNF zero X := by
  unfold omegaNF
  rw [h]
  simp only [Bool.false_eq_true, if_false]
  split
  · rename_i hM
    have : X = M := by simpa using hM
    subst this; rfl
  · rfl

/-- Finite terms stay below M. -/
theorem lt_M_mulNat_one : ∀ k, lt M (mulNat one k) = false
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

theorem omegaNF_mulNat_one (k : Nat) : omegaNF (mulNat one k) = phiNF zero (mulNat one k) :=
  omegaNF_of_le_M (lt_M_mulNat_one k)

theorem omegaNF_phiNF (a b : Term) : omegaNF (phiNF a b) = phiNF zero (phiNF a b) :=
  omegaNF_of_le_M (lt_M_phiNF a b)

end Term
end TM
