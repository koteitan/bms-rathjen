/-
Trans/Lemmas.lean — unfolding and shape lemmas for the Stage-A translation

These were born in Rows/Proofs.lean as the machinery of the first per-row proofs
and moved here when Evidence/StageA.lean (the general theorem of the one-row
region) took them over as its foundation.  Rows/Proofs.lean now derives the
per-row statements from the general theorem instead, so the dependency runs
  Trans/Lemmas.lean  ←  Evidence/StageA.lean  ←  Rows/Proofs.lean.
-/
import Trans.TM
import TM.Lemmas

namespace Trans

open BMS (Matrix)
open TM (Term)
open TM.Term

/-! ## Unfolding lemmas for the translation -/

/-- The `isEmpty` guard of `oPrAux` is redundant: `blocks0 [] = []` folds to `zero`. -/
theorem oPrAux_unfold (f : Nat) (s : List Nat) :
    oPrAux (f + 1) s
      = ((blocks0 s).map (fun b => omegaNF (oPrAux f ((b.drop 1).map (· - 1))))).foldr plus zero := by
  cases s <;> rfl

/-- The empty sequence translates to 0, whatever the fuel. -/
theorem oPrAux_nil (f : Nat) : oPrAux f [] = zero := by cases f <;> rfl

/-- The one-term block `(0)` translates to 1. -/
theorem oPrAux_single (f : Nat) : oPrAux (f + 1) [0] = one := by
  rw [oPrAux_unfold]
  show plus (omegaNF (oPrAux f [])) zero = one
  rw [oPrAux_nil]
  rfl

/-! ## Block decomposition -/

/-- A new block starts exactly at a 0. -/
theorem blocks0_cons_zero (a : Nat) (s : List Nat) (h : s.head? = some 0) :
    blocks0 (a :: s) = [a] :: blocks0 s := by
  cases s <;> simp_all [blocks0]

/-- A sequence without further zeros forms a single block. -/
theorem blocks0_single (a : Nat) :
    ∀ (s : List Nat), (∀ x ∈ s, x ≠ 0) → blocks0 (a :: s) = [a :: s]
  | [], _ => rfl
  | b :: t, h => by
    have hb : b ≠ 0 := h b (by simp)
    have ih : blocks0 (b :: t) = [b :: t] :=
      blocks0_single b t (fun x hx => h x (List.mem_cons_of_mem b hx))
    show (match blocks0 (b :: t), (b :: t).head? with
          | acc, some hd => if hd == 0 then [a] :: acc else (a :: acc.headD []) :: acc.tail
          | _, none => [[a]]) = [a :: b :: t]
    rw [ih]
    simp [hb]

/-! ## Repeated blocks -/

/-- `B` repeated `k` times. -/
def repM (B : Matrix) : Nat → Matrix
  | 0 => []
  | k + 1 => B ++ repM B k

theorem repM_append (B : Matrix) : ∀ k, repM B k ++ B = repM B (k + 1)
  | 0 => by simp [repM]
  | k + 1 => by
    show (B ++ repM B k) ++ B = B ++ repM B (k + 1)
    rw [List.append_assoc, repM_append B k]

/-- The copies laid down by the expansion rule are exactly `repM B m`. -/
theorem flat_range (B : Matrix) : ∀ m, ((List.range m).map (fun _ => B)).flatten = repM B m
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.flatten_append, flat_range B m]
    simpa using repM_append B m

/-- `(0)` repeated `k` times translates to the natural number `k`. -/
theorem oPrAux_rep0 (f : Nat) : ∀ k, oPrAux (f + 1) (List.replicate k 0) = mulNat one k
  | 0 => rfl
  | k + 1 => by
    have hb : blocks0 (List.replicate (k + 1) 0) = [0] :: blocks0 (List.replicate k 0) := by
      cases k with
      | zero => rfl
      | succ m => exact blocks0_cons_zero 0 (List.replicate (m + 1) 0) rfl
    rw [oPrAux_unfold, hb]
    show plus (omegaNF (oPrAux f [])) (((blocks0 (List.replicate k 0)).map
      (fun b => omegaNF (oPrAux f ((b.drop 1).map (· - 1))))).foldr plus zero) = mulNat one (k + 1)
    rw [oPrAux_nil, ← oPrAux_unfold, oPrAux_rep0 f k]
    exact mulNat_succ isAP_one k

end Trans
