/-
Rows/Proofs.lean — per-row proofs

For a row (M, t) of the table the claim is that the BMS expansion of M agrees
with the fundamental sequence of t, for EVERY copy count n:

    e3 : ∀ n, o (M[n]) = t[n+1]        (limit rows)

(the index shift is the convention of Trans/TM.lean: M[n] lays down n+1 copies).
Successor rows carry `esucc` instead — their expansion drops the last column, so
it must translate to the predecessor of t — and the zero row carries only `e1`.
This is the real content of a table row; the `#guard`s of Rows/TM.lean only check
finitely many n.

Each row lives in a namespace named after the matrix itself and provides
  M, t : the row,
  e1   : o M = t,
  e3 / esucc : the statement above.
-/
import Rows.TM
import TM.Lemmas

namespace Rows.Proofs

open BMS (Matrix)
open TM (Term)
open TM.Term
open Trans

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

/-! ## Translation of the repeated shapes -/

theorem row0_repM1 (a : Nat) : ∀ k, row0 (repM [[a]] k) = List.replicate k a
  | 0 => rfl
  | k + 1 => by
    show a :: row0 (repM [[a]] k) = a :: List.replicate k a
    rw [row0_repM1 a k]

theorem onlyRow0_repM1 (a : Nat) : ∀ k, onlyRow0 (repM [[a]] k) = true
  | 0 => rfl
  | k + 1 => by
    show (true && onlyRow0 (repM [[a]] k)) = true
    rw [onlyRow0_repM1 a k]; rfl

theorem length_repM1 (a : Nat) : ∀ k, (repM [[a]] k).length = k
  | 0 => rfl
  | k + 1 => by
    show ([[a]] ++ repM [[a]] k).length = k + 1
    rw [List.length_append, length_repM1 a k]
    show 1 + k = k + 1
    omega

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

/-- `(0)(1)…(1)` with `k` ones translates to ω^k. -/
theorem oPrAux_0ones (f k : Nat) :
    oPrAux (f + 2) (0 :: List.replicate k 1) = phiNF zero (mulNat one k) := by
  have hb : blocks0 (0 :: List.replicate k 1) = [0 :: List.replicate k 1] :=
    blocks0_single 0 (List.replicate k 1) (fun x hx => by
      rw [List.eq_of_mem_replicate hx]; exact Nat.one_ne_zero)
  rw [oPrAux_unfold, hb]
  show plus (omegaNF (oPrAux (f + 1) ((List.replicate k 1).map (· - 1)))) zero
     = phiNF zero (mulNat one k)
  rw [plus_zero, List.map_replicate]
  show omegaNF (oPrAux (f + 1) (List.replicate k 0)) = phiNF zero (mulNat one k)
  rw [oPrAux_rep0, omegaNF_mulNat_one]

/-- `(0)(1)(2)…(2)` with `k` twos translates to ω^(ω^k). -/
theorem oPrAux_01twos (f k : Nat) :
    oPrAux (f + 3) (0 :: 1 :: List.replicate k 2)
      = phiNF zero (phiNF zero (mulNat one k)) := by
  have hb : blocks0 (0 :: 1 :: List.replicate k 2) = [0 :: 1 :: List.replicate k 2] :=
    blocks0_single 0 (1 :: List.replicate k 2) (fun x hx => by
      cases hx with
      | head => exact Nat.one_ne_zero
      | tail _ h => rw [List.eq_of_mem_replicate h]; decide)
  rw [oPrAux_unfold, hb]
  show plus (omegaNF (oPrAux (f + 2) ((1 :: List.replicate k 2).map (· - 1)))) zero
     = phiNF zero (phiNF zero (mulNat one k))
  rw [plus_zero]
  show omegaNF (oPrAux (f + 2) (0 :: (List.replicate k 2).map (· - 1)))
     = phiNF zero (phiNF zero (mulNat one k))
  rw [List.map_replicate]
  show omegaNF (oPrAux (f + 2) (0 :: List.replicate k 1))
     = phiNF zero (phiNF zero (mulNat one k))
  rw [oPrAux_0ones, omegaNF_phiNF]

/-- `(0)(1)(0)…(0)` with `k` trailing zeros translates to ω + k. -/
theorem oPrAux_01zeros (f k : Nat) :
    oPrAux (f + 2) (0 :: 1 :: List.replicate k 0) = plus omega (mulNat one k) := by
  have hb : blocks0 (0 :: 1 :: List.replicate k 0)
      = [0, 1] :: blocks0 (List.replicate k 0) := by
    cases k with
    | zero => rfl
    | succ m =>
      show (match blocks0 (1 :: List.replicate (m + 1) 0),
                  (1 :: List.replicate (m + 1) 0).head? with
            | acc, some hd => if hd == 0 then [0] :: acc else (0 :: acc.headD []) :: acc.tail
            | _, none => [[0]]) = [0, 1] :: blocks0 (List.replicate (m + 1) 0)
      rw [blocks0_cons_zero 1 (List.replicate (m + 1) 0) rfl]
      rfl
  rw [oPrAux_unfold, hb]
  show plus (omegaNF (oPrAux (f + 1) [0]))
        (((blocks0 (List.replicate k 0)).map
          (fun b => omegaNF (oPrAux (f + 1) ((b.drop 1).map (· - 1))))).foldr plus zero)
      = plus omega (mulNat one k)
  rw [oPrAux_single, ← oPrAux_unfold, oPrAux_rep0]
  rfl

/-! ## Fundamental sequences of the terms that occur in the table -/

theorem fs_omega (n : Nat) : fsN omega (n + 1) = mulNat one (n + 1) := by
  show fsN (phi zero one) (n + 1) = mulNat one (n + 1)
  rw [fsN]; rfl

theorem fs_omega_two (n : Nat) :
    fsN (add omega omega) (n + 1) = plus omega (mulNat one (n + 1)) := by
  rw [fsN, fs_omega]

theorem fs_omega_sq (n : Nat) :
    fsN (phi zero (ofNat 2)) (n + 1) = mulNat omega (n + 1) := by
  rw [fsN]; rfl

theorem fs_omega_omega (n : Nat) :
    fsN (phi zero omega) (n + 1) = phiNF zero (mulNat one (n + 1)) := by
  rw [fsN, fs_omega]; rfl

theorem fs_omega_omega_omega (n : Nat) :
    fsN (phi zero (phi zero omega)) (n + 1)
      = phiNF zero (phiNF zero (mulNat one (n + 1))) := by
  rw [fsN, fs_omega_omega]; rfl

/-! ## Rows -/

/-! ### Row `(空)` = 0. -/
namespace «(empty)»

def M : Matrix := []
def t : Term := zero

theorem e1 : o? M = some t := rfl

/-- The empty matrix is the zero of the notation, and so is its term. -/
theorem kinds : BMS.kind M = .zero ∧ kindT t = .isZero := ⟨rfl, rfl⟩

end «(empty)»

/-! ### Row `(0)` = 1. -/
namespace «(0)»

def M : Matrix := [[0]]
def t : Term := one

theorem e1 : o? M = some t := rfl

/-- Successor: the expansion drops the last column and lands on the predecessor. -/
theorem esucc (n : Nat) : o? (BMS.expand M n) = some (predT t) := by
  cases n <;> rfl

end «(0)»

/-! ### Row `(0)(0)` = 2. -/
namespace «(0)(0)»

def M : Matrix := [[0], [0]]
def t : Term := ofNat 2

theorem e1 : o? M = some t := rfl

theorem esucc (n : Nat) : o? (BMS.expand M n) = some (predT t) := by
  cases n <;> rfl

end «(0)(0)»

/-! ### Row `(0)(1)` = ω. -/
namespace «(0)(1)»

def M : Matrix := [[0], [1]]
def t : Term := omega

theorem e1 : o? M = some t := rfl

theorem expand_eq (n : Nat) : BMS.expand? M n = some (repM [[0]] (n + 1)) := by
  have h : BMS.expand? M n
      = some (((List.range (n + 1)).map (fun _ => ([[0]] : Matrix))).flatten) := rfl
  rw [h, flat_range]

theorem fs_eq (n : Nat) : fsN t (n + 1) = mulNat one (n + 1) := fs_omega n

/-- **E3** for this row. -/
theorem e3 (n : Nat) : o? (BMS.expand M n) = some (fsN t (n + 1)) := by
  have hE : BMS.expand M n = repM [[0]] (n + 1) := by
    show (BMS.expand? M n).getD [] = repM [[0]] (n + 1)
    rw [expand_eq]; rfl
  rw [hE, fs_eq]
  simp only [o?, oPr, onlyRow0_repM1, row0_repM1, length_repM1, if_true]
  exact congrArg some (oPrAux_rep0 (n + 1) (n + 1))

end «(0)(1)»

/-! ### Row `(0)(1)(0)(1)` = ω·2. -/
namespace «(0)(1)(0)(1)»

def M : Matrix := [[0], [1], [0], [1]]
def t : Term := add omega omega

theorem e1 : o? M = some t := rfl

theorem expand_eq (n : Nat) :
    BMS.expand? M n = some ([[0], [1]] ++ repM [[0]] (n + 1)) := by
  have h : BMS.expand? M n
      = some ([[0], [1]] ++ ((List.range (n + 1)).map (fun _ => ([[0]] : Matrix))).flatten) := rfl
  rw [h, flat_range]

theorem fs_eq (n : Nat) : fsN t (n + 1) = plus omega (mulNat one (n + 1)) := fs_omega_two n

/-- **E3** for this row. -/
theorem e3 (n : Nat) : o? (BMS.expand M n) = some (fsN t (n + 1)) := by
  have hE : BMS.expand M n = [[0], [1]] ++ repM [[0]] (n + 1) := by
    show (BMS.expand? M n).getD [] = [[0], [1]] ++ repM [[0]] (n + 1)
    rw [expand_eq]; rfl
  have hwf : onlyRow0 ([[0], [1]] ++ repM [[0]] (n + 1)) = true := by
    show (true && (true && onlyRow0 (repM [[0]] (n + 1)))) = true
    rw [onlyRow0_repM1]; rfl
  have hrow : row0 ([[0], [1]] ++ repM [[0]] (n + 1)) = 0 :: 1 :: List.replicate (n + 1) 0 := by
    show 0 :: 1 :: row0 (repM [[0]] (n + 1)) = 0 :: 1 :: List.replicate (n + 1) 0
    rw [row0_repM1]
  have hlen : ([[0], [1]] ++ repM [[0]] (n + 1)).length = n + 3 := by
    rw [List.length_append, length_repM1]
    show 2 + (n + 1) = n + 3
    omega
  rw [hE, fs_eq]
  simp only [o?, oPr, hwf, hrow, hlen, if_true]
  exact congrArg some (oPrAux_01zeros (n + 2) (n + 1))

end «(0)(1)(0)(1)»

/-! ### Row `(0)(1)(1)` = ω². -/
namespace «(0)(1)(1)»

def M : Matrix := [[0], [1], [1]]
def t : Term := phi zero (ofNat 2)

/-- `(0)(1)` repeated `k` times — the shape of every expansion of this row. -/
abbrev E (k : Nat) : Matrix := repM [[0], [1]] k

/-- Row 0 of `E k`. -/
def S : Nat → List Nat
  | 0 => []
  | k + 1 => [0, 1] ++ S k

theorem e1 : o? M = some t := rfl

theorem expand_eq (n : Nat) : BMS.expand? M n = some (E (n + 1)) := by
  have h : BMS.expand? M n
      = some (((List.range (n + 1)).map (fun _ => ([[0], [1]] : Matrix))).flatten) := rfl
  rw [h, flat_range]

theorem row0_E : ∀ k, row0 (E k) = S k
  | 0 => rfl
  | k + 1 => by
    show [0, 1] ++ row0 (E k) = [0, 1] ++ S k
    rw [row0_E k]

theorem onlyRow0_E : ∀ k, onlyRow0 (E k) = true
  | 0 => rfl
  | k + 1 => by
    show (true && (true && onlyRow0 (E k))) = true
    rw [onlyRow0_E k]; rfl

theorem length_E : ∀ k, (E k).length = 2 * k
  | 0 => rfl
  | k + 1 => by
    show ([[0], [1]] ++ E k).length = 2 * (k + 1)
    rw [List.length_append, length_E k]
    show 2 + 2 * k = 2 * (k + 1)
    omega

/-- Splitting the row-0 sequence into blocks peels off one `(0)(1)`. -/
theorem blocks0_S : ∀ k, blocks0 (S (k + 1)) = [0, 1] :: blocks0 (S k)
  | 0 => rfl
  | _ + 1 => rfl

/-- `k` copies of `(0)(1)` translate to ω·k. -/
theorem oPrAux_S (f : Nat) : ∀ k, oPrAux (f + 2) (S k) = mulNat omega k
  | 0 => rfl
  | k + 1 => by
    rw [oPrAux_unfold, blocks0_S]
    show plus (omegaNF (oPrAux (f + 1) [0]))
           (((blocks0 (S k)).map
              (fun b => omegaNF (oPrAux (f + 1) ((b.drop 1).map (· - 1))))).foldr plus zero)
         = mulNat omega (k + 1)
    rw [oPrAux_single, ← oPrAux_unfold, oPrAux_S f k]
    exact mulNat_succ isAP_omega k

theorem fs_eq (n : Nat) : fsN t (n + 1) = mulNat omega (n + 1) := fs_omega_sq n

/-- **E3** for this row. -/
theorem e3 (n : Nat) : o? (BMS.expand M n) = some (fsN t (n + 1)) := by
  have hE : BMS.expand M n = E (n + 1) := by
    show (BMS.expand? M n).getD [] = E (n + 1)
    rw [expand_eq]; rfl
  rw [hE, fs_eq]
  simp only [o?, oPr, onlyRow0_E, row0_E, length_E, if_true]
  exact congrArg some (oPrAux_S (2 * n + 1) (n + 1))

end «(0)(1)(1)»

/-! ### Row `(0)(1)(2)` = ω^ω. -/
namespace «(0)(1)(2)»

def M : Matrix := [[0], [1], [2]]
def t : Term := phi zero omega

theorem e1 : o? M = some t := rfl

theorem expand_eq (n : Nat) :
    BMS.expand? M n = some ([[0]] ++ repM [[1]] (n + 1)) := by
  have h : BMS.expand? M n
      = some ([[0]] ++ ((List.range (n + 1)).map (fun _ => ([[1]] : Matrix))).flatten) := rfl
  rw [h, flat_range]

theorem fs_eq (n : Nat) : fsN t (n + 1) = phiNF zero (mulNat one (n + 1)) :=
  fs_omega_omega n

/-- **E3** for this row. -/
theorem e3 (n : Nat) : o? (BMS.expand M n) = some (fsN t (n + 1)) := by
  have hE : BMS.expand M n = [[0]] ++ repM [[1]] (n + 1) := by
    show (BMS.expand? M n).getD [] = [[0]] ++ repM [[1]] (n + 1)
    rw [expand_eq]; rfl
  have hwf : onlyRow0 ([[0]] ++ repM [[1]] (n + 1)) = true := by
    show (true && onlyRow0 (repM [[1]] (n + 1))) = true
    rw [onlyRow0_repM1]; rfl
  have hrow : row0 ([[0]] ++ repM [[1]] (n + 1)) = 0 :: List.replicate (n + 1) 1 := by
    show 0 :: row0 (repM [[1]] (n + 1)) = 0 :: List.replicate (n + 1) 1
    rw [row0_repM1]
  have hlen : ([[0]] ++ repM [[1]] (n + 1)).length = n + 2 := by
    rw [List.length_append, length_repM1]
    show 1 + (n + 1) = n + 2
    omega
  rw [hE, fs_eq]
  simp only [o?, oPr, hwf, hrow, hlen, if_true]
  exact congrArg some (oPrAux_0ones (n + 1) (n + 1))

end «(0)(1)(2)»

/-! ### Row `(0)(1)(2)(3)` = ω^(ω^ω). -/
namespace «(0)(1)(2)(3)»

def M : Matrix := [[0], [1], [2], [3]]
def t : Term := phi zero (phi zero omega)

theorem e1 : o? M = some t := rfl

theorem expand_eq (n : Nat) :
    BMS.expand? M n = some ([[0], [1]] ++ repM [[2]] (n + 1)) := by
  have h : BMS.expand? M n
      = some ([[0], [1]] ++ ((List.range (n + 1)).map (fun _ => ([[2]] : Matrix))).flatten) := rfl
  rw [h, flat_range]

theorem fs_eq (n : Nat) :
    fsN t (n + 1) = phiNF zero (phiNF zero (mulNat one (n + 1))) :=
  fs_omega_omega_omega n

/-- **E3** for this row. -/
theorem e3 (n : Nat) : o? (BMS.expand M n) = some (fsN t (n + 1)) := by
  have hE : BMS.expand M n = [[0], [1]] ++ repM [[2]] (n + 1) := by
    show (BMS.expand? M n).getD [] = [[0], [1]] ++ repM [[2]] (n + 1)
    rw [expand_eq]; rfl
  have hwf : onlyRow0 ([[0], [1]] ++ repM [[2]] (n + 1)) = true := by
    show (true && (true && onlyRow0 (repM [[2]] (n + 1)))) = true
    rw [onlyRow0_repM1]; rfl
  have hrow : row0 ([[0], [1]] ++ repM [[2]] (n + 1)) = 0 :: 1 :: List.replicate (n + 1) 2 := by
    show 0 :: 1 :: row0 (repM [[2]] (n + 1)) = 0 :: 1 :: List.replicate (n + 1) 2
    rw [row0_repM1]
  have hlen : ([[0], [1]] ++ repM [[2]] (n + 1)).length = n + 3 := by
    rw [List.length_append, length_repM1]
    show 2 + (n + 1) = n + 3
    omega
  rw [hE, fs_eq]
  simp only [o?, oPr, hwf, hrow, hlen, if_true]
  exact congrArg some (oPrAux_01twos (n + 1) (n + 1))

end «(0)(1)(2)(3)»

end Rows.Proofs
