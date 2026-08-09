/-
Rows/Proofs.lean — per-row proofs, as instances of the general theorem

For a row (M, t) of the table the claim is that the BMS expansion of M agrees
with the fundamental sequence of t, for EVERY copy count n:

    e3 : ∀ n, o (M[n]) = t[n+1]        (limit rows)

(the index shift is the convention of Trans/TM.lean: M[n] lays down n+1 copies).
Successor rows carry `esucc` instead — their expansion drops the last column, so
it must translate to the predecessor of t — and the zero row carries only `e1`.

Every row below lies in the one-row region, so each proof is now a ONE-LINE
instance of the general theorems of Evidence/StageA.lean (`e3_matrix` /
`esucc_matrix`): the side conditions (syntactic standardness `stdSeq`, the last
entry) are decidable and discharged by `decide`/`rfl`, and `t = oPr M` holds by
computation.  The original hand proofs (one induction per row) lived here up to
v0.1.8 and were replaced by these instances; their machinery moved to
Trans/Lemmas.lean and is what Evidence/StageA.lean is built on.

Each row lives in a namespace named after the matrix itself and provides
  M, t : the row,
  e1   : o M = t,
  e3 / esucc : the statement above.
-/
import Evidence.StageA
import Evidence.StageB
import Rows.TM

namespace Rows.Proofs

open BMS (Matrix)
open TM (Term)
open TM.Term
open Trans
open Evidence.StageA (e3_matrix esucc_matrix)

-- Backward-compatible re-exports: this machinery originated here and moved to
-- Trans/Lemmas.lean; keep the old qualified names resolvable.
export Trans (oPrAux_unfold oPrAux_nil oPrAux_single blocks0_cons_zero blocks0_single
  repM repM_append flat_range oPrAux_rep0)

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

theorem esucc (n : Nat) : o? (BMS.expand M n) = some (predT t) :=
  esucc_matrix (X := M) rfl (by decide) rfl n

end «(0)»

/-! ### Row `(0)(0)` = 2. -/
namespace «(0)(0)»

def M : Matrix := [[0], [0]]
def t : Term := ofNat 2

theorem e1 : o? M = some t := rfl

theorem esucc (n : Nat) : o? (BMS.expand M n) = some (predT t) :=
  esucc_matrix (X := M) rfl (by decide) rfl n

end «(0)(0)»

/-! ### Row `(0)(1)` = ω. -/
namespace «(0)(1)»

def M : Matrix := [[0], [1]]
def t : Term := omega

theorem e1 : o? M = some t := rfl

theorem e3 (n : Nat) : o? (BMS.expand M n) = some (fsN t (n + 1)) :=
  e3_matrix (X := M) rfl (by decide) (c := 1) (by decide) rfl n

end «(0)(1)»

/-! ### Row `(0)(1)(0)(1)` = ω·2. -/
namespace «(0)(1)(0)(1)»

def M : Matrix := [[0], [1], [0], [1]]
def t : Term := add omega omega

theorem e1 : o? M = some t := rfl

theorem e3 (n : Nat) : o? (BMS.expand M n) = some (fsN t (n + 1)) :=
  e3_matrix (X := M) rfl (by decide) (c := 1) (by decide) rfl n

end «(0)(1)(0)(1)»

/-! ### Row `(0)(1)(1)` = ω². -/
namespace «(0)(1)(1)»

def M : Matrix := [[0], [1], [1]]
def t : Term := phi zero (ofNat 2)

theorem e1 : o? M = some t := rfl

theorem e3 (n : Nat) : o? (BMS.expand M n) = some (fsN t (n + 1)) :=
  e3_matrix (X := M) rfl (by decide) (c := 1) (by decide) rfl n

end «(0)(1)(1)»

/-! ### Row `(0)(1)(2)` = ω^ω. -/
namespace «(0)(1)(2)»

def M : Matrix := [[0], [1], [2]]
def t : Term := phi zero omega

theorem e1 : o? M = some t := rfl

theorem e3 (n : Nat) : o? (BMS.expand M n) = some (fsN t (n + 1)) :=
  e3_matrix (X := M) rfl (by decide) (c := 2) (by decide) rfl n

end «(0)(1)(2)»

/-! ### Row `(0)(1)(2)(3)` = ω^(ω^ω). -/
namespace «(0)(1)(2)(3)»

def M : Matrix := [[0], [1], [2], [3]]
def t : Term := phi zero (phi zero omega)

theorem e1 : o? M = some t := rfl

theorem e3 (n : Nat) : o? (BMS.expand M n) = some (fsN t (n + 1)) :=
  e3_matrix (X := M) rfl (by decide) (c := 3) (by decide) rfl n

end «(0)(1)(2)(3)»

/-! ### Successor rows `(0,0)(1,1)…(a,1)(0,0)` = `φ̄(a,0)+1`.

The `a = 1, 2, 3` instances of the F4 `b = 0` case of Evidence/StageB.lean
(`o?_M4z` / `esucc_M4z`), which proves the whole family. -/

namespace «(0,0)(1,1)(0,0)»

def M : Matrix := [[0,0],[1,1],[0,0]]
def t : Term := add (phi one zero) one

theorem e1 : o? M = some t := Evidence.StageB.o?_M4z 0

theorem esucc (n : Nat) : o? (BMS.expand M n) = some (predT t) :=
  Evidence.StageB.esucc_M4z 0 n

end «(0,0)(1,1)(0,0)»

namespace «(0,0)(1,1)(2,1)(0,0)»

def M : Matrix := [[0,0],[1,1],[2,1],[0,0]]
def t : Term := add (phi (ofNat 2) zero) one

theorem e1 : o? M = some t := Evidence.StageB.o?_M4z 1

theorem esucc (n : Nat) : o? (BMS.expand M n) = some (predT t) :=
  Evidence.StageB.esucc_M4z 1 n

end «(0,0)(1,1)(2,1)(0,0)»

namespace «(0,0)(1,1)(2,1)(3,1)(0,0)»

def M : Matrix := [[0,0],[1,1],[2,1],[3,1],[0,0]]
def t : Term := add (phi (ofNat 3) zero) one

theorem e1 : o? M = some t := Evidence.StageB.o?_M4z 2

theorem esucc (n : Nat) : o? (BMS.expand M n) = some (predT t) :=
  Evidence.StageB.esucc_M4z 2 n

end «(0,0)(1,1)(2,1)(3,1)(0,0)»

/-! ### Rows `(0,0)(1,1)…(a,1)(1,0)` = `φ̄(0,φ̄(a,0))`, instances of the F4 `b = 1` case
(`Evidence.StageB.e3_F4bfamily`; `a = 1` is Rows/ProofsB.lean's R2). -/

namespace «(0,0)(1,1)(2,1)(1,0)»

def M : Matrix := [[0,0],[1,1],[2,1],[1,0]]
def t : Term := phi zero (phi (ofNat 2) zero)

theorem e1 : o? M = some t := rfl

theorem e3 (n : Nat) : o? (BMS.expand M n) = some (fsN t (n + 1)) :=
  Evidence.StageB.e3_val4b 1 n

end «(0,0)(1,1)(2,1)(1,0)»

namespace «(0,0)(1,1)(2,1)(3,1)(1,0)»

def M : Matrix := [[0,0],[1,1],[2,1],[3,1],[1,0]]
def t : Term := phi zero (phi (ofNat 3) zero)

theorem e1 : o? M = some t := rfl

theorem e3 (n : Nat) : o? (BMS.expand M n) = some (fsN t (n + 1)) :=
  Evidence.StageB.e3_val4b 2 n

end «(0,0)(1,1)(2,1)(3,1)(1,0)»

/-! ### Row `(0,0)(1,1)(2,1)(2,0)` = `φ̄(1,φ̄(0,ζ₀))`, the `a = b = 2` instance of the
F4 case-C family (`Evidence.StageB.e3_F4cfamily`, whole `r = 0` column). -/

namespace «(0,0)(1,1)(2,1)(2,0)»

def M : Matrix := [[0,0],[1,1],[2,1],[2,0]]
def t : Term := phi one (phi zero (phi (ofNat 2) zero))

theorem e1 : o? M = some t := rfl

theorem e3 (n : Nat) : o? (BMS.expand M n) = some (fsN t (n + 1)) :=
  Evidence.StageB.e3_val4c 0 0 n

end «(0,0)(1,1)(2,1)(2,0)»

/-! ### Row `(0,0)(1,1)(2,1)(1,1)` = `φ̄(1,ζ₀)`, the `a = 2, b = 1` instance of the
F4 case-A family (`Evidence.StageB.e3_F4afamily`) — a no-shift row, so `e3` is the
4-part mutual-cofinality package. -/

namespace «(0,0)(1,1)(2,1)(1,1)»

def M : Matrix := [[0,0],[1,1],[2,1],[1,1]]
def t : Term := phi one (phi (ofNat 2) zero)

theorem e1 : o? M = some t := rfl

theorem e3 :
    (∀ n, o? (BMS.expand M n) = some (Evidence.StageB.oval4a 1 0 n))
    ∧ (∀ n, lt (Evidence.StageB.oval4a 1 0 n) t = true)
    ∧ (∀ n, lt (Evidence.StageB.oval4a 1 0 n) (fsN t (n + 1)) = true)
    ∧ (∀ m, lt (fsN t (m + 1)) (Evidence.StageB.oval4a 1 0 (m + 1)) = true) :=
  Evidence.StageB.e3_F4afamily 0 0

end «(0,0)(1,1)(2,1)(1,1)»

/-! ### Row `(0,0)(1,1)(2,1)(3,0)(4,1)` = `φ̄(2,ε₀)`, the `a = 2` instance of the
F5 family (`Evidence.StageB.e3_F5family`, the first ladder+two-columns family;
a shift-2 equality family, R5's convention). -/

namespace «(0,0)(1,1)(2,1)(3,0)(4,1)»

def M : Matrix := [[0,0],[1,1],[2,1],[3,0],[4,1]]
def t : Term := phi (ofNat 2) (phi one zero)

theorem e1 : o? M = some t := rfl

theorem e3 (n : Nat) : o? (BMS.expand M n) = some (fsN t (n + 2)) :=
  (Evidence.StageB.e3_F5family 1).1 n

end «(0,0)(1,1)(2,1)(3,0)(4,1)»

/-! ### Row `(0,0)(1,1)(2,0)(0,0)` = `φ̄(1,ω)+1` = `ε_ω+1`, the `a = 1` instance of the
class-IV successor shape (`Evidence.StageB.o?_M2z` / `esucc_M2z`). -/

namespace «(0,0)(1,1)(2,0)(0,0)»

def M : Matrix := [[0,0],[1,1],[2,0],[0,0]]
def t : Term := add (phi one omega) one

theorem e1 : o? M = some t := rfl

theorem esucc (n : Nat) : o? (BMS.expand M n) = some (predT t) :=
  Evidence.StageB.esucc_M2z 0 n

end «(0,0)(1,1)(2,0)(0,0)»

/-! ### Row `(0,0)(1,1)(2,0)(3,0)` = `φ̄(1,ω^ω)` = `ε_{ω^ω}`, the `a = 1` instance of the
F6 family (`Evidence.StageB.e3_F6family`, a shift-1 equality family). -/

namespace «(0,0)(1,1)(2,0)(3,0)»

def M : Matrix := [[0,0],[1,1],[2,0],[3,0]]
def t : Term := phi one (phi zero omega)

theorem e1 : o? M = some t := rfl

theorem e3 (n : Nat) : o? (BMS.expand M n) = some (fsN t (n + 1)) :=
  (Evidence.StageB.e3_F6family 0).1 n

end «(0,0)(1,1)(2,0)(3,0)»

/-! ### Row `(0,0)(1,1)(2,0)(2,0)` = `φ̄(1,ω²)` = `ε_{ω²}`, the `a = 1` instance of the
F7 family (`Evidence.StageB.e3_F7family`, a shift-1 equality family). -/

namespace «(0,0)(1,1)(2,0)(2,0)»

def M : Matrix := [[0,0],[1,1],[2,0],[2,0]]
def t : Term := phi one (phi zero (ofNat 2))

theorem e1 : o? M = some t := rfl

theorem e3 (n : Nat) : o? (BMS.expand M n) = some (fsN t (n + 1)) :=
  (Evidence.StageB.e3_F7family 0).1 n

end «(0,0)(1,1)(2,0)(2,0)»

/-! ## Row-linkage guards

Each guard pins the table rows of Rows/TM.lean that cite a namespace of this
file: some row cites the name, and EVERY row citing it carries exactly this
namespace's matrix and term.  This closes the only unchecked step of the table's
✅ column — the string link between a row and its proof. -/

def rowLinked (nm : String) (M : BMS.Matrix) (t : Term) : Bool :=
  Rows.rows.any (·.proof == nm) &&
  Rows.rows.all fun r => r.proof != nm || (r.m == M && r.t == t)

#guard rowLinked "«(empty)»" «(empty)».M «(empty)».t
#guard rowLinked "«(0)»" «(0)».M «(0)».t
#guard rowLinked "«(0)(0)»" «(0)(0)».M «(0)(0)».t
#guard rowLinked "«(0)(1)»" «(0)(1)».M «(0)(1)».t
#guard rowLinked "«(0)(1)(0)(1)»" «(0)(1)(0)(1)».M «(0)(1)(0)(1)».t
#guard rowLinked "«(0)(1)(1)»" «(0)(1)(1)».M «(0)(1)(1)».t
#guard rowLinked "«(0)(1)(2)»" «(0)(1)(2)».M «(0)(1)(2)».t
#guard rowLinked "«(0)(1)(2)(3)»" «(0)(1)(2)(3)».M «(0)(1)(2)(3)».t
#guard rowLinked "«(0,0)(1,1)(0,0)»" «(0,0)(1,1)(0,0)».M «(0,0)(1,1)(0,0)».t
#guard rowLinked "«(0,0)(1,1)(2,1)(0,0)»" «(0,0)(1,1)(2,1)(0,0)».M «(0,0)(1,1)(2,1)(0,0)».t
#guard rowLinked "«(0,0)(1,1)(2,1)(3,1)(0,0)»"
  «(0,0)(1,1)(2,1)(3,1)(0,0)».M «(0,0)(1,1)(2,1)(3,1)(0,0)».t
#guard rowLinked "«(0,0)(1,1)(2,1)(1,0)»" «(0,0)(1,1)(2,1)(1,0)».M «(0,0)(1,1)(2,1)(1,0)».t
#guard rowLinked "«(0,0)(1,1)(2,1)(3,1)(1,0)»"
  «(0,0)(1,1)(2,1)(3,1)(1,0)».M «(0,0)(1,1)(2,1)(3,1)(1,0)».t
#guard rowLinked "«(0,0)(1,1)(2,1)(2,0)»" «(0,0)(1,1)(2,1)(2,0)».M «(0,0)(1,1)(2,1)(2,0)».t
#guard rowLinked "«(0,0)(1,1)(2,1)(1,1)»" «(0,0)(1,1)(2,1)(1,1)».M «(0,0)(1,1)(2,1)(1,1)».t
#guard rowLinked "«(0,0)(1,1)(2,1)(3,0)(4,1)»"
  «(0,0)(1,1)(2,1)(3,0)(4,1)».M «(0,0)(1,1)(2,1)(3,0)(4,1)».t
#guard rowLinked "«(0,0)(1,1)(2,0)(0,0)»" «(0,0)(1,1)(2,0)(0,0)».M «(0,0)(1,1)(2,0)(0,0)».t
#guard rowLinked "«(0,0)(1,1)(2,0)(3,0)»" «(0,0)(1,1)(2,0)(3,0)».M «(0,0)(1,1)(2,0)(3,0)».t
#guard rowLinked "«(0,0)(1,1)(2,0)(2,0)»" «(0,0)(1,1)(2,0)(2,0)».M «(0,0)(1,1)(2,0)(2,0)».t

-- the rows proved in Rows/ProofsB.lean, pinned here (this file can import both)
#guard rowLinked "R1" Rows.ProofsB.R1.m0 Rows.ProofsB.R1.t0
#guard rowLinked "R2" Rows.ProofsB.R2.m0 Rows.ProofsB.R2.t0
#guard rowLinked "R3" Rows.ProofsB.R3.m0 Rows.ProofsB.R3.t0
#guard rowLinked "R4" Rows.ProofsB.R4.m0 Rows.ProofsB.R4.t0
#guard rowLinked "R5" Rows.ProofsB.R5.m0 Rows.ProofsB.R5.t0
#guard rowLinked "R6" Rows.ProofsB.R6.m0 Rows.ProofsB.R6.t0
#guard rowLinked "R7" Rows.ProofsB.R7.m0 Rows.ProofsB.R7.t0
#guard rowLinked "R8" Rows.ProofsB.R8.m0 Rows.ProofsB.R8.t0
#guard rowLinked "R9" Rows.ProofsB.R9.m0 Rows.ProofsB.R9.t0

end Rows.Proofs
