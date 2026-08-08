/-
BMS/Expand.lean — the BM4 expansion rule

A faithful transcription of the formal definition (BM4):

  parent:      P_0(x)     = max{ p | S_{p0} < S_{x0} ∧ p < x }
               P_y(x)     = max{ p | S_{py} < S_{xy} ∧ ∃a>0, p = (P_{y-1})^a(x) }  (y > 0)
  lowest nonzero row:
               t          = max{ y | S_{(X-1)y} > 0 }
  bad root:    r          = P_t(X-1)
  good part:   G          = S_0 ... S_{r-1}
  ascension amount:
               Δ_y        = S_{(X-1)y} - S_{ry}  (y < t),  0  (y ≥ t)
  ascension matrix:
               A_{xy}     = 1  if ∃a≥0, r = (P_y)^a(r+x),  0  otherwise
  bad part:    B_{xy}(a)  = S_{(r+x)y} + a·Δ_y·A_{xy}      (0 ≤ x ≤ X-2-r)
  expansion:   S[n]       = S_0...S_{X-2}                   (last column all zero)
               S[n]       = G B(0) B(1) ... B(n)            (otherwise)

The activation function is not fixed: the copy bound `n` is an argument of the
expansion (blocks B(0)...B(n), i.e. n+1 of them — the same convention as yaBMS
"(...)[n]").  This is what lets a matrix be read as an ordinal notation without
carrying a bracket.
-/
import BMS.Basic

namespace BMS

/-- Proper ancestors obtained by iterating `f` up to `fuel` times (nearest first).
    Since P_y(x) < x, `fuel = x` is enough. -/
def iterParent (f : Nat → Option Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, x =>
    match f x with
    | none => []
    | some p => p :: iterParent f fuel p

/-- The parent P_y(x) at row `y`; `none` if there is none. -/
def parent (M : Matrix) : Nat → Nat → Option Nat
  | 0, x =>
    ((List.range x).filter (fun p => decide (ent M p 0 < ent M x 0))).max?
  | y + 1, x =>
    ((iterParent (parent M y) x x).filter
      (fun p => decide (ent M p (y + 1) < ent M x (y + 1)))).max?

/-- The lowest nonzero row of a column (`none` if the column is all zero). -/
def lnz (c : Col) : Option Nat :=
  ((List.range c.length).filter (fun y => decide (c.getD y 0 > 0))).max?

/-- The ascension amount Δ_y. -/
def delta (M : Matrix) (r t y : Nat) : Nat :=
  if y < t then ent M (M.length - 1) y - ent M r y else 0

/-- The ascension matrix A_{xy}, taking the column index j = r + x:
    is `r` an ancestor (in a ≥ 0 steps) of `j` at row `y`? -/
def ascends (M : Matrix) (r j y : Nat) : Bool :=
  j == r || (iterParent (parent M y) j j).contains r

/-- The BM4 expansion S[n].
    `none` for the empty matrix, or when there is no bad root (non-standard input). -/
def expand? (M : Matrix) (n : Nat) : Option Matrix := do
  let L ← M.getLast?
  match lnz L with
  | none =>
    -- successor: drop the last column when it is all zero
    pure M.dropLast
  | some t =>
    let X := M.length
    let r ← parent M t (X - 1)
    let h := L.length
    let bad (a : Nat) : Matrix :=
      (List.range (X - 1 - r)).map fun x =>
        let j := r + x
        (List.range h).map fun y =>
          ent M j y + a * delta M r t y * (if ascends M r j y then 1 else 0)
    pure (M.take r ++ ((List.range (n + 1)).map bad).flatten)

/-- A total version of the expansion (the empty matrix where undefined).
    Statements of theorems should use `expand?`. -/
def expand (M : Matrix) (n : Nat) : Matrix := (expand? M n).getD []

/-- Classification into zero, successor and limit. -/
inductive Kind | zero | succ | lim
deriving DecidableEq, Repr

def kind (M : Matrix) : Kind :=
  match M.getLast? with
  | none => .zero
  | some L => match lnz L with
    | none => .succ
    | some _ => .lim

end BMS
