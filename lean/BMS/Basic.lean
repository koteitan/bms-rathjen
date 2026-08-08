/-
BMS/Basic.lean — representation of Bashicu matrices and basic operations

Source: Koteitan, "バシク行列の数式的定義" ("A formula-only definition of the Bashicu
matrices", Googology Wiki user blog).  Cited below as "the formal definition".
The BMS version is BM4.

A matrix S = S_0 S_1 ... S_{X-1} is a list of columns.
A column S_x = (S_{x0}, ..., S_{x(Y-1)}) lists its entries from the top row down.
-/

namespace BMS

/-- A column: entries from row 0 (top) downwards. -/
abbrev Col := List Nat

/-- A matrix: columns from left to right. -/
abbrev Matrix := List Col

/-- All columns have height `h`. -/
def WF (h : Nat) (M : Matrix) : Prop := ∀ c ∈ M, c.length = h

/-- The entry S_{xy}.  Out of range reads as 0 (never consulted on standard input). -/
def ent (M : Matrix) (x y : Nat) : Nat := (M.getD x []).getD y 0

/-- The initial matrix (0,...,0)(1,...,1) of height `h`; the origin of the table. -/
def init (h : Nat) : Matrix := [List.replicate h 0, List.replicate h 1]

/-- Printing in the "(0,0,0)(1,1,1)" format (the same syntax as yaBMS). -/
def showMatrix (M : Matrix) : String :=
  String.join (M.map fun c => "(" ++ String.intercalate "," (c.map toString) ++ ")")

/-- Whitespace trimming (in v4.30 `trimAscii` yields a slice, so convert back). -/
def trimS (s : String) : String := s.trimAscii.toString

/-- Parsing of the "(0,0,0)(1,1,1)" format.  The empty string is the empty matrix. -/
def parseMatrix (s : String) : Option Matrix :=
  let parts := (((trimS s).splitOn ")").map trimS).filter (· ≠ "")
  parts.mapM fun p => do
    guard (p.startsWith "(")
    ((trimS (p.drop 1).toString).splitOn ",").mapM (fun w => (trimS w).toNat?)

end BMS
