/-
BMS/Order.lean — the lexicographic order on matrices

Columns are compared left to right, entries within a column top to bottom.
Whichever side runs out on a common prefix is the smaller one.
This is the order implemented by yaBMS `-c` (compare).
-/
import BMS.Basic

namespace BMS

/-- Comparison of columns: lexicographic from the top row. -/
def cmpCol : Col → Col → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (compare a b).then (cmpCol as bs)

/-- Comparison of matrices: lexicographic from the leftmost column. -/
def cmpM : Matrix → Matrix → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | c :: cs, d :: ds => (cmpCol c d).then (cmpM cs ds)

/-- The strict order M <_B N. -/
def ltB (M N : Matrix) : Prop := cmpM M N = .lt

instance : DecidablePred (fun p : Matrix × Matrix => ltB p.1 p.2) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

instance (M N : Matrix) : Decidable (ltB M N) :=
  inferInstanceAs (Decidable (_ = _))

end BMS
