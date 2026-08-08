/-
BMS/Order.lean — 行列の辞書式順序

列を左から右へ、列内は上の行から下の行へ比較する。
共通接頭辞で尽きた側が小さい。yaBMS の -c (compare) と同じ順序。
-/
import BMS.Basic

namespace BMS

/-- 列の比較: 上の行から辞書式 -/
def cmpCol : Col → Col → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (compare a b).then (cmpCol as bs)

/-- 行列の比較: 左の列から辞書式 -/
def cmpM : Matrix → Matrix → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | c :: cs, d :: ds => (cmpCol c d).then (cmpM cs ds)

/-- 狭義順序 M <_B N -/
def ltB (M N : Matrix) : Prop := cmpM M N = .lt

instance : DecidablePred (fun p : Matrix × Matrix => ltB p.1 p.2) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

instance (M N : Matrix) : Decidable (ltB M N) :=
  inferInstanceAs (Decidable (_ = _))

end BMS
