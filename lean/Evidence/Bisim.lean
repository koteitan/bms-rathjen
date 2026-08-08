/-
Evidence/Bisim.lean — 双模倣検査器 (E3 の計算版)

行列 M と項 t の対応主張「M = t」を、o の式が無くても直接検査する:
  - 種類 (零・後続・極限) が一致し、
  - 後続なら前者同士が対応し、
  - 極限なら各 n < width で M[n] と t[n+1] が対応する
ことを深さ fuel まで再帰的に確かめる。

添字規約 (Trans/TM.lean 参照): BMS の M[n] は n+1 個のコピーなので
T(M) 側は t[n+1] と比較する。

これは有限深さの検査であり、行ごとの E3 補題 (∀n) の代わりにはならないが、
o の設計段階で誤対応を高感度で弾くフィルタとして働く。
深さ d・幅 w で約 w^d 個の対を検査する。
-/
import BMS
import TM

namespace Evidence

open BMS (Matrix)
open TM (Term)
open TM.Term

/-- M と t の有限深さ双模倣検査 -/
def bisim (fuel : Nat) (M : Matrix) (t : Term) (width : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 =>
    match BMS.kind M, kindT t with
    | .zero, .isZero => true
    | .succ, .isSucc =>
      -- 後続: 前者同士 (BMS 側は最後列を落とすだけなので n は任意)
      (match BMS.expand? M 0 with
       | some M' => bisim fuel M' (predT t) width
       | none => false)
    | .lim, .isLim =>
      (List.range width).all fun n =>
        match BMS.expand? M n with
        | some M' => bisim fuel M' (fsN t (n + 1)) width
        | none => false
    | _, _ => false

/-- 既定パラメータ (深さ 5, 幅 3) -/
def bisim5 (M : Matrix) (t : Term) : Bool := bisim 5 M t 3

/-!
## 跨システムの値同値検査を採用しない理由 (記録)

「val(M) = val(t)」を展開・基本列の相互共終で直接検査する方式 (eqv) を
試作したが、有限 fuel では矛盾へ到達する前に打ち切りとなり、誤対応
(例: ε₁ の行列と ε₂ の項) も通してしまう判別力しか得られなかった。
行列と項の比較は展開の深い追跡でしか出来ないためである。

そこで対応の検証は o を経由して T(M) 側の決定可能な順序で行う
(Evidence/Check.lean):
  - E2 インスタンス: コーパス上の順序埋め込み検査
  - E3 相互共終形: o(M[n]) の列と fsN (o M) の列が互いに追い越し合う
strict bisim (上) は fs の列が BMS の展開列と一致する領域 (CNF 領域) での
検査器として引き続き有効。
-/

end Evidence
