/-
BMS/Standard.lean — 標準形 = 初期行列からの展開到達性

標準形の定義: (0,...,0)(1,...,1) (高さ h) から展開を有限回
(各回のコピー数 n は任意) 施して得られる行列。

行 DB では到達の witness (展開パス) を具体的に持たせ、
reachBy の計算 (decide/rfl) で標準形であることを検査する。
-/
import BMS.Expand

namespace BMS

/-- M から N へ展開で到達できる -/
inductive Reach : Matrix → Matrix → Prop
  | refl (M : Matrix) : Reach M M
  | step {M N N' : Matrix} (n : Nat) :
      Reach M N → expand? N n = some N' → Reach M N'

theorem Reach.trans {A B C : Matrix} (hab : Reach A B) (hbc : Reach B C) :
    Reach A C := by
  induction hbc with
  | refl => exact hab
  | step n _ he ih => exact Reach.step n ih he

/-- 標準形 (高さ h): 初期行列から到達可能 -/
def Standard (h : Nat) (M : Matrix) : Prop := Reach (init h) M

/-- 展開パス (各ステップのコピー数) に沿って計算する witness 評価器 -/
def reachBy (M : Matrix) : List Nat → Option Matrix
  | [] => some M
  | n :: ns =>
    match expand? M n with
    | none => none
    | some N => reachBy N ns

/-- witness の健全性: reachBy が成功すれば Reach が成り立つ -/
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
