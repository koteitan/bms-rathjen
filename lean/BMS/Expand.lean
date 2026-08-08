/-
BMS/Expand.lean — BM4 の展開規則

数式的定義 (BM4) に忠実な実装:

  親:        P_0(x)     = max{ p | S_{p0} < S_{x0} ∧ p < x }
             P_y(x)     = max{ p | S_{py} < S_{xy} ∧ ∃a>0, p = (P_{y-1})^a(x) }   (y > 0)
  非零最下行: t          = max{ y | S_{(X-1)y} > 0 }
  bad root:  r          = P_t(X-1)
  良い部分:   G          = S_0 ... S_{r-1}
  上昇量:     Δ_y        = S_{(X-1)y} - S_{ry}  (y < t),  0  (y ≥ t)
  上昇行列:   A_{xy}     = 1  if ∃a≥0, r = (P_y)^a(r+x),  0  otherwise
  悪い部分:   B_{xy}(a)  = S_{(r+x)y} + a·Δ_y·A_{xy}      (0 ≤ x ≤ X-2-r)
  展開:      S[n]       = S_0...S_{X-2}                    (最後列が全零のとき)
             S[n]       = G B(0) B(1) ... B(n)            (それ以外)

活性化関数は固定せず、コピー上限 n を展開の引数に取る
(B(0)...B(n) の n+1 ブロック。yaBMS の "(...)[n]" と同じ)。
これにより行列は [n] なしの順序数表記として扱える。
-/
import BMS.Basic

namespace BMS

/-- f を fuel 回まで繰り返し辿って得る真先祖リスト (近い順)。
    P_y(x) < x なので fuel = x で十分。 -/
def iterParent (f : Nat → Option Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, x =>
    match f x with
    | none => []
    | some p => p :: iterParent f fuel p

/-- 行 y での親 P_y(x)。存在しなければ none。 -/
def parent (M : Matrix) : Nat → Nat → Option Nat
  | 0, x =>
    ((List.range x).filter (fun p => decide (ent M p 0 < ent M x 0))).max?
  | y + 1, x =>
    ((iterParent (parent M y) x x).filter
      (fun p => decide (ent M p (y + 1) < ent M x (y + 1)))).max?

/-- 列 c の非零最下行 (全零なら none) -/
def lnz (c : Col) : Option Nat :=
  ((List.range c.length).filter (fun y => decide (c.getD y 0 > 0))).max?

/-- 上昇量 Δ_y -/
def delta (M : Matrix) (r t y : Nat) : Nat :=
  if y < t then ent M (M.length - 1) y - ent M r y else 0

/-- 上昇行列 A_{xy} (列番号 j = r + x で受ける):
    r が j の行 y での先祖 (a ≥ 0 回) かどうか -/
def ascends (M : Matrix) (r j y : Nat) : Bool :=
  j == r || (iterParent (parent M y) j j).contains r

/-- BM4 の展開 S[n]。
    空行列、または bad root が存在しない (非標準) 場合は none。 -/
def expand? (M : Matrix) (n : Nat) : Option Matrix := do
  let L ← M.getLast?
  match lnz L with
  | none =>
    -- 後続: 最後列が全零なら落とす
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

/-- 展開の全域版 (未定義は空行列)。定理の記述用は expand? を使う。 -/
def expand (M : Matrix) (n : Nat) : Matrix := (expand? M n).getD []

/-- 零・後続・極限の分類 -/
inductive Kind | zero | succ | lim
deriving DecidableEq, Repr

def kind (M : Matrix) : Kind :=
  match M.getLast? with
  | none => .zero
  | some L => match lnz L with
    | none => .succ
    | some _ => .lim

end BMS
