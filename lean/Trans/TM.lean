/-
Trans/TM.lean — 翻訳関数 o : BMS → 𝔗(M) (段階的構築)

方針: 対応表の予想 (BM4-Analysis 等) は大きい側で信頼できないため、
o は小さい領域から段階的に定義し、各段階を E3 (展開 ↔ 基本列) の
計算検査 (Evidence/Bisim.lean) で検証しながら拡張する。

添字の規約: BMS の M[n] はコピー B(0)…B(n) (n+1 個) を並べるため、
T(M) 側の基本列とは添字が 1 ずれる:
    o(M[n]) = (o M)[n+1]
E3 の行ごとの補題もこの形で立てる。

現在の定義域:
  Stage A: 1 行有効領域 (行 0 以外が全零) = ε₀ 未満の CNF 領域
-/
import BMS
import TM

namespace Trans

open TM (Term)
open TM.Term

/-- 行列の行 0 (先頭行) の並び -/
def row0 (M : BMS.Matrix) : List Nat := M.map (·.getD 0 0)

/-- 行 0 以外が全零 (1 行有効) か -/
def onlyRow0 (M : BMS.Matrix) : Bool :=
  M.all fun c => (c.drop 1).all (· == 0)

/-- 0 の直前で区切ってブロックに分割する:
    (0,1,2,0,1) → [[0,1,2],[0,1]]。標準形の 1 行数列は 0 始まりのブロックの並び。 -/
def blocks0 : List Nat → List (List Nat)
  | [] => []
  | x :: rest =>
    match blocks0 rest, rest.head? with
    | acc, some h => if h == 0 then [x] :: acc else (x :: acc.headD []) :: acc.tail
    | _, none => [[x]]

/-- 原始数列 (1 行) → CNF 項。
    o(ブロック列) = Σ_i ω^{o(ブロック i の先頭 0 を除き全体を -1)}  -/
def oPrAux : Nat → List Nat → Term
  | 0, _ => zero
  | fuel + 1, s =>
    if s.isEmpty then zero
    else
      let bs := blocks0 s
      (bs.map fun b =>
        omegaNF (oPrAux fuel ((b.drop 1).map (· - 1)))).foldr plus zero

/-- Stage A: 1 行有効行列の翻訳 -/
def oPr (M : BMS.Matrix) : Term := oPrAux (M.length + 1) (row0 M)

/-- 翻訳関数 (部分)。定義域を段階的に広げる。
    定義域外は none (行の検証は bisim による直接ペアで行う)。 -/
def o? (M : BMS.Matrix) : Option Term :=
  if onlyRow0 M then some (oPr M) else none

end Trans
