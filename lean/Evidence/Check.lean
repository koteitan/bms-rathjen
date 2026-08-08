/-
Evidence/Check.lean — o の定義域上の全数検査 (E1/E2/E3 のインスタンス検査器)

o が定義されている領域のコーパス (展開で到達する行列の有限集合) に対し、
T(M) 側の決定可能な順序だけを使って検査する:

  checkKind : 零・後続・極限の分類が o で保たれる
  checkSucc : 後続で o(pred M) = pred (o M)
  checkE2   : 順序埋め込み ltB M N ↔ o M <_T o N (全ペア)
  checkE3i  : 極限 M で
                (a) o(M[n]) < o(M)
                (b) ∀n ∃k. o(M[n]) < (o M)[k]   (展開像が基本列に抜かれる)
                (c) ∀k ∃n. (o M)[k] < o(M[n])   (基本列が展開像に抜かれる)
              — E3 の相互共終形。(b)(c) が両立すれば両列の上限は一致する。

BMS の展開列と fs の列は同じ順序数への異なる共終列になり得るため
(ε₁ に対する ε₀-タワーと ω-タワー)、E3 は等式ではなくこの相互共終形で立てる。
-/
import BMS
import TM
import Trans.TM

namespace Evidence

open BMS (Matrix)
open TM (Term)
open TM.Term

/-- 1 段の展開像 (幅 w) -/
def stepAll (w : Nat) (ms : List Matrix) : List Matrix :=
  ms.flatMap fun m => (List.range w).filterMap fun n => BMS.expand? m n

/-- seed から深さ d・幅 w で到達する行列のコーパス (重複除去) -/
def corpus (seed : Matrix) (d w : Nat) : List Matrix :=
  (List.range d).foldl (fun acc _ => (acc ++ stepAll w acc).eraseDups) [seed]

/-- 分類の保存 -/
def checkKind (o : Matrix → Term) (c : List Matrix) : Bool :=
  c.all fun m =>
    match BMS.kind m, kindT (o m) with
    | .zero, .isZero => true
    | .succ, .isSucc => true
    | .lim, .isLim => true
    | _, _ => false

/-- 後続の前者の対応 -/
def checkSucc (o : Matrix → Term) (c : List Matrix) : Bool :=
  c.all fun m =>
    BMS.kind m != .succ ||
    (match BMS.expand? m 0 with
     | some m' => o m' == predT (o m)
     | none => false)

/-- E2 インスタンス: 順序埋め込み (コーパス内全ペア) -/
def checkE2 (o : Matrix → Term) (c : List Matrix) : Bool :=
  c.all fun m1 => c.all fun m2 =>
    (BMS.cmpM m1 m2 == .lt) == lt (o m1) (o m2)

/-- E3 相互共終形 (幅 w、追い越しの探索幅 w') -/
def checkE3i (o : Matrix → Term) (c : List Matrix) (w w' : Nat) : Bool :=
  c.all fun m =>
    BMS.kind m != .lim ||
    (let t := o m
     ((List.range w).all fun n =>
       match BMS.expand? m n with
       | some m' => lt (o m') t
       | none => false)
     &&
     ((List.range w).all fun n =>
       match BMS.expand? m n with
       | some m' => (List.range w').any fun k => lt (o m') (fsN t (k + 1))
       | none => false)
     &&
     ((List.range w).all fun k =>
       (List.range w').any fun n =>
         match BMS.expand? m n with
         | some m' => lt (fsN t (k + 1)) (o m')
         | none => false))

/-- 全検査をまとめて実行 -/
def checkAll (o : Matrix → Term) (c : List Matrix) (w w' : Nat) : Bool :=
  checkKind o c && checkSucc o c && checkE2 o c && checkE3i o c w w'

end Evidence
