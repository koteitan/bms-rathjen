/-
Rows/Selected.lean — the E-proof shortlist, with each row's statement pinned

WHY THIS FILE EXISTS.  The table's rightmost column names 23 rows to prove E for.  A
selection in prose is not a target: **the E3 index is per row**, and applying a uniform
`+1` against `fsN` is the mistake this repository has made more than once (see the header
of `Rows/TM.lean`).  So before any proof is attempted, every selected row that `o?` reaches
gets its index MEASURED and pinned here, and its E1 proved.

WHAT IS PROVED HERE.  `e1 : o? M = some t := rfl` for all six rows — the translation is
defined on the matrix and gives the table's term.  E3 is not proved for any row; for each
row its exact statement is here with the index `k` fixed and verified on `n < 8`, together
with a control that the neighbouring indices fail.

FAMILY 1 IS FURTHER ALONG: its E3 is split into three, and two of the three are proved.
The matrix side (`expand_F1`) and the term side (`fsN_t`) are theorems; `e3_of` shows they
reduce E3 to the value side alone (`valClaim`), which is the half every `e3_val*` of
`Evidence/StageB.lean` spends a hundred lines on.

WHICH ROWS.  The six rows of the shortlist that `o?` reaches AND agrees with the table on.
They are exactly the rows of families 1–3 of `diff.md`, i.e. six of the nine where an
external table disagrees with this one.  That is a coincidence worth stating: the disputed
rows are the ones the existing machinery can still speak about, because `o?` was withdrawn
only from `(0,0)(1,1)(2,1)(1,1)(2,1)` upward and families 1–3 sit below it.  The remaining
selected rows are out of `o?`'s reach — the three of family 4 and `φ̄(ω,0)`, `φ̄(ε₀,0)`, `Γ₀`
are in the withdrawn region (`o?` answers, and is wrong), and the six `(2,2)` rows have no
`o?` value at all.  They need the `oR` equation layer, which does not exist yet.

THE INDEX IS NOT UNIFORM, measured:  1, 1, 2, (none), 1, 1.

THE FOURTH ROW HAS NO UNIFORM INDEX AT ALL, and that is the sharpest thing in this file.
`(0,0)(1,1)(2,1)(1,1)(2,0)(3,1)(4,1)(3,1)(4,0)(5,1)(6,1)(5,0)` agrees with `fsN` at shift 2
from `n = 1` on, but its 0-th expansion is **not a member of `fsN t` at all** (searched to
30).  `fsN t 1` is `ζ₀` and `fsN t 2` jumps past the 0-th expansion value, which lies
strictly between them.  So this row cannot get a ✅ with `fsN` as its fundamental sequence:
`Certified.lim` demands `fs' n` be the certified value of the n-th expansion for EVERY n.
It needs a bespoke sequence, like the ε₁ row (`R3`) already does.
-/
import Rows.TM
import Rows.Proofs

namespace Rows
namespace Selected

open BMS (Matrix)
open TM (Term)
open TM.Term
open Trans (o?)

/-! ## diff.md 族 1 -/

namespace F1

def M : Matrix := [[0,0],[1,1],[2,0],[1,1],[1,0],[2,1],[3,0],[1,0],[2,1]]
def t : Term := phi zero (add (phi (phi zero zero) (add (phi zero (phi zero zero)) (phi zero zero)))
  (add (phi (phi zero zero) (phi zero (phi zero zero))) (phi (phi zero zero) zero)))

theorem e1 : o? M = some t := rfl

/-- E3 の主張。**未証明**。添字は測定値で、`n < 8` で確かめてある。 -/
def e3Claim : Prop := ∀ n, o? (BMS.expand M n) = some (fsN t (n + 1))

#guard kindT t == KindT.isLim
#guard (List.range 8).all fun n => o? (BMS.expand M n) == some (fsN t (n + 1))
-- CTRL 隣の添字では合わない (合ってしまうなら試験が効いていない)
#guard (List.range 8).any fun n => !(o? (BMS.expand M n) == some (fsN t n))
#guard (List.range 8).any fun n => !(o? (BMS.expand M n) == some (fsN t (n + 2)))

/-! ### 分解: E3 を 3 つに割る

行列の側は `M[n] = P ++ (2,0)(3,0)…(n+1,0)` で、値の側はその梯子が ω 塔を積む。
項の側は `fsN t` が最後の加数 ε₀ の基本列を走る。**項の側だけは今証明できる**ので、
残る 2 つが何であるかがはっきりする。 -/

/-- 展開の共通の頭。`M` から最後の `(2,1)` を落としたもの。 -/
def P : Matrix := [[0,0],[1,1],[2,0],[1,1],[1,0],[2,1],[3,0],[1,0]]
/-- 梯子 `(o,0)(o+1,0)…`、`k` 本。 -/
def zeroLad (o : Nat) : Nat → Matrix
  | 0 => []
  | k + 1 => ([o,0] : BMS.Col) :: zeroLad (o+1) k

def A : Term := phi (phi zero zero) (add (phi zero (phi zero zero)) (phi zero zero))
def B : Term := phi (phi zero zero) (phi zero (phi zero zero))
def e0 : Term := phi (phi zero zero) zero

theorem t_eq : t = phi zero (add A (add B e0)) := rfl

/-- **項の側。証明済み。** `t` の基本列は最後の加数 ε₀ の基本列を走る。 -/
theorem fsN_add (a b : Term) (n : Nat) : fsN (add a b) n = plus a (fsN b n) := by rw [fsN]

theorem fsN_t (n : Nat) : fsN t n = phiNF zero (plus A (plus B (fsN e0 n))) := by
  rw [t_eq, Rows.ProofsB.fsN_phi_lim (a := zero) (b := add A (add B e0)) rfl rfl n,
      fsN_add, fsN_add]

/-- 行列の側。 -/
def expandClaim : Prop := ∀ n, BMS.expand M n = P ++ zeroLad 2 n

/-! #### 行列の側の証明

`expand?` を `M` で計算すると、最後の列 `(2,1)` の `lnz` が 1、その親が列 7 で、
悪い部分は 1 列だけ、上昇量は行 0 で 1、行 1 で 0 になる。つまり `a` 番目の複製は
`(1+a, 0)` の 1 列である。あとは `flatten ∘ map` を梯子に直せばよい。 -/

theorem zeroLad_succ : ∀ (k o : Nat), zeroLad o (k+1) = zeroLad o k ++ [([o+k, 0] : BMS.Col)]
  | 0, o => by show _ = [] ++ _; rw [List.nil_append]; simp [zeroLad]
  | k+1, o => by
    show ([o,0] : BMS.Col) :: zeroLad (o+1) (k+1) = ([o,0] : BMS.Col) :: zeroLad (o+1) k ++ _
    rw [zeroLad_succ k (o+1)]
    have h : o + 1 + k = o + (k+1) := by omega
    rw [h]
    rfl

theorem lad_flatten : ∀ k,
    ((List.range k).map fun a => ([[1+a,0]] : Matrix)).flatten = zeroLad 1 k
  | 0 => rfl
  | k+1 => by
    rw [List.range_succ, List.map_append, List.flatten_append, lad_flatten k,
        zeroLad_succ k 1]
    rfl

/-- **行列の側。証明済み。** -/
theorem expand_F1 (n : Nat) : BMS.expand M n = P ++ zeroLad 2 n := by
  show (BMS.expand? M n).getD [] = _
  have h : BMS.expand? M n
      = some (M.take 7 ++
          ((List.range (n+1)).map fun a => ([[1 + a*1*1, 0 + a*0*1]] : Matrix)).flatten) := rfl
  have hf : (fun a => ([[1 + a*1*1, 0 + a*0*1]] : Matrix))
      = (fun a => ([[1+a,0]] : Matrix)) := by funext a; simp
  rw [h, hf, lad_flatten (n+1)]
  rfl
/-- 値の側。**未証明。** -/
def valClaim : Prop := ∀ n, o? (P ++ zeroLad 2 n) = some (phiNF zero (plus A (plus B (fsN e0 (n+1)))))

/-- 3 つが揃えば E3 が出る。**この含意だけは証明してある**ので、残りは 2 つの補題である。 -/
theorem e3_of (hv : valClaim) : e3Claim := by
  intro n
  rw [expand_F1 n, hv n, fsN_t (n+1)]

#guard (List.range 8).all fun n => BMS.expand M n == P ++ zeroLad 2 n
#guard (List.range 8).all fun n =>
  o? (P ++ zeroLad 2 n) == some (phiNF zero (plus A (plus B (fsN e0 (n+1)))))
-- CTRL 頭を 1 列削れば合わなくなる
#guard (List.range 8).any fun n => !(BMS.expand M n == P.dropLast ++ zeroLad 2 n)

end F1

/-! ## diff.md 族 2 -/

namespace F2a

def M : Matrix := [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[1,1],[2,0]]
def t : Term := phi (phi zero zero) (add (phi (phi zero zero)
  (phi (add (phi zero zero) (phi zero zero)) zero)) (phi zero (phi zero zero)))

theorem e1 : o? M = some t := rfl

def e3Claim : Prop := ∀ n, o? (BMS.expand M n) = some (fsN t (n + 1))

#guard kindT t == KindT.isLim
#guard (List.range 8).all fun n => o? (BMS.expand M n) == some (fsN t (n + 1))
#guard (List.range 8).any fun n => !(o? (BMS.expand M n) == some (fsN t n))
#guard (List.range 8).any fun n => !(o? (BMS.expand M n) == some (fsN t (n + 2)))

end F2a

namespace F2b

def M : Matrix := [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[1,1],[2,0],[3,1]]
def t : Term := phi (phi zero zero) (add (phi (phi zero zero)
  (phi (add (phi zero zero) (phi zero zero)) zero)) (phi (phi zero zero) zero))

theorem e1 : o? M = some t := rfl

/-- **添字は 2 で、隣の F2a は 1 である。** 同じ族の隣り合う 2 行で違う。 -/
def e3Claim : Prop := ∀ n, o? (BMS.expand M n) = some (fsN t (n + 2))

#guard kindT t == KindT.isLim
#guard (List.range 8).all fun n => o? (BMS.expand M n) == some (fsN t (n + 2))
#guard (List.range 8).any fun n => !(o? (BMS.expand M n) == some (fsN t (n + 1)))
#guard (List.range 8).any fun n => !(o? (BMS.expand M n) == some (fsN t (n + 3)))

end F2b

/-! ## diff.md 族 3 -/

namespace F3a

def M : Matrix :=
  [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[4,0],[5,1],[6,1],[5,0]]
def t : Term := phi (phi zero zero) (phi (phi zero zero) (phi zero (phi zero
  (phi (add (phi zero zero) (phi zero zero)) zero))))

theorem e1 : o? M = some t := rfl

/-- **この行だけ一様な添字が無い。** `n ≥ 1` では 2 で合うが、`n = 0` の値は `fsN t` の
    項ではない (30 項まで探して不在)。`fsN t 1 = ζ₀` と `fsN t 2` の間に落ちる。 -/
def e3ClaimFrom1 : Prop := ∀ n, o? (BMS.expand M (n + 1)) = some (fsN t (n + 2))

#guard kindT t == KindT.isLim
#guard (List.range 8).all fun n => o? (BMS.expand M (n + 1)) == some (fsN t (n + 2))
-- n = 0 は基本列の上に無い。**これが「一様な添字が無い」の実体である。**
#guard (List.range 30).all fun j => !(o? (BMS.expand M 0) == some (fsN t j))
-- そしてその値は fsN t 1 と fsN t 2 の間にある (飛ばされている)
#guard match o? (BMS.expand M 0) with
       | some v => lt (fsN t 1) v && lt v (fsN t 2)
       | none => false

end F3a

namespace F3b

def M : Matrix :=
  [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[4,0],[5,1],[6,1],[5,0],[6,1]]
def t : Term := phi (phi zero zero) (phi (phi zero zero) (phi zero (phi zero
  (add (phi (add (phi zero zero) (phi zero zero)) zero) (phi (phi zero zero) zero)))))

theorem e1 : o? M = some t := rfl

def e3Claim : Prop := ∀ n, o? (BMS.expand M n) = some (fsN t (n + 1))

#guard kindT t == KindT.isLim
#guard (List.range 8).all fun n => o? (BMS.expand M n) == some (fsN t (n + 1))
#guard (List.range 8).any fun n => !(o? (BMS.expand M n) == some (fsN t n))
#guard (List.range 8).any fun n => !(o? (BMS.expand M n) == some (fsN t (n + 2)))

end F3b

namespace F3c

def M : Matrix :=
  [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[4,0],[5,1],[6,1],[5,0],[6,1],[7,1]]
def t : Term := phi (phi zero zero) (phi (phi zero zero) (phi zero (phi zero
  (add (phi (add (phi zero zero) (phi zero zero)) zero)
    (phi (add (phi zero zero) (phi zero zero)) zero)))))

theorem e1 : o? M = some t := rfl

def e3Claim : Prop := ∀ n, o? (BMS.expand M n) = some (fsN t (n + 1))

#guard kindT t == KindT.isLim
#guard (List.range 8).all fun n => o? (BMS.expand M n) == some (fsN t (n + 1))
#guard (List.range 8).any fun n => !(o? (BMS.expand M n) == some (fsN t n))
#guard (List.range 8).any fun n => !(o? (BMS.expand M n) == some (fsN t (n + 2)))

end F3c

/-! ## 行との対応

**この 6 つが表の行そのものであることを固定する。** 名前で結んでいると、表の行が動いた
ときに証明が別の行を指したまま通る。 -/

def isRow (M : Matrix) (t : Term) : Bool := rows.any fun r => r.m == M && r.t == t

#guard isRow F1.M F1.t
#guard isRow F2a.M F2a.t
#guard isRow F2b.M F2b.t
#guard isRow F3a.M F3a.t
#guard isRow F3b.M F3b.t
#guard isRow F3c.M F3c.t
-- CTRL 存在しない対は結ばれない
#guard !(isRow F1.M F2a.t)

/-! ## 残りの選定行が、なぜここに無いか

`o?` が届かないか、届いても撤回領域で誤った値を返す。**測定して数で固定する。** -/

def selected : List Row := rows.filter fun r => r.sel != ""
def reached : List Row := selected.filter fun r => o? r.m == some r.t

#guard selected.length == 23
#guard reached.length == 11            -- 既証明 5 + ここの 6
#guard (reached.filter fun r => r.proof == "").length == 6
-- `o?` が値を返すのに表と違う行 (撤回領域)、と `o?` が未定義の行
#guard (selected.filter fun r => (o? r.m).isSome && !(o? r.m == some r.t)).length == 6
#guard (selected.filter fun r => (o? r.m).isNone).length == 6

end Selected
end Rows
