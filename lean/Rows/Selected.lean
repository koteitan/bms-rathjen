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

FAMILY 1'S E3 IS PROVED — `F1.e3 : ∀ n, o? (M[n]) = some (fsN t (n+1))`.  It is the first
E3 in this repository above the region `Rows/Proofs.lean` covers, and the first for a row
that an external table disagrees with.  The chain:

    expand_F1   BMS.expand M n = P ++ zeroLad 2 n                          the matrix side
    val_F1      o? (P ++ zeroLad 2 n) = φ̄(0, A+B+fsN e0 (n+1))             the value side
    fsN_t       fsN t n = φ̄(0, A+B+fsN e0 n)                               the term side
    arith       the identity the value side needed                         the arithmetic
    e3          the four, joined                                           E3

Where the work actually was, in case the next row looks similar:

  * The MATRIX side is short once `expand?` is read on the concrete matrix instead of
    guessed: the last column (2,1) has `lnz` 1, its parent at row 1 is column 7, so the bad
    part is one column, the ascension is 1 at row 0 and 0 at row 1, and the a-th copy is
    the single column `(1+a, 0)`.  Only `a*1*1 = a` and `a*0*1 = 0` need rewriting.
  * The VALUE side goes through StageB §9's fuel-free `oLV`, so no fuel budget is threaded.
    The matrix is one block; its head `(0,0)` peels off by `oLAux_single`; one `decP` later
    the ladder starts with a row-0-zero column so `blocksP_append` cuts exactly there; and
    the ladder's own value is the ω tower (`oLV_zeroLad`).
  * The ORDINAL content is one fact: the tower stays below ε_ω.  `plus` is decided against
    the HEAD of its right argument, and that head is the tower.  `Rows.ProofsB`'s
    `lt_iterT_bound` only bounds the tower by `φ̄(c,0)`, but `ltF_phi_fst` already takes a
    general second argument, so `lt_iterT_bd` widens it to `φ̄(c,d)` in six lines.
  * The rest is NOTATION, not ordinals: `ω^W = φ̄(0,W)` because `M < W` is decided by W's
    head alone, and `φ̄(0,·)` does not fold because `splitFin`'s prefix is a sum.  The
    fixed-point branch still has to be split on, since at n = 0 the tower is `1`.

`e3` inherits `Classical.choice` from StageB's fold machinery through the value side;
`arith` and the tower bounds are `[propext, Quot.sound]`.

HOW DEEP EACH ROW GOES, measured for all six.  This is the thing that decides how much work
a row is, and it is not visible from the term:

    row   展開の形                          `decP` の段数
    F1    梯子 (2,0)(3,0)…                  2
    F2b   梯子 (3,0)(4,0)…                  2
    F2a   (1,1) の反復                      1 + 複製ごとの平坦な連鎖
    F3b   梯子 (6,0)(7,0)…                  6   梯子の底が段ごとに 1 下がる
    F3a   3 列ブロック (4,0)(5,1)(6,1)      4 + 複製ごとの平坦な連鎖
    F3c   2 列ブロック (o,0)(o+1,1)、歩幅 2  6 + 入れ子の再帰 `H`

**6 行とも `oLAux_chain` を要さなかった。** 着手前は F3a が「ブロックが `decP` のたびに
1 下がって 0 に達すると自分が分裂を始めるので深さが反復回数とともに増える」と読んでいたが、
測ると 4 段目で複製が n+1 個の独立ブロックに割れ、そこから先は `plus · ζ₀` を積むだけの
平坦な連鎖だった (F2a と同じ形)。F3c だけは底が 0 に着いてから自分自身に戻るが、それも
2 項の相互再帰 (`H`) で閉じており、`Evidence/StageB.lean` §5 の機械は要らない。
**読みではなく測ってから書くこと。**

FAMILY 2's SECOND ROW has the same ladder — `expand_F2b` is proved, and it is four lines
because the generic ladder lemmas moved out of `F1` into this namespace.  ITS VALUE SIDE IS
SHAPED DIFFERENTLY, and that is the thing to know before starting it: in family 1 one
`decP` puts a `(0,0)` immediately before the ladder, so `blocksP` cuts there and the ladder
is its own block; here the column before the ladder is `(1,0)`, so the ladder JOINS that
block, the cut is one column earlier at a `(0,1)`, and `r1 = 1` there means the fold emits
`phiStep` where family 1 emitted `plus`.  Both shapes are `#guard`ed below.

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
open Evidence.StageB (oLV)
open Rows.ProofsB (iterT)

/-! ## 共通の道具

梯子 `(o,0)(o+1,0)…`、その `decP`・`blocksP`・値、そして ω 塔の評価。族をまたいで使う。 -/

/-- 梯子 `(o,0)(o+1,0)…`、`k` 本。 -/
def zeroLad (o : Nat) : Nat → Matrix
  | 0 => []
  | k + 1 => ([o,0] : BMS.Col) :: zeroLad (o+1) k

/-- **項の側。証明済み。** `t` の基本列は最後の加数 ε₀ の基本列を走る。 -/
theorem fsN_add (a b : Term) (n : Nat) : fsN (add a b) n = plus a (fsN b n) := by rw [fsN]

theorem zeroLad_succ : ∀ (k o : Nat), zeroLad o (k+1) = zeroLad o k ++ [([o+k, 0] : BMS.Col)]
  | 0, o => by show _ = [] ++ _; rw [List.nil_append]; simp [zeroLad]
  | k+1, o => by
    show ([o,0] : BMS.Col) :: zeroLad (o+1) (k+1) = ([o,0] : BMS.Col) :: zeroLad (o+1) k ++ _
    rw [zeroLad_succ k (o+1)]
    have h : o + 1 + k = o + (k+1) := by omega
    rw [h]
    rfl

theorem lad_flatten : ∀ (k o : Nat),
    ((List.range k).map fun a => ([[o+a,0]] : Matrix)).flatten = zeroLad o k
  | 0, _ => rfl
  | k+1, o => by
    rw [List.range_succ, List.map_append, List.flatten_append, lad_flatten k o,
        zeroLad_succ k o]
    rfl

theorem r0_zeroLad : ∀ (k o : Nat), 1 ≤ o → ∀ c ∈ zeroLad o k, Trans.Pair.r0 c ≠ 0
  | 0, _, _, _, hc => by simp [zeroLad] at hc
  | k+1, o, ho, c, hc => by
    rcases List.mem_cons.mp hc with h | h
    · subst h; show o ≠ 0; omega
    · exact r0_zeroLad k (o+1) (by omega) c h

theorem decP_zeroLad : ∀ (k o : Nat), Trans.Pair.decP (zeroLad (o+1) k) = zeroLad o k
  | 0, _ => rfl
  | k+1, o => by
    show ([o+1-1, 0] : BMS.Col) :: Trans.Pair.decP (zeroLad (o+1+1) k)
        = ([o,0] : BMS.Col) :: zeroLad (o+1) k
    have h : o + 1 - 1 = o := by omega
    rw [h, decP_zeroLad k (o+1)]

theorem inFrag_zeroLad : ∀ (k o : Nat), Trans.Pair.inFrag (zeroLad o k) = true
  | 0, _ => rfl
  | k+1, o => by
    have ih : (List.all (zeroLad (o+1) k) fun c =>
        decide (List.length c ≤ 2) && decide (Trans.Pair.r1 c ≤ 1)) = true := inFrag_zeroLad k (o+1)
    show Trans.Pair.inFrag (([o,0] : BMS.Col) :: zeroLad (o+1) k) = true
    unfold Trans.Pair.inFrag
    rw [List.all_cons, ih]
    rfl

theorem onlyRow0_append_false (u v : Matrix) (h : Trans.onlyRow0 u = false) :
    Trans.onlyRow0 (u ++ v) = false := by
  unfold Trans.onlyRow0 at h ⊢
  rw [List.all_append, h]; rfl

theorem omegaNF_iterT : ∀ m, omegaNF (iterT zero m) = iterT zero (m+1)
  | 0 => rfl
  | m+1 => Rows.ProofsB.omegaNF_iterT_zero m

/-- 梯子の値は ω 塔。 -/
theorem oLV_zeroLad : ∀ (m k : Nat), oLV k (zeroLad 0 m) = iterT zero m
  | 0, _ => rfl
  | m+1, k => by
    rw [Evidence.StageB.oLV_eq]
    show (Trans.Pair.blocksP (([0,0] : BMS.Col) :: zeroLad 1 m)).foldl _ _ = _
    rw [Rows.ProofsB.blocksP_single ([0,0] : BMS.Col) (zeroLad 1 m) (r0_zeroLad m 1 (by omega))]
    show plus zero (omegaNF (oLV 1 (Trans.Pair.decP (zeroLad 1 m)))) = _
    rw [decP_zeroLad m 0, oLV_zeroLad m 1, omegaNF_iterT m]
    exact Rows.ProofsB.plus_zero_left (by
      rw [Rows.ProofsB.iterT_succ Rows.ProofsB.isSC_zero m]; rfl)

theorem ltF_iterT_bd {a c d : Term} (ha : a.isSC = false) (hac : (a == c) = false)
    (hlt : ∀ f, 2 ≤ f → TM.Term.ltF f a c = true) :
    ∀ (m f : Nat), m + 2 ≤ f → TM.Term.ltF f (iterT a m) (phi c d) = true
  | 0, f, hf => Rows.ProofsB.ltF_zero (by omega) (by intro hh; exact Term.noConfusion hh)
  | m + 1, f, hf => by
    cases f with
    | zero => omega
    | succ g =>
      rw [Rows.ProofsB.iterT_succ ha m]
      exact Rows.ProofsB.ltF_phi_fst hac (hlt g (by omega)) (ltF_iterT_bd ha hac hlt m g (by omega))

theorem lt_iterT_bd {a c d : Term} (ha : a.isSC = false) (hac : (a == c) = false)
    (hlt : ∀ f, 2 ≤ f → TM.Term.ltF f a c = true) (m : Nat) :
    lt (iterT a m) (phi c d) = true := by
  show TM.Term.ltF (TM.Term.fuelOf (iterT a m) (phi c d)) (iterT a m) (phi c d) = true
  refine ltF_iterT_bd ha hac hlt m _ ?_
  show m + 2 ≤ 2 * ((iterT a m).deg + (phi c d).deg) + 8
  have := Rows.ProofsB.deg_iterT ha m
  omega

theorem iterPhiAt_zero : ∀ m, TM.Term.iterPhiAt zero zero m = iterT zero m
  | 0 => rfl
  | m+1 => by
    show phiNF zero (TM.Term.iterPhiAt zero zero m) = phiNF zero (iterT zero m)
    rw [iterPhiAt_zero m]

def e0 : Term := phi (phi zero zero) zero

theorem fsN_e0 (m : Nat) : fsN e0 m = iterT zero m := by
  show fsN (phi (phi zero zero) zero) m = _
  rw [fsN]
  show TM.Term.iterPhiAt zero zero m = iterT zero m
  exact iterPhiAt_zero m

/-! ### ブロックの 2 形。族をまたいで使う。

**`show` を使わないこと。** F3b の値側は `show` で段ごとに式を書き直していたとき
554 秒でも終わらず (8M heartbeats を使い切る)、`show` を全部外して `d1`..`d5` が
cons の形を直接出すようにしたら **3 秒**になった。`show` は毎回入れ子の式全体を
書き直すので、Lean が 12 列の行列リテラルの上で `oLV` と `decP` を展開しながら
defeq 検査をやり直す。下の 2 つの補題は左辺が構文的に当たる形にしてあるので、
降下は `rw` の連鎖 1 本で書ける。 -/

/-- 単一ブロック (先頭が `(0,0)`)。 -/
theorem oLV_single (j : Nat) (c : BMS.Col) (rest : Matrix)
    (h : ∀ x ∈ rest, Trans.Pair.r0 x ≠ 0) (hr1 : (Trans.Pair.r1 c == 0) = true) :
    oLV j (c :: rest) = plus zero (omegaNF (oLV 1 (Trans.Pair.decP rest))) := by
  rw [Evidence.StageB.oLV_eq, Rows.ProofsB.blocksP_single c rest h]
  show (if (Trans.Pair.r1 c == 0) = true then _ else _) = _
  rw [hr1]
  rfl

/-- 前置き `Q` の後にもう 1 ブロック (先頭が `r0 = 0`、`r1 ≠ 0`)。 -/
theorem oLV_pre (j : Nat) (Q : Matrix) (c : BMS.Col) (tl : Matrix)
    (hc : Trans.Pair.r0 c = 0) (hr1 : (Trans.Pair.r1 c == 0) = false)
    (ht : ∀ x ∈ tl, Trans.Pair.r0 x ≠ 0) :
    oLV j (Q ++ (c :: tl))
      = Trans.Pair.phiStep (ofNat j) (oLV j Q) (oLV (j+1) (Trans.Pair.decP tl)) := by
  rw [Evidence.StageB.oLV_eq,
      Evidence.StageB.blocksP_append Q (c :: tl) (Or.inr ⟨c, tl, rfl, hc⟩),
      List.foldl_append, Rows.ProofsB.blocksP_single c tl ht,
      ← Evidence.StageB.oLV_eq j Q]
  show (if (Trans.Pair.r1 c == 0) = true then _ else _) = _
  rw [hr1]
  rfl

theorem r0_L (o k : Nat) (l : Matrix) (hl : ∀ x ∈ l, Trans.Pair.r0 x ≠ 0) (ho : 1 ≤ o) :
    ∀ x ∈ l ++ zeroLad o k, Trans.Pair.r0 x ≠ 0 := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hl x h
  · exact r0_zeroLad k o ho x h

/-- 前置き `Q` の後にもう 1 ブロック (先頭が `r0 = 0`、`r1 = 0`)。`oLV_pre` の兄弟で、
    こちらは `plus` を積む枝。ブロックが繰り返し並ぶ (深さが n に依らない) 形で使う。 -/
theorem oLV_preZ (j : Nat) (Q : Matrix) (c : BMS.Col) (tl : Matrix)
    (hc : Trans.Pair.r0 c = 0) (hr1 : (Trans.Pair.r1 c == 0) = true)
    (ht : ∀ x ∈ tl, Trans.Pair.r0 x ≠ 0) :
    oLV j (Q ++ (c :: tl)) = plus (oLV j Q) (omegaNF (oLV 1 (Trans.Pair.decP tl))) := by
  rw [Evidence.StageB.oLV_eq,
      Evidence.StageB.blocksP_append Q (c :: tl) (Or.inr ⟨c, tl, rfl, hc⟩),
      List.foldl_append, Rows.ProofsB.blocksP_single c tl ht,
      ← Evidence.StageB.oLV_eq j Q]
  show (if (Trans.Pair.r1 c == 0) = true then _ else _) = _
  rw [hr1]
  rfl

/-- 単一ブロック (先頭が `r0 = 0`、`r1 ≠ 0`)。`oLV_single` の兄弟で、こちらは
    `phiStep` を積む枝。前置きの無い `oLV_pre` にあたる。 -/
theorem oLV_singleP (j : Nat) (c : BMS.Col) (rest : Matrix)
    (h : ∀ x ∈ rest, Trans.Pair.r0 x ≠ 0) (hr1 : (Trans.Pair.r1 c == 0) = false) :
    oLV j (c :: rest)
      = Trans.Pair.phiStep (ofNat j) zero (oLV (j+1) (Trans.Pair.decP rest)) := by
  rw [Evidence.StageB.oLV_eq, Rows.ProofsB.blocksP_single c rest h]
  show (if (Trans.Pair.r1 c == 0) = true then _ else _) = _
  rw [hr1]
  rfl

/-! ### 一様な複製 `repM` の道具。`frep` (歩幅つき) の歩幅 0 の場合にあたる。 -/

theorem decP_repM (b : Matrix) : ∀ k,
    Trans.Pair.decP (Trans.repM b k) = Trans.repM (Trans.Pair.decP b) k
  | 0 => rfl
  | k+1 => by
    show Trans.Pair.decP (b ++ Trans.repM b k) = _
    rw [Rows.ProofsB.decP_append, decP_repM b k]
    rfl

theorem r0_repM (b : Matrix) (hb : ∀ x ∈ b, Trans.Pair.r0 x ≠ 0) :
    ∀ k, ∀ x ∈ Trans.repM b k, Trans.Pair.r0 x ≠ 0
  | 0, x, hx => by simp [Trans.repM] at hx
  | k+1, x, hx => by
    rcases List.mem_append.mp (show x ∈ b ++ Trans.repM b k from hx) with h1 | h1
    · exact hb x h1
    · exact r0_repM b hb k x h1

theorem inFrag_repM (b : Matrix) (hb : Trans.Pair.inFrag b = true) :
    ∀ k, Trans.Pair.inFrag (Trans.repM b k) = true
  | 0 => rfl
  | k+1 => by
    show Trans.Pair.inFrag (b ++ Trans.repM b k) = true
    rw [Rows.ProofsB.inFrag_append, hb, inFrag_repM b hb k]; rfl

theorem r0_app (l : Matrix) (hl : ∀ x ∈ l, Trans.Pair.r0 x ≠ 0) (b : Matrix)
    (hb : ∀ x ∈ b, Trans.Pair.r0 x ≠ 0) (k : Nat) :
    ∀ x ∈ l ++ Trans.repM b k, Trans.Pair.r0 x ≠ 0 := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hl x h
  · exact r0_repM b hb k x h

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

/-! ### 外部の表の値は、同じ試験を通らない

`e3` は当方の値についての定理である。それだけでは「先方が誤り」とは言えないので、
**先方の値に同じ試験を当てる**。先方の 145 行目は末尾が `phi(0,1)` = ε₁ で、当方は
`phi(0,0)` = ε₀ である。 -/

/-- 先方の値 ([diff.md](../../table/diff.md) 族 1)。末尾だけが当方と違う。 -/
def tHex : Term := phi zero (add (phi (phi zero zero) (add (phi zero (phi zero zero)) (phi zero zero)))
  (add (phi (phi zero zero) (phi zero (phi zero zero))) (phi (phi zero zero) (phi zero zero))))

#guard !(o? M == some tHex)
#guard kindT tHex == KindT.isLim          -- 極限なので基本列を持つ。試験は空回りしない
-- どのずらしでも E3 は立たない
#guard (List.range 6).all fun k => (List.range 8).any fun n =>
  !(o? (BMS.expand M n) == some (fsN tHex (n + k)))
-- ずらし以前に、展開の像が先方の値の基本列に現れない (30 項まで)
#guard (List.range 4).all fun n => (List.range 30).all fun j =>
  !(o? (BMS.expand M n) == some (fsN tHex j))
-- CTRL 同じ探索は当方の値では当たる
#guard (List.range 4).all fun n => (List.range 30).any fun j =>
  o? (BMS.expand M n) == some (fsN t j)

/-! ### 分解: E3 を 3 つに割る

行列の側は `M[n] = P ++ (2,0)(3,0)…(n+1,0)` で、値の側はその梯子が ω 塔を積む。
項の側は `fsN t` が最後の加数 ε₀ の基本列を走る。**項の側だけは今証明できる**ので、
残る 2 つが何であるかがはっきりする。 -/

/-- 展開の共通の頭。`M` から最後の `(2,1)` を落としたもの。 -/
def P : Matrix := [[0,0],[1,1],[2,0],[1,1],[1,0],[2,1],[3,0],[1,0]]

def A : Term := phi (phi zero zero) (add (phi zero (phi zero zero)) (phi zero zero))
def B : Term := phi (phi zero zero) (phi zero (phi zero zero))

theorem t_eq : t = phi zero (add A (add B e0)) := rfl


theorem fsN_t (n : Nat) : fsN t n = phiNF zero (plus A (plus B (fsN e0 n))) := by
  rw [t_eq, Rows.ProofsB.fsN_phi_lim (a := zero) (b := add A (add B e0)) rfl rfl n,
      fsN_add, fsN_add]

/-- 行列の側。 -/
def expandClaim : Prop := ∀ n, BMS.expand M n = P ++ zeroLad 2 n

/-! #### 行列の側の証明

`expand?` を `M` で計算すると、最後の列 `(2,1)` の `lnz` が 1、その親が列 7 で、
悪い部分は 1 列だけ、上昇量は行 0 で 1、行 1 で 0 になる。つまり `a` 番目の複製は
`(1+a, 0)` の 1 列である。あとは `flatten ∘ map` を梯子に直せばよい。 -/



/-- **行列の側。証明済み。** -/
theorem expand_F1 (n : Nat) : BMS.expand M n = P ++ zeroLad 2 n := by
  show (BMS.expand? M n).getD [] = _
  have h : BMS.expand? M n
      = some (M.take 7 ++
          ((List.range (n+1)).map fun a => ([[1 + a*1*1, 0 + a*0*1]] : Matrix)).flatten) := rfl
  have hf : (fun a => ([[1 + a*1*1, 0 + a*0*1]] : Matrix))
      = (fun a => ([[1+a,0]] : Matrix)) := by funext a; simp
  rw [h, hf, lad_flatten (n+1) 1]
  rfl
/-- 値の側。 -/
def valClaim : Prop := ∀ n, o? (P ++ zeroLad 2 n) = some (phiNF zero (plus A (plus B (fsN e0 (n+1)))))

/-! #### 値の側の証明

`o?` は `blocksP` 上の畳み込みで、梯子は `(0,0)` で始まる 1 ブロックになるから
`blocksP_append` で切れる。前半は閉じた計算、後半は梯子で、梯子の値は ω 塔である。
燃料は `oLV` (`Evidence/StageB.lean` §9) に移して消す。 -/








/-- 1 段降りたあとの固定の頭。`decP` は行 0 を 1 下げる。 -/
def Q : List BMS.Col := [[0,1],[1,0],[0,1],[0,0],[1,1],[2,0]]

theorem tail_eq (n : Nat) :
    Trans.Pair.decP (P.tail ++ zeroLad 2 n) = Q ++ zeroLad 0 (n+1) := by
  rw [Rows.ProofsB.decP_append, decP_zeroLad n 1]
  rfl

/-! #### 塔の評価

`Rows.ProofsB.lt_iterT_bound` は行き先が `φ̄(c,0)` に限られている。`ltF_phi_fst` の
第 2 引数はもともと一般なので、そのまま `φ̄(c,d)` に広げられる。 -/





/-- **塔は ε_{ω+1} の下に留まる。** -/
theorem lt_tower_A (m : Nat) : lt (iterT zero m) A = true :=
  lt_iterT_bd Rows.ProofsB.isSC_zero rfl (fun f hf => Rows.ProofsB.ltF_zero_one f hf) m
/-- **塔は ε_ω の下に留まる。** -/
theorem lt_tower_B (m : Nat) : lt (iterT zero m) B = true :=
  lt_iterT_bd Rows.ProofsB.isSC_zero rfl (fun f hf => Rows.ProofsB.ltF_zero_one f hf) m



/-- `plus` を畳んだ形。`plus_shape` の証明が両辺で辿り着く先そのもの。 -/
theorem W_eq (m : Nat) :
    plus (plus A B) (iterT zero (m+1)) = add A (add B (iterT zero (m+1))) := by
  have hA : le (iterT zero (m+1)) A = true := by
    show ((iterT zero (m+1) == A) || lt (iterT zero (m+1)) A) = true
    rw [lt_tower_A (m+1)]; exact Bool.or_true _
  have hB : le (iterT zero (m+1)) B = true := by
    show ((iterT zero (m+1) == B) || lt (iterT zero (m+1)) B) = true
    rw [lt_tower_B (m+1)]; exact Bool.or_true _
  have hT : iterT zero (m+1) = phi zero (iterT zero m) :=
    Rows.ProofsB.iterT_succ Rows.ProofsB.isSC_zero m
  rw [hT] at hA hB ⊢
  show ofList ((toList (plus A B)).filter (fun a => le (phi zero (iterT zero m)) a)
        ++ [phi zero (iterT zero m)]) = _
  rw [show toList (plus A B) = [A, B] from rfl]
  simp only [List.filter_cons, hA, hB, List.filter_nil]
  rfl

/-- `ω^W = φ̄(0,W)`: `M < W` は W の**頭の成分だけ**で決まり、頭は A なので塔に依らない。 -/
theorem omegaNF_W (a b : Term) :
    omegaNF (add A (add B (phi a b))) = phiNF zero (add A (add B (phi a b))) := rfl

/-- `φ̄(0,·)` は畳まれない: W は和で、`splitFin` の前半も和だから、
    `phiNF` は既定の枝に落ちる。末尾が 1 かどうか (n = 0 か否か) で分岐するが、両方とも
    同じところに来る。 -/
theorem phiNF_zero_W (a b : Term) :
    phiNF zero (add A (add B (phi a b))) = phi zero (add A (add B (phi a b))) := by
  show phiNFsucc zero (add A (add B (phi a b))) = _
  unfold phiNFsucc
  cases hT : (phi a b == one) with
  | true =>
    have h1 : splitFin (add A (add B (phi a b))) = (add A B, 1) := by
      have h : phi a b = one := by simpa using hT
      rw [h]; rfl
    rw [h1]; rfl
  | false =>
    have h0 : splitFin (add A (add B (phi a b))) = (add A (add B (phi a b)), 0) := by
      unfold splitFin
      rw [show (add A (add B (phi a b))).toList = [A, B, phi a b] from rfl]
      simp only [List.reverse_cons, List.takeWhile_append, hT]
      simp [hT]
      rfl
    rw [h0]; rfl

/-- 残るのはこれだけ。**順序数の中身 — 塔が ε_ω の下に留まること — は上で証明した**
    (`lt_tower_A` / `lt_tower_B` / `plus_shape` / `fsN_e0`)。残っているのは
    `omegaNF W = phiNF zero W` すなわち `lt M W = false` と、`plus zero X = X` の
    正規化 2 つで、これは順序数の事実ではなく表記の畳み方の問題である。 -/
def arithClaim : Prop := ∀ n, plus zero (omegaNF (plus (plus A B) (iterT zero (n+1))))
  = phiNF zero (plus A (plus B (fsN e0 (n+1))))

/-- 両辺の引数が同じ 3 項和になる。`plus` は右引数の頭との比較で決まり、その頭が塔で、
    塔は `lt_tower_A` / `lt_tower_B` で A・B の下にある。 -/
theorem plus_shape (m : Nat) :
    plus (plus A B) (iterT zero (m+1)) = plus A (plus B (iterT zero (m+1))) := by
  have hA : le (iterT zero (m+1)) A = true := by
    show ((iterT zero (m+1) == A) || lt (iterT zero (m+1)) A) = true
    rw [lt_tower_A (m+1)]; exact Bool.or_true _
  have hB : le (iterT zero (m+1)) B = true := by
    show ((iterT zero (m+1) == B) || lt (iterT zero (m+1)) B) = true
    rw [lt_tower_B (m+1)]; exact Bool.or_true _
  have hT : iterT zero (m+1) = phi zero (iterT zero m) :=
    Rows.ProofsB.iterT_succ Rows.ProofsB.isSC_zero m
  rw [hT] at hA hB ⊢
  show ofList ((toList (plus A B)).filter (fun a => le (phi zero (iterT zero m)) a)
        ++ [phi zero (iterT zero m)])
      = plus A (ofList (([B]).filter (fun a => le (phi zero (iterT zero m)) a)
        ++ [phi zero (iterT zero m)]))
  rw [show toList (plus A B) = [A, B] from rfl]
  simp only [List.filter_cons, hA, hB, List.filter_nil]
  rfl

/-- **値の側。上の算術一つに落ちる。** -/
theorem val_F1 (ha : arithClaim) (n : Nat) :
    o? (P ++ zeroLad 2 n) = some (phiNF zero (plus A (plus B (fsN e0 (n+1))))) := by
  have hlen : (P ++ zeroLad 2 n).length ≤ (P ++ zeroLad 2 n).length + 1 := by omega
  have h0 : Trans.onlyRow0 (P ++ zeroLad 2 n) = false :=
    onlyRow0_append_false P (zeroLad 2 n) rfl
  have hf : Trans.Pair.inFrag (P ++ zeroLad 2 n) = true := by
    rw [Rows.ProofsB.inFrag_append, inFrag_zeroLad n 2]; rfl
  have hstep : o? (P ++ zeroLad 2 n) = some (oLV 1 (P ++ zeroLad 2 n)) := by
    show (if Trans.onlyRow0 _ = true then _ else Trans.oPair? _) = _
    simp only [h0, Bool.false_eq_true, if_false]
    show (if Trans.Pair.inFrag _ = true then some (if Trans.onlyRow0 _ = true then _ else
      Trans.Pair.oLAux ((P ++ zeroLad 2 n).length + 1) 1 (P ++ zeroLad 2 n)) else none) = _
    simp only [hf, h0, Bool.false_eq_true, if_true, if_false]
    rw [Evidence.StageB.oLAux_eq_oLV hlen]
  rw [hstep]
  congr 1
  -- 頭の (0,0) を剥がす: 残りは全部 r0 ≠ 0
  have hP : ∀ x ∈ P.tail, Trans.Pair.r0 x ≠ 0 := by decide
  have htail : ∀ x ∈ (P.tail ++ zeroLad 2 n), Trans.Pair.r0 x ≠ 0 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hP x h
    · exact r0_zeroLad n 2 (by omega) x h
  rw [Evidence.StageB.oLV_eq]
  show (Trans.Pair.blocksP (([0,0] : BMS.Col) :: (P.tail ++ zeroLad 2 n))).foldl _ _ = _
  rw [Rows.ProofsB.blocksP_single ([0,0] : BMS.Col) _ htail]
  show plus zero (omegaNF (oLV 1 (Trans.Pair.decP (P.tail ++ zeroLad 2 n)))) = _
  rw [tail_eq n]
  -- Q は閉じた計算、梯子は 1 ブロック
  rw [Evidence.StageB.oLV_eq,
      Evidence.StageB.blocksP_append Q (zeroLad 0 (n+1)) (Or.inr ⟨[0,0], zeroLad 1 n, rfl, rfl⟩),
      List.foldl_append,
      show zeroLad 0 (n+1) = ([0,0] : BMS.Col) :: zeroLad 1 n from rfl,
      Rows.ProofsB.blocksP_single ([0,0] : BMS.Col) (zeroLad 1 n) (r0_zeroLad n 1 (by omega)),
      ← Evidence.StageB.oLV_eq 1 Q]
  have hQ : oLV 1 Q = plus A B := rfl
  rw [hQ]
  show plus zero (omegaNF (plus (plus A B) (omegaNF (oLV 1 (Trans.Pair.decP (zeroLad 1 n)))))) = _
  rw [decP_zeroLad n 0, oLV_zeroLad n 1, omegaNF_iterT n]
  exact ha n

/-- **算術。証明済み。** -/
theorem arith : arithClaim := by
  intro n
  rw [fsN_e0 (n+1), ← plus_shape n, W_eq n,
      Rows.ProofsB.iterT_succ Rows.ProofsB.isSC_zero n, omegaNF_W, phiNF_zero_W]
  exact Rows.ProofsB.plus_zero_left rfl

/-- **E3。証明済み。** 行列側・値側・項側を継ぐ。 -/
theorem e3 : e3Claim := by
  intro n
  rw [expand_F1 n, val_F1 arith n, fsN_t (n+1)]

#guard (List.range 8).all fun n =>
  plus zero (omegaNF (plus (plus A B) (iterT zero (n+1))))
    == phiNF zero (plus A (plus B (fsN e0 (n+1))))

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

/-! ### 行列側・値側は済。残るのは算術 2 本 -/

def P : Matrix := [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[1,1]]
def Ua : Matrix := [[0,1],[1,1]]
def Ba : Matrix := [[0,1],[1,0],[2,1],[3,1],[2,1]]
def Va : Term := oLV 1 (Ua ++ Ba)
def stepA (x : Term) : Term := Trans.Pair.phiStep (ofNat 1) x zero
def chain : Nat → Term
  | 0 => Va
  | k+1 => stepA (chain k)

theorem flat_const_11 : ∀ (k : Nat),
    ((List.range k).map fun _ => ([[1,1]] : Matrix)).flatten = Trans.repM [[1,1]] k
  | 0 => rfl
  | k+1 => by
    rw [List.range_succ, List.map_append, List.flatten_append, flat_const_11 k]
    show Trans.repM ([[1,1]] : Matrix) k ++ ([[1,1]] : Matrix) = _
    rw [Trans.repM_append]

/-- **行列の側。** 悪い部分は 1 列 `(1,1)`、上昇なし。 -/
theorem expand_F2a (n : Nat) : BMS.expand M n = P ++ Trans.repM ([[1,1]] : Matrix) n := by
  show (BMS.expand? M n).getD [] = _
  have h : BMS.expand? M n
      = some (M.take 8 ++ ((List.range (n+1)).map fun a =>
          ([[1 + a*0*1, 1 + a*0*1]] : Matrix)).flatten) := rfl
  have hf : (fun a => ([[1 + a*0*1, 1 + a*0*1]] : Matrix)) = (fun _ => ([[1,1]] : Matrix)) := by
    funext a; simp
  rw [h, hf, flat_const_11 (n+1)]
  rfl

/-- 反復されたブロックの連鎖。`(0,1)` は `r0 = 0` なので 1 列ずつ独立したブロックになり、
    畳み込みは `phiStep` を 1 回ずつ積む。 -/
theorem chain_eq : ∀ (k : Nat),
    oLV 1 (Ua ++ Ba ++ Trans.repM ([[0,1]] : Matrix) k) = chain k
  | 0 => rfl
  | k+1 => by
    rw [← Trans.repM_append ([[0,1]] : Matrix) k, ← List.append_assoc,
        Evidence.StageB.oLV_eq,
        Evidence.StageB.blocksP_append (Ua ++ Ba ++ Trans.repM ([[0,1]] : Matrix) k)
          ([[0,1]] : Matrix) (Or.inr ⟨[0,1], [], rfl, rfl⟩),
        List.foldl_append,
        Rows.ProofsB.blocksP_single ([0,1] : BMS.Col) [] (by simp),
        ← Evidence.StageB.oLV_eq 1 (Ua ++ Ba ++ Trans.repM ([[0,1]] : Matrix) k),
        chain_eq k]
    rfl

theorem decP_rep : ∀ (k : Nat),
    Trans.Pair.decP (Trans.repM ([[1,1]] : Matrix) k) = Trans.repM ([[0,1]] : Matrix) k
  | 0 => rfl
  | k+1 => by
    show Trans.Pair.decP (([[1,1]] : Matrix) ++ Trans.repM ([[1,1]] : Matrix) k) = _
    rw [Rows.ProofsB.decP_append, decP_rep k]
    rfl

theorem dA (n : Nat) :
    Trans.Pair.decP (P.tail ++ Trans.repM ([[1,1]] : Matrix) n)
      = Ua ++ Ba ++ Trans.repM ([[0,1]] : Matrix) (n+1) := by
  rw [Rows.ProofsB.decP_append, decP_rep n]
  rfl

set_option maxHeartbeats 2000000 in
/-- **値の側。** -/
theorem val (n : Nat) :
    o? (BMS.expand M n) = some (plus zero (omegaNF (chain (n+1)))) := by
  have hlen : (P ++ Trans.repM ([[1,1]] : Matrix) n).length
      ≤ (P ++ Trans.repM ([[1,1]] : Matrix) n).length + 1 := by omega
  have hrep : ∀ (k : Nat), ∀ x ∈ Trans.repM ([[1,1]] : Matrix) k, Trans.Pair.r0 x ≠ 0 := by
    intro k
    induction k with
    | zero => intro x hx; simp [Trans.repM] at hx
    | succ k ih =>
      intro x hx
      have h : x ∈ ([[1,1]] : Matrix) ++ Trans.repM ([[1,1]] : Matrix) k := hx
      rcases List.mem_append.mp h with h1 | h1
      · rw [List.mem_singleton.mp h1]; decide
      · exact ih x h1
  have h0 : Trans.onlyRow0 (P ++ Trans.repM ([[1,1]] : Matrix) n) = false :=
    onlyRow0_append_false P _ rfl
  have hfr : ∀ (k : Nat), Trans.Pair.inFrag (Trans.repM ([[1,1]] : Matrix) k) = true := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      show Trans.Pair.inFrag (([[1,1]] : Matrix) ++ Trans.repM ([[1,1]] : Matrix) k) = true
      rw [Rows.ProofsB.inFrag_append, ih]; rfl
  have hf : Trans.Pair.inFrag (P ++ Trans.repM ([[1,1]] : Matrix) n) = true := by
    rw [Rows.ProofsB.inFrag_append, hfr n]; rfl
  have hP : ∀ x ∈ P.tail, Trans.Pair.r0 x ≠ 0 := by decide
  rw [expand_F2a n]
  have hstep : o? (P ++ Trans.repM ([[1,1]] : Matrix) n)
      = some (oLV 1 (P ++ Trans.repM ([[1,1]] : Matrix) n)) := by
    show (if Trans.onlyRow0 _ = true then _ else Trans.oPair? _) = _
    simp only [h0, Bool.false_eq_true, if_false]
    show (if Trans.Pair.inFrag _ = true then some (if Trans.onlyRow0 _ = true then _ else
      Trans.Pair.oLAux ((P ++ Trans.repM ([[1,1]] : Matrix) n).length + 1) 1
        (P ++ Trans.repM ([[1,1]] : Matrix) n)) else none) = _
    simp only [hf, h0, Bool.false_eq_true, if_true, if_false]
    rw [Evidence.StageB.oLAux_eq_oLV hlen]
  rw [hstep]
  congr 1
  have htail : ∀ x ∈ (P.tail ++ Trans.repM ([[1,1]] : Matrix) n), Trans.Pair.r0 x ≠ 0 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hP x h
    · exact hrep n x h
  rw [show P ++ Trans.repM ([[1,1]] : Matrix) n
        = ([0,0] : BMS.Col) :: (P.tail ++ Trans.repM ([[1,1]] : Matrix) n) from rfl,
      oLV_single _ _ _ htail rfl, dA n, chain_eq (n+1)]

/-- φ̄(1,ζ₀)。連鎖の各段が積む先。 -/
def Bt : Term := phi (phi zero zero) (phi (add (phi zero zero) (phi zero zero)) zero)

theorem fsN_omega (k : Nat) : fsN TM.Term.omega k = ofNat k := by
  show fsN (phi zero TM.Term.one) k = _
  rw [fsN]
  show mulNat (omegaNF zero) k = ofNat k
  exact Rows.ProofsB.mulNat_one_ofNat k

theorem plus_Bt_eq (k : Nat) :
    plus Bt (ofNat (k+1)) = ofList (Bt :: List.replicate (k+1) TM.Term.one) := by
  unfold plus
  rw [Rows.ProofsB.toList_ofNat (k+1), List.replicate_succ]
  show ofList ((toList Bt).filter (fun a => le TM.Term.one a)
    ++ (TM.Term.one :: List.replicate k TM.Term.one)) = _
  rw [show toList Bt = [Bt] from rfl]
  simp only [List.filter_cons, show le TM.Term.one Bt = true from rfl, List.filter_nil]
  simp [List.replicate_succ]

theorem toList_plus_Bt : ∀ (k : Nat),
    toList (plus Bt (ofNat k)) = Bt :: List.replicate k TM.Term.one
  | 0 => rfl
  | k+1 => by
    rw [plus_Bt_eq k, toList_ofList]
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · subst h; rfl
    · rw [List.eq_of_mem_replicate h]; rfl
theorem takeWhile_rep : ∀ (k : Nat),
    (List.replicate k TM.Term.one ++ [Bt]).takeWhile (fun x => x == TM.Term.one)
      = List.replicate k TM.Term.one
  | 0 => rfl
  | k+1 => by
    rw [List.replicate_succ, List.cons_append, List.takeWhile_cons,
        show (TM.Term.one == TM.Term.one) = true from rfl, takeWhile_rep k]
    simp [List.replicate_succ]

theorem splitFin_Bt (k : Nat) : splitFin (plus Bt (ofNat k)) = (Bt, k) := by
  have hl := toList_plus_Bt k
  show (ofList ((toList (plus Bt (ofNat k))).take
        ((toList (plus Bt (ofNat k))).length -
          ((toList (plus Bt (ofNat k))).reverse.takeWhile (fun x => x == TM.Term.one)).length)),
      ((toList (plus Bt (ofNat k))).reverse.takeWhile (fun x => x == TM.Term.one)).length) = _
  rw [hl, List.reverse_cons, List.reverse_replicate, takeWhile_rep k]
  simp
  rfl

theorem plus_Bt_add (k : Nat) : plus Bt (ofNat (k+1)) = add Bt (ofNat (k+1)) := by
  rw [plus_Bt_eq k]
  show add Bt (ofList (List.replicate (k+1) TM.Term.one)) = _
  rw [show ofList (List.replicate (k+1) TM.Term.one) = mulNat TM.Term.one (k+1) from rfl,
      Rows.ProofsB.mulNat_one_ofNat (k+1)]

theorem phiNF_one_Bt : ∀ (k : Nat),
    phiNF (ofNat 1) (plus Bt (ofNat k)) = phi (ofNat 1) (plus Bt (ofNat k))
  | 0 => rfl
  | k+1 => by
    have hadd := plus_Bt_add k
    have hsp : splitFin (add Bt (ofNat (k+1))) = (Bt, k+1) := by
      rw [← hadd]; exact splitFin_Bt (k+1)
    rw [hadd]
    show phiNFsucc (ofNat 1) (add Bt (ofNat (k+1))) = _
    unfold phiNFsucc
    rw [hsp]
    rfl

theorem filter_rep : ∀ (k : Nat),
    (List.replicate k TM.Term.one).filter (fun a => le TM.Term.one a)
      = List.replicate k TM.Term.one
  | 0 => rfl
  | k+1 => by
    rw [List.replicate_succ, List.filter_cons,
        show le TM.Term.one TM.Term.one = true from rfl, filter_rep k]
    simp [List.replicate_succ]

theorem plus_succ (k : Nat) :
    plus (plus Bt (ofNat k)) TM.Term.one = plus Bt (ofNat (k+1)) := by
  rw [plus_Bt_eq k]
  show ofList ((toList (plus Bt (ofNat k))).filter (fun a => le TM.Term.one a)
    ++ [TM.Term.one]) = _
  rw [toList_plus_Bt k]
  simp only [List.filter_cons, show le TM.Term.one Bt = true from rfl, filter_rep k]
  rw [List.replicate_succ']
  simp

theorem chain_shape : ∀ (k : Nat), chain k = phiNF (ofNat 1) (plus Bt (ofNat k))
  | 0 => rfl
  | k+1 => by
    show stepA (chain k) = _
    rw [chain_shape k, phiNF_one_Bt k]
    unfold stepA Trans.Pair.phiStep
    rw [show Trans.Pair.logPhi (ofNat 1) (phi (ofNat 1) (plus Bt (ofNat k)))
          = some (plus Bt (ofNat k)) from by
        show (if ((ofNat 1) == (ofNat 1)) = true then
          some (if phiShifted (ofNat 1) (plus Bt (ofNat k)) then _ else _) else _) = _
        rw [show phiShifted (ofNat 1) (plus Bt (ofNat k)) = false from by
          show (isFP (ofNat 1) (splitFin (plus Bt (ofNat k))).1
            || ((plus Bt (ofNat k)) == zero && (ofNat 1).isSC)) = false
          rw [splitFin_Bt k]
          show (isFP (ofNat 1) Bt || ((plus Bt (ofNat k)) == zero && (ofNat 1).isSC)) = false
          rw [show isFP (ofNat 1) Bt = false from rfl,
              show ((ofNat 1) : Term).isSC = false from rfl]
          simp]
        rfl]
    show phiNF (ofNat 1) (plus (plus Bt (ofNat k)) TM.Term.one) = _
    rw [plus_succ k]

theorem fsN_t_eq (j : Nat) : fsN t (j+1) = phiNF (ofNat 1) (plus Bt (ofNat (j+1))) := by
  show fsN (phi (ofNat 1) (add Bt TM.Term.omega)) (j+1) = _
  rw [Rows.ProofsB.fsN_phi_lim rfl rfl, fsN_add, fsN_omega]

/-- **算術。証明済み。** -/
theorem arith (n : Nat) : plus zero (omegaNF (chain (n+1))) = fsN t (n+1) := by
  rw [chain_shape (n+1), fsN_t_eq n, phiNF_one_Bt (n+1)]
  rfl

/-- **E3。証明済み。** -/
theorem e3 : ∀ n, o? (BMS.expand M n) = some (fsN t (n + 1)) := by
  intro n; rw [val n, arith n]

/-! ### 外部の表の値は、同じ試験を通らない -/

/-- 先方の値 ([diff.md](../../table/diff.md) 族 2 の 248 行目)。先方の構文解析器で訳した。 -/
def tHex : Term := phiNF (ofNat 1) (add (phiNF (ofNat 1) (add (phiNF (ofNat 2) zero) (ofNat 1)))
  (phiNF (ofNat 1) zero))

#guard !(o? M == some tHex)
#guard kindT tHex == KindT.isLim
#guard (List.range 6).all fun k => (List.range 8).any fun n =>
  !(o? (BMS.expand M n) == some (fsN tHex (n + k)))
-- **この行だけ 0 番目が偶然当たる。** `fsN tHex 1` に一致する。それでも E3 は
-- 全 n で固定の添字を要求するので、上のずらしの不成立で反証は足りている。
-- 1 番目から先は先方の基本列に載らない (30 項まで探索)。
#guard (List.range 4).all fun n => (List.range 30).all fun j =>
  !(o? (BMS.expand M (n+1)) == some (fsN tHex j))
#guard (List.range 30).any fun j => o? (BMS.expand M 0) == some (fsN tHex j)
-- CTRL 同じ探索は当方の値では全部当たる
#guard (List.range 4).all fun n => (List.range 30).any fun j =>
  o? (BMS.expand M n) == some (fsN t j)

#guard (List.range 6).all fun n =>
  plus zero (omegaNF (chain (n+1))) == fsN t (n+1)
#guard (List.range 6).all fun k => chain k == phiNF (ofNat 1) (plus Bt (ofNat k))

end F2a

namespace F2b

def M : Matrix := [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[1,1],[2,0],[3,1]]
def t : Term := phi (phi zero zero) (add (phi (phi zero zero)
  (phi (add (phi zero zero) (phi zero zero)) zero)) (phi (phi zero zero) zero))

theorem e1 : o? M = some t := rfl

/-- **添字は 2 で、隣の F2a は 1 である。** 同じ族の隣り合う 2 行で違う。 -/
def e3Claim : Prop := ∀ n, o? (BMS.expand M n) = some (fsN t (n + 2))

/-! ### 行列の側 — 族 1 と同じ梯子

最後の列 `(3,1)` の `lnz` は 1、その親は列 9、悪い部分は 1 列で上昇量は行 0 で 1、
行 1 で 0。`a` 番目の複製は `(2+a, 0)` の 1 列である。 -/

def P : Matrix := [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[1,1],[2,0]]

/-- **行列の側。証明済み。** -/
theorem expand_F2b (n : Nat) : BMS.expand M n = P ++ zeroLad 3 n := by
  show (BMS.expand? M n).getD [] = _
  have h : BMS.expand? M n
      = some (M.take 9 ++
          ((List.range (n+1)).map fun a => ([[2 + a*1*1, 0 + a*0*1]] : Matrix)).flatten) := rfl
  have hf : (fun a => ([[2 + a*1*1, 0 + a*0*1]] : Matrix))
      = (fun a => ([[2+a,0]] : Matrix)) := by funext a; simp
  rw [h, hf, lad_flatten (n+1) 2]
  rfl

#guard kindT t == KindT.isLim
#guard (List.range 8).all fun n => o? (BMS.expand M n) == some (fsN t (n + 2))
#guard (List.range 8).any fun n => !(o? (BMS.expand M n) == some (fsN t (n + 1)))
#guard (List.range 8).any fun n => !(o? (BMS.expand M n) == some (fsN t (n + 3)))

/-! ### 値の側は族 1 と形が違う

族 1 では `decP` を 1 回とると梯子の直前が `(0,0)` になり、`blocksP` がそこで切れて
梯子が独立したブロックになった。ここは違う: `decP (P.tail)` の末尾が `(1,0)` で、梯子は
`(2,0)` から始まるので**同じブロックに合流する**。切れ目はもう一つ手前の `(0,1)` で、
その列は `r1 = 1` なので `plus` ではなく `phiStep` が出る。

    最後のブロック = (0,1) (1,0) (2,0) (3,0) …
    → phiStep (ofNat 1) V (oLV 2 (decP ((1,0) :: zeroLad 2 n)))
    → decP がもう一段下げて zeroLad 0 (n+1)、その値は ω 塔

つまり残りは `phiStep` を畳む仕事で、族 1 の `plus` の場所に来る。 -/

/-- 梯子を含む最後のブロック。 -/
def lastBlock (n : Nat) : List BMS.Col := ([0,1] : BMS.Col) :: ([1,0] : BMS.Col) :: zeroLad 2 n

#guard (List.range 6).all fun n =>
  Trans.Pair.decP (P.tail ++ zeroLad 3 n) ==
    [[0,1],[1,1],[0,1],[1,0],[2,1],[3,1],[2,1]] ++ lastBlock n
#guard (List.range 6).all fun n =>
  Trans.Pair.decP (([1,0] : BMS.Col) :: zeroLad 2 n) == zeroLad 0 (n+1)

/-- 切れ目より前の 7 列。閉じた計算。 -/
def U : List BMS.Col := [[0,1],[1,1],[0,1],[1,0],[2,1],[3,1],[2,1]]
/-- `logPhi 1` がそこから取り出す値 = φ̄(1,ζ₀)。 -/
def b2 : Term := phi (phi zero zero) (phi (add (phi zero zero) (phi zero zero)) zero)

theorem logPhi_U : Trans.Pair.logPhi TM.Term.one (oLV 1 U) = some b2 := rfl

theorem tail_eq (n : Nat) :
    Trans.Pair.decP (P.tail ++ zeroLad 3 n) = U ++ lastBlock n := by
  rw [Rows.ProofsB.decP_append, decP_zeroLad n 2]
  rfl

theorem decP_lastTail (n : Nat) :
    Trans.Pair.decP (([1,0] : BMS.Col) :: zeroLad 2 n) = zeroLad 0 (n+1) := by
  show ([0,0] : BMS.Col) :: Trans.Pair.decP (zeroLad 2 n) = _
  rw [decP_zeroLad n 1]
  rfl

/-- **値の側。証明済み。** 族 1 の `plus` の位置に `phiStep` が来る。 -/
theorem val_F2b (n : Nat) :
    o? (P ++ zeroLad 3 n)
      = some (plus zero (omegaNF (Trans.Pair.phiStep TM.Term.one (oLV 1 U) (iterT zero (n+1))))) := by
  have hlen : (P ++ zeroLad 3 n).length ≤ (P ++ zeroLad 3 n).length + 1 := by omega
  have h0 : Trans.onlyRow0 (P ++ zeroLad 3 n) = false :=
    onlyRow0_append_false P (zeroLad 3 n) rfl
  have hf : Trans.Pair.inFrag (P ++ zeroLad 3 n) = true := by
    rw [Rows.ProofsB.inFrag_append, inFrag_zeroLad n 3]; rfl
  have hstep : o? (P ++ zeroLad 3 n) = some (oLV 1 (P ++ zeroLad 3 n)) := by
    show (if Trans.onlyRow0 _ = true then _ else Trans.oPair? _) = _
    simp only [h0, Bool.false_eq_true, if_false]
    show (if Trans.Pair.inFrag _ = true then some (if Trans.onlyRow0 _ = true then _ else
      Trans.Pair.oLAux ((P ++ zeroLad 3 n).length + 1) 1 (P ++ zeroLad 3 n)) else none) = _
    simp only [hf, h0, Bool.false_eq_true, if_true, if_false]
    rw [Evidence.StageB.oLAux_eq_oLV hlen]
  rw [hstep]
  congr 1
  have hP : ∀ x ∈ P.tail, Trans.Pair.r0 x ≠ 0 := by decide
  have htail : ∀ x ∈ (P.tail ++ zeroLad 3 n), Trans.Pair.r0 x ≠ 0 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hP x h
    · exact r0_zeroLad n 3 (by omega) x h
  rw [Evidence.StageB.oLV_eq]
  show (Trans.Pair.blocksP (([0,0] : BMS.Col) :: (P.tail ++ zeroLad 3 n))).foldl _ _ = _
  rw [Rows.ProofsB.blocksP_single ([0,0] : BMS.Col) _ htail]
  show plus zero (omegaNF (oLV 1 (Trans.Pair.decP (P.tail ++ zeroLad 3 n)))) = _
  have hb : ∀ x ∈ (([1,0] : BMS.Col) :: zeroLad 2 n), Trans.Pair.r0 x ≠ 0 := by
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · subst h; decide
    · exact r0_zeroLad n 2 (by omega) x h
  rw [tail_eq n, Evidence.StageB.oLV_eq,
      Evidence.StageB.blocksP_append U (lastBlock n)
        (Or.inr ⟨[0,1], ([1,0] : BMS.Col) :: zeroLad 2 n, rfl, rfl⟩),
      List.foldl_append,
      show lastBlock n = ([0,1] : BMS.Col) :: (([1,0] : BMS.Col) :: zeroLad 2 n) from rfl,
      Rows.ProofsB.blocksP_single ([0,1] : BMS.Col) _ hb,
      ← Evidence.StageB.oLV_eq 1 U]
  show plus zero (omegaNF (Trans.Pair.phiStep (ofNat 1) (oLV 1 U)
    (oLV (1+1) (Trans.Pair.decP (([1,0] : BMS.Col) :: zeroLad 2 n))))) = _
  rw [decP_lastTail n, oLV_zeroLad (n+1) 2]
  rfl

/-! ### 算術 -/

theorem lt_tower_b2 (m : Nat) : lt (iterT zero m) b2 = true :=
  lt_iterT_bd Rows.ProofsB.isSC_zero rfl (fun f hf => Rows.ProofsB.ltF_zero_one f hf) m

theorem plus_b2 (m : Nat) :
    plus b2 (iterT zero (m+1)) = add b2 (iterT zero (m+1)) := by
  have hb : le (iterT zero (m+1)) b2 = true := by
    show ((iterT zero (m+1) == b2) || lt (iterT zero (m+1)) b2) = true
    rw [lt_tower_b2 (m+1)]; exact Bool.or_true _
  have hT : iterT zero (m+1) = phi zero (iterT zero m) :=
    Rows.ProofsB.iterT_succ Rows.ProofsB.isSC_zero m
  rw [hT] at hb ⊢
  show ofList ((toList b2).filter (fun a => le (phi zero (iterT zero m)) a)
        ++ [phi zero (iterT zero m)]) = _
  rw [show toList b2 = [b2] from rfl]
  simp only [List.filter_cons, hb, List.filter_nil]
  rfl

theorem phiNF_one_shape (a b : Term) :
    phiNF TM.Term.one (add b2 (phi a b)) = phi TM.Term.one (add b2 (phi a b)) := by
  show phiNFsucc TM.Term.one (add b2 (phi a b)) = _
  unfold phiNFsucc
  cases hT : (phi a b == TM.Term.one) with
  | true =>
    have h : phi a b = TM.Term.one := by simpa using hT
    rw [show splitFin (add b2 (phi a b)) = (b2, 1) from by rw [h]; rfl]
    rfl
  | false =>
    have h0 : splitFin (add b2 (phi a b)) = (add b2 (phi a b), 0) := by
      unfold splitFin
      rw [show (add b2 (phi a b)).toList = [b2, phi a b] from rfl]
      simp only [List.reverse_cons, List.takeWhile_append, hT]
      simp [hT]
      rfl
    rw [h0]; rfl

theorem fsN_t (m : Nat) : fsN t (m+2) = phiNF TM.Term.one (plus b2 (iterT zero (m+2))) := by
  show fsN (phi TM.Term.one (add b2 e0)) (m+2) = _
  rw [Rows.ProofsB.fsN_phi_lim (a := TM.Term.one) (b := add b2 e0) rfl rfl (m+2),
      fsN_add, fsN_e0 (m+2)]

theorem phiStep_eq (n : Nat) :
    Trans.Pair.phiStep TM.Term.one (oLV 1 U) (iterT zero (n+1))
      = phiNF TM.Term.one (plus b2 (omegaNF (iterT zero (n+1)))) := by
  have hz : (iterT zero (n+1) == zero) = false := by
    have h := Rows.ProofsB.iterT_ne_zero Rows.ProofsB.isSC_zero n
    simpa using h
  unfold Trans.Pair.phiStep
  rw [logPhi_U, hz]

/-- **算術。証明済み。** -/
theorem arith (n : Nat) :
    plus zero (omegaNF (Trans.Pair.phiStep TM.Term.one (oLV 1 U) (iterT zero (n+1))))
      = fsN t (n+2) := by
  rw [fsN_t n, phiStep_eq n, omegaNF_iterT (n+1), plus_b2 (n+1),
      Rows.ProofsB.iterT_succ Rows.ProofsB.isSC_zero (n+1), phiNF_one_shape]
  rfl

/-- **E3。証明済み。** -/
theorem e3 : e3Claim := by
  intro n
  rw [expand_F2b n, val_F2b n, arith n]

/-! ### 外部の表の値は、同じ試験を通らない -/

/-- 先方の値 ([diff.md](../../table/diff.md) 族 2 の 249 行目) を先方の構文解析器で訳したもの。 -/
def tHex : Term := phiNF (ofNat 1) (add (phiNF (ofNat 1) (add (phiNF (ofNat 2) zero) (ofNat 1)))
  (phiNF (ofNat 1) (ofNat 1)))

#guard !(o? M == some tHex)
#guard kindT tHex == KindT.isLim
#guard (List.range 6).all fun k => (List.range 8).any fun n =>
  !(o? (BMS.expand M n) == some (fsN tHex (n + k)))
#guard (List.range 4).all fun n => (List.range 30).all fun j =>
  !(o? (BMS.expand M n) == some (fsN tHex j))
-- CTRL 同じ探索は当方の値では当たる
#guard (List.range 4).all fun n => (List.range 30).any fun j =>
  o? (BMS.expand M n) == some (fsN t j)

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

/-! ### 行列の側 — 梯子ではなく 3 列ブロックの反復

最後の列 `(5,0)` の `lnz` は 0 なので `delta` が全て 0 で、**複製は上昇しない**。
悪い部分は 3 列 `(4,0)(5,1)(6,1)` で、それがそのまま n+1 回並ぶ。 -/

def blk : Matrix := [[4,0],[5,1],[6,1]]

theorem flat_const : ∀ (k : Nat), ((List.range k).map fun _ => blk).flatten = Trans.repM blk k
  | 0 => rfl
  | k+1 => by
    rw [List.range_succ_eq_map, List.map_cons, List.flatten_cons, List.map_map]
    show blk ++ ((List.range k).map fun _ => blk).flatten = blk ++ Trans.repM blk k
    rw [flat_const k]

/-- **行列の側。証明済み。** -/
theorem expand_F3a (n : Nat) : BMS.expand M n = M.take 8 ++ Trans.repM blk (n+1) := by
  show (BMS.expand? M n).getD [] = _
  have h : BMS.expand? M n
      = some (M.take 8 ++ ((List.range (n+1)).map fun a =>
          ([[4 + a*0*1, 0 + a*0*1], [5 + a*0*1, 1 + a*0*1],
            [6 + a*0*1, 1 + a*0*1]] : Matrix)).flatten) := rfl
  have hf : (fun a => ([[4 + a*0*1, 0 + a*0*1], [5 + a*0*1, 1 + a*0*1],
      [6 + a*0*1, 1 + a*0*1]] : Matrix)) = (fun _ => blk) := by funext a; simp [blk]
  rw [h, hf, flat_const (n+1)]
  rfl

#guard (List.range 6).all fun n => BMS.expand M n == M.take 8 ++ Trans.repM blk (n+1)

/-! ### 値の側 — 4 段降りると平坦な連鎖になる

`decP` を 4 回かけると `repM [[0,0],[1,1],[2,1]] (n+1)` だけが残る。各複製は先頭が
`(0,0)` なので**それぞれが 1 ブロック**になり、畳み込みは `plus · ζ₀` を n+1 回積むだけ。
**深さは n に依らない**ので `oLAux_chain` は要らない (冒頭の測定表を見よ)。

    level 0  [11+3n]   1  [2, 8+3n]   2  [1, 7+3n]   3  [2, 4+3n]
    level 4  (n+1) 個の [3]

途中の 2 段が `oLV_pre` (前置き `(0,1)(1,1)` の後にもう 1 ブロック)、
残る 2 段が `oLV_single`、最後が `oLV_preZ` の連鎖である。 -/

def U : Matrix := [[0,1],[1,1]]
/-- ζ₀ = φ̄(2,0)。複製 1 つが積む量。 -/
def A : Term := phi (add TM.Term.one TM.Term.one) zero
theorem A_eq : oLV 1 U = A := rfl

def chain : Nat → Term
  | 0 => zero
  | k+1 => plus (chain k) (omegaNF A)

theorem chain_eq : ∀ k, oLV 2 (Trans.repM ([[0,0],[1,1],[2,1]] : Matrix) k) = chain k
  | 0 => rfl
  | k+1 => by
    rw [← Trans.repM_append ([[0,0],[1,1],[2,1]] : Matrix) k,
        oLV_preZ 2 (Trans.repM ([[0,0],[1,1],[2,1]] : Matrix) k) ([0,0] : BMS.Col)
          ([[1,1],[2,1]] : Matrix) rfl rfl (by decide),
        chain_eq k]
    rfl

/-- 値側が出すべき閉じた式。 -/
def valExpr (n : Nat) : Term :=
  plus zero (omegaNF (Trans.Pair.phiStep (ofNat 1) A
    (plus zero (omegaNF (Trans.Pair.phiStep (ofNat 1) A (chain (n+1)))))))

set_option maxHeartbeats 1000000 in
/-- **値の側。証明済み。** `show` を使わず `rw` の連鎖だけで降りる。 -/
theorem val (n : Nat) : o? (BMS.expand M n) = some (valExpr n) := by
  have hb : ∀ x ∈ blk, Trans.Pair.r0 x ≠ 0 := by decide
  have h0 : Trans.onlyRow0 (M.take 8 ++ Trans.repM blk (n+1)) = false :=
    onlyRow0_append_false _ _ rfl
  have hfr : Trans.Pair.inFrag (M.take 8 ++ Trans.repM blk (n+1)) = true := by
    rw [Rows.ProofsB.inFrag_append, inFrag_repM blk rfl (n+1)]; rfl
  have d0 : M.take 8 ++ Trans.repM blk (n+1)
      = ([0,0] : BMS.Col) ::
        (([[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1]] : Matrix) ++ Trans.repM blk (n+1)) := rfl
  have d1 : Trans.Pair.decP
        (([[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1]] : Matrix) ++ Trans.repM blk (n+1))
      = U ++ (([0,1] : BMS.Col) ::
          (([[1,0],[2,1],[3,1],[2,1]] : Matrix)
            ++ Trans.repM ([[3,0],[4,1],[5,1]] : Matrix) (n+1))) := by
    rw [Rows.ProofsB.decP_append, decP_repM]; rfl
  have d2 : Trans.Pair.decP (([[1,0],[2,1],[3,1],[2,1]] : Matrix)
        ++ Trans.repM ([[3,0],[4,1],[5,1]] : Matrix) (n+1))
      = ([0,0] : BMS.Col) :: (([[1,1],[2,1],[1,1]] : Matrix)
          ++ Trans.repM ([[2,0],[3,1],[4,1]] : Matrix) (n+1)) := by
    rw [Rows.ProofsB.decP_append, decP_repM]; rfl
  have d3 : Trans.Pair.decP (([[1,1],[2,1],[1,1]] : Matrix)
        ++ Trans.repM ([[2,0],[3,1],[4,1]] : Matrix) (n+1))
      = U ++ (([0,1] : BMS.Col) :: Trans.repM ([[1,0],[2,1],[3,1]] : Matrix) (n+1)) := by
    rw [Rows.ProofsB.decP_append, decP_repM]; rfl
  have d4 : Trans.Pair.decP (Trans.repM ([[1,0],[2,1],[3,1]] : Matrix) (n+1))
      = Trans.repM ([[0,0],[1,1],[2,1]] : Matrix) (n+1) := by
    rw [decP_repM]; rfl
  rw [expand_F3a n, Evidence.StageB.o?_oLV h0 hfr]
  congr 1
  rw [d0, oLV_single 1 _ _ (r0_app _ (by decide) blk hb (n+1)) rfl, d1,
      oLV_pre 1 U _ _ rfl rfl (r0_app _ (by decide) _ (by decide) (n+1)), d2,
      oLV_single 2 _ _ (r0_app _ (by decide) _ (by decide) (n+1)) rfl, d3,
      oLV_pre 1 U _ _ rfl rfl (r0_repM _ (by decide) (n+1)), d4, chain_eq (n+1), A_eq]
  rfl

/-! ### 算術。`n = 0` は塔が 1 本足りないのでここに入らない (`e3ClaimFrom1` の由来) -/

/-- `ζ₀·(j+2)`。**和の形で持つ**と `omegaNF`・`phiNF` の畳み込みが全部 `rfl` になる。 -/
def AW (j : Nat) : Term := add A (mulNat A (j+1))

theorem AW_eq (j : Nat) : mulNat A (j+2) = AW j := rfl

theorem chain_mul : ∀ k, chain k = mulNat A k
  | 0 => rfl
  | k+1 => by
    show plus (chain k) (omegaNF A) = _
    rw [chain_mul k, show omegaNF A = A from rfl]
    exact Rows.ProofsB.plus_mulNat (show A.isAP = true from rfl) k

/-! `ζ₀ < ω^(ζ₀·(j+2)) < φ̄(1, ω^(ζ₀·(j+2)))`。どれも和の頭が ζ₀ で決まるので、
`Rows/ProofsB.lean` の `ltF_…_not_lt` と同じ形の燃料帰納で潰れる。 -/

theorem ltF_AW_A : ∀ (f j : Nat), TM.Term.ltF f (AW j) A = false
  | 0, _ => rfl
  | f+1, j => by
    show (if ((add A (mulNat A (j+1)) : Term) == A) = true then false
          else TM.Term.ltF f A A) = false
    simp only [show ((add A (mulNat A (j+1)) : Term) == A) = false from rfl,
      Bool.false_eq_true, if_false]
    exact Rows.ProofsB.ltF_irrefl f A

theorem ltF_pAW_A : ∀ (f j : Nat), TM.Term.ltF f (phi zero (AW j)) A = false
  | 0, _ => rfl
  | f+1, j => by
    show (if ((phi zero (AW j) : Term) == A) = true then false
          else if ((zero : Term) == add TM.Term.one TM.Term.one) = true then
            TM.Term.ltF f (AW j) zero
          else if TM.Term.ltF f zero (add TM.Term.one TM.Term.one) = true then
            TM.Term.ltF f (AW j) A
          else ((phi zero (AW j) : Term) == zero)
            || TM.Term.ltF f (phi zero (AW j)) zero) = false
    simp only [show ((phi zero (AW j) : Term) == A) = false from rfl,
      show ((zero : Term) == add TM.Term.one TM.Term.one) = false from rfl,
      Bool.false_eq_true, if_false]
    cases hlt : TM.Term.ltF f zero (add TM.Term.one TM.Term.one) with
    | true => simp only [if_true]; exact ltF_AW_A f j
    | false =>
      simp only [Bool.false_eq_true, if_false,
        show ((phi zero (AW j) : Term) == zero) = false from rfl, Bool.false_or]
      exact Rows.ProofsB.ltF_lt_zero f _

theorem ltF_qAW_A : ∀ (f j : Nat),
    TM.Term.ltF f (phi TM.Term.one (phi zero (AW j))) A = false
  | 0, _ => rfl
  | f+1, j => by
    show (if ((phi TM.Term.one (phi zero (AW j)) : Term) == A) = true then false
          else if ((TM.Term.one : Term) == add TM.Term.one TM.Term.one) = true then
            TM.Term.ltF f (phi zero (AW j)) zero
          else if TM.Term.ltF f TM.Term.one (add TM.Term.one TM.Term.one) = true then
            TM.Term.ltF f (phi zero (AW j)) A
          else ((phi TM.Term.one (phi zero (AW j)) : Term) == zero)
            || TM.Term.ltF f (phi TM.Term.one (phi zero (AW j))) zero) = false
    simp only [show ((phi TM.Term.one (phi zero (AW j)) : Term) == A) = false from rfl,
      show ((TM.Term.one : Term) == add TM.Term.one TM.Term.one) = false from rfl,
      Bool.false_eq_true, if_false]
    cases hlt : TM.Term.ltF f TM.Term.one (add TM.Term.one TM.Term.one) with
    | true => simp only [if_true]; exact ltF_pAW_A f j
    | false =>
      simp only [Bool.false_eq_true, if_false,
        show ((phi TM.Term.one (phi zero (AW j)) : Term) == zero) = false from rfl, Bool.false_or]
      exact Rows.ProofsB.ltF_lt_zero f _

theorem le_pAW_A (j : Nat) : le (phi zero (AW j)) A = false := by
  show ((phi zero (AW j) == A) || lt (phi zero (AW j)) A) = false
  simp only [show ((phi zero (AW j) : Term) == A) = false from rfl, Bool.false_or]
  exact ltF_pAW_A _ j

theorem le_qAW_A (j : Nat) : le (phi TM.Term.one (phi zero (AW j))) A = false := by
  show ((phi TM.Term.one (phi zero (AW j)) == A) || lt (phi TM.Term.one (phi zero (AW j))) A)
      = false
  simp only [show ((phi TM.Term.one (phi zero (AW j)) : Term) == A) = false from rfl,
    Bool.false_or]
  exact ltF_qAW_A _ j

theorem toList_AW (j : Nat) : toList (AW j) = List.replicate (j+2) A := by
  show A :: toList (mulNat A (j+1)) = _
  rw [Rows.ProofsB.toList_mulNat (show A.isAP = true from rfl) (j+1)]
  rfl

theorem takeWhile_replA : ∀ i,
    (List.replicate i A).takeWhile (fun x => x == TM.Term.one) = []
  | 0 => rfl
  | i+1 => by
    rw [List.replicate_succ, List.takeWhile_cons]
    simp [show (A == TM.Term.one) = false from rfl]

theorem take_replA : ∀ i, List.take i (List.replicate i A) = List.replicate i A
  | 0 => rfl
  | i+1 => by rw [List.replicate_succ, List.take_succ_cons, take_replA i]

theorem splitFin_AW (j : Nat) : splitFin (AW j) = (AW j, 0) := by
  have hl := toList_AW j
  show (ofList ((toList (AW j)).take
        ((toList (AW j)).length -
          ((toList (AW j)).reverse.takeWhile (fun x => x == TM.Term.one)).length)),
      ((toList (AW j)).reverse.takeWhile (fun x => x == TM.Term.one)).length) = _
  rw [hl, List.reverse_replicate, takeWhile_replA (j+2)]
  simp only [List.length_nil, Nat.sub_zero, List.length_replicate, take_replA]
  exact congrArg (fun x => (x, 0)) (AW_eq j)

theorem phiNF_zero_AW (j : Nat) : phiNF zero (AW j) = phi zero (AW j) := by
  show phiNFsucc zero (AW j) = _
  unfold phiNFsucc
  rw [splitFin_AW j]
  rfl

theorem step1 (j : Nat) :
    Trans.Pair.phiStep (ofNat 1) A (AW j) = phi TM.Term.one (phi zero (AW j)) := by
  show phiNF (ofNat 1) (plus A (omegaNF (AW j))) = _
  rw [show omegaNF (AW j) = phiNF zero (AW j) from rfl, phiNF_zero_AW j,
      Rows.ProofsB.plus_drop (show A.isAP = true from rfl)
        (show (phi zero (AW j)).isAP = true from rfl) (le_pAW_A j)]
  rfl

theorem step2 (j : Nat) :
    Trans.Pair.phiStep (ofNat 1) A (phi TM.Term.one (phi zero (AW j)))
      = phi TM.Term.one (phi TM.Term.one (phi zero (AW j))) := by
  show phiNF (ofNat 1) (plus A (omegaNF (phi TM.Term.one (phi zero (AW j))))) = _
  rw [show omegaNF (phi TM.Term.one (phi zero (AW j)))
        = phi TM.Term.one (phi zero (AW j)) from rfl,
      Rows.ProofsB.plus_drop (show A.isAP = true from rfl)
        (show (phi TM.Term.one (phi zero (AW j))).isAP = true from rfl) (le_qAW_A j)]
  rfl

/-- `plus zero ∘ omegaNF` は φ̄(1,·) の上では恒等。 -/
theorem wrap (Y : Term) : plus zero (omegaNF (phi TM.Term.one Y)) = phi TM.Term.one Y := by
  rw [show omegaNF (phi TM.Term.one Y) = phi TM.Term.one Y from rfl]
  exact Rows.ProofsB.plus_zero_left rfl

/-- **項の側。証明済み。** 外の 3 枚は極限の節で剥がれ、最内は
    φ̄(0, ζ₀) の引数が「不動点ずらし」で後続扱いになるので `ω^{c+1}[n] = ω^c·n` になる。 -/
theorem fsN_t_eq (k : Nat) :
    fsN t k = phiNF TM.Term.one (phiNF TM.Term.one (phiNF zero (mulNat A k))) := by
  show fsN (phi TM.Term.one (phi TM.Term.one (phi zero (phi zero A)))) k = _
  rw [Rows.ProofsB.fsN_phi_lim rfl rfl, Rows.ProofsB.fsN_phi_lim rfl rfl,
      Rows.ProofsB.fsN_phi_lim rfl rfl,
      show fsN (phi zero A) k = mulNat (omegaNF A) k from by rw [fsN]; rfl]
  rfl

/-- **算術。証明済み。** -/
theorem arith (n : Nat) : valExpr (n+1) = fsN t (n+2) := by
  rw [fsN_t_eq (n+2), AW_eq n, phiNF_zero_AW n]
  show plus zero (omegaNF (Trans.Pair.phiStep (ofNat 1) A
    (plus zero (omegaNF (Trans.Pair.phiStep (ofNat 1) A (chain (n+2))))))) = _
  rw [chain_mul (n+2), AW_eq n, step1 n, wrap, step2 n, wrap]
  rfl

/-- **E3。証明済み。** ただし添字は 1 から — `n = 0` は基本列の上に無い (上の `#guard`)。 -/
theorem e3 : e3ClaimFrom1 := by
  intro n; rw [val (n+1), arith n]

/-! ### 外部の表の値は、同じ試験を通らない -/

/-- 先方の値 ([diff.md](../../table/diff.md) 族 3 の 265 行目)。先方の構文解析器で訳した。 -/
def tHex : Term := phiNF (ofNat 1) (phiNF (ofNat 1) (phiNF zero
  (add (phiNF (ofNat 2) zero) (ofNat 1))))

#guard !(o? M == some tHex)
#guard kindT tHex == KindT.isLim
#guard (List.range 6).all fun k => (List.range 8).any fun n =>
  !(o? (BMS.expand M n) == some (fsN tHex (n + k)))
-- **0 番目だけ偶然当たる** (`fsN tHex 2`)。1 番目から先は先方の基本列に 30 項まで無い。
-- E3 は全 n で固定の添字を要求するので、上のずらしの不成立で反証は足りている。
#guard (List.range 4).all fun n => (List.range 30).all fun j =>
  !(o? (BMS.expand M (n+1)) == some (fsN tHex j))
#guard (List.range 30).any fun j => o? (BMS.expand M 0) == some (fsN tHex j)
-- CTRL 同じ探索は当方の値では当たる (n = 0 を除く。上の `#guard` の通り)
#guard (List.range 4).all fun n => (List.range 30).any fun j =>
  o? (BMS.expand M (n+1)) == some (fsN t j)

#guard (List.range 5).all fun n => o? (BMS.expand M n) == some (valExpr n)
#guard (List.range 5).all fun n => valExpr (n+1) == fsN t (n+2)

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

/-! ### 行列の側と算術。残るのは値側の 6 段降下だけ

梯子で底は 6。`decP` のたびに底が 1 下がるので 6 段降りるが、**深さは n に依らない**。
各段のブロック長 (n = 2 で測定):

    level 0  [14]    1  [2, 11]    2  [1, 1, 10]    3  [1, 1, 2, 7]
    level 4  [1, 1, 1, 1, 6]       5  [1, 1, 1, 1, 2, 3]    6  [1, 1, 1, 1, 1, 1, 2]

`valExpr` は値側が出すべき閉じた式で、`phiStep` が 2 枚と `plus` が 1 枚。
**算術はそれで閉じている** (`arith_F3b`)。残りは `o? (M[n]) = valExpr n` である。 -/

def P : Matrix := [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[4,0],[5,1],[6,1],[5,0]]

/-- **行列の側。証明済み。** -/
theorem expand_F3b (n : Nat) : BMS.expand M n = P ++ zeroLad 6 n := by
  show (BMS.expand? M n).getD [] = _
  have h : BMS.expand? M n
      = some (M.take 11 ++ ((List.range (n+1)).map fun a =>
          ([[5 + a*1*1, 0 + a*0*1]] : Matrix)).flatten) := rfl
  have hf : (fun a => ([[5 + a*1*1, 0 + a*0*1]] : Matrix))
      = (fun a => ([[5+a,0]] : Matrix)) := by funext a; simp
  rw [h, hf, lad_flatten (n+1) 5]
  rfl

def U : Matrix := [[0,1],[1,1]]
def A : Term := oLV 1 U

/-- 値側が出すべき閉じた式。 -/
def valExpr (n : Nat) : Term :=
  plus zero (omegaNF
    (Trans.Pair.phiStep TM.Term.one A
      (plus zero (omegaNF
        (Trans.Pair.phiStep TM.Term.one A
          (plus zero (omegaNF (plus A (iterT zero (n + 1))))))))))

/-- 算術。**未証明。**

    `codex:rescue` の作業役が `rfl` で通ると報告し、その時点では
    `leanman check` が 0 を返した。**ここでは通らない。** `#print axioms` を当てると
    `sorryAx` が出る — Lean は失敗した elaboration を `sorryAx` で埋めるので、
    エラーのある状態での `sorryAx` は「証明できていない」の意味である
    (`lean/scripts/axiom_sweep.lean` 冒頭に同じ注意がある)。
    **終了コードだけでは足りず、公理も見なければならない。**

    式そのものは正しい。有限では合っている (下の `#guard`)。

    **書きかけて分かった罠が 2 つある。どちらも「一般に成り立つ」と書きたくなる形である。**

    1. `phiNF zero (add A X) = phi zero (add A X)` は **X = 1 のとき偽**。`splitFin` が
       末尾の 1 を取って `g = A` を返し、`A = φ̄(2,0)` は `phi d _` の形なので
       `lt 0 d` が真になり、`φ̄(0,A)` に畳まれる。塔は `n = 0` でちょうど 1 になるので、
       この場合分けは避けられない。φ̄ の不動点飛ばしが**また**別の場所で出た。
    2. `omegaNF W = phiNF zero W` は `lt M W` が W の**頭**だけで決まるので `rfl` で通る。
       頭は A で、塔はそこに入らない。F1 と同じ理屈だが、`plus` を畳む前に当てても
       通らない (項の形が違う)。順序は plus → omegaNF → phiNF である。 -/
def arithClaim : Prop := ∀ n, valExpr n = fsN t (n + 1)

def Z0 (n : Nat) : Term := plus A (iterT zero (n+1))
def Z1 (n : Nat) : Term := phiNF zero (Z0 n)
def Z2 (n : Nat) : Term := phiNF zero (Z1 n)
def Z3 (n : Nat) : Term := phiNF TM.Term.one (Z2 n)
def Z4 (n : Nat) : Term := phiNF TM.Term.one (Z3 n)

/-- `t = φ̄(1, φ̄(1, φ̄(0, φ̄(0, ζ₀+ε₀))))`。各層の引数は極限でずれも無いので
    `fsN_phi_lim` が 4 回当たり、最後は和の節と ε₀ の基本列。 -/
theorem fsN_t_eq (n : Nat) : fsN t (n+1) = Z4 n := by
  show fsN (phi TM.Term.one (phi TM.Term.one (phi zero (phi zero (add A e0))))) (n+1) = _
  rw [Rows.ProofsB.fsN_phi_lim rfl rfl, Rows.ProofsB.fsN_phi_lim rfl rfl,
      Rows.ProofsB.fsN_phi_lim rfl rfl, Rows.ProofsB.fsN_phi_lim rfl rfl,
      fsN_add, fsN_e0]
  rfl

theorem lt_tower_A (m : Nat) : lt (iterT zero m) A = true :=
  lt_iterT_bd Rows.ProofsB.isSC_zero rfl
    (fun f _ => Rows.ProofsB.ltF_zero (by omega) (by intro h; exact Term.noConfusion h)) m

theorem Z0_eq (n : Nat) : Z0 n = add A (iterT zero (n+1)) := by
  have hb : le (iterT zero (n+1)) A = true := by
    show ((iterT zero (n+1) == A) || lt (iterT zero (n+1)) A) = true
    rw [lt_tower_A (n+1)]; exact Bool.or_true _
  have hT : iterT zero (n+1) = phi zero (iterT zero n) :=
    Rows.ProofsB.iterT_succ Rows.ProofsB.isSC_zero n
  show plus A (iterT zero (n+1)) = _
  rw [hT] at hb ⊢
  show ofList ((toList A).filter (fun a => le (phi zero (iterT zero n)) a)
        ++ [phi zero (iterT zero n)]) = _
  rw [show toList A = [A] from rfl]
  simp only [List.filter_cons, hb, List.filter_nil]
  rfl

theorem tower_ne_one (m : Nat) : (iterT zero (m+2) == TM.Term.one) = false := by
  have h := Rows.ProofsB.iterT_ne_zero Rows.ProofsB.isSC_zero m
  rw [Rows.ProofsB.iterT_succ Rows.ProofsB.isSC_zero (m+1)]
  simp [TM.Term.one, h]

/-! ### 層をはがす補題のうち、どれが一般でどれが具体形を要るか (測定・部分証明済み)

`W` を記号のままにして 7 つ試したところ、**一般に `rfl` で通るのは 4 つだけ**だった。

    omegaNF (add A W) = phiNF zero (add A W)              一般。頭が A で決まる
    plus zero (phi zero V) = phi zero V                   一般
    plus zero (phi 1 V) = phi 1 V                         一般
    omegaNF (phi 1 V) = phi 1 V                           一般
    omegaNF (phi zero V) = phi zero (phi zero V)          **`V ≠ 0` が要る** (証明済み)
    phiStep 1 A (phi zero V) = phi 1 (phi zero (phi zero V))   **具体形が要る**
    phiStep 1 A (phi 1 V) = phi 1 (phi 1 V)                    **具体形が要る**

最後の 2 つが要求するのは `plus A X = X`、つまり A が呑まれることで、これは
`le X A = false` すなわち `lt A X`。`lt A (phi zero X)` は [Rathjen, 1991] 2.3.4 で `A ≤ X` に落ち、
X が `add A …` の形なら和の節が `A == A` で即決する — **だから V を記号のままにはできず、
`add A (塔)` という具体形まで開く必要がある**。逆に言えばそこまで開けば安い。

項側は済んだ (`fsN_t_eq`)。算術に残るのは `valExpr n = Z4 n`、すなわち
    `plus zero`・`omegaNF`・`phiStep` の 3 種類の畳み込みを 5 層はがすことである。
    層ごとの形は `Z1 (m+1) = φ̄(0, A + 塔)` から始まるが、**n = 0 は別扱いが要る**
    (塔が 1 になり `splitFin` が畳む。上の注意 1)。 -/

theorem Z1_shape (m : Nat) : Z1 (m+1) = phi zero (add A (iterT zero (m+2))) := by
  have hT : iterT zero (m+2) = phi zero (iterT zero (m+1)) :=
    Rows.ProofsB.iterT_succ Rows.ProofsB.isSC_zero (m+1)
  have hone : (phi zero (iterT zero (m+1)) == TM.Term.one) = false := by
    rw [← hT]; exact tower_ne_one m
  show phiNF zero (Z0 (m+1)) = _
  rw [Z0_eq (m+1), hT]
  show phiNFsucc zero (add A (phi zero (iterT zero (m+1)))) = _
  unfold phiNFsucc
  rw [show splitFin (add A (phi zero (iterT zero (m+1))))
        = (add A (phi zero (iterT zero (m+1))), 0) from by
    unfold splitFin
    rw [show (add A (phi zero (iterT zero (m+1)))).toList
          = [A, phi zero (iterT zero (m+1))] from rfl]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.takeWhile_cons, hone, List.length_nil, Nat.sub_zero]
    rfl]
  rfl

/-- A が呑まれる。`X` が加法主要項で `X > A` のとき。 -/
theorem plus_absorb (a b : Term) (h : le (phi a b) A = false) :
    plus A (phi a b) = phi a b := by
  show ofList ((toList A).filter (fun x => le (phi a b) x) ++ [phi a b]) = _
  rw [show toList A = [A] from rfl]
  simp only [List.filter_cons, h, List.filter_nil]
  rfl

theorem le_Z2 (W : Term) : le (phi zero (phi zero (add A W))) A = false := rfl
theorem le_Z3 (V : Term) : le (phi TM.Term.one (phi zero (phi zero (add A V)))) A = false := rfl

/-- `phiStep` を一度だけ開く。`logPhi 1 A = some A` と `X ≠ 0`。 -/
theorem phiStep_A (X : Term) (hX : (X == zero) = false) :
    Trans.Pair.phiStep TM.Term.one A X = phiNF TM.Term.one (plus A (omegaNF X)) := by
  unfold Trans.Pair.phiStep
  rw [show Trans.Pair.logPhi TM.Term.one A = some A from rfl, hX]

/-- 段 0: 一番内側。 -/
theorem s0 (m : Nat) :
    plus zero (omegaNF (plus A (iterT zero (m+2)))) = phi zero (add A (iterT zero (m+2))) := by
  have hz : plus A (iterT zero (m+2)) = add A (iterT zero (m+2)) := Z0_eq (m+1)
  have h1 : phiNF zero (plus A (iterT zero (m+2)))
      = phi zero (add A (iterT zero (m+2))) := Z1_shape m
  rw [show omegaNF (plus A (iterT zero (m+2))) = phiNF zero (plus A (iterT zero (m+2))) from by
        rw [hz]; rfl, h1]
  rfl

/-- 段 1: `phiStep` が 1 枚。 -/
theorem s1 (X : Term) (h2 : omegaNF (phi zero (add A X)) = phi zero (phi zero (add A X))) :
    Trans.Pair.phiStep TM.Term.one A (phi zero (add A X))
      = phi TM.Term.one (phi zero (phi zero (add A X))) := by
  rw [phiStep_A _ rfl, h2, plus_absorb _ _ (le_Z2 X)]
  rfl

/-- 段 2: `φ̄(1,·)` の上では `plus zero` も `omegaNF` も素通り。 -/
theorem s2 (V : Term) : plus zero (omegaNF (phi TM.Term.one V)) = phi TM.Term.one V := rfl

/-- 段 3: 2 枚目の `phiStep`。 -/
theorem s3 (X : Term) :
    Trans.Pair.phiStep TM.Term.one A (phi TM.Term.one (phi zero (phi zero (add A X))))
      = phi TM.Term.one (phi TM.Term.one (phi zero (phi zero (add A X)))) := by
  rw [phiStep_A _ rfl,
      show omegaNF (phi TM.Term.one (phi zero (phi zero (add A X))))
        = phi TM.Term.one (phi zero (phi zero (add A X))) from rfl,
      plus_absorb _ _ (le_Z3 X)]
  rfl

theorem e2p (X : Term) : phiNF zero (phi zero (add A X)) = phi zero (phi zero (add A X)) := by
  show phiNFsucc zero (phi zero (add A X)) = _
  unfold phiNFsucc
  rw [show splitFin (phi zero (add A X)) = (phi zero (add A X), 0) from by
    unfold splitFin
    rw [show (phi zero (add A X)).toList = [phi zero (add A X)] from rfl]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.takeWhile_cons,
      show (phi zero (add A X) == TM.Term.one) = false from rfl,
      List.length_nil, Nat.sub_zero]
    rfl]
  rfl

set_option maxHeartbeats 2000000 in
theorem arith_succ (m : Nat) : valExpr (m+1) = Z4 (m+1) := by
  show plus zero (omegaNF (Trans.Pair.phiStep TM.Term.one A
    (plus zero (omegaNF (Trans.Pair.phiStep TM.Term.one A
      (plus zero (omegaNF (plus A (iterT zero (m+2)))))))))) = _
  rw [s0 m]
  rw [s1 (iterT zero (m+2)) (e2p (iterT zero (m+2)))]
  rw [s2 (phi zero (phi zero (add A (iterT zero (m+2)))))]
  rw [s3 (iterT zero (m+2))]
  rw [s2 (phi TM.Term.one (phi zero (phi zero (add A (iterT zero (m+2))))))]
  show _ = phiNF TM.Term.one (Z3 (m+1))
  rw [show Z3 (m+1) = phiNF TM.Term.one (Z2 (m+1)) from rfl,
      show Z2 (m+1) = phiNF zero (Z1 (m+1)) from rfl, Z1_shape m,
      e2p (iterT zero (m+2))]
  rfl

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- **算術。証明済み。** `fsN` は整礎再帰なので定義的には簡約しない。先に `fsN_t_eq` で
    `Z4` に置き換えると、残りは `phiNF`・`omegaNF`・`plus` だけの構造的な計算になる。
    n = 0 は塔がちょうど 1 になって段の形が崩れるが、閉じているのでそのまま計算できる。 -/
theorem arith : arithClaim
  | 0 => by rw [fsN_t_eq 0]; rfl
  | m+1 => by rw [arith_succ m, fsN_t_eq (m+1)]

def T1 (n : Nat) : Matrix := [[1,0],[2,1],[3,1],[2,1],[3,0],[4,1],[5,1]] ++ zeroLad 4 (n+1)
def T2 (n : Nat) : Matrix := [[1,1],[2,1],[1,1],[2,0],[3,1],[4,1]] ++ zeroLad 3 (n+1)
def T3 (n : Nat) : Matrix := [[1,0],[2,1],[3,1]] ++ zeroLad 2 (n+1)
def T4 (n : Nat) : Matrix := [[1,1],[2,1]] ++ zeroLad 1 (n+1)




/-- 梯子の段。ここで塔が出る。 -/
theorem oLV_pre_lad (n : Nat) : oLV 1 (U ++ zeroLad 0 (n+1)) = plus A (iterT zero (n+1)) := by
  rw [Evidence.StageB.oLV_eq,
      Evidence.StageB.blocksP_append U (zeroLad 0 (n+1))
        (Or.inr ⟨[0,0], zeroLad 1 n, rfl, rfl⟩),
      List.foldl_append,
      show zeroLad 0 (n+1) = ([0,0] : BMS.Col) :: zeroLad 1 n from rfl,
      Rows.ProofsB.blocksP_single ([0,0] : BMS.Col) (zeroLad 1 n) (r0_zeroLad n 1 (by omega)),
      ← Evidence.StageB.oLV_eq 1 U]
  show plus (oLV 1 U) (omegaNF (oLV 1 (Trans.Pair.decP (zeroLad 1 n)))) = _
  rw [decP_zeroLad n 0, oLV_zeroLad n 1, omegaNF_iterT n]
  rfl

/-! 段ごとの `decP`。cons の形で出すので `show` が要らない。 -/

theorem d1 (n : Nat) :
    Trans.Pair.decP (P.tail ++ zeroLad 6 n) = U ++ (([0,1] : BMS.Col) :: T1 n) := by
  rw [Rows.ProofsB.decP_append, decP_zeroLad n 5]; rfl
theorem d2 (n : Nat) : Trans.Pair.decP (T1 n) = ([0,0] : BMS.Col) :: T2 n := by
  rw [show T1 n = [[1,0],[2,1],[3,1],[2,1],[3,0],[4,1],[5,1]] ++ zeroLad 4 (n+1) from rfl,
      Rows.ProofsB.decP_append, decP_zeroLad (n+1) 3]; rfl
theorem d3 (n : Nat) : Trans.Pair.decP (T2 n) = U ++ (([0,1] : BMS.Col) :: T3 n) := by
  rw [show T2 n = [[1,1],[2,1],[1,1],[2,0],[3,1],[4,1]] ++ zeroLad 3 (n+1) from rfl,
      Rows.ProofsB.decP_append, decP_zeroLad (n+1) 2]; rfl
theorem d4 (n : Nat) : Trans.Pair.decP (T3 n) = ([0,0] : BMS.Col) :: T4 n := by
  rw [show T3 n = [[1,0],[2,1],[3,1]] ++ zeroLad 2 (n+1) from rfl,
      Rows.ProofsB.decP_append, decP_zeroLad (n+1) 1]; rfl
theorem d5 (n : Nat) : Trans.Pair.decP (T4 n) = U ++ zeroLad 0 (n+1) := by
  rw [show T4 n = [[1,1],[2,1]] ++ zeroLad 1 (n+1) from rfl,
      Rows.ProofsB.decP_append, decP_zeroLad (n+1) 0]; rfl

theorem r0_T1 (n : Nat) : ∀ x ∈ T1 n, Trans.Pair.r0 x ≠ 0 :=
  r0_L 4 (n+1) _ (by decide) (by omega)
theorem r0_T2 (n : Nat) : ∀ x ∈ T2 n, Trans.Pair.r0 x ≠ 0 :=
  r0_L 3 (n+1) _ (by decide) (by omega)
theorem r0_T3 (n : Nat) : ∀ x ∈ T3 n, Trans.Pair.r0 x ≠ 0 :=
  r0_L 2 (n+1) _ (by decide) (by omega)
theorem r0_T4 (n : Nat) : ∀ x ∈ T4 n, Trans.Pair.r0 x ≠ 0 :=
  r0_L 1 (n+1) _ (by decide) (by omega)

set_option maxHeartbeats 2000000 in
/-- **値の側。** 5 段の降下。`show` を使わず `rw` の連鎖だけで降りる。 -/
theorem val (n : Nat) : o? (BMS.expand M n) = some (valExpr n) := by
  have hlen : (P ++ zeroLad 6 n).length ≤ (P ++ zeroLad 6 n).length + 1 := by omega
  have h0 : Trans.onlyRow0 (P ++ zeroLad 6 n) = false :=
    onlyRow0_append_false P (zeroLad 6 n) rfl
  have hf : Trans.Pair.inFrag (P ++ zeroLad 6 n) = true := by
    rw [Rows.ProofsB.inFrag_append, inFrag_zeroLad n 6]; rfl
  have hP : ∀ x ∈ P.tail, Trans.Pair.r0 x ≠ 0 := by decide
  rw [expand_F3b n]
  have hstep : o? (P ++ zeroLad 6 n) = some (oLV 1 (P ++ zeroLad 6 n)) := by
    show (if Trans.onlyRow0 _ = true then _ else Trans.oPair? _) = _
    simp only [h0, Bool.false_eq_true, if_false]
    show (if Trans.Pair.inFrag _ = true then some (if Trans.onlyRow0 _ = true then _ else
      Trans.Pair.oLAux ((P ++ zeroLad 6 n).length + 1) 1 (P ++ zeroLad 6 n)) else none) = _
    simp only [hf, h0, Bool.false_eq_true, if_true, if_false]
    rw [Evidence.StageB.oLAux_eq_oLV hlen]
  rw [hstep]
  congr 1
  rw [show P ++ zeroLad 6 n = ([0,0] : BMS.Col) :: (P.tail ++ zeroLad 6 n) from rfl,
      oLV_single _ _ _ (r0_L 6 n P.tail hP (by omega)) rfl, d1 n,
      oLV_pre _ U _ _ rfl rfl (r0_T1 n), d2 n,
      oLV_single _ _ _ (r0_T2 n) rfl, d3 n,
      oLV_pre _ U _ _ rfl rfl (r0_T3 n), d4 n,
      oLV_single _ _ _ (r0_T4 n) rfl, d5 n, oLV_pre_lad n]
  rfl

/-- **E3。証明済み。** 行列側・値側・項側・算術を継ぐ。 -/
theorem e3 : e3Claim := by
  intro n; rw [val n, arith n]

/-! ### 外部の表の値は、同じ試験を通らない -/

/-- 先方の値 ([diff.md](../../table/diff.md) 族 3 の 266 行目)。先方の構文解析器で訳した。 -/
def tHex : Term := phiNF (ofNat 1) (phiNF (ofNat 1) (phiNF zero
  (add (phiNF (ofNat 2) zero) (phiNF (ofNat 1) zero))))

#guard !(o? M == some tHex)
#guard kindT tHex == KindT.isLim
#guard (List.range 6).all fun k => (List.range 8).any fun n =>
  !(o? (BMS.expand M n) == some (fsN tHex (n + k)))
#guard (List.range 4).all fun n => (List.range 30).all fun j =>
  !(o? (BMS.expand M n) == some (fsN tHex j))
-- CTRL 同じ探索は当方の値では当たる
#guard (List.range 4).all fun n => (List.range 30).any fun j =>
  o? (BMS.expand M n) == some (fsN t j)

#guard (List.range 6).all fun n => BMS.expand M n == P ++ zeroLad 6 n
#guard (List.range 4).all fun n => o? (BMS.expand M n) == some (valExpr n)
#guard (List.range 6).all fun n => valExpr n == fsN t (n + 1)

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

/-! ### 行列の側と値の側

悪い部分は 2 列 `(o,0)(o+1,1)` で歩幅 2。`decP` を 6 回かけると `frep` の底が 0 に着き、
そこから先は**自分自身に戻る**: 底 0 の複製列は先頭 `(0,0)` の 1 ブロックになり、その
`decP` が 1 つ少ない複製列を生む。深さは n とともに増えるが、増える部分は 2 項の相互再帰
`H` に閉じているので `oLAux_chain` は要らない。

    H 0     = 0
    H (m+1) = plus zero (ω^(φ̄-step 1 0 (H m)))     = ε 塔 (`H_iterT`)

段の形 (n = 1 で測定、`level (ブロック長)`):

    0 (1) [15]   1 (1) [2,12]   2 (2) [11]   3 (1) [2,8]   4 (2) [7]   5 (1) [2,4]   6 …
-/

def blk2 (o : Nat) : Matrix := [[o,0],[o+1,1]]
def P : Matrix := [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[4,0],[5,1],[6,1]]
def U : Matrix := [[0,1],[1,1]]
/-- ζ₀。F3b と同じ値なので、算術は F3b の補題をそのまま使える (塔だけが違う)。 -/
abbrev A : Term := F3b.A
theorem A_shape : A = phi (add TM.Term.one TM.Term.one) zero := rfl

/-- **行列の側。** 悪い部分は 2 列 `(o,0)(o+1,1)`、歩幅 2。 -/
theorem expand_F3c (n : Nat) : BMS.expand M n = P ++ Rows.ProofsB.frep blk2 2 5 (n+1) := by
  show (BMS.expand? M n).getD [] = _
  have h : BMS.expand? M n
      = some (M.take 11 ++ ((List.range (n+1)).map fun a =>
          ([[5 + a*2*1, 0 + a*0*1], [6 + a*2*1, 1 + a*0*1]] : Matrix)).flatten) := rfl
  have hf : (fun a => ([[5 + a*2*1, 0 + a*0*1], [6 + a*2*1, 1 + a*0*1]] : Matrix))
      = (fun a => blk2 (2*a + 5)) := by
    funext a
    show ([[5 + a*2*1, 0 + a*0*1], [6 + a*2*1, 1 + a*0*1]] : Matrix) = [[2*a+5, 0], [2*a+5+1, 1]]
    rw [show 5 + a*2*1 = 2*a+5 from by omega, show 6 + a*2*1 = 2*a+5+1 from by omega]
    simp
  rw [h, hf, Rows.ProofsB.flat_frep blk2 2 (n+1) 5]
  rfl

theorem decP_blk2 (o : Nat) : Trans.Pair.decP (blk2 (o+1)) = blk2 o := rfl

theorem r0_blk2 (o : Nat) (ho : 1 ≤ o) : ∀ c ∈ blk2 o, Trans.Pair.r0 c ≠ 0 := by
  intro c hc
  rcases List.mem_cons.mp hc with h | h
  · subst h; show o ≠ 0; omega
  · rw [List.mem_singleton.mp h]; show o+1 ≠ 0; omega

theorem decP_F (m o : Nat) : Trans.Pair.decP (Rows.ProofsB.frep blk2 2 (o+1) m) = Rows.ProofsB.frep blk2 2 o m :=
  Rows.ProofsB.decP_frep decP_blk2 m o

theorem r0_F (m o : Nat) (ho : 1 ≤ o) : ∀ c ∈ Rows.ProofsB.frep blk2 2 o m, Trans.Pair.r0 c ≠ 0 :=
  Rows.ProofsB.r0_frep r0_blk2 m o ho

theorem inFrag_F (m o : Nat) : Trans.Pair.inFrag (Rows.ProofsB.frep blk2 2 o m) = true :=
  Rows.ProofsB.inFrag_frep (fun _ => rfl) m o

theorem r0_appF (l : Matrix) (hl : ∀ x ∈ l, Trans.Pair.r0 x ≠ 0) (m o : Nat) (ho : 1 ≤ o) :
    ∀ x ∈ l ++ Rows.ProofsB.frep blk2 2 o m, Trans.Pair.r0 x ≠ 0 := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hl x h
  · exact r0_F m o ho x h

/-! ### ε 塔。`frep` の底が 0 に着いたところから始まる入れ子の再帰 -/

def H : Nat → Term
  | 0 => zero
  | m+1 => plus zero (omegaNF (Trans.Pair.phiStep TM.Term.one zero (H m)))

theorem H_eq : ∀ m, oLV 2 (Rows.ProofsB.frep blk2 2 0 m) = H m
  | 0 => rfl
  | m+1 => by
    rw [show Rows.ProofsB.frep blk2 2 0 (m+1)
          = ([0,0] : BMS.Col) :: (([[1,1]] : Matrix) ++ Rows.ProofsB.frep blk2 2 2 m) from rfl,
        oLV_single 2 _ _ (r0_appF _ (by decide) m 2 (by omega)) rfl,
        show Trans.Pair.decP (([[1,1]] : Matrix) ++ Rows.ProofsB.frep blk2 2 2 m)
          = ([0,1] : BMS.Col) :: Rows.ProofsB.frep blk2 2 1 m from by
          rw [Rows.ProofsB.decP_append, decP_F m 1]; rfl,
        oLV_singleP 1 _ _ (r0_F m 1 (by omega)) rfl, decP_F m 0, H_eq m]
    rfl

def valExpr (n : Nat) : Term :=
  plus zero (omegaNF (Trans.Pair.phiStep TM.Term.one A
    (plus zero (omegaNF (Trans.Pair.phiStep TM.Term.one A
      (plus zero (omegaNF (plus A (H (n+1))))))))))

theorem H_succ (m : Nat) : H (m+1) = omegaNF (Trans.Pair.phiStep TM.Term.one zero (H m)) :=
  Rows.ProofsB.plus_zero_left (Rows.ProofsB.isAP_omegaNF _)

set_option maxHeartbeats 2000000 in
/-- **値の側。** 6 段の降下。最後の段で `frep` の底が 0 に着き、そこから `H` の再帰に入る。 -/
theorem val (n : Nat) : o? (BMS.expand M n) = some (valExpr n) := by
  have h0 : Trans.onlyRow0 (P ++ Rows.ProofsB.frep blk2 2 5 (n+1)) = false :=
    onlyRow0_append_false P _ rfl
  have hfr : Trans.Pair.inFrag (P ++ Rows.ProofsB.frep blk2 2 5 (n+1)) = true := by
    rw [Rows.ProofsB.inFrag_append, inFrag_F (n+1) 5]; rfl
  have d0 : P ++ Rows.ProofsB.frep blk2 2 5 (n+1)
      = ([0,0] : BMS.Col) ::
        (([[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[4,0],[5,1],[6,1]] : Matrix)
          ++ Rows.ProofsB.frep blk2 2 5 (n+1)) := rfl
  have d1 : Trans.Pair.decP
        (([[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[3,1],[4,0],[5,1],[6,1]] : Matrix)
          ++ Rows.ProofsB.frep blk2 2 5 (n+1))
      = U ++ (([0,1] : BMS.Col) ::
          (([[1,0],[2,1],[3,1],[2,1],[3,0],[4,1],[5,1]] : Matrix)
            ++ Rows.ProofsB.frep blk2 2 4 (n+1))) := by
    rw [Rows.ProofsB.decP_append, decP_F (n+1) 4]; rfl
  have d2 : Trans.Pair.decP (([[1,0],[2,1],[3,1],[2,1],[3,0],[4,1],[5,1]] : Matrix)
        ++ Rows.ProofsB.frep blk2 2 4 (n+1))
      = ([0,0] : BMS.Col) :: (([[1,1],[2,1],[1,1],[2,0],[3,1],[4,1]] : Matrix)
          ++ Rows.ProofsB.frep blk2 2 3 (n+1)) := by
    rw [Rows.ProofsB.decP_append, decP_F (n+1) 3]; rfl
  have d3 : Trans.Pair.decP (([[1,1],[2,1],[1,1],[2,0],[3,1],[4,1]] : Matrix)
        ++ Rows.ProofsB.frep blk2 2 3 (n+1))
      = U ++ (([0,1] : BMS.Col) ::
          (([[1,0],[2,1],[3,1]] : Matrix) ++ Rows.ProofsB.frep blk2 2 2 (n+1))) := by
    rw [Rows.ProofsB.decP_append, decP_F (n+1) 2]; rfl
  have d4 : Trans.Pair.decP (([[1,0],[2,1],[3,1]] : Matrix) ++ Rows.ProofsB.frep blk2 2 2 (n+1))
      = ([0,0] : BMS.Col) :: (([[1,1],[2,1]] : Matrix) ++ Rows.ProofsB.frep blk2 2 1 (n+1)) := by
    rw [Rows.ProofsB.decP_append, decP_F (n+1) 1]; rfl
  have d5 : Trans.Pair.decP (([[1,1],[2,1]] : Matrix) ++ Rows.ProofsB.frep blk2 2 1 (n+1))
      = U ++ (([0,0] : BMS.Col) :: (([[1,1]] : Matrix) ++ Rows.ProofsB.frep blk2 2 2 n)) := by
    rw [Rows.ProofsB.decP_append, decP_F (n+1) 0]; rfl
  have d6 : Trans.Pair.decP (([[1,1]] : Matrix) ++ Rows.ProofsB.frep blk2 2 2 n)
      = ([0,1] : BMS.Col) :: Rows.ProofsB.frep blk2 2 1 n := by
    rw [Rows.ProofsB.decP_append, decP_F n 1]; rfl
  rw [expand_F3c n, Evidence.StageB.o?_oLV h0 hfr]
  congr 1
  rw [d0, oLV_single 1 _ _ (r0_appF _ (by decide) (n+1) 5 (by omega)) rfl, d1,
      oLV_pre 1 U _ _ rfl rfl (r0_appF _ (by decide) (n+1) 4 (by omega)), d2,
      oLV_single 2 _ _ (r0_appF _ (by decide) (n+1) 3 (by omega)) rfl, d3,
      oLV_pre 1 U _ _ rfl rfl (r0_appF _ (by decide) (n+1) 2 (by omega)), d4,
      oLV_single 2 _ _ (r0_appF _ (by decide) (n+1) 1 (by omega)) rfl, d5,
      oLV_preZ 1 U _ _ rfl rfl (r0_appF _ (by decide) n 2 (by omega)), d6,
      oLV_singleP 1 _ _ (r0_F n 1 (by omega)) rfl, decP_F n 0, H_eq n,
      show plus (oLV 1 U) (omegaNF (Trans.Pair.phiStep (ofNat 1) zero (H n)))
          = plus A (H (n+1)) from by rw [H_succ n]; rfl]
  rfl

#guard (List.range 5).all fun n => BMS.expand M n == P ++ Rows.ProofsB.frep blk2 2 5 (n+1)
#guard (List.range 5).all fun m => oLV 2 (Rows.ProofsB.frep blk2 2 0 m) == H m
#guard (List.range 5).all fun n => o? (BMS.expand M n) == some (valExpr n)
#guard (List.range 5).all fun n => valExpr n == fsN t (n+1)
#guard (List.range 5).all fun m => H m == iterT TM.Term.one m

/-! ### 算術。F3b と同じ形で、塔だけ ω から ε に替わる -/

theorem H_iterT : ∀ m, H m = iterT TM.Term.one m
  | 0 => rfl
  | m+1 => by
    rw [H_succ m, H_iterT m]
    cases m with
    | zero => rfl
    | succ g =>
      rw [Rows.ProofsB.iterT_succ (show (TM.Term.one : Term).isSC = false from rfl) (g+1),
          Rows.ProofsB.iterT_succ (show (TM.Term.one : Term).isSC = false from rfl) g]
      rfl

theorem H_shape (m : Nat) : H (m+1) = phi TM.Term.one (iterT TM.Term.one m) := by
  rw [H_iterT (m+1), Rows.ProofsB.iterT_succ (show (TM.Term.one : Term).isSC = false from rfl) m]

theorem lt_tower_A (m : Nat) : lt (iterT TM.Term.one m) A = true := by
  rw [A_shape]
  exact lt_iterT_bd rfl rfl
    (fun f hf => by cases f with | zero => omega | succ g => rfl) m

theorem plusA_H (m : Nat) : plus A (H (m+1)) = add A (H (m+1)) := by
  have hb : le (H (m+1)) A = true := by
    show ((H (m+1) == A) || lt (H (m+1)) A) = true
    rw [H_iterT (m+1), lt_tower_A (m+1)]
    exact Bool.or_true _
  rw [H_shape m] at hb ⊢
  show ofList ((toList A).filter (fun a => le (phi TM.Term.one (iterT TM.Term.one m)) a)
        ++ [phi TM.Term.one (iterT TM.Term.one m)]) = _
  rw [show toList A = [A] from rfl]
  simp only [List.filter_cons, hb, List.filter_nil]
  rfl

theorem e1p (m : Nat) :
    phiNF zero (add A (H (m+1))) = phi zero (add A (H (m+1))) := by
  rw [H_shape m]
  show phiNFsucc zero (add A (phi TM.Term.one (iterT TM.Term.one m))) = _
  unfold phiNFsucc
  rw [show splitFin (add A (phi TM.Term.one (iterT TM.Term.one m)))
        = (add A (phi TM.Term.one (iterT TM.Term.one m)), 0) from by
    unfold splitFin
    rw [show (add A (phi TM.Term.one (iterT TM.Term.one m))).toList
          = [A, phi TM.Term.one (iterT TM.Term.one m)] from rfl]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.takeWhile_cons,
      show ((phi TM.Term.one (iterT TM.Term.one m) : Term) == TM.Term.one) = false from rfl]
    rfl]
  rfl

theorem s0 (m : Nat) :
    plus zero (omegaNF (plus A (H (m+1)))) = phi zero (add A (H (m+1))) := by
  rw [show omegaNF (plus A (H (m+1))) = phiNF zero (add A (H (m+1))) from by
        rw [plusA_H m]; rfl,
      e1p m]
  rfl

theorem iterPhiAt_zero_gen (a : Term) : ∀ m, TM.Term.iterPhiAt a zero m = iterT a m
  | 0 => rfl
  | m+1 => by
    show phiNF a (TM.Term.iterPhiAt a zero m) = phiNF a (iterT a m)
    rw [iterPhiAt_zero_gen a m]

theorem fsN_A (k : Nat) : fsN A k = iterT TM.Term.one k := by
  show fsN (phi (add TM.Term.one TM.Term.one) zero) k = _
  rw [fsN]
  exact iterPhiAt_zero_gen TM.Term.one k

/-- **項の側。** 4 枚とも極限の節で剥がれ、最後は和の節と ζ₀ の基本列 (ε 塔)。 -/
theorem fsN_t_eq (k : Nat) :
    fsN t k = phiNF TM.Term.one (phiNF TM.Term.one (phiNF zero (phiNF zero
      (plus A (H k))))) := by
  show fsN (phi TM.Term.one (phi TM.Term.one (phi zero (phi zero (add A A))))) k = _
  rw [Rows.ProofsB.fsN_phi_lim rfl rfl, Rows.ProofsB.fsN_phi_lim rfl rfl,
      Rows.ProofsB.fsN_phi_lim rfl rfl, Rows.ProofsB.fsN_phi_lim rfl rfl,
      fsN_add, fsN_A k, H_iterT k]

/-- **算術。** -/
theorem arith (n : Nat) : valExpr n = fsN t (n+1) := by
  rw [fsN_t_eq (n+1)]
  show plus zero (omegaNF (Trans.Pair.phiStep TM.Term.one A
    (plus zero (omegaNF (Trans.Pair.phiStep TM.Term.one A
      (plus zero (omegaNF (plus A (H (n+1)))))))))) = _
  rw [s0 n, F3b.s1 _ (F3b.e2p _), F3b.s2 _, F3b.s3 _, F3b.s2 _,
      plusA_H n, e1p n, F3b.e2p _]
  rfl

/-- **E3。証明済み。** -/
theorem e3 : e3Claim := by
  intro n; rw [val n, arith n]

/-! ### 外部の表の値は、同じ試験を通らない -/

/-- 先方の値 ([diff.md](../../table/diff.md) 族 3 の 267 行目)。先方の構文解析器で訳した。 -/
def tHex : Term := phiNF (ofNat 1) (phiNF (ofNat 1) (phiNF zero
  (add (phiNF (ofNat 2) zero) (phiNF (ofNat 2) zero))))

#guard !(o? M == some tHex)
#guard kindT tHex == KindT.isLim
#guard (List.range 6).all fun k => (List.range 8).any fun n =>
  !(o? (BMS.expand M n) == some (fsN tHex (n + k)))
#guard (List.range 4).all fun n => (List.range 30).all fun j =>
  !(o? (BMS.expand M n) == some (fsN tHex j))
-- CTRL 同じ探索は当方の値では当たる
#guard (List.range 4).all fun n => (List.range 30).any fun j =>
  o? (BMS.expand M n) == some (fsN t j)

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

/-- **6 行の E3 を 1 か所に集めたもの。主張は行ごとに添字が違う。**
    表の E3 印は行の `proof` から引かれ、`proof` はこの節の名前空間を指す。
    名前空間を消せば印は消える (`gentable` はリンクを解決できなければ何も出さない)。 -/
theorem e3_all :
    (∀ n, o? (BMS.expand F1.M n) = some (fsN F1.t (n+1)))
  ∧ (∀ n, o? (BMS.expand F2a.M n) = some (fsN F2a.t (n+1)))
  ∧ (∀ n, o? (BMS.expand F2b.M n) = some (fsN F2b.t (n+2)))
  ∧ (∀ n, o? (BMS.expand F3a.M (n+1)) = some (fsN F3a.t (n+2)))
  ∧ (∀ n, o? (BMS.expand F3b.M n) = some (fsN F3b.t (n+1)))
  ∧ (∀ n, o? (BMS.expand F3c.M n) = some (fsN F3c.t (n+1))) :=
  ⟨F1.e3, F2a.e3, F2b.e3, F3a.e3, F3b.e3, F3c.e3⟩

/-! ## 残りの選定行が、なぜここに無いか

`o?` が届かないか、届いても撤回領域で誤った値を返す。**測定して数で固定する。** -/

def selected : List Row := rows.filter fun r => r.sel != ""
def reached : List Row := selected.filter fun r => o? r.m == some r.t

#guard selected.length == 23
#guard reached.length == 11            -- 既証明 5 + ここの 6
-- **`o?` が届く 11 行はすべて E3 を持つ。** 表の E3 印はこの `proof` から引かれる。
#guard (reached.filter fun r => r.proof == "").length == 0
-- 6 行の `proof` は、この節の名前空間をそのまま指す
#guard (rows.filter fun r => r.proof == "namespace F1").length == 1
#guard (rows.filter fun r => r.proof == "namespace F2a").length == 1
#guard (rows.filter fun r => r.proof == "namespace F2b").length == 1
#guard (rows.filter fun r => r.proof == "namespace F3a").length == 1
#guard (rows.filter fun r => r.proof == "namespace F3b").length == 1
#guard (rows.filter fun r => r.proof == "namespace F3c").length == 1
-- `o?` が値を返すのに表と違う行 (撤回領域)、と `o?` が未定義の行
#guard (selected.filter fun r => (o? r.m).isSome && !(o? r.m == some r.t)).length == 6
#guard (selected.filter fun r => (o? r.m).isNone).length == 6

/-! ### 残る 12 行の添字 — **半分は `fsN` に乗らない**

`oR` で測ると、展開が `fsN t (n+j)` に一様なずらし `j` で乗るのは **12 行中 6 行**
(ずらしは 0, 1, 1, 1, 2, 2)。残る 6 行は展開の値が `fsN t` の 0〜30 項のどこにも
現れない (2 か所の偶然を除く)。

**これは「表の値が誤り」ではない。** `Certified` の極限節は `f` に標準基本列であることを
要求しない ([✅ の実体](../../table/table-r1.md#ezero--esucc--elim---の実体))。乗らない
6 行にも閉じた形は在る — 測ると Γ₀ 行 `(0,0)(1,1)(2,1)(3,1)` は `iterGamma` を ζ₀ から
始めた鎖、族 4 の `(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)` は `φ̄(0,·)` の塔で底が `B+B`
(`B = φ̄(3,ω)`) — `fsN` が別の底から始めているだけである。`Evidence/Cert.lean` §21.1 が
rung 族で同じことを見つけている (そこでは `fsC` ではなく `fsEsucc` が正解だった)。 -/

def rest12 : List Row := selected.filter fun r => !(o? r.m == some r.t)
def hasShift (r : Row) : Bool :=
  (List.range 6).any fun j =>
    (List.range 4).all fun n => Trans.oR (BMS.expand r.m n) == some (fsN r.t (n + j))

#guard rest12.length == 12
#guard (rest12.filter hasShift).length == 6
-- 乗らない 6 行は、ずらしを 12 まで広げても 1 始まりにしても乗らない
#guard (rest12.filter fun r => !(hasShift r)).all fun r =>
  (List.range 12).all fun j => !((List.range 4).all fun n =>
    Trans.oR (BMS.expand r.m n) == some (fsN r.t (n + j)))
#guard (rest12.filter fun r => !(hasShift r)).all fun r =>
  (List.range 12).all fun j => !((List.range 4).all fun n =>
    Trans.oR (BMS.expand r.m (n+1)) == some (fsN r.t (n + j)))
-- CTRL `oR` は 12 行とも表の値を出す (値そのものは合っている)
#guard rest12.all fun r => Trans.oR r.m == some r.t

/-! ### 乗らない 6 行の `f` — 閉じた形

**測ったら 6 行とも閉じた形があった。** `fsN` が別の底・別の種から始めているだけで、
展開の値の列そのものは規則的である。以下は測定であって定理ではない (`#guard` の範囲でのみ
確かめてある) が、`Certified` の極限節に渡すべき `f` の候補はこれである。

    Γ₀ 行            `iterGamma` を ζ₀ から始めた鎖
    族 4 の 326 行目  `φ̄(0,·)` の塔、底は `B+B` (B = φ̄(3,ω))。`fsN` の底は `φ̄(1,B)+1`
    高さ 3 の 4 行    `ψ_{Z0}` の中の `φ̄(0,·)` の塔。底は `Ω+Ω` または `φ̄(1,Ω)` の 2 倍

塔の底が「2 倍」なのは 6 行のうち 4 行に共通で、これは BMS の展開が最後のブロックを
2 つ置くことの像である。**先頭の 1〜3 項は例外**で、そこは塔ではない。 -/

/-- Ω = Z0。 -/
def Om : Term := Z zero
/-- ψ_{Z0}(ZΩ)。高さ 3 の 4 行に共通で現れる。 -/
def Cps : Term := psi (Z zero) (Z TM.Term.one)
def Dph : Term := phi TM.Term.one (Z zero)
def Bph : Term := phi (ofNat 3) TM.Term.omega

def MA : BMS.Matrix := [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1]]
def MB : BMS.Matrix := [[0,0],[1,1],[2,1],[3,1]]
def MC : BMS.Matrix := [[0,0],[1,1],[2,2]]
def MD : BMS.Matrix := [[0,0],[1,1],[2,2],[1,1],[2,1],[3,1]]
def ME : BMS.Matrix := [[0,0],[1,1],[2,2],[1,1],[2,2]]
def MF : BMS.Matrix := [[0,0],[1,1],[2,2],[2,2]]

def fA : Nat → Term
  | 0 => Bph
  | n+1 => iterPhiAt zero (plus Bph Bph) (n+1)
def fB (n : Nat) : Term := iterGamma (phi (ofNat 2) zero) n
def fC : Nat → Term
  | 0 => phi TM.Term.one zero
  | 1 => phi (ofNat 2) zero
  | 2 => psi (Z zero) zero
  | n+3 => psi (Z zero) (iterPhiAt zero (plus Om Om) (n+3))
def fD : Nat → Term
  | 0 => phi (ofNat 2) Cps
  | n+1 => phi (fD n) (plus Cps TM.Term.one)
def fE : Nat → Term
  | 0 => phi TM.Term.one Cps
  | 1 => phi (ofNat 2) Cps
  | 2 => psi (Z zero) (plus (Z TM.Term.one) TM.Term.one)
  | n+3 => psi (Z zero) (plus (Z TM.Term.one) (iterPhiAt zero (plus Om Om) (n+3)))
def fF : Nat → Term
  | 0 => Cps
  | n+1 => psi (Z zero) (plus (Z TM.Term.one) (iterPhiAt zero (plus Dph Dph) (n+1)))

-- 6 つの行列は、いずれも上の 12 行の 1 つで、`oR` はその行の掲載値を出す
#guard [MA, MB, MC, MD, ME, MF].all fun m =>
  rest12.any fun r => r.m == m && Trans.oR m == some r.t
-- `fsN` に乗らない 6 行はちょうどこの 6 つ
#guard (rest12.filter fun r => !(hasShift r)).all fun r => [MA, MB, MC, MD, ME, MF].contains r.m

#guard (List.range 7).all fun n => Trans.oR (BMS.expand MA n) == some (fA n)
#guard (List.range 6).all fun n => Trans.oR (BMS.expand MB n) == some (fB n)
#guard (List.range 8).all fun n => Trans.oR (BMS.expand MC n) == some (fC n)
#guard (List.range 6).all fun n => Trans.oR (BMS.expand MD n) == some (fD n)
#guard (List.range 8).all fun n => Trans.oR (BMS.expand ME n) == some (fE n)
#guard (List.range 7).all fun n => Trans.oR (BMS.expand MF n) == some (fF n)

-- CTRL 添字を 1 ずらすとどれも壊れる (偶然の一致ではない)
#guard [(MA, fA), (MB, fB), (MC, fC), (MD, fD), (ME, fE), (MF, fF)].all fun p =>
  (List.range 5).any fun n => !(Trans.oR (BMS.expand p.1 n) == some (p.2 (n+1)))

/-! ## `oR` の行 — 最初の 1 行の梯子

`oR` の側で $`n`$ を量化した主張を証明する道は 1 本しかない。`Evidence/Cert.lean` §21.2 が
両方の迂回路を閉じ、§21.3–§21.8 が rung 族で通した道である:

    展開の族 --ofMatrix--> PS の梯子 --transPort--> BT --dict--> 値

**`++` に沿った帰納は使えない。** `runAux` の構造判定 (`fpar`・`adm`・`predP`) はリスト全体を
見るので `p ++ q` の実行の中に `p` の実行が入らず、しかもメモ表を持ち回る。使えるのは
`runAux` 自身の再帰 `predP M = M.dropLast` に沿った帰納で、そのためには**族が 1 対ずつ
伸びる**必要がある。

**測ったところ、残り 12 行のうち 5 行は展開が最初から 1 列ずつ伸びていた** — rung 族が要した
2 段の細分 (§21.4 の `L`) が要らない。ここではその中で一番短い
`(0,0)(1,1)(2,1)(3,0)` を取る。 -/

namespace G1

def MG : BMS.Matrix := [[0,0],[1,1],[2,1],[3,0]]
def tG : Term := phi TM.Term.omega zero
/-- 梯子。`(2,1)` を m 本。 -/
def LG (m : Nat) : Trans.Recal.PS := (0,0) :: (1,1) :: List.replicate m (2,1)
/-- `transPort` の像。`D 1 0` を m 本、右結合の和で並べたもの。 -/
def rep1 : Nat → Trans.Dict.BT
  | 0 => .zero
  | 1 => .D 1 .zero
  | k+1 => .sum (.D 1 .zero) (rep1 k)
def LBT (m : Nat) : Trans.Dict.BT := .D 0 (.D 1 (rep1 m))

#guard Trans.oR MG == some tG
#guard rest12.any fun r => r.m == MG && r.t == tG
#guard (rows.filter fun r => r.proof == "namespace G1").length == 1

/-- **行列の側。証明済み。** 悪い部分は 1 列 `(2,1)`、上昇なし。 -/
theorem expand_MG (n : Nat) :
    BMS.expand MG n = ([[0,0],[1,1]] : Matrix) ++ Trans.repM ([[2,1]] : Matrix) (n+1) := by
  show (BMS.expand? MG n).getD [] = _
  have h : BMS.expand? MG n
      = some (MG.take 2 ++ ((List.range (n+1)).map fun a =>
          ([[2 + a*0*1, 1 + a*0*1]] : Matrix)).flatten) := rfl
  have hf : (fun a => ([[2 + a*0*1, 1 + a*0*1]] : Matrix)) = (fun _ => ([[2,1]] : Matrix)) := by
    funext a; simp
  rw [h, hf, Trans.flat_range ([[2,1]] : Matrix) (n+1)]
  rfl

theorem all_len_rep : ∀ k,
    (Trans.repM ([[2,1]] : Matrix) k).all (fun c => decide (c.length ≤ 2)) = true
  | 0 => rfl
  | k+1 => by
    show (([[2,1]] : Matrix) ++ Trans.repM ([[2,1]] : Matrix) k).all _ = true
    rw [List.all_append, all_len_rep k]; rfl

theorem map_rep : ∀ k,
    (Trans.repM ([[2,1]] : Matrix) k).map (fun c => ((c.getD 0 0 : Int), (c.getD 1 0 : Int)))
      = List.replicate k ((2 : Int), (1 : Int))
  | 0 => rfl
  | k+1 => by
    show (([[2,1]] : Matrix) ++ Trans.repM ([[2,1]] : Matrix) k).map _ = _
    rw [List.map_append, map_rep k, List.replicate_succ]
    rfl

/-- **リンク 1。証明済み。** 読み手の一番下の段。 -/
theorem ofMatrix_MG (n : Nat) :
    Trans.Recal.ofMatrix (BMS.expand MG n) = some (LG (n+1)) := by
  rw [expand_MG n]
  unfold Trans.Recal.ofMatrix
  rw [show (([[0,0],[1,1]] : Matrix) ++ Trans.repM ([[2,1]] : Matrix) (n+1)).isEmpty
        = false from by cases n <;> rfl,
      List.all_append, all_len_rep (n+1)]
  show some ((([[0,0],[1,1]] : Matrix) ++ Trans.repM ([[2,1]] : Matrix) (n+1)).map
    (fun c => ((c.getD 0 0 : Int), (c.getD 1 0 : Int)))) = _
  rw [List.map_append, map_rep (n+1)]
  rfl

theorem dropLast_replicate : ∀ (k : Nat) (a : Int × Int),
    (List.replicate (k+1) a).dropLast = List.replicate k a
  | 0, _ => rfl
  | k+1, a => by
    rw [List.replicate_succ (n := k+1), List.dropLast_cons_of_ne_nil (by simp [List.replicate_succ]),
        dropLast_replicate k a, ← List.replicate_succ]

/-- **梯子が `runAux` の再帰に乗ること。証明済み。** これが `++` に沿えない理由への答である。 -/
theorem predP_LG (m : Nat) : Trans.Recal.predP (LG (m+1)) = LG m := by
  show (if (LG (m+1)).length == 1 then LG (m+1) else (LG (m+1)).dropLast) = _
  rw [show ((LG (m+1)).length == 1) = false from by simp [LG]]
  show ((0,0) :: (1,1) :: List.replicate (m+1) ((2 : Int), (1 : Int))).dropLast = _
  rw [List.dropLast_cons_of_ne_nil (by simp [LG]),
      List.dropLast_cons_of_ne_nil (by simp [List.replicate_succ]),
      dropLast_replicate m (2, 1)]
  rfl

/-! ### リンク 3 は証明済み。残るはリンク 2

リンク 2 は `transPort (LG m) = LBT m` (**未証明**、下の `#guard` が 8 点)。
リンク 3 は `dict (LBT m) = fsN tG (m+1)` (`dict_LBT`、**証明済み**)。

リンク 3 に要る `collapse` の法則は 2 本で、**どちらも側条件が付く**。
`collapse` は正規化器 (`wcnf`・`foldl`・`omegaNF`) なので無条件の等式は無い
(`Evidence/Cert.lean` §21.7 の教訓「正規化器が等式を満たさないときは、何と等しいかでは
なく何を保つかを聞け」):

    collapse 1 (Ω·m)      = φ̄(0, Ω·(m+1))   m ≥ 1  (m = 0 では Ω)
    collapse 0 (φ̄(0, Ω·j)) = φ̄(j, 0)         j ≥ 2  (Ω 単体では φ̄(1,0))

Ω = `Z 0` = `collapse 1 0`。側条件が要ることの対照は下の `#guard` にある。
第 2 法則の `j = 1` が外れるのは `logOm` が [Rathjen, 1991] 2.7 の不動点ずらしを踏むためで、
**この族で唯一 `phiShifted` が真になる点**である。 -/

def Omg : Term := Z zero

theorem isAP_Omg : Omg.isAP = true := rfl

theorem toList_mulOm (m : Nat) : toList (mulNat Omg m) = List.replicate m Omg :=
  Rows.ProofsB.toList_mulNat isAP_Omg m

theorem plus_zero_mulOm (m : Nat) : plus zero (mulNat Omg m) = mulNat Omg m := by
  cases m with
  | zero => rfl
  | succ k =>
    unfold plus
    rw [toList_mulOm (k+1), List.replicate_succ]
    show ofList (([] : List Term).filter _ ++ (Omg :: List.replicate k Omg)) = _
    rw [List.filter_nil, List.nil_append, ← List.replicate_succ]
    rfl

theorem plus_Om_mulOm (m : Nat) : plus Omg (mulNat Omg m) = mulNat Omg (m+1) := by
  cases m with
  | zero => rfl
  | succ k =>
    unfold plus
    rw [toList_mulOm (k+1), List.replicate_succ]
    show ofList ((toList Omg).filter (fun a => le Omg a) ++ (Omg :: List.replicate k Omg)) = _
    rw [show toList Omg = [Omg] from rfl]
    simp only [List.filter_cons, show le Omg Omg = true from rfl, List.filter_nil, if_true]
    rw [List.singleton_append, ← List.replicate_succ, ← List.replicate_succ]
    rfl

theorem splitFin_mulOm (m : Nat) : splitFin (mulNat Omg (m+2)) = (mulNat Omg (m+2), 0) := by
  show (ofList ((toList (mulNat Omg (m+2))).take
        ((toList (mulNat Omg (m+2))).length -
          ((toList (mulNat Omg (m+2))).reverse.takeWhile (fun x => x == TM.Term.one)).length)),
      ((toList (mulNat Omg (m+2))).reverse.takeWhile (fun x => x == TM.Term.one)).length) = _
  rw [toList_mulOm (m+2), List.reverse_replicate,
    show (List.replicate (m+2) Omg).takeWhile (fun x => x == TM.Term.one) = [] from by
      rw [List.replicate_succ, List.takeWhile_cons,
          show (Omg == TM.Term.one) = false from rfl]
      rfl]
  simp only [List.length_nil, Nat.sub_zero, List.length_replicate,
    show (List.replicate (m+2) Omg).take (m+2) = List.replicate (m+2) Omg from by simp]
  rfl

theorem omegaNF_mulOm (m : Nat) :
    omegaNF (mulNat Omg (m+2)) = phi zero (mulNat Omg (m+2)) := by
  have hl : toList (mulNat Omg (m+2)) = Omg :: Omg :: List.replicate m Omg := by
    rw [toList_mulOm (m+2), List.replicate_succ, List.replicate_succ]
  have hne : mulNat Omg (m+2) = add Omg (mulNat Omg (m+1)) := by
    show ofList (List.replicate (m+2) Omg) = _
    rw [List.replicate_succ]
    show add Omg (ofList (List.replicate (m+1) Omg)) = _
    rfl
  have hsp := splitFin_mulOm m
  rw [hne]
  show phiNFsucc zero (add Omg (mulNat Omg (m+1))) = _
  unfold phiNFsucc
  rw [← hne, hsp, hne]
  rfl

/-- **法則 1。** `m ≥ 1` が要る (`m = 0` では Ω)。 -/
theorem collapse_one_mulOm (k : Nat) :
    Trans.Dict.collapse 1 (mulNat Omg (k+1)) = phi zero (mulNat Omg (k+2)) := by
  have hw : Trans.Dict.wcnf (Trans.Dict.reg 2) (toList (mulNat Omg (k+1))) = ([], mulNat Omg (k+1)) := by
    rw [toList_mulOm (k+1), List.replicate_succ]
    show (if lt Omg (Trans.Dict.reg 2) then ([], ofList (Omg :: List.replicate k Omg)) else _) = _
    rw [show lt Omg (Trans.Dict.reg 2) = true from rfl]
    simp only [if_true]
    rw [← List.replicate_succ]
    rfl
  simp only [Trans.Dict.collapse, hw]
  show omegaNF (plus (Trans.Dict.reg 1) (plus zero (mulNat Omg (k+1)))) = _
  rw [plus_zero_mulOm (k+1), show Trans.Dict.reg 1 = Omg from rfl, plus_Om_mulOm (k+1), omegaNF_mulOm k]

/-! ### 法則 2 -/

theorem ltF_mulOm_Om : ∀ (f j : Nat), TM.Term.ltF f (mulNat Omg (j+2)) Omg = false
  | 0, _ => rfl
  | f+1, j => by
    rw [show mulNat Omg (j+2) = add Omg (mulNat Omg (j+1)) from by
      show ofList (List.replicate (j+2) Omg) = _
      rw [List.replicate_succ]; rfl]
    show (if ((add Omg (mulNat Omg (j+1)) : Term) == Omg) = true then false
          else TM.Term.ltF f Omg Omg) = false
    simp only [show ((add Omg (mulNat Omg (j+1)) : Term) == Omg) = false from rfl,
      Bool.false_eq_true, if_false]
    exact Rows.ProofsB.ltF_irrefl f Omg

theorem ltF_pOm_Om : ∀ (f j : Nat),
    TM.Term.ltF f (phi zero (mulNat Omg (j+2))) Omg = false
  | 0, _ => rfl
  | f+1, j => by
    show (if ((phi zero (mulNat Omg (j+2)) : Term) == Omg) = true then false
          else TM.Term.ltF f zero Omg && TM.Term.ltF f (mulNat Omg (j+2)) Omg) = false
    simp only [show ((phi zero (mulNat Omg (j+2)) : Term) == Omg) = false from rfl,
      Bool.false_eq_true, if_false, ltF_mulOm_Om f j, Bool.and_false]

theorem lt_pOm_Om (j : Nat) : lt (phi zero (mulNat Omg (j+2))) (Trans.Dict.reg 1) = false :=
  ltF_pOm_Om _ j

theorem filter_notlt_rep : ∀ (n : Nat),
    (List.replicate n Omg).filter (fun q => !lt q (Trans.Dict.reg 1)) = List.replicate n Omg
  | 0 => rfl
  | n+1 => by
    rw [List.replicate_succ, List.filter_cons,
        show (!lt Omg (Trans.Dict.reg 1)) = true from rfl, filter_notlt_rep n]
    simp [List.replicate_succ]

theorem filter_lt_rep : ∀ (n : Nat),
    (List.replicate n Omg).filter (fun q => lt q (Trans.Dict.reg 1)) = []
  | 0 => rfl
  | n+1 => by
    rw [List.replicate_succ, List.filter_cons,
        show lt Omg (Trans.Dict.reg 1) = false from rfl, filter_lt_rep n]
    simp

theorem map_rep_Trans.Dict.divAP : ∀ (n : Nat),
    (List.replicate n Omg).map (Trans.Dict.divAP (Trans.Dict.reg 1)) = List.replicate n TM.Term.one
  | 0 => rfl
  | n+1 => by
    rw [List.replicate_succ, List.map_cons, map_rep_Trans.Dict.divAP n,
        show Trans.Dict.divAP (Trans.Dict.reg 1) Omg = TM.Term.one from rfl, ← List.replicate_succ]

theorem wcnf_law2 (j : Nat) :
    Trans.Dict.wcnf (Trans.Dict.reg 1) (toList (phi zero (mulNat Omg (j+2))))
      = ([(ofNat (j+2), TM.Term.one)], zero) := by
  rw [show toList (phi zero (mulNat Omg (j+2))) = [phi zero (mulNat Omg (j+2))] from rfl, Trans.Dict.wcnf,
      lt_pOm_Om j]
  simp only [Bool.false_eq_true, if_false,
    show Trans.Dict.wcnf (Trans.Dict.reg 1) ([] : List Term) = ([], zero) from rfl,
    show Trans.Dict.logOm (phi zero (mulNat Omg (j+2))) = mulNat Omg (j+2) from by
      show (if phiShifted zero (mulNat Omg (j+2)) then _ else _) = _
      rw [show phiShifted zero (mulNat Omg (j+2)) = false from by
        show (isFP zero (splitFin (mulNat Omg (j+2))).1
          || ((mulNat Omg (j+2)) == zero && (zero : Term).isSC)) = false
        rw [splitFin_mulOm j]
        rfl]
      rfl,
    toList_mulOm (j+2)]
  rw [filter_notlt_rep (j+2), filter_lt_rep (j+2), map_rep_Trans.Dict.divAP (j+2),
    show ofList (List.replicate (j+2) TM.Term.one) = ofNat (j+2) from
      Rows.ProofsB.mulNat_one_ofNat (j+2)]
  rfl

theorem ofNat_succ_add (j : Nat) : ofNat (j+2) = add TM.Term.one (ofNat (j+1)) := by
  rw [← Rows.ProofsB.mulNat_one_ofNat (j+2), ← Rows.ProofsB.mulNat_one_ofNat (j+1)]
  show ofList (List.replicate (j+2) TM.Term.one) = _
  rw [List.replicate_succ]
  rfl

theorem ltF_Om_ofNat : ∀ (f j : Nat), TM.Term.ltF f Omg (ofNat (j+2)) = false
  | 0, _ => rfl
  | f+1, j => by
    rw [ofNat_succ_add j]
    show (if ((Omg : Term) == add TM.Term.one (ofNat (j+1))) = true then false
          else ((Omg : Term) == TM.Term.one) || TM.Term.ltF f Omg TM.Term.one) = false
    simp only [show ((Omg : Term) == add TM.Term.one (ofNat (j+1))) = false from rfl,
      Bool.false_eq_true, if_false,
      show ((Omg : Term) == TM.Term.one) = false from rfl, Bool.false_or]
    cases f with
    | zero => rfl
    | succ g =>
      show (((Omg : Term) == zero) || ((Omg : Term) == zero)
        || TM.Term.ltF g Omg zero || TM.Term.ltF g Omg zero) = false
      rw [Rows.ProofsB.ltF_lt_zero g Omg]
      rfl

theorem le_reg_ofNat (j : Nat) : le (Trans.Dict.reg (0+1)) (ofNat (j+2)) = false := by
  show ((Omg == ofNat (j+2)) || lt Omg (ofNat (j+2))) = false
  rw [show ((Omg : Term) == ofNat (j+2)) = false from by
        rw [ofNat_succ_add j]; rfl]
  simp only [Bool.false_or]
  exact ltF_Om_ofNat _ j

theorem phiNF_ofNat_zero (j : Nat) : phiNF (ofNat (j+2)) zero = phi (ofNat (j+2)) zero := by
  show phiNFsucc (ofNat (j+2)) zero = _
  unfold phiNFsucc
  rw [show splitFin (zero : Term) = (zero, 0) from rfl]
  show phiNFdefault (ofNat (j+2)) zero = _
  unfold phiNFdefault
  rw [show ((ofNat (j+2)).isSC) = false from by rw [ofNat_succ_add j]; rfl]
  rfl

/-- **法則 2。** `j ≥ 2` が要る (`Ω` 単体では φ̄(1,0))。 -/
theorem collapse_zero_pOm (j : Nat) :
    Trans.Dict.collapse 0 (phi zero (mulNat Omg (j+2))) = phi (ofNat (j+2)) zero := by
  simp only [Trans.Dict.collapse, wcnf_law2 j, List.foldl_cons, List.foldl_nil, le_reg_ofNat j,
    Bool.false_eq_true, if_false]
  show omegaNF (plus (Trans.Dict.reg 0) (plus (phiNF (ofNat (j+2)) (plus zero (Trans.Dict.sub1 TM.Term.one))) zero)) = _
  rw [show Trans.Dict.sub1 TM.Term.one = zero from rfl]
  show omegaNF (plus zero (plus (phiNF (ofNat (j+2)) zero) zero)) = _
  rw [show plus (phiNF (ofNat (j+2)) zero) zero = phiNF (ofNat (j+2)) zero from rfl,
      Rows.ProofsB.plus_zero_left (Rows.ProofsB.isAP_phiNF _ _),
      phiNF_ofNat_zero j]
  show phiNF zero (phi (ofNat (j+2)) zero) = _
  unfold phiNF
  simp only [show (phi (ofNat (j+2)) zero).isSC = false from rfl, Bool.false_and,
    Bool.false_eq_true, if_false,
    show lt zero (ofNat (j+2)) = true from by rw [ofNat_succ_add j]; rfl, if_true]

/-- `rep1` の像は Ω の m 倍。 -/
theorem dict_rep1 : ∀ m, Trans.Dict.dict (rep1 m) = mulNat Omg m
  | 0 => rfl
  | 1 => rfl
  | k+2 => by
    show plus (Trans.Dict.dict (Trans.Dict.BT.D 1 .zero)) (Trans.Dict.dict (rep1 (k+1))) = _
    rw [dict_rep1 (k+1), show Trans.Dict.dict (Trans.Dict.BT.D 1 .zero) = Omg from rfl,
        plus_Om_mulOm (k+1)]

/-- **項の側。** `t = φ̄(ω,0)` の基本列は `φ̄(k,0)`。 -/
theorem fsN_tG (k : Nat) : fsN tG k = phiNF (ofNat k) zero := by
  show fsN (phi TM.Term.omega zero) k = _
  rw [fsN]
  show phiNF (fsN TM.Term.omega k) zero = _
  rw [F2a.fsN_omega k]

/-- **リンク 3。証明済み。** 2 つの `collapse` 法則を継ぐ。 -/
theorem dict_LBT : ∀ m, Trans.Dict.dict (LBT m) = fsN tG (m+1)
  | 0 => by rw [fsN_tG (0+1)]; rfl
  | k+1 => by
    show Trans.Dict.collapse 0 (Trans.Dict.collapse 1 (Trans.Dict.dict (rep1 (k+1)))) = _
    rw [dict_rep1 (k+1), collapse_one_mulOm k, collapse_zero_pOm k, fsN_tG (k+2),
        phiNF_ofNat_zero k]

/-! ### リンク 2 の中身 — 測定。梯子の上では `runAux` が一様

`runAux` の分岐を梯子の上で決めた (`Evidence/Cert.lean` §21.4 と同じ作業)。**m ≥ 1 では
毎段が同じ型 3** で、可変部分が無い:

    isZeroP = false   isPrincipalP = true   isReducedP = true
    trMax = 1   j1 = m+1   j0 = 1   adm j0 = 1   isAdm = true
    gp1 j0 = gp1 j1 = 1  ⟹  transTypeMain = 3

`Mark` の側も閉じた: `markP (LG m) 1 = D 1 (rep1 m)`、つまり `LBT m` から外側の `D 0` を
外したものである。型 3 の一段は

    c1 = D 1 (rep1 (m-1))  ⟹  c2 = D 1 (rep1 m)  ⟹  replMark で t1 の中を差し替え

で `LBT (m-1)` から `LBT m` へ進む。**`transPort` と `markP` の同時帰納**になる。

`redP (LG m) = LG m` (`red` の主枝) も測った。**畳み込みの各段が完全に同じ**である:

    brF = [(2,1)] が m 本   firstNodes = [2,3,…,m+2]   joints = 1 が m 本
    各段: nJ = 0, jnJ = 1, NJ = [(2,1)], red NJ = [(1,1)], incrFirst … 1 = [(2,1)]

つまり `foldl` は `[(0,0),(1,1)]` に `(2,1)` を m 回足すだけで、`LG m` に戻る。

**次の一手は `red` の燃料非依存性** — `red f NJ = [(1,1)]` を記号的な `f` について言うには、
`Evidence/StageB.lean` の `oLAux_fuel` にあたる補題 (十分な燃料の上で `red` が燃料に依らない)
が要る。`Trans/Recal.lean` にはまだ無い。 -/

def markP (M : Trans.Recal.PS) (j : Int) : Trans.Dict.BT :=
  (Trans.Recal.runAux (Trans.Recal.transFuel M) M (some j)).run' []

#guard (List.range 7).all fun m => markP (LG m) 1 == .D 1 (rep1 m)
#guard (List.range 8).all fun m => Trans.Recal.redP (LG m) == LG m
#guard (List.range 8).all fun m =>
  !(Trans.Recal.isZeroP (LG m)) && Trans.Recal.isPrincipalP (LG m)
    && Trans.Recal.isReducedP (LG m)
#guard (List.range 7).all fun m =>
  let M := LG (m+1); let j1 := Trans.Recal.lenI M - 1
  let j0 := Trans.Recal.fpar M 0 j1 0
  Trans.Recal.trMax M == 1 && j0 == 1 && Trans.Recal.adm M j0 == 1
    && Trans.Recal.transTypeMain M j0 j1 == 3
-- CTRL m = 0 だけは型 6 (j0 = 0、gp1 j0 = 0)
#guard Trans.Recal.transTypeMain (LG 0) 0 1 == 6

/-! #### `red` の燃料非依存性 — 内側の 2 入力について証明済み

`red` は燃料つきなので、記号的な `m` の上で `redP` を動かすには「十分な燃料の上では
燃料に依らない」が要る。**一般形は要らない。** 梯子の主枝が呼ぶ入力は 2 つだけで、
どちらも固定の行列である。

    X2 = (0,0)(3,1)   主枝の `j1p == j1` に落ちるので**再帰が無い** → 燃料 1 で止まる
    X1 = (2,1)        X2 を 1 回呼ぶだけ → 燃料 2 で止まる -/

def X1 : Trans.Recal.PS := [(2,1)]
def X2 : Trans.Recal.PS := [(0,0),(3,1)]

/-- **証明済み。** 再帰が無いので `rfl`。 -/
theorem red_X2 (f : Nat) : Trans.Recal.red (f+1) X2 = [(0,0),(1,1)] := rfl

/-- **証明済み。** -/
theorem red_X1 (f : Nat) : Trans.Recal.red (f+2) X1 = [(1,1)] := by
  show (if Trans.Recal.isZeroP X1 then Trans.Recal.zeroPS
        else if Trans.Recal.isPrincipalP X1 then
          (if Trans.Recal.gp0 X1 0 == 0 && Trans.Recal.gp1 X1 0 == 0 then _
           else
            (if Trans.Recal.gp1 X1 0 == 0 then
              Trans.Recal.red (f+1) (Trans.Recal.incrFirst X1 (-(Trans.Recal.gp0 X1 0)))
             else
              let N := Trans.Recal.red (f+1)
                (Trans.Recal.jjSeq 0 (Trans.Recal.gp1 X1 0 - 1)
                  ++ Trans.Recal.incrFirst X1 (Trans.Recal.gp1 X1 0))
              let jN : Int := Trans.Recal.lenI N - 1
              if decide (Trans.Recal.gp1 X1 0 ≤ jN)
                  && Trans.Recal.isPrincipalP (N.drop (Trans.Recal.gp1 X1 0).toNat) then
                Trans.Recal.incrFirst (N.drop (Trans.Recal.gp1 X1 0).toNat)
                  (-(Trans.Recal.gp0 N (Trans.Recal.gp1 X1 0))
                    + Trans.Recal.gp1 N (Trans.Recal.gp1 X1 0))
              else X1))
        else (Trans.Recal.ppair X1).flatMap (Trans.Recal.red (f+1))) = _
  rw [show (Trans.Recal.jjSeq 0 (Trans.Recal.gp1 X1 0 - 1)
        ++ Trans.Recal.incrFirst X1 (Trans.Recal.gp1 X1 0)) = X2 from rfl, red_X2 f]
  rfl

theorem maxE_rep : ∀ (m a : Nat), 2 ≤ a →
    (List.replicate m ((2 : Int), (1 : Int))).foldl
      (fun b c => Nat.max b (Nat.max c.1.toNat c.2.toNat)) a = a
  | 0, _, _ => rfl
  | m+1, a, h => by
    rw [List.replicate_succ, List.foldl_cons]
    show (List.replicate m ((2 : Int), (1 : Int))).foldl _ (Nat.max a 2) = a
    rw [show Nat.max a 2 = a from Nat.max_eq_left h, maxE_rep m a h]

/-- **証明済み。** 梯子の燃料は `redFuel (LG (m+1)) = 4m + 60`。 -/
theorem maxE_LG (m : Nat) : Trans.Recal.maxE (LG (m+1)) = 2 := by
  show (((0,0) :: (1,1) :: List.replicate (m+1) ((2 : Int), (1 : Int))).foldl
    (fun b c => Nat.max b (Nat.max c.1.toNat c.2.toNat)) 0) = 2
  rw [List.foldl_cons, List.foldl_cons, List.replicate_succ, List.foldl_cons]
  show (List.replicate m ((2 : Int), (1 : Int))).foldl _ 2 = 2
  exact maxE_rep m 2 (by omega)

/-! #### 残るのは主枝の畳み込み。材料は測ってある

    ppair (replicate m (2,1)) = replicate m [(2,1)]
    brF (LG (m+1))            = replicate (m+1) [(2,1)]
    joints (LG (m+1))         = replicate (m+1) 1
    firstNodes (LG (m+1))     = [2, 3, …, m+3]
    各段の nJ                  = 0        (`fpar M 1 (fn J) 0`)

各段は `r ↦ r ++ incrFirst (red f [(2,1)]) 1 = r ++ [(2,1)]` で**完全に同じ**なので、
畳み込みは `[(0,0),(1,1)]` に `(2,1)` を m+1 回足すだけ。**次に要るのは `ppair` の
閉じた形**で、`ppair` も燃料つきなので `ppairAux` の燃料非依存性から始まる。 -/

/-! #### `ppair` の閉じた形。証明済み

複製列は**各列が自分のブロック**になる。行 0 が全部 2 なので `fpar0Aux` が親を見つけられず
`-1` を返し、`fAnc` が 1 点集合になるからである。`ppairAux` の燃料は列数 +1 で足りる。 -/

abbrev CC : Int × Int := (2, 1)
abbrev RR (m : Nat) : Trans.Recal.PS := List.replicate m CC

theorem getD_rep : ∀ (m i : Nat), i < m → (RR m).getD i (0,0) = CC
  | 0, _, h => absurd h (by omega)
  | m+1, 0, _ => by
    show (List.replicate (m+1) CC).getD 0 (0,0) = CC
    rw [List.replicate_succ]; rfl
  | m+1, i+1, h => by
    show (List.replicate (m+1) CC).getD (i+1) (0,0) = CC
    rw [List.replicate_succ]
    show (RR m).getD i (0,0) = CC
    exact getD_rep m i (by omega)

theorem gp0_rep (m : Nat) (j : Int) (h0 : 0 ≤ j) (h1 : j < (m : Int)) : Trans.Recal.gp0 (RR m) j = 2 := by
  show (if j < 0 then 0 else ((RR m).getD j.toNat (0,0)).1) = 2
  rw [if_neg (by omega), getD_rep m j.toNat (by omega)]

theorem fpar0Aux_rep : ∀ (f m : Nat) (j0 : Int), j0 < (m : Int) →
    Trans.Recal.fpar0Aux f (RR m) 2 j0 0 = -1
  | 0, _, _, _ => rfl
  | f+1, m, j0, h => by
    show (if j0 < 0 then -1 else if Trans.Recal.gp0 (RR m) j0 < 2 then j0
          else Trans.Recal.fpar0Aux f (RR m) 2 (j0 - 1) 0) = -1
    by_cases hneg : j0 < 0
    · rw [if_pos hneg]
    · rw [if_neg hneg, gp0_rep m j0 (by omega) h, if_neg (by omega),
          fpar0Aux_rep f m (j0 - 1) (by omega)]

theorem fpar_rep (m : Nat) (j : Int) (h0 : 0 ≤ j) (h1 : j < (m : Int)) :
    Trans.Recal.fpar (RR m) 0 j 0 = -1 := by
  show (if j < 0 ∨ j ≥ Trans.Recal.lenI (RR m) then -1
        else if (0 : Nat) == 0 then Trans.Recal.fpar0Aux ((RR m).length + 1) (RR m) (Trans.Recal.gp0 (RR m) j) (j - 1) 0
        else Trans.Recal.fpar1Aux ((RR m).length + 1) (RR m) (Trans.Recal.gp1 (RR m) j) j 0) = -1
  rw [if_neg (by
    show ¬(j < 0 ∨ j ≥ ((RR m).length : Int))
    rw [List.length_replicate]
    omega)]
  simp only [show ((0 : Nat) == 0) = true from rfl, if_true]
  rw [gp0_rep m j h0 h1]
  exact fpar0Aux_rep _ m (j - 1) (by omega)

theorem fAnc_rep (m : Nat) (j : Int) (h0 : 0 ≤ j) (h1 : j < (m : Int)) :
    Trans.Recal.fAnc (RR m) 0 j 0 = [j] := by
  show (if j < 0 ∨ j ≥ Trans.Recal.lenI (RR m) then [] else Trans.Recal.fAncAux ((RR m).length + 1) (RR m) 0 j 0 [j]) = _
  rw [if_neg (by
    show ¬(j < 0 ∨ j ≥ ((RR m).length : Int))
    rw [List.length_replicate]
    omega)]
  cases hf : (RR m).length + 1 with
  | zero => omega
  | succ g =>
    show (let j1 := Trans.Recal.fpar (RR m) 0 j 0
          if j1 ≥ 0 then Trans.Recal.fAncAux g (RR m) 0 j1 0 ([j] ++ [j1]) else [j]) = _
    rw [fpar_rep m j h0 h1]
    rfl

theorem ppairAux_rep : ∀ (f m k : Nat), k ≤ m → k ≤ f → ∀ (acc : List Trans.Recal.PS),
    Trans.Recal.ppairAux f (RR m) ((k : Int) - 1) acc = List.replicate k [CC] ++ acc
  | 0, _, 0, _, _, acc => rfl
  | f+1, m, 0, _, _, acc => by
    show (if ((0 : Int) - 1) < 0 then acc else _) = _
    rw [if_pos (by omega)]
    simp
  | f+1, m, k+1, hkm, hkf, acc => by
    show (if ((k+1 : Int) - 1) < 0 then acc
          else
            let ans := Trans.Recal.fAnc (RR m) 0 ((k+1 : Int) - 1) 0
            let j0 := (ans.getLast?).getD 0
            Trans.Recal.ppairAux f (RR m) (j0 - 1) (Trans.Recal.slice (RR m) j0 (((k+1 : Int) - 1) + 1) :: acc)) = _
    rw [if_neg (by omega)]
    simp only [show ((k : Int) + 1 - 1) = (k : Int) from by omega]
    show Trans.Recal.ppairAux f (RR m) (((Trans.Recal.fAnc (RR m) 0 ((k : Int)) 0).getLast?).getD 0 - 1)
      (Trans.Recal.slice (RR m) (((Trans.Recal.fAnc (RR m) 0 ((k : Int)) 0).getLast?).getD 0) ((k : Int) + 1) :: acc) = _
    rw [fAnc_rep m (k : Int) (by omega) (by omega)]
    show Trans.Recal.ppairAux f (RR m) ((k : Int) - 1) (Trans.Recal.slice (RR m) (k : Int) ((k : Int) + 1) :: acc) = _
    rw [show Trans.Recal.slice (RR m) (k : Int) ((k : Int) + 1) = [CC] from by
      show ((RR m).drop k).take (((k : Int) + 1 - k).toNat) = _
      rw [show (((k : Int) + 1 - (k : Int)).toNat) = 1 from by omega,
          List.drop_replicate]
      cases hm : m - k with
      | zero => omega
      | succ p => rw [List.replicate_succ]; rfl,
      ppairAux_rep f m k (by omega) (by omega)]
    rw [List.replicate_succ']
    simp

theorem ppair_rep (m : Nat) : Trans.Recal.ppair (RR m) = List.replicate m [CC] := by
  show Trans.Recal.ppairAux ((RR m).length + 1) (RR m) (Trans.Recal.lenI (RR m) - 1) [] = _
  rw [show Trans.Recal.lenI (RR m) = (m : Int) from by
        show (((RR m).length : Nat) : Int) = _
        rw [List.length_replicate],
      ppairAux_rep ((RR m).length + 1) m m (by omega) (by rw [List.length_replicate]; omega) []]
  simp

#guard (List.range 6).all fun m => Trans.Recal.ppair (RR m) == List.replicate m [CC]
/-! #### 梯子の上の親関数と `trMax`。証明済み

`trMax (LG m) = 1` は、`(1,1)` が `(0,0)` の行 1 の親で、`(2,1)` はそうでない、という 2 段の
判定である。そこから `brF` がブロック分解に落ちる。 -/

theorem len_LG (m : Nat) : (LG m).length = m + 2 := by
  show ((0,0) :: (1,1) :: List.replicate m CC).length = _
  simp

theorem lenI_LG (m : Nat) : Trans.Recal.lenI (LG m) = (m : Int) + 2 := by
  show (((LG m).length : Nat) : Int) = _
  rw [len_LG m]; omega

theorem gp0_LG0 (m : Nat) : Trans.Recal.gp0 (LG m) 0 = 0 := rfl
theorem gp1_LG0 (m : Nat) : Trans.Recal.gp1 (LG m) 0 = 0 := rfl
theorem gp0_LG1 (m : Nat) : Trans.Recal.gp0 (LG m) 1 = 1 := rfl
theorem gp1_LG1 (m : Nat) : Trans.Recal.gp1 (LG m) 1 = 1 := rfl

theorem gp0_LG (m : Nat) (j : Int) (h0 : 2 ≤ j) (h1 : j < (m : Int) + 2) :
    Trans.Recal.gp0 (LG m) j = 2 := by
  show (if j < 0 then 0 else ((LG m).getD j.toNat (0,0)).1) = 2
  rw [if_neg (by omega)]
  have : (LG m).getD j.toNat (0,0) = (RR m).getD (j.toNat - 2) (0,0) := by
    obtain ⟨k, hk⟩ : ∃ k : Nat, j.toNat = k + 2 := ⟨j.toNat - 2, by omega⟩
    rw [hk]
    show ((0,0) :: (1,1) :: RR m).getD (k+2) (0,0) = _
    simp [hk]
  rw [this, getD_rep m (j.toNat - 2) (by omega)]

theorem gp1_LG (m : Nat) (j : Int) (h0 : 2 ≤ j) (h1 : j < (m : Int) + 2) :
    Trans.Recal.gp1 (LG m) j = 1 := by
  show (if j < 0 then 0 else ((LG m).getD j.toNat (0,0)).2) = 1
  rw [if_neg (by omega)]
  have : (LG m).getD j.toNat (0,0) = (RR m).getD (j.toNat - 2) (0,0) := by
    obtain ⟨k, hk⟩ : ∃ k : Nat, j.toNat = k + 2 := ⟨j.toNat - 2, by omega⟩
    rw [hk]
    show ((0,0) :: (1,1) :: RR m).getD (k+2) (0,0) = _
    simp [hk]
  rw [this, getD_rep m (j.toNat - 2) (by omega)]

/-! ### 親関数を梯子の上で決める -/

theorem fpar0_LG_1 (m : Nat) : Trans.Recal.fpar0 (LG m) 1 0 = 0 := by
  show (if (1 : Int) < 0 ∨ (1 : Int) ≥ Trans.Recal.lenI (LG m) then -1
        else Trans.Recal.fpar0Aux ((LG m).length + 1) (LG m) (Trans.Recal.gp0 (LG m) 1) 0 0) = 0
  rw [if_neg (by rw [lenI_LG m]; omega), gp0_LG1 m, len_LG m]
  show (if (0 : Int) < 0 then -1 else if Trans.Recal.gp0 (LG m) 0 < 1 then 0
        else Trans.Recal.fpar0Aux (m+2) (LG m) 1 (-1) 0) = 0
  rw [if_neg (by omega), gp0_LG0 m, if_pos (by omega)]

theorem fpar0_LG_2 (m : Nat) (hm : 1 ≤ m) : Trans.Recal.fpar0 (LG m) 2 1 = 1 := by
  show (if (2 : Int) < 0 ∨ (2 : Int) ≥ Trans.Recal.lenI (LG m) then -1
        else Trans.Recal.fpar0Aux ((LG m).length + 1) (LG m) (Trans.Recal.gp0 (LG m) 2) 1 1) = 1
  rw [if_neg (by rw [lenI_LG m]; omega), gp0_LG m 2 (by omega) (by omega), len_LG m]
  show (if (1 : Int) < 1 then -1 else if Trans.Recal.gp0 (LG m) 1 < 2 then 1
        else Trans.Recal.fpar0Aux (m+2) (LG m) 2 0 1) = 1
  rw [if_neg (by omega), gp0_LG1 m, if_pos (by omega)]

theorem fpar0_LG_3 (m : Nat) : Trans.Recal.fpar0 (LG m) 1 1 = -1 := by
  show (if (1 : Int) < 0 ∨ (1 : Int) ≥ Trans.Recal.lenI (LG m) then -1
        else Trans.Recal.fpar0Aux ((LG m).length + 1) (LG m) (Trans.Recal.gp0 (LG m) 1) 0 1) = -1
  rw [if_neg (by rw [lenI_LG m]; omega), gp0_LG1 m, len_LG m]
  show (if (0 : Int) < 1 then -1 else _) = -1
  rw [if_pos (by omega)]

theorem fpar_LG_1_1 (m : Nat) : Trans.Recal.fpar (LG m) 1 1 0 = 0 := by
  show (if (1 : Int) < 0 ∨ (1 : Int) ≥ Trans.Recal.lenI (LG m) then -1
        else if (1 : Nat) == 0 then Trans.Recal.fpar0Aux ((LG m).length + 1) (LG m) (Trans.Recal.gp0 (LG m) 1) 0 0
        else Trans.Recal.fpar1Aux ((LG m).length + 1) (LG m) (Trans.Recal.gp1 (LG m) 1) 1 0) = 0
  rw [if_neg (by rw [lenI_LG m]; omega)]
  simp only [show ((1 : Nat) == 0) = false from rfl, Bool.false_eq_true, if_false]
  rw [gp1_LG1 m, len_LG m]
  show (let j1 := Trans.Recal.fpar0 (LG m) 1 0
        if j1 < 0 then -1 else if Trans.Recal.gp1 (LG m) j1 < 1 then j1
        else Trans.Recal.fpar1Aux (m+1) (LG m) 1 j1 0) = 0
  rw [fpar0_LG_1 m]
  show (if (0 : Int) < 0 then -1 else if Trans.Recal.gp1 (LG m) 0 < 1 then 0 else _) = 0
  rw [if_neg (by omega), gp1_LG0 m, if_pos (by omega)]

theorem fpar_LG_1_2 (m : Nat) (hm : 1 ≤ m) : Trans.Recal.fpar (LG m) 1 2 1 = -1 := by
  show (if (2 : Int) < 0 ∨ (2 : Int) ≥ Trans.Recal.lenI (LG m) then -1
        else if (1 : Nat) == 0 then Trans.Recal.fpar0Aux ((LG m).length + 1) (LG m) (Trans.Recal.gp0 (LG m) 2) 1 1
        else Trans.Recal.fpar1Aux ((LG m).length + 1) (LG m) (Trans.Recal.gp1 (LG m) 2) 2 1) = -1
  rw [if_neg (by rw [lenI_LG m]; omega)]
  simp only [show ((1 : Nat) == 0) = false from rfl, Bool.false_eq_true, if_false]
  rw [gp1_LG m 2 (by omega) (by omega), len_LG m]
  show (let j1 := Trans.Recal.fpar0 (LG m) 2 1
        if j1 < 1 then -1 else if Trans.Recal.gp1 (LG m) j1 < 1 then j1
        else Trans.Recal.fpar1Aux (m+2) (LG m) 1 j1 1) = -1
  rw [fpar0_LG_2 m hm]
  show (if (1 : Int) < 1 then -1 else if Trans.Recal.gp1 (LG m) 1 < 1 then 1
        else Trans.Recal.fpar1Aux (m+2) (LG m) 1 1 1) = -1
  rw [if_neg (by omega), gp1_LG1 m, if_neg (by omega)]
  cases m with
  | zero => omega
  | succ p =>
    show (let j1 := Trans.Recal.fpar0 (LG (p+1)) 1 1
          if j1 < 1 then -1
          else if Trans.Recal.gp1 (LG (p+1)) j1 < 1 then j1
          else Trans.Recal.fpar1Aux (p+2) (LG (p+1)) 1 j1 1) = -1
    rw [fpar0_LG_3 (p+1), if_pos (by omega)]

theorem isParentP_LG_1 (m : Nat) : Trans.Recal.isParentP (LG m) 1 1 0 = true := by
  show (decide ((0:Int) ≤ 0) && decide ((0:Int) < Trans.Recal.lenI (LG m))
    && ((0 : Int) == Trans.Recal.fpar (LG m) 1 1 0)) = true
  rw [fpar_LG_1_1 m, lenI_LG m,
      show (decide ((0:Int) < (m : Int) + 2)) = true from decide_eq_true (by omega)]
  rfl

theorem isParentP_LG_2 (m : Nat) : Trans.Recal.isParentP (LG m) 1 2 1 = false := by
  show (decide ((1:Int) ≤ 1) && decide ((1:Int) < Trans.Recal.lenI (LG m))
    && ((1 : Int) == Trans.Recal.fpar (LG m) 1 2 1)) = false
  rw [show Trans.Recal.fpar (LG m) 1 2 1 = -1 from by
        cases m with
        | zero => rfl
        | succ p => exact fpar_LG_1_2 (p+1) (by omega),
      show ((1 : Int) == (-1 : Int)) = false from rfl, Bool.and_false]

/-- **証明済み。** 梯子の `Trans.Recal.trMax` は常に 1。 -/
theorem trMax_LG (m : Nat) : Trans.Recal.trMax (LG m) = 1 := by
  show Trans.Recal.trMaxAux ((LG m).length + 1) (LG m) 0 = 1
  rw [len_LG m]
  show (if (0 : Int) ≥ Trans.Recal.lenI (LG m) then Trans.Recal.lenI (LG m) - 1
        else if !(Trans.Recal.isParentP (LG m) 1 1 0) then 0
        else Trans.Recal.trMaxAux (m+2) (LG m) 1) = 1
  rw [if_neg (by rw [lenI_LG m]; omega),
      isParentP_LG_1 m]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  show (if (1 : Int) ≥ Trans.Recal.lenI (LG m) then Trans.Recal.lenI (LG m) - 1
        else if !(Trans.Recal.isParentP (LG m) 1 2 1) then 1
        else Trans.Recal.trMaxAux (m+1) (LG m) 2) = 1
  rw [if_neg (by rw [lenI_LG m]; omega),
      isParentP_LG_2 m]
  simp

/-- **証明済み。** 梯子のブロック分解は 1 列ずつ。 -/
theorem brF_LG (m : Nat) : Trans.Recal.brF (LG m) = List.replicate m [CC] := by
  show Trans.Recal.ppair ((LG m).drop (Trans.Recal.trMax (LG m) + 1).toNat) = _
  rw [trMax_LG m]
  show Trans.Recal.ppair ((LG m).drop 2) = _
  rw [show (LG m).drop 2 = RR m from rfl]
  exact ppair_rep m

#guard (List.range 6).all fun m => Trans.Recal.brF (LG (m+1)) == List.replicate (m+1) X1

/-! #### `firstNodes` と `joints`。証明済み

`idxSum` はブロック長の累積和なので、長さ 1 のブロックが m 本なら `0,1,…,m`。
`joints` はその先頭 m 個を行 0 の親に送るが、**2 以上の位置の親は常に 1** — 行 0 が
`0,1,2,2,…` なので、降りていって最初に 2 未満になるのが位置 1 だからである。 -/

theorem idxSum_step : ∀ (m : Nat) (l : List Int) (c : Int),
    (List.replicate m [CC]).foldl
      (fun (a : List Int × Int) q => (a.1 ++ [a.2 + (q.length : Int)], a.2 + (q.length : Int)))
      (l, c) = (l ++ (List.range m).map (fun (k : Nat) => c + 1 + (k : Int)), c + (m : Int))
  | 0, l, c => by simp
  | m+1, l, c => by
    rw [List.replicate_succ, List.foldl_cons]
    show (List.replicate m [CC]).foldl _ (l ++ [c + 1], c + 1) = _
    rw [idxSum_step m (l ++ [c + 1]) (c + 1)]
    have h : (List.range (m+1)).map (fun (k : Nat) => c + 1 + (k : Int))
        = [c + 1] ++ (List.range m).map (fun (k : Nat) => c + 1 + 1 + (k : Int)) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [List.singleton_append, List.cons.injEq]
      constructor
      · omega
      · apply List.map_congr_left
        intro k _
        show c + 1 + ((k+1 : Nat) : Int) = c + 1 + 1 + (k : Int)
        push_cast
        omega
    rw [h, ← List.append_assoc]
    congr 1
    omega

theorem idxSum_rep (m : Nat) :
    Trans.Recal.idxSum (List.replicate m [CC]) = (List.range (m+1)).map (fun (k : Nat) => (k : Int)) := by
  show ((List.replicate m [CC]).foldl _ ([0], 0)).1 = _
  rw [idxSum_step m [0] 0]
  show ([0] ++ (List.range m).map (fun (k : Nat) => (0 : Int) + 1 + (k : Int))) = _
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [List.singleton_append, List.cons.injEq]
  refine ⟨rfl, ?_⟩
  apply List.map_congr_left
  intro k _
  show (0 : Int) + 1 + (k : Int) = ((k+1 : Nat) : Int)
  push_cast; omega

theorem firstNodes_LG (m : Nat) :
    Trans.Recal.firstNodes (LG m) = (List.range (m+1)).map (fun (k : Nat) => (k : Int) + 2) := by
  show ((Trans.Recal.idxSum (Trans.Recal.brF (LG m))).map (fun e => Trans.Recal.trMax (LG m) + 1 + e)) = _
  rw [brF_LG m, trMax_LG m, idxSum_rep m, List.map_map]
  apply List.map_congr_left
  intro k _
  show (1 : Int) + 1 + (k : Int) = (k : Int) + 2
  omega

/-- 行 0 の親は、2 以上の位置では常に 1。 -/
theorem fpar0Aux_LG_to1 : ∀ (f : Nat) (m : Nat) (j0 : Int), 1 ≤ j0 → j0 < (m : Int) + 2 →
    j0 ≤ (f : Int) → Trans.Recal.fpar0Aux f (LG m) 2 j0 0 = 1
  | 0, _, _, h0, _, hf => by exfalso; simp at hf; omega
  | f+1, m, j0, h0, h1, hf => by
    show (if j0 < 0 then -1 else if Trans.Recal.gp0 (LG m) j0 < 2 then j0
          else Trans.Recal.fpar0Aux f (LG m) 2 (j0 - 1) 0) = 1
    rw [if_neg (by omega)]
    by_cases he : j0 = 1
    · subst he; rw [gp0_LG1 m, if_pos (by omega)]
    · rw [gp0_LG m j0 (by omega) (by omega), if_neg (by omega)]
      refine fpar0Aux_LG_to1 f m (j0 - 1) (by omega) (by omega) ?_
      push_cast at hf ⊢
      omega

theorem fpar_LG_0_e (m : Nat) (e : Int) (h0 : 2 ≤ e) (h1 : e < (m : Int) + 2) :
    Trans.Recal.fpar (LG m) 0 e 0 = 1 := by
  show (if e < 0 ∨ e ≥ Trans.Recal.lenI (LG m) then -1
        else if (0 : Nat) == 0 then Trans.Recal.fpar0Aux ((LG m).length + 1) (LG m) (Trans.Recal.gp0 (LG m) e) (e - 1) 0
        else Trans.Recal.fpar1Aux ((LG m).length + 1) (LG m) (Trans.Recal.gp1 (LG m) e) e 0) = 1
  rw [if_neg (by rw [lenI_LG m]; omega)]
  simp only [show ((0 : Nat) == 0) = true from rfl, if_true]
  rw [gp0_LG m e h0 h1, len_LG m]
  refine fpar0Aux_LG_to1 (m+3) m (e-1) (by omega) (by omega) ?_
  push_cast
  omega

theorem map_const_range (m : Nat) (a : Int) :
    (List.range m).map (fun _ => a) = List.replicate m a := by
  induction m with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.map_append, ih, List.replicate_succ']; rfl

theorem joints_LG (m : Nat) : Trans.Recal.joints (LG m) = List.replicate m 1 := by
  show ((Trans.Recal.firstNodes (LG m)).dropLast.map (fun e => Trans.Recal.fpar (LG m) 0 e 0)) = _
  rw [firstNodes_LG m, List.range_succ, List.map_append]
  show (((List.range m).map (fun (k : Nat) => (k : Int) + 2) ++ [(m : Int) + 2]).dropLast.map _) = _
  rw [List.dropLast_concat]
  rw [show ((List.range m).map (fun (k : Nat) => (k : Int) + 2)).map (fun e => Trans.Recal.fpar (LG m) 0 e 0)
        = (List.range m).map (fun (_ : Nat) => (1 : Int)) from by
      rw [List.map_map]
      apply List.map_congr_left
      intro k hk
      show Trans.Recal.fpar (LG m) 0 ((k : Int) + 2) 0 = 1
      refine fpar_LG_0_e m ((k : Int) + 2) (by omega) ?_
      have := List.mem_range.mp hk
      push_cast
      omega]
  exact map_const_range m 1

#guard (List.range 6).all fun m =>
  Trans.Recal.firstNodes (LG m) == (List.range (m+1)).map (fun (k : Nat) => (k : Int) + 2)
#guard (List.range 6).all fun m => Trans.Recal.joints (LG m) == List.replicate m (1 : Int)

/-! #### `redP (LG m) = LG m`。証明済み — リンク 2 の第 1 分岐が閉じた

主枝の畳み込みは**各段が完全に同じ**である。ブロックは `[(2,1)]`、joint は 1、
行 1 の親は 0 なので `NJ = [(2,1)]` が毎回同じで、`red` がそれを `[(1,1)]` に潰し、
`incrFirst … 1` が `(2,1)` に戻す。よって畳み込みは `(0,0)(1,1)` に `(2,1)` を
m 回足すだけになる。

これで `runAux` の最初の分岐 `!(isReducedP M)` が偽と決まり、記号的な `m` の上で
`transPort` の再帰に入れるようになった。 -/

theorem getD_repl {α : Type} : ∀ (m i : Nat) (a d : α), i < m → (List.replicate m a).getD i d = a
  | 0, _, _, _, h => absurd h (by omega)
  | m+1, 0, a, d, _ => by rw [List.replicate_succ]; rfl
  | m+1, i+1, a, d, h => by
    rw [List.replicate_succ]
    show (List.replicate m a).getD i d = a
    exact getD_repl m i a d (by omega)

theorem getD_map_range (m J : Nat) (f : Nat → Int) (h : J < m) :
    ((List.range m).map f).getD J 0 = f J := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

/-- 行 1 の親は、2 以上の位置では常に 0。 -/
theorem fpar_LG_1_e (m : Nat) (e : Int) (h0 : 2 ≤ e) (h1 : e < (m : Int) + 2) :
    Trans.Recal.fpar (LG m) 1 e 0 = 0 := by
  show (if e < 0 ∨ e ≥ Trans.Recal.lenI (LG m) then -1
        else if (1 : Nat) == 0 then Trans.Recal.fpar0Aux ((LG m).length + 1) (LG m) (Trans.Recal.gp0 (LG m) e) (e - 1) 0
        else Trans.Recal.fpar1Aux ((LG m).length + 1) (LG m) (Trans.Recal.gp1 (LG m) e) e 0) = 0
  rw [if_neg (by rw [lenI_LG m]; omega)]
  simp only [show ((1 : Nat) == 0) = false from rfl, Bool.false_eq_true, if_false]
  rw [gp1_LG m e h0 h1, len_LG m]
  show (let j1 := Trans.Recal.fpar0 (LG m) e 0
        if j1 < 0 then -1 else if Trans.Recal.gp1 (LG m) j1 < 1 then j1
        else Trans.Recal.fpar1Aux (m+2) (LG m) 1 j1 0) = 0
  rw [show Trans.Recal.fpar0 (LG m) e 0 = 1 from by
    show (if e < 0 ∨ e ≥ Trans.Recal.lenI (LG m) then -1
          else Trans.Recal.fpar0Aux ((LG m).length + 1) (LG m) (Trans.Recal.gp0 (LG m) e) (e - 1) 0) = 1
    rw [if_neg (by rw [lenI_LG m]; omega), gp0_LG m e h0 h1, len_LG m]
    refine fpar0Aux_LG_to1 (m+3) m (e-1) (by omega) (by omega) ?_
    push_cast; omega]
  show (if (1 : Int) < 0 then -1 else if Trans.Recal.gp1 (LG m) 1 < 1 then 1
        else Trans.Recal.fpar1Aux (m+2) (LG m) 1 1 0) = 0
  rw [if_neg (by omega), gp1_LG1 m, if_neg (by omega)]
  cases m with
  | zero => exfalso; omega
  | succ p =>
    show (let j1 := Trans.Recal.fpar0 (LG (p+1)) 1 0
          if j1 < 0 then -1 else if Trans.Recal.gp1 (LG (p+1)) j1 < 1 then j1
          else Trans.Recal.fpar1Aux (p+1) (LG (p+1)) 1 j1 0) = 0
    rw [fpar0_LG_1 (p+1)]
    show (if (0 : Int) < 0 then -1 else if Trans.Recal.gp1 (LG (p+1)) 0 < 1 then 0 else _) = 0
    rw [if_neg (by omega), gp1_LG0 (p+1), if_pos (by omega)]

theorem fpar_LG_0_one (m : Nat) : Trans.Recal.fpar (LG m) 0 1 0 = 0 := by
  show (if (1 : Int) < 0 ∨ (1 : Int) ≥ Trans.Recal.lenI (LG m) then -1
        else if (0 : Nat) == 0 then
          Trans.Recal.fpar0Aux ((LG m).length + 1) (LG m) (Trans.Recal.gp0 (LG m) 1) 0 0
        else Trans.Recal.fpar1Aux ((LG m).length + 1) (LG m) (Trans.Recal.gp1 (LG m) 1) 1 0) = 0
  rw [if_neg (by rw [lenI_LG m]; omega)]
  simp only [show ((0 : Nat) == 0) = true from rfl, if_true]
  rw [gp0_LG1 m, len_LG m]
  show (if (0 : Int) < 0 then -1 else if Trans.Recal.gp0 (LG m) 0 < 1 then 0 else _) = 0
  rw [if_neg (by omega), gp0_LG0 m, if_pos (by omega)]

theorem isAncAux_LG_zero (f m : Nat) (h : 1 ≤ f) : Trans.Recal.isAncAux f (LG m) 0 0 0 = true := by
  cases f with
  | zero => omega
  | succ g => rfl

theorem isAncAux_LG_one (f m : Nat) (h : 2 ≤ f) : Trans.Recal.isAncAux f (LG m) 0 1 0 = true := by
  cases f with
  | zero => omega
  | succ g =>
    show (if (0 : Int) == 1 then true
          else let j1 := Trans.Recal.fpar (LG m) 0 1 0
               if j1 == -1 then false else Trans.Recal.isAncAux g (LG m) 0 j1 0) = true
    simp only [show ((0 : Int) == (1 : Int)) = false from rfl, Bool.false_eq_true, if_false]
    rw [fpar_LG_0_one m]
    show (if ((0 : Int) == -1) then false else Trans.Recal.isAncAux g (LG m) 0 0 0) = true
    simp only [show ((0 : Int) == (-1 : Int)) = false from rfl, Bool.false_eq_true, if_false]
    exact isAncAux_LG_zero g m (by omega)

theorem isAncAux_LG (f m : Nat) (j : Int) (h0 : 0 ≤ j) (h1 : j < (m : Int) + 2) (hf : 3 ≤ f) :
    Trans.Recal.isAncAux f (LG m) 0 j 0 = true := by
  by_cases hz : j = 0
  · subst hz; exact isAncAux_LG_zero f m (by omega)
  by_cases ho : j = 1
  · subst ho; exact isAncAux_LG_one f m (by omega)
  cases f with
  | zero => omega
  | succ g =>
    show (if (0 : Int) == j then true
          else let j1 := Trans.Recal.fpar (LG m) 0 j 0
               if j1 == -1 then false else Trans.Recal.isAncAux g (LG m) 0 j1 0) = true
    rw [show ((0 : Int) == j) = false from by simp [Ne.symm hz]]
    simp only [Bool.false_eq_true, if_false]
    rw [fpar_LG_0_e m j (by omega) h1]
    show (if ((1 : Int) == -1) then false else Trans.Recal.isAncAux g (LG m) 0 1 0) = true
    simp only [show ((1 : Int) == (-1 : Int)) = false from rfl, Bool.false_eq_true, if_false]
    exact isAncAux_LG_one g m (by omega)

theorem isPrincipalP_LG (m : Nat) : Trans.Recal.isPrincipalP (LG m) = true := by
  show (!Trans.Recal.isZeroP (LG m) && Trans.Recal.isAnc (LG m) 0 (Trans.Recal.lenI (LG m) - 1) 0) = true
  rw [show Trans.Recal.isZeroP (LG m) = false from by
        show ((LG m).length == 1 && (Trans.Recal.gp1 (LG m) 0 == 0)) = false
        rw [len_LG m]; simp,
      lenI_LG m,
      show Trans.Recal.isAnc (LG m) 0 ((m : Int) + 2 - 1) 0 = true from by
        show (if (0:Int) < 0 ∨ (0:Int) ≥ Trans.Recal.lenI (LG m) then false
              else Trans.Recal.isAncAux ((LG m).length + 1) (LG m) 0 ((m : Int) + 2 - 1) 0) = true
        rw [if_neg (by rw [lenI_LG m]; omega), len_LG m]
        exact isAncAux_LG (m+3) m ((m : Int) + 2 - 1) (by omega) (by omega) (by omega)]
  rfl

theorem foldl_congr_mem {α β : Type} : ∀ (l : List α) (f g : β → α → β) (b : β),
    (∀ x ∈ l, ∀ y, f y x = g y x) → l.foldl f b = l.foldl g b
  | [], _, _, _, _ => rfl
  | a :: t, f, g, b, h => by
    rw [List.foldl_cons, List.foldl_cons, h a (by simp) b]
    exact foldl_congr_mem t f g (g b a) (fun x hx y => h x (by simp [hx]) y)

theorem foldStep : ∀ (m : Nat),
    (List.range m).foldl (fun (r : Trans.Recal.PS) (_ : Nat) => r ++ [CC])
      [((0:Int),(0:Int)), ((1:Int),(1:Int))] = LG m
  | 0 => rfl
  | m+1 => by
    rw [List.range_succ, List.foldl_append, foldStep m]
    show LG m ++ [CC] = _
    show ((0,0) :: (1,1) :: List.replicate m CC) ++ [CC] = (0,0) :: (1,1) :: List.replicate (m+1) CC
    rw [List.replicate_succ']
    simp

theorem redP_LG0 : Trans.Recal.redP (LG 0) = LG 0 := by decide

set_option maxHeartbeats 1000000 in
theorem redP_LG (m : Nat) : Trans.Recal.redP (LG (m+1)) = LG (m+1) := by
  show Trans.Recal.red (Trans.Recal.redFuel (LG (m+1))) (LG (m+1)) = _
  rw [show Trans.Recal.redFuel (LG (m+1)) = (4*m + 59) + 1 from by
        show 40 + 4*((LG (m+1)).length + Trans.Recal.maxE (LG (m+1))) = _
        rw [len_LG (m+1), maxE_LG m]; omega]
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (LG (m+1)) = false from by
        show ((LG (m+1)).length == 1 && (Trans.Recal.gp1 (LG (m+1)) 0 == 0)) = false
        rw [len_LG (m+1)]; simp]
  simp only [Bool.false_eq_true, if_false, isPrincipalP_LG (m+1), if_true]
  rw [show (Trans.Recal.gp0 (LG (m+1)) 0 == 0 && Trans.Recal.gp1 (LG (m+1)) 0 == 0) = true from rfl]
  simp only [if_true, trMax_LG (m+1), lenI_LG (m+1)]
  rw [show ((1 : Int) == (((m+1 : Nat) : Int) + 2 - 1)) = false from by
        simp; omega]
  simp only [Bool.false_eq_true, if_false, brF_LG (m+1), firstNodes_LG (m+1), joints_LG (m+1),
    List.length_replicate]
  rw [show ((List.range (m+1)).foldl
      (init := Trans.Recal.jjSeq 0 1)
      (fun (r : Trans.Recal.PS) (J : Nat) =>
        let bJ := (List.replicate (m+1) [CC]).getD J []
        let nJ : Int := if Trans.Recal.gp1 bJ 0 == 0 then -1
          else Trans.Recal.fpar (LG (m+1)) 1 (((List.range (m+1+1)).map (fun (k : Nat) => (k : Int) + 2)).getD J 0) 0
        let jnJ := (List.replicate (m+1) (1 : Int)).getD J 0
        let NJ : Trans.Recal.PS := (jnJ + 1, nJ + 1) :: Trans.Recal.derp bJ
        r ++ Trans.Recal.incrFirst (Trans.Recal.red (4*m + 59) NJ) (jnJ - nJ)))
      = (List.range (m+1)).foldl (fun (r : Trans.Recal.PS) (_ : Nat) => r ++ [CC]) (Trans.Recal.jjSeq 0 1) from by
    refine foldl_congr_mem _ _ _ _ (fun J hJ r => ?_)
    have hJ' : J < m + 1 := List.mem_range.mp hJ
    show r ++ Trans.Recal.incrFirst (Trans.Recal.red (4*m+59) _) _ = r ++ [CC]
    rw [getD_repl (m+1) J [CC] [] hJ', getD_repl (m+1) J (1 : Int) 0 hJ',
        getD_map_range (m+1+1) J (fun (k : Nat) => (k : Int) + 2) (by omega)]
    show r ++ Trans.Recal.incrFirst (Trans.Recal.red (4*m+59)
      ((1 + 1, (if Trans.Recal.gp1 [CC] 0 == 0 then (-1 : Int)
        else Trans.Recal.fpar (LG (m+1)) 1 ((J : Int) + 2) 0) + 1) :: Trans.Recal.derp [CC])) _ = _
    rw [show (Trans.Recal.gp1 [CC] 0 == 0) = false from rfl]
    simp only [Bool.false_eq_true, if_false]
    rw [fpar_LG_1_e (m+1) ((J : Int) + 2) (by omega) (by push_cast; omega)]
    show r ++ Trans.Recal.incrFirst (Trans.Recal.red (4*m+59) X1) (1 - 0) = _
    rw [show ((4*m + 59 : Nat)) = (4*m + 57) + 2 from by omega, red_X1 (4*m+57)]
    rfl]
  rw [show Trans.Recal.jjSeq 0 1 = [((0:Int),(0:Int)), ((1:Int),(1:Int))] from rfl, foldStep (m+1)]

#guard (List.range 6).all fun m => Trans.Recal.isPrincipalP (LG m)
#guard (List.range 8).all fun m => Trans.Recal.redP (LG m) == LG m
#guard (List.range 8).all fun m => Trans.Recal.isReducedP (LG m)

/-! #### 一段ぶんの部品。証明済み

`runAux` の型 3 の一段が何をするかを、記号的な `m` の上で全部決めた。残るのは
メモ表を通した `transPort` と `markP` の同時帰納だけである。 -/

abbrev D1z : Trans.Dict.BT := .D 1 .zero

theorem beq_BT_self : ∀ (t : Trans.Dict.BT), (t == t) = true
  | .zero => rfl
  | .D u a => by
    show (u == u && (a == a)) = true
    rw [beq_BT_self a, Bool.and_true]
    exact decide_eq_true rfl
  | .sum a b => by
    show ((a == a) && (b == b)) = true
    rw [beq_BT_self a, beq_BT_self b]
    rfl

theorem toL_rep1 : ∀ k, Trans.Dict.BT.toL (rep1 k) = List.replicate k D1z
  | 0 => rfl
  | 1 => rfl
  | k+2 => by
    show Trans.Dict.BT.toL (Trans.Dict.BT.sum D1z (rep1 (k+1))) = _
    show Trans.Dict.BT.toL D1z ++ Trans.Dict.BT.toL (rep1 (k+1)) = _
    rw [toL_rep1 (k+1)]
    rfl

theorem ofL_rep1 : ∀ k, Trans.Dict.BT.ofL (List.replicate k D1z) = rep1 k
  | 0 => rfl
  | 1 => rfl
  | k+2 => by
    rw [List.replicate_succ]
    show Trans.Dict.BT.sum D1z (Trans.Dict.BT.ofL (List.replicate (k+1) D1z)) = _
    rw [ofL_rep1 (k+1)]
    rfl

theorem bplus_rep1 (k : Nat) : Trans.Recal.bplus (rep1 k) D1z = rep1 (k+1) := by
  show Trans.Dict.BT.ofL (Trans.Dict.BT.toL (rep1 k) ++ Trans.Dict.BT.toL D1z) = _
  rw [toL_rep1 k, show Trans.Dict.BT.toL D1z = [D1z] from rfl, ← List.replicate_succ', ofL_rep1 (k+1)]

/-! ### 一段ぶんの部品 -/

theorem isAdm_LG_1 (m : Nat) : Trans.Recal.isAdm (LG m) 1 = true := by
  show (!(decide ((1:Int) > Trans.Recal.lenI (LG m))
    || (Trans.Recal.isParentP (LG m) 1 1 0 && Trans.Recal.isParentP (LG m) 1 2 1))) = true
  rw [isParentP_LG_1 m, isParentP_LG_2 m, lenI_LG m,
      show (decide ((1:Int) > (m : Int) + 2)) = false from by
        apply decide_eq_false; omega]
  rfl

theorem adm_LG_1 (m : Nat) : Trans.Recal.adm (LG m) 1 = 1 := by
  show Trans.Recal.admAux ((LG m).length + 2) (LG m) 1 = 1
  rw [len_LG m]
  show (if (1 : Int) < 0 then 0 else if Trans.Recal.isAdm (LG m) 1 then 1 else Trans.Recal.admAux (m+3) (LG m) 0) = 1
  rw [if_neg (by omega), isAdm_LG_1 m, if_pos rfl]

theorem transType_LG (k : Nat) : Trans.Recal.transTypeMain (LG (k+1)) 1 ((k : Int) + 2) = 3 := by
  show (if Trans.Recal.gp1 (LG (k+1)) ((k : Int)+2) == 0 then _
        else if Trans.Recal.gp1 (LG (k+1)) 1 ≥ Trans.Recal.gp1 (LG (k+1)) ((k : Int)+2) then
          (if Trans.Recal.isAdm (LG (k+1)) 1 then 3 else 4)
        else _) = 3
  rw [gp1_LG (k+1) ((k : Int)+2) (by omega) (by push_cast; omega), gp1_LG1 (k+1)]
  simp only [show ((1 : Int) == 0) = false from rfl, Bool.false_eq_true, if_false]
  rw [if_pos (by omega), isAdm_LG_1 (k+1), if_pos rfl]

theorem mkC2_LG (k : Nat) :
    Trans.Recal.mkC2 (LG (k+1)) 1 ((k : Int) + 2) 3 (Trans.Dict.BT.D 1 (rep1 k)) = Trans.Dict.BT.D 1 (rep1 (k+1)) := by
  show Trans.Dict.BT.D 1 (Trans.Recal.bplus (rep1 k) (Trans.Dict.BT.D (Trans.Recal.gp1 (LG (k+1)) ((k : Int)+2)).toNat Trans.Dict.BT.zero)) = _
  rw [gp1_LG (k+1) ((k : Int)+2) (by omega) (by push_cast; omega)]
  show Trans.Dict.BT.D 1 (Trans.Recal.bplus (rep1 k) D1z) = _
  rw [bplus_rep1 k]

theorem replMark_LG : ∀ (f k : Nat), 2 ≤ f →
    Trans.Recal.replMark f (LBT k) (Trans.Dict.BT.D 1 (rep1 k)) (Trans.Dict.BT.D 1 (rep1 (k+1))) = some (LBT (k+1))
  | 0, _, h => absurd h (by omega)
  | f+1, k, _ => by
    show (if (LBT k) == (Trans.Dict.BT.D 1 (rep1 k)) then some (Trans.Dict.BT.D 1 (rep1 (k+1)))
          else (Trans.Recal.replMark f (Trans.Dict.BT.D 1 (rep1 k)) (Trans.Dict.BT.D 1 (rep1 k)) (Trans.Dict.BT.D 1 (rep1 (k+1)))).map
            (fun aa => Trans.Dict.BT.D 0 aa)) = _
    rw [show ((LBT k) == (Trans.Dict.BT.D 1 (rep1 k))) = false from rfl]
    simp only [Bool.false_eq_true, if_false]
    cases f with
    | zero => omega
    | succ g =>
      rw [show Trans.Recal.replMark (g+1) (Trans.Dict.BT.D 1 (rep1 k)) (Trans.Dict.BT.D 1 (rep1 k)) (Trans.Dict.BT.D 1 (rep1 (k+1)))
            = some (Trans.Dict.BT.D 1 (rep1 (k+1))) from by
        show (if (Trans.Dict.BT.D 1 (rep1 k)) == (Trans.Dict.BT.D 1 (rep1 k)) then some (Trans.Dict.BT.D 1 (rep1 (k+1)))
              else _) = _
        rw [if_pos (beq_BT_self (Trans.Dict.BT.D 1 (rep1 k)))]]
      rfl

/-! #### メモ表の不変量。残るのは `runAux` の再帰そのもの

`runAux` はメモ表を持ち回るので、`transPort` と `markP` は**同時に**帰納しなければ
ならない。表そのものを量化するのではなく、**表が保つ性質**を与えるのが
`Evidence/Cert.lean` §21.6 の型である。

梯子の上で `runAux` が書き込む鍵は 3 種類しかない — `(LG k, none)`、`(LG k, some 1)`、
そして底の `([(0,0)], none)`。`Sound` はその 3 つに正しい値が入っていることを言う。
`Sound_cons` / `Sound_cons_base` が「正しい値を積んでも健全のまま」を与える。

**残っているのは `runAux` の再帰の展開だけ**である。`StateM` の do 記法を
`.run` の形に開いて、燃料の帰納と `Sound` を同時に回す。上の部品 (`redP_LG`・
`transType_LG`・`mkC2_LG`・`replMark_LG`・`adm_LG_1`) が一段ぶんを全部決めているので、
残りは配管である。 -/

/-- 梯子の上で `runAux` が書き込む鍵は 3 種類しかない。 -/
def Val (k : Nat) : Option Int → Trans.Dict.BT
  | none => LBT k
  | _ => .D 1 (rep1 k)

def Good (p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT) : Prop :=
  (∀ k, p.1 = (LG k, none) → p.2 = LBT k)
  ∧ (∀ k, p.1 = (LG k, some 1) → p.2 = .D 1 (rep1 k))
  ∧ (p.1 = ([((0:Int),(0:Int))], none) → p.2 = Trans.Dict.BT.zero)

def Sound (tbl : Trans.Recal.Memo) : Prop := ∀ p ∈ tbl, Good p

/-- 梯子は長さ 2 以上なので `[(0,0)]` とは決して一致しない。 -/
theorem LG_ne_base (k : Nat) : LG k ≠ [((0:Int),(0:Int))] := by
  intro h
  have := congrArg List.length h
  rw [len_LG k] at this
  simp at this

theorem LG_inj (a b : Nat) (h : LG a = LG b) : a = b := by
  have := congrArg List.length h
  rw [len_LG a, len_LG b] at this
  omega

/-- 空の表は健全。 -/
theorem Sound_nil : Sound [] := by intro p hp; simp at hp

/-- 正しい値を積んでも健全。 -/
theorem Sound_cons (tbl : Trans.Recal.Memo) (h : Sound tbl) (k : Nat) (req : Option Int) :
    Sound (((LG k, req), Val k req) :: tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h1 | h1
  · subst h1
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      have e1 : LG k = LG j := congrArg Prod.fst hj
      have e2 : req = none := congrArg Prod.snd hj
      have hkj := LG_inj k j e1
      subst hkj; rw [e2]; rfl
    · intro j hj
      have e1 : LG k = LG j := congrArg Prod.fst hj
      have e2 : req = some 1 := congrArg Prod.snd hj
      have hkj := LG_inj k j e1
      subst hkj; rw [e2]; rfl
    · intro hj
      exact absurd (congrArg Prod.fst hj) (LG_ne_base k)
  · exact h p h1

/-- 底の `[(0,0)]` を積んでも健全。 -/
theorem Sound_cons_base (tbl : Trans.Recal.Memo) (h : Sound tbl) :
    Sound (((([((0:Int),(0:Int))] : Trans.Recal.PS), (none : Option Int)), Trans.Dict.BT.zero) :: tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h1 | h1
  · subst h1
    refine ⟨?_, ?_, fun _ => rfl⟩
    · intro j hj
      exact absurd (congrArg Prod.fst hj).symm (LG_ne_base j)
    · intro j hj
      exact absurd (congrArg Prod.snd hj) (by simp)
  · exact h p h1

/-! #### `runAux` を `.run` の形に開く

`StateM` の do 記法は `StateT.run`・`StateT.bind`・`StateT.get`・`StateT.modifyGet`・
`StateT.pure` を `simp only` で剥がすと開く。**開いた形は下の 2 本が示す通り**で、
表を引いて当たれば表は変わらず、外れれば計算して 1 つ積む。

`isReducedP` は `redP M == M` なので、`redP_LG` から従う。`==` の反射律は
`beq_self_eq_true` を使うと `Classical.choice` が入るので手で書いた
(`Int` は `decide`、`Prod`・`List` は構造帰納)。 -/

theorem beq_Int_self (n : Int) : (n == n) = true := decide_eq_true rfl

theorem beq_pair_self (c : Int × Int) : (c == c) = true := by
  show ((c.1 == c.1) && (c.2 == c.2)) = true
  rw [beq_Int_self c.1, beq_Int_self c.2]; rfl

theorem beq_PS_self : ∀ (l : Trans.Recal.PS), (l == l) = true
  | [] => rfl
  | a :: t => by
    show ((a == a) && (t == t)) = true
    rw [beq_pair_self a, beq_PS_self t]; rfl

/-- **証明済み。** 梯子は既約なので `runAux` の第 1 分岐を通り抜ける。 -/
theorem isReducedP_LG (k : Nat) : Trans.Recal.isReducedP (LG k) = true := by
  show (Trans.Recal.redP (LG k) == LG k) = true
  cases k with
  | zero => rw [redP_LG0]; exact beq_PS_self _
  | succ p => rw [redP_LG p]; exact beq_PS_self _

/-- **証明済み。** 表に当たれば表は変わらない。 -/
theorem run_hit (f : Nat) (M : Trans.Recal.PS) (req : Option Int) (tbl : Trans.Recal.Memo)
    (p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT)
    (h : tbl.find? (fun q => q.1 == (M, req)) = some p) :
    (Trans.Recal.runAux (f+1) M req).run tbl = (p.2, tbl) := by
  rw [Trans.Recal.runAux]
  simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
    MonadStateOf.get, Id.run, h]

/-- **証明済み。** 梯子の底 `[(0,0)]` は `zero` を返して 1 つ積む。 -/
theorem run_base (f : Nat) (tbl : Trans.Recal.Memo)
    (h : tbl.find? (fun q => q.1
      == ((([((0:Int),(0:Int))] : Trans.Recal.PS)), (none : Option Int))) = none) :
    (Trans.Recal.runAux (f+1) ([((0:Int),(0:Int))] : Trans.Recal.PS) none).run tbl
      = (Trans.Dict.BT.zero,
         ((([((0:Int),(0:Int))] : Trans.Recal.PS), (none : Option Int)),
           Trans.Dict.BT.zero) :: tbl) := by
  rw [Trans.Recal.runAux]
  simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
    MonadStateOf.get, Id.run, h]
  rfl

/-! **残るのは外れた場合の合成だけ。** 開いた形は

    match runAux f (predP (LG k)) none tbl with
    | (a, s) => if a == 0 then <型 0 の枝> else <型 1〜6 の枝、c1 を呼ぶ>

で、`k = 0` は `predP = [(0,0)]` なので `a = 0` の枝 (`run_base`)、`k+1` は
`predP = LG k` なので帰納法の仮定から `a = LBT k ≠ 0` で下の枝に入る。下の枝の中身は
`transType_LG`・`mkC2_LG`・`replMark_LG`・`adm_LG_1` が全部決めている。 -/

#guard (List.range 7).all fun k => Trans.Recal.adm (LG k) 1 == 1
#guard (List.range 7).all fun k => Trans.Recal.transTypeMain (LG (k+1)) 1 ((k:Int)+2) == 3
#guard (List.range 6).all fun m => Trans.Recal.joints (LG (m+1)) == List.replicate (m+1) (1 : Int)
#guard (List.range 6).all fun m => Trans.Recal.redFuel (LG (m+1)) == 4*m + 60

/-! #### リンク 2、そして鎖の合流。**証明済み**

`runAux` はメモ表を持ち回るので `transPort` と `markP` を同時に帰納する。表を量化する
代わりに `Sound` を回すのが型で、鍵が 3 種類しかないことがそれを可能にしている。

段の中身は上で全部決めてある: 第 1 分岐は `isReducedP_LG` で抜け、`predP` が梯子を 1 段
下ろし、`k = 0` では底 `[(0,0)]` が `zero` を返して型 0 の枝に入り、`k+1` では
`LBT k ≠ 0` なので型 3 の枝に入って `mkC2` → `replMark` で `LBT (k+1)` になる。

**これで `(0,0)(1,1)(2,1)(3,0)` の行が `oR` の側で全 n について定理になった** — この
リポジトリで `oR` を量化した主張が定理になるのは rung 族に続いて 2 例目、表の行としては
初めてである。 -/

abbrev Base : Trans.Recal.PS := [((0:Int),(0:Int))]

/-- 表に当たった項目は `Good`。 -/
theorem good_of_find {tbl : Trans.Recal.Memo} (hs : Sound tbl) {key : Trans.Recal.PS × Option Int}
    {p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT} (h : tbl.find? (fun q => q.1 == key) = some p) :
    Good p ∧ p.1 = key := by
  refine ⟨hs p (List.mem_of_find?_eq_some h), ?_⟩
  have := List.find?_some h
  exact eq_of_beq this

theorem run_base_ok (f : Nat) (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (f+1) Base none).run tbl).1 = Trans.Dict.BT.zero
    ∧ Sound ((Trans.Recal.runAux (f+1) Base none).run tbl).2 := by
  cases hf : tbl.find? (fun q => q.1 == (Base, (none : Option Int))) with
  | some p =>
    rw [run_hit f Base none tbl p hf]
    obtain ⟨hg, he⟩ := good_of_find hs hf
    exact ⟨hg.2.2 he, hs⟩
  | none =>
    rw [run_base f tbl hf]
    exact ⟨rfl, Sound_cons_base tbl hs⟩

theorem runAux_LG0 (g : Nat) (req : Option Int) (hr : req = none ∨ req = some 1)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+2) (LG 0) req).run tbl).1 = Val 0 req
    ∧ Sound ((Trans.Recal.runAux (g+2) (LG 0) req).run tbl).2 := by
  cases hf : tbl.find? (fun q => q.1 == (LG 0, req)) with
  | some p =>
    rw [run_hit (g+1) (LG 0) req tbl p hf]
    obtain ⟨hg, he⟩ := good_of_find hs hf
    refine ⟨?_, hs⟩
    rcases hr with h1 | h1
    · subst h1; exact hg.1 0 he
    · subst h1; exact hg.2.1 0 he
  | none =>
    rw [Trans.Recal.runAux]
    simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
      MonadStateOf.get, Id.run, hf, isReducedP_LG 0, isPrincipalP_LG 0, Bool.not_true,
      Bool.false_eq_true, if_false, lenI_LG 0,
      show (((0 : Nat) : Int) + 2 - 1 == 0) = false from by decide,
      show Trans.Recal.predP (LG 0) = Base from rfl]
    cases hrun : (Trans.Recal.runAux (g+1) Base none) tbl with
    | mk a s =>
      have ih := run_base_ok g tbl hs
      rw [show ((Trans.Recal.runAux (g+1) Base none).run tbl) = (a, s) from hrun] at ih
      obtain ⟨ha, hsm⟩ := ih
      have ha' : a = Trans.Dict.BT.zero := ha
      have hsm' : Sound s := hsm
      subst ha'
      simp only [show ((Trans.Dict.BT.zero : Trans.Dict.BT) == Trans.Dict.BT.zero) = true from rfl, if_true]
      rcases hr with h1 | h1
      · subst h1
        exact ⟨rfl, Sound_cons s hsm' 0 none⟩
      · subst h1
        exact ⟨rfl, Sound_cons s hsm' 0 (some 1)⟩

theorem isMarkedB_self (t : Trans.Dict.BT) : Trans.Recal.isMarkedB t t = true := by
  show Trans.Recal.isMarkedBAux (Trans.Dict.BT.size t + 2) (some t) t = true
  cases h : Trans.Dict.BT.size t + 2 with
  | zero => omega
  | succ g =>
    show (if t == t then true else Trans.Recal.isMarkedBAux g (Trans.Recal.nextMarkedB t) t) = true
    rw [if_pos (beq_BT_self t)]

theorem replMark_self : ∀ (f u : Nat) (a cc : Trans.Dict.BT), 1 ≤ f →
    Trans.Recal.replMark f (Trans.Dict.BT.D u a) (Trans.Dict.BT.D u a) cc = some cc
  | 0, _, _, _, h => absurd h (by omega)
  | f+1, u, a, cc, _ => by
    show (if (Trans.Dict.BT.D u a) == (Trans.Dict.BT.D u a) then some cc
          else (Trans.Recal.replMark f a (Trans.Dict.BT.D u a) cc).map (fun aa => Trans.Dict.BT.D u aa)) = _
    rw [if_pos (beq_BT_self (Trans.Dict.BT.D u a))]

theorem runAux_LG : ∀ (k g : Nat) (req : Option Int), req = none ∨ req = some 1 →
    ∀ (tbl : Trans.Recal.Memo), Sound tbl →
      ((Trans.Recal.runAux (k+g+2) (LG k) req).run tbl).1 = Val k req
      ∧ Sound ((Trans.Recal.runAux (k+g+2) (LG k) req).run tbl).2
  | 0, g, req, hr, tbl, hs => runAux_LG0 g req hr tbl hs
  | k+1, g, req, hr, tbl, hs => by
    cases hf : tbl.find? (fun q => q.1 == (LG (k+1), req)) with
    | some p =>
      rw [show k+1+g+2 = (k+g+2)+1 from by omega, run_hit (k+g+2) (LG (k+1)) req tbl p hf]
      obtain ⟨hg, he⟩ := good_of_find hs hf
      refine ⟨?_, hs⟩
      rcases hr with h1 | h1
      · subst h1; exact hg.1 (k+1) he
      · subst h1; exact hg.2.1 (k+1) he
    | none =>
      rw [show k+1+g+2 = (k+g+2)+1 from by omega, Trans.Recal.runAux]
      simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
        modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
        MonadStateOf.get, Id.run, hf, isReducedP_LG (k+1), isPrincipalP_LG (k+1),
        Bool.not_true, Bool.false_eq_true, if_false, lenI_LG (k+1),
        show ((((k+1 : Nat) : Int) + 2 - 1) == 0) = false from by simp; omega,
        predP_LG k]
      cases hrun : (Trans.Recal.runAux (k+g+2) (LG k) none) tbl with
      | mk a s =>
        have ih1 := runAux_LG k g none (Or.inl rfl) tbl hs
        rw [show ((Trans.Recal.runAux (k+g+2) (LG k) none).run tbl) = (a, s) from hrun] at ih1
        have ha : a = LBT k := ih1.1
        have hsm : Sound s := ih1.2
        subst ha
        simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
          MonadStateOf.get, Id.run,
          show ((LBT k) == Trans.Dict.BT.zero) = false from rfl, Bool.false_eq_true, if_false,
          show Trans.Recal.fpar (LG (k+1)) 0 (((k+1 : Nat) : Int) + 2 - 1) 0 = 1 from
            fpar_LG_0_e (k+1) (((k+1 : Nat) : Int) + 2 - 1) (by push_cast; omega)
              (by push_cast; omega),
          adm_LG_1 (k+1)]
        cases hrun2 : (Trans.Recal.runAux (k+g+2) (LG k) (some 1)) s with
        | mk c1 s2 =>
          have ih2 := runAux_LG k g (some 1) (Or.inr rfl) s hsm
          rw [show ((Trans.Recal.runAux (k+g+2) (LG k) (some 1)).run s) = (c1, s2) from hrun2] at ih2
          have hc1 : c1 = Trans.Dict.BT.D 1 (rep1 k) := ih2.1
          have hsm2 : Sound s2 := ih2.2
          subst hc1
          simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
          MonadStateOf.get, Id.run,
            show Trans.Recal.transTypeMain (LG (k+1)) 1 (((k+1 : Nat) : Int) + 2 - 1) = 3 from by
              rw [show (((k+1 : Nat) : Int) + 2 - 1) = (k : Int) + 2 from by push_cast; omega]
              exact transType_LG k,
            show Trans.Recal.mkC2 (LG (k+1)) 1 (((k+1 : Nat) : Int) + 2 - 1) 3 (Trans.Dict.BT.D 1 (rep1 k))
                = Trans.Dict.BT.D 1 (rep1 (k+1)) from by
              rw [show (((k+1 : Nat) : Int) + 2 - 1) = (k : Int) + 2 from by push_cast; omega]
              exact mkC2_LG k]
          rcases hr with h1 | h1
          · subst h1
            rw [replMark_LG ((LBT k).size
              + ((Trans.Dict.BT.D 1 (rep1 k)).size + (Trans.Dict.BT.D 1 (rep1 (k+1))).size + 4)) k (by
                show 2 ≤ (LBT k).size + ((Trans.Dict.BT.D 1 (rep1 k)).size + (Trans.Dict.BT.D 1 (rep1 (k+1))).size + 4)
                omega)]
            simp only [Option.getD_some]
            exact ⟨rfl, Sound_cons s2 hsm2 (k+1) none⟩
          · subst h1
            simp only [show ((1 : Int) < ((k+1 : Nat) : Int) + 2 - 1) = True from by
              simp; push_cast; omega, if_true,
              StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
              modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
              MonadStateOf.get, Id.run]
            cases hrun3 : (Trans.Recal.runAux (k+g+2) (LG k) (some 1)) s2 with
            | mk c0 s3 =>
              have ih3 := runAux_LG k g (some 1) (Or.inr rfl) s2 hsm2
              rw [show ((Trans.Recal.runAux (k+g+2) (LG k) (some 1)).run s2) = (c0, s3) from hrun3] at ih3
              have hc0 : c0 = Trans.Dict.BT.D 1 (rep1 k) := ih3.1
              have hsm3 : Sound s3 := ih3.2
              subst hc0
              dsimp only
              rw [if_pos (isMarkedB_self (Trans.Dict.BT.D 1 (rep1 k))),
                replMark_self ((Trans.Dict.BT.D 1 (rep1 k)).size
                  + ((Trans.Dict.BT.D 1 (rep1 k)).size + (Trans.Dict.BT.D 1 (rep1 (k+1))).size + 4))
                  1 (rep1 k) (Trans.Dict.BT.D 1 (rep1 (k+1))) (by
                    show 1 ≤ (Trans.Dict.BT.D 1 (rep1 k)).size
                      + ((Trans.Dict.BT.D 1 (rep1 k)).size + (Trans.Dict.BT.D 1 (rep1 (k+1))).size + 4)
                    omega)]
              simp only [Option.getD_some]
              exact ⟨rfl, Sound_cons s3 hsm3 (k+1) (some 1)⟩

/-- **リンク 2。証明済み。** -/
theorem transPort_LG (m : Nat) : Trans.Recal.transPort (LG m) = LBT m := by
  have hb : m + 2 ≤ Trans.Recal.transFuel (LG m) := by
    show m + 2 ≤ 40 + 6 * ((LG m).length + Trans.Recal.maxE (LG m))
    rw [len_LG m]; omega
  have h : Trans.Recal.transFuel (LG m) = m + (Trans.Recal.transFuel (LG m) - m - 2) + 2 := by omega
  show ((Trans.Recal.runAux (Trans.Recal.transFuel (LG m)) (LG m) none).run []).1 = _
  rw [h]
  exact (runAux_LG m _ none (Or.inl rfl) [] Sound_nil).1

#guard (List.range 8).all fun m => Trans.Recal.transPort (LG m) == LBT m

theorem le_phiofNat_one (j : Nat) : le (phi (ofNat (j+2)) zero) TM.Term.one = false := by
  show ((phi (ofNat (j+2)) zero == TM.Term.one) || lt (phi (ofNat (j+2)) zero) TM.Term.one) = false
  rw [show ((phi (ofNat (j+2)) zero : Term) == TM.Term.one) = false from by
        rw [ofNat_succ_add j]; rfl]
  simp only [Bool.false_or]
  show TM.Term.ltF (TM.Term.fuelOf (phi (ofNat (j+2)) zero) TM.Term.one)
    (phi (ofNat (j+2)) zero) TM.Term.one = false
  cases h : TM.Term.fuelOf (phi (ofNat (j+2)) zero) TM.Term.one with
  | zero => rfl
  | succ g =>
    show (if ((phi (ofNat (j+2)) zero : Term) == TM.Term.one) = true then false
          else if ((ofNat (j+2) : Term) == zero) = true then TM.Term.ltF g zero zero
          else if TM.Term.ltF g (ofNat (j+2)) zero = true then TM.Term.ltF g zero TM.Term.one
          else ((phi (ofNat (j+2)) zero : Term) == zero)
            || TM.Term.ltF g (phi (ofNat (j+2)) zero) zero) = false
    rw [show ((phi (ofNat (j+2)) zero : Term) == TM.Term.one) = false from by
          rw [ofNat_succ_add j]; rfl]
    simp only [Bool.false_eq_true, if_false]
    rw [show ((ofNat (j+2) : Term) == zero) = false from by rw [ofNat_succ_add j]; rfl]
    simp only [Bool.false_eq_true, if_false]
    rw [Rows.ProofsB.ltF_lt_zero g (ofNat (j+2))]
    simp only [Bool.false_eq_true, if_false,
      show ((phi (ofNat (j+2)) zero : Term) == zero) = false from rfl, Bool.false_or]
    exact Rows.ProofsB.ltF_lt_zero g _

/-- **行の主張。証明済み。** 4 本のリンクが継がった。 -/
theorem oR_MG (n : Nat) : Trans.oR (BMS.expand MG n) = some (fsN tG (n+2)) := by
  show (if (BMS.expand MG n).isEmpty then some TM.Term.zero
        else ((Trans.Recal.ofMatrix (BMS.expand MG n)).map Trans.Recal.transPort).map
          (fun t => plus TM.Term.one (Trans.Dict.dict t))) = _
  rw [show (BMS.expand MG n).isEmpty = false from by
        rw [expand_MG n]; cases n <;> rfl]
  simp only [Bool.false_eq_true, if_false, ofMatrix_MG n, Option.map_some]
  rw [transPort_LG (n+1), dict_LBT (n+1), fsN_tG (n+2), phiNF_ofNat_zero n]
  show some (plus TM.Term.one (phi (ofNat (n+2)) zero)) = _
  rw [show plus TM.Term.one (phi (ofNat (n+2)) zero) = phi (ofNat (n+2)) zero from by
    show ofList ((toList TM.Term.one).filter (fun a => le (phi (ofNat (n+2)) zero) a)
      ++ [phi (ofNat (n+2)) zero]) = _
    rw [show toList TM.Term.one = [TM.Term.one] from rfl]
    simp only [List.filter_cons, le_phiofNat_one n, Bool.false_eq_true, if_false, List.filter_nil]
    rfl]

#guard (List.range 6).all fun n => Trans.oR (BMS.expand MG n) == some (fsN tG (n+2))
#guard (List.range 8).all fun m => Trans.Recal.transPort (LG m) == LBT m
#guard Trans.Dict.collapse 1 zero == Omg
-- 側条件が要ることの対照: m = 0 / j = 1 では上の 2 本は成り立たない
#guard !(Trans.Dict.collapse 1 (mulNat Omg 0) == phi zero (mulNat Omg 1))
#guard !(Trans.Dict.collapse 0 (phi zero (mulNat Omg 1)) == phi (ofNat 1) zero)
-- 3 段を合わせると行の主張になる (測定)
#guard (List.range 6).all fun n => Trans.oR (BMS.expand MG n) == some (fsN tG (n+2))

end G1

/-! ## `oR` の行 — 2 行目の測定

展開が 1 列ずつ伸びる行は測定で 5 つあった。G1 で 1 つ閉じたので、同じ形の
`(0,0)(1,1)(2,2)(3,0)` を次に取る。**梯子の形は同じだが、`runAux` の中身は違う。**

    G1 `(0,0)(1,1)(2,1)(3,0)`   trMax = 1 (一定)   型 3   adm = 1   Mark は伸びる
    G2 `(0,0)(1,1)(2,2)(3,0)`   trMax = 1, 2, 2…   型 5   adm = 0   Mark は一定

繰り返す列の行 1 成分が 2 になるだけで `transTypeMain` の枝が変わる。**G1 の道具のうち
持ち越せるのは枠 (`Sound`・`run_hit`・`run_base`・`StateM` の展開・`==` の反射律) で、
一段ぶんの中身は行ごとに取り直しになる。** 下は測定であって定理ではない。 -/

namespace G2

def M2 : BMS.Matrix := [[0,0],[1,1],[2,2],[3,0]]
def t2 : Term := psi (Z zero) (phi zero (Z TM.Term.one))
def L2 (m : Nat) : Trans.Recal.PS := (0,0) :: (1,1) :: List.replicate m ((2:Int),(2:Int))
def rep2 : Nat → Trans.Dict.BT
  | 0 => .D 1 .zero
  | 1 => .D 2 .zero
  | k+1 => .sum (.D 2 .zero) (rep2 k)
def L2BT (m : Nat) : Trans.Dict.BT := .D 0 (rep2 m)

#guard Trans.oR M2 == some t2
#guard rest12.any fun r => r.m == M2 && r.t == t2
#guard (rows.filter fun r => r.proof == "namespace G2").length == 1
#guard (List.range 6).all fun n => BMS.expand M2 n == [[0,0],[1,1]] ++ Trans.repM [[2,2]] (n+1)
#guard (List.range 6).all fun n => Trans.Recal.ofMatrix (BMS.expand M2 n) == some (L2 (n+1))
#guard (List.range 8).all fun m => Trans.Recal.predP (L2 (m+1)) == L2 m
#guard (List.range 8).all fun m => Trans.Recal.redP (L2 m) == L2 m
#guard (List.range 8).all fun m =>
  Trans.Recal.isPrincipalP (L2 m) && !(Trans.Recal.isZeroP (L2 m))
#guard (List.range 8).all fun m => Trans.Recal.transPort (L2 m) == L2BT m
-- **`Mark` の添字は 0 である** (m ≥ 1 で `adm (L2 m) 1 = 0`)。そしてその値は `Trans` と同じ、
-- つまり `c1 = t1` になる。G1 は `Mark 1` が `Trans` と別に伸びていたので、ここは
-- 段が**簡単**になる — `replMark` は自分自身の差し替えなので `G1.replMark_self` が効く。
#guard (List.range 8).all fun m =>
  ((Trans.Recal.runAux (Trans.Recal.transFuel (L2 m)) (L2 m) (some 0)).run []).1 == L2BT m
-- m = 0 だけ  (そこは型 6 で  を呼ばない)
#guard Trans.Recal.adm (L2 0) 1 == 1
#guard (List.range 8).all fun m => Trans.Recal.adm (L2 (m+1)) 1 == 0
#guard (List.range 6).all fun n => Trans.Dict.dict (L2BT (n+1)) == fsN t2 (n+1)
#guard (List.range 6).all fun n => Trans.oR (BMS.expand M2 n) == some (fsN t2 (n+1))
/-! ### 梯子の成分と親関数 (G2)。証明済み -/

abbrev C2 : Int × Int := (2, 2)

theorem len_L2 (m : Nat) : (L2 m).length = m + 2 := by
  show ((0,0) :: (1,1) :: List.replicate m C2).length = _
  simp

theorem lenI_L2 (m : Nat) : Trans.Recal.lenI (L2 m) = (m : Int) + 2 := by
  show (((L2 m).length : Nat) : Int) = _
  rw [len_L2 m]; omega

theorem gp0_L2_0 (m : Nat) : Trans.Recal.gp0 (L2 m) 0 = 0 := rfl
theorem gp1_L2_0 (m : Nat) : Trans.Recal.gp1 (L2 m) 0 = 0 := rfl
theorem gp0_L2_1 (m : Nat) : Trans.Recal.gp0 (L2 m) 1 = 1 := rfl
theorem gp1_L2_1 (m : Nat) : Trans.Recal.gp1 (L2 m) 1 = 1 := rfl

theorem getD_L2 (m : Nat) (j : Int) (h0 : 2 ≤ j) (h1 : j < (m : Int) + 2) :
    (L2 m).getD j.toNat (0,0) = C2 := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, j.toNat = k + 2 := ⟨j.toNat - 2, by omega⟩
  rw [hk]
  show ((0,0) :: (1,1) :: List.replicate m C2).getD (k+2) (0,0) = _
  show (List.replicate m C2).getD k (0,0) = _
  exact G1.getD_repl m k C2 (0,0) (by omega)

theorem gp0_L2 (m : Nat) (j : Int) (h0 : 2 ≤ j) (h1 : j < (m : Int) + 2) : Trans.Recal.gp0 (L2 m) j = 2 := by
  show (if j < 0 then 0 else ((L2 m).getD j.toNat (0,0)).1) = 2
  rw [if_neg (by omega), getD_L2 m j h0 h1]

theorem gp1_L2 (m : Nat) (j : Int) (h0 : 2 ≤ j) (h1 : j < (m : Int) + 2) : Trans.Recal.gp1 (L2 m) j = 2 := by
  show (if j < 0 then 0 else ((L2 m).getD j.toNat (0,0)).2) = 2
  rw [if_neg (by omega), getD_L2 m j h0 h1]

/-! ### 親関数 -/

theorem fpar0_L2_1 (m : Nat) : Trans.Recal.fpar0 (L2 m) 1 0 = 0 := by
  show (if (1 : Int) < 0 ∨ (1 : Int) ≥ Trans.Recal.lenI (L2 m) then -1
        else Trans.Recal.fpar0Aux ((L2 m).length + 1) (L2 m) (Trans.Recal.gp0 (L2 m) 1) 0 0) = 0
  rw [if_neg (by rw [lenI_L2 m]; omega), gp0_L2_1 m, len_L2 m]
  show (if (0 : Int) < 0 then -1 else if Trans.Recal.gp0 (L2 m) 0 < 1 then 0
        else Trans.Recal.fpar0Aux (m+2) (L2 m) 1 (-1) 0) = 0
  rw [if_neg (by omega), gp0_L2_0 m, if_pos (by omega)]

theorem fpar0_L2_2 (m : Nat) (hm : 1 ≤ m) : Trans.Recal.fpar0 (L2 m) 2 1 = 1 := by
  show (if (2 : Int) < 0 ∨ (2 : Int) ≥ Trans.Recal.lenI (L2 m) then -1
        else Trans.Recal.fpar0Aux ((L2 m).length + 1) (L2 m) (Trans.Recal.gp0 (L2 m) 2) 1 1) = 1
  rw [if_neg (by rw [lenI_L2 m]; omega), gp0_L2 m 2 (by omega) (by omega), len_L2 m]
  show (if (1 : Int) < 1 then -1 else if Trans.Recal.gp0 (L2 m) 1 < 2 then 1
        else Trans.Recal.fpar0Aux (m+2) (L2 m) 2 0 1) = 1
  rw [if_neg (by omega), gp0_L2_1 m, if_pos (by omega)]

theorem fpar0_L2_3 (m : Nat) (hm : 2 ≤ m) : Trans.Recal.fpar0 (L2 m) 3 2 = -1 := by
  show (if (3 : Int) < 0 ∨ (3 : Int) ≥ Trans.Recal.lenI (L2 m) then -1
        else Trans.Recal.fpar0Aux ((L2 m).length + 1) (L2 m) (Trans.Recal.gp0 (L2 m) 3) 2 2) = -1
  rw [if_neg (by rw [lenI_L2 m]; omega), gp0_L2 m 3 (by omega) (by omega), len_L2 m]
  show (if (2 : Int) < 2 then -1 else if Trans.Recal.gp0 (L2 m) 2 < 2 then 2
        else Trans.Recal.fpar0Aux (m+2) (L2 m) 2 1 2) = -1
  rw [if_neg (by omega), gp0_L2 m 2 (by omega) (by omega), if_neg (by omega)]
  cases m with
  | zero => omega
  | succ p =>
    show (if (1 : Int) < 2 then -1 else _) = -1
    rw [if_pos (by omega)]

theorem fpar0Aux_L2_to1 : ∀ (f : Nat) (m : Nat) (j0 : Int), 1 ≤ j0 → j0 < (m : Int) + 2 →
    j0 ≤ (f : Int) → Trans.Recal.fpar0Aux f (L2 m) 2 j0 0 = 1
  | 0, _, _, h0, _, hf => by exfalso; simp at hf; omega
  | f+1, m, j0, h0, h1, hf => by
    show (if j0 < 0 then -1 else if Trans.Recal.gp0 (L2 m) j0 < 2 then j0
          else Trans.Recal.fpar0Aux f (L2 m) 2 (j0 - 1) 0) = 1
    rw [if_neg (by omega)]
    by_cases he : j0 = 1
    · subst he; rw [gp0_L2_1 m, if_pos (by omega)]
    · rw [gp0_L2 m j0 (by omega) (by omega), if_neg (by omega)]
      refine fpar0Aux_L2_to1 f m (j0 - 1) (by omega) (by omega) ?_
      push_cast at hf ⊢
      omega

theorem fpar_L2_0_e (m : Nat) (e : Int) (h0 : 2 ≤ e) (h1 : e < (m : Int) + 2) :
    Trans.Recal.fpar (L2 m) 0 e 0 = 1 := by
  show (if e < 0 ∨ e ≥ Trans.Recal.lenI (L2 m) then -1
        else if (0 : Nat) == 0 then Trans.Recal.fpar0Aux ((L2 m).length + 1) (L2 m) (Trans.Recal.gp0 (L2 m) e) (e - 1) 0
        else Trans.Recal.fpar1Aux ((L2 m).length + 1) (L2 m) (Trans.Recal.gp1 (L2 m) e) e 0) = 1
  rw [if_neg (by rw [lenI_L2 m]; omega)]
  simp only [show ((0 : Nat) == 0) = true from rfl, if_true]
  rw [gp0_L2 m e h0 h1, len_L2 m]
  refine fpar0Aux_L2_to1 (m+3) m (e-1) (by omega) (by omega) ?_
  push_cast; omega

theorem fpar_L2_1_1 (m : Nat) : Trans.Recal.fpar (L2 m) 1 1 0 = 0 := by
  show (if (1 : Int) < 0 ∨ (1 : Int) ≥ Trans.Recal.lenI (L2 m) then -1
        else if (1 : Nat) == 0 then Trans.Recal.fpar0Aux ((L2 m).length + 1) (L2 m) (Trans.Recal.gp0 (L2 m) 1) 0 0
        else Trans.Recal.fpar1Aux ((L2 m).length + 1) (L2 m) (Trans.Recal.gp1 (L2 m) 1) 1 0) = 0
  rw [if_neg (by rw [lenI_L2 m]; omega)]
  simp only [show ((1 : Nat) == 0) = false from rfl, Bool.false_eq_true, if_false]
  rw [gp1_L2_1 m, len_L2 m]
  show (let j1 := Trans.Recal.fpar0 (L2 m) 1 0
        if j1 < 0 then -1 else if Trans.Recal.gp1 (L2 m) j1 < 1 then j1
        else Trans.Recal.fpar1Aux (m+2) (L2 m) 1 j1 0) = 0
  rw [fpar0_L2_1 m]
  show (if (0 : Int) < 0 then -1 else if Trans.Recal.gp1 (L2 m) 0 < 1 then 0 else _) = 0
  rw [if_neg (by omega), gp1_L2_0 m, if_pos (by omega)]

theorem fpar_L2_1_2 (m : Nat) (hm : 1 ≤ m) : Trans.Recal.fpar (L2 m) 1 2 1 = 1 := by
  show (if (2 : Int) < 0 ∨ (2 : Int) ≥ Trans.Recal.lenI (L2 m) then -1
        else if (1 : Nat) == 0 then Trans.Recal.fpar0Aux ((L2 m).length + 1) (L2 m) (Trans.Recal.gp0 (L2 m) 2) 1 1
        else Trans.Recal.fpar1Aux ((L2 m).length + 1) (L2 m) (Trans.Recal.gp1 (L2 m) 2) 2 1) = 1
  rw [if_neg (by rw [lenI_L2 m]; omega)]
  simp only [show ((1 : Nat) == 0) = false from rfl, Bool.false_eq_true, if_false]
  rw [gp1_L2 m 2 (by omega) (by omega), len_L2 m]
  show (let j1 := Trans.Recal.fpar0 (L2 m) 2 1
        if j1 < 1 then -1 else if Trans.Recal.gp1 (L2 m) j1 < 2 then j1
        else Trans.Recal.fpar1Aux (m+2) (L2 m) 2 j1 1) = 1
  rw [fpar0_L2_2 m hm]
  show (if (1 : Int) < 1 then -1 else if Trans.Recal.gp1 (L2 m) 1 < 2 then 1 else _) = 1
  rw [if_neg (by omega), gp1_L2_1 m, if_pos (by omega)]

theorem fpar_L2_1_3 (m : Nat) (hm : 2 ≤ m) : Trans.Recal.fpar (L2 m) 1 3 2 = -1 := by
  show (if (3 : Int) < 0 ∨ (3 : Int) ≥ Trans.Recal.lenI (L2 m) then -1
        else if (1 : Nat) == 0 then Trans.Recal.fpar0Aux ((L2 m).length + 1) (L2 m) (Trans.Recal.gp0 (L2 m) 3) 2 2
        else Trans.Recal.fpar1Aux ((L2 m).length + 1) (L2 m) (Trans.Recal.gp1 (L2 m) 3) 3 2) = -1
  rw [if_neg (by rw [lenI_L2 m]; omega)]
  simp only [show ((1 : Nat) == 0) = false from rfl, Bool.false_eq_true, if_false]
  rw [gp1_L2 m 3 (by omega) (by omega), len_L2 m]
  show (let j1 := Trans.Recal.fpar0 (L2 m) 3 2
        if j1 < 2 then -1 else if Trans.Recal.gp1 (L2 m) j1 < 2 then j1
        else Trans.Recal.fpar1Aux (m+2) (L2 m) 2 j1 2) = -1
  rw [fpar0_L2_3 m hm, if_pos (by omega)]

theorem fpar_L2_1_e (m : Nat) (e : Int) (h0 : 2 ≤ e) (h1 : e < (m : Int) + 2) :
    Trans.Recal.fpar (L2 m) 1 e 0 = 1 := by
  show (if e < 0 ∨ e ≥ Trans.Recal.lenI (L2 m) then -1
        else if (1 : Nat) == 0 then Trans.Recal.fpar0Aux ((L2 m).length + 1) (L2 m) (Trans.Recal.gp0 (L2 m) e) (e - 1) 0
        else Trans.Recal.fpar1Aux ((L2 m).length + 1) (L2 m) (Trans.Recal.gp1 (L2 m) e) e 0) = 1
  rw [if_neg (by rw [lenI_L2 m]; omega)]
  simp only [show ((1 : Nat) == 0) = false from rfl, Bool.false_eq_true, if_false]
  rw [gp1_L2 m e h0 h1, len_L2 m]
  show (let j1 := Trans.Recal.fpar0 (L2 m) e 0
        if j1 < 0 then -1 else if Trans.Recal.gp1 (L2 m) j1 < 2 then j1
        else Trans.Recal.fpar1Aux (m+2) (L2 m) 2 j1 0) = 1
  rw [show Trans.Recal.fpar0 (L2 m) e 0 = 1 from by
    show (if e < 0 ∨ e ≥ Trans.Recal.lenI (L2 m) then -1
          else Trans.Recal.fpar0Aux ((L2 m).length + 1) (L2 m) (Trans.Recal.gp0 (L2 m) e) (e - 1) 0) = 1
    rw [if_neg (by rw [lenI_L2 m]; omega), gp0_L2 m e h0 h1, len_L2 m]
    refine fpar0Aux_L2_to1 (m+3) m (e-1) (by omega) (by omega) ?_
    push_cast; omega]
  show (if (1 : Int) < 0 then -1 else if Trans.Recal.gp1 (L2 m) 1 < 2 then 1 else _) = 1
  rw [if_neg (by omega), gp1_L2_1 m, if_pos (by omega)]

#guard (List.range 5).all fun m => (List.range (m+2)).all fun j =>
  (Trans.Recal.gp0 (L2 m) j == (if j == 0 then 0 else if j == 1 then 1 else 2))
    && (Trans.Recal.gp1 (L2 m) j == (if j == 0 then 0 else if j == 1 then 1 else 2))

/-! ### `Trans.Recal.ppair` — 定数列の一般形 (G1 の `ppair_rep` を列で一般化したもの) -/

theorem gp0_repc (c : Int × Int) (m : Nat) (j : Int) (h0 : 0 ≤ j) (h1 : j < (m : Int)) :
    Trans.Recal.gp0 (List.replicate m c) j = c.1 := by
  show (if j < 0 then 0 else ((List.replicate m c).getD j.toNat (0,0)).1) = c.1
  rw [if_neg (by omega), G1.getD_repl m j.toNat c (0,0) (by omega)]

theorem fpar0Aux_repc (c : Int × Int) : ∀ (f m : Nat) (j0 : Int), j0 < (m : Int) →
    Trans.Recal.fpar0Aux f (List.replicate m c) c.1 j0 0 = -1
  | 0, _, _, _ => rfl
  | f+1, m, j0, h => by
    show (if j0 < 0 then -1 else if Trans.Recal.gp0 (List.replicate m c) j0 < c.1 then j0
          else Trans.Recal.fpar0Aux f (List.replicate m c) c.1 (j0 - 1) 0) = -1
    by_cases hneg : j0 < 0
    · rw [if_pos hneg]
    · rw [if_neg hneg, gp0_repc c m j0 (by omega) h, if_neg (by omega),
          fpar0Aux_repc c f m (j0 - 1) (by omega)]

theorem fAnc_repc (c : Int × Int) (m : Nat) (j : Int) (h0 : 0 ≤ j) (h1 : j < (m : Int)) :
    Trans.Recal.fAnc (List.replicate m c) 0 j 0 = [j] := by
  show (if j < 0 ∨ j ≥ Trans.Recal.lenI (List.replicate m c) then []
        else Trans.Recal.fAncAux ((List.replicate m c).length + 1) (List.replicate m c) 0 j 0 [j]) = _
  rw [if_neg (by
    show ¬(j < 0 ∨ j ≥ (((List.replicate m c).length : Nat) : Int))
    rw [List.length_replicate]; omega)]
  cases hf : (List.replicate m c).length + 1 with
  | zero => simp at hf
  | succ g =>
    show (let j1 := Trans.Recal.fpar (List.replicate m c) 0 j 0
          if j1 ≥ 0 then Trans.Recal.fAncAux g (List.replicate m c) 0 j1 0 ([j] ++ [j1]) else [j]) = _
    rw [show Trans.Recal.fpar (List.replicate m c) 0 j 0 = -1 from by
      show (if j < 0 ∨ j ≥ Trans.Recal.lenI (List.replicate m c) then -1
            else if (0 : Nat) == 0 then
              Trans.Recal.fpar0Aux ((List.replicate m c).length + 1) (List.replicate m c)
                (Trans.Recal.gp0 (List.replicate m c) j) (j - 1) 0
            else Trans.Recal.fpar1Aux ((List.replicate m c).length + 1) (List.replicate m c)
                (Trans.Recal.gp1 (List.replicate m c) j) j 0) = -1
      rw [if_neg (by
        show ¬(j < 0 ∨ j ≥ (((List.replicate m c).length : Nat) : Int))
        rw [List.length_replicate]; omega)]
      simp only [show ((0 : Nat) == 0) = true from rfl, if_true]
      rw [gp0_repc c m j h0 h1]
      exact fpar0Aux_repc c _ m (j - 1) (by omega)]
    rfl

theorem ppairAux_repc (c : Int × Int) : ∀ (f m k : Nat), k ≤ m → k ≤ f → ∀ (acc : List Trans.Recal.PS),
    Trans.Recal.ppairAux f (List.replicate m c) ((k : Int) - 1) acc = List.replicate k [c] ++ acc
  | 0, _, 0, _, _, acc => rfl
  | f+1, m, 0, _, _, acc => by
    show (if ((0 : Int) - 1) < 0 then acc else _) = _
    rw [if_pos (by omega)]; simp
  | f+1, m, k+1, hkm, hkf, acc => by
    show (if ((k+1 : Int) - 1) < 0 then acc
          else
            let ans := Trans.Recal.fAnc (List.replicate m c) 0 ((k+1 : Int) - 1) 0
            let j0 := (ans.getLast?).getD 0
            Trans.Recal.ppairAux f (List.replicate m c) (j0 - 1)
              (Trans.Recal.slice (List.replicate m c) j0 (((k+1 : Int) - 1) + 1) :: acc)) = _
    rw [if_neg (by omega)]
    simp only [show ((k : Int) + 1 - 1) = (k : Int) from by omega]
    show Trans.Recal.ppairAux f (List.replicate m c)
      (((Trans.Recal.fAnc (List.replicate m c) 0 ((k : Int)) 0).getLast?).getD 0 - 1)
      (Trans.Recal.slice (List.replicate m c) (((Trans.Recal.fAnc (List.replicate m c) 0 ((k : Int)) 0).getLast?).getD 0)
        ((k : Int) + 1) :: acc) = _
    rw [fAnc_repc c m (k : Int) (by omega) (by omega)]
    show Trans.Recal.ppairAux f (List.replicate m c) ((k : Int) - 1)
      (Trans.Recal.slice (List.replicate m c) (k : Int) ((k : Int) + 1) :: acc) = _
    rw [show Trans.Recal.slice (List.replicate m c) (k : Int) ((k : Int) + 1) = [c] from by
      show ((List.replicate m c).drop k).take (((k : Int) + 1 - k).toNat) = _
      rw [show (((k : Int) + 1 - (k : Int)).toNat) = 1 from by omega, List.drop_replicate]
      cases hm : m - k with
      | zero => omega
      | succ p => rw [List.replicate_succ]; rfl,
      ppairAux_repc c f m k (by omega) (by omega)]
    rw [List.replicate_succ']
    simp

theorem ppair_repc (c : Int × Int) (m : Nat) :
    Trans.Recal.ppair (List.replicate m c) = List.replicate m [c] := by
  show Trans.Recal.ppairAux ((List.replicate m c).length + 1) (List.replicate m c)
    (Trans.Recal.lenI (List.replicate m c) - 1) [] = _
  rw [show Trans.Recal.lenI (List.replicate m c) = (m : Int) from by
        show (((List.replicate m c).length : Nat) : Int) = _
        rw [List.length_replicate],
      ppairAux_repc c ((List.replicate m c).length + 1) m m (by omega)
        (by rw [List.length_replicate]; omega) []]
  simp

#guard (List.range 5).all fun m =>
  Trans.Recal.ppair (List.replicate m C2) == List.replicate m [C2]

/-! ### `trMax`・`brF`・`joints` (G2)。証明済み

`trMax` が 2 になるのは、`(2,2)` が位置 2 まで行 1 の親の鎖を伸ばすからである。G1 は
`(2,1)` で位置 1 で切れていた。その 1 段の差が `brF` の起点と `firstNodes` を 1 ずらす。 -/

theorem fpar_L2_1_3' (m : Nat) (hm : 1 ≤ m) : Trans.Recal.fpar (L2 m) 1 3 2 = -1 := by
  cases m with
  | zero => omega
  | succ p =>
    cases p with
    | zero => rfl
    | succ q => exact fpar_L2_1_3 (q+2) (by omega)

theorem isParentP_L2_1 (m : Nat) : Trans.Recal.isParentP (L2 m) 1 1 0 = true := by
  show (decide ((0:Int) ≤ 0) && decide ((0:Int) < Trans.Recal.lenI (L2 m))
    && ((0 : Int) == Trans.Recal.fpar (L2 m) 1 1 0)) = true
  rw [fpar_L2_1_1 m, lenI_L2 m,
      show (decide ((0:Int) < (m : Int) + 2)) = true from decide_eq_true (by omega)]
  rfl

theorem isParentP_L2_2 (m : Nat) (hm : 1 ≤ m) : Trans.Recal.isParentP (L2 m) 1 2 1 = true := by
  show (decide ((1:Int) ≤ 1) && decide ((1:Int) < Trans.Recal.lenI (L2 m))
    && ((1 : Int) == Trans.Recal.fpar (L2 m) 1 2 1)) = true
  rw [fpar_L2_1_2 m hm, lenI_L2 m,
      show (decide ((1:Int) < (m : Int) + 2)) = true from decide_eq_true (by omega)]
  rfl

theorem isParentP_L2_3 (m : Nat) (hm : 1 ≤ m) : Trans.Recal.isParentP (L2 m) 1 3 2 = false := by
  show (decide ((2:Int) ≤ 2) && decide ((2:Int) < Trans.Recal.lenI (L2 m))
    && ((2 : Int) == Trans.Recal.fpar (L2 m) 1 3 2)) = false
  rw [fpar_L2_1_3' m hm, show ((2 : Int) == (-1 : Int)) = false from rfl, Bool.and_false]

/-- **証明済み。** `m ≥ 1` の梯子の `Trans.Recal.trMax` は 2。 -/
theorem trMax_L2 (m : Nat) (hm : 1 ≤ m) : Trans.Recal.trMax (L2 m) = 2 := by
  show Trans.Recal.trMaxAux ((L2 m).length + 1) (L2 m) 0 = 2
  rw [len_L2 m]
  show (if (0 : Int) ≥ Trans.Recal.lenI (L2 m) then Trans.Recal.lenI (L2 m) - 1
        else if !(Trans.Recal.isParentP (L2 m) 1 1 0) then 0
        else Trans.Recal.trMaxAux (m+2) (L2 m) 1) = 2
  rw [if_neg (by rw [lenI_L2 m]; omega), isParentP_L2_1 m]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  show (if (1 : Int) ≥ Trans.Recal.lenI (L2 m) then Trans.Recal.lenI (L2 m) - 1
        else if !(Trans.Recal.isParentP (L2 m) 1 2 1) then 1
        else Trans.Recal.trMaxAux (m+1) (L2 m) 2) = 2
  rw [if_neg (by rw [lenI_L2 m]; omega), isParentP_L2_2 m hm]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  cases m with
  | zero => omega
  | succ p =>
    show (if (2 : Int) ≥ Trans.Recal.lenI (L2 (p+1)) then Trans.Recal.lenI (L2 (p+1)) - 1
          else if !(Trans.Recal.isParentP (L2 (p+1)) 1 3 2) then 2
          else Trans.Recal.trMaxAux (p+1) (L2 (p+1)) 3) = 2
    rw [if_neg (by rw [lenI_L2 (p+1)]; push_cast; omega), isParentP_L2_3 (p+1) (by omega)]
    simp

/-- **証明済み。** -/
theorem brF_L2 (m : Nat) : Trans.Recal.brF (L2 (m+1)) = List.replicate m [C2] := by
  show Trans.Recal.ppair ((L2 (m+1)).drop (Trans.Recal.trMax (L2 (m+1)) + 1).toNat) = _
  rw [trMax_L2 (m+1) (by omega)]
  show Trans.Recal.ppair ((L2 (m+1)).drop 3) = _
  rw [show (L2 (m+1)).drop 3 = List.replicate m C2 from by
    show ((0,0) :: (1,1) :: List.replicate (m+1) C2).drop 3 = _
    rw [List.replicate_succ]; rfl]
  exact ppair_repc C2 m

theorem idxSum_step2 : ∀ (m : Nat) (l : List Int) (c : Int),
    (List.replicate m [C2]).foldl
      (fun (a : List Int × Int) q => (a.1 ++ [a.2 + (q.length : Int)], a.2 + (q.length : Int)))
      (l, c) = (l ++ (List.range m).map (fun (k : Nat) => c + 1 + (k : Int)), c + (m : Int))
  | 0, l, c => by simp
  | m+1, l, c => by
    rw [List.replicate_succ, List.foldl_cons]
    show (List.replicate m [C2]).foldl _ (l ++ [c + 1], c + 1) = _
    rw [idxSum_step2 m (l ++ [c + 1]) (c + 1)]
    have h : (List.range (m+1)).map (fun (k : Nat) => c + 1 + (k : Int))
        = [c + 1] ++ (List.range m).map (fun (k : Nat) => c + 1 + 1 + (k : Int)) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [List.singleton_append, List.cons.injEq]
      refine ⟨by omega, ?_⟩
      apply List.map_congr_left
      intro k _
      show c + 1 + ((k+1 : Nat) : Int) = c + 1 + 1 + (k : Int)
      push_cast; omega
    rw [h, ← List.append_assoc]
    congr 1
    omega

theorem firstNodes_L2 (m : Nat) :
    Trans.Recal.firstNodes (L2 (m+1)) = (List.range (m+1)).map (fun (k : Nat) => (k : Int) + 3) := by
  show ((Trans.Recal.idxSum (Trans.Recal.brF (L2 (m+1)))).map (fun e => Trans.Recal.trMax (L2 (m+1)) + 1 + e)) = _
  rw [brF_L2 m, trMax_L2 (m+1) (by omega)]
  rw [show Trans.Recal.idxSum (List.replicate m [C2]) = (List.range (m+1)).map (fun (k : Nat) => (k : Int)) from by
    show ((List.replicate m [C2]).foldl _ ([0], 0)).1 = _
    rw [idxSum_step2 m [0] 0]
    show ([0] ++ (List.range m).map (fun (k : Nat) => (0 : Int) + 1 + (k : Int))) = _
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.singleton_append, List.cons.injEq]
    refine ⟨rfl, ?_⟩
    apply List.map_congr_left
    intro k _
    show (0 : Int) + 1 + (k : Int) = ((k+1 : Nat) : Int)
    push_cast; omega]
  rw [List.map_map]
  apply List.map_congr_left
  intro k _
  show (2 : Int) + 1 + (k : Int) = (k : Int) + 3
  omega

/-- **証明済み。** -/
theorem joints_L2 (m : Nat) : Trans.Recal.joints (L2 (m+1)) = List.replicate m 1 := by
  show ((Trans.Recal.firstNodes (L2 (m+1))).dropLast.map (fun e => Trans.Recal.fpar (L2 (m+1)) 0 e 0)) = _
  rw [firstNodes_L2 m, List.range_succ, List.map_append]
  show ((((List.range m).map (fun (k : Nat) => (k : Int) + 3)) ++ [(m : Int) + 3]).dropLast.map _) = _
  rw [List.dropLast_concat, List.map_map]
  rw [show ((List.range m).map ((fun e => Trans.Recal.fpar (L2 (m+1)) 0 e 0) ∘ (fun (k : Nat) => (k : Int) + 3)))
        = (List.range m).map (fun (_ : Nat) => (1 : Int)) from by
      apply List.map_congr_left
      intro k hk
      show Trans.Recal.fpar (L2 (m+1)) 0 ((k : Int) + 3) 0 = 1
      have := List.mem_range.mp hk
      exact fpar_L2_0_e (m+1) ((k : Int) + 3) (by omega) (by push_cast; omega)]
  exact G1.map_const_range m 1

#guard (List.range 6).all fun m => Trans.Recal.trMax (L2 (m+1)) == 2
#guard (List.range 6).all fun m => Trans.Recal.brF (L2 (m+1)) == List.replicate m [C2]
#guard (List.range 6).all fun m => Trans.Recal.joints (L2 (m+1)) == List.replicate m (1 : Int)
#guard (List.range 6).all fun m =>
  Trans.Recal.firstNodes (L2 (m+1)) == (List.range (m+1)).map (fun (k : Nat) => (k : Int) + 3)

/-! ### `red` の燃料非依存性 (G2)。証明済み

主枝が呼ぶ入力は 2 つ。`Y2` は `j1p == j1` に落ちて再帰が無く、`Y1` はそれを 1 回呼んで
自分に戻る。**`Y1` は燃料 0 でも同じ値**なので、全 f で成り立つ。 -/

def Y1 : Trans.Recal.PS := [((2:Int),(2:Int))]
def Y2 : Trans.Recal.PS := [((0:Int),(0:Int)),((1:Int),(1:Int)),((4:Int),(2:Int))]

/-- `Y2` は `j1p == j1` に落ちるので再帰が無い。 -/
theorem red_Y2 (f : Nat) : Trans.Recal.red (f+1) Y2 = [((0:Int),(0:Int)),((1:Int),(1:Int)),((2:Int),(2:Int))] :=
  rfl

/-- `Y1` は `Y2` を 1 回呼んで自分に戻る。**燃料 0 でも同じ値**なので全 f で成り立つ。 -/
theorem red_Y1 : ∀ (f : Nat), Trans.Recal.red f Y1 = Y1
  | 0 => rfl
  | f+1 => by
    show (if Trans.Recal.isZeroP Y1 then Trans.Recal.zeroPS
          else if Trans.Recal.isPrincipalP Y1 then
            (if Trans.Recal.gp0 Y1 0 == 0 && Trans.Recal.gp1 Y1 0 == 0 then _
             else
              (if Trans.Recal.gp1 Y1 0 == 0 then Trans.Recal.red f (Trans.Recal.incrFirst Y1 (-(Trans.Recal.gp0 Y1 0)))
               else
                let N := Trans.Recal.red f (Trans.Recal.jjSeq 0 (Trans.Recal.gp1 Y1 0 - 1) ++ Trans.Recal.incrFirst Y1 (Trans.Recal.gp1 Y1 0))
                let jN : Int := Trans.Recal.lenI N - 1
                if decide (Trans.Recal.gp1 Y1 0 ≤ jN) && Trans.Recal.isPrincipalP (N.drop (Trans.Recal.gp1 Y1 0).toNat) then
                  Trans.Recal.incrFirst (N.drop (Trans.Recal.gp1 Y1 0).toNat)
                    (-(Trans.Recal.gp0 N (Trans.Recal.gp1 Y1 0)) + Trans.Recal.gp1 N (Trans.Recal.gp1 Y1 0))
                else Y1))
          else (Trans.Recal.ppair Y1).flatMap (Trans.Recal.red f)) = _
    rw [show (Trans.Recal.jjSeq 0 (Trans.Recal.gp1 Y1 0 - 1) ++ Trans.Recal.incrFirst Y1 (Trans.Recal.gp1 Y1 0)) = Y2 from rfl]
    cases f with
    | zero => rfl
    | succ g => rw [red_Y2 g]; rfl

#guard (List.range 6).all fun f => Trans.Recal.red f Y1 == Y1
#guard (List.range 6).all fun f =>
  Trans.Recal.red (f+1) Y2 == [((0:Int),(0:Int)),((1:Int),(1:Int)),((2:Int),(2:Int))]
/-! ### `redP (L2 m) = L2 m`。証明済み

主枝の各段は `r ↦ r ++ [(2,2)]` で同一。初期値が `jjSeq 0 2` = `(0,0)(1,1)(2,2)` になる
のが G1 (`jjSeq 0 1`) との違いで、`trMax` の 1 段ぶんである。**`m = 0, 1` は畳み込みに
入らない** (`trMax == j1` で `jjSeq` がそのまま答になる) ので別に扱う。 -/

theorem maxE_rep2 : ∀ (m a : Nat), 2 ≤ a →
    (List.replicate m C2).foldl
      (fun b c => Nat.max b (Nat.max c.1.toNat c.2.toNat)) a = a
  | 0, _, _ => rfl
  | m+1, a, h => by
    rw [List.replicate_succ, List.foldl_cons]
    show (List.replicate m C2).foldl _ (Nat.max a 2) = a
    rw [show Nat.max a 2 = a from Nat.max_eq_left h, maxE_rep2 m a h]

theorem maxE_L2 (m : Nat) : Trans.Recal.maxE (L2 (m+1)) = 2 := by
  show (((0,0) :: (1,1) :: List.replicate (m+1) C2).foldl
    (fun b c => Nat.max b (Nat.max c.1.toNat c.2.toNat)) 0) = 2
  rw [List.foldl_cons, List.foldl_cons, List.replicate_succ, List.foldl_cons]
  show (List.replicate m C2).foldl _ 2 = 2
  exact maxE_rep2 m 2 (by omega)

theorem fpar_L2_0_one (m : Nat) : Trans.Recal.fpar (L2 m) 0 1 0 = 0 := by
  show (if (1 : Int) < 0 ∨ (1 : Int) ≥ Trans.Recal.lenI (L2 m) then -1
        else if (0 : Nat) == 0 then Trans.Recal.fpar0Aux ((L2 m).length + 1) (L2 m) (Trans.Recal.gp0 (L2 m) 1) 0 0
        else Trans.Recal.fpar1Aux ((L2 m).length + 1) (L2 m) (Trans.Recal.gp1 (L2 m) 1) 1 0) = 0
  rw [if_neg (by rw [lenI_L2 m]; omega)]
  simp only [show ((0 : Nat) == 0) = true from rfl, if_true]
  rw [gp0_L2_1 m, len_L2 m]
  show (if (0 : Int) < 0 then -1 else if Trans.Recal.gp0 (L2 m) 0 < 1 then 0 else _) = 0
  rw [if_neg (by omega), gp0_L2_0 m, if_pos (by omega)]

theorem isAncAux_L2_zero (f m : Nat) (h : 1 ≤ f) : Trans.Recal.isAncAux f (L2 m) 0 0 0 = true := by
  cases f with
  | zero => omega
  | succ g => rfl

theorem isAncAux_L2_one (f m : Nat) (h : 2 ≤ f) : Trans.Recal.isAncAux f (L2 m) 0 1 0 = true := by
  cases f with
  | zero => omega
  | succ g =>
    show (if (0 : Int) == 1 then true
          else let j1 := Trans.Recal.fpar (L2 m) 0 1 0
               if j1 == -1 then false else Trans.Recal.isAncAux g (L2 m) 0 j1 0) = true
    simp only [show ((0 : Int) == (1 : Int)) = false from rfl, Bool.false_eq_true, if_false]
    rw [fpar_L2_0_one m]
    show (if ((0 : Int) == -1) then false else Trans.Recal.isAncAux g (L2 m) 0 0 0) = true
    simp only [show ((0 : Int) == (-1 : Int)) = false from rfl, Bool.false_eq_true, if_false]
    exact isAncAux_L2_zero g m (by omega)

theorem isAncAux_L2 (f m : Nat) (j : Int) (h0 : 0 ≤ j) (h1 : j < (m : Int) + 2) (hf : 3 ≤ f) :
    Trans.Recal.isAncAux f (L2 m) 0 j 0 = true := by
  by_cases hz : j = 0
  · subst hz; exact isAncAux_L2_zero f m (by omega)
  by_cases ho : j = 1
  · subst ho; exact isAncAux_L2_one f m (by omega)
  cases f with
  | zero => omega
  | succ g =>
    show (if (0 : Int) == j then true
          else let j1 := Trans.Recal.fpar (L2 m) 0 j 0
               if j1 == -1 then false else Trans.Recal.isAncAux g (L2 m) 0 j1 0) = true
    rw [show ((0 : Int) == j) = false from by simp [Ne.symm hz]]
    simp only [Bool.false_eq_true, if_false]
    rw [fpar_L2_0_e m j (by omega) h1]
    show (if ((1 : Int) == -1) then false else Trans.Recal.isAncAux g (L2 m) 0 1 0) = true
    simp only [show ((1 : Int) == (-1 : Int)) = false from rfl, Bool.false_eq_true, if_false]
    exact isAncAux_L2_one g m (by omega)

theorem isPrincipalP_L2 (m : Nat) : Trans.Recal.isPrincipalP (L2 m) = true := by
  show (!Trans.Recal.isZeroP (L2 m) && Trans.Recal.isAnc (L2 m) 0 (Trans.Recal.lenI (L2 m) - 1) 0) = true
  rw [show Trans.Recal.isZeroP (L2 m) = false from by
        show ((L2 m).length == 1 && (Trans.Recal.gp1 (L2 m) 0 == 0)) = false
        rw [len_L2 m]; simp,
      lenI_L2 m,
      show Trans.Recal.isAnc (L2 m) 0 ((m : Int) + 2 - 1) 0 = true from by
        show (if (0:Int) < 0 ∨ (0:Int) ≥ Trans.Recal.lenI (L2 m) then false
              else Trans.Recal.isAncAux ((L2 m).length + 1) (L2 m) 0 ((m : Int) + 2 - 1) 0) = true
        rw [if_neg (by rw [lenI_L2 m]; omega), len_L2 m]
        exact isAncAux_L2 (m+3) m ((m : Int) + 2 - 1) (by omega) (by omega) (by omega)]
  rfl

theorem foldStep2 : ∀ (m : Nat),
    (List.range m).foldl (fun (r : Trans.Recal.PS) (_ : Nat) => r ++ [C2])
      [((0:Int),(0:Int)), ((1:Int),(1:Int)), ((2:Int),(2:Int))] = L2 (m+1)
  | 0 => rfl
  | m+1 => by
    rw [List.range_succ, List.foldl_append, foldStep2 m]
    show L2 (m+1) ++ [C2] = _
    show ((0,0) :: (1,1) :: List.replicate (m+1) C2) ++ [C2]
       = (0,0) :: (1,1) :: List.replicate (m+2) C2
    rw [List.replicate_succ' (n := m+1)]
    simp

theorem redP_L2_small : Trans.Recal.redP (L2 0) = L2 0 ∧ Trans.Recal.redP (L2 1) = L2 1 := by
  constructor <;> decide

set_option maxHeartbeats 1000000 in
/-- **証明済み。** -/
theorem redP_L2 (m : Nat) : Trans.Recal.redP (L2 (m+2)) = L2 (m+2) := by
  show Trans.Recal.red (Trans.Recal.redFuel (L2 (m+2))) (L2 (m+2)) = _
  rw [show Trans.Recal.redFuel (L2 (m+2)) = (4*m + 63) + 1 from by
        show 40 + 4*((L2 (m+2)).length + Trans.Recal.maxE (L2 (m+2))) = _
        rw [len_L2 (m+2), maxE_L2 (m+1)]; omega]
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (L2 (m+2)) = false from by
        show ((L2 (m+2)).length == 1 && (Trans.Recal.gp1 (L2 (m+2)) 0 == 0)) = false
        rw [len_L2 (m+2)]; simp]
  simp only [Bool.false_eq_true, if_false, isPrincipalP_L2 (m+2), if_true]
  rw [show (Trans.Recal.gp0 (L2 (m+2)) 0 == 0 && Trans.Recal.gp1 (L2 (m+2)) 0 == 0) = true from rfl]
  simp only [if_true, trMax_L2 (m+2) (by omega), lenI_L2 (m+2)]
  rw [show ((2 : Int) == (((m+2 : Nat) : Int) + 2 - 1)) = false from by simp; omega]
  simp only [Bool.false_eq_true, if_false, brF_L2 (m+1), firstNodes_L2 (m+1), joints_L2 (m+1),
    List.length_replicate]
  rw [show ((List.range (m+1)).foldl
      (init := Trans.Recal.jjSeq 0 2)
      (fun (r : Trans.Recal.PS) (J : Nat) =>
        let bJ := (List.replicate (m+1) [C2]).getD J []
        let nJ : Int := if Trans.Recal.gp1 bJ 0 == 0 then -1
          else Trans.Recal.fpar (L2 (m+2)) 1
            (((List.range (m+2)).map (fun (k : Nat) => (k : Int) + 3)).getD J 0) 0
        let jnJ := (List.replicate (m+1) (1 : Int)).getD J 0
        let NJ : Trans.Recal.PS := (jnJ + 1, nJ + 1) :: Trans.Recal.derp bJ
        r ++ Trans.Recal.incrFirst (Trans.Recal.red (4*m + 63) NJ) (jnJ - nJ)))
      = (List.range (m+1)).foldl (fun (r : Trans.Recal.PS) (_ : Nat) => r ++ [C2]) (Trans.Recal.jjSeq 0 2) from by
    refine G1.foldl_congr_mem _ _ _ _ (fun J hJ r => ?_)
    have hJ' : J < m+1 := List.mem_range.mp hJ
    show r ++ Trans.Recal.incrFirst (Trans.Recal.red (4*m+63) _) _ = r ++ [C2]
    rw [G1.getD_repl (m+1) J [C2] [] hJ', G1.getD_repl (m+1) J (1 : Int) 0 hJ',
        G1.getD_map_range (m+2) J (fun (k : Nat) => (k : Int) + 3) (by omega)]
    show r ++ Trans.Recal.incrFirst (Trans.Recal.red (4*m+63)
      ((1 + 1, (if Trans.Recal.gp1 [C2] 0 == 0 then (-1 : Int)
        else Trans.Recal.fpar (L2 (m+2)) 1 ((J : Int) + 3) 0) + 1) :: Trans.Recal.derp [C2])) _ = _
    rw [show (Trans.Recal.gp1 [C2] 0 == 0) = false from rfl]
    simp only [Bool.false_eq_true, if_false]
    rw [fpar_L2_1_e (m+2) ((J : Int) + 3) (by omega) (by push_cast; omega)]
    show r ++ Trans.Recal.incrFirst (Trans.Recal.red (4*m+63) Y1) (1 - 1) = _
    rw [red_Y1 (4*m+63)]
    rfl]
  rw [show Trans.Recal.jjSeq 0 2 = [((0:Int),(0:Int)), ((1:Int),(1:Int)), ((2:Int),(2:Int))] from rfl,
      foldStep2 (m+1)]

#guard (List.range 6).all fun m => Trans.Recal.redP (L2 m) == L2 m
#guard (List.range 6).all fun m => Trans.Recal.isReducedP (L2 m)

/-! ### 一段ぶんの部品 (G2)。証明済み

型 5 の一段は `c1 = t1 = L2BT (m+1)` から `mkC2` が `D 2 0` を 1 つ足して `L2BT (m+2)` を
作り、`replMark` は自分自身の差し替えなので `G1.replMark_self` で閉じる。**`Mark` の添字が
0 なのは `adm (L2 m) 1 = 0` から**で、位置 1 が admitted でない (行 1 の親の鎖が
位置 2 まで伸びている) ことの帰結である。 -/

abbrev D2z : Trans.Dict.BT := .D 2 .zero

theorem toL_rep2 : ∀ k, Trans.Dict.BT.toL (rep2 (k+1)) = List.replicate (k+1) D2z
  | 0 => rfl
  | k+1 => by
    show Trans.Dict.BT.toL (Trans.Dict.BT.sum D2z (rep2 (k+1))) = _
    show Trans.Dict.BT.toL D2z ++ Trans.Dict.BT.toL (rep2 (k+1)) = _
    rw [toL_rep2 k]
    rfl

theorem ofL_rep2 : ∀ k, Trans.Dict.BT.ofL (List.replicate (k+1) D2z) = rep2 (k+1)
  | 0 => rfl
  | k+1 => by
    rw [List.replicate_succ]
    show Trans.Dict.BT.sum D2z (Trans.Dict.BT.ofL (List.replicate (k+1) D2z)) = _
    rw [ofL_rep2 k]
    rfl

theorem bplus_rep2 (k : Nat) : Trans.Recal.bplus (rep2 (k+1)) D2z = rep2 (k+2) := by
  show Trans.Dict.BT.ofL (Trans.Dict.BT.toL (rep2 (k+1)) ++ Trans.Dict.BT.toL D2z) = _
  rw [toL_rep2 k, show Trans.Dict.BT.toL D2z = [D2z] from rfl, ← List.replicate_succ', ofL_rep2 (k+1)]

/-- `k = -1` は `Trans.Recal.isParentP` の第 1 連言 `0 ≤ k` で落ちる。 -/
theorem isParentP_L2_neg (m : Nat) : Trans.Recal.isParentP (L2 m) 1 0 (-1) = false := by
  show (decide ((0:Int) ≤ (-1:Int)) && decide ((-1:Int) < Trans.Recal.lenI (L2 m))
    && ((-1 : Int) == Trans.Recal.fpar (L2 m) 1 0 (-1))) = false
  rw [show (decide ((0:Int) ≤ (-1:Int))) = false from by decide]
  rfl

theorem isAdm_L2_0 (m : Nat) : Trans.Recal.isAdm (L2 m) 0 = true := by
  show (!(decide ((0:Int) > Trans.Recal.lenI (L2 m))
    || (Trans.Recal.isParentP (L2 m) 1 0 (0 - 1) && Trans.Recal.isParentP (L2 m) 1 (0 + 1) 0))) = true
  rw [show ((0:Int) - 1) = -1 from by omega, show ((0:Int) + 1) = 1 from by omega,
      isParentP_L2_neg m, lenI_L2 m,
      show (decide ((0:Int) > (m : Int) + 2)) = false from by apply decide_eq_false; omega]
  rfl

theorem isAdm_L2_1 (m : Nat) (hm : 1 ≤ m) : Trans.Recal.isAdm (L2 m) 1 = false := by
  show (!(decide ((1:Int) > Trans.Recal.lenI (L2 m))
    || (Trans.Recal.isParentP (L2 m) 1 1 (1 - 1) && Trans.Recal.isParentP (L2 m) 1 (1 + 1) 1))) = false
  rw [show ((1:Int) - 1) = 0 from by omega, show ((1:Int) + 1) = 2 from by omega,
      isParentP_L2_1 m, isParentP_L2_2 m hm, lenI_L2 m,
      show (decide ((1:Int) > (m : Int) + 2)) = false from by apply decide_eq_false; omega]
  rfl

theorem adm_L2_1 (m : Nat) (hm : 1 ≤ m) : Trans.Recal.adm (L2 m) 1 = 0 := by
  show Trans.Recal.admAux ((L2 m).length + 2) (L2 m) 1 = 0
  rw [len_L2 m]
  show (if (1 : Int) < 0 then 0 else if Trans.Recal.isAdm (L2 m) 1 then 1 else Trans.Recal.admAux (m+3) (L2 m) 0) = 0
  rw [if_neg (by omega), isAdm_L2_1 m hm]
  simp only [Bool.false_eq_true, if_false]
  show (if (0 : Int) < 0 then 0 else if Trans.Recal.isAdm (L2 m) 0 then 0 else Trans.Recal.admAux (m+2) (L2 m) (-1)) = 0
  rw [if_neg (by omega), isAdm_L2_0 m, if_pos rfl]

theorem transType_L2 (m : Nat) : Trans.Recal.transTypeMain (L2 (m+2)) 1 ((m : Int) + 3) = 5 := by
  show (if Trans.Recal.gp1 (L2 (m+2)) ((m : Int)+3) == 0 then _
        else if Trans.Recal.gp1 (L2 (m+2)) 1 ≥ Trans.Recal.gp1 (L2 (m+2)) ((m : Int)+3) then _
        else if (1 : Int) + 1 < (m : Int) + 3 then 5 else 6) = 5
  rw [gp1_L2 (m+2) ((m : Int)+3) (by omega) (by push_cast; omega), gp1_L2_1 (m+2)]
  simp only [show ((2 : Int) == 0) = false from rfl, Bool.false_eq_true, if_false]
  rw [if_neg (by omega), if_pos (by omega)]

theorem mkC2_L2 (m : Nat) :
    Trans.Recal.mkC2 (L2 (m+2)) 1 ((m : Int) + 3) 5 (L2BT (m+1)) = L2BT (m+2) := by
  show Trans.Dict.BT.D 0 (Trans.Recal.bplus (rep2 (m+1)) (Trans.Dict.BT.D (Trans.Recal.gp1 (L2 (m+2)) ((m : Int)+3)).toNat Trans.Dict.BT.zero)) = _
  rw [gp1_L2 (m+2) ((m : Int)+3) (by omega) (by push_cast; omega)]
  show Trans.Dict.BT.D 0 (Trans.Recal.bplus (rep2 (m+1)) D2z) = _
  rw [bplus_rep2 m]
  rfl

#guard (List.range 6).all fun m => Trans.Recal.adm (L2 (m+1)) 1 == 0
#guard (List.range 6).all fun m =>
  Trans.Recal.transTypeMain (L2 (m+2)) 1 ((m : Int) + 3) == 5
#guard (List.range 6).all fun m =>
  Trans.Recal.mkC2 (L2 (m+2)) 1 ((m : Int) + 3) 5 (L2BT (m+1)) == L2BT (m+2)

/-! ### メモ帰納とリンク 2 (G2)。証明済み

G1 で作った枠 (`Sound` の型・`G1.run_hit`・`G1.run_base`・`StateM` の展開・`==` の反射律・
`G1.replMark_self`・`G1.isMarkedB_self`) がそのまま効く。**`c1 = t1` なので `replMark` は自分
自身の差し替えで、G1 の `replMark_LG` にあたるものは要らない。** 場合は 3 つ:
`k = 0` が型 0、`k = 1` が型 6、`k ≥ 2` が型 5。 -/

def Val2 (k : Nat) : Option Int → Trans.Dict.BT := fun _ => L2BT k

def Good2 (p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT) : Prop :=
  (∀ k, p.1 = (L2 k, none) → p.2 = L2BT k)
  ∧ (∀ k, p.1 = (L2 k, some 0) → p.2 = L2BT k)
  ∧ (p.1 = (G1.Base, (none : Option Int)) → p.2 = Trans.Dict.BT.zero)

def Sound2 (tbl : Trans.Recal.Memo) : Prop := ∀ p ∈ tbl, Good2 p

theorem L2_ne_base (k : Nat) : L2 k ≠ G1.Base := by
  intro h
  have := congrArg List.length h
  rw [len_L2 k] at this
  simp [G1.Base] at this

theorem L2_inj (a b : Nat) (h : L2 a = L2 b) : a = b := by
  have := congrArg List.length h
  rw [len_L2 a, len_L2 b] at this
  omega

theorem Sound2_nil : Sound2 [] := by intro p hp; simp at hp

theorem Sound2_cons (tbl : Trans.Recal.Memo) (h : Sound2 tbl) (k : Nat) (req : Option Int) :
    Sound2 (((L2 k, req), Val2 k req) :: tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h1 | h1
  · subst h1
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      have e1 : L2 k = L2 j := congrArg Prod.fst hj
      have hkj := L2_inj k j e1
      subst hkj; rfl
    · intro j hj
      have e1 : L2 k = L2 j := congrArg Prod.fst hj
      have hkj := L2_inj k j e1
      subst hkj; rfl
    · intro hj
      exact absurd (congrArg Prod.fst hj) (L2_ne_base k)
  · exact h p h1

theorem Sound2_cons_base (tbl : Trans.Recal.Memo) (h : Sound2 tbl) :
    Sound2 (((G1.Base, (none : Option Int)), Trans.Dict.BT.zero) :: tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h1 | h1
  · subst h1
    refine ⟨?_, ?_, fun _ => rfl⟩
    · intro j hj
      exact absurd (congrArg Prod.fst hj).symm (L2_ne_base j)
    · intro j hj
      exact absurd (congrArg Prod.snd hj) (by simp)
  · exact h p h1

theorem run_base_ok2 (f : Nat) (tbl : Trans.Recal.Memo) (hs : Sound2 tbl) :
    ((Trans.Recal.runAux (f+1) G1.Base none).run tbl).1 = Trans.Dict.BT.zero
    ∧ Sound2 ((Trans.Recal.runAux (f+1) G1.Base none).run tbl).2 := by
  cases hf : tbl.find? (fun q => q.1 == (G1.Base, (none : Option Int))) with
  | some p =>
    rw [G1.run_hit f G1.Base none tbl p hf]
    have hm := hs p (List.mem_of_find?_eq_some hf)
    have hb := List.find?_some hf
    have he : p.1 = (G1.Base, (none : Option Int)) := eq_of_beq hb
    exact ⟨hm.2.2 he, hs⟩
  | none =>
    rw [G1.run_base f tbl hf]
    exact ⟨rfl, Sound2_cons_base tbl hs⟩

theorem predP_L2 (m : Nat) : Trans.Recal.predP (L2 (m+1)) = L2 m := by
  show (if (L2 (m+1)).length == 1 then L2 (m+1) else (L2 (m+1)).dropLast) = _
  rw [show ((L2 (m+1)).length == 1) = false from by rw [len_L2 (m+1)]; simp]
  show ((0,0) :: (1,1) :: List.replicate (m+1) C2).dropLast = _
  rw [List.dropLast_cons_of_ne_nil (by simp [List.replicate_succ]),
      List.dropLast_cons_of_ne_nil (by simp [List.replicate_succ]),
      G1.dropLast_replicate m C2]
  rfl

theorem isReducedP_L2 (k : Nat) : Trans.Recal.isReducedP (L2 k) = true := by
  show (Trans.Recal.redP (L2 k) == L2 k) = true
  cases k with
  | zero => rw [redP_L2_small.1]; exact G1.beq_PS_self _
  | succ p =>
    cases p with
    | zero => rw [redP_L2_small.2]; exact G1.beq_PS_self _
    | succ q => rw [redP_L2 q]; exact G1.beq_PS_self _

theorem transType_L2_one : Trans.Recal.transTypeMain (L2 1) 1 2 = 6 := rfl
theorem mkC2_L2_one : Trans.Recal.mkC2 (L2 1) 1 2 6 (L2BT 0) = L2BT 1 := rfl


theorem replMark_L2BT (f k : Nat) (cc : Trans.Dict.BT) (h : 1 ≤ f) :
    Trans.Recal.replMark f (L2BT k) (L2BT k) cc = some cc :=
  G1.replMark_self f 0 (rep2 k) cc h

theorem runAux_L2 : ∀ (k g : Nat) (req : Option Int), req = none ∨ req = some 0 →
    ∀ (tbl : Trans.Recal.Memo), Sound2 tbl →
      ((Trans.Recal.runAux (k+g+2) (L2 k) req).run tbl).1 = L2BT k
      ∧ Sound2 ((Trans.Recal.runAux (k+g+2) (L2 k) req).run tbl).2
  | 0, g, req, hr, tbl, hs => by
    cases hf : tbl.find? (fun q => q.1 == (L2 0, req)) with
    | some p =>
      rw [show 0+g+2 = (g+1)+1 from by omega, G1.run_hit (g+1) (L2 0) req tbl p hf]
      have hm := hs p (List.mem_of_find?_eq_some hf)
      have hb := List.find?_some hf
      have he : p.1 = (L2 0, req) := eq_of_beq hb
      refine ⟨?_, hs⟩
      rcases hr with h1 | h1
      · subst h1; exact hm.1 0 he
      · subst h1; exact hm.2.1 0 he
    | none =>
      rw [show 0+g+2 = (g+1)+1 from by omega, Trans.Recal.runAux]
      simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
          MonadStateOf.get, Id.run, hf, isReducedP_L2 0, isPrincipalP_L2 0, Bool.not_true,
        Bool.false_eq_true, if_false, lenI_L2 0,
        show (((0 : Nat) : Int) + 2 - 1 == 0) = false from by decide,
        show Trans.Recal.predP (L2 0) = G1.Base from rfl]
      cases hrun : (Trans.Recal.runAux (g+1) G1.Base none) tbl with
      | mk a s =>
        have ih := run_base_ok2 g tbl hs
        rw [show ((Trans.Recal.runAux (g+1) G1.Base none).run tbl) = (a, s) from hrun] at ih
        have ha' : a = Trans.Dict.BT.zero := ih.1
        have hsm' : Sound2 s := ih.2
        subst ha'
        simp only [show ((Trans.Dict.BT.zero : Trans.Dict.BT) == Trans.Dict.BT.zero) = true from rfl, if_true]
        rcases hr with h1 | h1
        · subst h1; exact ⟨rfl, Sound2_cons s hsm' 0 none⟩
        · subst h1; exact ⟨rfl, Sound2_cons s hsm' 0 (some 0)⟩
  | k+1, g, req, hr, tbl, hs => by
    cases hf : tbl.find? (fun q => q.1 == (L2 (k+1), req)) with
    | some p =>
      rw [show k+1+g+2 = (k+g+2)+1 from by omega, G1.run_hit (k+g+2) (L2 (k+1)) req tbl p hf]
      have hm := hs p (List.mem_of_find?_eq_some hf)
      have hb := List.find?_some hf
      have he : p.1 = (L2 (k+1), req) := eq_of_beq hb
      refine ⟨?_, hs⟩
      rcases hr with h1 | h1
      · subst h1; exact hm.1 (k+1) he
      · subst h1; exact hm.2.1 (k+1) he
    | none =>
      rw [show k+1+g+2 = (k+g+2)+1 from by omega, Trans.Recal.runAux]
      simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
          MonadStateOf.get, Id.run, hf, isReducedP_L2 (k+1), isPrincipalP_L2 (k+1),
        Bool.not_true, Bool.false_eq_true, if_false, lenI_L2 (k+1),
        show ((((k+1 : Nat) : Int) + 2 - 1) == 0) = false from by simp; omega,
        show Trans.Recal.predP (L2 (k+1)) = L2 k from predP_L2 k]
      cases hrun : (Trans.Recal.runAux (k+g+2) (L2 k) none) tbl with
      | mk a s =>
        have ih1 := runAux_L2 k g none (Or.inl rfl) tbl hs
        rw [show ((Trans.Recal.runAux (k+g+2) (L2 k) none).run tbl) = (a, s) from hrun] at ih1
        have ha : a = L2BT k := ih1.1
        have hsm : Sound2 s := ih1.2
        subst ha
        simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
          MonadStateOf.get, Id.run,
          show ((L2BT k) == Trans.Dict.BT.zero) = false from by cases k <;> rfl,
          Bool.false_eq_true, if_false,
          show Trans.Recal.fpar (L2 (k+1)) 0 (((k+1 : Nat) : Int) + 2 - 1) 0 = 1 from
            fpar_L2_0_e (k+1) (((k+1 : Nat) : Int) + 2 - 1) (by push_cast; omega)
              (by push_cast; omega),
          adm_L2_1 (k+1) (by omega)]
        cases hrun2 : (Trans.Recal.runAux (k+g+2) (L2 k) (some 0)) s with
        | mk c1 s2 =>
          have ih2 := runAux_L2 k g (some 0) (Or.inr rfl) s hsm
          rw [show ((Trans.Recal.runAux (k+g+2) (L2 k) (some 0)).run s) = (c1, s2) from hrun2] at ih2
          have hc1 : c1 = L2BT k := ih2.1
          have hsm2 : Sound2 s2 := ih2.2
          subst hc1
          simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
          MonadStateOf.get, Id.run,
            show Trans.Recal.mkC2 (L2 (k+1)) 1 (((k+1 : Nat) : Int) + 2 - 1)
                (Trans.Recal.transTypeMain (L2 (k+1)) 1 (((k+1 : Nat) : Int) + 2 - 1)) (L2BT k)
                = L2BT (k+1) from by
              cases k with
              | zero => rfl
              | succ p =>
                rw [show ((((p+2 : Nat) : Int) + 2 - 1)) = (p : Int) + 3 from by push_cast; omega,
                    transType_L2 p, mkC2_L2 p]]
          rcases hr with h1 | h1
          · subst h1
            rw [replMark_L2BT ((L2BT k).size + ((L2BT k).size + (L2BT (k+1)).size + 4))
              k (L2BT (k+1)) (by omega)]
            exact ⟨rfl, Sound2_cons s2 hsm2 (k+1) none⟩
          · subst h1
            simp only [show ((0 : Int) < ((k+1 : Nat) : Int) + 2 - 1) = True from by
              simp; push_cast; omega, if_true, StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
          MonadStateOf.get, Id.run]
            cases hrun3 : (Trans.Recal.runAux (k+g+2) (L2 k) (some 0)) s2 with
            | mk c0 s3 =>
              have ih3 := runAux_L2 k g (some 0) (Or.inr rfl) s2 hsm2
              rw [show ((Trans.Recal.runAux (k+g+2) (L2 k) (some 0)).run s2) = (c0, s3) from hrun3] at ih3
              have hc0 : c0 = L2BT k := ih3.1
              have hsm3 : Sound2 s3 := ih3.2
              subst hc0
              dsimp only
              rw [if_pos (G1.isMarkedB_self (L2BT k)),
                replMark_L2BT ((L2BT k).size + ((L2BT k).size + (L2BT (k+1)).size + 4))
                  k (L2BT (k+1)) (by omega)]
              exact ⟨rfl, Sound2_cons s3 hsm3 (k+1) (some 0)⟩

/-- **リンク 2 (2 行目)。証明済み。** -/
theorem transPort_L2 (m : Nat) : Trans.Recal.transPort (L2 m) = L2BT m := by
  have hb : m + 2 ≤ Trans.Recal.transFuel (L2 m) := by
    show m + 2 ≤ 40 + 6 * ((L2 m).length + Trans.Recal.maxE (L2 m))
    rw [len_L2 m]; omega
  have h : Trans.Recal.transFuel (L2 m) = m + (Trans.Recal.transFuel (L2 m) - m - 2) + 2 := by omega
  show ((Trans.Recal.runAux (Trans.Recal.transFuel (L2 m)) (L2 m) none).run []).1 = _
  rw [h]
  exact (runAux_L2 m _ none (Or.inl rfl) [] Sound2_nil).1

#guard (List.range 8).all fun m => Trans.Recal.transPort (L2 m) == L2BT m

/-! ### リンク 1・3 と行の主張 (G2)。証明済み

リンク 3 は初めて `collapse` の**強臨界の枝**に入る。Ω₂ の倍数は `le (reg 1) a` が真に
なるのでそちらに落ち、`ψ_{Z0}` がそのまま被る。項の側は `cofT (φ̄(0,Ω₂)) = ω` なので
`fsN` の `ψ` の節が**対角化ではなく素通り**になり、中は G1 と同じ
`ω^{c+1}[n] = ω^c·n` の規則である。 -/

theorem expand_M2 (n : Nat) :
    BMS.expand M2 n = ([[0,0],[1,1]] : Matrix) ++ Trans.repM ([[2,2]] : Matrix) (n+1) := by
  show (BMS.expand? M2 n).getD [] = _
  have h : BMS.expand? M2 n
      = some (M2.take 2 ++ ((List.range (n+1)).map fun a =>
          ([[2 + a*0*1, 2 + a*0*1]] : Matrix)).flatten) := rfl
  have hf : (fun a => ([[2 + a*0*1, 2 + a*0*1]] : Matrix)) = (fun _ => ([[2,2]] : Matrix)) := by
    funext a; simp
  rw [h, hf, Trans.flat_range ([[2,2]] : Matrix) (n+1)]
  rfl

theorem all_len_rep2 : ∀ k,
    (Trans.repM ([[2,2]] : Matrix) k).all (fun c => decide (c.length ≤ 2)) = true
  | 0 => rfl
  | k+1 => by
    show (([[2,2]] : Matrix) ++ Trans.repM ([[2,2]] : Matrix) k).all _ = true
    rw [List.all_append, all_len_rep2 k]; rfl

theorem map_rep2 : ∀ k,
    (Trans.repM ([[2,2]] : Matrix) k).map (fun c => ((c.getD 0 0 : Int), (c.getD 1 0 : Int)))
      = List.replicate k ((2 : Int), (2 : Int))
  | 0 => rfl
  | k+1 => by
    show (([[2,2]] : Matrix) ++ Trans.repM ([[2,2]] : Matrix) k).map _ = _
    rw [List.map_append, map_rep2 k, List.replicate_succ]
    rfl

/-- **リンク 1 (G2)。証明済み。** -/
theorem ofMatrix_M2 (n : Nat) : Trans.Recal.ofMatrix (BMS.expand M2 n) = some (L2 (n+1)) := by
  rw [expand_M2 n]
  unfold Trans.Recal.ofMatrix
  rw [show (([[0,0],[1,1]] : Matrix) ++ Trans.repM ([[2,2]] : Matrix) (n+1)).isEmpty
        = false from by cases n <;> rfl,
      List.all_append, all_len_rep2 (n+1)]
  show some ((([[0,0],[1,1]] : Matrix) ++ Trans.repM ([[2,2]] : Matrix) (n+1)).map
    (fun c => ((c.getD 0 0 : Int), (c.getD 1 0 : Int)))) = _
  rw [List.map_append, map_rep2 (n+1)]
  rfl

#guard (List.range 6).all fun n => Trans.Recal.ofMatrix (BMS.expand M2 n) == some (L2 (n+1))

/-! ### リンク 3 (G2) -/

abbrev ZO : Term := Z TM.Term.one

theorem isAP_ZO : ZO.isAP = true := rfl

theorem plus_one_ofNat : ∀ (j : Nat), plus TM.Term.one (ofNat j) = ofNat (j+1)
  | 0 => rfl
  | j+1 => by
    rw [← Rows.ProofsB.mulNat_one_ofNat (j+1), ← Rows.ProofsB.mulNat_one_ofNat (j+2)]
    unfold plus
    rw [Rows.ProofsB.toList_mulNat (show (TM.Term.one : Term).isAP = true from rfl) (j+1),
        List.replicate_succ]
    show ofList ((toList TM.Term.one).filter (fun a => le TM.Term.one a)
      ++ (TM.Term.one :: List.replicate j TM.Term.one)) = _
    rw [show toList TM.Term.one = [TM.Term.one] from rfl]
    simp only [List.filter_cons, show le TM.Term.one TM.Term.one = true from rfl,
      List.filter_nil, if_true]
    rw [List.singleton_append, ← List.replicate_succ, ← List.replicate_succ]
    rfl

theorem wcnf_ZO : ∀ (j : Nat),
    Trans.Dict.wcnf (Trans.Dict.reg 1) (List.replicate (j+1) ZO) = ([(ZO, ofNat (j+1))], zero)
  | 0 => rfl
  | j+1 => by
    rw [List.replicate_succ]
    show (if lt ZO (Trans.Dict.reg 1) = true then ([], ofList (ZO :: List.replicate (j+1) ZO))
          else
            match Trans.Dict.wcnf (Trans.Dict.reg 1) (List.replicate (j+1) ZO) with
            | ((a', c') :: ps, tl) =>
              if (ofList (((toList (Trans.Dict.logOm ZO)).filter (fun q => !lt q (Trans.Dict.reg 1))).map (Trans.Dict.divAP (Trans.Dict.reg 1)))
                    == a') = true then
                ((ofList (((toList (Trans.Dict.logOm ZO)).filter (fun q => !lt q (Trans.Dict.reg 1))).map
                    (Trans.Dict.divAP (Trans.Dict.reg 1))),
                  plus (omegaNF (ofList ((toList (Trans.Dict.logOm ZO)).filter (fun q => lt q (Trans.Dict.reg 1))))) c')
                  :: ps, tl)
              else ((ofList (((toList (Trans.Dict.logOm ZO)).filter (fun q => !lt q (Trans.Dict.reg 1))).map
                      (Trans.Dict.divAP (Trans.Dict.reg 1))),
                     omegaNF (ofList ((toList (Trans.Dict.logOm ZO)).filter (fun q => lt q (Trans.Dict.reg 1)))))
                    :: (a', c') :: ps, tl)
            | ([], tl) =>
              ([(ofList (((toList (Trans.Dict.logOm ZO)).filter (fun q => !lt q (Trans.Dict.reg 1))).map (Trans.Dict.divAP (Trans.Dict.reg 1))),
                 omegaNF (ofList ((toList (Trans.Dict.logOm ZO)).filter (fun q => lt q (Trans.Dict.reg 1)))))], tl)) = _
    rw [show lt ZO (Trans.Dict.reg 1) = false from rfl, wcnf_ZO j]
    simp only [Bool.false_eq_true, if_false,
      show (ofList ((((toList (Trans.Dict.logOm ZO)).filter (fun q => !lt q (Trans.Dict.reg 1)))).map
        (Trans.Dict.divAP (Trans.Dict.reg 1))) == ZO) = true from rfl, if_true]
    show ((ZO, plus TM.Term.one (ofNat (j+1))) :: [], zero) = _
    rw [plus_one_ofNat (j+1)]

#guard (List.range 6).all fun j => Trans.Dict.wcnf (Trans.Dict.reg 1) (List.replicate (j+1) ZO)
  == ([(ZO, ofNat (j+1))], zero)

theorem toList_mulZO (j : Nat) : toList (mulNat ZO j) = List.replicate j ZO :=
  Rows.ProofsB.toList_mulNat isAP_ZO j

theorem mulL_ZO : ∀ (j : Nat), Trans.Dict.mulL ZO (ofNat (j+1)) = mulNat ZO (j+1)
  | 0 => rfl
  | j+1 => by
    show ofList ((toList (ofNat (j+2))).map (fun p => omegaNF (plus ZO (Trans.Dict.logOm p)))) = _
    rw [← Rows.ProofsB.mulNat_one_ofNat (j+2),
        Rows.ProofsB.toList_mulNat (show (TM.Term.one : Term).isAP = true from rfl) (j+2)]
    rw [show ((List.replicate (j+2) TM.Term.one).map
          (fun p => omegaNF (plus ZO (Trans.Dict.logOm p)))) = List.replicate (j+2) ZO from by
        rw [List.map_replicate]
        rfl]
    rfl

/-- **`Trans.Dict.collapse` の法則 (G2)。** Ω₂ の倍数は強臨界の枝に入り、`ψ_{Z0}` がそのまま被る。 -/
theorem collapse_zero_ZO (j : Nat) :
    Trans.Dict.collapse 0 (mulNat ZO (j+1)) = psi (Z zero) (mulNat ZO (j+1)) := by
  have hw : Trans.Dict.wcnf (Trans.Dict.reg 1) (toList (mulNat ZO (j+1))) = ([(ZO, ofNat (j+1))], zero) := by
    rw [toList_mulZO (j+1)]; exact wcnf_ZO j
  simp only [Trans.Dict.collapse, hw, List.foldl_cons, List.foldl_nil,
    show le (Trans.Dict.reg 1) ZO = true from rfl]
  show omegaNF (plus (Trans.Dict.reg 0) (plus (psi (Trans.Dict.reg 1)
    (Trans.Dict.sub1 (Trans.Dict.mulL (Trans.Dict.mulL (Trans.Dict.reg 1) (Trans.Dict.subAP (Trans.Dict.reg 1) ZO)) (ofNat (j+1))))) zero)) = _
  rw [show (Trans.Dict.mulL (Trans.Dict.reg 1) (Trans.Dict.subAP (Trans.Dict.reg 1) ZO)) = ZO from rfl, mulL_ZO j,
      show Trans.Dict.sub1 (mulNat ZO (j+1)) = mulNat ZO (j+1) from by
        show (match toList (mulNat ZO (j+1)) with
              | [] => zero
              | p :: rest => if p == TM.Term.one then ofList rest else mulNat ZO (j+1)) = _
        rw [toList_mulZO (j+1), List.replicate_succ]
        show (if (ZO == TM.Term.one) = true then ofList (List.replicate j ZO)
              else mulNat ZO (j+1)) = _
        rw [show ((ZO : Term) == TM.Term.one) = false from rfl]
        rfl]
  rfl

theorem dict_rep2 : ∀ k, Trans.Dict.dict (rep2 (k+1)) = mulNat ZO (k+1)
  | 0 => rfl
  | k+1 => by
    show plus (Trans.Dict.dict (Trans.Dict.BT.D 2 .zero)) (Trans.Dict.dict (rep2 (k+1))) = _
    rw [dict_rep2 k, show Trans.Dict.dict (Trans.Dict.BT.D 2 Trans.Dict.BT.zero) = ZO from rfl]
    show plus ZO (mulNat ZO (k+1)) = _
    unfold plus
    rw [toList_mulZO (k+1), List.replicate_succ]
    show ofList ((toList ZO).filter (fun a => le ZO a) ++ (ZO :: List.replicate k ZO)) = _
    rw [show toList ZO = [ZO] from rfl]
    simp only [List.filter_cons, show le ZO ZO = true from rfl, List.filter_nil, if_true]
    rw [List.singleton_append, ← List.replicate_succ, ← List.replicate_succ]
    rfl

/-- **項の側 (G2)。** `cofT (φ̄(0,Ω₂)) = ω` なので `ψ` の節は対角化ではなく素通りになり、
    中は G1 と同じ `ω^{c+1}[n] = ω^c·n` の規則になる。 -/
theorem fsN_t2 (k : Nat) : fsN t2 (k+1) = psi (Z zero) (mulNat ZO (k+1)) := by
  show fsN (psi (Z zero) (phi zero (Z TM.Term.one))) (k+1) = _
  rw [fsN]
  simp only [show kindT (phi zero (Z TM.Term.one)) = KindT.isLim from rfl,
    show cofT (phi zero (Z TM.Term.one)) = TM.Term.omega from rfl,
    show ((TM.Term.omega : Term) == TM.Term.omega) = true from decide_eq_true rfl, if_true]
  show psi (Z zero) (fsN (phi zero (Z TM.Term.one)) (k+1)) = _
  rw [show fsN (phi zero (Z TM.Term.one)) (k+1) = mulNat (omegaNF (Z TM.Term.one)) (k+1) from by
    rw [fsN]; rfl]
  rfl

/-- **リンク 3 (G2)。証明済み。** -/
theorem dict_L2BT (n : Nat) : Trans.Dict.dict (L2BT (n+1)) = fsN t2 (n+1) := by
  show Trans.Dict.collapse 0 (Trans.Dict.dict (rep2 (n+1))) = _
  rw [dict_rep2 n, collapse_zero_ZO n, fsN_t2 n]

#guard (List.range 6).all fun n => Trans.Dict.dict (L2BT (n+1)) == fsN t2 (n+1)

theorem le_psi_one (X : Term) : le (psi (Z zero) X) TM.Term.one = false := by
  show ((psi (Z zero) X == TM.Term.one) || lt (psi (Z zero) X) TM.Term.one) = false
  rw [show ((psi (Z zero) X : Term) == TM.Term.one) = false from rfl]
  simp only [Bool.false_or]
  show TM.Term.ltF (TM.Term.fuelOf (psi (Z zero) X) TM.Term.one)
    (psi (Z zero) X) TM.Term.one = false
  cases h : TM.Term.fuelOf (psi (Z zero) X) TM.Term.one with
  | zero => rfl
  | succ g =>
    show (if ((psi (Z zero) X : Term) == TM.Term.one) = true then false
          else ((psi (Z zero) X : Term) == zero) || ((psi (Z zero) X : Term) == zero)
            || TM.Term.ltF g (psi (Z zero) X) zero || TM.Term.ltF g (psi (Z zero) X) zero) = false
    rw [show ((psi (Z zero) X : Term) == TM.Term.one) = false from rfl]
    simp only [Bool.false_eq_true, if_false,
      show ((psi (Z zero) X : Term) == zero) = false from rfl, Bool.false_or,
      Rows.ProofsB.ltF_lt_zero g (psi (Z zero) X), Bool.or_false]

/-- **行の主張 (G2)。証明済み。** -/
theorem oR_M2 (n : Nat) : Trans.oR (BMS.expand M2 n) = some (fsN t2 (n+1)) := by
  show (if (BMS.expand M2 n).isEmpty then some TM.Term.zero
        else ((Trans.Recal.ofMatrix (BMS.expand M2 n)).map Trans.Recal.transPort).map
          (fun t => plus TM.Term.one (Trans.Dict.dict t))) = _
  rw [show (BMS.expand M2 n).isEmpty = false from by
        rw [expand_M2 n]; cases n <;> rfl]
  simp only [Bool.false_eq_true, if_false, ofMatrix_M2 n, Option.map_some]
  rw [transPort_L2 (n+1), dict_L2BT n, fsN_t2 n]
  show some (plus TM.Term.one (psi (Z zero) (mulNat ZO (n+1)))) = _
  rw [show plus TM.Term.one (psi (Z zero) (mulNat ZO (n+1)))
        = psi (Z zero) (mulNat ZO (n+1)) from by
    show ofList ((toList TM.Term.one).filter (fun a => le (psi (Z zero) (mulNat ZO (n+1))) a)
      ++ [psi (Z zero) (mulNat ZO (n+1))]) = _
    rw [show toList TM.Term.one = [TM.Term.one] from rfl]
    simp only [List.filter_cons, le_psi_one (mulNat ZO (n+1)), Bool.false_eq_true, if_false,
      List.filter_nil]
    rfl]

#guard (List.range 6).all fun n => Trans.oR (BMS.expand M2 n) == some (fsN t2 (n+1))

-- **G1 と違うところ**
#guard Trans.Recal.trMax (L2 0) == 1 && Trans.Recal.trMax (L2 1) == 2
  && Trans.Recal.trMax (L2 5) == 2
#guard (List.range 5).all fun m =>
  let M := L2 (m+2)
  Trans.Recal.transTypeMain M (Trans.Recal.fpar M 0 (Trans.Recal.lenI M - 1) 0)
    (Trans.Recal.lenI M - 1) == 5
-- 主枝の材料 (測定)
#guard (List.range 5).all fun m =>
  Trans.Recal.brF (L2 (m+1)) == List.replicate m [((2:Int),(2:Int))]
#guard (List.range 5).all fun m =>
  Trans.Recal.joints (L2 (m+1)) == List.replicate m (1 : Int)
#guard (List.range 5).all fun m => Trans.Recal.trMax (L2 (m+1)) == 2
#guard (List.range 5).all fun m => Trans.Recal.redFuel (L2 (m+1)) == 4*m + 60

-- 型 5 の一段: `c1 = t1 = L2BT (m-1)` から `mkC2` が `D 2 0` を 1 つ足して `L2BT m`
#guard (List.range 5).all fun m =>
  Trans.Recal.mkC2 (L2 (m+2)) 1 ((m : Int) + 3) 5 (L2BT (m+1)) == L2BT (m+2)

end G2

end Selected
end Rows
