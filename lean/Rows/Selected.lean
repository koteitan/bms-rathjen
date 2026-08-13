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

/-- 先方の値 ([diff.md](../../diff.md) 族 1)。末尾だけが当方と違う。 -/
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
def e0 : Term := phi (phi zero zero) zero

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


theorem fsN_e0 (m : Nat) : fsN e0 m = iterT zero m := by
  show fsN (phi (phi zero zero) zero) m = _
  rw [fsN]
  show TM.Term.iterPhiAt zero zero m = iterT zero m
  exact iterPhiAt_zero m

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
