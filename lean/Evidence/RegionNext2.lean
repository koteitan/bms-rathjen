import Evidence.Region
import Rows.TM
import Rows.Ladder
import Trans.DictInv

/-
Evidence/RegionNext2.lean — THE REGION, ITS VALUE, AND THE LIMIT CLAUSES

`Evidence/RegionNext.lean` closed the port: `transPort (psM (matB t 0)) = bVal t` and the
same for the marks (§60).  That part is settled and does not change, so it lives in its own
module and is compiled once.

This file is everything after it — BMS standardness on the index side (§61), the region and
its closure (§62), the value and `Hsucc` (§63-§68), `Hlim` and its refutation (§69), the
level-one sub-region that repairs it (§70), and the gates row 326 still waits on.
-/

import Evidence.RegionNext

namespace Evidence.Region

open BMS

/-! ## §61 BMS STANDARDNESS ON THE INDEX SIDE, AND THE FIRST TWO SUPPLIES

§60 closed the port: `transPort (psM (matB t 0)) = bVal t`.  §61 measures what the region
must be, and hands `certIn_region` the two supplies that do not need the limit clause.

THE PROBLEM §60 LEFT.  The generalised region is `nfB` — the Trans-side reduced form — and
on it `Hlim`'s clause `lt (value (fsB t n)) (value t)` is FALSE.  The three smallest
failures are `(0,0)(1,0)(2,1)(1,1)`, `(0,0)(1,0)(2,0)(3,1)(2,1)` and
`(0,0)(1,1)(2,1)(3,2)(2,2)`, and all three are NON-STANDARD as Bashicu matrices: no
expansion path from `(0,0)` reaches them.  `nfB` is strictly weaker than BMS standardness.

WHAT THIS SECTION FINDS.  A decidable structural predicate `stdB : B → Bool` that agrees
with the C reference implementation `~/proofs/yaBMS/c/bms -s` on **236 422 matrices**,
with zero mismatches in either direction:

    popNFB 3 6      670   (verdicts frozen verbatim below, as a 670-character string)
    enumB   3 6  16 332   1105 standard
    enumB   4 5   5 101    250 standard
    enumB   3 7 153 421   5507 standard
    enumB   4 6  60 898   1263 standard

and, on a population of a completely different shape — the depth-three expansion closure of
the table's 52 width-two rows, `popB`, 877 matrices reaching **47 columns**, every one of
which the reference calls standard — `stdB` accepts all 877.  So the agreement is not an
artefact of small enumerations.

`stdB` is `nfB` (a node's level is at most its parent's plus one) conjoined with two
conditions, and both are the classical normal-form conditions for a Buchholz-style ψ:

  CNF   the summands of every argument — and of the whole term — descend, `nonIncr`;
  BNF   for a node of level `v` with argument `a`: scanning `a` and descending only
        through nodes of level `≥ v`, every node of level EXACTLY `v` has an argument
        strictly below `a`.  That is `visOK`, and the comparison is `cmpS`, the ordinary
        lexicographic-from-the-left order on descending sums.

THE ONE SURPRISE, worth recording because the first attempt failed on it: Buchholz's own
condition constrains `ψ_u(b)` for EVERY `u ≥ v`, not only `u = v`.  That version is sound
(no false positives) but rejects 75 of the 670 — every index containing the diagonal
`(0,0)(1,1)(2,2)`, which IS standard.  Constraining only `u = v` is exact.  So the pair
sequence system's standard form is NOT Buchholz's normal form; it is the weaker one.

WHAT `stdB` BUYS, measured:

  (i)   `stdB t → stdB (fsB t n)` — closure under the fundamental sequence.  Zero
        counterexamples over all five populations above, and to three iterated steps.
  (ii)  row 326's index `(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)` is `stdB`, and so is every
        member of its fundamental sequence.
  (iii) **the failing clause is restored.**  Over `popNFB 3 6`, 13 limit indices violate
        `lt (value (fsB t n)) (value t)`; **none of the 13 is `stdB`**, and on the 235
        `stdB` indices the clause holds to `n ≤ 8`, together with strict increase.

WHAT IS PROVED HERE.  `kind_matB` (§4) and `oR_matB` (§5) — the latter carries §60 through
`oRB` and `dict` to the value the table actually holds — and `hzero_supply` plus the INDEX
half of `Hsucc` (§6).

WHAT IS **NOT** CLAIMED.  `stdB t = true` is not proved equivalent to `BMS.Standard`; the
evidence is the 236 422-matrix agreement with the reference implementation, nothing more.
(i) is measured, not proved, so `Hclosed` for this region is still owed.  The VALUE half of
`Hsucc` — `v = plus u one`, `inT v`, `inT u`, `lt u v` — is measured and NOT proved: it
needs `plus`-algebra and an `inT (dict ·)` theorem that this repository does not have.
`Hlim` is not touched. -/

section
open Trans.Recal
open Trans.Dict (BT)

/-! ### 1. 降べきの和の比較

`B` は「和を左に積む」形なので、比較には成分を左から右へ並べ直す必要がある。
`toLA` は蓄積器つきの並べ直し、`cmpS` はその上の辞書式比較 (短い方が小さい)。 -/

/-- 和の成分の重み。停止性の測度。 -/
def sizeL : List (Nat × B) → Nat
  | [] => 0
  | p :: r => sizeB p.2 + 1 + sizeL r

/-- 和の成分を左から右へ (蓄積器つき)。 -/
def toLA : B → List (Nat × B) → List (Nat × B)
  | .nil, acc => acc
  | .nd v r a, acc => toLA r ((v, a) :: acc)

/-- 和の成分を左から右へ。 -/
def toL (t : B) : List (Nat × B) := toLA t []

theorem sizeL_toLA : ∀ (t : B) (acc : List (Nat × B)),
    sizeL (toLA t acc) = sizeB t + sizeL acc := by
  intro t
  induction t with
  | nil => intro acc; show sizeL acc = 0 + sizeL acc; omega
  | nd v r a ihr _ =>
    intro acc
    show sizeL (toLA r ((v, a) :: acc)) = sizeB r + 1 + sizeB a + sizeL acc
    rw [ihr ((v, a) :: acc)]
    show sizeB r + (sizeB a + 1 + sizeL acc) = _
    omega

/-- 成分の重みの合計は節の個数。 -/
theorem sizeL_toL (t : B) : sizeL (toL t) = sizeB t := by
  rw [toL, sizeL_toLA t []]
  rfl

theorem toLA_append : ∀ (t : B) (acc : List (Nat × B)), toLA t acc = toL t ++ acc := by
  intro t
  induction t with
  | nil => intro acc; rfl
  | nd v r a ihr _ =>
    intro acc
    show toLA r ((v, a) :: acc) = toL (B.nd v r a) ++ acc
    rw [ihr ((v, a) :: acc)]
    show toL r ++ ((v, a) :: acc) = (toLA r [(v, a)]) ++ acc
    rw [ihr [(v, a)]]
    rw [List.append_assoc]
    rfl

/-- 節を 1 つ足すと成分が右に 1 つ増える。 -/
theorem toL_nd (v : Nat) (r a : B) : toL (.nd v r a) = toL r ++ [(v, a)] := by
  show toLA r [(v, a)] = _
  rw [toLA_append r [(v, a)]]

/-- **和の比較。** 左から辞書式、成分が尽きた方が小さい。降べきの和の上でだけ意味を持つ。 -/
def cmpS : List (Nat × B) → List (Nat × B) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | (u, a) :: xs, (w, b) :: ys =>
      if u < w then .lt
      else if w < u then .gt
      else
        match cmpS (toL a) (toL b) with
        | .eq => cmpS xs ys
        | o => o
termination_by x y => sizeL x + sizeL y
decreasing_by
  · rw [sizeL_toL, sizeL_toL]
    show _ < (sizeB a + 1 + sizeL xs) + (sizeB b + 1 + sizeL ys)
    omega
  · show sizeL xs + sizeL ys < (sizeB a + 1 + sizeL xs) + (sizeB b + 1 + sizeL ys)
    omega

/-- 1 つの節どうしの比較。 -/
def cmpN (u : Nat) (a : B) (w : Nat) (b : B) : Ordering := cmpS [(u, a)] [(w, b)]

/-! ### 2. `stdB`

三つの条件の連言。`nfB` は §19 のもの、`nonIncr` は和が降べきであること、`visOK` は
「段 `v` の節の引数の中に現れる段 `v` の節は、その引数より真に小さい引数を持つ」。 -/

/-- 先頭の 2 つが降べきか。 -/
def hdOK (x : Nat × B) : List (Nat × B) → Bool
  | [] => true
  | y :: _ => !(cmpN x.1 x.2 y.1 y.2 == Ordering.lt)

/-- 成分が左から右へ広義単調減少。 -/
def nonIncrL : List (Nat × B) → Bool
  | [] => true
  | x :: r => hdOK x r && nonIncrL r

/-- 和が降べき。 -/
def nonIncr (t : B) : Bool := nonIncrL (toL t)

/-- **段 `v` の節の許容条件。** 引数 `a` の中を走査し、段が `v` 未満の節で打ち切る。
    段がちょうど `v` の節は、その引数が `a` より真に小さくなければならない。 -/
def visOK (v : Nat) (a : B) : B → Bool
  | .nil => true
  | .nd u r c =>
      visOK v a r &&
      (if u < v then true
       else (if u == v then cmpS (toL c) (toL a) == Ordering.lt else true) && visOK v a c)

/-- すべての節での条件。 -/
def stdIn : B → Bool
  | .nil => true
  | .nd v r c => stdIn r && nonIncr c && visOK v c c && stdIn c

/-- **BMS 標準性の添字側の判定。** `~/proofs/yaBMS/c/bms -s` と 236 422 個で一致。 -/
def stdB (t : B) : Bool := nfB t && nonIncr t && stdIn t

/-! ### 3. 測定 (凍結)

`bms -s` の判定を Lean のリテラルとして凍結する。1 行目は `popNFB 3 6` の 670 個ぶんの
判定そのもの、以下は各母集団の標準行列の個数。すべて参照実装の出力。 -/

/-- `~/proofs/yaBMS/c/bms -s` を `popNFB 3 6` の 670 個の行列に順に当てた結果。 -/
def bmsStd670 : String :=
  "1111110111011001111101101011001110000101011100000101001011001111100010110000000001011001101110110011111011010110010001100011001000010011101100000000010110101100000100100100000000000000100001000000110110101100001010111010000101011100000111110000000000001000010100001001101110000000000000000000000000010000000000001000010000000100001110000000111101111100000000000000010100101100111100110011110000111011000000001100110011111100000000001000100000100010110000101110111000000010001011000000000000000000000000000000000000000000000000000000000000000100001000000000000101100111110001111000000000011011010110011100001010111000001010010110011111000101100000000010110011011101100111"

#guard bmsStd670.length == 670
#guard (bmsStd670.toList.filter (· == '1')).length == 235
-- **`stdB` は参照実装そのもの。**
#guard (String.join ((popNFB 3 6).map fun t => if stdB t then "1" else "0")) == bmsStd670
-- 参照実装が数えた標準行列の個数と、`stdB` が数えた個数。
#guard ((enumB 3 6).filter stdB).length == 1105
#guard ((enumB 4 5).filter stdB).length == 250
#guard ((enumB 3 7).filter stdB).length == 5507
#guard ((enumB 4 6).filter stdB).length == 1263

/-- 標準な添字の母集団。 -/
def popS (L n : Nat) : List B := (popNFB L n).filter stdB

#guard (popS 3 6).length == 235
#guard (popS 4 6).length == 250

-- (i) 基本列で閉じる。**測定のみ。**
#guard (enumB 3 6).all fun t => !(stdB t) || (List.range 6).all fun n => stdB (fsB t n)
#guard (enumB 4 5).all fun t => !(stdB t) || (List.range 6).all fun n => stdB (fsB t n)
#guard (enumB 3 7).all fun t => !(stdB t) || (List.range 4).all fun n => stdB (fsB t n)
#guard (enumB 4 6).all fun t => !(stdB t) || (List.range 4).all fun n => stdB (fsB t n)
-- 2 段、3 段でも。
#guard (popNFB 3 6).all fun t => !(stdB t) ||
  (List.range 4).all fun n => (List.range 4).all fun m => stdB (fsB (fsB t n) m)
#guard (popNFB 3 6).all fun t => !(stdB t) ||
  (List.range 3).all fun n => (List.range 3).all fun m => (List.range 3).all fun k =>
    stdB (fsB (fsB (fsB t n) m) k)

-- 表そのもの。参照実装は `popB` の 877 個と `wideRows` の 52 個をすべて標準と呼び、
-- `stdB` もすべて受け入れる。`popB` は最大 47 列で、上の列挙とは母集団の形が違う。
#guard popB.length == 877
#guard popB.all fun S => match decodeB S with | none => false | some t => stdB t
#guard wideRows.all fun M => match decodeB M with | none => false | some t => stdB t
#guard popB.all fun S => match decodeB S with
  | none => false | some t => (List.range 5).all fun n => stdB (fsB t n)

-- (ii) 326 行目の添字。
#guard (decodeB [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1]]).isSome
#guard match decodeB [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1]] with
  | none => false
  | some t => nfB t && stdB t && (List.range 6).all fun n => stdB (fsB t n)

/-- 添字の値。`oR` と同じ `1 +` の約束を持つ (空行列は 0)。 -/
def vOf : B → TM.Term
  | .nil => TM.Term.zero
  | t@(.nd _ _ _) => TM.Term.plus TM.Term.one (Trans.Dict.dict (bVal t))

/-- 添字が自分で読む種別。 -/
def kindB : B → BMS.Kind
  | .nil => .zero
  | .nd v _ .nil => if v == 0 then .succ else .lim
  | .nd _ _ _ => .lim

-- `vOf` は表の値そのもの (§5 が定理にする)。
#guard (popNFB 3 6).all fun t => Trans.Recal.oR (matB t 0) == some (vOf t)

-- (iii) **落ちていた極限の条項が戻る。** `nfB` だけでは 13 個が落ち、そのどれも `stdB` でない。
#guard ((popNFB 3 6).filter fun t => kindB t == BMS.Kind.lim &&
  !((List.range 5).all fun n => TM.Term.lt (vOf (fsB t n)) (vOf t))).length == 13
#guard ((popNFB 3 6).filter fun t => kindB t == BMS.Kind.lim && stdB t &&
  !((List.range 5).all fun n => TM.Term.lt (vOf (fsB t n)) (vOf t))).length == 0
-- 標準な添字の上では `n ≤ 8` まで成り立ち、真に増える。**測定のみ。**
#guard (popS 3 6).all fun t => !(kindB t == BMS.Kind.lim) ||
  (List.range 9).all fun n => TM.Term.lt (vOf (fsB t n)) (vOf t)
#guard (popS 4 6).all fun t => !(kindB t == BMS.Kind.lim) ||
  (List.range 6).all fun n => TM.Term.lt (vOf (fsB t n)) (vOf t)
#guard (popS 3 6).all fun t => !(kindB t == BMS.Kind.lim) ||
  (List.range 8).all fun n => TM.Term.lt (vOf (fsB t n)) (vOf (fsB t (n+1)))
#guard (popS 4 6).all fun t => !(kindB t == BMS.Kind.lim) ||
  (List.range 5).all fun n => TM.Term.lt (vOf (fsB t n)) (vOf (fsB t (n+1)))
-- 3 つの最小の反例は、どれも `stdB` でない。
#guard (decodeB [[0,0],[1,0],[2,1],[1,1]]).isSome
#guard match decodeB [[0,0],[1,0],[2,1],[1,1]] with
  | none => false | some t => nfB t && !(stdB t)
#guard match decodeB [[0,0],[1,0],[2,0],[3,1],[2,1]] with
  | none => false | some t => nfB t && !(stdB t)
#guard match decodeB [[0,0],[1,1],[2,1],[3,2],[2,2]] with
  | none => false | some t => nfB t && !(stdB t)
-- Buchholz そのものの条件 (段が `v` 以上のすべての節を縛る) は**強すぎる**。
-- 対角 `(0,0)(1,1)(2,2)` を含む 75 個を落としてしまう。その最小のもの。
#guard match decodeB [[0,0],[1,1],[2,2]] with
  | none => false | some t => stdB t
-- `Hsucc` の値の側。**測定のみ、証明されていない。**
#guard (popS 3 6).all fun t => !(kindB t == BMS.Kind.succ) ||
  (vOf t == TM.Term.plus (vOf (fsB t 0)) TM.Term.one)
#guard (popS 3 6).all fun t => !(kindB t == BMS.Kind.succ) ||
  (List.range 5).all fun n => fsB t n == fsB t 0
#guard (popS 3 6).all fun t => TM.Term.inT (vOf t)
#guard (popS 4 6).all fun t => TM.Term.inT (vOf t)
-- `CNV` は 235 個中 150 個。`certIn_region_cnv` は最上位の値にしか要らない。
#guard ((popS 3 6).filter fun t => Evidence.WF.CNV (vOf t)).length == 150
-- 値は添字を分ける。
#guard ((popS 3 6).map vOf).eraseDups.length == 235

/-! ### 4. 種別

`BMS.lnz` は列の**最後の**非零行なので、種別が後続になるのは最後の列が `[0,0]` の
ときちょうど — つまり最上位に段 0 の葉が来たとき。仮定は要らない。 -/

/-- 空でない添字の行列の最後の列。 -/
theorem matB_getLast? (a : B) (ha : a ≠ .nil) (d : Nat) :
    (matB a d).getLast? = some [d + lastDep a, lastLvl a] := by
  have h := matB_last a ha d
  calc (matB a d).getLast?
      = ((matB a d).dropLast ++ [[d + lastDep a, lastLvl a]]).getLast? := by rw [← h]
    _ = some [d + lastDep a, lastLvl a] := getLast?_append_ne _ _ (by simp)

/-- **種別は添字が決める。** 仮定は要らない。 -/
theorem kind_matB (t : B) : BMS.kind (matB t 0) = kindB t := by
  cases t with
  | nil => rfl
  | nd v r a =>
    cases a with
    | nil =>
      show (match (matB r 0 ++ ([0, v] :: matB B.nil 1)).getLast? with
        | none => BMS.Kind.zero
        | some L => match lnz L with | none => BMS.Kind.succ | some _ => BMS.Kind.lim)
        = (if v == 0 then BMS.Kind.succ else BMS.Kind.lim)
      rw [show ([0, v] :: matB B.nil 1) = [[0, v]] from rfl,
        getLast?_append_ne _ _ (by simp)]
      show (match lnz [0, v] with | none => BMS.Kind.succ | some _ => BMS.Kind.lim) = _
      rw [lnz_pair]
      cases v with
      | zero => rfl
      | succ k => rw [if_pos (by omega)]; rfl
    | nd w b c =>
      have ha : (B.nd w b c) ≠ .nil := by intro h; exact B.noConfusion h
      have hne : matB (B.nd w b c) 1 ≠ [] := by
        intro h
        have := matB_len_pos (B.nd w b c) 1 ha
        rw [h] at this
        exact absurd this (by simp)
      show (match (matB r 0 ++ ([0, v] :: matB (B.nd w b c) 1)).getLast? with
        | none => BMS.Kind.zero
        | some L => match lnz L with | none => BMS.Kind.succ | some _ => BMS.Kind.lim)
        = BMS.Kind.lim
      rw [getLast?_append_ne _ _ (by simp), List.getLast?_cons_of_ne_nil hne,
        matB_getLast? (B.nd w b c) ha 1]
      show (match lnz [1 + lastDep (B.nd w b c), lastLvl (B.nd w b c)] with
        | none => BMS.Kind.succ | some _ => BMS.Kind.lim) = _
      rw [lnz_pair]
      cases hl : lastLvl (B.nd w b c) with
      | zero => rw [if_neg (by omega), if_pos (by omega)]
      | succ _ => rw [if_pos (by omega)]

/-- 種別 0 の添字は `nil` だけ。 -/
theorem kindB_nd_nil (v : Nat) (r : B) :
    kindB (.nd v r .nil) = (if v == 0 then BMS.Kind.succ else BMS.Kind.lim) := rfl

theorem kindB_zero : ∀ (t : B), kindB t = BMS.Kind.zero → t = .nil := by
  intro t
  cases t with
  | nil => intro _; rfl
  | nd v r a =>
    cases a with
    | nil =>
      intro h
      rw [kindB_nd_nil] at h
      cases hv : (v == 0) with
      | true => rw [hv] at h; exact BMS.Kind.noConfusion h
      | false => rw [hv] at h; exact BMS.Kind.noConfusion h
    | nd w b c => intro h; exact BMS.Kind.noConfusion h

/-- 種別後続の添字は `nd 0 r nil`。 -/
theorem kindB_succ : ∀ (t : B), kindB t = BMS.Kind.succ → ∃ r, t = .nd 0 r .nil := by
  intro t
  cases t with
  | nil => intro h; exact BMS.Kind.noConfusion h
  | nd v r a =>
    cases a with
    | nil =>
      intro h
      rw [kindB_nd_nil] at h
      cases hv : (v == 0) with
      | true =>
        refine ⟨r, ?_⟩
        rw [show v = 0 from (beq_iff_eq (a := v) (b := 0)).mp hv]
      | false =>
        rw [hv] at h
        exact BMS.Kind.noConfusion h
    | nd w b c => intro h; exact BMS.Kind.noConfusion h

/-! ### 5. `oR`

§60 の `transPort_bVal` を `oRB` と `dict` を通して表の値まで運ぶ。`oR` は空行列だけを
特別扱いして `0` を返すので、添字側の値 `vOf` も同じ特別扱いを持つ。 -/

/-- **`oR` は `bVal` の辞書引きに `1 +` を付けたもの。** -/
theorem oR_matB (t : B) (hnf : nfB t = true) (hne : t ≠ .nil) :
    Trans.Recal.oR (matB t 0)
      = some (TM.Term.plus TM.Term.one (Trans.Dict.dict (bVal t))) := by
  have h1 : (matB t 0).isEmpty = false := by
    have hp := matB_len_pos t 0 hne
    cases hm : matB t 0 with
    | nil => rw [hm] at hp; exact absurd hp (by simp)
    | cons c cs => rfl
  show (if (matB t 0).isEmpty = true then some TM.Term.zero
        else (Trans.Recal.oRB (matB t 0)).map
          (fun x => TM.Term.plus TM.Term.one (Trans.Dict.dict x))) = _
  rw [if_neg (by rw [h1]; exact fun h => Bool.noConfusion h)]
  show ((ofMatrix (matB t 0)).map transPort).map
      (fun x => TM.Term.plus TM.Term.one (Trans.Dict.dict x)) = _
  rw [ofMatrix_matB t 0 hne]
  show some (TM.Term.plus TM.Term.one (Trans.Dict.dict (transPort (psM (matB t 0))))) = _
  rw [transPort_bVal t hnf hne]

/-- **`vOf` は表の値。** 空添字も込めて 1 本の等式。 -/
theorem oR_vOf (t : B) (hnf : nfB t = true) : Trans.Recal.oR (matB t 0) = some (vOf t) := by
  cases t with
  | nil => rfl
  | nd v r a =>
    have hne : (B.nd v r a) ≠ .nil := by intro h; exact B.noConfusion h
    rw [oR_matB (B.nd v r a) hnf hne]
    rfl

/-! ### 6. 領域と、最初の 2 つの供給

`RegS`/`ValS` は `certIn_region` の 2 つの引数。`Evidence/RegionV.lean` §12 の形をそのまま
一般化した添字に載せ替えたもの。`Hzero` は定理、`Hsucc` は**添字の側だけ**が定理。 -/

/-- 領域: 標準な添字の行列。 -/
def RegS (S : BMS.Matrix) : Prop := ∃ t : B, stdB t = true ∧ S = matB t 0

/-- その上の値付け。 -/
def ValS (S : BMS.Matrix) (v : TM.Term) : Prop :=
  ∃ t : B, stdB t = true ∧ S = matB t 0 ∧ v = vOf t

theorem stdB_nil : stdB .nil = true := rfl

theorem nfB_of_stdB (t : B) (h : stdB t = true) : nfB t = true :=
  ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).1).1

theorem nonIncr_of_stdB (t : B) (h : stdB t = true) : nonIncr t = true :=
  ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).1).2

theorem stdIn_of_stdB (t : B) (h : stdB t = true) : stdIn t = true :=
  ((Bool.and_eq_true _ _).mp h).2

/-- 成分を 1 つ右に足しても、左側の降べきは残る。 -/
theorem nonIncrL_cons (x : Nat × B) (r : List (Nat × B)) :
    nonIncrL (x :: r) = (hdOK x r && nonIncrL r) := rfl

theorem nonIncrL_dropLast : ∀ (l : List (Nat × B)) (x : Nat × B),
    nonIncrL (l ++ [x]) = true → nonIncrL l = true := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons a l ih =>
    intro x h
    rw [show (a :: l) ++ [x] = a :: (l ++ [x]) from rfl, nonIncrL_cons] at h
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
    rw [nonIncrL_cons, ih x h2, Bool.and_true]
    cases l with
    | nil => rfl
    | cons b l' => exact h1

/-- **`stdB` は最後の節を落としても残る (段 0 の葉のとき)。** -/
theorem stdB_pred (r : B) (h : stdB (.nd 0 r .nil) = true) : stdB r = true := by
  have hnf : nfB (.nd 0 r .nil) = true := nfB_of_stdB _ h
  have hni : nonIncr (.nd 0 r .nil) = true := nonIncr_of_stdB _ h
  have hin : stdIn (.nd 0 r .nil) = true := stdIn_of_stdB _ h
  have h1 : nfB r = true := ((nfLe_nd_iff 0 0 r .nil).mp hnf).2.1
  have h2 : nonIncr r = true := by
    have hni' : nonIncrL (toL (B.nd 0 r .nil)) = true := hni
    rw [toL_nd 0 r .nil] at hni'
    exact nonIncrL_dropLast (toL r) (0, .nil) hni'
  have h3 : stdIn r = true := by
    have : (stdIn r && nonIncr .nil && visOK 0 .nil .nil && stdIn .nil) = true := hin
    exact ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp
      ((Bool.and_eq_true _ _).mp this).1).1).1
  show (nfB r && nonIncr r && stdIn r) = true
  rw [h1, h2, h3]
  rfl

/-- **`Hzero`。** 種別 0 の行列は添字 `nil` から来て、値は `0`。 -/
theorem hzeroS_supply : ∀ (S : BMS.Matrix) (v : TM.Term), RegS S → ValS S v →
    BMS.kind S = BMS.Kind.zero → v = TM.Term.zero := by
  rintro S v _ ⟨t, hstd, rfl, rfl⟩ hk
  rw [kind_matB t] at hk
  rw [kindB_zero t hk]
  rfl

/-- **`Hsucc` の添字の側。** 種別後続の行列は `nd 0 r nil` から来て、その展開は `n` に
    よらず `matB r 0`、値は `vOf r`。値の等式 `v = plus (vOf r) one` は**測定のみ**。 -/
theorem hsuccS_index : ∀ (S : BMS.Matrix) (v : TM.Term), RegS S → ValS S v →
    BMS.kind S = BMS.Kind.succ →
    ∃ r : B, v = vOf (.nd 0 r .nil) ∧ stdB r = true
             ∧ ∀ n, BMS.expand S n = matB r 0 ∧ ValS (BMS.expand S n) (vOf r) := by
  rintro S v _ ⟨t, hstd, rfl, rfl⟩ hk
  rw [kind_matB t] at hk
  obtain ⟨r, rfl⟩ := kindB_succ t hk
  have hr : stdB r = true := stdB_pred r hstd
  have hnf : nfB (B.nd 0 r .nil) = true := nfB_of_stdB _ hstd
  have htop : topOKB (B.nd 0 r .nil) = true := topOKB_of_nfB _ hnf
  have hexp : ∀ n, BMS.expand (matB (B.nd 0 r .nil) 0) n = matB r 0 := by
    intro n
    show (BMS.expand? (matB (B.nd 0 r .nil) 0) n).getD [] = _
    rw [expand_matB (B.nd 0 r .nil) htop (by intro h; exact B.noConfusion h) n]
    rfl
  exact ⟨r, rfl, hr, fun n => ⟨hexp n, ⟨r, hr, (hexp n).symm ▸ rfl, rfl⟩⟩⟩

/-! ### 公理の確認 -/

end

/-! ## §62 `stdB` IS CLOSED UNDER THE FUNDAMENTAL SEQUENCE

§61 found `stdB` — `nfB && nonIncr && stdIn` — measured that it agrees with the C reference
implementation on 236 422 matrices, and left its closure under `fsB` as a measurement.  §62
proves it, and with it `Hclosed` for the narrowed region:

    stdB_fsB        stdB t → stdB (fsB t n)
    hclosedS_supply ∀ S, RegS S → ∀ n, RegS (BMS.expand S n)

WHY IT IS NOT A WALK OVER THE OPERATORS.  `nfB` is LOCAL and §19 pushed it through `appB`,
`plugB`, `repNode`, `repB`, `iterD`, `rwB` one lemma each.  `nonIncr` and `stdIn` are not:
`nonIncr` compares a node's argument against its neighbour and `visOK` compares it against the
WHOLE sum it sits in.  So the first thing §62 needs is an ORDER on `cmpS`, and there was none.

    §62.1  cmpS_refl / cmpS_eq_imp / cmpS_swap / cmpS_trans   `cmpS` is a linear order
    §62.2  cmpS_lt_append / cmpS_append_left                  a common prefix is inert
           cmpS_ctx        a term smaller than the prefix cannot see past it
           cmpS_split      `x < p ++ q` splits into three exhaustive shapes — the workhorse
           cmpS_lt_snoc_zero  `(0,0)` is the least component, so it can be dropped
    §62.4  visOK_iff       `visOK v a s` is `∀ c ∈ vArgs v s, c < a`, and `vArgs v s` is a
                           list of SUBTERMS (`vArgs_size`), which is what makes the size
                           bounds in the transfers usable

THE TWO TRANSFERS.  Every step of the closure is one of exactly two shapes, and both have to
be proved for `repB` (§62.6–§62.7) and again for `plugB` (§62.8):

    the reference STAYS PUT   `visOK v ref a → visOK v ref (op a)`.  Every argument the
                              operator creates is BELOW the one it replaces (`repB_lt`,
                              `plugB_lt`, `GG_lt`), so transitivity alone does it.
    the reference MOVES       a subterm of `op a` that was below `a` is below `op a`
                              (`C1_repB`, `C1_GG`).  `cmpS_split` leaves three cases and the
                              size bound `sizeB x < sizeB (op a)` kills two of them.

`visOK_self_repB` / `visOK_self_GG` / `visOK_self_rwB` close the loop: the self-referential
`visOK v (op a) (op a)` is the first transfer followed by the second, applied to each element
of `vArgs`.

THE ONE PLACE THE NAIVE INDUCTION FAILS, and it is worth recording because the first attempt
died on it.  `C1_repB`'s statement is FALSE for `plugB`: with `a = ψ₁(0)`, `x = ψ₀(ψ₁(0))`,
`n = 2` one has `x < a`, `sizeB x < sizeB (plugB a (iterD 0 a 2))` and yet
`x > plugB a (iterD 0 a 2)` (frozen as a `#guard` in §62.11).  What is missing is
`visOK (w-1) x x`, and — this is the point — it does NOT propagate as the induction descends
`a`'s last spine, because that descent passes through nodes of level `≥ w > w-1`.  The fix is
to hold the REFERENCE fixed at the top argument `a₀` while the scan descends
(`C1_plugB_cons`'s `∀ z' ∈ vArgs v' x, z' < a₀`), and to run an OUTER induction on the
nesting depth of `iterD`, whose base case is killed by the size bound alone
(`C1_plugB_nil`).  `lowAnc_lvl` is the only place `nfB` is used: it says the nearest ancestor
of lower level has level EXACTLY `w-1`, which is what makes `u < w → u ≤ v'` available at the
bottom of the descent.

WHAT IS **NOT** CLAIMED.  `stdB t = true` is still not proved equivalent to `BMS.Standard`;
§61's 236 422-matrix agreement with the reference is the only evidence for that, and §62 adds
none.  `Hlim` and the VALUE half of `Hsucc` are untouched.  Task 3 of the brief —
`dict (bplus x y) = plus (dict x) (dict y)` — is measured (§62.11) and NOT proved: it needs
`plus` to be associative, and the repository's only associativity, `Evidence.CNVOps.plus_assoc`,
requires `CNV`, which only 150 of the 235 standard values of `popNFB 3 6` satisfy.  The general
route needs a `plus_assoc` built on `Evidence.WF.lt_trans_inT` / `lt_trichotomy_inT` plus an
`inT (dict ·)` theorem, and neither exists. -/

section
open Trans.Recal
open Trans.Dict (BT)

/-! ### §62.1 `cmpS` の式と、それが線形順序であること -/

theorem cmpS_nil_nil : cmpS [] [] = .eq := by rw [cmpS]
theorem cmpS_nil_cons (y : Nat × B) (ys : List (Nat × B)) : cmpS [] (y :: ys) = .lt := by
  rw [cmpS]
theorem cmpS_cons_nil (x : Nat × B) (xs : List (Nat × B)) : cmpS (x :: xs) [] = .gt := by
  rw [cmpS]
theorem cmpS_cons (u : Nat) (a : B) (xs : List (Nat × B)) (w : Nat) (b : B)
    (ys : List (Nat × B)) :
    cmpS ((u, a) :: xs) ((w, b) :: ys)
      = (if u < w then .lt else if w < u then .gt else
          match cmpS (toL a) (toL b) with | .eq => cmpS xs ys | o => o) := by
  rw [cmpS]

/-! #### リストの補題と `toL` の単射性 -/

theorem app_sing_ne_nil {α : Type} : ∀ (l : List α) (x : α), l ++ [x] ≠ []
  | [], x => List.cons_ne_nil x []
  | a :: l', x => List.cons_ne_nil a (l' ++ [x])

theorem app_sing_inj {α : Type} : ∀ (l1 l2 : List α) (x y : α),
    l1 ++ [x] = l2 ++ [y] → l1 = l2 ∧ x = y
  | [], [], x, y, h => ⟨rfl, by injection h⟩
  | [], b :: l2', x, y, h => by
      exfalso
      injection h with _ h2
      exact app_sing_ne_nil l2' y h2.symm
  | a :: l1', [], x, y, h => by
      exfalso
      injection h with _ h2
      exact app_sing_ne_nil l1' x h2
  | a :: l1', b :: l2', x, y, h => by
      injection h with h1 h2
      obtain ⟨h3, h4⟩ := app_sing_inj l1' l2' x y h2
      exact ⟨by rw [h1, h3], h4⟩

theorem toL_nil : toL (.nil : B) = [] := rfl

theorem toL_ne_nil (v : Nat) (r a : B) : toL (.nd v r a) ≠ [] := by
  rw [toL_nd]
  exact app_sing_ne_nil (toL r) (v, a)

/-- `toL` は単射。 -/
theorem toL_inj : ∀ (s t : B), toL s = toL t → s = t := by
  intro s
  induction s with
  | nil =>
    intro t h
    cases t with
    | nil => rfl
    | nd w u b => exact absurd h.symm (toL_ne_nil w u b)
  | nd v r a ihr _ =>
    intro t h
    cases t with
    | nil => exact absurd h (toL_ne_nil v r a)
    | nd w u b =>
      rw [toL_nd, toL_nd] at h
      obtain ⟨h1, h2⟩ := app_sing_inj _ _ _ _ h
      injection h2 with h3 h4
      rw [ihr u h1, h3, h4]


/-! #### 反射・等号・推移 -/

theorem sizeL_cons (u : Nat) (a : B) (xs : List (Nat × B)) :
    sizeL ((u, a) :: xs) = sizeB a + 1 + sizeL xs := rfl

theorem cmpS_refl : ∀ (x : List (Nat × B)), cmpS x x = .eq
  | [] => cmpS_nil_nil
  | (u, a) :: xs => by
      rw [cmpS_cons, if_neg (Nat.lt_irrefl u), if_neg (Nat.lt_irrefl u),
        cmpS_refl (toL a)]
      exact cmpS_refl xs
termination_by x => sizeL x
decreasing_by
  · rw [sizeL_toL, sizeL_cons]; omega
  · rw [sizeL_cons]; omega

/-- `eq` は等しさ。 -/
theorem cmpS_eq_imp : ∀ (x y : List (Nat × B)), cmpS x y = .eq → x = y
  | [], [], _ => rfl
  | [], y :: ys, h => by rw [cmpS_nil_cons] at h; exact Ordering.noConfusion h
  | x :: xs, [], h => by rw [cmpS_cons_nil] at h; exact Ordering.noConfusion h
  | (u, a) :: xs, (w, b) :: ys, h => by
      rw [cmpS_cons] at h
      have huw : u = w := by
        by_cases h1 : u < w
        · rw [if_pos h1] at h; exact absurd h (by intro hc; exact Ordering.noConfusion hc)
        · rw [if_neg h1] at h
          by_cases h2 : w < u
          · rw [if_pos h2] at h; exact absurd h (by intro hc; exact Ordering.noConfusion hc)
          · omega
      subst huw
      rw [if_neg (Nat.lt_irrefl u), if_neg (Nat.lt_irrefl u)] at h
      cases hab : cmpS (toL a) (toL b) with
      | lt => rw [hab] at h; exact absurd h (by intro hc; exact Ordering.noConfusion hc)
      | gt => rw [hab] at h; exact absurd h (by intro hc; exact Ordering.noConfusion hc)
      | eq =>
        rw [hab] at h
        have hb : a = b := toL_inj a b (cmpS_eq_imp (toL a) (toL b) hab)
        have hx : xs = ys := cmpS_eq_imp xs ys h
        rw [hb, hx]
termination_by x y => sizeL x + sizeL y
decreasing_by
  · rw [sizeL_toL, sizeL_toL, sizeL_cons, sizeL_cons]; omega
  · rw [sizeL_cons, sizeL_cons]; omega

/-- 推移律。 -/
theorem cmpS_trans : ∀ (x y z : List (Nat × B)),
    cmpS x y = .lt → cmpS y z = .lt → cmpS x z = .lt
  | [], [], _, h1, _ => by rw [cmpS_nil_nil] at h1; exact Ordering.noConfusion h1
  | [], _ :: _, [], _, h2 => by rw [cmpS_cons_nil] at h2; exact Ordering.noConfusion h2
  | [], _ :: _, _ :: _, _, _ => by rw [cmpS_nil_cons]
  | _ :: _, [], _, h1, _ => by rw [cmpS_cons_nil] at h1; exact Ordering.noConfusion h1
  | _ :: _, _ :: _, [], _, h2 => by rw [cmpS_cons_nil] at h2; exact Ordering.noConfusion h2
  | (u, a) :: xs, (w, b) :: ys, (p, c) :: zs, h1, h2 => by
      rw [cmpS_cons] at h1
      rw [cmpS_cons] at h2
      rw [cmpS_cons]
      have hpw : ¬ (p < w) := by
        intro hc
        rw [if_neg (by omega), if_pos hc] at h2
        exact Ordering.noConfusion h2
      by_cases huw : u < w
      · rw [if_pos (show u < p by omega)]
      · rw [if_neg huw] at h1
        have hwu : ¬ (w < u) := by
          intro hc
          rw [if_pos hc] at h1
          exact Ordering.noConfusion h1
        rw [if_neg hwu] at h1
        have hu : u = w := by omega
        subst hu
        by_cases hup : u < p
        · rw [if_pos hup]
        · rw [if_neg hup] at h2
          have hu2 : u = p := by omega
          subst hu2
          rw [if_neg (show ¬ (u < u) by omega)] at h2
          rw [if_neg (show ¬ (u < u) by omega), if_neg (show ¬ (u < u) by omega)]
          cases hab : cmpS (toL a) (toL b) with
          | gt => rw [hab] at h1; exact Ordering.noConfusion h1
          | lt =>
            cases hbc : cmpS (toL b) (toL c) with
            | gt =>
              rw [hbc] at h2
              exact Ordering.noConfusion (show Ordering.gt = Ordering.lt from h2)
            | lt =>
              rw [cmpS_trans (toL a) (toL b) (toL c) hab hbc]
            | eq =>
              have : b = c := toL_inj b c (cmpS_eq_imp (toL b) (toL c) hbc)
              subst this
              rw [hab]
          | eq =>
            have hbe : a = b := toL_inj a b (cmpS_eq_imp (toL a) (toL b) hab)
            subst hbe
            rw [hab] at h1
            cases hbc : cmpS (toL a) (toL c) with
            | gt =>
              rw [hbc] at h2
              exact Ordering.noConfusion (show Ordering.gt = Ordering.lt from h2)
            | lt => rfl
            | eq =>
              rw [hbc] at h2
              exact cmpS_trans xs ys zs h1 h2
termination_by x y z => sizeL x + sizeL y + sizeL z
decreasing_by
  · rw [sizeL_toL, sizeL_toL, sizeL_toL, sizeL_cons, sizeL_cons, sizeL_cons]; omega
  · rw [sizeL_cons, sizeL_cons, sizeL_cons]; omega


/-! ### §62.2 連結と文脈 -/

theorem sizeL_append : ∀ (l1 l2 : List (Nat × B)), sizeL (l1 ++ l2) = sizeL l1 + sizeL l2
  | [], l2 => by show sizeL l2 = 0 + sizeL l2; omega
  | (u, a) :: l1, l2 => by
      show sizeB a + 1 + sizeL (l1 ++ l2) = (sizeB a + 1 + sizeL l1) + sizeL l2
      rw [sizeL_append l1 l2]
      omega

theorem cmpS_nil_right_ne_lt : ∀ (x : List (Nat × B)), cmpS x [] ≠ .lt
  | [] => by rw [cmpS_nil_nil]; intro hc; exact Ordering.noConfusion hc
  | y :: ys => by rw [cmpS_cons_nil]; intro hc; exact Ordering.noConfusion hc

/-- 右に足しても `lt` は保たれる。 -/
theorem cmpS_lt_append : ∀ (x p q : List (Nat × B)), cmpS x p = .lt → cmpS x (p ++ q) = .lt
  | [], [], q, h => by rw [cmpS_nil_nil] at h; exact Ordering.noConfusion h
  | [], y :: ys, q, _ => cmpS_nil_cons y (ys ++ q)
  | x :: xs, [], q, h => by rw [cmpS_cons_nil] at h; exact Ordering.noConfusion h
  | (u, a) :: xs, (w, b) :: ps, q, h => by
      rw [cmpS_cons] at h
      show cmpS ((u, a) :: xs) ((w, b) :: (ps ++ q)) = .lt
      rw [cmpS_cons]
      by_cases h1 : u < w
      · rw [if_pos h1]
      · rw [if_neg h1] at h ⊢
        by_cases h2 : w < u
        · rw [if_pos h2] at h; exact Ordering.noConfusion h
        · rw [if_neg h2] at h ⊢
          cases hab : cmpS (toL a) (toL b) with
          | lt => rfl
          | gt => rw [hab] at h; exact Ordering.noConfusion h
          | eq =>
            rw [hab] at h
            exact cmpS_lt_append xs ps q h
termination_by x p _ => sizeL x + sizeL p
decreasing_by
  · rw [sizeL_cons, sizeL_cons]; omega

/-- 共通の接頭辞は無視できる。 -/
theorem cmpS_append_left : ∀ (p q1 q2 : List (Nat × B)),
    cmpS (p ++ q1) (p ++ q2) = cmpS q1 q2
  | [], q1, q2 => rfl
  | (w, b) :: ps, q1, q2 => by
      show cmpS ((w, b) :: (ps ++ q1)) ((w, b) :: (ps ++ q2)) = _
      rw [cmpS_cons, if_neg (Nat.lt_irrefl w), if_neg (Nat.lt_irrefl w), cmpS_refl (toL b)]
      exact cmpS_append_left ps q1 q2

/-- 真の接頭辞は小さい。 -/
theorem cmpS_lt_self_append (p q : List (Nat × B)) (hq : q ≠ []) : cmpS p (p ++ q) = .lt := by
  have := cmpS_append_left p [] q
  rw [List.append_nil] at this
  rw [this]
  cases q with
  | nil => exact absurd rfl hq
  | cons y ys => rw [cmpS_nil_cons]

/-- **文脈独立性。** `x` が接頭辞より真に小さいなら、その先は比較に効かない。 -/
theorem cmpS_ctx : ∀ (x p q : List (Nat × B)), sizeL x < sizeL p →
    cmpS x (p ++ q) = cmpS x p
  | x, [], q, h => by
      exact absurd h (by rw [show sizeL ([] : List (Nat × B)) = 0 from rfl]; omega)
  | [], (w, b) :: ps, q, _ => by
      show cmpS [] ((w, b) :: (ps ++ q)) = _
      rw [cmpS_nil_cons, cmpS_nil_cons]
  | (u, a) :: xs, (w, b) :: ps, q, h => by
      show cmpS ((u, a) :: xs) ((w, b) :: (ps ++ q)) = _
      rw [cmpS_cons, cmpS_cons]
      by_cases h1 : u < w
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : w < u
        · rw [if_pos h2, if_pos h2]
        · rw [if_neg h2, if_neg h2]
          cases hab : cmpS (toL a) (toL b) with
          | lt => rfl
          | gt => rfl
          | eq =>
            have hb : a = b := toL_inj a b (cmpS_eq_imp (toL a) (toL b) hab)
            subst hb
            refine cmpS_ctx xs ps q ?_
            rw [sizeL_cons, sizeL_cons] at h
            omega
termination_by x p _ _ => sizeL x + sizeL p
decreasing_by
  · rw [sizeL_cons, sizeL_cons]; omega

/-- **末尾の `ψ₀(0)` を落とす。** `(0, nil)` は最小の成分なので、これを付けた和より
    小さいものは、付ける前より小さいか、ちょうど等しい。 -/
theorem cmpS_lt_snoc_zero : ∀ (x p : List (Nat × B)),
    cmpS x (p ++ [(0, (.nil : B))]) = .lt → cmpS x p = .lt ∨ x = p
  | [], [], _ => Or.inr rfl
  | (u, a) :: xs, [], h => by
      exfalso
      have h' : cmpS ((u, a) :: xs) [(0, (.nil : B))] = .lt := h
      rw [cmpS_cons] at h'
      rw [if_neg (show ¬ (u < 0) by omega)] at h'
      by_cases h1 : 0 < u
      · rw [if_pos h1] at h'; exact Ordering.noConfusion h'
      · rw [if_neg h1] at h'
        cases haa : cmpS (toL a) (toL (.nil : B)) with
        | lt => exact cmpS_nil_right_ne_lt (toL a) haa
        | gt => rw [haa] at h'; exact Ordering.noConfusion h'
        | eq =>
          rw [haa] at h'
          exact cmpS_nil_right_ne_lt xs h'
  | [], (w, b) :: ps, _ => Or.inl (cmpS_nil_cons (w, b) ps)
  | (u, a) :: xs, (w, b) :: ps, h => by
      have h' : cmpS ((u, a) :: xs) ((w, b) :: (ps ++ [(0, (.nil : B))])) = .lt := h
      rw [cmpS_cons] at h'
      rw [cmpS_cons]
      by_cases h1 : u < w
      · rw [if_pos h1]; exact Or.inl rfl
      · rw [if_neg h1] at h' ⊢
        by_cases h2 : w < u
        · rw [if_pos h2] at h'; exact Ordering.noConfusion h'
        · rw [if_neg h2] at h' ⊢
          cases hab : cmpS (toL a) (toL b) with
          | lt => exact Or.inl rfl
          | gt => rw [hab] at h'; exact Ordering.noConfusion h'
          | eq =>
            rw [hab] at h'
            have hb : a = b := toL_inj a b (cmpS_eq_imp (toL a) (toL b) hab)
            subst hb
            rcases cmpS_lt_snoc_zero xs ps h' with hl | he
            · exact Or.inl hl
            · subst he
              have huw : u = w := by omega
              subst huw
              exact Or.inr rfl
termination_by x p => sizeL x + sizeL p
decreasing_by
  · rw [sizeL_cons, sizeL_cons]; omega


/-! #### 接頭辞による三分 -/

/-- **`p ++ q` より小さいものの三分。** `p` より小さいか、`p` そのものか、`p` を接頭辞に持つ。 -/
theorem cmpS_split : ∀ (x p q : List (Nat × B)), cmpS x (p ++ q) = .lt →
    cmpS x p = .lt ∨ x = p ∨ ∃ x', x' ≠ [] ∧ x = p ++ x' ∧ cmpS x' q = .lt
  | [], [], q, h => Or.inr (Or.inl rfl)
  | y :: ys, [], q, h => Or.inr (Or.inr ⟨y :: ys, List.cons_ne_nil y ys, rfl, h⟩)
  | [], (w, b) :: ps, q, _ => Or.inl (cmpS_nil_cons (w, b) ps)
  | (u, a) :: xs, (w, b) :: ps, q, h => by
      have h' : cmpS ((u, a) :: xs) ((w, b) :: (ps ++ q)) = .lt := h
      rw [cmpS_cons] at h'
      by_cases h1 : u < w
      · exact Or.inl (by rw [cmpS_cons, if_pos h1])
      · rw [if_neg h1] at h'
        by_cases h2 : w < u
        · rw [if_pos h2] at h'; exact Ordering.noConfusion h'
        · rw [if_neg h2] at h'
          cases hab : cmpS (toL a) (toL b) with
          | lt => exact Or.inl (by rw [cmpS_cons, if_neg h1, if_neg h2, hab])
          | gt => rw [hab] at h'; exact Ordering.noConfusion h'
          | eq =>
            rw [hab] at h'
            have hb : a = b := toL_inj a b (cmpS_eq_imp (toL a) (toL b) hab)
            have huw : u = w := by omega
            subst hb
            subst huw
            rcases cmpS_split xs ps q h' with hl | he | ⟨x', hne, hx, hq⟩
            · refine Or.inl ?_
              rw [cmpS_cons, if_neg h1, if_neg h2, hab]
              exact hl
            · exact Or.inr (Or.inl (by rw [he]))
            · exact Or.inr (Or.inr ⟨x', hne, by rw [hx]; rfl, hq⟩)
termination_by x p _ _ => sizeL x + sizeL p
decreasing_by
  · rw [sizeL_cons, sizeL_cons]; omega

/-! ### §62.3 `B` の演算と成分列 -/

theorem toL_appB : ∀ (s r : B), toL (appB r s) = toL r ++ toL s
  | .nil, r => by rw [show appB r .nil = r from rfl, show toL (.nil : B) = [] from rfl,
      List.append_nil]
  | .nd v s a, r => by
      show toL (B.nd v (appB r s) a) = _
      rw [toL_nd, toL_appB s r, toL_nd, List.append_assoc]

theorem sizeB_appB : ∀ (s r : B), sizeB (appB r s) = sizeB r + sizeB s
  | .nil, r => by show sizeB r = sizeB r + 0; omega
  | .nd v s a, r => by
      show sizeB (appB r s) + 1 + sizeB a = sizeB r + (sizeB s + 1 + sizeB a)
      rw [sizeB_appB s r]
      omega

theorem replicate_snoc {α : Type} (x : α) : ∀ (m : Nat),
    List.replicate m x ++ [x] = List.replicate (m + 1) x
  | 0 => rfl
  | k + 1 => by
      show x :: (List.replicate k x ++ [x]) = x :: List.replicate (k + 1) x
      rw [replicate_snoc x k]

theorem toL_repNode (v : Nat) (P : B) : ∀ (k : Nat),
    toL (repNode v P k) = List.replicate (k + 1) (v, P)
  | 0 => rfl
  | j + 1 => by
      show toL (B.nd v (repNode v P j) P) = _
      rw [toL_nd, toL_repNode v P j, replicate_snoc]

theorem sizeL_replicate (v : Nat) (P : B) : ∀ (m : Nat),
    sizeL (List.replicate m (v, P)) = m * (sizeB P + 1)
  | 0 => by show 0 = 0 * (sizeB P + 1); rw [Nat.zero_mul]
  | k + 1 => by
      show sizeB P + 1 + sizeL (List.replicate k (v, P)) = _
      rw [sizeL_replicate v P k, Nat.succ_mul]
      omega

/-! ### §62.4 `vArgs`: `visOK` が見る節の引数の並び -/

/-- 段 `v` の節の引数を、段が `v` 未満の節で打ち切りつつ集める。 -/
def vArgs (v : Nat) : B → List B
  | .nil => []
  | .nd u r c => vArgs v r ++ (if u < v then [] else (if u == v then [c] else []) ++ vArgs v c)

theorem vArgs_nd (v u : Nat) (r c : B) :
    vArgs v (.nd u r c)
      = vArgs v r ++ (if u < v then [] else (if u == v then [c] else []) ++ vArgs v c) := rfl

/-- **`visOK` は `vArgs` の全称。** -/
theorem visOK_iff : ∀ (s : B) (v : Nat) (a : B),
    visOK v a s = true ↔ ∀ c ∈ vArgs v s, cmpS (toL c) (toL a) = .lt := by
  intro s
  induction s with
  | nil =>
    intro v a
    exact ⟨fun _ c hc => absurd hc (by intro hm; exact List.not_mem_nil hm),
      fun _ => rfl⟩
  | nd u r c ihr ihc =>
    intro v a
    constructor
    · intro h
      have h' : (visOK v a r &&
        (if u < v then true
         else (if u == v then cmpS (toL c) (toL a) == Ordering.lt else true) && visOK v a c)) = true := h
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h'
      intro z hz
      rw [vArgs_nd] at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact (ihr v a).mp h1 z hz
      · by_cases hu : u < v
        · rw [if_pos hu] at hz; exact absurd hz (by intro hm; exact List.not_mem_nil hm)
        · rw [if_neg hu] at h2 hz
          obtain ⟨h3, h4⟩ := (Bool.and_eq_true _ _).mp h2
          rcases List.mem_append.mp hz with hz | hz
          · by_cases hv : (u == v) = true
            · rw [if_pos hv] at h3 hz
              rw [List.mem_singleton.mp hz]
              exact (beq_iff_eq (a := cmpS (toL c) (toL a)) (b := Ordering.lt)).mp h3
            · rw [if_neg hv] at hz; exact absurd hz (by intro hm; exact List.not_mem_nil hm)
          · exact (ihc v a).mp h4 z hz
    · intro h
      show (visOK v a r &&
        (if u < v then true
         else (if u == v then cmpS (toL c) (toL a) == Ordering.lt else true) && visOK v a c)) = true
      have hr : visOK v a r = true := (ihr v a).mpr (fun z hz => h z (by
        rw [vArgs_nd]; exact List.mem_append_left _ hz))
      rw [hr, Bool.true_and]
      by_cases hu : u < v
      · rw [if_pos hu]
      · rw [if_neg hu]
        have hc' : visOK v a c = true := (ihc v a).mpr (fun z hz => h z (by
          rw [vArgs_nd, if_neg hu]
          exact List.mem_append_right _ (List.mem_append_right _ hz)))
        rw [hc', Bool.and_true]
        by_cases hv : (u == v) = true
        · rw [if_pos hv]
          have : cmpS (toL c) (toL a) = .lt := h c (by
            rw [vArgs_nd, if_neg hu, if_pos hv]
            exact List.mem_append_right _ (List.mem_append_left _ (List.mem_singleton.mpr rfl)))
          rw [this]
          rfl
        · rw [if_neg hv]

/-- `vArgs` の要素は真部分項。 -/
theorem vArgs_size : ∀ (s : B) (v : Nat) (c : B), c ∈ vArgs v s → sizeB c < sizeB s := by
  intro s
  induction s with
  | nil => intro v c hc; exact absurd hc (by intro hm; exact List.not_mem_nil hm)
  | nd u r a ihr iha =>
    intro v c hc
    rw [vArgs_nd] at hc
    have hs : sizeB (B.nd u r a) = sizeB r + 1 + sizeB a := rfl
    rcases List.mem_append.mp hc with hc | hc
    · have := ihr v c hc; omega
    · by_cases hu : u < v
      · rw [if_pos hu] at hc; exact absurd hc (by intro hm; exact List.not_mem_nil hm)
      · rw [if_neg hu] at hc
        rcases List.mem_append.mp hc with hc | hc
        · by_cases hv : (u == v) = true
          · rw [if_pos hv] at hc
            rw [List.mem_singleton.mp hc]
            omega
          · rw [if_neg hv] at hc; exact absurd hc (by intro hm; exact List.not_mem_nil hm)
        · have := iha v c hc; omega

/-- `stdIn` は `vArgs` の要素にも伝わる。 -/
theorem stdIn_vArgs : ∀ (s : B), stdIn s = true → ∀ (v : Nat) (c : B), c ∈ vArgs v s →
    nonIncr c = true ∧ stdIn c = true := by
  intro s
  induction s with
  | nil => intro _ v c hc; exact absurd hc (by intro hm; exact List.not_mem_nil hm)
  | nd u r a ihr iha =>
    intro h v c hc
    have h' : (stdIn r && nonIncr a && visOK u a a && stdIn a) = true := h
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h'
    obtain ⟨h3, _⟩ := (Bool.and_eq_true _ _).mp h1
    obtain ⟨h5, h6⟩ := (Bool.and_eq_true _ _).mp h3
    rw [vArgs_nd] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ihr h5 v c hc
    · by_cases hu : u < v
      · rw [if_pos hu] at hc; exact absurd hc (by intro hm; exact List.not_mem_nil hm)
      · rw [if_neg hu] at hc
        rcases List.mem_append.mp hc with hc | hc
        · by_cases hv : (u == v) = true
          · rw [if_pos hv] at hc
            rw [List.mem_singleton.mp hc]
            exact ⟨h6, h2⟩
          · rw [if_neg hv] at hc; exact absurd hc (by intro hm; exact List.not_mem_nil hm)
        · exact iha h2 v c hc

/-! #### `nonIncrL` の切り出し -/

theorem nonIncrL_suffix : ∀ (p q : List (Nat × B)), nonIncrL (p ++ q) = true → nonIncrL q = true
  | [], q, h => h
  | x :: p, q, h => by
      have h' : nonIncrL (x :: (p ++ q)) = true := h
      rw [nonIncrL_cons] at h'
      exact nonIncrL_suffix p q ((Bool.and_eq_true _ _).mp h').2


/-! ### §62.5 `repB` の式と補助 -/

theorem cmpS_nil_lt : ∀ (l : List (Nat × B)), l ≠ [] → cmpS [] l = .lt
  | [], h => absurd rfl h
  | y :: ys, _ => cmpS_nil_cons y ys

theorem repB_arg_nil (v : Nat) (r : B) (n : Nat) : repB (.nd v r .nil) n = .nil := rfl
theorem repB_base (v : Nat) (r P : B) (n : Nat) :
    repB (.nd v r (.nd 0 P .nil)) n = appB r (repNode v P n) := rfl
theorem repB_rec1 (v : Nat) (r P : B) (u2 : Nat) (s2 c2 : B) (n : Nat) :
    repB (.nd v r (.nd 0 P (.nd u2 s2 c2))) n = .nd v r (repB (.nd 0 P (.nd u2 s2 c2)) n) := rfl
theorem repB_rec2 (v : Nat) (r : B) (k : Nat) (P c : B) (n : Nat) :
    repB (.nd v r (.nd (k + 1) P c)) n = .nd v r (repB (.nd (k + 1) P c) n) := rfl

theorem vArgs_appB : ∀ (X : B) (v : Nat) (r : B),
    vArgs v (appB r X) = vArgs v r ++ vArgs v X
  | .nil, v, r => by
      show vArgs v r = vArgs v r ++ []
      rw [List.append_nil]
  | .nd u X a, v, r => by
      show vArgs v (B.nd u (appB r X) a) = _
      rw [vArgs_nd, vArgs_appB X v r, vArgs_nd, List.append_assoc]

theorem mem_vArgs_repNode : ∀ (k : Nat) (v u : Nat) (P z : B), z ∈ vArgs v (repNode u P k) →
    ¬ (u < v) ∧ ((z = P ∧ (u == v) = true) ∨ z ∈ vArgs v P) := by
  intro k
  induction k with
  | zero =>
    intro v u P z hz
    have hz' : z ∈ vArgs v (B.nd u .nil P) := hz
    rw [vArgs_nd] at hz'
    rcases List.mem_append.mp hz' with h | h
    · exact absurd h (by intro hm; exact List.not_mem_nil hm)
    · by_cases hu : u < v
      · rw [if_pos hu] at h; exact absurd h (by intro hm; exact List.not_mem_nil hm)
      · rw [if_neg hu] at h
        refine ⟨hu, ?_⟩
        rcases List.mem_append.mp h with h | h
        · by_cases hv : (u == v) = true
          · rw [if_pos hv] at h; exact Or.inl ⟨List.mem_singleton.mp h, hv⟩
          · rw [if_neg hv] at h; exact absurd h (by intro hm; exact List.not_mem_nil hm)
        · exact Or.inr h
  | succ j ih =>
    intro v u P z hz
    have hz' : z ∈ vArgs v (B.nd u (repNode u P j) P) := hz
    rw [vArgs_nd] at hz'
    rcases List.mem_append.mp hz' with h | h
    · exact ih v u P z h
    · by_cases hu : u < v
      · rw [if_pos hu] at h; exact absurd h (by intro hm; exact List.not_mem_nil hm)
      · rw [if_neg hu] at h
        refine ⟨hu, ?_⟩
        rcases List.mem_append.mp h with h | h
        · by_cases hv : (u == v) = true
          · rw [if_pos hv] at h; exact Or.inl ⟨List.mem_singleton.mp h, hv⟩
          · rw [if_neg hv] at h; exact absurd h (by intro hm; exact List.not_mem_nil hm)
        · exact Or.inr h

/-- 最上位の成分の引数は `vArgs` に入る。 -/
theorem mem_toL_vArgs : ∀ (s : B) (u : Nat) (c : B), (u, c) ∈ toL s → c ∈ vArgs u s := by
  intro s
  induction s with
  | nil => intro u c h; exact absurd h (by intro hm; exact List.not_mem_nil hm)
  | nd u' r c' ihr _ =>
    intro u c h
    rw [toL_nd] at h
    rw [vArgs_nd]
    rcases List.mem_append.mp h with h | h
    · exact List.mem_append_left _ (ihr u c h)
    · have he : (u', c') = (u, c) := (List.mem_singleton.mp h).symm
      injection he with h1 h2
      subst h1
      subst h2
      refine List.mem_append_right _ ?_
      rw [if_neg (show ¬ (u' < u') by omega), if_pos (show (u' == u') = true from beq_self_eq_true u')]
      exact List.mem_append_left _ (List.mem_singleton.mpr rfl)

/-- 比較の向きを入れ替える。 -/
theorem cmpS_swap : ∀ (x y : List (Nat × B)), cmpS y x = (cmpS x y).swap
  | [], [] => by rw [cmpS_nil_nil]; rfl
  | [], y :: ys => by rw [cmpS_nil_cons, cmpS_cons_nil]; rfl
  | x :: xs, [] => by rw [cmpS_nil_cons, cmpS_cons_nil]; rfl
  | (u, a) :: xs, (w, b) :: ys => by
      rw [cmpS_cons, cmpS_cons]
      by_cases h1 : u < w
      · rw [if_neg (show ¬ (w < u) by omega), if_pos h1, if_pos h1]
        rfl
      · by_cases h2 : w < u
        · rw [if_pos h2, if_neg h1, if_pos h2]
          rfl
        · rw [if_neg h2, if_neg h1, if_neg h1, if_neg h2]
          rw [cmpS_swap (toL a) (toL b)]
          cases hab : cmpS (toL a) (toL b) with
          | lt => rfl
          | gt => rfl
          | eq => exact cmpS_swap xs ys
termination_by x y => sizeL x + sizeL y
decreasing_by
  · rw [sizeL_toL, sizeL_toL, sizeL_cons, sizeL_cons]; omega
  · rw [sizeL_cons, sizeL_cons]; omega

theorem cmpS_gt_lt {x y : List (Nat × B)} (h : cmpS x y = .gt) : cmpS y x = .lt := by
  rw [cmpS_swap x y, h]; rfl

theorem cmpS_lt_gt {x y : List (Nat × B)} (h : cmpS x y = .lt) : cmpS y x = .gt := by
  rw [cmpS_swap x y, h]; rfl

/-- 降べきの尻尾は同じ成分の繰り返しより短ければ小さい。 -/
theorem rep_tail : ∀ (m : Nat) (u : Nat) (P : B) (rest : List (Nat × B)),
    nonIncrL ((u, P) :: rest) = true → sizeL rest < m * (sizeB P + 1) →
    cmpS rest (List.replicate m (u, P)) = .lt := by
  intro m
  induction m with
  | zero => intro u P rest _ hs; rw [Nat.zero_mul] at hs; omega
  | succ j ih =>
    intro u P rest hni hs
    cases rest with
    | nil => exact cmpS_nil_cons (u, P) (List.replicate j (u, P))
    | cons y ys =>
      rw [nonIncrL_cons] at hni
      obtain ⟨hhd, hni2⟩ := (Bool.and_eq_true _ _).mp hni
      have hne : ¬ (cmpS [(u, P)] [(y.1, y.2)] = .lt) := by
        intro hc
        rw [show hdOK (u, P) (y :: ys) = !(cmpN (u, P).1 (u, P).2 y.1 y.2 == Ordering.lt) from rfl,
          show cmpN (u, P).1 (u, P).2 y.1 y.2 = cmpS [(u, P)] [(y.1, y.2)] from rfl, hc] at hhd
        exact Bool.noConfusion hhd
      rw [cmpS_cons] at hne
      have hu1 : ¬ (u < y.1) := by
        intro hc; rw [if_pos hc] at hne; exact hne rfl
      rw [if_neg hu1] at hne
      show cmpS ((y.1, y.2) :: ys) ((u, P) :: List.replicate j (u, P)) = .lt
      rw [cmpS_cons]
      by_cases h1 : y.1 < u
      · rw [if_pos h1]
      · rw [if_neg h1, if_neg hu1]
        rw [if_neg h1] at hne
        cases hpy : cmpS (toL P) (toL y.2) with
        | lt => rw [hpy] at hne; exact absurd rfl hne
        | gt => rw [cmpS_gt_lt hpy]
        | eq =>
          have hyP : y.2 = P := toL_inj y.2 P (cmpS_eq_imp (toL y.2) (toL P)
            (by rw [cmpS_swap (toL P) (toL y.2), hpy]; rfl))
          rw [hyP, cmpS_refl]
          refine ih u P ys ?_ ?_
          · have hy : y = (u, P) := by
              have hu : y.1 = u := by omega
              rw [← hyP, ← hu]
            rw [← hy]
            exact hni2
          · have hsz : sizeL (y :: ys) = sizeB y.2 + 1 + sizeL ys := rfl
            rw [hsz, hyP, Nat.succ_mul] at hs
            omega


/-! #### `visOK` の分解 -/

theorem visOK_nd_eq (v u : Nat) (ref r c : B) :
    visOK v ref (.nd u r c)
      = (visOK v ref r &&
         (if u < v then true
          else (if u == v then cmpS (toL c) (toL ref) == Ordering.lt else true)
                 && visOK v ref c)) := rfl

theorem visOK_nd_r {v u : Nat} {ref r c : B} (h : visOK v ref (.nd u r c) = true) :
    visOK v ref r = true := by
  rw [visOK_nd_eq] at h
  exact ((Bool.and_eq_true _ _).mp h).1

theorem visOK_nd_c {v u : Nat} {ref r c : B} (hu : ¬ (u < v))
    (h : visOK v ref (.nd u r c) = true) : visOK v ref c = true := by
  rw [visOK_nd_eq, if_neg hu] at h
  exact ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).2).2

theorem visOK_nd_arg {v u : Nat} {ref r c : B} (hu : ¬ (u < v)) (hv : (u == v) = true)
    (h : visOK v ref (.nd u r c) = true) : cmpS (toL c) (toL ref) = .lt := by
  rw [visOK_nd_eq, if_neg hu, if_pos hv] at h
  have := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).2).1
  exact (beq_iff_eq (a := cmpS (toL c) (toL ref)) (b := Ordering.lt)).mp this

theorem visOK_nd_mk {v u : Nat} {ref r c : B} (h1 : visOK v ref r = true)
    (h2 : ¬ (u < v) → visOK v ref c = true)
    (h3 : ¬ (u < v) → (u == v) = true → cmpS (toL c) (toL ref) = .lt) :
    visOK v ref (.nd u r c) = true := by
  rw [visOK_nd_eq, h1, Bool.true_and]
  by_cases hu : u < v
  · rw [if_pos hu]
  · rw [if_neg hu, h2 hu, Bool.and_true]
    by_cases hv : (u == v) = true
    · rw [if_pos hv, h3 hu hv]; rfl
    · rw [if_neg hv]

/-! ### §62.6 `repB` は真に小さい -/

theorem repB_lt : ∀ (a : B) (n : Nat), a ≠ .nil → cmpS (toL (repB a n)) (toL a) = .lt := by
  intro a
  induction a with
  | nil => intro n h; exact absurd rfl h
  | nd v r a1 _ iha =>
    intro n _
    cases a1 with
    | nil =>
      rw [repB_arg_nil]
      exact cmpS_nil_lt _ (toL_ne_nil v r .nil)
    | nd u P c =>
      cases u with
      | zero =>
        cases c with
        | nil =>
          rw [repB_base, toL_appB, toL_nd, toL_repNode, cmpS_append_left]
          show cmpS ((v, P) :: List.replicate n (v, P)) [(v, B.nd 0 P .nil)] = .lt
          rw [cmpS_cons, if_neg (Nat.lt_irrefl v), if_neg (Nat.lt_irrefl v),
            toL_nd 0 P .nil,
            cmpS_lt_self_append (toL P) [(0, (.nil : B))] (List.cons_ne_nil _ _)]
        | nd u2 s2 c2 =>
          rw [repB_rec1, toL_nd, toL_nd, cmpS_append_left]
          show cmpS [(v, repB (B.nd 0 P (.nd u2 s2 c2)) n)] [(v, B.nd 0 P (.nd u2 s2 c2))] = .lt
          rw [cmpS_cons, if_neg (Nat.lt_irrefl v), if_neg (Nat.lt_irrefl v),
            iha n (by intro hc; exact B.noConfusion hc)]
      | succ k =>
        rw [repB_rec2, toL_nd, toL_nd, cmpS_append_left]
        show cmpS [(v, repB (B.nd (k + 1) P c) n)] [(v, B.nd (k + 1) P c)] = .lt
        rw [cmpS_cons, if_neg (Nat.lt_irrefl v), if_neg (Nat.lt_irrefl v),
          iha n (by intro hc; exact B.noConfusion hc)]


/-! ### §62.7 二つの移送補題 -/

/-! #### 基準は据え置き -/

theorem visOK_repB : ∀ (a : B) (n v : Nat) (ref : B),
    visOK v ref a = true → visOK v ref (repB a n) = true := by
  intro a
  induction a with
  | nil => intro n v ref _; rfl
  | nd u r a1 _ iha =>
    intro n v ref h
    have hr : visOK v ref r = true := visOK_nd_r h
    cases a1 with
    | nil => rw [repB_arg_nil]; rfl
    | nd u1 P c =>
      cases u1 with
      | zero =>
        cases c with
        | nil =>
          rw [repB_base]
          refine (visOK_iff _ v ref).mpr ?_
          intro z hz
          rw [vArgs_appB] at hz
          rcases List.mem_append.mp hz with hz | hz
          · exact (visOK_iff r v ref).mp hr z hz
          · obtain ⟨hu, hcase⟩ := mem_vArgs_repNode n v u P z hz
            rcases hcase with ⟨hzP, huv⟩ | hz2
            · have harg : cmpS (toL (B.nd 0 P .nil)) (toL ref) = .lt := visOK_nd_arg hu huv h
              have hPlt : cmpS (toL P) (toL (B.nd 0 P .nil)) = .lt := by
                rw [toL_nd 0 P .nil]
                exact cmpS_lt_self_append (toL P) [(0, (.nil : B))] (List.cons_ne_nil _ _)
              rw [hzP]
              exact cmpS_trans (toL P) _ (toL ref) hPlt harg
            · exact (visOK_iff P v ref).mp (visOK_nd_r (visOK_nd_c hu h)) z hz2
        | nd u2 s2 c2 =>
          rw [repB_rec1]
          refine visOK_nd_mk hr (fun hu => iha n v ref (visOK_nd_c hu h)) ?_
          intro hu huv
          exact cmpS_trans _ _ _ (repB_lt _ n (by intro hc; exact B.noConfusion hc))
            (visOK_nd_arg hu huv h)
      | succ k =>
        rw [repB_rec2]
        refine visOK_nd_mk hr (fun hu => iha n v ref (visOK_nd_c hu h)) ?_
        intro hu huv
        exact cmpS_trans _ _ _ (repB_lt _ n (by intro hc; exact B.noConfusion hc))
          (visOK_nd_arg hu huv h)

/-! #### 基準も動かす -/

theorem C1_repB_base (u : Nat) (r P : B) (n : Nat) (x : B)
    (hni : nonIncr x = true)
    (hs : sizeB x < sizeB (appB r (repNode u P n)))
    (hlt : cmpS (toL x) (toL (B.nd u r (.nd 0 P .nil))) = .lt) :
    cmpS (toL x) (toL (appB r (repNode u P n))) = .lt := by
  have hA : toL (appB r (repNode u P n)) = toL r ++ List.replicate (n + 1) (u, P) := by
    rw [toL_appB, toL_repNode]
  rw [toL_nd] at hlt
  rw [hA]
  rcases cmpS_split (toL x) (toL r) [(u, (B.nd 0 P .nil))] hlt with h1 | h2 | ⟨x', hne, hx, hq⟩
  · exact cmpS_lt_append _ _ _ h1
  · rw [h2]
    exact cmpS_lt_self_append (toL r) _ (List.cons_ne_nil _ _)
  · rw [hx, cmpS_append_left]
    cases x' with
    | nil => exact absurd rfl hne
    | cons y rest =>
      obtain ⟨u0, z0⟩ := y
      rw [cmpS_cons] at hq
      by_cases h1 : u0 < u
      · show cmpS ((u0, z0) :: rest) ((u, P) :: List.replicate n (u, P)) = .lt
        rw [cmpS_cons, if_pos h1]
      · rw [if_neg h1] at hq
        by_cases h2 : u < u0
        · rw [if_pos h2] at hq; exact Ordering.noConfusion hq
        · rw [if_neg h2] at hq
          have hu0 : u0 = u := by omega
          subst hu0
          have hz : cmpS (toL z0) (toL (B.nd 0 P .nil)) = .lt := by
            cases hzz : cmpS (toL z0) (toL (B.nd 0 P .nil)) with
            | lt => rfl
            | gt => rw [hzz] at hq; exact Ordering.noConfusion hq
            | eq => rw [hzz] at hq; exact absurd hq (cmpS_nil_right_ne_lt rest)
          rw [toL_nd 0 P .nil] at hz
          show cmpS ((u0, z0) :: rest) ((u0, P) :: List.replicate n (u0, P)) = .lt
          rw [cmpS_cons, if_neg (Nat.lt_irrefl u0), if_neg (Nat.lt_irrefl u0)]
          rcases cmpS_lt_snoc_zero (toL z0) (toL P) hz with hlt2 | heq
          · rw [hlt2]
          · have hzP : z0 = P := toL_inj z0 P heq
            subst hzP
            rw [cmpS_refl]
            refine rep_tail n u0 z0 rest ?_ ?_
            · have h3 : nonIncrL (toL r ++ ((u0, z0) :: rest)) = true := by
                rw [← hx]; exact hni
              exact nonIncrL_suffix (toL r) _ h3
            · have e1 : sizeB x = sizeB r + (sizeB z0 + 1 + sizeL rest) := by
                rw [← sizeL_toL, hx, sizeL_append, sizeL_toL]
                rfl
              have e2 : sizeB (appB r (repNode u0 z0 n))
                  = sizeB r + (n + 1) * (sizeB z0 + 1) := by
                rw [sizeB_appB, ← sizeL_toL (repNode u0 z0 n), toL_repNode, sizeL_replicate]
              rw [e1, e2, Nat.succ_mul] at hs
              omega

theorem C1_repB_rec (u : Nat) (r a1 : B) (n : Nat) (x : B)
    (hIH : ∀ (z : B), nonIncr z = true → stdIn z = true → sizeB z < sizeB (repB a1 n) →
      cmpS (toL z) (toL a1) = .lt → cmpS (toL z) (toL (repB a1 n)) = .lt)
    (_hni : nonIncr x = true) (hst : stdIn x = true)
    (hs : sizeB x < sizeB (B.nd u r (repB a1 n)))
    (hlt : cmpS (toL x) (toL (B.nd u r a1)) = .lt) :
    cmpS (toL x) (toL (B.nd u r (repB a1 n))) = .lt := by
  rw [toL_nd] at hlt
  rw [toL_nd]
  rcases cmpS_split (toL x) (toL r) [(u, a1)] hlt with h1 | h2 | ⟨x', hne, hx, hq⟩
  · exact cmpS_lt_append _ _ _ h1
  · rw [h2]
    exact cmpS_lt_self_append (toL r) _ (List.cons_ne_nil _ _)
  · rw [hx, cmpS_append_left]
    cases x' with
    | nil => exact absurd rfl hne
    | cons y rest =>
      obtain ⟨u0, z0⟩ := y
      rw [cmpS_cons] at hq
      by_cases h1 : u0 < u
      · rw [cmpS_cons, if_pos h1]
      · rw [if_neg h1] at hq
        by_cases h2 : u < u0
        · rw [if_pos h2] at hq; exact Ordering.noConfusion hq
        · rw [if_neg h2] at hq
          have hu0 : u0 = u := by omega
          subst hu0
          have hz : cmpS (toL z0) (toL a1) = .lt := by
            cases hzz : cmpS (toL z0) (toL a1) with
            | lt => rfl
            | gt => rw [hzz] at hq; exact Ordering.noConfusion hq
            | eq => rw [hzz] at hq; exact absurd hq (cmpS_nil_right_ne_lt rest)
          have hmem : (u0, z0) ∈ toL x := by
            rw [hx]
            exact List.mem_append_right _ (List.mem_cons_self ..)
          obtain ⟨hnz, hsz⟩ := stdIn_vArgs x hst u0 z0 (mem_toL_vArgs x u0 z0 hmem)
          have e1 : sizeB x = sizeB r + (sizeB z0 + 1 + sizeL rest) := by
            rw [← sizeL_toL, hx, sizeL_append, sizeL_toL]
            rfl
          have e2 : sizeB (B.nd u0 r (repB a1 n)) = sizeB r + 1 + sizeB (repB a1 n) := rfl
          rw [e1, e2] at hs
          rw [cmpS_cons, if_neg (Nat.lt_irrefl u0), if_neg (Nat.lt_irrefl u0),
            hIH z0 hnz hsz (by omega) hz]

theorem C1_repB : ∀ (a : B) (n : Nat) (x : B), nonIncr x = true → stdIn x = true →
    sizeB x < sizeB (repB a n) → cmpS (toL x) (toL a) = .lt →
    cmpS (toL x) (toL (repB a n)) = .lt := by
  intro a
  induction a with
  | nil =>
    intro n x _ _ hs _
    have : sizeB (repB (.nil : B) n) = 0 := rfl
    omega
  | nd u r a1 _ iha =>
    intro n x hni hst hs hlt
    cases a1 with
    | nil =>
      rw [repB_arg_nil] at hs ⊢
      have : sizeB (.nil : B) = 0 := rfl
      omega
    | nd u1 P c =>
      cases u1 with
      | zero =>
        cases c with
        | nil =>
          rw [repB_base] at hs ⊢
          exact C1_repB_base u r P n x hni hs hlt
        | nd u2 s2 c2 =>
          rw [repB_rec1] at hs ⊢
          exact C1_repB_rec u r _ n x (fun z h1 h2 h3 h4 => iha n z h1 h2 h3 h4) hni hst hs hlt
      | succ k =>
        rw [repB_rec2] at hs ⊢
        exact C1_repB_rec u r _ n x (fun z h1 h2 h3 h4 => iha n z h1 h2 h3 h4) hni hst hs hlt


/-! #### 降べきの張り替え -/

theorem cmpS_not_lt {x y : List (Nat × B)} (h : ¬ (cmpS x y = .lt)) :
    cmpS y x = .lt ∨ x = y := by
  cases hxy : cmpS x y with
  | lt => exact absurd hxy h
  | eq => exact Or.inr (cmpS_eq_imp x y hxy)
  | gt => exact Or.inl (cmpS_gt_lt hxy)

theorem cmpS_asymm {x y : List (Nat × B)} (h : cmpS x y = .lt) : ¬ (cmpS y x = .lt) := by
  intro hc
  rw [cmpS_lt_gt h] at hc
  exact Ordering.noConfusion hc

theorem hdOK_cons (x y : Nat × B) (l : List (Nat × B)) :
    hdOK x (y :: l) = !(cmpS [(x.1, x.2)] [(y.1, y.2)] == Ordering.lt) := rfl

theorem hdOK_of_not_lt (x y : Nat × B) (l : List (Nat × B))
    (h : ¬ (cmpS [x] [y] = .lt)) : hdOK x (y :: l) = true := by
  rw [hdOK_cons]
  cases hc : (cmpS [(x.1, x.2)] [(y.1, y.2)] == Ordering.lt) with
  | false => rfl
  | true => exact absurd ((beq_iff_eq (a := cmpS [x] [y]) (b := Ordering.lt)).mp hc) h

theorem not_lt_of_hdOK {x y : Nat × B} {l : List (Nat × B)} (h : hdOK x (y :: l) = true) :
    ¬ (cmpS [x] [y] = .lt) := by
  intro hc
  rw [hdOK_cons, show cmpS [(x.1, x.2)] [(y.1, y.2)] = cmpS [x] [y] from rfl, hc] at h
  exact Bool.noConfusion h

theorem hdOK_trans {y z : Nat × B} {q : List (Nat × B)}
    (h1 : hdOK y q = true) (h2 : ¬ (cmpS [z] [y] = .lt)) : hdOK z q = true := by
  cases q with
  | nil => rfl
  | cons w q' =>
    refine hdOK_of_not_lt z w q' ?_
    intro hzw
    have hwy : ¬ (cmpS [y] [w] = .lt) := not_lt_of_hdOK h1
    rcases cmpS_not_lt hwy with hlt | heq
    · exact h2 (cmpS_trans [z] [w] [y] hzw hlt)
    · rw [← heq] at hzw; exact h2 hzw

theorem nonIncrL_replicate (u : Nat) (P : B) : ∀ (m : Nat),
    nonIncrL (List.replicate m (u, P)) = true
  | 0 => rfl
  | k + 1 => by
      show (hdOK (u, P) (List.replicate k (u, P)) && nonIncrL (List.replicate k (u, P))) = true
      rw [nonIncrL_replicate u P k, Bool.and_true]
      cases k with
      | zero => rfl
      | succ j =>
        refine hdOK_of_not_lt (u, P) (u, P) _ ?_
        rw [cmpS_refl]
        intro hc; exact Ordering.noConfusion hc

/-- **末尾の成分を、より小さい列で置き換える。** -/
theorem nonIncrL_subst : ∀ (l : List (Nat × B)) (y : Nat × B) (q : List (Nat × B)),
    nonIncrL (l ++ [y]) = true → nonIncrL q = true → hdOK y q = true →
    nonIncrL (l ++ q) = true
  | [], y, q, _, hq, _ => hq
  | z :: l', y, q, h, hq, hy => by
      have h' : (hdOK z (l' ++ [y]) && nonIncrL (l' ++ [y])) = true := h
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h'
      show (hdOK z (l' ++ q) && nonIncrL (l' ++ q)) = true
      rw [nonIncrL_subst l' y q h2 hq hy, Bool.and_true]
      cases l' with
      | nil => exact hdOK_trans hy (not_lt_of_hdOK h1)
      | cons w l'' => exact h1

/-! #### `repB` は降べきを保つ -/

theorem P_lt_snoc (u : Nat) (P : B) : cmpS [(u, P)] [(u, (B.nd 0 P .nil))] = .lt := by
  rw [cmpS_cons, if_neg (Nat.lt_irrefl u), if_neg (Nat.lt_irrefl u), toL_nd 0 P .nil,
    cmpS_lt_self_append (toL P) [(0, (.nil : B))] (List.cons_ne_nil _ _)]

theorem nonIncr_repB : ∀ (a : B) (n : Nat), nonIncr a = true → nonIncr (repB a n) = true := by
  intro a
  induction a with
  | nil => intro n h; exact h
  | nd u r a1 _ iha =>
    intro n h
    have h' : nonIncrL (toL r ++ [(u, a1)]) = true := by rw [← toL_nd]; exact h
    cases a1 with
    | nil => rw [repB_arg_nil]; rfl
    | nd u1 P c =>
      cases u1 with
      | zero =>
        cases c with
        | nil =>
          rw [repB_base]
          show nonIncrL (toL (appB r (repNode u P n))) = true
          rw [toL_appB, toL_repNode]
          refine nonIncrL_subst (toL r) (u, (B.nd 0 P .nil)) _ h'
            (nonIncrL_replicate u P (n + 1)) ?_
          exact hdOK_of_not_lt _ (u, P) _ (cmpS_asymm (P_lt_snoc u P))
        | nd u2 s2 c2 =>
          rw [repB_rec1]
          show nonIncrL (toL (B.nd u r (repB (B.nd 0 P (.nd u2 s2 c2)) n))) = true
          rw [toL_nd]
          refine nonIncrL_subst (toL r) (u, (B.nd 0 P (.nd u2 s2 c2))) _ h' rfl ?_
          refine hdOK_of_not_lt _ (u, repB (B.nd 0 P (.nd u2 s2 c2)) n) _ (cmpS_asymm ?_)
          rw [cmpS_cons, if_neg (Nat.lt_irrefl u), if_neg (Nat.lt_irrefl u),
            repB_lt _ n (by intro hc; exact B.noConfusion hc)]
      | succ k =>
        rw [repB_rec2]
        show nonIncrL (toL (B.nd u r (repB (B.nd (k + 1) P c) n))) = true
        rw [toL_nd]
        refine nonIncrL_subst (toL r) (u, (B.nd (k + 1) P c)) _ h' rfl ?_
        refine hdOK_of_not_lt _ (u, repB (B.nd (k + 1) P c) n) _ (cmpS_asymm ?_)
        rw [cmpS_cons, if_neg (Nat.lt_irrefl u), if_neg (Nat.lt_irrefl u),
          repB_lt _ n (by intro hc; exact B.noConfusion hc)]


/-! #### `stdIn` の閉包 -/

theorem stdIn_nd_eq (v : Nat) (r c : B) :
    stdIn (.nd v r c) = (stdIn r && nonIncr c && visOK v c c && stdIn c) := rfl

theorem and_assoc4 (x y n v d : Bool) :
    ((((x && y) && n) && v) && d) = (x && (((y && n) && v) && d)) := by
  cases x <;> cases y <;> cases n <;> cases v <;> cases d <;> rfl

/-- **基準を `P ⊕ ψ₀(0)` から `P` に縮める。** 走査対象が `P` より大きくない限り通る。 -/
theorem visOK_shrink (v : Nat) (P s : B) (hsz : sizeB s ≤ sizeB P)
    (h : visOK v (.nd 0 P .nil) s = true) : visOK v P s = true := by
  refine (visOK_iff s v P).mpr ?_
  intro z hz
  have h1 : cmpS (toL z) (toL (B.nd 0 P .nil)) = .lt := (visOK_iff s v _).mp h z hz
  rw [toL_nd 0 P .nil] at h1
  rcases cmpS_lt_snoc_zero (toL z) (toL P) h1 with hlt | heq
  · exact hlt
  · exfalso
    have he := toL_inj z P heq
    have h2 := vArgs_size s v z hz
    rw [he] at h2
    omega

theorem stdIn_appB : ∀ (X r : B), stdIn (appB r X) = (stdIn r && stdIn X)
  | .nil, r => by
      show stdIn r = (stdIn r && true)
      rw [Bool.and_true]
  | .nd v s a, r => by
      show (stdIn (appB r s) && nonIncr a && visOK v a a && stdIn a)
        = (stdIn r && (stdIn s && nonIncr a && visOK v a a && stdIn a))
      rw [stdIn_appB s r, and_assoc4]

theorem stdIn_repNode (u : Nat) (P : B) (hP1 : nonIncr P = true) (hP2 : visOK u P P = true)
    (hP3 : stdIn P = true) : ∀ (k : Nat), stdIn (repNode u P k) = true
  | 0 => by
      show (stdIn .nil && nonIncr P && visOK u P P && stdIn P) = true
      rw [hP1, hP2, hP3]
      rfl
  | j + 1 => by
      show (stdIn (repNode u P j) && nonIncr P && visOK u P P && stdIn P) = true
      rw [stdIn_repNode u P hP1 hP2 hP3 j, hP1, hP2, hP3]
      rfl

/-- **`repB` は `visOK` の自己参照版を保つ。** `stdIn (repB a n)` を仮定に取る。 -/
theorem visOK_self_repB (a : B) (n v : Nat) (hst : stdIn (repB a n) = true)
    (h : visOK v a a = true) : visOK v (repB a n) (repB a n) = true := by
  refine (visOK_iff (repB a n) v (repB a n)).mpr ?_
  intro z hz
  have h1 : cmpS (toL z) (toL a) = .lt :=
    (visOK_iff (repB a n) v a).mp (visOK_repB a n v a h) z hz
  obtain ⟨hnz, hstz⟩ := stdIn_vArgs (repB a n) hst v z hz
  exact C1_repB a n z hnz hstz (vArgs_size (repB a n) v z hz) h1

theorem stdIn_repB : ∀ (a : B) (n : Nat), stdIn a = true → stdIn (repB a n) = true := by
  intro a
  induction a with
  | nil => intro n _; rfl
  | nd u r a1 _ iha =>
    intro n h
    rw [stdIn_nd_eq] at h
    obtain ⟨h123, h4⟩ := (Bool.and_eq_true _ _).mp h
    obtain ⟨h12, h3⟩ := (Bool.and_eq_true _ _).mp h123
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h12
    cases a1 with
    | nil => rw [repB_arg_nil]; rfl
    | nd u1 P c =>
      cases u1 with
      | zero =>
        cases c with
        | nil =>
          rw [repB_base, stdIn_appB, h1, Bool.true_and]
          have hPni : nonIncr P = true := by
            have : nonIncrL (toL P ++ [(0, (.nil : B))]) = true := by
              rw [← toL_nd 0 P .nil]; exact h2
            exact nonIncrL_dropLast (toL P) (0, .nil) this
          have hPst : stdIn P = true := by
            rw [stdIn_nd_eq] at h4
            exact ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp
              ((Bool.and_eq_true _ _).mp h4).1).1).1
          have hPvis : visOK u P P = true :=
            visOK_shrink u P P (by omega) (visOK_nd_r h3)
          exact stdIn_repNode u P hPni hPvis hPst n
        | nd u2 s2 c2 =>
          rw [repB_rec1, stdIn_nd_eq, h1, Bool.true_and,
            nonIncr_repB _ n h2, Bool.true_and, iha n h4, Bool.and_true,
            visOK_self_repB _ n u (iha n h4) h3]
      | succ k =>
        rw [repB_rec2, stdIn_nd_eq, h1, Bool.true_and,
          nonIncr_repB _ n h2, Bool.true_and, iha n h4, Bool.and_true,
          visOK_self_repB _ n u (iha n h4) h3]



/-! ### §62.8 `rwB` の枝: `plugB`・`iterD`・`GG` -/

theorem plugB_nil_arg (u : Nat) (s Y : B) : plugB (.nd u s .nil) Y = appB s Y := rfl
theorem plugB_rec (u : Nat) (s : B) (u2 : Nat) (s2 c2 Y : B) :
    plugB (.nd u s (.nd u2 s2 c2)) Y = .nd u s (plugB (.nd u2 s2 c2) Y) := rfl

theorem hasLowAnc_nd (w v : Nat) (s : B) (u2 : Nat) (s2 c2 : B) :
    hasLowAnc w (.nd v s (.nd u2 s2 c2))
      = (decide (v < w) || hasLowAnc w (.nd u2 s2 c2)) := rfl

theorem lastLvl_leaf (v : Nat) (s : B) : lastLvl (.nd v s .nil) = v := rfl
theorem lastLvl_nd (v : Nat) (s : B) (u2 : Nat) (s2 c2 : B) :
    lastLvl (.nd v s (.nd u2 s2 c2)) = lastLvl (.nd u2 s2 c2) := rfl

theorem rwB_leaf (w n v : Nat) (s : B) : rwB w n (.nd v s .nil) = .nd v s .nil := rfl
theorem rwB_nd (w n v : Nat) (s : B) (u2 : Nat) (s2 c2 : B) :
    rwB w n (.nd v s (.nd u2 s2 c2))
      = (if hasLowAnc w (.nd u2 s2 c2) then .nd v s (rwB w n (.nd u2 s2 c2))
         else if v < w then appB s (iterD v (.nd u2 s2 c2) n)
         else .nd v s (.nd u2 s2 c2)) := rfl

/-- `iterD` の内側。`GG v a k` は `a` の最後の節を `k` 回入れ子に差し替えたもの。 -/
def GG (v : Nat) (a : B) : Nat → B
  | 0 => plugB a .nil
  | k + 1 => plugB a (.nd v .nil (GG v a k))

theorem iterD_GG (v : Nat) (a : B) : ∀ (k : Nat), iterD v a k = .nd v .nil (GG v a k)
  | 0 => rfl
  | j + 1 => by
      show B.nd v .nil (plugB a (iterD v a j)) = _
      rw [iterD_GG v a j]
      rfl

theorem appB_iterD (v : Nat) (s a : B) (k : Nat) :
    appB s (iterD v a k) = .nd v s (GG v a k) := by
  rw [iterD_GG]
  rfl

theorem toL_iterD (v : Nat) (a : B) (k : Nat) : toL (iterD v a k) = [(v, GG v a k)] := by
  rw [iterD_GG, toL_nd]
  rfl

/-! #### `plugB` は成分列をどう変えるか -/

theorem toL_plugB_leaf (u : Nat) (s Y : B) : toL (plugB (.nd u s .nil) Y) = toL s ++ toL Y := by
  rw [plugB_nil_arg, toL_appB]

theorem toL_plugB_rec (u : Nat) (s : B) (u2 : Nat) (s2 c2 Y : B) :
    toL (plugB (.nd u s (.nd u2 s2 c2)) Y) = toL s ++ [(u, plugB (.nd u2 s2 c2) Y)] := by
  rw [plugB_rec, toL_nd]

theorem sizeB_plugB_leaf (u : Nat) (s Y : B) : sizeB (plugB (.nd u s .nil) Y)
    = sizeB s + sizeB Y := by
  rw [plugB_nil_arg, sizeB_appB]

/-- **`plugB` は真に小さい。** 差し込む列が `ψ_{lastLvl a}(0)` より小さければよい。 -/
theorem plugB_lt : ∀ (a : B) (Y : B), a ≠ .nil →
    cmpS (toL Y) [(lastLvl a, (.nil : B))] = .lt →
    cmpS (toL (plugB a Y)) (toL a) = .lt := by
  intro a
  induction a with
  | nil => intro Y h _; exact absurd rfl h
  | nd u s a2 _ iha =>
    intro Y _ hY
    cases a2 with
    | nil =>
      rw [toL_plugB_leaf, toL_nd, cmpS_append_left]
      rw [lastLvl_leaf] at hY
      exact hY
    | nd u2 s2 c2 =>
      rw [toL_plugB_rec, toL_nd, cmpS_append_left]
      show cmpS [(u, plugB (B.nd u2 s2 c2) Y)] [(u, (B.nd u2 s2 c2))] = .lt
      rw [cmpS_cons, if_neg (Nat.lt_irrefl u), if_neg (Nat.lt_irrefl u)]
      rw [iha Y (by intro hc; exact B.noConfusion hc) (by rw [← lastLvl_nd u s u2 s2 c2]; exact hY)]

/-! #### `visOK` の伝播 -/

/-- 走査で届いた引数の中の走査は、元の走査に含まれる。 -/
theorem visOK_of_vArgs_mem : ∀ (s : B) (v u : Nat) (ref z : B), v ≤ u →
    visOK v ref s = true → z ∈ vArgs u s → visOK v ref z = true := by
  intro s
  induction s with
  | nil => intro v u ref z _ _ hz; exact absurd hz (by intro hm; exact List.not_mem_nil hm)
  | nd u0 r c ihr ihc =>
    intro v u ref z hvu h hz
    rw [vArgs_nd] at hz
    rcases List.mem_append.mp hz with hz | hz
    · exact ihr v u ref z hvu (visOK_nd_r h) hz
    · by_cases hu : u0 < u
      · rw [if_pos hu] at hz; exact absurd hz (by intro hm; exact List.not_mem_nil hm)
      · have hv0 : ¬ (u0 < v) := by omega
        rw [if_neg hu] at hz
        rcases List.mem_append.mp hz with hz | hz
        · by_cases hv : (u0 == u) = true
          · rw [if_pos hv] at hz
            rw [List.mem_singleton.mp hz]
            exact visOK_nd_c hv0 h
          · rw [if_neg hv] at hz; exact absurd hz (by intro hm; exact List.not_mem_nil hm)
        · exact ihc v u ref z hvu (visOK_nd_c hv0 h) hz

/-- **`plugB` は基準を据え置いたまま `visOK` を保つ。** -/
theorem visOK_plugB : ∀ (a : B) (Y : B) (v : Nat) (ref : B),
    cmpS (toL Y) [(lastLvl a, (.nil : B))] = .lt →
    visOK v ref a = true → visOK v ref Y = true →
    visOK v ref (plugB a Y) = true := by
  intro a
  induction a with
  | nil => intro Y v ref _ _ _; rfl
  | nd u s a2 _ iha =>
    intro Y v ref hY h hYv
    cases a2 with
    | nil =>
      rw [plugB_nil_arg]
      refine (visOK_iff _ v ref).mpr ?_
      intro z hz
      rw [vArgs_appB] at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact (visOK_iff s v ref).mp (visOK_nd_r h) z hz
      · exact (visOK_iff Y v ref).mp hYv z hz
    | nd u2 s2 c2 =>
      rw [plugB_rec]
      have hY2 : cmpS (toL Y) [(lastLvl (B.nd u2 s2 c2), (.nil : B))] = .lt := by
        rw [← lastLvl_nd u s u2 s2 c2]; exact hY
      refine visOK_nd_mk (visOK_nd_r h)
        (fun hu => iha Y v ref hY2 (visOK_nd_c hu h) hYv) ?_
      intro hu huv
      exact cmpS_trans _ _ _
        (plugB_lt (B.nd u2 s2 c2) Y (by intro hc; exact B.noConfusion hc) hY2)
        (visOK_nd_arg hu huv h)

/-- 段が `v` より低い単一成分は `vArgs v` に何も足さない。 -/
theorem visOK_low_node (v v0 : Nat) (ref G : B) (h : v0 < v) :
    visOK v ref (.nd v0 .nil G) = true := by
  rw [visOK_nd_eq, if_pos h]
  rfl


/-! #### `plugB` への移送 -/

theorem lt_leaf_lvl {u0 : Nat} {z0 : B} {rest : List (Nat × B)} {w : Nat}
    (h : cmpS ((u0, z0) :: rest) [(w, (.nil : B))] = .lt) : u0 < w := by
  rw [cmpS_cons] at h
  by_cases h1 : u0 < w
  · exact h1
  · rw [if_neg h1] at h
    by_cases h2 : w < u0
    · rw [if_pos h2] at h; exact absurd h (by intro hc; exact Ordering.noConfusion hc)
    · rw [if_neg h2] at h
      exfalso
      cases hz : cmpS (toL z0) (toL (.nil : B)) with
      | lt => exact cmpS_nil_right_ne_lt (toL z0) hz
      | gt => rw [hz] at h; exact Ordering.noConfusion h
      | eq => rw [hz] at h; exact cmpS_nil_right_ne_lt rest h

theorem sizeL_pos : ∀ (l : List (Nat × B)), l ≠ [] → 0 < sizeL l
  | [], h => absurd rfl h
  | (u, a) :: l, _ => by rw [sizeL_cons]; omega

/-- **最内の差し替え (`Y = 0`) への移送。** 大きさの条件だけで通る。 -/
theorem C1_plugB_nil : ∀ (a : B) (x : B), sizeB x < sizeB (plugB a .nil) →
    cmpS (toL x) (toL a) = .lt → cmpS (toL x) (toL (plugB a .nil)) = .lt := by
  intro a
  induction a with
  | nil => intro x hs _; exact absurd hs (by rw [show sizeB (plugB (.nil : B) .nil) = 0 from rfl]; omega)
  | nd u s a2 _ iha =>
    intro x hs hlt
    cases a2 with
    | nil =>
      rw [plugB_nil_arg, show appB s (.nil : B) = s from rfl] at hs ⊢
      rw [toL_nd] at hlt
      rcases cmpS_split (toL x) (toL s) [(u, (.nil : B))] hlt with h1 | h2 | ⟨x', hne, hx, _⟩
      · exact h1
      · exfalso
        have : sizeB x = sizeB s := by rw [← sizeL_toL, h2, sizeL_toL]
        omega
      · exfalso
        have : sizeB x = sizeB s + sizeL x' := by
          rw [← sizeL_toL, hx, sizeL_append, sizeL_toL]
        have := sizeL_pos x' hne
        omega
    | nd u2 s2 c2 =>
      rw [plugB_rec] at hs ⊢
      rw [toL_nd] at hlt
      rw [toL_nd]
      rcases cmpS_split (toL x) (toL s) [(u, (B.nd u2 s2 c2))] hlt with h1 | h2 | ⟨x', hne, hx, hq⟩
      · exact cmpS_lt_append _ _ _ h1
      · rw [h2]; exact cmpS_lt_self_append (toL s) _ (List.cons_ne_nil _ _)
      · rw [hx, cmpS_append_left]
        cases x' with
        | nil => exact absurd rfl hne
        | cons y rest =>
          obtain ⟨u0, z0⟩ := y
          rw [cmpS_cons] at hq
          by_cases h1 : u0 < u
          · rw [cmpS_cons, if_pos h1]
          · rw [if_neg h1] at hq
            by_cases h2 : u < u0
            · rw [if_pos h2] at hq; exact Ordering.noConfusion hq
            · rw [if_neg h2] at hq
              have hu0 : u0 = u := by omega
              subst hu0
              have hz : cmpS (toL z0) (toL (B.nd u2 s2 c2)) = .lt := by
                cases hzz : cmpS (toL z0) (toL (B.nd u2 s2 c2)) with
                | lt => rfl
                | gt => rw [hzz] at hq; exact Ordering.noConfusion hq
                | eq => rw [hzz] at hq; exact absurd hq (cmpS_nil_right_ne_lt rest)
              have e1 : sizeB x = sizeB s + (sizeB z0 + 1 + sizeL rest) := by
                rw [← sizeL_toL, hx, sizeL_append, sizeL_toL]
                rfl
              have e2 : sizeB (B.nd u0 s (plugB (B.nd u2 s2 c2) .nil))
                  = sizeB s + 1 + sizeB (plugB (B.nd u2 s2 c2) .nil) := rfl
              rw [e1, e2] at hs
              rw [cmpS_cons, if_neg (Nat.lt_irrefl u0), if_neg (Nat.lt_irrefl u0),
                iha z0 (by omega) hz]

/-- **入れ子の差し替えへの移送。** 底では `BOT` に落とす。 -/
theorem C1_plugB_cons : ∀ (a : B) (w v' : Nat) (a0 G : B), v' + 1 = w →
    hasLowAnc w a = false → lastLvl a = w →
    (∀ z : B, nonIncr z = true → stdIn z = true →
       (∀ z' ∈ vArgs v' z, cmpS (toL z') (toL a0) = .lt) →
       cmpS (toL z) (toL a0) = .lt → sizeB z < sizeB G →
       cmpS (toL z) (toL G) = .lt) →
    ∀ (x : B), nonIncr x = true → stdIn x = true →
      (∀ z' ∈ vArgs v' x, cmpS (toL z') (toL a0) = .lt) →
      sizeB x < sizeB (plugB a (.nd v' .nil G)) → cmpS (toL x) (toL a) = .lt →
      cmpS (toL x) (toL (plugB a (.nd v' .nil G))) = .lt := by
  intro a
  induction a with
  | nil =>
    intro w v' a0 G _ _ _ _ x _ _ _ hs _
    exact absurd hs (by rw [show sizeB (plugB (.nil : B) (.nd v' .nil G)) = 0 from rfl]; omega)
  | nd u s a2 _ iha =>
    intro w v' a0 G hvw hLA hll BOT x hni hst hvis hs hlt
    cases a2 with
    | nil =>
      have huw : u = w := hll
      subst huw
      rw [plugB_nil_arg] at hs ⊢
      rw [toL_nd] at hlt
      rw [toL_appB, show toL (B.nd v' (.nil : B) G) = [(v', G)] from rfl]
      rcases cmpS_split (toL x) (toL s) [(u, (.nil : B))] hlt with h1 | h2 | ⟨x', hne, hx, hq⟩
      · exact cmpS_lt_append _ _ _ h1
      · rw [h2]; exact cmpS_lt_self_append (toL s) _ (List.cons_ne_nil _ _)
      · rw [hx, cmpS_append_left]
        cases x' with
        | nil => exact absurd rfl hne
        | cons y rest =>
          obtain ⟨u0, z0⟩ := y
          have hu0 : u0 < u := lt_leaf_lvl hq
          rw [cmpS_cons]
          by_cases h1 : u0 < v'
          · rw [if_pos h1]
          · rw [if_neg h1, if_neg (show ¬ (v' < u0) by omega)]
            have hmem : (u0, z0) ∈ toL x := by
              rw [hx]; exact List.mem_append_right _ (List.mem_cons_self ..)
            have hmv : z0 ∈ vArgs u0 x := mem_toL_vArgs x u0 z0 hmem
            obtain ⟨hnz, hsz⟩ := stdIn_vArgs x hst u0 z0 hmv
            have hvisx : visOK v' a0 x = true := (visOK_iff x v' a0).mpr hvis
            have hmv' : z0 ∈ vArgs v' x := by
              have : u0 = v' := by omega
              rw [← this]; exact hmv
            have hz0a0 : cmpS (toL z0) (toL a0) = .lt := hvis z0 hmv'
            have hvz0 : ∀ z' ∈ vArgs v' z0, cmpS (toL z') (toL a0) = .lt :=
              (visOK_iff z0 v' a0).mp
                (visOK_of_vArgs_mem x v' u0 a0 z0 (by omega) hvisx hmv)
            have e1 : sizeB x = sizeB s + (sizeB z0 + 1 + sizeL rest) := by
              rw [← sizeL_toL, hx, sizeL_append, sizeL_toL]
              rfl
            have e2 : sizeB (appB s (B.nd v' (.nil : B) G)) = sizeB s + (0 + 1 + sizeB G) := by
              rw [sizeB_appB]
              rfl
            rw [e1, e2] at hs
            rw [BOT z0 hnz hsz hvz0 hz0a0 (by omega)]
    | nd u2 s2 c2 =>
      have hLA2 : hasLowAnc w (B.nd u2 s2 c2) = false := by
        rw [hasLowAnc_nd] at hLA
        cases hd : hasLowAnc w (B.nd u2 s2 c2) with
        | false => rfl
        | true => rw [hd, Bool.or_true] at hLA; exact absurd hLA (by intro hc; exact Bool.noConfusion hc)
      have huw : ¬ (u < w) := by
        rw [hasLowAnc_nd] at hLA
        intro hc
        rw [show decide (u < w) = true from decide_eq_true hc, Bool.true_or] at hLA
        exact Bool.noConfusion hLA
      have hll2 : lastLvl (B.nd u2 s2 c2) = w := by rw [← lastLvl_nd u s u2 s2 c2]; exact hll
      rw [plugB_rec] at hs ⊢
      rw [toL_nd] at hlt
      rw [toL_nd]
      rcases cmpS_split (toL x) (toL s) [(u, (B.nd u2 s2 c2))] hlt with h1 | h2 | ⟨x', hne, hx, hq⟩
      · exact cmpS_lt_append _ _ _ h1
      · rw [h2]; exact cmpS_lt_self_append (toL s) _ (List.cons_ne_nil _ _)
      · rw [hx, cmpS_append_left]
        cases x' with
        | nil => exact absurd rfl hne
        | cons y rest =>
          obtain ⟨u0, z0⟩ := y
          rw [cmpS_cons] at hq
          by_cases h1 : u0 < u
          · rw [cmpS_cons, if_pos h1]
          · rw [if_neg h1] at hq
            by_cases h2 : u < u0
            · rw [if_pos h2] at hq; exact Ordering.noConfusion hq
            · rw [if_neg h2] at hq
              have hu0 : u0 = u := by omega
              subst hu0
              have hz : cmpS (toL z0) (toL (B.nd u2 s2 c2)) = .lt := by
                cases hzz : cmpS (toL z0) (toL (B.nd u2 s2 c2)) with
                | lt => rfl
                | gt => rw [hzz] at hq; exact Ordering.noConfusion hq
                | eq => rw [hzz] at hq; exact absurd hq (cmpS_nil_right_ne_lt rest)
              have hmem : (u0, z0) ∈ toL x := by
                rw [hx]; exact List.mem_append_right _ (List.mem_cons_self ..)
              have hmv : z0 ∈ vArgs u0 x := mem_toL_vArgs x u0 z0 hmem
              obtain ⟨hnz, hsz⟩ := stdIn_vArgs x hst u0 z0 hmv
              have hvisx : visOK v' a0 x = true := (visOK_iff x v' a0).mpr hvis
              have hvz0 : ∀ z' ∈ vArgs v' z0, cmpS (toL z') (toL a0) = .lt :=
                (visOK_iff z0 v' a0).mp
                  (visOK_of_vArgs_mem x v' u0 a0 z0 (by omega) hvisx hmv)
              have e1 : sizeB x = sizeB s + (sizeB z0 + 1 + sizeL rest) := by
                rw [← sizeL_toL, hx, sizeL_append, sizeL_toL]
                rfl
              have e2 : sizeB (B.nd u0 s (plugB (B.nd u2 s2 c2) (.nd v' .nil G)))
                  = sizeB s + 1 + sizeB (plugB (B.nd u2 s2 c2) (.nd v' .nil G)) := rfl
              rw [e1, e2] at hs
              rw [cmpS_cons, if_neg (Nat.lt_irrefl u0), if_neg (Nat.lt_irrefl u0),
                iha w v' a0 G hvw hLA2 hll2 BOT z0 hnz hsz hvz0 (by omega) hz]

/-- **`GG` への移送。** 入れ子の深さ `k` の帰納。 -/
theorem C1_GG : ∀ (k : Nat) (a0 : B) (w v' : Nat), v' + 1 = w →
    hasLowAnc w a0 = false → lastLvl a0 = w →
    ∀ (x : B), nonIncr x = true → stdIn x = true →
      (∀ z' ∈ vArgs v' x, cmpS (toL z') (toL a0) = .lt) →
      sizeB x < sizeB (GG v' a0 k) → cmpS (toL x) (toL a0) = .lt →
      cmpS (toL x) (toL (GG v' a0 k)) = .lt := by
  intro k
  induction k with
  | zero =>
    intro a0 w v' _ _ _ x _ _ _ hs hlt
    exact C1_plugB_nil a0 x hs hlt
  | succ j ih =>
    intro a0 w v' hvw hLA hll x hni hst hvis hs hlt
    exact C1_plugB_cons a0 w v' a0 (GG v' a0 j) hvw hLA hll
      (fun z h1 h2 h3 h4 h5 => ih a0 w v' hvw hLA hll z h1 h2 h3 h5 h4)
      x hni hst hvis hs hlt


/-! #### `GG` の基本性質 -/

theorem GG_lt (v' : Nat) (a0 : B) (hne : a0 ≠ .nil) (hv : v' < lastLvl a0) :
    ∀ (k : Nat), cmpS (toL (GG v' a0 k)) (toL a0) = .lt
  | 0 => plugB_lt a0 .nil hne (cmpS_nil_cons _ _)
  | j + 1 => by
      show cmpS (toL (plugB a0 (.nd v' .nil (GG v' a0 j)))) (toL a0) = .lt
      refine plugB_lt a0 _ hne ?_
      rw [show toL (B.nd v' (.nil : B) (GG v' a0 j)) = [(v', GG v' a0 j)] from rfl,
        cmpS_cons, if_pos hv]

theorem visOK_Z (v v' : Nat) (ref G : B)
    (hG : (v' == v) = true → cmpS (toL G) (toL ref) = .lt)
    (hGv : ¬ (v' < v) → visOK v ref G = true) : visOK v ref (.nd v' .nil G) = true :=
  visOK_nd_mk rfl hGv (fun _ huv => hG huv)

theorem visOK_GG (v v' : Nat) (a0 ref : B) (hne : a0 ≠ .nil) (hv : v' < lastLvl a0)
    (h0 : visOK v ref a0 = true)
    (hGref : (v' == v) = true → ∀ j, cmpS (toL (GG v' a0 j)) (toL ref) = .lt) :
    ∀ (k : Nat), visOK v ref (GG v' a0 k) = true
  | 0 => by
      show visOK v ref (plugB a0 .nil) = true
      exact visOK_plugB a0 .nil v ref (cmpS_nil_cons _ _) h0 rfl
  | j + 1 => by
      show visOK v ref (plugB a0 (.nd v' .nil (GG v' a0 j))) = true
      refine visOK_plugB a0 _ v ref ?_ h0 ?_
      · rw [show toL (B.nd v' (.nil : B) (GG v' a0 j)) = [(v', GG v' a0 j)] from rfl,
          cmpS_cons, if_pos hv]
      · exact visOK_Z v v' ref _ (fun huv => hGref huv j)
          (fun _ => visOK_GG v v' a0 ref hne hv h0 hGref j)

/-! #### `plugB` は降べきを保つ -/

theorem nonIncr_plugB : ∀ (a Y : B), a ≠ .nil → nonIncr a = true →
    nonIncrL (toL Y) = true → hdOK (lastLvl a, (.nil : B)) (toL Y) = true →
    cmpS (toL Y) [(lastLvl a, (.nil : B))] = .lt →
    nonIncr (plugB a Y) = true := by
  intro a
  induction a with
  | nil => intro Y h _ _ _ _; exact absurd rfl h
  | nd u s a2 _ iha =>
    intro Y _ hni hYni hYhd hYlt
    cases a2 with
    | nil =>
      show nonIncrL (toL (plugB (B.nd u s .nil) Y)) = true
      rw [toL_plugB_leaf]
      refine nonIncrL_subst (toL s) (u, (.nil : B)) (toL Y) ?_ hYni hYhd
      rw [← toL_nd]
      exact hni
    | nd u2 s2 c2 =>
      show nonIncrL (toL (plugB (B.nd u s (.nd u2 s2 c2)) Y)) = true
      rw [toL_plugB_rec]
      refine nonIncrL_subst (toL s) (u, (B.nd u2 s2 c2)) _ (by rw [← toL_nd]; exact hni) rfl ?_
      refine hdOK_of_not_lt _ (u, plugB (B.nd u2 s2 c2) Y) _ (cmpS_asymm ?_)
      rw [cmpS_cons, if_neg (Nat.lt_irrefl u), if_neg (Nat.lt_irrefl u),
        plugB_lt (B.nd u2 s2 c2) Y (by intro hc; exact B.noConfusion hc)
          (by rw [← lastLvl_nd u s u2 s2 c2]; exact hYlt)]

theorem nonIncr_GG (v' : Nat) (a0 : B) (hne : a0 ≠ .nil) (hv : v' < lastLvl a0)
    (hni : nonIncr a0 = true) : ∀ (k : Nat), nonIncr (GG v' a0 k) = true
  | 0 => by
      show nonIncr (plugB a0 .nil) = true
      exact nonIncr_plugB a0 .nil hne hni rfl rfl (cmpS_nil_cons _ _)
  | j + 1 => by
      show nonIncr (plugB a0 (.nd v' .nil (GG v' a0 j))) = true
      have hlt : cmpS (toL (B.nd v' (.nil : B) (GG v' a0 j))) [(lastLvl a0, (.nil : B))] = .lt := by
        rw [show toL (B.nd v' (.nil : B) (GG v' a0 j)) = [(v', GG v' a0 j)] from rfl,
          cmpS_cons, if_pos hv]
      refine nonIncr_plugB a0 _ hne hni rfl ?_ hlt
      exact hdOK_of_not_lt _ (v', GG v' a0 j) _ (cmpS_asymm hlt)


/-! #### `stdIn` と `plugB` -/

theorem hdOK_leaf (w : Nat) (Y : B) (h : cmpS (toL Y) [(w, (.nil : B))] = .lt) :
    hdOK (w, (.nil : B)) (toL Y) = true := by
  cases hY : toL Y with
  | nil => rfl
  | cons y ys =>
    rw [hY] at h
    obtain ⟨u0, z0⟩ := y
    have hu0 : u0 < w := lt_leaf_lvl h
    refine hdOK_of_not_lt _ (u0, z0) _ ?_
    rw [cmpS_cons, if_neg (show ¬ (w < u0) by omega), if_pos hu0]
    intro hc; exact Ordering.noConfusion hc

theorem stdIn_plugB : ∀ (a : B) (w v' : Nat) (a0 Y : B), v' + 1 = w →
    hasLowAnc w a = false → lastLvl a = w →
    cmpS (toL Y) [(w, (.nil : B))] = .lt →
    nonIncrL (toL Y) = true → stdIn Y = true →
    (∀ (u : Nat) (ref : B), w ≤ u → visOK u ref Y = true) →
    visOK v' a0 Y = true →
    visOK v' a0 a = true →
    stdIn a = true →
    (∀ (a' : B), hasLowAnc w a' = false → lastLvl a' = w →
      ∀ x : B, nonIncr x = true → stdIn x = true →
        (∀ z' ∈ vArgs v' x, cmpS (toL z') (toL a0) = .lt) →
        sizeB x < sizeB (plugB a' Y) → cmpS (toL x) (toL a') = .lt →
        cmpS (toL x) (toL (plugB a' Y)) = .lt) →
    stdIn (plugB a Y) = true := by
  intro a
  induction a with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; rfl
  | nd u s a2 _ iha =>
    intro w v' a0 Y hvw hLA hll hYlt hYni hYst hYvis hYv' hva hst hTR
    have hst4 : (stdIn s && nonIncr a2 && visOK u a2 a2 && stdIn a2) = true := hst
    obtain ⟨hst123, hsta2⟩ := (Bool.and_eq_true _ _).mp hst4
    obtain ⟨hst12, hvisa2⟩ := (Bool.and_eq_true _ _).mp hst123
    obtain ⟨hsts, hnia2⟩ := (Bool.and_eq_true _ _).mp hst12
    cases a2 with
    | nil =>
      rw [plugB_nil_arg, stdIn_appB, hsts, hYst]
      rfl
    | nd u2 s2 c2 =>
      have hLA2 : hasLowAnc w (B.nd u2 s2 c2) = false := by
        rw [hasLowAnc_nd] at hLA
        cases hd : hasLowAnc w (B.nd u2 s2 c2) with
        | false => rfl
        | true =>
          rw [hd, Bool.or_true] at hLA
          exact absurd hLA (by intro hc; exact Bool.noConfusion hc)
      have huw : ¬ (u < w) := by
        rw [hasLowAnc_nd] at hLA
        intro hc
        rw [show decide (u < w) = true from decide_eq_true hc, Bool.true_or] at hLA
        exact Bool.noConfusion hLA
      have hll2 : lastLvl (B.nd u2 s2 c2) = w := by rw [← lastLvl_nd u s u2 s2 c2]; exact hll
      have hne2 : (B.nd u2 s2 c2) ≠ .nil := by intro hc; exact B.noConfusion hc
      have hYlt2 : cmpS (toL Y) [(lastLvl (B.nd u2 s2 c2), (.nil : B))] = .lt := by
        rw [hll2]; exact hYlt
      have hva2 : visOK v' a0 (B.nd u2 s2 c2) := visOK_nd_c (show ¬ (u < v') by omega) hva
      have hIH : stdIn (plugB (B.nd u2 s2 c2) Y) = true :=
        iha w v' a0 Y hvw hLA2 hll2 hYlt hYni hYst hYvis hYv' hva2 hsta2 hTR
      have hnip : nonIncr (plugB (B.nd u2 s2 c2) Y) = true :=
        nonIncr_plugB _ Y hne2 hnia2 hYni (by rw [hll2]; exact hdOK_leaf w Y hYlt) hYlt2
      have hvp : visOK v' a0 (plugB (B.nd u2 s2 c2) Y) = true :=
        visOK_plugB _ Y v' a0 hYlt2 hva2 hYv'
      have hself : visOK u (plugB (B.nd u2 s2 c2) Y) (plugB (B.nd u2 s2 c2) Y) = true := by
        have h1 : visOK u (B.nd u2 s2 c2) (plugB (B.nd u2 s2 c2) Y) = true :=
          visOK_plugB _ Y u _ hYlt2 hvisa2 (hYvis u _ (by omega))
        refine (visOK_iff _ u _).mpr ?_
        intro z hz
        have hz1 : cmpS (toL z) (toL (B.nd u2 s2 c2)) = .lt :=
          (visOK_iff _ u _).mp h1 z hz
        obtain ⟨hnz, hstz⟩ := stdIn_vArgs _ hIH u z hz
        have hvz : ∀ z' ∈ vArgs v' z, cmpS (toL z') (toL a0) = .lt :=
          (visOK_iff z v' a0).mp
            (visOK_of_vArgs_mem _ v' u a0 z (by omega) hvp hz)
        exact hTR (B.nd u2 s2 c2) hLA2 hll2 z hnz hstz hvz (vArgs_size _ u z hz) hz1
      rw [plugB_rec, stdIn_nd_eq, hsts, hnip, hself, hIH]
      rfl


/-! #### `GG` の `stdIn` と自己 `visOK` -/

theorem visOK_self_GG (v' : Nat) (a0 : B) (w : Nat) (hvw : v' + 1 = w)
    (hne : a0 ≠ .nil) (hLA : hasLowAnc w a0 = false) (hll : lastLvl a0 = w)
    (hv0 : visOK v' a0 a0 = true) (k : Nat) (hst : stdIn (GG v' a0 k) = true) :
    visOK v' (GG v' a0 k) (GG v' a0 k) = true := by
  have hv : v' < lastLvl a0 := by rw [hll]; omega
  have h1 : visOK v' a0 (GG v' a0 k) = true :=
    visOK_GG v' v' a0 a0 hne hv hv0 (fun _ j => GG_lt v' a0 hne hv j) k
  refine (visOK_iff _ v' _).mpr ?_
  intro z hz
  have hz1 : cmpS (toL z) (toL a0) = .lt := (visOK_iff _ v' a0).mp h1 z hz
  obtain ⟨hnz, hstz⟩ := stdIn_vArgs _ hst v' z hz
  have hvz : ∀ z' ∈ vArgs v' z, cmpS (toL z') (toL a0) = .lt :=
    (visOK_iff z v' a0).mp (visOK_of_vArgs_mem _ v' v' a0 z (Nat.le_refl v') h1 hz)
  exact C1_GG k a0 w v' hvw hLA hll z hnz hstz hvz (vArgs_size _ v' z hz) hz1

theorem stdIn_GG (v' : Nat) (a0 : B) (w : Nat) (hvw : v' + 1 = w)
    (hne : a0 ≠ .nil) (hLA : hasLowAnc w a0 = false) (hll : lastLvl a0 = w)
    (hni0 : nonIncr a0 = true) (hst0 : stdIn a0 = true) (hv0 : visOK v' a0 a0 = true) :
    ∀ (k : Nat), stdIn (GG v' a0 k) = true
  | 0 => by
      show stdIn (plugB a0 .nil) = true
      exact stdIn_plugB a0 w v' a0 .nil hvw hLA hll (cmpS_nil_cons _ _) rfl rfl
        (fun _ _ _ => rfl) rfl hv0 hst0
        (fun a' _ _ x _ _ _ hs hlt => C1_plugB_nil a' x hs hlt)
  | j + 1 => by
      have hv : v' < lastLvl a0 := by rw [hll]; omega
      have hstj : stdIn (GG v' a0 j) = true :=
        stdIn_GG v' a0 w hvw hne hLA hll hni0 hst0 hv0 j
      have hYlt : cmpS (toL (B.nd v' (.nil : B) (GG v' a0 j))) [(w, (.nil : B))] = .lt := by
        rw [show toL (B.nd v' (.nil : B) (GG v' a0 j)) = [(v', GG v' a0 j)] from rfl,
          cmpS_cons, if_pos (show v' < w by omega)]
      have hYst : stdIn (B.nd v' (.nil : B) (GG v' a0 j)) = true := by
        rw [stdIn_nd_eq, nonIncr_GG v' a0 hne hv hni0 j,
          visOK_self_GG v' a0 w hvw hne hLA hll hv0 j hstj, hstj]
        rfl
      show stdIn (plugB a0 (.nd v' .nil (GG v' a0 j))) = true
      refine stdIn_plugB a0 w v' a0 _ hvw hLA hll hYlt rfl hYst
        (fun u ref hu => visOK_low_node u v' ref _ (by omega)) ?_ hv0 hst0 ?_
      · exact visOK_Z v' v' a0 _ (fun _ => GG_lt v' a0 hne hv j)
          (fun _ => visOK_GG v' v' a0 a0 hne hv hv0 (fun _ i => GG_lt v' a0 hne hv i) j)
      · exact fun a' hLA' hll' x hnx hsx hvx hs hlt =>
          C1_plugB_cons a' w v' a0 (GG v' a0 j) hvw hLA' hll'
            (fun z h1 h2 h3 h4 h5 => C1_GG j a0 w v' hvw hLA hll z h1 h2 h3 h5 h4)
            x hnx hsx hvx hs hlt


/-! ### §62.9 `rwB` の枝: 組み立て -/

theorem stdIn_toL_visOK : ∀ (s : B), stdIn s = true → ∀ (u : Nat) (c : B),
    (u, c) ∈ toL s → visOK u c c = true := by
  intro s
  induction s with
  | nil => intro _ u c hc; exact absurd hc (by intro hm; exact List.not_mem_nil hm)
  | nd u0 r c0 ihr _ =>
    intro h u c hc
    have h4 : (stdIn r && nonIncr c0 && visOK u0 c0 c0 && stdIn c0) = true := h
    obtain ⟨h123, _⟩ := (Bool.and_eq_true _ _).mp h4
    obtain ⟨h12, hv⟩ := (Bool.and_eq_true _ _).mp h123
    obtain ⟨hr, _⟩ := (Bool.and_eq_true _ _).mp h12
    rw [toL_nd] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ihr hr u c hc
    · have he : (u0, c0) = (u, c) := (List.mem_singleton.mp hc).symm
      injection he with h1 h2
      rw [← h1, ← h2]
      exact hv

/-- 最後の成分の引数だけを差し替える移送 (`repB` でも `rwB` でも同じ形)。 -/
theorem C1_rec_gen (u : Nat) (r a1 g : B) (x : B)
    (hIH : ∀ (z : B), nonIncr z = true → stdIn z = true → visOK u z z = true →
      sizeB z < sizeB g → cmpS (toL z) (toL a1) = .lt → cmpS (toL z) (toL g) = .lt)
    (hst : stdIn x = true)
    (hs : sizeB x < sizeB (B.nd u r g))
    (hlt : cmpS (toL x) (toL (B.nd u r a1)) = .lt) :
    cmpS (toL x) (toL (B.nd u r g)) = .lt := by
  rw [toL_nd] at hlt
  rw [toL_nd]
  rcases cmpS_split (toL x) (toL r) [(u, a1)] hlt with h1 | h2 | ⟨x', hne, hx, hq⟩
  · exact cmpS_lt_append _ _ _ h1
  · rw [h2]
    exact cmpS_lt_self_append (toL r) _ (List.cons_ne_nil _ _)
  · rw [hx, cmpS_append_left]
    cases x' with
    | nil => exact absurd rfl hne
    | cons y rest =>
      obtain ⟨u0, z0⟩ := y
      rw [cmpS_cons] at hq
      by_cases h1 : u0 < u
      · rw [cmpS_cons, if_pos h1]
      · rw [if_neg h1] at hq
        by_cases h2 : u < u0
        · rw [if_pos h2] at hq; exact Ordering.noConfusion hq
        · rw [if_neg h2] at hq
          have hu0 : u0 = u := by omega
          subst hu0
          have hz : cmpS (toL z0) (toL a1) = .lt := by
            cases hzz : cmpS (toL z0) (toL a1) with
            | lt => rfl
            | gt => rw [hzz] at hq; exact Ordering.noConfusion hq
            | eq => rw [hzz] at hq; exact absurd hq (cmpS_nil_right_ne_lt rest)
          have hmem : (u0, z0) ∈ toL x := by
            rw [hx]
            exact List.mem_append_right _ (List.mem_cons_self ..)
          obtain ⟨hnz, hsz⟩ := stdIn_vArgs x hst u0 z0 (mem_toL_vArgs x u0 z0 hmem)
          have hvz : visOK u0 z0 z0 = true := stdIn_toL_visOK x hst u0 z0 hmem
          have e1 : sizeB x = sizeB r + (sizeB z0 + 1 + sizeL rest) := by
            rw [← sizeL_toL, hx, sizeL_append, sizeL_toL]
            rfl
          have e2 : sizeB (B.nd u0 r g) = sizeB r + 1 + sizeB g := rfl
          rw [e1, e2] at hs
          rw [cmpS_cons, if_neg (Nat.lt_irrefl u0), if_neg (Nat.lt_irrefl u0),
            hIH z0 hnz hsz hvz (by omega) hz]

/-- 最も近い低い祖先の段は `w - 1` ちょうど。`nfLe` が効く唯一の場所。 -/
theorem lowAnc_lvl (w : Nat) : ∀ (a : B) (m : Nat), a ≠ .nil → hasLowAnc w a = false →
    lastLvl a = w → nfLe m a = true → w ≤ m := by
  intro a m hne hLA hll hnf
  cases a with
  | nil => exact absurd rfl hne
  | nd u s a2 =>
    obtain ⟨h1, _, _⟩ := (nfLe_nd_iff m u s a2).mp hnf
    cases a2 with
    | nil => rw [← hll]; exact h1
    | nd u2 s2 c2 =>
      rw [hasLowAnc_nd] at hLA
      have huw : ¬ (u < w) := by
        intro hc
        rw [show decide (u < w) = true from decide_eq_true hc, Bool.true_or] at hLA
        exact Bool.noConfusion hLA
      omega

/-- `rwB` は小さくするか、何もしない。 -/
theorem rwB_le : ∀ (a : B) (w n : Nat), lastLvl a = w →
    cmpS (toL (rwB w n a)) (toL a) = .lt ∨ rwB w n a = a := by
  intro a
  induction a with
  | nil => intro w n _; exact Or.inr rfl
  | nd v s a1 _ iha =>
    intro w n hll
    cases a1 with
    | nil => exact Or.inr rfl
    | nd u2 s2 c2 =>
      have hll2 : lastLvl (B.nd u2 s2 c2) = w := by rw [← lastLvl_nd v s u2 s2 c2]; exact hll
      rw [rwB_nd]
      by_cases h1 : hasLowAnc w (B.nd u2 s2 c2) = true
      · rw [if_pos h1]
        rcases iha w n hll2 with hlt | heq
        · refine Or.inl ?_
          rw [toL_nd, toL_nd, cmpS_append_left, cmpS_cons,
            if_neg (Nat.lt_irrefl v), if_neg (Nat.lt_irrefl v), hlt]
        · exact Or.inr (by rw [heq])
      · rw [if_neg h1]
        by_cases h2 : v < w
        · rw [if_pos h2, appB_iterD]
          refine Or.inl ?_
          rw [toL_nd, toL_nd, cmpS_append_left, cmpS_cons,
            if_neg (Nat.lt_irrefl v), if_neg (Nat.lt_irrefl v),
            GG_lt v (B.nd u2 s2 c2) (by intro hc; exact B.noConfusion hc)
              (by rw [hll2]; exact h2) n]
        · rw [if_neg h2]; exact Or.inr rfl

theorem nonIncr_rwB : ∀ (a : B) (w n : Nat), lastLvl a = w → nonIncr a = true →
    nonIncr (rwB w n a) = true := by
  intro a
  induction a with
  | nil => intro _ _ _ h; exact h
  | nd v s a1 _ _ =>
    intro w n hll hni
    have hni' : nonIncrL (toL s ++ [(v, a1)]) = true := by rw [← toL_nd]; exact hni
    cases a1 with
    | nil => exact hni
    | nd u2 s2 c2 =>
      have hll2 : lastLvl (B.nd u2 s2 c2) = w := by rw [← lastLvl_nd v s u2 s2 c2]; exact hll
      have hne2 : (B.nd u2 s2 c2) ≠ .nil := by intro hc; exact B.noConfusion hc
      rw [rwB_nd]
      by_cases h1 : hasLowAnc w (B.nd u2 s2 c2) = true
      · rw [if_pos h1]
        show nonIncrL (toL (B.nd v s (rwB w n (B.nd u2 s2 c2)))) = true
        rw [toL_nd]
        refine nonIncrL_subst (toL s) (v, (B.nd u2 s2 c2)) _ hni' rfl ?_
        refine hdOK_of_not_lt _ (v, rwB w n (B.nd u2 s2 c2)) _ ?_
        rcases rwB_le (B.nd u2 s2 c2) w n hll2 with hlt | heq
        · refine cmpS_asymm ?_
          rw [cmpS_cons, if_neg (Nat.lt_irrefl v), if_neg (Nat.lt_irrefl v), hlt]
        · rw [heq, cmpS_refl]
          intro hc; exact Ordering.noConfusion hc
      · rw [if_neg h1]
        by_cases h2 : v < w
        · rw [if_pos h2, appB_iterD]
          show nonIncrL (toL (B.nd v s (GG v (B.nd u2 s2 c2) n))) = true
          rw [toL_nd]
          refine nonIncrL_subst (toL s) (v, (B.nd u2 s2 c2)) _ hni' rfl ?_
          refine hdOK_of_not_lt _ (v, GG v (B.nd u2 s2 c2) n) _ (cmpS_asymm ?_)
          rw [cmpS_cons, if_neg (Nat.lt_irrefl v), if_neg (Nat.lt_irrefl v),
            GG_lt v (B.nd u2 s2 c2) hne2 (by rw [hll2]; exact h2) n]
        · rw [if_neg h2]; exact hni

theorem visOK_rwB : ∀ (a : B) (w n v : Nat) (ref : B), lastLvl a = w →
    visOK v ref a = true → visOK v ref (rwB w n a) = true := by
  intro a
  induction a with
  | nil => intro _ _ _ _ _ h; exact h
  | nd v0 s a1 _ iha =>
    intro w n v ref hll h
    cases a1 with
    | nil => exact h
    | nd u2 s2 c2 =>
      have hll2 : lastLvl (B.nd u2 s2 c2) = w := by rw [← lastLvl_nd v0 s u2 s2 c2]; exact hll
      have hne2 : (B.nd u2 s2 c2) ≠ .nil := by intro hc; exact B.noConfusion hc
      rw [rwB_nd]
      by_cases h1 : hasLowAnc w (B.nd u2 s2 c2) = true
      · rw [if_pos h1]
        refine visOK_nd_mk (visOK_nd_r h) (fun hu => iha w n v ref hll2 (visOK_nd_c hu h)) ?_
        intro hu huv
        rcases rwB_le (B.nd u2 s2 c2) w n hll2 with hlt | heq
        · exact cmpS_trans _ _ _ hlt (visOK_nd_arg hu huv h)
        · rw [heq]; exact visOK_nd_arg hu huv h
      · rw [if_neg h1]
        by_cases h2 : v0 < w
        · rw [if_pos h2, appB_iterD]
          have hv : v0 < lastLvl (B.nd u2 s2 c2) := by rw [hll2]; exact h2
          refine visOK_nd_mk (visOK_nd_r h) ?_ ?_
          · intro hu
            refine visOK_GG v v0 (B.nd u2 s2 c2) ref hne2 hv (visOK_nd_c hu h) ?_ n
            intro huv j
            exact cmpS_trans _ _ _ (GG_lt v0 _ hne2 hv j) (visOK_nd_arg hu huv h)
          · intro hu huv
            exact cmpS_trans _ _ _ (GG_lt v0 _ hne2 hv n) (visOK_nd_arg hu huv h)
        · rw [if_neg h2]; exact h

theorem C1_rwB : ∀ (a : B) (w n m : Nat), lastLvl a = w → nfLe m a = true →
    ∀ (x : B), nonIncr x = true → stdIn x = true →
      sizeB x < sizeB (rwB w n a) → cmpS (toL x) (toL a) = .lt →
      cmpS (toL x) (toL (rwB w n a)) = .lt := by
  intro a
  induction a with
  | nil => intro _ _ _ _ _ x _ _ _ hlt; exact hlt
  | nd v0 s a1 _ iha =>
    intro w n m hll hnf x hni hst hs hlt
    obtain ⟨_, _, hnf1⟩ := (nfLe_nd_iff m v0 s a1).mp hnf
    cases a1 with
    | nil => exact hlt
    | nd u2 s2 c2 =>
      have hll2 : lastLvl (B.nd u2 s2 c2) = w := by rw [← lastLvl_nd v0 s u2 s2 c2]; exact hll
      have hne2 : (B.nd u2 s2 c2) ≠ .nil := by intro hc; exact B.noConfusion hc
      rw [rwB_nd] at hs ⊢
      by_cases h1 : hasLowAnc w (B.nd u2 s2 c2) = true
      · rw [if_pos h1] at hs ⊢
        exact C1_rec_gen v0 s (B.nd u2 s2 c2) (rwB w n (B.nd u2 s2 c2)) x
          (fun z hz1 hz2 _ hz3 hz4 => iha w n (v0 + 1) hll2 hnf1 z hz1 hz2 hz3 hz4)
          hst hs hlt
      · rw [if_neg h1] at hs ⊢
        have hLA2 : hasLowAnc w (B.nd u2 s2 c2) = false := by
          cases hd : hasLowAnc w (B.nd u2 s2 c2) with
          | false => rfl
          | true => exact absurd hd h1
        by_cases h2 : v0 < w
        · rw [if_pos h2, appB_iterD] at hs ⊢
          have hvw : v0 + 1 = w := by
            have := lowAnc_lvl w (B.nd u2 s2 c2) (v0 + 1) hne2 hLA2 hll2 hnf1
            omega
          refine C1_rec_gen v0 s (B.nd u2 s2 c2) (GG v0 (B.nd u2 s2 c2) n) x ?_ hst hs hlt
          intro z hz1 hz2 hzv hz3 hz4
          refine C1_GG n (B.nd u2 s2 c2) w v0 hvw hLA2 hll2 z hz1 hz2 ?_ hz3 hz4
          intro z' hz'
          exact cmpS_trans _ _ _ ((visOK_iff z v0 z).mp hzv z' hz') hz4
        · rw [if_neg h2] at hs ⊢; exact hlt

theorem visOK_self_rwB (a : B) (w n m v : Nat) (hll : lastLvl a = w) (hnf : nfLe m a = true)
    (hst : stdIn (rwB w n a) = true) (h : visOK v a a = true) :
    visOK v (rwB w n a) (rwB w n a) = true := by
  refine (visOK_iff _ v _).mpr ?_
  intro z hz
  have h1 : cmpS (toL z) (toL a) = .lt :=
    (visOK_iff _ v a).mp (visOK_rwB a w n v a hll h) z hz
  obtain ⟨hnz, hstz⟩ := stdIn_vArgs _ hst v z hz
  exact C1_rwB a w n m hll hnf z hnz hstz (vArgs_size _ v z hz) h1

theorem stdIn_rwB : ∀ (a : B) (w n m : Nat), lastLvl a = w → nfLe m a = true →
    stdIn a = true → stdIn (rwB w n a) = true := by
  intro a
  induction a with
  | nil => intro _ _ _ _ _ h; exact h
  | nd v0 s a1 _ iha =>
    intro w n m hll hnf hst
    obtain ⟨_, _, hnf1⟩ := (nfLe_nd_iff m v0 s a1).mp hnf
    have hst4 : (stdIn s && nonIncr a1 && visOK v0 a1 a1 && stdIn a1) = true := hst
    obtain ⟨hst123, hsta1⟩ := (Bool.and_eq_true _ _).mp hst4
    obtain ⟨hst12, hvisa1⟩ := (Bool.and_eq_true _ _).mp hst123
    obtain ⟨hsts, hnia1⟩ := (Bool.and_eq_true _ _).mp hst12
    cases a1 with
    | nil => exact hst
    | nd u2 s2 c2 =>
      have hll2 : lastLvl (B.nd u2 s2 c2) = w := by rw [← lastLvl_nd v0 s u2 s2 c2]; exact hll
      have hne2 : (B.nd u2 s2 c2) ≠ .nil := by intro hc; exact B.noConfusion hc
      rw [rwB_nd]
      by_cases h1 : hasLowAnc w (B.nd u2 s2 c2) = true
      · rw [if_pos h1]
        have hIH : stdIn (rwB w n (B.nd u2 s2 c2)) = true :=
          iha w n (v0 + 1) hll2 hnf1 hsta1
        rw [stdIn_nd_eq, hsts, nonIncr_rwB _ w n hll2 hnia1,
          visOK_self_rwB _ w n (v0 + 1) v0 hll2 hnf1 hIH hvisa1, hIH]
        rfl
      · rw [if_neg h1]
        have hLA2 : hasLowAnc w (B.nd u2 s2 c2) = false := by
          cases hd : hasLowAnc w (B.nd u2 s2 c2) with
          | false => rfl
          | true => exact absurd hd h1
        by_cases h2 : v0 < w
        · rw [if_pos h2, appB_iterD]
          have hvw : v0 + 1 = w := by
            have := lowAnc_lvl w (B.nd u2 s2 c2) (v0 + 1) hne2 hLA2 hll2 hnf1
            omega
          have hv : v0 < lastLvl (B.nd u2 s2 c2) := by rw [hll2]; exact h2
          have hGst : stdIn (GG v0 (B.nd u2 s2 c2) n) = true :=
            stdIn_GG v0 _ w hvw hne2 hLA2 hll2 hnia1 hsta1 hvisa1 n
          rw [stdIn_nd_eq, hsts, nonIncr_GG v0 _ hne2 hv hnia1 n,
            visOK_self_GG v0 _ w hvw hne2 hLA2 hll2 hvisa1 n hGst, hGst]
          rfl
        · rw [if_neg h2]; exact hst

/-! ### §62.10 主定理と、狭めた領域 -/

/-- **`stdB` は `repB` で閉じている。** `nfB` は §19、残る 2 つが §62 の内容。 -/
theorem stdB_repB (t : B) (n : Nat) (h : stdB t = true) : stdB (repB t n) = true := by
  have h1 : nfB t = true := nfB_of_stdB t h
  have h2 : nonIncr t = true := nonIncr_of_stdB t h
  have h3 : stdIn t = true := stdIn_of_stdB t h
  show (nfB (repB t n) && nonIncr (repB t n) && stdIn (repB t n)) = true
  rw [show nfB (repB t n) = true from nfLe_repB t 0 n h1,
    nonIncr_repB t n h2, stdIn_repB t n h3]
  rfl

/-- **`stdB` は `rwB` で閉じている。** -/
theorem stdB_rwB (t : B) (w n : Nat) (hll : lastLvl t = w) (h : stdB t = true) :
    stdB (rwB w n t) = true := by
  have h1 : nfB t = true := nfB_of_stdB t h
  have h2 : nonIncr t = true := nonIncr_of_stdB t h
  have h3 : stdIn t = true := stdIn_of_stdB t h
  show (nfB (rwB w n t) && nonIncr (rwB w n t) && stdIn (rwB w n t)) = true
  rw [show nfB (rwB w n t) = true from nfLe_rwB t w n 0 h1,
    nonIncr_rwB t w n hll h2, stdIn_rwB t w n 0 hll h1 h3]
  rfl

/-- **主定理。標準性は基本列で閉じている。** §61 の (i) が定理になった。 -/
theorem stdB_fsB (t : B) (h : stdB t = true) (n : Nat) : stdB (fsB t n) = true := by
  cases t with
  | nil => exact rfl
  | nd v r a =>
    cases v with
    | zero =>
      cases a with
      | nil => exact stdB_pred r h
      | nd u s c =>
        show stdB (if (lastLvl (B.nd u s c) == 0) = true
          then repB (B.nd 0 r (B.nd u s c)) n
          else rwB (lastLvl (B.nd u s c)) n (B.nd 0 r (B.nd u s c))) = true
        by_cases hz : (lastLvl (B.nd u s c) == 0) = true
        · rw [if_pos hz]; exact stdB_repB _ n h
        · rw [if_neg hz]
          exact stdB_rwB _ (lastLvl (B.nd u s c)) n rfl h
    | succ k =>
      cases a with
      | nil => exact rfl
      | nd u s c =>
        show stdB (if (lastLvl (B.nd u s c) == 0) = true
          then repB (B.nd (k + 1) r (B.nd u s c)) n
          else rwB (lastLvl (B.nd u s c)) n (B.nd (k + 1) r (B.nd u s c))) = true
        by_cases hz : (lastLvl (B.nd u s c) == 0) = true
        · rw [if_pos hz]; exact stdB_repB _ n h
        · rw [if_neg hz]
          exact stdB_rwB _ (lastLvl (B.nd u s c)) n rfl h

/-- **`certIn_region` の第 1 供給、狭めた領域で。** -/
theorem hclosedS_supply : ∀ (S : Matrix), RegS S → ∀ (n : Nat), RegS (BMS.expand S n) := by
  rintro S ⟨t, hstd, rfl⟩ n
  cases t with
  | nil =>
    refine ⟨.nil, rfl, ?_⟩
    show ((BMS.expand? [] n).getD []) = []
    rfl
  | nd v r a =>
    refine ⟨fsB (B.nd v r a) n, stdB_fsB _ hstd n, ?_⟩
    show ((BMS.expand? (matB (B.nd v r a) 0) n).getD []) = _
    rw [expand_matB (B.nd v r a) (topOKB_of_nfB _ (nfB_of_stdB _ hstd))
      (by intro hc; exact B.noConfusion hc) n]
    rfl

/-! ### §62.11 測定 (凍結)

否定的なものから。`C1_repB` の素朴な `plugB` 版は**偽**で、これが §62.8–§62.9 が
基準を据え置く形の帰納になっている理由。 -/

-- **否定。** `C1_repB` の素朴な `plugB` 版は偽。最小の反例。
#guard
  (let a : B := .nd 1 .nil .nil                      -- ψ₁(0)
   let x : B := .nd 0 .nil (.nd 1 .nil .nil)         -- ψ₀(ψ₁(0))
   let g : B := plugB a (iterD 0 a 2)
   nonIncr x && stdIn x && decide (sizeB x < sizeB g)
     && (cmpS (toL x) (toL a) == Ordering.lt)
     && !(cmpS (toL x) (toL g) == Ordering.lt)
     && !(visOK 0 x x))                              -- これが落ちている側条件
#guard matB (.nd 1 (.nil : B) .nil) 0 == [[0, 1]]
#guard matB (.nd 0 (.nil : B) (.nd 1 .nil .nil)) 0 == [[0, 0], [1, 1]]

-- 肯定。§61 の (i) は定理になったが、受領として再測定を残す。
#guard (enumB 3 6).all fun t => !(stdB t) || (List.range 6).all fun n => stdB (fsB t n)
#guard (enumB 4 5).all fun t => !(stdB t) || (List.range 6).all fun n => stdB (fsB t n)
-- 二つの枝の内訳 (`repB` 側 / `rwB` 側)。
#guard ((enumB 3 6).filter fun t => stdB t && lastLvl t == 0).length == 741
#guard ((enumB 3 6).filter fun t => stdB t).length == 1105
#guard ((popNFB 3 6).filter fun t => stdB t && lastLvl t == 0).length == 161
#guard ((popNFB 3 6).filter stdB).length == 235
-- 326 行目の添字とその基本列。
#guard match decodeB [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1]] with
  | none => false
  | some t => stdB t && (List.range 6).all fun n => stdB (fsB t n)

-- **task 3 の測定。** `dict (bplus x y) = plus (dict x) (dict y)` は
-- `popNFB 3 6` の値の上で反例なし。**測定のみ、証明されていない。**
#guard (((popNFB 3 6).map bVal).eraseDups.take 40).all fun x =>
  (((popNFB 3 6).map bVal).eraseDups.take 40).all fun y =>
    Trans.Dict.dict (bplus x y) == TM.Term.plus (Trans.Dict.dict x) (Trans.Dict.dict y)
#guard (((popNFB 3 6).map bVal).eraseDups.take 80).all fun x =>
  Trans.Dict.dict (bplus x (BT.D 0 BT.zero)) == TM.Term.plus (Trans.Dict.dict x) TM.Term.one
-- `plus` の結合則が要るが、この repo の唯一のものは `CNV` を要求し、
-- 標準な値 235 個のうち `CNV` は 150 個しかない。
#guard (((popNFB 3 6).filter stdB).filter fun t => Evidence.WF.CNV (vOf t)).length == 150

/-! ### 公理の確認 -/

end

/-! ## §63 `plus` IS ASSOCIATIVE ON 𝔗(M), NOT ONLY ON THE VEBLEN FRAGMENT

`Evidence/CNVOps.lean` §19 proves `plus (plus a b) c = plus a (plus b c)` under `CNV`.
`CNV` admits only `zero`, `phi` and `add`, so it is the VEBLEN FRAGMENT and it excludes every
value that contains a `psi` or a `Z` — 85 of the 235 standard region values (§62.11's
`#guard`).  That is why §62 could not prove `dict (bplus x y) = plus (dict x) (dict y)` and had
to freeze it as a measurement.

WHAT THE §19 PROOF ACTUALLY USES.  Two things, and neither of them is `CNV`:

    (a) the components of a sum are additively principal and DESCEND;
    (b) `le` is transitive on the components.

`inT` says (a) verbatim — [Rathjen, 1991] 2.1(iii) is exactly `a.isAP && inT a && inT b` plus
`hdLe b a` — and §8.5.4 of `Evidence/WF.lean` says (b) verbatim: `le_trans_inT`.  So the whole
of §19 goes through one notch up, and this section restates it there.

MEASURED FIRST (all frozen as `#guard`s below).  Negative results first:

  * (a) is NOT optional.  With additively principal components but the DESCENT DROPPED the
    equation is false; the smallest counterexample found is `a = ω`, `b = 1 ⊕ ε₀`, `c = ω`
    (degree sum 19).  A component `zero` breaks it even sooner: `a = 1`, `b = 0 ⊕ ω`, `c = 1`.
  * (b) is NOT optional either, and this is the part that says `inT` — not merely "AP
    components, descending" — is the right hypothesis.  Over sums built from `ψ_M M`
    and `φ̄(ψ_M M)M` (terms that are AP, descending, and NOT `inT`, and on which §8.5.5's
    asymmetry counterexample lives) the equation FAILS.  So the structural condition alone
    is not enough: the components have to be genuinely comparable, and in this repository
    that is `FragR`, of which `inT` is the client-facing form.

  * POSITIVE: on all `inT` triples of two independent populations — the region's own 257
    distinct values `vOf` over `popNFB 3 6` (40³ triples measured, 25³ frozen below) and a
    hand enumeration of sums over `{1, ω, ε₀, Ω, Γ₀, ψ_{Z0}(Z1), Z1, M, ω^(M⊕1)}` (100³
    triples, frozen below) — zero counterexamples.

WHAT IS RESTATED.  Only what §63 itself needs, and each one is the §19 proof with `CNV`
replaced by `inT` and `frag_of_cnv`/`le_trans` replaced by `le_trans_inT`:
`inT_toList`, `inT_ofList_toList`, `filter_eq_take_inT`, `toList_plus_inT`,
`filter_nil_of_head_inT`, `inT_plus`, `plus_assoc_inT`.  `lt_ofList` (§20) is NOT restated —
§63 never reads the order off the component list.

WHAT IS NOT CLAIMED.  Nothing here says anything about `dict`, about `collapse`, or about the
values of the region; those are §63.3 and §63.4 below, and §63.4 does NOT close.
-/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term
open Evidence.WF

/-! ### §63.1 `plus` の結合則、`inT` の上で -/

/-- 成分がすべて加法主要かつ `inT` か (`cnvL` の `inT` 版)。 -/
def inTL (l : List Term) : Bool := l.all (fun x => x.isAP && inT x)

theorem inTL_cons {a : Term} {l : List Term} :
    inTL (a :: l) = true ↔ (a.isAP = true ∧ inT a = true) ∧ inTL l = true := by
  constructor
  · intro h
    have h' := (List.all_cons ..).symm.trans h
    have h2 := (Bool.and_eq_true _ _).mp h'
    exact ⟨(Bool.and_eq_true _ _).mp h2.1, h2.2⟩
  · intro ⟨⟨h1, h2⟩, h3⟩
    show ((a.isAP && inT a) && inTL l) = true
    rw [h1, h2, h3]
    rfl

theorem inTL_take (k : Nat) (l : List Term) (h : inTL l = true) : inTL (l.take k) = true := by
  show (l.take k).all _ = true
  rw [List.all_eq_true]
  intro x hx
  exact List.all_eq_true.mp h x (List.mem_of_mem_take hx)

/-- [Rathjen, 1991] 2.1(iii) を `hdLe` で書き直す。最後の連言はちょうど `hdLe b a`。 -/
theorem inT_add_eq (a b : Term) :
    inT (add a b) = (a.isAP && inT a && inT b && hdLe b a) := by
  show (a.isAP && inT a && inT b &&
      (match b with | add c _ => le c a | _ => b.isAP && le b a)) = _
  cases b with
  | zero => rfl
  | add _ _ => rfl
  | M => rfl | omg _ => rfl | phi _ _ => rfl | psi _ _ => rfl | Z _ => rfl

theorem inT_add {a b : Term} (h : inT (add a b) = true) :
    a.isAP = true ∧ inT a = true ∧ inT b = true ∧ hdLe b a = true := by
  rw [inT_add_eq] at h
  obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
  obtain ⟨h3, h4⟩ := (Bool.and_eq_true _ _).mp h1
  obtain ⟨h5, h6⟩ := (Bool.and_eq_true _ _).mp h3
  exact ⟨h5, h6, h4, h2⟩

/-- **𝔗(M) の項は、降順の加法主要成分の列。**  §19 の `cnv_toList` の `inT` 版。 -/
theorem inT_toList : ∀ (t : Term), inT t = true →
    inTL (toList t) = true ∧ descL (toList t) = true := by
  intro t
  induction t with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | M => intro h; exact ⟨inTL_cons.mpr ⟨⟨rfl, h⟩, rfl⟩, rfl⟩
  | omg a _ => intro h; exact ⟨inTL_cons.mpr ⟨⟨rfl, h⟩, rfl⟩, rfl⟩
  | phi a b _ _ => intro h; exact ⟨inTL_cons.mpr ⟨⟨rfl, h⟩, rfl⟩, rfl⟩
  | psi k a _ _ => intro h; exact ⟨inTL_cons.mpr ⟨⟨rfl, h⟩, rfl⟩, rfl⟩
  | Z a _ => intro h; exact ⟨inTL_cons.mpr ⟨⟨rfl, h⟩, rfl⟩, rfl⟩
  | add a b _ ihb =>
    intro h
    obtain ⟨hap, hia, hib, hhd⟩ := inT_add h
    obtain ⟨hcl, hdl⟩ := ihb hib
    have he : toList (add a b) = a :: toList b := rfl
    rw [he]
    refine ⟨inTL_cons.mpr ⟨⟨hap, hia⟩, hcl⟩, ?_⟩
    cases hb : toList b with
    | nil => rfl
    | cons c rest =>
      refine descL_cons.mpr ⟨?_, by rw [← hb]; exact hdl⟩
      rw [← hdLe_eq_of_toList (a := a) hb]
      exact hhd

theorem inTL_isAP {t : Term} (h : inT t = true) : ∀ x ∈ toList t, x.isAP = true := by
  intro x hx
  exact ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp (inT_toList t h).1 x hx)).1

theorem inTL_inT {t : Term} (h : inT t = true) : ∀ x ∈ toList t, inT x = true := by
  intro x hx
  exact ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp (inT_toList t h).1 x hx)).2

/-- 成分列から組み直す。`hdLe` が `b ≠ zero` を保証する。 -/
theorem inT_ofList_toList : ∀ (t : Term), inT t = true → ofList (toList t) = t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | M => intro _; rfl
  | omg _ _ => intro _; rfl
  | phi _ _ _ _ => intro _; rfl
  | psi _ _ _ _ => intro _; rfl
  | Z _ _ => intro _; rfl
  | add a b _ ihb =>
    intro h
    obtain ⟨_, _, hib, hhd⟩ := inT_add h
    have hbz : b ≠ zero := by
      intro hz; rw [hz] at hhd; exact Bool.noConfusion hhd
    show ofList (a :: toList b) = add a b
    cases hbl : toList b with
    | nil => exact absurd (toList_eq_nil b hbl) hbz
    | cons c u =>
      show add a (ofList (c :: u)) = add a b
      rw [← hbl, ihb hib]

theorem lt_of_not_le_inT {a b : Term} (ha : inT a = true) (hb : inT b = true)
    (h : le a b = false) : lt b a = true :=
  lt_of_not_le3 (inT_le_fragR a ha) (inT_le_fragR b hb) h

/-- 降順の列で `le b₁ ·` を通すのは、前を切り取るのと同じ (§17 の `inT` 版)。 -/
theorem filter_eq_take_inT : ∀ (b1 : Term) (l : List Term), inTL l = true → descL l = true →
    inT b1 = true → ∃ k, l.filter (fun a => le b1 a) = l.take k := by
  intro b1 l
  induction l with
  | nil => intro _ _ _; exact ⟨0, rfl⟩
  | cons a t ih =>
    intro hc hd hb1
    obtain ⟨⟨_, hia⟩, hct⟩ := inTL_cons.mp hc
    cases hle : le b1 a with
    | true =>
      obtain ⟨k, hk⟩ := ih hct (descL_tail hd) hb1
      refine ⟨k + 1, ?_⟩
      rw [List.filter_cons_of_pos (by rw [hle]), hk]
      rfl
    | false =>
      refine ⟨0, ?_⟩
      rw [List.filter_cons_of_neg (by rw [hle]; exact Bool.noConfusion)]
      have hnil : ∀ (u : List Term), inTL u = true → descL (a :: u) = true →
          u.filter (fun x => le b1 x) = [] := by
        intro u
        induction u with
        | nil => intro _ _; rfl
        | cons c v ihv =>
          intro hcu hdu
          obtain ⟨⟨_, hicv⟩, hcv⟩ := inTL_cons.mp hcu
          have hca' : le c a = true := (descL_cons.mp hdu).1
          have hnc : le b1 c = false := by
            cases hbc : le b1 c with
            | false => rfl
            | true =>
              exact absurd (le_trans_inT hb1 hicv hia hbc hca')
                (by rw [hle]; exact Bool.noConfusion)
          rw [List.filter_cons_of_neg (by rw [hnc]; exact Bool.noConfusion)]
          refine ihv hcv ?_
          cases v with
          | nil => rfl
          | cons d w =>
            refine descL_cons.mpr ⟨?_, descL_tail (descL_tail hdu)⟩
            exact le_trans_inT (inTL_cons.mp hcv).1.2 hicv hia
              (descL_cons.mp (descL_tail hdu)).1 hca'
      exact hnil t hct hd

/-- 先頭より上のものは、その後ろにも無い (§19 の `filter_nil_of_head` の `inT` 版)。 -/
theorem filter_nil_of_head_inT {b1 : Term} (hb1 : inT b1 = true) :
    ∀ (a : Term) (u : List Term), inT a = true → inTL u = true → descL (a :: u) = true →
      le b1 a = false → (a :: u).filter (fun x => le b1 x) = [] := by
  intro a u hia hcu hd hle
  rw [List.filter_cons_of_neg (by rw [hle]; exact Bool.noConfusion)]
  have hnil : ∀ (v : List Term), inTL v = true → descL (a :: v) = true →
      v.filter (fun x => le b1 x) = [] := by
    intro v
    induction v with
    | nil => intro _ _; rfl
    | cons c w ihw =>
      intro hcv hdv
      obtain ⟨⟨_, hicv⟩, hcw⟩ := inTL_cons.mp hcv
      have hca' : le c a = true := (descL_cons.mp hdv).1
      have hnc : le b1 c = false := by
        cases hbc : le b1 c with
        | false => rfl
        | true =>
          exact absurd (le_trans_inT hb1 hicv hia hbc hca')
            (by rw [hle]; exact Bool.noConfusion)
      rw [List.filter_cons_of_neg (by rw [hnc]; exact Bool.noConfusion)]
      refine ihw hcw ?_
      cases w with
      | nil => rfl
      | cons d z =>
        refine descL_cons.mpr ⟨?_, descL_tail (descL_tail hdv)⟩
        exact le_trans_inT (inTL_cons.mp hcw).1.2 hicv hia
          (descL_cons.mp (descL_tail hdv)).1 hca'
  exact hnil u hcu hd

/-- `plus` の成分列 (§19 の `toList_plus` の `inT` 版)。 -/
theorem toList_plus_inT {s t : Term} (hs : inT s = true) (ht : inT t = true)
    {b1 : Term} {rest : List Term} (hl : toList t = b1 :: rest) :
    toList (plus s t) = (toList s).filter (fun a => le b1 a) ++ toList t := by
  have hall : ∀ x ∈ (toList s).filter (fun a => le b1 a) ++ toList t, x.isAP = true := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact inTL_isAP hs x ((List.mem_filter.mp h).1)
    · exact inTL_isAP ht x h
  show toList (match toList t with
      | [] => s
      | b :: _ => ofList ((toList s).filter (fun a => le b a) ++ toList t)) = _
  rw [hl]
  show toList (ofList ((toList s).filter (fun a => le b1 a) ++ (b1 :: rest))) = _
  rw [hl] at hall
  rw [toList_ofList _ hall]

/-- **`plus` は 𝔗(M) の上で結合的。**  §19 `plus_assoc` の `CNV` を `inT` に落としたもの。 -/
theorem plus_assoc_inT (a b c : Term) (ha : inT a = true) (hb : inT b = true)
    (hc : inT c = true) : plus (plus a b) c = plus a (plus b c) := by
  obtain ⟨hca, hda⟩ := inT_toList a ha
  obtain ⟨hcb, hdb⟩ := inT_toList b hb
  obtain ⟨hcc, hdc⟩ := inT_toList c hc
  cases hC : toList c with
  | nil =>
    have hcz : c = zero := toList_eq_nil c hC
    rw [hcz]
    show plus (plus a b) zero = plus a (plus b zero)
    rfl
  | cons c1 C' =>
    rw [hC] at hcc hdc
    obtain ⟨⟨_, hic1⟩, _⟩ := inTL_cons.mp hcc
    cases hB : toList b with
    | nil =>
      have hbz : b = zero := toList_eq_nil b hB
      have h1 : plus a b = a := by rw [hbz]; rfl
      have h2 : plus b c = c := by
        rw [plus_eq (s := b) hC, hB]
        show ofList (([] : List Term) ++ toList c) = c
        show ofList (toList c) = c
        exact inT_ofList_toList c hc
      rw [h1, h2]
    | cons b1 B' =>
      rw [hB] at hcb hdb
      obtain ⟨⟨_, hib1⟩, hcB'⟩ := inTL_cons.mp hcb
      have hab : toList (plus a b) = (toList a).filter (fun x => le b1 x) ++ toList b :=
        toList_plus_inT ha hb hB
      have hbc : toList (plus b c) = (toList b).filter (fun x => le c1 x) ++ toList c :=
        toList_plus_inT hb hc hC
      have hL : plus (plus a b) c
          = ofList ((((toList a).filter (fun x => le b1 x) ++ toList b).filter
              (fun x => le c1 x)) ++ toList c) := by
        rw [plus_eq (s := plus a b) hC, hab]
      cases hcb1' : le c1 b1 with
      | true =>
        have hkeep : ((toList a).filter (fun x => le b1 x)).filter (fun x => le c1 x)
            = (toList a).filter (fun x => le b1 x) := by
          refine filter_self_of_all _ _ ?_
          intro x hx
          have hbx : le b1 x = true := (List.mem_filter.mp hx).2
          have hix : inT x = true := inTL_inT ha x (List.mem_filter.mp hx).1
          exact le_trans_inT hic1 hib1 hix hcb1' hbx
        have hhead : (toList b).filter (fun x => le c1 x)
            = b1 :: B'.filter (fun x => le c1 x) := by
          rw [hB]; exact List.filter_cons_of_pos (by rw [hcb1'])
        have hbc' : toList (plus b c)
            = b1 :: (B'.filter (fun x => le c1 x) ++ toList c) := by
          rw [hbc, hhead]; rfl
        rw [hL, plus_eq (s := a) hbc', hbc, List.filter_append, hkeep, hhead,
          List.append_assoc]
      | false =>
        have hbn : (toList b).filter (fun x => le c1 x) = [] := by
          rw [hB]; exact filter_nil_of_head_inT hic1 b1 B' hib1 hcB' hdb hcb1'
        have hswap : ((toList a).filter (fun x => le b1 x)).filter (fun x => le c1 x)
            = (toList a).filter (fun x => le c1 x) := by
          refine filter_of_imp _ _ _ ?_
          intro x hx hcx
          have hix : inT x = true := inTL_inT ha x hx
          have hbc1 : le b1 c1 = true := by
            have h1 : lt b1 c1 = true := lt_of_not_le_inT hic1 hib1 hcb1'
            show (b1 == c1 || lt b1 c1) = true
            rw [h1]
            exact Bool.or_true _
          exact le_trans_inT hib1 hic1 hix hbc1 hcx
        have hbc' : toList (plus b c) = c1 :: C' := by
          rw [hbc, hbn, hC]; rfl
        rw [hL, plus_eq (s := a) hbc', hbc, List.filter_append, hswap, hbn,
          List.append_nil, List.nil_append]

/-! ### §63.2 `plus` の閉包、`0 ⊕ ·`、`· ⊕ 1`

§17 の `cnv_plus` と §21 の `lt_plus_left` のうち §63 が使う分だけ。`lt_plus_left` は
§20 の `lt_ofList` を経由するが、`lt_ofList` は `eq_phi_of_isAP_cnv`(「`CNV` の加法主要項は
`φ̄`」) を使うので `inT` へはそのままでは上がらない。ここで要るのは `x = 1` の場合だけなので、
`Evidence/Cert.lean` §15.1 の一般加法主要版の節 (`lt_ap_add`, `plus_one_add`, `le_one_ap`) を
使って和の長さの帰納で直接示す。§20 は復元していない。 -/

theorem inT_ofList : ∀ (l : List Term), inTL l = true → descL l = true →
    inT (ofList l) = true
  | [], _, _ => rfl
  | [a], h, _ => (inTL_cons.mp h).1.2
  | a :: b :: t, h, hd => by
    obtain ⟨⟨hap, hia⟩, hrest⟩ := inTL_cons.mp h
    obtain ⟨hle, hd2⟩ := descL_cons.mp hd
    have hbap : b.isAP = true := (inTL_cons.mp hrest).1.1
    show inT (add a (ofList (b :: t))) = true
    rw [inT_add_eq, hap, hia, inT_ofList (b :: t) hrest hd2, hdLe_ofList hbap, hle]
    rfl

/-- **𝔗(M) は `plus` で閉じる。** §17 の `cnv_plus` の `inT` 版。 -/
theorem inT_plus {s t : Term} (hs : inT s = true) (ht : inT t = true) :
    inT (plus s t) = true := by
  obtain ⟨hcs, hds⟩ := inT_toList s hs
  obtain ⟨hct, hdt⟩ := inT_toList t ht
  show inT (match toList t with
            | [] => s
            | b1 :: _ => ofList ((toList s).filter (fun a => le b1 a) ++ toList t)) = true
  cases hl : toList t with
  | nil => exact hs
  | cons b1 rest =>
    rw [hl] at hct hdt
    obtain ⟨⟨_, hb1⟩, _⟩ := inTL_cons.mp hct
    obtain ⟨k, hk⟩ := filter_eq_take_inT b1 (toList s) hcs hds hb1
    show inT (ofList ((toList s).filter (fun a => le b1 a) ++ (b1 :: rest))) = true
    rw [hk]
    refine inT_ofList _ ?_ ?_
    · show ((toList s).take k ++ (b1 :: rest)).all _ = true
      rw [List.all_eq_true]
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact List.all_eq_true.mp (inTL_take k (toList s) hcs) x h
      · exact List.all_eq_true.mp hct x h
    · refine descL_append _ _ (descL_take k (toList s) hds) hdt ?_
      intro a b w ha hb
      injection hb with hb1eq _
      rw [← hb1eq]
      have hmem : a ∈ (toList s).filter (fun x => le b1 x) := by
        rw [hk]; exact getLast?_mem ha
      exact (List.mem_filter.mp hmem).2

/-- `0` は `plus` の左単位 (成分から組み直せる項の上で)。 -/
theorem plus_zero_left_inT {t : Term} (ht : inT t = true) : plus zero t = t := by
  cases hl : toList t with
  | nil => rw [toList_eq_nil t hl]; rfl
  | cons b1 rest =>
    rw [plus_eq (s := zero) hl]
    show ofList (([] : List Term) ++ toList t) = t
    rw [List.nil_append]
    exact inT_ofList_toList t ht

/-- **`v < v ⊕ 1`。** 和の長さの帰納。 -/
theorem lt_self_plus_one_inT : ∀ (v : Term), inT v = true → lt v (plus v one) = true := by
  intro v
  induction v with
  | zero => intro _; exact rfl
  | M => intro _; rw [Evidence.Cert.plus_one_ap rfl (Evidence.Cert.le_one_ap rfl),
      Evidence.Cert.lt_ap_add rfl M one]; exact Evidence.WF.le_self M
  | omg a _ => intro _; rw [Evidence.Cert.plus_one_ap rfl (Evidence.Cert.le_one_ap rfl),
      Evidence.Cert.lt_ap_add rfl (omg a) one]; exact Evidence.WF.le_self (omg a)
  | phi a b _ _ => intro _; rw [Evidence.Cert.plus_one_ap rfl (Evidence.Cert.le_one_ap rfl),
      Evidence.Cert.lt_ap_add rfl (phi a b) one]; exact Evidence.WF.le_self (phi a b)
  | psi k a _ _ => intro _; rw [Evidence.Cert.plus_one_ap rfl (Evidence.Cert.le_one_ap rfl),
      Evidence.Cert.lt_ap_add rfl (psi k a) one]; exact Evidence.WF.le_self (psi k a)
  | Z a _ => intro _; rw [Evidence.Cert.plus_one_ap rfl (Evidence.Cert.le_one_ap rfl),
      Evidence.Cert.lt_ap_add rfl (Z a) one]; exact Evidence.WF.le_self (Z a)
  | add a b _ ihb =>
    intro h
    obtain ⟨hap, _, hib, _⟩ := inT_add h
    have hone : le one a = true := Evidence.Cert.le_one_ap hap
    have hrec : lt b (plus b one) = true := ihb hib
    have hne : b ≠ plus b one := by
      intro hc; rw [← hc, Evidence.WF.lt_irrefl] at hrec; exact Bool.noConfusion hrec
    rw [Evidence.Cert.plus_one_add hone,
      Evidence.WF.lt_add_add (by intro hc; injection hc with _ h2; exact hne h2), if_pos rfl]
    exact hrec

end

/-! ## §63.3 `dict` DISTRIBUTES OVER `bplus`

`bplus x y` is `BT.ofL (x.toL ++ y.toL)` and `dict` is compositional over `.sum`
(`Trans/Dict.lean`'s `dict_sum`), so the content of

    dict (bplus x y) = plus (dict x) (dict y)

is the `toL`/`ofL` round trip of §53 plus §63.1's associativity.  §62.11 measured the equation
with ZERO counterexamples and NO side condition (40×40 region values, and the corollary on 80).

THE SIDE CONDITION THE PROOF NEEDS, HONESTLY.  Two, and neither is visible in the equation:

  * `NfSum x` and `NfSum y` (§53) — `ofL` is a section of `toL` only on terms already in
    that shape, so without it `dict (bplus x y)` and `plus (dict x) (dict y)` are statements
    about different terms.  `nfSum_bplus`/`nfSum_D`/`nfSum_zero` discharge it everywhere §63
    uses it, and `nfSum_bVal` below discharges it for the region's own values.
  * `inT (dict a) = true` for every component `a` of `x.toL ++ y.toL`.  This is where §63.1
    is consumed: the induction on `l1` peels one component and re-associates, and
    `plus_assoc_inT` wants all three arguments `inT`.  There is no way around it — §63.1's
    own measurement shows associativity is FALSE without it.

The second condition is not decoration either: `inT (dict ·)` is exactly the theorem this
repository does not have (`Evidence/RegionNext.lean` line 14637 and line 15126 both say so).
`CollapseInT` below isolates it to one line, and §63.4 carries it as a hypothesis rather than
pretending it is proved. -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT)
open TM TM.Term
open Trans.Dict (dict)

/-- 成分の像がすべて 𝔗(M) に入るなら、和の像も入る。 -/
theorem inT_dict_ofL : ∀ (l : List BT), (∀ x ∈ l, inT (dict x) = true) →
    inT (dict (BT.ofL l)) = true
  | [], _ => rfl
  | [a], h => h a (List.Mem.head _)
  | a :: b :: t, h => by
    show inT (dict (BT.sum a (BT.ofL (b :: t)))) = true
    rw [Trans.Dict.dict_sum]
    exact inT_plus (h a (List.Mem.head _))
      (inT_dict_ofL (b :: t) (fun z hz => h z (List.Mem.tail a hz)))

/-- **`dict` は成分列の連結を `plus` に送る。** §63.1 を消費するのはここ。 -/
theorem dict_ofL_append : ∀ (l1 l2 : List BT),
    (∀ x ∈ l1, inT (dict x) = true) → (∀ x ∈ l2, inT (dict x) = true) →
    dict (BT.ofL (l1 ++ l2)) = plus (dict (BT.ofL l1)) (dict (BT.ofL l2))
  | [], l2, _, h2 => by
    show dict (BT.ofL l2) = plus (dict BT.zero) (dict (BT.ofL l2))
    rw [show dict BT.zero = zero from rfl]
    exact (plus_zero_left_inT (inT_dict_ofL l2 h2)).symm
  | [a], l2, _, _ => by
    cases l2 with
    | nil => rfl
    | cons b t => exact Trans.Dict.dict_sum a (BT.ofL (b :: t))
  | a :: b :: t, l2, h1, h2 => by
    have hIH := dict_ofL_append (b :: t) l2 (fun z hz => h1 z (List.Mem.tail a hz)) h2
    show dict (BT.sum a (BT.ofL (b :: (t ++ l2))))
        = plus (dict (BT.sum a (BT.ofL (b :: t)))) (dict (BT.ofL l2))
    rw [Trans.Dict.dict_sum, Trans.Dict.dict_sum,
      show BT.ofL (b :: (t ++ l2)) = BT.ofL ((b :: t) ++ l2) from rfl, hIH]
    exact (plus_assoc_inT _ _ _ (h1 a (List.Mem.head _))
      (inT_dict_ofL (b :: t) (fun z hz => h1 z (List.Mem.tail a hz)))
      (inT_dict_ofL l2 h2)).symm

/-- **§63.3 の主定理。** -/
theorem dict_bplus (x y : BT) (hx : NfSum x) (hy : NfSum y)
    (hdx : ∀ a ∈ x.toL, inT (dict a) = true) (hdy : ∀ a ∈ y.toL, inT (dict a) = true) :
    dict (bplus x y) = plus (dict x) (dict y) := by
  show dict (BT.ofL (x.toL ++ y.toL)) = _
  rw [dict_ofL_append x.toL y.toL hdx hdy,
    show BT.ofL x.toL = x from hx, show BT.ofL y.toL = y from hy]

theorem dict_D0_zero : dict (BT.D 0 BT.zero) = one := by decide

theorem inT_one : inT one = true := by decide

/-- **`Hsucc` を開ける系。** -/
theorem dict_bplus_one (x : BT) (hx : NfSum x) (hdx : ∀ a ∈ x.toL, inT (dict a) = true) :
    dict (bplus x (BT.D 0 BT.zero)) = plus (dict x) one := by
  rw [dict_bplus x (BT.D 0 BT.zero) hx (nfSum_D 0 BT.zero) hdx
    (by intro a ha
        rw [List.mem_singleton.mp (show a ∈ [BT.D 0 BT.zero] from ha), dict_D0_zero]
        exact inT_one), dict_D0_zero]

end

/-! ## §63.4 THE VALUE HALF OF `Hsucc`, AND THE ONE FACT THAT IS MISSING

WHAT IS PROVED.  `vOf (nd 0 r nil) = plus (vOf r) 1` and `lt (vOf r) (vOf (nd 0 r nil))`, and
with §61's `hsuccS_index` the whole of `certIn_region`'s `Hsucc` supply for the narrowed
region — **conditionally on `CollapseInT`**.

WHAT IS NOT PROVED, AND IS NOT WEAKENED AWAY.  `CollapseInT` says

    ∀ u a, inT (dict (BT.D u a)) = true

— "the Buchholz collapse always lands in 𝔗(M)".  It is `Trans/Dict.lean`'s acceptance record
item (B), which that file states only as `#guard`s over three corpora.  It is MEASURED here
too (see the `#guard`s below): 1805 `BT` terms of a systematic enumeration that does NOT
filter by `BT.isStd`, and the 443 distinct components of `bVal` over `popNFB 3 6`, with zero
counterexamples.  Restricting it to `BT.isStd` would be WRONG for this client: the 443
components of the region's own values are not all `isStd` (measured below).

Proving it means proving `inT (collapse u x)` — the whole of `wcnf`/`mulL`/`divAP`/`phiNF`
and, for the strongly critical branch, [Rathjen, 1991] 2.1(vi)'s `(Kset κ α).all (· < α)`.
That is a section of its own and none of it is attempted here.

AND INDUCTING ON THE INDEX DOES NOT DODGE IT.  `inT_vOf` below is proved by structure on `B`
and needs no `stdB`, but the induction bottoms out at the components of `bVal t`, which
`atomsL_bVal` (§53) says are exactly the `BT.D w (bArg w c)` — and `dict` is NOT compositional
through `.D`: `dict (.D u a) = collapse u (dict a)` throws away the Buchholz syntax.  So the
index-side induction reaches the same wall from the other side; there is no region-restricted
version of item 3 that is cheaper than `inT (collapse ·)` itself.  Everything below therefore
takes `CollapseInT` as an explicit hypothesis, and `hsuccS_supply` cannot be handed to
`certIn_region` until it is discharged. -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT)
open TM TM.Term
open Trans.Dict (dict)

/-- **欠けている 1 つの事実。** Buchholz の崩壊の像が 𝔗(M) に入ること。証明されていない。 -/
def CollapseInT : Prop := ∀ (u : Nat) (a : BT), inT (dict (BT.D u a)) = true

-- `nfSum_bVal` (§56) と `atomsL_bVal` (§53) は既にある。ここで使う。

theorem dictAtoms_bVal (H : CollapseInT) (t : B) :
    ∀ a ∈ (bVal t).toL, inT (dict a) = true := by
  intro a ha
  obtain ⟨u, b, rfl⟩ := atomsL_bVal t a ha
  exact H u b

theorem inT_dict_bVal (H : CollapseInT) (t : B) : inT (dict (bVal t)) = true := by
  have h := inT_dict_ofL (bVal t).toL (dictAtoms_bVal H t)
  rwa [show BT.ofL (bVal t).toL = bVal t from nfSum_bVal t] at h

/-- **§63 の項目 3。** 領域の値は 𝔗(M) の項 — `CollapseInT` を仮定して、しかし `stdB` は不要。 -/
theorem inT_vOf (H : CollapseInT) (t : B) : inT (vOf t) = true := by
  cases t with
  | nil => exact rfl
  | nd w r c =>
    show inT (plus one (dict (bVal (B.nd w r c)))) = true
    exact inT_plus inT_one (inT_dict_bVal H _)

/-- **§63 の項目 4 の値の等式。** -/
theorem vOf_succ (H : CollapseInT) (r : B) : vOf (.nd 0 r .nil) = plus (vOf r) one := by
  cases r with
  | nil => exact rfl
  | nd w s c =>
    show plus one (dict (bVal (B.nd 0 (B.nd w s c) B.nil)))
        = plus (plus one (dict (bVal (B.nd w s c)))) one
    rw [show bVal (B.nd 0 (B.nd w s c) B.nil)
          = bplus (bVal (B.nd w s c)) (BT.D 0 BT.zero) from rfl,
      dict_bplus_one _ (nfSum_bVal _) (dictAtoms_bVal H _)]
    exact (plus_assoc_inT _ _ _ inT_one (inT_dict_bVal H _) inT_one).symm

theorem lt_vOf_succ (H : CollapseInT) (r : B) : lt (vOf r) (vOf (.nd 0 r .nil)) = true := by
  rw [vOf_succ H r]
  exact lt_self_plus_one_inT (vOf r) (inT_vOf H r)

/-- **`certIn_region` の `Hsucc` 供給、狭めた領域で。** `CollapseInT` に依存する。 -/
theorem hsuccS_supply (H : CollapseInT) :
    ∀ (S : BMS.Matrix) (v : TM.Term), RegS S → ValS S v → BMS.kind S = BMS.Kind.succ →
    ∃ u, v = plus u TM.Term.one ∧ inT v = true ∧ inT u = true ∧ lt u v = true
         ∧ ∀ n, ValS (BMS.expand S n) u := by
  intro S v hreg hval hk
  obtain ⟨r, hv, _, hexp⟩ := hsuccS_index S v hreg hval hk
  refine ⟨vOf r, ?_, ?_, inT_vOf H r, ?_, fun n => (hexp n).2⟩
  · rw [hv]; exact vOf_succ H r
  · rw [hv]; exact inT_vOf H _
  · rw [hv]; exact lt_vOf_succ H r

end

/-! ## §63.5 MEASURED (frozen)

Negative results first: the three ways `plus (plus a b) c = plus a (plus b c)` fails, one per
conjunct of the hypothesis it is proved under.  The third is the one that decides the design —
it says the hypothesis has to be `inT` and not merely "additively principal components,
descending", because the order is not even TOTAL outside `FragR`. -/

section
open Trans.Recal (bplus)
open TM TM.Term
open Trans.Dict (BT)

-- **否定 1.** 成分に `zero` が混ざると落ちる。`a = 1`, `b = 0 ⊕ ω`, `c = 1`。
#guard !((TM.Term.toList (add zero omega)).all (fun x => x.isAP))
#guard TM.Term.plus (TM.Term.plus one (add zero omega)) one
       != TM.Term.plus one (TM.Term.plus (add zero omega) one)

-- **否定 2.** 成分は加法主要でも、降順でないと落ちる。`a = ω`, `b = 1 ⊕ ε₀`, `c = ω` (次数和 19)。
#guard (TM.Term.toList (add one (phi one zero))).all (fun x => x.isAP)
#guard !(Evidence.WF.descL (TM.Term.toList (add one (phi one zero))))
#guard TM.Term.plus (TM.Term.plus omega (add one (phi one zero))) omega
       != TM.Term.plus omega (TM.Term.plus (add one (phi one zero)) omega)

-- **否定 3.** 加法主要かつ降順でも `inT` でないと落ちる。`a = c = ψ_M M`, `b = ψ_{ψ_M M} 0`
--   (次数和 11)。この 2 つは **比較不能** — `lt` がどちらの向きにも `false` で、
--   `plus` の篩 `le b₁ ·` はそこで意味を失う。`WF` §8.5.5 と同じ場所。
#guard !(inT (psi M M)) && !(inT (psi (psi M M) zero))
#guard !(TM.Term.lt (psi M M) (psi (psi M M) zero))
     && !(TM.Term.lt (psi (psi M M) zero) (psi M M))
#guard (psi M M) != (psi (psi M M) zero)
#guard TM.Term.plus (TM.Term.plus (psi M M) (psi (psi M M) zero)) (psi M M)
       != TM.Term.plus (psi M M) (TM.Term.plus (psi (psi M M) zero) (psi M M))

-- 肯定 1.  領域の値そのもの。`vOf` の相異なる像は 257 個、その先頭 25 個で 25³ 三つ組。
#guard ((popNFB 3 6).map vOf).eraseDups.length == 257
#guard ((popNFB 3 6).map vOf).eraseDups.all fun x => TM.Term.inT x
#guard (((popNFB 3 6).map vOf).eraseDups.take 25).all fun a =>
  (((popNFB 3 6).map vOf).eraseDups.take 25).all fun b =>
    (((popNFB 3 6).map vOf).eraseDups.take 25).all fun c =>
      TM.Term.plus (TM.Term.plus a b) c == TM.Term.plus a (TM.Term.plus b c)
-- `CNV` はこの母集団の 159 個にしか成り立たない。§19 が届かない理由。
#guard (((popNFB 3 6).map vOf).eraseDups.filter fun x => Evidence.WF.CNV x).length == 159

-- 肯定 2.  ψ・Z の原子を含む手作りの母集団 (`{1, ω, ε₀, Ω, Γ₀, ψ_{Z0}(Z1), Z1, M, ω^(M⊕1)}`
--   から作った 0〜3 成分の和のうち `inT` なもの) で、全三つ組。
private def at63 : List TM.Term :=
  [one, omega, phi one zero, Z zero, psi (Z zero) zero, psi (Z zero) (Z one),
   Z one, M, omg (add M one)]
private def raw63 : List TM.Term :=
  [zero] ++ at63
  ++ (at63.flatMap fun a => at63.map fun b => add a b)
  ++ (at63.flatMap fun a => at63.map fun b => add a (add b one))
  ++ (at63.map fun a => add a zero) ++ (at63.map fun a => add zero a)
  ++ (at63.flatMap fun a => at63.map fun b => add (add a b) one)
private def in63 : List TM.Term := raw63.filter fun x => TM.Term.inT x
#guard at63.all fun x => TM.Term.inT x
#guard raw63.length == 271
#guard in63.length == 100
#guard in63.all fun a => in63.all fun b => in63.all fun c =>
  TM.Term.plus (TM.Term.plus a b) c == TM.Term.plus a (TM.Term.plus b c)

-- 肯定 3.  §63.3 の等式 (§62.11 の再掲)。
#guard (((popNFB 3 6).map bVal).eraseDups.take 25).all fun x =>
  (((popNFB 3 6).map bVal).eraseDups.take 25).all fun y =>
    Trans.Dict.dict (bplus x y) == TM.Term.plus (Trans.Dict.dict x) (Trans.Dict.dict y)

-- 肯定 4.  §63.4 が仮定する `CollapseInT` の測定。**証明ではない。**
--   (i) 領域の値の成分 443 個すべて。
#guard ((popNFB 3 6).flatMap fun t => (bVal t).toL).eraseDups.length == 443
#guard ((popNFB 3 6).flatMap fun t => (bVal t).toL).eraseDups.all fun a =>
  TM.Term.inT (Trans.Dict.dict a)
--   **`BT.isStd` に制限してはいけない。** 領域の成分は全部が標準ではない。
#guard !(((popNFB 3 6).flatMap fun t => (bVal t).toL).eraseDups.all fun a => BT.isStd a)
--   (ii) `isStd` で絞らない `BT` の系統的な列挙 1805 個。
private def bseed63 : List BT := [.zero, .D 0 .zero, .D 1 .zero, .D 2 .zero, .D 0 (.D 1 .zero)]
private def bstep63 (l : List BT) : List BT :=
  l ++ (List.range 3).flatMap (fun u => l.map (fun a => BT.D u a))
    ++ (l.flatMap fun a => l.map fun b => BT.sum a b)
private def bcorp63 : List BT := (bstep63 (bstep63 bseed63).eraseDups).eraseDups
#guard bcorp63.length == 1805
#guard bcorp63.all fun a => TM.Term.inT (Trans.Dict.dict a)

end


/-! ## §64 `collapse` LANDS IN 𝔗(M) — EVERY OPERATOR BUT TWO, AND THE TWO ARE NAMED

§63 closed `Hsucc` for the generalised region except for one hypothesis:

    CollapseInT : ∀ (u : Nat) (a : BT), inT (dict (BT.D u a)) = true

i.e. `inT (collapse u (dict a))`.  §64 takes it apart operator by operator.  What comes out
is that `collapse` is `inT` for EVERY operator it uses except two, and the two are isolated,
stated, and measured rather than assumed silently.

WHAT IS PROVED, UNCONDITIONALLY.

  §64.1  `lt · M` is STRUCTURAL: `lt t M = hdBelowM t`, where `hdBelowM` reads the head
         component and answers `false` only for `M` and `ω̄^·` ([Rathjen, 1991] 2.3.2/2.3.3).
         With it, `lt (ofList l) M`, `lt (plus s t) M` and "every component of a term below
         `M` is below `M`" are all one step.  This is the toolkit the rest of §64 runs on:
         2.1(v) asks `α, β < M` of every `φ̄` and nothing in §63 could supply it.

  §64.2  one `inT`-preservation lemma per operator, each with its `lt · M` twin:
         `sub1`, `subAP`, `logOm`, `divAP`, `phiNFdefault`, `phiNFsucc`, `phiNF`, `omegaNF`,
         `ofNat`, `splitFin`.  `inT_omegaNF` needs NO side condition (the `ω̄^·` branch
         carries `M < α` itself); `inT_phiNF` needs exactly 2.1(v)'s `α, β < M`.

  §64.3  the component-list toolkit: a descending list of `inT` terms is bounded by its head
         (`descL_bound_inT` — the only place `le_trans_inT` is used), hence filtering keeps
         it descending (`descL_filter_inT`).

  §64.4  `wcnf` returns components that are `inT` and below `M` (`wcnf_spec`), by induction
         on the component list.

  §64.5  the fold: `stepF`/`idxOf`/`scanSt` copy `collapse`'s own fold, `collapse_eq` is
         `rfl`, and `fold_inv` carries the invariant "both accumulator slots are `inT` and
         below `M`" through it.  `inT_collapse`, `inT_dict` and `collapseInT_of_gaps` follow.

WHAT IS NOT PROVED, AND IS NOT WEAKENED AWAY.  Exactly three named hypotheses, and
`collapseInT_of_gaps` shows `CollapseInT` follows from them:

  (G1) `DivDescInT` — `divAP w` maps a descending list to a descending list, PROVIDED every
       member is `≥ w`.  **The side condition is not decoration: without it the statement is
       FALSE.**  Smallest counterexample found, `w = M`, `l = [M, Z0]` (degree sum 5):
       `divAP M M = 1` but `divAP M (Z0) = Z0`, so `[1, Z0]` is not descending.  With `w`
       restricted to R the smallest is `w = Z M`, `l = [Z M, Z 0]` (degree sum 7) — so
       "regular" does NOT rescue it and "every member `≥ w`" does: 0 failures on 82 373
       (w, l) pairs.  This is `Evidence/CNVOps.lean` §27–§29's `omegaNF_mono` one notch up
       (`CNV` → `inT`), and that is why it is not proved here: `DnFacts` is a theorem for
       `CNV` only, and its `inT` version is a section of its own.

  (G2) `MulDescInT` — the same for `mulL`'s map `p ↦ ω^(e ⊕ logOm p)`.  Here NO side
       condition was needed: 0 failures on 274 576 `inT` pairs.  Both (G1) and (G2) were
       re-measured on a SECOND, independently seeded population of 80 deeper terms
       (max degree 12): 0 failures on 2324 and 6400 pairs respectively.

  (G3) `PsiIdxOK u x` — [Rathjen, 1991] 2.1(vi)'s LAST conjunct, `K_κ α < α`, for the indices
       the strongly critical branch actually emits.  It is stated over `scanSt`, the list of
       (state, component) pairs the fold really visits, so it says nothing about indices the
       fold never builds.  **It is not vacuous and it is not free**: on a hand corpus of 463
       `inT` terms below `M` it FAILS 17 times at `u = 0`.  Smallest by degree, `x = ψ_{ZM}(ZM)`
       (degree 5): the whole of `x` is below `Ω = Z0`, so `wcnf` hands the fold one component
       with exponent `≥ Ω`, the emitted index is `x` itself, and `K_Ω x = {ZM}` — which is NOT
       `< x`, so `ψ_Ω x` is not a term.  On `dict`'s image — 1805 systematically enumerated
       `BT` terms, `BT.isStd` NOT applied — it holds for every one of them at `u = 0,1,2,3`.

  For the fragment where the strongly critical branch never fires, (G3) is discharged:
  `inT_collapse_noSC` needs only (G1) and (G2).  That fragment is 743 of the 1805 at `u = 0`,
  1804 of 1805 at `u = 1` and all of them at `u = 2`.

WHAT IS NOT CLAIMED.  `CollapseInT` is NOT discharged.  Nothing here says `dict`'s image is
characterised; (G3) is stated for a given `x` and MEASURED on `dict`'s image, not proved
there.  The order-theoretic content of (G1)/(G2) — monotonicity of `ω^·` on `inT` — and the
Kset content of (G3) are the two things a next attempt has to buy.

**CORRECTION (§65).  `DivDescInT` as stated here is FALSE** — `not_divDescInT` proves it,
smallest counterexample `w = ω`, `l = [ω^ω, ω]`.  So every theorem of this section that takes
it as a hypothesis (`wcnf_spec`, `inT_collapse`, `inT_collapse_noSC`, `inT_dict`,
`collapseInT_of_gaps`, `hsuccS_supply_of_gaps`) is VACUOUS and must not be used.  §65 restates
them against `DivDescSC`, which adds `w.isSC` and IS proved; the live consumers are
`collapseInT_of_gap3` and `hsuccS_supply_of_gap3`, whose only hypothesis is (G3).
-/


/-! ### §64.1 `M` の下 — `lt · M` は頭部だけで決まる

[Rathjen, 1991] 2.3.2 (`φ̄, ψ, Z < M`) と 2.3.3 (`M < ω̄^γ`) を、和の頭部を読むだけの判定
`hdBelowM` にまとめる。2.1(v) の 2 つの側条件はすべてここから出る。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

/-- `M` より小さいか。和は頭部成分だけで決まる ([Rathjen, 1991] 2.3.2, 2.3.3, 2.3.10)。 -/
def hdBelowM : Term → Bool
  | M => false
  | omg _ => false
  | add a _ => hdBelowM a
  | _ => true

theorem inT_zero : inT (zero : Term) = true := rfl
theorem inT_M : inT (M : Term) = true := rfl

theorem lt_zero_M : lt zero M = true := by
  rw [Evidence.WF.lt_eq_ltF zero M ((zero : Term).deg + (M : Term).deg) (Nat.le_refl _)]; rfl

theorem lt_M_M : lt M M = false := by
  rw [Evidence.WF.lt_eq_ltF M M ((M : Term).deg + (M : Term).deg) (Nat.le_refl _)]; rfl

theorem lt_omg_M (a : Term) : lt (omg a) M = false := by
  rw [Evidence.WF.lt_eq_ltF (omg a) M ((omg a).deg + (M : Term).deg) (Nat.le_refl _)]
  show (if ((omg a) == M) = true then false else false) = false
  rw [show (((omg a) == M) : Bool) = false from rfl]; rfl

theorem lt_psi_M (k a : Term) : lt (psi k a) M = true := by
  rw [Evidence.WF.lt_eq_ltF (psi k a) M ((psi k a).deg + (M : Term).deg) (Nat.le_refl _)]
  show (if ((psi k a) == M) = true then false else true) = true
  rw [show (((psi k a) == M) : Bool) = false from rfl]; rfl

theorem lt_Z_M (a : Term) : lt (Z a) M = true := by
  rw [Evidence.WF.lt_eq_ltF (Z a) M ((Z a).deg + (M : Term).deg) (Nat.le_refl _)]
  show (if ((Z a) == M) = true then false else true) = true
  rw [show (((Z a) == M) : Bool) = false from rfl]; rfl

theorem lt_one_M : lt one M = true := lt_phi_M zero zero

/-- **`lt · M` は構造的。** -/
theorem lt_M_eq : ∀ (t : Term), lt t M = hdBelowM t
  | zero => lt_zero_M
  | M => lt_M_M
  | omg a => lt_omg_M a
  | phi a b => lt_phi_M a b
  | psi k a => lt_psi_M k a
  | Z a => lt_Z_M a
  | add a b => by rw [lt_add_M a b, lt_M_eq a]; rfl

theorem lt_ofList_M : ∀ (l : List Term), (∀ x ∈ l, lt x M = true) → lt (ofList l) M = true
  | [], _ => lt_zero_M
  | [a], h => h a (List.Mem.head _)
  | a :: b :: t, h => by
    show lt (add a (ofList (b :: t))) M = true
    rw [lt_add_M]
    exact h a (List.Mem.head _)

theorem lt_M_of_le {y a : Term} (hy : inT y = true) (ha : inT a = true)
    (hle : le y a = true) (hla : lt a M = true) : lt y M = true := by
  rcases (Bool.or_eq_true _ _).mp hle with h | h
  · rw [show y = a from eq_of_beq h]; exact hla
  · exact lt_trans_inT hy ha inT_M h hla

theorem ltM_of_hdLe : ∀ {a b : Term}, inT a = true → inT b = true →
    hdLe b a = true → lt a M = true → lt b M = true := by
  intro a b hia hib hhd hla
  cases b with
  | zero => exact Bool.noConfusion hhd
  | M => exact lt_M_of_le hib hia hhd hla
  | omg c => exact lt_M_of_le hib hia hhd hla
  | phi c d => exact lt_M_of_le hib hia hhd hla
  | psi c d => exact lt_M_of_le hib hia hhd hla
  | Z c => exact lt_M_of_le hib hia hhd hla
  | add c d =>
    obtain ⟨_, hic, _, _⟩ := inT_add hib
    rw [lt_add_M]
    exact lt_M_of_le hic hia hhd hla

/-- `M` より下の項の成分はすべて `M` より下。 -/
theorem ltM_toList : ∀ (s : Term), inT s = true → lt s M = true →
    ∀ x ∈ toList s, lt x M = true := by
  intro s
  induction s with
  | zero => intro _ _ x hx; cases hx
  | M => intro _ h x hx; rw [List.mem_singleton.mp hx]; exact h
  | omg a _ => intro _ h x hx; rw [List.mem_singleton.mp hx]; exact h
  | phi a b _ _ => intro _ h x hx; rw [List.mem_singleton.mp hx]; exact h
  | psi k a _ _ => intro _ h x hx; rw [List.mem_singleton.mp hx]; exact h
  | Z a _ => intro _ h x hx; rw [List.mem_singleton.mp hx]; exact h
  | add a b _ ihb =>
    intro h hl x hx
    obtain ⟨hap, hia, hib, hhd⟩ := inT_add h
    have hla : lt a M = true := by rw [← lt_add_M a b]; exact hl
    have hlb : lt b M = true := ltM_of_hdLe hia hib hhd hla
    rcases List.mem_cons.mp (show x ∈ a :: toList b from hx) with h1 | h1
    · rw [h1]; exact hla
    · exact ihb hib hlb x h1

theorem lt_plus_M {s t : Term} (hs : inT s = true) (ht : inT t = true)
    (hls : lt s M = true) (hlt : lt t M = true) : lt (plus s t) M = true := by
  cases hl : toList t with
  | nil => rw [show plus s t = s from by unfold TM.Term.plus; rw [hl]]; exact hls
  | cons b1 rest =>
    rw [plus_eq (s := s) hl]
    refine lt_ofList_M _ ?_
    intro x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact ltM_toList s hs hls x (List.mem_filter.mp h1).1
    · exact ltM_toList t ht hlt x h1

end

/-! ### §64.2 演算ごとの `inT` 保存

`Trans/Dict.lean` の `collapse` が使う演算を 1 つずつ。どれも「`inT` を保つ」と
「`M` の下に留まる」を対にして出す。 -/

section
open Trans.Recal (bplus)
open TM TM.Term
open Evidence.WF
open Trans.Dict (sub1 subAP logOm divAP)

theorem inT_ofNat : ∀ n, inT (ofNat n) = true
  | 0 => rfl
  | n + 1 => inT_plus (inT_ofNat n) inT_one

theorem ltM_ofNat : ∀ n, lt (ofNat n) M = true
  | 0 => lt_zero_M
  | n + 1 => lt_plus_M (inT_ofNat n) inT_one (ltM_ofNat n) lt_one_M

/-- 2.1(v) の 4 つの連言。 -/
theorem inT_phi4 {a b : Term} (h : inT (phi a b) = true) :
    inT a = true ∧ inT b = true ∧ lt a M = true ∧ lt b M = true := by
  have h' : (inT a && inT b && lt a M && lt b M) = true := h
  obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h'
  obtain ⟨h3, h4⟩ := (Bool.and_eq_true _ _).mp h1
  obtain ⟨h5, h6⟩ := (Bool.and_eq_true _ _).mp h3
  exact ⟨h5, h6, h4, h2⟩

theorem inT_phi_intro {a b : Term} (hia : inT a = true) (hib : inT b = true)
    (hla : lt a M = true) (hlb : lt b M = true) : inT (phi a b) = true := by
  show (inT a && inT b && lt a M && lt b M) = true
  rw [hia, hib, hla, hlb]; rfl

theorem inT_phiNFdefault {a b : Term} (hia : inT a = true) (hib : inT b = true)
    (hla : lt a M = true) (hlb : lt b M = true) : inT (phiNFdefault a b) = true := by
  unfold phiNFdefault
  split
  · exact hia
  · exact inT_phi_intro hia hib hla hlb

theorem ltM_phiNFdefault {a b : Term} (hla : lt a M = true) :
    lt (phiNFdefault a b) M = true := by
  unfold phiNFdefault
  split
  · exact hla
  · exact lt_phi_M a b

theorem inT_take_ofList {b : Term} (h : inT b = true) (k : Nat) :
    inT (ofList ((toList b).take k)) = true := by
  obtain ⟨hc, hd⟩ := inT_toList b h
  exact inT_ofList _ (inTL_take k _ hc) (descL_take k _ hd)

theorem ltM_take_ofList {b : Term} (h : inT b = true) (hl : lt b M = true) (k : Nat) :
    lt (ofList ((toList b).take k)) M = true :=
  lt_ofList_M _ (fun x hx => ltM_toList b h hl x (List.mem_of_mem_take hx))

theorem inT_splitFin {b : Term} (h : inT b = true) : inT (splitFin b).1 = true :=
  inT_take_ofList h _

theorem ltM_splitFin {b : Term} (h : inT b = true) (hl : lt b M = true) :
    lt (splitFin b).1 M = true := ltM_take_ofList h hl _

theorem inT_phiNFsucc {a b : Term} (hia : inT a = true) (hib : inT b = true)
    (hla : lt a M = true) (hlb : lt b M = true) : inT (phiNFsucc a b) = true := by
  have hdef := inT_phiNFdefault hia hib hla hlb
  have hg : inT (splitFin b).1 = true := inT_splitFin hib
  have hgm : lt (splitFin b).1 M = true := ltM_splitFin hib hlb
  unfold phiNFsucc
  split
  rename_i heq
  rw [heq] at hg hgm
  split
  · split <;> (split <;>
      first
        | exact inT_phi_intro hia (inT_plus hg (inT_ofNat _)) hla
            (lt_plus_M hg (inT_ofNat _) hgm (ltM_ofNat _))
        | exact hdef)
  · exact hdef

theorem ltM_phiNFsucc {a b : Term} (hla : lt a M = true) :
    lt (phiNFsucc a b) M = true := by
  have hdef := ltM_phiNFdefault (b := b) hla
  unfold phiNFsucc
  split
  rename_i heq
  split
  · split <;> (split <;> first | exact lt_phi_M _ _ | exact hdef)
  · exact hdef

/-- **`φαβ` は 𝔗(M) に留まる** — 2.1(v) の 2 つの側条件つき。 -/
theorem inT_phiNF {a b : Term} (hia : inT a = true) (hib : inT b = true)
    (hla : lt a M = true) (hlb : lt b M = true) : inT (phiNF a b) = true := by
  unfold phiNF
  split
  · exact hib
  · split
    · split
      · exact hib
      · exact inT_phiNFsucc hia hib hla hlb
    · exact inT_phiNFsucc hia hib hla hlb

theorem ltM_phiNF {a b : Term} (hla : lt a M = true) (hlb : lt b M = true) :
    lt (phiNF a b) M = true := by
  unfold phiNF
  split
  · exact hlb
  · split
    · split
      · exact hlb
      · exact ltM_phiNFsucc hla
    · exact ltM_phiNFsucc hla

theorem ltM_of_not_gt {x : Term} (hx : inT x = true) (h1 : lt M x = false)
    (h2 : (x == M) = false) : lt x M = true := by
  rcases lt_trichotomy_inT hx inT_M with ⟨h, _, _⟩ | ⟨_, he, _⟩ | ⟨_, _, h⟩
  · exact h
  · exact absurd (beq_of_eq he) (by rw [h2]; exact Bool.noConfusion)
  · exact absurd h (by rw [h1]; exact Bool.noConfusion)

/-- **`ω^α` は 𝔗(M) に留まる** — 側条件なし。`ω̄^·` の枝は 2.1(iv) の `M < α` を自分で持つ。 -/
theorem inT_omegaNF {x : Term} (hx : inT x = true) : inT (omegaNF x) = true := by
  unfold omegaNF
  split
  · rename_i h
    show (inT x && lt M x) = true
    rw [hx, h]; rfl
  · split
    · exact inT_M
    · rename_i h1 h2
      exact inT_phiNF inT_zero hx lt_zero_M
        (ltM_of_not_gt hx (bool_false h1) (bool_false h2))

theorem ltM_omegaNF {x : Term} (hx : inT x = true) (hlx : lt x M = true) :
    lt (omegaNF x) M = true := by
  unfold omegaNF
  split
  · rename_i h
    exact absurd hlx (by rw [lt_asymm_inT inT_M hx h]; exact Bool.noConfusion)
  · split
    · rename_i h1 h2
      exact absurd hlx (by rw [eq_of_beq h2, lt_M_M]; exact Bool.noConfusion)
    · exact ltM_phiNF lt_zero_M hlx

/-- `sub1` と `subAP` は同じ形 — 先頭を落とすか、そのまま返すか。 -/
theorem inT_dropIfHead {c : Term} (h : inT c = true) (P : Term → Bool) :
    inT (match toList c with
         | [] => zero
         | p :: rest => if P p then ofList rest else c) = true := by
  cases hl : toList c with
  | nil => exact inT_zero
  | cons p rest =>
    obtain ⟨hc, hd⟩ := inT_toList c h
    rw [hl] at hc hd
    show inT (if P p = true then ofList rest else c) = true
    split
    · exact inT_ofList rest (inTL_cons.mp hc).2 (descL_tail hd)
    · exact h

theorem ltM_dropIfHead {c : Term} (h : inT c = true) (hlc : lt c M = true) (P : Term → Bool) :
    lt (match toList c with
        | [] => zero
        | p :: rest => if P p then ofList rest else c) M = true := by
  cases hl : toList c with
  | nil => exact lt_zero_M
  | cons p rest =>
    show lt (if P p = true then ofList rest else c) M = true
    split
    · exact lt_ofList_M rest (fun x hx =>
        ltM_toList c h hlc x (by rw [hl]; exact List.Mem.tail p hx))
    · exact hlc

theorem inT_sub1 {c : Term} (h : inT c = true) : inT (sub1 c) = true :=
  inT_dropIfHead h (fun p => p == one)

theorem ltM_sub1 {c : Term} (h : inT c = true) (hl : lt c M = true) :
    lt (sub1 c) M = true := ltM_dropIfHead h hl (fun p => p == one)

theorem inT_subAP {w x : Term} (h : inT x = true) : inT (subAP w x) = true :=
  inT_dropIfHead h (fun p => p == w)

theorem ltM_subAP {w x : Term} (h : inT x = true) (hl : lt x M = true) :
    lt (subAP w x) M = true := ltM_dropIfHead h hl (fun p => p == w)

theorem inT_logOm {t : Term} (ht : inT t = true) : inT (logOm t) = true := by
  cases t with
  | zero => exact ht
  | M => exact ht
  | omg a => exact ht
  | psi k a => exact ht
  | Z a => exact ht
  | add a b => exact ht
  | phi c d =>
    cases c with
    | zero =>
      obtain ⟨_, hd, _, _⟩ := inT_phi4 ht
      show inT (if TM.Term.phiShifted zero d then plus d one else d) = true
      split
      · exact inT_plus hd inT_one
      · exact hd
    | M => exact ht
    | omg _ => exact ht
    | phi _ _ => exact ht
    | psi _ _ => exact ht
    | Z _ => exact ht
    | add _ _ => exact ht

theorem ltM_logOm {t : Term} (ht : inT t = true) (hl : lt t M = true) :
    lt (logOm t) M = true := by
  cases t with
  | zero => exact hl
  | M => exact hl
  | omg a => exact hl
  | psi k a => exact hl
  | Z a => exact hl
  | add a b => exact hl
  | phi c d =>
    cases c with
    | zero =>
      obtain ⟨_, hd, _, hld⟩ := inT_phi4 ht
      show lt (if TM.Term.phiShifted zero d then plus d one else d) M = true
      split
      · exact lt_plus_M hd inT_one hld lt_one_M
      · exact hld
    | M => exact hl
    | omg _ => exact hl
    | phi _ _ => exact hl
    | psi _ _ => exact hl
    | Z _ => exact hl
    | add _ _ => exact hl

theorem inT_divAP {w p : Term} (hp : inT p = true) : inT (divAP w p) = true :=
  inT_omegaNF (inT_subAP (inT_logOm hp))

theorem ltM_divAP {w p : Term} (hp : inT p = true) (hlp : lt p M = true) :
    lt (divAP w p) M = true :=
  ltM_omegaNF (inT_subAP (inT_logOm hp)) (ltM_subAP (inT_logOm hp) (ltM_logOm hp hlp))

theorem isAP_divAP (w p : Term) : (divAP w p).isAP = true := isAP_omegaNF _

end

/-! ### §64.3 成分列の道具、そして単調性の 2 つの穴

`ofList` が 𝔗(M) の項になるには成分が降順でなければならない (2.1(iii))。`filter` は
`le_trans_inT` を 1 度だけ使えば降順を保つ。`map` はそうはいかない — そこが穴で、
`DivDescInT` と `MulDescInT` に名前をつけて分離する。 -/

section
open Trans.Recal (bplus)
open TM TM.Term
open Evidence.WF
open Trans.Dict (logOm divAP mulL)

/-- 降順の列は頭で押さえられる。`le_trans_inT` を使うのはここだけ。 -/
theorem descL_bound_inT : ∀ (l : List Term) (a : Term), inT a = true → inTL l = true →
    descL (a :: l) = true → ∀ x ∈ l, le x a = true := by
  intro l
  induction l with
  | nil => intro _ _ _ _ x hx; cases hx
  | cons b t ih =>
    intro a hia hc hd x hx
    obtain ⟨hba, hdt⟩ := descL_cons.mp hd
    obtain ⟨⟨_, hib⟩, hct⟩ := inTL_cons.mp hc
    rcases List.mem_cons.mp hx with h | h
    · rw [h]; exact hba
    · have hxb : le x b = true := ih b hib hct hdt x h
      have hix : inT x = true := ((Bool.and_eq_true _ _).mp
        (List.all_eq_true.mp hct x h)).2
      exact le_trans_inT hix hib hia hxb hba

theorem inTL_filter (P : Term → Bool) : ∀ {l : List Term}, inTL l = true →
    inTL (l.filter P) = true := by
  intro l h
  show (l.filter P).all _ = true
  rw [List.all_eq_true]
  intro x hx
  exact List.all_eq_true.mp h x (List.mem_filter.mp hx).1

theorem descL_filter_inT : ∀ (l : List Term), inTL l = true → descL l = true →
    ∀ (P : Term → Bool), descL (l.filter P) = true := by
  intro l
  induction l with
  | nil => intro _ _ _; rfl
  | cons a t ih =>
    intro hc hd P
    obtain ⟨⟨_, hia⟩, hct⟩ := inTL_cons.mp hc
    have hdt := descL_tail hd
    have hbound := descL_bound_inT t a hia hct hd
    by_cases hp : P a = true
    · rw [List.filter_cons_of_pos hp]
      cases hf : t.filter P with
      | nil => rfl
      | cons b s =>
        refine descL_cons.mpr ⟨?_, by rw [← hf]; exact ih hct hdt P⟩
        have hb : b ∈ t.filter P := by rw [hf]; exact List.Mem.head _
        exact hbound b (List.mem_filter.mp hb).1
    · rw [List.filter_cons_of_neg (by simpa using hp)]
      exact ih hct hdt P

theorem inT_filter_ofList {l : List Term} (hc : inTL l = true) (hd : descL l = true)
    (P : Term → Bool) : inT (ofList (l.filter P)) = true :=
  inT_ofList _ (inTL_filter P hc) (descL_filter_inT l hc hd P)

theorem ltM_filter_ofList {l : List Term} (hm : ∀ x ∈ l, lt x M = true)
    (P : Term → Bool) : lt (ofList (l.filter P)) M = true :=
  lt_ofList_M _ (fun x hx => hm x (List.mem_filter.mp hx).1)

/-- **(G1) 穴 1。** `divAP w` は降順を保つ — **ただし列の成分がすべて `w` 以上のとき**。
    側条件を落とすと偽で、最小の反例は `w = M`, `l = [M, Z0]` (下の `#guard`)。
    `Evidence/CNVOps.lean` §27–§29 の `omegaNF_mono` の `inT` 版にあたる。 -/
def DivDescInT : Prop := ∀ (w : Term) (l : List Term), inT w = true →
  inTL l = true → descL l = true → (∀ q ∈ l, lt q w = false) →
  descL (l.map (divAP w)) = true

/-- **(G2) 穴 2。** `mulL` の写像も降順を保つ。側条件は測定では要らなかった。 -/
def MulDescInT : Prop := ∀ (e y : Term), inT e = true → inT y = true →
  descL ((toList y).map (fun p => omegaNF (plus e (logOm p)))) = true

theorem inT_mulL (H : MulDescInT) {e y : Term} (he : inT e = true) (hy : inT y = true) :
    inT (mulL e y) = true := by
  show inT (ofList ((toList y).map (fun p => omegaNF (plus e (logOm p))))) = true
  refine inT_ofList _ ?_ (H e y he hy)
  show ((toList y).map _).all _ = true
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨p, hp, hxe⟩ := List.mem_map.mp hx
  rw [← hxe]
  show ((omegaNF (plus e (logOm p))).isAP && inT (omegaNF (plus e (logOm p)))) = true
  rw [isAP_omegaNF, inT_omegaNF (inT_plus he (inT_logOm (inTL_inT hy p hp)))]
  rfl

theorem ltM_mulL {e y : Term} (he : inT e = true) (hy : inT y = true)
    (hle : lt e M = true) (hly : lt y M = true) : lt (mulL e y) M = true := by
  show lt (ofList ((toList y).map (fun p => omegaNF (plus e (logOm p))))) M = true
  refine lt_ofList_M _ ?_
  intro x hx
  obtain ⟨p, hp, hxe⟩ := List.mem_map.mp hx
  rw [← hxe]
  have hip := inTL_inT hy p hp
  have hlp := ltM_toList y hy hly p hp
  exact ltM_omegaNF (inT_plus he (inT_logOm hip))
    (lt_plus_M he (inT_logOm hip) hle (ltM_logOm hip hlp))

end

/-! ### §64.4 `wcnf` の成分

底 `w` の Cantor 標準形。指数 `a` と係数 `c` がどちらも 𝔗(M) の項で `M` の下にあること、
尾 `ρ` も同じであることを、成分列の帰納で出す。指数の側だけが (G1) を消費する。 -/

section
open Trans.Recal (bplus)
open TM TM.Term
open Evidence.WF
open Trans.Dict (wcnf divAP logOm)

theorem wcnf_nil (w : Term) : wcnf w [] = ([], zero) := rfl

theorem wcnf_cons_lt {w p : Term} {rest : List Term} (h : lt p w = true) :
    wcnf w (p :: rest) = ([], ofList (p :: rest)) := by
  show (if lt p w = true then _ else _) = _
  rw [if_pos h]

/-- `wcnf` の 1 成分ぶんの指数。 -/
def wA (w p : Term) : Term :=
  ofList (((toList (logOm p)).filter (fun q => !lt q w)).map (divAP w))
/-- `wcnf` の 1 成分ぶんの係数。 -/
def wC (w p : Term) : Term :=
  omegaNF (ofList ((toList (logOm p)).filter (fun q => lt q w)))

theorem wcnf_cons_ge {w p : Term} {rest : List Term} (h : lt p w = false) :
    wcnf w (p :: rest) =
      (match wcnf w rest with
       | ((a', c') :: ps, tl) =>
         if wA w p == a' then ((wA w p, plus (wC w p) c') :: ps, tl)
         else ((wA w p, wC w p) :: (a', c') :: ps, tl)
       | ([], tl) => ([(wA w p, wC w p)], tl)) := by
  show (if lt p w = true then _ else _) = _
  rw [if_neg (by rw [h]; exact Bool.noConfusion)]
  rfl

theorem inT_wA (Hd : DivDescInT) {w p : Term} (hw : inT w = true) (hp : inT p = true) :
    inT (wA w p) = true := by
  obtain ⟨hc, hd⟩ := inT_toList _ (inT_logOm hp)
  refine inT_ofList _ ?_
    (Hd w _ hw (inTL_filter _ hc) (descL_filter_inT _ hc hd _) ?_)
  · show (List.map (divAP w) _).all _ = true
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨q, hq, hxe⟩ := List.mem_map.mp hx
    rw [← hxe]
    show ((divAP w q).isAP && inT (divAP w q)) = true
    rw [isAP_divAP, inT_divAP (inTL_inT (inT_logOm hp) q (List.mem_filter.mp hq).1)]
    rfl
  · intro q hq
    have := (List.mem_filter.mp hq).2
    cases hlq : lt q w with
    | false => rfl
    | true => rw [hlq] at this; exact Bool.noConfusion this

theorem ltM_wA {w p : Term} (hp : inT p = true) (hlp : lt p M = true) :
    lt (wA w p) M = true := by
  refine lt_ofList_M _ ?_
  intro x hx
  obtain ⟨q, hq, hxe⟩ := List.mem_map.mp hx
  rw [← hxe]
  have hmq := (List.mem_filter.mp hq).1
  exact ltM_divAP (inTL_inT (inT_logOm hp) q hmq)
    (ltM_toList _ (inT_logOm hp) (ltM_logOm hp hlp) q hmq)

theorem inT_wC {w p : Term} (hp : inT p = true) : inT (wC w p) = true := by
  obtain ⟨hc, hd⟩ := inT_toList _ (inT_logOm hp)
  exact inT_omegaNF (inT_filter_ofList hc hd _)

theorem ltM_wC {w p : Term} (hp : inT p = true) (hlp : lt p M = true) :
    lt (wC w p) M = true := by
  obtain ⟨hc, hd⟩ := inT_toList _ (inT_logOm hp)
  exact ltM_omegaNF (inT_filter_ofList hc hd _)
    (ltM_filter_ofList (ltM_toList _ (inT_logOm hp) (ltM_logOm hp hlp)) _)

/-- `wcnf` の返り値がすべて 𝔗(M) の項で `M` の下にあること。 -/
def PairOK (r : List (Term × Term) × Term) : Prop :=
  (inT r.2 = true ∧ lt r.2 M = true) ∧
  (∀ ac ∈ r.1, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true)

/-- **`wcnf` は 𝔗(M) の中に留まる。** (G1) だけを使う。 -/
theorem wcnf_spec (Hd : DivDescInT) {w : Term} (hw : inT w = true) : ∀ (L : List Term),
    inTL L = true → descL L = true → (∀ x ∈ L, lt x M = true) → PairOK (wcnf w L) := by
  intro L
  induction L with
  | nil =>
    intro _ _ _
    exact ⟨⟨inT_zero, lt_zero_M⟩, by intro ac hac; cases hac⟩
  | cons p rest ih =>
    intro hc hd hm
    obtain ⟨⟨hap, hip⟩, hcr⟩ := inTL_cons.mp hc
    have hdr := descL_tail hd
    have hmr : ∀ x ∈ rest, lt x M = true := fun x hx => hm x (List.Mem.tail p hx)
    have hlpM : lt p M = true := hm p (List.Mem.head _)
    have IH := ih hcr hdr hmr
    by_cases hlp : lt p w = true
    · rw [wcnf_cons_lt hlp]
      exact ⟨⟨inT_ofList _ hc hd, lt_ofList_M _ hm⟩, by intro ac hac; cases hac⟩
    · have hlp' : lt p w = false := bool_false hlp
      have hA := inT_wA Hd (w := w) hw hip
      have hAM := ltM_wA (w := w) hip hlpM
      have hC := inT_wC (w := w) hip
      have hCM := ltM_wC (w := w) hip hlpM
      rw [wcnf_cons_ge hlp']
      cases hr : wcnf w rest with
      | mk fst snd =>
        rw [hr] at IH
        obtain ⟨⟨hs1, hs2⟩, hall⟩ := IH
        cases fst with
        | nil =>
          refine ⟨⟨hs1, hs2⟩, ?_⟩
          intro ac hac
          rw [List.mem_singleton.mp hac]
          exact ⟨hA, hAM, hC, hCM⟩
        | cons ac0 ps =>
          cases ac0 with
          | mk a' c' =>
            have hac0 := hall (a', c') (List.Mem.head _)
            show PairOK (if (wA w p == a') = true
              then ((wA w p, plus (wC w p) c') :: ps, snd)
              else ((wA w p, wC w p) :: (a', c') :: ps, snd))
            by_cases heq : (wA w p == a') = true
            · rw [if_pos heq]
              refine ⟨⟨hs1, hs2⟩, ?_⟩
              intro ac hac
              rcases List.mem_cons.mp hac with h | h
              · rw [h]
                exact ⟨hA, hAM, inT_plus hC hac0.2.2.1,
                  lt_plus_M hC hac0.2.2.1 hCM hac0.2.2.2⟩
              · exact hall ac (List.Mem.tail _ h)
            · rw [if_neg heq]
              refine ⟨⟨hs1, hs2⟩, ?_⟩
              intro ac hac
              rcases List.mem_cons.mp hac with h | h
              · rw [h]; exact ⟨hA, hAM, hC, hCM⟩
              · exact hall ac h

end

/-! ### §64.5 畳み込み、`collapse`、そして `CollapseInT` が何に還元されるか

`stepF`・`idxOf`・`scanSt` は `collapse` の畳み込みをそのまま写したもので、`collapse_eq`
は `rfl`。不変量は「累算器の 2 つの枠がどちらも 𝔗(M) の項で `M` の下」。ヴェブレン枝は
§64.2 だけで閉じ、強臨界枝は `PsiIdxOK` — 2.1(vi) の最後の連言 — を消費する。 -/

section
open Trans.Recal (bplus)
open TM TM.Term
open Evidence.WF
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse dict)
open Trans.Dict (BT)

/-- 強臨界枝が組み立てる指数。`collapse` の定義をそのまま写したもの。 -/
def idxOf (w : Term) (s : Option Term × Option Term) (ac : Term × Term) : Term :=
  match s.1 with
  | none => sub1 (mulL (mulL w (subAP w ac.1)) ac.2)
  | some i0 => plus i0 (mulL (mulL w (subAP w ac.1)) ac.2)

/-- `collapse` の畳み込みの 1 歩。 -/
def stepF (w base : Term) (s : Option Term × Option Term) (ac : Term × Term) :
    Option Term × Option Term :=
  if le w ac.1 then (some (idxOf w s ac), some (psi w (idxOf w s ac)))
  else
    let bse := match s.2 with | none => base | some v => v
    let cc := match s.2 with | none => sub1 ac.2 | some _ => ac.2
    (s.1, some (phiNF ac.1 (plus bse cc)))

def baseOf (u : Nat) : Term := if u == 0 then zero else plus (reg u) TM.Term.one

/-- **`collapse` は畳み込みそのもの。** -/
theorem collapse_eq (u : Nat) (x : Term) :
    collapse u x =
      omegaNF (plus (reg u) (plus
        (((wcnf (reg (u+1)) (toList x)).1.foldl
            (init := ((none : Option Term), (none : Option Term)))
            (stepF (reg (u+1)) (baseOf u))).2.getD zero)
        (wcnf (reg (u+1)) (toList x)).2)) := rfl

/-- 畳み込みが実際に通る (状態, 成分) の並び。 -/
def scanSt (w base : Term) : (Option Term × Option Term) → List (Term × Term) →
    List ((Option Term × Option Term) × (Term × Term))
  | _, [] => []
  | s, ac :: t => (s, ac) :: scanSt w base (stepF w base s ac) t

theorem scanSt_mem_snd : ∀ (w base : Term) (s : Option Term × Option Term)
    (l : List (Term × Term)) (p : (Option Term × Option Term) × (Term × Term)),
    p ∈ scanSt w base s l → p.2 ∈ l := by
  intro w base s l
  induction l generalizing s with
  | nil => intro p hp; cases hp
  | cons ac t ih =>
    intro p hp
    rcases List.mem_cons.mp (show p ∈ (s, ac) :: scanSt w base (stepF w base s ac) t from hp)
      with h | h
    · rw [h]; exact List.Mem.head _
    · exact List.Mem.tail _ (ih (stepF w base s ac) p h)

theorem inT_reg : ∀ u, inT (reg u) = true
  | 0 => inT_zero
  | u + 1 => show inT (ofNat u) = true from inT_ofNat u

theorem ltM_reg : ∀ u, lt (reg u) M = true
  | 0 => lt_zero_M
  | _ + 1 => lt_Z_M _

theorem inT_baseOf (u : Nat) : inT (baseOf u) = true := by
  unfold baseOf
  split
  · exact inT_zero
  · exact inT_plus (inT_reg u) inT_one

theorem ltM_baseOf (u : Nat) : lt (baseOf u) M = true := by
  unfold baseOf
  split
  · exact lt_zero_M
  · exact lt_plus_M (inT_reg u) inT_one (ltM_reg u) lt_one_M

/-- 畳み込みの不変量。 -/
def StInv (s : Option Term × Option Term) : Prop :=
  (∀ i0, s.1 = some i0 → inT i0 = true ∧ lt i0 M = true) ∧
  (∀ v, s.2 = some v → inT v = true ∧ lt v M = true)

theorem inT_idxOf (Hm : MulDescInT) {w : Term} (hw : inT w = true) (hlw : lt w M = true)
    {s : Option Term × Option Term} {ac : Term × Term} (hs : StInv s)
    (h1 : inT ac.1 = true) (h2 : lt ac.1 M = true) (h3 : inT ac.2 = true)
    (h4 : lt ac.2 M = true) :
    inT (idxOf w s ac) = true ∧ lt (idxOf w s ac) M = true := by
  have he : inT (mulL w (subAP w ac.1)) = true := inT_mulL Hm hw (inT_subAP h1)
  have hle : lt (mulL w (subAP w ac.1)) M = true :=
    ltM_mulL hw (inT_subAP h1) hlw (ltM_subAP h1 h2)
  have hd : inT (mulL (mulL w (subAP w ac.1)) ac.2) = true := inT_mulL Hm he h3
  have hld : lt (mulL (mulL w (subAP w ac.1)) ac.2) M = true := ltM_mulL he h3 hle h4
  unfold idxOf
  cases hs1 : s.1 with
  | none => exact ⟨inT_sub1 hd, ltM_sub1 hd hld⟩
  | some i0 =>
    obtain ⟨hi, hli⟩ := hs.1 i0 hs1
    exact ⟨inT_plus hi hd, lt_plus_M hi hd hli hld⟩

theorem stepF_inv (Hm : MulDescInT) {w base : Term} (hw : inT w = true) (hlw : lt w M = true)
    (hb : inT base = true) (hlb : lt base M = true)
    {s : Option Term × Option Term} {ac : Term × Term} (hs : StInv s)
    (hac : inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true)
    (hpsi : le w ac.1 = true → inT (psi w (idxOf w s ac)) = true) :
    StInv (stepF w base s ac) := by
  obtain ⟨h1, h2, h3, h4⟩ := hac
  unfold stepF
  split
  · rename_i hle
    obtain ⟨hi, hli⟩ := inT_idxOf Hm hw hlw hs h1 h2 h3 h4
    refine ⟨?_, ?_⟩
    · intro i0 hq
      rw [← Option.some.inj (show some (idxOf w s ac) = some i0 from hq)]
      exact ⟨hi, hli⟩
    · intro v hq
      rw [← Option.some.inj (show some (psi w (idxOf w s ac)) = some v from hq)]
      exact ⟨hpsi hle, lt_psi_M _ _⟩
  · refine ⟨hs.1, ?_⟩
    intro v hq
    have hbse : inT (match s.2 with | none => base | some v => v) = true ∧
        lt (match s.2 with | none => base | some v => v) M = true := by
      cases hq2 : s.2 with
      | none => exact ⟨hb, hlb⟩
      | some v0 => exact hs.2 v0 hq2
    have hcc : inT (match s.2 with | none => sub1 ac.2 | some _ => ac.2) = true ∧
        lt (match s.2 with | none => sub1 ac.2 | some _ => ac.2) M = true := by
      cases hq2 : s.2 with
      | none => exact ⟨inT_sub1 h3, ltM_sub1 h3 h4⟩
      | some v0 => exact ⟨h3, h4⟩
    rw [← Option.some.inj (show some (phiNF ac.1
      (plus (match s.2 with | none => base | some v => v)
            (match s.2 with | none => sub1 ac.2 | some _ => ac.2))) = some v from hq)]
    exact ⟨inT_phiNF h1 (inT_plus hbse.1 hcc.1) h2
             (lt_plus_M hbse.1 hcc.1 hbse.2 hcc.2),
           ltM_phiNF h2 (lt_plus_M hbse.1 hcc.1 hbse.2 hcc.2)⟩

theorem fold_inv (Hm : MulDescInT) {w base : Term} (hw : inT w = true) (hlw : lt w M = true)
    (hb : inT base = true) (hlb : lt base M = true) :
    ∀ (l : List (Term × Term)) (s : Option Term × Option Term), StInv s →
      (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
      (∀ p ∈ scanSt w base s l, le w p.2.1 = true →
          inT (psi w (idxOf w p.1 p.2)) = true) →
      StInv (l.foldl (stepF w base) s) := by
  intro l
  induction l with
  | nil => intro s hs _ _; exact hs
  | cons ac t ih =>
    intro s hs hall hpsi
    have h1 : StInv (stepF w base s ac) :=
      stepF_inv Hm hw hlw hb hlb hs (hall ac (List.Mem.head _))
        (hpsi (s, ac) (List.Mem.head _))
    exact ih (stepF w base s ac) h1 (fun a ha => hall a (List.Mem.tail _ ha))
      (fun p hp => hpsi p (List.Mem.tail _ hp))

/-- **(G3) 穴 3。** 強臨界枝が実際に吐く指数について [Rathjen, 1991] 2.1(vi) の最後の連言。
    `scanSt` を通しているので、畳み込みが決して作らない指数については何も言っていない。
    一般には**偽** (下の `#guard`)。`dict` の像では 1805 項すべてで成り立つ (測定)。 -/
def PsiIdxOK (u : Nat) (x : Term) : Prop :=
  ∀ p ∈ scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1,
    le (reg (u+1)) p.2.1 = true →
    inT (psi (reg (u+1)) (idxOf (reg (u+1)) p.1 p.2)) = true

/-- **§64 の主定理。** `collapse` は 𝔗(M) に落ちる — (G1)(G2)(G3) を仮定して。 -/
theorem inT_collapse (Hd : DivDescInT) (Hm : MulDescInT) (u : Nat) (x : Term)
    (hx : inT x = true) (hlx : lt x M = true) (Hp : PsiIdxOK u x) :
    inT (collapse u x) = true ∧ lt (collapse u x) M = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨⟨h21, h22⟩, hallOK⟩ :=
    wcnf_spec Hd (inT_reg (u+1)) (toList x) hc hd (ltM_toList x hx hlx)
  have hinit : StInv ((none : Option Term), (none : Option Term)) := by
    constructor
    · intro i0 h; cases h
    · intro v h; cases h
  have hst := fold_inv Hm (inT_reg (u+1)) (ltM_reg (u+1)) (inT_baseOf u) (ltM_baseOf u)
    (wcnf (reg (u+1)) (toList x)).1 (none, none) hinit hallOK Hp
  have hv : inT (((wcnf (reg (u+1)) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg (u+1)) (baseOf u))).2.getD zero) = true ∧
      lt (((wcnf (reg (u+1)) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg (u+1)) (baseOf u))).2.getD zero) M = true := by
    cases hg : ((wcnf (reg (u+1)) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg (u+1)) (baseOf u))).2 with
    | none => exact ⟨inT_zero, lt_zero_M⟩
    | some v => exact hst.2 v hg
  rw [collapse_eq]
  have harg : inT (plus (reg u) (plus _ (wcnf (reg (u+1)) (toList x)).2)) = true :=
    inT_plus (inT_reg u) (inT_plus hv.1 h21)
  have hlarg : lt (plus (reg u) (plus _ (wcnf (reg (u+1)) (toList x)).2)) M = true :=
    lt_plus_M (inT_reg u) (inT_plus hv.1 h21) (ltM_reg u)
      (lt_plus_M hv.1 h21 hv.2 h22)
  exact ⟨inT_omegaNF harg, ltM_omegaNF harg hlarg⟩

/-- 強臨界枝が一度も点火しないなら (G3) は自動的に成り立つ。 -/
theorem psiIdxOK_of_noSC (u : Nat) (x : Term)
    (h : ∀ ac ∈ (wcnf (reg (u+1)) (toList x)).1, le (reg (u+1)) ac.1 = false) :
    PsiIdxOK u x := by
  intro p hp hle
  have hmem := scanSt_mem_snd _ _ _ _ p hp
  exact absurd hle (by rw [h p.2 hmem]; exact Bool.noConfusion)

/-- **強臨界枝のない断片では (G3) は要らない。** -/
theorem inT_collapse_noSC (Hd : DivDescInT) (Hm : MulDescInT) (u : Nat) (x : Term)
    (hx : inT x = true) (hlx : lt x M = true)
    (h : ∀ ac ∈ (wcnf (reg (u+1)) (toList x)).1, le (reg (u+1)) ac.1 = false) :
    inT (collapse u x) = true :=
  (inT_collapse Hd Hm u x hx hlx (psiIdxOK_of_noSC u x h)).1

/-- `dict` の像は 𝔗(M) の中で `M` の下にある — 3 つの穴を仮定して。 -/
theorem inT_dict (Hd : DivDescInT) (Hm : MulDescInT)
    (Hp : ∀ (u : Nat) (a : BT), PsiIdxOK u (dict a)) :
    ∀ a : BT, inT (dict a) = true ∧ lt (dict a) M = true
  | .zero => ⟨inT_zero, lt_zero_M⟩
  | .D u a => by
    have ih := inT_dict Hd Hm Hp a
    exact inT_collapse Hd Hm u (dict a) ih.1 ih.2 (Hp u a)
  | .sum a b => by
    have iha := inT_dict Hd Hm Hp a
    have ihb := inT_dict Hd Hm Hp b
    exact ⟨inT_plus iha.1 ihb.1, lt_plus_M iha.1 ihb.1 iha.2 ihb.2⟩

/-- **§63 の `CollapseInT` は、名前のついた 3 つの事実に還元される。** -/
theorem collapseInT_of_gaps (Hd : DivDescInT) (Hm : MulDescInT)
    (Hp : ∀ (u : Nat) (a : BT), PsiIdxOK u (dict a)) : CollapseInT :=
  fun u a => (inT_dict Hd Hm Hp (BT.D u a)).1

/-- **消費者を通す。** §63 の `hsuccS_supply` — `certIn_region` の 2 番目の供給 — が
    (G1)(G2)(G3) だけで開く。仮説が満たせないものでないことの確認はこれ。 -/
theorem hsuccS_supply_of_gaps (Hd : DivDescInT) (Hm : MulDescInT)
    (Hp : ∀ (u : Nat) (a : BT), PsiIdxOK u (dict a)) :
    ∀ (S : BMS.Matrix) (v : TM.Term), RegS S → ValS S v → BMS.kind S = BMS.Kind.succ →
    ∃ u, v = plus u TM.Term.one ∧ inT v = true ∧ inT u = true ∧ lt u v = true
         ∧ ∀ n, ValS (BMS.expand S n) u :=
  hsuccS_supply (collapseInT_of_gaps Hd Hm Hp)

end

/-! ### §64.6 測定 (凍結)

否定的なものから。 -/

section
open TM TM.Term
open Evidence.WF
open Trans.Recal
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse dict)
open Trans.Dict (BT)

/-- 測定用の判定器。 -/
def divDescb (w : Term) (l : List Term) : Bool := descL (l.map (divAP w))
def mulDescb (e y : Term) : Bool := descL ((toList y).map (fun p => omegaNF (plus e (logOm p))))
def psiIdxOKb (u : Nat) (x : Term) : Bool :=
  (scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1).all
    fun p => !(le (reg (u+1)) p.2.1) || inT (psi (reg (u+1)) (idxOf (reg (u+1)) p.1 p.2))
def noSCb (u : Nat) (x : Term) : Bool :=
  (wcnf (reg (u+1)) (toList x)).1.all fun ac => !(le (reg (u+1)) ac.1)

-- **否定 1.** `inT x` だけでは `inT (collapse u x)` は出ない。最小は `x = M`。
#guard inT (M : Term)
#guard !(inT (Trans.Dict.collapse 0 M))

-- **否定 2.** `inT x && lt x M` でも出ない。最小は `x = ψ_{ZM}(ZM)` (次数 5)。
#guard inT (psi (Z M) (Z M)) && lt (psi (Z M) (Z M)) M
#guard (psi (Z M) (Z M)).deg == 5
#guard !(inT (Trans.Dict.collapse 0 (psi (Z M) (Z M))))
--   落ちるのはちょうど (G3) — 吐かれる指数は `x` 自身で、`K_Ω x = {ZM}` が `x` 未満でない。
#guard !(psiIdxOKb 0 (psi (Z M) (Z M)))
#guard Kset (Z zero) (psi (Z M) (Z M)) == [Z M]
#guard !(lt (Z M) (psi (Z M) (Z M)))
--   次数 10 の `φ̄(Ω, ψ_Ω(Z1))` も同じ形で落ちる (機構は同一)。
#guard !(psiIdxOKb 0 (phi (Z zero) (psi (Z zero) (Z one))))

-- **否定 3.** (G1) の側条件を落とすと偽。最小は `w = M`, `l = [M, Z0]` (次数和 5)。
#guard inT (add M (Z zero)) && descL (TM.Term.toList (add M (Z zero)))
#guard !(divDescb M (TM.Term.toList (add M (Z zero))))
#guard ((TM.Term.toList (add M (Z zero))).map (divAP M)) == [one, Z zero]
--   `w` を R に限っても救われない。最小は `w = Z M`, `l = [Z M, Z 0]` (次数和 7)。
#guard (Z M).isR && inT (add (Z M) (Z zero))
#guard !(divDescb (Z M) (TM.Term.toList (add (Z M) (Z zero))))
--   救うのは「成分がすべて `w` 以上」。上の 2 つはどちらもそれを破る。
#guard !((TM.Term.toList (add M (Z zero))).all (fun q => !lt q M))
#guard !((TM.Term.toList (add (Z M) (Z zero))).all (fun q => !lt q (Z M)))

/-! 肯定。母集団は 2 つ — 手作りの `inT` 項 (`corp64`) と `dict` の像 (`bcorp64`)。 -/

private def at64 : List Term :=
  [zero, one, omega, phi one zero, Z zero, Z one, psi (Z zero) zero,
   psi (Z zero) (Z one), M, omg (add M one), psi M M, phi M M, Z (Z zero), Z M,
   psi (Z one) zero, psi (Z one) (Z zero), phi (Z zero) zero, phi zero (Z zero)]
private def corp64 : List Term :=
  at64
  ++ (at64.flatMap fun a => at64.map fun b => add a b)
  ++ (at64.flatMap fun a => at64.map fun b => phi a b)
  ++ (at64.flatMap fun a => at64.map fun b => psi a b)
  ++ (at64.map fun a => omg a)
  ++ (at64.map fun a => Z a)
  ++ (at64.flatMap fun a => at64.map fun b => add a (add b one))
private def gT64 : List Term := corp64.filter fun x => inT x
private def gTM64 : List Term := corp64.filter fun x => inT x && lt x M
private def bseed64 : List BT := [.zero, .D 0 .zero, .D 1 .zero, .D 2 .zero, .D 0 (.D 1 .zero)]
private def bstep64 (l : List BT) : List BT :=
  l ++ (List.range 3).flatMap (fun u => l.map (fun a => BT.D u a))
    ++ (l.flatMap fun a => l.map fun b => BT.sum a b)
private def bcorp64 : List BT := (bstep64 (bstep64 bseed64).eraseDups).eraseDups

#guard corp64.length == 1350
#guard gT64.length == 524
#guard gTM64.length == 463
#guard bcorp64.length == 1805

-- 肯定 1.  (G1) — 側条件つきなら 0 失敗。`gT64` の全ペアで 82 373 組。
#guard (gT64.flatMap fun w => gT64.filter fun y =>
    (TM.Term.toList y).all (fun q => !lt q w) && !(divDescb w (TM.Term.toList y))).length == 0
#guard (gT64.flatMap fun w => gT64.filter fun y =>
    (TM.Term.toList y).all (fun q => !lt q w)).length == 82373

-- 肯定 2.  (G2) — 側条件なしで 0 失敗。`gT64` の全ペアで 274 576 組。
#guard (gT64.flatMap fun e => gT64.filter fun y => !(mulDescb e y)).length == 0
#guard gT64.length * gT64.length == 274576

-- 肯定 3.  (G3) — `dict` の像 1805 項すべて、`u = 0,1,2,3` で 0 失敗。
--   **`BT.isStd` で絞っていない。**
#guard (bcorp64.filter fun a => !(psiIdxOKb 0 (dict a))).length == 0
#guard (bcorp64.filter fun a => !(psiIdxOKb 1 (dict a))).length == 0
#guard (bcorp64.filter fun a => !(psiIdxOKb 2 (dict a))).length == 0
#guard (bcorp64.filter fun a => !(psiIdxOKb 3 (dict a))).length == 0
#guard !(bcorp64.all fun a => BT.isStd a)
--   そして (G3) は真空ではない。手作りの母集団では `u = 0` で 17 回落ちる。
#guard (gTM64.filter fun x => !(psiIdxOKb 0 x)).length == 17
#guard (gTM64.filter fun x => !(psiIdxOKb 1 x)).length == 3

-- 肯定 4.  `inT_collapse_noSC` の射程。`u = 0` で 743/1805、`u = 1` で 1804/1805。
#guard (bcorp64.filter fun a => noSCb 0 (dict a)).length == 743
#guard (bcorp64.filter fun a => noSCb 1 (dict a)).length == 1804
#guard (bcorp64.filter fun a => noSCb 2 (dict a)).length == 1805

-- 肯定 5.  `dict` の像は `inT` かつ `M` の下 — §64.5 の `inT_dict` が結論する形。
#guard bcorp64.all fun a => inT (dict a) && lt (dict a) M

-- 肯定 7.  (G1)(G2) の第 2 母集団 — 種を変えて 2 回閉じた深い項 (最大次数 12)。
--   種は {0, 1, Ω, M, ψ_Ω0, ω^Ω}、閉包は add/phi/psi/Z/omg。
private def a64 : List Term := [zero, one, Z zero, M, psi (Z zero) zero, phi zero (Z zero)]
private def step64 (l : List Term) : List Term :=
  l ++ (l.flatMap fun a => l.map fun b => add a b)
    ++ (l.flatMap fun a => l.map fun b => phi a b)
    ++ (l.flatMap fun a => l.map fun b => psi a b)
    ++ (l.map fun a => Z a) ++ (l.map fun a => omg a)
private def a64' : List Term := (step64 a64).eraseDups.filter fun x => inT x
private def deep64 : List Term :=
  (((step64 (a64'.take 14)).eraseDups).filter fun x => inT x).take 80
#guard a64'.length == 53
#guard deep64.length == 80
#guard (deep64.map fun x => x.deg).foldl (fun a b => if a < b then b else a) 0 == 12
#guard (deep64.flatMap fun w => deep64.filter fun y =>
    (TM.Term.toList y).all (fun q => !lt q w) && !(divDescb w (TM.Term.toList y))).length == 0
#guard (deep64.flatMap fun w => deep64.filter fun y =>
    (TM.Term.toList y).all (fun q => !lt q w)).length == 2324
#guard (deep64.flatMap fun e => deep64.filter fun y => !(mulDescb e y)).length == 0
#guard deep64.length * deep64.length == 6400

-- 肯定 6.  領域そのもの。§63.5 の `CollapseInT` 測定を (G3) の形で取り直す。
#guard ((popNFB 3 6).flatMap fun t => (bVal t).toL).eraseDups.length == 443
#guard ((popNFB 3 6).flatMap fun t => (bVal t).toL).eraseDups.all fun a =>
  TM.Term.inT (Trans.Dict.dict a)

end


/-! ## §65 (G1) IS FALSE AS STATED, (G2) IS TRUE — AND BOTH CLOSE

§64 reduced `CollapseInT` to three named hypotheses and recommended closing the first two.
The recommendation was checked before it was followed, and the check came back split.

  **(G1) `DivDescInT` IS FALSE — and `not_divDescInT` below PROVES it** (axioms: `propext`
  only).  Not for want of the side condition §64 already found: with it.  Smallest
  counterexample, degree sum 17:

      w = ω,   l = [ω^ω, ω]

  Every hypothesis holds — `inT ω`; both members additively principal and `inT`; `l`
  descending (`ω ≤ ω^ω`); and `lt q w = false` for BOTH members, since `ω ≤ ω ≤ ω^ω`.  But
  `divAP ω (ω^ω) = 1` while `divAP ω ω = ω`, so the image `[1, ω]` ASCENDS.  The list is not
  an artefact of the Prop's generality either: `l = toList (ω^ω ⊕ ω)` and `ω^ω ⊕ ω` is a
  genuine term of 𝔗(M).

  WHY 82373 + 2324 PAIRS MISSED IT.  §64's positive sweep quantified `l` not over lists but
  as `toList y` for `y` RANGING OVER THE CORPUS, so it only ever saw the component lists of
  corpus terms — and `ω^ω ⊕ ω` is in neither population (`corp64` closes `add` over `at64`
  only, and `ω^ω = φ̄(0,ω)` is not in `at64`).  §64's counterexample search, which did range
  over lists, stopped at `w = M` and `w = Z M` and concluded "regular does not rescue it,
  `w ≤ every member` does".  Both halves of that conclusion are right about what they tested
  and wrong as stated: the missing fact is that `w ≤ p` does NOT give `w ≤ logOm p` unless
  `w` is STRONGLY CRITICAL — at `w = p = ω`, `ω ≤ ω` but `logOm ω = 1 < ω`.

  **The repair is `w ∈ SC`, and it is exactly what the call site has**: `wcnf`'s base is
  always `reg (u+1) = Z u`, and `(Z ·).isSC` is `rfl`.  `DivDescSC` is `DivDescInT` with that
  one conjunct added, and it is PROVED, unconditionally.

  **(G2) `MulDescInT` is true exactly as §64 states it** — no side condition — and is PROVED,
  unconditionally.

WHAT CARRIES THEM.  Three monotonicity steps and one order fact, each measured before it was
proved (§65.7) and each with its own side condition, none of them decoration:

  §65.1  heads and sums at `inT`: `0 ≤ ·`, `1 ≤ ·` for nonzero, `ofList (b :: t) < a` is
         `b < a` for additively principal `a`, and HEAD MONOTONICITY — `x ≤ y` forces the
         head component of `x` below the head component of `y`.  That is what makes the
         `subAP` case analysis finite.
  §65.2  `succT` at `inT`: `p < succT p`, and `p < v → succT p ≤ v` (NOTHING lies strictly
         between `p` and `p ⊕ 1`), `splitFin` rebuilds its argument, and hence **D1**
         (`dnArg x ≤ x`) and **D2** (`x < y → x ≤ dnArg y`) of `CNVOps` §28 one notch up.
         `CNV` admits three shapes and 𝔗(M) seven; the four new ones are additively principal
         atoms and go through the `φ̄` case of §28 unchanged.  **D3 — §29's hard one — is not
         needed and not restated**: it buys strictness, and every consumer here is non-strict.
  §65.3  `ω^·` is MONOTONE on 𝔗(M).  `omegaNF_eq_gen` — `ω^x = if M < x then ω̄^x else if
         isFP 0 x then x else φ̄0(dnArg x)` — holds for EVERY term, with no hypothesis at all,
         and is where the `isFixP` of `CNVOps` §26 WIDENS: at `CNV` a fixed point of `ω^·` is
         a `φ̄αβ` with `α ≠ 0`; at `inT` every strongly critical term is one too, and
         `TM/FS.lean`'s `isFP zero` — the predicate `logOm`'s own `φ̄0·` clause already uses —
         is exactly that.  Nine cases, `ω̄^·` included, none skipped.
  §65.4  `logOm` is monotone ON THE ADDITIVELY PRINCIPAL TERMS (**false without that**:
         `Ω ⊕ Ω ≤ ω^Ω` but `logOm (Ω ⊕ Ω) = Ω ⊕ Ω > Ω`, degree sum 9); `subAP w` is monotone
         ON `{x : w ≤ x}` (**false without that**: `w = M`, `x = Ω`, `y = M`, degree sum 4);
         `plus e ·` is monotone with no side condition; and the SC step `w ∈ SC ∧ w ≤ p ⟹
         w ≤ logOm p` (**false without SC**: `w = p = 1`).
         TWO THINGS THE MEASUREMENT SETTLED THAT THE RECOMMENDATION DID NOT.  `subAP` needs
         only `w ≤ x` — the condition on the SMALLER argument — and needs `w ∈ SC` not at all
         (0 failures over 109³ triples with SC dropped).  So `w ∈ SC` is consumed in exactly
         ONE place, `lt_logOm_of_sc`, and that is the whole content of the repair.
  §65.5  (G1) as `DivDescSC`; `not_divDescInT`; and (G2) as `MulDescInT` itself.
  §65.6  the consumers.  §64.4/§64.5's `wcnf_spec`, `inT_collapse`, `inT_dict` and
         `collapseInT_of_gaps` take the FALSE `DivDescInT` as a hypothesis and therefore
         CANNOT BE APPLIED; their proofs are re-run here against `DivDescSC`.  §64.3's
         `inT_mulL`/`ltM_mulL` and §64.5's `inT_idxOf`/`stepF_inv`/`fold_inv` take only
         `MulDescInT` and are reused as they stand.  The results are `wcnf_spec_sc`,
         `inT_collapse_gap3`, `inT_dict_gap3`, `collapseInT_of_gap3` and
         `hsuccS_supply_of_gap3`: **(G3) `PsiIdxOK` is the only hypothesis left.**

WHAT IS NOT CLAIMED.  (G3) is untouched — §64 measured it FALSE on hand terms (17 of 463 at
`u = 0`) and true on `dict`'s 1805-term image, and nothing here changes either.
`DivDescInT` is not repaired, it is REFUTED, so `collapseInT_of_gaps` still carries a false
hypothesis and is not used.  Nothing here says `dict`'s image is characterised, and nothing
here is a claim about `BT.isStd`.
-/


/-! ### §65.1 頭部と和 — 𝔗(M) の上の順序の道具

`le` の左が `0`、`1` が最小の非零、加法主要な右辺に対する和の比較、そして**頭部の単調性**。
最後のものが §65.4 の `subAP` の単調性を支える。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

theorem le_zero_left (t : Term) : le zero t = true := by
  show ((zero == t) || lt zero t) = true
  cases hz : ((zero : Term) == t) with
  | true => rfl
  | false =>
    rw [Bool.false_or]
    refine lt_zero_left ?_
    intro hc
    subst hc
    exact Bool.noConfusion hz

/-- `1` は 𝔗(M) の最小の非零項。 -/
theorem le_one_inT {v : Term} (hv : inT v = true) (hz : v ≠ zero) : le one v = true := by
  refine le_of_not_lt3 (inT_le_fragR v hv) (show FragR (one : Term) = true from rfl) ?_
  cases hlt : lt v one with
  | false => rfl
  | true => exact absurd (below_one v hv (fuelOf v one) hlt) hz

/-- 非和・非零に対する `⊕` の比較は頭部だけで決まる。 -/
theorem lt_ofList_nsum {a : Term} (hap : a.isAP = true) :
    ∀ (b : Term) (t : List Term), lt (ofList (b :: t)) a = lt b a := by
  intro b t
  cases t with
  | nil => rfl
  | cons c u =>
    show lt (add b (ofList (c :: u))) a = _
    exact lt_add_nsum (ne_zero_of_isAP hap) (nsum_of_isAP hap)

theorem toList_cons_hd {x b : Term} {s : List Term} (h : toList x = b :: s) :
    x = b ∨ ∃ v, x = add b v := by
  have hb : (toList x).head? = some b := by rw [h]; rfl
  cases x with
  | zero =>
    exact absurd (show b :: s = ([] : List Term) from h.symm) (List.cons_ne_nil b s)
  | M => exact Or.inl (Option.some.inj (show some (M : Term) = some b from hb))
  | omg a => exact Or.inl (Option.some.inj (show some (omg a) = some b from hb))
  | phi a c => exact Or.inl (Option.some.inj (show some (phi a c) = some b from hb))
  | psi k a => exact Or.inl (Option.some.inj (show some (psi k a) = some b from hb))
  | Z a => exact Or.inl (Option.some.inj (show some (Z a) = some b from hb))
  | add u v =>
    exact Or.inr ⟨v, by rw [Option.some.inj (show some u = some b from hb)]⟩

/-- 頭部成分は自分自身以下。 -/
theorem le_hd_self_inT {x b : Term} {s : List Term} (hx : inT x = true)
    (h : toList x = b :: s) : le b x = true := by
  rcases toList_cons_hd h with hb | ⟨v, hb⟩
  · rw [hb]; exact Evidence.WF.le_self _
  · rw [hb]
    refine le_of_lt (lt_head_add ?_ v)
    have := inT_add (by rw [← hb]; exact hx)
    exact this.1

/-- **頭部の単調性。** `x ≤ y` なら `x` の頭部は `y` の頭部以下。 -/
theorem hd_mono_inT {x y b c : Term} {s t : List Term} (hx : inT x = true) (hy : inT y = true)
    (hxl : toList x = b :: s) (hyl : toList y = c :: t) (h : le x y = true) :
    le b c = true := by
  have hib : inT b = true := inTL_inT hx b (by rw [hxl]; exact List.Mem.head _)
  have hic : inT c = true := inTL_inT hy c (by rw [hyl]; exact List.Mem.head _)
  have hapb : b.isAP = true := inTL_isAP hx b (by rw [hxl]; exact List.Mem.head _)
  cases hbc : le b c with
  | true => rfl
  | false =>
    exfalso
    have hcb : lt c b = true := lt_of_not_le_inT hib hic hbc
    have hyb : lt y b = true := by
      rw [← inT_ofList_toList y hy, hyl, lt_ofList_nsum hapb]
      exact hcb
    have hbx : le b x = true := le_hd_self_inT hx hxl
    have : lt y x = true := lt_of_lt_of_le3 (inT_le_fragR y hy) (inT_le_fragR b hib)
      (inT_le_fragR x hx) hyb hbx
    rcases (Bool.or_eq_true _ _).mp h with he | hl
    · rw [eq_of_beq he, lt_irrefl] at this; exact Bool.noConfusion this
    · rw [lt_asymm_inT hx hy hl] at this; exact Bool.noConfusion this

/-- 単調な写像は降順の列を降順に写す。 -/
theorem descL_map_mono (f : Term → Term) (P : Term → Prop)
    (hf : ∀ a b, P a → P b → le b a = true → le (f b) (f a) = true) :
    ∀ (l : List Term), (∀ x ∈ l, P x) → descL l = true → descL (l.map f) = true := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons a t ih =>
    intro hp hd
    cases t with
    | nil => rfl
    | cons b u =>
      obtain ⟨hba, hdt⟩ := descL_cons.mp hd
      refine descL_cons.mpr ⟨?_, ih (fun x hx => hp x (List.Mem.tail a hx)) hdt⟩
      exact hf a b (hp a (List.Mem.head _)) (hp b (List.Mem.tail a (List.Mem.head _))) hba

end

/-! ### §65.2 `succT` と `splitFin` — D1 と D2 を 𝔗(M) の上で

`CNVOps` §28 は `CNV` の 3 形 (`0`, `φ̄`, `⊕`) しか見ない。𝔗(M) には `M`, `ω̄^·`, `ψ`, `Z`
の 4 形が増えるが、そのどれも**加法主要な原子**であって `⊕` の頭部と同じ扱いで済む
(`le_succT_atom`)。`splitFin_rebuild` は `plus_ofNat` の成分列を直接計算する形に書き換えた
——`CNV` 版の `plus_ofNat_spec` は `cnv_succT` を経由するが、その必要はない。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

/-- `p < p ⊕ 1`。 -/
theorem lt_succT_inT : ∀ (p : Term), inT p = true → lt p (succT p) = true := by
  intro p
  induction p with
  | zero => intro _; exact lt_zero_left (by intro hc; exact Term.noConfusion hc)
  | M => intro _; exact lt_head_add rfl one
  | omg _ _ => intro _; exact lt_head_add rfl one
  | phi _ _ _ _ => intro _; exact lt_head_add rfl one
  | psi _ _ _ _ => intro _; exact lt_head_add rfl one
  | Z _ _ => intro _; exact lt_head_add rfl one
  | add s t _ iht =>
    intro h
    obtain ⟨_, _, hit, _⟩ := inT_add h
    have hrec := iht hit
    have hne : add s t ≠ add s (succT t) := by
      intro hc
      injection hc with _ h2
      rw [← h2, lt_irrefl] at hrec
      exact Bool.noConfusion hrec
    show lt (add s t) (add s (succT t)) = true
    rw [lt_add_add hne, if_pos rfl]
    exact hrec

theorem toList_ne_nil_inT {d : Term} (hz : d ≠ zero) : toList d ≠ [] := by
  intro hc
  exact hz (toList_eq_nil d hc)

/-- 末尾に `1` を継ぎ足すのは `succT`。 -/
theorem ofList_toList_snoc_inT : ∀ (a : Term), inT a = true →
    ofList (toList a ++ [one]) = succT a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | M => intro _; rfl
  | omg _ _ => intro _; rfl
  | phi _ _ _ _ => intro _; rfl
  | psi _ _ _ _ => intro _; rfl
  | Z _ _ => intro _; rfl
  | add c d _ ihd =>
    intro h
    obtain ⟨_, _, hid, hdesc⟩ := inT_add h
    have hdz : d ≠ zero := by intro hc; rw [hc] at hdesc; exact Bool.noConfusion hdesc
    show ofList (c :: (toList d ++ [one])) = add c (succT d)
    cases hl : toList d with
    | nil => exact absurd hl (toList_ne_nil_inT hdz)
    | cons e rest =>
      show add c (ofList (e :: (rest ++ [one]))) = add c (succT d)
      rw [show (e :: (rest ++ [one])) = toList d ++ [one] from by rw [hl]; rfl, ihd hid]

/-- 非和の右辺に対しては、和は頭部だけで決まる。 -/
theorem le_add_of_lt_nsum {a e v : Term} (hv : NSum v = true) (hvz : v ≠ zero)
    (hlt : lt a v = true) : le (add a e) v = true :=
  le_of_lt (by rw [lt_add_nsum hvz hv]; exact hlt)

/-- 加法主要な原子に対する `≤ succ`。 -/
theorem le_succT_atom {a : Term} (hap : a.isAP = true) {v : Term} (hv : inT v = true)
    (hlt : lt a v = true) : le (add a one) v = true := by
  cases v with
  | zero => rw [lt_zero_right] at hlt; exact Bool.noConfusion hlt
  | M => exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
  | omg _ => exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
  | phi _ _ => exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
  | psi _ _ => exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
  | Z _ => exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
  | add c d =>
    rw [Evidence.Cert.lt_ap_add hap] at hlt
    obtain ⟨_, _, hid, hdesc⟩ := inT_add hv
    by_cases hac : a = c
    · rw [hac]
      refine le_add_tail (le_one_inT hid ?_)
      intro hz; rw [hz] at hdesc; exact Bool.noConfusion hdesc
    · refine le_of_lt (lt_add_head hac ?_)
      rcases (Bool.or_eq_true _ _).mp hlt with he | hl
      · exact absurd (eq_of_beq he) hac
      · exact hl

/-- **`p` と `p ⊕ 1` のあいだには何も無い** — 𝔗(M) の上で。`CNVOps` §28 が `CNV` で言う
    `le_succT_of_lt` の 𝔗(M) 版。 -/
theorem le_succT_of_lt_inT : ∀ (a : Term), inT a = true → ∀ (v : Term), inT v = true →
    lt a v = true → le (succT a) v = true := by
  intro a
  induction a with
  | zero =>
    intro _ v hv hlt
    show le one v = true
    refine le_one_inT hv ?_
    intro hc
    rw [hc, lt_irrefl] at hlt
    exact Bool.noConfusion hlt
  | M => intro _ v hv hlt; exact le_succT_atom rfl hv hlt
  | omg _ _ => intro _ v hv hlt; exact le_succT_atom rfl hv hlt
  | phi _ _ _ _ => intro _ v hv hlt; exact le_succT_atom rfl hv hlt
  | psi _ _ _ _ => intro _ v hv hlt; exact le_succT_atom rfl hv hlt
  | Z _ _ => intro _ v hv hlt; exact le_succT_atom rfl hv hlt
  | add s t _ iht =>
    intro ha v hv hlt
    obtain ⟨_, _, hit, _⟩ := inT_add ha
    show le (add s (succT t)) v = true
    cases v with
    | zero => rw [lt_zero_right] at hlt; exact Bool.noConfusion hlt
    | M =>
      rw [lt_add_nsum (by intro hc; exact Term.noConfusion hc) rfl] at hlt
      exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
    | omg _ =>
      rw [lt_add_nsum (by intro hc; exact Term.noConfusion hc) rfl] at hlt
      exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
    | phi _ _ =>
      rw [lt_add_nsum (by intro hc; exact Term.noConfusion hc) rfl] at hlt
      exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
    | psi _ _ =>
      rw [lt_add_nsum (by intro hc; exact Term.noConfusion hc) rfl] at hlt
      exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
    | Z _ =>
      rw [lt_add_nsum (by intro hc; exact Term.noConfusion hc) rfl] at hlt
      exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
    | add c d =>
      obtain ⟨_, _, hid, _⟩ := inT_add hv
      by_cases heq : add s t = add c d
      · rw [heq, lt_irrefl] at hlt; exact Bool.noConfusion hlt
      · rw [lt_add_add heq] at hlt
        by_cases hsc : s = c
        · rw [if_pos hsc] at hlt
          rw [hsc]
          exact le_add_tail (iht hit d hid hlt)
        · rw [if_neg hsc] at hlt
          exact le_of_lt (lt_add_head hsc hlt)

/-! `plus g (ofNat m)` の成分列 — `1` を `m` 個継ぎ足すだけ。 -/

theorem filter_one_toList_inT {a : Term} (h : inT a = true) :
    (toList a).filter (fun x => le one x) = toList a :=
  filter_self_of_all _ _ (fun x hx => Evidence.Cert.le_one_ap (inTL_isAP h x hx))

theorem plus_ofNat_eq_inT {g : Term} (hg : inT g = true) (k : Nat) :
    plus g (ofNat (k + 1)) = ofList (toList g ++ List.replicate (k + 1) one) := by
  have hl : toList (ofNat (k + 1)) = one :: List.replicate k one := by
    rw [toList_ofNat (k + 1)]; rfl
  rw [plus_eq hl, filter_one_toList_inT hg, toList_ofNat (k + 1)]

theorem toList_plus_ofNat_inT {g : Term} (hg : inT g = true) : ∀ m,
    toList (plus g (ofNat m)) = toList g ++ List.replicate m one := by
  intro m
  cases m with
  | zero =>
    show toList (plus g zero) = toList g ++ []
    exact (List.append_nil _).symm
  | succ k =>
    rw [plus_ofNat_eq_inT hg k]
    refine toList_ofList _ ?_
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact inTL_isAP hg x h
    · rw [List.eq_of_mem_replicate h]; rfl

theorem plus_ofNat_step_inT {g : Term} (hg : inT g = true) (m : Nat) :
    plus g (ofNat (m + 1)) = succT (plus g (ofNat m)) := by
  rw [plus_ofNat_eq_inT hg m, ← ofList_toList_snoc_inT _ (inT_plus hg (inT_ofNat m)),
    toList_plus_ofNat_inT hg m, List.append_assoc, ← List.replicate_succ']

/-- **`splitFin` は引数を組み立て直す** — 𝔗(M) の上で。 -/
theorem splitFin_rebuild_inT (t : Term) (ht : inT t = true) :
    plus (splitFin t).1 (ofNat (splitFin t).2) = t := by
  have hcg : inT (splitFin t).1 = true := inT_splitFin ht
  have hF1 : ((toList t).reverse.dropWhile (fun x => x == one)).reverse
      ++ List.replicate (((toList t).reverse.takeWhile (fun x => x == one)).length) one
      = toList t := by
    have h := trailing_ones (toList t).reverse
    rwa [List.reverse_reverse] at h
  have hAP : ∀ x ∈ ((toList t).reverse.dropWhile (fun x => x == one)).reverse,
      x.isAP = true := by
    intro x hx
    exact inTL_isAP ht x (by rw [← hF1]; exact List.mem_append_left _ hx)
  have hg : toList (splitFin t).1
      = ((toList t).reverse.dropWhile (fun x => x == one)).reverse := by
    rw [splitFin_fst t, toList_ofList _ hAP]
  have hto : toList (plus (splitFin t).1 (ofNat (splitFin t).2)) = toList t := by
    rw [toList_plus_ofNat_inT hcg, hg]
    exact hF1
  rw [← inT_ofList_toList _ (inT_plus hcg (inT_ofNat _)), hto, inT_ofList_toList t ht]

theorem inT_dnArg {x : Term} (hx : inT x = true) : inT (dnArg x) = true := by
  have hg : inT (splitFin x).1 = true := inT_splitFin hx
  cases hs : splitFin x with
  | mk g m =>
    rw [hs] at hg
    rcases dnArg_or hs with h | ⟨_, h⟩
    · rw [h]; exact hx
    · rw [h]; exact inT_plus hg (inT_ofNat _)

/-- **D1** — `dnArg` は下げるだけ (𝔗(M) 版)。 -/
theorem dnArg_le_inT {x : Term} (hx : inT x = true) : le (dnArg x) x = true := by
  cases hs : splitFin x with
  | mk g m =>
    rcases dnArg_or hs with h | ⟨hm, h⟩
    · rw [h]; exact Evidence.WF.le_self _
    · have hcg : inT g = true := by
        have h0 := inT_splitFin hx; rw [hs] at h0; exact h0
      have hreb : plus g (ofNat m) = x := by
        have h0 := splitFin_rebuild_inT x hx; rw [hs] at h0; exact h0
      cases m with
      | zero => exact absurd hm (by omega)
      | succ k =>
        rw [h, ← hreb, show k + 1 - 1 = k from rfl, plus_ofNat_step_inT hcg k]
        exact le_of_lt (lt_succT_inT _ (inT_plus hcg (inT_ofNat k)))

/-- **D2** — 下げるのは高々 1 (𝔗(M) 版)。 -/
theorem dnArg_ge_inT {x y : Term} (hx : inT x = true) (hy : inT y = true)
    (h : lt x y = true) : le x (dnArg y) = true := by
  cases hs : splitFin y with
  | mk g m =>
    rcases dnArg_or hs with hd | ⟨hm, hd⟩
    · rw [hd]; exact le_of_lt h
    · have hcg : inT g = true := by
        have h0 := inT_splitFin hy; rw [hs] at h0; exact h0
      have hreb : plus g (ofNat m) = y := by
        have h0 := splitFin_rebuild_inT y hy; rw [hs] at h0; exact h0
      cases m with
      | zero => exact absurd hm (by omega)
      | succ k =>
        have hz : inT (plus g (ofNat k)) = true := inT_plus hcg (inT_ofNat k)
        have hy' : y = succT (plus g (ofNat k)) := by
          rw [← hreb, plus_ofNat_step_inT hcg k]
        rw [hd, show k + 1 - 1 = k from rfl]
        cases hle : le x (plus g (ofNat k)) with
        | true => rfl
        | false =>
          exfalso
          have hlt : lt (plus g (ofNat k)) x = true := lt_of_not_le_inT hx hz hle
          have hs2 : le y x = true := by
            rw [hy']; exact le_succT_of_lt_inT _ hz x hx hlt
          have hcon := lt_of_le_of_lt3 (inT_le_fragR y hy) (inT_le_fragR x hx)
            (inT_le_fragR y hy) hs2 h
          rw [lt_irrefl] at hcon
          exact Bool.noConfusion hcon

end

/-! ### §65.3 `ω^·` は 𝔗(M) の上で単調

`CNVOps` §26 は `CNV` の上で `ω^x = if isFixP x then x else φ̄0(dnArg x)` と書く。𝔗(M) では
枝が 2 つ増える: `M < x` の `ω̄^x` と、**不動点の範囲が広がる**こと。`CNV` では不動点は
`φ̄αβ` (`α ≠ 0`) だけだが、𝔗(M) では `M`・`ψκα`・`Zα` — 強臨界項はすべて自分自身が
`ω` の指数である。その述語は `TM/FS.lean` の `isFP zero` がすでにそのもので、`logOm` の
`φ̄0·` 節が使っているのと同じものである。

D3 (`CNVOps` §29) は使わない。結論が `le` であって `lt` ではないからで、`dnArg` が 2 つの
引数を潰しても困らない。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

theorem lt_eq_ltF_succ (s t : Term) : lt s t = ltF (2 * (s.deg + t.deg) + 7 + 1) s t := by
  rw [lt_eq_ltF s t (2 * (s.deg + t.deg) + 7 + 1) (by omega)]

/-- **`ω^·` の 3 つの形**、側条件なし。`isFP zero` が `CNVOps` §26 の `isFixP` の
    𝔗(M) 版 — 強臨界項もまた `ω^·` の不動点である。 -/
theorem phiNF_zero_eq_gen (x : Term) :
    (if x == M then M else phiNF zero x)
      = (if TM.Term.isFP zero x then x else phi zero (dnArg x)) := by
  cases x with
  | zero => exact phiNFsucc_zero_eq zero
  | omg a => exact phiNFsucc_zero_eq (omg a)
  | add u v => exact phiNFsucc_zero_eq (add u v)
  | M =>
    have h1 : TM.Term.isFP zero M = true := by
      unfold TM.Term.isFP
      rw [lt_zero_M]
      rfl
    rw [h1]
    rfl
  | psi k a =>
    have hz : lt zero (psi k a) = true := lt_zero_left (by intro hc; exact Term.noConfusion hc)
    have h1 : TM.Term.isFP zero (psi k a) = true := by
      unfold TM.Term.isFP
      rw [hz]
      rfl
    rw [h1]
    show phiNF zero (psi k a) = psi k a
    unfold phiNF
    rw [hz]
    rfl
  | Z a =>
    have hz : lt zero (Z a) = true := lt_zero_left (by intro hc; exact Term.noConfusion hc)
    have h1 : TM.Term.isFP zero (Z a) = true := by
      unfold TM.Term.isFP
      rw [hz]
      rfl
    rw [h1]
    show phiNF zero (Z a) = Z a
    unfold phiNF
    rw [hz]
    rfl
  | phi c d =>
    have h1 : TM.Term.isFP zero (phi c d) = lt zero c := by
      unfold TM.Term.isFP; rfl
    rw [h1]
    show (if lt zero c then phi c d else phiNFsucc zero (phi c d))
        = (if lt zero c then phi c d else phi zero (dnArg (phi c d)))
    by_cases hc : lt zero c = true
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
      exact phiNFsucc_zero_eq (phi c d)

theorem omegaNF_eq_gen (x : Term) :
    omegaNF x = if lt M x then omg x
                else if TM.Term.isFP zero x then x else phi zero (dnArg x) := by
  show (if lt M x then omg x else if x == M then M else phiNF zero x) = _
  rw [phiNF_zero_eq_gen x]

/-! `ω̄^·` の枝に落ちるときの比較 (2.3.2, 2.3.3, 2.3.12)。 -/

theorem lt_phi_omg (a b y : Term) : lt (phi a b) (omg y) = true := by
  rw [lt_eq_ltF_succ]; exact ltF_succ_phi_omg _ _ _ _

theorem lt_isFP_omg {x y : Term} (hfix : TM.Term.isFP zero x = true) :
    lt x (omg y) = true := by
  cases x with
  | zero => exact Bool.noConfusion hfix
  | omg _ => exact Bool.noConfusion hfix
  | add _ _ => exact Bool.noConfusion hfix
  | M => rw [lt_eq_ltF_succ]; exact ltF_succ_M_omg _ _
  | psi k a => rw [lt_eq_ltF_succ]; exact ltF_succ_psi_omg _ _ _ _
  | Z a => rw [lt_eq_ltF_succ]; exact ltF_succ_Z_omg _ _ _
  | phi a b => exact lt_phi_omg a b y

theorem lt_omg_omg {x y : Term} (h : lt x y = true) : lt (omg x) (omg y) = true := by
  have hne : omg x ≠ omg y := by
    intro hc
    injection hc with h1
    rw [h1, lt_irrefl] at h
    exact Bool.noConfusion h
  rw [lt_eq_ltF_succ, ltF_succ_omg_omg _ hne,
    ← lt_eq_ltF x y _ (by show x.deg + y.deg ≤ 2 * ((1 + x.deg) + (1 + y.deg)) + 7; omega)]
  exact h

/-! 2.3.4 と 2.3.5 — 強臨界項と `φ̄` のあいだ。 -/

theorem lt_psi_phi_of_le {k a c w : Term} (h : le (psi k a) w = true) :
    lt (psi k a) (phi c w) = true := by
  rw [lt_eq_ltF_succ, ltF_succ_psi_phi,
    show ltF (2 * ((psi k a).deg + (phi c w).deg) + 7) (psi k a) w = lt (psi k a) w from
      (lt_eq_ltF (psi k a) w _ (by
        show (1 + k.deg + a.deg) + w.deg
          ≤ 2 * ((1 + k.deg + a.deg) + (1 + c.deg + w.deg)) + 7
        omega)).symm]
  rcases (Bool.or_eq_true _ _).mp h with he | hl
  · rw [he, Bool.or_true, Bool.true_or, Bool.true_or]
  · rw [hl, Bool.or_true]

theorem lt_Z_phi_of_le {e c w : Term} (h : le (Z e) w = true) :
    lt (Z e) (phi c w) = true := by
  rw [lt_eq_ltF_succ, ltF_succ_Z_phi,
    show ltF (2 * ((Z e).deg + (phi c w).deg) + 7) (Z e) w = lt (Z e) w from
      (lt_eq_ltF (Z e) w _ (by
        show (1 + e.deg) + w.deg ≤ 2 * ((1 + e.deg) + (1 + c.deg + w.deg)) + 7
        omega)).symm]
  rcases (Bool.or_eq_true _ _).mp h with he | hl
  · rw [he, Bool.or_true, Bool.true_or, Bool.true_or]
  · rw [hl, Bool.or_true]

theorem lt_phi_psi_of {a b k c : Term} (h1 : lt a (psi k c) = true)
    (h2 : lt b (psi k c) = true) : lt (phi a b) (psi k c) = true := by
  rw [lt_eq_ltF_succ, ltF_succ_phi_psi,
    show ltF (2 * ((phi a b).deg + (psi k c).deg) + 7) a (psi k c) = lt a (psi k c) from
      (lt_eq_ltF a (psi k c) _ (by
        show a.deg + (1 + k.deg + c.deg)
          ≤ 2 * ((1 + a.deg + b.deg) + (1 + k.deg + c.deg)) + 7
        omega)).symm,
    show ltF (2 * ((phi a b).deg + (psi k c).deg) + 7) b (psi k c) = lt b (psi k c) from
      (lt_eq_ltF b (psi k c) _ (by
        show b.deg + (1 + k.deg + c.deg)
          ≤ 2 * ((1 + a.deg + b.deg) + (1 + k.deg + c.deg)) + 7
        omega)).symm, h1, h2]
  rfl

theorem lt_phi_Z_of {a b d : Term} (h1 : lt a (Z d) = true)
    (h2 : lt b (Z d) = true) : lt (phi a b) (Z d) = true := by
  rw [lt_eq_ltF_succ, ltF_succ_phi_Z,
    show ltF (2 * ((phi a b).deg + (Z d).deg) + 7) a (Z d) = lt a (Z d) from
      (lt_eq_ltF a (Z d) _ (by
        show a.deg + (1 + d.deg) ≤ 2 * ((1 + a.deg + b.deg) + (1 + d.deg)) + 7
        omega)).symm,
    show ltF (2 * ((phi a b).deg + (Z d).deg) + 7) b (Z d) = lt b (Z d) from
      (lt_eq_ltF b (Z d) _ (by
        show b.deg + (1 + d.deg) ≤ 2 * ((1 + a.deg + b.deg) + (1 + d.deg)) + 7
        omega)).symm, h1, h2]
  rfl

/-- 不動点は `φ̄0w` の下 — `x ≤ w` があれば。`x = M` だけは除く (`M < φ̄0w` は偽)。 -/
theorem lt_isFP_phi_zero {x w : Term} (hfix : TM.Term.isFP zero x = true) (hne : x ≠ M)
    (h : le x w = true) : lt x (phi zero w) = true := by
  cases x with
  | zero => exact Bool.noConfusion hfix
  | omg _ => exact Bool.noConfusion hfix
  | add _ _ => exact Bool.noConfusion hfix
  | M => exact absurd rfl hne
  | psi k a => exact lt_psi_phi_of_le h
  | Z e => exact lt_Z_phi_of_le h
  | phi c d =>
    have hc : lt zero c = true := by
      have h1 : TM.Term.isFP zero (phi c d) = lt zero c := by unfold TM.Term.isFP; rfl
      rw [h1] at hfix; exact hfix
    have hzc : ¬ (c = zero) := by
      intro hcc
      rw [hcc, lt_irrefl] at hc
      exact Bool.noConfusion hc
    have hnn : phi c d ≠ phi zero w := by
      intro hcc
      injection hcc with h1 _
      exact hzc h1
    rw [lt_phi_phi hnn, if_neg hzc,
      if_neg (by rw [lt_zero_right]; exact Bool.noConfusion)]
    exact h

/-- `φ̄0z` は不動点 `y` の下 — `z < y` があれば。 -/
theorem lt_phi_zero_isFP {z y : Term} (hfix : TM.Term.isFP zero y = true)
    (h : lt z y = true) : lt (phi zero z) y = true := by
  cases y with
  | zero => exact Bool.noConfusion hfix
  | omg _ => exact Bool.noConfusion hfix
  | add _ _ => exact Bool.noConfusion hfix
  | M => exact lt_phi_M zero z
  | psi k a =>
    exact lt_phi_psi_of (lt_zero_left (by intro hc; exact Term.noConfusion hc)) h
  | Z e =>
    exact lt_phi_Z_of (lt_zero_left (by intro hc; exact Term.noConfusion hc)) h
  | phi c d =>
    have hc : lt zero c = true := by
      have h1 : TM.Term.isFP zero (phi c d) = lt zero c := by unfold TM.Term.isFP; rfl
      rw [h1] at hfix; exact hfix
    have hzc : ¬ ((zero : Term) = c) := by
      intro hcc
      rw [← hcc, lt_irrefl] at hc
      exact Bool.noConfusion hc
    have hnn : phi zero z ≠ phi c d := by
      intro hcc
      injection hcc with h1 _
      exact hzc h1
    rw [lt_phi_phi hnn, if_neg hzc, if_pos hc]
    exact h

theorem le_phi_zero_arg {a b : Term} (h : le a b = true) :
    le (phi zero a) (phi zero b) = true := by
  rcases (Bool.or_eq_true _ _).mp h with he | hl
  · rw [eq_of_beq he]; exact Evidence.WF.le_self _
  · exact le_of_lt (lt_phi_arg hl)

/-- **`ω^·` は 𝔗(M) の上で単調** (非狭義)。D1 と D2 だけを使い、D3 は使わない。 -/
theorem le_omegaNF_of_lt_inT {x y : Term} (hx : inT x = true) (hy : inT y = true)
    (h : lt x y = true) : le (omegaNF x) (omegaNF y) = true := by
  rw [omegaNF_eq_gen x, omegaNF_eq_gen y]
  by_cases hMy : lt M y = true
  · rw [if_pos hMy]
    by_cases hMx : lt M x = true
    · rw [if_pos hMx]; exact le_of_lt (lt_omg_omg h)
    · rw [if_neg hMx]
      by_cases hfx : TM.Term.isFP zero x = true
      · rw [if_pos hfx]; exact le_of_lt (lt_isFP_omg hfx)
      · rw [if_neg hfx]; exact le_of_lt (lt_phi_omg _ _ _)
  · rw [if_neg hMy]
    have hMx : ¬ (lt M x = true) := by
      intro hc
      exact hMy (lt_trans_inT inT_M hx hy hc h)
    rw [if_neg hMx]
    have hxM : x ≠ M := by
      intro hc
      rw [hc] at h
      exact hMy h
    by_cases hfx : TM.Term.isFP zero x = true
    · rw [if_pos hfx]
      by_cases hfy : TM.Term.isFP zero y = true
      · rw [if_pos hfy]; exact le_of_lt h
      · rw [if_neg hfy]
        exact le_of_lt (lt_isFP_phi_zero hfx hxM (dnArg_ge_inT hx hy h))
    · rw [if_neg hfx]
      by_cases hfy : TM.Term.isFP zero y = true
      · rw [if_pos hfy]
        refine le_of_lt (lt_phi_zero_isFP hfy ?_)
        exact lt_of_le_of_lt3 (inT_le_fragR _ (inT_dnArg hx)) (inT_le_fragR x hx)
          (inT_le_fragR y hy) (dnArg_le_inT hx) h
      · rw [if_neg hfy]
        refine le_phi_zero_arg ?_
        exact le_trans_inT (inT_dnArg hx) hx (inT_dnArg hy)
          (dnArg_le_inT hx) (dnArg_ge_inT hx hy h)

theorem omegaNF_mono_inT {x y : Term} (hx : inT x = true) (hy : inT y = true)
    (h : le x y = true) : le (omegaNF x) (omegaNF y) = true := by
  rcases (Bool.or_eq_true _ _).mp h with he | hl
  · rw [eq_of_beq he]; exact Evidence.WF.le_self _
  · exact le_omegaNF_of_lt_inT hx hy hl

end

/-! ### §65.4 `logOm`・`subAP`・`plus` の単調性、そして SC の一段

3 つとも側条件つきで、どれも側条件を落とすと偽 (§65.7 に反例を凍結)。

  `logOm`  加法主要な項の上でのみ単調。`Ω ⊕ Ω ≤ ω^Ω` だが `logOm (Ω ⊕ Ω) = Ω ⊕ Ω > Ω`。
  `subAP`  `w ≤ x` と `w ≤ y` の上でのみ単調。`w = M`, `x = Ω`, `y = M` が最小反例。
  `plus`   側条件なし。
  SC の一段  `w ∈ SC` かつ `w ≤ p` (`p` は加法主要) なら `w ≤ logOm p`。**これが (G1) の
           側条件が `w ∈ SC` でなければならない理由**で、`w = p = 1` で破れる。 -/

section
open Trans.Recal (bplus)
open TM TM.Term
open Evidence.WF
open Trans.Dict (logOm subAP divAP mulL)

theorem plus_one_eq_succT_inT {a : Term} (ha : inT a = true) : plus a one = succT a := by
  rw [plus_eq (show toList (one : Term) = [one] from rfl), filter_one_toList_inT ha]
  exact ofList_toList_snoc_inT a ha

theorem inT_succT_inT {a : Term} (ha : inT a = true) : inT (succT a) = true := by
  rw [← plus_one_eq_succT_inT ha]
  exact inT_plus ha inT_one

/-! 2.3.4/2.3.5 の逆読み — `φ̄` と強臨界項のあいだの比較から引数の比較を取り出す。 -/

theorem lt_arg_of_phi_lt_psi {a b k c : Term} (h : lt (phi a b) (psi k c) = true) :
    lt b (psi k c) = true := by
  rw [lt_eq_ltF_succ, ltF_succ_phi_psi,
    show ltF (2 * ((phi a b).deg + (psi k c).deg) + 7) b (psi k c) = lt b (psi k c) from
      (lt_eq_ltF b (psi k c) _ (by
        show b.deg + (1 + k.deg + c.deg)
          ≤ 2 * ((1 + a.deg + b.deg) + (1 + k.deg + c.deg)) + 7
        omega)).symm] at h
  exact ((Bool.and_eq_true _ _).mp h).2

theorem lt_arg_of_phi_lt_Z {a b d : Term} (h : lt (phi a b) (Z d) = true) :
    lt b (Z d) = true := by
  rw [lt_eq_ltF_succ, ltF_succ_phi_Z,
    show ltF (2 * ((phi a b).deg + (Z d).deg) + 7) b (Z d) = lt b (Z d) from
      (lt_eq_ltF b (Z d) _ (by
        show b.deg + (1 + d.deg) ≤ 2 * ((1 + a.deg + b.deg) + (1 + d.deg)) + 7
        omega)).symm] at h
  exact ((Bool.and_eq_true _ _).mp h).2

theorem le_of_psi_lt_phi_zero {k a e : Term} (h : lt (psi k a) (phi zero e) = true) :
    le (psi k a) e = true := by
  rw [lt_eq_ltF_succ, ltF_succ_psi_phi,
    show ltF (2 * ((psi k a).deg + (phi zero e).deg) + 7) (psi k a) e = lt (psi k a) e from
      (lt_eq_ltF (psi k a) e _ (by
        show (1 + k.deg + a.deg) + e.deg
          ≤ 2 * ((1 + k.deg + a.deg) + (1 + (zero : Term).deg + e.deg)) + 7
        omega)).symm,
    show ((psi k a) == (zero : Term)) = false from rfl, ltF_right_zero,
    Bool.false_or, Bool.or_false] at h
  exact h

theorem le_of_Z_lt_phi_zero {d e : Term} (h : lt (Z d) (phi zero e) = true) :
    le (Z d) e = true := by
  rw [lt_eq_ltF_succ, ltF_succ_Z_phi,
    show ltF (2 * ((Z d).deg + (phi zero e).deg) + 7) (Z d) e = lt (Z d) e from
      (lt_eq_ltF (Z d) e _ (by
        show (1 + d.deg) + e.deg
          ≤ 2 * ((1 + d.deg) + (1 + (zero : Term).deg + e.deg)) + 7
        omega)).symm,
    show ((Z d) == (zero : Term)) = false from rfl, ltF_right_zero,
    Bool.false_or, Bool.or_false] at h
  exact h

theorem le_arg_of_le_pow {b d : Term} (h : le (phi zero b) (phi zero d) = true) :
    le b d = true := by
  rcases (Bool.or_eq_true _ _).mp h with he | hl
  · have hq := eq_of_beq he
    injection hq with _ h2
    rw [h2]
    exact Evidence.WF.le_self _
  · rw [lt_pow] at hl
    exact le_of_lt hl

/-! `logOm (φ̄0b)` は `b` か `b ⊕ 1`。どちらでも `b < y` から `logOm (φ̄0b) ≤ y` が出る。 -/

theorem le_shift_of_lt {b y : Term} (hb : inT b = true) (hy : inT y = true)
    (h : lt b y = true) : le (logOm (phi zero b)) y = true := by
  show le (if TM.Term.phiShifted zero b then plus b one else b) y = true
  by_cases hs : TM.Term.phiShifted zero b = true
  · rw [if_pos hs, plus_one_eq_succT_inT hb]
    exact le_succT_of_lt_inT b hb y hy h
  · rw [if_neg hs]
    exact le_of_lt h

theorem le_logOm_phi_zero_of_le {x e : Term} (hx : inT x = true) (he : inT e = true)
    (h : le x e = true) : le x (logOm (phi zero e)) = true := by
  show le x (if TM.Term.phiShifted zero e then plus e one else e) = true
  by_cases hs : TM.Term.phiShifted zero e = true
  · rw [if_pos hs]
    refine le_trans_inT hx he (inT_plus he inT_one) h ?_
    rw [plus_one_eq_succT_inT he]
    exact le_of_lt (lt_succT_inT e he)
  · rw [if_neg hs]
    exact h

theorem le_shift_shift {b d : Term} (hb : inT b = true) (hd : inT d = true)
    (h : le b d = true) :
    le (logOm (phi zero b)) (logOm (phi zero d)) = true := by
  show le (if TM.Term.phiShifted zero b then plus b one else b)
         (if TM.Term.phiShifted zero d then plus d one else d) = true
  by_cases hsb : TM.Term.phiShifted zero b = true
  · rw [if_pos hsb, plus_one_eq_succT_inT hb]
    by_cases hsd : TM.Term.phiShifted zero d = true
    · rw [if_pos hsd, plus_one_eq_succT_inT hd]
      rcases (Bool.or_eq_true _ _).mp h with he | hl
      · rw [eq_of_beq he]; exact Evidence.WF.le_self _
      · exact le_trans_inT (inT_succT_inT hb) hd (inT_succT_inT hd)
          (le_succT_of_lt_inT b hb d hd hl) (le_of_lt (lt_succT_inT d hd))
    · rw [if_neg hsd]
      have hne : b ≠ d := by
        intro hc
        rw [hc] at hsb
        exact hsd hsb
      exact le_succT_of_lt_inT b hb d hd (lt_of_le_of_ne h hne)
  · rw [if_neg hsb]
    by_cases hsd : TM.Term.phiShifted zero d = true
    · rw [if_pos hsd]
      refine le_trans_inT hb hd (inT_plus hd inT_one) h ?_
      rw [plus_one_eq_succT_inT hd]
      exact le_of_lt (lt_succT_inT d hd)
    · rw [if_neg hsd]
      exact h


/-- `logOm` は `φ̄0·` 以外の形では恒等。 -/
theorem logOm_eq_self_of_ne : ∀ (x : Term), (∀ b, x ≠ phi zero b) → logOm x = x := by
  intro x hne
  cases x with
  | zero => rfl
  | M => rfl
  | omg _ => rfl
  | psi _ _ => rfl
  | Z _ => rfl
  | add _ _ => rfl
  | phi c d =>
    cases c with
    | zero => exact absurd rfl (hne d)
    | M => rfl
    | omg _ => rfl
    | phi _ _ => rfl
    | psi _ _ => rfl
    | Z _ => rfl
    | add _ _ => rfl

/-- `c ≠ 0` の `φ̄cd` が `φ̄0e` の下なら `φ̄cd ≤ e` (2.3.13(iii))。 -/
theorem le_of_phi_lt_phi_zero {c d e : Term} (hc : ¬ (c = zero))
    (hlt : lt (phi c d) (phi zero e) = true) : le (phi c d) e = true := by
  have hne : phi c d ≠ phi zero e := by
    intro hcc
    injection hcc with h1 _
    exact hc h1
  rw [lt_phi_phi hne, if_neg hc,
    if_neg (by rw [lt_zero_right]; exact Bool.noConfusion)] at hlt
  exact hlt

/-- `φ̄0b < φ̄ce` (`c ≠ 0`) なら `b < φ̄ce` (2.3.13(i))。 -/
theorem lt_arg_of_pow_lt_phi {b c e : Term} (hc : ¬ ((zero : Term) = c))
    (hlt : lt (phi zero b) (phi c e) = true) : lt b (phi c e) = true := by
  have hne : phi zero b ≠ phi c e := by
    intro hcc
    injection hcc with h1 _
    exact hc h1
  rw [lt_phi_phi hne, if_neg hc, if_pos (lt_zero_left (fun hcc => hc hcc.symm))] at hlt
  exact hlt

/-- `logOm x = x` の側の単調性。`hkey` は「`x < φ̄0e` なら `x ≤ e`」で、`x` の形ごとに供給する。 -/
theorem logOm_mono_self {x y : Term} (hlx : logOm x = x) (hxne : ∀ e, x ≠ phi zero e)
    (hkey : ∀ e, lt x (phi zero e) = true → le x e = true)
    (hx : inT x = true) (hy : inT y = true) (hya : y.isAP = true) (h : le x y = true) :
    le (logOm x) (logOm y) = true := by
  rw [hlx]
  cases y with
  | zero => exact Bool.noConfusion hya
  | add _ _ => exact Bool.noConfusion hya
  | M => exact h
  | omg _ => exact h
  | psi _ _ => exact h
  | Z _ => exact h
  | phi c e =>
    cases c with
    | zero =>
      refine le_logOm_phi_zero_of_le hx (inT_phi4 hy).2.1 ?_
      exact hkey e (lt_of_le_of_ne h (hxne e))
    | M => exact h
    | omg _ => exact h
    | phi _ _ => exact h
    | psi _ _ => exact h
    | Z _ => exact h
    | add _ _ => exact h

/-- `x = φ̄0b` の側の単調性。 -/
theorem logOm_mono_pow {b y : Term} (hx : inT (phi zero b) = true) (hy : inT y = true)
    (hya : y.isAP = true) (h : le (phi zero b) y = true) :
    le (logOm (phi zero b)) (logOm y) = true := by
  have hib : inT b = true := (inT_phi4 hx).2.1
  have hbM : lt b M = true := (inT_phi4 hx).2.2.2
  cases y with
  | zero => exact Bool.noConfusion hya
  | add _ _ => exact Bool.noConfusion hya
  | M => exact le_shift_of_lt hib inT_M hbM
  | omg a =>
    refine le_shift_of_lt hib hy ?_
    exact lt_trans_inT hib inT_M hy hbM (by rw [lt_eq_ltF_succ]; exact ltF_succ_M_omg _ _)
  | psi k a =>
    refine le_shift_of_lt hib hy ?_
    exact lt_arg_of_phi_lt_psi (lt_of_le_of_ne h (by intro hc; exact Term.noConfusion hc))
  | Z d =>
    refine le_shift_of_lt hib hy ?_
    exact lt_arg_of_phi_lt_Z (lt_of_le_of_ne h (by intro hc; exact Term.noConfusion hc))
  | phi c e =>
    cases c with
    | zero => exact le_shift_shift hib (inT_phi4 hy).2.1 (le_arg_of_le_pow h)
    | M =>
      refine le_shift_of_lt hib hy (lt_arg_of_pow_lt_phi ?_ ?_)
      · intro hc; exact Term.noConfusion hc
      · exact lt_of_le_of_ne h (by intro hc; injection hc with h1 _; exact Term.noConfusion h1)
    | omg _ =>
      refine le_shift_of_lt hib hy (lt_arg_of_pow_lt_phi ?_ ?_)
      · intro hc; exact Term.noConfusion hc
      · exact lt_of_le_of_ne h (by intro hc; injection hc with h1 _; exact Term.noConfusion h1)
    | phi _ _ =>
      refine le_shift_of_lt hib hy (lt_arg_of_pow_lt_phi ?_ ?_)
      · intro hc; exact Term.noConfusion hc
      · exact lt_of_le_of_ne h (by intro hc; injection hc with h1 _; exact Term.noConfusion h1)
    | psi _ _ =>
      refine le_shift_of_lt hib hy (lt_arg_of_pow_lt_phi ?_ ?_)
      · intro hc; exact Term.noConfusion hc
      · exact lt_of_le_of_ne h (by intro hc; injection hc with h1 _; exact Term.noConfusion h1)
    | Z _ =>
      refine le_shift_of_lt hib hy (lt_arg_of_pow_lt_phi ?_ ?_)
      · intro hc; exact Term.noConfusion hc
      · exact lt_of_le_of_ne h (by intro hc; injection hc with h1 _; exact Term.noConfusion h1)
    | add _ _ =>
      refine le_shift_of_lt hib hy (lt_arg_of_pow_lt_phi ?_ ?_)
      · intro hc; exact Term.noConfusion hc
      · exact lt_of_le_of_ne h (by intro hc; injection hc with h1 _; exact Term.noConfusion h1)

/-- **`logOm` は加法主要な項の上で単調。** 加法主要を落とすと偽 (§65.7)。 -/
theorem logOm_mono_inT {x y : Term} (hxa : x.isAP = true) (hya : y.isAP = true)
    (hx : inT x = true) (hy : inT y = true) (h : le x y = true) :
    le (logOm x) (logOm y) = true := by
  cases x with
  | zero => exact Bool.noConfusion hxa
  | add _ _ => exact Bool.noConfusion hxa
  | M =>
    refine logOm_mono_self rfl (fun e hc => Term.noConfusion hc) (fun e hlt => ?_) hx hy hya h
    exact absurd hlt (by
      rw [show lt (M : Term) (phi zero e) = false from by
        rw [lt_eq_ltF_succ]; exact ltF_succ_M_phi _ _ _]
      exact Bool.noConfusion)
  | omg a =>
    refine logOm_mono_self rfl (fun e hc => Term.noConfusion hc) (fun e hlt => ?_) hx hy hya h
    exact absurd hlt (by
      rw [show lt (omg a) (phi zero e) = false from by
        rw [lt_eq_ltF_succ]; exact ltF_succ_omg_phi _ _ _ _]
      exact Bool.noConfusion)
  | psi k a =>
    exact logOm_mono_self rfl (fun e hc => Term.noConfusion hc)
      (fun _ hlt => le_of_psi_lt_phi_zero hlt) hx hy hya h
  | Z d =>
    exact logOm_mono_self rfl (fun e hc => Term.noConfusion hc)
      (fun _ hlt => le_of_Z_lt_phi_zero hlt) hx hy hya h
  | phi c d =>
    cases c with
    | zero => exact logOm_mono_pow hx hy hya h
    | M =>
      exact logOm_mono_self rfl (fun e hc => by injection hc with h1 _; exact Term.noConfusion h1)
        (fun _ hlt => le_of_phi_lt_phi_zero (fun hc => Term.noConfusion hc) hlt) hx hy hya h
    | omg _ =>
      exact logOm_mono_self rfl (fun e hc => by injection hc with h1 _; exact Term.noConfusion h1)
        (fun _ hlt => le_of_phi_lt_phi_zero (fun hc => Term.noConfusion hc) hlt) hx hy hya h
    | phi _ _ =>
      exact logOm_mono_self rfl (fun e hc => by injection hc with h1 _; exact Term.noConfusion h1)
        (fun _ hlt => le_of_phi_lt_phi_zero (fun hc => Term.noConfusion hc) hlt) hx hy hya h
    | psi _ _ =>
      exact logOm_mono_self rfl (fun e hc => by injection hc with h1 _; exact Term.noConfusion h1)
        (fun _ hlt => le_of_phi_lt_phi_zero (fun hc => Term.noConfusion hc) hlt) hx hy hya h
    | Z _ =>
      exact logOm_mono_self rfl (fun e hc => by injection hc with h1 _; exact Term.noConfusion h1)
        (fun _ hlt => le_of_phi_lt_phi_zero (fun hc => Term.noConfusion hc) hlt) hx hy hya h
    | add _ _ =>
      exact logOm_mono_self rfl (fun e hc => by injection hc with h1 _; exact Term.noConfusion h1)
        (fun _ hlt => le_of_phi_lt_phi_zero (fun hc => Term.noConfusion hc) hlt) hx hy hya h

/-! `subAP w` — 頭部がちょうど `w` なら落とし、そうでなければ何もしない。 -/

theorem subAP_nil (w x : Term) (h : toList x = []) : subAP w x = zero := by
  show (match toList x with
        | [] => zero
        | p :: rest => if p == w then ofList rest else x) = _
  rw [h]

theorem subAP_cons (w x b : Term) (s : List Term) (h : toList x = b :: s) :
    subAP w x = if b == w then ofList s else x := by
  show (match toList x with
        | [] => zero
        | p :: rest => if p == w then ofList rest else x) = _
  rw [h]

theorem le_tail_of_le_add {u A B : Term} (h : le (add u A) (add u B) = true) :
    le A B = true := by
  by_cases heq : add u A = add u B
  · injection heq with _ h2
    rw [h2]
    exact Evidence.WF.le_self _
  · rcases (Bool.or_eq_true _ _).mp h with he | hl
    · exact absurd (eq_of_beq he) heq
    · rw [lt_add_add heq, if_pos rfl] at hl
      exact le_of_lt hl

/-- **`subAP w` は `{x : w ≤ x}` の上で単調。** 側条件を落とすと偽 (§65.7)。 -/
theorem subAP_mono_inT {w x y : Term} (hx : inT x = true) (hy : inT y = true)
    (hwx : lt x w = false) (h : le x y = true) :
    le (subAP w x) (subAP w y) = true := by
  obtain ⟨hcx, hdx⟩ := inT_toList x hx
  cases hxl : toList x with
  | nil => rw [subAP_nil w x hxl]; exact le_zero_left _
  | cons b s =>
    cases hyl : toList y with
    | nil =>
      exfalso
      have hyz : y = zero := toList_eq_nil y hyl
      rw [hyz] at h
      have hz : x = zero := by
        rcases (Bool.or_eq_true _ _).mp h with he | hl
        · exact eq_of_beq he
        · rw [lt_zero_right] at hl; exact Bool.noConfusion hl
      rw [hz] at hxl
      exact absurd (show b :: s = ([] : List Term) from hxl.symm) (List.cons_ne_nil b s)
    | cons c t =>
      rw [subAP_cons w x b s hxl, subAP_cons w y c t hyl]
      have hbc : le b c = true := hd_mono_inT hx hy hxl hyl h
      have hapb : b.isAP = true := inTL_isAP hx b (by rw [hxl]; exact List.Mem.head _)
      have hapc : c.isAP = true := inTL_isAP hy c (by rw [hyl]; exact List.Mem.head _)
      have hxe : x = ofList (b :: s) := by rw [← hxl, inT_ofList_toList x hx]
      have hye : y = ofList (c :: t) := by rw [← hyl, inT_ofList_toList y hy]
      rw [hxl] at hcx hdx
      obtain ⟨_, hcs⟩ := inTL_cons.mp hcx
      have hds := descL_tail hdx
      have his : inT (ofList s) = true := inT_ofList s hcs hds
      by_cases hcw : (c == w) = true
      · have hcw' : c = w := eq_of_beq hcw
        rw [if_pos hcw]
        by_cases hbw : (b == w) = true
        · rw [if_pos hbw]
          have hbw' : b = w := eq_of_beq hbw
          cases hs : s with
          | nil => exact le_zero_left _
          | cons a s' =>
            cases ht : t with
            | nil =>
              exfalso
              have hy' : y = w := by rw [hye, ht, hcw']; rfl
              have hx' : x = add w (ofList (a :: s')) := by rw [hxe, hs, hbw']; rfl
              have hlt : lt y x = true := by
                rw [hy', hx']
                exact lt_head_add (by rw [← hbw']; exact hapb) _
              rcases (Bool.or_eq_true _ _).mp h with he | hl
              · rw [eq_of_beq he, lt_irrefl] at hlt; exact Bool.noConfusion hlt
              · rw [lt_asymm_inT hx hy hl] at hlt; exact Bool.noConfusion hlt
            | cons d t' =>
              refine le_tail_of_le_add (u := w) ?_
              have hx' : x = add w (ofList (a :: s')) := by rw [hxe, hs, hbw']; rfl
              have hy' : y = add w (ofList (d :: t')) := by rw [hye, ht, hcw']; rfl
              rw [← hx', ← hy']
              exact h
        · exfalso
          have hbne : b ≠ w := fun hc => hbw (beq_of_eq hc)
          have hbltw : lt b w = true := by
            rw [← hcw']
            exact lt_of_le_of_ne hbc (by rw [hcw']; exact hbne)
          have hlt : lt x w = true := by
            rw [hxe, lt_ofList_nsum (by rw [← hcw']; exact hapc)]
            exact hbltw
          rw [hwx] at hlt
          exact Bool.noConfusion hlt
      · rw [if_neg hcw]
        by_cases hbw : (b == w) = true
        · rw [if_pos hbw]
          have hbw' : b = w := eq_of_beq hbw
          have hwc : lt w c = true := by
            rw [← hbw']
            exact lt_of_le_of_ne hbc (fun hc => hcw (beq_of_eq (hc.symm.trans hbw')))
          have hlsc : lt (ofList s) c = true := by
            cases hs : s with
            | nil => exact lt_zero_left (ne_zero_of_isAP hapc)
            | cons a s' =>
              rw [lt_ofList_nsum hapc]
              have haw : le a b = true := by
                rw [hs] at hdx
                exact (descL_cons.mp hdx).1
              have hia : inT a = true :=
                inTL_inT hx a (by rw [hxl, hs]; exact List.Mem.tail b (List.Mem.head _))
              exact lt_of_le_of_lt3 (inT_le_fragR a hia)
                (inT_le_fragR b (inTL_inT hx b (by rw [hxl]; exact List.Mem.head _)))
                (inT_le_fragR c (inTL_inT hy c (by rw [hyl]; exact List.Mem.head _)))
                haw (by rw [hbw']; exact hwc)
          refine le_of_lt (lt_of_lt_of_le3 (inT_le_fragR _ his)
            (inT_le_fragR c (inTL_inT hy c (by rw [hyl]; exact List.Mem.head _)))
            (inT_le_fragR y hy) hlsc (le_hd_self_inT hy hyl))
        · rw [if_neg hbw]
          exact h

/-! `plus e ·` の単調性。`e` の成分列の頭で場合分けし、尾に帰納する。 -/

theorem ofList_cons_ne_nil {a : Term} {L : List Term} (h : L ≠ []) :
    ofList (a :: L) = add a (ofList L) := by
  cases L with
  | nil => exact absurd rfl h
  | cons b t => rfl

theorem append_toList_ne_nil {L : List Term} {x x1 : Term} {X' : List Term}
    (hX : toList x = x1 :: X') : L ++ toList x ≠ [] := by
  rw [hX]
  cases L with
  | nil => exact List.cons_ne_nil x1 X'
  | cons a u => exact List.cons_ne_nil a (u ++ (x1 :: X'))

/-- 頭部が下なら和も下 (右辺の成分列が分かっているとき)。 -/
theorem lt_add_of_lt_hd {a A y y1 : Term} {Y' : List Term} (hy : inT y = true)
    (hY : toList y = y1 :: Y') (h : lt a y1 = true) : lt (add a A) y = true := by
  have hap : y1.isAP = true := inTL_isAP hy y1 (by rw [hY]; exact List.Mem.head _)
  have hye : y = ofList (y1 :: Y') := by rw [← hY, inT_ofList_toList y hy]
  rw [hye]
  cases Y' with
  | nil =>
    show lt (add a A) y1 = true
    rw [lt_add_nsum (ne_zero_of_isAP hap) (nsum_of_isAP hap)]
    exact h
  | cons d u =>
    show lt (add a A) (add y1 (ofList (d :: u))) = true
    refine lt_add_head ?_ h
    intro hc
    rw [hc, lt_irrefl] at h
    exact Bool.noConfusion h

theorem lt_of_hd_lt {e y e1 y1 : Term} {E' Y' : List Term} (he : inT e = true)
    (hy : inT y = true) (hE : toList e = e1 :: E') (hY : toList y = y1 :: Y')
    (h : lt e1 y1 = true) : lt e y = true := by
  have hee : e = ofList (e1 :: E') := by rw [← hE, inT_ofList_toList e he]
  have hi1 : inT e1 = true := inTL_inT he e1 (by rw [hE]; exact List.Mem.head _)
  have hj1 : inT y1 = true := inTL_inT hy y1 (by rw [hY]; exact List.Mem.head _)
  cases E' with
  | nil =>
    rw [show e = e1 from hee]
    exact lt_of_lt_of_le3 (inT_le_fragR e1 hi1) (inT_le_fragR y1 hj1)
      (inT_le_fragR y hy) h (le_hd_self_inT hy hY)
  | cons f F =>
    rw [hee]
    show lt (add e1 (ofList (f :: F))) y = true
    exact lt_add_of_lt_hd hy hY h

theorem plus_cons {e x e1 e' x1 : Term} {E' X' : List Term} (he : inT e = true)
    (hx : inT x = true) (hE : toList e = e1 :: E') (hE' : ofList E' = e')
    (hX : toList x = x1 :: X') :
    plus e x = if le x1 e1 then add e1 (plus e' x) else x := by
  obtain ⟨hce, hde⟩ := inT_toList e he
  rw [hE] at hce hde
  obtain ⟨⟨hap1, hi1⟩, hcE⟩ := inTL_cons.mp hce
  have htE : toList (ofList E') = E' := toList_ofList E' (fun z hz =>
    ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcE z hz)).1)
  have hix1 : inT x1 = true := inTL_inT hx x1 (by rw [hX]; exact List.Mem.head _)
  rw [plus_eq hX, hE, ← hE']
  by_cases hle : le x1 e1 = true
  · rw [if_pos hle, List.filter_cons_of_pos (by rw [hle]),
      plus_eq (s := ofList E') hX, htE]
    exact ofList_cons_ne_nil (append_toList_ne_nil hX)
  · rw [if_neg hle,
      filter_nil_of_head_inT hix1 e1 E' hi1 hcE hde (bool_false hle),
      List.nil_append]
    exact inT_ofList_toList x hx

theorem plus_mono_step {e e' e1 : Term} {E' : List Term} (he : inT e = true)
    (hE : toList e = e1 :: E') (hE' : ofList E' = e')
    (ih : ∀ x y, inT x = true → inT y = true → le x y = true →
        le (plus e' x) (plus e' y) = true) :
    ∀ (x y : Term), inT x = true → inT y = true → le x y = true →
      le (plus e x) (plus e y) = true := by
  intro x y hx hy h
  have hap1 : e1.isAP = true := inTL_isAP he e1 (by rw [hE]; exact List.Mem.head _)
  have hi1 : inT e1 = true := inTL_inT he e1 (by rw [hE]; exact List.Mem.head _)
  have hee : e = ofList (e1 :: E') := by rw [← hE, inT_ofList_toList e he]
  cases hX : toList x with
  | nil =>
    have hxz : x = zero := toList_eq_nil x hX
    subst hxz
    show le e (plus e y) = true
    cases hY : toList y with
    | nil =>
      have hyz : y = zero := toList_eq_nil y hY
      subst hyz
      exact Evidence.WF.le_self e
    | cons y1 Y' =>
      have hiy1 : inT y1 = true := inTL_inT hy y1 (by rw [hY]; exact List.Mem.head _)
      rw [plus_cons he hy hE hE' hY]
      by_cases hle : le y1 e1 = true
      · rw [if_pos hle]
        cases hEc : E' with
        | nil =>
          rw [hEc] at hee
          rw [show e = e1 from hee]
          exact le_of_lt (lt_head_add hap1 _)
        | cons f F =>
          rw [hEc] at hee hE'
          have hee2 : e = add e1 e' := by rw [hee, ← hE']; rfl
          rw [hee2]
          refine le_add_tail ?_
          exact ih zero y inT_zero hy (le_zero_left y)
      · rw [if_neg hle]
        refine le_of_lt (lt_of_hd_lt he hy hE hY ?_)
        exact lt_of_not_le_inT hiy1 hi1 (bool_false hle)
  | cons x1 X' =>
    have hix1 : inT x1 = true := inTL_inT hx x1 (by rw [hX]; exact List.Mem.head _)
    rw [plus_cons he hx hE hE' hX]
    cases hY : toList y with
    | nil =>
      exfalso
      have hyz : y = zero := toList_eq_nil y hY
      rw [hyz] at h
      have hz : x = zero := by
        rcases (Bool.or_eq_true _ _).mp h with hq | hl
        · exact eq_of_beq hq
        · rw [lt_zero_right] at hl; exact Bool.noConfusion hl
      rw [hz] at hX
      exact absurd (show x1 :: X' = ([] : List Term) from hX.symm) (List.cons_ne_nil x1 X')
    | cons y1 Y' =>
      have hiy1 : inT y1 = true := inTL_inT hy y1 (by rw [hY]; exact List.Mem.head _)
      rw [plus_cons he hy hE hE' hY]
      have hxy1 : le x1 y1 = true := hd_mono_inT hx hy hX hY h
      by_cases hlx : le x1 e1 = true
      · rw [if_pos hlx]
        by_cases hly : le y1 e1 = true
        · rw [if_pos hly]
          exact le_add_tail (ih x y hx hy h)
        · rw [if_neg hly]
          refine le_of_lt (lt_add_of_lt_hd hy hY ?_)
          exact lt_of_not_le_inT hiy1 hi1 (bool_false hly)
      · have hly : ¬ (le y1 e1 = true) := by
          intro hc
          exact hlx (le_trans_inT hix1 hiy1 hi1 hxy1 hc)
        rw [if_neg hlx, if_neg hly]
        exact h

/-- **`plus e ·` は単調。** 側条件なし。 -/
theorem plus_mono_right_inT : ∀ (e : Term), inT e = true → ∀ (x y : Term), inT x = true →
    inT y = true → le x y = true → le (plus e x) (plus e y) = true := by
  have hzero : ∀ (x y : Term), inT x = true → inT y = true → le x y = true →
      le (plus zero x) (plus zero y) = true := by
    intro x y hx hy h
    rw [plus_zero_left_inT hx, plus_zero_left_inT hy]
    exact h
  intro e
  induction e with
  | zero => intro _; exact hzero
  | M => intro he; exact plus_mono_step he rfl rfl hzero
  | omg _ _ => intro he; exact plus_mono_step he rfl rfl hzero
  | phi _ _ _ _ => intro he; exact plus_mono_step he rfl rfl hzero
  | psi _ _ _ _ => intro he; exact plus_mono_step he rfl rfl hzero
  | Z _ _ => intro he; exact plus_mono_step he rfl rfl hzero
  | add u v _ ihv =>
    intro he
    obtain ⟨_, _, hiv, _⟩ := inT_add he
    exact plus_mono_step he rfl (inT_ofList_toList v hiv) (ihv hiv)

/-- **SC の一段。** `w` が強臨界で `w ≤ p` (`p` は加法主要) なら `w ≤ logOm p`。
    これが (G1) の側条件が `w ∈ SC` でなければならない理由。`w = p = 1` で破れる。 -/
theorem lt_logOm_of_sc {w p : Term} (hsc : w.isSC = true) (hw : inT w = true)
    (hap : p.isAP = true) (hp : inT p = true) (h : lt p w = false) :
    lt (logOm p) w = false := by
  have hlew : le w p = true := le_of_not_lt3 (inT_le_fragR p hp) (inT_le_fragR w hw) h
  have hkey : le w (logOm p) = true := by
    cases p with
    | zero => exact Bool.noConfusion hap
    | add _ _ => exact Bool.noConfusion hap
    | M => exact hlew
    | omg _ => exact hlew
    | psi _ _ => exact hlew
    | Z _ => exact hlew
    | phi c d =>
      cases c with
      | zero =>
        refine le_logOm_phi_zero_of_le hw (inT_phi4 hp).2.1 ?_
        cases w with
        | zero => exact Bool.noConfusion hsc
        | omg _ => exact Bool.noConfusion hsc
        | phi _ _ => exact Bool.noConfusion hsc
        | add _ _ => exact Bool.noConfusion hsc
        | M =>
          exfalso
          rw [show le (M : Term) (phi zero d) = false from by
            show ((M == phi zero d) || lt M (phi zero d)) = false
            rw [show ((M : Term) == phi zero d) = false from rfl,
              show lt (M : Term) (phi zero d) = false from by
                rw [lt_eq_ltF_succ]; exact ltF_succ_M_phi _ _ _]
            rfl] at hlew
          exact Bool.noConfusion hlew
        | psi k a =>
          exact le_of_psi_lt_phi_zero
            (lt_of_le_of_ne hlew (by intro hc; exact Term.noConfusion hc))
        | Z e =>
          exact le_of_Z_lt_phi_zero
            (lt_of_le_of_ne hlew (by intro hc; exact Term.noConfusion hc))
      | M => exact hlew
      | omg _ => exact hlew
      | phi _ _ => exact hlew
      | psi _ _ => exact hlew
      | Z _ => exact hlew
      | add _ _ => exact hlew
  rcases (Bool.or_eq_true _ _).mp hkey with he | hl
  · rw [← eq_of_beq he, lt_irrefl]
  · exact lt_asymm_inT hw (inT_logOm hp) hl

end

/-! ### §65.5 (G1) を直した形と、(G2) そのもの

`DivDescSC` は §64 の `DivDescInT` に `w ∈ SC` を 1 つ足したもの。足さないと偽で、反例は
§65.7 に凍結してある。`MulDescInT` は §64 の定義そのままで、直しは要らない。 -/

section
open Trans.Recal (bplus)
open TM TM.Term
open Evidence.WF
open Trans.Dict (logOm subAP divAP mulL)

/-- **(G1) を直した形。** §64 の `DivDescInT` に `w.isSC` を足したもの。 -/
def DivDescSC : Prop := ∀ (w : Term) (l : List Term), inT w = true → w.isSC = true →
  inTL l = true → descL l = true → (∀ q ∈ l, lt q w = false) →
  descL (l.map (divAP w)) = true

/-- **(G1) は偽。** §64 の `DivDescInT` の反証 — `w = ω`, `l = [ω^ω, ω]`。 -/
theorem not_divDescInT : ¬ DivDescInT := by
  intro H
  have h := H omega [phi zero omega, omega] rfl rfl rfl
    (by intro q hq
        rcases List.mem_cons.mp hq with h1 | h1
        · rw [h1]; rfl
        · rw [List.mem_singleton.mp h1]; rfl)
  exact Bool.noConfusion (h.symm.trans
    (show descL ([phi zero omega, omega].map (divAP omega)) = false from rfl))

/-- **(G1) 完了。** `logOm` の単調性 → SC の一段 → `subAP` の単調性 → `ω^·` の単調性。 -/
theorem divDescSC : DivDescSC := by
  intro w l hw hsc hcl hdl hge
  refine descL_map_mono (divAP w)
    (fun p => p.isAP = true ∧ inT p = true ∧ lt p w = false) ?_ l ?_ hdl
  · intro a b ha hb hba
    obtain ⟨hapa, hia, _⟩ := ha
    obtain ⟨hapb, hib, hwb⟩ := hb
    show le (omegaNF (subAP w (logOm b))) (omegaNF (subAP w (logOm a))) = true
    refine omegaNF_mono_inT (inT_subAP (inT_logOm hib)) (inT_subAP (inT_logOm hia)) ?_
    refine subAP_mono_inT (inT_logOm hib) (inT_logOm hia)
      (lt_logOm_of_sc hsc hw hapb hib hwb) ?_
    exact logOm_mono_inT hapb hapa hib hia hba
  · intro x hx
    exact ⟨((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcl x hx)).1,
           ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcl x hx)).2, hge x hx⟩

/-- **(G2) 完了。** §64 の `MulDescInT` そのまま — 側条件は要らない。 -/
theorem mulDescInT : MulDescInT := by
  intro e y he hy
  obtain ⟨hc, hd⟩ := inT_toList y hy
  refine descL_map_mono (fun p => omegaNF (plus e (logOm p)))
    (fun p => p.isAP = true ∧ inT p = true) ?_ (toList y) ?_ hd
  · intro a b ha hb hba
    obtain ⟨hapa, hia⟩ := ha
    obtain ⟨hapb, hib⟩ := hb
    refine omegaNF_mono_inT (inT_plus he (inT_logOm hib)) (inT_plus he (inT_logOm hia)) ?_
    exact plus_mono_right_inT e he _ _ (inT_logOm hib) (inT_logOm hia)
      (logOm_mono_inT hapb hapa hib hia hba)
  · intro x hx
    exact ⟨inTL_isAP hy x hx, inTL_inT hy x hx⟩

end

/-! ### §65.6 消費者 — `wcnf`・`collapse`・`dict` を直した仮説の上で

§64.4 の `wcnf_spec` と §64.5 の `inT_collapse` / `inT_dict` / `collapseInT_of_gaps` は
**偽である `DivDescInT` を仮説に取っている**ので、そのままでは使えない。ここでは同じ証明を
`DivDescSC` に対して引き直す。呼び出し側の底はいつも `reg (u+1) = Z u` で、`isSC` は `rfl`。

§64.3 の `inT_mulL` / `ltM_mulL` と §64.5 の `inT_idxOf` / `stepF_inv` / `fold_inv` は
`MulDescInT` しか取らないので、そのまま `mulDescInT` を渡して再利用する。 -/

section
open Trans.Recal (bplus)
open TM TM.Term
open Evidence.WF
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse dict)
open Trans.Dict (BT)

theorem isSC_reg_succ (u : Nat) : (reg (u + 1)).isSC = true := rfl

theorem inT_wA_sc {w p : Term} (hw : inT w = true) (hsc : w.isSC = true)
    (hp : inT p = true) : inT (wA w p) = true := by
  obtain ⟨hc, hd⟩ := inT_toList _ (inT_logOm hp)
  refine inT_ofList _ ?_
    (divDescSC w _ hw hsc (inTL_filter _ hc) (descL_filter_inT _ hc hd _) ?_)
  · show (List.map (divAP w) _).all _ = true
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨q, hq, hxe⟩ := List.mem_map.mp hx
    rw [← hxe]
    show ((divAP w q).isAP && inT (divAP w q)) = true
    rw [isAP_divAP, inT_divAP (inTL_inT (inT_logOm hp) q (List.mem_filter.mp hq).1)]
    rfl
  · intro q hq
    have hq2 := (List.mem_filter.mp hq).2
    cases hlq : lt q w with
    | false => rfl
    | true => rw [hlq] at hq2; exact Bool.noConfusion hq2

/-- **`wcnf` は 𝔗(M) の中に留まる** — 底が強臨界なら。§64.4 の `wcnf_spec` の直した版。 -/
theorem wcnf_spec_sc {w : Term} (hw : inT w = true) (hsc : w.isSC = true) :
    ∀ (L : List Term), inTL L = true → descL L = true → (∀ x ∈ L, lt x M = true) →
      PairOK (wcnf w L) := by
  intro L
  induction L with
  | nil =>
    intro _ _ _
    exact ⟨⟨inT_zero, lt_zero_M⟩, by intro ac hac; cases hac⟩
  | cons p rest ih =>
    intro hc hd hm
    obtain ⟨⟨hap, hip⟩, hcr⟩ := inTL_cons.mp hc
    have hdr := descL_tail hd
    have hmr : ∀ x ∈ rest, lt x M = true := fun x hx => hm x (List.Mem.tail p hx)
    have hlpM : lt p M = true := hm p (List.Mem.head _)
    have IH := ih hcr hdr hmr
    by_cases hlp : lt p w = true
    · rw [wcnf_cons_lt hlp]
      exact ⟨⟨inT_ofList _ hc hd, lt_ofList_M _ hm⟩, by intro ac hac; cases hac⟩
    · have hlp' : lt p w = false := bool_false hlp
      have hA := inT_wA_sc (w := w) hw hsc hip
      have hAM := ltM_wA (w := w) hip hlpM
      have hC := inT_wC (w := w) hip
      have hCM := ltM_wC (w := w) hip hlpM
      rw [wcnf_cons_ge hlp']
      cases hr : wcnf w rest with
      | mk fst snd =>
        rw [hr] at IH
        obtain ⟨⟨hs1, hs2⟩, hall⟩ := IH
        cases fst with
        | nil =>
          refine ⟨⟨hs1, hs2⟩, ?_⟩
          intro ac hac
          rw [List.mem_singleton.mp hac]
          exact ⟨hA, hAM, hC, hCM⟩
        | cons ac0 ps =>
          cases ac0 with
          | mk a' c' =>
            have hac0 := hall (a', c') (List.Mem.head _)
            show PairOK (if (wA w p == a') = true
              then ((wA w p, plus (wC w p) c') :: ps, snd)
              else ((wA w p, wC w p) :: (a', c') :: ps, snd))
            by_cases heq : (wA w p == a') = true
            · rw [if_pos heq]
              refine ⟨⟨hs1, hs2⟩, ?_⟩
              intro ac hac
              rcases List.mem_cons.mp hac with hq | hq
              · rw [hq]
                exact ⟨hA, hAM, inT_plus hC hac0.2.2.1,
                  lt_plus_M hC hac0.2.2.1 hCM hac0.2.2.2⟩
              · exact hall ac (List.Mem.tail _ hq)
            · rw [if_neg heq]
              refine ⟨⟨hs1, hs2⟩, ?_⟩
              intro ac hac
              rcases List.mem_cons.mp hac with hq | hq
              · rw [hq]; exact ⟨hA, hAM, hC, hCM⟩
              · exact hall ac hq

/-- **`collapse` は 𝔗(M) に落ちる** — (G3) だけを仮定して。§64.5 の `inT_collapse` から
    (G1)(G2) の仮説が消えた形。 -/
theorem inT_collapse_gap3 (u : Nat) (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (Hp : PsiIdxOK u x) :
    inT (collapse u x) = true ∧ lt (collapse u x) M = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨⟨h21, h22⟩, hallOK⟩ :=
    wcnf_spec_sc (inT_reg (u+1)) (isSC_reg_succ u) (toList x) hc hd (ltM_toList x hx hlx)
  have hinit : StInv ((none : Option Term), (none : Option Term)) := by
    constructor
    · intro i0 hq; cases hq
    · intro v hq; cases hq
  have hst := fold_inv mulDescInT (inT_reg (u+1)) (ltM_reg (u+1)) (inT_baseOf u) (ltM_baseOf u)
    (wcnf (reg (u+1)) (toList x)).1 (none, none) hinit hallOK Hp
  have hv : inT (((wcnf (reg (u+1)) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg (u+1)) (baseOf u))).2.getD zero) = true ∧
      lt (((wcnf (reg (u+1)) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg (u+1)) (baseOf u))).2.getD zero) M = true := by
    cases hg : ((wcnf (reg (u+1)) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg (u+1)) (baseOf u))).2 with
    | none => exact ⟨inT_zero, lt_zero_M⟩
    | some v => exact hst.2 v hg
  rw [collapse_eq]
  have harg : inT (plus (reg u) (plus _ (wcnf (reg (u+1)) (toList x)).2)) = true :=
    inT_plus (inT_reg u) (inT_plus hv.1 h21)
  have hlarg : lt (plus (reg u) (plus _ (wcnf (reg (u+1)) (toList x)).2)) M = true :=
    lt_plus_M (inT_reg u) (inT_plus hv.1 h21) (ltM_reg u)
      (lt_plus_M hv.1 h21 hv.2 h22)
  exact ⟨inT_omegaNF harg, ltM_omegaNF harg hlarg⟩

/-- 強臨界枝が一度も点火しない断片では、もう仮説はひとつも要らない。 -/
theorem inT_collapse_noSC_gap3 (u : Nat) (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (h : ∀ ac ∈ (wcnf (reg (u+1)) (toList x)).1, le (reg (u+1)) ac.1 = false) :
    inT (collapse u x) = true :=
  (inT_collapse_gap3 u x hx hlx (psiIdxOK_of_noSC u x h)).1

/-- `dict` の像は 𝔗(M) の中で `M` の下 — (G3) だけを仮定して。 -/
theorem inT_dict_gap3 (Hp : ∀ (u : Nat) (a : BT), PsiIdxOK u (dict a)) :
    ∀ a : BT, inT (dict a) = true ∧ lt (dict a) M = true
  | .zero => ⟨inT_zero, lt_zero_M⟩
  | .D u a => by
    have ih := inT_dict_gap3 Hp a
    exact inT_collapse_gap3 u (dict a) ih.1 ih.2 (Hp u a)
  | .sum a b => by
    have iha := inT_dict_gap3 Hp a
    have ihb := inT_dict_gap3 Hp b
    exact ⟨inT_plus iha.1 ihb.1, lt_plus_M iha.1 ihb.1 iha.2 ihb.2⟩

/-- **§65 の主定理。** §63 の `CollapseInT` は (G3) だけに還元される。 -/
theorem collapseInT_of_gap3 (Hp : ∀ (u : Nat) (a : BT), PsiIdxOK u (dict a)) : CollapseInT :=
  fun u a => (inT_dict_gap3 Hp (BT.D u a)).1

/-- **消費者を通す。** §63 の `hsuccS_supply` — `certIn_region` の 2 番目の供給 — が
    (G3) だけで開く。 -/
theorem hsuccS_supply_of_gap3 (Hp : ∀ (u : Nat) (a : BT), PsiIdxOK u (dict a)) :
    ∀ (S : BMS.Matrix) (v : TM.Term), RegS S → ValS S v → BMS.kind S = BMS.Kind.succ →
    ∃ u, v = plus u TM.Term.one ∧ inT v = true ∧ inT u = true ∧ lt u v = true
         ∧ ∀ n, ValS (BMS.expand S n) u :=
  hsuccS_supply (collapseInT_of_gap3 Hp)

end

/-! ### §65.7 測定 (凍結)

否定的なものから。母集団は `ofNat` を種に入れてある — §64 の 2 つの母集団がどちらも
`ω^n` を作れず、しかも肯定側の掃引が `l` を「母集団の項 `y` の `toList`」に限っていたので、
(G1) の反例が 82373 + 2324 組すべてをすり抜けていた。 -/

section
open TM TM.Term
open Evidence.WF
open Trans.Recal
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse dict)
open Trans.Dict (BT)

/-! **否定 1 — (G1) `DivDescInT` は偽。** `w = ω`, `l = [ω^ω, ω]`、次数和 17。 -/

#guard inT omega && inT (phi zero omega)
#guard omega.isAP && (phi zero omega).isAP
#guard descL [phi zero omega, omega]
#guard !(lt (phi zero omega) omega) && !(lt omega omega)
#guard !(descL ([phi zero omega, omega].map (divAP omega)))
#guard ([phi zero omega, omega].map (divAP omega)) == [one, omega]
#guard omega.deg + (phi zero omega).deg + omega.deg == 17
--   `w = ω` は SC ではない。これが唯一の逃げ道である。
#guard !(omega.isSC)
--   `l` は正真正銘 𝔗(M) の項の成分列 — 命題の一般性の artefact ではない。
#guard inT (add (phi zero omega) omega)
#guard TM.Term.toList (add (phi zero omega) omega) == [phi zero omega, omega]
--   §64 の判定器でも同じ。
#guard !(divDescb omega [phi zero omega, omega])
--   壊れているのは `w ≤ p` から `w ≤ logOm p` への一段。
#guard !(lt omega omega) && lt (logOm omega) omega
#guard logOm omega == one

/-! **否定 2 — `logOm` の単調性は加法主要を落とすと偽。** 最小は `Ω ⊕ Ω ≤ ω^Ω`、次数和 9。 -/

#guard le (add (Z zero) (Z zero)) (phi zero (Z zero))
#guard !(le (logOm (add (Z zero) (Z zero))) (logOm (phi zero (Z zero))))
#guard (add (Z zero) (Z zero)).deg + (phi zero (Z zero)).deg == 9
#guard !((add (Z zero) (Z zero)).isAP)

/-! **否定 3 — `subAP` の単調性は `w ≤ x` を落とすと偽。** 最小は `w = M`, `x = Ω`, `y = M`。 -/

#guard le (Z zero) (M : Term)
#guard !(le (subAP M (Z zero)) (subAP M M))
#guard (M : Term).deg + (Z zero).deg + (M : Term).deg == 4
#guard lt (Z zero) M          -- `w ≤ x` が破れている

/-! **否定 4 — SC の一段は SC を落とすと偽。** `w = p = 1`。 -/

#guard !(lt one one) && lt (logOm one) one
#guard !((one : Term).isSC)

/-! **否定 5 — `z < ω^z` は `z < M` を要る。** `z = M` で偽。 -/

#guard !(lt M (phi zero M))
#guard !(lt (M : Term) M)

/-! 肯定。母集団は `ofNat` 入りの閉包を 2 段。 -/

private def b65 : List Term :=
  [zero, one, ofNat 2, ofNat 3, omega, Z zero, M, psi (Z zero) zero, phi one zero]
private def stp65 (l : List Term) : List Term :=
  l ++ (l.flatMap fun a => l.map fun b => add a b)
    ++ (l.flatMap fun a => l.map fun b => phi a b)
    ++ (l.map fun a => omegaNF a)
    ++ (l.map fun a => Z a)
    ++ (l.map fun a => omg a)
private def raw65 : List Term := (stp65 b65).eraseDups
private def C65 : List Term := raw65.filter fun x => inT x
private def C65ap : List Term := C65.filter fun x => x.isAP
private def D65 : List Term := ((stp65 (C65.take 22)).eraseDups.filter fun x => inT x).take 120
private def D65ap : List Term := D65.filter fun x => x.isAP

#guard raw65.length == 183
#guard C65.length == 109
#guard C65ap.length == 75
#guard D65.length == 120
#guard D65ap.length == 45
#guard (D65.map fun x => x.deg).foldl (fun a b => if a < b then b else a) 0 == 23

/-! 肯定 1. `ω^·` の 3 分岐 (`omegaNF_eq_gen`) — `inT` でない項も含めて 0 失敗。 -/

private def omEq65 (x : Term) : Bool :=
  omegaNF x ==
    (if lt M x then omg x else if TM.Term.isFP zero x then x else phi zero (dnArg x))
#guard (raw65.filter fun x => !(omEq65 x)).length == 0
#guard (D65.filter fun x => !(omEq65 x)).length == 0

/-! 肯定 2. `logOm` の単調性 — 加法主要に限れば 0 失敗、落とすと 33 失敗。 -/

#guard (C65ap.flatMap fun x => C65ap.filter fun y =>
    le x y && !(le (logOm x) (logOm y))).length == 0
#guard (D65ap.flatMap fun x => D65ap.filter fun y =>
    le x y && !(le (logOm x) (logOm y))).length == 0
#guard (C65.flatMap fun x => C65.filter fun y =>
    le x y && !(le (logOm x) (logOm y))).length == 33

/-! 肯定 3. `ω^·` の単調性 (非狭義) — 0 失敗。 -/

#guard (C65.flatMap fun x => C65.filter fun y =>
    le x y && !(le (omegaNF x) (omegaNF y))).length == 0
#guard (D65.flatMap fun x => D65.filter fun y =>
    le x y && !(le (omegaNF x) (omegaNF y))).length == 0

/-! 肯定 4. D1 と D2 — 0 失敗。D3 は使っていないので測っていない。 -/

#guard (C65.filter fun x => !(le (dnArg x) x)).length == 0
#guard (C65.flatMap fun x => C65.filter fun y => lt x y && !(le x (dnArg y))).length == 0
#guard (D65.filter fun x => !(le (dnArg x) x)).length == 0
#guard (D65.flatMap fun x => D65.filter fun y => lt x y && !(le x (dnArg y))).length == 0

/-! 肯定 5. `plus e ·` の単調性 — 側条件なしで 0 失敗 (109³ 組)。 -/

#guard (C65.flatMap fun e => C65.flatMap fun x => C65.filter fun y =>
    le x y && !(le (plus e x) (plus e y))).length == 0

/-! 肯定 6. `subAP w` の単調性 — `w ≤ x` があれば 0 失敗、無いと 2073 失敗。
    **`w ∈ SC` は `subAP` には要らない** (証明も使っていない)。 -/

#guard (C65.flatMap fun w => C65.flatMap fun x => C65.filter fun y =>
    !(lt x w) && le x y && !(le (subAP w x) (subAP w y))).length == 0
#guard (D65.flatMap fun w => D65.flatMap fun x => D65.filter fun y =>
    !(lt x w) && !(lt y w) && le x y && !(le (subAP w x) (subAP w y))).length == 0
#guard (C65.flatMap fun w => C65.flatMap fun x => C65.filter fun y =>
    w.isSC && le x y && !(le (subAP w x) (subAP w y))).length == 2073

/-! 肯定 7. SC の一段 — `w ∈ SC` なら 0 失敗、落とすと 46 失敗。 -/

#guard (C65.flatMap fun w => C65ap.filter fun p =>
    w.isSC && !(lt p w) && (lt (logOm p) w)).length == 0
#guard (D65.flatMap fun w => D65ap.filter fun p =>
    w.isSC && !(lt p w) && (lt (logOm p) w)).length == 0
#guard (C65.flatMap fun w => C65ap.filter fun p =>
    !(lt p w) && (lt (logOm p) w)).length == 46

/-! 肯定 8. (G1) を直した形 — 0 失敗。C65 で 1270 組、D65 で 403 組。 -/

#guard (C65.flatMap fun w => C65ap.flatMap fun p => C65ap.filter fun p' =>
    w.isSC && le p' p && !(lt p w) && !(lt p' w)
      && !(descL [divAP w p, divAP w p'])).length == 0
#guard (C65.flatMap fun w => C65ap.flatMap fun p => C65ap.filter fun p' =>
    w.isSC && le p' p && !(lt p w) && !(lt p' w)).length == 1270
#guard (D65.flatMap fun w => D65ap.flatMap fun p => D65ap.filter fun p' =>
    w.isSC && le p' p && !(lt p w) && !(lt p' w)
      && !(descL [divAP w p, divAP w p'])).length == 0
#guard (D65.flatMap fun w => D65ap.flatMap fun p => D65ap.filter fun p' =>
    w.isSC && le p' p && !(lt p w) && !(lt p' w)).length == 403

/-! 肯定 9. (G2) — 0 失敗。 -/

#guard (C65.flatMap fun e => C65.filter fun y => !(mulDescb e y)).length == 0
#guard (D65.flatMap fun e => D65.filter fun y => !(mulDescb e y)).length == 0

/-! 肯定 10. 領域そのもの。§64.6 肯定 6 を、(G1)(G2) が定理になった今の形で取り直す。 -/

#guard ((popNFB 3 6).flatMap fun t => (bVal t).toL).eraseDups.length == 443
#guard ((popNFB 3 6).flatMap fun t => (bVal t).toL).eraseDups.all fun a =>
  TM.Term.inT (Trans.Dict.dict a)


end

/-! ### §65.8 公理 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

end

/-! ## §66 (G3) IS FALSE — AND SO IS `CollapseInT`.  THE REPAIR IS `BT.isStd`

§65 left `certIn_region`'s second supply waiting on exactly one hypothesis,

    Hp : ∀ (u : Nat) (a : BT), PsiIdxOK u (dict a)

i.e. [Rathjen, 1991] 2.1(vi) for the indices `collapse`'s strongly critical branch actually
emits.  §66 took 2.1(vi) apart, proved the traceback §64 asked for — and then found the
hypothesis FALSE.

WHAT IS PROVED, UNCONDITIONALLY.

  §66.1  **`PsiIdxOK u x` IS EXACTLY ITS `K`-set conjunct.**  2.1(vi) is a conjunction of five
         clauses — `κ ∈ R`, `κ ∈ 𝔗(M)`, `α ∈ 𝔗(M)`, `α < M`, `K_κ α < α` — and for the emitted
         indices the first four are theorems: `(Z ·).isR` and `inT (reg (u+1))` are immediate,
         and `inT` / `lt · M` of the index come from §64.5's `inT_idxOf` once the fold's state
         invariant `StInv` is available at the visited state.  Making `StInv` available is the
         one non-trivial step, because §64.5's `fold_inv` DEMANDS the `ψ` facts it is supposed
         to deliver: `scanSt_stInv` breaks the circle by running the two inductions
         simultaneously along `scanSt`.  The result is `psiIdxOK_iff_ksetIdxOK`: for
         `x ∈ 𝔗(M)` below `M`, `PsiIdxOK u x ↔ KsetIdxOK u x`.

  §66.2  **THE TRACEBACK.**  §64 named the missing structural fact as "`Kset w i` traces back
         through `mulL` / `plus` / `omegaNF` to `Kset w` of the `wcnf` components of `x`".
         It is proved here in full, with no hypothesis — and SHARPER than asked, because
         `wcnf` stops at the first component below `w`:

             y ∈ Kset (reg (u+1)) i  →  y ∈ KsetL (reg (u+1)) (bigPart (reg (u+1)) (toList x))

         (`Kset_scanSt_big`), whence `y ∈ Kset (reg (u+1)) x` (`Kset_scanSt_sub`).  One
         membership lemma per operator carries it — `ofList`, `plus`, `ofNat`, `reg`,
         `omegaNF`, `phiNF`, `phiNFsucc`, `phiNFdefault`, `splitFin`, `logOm`, `subAP`, `sub1`,
         `divAP`, `mulL`, `wA`, `wC`, `wcnf`, `idxOf`, `scanSt` — and the `reg` one is what
         makes `mulL w ·` lose its `w`: `Kset κ Ω_{u+1}` is empty because `Ω_{u+1} = Z n` and
         `Kset κ (Z β) = Kset κ β = Kset κ n = ∅`.  `KsetBigOK` is the sufficient condition the
         traceback buys, and `psiIdxOK_of_bigOK` is the reduction.

  §66.3  **(G3) IS FALSE, AND `not_psiIdxOK_dict` PROVES IT.**  Smallest counterexample,
         `BT`-size 4:

             u = 0,   a = ψ₁(ψ₃0)   (`BT.D 1 (BT.D 3 BT.zero)`)

         `dict a = ψ_{Ω₂}(Ω₃)`, which is a genuine term of 𝔗(M).  At `u = 0` the base is
         `w = Ω₁`, `wcnf` returns the single pair `(ψ_{Ω₂}(Ω₃), 1)`, the strongly critical
         branch fires, and the emitted index is `ψ_{Ω₂}(Ω₃)` itself — but
         `K_{Ω₁} ψ_{Ω₂}(Ω₃) = {Ω₃}` and `Ω₃ ≮ ψ_{Ω₂}(Ω₃)`, so `ψ_{Ω₁}` of it is not a term.
         **Hence `CollapseInT` (§63) is FALSE too** (`not_collapseInT`):
         `inT (dict (ψ₀(ψ₁(ψ₃0)))) = false`, and over ALL 3966 `BT` terms of the 3-fold
         closure of `{0}` under `ψ_u` (`u < 4`) and `⊕`, that is the ONLY failure.

         WHY §64's 1805-TERM SWEEP MISSED IT.  `bcorp64` uses subscripts 0,1,2 only, and the
         pattern needs an inner subscript ≥ u+2 ABOVE the middle one: at the middle level
         `u' = 1` the base is `Ω₂`, and `dict (ψ₂0) = Ω₂` divides out exactly (`a = 1`, Veblen
         branch, nothing emitted), while `dict (ψ₃0) = Ω₃` does not (`a = Ω₃ ≥ Ω₂`, strongly
         critical branch, index `Ω₃`).  So `ψ₀(ψ₁(ψ₂0))` is fine and `ψ₀(ψ₁(ψ₃0))` is not:
         the corpus was one subscript short.

  §66.4  **THE REPAIR IS `BT.isStd`, AND IT IS MEASURED, NOT PROVED.**  `PsiIdxOKStd` and
         `CollapseInTStd` add exactly Buchholz's standardness of the collapsed term, and
         `collapseInTStd_of_psiIdxOKStd` proves the second from the first — the induction
         goes through because every `BT`-subterm of a standard term is standard.
         `PsiIdxOKStd` itself is NOT proved: 0 failures over `bcorp` (1805) and a second,
         subscript-3 corpus `ccorp` (1761), at `u = 0,1,2,3`.

WHAT IS NOT CLAIMED, AND WHAT THE REFUTATION COSTS.  §65's `collapseInT_of_gap3` and
`hsuccS_supply_of_gap3` carry `∀ u a, PsiIdxOK u (dict a)`, which §66.3 refutes, so **they are
now known to be VACUOUS and must not be used**, exactly as §65 said of §64's `DivDescInT`
consumers.  `Hsucc` is therefore NOT closed and is further from closed than §65 believed.
Nor does `BT.isStd` immediately rescue the region: of the 443 `bVal` components the region
actually produces, 280 are NOT `BT.isStd`, though all 443 do satisfy `PsiIdxOK` at
`u = 0,1,2,3` (measured).  So a §67 has two jobs: prove `PsiIdxOKStd`, and find the weaker
condition the region's own terms satisfy.
-/


/-! ### §66.1 2.1(vi) の 5 つの連言のうち 4 つは定理

`inT (ψκα)` は `κ ∈ R`・`inT κ`・`inT α`・`α < M`・`K_κ α < α` の連言。強臨界枝が吐く指数に
ついて、前の 4 つはここで落ちる。難所は「畳み込みの状態が `StInv` を満たす」ことで、§64.5 の
`fold_inv` はそれを出すのに `ψ` の事実を要求する — 循環している。`scanSt_stInv` は
`scanSt` に沿って 2 つの帰納法を同時に回してこの循環を切る。 -/

section
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **2.1(vi) の最後の連言だけ。** `PsiIdxOK` から易しい 4 つを落としたもの。 -/
def KsetIdxOK (u : Nat) (x : Term) : Prop :=
  ∀ p ∈ scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1,
    le (reg (u+1)) p.2.1 = true →
    (Kset (reg (u+1)) (idxOf (reg (u+1)) p.1 p.2)).all
      (fun y => lt y (idxOf (reg (u+1)) p.1 p.2)) = true

/-- `Ω_{u+1} = Z u` は正則 ([Rathjen, 1991] 2.1(vii))。 -/
theorem isR_reg_succ (u : Nat) : (reg (u+1)).isR = true := rfl

/-- `inT (ψκα)` の 5 連言をそのまま書き下したもの。 -/
theorem inT_psi_eq (k a : Term) :
    inT (psi k a) =
      (k.isR && inT k && inT a && lt a M && (Kset k a).all (fun x => lt x a)) := rfl

/-- `inT (ψκα)` から最後の連言を取り出す。 -/
theorem ksetAll_of_inT_psi {k a : Term} (h : inT (psi k a) = true) :
    (Kset k a).all (fun x => lt x a) = true := by
  rw [inT_psi_eq, Bool.and_eq_true] at h
  exact h.2

/-- **易しい 4 つ。** `K` の条件さえあれば、吐かれた指数の `ψ` は 𝔗(M) の項。 -/
theorem inT_psi_idx {w : Term} (hR : w.isR = true) (hw : inT w = true) (hlw : lt w M = true)
    {s : Option Term × Option Term} {ac : Term × Term} (hs : StInv s)
    (h1 : inT ac.1 = true) (h2 : lt ac.1 M = true) (h3 : inT ac.2 = true)
    (h4 : lt ac.2 M = true)
    (hk : (Kset w (idxOf w s ac)).all (fun y => lt y (idxOf w s ac)) = true) :
    inT (psi w (idxOf w s ac)) = true := by
  obtain ⟨hi, hli⟩ := inT_idxOf mulDescInT hw hlw hs h1 h2 h3 h4
  rw [inT_psi_eq, hR, hw, hi, hli, hk]
  rfl

/-- **循環を切る。** `scanSt` に沿って「状態は `StInv`」と「吐かれる `ψ` は 𝔗(M) の項」を
    同時に回す。§64.5 の `fold_inv` は後者を仮説に取るので、これがないと使えない。 -/
theorem scanSt_stInv {w base : Term} (hR : w.isR = true) (hw : inT w = true)
    (hlw : lt w M = true) (hb : inT base = true) (hlb : lt base M = true) :
    ∀ (l : List (Term × Term)) (s : Option Term × Option Term), StInv s →
      (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
      (∀ p ∈ scanSt w base s l, le w p.2.1 = true →
        (Kset w (idxOf w p.1 p.2)).all (fun y => lt y (idxOf w p.1 p.2)) = true) →
      ∀ p ∈ scanSt w base s l,
        StInv p.1 ∧ (le w p.2.1 = true → inT (psi w (idxOf w p.1 p.2)) = true) := by
  intro l
  induction l with
  | nil => intro s _ _ _ p hp; cases hp
  | cons ac t ih =>
    intro s hs hall hk p hp
    have hhead : StInv s ∧ (le w ac.1 = true → inT (psi w (idxOf w s ac)) = true) := by
      refine ⟨hs, ?_⟩
      intro hle
      obtain ⟨g1, g2, g3, g4⟩ := hall ac (List.Mem.head _)
      exact inT_psi_idx hR hw hlw hs g1 g2 g3 g4 (hk (s, ac) (List.Mem.head _) hle)
    rcases List.mem_cons.mp (show p ∈ (s, ac) :: scanSt w base (stepF w base s ac) t from hp)
      with h | h
    · rw [h]; exact hhead
    · have hs' : StInv (stepF w base s ac) :=
        stepF_inv mulDescInT hw hlw hb hlb hs (hall ac (List.Mem.head _)) hhead.2
      exact ih (stepF w base s ac) hs' (fun a ha => hall a (List.Mem.tail _ ha))
        (fun q hq => hk q (List.Mem.tail _ hq)) p h

theorem stInv_none : StInv ((none : Option Term), (none : Option Term)) := by
  constructor
  · intro i0 h; cases h
  · intro v h; cases h

/-- **§66.1 の主定理 (→)。** `K` の条件だけで (G3) が出る。 -/
theorem psiIdxOK_of_ksetIdxOK (u : Nat) (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (Hk : KsetIdxOK u x) : PsiIdxOK u x := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨_, hallOK⟩ :=
    wcnf_spec_sc (inT_reg (u+1)) (isSC_reg_succ u) (toList x) hc hd (ltM_toList x hx hlx)
  intro p hp hle
  exact (scanSt_stInv (isR_reg_succ u) (inT_reg (u+1)) (ltM_reg (u+1)) (inT_baseOf u)
    (ltM_baseOf u) (wcnf (reg (u+1)) (toList x)).1 (none, none) stInv_none hallOK Hk p hp).2 hle

/-- **§66.1 の主定理 (←)。** 逆は仮説なしで出る。 -/
theorem ksetIdxOK_of_psiIdxOK (u : Nat) (x : Term) (Hp : PsiIdxOK u x) : KsetIdxOK u x :=
  fun p hp hle => ksetAll_of_inT_psi (Hp p hp hle)

/-- **(G3) はちょうど 2.1(vi) の `K` の連言。** 残り 4 つは定理。 -/
theorem psiIdxOK_iff_ksetIdxOK (u : Nat) (x : Term) (hx : inT x = true) (hlx : lt x M = true) :
    PsiIdxOK u x ↔ KsetIdxOK u x :=
  ⟨ksetIdxOK_of_psiIdxOK u x, psiIdxOK_of_ksetIdxOK u x hx hlx⟩

end

/-! ### §66.2 追跡 — 吐かれた指数の `K` は `x` の「大きい成分」の `K` に戻る

演算ごとに 1 本ずつ。`ω^·`・`φ`・`plus`・`ofList`・`mulL`・`subAP`・`sub1`・`divAP`・`logOm`・
`wA`・`wC`・`wcnf`・`idxOf`・`scanSt`。`mulL w ·` が `w` を落とすのは `Kset κ Ω_{u+1} = ∅`
だから ([Rathjen, 1991] 2.2(vii) と 2.2(iv))。`wcnf` は `w` 未満の成分で止まるので、追跡先は
`toList x` 全体ではなく先頭の「大きい」部分 `bigPart` でよい。 -/

section
open Trans.Recal (bplus)
open Evidence.Region
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg)
open TM TM.Term
open Evidence.WF

def KsetL (k : Term) : List Term → List Term
  | [] => []
  | a :: t => Kset k a ++ KsetL k t

theorem mem_KsetL_iff (k y : Term) : ∀ (l : List Term),
    (y ∈ KsetL k l) ↔ (∃ a, a ∈ l ∧ y ∈ Kset k a) := by
  intro l
  induction l with
  | nil =>
    constructor
    · intro h; cases h
    · intro h; obtain ⟨a, ha, _⟩ := h; cases ha
  | cons b t ih =>
    constructor
    · intro h
      rcases List.mem_append.mp (show y ∈ Kset k b ++ KsetL k t from h) with h1 | h1
      · exact ⟨b, List.Mem.head _, h1⟩
      · obtain ⟨a, ha, hy⟩ := ih.mp h1
        exact ⟨a, List.Mem.tail _ ha, hy⟩
    · intro h
      obtain ⟨a, ha, hy⟩ := h
      rcases List.mem_cons.mp ha with h1 | h1
      · exact List.mem_append.mpr (Or.inl (by rw [← h1]; exact hy))
      · exact List.mem_append.mpr (Or.inr (ih.mpr ⟨a, h1, hy⟩))

theorem mem_KsetL_of_sub {k y : Term} {l1 l2 : List Term}
    (hs : ∀ a, a ∈ l1 → a ∈ l2) (h : y ∈ KsetL k l1) : y ∈ KsetL k l2 := by
  obtain ⟨a, ha, hy⟩ := (mem_KsetL_iff k y l1).mp h
  exact (mem_KsetL_iff k y l2).mpr ⟨a, hs a ha, hy⟩

theorem KsetL_append (k : Term) : ∀ (l1 l2 : List Term),
    KsetL k (l1 ++ l2) = KsetL k l1 ++ KsetL k l2 := by
  intro l1
  induction l1 with
  | nil => intro l2; rfl
  | cons a t ih =>
    intro l2
    show Kset k a ++ KsetL k (t ++ l2) = (Kset k a ++ KsetL k t) ++ KsetL k l2
    rw [ih l2, List.append_assoc]

theorem mem_KsetL_append {k y : Term} {l1 l2 : List Term} (h : y ∈ KsetL k (l1 ++ l2)) :
    y ∈ KsetL k l1 ∨ y ∈ KsetL k l2 := by
  rw [KsetL_append] at h
  exact List.mem_append.mp h

theorem Kset_eq_KsetL (k : Term) : ∀ t : Term, Kset k t = KsetL k (toList t)
  | zero => rfl
  | M => rfl
  | add a b => by
    show Kset k a ++ Kset k b = Kset k a ++ KsetL k (toList b)
    rw [Kset_eq_KsetL k b]
  | omg a => (List.append_nil _).symm
  | phi a b => (List.append_nil _).symm
  | psi p b => (List.append_nil _).symm
  | Z b => (List.append_nil _).symm

theorem Kset_ofList (k : Term) : ∀ l : List Term, Kset k (ofList l) = KsetL k l
  | [] => rfl
  | [a] => (List.append_nil _).symm
  | a :: b :: t => by
    show Kset k a ++ Kset k (ofList (b :: t)) = Kset k a ++ KsetL k (b :: t)
    rw [Kset_ofList k (b :: t)]


theorem plus_nil {s t : Term} (h : toList t = []) : plus s t = s := by
  show (match toList t with
        | [] => s
        | b1 :: _ => ofList ((toList s).filter (fun a => le b1 a) ++ toList t)) = s
  rw [h]

theorem plus_cons66 {s t b1 : Term} {r : List Term} (h : toList t = b1 :: r) :
    plus s t = ofList ((toList s).filter (fun a => le b1 a) ++ (b1 :: r)) := by
  show (match toList t with
        | [] => s
        | b1 :: _ => ofList ((toList s).filter (fun a => le b1 a) ++ toList t)) = _
  rw [h]

theorem mem_Kset_plus {k y s t : Term} (h : y ∈ Kset k (plus s t)) :
    y ∈ Kset k s ∨ y ∈ Kset k t := by
  cases hl : toList t with
  | nil => rw [plus_nil hl] at h; exact Or.inl h
  | cons b1 r =>
    rw [plus_cons66 hl, Kset_ofList] at h
    rcases mem_KsetL_append h with h1 | h1
    · refine Or.inl ?_
      rw [Kset_eq_KsetL]
      exact mem_KsetL_of_sub (fun a ha => (List.mem_filter.mp ha).1) h1
    · refine Or.inr ?_
      rw [Kset_eq_KsetL, hl]
      exact h1

theorem Kset_one (k : Term) : Kset k one = [] := rfl

theorem mem_Kset_ofNat {k y : Term} : ∀ n : Nat, y ∈ Kset k (ofNat n) → False
  | 0 => fun h => by cases h
  | n+1 => fun h => by
    rcases mem_Kset_plus (show y ∈ Kset k (plus (ofNat n) one) from h) with h1 | h1
    · exact mem_Kset_ofNat n h1
    · rw [Kset_one] at h1; cases h1

theorem mem_Kset_reg {k y : Term} : ∀ u : Nat, y ∈ Kset k (reg u) → False
  | 0 => fun h => by cases h
  | u+1 => fun h => mem_Kset_ofNat u (show y ∈ Kset k (ofNat u) from h)


theorem mem_of_mem_take {α : Type} {a : α} : ∀ (n : Nat) (l : List α), a ∈ l.take n → a ∈ l
  | 0, l, h => by cases h
  | _+1, [], h => by cases h
  | n+1, b :: t, h => by
    rcases List.mem_cons.mp (show a ∈ b :: t.take n from h) with h1 | h1
    · rw [h1]; exact List.Mem.head _
    · exact List.Mem.tail _ (mem_of_mem_take n t h1)

theorem mem_Kset_splitFin_fst {k y b : Term} (h : y ∈ Kset k (splitFin b).1) : y ∈ Kset k b := by
  have he : (splitFin b).1 = ofList ((toList b).take ((toList b).length -
      (((toList b).reverse.takeWhile (fun x => x == one)).length))) := rfl
  rw [he, Kset_ofList] at h
  rw [Kset_eq_KsetL]
  exact mem_KsetL_of_sub (fun a ha => mem_of_mem_take _ _ ha) h

theorem mem_Kset_phiNFdefault {k y a b : Term} (h : y ∈ Kset k (phiNFdefault a b)) :
    y ∈ Kset k a ∨ y ∈ Kset k b := by
  unfold TM.Term.phiNFdefault at h
  split at h
  · exact Or.inl h
  · exact List.mem_append.mp h

theorem mem_Kset_phiNFsucc {k y a b : Term} (h : y ∈ Kset k (phiNFsucc a b)) :
    y ∈ Kset k a ∨ y ∈ Kset k b := by
  unfold TM.Term.phiNFsucc at h
  split at h
  · rename_i g m heq
    have hgb : ∀ z, z ∈ Kset k g → z ∈ Kset k b := by
      intro z hz
      refine mem_Kset_splitFin_fst ?_
      rw [heq]; exact hz
    have hphi : ∀ (n : Nat), y ∈ Kset k (phi a (plus g (ofNat n))) →
        y ∈ Kset k a ∨ y ∈ Kset k b := by
      intro n h1
      rcases List.mem_append.mp
        (show y ∈ Kset k a ++ Kset k (plus g (ofNat n)) from h1) with h2 | h2
      · exact Or.inl h2
      · rcases mem_Kset_plus h2 with h3 | h3
        · exact Or.inr (hgb y h3)
        · exact absurd h3 (fun hc => mem_Kset_ofNat _ hc)
    split at h
    · split at h
      · split at h
        · exact hphi _ h
        · exact mem_Kset_phiNFdefault h
      · split at h
        · exact hphi _ h
        · exact mem_Kset_phiNFdefault h
    · exact mem_Kset_phiNFdefault h

theorem mem_Kset_phiNF {k y a b : Term} (h : y ∈ Kset k (phiNF a b)) :
    y ∈ Kset k a ∨ y ∈ Kset k b := by
  unfold TM.Term.phiNF at h
  split at h
  · exact Or.inr h
  · split at h
    · split at h
      · exact Or.inr h
      · exact mem_Kset_phiNFsucc h
    · exact mem_Kset_phiNFsucc h

theorem mem_Kset_omegaNF {k y a : Term} (h : y ∈ Kset k (omegaNF a)) : y ∈ Kset k a := by
  unfold TM.Term.omegaNF at h
  split at h
  · exact h
  · split at h
    · cases h
    · rcases mem_Kset_phiNF h with h1 | h1
      · cases h1
      · exact h1


theorem mem_Kset_logOm {k y : Term} (p : Term) (h : y ∈ Kset k (logOm p)) : y ∈ Kset k p := by
  unfold Trans.Dict.logOm at h
  split at h
  · rename_i b
    split at h
    · rcases mem_Kset_plus h with h1 | h1
      · exact h1
      · rw [Kset_one] at h1; cases h1
    · exact h
  · exact h

theorem mem_Kset_subAP {k y w c : Term} (h : y ∈ Kset k (subAP w c)) : y ∈ Kset k c := by
  unfold Trans.Dict.subAP at h
  split at h
  · cases h
  · rename_i p rest heq
    split at h
    · rw [Kset_ofList] at h
      rw [Kset_eq_KsetL, heq]
      exact mem_KsetL_of_sub (fun a ha => List.Mem.tail _ ha) h
    · exact h

theorem mem_Kset_sub1 {k y c : Term} (h : y ∈ Kset k (sub1 c)) : y ∈ Kset k c := by
  unfold Trans.Dict.sub1 at h
  split at h
  · cases h
  · rename_i p rest heq
    split at h
    · rw [Kset_ofList] at h
      rw [Kset_eq_KsetL, heq]
      exact mem_KsetL_of_sub (fun a ha => List.Mem.tail _ ha) h
    · exact h

theorem mem_Kset_divAP {k y w p : Term} (h : y ∈ Kset k (divAP w p)) : y ∈ Kset k p :=
  mem_Kset_logOm p (mem_Kset_subAP (mem_Kset_omegaNF h))

theorem mem_Kset_mulL {k y w z : Term} (h : y ∈ Kset k (mulL w z)) :
    y ∈ Kset k w ∨ y ∈ Kset k z := by
  rw [show mulL w z = ofList ((toList z).map (fun p => omegaNF (plus w (logOm p)))) from rfl,
    Kset_ofList] at h
  obtain ⟨a, ha, hy⟩ := (mem_KsetL_iff k y _).mp h
  obtain ⟨p, hp, hpe⟩ := List.mem_map.mp ha
  rw [← hpe] at hy
  rcases mem_Kset_plus (mem_Kset_omegaNF hy) with h1 | h1
  · exact Or.inl h1
  · refine Or.inr ?_
    rw [Kset_eq_KsetL]
    exact (mem_KsetL_iff k y _).mpr ⟨p, hp, mem_Kset_logOm p h1⟩


theorem mem_Kset_wA {k y w p : Term} (h : y ∈ Kset k (wA w p)) : y ∈ Kset k p := by
  rw [show wA w p
      = ofList (((toList (logOm p)).filter (fun q => !lt q w)).map (divAP w)) from rfl,
    Kset_ofList] at h
  obtain ⟨a, ha, hy⟩ := (mem_KsetL_iff k y _).mp h
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp ha
  rw [← hqe] at hy
  refine mem_Kset_logOm p ?_
  rw [Kset_eq_KsetL]
  exact (mem_KsetL_iff k y _).mpr ⟨q, (List.mem_filter.mp hq).1, mem_Kset_divAP hy⟩

theorem mem_Kset_wC {k y w p : Term} (h : y ∈ Kset k (wC w p)) : y ∈ Kset k p := by
  rw [show wC w p = omegaNF (ofList ((toList (logOm p)).filter (fun q => lt q w))) from rfl] at h
  have h1 := mem_Kset_omegaNF h
  rw [Kset_ofList] at h1
  refine mem_Kset_logOm p ?_
  rw [Kset_eq_KsetL]
  exact mem_KsetL_of_sub (fun a ha => (List.mem_filter.mp ha).1) h1

/-- `w` 以上の先頭成分だけ。`wcnf` は最初の `< w` で止まるので、指数が見るのはここだけ。 -/
def bigPart (w : Term) : List Term → List Term
  | [] => []
  | p :: rest => if lt p w then [] else p :: bigPart w rest

theorem bigPart_sub (w : Term) : ∀ (L : List Term) (a : Term), a ∈ bigPart w L → a ∈ L := by
  intro L
  induction L with
  | nil => intro a h; cases h
  | cons p rest ih =>
    intro a h
    by_cases hlp : lt p w = true
    · rw [show bigPart w (p :: rest) = [] from by
        show (if lt p w = true then [] else p :: bigPart w rest) = []
        rw [if_pos hlp]] at h
      cases h
    · rw [show bigPart w (p :: rest) = p :: bigPart w rest from by
        show (if lt p w = true then [] else p :: bigPart w rest) = _
        rw [if_neg hlp]] at h
      rcases List.mem_cons.mp h with h1 | h1
      · rw [h1]; exact List.Mem.head _
      · exact List.Mem.tail _ (ih a h1)

theorem mem_Kset_wcnf {k w y : Term} : ∀ (L : List Term) (ac : Term × Term),
    ac ∈ (wcnf w L).1 → (y ∈ Kset k ac.1 ∨ y ∈ Kset k ac.2) → y ∈ KsetL k (bigPart w L) := by
  intro L
  induction L with
  | nil => intro ac hac _; cases hac
  | cons p rest ih =>
    intro ac hac hy
    by_cases hlp : lt p w = true
    · rw [wcnf_cons_lt hlp] at hac; cases hac
    · have hlp' : lt p w = false := by
        cases hh : lt p w with
        | false => rfl
        | true => exact absurd hh hlp
      have hbig : bigPart w (p :: rest) = p :: bigPart w rest := by
        show (if lt p w = true then [] else p :: bigPart w rest) = _
        rw [if_neg hlp]
      rw [hbig]
      have hp : ∀ z, (z ∈ Kset k (wA w p) ∨ z ∈ Kset k (wC w p)) →
          z ∈ KsetL k (p :: bigPart w rest) := by
        intro z hz
        refine (mem_KsetL_iff k z (p :: bigPart w rest)).mpr ⟨p, List.Mem.head _, ?_⟩
        rcases hz with h1 | h1
        · exact mem_Kset_wA h1
        · exact mem_Kset_wC h1
      have htail : ∀ z, z ∈ KsetL k (bigPart w rest) → z ∈ KsetL k (p :: bigPart w rest) :=
        fun z hz => mem_KsetL_of_sub (fun a ha => List.Mem.tail _ ha) hz
      rw [wcnf_cons_ge hlp'] at hac
      cases hr : wcnf w rest with
      | mk fst snd =>
        rw [hr] at hac
        have hmem0 : ∀ (q : Term × Term), q ∈ fst → q ∈ (wcnf w rest).1 := by
          intro q hq; rw [hr]; exact hq
        cases fst with
        | nil =>
          rw [List.mem_singleton] at hac
          rw [hac] at hy
          exact hp y hy
        | cons ac0 ps =>
          cases ac0 with
          | mk a' c' =>
            have hac' : ac ∈ (if (wA w p == a') = true
                then ((wA w p, plus (wC w p) c') :: ps, snd)
                else ((wA w p, wC w p) :: (a', c') :: ps, snd)).1 := hac
            by_cases heq : (wA w p == a') = true
            · rw [if_pos heq] at hac'
              rcases List.mem_cons.mp hac' with h1 | h1
              · rw [h1] at hy
                rcases hy with h2 | h2
                · exact hp y (Or.inl h2)
                · rcases mem_Kset_plus h2 with h3 | h3
                  · exact hp y (Or.inr h3)
                  · exact htail y (ih (a', c') (hmem0 _ (List.Mem.head _)) (Or.inr h3))
              · exact htail y (ih ac (hmem0 _ (List.Mem.tail _ h1)) hy)
            · rw [if_neg heq] at hac'
              rcases List.mem_cons.mp hac' with h1 | h1
              · rw [h1] at hy; exact hp y hy
              · exact htail y (ih ac (hmem0 _ h1) hy)

theorem mem_Kset_idxOf {k w y : Term} {s : Option Term × Option Term} {ac : Term × Term}
    (hw : ∀ z, z ∈ Kset k w → False)
    (h : y ∈ Kset k (idxOf w s ac)) :
    (∃ i0, s.1 = some i0 ∧ y ∈ Kset k i0) ∨ y ∈ Kset k ac.1 ∨ y ∈ Kset k ac.2 := by
  have hd : ∀ z, z ∈ Kset k (mulL (mulL w (subAP w ac.1)) ac.2) →
      z ∈ Kset k ac.1 ∨ z ∈ Kset k ac.2 := by
    intro z hz
    rcases mem_Kset_mulL hz with h1 | h1
    · rcases mem_Kset_mulL h1 with h2 | h2
      · exact absurd h2 (fun hc => hw z hc)
      · exact Or.inl (mem_Kset_subAP h2)
    · exact Or.inr h1
  unfold idxOf at h
  split at h
  · exact Or.inr (hd y (mem_Kset_sub1 h))
  · rename_i i0 heq
    rcases mem_Kset_plus h with h1 | h1
    · exact Or.inl ⟨i0, heq, h1⟩
    · exact Or.inr (hd y h1)

theorem stepF_fst (w base : Term) (s : Option Term × Option Term) (ac : Term × Term) :
    (stepF w base s ac).1 = if le w ac.1 = true then some (idxOf w s ac) else s.1 := by
  unfold stepF
  split <;> rfl

/-- 畳み込みが通るどの状態でも、吐かれた指数の `K` は成分の `K` の外に出ない。 -/
theorem Kset_scanSt {k w base : Term} (hw : ∀ z, z ∈ Kset k w → False) (S : Term → Prop) :
    ∀ (l : List (Term × Term)) (s : Option Term × Option Term),
      (∀ i0, s.1 = some i0 → ∀ y, y ∈ Kset k i0 → S y) →
      (∀ ac ∈ l, ∀ y, (y ∈ Kset k ac.1 ∨ y ∈ Kset k ac.2) → S y) →
      ∀ p ∈ scanSt w base s l, ∀ y, y ∈ Kset k (idxOf w p.1 p.2) → S y := by
  intro l
  induction l with
  | nil => intro s _ _ p hp; cases hp
  | cons ac t ih =>
    intro s hs hall p hp y hy
    have hhead : ∀ z, z ∈ Kset k (idxOf w s ac) → S z := by
      intro z hz
      rcases mem_Kset_idxOf hw hz with h1 | h1
      · obtain ⟨i0, hi0, hz0⟩ := h1
        exact hs i0 hi0 z hz0
      · exact hall ac (List.Mem.head _) z h1
    rcases List.mem_cons.mp (show p ∈ (s, ac) :: scanSt w base (stepF w base s ac) t from hp)
      with h | h
    · rw [h] at hy; exact hhead y hy
    · refine ih (stepF w base s ac) ?_ (fun a ha => hall a (List.Mem.tail _ ha)) p h y hy
      intro i0 hi0 z hz
      rw [stepF_fst] at hi0
      split at hi0
      · exact hhead z (by rw [Option.some.inj hi0]; exact hz)
      · exact hs i0 hi0 z hz

/-- **§66.2 の主定理。** 吐かれた指数の `K` は `x` の「大きい成分」の `K` の中。 -/
theorem Kset_scanSt_big (u : Nat) (x : Term) :
    ∀ p ∈ scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1,
      ∀ y, y ∈ Kset (reg (u+1)) (idxOf (reg (u+1)) p.1 p.2) →
        y ∈ KsetL (reg (u+1)) (bigPart (reg (u+1)) (toList x)) := by
  refine Kset_scanSt (fun z hz => mem_Kset_reg (u+1) hz)
    (fun y => y ∈ KsetL (reg (u+1)) (bigPart (reg (u+1)) (toList x)))
    (wcnf (reg (u+1)) (toList x)).1 (none, none) (fun i0 hi0 => by cases hi0) ?_
  intro ac hac y hy
  exact mem_Kset_wcnf (toList x) ac hac hy

/-- 粗い形。§64 が名指しした「`Kset w i` は `x` の `K` に戻る」そのもの。 -/
theorem Kset_scanSt_sub (u : Nat) (x : Term) :
    ∀ p ∈ scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1,
      ∀ y, y ∈ Kset (reg (u+1)) (idxOf (reg (u+1)) p.1 p.2) → y ∈ Kset (reg (u+1)) x := by
  intro p hp y hy
  rw [Kset_eq_KsetL]
  exact mem_KsetL_of_sub (fun a ha => bigPart_sub _ _ a ha) (Kset_scanSt_big u x p hp y hy)

/-- **追跡が買う十分条件。** `x` の大きい成分の `K` の各元が、吐かれる指数より小さいこと。
    `KsetIdxOK` より強いが、指数の `K` を計算せずに `x` だけで書けている。 -/
def KsetBigOK (u : Nat) (x : Term) : Prop :=
  ∀ p ∈ scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1,
    le (reg (u+1)) p.2.1 = true →
    ∀ y ∈ KsetL (reg (u+1)) (bigPart (reg (u+1)) (toList x)),
      lt y (idxOf (reg (u+1)) p.1 p.2) = true

/-- `KsetBigOK` の判定器。 -/
def bigOKb (u : Nat) (x : Term) : Bool :=
  (scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1).all fun p =>
    !(le (reg (u+1)) p.2.1) ||
      (KsetL (reg (u+1)) (bigPart (reg (u+1)) (toList x))).all
        (fun y => lt y (idxOf (reg (u+1)) p.1 p.2))

theorem ksetBigOK_of_b {u : Nat} {x : Term} (h : bigOKb u x = true) : KsetBigOK u x := by
  intro p hp hle y hy
  have h1 := List.all_eq_true.mp h p hp
  rw [hle, Bool.not_true, Bool.false_or] at h1
  exact List.all_eq_true.mp h1 y hy

theorem ksetIdxOK_of_bigOK (u : Nat) (x : Term) (H : KsetBigOK u x) : KsetIdxOK u x := by
  intro p hp hle
  rw [List.all_eq_true]
  intro y hy
  exact H p hp hle y (Kset_scanSt_big u x p hp y hy)

/-- **§66.1 と §66.2 を継ぐ。** -/
theorem psiIdxOK_of_bigOK (u : Nat) (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (H : KsetBigOK u x) : PsiIdxOK u x :=
  psiIdxOK_of_ksetIdxOK u x hx hlx (ksetIdxOK_of_bigOK u x H)

end

/-! ### §66.3 (G3) は偽 — そして `CollapseInT` も偽

最小の反例は `u = 0`, `a = ψ₁(ψ₃0)`。`dict a = ψ_{Ω₂}(Ω₃)` は 𝔗(M) の項だが、`u = 0` の底
`w = Ω₁` で `wcnf` が返す唯一の対は `(ψ_{Ω₂}(Ω₃), 1)`、強臨界枝が点火して指数は
`ψ_{Ω₂}(Ω₃)` 自身、そして `K_{Ω₁} ψ_{Ω₂}(Ω₃) = {Ω₃}` は指数より小さくない。 -/

section
open Trans.Recal (bplus)
open Evidence.Region
open Trans.Dict (wcnf reg dict)
open Trans.Dict (BT)
open TM TM.Term
open Evidence.WF

/-- 反例の引数。`BT` の大きさは 4。 -/
def badArg : BT := BT.D 1 (BT.D 3 BT.zero)

/-- 判定器は `PsiIdxOK` の必要条件。 -/
theorem psiIdxOKb_of_psiIdxOK {u : Nat} {x : Term} (H : PsiIdxOK u x) :
    psiIdxOKb u x = true := by
  show (scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1).all
      (fun p => !(le (reg (u+1)) p.2.1) ||
        inT (psi (reg (u+1)) (idxOf (reg (u+1)) p.1 p.2))) = true
  rw [List.all_eq_true]
  intro p hp
  cases hle : le (reg (u+1)) p.2.1 with
  | false => rfl
  | true => rw [H p hp hle]; rfl

/-- **(G3) の個別反例。** -/
theorem not_psiIdxOK_badArg : ¬ PsiIdxOK 0 (dict badArg) := fun H =>
  Bool.noConfusion ((psiIdxOKb_of_psiIdxOK H).symm.trans
    (show psiIdxOKb 0 (dict badArg) = false from rfl))

/-- **(G3) は偽。** §65 の `collapseInT_of_gap3` と `hsuccS_supply_of_gap3` の仮説は
    満たされない — したがってあの 2 つは真空で、使ってはならない。 -/
theorem not_psiIdxOK_dict : ¬ (∀ (u : Nat) (a : BT), PsiIdxOK u (dict a)) :=
  fun H => not_psiIdxOK_badArg (H 0 badArg)

/-- 同じ反例で `K` の連言そのものも落ちる。 -/
theorem not_ksetIdxOK_dict : ¬ (∀ (u : Nat) (a : BT), KsetIdxOK u (dict a)) := fun H =>
  not_psiIdxOK_badArg
    (psiIdxOK_of_ksetIdxOK 0 (dict badArg)
      (show inT (dict badArg) = true from rfl)
      (show lt (dict badArg) M = true from rfl) (H 0 badArg))

/-- **§63 の `CollapseInT` も偽。** `dict (ψ₀(ψ₁(ψ₃0)))` は 𝔗(M) の項ではない。 -/
theorem not_collapseInT : ¬ CollapseInT := fun H =>
  Bool.noConfusion ((H 0 badArg).symm.trans
    (show inT (dict (BT.D 0 badArg)) = false from rfl))

end

/-! ### §66.4 直しの候補 — `BT` の標準性 (測定のみ、未証明)

反例 `ψ₀(ψ₁(ψ₃0))` は Buchholz の意味で標準でない (`BT.isStd` が偽) — 一方その引数
`ψ₁(ψ₃0)` は標準である。標準性を側条件に足すと、測った限り反例は消える。ここでは名前を
つけ、片方からもう片方が出ることだけを証明する。**どちらも未証明のまま残す。** -/

section
open Trans.Recal (bplus)
open Evidence.Region
open Trans.Dict (reg dict collapse)
open Trans.Dict (BT)
open TM TM.Term
open Evidence.WF

/-- **直しの候補 1。** Buchholz 標準性つきの (G3)。**未証明** (§66.5 で測定のみ)。 -/
def PsiIdxOKStd : Prop :=
  ∀ (u : Nat) (a : BT), BT.isStd (BT.D u a) = true → PsiIdxOK u (dict a)

/-- **直しの候補 2。** Buchholz 標準性つきの `CollapseInT`。 -/
def CollapseInTStd : Prop :=
  ∀ (u : Nat) (a : BT), BT.isStd (BT.D u a) = true → inT (dict (BT.D u a)) = true

/-- 標準な `BT` 項の部分項はまた標準。`D` の場合。 -/
theorem isStd_of_D {u : Nat} {a : BT} (h : BT.isStd (BT.D u a) = true) : BT.isStd a = true :=
  ((Bool.and_eq_true _ _).mp h).1

/-- 同じく `sum` の場合。 -/
theorem isStd_of_sum {a b : BT} (h : BT.isStd (BT.sum a b) = true) :
    BT.isStd a = true ∧ BT.isStd b = true := by
  obtain ⟨h1, _⟩ := (Bool.and_eq_true _ _).mp h
  obtain ⟨h2, h3⟩ := (Bool.and_eq_true _ _).mp h1
  exact ⟨((Bool.and_eq_true _ _).mp h2).2, h3⟩

/-- **標準な `BT` の像は 𝔗(M) に入る — 直した (G3) を仮定して。** -/
theorem inT_dict_of_std (H : PsiIdxOKStd) : ∀ a : BT, BT.isStd a = true →
    inT (dict a) = true ∧ lt (dict a) M = true
  | .zero => fun _ => ⟨inT_zero, lt_zero_M⟩
  | .D u a => fun h => by
    have ih := inT_dict_of_std H a (isStd_of_D h)
    exact inT_collapse_gap3 u (dict a) ih.1 ih.2 (H u a h)
  | .sum a b => fun h => by
    have iha := inT_dict_of_std H a (isStd_of_sum h).1
    have ihb := inT_dict_of_std H b (isStd_of_sum h).2
    exact ⟨inT_plus iha.1 ihb.1, lt_plus_M iha.1 ihb.1 iha.2 ihb.2⟩

/-- **候補 2 は候補 1 から出る。** -/
theorem collapseInTStd_of_psiIdxOKStd (H : PsiIdxOKStd) : CollapseInTStd :=
  fun u a h => (inT_dict_of_std H (BT.D u a) h).1

end

/-! ### §66.5 測定 (凍結)

否定的なものから。母集団は 3 つ — §64 の `bcorp` (添字 0..2)、添字 3 を入れた第 2 母集団
`ccorp`、そして `{0}` を `ψ_u` (`u < 4`) と `⊕` で 3 回閉じた `BT` 項**全部** `small2`。
(G3) の反例が §64 をすり抜けたのは、`bcorp` に添字 3 がなかったからで、それだけ。 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse dict)
open Trans.Dict (BT)
open TM TM.Term
open Evidence.WF

private def emitted66 (u : Nat) (x : Term) : List Term :=
  ((scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1).filter
    (fun p => le (reg (u+1)) p.2.1)).map (fun p => idxOf (reg (u+1)) p.1 p.2)
private def ksetBig66 (u : Nat) (x : Term) : List Term :=
  KsetL (reg (u+1)) (bigPart (reg (u+1)) (toList x))
private def dOf66 (u : Nat) (p : Term) : Term :=
  mulL (mulL (reg (u+1)) (subAP (reg (u+1)) (wA (reg (u+1)) p))) (wC (reg (u+1)) p)

private def bseed66 : List BT := [.zero, .D 0 .zero, .D 1 .zero, .D 2 .zero, .D 0 (.D 1 .zero)]
private def bstep66 (l : List BT) : List BT :=
  l ++ (List.range 3).flatMap (fun u => l.map (fun a => BT.D u a))
    ++ (l.flatMap fun a => l.map fun b => BT.sum a b)
private def bcorp : List BT := (bstep66 (bstep66 bseed66).eraseDups).eraseDups

private def cseed66 : List BT := [.zero, .D 0 .zero, .D 1 .zero, .D 2 .zero, .D 3 .zero,
  .D 1 (.D 2 .zero), .D 0 (.D 2 .zero)]
private def cstep66 (l : List BT) : List BT :=
  l ++ (List.range 4).flatMap (fun u => l.map (fun a => BT.D u a))
    ++ (l.flatMap fun a => l.map fun b => BT.sum a b)
private def ccorp : List BT := (cstep66 ((cstep66 cseed66).eraseDups.take 40)).eraseDups

private def allBT66 : Nat → Nat → List BT
  | 0, _ => [.zero]
  | n+1, k =>
    let sub := (allBT66 n k).eraseDups
    (sub ++ ((List.range k).flatMap fun u => sub.map fun a => BT.D u a)
        ++ (sub.flatMap fun a => sub.map fun b => BT.sum a b)).eraseDups
private def small2 : List BT := allBT66 3 4

/-! **否定 1 — (G3) は偽。** 最小の反例は `u = 0`, `a = ψ₁(ψ₃0)` (`BT` の大きさ 4)。 -/

#guard badArg.size == 3
#guard (BT.D 0 badArg).size == 4
#guard BT.isStd badArg
#guard !(BT.isStd (BT.D 0 badArg))
--   `dict a = ψ_{Ω₂}(Ω₃)` は 𝔗(M) の項で `M` の下。
#guard dict badArg == psi (reg 2) (reg 3)
#guard inT (dict badArg) && lt (dict badArg) M
--   `u = 0` の底は `Ω₁`、`wcnf` の対はただひとつ `(ψ_{Ω₂}(Ω₃), 1)`、強臨界枝が点火する。
#guard (wcnf (reg 1) (toList (dict badArg))).1 == [(dict badArg, one)]
#guard (wcnf (reg 1) (toList (dict badArg))).2 == zero
#guard le (reg 1) (dict badArg)
--   吐かれる指数は `x` 自身で、`K_{Ω₁}` はその外に出る。
#guard emitted66 0 (dict badArg) == [dict badArg]
#guard Kset (reg 1) (dict badArg) == [reg 3]
#guard !(lt (reg 3) (dict badArg))
#guard !(psiIdxOKb 0 (dict badArg))
--   したがって `CollapseInT` も偽。
#guard !(inT (dict (BT.D 0 badArg)))

/-! **否定 2 — なぜ §64 の 1805 項がすり抜けたか。** 添字 2 では割り切れて枝が点火しない。 -/

#guard bcorp.length == 1805
#guard (bcorp.filter fun a => !(inT (dict a))).length == 0
#guard inT (dict (BT.D 0 (BT.D 1 (BT.D 2 BT.zero))))
#guard psiIdxOKb 0 (dict (BT.D 1 (BT.D 2 BT.zero)))
--   `dict (ψ₂0) = Ω₂` はちょうど底なので `a = 1` になりヴェブレン枝、`dict (ψ₃0) = Ω₃` は違う。
#guard dict (BT.D 2 BT.zero) == reg 2
#guard dict (BT.D 3 BT.zero) == reg 3
#guard wA (reg 2) (reg 2) == one
#guard wA (reg 2) (reg 3) == reg 3
#guard !(le (reg 2) (wA (reg 2) (reg 2)))
#guard le (reg 2) (wA (reg 2) (reg 3))

/-! **否定 3 — 全数探索。** `{0}` を `ψ_u` (`u < 4`) と `⊕` で 3 回閉じた 3966 項すべてで、
`inT ∘ dict` が落ちるのはちょうど 1 個、上の反例だけ。標準なものは 1 個も落ちない。 -/

#guard small2.length == 3966
#guard (small2.filter fun a => !(inT (dict a))).length == 1
#guard (small2.filter fun a => !(inT (dict a))) == [BT.D 0 badArg]
#guard (small2.filter fun a => BT.isStd a && !(inT (dict a))).length == 0

/-! **否定 4 — 第 2 母集団。** 添字 3 を入れると (G3) は 1761 項中 67 回落ちる。 -/

#guard ccorp.length == 1761
#guard (ccorp.filter fun a => !(psiIdxOKb 0 (dict a))).length == 67
#guard (ccorp.filter fun a => !(inT (dict a))).length == 1

/-! **否定 5 — 落とした候補たち** (母集団は `bcorp`、`u = 0`)。

  * 「`K_w i` は空」— 空でない成分がある (2 件)。§64 の観察の再確認。
  * 「`K_w x` の元はすべて吐かれる指数より小さい」— 10 件落ちる。落ちる元は `wcnf` の
    **末尾** `ρ` にいて、指数はそれを見ない。追跡を `bigPart` まで細めた理由がこれ。
  * 「大きい成分 `p` ごとに `K_w p < p`」(candQ) — 1 件落ちる。
  * 「大きい成分 `p` ごとに `K_w p < d_p`」(candS) — 1 件落ちる。
  * 「`d_p ≤` 吐かれる指数」(candT) — 1 件落ちる。 -/

#guard (bcorp.filter fun a => !(ksetBig66 0 (dict a)).isEmpty).length == 2
#guard (bcorp.filter fun a =>
    !((emitted66 0 (dict a)).all fun i =>
        (Kset (reg 1) (dict a)).all fun y => lt y i)).length == 10
#guard (bcorp.filter fun a =>
    !((bigPart (reg 1) (toList (dict a))).all fun p =>
        (Kset (reg 1) p).all fun y => lt y p)).length == 1
#guard (bcorp.filter fun a =>
    !((bigPart (reg 1) (toList (dict a))).all fun p =>
        (Kset (reg 1) p).all fun y => lt y (dOf66 0 p))).length == 1
#guard (bcorp.filter fun a =>
    !((bigPart (reg 1) (toList (dict a))).all fun p =>
        (emitted66 0 (dict a)).all fun i => le (dOf66 0 p) i)).length == 1

/-! 肯定。 -/

/-! **肯定 1 — 直しの候補。** `BT.isStd (ψ_u a)` を側条件に足すと、両母集団・`u = 0,1,2,3`
で 0 失敗。`PsiIdxOKStd` はこれを述べたもので、**証明はしていない**。 -/

#guard (List.range 4).all fun u =>
  (bcorp.filter fun a => BT.isStd (BT.D u a) && !(psiIdxOKb u (dict a))).length == 0
#guard (List.range 4).all fun u =>
  (ccorp.filter fun a => BT.isStd (BT.D u a) && !(psiIdxOKb u (dict a))).length == 0
#guard (ccorp.filter fun a => BT.isStd (BT.D 0 a)).length == 322
#guard (ccorp.filter fun a => BT.isStd (BT.D 3 a)).length == 448
#guard (bcorp.filter fun a => BT.isStd a && !(inT (dict a))).length == 0
#guard (ccorp.filter fun a => BT.isStd a && !(inT (dict a))).length == 0

/-! **肯定 2 — §66.2 が買う十分条件 `KsetBigOK`。** `bcorp` では `u = 0,1,2,3` で 0 失敗。
`ccorp` では `psiIdxOKb` より **多く** 落ちる (75 対 67) ので、これは真に強い十分条件であって
(G3) と同値ではない。`ksetBigOK_of_b` があるので、下の `#guard` は 1805 項ぶんの
`KsetBigOK` の証明そのものになっている。 -/

#guard (List.range 4).all fun u => (bcorp.filter fun a => !(bigOKb u (dict a))).length == 0
#guard (ccorp.filter fun a => !(bigOKb 0 (dict a))).length == 75

/-! **肯定 3 — 領域そのもの。** `popNFB 3 6` が作る 443 個の `bVal` 成分では、(G3) も
`KsetBigOK` も `u = 0,1,2,3` で 0 失敗。ただし **280 個は `BT.isStd` ではない** ので、
`PsiIdxOKStd` を証明しても領域はそれだけでは通らない。 -/

#guard ((popNFB 3 6).flatMap fun t => (bVal t).toL).eraseDups.length == 443
#guard (((popNFB 3 6).flatMap fun t => (bVal t).toL).eraseDups.filter
  fun a => !(BT.isStd a)).length == 280
#guard (List.range 4).all fun u =>
  (((popNFB 3 6).flatMap fun t => (bVal t).toL).eraseDups.filter
    fun a => !(psiIdxOKb u (dict a))).length == 0
#guard (List.range 4).all fun u =>
  (((popNFB 3 6).flatMap fun t => (bVal t).toL).eraseDups.filter
    fun a => !(bigOKb u (dict a))).length == 0

end

/-! ### §66.6 公理 -/


/-! ## §67 `CollapseInT` ON THE REGION — `nfB` DOES NOT DODGE IT, `stdB` DOES

§66 proved `CollapseInT` FALSE and left §67 two jobs: "prove `PsiIdxOKStd`, and find the
weaker condition the region's own terms satisfy".  §67 answers the second and REFUTES the
premise the first was going to be used with.

WHAT IS PROVED, UNCONDITIONALLY.

  §67.1  **THE `nfB` REGION DOES NOT DODGE §66'S COUNTEREXAMPLE.**  The idea that the region
         escapes because §66's index `(0,0)(1,1)(2,3)` jumps two levels at once is WRONG: the
         counterexample `ψ₁(ψ₃0)` is reachable from a `nfB` index without any level jump.  The
         witness is

             tbad = (0,0)(1,1)(1,1)(2,2)(3,3)      `nd 0 nil (nd 1 (nd 1 nil nil) (nd 2 nil (nd 3 nil nil)))`

         whose levels rise by exactly one at every step.  `bVal tbad = ψ₀(ψ₁0 ⊕ ψ₁(ψ₃0))`,
         and `inT (vOf tbad) = false` (`not_inT_vOf_tbad`, by `rfl`).  The `ψ₃` appears because
         `bArg` COLLAPSES: the level-2 node with a level-3 child and no left sibling is deleted
         and its child lifted, which turns a one-step ladder `1 → 2 → 3` into the two-step jump
         `ψ₁(ψ₃·)`.  So `not_inT_vOf_nfB` : `¬ ∀ t, nfB t = true → inT (vOf t) = true`.
         `tbad` is one of exactly 5 smallest such indices (5 nodes) and there are 143 of them
         among the 5443 `nfB` indices of levels < 4 with ≤ 6 nodes (measured).

  §67.2  **THE INVARIANT IS `BT.isStd` AFTER ALL — ON `stdB`, WHICH IS WHAT `RegS` IS.**
         `RegS` is `∃ t, stdB t = true ∧ S = matB t 0`, not `nfB`.  §66's "280 of the 443
         `bVal` components are not `BT.isStd`" was measured over `popNFB 3 6`, which filters by
         `nfB` ONLY; restricted to the 235 `stdB` indices of that same population the 443
         components become 163 and the count of non-`BT.isStd` ones becomes **0** (frozen in
         §67.5).  Over every population measured — 1263 / 6933 / 251 standard indices and the
         877 table matrices — `BT.isStd (bVal t)` holds with 0 failures, and so does
         `inT (vOf t)`.  `RegionStdSum` and `RegionStd` name it; `regionStd_of_sum` and
         `isStd_mem_toL` are the (proved) passage from the sum to the components, which is the
         form the consumers want.  **`RegionStd` itself is MEASURED, NOT PROVED.**

  §67.3  **§66.2'S ROUTE DOES NOT REACH THE REGION.**  `KsetBigOK` — the sufficient condition
         §66.2's traceback buys — is strictly stronger than `PsiIdxOK`, and the region falls in
         the gap: of the 1327 `(u, b)` pairs `ψ_u b` occurring inside the `bVal` components of
         the 1263 standard indices of levels < 4, all 1327 satisfy `psiIdxOKb` and **33 fail
         `bigOKb`**.  The smallest failure is an honest region term,

             tBig = (0,0)(1,1)(2,2)(3,3)(2,0),   bVal tBig = ψ₀(Ω₃ ⊕ ψ₁(Ω₃ ⊕ 1))

         (`not_ksetBigOK_aBig`, proved).  So a §68 that wants `PsiIdxOKStd` must go through
         `KsetIdxOK` — the `K` of the index actually emitted — and NOT through the `bigPart`
         over-approximation.  `bigOKb_of_ksetBigOK` is the converse of §66's `ksetBigOK_of_b`
         and is what makes the refutation a theorem rather than a `#guard`.

  §67.4  **THE CONSUMERS, RESTATED.**  §63's `inT_vOf` / `vOf_succ` / `lt_vOf_succ` /
         `hsuccS_supply` carried `CollapseInT`, which §66 refuted, so they are VACUOUS.  Here
         they are restated on the region with `CollapseInT` replaced by the pair

             PsiIdxOKStd   (§66.4, measured: 0 failures on `bcorp` 1805 and `ccorp` 1761)
             RegionStd     (§67.2, measured: 0 failures on 1263 + 6933 + 251 + 877 indices)

         and the extra hypothesis `stdB t = true`, which `hsuccS_index` (§61) supplies for
         free.  Neither hypothesis is refuted by anything measured.

WHAT IS NOT CLAIMED.  **`Hsucc` IS STILL NOT UNCONDITIONAL.**  Two named facts stand between
`hsuccS_supply_std` and `certIn_region`, and neither is proved here:

  (S1)  `PsiIdxOKStd` — [Rathjen, 1991] 2.1(vi) for the indices `collapse` emits from a
        BUCHHOLZ-STANDARD term.  §66 named it, §67 confirms it is the right hypothesis and
        §67.3 tells the next section which route to take to it.
  (S2)  `RegionStd` — `stdB t = true → BT.isStd (bVal t) = true`, i.e. the region's index
        standardness implies Buchholz's standardness of its value.  This is a statement about
        `bVal`/`bArg`/`bFold` versus `nfB`/`nonIncr`/`stdIn`, and proving it needs an order
        theory for `BT.lt` (which the repository does not have yet) plus the transfer of §62's
        `cmpS` through `bArg`.  The shape of the transfer is visible in the definitions:
        `visOK v a` cuts its scan at the first node of level `< v` and `GB v` cuts its descent
        at the first `ψ_w` with `w < v`, which is the same cut; what is missing is that
        `visOK`'s constraint at level EXACTLY `v` plus `nonIncr` covers `GB`'s constraint at
        every level `≥ v`.

NOTHING HERE WEAKENS A STATEMENT.  `not_inT_vOf_nfB` and `not_ksetBigOK_aBig` are
unconditional; everything with `Hp`/`Hr` in it carries them visibly. -/


/-! ### §67.1 `nfB` は §66 の反例を避けない

§66 の反例の添字 `(0,0)(1,1)(2,3)` は段が 1 から 3 に飛ぶので `nfB` ではない。しかし
`bArg` は節を**潰す**ので、段が 1 ずつしか上がらない添字からも同じ `ψ₁(ψ₃0)` が出る。
左に兄弟がある段 1 の節の引数に、段 2 → 段 3 の梯子を置けばよい。 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open TM TM.Term

/-- **反例の添字。** 行列は `(0,0)(1,1)(1,1)(2,2)(3,3)`、段は 1 ずつしか上がらない。 -/
def tbad : B := .nd 0 .nil (.nd 1 (.nd 1 .nil .nil) (.nd 2 .nil (.nd 3 .nil .nil)))

/-- `tbad` は標準形 — つまり `nfB` の意味の「領域」の中にいる。 -/
theorem nfB_tbad : nfB tbad = true := rfl

/-- 値の `BT` は §66 の `badArg = ψ₁(ψ₃0)` を含む。 -/
theorem bVal_tbad :
    bVal tbad = BT.D 0 (BT.sum (BT.D 1 BT.zero) (BT.D 1 (BT.D 3 BT.zero))) := rfl

/-- Buchholz の意味では標準でない。 -/
theorem not_isStd_bVal_tbad : BT.isStd (bVal tbad) = false := rfl

/-- **`vOf tbad` は 𝔗(M) の項ではない。** -/
theorem not_inT_vOf_tbad : inT (vOf tbad) = false := rfl

/-- **§67.1 の主定理。** `nfB` だけでは §63 の `inT_vOf` は救えない。 -/
theorem not_inT_vOf_nfB : ¬ (∀ t : B, nfB t = true → inT (vOf t) = true) := fun H =>
  Bool.noConfusion ((H tbad nfB_tbad).symm.trans not_inT_vOf_tbad)

/-- 同じ添字が `BT.isStd (bVal ·)` も落とす。 -/
theorem not_isStd_bVal_nfB : ¬ (∀ t : B, nfB t = true → BT.isStd (bVal t) = true) := fun H =>
  Bool.noConfusion ((H tbad nfB_tbad).symm.trans not_isStd_bVal_tbad)

end

/-! ### §67.2 領域の不変量 — `stdB` の上では `BT.isStd`

`RegS` は `stdB`。`stdB` に絞ると `bVal` の値は Buchholz の意味で標準になる (測定)。
消費者が要るのは成分ごとの標準性なので、和から成分への通過だけをここで証明する。 -/

section
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open TM TM.Term

/-- **領域の不変量 (和の形)。** **未証明** — §67.5 で測定のみ。 -/
def RegionStdSum : Prop := ∀ t : B, stdB t = true → BT.isStd (bVal t) = true

/-- **消費者が実際に使う形。** `RegionStdSum` より弱い。 -/
def RegionStd : Prop := ∀ t : B, stdB t = true → ∀ a ∈ (bVal t).toL, BT.isStd a = true

/-- 標準な和の成分はまた標準。`isP` が「成分は主要」を保証するので分解できる。 -/
theorem isStd_mem_toL : ∀ (x : BT), BT.isStd x = true → ∀ a ∈ x.toL, BT.isStd a = true
  | .zero => by intro _ a ha; cases ha
  | .D u b => by
      intro h a ha
      rw [List.mem_singleton.mp (show a ∈ [BT.D u b] from ha)]
      exact h
  | .sum x y => by
      intro h a ha
      obtain ⟨h1, h3⟩ := (Bool.and_eq_true _ _).mp h
      obtain ⟨h12, h2⟩ := (Bool.and_eq_true _ _).mp h1
      obtain ⟨hP, h1'⟩ := (Bool.and_eq_true _ _).mp h12
      rcases List.mem_append.mp (show a ∈ x.toL ++ y.toL from ha) with hx | hy
      · cases x with
        | zero => exact Bool.noConfusion hP
        | sum _ _ => exact Bool.noConfusion hP
        | D u b =>
          rw [List.mem_singleton.mp (show a ∈ [BT.D u b] from hx)]
          exact h1'
      · exact isStd_mem_toL y h2 a hy

/-- **和の形から成分の形へ。** -/
theorem regionStd_of_sum (H : RegionStdSum) : RegionStd :=
  fun t ht a ha => isStd_mem_toL (bVal t) (H t ht) a ha

end

/-! ### §67.3 §66.2 の十分条件は領域に届かない

`KsetBigOK` は `PsiIdxOK` より真に強い。領域はその隙間に落ちる — 領域の項で
`psiIdxOKb` は通り `bigOKb` は落ちる。したがって §68 は `bigPart` の上からの評価ではなく、
実際に吐かれる指数の `K` (`KsetIdxOK`) を通らなければならない。 -/

section
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse dict)
open Trans.Dict (BT)
open TM TM.Term
open Evidence.WF

/-- **領域の添字。** 行列は `(0,0)(1,1)(2,2)(3,3)(2,0)`、`nfB` かつ `stdB` (§67.5 で測定)。 -/
def tBig : B := .nd 0 .nil (.nd 1 .nil (.nd 0 (.nd 2 .nil (.nd 3 .nil .nil)) .nil))

/-- その値の `ψ₀` の引数 — `Ω₃ ⊕ ψ₁(Ω₃ ⊕ 1)`。 -/
def aBig : BT := BT.sum (BT.D 3 BT.zero) (BT.D 1 (BT.sum (BT.D 3 BT.zero) (BT.D 0 BT.zero)))

theorem nfB_tBig : nfB tBig = true := rfl
theorem bVal_tBig : bVal tBig = BT.D 0 aBig := rfl

/-- `aBig` は Buchholz の意味で標準で、その `ψ₀` も標準。 -/
theorem isStd_D0_aBig : BT.isStd (BT.D 0 aBig) = true := rfl

/-- **§66 の判定器の逆向き。** `ksetBigOK_of_b` の converse。 -/
theorem bigOKb_of_ksetBigOK {u : Nat} {x : Term} (H : KsetBigOK u x) : bigOKb u x = true := by
  show ((scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1).all
    fun p => !(le (reg (u+1)) p.2.1) ||
      (KsetL (reg (u+1)) (bigPart (reg (u+1)) (toList x))).all
        (fun y => lt y (idxOf (reg (u+1)) p.1 p.2))) = true
  rw [List.all_eq_true]
  intro p hp
  cases hle : le (reg (u+1)) p.2.1 with
  | false => rfl
  | true =>
    rw [Bool.not_true, Bool.false_or, List.all_eq_true]
    intro y hy
    exact H p hp hle y hy

/-- **`KsetBigOK` は領域で落ちる。** -/
theorem not_ksetBigOK_aBig : ¬ KsetBigOK 0 (dict aBig) := fun H =>
  Bool.noConfusion ((bigOKb_of_ksetBigOK H).symm.trans
    (show bigOKb 0 (dict aBig) = false from rfl))

/-- **なのに 2.1(vi) 自身は通る。** 隙間はちょうど §66.2 の追跡の粗さ。 -/
theorem psiIdxOKb_aBig : psiIdxOKb 0 (dict aBig) = true := rfl

/-- **§67.3 の主定理。** `dict` の像の上で `KsetBigOK` を仮定してはいけない。 -/
theorem not_ksetBigOK_dict : ¬ (∀ (u : Nat) (a : BT), BT.isStd (BT.D u a) = true →
    KsetBigOK u (dict a)) := fun H => not_ksetBigOK_aBig (H 0 aBig isStd_D0_aBig)

end

/-! ### §67.4 消費者 — §63 の 4 つを、領域の仮説の上で

§63 の 4 つは `CollapseInT` の上にあり、§66 がそれを反証したので真空。ここでは
`PsiIdxOKStd` (§66.4) と `RegionStd` (§67.2)、そして `stdB` を仮説に置き換える。
`stdB` は §61 の `hsuccS_index` がただで供給する。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT)
open TM TM.Term
open Trans.Dict (dict)

/-- 領域の値の成分は 𝔗(M) の項。 -/
theorem dictAtoms_bVal_std (Hp : PsiIdxOKStd) (Hr : RegionStd) (t : B) (ht : stdB t = true) :
    ∀ a ∈ (bVal t).toL, inT (dict a) = true :=
  fun a ha => (inT_dict_of_std Hp a (Hr t ht a ha)).1

theorem inT_dict_bVal_std (Hp : PsiIdxOKStd) (Hr : RegionStd) (t : B) (ht : stdB t = true) :
    inT (dict (bVal t)) = true := by
  have h := inT_dict_ofL (bVal t).toL (dictAtoms_bVal_std Hp Hr t ht)
  rwa [show BT.ofL (bVal t).toL = bVal t from nfSum_bVal t] at h

/-- **§63 の `inT_vOf` の直し。** 領域の値は 𝔗(M) の項。 -/
theorem inT_vOf_std (Hp : PsiIdxOKStd) (Hr : RegionStd) (t : B) (ht : stdB t = true) :
    inT (vOf t) = true := by
  cases t with
  | nil => exact rfl
  | nd w r c =>
    show inT (plus one (dict (bVal (B.nd w r c)))) = true
    exact inT_plus inT_one (inT_dict_bVal_std Hp Hr _ ht)

/-- **§63 の `vOf_succ` の直し。** -/
theorem vOf_succ_std (Hp : PsiIdxOKStd) (Hr : RegionStd) (r : B) (hr : stdB r = true) :
    vOf (.nd 0 r .nil) = plus (vOf r) one := by
  cases r with
  | nil => exact rfl
  | nd w s c =>
    show plus one (dict (bVal (B.nd 0 (B.nd w s c) B.nil)))
        = plus (plus one (dict (bVal (B.nd w s c)))) one
    rw [show bVal (B.nd 0 (B.nd w s c) B.nil)
          = bplus (bVal (B.nd w s c)) (BT.D 0 BT.zero) from rfl,
      dict_bplus_one _ (nfSum_bVal _) (dictAtoms_bVal_std Hp Hr _ hr)]
    exact (plus_assoc_inT _ _ _ inT_one (inT_dict_bVal_std Hp Hr _ hr) inT_one).symm

/-- **§63 の `lt_vOf_succ` の直し。** -/
theorem lt_vOf_succ_std (Hp : PsiIdxOKStd) (Hr : RegionStd) (r : B) (hr : stdB r = true) :
    lt (vOf r) (vOf (.nd 0 r .nil)) = true := by
  rw [vOf_succ_std Hp Hr r hr]
  exact lt_self_plus_one_inT (vOf r) (inT_vOf_std Hp Hr r hr)

/-- **`certIn_region` の `Hsucc` 供給。** `CollapseInT` (偽) の代わりに `PsiIdxOKStd` と
    `RegionStd` の上で。**まだ無条件ではない。** -/
theorem hsuccS_supply_std (Hp : PsiIdxOKStd) (Hr : RegionStd) :
    ∀ (S : BMS.Matrix) (v : TM.Term), RegS S → ValS S v → BMS.kind S = BMS.Kind.succ →
    ∃ u, v = plus u TM.Term.one ∧ inT v = true ∧ inT u = true ∧ lt u v = true
         ∧ ∀ n, ValS (BMS.expand S n) u := by
  rintro S v _ ⟨t, hstd, rfl, rfl⟩ hk
  rw [kind_matB t] at hk
  obtain ⟨r, rfl⟩ := kindB_succ t hk
  have hr : stdB r = true := stdB_pred r hstd
  have hnf : nfB (B.nd 0 r .nil) = true := nfB_of_stdB _ hstd
  have htop : topOKB (B.nd 0 r .nil) = true := topOKB_of_nfB _ hnf
  have hexp : ∀ n, BMS.expand (matB (B.nd 0 r .nil) 0) n = matB r 0 := by
    intro n
    show (BMS.expand? (matB (B.nd 0 r .nil) 0) n).getD [] = _
    rw [expand_matB (B.nd 0 r .nil) htop (by intro h; exact B.noConfusion h) n]
    rfl
  exact ⟨vOf r, vOf_succ_std Hp Hr r hr, inT_vOf_std Hp Hr _ hstd,
    inT_vOf_std Hp Hr r hr, lt_vOf_succ_std Hp Hr r hr,
    fun n => ⟨r, hr, hexp n, rfl⟩⟩

end

/-! ### §67.5 測定 (凍結)

母集団の作り方を先に書く。`enumNodes L n` は「節が `n` 個以下・段が `L` 未満」の `B` を
全部並べる (§19.3)。ここでは

    popNF67 L n := ((List.range n).flatMap (enumNodes L)).filter (nfB · && · != nil)
    popSt67 L n := (popNF67 L n).filter stdB

すなわち **節の個数は `0 … n-1`、段は `0 … L-1`**。§66 が使った `popNFB 3 6` は
`popNF67 3 6` と同じもので、段は **0,1,2 しかない**。§66 の反例は添字 3 を要るので、
ここでは `L = 4` 以上 (段 0..3) を必ず含める。`popB` は表の 877 行列そのもの。 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse dict)
open Trans.Dict (BT)
open TM TM.Term
open Evidence.WF

private def popNF67 (L n : Nat) : List B :=
  ((List.range n).flatMap (enumNodes L)).filter fun t => nfB t && t != .nil
private def popSt67 (L n : Nat) : List B := (popNF67 L n).filter stdB
/-- `bVal` の成分の中に現れる `ψ_u b` を全部、対 `(u, b)` として。 -/
private def pairsOf : BT → List (Nat × BT)
  | .zero => []
  | .D u a => (u, a) :: pairsOf a
  | .sum a b => pairsOf a ++ pairsOf b
private def pairs67 (l : List B) : List (Nat × BT) :=
  (l.flatMap fun t => (bVal t).toL.flatMap pairsOf).eraseDups

-- 母集団が §66 のものと同じであることの確認。
#guard popNF67 3 6 == popNFB 3 6
#guard (popNF67 3 6).length == 670
#guard (popNF67 4 7).length == 5443
#guard (popSt67 4 7).length == 1263
#guard (popSt67 4 8).length == 6933
#guard (popSt67 5 6).length == 251

/-! **否定 1 — `nfB` は §66 の反例を避けない。** 段が 1 ずつしか上がらない添字から
`ψ₁(ψ₃0)` が出る。`bArg` が段 2 の節を潰して段 3 の子を持ち上げるから。 -/

#guard matB tbad 0 == [[0, 0], [1, 1], [1, 1], [2, 2], [3, 3]]
#guard nfB tbad
#guard !(stdB tbad)
#guard Trans.Recal.Test.showRaw (bVal tbad) == "D_0 (D_1 0,D_1 D_3 0)"
#guard (bVal tbad).toL.length == 1
#guard !(BT.isStd (bVal tbad))
#guard !(inT (vOf tbad))
--   落ちる場所はちょうど §66 の `badArg`。
#guard (BT.D 1 (BT.D 3 BT.zero)) == badArg
#guard !(inT (dict (BT.D 0 (BT.sum (BT.D 1 BT.zero) (BT.D 1 (BT.D 3 BT.zero))))))
--   `nfB` の母集団 (段 0..3・節 ≤ 6) では 5443 個中 143 個が落ち、最小は 5 節でちょうど 5 個。
#guard ((popNF67 4 7).filter fun t => !(inT (vOf t))).length == 143
#guard (((popNF67 4 7).filter fun t => !(inT (vOf t))).map sizeB).foldl min 99 == 5
#guard (((popNF67 4 7).filter fun t => !(inT (vOf t))).filter fun t => sizeB t == 5).length == 5
#guard ((popNF67 4 7).filter fun t => !(inT (vOf t))).any (· == tbad)
--   `BT.isStd (bVal ·)` は `nfB` の上では 5443 個中 3933 個で落ちる。
#guard ((popNF67 4 7).filter fun t => !(BT.isStd (bVal t))).length == 3933

/-! **否定 2 — §66 の「443 成分のうち 280 が標準でない」は `nfB` の母集団の話。**
`RegS` は `stdB`。同じ `popNFB 3 6` を `stdB` で絞ると 235 個・成分 163 個・非標準 0 個。 -/

#guard ((popNF67 3 6).flatMap fun t => (bVal t).toL).eraseDups.length == 443
#guard (((popNF67 3 6).flatMap fun t => (bVal t).toL).eraseDups.filter
  fun a => !(BT.isStd a)).length == 280
#guard ((popNF67 3 6).filter stdB).length == 235
#guard (((popNF67 3 6).filter stdB).flatMap fun t => (bVal t).toL).eraseDups.length == 163
#guard ((((popNF67 3 6).filter stdB).flatMap fun t => (bVal t).toL).eraseDups.filter
  fun a => !(BT.isStd a)).length == 0

/-! **否定 3 — §66.2 の `KsetBigOK` は領域に届かない。** 領域の 1327 対のうち
`psiIdxOKb` は 0 個落ち、`bigOKb` は 33 個落ちる。最小の落ち方が `tBig`。 -/

#guard (pairs67 (popSt67 4 7)).length == 1327
#guard ((pairs67 (popSt67 4 7)).filter fun p => !(psiIdxOKb p.1 (dict p.2))).length == 0
#guard ((pairs67 (popSt67 4 7)).filter fun p => !(bigOKb p.1 (dict p.2))).length == 33
--   強臨界枝は領域でも実際に点火する (1327 対のうち 626 対) ので、`noSC` の逃げ道はない。
#guard ((pairs67 (popSt67 4 7)).filter fun p => !(noSCb p.1 (dict p.2))).length == 626
--   `tBig` は領域の添字で、その値の `ψ₀` の引数が `aBig`。
#guard matB tBig 0 == [[0, 0], [1, 1], [2, 2], [3, 3], [2, 0]]
#guard nfB tBig && stdB tBig
#guard Trans.Recal.Test.showRaw (bVal tBig) == "D_0 (D_3 0,D_1 (D_3 0,D_0 0))"
#guard BT.isStd (BT.D 0 aBig)
#guard psiIdxOKb 0 (dict aBig)
#guard !(bigOKb 0 (dict aBig))
#guard inT (dict (BT.D 0 aBig))

/-! **否定 4 — `nfB` では 2.1(vi) 自身も落ちる。** 段 0..3・節 ≤ 6 の `nfB` 母集団の
`bVal` 成分の中の 5013 対のうち 128 対で `psiIdxOKb` が偽。`stdB` に絞ると 0 個。 -/

#guard (pairs67 (popNF67 4 7)).length == 5013
#guard ((pairs67 (popNF67 4 7)).filter fun p => !(psiIdxOKb p.1 (dict p.2))).length == 128

/-! **肯定 1 — 領域の不変量 `RegionStdSum`。** 3 つの母集団と表の 877 行列で 0 失敗。
`RegionStd` はこれから `regionStd_of_sum` で出る。**証明ではない。** -/

#guard ((popSt67 4 7).filter fun t => !(BT.isStd (bVal t))).length == 0
#guard ((popSt67 4 8).filter fun t => !(BT.isStd (bVal t))).length == 0
#guard ((popSt67 5 6).filter fun t => !(BT.isStd (bVal t))).length == 0
#guard popB.length == 877
#guard (popB.filterMap decodeB).length == 877
#guard ((popB.filterMap decodeB).filter fun t => !(stdB t)).length == 0
#guard ((popB.filterMap decodeB).filter fun t => !(BT.isStd (bVal t))).length == 0

/-! **肯定 2 — 結論そのもの。** 同じ母集団で `inT (vOf t)` が 0 失敗。`inT_vOf_std` が
主張するのはこれで、(S1)(S2) を仮定して証明されている。 -/

#guard ((popSt67 4 7).filter fun t => !(inT (vOf t))).length == 0
#guard ((popSt67 4 8).filter fun t => !(inT (vOf t))).length == 0
#guard ((popSt67 5 6).filter fun t => !(inT (vOf t))).length == 0
#guard ((popB.filterMap decodeB).filter fun t => !(inT (vOf t))).length == 0

/-! **肯定 3 — (S1) `PsiIdxOKStd` の再測定、段 3 を入れた母集団で。** §66 の
`ccorp` は添字 0..3 で 1761 項。`BT.isStd (ψ_u a)` を課すと `u = 0,1,2,3` で 0 失敗。
領域の 1327 対はすべて `BT.isStd (ψ_u b)` を満たす。 -/

#guard ((pairs67 (popSt67 4 7)).filter fun p => !(BT.isStd (BT.D p.1 p.2))).length == 0
#guard ((pairs67 (popNF67 4 7)).filter fun p => !(BT.isStd (BT.D p.1 p.2))).length == 3630

end

/-! ### §67.6 公理 -/

/-! ## §69 `Hlim` FOR THE GENERALISED REGION — THE INDEX HALF IS A THEOREM,
    AND COFINALITY IS FALSE

§61 built the region (`RegS`/`ValS`, the `stdB` indices and their value `vOf`), §62 closed
`Hclosed`, §67 closed `Hsucc` modulo two named gates.  `Hlim` is the last supply, and it has
six conjuncts.  This section settles four of them and REFUTES one.

WHAT IS PROVED, UNCONDITIONALLY.

  §69.1  **THE INDEX HALF.**  For a region matrix of kind `lim` the index is `nd 0 r a` with
         `a ≠ nil`, its `n`-th expansion is `matB (fsB t n) 0`, and `fsB t n` is again a
         region index.  `hlimS_index` packages it; `kindB_lim_std` is the shape lemma
         (`nfB` forces every TOP-LEVEL node to level 0, so the `nd v r nil` with `v ≥ 1`
         branch of `fsB` — the one that returns `nil` — is unreachable inside the region).
         Nothing is assumed.

  §69.4  **COFINALITY IS FALSE ON THE REGION.**  The witness is the diagonal index

             tdiag = (0,0)(1,1)(2,2)      `nd 0 nil (nd 1 nil (nd 2 nil nil))`

         which is `stdB`, has `kindB = lim`, and whose value is `ψ_{Ω₁}(Ω₂)`.  Its
         fundamental sequence is pinned here as a THEOREM at the Buchholz level,

             bVal_fsB_tdiag :  bVal (fsB tdiag k) = ψ₀((ψ₁)^{k+1} 0)

         (`fsB` walks to the nearest ancestor of lower level and iterates there, so the
         sequence is the ψ₁-TOWER, matching §3.1's measured `ε₀, ζ₀, Γ₀, …`).  Under `dict`
         the tower's values are `ψ_{Ω₁}` of a φ̄0-tower over `Ω₁ ⊕ Ω₁`, whose supremum is the
         first ε-number above `Ω₁`.  The term

             sbad = ψ_{Ω₁}(φ̄(1, Ω₁))

         is `inT`, is STRICTLY BELOW `vOf tdiag`, and is strictly ABOVE every member of the
         sequence (checked to `k ≤ 39`).  So `vOf tdiag` is not the supremum of its own
         fundamental sequence in 𝔗(M): there is a gap, and `sbad` sits in it.
         `not_limCofS` / `not_hlimS` turn that into `¬ LimCofS` and `¬ Hlim`.
         Exactly three of the 179 standard limit indices of `popNFB 3 6` fail, and all three
         contain the diagonal: `(0,0)(1,1)(2,2)`, `(0,0)(1,1)(2,2)(3,2)`,
         `(0,0)(1,1)(2,2)(2,2)`.

  §69.4b **THE ORDER HALF OF THE REFUTATION IS A THEOREM.**  `CofGap` — "`sbad` is above
         every member" — splits into an ORDER part and a `dict`-COMPUTATION part, and the
         order part is closed here, unconditionally: `lt_psi_same` ([Rathjen, 1991] 2.3.14(ii),
         read off `ltF` with the fuel matched), `lt_phi_zero_one` (2.3.13(i): `φ̄0x < φ̄1c`
         iff `x < φ̄1c`, so `φ̄(1, Ω₁)` is closed under `ω^·`), `lt_TW` (every φ̄0-tower over
         `Ω₁ ⊕ Ω₁` stays below `φ̄(1, Ω₁)`), `inT_TW`, and `le_sbad_psi_TW`.  What is left is
         ONE named hypothesis, `TowerVal` — the closed form `vOf (fsB tdiag (j+3)) =
         ψ_{Ω₁}(TW (j+3))`, a pure `dict` computation with no order content — and
         `cofGap_of` / `not_limCofS_of` / `not_hlimS_of` carry it visibly.

WHAT IS NAMED AND NOT PROVED.  §69.2 states the three ORDER conjuncts as Props on the
region — `LimDecS`, `LimIncS`, `LimCofS` — and §69.3 assembles `hlimS_supply` from them
together with §67's `PsiIdxOKStd` and `RegionStd` (which carry the two `inT` conjuncts).
`LimDecS` and `LimIncS` are measured with zero counterexamples on five populations; §69.2
also reduces them to the Buchholz level through the measured `VOfLtStd` (`BT.lt` on `bVal`
agrees with `lt` on `vOf`: 0 mismatches on all 235² pairs of `popS 3 6`).  §69.3's `certInS`
puts the four supplies into `certIn_region` and shows the whole region closing on exactly
those five hypotheses.  But `LimCofS` is FALSE, so `hlimS_supply` and `certInS` are not
merely un-discharged — their cofinality hypothesis cannot be discharged at all, and
`certIn_region` cannot be instantiated at `RegS`/`ValS` as they stand.  What would have to
change is the VALUE or the EXPANSION at the diagonal, not the proof.

WHAT IS **NOT** CLAIMED.  `TowerVal` is measured (`j ≤ 9`, plus the two closed forms it
factors through, `dict (psiTow (m+2)) = TW (m+1)` for `m ≤ 7` and
`dict (ψ₀ (psiTow (m+4))) = ψ_{Ω₁}(TW (m+3))` for `m ≤ 5`), NOT proved: proving it means
unfolding `collapse` through `wcnf` / `mulL` / `subAP` / `ω^·` on a parametrised argument,
which is a §64–§65-sized job.  Nothing here is a claim about `Hsucc`, about `PsiIdxOKStd`
or `RegionStd` (§68's job), or about whether the table's value for `(0,0)(1,1)(2,2)` is the
right ordinal — the finding is that the value and the expansion do not agree, not which of
the two is wrong. -/


/-! ### §69.1 添字の側 — 無条件

領域の添字は `nfB` なので最上位の節の段は必ず 0。したがって種別が極限の添字は
`nd 0 r a` (`a ≠ nil`) の形しかなく、`fsB` の「段 ≥ 1 の葉で `nil` を返す」枝は
領域の中では到達しない。展開の同一視は §13 の `expand_matB`、標準性は §62 の `stdB_fsB`。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- 種別が極限なら添字は空でない。 -/
theorem kindB_ne_nil {t : B} (h : kindB t = BMS.Kind.lim) : t ≠ .nil := by
  intro hc
  rw [hc] at h
  exact BMS.Kind.noConfusion h

/-- **領域の極限添字の形。** `nfB` が最上位の段を 0 に縛るので、`a ≠ nil` が出る。 -/
theorem kindB_lim_std : ∀ (t : B), stdB t = true → kindB t = BMS.Kind.lim →
    ∃ r a, a ≠ .nil ∧ t = .nd 0 r a := by
  intro t hstd hk
  cases t with
  | nil => exact absurd rfl (kindB_ne_nil hk)
  | nd v r a =>
    have hv : v = 0 := by
      have h := nfB_of_stdB _ hstd
      have h1 := (nfLe_nd_iff 0 v r a).mp h
      omega
    subst hv
    cases a with
    | nil =>
      rw [kindB_nd_nil, if_pos (show (0 == 0) = true from rfl)] at hk
      exact BMS.Kind.noConfusion hk
    | nd w b c => exact ⟨r, .nd w b c, (by intro hc; exact B.noConfusion hc), rfl⟩

/-- **展開は添字の基本列。** 領域の中では仮定なしで使える形。 -/
theorem expand_matB_std {t : B} (hstd : stdB t = true) (hne : t ≠ .nil) (n : Nat) :
    BMS.expand (matB t 0) n = matB (fsB t n) 0 := by
  show (BMS.expand? (matB t 0) n).getD [] = _
  rw [expand_matB t (topOKB_of_nfB _ (nfB_of_stdB _ hstd)) hne n]
  rfl

/-- **`Hlim` の添字の側。** 値については何も言わない。**無条件。** -/
theorem hlimS_index : ∀ (S : BMS.Matrix), RegS S → BMS.kind S = BMS.Kind.lim →
    ∃ t : B, stdB t = true ∧ S = matB t 0 ∧ kindB t = BMS.Kind.lim
      ∧ ∀ n, BMS.expand S n = matB (fsB t n) 0 ∧ stdB (fsB t n) = true := by
  rintro S ⟨t, hstd, rfl⟩ hk
  rw [kind_matB t] at hk
  exact ⟨t, hstd, rfl, hk, fun n =>
    ⟨expand_matB_std hstd (kindB_ne_nil hk) n, stdB_fsB t hstd n⟩⟩

/-- **極限の展開は領域の値を持つ。** `ValS` の側の条項がこれ。**無条件。** -/
theorem valS_expand : ∀ (t : B), stdB t = true → kindB t = BMS.Kind.lim →
    ∀ n, ValS (BMS.expand (matB t 0) n) (vOf (fsB t n)) := by
  intro t hstd hk n
  exact ⟨fsB t n, stdB_fsB t hstd n, expand_matB_std hstd (kindB_ne_nil hk) n, rfl⟩

end

/-! ### §69.2 三つの順序の条項 — 名前をつける

`Hlim` の 6 連言のうち、`inT` の 2 つは §67 の `PsiIdxOKStd`/`RegionStd` が運び、
`ValS` の 1 つは §69.1 が閉じた。残るのは順序の 3 つで、それがこの節の対象。
`LimDecS`/`LimIncS` は 5 つの母集団で反例 0 (§69.5)、`LimCofS` は §69.4 で**偽**。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- **減少。** 基本列の値は元の値より真に小さい。**測定のみ** (§69.5)。 -/
def LimDecS : Prop := ∀ (t : B), stdB t = true → kindB t = BMS.Kind.lim →
    ∀ n, lt (vOf (fsB t n)) (vOf t) = true

/-- **増加。** 基本列の値は真に増える。**測定のみ** (§69.5)。 -/
def LimIncS : Prop := ∀ (t : B), stdB t = true → kindB t = BMS.Kind.lim →
    ∀ n, lt (vOf (fsB t n)) (vOf (fsB t (n + 1))) = true

/-- **共終性。** 値より下の 𝔗(M) の項はどれか一つの基本列の項以下。**§69.4 で偽。** -/
def LimCofS : Prop := ∀ (t : B), stdB t = true → kindB t = BMS.Kind.lim →
    ∀ s, inT s = true → lt s (vOf t) = true → ∃ n, le s (vOf (fsB t n)) = true

/-- **Buchholz 側の順序を 𝔗(M) 側へ運ぶ仮説。** `dict` の順序保存の、領域に絞った形。
    `popS 3 6` の 235² 対で不一致 0 (§69.5)。**未証明。** -/
def VOfLtStd : Prop := ∀ (u t : B), stdB u = true → stdB t = true →
    BT.lt (bVal u) (bVal t) = true → lt (vOf u) (vOf t) = true

/-- 減少の Buchholz 側。**測定のみ** (§69.5)。 -/
def BLimDec : Prop := ∀ (t : B), stdB t = true → kindB t = BMS.Kind.lim →
    ∀ n, BT.lt (bVal (fsB t n)) (bVal t) = true

/-- 増加の Buchholz 側。**測定のみ** (§69.5)。 -/
def BLimInc : Prop := ∀ (t : B), stdB t = true → kindB t = BMS.Kind.lim →
    ∀ n, BT.lt (bVal (fsB t n)) (bVal (fsB t (n + 1))) = true

/-- **減少は Buchholz 側へ落ちる。** -/
theorem limDecS_of (HV : VOfLtStd) (HB : BLimDec) : LimDecS :=
  fun t hstd hk n => HV (fsB t n) t (stdB_fsB t hstd n) hstd (HB t hstd hk n)

/-- **増加も Buchholz 側へ落ちる。** -/
theorem limIncS_of (HV : VOfLtStd) (HB : BLimInc) : LimIncS :=
  fun t hstd hk n => HV (fsB t n) (fsB t (n + 1)) (stdB_fsB t hstd n)
    (stdB_fsB t hstd (n + 1)) (HB t hstd hk n)

end

/-! ### §69.3 組み立て

`certIn_region` が求める `Hlim` の形そのもの。`f n = vOf (fsB t n)` で、`ValS` と
`inT` の条項は §69.1 と §67 が閉じ、順序の 3 つは仮説のまま残る。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- **`certIn_region` の `Hlim` 供給。** 仮説は 5 つ — §67 の 2 つ (`inT` の側) と
    §69.2 の 3 つ (順序の側)。**`LimCofS` は §69.4 で偽なので、この定理は
    `certIn_region` を実際に起動できない。**そのことを含めて §69.4 に書く。 -/
theorem hlimS_supply (Hp : PsiIdxOKStd) (Hr : RegionStd)
    (HD : LimDecS) (HI : LimIncS) (HC : LimCofS) :
    ∀ (S : BMS.Matrix) (v : TM.Term), RegS S → ValS S v → BMS.kind S = BMS.Kind.lim →
    ∃ f : Nat → TM.Term, inT v = true
      ∧ (∀ n, ValS (BMS.expand S n) (f n))
      ∧ (∀ n, inT (f n) = true)
      ∧ (∀ n, lt (f n) v = true)
      ∧ (∀ n, lt (f n) (f (n + 1)) = true)
      ∧ (∀ s, inT s = true → lt s v = true → ∃ n, le s (f n) = true) := by
  rintro S v _ ⟨t, hstd, rfl, rfl⟩ hk
  rw [kind_matB t] at hk
  exact ⟨fun n => vOf (fsB t n), inT_vOf_std Hp Hr t hstd,
    valS_expand t hstd hk,
    fun n => inT_vOf_std Hp Hr _ (stdB_fsB t hstd n),
    HD t hstd hk, HI t hstd hk, HC t hstd hk⟩

/-- 同じものを Buchholz 側の仮説で。 -/
theorem hlimS_supply_bt (Hp : PsiIdxOKStd) (Hr : RegionStd)
    (HV : VOfLtStd) (HBD : BLimDec) (HBI : BLimInc) (HC : LimCofS) :
    ∀ (S : BMS.Matrix) (v : TM.Term), RegS S → ValS S v → BMS.kind S = BMS.Kind.lim →
    ∃ f : Nat → TM.Term, inT v = true
      ∧ (∀ n, ValS (BMS.expand S n) (f n))
      ∧ (∀ n, inT (f n) = true)
      ∧ (∀ n, lt (f n) v = true)
      ∧ (∀ n, lt (f n) (f (n + 1)) = true)
      ∧ (∀ s, inT s = true → lt s v = true → ∃ n, le s (f n) = true) :=
  hlimS_supply Hp Hr (limDecS_of HV HBD) (limIncS_of HV HBI) HC

/-- **輪が閉じる形。** §62 の `Hclosed`、§61 の `Hzero`、§67 の `Hsucc`、そしてここの
    `Hlim` を `certIn_region` に入れると、領域のすべての行列が証明書を持つ。仮説は 5 つ
    — §67 の 2 つと §69.2 の 3 つ。**そのうち `LimCofS` は §69.4 で偽なので、この定理は
    実際には起動できない。**残っているのが何かを 1 行で言うために置いてある。 -/
theorem certInS (Hp : PsiIdxOKStd) (Hr : RegionStd)
    (HD : LimDecS) (HI : LimIncS) (HC : LimCofS) :
    ∀ (v : TM.Term), Acc Evidence.WF.RT v → ∀ (S : BMS.Matrix), RegS S → ValS S v →
      Evidence.Cert.CertifiedIn Evidence.Cert.DomI S v :=
  Evidence.Cert.certIn_region hclosedS_supply hzeroS_supply (hsuccS_supply_std Hp Hr)
    (hlimS_supply Hp Hr HD HI HC)

end

/-! ### §69.4 共終性は偽 — 対角の添字で

`fsB` は「段が `w` 未満の最も近い祖先」まで降りてそこで反復する (§3.2)。対角の添字
`(0,0)(1,1)(2,2)` では最後の節の段が 2、その祖先で段が 2 未満の最も近いものが段 1 の節
なので、反復されるのは ψ₁ の梯子であり、基本列は **ψ₁ の塔** になる。ここではそれを
Buchholz 項の等式として証明する (`bVal_fsB_tdiag`)。

値の側は測定 (§69.5): 塔の値は `ψ_{Ω₁}` を頭に持ち、その引数は `Ω₁ ⊕ Ω₁` の上の
φ̄0 の塔で、上限は `Ω₁` より上の最初の ε 数。一方 `vOf tdiag = ψ_{Ω₁}(Ω₂)` はそれより
はるかに上にある。その隙間に `sbad = ψ_{Ω₁}(φ̄(1, Ω₁))` が入る。 -/

section
open Trans.Recal
open Trans.Dict (BT dict)
open TM TM.Term

/-- **対角の添字。** 行列は `(0,0)(1,1)(2,2)`。 -/
def tdiag : B := .nd 0 .nil (.nd 1 .nil (.nd 2 .nil .nil))

theorem matB_tdiag : matB tdiag 0 = [[0, 0], [1, 1], [2, 2]] := rfl
theorem stdB_tdiag : stdB tdiag = true := rfl
theorem kindB_tdiag : kindB tdiag = BMS.Kind.lim := rfl
theorem bVal_tdiag : bVal tdiag = BT.D 0 (BT.D 2 BT.zero) := rfl

/-- ψ₁ の塔 (添字の側)。 -/
def bTow : Nat → B
  | 0 => .nd 1 .nil .nil
  | k + 1 => .nd 1 .nil (bTow k)

/-- ψ₁ の塔 (Buchholz 項の側)。 -/
def psiTow : Nat → BT
  | 0 => BT.zero
  | m + 1 => BT.D 1 (psiTow m)

theorem bTow_shape : ∀ k, ∃ x, bTow k = .nd 1 .nil x
  | 0 => ⟨.nil, rfl⟩
  | k + 1 => ⟨bTow k, rfl⟩

/-- `iterD` が作るのは塔そのもの。 -/
theorem iterD_bTow : ∀ k, iterD 1 (.nd 2 .nil .nil) k = bTow k
  | 0 => rfl
  | k + 1 => by
      show B.nd 1 .nil (appB .nil (iterD 1 (.nd 2 .nil .nil) k)) = _
      rw [appB_nil, iterD_bTow k]
      rfl

/-- **対角の基本列。** `rwB` が段 1 の節まで降りて、そこで反復する。 -/
theorem fsB_tdiag (k : Nat) : fsB tdiag k = .nd 0 .nil (bTow k) := by
  show B.nd 0 .nil (appB .nil (iterD 1 (.nd 2 .nil .nil) k)) = _
  rw [appB_nil, iterD_bTow k]

theorem bArg1_bTow : ∀ k, bArg 1 (bTow k) = psiTow (k + 1)
  | 0 => rfl
  | k + 1 => by
      have h : bArg 1 (bTow (k + 1)) = BT.D 1 (bArg 1 (bTow k)) := by
        show bArg 1 (B.nd 1 .nil (bTow k)) = _
        rw [bArg_single]
        exact bK_le 1 1 .nil (bTow k) (Nat.le_refl 1)
      rw [h, bArg1_bTow k]
      rfl

theorem bArg0_bTow : ∀ k, bArg 0 (bTow k) = psiTow (k + 1)
  | 0 => rfl
  | k + 1 => by
      obtain ⟨x, hx⟩ := bTow_shape k
      have h : bArg 0 (bTow (k + 1)) = BT.D 1 (bArg 1 (bTow k)) := by
        show bArg 0 (B.nd 1 .nil (bTow k)) = _
        rw [bArg_single, hx]
        rfl
      rw [h, bArg1_bTow k]
      rfl

/-- **対角の基本列の値 (Buchholz 側)、証明済み。** `ψ₀((ψ₁)^{k+1} 0)`。 -/
theorem bVal_fsB_tdiag (k : Nat) : bVal (fsB tdiag k) = BT.D 0 (psiTow (k + 1)) := by
  rw [fsB_tdiag k]
  obtain ⟨x, hx⟩ := bTow_shape k
  have h : bVal (B.nd 0 .nil (bTow k)) = BT.D 0 (bArg 0 (bTow k)) := by
    rw [hx]; rfl
  rw [h, bArg0_bTow k]

/-- **隙間に入る項。** `ψ_{Ω₁}(φ̄(1, Ω₁))`。 -/
def sbad : Term := psi (Z zero) (phi (phi zero zero) (Z zero))

theorem inT_sbad : inT sbad = true := rfl
theorem lt_sbad_tdiag : lt sbad (vOf tdiag) = true := rfl

/-- **隙間の主張。** `sbad` は基本列のどの項以下でもない。`k ≤ 39` まで測定 (§69.5)、
    **証明されていない**。閉じた形が要る — §69.5 の最後を見よ。 -/
def CofGap : Prop := ∀ k, le sbad (vOf (fsB tdiag k)) = false

/-- **§69.4 の主定理。** 共終性の条項は領域の上で偽。 -/
theorem not_limCofS (H : CofGap) : ¬ LimCofS := by
  intro HC
  obtain ⟨n, hn⟩ := HC tdiag stdB_tdiag kindB_tdiag sbad inT_sbad lt_sbad_tdiag
  exact Bool.noConfusion (hn.symm.trans (H n))

/-- 同じ行列から来る領域の添字は同じ値を持つ (`oR_vOf` の一意性)。 -/
theorem vOf_of_matB_eq {u t : B} (hu : stdB u = true) (ht : stdB t = true)
    (h : matB u 0 = matB t 0) : vOf u = vOf t := by
  have h1 := oR_vOf u (nfB_of_stdB _ hu)
  have h2 := oR_vOf t (nfB_of_stdB _ ht)
  rw [h] at h1
  exact Option.some.inj (h1.symm.trans h2)

/-- **`ValS` は列を決めてしまう。** 別の `f` を選ぶ逃げ道は無い。 -/
theorem valS_pins {t : B} (hstd : stdB t = true) (hk : kindB t = BMS.Kind.lim)
    {v : TM.Term} (n : Nat) (h : ValS (BMS.expand (matB t 0) n) v) : v = vOf (fsB t n) := by
  obtain ⟨u, hu, heq, rfl⟩ := h
  rw [expand_matB_std hstd (kindB_ne_nil hk) n] at heq
  exact vOf_of_matB_eq hu (stdB_fsB t hstd n) heq.symm

/-- **`Hlim` は `RegS`/`ValS` では成り立たない。** `certIn_region` をこの領域で
    起動することはできない。 -/
theorem not_hlimS (H : CofGap) :
    ¬ (∀ (S : BMS.Matrix) (v : TM.Term), RegS S → ValS S v → BMS.kind S = BMS.Kind.lim →
      ∃ f : Nat → TM.Term, inT v = true
        ∧ (∀ n, ValS (BMS.expand S n) (f n))
        ∧ (∀ n, inT (f n) = true)
        ∧ (∀ n, lt (f n) v = true)
        ∧ (∀ n, lt (f n) (f (n + 1)) = true)
        ∧ (∀ s, inT s = true → lt s v = true → ∃ n, le s (f n) = true)) := by
  intro HL
  obtain ⟨f, _, hval, _, _, _, hcof⟩ := HL (matB tdiag 0) (vOf tdiag)
    ⟨tdiag, stdB_tdiag, rfl⟩ ⟨tdiag, stdB_tdiag, rfl, rfl⟩
    (by rw [kind_matB]; exact kindB_tdiag)
  obtain ⟨n, hn⟩ := hcof sbad inT_sbad lt_sbad_tdiag
  rw [valS_pins stdB_tdiag kindB_tdiag n (hval n)] at hn
  exact Bool.noConfusion (hn.symm.trans (H n))

end

/-! ### §69.4b 隙間の順序の側は定理 — 残るのは `dict` の閉じた形だけ

`CofGap` を二つに割る。順序の部分 (「φ̄0 の塔はどれも `φ̄(1, Ω₁)` の下」と
「だから `sbad` はどの項以下でもない」) は**ここで証明する**。残るのは `dict` の
計算そのもの、すなわち `TowerVal` — 基本列の値の閉じた形 — だけになる。

道具は 3 つで、どれも [Rathjen, 1991] 2.3 の節を `ltF` の燃料を合わせて読んだもの:
`lt_psi_same` (2.3.14(ii): 添字が同じ `ψ` の比較は引数の比較)、`lt_phi_zero_one`
(2.3.13(i): `φ̄0x < φ̄1c ⟺ x < φ̄1c`)、そして `Evidence/WF.lean` §8.5.4 の `lt_asymm_inT`。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term
open Evidence.WF

/-- `Ω₁ ⊕ Ω₁` の上に積んだ φ̄0 の塔。基本列の値の引数はこれ (§69.5 で測定)。 -/
def TW : Nat → TM.Term
  | 0 => TM.Term.add (Z zero) (Z zero)
  | j + 1 => phi zero (TW j)

/-- **2.3.14(ii)。** 添字が同じ `ψ` の比較は、引数の比較そのもの。 -/
theorem lt_psi_same (k a b : Term) : lt (psi k a) (psi k b) = lt a b := by
  by_cases h : a = b
  · subst h; rw [lt_irrefl, lt_irrefl]
  · have hne : ((psi k a : Term) == psi k b) = false := by
      cases hq : ((psi k a : Term) == psi k b) with
      | false => rfl
      | true =>
        exfalso
        have he : (psi k a : Term) = psi k b := of_decide_eq_true hq
        injection he with _ h2
        exact h h2
    have hd : (psi k a).deg + (psi k b).deg
        = (k.deg + k.deg + a.deg + b.deg + 1) + 1 := by
      show (1 + k.deg + a.deg) + (1 + k.deg + b.deg) = _
      omega
    rw [lt_eq_ltF (psi k a) (psi k b) ((psi k a).deg + (psi k b).deg) (Nat.le_refl _), hd]
    show (if ((psi k a : Term) == psi k b) = true then false
          else if ((k : Term) == k) = true then
            ltF (k.deg + k.deg + a.deg + b.deg + 1) a b
          else if ltF (k.deg + k.deg + a.deg + b.deg + 1) k k = true then
            ltF (k.deg + k.deg + a.deg + b.deg + 1) k (psi k b)
          else ltF (k.deg + k.deg + a.deg + b.deg + 1) (psi k a) k) = _
    rw [hne, if_neg (fun hc => Bool.noConfusion hc),
      if_pos (show ((k : Term) == k) = true from beq_self_eq_true k)]
    exact (lt_eq_ltF a b (k.deg + k.deg + a.deg + b.deg + 1) (by omega)).symm

/-- **2.3.13(i)。** `φ̄(1, c)` は `ω^·` で閉じている — 第 1 引数が上がるので、
    比較は引数のほうへ落ちる。 -/
theorem lt_phi_zero_one (x c : Term) :
    lt (phi zero x) (phi TM.Term.one c) = lt x (phi TM.Term.one c) := by
  have hd : (phi zero x).deg + (phi TM.Term.one c).deg = (x.deg + c.deg + 5) + 1 := by
    show (1 + 1 + x.deg) + (1 + (1 + 1 + 1) + c.deg) = _
    omega
  have hz : ltF (x.deg + c.deg + 5) zero TM.Term.one = true := by
    rw [← lt_eq_ltF zero TM.Term.one (x.deg + c.deg + 5) (by show 1 + (1 + 1 + 1) ≤ _; omega)]
    rfl
  rw [lt_eq_ltF (phi zero x) (phi TM.Term.one c)
      ((phi zero x).deg + (phi TM.Term.one c).deg) (Nat.le_refl _), hd]
  show (if ((phi zero x : Term) == phi TM.Term.one c) = true then false
        else if ((zero : Term) == TM.Term.one) = true then
          ltF (x.deg + c.deg + 5) x c
        else if ltF (x.deg + c.deg + 5) zero TM.Term.one = true then
          ltF (x.deg + c.deg + 5) x (phi TM.Term.one c)
        else (((phi zero x : Term) == c)
              || ltF (x.deg + c.deg + 5) (phi zero x) c)) = _
  rw [show ((phi zero x : Term) == phi TM.Term.one c) = false from rfl,
    if_neg (fun hc => Bool.noConfusion hc),
    show ((zero : Term) == TM.Term.one) = false from rfl,
    if_neg (fun hc => Bool.noConfusion hc), hz, if_pos rfl]
  exact (lt_eq_ltF x (phi TM.Term.one c) (x.deg + c.deg + 5)
    (by show x.deg + (1 + (1 + 1 + 1) + c.deg) ≤ _; omega)).symm

/-- **塔はすべて `φ̄(1, Ω₁)` の下。** これが隙間の理由。 -/
theorem lt_TW : ∀ j, lt (TW j) (phi TM.Term.one (Z zero)) = true
  | 0 => rfl
  | j + 1 => by
      show lt (phi zero (TW j)) (phi TM.Term.one (Z zero)) = true
      rw [lt_phi_zero_one]
      exact lt_TW j

theorem lt_TW_M : ∀ j, lt (TW j) M = true
  | 0 => by
      show lt (TM.Term.add (Z zero) (Z zero)) M = true
      rw [lt_add_M]
      exact lt_Z_M zero
  | j + 1 => lt_phi_M zero (TW j)

theorem inT_TW : ∀ j, inT (TW j) = true
  | 0 => rfl
  | j + 1 => by
      show (inT zero && inT (TW j) && lt zero M && lt (TW j) M) = true
      rw [inT_TW j, lt_TW_M j]
      rfl

theorem sbad_eq : sbad = psi (Z zero) (phi TM.Term.one (Z zero)) := rfl

/-- **隙間の順序の側、証明済み。** `sbad` は `ψ_{Ω₁}(TW j)` のどれ以下でもない。 -/
theorem le_sbad_psi_TW (j : Nat) : le sbad (psi (Z zero) (TW j)) = false := by
  have h1 : lt (TW j) (phi TM.Term.one (Z zero)) = true := lt_TW j
  have hne2 : TW j ≠ phi TM.Term.one (Z zero) := by
    intro hc
    rw [hc, lt_irrefl] at h1
    exact Bool.noConfusion h1
  have hne : ((sbad : Term) == psi (Z zero) (TW j)) = false := by
    cases hq : ((sbad : Term) == psi (Z zero) (TW j)) with
    | false => rfl
    | true =>
      exfalso
      have he : (psi (Z zero) (phi TM.Term.one (Z zero)) : Term) = psi (Z zero) (TW j) :=
        sbad_eq ▸ of_decide_eq_true hq
      injection he with _ h2
      exact hne2 h2.symm
  have h2 : lt sbad (psi (Z zero) (TW j)) = false := by
    rw [sbad_eq, lt_psi_same]
    exact lt_asymm_inT (inT_TW j) (show inT (phi TM.Term.one (Z zero)) = true from rfl) h1
  show (((sbad : Term) == psi (Z zero) (TW j)) || lt sbad (psi (Z zero) (TW j))) = false
  rw [hne, h2]
  rfl

/-- **残った穴は `dict` の計算そのもの。** 基本列の値の閉じた形。`j ≤ 9` まで測定
    (§69.5)、**証明されていない**。`collapse` を `wcnf`/`mulL`/`subAP`/`ω^·` まで
    展開する必要があり、それは §64–§65 と同じ規模の仕事。 -/
def TowerVal : Prop := ∀ j, vOf (fsB tdiag (j + 3)) = psi (Z zero) (TW (j + 3))

/-- **`CofGap` は `TowerVal` だけに縮む。** 順序の側は上で閉じた。 -/
theorem cofGap_of (H : TowerVal) : CofGap := by
  intro k
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | (j + 3) =>
    rw [H j]
    exact le_sbad_psi_TW (j + 3)

/-- **共終性は偽 — 仮説は `TowerVal` ただ 1 つ。** -/
theorem not_limCofS_of (H : TowerVal) : ¬ LimCofS := not_limCofS (cofGap_of H)

/-- **`Hlim` は成り立たない — 仮説は `TowerVal` ただ 1 つ。** -/
theorem not_hlimS_of (H : TowerVal) :
    ¬ (∀ (S : BMS.Matrix) (v : TM.Term), RegS S → ValS S v → BMS.kind S = BMS.Kind.lim →
      ∃ f : Nat → TM.Term, inT v = true
        ∧ (∀ n, ValS (BMS.expand S n) (f n))
        ∧ (∀ n, inT (f n) = true)
        ∧ (∀ n, lt (f n) v = true)
        ∧ (∀ n, lt (f n) (f (n + 1)) = true)
        ∧ (∀ s, inT s = true → lt s v = true → ∃ n, le s (f n) = true)) :=
  not_hlimS (cofGap_of H)

end

/-! ### §69.5 測定 (凍結)

母集団の作り方を先に書く。`enumNodes L n` は「節がちょうど `n` 個・段が `L` 未満」の `B`
を全部並べる (§19.3)。それを使って

    popNFB L n  =  ((List.range n).flatMap (enumNodes L)).filter (nfB · && · != nil)   §48
    popS   L n  =  (popNFB L n).filter stdB                                            §61
    limP   L n  =  (popS L n).filter (kindB · == lim)          極限の添字だけ
    valP   L n  =  ((popS L n).map vOf).eraseDups              領域の値だけ
    outP   L n  =  (((popNFB L n).filter (!stdB ·)).map vOf).eraseDups.filter inT
                                                              領域の**外**の 𝔗(M) の項
    cloP        =  valP 3 5 を `plus` / `ω^·` / `φ̄(·,0)` / `ψ_{Ω₁}(·)` で 1 段閉じ、
                   `inT` かつ `< Ω₁` に絞ったもの (1450 項)
    popB        =  表の幅 2 の 52 行の深さ 3 の閉包、877 行列 (§3.5)

すなわち **節の個数は `0 … n-1`、段は `0 … L-1`**。`outP` と `cloP` が要るのは、共終性の
`s` が領域の値だけでなく 𝔗(M) の項**すべて**を走るからで、§65–§67 が三度続けて踏んだ罠
(母集団が量化の形と違う) はここにある。実際、**領域の値だけで掃くと共終性は通る**。 -/

section
open Trans.Recal
open Trans.Dict (BT dict)
open TM TM.Term

private def limP (L n : Nat) : List B := (popS L n).filter fun t => kindB t == BMS.Kind.lim
private def valP (L n : Nat) : List Term := ((popS L n).map vOf).eraseDups
private def outP (L n : Nat) : List Term :=
  (((popNFB L n).filter fun t => !(stdB t)).map vOf).eraseDups.filter fun x => inT x
private def cloP : List Term :=
  ((valP 3 5) ++ (valP 3 5).flatMap (fun a => (valP 3 5).map (fun b => plus a b))
     ++ (valP 3 5).map omegaNF
     ++ (valP 3 5).map (fun a => phi a zero)
     ++ (valP 3 5).map (fun a => psi (Z zero) a)).eraseDups.filter
    fun x => inT x && lt x (Z zero)
/-- 共終性が落ちる対 `(t, s)`。 -/
private def cofFail (N : Nat) (ts : List B) (ss : List Term) : List (B × Term) :=
  ts.flatMap fun t => (ss.filter fun s =>
    lt s (vOf t) && !((List.range N).any fun k => le s (vOf (fsB t k)))).map fun s => (t, s)
/-- 共終性が落ちる添字。 -/
private def cofBad (N : Nat) (ts : List B) (ss : List Term) : List B :=
  ts.filter fun t => ss.any fun s =>
    lt s (vOf t) && !((List.range N).any fun k => le s (vOf (fsB t k)))
-- 母集団の大きさ。
#guard (popNFB 3 6).length == 670
#guard (popS 3 6).length == 235
#guard (limP 3 6).length == 179
#guard (valP 3 6).length == 235
#guard (outP 3 6).length == 74
#guard (outP 4 7).length == 458
#guard cloP.length == 1450
#guard (popS 4 6).length == 250
#guard (limP 4 6).length == 193
#guard (popS 4 7).length == 1263
#guard (limP 4 7).length == 1012
#guard (popS 5 6).length == 251
#guard (limP 5 6).length == 194
#guard popB.length == 877

/-! **否定 1 — 共終性は偽。** `s` を領域の外の 𝔗(M) の項まで広げると落ちる。
`popNFB 3 6` の 179 個の極限添字のうち、`outP 3 6` (74 項) では 1 個・12 対が落ち、
`outP 4 7` (458 項) では **3 個**が落ちる。落ちる 3 個はどれも対角 `(0,0)(1,1)(2,2)` を
含む。`N = 12` で測っているが、対角では `N = 40` でも落ちる (下)。 -/

#guard (cofFail 12 (limP 3 6) (outP 3 6)).length == 12
#guard (cofBad 12 (limP 3 6) (outP 3 6)).length == 1
#guard (cofBad 12 (limP 3 6) (outP 3 6)).map (fun t => matB t 0) == [[[0,0],[1,1],[2,2]]]
#guard (cofBad 12 (limP 3 6) (outP 4 7)).map (fun t => matB t 0)
  == [[[0,0],[1,1],[2,2]], [[0,0],[1,1],[2,2],[3,2]], [[0,0],[1,1],[2,2],[2,2]]]

/-! **否定 1 の中身。** 対角の添字は標準・極限で、値は `ψ_{Ω₁}(Ω₂)`。基本列は ψ₁ の塔で
`ε₀, ζ₀, Γ₀, …` (§3.1 の測定と一致)。`sbad = ψ_{Ω₁}(φ̄(1,Ω₁))` は `inT`、`vOf tdiag` より
真に小さく、基本列のどの項よりも真に大きい — `k ≤ 39` まで。 -/

#guard matB tdiag 0 == [[0,0],[1,1],[2,2]]
#guard stdB tdiag && (kindB tdiag == BMS.Kind.lim)
-- 展開は `fsB` を経由せず `BMS.expand` で直接。値は表の値 `oR` そのもの。
#guard (List.range 6).map (fun k => BMS.expand (matB tdiag 0) k)
  == [[[0,0],[1,1]], [[0,0],[1,1],[2,1]], [[0,0],[1,1],[2,1],[3,1]],
      [[0,0],[1,1],[2,1],[3,1],[4,1]], [[0,0],[1,1],[2,1],[3,1],[4,1],[5,1]],
      [[0,0],[1,1],[2,1],[3,1],[4,1],[5,1],[6,1]]]
#guard Trans.Recal.oR (matB tdiag 0) == some (vOf tdiag)
#guard (List.range 6).all fun k =>
  Trans.Recal.oR (BMS.expand (matB tdiag 0) k) == some (vOf (fsB tdiag k))
#guard Test.showRaw (bVal tdiag) == "D_0 D_2 0"
#guard vOf tdiag == psi (Z zero) (Z (phi zero zero))
#guard (List.range 6).map (fun k => matB (fsB tdiag k) 0)
  == [[[0,0],[1,1]], [[0,0],[1,1],[2,1]], [[0,0],[1,1],[2,1],[3,1]],
      [[0,0],[1,1],[2,1],[3,1],[4,1]], [[0,0],[1,1],[2,1],[3,1],[4,1],[5,1]],
      [[0,0],[1,1],[2,1],[3,1],[4,1],[5,1],[6,1]]]
#guard (List.range 6).all fun k => bVal (fsB tdiag k) == BT.D 0 (psiTow (k + 1))
#guard inT sbad
#guard lt sbad (vOf tdiag)
#guard (List.range 40).all fun k => lt (vOf (fsB tdiag k)) sbad
#guard (List.range 40).all fun k => !(le sbad (vOf (fsB tdiag k)))
-- 領域の値の中には隙間に入るものは無い。だから領域だけを掃いても見えない。
#guard (cofFail 12 (limP 3 6) (valP 3 6)).length == 0

/-! **否定 2 — `CofGap` を証明するのに要る閉じた形 (測定のみ)。** ψ₁ の塔の値は
`Ω₁` から始まり、以後は `Ω₁ ⊕ Ω₁` の上の φ̄0 の塔。`ψ₀` を被せると `k ≥ 3` で
`ψ_{Ω₁}(TW k)`。`TW j` はすべて `φ̄(1, Ω₁)` より下 — これが隙間の理由。 -/

#guard dict (psiTow 1) == Z zero
#guard (List.range 8).all fun m => dict (psiTow (m + 2)) == TW (m + 1)
#guard (List.range 6).all fun m => dict (BT.D 0 (psiTow (m + 4))) == psi (Z zero) (TW (m + 3))
#guard (List.range 10).all fun j => vOf (fsB tdiag (j + 3)) == psi (Z zero) (TW (j + 3))
#guard (List.range 12).all fun j => lt (TW j) (phi (phi zero zero) (Z zero))
#guard sbad == psi (Z zero) (phi TM.Term.one (Z zero))

/-! **肯定 1 — 減少と増加。** 五つの母集団で反例 0。`popS 3 6` は `n ≤ 12` まで、
以下は母集団が大きいぶん `n` を落としてある。 -/

#guard (limP 3 6).all fun t => (List.range 13).all fun n => lt (vOf (fsB t n)) (vOf t)
#guard (limP 3 6).all fun t => (List.range 12).all fun n =>
  lt (vOf (fsB t n)) (vOf (fsB t (n + 1)))
#guard (limP 4 6).all fun t => (List.range 7).all fun n => lt (vOf (fsB t n)) (vOf t)
#guard (limP 4 6).all fun t => (List.range 6).all fun n =>
  lt (vOf (fsB t n)) (vOf (fsB t (n + 1)))
#guard (limP 4 7).all fun t => (List.range 5).all fun n => lt (vOf (fsB t n)) (vOf t)
#guard (limP 4 7).all fun t => (List.range 4).all fun n =>
  lt (vOf (fsB t n)) (vOf (fsB t (n + 1)))
#guard (limP 5 6).all fun t => (List.range 5).all fun n => lt (vOf (fsB t n)) (vOf t)
#guard (limP 5 6).all fun t => (List.range 4).all fun n =>
  lt (vOf (fsB t n)) (vOf (fsB t (n + 1)))
-- 表そのもの。877 行列のうち極限は 864 個。
#guard ((popB.filterMap decodeB).filter fun t => kindB t == BMS.Kind.lim).length == 864
#guard ((popB.filterMap decodeB).filter fun t => kindB t == BMS.Kind.lim).all fun t =>
  (List.range 5).all fun n => lt (vOf (fsB t n)) (vOf t)
#guard ((popB.filterMap decodeB).filter fun t => kindB t == BMS.Kind.lim).all fun t =>
  (List.range 4).all fun n => lt (vOf (fsB t n)) (vOf (fsB t (n + 1)))

/-! **肯定 2 — Buchholz 側でも同じ。** `BLimDec`/`BLimInc` の測定。 -/

#guard (limP 3 6).all fun t => (List.range 9).all fun n => BT.lt (bVal (fsB t n)) (bVal t)
#guard (limP 3 6).all fun t => (List.range 8).all fun n =>
  BT.lt (bVal (fsB t n)) (bVal (fsB t (n + 1)))

/-! **肯定 3 — `VOfLtStd`。** `popS 3 6` の 235² = 55225 対で `BT.lt (bVal ·) (bVal ·)` と
`lt (vOf ·) (vOf ·)` は**完全に一致**する (含意ではなく同値で 0 不一致)。 -/

#guard ((popS 3 6).flatMap fun u => (popS 3 6).map fun t =>
  BT.lt (bVal u) (bVal t) == lt (vOf u) (vOf t)).all (fun b => b)

/-! **肯定 4 — 領域の値と、その 1 段の閉包では共終性は通る。** これが「測ってから
信じよ」の一番の実例: 母集団を領域の中に取ると偽の条項が真に見える。 -/

#guard (cofFail 12 (limP 3 6) (valP 3 6)).length == 0
#guard (cofFail 12 (limP 3 6) cloP).length == 0
#guard (cofFail 9 (limP 4 6) (valP 4 6)).length == 0

end

/-! ### §69.6 公理 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

end

/-! ## §68 THE TWO HYPOTHESES OF §67, EACH REDUCED TO ONE LOCAL FACT — NEITHER PROVED

§67 rebuilt `certIn_region`'s second supply on two named, measured, unproved hypotheses —
`PsiIdxOKStd` and `RegionStd` — and §68 was to prove both.  **It proves neither.**  What it
does instead is: replace each by a strictly more local statement and prove the replacement is
enough; kill §67.3's dead route by proving a live one; and pin down, with counterexamples that
are theorems, exactly which hypotheses the two remaining gaps need.  Everything below is
unconditional unless it visibly carries `Ha`/`Hs`.

WHAT IS PROVED, UNCONDITIONALLY.

  §68.1  **THE `BT.lt` ORDER THEORY §67 SAID THE REPOSITORY DID NOT HAVE — ITS FIRST BRICKS.**
         Nothing can be said about `BT.lt` before its fuel is dealt with: `BT.ltL` counts down
         a fuel argument and `BT.lt s t` seeds it with `size s + size t + 2`, so the recursive
         calls are at a DIFFERENT fuel than the one an induction hypothesis offers.
         `ltL_fuel` proves the fuel is irrelevant as soon as it exceeds the component weight
         `sizeLB`, `ltS` fixes it at the weight, and `ltS_cons` is the unfolding equation that
         a proof can actually `rw` with.  `lt_zero_toL` and `lt_D_lvl` are the two facts that
         follow at once: `0` is least, and a strictly smaller subscript decides.

  §68.2  **`RegionStd` IS A STATEMENT ABOUT ONE NODE.**  `regionStd_of_argStd` reduces it to

             ArgStd : ∀ w c, nfLe (w+1) c → nonIncr c → visOK w c c → stdIn c
                             → BT.isStd (BT.D w (bArg w c)) = true

         — no sum, no spine, no `bVal`: one node of level `w` with argument `c`.  The passage
         is `toL_bVal_nd` (the components of `bVal` are exactly the top-level nodes' `bK`s)
         and `stdIn_nd` (each top-level node's argument carries `nonIncr`/`visOK`/`stdIn` for
         free).  `nonIncr t` is NOT used: the region's own descent is not needed for the
         COMPONENTS to be standard, only `nfB` and `stdIn` are.

         **ALL FOUR HYPOTHESES OF `ArgStd` ARE LOAD-BEARING**, and the witnesses are tiny:

             drop `visOK`   c = (0,0)(1,1)        `ψ₀(ψ₀(Ω₁))`             2 nodes
             drop `nonIncr` c = (0,0)(0,1)        `ψ₀(1 ⊕ Ω₁)`             2 nodes
             drop `stdIn`   c = (0,1)(1,1)(2,2)   `ψ₀(ψ₁(ψ₁(Ω₂)))`         3 nodes
             drop `nfLe`    c = (0,2)(1,1)(2,3)   `ψ₀(ψ₂(ψ₁(Ω₃)))`         3 nodes

         (`not_argStd_no_visOK` … `not_argStd_no_nfLe`, all four proved).  So §67's question
         "which one implies which" has an answer: no three of the four suffice.

         **THE CRUX IS AN ORDER TRANSFER, AND IT IS FALSE WITHOUT `stdIn`.**  What `ArgStd`
         needs and does not have is `ArgTransfer`: on trees that are good at level `w`, the
         index-side order `cmpS` and the value-side order `BT.lt` agree through `bArg`.
         Measured it is an order ISOMORPHISM (1 485 370 ordered pairs, zero disagreement).
         Dropping `stdIn` — keeping only `nfLe` — breaks it, and `not_argTransfer_nfLe`
         proves that with the smallest witness, a pair of 4-node arguments

             cT1 = (0,1)(1,2)(1,0)(1,0)   bArg = Ω₂ ⊕ ψ₁(Ω₂ ⊕ 1 ⊕ 1)
             cT2 = (0,1)(1,2)(1,0)(1,2)   bArg = Ω₂ ⊕ ψ₁(Ω₂ ⊕ 1) ⊕ Ω₂

         with `cmpS cT1 cT2 = .lt` and `BT.lt (bArg 0 cT1) (bArg 0 cT2) = false`.

         `toL_bArg` (§68.2c) is the shape the next induction has to run on: `bArg`'s
         component list is the FIRST node's contribution — the only one that can collapse —
         followed by a plain `ψ_u` per remaining node.  That asymmetry is what makes the
         proper-prefix case above appear, and it has no counterpart on the `cmpS` side.

  §68.3  **`PsiIdxOKStd` IS A STATEMENT ABOUT ONE SCAN STEP, AND §67.3'S DEAD ROUTE HAS A LIVE
         REPLACEMENT.**  §67.3 proved `KsetBigOK` — §66.2's sufficient condition — FALSE on the
         region, and told §68 to go at the `K` of the index actually emitted.  `KsetStepOK`
         does exactly that: it asks the `K`-condition only of the two things the emitted index
         is BUILT from, the previous index and the component being consumed, which is what
         `mem_Kset_idxOf` splits it into.  `ksetIdxOK_of_stepOK` needs no induction at all,
         `psiIdxOKStd_of_stepStd` carries it through `dict` (the `inT`/`< M` side conditions
         come along in the same induction, `inT_dict_of_stepStd`), and the region passes:

             region's 1327 `(u, ψ_u b)` pairs   `bigOKb` fails 33   `stepOKb` fails 0

         §67.3's own counterexample `aBig` is repaired (`ksetStepOK_aBig`, proved), and §66.3's
         genuine counterexample `badArg` is still rejected (`not_ksetStepOK_badArg`, proved) —
         so the new condition is not vacuous slack.  Over ALL 3966 `BT` terms of the 3-fold
         closure of `{0}` under `ψ_u` (`u < 4`) and `⊕`, `stepOKb` and `psiIdxOKb` fail at
         `u = 0` on exactly the same 93 terms (`bigOKb` fails on 105): on that population the
         step condition is not merely sufficient, it is equivalent to 2.1(vi)'s decider.
         On the standard side it never fails: 34 551 standard pairs `(u, a)` with subscripts
         up to 7 and `u` up to 8 — so the "sweep to at least `u+2`" rule is met for `u ≤ 5`.

  §68.4  **THE CONSUMER.**  `hsuccS_supply_68` is `certIn_region`'s second supply on the two
         new hypotheses alone.

WHAT IS NOT CLAIMED.  **`Hsucc` IS STILL NOT UNCONDITIONAL.**  Two named facts stand between
`hsuccS_supply_68` and `certIn_region`:

  (S1')  `PsiIdxStepStd` — §68.3's local form of [Rathjen, 1991] 2.1(vi).  Measured: 0 failures
         over every population below.  A proof needs the `K`-sets of `dict`'s image, i.e. the
         transport of Buchholz's `G(a,u) < a` to Rathjen's `K_κ α < α`; nothing here does that.
  (S2')  `ArgStd` — §68.2's one-node form.  A proof needs `ArgTransfer` (§68.2, measured) plus
         the structure of the collapsing head `bClose ∘ bFold`, and `ArgTransfer` itself needs
         `ltS`-analogues of §62's `cmpS_split` / `cmpS_ctx`, which §68.1 does not build.
         The obstruction is identified precisely: on a common prefix `ltS` behaves like `cmpS`,
         but the collapsed head is a LIST, not a single component, so a proper-prefix case
         appears that has no analogue on the index side.

NEITHER IS REFUTED.  Every measurement in §68.5 is consistent with both, over populations of
four different shapes, and the four negative results are all about DROPPING a hypothesis, not
about the hypotheses themselves. -/


/-! ### §68.1 `BT.lt` の燃料を外す

`BT.ltL` は燃料を数えながら降りるので、帰納法の仮説が持つ燃料と再帰呼び出しの燃料が
食い違う。まず「燃料は成分の重み `sizeLB` を超えていれば何でもよい」を示し、燃料を
その重みに固定した `ltS` を作る。`ltS_cons` が `rw` できる展開式である。 -/

section
open TM TM.Term
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (BT)

/-- 成分列の重み。`BT.ltL` の燃料の測度。 -/
def sizeLB : List BT → Nat
  | [] => 0
  | a :: r => a.size + sizeLB r

theorem sizeLB_append : ∀ (l1 l2 : List BT), sizeLB (l1 ++ l2) = sizeLB l1 + sizeLB l2
  | [], l2 => by show sizeLB l2 = 0 + sizeLB l2; omega
  | a :: r, l2 => by
    show a.size + sizeLB (r ++ l2) = (a.size + sizeLB r) + sizeLB l2
    rw [sizeLB_append r l2]; omega

theorem one_le_size : ∀ x : BT, 1 ≤ x.size
  | .zero => Nat.le_refl 1
  | .D _ a => by show 1 ≤ 1 + a.size; omega
  | .sum a b => by show 1 ≤ 1 + a.size + b.size; omega

theorem sizeLB_toL : ∀ x : BT, sizeLB x.toL ≤ x.size
  | .zero => Nat.zero_le _
  | .D _ _ => Nat.le_refl _
  | .sum a b => by
    show sizeLB (a.toL ++ b.toL) ≤ 1 + a.size + b.size
    rw [sizeLB_append]
    have h1 := sizeLB_toL a
    have h2 := sizeLB_toL b
    omega

/-- **燃料は足りてさえいればよい。** -/
theorem ltL_fuel : ∀ (f1 : Nat) (f2 : Nat) (l1 l2 : List BT),
    sizeLB l1 + sizeLB l2 < f1 → sizeLB l1 + sizeLB l2 < f2 →
    BT.ltL f1 l1 l2 = BT.ltL f2 l1 l2 := by
  intro f1
  induction f1 with
  | zero => intro _ l1 l2 h _; exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    intro f2 l1 l2 h1 h2
    cases f2 with
    | zero => exact absurd h2 (Nat.not_lt_zero _)
    | succ k2 =>
      cases l1 with
      | nil => cases l2 with
        | nil => rfl
        | cons y ys => rfl
      | cons x xs => cases l2 with
        | nil => cases x <;> rfl
        | cons y ys =>
          cases x with
          | zero => cases y <;> rfl
          | sum p q => cases y <;> rfl
          | D u a =>
            cases y with
            | zero => rfl
            | sum p q => rfl
            | D v b =>
              have hs1 : 1 ≤ a.size := one_le_size a
              have hs2 : 1 ≤ b.size := one_le_size b
              have t1 := sizeLB_toL a
              have t2 := sizeLB_toL b
              have hsum : sizeLB ((BT.D u a) :: xs) + sizeLB ((BT.D v b) :: ys)
                  = (1 + a.size + sizeLB xs) + (1 + b.size + sizeLB ys) := by
                show ((1 + a.size) + sizeLB xs) + ((1 + b.size) + sizeLB ys) = _
                omega
              show (if u < v then true else if v < u then false
                    else if a == b then BT.ltL k xs ys else BT.ltL k a.toL b.toL)
                = (if u < v then true else if v < u then false
                    else if a == b then BT.ltL k2 xs ys else BT.ltL k2 a.toL b.toL)
              by_cases h3 : u < v
              · rw [if_pos h3, if_pos h3]
              · rw [if_neg h3, if_neg h3]
                by_cases h4 : v < u
                · rw [if_pos h4, if_pos h4]
                · rw [if_neg h4, if_neg h4]
                  by_cases h5 : (a == b) = true
                  · rw [if_pos h5, if_pos h5]
                    exact ih k2 xs ys (by omega) (by omega)
                  · rw [if_neg h5, if_neg h5]
                    exact ih k2 a.toL b.toL (by omega) (by omega)

/-- 燃料を重みに固定した比較。 -/
def ltS (l1 l2 : List BT) : Bool := BT.ltL (sizeLB l1 + sizeLB l2 + 1) l1 l2

theorem lt_eq_ltS (s t : BT) : BT.lt s t = ltS s.toL t.toL := by
  have h1 := sizeLB_toL s
  have h2 := sizeLB_toL t
  exact ltL_fuel (s.size + t.size + 2) (sizeLB s.toL + sizeLB t.toL + 1) s.toL t.toL
    (by omega) (by omega)

theorem ltS_nil_nil : ltS [] [] = false := rfl
theorem ltS_nil_cons (y : BT) (ys : List BT) : ltS [] (y :: ys) = true := rfl

theorem ltS_cons_nil (x : BT) (xs : List BT) : ltS (x :: xs) [] = false := by
  show BT.ltL (sizeLB (x :: xs) + sizeLB [] + 1) (x :: xs) [] = false
  cases h : sizeLB (x :: xs) + sizeLB [] + 1 with
  | zero => rfl
  | succ k => cases x <;> rfl

/-- **展開式。** 段が決め、同段なら引数、引数が同じなら後続。 -/
theorem ltS_cons (u : Nat) (a : BT) (xs : List BT) (v : Nat) (b : BT) (ys : List BT) :
    ltS (BT.D u a :: xs) (BT.D v b :: ys)
      = (if u < v then true else if v < u then false
         else if a == b then ltS xs ys else ltS a.toL b.toL) := by
  have hs1 : 1 ≤ a.size := one_le_size a
  have hs2 : 1 ≤ b.size := one_le_size b
  have t1 := sizeLB_toL a
  have t2 := sizeLB_toL b
  have hsum : sizeLB (BT.D u a :: xs) + sizeLB (BT.D v b :: ys)
      = (1 + a.size + sizeLB xs) + (1 + b.size + sizeLB ys) := by
    show ((1 + a.size) + sizeLB xs) + ((1 + b.size) + sizeLB ys) = _
    omega
  show BT.ltL ((sizeLB (BT.D u a :: xs) + sizeLB (BT.D v b :: ys)) + 1) _ _ = _
  rw [show (sizeLB (BT.D u a :: xs) + sizeLB (BT.D v b :: ys)) + 1
        = ((1 + a.size + sizeLB xs) + (1 + b.size + sizeLB ys)) + 1 from by rw [hsum]]
  show (if u < v then true else if v < u then false
        else if a == b then BT.ltL ((1 + a.size + sizeLB xs) + (1 + b.size + sizeLB ys)) xs ys
        else BT.ltL ((1 + a.size + sizeLB xs) + (1 + b.size + sizeLB ys)) a.toL b.toL) = _
  by_cases h3 : u < v
  · rw [if_pos h3, if_pos h3]
  · rw [if_neg h3, if_neg h3]
    by_cases h4 : v < u
    · rw [if_pos h4, if_pos h4]
    · rw [if_neg h4, if_neg h4]
      by_cases h5 : (a == b) = true
      · rw [if_pos h5, if_pos h5]
        exact ltL_fuel _ _ xs ys (by omega) (by omega)
      · rw [if_neg h5, if_neg h5]
        exact ltL_fuel _ _ a.toL b.toL (by omega) (by omega)

/-- `0` は最小。 -/
theorem lt_zero_toL (x : BT) (h : x.toL ≠ []) : BT.lt BT.zero x = true := by
  rw [lt_eq_ltS]
  cases hx : x.toL with
  | nil => exact absurd hx h
  | cons y ys => exact ltS_nil_cons y ys

/-- 段が小さければそれで決まる。 -/
theorem lt_D_lvl (u v : Nat) (a b : BT) (h : u < v) :
    BT.lt (BT.D u a) (BT.D v b) = true := by
  rw [lt_eq_ltS]
  show ltS (BT.D u a :: []) (BT.D v b :: []) = true
  rw [ltS_cons, if_pos h]

end

/-! ### §68.2 `RegionStd` は一つの節の話

`bVal` の成分は最上位の節の寄与そのもので、`stdIn` は各節の引数に `nonIncr`・`visOK`・
`stdIn` をただで渡す。だから `RegionStd` は「一つの節の寄与が Buchholz 標準」に落ちる。
落ちた先 `ArgStd` は**証明しない**。四つの仮説がどれも外せないことだけを示す。 -/

section
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (BT)
open TM TM.Term

/-- 段 `w` の節の引数として「良い」こと。 -/
def goodAt (w : Nat) (c : B) : Bool :=
  nfLe (w+1) c && nonIncr c && visOK w c c && stdIn c

/-- **一つの節の条件。** `RegionStd` はこれに落ちる (`regionStd_of_argStd`)。**未証明。** -/
def ArgStd : Prop := ∀ (w : Nat) (c : B),
  nfLe (w+1) c = true → nonIncr c = true → visOK w c c = true → stdIn c = true →
  BT.isStd (BT.D w (bArg w c)) = true

/-- **その核。** 添字の側の順序 `cmpS` は `bArg` を通って値の側の順序になる。**未証明。** -/
def ArgTransfer : Prop := ∀ (w : Nat) (c1 c2 : B),
  goodAt w c1 = true → goodAt w c2 = true →
  cmpS (toL c1) (toL c2) = Ordering.lt → BT.lt (bArg w c1) (bArg w c2) = true

theorem stdIn_nd {v : Nat} {r c : B} (h : stdIn (.nd v r c) = true) :
    stdIn r = true ∧ nonIncr c = true ∧ visOK v c c = true ∧ stdIn c = true := by
  have h' : ((stdIn r && nonIncr c && visOK v c c) && stdIn c) = true := h
  obtain ⟨h1, h4⟩ := (Bool.and_eq_true _ _).mp h'
  obtain ⟨h2, h3⟩ := (Bool.and_eq_true _ _).mp h1
  obtain ⟨hr, hn⟩ := (Bool.and_eq_true _ _).mp h2
  exact ⟨hr, hn, h3, h4⟩

/-- **`bVal` の成分は最上位の節の寄与そのもの。** -/
theorem toL_bVal_nd (v : Nat) (r c : B) :
    (bVal (.nd v r c)).toL = (bVal r).toL ++
      (if (r == .nil && v == 0 && c == .nil) = true then ([] : List BT)
       else [BT.D v (bArg v c)]) := by
  have hX : AtomsL (if (r == .nil && v == 0 && c == .nil) = true then BT.zero
      else BT.D v (bArg v c)) := by
    by_cases hc : (r == .nil && v == 0 && c == .nil) = true
    · rw [if_pos hc]; exact atomsL_zero
    · rw [if_neg hc]; exact atomsL_D _ _
  show (bplus (bVal r) (if (r == .nil && v == 0 && c == .nil) = true then BT.zero
      else BT.D v (bArg v c))).toL = _
  rw [toL_bplus _ _ (atomsL_bVal r) hX]
  by_cases hc : (r == .nil && v == 0 && c == .nil) = true
  · rw [if_pos hc, if_pos hc]; rfl
  · rw [if_neg hc, if_neg hc]; rfl

theorem regionStd_aux (H : ArgStd) : ∀ (t : B), nfB t = true → stdIn t = true →
    ∀ a ∈ (bVal t).toL, BT.isStd a = true := by
  intro t
  induction t with
  | nil => intro _ _ a ha; cases ha
  | nd v r c ihr _ =>
    intro hnf hst a ha
    obtain ⟨_, hnfr, hnfc⟩ := (nfLe_nd_iff 0 v r c).mp hnf
    obtain ⟨hstr, hnc, hvis, hstc⟩ := stdIn_nd hst
    rw [toL_bVal_nd v r c] at ha
    rcases List.mem_append.mp ha with h | h
    · exact ihr hnfr hstr a h
    · by_cases hc : (r == .nil && v == 0 && c == .nil) = true
      · rw [if_pos hc] at h; cases h
      · rw [if_neg hc, List.mem_singleton] at h
        rw [h]
        exact H v c hnfc hnc hvis hstc

/-- **§68.2 の主定理。** `RegionStd` は一つの節の条件に落ちる。`nonIncr t` は要らない。 -/
theorem regionStd_of_argStd (H : ArgStd) : RegionStd := by
  intro t ht a ha
  have h' : ((nfB t && nonIncr t) && stdIn t) = true := ht
  obtain ⟨h1, h3⟩ := (Bool.and_eq_true _ _).mp h'
  obtain ⟨h2, _⟩ := (Bool.and_eq_true _ _).mp h1
  exact regionStd_aux H t h2 h3 a ha

end

/-! ### §68.2b 四つの仮説はどれも外せない

`ArgStd` の連言から一つずつ外して、最小の反例を挙げる。どれも 2 節か 3 節である。 -/

section
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (BT)
open TM TM.Term

/-- `visOK` を外す反例。行列 `(0,0)(1,1)`、値 `ψ₀(ψ₀(Ω₁))`。 -/
def cVis : B := .nd 0 .nil (.nd 1 .nil .nil)
/-- `nonIncr` を外す反例。行列 `(0,0)(0,1)`、値 `ψ₀(1 ⊕ Ω₁)`。 -/
def cInc : B := .nd 1 (.nd 0 .nil .nil) .nil
/-- `stdIn` を外す反例。行列 `(0,1)(1,1)(2,2)`、値 `ψ₀(ψ₁(ψ₁(Ω₂)))`。 -/
def cStd : B := .nd 1 .nil (.nd 1 .nil (.nd 2 .nil .nil))
/-- `nfLe` を外す反例。行列 `(0,2)(1,1)(2,3)`、値 `ψ₀(ψ₂(ψ₁(Ω₃)))`。 -/
def cNf : B := .nd 2 .nil (.nd 1 .nil (.nd 3 .nil .nil))

theorem not_argStd_no_visOK :
    ¬ (∀ (w : Nat) (c : B), nfLe (w+1) c = true → nonIncr c = true → stdIn c = true →
        BT.isStd (BT.D w (bArg w c)) = true) := fun H =>
  Bool.noConfusion ((H 0 cVis rfl rfl rfl).symm.trans
    (show BT.isStd (BT.D 0 (bArg 0 cVis)) = false from rfl))

/-- `cInc` の中の段 0 の節の引数は空和で、`cInc` より真に小さい。 -/
theorem cmpS_nil_cInc : (cmpS (toL (B.nil)) (toL cInc) == Ordering.lt) = true := by
  show (cmpS [] [((0 : Nat), (B.nil)), ((1 : Nat), (B.nil))] == Ordering.lt) = true
  rw [cmpS_nil_cons]
  rfl

/-- `visOK` は `cmpS` を含むので `rfl` では出ない。値は §62 の展開式から。 -/
theorem visOK_cInc : visOK 0 cInc cInc = true := by
  show ((true && ((cmpS (toL (B.nil)) (toL cInc) == Ordering.lt) && true))
        && (true && true)) = true
  rw [cmpS_nil_cInc]
  rfl

theorem not_argStd_no_nonIncr :
    ¬ (∀ (w : Nat) (c : B), nfLe (w+1) c = true → visOK w c c = true → stdIn c = true →
        BT.isStd (BT.D w (bArg w c)) = true) := fun H =>
  Bool.noConfusion ((H 0 cInc rfl visOK_cInc rfl).symm.trans
    (show BT.isStd (BT.D 0 (bArg 0 cInc)) = false from rfl))

theorem not_argStd_no_stdIn :
    ¬ (∀ (w : Nat) (c : B), nfLe (w+1) c = true → nonIncr c = true → visOK w c c = true →
        BT.isStd (BT.D w (bArg w c)) = true) := fun H =>
  Bool.noConfusion ((H 0 cStd rfl rfl rfl).symm.trans
    (show BT.isStd (BT.D 0 (bArg 0 cStd)) = false from rfl))

theorem not_argStd_no_nfLe :
    ¬ (∀ (w : Nat) (c : B), nonIncr c = true → visOK w c c = true → stdIn c = true →
        BT.isStd (BT.D w (bArg w c)) = true) := fun H =>
  Bool.noConfusion ((H 0 cNf rfl rfl rfl).symm.trans
    (show BT.isStd (BT.D 0 (bArg 0 cNf)) = false from rfl))

/-- 移送の反例、小さい方。四つの条件をすべて満たす。 -/
def cT1 : B := .nd 1 .nil (.nd 0 (.nd 0 (.nd 2 .nil .nil) .nil) .nil)
/-- 移送の反例、大きい方。子の並び `(2)(0)(2)` が降べきでないので `stdIn` だけが落ちる。 -/
def cT2 : B := .nd 1 .nil (.nd 2 (.nd 0 (.nd 2 .nil .nil) .nil) .nil)

theorem cmpS_cT1_cT2 : cmpS (toL cT1) (toL cT2) = Ordering.lt := by
  have h3 : cmpS [((0 : Nat), (B.nil))] [((2 : Nat), (B.nil))] = Ordering.lt := by
    rw [cmpS_cons, if_pos (by omega)]
  have h2 : cmpS [((0 : Nat), (B.nil)), ((0 : Nat), (B.nil))]
      [((0 : Nat), (B.nil)), ((2 : Nat), (B.nil))] = Ordering.lt := by
    rw [cmpS_cons, if_neg (by omega), if_neg (by omega),
      show cmpS (toL (B.nil)) (toL (B.nil)) = Ordering.eq from cmpS_nil_nil]
    exact h3
  have h1 : cmpS [((2 : Nat), (B.nil)), ((0 : Nat), (B.nil)), ((0 : Nat), (B.nil))]
      [((2 : Nat), (B.nil)), ((0 : Nat), (B.nil)), ((2 : Nat), (B.nil))] = Ordering.lt := by
    rw [cmpS_cons, if_neg (by omega), if_neg (by omega),
      show cmpS (toL (B.nil)) (toL (B.nil)) = Ordering.eq from cmpS_nil_nil]
    exact h2
  show cmpS [((1 : Nat), (B.nd 0 (B.nd 0 (B.nd 2 .nil .nil) .nil) .nil))]
      [((1 : Nat), (B.nd 2 (B.nd 0 (B.nd 2 .nil .nil) .nil) .nil))] = Ordering.lt
  rw [cmpS_cons, if_neg (by omega), if_neg (by omega),
    show cmpS (toL (B.nd 0 (B.nd 0 (B.nd 2 .nil .nil) .nil) .nil))
        (toL (B.nd 2 (B.nd 0 (B.nd 2 .nil .nil) .nil) .nil)) = Ordering.lt from h1]

/-- **移送は `nfLe` だけでは成り立たない。** 最小の反例は 4 節どうし。 -/
theorem not_argTransfer_nfLe :
    ¬ (∀ (w : Nat) (c1 c2 : B), nfLe (w+1) c1 = true → nfLe (w+1) c2 = true →
        cmpS (toL c1) (toL c2) = Ordering.lt → BT.lt (bArg w c1) (bArg w c2) = true) :=
  fun H => Bool.noConfusion ((H 0 cT1 cT2 rfl rfl cmpS_cT1_cT2).symm.trans
    (show BT.lt (bArg 0 cT1) (bArg 0 cT2) = false from rfl))

end

/-! ### §68.2c `bArg` の成分列 — 次の帰納法が回る形

`ArgTransfer` を証明するには `bArg` を成分列として見る必要がある。潰れるのは**先頭の
節だけ**で、残りはそのまま `ψ_u` になる — それが `toL_bArg` である。`argL` の第一項が
`bK w u .nil a` (潰れうる) で第二項が `map` (潰れない) という非対称が、`cmpS` 側には無い
「真の接頭辞」の場合を作る。§69 が塞ぐべき穴はそこにある。 -/

section
open TM TM.Term
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (BT)

/-- 成分列の側から見た `bArg`。先頭の節だけが潰れうる。 -/
def argL (w : Nat) : List (Nat × B) → List BT
  | [] => []
  | (u, a) :: rest => (bK w u .nil a).toL ++ rest.map (fun q => BT.D q.1 (bArg q.1 q.2))

/-- **先頭でない節の寄与は必ず `ψ_u`。** 潰れるのは先頭だけ。 -/
theorem bK_tail (w u : Nat) (r c : B) (hr : r ≠ .nil) : bK w u r c = BT.D u (bArg u c) := by
  cases r with
  | nil => exact absurd rfl hr
  | nd v r' c' =>
    show (if (c == .nil) = true then (BT.D u BT.zero)
          else if (decide (u ≤ w) || !(B.nd v r' c' == .nil) || decide (headLvl c ≤ u)) = true
               then BT.D u (bArg u c) else bClose u (bFold u c)) = _
    by_cases hc : (c == .nil) = true
    · rw [if_pos hc, show c = .nil from of_decide_eq_true hc]
      rfl
    · rw [if_neg hc, if_pos ?_]
      show (decide (u ≤ w) || !(B.nd v r' c' == .nil) || decide (headLvl c ≤ u)) = true
      rw [show (!(B.nd v r' c' == B.nil)) = true from rfl, Bool.or_true]
      rfl

theorem argL_snoc (w : Nat) : ∀ (l : List (Nat × B)) (x : Nat × B), l ≠ [] →
    argL w (l ++ [x]) = argL w l ++ [BT.D x.1 (bArg x.1 x.2)]
  | [], _, h => absurd rfl h
  | (u, a) :: rest, x, _ => by
    show (bK w u .nil a).toL ++ (rest ++ [x]).map (fun q => BT.D q.1 (bArg q.1 q.2))
      = ((bK w u .nil a).toL ++ rest.map (fun q => BT.D q.1 (bArg q.1 q.2)))
          ++ [BT.D x.1 (bArg x.1 x.2)]
    rw [List.map_append, List.append_assoc]
    rfl

/-- **`bArg` の成分列。** 先頭の節の寄与 (潰れうる) に、残りの節の `ψ_u` を並べたもの。 -/
theorem toL_bArg (w : Nat) : ∀ (c : B), (bArg w c).toL = argL w (toL c)
  | .nil => rfl
  | .nd u r a => by
    rw [show bArg w (.nd u r a) = bplus (bArg w r) (bK w u r a) from rfl,
      toL_bplus _ _ (atomsL_bArg_bFold r w).1 (atomsL_bK w u r a), toL_nd]
    cases hr : r with
    | nil =>
      rw [show toL (B.nil) = ([] : List (Nat × B)) from rfl, List.nil_append]
      show (bArg w B.nil).toL ++ (bK w u B.nil a).toL = (bK w u .nil a).toL ++ [].map _
      rw [show (bArg w B.nil).toL = ([] : List BT) from rfl,
        show ((bK w u B.nil a).toL ++ ([] : List (Nat × B)).map
          (fun q => BT.D q.1 (bArg q.1 q.2))) = (bK w u B.nil a).toL from List.append_nil _]
      exact List.nil_append _
    | nd v r' c' =>
      rw [argL_snoc w (toL (B.nd v r' c')) (u, a) (toL_ne_nil v r' c'),
        ← toL_bArg w (B.nd v r' c'),
        bK_tail w u (B.nd v r' c') a (by intro h; exact B.noConfusion h)]
      rfl

end

/-! ### §68.3 `PsiIdxOKStd` は一歩の話

`mem_Kset_idxOf` は「吐かれた指数の `K`」を「直前の指数の `K`」と「今の成分の `K`」に
分ける。分けた先だけを条件にしたものが `KsetStepOK` で、`KsetIdxOK` はそこから帰納法
なしで出る。§66.2 の `bigPart` と違い、まだ消費していない成分を見ないので領域に届く。 -/

section
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **一歩ぶんの条件。** 吐かれた指数を作る材料 — 直前の指数と今の成分 — の `K` が、
    その指数より小さいこと。 -/
def KsetStepOK (u : Nat) (x : Term) : Prop :=
  ∀ p ∈ scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1,
    le (reg (u+1)) p.2.1 = true →
      (∀ i0, p.1.1 = some i0 → ∀ y ∈ Kset (reg (u+1)) i0,
          lt y (idxOf (reg (u+1)) p.1 p.2) = true) ∧
      (∀ y, (y ∈ Kset (reg (u+1)) p.2.1 ∨ y ∈ Kset (reg (u+1)) p.2.2) →
          lt y (idxOf (reg (u+1)) p.1 p.2) = true)

/-- **§68.3 の主定理。** 一歩ぶんの条件から 2.1(vi) の `K` の連言が出る。帰納法は要らない。 -/
theorem ksetIdxOK_of_stepOK (u : Nat) (x : Term) (H : KsetStepOK u x) : KsetIdxOK u x := by
  intro p hp hle
  rw [List.all_eq_true]
  intro y hy
  rcases mem_Kset_idxOf (fun z hz => mem_Kset_reg (u+1) hz) hy with h1 | h1
  · obtain ⟨i0, hi0, hy0⟩ := h1
    exact (H p hp hle).1 i0 hi0 y hy0
  · exact (H p hp hle).2 y h1

theorem psiIdxOK_of_stepOK (u : Nat) (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (H : KsetStepOK u x) : PsiIdxOK u x :=
  psiIdxOK_of_ksetIdxOK u x hx hlx (ksetIdxOK_of_stepOK u x H)

/-- **候補 3。** `PsiIdxOKStd` の一歩ぶんの形。**未証明。** -/
def PsiIdxStepStd : Prop :=
  ∀ (u : Nat) (a : BT), BT.isStd (BT.D u a) = true → KsetStepOK u (dict a)

theorem inT_dict_of_stepStd (H : PsiIdxStepStd) : ∀ a : BT, BT.isStd a = true →
    inT (dict a) = true ∧ lt (dict a) M = true
  | .zero => fun _ => ⟨inT_zero, lt_zero_M⟩
  | .D u a => fun h => by
    have ih := inT_dict_of_stepStd H a (isStd_of_D h)
    exact inT_collapse_gap3 u (dict a) ih.1 ih.2
      (psiIdxOK_of_stepOK u (dict a) ih.1 ih.2 (H u a h))
  | .sum a b => fun h => by
    have iha := inT_dict_of_stepStd H a (isStd_of_sum h).1
    have ihb := inT_dict_of_stepStd H b (isStd_of_sum h).2
    exact ⟨inT_plus iha.1 ihb.1, lt_plus_M iha.1 ihb.1 iha.2 ihb.2⟩

/-- **一歩ぶんの条件から §66.4 の候補が出る。** -/
theorem psiIdxOKStd_of_stepStd (H : PsiIdxStepStd) : PsiIdxOKStd := by
  intro u a h
  have ih := inT_dict_of_stepStd H a (isStd_of_D h)
  exact psiIdxOK_of_stepOK u (dict a) ih.1 ih.2 (H u a h)

/-- 一歩ぶんの条件の判定器。 -/
def stepOKb (u : Nat) (x : Term) : Bool :=
  (scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1).all fun p =>
    !(le (reg (u+1)) p.2.1) ||
      (((match p.1.1 with
         | none => ([] : List Term)
         | some i0 => Kset (reg (u+1)) i0) ++
        Kset (reg (u+1)) p.2.1 ++ Kset (reg (u+1)) p.2.2).all
          (fun y => lt y (idxOf (reg (u+1)) p.1 p.2)))

theorem ksetStepOK_of_b {u : Nat} {x : Term} (h : stepOKb u x = true) : KsetStepOK u x := by
  intro p hp hle
  have h1 := List.all_eq_true.mp h p hp
  rw [hle, Bool.not_true, Bool.false_or] at h1
  have h2 := List.all_eq_true.mp h1
  constructor
  · intro i0 hi0 y hy
    refine h2 y (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ?_))))
    rw [hi0]; exact hy
  · intro y hy
    rcases hy with hy | hy
    · exact h2 y (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hy))))
    · exact h2 y (List.mem_append.mpr (Or.inr hy))

theorem stepOKb_of_ksetStepOK {u : Nat} {x : Term} (H : KsetStepOK u x) : stepOKb u x = true := by
  show ((scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1).all fun p =>
    !(le (reg (u+1)) p.2.1) ||
      (((match p.1.1 with
         | none => ([] : List Term)
         | some i0 => Kset (reg (u+1)) i0) ++
        Kset (reg (u+1)) p.2.1 ++ Kset (reg (u+1)) p.2.2).all
          (fun y => lt y (idxOf (reg (u+1)) p.1 p.2)))) = true
  rw [List.all_eq_true]
  intro p hp
  cases hle : le (reg (u+1)) p.2.1 with
  | false => rfl
  | true =>
    rw [Bool.not_true, Bool.false_or, List.all_eq_true]
    intro y hy
    rcases List.mem_append.mp hy with h1 | h1
    · rcases List.mem_append.mp h1 with h2 | h2
      · cases hq : p.1.1 with
        | none => rw [hq] at h2; cases h2
        | some i0 => exact (H p hp hle).1 i0 hq y (by rw [hq] at h2; exact h2)
      · exact (H p hp hle).2 y (Or.inl h2)
    · exact (H p hp hle).2 y (Or.inr h1)

/-- **§67.3 の反例は直る。** `KsetBigOK` が落ちた `aBig` で、一歩ぶんの条件は成り立つ。 -/
theorem ksetStepOK_aBig : KsetStepOK 0 (dict aBig) :=
  ksetStepOK_of_b (show stepOKb 0 (dict aBig) = true from rfl)

/-- **§66.3 の反例は落ちたまま。** 条件は空回りしていない。 -/
theorem not_ksetStepOK_badArg : ¬ KsetStepOK 0 (dict badArg) := fun H =>
  Bool.noConfusion ((stepOKb_of_ksetStepOK H).symm.trans
    (show stepOKb 0 (dict badArg) = false from rfl))

end

/-! ### §68.4 消費者

§67.4 の `hsuccS_supply_std` に、§68.2 と §68.3 の還元を差し込むだけ。 -/

section
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

/-- 領域の値は 𝔗(M) の項 — 二つの局所仮説の上で。 -/
theorem inT_vOf_68 (Ha : ArgStd) (Hs : PsiIdxStepStd) (t : B) (ht : stdB t = true) :
    inT (vOf t) = true :=
  inT_vOf_std (psiIdxOKStd_of_stepStd Hs) (regionStd_of_argStd Ha) t ht

/-- **`certIn_region` の `Hsucc` 供給。** `ArgStd` と `PsiIdxStepStd` の上で。
    **まだ無条件ではない。** -/
theorem hsuccS_supply_68 (Ha : ArgStd) (Hs : PsiIdxStepStd) :
    ∀ (S : BMS.Matrix) (v : TM.Term), RegS S → ValS S v → BMS.kind S = BMS.Kind.succ →
    ∃ u, v = plus u TM.Term.one ∧ inT v = true ∧ inT u = true ∧ lt u v = true
         ∧ ∀ n, ValS (BMS.expand S n) u :=
  hsuccS_supply_std (psiIdxOKStd_of_stepStd Hs) (regionStd_of_argStd Ha)

end

/-! ### §68.5 測定 (凍結)

母集団の作り方を先に書く。

    popNF68 L n := ((List.range n).flatMap (enumNodes L)).filter (nfB · && · != nil)
    popSt68 L n := (popNF68 L n).filter stdB          -- 節 0..n-1、段 0..L-1
    pool68  L n := (List.range n).flatMap (enumNodes L)   -- 標準形とは限らない木
    goods   w L n := (pool68 L n).filter (goodAt w)
    expPop  := popSt68 4 7 の各元を基本列で 2 回展開したもの (節は最大 36)
    sclos k n := `{0}` を `ψ_u` (`u < k`) と `⊕` で n 回閉じ、各段で `BT.isStd` に絞ったもの
                 (部分項は標準なので、これで深さ n の標準項をすべて得る)
    small68 := `{0}` を `ψ_u` (`u < 4`) と `⊕` で 3 回閉じた **全部** (絞らない)

`pairs68 l` は `l` の `bVal` の成分の中に現れる `ψ_u b` を対 `(u, b)` として全部集める。
量化子はそれぞれ「実際に量化されている形」の上で走らせてある — 木の対は木の対の上で、
`(u, a)` の対は `(u, a)` の対の上で。段は `u+2` 以上まで振ってある (§66 の教訓)。 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse dict)
open Trans.Dict (BT)
open TM TM.Term
open Evidence.WF

private def popNF68 (L n : Nat) : List B :=
  ((List.range n).flatMap (enumNodes L)).filter fun t => nfB t && t != .nil
private def popSt68 (L n : Nat) : List B := (popNF68 L n).filter stdB
private def pool68 (L n : Nat) : List B := (List.range n).flatMap (enumNodes L)
private def goods (w L n : Nat) : List B := (pool68 L n).filter (goodAt w)
private def expPop : List B :=
  ((popSt68 4 7).flatMap fun t =>
    (List.range 3).flatMap fun n => (List.range 3).map fun m => fsB (fsB t n) m).eraseDups
private def pairsOf68 : BT → List (Nat × BT)
  | .zero => []
  | .D u a => (u, a) :: pairsOf68 a
  | .sum a b => pairsOf68 a ++ pairsOf68 b
private def pairs68 (l : List B) : List (Nat × BT) :=
  (l.flatMap fun t => (bVal t).toL.flatMap pairsOf68).eraseDups
private def sstep (k : Nat) (l : List BT) : List BT :=
  (l ++ ((List.range k).flatMap fun u => l.map fun a => BT.D u a)
     ++ (l.flatMap fun a => l.map fun b => BT.sum a b)).eraseDups.filter BT.isStd
private def sclos (k : Nat) : Nat → List BT
  | 0 => [BT.zero]
  | n+1 => sstep k (sclos k n)
private def allBT68 : Nat → Nat → List BT
  | 0, _ => [.zero]
  | n+1, k =>
    let sub := (allBT68 n k).eraseDups
    (sub ++ ((List.range k).flatMap fun u => sub.map fun a => BT.D u a)
        ++ (sub.flatMap fun a => sub.map fun b => BT.sum a b)).eraseDups
private def small68 : List BT := allBT68 3 4

-- 母集団の大きさ。
#guard (popSt68 4 7).length == 1263
#guard (popSt68 4 8).length == 6933
#guard (popSt68 5 7).length == 1284
#guard (popSt68 5 8).length == 7227
#guard (popSt68 6 7).length == 1285
#guard expPop.length == 5794
#guard (expPop.map sizeB).foldl max 0 == 36
#guard (goods 0 4 5).length == 177
#guard (goods 1 4 5).length == 485
#guard (goods 2 5 5).length == 1104
#guard (sclos 4 3).length == 425
#guard (sclos 6 3).length == 1645
#guard (sclos 8 3).length == 4497
#guard small68.length == 3966

/-! **否定 1 — `ArgStd` の四つの仮説はどれも外せない。** 反例は 2 節・2 節・3 節・3 節。 -/

#guard matB cVis 0 == [[0, 0], [1, 1]]
#guard matB cInc 0 == [[0, 0], [0, 1]]
#guard matB cStd 0 == [[0, 1], [1, 1], [2, 2]]
#guard matB cNf 0 == [[0, 2], [1, 1], [2, 3]]
#guard nfLe 1 cVis && nonIncr cVis && stdIn cVis && !(visOK 0 cVis cVis)
#guard nfLe 1 cInc && visOK 0 cInc cInc && stdIn cInc && !(nonIncr cInc)
#guard nfLe 1 cStd && nonIncr cStd && visOK 0 cStd cStd && !(stdIn cStd)
#guard nonIncr cNf && visOK 0 cNf cNf && stdIn cNf && !(nfLe 1 cNf)
#guard !(BT.isStd (BT.D 0 (bArg 0 cVis)))
#guard !(BT.isStd (BT.D 0 (bArg 0 cInc)))
#guard !(BT.isStd (BT.D 0 (bArg 0 cStd)))
#guard !(BT.isStd (BT.D 0 (bArg 0 cNf)))
#guard Trans.Recal.Test.showRaw (BT.D 0 (bArg 0 cVis)) == "D_0 D_0 D_1 0"
#guard Trans.Recal.Test.showRaw (BT.D 0 (bArg 0 cInc)) == "D_0 (D_0 0,D_1 0)"
#guard Trans.Recal.Test.showRaw (BT.D 0 (bArg 0 cStd)) == "D_0 D_1 D_1 D_2 0"
#guard Trans.Recal.Test.showRaw (BT.D 0 (bArg 0 cNf)) == "D_0 D_2 D_1 D_3 0"
--   節 ≤ 5・段 < 4 の母集団で、外した連言ごとの反例の個数と最小の節数。
#guard ((pool68 4 6).filter fun c =>
  nfLe 1 c && nonIncr c && stdIn c && !(BT.isStd (BT.D 0 (bArg 0 c)))).length == 275
#guard (((pool68 4 6).filter fun c =>
  nfLe 1 c && nonIncr c && stdIn c && !(BT.isStd (BT.D 0 (bArg 0 c)))).map sizeB).foldl min 99 == 2
#guard (((pool68 4 6).filter fun c =>
  nfLe 1 c && visOK 0 c c && stdIn c && !(BT.isStd (BT.D 0 (bArg 0 c)))).map sizeB).foldl min 99 == 2
#guard (((pool68 4 6).filter fun c =>
  nfLe 1 c && nonIncr c && visOK 0 c c && !(BT.isStd (BT.D 0 (bArg 0 c)))).map sizeB).foldl min 99 == 3
#guard (((pool68 4 6).filter fun c =>
  nonIncr c && visOK 0 c c && stdIn c && !(BT.isStd (BT.D 0 (bArg 0 c)))).map sizeB).foldl min 99 == 3

/-! **否定 2 — 移送は `nfLe` だけでは落ちる。** 節 ≤ 4・段 < 4 の `nfLe` な木 468 個の
219 024 対のうち 8 対で `cmpS` と `BT.lt` が食い違う。最小は 4 節どうしの `cT1`/`cT2`。 -/

#guard matB cT1 0 == [[0, 1], [1, 2], [1, 0], [1, 0]]
#guard matB cT2 0 == [[0, 1], [1, 2], [1, 0], [1, 2]]
#guard nfLe 1 cT1 && nonIncr cT1 && visOK 0 cT1 cT1 && stdIn cT1
#guard nfLe 1 cT2 && nonIncr cT2 && visOK 0 cT2 cT2 && !(stdIn cT2)
#guard cmpS (toL cT1) (toL cT2) == Ordering.lt
#guard !(BT.lt (bArg 0 cT1) (bArg 0 cT2))
#guard Trans.Recal.Test.showRaw (bArg 0 cT1) == "(D_2 0,D_1 (D_2 0,D_0 0,D_0 0))"
#guard Trans.Recal.Test.showRaw (bArg 0 cT2) == "(D_2 0,D_1 (D_2 0,D_0 0),D_2 0)"
#guard ((pool68 4 5).filter (nfLe 1)).length == 468
#guard ((pool68 4 5).flatMap fun c1 => (pool68 4 5).filter fun c2 =>
  nfLe 1 c1 && nfLe 1 c2 &&
    ((cmpS (toL c1) (toL c2) == Ordering.lt) != BT.lt (bArg 0 c1) (bArg 0 c2))).length == 8

/-! **否定 3 — 一歩ぶんの条件は空回りではない。** §66.3 の反例では落ちる。
`small68` の 3966 項のうち `psiIdxOKb` が落ちるのは 93 項で、`stepOKb` が落ちるのも同じ
93 項 — この母集団では一歩ぶんの条件は 2.1(vi) の判定器と**一致する**。
§66.2 の `bigOKb` はもっと多く落ちる (105 項)。 -/

#guard !(stepOKb 0 (dict badArg))
#guard !(psiIdxOKb 0 (dict badArg))
#guard (small68.filter fun a => !(psiIdxOKb 0 (dict a))).length == 93
#guard (small68.filter fun a => !(stepOKb 0 (dict a))).length == 93
#guard (small68.filter fun a => psiIdxOKb 0 (dict a) && !(stepOKb 0 (dict a))).length == 0
#guard (small68.filter fun a => !(bigOKb 0 (dict a))).length == 105

/-! **肯定 1 — §67.3 の穴は塞がる。** 領域の 1327 対で `bigOKb` は 33 個落ち、
`stepOKb` は 0 個。反例 `aBig` そのものでも一歩ぶんの条件は成り立つ。 -/

#guard (pairs68 (popSt68 4 7)).length == 1327
#guard ((pairs68 (popSt68 4 7)).filter fun p => !(bigOKb p.1 (dict p.2))).length == 33
#guard ((pairs68 (popSt68 4 7)).filter fun p => !(stepOKb p.1 (dict p.2))).length == 0
#guard ((pairs68 (popSt68 4 7)).filter fun p => !(psiIdxOKb p.1 (dict p.2))).length == 0
#guard !(bigOKb 0 (dict aBig))
#guard stepOKb 0 (dict aBig)

/-! **肯定 2 — (S1') `PsiIdxStepStd`。** 標準な `BT` の母集団で 0 失敗。`sclos 4 3` は
425 項・1894 対 (`u < 5`)、`sclos 6 3` は 1645 項・9989 対 (`u < 7`)、`sclos 8 3` は
4497 項・34551 対 (`u < 9`、内側の添字は 7 まで) — 最後のものは `u ≤ 5` について
「添字を `u+2` まで振る」を満たしている。(開発中には `sclos 3 4` の 4701 項・16793 対で
`psiIdxOKb` が 0 失敗であることも見ている。) -/

#guard ((List.range 5).flatMap fun u =>
  (sclos 4 3).filter fun a => BT.isStd (BT.D u a)).length == 1894
#guard ((List.range 5).flatMap fun u =>
  (sclos 4 3).filter fun a => BT.isStd (BT.D u a) && !(stepOKb u (dict a))).length == 0
#guard ((List.range 7).flatMap fun u =>
  (sclos 6 3).filter fun a => BT.isStd (BT.D u a)).length == 9989
#guard ((List.range 7).flatMap fun u =>
  (sclos 6 3).filter fun a => BT.isStd (BT.D u a) && !(stepOKb u (dict a))).length == 0
#guard ((List.range 9).flatMap fun u =>
  (sclos 8 3).filter fun a => BT.isStd (BT.D u a)).length == 34551
#guard ((List.range 9).flatMap fun u =>
  (sclos 8 3).filter fun a => BT.isStd (BT.D u a) && !(stepOKb u (dict a))).length == 0
#guard (small68.filter fun a => BT.isStd (BT.D 0 a) && !(stepOKb 0 (dict a))).length == 0

/-! **肯定 3 — (S2') `ArgStd`。** 良い木の上で 0 失敗。母集団は木そのもの (和ではない)。 -/

#guard ((pool68 4 6).filter fun c => goodAt 0 c).length == 906
#guard ((pool68 4 6).filter fun c => goodAt 1 c).length == 2824
#guard ((pool68 5 6).filter fun c => goodAt 2 c).length == 7606
#guard ((pool68 4 6).filter fun c => goodAt 0 c && !(BT.isStd (BT.D 0 (bArg 0 c)))).length == 0
#guard ((pool68 4 6).filter fun c => goodAt 1 c && !(BT.isStd (BT.D 1 (bArg 1 c)))).length == 0
#guard ((pool68 5 6).filter fun c => goodAt 2 c && !(BT.isStd (BT.D 2 (bArg 2 c)))).length == 0

/-! **肯定 4 — `ArgTransfer`。** 良い木の対の上では `cmpS` と `BT.lt` は**同値**
(片側の含意ではない)。177² + 485² + 1104² = 1 485 370 対で食い違い 0。 -/

#guard ((goods 0 4 5).flatMap fun c1 => (goods 0 4 5).filter fun c2 =>
  ((cmpS (toL c1) (toL c2) == Ordering.lt) != BT.lt (bArg 0 c1) (bArg 0 c2))).length == 0
#guard ((goods 1 4 5).flatMap fun c1 => (goods 1 4 5).filter fun c2 =>
  ((cmpS (toL c1) (toL c2) == Ordering.lt) != BT.lt (bArg 1 c1) (bArg 1 c2))).length == 0
#guard ((goods 2 5 5).flatMap fun c1 => (goods 2 5 5).filter fun c2 =>
  ((cmpS (toL c1) (toL c2) == Ordering.lt) != BT.lt (bArg 2 c1) (bArg 2 c2))).length == 0

/-! **肯定 5 — `RegionStd` そのもの (和の形)。** 四つの形の母集団で 0 失敗。
`expPop` は基本列で 2 回展開したもので、最大 36 節 — 列挙とは形が違う。 -/

#guard ((popSt68 4 7).filter fun t => !(BT.isStd (bVal t))).length == 0
#guard ((popSt68 4 8).filter fun t => !(BT.isStd (bVal t))).length == 0
#guard ((popSt68 5 8).filter fun t => !(BT.isStd (bVal t))).length == 0
#guard ((popSt68 6 7).filter fun t => !(BT.isStd (bVal t))).length == 0
#guard (expPop.filter fun t => !(stdB t)).length == 0
#guard (expPop.filter fun t => !(BT.isStd (bVal t))).length == 0
#guard popB.length == 877
#guard ((popB.filterMap decodeB).filter fun t => !(BT.isStd (bVal t))).length == 0

/-! **肯定 6 — 結論そのもの。** 同じ母集団で `inT (vOf t)` が 0 失敗。 -/

#guard ((popSt68 4 7).filter fun t => !(inT (vOf t))).length == 0
#guard ((popSt68 5 8).filter fun t => !(inT (vOf t))).length == 0
#guard (expPop.filter fun t => !(inT (vOf t))).length == 0
#guard ((popB.filterMap decodeB).filter fun t => !(inT (vOf t))).length == 0

end

/-! ### §68.6 公理 -/

/-! ## §70 THE LEVEL-ONE SUB-REGION — COFINALITY SURVIVES, AND ROW 326 IS INSIDE

§69 refuted `Hlim` for the generalised region: at the diagonal index `(0,0)(1,1)(2,2)` the
value is `ψ_{Ω₁}(Ω₂)`, the fundamental sequence is the ψ₁-tower with values `ψ_{Ω₁}(TW k)`,
and `sbad = ψ_{Ω₁}(φ̄(1,Ω₁))` sits in the gap between the two.  That index has a node of
LEVEL 2.  Row 326 — the target of the whole exercise — is `(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)`,
where every row-1 entry is 0 or 1.  §70 cuts the region down to that: `stdB1 t = stdB t &&
lvlLe 1 t`, "standard AND every node of level ≤ 1".

WHAT IS PROVED, UNCONDITIONALLY.

  §70.1  **THE LEVEL BOUND IS CLOSED UNDER THE FUNDAMENTAL SEQUENCE.**  `lvlLe_fsB` — for
         EVERY `m`, not only `m = 1`.  It is the easy half exactly as `table/diff.md`'s
         remark predicts: `fsB`'s three operators (`repB`, `rwB` through `iterD`/`plugB`,
         and dropping a leaf) only ever COPY nodes that are already there, so no node's
         level can rise.  Six one-line inductions — `lvlLe_appB`, `lvlLe_plugB`,
         `lvlLe_iterD`, `lvlLe_repNode`, `lvlLe_repB`, `lvlLe_rwB` — and none of them needs
         `lastBnd`, which is what §19's `nfLe` versions had to carry.  With §62's `stdB_fsB`
         this gives `stdB1_fsB`: **the sub-region is a region.**

  §70.2  **THE SUPPLIES.**  `hclosedS1_supply` (`certIn_region`'s first) and
         `hzeroS1_supply` are unconditional; `hsuccS1_supply_std` carries §67's two named
         hypotheses unchanged; `hlimS1_index` and `valS1_expand` are the index half and the
         `ValS` conjunct of `Hlim`, both unconditional.  `valS1_pins` shows the `f` in
         `Hlim` is not a free choice: `ValS1` forces `f n = vOf (fsB t n)`.

  §70.3  **§69'S COUNTEREXAMPLE DOES NOT REACH HERE — AND THE REASON IS A THEOREM.**
         `not_stdB1_tdiag : stdB1 tdiag = false` (the diagonal has a level-2 node), while
         `stdB1_fsB_tdiag : ∀ k, stdB1 (fsB tdiag k) = true` — **the whole ψ₁-tower IS in
         the sub-region and only its limit is not.**  So the sub-region climbs exactly the
         sequence §69's gap sits on top of, and stops one step short of it.  Measured
         (§70.6): no value of the sub-region reaches `sbad`, on `subP 8` (2397 indices) and
         `subP 10` (40 882).  `BelowGap` names that, and `sbad_not_witness` proves from it
         that §69's witness can never satisfy `lt sbad (vOf t)` inside the sub-region — the
         one hypothesis of §69's refutation is unavailable here.

  §70.4  **ROW 326 IS IN THE SUB-REGION, AS A THEOREM.**  `t326` is the index of
         `(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)` (`matB_t326`), `stdB1_t326` is proved — not
         measured: `stdB` runs through `cmpS`, which is well-founded and does not reduce, so
         the four comparisons it needs are unfolded by hand with §62.1's `cmpS_cons` —
         `kindB_t326 = lim`, and `vOf_t326` is the table's value
         `φ̄(φ̄00, φ̄(φ̄00 ⊕ φ̄00 ⊕ φ̄00, φ̄0 φ̄00))`, i.e. `ε_{φ̄(3,ω)+1}` in the table's own
         normal form.  Because §70.1 is a theorem, `stdB1_fsB t326 stdB1_t326` gives the
         WHOLE fundamental sequence of row 326 inside the sub-region for every `n` — no
         measurement, no bound on `n`.

  §70.5  **THE ASSEMBLY.**  `LimDecS1`/`LimIncS1`/`LimCofS1` are the three order conjuncts
         restricted to the sub-region, `limDecS1_of`/`limIncS1_of`/`limCofS1_of` show each
         is implied by §69's un-restricted version, `hlimS1_supply` is `certIn_region`'s
         `Hlim` in its exact shape, and `certInS1` closes the loop on five hypotheses.

WHAT THE MEASUREMENT SAYS — ITEM 2, THE POINT OF THE SECTION.  **COFINALITY SURVIVES.**
`LimCofS1` was swept the way §69 swept `LimCofS`: `s` over terms of 𝔗(M) that the
sub-region does NOT contain, never over the sub-region's own values.  **Zero
counterexamples**, over 1787 limit indices × 36 951 terms (§70.6 gives every population's
construction).  The control that the sweep is not vacuous: at `N = 6` the same pools produce
572 failing pairs on 9 indices, all of which are closed by some `n < 12`.  This is the
opposite of §69's finding, and §70.3 says why in one line: the level-2 node is what created
the gap, and it is exactly what `lvlLe 1` removes.

WHAT IS **NOT** CLAIMED.  `LimCofS1` is MEASURED, NOT PROVED — it is a statement about all
of 𝔗(M) and no finite sweep settles it; `hlimS1_supply` and `certInS1` carry it as a named
hypothesis, together with `LimDecS1`, `LimIncS1` and §67's `PsiIdxOKStd`/`RegionStd`, and
none of those five is discharged here.  `BelowGap` is measured, not proved.  Nothing here
repairs §69: `LimCofS` is still false, and this section does not say the table's value at
`(0,0)(1,1)(2,2)` is right or wrong.  It says the sub-region that contains row 326 is not
where that failure lives. -/

/-! ### §70.1 段の上限は基本列で保たれる

`nfLe` (§19) は「親の段 + 1」で上限が上がるが、ここで要るのは上がらない上限。`fsB` の
三つの演算はどれも既にある節を**複写する**だけなので、節の段は上がらない。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- **段の上限。** すべての節の段が `m` 以下。`nfLe` と違い上限は伝播しても上がらない。 -/
def lvlLe (m : Nat) : B → Bool
  | .nil => true
  | .nd v r a => decide (v ≤ m) && lvlLe m r && lvlLe m a

theorem lvlLe_nd_iff (m v : Nat) (r a : B) :
    lvlLe m (.nd v r a) = true ↔ (v ≤ m ∧ lvlLe m r = true ∧ lvlLe m a = true) := by
  show (decide (v ≤ m) && lvlLe m r && lvlLe m a) = true ↔ _
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, and_assoc]

/-- 和の連結。 -/
theorem lvlLe_appB : ∀ (s r : B) (m : Nat), lvlLe m r = true → lvlLe m s = true →
    lvlLe m (appB r s) = true := by
  intro s
  induction s with
  | nil => intro r m hr _; exact hr
  | nd v s a ihs _ =>
    intro r m hr hs
    obtain ⟨h1, h2, h3⟩ := (lvlLe_nd_iff m v s a).mp hs
    exact (lvlLe_nd_iff m v (appB r s) a).mpr ⟨h1, ihs r m hr h2, h3⟩

/-- 最後の節の差し替え。差し込む側も段が `m` 以下なら結果も。 -/
theorem lvlLe_plugB : ∀ (a : B) (m : Nat) (y : B), lvlLe m a = true → lvlLe m y = true →
    lvlLe m (plugB a y) = true := by
  intro a
  induction a with
  | nil => intro m y _ _; rfl
  | nd v r a _ iha =>
    intro m y ha hy
    obtain ⟨h1, h2, h3⟩ := (lvlLe_nd_iff m v r a).mp ha
    cases a with
    | nil =>
      show lvlLe m (appB r y) = true
      exact lvlLe_appB y r m h2 hy
    | nd u s b =>
      show lvlLe m (.nd v r (plugB (.nd u s b) y)) = true
      exact (lvlLe_nd_iff m v r _).mpr ⟨h1, h2, iha m y h3 hy⟩

/-- 悪い根の反復。新しく作る節の段は `v` そのもの。 -/
theorem lvlLe_iterD : ∀ (k v : Nat) (a : B) (m : Nat), v ≤ m → lvlLe m a = true →
    lvlLe m (iterD v a k) = true := by
  intro k
  induction k with
  | zero =>
    intro v a m hvm ha
    exact (lvlLe_nd_iff m v .nil _).mpr ⟨hvm, rfl, lvlLe_plugB a m .nil ha rfl⟩
  | succ j ih =>
    intro v a m hvm ha
    exact (lvlLe_nd_iff m v .nil _).mpr
      ⟨hvm, rfl, lvlLe_plugB a m _ ha (ih v a m hvm ha)⟩

/-- 親の節の複製。 -/
theorem lvlLe_repNode : ∀ (k v : Nat) (P : B) (m : Nat), v ≤ m → lvlLe m P = true →
    lvlLe m (repNode v P k) = true := by
  intro k
  induction k with
  | zero => intro v P m hvm hP; exact (lvlLe_nd_iff m v .nil P).mpr ⟨hvm, rfl, hP⟩
  | succ j ih =>
    intro v P m hvm hP
    exact (lvlLe_nd_iff m v _ P).mpr ⟨hvm, ih v P m hvm hP, hP⟩

/-- 段 0 の葉の枝。 -/
theorem lvlLe_repB : ∀ (t : B) (m n : Nat), lvlLe m t = true → lvlLe m (repB t n) = true := by
  intro t
  induction t with
  | nil => intro _ _ _; rfl
  | nd v r a _ iha =>
    intro m n h
    obtain ⟨h1, h2, h3⟩ := (lvlLe_nd_iff m v r a).mp h
    cases a with
    | nil => exact rfl
    | nd u P c =>
      cases u with
      | zero =>
        cases c with
        | nil =>
          show lvlLe m (appB r (repNode v P n)) = true
          obtain ⟨_, hP, _⟩ := (lvlLe_nd_iff m 0 P .nil).mp h3
          exact lvlLe_appB _ r m h2 (lvlLe_repNode n v P m h1 hP)
        | nd u2 s2 c2 =>
          show lvlLe m (.nd v r (repB (.nd 0 P (.nd u2 s2 c2)) n)) = true
          exact (lvlLe_nd_iff m v r _).mpr ⟨h1, h2, iha m n h3⟩
      | succ u' =>
        show lvlLe m (.nd v r (repB (.nd (u' + 1) P c) n)) = true
        exact (lvlLe_nd_iff m v r _).mpr ⟨h1, h2, iha m n h3⟩

/-- 段 `w ≥ 1` の葉の枝。§19 の `nfLe_rwB` と違い `lastBnd` は要らない。 -/
theorem lvlLe_rwB : ∀ (t : B) (w n m : Nat), lvlLe m t = true → lvlLe m (rwB w n t) = true := by
  intro t
  induction t with
  | nil => intro _ _ _ _; rfl
  | nd v r a _ iha =>
    intro w n m h
    obtain ⟨h1, h2, h3⟩ := (lvlLe_nd_iff m v r a).mp h
    cases a with
    | nil => exact h
    | nd u s b =>
      show lvlLe m (if hasLowAnc w (.nd u s b) then .nd v r (rwB w n (.nd u s b))
        else if v < w then appB r (iterD v (.nd u s b) n) else .nd v r (.nd u s b)) = true
      by_cases hl : hasLowAnc w (.nd u s b) = true
      · rw [if_pos hl]
        exact (lvlLe_nd_iff m v r _).mpr ⟨h1, h2, iha w n m h3⟩
      · rw [if_neg hl]
        by_cases hv : v < w
        · rw [if_pos hv]
          exact lvlLe_appB _ r m h2 (lvlLe_iterD n v (.nd u s b) m h1 h3)
        · rw [if_neg hv]
          exact h

/-- **§70.1 の主定理。** 段の上限は基本列で保たれる — `m` は任意。 -/
theorem lvlLe_fsB : ∀ (t : B) (m n : Nat), lvlLe m t = true → lvlLe m (fsB t n) = true := by
  intro t
  cases t with
  | nil => intro _ _ _; rfl
  | nd v r a =>
    intro m n h
    obtain ⟨_, h2, _⟩ := (lvlLe_nd_iff m v r a).mp h
    cases v with
    | zero =>
      cases a with
      | nil => exact h2
      | nd u s c =>
        show lvlLe m (if (lastLvl (B.nd u s c) == 0) = true
          then repB (B.nd 0 r (B.nd u s c)) n
          else rwB (lastLvl (B.nd u s c)) n (B.nd 0 r (B.nd u s c))) = true
        by_cases hz : (lastLvl (B.nd u s c) == 0) = true
        · rw [if_pos hz]; exact lvlLe_repB _ m n h
        · rw [if_neg hz]; exact lvlLe_rwB _ (lastLvl (B.nd u s c)) n m h
    | succ k =>
      cases a with
      | nil => exact rfl
      | nd u s c =>
        show lvlLe m (if (lastLvl (B.nd u s c) == 0) = true
          then repB (B.nd (k + 1) r (B.nd u s c)) n
          else rwB (lastLvl (B.nd u s c)) n (B.nd (k + 1) r (B.nd u s c))) = true
        by_cases hz : (lastLvl (B.nd u s c) == 0) = true
        · rw [if_pos hz]; exact lvlLe_repB _ m n h
        · rw [if_neg hz]; exact lvlLe_rwB _ (lastLvl (B.nd u s c)) n m h

/-- **部分領域の添字。** 標準で、しかもすべての節の段が 1 以下。 -/
def stdB1 (t : B) : Bool := stdB t && lvlLe 1 t

theorem stdB_of_stdB1 (t : B) (h : stdB1 t = true) : stdB t = true :=
  ((Bool.and_eq_true _ _).mp h).1

theorem lvlLe1_of_stdB1 (t : B) (h : stdB1 t = true) : lvlLe 1 t = true :=
  ((Bool.and_eq_true _ _).mp h).2

/-- **項目 1 の主定理。** 部分領域は基本列で閉じている。§62 の `stdB_fsB` と §70.1。 -/
theorem stdB1_fsB (t : B) (h : stdB1 t = true) (n : Nat) : stdB1 (fsB t n) = true := by
  show (stdB (fsB t n) && lvlLe 1 (fsB t n)) = true
  rw [stdB_fsB t (stdB_of_stdB1 t h) n, lvlLe_fsB t 1 n (lvlLe1_of_stdB1 t h)]
  rfl

end

/-! ### §70.2 部分領域と、`certIn_region` の供給

`RegS`/`ValS` (§61) を `stdB1` に絞っただけ。`Hclosed` と `Hzero` は無条件、`Hsucc` は
§67 の 2 つの仮説をそのまま運ぶ、`Hlim` の添字の側と `ValS` の条項は無条件。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- 部分領域: 段 1 以下の標準添字の行列。 -/
def RegS1 (S : BMS.Matrix) : Prop := ∃ t : B, stdB1 t = true ∧ S = matB t 0

/-- その上の値付け。 -/
def ValS1 (S : BMS.Matrix) (v : TM.Term) : Prop :=
  ∃ t : B, stdB1 t = true ∧ S = matB t 0 ∧ v = vOf t

theorem stdB1_nil : stdB1 .nil = true := rfl

theorem regS_of_regS1 {S : BMS.Matrix} : RegS1 S → RegS S
  | ⟨t, h, he⟩ => ⟨t, stdB_of_stdB1 t h, he⟩

theorem valS_of_valS1 {S : BMS.Matrix} {v : TM.Term} : ValS1 S v → ValS S v
  | ⟨t, h, he, hv⟩ => ⟨t, stdB_of_stdB1 t h, he, hv⟩

/-- **`certIn_region` の第 1 供給、部分領域で。無条件。** -/
theorem hclosedS1_supply : ∀ (S : BMS.Matrix), RegS1 S → ∀ (n : Nat),
    RegS1 (BMS.expand S n) := by
  rintro S ⟨t, hstd, rfl⟩ n
  cases t with
  | nil =>
    refine ⟨.nil, rfl, ?_⟩
    show ((BMS.expand? [] n).getD []) = []
    rfl
  | nd v r a =>
    refine ⟨fsB (B.nd v r a) n, stdB1_fsB _ hstd n, ?_⟩
    show ((BMS.expand? (matB (B.nd v r a) 0) n).getD []) = _
    rw [expand_matB (B.nd v r a) (topOKB_of_nfB _ (nfB_of_stdB _ (stdB_of_stdB1 _ hstd)))
      (by intro hc; exact B.noConfusion hc) n]
    rfl

/-- **`Hzero`、部分領域で。無条件。** -/
theorem hzeroS1_supply : ∀ (S : BMS.Matrix) (v : TM.Term), RegS1 S → ValS1 S v →
    BMS.kind S = BMS.Kind.zero → v = TM.Term.zero := by
  rintro S v _ ⟨t, hstd, rfl, rfl⟩ hk
  rw [kind_matB t] at hk
  rw [kindB_zero t hk]
  rfl

/-- 後続の添字の前身も部分領域。 -/
theorem stdB1_pred (r : B) (h : stdB1 (.nd 0 r .nil) = true) : stdB1 r = true := by
  have h1 : stdB r = true := stdB_pred r (stdB_of_stdB1 _ h)
  have h2 : lvlLe 1 r = true := ((lvlLe_nd_iff 1 0 r .nil).mp (lvlLe1_of_stdB1 _ h)).2.1
  show (stdB r && lvlLe 1 r) = true
  rw [h1, h2]
  rfl

/-- **`Hsucc` の供給、部分領域で。** §67 の 2 つの仮説はそのまま。 -/
theorem hsuccS1_supply_std (Hp : PsiIdxOKStd) (Hr : RegionStd) :
    ∀ (S : BMS.Matrix) (v : TM.Term), RegS1 S → ValS1 S v → BMS.kind S = BMS.Kind.succ →
    ∃ u, v = plus u TM.Term.one ∧ inT v = true ∧ inT u = true ∧ lt u v = true
         ∧ ∀ n, ValS1 (BMS.expand S n) u := by
  rintro S v _ ⟨t, hstd, rfl, rfl⟩ hk
  rw [kind_matB t] at hk
  obtain ⟨r, rfl⟩ := kindB_succ t hk
  have hstd' : stdB (B.nd 0 r .nil) = true := stdB_of_stdB1 _ hstd
  have hr1 : stdB1 r = true := stdB1_pred r hstd
  have hr : stdB r = true := stdB_of_stdB1 r hr1
  have htop : topOKB (B.nd 0 r .nil) = true := topOKB_of_nfB _ (nfB_of_stdB _ hstd')
  have hexp : ∀ n, BMS.expand (matB (B.nd 0 r .nil) 0) n = matB r 0 := by
    intro n
    show (BMS.expand? (matB (B.nd 0 r .nil) 0) n).getD [] = _
    rw [expand_matB (B.nd 0 r .nil) htop (by intro h; exact B.noConfusion h) n]
    rfl
  exact ⟨vOf r, vOf_succ_std Hp Hr r hr, inT_vOf_std Hp Hr _ hstd',
    inT_vOf_std Hp Hr r hr, lt_vOf_succ_std Hp Hr r hr,
    fun n => ⟨r, hr1, hexp n, rfl⟩⟩

/-- **`Hlim` の添字の側、部分領域で。無条件。** -/
theorem hlimS1_index : ∀ (S : BMS.Matrix), RegS1 S → BMS.kind S = BMS.Kind.lim →
    ∃ t : B, stdB1 t = true ∧ S = matB t 0 ∧ kindB t = BMS.Kind.lim
      ∧ ∀ n, BMS.expand S n = matB (fsB t n) 0 ∧ stdB1 (fsB t n) = true := by
  rintro S ⟨t, hstd, rfl⟩ hk
  rw [kind_matB t] at hk
  exact ⟨t, hstd, rfl, hk, fun n =>
    ⟨expand_matB_std (stdB_of_stdB1 t hstd) (kindB_ne_nil hk) n, stdB1_fsB t hstd n⟩⟩

/-- **極限の展開は部分領域の値を持つ。無条件。** -/
theorem valS1_expand : ∀ (t : B), stdB1 t = true → kindB t = BMS.Kind.lim →
    ∀ n, ValS1 (BMS.expand (matB t 0) n) (vOf (fsB t n)) := by
  intro t hstd hk n
  exact ⟨fsB t n, stdB1_fsB t hstd n,
    expand_matB_std (stdB_of_stdB1 t hstd) (kindB_ne_nil hk) n, rfl⟩

/-- **`ValS1` は列を決めてしまう。** `Hlim` の `f` を別に選ぶ逃げ道は無い。 -/
theorem valS1_pins {t : B} (hstd : stdB1 t = true) (hk : kindB t = BMS.Kind.lim)
    {v : TM.Term} (n : Nat) (h : ValS1 (BMS.expand (matB t 0) n) v) : v = vOf (fsB t n) := by
  obtain ⟨u, hu, heq, rfl⟩ := h
  rw [expand_matB_std (stdB_of_stdB1 t hstd) (kindB_ne_nil hk) n] at heq
  exact vOf_of_matB_eq (stdB_of_stdB1 u hu) (stdB_of_stdB1 _ (stdB1_fsB t hstd n)) heq.symm

end

/-! ### §70.3 §69 の反例は部分領域に届かない

対角 `(0,0)(1,1)(2,2)` は段 2 の節を持つので `stdB1` ではない。ところが**その基本列は
すべて部分領域の中にある** — ψ₁ の塔は段 1 の節だけでできているから。つまり部分領域は
§69 の隙間が載っている列そのものを登り、その一歩手前で止まる。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term
open Evidence.WF

/-- **対角は部分領域の外。** 段 2 の節がある。 -/
theorem not_stdB1_tdiag : stdB1 tdiag = false := rfl

/-- ψ₁ の塔は段 1 の節だけでできている。 -/
theorem lvlLe1_bTow : ∀ k, lvlLe 1 (bTow k) = true
  | 0 => rfl
  | k + 1 => by
      show (decide (1 ≤ 1) && lvlLe 1 .nil && lvlLe 1 (bTow k)) = true
      rw [lvlLe1_bTow k]
      rfl

theorem lvlLe1_fsB_tdiag (k : Nat) : lvlLe 1 (fsB tdiag k) = true := by
  rw [fsB_tdiag k]
  show (decide (0 ≤ 1) && lvlLe 1 .nil && lvlLe 1 (bTow k)) = true
  rw [lvlLe1_bTow k]
  rfl

/-- **§69 の基本列はまるごと部分領域の中。極限だけが外。** これが §70 が §69 を
    避けられる理由そのもの。 -/
theorem stdB1_fsB_tdiag (k : Nat) : stdB1 (fsB tdiag k) = true := by
  show (stdB (fsB tdiag k) && lvlLe 1 (fsB tdiag k)) = true
  rw [stdB_fsB tdiag stdB_tdiag k, lvlLe1_fsB_tdiag k]
  rfl

/-- **部分領域は §69 の隙間の下で終わる。** `subP 8` (2397) と `subP 10` (40 882) で
    反例 0 (§70.6)。**測定のみ、証明ではない。** -/
def BelowGap : Prop := ∀ (t : B), stdB1 t = true → lt (vOf t) sbad = true

/-- **`BelowGap` から: §69 の証人は部分領域では使えない。** `LimCofS1` の `s` に `sbad`
    を入れる道が塞がる — 前提 `lt s (vOf t)` が成り立たない。 -/
theorem sbad_not_witness (Hp : PsiIdxOKStd) (Hr : RegionStd) (H : BelowGap)
    (t : B) (ht : stdB1 t = true) : lt sbad (vOf t) = false :=
  lt_asymm_inT (inT_vOf_std Hp Hr t (stdB_of_stdB1 t ht)) inT_sbad (H t ht)

end

/-! ### §70.4 326 行目

`stdB` は `cmpS` を含み、`cmpS` は整礎再帰なので `rfl` では出ない (§68 の `visOK_cInc` と
同じ事情)。要る比較は 4 つだけで、§62.1 の `cmpS_cons` で手で開く。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

def b326a : B := .nd 1 .nil .nil
def b326b : B := .nd 1 b326a .nil
def b326c : B := .nd 0 b326b .nil
def b326d : B := .nd 1 .nil b326c
def b326e : B := .nd 1 b326d .nil

/-- **326 行目の添字。** 行列は `(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)`。 -/
def t326 : B := .nd 0 .nil b326e

theorem matB_t326 : matB t326 0 = [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1]] := rfl

theorem cmpS_b326c_nil : cmpS (toL b326c) (toL (B.nil)) = Ordering.gt := by
  show cmpS [((1:Nat), (B.nil)), ((1:Nat), (B.nil)), ((0:Nat), (B.nil))] [] = Ordering.gt
  exact cmpS_cons_nil _ _

theorem cmpN_b326c : cmpN 1 b326c 1 B.nil = Ordering.gt := by
  show cmpS [((1:Nat), b326c)] [((1:Nat), (B.nil))] = Ordering.gt
  rw [cmpS_cons, cmpS_b326c_nil]
  rfl

theorem cmpN_11 : cmpN 1 B.nil 1 B.nil = Ordering.eq := by
  show cmpS [((1:Nat), (B.nil))] [((1:Nat), (B.nil))] = Ordering.eq
  rw [cmpS_cons]
  show (if 1 < 1 then Ordering.lt else if 1 < 1 then Ordering.gt
        else match cmpS ([] : List (Nat × B)) [] with
             | Ordering.eq => cmpS ([] : List (Nat × B)) [] | o => o) = Ordering.eq
  rw [cmpS_nil_nil]
  rfl

theorem cmpN_10 : cmpN 1 B.nil 0 B.nil = Ordering.gt := by
  show cmpS [((1:Nat), (B.nil))] [((0:Nat), (B.nil))] = Ordering.gt
  rw [cmpS_cons]
  rfl

theorem cmpS_nil_lt_b326e : (cmpS (toL (B.nil)) (toL b326e) == Ordering.lt) = true := by
  rw [show toL b326e = [((1:Nat), b326c), ((1:Nat), (B.nil))] from rfl,
    show toL (B.nil) = ([] : List (Nat × B)) from rfl, cmpS_nil_cons]
  rfl

theorem cmpS_nil_lt_b326c : (cmpS (toL (B.nil)) (toL b326c) == Ordering.lt) = true := by
  rw [show toL b326c = [((1:Nat), (B.nil)), ((1:Nat), (B.nil)), ((0:Nat), (B.nil))] from rfl,
    show toL (B.nil) = ([] : List (Nat × B)) from rfl, cmpS_nil_cons]
  rfl

theorem nonIncr_b326e : nonIncr b326e = true := by
  show (!(cmpN 1 b326c 1 B.nil == Ordering.lt) && (true && true)) = true
  rw [cmpN_b326c]
  rfl

theorem nonIncr_b326c : nonIncr b326c = true := by
  show (!(cmpN 1 B.nil 1 B.nil == Ordering.lt)
    && (!(cmpN 1 B.nil 0 B.nil == Ordering.lt) && (true && true))) = true
  rw [cmpN_11, cmpN_10]
  rfl

theorem visOK_b326e : visOK 0 b326e b326e = true := by
  show ((true && (true && (((true && (true && true)) && (true && true))
    && ((cmpS (toL (B.nil)) (toL b326e) == Ordering.lt) && true)))) && (true && true)) = true
  rw [cmpS_nil_lt_b326e]
  rfl

theorem visOK_b326c : visOK 1 b326c b326c = true := by
  show (((true && ((cmpS (toL (B.nil)) (toL b326c) == Ordering.lt) && true))
    && ((cmpS (toL (B.nil)) (toL b326c) == Ordering.lt) && true)) && true) = true
  rw [cmpS_nil_lt_b326c]
  rfl

theorem stdIn_b326c : stdIn b326c = true := rfl

theorem stdIn_b326d : stdIn b326d = true := by
  show (((true && nonIncr b326c) && visOK 1 b326c b326c) && stdIn b326c) = true
  rw [nonIncr_b326c, visOK_b326c, stdIn_b326c]
  rfl

theorem stdIn_b326e : stdIn b326e = true := by
  show (((stdIn b326d && true) && true) && true) = true
  rw [stdIn_b326d]
  rfl

theorem stdIn_t326 : stdIn t326 = true := by
  show (((true && nonIncr b326e) && visOK 0 b326e b326e) && stdIn b326e) = true
  rw [nonIncr_b326e, visOK_b326e, stdIn_b326e]
  rfl

theorem stdB_t326 : stdB t326 = true := by
  show ((true && true) && stdIn t326) = true
  rw [stdIn_t326]
  rfl

/-- **326 行目は部分領域の中。証明済み。** -/
theorem stdB1_t326 : stdB1 t326 = true := by
  show (stdB t326 && true) = true
  rw [stdB_t326]
  rfl

theorem kindB_t326 : kindB t326 = BMS.Kind.lim := rfl

/-- **326 行目の値は表の値。** `φ̄(φ̄00, φ̄(φ̄00 ⊕ φ̄00 ⊕ φ̄00, φ̄0 φ̄00))` = `ε_{φ̄(3,ω)+1}`。 -/
theorem vOf_t326 : vOf t326
    = phi (phi zero zero) (phi (add (phi zero zero) (add (phi zero zero) (phi zero zero)))
        (phi zero (phi zero zero))) := rfl

theorem inT_vOf_t326 : inT (vOf t326) = true := rfl

/-- **326 行目の基本列は、すべての `n` で部分領域の中。** §70.1 の系。**測定ではない。** -/
theorem stdB1_fsB_t326 (n : Nat) : stdB1 (fsB t326 n) = true := stdB1_fsB t326 stdB1_t326 n

/-- 展開の側でも同じことを言った形。 -/
theorem regS1_expand_t326 (n : Nat) : RegS1 (BMS.expand (matB t326 0) n) :=
  hclosedS1_supply (matB t326 0) ⟨t326, stdB1_t326, rfl⟩ n

end

/-! ### §70.5 三つの順序の条項と、組み立て

§69.2 の 3 つを部分領域に絞ったもの。`LimDecS1`/`LimIncS1` は §70.6 で反例 0、
**`LimCofS1` も反例 0** — §69 の `LimCofS` が偽だったのと逆。ただしどれも測定であって
証明ではない。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- **減少。** 部分領域で。**測定のみ** (§70.6)。 -/
def LimDecS1 : Prop := ∀ (t : B), stdB1 t = true → kindB t = BMS.Kind.lim →
    ∀ n, lt (vOf (fsB t n)) (vOf t) = true

/-- **増加。** 部分領域で。**測定のみ** (§70.6)。 -/
def LimIncS1 : Prop := ∀ (t : B), stdB1 t = true → kindB t = BMS.Kind.lim →
    ∀ n, lt (vOf (fsB t n)) (vOf (fsB t (n + 1))) = true

/-- **共終性。** 部分領域で。**§69 と違い、反例は見つからない** (§70.6)。**測定のみ。** -/
def LimCofS1 : Prop := ∀ (t : B), stdB1 t = true → kindB t = BMS.Kind.lim →
    ∀ s, inT s = true → lt s (vOf t) = true → ∃ n, le s (vOf (fsB t n)) = true

theorem limDecS1_of (H : LimDecS) : LimDecS1 := fun t h => H t (stdB_of_stdB1 t h)
theorem limIncS1_of (H : LimIncS) : LimIncS1 := fun t h => H t (stdB_of_stdB1 t h)
/-- §69 の `LimCofS` は偽なのでこれは起動できない。向きを記録しておくためだけの補題。 -/
theorem limCofS1_of (H : LimCofS) : LimCofS1 := fun t h => H t (stdB_of_stdB1 t h)

/-- **`certIn_region` の `Hlim` 供給、部分領域で。** 仮説は 5 つ — §67 の 2 つと
    §70.5 の 3 つ。**`LimCofS1` は §69 の `LimCofS` と違って反証されていない。** -/
theorem hlimS1_supply (Hp : PsiIdxOKStd) (Hr : RegionStd)
    (HD : LimDecS1) (HI : LimIncS1) (HC : LimCofS1) :
    ∀ (S : BMS.Matrix) (v : TM.Term), RegS1 S → ValS1 S v → BMS.kind S = BMS.Kind.lim →
    ∃ f : Nat → TM.Term, inT v = true
      ∧ (∀ n, ValS1 (BMS.expand S n) (f n))
      ∧ (∀ n, inT (f n) = true)
      ∧ (∀ n, lt (f n) v = true)
      ∧ (∀ n, lt (f n) (f (n + 1)) = true)
      ∧ (∀ s, inT s = true → lt s v = true → ∃ n, le s (f n) = true) := by
  rintro S v _ ⟨t, hstd, rfl, rfl⟩ hk
  rw [kind_matB t] at hk
  exact ⟨fun n => vOf (fsB t n), inT_vOf_std Hp Hr t (stdB_of_stdB1 t hstd),
    valS1_expand t hstd hk,
    fun n => inT_vOf_std Hp Hr _ (stdB_of_stdB1 _ (stdB1_fsB t hstd n)),
    HD t hstd hk, HI t hstd hk, HC t hstd hk⟩

/-- **輪が閉じる形。** §70.2 の 3 つの供給と §70.5 の `Hlim` を `certIn_region` に入れる。
    仮説は 5 つ、そのうち **どれも §69 のようには反証されていない**。 -/
theorem certInS1 (Hp : PsiIdxOKStd) (Hr : RegionStd)
    (HD : LimDecS1) (HI : LimIncS1) (HC : LimCofS1) :
    ∀ (v : TM.Term), Acc Evidence.WF.RT v → ∀ (S : BMS.Matrix), RegS1 S → ValS1 S v →
      Evidence.Cert.CertifiedIn Evidence.Cert.DomI S v :=
  Evidence.Cert.certIn_region hclosedS1_supply hzeroS1_supply (hsuccS1_supply_std Hp Hr)
    (hlimS1_supply Hp Hr HD HI HC)

/-- **326 行目に当てた形。** 仮説は `certInS1` と同じ 5 つに停止性 1 つ。 -/
theorem certIn_t326 (Hp : PsiIdxOKStd) (Hr : RegionStd)
    (HD : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certInS1 Hp Hr HD HI HC (vOf t326) hacc (matB t326 0) ⟨t326, stdB1_t326, rfl⟩
    ⟨t326, stdB1_t326, rfl, rfl⟩

end

/-! ### §70.6 測定 (凍結)

母集団の作り方を先に書く。`enumNodes L n` は「節がちょうど `n` 個・段が `L` 未満」の `B`
を全部並べる (§19.3)。したがって

    popNFB L n = ((List.range n).flatMap (enumNodes L)).filter (nfB · && · != nil)   §48
    subP   n   = (popNFB 2 n).filter stdB1        段は 0,1 の 2 つしかない
    subLim n   = (subP n).filter (kindB · == lim)

すなわち **節の個数は `0 … n-1`、段は 0 と 1**。`subP n = (popS L n).filter (lvlLe 1)` が
`L = 3, 4` で確かめてある (下の 2 行) ので、段を 2 つに絞った列挙で取りこぼしは無い。

`s` の母集団は**部分領域の外**を含まなければならない (§69 が踏んだ罠)。三段構えで作る:

    baseD = (valP70 3 6 ++ valP70 4 7 ++ outP70 3 6 ++ outP70 4 7) の**部分項をすべて**取り、
            `inT` かつ `< cap` に絞って重複を除いたもの (671 項)
    phiL  = idxA (15 個) と baseD の `φ̄` の積 — 両側から (17 446 項)
    uni   = baseD の `ω^·`, `ω̄^·`, `· ⊕ 1`, `· ⊕ ·`, および idxP (5 個) を添字とする
            `ψ` を baseD と phiL に当てたもの (18 834 項)

ここで `valP70 L n = ((popS L n).map vOf).eraseDups` は**領域全体**の値 (段 0..L-1、
つまり段 2・段 3 の添字の値を含む — それらは部分領域の外)、
`outP70 L n` は**標準でない**添字の値を `inT` で絞ったもの (§69.5 と同じ)。
`cap = ψ_{Ω₁}(φ̄(1,Ω₁)) = sbad` で切るのは損が無い: `(subLim 8).all (lt (vOf ·) cap)` が
真なので、`cap` 以上の項は `lt s (vOf t)` を満たしようがない。

添字の掃き幅 (§66 の教訓)。`idxA` は `φ̄` の第 1 引数を `0,1,…,7, ω, ε₀, ζ₀, φ̄(3,0),
Γ₀, Ω₁, φ̄(1,Ω₁)` まで、`idxP` は `ψ` の添字を `Z0, Z1, Z2, Z3, Zω` まで取る。測定に
現れる `ψ` の添字は `Z0` と `Z1` の 2 つだけなので、これは実測の上限の 3 つ先まで。
`sbad = ψ_{Ω₁}(φ̄(1,Ω₁))` 自身も `idxP × phiL` の中に入っている。 -/

section
open Trans.Recal
open Trans.Dict (BT dict)
open TM TM.Term

def subP (n : Nat) : List B := (popNFB 2 n).filter stdB1
def subLim (n : Nat) : List B := (subP n).filter fun t => kindB t == BMS.Kind.lim
def valP70 (L n : Nat) : List Term := ((popS L n).map vOf).eraseDups
def outP70 (L n : Nat) : List Term :=
  (((popNFB L n).filter fun t => !(stdB t)).map vOf).eraseDups.filter fun x => inT x

/-- 部分項をすべて。 -/
def subs : Term → List Term
  | .zero => [.zero]
  | .M => [.M]
  | .add a b => .add a b :: (subs a ++ subs b)
  | .omg a => .omg a :: subs a
  | .phi a b => .phi a b :: (subs a ++ subs b)
  | .psi k a => .psi k a :: (subs k ++ subs a)
  | .Z a => .Z a :: subs a

/-- 掃く上限。`sbad` そのもの。 -/
def cap : Term := psi (Z zero) (phi TM.Term.one (Z zero))

def baseD : List Term :=
  ((((valP70 3 6) ++ (valP70 4 7) ++ (outP70 3 6) ++ (outP70 4 7)).flatMap subs).filter
    fun x => inT x && lt x cap).eraseDups

def idxA : List Term :=
  [zero, TM.Term.one, ofNat 2, ofNat 3, ofNat 4, ofNat 5, ofNat 6, ofNat 7,
   TM.Term.omega, phi TM.Term.one zero, phi (ofNat 2) zero, phi (ofNat 3) zero,
   psi (Z zero) zero, Z zero, phi TM.Term.one (Z zero)]
def idxP : List Term := [Z zero, Z TM.Term.one, Z (ofNat 2), Z (ofNat 3), Z TM.Term.omega]

def phiL : List Term :=
  (idxA.flatMap (fun c => baseD.map (fun a => phi c a))
   ++ idxA.flatMap (fun c => baseD.map (fun a => phi a c))).filter
    fun x => inT x && lt x cap

def uni : List Term :=
  (baseD.map omegaNF ++ baseD.map omg
   ++ idxP.flatMap (fun k => baseD.map (fun a => psi k a))
   ++ idxP.flatMap (fun k => phiL.map (fun a => psi k a))
   ++ baseD.map (fun a => plus a TM.Term.one)
   ++ baseD.map (fun a => plus a a)).filter fun x => inT x && lt x cap

/-- 共終性が落ちる対 `(t, s)`。`vOf t` と基本列の値は `t` ごとに 1 度だけ計算する。 -/
def cofFail2 (N : Nat) (ts : List B) (ss : List Term) : List (B × Term) :=
  ts.flatMap fun t =>
    let v := vOf t
    let fsv := (List.range N).map fun k => vOf (fsB t k)
    (ss.filter fun s => lt s v && !(fsv.any fun w => le s w)).map fun s => (t, s)

/-- 共終性が落ちる添字。 -/
def cofBad2 (N : Nat) (ts : List B) (ss : List Term) : List B :=
  ts.filter fun t =>
    let v := vOf t
    let fsv := (List.range N).map fun k => vOf (fsB t k)
    ss.any fun s => lt s v && !(fsv.any fun w => le s w)

-- 母集団の大きさ。
#guard (popNFB 2 6).length == 465
#guard (popNFB 2 8).length == 17361
#guard (subP 6).length == 160
#guard (subP 7).length == 609
#guard (subP 8).length == 2397
#guard (subLim 6).length == 114
#guard (subLim 7).length == 448
#guard (subLim 8).length == 1787
-- 段 2 つの列挙で取りこぼしが無いこと。
#guard ((popS 3 6).filter (lvlLe 1)).length == 160
#guard ((popS 4 7).filter (lvlLe 1)).length == 609
-- 領域のうち部分領域でないものの数。
#guard ((popS 3 6).filter fun t => !(lvlLe 1 t)).length == 75
#guard ((popS 4 7).filter fun t => !(lvlLe 1 t)).length == 654
-- s の母集団。
#guard baseD.length == 671
#guard phiL.length == 17446
#guard uni.length == 18834
#guard (baseD ++ phiL ++ uni).length == 36951
-- `cap` で切って損が無いこと。
#guard (subLim 8).all fun t => lt (vOf t) cap

/-! **項目 1 の受領。** §70.1 は定理なので、これは確認であって根拠ではない。 -/

#guard (subP 8).all fun t => (List.range 5).all fun n => stdB1 (fsB t n)
#guard (subP 8).all fun t => (List.range 3).all fun n => (List.range 3).all fun m =>
  stdB1 (fsB (fsB t n) m)

/-! **§69 との関係 (§70.3)。** 対角は外、その基本列は中。部分領域の値は `sbad` に届かない
— これが `BelowGap`。 -/

#guard !(stdB1 tdiag) && stdB tdiag
#guard (List.range 12).all fun k => stdB1 (fsB tdiag k)
#guard (subP 8).all fun t => lt (vOf t) sbad
#guard (subP 10).all fun t => lt (vOf t) sbad
#guard !((subP 10).any fun t => vOf t == sbad)
-- 部分領域は §69 の塔の項をそのまま値に持つ (`subP 8` では k = 1..5)。
#guard (List.range 8).map (fun k => (subP 8).any fun t => vOf t == psi (Z zero) (TW k))
  == [false, true, true, true, true, true, false, false]

/-! **項目 2 — 共終性は落ちない。** `s` は部分領域の外まで走らせている。
`N = 12` で反例 0。`N` を上げると失敗は減るだけなので、これは `N ≥ 12` すべてで反例 0
ということ。 -/

#guard (cofFail2 12 (subLim 6) baseD).length == 0
#guard (cofFail2 12 (subLim 8) baseD).length == 0
#guard (cofFail2 12 (subLim 6) phiL).length == 0
#guard (cofFail2 12 (subLim 6) uni).length == 0

/-! **測定が空回りしていないことの対照。** 同じ母集団を `N = 6` で掃くと 572 対・9 個の
添字が落ちる。つまりこの試験は落ちるときには落ちる — 落ちた 572 対はどれも
`6 ≤ n < 12` で閉じる。 -/

#guard (cofFail2 6 (subLim 6) phiL).length == 559
#guard (cofFail2 6 (subLim 6) uni).length == 13
#guard (cofBad2 6 (subLim 6) (phiL ++ uni)).length == 9

/-! **減少と増加 (§70.5 の 2 つ)。** 反例 0。 -/

#guard (subLim 8).all fun t => (List.range 8).all fun n => lt (vOf (fsB t n)) (vOf t)
#guard (subLim 8).all fun t => (List.range 7).all fun n =>
  lt (vOf (fsB t n)) (vOf (fsB t (n + 1)))
#guard (subLim 6).all fun t => (List.range 13).all fun n => lt (vOf (fsB t n)) (vOf t)
#guard (subLim 6).all fun t => (List.range 12).all fun n =>
  lt (vOf (fsB t n)) (vOf (fsB t (n + 1)))

/-! **326 行目 (§70.4)。** 定理になっている分の受領と、`oR` (表の値そのもの) との一致。 -/

#guard matB t326 0 == [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1]]
#guard decodeB [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1]] == some t326
#guard stdB1 t326 && (kindB t326 == BMS.Kind.lim)
#guard Trans.Recal.oR (matB t326 0) == some (vOf t326)
#guard (List.range 8).all fun n =>
  Trans.Recal.oR (BMS.expand (matB t326 0) n) == some (vOf (fsB t326 n))
#guard (List.range 8).all fun n => stdB1 (fsB t326 n)
-- 表の 326 行目の値そのもの。
#guard (Rows.rows.filter fun r : Rows.Row =>
  r.m == [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1]]).length == 1
#guard (Rows.rows.filter fun r : Rows.Row =>
  r.m == [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1]]).all fun r : Rows.Row => r.t == vOf t326

end

/-! ### §70.7 公理 -/

/-! ## §72 THE LEVEL-ONE SUB-REGION CLOSES `RegionStd` — `ArgStd` IS A THEOREM THERE

§67 left `certIn_region`'s second supply on two named, measured, unproved hypotheses,
`RegionStd` and `PsiIdxOKStd`; §68 replaced each by a strictly more local one, `ArgStd` and
`PsiIdxStepStd`, and proved NEITHER; §70 cut the region down to `stdB1 t = stdB t && lvlLe 1 t`,
the sub-region that contains row 326.  §72 **closes the first of the two gates on that
sub-region, unconditionally**, and reduces the second one to the same sub-region.  Everything
below is a theorem unless it visibly carries `Hp`.

WHAT IS PROVED, UNCONDITIONALLY.

  §72.1  **AT LEVEL ONE `bArg` DOES NOT COLLAPSE, AND DOES NOT SEE THE PARENT.**  `bK`'s
         three-way branch has the guard `u ≤ w || r ≠ nil || headLvl c ≤ u`, and at level one
         every node satisfies it for a trivial reason: `u = 0` gives `u ≤ w` for every `w`,
         and `u = 1` gives `headLvl c ≤ 1 = u`.  So `bK w u r c = ψ_u (bArg u c)` always and
         `toL_bArg72` says the component list of `bArg w c` is the plain `map` of `toL c` —
         **the very asymmetry §68.2c named as the obstruction (a collapsing head contributes
         a LIST, the other nodes one `ψ` each) is gone**, and with it the proper-prefix case
         that has no counterpart on the `cmpS` side.  `bArg_indep72`: `bArg w c` does not
         depend on `w` at all.

  §72.2  **THE ORDER TRANSFER IS A THEOREM AT LEVEL ONE — AND IT NEEDS NOTHING ELSE.**
         `argTransfer72` : `lvlLe 1 c₁ → lvlLe 1 c₂ → cmpS (toL c₁) (toL c₂) = .lt →
         BT.lt (bArg w₁ c₁) (bArg w₂ c₂) = true`.  **No `nonIncr`, no `visOK`, no `stdIn`,
         no `nfLe`** — the level bound alone replaces all of them.  §68's witness for
         "`ArgTransfer` is false with only `nfLe`" (`cT1`/`cT2`, `not_argTransfer_nfLe`) has a
         LEVEL-2 node, so it is outside.  The proof runs on component lists with §68.1's
         fuel-free `ltS` (`ltS_cons`) against §62.1's `cmpS_cons`, one case at a time; the
         only extra brick is `ltL_irrefl72`, which picks the "arguments differ" branch.

  §72.3  **EVERY NODE'S ARGUMENT IS `cmpS`-BELOW THE WHOLE TREE.**  `key72` : for `c` with
         `lvlLe 1`, `nonIncr`, `visOK 0 c c` and `stdIn`, EVERY node of `c` at EVERY depth has
         `cmpS (toL (its argument)) (toL c) = .lt`.  `visOK 0 c c` gives this for the level-0
         nodes directly (its traversal never stops, since it only stops below level 0), and
         the level-1 nodes are the work: `topLvl1_72` does the top-level ones — `nonIncr` makes
         the head component the maximum, so the head has level 1 too, and `stdIn`'s
         `visOK 1 d d` puts the head of `d` strictly below `d`, which `cmpS_trans` turns into
         the head comparison — and `keyInner72` does the deeper ones by a two-part induction:
         under a level-0 node the child is good at 0, so `key72` applies to it and `cmpS_trans`
         lifts; under a level-1 node `visOK 1` applies and `cmpS_trans` lifts.

  §72.4  **`ArgStd` AT LEVEL ONE IS A THEOREM.**  `argStd72` :

             lvlLe 1 c → nonIncr c → visOK w c c → stdIn c → BT.isStd (ψ_w (bArg w c)) = true

         for EVERY `w`, not only `w ≤ 1`.  `isStd` of a sum splits into "components standard"
         (the induction) and "components descending" (`descOK_map72`, from `nonIncr` through
         §72.2), and `GB w`'s condition splits into "which nodes `GB w` descends through"
         (`gbL72`, the SAME traversal as `visOK w`) and "each of them is below" (§72.3 through
         §72.2).  **`nfLe` IS NOT A HYPOTHESIS** — `nfLe_of_lvlLe72` derives `nfLe m` from
         `lvlLe 1` for every `m ≥ 1`, so §68's fourth load-bearing conjunct is free here (its
         witness `cNf` has a level-3 node).  The other three are STILL load-bearing, with
         witnesses that are theorems: `not_argStd72_no_visOK` (2 nodes), `..._no_nonIncr`
         (2 nodes), `..._no_stdIn` (4 nodes, new — §68's `cStd` has a level-2 node).
         `regionStd1_72` is the consumer's form: **§67's `RegionStd`, restricted to `stdB1`,
         is a theorem.**  §72.7b goes one better: `toL_bVal72` says `bVal`'s component list is
         `toL t`'s `map` with a leading `(0, nil)` dropped, and `regionStdSum1_72` proves
         **§67.2's stronger `RegionStdSum` on the sub-region** — the whole sum is
         Buchholz-standard, not only its components.

  §72.5  **THE SECOND GATE, RESTRICTED TO THE SAME PLACE.**  `btLe72 1` is the level bound on
         the `BT` side and `btLe_bVal_mem72` proves the sub-region's values carry it, so the
         consumers only ever need `PsiIdxOKStd172` — 2.1(vi) for `ψ_u a` with `u ≤ 1` and every
         subscript of `a` at most 1.  `psiIdxOKStd172_of_step172` carries §68.3's one-step form
         `PsiIdxStepStd172` to it; `psiIdxOKStd172_of_std` records that it is weaker than §66.4.

  §72.6/§72.7  **THE CONSUMERS AND THE ASSEMBLY.**  `hsuccS1_supply_72` and `hlimS1_supply_72`
         are §70.2/§70.5's supplies with `RegionStd` REMOVED, and `certIn_t326_72` is §70's
         `certIn_t326` with the same hypothesis removed: what is left is `PsiIdxOKStd172`,
         §70.5's `LimDecS1`/`LimIncS1`/`LimCofS1`, and the accessibility of `vOf t326`.
         **Five hypotheses become four, and the one that goes was the harder-looking one.**

WHAT IS **NOT** CLAIMED.

  * **`PsiIdxStepStd172` IS NOT PROVED, AND THE LEVEL BOUND DOES NOT TRIVIALISE IT.**  The
    obvious hope — that at level one the strongly-critical branch of `collapse`, the only
    branch `KsetStepOK` constrains, never fires — is FALSE, measured: over the 1908 `(u, a)`
    pairs occurring inside the values of the level-≤1 standard indices of at most 7 nodes, the
    scan takes 1614 steps and **335 of them take that branch**.  `stepOKb` fails on none of
    them, and on none of 1767 standard `(u, a)` pairs of a systematic level-≤1 `BT` pool with
    `u` swept to 5 — but that is measurement, not proof.  A proof still needs what §68 named:
    the transport of Buchholz's `G(a,u) < a` to Rathjen's `K_κ α < α`.
  * **NOTHING HERE IS ABOUT THE UNRESTRICTED `ArgStd` OR `RegionStd`.**  §68's four
    counterexamples and §67.2's `tbad` stand untouched; `argStd72` says nothing about trees
    with a node of level 2 or more, and §69's refutation of `Hlim` lives exactly there.
  * `LimDecS1`, `LimIncS1`, `LimCofS1` are §70.5's, still measured and still unproved.  This
    section does not touch them, and it does not prove `Acc RT (vOf t326)`. -/

/-! ### §72.1 段が 1 以下なら `bArg` は潰れない -/

section
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (BT)
open TM TM.Term

/-- 成分列の側の段の上限。 -/
def LvlL72 (l : List (Nat × B)) : Prop := ∀ q ∈ l, q.1 ≤ 1 ∧ lvlLe 1 q.2 = true

/-- 節の寄与 — 潰れない形。 -/
def fB72 (q : Nat × B) : BT := BT.D q.1 (bArg q.1 q.2)

theorem lvlL72_nil : LvlL72 [] := by intro q hq; cases hq

theorem lvlL72_of_lvlLe : ∀ (c : B), lvlLe 1 c = true → LvlL72 (toL c)
  | .nil, _ => lvlL72_nil
  | .nd v r a, h => by
    obtain ⟨h1, h2, h3⟩ := (lvlLe_nd_iff 1 v r a).mp h
    rw [toL_nd]
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact lvlL72_of_lvlLe r h2 q hq
    · rw [List.mem_singleton.mp hq]; exact ⟨h1, h3⟩

theorem lvlL72_tail {q : Nat × B} {l : List (Nat × B)} (h : LvlL72 (q :: l)) : LvlL72 l :=
  fun x hx => h x (List.mem_cons_of_mem q hx)

theorem headLvl_le72 : ∀ (a : B), lvlLe 1 a = true → headLvl a ≤ 1
  | .nil, _ => Nat.zero_le 1
  | .nd v .nil a, h => ((lvlLe_nd_iff 1 v .nil a).mp h).1
  | .nd v (.nd u s b) a, h => by
    show headLvl (B.nd u s b) ≤ 1
    exact headLvl_le72 (B.nd u s b) ((lvlLe_nd_iff 1 v (.nd u s b) a).mp h).2.1

/-- **段が 1 以下なら三分岐は一本になる。** 潰す枝は決して選ばれない。 -/
theorem bK_nil72 (w u : Nat) (a : B) (hu : u ≤ 1) (ha : lvlLe 1 a = true) :
    bK w u .nil a = BT.D u (bArg u a) := by
  show (if (a == .nil) = true then (BT.D u BT.zero)
        else if (decide (u ≤ w) || !(B.nil == .nil) || decide (headLvl a ≤ u)) = true
             then BT.D u (bArg u a) else bClose u (bFold u a)) = _
  by_cases hc : (a == .nil) = true
  · rw [if_pos hc, show a = .nil from of_decide_eq_true hc]
    rfl
  · rw [if_neg hc, if_pos ?_]
    show (decide (u ≤ w) || false || decide (headLvl a ≤ u)) = true
    rw [Bool.or_false, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr (by have := headLvl_le72 a ha; omega)

/-- **潰れない形の成分列。** `argL` は単なる `map` になる。 -/
theorem argL_map72 : ∀ (w : Nat) (l : List (Nat × B)), LvlL72 l → argL w l = l.map fB72
  | _, [], _ => rfl
  | w, (u, a) :: rest, h => by
    obtain ⟨h1, h2⟩ := h (u, a) (List.mem_cons.mpr (Or.inl rfl))
    show (bK w u .nil a).toL ++ rest.map (fun q => BT.D q.1 (bArg q.1 q.2))
      = fB72 (u, a) :: rest.map fB72
    rw [bK_nil72 w u a h1 h2]
    rfl

/-- **§72.1 の主定理。** 段が 1 以下の添字では `bArg` の成分列はただの `map`。 -/
theorem toL_bArg72 (w : Nat) (c : B) (h : lvlLe 1 c = true) :
    (bArg w c).toL = (toL c).map fB72 := by
  rw [toL_bArg w c, argL_map72 w (toL c) (lvlL72_of_lvlLe c h)]

end

/-! ### §72.2 移送 — 段が 1 以下なら添字の順序はそのまま値の順序 -/

section
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (BT)
open TM TM.Term

theorem beq_refl72 : ∀ a : BT, (a == a) = true
  | .zero => rfl
  | .D u a => by
    show (u == u && (a == a)) = true
    rw [beq_refl72 a, beq_self_eq_true u]
    rfl
  | .sum a b => by
    show ((a == a) && (b == b)) = true
    rw [beq_refl72 a, beq_refl72 b]
    rfl

theorem eq_of_beq72 : ∀ (a b : BT), (a == b) = true → a = b
  | .zero, .zero, _ => rfl
  | .zero, .D _ _, h => Bool.noConfusion h
  | .zero, .sum _ _, h => Bool.noConfusion h
  | .D _ _, .zero, h => Bool.noConfusion h
  | .sum _ _, .zero, h => Bool.noConfusion h
  | .D _ _, .sum _ _, h => Bool.noConfusion h
  | .sum _ _, .D _ _, h => Bool.noConfusion h
  | .D u a, .D v b, h => by
    have h' : (u == v && (a == b)) = true := h
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h'
    rw [eq_of_beq h1, eq_of_beq72 a b h2]
  | .sum a b, .sum c d, h => by
    have h' : ((a == c) && (b == d)) = true := h
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h'
    rw [eq_of_beq72 a c h1, eq_of_beq72 b d h2]

/-- `ltS` は非反射。移送の「引数が違う」枝を選ぶのに要る。 -/
theorem ltL_irrefl72 : ∀ (f : Nat) (l : List BT), BT.ltL f l l = false
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | f + 1, x :: xs => by
    cases x with
    | zero => rfl
    | sum p q => rfl
    | D u a =>
      show (if u < u then true else if u < u then false
            else if (a == a) = true then BT.ltL f xs xs else BT.ltL f a.toL a.toL) = false
      rw [if_neg (Nat.lt_irrefl u), if_neg (Nat.lt_irrefl u), if_pos (beq_refl72 a)]
      exact ltL_irrefl72 f xs

theorem ltS_irrefl72 (l : List BT) : ltS l l = false := ltL_irrefl72 _ l

theorem sizeL_pos72 : ∀ (x : Nat × B) (xs : List (Nat × B)), 0 < sizeL (x :: xs)
  | (_, a), xs => by show 0 < sizeB a + 1 + sizeL xs; omega

/-- **§72.2 の主定理 (成分列の形)。** 段が 1 以下なら `cmpS` の `lt` は `ltS` の `true`
    にそのまま移る。`nonIncr` も `visOK` も `stdIn` も要らない — §68 の `ArgTransfer` が
    要求した側条件は、段の上限が肩代わりする。 -/
theorem transfer72 : ∀ (n : Nat) (l1 l2 : List (Nat × B)), sizeL l1 + sizeL l2 < n →
    LvlL72 l1 → LvlL72 l2 → cmpS l1 l2 = Ordering.lt →
    ltS (l1.map fB72) (l2.map fB72) = true
  | 0, _, _, hs, _, _, _ => absurd hs (Nat.not_lt_zero _)
  | n + 1, [], [], _, _, _, hlt => by rw [cmpS_nil_nil] at hlt; exact Ordering.noConfusion hlt
  | n + 1, [], y :: ys, _, _, _, _ => by
    show ltS [] (fB72 y :: ys.map fB72) = true
    exact ltS_nil_cons _ _
  | n + 1, _ :: _, [], _, _, _, hlt => by
    rw [cmpS_cons_nil] at hlt; exact Ordering.noConfusion hlt
  | n + 1, (u, a) :: xs, (v, b) :: ys, hs, h1, h2, hlt => by
    obtain ⟨hu, ha⟩ := h1 (u, a) (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨hv, hb⟩ := h2 (v, b) (List.mem_cons.mpr (Or.inl rfl))
    have hsa : sizeL (toL a) + sizeL (toL b) < n := by
      have e1 : sizeL (toL a) = sizeB a := sizeL_toL a
      have e2 : sizeL (toL b) = sizeB b := sizeL_toL b
      have e3 : sizeL ((u, a) :: xs) = sizeB a + 1 + sizeL xs := rfl
      have e4 : sizeL ((v, b) :: ys) = sizeB b + 1 + sizeL ys := rfl
      omega
    have hsx : sizeL xs + sizeL ys < n := by
      have e3 : sizeL ((u, a) :: xs) = sizeB a + 1 + sizeL xs := rfl
      have e4 : sizeL ((v, b) :: ys) = sizeB b + 1 + sizeL ys := rfl
      omega
    rw [cmpS_cons] at hlt
    show ltS (BT.D u (bArg u a) :: xs.map fB72) (BT.D v (bArg v b) :: ys.map fB72) = true
    rw [ltS_cons]
    by_cases huv : u < v
    · rw [if_pos huv]
    · rw [if_neg huv] at hlt ⊢
      by_cases hvu : v < u
      · rw [if_pos hvu] at hlt; exact Ordering.noConfusion hlt
      · rw [if_neg hvu] at hlt ⊢
        cases hab : cmpS (toL a) (toL b) with
        | gt => rw [hab] at hlt; exact Ordering.noConfusion hlt
        | lt =>
          have key : ltS (bArg u a).toL (bArg v b).toL = true := by
            rw [toL_bArg72 u a ha, toL_bArg72 v b hb]
            exact transfer72 n (toL a) (toL b) hsa (lvlL72_of_lvlLe a ha)
              (lvlL72_of_lvlLe b hb) hab
          have hne : ¬ ((bArg u a == bArg v b) = true) := by
            intro he
            rw [eq_of_beq72 _ _ he, ltS_irrefl72] at key
            exact Bool.noConfusion key
          rw [if_neg hne]
          exact key
        | eq =>
          have hab' : a = b := toL_inj a b (cmpS_eq_imp (toL a) (toL b) hab)
          have huv' : u = v := by omega
          rw [hab] at hlt
          rw [if_pos (show (bArg u a == bArg v b) = true by rw [hab', huv']; exact beq_refl72 _)]
          exact transfer72 n xs ys hsx (lvlL72_tail h1) (lvlL72_tail h2) hlt

/-- **§72.2 の主定理 (木の形)。** -/
theorem argTransfer72 (w1 w2 : Nat) (c1 c2 : B)
    (h1 : lvlLe 1 c1 = true) (h2 : lvlLe 1 c2 = true)
    (h : cmpS (toL c1) (toL c2) = Ordering.lt) : BT.lt (bArg w1 c1) (bArg w2 c2) = true := by
  rw [Trans.Dict.BT.lt, toL_bArg72 w1 c1 h1, toL_bArg72 w2 c2 h2]
  rw [show BT.ltL ((bArg w1 c1).size + (bArg w2 c2).size + 2)
        ((toL c1).map fB72) ((toL c2).map fB72)
      = ltS ((toL c1).map fB72) ((toL c2).map fB72) from ?_]
  · exact transfer72 (sizeL (toL c1) + sizeL (toL c2) + 1) (toL c1) (toL c2)
      (Nat.lt_succ_self _) (lvlL72_of_lvlLe c1 h1) (lvlL72_of_lvlLe c2 h2) h
  · have e1 : (bArg w1 c1).toL = (toL c1).map fB72 := toL_bArg72 w1 c1 h1
    have e2 : (bArg w2 c2).toL = (toL c2).map fB72 := toL_bArg72 w2 c2 h2
    have s1 := sizeLB_toL (bArg w1 c1)
    have s2 := sizeLB_toL (bArg w2 c2)
    rw [e1] at s1
    rw [e2] at s2
    exact ltL_fuel _ _ _ _ (by omega) (by omega)

/-- 一成分どうしの移送。`nonIncr` から降べきを取り出すのに使う。 -/
theorem lt_fB72 (q1 q2 : Nat × B) (h1 : q1.1 ≤ 1) (ha1 : lvlLe 1 q1.2 = true)
    (h2 : q2.1 ≤ 1) (ha2 : lvlLe 1 q2.2 = true)
    (h : cmpS [q1] [q2] = Ordering.lt) : BT.lt (fB72 q1) (fB72 q2) = true := by
  rw [Trans.Dict.BT.lt]
  show BT.ltL _ [fB72 q1] [fB72 q2] = true
  rw [show BT.ltL ((fB72 q1).size + (fB72 q2).size + 2) [fB72 q1] [fB72 q2]
      = ltS [fB72 q1] [fB72 q2] from ?_]
  · exact transfer72 (sizeL [q1] + sizeL [q2] + 1) [q1] [q2] (Nat.lt_succ_self _)
      (fun x hx => by rw [List.mem_singleton.mp hx]; exact ⟨h1, ha1⟩)
      (fun x hx => by rw [List.mem_singleton.mp hx]; exact ⟨h2, ha2⟩) h
  · have s1 := sizeLB_toL (fB72 q1)
    have s2 := sizeLB_toL (fB72 q2)
    have e1 : (fB72 q1).toL = [fB72 q1] := rfl
    have e2 : (fB72 q2).toL = [fB72 q2] := rfl
    rw [e1] at s1
    rw [e2] at s2
    exact ltL_fuel _ _ _ _ (by omega) (by omega)

end

/-! ### §72.3 添字の側 — 節の引数はどれも木そのものより小さい -/

section
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (BT)
open TM TM.Term

/-- 木のすべての節を「(段, 引数)」の対として。 -/
def nodes72 : B → List (Nat × B)
  | .nil => []
  | .nd u r c => nodes72 r ++ ((u, c) :: nodes72 c)

/-- `GB w` が降りる節だけ。段が `w` 未満の節で打ち切る — `visOK w` と同じ走査。 -/
def gbL72 (w : Nat) : B → List (Nat × B)
  | .nil => []
  | .nd u r c => gbL72 w r ++ (if w ≤ u then (u, c) :: gbL72 w c else [])

theorem ord_ne_lt72 {o : Ordering} (h : (!(o == Ordering.lt)) = true) : o ≠ Ordering.lt := by
  cases o with
  | lt => exact Bool.noConfusion h
  | eq => intro hc; exact Ordering.noConfusion hc
  | gt => intro hc; exact Ordering.noConfusion hc

theorem ord_lt72 : ∀ (o : Ordering), (o == Ordering.lt) = true → o = Ordering.lt
  | .lt, _ => rfl
  | .eq, h => Bool.noConfusion h
  | .gt, h => Bool.noConfusion h

/-- `visOK` の展開式。 -/
theorem visOK_nd72 (v u : Nat) (a r c : B) :
    visOK v a (.nd u r c)
      = (visOK v a r &&
         (if u < v then true
          else (if u == v then cmpS (toL c) (toL a) == Ordering.lt else true) && visOK v a c)) :=
  rfl

/-- `stdIn` は各成分に `nonIncr`・`visOK`・`stdIn` を渡す。 -/
theorem stdIn_mem72 : ∀ (t : B), stdIn t = true → ∀ q ∈ toL t,
    nonIncr q.2 = true ∧ visOK q.1 q.2 q.2 = true ∧ stdIn q.2 = true
  | .nil, _ => by intro q hq; cases hq
  | .nd v r c, h => by
    obtain ⟨hr, hn, hv, hs⟩ := stdIn_nd h
    rw [toL_nd]
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact stdIn_mem72 r hr q hq
    · rw [List.mem_singleton.mp hq]; exact ⟨hn, hv, hs⟩

/-- 最上位の段 `v` の節は、引数が基準より真に小さい。 -/
theorem visOK_top72 : ∀ (v : Nat) (a t : B), visOK v a t = true →
    ∀ q ∈ toL t, q.1 = v → cmpS (toL q.2) (toL a) = Ordering.lt
  | _, _, .nil, _ => by intro q hq; cases hq
  | v, a, .nd u r c, h => by
    rw [visOK_nd72] at h
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
    rw [toL_nd]
    intro q hq hqv
    rcases List.mem_append.mp hq with hq | hq
    · exact visOK_top72 v a r h1 q hq hqv
    · rw [List.mem_singleton.mp hq] at hqv ⊢
      have hne : ¬ (u < v) := by omega
      rw [if_neg hne] at h2
      obtain ⟨h3, _⟩ := (Bool.and_eq_true _ _).mp h2
      rw [if_pos (show (u == v) = true by rw [show u = v from hqv]; exact beq_self_eq_true v)] at h3
      exact ord_lt72 _ h3

/-- 段 0 を基準にした走査はすべての節を通り、段 0 の節の引数を押さえる。 -/
theorem visOK0_mem72 : ∀ (c t : B), visOK 0 c t = true →
    ∀ q ∈ nodes72 t, q.1 = 0 → cmpS (toL q.2) (toL c) = Ordering.lt
  | _, .nil, _ => by intro q hq; cases hq
  | c, .nd u r a, h => by
    rw [visOK_nd72] at h
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
    rw [if_neg (Nat.not_lt_zero u)] at h2
    obtain ⟨h3, h4⟩ := (Bool.and_eq_true _ _).mp h2
    show ∀ q ∈ nodes72 r ++ ((u, a) :: nodes72 a), q.1 = 0 → _
    intro q hq hq0
    rcases List.mem_append.mp hq with hq | hq
    · exact visOK0_mem72 c r h1 q hq hq0
    · rcases List.mem_cons.mp hq with hq | hq
      · rw [hq] at hq0 ⊢
        rw [if_pos (show (u == 0) = true by rw [show u = 0 from hq0]; rfl)] at h3
        exact ord_lt72 _ h3
      · exact visOK0_mem72 c a h4 q hq hq0

/-- 段 0 の走査は子にも渡る。 -/
theorem visOK0_child72 : ∀ (c t : B), visOK 0 c t = true →
    ∀ q ∈ toL t, visOK 0 c q.2 = true
  | _, .nil, _ => by intro q hq; cases hq
  | c, .nd u r a, h => by
    rw [visOK_nd72] at h
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
    rw [if_neg (Nat.not_lt_zero u)] at h2
    obtain ⟨_, h4⟩ := (Bool.and_eq_true _ _).mp h2
    rw [toL_nd]
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact visOK0_child72 c r h1 q hq
    · rw [List.mem_singleton.mp hq]; exact h4

/-- 段 1 を基準にした走査は `gbL72 1` とちょうど同じ。 -/
theorem visOK1_mem72 : ∀ (c t : B), lvlLe 1 t = true → visOK 1 c t = true →
    ∀ q ∈ gbL72 1 t, cmpS (toL q.2) (toL c) = Ordering.lt
  | _, .nil, _, _ => by intro q hq; cases hq
  | c, .nd u r a, hl, h => by
    obtain ⟨hu, hlr, hla⟩ := (lvlLe_nd_iff 1 u r a).mp hl
    rw [visOK_nd72] at h
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
    show ∀ q ∈ gbL72 1 r ++ (if 1 ≤ u then (u, a) :: gbL72 1 a else []), _
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact visOK1_mem72 c r hlr h1 q hq
    · by_cases hu1 : 1 ≤ u
      · rw [if_pos hu1] at hq
        rw [if_neg (show ¬ (u < 1) by omega)] at h2
        obtain ⟨h3, h4⟩ := (Bool.and_eq_true _ _).mp h2
        rw [if_pos (show (u == 1) = true by rw [show u = 1 by omega]; rfl)] at h3
        rcases List.mem_cons.mp hq with hq | hq
        · rw [hq]; exact ord_lt72 _ h3
        · exact visOK1_mem72 c a hla h4 q hq
      · rw [if_neg hu1] at hq; cases hq

/-- 段が 2 以上なら `GB` は何も拾わない。 -/
theorem gbL72_ge2 : ∀ (w : Nat) (t : B), 2 ≤ w → lvlLe 1 t = true → gbL72 w t = []
  | _, .nil, _, _ => rfl
  | w, .nd u r a, hw, hl => by
    obtain ⟨hu, hlr, _⟩ := (lvlLe_nd_iff 1 u r a).mp hl
    show gbL72 w r ++ (if w ≤ u then (u, a) :: gbL72 w a else []) = []
    rw [gbL72_ge2 w r hw hlr, if_neg (show ¬ (w ≤ u) by omega)]
    rfl

end

/-! ### §72.3b 降べきの先頭は最大 -/

section
open Trans.Recal (bplus)
open Evidence.Region
open Trans.Dict (BT)
open TM TM.Term

theorem hdOK_cons72 (x y : Nat × B) (l : List (Nat × B)) :
    hdOK x (y :: l) = !(cmpS [x] [y] == Ordering.lt) := rfl

theorem nonIncrL_cons72 (x : Nat × B) (l : List (Nat × B)) :
    nonIncrL (x :: l) = (hdOK x l && nonIncrL l) := rfl

theorem nonIncrL_head72 : ∀ (l : List (Nat × B)) (x : Nat × B), nonIncrL (x :: l) = true →
    ∀ y ∈ l, cmpS [x] [y] ≠ Ordering.lt
  | [], _, _ => by intro y hy; cases hy
  | y :: l', x, h => by
    rw [nonIncrL_cons72] at h
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
    rw [hdOK_cons72] at h1
    have hxy : cmpS [x] [y] ≠ Ordering.lt := ord_ne_lt72 h1
    intro z hz
    rcases List.mem_cons.mp hz with hz | hz
    · rw [hz]; exact hxy
    · have hyz := nonIncrL_head72 l' y h2 z hz
      intro hcon
      cases hxy' : cmpS [x] [y] with
      | lt => exact hxy hxy'
      | eq =>
        have he : x = y := by
          have := cmpS_eq_imp [x] [y] hxy'
          injection this
        rw [he] at hcon
        exact hyz hcon
      | gt => exact hyz (cmpS_trans _ _ _ (cmpS_gt_lt hxy') hcon)

theorem nonIncrL_max72 (l : List (Nat × B)) (x q : Nat × B) (h : nonIncrL (x :: l) = true)
    (hq : q ∈ x :: l) : cmpS [x] [q] ≠ Ordering.lt := by
  rcases List.mem_cons.mp hq with hq | hq
  · rw [hq, cmpS_refl]; intro hcon; exact Ordering.noConfusion hcon
  · exact nonIncrL_head72 l x h q hq

theorem nonIncrL_prefix72 : ∀ (l1 l2 : List (Nat × B)), nonIncrL (l1 ++ l2) = true →
    nonIncrL l1 = true
  | [], _, _ => rfl
  | x :: l1', l2, h => by
    rw [show (x :: l1') ++ l2 = x :: (l1' ++ l2) from rfl, nonIncrL_cons72] at h
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
    rw [nonIncrL_cons72]
    refine (Bool.and_eq_true _ _).mpr ⟨?_, nonIncrL_prefix72 l1' l2 h2⟩
    cases l1' with
    | nil => rfl
    | cons y l'' =>
      rw [hdOK_cons72]
      rw [show (y :: l'') ++ l2 = y :: (l'' ++ l2) from rfl, hdOK_cons72] at h1
      exact h1

/-- **最上位の段 1 の節の引数は、木そのものより小さい。** `nonIncr` で先頭が最大、
    `stdIn` の `visOK 1` でその中がさらに小さい — この二つだけで出る。 -/
theorem topLvl1_72 (c : B) (hl : lvlLe 1 c = true) (hn : nonIncr c = true)
    (hs : stdIn c = true) :
    ∀ q ∈ toL c, q.1 = 1 → cmpS (toL q.2) (toL c) = Ordering.lt := by
  rintro ⟨v, d⟩ hq hq1
  have hq1' : v = 1 := hq1
  subst hq1'
  have hn' : nonIncrL (toL c) = true := hn
  have hmemL := lvlL72_of_lvlLe c hl
  have hld : lvlLe 1 d = true := (hmemL (1, d) hq).2
  have hvd : visOK 1 d d = true := (stdIn_mem72 c hs (1, d) hq).2.1
  cases hc : toL c with
  | nil => rw [hc] at hq; cases hq
  | cons x rest =>
    obtain ⟨u1, a1⟩ := x
    rw [hc] at hn' hq
    have hmax : cmpS [(u1, a1)] [(1, d)] ≠ Ordering.lt :=
      nonIncrL_max72 rest (u1, a1) (1, d) hn' hq
    have hu1le : u1 ≤ 1 := (hmemL (u1, a1) (by rw [hc]; exact List.mem_cons.mpr (Or.inl rfl))).1
    have hu1 : u1 = 1 := by
      rcases Nat.lt_or_ge u1 1 with h0 | h0
      · exact absurd (by rw [cmpS_cons, if_pos h0]) hmax
      · omega
    subst hu1
    have hcm : cmpS (toL a1) (toL d) ≠ Ordering.lt := by
      intro hc2
      exact hmax (by rw [cmpS_cons, if_neg (Nat.lt_irrefl 1), if_neg (Nat.lt_irrefl 1), hc2])
    cases hd : toL d with
    | nil => exact cmpS_nil_cons _ _
    | cons y r' =>
      obtain ⟨v2, b⟩ := y
      have hv2 : v2 ≤ 1 :=
        ((lvlL72_of_lvlLe d hld) (v2, b) (by rw [hd]; exact List.mem_cons.mpr (Or.inl rfl))).1
      rcases Nat.lt_or_ge v2 1 with h0 | h0
      · rw [cmpS_cons, if_pos h0]
      · have hv2' : v2 = 1 := by omega
        subst hv2'
        have hb : cmpS (toL b) (toL d) = Ordering.lt :=
          visOK_top72 1 d d hvd (1, b) (by rw [hd]; exact List.mem_cons.mpr (Or.inl rfl)) rfl
        have hba : cmpS (toL b) (toL a1) = Ordering.lt := by
          cases had : cmpS (toL a1) (toL d) with
          | lt => exact absurd had hcm
          | eq => rw [toL_inj a1 d (cmpS_eq_imp _ _ had)]; exact hb
          | gt => exact cmpS_trans _ _ _ hb (cmpS_gt_lt had)
        rw [cmpS_cons, if_neg (Nat.lt_irrefl 1), if_neg (Nat.lt_irrefl 1), hba]

end

/-! ### §72.3c 主定理 — 節の引数はどれも木より小さい -/

section
open Trans.Recal (bplus)
open Evidence.Region
open Trans.Dict (BT)
open TM TM.Term

theorem toL_sub_nodes72 : ∀ (t : B) (q : Nat × B), q ∈ toL t → q ∈ nodes72 t
  | .nil, _, hq => by cases hq
  | .nd u r a, q, hq => by
    rw [toL_nd] at hq
    show q ∈ nodes72 r ++ ((u, a) :: nodes72 a)
    rcases List.mem_append.mp hq with hq | hq
    · exact List.mem_append.mpr (Or.inl (toL_sub_nodes72 r q hq))
    · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hq))))

theorem nonIncr_pred72 (u : Nat) (r a : B) (h : nonIncr (.nd u r a) = true) :
    nonIncr r = true := by
  have h' : nonIncrL (toL r ++ [(u, a)]) = true := by rw [← toL_nd]; exact h
  exact nonIncrL_prefix72 (toL r) [(u, a)] h'

/-- **§72.3 の主定理 (二本立ての帰納法)。** 第一の連言が結論、第二はその中で回る形。 -/
theorem keyInner72 : ∀ (n : Nat),
    (∀ (c : B), sizeB c < n → lvlLe 1 c = true → nonIncr c = true → visOK 0 c c = true →
      stdIn c = true → ∀ q ∈ nodes72 c, cmpS (toL q.2) (toL c) = Ordering.lt)
    ∧ (∀ (c t : B), sizeB t < n → lvlLe 1 t = true → nonIncr t = true → stdIn t = true →
      visOK 0 c t = true → (∀ q ∈ toL t, q.1 = 1 → cmpS (toL q.2) (toL c) = Ordering.lt) →
      ∀ q ∈ nodes72 t, cmpS (toL q.2) (toL c) = Ordering.lt) := by
  intro n
  induction n with
  | zero =>
    exact ⟨fun _ hsz => absurd hsz (Nat.not_lt_zero _),
           fun _ _ hsz => absurd hsz (Nat.not_lt_zero _)⟩
  | succ n ih =>
    have hinner : ∀ (c t : B), sizeB t < n + 1 → lvlLe 1 t = true → nonIncr t = true →
        stdIn t = true → visOK 0 c t = true →
        (∀ q ∈ toL t, q.1 = 1 → cmpS (toL q.2) (toL c) = Ordering.lt) →
        ∀ q ∈ nodes72 t, cmpS (toL q.2) (toL c) = Ordering.lt := by
      intro c t
      induction t with
      | nil => intro _ _ _ _ _ _ q hq; cases hq
      | nd u r a ihr iha =>
        intro hsz hl hn hs hv htop q hq
        obtain ⟨hu, hlr, hla⟩ := (lvlLe_nd_iff 1 u r a).mp hl
        obtain ⟨hsr, hna, hva, hsa⟩ := stdIn_nd hs
        have hnr : nonIncr r = true := nonIncr_pred72 u r a hn
        rw [visOK_nd72] at hv
        obtain ⟨hvr, hv2⟩ := (Bool.and_eq_true _ _).mp hv
        rw [if_neg (Nat.not_lt_zero u)] at hv2
        obtain ⟨hv3, hvc⟩ := (Bool.and_eq_true _ _).mp hv2
        have hszr : sizeB r < n + 1 := by
          have : sizeB (B.nd u r a) = sizeB r + 1 + sizeB a := rfl
          omega
        have hsza : sizeB a < n := by
          have : sizeB (B.nd u r a) = sizeB r + 1 + sizeB a := rfl
          omega
        have htopr : ∀ q' ∈ toL r, q'.1 = 1 → cmpS (toL q'.2) (toL c) = Ordering.lt :=
          fun q' hq' => htop q' (by rw [toL_nd]; exact List.mem_append.mpr (Or.inl hq'))
        have hua : cmpS (toL a) (toL c) = Ordering.lt := by
          rcases Nat.eq_zero_or_pos u with h0 | h0
          · rw [if_pos (show (u == 0) = true by rw [h0]; rfl)] at hv3
            exact ord_lt72 _ hv3
          · have hmem : (u, a) ∈ toL (B.nd u r a) := by
              rw [toL_nd]
              exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
            exact htop (u, a) hmem (by omega)
        have htopa : ∀ q' ∈ toL a, q'.1 = 1 → cmpS (toL q'.2) (toL c) = Ordering.lt := by
          intro q' hq' hq1
          rcases Nat.eq_zero_or_pos u with h0 | h0
          · have hva0 : visOK 0 a a = true := by rw [← h0]; exact hva
            have := ih.1 a hsza hla hna hva0 hsa q' (toL_sub_nodes72 a q' hq')
            exact cmpS_trans _ _ _ this hua
          · have hu1 : u = 1 := by omega
            have hva1 : visOK 1 a a = true := by rw [← hu1]; exact hva
            exact cmpS_trans _ _ _ (visOK_top72 1 a a hva1 q' hq' hq1) hua
        have hq2 : q ∈ nodes72 r ++ ((u, a) :: nodes72 a) := hq
        rcases List.mem_append.mp hq2 with hq | hq
        · exact ihr hszr hlr hnr hsr hvr htopr q hq
        · rcases List.mem_cons.mp hq with hq | hq
          · rw [hq]; exact hua
          · exact iha (by omega) hla hna hsa hvc htopa q hq
    exact ⟨fun c hsz hl hn hv hs q hq =>
             hinner c c hsz hl hn hs hv (topLvl1_72 c hl hn hs) q hq, hinner⟩

/-- **§72.3 の結論。** 段が 1 以下で良い添字なら、どの節の引数も木そのものより小さい。 -/
theorem key72 (c : B) (hl : lvlLe 1 c = true) (hn : nonIncr c = true)
    (hv : visOK 0 c c = true) (hs : stdIn c = true) :
    ∀ q ∈ nodes72 c, cmpS (toL q.2) (toL c) = Ordering.lt :=
  (keyInner72 (sizeB c + 1)).1 c (Nat.lt_succ_self _) hl hn hv hs

end

/-! ### §72.4a `BT` の側 — 和の標準性と `GB` を成分列で見る -/

section
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (BT)
open TM TM.Term

/-- 成分列が広義単調減少。`BT.isStd` の和の条項そのもの。 -/
def descOK72 : List BT → Bool
  | [] => true
  | [_] => true
  | x :: y :: r => BT.le y x && descOK72 (y :: r)

/-- **和の標準性は成分ごとの標準性と降べきに分かれる。** -/
theorem isStd_ofL72 : ∀ (l : List BT), Atoms l → (∀ x ∈ l, BT.isStd x = true) →
    descOK72 l = true → BT.isStd (BT.ofL l) = true
  | [], _, _, _ => rfl
  | [a], _, hs, _ => hs a (List.mem_cons.mpr (Or.inl rfl))
  | a :: y :: r, hat, hs, hd => by
    obtain ⟨p1, q1, rfl⟩ := hat a (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨p2, q2, rfl⟩ := hat y (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
    have hdd : (BT.le (BT.D p2 q2) (BT.D p1 q1) && descOK72 (BT.D p2 q2 :: r)) = true := hd
    obtain ⟨hle, hd2⟩ := (Bool.and_eq_true _ _).mp hdd
    have hrest : BT.isStd (BT.ofL (BT.D p2 q2 :: r)) = true :=
      isStd_ofL72 (BT.D p2 q2 :: r) (fun z hz => hat z (List.mem_cons.mpr (Or.inr hz)))
        (fun z hz => hs z (List.mem_cons.mpr (Or.inr hz))) hd2
    have hsa : BT.isStd (BT.D p1 q1) = true := hs _ (List.mem_cons.mpr (Or.inl rfl))
    cases r with
    | nil =>
      have hsy : BT.isStd (BT.D p2 q2) = true := hrest
      show (BT.isP (BT.D p1 q1) && BT.isStd (BT.D p1 q1) && BT.isStd (BT.D p2 q2) &&
            (BT.isP (BT.D p2 q2) && BT.le (BT.D p2 q2) (BT.D p1 q1))) = true
      rw [hsa, hsy, hle, show BT.isP (BT.D p1 q1) = true from rfl,
        show BT.isP (BT.D p2 q2) = true from rfl]
      rfl
    | cons z r' =>
      show (BT.isP (BT.D p1 q1) && BT.isStd (BT.D p1 q1) &&
            BT.isStd (BT.sum (BT.D p2 q2) (BT.ofL (z :: r'))) &&
            BT.le (BT.D p2 q2) (BT.D p1 q1)) = true
      rw [hsa, hle, show BT.isP (BT.D p1 q1) = true from rfl,
        show BT.isStd (BT.sum (BT.D p2 q2) (BT.ofL (z :: r'))) = true from hrest]
      rfl

/-- `GB` は和の成分に散る。 -/
theorem mem_GB_ofL72 : ∀ (w : Nat) (l : List BT) (e : BT),
    e ∈ BT.GB w (BT.ofL l) → ∃ x ∈ l, e ∈ BT.GB w x
  | _, [], _, he => by cases he
  | _, [a], _, he => ⟨a, List.mem_cons.mpr (Or.inl rfl), he⟩
  | w, a :: y :: r, e, he => by
    have he' : e ∈ BT.GB w a ++ BT.GB w (BT.ofL (y :: r)) := he
    rcases List.mem_append.mp he' with h | h
    · exact ⟨a, List.mem_cons.mpr (Or.inl rfl), h⟩
    · obtain ⟨x, hx, hex⟩ := mem_GB_ofL72 w (y :: r) e h
      exact ⟨x, List.mem_cons.mpr (Or.inr hx), hex⟩

theorem GB_D72 (w u : Nat) (a : BT) :
    BT.GB w (BT.D u a) = (if u ≥ w then a :: BT.GB w a else []) := rfl

end

/-! ### §72.4b `gbL72` の帰属と大きさ -/

section
open Trans.Recal (bplus)
open Evidence.Region
open Trans.Dict (BT)
open TM TM.Term

theorem sizeB_mem72 : ∀ (t : B) (q : Nat × B), q ∈ toL t → sizeB q.2 < sizeB t
  | .nil, _, hq => by cases hq
  | .nd u r a, q, hq => by
    rw [toL_nd] at hq
    have e : sizeB (B.nd u r a) = sizeB r + 1 + sizeB a := rfl
    rcases List.mem_append.mp hq with hq | hq
    · have := sizeB_mem72 r q hq
      omega
    · rw [List.mem_singleton.mp hq]
      show sizeB a < sizeB r + 1 + sizeB a
      omega

theorem mem_gbL72_self : ∀ (w : Nat) (t : B) (q : Nat × B), q ∈ toL t → w ≤ q.1 →
    q ∈ gbL72 w t
  | _, .nil, _, hq, _ => by cases hq
  | w, .nd u r a, q, hq, hw => by
    rw [toL_nd] at hq
    show q ∈ gbL72 w r ++ (if w ≤ u then (u, a) :: gbL72 w a else [])
    rcases List.mem_append.mp hq with hq | hq
    · exact List.mem_append.mpr (Or.inl (mem_gbL72_self w r q hq hw))
    · have hq' : q = (u, a) := List.mem_singleton.mp hq
      rw [hq'] at hw ⊢
      rw [if_pos (show w ≤ u from hw)]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

theorem mem_gbL72_sub : ∀ (w : Nat) (t : B) (q0 q : Nat × B), q0 ∈ toL t → w ≤ q0.1 →
    q ∈ gbL72 w q0.2 → q ∈ gbL72 w t
  | _, .nil, _, _, hq, _, _ => by cases hq
  | w, .nd u r a, q0, q, hq0, hw, hq => by
    rw [toL_nd] at hq0
    show q ∈ gbL72 w r ++ (if w ≤ u then (u, a) :: gbL72 w a else [])
    rcases List.mem_append.mp hq0 with hq0 | hq0
    · exact List.mem_append.mpr (Or.inl (mem_gbL72_sub w r q0 q hq0 hw hq))
    · have hq' : q0 = (u, a) := List.mem_singleton.mp hq0
      rw [hq'] at hw hq
      rw [if_pos (show w ≤ u from hw)]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hq)))

theorem gbL72_zero72 : ∀ (t : B), gbL72 0 t = nodes72 t
  | .nil => rfl
  | .nd u r a => by
    show gbL72 0 r ++ (if 0 ≤ u then (u, a) :: gbL72 0 a else [])
      = nodes72 r ++ ((u, a) :: nodes72 a)
    rw [if_pos (Nat.zero_le u), gbL72_zero72 r, gbL72_zero72 a]

end

/-! ### §72.4c `ArgStd` の段 1 以下の形 — 証明 -/

section
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (BT)
open TM TM.Term

theorem gbL72_lvl72 : ∀ (w : Nat) (t : B), lvlLe 1 t = true →
    ∀ q ∈ gbL72 w t, q.1 ≤ 1 ∧ lvlLe 1 q.2 = true
  | _, .nil, _, _, hq => by cases hq
  | w, .nd u r a, hl, q, hq => by
    obtain ⟨hu, hlr, hla⟩ := (lvlLe_nd_iff 1 u r a).mp hl
    have hq2 : q ∈ gbL72 w r ++ (if w ≤ u then (u, a) :: gbL72 w a else []) := hq
    rcases List.mem_append.mp hq2 with h | h
    · exact gbL72_lvl72 w r hlr q h
    · by_cases hw : w ≤ u
      · rw [if_pos hw] at h
        rcases List.mem_cons.mp h with h | h
        · rw [h]; exact ⟨hu, hla⟩
        · exact gbL72_lvl72 w a hla q h
      · rw [if_neg hw] at h; cases h

theorem ofL_bArg72 (w : Nat) (c : B) (hl : lvlLe 1 c = true) :
    bArg w c = BT.ofL ((toL c).map fB72) := by
  rw [← toL_bArg72 w c hl]
  exact (nfSum_bArg w c).symm

/-- **段が 1 以下なら `bArg` は親の段に依らない。** 潰す枝が消えたので `w` が効かない。 -/
theorem bArg_indep72 (w1 w2 : Nat) (c : B) (hl : lvlLe 1 c = true) :
    bArg w1 c = bArg w2 c := by
  rw [ofL_bArg72 w1 c hl, ofL_bArg72 w2 c hl]

/-- `GB w (bArg w c)` の要素は `gbL72 w c` の節の引数の `bArg`。 -/
theorem mem_GB_bArg72 : ∀ (n w : Nat) (c : B) (e : BT), sizeB c < n → lvlLe 1 c = true →
    e ∈ BT.GB w (bArg w c) → ∃ q ∈ gbL72 w c, e = bArg q.1 q.2
  | 0, _, _, _, hsz, _, _ => absurd hsz (Nat.not_lt_zero _)
  | n + 1, w, c, e, hsz, hl, he => by
    rw [ofL_bArg72 w c hl] at he
    obtain ⟨x, hxm, hex⟩ := mem_GB_ofL72 w _ e he
    obtain ⟨q, hqm, hxq⟩ := List.mem_map.mp hxm
    rw [← hxq] at hex
    rw [show fB72 q = BT.D q.1 (bArg q.1 q.2) from rfl, GB_D72] at hex
    by_cases hw : q.1 ≥ w
    · rw [if_pos hw] at hex
      rcases List.mem_cons.mp hex with h | h
      · exact ⟨q, mem_gbL72_self w c q hqm hw, h⟩
      · have hlq : lvlLe 1 q.2 = true := (lvlL72_of_lvlLe c hl q hqm).2
        have hsq : sizeB q.2 < n := by have := sizeB_mem72 c q hqm; omega
        rw [bArg_indep72 q.1 w q.2 hlq] at h
        obtain ⟨q', hq', he'⟩ := mem_GB_bArg72 n w q.2 e hsq hlq h
        exact ⟨q', mem_gbL72_sub w c q q' hqm hw hq', he'⟩
    · rw [if_neg hw] at hex; cases hex

/-- `nonIncr` が `BT` 側の降べきになる。 -/
theorem descOK_map72 : ∀ (l : List (Nat × B)), LvlL72 l → nonIncrL l = true →
    descOK72 (l.map fB72) = true
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | x :: y :: r, hl, hn => by
    rw [nonIncrL_cons72] at hn
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hn
    rw [hdOK_cons72] at h1
    have hxy : cmpS [x] [y] ≠ Ordering.lt := ord_ne_lt72 h1
    have hlx := hl x (List.mem_cons.mpr (Or.inl rfl))
    have hly := hl y (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
    have hle : BT.le (fB72 y) (fB72 x) = true := by
      cases hcc : cmpS [x] [y] with
      | lt => exact absurd hcc hxy
      | eq =>
        have he : x = y := by
          have hee := cmpS_eq_imp [x] [y] hcc
          injection hee
        show ((fB72 y == fB72 x) || BT.lt (fB72 y) (fB72 x)) = true
        rw [he, beq_refl72 (fB72 y)]
        rfl
      | gt =>
        show ((fB72 y == fB72 x) || BT.lt (fB72 y) (fB72 x)) = true
        rw [lt_fB72 y x hly.1 hly.2 hlx.1 hlx.2 (cmpS_gt_lt hcc), Bool.or_true]
    show (BT.le (fB72 y) (fB72 x) && descOK72 (fB72 y :: r.map fB72)) = true
    exact (Bool.and_eq_true _ _).mpr ⟨hle, descOK_map72 (y :: r) (lvlL72_tail hl) h2⟩

/-- **`GB` が降りる節の引数は、どれも木そのものより小さい。** 段 0 では §72.3 の
    `key72`、段 1 では `visOK 1`、段 2 以上では `GB` が空。 -/
theorem gbL72_lt72 (w : Nat) (c : B) (hl : lvlLe 1 c = true) (hn : nonIncr c = true)
    (hv : visOK w c c = true) (hs : stdIn c = true) :
    ∀ q ∈ gbL72 w c, cmpS (toL q.2) (toL c) = Ordering.lt := by
  cases w with
  | zero => rw [gbL72_zero72 c]; exact key72 c hl hn hv hs
  | succ k =>
    cases k with
    | zero => exact visOK1_mem72 c c hl hv
    | succ k2 => rw [gbL72_ge2 _ c (by omega) hl]; intro q hq; cases hq

/-- **§72.4 の主定理 (帰納の形)。** -/
theorem argStd72aux : ∀ (n w : Nat) (c : B), sizeB c < n → lvlLe 1 c = true →
    nonIncr c = true → visOK w c c = true → stdIn c = true →
    BT.isStd (BT.D w (bArg w c)) = true
  | 0, _, _, hsz, _, _, _, _ => absurd hsz (Nat.not_lt_zero _)
  | n + 1, w, c, hsz, hl, hn, hv, hs => by
    have hat : Atoms ((toL c).map fB72) := by
      intro z hz
      obtain ⟨q, _, hq⟩ := List.mem_map.mp hz
      exact ⟨q.1, bArg q.1 q.2, hq.symm⟩
    have hcomp : ∀ z ∈ (toL c).map fB72, BT.isStd z = true := by
      intro z hz
      obtain ⟨q, hqm, hq⟩ := List.mem_map.mp hz
      rw [← hq]
      obtain ⟨hnq, hvq, hsq⟩ := stdIn_mem72 c hs q hqm
      have hlq : lvlLe 1 q.2 = true := (lvlL72_of_lvlLe c hl q hqm).2
      have hsz2 : sizeB q.2 < n := by have := sizeB_mem72 c q hqm; omega
      exact argStd72aux n q.1 q.2 hsz2 hlq hnq hvq hsq
    have hstdx : BT.isStd (bArg w c) = true := by
      rw [ofL_bArg72 w c hl]
      exact isStd_ofL72 _ hat hcomp (descOK_map72 (toL c) (lvlL72_of_lvlLe c hl) hn)
    have hgb : ∀ e ∈ BT.GB w (bArg w c), BT.lt e (bArg w c) = true := by
      intro e he
      obtain ⟨q, hqm, hqe⟩ := mem_GB_bArg72 (sizeB c + 1) w c e (Nat.lt_succ_self _) hl he
      rw [hqe]
      exact argTransfer72 q.1 w q.2 c (gbL72_lvl72 w c hl q hqm).2 hl
        (gbL72_lt72 w c hl hn hv hs q hqm)
    show (BT.isStd (bArg w c) && (BT.GB w (bArg w c)).all (fun e => BT.lt e (bArg w c))) = true
    rw [hstdx, Bool.true_and, List.all_eq_true]
    exact hgb

/-- **§72 の第一の門。** 段が 1 以下なら `ArgStd` は定理。`nfLe` は仮説に要らない
    (`lvlLe 1` から出る)。 -/
theorem argStd72 (w : Nat) (c : B) (hl : lvlLe 1 c = true) (hn : nonIncr c = true)
    (hv : visOK w c c = true) (hs : stdIn c = true) :
    BT.isStd (BT.D w (bArg w c)) = true :=
  argStd72aux (sizeB c + 1) w c (Nat.lt_succ_self _) hl hn hv hs

/-- 段が 1 以下なら `nfLe m` は `1 ≤ m` のとき自動。 -/
theorem nfLe_of_lvlLe72 : ∀ (c : B) (m : Nat), 1 ≤ m → lvlLe 1 c = true → nfLe m c = true
  | .nil, _, _, _ => rfl
  | .nd v r a, m, hm, h => by
    obtain ⟨h1, h2, h3⟩ := (lvlLe_nd_iff 1 v r a).mp h
    exact (nfLe_nd_iff m v r a).mpr
      ⟨by omega, nfLe_of_lvlLe72 r m hm h2, nfLe_of_lvlLe72 a (v + 1) (by omega) h3⟩

end

/-! ### §72.5 第二の門を段 1 以下に絞る (還元のみ、証明はしない) -/

section
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! `btLe72` — `BT` の側の添字の上限 — は `Evidence/Index.lean` で**定義**してある
    (`Trans.Dict` しか要らないので)。その性質はここで証明する。 -/

theorem btLe72_D (m u : Nat) (a : BT) (h : btLe72 m (BT.D u a) = true) :
    u ≤ m ∧ btLe72 m a = true := by
  obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
  exact ⟨of_decide_eq_true h1, h2⟩

theorem btLe72_sum (m : Nat) (a b : BT) (h : btLe72 m (BT.sum a b) = true) :
    btLe72 m a = true ∧ btLe72 m b = true := (Bool.and_eq_true _ _).mp h

theorem btLe72_ofL72 : ∀ (l : List BT), (∀ x ∈ l, btLe72 1 x = true) →
    btLe72 1 (BT.ofL l) = true
  | [], _ => rfl
  | [a], h => h a (List.mem_cons.mpr (Or.inl rfl))
  | a :: y :: r, h => by
    show (btLe72 1 a && btLe72 1 (BT.ofL (y :: r))) = true
    rw [h a (List.mem_cons.mpr (Or.inl rfl)),
      btLe72_ofL72 (y :: r) (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))]
    rfl

theorem btLe72_bArg72 : ∀ (n w : Nat) (c : B), sizeB c < n → lvlLe 1 c = true →
    btLe72 1 (bArg w c) = true
  | 0, _, _, hsz, _ => absurd hsz (Nat.not_lt_zero _)
  | n + 1, w, c, hsz, hl => by
    rw [ofL_bArg72 w c hl]
    refine btLe72_ofL72 _ ?_
    intro x hx
    obtain ⟨q, hqm, hq⟩ := List.mem_map.mp hx
    rw [← hq]
    obtain ⟨hu, hlq⟩ := lvlL72_of_lvlLe c hl q hqm
    have hsz2 : sizeB q.2 < n := by have := sizeB_mem72 c q hqm; omega
    show (decide (q.1 ≤ 1) && btLe72 1 (bArg q.1 q.2)) = true
    rw [decide_eq_true hu, btLe72_bArg72 n q.1 q.2 hsz2 hlq]
    rfl

/-- **部分領域の値の成分は添字が 1 以下。** -/
theorem btLe_bVal_mem72 : ∀ (t : B), lvlLe 1 t = true →
    ∀ a ∈ (bVal t).toL, btLe72 1 a = true
  | .nil, _, _, ha => by cases ha
  | .nd v r c, hl, a, ha => by
    obtain ⟨hv, hlr, hlc⟩ := (lvlLe_nd_iff 1 v r c).mp hl
    rw [toL_bVal_nd v r c] at ha
    rcases List.mem_append.mp ha with h | h
    · exact btLe_bVal_mem72 r hlr a h
    · by_cases hcc : (r == .nil && v == 0 && c == .nil) = true
      · rw [if_pos hcc] at h; cases h
      · rw [if_neg hcc, List.mem_singleton] at h
        rw [h]
        show (decide (v ≤ 1) && btLe72 1 (bArg v c)) = true
        rw [decide_eq_true hv, btLe72_bArg72 (sizeB c + 1) v c (Nat.lt_succ_self _) hlc]
        rfl

/-- **第二の門、段 1 以下の形。** §66.4 の `PsiIdxOKStd` を、添字も引数も段 1 以下の
    ところに絞ったもの。**証明しない** (§72.8 で測定のみ)。 -/
def PsiIdxOKStd172 : Prop :=
  ∀ (u : Nat) (a : BT), u ≤ 1 → btLe72 1 a = true → BT.isStd (BT.D u a) = true →
    PsiIdxOK u (dict a)

/-- **その一歩ぶんの形。** §68.3 の `PsiIdxStepStd` を同じところに絞ったもの。 -/
def PsiIdxStepStd172 : Prop :=
  ∀ (u : Nat) (a : BT), u ≤ 1 → btLe72 1 a = true → BT.isStd (BT.D u a) = true →
    KsetStepOK u (dict a)

theorem inT_dict_of_step172 (H : PsiIdxStepStd172) : ∀ a : BT, btLe72 1 a = true →
    BT.isStd a = true → inT (dict a) = true ∧ lt (dict a) M = true
  | .zero, _, _ => ⟨inT_zero, lt_zero_M⟩
  | .D u a, hb, h => by
    obtain ⟨hu, hba⟩ := btLe72_D 1 u a hb
    have ih := inT_dict_of_step172 H a hba (isStd_of_D h)
    exact inT_collapse_gap3 u (dict a) ih.1 ih.2
      (psiIdxOK_of_stepOK u (dict a) ih.1 ih.2 (H u a hu hba h))
  | .sum a b, hb, h => by
    obtain ⟨hba, hbb⟩ := btLe72_sum 1 a b hb
    have iha := inT_dict_of_step172 H a hba (isStd_of_sum h).1
    have ihb := inT_dict_of_step172 H b hbb (isStd_of_sum h).2
    exact ⟨inT_plus iha.1 ihb.1, lt_plus_M iha.1 ihb.1 iha.2 ihb.2⟩

/-- 一歩ぶんの形から §72.7 の門が出る。 -/
theorem psiIdxOKStd172_of_step172 (H : PsiIdxStepStd172) : PsiIdxOKStd172 := by
  intro u a hu hb h
  have ih := inT_dict_of_step172 H a (btLe72_D 1 u a (by
    show (decide (u ≤ 1) && btLe72 1 a) = true
    rw [decide_eq_true hu, hb]
    rfl)).2 (isStd_of_D h)
  exact psiIdxOK_of_stepOK u (dict a) ih.1 ih.2 (H u a hu hb h)

/-- §66.4 の無制限の形から絞った形が出る (向きの記録)。 -/
theorem psiIdxOKStd172_of_std (H : PsiIdxOKStd) : PsiIdxOKStd172 :=
  fun u a _ _ h => H u a h

theorem inT_dict_of_std172 (H : PsiIdxOKStd172) : ∀ a : BT, btLe72 1 a = true →
    BT.isStd a = true → inT (dict a) = true ∧ lt (dict a) M = true
  | .zero, _, _ => ⟨inT_zero, lt_zero_M⟩
  | .D u a, hb, h => by
    obtain ⟨hu, hba⟩ := btLe72_D 1 u a hb
    have ih := inT_dict_of_std172 H a hba (isStd_of_D h)
    exact inT_collapse_gap3 u (dict a) ih.1 ih.2 (H u a hu hba h)
  | .sum a b, hb, h => by
    obtain ⟨hba, hbb⟩ := btLe72_sum 1 a b hb
    have iha := inT_dict_of_std172 H a hba (isStd_of_sum h).1
    have ihb := inT_dict_of_std172 H b hbb (isStd_of_sum h).2
    exact ⟨inT_plus iha.1 ihb.1, lt_plus_M iha.1 ihb.1 iha.2 ihb.2⟩

end

/-! ### §72.6 消費者 — `RegionStd` は部分領域で無条件 -/

section
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (BT)
open TM TM.Term
open Trans.Dict (dict)

/-- **`RegionStd` を部分領域に絞った形。** -/
def RegionStd172 : Prop := ∀ t : B, stdB1 t = true → ∀ a ∈ (bVal t).toL, BT.isStd a = true

theorem regionStd1_aux72 : ∀ (t : B), lvlLe 1 t = true → stdIn t = true →
    ∀ a ∈ (bVal t).toL, BT.isStd a = true := by
  intro t
  induction t with
  | nil => intro _ _ a ha; cases ha
  | nd v r c ihr _ =>
    intro hl hst a ha
    obtain ⟨_, hlr, hlc⟩ := (lvlLe_nd_iff 1 v r c).mp hl
    obtain ⟨hstr, hnc, hvis, hstc⟩ := stdIn_nd hst
    rw [toL_bVal_nd v r c] at ha
    rcases List.mem_append.mp ha with h | h
    · exact ihr hlr hstr a h
    · by_cases hc : (r == .nil && v == 0 && c == .nil) = true
      · rw [if_pos hc] at h; cases h
      · rw [if_neg hc, List.mem_singleton] at h
        rw [h]
        exact argStd72 v c hlc hnc hvis hstc

/-- **§72 の第一の門、消費者の形。** §67 の `RegionStd` は部分領域では**定理**。 -/
theorem regionStd1_72 : RegionStd172 := by
  intro t ht a ha
  have h1 : stdB t = true := stdB_of_stdB1 t ht
  have h2 : ((nfB t && nonIncr t) && stdIn t) = true := h1
  exact regionStd1_aux72 t (lvlLe1_of_stdB1 t ht) ((Bool.and_eq_true _ _).mp h2).2 a ha

theorem dictAtoms_bVal_72 (Hp : PsiIdxOKStd172) (t : B) (ht : stdB1 t = true) :
    ∀ a ∈ (bVal t).toL, inT (dict a) = true :=
  fun a ha => (inT_dict_of_std172 Hp a (btLe_bVal_mem72 t (lvlLe1_of_stdB1 t ht) a ha)
    (regionStd1_72 t ht a ha)).1

theorem inT_dict_bVal_72 (Hp : PsiIdxOKStd172) (t : B) (ht : stdB1 t = true) :
    inT (dict (bVal t)) = true := by
  have h := inT_dict_ofL (bVal t).toL (dictAtoms_bVal_72 Hp t ht)
  rwa [show BT.ofL (bVal t).toL = bVal t from nfSum_bVal t] at h

/-- **部分領域の値は 𝔗(M) の項** — 仮説は `PsiIdxOKStd172` ただ一つ。 -/
theorem inT_vOf_72 (Hp : PsiIdxOKStd172) (t : B) (ht : stdB1 t = true) :
    inT (vOf t) = true := by
  cases t with
  | nil => exact rfl
  | nd w r c =>
    show inT (plus one (dict (bVal (B.nd w r c)))) = true
    exact inT_plus inT_one (inT_dict_bVal_72 Hp _ ht)

theorem vOf_succ_72 (Hp : PsiIdxOKStd172) (r : B) (hr : stdB1 r = true) :
    vOf (.nd 0 r .nil) = plus (vOf r) one := by
  cases r with
  | nil => exact rfl
  | nd w s c =>
    show plus one (dict (bVal (B.nd 0 (B.nd w s c) B.nil)))
        = plus (plus one (dict (bVal (B.nd w s c)))) one
    rw [show bVal (B.nd 0 (B.nd w s c) B.nil)
          = bplus (bVal (B.nd w s c)) (BT.D 0 BT.zero) from rfl,
      dict_bplus_one _ (nfSum_bVal _) (dictAtoms_bVal_72 Hp _ hr)]
    exact (plus_assoc_inT _ _ _ inT_one (inT_dict_bVal_72 Hp _ hr) inT_one).symm

theorem lt_vOf_succ_72 (Hp : PsiIdxOKStd172) (r : B) (hr : stdB1 r = true) :
    lt (vOf r) (vOf (.nd 0 r .nil)) = true := by
  rw [vOf_succ_72 Hp r hr]
  exact lt_self_plus_one_inT (vOf r) (inT_vOf_72 Hp r hr)

end

/-! ### §72.7 組み立て — `certIn_t326` から `RegionStd` を外す -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- **`Hsucc` の供給、部分領域で。** 仮説は `PsiIdxOKStd172` だけ。§70 の
    `hsuccS1_supply_std` から `RegionStd` が落ちた形。 -/
theorem hsuccS1_supply_72 (Hp : PsiIdxOKStd172) :
    ∀ (S : BMS.Matrix) (v : TM.Term), RegS1 S → ValS1 S v → BMS.kind S = BMS.Kind.succ →
    ∃ u, v = plus u TM.Term.one ∧ inT v = true ∧ inT u = true ∧ lt u v = true
         ∧ ∀ n, ValS1 (BMS.expand S n) u := by
  rintro S v _ ⟨t, hstd, rfl, rfl⟩ hk
  rw [kind_matB t] at hk
  obtain ⟨r, rfl⟩ := kindB_succ t hk
  have hstd' : stdB (B.nd 0 r .nil) = true := stdB_of_stdB1 _ hstd
  have hr1 : stdB1 r = true := stdB1_pred r hstd
  have htop : topOKB (B.nd 0 r .nil) = true := topOKB_of_nfB _ (nfB_of_stdB _ hstd')
  have hexp : ∀ n, BMS.expand (matB (B.nd 0 r .nil) 0) n = matB r 0 := by
    intro n
    show (BMS.expand? (matB (B.nd 0 r .nil) 0) n).getD [] = _
    rw [expand_matB (B.nd 0 r .nil) htop (by intro h; exact B.noConfusion h) n]
    rfl
  exact ⟨vOf r, vOf_succ_72 Hp r hr1, inT_vOf_72 Hp _ hstd,
    inT_vOf_72 Hp r hr1, lt_vOf_succ_72 Hp r hr1,
    fun n => ⟨r, hr1, hexp n, rfl⟩⟩

/-- **`Hlim` の供給、部分領域で。** 仮説は `PsiIdxOKStd172` と §70.5 の 3 つ。 -/
theorem hlimS1_supply_72 (Hp : PsiIdxOKStd172)
    (HD : LimDecS1) (HI : LimIncS1) (HC : LimCofS1) :
    ∀ (S : BMS.Matrix) (v : TM.Term), RegS1 S → ValS1 S v → BMS.kind S = BMS.Kind.lim →
    ∃ f : Nat → TM.Term, inT v = true
      ∧ (∀ n, ValS1 (BMS.expand S n) (f n))
      ∧ (∀ n, inT (f n) = true)
      ∧ (∀ n, lt (f n) v = true)
      ∧ (∀ n, lt (f n) (f (n + 1)) = true)
      ∧ (∀ s, inT s = true → lt s v = true → ∃ n, le s (f n) = true) := by
  rintro S v _ ⟨t, hstd, rfl, rfl⟩ hk
  rw [kind_matB t] at hk
  exact ⟨fun n => vOf (fsB t n), inT_vOf_72 Hp t hstd,
    valS1_expand t hstd hk,
    fun n => inT_vOf_72 Hp _ (stdB1_fsB t hstd n),
    HD t hstd hk, HI t hstd hk, HC t hstd hk⟩

/-- **輪が閉じる形、`RegionStd` 抜き。** 仮説は 4 つ。 -/
theorem certInS1_72 (Hp : PsiIdxOKStd172)
    (HD : LimDecS1) (HI : LimIncS1) (HC : LimCofS1) :
    ∀ (v : TM.Term), Acc Evidence.WF.RT v → ∀ (S : BMS.Matrix), RegS1 S → ValS1 S v →
      Evidence.Cert.CertifiedIn Evidence.Cert.DomI S v :=
  Evidence.Cert.certIn_region hclosedS1_supply hzeroS1_supply (hsuccS1_supply_72 Hp)
    (hlimS1_supply_72 Hp HD HI HC)

/-- **§72 の結論。** 326 行目の証明書は `RegionStd` に依らない。残る仮説は
    `PsiIdxOKStd172` と `LimDecS1`・`LimIncS1`・`LimCofS1`、それに停止性。 -/
theorem certIn_t326_72 (Hp : PsiIdxOKStd172)
    (HD : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certInS1_72 Hp HD HI HC (vOf t326) hacc (matB t326 0) ⟨t326, stdB1_t326, rfl⟩
    ⟨t326, stdB1_t326, rfl, rfl⟩

/-- **一歩ぶんの形からも同じ。** §68.4 の `inT_vOf_68` の段 1 以下の形。 -/
theorem inT_vOf_step72 (Hs : PsiIdxStepStd172) (t : B) (ht : stdB1 t = true) :
    inT (vOf t) = true :=
  inT_vOf_72 (psiIdxOKStd172_of_step172 Hs) t ht

/-- §68.4 の `hsuccS_supply_68` の段 1 以下の形。`ArgStd` はもう仮説ではない。 -/
theorem hsuccS1_supply_step72 (Hs : PsiIdxStepStd172) :
    ∀ (S : BMS.Matrix) (v : TM.Term), RegS1 S → ValS1 S v → BMS.kind S = BMS.Kind.succ →
    ∃ u, v = plus u TM.Term.one ∧ inT v = true ∧ inT u = true ∧ lt u v = true
         ∧ ∀ n, ValS1 (BMS.expand S n) u :=
  hsuccS1_supply_72 (psiIdxOKStd172_of_step172 Hs)

/-- **§72 の結論、一歩ぶんの形で。** 326 行目の証明書は `PsiIdxStepStd172` と
    §70.5 の 3 つと停止性だけに依る。 -/
theorem certIn_t326_step72 (Hs : PsiIdxStepStd172)
    (HD : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_72 (psiIdxOKStd172_of_step172 Hs) HD HI HC hacc

end

/-! ### §72.7b 和の形 — §67.2 の `RegionStdSum` も部分領域では定理

消費者が要るのは成分ごとの標準性 (`RegionStd`) だけだが、和そのものの標準性も出る。
`bVal` の成分列は `toL t` の `map` から**先頭の `(0, nil)` を落としただけ**。 -/

section
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (BT)
open TM TM.Term

/-- 先頭が `(0, nil)` ならそれを落とす。`bVal` が先頭の `(0,0)` を 0 にする分。 -/
def dropHd72 : List (Nat × B) → List (Nat × B)
  | (0, .nil) :: r => r
  | l => l

theorem dropHd72_sub : ∀ (l : List (Nat × B)) (q : Nat × B), q ∈ dropHd72 l → q ∈ l
  | (0, .nil) :: _, _, hq => List.mem_cons.mpr (Or.inr hq)
  | [], _, hq => hq
  | (0, .nd _ _ _) :: _, _, hq => hq
  | (_ + 1, _) :: _, _, hq => hq

theorem nonIncrL_dropHd72 : ∀ (l : List (Nat × B)), nonIncrL l = true →
    nonIncrL (dropHd72 l) = true
  | (0, .nil) :: r, h => ((Bool.and_eq_true _ _).mp h).2
  | [], h => h
  | (0, .nd _ _ _) :: _, h => h
  | (_ + 1, _) :: _, h => h

theorem dropHd72_snoc : ∀ (l : List (Nat × B)) (x : Nat × B), l ≠ [] →
    dropHd72 (l ++ [x]) = dropHd72 l ++ [x]
  | [], _, hn => absurd rfl hn
  | (0, .nil) :: r, x, _ => rfl
  | (0, .nd _ _ _) :: _, _, _ => rfl
  | (_ + 1, _) :: _, _, _ => rfl

/-- **`bVal` の成分列。** `toL t` の `map` から先頭の `(0, nil)` を落としたもの。 -/
theorem toL_bVal72 : ∀ (t : B), (bVal t).toL = (dropHd72 (toL t)).map fB72
  | .nil => rfl
  | .nd v r c => by
    rw [toL_bVal_nd v r c, toL_nd]
    cases hr : r with
    | nil =>
      rw [show toL (B.nil) = ([] : List (Nat × B)) from rfl, List.nil_append,
        show (bVal B.nil).toL = ([] : List BT) from rfl, List.nil_append]
      by_cases hc : ((B.nil : B) == .nil && v == 0 && c == .nil) = true
      · obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hc
        obtain ⟨_, h3⟩ := (Bool.and_eq_true _ _).mp h1
        rw [if_pos hc, show v = 0 from of_decide_eq_true h3,
          show c = B.nil from of_decide_eq_true h2]
        rfl
      · rw [if_neg hc]
        cases v with
        | zero =>
          cases c with
          | nil => exact absurd rfl hc
          | nd u s b => rfl
        | succ k => rfl
    | nd u s b =>
      rw [if_neg (show ¬ ((B.nd u s b : B) == .nil && v == 0 && c == .nil) = true from by
        intro hcon
        obtain ⟨h1, _⟩ := (Bool.and_eq_true _ _).mp hcon
        obtain ⟨h2, _⟩ := (Bool.and_eq_true _ _).mp h1
        exact B.noConfusion (of_decide_eq_true h2))]
      rw [dropHd72_snoc (toL (B.nd u s b)) (v, c) (toL_ne_nil u s b), List.map_append,
        toL_bVal72 (B.nd u s b)]
      rfl

/-- **§67.2 の `RegionStdSum` の部分領域版。** 消費者より強い形。 -/
theorem regionStdSum1_72 : ∀ (t : B), stdB1 t = true → BT.isStd (bVal t) = true := by
  intro t ht
  have hl : lvlLe 1 t = true := lvlLe1_of_stdB1 t ht
  have hs' : ((nfB t && nonIncr t) && stdIn t) = true := stdB_of_stdB1 t ht
  have hst : stdIn t = true := ((Bool.and_eq_true _ _).mp hs').2
  have hni : nonIncr t = true := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hs').1).2
  have hlv : LvlL72 (dropHd72 (toL t)) :=
    fun q hq => lvlL72_of_lvlLe t hl q (dropHd72_sub (toL t) q hq)
  have hx : bVal t = BT.ofL ((dropHd72 (toL t)).map fB72) := by
    rw [← toL_bVal72 t]
    exact (nfSum_bVal t).symm
  rw [hx]
  refine isStd_ofL72 _ ?_ ?_ (descOK_map72 (dropHd72 (toL t)) hlv (nonIncrL_dropHd72 (toL t) hni))
  · intro z hz
    obtain ⟨q, _, hq⟩ := List.mem_map.mp hz
    exact ⟨q.1, bArg q.1 q.2, hq.symm⟩
  · intro z hz
    obtain ⟨q, hqm, hq⟩ := List.mem_map.mp hz
    rw [← hq]
    have hqt := dropHd72_sub (toL t) q hqm
    obtain ⟨hnq, hvq, hsq⟩ := stdIn_mem72 t hst q hqt
    exact argStd72 q.1 q.2 (lvlL72_of_lvlLe t hl q hqt).2 hnq hvq hsq

end

/-! ### §72.8 三つの仮説はどれも外せない (段 1 以下でも)

`nfLe` は `lvlLe 1` から出るので外れた (`nfLe_of_lvlLe72`)。残る三つは段 1 以下でも
外せない。`cVis`・`cInc` は §68.2b のものがそのまま段 1 以下で、`stdIn` の反例だけ
新しい — §68 の `cStd` は段 2 の節を持つ。 -/

section
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (BT)
open TM TM.Term

/-- `stdIn` を外す反例、段 1 以下。行列 `(0,1)(1,1)(1,1)(2,1)`、値 `ψ₁(ψ₁(1 ⊕ Ω₁))` の形。
    引数の和 `Ω₁ ⊕ ψ₁(Ω₁)` が降べきでない。 -/
def cStd72 : B := .nd 1 .nil (.nd 1 (.nd 1 .nil .nil) (.nd 1 .nil .nil))

theorem matB_cStd72 : matB cStd72 0 = [[0,1],[1,1],[1,1],[2,1]] := rfl

theorem not_argStd72_no_visOK :
    ¬ (∀ (w : Nat) (c : B), lvlLe 1 c = true → nonIncr c = true → stdIn c = true →
        BT.isStd (BT.D w (bArg w c)) = true) := fun H =>
  Bool.noConfusion ((H 0 cVis rfl rfl rfl).symm.trans
    (show BT.isStd (BT.D 0 (bArg 0 cVis)) = false from rfl))

theorem not_argStd72_no_nonIncr :
    ¬ (∀ (w : Nat) (c : B), lvlLe 1 c = true → visOK w c c = true → stdIn c = true →
        BT.isStd (BT.D w (bArg w c)) = true) := fun H =>
  Bool.noConfusion ((H 0 cInc rfl visOK_cInc rfl).symm.trans
    (show BT.isStd (BT.D 0 (bArg 0 cInc)) = false from rfl))

theorem not_argStd72_no_stdIn :
    ¬ (∀ (w : Nat) (c : B), lvlLe 1 c = true → nonIncr c = true → visOK w c c = true →
        BT.isStd (BT.D w (bArg w c)) = true) := fun H =>
  Bool.noConfusion ((H 0 cStd72 rfl rfl rfl).symm.trans
    (show BT.isStd (BT.D 0 (bArg 0 cStd72)) = false from rfl))

end

/-! ### §72.9 測定 (凍結)

母集団の作り方を先に書く。

    pool72 n   = ((List.range (n+1)).flatMap (enumNodes 2))
                 — 節が `n` 個以下、段が **0 か 1 だけ**の `B` を全部。`topOKB` でも
                   `nfB` でも絞らない。`ArgStd` が量化しているのは添字の全体ではなく
                   **一つの節の引数**なので、絞ってはいけない。
    good72 w c = lvlLe 1 c && nonIncr c && visOK w c c && stdIn c
    btPool72   = dg72 (sg72 (dg72 (sg72 (dg72 [zero]))))  ただし
                 dg72 l = l ++ {ψ₀ a, ψ₁ a : a ∈ l}、sg72 l = l ++ {a ⊕ b : a,b ∈ l}
                 — 添字が 0 か 1 だけの `BT` を 3519 個。`isStd` で絞らずに作る。
    sub72 n    = (popNFB 2 n).filter stdB1   — §70.6 の `subP` と同じもの。
    regPairs72 l = l の値 `bVal t` の成分の中に現れる `ψ_u a` を対 `(u, a)` として全部。
    exp72      = t326 の基本列を 2 回まで適用したもの 36 個 (最大 44 節)。 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

def pool72 (n : Nat) : List B := (List.range (n+1)).flatMap (enumNodes 2)
def good72 (w : Nat) (c : B) : Bool := lvlLe 1 c && nonIncr c && visOK w c c && stdIn c
def dg72 (l : List BT) : List BT := (l ++ l.flatMap fun a => [BT.D 0 a, BT.D 1 a]).eraseDups
def sg72 (l : List BT) : List BT := (l ++ l.flatMap fun a => l.map fun b => BT.sum a b).eraseDups
def btPool72 : List BT := dg72 (sg72 (dg72 (sg72 (dg72 [BT.zero]))))
def pairs72 : BT → List (Nat × BT)
  | .zero => []
  | .D u a => (u, a) :: pairs72 a
  | .sum a b => pairs72 a ++ pairs72 b
def regPairs72 (l : List B) : List (Nat × BT) :=
  (l.flatMap fun t => (bVal t).toL.flatMap pairs72).eraseDups
def sub72 (n : Nat) : List B := (popNFB 2 n).filter stdB1
def exp72 : List B :=
  ((List.range 6).flatMap fun n => (List.range 6).map fun m => fsB (fsB t326 n) m).eraseDups
/-- 走査のうち強臨界枝を取る歩数 — `KsetStepOK` が条件を課す唯一の枝。 -/
def scFire72 (u : Nat) (x : Term) : Nat :=
  ((scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1).filter
    (fun p => le (reg (u+1)) p.2.1)).length
def scLen72 (u : Nat) (x : Term) : Nat :=
  (scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1).length

-- 母集団の大きさ。
#guard (pool72 4).length == 275
#guard (pool72 5).length == 1619
#guard (pool72 7).length == 64979
#guard ((pool72 7).filter (good72 0)).length == 5744
#guard ((pool72 7).filter (good72 1)).length == 9135

/-! **肯定 1 — §72.1 の潰れなさ。** `w` を 4 まで振って 64979 本すべてで成分列は `map`。 -/

#guard ((pool72 7).filter fun c =>
  !((List.range 5).all fun w => (bArg w c).toL == (toL c).map fB72)).length == 0

/-! **肯定 2 — §72.2 の移送は順序同型。** 段 1 以下の木の**すべての**順序対で、良さの
仮定を一切置かずに `cmpS = lt` と `BT.lt` が一致する。275² = 75 625 対、うち `lt` は
37 675 対 (空回りしていない)。1619² = 2 621 161 対でも食い違い 0 (重いので凍結しない)。 -/

#guard ((pool72 4).flatMap fun c1 => (pool72 4).filter fun c2 =>
  ((cmpS (toL c1) (toL c2) == Ordering.lt) != BT.lt (bArg 0 c1) (bArg 0 c2))).length == 0
#guard ((pool72 4).flatMap fun c1 => (pool72 4).filter fun c2 =>
  cmpS (toL c1) (toL c2) == Ordering.lt).length == 37675

/-! **肯定 3 — §72.3 と §72.4 そのもの。** 良い木の上で `key72` も `argStd72` も 0 失敗
(定理なので当然だが、判定器と定義の食い違いの検査になる)。 -/

#guard ((pool72 7).filter fun c => good72 0 c &&
  !((nodes72 c).all fun q => cmpS (toL q.2) (toL c) == Ordering.lt)).length == 0
#guard ((pool72 7).filter fun c => good72 0 c && !(BT.isStd (BT.D 0 (bArg 0 c)))).length == 0
#guard ((pool72 7).filter fun c => good72 1 c && !(BT.isStd (BT.D 1 (bArg 1 c)))).length == 0
#guard ((pool72 7).filter fun c => good72 2 c && !(BT.isStd (BT.D 2 (bArg 2 c)))).length == 0

/-! **否定 1 — 三つの仮説はどれも外せない。** 最小の反例の節数は 2・2・3。
(`not_argStd72_no_stdIn` が使う `cStd72` は 4 節。3 節の最小反例 `(0,0)(1,0)(1,1)` は
`visOK` の中の `cmpS` が簡約しないので、定理にするには手で展開が要る。) -/

#guard (((pool72 7).filter fun c => lvlLe 1 c && nonIncr c && stdIn c
  && !(BT.isStd (BT.D 0 (bArg 0 c)))).map sizeB).foldl (fun a b => min a b) 99 == 2
#guard (((pool72 7).filter fun c => lvlLe 1 c && visOK 0 c c && stdIn c
  && !(BT.isStd (BT.D 0 (bArg 0 c)))).map sizeB).foldl (fun a b => min a b) 99 == 2
#guard (((pool72 7).filter fun c => lvlLe 1 c && nonIncr c && visOK 0 c c
  && !(BT.isStd (BT.D 0 (bArg 0 c)))).map sizeB).foldl (fun a b => min a b) 99 == 3

/-! **否定 2 — 段 1 以下でも強臨界枝は firing する。** 「段を 1 に絞れば `KsetStepOK` は
空回りする」という期待は**偽**。部分領域自身の値の 1908 個の `ψ` 対で、走査は 1614 歩、
そのうち 335 歩が強臨界枝を取る。ただし `t326` の基本列 (36 個, 最大 44 節) の側では
0 歩 — 行 326 の周りだけを見ると空回りに見えてしまう。 -/

#guard (sub72 8).length == 2397
#guard (regPairs72 (sub72 8)).length == 1908
#guard (regPairs72 (sub72 8)).all fun q => q.1 ≤ 1
#guard ((regPairs72 (sub72 8)).map fun q => scLen72 q.1 (dict q.2)).foldl (· + ·) 0 == 1614
#guard ((regPairs72 (sub72 8)).map fun q => scFire72 q.1 (dict q.2)).foldl (· + ·) 0 == 335
#guard exp72.length == 36
#guard exp72.all stdB1
#guard (exp72.map sizeB).foldl (fun a b => max a b) 0 == 44
#guard (regPairs72 exp72).length == 40
#guard ((regPairs72 exp72).map fun q => scFire72 q.1 (dict q.2)).foldl (· + ·) 0 == 0

/-! **肯定 4 — (S1'') `PsiIdxStepStd172`。** 二つの母集団で 0 失敗。添字は 5 まで振った
(要るのは 1 まで)。btPool72 は `isStd` で絞らずに作ってから `isStd (ψ_u a)` で選ぶ。 -/

#guard btPool72.length == 3519
#guard ((List.range 6).flatMap fun u =>
  btPool72.filter fun a => BT.isStd (BT.D u a)).length == 1767
#guard ((List.range 6).flatMap fun u =>
  btPool72.filter fun a => BT.isStd (BT.D u a) && !(stepOKb u (dict a))).length == 0
#guard ((regPairs72 (sub72 8)).filter fun q => !(BT.isStd (BT.D q.1 q.2))).length == 0
#guard ((regPairs72 (sub72 8)).filter fun q => !(stepOKb q.1 (dict q.2))).length == 0
#guard ((regPairs72 exp72).filter fun q => !(stepOKb q.1 (dict q.2))).length == 0

/-! **肯定 5 — 段 1 以下の `BT` の上限は値から出る。** 部分領域の値の成分の添字は 1 以下。 -/

#guard (sub72 8).all fun t => (bVal t).toL.all (btLe72 1)
#guard exp72.all fun t => (bVal t).toL.all (btLe72 1)

end

/-! ### §72.10 公理 -/

/-! ## §71 DECREASING AND INCREASING ARE THEOREMS ON THE LEVEL-ONE SUB-REGION —
    THE PREFIX IS GONE, THE COLLAPSE NEVER FIRES, AND COFINALITY SPLITS WHERE §69 FELL

§70 cut the region down to `stdB1 t = stdB t && lvlLe 1 t`, proved it closed under `fsB`,
put row 326 inside it, and left `certIn_t326` standing on five hypotheses: §67's
`PsiIdxOKStd` / `RegionStd` (§68's job) and §70.5's `LimDecS1` / `LimIncS1` / `LimCofS1`.
§71 is about those last three.  **Two of them stop being open problems.**  On the
sub-region the Buchholz-side halves of `LimDecS1` and `LimIncS1` are PROVED here, with no
hypothesis at all, so each of those two clauses now rests on ONE measured statement — the
order bridge `VOfLtA71` — and on nothing else.  The third, `LimCofS1`, is split into the
half §69 swept and the half §69 did not.

WHAT IS PROVED, UNCONDITIONALLY.

  §71.1  **THE FUNDAMENTAL SEQUENCE DOES NOT TOUCH THE PREFIX.**  `fsB_appB71` —

             a ≠ nil  ⟹  fsB (nd v r a) n = appB r (fsB (nd v nil a) n)

         for EVERY `v`, `r`, `a`, `n`, with no normal form and no standardness.  All three
         of `fsB`'s operators (`repB`, `rwB` through `iterD`/`plugB`, and dropping a leaf)
         rebuild the node they are applied to and copy the prefix verbatim.  This is
         `Evidence/RegionV.lean` §14's `sumVal_fs_lim` — the seam that let the SMALL region
         reduce `Hlim` to its last summand — now at the generalised index, where §14's `A`
         had no analogue.  `fsB_ne_nil71` is the unfolding equation it needs.

  §71.2  **THE PREFIX CANCELS IN THE BUCHHOLZ ORDER.**  `bValA71` is `bVal` without the
         leading-`(0,0)` exception — the Buchholz-side reading of `vOf`'s `1 +`.  Its
         component list is a homomorphism for `appB` with NO side condition
         (`toL_bValA71_appB71`), `ltS_append_left71` cancels a common prefix of `BT.ltL`
         (§68.1's `ltS_cons` with equal heads), and together

             lt_bValA71_appB71 :  BT.lt (bValA71 (appB r s₁)) (bValA71 (appB r s₂))
                                    = BT.lt (bValA71 s₁) (bValA71 s₂)

         again for every `r`, `s₁`, `s₂`.  `toL_bVal_appB71` is the same statement for `bVal`
         itself and does carry `r ≠ nil` — that side condition IS the leading-`(0,0)`
         exception, which is why `bValA71` and not `bVal` is the right object here.
         Measured: `bValA71 ≠ bVal` on exactly 7 of `subP 8`'s 2397 indices, and those 7 are
         the all-`(0,0)` matrices, i.e. the natural numbers.

  §71.3  **THE TWO ORDER CLAUSES LOSE THEIR PREFIX.**  `blimDecA71_of_core71` /
         `blimIncA71_of_core71`: the Buchholz-side clauses on the WHOLE sub-region follow
         from the same clauses on PREFIX-FREE indices `nd 0 nil a` alone.
         `stdB1_drop_prefix71` is what makes the reduction legal.

  §71.4  **COFINALITY SPLITS INTO THE HALF §69 SWEPT AND THE HALF §69 DID NOT.**
         `limCofS1_of71` proves  `CofDenseS1 ∧ CofInS1 ⟹ LimCofS1`, where `CofDenseS1` says
         every `s ∈ 𝔗(M)` below `vOf t` is `≤` some SUB-REGION value that is still
         `< vOf t`, and `CofInS1` says the fundamental sequence is cofinal in the
         sub-region's own values below `vOf t`.  §69 measured `CofInS1` and reported it as
         `LimCofS`; §70 swept the whole of `LimCofS1` and found nothing.  `cofInS1_of71`
         transports the SECOND half to the Buchholz level through `VOfLtA71'` and the
         linearity of `lt` on 𝔗(M) (`Evidence/WF.lean` §8.4), so cofinality's index-side
         half is `BCofIn71`, a statement with no `dict` in it.  **`CofDenseS1` is where
         𝔗(M) enters and it is NOT reduced.**

  §71.6  **THE COLLAPSE NEVER FIRES BELOW LEVEL 2.**  `bK`'s third branch
         (`bClose ∘ bFold`, §48's fold — the one that turns a run of low children into a
         single `ψ`) is unreachable when every node has level ≤ 1: the guard
         `u ≤ w || !(r == nil) || headLvl c ≤ u` is already true at `u = 0` by its first
         disjunct and at `u = 1` by its third.  Hence

             bArg_eq_bValA71_71 :  lvlLe 1 t  ⟹  bArg w t = bValA71 t   for every w

         — on the sub-region the Buchholz value is a plain nested sum, with no collapsing
         anywhere and no dependence on the ambient level.  **The bound is sharp**: of the
         1291 trees with ≤ 4 nodes and levels < 3, 91 have `bArg 0 t ≠ bValA71 t`, the
         smallest being `(0,1)(1,2) = ψ₁(ψ₂(0))`; of the 10 067 trees with ≤ 6 nodes and
         levels < 2, none does, at `w = 0, 1, 2` alike.

  §71.7  **THE CORES ARE THEOREMS — SO DECREASING AND INCREASING ARE.**  With §71.6 the
         value side of `fsB` can be followed operator by operator:

             `repB`   `lt_bValA71_repNode_dec71` / `_inc71` close the leaf branch outright —
                      `ψ_v(P)` repeated `n+1` times is below `ψ_v(P ⊕ ψ₀0)` because the very
                      first component already decides, and adding one more copy is one more
                      component on the right;
             `plugB`  `lt_bValA71_plugB_dec71` / `_mono71` — replacing the last node by
                      something below `ψ_{lastLvl c}(0)` lowers the value, and does so
                      monotonically;
             `iterD`  the two above give the `rwB` leaf branch;
             `rwB`    `rwB_dec_inc71` carries the invariant `hasLowAnc w c = true ∨ v < w`
                      down the argument chain, and that invariant is exactly what makes
                      `rwB`'s THIRD branch — the one that returns its argument unchanged,
                      where decrease would be false — unreachable.

         `bDecCore71_thm` and `bIncCore71_thm` are the resulting theorems, and
         `blimDecA71_thm` / `blimIncA71_thm` lift them to the whole sub-region through
         §71.3.  Therefore

             limDecS1_of_bridge71 (HV : VOfLtA71) : LimDecS1
             limIncS1_of_bridge71 (HV : VOfLtA71) : LimIncS1

         and `certIn_t326_71'` needs, of §70.5's three, only `VOfLtA71`, `CofDenseS1` and
         `CofInS1`.  **`LimDecS1` and `LimIncS1` are no longer independent hypotheses.**

WHAT THE MEASUREMENT SAYS.  Every population is re-swept on the SUB-region, wider than
§70: `subLim 10` (31 099 limit indices) for decreasing and increasing, `subP 7`'s
609² = 370 881 ordered pairs for the bridge in the form

    BT.lt (bValA71 ·) (bValA71 ·)  =  BT.lt (bVal ·) (bVal ·)  =  lt (vOf ·) (vOf ·)

— an EQUALITY of three Booleans, not an implication — and a new 175 439-term pool of 𝔗(M)
for cofinality (§71.8 gives every construction).  **Zero counterexamples everywhere.**
Nothing was refuted.

WHAT IS **NOT** CLAIMED.  `VOfLtA71`, `VOfLtA71'`, `CofDenseS1`, `CofInS1` and `BCofIn71`
are NAMED AND UNPROVED; so `LimCofS1` is still open and `certIn_t326_71'` still carries
§68's `PsiIdxOKStd` / `RegionStd`.  §71 proves nothing about `dict`: `VOfLtA71` is exactly
the place where `dict` has to preserve the order, and §69's `VOfLtStd` is the same gap in
the un-restricted region.  Nothing here says the table's value at `(0,0)(1,1)(2,2)` is right
or wrong, and nothing here repairs §69 — `LimCofS` is still false OUTSIDE the sub-region.
The proofs of §71.7 use `lvlLe 1` essentially (through §71.6) and say nothing about
level 2, where §69's counterexample lives. -/

/-! ### §71.1 基本列は前置きに触らない

`fsB` の三つの演算はどれも当てられた節を組み直すだけで、前置き `r` はそのまま複写する。
だから前置きは再帰の外に出せる。§14 の `sumVal_fs_lim` に当たるもの。**無条件。** -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- 前置きは `repB` を素通りする。 -/
theorem repB_appB71 : ∀ (v : Nat) (r a : B) (n : Nat), a ≠ .nil →
    repB (.nd v r a) n = appB r (repB (.nd v .nil a) n) := by
  intro v r a n ha
  cases a with
  | nil => exact absurd rfl ha
  | nd u P c =>
    cases u with
    | zero =>
      cases c with
      | nil =>
        show appB r (repNode v P n) = appB r (appB .nil (repNode v P n))
        rw [appB_nil]
      | nd u2 s2 c2 =>
        show B.nd v r (repB (.nd 0 P (.nd u2 s2 c2)) n)
          = appB r (.nd v .nil (repB (.nd 0 P (.nd u2 s2 c2)) n))
        rfl
    | succ u' =>
      show B.nd v r (repB (.nd (u' + 1) P c) n)
        = appB r (.nd v .nil (repB (.nd (u' + 1) P c) n))
      rfl

/-- 前置きは `rwB` を素通りする。 -/
theorem rwB_appB71 : ∀ (w n v : Nat) (r a : B), a ≠ .nil →
    rwB w n (.nd v r a) = appB r (rwB w n (.nd v .nil a)) := by
  intro w n v r a ha
  cases a with
  | nil => exact absurd rfl ha
  | nd u s b =>
    show (if hasLowAnc w (.nd u s b) then B.nd v r (rwB w n (.nd u s b))
          else if v < w then appB r (iterD v (.nd u s b) n) else B.nd v r (.nd u s b))
        = appB r (if hasLowAnc w (.nd u s b) then B.nd v .nil (rwB w n (.nd u s b))
          else if v < w then appB .nil (iterD v (.nd u s b) n) else B.nd v .nil (.nd u s b))
    by_cases hl : hasLowAnc w (.nd u s b) = true
    · rw [if_pos hl, if_pos hl]; rfl
    · rw [if_neg hl, if_neg hl]
      by_cases hv : v < w
      · rw [if_pos hv, if_pos hv, appB_nil]
      · rw [if_neg hv, if_neg hv]; rfl

/-- `fsB` の第 4 枝の展開式。`a ≠ nil` なら段によらずこの形。 -/
theorem fsB_ne_nil71 : ∀ (v : Nat) (r a : B) (n : Nat), a ≠ .nil →
    fsB (.nd v r a) n
      = (if lastLvl a == 0 then repB (.nd v r a) n else rwB (lastLvl a) n (.nd v r a)) := by
  intro v r a n ha
  cases a with
  | nil => exact absurd rfl ha
  | nd u s b => cases v with
    | zero => rfl
    | succ k => rfl

/-- **§71.1 の主定理。** 基本列は前置きに触らない — 最後の加数だけを動かす。
    §14 の `sumVal_fs_lim` の、一般化した添字での対応物。**無条件。** -/
theorem fsB_appB71 (v : Nat) (r a : B) (ha : a ≠ .nil) (n : Nat) :
    fsB (.nd v r a) n = appB r (fsB (.nd v .nil a) n) := by
  rw [fsB_ne_nil71 v r a n ha, fsB_ne_nil71 v .nil a n ha]
  by_cases hz : (lastLvl a == 0) = true
  · rw [if_pos hz, if_pos hz]; exact repB_appB71 v r a n ha
  · rw [if_neg hz, if_neg hz]; exact rwB_appB71 _ n v r a ha

/-- 節を 1 つ足すのは前置きを付けるのと同じ。 -/
theorem nd_eq_appB71 (v : Nat) (r a : B) : B.nd v r a = appB r (.nd v .nil a) := rfl

end

/-! ### §71.2 前置きは Buchholz 側の順序で相殺する

`bVal` は先頭の `(0,0)` だけを 0 に読む (`vOf` の `1 +` の分)。その例外を外したのが
`bValA71` で、こちらは `appB` について**側条件なしで**準同型になる。共通の前置きは
`ltS` を素通りするので、順序は最後の加数だけの話になる。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

theorem bt_beq_self71 : ∀ (a : BT), (a == a) = true := by
  intro a
  induction a with
  | zero => rfl
  | D u b ih => show (u == u && (b == b)) = true; rw [ih, beq_self_eq_true u]; rfl
  | sum p q ihp ihq => show ((p == p) && (q == q)) = true; rw [ihp, ihq]; rfl

theorem bt_eq_of_beq71 : ∀ (a b : BT), (a == b) = true → a = b := by
  intro a
  induction a with
  | zero => intro b h; cases b with
    | zero => rfl
    | D u x => exact Bool.noConfusion h
    | sum p q => exact Bool.noConfusion h
  | D u x ihx => intro b h; cases b with
    | zero => exact Bool.noConfusion h
    | D v y =>
      have h' : ((u == v) && (x == y)) = true := h
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h'
      rw [eq_of_beq h1, ihx y h2]
    | sum p q => exact Bool.noConfusion h
  | sum p q ihp ihq => intro b h; cases b with
    | zero => exact Bool.noConfusion h
    | D v y => exact Bool.noConfusion h
    | sum s t =>
      have h' : ((p == s) && (q == t)) = true := h
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h'
      rw [ihp s h1, ihq t h2]

/-- **前置きの相殺。** 共通の前置きは `ltS` を素通りする。 -/
theorem ltS_append_left71 : ∀ (p : List BT), (∀ z ∈ p, ∃ u a, z = BT.D u a) →
    ∀ (x y : List BT), ltS (p ++ x) (p ++ y) = ltS x y := by
  intro p
  induction p with
  | nil => intro _ x y; rfl
  | cons z p' ih =>
    intro hp x y
    obtain ⟨u, a, rfl⟩ := hp z (List.mem_cons_self ..)
    show ltS (BT.D u a :: (p' ++ x)) (BT.D u a :: (p' ++ y)) = ltS x y
    rw [ltS_cons u a (p' ++ x) u a (p' ++ y), if_neg (Nat.lt_irrefl u),
      if_neg (Nat.lt_irrefl u), if_pos (bt_beq_self71 a)]
    exact ih (fun z hz => hp z (List.mem_cons_of_mem _ hz)) x y

/-- **前置きを付けない値。** `bVal` と違い先頭の `(0,0)` も 1 つの成分として数える。
    `vOf` の `1 +` を Buchholz 側に写したもの。 -/
def bValA71 : B → BT
  | .nil => .zero
  | .nd w r c => bplus (bValA71 r) (BT.D w (bArg w c))

theorem atomsL_bValA71 : ∀ (t : B), AtomsL (bValA71 t)
  | .nil => atomsL_zero
  | .nd w r c => atomsL_bplus _ _ (atomsL_bValA71 r) (atomsL_D w (bArg w c))

theorem toL_bValA71_nd (w : Nat) (r c : B) :
    (bValA71 (.nd w r c)).toL = (bValA71 r).toL ++ [BT.D w (bArg w c)] :=
  toL_bplus _ _ (atomsL_bValA71 r) (atomsL_D w (bArg w c))

theorem appB_ne_nil71 : ∀ (s r : B), r ≠ .nil → appB r s ≠ .nil := by
  intro s
  cases s with
  | nil => intro r hr; exact hr
  | nd v s' a => intro r _ hc; exact B.noConfusion hc

/-- **`bValA71` は `appB` の準同型。側条件は無い。** -/
theorem toL_bValA71_appB71 : ∀ (s r : B),
    (bValA71 (appB r s)).toL = (bValA71 r).toL ++ (bValA71 s).toL := by
  intro s
  induction s with
  | nil => intro r; exact (List.append_nil _).symm
  | nd w s' c ih =>
    intro r
    show (bValA71 (.nd w (appB r s') c)).toL = _
    rw [toL_bValA71_nd w (appB r s') c, ih r, toL_bValA71_nd w s' c, List.append_assoc]

/-- 同じことを `bVal` で。**`r ≠ nil` が要る** — それが先頭の `(0,0)` の例外そのもの。 -/
theorem toL_bVal_appB71 : ∀ (s r : B), r ≠ .nil →
    (bVal (appB r s)).toL = (bVal r).toL ++ (bValA71 s).toL := by
  intro s
  induction s with
  | nil => intro r _; exact (List.append_nil _).symm
  | nd w s' c ih =>
    intro r hr
    have hne : (appB r s' == .nil) = false := by
      cases h : (appB r s' == B.nil) with
      | false => rfl
      | true => exact absurd (eq_of_beq h) (appB_ne_nil71 s' r hr)
    show (bVal (.nd w (appB r s') c)).toL = _
    rw [toL_bVal_nd w (appB r s') c, ih r hr, toL_bValA71_nd w s' c,
      if_neg (show ¬((appB r s' == .nil && w == 0 && c == .nil) = true) from by
        rw [hne]; intro hc; exact Bool.noConfusion hc),
      List.append_assoc]

/-- **§71.2 の主定理。** 共通の前置きの下では Buchholz 側の順序は最後の加数だけの話。
    **無条件、`r = nil` も込み。** -/
theorem lt_bValA71_appB71 (r s1 s2 : B) :
    BT.lt (bValA71 (appB r s1)) (bValA71 (appB r s2)) = BT.lt (bValA71 s1) (bValA71 s2) := by
  rw [lt_eq_ltS, lt_eq_ltS, toL_bValA71_appB71 s1 r, toL_bValA71_appB71 s2 r]
  exact ltS_append_left71 (bValA71 r).toL (atomsL_bValA71 r) _ _

/-- `bVal` の側の同じ主張。前置きが空でないときだけ。 -/
theorem lt_bVal_appB71 (r s1 s2 : B) (hr : r ≠ .nil) :
    BT.lt (bVal (appB r s1)) (bVal (appB r s2)) = BT.lt (bValA71 s1) (bValA71 s2) := by
  rw [lt_eq_ltS, lt_eq_ltS, toL_bVal_appB71 s1 r hr, toL_bVal_appB71 s2 r hr]
  exact ltS_append_left71 (bVal r).toL (atomsL_bVal r) _ _

end

/-! ### §71.3 減少と増加は前置きを失う

`fsB` が前置きを動かさず (§71.1)、前置きが `bValA71` の順序で相殺する (§71.2) ので、
Buchholz 側の 2 つの条項は「前置きの無い添字 `nd 0 nil a`」の話に落ちる。
落とす操作が正当なのは `stdB1_drop_prefix71` — 前置きを外しても標準性と段の上限は残る。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- **前置きは外せる。** 標準で段 1 以下の添字から前置きを外しても標準で段 1 以下。 -/
theorem stdB1_drop_prefix71 (r a : B) (h : stdB1 (.nd 0 r a) = true) :
    stdB1 (.nd 0 .nil a) = true := by
  have hs := stdB_of_stdB1 _ h
  have hl := lvlLe1_of_stdB1 _ h
  have hs' : ((nfB (B.nd 0 r a) && nonIncr (B.nd 0 r a)) && stdIn (B.nd 0 r a)) = true := hs
  obtain ⟨h1, hstdIn⟩ := (Bool.and_eq_true _ _).mp hs'
  obtain ⟨hnf, _⟩ := (Bool.and_eq_true _ _).mp h1
  obtain ⟨_, _, hnfa⟩ := (nfLe_nd_iff 0 0 r a).mp hnf
  obtain ⟨_, hna, hvis, hsta⟩ := stdIn_nd hstdIn
  obtain ⟨_, _, hla⟩ := (lvlLe_nd_iff 1 0 r a).mp hl
  have hnf' : nfB (B.nd 0 B.nil a) = true :=
    (nfLe_nd_iff 0 0 .nil a).mpr ⟨Nat.le_refl 0, rfl, hnfa⟩
  have hni' : nonIncr (B.nd 0 B.nil a) = true := rfl
  have hsi' : stdIn (B.nd 0 B.nil a) = true := by
    show ((stdIn B.nil && nonIncr a && visOK 0 a a) && stdIn a) = true
    rw [hna, hvis, hsta]; rfl
  have hlv' : lvlLe 1 (B.nd 0 B.nil a) = true :=
    (lvlLe_nd_iff 1 0 .nil a).mpr ⟨Nat.zero_le 1, rfl, hla⟩
  show ((nfB (B.nd 0 B.nil a) && nonIncr (B.nd 0 B.nil a) && stdIn (B.nd 0 B.nil a))
    && lvlLe 1 (B.nd 0 B.nil a)) = true
  rw [hnf', hni', hsi', hlv']
  rfl

/-- **前置きの無い添字での減少。** これが `LimDecS1` の核。**未証明** (§71.6 で反例 0)。 -/
def BDecCore71 : Prop := ∀ (a : B) (n : Nat), a ≠ .nil → stdB1 (.nd 0 .nil a) = true →
    BT.lt (bValA71 (fsB (.nd 0 .nil a) n)) (bValA71 (.nd 0 .nil a)) = true

/-- **前置きの無い添字での増加。** **未証明** (§71.6 で反例 0)。 -/
def BIncCore71 : Prop := ∀ (a : B) (n : Nat), a ≠ .nil → stdB1 (.nd 0 .nil a) = true →
    BT.lt (bValA71 (fsB (.nd 0 .nil a) n)) (bValA71 (fsB (.nd 0 .nil a) (n + 1))) = true

/-- 部分領域ぜんぶでの減少 (Buchholz 側)。 -/
def BLimDecA71 : Prop := ∀ (t : B), stdB1 t = true → kindB t = BMS.Kind.lim →
    ∀ n, BT.lt (bValA71 (fsB t n)) (bValA71 t) = true

/-- 部分領域ぜんぶでの増加 (Buchholz 側)。 -/
def BLimIncA71 : Prop := ∀ (t : B), stdB1 t = true → kindB t = BMS.Kind.lim →
    ∀ n, BT.lt (bValA71 (fsB t n)) (bValA71 (fsB t (n + 1))) = true

/-- **§71.3 の主定理 (減少)。** 前置きの無い添字で足りる。 -/
theorem blimDecA71_of_core71 (H : BDecCore71) : BLimDecA71 := by
  intro t ht hk n
  obtain ⟨r, a, ha, rfl⟩ := kindB_lim_std t (stdB_of_stdB1 t ht) hk
  rw [fsB_appB71 0 r a ha n]
  show BT.lt (bValA71 (appB r (fsB (B.nd 0 B.nil a) n)))
    (bValA71 (appB r (B.nd 0 B.nil a))) = true
  rw [lt_bValA71_appB71]
  exact H a n ha (stdB1_drop_prefix71 r a ht)

/-- **§71.3 の主定理 (増加)。** -/
theorem blimIncA71_of_core71 (H : BIncCore71) : BLimIncA71 := by
  intro t ht hk n
  obtain ⟨r, a, ha, rfl⟩ := kindB_lim_std t (stdB_of_stdB1 t ht) hk
  rw [fsB_appB71 0 r a ha n, fsB_appB71 0 r a ha (n + 1), lt_bValA71_appB71]
  exact H a n ha (stdB1_drop_prefix71 r a ht)

/-- **順序の橋、部分領域で。** `bValA71` の `BT.lt` は `vOf` の `lt` を出す。
    §69 の `VOfLtStd` を部分領域に絞り、`bVal` を `bValA71` に替えたもの。
    `subP 7` の 609² = 370 881 対で `BT.lt (bValA71 ·) (bValA71 ·)`・
    `BT.lt (bVal ·) (bVal ·)`・`lt (vOf ·) (vOf ·)` の 3 つが**一致** (§71.6)。**未証明。** -/
def VOfLtA71 : Prop := ∀ (u t : B), stdB1 u = true → stdB1 t = true →
    BT.lt (bValA71 u) (bValA71 t) = true → lt (vOf u) (vOf t) = true

/-- 逆向き。同じ測定が支える。**未証明。** -/
def VOfLtA71' : Prop := ∀ (u t : B), stdB1 u = true → stdB1 t = true →
    lt (vOf u) (vOf t) = true → BT.lt (bValA71 u) (bValA71 t) = true

theorem limDecS1_71 (HV : VOfLtA71) (HB : BLimDecA71) : LimDecS1 :=
  fun t ht hk n => HV (fsB t n) t (stdB1_fsB t ht n) ht (HB t ht hk n)

theorem limIncS1_71 (HV : VOfLtA71) (HB : BLimIncA71) : LimIncS1 :=
  fun t ht hk n => HV (fsB t n) (fsB t (n + 1)) (stdB1_fsB t ht n)
    (stdB1_fsB t ht (n + 1)) (HB t ht hk n)

/-- **§70.5 の `LimDecS1` は、橋と前置きの無い核の 2 つに落ちる。** -/
theorem limDecS1_of_core71 (HV : VOfLtA71) (H : BDecCore71) : LimDecS1 :=
  limDecS1_71 HV (blimDecA71_of_core71 H)

/-- **§70.5 の `LimIncS1` も同じ。** -/
theorem limIncS1_of_core71 (HV : VOfLtA71) (H : BIncCore71) : LimIncS1 :=
  limIncS1_71 HV (blimIncA71_of_core71 H)

end

/-! ### §71.4 共終性は二つに割れる — §69 が掃いた側と、掃かなかった側

`LimCofS1` の `s` は 𝔗(M) 全体を走る。それを

    CofDenseS1  `s` は「部分領域のある値以下、かつその値は `vOf t` 未満」
    CofInS1     基本列は部分領域の値の中で共終

に割る。§69 は後者だけを測って `LimCofS` と呼び、前者を確かめなかった (§70 が同じ掃きを
正しくやり直して逆の答えを得た)。後者は Buchholz 側へ運べる — `dict` は出てこない。
前者は 𝔗(M) が入ってくる側で、**ここでは落とせない**。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term
open Evidence.WF

/-- **密度。** `vOf t` より下の 𝔗(M) の項は、部分領域のどれかの値で上から押さえられ、
    その値は `vOf t` より真に小さい。**未証明。** -/
def CofDenseS1 : Prop := ∀ (t : B), stdB1 t = true → kindB t = BMS.Kind.lim →
    ∀ s, inT s = true → lt s (vOf t) = true →
    ∃ u : B, stdB1 u = true ∧ le s (vOf u) = true ∧ lt (vOf u) (vOf t) = true

/-- **内側の共終性。** 部分領域の値だけを相手にした共終性。§69 が測ったのはこれ。
    **未証明。** -/
def CofInS1 : Prop := ∀ (t : B), stdB1 t = true → kindB t = BMS.Kind.lim →
    ∀ u : B, stdB1 u = true → lt (vOf u) (vOf t) = true →
    ∃ n, le (vOf u) (vOf (fsB t n)) = true

/-- **§71.4 の主定理。** 共終性は密度と内側の共終性の連言。`inT` の側は §67 の 2 つが運ぶ。 -/
theorem limCofS1_of71 (Hp : PsiIdxOKStd) (Hr : RegionStd)
    (HD : CofDenseS1) (HI : CofInS1) : LimCofS1 := by
  intro t ht hk s hs hlt
  obtain ⟨u, hu, hle, hult⟩ := HD t ht hk s hs hlt
  obtain ⟨n, hn⟩ := HI t ht hk u hu hult
  exact ⟨n, le_trans_inT hs (inT_vOf_std Hp Hr u (stdB_of_stdB1 u hu))
    (inT_vOf_std Hp Hr _ (stdB_of_stdB1 _ (stdB1_fsB t ht n))) hle hn⟩

/-- **内側の共終性の Buchholz 側。** `dict` は出てこない。**未証明。** -/
def BCofIn71 : Prop := ∀ (t : B), stdB1 t = true → kindB t = BMS.Kind.lim →
    ∀ u : B, stdB1 u = true → BT.lt (bValA71 u) (bValA71 t) = true →
    ∃ n, BT.lt (bValA71 (fsB t n)) (bValA71 u) = false

/-- **内側の共終性は Buchholz 側へ落ちる。** 使うのは橋の逆向きと、𝔗(M) の順序が
    線型であること (`Evidence/WF.lean` §8.4) だけ。 -/
theorem cofInS1_of71 (Hp : PsiIdxOKStd) (Hr : RegionStd)
    (HV : VOfLtA71') (HB : BCofIn71) : CofInS1 := by
  intro t ht hk u hu hlt
  obtain ⟨n, hn⟩ := HB t ht hk u hu (HV u t hu ht hlt)
  refine ⟨n, ?_⟩
  have hfs := stdB1_fsB t ht n
  have hiu : inT (vOf u) = true := inT_vOf_std Hp Hr u (stdB_of_stdB1 u hu)
  have hif : inT (vOf (fsB t n)) = true :=
    inT_vOf_std Hp Hr _ (stdB_of_stdB1 _ hfs)
  rcases lt_comparable_inT hiu hif with h | h | h
  · show (vOf u == vOf (fsB t n) || lt (vOf u) (vOf (fsB t n))) = true
    rw [h]; exact Bool.or_true _
  · rw [h]; exact le_self _
  · rw [HV (fsB t n) u hfs hu h] at hn
    exact absurd hn (by intro hc; exact Bool.noConfusion hc)

end

/-! ### §71.5 組み立て

`certIn_t326` (§70.5) を §71 の仮説で書き直す。§68 の 2 つはそのまま、順序の 3 つは
橋 1 つ・前置きの無い核 2 つ・共終性の 2 つ半に置き換わる。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- **§70.5 の 3 つを §71 の形に置き換えた `certIn_t326`。** -/
theorem certIn_t326_71 (Hp : PsiIdxOKStd) (Hr : RegionStd)
    (HV : VOfLtA71) (HBD : BDecCore71) (HBI : BIncCore71)
    (HCD : CofDenseS1) (HCI : CofInS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326 Hp Hr (limDecS1_of_core71 HV HBD) (limIncS1_of_core71 HV HBI)
    (limCofS1_of71 Hp Hr HCD HCI) hacc

/-- 共終性の内側の半分まで Buchholz 側へ落としきった形。仮説は 8 つ、そのうち
    `dict` を含むのは `Hp`・`Hr`・`VOfLtA71`・`VOfLtA71'`・`CofDenseS1` の 5 つだけで、
    残る 3 つ (`BDecCore71`・`BIncCore71`・`BCofIn71`) は Buchholz 側の純粋な順序の話。 -/
theorem certIn_t326_bt71 (Hp : PsiIdxOKStd) (Hr : RegionStd)
    (HV : VOfLtA71) (HV' : VOfLtA71') (HBD : BDecCore71) (HBI : BIncCore71)
    (HCD : CofDenseS1) (HBC : BCofIn71)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_71 Hp Hr HV HBD HBI HCD (cofInS1_of71 Hp Hr HV' HBC) hacc

end

/-! ### §71.6 部分領域では崩れが起きない — 核の再帰と、その底

`bArg` の三分岐 (§48 の `bK`) の第 3 枝は `bClose ∘ bFold`、すなわち「低い子の連なりを
一つの `ψ` に畳む」崩れの枝である。**段が 1 以下ならこの枝は決して選ばれない** — 条件
`u ≤ w || !(r == nil) || headLvl c ≤ u` は `u = 0` なら第 1 項で、`u = 1` なら第 3 項で
すでに真だからである。したがって部分領域の値は「崩れの無い」素直な入れ子の和で、
`bArg w t = bValA71 t` が段 `w` によらず成り立つ。

その帰結が核の再帰である。`bValA71 (nd u nil a) = ψ_u (bValA71 a)` なので、`fsB` が
引数の中へ降りる枝では減少・増加はそのまま一段下の同じ主張になり (`lt_bValA71_nd71`)、
降りない枝 — `repNode` の枝 — は**ここで無条件に閉じる**。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- 段の上限は頭の段を縛る。 -/
theorem headLvl_le71 : ∀ (t : B) (m : Nat), lvlLe m t = true → headLvl t ≤ m := by
  intro t
  induction t with
  | nil => intro m _; exact Nat.zero_le m
  | nd v r c ihr _ =>
    intro m h
    obtain ⟨h1, h2, _⟩ := (lvlLe_nd_iff m v r c).mp h
    cases r with
    | nil => exact h1
    | nd v' r' c' => exact ihr m h2

/-- **崩れは起きない。** 段が 1 以下なら `bK` の第 3 枝 (`bClose ∘ bFold`) は選ばれない。 -/
theorem bK_eq71 (w u : Nat) (r c : B) (hu : u ≤ 1) (hc : lvlLe 1 c = true) :
    bK w u r c = BT.D u (bArg u c) := by
  show (if c == .nil then (BT.D u .zero) else
        if u ≤ w || !(r == .nil) || headLvl c ≤ u then BT.D u (bArg u c)
        else bClose u (bFold u c)) = BT.D u (bArg u c)
  by_cases h1 : (c == B.nil) = true
  · rw [if_pos h1, show c = B.nil from eq_of_beq h1]
    rfl
  · rw [if_neg h1]
    have hcond : (u ≤ w || !(r == B.nil) || headLvl c ≤ u) = true := by
      cases u with
      | zero =>
        rw [show (decide (0 ≤ w)) = true from decide_eq_true (Nat.zero_le w)]
        rfl
      | succ k =>
        have hk : k = 0 := by omega
        subst hk
        rw [show (decide (headLvl c ≤ 1)) = true from decide_eq_true (headLvl_le71 c 1 hc)]
        exact Bool.or_true _
    rw [if_pos hcond]

/-- **§71.6 の主定理。** 段 1 以下の添字では `bArg` は段 `w` によらず `bValA71` そのもの。
    §48 の畳み込みは部分領域では恒等写像である。**無条件。** -/
theorem bArg_eq_bValA71_71 : ∀ (t : B) (w : Nat), lvlLe 1 t = true → bArg w t = bValA71 t := by
  intro t
  induction t with
  | nil => intro w _; rfl
  | nd u r c ihr _ =>
    intro w h
    obtain ⟨hu, hr, hc⟩ := (lvlLe_nd_iff 1 u r c).mp h
    rw [bArg_nd w u r c, bK_eq71 w u r c hu hc, ihr w hr]
    rfl

/-- 前置きの無い一節の値は `ψ_u` そのもの。 -/
theorem bValA71_nd_nil71 (u : Nat) (a : B) (h : lvlLe 1 a = true) :
    bValA71 (.nd u .nil a) = BT.D u (bValA71 a) := by
  show bplus (bValA71 B.nil) (BT.D u (bArg u a)) = _
  rw [bArg_eq_bValA71_71 a u h]
  rfl

/-- Buchholz 側の順序は非反射的 — 少なくとも `bValA71` の像の上では。 -/
theorem lt_bValA71_irrefl71 (x : B) : BT.lt (bValA71 x) (bValA71 x) = false := by
  rw [lt_eq_ltS]
  have h := ltS_append_left71 (bValA71 x).toL (atomsL_bValA71 x) [] []
  rw [List.append_nil] at h
  rw [h]
  rfl

/-- **核の再帰の一段。** 引数の中で減れば、`ψ_u` を被せても減る。 -/
theorem lt_bValA71_nd71 (u : Nat) (x y : B) (hx : lvlLe 1 x = true) (hy : lvlLe 1 y = true)
    (h : BT.lt (bValA71 x) (bValA71 y) = true) :
    BT.lt (bValA71 (.nd u .nil x)) (bValA71 (.nd u .nil y)) = true := by
  have hne : ¬((bValA71 x == bValA71 y) = true) := by
    intro hc
    rw [bt_eq_of_beq71 _ _ hc, lt_bValA71_irrefl71 y] at h
    exact Bool.noConfusion h
  rw [bValA71_nd_nil71 u x hx, bValA71_nd_nil71 u y hy, lt_eq_ltS]
  show ltS [BT.D u (bValA71 x)] [BT.D u (bValA71 y)] = true
  rw [ltS_cons u (bValA71 x) [] u (bValA71 y) [], if_neg (Nat.lt_irrefl u),
    if_neg (Nat.lt_irrefl u), if_neg hne, ← lt_eq_ltS]
  exact h

/-- `repNode` の成分列の頭。 -/
theorem toL_bValA71_repNode71 (u : Nat) (P : B) : ∀ n,
    ∃ rest, (bValA71 (repNode u P n)).toL = BT.D u (bArg u P) :: rest
  | 0 => ⟨[], rfl⟩
  | k + 1 => by
    obtain ⟨rest, hrest⟩ := toL_bValA71_repNode71 u P k
    refine ⟨rest ++ [BT.D u (bArg u P)], ?_⟩
    show (bValA71 (.nd u (repNode u P k) P)).toL = _
    rw [toL_bValA71_nd u (repNode u P k) P, hrest]
    rfl

/-- **`repNode` の枝の増加 — 無条件。** 一つ増やすと成分が右に一つ増えるだけ。 -/
theorem lt_bValA71_repNode_inc71 (u : Nat) (P : B) (n : Nat) :
    BT.lt (bValA71 (repNode u P n)) (bValA71 (repNode u P (n + 1))) = true := by
  rw [lt_eq_ltS]
  show ltS (bValA71 (repNode u P n)).toL (bValA71 (.nd u (repNode u P n) P)).toL = true
  rw [toL_bValA71_nd u (repNode u P n) P]
  have h := ltS_append_left71 (bValA71 (repNode u P n)).toL
    (atomsL_bValA71 (repNode u P n)) [] [BT.D u (bArg u P)]
  rw [List.append_nil] at h
  rw [h]
  rfl

/-- **`repNode` の枝の減少 — 無条件。** `ψ_u(P)` の並びは `ψ_u(P ⊕ ψ₀0)` より小さい。 -/
theorem lt_bValA71_repNode_dec71 (u : Nat) (P : B) (hP : lvlLe 1 P = true) (n : Nat) :
    BT.lt (bValA71 (repNode u P n)) (bValA71 (.nd u .nil (.nd 0 P .nil))) = true := by
  have hA : (bValA71 (.nd 0 P .nil)).toL = (bValA71 P).toL ++ [BT.D 0 BT.zero] := by
    rw [toL_bValA71_nd 0 P .nil]; rfl
  have hne : ¬((bValA71 P == bValA71 (.nd 0 P .nil)) = true) := by
    intro hc
    have h1 : (bValA71 P).toL = (bValA71 P).toL ++ [BT.D 0 BT.zero] := by
      rw [← hA, bt_eq_of_beq71 _ _ hc]
    have h2 := congrArg List.length h1
    rw [List.length_append, show ([BT.D 0 BT.zero]).length = 1 from rfl] at h2
    omega
  have hlv : lvlLe 1 (.nd 0 P .nil) = true :=
    (lvlLe_nd_iff 1 0 P .nil).mpr ⟨Nat.zero_le 1, hP, rfl⟩
  obtain ⟨rest, hrest⟩ := toL_bValA71_repNode71 u P n
  rw [bValA71_nd_nil71 u _ hlv, lt_eq_ltS, hrest]
  show ltS (BT.D u (bArg u P) :: rest) [BT.D u (bValA71 (.nd 0 P .nil))] = true
  rw [bArg_eq_bValA71_71 P u hP, ltS_cons u (bValA71 P) rest u (bValA71 (.nd 0 P .nil)) [],
    if_neg (Nat.lt_irrefl u), if_neg (Nat.lt_irrefl u), if_neg hne, hA]
  have h := ltS_append_left71 (bValA71 P).toL (atomsL_bValA71 P) [] [BT.D 0 BT.zero]
  rw [List.append_nil] at h
  rw [h]
  rfl

end

/-! ### §71.7 核は定理である — `BDecCore71` と `BIncCore71` の証明

§71.6 で `bValA71` が崩れの無い入れ子の和だと分かったので、`fsB` の三つの演算を値の側で
そのまま追える。`plugB` は最後の節を差し替えるだけ、`repB` は葉を複製するだけ、`rwB` は
段が低い最も近い祖先まで降りてそこで `iterD` する。どれも「共通の前置きを消して一段下の
同じ主張にする」形になるので、節の個数についての帰納法で閉じる。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

theorem lastLvl_nd71 (v : Nat) (r c : B) (h : c ≠ .nil) :
    lastLvl (.nd v r c) = lastLvl c := by
  cases c with
  | nil => exact absurd rfl h
  | nd u s d => rfl

theorem toL_bValA71_ne_nil71 : ∀ (t : B), t ≠ .nil → (bValA71 t).toL ≠ []
  | .nil, h => absurd rfl h
  | .nd w r c, _ => by
      intro hc
      have h2 := congrArg List.length hc
      rw [toL_bValA71_nd w r c, List.length_append,
        show ([BT.D w (bArg w c)]).length = 1 from rfl,
        show (([] : List BT)).length = 0 from rfl] at h2
      omega

/-- 0 は最小。 -/
theorem lt_bValA71_nil71 (x : B) (h : x ≠ .nil) :
    BT.lt (bValA71 .nil) (bValA71 x) = true := by
  have hne := toL_bValA71_ne_nil71 x h
  rw [lt_eq_ltS]
  show ltS [] (bValA71 x).toL = true
  cases hx : (bValA71 x).toL with
  | nil => exact absurd hx hne
  | cons y ys => exact ltS_nil_cons y ys

/-- **最後の節の差し替えは値を下げる。** 差し込む側が `ψ_{lastLvl c}(0)` より小さければ。 -/
theorem lt_bValA71_plugB_dec71 : ∀ (c : B), c ≠ .nil → lvlLe 1 c = true → ∀ (Y : B),
    lvlLe 1 Y = true → BT.lt (bValA71 Y) (BT.D (lastLvl c) BT.zero) = true →
    BT.lt (bValA71 (plugB c Y)) (bValA71 c) = true := by
  intro c
  induction c with
  | nil => intro h; exact absurd rfl h
  | nd v r c' _ ihc =>
    intro _ hlv Y hY hlt
    obtain ⟨_, _, hc'⟩ := (lvlLe_nd_iff 1 v r c').mp hlv
    cases c' with
    | nil =>
      show BT.lt (bValA71 (appB r Y)) (bValA71 (appB r (.nd v .nil .nil))) = true
      rw [lt_bValA71_appB71]
      exact hlt
    | nd u s d =>
      show BT.lt (bValA71 (appB r (.nd v .nil (plugB (.nd u s d) Y))))
        (bValA71 (appB r (.nd v .nil (.nd u s d)))) = true
      rw [lt_bValA71_appB71]
      exact lt_bValA71_nd71 v _ _ (lvlLe_plugB _ 1 Y hc' hY) hc'
        (ihc (by intro hc; exact B.noConfusion hc) hc' Y hY hlt)

/-- **最後の節の差し替えは単調。** -/
theorem lt_bValA71_plugB_mono71 : ∀ (c : B), c ≠ .nil → lvlLe 1 c = true → ∀ (Y Y' : B),
    lvlLe 1 Y = true → lvlLe 1 Y' = true → BT.lt (bValA71 Y) (bValA71 Y') = true →
    BT.lt (bValA71 (plugB c Y)) (bValA71 (plugB c Y')) = true := by
  intro c
  induction c with
  | nil => intro h; exact absurd rfl h
  | nd v r c' _ ihc =>
    intro _ hlv Y Y' hY hY' hlt
    obtain ⟨_, _, hc'⟩ := (lvlLe_nd_iff 1 v r c').mp hlv
    cases c' with
    | nil =>
      show BT.lt (bValA71 (appB r Y)) (bValA71 (appB r Y')) = true
      rw [lt_bValA71_appB71]
      exact hlt
    | nd u s d =>
      show BT.lt (bValA71 (appB r (.nd v .nil (plugB (.nd u s d) Y))))
        (bValA71 (appB r (.nd v .nil (plugB (.nd u s d) Y')))) = true
      rw [lt_bValA71_appB71]
      exact lt_bValA71_nd71 v _ _ (lvlLe_plugB _ 1 Y hc' hY) (lvlLe_plugB _ 1 Y' hc' hY')
        (ihc (by intro hc; exact B.noConfusion hc) hc' Y Y' hY hY' hlt)

/-- `ψ_v(0)` より小さい: `iterD` の値の段は `v`。 -/
theorem lt_bValA71_iterD_D71 (v w : Nat) (c : B) (hv : v ≤ 1) (hc : lvlLe 1 c = true)
    (h : v < w) : ∀ n, BT.lt (bValA71 (iterD v c n)) (BT.D w BT.zero) = true
  | 0 => by
      show BT.lt (bValA71 (.nd v .nil (plugB c .nil))) (BT.D w BT.zero) = true
      rw [bValA71_nd_nil71 v _ (lvlLe_plugB c 1 .nil hc rfl)]
      exact lt_D_lvl v w _ BT.zero h
  | k + 1 => by
      show BT.lt (bValA71 (.nd v .nil (plugB c (iterD v c k)))) (BT.D w BT.zero) = true
      rw [bValA71_nd_nil71 v _ (lvlLe_plugB c 1 _ hc (lvlLe_iterD k v c 1 hv hc))]
      exact lt_D_lvl v w _ BT.zero h

theorem lt_zero_D71 (w : Nat) : BT.lt (bValA71 .nil) (BT.D w BT.zero) = true := by
  refine lt_zero_toL (BT.D w BT.zero) ?_
  intro hc
  have h2 := congrArg List.length hc
  rw [show ((BT.D w BT.zero).toL).length = 1 from rfl,
    show (([] : List BT)).length = 0 from rfl] at h2
  omega

/-- **悪い根の反復は値を下げる。** -/
theorem lt_bValA71_iterD_dec71 (v : Nat) (c : B) (hv : v ≤ 1) (hc : lvlLe 1 c = true)
    (hne : c ≠ .nil) (h : v < lastLvl c) : ∀ n,
    BT.lt (bValA71 (iterD v c n)) (bValA71 (.nd v .nil c)) = true
  | 0 => by
      show BT.lt (bValA71 (.nd v .nil (plugB c .nil))) (bValA71 (.nd v .nil c)) = true
      exact lt_bValA71_nd71 v _ c (lvlLe_plugB c 1 .nil hc rfl) hc
        (lt_bValA71_plugB_dec71 c hne hc .nil rfl (lt_zero_D71 (lastLvl c)))
  | k + 1 => by
      show BT.lt (bValA71 (.nd v .nil (plugB c (iterD v c k)))) (bValA71 (.nd v .nil c)) = true
      exact lt_bValA71_nd71 v _ c
        (lvlLe_plugB c 1 _ hc (lvlLe_iterD k v c 1 hv hc)) hc
        (lt_bValA71_plugB_dec71 c hne hc _ (lvlLe_iterD k v c 1 hv hc)
          (lt_bValA71_iterD_D71 v (lastLvl c) c hv hc h k))

/-- **悪い根の反復は真に増える。** -/
theorem lt_bValA71_iterD_inc71 (v : Nat) (c : B) (hv : v ≤ 1) (hc : lvlLe 1 c = true)
    (hne : c ≠ .nil) : ∀ n,
    BT.lt (bValA71 (iterD v c n)) (bValA71 (iterD v c (n + 1))) = true
  | 0 => by
      show BT.lt (bValA71 (.nd v .nil (plugB c .nil)))
        (bValA71 (.nd v .nil (plugB c (iterD v c 0)))) = true
      exact lt_bValA71_nd71 v _ _ (lvlLe_plugB c 1 .nil hc rfl)
        (lvlLe_plugB c 1 _ hc (lvlLe_iterD 0 v c 1 hv hc))
        (lt_bValA71_plugB_mono71 c hne hc .nil (iterD v c 0) rfl
          (lvlLe_iterD 0 v c 1 hv hc)
          (lt_bValA71_nil71 (iterD v c 0)
            (by intro hcc; exact B.noConfusion (show B.nd v B.nil (plugB c B.nil) = B.nil from hcc))))
  | k + 1 => by
      show BT.lt (bValA71 (.nd v .nil (plugB c (iterD v c k))))
        (bValA71 (.nd v .nil (plugB c (iterD v c (k + 1))))) = true
      exact lt_bValA71_nd71 v _ _
        (lvlLe_plugB c 1 _ hc (lvlLe_iterD k v c 1 hv hc))
        (lvlLe_plugB c 1 _ hc (lvlLe_iterD (k + 1) v c 1 hv hc))
        (lt_bValA71_plugB_mono71 c hne hc _ _ (lvlLe_iterD k v c 1 hv hc)
          (lvlLe_iterD (k + 1) v c 1 hv hc)
          (lt_bValA71_iterD_inc71 v c hv hc hne k))

/-! #### `repB` の枝 -/

theorem repB_base71 (v : Nat) (r P : B) (n : Nat) :
    repB (.nd v r (.nd 0 P .nil)) n = appB r (repNode v P n) := rfl

theorem repB_deep71 (v : Nat) (r : B) (u : Nat) (P d : B) (n : Nat) (hd : d ≠ .nil) :
    repB (.nd v r (.nd u P d)) n = .nd v r (repB (.nd u P d) n) := by
  cases d with
  | nil => exact absurd rfl hd
  | nd u2 s2 d2 => cases u with
    | zero => rfl
    | succ k => rfl

/-- **段 0 の葉の枝は減って増える。** 節の個数についての帰納法。 -/
theorem repB_dec_inc71 : ∀ (c : B), c ≠ .nil → lastLvl c = 0 → ∀ (v : Nat) (r : B),
    lvlLe 1 (.nd v r c) = true → ∀ n,
    BT.lt (bValA71 (repB (.nd v r c) n)) (bValA71 (.nd v r c)) = true
    ∧ BT.lt (bValA71 (repB (.nd v r c) n)) (bValA71 (repB (.nd v r c) (n + 1))) = true := by
  intro c
  induction c with
  | nil => intro h; exact absurd rfl h
  | nd u P d _ ihd =>
    intro _ hll v r hlv n
    obtain ⟨_, _, hc⟩ := (lvlLe_nd_iff 1 v r (.nd u P d)).mp hlv
    obtain ⟨_, hP, _⟩ := (lvlLe_nd_iff 1 u P d).mp hc
    cases d with
    | nil =>
      have hu0 : u = 0 := hll
      subst hu0
      refine ⟨?_, ?_⟩
      · rw [repB_base71 v r P n]
        show BT.lt (bValA71 (appB r (repNode v P n)))
          (bValA71 (appB r (.nd v .nil (.nd 0 P .nil)))) = true
        rw [lt_bValA71_appB71]
        exact lt_bValA71_repNode_dec71 v P hP n
      · rw [repB_base71 v r P n, repB_base71 v r P (n + 1), lt_bValA71_appB71]
        exact lt_bValA71_repNode_inc71 v P n
    | nd u2 s2 d2 =>
      have hdne : (B.nd u2 s2 d2) ≠ .nil := by intro hcc; exact B.noConfusion hcc
      obtain ⟨g1, g2⟩ := ihd hdne hll u P hc n
      have hlr : lvlLe 1 (repB (.nd u P (.nd u2 s2 d2)) n) = true :=
        lvlLe_repB _ 1 n hc
      have hlr' : lvlLe 1 (repB (.nd u P (.nd u2 s2 d2)) (n + 1)) = true :=
        lvlLe_repB _ 1 (n + 1) hc
      refine ⟨?_, ?_⟩
      · rw [repB_deep71 v r u P (.nd u2 s2 d2) n hdne]
        show BT.lt (bValA71 (appB r (.nd v .nil (repB (.nd u P (.nd u2 s2 d2)) n))))
          (bValA71 (appB r (.nd v .nil (.nd u P (.nd u2 s2 d2))))) = true
        rw [lt_bValA71_appB71]
        exact lt_bValA71_nd71 v _ _ hlr hc g1
      · rw [repB_deep71 v r u P (.nd u2 s2 d2) n hdne,
          repB_deep71 v r u P (.nd u2 s2 d2) (n + 1) hdne]
        show BT.lt (bValA71 (appB r (.nd v .nil (repB (.nd u P (.nd u2 s2 d2)) n))))
          (bValA71 (appB r (.nd v .nil (repB (.nd u P (.nd u2 s2 d2)) (n + 1))))) = true
        rw [lt_bValA71_appB71]
        exact lt_bValA71_nd71 v _ _ hlr hlr' g2

/-! #### `rwB` の枝 -/

theorem hasLowAnc_nd71 (w u : Nat) (P d : B) (hd : d ≠ .nil) :
    hasLowAnc w (.nd u P d) = (decide (u < w) || hasLowAnc w d) := by
  cases d with
  | nil => exact absurd rfl hd
  | nd u2 s2 d2 => rfl

theorem hasLowAnc_leaf71 (w u : Nat) (P : B) : hasLowAnc w (.nd u P .nil) = false := rfl

theorem rwB_nd71 (w n v : Nat) (r : B) (u : Nat) (P d : B) :
    rwB w n (.nd v r (.nd u P d))
      = (if hasLowAnc w (.nd u P d) then .nd v r (rwB w n (.nd u P d))
         else if v < w then appB r (iterD v (.nd u P d) n) else .nd v r (.nd u P d)) := rfl

/-- **段 `w ≥ 1` の葉の枝は減って増える。** 「段が `w` 未満の最も近い祖先が在る」
    という不変量 (`hasLowAnc w c = true ∨ v < w`) が降下のたびに保たれるので、
    `fsB` が添字を動かさない第 3 枝には決して落ちない。 -/
theorem rwB_dec_inc71 : ∀ (c : B), c ≠ .nil → ∀ (w : Nat), lastLvl c = w →
    ∀ (v : Nat) (r : B), (hasLowAnc w c = true ∨ v < w) → lvlLe 1 (.nd v r c) = true → ∀ n,
    BT.lt (bValA71 (rwB w n (.nd v r c))) (bValA71 (.nd v r c)) = true
    ∧ BT.lt (bValA71 (rwB w n (.nd v r c))) (bValA71 (rwB w (n + 1) (.nd v r c))) = true := by
  intro c
  induction c with
  | nil => intro h; exact absurd rfl h
  | nd u P d _ ihd =>
    intro _ w hll v r hdis hlv n
    obtain ⟨hv, _, hc⟩ := (lvlLe_nd_iff 1 v r (.nd u P d)).mp hlv
    have hcne : (B.nd u P d) ≠ .nil := by intro hcc; exact B.noConfusion hcc
    by_cases hla : hasLowAnc w (.nd u P d) = true
    · have hdne : d ≠ .nil := by
        intro hcc
        rw [hcc, hasLowAnc_leaf71 w u P] at hla
        exact Bool.noConfusion hla
      have hdis2 : hasLowAnc w d = true ∨ u < w := by
        rw [hasLowAnc_nd71 w u P d hdne] at hla
        rcases (Bool.or_eq_true _ _).mp hla with h | h
        · exact Or.inr (of_decide_eq_true h)
        · exact Or.inl h
      have hll2 : lastLvl d = w := by rw [← hll]; exact (lastLvl_nd71 u P d hdne).symm
      obtain ⟨g1, g2⟩ := ihd hdne w hll2 u P hdis2 hc n
      have hlr : lvlLe 1 (rwB w n (.nd u P d)) = true := lvlLe_rwB _ w n 1 hc
      have hlr' : lvlLe 1 (rwB w (n + 1) (.nd u P d)) = true := lvlLe_rwB _ w (n + 1) 1 hc
      refine ⟨?_, ?_⟩
      · rw [rwB_nd71 w n v r u P d, if_pos hla]
        show BT.lt (bValA71 (appB r (.nd v .nil (rwB w n (.nd u P d)))))
          (bValA71 (appB r (.nd v .nil (.nd u P d)))) = true
        rw [lt_bValA71_appB71]
        exact lt_bValA71_nd71 v _ _ hlr hc g1
      · rw [rwB_nd71 w n v r u P d, rwB_nd71 w (n + 1) v r u P d, if_pos hla, if_pos hla]
        show BT.lt (bValA71 (appB r (.nd v .nil (rwB w n (.nd u P d)))))
          (bValA71 (appB r (.nd v .nil (rwB w (n + 1) (.nd u P d))))) = true
        rw [lt_bValA71_appB71]
        exact lt_bValA71_nd71 v _ _ hlr hlr' g2
    · have hvw : v < w := by
        rcases hdis with h | h
        · exact absurd h hla
        · exact h
      have hvl : v < lastLvl (.nd u P d) := by rw [hll]; exact hvw
      refine ⟨?_, ?_⟩
      · rw [rwB_nd71 w n v r u P d, if_neg hla, if_pos hvw]
        show BT.lt (bValA71 (appB r (iterD v (.nd u P d) n)))
          (bValA71 (appB r (.nd v .nil (.nd u P d)))) = true
        rw [lt_bValA71_appB71]
        exact lt_bValA71_iterD_dec71 v _ hv hc hcne hvl n
      · rw [rwB_nd71 w n v r u P d, rwB_nd71 w (n + 1) v r u P d,
          if_neg hla, if_neg hla, if_pos hvw, if_pos hvw, lt_bValA71_appB71]
        exact lt_bValA71_iterD_inc71 v _ hv hc hcne n

/-! #### 核は定理 -/

theorem lastLvl_pos71 (a : B) (hz : ¬((lastLvl a == 0) = true)) : 0 < lastLvl a := by
  refine Nat.pos_of_ne_zero ?_
  intro hcc
  exact hz (by rw [hcc]; rfl)

/-- **§71.7 の主定理 (減少)。** `BDecCore71` は定理である。 -/
theorem bDecCore71_thm : BDecCore71 := by
  intro a n ha hstd
  have hlv : lvlLe 1 (.nd 0 .nil a) = true := lvlLe1_of_stdB1 _ hstd
  rw [fsB_ne_nil71 0 .nil a n ha]
  by_cases hz : (lastLvl a == 0) = true
  · rw [if_pos hz]
    exact (repB_dec_inc71 a ha (eq_of_beq hz) 0 .nil hlv n).1
  · rw [if_neg hz]
    exact (rwB_dec_inc71 a ha (lastLvl a) rfl 0 .nil (Or.inr (lastLvl_pos71 a hz)) hlv n).1

/-- **§71.7 の主定理 (増加)。** `BIncCore71` は定理である。 -/
theorem bIncCore71_thm : BIncCore71 := by
  intro a n ha hstd
  have hlv : lvlLe 1 (.nd 0 .nil a) = true := lvlLe1_of_stdB1 _ hstd
  rw [fsB_ne_nil71 0 .nil a n ha, fsB_ne_nil71 0 .nil a (n + 1) ha]
  by_cases hz : (lastLvl a == 0) = true
  · rw [if_pos hz, if_pos hz]
    exact (repB_dec_inc71 a ha (eq_of_beq hz) 0 .nil hlv n).2
  · rw [if_neg hz, if_neg hz]
    exact (rwB_dec_inc71 a ha (lastLvl a) rfl 0 .nil (Or.inr (lastLvl_pos71 a hz)) hlv n).2

/-- **部分領域ぜんぶで減少 (Buchholz 側)。仮説なし。** -/
theorem blimDecA71_thm : BLimDecA71 := blimDecA71_of_core71 bDecCore71_thm

/-- **部分領域ぜんぶで増加 (Buchholz 側)。仮説なし。** -/
theorem blimIncA71_thm : BLimIncA71 := blimIncA71_of_core71 bIncCore71_thm

/-- **§70.5 の `LimDecS1` は、橋 `VOfLtA71` ただ 1 つに落ちる。** -/
theorem limDecS1_of_bridge71 (HV : VOfLtA71) : LimDecS1 := limDecS1_71 HV blimDecA71_thm

/-- **§70.5 の `LimIncS1` も、橋 `VOfLtA71` ただ 1 つに落ちる。** -/
theorem limIncS1_of_bridge71 (HV : VOfLtA71) : LimIncS1 := limIncS1_71 HV blimIncA71_thm

/-- **§71 の最終形。** `certIn_t326` の 5 つの仮説のうち、順序の 3 つは
    `VOfLtA71` (橋) と `CofDenseS1`・`CofInS1` (共終性の 2 つ) だけになる。
    減少と増加はもう仮説ではない。 -/
theorem certIn_t326_71' (Hp : PsiIdxOKStd) (Hr : RegionStd)
    (HV : VOfLtA71) (HCD : CofDenseS1) (HCI : CofInS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326 Hp Hr (limDecS1_of_bridge71 HV) (limIncS1_of_bridge71 HV)
    (limCofS1_of71 Hp Hr HCD HCI) hacc

end

/-! ### §71.8 測定 (凍結)

母集団の作り方を先に書く。添字の側は §70.6 のものをそのまま使う:

    popNFB 2 n = ((List.range n).flatMap (enumNodes 2)).filter (nfB · && · != nil)
    subP   n   = (popNFB 2 n).filter stdB1        節は 0 … n-1 個、段は 0 と 1
    subLim n   = (subP n).filter (kindB · == lim)

`pfree71` は前置きの無い添字 (`nd _ nil _`)、`allB71 L n` は「節が n 個未満・段が L 未満」の
`B` を**標準形も標準性も問わずに**全部並べたもの — §71.6 の鋭さはここで測る。

`s` の側 (共終性) は §70.6 より広い `§71` 独自の母集団を作る。**部分領域の外を必ず含める**
(§69 が踏んだ罠):

    seedT71 = valP70 3 6 ++ valP70 4 7 ++ outP70 3 6 ++ outP70 4 7 ++ (subP 8).map vOf
              — 段 0..2 と 0..3 の**領域全体**の値 (段 2・段 3 の添字の値、すなわち部分領域の
                外の値を含む)、標準でない添字の値、そして部分領域自身の値
    base71  = seedT71 の**部分項をすべて**取り、`inT` かつ `< cap71` に絞って重複を除く (2437)
    phiL71  = idxA71 (22 個) と base71 の `φ̄` の積 — 両側から (87 732)
    uni71   = base71 の `ω^·`・`ω̄^·`・`· ⊕ 1`・`· ⊕ ·`、および idxP71 (6 個) を添字とする
              `ψ` を base71 に当てたもの (9418)
    psiL71  = idxP71 を添字とする `ψ` を phiL71 に当てたもの (75 852)

合計 175 439 項。`cap71 = ψ_{Ω₁}(φ̄(1,Ω₁)) = §69 の `sbad` で切るのは損が無い (§70.6 の
`BelowGap` の測定)。添字の掃き幅は §70.6 より広い — `idxA71` は `φ̄` の第 1 引数を
`0..8, ω, φ̄(1,0), φ̄(2,0), φ̄(3,0), φ̄(4,0), φ̄(ω,0), φ̄(φ̄(1,0),0), ψ_{Ω₁}0, ψ_{Ω₁}1, Ω₁,
φ̄(1,Ω₁), φ̄(2,Ω₁), Ω₁⊕Ω₁` まで、`idxP71` は `Z0, Z1, Z2, Z3, Zω, Z(Z0)` まで。

重い掃きは同じ母集団で別ファイルに凍結してある — この節には 300 秒に収まる分だけを置く。

    s71sweep1.lean   base71 (2437) × subLim 8 (1787) = 4 354 919 対、uni71 (9418) ×
                     subLim 7 (448) = 4 219 264 対
    s71sweep2.lean   phiL71a (43 866) × subLim 6 (114) = 5 000 724 対
    s71sweep4.lean   phiL71b (43 866) × subLim 6 (114) = 5 000 724 対
    s71sweep3.lean   psiL71 (75 852) × subLim 6 (114) = 8 647 128 対

`phiL71a` は `φ̄` の第 1 引数に `idxA71` を、`phiL71b` は第 2 引数に置いたもので
`phiL71 = phiL71a ++ phiL71b`。どれも `N = 14` で反例 0、合計 27 222 759 対。 -/

section
open Trans.Recal
open Trans.Dict (BT dict)
open TM TM.Term

/-- 前置きの無い添字。 -/
def pfree71 : B → Bool
  | .nd _ .nil _ => true
  | _ => false

/-- 標準形も標準性も問わない全列挙。 -/
def allB71 (L n : Nat) : List B := (List.range n).flatMap (enumNodes L)

/-- `cap71` は §69 の `sbad`。 -/
def cap71 : Term := psi (Z zero) (phi TM.Term.one (Z zero))

def seedT71 : List Term :=
  ((valP70 3 6) ++ (valP70 4 7) ++ (outP70 3 6) ++ (outP70 4 7)
   ++ ((subP 8).map vOf)).eraseDups

def base71 : List Term :=
  ((seedT71.flatMap subs).filter fun x => inT x && lt x cap71).eraseDups

def idxA71 : List Term :=
  [zero, TM.Term.one, ofNat 2, ofNat 3, ofNat 4, ofNat 5, ofNat 6, ofNat 7, ofNat 8,
   TM.Term.omega, phi TM.Term.one zero, phi (ofNat 2) zero, phi (ofNat 3) zero,
   phi (ofNat 4) zero, phi TM.Term.omega zero, phi (phi TM.Term.one zero) zero,
   psi (Z zero) zero, psi (Z zero) TM.Term.one, Z zero, phi TM.Term.one (Z zero),
   phi (ofNat 2) (Z zero), plus (Z zero) (Z zero)]

def idxP71 : List Term :=
  [Z zero, Z TM.Term.one, Z (ofNat 2), Z (ofNat 3), Z TM.Term.omega, Z (Z zero)]

def uni71 : List Term :=
  (base71.map omegaNF ++ base71.map omg
   ++ base71.map (fun a => plus a TM.Term.one)
   ++ base71.map (fun a => plus a a)
   ++ (idxP71.flatMap fun k => base71.map fun a => psi k a)).filter
    fun x => inT x && lt x cap71

/-- `BCofIn71` が落ちる対 `(t, u)`。基本列の値は `t` ごとに 1 度だけ計算する。 -/
def bcofFail71 (N : Nat) (ts us : List B) : Nat :=
  (ts.flatMap fun t =>
    let v := bValA71 t
    let fsv := (List.range N).map fun k => bValA71 (fsB t k)
    us.filter fun u => BT.lt (bValA71 u) v && (fsv.all fun w => BT.lt w (bValA71 u))).length

/-- 三つの順序が一致しない対。 -/
def bridgeFail71 (l : List B) : Nat :=
  (l.flatMap fun u => (l.filter fun t =>
    !((BT.lt (bValA71 u) (bValA71 t) == BT.lt (bVal u) (bVal t))
      && (BT.lt (bVal u) (bVal t) == lt (vOf u) (vOf t))))).length

-- 添字の母集団の大きさ。
#guard (subP 6).length == 160
#guard (subP 7).length == 609
#guard (subP 8).length == 2397
#guard (subP 9).length == 9782
#guard (subLim 6).length == 114
#guard (subLim 7).length == 448
#guard (subLim 8).length == 1787
#guard (subLim 9).length == 7384
-- 前置きの無い添字が占める割合。§71.3 の還元が消す分。
#guard ((subLim 8).filter pfree71).length == 1427
#guard ((subLim 9).filter pfree71).length == 5743

/-! **§71.6 の鋭さ。** 段 2 が入ると崩れは実際に起きる。最小の証人は `(0,1)(1,2)`。 -/

#guard (allB71 3 5).length == 1291
#guard ((allB71 3 5).filter fun t => bArg 0 t != bValA71 t).length == 91
#guard ((allB71 3 5).filter fun t => bArg 0 t != bValA71 t).head? ==
  some (.nd 1 .nil (.nd 2 .nil .nil))
#guard (allB71 2 7).length == 10067
#guard ((allB71 2 7).filter fun t =>
  bArg 0 t != bValA71 t || bArg 1 t != bValA71 t || bArg 2 t != bValA71 t).length == 0
-- §71.6 は定理なので、これは受領であって根拠ではない。
#guard (subP 8).all fun t => bArg 0 t == bValA71 t && bArg 1 t == bValA71 t

/-! **`bValA71` と `bVal` の差。** 先頭の `(0,0)` の例外そのもの — 自然数だけ。 -/

#guard ((subP 8).filter fun t => bValA71 t != bVal t).length == 7
#guard ((subP 8).filter fun t => bValA71 t != bVal t).all fun t =>
  (matB t 0).all fun row => row.getD 1 9 == 0

/-! **§71.7 の受領。** 減少と増加は定理になったので、これは確認である。 -/

#guard (subLim 8).all fun t => (List.range 6).all fun n =>
  BT.lt (bValA71 (fsB t n)) (bValA71 t)
#guard (subLim 8).all fun t => (List.range 6).all fun n =>
  BT.lt (bValA71 (fsB t n)) (bValA71 (fsB t (n + 1)))

/-! **橋 `VOfLtA71` — §71 に残る唯一の順序の仮説。** `bValA71` の `BT.lt`、`bVal` の
`BT.lt`、`vOf` の `lt` の 3 つが**一致**する。含意ではなく等号で測る。反例 0。 -/

#guard bridgeFail71 (subP 6) == 0
#guard bridgeFail71 (subP 7) == 0

/-! **共終性 (§71.4 の 2 つを合わせたもの、すなわち `LimCofS1` そのもの)。** `s` は
部分領域の**外**まで走らせる。`N = 14` で反例 0。基本列は増えるので `N` を上げても
失敗は減るだけ — したがってこれは `N ≥ 14` すべてで反例 0 ということ。 -/

#guard base71.length == 2437
#guard uni71.length == 9418
#guard (cofFail2 14 (subLim 7) base71).length == 0
#guard (cofFail2 14 (subLim 6) uni71).length == 0

/-! **測定が空回りしていないことの対照 (§70.6 と同じ試験)。** 同じ母集団を `N = 4` で
掃くと落ちる。落ちた分はどれも `4 ≤ n < 14` で閉じる。 -/

#guard (cofFail2 4 (subLim 6) uni71).length > 0

/-! **§71.4 の内側の半分 `BCofIn71` を Buchholz 側で直接測る。** `u` は部分領域の添字を
走る (§69 が測ったのと同じ母集団の形だが、こちらは `bValA71` の `BT.lt` で、`dict` を
通さない)。`N = 14` で反例 0。`N = 3` では 108 対落ちるので、試験は空回りしていない。
**`CofDenseS1` の側はこの測定では何も言えない** — それが §71.4 の要点である。 -/

#guard bcofFail71 14 (subLim 6) (subP 7) == 0
#guard bcofFail71 14 (subLim 7) (subP 8) == 0
#guard bcofFail71 3 (subLim 6) (subP 7) == 108

end

/-! ### §71.9 公理 -/

/-! ## §73 THE `u = 1` HALF OF THE LAST `inT` GATE IS A THEOREM — `u = 0` IS NOT

§72 reduced row 326's certificate to four hypotheses.  Three are order clauses.  The fourth
is [Rathjen, 1991] 2.1(vi)'s `K`-condition for the indices `collapse`'s strongly critical
branch emits, restricted to level-one arguments:

    PsiIdxStepStd172 : ∀ u a, u ≤ 1 → btLe72 1 a = true → BT.isStd (BT.D u a) = true →
                       KsetStepOK u (dict a)

§73 splits it at `u`.  **The `u = 1` half is proved here, and unconditionally** — neither
`BT.isStd` nor anything else is needed.  The `u = 0` half is NOT proved; §73 states it as one
named hypothesis, measures it, and says what a §74 should try first.

WHAT IS PROVED, UNCONDITIONALLY.

  §73.1–§73.2  **PURITY, AND THE ORDER FACT IT BUYS.**  `pure73` is a purely SYNTACTIC
    predicate on 𝔗(M): no `M`, no `ω̄^·`, every `Z` is `Z 0`, and every `ψ` has a regular
    subscript.  Two things come out of it with no side condition.  `lt_pure73_reg2`: a pure
    term is below `Z 1 = reg 2 = Ω₂`, by an induction on the fuel of 2.3 that touches only
    five of its sixteen clauses.  `fragR_of_pure73` (in §73.4): a pure term is `FragR`, so
    `Evidence/WF.lean` §8.5's order theory — transitivity, asymmetry, trichotomy — applies to
    the whole level-one image **without any `inT` hypothesis**, which is what makes the
    corollaries `lt_trans_dict73` / `lt_comparable_dict73` free of the very gate being proved.

  §73.3–§73.4  **THE LEVEL-ONE IMAGE IS PURE.**  Twenty preservation lemmas, one per
    operation of the dictionary (`ofList`, `toList`, `plus`, `ofNat`, `sub1`, `subAP`,
    `logOm`, `splitFin`, `phiNFdefault`, `phiNFsucc`, `phiNF`, `omegaNF`, `divAP`, `mulL`,
    `wA`, `wC`, `wcnf`, `idxOf`, `stepF`, the fold), then `pure73_dict`.  Unlike §64's `inT`
    versions these carry NO order side conditions: purity is preserved by both branches of
    every `if`, so the comparisons inside `phiNF` and `plus` never have to be decided.  The
    one place where that fails is `omegaNF`'s `ω̄^·` branch and `collapse`'s `ψ_w` branch, and
    both are settled: `lt_M_pure73` kills the first, and for the second the subscript is
    `reg (u+1)`, pure exactly when `u = 0`.

    **`collapse 1` LOOKS CIRCULAR AND IS NOT.**  Its strongly critical branch would emit
    `ψ_{Z 1}`, which is not pure — and it never fires, because `lt_pure73_reg2` puts every
    component of the argument below `Z 1`, so `wcnf (reg 2)` returns the empty pair list
    (`wcnf_reg2_nil73`).  The scan is then literally `[]`, and `ksetStepOK_one73` closes the
    `u = 1` gate with no hypothesis at all.

  §73.5  **THE SPLIT.**  `PsiIdxStep073` is §72's gate with `u` fixed to `0`;
    `psiIdxStepStd172_of_step073` proves §72's gate from it and `step073_of_psiIdxStepStd172`
    records that nothing was lost.  `certIn_t326_step73` re-derives row 326's certificate:
    on the `K` side it now waits on `PsiIdxStep073` alone.

WHAT IS NOT CLAIMED, AND WHAT §73.6 MEASURED.  `PsiIdxStep073` is NOT proved, and the
measurements say the easy routes to it are all closed.

  * **The `K`-sets are not empty.**  `aBad73 = ψ₁(ψ₁ψ₁0 ⊕ ψ₀ψ₁ψ₁ψ₁0)` is level-one and
    Buchholz-standard, its scan fires once, and that step's coefficient is `Γ₀`, whose
    `K_{Ω₁}` is `{0}`.  The step passes because `0 < Γ₀`, not because anything is empty.
  * **§72's `btPool72` cannot see this.**  On its 3519 terms all 378 firing steps have empty
    `K`-sets and `K_{Ω₁}(dict a) < dict a` never fails — both look like theorems and both are
    false.  `aBad73` needs a `ψ`-nesting of 5; `btPool72` reaches 3.  §73 therefore measures
    on `hotB73`, built from a seed that already contains the three-fold `ψ₁`-tower.
  * **`K_{Ω₁}(dict a) < dict a` is FALSE without `BT.isStd`** (79 of 483) **and holds with it**
    (0 of 87).  That statement IS the transport of Buchholz's `G(a,u) < a` that §68 and §72
    named, and this is where `isStd` is spent.  It is not proved here.
  * **The level-one image does contain `ψ_{Ω₁}(β)` with `β ≥ Ω₁`** — 79 of its 218 `ψ`s.  The
    shape that refuted §66 at level three is present at level one as well; the level bound
    does not remove it, the `K`-condition survives it.
  * **The level bound is not decoration.**  `dict (ψ₂0) = Z 1 = Ω₂` itself, so `pure73` and
    `lt · (reg 2)` both fail one level up, and with them the whole `u = 1` argument.

WHAT A §74 SHOULD TRY FIRST.  §73.6's "肯定 3" decomposes the `u = 0` step into four facts,
each measured with 0 failures on all 120 firing steps of `hotB73` and on the sub-region's
1908 pairs, and each an ordinary order statement once the transport above is available:

    (K2)  `K_{Ω₁} aV < aV` and `K_{Ω₁} cV < cV` at every firing pair;
    (K3)  `cV ≤ Δ`;
    (K5)  `aV ≤ Δ` except when `aV = Ω₁`, where `K_{Ω₁} aV = ∅`;
    (K4)  when `sub1 Δ ≠ Δ`, both `K`-sets are empty.

Together with transitivity — free here, by `fragR_of_pure73` — these give the state-free local
condition `localOKb73`, which §73.6 measures at 0 failures everywhere.  What §73 does NOT
provide is the step from that local condition back to `KsetStepOK`: the fold's later steps use
`plus i0 Δ` rather than `sub1 Δ`, and `le i0 (plus i0 Δ)` is an `inT`-conditioned lemma in
§65.1 whose `inT` is exactly what this gate is for.  Breaking that is the second job.
-/

/-! ### §73.1 純粋な項 — `Z 0` までの構文しか使わない形 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **純粋** — `M`・`ω̄^·` を含まず、`Z` は `Z 0` だけ。段 1 以下の `dict` の像が
    ちょうどこの形に留まる。順序の話を一切使わずに構文だけで定義する。 -/
def pure73 : Term → Bool
  | zero => true
  | M => false
  | omg _ => false
  | add a b => pure73 a && pure73 b
  | phi a b => pure73 a && pure73 b
  | psi k a => k.isR && pure73 k && pure73 a
  | Z a => a == zero

theorem pure73_add {a b : Term} (ha : pure73 a = true) (hb : pure73 b = true) :
    pure73 (add a b) = true := by
  show (pure73 a && pure73 b) = true
  rw [ha, hb]; rfl

theorem pure73_add_iff {a b : Term} (h : pure73 (add a b) = true) :
    pure73 a = true ∧ pure73 b = true := (Bool.and_eq_true _ _).mp h

theorem pure73_phi {a b : Term} (ha : pure73 a = true) (hb : pure73 b = true) :
    pure73 (phi a b) = true := by
  show (pure73 a && pure73 b) = true
  rw [ha, hb]; rfl

theorem pure73_psi {k a : Term} (hr : k.isR = true) (hk : pure73 k = true)
    (ha : pure73 a = true) : pure73 (psi k a) = true := by
  show (k.isR && pure73 k && pure73 a) = true
  rw [hr, hk, ha]; rfl

/-- 純粋な項の `ψ` の添字はどれも `Z 0` そのもの。 -/
theorem pure73_psi_iff {k a : Term} (h : pure73 (psi k a) = true) :
    k.isR = true ∧ pure73 k = true ∧ pure73 a = true := by
  have h' : (k.isR && pure73 k && pure73 a) = true := h
  obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h'
  obtain ⟨h3, h4⟩ := (Bool.and_eq_true _ _).mp h1
  exact ⟨h3, h4, h2⟩

theorem pure73_zero : pure73 zero = true := rfl
theorem pure73_one : pure73 TM.Term.one = true := rfl
theorem pure73_reg0 : pure73 (reg 0) = true := rfl
theorem pure73_reg1 : pure73 (reg 1) = true := rfl

/-- `reg 2 = Z 1` は純粋でない。段 1 以下の像に `Z 1` が出ないことが §73.3 の要。 -/
theorem not_pure73_reg2 : pure73 (reg 2) = false := rfl

end

/-! ### §73.2 純粋な項は `Z 1` より小さい -/

section
open Trans.Recal (bplus)
open Trans.Dict (reg)
open TM TM.Term
open Evidence.WF

theorem ltF_succ_add_Z73 (f : Nat) (a b d : Term) :
    ltF (f + 1) (add a b) (Z d) = ltF f a (Z d) := rfl

theorem ltF_succ_zero_Z73 (f : Nat) (d : Term) : ltF (f + 1) zero (Z d) = true := rfl

theorem deg_pos73 : ∀ t : Term, 1 ≤ t.deg
  | zero => Nat.le_refl 1
  | M => Nat.le_refl 1
  | add a b => by show 1 ≤ 1 + a.deg + b.deg; omega
  | omg a => by show 1 ≤ 1 + a.deg; omega
  | phi a b => by show 1 ≤ 1 + a.deg + b.deg; omega
  | psi k a => by show 1 ≤ 1 + k.deg + a.deg; omega
  | Z a => by show 1 ≤ 1 + a.deg; omega

/-- 純粋な項は `Z 1` より小さい — 燃料つきの形。 -/
theorem ltF_pure73_Z1 : ∀ (f : Nat) (t : Term), t.deg + 2 ≤ f + 1 → pure73 t = true →
    ltF (f + 1) t (Z TM.Term.one) = true := by
  intro f
  induction f with
  | zero => intro t hf _; exact absurd hf (by have := deg_pos73 t; omega)
  | succ f ih =>
    intro t hf hp
    cases t with
    | zero => exact ltF_succ_zero_Z73 _ _
    | M => exact Bool.noConfusion hp
    | omg a => exact Bool.noConfusion hp
    | add a b =>
      rw [ltF_succ_add_Z73]
      refine ih a ?_ (pure73_add_iff hp).1
      have h1 : (add a b).deg = 1 + a.deg + b.deg := rfl
      have := deg_pos73 b
      omega
    | phi a b =>
      obtain ⟨ha, hb⟩ := (Bool.and_eq_true _ _).mp hp
      have h1 : (phi a b).deg = 1 + a.deg + b.deg := rfl
      have h2 := deg_pos73 a
      have h3 := deg_pos73 b
      rw [ltF_succ_phi_Z, ih a (by omega) ha, ih b (by omega) hb]
      rfl
    | psi k a =>
      have hk := (pure73_psi_iff hp).2.1
      have h1 : (psi k a).deg = 1 + k.deg + a.deg := rfl
      have h2 := deg_pos73 a
      rw [ltF_succ_psi_Z, if_pos (by rw [ih k (by omega) hk, Bool.or_true])]
    | Z a =>
      have ha : a = zero := of_decide_eq_true (show (a == zero) = true from hp)
      subst ha
      have hne : (Z zero : Term) ≠ Z TM.Term.one := by
        intro hc; injection hc with h1; exact Term.noConfusion h1
      rw [ltF_succ_Z_Z _ hne, if_pos (show ltF (f + 1) zero TM.Term.one = true from rfl),
        starF_succ_zero, ltF_succ_zero_Z73]

/-- **§73.2 の主定理。** 純粋な項は `Z 1 = reg 2` より小さい。 -/
theorem lt_pure73_reg2 {t : Term} (h : pure73 t = true) : lt t (reg 2) = true := by
  show lt t (Z TM.Term.one) = true
  rw [lt_eq_ltF t (Z TM.Term.one) (2 * (t.deg + (Z TM.Term.one).deg) + 7 + 1) (by omega)]
  refine ltF_pure73_Z1 _ t ?_ h
  have h1 : (Z TM.Term.one).deg = 4 := rfl
  omega

end


/-! ### §73.3 純粋性は辞書のすべての演算を通る -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

theorem pure73_phi_iff {a b : Term} (h : pure73 (phi a b) = true) :
    pure73 a = true ∧ pure73 b = true := (Bool.and_eq_true _ _).mp h

theorem pure73_ofList : ∀ (l : List Term), (∀ p ∈ l, pure73 p = true) →
    pure73 (ofList l) = true
  | [], _ => rfl
  | [a], h => h a (List.mem_cons.mpr (Or.inl rfl))
  | a :: b :: r, h => by
    show pure73 (add a (ofList (b :: r))) = true
    exact pure73_add (h a (List.mem_cons.mpr (Or.inl rfl)))
      (pure73_ofList (b :: r) fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))

theorem pure73_toList : ∀ (t : Term), pure73 t = true → ∀ p ∈ toList t, pure73 p = true
  | zero, _, _, hp => by cases hp
  | M, h, _, _ => Bool.noConfusion h
  | omg _, h, _, _ => Bool.noConfusion h
  | add a b, h, p, hp => by
    rcases List.mem_cons.mp (show p ∈ a :: toList b from hp) with h1 | h1
    · rw [h1]; exact (pure73_add_iff h).1
    · exact pure73_toList b (pure73_add_iff h).2 p h1
  | phi a b, h, p, hp => by
    rw [List.mem_singleton.mp (show p ∈ [phi a b] from hp)]; exact h
  | psi k a, h, p, hp => by
    rw [List.mem_singleton.mp (show p ∈ [psi k a] from hp)]; exact h
  | Z a, h, p, hp => by
    rw [List.mem_singleton.mp (show p ∈ [Z a] from hp)]; exact h

theorem pure73_plus {s t : Term} (hs : pure73 s = true) (ht : pure73 t = true) :
    pure73 (plus s t) = true := by
  show pure73 (match toList t with
    | [] => s
    | b1 :: _ => ofList ((toList s).filter (fun a => le b1 a) ++ toList t)) = true
  cases hl : toList t with
  | nil => exact hs
  | cons b1 r =>
    refine pure73_ofList _ ?_
    intro x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact pure73_toList s hs x (List.mem_filter.mp h1).1
    · exact pure73_toList t ht x (by rw [hl]; exact h1)

theorem pure73_ofNat : ∀ n, pure73 (TM.Term.ofNat n) = true
  | 0 => rfl
  | n + 1 => pure73_plus (pure73_ofNat n) pure73_one

theorem pure73_dropIfHead {c : Term} (h : pure73 c = true) (P : Term → Bool) :
    pure73 (match toList c with
            | [] => zero
            | p :: rest => if P p then ofList rest else c) = true := by
  cases hl : toList c with
  | nil => exact pure73_zero
  | cons p rest =>
    show pure73 (if P p = true then ofList rest else c) = true
    split
    · exact pure73_ofList rest fun x hx =>
        pure73_toList c h x (by rw [hl]; exact List.Mem.tail p hx)
    · exact h

theorem pure73_sub1 {c : Term} (h : pure73 c = true) : pure73 (sub1 c) = true :=
  pure73_dropIfHead h (fun p => p == TM.Term.one)

theorem pure73_subAP {w x : Term} (h : pure73 x = true) : pure73 (subAP w x) = true :=
  pure73_dropIfHead h (fun p => p == w)

theorem pure73_logOm {t : Term} (h : pure73 t = true) : pure73 (logOm t) = true := by
  cases t with
  | zero => exact h
  | M => exact h
  | omg a => exact h
  | psi k a => exact h
  | Z a => exact h
  | add a b => exact h
  | phi c d =>
    cases c with
    | zero =>
      show pure73 (if TM.Term.phiShifted zero d then plus d TM.Term.one else d) = true
      have hd := (pure73_phi_iff h).2
      split
      · exact pure73_plus hd pure73_one
      · exact hd
    | M => exact h
    | omg _ => exact h
    | phi _ _ => exact h
    | psi _ _ => exact h
    | Z _ => exact h
    | add _ _ => exact h

theorem pure73_take_ofList {b : Term} (h : pure73 b = true) (k : Nat) :
    pure73 (ofList ((toList b).take k)) = true :=
  pure73_ofList _ fun x hx => pure73_toList b h x (List.mem_of_mem_take hx)

theorem pure73_splitFin {b : Term} (h : pure73 b = true) :
    pure73 (splitFin b).1 = true := pure73_take_ofList h _

theorem pure73_phiNFdefault {a b : Term} (ha : pure73 a = true) (hb : pure73 b = true) :
    pure73 (phiNFdefault a b) = true := by
  unfold TM.Term.phiNFdefault
  split
  · exact ha
  · exact pure73_phi ha hb

theorem pure73_phiNFsucc {a b : Term} (ha : pure73 a = true) (hb : pure73 b = true) :
    pure73 (phiNFsucc a b) = true := by
  have hdef := pure73_phiNFdefault ha hb
  have hg : pure73 (splitFin b).1 = true := pure73_splitFin hb
  unfold TM.Term.phiNFsucc
  split
  rename_i heq
  rw [heq] at hg
  split
  · split <;> (split <;>
      first
        | exact pure73_phi ha (pure73_plus hg (pure73_ofNat _))
        | exact hdef)
  · exact hdef

theorem pure73_phiNF {a b : Term} (ha : pure73 a = true) (hb : pure73 b = true) :
    pure73 (phiNF a b) = true := by
  unfold TM.Term.phiNF
  split
  · exact hb
  · split
    · split
      · exact hb
      · exact pure73_phiNFsucc ha hb
    · exact pure73_phiNFsucc ha hb

theorem beq_M_pure73 : ∀ {t : Term}, pure73 t = true → (t == M) = false
  | zero, _ => rfl
  | M, h => Bool.noConfusion h
  | omg _, h => Bool.noConfusion h
  | add _ _, _ => rfl
  | phi _ _, _ => rfl
  | psi _ _, _ => rfl
  | Z _, _ => rfl

theorem beq_pure73_M : ∀ {t : Term}, pure73 t = true → ((M : Term) == t) = false
  | zero, _ => rfl
  | M, h => Bool.noConfusion h
  | omg _, h => Bool.noConfusion h
  | add _ _, _ => rfl
  | phi _ _, _ => rfl
  | psi _ _, _ => rfl
  | Z _, _ => rfl

theorem ltF_M_pure73 : ∀ (f : Nat) (t : Term), t.deg ≤ f + 1 → pure73 t = true →
    ltF (f + 1) M t = false := by
  intro f
  induction f with
  | zero =>
    intro t hf hp
    cases t with
    | zero => rfl
    | M => exact Bool.noConfusion hp
    | omg _ => exact Bool.noConfusion hp
    | add a b =>
      refine absurd hf ?_
      have h1 : (add a b).deg = 1 + a.deg + b.deg := rfl
      have h2 := deg_pos73 a
      have h3 := deg_pos73 b
      omega
    | phi _ _ => rfl
    | psi _ _ => rfl
    | Z _ => rfl
  | succ f ih =>
    intro t hf hp
    cases t with
    | zero => rfl
    | M => exact Bool.noConfusion hp
    | omg _ => exact Bool.noConfusion hp
    | add a b =>
      rw [ltF_succ_M_add, beq_pure73_M (pure73_add_iff hp).1, Bool.false_or]
      refine ih a ?_ (pure73_add_iff hp).1
      have h1 : (add a b).deg = 1 + a.deg + b.deg := rfl
      have h2 := deg_pos73 b
      omega
    | phi _ _ => rfl
    | psi _ _ => rfl
    | Z _ => rfl

theorem lt_M_pure73 {t : Term} (h : pure73 t = true) : lt M t = false := by
  rw [lt_eq_ltF M t (2 * (M.deg + t.deg) + 7 + 1) (by omega)]
  exact ltF_M_pure73 _ t (by omega) h

theorem pure73_omegaNF {x : Term} (h : pure73 x = true) : pure73 (omegaNF x) = true := by
  show pure73 (if lt M x then omg x else if x == M then M else phiNF zero x) = true
  rw [if_neg (by rw [lt_M_pure73 h]; exact Bool.noConfusion),
    if_neg (by rw [beq_M_pure73 h]; exact Bool.noConfusion)]
  exact pure73_phiNF pure73_zero h

theorem pure73_divAP {w p : Term} (hp : pure73 p = true) : pure73 (divAP w p) = true :=
  pure73_omegaNF (pure73_subAP (pure73_logOm hp))

theorem pure73_mulL {e y : Term} (he : pure73 e = true) (hy : pure73 y = true) :
    pure73 (mulL e y) = true := by
  show pure73 (ofList ((toList y).map (fun p => omegaNF (plus e (logOm p))))) = true
  refine pure73_ofList _ ?_
  intro x hx
  obtain ⟨p, hp, hxe⟩ := List.mem_map.mp hx
  rw [← hxe]
  exact pure73_omegaNF (pure73_plus he (pure73_logOm (pure73_toList y hy p hp)))

theorem pure73_wA {w p : Term} (hp : pure73 p = true) : pure73 (wA w p) = true := by
  refine pure73_ofList _ ?_
  intro x hx
  obtain ⟨q, hq, hxe⟩ := List.mem_map.mp hx
  rw [← hxe]
  exact pure73_divAP (pure73_toList _ (pure73_logOm hp) q (List.mem_filter.mp hq).1)

theorem pure73_wC {w p : Term} (hp : pure73 p = true) : pure73 (wC w p) = true := by
  refine pure73_omegaNF (pure73_ofList _ ?_)
  intro x hx
  exact pure73_toList _ (pure73_logOm hp) x (List.mem_filter.mp hx).1

/-- `wcnf` の返り値がすべて純粋であること。 -/
def PurePair73 (r : List (Term × Term) × Term) : Prop :=
  pure73 r.2 = true ∧ ∀ ac ∈ r.1, pure73 ac.1 = true ∧ pure73 ac.2 = true

theorem pure73_wcnf {w : Term} : ∀ (L : List Term), (∀ x ∈ L, pure73 x = true) →
    PurePair73 (wcnf w L) := by
  intro L
  induction L with
  | nil => intro _; exact ⟨pure73_zero, by intro ac hac; cases hac⟩
  | cons p rest ih =>
    intro hm
    have hp : pure73 p = true := hm p (List.Mem.head _)
    have IH := ih fun x hx => hm x (List.Mem.tail p hx)
    by_cases hlp : lt p w = true
    · rw [wcnf_cons_lt hlp]
      exact ⟨pure73_ofList _ hm, by intro ac hac; cases hac⟩
    · rw [wcnf_cons_ge (bool_false hlp)]
      have hA := pure73_wA (w := w) hp
      have hC := pure73_wC (w := w) hp
      cases hr : wcnf w rest with
      | mk fst snd =>
        rw [hr] at IH
        obtain ⟨hs, hall⟩ := IH
        cases fst with
        | nil =>
          refine ⟨hs, ?_⟩
          intro ac hac
          rw [List.mem_singleton.mp hac]
          exact ⟨hA, hC⟩
        | cons ac0 ps =>
          cases ac0 with
          | mk a' c' =>
            have hac0 := hall (a', c') (List.Mem.head _)
            show PurePair73 (if (wA w p == a') = true
              then ((wA w p, plus (wC w p) c') :: ps, snd)
              else ((wA w p, wC w p) :: (a', c') :: ps, snd))
            by_cases heq : (wA w p == a') = true
            · rw [if_pos heq]
              refine ⟨hs, ?_⟩
              intro ac hac
              rcases List.mem_cons.mp hac with h | h
              · rw [h]; exact ⟨hA, pure73_plus hC hac0.2⟩
              · exact hall ac (List.Mem.tail _ h)
            · rw [if_neg heq]
              refine ⟨hs, ?_⟩
              intro ac hac
              rcases List.mem_cons.mp hac with h | h
              · rw [h]; exact ⟨hA, hC⟩
              · exact hall ac h

end


/-! ### §73.4 `dict` の像は純粋 — そして `u = 1` の門は無条件 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **純粋な項は `FragR`。** `Evidence/WF.lean` §8.5 の順序理論 — 推移律・三分律 —
    が `inT` を仮定せずに使えるようになる。`ψ` の添字が `Z 0` だけであることが要。 -/
theorem fragR_of_pure73 : ∀ (t : Term), pure73 t = true → FragR t = true
  | zero, _ => rfl
  | M, _ => rfl
  | omg _, h => Bool.noConfusion h
  | add a b, h => by
    show (FragR a && FragR b) = true
    rw [fragR_of_pure73 a (pure73_add_iff h).1, fragR_of_pure73 b (pure73_add_iff h).2]
    rfl
  | phi a b, h => by
    show (FragR a && FragR b) = true
    rw [fragR_of_pure73 a (pure73_phi_iff h).1, fragR_of_pure73 b (pure73_phi_iff h).2]
    rfl
  | psi k a, h => by
    obtain ⟨hr, hk, ha⟩ := pure73_psi_iff h
    show (k.isR && FragR k && FragR a) = true
    rw [hr, fragR_of_pure73 k hk, fragR_of_pure73 a ha]
    rfl
  | Z a, h => by
    have ha : a = zero := of_decide_eq_true (show (a == zero) = true from h)
    subst ha
    rfl

theorem pure73_reg73 : ∀ u : Nat, u ≤ 1 → pure73 (reg u) = true
  | 0, _ => rfl
  | 1, _ => rfl
  | _ + 2, h => absurd h (by omega)

theorem pure73_getD73 {o : Option Term} (h : ∀ v, o = some v → pure73 v = true) :
    pure73 (o.getD zero) = true := by
  cases hq : o with
  | none => exact pure73_zero
  | some v => exact h v hq

/-- 畳み込みの状態が純粋であること。 -/
def StPure73 (s : Option Term × Option Term) : Prop :=
  (∀ i0, s.1 = some i0 → pure73 i0 = true) ∧ (∀ v, s.2 = some v → pure73 v = true)

theorem stPure73_init : StPure73 ((none : Option Term), (none : Option Term)) :=
  ⟨(by intro i0 h; cases h), (by intro v h; cases h)⟩

theorem pure73_idxOf {w : Term} {s : Option Term × Option Term} {ac : Term × Term}
    (hw : pure73 w = true) (hs : StPure73 s)
    (h1 : pure73 ac.1 = true) (h2 : pure73 ac.2 = true) :
    pure73 (idxOf w s ac) = true := by
  have hd : pure73 (mulL (mulL w (subAP w ac.1)) ac.2) = true :=
    pure73_mulL (pure73_mulL hw (pure73_subAP h1)) h2
  unfold idxOf
  split
  · exact pure73_sub1 hd
  · rename_i i0 heq
    exact pure73_plus (hs.1 i0 heq) hd

theorem stPure73_stepF {w base : Term} {s : Option Term × Option Term} {ac : Term × Term}
    (hwR : w.isR = true) (hw : pure73 w = true) (hb : pure73 base = true) (hs : StPure73 s)
    (h1 : pure73 ac.1 = true) (h2 : pure73 ac.2 = true) :
    StPure73 (stepF w base s ac) := by
  have hi := pure73_idxOf hw hs h1 h2
  unfold stepF
  split
  · exact ⟨(by intro i0 h; rw [← Option.some.inj h]; exact hi),
      (by intro v h; rw [← Option.some.inj h]; exact pure73_psi hwR hw hi)⟩
  · refine ⟨hs.1, ?_⟩
    intro v h
    rw [← Option.some.inj h]
    refine pure73_phiNF h1 (pure73_plus ?_ ?_)
    · cases hq : s.2 with
      | none => exact hb
      | some v0 => exact hs.2 v0 hq
    · cases hq : s.2 with
      | none => exact pure73_sub1 h2
      | some _ => exact h2

theorem stPure73_fold {w base : Term} (hwR : w.isR = true) (hw : pure73 w = true)
    (hb : pure73 base = true) :
    ∀ (l : List (Term × Term)) (s : Option Term × Option Term), StPure73 s →
      (∀ ac ∈ l, pure73 ac.1 = true ∧ pure73 ac.2 = true) →
      StPure73 (l.foldl (stepF w base) s) := by
  intro l
  induction l with
  | nil => intro s hs _; exact hs
  | cons ac t ih =>
    intro s hs hall
    have h0 := hall ac (List.Mem.head _)
    exact ih (stepF w base s ac) (stPure73_stepF hwR hw hb hs h0.1 h0.2)
      (fun a ha => hall a (List.Mem.tail _ ha))

/-- 成分がすべて `w` より小さければ `wcnf` は対を出さない。 -/
theorem wcnf_nil73 {w : Term} : ∀ (L : List Term), (∀ p ∈ L, lt p w = true) →
    (wcnf w L).1 = []
  | [], _ => rfl
  | p :: rest, h => by rw [wcnf_cons_lt (h p (List.Mem.head _))]

theorem pure73_collapse0_73 {x : Term} (hx : pure73 x = true) :
    pure73 (collapse 0 x) = true := by
  have hP := pure73_wcnf (w := reg (0+1)) (toList x) (pure73_toList x hx)
  rw [collapse_eq]
  refine pure73_omegaNF (pure73_plus pure73_reg0 (pure73_plus ?_ hP.1))
  refine pure73_getD73 ?_
  exact (stPure73_fold (w := reg (0+1)) (base := baseOf 0) (isR_reg_succ 0) pure73_reg1 pure73_zero
    (wcnf (reg (0+1)) (toList x)).1 (none, none) stPure73_init hP.2).2

theorem pure73_collapse1_73 {x : Term} (hx : pure73 x = true) :
    pure73 (collapse 1 x) = true := by
  have hP := pure73_wcnf (w := reg (1+1)) (toList x) (pure73_toList x hx)
  have hnil : (wcnf (reg (1+1)) (toList x)).1 = [] :=
    wcnf_nil73 _ fun p hp => lt_pure73_reg2 (pure73_toList x hx p hp)
  rw [collapse_eq, hnil]
  exact pure73_omegaNF (pure73_plus (pure73_reg73 1 (by omega))
    (pure73_plus pure73_zero hP.1))

theorem pure73_collapse73 (u : Nat) (hu : u ≤ 1) {x : Term} (hx : pure73 x = true) :
    pure73 (collapse u x) = true := by
  cases u with
  | zero => exact pure73_collapse0_73 hx
  | succ u' =>
    cases u' with
    | zero => exact pure73_collapse1_73 hx
    | succ u'' => exact absurd hu (by omega)

/-- **§73.4 の主定理。** 段 1 以下の `BT` の像は純粋。 -/
theorem pure73_dict : ∀ (a : BT), btLe72 1 a = true → pure73 (dict a) = true
  | .zero, _ => rfl
  | .D u a, hb => by
    obtain ⟨hu, hba⟩ := btLe72_D 1 u a hb
    rw [Trans.Dict.dict_D]
    exact pure73_collapse73 u hu (pure73_dict a hba)
  | .sum a b, hb => by
    obtain ⟨hba, hbb⟩ := btLe72_sum 1 a b hb
    rw [Trans.Dict.dict_sum]
    exact pure73_plus (pure73_dict a hba) (pure73_dict b hbb)

/-- 段 1 以下の像は `Ω₂ = reg 2` の下。 -/
theorem lt_dict_reg2_73 (a : BT) (hb : btLe72 1 a = true) : lt (dict a) (reg 2) = true :=
  lt_pure73_reg2 (pure73_dict a hb)

/-- **`u = 1` では `wcnf` が対を出さない** — 走査そのものが空。 -/
theorem wcnf_reg2_nil73 (a : BT) (hb : btLe72 1 a = true) :
    (wcnf (reg (1+1)) (toList (dict a))).1 = [] :=
  wcnf_nil73 _ fun p hp => lt_pure73_reg2 (pure73_toList _ (pure73_dict a hb) p hp)

/-- **§73 の第一の結論。** 段 1 以下では `u = 1` の門は**無条件に**閉じる。
    `BT.isStd` も要らない。 -/
theorem ksetStepOK_one73 (a : BT) (hb : btLe72 1 a = true) : KsetStepOK 1 (dict a) := by
  intro p hp _
  rw [wcnf_reg2_nil73 a hb] at hp
  cases hp

/-- **段 1 以下の像の上では順序理論に `inT` が要らない。** `fragR_of_pure73` の系で、
    証明しようとしている門そのものを仮定せずに推移律が使える。 -/
theorem lt_trans_dict73 {a b c : BT} (ha : btLe72 1 a = true) (hb : btLe72 1 b = true)
    (hc : btLe72 1 c = true) (h1 : lt (dict a) (dict b) = true)
    (h2 : lt (dict b) (dict c) = true) : lt (dict a) (dict c) = true :=
  lt_trans3 (fragR_of_pure73 _ (pure73_dict a ha)) (fragR_of_pure73 _ (pure73_dict b hb))
    (fragR_of_pure73 _ (pure73_dict c hc)) h1 h2

theorem lt_comparable_dict73 {a b : BT} (ha : btLe72 1 a = true) (hb : btLe72 1 b = true) :
    lt (dict a) (dict b) = true ∨ dict a = dict b ∨ lt (dict b) (dict a) = true :=
  lt_comparable3 (fragR_of_pure73 _ (pure73_dict a ha)) (fragR_of_pure73 _ (pure73_dict b hb))

/-! **段 1 の上限は飾りではない。** `dict (ψ₂0)` は `Z 1 = reg 2` そのもので、
`pure73` も `lt · (reg 2)` もそこで落ちる。 -/

#guard dict (BT.D 2 BT.zero) == reg 2
#guard !(pure73 (dict (BT.D 2 BT.zero)))
#guard !(lt (dict (BT.D 2 BT.zero)) (reg 2))
#guard !(btLe72 1 (BT.D 2 BT.zero))

end


/-! ### §73.5 門の分割 — 残るのは `u = 0` の一節だけ -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf reg collapse)
open TM TM.Term
open Evidence.WF

/-- **残る門。** §72 の `PsiIdxStepStd172` から `u = 1` を抜いたもの。**証明しない。** -/
def PsiIdxStep073 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → KsetStepOK 0 (dict a)

/-- **§73 の第二の結論。** §72 の門は `u = 0` の一節に落ちる。`u = 1` は §73.4 が
    無条件に閉じているので、仮定に残らない。 -/
theorem psiIdxStepStd172_of_step073 (H : PsiIdxStep073) : PsiIdxStepStd172 := by
  intro u a hu hb h
  cases u with
  | zero => exact H a hb h
  | succ u' =>
    cases u' with
    | zero => exact ksetStepOK_one73 a hb
    | succ u'' => exact absurd hu (by omega)

/-- 逆向き — 分割が本当に分割であることの記録。 -/
theorem step073_of_psiIdxStepStd172 (H : PsiIdxStepStd172) : PsiIdxStep073 :=
  fun a hb h => H 0 a (by omega) hb h

/-- §72 の第二の門も `u = 0` の一節から出る。 -/
theorem psiIdxOKStd172_of_step073 (H : PsiIdxStep073) : PsiIdxOKStd172 :=
  psiIdxOKStd172_of_step172 (psiIdxStepStd172_of_step073 H)

/-- 領域の値は 𝔗(M) の項 — `u = 0` の一節の上で。 -/
theorem inT_vOf_step73 (H : PsiIdxStep073) (t : B) (ht : stdB1 t = true) :
    inT (vOf t) = true :=
  inT_vOf_step72 (psiIdxStepStd172_of_step073 H) t ht

/-- **§73 の第三の結論。** 326 行目の証明書が `K` の側で待っているのは
    `PsiIdxStep073` — 段 1 以下・`u = 0`・一歩ぶん — ただ一つ。残りは §70.5 の
    3 つの順序の条項と停止性。 -/
theorem certIn_t326_step73 (H : PsiIdxStep073)
    (HD : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_step72 (psiIdxStepStd172_of_step073 H) HD HI HC hacc

end


/-! ### §73.6 測定 (凍結)

母集団の作り方を先に書く。§72 の `btPool72` は**この節には浅すぎる** (否定 1)。

    d1a73 = ψ₁0,  d1b73 = ψ₁ψ₁0,  d1c73 = ψ₁ψ₁ψ₁0
    hot073 = [0, ψ₀0, d1a73, d1b73, d1c73, ψ₀d1c73, ψ₁d1c73, ψ₀d1b73]        8 個
    hotA73 = dg72 (sg72 hot073)                                            209 個
    hotB73 = dg72 hotA73                                                   483 個
      ただし dg72 l = l ++ {ψ₀a, ψ₁a : a ∈ l}、sg72 l = l ++ {a ⊕ b : a,b ∈ l}
      (どちらも §72 のもの)。`isStd` では絞らずに作る。
    btPool72 = §72 の 3519 個 (`ψ` の入れ子はたかだか 3 段)
    regPairs72 (sub72 8) = §72 の部分領域の 1908 個の `(u, a)`
    aBad73 = ψ₁(ψ₁ψ₁0 ⊕ ψ₀ψ₁ψ₁ψ₁0)  — `btPool72` には**入っていない** (入れ子 5 段) -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 項の中の `ψ` を (添字, 引数) の対として全部集める。 -/
def psis73 : Term → List (Term × Term)
  | zero => []
  | M => []
  | omg a => psis73 a
  | add a b => psis73 a ++ psis73 b
  | phi a b => psis73 a ++ psis73 b
  | psi k a => (k, a) :: psis73 k ++ psis73 a
  | Z a => psis73 a

def d1a73 : BT := BT.D 1 BT.zero
def d1b73 : BT := BT.D 1 d1a73
def d1c73 : BT := BT.D 1 d1b73
def hot073 : List BT :=
  [BT.zero, BT.D 0 BT.zero, d1a73, d1b73, d1c73, BT.D 0 d1c73, BT.D 1 d1c73, BT.D 0 d1b73]
def hotA73 : List BT := dg72 (sg72 hot073)
def hotB73 : List BT := dg72 hotA73
def aBad73 : BT := BT.D 1 (BT.sum d1b73 (BT.D 0 d1c73))
/-- 移送 `K_{Ω₁}(dict a) < dict a` の最小の反例 (`BT` の大きさ 6)。 -/
def wKOK73 : BT := BT.D 0 (BT.D 1 d1c73)

/-- 走査のうち強臨界枝を取る歩だけ (`u = 0`)。 -/
def fires73 (a : BT) : List ((Option Term × Option Term) × (Term × Term)) :=
  (scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1).filter
    (fun p => le (reg 1) p.2.1)
/-- 指数の材料 `Δ = Ω₁·(a ⊖ Ω₁) の ω 冪 × c`。 -/
def dd73 (p : (Option Term × Option Term) × (Term × Term)) : Term :=
  mulL (mulL (reg 1) (subAP (reg 1) p.2.1)) p.2.2
/-- 2.1(vi) の `K` の連言そのもの — 「`K_{Ω₁} t < t`」。 -/
def KOK73 (t : Term) : Bool := (Kset (reg 1) t).all fun y => lt y t
/-- 状態を落とした局所条件の判定器 (§73.7 の候補)。 -/
def localOKb73 (u : Nat) (x : Term) : Bool :=
  (wcnf (reg (u+1)) (toList x)).1.all fun ac =>
    !(le (reg (u+1)) ac.1) ||
      ((Kset (reg (u+1)) ac.1 ++ Kset (reg (u+1)) ac.2).all fun y =>
        lt y (sub1 (mulL (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) ac.2)))

-- 母集団の大きさ。
#guard hotA73.length == 209
#guard hotB73.length == 483
#guard (hotB73.filter fun a => BT.isStd (BT.D 0 a)).length == 87
#guard hotB73.all (btLe72 1)

/-! **否定 1 — §72 の `btPool72` はこの節には浅すぎる。** 3519 個の上では
`u = 0` の強臨界枝は 378 歩 firing するが、そのどれも `K` が空で、しかも
`K_{Ω₁}(dict a) < dict a` が一度も落ちない。**どちらも定理に見えるが、どちらも偽。**
反例は `ψ` の入れ子が 5 段いる (`btPool72` はたかだか 3 段)。 -/

#guard (btPool72.flatMap fires73).length == 378
#guard ((btPool72.flatMap fires73).filter fun p =>
  !((Kset (reg 1) p.2.1 ++ Kset (reg 1) p.2.2).isEmpty)).length == 0
#guard (btPool72.filter fun a => !(KOK73 (dict a))).length == 0
#guard !(btPool72.contains aBad73)
#guard hotB73.contains aBad73

/-! **否定 2 — 「発火する歩の `K` は空」という道は偽。** `aBad73` は段 1 以下で
`BT.isStd (ψ₀ ·)` を満たし、走査は 1 歩だけ発火して、その対は `(Ω₁, Γ₀)`。
`K_{Ω₁} Γ₀ = {0}` は空でない。それでも一歩ぶんの条件は通る — 通る理由は
「`K` が空」ではなく「`0 < Γ₀`」である。 -/

#guard BT.isStd (BT.D 0 aBad73) && btLe72 1 aBad73
#guard (fires73 aBad73).length == 1
#guard ((fires73 aBad73).map fun p =>
  ((Kset (reg 1) p.2.1).length, (Kset (reg 1) p.2.2).length)) == [(0, 1)]
#guard stepOKb 0 (dict aBad73)

/-- **否定 2、定理の形。** `aBad73` は段 1 以下で Buchholz 標準。 -/
theorem std_aBad73 : BT.isStd (BT.D 0 aBad73) = true ∧ btLe72 1 aBad73 = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **発火する歩の `K` は空ではない。** 係数 `cV = Γ₀` の `K_{Ω₁}` は `{0}`。 -/
theorem kset_fires_aBad73 :
    ((fires73 aBad73).map fun p => (Kset (reg 1) p.2.2).length) = [1] := by decide

/-- それでも一歩ぶんの条件は通る — 「`K` が空だから」ではない。 -/
theorem stepOKb_aBad73 : stepOKb 0 (dict aBad73) = true := by decide

/-! **否定 3 — `K_{Ω₁}(dict a) < dict a` は `BT.isStd` なしでは偽。**
`hotB73` の 483 個のうち 79 個で落ちる。`BT.isStd (ψ₀ a)` で絞った 87 個では 0 個。
**これが §68・§72 が名指しした「Buchholz の `G(a,u) < a` の移送」で、`isStd` は
まさにそこで要る。** -/

#guard (hotB73.filter fun a => !(KOK73 (dict a))).length == 79
#guard (hotB73.filter fun a => BT.isStd (BT.D 0 a) && !(KOK73 (dict a))).length == 0

/-- **否定 3、定理の形。** 段 1 以下で、大きさ 6 の `ψ₀ψ₁ψ₁ψ₁ψ₁0` が移送を落とす。
    Buchholz 標準ではない — そして標準性を課した母集団では 0 失敗 (上の `#guard`)。 -/
theorem not_KOK73_wKOK73 :
    btLe72 1 wKOK73 = true ∧ BT.isStd (BT.D 0 wKOK73) = false ∧ KOK73 (dict wKOK73) = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! **否定 4 — 段 1 の像にも `ψ_{Ω₁}(β)` で `β ≥ Ω₁` のものが出る。**
§66 の反例を殺したのはこの形だったが、段 1 でも 218 個の `ψ` のうち 79 個がこの形。
添字はどれも `Ω₁ = reg 1` ちょうど (§73.4 の `pure73_dict` の系)。
**形が安全なのではなく `K` の条件が効いている。** -/

#guard (hotB73.flatMap fun a => psis73 (dict a)).length == 218
#guard (hotB73.flatMap fun a => (psis73 (dict a)).filter fun q => q.1 != reg 1).length == 0
#guard (hotB73.flatMap fun a => (psis73 (dict a)).filter fun q => !(lt q.2 (reg 1))).length == 79

/-! **否定 5 — `u = 0` は空回りしない。** `hotB73` で 120 歩が発火し、うち 4 歩は
`K_{Ω₁} aV` が、3 歩は `K_{Ω₁} cV` が空でなく、1 歩は前の指数を持つ。 -/

#guard (hotB73.flatMap fires73).length == 120
#guard ((hotB73.flatMap fires73).filter fun p => !((Kset (reg 1) p.2.1).isEmpty)).length == 4
#guard ((hotB73.flatMap fires73).filter fun p => !((Kset (reg 1) p.2.2).isEmpty)).length == 3
#guard ((hotB73.flatMap fires73).filter fun p => p.1.1.isSome).length == 1

/-! **肯定 1 — §73.2・§73.4 の定理の判定器での裏取り。** 段 1 以下の像は
`Z 1` の下、`u = 1` の `wcnf` は対を出さない。 -/

#guard hotB73.all fun a => pure73 (dict a)
#guard btPool72.all fun a => pure73 (dict a)
#guard hotB73.all fun a => lt (dict a) (reg 2)
#guard hotB73.all fun a => (wcnf (reg 2) (toList (dict a))).1.isEmpty
#guard btPool72.all fun a => (wcnf (reg 2) (toList (dict a))).1.isEmpty

/-! **肯定 2 — 残る門 `PsiIdxStep073` は 0 失敗。** `isStd` を課さなくても落ちない
(課さないでよいとは**言わない** — 否定 3 が示すとおり、その先の補題には要る)。 -/

#guard (hotB73.filter fun a => !(stepOKb 0 (dict a))).length == 0
#guard (btPool72.filter fun a => !(stepOKb 0 (dict a))).length == 0
#guard ((regPairs72 (sub72 8)).filter fun q => !(stepOKb q.1 (dict q.2))).length == 0
#guard ((regPairs72 (sub72 8)).filter fun q => !(KOK73 (dict q.2))).length == 0

/-! **肯定 3 — §74 への分解。** 状態を落とした局所条件 `localOKb73` は 0 失敗で、
発火する歩ごとに次の 4 つが成り立つ (`d := Δ`):

    (K2)  `K_{Ω₁} aV < aV` かつ `K_{Ω₁} cV < cV`                    120 歩で 0 失敗
    (K3)  `cV ≤ d`                                                  120 歩で 0 失敗
    (K5)  `aV ≰ d` は 30 歩、うち 29 歩は `aV = Ω₁` (そこで `K aV = ∅`)、
          残り 1 歩も `K aV = ∅`                                     0 失敗
    (K4)  `sub1 d ≠ d` の 26 歩では `K aV = K cV = ∅`                0 失敗

この 4 つと推移律 (`fragR_of_pure73` で `inT` 抜きに使える) から局所条件が出る。 -/

#guard (hotB73.filter fun a => !(localOKb73 0 (dict a))).length == 0
#guard (btPool72.filter fun a => !(localOKb73 0 (dict a))).length == 0
#guard ((regPairs72 (sub72 8)).filter fun q => !(localOKb73 q.1 (dict q.2))).length == 0
#guard ((hotB73.flatMap fires73).filter fun p => !(KOK73 p.2.1) || !(KOK73 p.2.2)).length == 0
#guard ((hotB73.flatMap fires73).filter fun p => !(le p.2.2 (dd73 p))).length == 0
#guard ((hotB73.flatMap fires73).filter fun p => !(le p.2.1 (dd73 p))).length == 30
#guard ((hotB73.flatMap fires73).filter fun p => p.2.1 == reg 1).length == 29
#guard ((hotB73.flatMap fires73).filter fun p =>
  p.2.1 != reg 1 && !(le p.2.1 (dd73 p)) && !((Kset (reg 1) p.2.1).isEmpty)).length == 0
#guard ((hotB73.flatMap fires73).filter fun p => sub1 (dd73 p) != dd73 p).length == 26
#guard ((hotB73.flatMap fires73).filter fun p => sub1 (dd73 p) != dd73 p &&
  !((Kset (reg 1) p.2.1 ++ Kset (reg 1) p.2.2).isEmpty)).length == 0

end

/-! ### §73.7 公理 -/

/-! ## §74 THE ORDER BRIDGE — WHICH HALF IS FREE, WHAT THE MEASUREMENT MEASURES,
    AND EXACTLY WHERE IT STOPS

§71 reduced row 326's decreasing and increasing clauses to ONE hypothesis, the order bridge
`VOfLtA71`, and split cofinality so that its index-side half rides on the OTHER direction,
`VOfLtA71'`.  §74 is about those two.  **The second one stops being an independent
hypothesis.**  It is a THEOREM given the first, so `certIn_t326_bt71`'s eight hypotheses
become seven, and every measurement of `VOfLtA71` is at the same time a measurement of
`VOfLtA71'`.  The bridge ITSELF is NOT proved; §74.6 says in two named pieces what is left,
and §74.8 says what was swept.

WHAT IS PROVED, UNCONDITIONALLY.

  §74.1  **THE BUCHHOLZ ORDER IS TRICHOTOMOUS.**  `toL` only ever returns `.D` atoms —
         `atomsL_any74` proves `AtomsL` for EVERY `BT`, so it is a theorem and not a side
         condition, and `BT.ltL`'s junk branch (`| _, _ => false`, the one that makes the
         decision partial) is unreachable on component lists.  `ltS_tricho74` is trichotomy
         by induction on `sizeLB`, `lt_tricho74` lifts it to `BT.lt`.  The one hypothesis it
         does need is `Hwf74`: every `.D`'s argument must satisfy `BT.ofL a.toL = a`.
         **That is not decoration.**  `BT.zero` and `BT.sum BT.zero BT.zero` have the same
         component list and are different terms, so `.D 0 .zero` and `.D 0 (.sum .zero .zero)`
         are incomparable AND unequal — §74.8 freezes the witness.

  §74.4  **AND IT IS IRREFLEXIVE AND ASYMMETRIC, with no side condition at all.**
         `lt_irrefl74` / `lt_asymm74` hold for every `BT`, `Hwf74` or not: those two need
         only that the recursion follows the same `if`-chain on both sides.  `lt_tricho3_74`
         puts the three together in the exclusive form — the Buchholz-side counterpart of
         `Evidence/WF.lean` §8.4's `lt_trichotomy_inT`.

  §74.2  The sub-region's values are hereditarily rebuildable: `nfSum_bValA7174`
         unconditionally, `hwf74_bValA7174` from `lvlLe 1` through §71.6's
         `bArg_eq_bValA71_71` (below level 2 the collapsing branch never fires, so the
         argument of every `.D` is again a `bValA71`).  Hence `lt_tricho_bValA7174`:
         any two sub-region indices are comparable on the Buchholz side.

  §74.3  **`bVal` IS A FUNCTION OF `bValA71`.**  `bVal_eq_strip74`:

             bVal t = BT.ofL (stripL74 (bValA71 t).toL)         (lvlLe 1 t)

         where `stripL74` drops a leading `ψ₀0` and does nothing else.  That is the ENTIRE
         leading-`(0,0)` exception of §71.2, stated in the direction that can be used
         backwards: equal `bValA71` forces equal `bVal`, hence equal `vOf`
         (`vOf_eq_of_bValA7174`).  Without it the "the two values are equal" branch of the
         trichotomy cannot be closed, and the reduction below does not go through.
         (Measured beyond its hypothesis: it holds on all 1291 trees with ≤ 4 nodes and
         levels < 3 and all 3941 with levels < 4.  `lvlLe 1` is used only to know
         `bArg w c = 0 ⟺ c = nil`, which is where the fold would have to be analysed.)

  §74.5  **THE BRIDGE ONLY HAS TO BE PROVED IN ONE DIRECTION.**

             vOfLtA71'_of74 (Hp) (Hr) (HV : VOfLtA71) : VOfLtA71'

         Three ingredients and nothing else: trichotomy on the Buchholz side (§74.1/§74.2),
         `vOf` being well defined on `bValA71` (§74.3), and the linearity of `lt` on 𝔗(M)
         (`Evidence/WF.lean` §8.4 — that is all `Hp`/`Hr` are for here, they supply
         `inT (vOf ·)` and nothing else).  The same three give `vOfInj_of74`: **the bridge
         PROVES that `vOf` is injective on the sub-region**, which §71 could only measure.
         The converse `vOfLtA71_of74` needs that injectivity back as a hypothesis
         (`VOfInjA74`), and `vOfLt_iff74` packages the pair:
         `VOfLtA71 ↔ VOfInjA74 ∧ VOfLtA71'`.

  §74.6  **THE MEASURED FORM IS THE HYPOTHESIS, AND THE HYPOTHESIS IS `dict`.**  §71.8
         measured an EQUALITY of Booleans, not an implication.  `bridgeEq_iff74` proves
         `BridgeEq74 ↔ VOfLtA71` (given `Hp`/`Hr`), so `bridgeFail71 == 0` measures the
         hypothesis itself and nothing weaker.  `vOfLtA71_of_dict74` then splits the bridge
         into two named halves:

             VOfIsDict74 :  vOf t = dict (bValA71 t)              on the sub-region
             DictLtA74   :  dict preserves `BT.lt` on those values

         `DictLtA74` is `Trans/Dict.lean`'s acceptance record item (C) verbatim.
         `VOfIsDict74` is the bookkeeping half — the `1 +` of `vOf` against the leading
         `ψ₀0` of `bValA71` — and it is NOT free: 2390 of `subP 8`'s 2397 indices have a
         leading component that is not `ψ₀0`, and for those the identity is exactly
         `1 + ψ₀(α) = ψ₀(α)`, i.e. `ψ₀(α) ≥ ω` for `α ≠ 0`, which needs `collapse`
         unfolded.  §74 does not unfold it.

  §74.7  `certIn_t326_74'` — §71's best form with `VOfLtA71'` deleted.  Row 326's
         certificate now stands on FIVE hypotheses: §68's `PsiIdxOKStd` / `RegionStd`, the
         bridge `VOfLtA71`, the density half `CofDenseS1`, and `BCofIn71`, which mentions
         no `dict` at all.  §71's best was six.  (`certIn_t326_74` does the same to
         `certIn_t326_bt71`, which still carries §71.7's two cores as hypotheses.)

WHAT THE MEASUREMENT SAYS (§74.8 gives every construction).  **The negative result first:
STANDARDNESS IS ESSENTIAL AND THE LEVEL BOUND IS NOT ENOUGH.**  On `nf1_74 6` — the 465
normal-form indices with ≤ 5 nodes and levels ≤ 1, standard or not — the bridge fails on
51 143 of the 216 225 ordered pairs.  305 of the 465 are non-standard, and EVERY failing
pair has a non-standard endpoint: restricted to the 160 standard ones (= `subP 6`) there is
not one failure.  So `stdB1` cannot be relaxed to `nfB && lvlLe 1`, and the smallest witness
is `(0,0)(1,0)` against `(0,0)(0,0)(1,1)`, the second of which `stdB` rejects.

The same split is confirmed one size up (`s74sweep3.lean`): on `nf1_74 7`'s 2772 indices —
2163 of them non-standard — 2 233 666 of the 7 683 984 pairs fail, and ZERO of the failures
has both endpoints standard.

Positively: zero counterexamples to the equality on `subP 6` (25 600 pairs), `subP 7`
(370 881, §71.8's population) and `subP 8` (5 745 609, `s74sweep1.lean`), and the sweep is
not vacuous — 12 720 of `subP 6`'s 25 600 pairs have `BT.lt` true.  `vOf` and `bValA71` are
both injective on `subP 8`.  **A more general form falls out of the measurement, not of the
proof:** the same equality holds on `popS 3 6` (235 standard indices, levels 0..2),
`popS 4 6` (250, levels 0..3), `popS 3 7` (1105) and `popS 4 7` (1263) — 2 816 194 further
pairs in `s74sweep2.lean` — i.e. §69's un-restricted `VOfLtStd` shape, with no failure.
`VOfIsDict74` is measured well past the sub-region: `subP 8` (2397), `popNFB 3 7` (4958,
levels 0..2) and `allB71 3 6` (11 497, no normal form and no standardness), zero mismatches.

WHAT IS **NOT** CLAIMED.  `VOfLtA71`, `VOfInjA74`, `VOfIsDict74`, `DictLtA74`, `CofDenseS1`
and `BCofIn71` are NAMED AND UNPROVED.  §74 proves nothing about `dict`: not that it
preserves the order, not that it is injective, not that its image is `vOf`.  The
`popS 3 6` / `popS 4 6` measurement is a measurement — nothing here says the bridge holds
above level 1, and §71.6's collapsing branch, which §74.2 relies on being unreachable, does
fire at level 2.  Nothing here repairs `LimCofS1`: `CofDenseS1` still stands untouched, and
§69's counterexample outside the sub-region is untouched too. -/

/-! ### §74.1 Buchholz 側の順序は線型である -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- `toL` が返すのはいつでも `.D` の列。`AtomsL` は仮定ではなく定理である。 -/
theorem atomsL_any74 : ∀ t : BT, AtomsL t
  | .zero => atomsL_zero
  | .D u a => atomsL_D u a
  | .sum a b => by
      intro x hx
      rcases List.mem_append.mp (show x ∈ a.toL ++ b.toL from hx) with h | h
      · exact atomsL_any74 a x h
      · exact atomsL_any74 b x h

theorem atoms_toL74 (t : BT) : Atoms t.toL := atomsL_any74 t

/-- **遺伝的な `ofL` 正規性。** どの `.D` の引数も成分から組み直せる。 -/
def Hwf74 : BT → Prop
  | .zero => True
  | .D _ a => NfSum a ∧ Hwf74 a
  | .sum a b => Hwf74 a ∧ Hwf74 b

theorem hwf74_zero : Hwf74 .zero := trivial

theorem hwf74_D {u : Nat} {a : BT} (h1 : NfSum a) (h2 : Hwf74 a) : Hwf74 (.D u a) := ⟨h1, h2⟩

theorem hwf74_toL : ∀ (t : BT), Hwf74 t → ∀ z ∈ t.toL, Hwf74 z
  | .zero => by intro _ z hz; exact absurd hz (by simp [Trans.Dict.BT.toL])
  | .D u a => by
      intro h z hz
      rw [List.mem_singleton.mp (show z ∈ [BT.D u a] from hz)]; exact h
  | .sum a b => by
      intro h z hz
      rcases List.mem_append.mp (show z ∈ a.toL ++ b.toL from hz) with hh | hh
      · exact hwf74_toL a h.1 z hh
      · exact hwf74_toL b h.2 z hh

theorem hwf74_ofL : ∀ (l : List BT), (∀ z ∈ l, Hwf74 z) → Hwf74 (BT.ofL l)
  | [], _ => trivial
  | [x], h => h x (List.Mem.head _)
  | x :: y :: r, h => ⟨h x (List.Mem.head _),
      hwf74_ofL (y :: r) (fun z hz => h z (List.Mem.tail x hz))⟩

theorem hwf74_bplus {a b : BT} (ha : Hwf74 a) (hb : Hwf74 b) : Hwf74 (bplus a b) := by
  refine hwf74_ofL _ (fun z hz => ?_)
  rcases List.mem_append.mp hz with h | h
  · exact hwf74_toL a ha z h
  · exact hwf74_toL b hb z h

/-- **§74.1 の主定理。** `ltS` は遺伝的に正規な `.D` の列の上で三分律を満たす。 -/
theorem ltS_tricho74 : ∀ (n : Nat) (x y : List BT), Atoms x → Atoms y →
    (∀ z ∈ x, Hwf74 z) → (∀ z ∈ y, Hwf74 z) → sizeLB x + sizeLB y ≤ n →
    ltS x y = true ∨ x = y ∨ ltS y x = true := by
  intro n
  induction n with
  | zero =>
    intro x y _ _ _ _ hn
    cases x with
    | nil => cases y with
      | nil => exact Or.inr (Or.inl rfl)
      | cons z zs =>
        exact absurd hn (by have := one_le_size z; show ¬ (0 + (z.size + sizeLB zs) ≤ 0); omega)
    | cons z zs =>
      exact absurd hn (by have := one_le_size z
                          show ¬ ((z.size + sizeLB zs) + sizeLB y ≤ 0); omega)
  | succ k ih =>
    intro x y hax hay hwx hwy hn
    cases x with
    | nil => cases y with
      | nil => exact Or.inr (Or.inl rfl)
      | cons y0 ys => exact Or.inl (by
          obtain ⟨v, b, rfl⟩ := hay y0 (List.Mem.head _)
          exact ltS_nil_cons _ _)
    | cons x0 xs =>
      obtain ⟨u, a, rfl⟩ := hax x0 (List.Mem.head _)
      cases y with
      | nil => exact Or.inr (Or.inr (ltS_nil_cons _ _))
      | cons y0 ys =>
        obtain ⟨v, b, rfl⟩ := hay y0 (List.Mem.head _)
        have hsx : sizeLB (BT.D u a :: xs) = (1 + a.size) + sizeLB xs := rfl
        have hsy : sizeLB (BT.D v b :: ys) = (1 + b.size) + sizeLB ys := rfl
        by_cases h3 : u < v
        · exact Or.inl (by rw [ltS_cons u a xs v b ys, if_pos h3])
        · by_cases h4 : v < u
          · exact Or.inr (Or.inr (by rw [ltS_cons v b ys u a xs, if_pos h4]))
          · by_cases h5 : (a == b) = true
            · have hab : a = b := bt_eq_of_beq71 a b h5
              subst hab
              have hba : (a == a) = true := bt_beq_self71 a
              rcases ih xs ys (fun z hz => hax z (List.Mem.tail _ hz))
                  (fun z hz => hay z (List.Mem.tail _ hz))
                  (fun z hz => hwx z (List.Mem.tail _ hz))
                  (fun z hz => hwy z (List.Mem.tail _ hz))
                  (by have := one_le_size a; omega) with h | h | h
              · exact Or.inl (by
                  rw [ltS_cons u a xs v a ys, if_neg h3, if_neg h4, if_pos hba]; exact h)
              · exact Or.inr (Or.inl (by
                  rw [h, show u = v from Nat.le_antisymm (Nat.not_lt.mp h4) (Nat.not_lt.mp h3)]))
              · exact Or.inr (Or.inr (by
                  rw [ltS_cons v a ys u a xs, if_neg h4, if_neg h3, if_pos hba]; exact h))
            · have hwa : Hwf74 (BT.D u a) := hwx _ (List.Mem.head _)
              have hwb : Hwf74 (BT.D v b) := hwy _ (List.Mem.head _)
              have hta := sizeLB_toL a
              have htb := sizeLB_toL b
              rcases ih a.toL b.toL (atoms_toL74 a) (atoms_toL74 b)
                  (hwf74_toL a hwa.2) (hwf74_toL b hwb.2) (by omega) with h | h | h
              · exact Or.inl (by
                  rw [ltS_cons u a xs v b ys, if_neg h3, if_neg h4, if_neg h5]; exact h)
              · exact absurd (show (a == b) = true from by
                    rw [show a = b from by
                      rw [← show BT.ofL a.toL = a from hwa.1,
                        ← show BT.ofL b.toL = b from hwb.1, h]]
                    exact bt_beq_self71 b) h5
              · exact Or.inr (Or.inr (by
                  rw [ltS_cons v b ys u a xs, if_neg h4, if_neg h3,
                    if_neg (show ¬((b == a) = true) from by
                      intro hc; exact h5 (by rw [bt_eq_of_beq71 b a hc]; exact bt_beq_self71 a))]
                  exact h))

/-- **`BT.lt` の三分律。** -/
theorem lt_tricho74 (s t : BT) (hs : Hwf74 s) (ht : Hwf74 t) (hns : NfSum s) (hnt : NfSum t) :
    BT.lt s t = true ∨ s = t ∨ BT.lt t s = true := by
  rw [lt_eq_ltS, lt_eq_ltS]
  rcases ltS_tricho74 (sizeLB s.toL + sizeLB t.toL) s.toL t.toL
      (atoms_toL74 s) (atoms_toL74 t) (hwf74_toL s hs) (hwf74_toL t ht)
      (Nat.le_refl _) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by rw [← show BT.ofL s.toL = s from hns,
      ← show BT.ofL t.toL = t from hnt, h]))
  · exact Or.inr (Or.inr h)

end

/-! ### §74.2 部分領域の値は遺伝的に正規 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

theorem nfSum_bValA7174 : ∀ t : B, NfSum (bValA71 t)
  | .nil => nfSum_zero
  | .nd _ r c => nfSum_bplus (bValA71 r) (BT.D _ (bArg _ c)) (atomsL_any74 _) (atomsL_any74 _)

theorem hwf74_bValA7174 : ∀ (t : B), lvlLe 1 t = true → Hwf74 (bValA71 t)
  | .nil => fun _ => trivial
  | .nd w r c => by
      intro h
      obtain ⟨_, hr, hc⟩ := (lvlLe_nd_iff 1 w r c).mp h
      show Hwf74 (bplus (bValA71 r) (BT.D w (bArg w c)))
      refine hwf74_bplus (hwf74_bValA7174 r hr) (hwf74_D ?_ ?_)
      · rw [bArg_eq_bValA71_71 c w hc]; exact nfSum_bValA7174 c
      · rw [bArg_eq_bValA71_71 c w hc]; exact hwf74_bValA7174 c hc

theorem append_singleton_ne_nil74 (l : List BT) (x : BT) : l ++ [x] ≠ [] := by
  cases l with
  | nil => exact List.cons_ne_nil x []
  | cons z zs => exact List.cons_ne_nil z (zs ++ [x])

theorem toL_bValA71_ne_nil74 : ∀ (t : B), t ≠ .nil → (bValA71 t).toL ≠ []
  | .nil => fun h => absurd rfl h
  | .nd w r c => fun _ => by
      rw [toL_bValA71_nd w r c]; exact append_singleton_ne_nil74 _ _

theorem bValA71_ne_zero74 (t : B) (h : t ≠ .nil) : bValA71 t ≠ .zero := by
  intro hc
  exact toL_bValA71_ne_nil74 t h (by rw [hc]; rfl)

/-- **部分領域での三分律。** -/
theorem lt_tricho_bValA7174 (u t : B) (hu : lvlLe 1 u = true) (ht : lvlLe 1 t = true) :
    BT.lt (bValA71 u) (bValA71 t) = true ∨ bValA71 u = bValA71 t
      ∨ BT.lt (bValA71 t) (bValA71 u) = true :=
  lt_tricho74 _ _ (hwf74_bValA7174 u hu) (hwf74_bValA7174 t ht)
    (nfSum_bValA7174 u) (nfSum_bValA7174 t)

end

/-! ### §74.3 `bVal` は `bValA71` の関数である — 先頭の `(0,0)` を落とすだけ -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- 先頭が `ψ₀0` ならそれを落とす。`bVal` と `bValA71` の差はこれだけ。 -/
def stripL74 : List BT → List BT
  | BT.D 0 BT.zero :: rest => rest
  | l => l

theorem stripL74_cons_eq74 (zs : List BT) : stripL74 (BT.D 0 BT.zero :: zs) = zs := rfl

theorem stripL74_cons_ne74 (z : BT) (zs : List BT) (h : z ≠ BT.D 0 BT.zero) :
    stripL74 (z :: zs) = z :: zs := by
  cases z with
  | zero => rfl
  | sum p q => rfl
  | D u a =>
    cases u with
    | zero =>
      cases a with
      | zero => exact absurd rfl h
      | D p b => rfl
      | sum p q => rfl
    | succ k => rfl

theorem stripL74_append74 (l m : List BT) (h : l ≠ []) :
    stripL74 (l ++ m) = stripL74 l ++ m := by
  cases l with
  | nil => exact absurd rfl h
  | cons z zs =>
    by_cases hz : z = BT.D 0 BT.zero
    · subst hz
      rw [List.cons_append, stripL74_cons_eq74, stripL74_cons_eq74]
    · rw [List.cons_append, stripL74_cons_ne74 z (zs ++ m) hz,
        stripL74_cons_ne74 z zs hz, List.cons_append]

theorem atoms_stripL74 (l : List BT) (h : Atoms l) : Atoms (stripL74 l) := by
  cases l with
  | nil => exact h
  | cons z zs =>
    by_cases hz : z = BT.D 0 BT.zero
    · subst hz; rw [stripL74_cons_eq74]; exact fun x hx => h x (List.Mem.tail _ hx)
    · rw [stripL74_cons_ne74 z zs hz]; exact h

/-- **§74.3 の主定理。** `bVal` は `bValA71` の成分列から先頭の `ψ₀0` を落として組み直したもの。
    段 1 以下でのみ主張する — `bArg w c = 0 ⟺ c = nil` がそこでしか言えないため。 -/
theorem bVal_eq_strip74 : ∀ (t : B), lvlLe 1 t = true →
    bVal t = BT.ofL (stripL74 (bValA71 t).toL) := by
  intro t
  induction t with
  | nil => intro _; rfl
  | nd w r c ihr _ =>
    intro h
    obtain ⟨_, hr, hc⟩ := (lvlLe_nd_iff 1 w r c).mp h
    have hA : bArg w c = bValA71 c := bArg_eq_bValA71_71 c w hc
    cases r with
    | nil =>
      by_cases hc0 : c = B.nil
      · subst hc0
        by_cases hw0 : w = 0
        · subst hw0
          show bplus (bVal B.nil) BT.zero = _
          rw [toL_bValA71_nd 0 B.nil B.nil,
            show (bValA71 B.nil).toL = ([] : List BT) from rfl,
            show bArg 0 B.nil = BT.zero from rfl, List.nil_append, stripL74_cons_eq74]
          rfl
        · show bplus (bVal B.nil) (if (B.nil == B.nil && w == 0 && B.nil == B.nil) = true
              then BT.zero else BT.D w (bArg w B.nil)) = _
          rw [if_neg (show ¬((B.nil == B.nil && w == 0 && B.nil == B.nil) = true) from by
              intro hcc
              obtain ⟨h1, _⟩ := (Bool.and_eq_true _ _).mp hcc
              obtain ⟨_, h3⟩ := (Bool.and_eq_true _ _).mp h1
              exact hw0 (eq_of_beq h3))]
          rw [toL_bValA71_nd w B.nil B.nil,
            show (bValA71 B.nil).toL = ([] : List BT) from rfl, List.nil_append,
            stripL74_cons_ne74 _ _ (show BT.D w (bArg w B.nil) ≠ BT.D 0 BT.zero from by
              intro hcc; injection hcc with h1 _; exact hw0 h1)]
          rfl
      · show bplus (bVal B.nil) (if (B.nil == B.nil && w == 0 && c == B.nil) = true
              then BT.zero else BT.D w (bArg w c)) = _
        rw [if_neg (show ¬((B.nil == B.nil && w == 0 && c == B.nil) = true) from by
            intro hcc
            obtain ⟨_, h2⟩ := (Bool.and_eq_true _ _).mp hcc
            exact hc0 (of_decide_eq_true h2))]
        rw [toL_bValA71_nd w B.nil c,
          show (bValA71 B.nil).toL = ([] : List BT) from rfl, List.nil_append,
          stripL74_cons_ne74 _ _ (show BT.D w (bArg w c) ≠ BT.D 0 BT.zero from by
            intro hcc; injection hcc with _ h2
            rw [hA] at h2
            exact bValA71_ne_zero74 c hc0 h2)]
        rfl
    | nd v s a =>
      have hrne : (B.nd v s a) ≠ B.nil := fun hcc => B.noConfusion hcc
      have hnn : (bValA71 (B.nd v s a)).toL ≠ [] := toL_bValA71_ne_nil74 _ hrne
      have hbr : bVal (B.nd v s a) = BT.ofL (stripL74 (bValA71 (B.nd v s a)).toL) := ihr hr
      have htbr : (bVal (B.nd v s a)).toL = stripL74 (bValA71 (B.nd v s a)).toL := by
        rw [hbr]
        exact toL_ofL _ (atoms_stripL74 _ (atoms_toL74 _))
      show bplus (bVal (B.nd v s a)) (if (B.nd v s a == B.nil && w == 0 && c == B.nil) = true
          then BT.zero else BT.D w (bArg w c)) = _
      rw [if_neg (show ¬((B.nd v s a == B.nil && w == 0 && c == B.nil) = true) from by
          intro hcc
          obtain ⟨h1, _⟩ := (Bool.and_eq_true _ _).mp hcc
          obtain ⟨h2, _⟩ := (Bool.and_eq_true _ _).mp h1
          exact Bool.noConfusion h2)]
      show BT.ofL ((bVal (B.nd v s a)).toL ++ (BT.D w (bArg w c)).toL) = _
      rw [htbr, toL_bValA71_nd w (B.nd v s a) c, stripL74_append74 _ _ hnn]
      rfl

/-- **`bValA71` が決まれば `vOf` も決まる。** -/
theorem vOf_eq_of_bValA7174 (u t : B) (hu : lvlLe 1 u = true) (ht : lvlLe 1 t = true)
    (h : bValA71 u = bValA71 t) : vOf u = vOf t := by
  cases u with
  | nil => cases t with
    | nil => rfl
    | nd w r c =>
      exact absurd h.symm (bValA71_ne_zero74 (.nd w r c) (fun hcc => B.noConfusion hcc))
  | nd w1 r1 c1 => cases t with
    | nil => exact absurd h (bValA71_ne_zero74 (.nd w1 r1 c1) (fun hcc => B.noConfusion hcc))
    | nd w2 r2 c2 =>
      show TM.Term.plus TM.Term.one (Trans.Dict.dict (bVal (B.nd w1 r1 c1)))
         = TM.Term.plus TM.Term.one (Trans.Dict.dict (bVal (B.nd w2 r2 c2)))
      rw [bVal_eq_strip74 _ hu, bVal_eq_strip74 _ ht, h]

end

/-! ### §74.4 反射律と反対称律 — 燃料の再帰で直に -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

theorem ltS_irrefl74 : ∀ (n : Nat) (x : List BT), Atoms x → sizeLB x + sizeLB x ≤ n →
    ltS x x = false := by
  intro n
  induction n with
  | zero =>
    intro x _ hn
    cases x with
    | nil => exact ltS_nil_nil
    | cons z zs =>
      exact absurd hn (by have := one_le_size z
                          show ¬ ((z.size + sizeLB zs) + (z.size + sizeLB zs) ≤ 0); omega)
  | succ k ih =>
    intro x hax hn
    cases x with
    | nil => exact ltS_nil_nil
    | cons x0 xs =>
      obtain ⟨u, a, rfl⟩ := hax x0 (List.Mem.head _)
      rw [ltS_cons u a xs u a xs, if_neg (Nat.lt_irrefl u), if_neg (Nat.lt_irrefl u),
        if_pos (bt_beq_self71 a)]
      exact ih xs (fun z hz => hax z (List.Mem.tail _ hz))
        (by have := one_le_size a
            have h1 : sizeLB (BT.D u a :: xs) = (1 + a.size) + sizeLB xs := rfl
            omega)

theorem ltS_asymm74 : ∀ (n : Nat) (x y : List BT), Atoms x → Atoms y →
    sizeLB x + sizeLB y ≤ n → ltS x y = true → ltS y x = false := by
  intro n
  induction n with
  | zero =>
    intro x y _ _ hn _
    cases x with
    | nil => cases y with
      | nil => exact ltS_nil_nil
      | cons z zs =>
        exact absurd hn (by have := one_le_size z
                            show ¬ (0 + (z.size + sizeLB zs) ≤ 0); omega)
    | cons z zs =>
      exact absurd hn (by have := one_le_size z
                          show ¬ ((z.size + sizeLB zs) + sizeLB y ≤ 0); omega)
  | succ k ih =>
    intro x y hax hay hn hlt
    cases x with
    | nil => cases y with
      | nil => exact ltS_nil_nil
      | cons y0 ys =>
        obtain ⟨v, b, rfl⟩ := hay y0 (List.Mem.head _)
        exact ltS_cons_nil _ _
    | cons x0 xs =>
      obtain ⟨u, a, rfl⟩ := hax x0 (List.Mem.head _)
      cases y with
      | nil => exact absurd hlt (by rw [ltS_cons_nil]; exact fun hc => Bool.noConfusion hc)
      | cons y0 ys =>
        obtain ⟨v, b, rfl⟩ := hay y0 (List.Mem.head _)
        have hsx : sizeLB (BT.D u a :: xs) = (1 + a.size) + sizeLB xs := rfl
        have hsy : sizeLB (BT.D v b :: ys) = (1 + b.size) + sizeLB ys := rfl
        by_cases h3 : u < v
        · rw [ltS_cons v b ys u a xs, if_neg (Nat.not_lt.mpr (Nat.le_of_lt h3)), if_pos h3]
        · rw [ltS_cons u a xs v b ys, if_neg h3] at hlt
          by_cases h4 : v < u
          · exact absurd hlt (by rw [if_pos h4]; exact fun hc => Bool.noConfusion hc)
          · rw [if_neg h4] at hlt
            rw [ltS_cons v b ys u a xs, if_neg h4, if_neg h3]
            by_cases h5 : (a == b) = true
            · have hab : a = b := bt_eq_of_beq71 a b h5
              subst hab
              rw [if_pos h5] at hlt
              rw [if_pos (bt_beq_self71 a)]
              exact ih xs ys (fun z hz => hax z (List.Mem.tail _ hz))
                (fun z hz => hay z (List.Mem.tail _ hz))
                (by have := one_le_size a; omega) hlt
            · rw [if_neg h5] at hlt
              rw [if_neg (show ¬((b == a) = true) from by
                intro hc; exact h5 (by rw [bt_eq_of_beq71 b a hc]; exact bt_beq_self71 a))]
              have hta := sizeLB_toL a
              have htb := sizeLB_toL b
              exact ih a.toL b.toL (atoms_toL74 a) (atoms_toL74 b) (by omega) hlt

/-- **`BT.lt` は非反射的。** 無条件。 -/
theorem lt_irrefl74 (s : BT) : BT.lt s s = false := by
  rw [lt_eq_ltS]
  exact ltS_irrefl74 (sizeLB s.toL + sizeLB s.toL) s.toL (atoms_toL74 s) (Nat.le_refl _)

/-- **`BT.lt` は反対称的。** 無条件。 -/
theorem lt_asymm74 {s t : BT} (h : BT.lt s t = true) : BT.lt t s = false := by
  rw [lt_eq_ltS] at h
  rw [lt_eq_ltS]
  exact ltS_asymm74 (sizeLB s.toL + sizeLB t.toL) s.toL t.toL
    (atoms_toL74 s) (atoms_toL74 t) (Nat.le_refl _) h

/-- **Buchholz 側の順序は狭義の全順序である。** 三分律を排他の形で書いたもの
    (`Evidence/WF.lean` §8.4 の `lt_trichotomy_inT` の Buchholz 側の相方)。 -/
theorem lt_tricho3_74 (s t : BT) (hs : Hwf74 s) (ht : Hwf74 t) (hns : NfSum s) (hnt : NfSum t) :
    (BT.lt s t = true ∧ s ≠ t ∧ BT.lt t s = false)
  ∨ (BT.lt s t = false ∧ s = t ∧ BT.lt t s = false)
  ∨ (BT.lt s t = false ∧ s ≠ t ∧ BT.lt t s = true) := by
  rcases lt_tricho74 s t hs ht hns hnt with h | h | h
  · refine Or.inl ⟨h, ?_, lt_asymm74 h⟩
    intro hc; rw [hc, lt_irrefl74] at h; exact Bool.noConfusion h
  · subst h; exact Or.inr (Or.inl ⟨lt_irrefl74 s, rfl, lt_irrefl74 s⟩)
  · refine Or.inr (Or.inr ⟨lt_asymm74 h, ?_, h⟩)
    intro hc; rw [hc, lt_irrefl74] at h; exact Bool.noConfusion h

end

/-! ### §74.5 橋は一方向で足りる -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term
open Evidence.WF

/-- **§74.5 の主定理。** `VOfLtA71` から `VOfLtA71'` が出る。使うのは Buchholz 側の
    三分律 (§74.1)、`bVal` が `bValA71` の関数であること (§74.3)、そして 𝔗(M) の
    順序が非反射・反対称であること (`Evidence/WF.lean` §8.4) だけ。 -/
theorem vOfLtA71'_of74 (Hp : PsiIdxOKStd) (Hr : RegionStd) (HV : VOfLtA71) : VOfLtA71' := by
  intro u t hu ht hlt
  rcases lt_tricho_bValA7174 u t (lvlLe1_of_stdB1 u hu) (lvlLe1_of_stdB1 t ht) with h | h | h
  · exact h
  · exact absurd hlt (by
      rw [vOf_eq_of_bValA7174 u t (lvlLe1_of_stdB1 u hu) (lvlLe1_of_stdB1 t ht) h,
        Evidence.WF.lt_irrefl]
      exact fun hc => Bool.noConfusion hc)
  · exact absurd hlt (by
      rw [lt_asymm_inT (inT_vOf_std Hp Hr t (stdB_of_stdB1 t ht))
        (inT_vOf_std Hp Hr u (stdB_of_stdB1 u hu)) (HV t u ht hu h)]
      exact fun hc => Bool.noConfusion hc)

/-- **橋は `vOf` の単射性も出す。** -/
theorem vOfInj_of74 (HV : VOfLtA71) (u t : B) (hu : stdB1 u = true) (ht : stdB1 t = true)
    (h : vOf u = vOf t) : bValA71 u = bValA71 t := by
  rcases lt_tricho_bValA7174 u t (lvlLe1_of_stdB1 u hu) (lvlLe1_of_stdB1 t ht) with hh | hh | hh
  · exact absurd (HV u t hu ht hh)
      (by rw [h, Evidence.WF.lt_irrefl]; exact fun hc => Bool.noConfusion hc)
  · exact hh
  · exact absurd (HV t u ht hu hh)
      (by rw [h, Evidence.WF.lt_irrefl]; exact fun hc => Bool.noConfusion hc)

/-- 逆向きに要る単射性。**未証明** — §74.6 で測る。 -/
def VOfInjA74 : Prop := ∀ (u t : B), stdB1 u = true → stdB1 t = true →
    vOf u = vOf t → bValA71 u = bValA71 t

/-- **逆向き。** `VOfLtA71'` と単射性から `VOfLtA71`。§74.5 と合わせて、単射性の下では
    橋の二つの向きは同値である。 -/
theorem vOfLtA71_of74 (Hp : PsiIdxOKStd) (Hr : RegionStd) (HI : VOfInjA74) (HV' : VOfLtA71') :
    VOfLtA71 := by
  intro u t hu ht hlt
  rcases lt_comparable_inT (inT_vOf_std Hp Hr u (stdB_of_stdB1 u hu))
      (inT_vOf_std Hp Hr t (stdB_of_stdB1 t ht)) with h | h | h
  · exact h
  · exact absurd hlt (by rw [HI u t hu ht h, lt_irrefl74]; exact fun hc => Bool.noConfusion hc)
  · exact absurd hlt (by rw [lt_asymm74 (HV' t u ht hu h)]; exact fun hc => Bool.noConfusion hc)

/-- **単射性は橋から出るので、同値は片側だけの話になる。** -/
theorem vOfLt_iff74 (Hp : PsiIdxOKStd) (Hr : RegionStd) :
    VOfLtA71 ↔ (VOfInjA74 ∧ VOfLtA71') :=
  ⟨fun HV => ⟨fun u t hu ht h => vOfInj_of74 HV u t hu ht h, vOfLtA71'_of74 Hp Hr HV⟩,
   fun h => vOfLtA71_of74 Hp Hr h.1 h.2⟩

end

/-! ### §74.6 測定の形 — 等号と、`dict` への還元 -/

section
open Trans.Recal
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

/-- §71.8 が実際に測ったのはこの等号である (含意ではない)。 -/
def BridgeEq74 : Prop := ∀ (u t : B), stdB1 u = true → stdB1 t = true →
    BT.lt (bValA71 u) (bValA71 t) = lt (vOf u) (vOf t)

/-- **等号は片側の含意から出る。** -/
theorem bridgeEq_of74 (Hp : PsiIdxOKStd) (Hr : RegionStd) (HV : VOfLtA71) : BridgeEq74 := by
  intro u t hu ht
  cases h : BT.lt (bValA71 u) (bValA71 t) with
  | true => exact (HV u t hu ht h).symm
  | false =>
    rcases lt_tricho_bValA7174 u t (lvlLe1_of_stdB1 u hu) (lvlLe1_of_stdB1 t ht) with
      hh | hh | hh
    · exact absurd hh (by rw [h]; exact fun hc => Bool.noConfusion hc)
    · rw [vOf_eq_of_bValA7174 u t (lvlLe1_of_stdB1 u hu) (lvlLe1_of_stdB1 t ht) hh,
        Evidence.WF.lt_irrefl]
    · rw [lt_asymm_inT (inT_vOf_std Hp Hr t (stdB_of_stdB1 t ht))
        (inT_vOf_std Hp Hr u (stdB_of_stdB1 u hu)) (HV t u ht hu hh)]

theorem vOfLtA71_of_bridgeEq74 (H : BridgeEq74) : VOfLtA71 :=
  fun u t hu ht h => by rw [← H u t hu ht]; exact h

theorem vOfLtA71'_of_bridgeEq74 (H : BridgeEq74) : VOfLtA71' :=
  fun u t hu ht h => by rw [H u t hu ht]; exact h

/-- **測定の形と仮説の形は同値。** `bridgeFail71 == 0` が言っているのは左辺である。 -/
theorem bridgeEq_iff74 (Hp : PsiIdxOKStd) (Hr : RegionStd) : BridgeEq74 ↔ VOfLtA71 :=
  ⟨vOfLtA71_of_bridgeEq74, bridgeEq_of74 Hp Hr⟩

/-- **添字の値は `dict` の像そのもの。** `vOf` の `1 +` は `bValA71` の先頭の `ψ₀0` と
    同じもの。**未証明** — 段 1 以下の部分領域でも `ψ₀(α) ≥ ω` (`α ≠ 0`) が要る。
    §74.8 で 11 497 個の添字 (標準形も標準性も問わない) について測る。 -/
def VOfIsDict74 : Prop := ∀ (t : B), stdB1 t = true → vOf t = dict (bValA71 t)

/-- **`dict` が順序を保つこと** — `Trans/Dict.lean` の受領記録 (C) そのもの。**未証明。** -/
def DictLtA74 : Prop := ∀ (u t : B), stdB1 u = true → stdB1 t = true →
    BT.lt (bValA71 u) (bValA71 t) = true → lt (dict (bValA71 u)) (dict (bValA71 t)) = true

/-- **§74.6 の主定理。** 橋は「値は `dict` の像である」と「`dict` は順序を保つ」の
    二つに割れる。§74 が止まったのはこの二つの手前である。 -/
theorem vOfLtA71_of_dict74 (H1 : VOfIsDict74) (H2 : DictLtA74) : VOfLtA71 := by
  intro u t hu ht h
  rw [H1 u hu, H1 t ht]
  exact H2 u t hu ht h

end

/-! ### §74.7 組み立て -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- **§71.5 の `certIn_t326_bt71` から `VOfLtA71'` が落ちる。** 仮説は 7 つ。 -/
theorem certIn_t326_74 (Hp : PsiIdxOKStd) (Hr : RegionStd)
    (HV : VOfLtA71) (HBD : BDecCore71) (HBI : BIncCore71)
    (HCD : CofDenseS1) (HBC : BCofIn71)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_bt71 Hp Hr HV (vOfLtA71'_of74 Hp Hr HV) HBD HBI HCD HBC hacc

/-- **§74 の最終形。** §71.7 が減少と増加を定理にしたので、`certIn_t326_71'` の側に
    §74.5 を差すと、326 行目の証明書が持つ仮説は

        `Hp`・`Hr` (§68 の 2 つ)、橋 `VOfLtA71`、密度 `CofDenseS1`、
        そして Buchholz 側だけの `BCofIn71`

    の 5 つになる。`dict` を含むのはうち 4 つ (`BCofIn71` は `dict` を含まない)。
    §71 の最良は `VOfLtA71'` を別に要求して 6 つだった。 -/
theorem certIn_t326_74' (Hp : PsiIdxOKStd) (Hr : RegionStd)
    (HV : VOfLtA71) (HCD : CofDenseS1) (HBC : BCofIn71)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_71' Hp Hr HV HCD
    (cofInS1_of71 Hp Hr (vOfLtA71'_of74 Hp Hr HV) HBC) hacc

end

/-! ### §74.8 測定 (凍結)

母集団の作り方を先に書く。添字の側は §70.6 / §71.8 のものに二つ足す:

    popNFB L n = ((List.range n).flatMap (enumNodes L)).filter (nfB · && · != nil)
                 節は 0 … n-1 個、段は 0 … L-1
    subP n     = (popNFB 2 n).filter stdB1              段 1 以下の標準な添字 (部分領域)
    popS L n   = (popNFB L n).filter stdB               段の上限を外した標準な添字
    allB71 L n = (List.range n).flatMap (enumNodes L)   標準形も標準性も問わない全列挙
    nf1_74 n   = (popNFB 2 n).filter (lvlLe 1 ·)        段 1 以下の標準形、**標準性は問わない**

`nf1_74` が §74 で新しく足したもので、否定的な結果はここで出る。重い掃きは

    s74sweep1.lean   subP 8 (2397) の 2397² = 5 745 609 対              反例 0
    s74sweep2.lean   popS 3 7 (1105) の 1 221 025 対、popS 4 7 (1263) の
                     1 595 169 対 — **部分領域の外**、段 2・段 3 まで       反例 0
    s74sweep3.lean   nf1_74 7 (2772、うち標準でないもの 2163) の 7 683 984 対
                     — 2 233 666 対で落ちるが、両端が標準な対は 0

に凍結してある。合計 16 245 787 対。 -/

section
open Trans.Recal
open Trans.Dict (BT dict)
open TM TM.Term

/-- 段 1 以下の標準形。**標準性は問わない** — 橋が落ちるのはここ。 -/
def nf1_74 (n : Nat) : List B := (popNFB 2 n).filter fun t => lvlLe 1 t

/-- 等号の形で数える (§71.8 の `bridgeFail71` と同じ主張、値を先に作る)。 -/
def pairFail74 (l : List B) : Nat :=
  let vs := l.map fun t => (bValA71 t, vOf t)
  (vs.flatMap fun p => vs.filter fun q => !(BT.lt p.1 q.1 == lt p.2 q.2)).length

/-! **§74.1 の鋭さ。** `Hwf74` を落とすと三分律は本当に壊れる。成分列が同じで項が違う
二つ — これが `BT.ltL` の唯一の穴である。 -/

#guard BT.lt (BT.D 0 BT.zero) (BT.D 0 (BT.sum BT.zero BT.zero)) == false
#guard BT.lt (BT.D 0 (BT.sum BT.zero BT.zero)) (BT.D 0 BT.zero) == false
#guard ((BT.D 0 BT.zero) == (BT.D 0 (BT.sum BT.zero BT.zero))) == false
#guard (BT.zero).toL == (BT.sum BT.zero BT.zero).toL

/-! **§74.3 の受領と、その仮説の緩さ。** 定理なので `subP` の行は確認であり、
`allB71` の行は `lvlLe 1` が鋭くないことの測定である。 -/

#guard (subP 8).all fun t => bVal t == BT.ofL (stripL74 (bValA71 t).toL)
#guard (allB71 3 5).length == 1291
#guard ((allB71 3 5).filter fun t => bVal t != BT.ofL (stripL74 (bValA71 t).toL)).length == 0
#guard (allB71 4 5).length == 3941
#guard ((allB71 4 5).filter fun t => bVal t != BT.ofL (stripL74 (bValA71 t).toL)).length == 0

/-! **先頭の成分の割れ方。** `bVal` が `bValA71` と違うのは先頭が `ψ₀0` のときだけで、
それは自然数の添字 7 個しかない。残る 2390 個では `VOfIsDict74` は `1 + ψ₀(α) = ψ₀(α)`
そのものになる — §74.6 が止まったのはここ。 -/

#guard (subP 8).length == 2397
#guard ((subP 8).filter fun t => (bValA71 t).toL.head? == some (BT.D 0 BT.zero)).length == 7
#guard ((subP 8).filter fun t => (bValA71 t).toL.head? != some (BT.D 0 BT.zero)).length == 2390

/-! **`VOfIsDict74` の測定。** 部分領域の外まで走らせる — 段 2 まで、標準形でも標準でも
ないものまで。反例 0。**未証明。** -/

#guard (subP 8).all fun t => vOf t == dict (bValA71 t)
#guard (popNFB 3 7).length == 4958
#guard ((popNFB 3 7).filter fun t => vOf t != dict (bValA71 t)).length == 0
#guard (allB71 3 6).length == 11497
#guard ((allB71 3 6).filter fun t => vOf t != dict (bValA71 t)).length == 0

/-! **`VOfInjA74` の測定。** `vOf` も `bValA71` も部分領域で単射。§74.5 はこれを橋から
出すので、これは橋を測るのと同じ強さの測定である。 -/

#guard ((subP 8).map vOf).eraseDups.length == 2397
#guard ((subP 8).map bValA71).eraseDups.length == 2397

/-! **橋そのもの (等号の形)。** `subP 8` は `s74sweep1.lean`。 -/

#guard (subP 6).length == 160
#guard pairFail74 (subP 6) == 0
#guard (subP 7).length == 609
#guard pairFail74 (subP 7) == 0
-- 掃きが空回りしていないこと。`BT.lt` が真になる対の数。
#guard ((subP 6).flatMap fun u =>
  (subP 6).filter fun t => BT.lt (bValA71 u) (bValA71 t)).length == 12720

/-! **否定的な結果 — 標準性は落とせない。** 段 1 以下の標準形でも、標準でない添字を
入れると橋は 216 225 対のうち 51 143 対で落ちる。落ちた対にはかならず標準でない端がある。
最小の証人は `(0,0)(1,0)` と `(0,0)(0,0)(1,1)` で、後者を `stdB` は退ける。 -/

#guard (nf1_74 6).length == 465
#guard ((nf1_74 6).filter fun t => !(stdB t)).length == 305
#guard ((nf1_74 6).filter stdB).length == 160
#guard pairFail74 (nf1_74 6) == 51143
#guard ((nf1_74 6).flatMap fun u => (nf1_74 6).filter fun t =>
  !(BT.lt (bValA71 u) (bValA71 t) == lt (vOf u) (vOf t)) && stdB u && stdB t).length == 0
#guard (decodeB [[0,0],[1,0]]).map stdB == some true
#guard (decodeB [[0,0],[0,0],[1,1]]).map stdB == some false

/-! **部分領域の外 — より一般の形は測定としては通る。** 段 2・段 3 まで許した標準な添字で
反例 0。§69 の `VOfLtStd` の形である。**定理ではない。** -/

#guard (popS 3 6).length == 235
#guard pairFail74 (popS 3 6) == 0
#guard (popS 4 6).length == 250
#guard pairFail74 (popS 4 6) == 0

end

/-! ### §74.9 公理 -/

/-! ## §76 THE BOOKKEEPING HALF OF THE ORDER BRIDGE IS A THEOREM

§74 split row 326's remaining order hypothesis `VOfLtA71` into two named pieces,

    VOfIsDict74 : ∀ t, stdB1 t = true → vOf t = dict (bValA71 t)
    DictLtA74   : `dict` preserves `BT.lt` on the sub-region's values

and proved `vOfLtA71_of_dict74 : VOfIsDict74 → DictLtA74 → VOfLtA71`.  **§76 proves the first
one.**  It is not proved outright — nothing about `dict` can be, until `inT (dict ·)` is —
but it is proved from `PsiIdxOKStd172` ALONE, and that is a hypothesis row 326's certificate
already carries (§72).  So the split of §74 collapses: `DictLtA74` and `VOfLtA71` become the
SAME hypothesis (`dictLtA74_iff76`), and the bridge is now exactly one statement about `dict`
and nothing about bookkeeping.

WHAT IS PROVED.

  §76.1  **NOTHING IN THE IMAGE OF `ω^·` IS `0`, AND NOTHING IS `1` UNLESS ITS ARGUMENT IS.**
         `omegaNF_ne_zero76` and `omegaNF_ne_one76` (`x ≠ 0 → ω^x ≠ 1`), by §65.3's
         `omegaNF_eq_gen` and a case analysis of `dnArg` that needs no side condition:
         `dnArg_cases76` says `dnArg x` is either `x` itself or `plus g (ofNat k)` with
         `g ≠ 0`, and `plus_ne_zero76` closes the second.  `phiNF_ne_zero76` is the same
         statement for `φ`, needed one level down.

  §76.2  **`ψ_u(α) ≠ 1` UNLESS `u = 0` AND `α = 0`.**  `collapse_ne_one76`.  This is the fact
         the identity actually needs: for 2390 of `subP 8`'s 2397 indices the leading
         component is NOT `ψ₀0`, and there `1 + ψ₀(α) = ψ₀(α)` says exactly that `ψ₀(α) ≥ ω`.
         The proof unfolds `collapse` through `collapse_eq`, keeps `wcnf`'s output alive with
         §65.6's `wcnf_spec_sc` and `fold_inv`, and then only has to see that the fold's
         second component is `some` of a `ψ` or a `φ` — never `0` (`fold_snd_ne_zero76`) —
         and that `wcnf` of a nonempty list returns either a nonempty pair list or the list
         itself (`wcnf_cons_ne76`).  `PsiIdxOK u x` is a hypothesis; at the call site it is
         exactly what `PsiIdxOKStd172` hands over.

  §76.3  **`1 + α = α` FOR ADDITIVELY PRINCIPAL `α ≠ 1`.**  `plus_one_eq76`, from
         §65.1's `le_one_ap` and `Evidence/WF.lean`'s `lt_asymm_inT`.

  §76.4  **THE IDENTITY.**  `vOfIsDict76 (Hp : PsiIdxOKStd172) : VOfIsDict74`.  §74.3's
         `bVal_eq_strip74` says the two values differ by at most a leading `ψ₀0`, so the
         proof splits on that leading component.  When it IS `ψ₀0` the identity is
         `dict`'s distribution over `⊕` (§63.3) and `dict (ψ₀0) = 1`.  When it is NOT, the
         identity is `1 + α = α` at the head, which is §76.2 plus associativity
         (`plus_assoc_inT`) — and the `α ≠ 0` side condition of §76.2 is discharged by
         `dict_ne_zero76`, which is where `BT.isStd` is spent (its `isP` conjunct; see the
         negative result below).

  §76.4b **THE TWO BOTTOM CASES OF `DictLtA74`.**  `dictLt_zero76` and `dictLt_D0_zero76`.
         Neither needs the `BT.lt` hypothesis: they are unconditional strict inequalities.

  §76.5  **THE COLLAPSE OF THE SPLIT.**  `dictLtA74_iff76 : DictLtA74 ↔ VOfLtA71`, and
         `limDecS1_76` / `limIncS1_76` — row 326's decreasing and increasing clauses are
         theorems given `PsiIdxOKStd172` and `DictLtA74` alone.

  §76.5b **AND THE CERTIFICATE IS DOWN TO FOUR NAMED HYPOTHESES.**  §71.4's and §74.5's
         cofinality tools carried `PsiIdxOKStd` and `RegionStd`, the UNRESTRICTED pair, only
         because they predate §72's `inT_vOf_72`; the same proofs go through with
         `PsiIdxOKStd172` alone (`vOfLtA71'_76`, `cofInS1_172_76`, `limCofS1_172_76`).  So

             certIn_t326_dict76 :  PsiIdxOKStd172, DictLtA74, CofDenseS1, BCofIn71  ⊢ row 326
             certIn_t326_step76 :  PsiIdxStep073,  DictLtA74, CofDenseS1, BCofIn71  ⊢ row 326

         (plus the accessibility of `vOf t326`, as always).  §74.7's best was five, two of
         them the unrestricted gates.

WHAT IS **NOT** CLAIMED.  `DictLtA74` is NOT proved.  §76.4b closes the two BOTTOM cases of
its induction and nothing else — `dictLt_zero76` (`dict 0 = 0` is below every standard nonzero
image) and `dictLt_D0_zero76` (`dict (ψ₀0) = 1` is below every other `ψ_u(α)` image) — and both
are §76.2 restated, with no order content in them.  The general head comparison, `ψ_u(α)`
against `ψ_v(β)` lexicographically in `(u, α)`, is untouched, and so is the sum-level
induction that would need it.  `PsiIdxOKStd172`, `CofDenseS1` and
`BCofIn71` are still named and unproved, and §70.5's `LimCofS1` is still open on the
`CofDenseS1` side.  `vOfIsDict76` needs `PsiIdxOKStd172` and cannot be made unconditional:
`collapse_ne_one76` needs `inT (dict a)`, and `inT (dict ·)` is that gate.

WHAT THE MEASUREMENT SAYS (§76.6 gives every construction).  **The negative results first.**
The identity `vOf t = dict (bValA71 t)` is FALSE outside the sub-region — it fails on indices
of the deep corpus that carry a level-2 or level-3 node, so the `lvlLe 1` half of `stdB1` is
not decoration.  `dict_ne_zero76` is FALSE without `BT.isStd`: `dict (0 ⊕ 0) = 0` with
`0 ⊕ 0 ≠ 0`.  `collapse_ne_one76` is FALSE without its side condition: `ψ₀0 = 1` exactly.
`plus_one_eq76` is FALSE without `α ≠ 1`: `1 + 1 = 2`.
-/

/-! ### §76.1 `ω^·` の像は 0 でなく、引数が 0 でなければ 1 でもない -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- 加法主要なら 0 でない。 -/
theorem ne_zero_of_isAP76 {a : Term} (h : a.isAP = true) : a ≠ zero := by
  intro hc; rw [hc] at h; exact Bool.noConfusion h

/-- 強臨界なら 0 でない。 -/
theorem ne_zero_of_isSC76 {a : Term} (h : a.isSC = true) : a ≠ zero := by
  intro hc; rw [hc] at h; exact Bool.noConfusion h

/-- 0 でない項の成分列は空でない。 -/
theorem toList_ne_nil76 {t : Term} (h : t ≠ zero) : t.toList ≠ [] := by
  cases t with
  | zero => exact absurd rfl h
  | M => exact List.cons_ne_nil _ _
  | add a b => exact List.cons_ne_nil _ _
  | omg a => exact List.cons_ne_nil _ _
  | phi a b => exact List.cons_ne_nil _ _
  | psi k a => exact List.cons_ne_nil _ _
  | Z a => exact List.cons_ne_nil _ _

/-- 0 でない成分を 1 つでも含む列から組んだ項は 0 でない。 -/
theorem ofList_append_ne_zero76 : ∀ (f : List Term) (a : Term) (r : List Term),
    a ≠ zero → ofList (f ++ a :: r) ≠ zero
  | [], a, r, ha => by
      cases r with
      | nil => exact ha
      | cons b t => exact fun hc => Term.noConfusion hc
  | x :: f', a, r, ha => by
      have hne : f' ++ a :: r ≠ [] := by
        cases f' with
        | nil => exact List.cons_ne_nil a r
        | cons z zs => exact List.cons_ne_nil z (zs ++ a :: r)
      cases h : f' ++ a :: r with
      | nil => exact absurd h hne
      | cons y t =>
        show ofList (x :: (f' ++ a :: r)) ≠ zero
        rw [h]
        exact fun hc => Term.noConfusion hc

/-- **和は 0 でない。** 右の項が 𝔗(M) の項なら、左が 0 でないだけで足りる。 -/
theorem plus_ne_zero76 {s t : Term} (ht : t.inT = true) (hs : s ≠ zero) :
    plus s t ≠ zero := by
  cases htl : t.toList with
  | nil =>
      show (match t.toList with
            | [] => s
            | b1 :: _ => ofList ((toList s).filter (fun a => le b1 a) ++ toList t)) ≠ zero
      rw [htl]
      exact hs
  | cons b1 r =>
      have hb1 : b1 ≠ zero := by
        have h1 := (inT_toList t ht).1
        rw [htl] at h1
        exact ne_zero_of_isAP76 (inTL_cons.mp h1).1.1
      show (match t.toList with
            | [] => s
            | b1 :: _ => ofList ((toList s).filter (fun a => le b1 a) ++ toList t)) ≠ zero
      rw [htl]
      exact ofList_append_ne_zero76 _ b1 r hb1

/-- **`dnArg` の 2 つの形。** そのままか、`0` でない `g` に有限個を足したもの。
    側条件は無い — `CNVOps` §26 の枝分けをそのまま読んだだけ。 -/
theorem dnArg_cases76 (v : Term) :
    dnArg v = v ∨ ∃ (g : Term) (k : Nat), g ≠ zero ∧ dnArg v = plus g (ofNat k) := by
  unfold dnArg
  cases hs : splitFin v with
  | mk g m =>
    dsimp only
    split
    · cases g with
      | phi a b =>
        dsimp only
        split
        · exact Or.inr ⟨phi a b, m - 1, fun h => Term.noConfusion h, rfl⟩
        · exact Or.inl rfl
      | zero =>
        dsimp only
        split
        · rename_i hcond; exact Bool.noConfusion hcond
        · exact Or.inl rfl
      | M =>
        dsimp only
        split
        · exact Or.inr ⟨M, m - 1, fun h => Term.noConfusion h, rfl⟩
        · exact Or.inl rfl
      | add a b =>
        dsimp only
        split
        · rename_i hcond; exact Bool.noConfusion hcond
        · exact Or.inl rfl
      | omg a =>
        dsimp only
        split
        · rename_i hcond; exact Bool.noConfusion hcond
        · exact Or.inl rfl
      | psi k a =>
        dsimp only
        split
        · exact Or.inr ⟨psi k a, m - 1, fun h => Term.noConfusion h, rfl⟩
        · exact Or.inl rfl
      | Z a =>
        dsimp only
        split
        · exact Or.inr ⟨Z a, m - 1, fun h => Term.noConfusion h, rfl⟩
        · exact Or.inl rfl
    · exact Or.inl rfl

theorem dnArg_ne_zero76 {v : Term} (h : v ≠ zero) : dnArg v ≠ zero := by
  rcases dnArg_cases76 v with h1 | ⟨g, k, hg, h1⟩
  · rw [h1]; exact h
  · rw [h1]; exact plus_ne_zero76 (inT_ofNat k) hg

/-- **`ω^x` は決して 0 でない。** -/
theorem omegaNF_ne_zero76 (x : Term) : omegaNF x ≠ zero := by
  rw [omegaNF_eq_gen x]
  split
  · exact fun hc => Term.noConfusion hc
  · split
    · rename_i hfp
      intro hc
      rw [hc] at hfp
      exact Bool.noConfusion hfp
    · exact fun hc => Term.noConfusion hc

/-- **`x ≠ 0` なら `ω^x ≠ 1`。** つまり `ω^x ≥ ω`。 -/
theorem omegaNF_ne_one76 (x : Term) (h : x ≠ zero) : omegaNF x ≠ one := by
  rw [omegaNF_eq_gen x]
  split
  · exact fun hc => Term.noConfusion hc
  · split
    · rename_i hfp
      intro hc
      rw [hc] at hfp
      exact Bool.noConfusion hfp
    · intro hc
      exact absurd (show dnArg x = zero by injection hc) (dnArg_ne_zero76 h)

/-- `φ` の既定枝は 0 でない。 -/
theorem phiNFdefault_ne_zero76 (a b : Term) : phiNFdefault a b ≠ zero := by
  unfold phiNFdefault
  split
  · rename_i h
    exact ne_zero_of_isSC76 ((Bool.and_eq_true _ _).mp h).2
  · exact fun hc => Term.noConfusion hc

/-- `φ` の数え直しの枝も 0 でない。 -/
theorem phiNFsucc_ne_zero76 (a b : Term) : phiNFsucc a b ≠ zero := by
  unfold phiNFsucc
  cases hs : splitFin b with
  | mk g m =>
    dsimp only
    split
    · cases g with
      | phi c d =>
        dsimp only
        split
        · exact fun hc => Term.noConfusion hc
        · exact phiNFdefault_ne_zero76 a b
      | zero => dsimp only; split
                · exact fun hc => Term.noConfusion hc
                · exact phiNFdefault_ne_zero76 a b
      | M => dsimp only; split
             · exact fun hc => Term.noConfusion hc
             · exact phiNFdefault_ne_zero76 a b
      | add p q => dsimp only; split
                   · exact fun hc => Term.noConfusion hc
                   · exact phiNFdefault_ne_zero76 a b
      | omg p => dsimp only; split
                 · exact fun hc => Term.noConfusion hc
                 · exact phiNFdefault_ne_zero76 a b
      | psi k p => dsimp only; split
                   · exact fun hc => Term.noConfusion hc
                   · exact phiNFdefault_ne_zero76 a b
      | Z p => dsimp only; split
               · exact fun hc => Term.noConfusion hc
               · exact phiNFdefault_ne_zero76 a b
    · exact phiNFdefault_ne_zero76 a b

/-- **`φαβ` は決して 0 でない。** -/
theorem phiNF_ne_zero76 (a b : Term) : phiNF a b ≠ zero := by
  unfold phiNF
  split
  · rename_i h
    exact ne_zero_of_isSC76 ((Bool.and_eq_true _ _).mp h).1
  · cases b with
    | phi c d =>
      dsimp only
      split
      · exact fun hc => Term.noConfusion hc
      · exact phiNFsucc_ne_zero76 a (phi c d)
    | zero => exact phiNFsucc_ne_zero76 a zero
    | M => exact phiNFsucc_ne_zero76 a M
    | add p q => exact phiNFsucc_ne_zero76 a (add p q)
    | omg p => exact phiNFsucc_ne_zero76 a (omg p)
    | psi k p => exact phiNFsucc_ne_zero76 a (psi k p)
    | Z p => exact phiNFsucc_ne_zero76 a (Z p)

end

/-! ### §76.2 `collapse` は 0 でなく、`(u, x) = (0, 0)` でなければ 1 でもない -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- 畳み込みの 1 歩は第 2 成分に必ず 0 でない項を置く。`ψ` か `φ` のどちらか。 -/
theorem stepF_snd_ne_zero76 (w base : Term) (s : Option Term × Option Term)
    (ac : Term × Term) : ∃ v, (stepF w base s ac).2 = some v ∧ v ≠ zero := by
  unfold stepF
  split
  · exact ⟨psi w (idxOf w s ac), rfl, fun hc => Term.noConfusion hc⟩
  · refine ⟨_, rfl, ?_⟩
    exact phiNF_ne_zero76 _ _

/-- **畳み込みが 1 歩でも進めば第 2 成分は 0 でない `some`。** -/
theorem fold_snd_ne_zero76 (w base : Term) :
    ∀ (l : List (Term × Term)) (s : Option Term × Option Term), l ≠ [] →
      ∃ v, (l.foldl (stepF w base) s).2 = some v ∧ v ≠ zero
  | [], _, h => absurd rfl h
  | [ac], s, _ => stepF_snd_ne_zero76 w base s ac
  | ac :: b :: t, s, _ =>
      fold_snd_ne_zero76 w base (b :: t) (stepF w base s ac) (List.cons_ne_nil _ _)

/-- **空でない列の `wcnf`。** 対の列が空でないか、さもなくば余りが列そのもの。 -/
theorem wcnf_cons_ne76 (w p : Term) (rest : List Term) :
    (wcnf w (p :: rest)).1 ≠ [] ∨ (wcnf w (p :: rest)).2 = ofList (p :: rest) := by
  cases h : lt p w with
  | true => exact Or.inr (by rw [wcnf_cons_lt h])
  | false =>
    left
    cases hr : wcnf w rest with
    | mk fst snd =>
      rw [wcnf_cons_ge h, hr]
      cases fst with
      | nil => exact List.cons_ne_nil _ _
      | cons ac0 ps =>
        cases ac0 with
        | mk a' c' =>
          dsimp only
          split
          · exact List.cons_ne_nil _ _
          · exact List.cons_ne_nil _ _

/-- **`ψ_u(α) ≠ 0`。** 仮説は何も要らない。 -/
theorem collapse_ne_zero76 (u : Nat) (x : Term) : collapse u x ≠ zero := by
  rw [collapse_eq]
  exact omegaNF_ne_zero76 _

/-- **§76.2 の主定理。** `ψ_u(α) = 1` になるのは `u = 0` かつ `α = 0` のときだけ。
    `PsiIdxOK` は §65.6 の `fold_inv` を通すために要る — 呼び出し側では
    `PsiIdxOKStd172` がそのまま供給する。 -/
theorem collapse_ne_one76 (u : Nat) (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (Hpx : PsiIdxOK u x) (h : ¬(u = 0 ∧ x = zero)) : collapse u x ≠ one := by
  rw [collapse_eq]
  refine omegaNF_ne_one76 _ ?_
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨⟨h21, _⟩, hallOK⟩ :=
    wcnf_spec_sc (inT_reg (u + 1)) (isSC_reg_succ u) (toList x) hc hd (ltM_toList x hx hlx)
  have hinit : StInv ((none : Option Term), (none : Option Term)) := by
    constructor
    · intro i0 hq; cases hq
    · intro v hq; cases hq
  have hst := fold_inv mulDescInT (inT_reg (u + 1)) (ltM_reg (u + 1)) (inT_baseOf u)
    (ltM_baseOf u) (wcnf (reg (u + 1)) (toList x)).1 (none, none) hinit hallOK Hpx
  have hv : inT (((wcnf (reg (u + 1)) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg (u + 1)) (baseOf u))).2.getD zero) = true := by
    cases hg : ((wcnf (reg (u + 1)) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg (u + 1)) (baseOf u))).2 with
    | none => exact inT_zero
    | some v => exact (hst.2 v hg).1
  cases u with
  | succ k =>
    exact plus_ne_zero76 (inT_plus hv h21)
      (show reg (k + 1) ≠ zero from fun hcc => Term.noConfusion hcc)
  | zero =>
    have hxz : x ≠ zero := fun hcc => h ⟨rfl, hcc⟩
    rw [show reg 0 = zero from rfl, plus_zero_left_inT (inT_plus hv h21)]
    cases hl : (wcnf (reg (0 + 1)) (toList x)).1 with
    | cons a0 t0 =>
      obtain ⟨v, hvq, hvz⟩ := fold_snd_ne_zero76 (reg (0 + 1)) (baseOf 0) (a0 :: t0) (none, none)
        (List.cons_ne_nil _ _)
      rw [hvq]
      exact plus_ne_zero76 h21 hvz
    | nil =>
      show plus zero (wcnf (reg (0 + 1)) (toList x)).2 ≠ zero
      rw [plus_zero_left_inT h21]
      cases htl : (toList x) with
      | nil => exact absurd htl (toList_ne_nil76 hxz)
      | cons p rest =>
        rcases wcnf_cons_ne76 (reg (0 + 1)) p rest with hne | heq
        · exact absurd (by rw [← htl]; exact hl) hne
        · rw [heq, ← htl, inT_ofList_toList x hx]
          exact hxz

end

/-! ### §76.3 `1 + α = α` — `α` が加法主要で 1 でないとき -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- 加法主要な項の成分列はそれ自身 1 つ。 -/
theorem toList_ap76 {A : Term} (hap : A.isAP = true) : toList A = [A] := by
  cases A with
  | zero => exact Bool.noConfusion hap
  | add a b => exact Bool.noConfusion hap
  | M => rfl
  | omg a => rfl
  | phi a b => rfl
  | psi k a => rfl
  | Z a => rfl

/-- 加法主要で 1 でなければ `α ≤ 1` は偽。 -/
theorem le_one_eq_false76 {A : Term} (hap : A.isAP = true) (hiA : inT A = true)
    (hne : A ≠ one) : le A one = false := by
  have hb : (one == A) = false := by
    cases hbb : (one == A) with
    | true => exact absurd (eq_of_beq hbb).symm hne
    | false => rfl
  have h2 : lt one A = true := by
    have h1 : (one == A || lt one A) = true := Evidence.Cert.le_one_ap hap
    rw [hb, Bool.false_or] at h1
    exact h1
  have h3 : lt A one = false := lt_asymm_inT inT_one hiA h2
  have hb2 : (A == one) = false := by
    cases hbb : (A == one) with
    | true => exact absurd (eq_of_beq hbb) hne
    | false => rfl
  show (A == one || lt A one) = false
  rw [hb2, h3]
  rfl

/-- 0 でない項は 0 より真に大きい。2.3.1 そのもの。 -/
theorem lt_zero_ne76 {y : Term} (h : y ≠ zero) : lt zero y = true := by
  have hb : (zero == y) = false := by
    cases hbb : (zero == y) with
    | true => exact absurd (eq_of_beq hbb).symm h
    | false => rfl
  rw [lt_eq_ltF_succ]
  cases y with
  | zero => exact absurd rfl h
  | M => rfl
  | add a b => rfl
  | omg a => rfl
  | phi a b => rfl
  | psi k a => rfl
  | Z a => rfl

/-- 加法主要で 1 でなければ 1 より真に大きい。 -/
theorem lt_one_ap76 {A : Term} (hap : A.isAP = true) (hne : A ≠ one) : lt one A = true := by
  have hb : (one == A) = false := by
    cases hbb : (one == A) with
    | true => exact absurd (eq_of_beq hbb).symm hne
    | false => rfl
  have h1 : (one == A || lt one A) = true := Evidence.Cert.le_one_ap hap
  rw [hb, Bool.false_or] at h1
  exact h1

/-- **§76.3 の主定理。** `1 + α = α`。 -/
theorem plus_one_eq76 {A : Term} (hap : A.isAP = true) (hiA : inT A = true)
    (hne : A ≠ one) : plus one A = A := by
  have hle : le A one = false := le_one_eq_false76 hap hiA hne
  have hfil : List.filter (fun a => le A a) [one] = [] := by
    show (match le A one with
          | true => one :: List.filter (fun a => le A a) []
          | false => List.filter (fun a => le A a) []) = []
    rw [hle]
    rfl
  show (match toList A with
        | [] => one
        | b1 :: _ => ofList ((toList one).filter (fun a => le b1 a) ++ toList A)) = A
  rw [toList_ap76 hap]
  show ofList (List.filter (fun a => le A a) (toList one) ++ [A]) = A
  rw [show toList one = [one] from rfl, hfil]
  rfl

end

/-! ### §76.4 `VOfIsDict74` — 添字の値は `dict` の像そのもの -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- **部分領域の標準な `BT` 項の像は 0 でない。** `BT.isStd` の `isP` の連言を使う —
    これを落とすと偽 (`0 ⊕ 0`、§76.6)。 -/
theorem dict_ne_zero76 (Hp : PsiIdxOKStd172) : ∀ (x : BT), btLe72 1 x = true →
    BT.isStd x = true → x ≠ BT.zero → dict x ≠ zero
  | .zero, _, _, h => absurd rfl h
  | .D u a, _, _, _ => by
      rw [Trans.Dict.dict_D]
      exact collapse_ne_zero76 u (dict a)
  | .sum a b, hb, hs, _ => by
      obtain ⟨hba, hbb⟩ := btLe72_sum 1 a b hb
      obtain ⟨h1, _⟩ := (Bool.and_eq_true _ _).mp hs
      obtain ⟨h12, h3⟩ := (Bool.and_eq_true _ _).mp h1
      obtain ⟨hP, _⟩ := (Bool.and_eq_true _ _).mp h12
      rw [Trans.Dict.dict_sum]
      refine plus_ne_zero76 (inT_dict_of_std172 Hp b hbb h3).1 ?_
      cases a with
      | zero => exact Bool.noConfusion hP
      | sum p q => exact Bool.noConfusion hP
      | D u p => rw [Trans.Dict.dict_D]; exact collapse_ne_zero76 u (dict p)

/-- `ψ_u` の像は加法主要。`collapse` の出口は `omegaNF` だから。 -/
theorem isAP_dict_D76 (u : Nat) (a : BT) : (dict (BT.D u a)).isAP = true := by
  rw [Trans.Dict.dict_D, collapse_eq]
  exact isAP_omegaNF _

/-- **`ψ_u(α)` の像は 1 でない** — 部分領域の仮説の上で。§76.2 の `BT` 側の形。 -/
theorem dict_D_ne_one76 (Hp : PsiIdxOKStd172) (u : Nat) (b : BT)
    (hb : btLe72 1 (BT.D u b) = true) (hs : BT.isStd (BT.D u b) = true)
    (hne : BT.D u b ≠ BT.D 0 BT.zero) : dict (BT.D u b) ≠ one := by
  obtain ⟨hu1, hbtb⟩ := btLe72_D 1 u b hb
  have hib := inT_dict_of_std172 Hp b hbtb (isStd_of_D hs)
  rw [Trans.Dict.dict_D]
  refine collapse_ne_one76 u (dict b) hib.1 hib.2 (Hp u b hu1 hbtb hs) ?_
  rintro ⟨hu0, hz⟩
  subst hu0
  exact dict_ne_zero76 Hp b hbtb (isStd_of_D hs) (fun hcc => hne (by rw [hcc])) hz

/-- **§76 の主定理。** §74.6 の `VOfIsDict74` — 添字の値は `dict` の像そのもの。
    仮説は `PsiIdxOKStd172` ただ一つで、それは §72 が 326 行目の証明書に残した
    4 つのうちの 1 つである。 -/
theorem vOfIsDict76 (Hp : PsiIdxOKStd172) : VOfIsDict74 := by
  intro t ht
  cases t with
  | nil => rfl
  | nd w r c =>
    have hl : lvlLe 1 (B.nd w r c) = true := lvlLe1_of_stdB1 _ ht
    have hLne : (bValA71 (B.nd w r c)).toL ≠ [] :=
      toL_bValA71_ne_nil74 _ (fun hcc => B.noConfusion hcc)
    have hstrip : (bVal (B.nd w r c)).toL = stripL74 (bValA71 (B.nd w r c)).toL := by
      rw [bVal_eq_strip74 _ hl]
      exact toL_ofL _ (atoms_stripL74 _ (atoms_toL74 _))
    have hdA : ∀ a ∈ (bVal (B.nd w r c)).toL, inT (dict a) = true :=
      dictAtoms_bVal_72 Hp _ ht
    cases hLc : (bValA71 (B.nd w r c)).toL with
    | nil => exact absurd hLc hLne
    | cons h1 rest =>
      rw [hLc] at hstrip
      by_cases hh : h1 = BT.D 0 BT.zero
      · -- 先頭が `ψ₀0` — `bVal` はそれを落とす。`dict` の分配で終わり。
        subst hh
        rw [stripL74_cons_eq74] at hstrip
        have hdr : ∀ x ∈ rest, inT (dict x) = true := by
          intro x hx; exact hdA x (by rw [hstrip]; exact hx)
        show plus one (dict (bVal (B.nd w r c))) = dict (bValA71 (B.nd w r c))
        have e1 : bValA71 (B.nd w r c) = BT.ofL ([BT.D 0 BT.zero] ++ rest) := by
          rw [show ([BT.D 0 BT.zero] ++ rest) = BT.D 0 BT.zero :: rest from rfl, ← hLc]
          exact (nfSum_bValA7174 _).symm
        have e2 : bVal (B.nd w r c) = BT.ofL rest := by
          rw [← hstrip]; exact (nfSum_bVal _).symm
        rw [e1, dict_ofL_append [BT.D 0 BT.zero] rest
          (by intro x hx
              rw [List.mem_singleton.mp hx, dict_D0_zero]
              exact inT_one) hdr,
          show BT.ofL [BT.D 0 BT.zero] = BT.D 0 BT.zero from rfl, dict_D0_zero, ← e2]
      · -- 先頭が `ψ₀0` でない — `1 + ψ_u(α) = ψ_u(α)` そのもの。
        rw [stripL74_cons_ne74 h1 rest hh] at hstrip
        have hdr : ∀ x ∈ rest, inT (dict x) = true := by
          intro x hx; exact hdA x (by rw [hstrip]; exact List.Mem.tail _ hx)
        have hh1mem : h1 ∈ (bVal (B.nd w r c)).toL := by rw [hstrip]; exact List.Mem.head _
        have hbv : bVal (B.nd w r c) = bValA71 (B.nd w r c) := by
          rw [← nfSum_bVal (B.nd w r c), ← nfSum_bValA7174 (B.nd w r c), hstrip, hLc]
        obtain ⟨u, b, hub⟩ :=
          atoms_toL74 (bValA71 (B.nd w r c)) h1 (by rw [hLc]; exact List.Mem.head _)
        have hiA : inT (dict h1) = true := hdA h1 hh1mem
        have hbt : btLe72 1 h1 = true := btLe_bVal_mem72 _ hl h1 hh1mem
        have hst1 : BT.isStd h1 = true := regionStd1_72 _ ht h1 hh1mem
        subst hub
        have hAne : dict (BT.D u b) ≠ one := dict_D_ne_one76 Hp u b hbt hst1 hh
        have e1 : bValA71 (B.nd w r c) = BT.ofL ([BT.D u b] ++ rest) := by
          rw [show ([BT.D u b] ++ rest) = BT.D u b :: rest from rfl, ← hLc]
          exact (nfSum_bValA7174 _).symm
        show plus one (dict (bVal (B.nd w r c))) = dict (bValA71 (B.nd w r c))
        rw [hbv, e1, dict_ofL_append [BT.D u b] rest
          (by intro x hx; rw [List.mem_singleton.mp hx]; exact hiA) hdr,
          show BT.ofL [BT.D u b] = BT.D u b from rfl,
          ← plus_assoc_inT one (dict (BT.D u b)) (dict (BT.ofL rest)) inT_one hiA
            (inT_dict_ofL rest hdr),
          plus_one_eq76 (isAP_dict_D76 u b) hiA hAne]

/-- §66.4 の絞らない形からも同じ。 -/
theorem vOfIsDict76' (Hp : PsiIdxOKStd) : VOfIsDict74 :=
  vOfIsDict76 (psiIdxOKStd172_of_std Hp)

end

/-! ### §76.4b `DictLtA74` の底の二段 — 0 と `ψ₀0` の行き先

**`DictLtA74` そのものは証明しない。**  ここで閉じるのは、その帰納法の底になる 2 つの
場合だけである: 小さい側が `0` のときと `ψ₀0` (= Buchholz の 1) のとき。どちらも §76.2 の
「`ψ_u(α)` は 0 でも 1 でもない」の言い換えで、順序の中身は入っていない。頭の比較の
一般の場合 — `ψ_u(α)` と `ψ_v(β)` を `(u, α)` の辞書式で比べる — は手つかずである。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- **底、その 1。** `dict 0 = 0` は標準な非零項の像より真に小さい。 -/
theorem dictLt_zero76 (Hp : PsiIdxOKStd172) (x : BT) (hb : btLe72 1 x = true)
    (hs : BT.isStd x = true) (hx : x ≠ BT.zero) :
    lt (dict BT.zero) (dict x) = true :=
  lt_zero_ne76 (dict_ne_zero76 Hp x hb hs hx)

/-- **底、その 2。** `dict (ψ₀0) = 1` は他のどの `ψ_u(α)` の像より真に小さい。
    Buchholz 側でも `BT.lt (ψ₀0) (ψ_u(α)) = true` なので、これは `DictLtA74` を
    「小さい側の先頭成分が `ψ₀0`」に絞った形そのものである。仮説に `BT.lt` は要らない。 -/
theorem dictLt_D0_zero76 (Hp : PsiIdxOKStd172) (u : Nat) (b : BT)
    (hb : btLe72 1 (BT.D u b) = true) (hs : BT.isStd (BT.D u b) = true)
    (hne : BT.D u b ≠ BT.D 0 BT.zero) :
    lt (dict (BT.D 0 BT.zero)) (dict (BT.D u b)) = true := by
  rw [dict_D0_zero]
  exact lt_one_ap76 (isAP_dict_D76 u b) (dict_D_ne_one76 Hp u b hb hs hne)

end

/-! ### §76.5 帰結 — 二つに割れていた橋がひとつに戻る -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

/-- **§74.6 の分解は片方が定理になったので、残りは一つ。** -/
theorem vOfLtA71_of_dictLt76 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) : VOfLtA71 :=
  vOfLtA71_of_dict74 (vOfIsDict76 Hp) H2

/-- 逆向き。`vOf` が `dict` の像なので、橋は `dict` の順序保存そのもの。 -/
theorem dictLt_of_vOfLtA7176 (Hp : PsiIdxOKStd172) (HV : VOfLtA71) : DictLtA74 := by
  intro u t hu ht h
  rw [← vOfIsDict76 Hp u hu, ← vOfIsDict76 Hp t ht]
  exact HV u t hu ht h

/-- **§76.5 の主定理。** `DictLtA74` と `VOfLtA71` は同じ仮説である。
    §74 が二つに割ったうちの一方が定理になったので、割れ目が消えた。 -/
theorem dictLtA74_iff76 (Hp : PsiIdxOKStd172) : DictLtA74 ↔ VOfLtA71 :=
  ⟨vOfLtA71_of_dictLt76 Hp, dictLt_of_vOfLtA7176 Hp⟩

/-- **減少。** 仮説は `PsiIdxOKStd172` と `DictLtA74` の 2 つだけ。 -/
theorem limDecS1_76 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) : LimDecS1 :=
  limDecS1_of_bridge71 (vOfLtA71_of_dictLt76 Hp H2)

/-- **増加。** 同じ 2 つ。 -/
theorem limIncS1_76 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) : LimIncS1 :=
  limIncS1_of_bridge71 (vOfLtA71_of_dictLt76 Hp H2)

/-- **共終性の内側の半分。** §74.5 で逆向きが要らなくなっているので、
    `DictLtA74` から `CofInS1` が出る。 -/
theorem cofInS1_76 (Hp : PsiIdxOKStd) (Hr : RegionStd) (H2 : DictLtA74)
    (HBC : BCofIn71) : CofInS1 :=
  cofInS1_of71 Hp Hr
    (vOfLtA71'_of74 Hp Hr (vOfLtA71_of_dictLt76 (psiIdxOKStd172_of_std Hp) H2)) HBC

/-- **§76 の最終形。** §74.7 の 5 つの仮説のうち、橋 `VOfLtA71` が `DictLtA74` に
    置き換わる。数は変わらないが、残った 1 つは `dict` の順序保存だけになった —
    帳簿の分 (`VOfIsDict74`) はもう仮説ではない。 -/
theorem certIn_t326_76 (Hp : PsiIdxOKStd) (Hr : RegionStd) (H2 : DictLtA74)
    (HCD : CofDenseS1) (HBC : BCofIn71)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_74' Hp Hr (vOfLtA71_of_dictLt76 (psiIdxOKStd172_of_std Hp) H2) HCD HBC hacc

end

/-! ### §76.5b 部分領域の仮説だけで閉じる — 326 行目に残るのは 4 つ

§71.4 / §74.5 の共終性の道具は `PsiIdxOKStd` と `RegionStd` (絞らない形の 2 つ) を
取っていた。§72 の `inT_vOf_72` があるので、同じ証明がそのまま `PsiIdxOKStd172` だけで
通る。これで 326 行目の証明書は部分領域の仮説だけで書ける。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

/-- §74.5 の `vOfLtA71'_of74` を部分領域の仮説だけで。 -/
theorem vOfLtA71'_76 (Hp : PsiIdxOKStd172) (HV : VOfLtA71) : VOfLtA71' := by
  intro u t hu ht hlt
  rcases lt_tricho_bValA7174 u t (lvlLe1_of_stdB1 u hu) (lvlLe1_of_stdB1 t ht) with h | h | h
  · exact h
  · exact absurd hlt (by
      rw [vOf_eq_of_bValA7174 u t (lvlLe1_of_stdB1 u hu) (lvlLe1_of_stdB1 t ht) h,
        Evidence.WF.lt_irrefl]
      exact fun hc => Bool.noConfusion hc)
  · exact absurd hlt (by
      rw [lt_asymm_inT (inT_vOf_72 Hp t ht) (inT_vOf_72 Hp u hu) (HV t u ht hu h)]
      exact fun hc => Bool.noConfusion hc)

/-- §71.4 の `cofInS1_of71` を部分領域の仮説だけで。 -/
theorem cofInS1_172_76 (Hp : PsiIdxOKStd172) (HV : VOfLtA71') (HB : BCofIn71) : CofInS1 := by
  intro t ht hk u hu hlt
  obtain ⟨n, hn⟩ := HB t ht hk u hu (HV u t hu ht hlt)
  refine ⟨n, ?_⟩
  have hfs := stdB1_fsB t ht n
  have hiu : inT (vOf u) = true := inT_vOf_72 Hp u hu
  have hif : inT (vOf (fsB t n)) = true := inT_vOf_72 Hp _ hfs
  rcases lt_comparable_inT hiu hif with h | h | h
  · show (vOf u == vOf (fsB t n) || lt (vOf u) (vOf (fsB t n))) = true
    rw [h]; exact Bool.or_true _
  · rw [h]; exact le_self _
  · rw [HV (fsB t n) u hfs hu h] at hn
    exact absurd hn (by intro hc; exact Bool.noConfusion hc)

/-- §71.4 の `limCofS1_of71` を部分領域の仮説だけで。 -/
theorem limCofS1_172_76 (Hp : PsiIdxOKStd172) (HD : CofDenseS1) (HI : CofInS1) :
    LimCofS1 := by
  intro t ht hk s hs hlt
  obtain ⟨u, hu, hle, hult⟩ := HD t ht hk s hs hlt
  obtain ⟨n, hn⟩ := HI t ht hk u hu hult
  exact ⟨n, le_trans_inT hs (inT_vOf_72 Hp u hu) (inT_vOf_72 Hp _ (stdB1_fsB t ht n)) hle hn⟩

/-- **§76 の最終形。** 326 行目の証明書に残る仮説は 4 つ —
    `PsiIdxOKStd172` (§72 の門)、`DictLtA74` (`dict` の順序保存)、`CofDenseS1` (密度)、
    `BCofIn71` (Buchholz 側の共終性)。§74.7 の最良は 5 つで、うち 2 つは絞らない形の
    `PsiIdxOKStd`・`RegionStd` だった。 -/
theorem certIn_t326_dict76 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (HCD : CofDenseS1) (HBC : BCofIn71)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_72 Hp (limDecS1_76 Hp H2) (limIncS1_76 Hp H2)
    (limCofS1_172_76 Hp HCD
      (cofInS1_172_76 Hp (vOfLtA71'_76 Hp (vOfLtA71_of_dictLt76 Hp H2)) HBC)) hacc

/-- 同じものを §73 の一歩ぶんの門で。`K` の側に残るのは `PsiIdxStep073` ひとつ。 -/
theorem certIn_t326_step76 (Hs : PsiIdxStep073) (H2 : DictLtA74)
    (HCD : CofDenseS1) (HBC : BCofIn71)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_dict76 (psiIdxOKStd172_of_step073 Hs) H2 HCD HBC hacc

/-- 恒等式そのものも §73 の一歩ぶんの門だけで出る。 -/
theorem vOfIsDict_step76 (Hs : PsiIdxStep073) : VOfIsDict74 :=
  vOfIsDict76 (psiIdxOKStd172_of_step073 Hs)

end

/-! ### §76.6 測定 (凍結)

母集団の作り方を先に書く。§65–§74 の掃きとは違って**深さで作る** — §66 の反例は `ψ` の
添字 3 が要り、§73 の反例は `ψ` の入れ子 5 段が要ったのに、どちらも幅で作った何千個の
母集団には現れなかったからである。したがってここは 100 個ほどしか使わず、そのかわり

  * 入れ子はどれも **5 段**、
  * `ψ` の添字は **0…3** — いま効いている上限 `1` の 2 つ先まで、
  * 変数はそれが実際に走る形の上で動かす (`BT` の変数は `BT` 全体の上で、
    `bValA71` の像の上ではなく)、
  * **領域の外の項をわざと入れる**、

の 4 つを守る。

    mixT76 [v₁,…,vₙ] = ψ_{v₁}(ψ_{v₂}(… ψ_{vₙ}(0) …))     添字の側の縦棒 (深さ n)
    btT76  [u₁,…,uₙ] = D_{u₁}(D_{u₂}(… D_{uₙ}(0) …))       BT の側の縦棒
    bits76 5         = {0,1}⁵                              32 通り
    hiSeqs76         = 4 つの型の 5 か所のどれか 1 つを 2 か 3 に替えたもの   40 通り
    seedS76          = 5 つの型

    deepB76  = (bits76 5).map mixT76                        32 本の縦棒 (段 0,1)
             ++ hiSeqs76.map mixT76                         40 本 (段 2,3 を含む = 領域の外)
             ++ seedS76 × seedS76 の 2 成分和                25 個
             ++ seedS76 の先頭に (0,0) を足したもの           5 個 (先頭成分が ψ₀0 になる側)
             ++ [t326, fsB t326 0, fsB t326 1, fsB t326 2]   326 行目そのもの
                                                            計 106、重複なし
    deepBT76 = 同じ 3 つを `BT` の上で                       計 97、重複なし
    tPool76  = 𝔗(M) の項 15 個。`inT` で絞らない — 側条件を測るための母集団だから。

**否定的結果を先に。**

  * `collapse_ne_one76` の `inT x` は飾りではない。`ψ₀(0 ⊕ 0) = 1` であって `0 ⊕ 0 ≠ 0`。
    `tPool76` を 𝔗(M) の項の上で (`dict` の像の上でではなく) 走らせるとこれが出る。
    `collapse u x = one` になるのは `tPool76 × {0,1,2,3}` の 60 通りのうち 2 通りだけで、
    その 2 つが `(0, 0)` と `(0, 0 ⊕ 0)` である。
  * `dict_ne_zero76` の `BT.isStd` も飾りではない。`dict (0 ⊕ 0) = 0` で `0 ⊕ 0 ≠ 0`。
    落ちるのは `isStd` の `isP` の連言である。
  * **`DictLtA74` は段の上限を外すと偽。** 段 2 以上の節を持つ添字 10 個の 100 対のうち
    **6 対**で `dict` が Buchholz の順序を保たない。最小の証人は

        (0,0)(1,0)(2,3)(3,0)(4,0)  <  (0,0)(1,2)(2,0)(3,0)(4,0)   (Buchholz)
        `dict` の像では成り立たない。

  * **`BT` の側では `BT.isStd` も要る。** 段 1 以下だが Buchholz 標準でない 10 項の
    100 対のうち **5 対**で破れる。証人は `ψ₀ψ₀ψ₁ψ₁ψ₀0 < ψ₀ψ₁ψ₀ψ₀ψ₁0`。
    添字の側 (`bValA71` の像) にはこの形が現れないので、`deepB76` を使う限りこの
    反例は見えない — **母集団の形が答えを変える例**である。

肯定的な側。`VOfIsDict74` は定理なので `deepB76` の行は確認であって根拠ではないが、
**領域の外でも 1 つも破れない** (106 個で 0 失敗)。部分領域の 14 個はどれも先頭成分が
`ψ₀0` ではない、つまり恒等式はどれも `1 + ψ₀(α) = ψ₀(α)` の側で、帳簿ではない。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term

/-- 段の列を 1 本の縦棒に。 -/
def mixT76 : List Nat → B
  | [] => .nil
  | v :: r => .nd v .nil (mixT76 r)

/-- `BT` の側の縦棒。 -/
def btT76 : List Nat → BT
  | [] => BT.zero
  | u :: r => BT.D u (btT76 r)

/-- 長さ `n` の `{0,1}` 列すべて。 -/
def bits76 : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (bits76 n).flatMap fun l => [0 :: l, 1 :: l]

/-- 5 か所のどれか 1 つを 2 か 3 に替えたもの — 上限 1 の 2 つ先まで届かせる。 -/
def hiSeqs76 : List (List Nat) :=
  [[0,0,0,0,0], [0,1,0,1,0], [1,1,1,1,1], [0,0,1,1,0]].flatMap fun l =>
    (List.range 5).flatMap fun i => [2, 3].map fun v => l.set i v

def seedS76 : List (List Nat) :=
  [[0,0,0,0,0], [0,1,0,1,0], [1,0,0,1,0], [0,0,1,0,1], [1,1,0,0,0]]

/-- 添字の側の母集団。 -/
def deepB76 : List B :=
  (bits76 5).map mixT76
  ++ hiSeqs76.map mixT76
  ++ (seedS76.flatMap fun l1 => seedS76.map fun l2 => appB (mixT76 l1) (mixT76 l2))
  ++ seedS76.map (fun l => appB (B.nd 0 .nil .nil) (mixT76 l))
  ++ [t326, fsB t326 0, fsB t326 1, fsB t326 2]

/-- `BT` の側の母集団。`bValA71` の像に限らない。 -/
def deepBT76 : List BT :=
  (bits76 5).map btT76
  ++ hiSeqs76.map btT76
  ++ (seedS76.flatMap fun l1 => seedS76.map fun l2 => BT.sum (btT76 l1) (btT76 l2))

/-- 𝔗(M) の項の母集団。`inT` で絞らない。 -/
def tPool76 : List Term :=
  [zero, one, omega, M, Om, add zero zero, add zero one, add one zero,
   omg zero, phi zero zero, phi one zero, psi Om zero, Z zero, Z one, ofNat 3]

def subD76 : List B := (deepB76.filter stdB1).take 10
def outD76 : List B := (deepB76.filter fun t => !(lvlLe 1 t)).take 10

def dictLtFailB76 (l : List B) : Nat :=
  (l.flatMap fun u => l.filter fun t =>
     BT.lt (bValA71 u) (bValA71 t) && !(TM.Term.lt (dict (bValA71 u)) (dict (bValA71 t)))).length

def pairsBT76 : List BT := (deepBT76.filter fun x => BT.isStd x && btLe72 1 x).take 10
def pairsBTout76 : List BT := (deepBT76.filter fun x => !(btLe72 1 x)).take 10
def pairsBTns76 : List BT := (deepBT76.filter fun x => !(BT.isStd x) && btLe72 1 x).take 10

def dictLtFailBT76 (l : List BT) : Nat :=
  (l.flatMap fun x => l.filter fun y => BT.lt x y && !(TM.Term.lt (dict x) (dict y))).length

/-! 母集団の形。 -/
#guard deepB76.length == 106
#guard deepB76.eraseDups.length == 106
#guard deepBT76.length == 97
#guard deepBT76.eraseDups.length == 97
#guard tPool76.length == 15
#guard (deepB76.filter stdB1).length == 14
#guard (deepB76.filter fun t => lvlLe 1 t).length == 66
#guard (deepBT76.filter fun x => btLe72 1 x).length == 57

/-! §76.4 の確認。**定理なので根拠ではない。** 領域の外でも破れない。 -/
#guard (deepB76.filter fun t => !(vOf t == dict (bValA71 t))).length == 0
/-! 恒等式は自明ではない — 部分領域の 14 個はどれも先頭成分が `ψ₀0` でない。 -/
#guard ((deepB76.filter stdB1).filter fun t =>
  (bValA71 t).toL.head? == some (BT.D 0 BT.zero)).length == 0
#guard (deepB76.filter fun t => (bValA71 t).toL.head? == some (BT.D 0 BT.zero)).length == 5

/-! 側条件の鋭さ (否定的結果)。 -/
-- `collapse_ne_one76` の除外した場合そのもの。
#guard collapse 0 TM.Term.zero == TM.Term.one
-- `inT x` を落とすと偽。`0 ⊕ 0 ≠ 0` なのに `ψ₀(0 ⊕ 0) = 1`。
#guard collapse 0 (TM.Term.add TM.Term.zero TM.Term.zero) == TM.Term.one
#guard TM.Term.inT (TM.Term.add TM.Term.zero TM.Term.zero) == false
#guard (tPool76.flatMap fun x => (List.range 4).filter fun u => collapse u x == one).length == 2
-- `dict_ne_zero76` の `BT.isStd` を落とすと偽。
#guard dict (BT.sum BT.zero BT.zero) == TM.Term.zero
#guard BT.isStd (BT.sum BT.zero BT.zero) == false
-- `plus_one_eq76` の `α ≠ 1`、`omegaNF_ne_one76` の `x ≠ 0`。
#guard TM.Term.plus TM.Term.one TM.Term.one != TM.Term.one
#guard TM.Term.omegaNF TM.Term.zero == TM.Term.one

/-! `DictLtA74` — **未証明**。100 対ずつ、深さ 5、添字 0…3。 -/
#guard subD76.length == 10
#guard dictLtFailB76 subD76 == 0
#guard outD76.length == 10
-- **段の上限を外すと偽。**
#guard dictLtFailB76 outD76 == 6
#guard pairsBT76.length == 10
#guard dictLtFailBT76 pairsBT76 == 0
#guard pairsBTout76.length == 10
#guard dictLtFailBT76 pairsBTout76 == 6
#guard pairsBTns76.length == 10
-- **`BT` の側では `BT.isStd` を外しても偽。添字の側の母集団では見えない。**
#guard dictLtFailBT76 pairsBTns76 == 5

end

/-! ### §76.7 公理 -/

/-! ## §75 THE `u = 0` BRANCH: THE STATE FALLS OUT OF THE `K`-GATE, AND `isStd` IS NOT
    DECORATION

§73 closed the `u = 1` half of the last `inT` gate and left exactly one clause,

    PsiIdxStep073 : ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true →
                    KsetStepOK 0 (dict a)

together with two independent jobs for whoever came next — (1) the transport
`K_{Ω₁}(dict a) < dict a`, which is where `BT.isStd` has to be spent, and (3) "the step from
the local condition back to `KsetStepOK`", which §73 said it does **not** provide, because the
fold's later steps use `plus i0 Δ` rather than `sub1 Δ` and `le i0 (plus i0 Δ)` was only
available as an `inT`-conditioned lemma whose `inT` is what the gate produces.

**§75 does jobs (3) and (2) in full.**  The gate is NOT closed; what closes is the whole
distance between the gate and a condition that looks at ONE `(a, c)` pair at a time, never at
the state of the fold, and is then implied by the four order facts §73.7 named.  What is left
is (1) alone.

WHAT IS PROVED, UNCONDITIONALLY.

  §75.1  **A SUM DOMINATES ITS RIGHT SUMMAND, on 𝔗(M).**  `le_ofList_append75`: for a
         descending list of 𝔗(M)-components, `ofList L ≤ ofList (Q ++ L)`.  The induction is
         on `|Q| + |L|`, not on `|Q|`: the equal-head branch moves the head of `L` into `Q`,
         which keeps `|Q|` fixed and shortens `L`.  Two corollaries carry the section:
         `le_self_plus75 : le t (plus s t)` — the missing half of §65.1's `plus_mono_right_inT`,
         which only ever gave `le s (plus s t)` — and `le_sub1_self75 : le (sub1 d) d`.
         `inT_mem_Kset75` records that the elements of a `K`-set of a 𝔗(M) term are 𝔗(M)
         terms, so §8.5's order theory applies to them; without it the transitivity steps
         below cannot even be stated.

  §75.2  **THE MATERIAL OF ONE INDEX STEP.**  `ddOf75 w (a,c) = W^(a ⊖ W)·c` is the amount
         the strongly critical branch adds.  `mem_Kset_ddOf75` : `K_κ Δ ⊆ K_κ a ∪ K_κ c`,
         by §66.2's `mem_Kset_mulL` twice and `Kset κ Ω_{u+1} = ∅`.  `le_prev_idxOf75` and
         `le_sub1dd_idxOf75` say what the emitted index dominates: the PREVIOUS index `i0`,
         and `Δ ⊖ 1`.  **Both branches of `idxOf` are covered** — that is exactly what §73
         could not do, and §75.6 says how thinly §73's corpus exercised the second one.

  §75.3  **THE STATE FALLS OUT.**  `scan_local75` runs `StInv` (§64.5) and the new `KInv75`
         along `scanSt` at the same time, and `ksetStepOK_of_local75` concludes

             inT x → lt x M → LocalK75 u x → KsetStepOK u x

         for EVERY `u`, not just `u = 0`.  `LocalK75` is the proposition form of §73.6's
         decided `localOKb73`, and `localK75_of_b` turns a `#guard` into a proof of it for a
         given term.  Note what is NOT assumed: no `inT` on the index, no `PsiIdxOK`, and no
         `BT.isStd`.  The `inT (psi …)` that `stepF_inv` demands is manufactured on the way
         past, out of `KInv75` itself, by §66.1's `inT_psi_idx`.

  §75.4  **AND THE FOUR LOCAL FACTS SUFFICE (= §73's job (2)).**  `LocalFacts75` is §73.7's
         (K2)–(K5) for one pair, and `localK75_of_facts75` derives the local condition from
         them.  Transitivity comes from `inT` through §8.5 — `pure73` is not needed, and
         neither is the gate.  The (K4) branch is where `sub1 Δ ≠ Δ` is used, and it is used
         exactly once.

  §75.4b/§75.4c  **BUT (K2) IS FALSE AS §73 STATED IT, AND TWO CLAUSES DO THE WORK OF FOUR.**
         `K_{Ω₁} aV < aV` fails on 9 of the 204 firing steps of the `BT.isStd`-filtered
         depth-9 corpus (§75.6, 否定 4) — §73 measured it at zero failures on 120 steps one
         level shallower.  What is true there is the comparison against `Δ`, not against
         `aV`, so `LocalFacts2_75` keeps only (K2') `K_κ aV ∪ K_κ cV < Δ` and (K4), and
         `localK75_of_facts2_75` gets the local condition out of those two alone; (K3) and
         (K5) are not needed.  `localFacts2_of_facts75` shows the corrected pair is weaker
         than §73's four.  `kset_fst_reg75` and `kset_snd_ofNat75` discharge, for free, 30 of
         the 31 (K5) exceptions and every step whose coefficient is a natural number.

  §75.5  **THE ASSEMBLY.**  `inT_dict_of_local75` is the structural induction that makes the
         `inT x` hypothesis of §75.3 legitimate: the argument's `inT` comes from the induction
         hypothesis, not from the gate, so there is no circle.  `psiIdxStep073_of_local75`
         (and `psiIdxStep073_of_facts75`) proves §73's remaining clause, and
         `certIn_t326_local75` re-derives row 326's certificate.

WHAT IS NOT CLAIMED, AND THE TWO THINGS §73 GOT WRONG ABOUT ITS OWN CORPUS.

  `LocalStd75` is NOT proved.  It is much weaker in SHAPE than `PsiIdxStep073` — one pair, no
  state, no fold — but it is the same amount of ordinal theory: it still needs the transport,
  and §75.6 measures where.

  **Two of §73's measurements were corpus artefacts, and both fail one level deeper.**

  (i) **"肯定 2" — the gate without `BT.isStd`.**  §73 measured `stepOKb 0 (dict a)` at zero
  failures on all of `btPool72`, `hotB73` and the sub-region, and wrote that the gate does not
  fall even without `BT.isStd`.  One more level of `ψ`-nesting kills that: on `hotD75`
  (`ψ`-nesting 8, 2127 terms) the gate falls on **16** terms, on `hotE75` (nesting 9, 4319
  terms) on 61, and every one of them has `BT.isStd (BT.D 0 a) = false`.
  `not_ksetStepOK_wStep75` freezes the smallest, `wStep75 = ψ₁ψ₁ψ₁ψ₀ψ₁ψ₁ψ₁ψ₁0`, which is
  itself Buchholz standard and stops being so under one `ψ₀`.  **`BT.isStd` is load-bearing
  for the gate itself, not only for the transport §73 named.**

  (ii) **"肯定 3" — the (K2) half of the decomposition.**  See §75.4c above.  The route §73
  recommended cannot be walked as written; the corrected two-clause version can.

  WHAT IS STILL MEASURED-ONLY.  (K3) `cV ≤ Δ` holds at every firing step of every corpus
  swept, and the general lemma behind it, `le c (mulL e c)`, holds on all 434281 ordered
  pairs from a 659-term pool of the level-one image (`s75sweep5.lean`); so does
  `omegaNF (logOm p) = p` on all 630 additively principal `inT` subterms below `M`.  Neither
  is proved, and the second is FALSE without `lt p M` — `ω̄^·` breaks it.  (K4) holds at all
  27 steps where `Δ ⊖ 1 ≠ Δ`.  The transport `K_{Ω₁}(dict a) < dict a` is still exactly where
  `BT.isStd` has to be spent, and §75 did not spend it.
-/

/-! ### §75.1 和と接尾辞 — `le t (plus s t)` -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

private theorem inTL_sub75 {l1 l2 : List Term} (h : ∀ x ∈ l1, x ∈ l2)
    (h2 : inTL l2 = true) : inTL l1 = true := by
  show l1.all _ = true
  rw [List.all_eq_true]
  intro x hx
  exact List.all_eq_true.mp h2 x (h x hx)

/-- **接尾辞は本体以下。** 降順の成分列 `Q ++ L` について `ofList L ≤ ofList (Q ++ L)`。 -/
private theorem le_ofList_append75 : ∀ (n : Nat) (Q L : List Term),
    Q.length + L.length ≤ n → inTL (Q ++ L) = true → descL (Q ++ L) = true →
    le (ofList L) (ofList (Q ++ L)) = true := by
  intro n
  induction n with
  | zero =>
    intro Q L hn _ _
    have hQ : Q = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hL : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hQ, hL]
    exact Evidence.WF.le_self _
  | succ m ih =>
    intro Q L hn hc hd
    cases Q with
    | nil => exact Evidence.WF.le_self _
    | cons q Q' =>
      cases L with
      | nil =>
        show le zero _ = true
        exact le_zero_left _
      | cons b r =>
        have hAeq : (q :: Q') ++ (b :: r) = q :: (Q' ++ (b :: r)) := rfl
        rw [hAeq] at hc hd ⊢
        obtain ⟨⟨hapq, hiq⟩, hcA⟩ := inTL_cons.mp hc
        have hdA : descL (Q' ++ (b :: r)) = true := descL_tail hd
        have hbmem : b ∈ Q' ++ (b :: r) := List.mem_append.mpr (Or.inr (List.Mem.head _))
        have hbq : le b q = true := descL_bound_inT _ q hiq hcA hd b hbmem
        have hAne : Q' ++ (b :: r) ≠ [] := by
          intro hz; rw [hz] at hbmem; cases hbmem
        rw [ofList_cons_ne_nil hAne]
        have hcbr : inTL (b :: r) = true :=
          inTL_sub75 (fun x hx => List.mem_append.mpr (Or.inr hx)) hcA
        have hdbr : descL (b :: r) = true := descL_of_append_right Q' (b :: r) hdA
        by_cases hqb : q = b
        · subst hqb
          cases r with
          | nil =>
            show le q _ = true
            exact le_of_lt (lt_head_add hapq _)
          | cons c s =>
            show le (add q (ofList (c :: s))) (add q (ofList (Q' ++ (q :: c :: s)))) = true
            refine le_add_tail ?_
            have hsplit : Q' ++ (q :: c :: s) = (Q' ++ [q]) ++ (c :: s) := by
              rw [List.append_assoc]; rfl
            rw [hsplit]
            refine ih (Q' ++ [q]) (c :: s) ?_ (by rw [← hsplit]; exact hcA)
              (by rw [← hsplit]; exact hdA)
            simp only [List.length_append, List.length_cons, List.length_nil] at hn ⊢
            omega
        · have hltbq : lt b q = true := by
            rcases (Bool.or_eq_true _ _).mp hbq with he | hl
            · exact absurd (eq_of_beq he).symm hqb
            · exact hl
          refine le_of_lt ?_
          refine lt_of_hd_lt (inT_ofList _ hcbr hdbr)
            (show inT (add q (ofList (Q' ++ (b :: r)))) = true from by
              rw [← ofList_cons_ne_nil hAne]; exact inT_ofList _ hc hd)
            (toList_ofList _ (fun x hx =>
              ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcbr x hx)).1))
            (show toList (add q (ofList (Q' ++ (b :: r)))) = q :: _ from rfl) hltbq

/-- **右の引数は和以下。** `t ≤ s ⊕ t` — §73 が名指しした `le i0 (plus i0 Δ)` の対。 -/
theorem le_self_plus75 {s t : Term} (hs : inT s = true) (ht : inT t = true) :
    le t (plus s t) = true := by
  cases hl : toList t with
  | nil =>
    rw [plus_nil hl, toList_eq_nil t hl]
    exact le_zero_left s
  | cons b1 r =>
    have hp : inT (plus s t) = true := inT_plus hs ht
    have htl : toList (plus s t) = (toList s).filter (fun a => le b1 a) ++ toList t :=
      toList_plus_inT hs ht hl
    obtain ⟨hcp, hdp⟩ := inT_toList _ hp
    rw [htl] at hcp hdp
    have key := le_ofList_append75
      (((toList s).filter (fun a => le b1 a)).length + (toList t).length)
      ((toList s).filter (fun a => le b1 a)) (toList t) (Nat.le_refl _) hcp hdp
    rw [inT_ofList_toList t ht] at key
    rw [show ofList ((toList s).filter (fun a => le b1 a) ++ toList t) = plus s t from by
      rw [← htl, inT_ofList_toList _ hp]] at key
    exact key

/-- **`sub1` は下げるだけ。** -/
theorem le_sub1_self75 {d : Term} (hd : inT d = true) : le (sub1 d) d = true := by
  obtain ⟨hc, hdd⟩ := inT_toList d hd
  show le (match toList d with
      | [] => zero
      | p :: rest => if p == TM.Term.one then ofList rest else d) d = true
  cases hl : toList d with
  | nil => rw [toList_eq_nil d hl]; exact Evidence.WF.le_self _
  | cons p rest =>
    show le (if (p == TM.Term.one) = true then ofList rest else d) d = true
    by_cases hp : (p == TM.Term.one) = true
    · rw [if_pos hp]
      rw [hl] at hc hdd
      have key := le_ofList_append75 (1 + rest.length) [p] rest (by simp)
        (show inTL ([p] ++ rest) = true from hc) (show descL ([p] ++ rest) = true from hdd)
      rw [show ([p] ++ rest) = p :: rest from rfl, ← hl, inT_ofList_toList d hd] at key
      exact key
    · rw [if_neg hp]; exact Evidence.WF.le_self _

/-- `K` の元は 𝔗(M) の項。 -/
theorem inT_mem_Kset75 : ∀ (t : Term), inT t = true → ∀ (k y : Term),
    y ∈ Kset k t → inT y = true := by
  intro t
  induction t with
  | zero => intro _ k y h; cases h
  | M => intro _ k y h; cases h
  | omg a iha =>
    intro ht k y h
    exact iha ((Bool.and_eq_true _ _).mp (show (inT a && lt M a) = true from ht)).1 k y
      (show y ∈ Kset k a from h)
  | phi a b iha ihb =>
    intro ht k y h
    have h2 := (Bool.and_eq_true _ _).mp
      ((Bool.and_eq_true _ _).mp
        ((Bool.and_eq_true _ _).mp
          (show (inT a && inT b && lt a M && lt b M) = true from ht)).1).1
    rcases List.mem_append.mp (show y ∈ Kset k a ++ Kset k b from h) with h1 | h1
    · exact iha h2.1 k y h1
    · exact ihb h2.2 k y h1
  | psi p b ihp ihb =>
    intro ht k y h
    have h2 := (Bool.and_eq_true _ _).mp
      ((Bool.and_eq_true _ _).mp
        ((Bool.and_eq_true _ _).mp
          ((Bool.and_eq_true _ _).mp
            (show (p.isR && inT p && inT b && lt b M &&
              (Kset p b).all (fun x => lt x b)) = true from ht)).1).1).1
    have hip : inT p = true := h2.2
    have hib : inT b = true := ((Bool.and_eq_true _ _).mp
      ((Bool.and_eq_true _ _).mp
        ((Bool.and_eq_true _ _).mp
          (show (p.isR && inT p && inT b && lt b M &&
            (Kset p b).all (fun x => lt x b)) = true from ht)).1).1).2
    rw [show Kset k (psi p b) = (if le (psi p b) (kminus k) then [] else
        if lt p k then Kset k p else b :: (Kset k p ++ Kset k b)) from rfl] at h
    split at h
    · cases h
    · split at h
      · exact ihp hip k y h
      · rcases List.mem_cons.mp h with hq | hq
        · rw [hq]; exact hib
        · rcases List.mem_append.mp hq with h1 | h1
          · exact ihp hip k y h1
          · exact ihb hib k y h1
  | Z b ihb =>
    intro ht k y h
    exact ihb (show inT b = true from ht) k y (show y ∈ Kset k b from h)
  | add a b iha ihb =>
    intro ht k y h
    obtain ⟨_, hia, hib, _⟩ := inT_add ht
    rcases List.mem_append.mp (show y ∈ Kset k a ++ Kset k b from h) with h1 | h1
    · exact iha hia k y h1
    · exact ihb hib k y h1

/-! ### §75.2 一歩ぶんの指数 — 材料と `K` -/

/-- 強臨界枝が一歩で足す量 `Δ = W^(a ⊖ W)·c`。 -/
def ddOf75 (w : Term) (ac : Term × Term) : Term := mulL (mulL w (subAP w ac.1)) ac.2

theorem inT_ddOf75 {w : Term} (hw : inT w = true) {ac : Term × Term}
    (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) : inT (ddOf75 w ac) = true :=
  inT_mulL mulDescInT (inT_mulL mulDescInT hw (inT_subAP h1)) h3

/-- **`Δ` の `K` は材料の `K` に戻る。** `Kset κ Ω_{u+1} = ∅` を使う。 -/
theorem mem_Kset_ddOf75 {u : Nat} {y : Term} {ac : Term × Term}
    (h : y ∈ Kset (reg (u+1)) (ddOf75 (reg (u+1)) ac)) :
    y ∈ Kset (reg (u+1)) ac.1 ∨ y ∈ Kset (reg (u+1)) ac.2 := by
  rcases mem_Kset_mulL (show y ∈ Kset (reg (u+1))
      (mulL (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) ac.2) from h) with h1 | h1
  · rcases mem_Kset_mulL h1 with h2 | h2
    · exact absurd h2 (fun hc => mem_Kset_reg (u+1) hc)
    · exact Or.inl (mem_Kset_subAP h2)
  · exact Or.inr h1

/-- 直前の指数は今の指数以下。 -/
theorem le_prev_idxOf75 {w : Term} (hw : inT w = true) {s : Option Term × Option Term}
    {ac : Term × Term} {i0 : Term} (hs : StInv s) (hs1 : s.1 = some i0)
    (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) :
    le i0 (idxOf w s ac) = true := by
  have hi0 : inT i0 = true := (hs.1 i0 hs1).1
  have hd : inT (ddOf75 w ac) = true := inT_ddOf75 hw h1 h3
  have hidx : idxOf w s ac = plus i0 (ddOf75 w ac) := by
    show (match s.1 with
          | none => sub1 (mulL (mulL w (subAP w ac.1)) ac.2)
          | some j => plus j (mulL (mulL w (subAP w ac.1)) ac.2)) = _
    rw [hs1]
    try rfl
  rw [hidx]
  have h := plus_mono_right_inT i0 hi0 zero (ddOf75 w ac) inT_zero hd (le_zero_left _)
  rwa [plus_nil (show toList (zero : Term) = [] from rfl)] at h

/-- `Δ ⊖ 1` は今の指数以下 — 状態がどちらでも。 -/
theorem le_sub1dd_idxOf75 {w : Term} (hw : inT w = true) {s : Option Term × Option Term}
    {ac : Term × Term} (hs : StInv s) (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) :
    le (sub1 (ddOf75 w ac)) (idxOf w s ac) = true := by
  have hd : inT (ddOf75 w ac) = true := inT_ddOf75 hw h1 h3
  have hsd : inT (sub1 (ddOf75 w ac)) = true := inT_sub1 hd
  cases hs1 : s.1 with
  | none =>
    have hidx : idxOf w s ac = sub1 (ddOf75 w ac) := by
      show (match s.1 with
            | none => sub1 (mulL (mulL w (subAP w ac.1)) ac.2)
            | some j => plus j (mulL (mulL w (subAP w ac.1)) ac.2)) = _
      rw [hs1]
      try rfl
    rw [hidx]
    exact Evidence.WF.le_self _
  | some i0 =>
    have hi0 : inT i0 = true := (hs.1 i0 hs1).1
    have hidx : idxOf w s ac = plus i0 (ddOf75 w ac) := by
      show (match s.1 with
            | none => sub1 (mulL (mulL w (subAP w ac.1)) ac.2)
            | some j => plus j (mulL (mulL w (subAP w ac.1)) ac.2)) = _
      rw [hs1]
      try rfl
    rw [hidx]
    exact le_trans_inT hsd hd (inT_plus hi0 hd) (le_sub1_self75 hd) (le_self_plus75 hi0 hd)

/-- 局所条件から、吐かれた指数についての 2.1(vi) の `K` の連言。 -/
theorem kall_idxOf75 {u : Nat} {s : Option Term × Option Term} {ac : Term × Term}
    (hs : StInv s)
    (hk : ∀ i0, s.1 = some i0 → ∀ y, y ∈ Kset (reg (u+1)) i0 → lt y i0 = true)
    (h1 : inT ac.1 = true) (h2 : lt ac.1 M = true)
    (h3 : inT ac.2 = true) (h4 : lt ac.2 M = true)
    (hloc : ∀ y, (y ∈ Kset (reg (u+1)) ac.1 ∨ y ∈ Kset (reg (u+1)) ac.2) →
        lt y (sub1 (ddOf75 (reg (u+1)) ac)) = true) :
    ∀ y, y ∈ Kset (reg (u+1)) (idxOf (reg (u+1)) s ac) →
      lt y (idxOf (reg (u+1)) s ac) = true := by
  have hw : inT (reg (u+1)) = true := inT_reg (u+1)
  have hlw : lt (reg (u+1)) M = true := ltM_reg (u+1)
  have hd : inT (ddOf75 (reg (u+1)) ac) = true := inT_ddOf75 hw h1 h3
  have hsd : inT (sub1 (ddOf75 (reg (u+1)) ac)) = true := inT_sub1 hd
  obtain ⟨hidxT, _⟩ := inT_idxOf mulDescInT hw hlw hs h1 h2 h3 h4
  have hlocIdx : ∀ y, (y ∈ Kset (reg (u+1)) ac.1 ∨ y ∈ Kset (reg (u+1)) ac.2) →
      lt y (idxOf (reg (u+1)) s ac) = true := by
    intro y hy
    have hyi : inT y = true := by
      rcases hy with hy | hy
      · exact inT_mem_Kset75 ac.1 h1 _ y hy
      · exact inT_mem_Kset75 ac.2 h3 _ y hy
    exact lt_of_lt_of_le3 (inT_le_fragR y hyi) (inT_le_fragR _ hsd) (inT_le_fragR _ hidxT)
      (hloc y hy) (le_sub1dd_idxOf75 hw hs h1 h3)
  intro y hy
  cases hs1 : s.1 with
  | none =>
    have hidx : idxOf (reg (u+1)) s ac = sub1 (ddOf75 (reg (u+1)) ac) := by
      show (match s.1 with
            | none => sub1 (mulL (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) ac.2)
            | some j => plus j (mulL (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) ac.2)) = _
      rw [hs1]
      try rfl
    rw [hidx] at hy
    exact hlocIdx y (mem_Kset_ddOf75 (mem_Kset_sub1 hy))
  | some i0 =>
    have hi0 : inT i0 = true := (hs.1 i0 hs1).1
    have hidx : idxOf (reg (u+1)) s ac = plus i0 (ddOf75 (reg (u+1)) ac) := by
      show (match s.1 with
            | none => sub1 (mulL (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) ac.2)
            | some j => plus j (mulL (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) ac.2)) = _
      rw [hs1]
      try rfl
    rw [hidx] at hy
    rcases mem_Kset_plus hy with h5 | h5
    · have hyi : inT y = true := inT_mem_Kset75 i0 hi0 _ y h5
      exact lt_of_lt_of_le3 (inT_le_fragR y hyi) (inT_le_fragR i0 hi0) (inT_le_fragR _ hidxT)
        (hk i0 hs1 y h5) (le_prev_idxOf75 hw hs hs1 h1 h3)
    · exact hlocIdx y (mem_Kset_ddOf75 h5)

/-! ### §75.3 走査に沿って — 局所条件から一歩ぶんの門 -/

/-- 状態の `K` 不変量 — 直前の指数は自分の `K` より上。 -/
def KInv75 (u : Nat) (s : Option Term × Option Term) : Prop :=
  ∀ i0, s.1 = some i0 → ∀ y, y ∈ Kset (reg (u+1)) i0 → lt y i0 = true

theorem kInv75_none (u : Nat) :
    KInv75 u ((none : Option Term), (none : Option Term)) := by
  intro i0 h; cases h

/-- **局所条件。** §73.6 の `localOKb73` の命題版 — 状態を見ない、対ごとの条件。 -/
def LocalK75 (u : Nat) (x : Term) : Prop :=
  ∀ ac ∈ (wcnf (reg (u+1)) (toList x)).1, le (reg (u+1)) ac.1 = true →
    ∀ y, (y ∈ Kset (reg (u+1)) ac.1 ∨ y ∈ Kset (reg (u+1)) ac.2) →
      lt y (sub1 (ddOf75 (reg (u+1)) ac)) = true

theorem localK75_of_b {u : Nat} {x : Term} (h : localOKb73 u x = true) : LocalK75 u x := by
  intro ac hac hle y hy
  have h1 := List.all_eq_true.mp
    (show (wcnf (reg (u+1)) (toList x)).1.all (fun ac =>
        !(le (reg (u+1)) ac.1) ||
          ((Kset (reg (u+1)) ac.1 ++ Kset (reg (u+1)) ac.2).all fun y =>
            lt y (sub1 (mulL (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) ac.2)))) = true from h)
    ac hac
  rw [hle, Bool.not_true, Bool.false_or] at h1
  refine List.all_eq_true.mp h1 y ?_
  rcases hy with hy | hy
  · exact List.mem_append.mpr (Or.inl hy)
  · exact List.mem_append.mpr (Or.inr hy)

/-- **§75 の心臓。** 走査に沿って `StInv` と `KInv75` を同時に回し、局所条件から
    一歩ぶんの 2 つの連言を出す。`plus i0 Δ` の枝を閉じるのが `le_prev_idxOf75` と
    `le_sub1dd_idxOf75` — どちらも `le_ofList_append75` に載っている。 -/
theorem scan_local75 {u : Nat} :
    ∀ (l : List (Term × Term)) (s : Option Term × Option Term), StInv s → KInv75 u s →
      (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
      (∀ ac ∈ l, le (reg (u+1)) ac.1 = true → ∀ y,
          (y ∈ Kset (reg (u+1)) ac.1 ∨ y ∈ Kset (reg (u+1)) ac.2) →
          lt y (sub1 (ddOf75 (reg (u+1)) ac)) = true) →
      ∀ p ∈ scanSt (reg (u+1)) (baseOf u) s l, le (reg (u+1)) p.2.1 = true →
        (∀ i0, p.1.1 = some i0 → ∀ y, y ∈ Kset (reg (u+1)) i0 →
            lt y (idxOf (reg (u+1)) p.1 p.2) = true) ∧
        (∀ y, (y ∈ Kset (reg (u+1)) p.2.1 ∨ y ∈ Kset (reg (u+1)) p.2.2) →
            lt y (idxOf (reg (u+1)) p.1 p.2) = true) := by
  have hw : inT (reg (u+1)) = true := inT_reg (u+1)
  have hlw : lt (reg (u+1)) M = true := ltM_reg (u+1)
  intro l
  induction l with
  | nil => intro s _ _ _ _ p hp; cases hp
  | cons ac t ih =>
    intro s hs hk hall hloc p hp hle
    have hac := hall ac (List.Mem.head _)
    have hhead : le (reg (u+1)) ac.1 = true →
        (∀ i0, s.1 = some i0 → ∀ y, y ∈ Kset (reg (u+1)) i0 →
            lt y (idxOf (reg (u+1)) s ac) = true) ∧
        (∀ y, (y ∈ Kset (reg (u+1)) ac.1 ∨ y ∈ Kset (reg (u+1)) ac.2) →
            lt y (idxOf (reg (u+1)) s ac) = true) := by
      intro hle2
      obtain ⟨hidxT, _⟩ := inT_idxOf mulDescInT hw hlw hs hac.1 hac.2.1 hac.2.2.1 hac.2.2.2
      constructor
      · intro i0 hs1 y hy
        have hi0 : inT i0 = true := (hs.1 i0 hs1).1
        have hyi : inT y = true := inT_mem_Kset75 i0 hi0 _ y hy
        exact lt_of_lt_of_le3 (inT_le_fragR y hyi) (inT_le_fragR i0 hi0)
          (inT_le_fragR _ hidxT) (hk i0 hs1 y hy)
          (le_prev_idxOf75 hw hs hs1 hac.1 hac.2.2.1)
      · intro y hy
        have hyi : inT y = true := by
          rcases hy with hy | hy
          · exact inT_mem_Kset75 ac.1 hac.1 _ y hy
          · exact inT_mem_Kset75 ac.2 hac.2.2.1 _ y hy
        exact lt_of_lt_of_le3 (inT_le_fragR y hyi)
          (inT_le_fragR _ (inT_sub1 (inT_ddOf75 hw hac.1 hac.2.2.1)))
          (inT_le_fragR _ hidxT)
          (hloc ac (List.Mem.head _) hle2 y hy)
          (le_sub1dd_idxOf75 hw hs hac.1 hac.2.2.1)
    rcases List.mem_cons.mp (show p ∈ (s, ac) :: scanSt (reg (u+1)) (baseOf u)
        (stepF (reg (u+1)) (baseOf u) s ac) t from hp) with h | h
    · subst h
      exact hhead hle
    · have hkall : le (reg (u+1)) ac.1 = true →
          ∀ y, y ∈ Kset (reg (u+1)) (idxOf (reg (u+1)) s ac) →
            lt y (idxOf (reg (u+1)) s ac) = true := fun hle2 =>
        kall_idxOf75 hs hk hac.1 hac.2.1 hac.2.2.1 hac.2.2.2
          (hloc ac (List.Mem.head _) hle2)
      have hpsi : le (reg (u+1)) ac.1 = true →
          inT (psi (reg (u+1)) (idxOf (reg (u+1)) s ac)) = true := by
        intro hle2
        refine inT_psi_idx (isR_reg_succ u) hw hlw hs hac.1 hac.2.1 hac.2.2.1 hac.2.2.2 ?_
        rw [List.all_eq_true]
        intro y hy
        exact hkall hle2 y hy
      have hs' : StInv (stepF (reg (u+1)) (baseOf u) s ac) :=
        stepF_inv mulDescInT hw hlw (inT_baseOf u) (ltM_baseOf u) hs hac hpsi
      have hk' : KInv75 u (stepF (reg (u+1)) (baseOf u) s ac) := by
        intro i0 hi0 y hy
        cases hle2 : le (reg (u+1)) ac.1 with
        | true =>
          have hfst : (stepF (reg (u+1)) (baseOf u) s ac).1
              = some (idxOf (reg (u+1)) s ac) := by
            unfold stepF; rw [hle2]; try rfl
          rw [hfst] at hi0
          rw [← Option.some.inj hi0] at hy ⊢
          exact hkall hle2 y hy
        | false =>
          have hfst : (stepF (reg (u+1)) (baseOf u) s ac).1 = s.1 := by
            unfold stepF; rw [hle2]; try rfl
          rw [hfst] at hi0
          exact hk i0 hi0 y hy
      exact ih (stepF (reg (u+1)) (baseOf u) s ac) hs' hk'
        (fun a ha => hall a (List.Mem.tail _ ha))
        (fun a ha => hloc a (List.Mem.tail _ ha)) p h hle

/-- **§75.3 の主定理。** 状態を落とした局所条件から `KsetStepOK` — §73 が「二つ目の
    仕事」と呼んだ段。`inT x` は仮説だが `PsiIdxStep073` そのものではない。 -/
theorem ksetStepOK_of_local75 (u : Nat) (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (H : LocalK75 u x) : KsetStepOK u x := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨_, hallOK⟩ :=
    wcnf_spec_sc (inT_reg (u+1)) (isSC_reg_succ u) (toList x) hc hd (ltM_toList x hx hlx)
  intro p hp hle
  exact scan_local75 (wcnf (reg (u+1)) (toList x)).1 (none, none)
    stInv_none (kInv75_none u) hallOK H p hp hle

/-- 系 — 2.1(vi) の `K` の連言も出る。 -/
theorem ksetIdxOK_of_local75 (u : Nat) (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (H : LocalK75 u x) : KsetIdxOK u x :=
  ksetIdxOK_of_stepOK u x (ksetStepOK_of_local75 u x hx hlx H)


/-! ### §75.4 §73.7 の 4 つの局所事実から局所条件へ -/

/-- **§73.7 が名指しした 4 つ、対ひとつぶん。** `d := Δ = W^(a ⊖ W)·c` として
    (K2) `K a < a` かつ `K c < c`、(K3) `c ≤ d`、(K5) `a ≤ d` か `K a = ∅`、
    (K4) `d ⊖ 1 ≠ d` なら両方の `K` が空。 -/
def LocalFacts75 (u : Nat) (ac : Term × Term) : Prop :=
  (∀ y, y ∈ Kset (reg (u+1)) ac.1 → lt y ac.1 = true) ∧
  (∀ y, y ∈ Kset (reg (u+1)) ac.2 → lt y ac.2 = true) ∧
  le ac.2 (ddOf75 (reg (u+1)) ac) = true ∧
  (le ac.1 (ddOf75 (reg (u+1)) ac) = true ∨ ∀ y, y ∈ Kset (reg (u+1)) ac.1 → False) ∧
  (sub1 (ddOf75 (reg (u+1)) ac) ≠ ddOf75 (reg (u+1)) ac →
    (∀ y, y ∈ Kset (reg (u+1)) ac.1 → False) ∧ (∀ y, y ∈ Kset (reg (u+1)) ac.2 → False))

/-- **§75.4 の主定理 (= §73 の仕事 (2))。** 4 つの局所事実と推移律だけで局所条件が出る。
    推移律は `inT` からで、`pure73` も `inT` の門も要らない。 -/
theorem localK75_of_facts75 (u : Nat) (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (H : ∀ ac ∈ (wcnf (reg (u+1)) (toList x)).1, le (reg (u+1)) ac.1 = true →
      LocalFacts75 u ac) : LocalK75 u x := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg (u+1)) (isSC_reg_succ u) (toList x) hc hd
    (ltM_toList x hx hlx)
  intro ac hac hle y hy
  obtain ⟨h1, _, h3, _⟩ := hallOK ac hac
  obtain ⟨k2a, k2c, k3, k5, k4⟩ := H ac hac hle
  have hdT : inT (ddOf75 (reg (u+1)) ac) = true := inT_ddOf75 (inT_reg (u+1)) h1 h3
  by_cases hsd : sub1 (ddOf75 (reg (u+1)) ac) = ddOf75 (reg (u+1)) ac
  · rw [hsd]
    rcases hy with hy | hy
    · rcases k5 with k5 | k5
      · exact lt_of_lt_of_le3 (inT_le_fragR y (inT_mem_Kset75 ac.1 h1 _ y hy))
          (inT_le_fragR _ h1) (inT_le_fragR _ hdT) (k2a y hy) k5
      · exact (k5 y hy).elim
    · exact lt_of_lt_of_le3 (inT_le_fragR y (inT_mem_Kset75 ac.2 h3 _ y hy))
        (inT_le_fragR _ h3) (inT_le_fragR _ hdT) (k2c y hy) k3
  · obtain ⟨e1, e2⟩ := k4 hsd
    rcases hy with hy | hy
    · exact (e1 y hy).elim
    · exact (e2 y hy).elim


/-! ### §75.4b (K2)-(K5) のうち只で来る分

`Kset κ Ω_{u+1} = ∅` と `Kset κ n = ∅` の 2 本だけで、§73.6 が数えた例外のほとんどが
片づく。残りが本当の仕事。 -/

/-- **(K5) の例外の 29/30 はこれ。** 指数が `Ω_{u+1}` ちょうどなら `K` は空。 -/
theorem kset_fst_reg75 {u : Nat} {ac : Term × Term} (h : ac.1 = reg (u+1)) :
    ∀ y, y ∈ Kset (reg (u+1)) ac.1 → False := by
  intro y hy
  rw [h] at hy
  exact mem_Kset_reg (u+1) hy

/-- **(K2) の係数側は、係数が自然数なら空。** -/
theorem kset_snd_ofNat75 {u : Nat} {ac : Term × Term} {n : Nat} (h : ac.2 = ofNat n) :
    ∀ y, y ∈ Kset (reg (u+1)) ac.2 → False := by
  intro y hy
  rw [h] at hy
  exact mem_Kset_ofNat n hy

/-- 只で来る分をまとめた形 — 両方の `K` が空なら局所事実は残り 3 つに落ちる。 -/
theorem localFacts75_of_empty {u : Nat} {ac : Term × Term}
    (h1 : ∀ y, y ∈ Kset (reg (u+1)) ac.1 → False)
    (h2 : ∀ y, y ∈ Kset (reg (u+1)) ac.2 → False)
    (h3 : le ac.2 (ddOf75 (reg (u+1)) ac) = true) : LocalFacts75 u ac :=
  ⟨fun y hy => (h1 y hy).elim, fun y hy => (h2 y hy).elim, h3, Or.inr h1, fun _ => ⟨h1, h2⟩⟩


/-! ### §75.4c 直した分解 — (K2) は §73 の形では偽

§75.6 の否定 4 が測るとおり、§73.7 の (K2) 「`K_{Ω₁} aV < aV`」は**標準な母集団でも
落ちる** (深さ 9 の 284 個の 204 歩のうち 9 歩)。落ちても局所条件は通る。通る理由は
`K_{Ω₁} aV < Δ` の方で、`aV` ではなく `Δ` と比べれば 0 失敗。直した分解は 2 条項で、
(K3)・(K5) は要らなくなる。 -/

/-- **直した局所事実。** (K2') `K aV ∪ K cV < Δ`、(K4) `Δ ⊖ 1 ≠ Δ` なら両方空。 -/
def LocalFacts2_75 (u : Nat) (ac : Term × Term) : Prop :=
  (∀ y, (y ∈ Kset (reg (u+1)) ac.1 ∨ y ∈ Kset (reg (u+1)) ac.2) →
      lt y (ddOf75 (reg (u+1)) ac) = true) ∧
  (sub1 (ddOf75 (reg (u+1)) ac) ≠ ddOf75 (reg (u+1)) ac →
    (∀ y, y ∈ Kset (reg (u+1)) ac.1 → False) ∧ (∀ y, y ∈ Kset (reg (u+1)) ac.2 → False))

/-- **直した分解から局所条件。** `⊖ 1` の始末だけが (K4) の仕事。 -/
theorem localK75_of_facts2_75 (u : Nat) (x : Term)
    (H : ∀ ac ∈ (wcnf (reg (u+1)) (toList x)).1, le (reg (u+1)) ac.1 = true →
      LocalFacts2_75 u ac) : LocalK75 u x := by
  intro ac hac hle y hy
  obtain ⟨k2, k4⟩ := H ac hac hle
  by_cases hsd : sub1 (ddOf75 (reg (u+1)) ac) = ddOf75 (reg (u+1)) ac
  · rw [hsd]; exact k2 y hy
  · obtain ⟨e1, e2⟩ := k4 hsd
    rcases hy with hy | hy
    · exact (e1 y hy).elim
    · exact (e2 y hy).elim

/-- §73 の 4 つからも直した 2 つが出る (逆は出ない — §75.6 の否定 4)。 -/
theorem localFacts2_of_facts75 {u : Nat} {ac : Term × Term}
    (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (H : LocalFacts75 u ac) :
    LocalFacts2_75 u ac := by
  obtain ⟨k2a, k2c, k3, k5, k4⟩ := H
  have hdT : inT (ddOf75 (reg (u+1)) ac) = true := inT_ddOf75 (inT_reg (u+1)) h1 h3
  refine ⟨?_, k4⟩
  intro y hy
  rcases hy with hy | hy
  · rcases k5 with k5 | k5
    · exact lt_of_lt_of_le3 (inT_le_fragR y (inT_mem_Kset75 ac.1 h1 _ y hy))
        (inT_le_fragR _ h1) (inT_le_fragR _ hdT) (k2a y hy) k5
    · exact (k5 y hy).elim
  · exact lt_of_lt_of_le3 (inT_le_fragR y (inT_mem_Kset75 ac.2 h3 _ y hy))
      (inT_le_fragR _ h3) (inT_le_fragR _ hdT) (k2c y hy) k3

/-! ### §75.5 組み立て — 残る門は局所条件ひとつ -/

/-- **§75 の残る仮説。** §73 の `PsiIdxStep073` を、状態を見ない対ごとの条件に
    落としたもの。像が既に 𝔗(M) の項であることは前提に入れてよい (下の帰納法が
    それを供給する)。**証明しない。** -/
def LocalStd75 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true →
    inT (dict a) = true → lt (dict a) M = true → LocalK75 0 (dict a)

/-- 4 つの局所事実の側の形。`localK75_of_facts75` でこちらからも入れる。 -/
def LocalStdFacts75 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true →
    inT (dict a) = true → lt (dict a) M = true →
    ∀ ac ∈ (wcnf (reg 1) (toList (dict a))).1, le (reg 1) ac.1 = true → LocalFacts75 0 ac

/-- **4 つの局所事実からも同じ仮説が出る。** -/
theorem localStd75_of_facts75 (H : LocalStdFacts75) : LocalStd75 :=
  fun a hb h hi hl => localK75_of_facts75 0 (dict a) hi hl (H a hb h hi hl)

/-- 局所条件だけで `dict` の像は 𝔗(M) の中。`u = 1` は §73.4 が閉じている。 -/
theorem inT_dict_of_local75 (H : LocalStd75) : ∀ a : BT, btLe72 1 a = true →
    BT.isStd a = true → inT (dict a) = true ∧ lt (dict a) M = true
  | .zero, _, _ => ⟨inT_zero, lt_zero_M⟩
  | .D u a, hb, h => by
    obtain ⟨hu, hba⟩ := btLe72_D 1 u a hb
    have ih := inT_dict_of_local75 H a hba (isStd_of_D h)
    refine inT_collapse_gap3 u (dict a) ih.1 ih.2
      (psiIdxOK_of_stepOK u (dict a) ih.1 ih.2 ?_)
    cases u with
    | zero => exact ksetStepOK_of_local75 0 (dict a) ih.1 ih.2 (H a hba h ih.1 ih.2)
    | succ u' =>
      cases u' with
      | zero => exact ksetStepOK_one73 a hba
      | succ u'' => exact absurd hu (by omega)
  | .sum a b, hb, h => by
    obtain ⟨hba, hbb⟩ := btLe72_sum 1 a b hb
    have iha := inT_dict_of_local75 H a hba (isStd_of_sum h).1
    have ihb := inT_dict_of_local75 H b hbb (isStd_of_sum h).2
    exact ⟨inT_plus iha.1 ihb.1, lt_plus_M iha.1 ihb.1 iha.2 ihb.2⟩

/-- **§75 の第一の結論。** §73 の残る門は局所条件から出る。 -/
theorem psiIdxStep073_of_local75 (H : LocalStd75) : PsiIdxStep073 := by
  intro a hb h
  have ih := inT_dict_of_local75 H a hb (isStd_of_D h)
  exact ksetStepOK_of_local75 0 (dict a) ih.1 ih.2 (H a hb h ih.1 ih.2)

/-- 4 つの局所事実からも。 -/
theorem psiIdxStep073_of_facts75 (H : LocalStdFacts75) : PsiIdxStep073 :=
  psiIdxStep073_of_local75 (localStd75_of_facts75 H)

/-- 直した 2 条項の側の門。 -/
def LocalStdFacts2_75 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true →
    inT (dict a) = true → lt (dict a) M = true →
    ∀ ac ∈ (wcnf (reg 1) (toList (dict a))).1, le (reg 1) ac.1 = true → LocalFacts2_75 0 ac

theorem localStd75_of_facts2_75 (H : LocalStdFacts2_75) : LocalStd75 :=
  fun a hb h hi hl => localK75_of_facts2_75 0 (dict a) (H a hb h hi hl)

theorem psiIdxStep073_of_facts2_75 (H : LocalStdFacts2_75) : PsiIdxStep073 :=
  psiIdxStep073_of_local75 (localStd75_of_facts2_75 H)

/-- **§75 の第二の結論。** 326 行目の証明書が `K` の側で待っているのは局所条件だけ。 -/
theorem certIn_t326_local75 (H : LocalStd75)
    (HD : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_step73 (psiIdxStep073_of_local75 H) HD HI HC hacc

end

/-! ### §75.6 測定 (凍結)

母集団の作り方を先に書く。**§73 の `hotB73` はこの節には浅すぎる** (否定 1)。

    hotB73  = §73 の 483 個 (`ψ` の入れ子 6 段)
    hotC75  = dg72 hotB73                                   1031 個, 入れ子 7 段
    hotD75  = dg72 hotC75                                   2127 個, 入れ子 8 段
    hotE75  = dg72 hotD75                                   4319 個, 入れ子 9 段
    stdE75  = hotE75 を `BT.isStd (ψ₀ ·)` で絞ったもの         284 個
    seedP75 = (dg72 を 6 回) を主要項に絞ったもの            126 個, 入れ子 6 段
    wide2_75 = seedP75 の 2 項和すべて                     15876 個, 入れ子 6 段
      (dg72 l = l ++ {ψ₀a, ψ₁a : a ∈ l} は §72 のもの。`isStd` では絞らずに作る。)
    wStep75 = ψ₁ψ₁ψ₁ψ₀ψ₁ψ₁ψ₁ψ₁0                   節 9 個, 入れ子 8 段

`wide2_75` は「前の指数を持つ歩」(`plus i0 Δ` の枝 — §75.2 が閉じたもの) を稼ぐために
入れた。§73 の母集団ではその歩は 120 歩中 **1 歩**しかなく、枝が空回りして見えていた。 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

def hotC75 : List BT := dg72 hotB73
def hotD75 : List BT := dg72 hotC75
def hotE75 : List BT := dg72 hotD75
def stdE75 : List BT := hotE75.filter fun a => BT.isStd (BT.D 0 a)
/-- 段 1 以下・`ψ` の入れ子 8 段。`BT.isStd` は `ψ₀` を被せたところで落ちる。 -/
def wStep75 : BT :=
  BT.D 1 (BT.D 1 (BT.D 1 (BT.D 0 (BT.D 1 (BT.D 1 (BT.D 1 (BT.D 1 BT.zero)))))))

-- 母集団の大きさ。
#guard hotC75.length == 1031
#guard hotD75.length == 2127
#guard hotD75.all (btLe72 1)

/-! **否定 1 — §73 の母集団はこの節には浅すぎる。`u = 0` の門は `BT.isStd` なしでは偽。**
§73 の `hotB73` (入れ子 6 段) では `stepOKb 0 (dict a)` が一度も落ちず、門が仮説なしで
成り立つように見える。入れ子を 8 段にすると 2127 個のうち **16 個**で落ちる。16 個は
どれも `BT.isStd (ψ₀ ·)` が偽で、`BT.isStd` を課すと 0 個。**§73 の「肯定 2」は
母集団が一段浅かった。** -/

#guard (hotB73.filter fun a => !(stepOKb 0 (dict a))).length == 0
#guard (hotD75.filter fun a => !(stepOKb 0 (dict a))).length == 16
#guard (hotD75.filter fun a => BT.isStd (BT.D 0 a) && !(stepOKb 0 (dict a))).length == 0
#guard ((hotD75.filter fun a => !(stepOKb 0 (dict a))).all
  fun a => BT.isStd (BT.D 0 a) == false)
#guard ((hotD75.filter fun a => !(stepOKb 0 (dict a))).all fun a => BT.size a >= 9)

/-- **否定 1、定理の形。** 段 1 以下で、`BT` そのものは Buchholz 標準なのに `ψ₀` を
    被せると標準でなくなる項があり、そこで残る門は破れる。§73 の `btPool72`・`hotB73`
    のどちらにも入っていない。 -/
theorem not_ksetStepOK_wStep75 :
    btLe72 1 wStep75 = true ∧ BT.isStd wStep75 = true ∧
    BT.isStd (BT.D 0 wStep75) = false ∧ ¬ KsetStepOK 0 (dict wStep75) := by
  refine ⟨by decide, by decide, by decide, fun H => ?_⟩
  exact Bool.noConfusion ((stepOKb_of_ksetStepOK H).symm.trans
    (show stepOKb 0 (dict wStep75) = false from by decide))

/-! **否定 2 — 局所条件も同じところで落ちる、そしてそこだけで落ちる。**
`localOKb73 0 ·` が落ちる 16 個は `stepOKb 0 ·` が落ちる 16 個とちょうど同じ。
つまり §75.3 の還元はこの母集団では**損をしていない** — 門が通るのに局所条件が
落ちる項は一つも無い。 -/

#guard (hotD75.filter fun a => !(localOKb73 0 (dict a))) ==
  (hotD75.filter fun a => !(stepOKb 0 (dict a)))
#guard (hotD75.filter fun a => stepOKb 0 (dict a) && !(localOKb73 0 (dict a))).length == 0
#guard (hotC75.filter fun a => stepOKb 0 (dict a) && !(localOKb73 0 (dict a))).length == 0
#guard !(localOKb73 0 (dict wStep75))

/-! **否定 3 — 移送 `K_{Ω₁}(dict a) < dict a` は入れ子 8 段でも `isStd` で 0 失敗。**
§73 の否定 3 (`hotB73` で 483 個中 79 個) は深くしても同じ形で残る。 -/

#guard (hotD75.filter fun a => !(KOK73 (dict a))).length == 653
#guard (hotD75.filter fun a => BT.isStd (BT.D 0 a) && !(KOK73 (dict a))).length == 0

/-! **肯定 1 — 局所条件は空回りしていない。** `hotD75` の 325 歩の発火のうち、
67 歩で `K_{Ω₁} aV` が、3 歩で `K_{Ω₁} cV` が空でない。 -/

#guard (hotD75.flatMap fires73).length == 325
#guard ((hotD75.flatMap fires73).filter fun p => !((Kset (reg 1) p.2.1).isEmpty)).length == 67
#guard ((hotD75.flatMap fires73).filter fun p => !((Kset (reg 1) p.2.2).isEmpty)).length == 3


/-! **否定 4 — §73.7 の (K2) は「標準」を課しても偽。** `hotE75 = dg72 hotD75`
(`ψ` の入れ子 9 段、4319 個) を `BT.isStd (ψ₀ ·)` で絞ると 284 個、その発火は 204 歩。
そのうち **9 歩**で (K2) の `K_{Ω₁} aV < aV` が落ちる (`K_{Ω₁} cV < cV` の方は 0 歩)。
§73.6 は 120 歩で 0 失敗と測って「(K2) が成り立つ」と書いたが、母集団が浅かった。
**それでも局所条件は 204 歩すべてで通る。** 通る理由は `aV` ではなく `Δ` と比べる
からで、`K_{Ω₁} aV ∪ K_{Ω₁} cV < Δ` は 204 歩で 0 失敗。§75.4c の直した分解
(K2')+(K4) はこの測定に合わせたもので、(K3)・(K5) は要らなくなる。 -/

#guard hotE75.length == 4319
#guard (hotE75.filter fun a => !(stepOKb 0 (dict a))).length == 61
#guard (hotE75.filter fun a => BT.isStd (BT.D 0 a) && !(stepOKb 0 (dict a))).length == 0
#guard stdE75.length == 284
#guard (stdE75.flatMap fires73).length == 204
#guard ((stdE75.flatMap fires73).filter fun p => !(KOK73 p.2.1)).length == 9
#guard ((stdE75.flatMap fires73).filter fun p => !(KOK73 p.2.2)).length == 0
#guard ((stdE75.flatMap fires73).filter fun p =>
  !((Kset (reg 1) p.2.1 ++ Kset (reg 1) p.2.2).all fun y => lt y (dd73 p))).length == 0
#guard (stdE75.filter fun a => !(localOKb73 0 (dict a))).length == 0
#guard (stdE75.filter fun a => !(stepOKb 0 (dict a))).length == 0


/-- **否定 4、定理の形。** `kBad75 = ψ₁ wStep75` は段 1 以下で `ψ₀` を被せても Buchholz
    標準、門も局所条件も通る。それでも発火の一歩で §73.7 の (K2) `K_{Ω₁} aV < aV` が
    落ちる。**§73 の分解はこの形では使えない。** 直した (K2') は落ちない。 -/
def kBad75 : BT := BT.D 1 wStep75

theorem not_k2_kBad75 :
    btLe72 1 kBad75 = true ∧ BT.isStd (BT.D 0 kBad75) = true ∧
    stepOKb 0 (dict kBad75) = true ∧ localOKb73 0 (dict kBad75) = true ∧
    ((fires73 kBad75).any fun p => !(KOK73 p.2.1)) = true ∧
    ((fires73 kBad75).all fun p =>
      (Kset (reg 1) p.2.1 ++ Kset (reg 1) p.2.2).all fun y => lt y (dd73 p)) = true := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! **肯定 3 — (K3) と (K4) は測ったかぎり無条件。証明はしていない。**
`hotD75` の 325 歩で `cV ≤ Δ` は 0 失敗、`Δ ⊖ 1 ≠ Δ` の 27 歩ではどちらの `K` も空、
`aV ≰ Δ` の 31 歩のうち 30 歩は `aV = Ω₁` (そこは `kset_fst_reg75` が只で片づける) で、
残り 1 歩も `K aV` が空。 -/

#guard ((hotD75.flatMap fires73).filter fun p => !(le p.2.2 (dd73 p))).length == 0
#guard ((hotD75.flatMap fires73).filter fun p => sub1 (dd73 p) != dd73 p).length == 27
#guard ((hotD75.flatMap fires73).filter fun p => sub1 (dd73 p) != dd73 p &&
  !((Kset (reg 1) p.2.1 ++ Kset (reg 1) p.2.2).isEmpty)).length == 0
#guard ((hotD75.flatMap fires73).filter fun p => !(le p.2.1 (dd73 p))).length == 31
#guard ((hotD75.flatMap fires73).filter fun p =>
  !(le p.2.1 (dd73 p)) && p.2.1 == reg 1).length == 30
#guard ((hotD75.flatMap fires73).filter fun p => !(le p.2.1 (dd73 p)) && p.2.1 != reg 1 &&
  !((Kset (reg 1) p.2.1).isEmpty)).length == 0

/-! (K3) の裏にある補題 `omegaNF (logOm p) = p` は `lt p M` を落とすと**偽**。
`ω̄^(M ⊕ 1)` で `ω̄^(ω̄^(M ⊕ 1))` になる。段 1 以下の像には `ω̄^·` が出ない
(§73.3 の `lt_M_pure73`) ので、そこでは効いていない。 -/

#guard inT (omg (add M TM.Term.one)) && (omg (add M TM.Term.one)).isAP
#guard !(lt (omg (add M TM.Term.one)) M)
#guard !(omegaNF (logOm (omg (add M TM.Term.one))) == omg (add M TM.Term.one))

/-- **肯定 2 — §73 が「`K` が空だから通るのではない」と言った項で、§75.3 の道が通る。**
    `aBad73` の発火の係数は `Γ₀` で `K_{Ω₁} Γ₀ = {0}`。局所条件を経由して門が出る。 -/
theorem ksetStepOK_aBad73_75 : KsetStepOK 0 (dict aBad73) :=
  ksetStepOK_of_local75 0 (dict aBad73) (by decide) (by decide) (localK75_of_b (by decide))

/-- 同じ道で 2.1(vi) の `K` の連言も出る。 -/
theorem ksetIdxOK_aBad73_75 : KsetIdxOK 0 (dict aBad73) :=
  ksetIdxOK_of_stepOK 0 (dict aBad73) ksetStepOK_aBad73_75

end

/-! ### §75.7 公理 -/

/-! ## §77 THE SUM SIDE OF `DictLtA74` IS A THEOREM — ONE HEAD COMPARISON IS ALL THAT IS LEFT

§76 cut row 326's certificate down to four named hypotheses, and one of them is
`Trans/Dict.lean`'s acceptance record item (C) verbatim:

    DictLtA74 : ∀ u t, stdB1 u → stdB1 t →
                BT.lt (bValA71 u) (bValA71 t) → lt (dict (bValA71 u)) (dict (bValA71 t))

§76 closed the two BOTTOM cases of its induction (`dictLt_zero76`, `dictLt_D0_zero76`) and said
in as many words what was left: "the general head comparison, `ψ_u(α)` against `ψ_v(β)`
lexicographically in `(u, α)`, is untouched, and so is the sum-level induction that would need
it".  **§77 closes the sum-level induction, and the transfer from the index side.**  The head
comparison is NOT proved.  It is isolated as one named hypothesis, split into its two halves,
and each half measured — including a negative result that says which side condition each half
actually needs.

WHAT IS PROVED.

  §77.1  **A STANDARD `BT` TERM IS ITS COMPONENT LIST.**  `ofL_toL77` (`BT.ofL ∘ BT.toL = id` on
         `BT.isStd`), `good_toL77` (the components are principal, standard, level-bounded and
         DESCENDING — `descOK72`, §72's predicate), and `bt_beq_eq77` (`BT`'s derived `BEq` is
         equality, which `BT.ltL`'s `a == b` branch needs and which `deriving BEq` does not
         hand over).  `isStd_ofL72` (§72) is the converse and is reused as is.

  §77.2  **TWO LIFTING LEMMAS ON THE 𝔗(M) SIDE.**  §65's `lt_of_hd_lt` already says that a
         strictly smaller leading component decides `<` between two sums.  `lt_of_hd_eq77` is
         its missing twin: an EQUAL leading component hands the decision to the tails.  Between
         them they cover every branch of [Rathjen, 1991] 2.3.16 that the induction reaches.

  §77.3  **THE DESCENDING TRANSFER.**  `toList_dict_ofL77` : for a good component list `l`,
         `toList (dict (BT.ofL l)) = l.map dict` — the image of a formal sum has exactly the
         images of the components, in the same order, and NOTHING is absorbed.  This is the
         one place where `descOK72` is spent: `plus` filters away every component of its left
         argument that is below the head of its right argument, so without the descending
         condition the leading `dict` component disappears (`plus one α = α`, §76).  The
         transfer needs the head comparison for the pair `(component i+1, component i)`, which
         is why it lives INSIDE the induction, as `dictLe_atom77` under a `DictLtUpTo77 m`
         hypothesis rather than as a standalone lemma.

  §77.4  **THE SUM-LEVEL INDUCTION.**  `dictLtUpTo_all77` / `dictLt_of_head77` :

             DictHeadLt77 → ∀ x y, btLe72 1 x → btLe72 1 y → BT.isStd x → BT.isStd y →
                            BT.lt x y = true → lt (dict x) (dict y) = true

         The induction is on the SUM of the component sizes, with `BT.ltL`'s fuel universally
         quantified — that is what makes it go through without a fuel-adequacy lemma, because
         `BT.ltL`'s two recursive calls (into the tails, and into the ARGUMENTS of a common
         head) both shrink the measure while carrying whatever fuel they were handed.

  §77.5  **THE HEAD SPLIT.**  `DictCross77` (different subscripts: `ψ₀(α) < ψ₁(β)`) and
         `CollapseMono77` (equal subscripts: `collapse u` preserves the order of the argument's
         image).  `dictHeadLt_of_split77` puts them back together.

  §77.6  **THE INDEX SIDE TRANSFERS UNCONDITIONALLY.**  `stdA77` and `btLeA77` :
         `BT.isStd (bValA71 t)` and `btLe72 1 (bValA71 t)` for every `stdB1 t`.  §72 proved the
         first only for `bVal`, which drops the leading `(0, nil)` node; the measurement here
         says the `dropHd72` was never needed for standardness — `nonIncrL` holds of the whole
         list — and `descOK_map72` applies to `toL t` unchanged.  Hence

             dictLtA74_of_head77 : PsiIdxOKStd172 → DictHeadLt77 → DictLtA74

         and with §76, `vOfLtA71_of_head77`, `limDecS1_77`, `limIncS1_77`, `certIn_t326_head77`.

  §77.7  **`ψ₁(α) = ω^(Ω₁ + α)`, AND `ψ₀(α) = ω^α` FOR `α < Ω₁`.**  `collapse1_eq77` and
         `collapse0_eq77` — clause (D1) of `Trans/Dict.lean`'s header, which that file states
         only as `#guard`s.  At level one `wcnf` never splits (§73's `lt_pure73_reg2`), so the
         whole fold is the empty fold and `collapse` is a single `ω^·`.

  §77.8  **THE RESIDUAL, SHARPENED, AND ONE HALF OF IT REDUCED TO A KNOWN GAP.**
         `dictCross_of01_77` : the level bound forces `u = 0` and `v = 1`, so `DictCross77` is
         ONE inequality, `ψ₀(α) < ψ₁(β)`.  `collapseMono_of_split77` splits `CollapseMono77` at
         `u`, and `collapseMono1_of77` rewrites the `u = 1` half through §77.7 into
         `OmPlusMono77` — `α < β ⟹ ω^(Ω₁+α) < ω^(Ω₁+β)`.  `le_collapse1_77` then proves that
         half **non-strictly**, by §65.4's `plus_mono_right_inT` into §65.3's
         `omegaNF_mono_inT`; what is missing is exactly the STRICTNESS of `ω^·` on 𝔗(M), i.e.
         the 𝔗(M) analogue of `CNVOps` §29's D3 (`dnFacts`), which §65.3 deliberately avoided
         because `le` was all its consumers needed.  The `u = 0` half is the Veblen-and-`ψ_{Z0}`
         fold and is left as it stands.

WHAT IS **NOT** CLAIMED.  `DictHeadLt77` is NOT proved, in either half — `le_collapse1_77`
gets the `u = 1` half only up to `≤`, and the gap to `<` is a named one (§77.8).  Nothing here proves
`PsiIdxOKStd172`, `CofDenseS1` or `BCofIn71`, and `dict`'s order-preservation therefore remains
what `Trans/Dict.lean` always said it was: a `#guard`ed goal.  What has changed is its shape —
the sum, the descending condition, and the whole index side are gone from the statement.

WHAT THE MEASUREMENT SAYS (§77.9 gives the construction).  **The negative results first.**

  * **`BT.isStd` is not optional and the level bound is not what buys the order.**  On the
    level-bounded but NOT standard population (24 terms, 576 pairs) `dict` inverts 35 pairs.
    On the standard but NOT level-bounded population (71 terms, 5041 pairs) it inverts NONE.
    So §77's `btLe72 1` hypothesis is spent entirely on `inT (dict ·)` — it is what makes
    `PsiIdxOKStd172` applicable — and not on the order at all.  §76's opposite-looking finding
    ("`DictLtA74` is FALSE once the level bound is dropped") is about the INDEX side, where
    dropping the bound also drops `BT.isStd (bValA71 ·)`.
  * **`CollapseMono77`'s side condition is the `K`-condition, not `isStd` of the argument.**
    With `BT.isStd (BT.D 0 ·)` demanded of both sides — i.e. with `G(α,0) < α` — `collapse 0`
    inverts 0 pairs.  With it dropped but the arguments still standard and level-bounded, it
    inverts 28.  `collapse 1` inverts 0 either way, which is §77.7 showing: at level one the
    map is just `ω^(Ω₁+·)`.
  * **The descending transfer really does fail without `descOK72`.**  `toList (dict (BT.ofL l))
    = l.map dict` holds for all 19 good terms and fails for 4 of the 24 level-bounded ones.

  The positive side.  The statement itself holds on 361 good pairs, the head hypothesis holds
  on all principal pairs among them, and `stdA77`/`btLeA77` — now theorems — hold on `subP 6`
  (160 indices) and `subP 7` (609 indices).
-/

/-! ### §77.1 標準な `BT` 項と成分列 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- 成分列の大きさの和 — 外側の帰納法の測度。 -/
def szL77 : List BT → Nat
  | [] => 0
  | p :: l => BT.size p + szL77 l

theorem szL77_append : ∀ (l1 l2 : List BT), szL77 (l1 ++ l2) = szL77 l1 + szL77 l2
  | [], l2 => by show szL77 l2 = 0 + szL77 l2; omega
  | p :: l, l2 => by
      show BT.size p + szL77 (l ++ l2) = BT.size p + szL77 l + szL77 l2
      rw [szL77_append l l2]; omega

theorem size_pos77 : ∀ t : BT, 1 ≤ BT.size t
  | .zero => Nat.le_refl 1
  | .D _ a => by have h := size_pos77 a; show 1 ≤ 1 + BT.size a; omega
  | .sum a b => by
      have h1 := size_pos77 a; have h2 := size_pos77 b
      show 1 ≤ 1 + BT.size a + BT.size b; omega

theorem szL77_toL : ∀ t : BT, szL77 (BT.toL t) ≤ BT.size t
  | .zero => Nat.zero_le _
  | .D u a => by show BT.size (BT.D u a) + 0 ≤ BT.size (BT.D u a); omega
  | .sum a b => by
      have h1 := szL77_toL a; have h2 := szL77_toL b
      show szL77 (BT.toL a ++ BT.toL b) ≤ 1 + BT.size a + BT.size b
      rw [szL77_append]; omega

/-- `BT` の `==` は等号。`deriving BEq` の構造的比較を一度だけ開く。 -/
theorem bt_beq_eq77 : ∀ {a b : BT}, (a == b) = true → a = b := by
  intro a
  induction a with
  | zero =>
      intro b h
      cases b with
      | zero => rfl
      | D _ _ => exact Bool.noConfusion h
      | sum _ _ => exact Bool.noConfusion h
  | D u a ih =>
      intro b h
      cases b with
      | zero => exact Bool.noConfusion h
      | D v c =>
          have h' : (u == v && (a == c)) = true := h
          obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h'
          rw [eq_of_beq h1, ih h2]
      | sum _ _ => exact Bool.noConfusion h
  | sum a b iha ihb =>
      intro c h
      cases c with
      | zero => exact Bool.noConfusion h
      | D _ _ => exact Bool.noConfusion h
      | sum c d =>
          have h' : ((a == c) && (b == d)) = true := h
          obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h'
          rw [iha h1, ihb h2]

/-- 形式和の先頭成分。 -/
def bhd77 : BT → BT
  | .sum a _ => bhd77 a
  | t => t

theorem bhd77_of_isP {t : BT} (h : BT.isP t = true) : bhd77 t = t := by
  cases t with
  | zero => exact Bool.noConfusion h
  | D _ _ => rfl
  | sum _ _ => exact Bool.noConfusion h

theorem isP_of_isStd_sum {a b : BT} (h : BT.isStd (BT.sum a b) = true) : BT.isP a = true := by
  obtain ⟨h1, _⟩ := (Bool.and_eq_true _ _).mp h
  obtain ⟨h2, _⟩ := (Bool.and_eq_true _ _).mp h1
  exact ((Bool.and_eq_true _ _).mp h2).1

theorem isStd_sum_ne_zero77 {a b : BT} (h : BT.isStd (BT.sum a b) = true) : b ≠ BT.zero := by
  intro hb
  subst hb
  obtain ⟨_, h2⟩ := (Bool.and_eq_true _ _).mp h
  exact Bool.noConfusion h2

theorem toL_cons77 : ∀ (b : BT), BT.isStd b = true → b ≠ BT.zero →
    ∃ r, BT.toL b = bhd77 b :: r
  | .zero, _, hz => absurd rfl hz
  | .D _ _, _, _ => ⟨[], rfl⟩
  | .sum c d, hs, _ => by
      have hP : BT.isP c = true := isP_of_isStd_sum hs
      cases c with
      | zero => exact Bool.noConfusion hP
      | sum _ _ => exact Bool.noConfusion hP
      | D v e => exact ⟨BT.toL d, rfl⟩

theorem le_bhd77 {a b : BT} (h : BT.isStd (BT.sum a b) = true) : BT.le (bhd77 b) a = true := by
  cases b with
  | zero => exact absurd rfl (isStd_sum_ne_zero77 h)
  | D v d =>
      obtain ⟨_, h2⟩ := (Bool.and_eq_true _ _).mp h
      exact ((Bool.and_eq_true _ _).mp h2).2
  | sum c d =>
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
      have hsc : BT.isStd (BT.sum c d) = true := ((Bool.and_eq_true _ _).mp h1).2
      rw [show bhd77 (BT.sum c d) = bhd77 c from rfl, bhd77_of_isP (isP_of_isStd_sum hsc)]
      exact h2

/-- 標準な項は成分列から組み直せる。 -/
theorem ofL_toL77 : ∀ (x : BT), BT.isStd x = true → BT.ofL (BT.toL x) = x
  | .zero, _ => rfl
  | .D _ _, _ => rfl
  | .sum a b, hs => by
      have hP : BT.isP a = true := isP_of_isStd_sum hs
      obtain ⟨h1, _⟩ := (Bool.and_eq_true _ _).mp hs
      have hsb : BT.isStd b = true := ((Bool.and_eq_true _ _).mp h1).2
      obtain ⟨r, hr⟩ := toL_cons77 b hsb (isStd_sum_ne_zero77 hs)
      have hne : BT.toL b ≠ [] := by rw [hr]; exact List.cons_ne_nil _ _
      cases a with
      | zero => exact Bool.noConfusion hP
      | sum _ _ => exact Bool.noConfusion hP
      | D v e =>
          show BT.ofL (BT.D v e :: BT.toL b) = BT.sum (BT.D v e) b
          rw [ofL_cons_ne _ _ hne, ofL_toL77 b hsb]

/-- 成分列の「良さ」— 成分は主要・標準・段 1 以下で、降べき。 -/
def GoodL77 (l : List BT) : Prop :=
  Atoms l ∧ (∀ x ∈ l, BT.isStd x = true) ∧ (∀ x ∈ l, btLe72 1 x = true) ∧ descOK72 l = true

theorem goodL77_nil : GoodL77 ([] : List BT) := by
  refine ⟨?_, ?_, ?_, rfl⟩ <;> (intro z hz; cases hz)

theorem descOK72_tail {p : BT} {l : List BT} (h : descOK72 (p :: l) = true) :
    descOK72 l = true := by
  cases l with
  | nil => rfl
  | cons q r => exact ((Bool.and_eq_true _ _).mp h).2

theorem goodL77_tail {p : BT} {l : List BT} (h : GoodL77 (p :: l)) : GoodL77 l :=
  ⟨fun z hz => h.1 z (List.Mem.tail _ hz), fun z hz => h.2.1 z (List.Mem.tail _ hz),
    fun z hz => h.2.2.1 z (List.Mem.tail _ hz), descOK72_tail h.2.2.2⟩

theorem good_toL77 : ∀ (x : BT), BT.isStd x = true → btLe72 1 x = true → GoodL77 (BT.toL x)
  | .zero, _, _ => goodL77_nil
  | .D u a, hs, hb => by
      refine ⟨?_, ?_, ?_, rfl⟩
      · intro z hz; rw [List.mem_singleton.mp hz]; exact ⟨u, a, rfl⟩
      · intro z hz; rw [List.mem_singleton.mp hz]; exact hs
      · intro z hz; rw [List.mem_singleton.mp hz]; exact hb
  | .sum a b, hs, hb => by
      have hP : BT.isP a = true := isP_of_isStd_sum hs
      obtain ⟨h1, _⟩ := (Bool.and_eq_true _ _).mp hs
      have hsa : BT.isStd a = true := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h1).1).2
      have hsb : BT.isStd b = true := ((Bool.and_eq_true _ _).mp h1).2
      obtain ⟨hba, hbb⟩ := btLe72_sum 1 a b hb
      have ihb := good_toL77 b hsb hbb
      obtain ⟨r, hr⟩ := toL_cons77 b hsb (isStd_sum_ne_zero77 hs)
      cases a with
      | zero => exact Bool.noConfusion hP
      | sum _ _ => exact Bool.noConfusion hP
      | D v e =>
          show GoodL77 (BT.D v e :: BT.toL b)
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro z hz
            rcases List.mem_cons.mp hz with h | h
            · exact ⟨v, e, h⟩
            · exact ihb.1 z h
          · intro z hz
            rcases List.mem_cons.mp hz with h | h
            · rw [h]; exact hsa
            · exact ihb.2.1 z h
          · intro z hz
            rcases List.mem_cons.mp hz with h | h
            · rw [h]; exact hba
            · exact ihb.2.2.1 z h
          · have hd : descOK72 (BT.toL b) = true := ihb.2.2.2
            rw [hr] at hd ⊢
            show (BT.le (bhd77 b) (BT.D v e) && descOK72 (bhd77 b :: r)) = true
            rw [le_bhd77 hs, hd]
            rfl

theorem isStd_ofL77 {l : List BT} (h : GoodL77 l) : BT.isStd (BT.ofL l) = true :=
  isStd_ofL72 l h.1 h.2.1 h.2.2.2

theorem btLe_ofL77 {l : List BT} (h : GoodL77 l) : btLe72 1 (BT.ofL l) = true :=
  btLe72_ofL72 l h.2.2.1

theorem ofL_ne_zero77 {p : BT} {l : List BT} (h : ∃ u a, p = BT.D u a) :
    BT.ofL (p :: l) ≠ BT.zero := by
  obtain ⟨u, a, rfl⟩ := h
  cases l with
  | nil => intro hc; exact BT.noConfusion hc
  | cons q r =>
      rw [ofL_cons_ne _ _ (List.cons_ne_nil q r)]
      intro hc; exact BT.noConfusion hc

/-! ### §77.2 𝔗(M) 側の持ち上げ — 先頭が決めるか、先頭が同じか -/

theorem isAtom_of_isAP77 {t : Term} (h : t.isAP = true) : isAtom t = true := by
  cases t with
  | zero => exact Bool.noConfusion h
  | add _ _ => exact Bool.noConfusion h
  | M => rfl
  | omg _ => rfl
  | phi _ _ => rfl
  | psi _ _ => rfl
  | Z _ => rfl

theorem le_self77 (c : Term) : le c c = true := by
  show (c == c || lt c c) = true
  rw [beq_self_eq_true]
  rfl

theorem lt_hd_self77 {c Y0 : Term} (hc : c.isAP = true) : lt c (add c Y0) = true := by
  rw [lt_atom_add (isAtom_of_isAP77 hc)]
  exact le_self77 c

theorem lt_add_tail77 {A X0 Y0 : Term} (h : lt X0 Y0 = true) :
    lt (add A X0) (add A Y0) = true := by
  have hne : X0 ≠ Y0 := by
    intro hc; rw [hc, lt_irrefl] at h; exact Bool.noConfusion h
  rw [lt_add_add (by intro hc; injection hc with _ h2; exact hne h2), if_pos rfl]
  exact h

/-- **先頭が同じなら尾部が決める。** `lt_of_hd_lt` の等号版。 -/
theorem lt_of_hd_eq77 {e y c : Term} {E' Y' : List Term} (he : inT e = true) (hy : inT y = true)
    (hE : toList e = c :: E') (hY : toList y = c :: Y')
    (h : lt (ofList E') (ofList Y') = true) : lt e y = true := by
  have hcAP : c.isAP = true := inTL_isAP he c (by rw [hE]; exact List.Mem.head _)
  have hee : e = ofList (c :: E') := by rw [← hE, inT_ofList_toList e he]
  have hye : y = ofList (c :: Y') := by rw [← hY, inT_ofList_toList y hy]
  cases E' with
  | nil =>
      cases Y' with
      | nil =>
          rw [show ofList ([] : List Term) = zero from rfl,
            show lt zero zero = false from lt_irrefl zero] at h
          exact Bool.noConfusion h
      | cons d D =>
          rw [hee, hye]
          show lt c (add c (ofList (d :: D))) = true
          exact lt_hd_self77 hcAP
  | cons g G =>
      cases Y' with
      | nil =>
          rw [show ofList ([] : List Term) = zero from rfl,
            show lt (ofList (g :: G)) zero = false from ltF_right_zero _ _] at h
          exact Bool.noConfusion h
      | cons d D =>
          rw [hee, hye]
          show lt (add c (ofList (g :: G))) (add c (ofList (d :: D))) = true
          exact lt_add_tail77 h

/-! ### §77.3 帰納法の中で使う二つの補助 -/

/-- 大きさ `m` までの成分列で `dict` が `BT.ltL` を保つ、という主張。 -/
def DictLtUpTo77 (m : Nat) : Prop :=
  ∀ (f : Nat) (l1 l2 : List BT), szL77 l1 + szL77 l2 ≤ m → GoodL77 l1 → GoodL77 l2 →
    BT.ltL f l1 l2 = true → lt (dict (BT.ofL l1)) (dict (BT.ofL l2)) = true

theorem ltL_zero77 (l1 l2 : List BT) : BT.ltL 0 l1 l2 = false := rfl

theorem ltL_nil_nil77 (f : Nat) : BT.ltL f ([] : List BT) [] = false := by
  cases f with
  | zero => rfl
  | succ _ => rfl

theorem ltL_cons_nil77 (f : Nat) (p : BT) (l : List BT) : BT.ltL f (p :: l) [] = false := by
  cases f with
  | zero => rfl
  | succ _ => rfl

theorem goodL77_single77 {c : BT} (hc : ∃ u x, c = BT.D u x) (hsc : BT.isStd c = true)
    (hbc : btLe72 1 c = true) : GoodL77 [c] :=
  ⟨by intro z hz; rw [List.mem_singleton.mp hz]; exact hc,
   by intro z hz; rw [List.mem_singleton.mp hz]; exact hsc,
   by intro z hz; rw [List.mem_singleton.mp hz]; exact hbc, rfl⟩

/-- **降べきの移送。** `BT` の側の `≤` が像の `≤` になる。帰納法の内側でだけ使う。 -/
theorem dictLe_atom77 {m : Nat} (HQ : DictLtUpTo77 m) {c a : BT}
    (hc : ∃ u x, c = BT.D u x) (ha : ∃ v y, a = BT.D v y)
    (hsc : BT.isStd c = true) (hsa : BT.isStd a = true)
    (hbc : btLe72 1 c = true) (hba : btLe72 1 a = true)
    (hsz : BT.size c + BT.size a ≤ m)
    (h : BT.le c a = true) : le (dict c) (dict a) = true := by
  rcases (Bool.or_eq_true _ _).mp h with h1 | h1
  · rw [bt_beq_eq77 h1]
    exact le_self77 _
  · have g1 : GoodL77 [c] := goodL77_single77 hc hsc hbc
    have g2 : GoodL77 [a] := goodL77_single77 ha hsa hba
    obtain ⟨u, x, rfl⟩ := hc
    obtain ⟨v, y, rfl⟩ := ha
    exact le_of_lt (HQ (BT.size (BT.D u x) + BT.size (BT.D v y) + 2)
      [BT.D u x] [BT.D v y]
      (by show BT.size (BT.D u x) + 0 + (BT.size (BT.D v y) + 0) ≤ m; omega) g1 g2 h1)

/-- **良い成分列の像の成分列は像の並び。** 先頭が消えないことがここの内容で、
    それは §77.1 の降べきと `dictLe_atom77` が支えている。 -/
theorem toList_dict_ofL77 (Hp : PsiIdxOKStd172) {m : Nat} (HQ : DictLtUpTo77 m) :
    ∀ (l : List BT), GoodL77 l → szL77 l ≤ m → toList (dict (BT.ofL l)) = l.map dict
  | [], _, _ => rfl
  | [p], hg, _ => by
      obtain ⟨u, a, rfl⟩ := hg.1 p (List.Mem.head _)
      show toList (dict (BT.D u a)) = [dict (BT.D u a)]
      exact toList_of_isAP (isAP_dict_D76 u a)
  | p :: q :: r, hg, hsz => by
      obtain ⟨u, a, rfl⟩ := hg.1 p (List.Mem.head _)
      obtain ⟨v, b, rfl⟩ := hg.1 q (List.Mem.tail _ (List.Mem.head _))
      have hgt : GoodL77 (BT.D v b :: r) := goodL77_tail hg
      have he1 : szL77 (BT.D u a :: BT.D v b :: r)
          = BT.size (BT.D u a) + (BT.size (BT.D v b) + szL77 r) := rfl
      have hp1 := size_pos77 (BT.D u a)
      have hp2 := size_pos77 (BT.D v b)
      have hsz1 : szL77 (BT.D v b :: r) ≤ m := by
        have he2 : szL77 (BT.D v b :: r) = BT.size (BT.D v b) + szL77 r := rfl
        omega
      have ih : toList (dict (BT.ofL (BT.D v b :: r)))
          = dict (BT.D v b) :: r.map dict := toList_dict_ofL77 Hp HQ (BT.D v b :: r) hgt hsz1
      have hiP : inT (dict (BT.D u a)) = true :=
        (inT_dict_of_std172 Hp (BT.D u a) (hg.2.2.1 _ (List.Mem.head _))
          (hg.2.1 _ (List.Mem.head _))).1
      have hiT : inT (dict (BT.ofL (BT.D v b :: r))) = true :=
        (inT_dict_of_std172 Hp _ (btLe_ofL77 hgt) (isStd_ofL77 hgt)).1
      have hle : le (dict (BT.D v b)) (dict (BT.D u a)) = true :=
        dictLe_atom77 HQ ⟨v, b, rfl⟩ ⟨u, a, rfl⟩
          (hg.2.1 _ (List.Mem.tail _ (List.Mem.head _))) (hg.2.1 _ (List.Mem.head _))
          (hg.2.2.1 _ (List.Mem.tail _ (List.Mem.head _))) (hg.2.2.1 _ (List.Mem.head _))
          (by omega) ((Bool.and_eq_true _ _).mp hg.2.2.2).1
      have hfil : List.filter (fun z => le (dict (BT.D v b)) z) [dict (BT.D u a)]
          = [dict (BT.D u a)] := by
        show (match le (dict (BT.D v b)) (dict (BT.D u a)) with
              | true => dict (BT.D u a) :: List.filter (fun z => le (dict (BT.D v b)) z) []
              | false => List.filter (fun z => le (dict (BT.D v b)) z) []) = _
        rw [hle]
        rfl
      show toList (dict (BT.sum (BT.D u a) (BT.ofL (BT.D v b :: r)))) = _
      rw [Trans.Dict.dict_sum, toList_plus_inT hiP hiT ih,
        toList_of_isAP (isAP_dict_D76 u a), hfil, ih]
      rfl

/-- 良い成分列の `ofList`。 -/
theorem ofList_map_dict77 (Hp : PsiIdxOKStd172) {m : Nat} (HQ : DictLtUpTo77 m)
    (l : List BT) (hg : GoodL77 l) (hsz : szL77 l ≤ m) :
    ofList (l.map dict) = dict (BT.ofL l) := by
  rw [← toList_dict_ofL77 Hp HQ l hg hsz,
    inT_ofList_toList _ (inT_dict_of_std172 Hp _ (btLe_ofL77 hg) (isStd_ofL77 hg)).1]

/-! ### §77.4 和の帰納法 — 頭部の比較だけを残す -/

/-- **頭部の比較。** `ψ_u(α)` を `ψ_v(β)` と `(u, α)` の辞書式で比べる、その一歩。 -/
def DictHeadLt77 : Prop := ∀ (u v : Nat) (a b : BT),
    btLe72 1 (BT.D u a) = true → btLe72 1 (BT.D v b) = true →
    BT.isStd (BT.D u a) = true → BT.isStd (BT.D v b) = true →
    (u < v ∨ (u = v ∧ lt (dict a) (dict b) = true)) →
    lt (dict (BT.D u a)) (dict (BT.D v b)) = true

theorem dictLtUpTo_all77 (Hp : PsiIdxOKStd172) (H : DictHeadLt77) (n : Nat) :
    DictLtUpTo77 n := by
  refine Nat.strongRecOn (motive := fun n => DictLtUpTo77 n) n ?_
  intro n IH f l1 l2 hsz g1 g2 hlt
  cases f with
  | zero => rw [ltL_zero77] at hlt; exact Bool.noConfusion hlt
  | succ f' =>
    cases l1 with
    | nil =>
        cases l2 with
        | nil => rw [ltL_nil_nil77] at hlt; exact Bool.noConfusion hlt
        | cons q qs =>
            obtain ⟨v, b, rfl⟩ := g2.1 q (List.Mem.head _)
            show lt zero (dict (BT.ofL (BT.D v b :: qs))) = true
            exact lt_zero_ne76 (dict_ne_zero76 Hp _ (btLe_ofL77 g2) (isStd_ofL77 g2)
              (ofL_ne_zero77 ⟨v, b, rfl⟩))
    | cons p ps =>
        cases l2 with
        | nil => rw [ltL_cons_nil77] at hlt; exact Bool.noConfusion hlt
        | cons q qs =>
            obtain ⟨u, a, rfl⟩ := g1.1 p (List.Mem.head _)
            obtain ⟨v, b, rfl⟩ := g2.1 q (List.Mem.head _)
            have e1 : szL77 (BT.D u a :: ps) = 1 + BT.size a + szL77 ps := rfl
            have e2 : szL77 (BT.D v b :: qs) = 1 + BT.size b + szL77 qs := rfl
            have ha1 := size_pos77 a
            have hb1 := size_pos77 b
            have hm : n - 2 < n := by omega
            have HQ : DictLtUpTo77 (n - 2) := IH (n - 2) hm
            have hB1 : toList (dict (BT.ofL (BT.D u a :: ps)))
                = dict (BT.D u a) :: ps.map dict :=
              toList_dict_ofL77 Hp HQ _ g1 (by omega)
            have hB2 : toList (dict (BT.ofL (BT.D v b :: qs)))
                = dict (BT.D v b) :: qs.map dict :=
              toList_dict_ofL77 Hp HQ _ g2 (by omega)
            have hiX : inT (dict (BT.ofL (BT.D u a :: ps))) = true :=
              (inT_dict_of_std172 Hp _ (btLe_ofL77 g1) (isStd_ofL77 g1)).1
            have hiY : inT (dict (BT.ofL (BT.D v b :: qs))) = true :=
              (inT_dict_of_std172 Hp _ (btLe_ofL77 g2) (isStd_ofL77 g2)).1
            have hbA : btLe72 1 (BT.D u a) = true := g1.2.2.1 _ (List.Mem.head _)
            have hbB : btLe72 1 (BT.D v b) = true := g2.2.2.1 _ (List.Mem.head _)
            have hsA : BT.isStd (BT.D u a) = true := g1.2.1 _ (List.Mem.head _)
            have hsB : BT.isStd (BT.D v b) = true := g2.2.1 _ (List.Mem.head _)
            have hstep : BT.ltL (f' + 1) (BT.D u a :: ps) (BT.D v b :: qs)
                = (if u < v then true else if v < u then false else
                    if a == b then BT.ltL f' ps qs
                    else BT.ltL f' (BT.toL a) (BT.toL b)) := rfl
            rw [hstep] at hlt
            by_cases huv : u < v
            · exact lt_of_hd_lt hiX hiY hB1 hB2
                (H u v a b hbA hbB hsA hsB (Or.inl huv))
            · rw [if_neg huv] at hlt
              by_cases hvu : v < u
              · rw [if_pos hvu] at hlt; exact Bool.noConfusion hlt
              · rw [if_neg hvu] at hlt
                have huv2 : u = v := by omega
                by_cases hab : (a == b) = true
                · rw [if_pos hab] at hlt
                  have hPQ : dict (BT.D u a) = dict (BT.D v b) := by
                    rw [huv2, bt_beq_eq77 hab]
                  have hB2' : toList (dict (BT.ofL (BT.D v b :: qs)))
                      = dict (BT.D u a) :: qs.map dict := by rw [hB2, hPQ]
                  refine lt_of_hd_eq77 hiX hiY hB1 hB2' ?_
                  rw [ofList_map_dict77 Hp HQ ps (goodL77_tail g1) (by omega),
                    ofList_map_dict77 Hp HQ qs (goodL77_tail g2) (by omega)]
                  exact HQ f' ps qs (by omega) (goodL77_tail g1) (goodL77_tail g2) hlt
                · rw [if_neg hab] at hlt
                  have hsa : BT.isStd a = true := isStd_of_D hsA
                  have hsb : BT.isStd b = true := isStd_of_D hsB
                  have hba : btLe72 1 a = true := (btLe72_D 1 u a hbA).2
                  have hbb : btLe72 1 b = true := (btLe72_D 1 v b hbB).2
                  have t1 := szL77_toL a
                  have t2 := szL77_toL b
                  have hlta : lt (dict (BT.ofL (BT.toL a))) (dict (BT.ofL (BT.toL b))) = true :=
                    HQ f' (BT.toL a) (BT.toL b) (by omega)
                      (good_toL77 a hsa hba) (good_toL77 b hsb hbb) hlt
                  rw [ofL_toL77 a hsa, ofL_toL77 b hsb] at hlta
                  exact lt_of_hd_lt hiX hiY hB1 hB2
                    (H u v a b hbA hbB hsA hsB (Or.inr ⟨huv2, hlta⟩))

/-- **§77 の主定理。** 頭部の比較さえあれば、`dict` は段 1 以下の標準な `BT` 項の
    上で `BT.lt` を保つ。和の側の帰納法はここで閉じている。 -/
theorem dictLt_of_head77 (Hp : PsiIdxOKStd172) (H : DictHeadLt77) (x y : BT)
    (hbx : btLe72 1 x = true) (hby : btLe72 1 y = true)
    (hsx : BT.isStd x = true) (hsy : BT.isStd y = true)
    (h : BT.lt x y = true) : lt (dict x) (dict y) = true := by
  have hq := dictLtUpTo_all77 Hp H (szL77 (BT.toL x) + szL77 (BT.toL y))
    (BT.size x + BT.size y + 2) (BT.toL x) (BT.toL y) (Nat.le_refl _)
    (good_toL77 x hsx hbx) (good_toL77 y hsy hby) h
  rw [ofL_toL77 x hsx, ofL_toL77 y hsy] at hq
  exact hq

/-! ### §77.5 頭部の比較の二つの半分 -/

/-- **段をまたぐ半分。** `ψ_0(α) < ψ_1(β)` — 添字が違うとき。 -/
def DictCross77 : Prop := ∀ (u v : Nat) (a b : BT), u < v →
    btLe72 1 (BT.D u a) = true → btLe72 1 (BT.D v b) = true →
    BT.isStd (BT.D u a) = true → BT.isStd (BT.D v b) = true →
    lt (dict (BT.D u a)) (dict (BT.D v b)) = true

/-- **段が同じ半分。** `collapse u` が引数の像の順序を保つこと。 -/
def CollapseMono77 : Prop := ∀ (u : Nat) (a b : BT),
    btLe72 1 (BT.D u a) = true → btLe72 1 (BT.D u b) = true →
    BT.isStd (BT.D u a) = true → BT.isStd (BT.D u b) = true →
    lt (dict a) (dict b) = true →
    lt (collapse u (dict a)) (collapse u (dict b)) = true

theorem dictHeadLt_of_split77 (H1 : DictCross77) (H2 : CollapseMono77) : DictHeadLt77 := by
  intro u v a b hbA hbB hsA hsB h
  rcases h with h | ⟨huv, h2⟩
  · exact H1 u v a b h hbA hbB hsA hsB
  · subst huv
    rw [Trans.Dict.dict_D, Trans.Dict.dict_D]
    exact H2 u a b hbA hbB hsA hsB h2

/-- **§77 の結論の形。** 二つの半分から `dict` の順序保存が出る。 -/
theorem dictLt_of_split77 (Hp : PsiIdxOKStd172) (H1 : DictCross77) (H2 : CollapseMono77)
    (x y : BT) (hbx : btLe72 1 x = true) (hby : btLe72 1 y = true)
    (hsx : BT.isStd x = true) (hsy : BT.isStd y = true)
    (h : BT.lt x y = true) : lt (dict x) (dict y) = true :=
  dictLt_of_head77 Hp (dictHeadLt_of_split77 H1 H2) x y hbx hby hsx hsy h

end
/-! ### §77.6 添字の値の側 — `bValA71` は部分領域で標準 -/

section
open Evidence.Region
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- **`bValA71` の成分列。** `bVal` (§72) と違い先頭の `(0, nil)` も落とさない。 -/
theorem toL_bValA7177 : ∀ (t : B), (bValA71 t).toL = (toL t).map fB72
  | .nil => rfl
  | .nd v r c => by
      rw [toL_bValA71_nd v r c, toL_bValA7177 r, toL_nd, List.map_append]
      rfl

theorem bValA71_ofL77 (t : B) : bValA71 t = BT.ofL ((toL t).map fB72) := by
  rw [← toL_bValA7177 t]
  exact (nfSum_bValA7174 t).symm

/-- **前置きを付けない値も部分領域では標準。** §72 の `regionStdSum1_72` の
    `dropHd72` を外した形。`nonIncrL` は落とす前の列でも成り立つ。 -/
theorem stdA77 (t : B) (ht : stdB1 t = true) : BT.isStd (bValA71 t) = true := by
  have hl : lvlLe 1 t = true := lvlLe1_of_stdB1 t ht
  have hs' : ((nfB t && nonIncr t) && stdIn t) = true := stdB_of_stdB1 t ht
  have hst : stdIn t = true := ((Bool.and_eq_true _ _).mp hs').2
  have hni : nonIncr t = true := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hs').1).2
  have hlv : LvlL72 (toL t) := lvlL72_of_lvlLe t hl
  rw [bValA71_ofL77 t]
  refine isStd_ofL72 _ ?_ ?_ (descOK_map72 (toL t) hlv hni)
  · intro z hz
    obtain ⟨q, _, hq⟩ := List.mem_map.mp hz
    exact ⟨q.1, bArg q.1 q.2, hq.symm⟩
  · intro z hz
    obtain ⟨q, hqm, hq⟩ := List.mem_map.mp hz
    rw [← hq]
    obtain ⟨hnq, hvq, hsq⟩ := stdIn_mem72 t hst q hqm
    exact argStd72 q.1 q.2 (hlv q hqm).2 hnq hvq hsq

theorem btLeA77 (t : B) (ht : stdB1 t = true) : btLe72 1 (bValA71 t) = true := by
  have hl : lvlLe 1 t = true := lvlLe1_of_stdB1 t ht
  have hlv : LvlL72 (toL t) := lvlL72_of_lvlLe t hl
  rw [bValA71_ofL77 t]
  refine btLe72_ofL72 _ ?_
  intro z hz
  obtain ⟨q, hqm, hq⟩ := List.mem_map.mp hz
  rw [← hq]
  show (decide (q.1 ≤ 1) && btLe72 1 (bArg q.1 q.2)) = true
  rw [decide_eq_true (hlv q hqm).1,
    btLe72_bArg72 (sizeB q.2 + 1) q.1 q.2 (Nat.lt_succ_self _) (hlv q hqm).2]
  rfl

/-- **§77 の結論。** `DictLtA74` — `Trans/Dict.lean` の受領記録 (C) — は
    頭部の比較 `DictHeadLt77` ただ一つに落ちる。和の側は定理になった。 -/
theorem dictLtA74_of_head77 (Hp : PsiIdxOKStd172) (H : DictHeadLt77) : DictLtA74 :=
  fun u t hu ht h =>
    dictLt_of_head77 Hp H _ _ (btLeA77 u hu) (btLeA77 t ht) (stdA77 u hu) (stdA77 t ht) h

/-- 橋 `VOfLtA71` も同じ一つに落ちる。 -/
theorem vOfLtA71_of_head77 (Hp : PsiIdxOKStd172) (H : DictHeadLt77) : VOfLtA71 :=
  vOfLtA71_of_dictLt76 Hp (dictLtA74_of_head77 Hp H)

/-- 326 行目の減少条項。 -/
theorem limDecS1_77 (Hp : PsiIdxOKStd172) (H : DictHeadLt77) : LimDecS1 :=
  limDecS1_76 Hp (dictLtA74_of_head77 Hp H)

/-- 326 行目の増加条項。 -/
theorem limIncS1_77 (Hp : PsiIdxOKStd172) (H : DictHeadLt77) : LimIncS1 :=
  limIncS1_76 Hp (dictLtA74_of_head77 Hp H)

end

/-! ### §77.7 `ψ₁(α) = ω^(Ω₁ + α)` — 段 1 では `collapse` はただの `ω^·` -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- 成分がすべて `w` より下なら `wcnf` は何も分解しない。 -/
theorem wcnf_all_lt77 (w : Term) : ∀ (L : List Term), (∀ p ∈ L, lt p w = true) →
    wcnf w L = ([], ofList L)
  | [], _ => rfl
  | p :: _, h => wcnf_cons_lt (h p (List.Mem.head _))

/-- **`ψ_1(α) = ω^(Ω₁ + α)`。** `Trans/Dict.lean` の (D1) の `u = 1` の場合。
    強臨界の枝は段 1 以下では一度も発火しない (§73 の `wcnf_reg2_nil73` と同じ理由)。 -/
theorem collapse1_eq77 (x : Term) (hx : inT x = true)
    (hlt : ∀ p ∈ toList x, lt p (reg 2) = true) :
    collapse 1 x = omegaNF (plus (reg 1) x) := by
  rw [collapse_eq, wcnf_all_lt77 (reg (1+1)) (toList x) hlt]
  show omegaNF (plus (reg 1) (plus zero (ofList (toList x)))) = _
  rw [inT_ofList_toList x hx, plus_zero_left_inT hx]

/-- **`ψ_0(α) = ω^α` (`α < Ω₁`)。** (D1) の `u = 0` の場合。 -/
theorem collapse0_eq77 (x : Term) (hx : inT x = true)
    (hlt : ∀ p ∈ toList x, lt p (reg 1) = true) :
    collapse 0 x = omegaNF x := by
  rw [collapse_eq, wcnf_all_lt77 (reg (0+1)) (toList x) hlt]
  show omegaNF (plus (reg 0) (plus zero (ofList (toList x)))) = _
  rw [inT_ofList_toList x hx, plus_zero_left_inT hx,
    show plus (reg 0) x = plus zero x from rfl, plus_zero_left_inT hx]

/-- 段 1 以下の像に当てはめた形。 -/
theorem dict_D1_eq77 (Hp : PsiIdxOKStd172) (a : BT) (hb : btLe72 1 a = true)
    (hs : BT.isStd a = true) :
    dict (BT.D 1 a) = omegaNF (plus (reg 1) (dict a)) := by
  rw [Trans.Dict.dict_D]
  exact collapse1_eq77 (dict a) (inT_dict_of_std172 Hp a hb hs).1
    (fun p hp => lt_pure73_reg2 (pure73_toList _ (pure73_dict a hb) p hp))

end

/-! ### §77.8 残る仮説を絞る -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- **段をまたぐ半分は 1 本の不等式。** 段の上限が `u = 0`・`v = 1` を強いる。 -/
theorem dictCross_of01_77
    (H : ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 1 b) = true →
      BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 1 b) = true →
      lt (dict (BT.D 0 a)) (dict (BT.D 1 b)) = true) : DictCross77 := by
  intro u v a b huv hbA hbB hsA hsB
  have hu1 := (btLe72_D 1 u a hbA).1
  have hv1 := (btLe72_D 1 v b hbB).1
  have hu0 : u = 0 := by omega
  have hv0 : v = 1 := by omega
  subst hu0; subst hv0
  exact H a b hbA hbB hsA hsB

/-- **段が同じ半分は `u = 0` と `u = 1` の 2 本。** -/
theorem collapseMono_of_split77
    (H0 : ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
      BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true → lt (dict a) (dict b) = true →
      lt (collapse 0 (dict a)) (collapse 0 (dict b)) = true)
    (H1 : ∀ (a b : BT), btLe72 1 (BT.D 1 a) = true → btLe72 1 (BT.D 1 b) = true →
      BT.isStd (BT.D 1 a) = true → BT.isStd (BT.D 1 b) = true → lt (dict a) (dict b) = true →
      lt (collapse 1 (dict a)) (collapse 1 (dict b)) = true) : CollapseMono77 := by
  intro u a b hbA hbB hsA hsB h
  have hu1 := (btLe72_D 1 u a hbA).1
  cases u with
  | zero => exact H0 a b hbA hbB hsA hsB h
  | succ u' =>
      cases u' with
      | zero => exact H1 a b hbA hbB hsA hsB h
      | succ _ => exact absurd hu1 (by omega)

/-- **`u = 1` の半分は `ω^(Ω₁ + ·)` の単調性そのもの** — §77.7 で書き換えた形。 -/
def OmPlusMono77 : Prop := ∀ (a b : BT), btLe72 1 (BT.D 1 a) = true →
    btLe72 1 (BT.D 1 b) = true → BT.isStd (BT.D 1 a) = true → BT.isStd (BT.D 1 b) = true →
    lt (dict a) (dict b) = true →
    lt (omegaNF (plus (reg 1) (dict a))) (omegaNF (plus (reg 1) (dict b))) = true

theorem collapseMono1_of77 (Hp : PsiIdxOKStd172) (H : OmPlusMono77) :
    ∀ (a b : BT), btLe72 1 (BT.D 1 a) = true → btLe72 1 (BT.D 1 b) = true →
      BT.isStd (BT.D 1 a) = true → BT.isStd (BT.D 1 b) = true → lt (dict a) (dict b) = true →
      lt (collapse 1 (dict a)) (collapse 1 (dict b)) = true := by
  intro a b hbA hbB hsA hsB h
  rw [← Trans.Dict.dict_D, ← Trans.Dict.dict_D,
    dict_D1_eq77 Hp a (btLe72_D 1 1 a hbA).2 (isStd_of_D hsA),
    dict_D1_eq77 Hp b (btLe72_D 1 1 b hbB).2 (isStd_of_D hsB)]
  exact H a b hbA hbB hsA hsB h


/-- **`u = 1` の半分の、非狭義の分だけは定理。** §65.4 の `plus_mono_right_inT` と
    §65.3 の `omegaNF_mono_inT` をつなぐだけで `≤` は出る。**出ないのは狭義の分**で、
    それは `ω^·` の狭義単調性 — `CNVOps` §29 の D3 (`dnFacts`) の 𝔗(M) 版 — が
    無いからである。§65.3 はそこを避けて `le` で止めている。 -/
theorem le_collapse1_77 (Hp : PsiIdxOKStd172) (a b : BT)
    (hbA : btLe72 1 (BT.D 1 a) = true) (hbB : btLe72 1 (BT.D 1 b) = true)
    (hsA : BT.isStd (BT.D 1 a) = true) (hsB : BT.isStd (BT.D 1 b) = true)
    (h : lt (dict a) (dict b) = true) :
    le (collapse 1 (dict a)) (collapse 1 (dict b)) = true := by
  have hia := (inT_dict_of_std172 Hp a (btLe72_D 1 1 a hbA).2 (isStd_of_D hsA)).1
  have hib := (inT_dict_of_std172 Hp b (btLe72_D 1 1 b hbB).2 (isStd_of_D hsB)).1
  rw [← Trans.Dict.dict_D, ← Trans.Dict.dict_D,
    dict_D1_eq77 Hp a (btLe72_D 1 1 a hbA).2 (isStd_of_D hsA),
    dict_D1_eq77 Hp b (btLe72_D 1 1 b hbB).2 (isStd_of_D hsB)]
  exact omegaNF_mono_inT (inT_plus (inT_reg 1) hia) (inT_plus (inT_reg 1) hib)
    (plus_mono_right_inT (reg 1) (inT_reg 1) (dict a) (dict b) hia hib (le_of_lt h))

/-- **326 行目の証明書。** §76 の 4 つのうち `DictLtA74` が `DictHeadLt77` に替わる。 -/
theorem certIn_t326_head77 (Hp : PsiIdxOKStd172) (H : DictHeadLt77)
    (HCD : CofDenseS1) (HBC : BCofIn71)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_dict76 Hp (dictLtA74_of_head77 Hp H) HCD HBC hacc

end

/-! ### §77.9 測定 (凍結)

**構成。** `seed77` は 12 個の `BT` 項 — `0`・`1`・`ω`・`Ω₁`・`ψ₁ψ₁0`・`ψ₀ψ₁0`、
**上限より 2 つ先の添字** `ψ₂0`・`ψ₃0`、それに `ψ` の入れ子が **5 段** のもの 4 本
(`ψ₀ψ₁ψ₁ψ₁ψ₀0`・`ψ₁ψ₁ψ₁ψ₁ψ₀0`・`ψ₂ψ₂ψ₁ψ₁ψ₀0`・`ψ₀ψ₂ψ₁ψ₁ψ₀0`) で、最後の 2 本は
**領域の外**にある。そこに添字 0…3 の `ψ` を 1 段かぶせ (`dsucc77 4`)、さらに和を
足して 107 項。母集団はそれを 3 通りに絞って作る:

    popGood77   btLe72 1 かつ BT.isStd     19 項 →  361 対   (§77 の仮説そのもの)
    popStd77    BT.isStd のみ               71 項 → 5041 対   (段の上限を外す)
    popLv77     btLe72 1 のみ               24 項 →  576 対   (標準性を外す)

各変数はそれが実際に走る形の上で振ってある — 頭部の測定は主要項の対、`collapse` の
測定は引数の対、成分列の測定は項そのもの。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

private def seed77 : List BT :=
  [BT.zero, BT.D 0 BT.zero, BT.D 0 (BT.D 0 BT.zero), BT.D 1 BT.zero,
   BT.D 1 (BT.D 1 BT.zero), BT.D 0 (BT.D 1 BT.zero), BT.D 2 BT.zero, BT.D 3 BT.zero,
   BT.D 0 (BT.D 1 (BT.D 1 (BT.D 1 (BT.D 0 BT.zero)))),
   BT.D 1 (BT.D 1 (BT.D 1 (BT.D 1 (BT.D 0 BT.zero)))),
   BT.D 2 (BT.D 2 (BT.D 1 (BT.D 1 (BT.D 0 BT.zero)))),
   BT.D 0 (BT.D 2 (BT.D 1 (BT.D 1 (BT.D 0 BT.zero))))]

private def dedup77 (l : List BT) : List BT :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []
private def dsucc77 (n : Nat) (l : List BT) : List BT :=
  (List.range n).flatMap (fun u => l.map (fun a => BT.D u a))
private def sums77 (l : List BT) : List BT :=
  l.flatMap (fun a => l.map (fun b => BT.add a b))
private def every77 (k : Nat) (l : List BT) : List BT :=
  (l.zipIdx.filter (fun p => p.2 % k == 0)).map (·.1)

private def lvlA77 : List BT := dedup77 (seed77 ++ every77 2 (dsucc77 4 seed77))
private def popAll77 : List BT := dedup77 (lvlA77 ++ every77 3 (sums77 (every77 2 lvlA77)))
private def popGood77 : List BT := popAll77.filter (fun x => btLe72 1 x && BT.isStd x)
private def popStd77 : List BT := popAll77.filter BT.isStd
private def popLv77 : List BT := popAll77.filter (btLe72 1 ·)

private def okPair77 (a b : BT) : Bool := !(BT.lt a b) || TM.Term.lt (dict a) (dict b)
private def fails77 (l : List BT) : Nat :=
  (l.flatMap (fun a => l.map (fun b => (a, b)))).countP (fun p => !(okPair77 p.1 p.2))
private def crossFail77 (l : List BT) : Nat :=
  ((l.filter BT.isP).flatMap (fun a => (l.filter BT.isP).map (fun b => (a, b)))).countP
    (fun p => match p.1, p.2 with
      | BT.D u _, BT.D v _ => u < v && !(TM.Term.lt (dict p.1) (dict p.2))
      | _, _ => false)
private def headFail77 (l : List BT) : Nat :=
  ((l.filter BT.isP).flatMap (fun a => (l.filter BT.isP).map (fun b => (a, b)))).countP
    (fun p => BT.lt p.1 p.2 && !(TM.Term.lt (dict p.1) (dict p.2)))
private def monoFail77 (w : Nat) (l : List BT) : Nat :=
  (l.flatMap (fun a => l.map (fun b => (a, b)))).countP
    (fun p => TM.Term.lt (dict p.1) (dict p.2) &&
      !(TM.Term.lt (collapse w (dict p.1)) (collapse w (dict p.2))))
private def transOK77 (x : BT) : Bool := (dict x).toList == (x.toL).map dict

/-! 母集団の大きさ。 -/
#guard (popAll77.length, popGood77.length, popStd77.length, popLv77.length) == (107, 19, 71, 24)

/-! **肯定 1 — §77 の主張そのもの。** 361 対で反例 0。 -/
#guard fails77 popGood77 == 0

/-! **肯定 2 — 頭部の仮説 `DictHeadLt77`。** 主要項の対で反例 0、段をまたぐ半分も 0。 -/
#guard headFail77 popGood77 == 0
#guard crossFail77 popGood77 == 0

/-! **否定 1 — `BT.isStd` は外せない。** 段の上限だけでは 576 対中 35 対が反転する。 -/
#guard fails77 popLv77 == 35

/-! **否定 2 — 段の上限は順序を買っていない。** 標準なら段 2・3 の節があっても
    5041 対で反例 0。§77 の `btLe72 1` は `inT (dict ·)` の門のためだけにある。 -/
#guard fails77 popStd77 == 0

/-! **否定 3 — `collapse 0` の単調性が要るのは `K` の条件。** 引数が標準で段 1 以下でも
    `BT.isStd (ψ₀ ·)` を落とすと 28 対が反転し、課すと 0 になる。`collapse 1` は
    どちらでも 0 — §77.7 が言うとおり `ω^(Ω₁ + ·)` でしかない。 -/
#guard monoFail77 0 popGood77 == 28
#guard monoFail77 0 (popGood77.filter (fun a => BT.isStd (BT.D 0 a))) == 0
#guard monoFail77 1 popGood77 == 0
#guard monoFail77 1 (popGood77.filter (fun a => BT.isStd (BT.D 1 a))) == 0

/-! **否定 4 — 降べきを落とすと成分列の移送が壊れる。** §77.3 が `descOK72` を使う場所。 -/
#guard popGood77.countP (fun x => !(transOK77 x)) == 0
#guard popLv77.countP (fun x => !(transOK77 x)) == 4

/-! **添字の側 (§77.6 は定理なので、これは確認であって根拠ではない)。** -/
#guard ((subP 6).filter (fun t => !(BT.isStd (bValA71 t)))).length == 0
#guard ((subP 7).filter (fun t => !(BT.isStd (bValA71 t)))).length == 0
#guard ((subP 6).filter (fun t => !(btLe72 1 (bValA71 t)))).length == 0

/-! **§77.7 の確認。** 段 1 の像は `ω^(Ω₁ + ·)`。 -/
#guard popGood77.all fun a =>
  dict (BT.D 1 a) == omegaNF (plus (reg 1) (dict a))

end

/-! ### §77.10 公理 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

end

/-! ## §78 THE `⊖ 1` HALF OF THE `K`-GATE IS A THEOREM — ONE COMPARISON IS ALL THAT IS LEFT

§75 reduced the whole `K`-gate to two clauses about a single firing pair `(aV, cV)` of the
`wcnf` scan on `dict a`, with `Δ = W^(aV ⊖ W)·cV`:

    LocalFacts2_75 0 (aV, cV) :  (K2')  K_{Ω₁} aV ∪ K_{Ω₁} cV < Δ
                                 (K4)   Δ ⊖ 1 ≠ Δ  ⟹  both `K`-sets are empty

**§78 proves (K4), unconditionally.**  Not for the level-one image, not for standard `a`, not
even for a firing pair: for EVERY pair of 𝔗(M) terms.  What is left of the gate is (K2')
alone, and §78.5 measures which of its two halves carries the content.

WHAT IS PROVED.

  §78.1  **FOUR SMALL FACTS ABOUT `0` AND `1`.**  `ofList l = 0` only for `l = []` and
         `l = [0]`; a `≤ 1` additively principal term IS `1` (through §8's `below_one`);
         `s ⊕ t = 0` forces both; and `ω^x = 1` forces `x = 0` — the last by `ω^1 = ω`
         and §65.3's `omegaNF_mono_inT`, which is cheaper than opening `phiNF`'s five
         branches.  `logOm q = 0` on an additively principal `q` likewise forces `q = 1`,
         and there the `φ̄(0,·)` clause of `logOm` is the only one that has to be looked at.

  §78.2  **(K4) IS A THEOREM.**  `k4_78`.  The proof is a chain of forcings and it says
         exactly where the branch lives:

             Δ ⊖ 1 ≠ Δ  ⟹  the leading component of Δ is `1`
                        ⟹  ω^(W·(aV ⊖ W) + log cV₀) = 1   (`Δ` is a `mulL`, so its
                                                            components are `ω`-powers)
                        ⟹  W·(aV ⊖ W) = 0  and  log cV₀ = 0
                        ⟹  aV = W  and  cV = a natural number.

         Both `K`-sets are then empty by §75.4b's `kset_fst_reg75` and `Kset κ 1 = ∅` — the
         two lemmas that §75 already had and could not reach.  **The branch is not vacuous**:
         §78.5 exhibits the pairs where it fires (4 of 102 in this section's population, 27 of
         325 in §75.6's), and at every one of them `Δ = 1`.

  §78.3  **WHAT IS LEFT IS ONE CLAUSE.**  `LocalK2_78` is (K2') by itself;
         `localStdFacts2_of_k2_78` recovers §75's two-clause `LocalStdFacts2_75` from it, and
         `psiIdxOKStd172_of_k2_78` chains §73's and §72's assemblies to §72's second gate.
         `certIn_t326_k2_78` re-derives row 326's certificate on top of §77:

             LocalK2_78 → DictHeadLt77 → CofDenseS1 → BCofIn71 → Acc → CertifiedIn …

         `localK2_of_split78` splits the residual at `aV` and `cV`, because §78.5 says the two
         halves are not equally hard, and `ksetOK_dd_of_k2_78` records — in one line off
         §75.2's `mem_Kset_ddOf75` — that the residual IMPLIES [Rathjen, 1991] 2.1(vi) for the
         single term `Δ`.  §78.5 measures the converse at 0 disagreements on 429 firing pairs,
         so the residual's real shape is one term, not a pair.

WHAT IS **NOT** CLAIMED.  (K2') is NOT proved, in either half.  It is the transport of
Buchholz's `G(a,0) < a` that §68, §72, §73 and §75 all named, and §78 does not spend `isStd`
either.  Nothing here proves `DictHeadLt77`, `CofDenseS1` or `BCofIn71`.

WHAT THE MEASUREMENT SAYS (§78.5 gives the construction).  **The negative results first.**

  * **The residual is the `aV` half.**  Over the three populations — 129 in-region terms,
    217 with an index past the bound, 118 non-standard, 429 firing pairs in all — (K2') fails
    87 times and **every single failure is `K_{Ω₁} aV ≮ Δ`.  The `cV` half does not fail
    once.**  §75.6 measured only the union.  A §79 that wants the gate should attack
    `K_{Ω₁} aV < Δ` and may treat `K_{Ω₁} cV < Δ` as the easier half.
  * **`BT.isStd` is the side condition that carries (K2'), not the level bound.**  On the
    bumped terms that stay standard (51 terms, 51 pairs) (K2') does not fail at all, even
    with `ψ₃` inside; on the level-bounded but NOT standard population (118 terms, 110 pairs)
    it fails 4 times.  `kBad78 = ψ₁ψ₁(ψ₁ψ₁ψ₀ψ₁ψ₁ψ₁0 ⊕ ψ₀ψ₁ψ₁ψ₁ψ₁ψ₁0)` freezes the smallest
    of the four as a theorem: level ≤ 1, `BT.isStd` TRUE, `BT.isStd (ψ₀ ·)` FALSE, `k2b78`
    false.  It is §75.6's `wStep75` phenomenon one width up — a term that is Buchholz standard
    and stops being so under one `ψ₀`; `wStep75` was a tower, this one is a sum.
  * **§73.7's (K2) is not the same clause as (K2'), and this population separates them.**
    `K_{Ω₁} aV < aV` fails 92 times against (K2')'s 87, and the two verdicts DISAGREE on 5
    pairs.  Inside the region (K2) fails 5 times and (K2') zero times.  §75.4c found this at
    `ψ`-nesting 9 in towers; it is here again at width 2 and 3, which is independent evidence
    that the comparison must be against `Δ`.
  * **(K4) survives everything.**  0 failures on all 429 pairs — which is what a theorem has
    to do, and the measurement was made BEFORE the proof; that is why (K4) was the clause to
    attack.

  The positive side.  0 failures of (K2') and of (K4) on the 102 firing pairs of the
  in-region population, 19 of which have a non-empty `K_{Ω₁} aV` and 12 a non-empty
  `K_{Ω₁} cV`; 88 distinct `(aV, cV)` shapes.  The (K4) branch `Δ ⊖ 1 ≠ Δ` fires at 4 of the
  102, and at every one of them `aV = Ω₁`, `cV = 1`, `Δ = 1` — exactly the shape §78.2 forces;
  on §75.6's `hotD75` it fires at 27 of 325 and `k4b78` holds at all 27.  `K_{Ω₁} Δ` is
  non-empty at 155 of the 429, so the reformulation above is not vacuous either.  §75.6's
  (K3) `cV ≤ Δ` holds at all 429 (still unproved); `aV ≤ Δ` fails at 8, which is why §75.4c
  dropped (K5).  `ksetStepOK_wOK78` and `ksetStepOK_wWide78` freeze the new decidable route
  on a `ψ`-nesting-9 tower and on a width-2 sum, both with a non-empty `K_{Ω₁} aV`.
-/
/-! ### §78.1 補助 — `0` と `1` をめぐる四つの小さな事実 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- `ofList l = 0` になるのは列が空か `[0]` のときだけ。 -/
private theorem ofList_eq_zero78 : ∀ (l : List Term), ofList l = zero → l = [] ∨ l = [zero]
  | [], _ => Or.inl rfl
  | [a], h => Or.inr (by rw [show a = zero from h])
  | _ :: _ :: _, h => absurd h (by intro hc; exact Term.noConfusion hc)

/-- `1` 以下の加法主要項は `1` そのもの。 -/
private theorem eq_one_of_le_one78 {q : Term} (hq : inT q = true) (hap : q.isAP = true)
    (h : le q one = true) : q = one := by
  rcases (Bool.or_eq_true _ _).mp (show ((q == one) || lt q one) = true from h) with h1 | h1
  · exact of_decide_eq_true h1
  · exact absurd (below_one q hq (fuelOf q one) h1) (ne_zero_of_isAP hap)

/-- `ω^x = 1` なら `x = 0`。`ω^1 = ω` で押さえる。 -/
private theorem eq_zero_of_omegaNF_one78 {z : Term} (hz : inT z = true)
    (h : omegaNF z = one) : z = zero := by
  by_cases hne : z = zero
  · exact hne
  exfalso
  have h2 : le (omegaNF one) (omegaNF z) = true :=
    omegaNF_mono_inT inT_one hz (le_one_inT hz hne)
  rw [h, show omegaNF one = phi zero one from rfl] at h2
  have h3 : (phi zero one : Term) = one :=
    eq_one_of_le_one78 (by decide) rfl h2
  exact Term.noConfusion h3 (fun _ h5 => Term.noConfusion h5)

/-- `s ⊕ t = 0` なら両方 `0`。 -/
private theorem plus_eq_zero78 {s t : Term} (ht : inT t = true) (h : plus s t = zero) :
    s = zero ∧ t = zero := by
  cases hl : toList t with
  | nil => rw [plus_nil hl] at h; exact ⟨h, toList_eq_nil t hl⟩
  | cons b1 r =>
    exfalso
    rw [plus_cons66 hl] at h
    have hb1 : b1 ∈ (toList s).filter (fun a => le b1 a) ++ (b1 :: r) :=
      List.mem_append.mpr (Or.inr (List.Mem.head _))
    rcases ofList_eq_zero78 _ h with h2 | h2
    · rw [h2] at hb1; cases hb1
    · rw [h2] at hb1
      have hz : b1 = zero := List.mem_singleton.mp hb1
      have hap : b1.isAP = true := inTL_isAP ht b1 (by rw [hl]; exact List.Mem.head _)
      rw [hz] at hap
      exact Bool.noConfusion hap

/-- `mulL e y = 0` なら `y` の成分列は空。 -/
private theorem toList_nil_of_mulL_zero78 {e y : Term} (h : mulL e y = zero) :
    toList y = [] := by
  cases hl : toList y with
  | nil => rfl
  | cons p r =>
    exfalso
    have h1 : ofList ((toList y).map (fun q => omegaNF (plus e (logOm q)))) = zero := h
    rw [hl, List.map_cons] at h1
    rcases ofList_eq_zero78 _ h1 with h2 | h2
    · exact List.cons_ne_nil _ _ h2
    · injection h2 with hh _
      exact ne_zero_of_isAP (isAP_omegaNF _) hh

/-- `subAP w h = 0` なら成分列は空か `[w]`。 -/
private theorem subAP_eq_zero78 {w t : Term} (ht : inT t = true) (h : subAP w t = zero) :
    toList t = [] ∨ toList t = [w] := by
  cases hl : toList t with
  | nil => exact Or.inl rfl
  | cons p r =>
    have h1 : (if p == w then ofList r else t) = zero := by
      rw [show subAP w t = (match toList t with
            | [] => zero
            | q :: rest => if q == w then ofList rest else t) from rfl, hl] at h
      exact h
    by_cases hp : (p == w) = true
    · rw [if_pos hp] at h1
      rcases ofList_eq_zero78 r h1 with h2 | h2
      · refine Or.inr ?_
        rw [h2, of_decide_eq_true hp]
      · exfalso
        have hap : (zero : Term).isAP = true :=
          inTL_isAP ht zero (by rw [hl, h2]; exact List.Mem.tail _ (List.Mem.head _))
        exact Bool.noConfusion hap
    · rw [if_neg hp] at h1
      exfalso
      rw [h1] at hl
      exact List.cons_ne_nil _ _ (show ([] : List Term) = p :: r from hl).symm

/-- 成分列が空か `[Ω_{u+1}]` なら `K_{Ω_{u+1}}` は空。 -/
private theorem kset_nil_of_toList78 {u : Nat} {t : Term}
    (h : toList t = [] ∨ toList t = [reg (u+1)]) : ∀ y, y ∈ Kset (reg (u+1)) t → False := by
  intro y hy
  rw [Kset_eq_KsetL] at hy
  rcases h with h | h
  · rw [h] at hy
    obtain ⟨a, ha, _⟩ := (mem_KsetL_iff _ y _).mp hy
    cases ha
  · rw [h] at hy
    obtain ⟨a, ha, hya⟩ := (mem_KsetL_iff _ y _).mp hy
    rw [List.mem_singleton.mp ha] at hya
    exact mem_Kset_reg (u+1) hya

/-- `logOm q = 0` になる加法主要項は `1` だけ。 -/
private theorem eq_one_of_logOm_zero78 : ∀ {q : Term}, q.isAP = true → logOm q = zero → q = one
  | zero, hap, _ => Bool.noConfusion hap
  | add _ _, hap, _ => Bool.noConfusion hap
  | M, _, h => absurd (show (M : Term) = zero from h) (fun hc => Term.noConfusion hc)
  | omg a, _, h => absurd (show (omg a : Term) = zero from h) (fun hc => Term.noConfusion hc)
  | psi k a, _, h => absurd (show (psi k a : Term) = zero from h) (fun hc => Term.noConfusion hc)
  | Z a, _, h => absurd (show (Z a : Term) = zero from h) (fun hc => Term.noConfusion hc)
  | phi M b, _, h => absurd (show (phi M b : Term) = zero from h) (fun hc => Term.noConfusion hc)
  | phi (add x y) b, _, h =>
    absurd (show (phi (add x y) b : Term) = zero from h) (fun hc => Term.noConfusion hc)
  | phi (omg x) b, _, h =>
    absurd (show (phi (omg x) b : Term) = zero from h) (fun hc => Term.noConfusion hc)
  | phi (phi x y) b, _, h =>
    absurd (show (phi (phi x y) b : Term) = zero from h) (fun hc => Term.noConfusion hc)
  | phi (psi x y) b, _, h =>
    absurd (show (phi (psi x y) b : Term) = zero from h) (fun hc => Term.noConfusion hc)
  | phi (Z x) b, _, h =>
    absurd (show (phi (Z x) b : Term) = zero from h) (fun hc => Term.noConfusion hc)
  | phi zero b, _, h => by
    by_cases hs : phiShifted zero b = true
    · exfalso
      have hz : plus b one = zero := by
        rw [show logOm (phi zero b) = (if phiShifted zero b then plus b one else b) from rfl,
          if_pos hs] at h
        exact h
      exact Term.noConfusion (plus_eq_zero78 inT_one hz).2
    · have hb : b = zero := by
        rw [show logOm (phi zero b) = (if phiShifted zero b then plus b one else b) from rfl,
          if_neg hs] at h
        exact h
      rw [hb]
      rfl

end

/-! ### §78.2 (K4) は定理 — `Δ ⊖ 1 ≠ Δ` は `aV = Ω_{u+1}`・`cV ∈ ℕ` を強いる -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§78.1 の主定理 — (K4) は定理。**  `Δ ⊖ 1 ≠ Δ` なら `aV` の `K` も `cV` の `K` も空。
    発火 (`Ω_{u+1} ≤ aV`) すら要らない。 -/
theorem k4_78 {u : Nat} {ac : Term × Term} (h1 : inT ac.1 = true) (h2 : inT ac.2 = true)
    (h : sub1 (ddOf75 (reg (u+1)) ac) ≠ ddOf75 (reg (u+1)) ac) :
    (∀ y, y ∈ Kset (reg (u+1)) ac.1 → False) ∧
      (∀ y, y ∈ Kset (reg (u+1)) ac.2 → False) := by
  have hw : inT (reg (u+1)) = true := inT_reg (u+1)
  have he : inT (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) = true :=
    inT_mulL mulDescInT hw (inT_subAP h1)
  have hmap : toList (ddOf75 (reg (u+1)) ac)
      = (toList ac.2).map
        (fun q => omegaNF (plus (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) (logOm q))) := by
    show toList (ofList _) = _
    refine toList_ofList _ (fun x hx => ?_)
    obtain ⟨q, _, hq⟩ := List.mem_map.mp hx
    rw [← hq]
    exact isAP_omegaNF _
  cases hl : toList (ddOf75 (reg (u+1)) ac) with
  | nil =>
    exact absurd (by rw [toList_eq_nil _ hl]; rfl) h
  | cons p r =>
    have hsub : sub1 (ddOf75 (reg (u+1)) ac)
        = (if p == one then ofList r else ddOf75 (reg (u+1)) ac) := by
      show (match toList (ddOf75 (reg (u+1)) ac) with
            | [] => zero
            | q :: rest => if q == one then ofList rest else ddOf75 (reg (u+1)) ac) = _
      rw [hl]
    have hp : p = one := by
      by_cases hpp : (p == one) = true
      · exact of_decide_eq_true hpp
      · exact absurd (by rw [hsub, if_neg hpp]) h
    cases hl2 : toList ac.2 with
    | nil =>
      exfalso
      rw [hl2, List.map_nil] at hmap
      rw [hmap] at hl
      exact List.cons_ne_nil _ _ hl.symm
    | cons q0 r0 =>
      obtain ⟨hc2, hd2⟩ := inT_toList ac.2 h2
      rw [hl2] at hc2 hd2
      obtain ⟨⟨hap0, hq0⟩, hcr⟩ := inTL_cons.mp hc2
      rw [hl2, List.map_cons] at hmap
      rw [hmap] at hl
      injection hl with hfp _
      rw [hp] at hfp
      have hz : plus (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) (logOm q0) = zero :=
        eq_zero_of_omegaNF_one78 (inT_plus he (inT_logOm hq0)) hfp
      obtain ⟨hez, hlz⟩ := plus_eq_zero78 (inT_logOm hq0) hz
      have hq01 : q0 = one := eq_one_of_logOm_zero78 hap0 hlz
      refine ⟨kset_nil_of_toList78 (subAP_eq_zero78 h1
        (toList_eq_nil _ (toList_nil_of_mulL_zero78 hez))), ?_⟩
      intro y hy
      rw [Kset_eq_KsetL] at hy
      obtain ⟨a, ha, hya⟩ := (mem_KsetL_iff _ y _).mp hy
      have haone : a = one := by
        rw [hl2] at ha
        cases ha with
        | head => exact hq01
        | tail _ hmem =>
          have hai := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcr a hmem)
          have hle : le a q0 = true := descL_bound_inT r0 q0 hq0 hcr hd2 a hmem
          rw [hq01] at hle
          exact eq_one_of_le_one78 hai.2 hai.1 hle
      rw [haone, Kset_one] at hya
      cases hya

/-- 両方の `K` が空なら (K2')・(K4) はそのまま出る。 -/
theorem localFacts2_of_empty78 {u : Nat} {ac : Term × Term}
    (h1 : ∀ y, y ∈ Kset (reg (u+1)) ac.1 → False)
    (h2 : ∀ y, y ∈ Kset (reg (u+1)) ac.2 → False) : LocalFacts2_75 u ac :=
  ⟨fun y hy => by
      rcases hy with hy | hy
      · exact (h1 y hy).elim
      · exact (h2 y hy).elim,
   fun _ => ⟨h1, h2⟩⟩

/-- 指数が `Ω_{u+1}` ちょうどで係数が自然数なら、対はまるごと只で片づく。 -/
theorem localFacts2_reg_ofNat78 {u n : Nat} {ac : Term × Term}
    (h1 : ac.1 = reg (u+1)) (h2 : ac.2 = ofNat n) : LocalFacts2_75 u ac :=
  localFacts2_of_empty78 (kset_fst_reg75 h1) (kset_snd_ofNat75 h2)

/-- **(K2') だけ残る形。** 指数側の `K` は `Ω_{u+1}` なら空、(K4) は §78.1 の定理。 -/
theorem localFacts2_of_reg_fst78 {u : Nat} {ac : Term × Term}
    (hi1 : inT ac.1 = true) (hi2 : inT ac.2 = true) (h1 : ac.1 = reg (u+1))
    (h2 : ∀ y, y ∈ Kset (reg (u+1)) ac.2 → lt y (ddOf75 (reg (u+1)) ac) = true) :
    LocalFacts2_75 u ac :=
  ⟨fun y hy => by
      rcases hy with hy | hy
      · exact (kset_fst_reg75 h1 y hy).elim
      · exact h2 y hy,
   fun hne => k4_78 hi1 hi2 hne⟩

end

/-! ### §78.3 残るのは一条項 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

def LocalK2_78 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true →
    inT (dict a) = true → lt (dict a) M = true →
    ∀ ac ∈ (wcnf (reg 1) (toList (dict a))).1, le (reg 1) ac.1 = true →
      ∀ y, (y ∈ Kset (reg 1) ac.1 ∨ y ∈ Kset (reg 1) ac.2) →
        lt y (ddOf75 (reg 1) ac) = true

/-- **§78.2 の主定理。** 一条項から §75 の二条項が出る — (K4) は仮説ではない。 -/
theorem localStdFacts2_of_k2_78 (H : LocalK2_78) : LocalStdFacts2_75 := by
  intro a hb hs hi hl ac hac hle
  obtain ⟨hc, hd⟩ := inT_toList (dict a) hi
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList (dict a)) hc hd
    (ltM_toList (dict a) hi hl)
  obtain ⟨hi1, _, hi2, _⟩ := hallOK ac hac
  exact ⟨H a hb hs hi hl ac hac hle, fun hne => k4_78 hi1 hi2 hne⟩

theorem localStd75_of_k2_78 (H : LocalK2_78) : LocalStd75 :=
  localStd75_of_facts2_75 (localStdFacts2_of_k2_78 H)

theorem psiIdxStep073_of_k2_78 (H : LocalK2_78) : PsiIdxStep073 :=
  psiIdxStep073_of_facts2_75 (localStdFacts2_of_k2_78 H)

theorem psiIdxOKStd172_of_k2_78 (H : LocalK2_78) : PsiIdxOKStd172 :=
  psiIdxOKStd172_of_step172 (psiIdxStepStd172_of_step073 (psiIdxStep073_of_k2_78 H))

/-- **§78 の結論。** 326 行目の証明書は、`K` の側では (K2') ただ一つを待つ。 -/
theorem certIn_t326_k2_78 (H : LocalK2_78) (HD : DictHeadLt77) (HCD : CofDenseS1)
    (HBC : BCofIn71) (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_head77 (psiIdxOKStd172_of_k2_78 H) HD HCD HBC hacc

/-- 残る一条項の `aV` 側。**§78.5 が測るとおり、破れるのはこちらだけ。** -/
def LocalK2Fst_78 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true →
    inT (dict a) = true → lt (dict a) M = true →
    ∀ ac ∈ (wcnf (reg 1) (toList (dict a))).1, le (reg 1) ac.1 = true →
      ∀ y, y ∈ Kset (reg 1) ac.1 → lt y (ddOf75 (reg 1) ac) = true

/-- 残る一条項の `cV` 側。**429 歩で一度も破れない** (§78.5)。 -/
def LocalK2Snd_78 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true →
    inT (dict a) = true → lt (dict a) M = true →
    ∀ ac ∈ (wcnf (reg 1) (toList (dict a))).1, le (reg 1) ac.1 = true →
      ∀ y, y ∈ Kset (reg 1) ac.2 → lt y (ddOf75 (reg 1) ac) = true

/-- 二つに割った形から元の一条項。 -/
theorem localK2_of_split78 (H1 : LocalK2Fst_78) (H2 : LocalK2Snd_78) : LocalK2_78 := by
  intro a hb hs hi hl ac hac hle y hy
  rcases hy with hy | hy
  · exact H1 a hb hs hi hl ac hac hle y hy
  · exact H2 a hb hs hi hl ac hac hle y hy

/-- **残る条項は `Δ` 自身の 2.1(vi) を含む。** §75.2 の `mem_Kset_ddOf75` の一行の系。
    **逆も 429 歩すべてで成り立つ** (§78.5、不一致 0) が、それは測定であって証明ではない
    — `K_{Ω₁} aV ∪ K_{Ω₁} cV ⊆ K_{Ω₁} Δ` を示すには `omegaNF`・`logOm`・`plus` の
    `Kset` 補題を逆向きに引き直さねばならない。§79 の材料。 -/
theorem ksetOK_dd_of_k2_78 {u : Nat} {ac : Term × Term}
    (h : ∀ y, (y ∈ Kset (reg (u+1)) ac.1 ∨ y ∈ Kset (reg (u+1)) ac.2) →
      lt y (ddOf75 (reg (u+1)) ac) = true) :
    ∀ y ∈ Kset (reg (u+1)) (ddOf75 (reg (u+1)) ac),
      lt y (ddOf75 (reg (u+1)) ac) = true :=
  fun y hy => h y (mem_Kset_ddOf75 hy)

end

/-! ### §78.4 判定器 — `⊖ 1` を見ない形 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

def k2b78 (u : Nat) (x : Term) : Bool :=
  (wcnf (reg (u+1)) (toList x)).1.all fun ac =>
    !(le (reg (u+1)) ac.1) ||
      ((Kset (reg (u+1)) ac.1 ++ Kset (reg (u+1)) ac.2).all fun y =>
        lt y (mulL (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) ac.2))

/-- **判定器から局所条件。** `⊖ 1` の始末は §78.1 の (K4) がする。 -/
theorem localK75_of_k2b78 {u : Nat} {x : Term} (hx : inT x = true) (hlx : lt x M = true)
    (h : k2b78 u x = true) : LocalK75 u x := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg (u+1)) (isSC_reg_succ u) (toList x) hc hd
    (ltM_toList x hx hlx)
  refine localK75_of_facts2_75 u x (fun ac hac hle => ?_)
  obtain ⟨hi1, _, hi2, _⟩ := hallOK ac hac
  have hall := List.all_eq_true.mp h ac hac
  rw [hle, Bool.not_true, Bool.false_or] at hall
  refine ⟨fun y hy => ?_, fun hne => k4_78 hi1 hi2 hne⟩
  refine List.all_eq_true.mp hall y ?_
  rcases hy with hy | hy
  · exact List.mem_append.mpr (Or.inl hy)
  · exact List.mem_append.mpr (Or.inr hy)

/-- 系 — 判定器から一歩ぶんの門。 -/
theorem ksetStepOK_of_k2b78 {u : Nat} {x : Term} (hx : inT x = true) (hlx : lt x M = true)
    (h : k2b78 u x = true) : KsetStepOK u x :=
  ksetStepOK_of_local75 u x hx hlx (localK75_of_k2b78 hx hlx h)

end

/-! ### §78.5 測定 (凍結)

**構成を先に書く。**  `tw78 p` は添字の列 `p` を上から順に重ねた塔
`ψ_{p₁}ψ_{p₂}…ψ_{p_k}0`、`T78 n k` は長さ `n` の `{0,1}` 列のうち `0` が `k` 個以下のもの
から作った塔の全体。母集団は**深さと幅を別々に振った四つの群**で、`ψ₀` をかぶせて
Buchholz 標準になるものだけを残す (条項が語るのはそこだけだから)。

    G1  深さ  `{0,1}^9` の塔ぜんぶ                              42 個  `ψ` の入れ子 9 段, 幅 1
    G2  幅 2   `ψ₁ψ₁(x ⊕ y)`,  x,y ∈ T78 6 1                    24 個  入れ子 8 段, 幅 2
    G3  幅 3   `ψ₁(x ⊕ y ⊕ z)`,  x,y,z ∈ T78 4 1                32 個  入れ子 5 段, 幅 3
    G4  係数枝 深さ 4 以下の塔ぜんぶ と `ψ₁^k 0 ⊕ y` (k = 3,4,5)  31 個  (K4) の枝が出るのは
                                                                       この形だけ
    ------------------------------------------------------------------------------------
    pop78 = G1 ++ G2 ++ G3 ++ G4 の標準なもの                   129 個, 発火 102 歩

**領域の外**も二通りに作る。`bump78 u` は `ψ₀` を `ψ_u` に差し替える (**上限より 2 つ・
3 つ先の添字**)、`nst78` は G2・G3 の生成元のうち標準でないもの。

    bmp78 = bump78 2 と bump78 3 を pop78 に当てたもの          217 個, 発火 217 歩
          (うち 41 個は `ψ₀` を持たない塔なので変わらない — 上限を本当に外れる歩は 176)
    nst78 = G2・G3 の非標準なもの (段の上限は満たす)            118 個, 発火 110 歩

`x ⊕ y` の形は `Δ` の材料を稼ぐために入れた。深さだけでは幅は出ない — §75.6 が
同じことを別の形で言っている。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 添字の列から塔を作る。 -/
def tw78 : List Nat → BT
  | [] => BT.zero
  | u :: r => BT.D u (tw78 r)

def bits78 : Nat → List (List Nat)
  | 0 => [[]]
  | k+1 => (bits78 k).flatMap fun l => [0 :: l, 1 :: l]

/-- 長さ `n` の `{0,1}` 列で `0` が `k` 個以下のものから作った塔。 -/
def T78 (n k : Nat) : List BT :=
  ((bits78 n).filter fun l => (l.filter (· == 0)).length ≤ k).map tw78

/-- 条項が語る側 — `ψ₀` をかぶせて Buchholz 標準。 -/
def std78 (a : BT) : Bool := BT.isStd (BT.D 0 a)

def sums2_78 (l : List BT) : List BT := l.flatMap fun x => l.map fun y => BT.sum x y
def sums3_78 (l : List BT) : List BT :=
  l.flatMap fun x => l.flatMap fun y => l.map fun z => BT.sum x (BT.sum y z)

/-- `ψ₀` を `ψ_u` に差し替える — **上限より先の添字**を入れる操作。 -/
def bump78 (u : Nat) : BT → BT
  | .zero => .zero
  | .D 0 a => .D u a
  | .D v a => .D v (bump78 u a)
  | .sum a b => .sum (bump78 u a) b

def rawG1_78 : List BT := T78 9 9
def rawG2_78 : List BT := (sums2_78 (T78 6 1)).map fun s => BT.D 1 (BT.D 1 s)
def rawG3_78 : List BT := (sums3_78 (T78 4 1)).map fun s => BT.D 1 s
def rawG4_78 : List BT := ((List.range 5).flatMap fun n => T78 n 9)
  ++ ([3,4,5].flatMap fun k => (T78 4 1).map fun y =>
        BT.sum (tw78 (List.replicate k 1)) y)

def pop78 : List BT := (rawG1_78 ++ rawG2_78 ++ rawG3_78 ++ rawG4_78).filter std78
def bmp78 : List BT := (pop78.map (bump78 2) ++ pop78.map (bump78 3)).eraseDups
def nst78 : List BT := (rawG2_78 ++ rawG3_78).filter fun a => !(std78 a)

/-- 発火する対だけ。 -/
def fire78 (a : BT) : List (Term × Term) :=
  ((wcnf (reg 1) (toList (dict a))).1).filter fun ac => le (reg 1) ac.1
def dd78 (ac : Term × Term) : Term := mulL (mulL (reg 1) (subAP (reg 1) ac.1)) ac.2
/-- (K4) の判定器 — 定理になった側。 -/
def k4b78 (ac : Term × Term) : Bool :=
  (sub1 (dd78 ac) == dd78 ac) || ((Kset (reg 1) ac.1 ++ Kset (reg 1) ac.2).isEmpty)
/-- 三つの母集団の発火する対をぜんぶ。 -/
def allp78 : List (Term × Term) := (pop78 ++ bmp78 ++ nst78).flatMap fire78

-- 母集団の大きさ。
#guard [(rawG1_78.filter std78).length, (rawG2_78.filter std78).length,
        (rawG3_78.filter std78).length, (rawG4_78.filter std78).length] == [42, 24, 32, 31]
#guard pop78.length == 129
#guard bmp78.length == 217
#guard nst78.length == 118
#guard (pop78.flatMap fire78).length == 102
#guard (bmp78.flatMap fire78).length == 217
#guard (nst78.flatMap fire78).length == 110
-- 段と標準性。
#guard pop78.all (btLe72 1)
#guard nst78.all (btLe72 1)
-- `ψ₀` を持たない塔は `bump78` で変わらない。段の上限を本当に外れるのは 176 個。
#guard (bmp78.filter (btLe72 1)).length == 41
#guard ((bmp78.filter fun a => !(btLe72 1 a)).flatMap fire78).length == 176
#guard (((bmp78.filter (btLe72 1)).flatMap fire78).filter fun ac =>
  !((Kset (reg 1) ac.1 ++ Kset (reg 1) ac.2).all fun y => lt y (dd78 ac))).length == 0

/-! **肯定 1 — 領域の中では (K2') も (K4) も落ちない。`K` は空回りしていない。**
102 歩のうち 19 歩で `K_{Ω₁} aV` が、12 歩で `K_{Ω₁} cV` が空でない。 -/

#guard (pop78.filter fun a => !(k2b78 0 (dict a))).length == 0
#guard ((pop78.flatMap fire78).filter fun ac => !(k4b78 ac)).length == 0
#guard ((pop78.flatMap fire78).filter fun ac =>
  !((Kset (reg 1) ac.1).isEmpty)).length == 19
#guard ((pop78.flatMap fire78).filter fun ac =>
  !((Kset (reg 1) ac.2).isEmpty)).length == 12
#guard ((pop78.flatMap fire78).map fun ac => (toStr ac.1, toStr ac.2)).eraseDups.length == 88

/-! **肯定 2 — (K4) の枝は空回りではない。** `Δ ⊖ 1 ≠ Δ` は 102 歩のうち 4 歩で起き、
そのどれでも `aV = Ω₁`・`cV = 1`・`Δ = 1` — §78.2 の証明が言うとおりの形。 -/

#guard ((pop78.flatMap fire78).filter fun ac => sub1 (dd78 ac) != dd78 ac).length == 4
#guard ((pop78.flatMap fire78).filter fun ac =>
  sub1 (dd78 ac) != dd78 ac && !(ac.1 == reg 1 && ac.2 == one && dd78 ac == one)).length == 0

/-! **否定 1 — 破れるのは (K2') の `aV` 側だけ。** 三つの母集団の 429 歩で (K2') は
87 回落ちるが、**そのすべてが `K_{Ω₁} aV ≮ Δ`**。`cV` 側は一度も落ちない。
§75.6 は和の形でしか測っていなかった。**§79 は `aV` 側を狙えばよい。** -/

#guard ((bmp78.flatMap fire78).filter fun ac =>
  !((Kset (reg 1) ac.1 ++ Kset (reg 1) ac.2).all fun y => lt y (dd78 ac))).length == 83
#guard ((nst78.flatMap fire78).filter fun ac =>
  !((Kset (reg 1) ac.1 ++ Kset (reg 1) ac.2).all fun y => lt y (dd78 ac))).length == 4
#guard (((bmp78 ++ nst78 ++ pop78).flatMap fire78).filter fun ac =>
  !((Kset (reg 1) ac.2).all fun y => lt y (dd78 ac))).length == 0
#guard (((bmp78 ++ nst78 ++ pop78).flatMap fire78).filter fun ac =>
  !((Kset (reg 1) ac.1).all fun y => lt y (dd78 ac))).length == 87

/-! **否定 2 — (K2') を担ぐ側条件は `BT.isStd` であって段の上限ではない。**
添字を 2・3 に上げても標準なままの 51 個では (K2') は一度も落ちない。段の上限を
満たしたまま標準でない 118 個では 4 回落ちる。 -/

#guard (bmp78.filter std78).length == 51
#guard (((bmp78.filter std78).flatMap fire78).filter fun ac =>
  !((Kset (reg 1) ac.1 ++ Kset (reg 1) ac.2).all fun y => lt y (dd78 ac))).length == 0
#guard (nst78.filter fun a => !(k2b78 0 (dict a))).length == 4

/-! **否定 3 — (K4) は三つの母集団のどこでも落ちない。** 定理なのだから当然だが、
**測ったのは定理を書く前**で、これが (K4) を狙った理由。 -/

#guard (((bmp78 ++ nst78 ++ pop78).flatMap fire78).filter fun ac => !(k4b78 ac)).length == 0

/-! **否定 4 — §73.7 の (K2) 「`K_{Ω₁} aV < aV`」はこの母集団でも偽、そして
`Δ` と比べる形とは一致しない。** 429 歩で (K2) は 92 回、(K2') は 87 回落ち、**5 歩で
食い違う** — 領域の中の 102 歩でも (K2) は 5 回落ち、(K2') は 0 回。§75.4c が
深さ 9 の塔で見たことが、幅 2・3 の和でも同じ形で起きる。 -/

#guard (allp78.filter fun ac => !(KOK73 ac.1)).length == 92
#guard (allp78.filter fun ac => !((Kset (reg 1) ac.1).all fun y => lt y (dd78 ac))).length == 87
#guard (allp78.filter fun ac =>
  KOK73 ac.1 != ((Kset (reg 1) ac.1).all fun y => lt y (dd78 ac))).length == 5
#guard ((pop78.flatMap fire78).filter fun ac => !(KOK73 ac.1)).length == 5
#guard ((pop78.flatMap fire78).filter fun ac => !(KOK73 ac.2)).length == 0

/-! **肯定 3 — 残る条項は `Δ` ひとつについての 2.1(vi) と一致する (測定のみ)。**
`K_{Ω₁} Δ ⊆ K_{Ω₁} aV ∪ K_{Ω₁} cV` は §75.2 の定理 (`mem_Kset_ddOf75`)。逆の包含は
429 歩すべてで成り立ち、判定は一度も食い違わない。155 歩で `K_{Ω₁} Δ` は空でないから
空回りでもない。**§79 は「対」ではなく「一項 `Δ`」を相手にすればよい。** -/

#guard (allp78.filter fun ac => !((Kset (reg 1) ac.1 ++ Kset (reg 1) ac.2).all fun y =>
  y ∈ Kset (reg 1) (dd78 ac))).length == 0
#guard (allp78.filter fun ac => !((Kset (reg 1) (dd78 ac)).all fun y =>
  y ∈ Kset (reg 1) ac.1 ++ Kset (reg 1) ac.2)).length == 0
#guard (allp78.filter fun ac =>
  ((Kset (reg 1) ac.1 ++ Kset (reg 1) ac.2).all fun y => lt y (dd78 ac))
    != KOK73 (dd78 ac)).length == 0
#guard (allp78.filter fun ac => !((Kset (reg 1) (dd78 ac)).isEmpty)).length == 155

/-! **肯定 4 — §75.6 の (K3) はこの母集団でも 429 歩で無条件。証明はしていない。**
`aV ≤ Δ` の方は 8 歩で落ちる — §75.4c が (K5) を捨てた理由。 -/

#guard (allp78.filter fun ac => !(le ac.2 (dd78 ac))).length == 0
#guard (allp78.filter fun ac => !(le ac.1 (dd78 ac))).length == 8

/-- **否定 2、定理の形。** 段 1 以下で、`BT` そのものは Buchholz 標準なのに `ψ₀` を
    かぶせると標準でなくなる項があり、そこで (K2') は破れる。§75.6 の `wStep75` の
    現象が幅 2 で起きたもので、`wStep75` 自身は塔だった。 -/
def kBad78 : BT :=
  BT.D 1 (BT.D 1 (BT.sum (BT.D 1 (BT.D 1 (BT.D 0 (BT.D 1 (BT.D 1 (BT.D 1 BT.zero))))))
    (BT.D 0 (BT.D 1 (BT.D 1 (BT.D 1 (BT.D 1 (BT.D 1 BT.zero))))))))

theorem not_k2_kBad78 :
    btLe72 1 kBad78 = true ∧ BT.isStd kBad78 = true ∧
    BT.isStd (BT.D 0 kBad78) = false ∧ k2b78 0 (dict kBad78) = false :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **肯定、定理の形 (深さ)。** `ψ` の入れ子 9 段の塔。`K_{Ω₁} aV` は空でない。
    §78.4 の判定器 — `⊖ 1` を見ない方 — だけで門が出る。 -/
def wOK78 : BT :=
  BT.D 1 (BT.D 1 (BT.D 1 (BT.D 0 (BT.D 1 (BT.D 1 (BT.D 1 (BT.D 0 (BT.D 0 BT.zero))))))))

theorem ksetStepOK_wOK78 : KsetStepOK 0 (dict wOK78) :=
  ksetStepOK_of_k2b78 (by decide) (by decide) (by decide)

/-- **肯定、定理の形 (幅)。** 二項和の上。 -/
def wWide78 : BT :=
  BT.D 1 (BT.D 1 (BT.sum (BT.D 1 (BT.D 1 (BT.D 1 (BT.D 1 (BT.D 1 (BT.D 0 BT.zero))))))
    (BT.D 1 (BT.D 1 (BT.D 0 (BT.D 1 (BT.D 1 (BT.D 1 BT.zero))))))))

theorem ksetStepOK_wWide78 : KsetStepOK 0 (dict wWide78) :=
  ksetStepOK_of_k2b78 (by decide) (by decide) (by decide)

/-- 系 — 2.1(vi) の `K` の連言も同じ道で出る。 -/
theorem ksetIdxOK_wOK78 : KsetIdxOK 0 (dict wOK78) :=
  ksetIdxOK_of_stepOK 0 (dict wOK78) ksetStepOK_wOK78

/-! §75.6 の母集団でも同じことを確かめておく。`hotD75` の 325 歩で (K4) は
27 歩で発火し、そのどれでも両方の `K` が空 — §78.2 が証明した形。 -/

#guard ((hotD75.flatMap fires73).filter fun p => sub1 (dd73 p) != dd73 p).length == 27
#guard ((hotD75.flatMap fires73).filter fun p =>
  sub1 (dd73 p) != dd73 p && !(k4b78 p.2)).length == 0
#guard ((stdE75.flatMap fires73).filter fun p => !(k4b78 p.2)).length == 0

end

/-! ### §78.6 公理 -/

/-! ## §79 TWO OF THE HEAD COMPARISON'S THREE HALVES ARE THEOREMS

§77 reduced `Trans/Dict.lean`'s acceptance record item (C) to ONE named hypothesis,
`DictHeadLt77`, and split it into two halves — `CollapseMono77` (equal subscripts) and
`DictCross77` (different subscripts, which the level bound forces to be the single
inequality `ψ₀(α) < ψ₁(β)`).  It proved the `u = v = 1` case of the first half only
NON-STRICTLY (`le_collapse1_77`) and named the gap exactly: the strictness of `ω^·` on
𝔗(M), the analogue of `CNVOps` §29's D3, which §65.3 deliberately stopped short of
because every consumer it had needed only `le`.

**§79 closes that gap, the half it was blocking, and the cross half as well.**  What is
left of the oldest unproved claim in the file is ONE statement: `collapse 0` preserves the
order of its argument's image — the Veblen / `ψ_{Z0}` fold.

WHAT IS PROVED.

  §79.1  **D3 ON 𝔗(M).**  `dnArg_ne_inT79` : `x` not a fixed point of `ω^·` and `x < y`
         forces `dnArg x ≠ dnArg y`.  The proof is `CNVOps` §29's, one notch up, and the
         work is exactly where §65 said it would be: at `CNV` the re-count fires only on
         `φ̄(d,e)` with `d ≠ 0`, at `inT` it fires on every STRONGLY CRITICAL `γ` too, so
         `dnArg_or79` has to produce `TM.Term.isFP zero γ` rather than a `φ̄` shape, and
         `splitFin_plus_ofNat79` / `splitFin_fst_last79` are the `inT` versions of the two
         `splitFin` facts that pin `x = γ ⊕ (m-1)`.

  §79.2  **`ω^·` IS STRICTLY MONOTONE ON 𝔗(M).**  `lt_omegaNF_inT79`.  Of §65.3's seven
         branches exactly ONE was losing strictness — both sides ordinary terms, where the
         comparison is `φ̄0(dnArg x)` against `φ̄0(dnArg y)`.  D1 and D2 give `≤` there and
         §79.1 rules out the equality.  The other six were strict already.

  §79.3  **`plus e ·` IS STRICTLY MONOTONE ON 𝔗(M).**  `plus_smono_right_inT79`.  §65.4's
         proof re-run with `lt` — three places had been weakened to `le` and all three were
         strict to begin with (`lt_head_add`, §77.2's `lt_add_tail77`, `lt_of_hd_lt`).

  §79.4  **THE `u = v = 1` HALF.**  `omPlusMono79 : PsiIdxOKStd172 → OmPlusMono77`, hence
         `collapseMono1_79`.  This is `le_collapse1_77` with §79.3 into §79.2 instead of
         §65.4 into §65.3.

  §79.5  **`ltM_·` RE-RUN AT `Ω₁`.**  The `M`-bound family of §64.2 (`lt_plus_M`,
         `ltM_phiNF`, `ltM_omegaNF`, `ltM_sub1`, …) has an `Ω₁` twin, with three
         differences and no more: `φ̄αβ < Z0` needs BOTH arguments below (2.3.5, where
         `φ̄αβ < M` was free); `ψ_{Ω₁}(ι) < Ω₁` comes from 2.3.8's `κ ≤ γ` branch and needs
         nothing of `ι`; and `ω^·`'s `ω̄^·` branch cannot fire because `x < Ω₁ < M`.  The
         last of these is `ltW_omegaNF79` — `Ω₁` is an ε-number.

  §79.6  **`ψ₀` LANDS BELOW `Ω₁`.**  `lt_collapse0_W79` : `PsiIdxOK 0 x → collapse 0 x < Ω₁`.
         `wcnf_W79` bounds the base-`Ω₁` CNF's coefficients and tail, and `foldW79` runs
         `StW79` — "the accumulator is in 𝔗(M) and below `Ω₁`" — along the same fold that
         §64.5's `StInv` runs.  The strongly critical branch needs NO side condition beyond
         the `PsiIdxOK` that the fold already consumes; the Veblen branch is 2.3.5 applied
         to `φ̄` with both arguments below.

  §79.7  **THE CROSS HALF.**  `dictCross79 : PsiIdxOKStd172 → DictCross77`, from §79.6 and
         `Ω₁ = ω^Ω₁ ≤ ω^(Ω₁+β) = ψ₁(β)` (`le_reg1_plus79`, `omegaNF_reg1_79`,
         `le_reg1_collapse1_79`, on §77.7's closed form for `ψ₁`).

  §79.8  **WHAT ROW 326 NOW WAITS FOR.**  `dictHeadLt79 (Hp : PsiIdxOKStd172)
         (H0 : CollapseMono0_79) : DictHeadLt77`, and through §77 and §76:
         `dictLtA74_79`, `vOfLtA71_79`, `limDecS1_79`, `limIncS1_79`, `certIn_t326_79`.

WHAT IS **NOT** CLAIMED.  `CollapseMono0_79` — `collapse 0` preserving the order — is NOT
proved and is stated as a named hypothesis, not smuggled in.  Nothing here proves
`PsiIdxOKStd172`, `CofDenseS1` or `BCofIn71`.  §79.6 is a bound on `collapse 0`, not a
monotonicity of it, and the two do not imply each other.

WHAT THE MEASUREMENT SAYS (§79.9 gives the construction).  **The negatives first.**

  * **D3's side condition is load-bearing, and its worst case is a `ψ`.**  On the 333
    `inT` terms, `dnArg` collapses NO pair once `isFP zero x = false` is demanded and **26
    pairs** once it is dropped.  The smallest witness is `x = ε₀`, `y = ε₀ ⊕ 1`; the third
    is `x = Γ₀ = ψ_{Z0}(0)` — the branch `CNV` never sees, which is precisely why §65.3
    could not reuse `CNVOps` §29 as it stood.
  * **`collapse 0`'s monotonicity still needs the `K`-condition, and depth makes it worse.**
    With `BT.isStd (ψ₀ ·)` demanded of both sides, 0 inversions; with it dropped, **66**.
    §77 measured 28 on a corpus nesting 5 deep; at 9 deep it is 66.  `collapse 1` inverts
    0 either way — §79.4 is a theorem.
  * **Standardness is not optional, and §77 under-measured it too.**  On the level-bounded
    but NOT standard population (109 terms, 11881 pairs) `dict` inverts **211** pairs;
    §77's 24-term version of the same population inverted 35.

  The positives.  `DictCross77` (§79.7) holds on all three populations with 0 inversions;
  `collapse 0 (dict a) < Ω₁` and `Ω₁ ≤ collapse 1 (dict a)` hold on all 127 terms, the 18
  region-outside ones included; `ω^·` is strictly monotone on 110889 `inT` pairs and on
  200704 pairs when 115 non-`inT` terms are mixed in; `plus e ·` on 84³ triples.
-/

/-! ### §79.1 D3 の 𝔗(M) 版 — `dnArg` は 2 つの引数を潰さない -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- `le` の反対称性 — 𝔗(M) の上で。 -/
theorem le_antisymm_inT79 {a b : Term} (ha : inT a = true) (hb : inT b = true)
    (h1 : le a b = true) (h2 : le b a = true) : a = b := by
  by_cases hab : a = b
  · exact hab
  · exfalso
    have l1 : lt a b = true := lt_of_le_of_ne h1 hab
    have l2 : lt b a = true := lt_of_le_of_ne h2 (fun hc => hab hc.symm)
    rw [lt_asymm_inT ha hb l1] at l2
    exact Bool.noConfusion l2

/-- `isFP zero` の十分条件 — 強臨界項。𝔗(M) で `isFixP` が広がるのはここ。 -/
theorem isFP_zero_of_sc79 {g : Term} (hsc : g.isSC = true) (hlt : lt zero g = true) :
    TM.Term.isFP zero g = true := by
  unfold TM.Term.isFP
  rw [hsc, hlt]
  rfl

/-- `isFP zero (φ̄cd)` は `0 < c` そのもの。 -/
theorem isFP_zero_phi_iff79 (c d : Term) :
    TM.Term.isFP zero (phi c d) = lt zero c := rfl

theorem lt_zero_sc79 {g : Term} (h : g ≠ zero) : lt zero g = true := lt_zero_left h

/-- 数え直しが起きなければ `dnArg` は恒等。 -/
theorem dnArg_self_of_not_isFP79 {x g : Term} {m : Nat} (hs : splitFin x = (g, m))
    (hfp : TM.Term.isFP zero g = false) : dnArg x = x := by
  unfold dnArg
  rw [hs]
  dsimp only
  split
  · cases g with
    | zero => rfl
    | omg _ => rfl
    | add _ _ => rfl
    | M =>
        rw [isFP_zero_of_sc79 rfl
          (lt_zero_sc79 (by intro hc; exact Term.noConfusion hc))] at hfp
        exact Bool.noConfusion hfp
    | psi _ _ =>
        rw [isFP_zero_of_sc79 rfl
          (lt_zero_sc79 (by intro hc; exact Term.noConfusion hc))] at hfp
        exact Bool.noConfusion hfp
    | Z _ =>
        rw [isFP_zero_of_sc79 rfl
          (lt_zero_sc79 (by intro hc; exact Term.noConfusion hc))] at hfp
        exact Bool.noConfusion hfp
    | phi c d =>
        dsimp only
        rw [if_neg (by rw [show lt zero c = false from hfp]; exact Bool.noConfusion)]
  · rfl

/-- `dnArg` の枝を、数え直しが起きた側の形つきで。**側条件なし。** -/
theorem dnArg_or79 {x g : Term} {m : Nat} (hs : splitFin x = (g, m)) :
    dnArg x = x ∨ (1 ≤ m ∧ TM.Term.isFP zero g = true
                   ∧ dnArg x = plus g (ofNat (m - 1))) := by
  rcases dnArg_or hs with h | ⟨hm, h⟩
  · exact Or.inl h
  · by_cases hfp : TM.Term.isFP zero g = true
    · exact Or.inr ⟨hm, hfp, h⟩
    · exact Or.inl (dnArg_self_of_not_isFP79 hs (bool_false hfp))

/-- 数え直しが起きる形での `dnArg` の値。 -/
theorem dnArg_recount79 {x g : Term} {k : Nat} (hs : splitFin x = (g, k + 1))
    (hfp : TM.Term.isFP zero g = true) : dnArg x = plus g (ofNat k) := by
  unfold dnArg
  rw [hs]
  dsimp only
  rw [if_pos (by omega : 1 ≤ k + 1)]
  cases g with
  | zero => exact Bool.noConfusion hfp
  | omg _ => exact Bool.noConfusion hfp
  | add _ _ => exact Bool.noConfusion hfp
  | M =>
      dsimp only
      rw [if_pos (show ((M : Term).isSC && lt zero M) = true from by
        rw [show ((M : Term).isSC) = true from rfl,
          lt_zero_sc79 (by intro hc; exact Term.noConfusion hc)]; rfl)]
      rfl
  | psi j a =>
      dsimp only
      rw [if_pos (show ((psi j a).isSC && lt zero (psi j a)) = true from by
        rw [show ((psi j a).isSC) = true from rfl,
          lt_zero_sc79 (by intro hc; exact Term.noConfusion hc)]; rfl)]
      rfl
  | Z e =>
      dsimp only
      rw [if_pos (show ((Z e).isSC && lt zero (Z e)) = true from by
        rw [show ((Z e).isSC) = true from rfl,
          lt_zero_sc79 (by intro hc; exact Term.noConfusion hc)]; rfl)]
      rfl
  | phi c d =>
      dsimp only
      rw [if_pos (show lt zero c = true from hfp)]
      rfl

/-- `γ ⊕ k` の `splitFin` は `(γ, k)` — 𝔗(M) 版。 -/
theorem splitFin_plus_ofNat79 {g : Term} (hg : inT g = true)
    (hlast : ∀ a, ((toList g).reverse).head? = some a → (a == one) = false) (k : Nat) :
    splitFin (plus g (ofNat k)) = (g, k) := by
  have hspec := toList_plus_ofNat_inT hg k
  have hrev : (toList (plus g (ofNat k))).reverse
      = List.replicate k one ++ (toList g).reverse := by
    rw [hspec, List.reverse_append, List.reverse_replicate]
  have hm : ((toList (plus g (ofNat k))).reverse.takeWhile (fun x => x == one)).length = k := by
    rw [hrev, takeWhile_replicate_append _ hlast k, List.length_replicate]
  show (ofList ((toList (plus g (ofNat k))).take
      ((toList (plus g (ofNat k))).length
        - ((toList (plus g (ofNat k))).reverse.takeWhile (fun x => x == one)).length)),
    ((toList (plus g (ofNat k))).reverse.takeWhile (fun x => x == one)).length) = (g, k)
  rw [hm, take_of_append_replicate hspec.symm, inT_ofList_toList g hg]

/-- `splitFin` の第 1 成分の末尾は `1` ではない — 𝔗(M) 版。 -/
theorem splitFin_fst_last79 {y g : Term} {m : Nat} (hy : inT y = true)
    (hs : splitFin y = (g, m)) :
    ∀ a, ((toList g).reverse).head? = some a → (a == one) = false := by
  have hgf : g = ofList (((toList y).reverse.dropWhile (fun x => x == one)).reverse) := by
    have h0 := splitFin_fst y; rw [hs] at h0; exact h0
  have hF1 : ((toList y).reverse.dropWhile (fun x => x == one)).reverse
      ++ List.replicate (((toList y).reverse.takeWhile (fun x => x == one)).length) one
      = toList y := by
    have h0 := trailing_ones (toList y).reverse
    rwa [List.reverse_reverse] at h0
  have hAP : ∀ x ∈ ((toList y).reverse.dropWhile (fun x => x == one)).reverse,
      x.isAP = true := by
    intro x hx
    exact inTL_isAP hy x (by rw [← hF1]; exact List.mem_append_left _ hx)
  have hgl : toList g = ((toList y).reverse.dropWhile (fun x => x == one)).reverse := by
    rw [hgf, toList_ofList _ hAP]
  intro a ha
  rw [hgl, List.reverse_reverse] at ha
  exact head?_dropWhile _ a ha

/-- **D3 の 𝔗(M) 版。** `x` が `ω^·` の不動点でなく `x < y` なら
    `dnArg x ≠ dnArg y`。§65.3 が避けた一点。 -/
theorem dnArg_ne_inT79 {x y : Term} (hx : inT x = true) (hy : inT y = true)
    (hfx : TM.Term.isFP zero x = false) (h : lt x y = true) : dnArg x ≠ dnArg y := by
  intro heq
  have hle1 : le (dnArg x) x = true := dnArg_le_inT hx
  have hle2 : le x (dnArg y) = true := dnArg_ge_inT hx hy h
  rw [← heq] at hle2
  have hxeq : dnArg x = x := le_antisymm_inT79 (inT_dnArg hx) hx hle1 hle2
  have hdy : dnArg y = x := heq.symm.trans hxeq
  cases hs : splitFin y with
  | mk g m =>
    have hcg : inT g = true := by have h0 := inT_splitFin hy; rw [hs] at h0; exact h0
    rcases dnArg_or79 hs with hd | ⟨_, hgfp, hdny⟩
    · rw [hd] at hdy
      rw [← hdy, lt_irrefl] at h
      exact Bool.noConfusion h
    · have hxval : x = plus g (ofNat (m - 1)) := by rw [← hdy, hdny]
      have hlast := splitFin_fst_last79 hy hs
      have hsx : splitFin x = (g, m - 1) := by
        rw [hxval]; exact splitFin_plus_ofNat79 hcg hlast (m - 1)
      cases hk : m - 1 with
      | zero =>
        have hxg : x = g := by rw [hxval, hk]; rfl
        rw [hxg, hgfp] at hfx
        exact Bool.noConfusion hfx
      | succ k =>
        rw [hk] at hsx
        have hdx : dnArg x = plus g (ofNat k) := dnArg_recount79 hsx hgfp
        rw [hxeq, hxval, hk] at hdx
        have h1 := toList_plus_ofNat_inT hcg (k + 1)
        have h2 := toList_plus_ofNat_inT hcg k
        rw [hdx, h2] at h1
        have hlen := congrArg List.length h1
        rw [List.length_append, List.length_append, List.length_replicate,
          List.length_replicate] at hlen
        omega

end

/-! ### §79.2 `ω^·` は 𝔗(M) の上で**狭義**単調

§65.3 の `le_omegaNF_of_lt_inT` の 7 分岐のうち、非狭義でしか結論が出ていなかったのは
最後の 1 つ — 両辺とも不動点でない枝 — だけである。そこは `φ̄0(dnArg x)` と
`φ̄0(dnArg y)` の比較で、D1・D2 が `dnArg x ≤ dnArg y` を与え、§79.1 の D3 が
等号を排除する。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- **`ω^·` は 𝔗(M) の上で狭義単調。** §65.3 の `le` 版に D3 を足しただけ。 -/
theorem lt_omegaNF_inT79 {x y : Term} (hx : inT x = true) (hy : inT y = true)
    (h : lt x y = true) : lt (omegaNF x) (omegaNF y) = true := by
  rw [omegaNF_eq_gen x, omegaNF_eq_gen y]
  by_cases hMy : lt M y = true
  · rw [if_pos hMy]
    by_cases hMx : lt M x = true
    · rw [if_pos hMx]; exact lt_omg_omg h
    · rw [if_neg hMx]
      by_cases hfx : TM.Term.isFP zero x = true
      · rw [if_pos hfx]; exact lt_isFP_omg hfx
      · rw [if_neg hfx]; exact lt_phi_omg _ _ _
  · rw [if_neg hMy]
    have hMx : ¬ (lt M x = true) := by
      intro hc
      exact hMy (lt_trans_inT inT_M hx hy hc h)
    rw [if_neg hMx]
    have hxM : x ≠ M := by
      intro hc
      rw [hc] at h
      exact hMy h
    by_cases hfx : TM.Term.isFP zero x = true
    · rw [if_pos hfx]
      by_cases hfy : TM.Term.isFP zero y = true
      · rw [if_pos hfy]; exact h
      · rw [if_neg hfy]
        exact lt_isFP_phi_zero hfx hxM (dnArg_ge_inT hx hy h)
    · rw [if_neg hfx]
      by_cases hfy : TM.Term.isFP zero y = true
      · rw [if_pos hfy]
        refine lt_phi_zero_isFP hfy ?_
        exact lt_of_le_of_lt3 (inT_le_fragR _ (inT_dnArg hx)) (inT_le_fragR x hx)
          (inT_le_fragR y hy) (dnArg_le_inT hx) h
      · rw [if_neg hfy]
        refine lt_phi_arg ?_
        refine lt_of_le_of_ne (le_trans_inT (inT_dnArg hx) hx (inT_dnArg hy)
          (dnArg_le_inT hx) (dnArg_ge_inT hx hy h)) ?_
        exact dnArg_ne_inT79 hx hy (bool_false hfx) h

end

/-! ### §79.3 `plus e ·` は**狭義**単調

§65.4 の `plus_mono_right_inT` の証明をそのまま `lt` で走らせる。分岐は同じ 6 つで、
`le_add_tail` が §77.2 の `lt_add_tail77` に、`le_of_lt (lt_head_add ·)` が
`lt_head_add` そのものに置き換わるだけ — つまり非狭義に落としていた場所が 3 つあり、
どれももとから狭義だった。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

theorem plus_smono_step79 {e e' e1 : Term} {E' : List Term} (he : inT e = true)
    (hE : toList e = e1 :: E') (hE' : ofList E' = e')
    (ih : ∀ x y, inT x = true → inT y = true → lt x y = true →
        lt (plus e' x) (plus e' y) = true) :
    ∀ (x y : Term), inT x = true → inT y = true → lt x y = true →
      lt (plus e x) (plus e y) = true := by
  intro x y hx hy h
  have hap1 : e1.isAP = true := inTL_isAP he e1 (by rw [hE]; exact List.Mem.head _)
  have hi1 : inT e1 = true := inTL_inT he e1 (by rw [hE]; exact List.Mem.head _)
  have hee : e = ofList (e1 :: E') := by rw [← hE, inT_ofList_toList e he]
  cases hX : toList x with
  | nil =>
    have hxz : x = zero := toList_eq_nil x hX
    subst hxz
    show lt e (plus e y) = true
    cases hY : toList y with
    | nil =>
      exfalso
      have hyz : y = zero := toList_eq_nil y hY
      rw [hyz, lt_irrefl] at h
      exact Bool.noConfusion h
    | cons y1 Y' =>
      have hyne : y ≠ zero := by
        intro hc
        rw [hc] at hY
        exact List.cons_ne_nil y1 Y' (show y1 :: Y' = ([] : List Term) from hY.symm)
      have hiy1 : inT y1 = true := inTL_inT hy y1 (by rw [hY]; exact List.Mem.head _)
      rw [plus_cons he hy hE hE' hY]
      by_cases hle : le y1 e1 = true
      · rw [if_pos hle]
        cases hEc : E' with
        | nil =>
          rw [hEc] at hee
          rw [show e = e1 from hee]
          exact lt_head_add hap1 _
        | cons f F =>
          rw [hEc] at hee hE'
          have hee2 : e = add e1 e' := by rw [hee, ← hE']; rfl
          rw [hee2]
          refine lt_add_tail77 ?_
          exact ih zero y inT_zero hy (lt_zero_left hyne)
      · rw [if_neg hle]
        refine lt_of_hd_lt he hy hE hY ?_
        exact lt_of_not_le_inT hiy1 hi1 (bool_false hle)
  | cons x1 X' =>
    have hix1 : inT x1 = true := inTL_inT hx x1 (by rw [hX]; exact List.Mem.head _)
    rw [plus_cons he hx hE hE' hX]
    cases hY : toList y with
    | nil =>
      exfalso
      have hyz : y = zero := toList_eq_nil y hY
      rw [hyz, lt_zero_right] at h
      exact Bool.noConfusion h
    | cons y1 Y' =>
      have hiy1 : inT y1 = true := inTL_inT hy y1 (by rw [hY]; exact List.Mem.head _)
      rw [plus_cons he hy hE hE' hY]
      have hxy1 : le x1 y1 = true := hd_mono_inT hx hy hX hY (le_of_lt h)
      by_cases hlx : le x1 e1 = true
      · rw [if_pos hlx]
        by_cases hly : le y1 e1 = true
        · rw [if_pos hly]
          exact lt_add_tail77 (ih x y hx hy h)
        · rw [if_neg hly]
          refine lt_add_of_lt_hd hy hY ?_
          exact lt_of_not_le_inT hiy1 hi1 (bool_false hly)
      · have hly : ¬ (le y1 e1 = true) := by
          intro hc
          exact hlx (le_trans_inT hix1 hiy1 hi1 hxy1 hc)
        rw [if_neg hlx, if_neg hly]
        exact h

/-- **`plus e ·` は狭義単調。** 側条件なし。 -/
theorem plus_smono_right_inT79 : ∀ (e : Term), inT e = true → ∀ (x y : Term), inT x = true →
    inT y = true → lt x y = true → lt (plus e x) (plus e y) = true := by
  have hzero : ∀ (x y : Term), inT x = true → inT y = true → lt x y = true →
      lt (plus zero x) (plus zero y) = true := by
    intro x y hx hy h
    rw [plus_zero_left_inT hx, plus_zero_left_inT hy]
    exact h
  intro e
  induction e with
  | zero => intro _; exact hzero
  | M => intro he; exact plus_smono_step79 he rfl rfl hzero
  | omg _ _ => intro he; exact plus_smono_step79 he rfl rfl hzero
  | phi _ _ _ _ => intro he; exact plus_smono_step79 he rfl rfl hzero
  | psi _ _ _ _ => intro he; exact plus_smono_step79 he rfl rfl hzero
  | Z _ _ => intro he; exact plus_smono_step79 he rfl rfl hzero
  | add u v _ ihv =>
    intro he
    obtain ⟨_, _, hiv, _⟩ := inT_add he
    exact plus_smono_step79 he rfl (inT_ofList_toList v hiv) (ihv hiv)

end

/-! ### §79.4 `u = v = 1` の半分は定理になった

§77.8 の `le_collapse1_77` が `≤` で止めていたところに §79.2 と §79.3 を入れるだけ。
`OmPlusMono77` — §77 が「`ω^(Ω₁+·)` の単調性そのもの」と書いた仮説 — が消える。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- **§79 の第一の主定理。** §77.8 の `OmPlusMono77` は定理である。 -/
theorem omPlusMono79 (Hp : PsiIdxOKStd172) : OmPlusMono77 := by
  intro a b hbA hbB hsA hsB h
  have hia := (inT_dict_of_std172 Hp a (btLe72_D 1 1 a hbA).2 (isStd_of_D hsA)).1
  have hib := (inT_dict_of_std172 Hp b (btLe72_D 1 1 b hbB).2 (isStd_of_D hsB)).1
  exact lt_omegaNF_inT79 (inT_plus (inT_reg 1) hia) (inT_plus (inT_reg 1) hib)
    (plus_smono_right_inT79 (reg 1) (inT_reg 1) (dict a) (dict b) hia hib h)

/-- **`CollapseMono77` の `u = 1` の半分。** §77.8 の `le_collapse1_77` の狭義版。 -/
theorem collapseMono1_79 (Hp : PsiIdxOKStd172) :
    ∀ (a b : BT), btLe72 1 (BT.D 1 a) = true → btLe72 1 (BT.D 1 b) = true →
      BT.isStd (BT.D 1 a) = true → BT.isStd (BT.D 1 b) = true → lt (dict a) (dict b) = true →
      lt (collapse 1 (dict a)) (collapse 1 (dict b)) = true :=
  collapseMono1_of77 Hp (omPlusMono79 Hp)

/-- **残るのは `u = v = 0` の Veblen 折り畳みと段をまたぐ 1 本だけ。** -/
theorem dictHeadLt_of_zero79 (Hp : PsiIdxOKStd172) (H1 : DictCross77)
    (H0 : ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
      BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true → lt (dict a) (dict b) = true →
      lt (collapse 0 (dict a)) (collapse 0 (dict b)) = true) : DictHeadLt77 :=
  dictHeadLt_of_split77 H1 (collapseMono_of_split77 H0 (collapseMono1_79 Hp))

end

/-! ### §79.5 `Ω₁` の下に留まる — `ltM_·` の一族をそのまま `Ω₁` で走らせる

段をまたぐ半分 `ψ₀(α) < ψ₁(β)` は、`ψ₀` の像が `Ω₁` の下にあること 1 本に落ちる
(§79.7)。そのために §64.2 の `ltM_phiNF`・`ltM_omegaNF`・`lt_plus_M` … の一族を
`M` の代わりに `Ω₁ = reg 1 = Z 0` で走らせる。違いは 3 か所しかない:

  * `lt (φ̄αβ) M` は無条件 (2.3.2) だが `lt (φ̄αβ) (Z 0)` は両引数が下であることを
    要求する (2.3.5) — `lt_phi_Z_of`;
  * `lt (ψκα) M` は無条件だが `lt (ψ_{Ω₁}α) (Ω₁)` は 2.3.8 の `κ ≤ γ` の枝で来る;
  * `ω^·` の `ω̄^·` 枝は `M < x` を要求するので、`x < Ω₁ < M` から潰れる。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open Trans.Dict (sub1 subAP logOm divAP mulL)
open TM TM.Term
open Evidence.WF

theorem inT_W79 : inT (reg 1) = true := inT_reg 1
theorem ltM_W79 : lt (reg 1) M = true := ltM_reg 1

theorem lt_zero_W79 : lt zero (reg 1) = true :=
  lt_zero_left (by intro hc; exact Term.noConfusion hc)

theorem ltM_of_ltW79 {t : Term} (ht : inT t = true) (h : lt t (reg 1) = true) :
    lt t M = true := lt_trans_inT ht inT_W79 inT_M h ltM_W79

theorem lt_add_W79 (a b : Term) : lt (add a b) (reg 1) = lt a (reg 1) :=
  lt_add_nsum (by intro hc; exact Term.noConfusion hc) rfl

theorem lt_phi_W79 {a b : Term} (h1 : lt a (reg 1) = true) (h2 : lt b (reg 1) = true) :
    lt (phi a b) (reg 1) = true := lt_phi_Z_of h1 h2

theorem lt_one_W79 : lt TM.Term.one (reg 1) = true := lt_phi_W79 lt_zero_W79 lt_zero_W79

/-- **2.3.8 の枝。** `ψ_{Ω₁}(ι) < Ω₁` — 添字について何も要らない。 -/
theorem lt_psi_W79 (i : Term) : lt (psi (reg 1) i) (reg 1) = true := by
  show lt (psi (Z zero) i) (Z zero) = true
  rw [lt_eq_ltF_succ, ltF_succ_psi_Z,
    if_pos (by rw [show ((Z zero : Term) == Z zero) = true from rfl, Bool.true_or])]

theorem lt_ofList_W79 : ∀ (l : List Term), (∀ x ∈ l, lt x (reg 1) = true) →
    lt (ofList l) (reg 1) = true
  | [], _ => lt_zero_W79
  | [a], h => h a (List.Mem.head _)
  | a :: b :: t, h => by
    show lt (add a (ofList (b :: t))) (reg 1) = true
    rw [lt_add_W79]
    exact h a (List.Mem.head _)

theorem lt_ofList_cons_W79 (a : Term) : ∀ (t : List Term), lt a (reg 1) = true →
    lt (ofList (a :: t)) (reg 1) = true
  | [], h => h
  | b :: u, h => by
    show lt (add a (ofList (b :: u))) (reg 1) = true
    rw [lt_add_W79]; exact h

theorem ltW_of_le79 {y a : Term} (hy : inT y = true) (ha : inT a = true)
    (hle : le y a = true) (hla : lt a (reg 1) = true) : lt y (reg 1) = true :=
  lt_of_le_of_lt3 (inT_le_fragR y hy) (inT_le_fragR a ha) (inT_le_fragR _ inT_W79) hle hla

theorem ltW_of_hdLe79 : ∀ {a b : Term}, inT a = true → inT b = true →
    hdLe b a = true → lt a (reg 1) = true → lt b (reg 1) = true := by
  intro a b hia hib hhd hla
  cases b with
  | zero => exact Bool.noConfusion hhd
  | M => exact ltW_of_le79 hib hia hhd hla
  | omg c => exact ltW_of_le79 hib hia hhd hla
  | phi c d => exact ltW_of_le79 hib hia hhd hla
  | psi c d => exact ltW_of_le79 hib hia hhd hla
  | Z c => exact ltW_of_le79 hib hia hhd hla
  | add c d =>
    obtain ⟨_, hic, _, _⟩ := inT_add hib
    rw [lt_add_W79]
    exact ltW_of_le79 hic hia hhd hla

/-- `Ω₁` より下の項の成分はすべて `Ω₁` より下。 -/
theorem ltW_toList79 : ∀ (s : Term), inT s = true → lt s (reg 1) = true →
    ∀ x ∈ toList s, lt x (reg 1) = true := by
  intro s
  induction s with
  | zero => intro _ _ x hx; cases hx
  | M => intro _ h x hx; rw [List.mem_singleton.mp hx]; exact h
  | omg a _ => intro _ h x hx; rw [List.mem_singleton.mp hx]; exact h
  | phi a b _ _ => intro _ h x hx; rw [List.mem_singleton.mp hx]; exact h
  | psi k a _ _ => intro _ h x hx; rw [List.mem_singleton.mp hx]; exact h
  | Z a _ => intro _ h x hx; rw [List.mem_singleton.mp hx]; exact h
  | add a b _ ihb =>
    intro h hl x hx
    obtain ⟨hap, hia, hib, hhd⟩ := inT_add h
    have hla : lt a (reg 1) = true := by rw [← lt_add_W79 a b]; exact hl
    have hlb : lt b (reg 1) = true := ltW_of_hdLe79 hia hib hhd hla
    rcases List.mem_cons.mp (show x ∈ a :: toList b from hx) with h1 | h1
    · rw [h1]; exact hla
    · exact ihb hib hlb x h1

theorem lt_plus_W79 {s t : Term} (hs : inT s = true) (ht : inT t = true)
    (hls : lt s (reg 1) = true) (hlt : lt t (reg 1) = true) :
    lt (plus s t) (reg 1) = true := by
  cases hl : toList t with
  | nil => rw [show plus s t = s from by unfold TM.Term.plus; rw [hl]]; exact hls
  | cons b1 rest =>
    rw [plus_eq (s := s) hl]
    refine lt_ofList_W79 _ ?_
    intro x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact ltW_toList79 s hs hls x (List.mem_filter.mp h1).1
    · exact ltW_toList79 t ht hlt x h1

theorem lt_ofNat_W79 : ∀ n, lt (ofNat n) (reg 1) = true
  | 0 => lt_zero_W79
  | n + 1 => lt_plus_W79 (inT_ofNat n) inT_one (lt_ofNat_W79 n) lt_one_W79

theorem ltW_take_ofList79 {b : Term} (h : inT b = true) (hl : lt b (reg 1) = true) (k : Nat) :
    lt (ofList ((toList b).take k)) (reg 1) = true :=
  lt_ofList_W79 _ (fun x hx => ltW_toList79 b h hl x (List.mem_of_mem_take hx))

theorem ltW_splitFin79 {b : Term} (h : inT b = true) (hl : lt b (reg 1) = true) :
    lt (splitFin b).1 (reg 1) = true := ltW_take_ofList79 h hl _

theorem ltW_dropIfHead79 {c : Term} (h : inT c = true) (hlc : lt c (reg 1) = true)
    (P : Term → Bool) :
    lt (match toList c with
        | [] => zero
        | p :: rest => if P p then ofList rest else c) (reg 1) = true := by
  cases hl : toList c with
  | nil => exact lt_zero_W79
  | cons p rest =>
    show lt (if P p = true then ofList rest else c) (reg 1) = true
    split
    · exact lt_ofList_W79 rest (fun x hx =>
        ltW_toList79 c h hlc x (by rw [hl]; exact List.Mem.tail p hx))
    · exact hlc

theorem ltW_sub1_79 {c : Term} (h : inT c = true) (hl : lt c (reg 1) = true) :
    lt (sub1 c) (reg 1) = true := ltW_dropIfHead79 h hl (fun p => p == TM.Term.one)

theorem ltW_phiNFdefault79 {a b : Term} (hla : lt a (reg 1) = true)
    (hlb : lt b (reg 1) = true) : lt (phiNFdefault a b) (reg 1) = true := by
  unfold phiNFdefault
  split
  · exact hla
  · exact lt_phi_W79 hla hlb

theorem ltW_phiNFsucc79 {a b : Term} (hib : inT b = true) (hla : lt a (reg 1) = true)
    (hlb : lt b (reg 1) = true) : lt (phiNFsucc a b) (reg 1) = true := by
  have hdef := ltW_phiNFdefault79 (b := b) hla hlb
  have hg : inT (splitFin b).1 = true := inT_splitFin hib
  have hgm : lt (splitFin b).1 (reg 1) = true := ltW_splitFin79 hib hlb
  unfold phiNFsucc
  split
  rename_i heq
  rw [heq] at hg hgm
  split
  · split <;> (split <;>
      first
        | exact lt_phi_W79 hla
            (lt_plus_W79 hg (inT_ofNat _) hgm (lt_ofNat_W79 _))
        | exact hdef)
  · exact hdef

theorem ltW_phiNF79 {a b : Term} (hib : inT b = true) (hla : lt a (reg 1) = true)
    (hlb : lt b (reg 1) = true) : lt (phiNF a b) (reg 1) = true := by
  unfold phiNF
  split
  · exact hlb
  · split
    · split
      · exact hlb
      · exact ltW_phiNFsucc79 hib hla hlb
    · exact ltW_phiNFsucc79 hib hla hlb

/-- **`Ω₁` は ε 数。** `x < Ω₁` なら `ω^x < Ω₁`。 -/
theorem ltW_omegaNF79 {x : Term} (hx : inT x = true) (hlx : lt x (reg 1) = true) :
    lt (omegaNF x) (reg 1) = true := by
  have hxM : lt x M = true := ltM_of_ltW79 hx hlx
  unfold omegaNF
  split
  · rename_i h
    exact absurd hxM (by rw [lt_asymm_inT inT_M hx h]; exact Bool.noConfusion)
  · split
    · rename_i h1 h2
      exact absurd hxM (by rw [eq_of_beq h2, lt_M_M]; exact Bool.noConfusion)
    · exact ltW_phiNF79 hx lt_zero_W79 hlx

end

/-! ### §79.6 `wcnf` と畳み込みは `Ω₁` を越えない

§64.4 の `wcnf_spec` と §64.5 の `fold_inv` を、`M` の代わりに `Ω₁` で走らせる。
係数は `ω^(w より下の部分)` なので §79.5 の ε 数性で下に留まり、畳み込みの累算器は
強臨界枝では `ψ_{Ω₁}(·)` (2.3.8 で無条件に下)、ヴェブレン枝では `φ̄` の引数が
どちらも下だから下 (2.3.5)。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open Trans.Dict (sub1 subAP logOm divAP mulL)
open TM TM.Term
open Evidence.WF

theorem ltW_wC79 {p : Term} (hp : inT p = true) : lt (wC (reg 1) p) (reg 1) = true := by
  obtain ⟨hc, hd⟩ := inT_toList _ (inT_logOm hp)
  unfold wC
  refine ltW_omegaNF79 (inT_filter_ofList hc hd _) ?_
  refine lt_ofList_W79 _ ?_
  intro x hx
  exact (List.mem_filter.mp hx).2

/-- `wcnf` の返り値が `Ω₁` の下にあること。 -/
def PairW79 (r : List (Term × Term) × Term) : Prop :=
  lt r.2 (reg 1) = true ∧ (∀ ac ∈ r.1, inT ac.2 = true ∧ lt ac.2 (reg 1) = true)

theorem wcnf_W79 : ∀ (L : List Term), inTL L = true → PairW79 (wcnf (reg 1) L) := by
  intro L
  induction L with
  | nil => intro _; exact ⟨lt_zero_W79, by intro ac hac; cases hac⟩
  | cons p rest ih =>
    intro hc
    obtain ⟨⟨hap, hip⟩, hcr⟩ := inTL_cons.mp hc
    have IH := ih hcr
    by_cases hlp : lt p (reg 1) = true
    · rw [wcnf_cons_lt hlp]
      exact ⟨lt_ofList_cons_W79 p rest hlp, by intro ac hac; cases hac⟩
    · have hlp' : lt p (reg 1) = false := bool_false hlp
      have hCi := inT_wC (w := reg 1) hip
      have hC := ltW_wC79 hip
      rw [wcnf_cons_ge hlp']
      cases hr : wcnf (reg 1) rest with
      | mk fst snd =>
        rw [hr] at IH
        obtain ⟨hs2, hall⟩ := IH
        cases fst with
        | nil =>
          refine ⟨hs2, ?_⟩
          intro ac hac
          rw [List.mem_singleton.mp hac]
          exact ⟨hCi, hC⟩
        | cons ac0 ps =>
          cases ac0 with
          | mk a' c' =>
            have hac0 := hall (a', c') (List.Mem.head _)
            show PairW79 (if (wA (reg 1) p == a') = true
              then ((wA (reg 1) p, plus (wC (reg 1) p) c') :: ps, snd)
              else ((wA (reg 1) p, wC (reg 1) p) :: (a', c') :: ps, snd))
            by_cases heq : (wA (reg 1) p == a') = true
            · rw [if_pos heq]
              refine ⟨hs2, ?_⟩
              intro ac hac
              rcases List.mem_cons.mp hac with h | h
              · rw [h]
                exact ⟨inT_plus hCi hac0.1, lt_plus_W79 hCi hac0.1 hC hac0.2⟩
              · exact hall ac (List.Mem.tail _ h)
            · rw [if_neg heq]
              refine ⟨hs2, ?_⟩
              intro ac hac
              rcases List.mem_cons.mp hac with h | h
              · rw [h]; exact ⟨hCi, hC⟩
              · exact hall ac h

/-- 畳み込みの不変量、`Ω₁` の側。累算器だけを見る。 -/
def StW79 (s : Option Term × Option Term) : Prop :=
  ∀ v, s.2 = some v → inT v = true ∧ lt v (reg 1) = true

theorem stepW79 {s : Option Term × Option Term} {ac : Term × Term}
    (hs : StW79 s) (h1 : inT ac.1 = true) (h2 : lt ac.1 M = true)
    (h3 : inT ac.2 = true) (h3w : lt ac.2 (reg 1) = true)
    (hpsi : le (reg 1) ac.1 = true → inT (psi (reg 1) (idxOf (reg 1) s ac)) = true) :
    StW79 (stepF (reg 1) (baseOf 0) s ac) := by
  unfold stepF
  split
  · rename_i hle
    intro v hq
    rw [← Option.some.inj (show some (psi (reg 1) (idxOf (reg 1) s ac)) = some v from hq)]
    exact ⟨hpsi hle, lt_psi_W79 _⟩
  · rename_i hle
    intro v hq
    have hbse : inT (match s.2 with | none => baseOf 0 | some v => v) = true ∧
        lt (match s.2 with | none => baseOf 0 | some v => v) (reg 1) = true := by
      cases hq2 : s.2 with
      | none => exact ⟨inT_baseOf 0, show lt (baseOf 0) (reg 1) = true from lt_zero_W79⟩
      | some v0 => exact hs v0 hq2
    have hcc : inT (match s.2 with | none => sub1 ac.2 | some _ => ac.2) = true ∧
        lt (match s.2 with | none => sub1 ac.2 | some _ => ac.2) (reg 1) = true := by
      cases hq2 : s.2 with
      | none => exact ⟨inT_sub1 h3, ltW_sub1_79 h3 h3w⟩
      | some v0 => exact ⟨h3, h3w⟩
    have hA : lt ac.1 (reg 1) = true := lt_of_not_le_inT inT_W79 h1 (bool_false hle)
    have hP := lt_plus_W79 hbse.1 hcc.1 hbse.2 hcc.2
    rw [← Option.some.inj (show some (phiNF ac.1
      (plus (match s.2 with | none => baseOf 0 | some v => v)
            (match s.2 with | none => sub1 ac.2 | some _ => ac.2))) = some v from hq)]
    exact ⟨inT_phiNF h1 (inT_plus hbse.1 hcc.1) h2
             (ltM_of_ltW79 (inT_plus hbse.1 hcc.1) hP),
           ltW_phiNF79 (inT_plus hbse.1 hcc.1) hA hP⟩

theorem foldW79 : ∀ (l : List (Term × Term)) (s : Option Term × Option Term), StW79 s →
    (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
    (∀ ac ∈ l, lt ac.2 (reg 1) = true) →
    (∀ p ∈ scanSt (reg 1) (baseOf 0) s l, le (reg 1) p.2.1 = true →
        inT (psi (reg 1) (idxOf (reg 1) p.1 p.2)) = true) →
    StW79 (l.foldl (stepF (reg 1) (baseOf 0)) s) := by
  intro l
  induction l with
  | nil => intro s hs _ _ _; exact hs
  | cons ac t ih =>
    intro s hs hall hallw hpsi
    have hstep : StW79 (stepF (reg 1) (baseOf 0) s ac) :=
      stepW79 hs (hall ac (List.Mem.head _)).1 (hall ac (List.Mem.head _)).2.1
        (hall ac (List.Mem.head _)).2.2.1 (hallw ac (List.Mem.head _))
        (hpsi (s, ac) (List.Mem.head _))
    exact ih (stepF (reg 1) (baseOf 0) s ac) hstep
      (fun a ha => hall a (List.Mem.tail _ ha))
      (fun a ha => hallw a (List.Mem.tail _ ha))
      (fun p hp => hpsi p (List.Mem.tail _ hp))

/-- **§79.6 の主定理。** `ψ₀` の像は `Ω₁` の下 — 崩壊関数がそもそも崩壊であること。 -/
theorem lt_collapse0_W79 (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (Hp : PsiIdxOK 0 x) : lt (collapse 0 x) (reg 1) = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨⟨h21, h22⟩, hallOK⟩ :=
    wcnf_spec_sc (inT_reg 1) (show (reg 1).isSC = true from rfl) (toList x) hc hd
      (ltM_toList x hx hlx)
  have hW := wcnf_W79 (toList x) hc
  have hinit : StW79 ((none : Option Term), (none : Option Term)) := by
    intro v h; cases h
  have hst := foldW79 (wcnf (reg 1) (toList x)).1 (none, none) hinit hallOK
    (fun ac hac => (hW.2 ac hac).2) Hp
  have hv : inT (((wcnf (reg 1) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero) = true ∧
      lt (((wcnf (reg 1) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero) (reg 1) = true := by
    cases hg : ((wcnf (reg 1) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2 with
    | none => exact ⟨inT_zero, lt_zero_W79⟩
    | some v => exact hst v hg
  rw [collapse_eq]
  refine ltW_omegaNF79 (inT_plus (inT_reg 0) (inT_plus hv.1 h21)) ?_
  exact lt_plus_W79 (inT_reg 0) (inT_plus hv.1 h21) lt_zero_W79
    (lt_plus_W79 hv.1 h21 hv.2 hW.1)

end

/-! ### §79.7 段をまたぐ半分 — `ψ₀(α) < Ω₁ ≤ ψ₁(β)`

`DictCross77` は段の上限で `u = 0`・`v = 1` に潰れる (§77.8)。そこに §79.6 の
「`ψ₀` は `Ω₁` の下」と、`Ω₁ = ω^Ω₁ ≤ ω^(Ω₁+β) = ψ₁(β)` を継ぐだけ。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- `Ω₁ ≤ Ω₁ ⊕ y` — 和が頭を落とすときも落とさないときも。 -/
theorem le_reg1_plus79 {y : Term} (hy : inT y = true) :
    le (reg 1) (plus (reg 1) y) = true := by
  cases hY : toList y with
  | nil =>
    have hyz : y = zero := toList_eq_nil y hY
    subst hyz
    show le (reg 1) (reg 1) = true
    exact Evidence.WF.le_self _
  | cons y1 Y' =>
    have hiy1 : inT y1 = true := inTL_inT hy y1 (by rw [hY]; exact List.Mem.head _)
    rw [plus_cons inT_W79 hy (show toList (reg 1) = (Z zero) :: [] from rfl) rfl hY]
    by_cases hle : le y1 (Z zero) = true
    · rw [if_pos hle]
      exact le_of_lt (lt_head_add (show ((Z zero : Term)).isAP = true from rfl) _)
    · rw [if_neg hle]
      refine le_of_lt (lt_of_lt_of_le3 (inT_le_fragR _ inT_W79) (inT_le_fragR y1 hiy1)
        (inT_le_fragR y hy) ?_ (le_hd_self_inT hy hY))
      exact lt_of_not_le_inT hiy1 inT_W79 (bool_false hle)

/-- `ω^Ω₁ = Ω₁` — 強臨界項は自分自身が `ω` の指数 (§65.3 が言う `isFixP` の拡がり)。 -/
theorem omegaNF_reg1_79 : omegaNF (reg 1) = reg 1 := by
  rw [omegaNF_eq_gen,
    if_neg (by rw [lt_asymm_inT inT_W79 inT_M ltM_W79]; exact Bool.noConfusion),
    if_pos (isFP_zero_of_sc79 (show (reg 1).isSC = true from rfl) lt_zero_W79)]

/-- `Ω₁ ≤ ψ₁(β)`。 -/
theorem le_reg1_collapse1_79 (y : Term) (hy : inT y = true)
    (hlt : ∀ p ∈ toList y, lt p (reg 2) = true) : le (reg 1) (collapse 1 y) = true := by
  have h1 : le (omegaNF (reg 1)) (omegaNF (plus (reg 1) y)) = true :=
    omegaNF_mono_inT inT_W79 (inT_plus inT_W79 hy) (le_reg1_plus79 hy)
  rw [omegaNF_reg1_79] at h1
  rw [collapse1_eq77 y hy hlt]
  exact h1

/-- **§79 の第二の主定理。** §77.8 の `DictCross77` は定理である。 -/
theorem dictCross79 (Hp : PsiIdxOKStd172) : DictCross77 := by
  refine dictCross_of01_77 ?_
  intro a b hbA hbB hsA hsB
  have hba := (btLe72_D 1 0 a hbA).2
  have hbb := (btLe72_D 1 1 b hbB).2
  have hia := inT_dict_of_std172 Hp a hba (isStd_of_D hsA)
  have hib := inT_dict_of_std172 Hp b hbb (isStd_of_D hsB)
  have h0 : lt (dict (BT.D 0 a)) (reg 1) = true := by
    rw [Trans.Dict.dict_D]
    exact lt_collapse0_W79 (dict a) hia.1 hia.2 (Hp 0 a (by omega) hba hsA)
  have h1 : le (reg 1) (dict (BT.D 1 b)) = true := by
    rw [Trans.Dict.dict_D]
    exact le_reg1_collapse1_79 (dict b) hib.1
      (fun p hp => lt_pure73_reg2 (pure73_toList _ (pure73_dict b hbb) p hp))
  exact lt_of_lt_of_le3 (inT_le_fragR _ (inT_dict_of_std172 Hp (BT.D 0 a) hbA hsA).1)
    (inT_le_fragR _ inT_W79)
    (inT_le_fragR _ (inT_dict_of_std172 Hp (BT.D 1 b) hbB hsB).1) h0 h1

end

/-! ### §79.8 残るのは Veblen の折り畳みひとつ

§77 は `DictHeadLt77` を 2 つに割った。§79.4 が `u = v = 1` を、§79.7 が段をまたぐ
半分を閉じた。残るのは `u = v = 0` — `collapse 0` の単調性、すなわち [Rathjen, 1991]
2.6(vi) の `φ̄` の再カウントと `ψ_{Z0}` の指数の折り畳みである。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- `u = v = 0` の半分。**証明していない。** -/
def CollapseMono0_79 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true → lt (dict a) (dict b) = true →
    lt (collapse 0 (dict a)) (collapse 0 (dict b)) = true

/-- **§79 の第三の主定理。** 頭部の比較に残る仮説は `CollapseMono0_79` ひとつ。 -/
theorem dictHeadLt79 (Hp : PsiIdxOKStd172) (H0 : CollapseMono0_79) : DictHeadLt77 :=
  dictHeadLt_of_split77 (dictCross79 Hp) (collapseMono_of_split77 H0 (collapseMono1_79 Hp))

theorem dictLtA74_79 (Hp : PsiIdxOKStd172) (H0 : CollapseMono0_79) : DictLtA74 :=
  dictLtA74_of_head77 Hp (dictHeadLt79 Hp H0)

theorem vOfLtA71_79 (Hp : PsiIdxOKStd172) (H0 : CollapseMono0_79) : VOfLtA71 :=
  vOfLtA71_of_head77 Hp (dictHeadLt79 Hp H0)

theorem limDecS1_79 (Hp : PsiIdxOKStd172) (H0 : CollapseMono0_79) : LimDecS1 :=
  limDecS1_77 Hp (dictHeadLt79 Hp H0)

theorem limIncS1_79 (Hp : PsiIdxOKStd172) (H0 : CollapseMono0_79) : LimIncS1 :=
  limIncS1_77 Hp (dictHeadLt79 Hp H0)

/-- **326 行目の証明書。** §77 の 4 つのうち `DictHeadLt77` が `CollapseMono0_79` に替わる。 -/
theorem certIn_t326_79 (Hp : PsiIdxOKStd172) (H0 : CollapseMono0_79)
    (HCD : CofDenseS1) (HBC : BCofIn71)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_head77 Hp (dictHeadLt79 Hp H0) HCD HBC hacc

end

/-! ### §79.9 測定 (凍結)

**構成。** 種 `bs79` は段 1 以下の 6 項 (`0`・`1`・`ω`・`Ω₁`・`ψ₁ψ₁0`・`ψ₀ψ₁0`)。
**深さの線** `deep79` は `ψ₀`・`ψ₁` を 1 段ずつかぶせて 2 つに 1 つ間引く操作を 7 回
繰り返した層の合併 — 入れ子は 10 段まで届き、標準かつ段 1 以下のものだけでも 9 段。
**幅の線** `wide79` は成分が降順の 2 項和・3 項和 (`BT.isStd` の和の節が要求する形)。
**領域の外** `out79` は添字 2・3 — **上限の 2 つ先** — を 1 段/2 段かぶせたもので、
そのうえにさらに `ψ₀`・`ψ₁` を重ねた形も入れてある。変数はそれぞれ自分の形で
量化する: 頭部の対は主要項どうし、和の対は和どうし、段をまたぐ対は `(ψ₀·, ψ₁·)`。

    popAll79   127 項  (入れ子 10 段まで、うち 18 項が段の上限の外)
    popGood79   55 項  段 1 以下かつ `BT.isStd`  (§79 の仮説そのもの)
                        単項 30・2 項和 20・3 項和 5、入れ子 8 段以上が 8 項、9 段が 1 項
    popStd79    67 項  `BT.isStd` のみ (段の上限を外す)
    popLv79    109 項  段の上限のみ (標準性を外す)

𝔗(M) の側 `tpopRaw79` は手で組んだ 14 項 (`M`・`ω̄^·`・`Z 1`・`ψ_{Z1}0` など領域の
外のものを含む) を `ω^·`・`⊕1`・`⊕2`・`φ̄0·`・`φ̄1·`・`ψ_{Z0}·` で 2 回閉じ、
`dict` の像を足したもの — 448 項、うち `inT` なのは 333 項。
-/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

private def dedup79 (l : List BT) : List BT :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []
private def every79 (k : Nat) (l : List BT) : List BT :=
  (l.zipIdx.filter (fun p => p.2 % k == 0)).map (·.1)
private def dep79 : BT → Nat
  | .zero => 0
  | .D _ a => 1 + dep79 a
  | .sum a b => max (dep79 a) (dep79 b)
private def wid79 : BT → Nat
  | .sum a b => wid79 a + wid79 b
  | _ => 1

private def bs79 : List BT :=
  [BT.zero, BT.D 0 BT.zero, BT.D 0 (BT.D 0 BT.zero), BT.D 1 BT.zero,
   BT.D 1 (BT.D 1 BT.zero), BT.D 0 (BT.D 1 BT.zero)]
private def cap01_79 (l : List BT) : List BT := l.map (BT.D 0) ++ l.map (BT.D 1)
private def cap23_79 (l : List BT) : List BT := l.map (BT.D 2) ++ l.map (BT.D 3)
private def lay79 : Nat → List BT → List BT
  | 0, l => l
  | n + 1, l => every79 2 (cap01_79 (lay79 n l))
private def deep79 : List BT :=
  dedup79 (bs79 ++ lay79 1 bs79 ++ lay79 2 bs79 ++ lay79 3 bs79 ++ lay79 4 bs79
            ++ lay79 5 bs79 ++ lay79 6 bs79 ++ lay79 7 bs79)
private def prin79 (l : List BT) : List BT := l.filter BT.isP
private def sums2_79 (l : List BT) : List BT :=
  (prin79 l).flatMap (fun a => ((prin79 l).filter (fun b => BT.le b a)).map (BT.sum a))
private def sums3_79 (l : List BT) : List BT :=
  (prin79 l).flatMap (fun a =>
    ((prin79 l).filter (fun b => BT.le b a)).flatMap (fun b =>
      ((prin79 l).filter (fun c => BT.le c b)).map (fun c => BT.sum a (BT.sum b c))))
private def wide79 : List BT :=
  dedup79 (every79 5 (sums2_79 (every79 2 deep79))
            ++ every79 31 (sums3_79 (every79 3 deep79)))
private def out79 : List BT :=
  dedup79 (every79 2 (cap23_79 (every79 3 deep79))
            ++ every79 3 (cap01_79 (every79 5 (cap23_79 (every79 5 deep79)))))

private def popAll79 : List BT := dedup79 (deep79 ++ wide79 ++ out79)
private def popGood79 : List BT := popAll79.filter (fun x => btLe72 1 x && BT.isStd x)
private def popStd79  : List BT := popAll79.filter BT.isStd
private def popLv79   : List BT := popAll79.filter (btLe72 1 ·)

/-! 母集団の形 — 深さも幅も、そして領域の外も。 -/
#guard (popAll79.length, popGood79.length, popStd79.length, popLv79.length) == (127, 55, 67, 109)
#guard (popAll79.foldl (fun m x => max m (dep79 x)) 0,
        popGood79.foldl (fun m x => max m (dep79 x)) 0) == (10, 9)
#guard (popGood79.countP (fun x => wid79 x == 1), popGood79.countP (fun x => wid79 x == 2),
        popGood79.countP (fun x => wid79 x == 3)) == (30, 20, 5)
#guard (popGood79.countP (fun x => 8 ≤ dep79 x), popAll79.countP (fun x => !(btLe72 1 x)))
        == (8, 18)

private def okPair79 (a b : BT) : Bool := !(BT.lt a b) || TM.Term.lt (dict a) (dict b)
private def fails79 (l : List BT) : Nat :=
  (l.flatMap (fun a => l.map (fun b => (a, b)))).countP (fun p => !(okPair79 p.1 p.2))
private def crossFail79 (l : List BT) : Nat :=
  ((l.filter BT.isP).flatMap (fun a => (l.filter BT.isP).map (fun b => (a, b)))).countP
    (fun p => match p.1, p.2 with
      | BT.D u _, BT.D v _ => u < v && !(TM.Term.lt (dict p.1) (dict p.2))
      | _, _ => false)
private def headFail79 (l : List BT) : Nat :=
  ((l.filter BT.isP).flatMap (fun a => (l.filter BT.isP).map (fun b => (a, b)))).countP
    (fun p => BT.lt p.1 p.2 && !(TM.Term.lt (dict p.1) (dict p.2)))
private def monoFail79 (w : Nat) (l : List BT) : Nat :=
  (l.flatMap (fun a => l.map (fun b => (a, b)))).countP
    (fun p => TM.Term.lt (dict p.1) (dict p.2) &&
      !(TM.Term.lt (collapse w (dict p.1)) (collapse w (dict p.2))))

/-! **肯定 1 — §77 の主張。** 3025 対で反例 0、標準性だけでも 4489 対で 0。 -/
#guard (fails79 popGood79, fails79 popStd79) == (0, 0)

/-! **否定 1 — 標準性は外せない、そして深さは効く。** 段の上限だけの 109 項
    (11881 対) で `dict` は **211 対**を反転する。§77 は同じ形の母集団 (24 項・
    入れ子 5 段) で 35 だった。 -/
#guard fails79 popLv79 == 211

/-! **肯定 2 — §79.7 の `DictCross77`。** 段をまたぐ対は 3 つの母集団すべてで反例 0
    (定理なので確認)。頭部の対も 0。 -/
#guard (headFail79 popGood79, crossFail79 popGood79, crossFail79 popStd79,
        crossFail79 popLv79) == (0, 0, 0, 0)

/-! **肯定 3 と否定 2 — §79.4 は定理、`u = 0` はまだ仮説。**
    `collapse 1` は門を課しても外しても 0 (§79.4 が定理にした半分)。
    `collapse 0` は `BT.isStd (ψ₀ ·)` — `K` の条件 — を落とすと **66 対**反転し、
    課すと 0。§77 は同じ測り方で 28 だった。 -/
#guard (monoFail79 1 popGood79,
        monoFail79 1 (popGood79.filter (fun a => BT.isStd (BT.D 1 a)))) == (0, 0)
#guard (monoFail79 0 popGood79,
        monoFail79 0 (popGood79.filter (fun a => BT.isStd (BT.D 0 a)))) == (66, 0)

/-! **肯定 4 — §79.6/§79.7 の 2 本。** `ψ₀` の像は `Ω₁` の下、`Ω₁` は `ψ₁` の像の下。
    どちらも 127 項すべて (領域の外の 18 項を含む) で反例 0。 -/
#guard (popAll79.countP (fun a => !(TM.Term.lt (collapse 0 (dict a)) (reg 1))),
        popAll79.countP (fun a => !(TM.Term.le (reg 1) (collapse 1 (dict a)))),
        popAll79.countP (fun a => !(TM.Term.lt (collapse 0 (dict a)) (collapse 1 (dict a)))))
        == (0, 0, 0)

private def tsd79 : List Term :=
  [zero, TM.Term.one, TM.Term.omega, phi TM.Term.one zero, phi (TM.Term.ofNat 2) zero,
   psi (Z zero) zero, Z zero, Z TM.Term.one, M, omg M, omg (Z zero),
   phi zero (Z zero), psi (Z zero) (Z zero), psi (Z TM.Term.one) zero]
private def tclose79 (l : List Term) : List Term :=
  l ++ l.map omegaNF ++ l.map (fun t => plus t TM.Term.one)
    ++ l.map (fun t => plus t (plus t TM.Term.one))
    ++ l.map (fun t => phi zero t) ++ l.map (fun t => phi TM.Term.one t)
    ++ l.map (fun t => psi (Z zero) t)
private def tdedup79 (l : List Term) : List Term :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []
private def tevery79 (k : Nat) (l : List Term) : List Term :=
  (l.zipIdx.filter (fun p => p.2 % k == 0)).map (·.1)
private def tpopRaw79 : List Term :=
  tdedup79 (tclose79 (tclose79 tsd79) ++ popGood79.map dict ++ popStd79.map dict)
private def tpop79 : List Term := tpopRaw79.filter (fun t => inT t)

private def omFail79 (l : List Term) : Nat :=
  (l.flatMap (fun a => l.map (fun b => (a, b)))).countP
    (fun p => TM.Term.lt p.1 p.2 && !(TM.Term.lt (omegaNF p.1) (omegaNF p.2)))
private def d3Fail79 (l : List Term) : Nat :=
  (l.flatMap (fun a => l.map (fun b => (a, b)))).countP
    (fun p => TM.Term.lt p.1 p.2 && !(TM.Term.isFP zero p.1) && dnArg p.1 == dnArg p.2)
private def d3Drop79 (l : List Term) : Nat :=
  (l.flatMap (fun a => l.map (fun b => (a, b)))).countP
    (fun p => TM.Term.lt p.1 p.2 && dnArg p.1 == dnArg p.2)
private def plusFail79 (l : List Term) : Nat :=
  (l.flatMap (fun e => l.flatMap (fun a => l.map (fun b => (e, a, b))))).countP
    (fun p => TM.Term.lt p.2.1 p.2.2 && !(TM.Term.lt (plus p.1 p.2.1) (plus p.1 p.2.2)))

#guard (tpopRaw79.length, tpop79.length) == (448, 333)

/-! **肯定 5 — §79.2 と §79.3。** `ω^·` の狭義単調性は `inT` の 333 項 (110889 対) で
    反例 0、`inT` でない 115 項を混ぜた 448 項 (200704 対) でも 0。`plus e ·` の
    狭義単調性は 84³ の三つ組で 0。 -/
#guard (omFail79 tpop79, omFail79 tpopRaw79) == (0, 0)
#guard plusFail79 (tevery79 4 tpop79) == 0

/-! **否定 3 — D3 の側条件は飾りではない。** `isFP zero x = false` を課すと `dnArg` が
    潰す対は 0。落とすと `inT` の中だけで **26 対**、全体で 33 対。最小の証人は
    `x = ε₀`, `y = ε₀ ⊕ 1` — `dnArg` はどちらも `ε₀` に送る。3 番目の証人 `Γ₀` は
    §65.3 が「𝔗(M) では強臨界項も `ω^·` の不動点」と言った、`CNV` には無い枝である。 -/
#guard (d3Fail79 tpop79, d3Drop79 tpop79) == (0, 26)
#guard (d3Fail79 tpopRaw79, d3Drop79 tpopRaw79) == (0, 33)
#guard dnArg (phi TM.Term.one zero) == dnArg (plus (phi TM.Term.one zero) TM.Term.one)
#guard dnArg (psi (Z zero) zero) == dnArg (plus (psi (Z zero) zero) TM.Term.one)

end

/-! ### §79.10 公理 -/

end Evidence.Region
