import Evidence.RegionNext3

/-
Evidence/RegionNext4.lean — THE GATES ROW 326 STILL WAITS ON (§95-)

Split out of `RegionNext3` when that file passed 17000 lines: §80-§94 are settled and
should not be re-elaborated on every step.  This file carries the part still moving.
-/

namespace Evidence.Region

open BMS
/-! ## §96 THE BRIDGE COSTS THE NON-STRICT HALF OF THE ORDER — AND ITS SIZE-INDEXED FORM

§93 proved that row 326's whole Veblen fold is ONE clause, `CollapseMono0Hi81`, and then
named, in its own words, what blocks the induction that would close it:

> every step also needs `toList (dict a) = (toL a).map dict` (§93.3's bridge, §77's
> `toList_dict_ofL77`), and that is available only from `DictLtUpTo77 m`, whose only
> producer `dictLtUpTo_all77` consumes the FULL `DictHeadLt77` — hence the full residual.

**§96 closes neither gate.**  What §96 proves is that the bridge is CHEAPER than the full
residual, and says by exactly how much — the accounting is an EQUIVALENCE, not a bound.

  §96.1  **THE BRIDGE IS EXACTLY "THE IMAGES DESCEND".**  `fullBridge_iff_desc96` :
         `FullBridge96 ↔ DictDesc96`, where `FullBridge96 a` is `toList (dict a) =
         (toL a).map dict` and `DictDesc96 a` is `descL ((toL a).map dict)`.  The `←`
         direction is `toList_dict_ofL96`, which is §77.3's induction with `DictLtUpTo77 m`
         cut out and the adjacent-pair `≤` put in its place; the `→` direction is free,
         because the component list of an `inT` term descends.  **So the bridge does have
         order content, and the content is the NON-STRICT order on ADJACENT components —
         no more and no less.**  That answers the question the task asked of it.

  §96.2  **§93'S BRIDGE IS A CONSEQUENCE.**  `hiBridge96_of_full : FullBridge96 → HiBridge93`
         and `toList_loW_dict96`.  The place where §93.3 spent `CollapseMono0Hi81` a second
         time is gone.

  §96.3  **THE NON-STRICT ORDER, AT ONE COMPONENT, SUFFICES.**  `fullBridge96_of_atom` /
         `hiBridge96_of_atom` : `PsiIdxOKStd172 → DictLeAtom96 → HiBridge93`, where
         `DictLeAtom96` is `BT.le (ψ_u α) (ψ_v β) ⟹ le (dict (ψ_u α)) (dict (ψ_v β))` — one
         COMPONENT, and only `≤`.  `dictLe96_of81` proves the new hypothesis sits below the
         old one, and `certIn_t326_le96` is row 326 with §93's `HiBridge93` replaced by it.
         `dictLtAtom96_iff` prices the difference exactly: **`DictLtAtom96 ↔ DictLeAtom96 ∧
         DictAtomInj96`** — strict is non-strict plus injectivity, the bridge buys the left
         factor only, and §77.4's sum induction is what wants the right one.

  §96.4  **THE ONE-COMPONENT COMPARISON SPLITS THREE WAYS, AND TWO OF THEM ARE FREE.**
         `bt_lt_D96` reads `BT.lt (ψ_u α) (ψ_v β)` as "`u < v`, or `u = v` and `α < β`"
         (the fuel is handled by §93.1's `ltL_adeq93`).  Then: the level-crossing case is a
         THEOREM, `dictLt_cross96`, from `PsiIdxOKStd172` alone — `ψ₀`'s image is below
         `Ω₁` and `ψ₁`'s is at or above it, so the pair never needs the Veblen fold; the
         level-1 case carries the argument's NON-STRICT order untouched
         (`le_collapse1_le96`, §77.8's `le_collapse1_77` with its hypothesis weakened to
         `le`, which is all its proof ever used); and the only clause left is
         `CollapseLe0_96` — `collapse 0` monotone non-strictly.  `dictLeAtom96_of_split`
         assembles them, using the order hypothesis at the ARGUMENTS only.

  §96.5  **THE SIZE-INDEXED CHAIN.**  `dictLtUpTo_all96` : §77.4's sum induction consuming
         only `DictHeadLtUpTo96 n` — the head comparison up to symbol count `n` — instead
         of the whole of `DictHeadLt77`.  `dictHeadLtUpTo96_of_hi` carries §79.8 and §81.7
         through unchanged (both were pointwise in the pair).  `bridgeUpTo96_of_leUpTo` :
         **the bridge at terms of size ≤ n needs the order only at pairs of total size ≤ n**,
         and `bridgeUpTo96_of_hi` runs the whole chain size-indexed.  This is the
         size-indexed form of §77 → §79 → §81 that §93 said would be needed, for the bridge.

  §96.6  **THE NEGATIVES.**  `bridge_drops96` — `plus` really does drop, and the witness is
         `aDrop96 = 1 ⊕ Ω₁` (`ψ₀0 ⊕ ψ₁0`): every component is principal, standard and of
         level ≤ 1, only the DESCENDING clause of `BT.isStd` fails, and `toList (dict ·)`
         has one component where `(toL ·).map dict` has two.  `desc_drops96` is the same
         fact through §96.1's equivalence.  And `hiBridge_blind96` — **§93's half-bridge
         HOLDS on that very term**: `hiW89 (dict aDrop96) = dict (hiB93 aDrop96)`.  So
         `HiBridge93` is strictly the hi-half; it cannot see the drop that `FullBridge96`
         is about.

WHAT IS **NOT** CLAIMED.  `CollapseMono0Hi81` is not proved, `HiBridge93` is not proved
unconditionally, and `CollapseLe0_96` is not proved.  §96 does not prove `PsiIdxOKStd172`,
`IdxStd90`, `DictDense85`, `CofDenseS1` or `BCofIn71`.  **Row 326 still has three gates.**
What has changed is that the bridge is no longer one of the places `CollapseMono0Hi81` is
spent: it is spent only on the strictness, and only through `CollapseLe0_96` at the
adjacent components whose two subscripts are both 0.

**WHERE §96 STOPPED, PRECISELY.**  `DictLe96` is not free.  The sum-level non-strict
induction closes in every branch but one: at a head pair `ψ_u α`, `ψ_u β` with `α ≠ β`, the
non-strict hypothesis allows `dict (ψ_u α) = dict (ψ_u β)`, and then the two tails decide a
comparison the hypothesis says nothing about.  So `DictLe96` needs, on top of the three
cases of §96.4, the INJECTIVITY of `dict` on one-component standard terms — and
`dictLtAtom96_iff` says in as many words that non-strictness plus injectivity IS strictness
again.  That is the exact shape of the remaining debt: the bridge is paid out of the
non-strict factor alone, and what §93 spent the whole residual on is the product.

**AND WHAT THAT SAYS ABOUT THE INDUCTION (§93's second question).**  Write Gate(a,b) for
`CollapseMono0Hi81` at one pair and Order(x,y) for `lt (dict x) (dict y)`.  §93.6 gives
Gate(a,b) ⟸ Gate(c, hi b) with `size c < size a` and `size (hi b) ≤ size b` — the pair
shrinks — and Gate(a,b) ⟸ Order(c,a), which sits at `size c + size a` and is what breaks
`size a + size b` when `b` is small.  §96.5 makes the second dependency explicit:
Order(x,y) at total size m needs Gate only at pairs of ARGUMENTS, hence at first components
of size `< size x`.  So along Gate(a,b) → Order(c,a) → Gate(x,y) the FIRST component runs
`a ↦ c ↦ x` with `size x < size c < size a`: **measured by `size a` alone, every gate
instance §93.6 reaches is strictly smaller — except the ones that come through the bridge
at `b`.**  With the bridge free, induction on `size a` alone closes; with the bridge paid
out of the order at `b`, it does not, because the bridge at `b` needs gate instances of
size up to `size b`, unbounded by `size a`.  **The bridge is not one obstacle among two; it
is the only thing standing between §93.6 and a running induction.**  §96 has not made it
free — it has priced it (§96.1) and cut its price roughly in half (§96.3, §96.4).

WHAT THE MEASUREMENT SAYS (§96.7 gives the construction: §93.9's population verbatim,
re-declared because §93's are `private` — the counts `(1532, 592, 592, 300, 290, 292)` are
guarded, so it IS the same population).

  * **The FULL bridge fails on 20 of the 1532**, and `descL` of the image list fails on the
    same 20 — **0 mismatches on all 1532**, which is §96.1's equivalence made visible.  All
    20 are level-bounded and none is `BT.isStd`: the failing clause is the descending one,
    every time.  Unlike §93.9's reading of the hi-half, this population is NOT blind to the
    statement being measured.
  * **§93's half-bridge holds on all 1532, including the 20.**  So the half-bridge is
    strictly weaker than the full one on this population, and `aDrop96` is the smallest
    witness of it (5 symbols).
  * **Of the 687 adjacent component pairs in the 592 good terms, 400 cross a level and are
    free by `dictLt_cross96`, 100 are equal terms, 157 sit at subscript 1, and only 30 —
    4.4% — sit at subscript 0 and touch the Veblen fold at all.**
  * **The population cannot tell the non-strict clause from the strict one, and §96 says so
    rather than hiding it.**  `dict` is INJECTIVE on the 592 (0 collisions), so on the 5050
    `le`-pairs drawn from a 100-term sample of the `K`-standard terms the only non-strict
    pairs are the 100 diagonal ones, and `CollapseLe0_96`'s conclusion fails 0 times.  A
    clean sweep here proves nothing about the gap between `CollapseLe0_96` and §79's
    `CollapseMono0_79`; that gap is exactly the injectivity above, and this corpus has it.
  * **The naive measure fails, and not vacuously.**  On the 4656 residual pairs the gate's
    own recursive instance `(c, hi b)` is below `size a + size b` on **all 4656**; the
    ORDER instance `(c, a)` that §93.6 also needs exceeds it on **117** of them (2.5%), and
    `size c ≥ size b` on 173.  `size c ≥ size a` never happens (0 of 4656) — §82's
    `G(a,0) < a` at the level of symbol counts, which is why §96's `size a`-alone reading
    is the one to try.
-/


/-! ### §96.1 橋の中身は隣り合う像の降べき、それだけ -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- **完全な橋。** `plus` が成分を一つも落とさないこと。§93.3 の橋 `HiBridge93` は
    この帰結である。 -/
def FullBridge96 : Prop :=
  ∀ (a : BT), btLe72 1 a = true → BT.isStd a = true →
    toList (dict a) = (BT.toL a).map dict

/-- **像の降べき。** `BT` の側で降べきな成分列が、像でも降べきであること。
    順序の**非狭義**の分しか言っていない。 -/
def DictDesc96 : Prop :=
  ∀ (a : BT), btLe72 1 a = true → BT.isStd a = true →
    descL ((BT.toL a).map dict) = true

/-- **§96.1 の主補題 — 像が降べきなら `plus` は何も落とさない。**
    §77.3 の `toList_dict_ofL77` から `DictLtUpTo77` を抜き、代わりに像の降べきだけを
    仮定した形。順序は隣り合う二成分の `≤` としてしか使われない。 -/
theorem toList_dict_ofL96 (Hp : PsiIdxOKStd172) :
    ∀ (l : List BT), GoodL77 l → descL (l.map dict) = true →
      toList (dict (BT.ofL l)) = l.map dict
  | [], _, _ => rfl
  | [p], hg, _ => by
      obtain ⟨u, a, rfl⟩ := hg.1 p (List.Mem.head _)
      show toList (dict (BT.D u a)) = [dict (BT.D u a)]
      exact toList_of_isAP (isAP_dict_D76 u a)
  | p :: q :: r, hg, hd => by
      obtain ⟨u, a, rfl⟩ := hg.1 p (List.Mem.head _)
      obtain ⟨v, b, rfl⟩ := hg.1 q (List.Mem.tail _ (List.Mem.head _))
      have hgt : GoodL77 (BT.D v b :: r) := goodL77_tail hg
      have hdd : descL (dict (BT.D u a) :: dict (BT.D v b) :: r.map dict) = true := hd
      have hle : le (dict (BT.D v b)) (dict (BT.D u a)) = true := (descL_cons.mp hdd).1
      have hdt : descL ((BT.D v b :: r).map dict) = true := (descL_cons.mp hdd).2
      have ih : toList (dict (BT.ofL (BT.D v b :: r)))
          = dict (BT.D v b) :: r.map dict := toList_dict_ofL96 Hp (BT.D v b :: r) hgt hdt
      have hiP : inT (dict (BT.D u a)) = true :=
        (inT_dict_of_std172 Hp (BT.D u a) (hg.2.2.1 _ (List.Mem.head _))
          (hg.2.1 _ (List.Mem.head _))).1
      have hiT : inT (dict (BT.ofL (BT.D v b :: r))) = true :=
        (inT_dict_of_std172 Hp _ (btLe_ofL77 hgt) (isStd_ofL77 hgt)).1
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

/-- **§96.1 の第一の帰結 — 像の降べきから完全な橋。** -/
theorem fullBridge96_of_desc (Hp : PsiIdxOKStd172) (D : DictDesc96) : FullBridge96 := by
  intro a hb hs
  have h := toList_dict_ofL96 Hp (BT.toL a) (good_toL77 a hs hb) (D a hb hs)
  rw [ofL_toL77 a hs] at h
  exact h

/-- **§96.1 の第二の帰結 — 完全な橋から像の降べき。** 𝔗(M) の項の成分列は降べきだから。 -/
theorem desc96_of_fullBridge (Hp : PsiIdxOKStd172) (B : FullBridge96) : DictDesc96 := by
  intro a hb hs
  have h := B a hb hs
  have hd := (inT_toList (dict a) (inT_dict_of_std172 Hp a hb hs).1).2
  rw [h] at hd
  exact hd

/-- **§96.1 の主定理 — 橋の中身は像の降べき、過不足なく。** -/
theorem fullBridge_iff_desc96 (Hp : PsiIdxOKStd172) : FullBridge96 ↔ DictDesc96 :=
  ⟨desc96_of_fullBridge Hp, fullBridge96_of_desc Hp⟩

end

/-! ### §96.2 §93 の橋は完全な橋の帰結 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- 良い成分列の像の `ofList`。§77 の `ofList_map_dict77` を橋から出した形。 -/
theorem ofList_map_dict96 (Hp : PsiIdxOKStd172) (B : FullBridge96)
    (l : List BT) (hg : GoodL77 l) : ofList (l.map dict) = dict (BT.ofL l) := by
  have h1 := B (BT.ofL l) (btLe_ofL77 hg) (isStd_ofL77 hg)
  rw [toL_ofL l hg.1] at h1
  rw [← h1, inT_ofList_toList _
    (inT_dict_of_std172 Hp _ (btLe_ofL77 hg) (isStd_ofL77 hg)).1]

/-- **§93.3 の橋は完全な橋から出る。** §93 が `CollapseMono0Hi81` を二度目に使った場所は
    これで消える。 -/
theorem hiBridge96_of_full (Hp : PsiIdxOKStd172) (B : FullBridge96) : HiBridge93 := by
  intro a hb hsa
  have hgood : GoodL77 (BT.toL a) := good_toL77 a hsa hb
  show ofList ((toList (dict a)).filter (fun p => !lt p (reg 1))) = dict (hiB93 a)
  rw [B a hb hsa, filter_map93 dict (fun p => !lt p (reg 1)) (BT.toL a),
    filter_congr93 (fun t => !lt (dict t) (reg 1)) hiA93 (BT.toL a) (fun t ht => by
      obtain ⟨u, c, rfl⟩ := hgood.1 t ht
      exact hiA_dict93 Hp u c (hgood.2.2.1 _ ht) (hgood.2.1 _ ht))]
  exact ofList_map_dict96 Hp B _ (goodL_hiL93 hgood)

/-- §93.6 の `toList_loW_dict93` も完全な橋から出る。 -/
theorem toList_loW_dict96 (Hp : PsiIdxOKStd172) (B : FullBridge96) {a : BT}
    (hb : btLe72 1 a = true) (hsa : BT.isStd a = true) :
    toList (loW89 (dict a)) = (loL93 (BT.toL a)).map dict := by
  have hgood : GoodL77 (BT.toL a) := good_toL77 a hsa hb
  have hia := inT_dict_of_std172 Hp a hb hsa
  rw [toList_loW89 hia.1, B a hb hsa, filter_map93 dict (fun p => lt p (reg 1)) (BT.toL a),
    filter_congr93 (fun t => lt (dict t) (reg 1)) (fun t => !hiA93 t) (BT.toL a) (fun t ht => by
      obtain ⟨u, c, rfl⟩ := hgood.1 t ht
      have hq := hiA_dict93 Hp u c (hgood.2.2.1 _ ht) (hgood.2.1 _ ht)
      show lt (dict (BT.D u c)) (reg 1) = !hiA93 (BT.D u c)
      rw [← hq]
      cases hz : lt (dict (BT.D u c)) (reg 1) with
      | true => rfl
      | false => rfl)]
  rfl

end

/-! ### §96.3 像の降べきは成分ひとつぶんの非狭義の順序 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- **成分ひとつぶんの非狭義の順序。** 橋が要求するのはこれだけである。 -/
def DictLeAtom96 : Prop := ∀ (u v : Nat) (a b : BT),
    btLe72 1 (BT.D u a) = true → btLe72 1 (BT.D v b) = true →
    BT.isStd (BT.D u a) = true → BT.isStd (BT.D v b) = true →
    BT.le (BT.D u a) (BT.D v b) = true →
    le (dict (BT.D u a)) (dict (BT.D v b)) = true

/-- **`dict` の非狭義の順序保存。** 狭義 (`DictLtA74`) より弱い。 -/
def DictLe96 : Prop := ∀ (x y : BT), btLe72 1 x = true → btLe72 1 y = true →
    BT.isStd x = true → BT.isStd y = true → BT.le x y = true →
    le (dict x) (dict y) = true

theorem dictLeAtom96_of_le (S : DictLe96) : DictLeAtom96 :=
  fun _ _ _ _ hbA hbB hsA hsB h => S _ _ hbA hbB hsA hsB h

/-- 良い成分列の像は降べき — 成分ひとつぶんの順序から。 -/
theorem descMap96_of_atom (A : DictLeAtom96) :
    ∀ (l : List BT), GoodL77 l → descL (l.map dict) = true
  | [], _ => rfl
  | [_], _ => rfl
  | p :: q :: r, hg => by
      obtain ⟨u, a, rfl⟩ := hg.1 p (List.Mem.head _)
      obtain ⟨v, b, rfl⟩ := hg.1 q (List.Mem.tail _ (List.Mem.head _))
      have hdd : (BT.le (BT.D v b) (BT.D u a) && descOK72 (BT.D v b :: r)) = true := hg.2.2.2
      refine descL_cons.mpr ⟨?_, descMap96_of_atom A (BT.D v b :: r) (goodL77_tail hg)⟩
      exact A v u b a (hg.2.2.1 _ (List.Mem.tail _ (List.Mem.head _)))
        (hg.2.2.1 _ (List.Mem.head _)) (hg.2.1 _ (List.Mem.tail _ (List.Mem.head _)))
        (hg.2.1 _ (List.Mem.head _)) ((Bool.and_eq_true _ _).mp hdd).1

theorem dictDesc96_of_atom (A : DictLeAtom96) : DictDesc96 :=
  fun a hb hs => descMap96_of_atom A (BT.toL a) (good_toL77 a hs hb)

/-- **§96.3 の主定理 — 橋は成分ひとつぶんの非狭義の順序だけで立つ。** §93.3 は狭義の
    順序 (`CollapseMono0Hi81` を経由した `DictLtA74`) を、しかも和の水準で払っていた。 -/
theorem fullBridge96_of_atom (Hp : PsiIdxOKStd172) (A : DictLeAtom96) : FullBridge96 :=
  fullBridge96_of_desc Hp (dictDesc96_of_atom A)

theorem hiBridge96_of_atom (Hp : PsiIdxOKStd172) (A : DictLeAtom96) : HiBridge93 :=
  hiBridge96_of_full Hp (fullBridge96_of_atom Hp A)

theorem fullBridge96_of_le (Hp : PsiIdxOKStd172) (S : DictLe96) : FullBridge96 :=
  fullBridge96_of_atom Hp (dictLeAtom96_of_le S)

theorem hiBridge96_of_le (Hp : PsiIdxOKStd172) (S : DictLe96) : HiBridge93 :=
  hiBridge96_of_full Hp (fullBridge96_of_le Hp S)

/-- 成分ひとつぶんの**狭義**の順序。 -/
def DictLtAtom96 : Prop := ∀ (u v : Nat) (a b : BT),
    btLe72 1 (BT.D u a) = true → btLe72 1 (BT.D v b) = true →
    BT.isStd (BT.D u a) = true → BT.isStd (BT.D v b) = true →
    BT.lt (BT.D u a) (BT.D v b) = true →
    lt (dict (BT.D u a)) (dict (BT.D v b)) = true

/-- 成分ひとつぶんの単射性。 -/
def DictAtomInj96 : Prop := ∀ (u v : Nat) (a b : BT),
    btLe72 1 (BT.D u a) = true → btLe72 1 (BT.D v b) = true →
    BT.isStd (BT.D u a) = true → BT.isStd (BT.D v b) = true →
    BT.lt (BT.D u a) (BT.D v b) = true →
    dict (BT.D u a) ≠ dict (BT.D v b)

theorem bt_le_of_lt96 {a b : BT} (h : BT.lt a b = true) : BT.le a b = true := by
  show ((a == b) || BT.lt a b) = true
  rw [h]
  cases (a == b) <;> rfl

theorem lt_of_le_ne96 {x y : Term} (h : le x y = true) (hne : x ≠ y) : lt x y = true := by
  rcases (Bool.or_eq_true _ _).mp h with h1 | h1
  · exact absurd (eq_of_beq h1) hne
  · exact h1

theorem ne_of_lt96 {x y : Term} (h : lt x y = true) : x ≠ y := by
  intro hc
  rw [hc, lt_irrefl] at h
  exact Bool.noConfusion h

/-- **狭義 = 非狭義 + 単射。** 橋が払うのは左の項だけで、右の項は払わない。
    和の水準の帰納法 (§77.4) が要求するのは狭義の側である — そこが §96 の残る借金。 -/
theorem dictLtAtom96_iff : DictLtAtom96 ↔ (DictLeAtom96 ∧ DictAtomInj96) := by
  constructor
  · intro H
    refine ⟨?_, ?_⟩
    · intro u v a b hbA hbB hsA hsB h
      rcases (Bool.or_eq_true _ _).mp h with h1 | h1
      · rw [bt_beq_eq77 h1]; exact le_self77 _
      · exact le_of_lt (H u v a b hbA hbB hsA hsB h1)
    · intro u v a b hbA hbB hsA hsB h
      exact ne_of_lt96 (H u v a b hbA hbB hsA hsB h)
  · intro ⟨A, I⟩ u v a b hbA hbB hsA hsB h
    exact lt_of_le_ne96 (A u v a b hbA hbB hsA hsB (bt_le_of_lt96 h))
      (I u v a b hbA hbB hsA hsB h)

/-- 新しい仮説は §81 の残余より下 — §77・§81 の狭義の移送を弱めただけ。 -/
theorem dictLe96_of81 (Hp : PsiIdxOKStd172) (H : CollapseMono0Hi81) : DictLe96 := by
  intro x y hbx hby hsx hsy h
  rcases (Bool.or_eq_true _ _).mp h with h1 | h1
  · rw [bt_beq_eq77 h1]; exact le_self77 _
  · exact le_of_lt (dictLt_of_head77 Hp (dictHeadLt81 Hp H) x y hbx hby hsx hsy h1)

end

/-! ### §96.4 成分ひとつぶんの三つの場合 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- 成分ひとつぶんの `BT.lt` は添字か引数のどちらかで決まる。 -/
theorem bt_lt_D96 : ∀ {u v : Nat} {a b : BT}, BT.lt (BT.D u a) (BT.D v b) = true →
    u < v ∨ (u = v ∧ BT.lt a b = true) := by
  intro u v a b h
  have he : BT.lt (BT.D u a) (BT.D v b)
      = BT.ltL ((BT.size (BT.D u a) + BT.size (BT.D v b) + 1) + 1)
          (BT.D u a :: []) (BT.D v b :: []) := rfl
  rw [he, ltL_DD93] at h
  by_cases huv : u < v
  · exact Or.inl huv
  · rw [if_neg huv] at h
    by_cases hvu : v < u
    · rw [if_pos hvu] at h; exact Bool.noConfusion h
    · rw [if_neg hvu] at h
      by_cases hab : (a == b) = true
      · rw [if_pos hab, ltL_nil_nil93] at h; exact Bool.noConfusion h
      · rw [if_neg hab] at h
        refine Or.inr ⟨by omega, ?_⟩
        have h2 := ltL_adeq93 _ _ _ h
        have h3 := ltL_fuel93 (szL77 (BT.toL a) + szL77 (BT.toL b) + 2)
          (BT.size a + BT.size b + 2) (BT.toL a) (BT.toL b)
          (by have := szL77_toL a; have := szL77_toL b; omega) h2
        exact h3

/-- **段をまたぐ成分の対は只。** `ψ₀` の像は `Ω₁` の下、`ψ₁` の像は `Ω₁` 以上。 -/
theorem dictLt_cross96 (Hp : PsiIdxOKStd172) {a b : BT}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hbB : btLe72 1 (BT.D 1 b) = true)
    (hsA : BT.isStd (BT.D 0 a) = true) (hsB : BT.isStd (BT.D 1 b) = true) :
    lt (dict (BT.D 0 a)) (dict (BT.D 1 b)) = true :=
  lt_of_lt_of_le3 (inT_le_fragR _ (inT_dict_of_std172 Hp _ hbA hsA).1)
    (inT_le_fragR _ inT_W79) (inT_le_fragR _ (inT_dict_of_std172 Hp _ hbB hsB).1)
    (lt_dict_D0_W93 Hp hbA hsA) (le_W_dict_D1_93 Hp hbB hsB)

/-- **添字 1 の成分は引数の非狭義の順序をそのまま運ぶ。** §77.8 の `le_collapse1_77` の
    仮説を `le` に弱めた形 — もとの証明も `le_of_lt` を通していたので中身は同じ。 -/
theorem le_collapse1_le96 (Hp : PsiIdxOKStd172) (a b : BT)
    (hbA : btLe72 1 (BT.D 1 a) = true) (hbB : btLe72 1 (BT.D 1 b) = true)
    (hsA : BT.isStd (BT.D 1 a) = true) (hsB : BT.isStd (BT.D 1 b) = true)
    (h : le (dict a) (dict b) = true) :
    le (dict (BT.D 1 a)) (dict (BT.D 1 b)) = true := by
  have hia := (inT_dict_of_std172 Hp a (btLe72_D 1 1 a hbA).2 (isStd_of_D hsA)).1
  have hib := (inT_dict_of_std172 Hp b (btLe72_D 1 1 b hbB).2 (isStd_of_D hsB)).1
  rw [dict_D1_eq77 Hp a (btLe72_D 1 1 a hbA).2 (isStd_of_D hsA),
    dict_D1_eq77 Hp b (btLe72_D 1 1 b hbB).2 (isStd_of_D hsB)]
  exact omegaNF_mono_inT (inT_plus (inT_reg 1) hia) (inT_plus (inT_reg 1) hib)
    (plus_mono_right_inT (reg 1) (inT_reg 1) (dict a) (dict b) hia hib h)

/-- **残る一本。** 添字 0 の成分の非狭義の単調性。**証明しない。**
    §81 の `CollapseMono0Hi81` の非狭義版で、`Ω₁ ≤ ·` の条件も持たない。 -/
def CollapseLe0_96 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (dict a) (dict b) = true →
    le (dict (BT.D 0 a)) (dict (BT.D 0 b)) = true

/-- **§96.4 の主定理 — 成分ひとつぶんの順序は、引数の順序と `CollapseLe0_96` に割れる。**
    `S` は**引数**にしか当たらない (記号数が真に小さい)。 -/
theorem dictLeAtom96_of_split (Hp : PsiIdxOKStd172) (C0 : CollapseLe0_96) (S : DictLe96) :
    DictLeAtom96 := by
  intro u v a b hbA hbB hsA hsB h
  rcases (Bool.or_eq_true _ _).mp h with h1 | h1
  · rw [bt_beq_eq77 h1]; exact le_self77 _
  · rcases bt_lt_D96 h1 with huv | ⟨huv, hab⟩
    · have hu := (btLe72_D 1 u a hbA).1
      have hv := (btLe72_D 1 v b hbB).1
      have hu0 : u = 0 := by omega
      have hv1 : v = 1 := by omega
      subst hu0; subst hv1
      exact le_of_lt (dictLt_cross96 Hp hbA hbB hsA hsB)
    · subst huv
      have hle : le (dict a) (dict b) = true :=
        S a b (btLe72_D 1 u a hbA).2 (btLe72_D 1 u b hbB).2 (isStd_of_D hsA) (isStd_of_D hsB)
          (bt_le_of_lt96 hab)
      have hu := (btLe72_D 1 u a hbA).1
      cases u with
      | zero => exact C0 a b hbA hbB hsA hsB hle
      | succ u' =>
        cases u' with
        | zero => exact le_collapse1_le96 Hp a b hbA hbB hsA hsB hle
        | succ _ => exact absurd hu (by omega)

end

/-! ### §96.5 記号数で切った §77 → §79 → §81 の鎖 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- 記号数で切った頭部の比較。 -/
def DictHeadLtUpTo96 (m : Nat) : Prop := ∀ (u v : Nat) (a b : BT),
    BT.size (BT.D u a) + BT.size (BT.D v b) ≤ m →
    btLe72 1 (BT.D u a) = true → btLe72 1 (BT.D v b) = true →
    BT.isStd (BT.D u a) = true → BT.isStd (BT.D v b) = true →
    (u < v ∨ (u = v ∧ lt (dict a) (dict b) = true)) →
    lt (dict (BT.D u a)) (dict (BT.D v b)) = true

theorem dictHeadLtUpTo96_mono {m n : Nat} (h : m ≤ n) (H : DictHeadLtUpTo96 n) :
    DictHeadLtUpTo96 m :=
  fun u v a b hsz hbA hbB hsA hsB hc => H u v a b (by omega) hbA hbB hsA hsB hc

/-- **記号数で切った §77.4。** `dictLtUpTo_all77` は `DictHeadLt77` を**丸ごと**
    消費していた。ここでは同じ記号数までの頭部の比較しか使わない。 -/
theorem dictLtUpTo_all96 (Hp : PsiIdxOKStd172) :
    ∀ (n : Nat), DictHeadLtUpTo96 n → DictLtUpTo77 n := by
  intro n
  refine Nat.strongRecOn (motive := fun n => DictHeadLtUpTo96 n → DictLtUpTo77 n) n ?_
  intro n IH H f l1 l2 hsz g1 g2 hlt
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
            have d1 : BT.size (BT.D u a) = 1 + BT.size a := rfl
            have d2 : BT.size (BT.D v b) = 1 + BT.size b := rfl
            have ha1 := size_pos77 a
            have hb1 := size_pos77 b
            have hm : n - 2 < n := by omega
            have HQ : DictLtUpTo77 (n - 2) :=
              IH (n - 2) hm (dictHeadLtUpTo96_mono (by omega) H)
            have hhd : BT.size (BT.D u a) + BT.size (BT.D v b) ≤ n := by omega
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
            rw [ltL_DD93] at hlt
            by_cases huv : u < v
            · exact lt_of_hd_lt hiX hiY hB1 hB2
                (H u v a b hhd hbA hbB hsA hsB (Or.inl huv))
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
                    (H u v a b hhd hbA hbB hsA hsB (Or.inr ⟨huv2, hlta⟩))

/-- 記号数で切った §77 の主定理。 -/
theorem dictLt_upTo96 (Hp : PsiIdxOKStd172) {n : Nat} (H : DictHeadLtUpTo96 n) (x y : BT)
    (hsz : BT.size x + BT.size y ≤ n)
    (hbx : btLe72 1 x = true) (hby : btLe72 1 y = true)
    (hsx : BT.isStd x = true) (hsy : BT.isStd y = true)
    (h : BT.lt x y = true) : lt (dict x) (dict y) = true := by
  have t1 := szL77_toL x
  have t2 := szL77_toL y
  have hq := dictLtUpTo_all96 Hp (szL77 (BT.toL x) + szL77 (BT.toL y))
    (dictHeadLtUpTo96_mono (by omega) H)
    (BT.size x + BT.size y + 2) (BT.toL x) (BT.toL y) (Nat.le_refl _)
    (good_toL77 x hsx hbx) (good_toL77 y hsy hby) h
  rw [ofL_toL77 x hsx, ofL_toL77 y hsy] at hq
  exact hq

/-- 記号数で切った非狭義の順序。 -/
def DictLeUpTo96 (n : Nat) : Prop :=
  ∀ (x y : BT), BT.size x + BT.size y ≤ n → btLe72 1 x = true → btLe72 1 y = true →
    BT.isStd x = true → BT.isStd y = true → BT.le x y = true → le (dict x) (dict y) = true

theorem dictLeUpTo96_of_head (Hp : PsiIdxOKStd172) {n : Nat} (H : DictHeadLtUpTo96 n) :
    DictLeUpTo96 n := by
  intro x y hsz hbx hby hsx hsy h
  rcases (Bool.or_eq_true _ _).mp h with h1 | h1
  · rw [bt_beq_eq77 h1]; exact le_self77 _
  · exact le_of_lt (dictLt_upTo96 Hp H x y hsz hbx hby hsx hsy h1)

/-- 記号数で切った成分ひとつぶんの非狭義の順序。 -/
def DictLeAtomUpTo96 (n : Nat) : Prop := ∀ (u v : Nat) (a b : BT),
    BT.size (BT.D u a) + BT.size (BT.D v b) ≤ n →
    btLe72 1 (BT.D u a) = true → btLe72 1 (BT.D v b) = true →
    BT.isStd (BT.D u a) = true → BT.isStd (BT.D v b) = true →
    BT.le (BT.D u a) (BT.D v b) = true →
    le (dict (BT.D u a)) (dict (BT.D v b)) = true

theorem dictLeAtomUpTo96_of_le {n : Nat} (S : DictLeUpTo96 n) : DictLeAtomUpTo96 n :=
  fun _ _ _ _ hsz hbA hbB hsA hsB h => S _ _ hsz hbA hbB hsA hsB h

theorem descMap96_upTo {n : Nat} (A : DictLeAtomUpTo96 n) :
    ∀ (l : List BT), GoodL77 l → szL77 l ≤ n → descL (l.map dict) = true
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | p :: q :: r, hg, hsz => by
      obtain ⟨u, a, rfl⟩ := hg.1 p (List.Mem.head _)
      obtain ⟨v, b, rfl⟩ := hg.1 q (List.Mem.tail _ (List.Mem.head _))
      have e1 : szL77 (BT.D u a :: BT.D v b :: r)
          = BT.size (BT.D u a) + (BT.size (BT.D v b) + szL77 r) := rfl
      have e2 : szL77 (BT.D v b :: r) = BT.size (BT.D v b) + szL77 r := rfl
      have hdd : (BT.le (BT.D v b) (BT.D u a) && descOK72 (BT.D v b :: r)) = true := hg.2.2.2
      refine descL_cons.mpr ⟨?_, descMap96_upTo A (BT.D v b :: r) (goodL77_tail hg) (by omega)⟩
      exact A v u b a (by omega) (hg.2.2.1 _ (List.Mem.tail _ (List.Mem.head _)))
        (hg.2.2.1 _ (List.Mem.head _)) (hg.2.1 _ (List.Mem.tail _ (List.Mem.head _)))
        (hg.2.1 _ (List.Mem.head _)) ((Bool.and_eq_true _ _).mp hdd).1

/-- 記号数で切った完全な橋。 -/
def BridgeUpTo96 (n : Nat) : Prop :=
  ∀ (a : BT), BT.size a ≤ n → btLe72 1 a = true → BT.isStd a = true →
    toList (dict a) = (BT.toL a).map dict

/-- **§96.5 の主定理 — 記号数 `n` までの橋には、記号数 `n` までの非狭義の順序で足りる。**
    §93 が「無い」と言った size-indexed な形は、橋については**これ**である。 -/
theorem bridgeUpTo96_of_leUpTo (Hp : PsiIdxOKStd172) {n : Nat} (S : DictLeUpTo96 n) :
    BridgeUpTo96 n := by
  intro a hsz hb hs
  have hg : GoodL77 (BT.toL a) := good_toL77 a hs hb
  have hb2 : szL77 (BT.toL a) ≤ n := by have := szL77_toL a; omega
  have h := toList_dict_ofL96 Hp (BT.toL a) hg
    (descMap96_upTo (dictLeAtomUpTo96_of_le S) (BT.toL a) hg hb2)
  rw [ofL_toL77 a hs] at h
  exact h

/-- 記号数で切った §81 の残余。 -/
def CollapseMono0HiUpTo96 (m : Nat) : Prop :=
  ∀ (a b : BT), BT.size (BT.D 0 a) + BT.size (BT.D 0 b) ≤ m →
    btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lt (dict a) (dict b) = true →
    lt (collapse 0 (dict a)) (collapse 0 (dict b)) = true

/-- **記号数で切った §81.7。** もとの証明は (a,b) について各点的だったので、そのまま通る。 -/
theorem dictHeadLtUpTo96_of_hi (Hp : PsiIdxOKStd172) {m : Nat}
    (H : CollapseMono0HiUpTo96 m) : DictHeadLtUpTo96 m := by
  intro u v a b hsz hbA hbB hsA hsB hc
  rcases hc with huv | ⟨huv, hlt⟩
  · exact dictCross79 Hp u v a b huv hbA hbB hsA hsB
  · subst huv
    have hu := (btLe72_D 1 u a hbA).1
    have hba := (btLe72_D 1 u a hbA).2
    have hbb := (btLe72_D 1 u b hbB).2
    have hsa := isStd_of_D hsA
    have hsb := isStd_of_D hsB
    cases u with
    | zero =>
      have hia := inT_dict_of_std172 Hp a hba hsa
      have hib := inT_dict_of_std172 Hp b hbb hsb
      rw [Trans.Dict.dict_D, Trans.Dict.dict_D]
      by_cases hWb : le (reg 1) (dict b) = true
      · by_cases hWa : le (reg 1) (dict a) = true
        · exact H a b hsz hbA hbB hsA hsB hWa hWb hlt
        · have hlow : lowHd81 a = true := by
            cases hh : lowHd81 a with
            | true => rfl
            | false => exact absurd (le_reg1_dict_of_not_lowHd81 Hp a hba hsa hh) hWa
          have hb0 : btLe72 0 a = true :=
            btLe0_of_lowHd81 a hba hsa hlow (lowHd_GB_of_std81 hsA hlow)
          exact lt_collapse0_cross81 hia.1 (lt_dict_E81 Hp a hb0 hsa) hib.1 hib.2
            (Hp 0 b (by omega) hbb hsB) hWb
      · have hlb : lt (dict b) (reg 1) = true :=
          lt_of_not_le_inT inT_W79 hib.1 (bool_false hWb)
        have hla : lt (dict a) (reg 1) = true := lt_trans_inT hia.1 hib.1 inT_W79 hlt hlb
        exact collapse0_mono_ltW81 hia.1 hib.1 hla hlb hlt
    | succ u' =>
      cases u' with
      | zero =>
        rw [Trans.Dict.dict_D, Trans.Dict.dict_D]
        exact collapseMono1_79 Hp a b hbA hbB hsA hsB hlt
      | succ _ => exact absurd hu (by omega)

/-- **§96.5 の系 — 記号数 `n` までの §81 の残余だけで、記号数 `n` までの橋が立つ。** -/
theorem bridgeUpTo96_of_hi (Hp : PsiIdxOKStd172) {n : Nat}
    (H : CollapseMono0HiUpTo96 n) : BridgeUpTo96 n :=
  bridgeUpTo96_of_leUpTo Hp (dictLeUpTo96_of_head Hp (dictHeadLtUpTo96_of_hi Hp H))

end

/-! ### §96.6 否定 — `plus` は本当に落とし、§93 の半橋はそれを見ない -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- **手で組んだ反例。** `1 ⊕ Ω₁` = `ψ₀0 ⊕ ψ₁0` — 記号 5 個。 -/
def aDrop96 : BT := BT.sum (BT.D 0 BT.zero) (BT.D 1 BT.zero)

/-- 成分は主要・標準・段 1 以下。**降べきだけが偽。** -/
theorem aDrop96_facts : (btLe72 1 aDrop96, BT.isStd aDrop96,
    (BT.toL aDrop96).all BT.isP, (BT.toL aDrop96).all BT.isStd,
    (BT.toL aDrop96).all (btLe72 1), descOK72 (BT.toL aDrop96))
    = (true, false, true, true, true, false) := rfl

/-- **`plus` は成分を落とす。** 像の成分は 1 つ、`BT` の成分は 2 つ。 -/
theorem bridge_drops96 : toList (dict aDrop96) ≠ (BT.toL aDrop96).map dict := by
  intro h
  have h1 : (toList (dict aDrop96)).length = ((BT.toL aDrop96).map dict).length :=
    congrArg List.length h
  rw [show (toList (dict aDrop96)).length = 1 from rfl,
    show ((BT.toL aDrop96).map dict).length = 2 from rfl] at h1
  exact absurd h1 (by omega)

/-- 同じことを §96.1 の同値の側から見た形 — 像が降べきでない。 -/
theorem desc_drops96 : descL ((BT.toL aDrop96).map dict) = false := rfl

/-- **§93 の半橋はこの項で成り立つ。** 前半しか見ないので落下が見えない。
    `HiBridge93` は `FullBridge96` より真に弱い。 -/
theorem hiBridge_blind96 : hiW89 (dict aDrop96) = dict (hiB93 aDrop96) := rfl

/-- 326 行目 — §93 の橋を非狭義の順序に置き換えた形。 -/
theorem certIn_t326_le96 (Hp : PsiIdxOKStd172) (S : DictLe96)
    (F : CollapseMono0HiFree93) (L : LoDomPair91)
    (HCD : CofDenseS1) (HBC : BCofIn71)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_free93 Hp (hiBridge96_of_le Hp S) F L HCD HBC hacc

end

/-! ### §96.7 測定 (凍結)

**構成。** §93.9 の母集団を**そのまま**使う — §93 のものは `private` なので同じ構成を
`96` の名で再宣言し、内訳 `(1532, 592, 592, 300, 290, 292)` を `#guard` で固定して
同一であることを確かめている。種 `bs96` は段 1 以下の 6 項、**深さの線** `deep96` は
`ψ₀`・`ψ₁` を 1 段ずつかぶせて 2 つに 1 つ間引く操作を 5 回、**入れ子の線** `nest96` は
和に帽子をかぶせたもの、**幅の線** `wide96` は 2 項和と 3 項和、**文から作った線**
`bad96` は前半が 2 成分以上で `ψ₀` の下に和が入る形。

    popAll96  1532 項
    popGood96  592 項  `BT.isStd` かつ段 1 以下
    popK96     300 項  さらに `BT.isStd (ψ₀ ·)`
    popHi96    290 項  さらに `Ω₁ ≤ dict a`
    popNK96    292 項  `K` の条件だけが偽 (負の対照)

対の母集団は `hipop96` (`popHi96` を 3 つに 1 つ、97 項) と `kpop96` (`popK96` を
3 つに 1 つ、100 項)。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

private def dedup96 (l : List BT) : List BT :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []
private def dedupT96 (l : List TM.Term) : List TM.Term :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []
private def every96 (k : Nat) (l : List BT) : List BT :=
  (l.zipIdx.filter (fun p => p.2 % k == 0)).map (·.1)

private def bs96 : List BT :=
  [BT.zero, BT.D 0 BT.zero, BT.D 0 (BT.D 0 BT.zero), BT.D 1 BT.zero,
   BT.D 1 (BT.D 1 BT.zero), BT.D 0 (BT.D 1 BT.zero)]
private def cap01_96 (l : List BT) : List BT := l.map (BT.D 0) ++ l.map (BT.D 1)
private def lay96 : Nat → List BT → List BT
  | 0, l => l
  | n + 1, l => every96 2 (cap01_96 (lay96 n l))
private def deep96 : List BT :=
  dedup96 (bs96 ++ lay96 1 bs96 ++ lay96 2 bs96 ++ lay96 3 bs96 ++ lay96 4 bs96
            ++ lay96 5 bs96)
private def prin96 (l : List BT) : List BT := l.filter BT.isP
private def sums2_96 (l : List BT) : List BT :=
  (prin96 l).flatMap (fun a => ((prin96 l).filter (fun b => BT.le b a)).map (BT.sum a))
private def sums3_96 (l : List BT) : List BT :=
  (prin96 l).flatMap (fun a =>
    ((prin96 l).filter (fun b => BT.le b a)).flatMap (fun b =>
      ((prin96 l).filter (fun c => BT.le c b)).map (fun c => BT.sum a (BT.sum b c))))
private def nest96 : List BT :=
  dedup96 (every96 2 (cap01_96 (sums2_96 (every96 2 deep96))))
private def wide96 : List BT :=
  dedup96 (every96 4 (sums2_96 (every96 2 (deep96 ++ nest96)))
            ++ every96 9 (sums3_96 (every96 3 deep96)))
private def bad96 : List BT :=
  dedup96 ((deep96 ++ sums2_96 bs96 ++ sums2_96 (every96 2 deep96)).flatMap
    (fun c => [BT.sum (BT.D 1 BT.zero) (BT.D 0 c),
               BT.sum (BT.D 1 BT.zero) (BT.sum (BT.D 1 BT.zero) (BT.D 0 c)),
               BT.sum (BT.D 1 (BT.D 1 BT.zero)) (BT.D 0 c),
               BT.sum (BT.D 1 (BT.D 1 BT.zero)) (BT.sum (BT.D 1 BT.zero) (BT.D 0 c))]))

private def popAll96 : List BT := dedup96 (deep96 ++ nest96 ++ wide96 ++ bad96)
private def popStd96 : List BT := popAll96.filter BT.isStd
private def popGood96 : List BT := popAll96.filter (fun x => btLe72 1 x && BT.isStd x)
private def popK96 : List BT := popGood96.filter (fun a => BT.isStd (BT.D 0 a))
private def lowW96 (a : BT) : Bool := TM.Term.lt (dict a) (reg 1)
private def popHi96 : List BT := popK96.filter (fun a => !(lowW96 a))
private def popNK96 : List BT := popGood96.filter (fun a => !(BT.isStd (BT.D 0 a)))

/-- 完全な橋の判定器。 -/
private def fullOK96 (a : BT) : Bool := toList (dict a) == (BT.toL a).map dict
/-- 像の降べきの判定器。 -/
private def descOKmap96 (a : BT) : Bool := descL ((BT.toL a).map dict)
/-- §93 の半橋の判定器。 -/
private def hiOK96 (a : BT) : Bool := hiW89 (dict a) == dict (hiB93 a)

/-! 母集団は §93.9 のものと同一。 -/
#guard (popAll96.length, popStd96.length, popGood96.length, popK96.length,
        popHi96.length, popNK96.length) == (1532, 592, 592, 300, 290, 292)

/-! **受領 1 — 完全な橋と像の降べきは同じもの。** 仮説を満たす 592 項では破れ 0、
    `K` の条件が偽の 292 項でも 0、そして**母集団全体では 20 項で破れる**。
    その 20 項で `descL` も同時に破れる — 全 1532 項で二つの判定器の食い違いは 0。
    §96.1 の同値が母集団に見えている。20 項はすべて段 1 以下で、`BT.isStd` はどれも偽。 -/
#guard (popGood96.countP (fun a => !(fullOK96 a)), popK96.countP (fun a => !(fullOK96 a)),
        popHi96.countP (fun a => !(fullOK96 a)), popNK96.countP (fun a => !(fullOK96 a)),
        popAll96.countP (fun a => !(fullOK96 a))) == (0, 0, 0, 0, 20)
#guard (popAll96.countP (fun a => fullOK96 a != descOKmap96 a),
        (popAll96.filter (fun a => !(fullOK96 a))).countP BT.isStd,
        (popAll96.filter (fun a => !(fullOK96 a))).countP (btLe72 1)) == (0, 0, 20)

/-! **受領 2 — §93 の半橋は 1532 項すべてで成立する。** 落ちる 20 項でも成立する。
    半橋は完全な橋より真に弱く、`aDrop96` (§96.6) がその最小の証人である。 -/
#guard (popAll96.countP (fun a => !(hiOK96 a)),
        popAll96.countP (fun a => hiOK96 a && !(fullOK96 a))) == (0, 20)

/-! **受領 3 — 隣り合う成分の対の内訳。** 段をまたぐ 400 対は `dictLt_cross96` で只、
    100 対は同じ項、157 対は添字 1、**Veblen の折り畳みに触るのは 30 対 (4.4%) だけ**。 -/
private def adjPairs96 : List BT → List (BT × BT)
  | [] => []
  | [_] => []
  | p :: q :: r => (p, q) :: adjPairs96 (q :: r)
private def subOf96 : BT → Nat
  | .D u _ => u
  | _ => 99
private def allAdj96 : List (BT × BT) := popGood96.flatMap (fun a => adjPairs96 (BT.toL a))
private def eqSubAdj96 : List (BT × BT) :=
  allAdj96.filter (fun p => subOf96 p.1 == subOf96 p.2 && !(p.1 == p.2))

#guard (allAdj96.length, allAdj96.countP (fun p => subOf96 p.2 < subOf96 p.1),
        allAdj96.countP (fun p => BT.le p.2 p.1 && (p.1 == p.2)),
        eqSubAdj96.length, eqSubAdj96.countP (fun p => subOf96 p.1 == 0),
        eqSubAdj96.countP (fun p => subOf96 p.1 == 1)) == (687, 400, 100, 187, 30, 157)

/-! **受領 4 (負) — 母集団は非狭義と狭義の差を見ない。** `dict` は 592 項で単射
    (衝突 0) なので、`kpop96` の 5050 個の `le` 対のうち狭義でないのは対角の 100 対
    だけ。`CollapseLe0_96` の結論は 0 回破れるが、**それは §79 の狭義の条項が
    0 回破れることと同じ事実である。** 掃除が綺麗なことは何の証拠にもならない。 -/
private def pairs96 (l : List BT) : List (BT × BT) :=
  l.flatMap (fun a => l.map (fun b => (a, b)))
private def kpop96 : List BT := dedup96 (every96 3 popK96)
private def lepairs96 : List (BT × BT) :=
  (pairs96 kpop96).filter (fun p => TM.Term.le (dict p.1) (dict p.2))

#guard (popGood96.length, (dedupT96 (popGood96.map dict)).length) == (592, 592)
#guard (kpop96.length, lepairs96.length,
        lepairs96.countP (fun p =>
          !(TM.Term.le (collapse 0 (dict p.1)) (collapse 0 (dict p.2)))),
        lepairs96.countP (fun p => !(TM.Term.lt (dict p.1) (dict p.2))),
        lepairs96.countP (fun p => p.1 == p.2)) == (100, 5050, 0, 100, 100)

/-! **受領 5 — 素朴な測度はどこで壊れるか。** 4656 の残余の対で、門自身の再帰の相手
    `(c, hi b)` は **4656 対すべてで** `size a + size b` より小さい。壊すのは §93.6 が
    同時に要る**順序**の相手 `(c, a)` で、`size c > size b` が **117 対 (2.5%)**、
    `size c ≥ size b` が 173 対。`size c ≥ size a` は **0 対** — §82 の `G(a,0) < a` が
    記号数の水準で効いている。だから `size a` だけで測る読みが試すべきものになる。 -/
private def hipop96 : List BT := dedup96 (every96 3 popHi96)
private def hipairs96 : List (BT × BT) :=
  (pairs96 hipop96).filter (fun p => TM.Term.lt (dict p.1) (dict p.2))
private def loArgs96 (a : BT) : List BT :=
  (loL93 (BT.toL a)).filterMap (fun t => match t with | BT.D 0 c => some c | _ => none)

#guard (hipop96.length, hipairs96.length,
        hipairs96.countP (fun p => !(loArgs96 p.1).isEmpty),
        hipairs96.countP (fun p => (loArgs96 p.1).any (fun c => BT.size c ≥ BT.size p.2)),
        hipairs96.countP (fun p => (loArgs96 p.1).any (fun c => BT.size c > BT.size p.2)),
        hipairs96.countP (fun p => (loArgs96 p.1).any (fun c => BT.size c ≥ BT.size p.1)),
        hipairs96.countP (fun p => (loArgs96 p.1).any
          (fun c => BT.size c + BT.size (hiB93 p.2) ≥ BT.size p.1 + BT.size p.2)))
        == (97, 4656, 3459, 173, 117, 0, 0)

/-! 母集団の記号数の上限。 -/
#guard (popHi96.foldl (fun m a => max m (BT.size a)) 0,
        popGood96.foldl (fun m a => max m (BT.size a)) 0) == (33, 33)

end

/-! ## §97 THE LOW SIDE OF THE DENSITY GATE IS A THEOREM — `dict` IS ONTO BELOW `ε₀`

§94 split row 326's density clause in two at `ε₀` (`dictDense85_iff94`) and named exactly
what the low half was missing: four 𝔗(M)-side order facts, `φ̄0` unskipped at every argument
below `ε₀`, and §94.5's transfer.  **§97 proves the low half.**  `DictDenseLo94` is no
longer a hypothesis — `dictDenseLo97` derives it from `PsiIdxOKStd172` and `DictLtA74`, the
two clauses row 326 already carries, and from nothing else.  What is left of `CofDenseS1`
is `DictDenseHi94` alone.

**The low side is not density, it is SURJECTIVITY, and the inverse is TOTAL.**  §94.7
measured that `s ↦ ψ₀(inv s)` reproduces 207 of 207 terms of the CNF fragment.  §97.5 turns
that measurement into `dictInv97`: for EVERY Cantor normal form `s` — and below `ε₀` that
is every term of 𝔗(M), §97.3 — the term `invE97 s` is a legal witness (level ≤ 1, standard,
every component `D 0`) and `dict (invE97 s) = s` exactly.  The density conclusion then takes
the witness to be the challenger's own preimage: `s ≤ dict (invE97 s) = s < vOf t`.

  §97.1  **THE SUM FACTS.**  `plus_eq_add97` : under `inT`, the normal sum IS the formal
         sum, `plus a b = a ⊕ b`.  Two of the other three the §94 preamble asked for were
         already in the repository, and are only restated in `⊕` form here — `le_left_add97`
         and `le_right_add97`, from §81's `le_self_plus_ap81` and §75's `le_self_plus75` —
         together with their strict forms.  The fourth, `d < φ̄0d`, is §12's `lt_pow_self`.

  §97.2  **`φ̄0` IS UNSKIPPED AT EVERY CN ARGUMENT.**  `phiNF_zero_cn97` : `phiNF 0 b = φ̄0b`
         for every Cantor normal form `b`; §94.2 had this only for arguments of the shape
         `φ̄0Y`.  The content is that `splitFin`'s first component can only be `0`, a `φ̄0·`
         or a `⊕` (`splitFin_shape97`), so `phiNFsucc` falls through to its default line
         every time.  `omegaNF_cn97` and `collapse0_cn97` are the consequences: below `ε₀`,
         `ψ₀` is the raw `φ̄0`.

  §97.3  **`inT` AND `CN` ARE THE SAME CONDITION BELOW `ε₀`.**  `lt_E081_cn97` one way, and
         `cn_of_ltE97` the other, from §9's `cof_eps0` and §13's downward closure.  This is
         what makes the inverse total rather than partial.

  §97.4  **THE COEFFICIENT SET, READ ON THE 𝔗(M) SIDE.**  `gsub97` mirrors `GB 0` through
         `invE97` (`GB_invE97`), and `lt_gsub97` says every element of it is below the term.
         That is the whole content of the standardness of `invE97 s`, and it is assembled
         from `lt_pow_self` and §97.1's two sum inequalities and nothing else.

  §97.5  **THE MAIN THEOREM.**  `dictInv97`, by one induction on the degree.  The
         standardness step is where §94.5's transfer is spent: `btlt_of_lt94` carries
         `lt e b` back to `BT.lt (invE97 e) (invE97 b)`, and `btle_of_le94` carries the
         descending condition of a sum.  That is the ONLY place the two carried hypotheses
         are used.

  §97.6  **`DictDenseLo94`, AND ROW 326.**  `dictDenseLo97`, `dictDense85_of97`,
         `dictOnto85_of97` and `certIn_t326_97`: on the cofinality side row 326 now waits on
         `DictDenseHi94` and on nothing else.

  §97.7  **THE LEVEL BOUND, HONESTLY, AND FOUR REFUTATIONS.**  `btLe0_invE97` : the
         construction never emits an index above `0`.  §85.6 refutes the clause one level
         up; §97 does not go there, and that is a theorem here, not a remark.  The four
         mutants pin the hypotheses: `plus_eq_add_needs_inT97` (`1 ⊕ ω`),
         `phiNF_zero_needs_cn97` (the skip is exactly at `ε₀` — `phiNF 0 ε₀ = ε₀`, not
         `φ̄0ε₀`), `dictInv97_needs_ltE97` (`ω^(ε₀+1)` has preimage `1`) and
         `dictInv97_needs_inT97` (`1 ⊕ ω` again, on the standardness side).

  §97.8  **§9's JUNK TERM, LIFTED TO THE CLAUSE.**  `denseLo_needs_inT97` : delete `inT s`
         from the low clause — even after relaxing the target all the way up to `ε₀` — and
         it is FALSE.  `φ̄(0 ⊕ M, 0)` is below `ε₀` and above every CN term
         (`le_junk_cn97`), hence above the whole image of `dict` there, so no witness
         exists.  This is §9's `cof_eps0_needs_inT` one floor up.

WHAT IS **NOT** CLAIMED.  `DictDense85` is NOT proved and `CofDenseS1` is NOT closed:
`DictDenseHi94` — challenger AND target at or above `ε₀` — is untouched, and §94.6's raw
`φ̄` tower over `Γ₀` lives there, not here.  `PsiIdxOKStd172` and `DictLtA74` are not proved
and §97 does not weaken them; it uses them, in one place, and says where.  Nothing here
touches level two, where §85.6 proves the clause FALSE.

WHAT THE MEASUREMENT SAYS (§97.9 gives the construction).  Two populations, and the point of
both is that the hypothesis is VISIBLE — §93's bridge held 292/292 where its hypothesis
FAILED, and that is the failure mode this design is built to avoid.

  * **117 terms below `ε₀`, 8 of them Cantor normal forms and 109 not.**  Grown from
    `[0, 1, ω, ε₀, φ̄(0 ⊕ M, 0)]` by `φ̄0·`, by the normal sum AND by the RAW `⊕` (which
    manufactures ascending, ill-formed sums), then filtered by `· < ε₀` ALONE — not by
    `inT`.  On all 117, "`invE97 s` is a legal witness and `dict` of it is `s`" holds
    **exactly when `CN s`**: 8 hits, 109 misses, 0 disagreements.
  * **The sweep is not carried by a trivial conjunct.**  `bgood94 (invE97 s)` alone is true
    10 times, not 8 — `invE97` answers `0` on junk and `0` is a legal witness.  The
    discriminating half is `dict (invE97 s) = s`.
  * **`inT` and `CN` coincide on all 117** — 0 terms with `inT` but not `CN`, and 0 the
    other way.  §97.3, as a computation.
  * **§94.7's populations, reused.**  Its 207-term low population lies entirely inside the
    hypothesis (207 of 207 are `CN`), and `invE97` agrees with §94.7's `invE94` on all 207 —
    so §94's 207/207 measurement is now a corollary, not evidence.  Of §94.7's 221
    challengers exactly 9 are `CN` and exactly 9 are below `ε₀`, and they are the same 9;
    the identity above holds on all 221; and NOT ONE of its 74 hard challengers is `CN` —
    a hard challenger has no legal Buchholz preimage, and §97.5 builds one for every `CN`
    term.  All 12 of §94.7's 2093 pairs that fall to `DictDenseLo94` have a `CN` challenger,
    so all 12 are now theorems.
  * **The negative, BUILT.**  `φ̄(0 ⊕ M, 0)` is below `ε₀`, above all 12 measured towers, and
    `invE97` answers `0` on it — a LEGAL witness that is NOT above the challenger
    (`le junk97 (dict (invE97 junk97)) = false`).  So "the image is a legal witness" is not
    the load-bearing half of §97.5; `1 ⊕ ω` is the same lesson on the standardness side.
    And §94.6's raw `φ̄` tower over `Γ₀` is not `CN` at any of its four rungs: the low side
    does not reach it, and does not claim to. -/

/-! ### §97.1 和の三つの事実 -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg)
open TM TM.Term
open Evidence.WF

/-- `CN ⊆ inT`。 -/
theorem inT_of_cn97 {t : Term} (h : CN t = true) : inT t = true :=
  inT_of_cnv t (cnv_of_cn t h)

/-- **(1) `plus a b = a ⊕ b`。** `inT` の形式和では正規和は形式和そのもの。 -/
theorem plus_eq_add97 {a b : Term} (h : inT (add a b) = true) : plus a b = add a b := by
  obtain ⟨hap, hia, hib, hhd⟩ := inT_add h
  have hbz : b ≠ zero := by intro hz; rw [hz] at hhd; exact Bool.noConfusion hhd
  cases hbl : toList b with
  | nil => exact absurd (toList_eq_nil b hbl) hbz
  | cons b1 r =>
    have hle : le b1 a = true := by
      rw [hdLe_eq_of_toList (a := a) hbl] at hhd; exact hhd
    rw [plus_cons66 hbl, toList_isAP81 hap,
      show List.filter (fun x => le b1 x) [a] = [a] from by
        rw [List.filter_cons_of_pos (by rw [hle])]; rfl]
    show add a (ofList (b1 :: r)) = add a b
    rw [← hbl, inT_ofList_toList b hib]

/-- **(2) `a ≤ a ⊕ b`。** -/
theorem le_left_add97 {a b : Term} (h : inT (add a b) = true) : le a (add a b) = true := by
  obtain ⟨hap, hia, hib, _⟩ := inT_add h
  rw [← plus_eq_add97 h]
  exact le_self_plus_ap81 hia hap hib

/-- **(3) `b ≤ a ⊕ b`。** -/
theorem le_right_add97 {a b : Term} (h : inT (add a b) = true) : le b (add a b) = true := by
  obtain ⟨_, hia, hib, _⟩ := inT_add h
  rw [← plus_eq_add97 h]
  exact le_self_plus75 hia hib


/-- `b ≠ a ⊕ b` — 次数で分かる。 -/
theorem ne_add_right97 (a b : Term) : b ≠ add a b := by
  intro h
  have hd : b.deg = (add a b).deg := congrArg Term.deg h
  rw [show (add a b).deg = 1 + a.deg + b.deg from rfl] at hd
  have := deg_pos a
  omega

/-- `a ≠ a ⊕ b`。 -/
theorem ne_add_left97 (a b : Term) : a ≠ add a b := by
  intro h
  have hd : a.deg = (add a b).deg := congrArg Term.deg h
  rw [show (add a b).deg = 1 + a.deg + b.deg from rfl] at hd
  have := deg_pos b
  omega

/-- **(2') `a < a ⊕ b`。** -/
theorem lt_left_add97 {a b : Term} (h : inT (add a b) = true) : lt a (add a b) = true := by
  rcases (Bool.or_eq_true _ _).mp (le_left_add97 h) with h1 | h1
  · exact absurd (eq_of_beq h1) (ne_add_left97 a b)
  · exact h1

/-- **(3') `b < a ⊕ b`。** -/
theorem lt_right_add97 {a b : Term} (h : inT (add a b) = true) : lt b (add a b) = true := by
  rcases (Bool.or_eq_true _ _).mp (le_right_add97 h) with h1 | h1
  · exact absurd (eq_of_beq h1) (ne_add_right97 a b)
  · exact h1

/-! ### §97.2 `φ̄0` は `ε₀` の下で飛ばさない -/

/-- CN の成分はすべて `φ̄0·`。 -/
theorem toList_cn_isPow97 : ∀ (b : Term), CN b = true → ∀ x ∈ toList b, isPow x = true
  | zero, _, _, hx => by cases hx
  | M, h, _, _ => Bool.noConfusion h
  | omg _, h, _, _ => Bool.noConfusion h
  | psi _ _, h, _, _ => Bool.noConfusion h
  | Z _, h, _, _ => Bool.noConfusion h
  | phi a c, h, x, hx => by
      obtain ⟨ha, _⟩ := cn_phi h
      subst ha
      rw [List.mem_singleton.mp (show x ∈ [phi zero c] from hx)]
      rfl
  | add a c, h, x, hx => by
      obtain ⟨hp, _, hc, _⟩ := cn_add h
      rcases List.mem_cons.mp (show x ∈ a :: toList c from hx) with h1 | h1
      · rw [h1]; exact hp
      · exact toList_cn_isPow97 c hc x h1

/-- `φ̄0·` の列を組み直したものの形は 3 通りしかない。 -/
theorem shape_ofList97 : ∀ (L : List Term), (∀ x ∈ L, isPow x = true) →
    ofList L = zero ∨ (∃ e, ofList L = phi zero e) ∨ (∃ u v, ofList L = add u v)
  | [], _ => Or.inl rfl
  | [a], h => by
      obtain ⟨e, he⟩ := eq_pow_of_isPow (h a (List.Mem.head _))
      exact Or.inr (Or.inl ⟨e, he⟩)
  | _ :: b :: r, _ => Or.inr (Or.inr ⟨_, ofList (b :: r), rfl⟩)

/-- `splitFin` の第一成分の形。 -/
theorem splitFin_shape97 {b : Term} (hb : CN b = true) :
    (splitFin b).1 = zero ∨ (∃ e, (splitFin b).1 = phi zero e) ∨
      (∃ u v, (splitFin b).1 = add u v) := by
  show ofList (List.take ((toList b).length -
      ((List.takeWhile (fun x => x == one) (toList b).reverse).length)) (toList b)) = zero ∨ _
  refine shape_ofList97 _ ?_
  intro x hx
  exact toList_cn_isPow97 b hb x (List.mem_of_mem_take hx)

/-- CN のところでは `phiNFsucc` は既定の枝に落ちる。 -/
theorem phiNFsucc_zero97 {b : Term} (hb : CN b = true) :
    phiNFsucc zero b = phiNFdefault zero b := by
  rcases splitFin_shape97 hb with h1 | ⟨e, h1⟩ | ⟨u, v, h1⟩
  · have heq : splitFin b = ((zero : Term), (splitFin b).2) := by rw [← h1]
    unfold phiNFsucc; rw [heq]
    split
    rename_i g m hgm
    injection hgm with hg _
    subst hg
    by_cases hm : m ≥ 1
    · rw [if_pos hm]; rfl
    · rw [if_neg hm]
  · have heq : splitFin b = (phi zero e, (splitFin b).2) := by rw [← h1]
    unfold phiNFsucc; rw [heq]
    split
    rename_i g m hgm
    injection hgm with hg _
    subst hg
    by_cases hm : m ≥ 1
    · rw [if_pos hm]; rfl
    · rw [if_neg hm]
  · have heq : splitFin b = (add u v, (splitFin b).2) := by rw [← h1]
    unfold phiNFsucc; rw [heq]
    split
    rename_i g m hgm
    injection hgm with hg _
    subst hg
    by_cases hm : m ≥ 1
    · rw [if_pos hm]; rfl
    · rw [if_neg hm]

/-- CN の項は強臨界ではない。 -/
theorem isSC_cn97 {b : Term} (h : CN b = true) : b.isSC = false := by
  cases b <;> first | rfl | exact Bool.noConfusion h

/-- **(4) `φ̄0` は CN のところで飛ばさない。** -/
theorem phiNF_zero_cn97 {b : Term} (hb : CN b = true) : phiNF zero b = phi zero b := by
  have key : phiNF zero b = phiNFsucc zero b := by
    unfold phiNF
    rw [isSC_cn97 hb, Bool.false_and, if_neg (by intro hc; exact Bool.noConfusion hc)]
    cases b with
    | zero => rfl
    | M => exact Bool.noConfusion hb
    | omg _ => exact Bool.noConfusion hb
    | psi _ _ => exact Bool.noConfusion hb
    | Z _ => exact Bool.noConfusion hb
    | add _ _ => rfl
    | phi c d =>
        obtain ⟨hc, _⟩ := cn_phi hb
        subst hc
        show (if lt zero zero = true then phi zero d else phiNFsucc zero (phi zero d))
            = phiNFsucc zero (phi zero d)
        rw [lt_irrefl]
        exact if_neg (by intro hc; exact Bool.noConfusion hc)
  rw [key, phiNFsucc_zero97 hb, phiNFdefault_zero94]

/-- CN の項は `M` より下。 -/
theorem lt_M_cn97 {b : Term} (hb : CN b = true) : lt b M = true := cnv_lt_M b (cnv_of_cn b hb)

theorem ltM_left_cn97 {b : Term} (hb : CN b = true) : lt M b = false :=
  lt_asymm_inT (inT_of_cn97 hb) (show inT M = true from rfl) (lt_M_cn97 hb)

/-- **CN のところでは `ω^·` は生の `φ̄0`。** -/
theorem omegaNF_cn97 {b : Term} (hb : CN b = true) : omegaNF b = phi zero b := by
  rw [omegaNF_of_le_M (ltM_left_cn97 hb), phiNF_zero_cn97 hb]

/-! ### §97.3 CN の項はみな `ε₀` より下 -/

theorem lt_pow_E97 (c : Term) : lt (phi zero c) E081 = lt c E081 := by
  rw [show E081 = phi one zero from rfl,
    lt_phi_phi (by intro hc; injection hc with h1 _; exact Term.noConfusion h1),
    if_neg (by intro hc; exact Term.noConfusion hc),
    if_pos (show lt zero one = true from by decide)]

theorem lt_E081_cn97 : ∀ (b : Term), CN b = true → lt b E081 = true
  | zero, _ => lt_zero_E81
  | M, h => Bool.noConfusion h
  | omg _, h => Bool.noConfusion h
  | psi _ _, h => Bool.noConfusion h
  | Z _, h => Bool.noConfusion h
  | phi a c, h => by
      obtain ⟨ha, hc⟩ := cn_phi h
      subst ha
      rw [lt_pow_E97]
      exact lt_E081_cn97 c hc
  | add a c, h => by
      rw [show lt (add a c) E081 = lt a E081 from lt_add_phi a c one zero]
      exact lt_E081_cn97 a (cn_add h).2.1

/-- **CN のところでは `ψ₀` は生の `φ̄0`。** -/
theorem collapse0_cn97 {b : Term} (hb : CN b = true) : collapse 0 b = phi zero b := by
  have hi := inT_of_cn97 hb
  rw [collapse0_eq77 b hi
      (fun p hp => ltW_toList79 b hi (ltW_of_ltE81 hi (lt_E081_cn97 b hb)) p hp),
    omegaNF_cn97 hb]

/-! ### §97.4 逆写像とその係数集合 -/

/-- `ε₀` の下の項を Buchholz 側へ戻す写像 — §94.7 の `invE94` そのもの。 -/
def invE97 : Term → BT
  | zero => BT.zero
  | phi a b => match a with | zero => BT.D 0 (invE97 b) | _ => BT.zero
  | add a b => BT.sum (invE97 a) (invE97 b)
  | _ => BT.zero

/-- `GB 0 (invE97 s)` の 𝔗(M) 側の原像。 -/
def gsub97 : Term → List Term
  | phi a b => match a with | zero => b :: gsub97 b | _ => []
  | add a b => gsub97 a ++ gsub97 b
  | _ => []

theorem invE97_phi0 (b : Term) : invE97 (phi zero b) = BT.D 0 (invE97 b) := rfl
theorem invE97_add (a b : Term) : invE97 (add a b) = BT.sum (invE97 a) (invE97 b) := rfl
theorem gsub97_phi0 (b : Term) : gsub97 (phi zero b) = b :: gsub97 b := rfl
theorem gsub97_add (a b : Term) : gsub97 (add a b) = gsub97 a ++ gsub97 b := rfl

/-- 係数集合の元は真に小さい部分項。 -/
theorem deg_gsub97 : ∀ (s : Term), ∀ e ∈ gsub97 s, e.deg < s.deg
  | zero, _, hx => by cases hx
  | M, _, hx => by cases hx
  | omg _, _, hx => by cases hx
  | psi _ _, _, hx => by cases hx
  | Z _, _, hx => by cases hx
  | phi a b, e, hx => by
      cases a with
      | zero =>
          rcases List.mem_cons.mp (show e ∈ b :: gsub97 b from hx) with h1 | h1
          · rw [h1]; show b.deg < 1 + (zero : Term).deg + b.deg; omega
          · have := deg_gsub97 b e h1
            show e.deg < 1 + (zero : Term).deg + b.deg; omega
      | M => cases hx
      | omg _ => cases hx
      | psi _ _ => cases hx
      | Z _ => cases hx
      | phi _ _ => cases hx
      | add _ _ => cases hx
  | add a b, e, hx => by
      rcases List.mem_append.mp (show e ∈ gsub97 a ++ gsub97 b from hx) with h1 | h1
      · have := deg_gsub97 a e h1
        show e.deg < 1 + a.deg + b.deg
        have := deg_pos b; omega
      · have := deg_gsub97 b e h1
        show e.deg < 1 + a.deg + b.deg
        have := deg_pos a; omega

/-- 係数集合の元も CN。 -/
theorem cn_gsub97 : ∀ (s : Term), CN s = true → ∀ e ∈ gsub97 s, CN e = true
  | zero, _, _, hx => by cases hx
  | M, h, _, _ => Bool.noConfusion h
  | omg _, h, _, _ => Bool.noConfusion h
  | psi _ _, h, _, _ => Bool.noConfusion h
  | Z _, h, _, _ => Bool.noConfusion h
  | phi a b, h, e, hx => by
      obtain ⟨ha, hb⟩ := cn_phi h
      subst ha
      rcases List.mem_cons.mp (show e ∈ b :: gsub97 b from hx) with h1 | h1
      · rw [h1]; exact hb
      · exact cn_gsub97 b hb e h1
  | add a b, h, e, hx => by
      obtain ⟨_, ha, hb, _⟩ := cn_add h
      rcases List.mem_append.mp (show e ∈ gsub97 a ++ gsub97 b from hx) with h1 | h1
      · exact cn_gsub97 a ha e h1
      · exact cn_gsub97 b hb e h1

/-- **係数集合の元はもとの項より小さい。** `d < φ̄0d` (§12 の `lt_pow_self`) と
    (2')(3') の和の不等式だけでできている。 -/
theorem lt_gsub97 : ∀ (s : Term), CN s = true → ∀ e ∈ gsub97 s, lt e s = true
  | zero, _, _, hx => by cases hx
  | M, h, _, _ => Bool.noConfusion h
  | omg _, h, _, _ => Bool.noConfusion h
  | psi _ _, h, _, _ => Bool.noConfusion h
  | Z _, h, _, _ => Bool.noConfusion h
  | phi a b, h, e, hx => by
      obtain ⟨ha, hb⟩ := cn_phi h
      subst ha
      rcases List.mem_cons.mp (show e ∈ b :: gsub97 b from hx) with h1 | h1
      · rw [h1]; exact lt_pow_self b hb
      · exact lt_trans_inT (inT_of_cn97 (cn_gsub97 b hb e h1)) (inT_of_cn97 hb)
          (inT_of_cn97 h) (lt_gsub97 b hb e h1) (lt_pow_self b hb)
  | add a b, h, e, hx => by
      obtain ⟨_, ha, hb, _⟩ := cn_add h
      have hi := inT_of_cn97 h
      rcases List.mem_append.mp (show e ∈ gsub97 a ++ gsub97 b from hx) with h1 | h1
      · exact lt_trans_inT (inT_of_cn97 (cn_gsub97 a ha e h1)) (inT_of_cn97 ha) hi
          (lt_gsub97 a ha e h1) (lt_left_add97 hi)
      · exact lt_trans_inT (inT_of_cn97 (cn_gsub97 b hb e h1)) (inT_of_cn97 hb) hi
          (lt_gsub97 b hb e h1) (lt_right_add97 hi)

/-- **`GB 0` は `gsub97` の像。** -/
theorem GB_invE97 : ∀ (s : Term), CN s = true → BT.GB 0 (invE97 s) = (gsub97 s).map invE97
  | zero, _ => rfl
  | M, h => Bool.noConfusion h
  | omg _, h => Bool.noConfusion h
  | psi _ _, h => Bool.noConfusion h
  | Z _, h => Bool.noConfusion h
  | phi a b, h => by
      obtain ⟨ha, hb⟩ := cn_phi h
      subst ha
      show invE97 b :: BT.GB 0 (invE97 b) = invE97 b :: (gsub97 b).map invE97
      rw [GB_invE97 b hb]
  | add a b, h => by
      obtain ⟨_, ha, hb, _⟩ := cn_add h
      show BT.GB 0 (invE97 a) ++ BT.GB 0 (invE97 b) = (gsub97 a ++ gsub97 b).map invE97
      rw [GB_invE97 a ha, GB_invE97 b hb, List.map_append]

/-! ### §97.5 CN の項はすべて正しい証人の像 -/

/-- **§97.5 の主定理。** `ε₀` より下の CN の項はどれも、段 1 以下・標準・成分が `D 0` の
    Buchholz 項の `dict` 像である。仮説は 326 行目がすでに抱えている 2 つだけ。 -/
theorem dictInv97 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) :
    ∀ (n : Nat) (s : Term), s.deg ≤ n → CN s = true →
      dict (invE97 s) = s ∧ btLe72 1 (invE97 s) = true ∧
      BT.isStd (invE97 s) = true ∧ Hd085 (invE97 s) := by
  intro n
  induction n with
  | zero => intro s hs _; exact absurd hs (by have := deg_pos s; omega)
  | succ k ih =>
    intro s hs hcn
    cases s with
    | M => exact Bool.noConfusion hcn
    | omg _ => exact Bool.noConfusion hcn
    | psi _ _ => exact Bool.noConfusion hcn
    | Z _ => exact Bool.noConfusion hcn
    | zero => exact ⟨rfl, rfl, rfl, fun x hx => by cases hx⟩
    | phi a b =>
        obtain ⟨ha, hb⟩ := cn_phi hcn
        subst ha
        have hdb : b.deg ≤ k := by
          rw [show (phi zero b).deg = 1 + (zero : Term).deg + b.deg from rfl] at hs
          have h1 : (zero : Term).deg = 1 := rfl
          omega
        obtain ⟨hd, hbl, hst, hhd⟩ := ih b hdb hb
        refine ⟨?_, ?_, ?_, ?_⟩
        · show collapse 0 (dict (invE97 b)) = phi zero b
          rw [hd, collapse0_cn97 hb]
        · show (decide (0 ≤ 1) && btLe72 1 (invE97 b)) = true
          rw [hbl]; rfl
        · show (BT.isStd (invE97 b) &&
              (BT.GB 0 (invE97 b)).all (fun e => BT.lt e (invE97 b))) = true
          rw [hst]
          show (BT.GB 0 (invE97 b)).all (fun e => BT.lt e (invE97 b)) = true
          rw [GB_invE97 b hb, List.all_eq_true]
          intro x hx
          obtain ⟨e, he, hxe⟩ := List.mem_map.mp hx
          have hce := cn_gsub97 b hb e he
          have hdege : e.deg ≤ k := by have := deg_gsub97 b e he; omega
          obtain ⟨hde, hble, hste, hhde⟩ := ih e hdege hce
          rw [← hxe]
          refine btlt_of_lt94 Hp H2 hble hste hhde hbl hst hhd ?_
          rw [hde, hd]
          exact lt_gsub97 b hb e he
        · intro x hx
          exact ⟨invE97 b, List.mem_singleton.mp hx⟩
    | add a b =>
        obtain ⟨hpow, ha, hb, hhdle⟩ := cn_add hcn
        have hia : inT (add a b) = true := inT_of_cn97 hcn
        have hdeg : (add a b).deg = 1 + a.deg + b.deg := rfl
        have hdega : a.deg ≤ k := by rw [hdeg] at hs; have := deg_pos b; omega
        have hdegb : b.deg ≤ k := by rw [hdeg] at hs; have := deg_pos a; omega
        obtain ⟨hda, hbla, hsta, hhda⟩ := ih a hdega ha
        obtain ⟨hdb, hblb, hstb, hhdb⟩ := ih b hdegb hb
        have hisPa : BT.isP (invE97 a) = true := by
          obtain ⟨e, he⟩ := eq_pow_of_isPow hpow
          rw [he]; rfl
        refine ⟨?_, ?_, ?_, ?_⟩
        · show plus (dict (invE97 a)) (dict (invE97 b)) = add a b
          rw [hda, hdb, plus_eq_add97 hia]
        · show (btLe72 1 (invE97 a) && btLe72 1 (invE97 b)) = true
          rw [hbla, hblb]; rfl
        · cases b with
          | M => exact Bool.noConfusion hb
          | omg _ => exact Bool.noConfusion hb
          | psi _ _ => exact Bool.noConfusion hb
          | Z _ => exact Bool.noConfusion hb
          | zero => exact Bool.noConfusion hhdle
          | phi c d =>
              obtain ⟨hc, _⟩ := cn_phi hb
              subst hc
              show (BT.isP (invE97 a) && BT.isStd (invE97 a) &&
                BT.isStd (BT.D 0 (invE97 d)) &&
                (BT.isP (BT.D 0 (invE97 d)) && BT.le (BT.D 0 (invE97 d)) (invE97 a))) = true
              rw [hisPa, hsta, show BT.isStd (BT.D 0 (invE97 d)) = true from hstb,
                show BT.isP (BT.D 0 (invE97 d)) = true from rfl]
              show BT.le (invE97 (phi zero d)) (invE97 a) = true
              refine btle_of_le94 Hp H2 hblb hstb hhdb hbla hsta hhda ?_
              rw [hdb, hda]
              exact hhdle
          | add c d =>
              obtain ⟨_, hc, _, _⟩ := cn_add hb
              have hdegc : c.deg ≤ k := by
                rw [show (add c d).deg = 1 + c.deg + d.deg from rfl] at hdegb
                have := deg_pos d; omega
              obtain ⟨hdc, hblc, hstc, hhdc⟩ := ih c hdegc hc
              show (BT.isP (invE97 a) && BT.isStd (invE97 a) &&
                BT.isStd (BT.sum (invE97 c) (invE97 d)) &&
                BT.le (invE97 c) (invE97 a)) = true
              rw [hisPa, hsta, show BT.isStd (BT.sum (invE97 c) (invE97 d)) = true from hstb]
              show BT.le (invE97 c) (invE97 a) = true
              refine btle_of_le94 Hp H2 hblc hstc hhdc hbla hsta hhda ?_
              rw [hdc, hda]
              exact hhdle
        · intro x hx
          rcases List.mem_append.mp
            (show x ∈ (invE97 a).toL ++ (invE97 b).toL from hx) with h1 | h1
          · exact hhda x h1
          · exact hhdb x h1

/-! ### §97.6 低い側の条項 -/

theorem cn_tower97 : ∀ n, CN (Evidence.WF.tower n) = true
  | 0 => rfl
  | n + 1 => by
      show (((zero : Term) == zero) && CN (Evidence.WF.tower n)) = true
      rw [cn_tower97 n]; rfl

/-- **`ε₀` より下の 𝔗(M) の項はすべて CN。** §9 の共終性 + §13 の下方閉性。 -/
theorem cn_of_ltE97 {s : Term} (hs : inT s = true) (h : lt s E081 = true) : CN s = true := by
  obtain ⟨n, hn⟩ := Evidence.WF.cof_eps0 s hs (show lt s Evidence.WF.eps0 = true from h)
  rcases (Bool.or_eq_true _ _).mp hn with h1 | h1
  · rw [eq_of_beq h1]; exact cn_tower97 n
  · exact cn_of_lt_cn hs (cn_tower97 n) h1

/-- 逆像はいつでも正しい証人。 -/
theorem dict_invE97 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) {s : Term} (hcn : CN s = true) :
    dict (invE97 s) = s ∧ btLe72 1 (invE97 s) = true ∧
    BT.isStd (invE97 s) = true ∧ Hd085 (invE97 s) :=
  dictInv97 Hp H2 s.deg s (Nat.le_refl _) hcn

/-- **§97 の主定理 — `DictDenseLo94` は定理である。**
    低い側は密度ではなく全射性で、証人は挑戦者そのものの逆像 `invE97 s`。
    仮説は 326 行目がすでに抱えている `PsiIdxOKStd172` と `DictLtA74` の 2 つだけ。 -/
theorem dictDenseLo97 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) : DictDenseLo94 := by
  intro t ht _ hv s hs hlt
  have hsE : lt s E081 = true := lt_trans_inT hs (inT_vOf94 Hp t ht) inT_E81 hlt hv
  obtain ⟨hd, hbl, hst, hhd⟩ := dict_invE97 Hp H2 (cn_of_ltE97 hs hsE)
  refine ⟨invE97 s, hbl, hst, hhd, ?_, ?_⟩
  · rw [hd]; exact Evidence.WF.le_self s
  · rw [hd]; exact hlt

/-- **残るのは `DictDenseHi94` ひとつ。** -/
theorem dictDense85_of97 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HH : DictDenseHi94) :
    DictDense85 :=
  dictDense85_of94 Hp (dictDenseLo97 Hp H2) HH

/-- **同じことを `DictOnto85` の形で。** §94.5 の同値を通す。 -/
theorem dictOnto85_of97 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HH : DictDenseHi94) :
    DictOnto85 :=
  dictOnto85_of_dictDense94 Hp H2 (dictDense85_of97 Hp H2 HH)

/-- **326 行目の証明書 — 共終性の側で待つのは `DictDenseHi94` だけ。** -/
theorem certIn_t326_97 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HH : DictDenseHi94)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_94 Hp H2 (dictDenseLo97 Hp H2) HH hacc

/-! ### §97.7 段は上がらない、そして四つの反証 -/

/-- **`invE97` は段 0 から出ない。** §85.6 が条項を反証するのは段 2 のところで、
    §97 の構成はそこへ一歩も届かない — 届かないことがこの定理である。 -/
theorem btLe0_invE97 : ∀ (s : Term), btLe72 0 (invE97 s) = true
  | zero => rfl
  | M => rfl
  | omg _ => rfl
  | psi _ _ => rfl
  | Z _ => rfl
  | add a b => by
      show (btLe72 0 (invE97 a) && btLe72 0 (invE97 b)) = true
      rw [btLe0_invE97 a, btLe0_invE97 b]; rfl
  | phi a b => by
      cases a with
      | zero =>
          show (decide (0 ≤ 0) && btLe72 0 (invE97 b)) = true
          rw [btLe0_invE97 b]; rfl
      | M => rfl
      | omg _ => rfl
      | psi _ _ => rfl
      | Z _ => rfl
      | phi _ _ => rfl
      | add _ _ => rfl

/-- **反証 1 — (1) は `inT` を要る。** `1 ⊕ ω` は形式和だが正規和は `ω`。 -/
theorem plus_eq_add_needs_inT97 : ¬ (∀ a b : Term, plus a b = add a b) := by
  intro h
  exact absurd (h TM.Term.one TM.Term.omega) (by decide)

/-- **反証 2 — (4) は CN を要る。飛ばしはちょうど `ε₀` で起きる。**
    `φ̄0ε₀ ≠ ω^ε₀`：`phiNF 0 ε₀ = ε₀` であって `φ̄0ε₀` ではない。 -/
theorem phiNF_zero_needs_cn97 : ¬ (∀ b : Term, inT b = true → phiNF zero b = phi zero b) := by
  intro h
  exact absurd (h E081 inT_E81) (by decide)

/-- **反証 3 — 全射性は `ε₀` より上へは伸びない。** `ω^(ε₀+1) = φ̄0ε₀` の逆像は `1`。 -/
theorem dictInv97_needs_ltE97 : ¬ (∀ s : Term, inT s = true → dict (invE97 s) = s) := by
  intro h
  exact absurd (h (phi zero E081) (by decide)) (by decide)

/-- 降順条件を破った和 — `1 ⊕ ω`。`ε₀` より下だが 𝔗(M) の項ではない。 -/
def bad97 : Term := add TM.Term.one TM.Term.omega

/-- **反証 4 — 全射性は `inT` を要る。** `1 ⊕ ω` は `ε₀` より下で、`invE97` の像は
    標準ですらなく、`dict` はそれを `ω` に潰す。 -/
theorem dictInv97_needs_inT97 : ¬ (∀ s : Term, lt s E081 = true →
    dict (invE97 s) = s ∧ BT.isStd (invE97 s) = true) := by
  intro h
  exact absurd (h bad97 (by decide)).2 (by decide)

/-! ### §97.8 §9 の junk 項を条項へ持ち上げる — `inT` を落とすと低い側は偽

§9 の `cof_eps0_needs_inT` は、形成条件を落とすと `ε₀` の共終性が**偽**になることを
`φ̄(0 ⊕ M, 0)` で示した。同じ項が密度条項でも同じ仕事をする。それは `ε₀` より下にいて、
しかも `dict` の像 (= `ε₀` の下では CN の項ぜんぶ、§97.5) を**すべて超える**。
だから証人は 1 つも取れない。 -/

/-- §9 の junk 項 — `φ̄(0 ⊕ M, 0)`。 -/
def junk97 : Term := phi (add zero M) zero

/-- **junk 項は CN の項をすべて超える。** -/
theorem le_junk_cn97 : ∀ (y : Term), CN y = true → le junk97 y = false
  | zero, _ => by decide
  | M, h => Bool.noConfusion h
  | omg _, h => Bool.noConfusion h
  | psi _ _, h => Bool.noConfusion h
  | Z _, h => Bool.noConfusion h
  | phi a c, h => by
      obtain ⟨ha, hc⟩ := cn_phi h
      subst ha
      show ((junk97 == phi zero c) || lt (phi (add zero M) zero) (phi zero c)) = false
      rw [show (junk97 == phi zero c) = false from by
            cases hh : (junk97 == phi zero c) with
            | false => rfl
            | true =>
                exact absurd (eq_of_beq hh)
                  (by intro hcc; injection hcc with h1 _; exact Term.noConfusion h1),
        lt_phi_phi (by intro hcc; injection hcc with h1 _; exact Term.noConfusion h1),
        if_neg (by intro hcc; exact Term.noConfusion hcc),
        if_neg (by rw [show lt (add zero M) zero = false from by decide]
                   intro hcc; exact Bool.noConfusion hcc)]
      exact le_junk_cn97 c hc
  | add u v, h => by
      obtain ⟨_, hu, _, _⟩ := cn_add h
      show ((junk97 == add u v) || lt junk97 (add u v)) = false
      rw [show (junk97 == add u v) = false from rfl,
        lt_atom_add (show isAtom junk97 = true from rfl) u v]
      exact le_junk_cn97 u hu

/-- **`inT` を落とすと低い側の条項は偽である。**  挑戦者の形成条件を消すと、
    目標を `ε₀` そのものまで緩めても証人は取れない。§9 の `cof_eps0_needs_inT` の
    密度版で、`DictDenseLo94` の `inT s` が飾りでないことの証明。 -/
theorem denseLo_needs_inT97 (Hp : PsiIdxOKStd172) :
    ¬ (∀ (s : Term), lt s E081 = true →
        ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
          lt (dict b) E081 = true ∧ le s (dict b) = true) := by
  intro h
  obtain ⟨b, hbl, hst, _, hE, hle⟩ := h junk97 (by decide)
  have hi := (inT_dict_of_std172 Hp b hbl hst).1
  rw [le_junk_cn97 (dict b) (cn_of_ltE97 hi hE)] at hle
  exact Bool.noConfusion hle

end

/-! ### §97.9 測定 (凍結)

**構成を先に書く。**  低い側の母集団を 1 つ新しく作り、§94.7 の母集団をそのまま再利用する。

    lowPop97   種 `[0, 1, ω, ε₀, φ̄(0 ⊕ M, 0)]` を `φ̄0·`・正規和 `plus`・**生の `⊕`**
               で 2 段育て、`· < ε₀` だけで濾す (`inT` では濾さない)。117 項、
               うち CN は 8、CN でないものが 109。
    §94.7 の側  `lowPop94` (207 項)・`chal94` (221 項)・`prs94` (2093 対) をそのまま使う。

生の `⊕` を入れるのは、`inT` を破る項を母集団に確実に混ぜるためである。仮説が母集団に
見えていない一斉合格は証拠にならない (§93 の教訓)。 -/

section
open Trans.Recal
open Trans.Dict (BT dict reg dictInv)
open TM TM.Term
open Evidence.WF

def lowSeed97 : List Term := [zero, TM.Term.one, TM.Term.omega, E081, junk97]
def lowGrow97 (p : List Term) : List Term :=
  (p ++ p.map (fun a => phi zero a)
     ++ p.flatMap (fun a => p.map (fun b => plus a b))
     ++ p.flatMap (fun a => p.map (fun b => add a b))).eraseDups
def lowP1_97 : List Term := (lowGrow97 lowSeed97).filter (fun s => lt s E081)
def lowPop97 : List Term := (lowGrow97 (everyT94 3 lowP1_97)).filter (fun s => lt s E081)

/-- §97.5 の結論そのもの — 像が正しい証人で、`dict` がもとに戻す。 -/
def okInv97 (s : Term) : Bool := bgood94 (invE97 s) && dict (invE97 s) == s

/-! 母集団。`inT` では濾していないので、形成条件を破る項が 109 入っている。 -/
#guard lowPop97.length == 117
#guard lowPop97.all fun s => lt s E081
#guard lowPop97.countP (fun s => CN s) == 8
#guard lowPop97.countP (fun s => !(CN s)) == 109

/-! **肯定 1 — 仮説は母集団に見えていて、結論はちょうどそこで成り立つ。** -/
#guard lowPop97.all fun s => okInv97 s == CN s

/-! **非退化 — `bgood94` の側だけでは判別しない。** 10 ≠ 8。判別するのは
    `dict (invE97 s) = s` の側である。 -/
#guard lowPop97.countP (fun s => bgood94 (invE97 s)) == 10

/-! **肯定 2 — `ε₀` の下では `inT` と `CN` は同じ条件 (§97.3)。** -/
#guard lowPop97.countP (fun s => inT s && !(CN s)) == 0
#guard lowPop97.countP (fun s => !(inT s) && CN s) == 0

/-! **肯定 3 — §94.7 の 207 項はまるごと仮説の中にいて、写像も同じ。** -/
#guard lowPop94.length == 207
#guard lowPop94.all CN
#guard lowPop94.all fun s => invE97 s == invE94 s

/-! **肯定 4 — §94.7 の 221 の挑戦者。** CN は 9、`ε₀` より下も 9 で、同じ 9。
    難しい挑戦者 74 のうち CN は 1 つもない — 難しいとは正しい逆像がないことで、
    §97.5 は CN の項すべてに逆像を作るから。 -/
#guard chal94.length == 221
#guard chal94.countP (fun s => CN s) == 9
#guard chal94.all fun s => CN s == lt s E081
#guard chal94.all fun s => okInv97 s == CN s
#guard chal94.countP (fun s => CN s && hardC94 s) == 0

/-! **肯定 5 — §94.7 が `DictDenseLo94` に振り分けた 12 対は、12 とも定理になった。** -/
#guard prs94.countP (fun p => lt p.1 E081) == 12
#guard prs94.countP (fun p => lt p.1 E081 && CN p.2) == 12

/-! **否定 (作った項)。** `φ̄(0 ⊕ M, 0)` は `ε₀` より下、塔をすべて超え、`inT` を破る。
    `invE97` はそれに `0` を返す — **正しい証人だが挑戦者の下にいる。**
    だから「像が正しい証人である」は §97.5 の効いている半分ではない。 -/
#guard lt junk97 E081
#guard inT junk97 == false
#guard CN junk97 == false
#guard (List.range 12).all fun n => le junk97 (Evidence.WF.tower n) == false
#guard bgood94 (invE97 junk97)
#guard le junk97 (dict (invE97 junk97)) == false
#guard okInv97 junk97 == false

/-! **否定 (作った項、標準性の側)。** `1 ⊕ ω` は `ε₀` より下の形式和だが降順ではない。
    `invE97` の像は標準ですらなく、`dict` はそれを `ω` に潰す。 -/
#guard lt bad97 E081
#guard inT bad97 == false
#guard BT.isStd (invE97 bad97) == false
#guard dict (invE97 bad97) == TM.Term.omega
#guard okInv97 bad97 == false

/-! **否定 (高い側)。** §94.6 の生の `φ̄` の塔はどの段も CN ではない。
    低い側はそこへ届かないし、届くとも言っていない。 -/
#guard (List.range 4).all fun n => CN (rawT94 n) == false

end

/-! ## §95 THE ACCUMULATOR NEVER FALLS, AND THE RESIDUE MOVES TO `aV = Ω₁`

§92 left item (2) — *at a firing step that is not the last, the `ψ₀`-argument's collapse index
`j` can exceed the index `i₀` the scan has already accumulated* — and named ONE concrete
missing arithmetic fact for it: the expansiveness of `φ`, `v ≤ φ(a, v ⊕ c)`, "true on all 192
corpus pairs, and NOT in this repo".  **§95 proves that fact**, in the form the fold actually
needs, and with it `accGeb92` — which §92 carried as a decidable side condition — becomes a
theorem.  §95 then spends two more decidable exemptions and finds that **§92's 13 remaining
obligations all go**; but the section does not stop there, because §84 also measured 0 and was
refuted by §86.  Reading the new clause, §95 BUILDS a family it cannot see, and the family is
not empty: **50 obligations survive, and every one of them sits at the first firing step of a
component whose base-`Ω₁` exponent is `Ω₁` EXACTLY, with the `K`-element on the `cV` side.**
**The gate is still open**, and it is now open in one shape only.

THE FIRST HALF IS ONE LINE OF `φ`.  The Veblen branch of the fold replaces the accumulator `v`
by `φ(aV, v ⊕ cV)`, and `phiNF` is **not** inflationary — `phiNFsucc` steps DOWN, which is the
whole point of [Rathjen, 1991] 2.6(vi).  But what it steps down is only the TRAILING `1`s:
`splitFin` writes `β = γ ⊕ m` and the branch that fires returns `φ̄(a, γ ⊕ (m-1))`.  The HEAD of
`β` survives every branch of `phiNF`, and the head of `v ⊕ cV` is `v` itself when `v` is
additively principal (and something above `v` otherwise).  2.3.4 — `γ ≤ β ⟹ γ < φ̄αβ` — then
puts the old accumulator strictly below the new one.  That is `le_psi_phiNF95`; along the fold
it is `accGe95_fold`; at the end it is

    **`accGeb95` : the accumulator never falls below the last `ψ_{Ω₁}` it emitted.
    No `lastFire92`, no measurement — a theorem.**

THE SECOND HALF IS THAT THE INDEX IS SMALLER THAN THE ARGUMENT.  §88 bounds the `K`-element by
`j = idxF88 0 (dict e)`; the fold builds `j` out of `dict e` by replacing each base-`Ω₁`
exponent `B` by `B ⊖ Ω₁`, so `j` can only shrink.  `LeIdxSelf95` says exactly that — `j ≤ x` —
and it mentions neither `dict`, nor `BT`, nor the gate: it is a statement about `idxF88` and
the order of `𝔗(M)` alone.  **It is NOT proved here** and is carried as a named hypothesis
(0 counterexamples on 466 terms, §95.4).  With it, the decidable exemption `freeSelf95` —
*`dict e` is below the index this step is building* — discharges the obligation outright,
because `y ≤ j ≤ dict e`.

WHAT IS PROVED, UNCONDITIONALLY.

  §95.1  **`φ` IS EXPANSIVE ALONG THE FOLD.**  `le_hd_ofList95`, `hd_splitFin95` (the head
         survives `splitFin` when it is not `1`), `le_hd_down95`, `le_psi_phiNF95`,
         `le_psi_hd_plus95`, `le_phiNF_plus95` and `phiExp95` — the last is §92's statement
         verbatim for `v = ψκβ`.  `AccGe95` / `accGe95_step` / `accGe95_fold` carry it along
         the fold, and `accGeb95` is the conclusion.  `lt_idxF_of_lt95` is §92.2's main
         theorem with the `accGeb92` side condition **gone**.

  §95.2  **THE RESIDUE, WITH THREE EXEMPTIONS.**  `monoClosed95` is `monoClosed92` minus the
         `accGeb92` conjunct (§95.1 made it free); `freeSelf95` is the new one; `zeroFree95`
         settles `y = 0` by 2.3.1 whenever the index is not `0` — and the index IS sometimes
         `0` (`Δ = 1`, `Δ ⊖ 1 = 0`), which is why the guard is there.  `IdxK95` is `IdxK92`
         with the three dropped, `gateStd87_of_idxK95` consumes it at ONE term,
         `idxStd95_of_step073` is the converse (so `IdxStd95` is still EXACTLY the gate), and
         `psiIdxStep073_of_idxStd95` / `certIn_t326_idx95` re-hang row 326 — now on
         `IdxStd95`, `DictLtStd92`, `HiMono89` and `LeIdxSelf95`.

  §95.3  **THE WITNESS, BUILT.**  `survA95 = ψ₁(ψ₁ψ₁0 ⊕ ψ₀ψ₁(ψ₁ψ₁0 ⊕ ψ₀0)) ⊕ ψ₁ψ₁ψ₁0 ⊕ ψ₁ψ₁0`
         (22 symbols) satisfies every hypothesis — `btLe72 1`, `BT.isStd (ψ₀ ·)`, `inT (dict ·)`,
         `dict · < M` — the gate holds on it (`stepOKb`), and it carries **one obligation that
         survives §92's clause AND §95's**.  It was built, not swept: the two moves are (i) a
         firing component whose exponent is `Ω₁` exactly, so `subAP Ω₁ aV = 0` and §90.3's
         exemption is inapplicable and the whole `K`-set sits on the `cV` side, and (ii) a
         Veblen tail `ψ₁ψ₁0`, which makes `lastFire92 (dict a)` FALSE and so shuts §92.2's
         road.  Neither move appears in §84/§86/§87/§88/§90/§92's populations, and the
         exhaustive enumeration of every standard sub-region term of at most 14 symbols does
         not reach it (the witness has 22).

WHAT IS **NOT** CLAIMED.  The gate is NOT closed.  `IdxStd95` is EQUIVALENT to
`PsiIdxStep073`, as `IdxStd92` and `IdxStd90` were.  `LeIdxSelf95` is **not proved** and §95
does not weaken it; neither are `HiMono89` and `DictLtStd92`.  Item (2) is NOT proved: §95
takes §92's measured residue to 0 and then shows, by building the witness, that the residue is
not empty — so what §95 delivers on item (2) is a **relocalisation**, not a closure.  §86's
wall stands: `freeSelf95` compares `dict e` against `i₀ ⊕ Δ`, not `y` against `i₀` alone or `Δ`
alone, so §95 is not a sixth single-summand clause; and it is not step-blind, since `freeSelf95`
names the step.  `IdxLtStd92`, `SplitK86`, `ArgStd87`, `LocalK2Snd_78`, `CofDenseS1`, `BCofIn71`
are untouched.

WHAT THE MEASUREMENT SAYS (§95.4 gives the construction).  §92's `corpus92` — all 233 terms,
both routings of `ψ₀` — reused verbatim, plus **11 qualifying terms of 25 built for §95**
(`famA95`, `famB95`, `famD95`, all around `argB95`, the low firing component).  244 terms.

  * **§92's residue goes to 0 on `corpus92`.**  163 obligations under §90's clause, 13 under
    §92's, **0 under §95's** — `freeSelf95` takes all 13 (the 3 at a first firing step and the
    10 at a middle one alike), `monoClosed95` takes 66, `freePrev92b` takes 84.
  * **And that is exactly why §95 built the family.**  On the 11 new terms: 50 obligations
    under §90's clause, **50 under §92's, 50 under §95's** — neither clause touches one of
    them.  Over all 244 terms the counts are **213 / 63 / 50**.
  * **The 50 have ONE shape.**  All 50 are at a FIRST firing step; all 50 have `aV = Ω₁`
    exactly; all 50 carry the element in `K_{Ω₁} cV` and **none** in `K_{Ω₁} aV`; and `lastFire92`
    is false at all 50.  That is `LocalK2Snd_78` — §78's `cV` side — restricted to the steps
    §90.3 cannot reach.  At those steps `Δ = cV` and the obligation reads `K_{Ω₁}(cV) < cV ⊖ 1`.
  * **The gate does not fail anywhere.**  `stepOKb`, `idxb84`, `splitb86`, `idxLt90b`,
    `ltArg90b` : 0 failures on all 244.  §95 is not a seventh refutation.
  * **The sweep could not have found the witness.**  Exhaustively, EVERY standard sub-region
    term of at most 12 symbols (5318 of them) gives 62 obligations, 1 under §92's clause and
    **0 under §95's**; carrying the same enumeration to 14 symbols (29338 qualifying terms)
    gives 748 obligations, 33 under §92's and still **0 under §95's** — measured, NOT frozen
    here, because that guard costs 100 s.  The witness has 22 symbols.
  * **`LeIdxSelf95` : 0 counterexamples on 466 distinct `𝔗(M)` terms**, and `accGeb92` — now a
    theorem — holds at all 238 terms of the population that have an index, as it must.
-/

/-! ### §95.1 φ の膨張性 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 頭部成分は組み立て直した和以下。 -/
theorem le_hd_ofList95 {b : Term} (hap : b.isAP = true) :
    ∀ (s : List Term), le b (ofList (b :: s)) = true
  | [] => Evidence.WF.le_self _
  | c :: t => le_of_lt (lt_head_add hap (ofList (c :: t)))

/-- `1 < ψκα` — 2.3.5。 -/
theorem lt_one_psi95 (k c : Term) : lt TM.Term.one (psi k c) = true :=
  lt_phi_psi_of (lt_zero_left (by intro hc; exact Term.noConfusion hc))
    (lt_zero_left (by intro hc; exact Term.noConfusion hc))

/-- `splitFin` の有限部は、頭部が `1` でないかぎり頭部を残す。 -/
theorem hd_splitFin95 {X x : Term} {s : List Term}
    (hl : toList X = x :: s) (hne : x ≠ TM.Term.one) :
    ∃ r, (splitFin X).1 = ofList (x :: r) ∧ ∀ q ∈ x :: r, q ∈ toList X := by
  have hF1 : ((toList X).reverse.dropWhile (fun q => q == TM.Term.one)).reverse
      ++ List.replicate (((toList X).reverse.takeWhile (fun q => q == TM.Term.one)).length)
          TM.Term.one = toList X := by
    have h := trailing_ones (toList X).reverse
    rwa [List.reverse_reverse] at h
  rw [splitFin_fst X]
  generalize hDr : ((toList X).reverse.dropWhile (fun q => q == TM.Term.one)).reverse = Dr
    at hF1 ⊢
  generalize hK : ((toList X).reverse.takeWhile (fun q => q == TM.Term.one)).length = K at hF1
  have hF2 : Dr ++ List.replicate K TM.Term.one = x :: s := by rw [hF1]; exact hl
  cases Dr with
  | nil =>
      exfalso
      rw [List.nil_append] at hF2
      cases K with
      | zero =>
          rw [show List.replicate 0 TM.Term.one = ([] : List Term) from rfl] at hF2
          exact List.cons_ne_nil x s hF2.symm
      | succ n =>
          rw [List.replicate_succ] at hF2
          injection hF2 with h1 _
          exact hne h1.symm
  | cons a r =>
      rw [List.cons_append] at hF2
      injection hF2 with hax _
      subst hax
      refine ⟨r, rfl, ?_⟩
      intro q hq
      rw [← hF1]
      exact List.mem_append_left _ hq

/-- `X` の頭部 `x` が `1` より上なら、`phiNFsucc` の下げた引数も `x` 以上。 -/
theorem le_hd_down95 {X x : Term} {s : List Term} (hX : inT X = true)
    (hl : toList X = x :: s) (h1x : lt TM.Term.one x = true) :
    le x (plus (splitFin X).1 (ofNat ((splitFin X).2 - 1))) = true := by
  have hne : x ≠ TM.Term.one := by
    intro hc; rw [hc, lt_irrefl] at h1x; exact Bool.noConfusion h1x
  have hap : x.isAP = true := inTL_isAP hX x (by rw [hl]; exact List.Mem.head _)
  obtain ⟨r, hg, hmem⟩ := hd_splitFin95 hl hne
  have hAPr : ∀ q ∈ x :: r, q.isAP = true := fun q hq => inTL_isAP hX q (hmem q hq)
  have htg : toList ((splitFin X).1) = x :: r := by rw [hg]; exact toList_ofList _ hAPr
  cases hn : (splitFin X).2 - 1 with
  | zero =>
      rw [show ofNat 0 = (zero : Term) from rfl, plus_nil rfl, hg]
      exact le_hd_ofList95 hap r
  | succ n =>
      have hto : toList (ofNat (n+1)) = TM.Term.one :: List.replicate n TM.Term.one := by
        rw [toList_ofNat]; rfl
      rw [plus_cons66 hto, htg,
        List.filter_cons_of_pos (show le TM.Term.one x = true from le_of_lt h1x)]
      exact le_hd_ofList95 hap _

/-- **§95.1 の核 — `φ` は頭部を落とさない。**  `ψκβ ≤ x` (`x` は `X` の頭部) なら
    `ψκβ ≤ φ(a, X)`。`phiNFsucc` が下げるのは末尾の `1` だけなので、頭部 `x` は
    どの枝にも残る。 -/
theorem le_psi_phiNF95 {k c a X x : Term} {s : List Term}
    (hfw : FragR (psi k c) = true) (hX : inT X = true)
    (hl : toList X = x :: s) (hwx : le (psi k c) x = true) :
    le (psi k c) (phiNF a X) = true := by
  have hix : inT x = true := inTL_inT hX x (by rw [hl]; exact List.Mem.head _)
  have h1x : lt TM.Term.one x = true :=
    lt_of_lt_of_le3 (show FragR TM.Term.one = true from rfl) hfw (inT_le_fragR x hix)
      (lt_one_psi95 k c) hwx
  have hwX : le (psi k c) X = true :=
    le_trans3 hfw (inT_le_fragR x hix) (inT_le_fragR X hX) hwx (le_hd_self_inT hX hl)
  have hXne : X ≠ zero := by
    intro hc; rw [hc] at hl; exact List.cons_ne_nil x s hl.symm
  have hdown : le (psi k c) (plus (splitFin X).1 (ofNat ((splitFin X).2 - 1))) = true :=
    le_trans3 hfw (inT_le_fragR x hix)
      (inT_le_fragR _ (inT_plus (inT_splitFin hX) (inT_ofNat _))) hwx
      (le_hd_down95 hX hl h1x)
  have hdef : le (psi k c) (phiNFdefault a X) = true := by
    unfold phiNFdefault
    split
    · rename_i h
      exact absurd (eq_of_beq ((Bool.and_eq_true _ _).mp h).1) hXne
    · exact le_of_lt (lt_psi_phi_of_le hwX)
  have hsucc : le (psi k c) (phiNFsucc a X) = true := by
    unfold phiNFsucc
    split
    rename_i heq
    rw [heq] at hdown
    split
    · split <;> (split <;> first | exact le_of_lt (lt_psi_phi_of_le hdown) | exact hdef)
    · exact hdef
  unfold phiNF
  split
  · exact hwX
  · split
    · split
      · exact hwX
      · exact hsucc
    · exact hsucc

/-- `v` が加法主要なら `v ⊕ c` の頭部は `v` かそれより上。 -/
theorem le_psi_hd_plus95 {k c v cc : Term} (hfw : FragR (psi k c) = true)
    (hv : inT v = true) (hap : v.isAP = true) (hcc : inT cc = true)
    (hwv : le (psi k c) v = true) :
    ∃ x s, toList (plus v cc) = x :: s ∧ le (psi k c) x = true := by
  have hvl : toList v = [v] := toList_isAP81 hap
  cases hY : toList cc with
  | nil => exact ⟨v, [], by rw [plus_nil hY]; exact hvl, hwv⟩
  | cons c1 r =>
      have hic1 : inT c1 = true := inTL_inT hcc c1 (by rw [hY]; exact List.Mem.head _)
      have hAPcc : ∀ q ∈ c1 :: r, q.isAP = true := by
        intro q hq; exact inTL_isAP hcc q (by rw [hY]; exact hq)
      rw [plus_cons66 hY, hvl]
      by_cases hle : le c1 v = true
      · refine ⟨v, c1 :: r, ?_, hwv⟩
        rw [List.filter_cons_of_pos hle,
          show (List.filter (fun a => le c1 a) ([] : List Term)) = [] from rfl]
        exact toList_ofList _ (by
          intro q hq
          rcases List.mem_cons.mp hq with h | h
          · rw [h]; exact hap
          · exact hAPcc q h)
      · have hlt : lt v c1 = true := lt_of_not_le_inT hic1 hv (bool_false hle)
        refine ⟨c1, r, ?_, ?_⟩
        · rw [List.filter_cons_of_neg hle,
            show (List.filter (fun a => le c1 a) ([] : List Term)) = [] from rfl,
            List.nil_append]
          exact toList_ofList _ hAPcc
        · exact le_trans3 hfw (inT_le_fragR v hv) (inT_le_fragR c1 hic1) hwv (le_of_lt hlt)

/-- **§95.1 の畳み込み不変量。** 累算器は加法主要で、指数が出ているならその
    `ψ_{Ω₁}` 以上である。 -/
def AccGe95 (s : Option Term × Option Term) : Prop :=
  (∀ v, s.2 = some v → v.isAP = true) ∧
  (∀ i, s.1 = some i → ∃ v, s.2 = some v ∧ le (psi (reg 1) i) v = true)

theorem accGe95_none : AccGe95 ((none : Option Term), (none : Option Term)) := by
  constructor
  · intro v h; cases h
  · intro i h; cases h

theorem accGe95_step {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (hidx : IdxInv92 s) (hg : AccGe95 s)
    (_h1 : inT ac.1 = true) (h3 : inT ac.2 = true) :
    AccGe95 (stepF (reg 1) (baseOf 0) s ac) := by
  cases hf : le (reg 1) ac.1 with
  | true =>
    constructor
    · intro v hv
      rw [stepF_snd_fire88 hf] at hv
      rw [← Option.some.inj hv]
      rfl
    · intro i hi
      rw [stepF_fst, if_pos hf] at hi
      refine ⟨psi (reg 1) (idxOf (reg 1) s ac), stepF_snd_fire88 hf, ?_⟩
      rw [← Option.some.inj hi]
      exact Evidence.WF.le_self _
  | false =>
    have hnf : ¬ (le (reg 1) ac.1 = true) := by rw [hf]; exact Bool.noConfusion
    constructor
    · intro w hw
      rw [stepF_snd_veb88 hf] at hw
      rw [← Option.some.inj hw]
      exact isAP_phiNF _ _
    · intro i hi
      have hs1 : s.1 = some i := by
        have : (stepF (reg 1) (baseOf 0) s ac).1 = s.1 := by
          rw [stepF_fst, if_neg hnf]
        rw [← this]; exact hi
      obtain ⟨v, hv2, hwv⟩ := hg.2 i hs1
      have hapv : v.isAP = true := hg.1 v hv2
      have hiv : inT v = true := (hst.2 v hv2).1
      have hii : inT i = true := hidx i hs1
      have hfw : FragR (psi (reg 1) i) = true := fragR_psi_reg92 (inT_le_fragR i hii)
      have h2 : (stepF (reg 1) (baseOf 0) s ac).2 = some (phiNF ac.1 (plus v ac.2)) := by
        rw [stepF_snd_veb88 hf, hv2]
      refine ⟨_, h2, ?_⟩
      obtain ⟨x, s', hxl, hwx⟩ := le_psi_hd_plus95 hfw hiv hapv h3 hwv
      exact le_psi_phiNF95 hfw (inT_plus hiv h3) hxl hwx

theorem accGe95_fold : ∀ (l : List (Term × Term)) (s : Option Term × Option Term),
    StInv s → IdxInv92 s → AccGe95 s →
      (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
      (∀ p ∈ scanSt (reg 1) (baseOf 0) s l, le (reg 1) p.2.1 = true →
          inT (psi (reg 1) (idxOf (reg 1) p.1 p.2)) = true) →
      AccGe95 (l.foldl (stepF (reg 1) (baseOf 0)) s) := by
  intro l
  induction l with
  | nil => intro s _ _ hg _ _; exact hg
  | cons ac t ih =>
    intro s hst hidx hg hall hpsi
    have hac := hall ac (List.Mem.head _)
    have h1 : StInv (stepF (reg 1) (baseOf 0) s ac) :=
      stepF_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0) hst hac
        (hpsi (s, ac) (List.Mem.head _))
    have h2 : IdxInv92 (stepF (reg 1) (baseOf 0) s ac) :=
      idxInv92_step (inT_reg 1) hidx hac.1 hac.2.2.1
    have h3 : AccGe95 (stepF (reg 1) (baseOf 0) s ac) :=
      accGe95_step hst hidx hg hac.1 hac.2.2.1
    exact ih _ h1 h2 h3 (fun a ha => hall a (List.Mem.tail _ ha))
      (fun p hp => hpsi p (List.Mem.tail _ hp))

/-- **§95.1 の主定理 — 累算器は最後に吐いた `ψ_{Ω₁}` を下回らない。**
    §92 が判定できる側条件として抱えていた `accGeb92` は**定理**である。
    中身は「ヴェブレン枝は末尾の `1` しか下げない」という一点で、
    §92 が名指しした `le v (phiNF a (plus v c))` の、必要な形そのもの。 -/
theorem accGeb95 {x : Term} (hx : inT x = true) (hlx : lt x M = true) (Hp : PsiIdxOK 0 x)
    {j : Term} (hj : idxF88 0 x = some j) : accGeb92 x = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨_, hallOK⟩ :=
    wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList x) hc hd (ltM_toList x hx hlx)
  have hg := accGe95_fold (wcnf (reg 1) (toList x)).1 (none, none) stInv_none idxInv92_none
    accGe95_none hallOK Hp
  obtain ⟨v, hv2, hwv⟩ := hg.2 j hj
  unfold accGeb92
  rw [hj]
  show le (psi (reg 1) j) (accW89 x) = true
  rw [show accW89 x = v from by unfold accW89; rw [hv2]; rfl]
  exact hwv

/-- **§92 が名指しした算術 — `φ` の膨張性**、必要な形で。§92 は「この repo に無い」と
    書いた。`v` が `ψ` の像であるかぎり、ここにある。 -/
theorem le_phiNF_plus95 {k c a v cc : Term} (hfw : FragR (psi k c) = true)
    (hv : inT v = true) (hap : v.isAP = true) (hcc : inT cc = true)
    (hwv : le (psi k c) v = true) :
    le (psi k c) (phiNF a (plus v cc)) = true := by
  obtain ⟨x, s', hxl, hwx⟩ := le_psi_hd_plus95 hfw hv hap hcc hwv
  exact le_psi_phiNF95 hfw (inT_plus hv hcc) hxl hwx

/-- `v ≤ φ(a, v ⊕ c)` — §92 が書いた形そのもの (`v = ψκβ`)。 -/
theorem phiExp95 {k c a cc : Term} (hv : inT (psi k c) = true) (hcc : inT cc = true) :
    le (psi k c) (phiNF a (plus (psi k c) cc)) = true :=
  le_phiNF_plus95 (inT_le_fragR _ hv) hv rfl hcc (Evidence.WF.le_self _)

end

/-! ### §95.2 残余 — 三つの免除と、残る算術 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§92.2 の主定理から `accGeb92` を落とした形。**  §95.1 でそれは定理になった。 -/
theorem lt_idxF_of_lt95 (HD : DictLtStd92) (HM : HiMono89)
    {e a : BT} (hbe : btLe72 1 e = true) (hba : btLe72 1 a = true)
    (hse : BT.isStd (BT.D 0 e) = true) (hsa : BT.isStd (BT.D 0 a) = true)
    (hlt : BT.lt e a = true)
    (hie : inT (dict e) = true) (hlie : lt (dict e) M = true)
    (hia : inT (dict a) = true) (hlia : lt (dict a) M = true)
    (Hpe : PsiIdxOK 0 (dict e))
    (hfa : lastFire92 (dict a) = true)
    (hne : hiW89 (dict e) ≠ hiW89 (dict a))
    {j J : Term} (hj : idxF88 0 (dict e) = some j) (hJ : idxF88 0 (dict a) = some J) :
    lt j J = true :=
  lt_idxF_of_lt92 HD HM hbe hba hse hsa hlt hie hlie hia hlia Hpe
    (accGeb95 hie hlie Hpe hj) hfa hne hj hJ

/-- §92.2 の道が通る歩 — `accGeb92` の連言は §95.1 が消した。 -/
def monoClosed95 (a : BT) (p : (Option Term × Option Term) × (Term × Term)) (e : BT) : Bool :=
  isLastIdx92 a p && lastFire92 (dict a) && !(hiW89 (dict e) == hiW89 (dict a))

/-- **`e` の像がこの歩の指数より下** — 判定できる。`LeIdxSelf95` があれば
    `y ≤ j ≤ dict e` で義務が消える。 -/
def freeSelf95 (p : (Option Term × Option Term) × (Term × Term)) (e : BT) : Bool :=
  lt (dict e) (idxOf (reg 1) p.1 p.2)

/-- `y = 0` は指数が `0` でなければ只 — 2.3.1。 -/
def zeroFree95 (p : (Option Term × Option Term) × (Term × Term)) (y : Term) : Bool :=
  (y == zero) && !(idxOf (reg 1) p.1 p.2 == zero)

/-- **§95 の残る算術。証明しない。**  崩壊指数は引数を超えない。
    `dict` も `BT` も門も出てこない — `idxF88` と `𝔗(M)` の順序だけの主張である。
    測定: 567 項で反例 0 (§95.4)。 -/
def LeIdxSelf95 : Prop :=
  ∀ x : Term, inT x = true → lt x M = true → PsiIdxOK 0 x →
    ∀ j, idxF88 0 x = some j → le j x = true

/-- **§95 の条項。** §92 の `IdxK92` から、
    (i) `accGeb92` の連言 (§95.1 が定理にした)、
    (ii) `freeSelf95` が真の歩 (`LeIdxSelf95` が片づける)、
    (iii) `y = 0` の場合 (2.3.1 が片づける)
    を義務から外した形。外したものはどれも定理か、名指しした算術ひとつだから、
    門との同値は保たれる (`idxStd95_of_step073` が逆向き)。 -/
def IdxK95 (a : BT) : Prop :=
  ∀ p ∈ scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1,
    le (reg 1) p.2.1 = true → inT (idxOf (reg 1) p.1 p.2) = true →
      ∀ (y : Term) (c e : BT) (j : Term),
        BT.D 1 c ∈ BT.toL a → BT.isStd (BT.D 1 c) = true → BT.lt c a = true →
        e ∈ d0Args88 c → BT.isStd (BT.D 0 e) = true → btLe72 1 e = true →
        BT.lt e a = true → BT.size e < BT.size a →
        idxF88 0 (dict e) = some j → inT j = true → inT (psi (reg 1) j) = true →
        le y j = true → inT y = true → y ∈ Kset (reg 1) (dict c) →
        (lt y (reg 1) = false ∨ subAP (reg 1) p.2.1 = zero) →
        (∀ i0, p.1.1 = some i0 → lt i0 y = true) →
        monoClosed95 a p e = false → freeSelf95 p e = false → zeroFree95 p y = false →
        (y ∈ Kset (reg 1) p.2.1 ∨ y ∈ Kset (reg 1) p.2.2) →
        lt y (idxOf (reg 1) p.1 p.2) = true

/-- §92 の条項は §95 の条項を出す — 仮説が増えただけだから。 -/
theorem idxK95_of_idxK92 {a : BT} (H : IdxK92 a) : IdxK95 a := by
  intro p hp hle hidxT y c e j hc hstd hltc he hse hbe hlte hsz hj hjT hpsiT hlej hyT hyk hfr
    hgt hmono _ _ hy
  refine H p hp hle hidxT y c e j hc hstd hltc he hse hbe hlte hsz hj hjT hpsiT hlej hyT hyk hfr
    hgt ?_ hy
  cases hm : monoClosed92 a p e with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hm
    obtain ⟨h3, _⟩ := (Bool.and_eq_true _ _).mp h1
    obtain ⟨h5, h6⟩ := (Bool.and_eq_true _ _).mp h3
    rw [show monoClosed95 a p e = true from by
      show (isLastIdx92 a p && lastFire92 (dict a) && !(hiW89 (dict e) == hiW89 (dict a))) = true
      rw [h5, h6, h2]; rfl] at hmono
    exact Bool.noConfusion hmono

/-- **§95 の残る仮説。** 部分領域の項について §95 の条項。**証明しない。** -/
def IdxStd95 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → IdxK95 a

/-- **§95.2 の主定理。** 一項ぶんの門は §95 の条項と、326 行目が既に抱えている
    二つの条項と、§95 が名指しした算術ひとつから出る。 -/
theorem gateStd87_of_idxK95 (HD : DictLtStd92) (HM : HiMono89) (HL : LeIdxSelf95) (a : BT)
    (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b)
    (H : btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → IdxK95 a) : GateStd87 a := by
  intro hb hs
  have hin := inT_dict_ih87 a ih hb (isStd_of_D hs)
  obtain ⟨hcL, hdL⟩ := inT_toList (dict a) hin.1
  obtain ⟨_, hallOK⟩ :=
    wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList (dict a)) hcL hdL
      (ltM_toList (dict a) hin.1 hin.2)
  have hnz := wcnf_snd_ne_zero84 (inT_reg 1) (isSC_reg_succ 0) (toList (dict a)) hcL hdL
    (ltM_toList (dict a) hin.1 hin.2)
  intro p hp hle
  refine scan_idx84 (wcnf (reg 1) (toList (dict a))).1 (none, none)
    stInv_none (kInv75_none 0) hallOK ?_ p hp hle
  intro q hq hle2 hst y hy
  obtain ⟨hi1, hl1, hi2, hl2⟩ := hallOK q.2 (scanSt_mem_snd _ _ _ _ q hq)
  obtain ⟨hidxT, _⟩ := inT_idxOf mulDescInT (inT_reg 1) (ltM_reg 1) hst hi1 hl1 hi2 hl2
  have hnz2 : q.2.2 ≠ zero := hnz q.2 (scanSt_mem_snd _ _ _ _ q hq)
  obtain ⟨c, hc, hstd, hltc, hyk⟩ := kset_arg87 ih hb hs hq hy
  have hszc0 : BT.size (BT.D 1 c) ≤ BT.size a := size_mem_toL87 a _ hc
  have hszc : BT.size c < BT.size a := by rw [size_D87] at hszc0; omega
  have hbc : btLe72 1 c = true := (btLe72_D 1 1 c (btLe72_toL87 a _ hb hc)).2
  have hsc : BT.isStd c = true := isStd_of_D hstd
  have ihc : ∀ b : BT, BT.size b < BT.size c → GateStd87 b := fun b hz => ih b (by omega)
  have hinc := inT_dict_ih87 c ihc hbc hsc
  have hyT : inT y = true := inT_mem_Kset75 (dict c) hinc.1 _ y hyk
  obtain ⟨e, he, j, hj, hlej, hjT⟩ := kset_dict_idx88 c ihc hbc hsc y hyk
  have hse : BT.isStd (BT.D 0 e) = true := isStd_d0Args_90 c hsc e he
  have hbe : btLe72 1 e = true := btLe72_d0Args_90 c hbc e he
  have hlte : BT.lt e a = true := lt_d0Args_90 hs hc he
  have hsze : BT.size e < BT.size a := by have := size_d0Args_90 c e he; omega
  have ihe : ∀ b : BT, BT.size b < BT.size e → GateStd87 b := fun b hz => ih b (by omega)
  have hine := inT_dict_ih87 e ihe hbe (isStd_of_D hse)
  have hpe : PsiIdxOK 0 (dict e) :=
    psiIdxOK_of_stepOK 0 (dict e) hine.1 hine.2 (ih e hsze hbe hse)
  have hpsiT : inT (psi (reg 1) j) = true := inT_psi_idxF90 hpe hj
  have hfin : (∀ i1, q.1.1 = some i1 → lt i1 y = true) →
      lt y (idxOf (reg 1) q.1 q.2) = true := by
    intro hgt
    cases hz : zeroFree95 q y with
    | true =>
      obtain ⟨hy0, hidxnz⟩ := (Bool.and_eq_true _ _).mp hz
      rw [eq_of_beq hy0]
      refine lt_zero_left ?_
      intro hcc
      rw [hcc, beq_self_eq_true] at hidxnz
      exact Bool.noConfusion hidxnz
    | false =>
    cases hsf : freeSelf95 q e with
    | true =>
      have hjle : le j (dict e) = true := HL (dict e) hine.1 hine.2 hpe j hj
      have hyle : le y (dict e) = true :=
        le_trans3 (inT_le_fragR _ hyT) (inT_le_fragR _ hjT) (inT_le_fragR _ hine.1) hlej hjle
      exact lt_of_le_of_lt3 (inT_le_fragR _ hyT) (inT_le_fragR _ hine.1)
        (inT_le_fragR _ hidxT) hyle hsf
    | false =>
    cases hmono : monoClosed95 a q e with
    | true =>
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hmono
      obtain ⟨h5, h6⟩ := (Bool.and_eq_true _ _).mp h1
      obtain ⟨J, hJ, hidxe⟩ := isLastIdx92_eq h5
      have hne : hiW89 (dict e) ≠ hiW89 (dict a) := by
        intro hcc
        rw [show (hiW89 (dict e) == hiW89 (dict a)) = true from by
          rw [hcc]; exact beq_self_eq_true _] at h2
        exact Bool.noConfusion h2
      have hlj : lt j J = true :=
        lt_idxF_of_lt95 HD HM hbe hb hse hs hlte hine.1 hine.2 hin.1 hin.2 hpe h6 hne hj hJ
      refine lt_of_le_of_lt3 (inT_le_fragR _ hyT) (inT_le_fragR _ hjT)
        (inT_le_fragR _ hidxT) hlej ?_
      rw [hidxe]
      exact hlj
    | false =>
      cases hlty : lt y (reg 1) with
      | false =>
        exact H hb hs q hq hle2 hidxT y c e j hc hstd hltc he hse hbe hlte hsze
          hj hjT hpsiT hlej hyT hyk (Or.inl hlty) hgt hmono hsf hz hy
      | true =>
        by_cases hsub : subAP (reg 1) q.2.1 = zero
        · exact H hb hs q hq hle2 hidxT y c e j hc hstd hltc he hse hbe hlte hsze
            hj hjT hpsiT hlej hyT hyk (Or.inr hsub) hgt hmono hsf hz hy
        · exact lt_idxOf_of_lt_reg90 hst hi1 hi2 hnz2 hsub hyT hlty hidxT
  cases hq1 : q.1.1 with
  | none =>
    refine hfin ?_
    intro i1 h1
    rw [hq1] at h1
    cases h1
  | some i0 =>
    cases hbb : le y i0 with
    | true =>
      exact lt_idxOf_of_le_prev92 (inT_reg 1) hst hq1 hi1 hi2 hnz2 hyT hidxT hbb
    | false =>
      refine hfin ?_
      intro i1 h1
      rw [hq1] at h1
      rw [← Option.some.inj h1]
      exact lt_of_not_le_inT hyT (hst.1 i0 hq1).1 hbb

/-- **§95 の第一の結論。** -/
theorem psiIdxStep073_of_idxStd95 (HD : DictLtStd92) (HM : HiMono89) (HL : LeIdxSelf95)
    (H : IdxStd95) : PsiIdxStep073 :=
  step073_of_gate87 (fun a ih => gateStd87_of_idxK95 HD HM HL a ih (fun hb hs => H a hb hs))

/-- **逆向き。** 足した仮説も外した義務もすべて落ちるので、分解は過不足がない。 -/
theorem idxStd95_of_step073 (H : PsiIdxStep073) : IdxStd95 := by
  intro a hb hs p hp hle
  intro _ y _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hy
  exact (H a hb hs p hp hle).2 y hy

/-- **§95 の第二の結論。** 326 行目の証明書が `K` の側で待つのは §95 の条項ひとつと、
    §74/§89 が既に名指ししている二つと、§95 が名指しした算術ひとつである。 -/
theorem certIn_t326_idx95 (HD : DictLtStd92) (HM : HiMono89) (HL : LeIdxSelf95)
    (H : IdxStd95) (HDe : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_step73 (psiIdxStep073_of_idxStd95 HD HM HL H) HDe HI HC hacc

end

/-! ### §95.3 証人 — 組み立てた、掃いて出ない義務 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 指数が `Ω₁` ちょうどになる低い発火成分の入れ子引数。 -/
def argB95 : Nat → BT
  | 0 => BT.zero
  | k+1 => BT.D 1 (BT.sum (BT.D 1 (BT.D 1 BT.zero)) (BT.D 0 (argB95 k)))

/-- ヴェブレンの尾 — 底 `Ω₁` の分解の最後の対を発火させない。`lastFire92` が偽になる。 -/
def vebTail95 : BT := BT.D 1 (BT.D 1 BT.zero)

/-- **§95.3 の証人。** 22 記号。§92 の条項にも §95 の条項にも義務が残る。 -/
def survA95 : BT := BT.sum (argB95 2) (BT.sum (twr86 3) vebTail95)

/-- **指数は本当に `0` になりうる。**  `Δ = 1` なら `Δ ⊖ 1 = 0`。11 記号、仮説は全部真。
    だから `zeroFree95` の側条件 `idxOf ≠ 0` は飾りではない — そこでは `K` の集合が
    空なので門は落ちないが、`y = 0` を無条件に只とはできない。 -/
def z0A95 : BT := BT.sum (twr86 3) (BT.D 1 (BT.D 0 (twr86 3)))

theorem z0A95_facts :
    okHyp84 z0A95 = true ∧
    ((fireSt90 z0A95).all fun p => idxOf (reg 1) p.1 p.2 == zero) = true ∧
    ((fireSt90 z0A95).all fun p =>
      (Kset (reg 1) p.2.1 ++ Kset (reg 1) p.2.2).isEmpty) = true :=
  ⟨by decide, by decide, by decide⟩

/-- 証人は母集団の仮説をすべて満たし、門はそこで落ちない。 -/
theorem surv95_hyps :
    btLe72 1 survA95 = true ∧ BT.isStd (BT.D 0 survA95) = true ∧
    inT (dict survA95) = true ∧ lt (dict survA95) M = true ∧
    stepOKb 0 (dict survA95) = true ∧ idxb84 0 (dict survA95) = true ∧
    splitb86 0 (dict survA95) = true ∧ idxLt90b survA95 = true :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **証人が閉じている道を塞ぐ二つの手。**  発火成分の指数は `Ω₁` ちょうど
    (`subAP Ω₁ aV = 0`、だから §90.3 の免除が効かない) で、分解の最後の対は
    発火しない (`lastFire92` が偽、だから §92.2 の道が通らない)。 -/
theorem surv95_shape :
    lastFire92 (dict survA95) = false ∧ (fireSt90 survA95).length = 1 ∧
    ((fireSt90 survA95).all fun p => p.2.1 == reg 1) = true ∧
    ((fireSt90 survA95).all fun p => p.1.1 == none) = true :=
  ⟨by decide, by decide, by decide, by decide⟩

end

/-! ### §95.4 測定 (凍結) -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- §95 の条項が訊く組 — §92.1・§92.2 と §95 の三つの免除を引いたもの。 -/
def oblPost95 (a : BT) :
    List (((Option Term × Option Term) × (Term × Term)) × Term × BT × Term) :=
  (oblPre92 a).filter fun w =>
    !(freePrev92b w.1 w.2.1) && !(monoClosed95 a w.1 w.2.2.1) && !(freeSelf95 w.1 w.2.2.1)
      && !(zeroFree95 w.1 w.2.1)

def famA95 : List BT :=
  (List.range 4).flatMap fun k => (List.range 3).map fun n =>
    BT.sum (argB95 (k+2)) (BT.sum (twr86 (n+3)) vebTail95)
def famB95 : List BT := (List.range 4).map fun k => BT.sum (argB95 (k+2)) vebTail95
def famD95 : List BT :=
  (List.range 3).flatMap fun k => (List.range 3).map fun n =>
    BT.sum (argB95 (k+2)) (BT.sum (twr86 (n+3)) (BT.sum (twr86 (n+2)) vebTail95))

def pop95 : List BT := (famA95 ++ famB95 ++ famD95).eraseDups
def qual95 : List BT := pop95.filter okHyp84

/-- 測る母集団ぜんぶ — §92 の 233 項に §95 の 11 項を足したもの。 -/
def corpus95 : List BT := corpus92 ++ qual95

/-- 添字 0,1 の `BT` 項を大きさ順に全部並べる (層ごと)。 -/
def layers95 : Nat → List (List BT)
  | 0 => []
  | 1 => [[BT.zero]]
  | n+1 =>
    let prev := layers95 n
    let get : Nat → List BT := fun i => (prev.drop (i-1)).headD []
    let dpart := (get n).flatMap (fun a => [BT.D 0 a, BT.D 1 a])
    let spart := (List.range n).flatMap fun i =>
      if i = 0 then [] else (get i).flatMap fun a => (get (n - i)).map fun b => BT.sum a b
    prev ++ [dpart ++ spart]

/-- 大きさ `n` までの、仮説を満たす項ぜんぶ。 -/
def ex95 (n : Nat) : List BT := ((layers95 n).flatten).filter okHyp84

-- 母集団の大きさと形。
#guard (pop95.length, qual95.length, corpus95.length,
        (famA95.filter okHyp84).length, (famB95.filter okHyp84).length,
        (famD95.filter okHyp84).length) == (25, 11, 244, 4, 4, 3)
#guard ((pop95.map BT.size).foldl min 999, (qual95.map BT.size).foldl max 0,
        BT.size survA95) == (17, 40, 22)
#guard (qual95.contains survA95, okHyp84 survA95) == (true, true)

/-! **肯定 — §92 の残余は `corpus92` で 0 になる。** 163 の義務のうち 84 は §92.1、
66 は §92.2、13 は §95 の `freeSelf95` が持っていく。 -/

#guard ((corpus92.flatMap oblPre92).length, (corpus92.flatMap oblPost92).length,
        (corpus92.flatMap oblPost95).length) == (163, 13, 0)
#guard
  (let o := corpus92.flatMap fun a => (oblPre92 a).map fun w => (a, w)
   (o.length,
    (o.countP fun w => freePrev92b w.2.1 w.2.2.1),
    (o.countP fun w => !(freePrev92b w.2.1 w.2.2.1) && monoClosed95 w.1 w.2.1 w.2.2.2.1),
    (o.countP fun w => !(freePrev92b w.2.1 w.2.2.1) && !(monoClosed95 w.1 w.2.1 w.2.2.2.1)
        && freeSelf95 w.2.1 w.2.2.2.1))) == (163, 84, 66, 13)

/-! **否定 — 組み立てた族は §92 の条項も §95 の条項も抜ける。** 11 項で 50 の義務、
どちらの条項も一つも落とせない。 -/

#guard ((qual95.flatMap oblPre92).length, (qual95.flatMap oblPost92).length,
        (qual95.flatMap oblPost95).length) == (50, 50, 50)
#guard ((corpus95.flatMap oblPre92).length, (corpus95.flatMap oblPost92).length,
        (corpus95.flatMap oblPost95).length) == (213, 63, 50)

/-! **残る 50 の形は一つ。** すべて最初の発火歩、すべて `aV = Ω₁` ちょうど、
すべて `cV` の側 (`aV` の側は 0)、そして `lastFire92` はすべて偽。 -/

#guard
  (let o := corpus95.flatMap fun a => (oblPost95 a).map fun w => (a, w)
   (o.length,
    (o.countP fun w => w.2.1.1.1 == none),
    (o.countP fun w => w.2.1.2.1 == reg 1),
    (o.countP fun w => (Kset (reg 1) w.2.1.2.2).contains w.2.2.1),
    (o.countP fun w => (Kset (reg 1) w.2.1.2.1).contains w.2.2.1),
    (o.countP fun w => lastFire92 (dict w.1)))) == (50, 50, 50, 50, 0, 0)

/-! **門はどこでも落ちない。** §95 は七つ目の反証を出していない。 -/

#guard ((corpus95.filter fun a => !(stepOKb 0 (dict a))).length,
        (corpus95.filter fun a => !(idxb84 0 (dict a))).length,
        (corpus95.filter fun a => !(splitb86 0 (dict a))).length,
        (corpus95.filter fun a => !(idxLt90b a)).length,
        (corpus95.filter fun a => !(ltArg90b a)).length) == (0, 0, 0, 0, 0)

/-! **掃いても出ない。** 大きさ 12 以下の標準な部分領域の項を**ぜんぶ** (5318 項) 並べても、
62 の義務のうち §92 の条項に残るのは 1、§95 の条項に残るのは 0。証人は 22 記号である。 -/

#guard ((ex95 12).length, ((ex95 12).flatMap oblPre92).length,
        ((ex95 12).flatMap oblPost92).length,
        ((ex95 12).flatMap oblPost95).length) == (5318, 62, 1, 0)

/-! **§95 の証人はただ一つの義務を残す。** -/

#guard (BT.size z0A95, (fireSt90 z0A95).length) == (11, 1)
#guard ((oblPre92 survA95).length, (oblPost92 survA95).length,
        (oblPost95 survA95).length) == (1, 1, 1)
#guard ((oblPre92 survA95).map fun w =>
          (w.1.2.1 == reg 1, w.2.1 == TM.Term.omega, w.2.2.2 == TM.Term.omega,
           (Kset (reg 1) w.1.2.2).contains w.2.1,
           lt w.2.1 (idxOf (reg 1) w.1.1 w.1.2)))
       == [(true, true, true, true, true)]

/-! **`LeIdxSelf95` の測定。** 母集団の像とその `ψ₀` 引数の像、成分の像 — 466 項で反例 0。 -/

#guard
  (let xs := ((corpus95.map dict) ++ (corpus95.flatMap fun a => (d0ArgsAll92 a).map dict)
                ++ (corpus95.flatMap fun a => (BT.toL a).map dict)).eraseDups
   (xs.length, (xs.countP fun x => match idxF88 0 x with
                                    | none => false | some j => !(le j x)))) == (466, 0)

/-! **`accGeb92` は定理になった (§95.1)。** 測定はその確認 — 指数を持つ 238 項で失敗 0。 -/

#guard
  (let xs := ((corpus95.map dict)
                ++ (corpus95.flatMap fun a => (d0ArgsAll92 a).map dict)).eraseDups
   ((xs.countP fun x => (idxF88 0 x).isSome),
    (xs.countP fun x => (idxF88 0 x).isSome && !(accGeb92 x)))) == (238, 0)

end

/-! ## §99 THE VEBLEN GATE IS `HiMono89` AND NOTHING ELSE — THE TAIL CLAUSE IS FREE

§93 proved that the split is exact — `CollapseMono0Hi81 ↔ HiMono89 ∧ LoDomPair91` — and
§96 named the one thing standing between §93.6 and a running induction:

> along Gate(a,b) → Order(c,a) → Gate(x,y) the FIRST component runs `a ↦ c ↦ x` with
> `size x < size c < size a`: measured by `size a` alone, every gate instance §93.6 reaches
> is strictly smaller — **except the ones that come through the bridge at `b`**.

**§99 removes the bridge at `b` from §93.6's proof, and the induction runs.**  The second
factor of §93's split is not a gate:

        `LoDomPair91`  is a THEOREM of  `HiMono89`        (`loDomPair91_of_hiMono99`)
        `CollapseMono0Hi81`  ↔  `HiMono89`                (`gate_iff_hiMono99`)

Everything §96 isolated as debt — the bridge (`HiBridge93`, `FullBridge96`), the
one-component clauses (`DictLeAtom96`, `CollapseLe0_96`), and the injectivity
(`DictAtomInj96`) — comes out of `HiMono89` as well.  **Row 326's Veblen fold is one
clause about tail-free arguments, and its three gates are `PsiIdxOKStd172`, `HiMono89`,
`DictDenseHi94`.**

WHAT IS PROVED.

  §99.1  **TWO 𝔗(M)-SIDE FACTS ABOUT `hi`.**  `ltM_hiW99` (`x < M ⟹ hi x < M`, through
         `ltM_ofList99`) and `psiIdxOK_hiW99` (`PsiIdxOK 0 x ⟹ PsiIdxOK 0 (hi x)`, one
         rewrite by §89.2's `wcnf_split89`: the pair list of the base-`Ω₁` CNF is decided by
         the part at or above `Ω₁`, so the two clauses are literally the same clause).
         **These two are the whole price of dropping the bridge at `b`** — they let the
         residual be applied to `hi (dict b)` as a 𝔗(M) TERM instead of to `dict (hi b)`.

  §99.2  **(A) THE PRICE OF `CollapseLe0_96`, EXACTLY.**  `mono79_iff99` :
         `CollapseMono0_79 ↔ CollapseLe0_96 ∧ CollapseInj0_99`.  The non-strict clause IS
         weaker, and the missing part is exactly the injectivity of `collapse 0 ∘ dict` —
         not any part of the Veblen fold.  `collapseLe0_of79` is the easy direction (the
         diagonal is free); §99.6 shows the difference is populated.  This is §96.3's
         `dictLtAtom96_iff` one floor down.

  §99.3  **THE ORDER CHAIN, INDEXED ON BOTH SIDES.**  §96's `DictHeadLtUpTo96` is indexed by
         the SUM of the two symbol counts, and that index cannot express "the gate is only
         ever needed at the argument of a head component".  `DictLtBoth99 n` bounds BOTH
         lists by `n` and `GateFst99 n` bounds only the FIRST argument of the gate;
         `dictLtBoth99_step` and `dictLtBoth99_all` then give: **the order at terms of
         symbol count `≤ n` needs the gate only at first arguments of symbol count `< n`.**
         `bridge99` is §96.1's bridge on the same index.

  §99.4  **THE MAIN INDUCTION.**  `loDomPairFst99_all` : `HiMono89 ⟹ LoDomPair91`, by strong
         induction on `size a` alone.  §93.6 sent the tail component `ψ₀c` of `a` to the
         residual at the pair `(c, hi b)`, which needs `hi (dict b) = dict (hi b)` — the
         bridge at `b`, hence gate instances up to `size b`, unbounded by `size a`.  §99
         never forms `hi b`.  It keeps `Y = hi (dict b)` as a 𝔗(M) term (legal by §99.1) and
         applies §91.2's `lt_collapse0_diffHi91` to the pair `(dict c, Y)`; its two side
         conditions are `HiMono89` at `(c, b)` — an instance of the hypothesis — and **this
         theorem's own instance at `(c, b)`**, where `size c < size a` by §93.1's
         `size_GB93`.  The order instance it still needs is `lt (dict c) (dict a)`, at two
         terms both of symbol count `≤ size a`, which is exactly what §99.3 supplies.

  §99.5  **THE ASSEMBLY.**  `collapseMono0Hi_of_hiMono99`, `gate_iff_hiMono99`,
         `gates_iff99`.  Then `hiBridge99`, `fullBridge99`, `dictDesc99`, `dictLe99`,
         `dictLeAtom96_99`, `collapseLe0_99`, `collapseMono0_99`, `collapseInj0_99`,
         `dictLtAtom99`, **`dictAtomInj99` (B)** and `dictLtA74_99` — every clause §96 left
         open, from `HiMono89`.  Row 326: `certIn_t326_99` (with §97's density half) and
         `certIn_t326_pair99`.

  §99.6  **THE NEGATIVES, BUILT.**  `injBad99 = ψ₀Ω₁` against `Ω₁` satisfies EVERY
         hypothesis of `CollapseInj0_99` except `BT.isStd (ψ₀ ψ₀Ω₁)`, and
         `collapseInj0_needs_K99` is `ψ₀ψ₀Ω₁ = ψ₀Ω₁`: the collapse is not injective off the
         `K`-condition.  `collapseLe0_holds_at_injBad99` — the NON-strict conclusion holds
         at the same pair, so §99.2's factorisation separates two statements that really do
         differ.  `leBad99 = ψ₀ψ₁ψ₁0` against `Ω₁` refutes `CollapseLe0_96` itself with the
         same single hypothesis removed: **the non-strict clause does not buy freedom from
         the `K`-condition.**  And `dict_collides99` : `dict (1 ⊕ Ω₁) = dict Ω₁` — §96.6's
         own witness is a `dict`-collision, which is what §96's corpus had none of.

WHAT IS **NOT** CLAIMED.  `HiMono89` is NOT proved.  §99 does not prove `PsiIdxOKStd172`,
`IdxStd90`, `DictDenseHi94`, `CofDenseS1` or `BCofIn71`.  What §99 changes is that the
Veblen fold is now ONE clause instead of two, and that the bridge, the non-strict
one-component order and the injectivity are all consequences of it rather than companions
to it.

**WHERE §99 STOPPED, PRECISELY.**  The reverse of §99.4 does not run.  `HiMono89` at
`(a, b)` asks for `ψ₀` of `hi (dict a)` against `ψ₀` of `hi (dict b)`, and the only route
from the tail-free clause `CollapseMono0HiFree93` to it — §93.7's `hiMono89_of_hiFree93` —
needs `HiBridge93` at BOTH `a` and `b`.  The trick of §99.4 does not apply: there the
second argument entered only as the TARGET of a comparison whose left side was a `dict`
image, and `lt_collapse0_diffHi91` could take it as a bare term; here both sides are `hi`
of a `dict` image and the clause to be applied is stated on `BT` terms.  Measured by
`size a + size b` the bridge at either side is affordable, but `LoDomPair91`'s own order
instance `(c, a)` sits at `size c + size a`, which is not below `size a + size b` when `b`
is small — §93's remark, still true, and the reason §99 measures by `size a` alone.

WHAT THE MEASUREMENT SAYS (§99.7 gives the construction).  **§96 recorded a blind spot —
`dict` is injective on its 592 good terms, so its corpus could not tell `CollapseLe0_96`
from §79's strict clause — and the first job here is to fix it.**  Following §97's model
the population manufactures ill-formed terms (ASCENDING two-term sums, where `plus` drops
the first component) and does NOT filter them out: 200 terms, 120 of them not `BT.isStd`.

  * **`dict` collides 78 times** on the 100-term sample, and **0 times** on the 40 good
    terms and the 34 `K`-standard ones.  The detector works and the hypothesis is exactly
    what excludes collisions — which is the thing §96 could not show.
  * **§99.2 is visible as a partition.**  On 10000 pairs the strict conclusion fails 830
    times, the non-strict one 744, and `collapse 0 ∘ dict` collides on 86: `830 = 744 + 86`.
    On the 1600 good pairs, `67 = 61 + 6`.  On the 1156 `K`-standard pairs, `0, 0, 0`.
  * **The measure, counted.**  On 406 residual pairs the instance §93.6 needs through the
    bridge at `b` exceeds the `size a` budget on **246 (61%)**, and the second component of
    its gate instance `(c, hi b)` exceeds it on **187 (46%)**.  §99's own recursion partner
    `c ∈ G(a,0)` is below `size a` on **all 406**.
  * **The tail clause is not vacuous.**  On the `K`-standard sample `LoDomPair91` and
    `HiMono89` both hold on all 427 residual pairs; on the 13-term negative control where
    only the `K`-condition fails, **`LoDomPair91` fails on 4 of 9 and `HiMono89` on 0** —
    so what §99.4 made free is a clause that can fail.
  * **§99.1 is not about the identity**: `hi (dict b) ≠ dict b` on 40 of the 80 good terms
    and 30 of the 67 `K`-standard ones.
-/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

theorem ltM_ofList99 : ∀ (l : List Term), (∀ x ∈ l, lt x M = true) →
    lt (ofList l) M = true
  | [], _ => lt_zero_M
  | [a], h => h a (List.Mem.head _)
  | a :: b :: t, h => by
    show lt (add a (ofList (b :: t))) M = true
    rw [lt_add_M]
    exact h a (List.Mem.head _)

theorem ltM_hiW99 {x : Term} (hx : inT x = true) (hlx : lt x M = true) :
    lt (hiW89 x) M = true := by
  show lt (ofList ((toList x).filter (fun p => !lt p (reg 1)))) M = true
  exact ltM_ofList99 _ (fun p hp => ltM_toList x hx hlx p (List.mem_filter.mp hp).1)

theorem psiIdxOK_hiW99 {x : Term} (hx : inT x = true) (H : PsiIdxOK 0 x) :
    PsiIdxOK 0 (hiW89 x) := by
  have e : (wcnf (reg 1) (toList x)).1 = (wcnf (reg 1) (toList (hiW89 x))).1 := by
    rw [wcnf_split89 hx]
  show ∀ p ∈ scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (hiW89 x))).1,
    le (reg 1) p.2.1 = true → inT (psi (reg 1) (idxOf (reg 1) p.1 p.2)) = true
  rw [← e]
  exact H

end

/-! ### §99.2 (A) 非狭義の単調性の値段 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- `collapse 0` が像の上で単射であること — 狭義と非狭義の差ちょうど。 -/
def CollapseInj0_99 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    lt (dict a) (dict b) = true →
    collapse 0 (dict a) ≠ collapse 0 (dict b)

/-- **非狭義は狭義から出る。** 対角は `le` の反射律で只。 -/
theorem collapseLe0_of79 (H : CollapseMono0_79) : CollapseLe0_96 := by
  intro a b hbA hbB hsA hsB h
  rw [Trans.Dict.dict_D, Trans.Dict.dict_D]
  rcases (Bool.or_eq_true _ _).mp h with h1 | h1
  · rw [eq_of_beq h1]; exact le_self77 _
  · exact le_of_lt (H a b hbA hbB hsA hsB h1)

theorem inj0_of79 (H : CollapseMono0_79) : CollapseInj0_99 :=
  fun a b hbA hbB hsA hsB h => ne_of_lt96 (H a b hbA hbB hsA hsB h)

theorem mono79_of_le_inj99 (L : CollapseLe0_96) (I : CollapseInj0_99) : CollapseMono0_79 := by
  intro a b hbA hbB hsA hsB h
  have h2 := L a b hbA hbB hsA hsB (le_of_lt h)
  rw [Trans.Dict.dict_D, Trans.Dict.dict_D] at h2
  exact lt_of_le_ne96 h2 (I a b hbA hbB hsA hsB h)

/-- **§99.2 の主定理 — 狭義 = 非狭義 + 単射。** §96.3 の `dictLtAtom96_iff` を
    添字 0 の一本ぶんに落とした形。**`CollapseLe0_96` は真に弱いが、弱い分は
    ちょうど単射性であって、Veblen の折り畳みの分ではない。** -/
theorem mono79_iff99 : CollapseMono0_79 ↔ (CollapseLe0_96 ∧ CollapseInj0_99) :=
  ⟨fun H => ⟨collapseLe0_of79 H, inj0_of79 H⟩, fun h => mono79_of_le_inj99 h.1 h.2⟩

/-- §81 の残余からも出る。 -/
theorem collapseLe0_of_hi81 (Hp : PsiIdxOKStd172) (H : CollapseMono0Hi81) : CollapseLe0_96 :=
  collapseLe0_of79 (collapseMono0_of_hi81 Hp H)

end

/-! ### §99.3 記号数を**両辺で**切った順序の鎖 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- 両辺の記号数を `n` で切った順序。§96 の `DictLtUpTo77` は**和**で切っていた。 -/
def DictLtBoth99 (n : Nat) : Prop :=
  ∀ (f : Nat) (l1 l2 : List BT), szL77 l1 ≤ n → szL77 l2 ≤ n →
    GoodL77 l1 → GoodL77 l2 → BT.ltL f l1 l2 = true →
    lt (dict (BT.ofL l1)) (dict (BT.ofL l2)) = true

/-- **第一成分の記号数だけで切った §81 の残余。** 第二引数は野放し。 -/
def GateFst99 (n : Nat) : Prop :=
  ∀ (a b : BT), BT.size a ≤ n →
    btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lt (dict a) (dict b) = true →
    lt (collapse 0 (dict a)) (collapse 0 (dict b)) = true

/-- 第一成分の記号数だけで切った頭部の比較。 -/
def DictHeadLtFst99 (n : Nat) : Prop := ∀ (u v : Nat) (a b : BT),
    BT.size a ≤ n →
    btLe72 1 (BT.D u a) = true → btLe72 1 (BT.D v b) = true →
    BT.isStd (BT.D u a) = true → BT.isStd (BT.D v b) = true →
    (u < v ∨ (u = v ∧ lt (dict a) (dict b) = true)) →
    lt (dict (BT.D u a)) (dict (BT.D v b)) = true

theorem gateFst99_mono {m n : Nat} (h : m ≤ n) (G : GateFst99 n) : GateFst99 m :=
  fun a b hsz => G a b (by omega)

theorem dictLtBoth99_mono {m n : Nat} (h : m ≤ n) (S : DictLtBoth99 n) : DictLtBoth99 m :=
  fun f l1 l2 h1 h2 => S f l1 l2 (by omega) (by omega)

theorem szL77_eq_zero99 : ∀ (l : List BT), szL77 l = 0 → l = []
  | [], _ => rfl
  | p :: r, h => by
      have := size_pos77 p
      have he : szL77 (p :: r) = BT.size p + szL77 r := rfl
      omega

/-- 成分ひとつぶんの非狭義の順序 — 両辺切りの鎖から。 -/
theorem dictLeAtom99 {n : Nat} (S : DictLtBoth99 n) {p q : BT}
    (hsp : BT.isStd p = true) (hsq : BT.isStd q = true)
    (hbp : btLe72 1 p = true) (hbq : btLe72 1 q = true)
    (hszp : BT.size p ≤ n) (hszq : BT.size q ≤ n)
    (h : BT.le p q = true) : le (dict p) (dict q) = true := by
  rcases (Bool.or_eq_true _ _).mp h with h1 | h1
  · rw [bt_beq_eq77 h1]; exact le_self77 _
  · have t1 := szL77_toL p
    have t2 := szL77_toL q
    have hq2 := S (BT.size p + BT.size q + 2) (BT.toL p) (BT.toL q)
      (by omega) (by omega) (good_toL77 p hsp hbp) (good_toL77 q hsq hbq) h1
    rw [ofL_toL77 p hsp, ofL_toL77 q hsq] at hq2
    exact le_of_lt hq2

/-- **橋、両辺切りの形。** 隣り合う成分の像が `le` で並ぶことしか使わない。 -/
theorem bridge99 (Hp : PsiIdxOKStd172) {n : Nat} (S : DictLtBoth99 n) :
    ∀ (l : List BT), GoodL77 l → szL77 l ≤ n + 1 →
      toList (dict (BT.ofL l)) = l.map dict
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
      have he2 : szL77 (BT.D v b :: r) = BT.size (BT.D v b) + szL77 r := rfl
      have hp1 := size_pos77 (BT.D u a)
      have hp2 := size_pos77 (BT.D v b)
      have ih : toList (dict (BT.ofL (BT.D v b :: r)))
          = dict (BT.D v b) :: r.map dict := bridge99 Hp S (BT.D v b :: r) hgt (by omega)
      have hiP : inT (dict (BT.D u a)) = true :=
        (inT_dict_of_std172 Hp (BT.D u a) (hg.2.2.1 _ (List.Mem.head _))
          (hg.2.1 _ (List.Mem.head _))).1
      have hiT : inT (dict (BT.ofL (BT.D v b :: r))) = true :=
        (inT_dict_of_std172 Hp _ (btLe_ofL77 hgt) (isStd_ofL77 hgt)).1
      have hle : le (dict (BT.D v b)) (dict (BT.D u a)) = true :=
        dictLeAtom99 S (hg.2.1 _ (List.Mem.tail _ (List.Mem.head _)))
          (hg.2.1 _ (List.Mem.head _))
          (hg.2.2.1 _ (List.Mem.tail _ (List.Mem.head _)))
          (hg.2.2.1 _ (List.Mem.head _)) (by omega) (by omega)
          ((Bool.and_eq_true _ _).mp hg.2.2.2).1
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

theorem ofListMap99 (Hp : PsiIdxOKStd172) {n : Nat} (S : DictLtBoth99 n)
    (l : List BT) (hg : GoodL77 l) (hsz : szL77 l ≤ n + 1) :
    ofList (l.map dict) = dict (BT.ofL l) := by
  rw [← bridge99 Hp S l hg hsz,
    inT_ofList_toList _ (inT_dict_of_std172 Hp _ (btLe_ofL77 hg) (isStd_ofL77 hg)).1]

end

/-! ### §99.3b 一段ぶんの前進と鎖の全体 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- **§77.4 の和の帰納法、両辺切りの形。** 頭部の比較は**第一成分の引数**でしか
    使わない — そこが §96 の和切りとの違い。 -/
theorem dictLtBoth99_step (Hp : PsiIdxOKStd172) {n : Nat}
    (H : DictHeadLtFst99 n) (S : DictLtBoth99 n) : DictLtBoth99 (n + 1) := by
  intro f l1 l2 hs1 hs2 g1 g2 hlt
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
            have ta := szL77_toL a
            have tb := szL77_toL b
            have hB1 : toList (dict (BT.ofL (BT.D u a :: ps)))
                = dict (BT.D u a) :: ps.map dict := bridge99 Hp S _ g1 hs1
            have hB2 : toList (dict (BT.ofL (BT.D v b :: qs)))
                = dict (BT.D v b) :: qs.map dict := bridge99 Hp S _ g2 hs2
            have hiX : inT (dict (BT.ofL (BT.D u a :: ps))) = true :=
              (inT_dict_of_std172 Hp _ (btLe_ofL77 g1) (isStd_ofL77 g1)).1
            have hiY : inT (dict (BT.ofL (BT.D v b :: qs))) = true :=
              (inT_dict_of_std172 Hp _ (btLe_ofL77 g2) (isStd_ofL77 g2)).1
            have hbA : btLe72 1 (BT.D u a) = true := g1.2.2.1 _ (List.Mem.head _)
            have hbB : btLe72 1 (BT.D v b) = true := g2.2.2.1 _ (List.Mem.head _)
            have hsA : BT.isStd (BT.D u a) = true := g1.2.1 _ (List.Mem.head _)
            have hsB : BT.isStd (BT.D v b) = true := g2.2.1 _ (List.Mem.head _)
            rw [ltL_DD93] at hlt
            by_cases huv : u < v
            · exact lt_of_hd_lt hiX hiY hB1 hB2
                (H u v a b (by omega) hbA hbB hsA hsB (Or.inl huv))
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
                  rw [ofListMap99 Hp S ps (goodL77_tail g1) (by omega),
                    ofListMap99 Hp S qs (goodL77_tail g2) (by omega)]
                  exact S f' ps qs (by omega) (by omega)
                    (goodL77_tail g1) (goodL77_tail g2) hlt
                · rw [if_neg hab] at hlt
                  have hsa : BT.isStd a = true := isStd_of_D hsA
                  have hsb : BT.isStd b = true := isStd_of_D hsB
                  have hba : btLe72 1 a = true := (btLe72_D 1 u a hbA).2
                  have hbb : btLe72 1 b = true := (btLe72_D 1 v b hbB).2
                  have hlta : lt (dict (BT.ofL (BT.toL a))) (dict (BT.ofL (BT.toL b))) = true :=
                    S f' (BT.toL a) (BT.toL b) (by omega) (by omega)
                      (good_toL77 a hsa hba) (good_toL77 b hsb hbb) hlt
                  rw [ofL_toL77 a hsa, ofL_toL77 b hsb] at hlta
                  exact lt_of_hd_lt hiX hiY hB1 hB2
                    (H u v a b (by omega) hbA hbB hsA hsB (Or.inr ⟨huv2, hlta⟩))

/-- **§81.7 を第一成分の記号数で切った形。** もとの証明は対について各点的。 -/
theorem dictHeadLtFst99_of_gate (Hp : PsiIdxOKStd172) {n : Nat}
    (G : GateFst99 n) : DictHeadLtFst99 n := by
  intro u v a b hsz hbA hbB hsA hsB hc
  rcases hc with huv | ⟨huv, hlt⟩
  · exact dictCross79 Hp u v a b huv hbA hbB hsA hsB
  · subst huv
    have hu := (btLe72_D 1 u a hbA).1
    have hba := (btLe72_D 1 u a hbA).2
    have hbb := (btLe72_D 1 u b hbB).2
    have hsa := isStd_of_D hsA
    have hsb := isStd_of_D hsB
    cases u with
    | zero =>
      have hia := inT_dict_of_std172 Hp a hba hsa
      have hib := inT_dict_of_std172 Hp b hbb hsb
      rw [Trans.Dict.dict_D, Trans.Dict.dict_D]
      by_cases hWb : le (reg 1) (dict b) = true
      · by_cases hWa : le (reg 1) (dict a) = true
        · exact G a b hsz hbA hbB hsA hsB hWa hWb hlt
        · have hlow : lowHd81 a = true := by
            cases hh : lowHd81 a with
            | true => rfl
            | false => exact absurd (le_reg1_dict_of_not_lowHd81 Hp a hba hsa hh) hWa
          have hb0 : btLe72 0 a = true :=
            btLe0_of_lowHd81 a hba hsa hlow (lowHd_GB_of_std81 hsA hlow)
          exact lt_collapse0_cross81 hia.1 (lt_dict_E81 Hp a hb0 hsa) hib.1 hib.2
            (Hp 0 b (by omega) hbb hsB) hWb
      · have hlb : lt (dict b) (reg 1) = true :=
          lt_of_not_le_inT inT_W79 hib.1 (bool_false hWb)
        have hla : lt (dict a) (reg 1) = true := lt_trans_inT hia.1 hib.1 inT_W79 hlt hlb
        exact collapse0_mono_ltW81 hia.1 hib.1 hla hlb hlt
    | succ u' =>
      cases u' with
      | zero =>
        rw [Trans.Dict.dict_D, Trans.Dict.dict_D]
        exact collapseMono1_79 Hp a b hbA hbB hsA hsB hlt
      | succ _ => exact absurd hu (by omega)

/-- **鎖の全体。** 記号数 `n` までの順序には、記号数 `n` 未満の門しか要らない。 -/
theorem dictLtBoth99_all (Hp : PsiIdxOKStd172) :
    ∀ (n : Nat), (∀ m, m < n → GateFst99 m) → DictLtBoth99 n
  | 0, _ => by
      intro f l1 l2 h1 h2 _ _ hlt
      rw [szL77_eq_zero99 l1 (by omega), szL77_eq_zero99 l2 (by omega)] at hlt
      cases f with
      | zero => exact Bool.noConfusion hlt
      | succ f' => rw [ltL_nil_nil77] at hlt; exact Bool.noConfusion hlt
  | n + 1, hg =>
      dictLtBoth99_step Hp (dictHeadLtFst99_of_gate Hp (hg n (by omega)))
        (dictLtBoth99_all Hp n (fun m hm => hg m (by omega)))

end

/-! ### §99.4 尾の条項は `HiMono89` から落ちる -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- 第一成分の記号数で切った §91 の尾の条項。 -/
def LoDomPairFst99 (n : Nat) : Prop :=
  ∀ (a b : BT), BT.size a ≤ n →
    btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    ∀ p ∈ toList (loW89 (dict a)), lt p (collapse 0 (hiW89 (dict b))) = true

/-- §91.3 の組み立てを記号数つきで。もとの証明は対について各点的。 -/
theorem gateFst99_of_loDom (Hp : PsiIdxOKStd172) (H : HiMono89) {n : Nat}
    (L : LoDomPairFst99 n) : GateFst99 n := by
  intro a b hsz hbA hbB hsA hsB hWa hWb h
  have hba := (btLe72_D 1 0 a hbA).2
  have hbb := (btLe72_D 1 0 b hbB).2
  have hsa := isStd_of_D hsA
  have hsb := isStd_of_D hsB
  have hia := inT_dict_of_std172 Hp a hba hsa
  have hib := inT_dict_of_std172 Hp b hbb hsb
  have hpa := Hp 0 a (by omega) hba hsA
  have hpb := Hp 0 b (by omega) hbb hsB
  by_cases heq : hiW89 (dict a) = hiW89 (dict b)
  · exact lt_collapse0_sameHi89 hia.1 hia.2 hpa hWa hib.1 hib.2 hpb hWb heq h
  · have hhi := lt_hi89 hia.1 hib.1 h heq
    exact lt_collapse0_diffHi91 hia.1 hia.2 hpa hWa hib.1 hib.2 hpb hWb
      (L a b hsz hbA hbB hsA hsB hWa hWb hhi) (H a b hbA hbB hsA hsB hWa hWb hhi)

/-- **§99 の主定理 — 尾の条項は `HiMono89` だけから、記号数 `size a` の帰納法で出る。**

    §93.6 は同じ場所で §81 の残余を対 `(c, hi b)` に当てていた。そのためには
    `hi (dict b) = dict (hi b)` — **`b` での橋** — が要り、その橋には `size b` までの
    門が要るので、`size a` だけの測度が閉じなかった (§96 の診断)。ここでは対
    `(c, hi b)` を作らず、`Y = hi (dict b)` を 𝔗(M) の項のまま扱い、
    `lt_collapse0_diffHi91` を `(dict c, Y)` に当てる。その二つの側条件は
    `HiMono89 (c, b)` と**この定理自身の `(c, b)` での例** — `size c < size a` —
    であって、`b` での橋はどこにも現れない。 -/
theorem loDomPairFst99_all (Hp : PsiIdxOKStd172) (H : HiMono89) :
    ∀ (n : Nat), LoDomPairFst99 n := by
  intro n
  refine Nat.strongRecOn (motive := fun n => LoDomPairFst99 n) n ?_
  intro n IH a b hsza hbA hbB hsA hsB hWa hWb hhi p hp
  have hgate : ∀ m, m < n → GateFst99 m :=
    fun m hm => gateFst99_of_loDom Hp H (IH m hm)
  have S : DictLtBoth99 n := dictLtBoth99_all Hp n hgate
  have hba := (btLe72_D 1 0 a hbA).2
  have hbb := (btLe72_D 1 0 b hbB).2
  have hsa := isStd_of_D hsA
  have hsb := isStd_of_D hsB
  have hia := inT_dict_of_std172 Hp a hba hsa
  have hib := inT_dict_of_std172 Hp b hbb hsb
  have hgood : GoodL77 (BT.toL a) := good_toL77 a hsa hba
  have hszLa := szL77_toL a
  have htl : toList (dict a) = (BT.toL a).map dict := by
    have h1 := bridge99 Hp S (BT.toL a) hgood (by omega)
    rw [ofL_toL77 a hsa] at h1
    exact h1
  have hlo : toList (loW89 (dict a)) = (loL93 (BT.toL a)).map dict := by
    rw [toList_loW89 hia.1, htl, filter_map93 dict (fun p => lt p (reg 1)) (BT.toL a),
      filter_congr93 (fun t => lt (dict t) (reg 1)) (fun t => !hiA93 t) (BT.toL a)
        (fun t ht => by
          obtain ⟨u, c, rfl⟩ := hgood.1 t ht
          have hq := hiA_dict93 Hp u c (hgood.2.2.1 _ ht) (hgood.2.1 _ ht)
          show lt (dict (BT.D u c)) (reg 1) = !hiA93 (BT.D u c)
          rw [← hq]
          cases hz : lt (dict (BT.D u c)) (reg 1) with
          | true => rfl
          | false => rfl)]
    rfl
  rw [hlo] at hp
  obtain ⟨t, htmem, hpt⟩ := List.mem_map.mp hp
  have htL : t ∈ BT.toL a := (List.mem_filter.mp htmem).1
  have hlot : hiA93 t = false := by
    have h1 := (List.mem_filter.mp htmem).2
    cases hz : hiA93 t with
    | false => rfl
    | true => rw [hz] at h1; exact absurd h1 Bool.noConfusion
  obtain ⟨u, c, rfl⟩ := hgood.1 t htL
  have hu0 : u = 0 := by
    have hu1 : u ≤ 1 := (btLe72_D 1 u c (hgood.2.2.1 _ htL)).1
    have h2 : decide (1 ≤ u) = false := hlot
    have h3 : ¬ (1 ≤ u) := of_decide_eq_false h2
    omega
  subst hu0
  have hst : BT.isStd (BT.D 0 c) = true := hgood.2.1 _ htL
  have hbt : btLe72 1 (BT.D 0 c) = true := hgood.2.2.1 _ htL
  have hbc := (btLe72_D 1 0 c hbt).2
  have hsc := isStd_of_D hst
  have hic := inT_dict_of_std172 Hp c hbc hsc
  have hmemGB : c ∈ BT.GB 0 a := arg_mem_GB0_82 a 0 c htL
  have hszc : BT.size c < BT.size a := size_GB93 a c hmemGB
  have hltca : BT.lt c a = true := (std0_split82 hsA).2 c hmemGB
  have hszLc := szL77_toL c
  have h1 : lt (dict c) (dict a) = true := by
    have h0 := S (BT.size c + BT.size a + 2) (BT.toL c) (BT.toL a)
      (by omega) (by omega) (good_toL77 c hsc hbc) hgood hltca
    rw [ofL_toL77 c hsc, ofL_toL77 a hsa] at h0
    exact h0
  have h2 : le (hiW89 (dict c)) (hiW89 (dict a)) = true := le_hiW_of_lt93 hic.1 hia.1 h1
  have h3 : lt (hiW89 (dict c)) (hiW89 (dict b)) = true :=
    lt_of_le_of_lt3 (inT_le_fragR _ (inT_hiW89 hic.1)) (inT_le_fragR _ (inT_hiW89 hia.1))
      (inT_le_fragR _ (inT_hiW89 hib.1)) h2 hhi
  have h4 : lt (dict c) (hiW89 (dict b)) = true := lt_hiW_of_lt_hiW93 hic.1 hib.1 h3
  have hiY : inT (hiW89 (dict b)) = true := inT_hiW89 hib.1
  have hlY : lt (hiW89 (dict b)) M = true := ltM_hiW99 hib.1 hib.2
  have hpY : PsiIdxOK 0 (hiW89 (dict b)) :=
    psiIdxOK_hiW99 hib.1 (Hp 0 b (by omega) hbb hsB)
  have hWY : le (reg 1) (hiW89 (dict b)) = true := le_W_hiW93 hib.1 hWb
  have hYY : hiW89 (hiW89 (dict b)) = hiW89 (dict b) :=
    hiW89_self89 hiY (loW_hiW93 hib.1)
  rw [← hpt, Trans.Dict.dict_D]
  cases hcase : le (reg 1) (dict c) with
  | false =>
    have hlow : lowHd81 c = true := by
      cases hh : lowHd81 c with
      | true => rfl
      | false =>
        rw [le_reg1_dict_of_not_lowHd81 Hp c hbc hsc hh] at hcase
        exact Bool.noConfusion hcase
    have hb0 : btLe72 0 c = true :=
      btLe0_of_lowHd81 c hbc hsc hlow (lowHd_GB_of_std81 hst hlow)
    exact lt_collapse0_cross81 hic.1 (lt_dict_E81 Hp c hb0 hsc) hiY hlY hpY hWY
  | true =>
    by_cases heq : hiW89 (dict c) = hiW89 (hiW89 (dict b))
    · exact lt_collapse0_sameHi89 hic.1 hic.2 (Hp 0 c (by omega) hbc hst) hcase
        hiY hlY hpY hWY heq h4
    · have h5 : lt (hiW89 (dict c)) (hiW89 (dict b)) = true := by
        have h6 := lt_hi89 hic.1 hiY h4 heq
        rw [hYY] at h6
        exact h6
      have hHi : lt (collapse 0 (hiW89 (dict c)))
          (collapse 0 (hiW89 (hiW89 (dict b)))) = true := by
        rw [hYY]
        exact H c b hbt hbB hst hsB hcase hWb h5
      have hhd : ∀ q ∈ toList (loW89 (dict c)),
          lt q (collapse 0 (hiW89 (hiW89 (dict b)))) = true := by
        rw [hYY]
        exact IH (BT.size c) (by omega) c b (Nat.le_refl _) hbt hbB hst hsB hcase hWb h5
      exact lt_collapse0_diffHi91 hic.1 hic.2 (Hp 0 c (by omega) hbc hst) hcase
        hiY hlY hpY hWY hhd hHi

end

/-! ### §99.5 組み立て — 326 行目の Veblen の門は `HiMono89` ただ一つ -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- **`LoDomPair91` は `HiMono89` の帰結。** §91 が条項として立て、§93 が
    「§81 の残余そのもの」と値付けした対の条項は、独立な条項ではなかった。 -/
theorem loDomPair91_of_hiMono99 (Hp : PsiIdxOKStd172) (H : HiMono89) : LoDomPair91 :=
  fun a b hbA hbB hsA hsB hWa hWb hhi p hp =>
    loDomPairFst99_all Hp H (BT.size a) a b (Nat.le_refl _) hbA hbB hsA hsB hWa hWb hhi p hp

/-- **§99 の主結論 — §81 の残余は `HiMono89` から出る。** -/
theorem collapseMono0Hi_of_hiMono99 (Hp : PsiIdxOKStd172) (H : HiMono89) :
    CollapseMono0Hi81 :=
  collapseMono0Hi_of_91 Hp H (loDomPair91_of_hiMono99 Hp H)

/-- **§93 の分割は、片方が只だった。** -/
theorem gate_iff_hiMono99 (Hp : PsiIdxOKStd172) : CollapseMono0Hi81 ↔ HiMono89 :=
  ⟨fun H => hiMono89_of81 Hp H, collapseMono0Hi_of_hiMono99 Hp⟩

/-- §93 の同値の、片方が消えた形。 -/
theorem gates_iff99 (Hp : PsiIdxOKStd172) : (HiMono89 ∧ LoDomPair91) ↔ HiMono89 :=
  ⟨fun h => h.1, fun H => ⟨H, loDomPair91_of_hiMono99 Hp H⟩⟩

/-- **橋は定理になった** — §93 の半橋も §96 の完全な橋も。 -/
theorem hiBridge99 (Hp : PsiIdxOKStd172) (H : HiMono89) : HiBridge93 :=
  hiBridge93_of81 Hp (collapseMono0Hi_of_hiMono99 Hp H)

theorem dictLe99 (Hp : PsiIdxOKStd172) (H : HiMono89) : DictLe96 :=
  dictLe96_of81 Hp (collapseMono0Hi_of_hiMono99 Hp H)

theorem fullBridge99 (Hp : PsiIdxOKStd172) (H : HiMono89) : FullBridge96 :=
  fullBridge96_of_le Hp (dictLe99 Hp H)

theorem dictDesc99 (Hp : PsiIdxOKStd172) (H : HiMono89) : DictDesc96 :=
  desc96_of_fullBridge Hp (fullBridge99 Hp H)

theorem dictLeAtom96_99 (Hp : PsiIdxOKStd172) (H : HiMono89) : DictLeAtom96 :=
  dictLeAtom96_of_le (dictLe99 Hp H)

/-- **(A) `CollapseLe0_96` も定理になった。** -/
theorem collapseLe0_99 (Hp : PsiIdxOKStd172) (H : HiMono89) : CollapseLe0_96 :=
  collapseLe0_of_hi81 Hp (collapseMono0Hi_of_hiMono99 Hp H)

theorem collapseMono0_99 (Hp : PsiIdxOKStd172) (H : HiMono89) : CollapseMono0_79 :=
  collapseMono0_of_hi81 Hp (collapseMono0Hi_of_hiMono99 Hp H)

theorem collapseInj0_99 (Hp : PsiIdxOKStd172) (H : HiMono89) : CollapseInj0_99 :=
  inj0_of79 (collapseMono0_99 Hp H)

theorem dictLtAtom99 (Hp : PsiIdxOKStd172) (H : HiMono89) : DictLtAtom96 :=
  fun u v a b hbA hbB hsA hsB h =>
    dictLt_of_head77 Hp (dictHeadLt81 Hp (collapseMono0Hi_of_hiMono99 Hp H))
      (BT.D u a) (BT.D v b) hbA hbB hsA hsB h

/-- **(B) `DictAtomInj96`。** §96.3 の分解の右の項。 -/
theorem dictAtomInj99 (Hp : PsiIdxOKStd172) (H : HiMono89) : DictAtomInj96 :=
  (dictLtAtom96_iff.mp (dictLtAtom99 Hp H)).2

theorem dictLtA74_99 (Hp : PsiIdxOKStd172) (H : HiMono89) : DictLtA74 :=
  dictLtA74_81 Hp (collapseMono0Hi_of_hiMono99 Hp H)

/-- **326 行目 — Veblen の折り畳みのぶんは `HiMono89` ひとつ。** §97 でとどめた
    密度の側は `DictDenseHi94` ひとつ。 -/
theorem certIn_t326_99 (Hp : PsiIdxOKStd172) (H : HiMono89) (HH : DictDenseHi94)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_97 Hp (dictLtA74_99 Hp H) HH hacc

/-- §91・§93 の形との繋ぎ — `LoDomPair91` はもう要らない。 -/
theorem certIn_t326_pair99 (Hp : PsiIdxOKStd172) (H : HiMono89)
    (HCD : CofDenseS1) (HBC : BCofIn71)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_81 Hp (collapseMono0Hi_of_hiMono99 Hp H) HCD HBC hacc

end

/-! ### §99.6 否定 — 反例は手で組んだ二つ、どちらも `K` の条件ひとつだけを外す -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- **反例 1 — `ψ₀Ω₁`。** 記号 3 個。 -/
def injBad99 : BT := BT.D 0 (BT.D 1 BT.zero)

/-- `ψ₀Ω₁` と `Ω₁` は `CollapseInj0_99` の仮説を**すべて**満たす — ただし
    `BT.isStd (ψ₀ ψ₀Ω₁)` だけが偽。文を読んで、そこ以外を満たすように組んだ。 -/
theorem injBad99_facts : (btLe72 1 injBad99, btLe72 1 (BT.D 1 BT.zero),
    BT.isStd injBad99, BT.isStd (BT.D 1 BT.zero),
    BT.isStd (BT.D 0 injBad99), BT.isStd (BT.D 0 (BT.D 1 BT.zero)),
    lt (dict injBad99) (dict (BT.D 1 BT.zero)))
    = (true, true, true, true, false, true, true) := rfl

/-- **`CollapseInj0_99` は `K` の条件なしでは偽。** `ψ₀ψ₀Ω₁ = ψ₀Ω₁` — Buchholz の
    `ψ₀` は正規形の外では単射でない。 -/
theorem collapseInj0_needs_K99 :
    collapse 0 (dict injBad99) = collapse 0 (dict (BT.D 1 BT.zero)) := rfl

/-- **同じ対で `CollapseLe0_96` の結論は成り立つ。** だから §99.2 の分解
    (狭義 = 非狭義 + 単射) は形式ではない — 母集団がその差を実際に持つ。
    §96 の母集団は `dict` が単射だったのでこの差が見えなかった。 -/
theorem collapseLe0_holds_at_injBad99 :
    le (collapse 0 (dict injBad99)) (collapse 0 (dict (BT.D 1 BT.zero))) = true := rfl

/-- **反例 2 — `ψ₀ψ₁ψ₁0`。** 記号 4 個。 -/
def leBad99 : BT := BT.D 0 (BT.D 1 (BT.D 1 BT.zero))

/-- **`CollapseLe0_96` そのものが `K` の条件なしでは偽。** 非狭義にしても
    `K` の条件は落とせない — 外れるのはやはりその一つだけである。 -/
theorem leBad99_facts : (btLe72 1 leBad99, BT.isStd leBad99,
    BT.isStd (BT.D 0 leBad99), BT.isStd (BT.D 0 (BT.D 1 BT.zero)),
    le (dict leBad99) (dict (BT.D 1 BT.zero)),
    le (collapse 0 (dict leBad99)) (collapse 0 (dict (BT.D 1 BT.zero))))
    = (true, true, false, true, true, false) := rfl

/-- **`dict` は仮説の外で衝突する。** §96.6 の `aDrop96 = 1 ⊕ Ω₁` の像は `Ω₁` の像
    そのもの — 昇べきの和で `plus` が第一成分を落とすから。§96 の母集団には
    こういう項が一つも無かった。 -/
theorem dict_collides99 : dict aDrop96 = dict (BT.D 1 BT.zero) := rfl

theorem dict_collides99_facts :
    (BT.isStd aDrop96, btLe72 1 aDrop96, BT.lt aDrop96 (BT.D 1 BT.zero))
    = (false, true, true) := rfl

end

/-! ### §99.7 測定 (凍結)

**構成 — §96 の盲点を先に潰す。** §96 の母集団は 592 個の良い項の上で `dict` が
単射だったので、`CollapseLe0_96` と §79 の狭義の条項の差を**一つも見なかった**。
ここでは §97 の作り方に倣い、**壊れた項を故意に作り、濾さない**。

    bs99      段 1 以下の種 7 項 (`cexA89` の親 `ψ₁ψ₀ψ₁ψ₁0` を含む)
    deep99    `ψ₀`・`ψ₁` を 1 段ずつかぶせて 2 つに 1 つ間引く操作を 3 回
    ksum99    `K` 標準な主要項どうしの降べき 2 項和・3 項和 (残余を厚くする線)
    desc99    降べきの 2 項和 (行儀のよい線)
    asc99     **昇べきの 2 項和** — `plus` がここで成分を落とす (衝突の線)
              とその `ψ₀`・`ψ₁` 帽子

    popRaw99  200 項   濾さない
    popGood99  80 項   段 1 以下かつ `BT.isStd`
    popK99     67 項   さらに `BT.isStd (ψ₀ ·)`
    popHi99    57 項   さらに `Ω₁ ≤ dict a`
    popNK99    13 項   `K` の条件だけが偽 (負の対照)

対の母集団は 2 つに 1 つ間引いた `sRaw99` (100 項)・`sGood99` (40)・`sK99` (34)・
`sHi99` (29)。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

private def dedup99 (l : List BT) : List BT :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []
private def every99 (k : Nat) (l : List BT) : List BT :=
  (l.zipIdx.filter (fun p => p.2 % k == 0)).map (·.1)

private def bs99 : List BT :=
  [BT.zero, BT.D 0 BT.zero, BT.D 0 (BT.D 0 BT.zero), BT.D 1 BT.zero,
   BT.D 1 (BT.D 1 BT.zero), BT.D 0 (BT.D 1 BT.zero),
   BT.D 1 (BT.D 0 (BT.D 1 (BT.D 1 BT.zero)))]
private def cap99 (l : List BT) : List BT := l.map (BT.D 0) ++ l.map (BT.D 1)
private def lay99 : Nat → List BT → List BT
  | 0, l => l
  | n + 1, l => every99 2 (cap99 (lay99 n l))
private def deep99 : List BT :=
  dedup99 (bs99 ++ lay99 1 bs99 ++ lay99 2 bs99 ++ lay99 3 bs99)
private def prin99 (l : List BT) : List BT := l.filter BT.isP
private def desc99 (l : List BT) : List BT :=
  (prin99 l).flatMap (fun a => ((prin99 l).filter (fun b => BT.le b a)).map (BT.sum a))
/-- **昇べきの和 — 故意に壊した線。** `plus` はここで第一成分を落とす。 -/
private def asc99 (l : List BT) : List BT :=
  (prin99 l).flatMap (fun a => ((prin99 l).filter (fun b => BT.lt a b)).map (BT.sum a))
private def kprin99 : List BT :=
  deep99.filter (fun a => BT.isP a && btLe72 1 a && BT.isStd a && BT.isStd (BT.D 0 a))
private def ksum99 : List BT :=
  dedup99 (desc99 kprin99 ++ (desc99 kprin99).flatMap
    (fun a => (kprin99.filter (fun b => BT.le b (BT.D 0 BT.zero))).map (fun b => BT.sum a b)))

private def popRaw99 : List BT :=
  dedup99 (deep99 ++ ksum99 ++ every99 3 (desc99 (every99 2 deep99))
            ++ every99 3 (asc99 (every99 2 deep99))
            ++ (every99 4 (asc99 (every99 2 deep99))).map (BT.D 0)
            ++ (every99 4 (asc99 (every99 2 deep99))).map (BT.D 1))
private def popGood99 : List BT := popRaw99.filter (fun x => btLe72 1 x && BT.isStd x)
private def popK99 : List BT := popGood99.filter (fun a => BT.isStd (BT.D 0 a))
private def lowW99 (a : BT) : Bool := TM.Term.lt (dict a) (reg 1)
private def popHi99 : List BT := popK99.filter (fun a => !(lowW99 a))
private def popNK99 : List BT := popGood99.filter (fun a => !(BT.isStd (BT.D 0 a)))

private def sRaw99 : List BT := every99 2 popRaw99
private def sGood99 : List BT := every99 2 popGood99
private def sK99 : List BT := every99 2 popK99
private def sHi99 : List BT := every99 2 popHi99

private def pairs99 (l : List BT) : List (BT × BT) :=
  l.flatMap (fun a => l.map (fun b => (a, b)))
private def C0_99 (x : BT) : Term := collapse 0 (dict x)
/-- `dict` の衝突。 -/
private def colls99 (l : List BT) : List (BT × BT) :=
  (pairs99 l).filter (fun p => !(p.1 == p.2) && (dict p.1 == dict p.2))
/-- §79 の狭義の条項の結論が破れる対。 -/
private def ltFail99 (l : List BT) : List (BT × BT) :=
  (pairs99 l).filter (fun p => TM.Term.lt (dict p.1) (dict p.2)
      && !(TM.Term.lt (C0_99 p.1) (C0_99 p.2)))
/-- §96 の非狭義の条項の結論が破れる対。 -/
private def leFail99 (l : List BT) : List (BT × BT) :=
  (pairs99 l).filter (fun p => TM.Term.le (dict p.1) (dict p.2)
      && !(TM.Term.le (C0_99 p.1) (C0_99 p.2)))
/-- `collapse 0 ∘ dict` の衝突 — 狭義と非狭義のちょうど差 (§99.2)。 -/
private def inj0Fail99 (l : List BT) : List (BT × BT) :=
  (pairs99 l).filter (fun p => TM.Term.lt (dict p.1) (dict p.2) && (C0_99 p.1 == C0_99 p.2))
private def hiOK99 (a : BT) : Bool := hiW89 (dict a) == dict (hiB93 a)
private def fullOK99 (a : BT) : Bool := toList (dict a) == (BT.toL a).map dict
private def hipairs99 : List (BT × BT) :=
  (pairs99 sHi99).filter (fun p => TM.Term.lt (dict p.1) (dict p.2))
private def loArgs99 (a : BT) : List BT :=
  (loL93 (BT.toL a)).filterMap (fun t => match t with | BT.D 0 c => some c | _ => none)
private def loDomOK99 (p : BT × BT) : Bool :=
  (toList (loW89 (dict p.1))).all (fun q => TM.Term.lt q (collapse 0 (hiW89 (dict p.2))))
private def hiMonoOK99 (p : BT × BT) : Bool :=
  TM.Term.lt (collapse 0 (hiW89 (dict p.1))) (collapse 0 (hiW89 (dict p.2)))
private def resPairs99 (l : List BT) : List (BT × BT) :=
  (pairs99 l).filter (fun p => TM.Term.le (reg 1) (dict p.1) && TM.Term.le (reg 1) (dict p.2)
      && TM.Term.lt (hiW89 (dict p.1)) (hiW89 (dict p.2)))

/-! 母集団の形。**200 項のうち 120 項は `BT.isStd` が偽** — §96 の母集団と違い、
    壊れた項を濾していない。 -/
#guard (popRaw99.length, popGood99.length, popK99.length, popHi99.length, popNK99.length)
        == (200, 80, 67, 57, 13)
#guard (popRaw99.countP (fun x => btLe72 1 x), popRaw99.countP (fun x => !(BT.isStd x)),
        sRaw99.length, sGood99.length, sK99.length, sHi99.length)
        == (200, 120, 100, 40, 34, 29)

/-! **受領 1 (盲点の修理) — `dict` はこの母集団で衝突する。** 100 項の標本で
    **78 対**が相異なる項で同じ像を持つ。良い 40 項・`K` 標準な 34 項では **0**。
    §96 は「`dict` は 592 項で単射 (衝突 0)」としか言えず、そのせいで
    `CollapseLe0_96` と §79 の狭義の条項を**区別できなかった**。ここでは区別できる。 -/
#guard ((colls99 sRaw99).length, (colls99 sGood99).length, (colls99 sK99).length)
        == (78, 0, 0)

/-! **受領 2 (§99.2 が母集団に見える) — 狭義の破れ = 非狭義の破れ + 単射の破れ。**
    10000 対で `830 = 744 + 86`、1600 対で `67 = 61 + 6`。**差は形式ではない。**
    `K` の条件を課した 1156 対では三つとも 0。 -/
#guard ((pairs99 sRaw99).length, (ltFail99 sRaw99).length, (leFail99 sRaw99).length,
        (inj0Fail99 sRaw99).length) == (10000, 830, 744, 86)
#guard ((pairs99 sGood99).length, (ltFail99 sGood99).length, (leFail99 sGood99).length,
        (inj0Fail99 sGood99).length) == (1600, 67, 61, 6)
#guard ((pairs99 sK99).length, (ltFail99 sK99).length, (leFail99 sK99).length,
        (inj0Fail99 sK99).length) == (1156, 0, 0, 0)

/-! **受領 3 — 橋の側は §96 の再確認。** §93 の半橋は 200 項すべてで成り立ち、
    §96 の完全な橋は 19 項で破れる (すべて `BT.isStd` が偽の項)。 -/
#guard (popRaw99.countP (fun a => !(hiOK99 a)), popRaw99.countP (fun a => !(fullOK99 a)),
        popGood99.countP (fun a => !(hiOK99 a)), popGood99.countP (fun a => !(fullOK99 a)))
        == (0, 19, 0, 0)

/-! **受領 4 (測度) — 古い道は `size a` の予算を超え、§99 の道は超えない。**
    29 項から取った 406 の残余の対で、§93.6 が要る門の相手 `(c, hi b)` の
    **第二成分が `size a` を超えるのが 187 対 (46%)**、`b` での橋が要る記号数
    `size b` が `size a` を超えるのが **246 対 (61%)**。いっぽう §99 が回す相手
    `c ∈ G(a,0)` は **406 対すべてで `size c < size a`** (§93.1 の `size_GB93`、
    定理なので確認)。**測度 `size a` だけで閉じるのはこの内訳のとおり。** -/
#guard (hipairs99.length,
        hipairs99.countP (fun p => !(loArgs99 p.1).isEmpty),
        hipairs99.countP (fun p => BT.size (hiB93 p.2) > BT.size p.1),
        hipairs99.countP (fun p => BT.size p.2 > BT.size p.1),
        hipairs99.countP (fun p => (loArgs99 p.1).any (fun c => BT.size c ≥ BT.size p.1)),
        hipairs99.countP (fun p => (loArgs99 p.1).any (fun c => BT.size c > BT.size p.2)))
        == (406, 159, 187, 246, 0, 0)

/-! **受領 5 (負の対照) — 尾の条項は `K` の条件がなければ偽。** `K` 標準な 34 項の
    427 の残余の対では `LoDomPair91` も `HiMono89` も破れ 0。`K` の条件だけが偽の
    13 項では、9 の残余の対のうち **`LoDomPair91` が 4 対で破れ、`HiMono89` は
    0 対**。§99 が只にしたのは、空虚な条項ではない。 -/
#guard ((resPairs99 sK99).length, (resPairs99 sK99).countP (fun p => !(loDomOK99 p)),
        (resPairs99 sK99).countP (fun p => !(hiMonoOK99 p)),
        (resPairs99 popNK99).length, (resPairs99 popNK99).countP (fun p => !(loDomOK99 p)),
        (resPairs99 popNK99).countP (fun p => !(hiMonoOK99 p))) == (427, 0, 0, 9, 4, 0)

/-! **受領 6 — §99.1 の二つの補題は恒等写像の話ではない。** `hi (dict b) ≠ dict b` が
    良い 80 項のうち 40 項、`K` 標準な 67 項のうち 30 項。 -/
#guard (popGood99.countP (fun b => !(hiW89 (dict b) == dict b)),
        popK99.countP (fun b => !(hiW89 (dict b) == dict b)),
        popRaw99.countP (fun b => !(BT.toL b == BT.toL (hiB93 b)))) == (40, 30, 139)

end

/-! ## §98 THE HIGH SIDE — THE `Γ₀` TOWER IS AN INDUCTION, AND THE STEP THAT BUILDS IT IS ONE LEMMA

§94 split row 326's density gate in two at `ε₀` and §97 closed the low half: below `ε₀`
`dict` is ONTO, so the witness for a challenger is its own preimage.  §98 attacks the other
half, and the first thing to say is why the low half's route is closed here.  §97's engine is
`phiNF_zero_cn97` — `φ̄0` does not skip at a Cantor normal form — and §97.7 already pinned
where that stops: `phiNF 0 ε₀ = ε₀`, the skip happens EXACTLY at `ε₀`.  Above it the inverse
`invE97` answers with the wrong term (§97's `dictInv97_needs_ltE97`: `ω^(ε₀+1)` comes back as
`1`), and §94.6 showed the failure is not one term but a TOWER — `rawT94 n`, every rung in
𝔗(M), every rung with `dictInv = none`, every rung below `Γ₁`, and not one rung dominated by
§94.7's 495-term pool.  **Above `ε₀` the witness must be BUILT.**

§94.6 built four of them and checked them in the kernel.  **§98 turns that into an
induction, and the induction is one lemma about one step.**

  §98.1  **THE `BT` TOOLKIT.**  `ltL_append_r98` (the right list may grow), `btlt_hd98` /
         `btlt_arg98` / `btlt_sum_r98` / `btlt_cons_same98` (one component's comparison),
         and the two facts that carry the head condition: `gb1_nil98` (`Hd085 b ⟹ GB 1 b = []`)
         and `btlt_hd0_D1_98` (`Hd085 b ⟹ b < ψ₁(y)`).  Everything later about standardness
         is assembled from these; no `BT`-order theory beyond §83's `lt_trans83` is used.

  §98.2  **THE STEP OPERATOR, AND THE INVARIANT IT NEEDS.**
         `bStep98 x = ψ₀( Ω^Ω ⊕ ψ₁(ψ₁ x) )`.  This is §94.6's `bWitT94` with the `⊕ Ω`
         removed — simpler, and its value is one Veblen step rather than one-plus-one.  It is
         NOT closed on legal witnesses: `Inv98 x` adds one conjunct to "level ≤ 1, standard,
         head `D 0`", namely that every element of `GB 0 x` is below the new argument
         `Ω^Ω ⊕ Ω^(dict x)`.  `inv_bStep98` proves the invariant is preserved, and §98.8's
         `bStep98_needs_gb98` proves the conjunct is not decoration.

  §98.2b **THE CLIMB IS GENERAL.**  `bIter98 x n` iterates the step from ANY `x` with
         `Inv98 x`; `lt_x_bStep98` (the step strictly increases — again only the fourth
         conjunct is spent), `inv_bIter98`, `lt_bIter98_mono`, `legal_bIter98`.  The `Γ₀`
         tower `bTowG98` is `bIter98 (ψ₀(Ω^Ω))` (`bTowG98_eq98`).

  §98.3  **`ψ₁` TWICE, IN CLOSED FORM.**  `dict_D1x98 : dict (ψ₁ x) = ω^(Ω₁ ⊕ dict x)` and
         `dict_D1D1x98 : dict (ψ₁ψ₁ x) = ω^(ω^(Ω₁ ⊕ dict x))`, from §77.7's `collapse1_eq77`
         and §79.7's `le_reg1_collapse1_79`.  The hypotheses are packaged as `Good98 (dict x)`:
         `inT`, additively principal, `≠ 1`, a fixed point of `ω^·`, below `Ω₁`, and at or
         above `Γ₀`.

  §98.4  **THE MAIN LEMMA — THE FOLD, COMPUTED.**  `dict_bStep98` :

             dict (bStep98 x)  =  φ̄( dict x , Γ₀ ⊕ 1 ).

         The base-`Ω₁` decomposition of the argument is `[(Ω₁, 1), (dict x, 1)]`
         (`wcnf_cons_ge` twice), the fold fires its strongly critical branch once — that is
         where `Γ₀ = ψ_{Ω₁}(0)` comes from — and then takes one Veblen step.  Every
         hypothesis of `Good98` is spent somewhere, and §98.8 says where.

  §98.5  **THE TOWER IS AN INDUCTION.**  `good_bIter98` and `dict_bIter98` (and the `Γ₀`
         instances `good_bTowG98`, `dict_bTowG98`): for EVERY `n`, `bTowG98 n` is a legal
         witness and `dict (bTowG98 (n+1)) = φ̄(dict (bTowG98 n), Γ₀ ⊕ 1)`.  The order
         transfer runs forwards here — `lt_dict98`, §94.5's `btlt_of_lt94` reversed, from
         `bOnto85` and `DictLtA74`.

  §98.6  **THE RAW TOWER IS DOMINATED, AT EVERY RUNG.**  `lt_rawT_bTowG98` :
         `rawT94 n < dict (bTowG98 (n+1))`, by induction on the Veblen order alone;
         `lt_bTowG_Gam98` : every rung's value is below `Γ₁`, by a `BT.lt` computation and
         the transfer; `inT_rawT98` and `lt_rawT_Gam98`.  §94.6's four frozen `#guard`s are
         now theorems for all `n`.

  §98.7  **WHAT THAT BUYS THE CLAUSE.**  `denseHi_step98` : for any `x` with `Inv98 x` and
         `Good98 (dict x)`, any challenger at or below `φ̄(dict x, 0)` — the shape §85.7 and
         §94.6 proved is MISSING from `dict`'s image — is witnessed by `bStep98 x` below any
         image point above it.  `denseHi_iter98` says the same at every rung of a climb, and
         `denseHi_rawT98` / `denseHi_rawT_vOf98` are the `Γ₀`-tower instance: a target at or
         above `Γ₁` and a challenger at or below `rawT94 n` need no hypothesis beyond the two
         row 326 already carries.

  §98.8  **THE ONE CLAUSE THAT REMAINS BELOW `Γ₁`, NAMED — AND FOUR REFUTATIONS.**
         `CofGam1_98` : every term of 𝔗(M) in `[Γ₀, Γ₁)` is at or below some rung of the raw
         tower.  It is a HYPOTHESIS and is marked as such.  `denseHi_below_Gam1_98` proves
         that with it, EVERY challenger below `Γ₁` is witnessed at every target at or above
         `Γ₁`.  The four refutations pin the rest: `bStep98_needs_gb98` (a legal `x` whose
         step is not standard), `dict_bStep98_needs_G098` (at `ε₀` the value is `φ̄(ε₀, Γ₀)` —
         `phiNFsucc` fires and the `⊕ 1` is lost), `dict_bStep98_needs_fp98` (`Γ₀ ⊕ Γ₀` is
         above `Γ₀` but not additively principal, and the exponent that reaches the fold is
         `ω^(Γ₀ ⊕ Γ₀)`), and `btLe0_bTowG98` — **the construction leaves level 0 at every
         rung.**  That is the honest counterpart of §97's `btLe0_invE97`: above `Γ₀` staying
         at level 0 is impossible, and level 1 is exactly where it stops.  §85.6 refutes the
         clause at level 2 and nothing here goes there.

WHAT IS **NOT** CLAIMED.  `DictDenseHi94` is NOT proved, `DictDense85` is NOT proved and
`CofDenseS1` is NOT closed.  On the cofinality side row 326 still waits on `DictDenseHi94`
and on nothing else (§97.6), and §98 does not change that.  `CofGam1_98` is an unproved
hypothesis, introduced by name and used only where it is written.  `PsiIdxOKStd172` and
`DictLtA74` are used, not proved, and they are the two clauses row 326 already carries.

**Where §98 stopped, precisely.**  Two gaps, and they are different.  (i) Below `Γ₁` the
clause is now ONE 𝔗(M)-side cofinality statement, `CofGam1_98` — the `Γ₁` analogue of §9's
`cof_eps0`, whose sequence is the raw `φ̄`-tower `rawT94` and whose proof this repository does
not have (`Evidence/WF.lean` §15's combinators cover `φ̄ a ·` in the SECOND argument,
`lim_clauses_phi_arg`; the tower climbs in the FIRST, which is `TM/FS.lean`'s `iterGamma`
clause and has no Evidence-level cofinality theorem).  (ii) At or above `Γ₁` nothing is
proved at all: `denseHi_step98` climbs from a given `x`, but choosing that `x` for an
arbitrary challenger is the general problem, and it needs the `Γ₀`-analogue of §97 — `dict`
onto the Veblen fragment below `Γ₀`, then onto the `ψ_{Ω₁}` fragment above it.  §98 does not
attempt either.  What §98 does remove is the doubt §94 recorded about its own construction:
the family is no longer "a construction with a frozen kernel check on four rungs".

WHAT THE MEASUREMENT SAYS (§98.9 gives the construction).  One population, 120 terms, built
so that BOTH hypotheses are visible and NEITHER is filtered out — §93's bridge held 292/292
where its own hypothesis failed, and that is the failure mode this design avoids.  19 of the
120 are not even legal witnesses, because the step operator does not preserve legality.

  * **The structural hypothesis is exactly right — 495 of 495.**  On the whole of §94.7's
    pool, `bStep98 x` is a legal witness EXACTLY when `Inv98`'s fourth conjunct holds: 324
    pass, 171 fail, 0 disagreements.
  * **The value hypothesis is exactly right — 120 of 120.**  `dict (bStep98 x) = φ̄(dict x,
    Γ₀ ⊕ 1)` holds EXACTLY when `Good98 (dict x)`: 65 hits, 55 misses, 0 disagreements.
  * **Not carried by a trivial conjunct.**  Drop `Γ₀ ≤ ·` and the predicate would call 70,
    not 65.  Each conjunct is visible: 49 terms are not additively principal, 50 are not
    fixed points of `ω^·`, 36 are below `Γ₀`, 1 is `1` itself.
  * **The tower, computed.**  Six rungs: all legal, all with the closed form, all dominating
    `rawT94 n` and all below `Γ₁` — and `btLe72 0` is FALSE at every rung.
  * **The negative, and it is §94.7's.**  0 of the 495 pool values land in `[rawT94 n, Γ₁)`,
    at any rung; the raw tower is `inT`, has `dictInv = none` and is below `Γ₁` at 8 rungs,
    and is NOT `CN` at any of them — §97's low side does not reach it and does not claim to.
  * **Three BUILT counterexamples**, one per hypothesis: `xBad98` (legal, step not standard),
    `xEps98` (value `φ̄(ε₀, Γ₀)`, the `⊕ 1` lost), `xSum98` (above `Γ₀`, not principal).
    §94.6's naive `ψ₀(Ω^(Γ₀+1))` is re-recorded as a theorem: right level, right head, not
    standard. -/


/-! ### §98.1 BT 側の道具 -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg)
open TM TM.Term

/-- `ltL` は右の列を伸ばしても真のまま。 -/
theorem ltL_append_r98 : ∀ (f : Nat) (l1 l2 l3 : List BT),
    BT.ltL f l1 l2 = true → BT.ltL f l1 (l2 ++ l3) = true := by
  intro f
  induction f with
  | zero => intro l1 l2 l3 h; rw [ltL_zero93] at h; exact Bool.noConfusion h
  | succ f ih =>
    intro l1 l2 l3 h
    cases l2 with
    | nil =>
      cases l1 with
      | nil => rw [ltL_nil_nil93] at h; exact Bool.noConfusion h
      | cons p ps => rw [ltL_cons_nil93] at h; exact Bool.noConfusion h
    | cons q qs =>
      cases l1 with
      | nil => exact ltL_nil_cons93 _ _ _
      | cons p ps =>
        cases p with
        | zero => exact absurd h (by cases q <;> exact Bool.noConfusion)
        | sum s t => exact absurd h (by cases q <;> exact Bool.noConfusion)
        | D u a =>
          cases q with
          | zero => exact absurd h (by exact Bool.noConfusion)
          | sum s t => exact absurd h (by exact Bool.noConfusion)
          | D v b =>
            rw [ltL_DD93] at h
            rw [List.cons_append, ltL_DD93]
            by_cases h1 : u < v
            · rw [if_pos h1]
            · rw [if_neg h1] at h ⊢
              by_cases h2 : v < u
              · rw [if_pos h2] at h; exact Bool.noConfusion h
              · rw [if_neg h2] at h ⊢
                by_cases h3 : (a == b) = true
                · rw [if_pos h3] at h ⊢; exact ih ps qs l3 h
                · rw [if_neg h3] at h ⊢; exact h

/-- 成分ひとつぶんの `BT.lt` — 添字で決まる場合。 -/
theorem btlt_hd98 {u v : Nat} (a b : BT) (h : u < v) : BT.lt (BT.D u a) (BT.D v b) = true := by
  show BT.ltL (BT.size (BT.D u a) + BT.size (BT.D v b) + 2) [BT.D u a] [BT.D v b] = true
  rw [show BT.size (BT.D u a) + BT.size (BT.D v b) + 2
      = (BT.size (BT.D u a) + BT.size (BT.D v b) + 1) + 1 from rfl, ltL_DD93, if_pos h]

/-- 成分ひとつぶんの `BT.lt` — 引数で決まる場合。 -/
theorem btlt_arg98 {u : Nat} {a b : BT} (hne : (a == b) = false) (h : BT.lt a b = true) :
    BT.lt (BT.D u a) (BT.D u b) = true := by
  show BT.ltL (BT.size (BT.D u a) + BT.size (BT.D u b) + 2) [BT.D u a] [BT.D u b] = true
  rw [show BT.size (BT.D u a) + BT.size (BT.D u b) + 2
      = (BT.size (BT.D u a) + BT.size (BT.D u b) + 1) + 1 from rfl, ltL_DD93,
    if_neg (by omega), if_neg (by omega),
    if_neg (by rw [hne]; exact Bool.noConfusion)]
  refine ltL_fuel93 (BT.size a + BT.size b + 2) _ _ _ ?_ h
  show BT.size a + BT.size b + 2 ≤ (1 + BT.size a) + (1 + BT.size b) + 1
  omega

/-- 右側に和を足しても `BT.lt` は保たれる。 -/
theorem btlt_sum_r98 {e p q : BT} (h : BT.lt e p = true) : BT.lt e (BT.sum p q) = true := by
  show BT.ltL (BT.size e + BT.size (BT.sum p q) + 2) (BT.toL e) (BT.toL p ++ BT.toL q) = true
  refine ltL_fuel93 (BT.size e + BT.size p + 2) _ _ _ ?_
    (ltL_append_r98 _ _ _ _ h)
  show BT.size e + BT.size p + 2 ≤ BT.size e + (1 + BT.size p + BT.size q) + 2
  omega

/-- 成分がすべて `D 0` なら `GB 1` は空。 -/
theorem gb1_nil98 : ∀ (x : BT), Hd085 x → BT.GB 1 x = []
  | .zero, _ => rfl
  | .D u c, h => by
      rw [hd085_D94 h]; rfl
  | .sum a b, h => by
      obtain ⟨ha, hb⟩ := hd085_sum94 h
      show BT.GB 1 a ++ BT.GB 1 b = []
      rw [gb1_nil98 a ha, gb1_nil98 b hb]; rfl

/-- 成分がすべて `D 0` なら段 1 の成分より下。 -/
theorem btlt_hd0_D1_98 {x : BT} (h : Hd085 x) (y : BT) : BT.lt x (BT.D 1 y) = true := by
  show BT.ltL (BT.size x + BT.size (BT.D 1 y) + 2) x.toL [BT.D 1 y] = true
  cases hx : x.toL with
  | nil => exact ltL_nil_cons93 _ _ _
  | cons z zs =>
      obtain ⟨c, hc⟩ := h z (by rw [hx]; exact List.Mem.head _)
      rw [hc]
      rw [show BT.size x + BT.size (BT.D 1 y) + 2
          = (BT.size x + BT.size (BT.D 1 y) + 1) + 1 from rfl, ltL_DD93, if_pos (by omega)]

/-- 成分がすべて `D 0` なら段 1 の成分ではない。 -/
theorem ne_D1_hd098 {x : BT} (h : Hd085 x) (y : BT) : ¬ (x = BT.D 1 y) := by
  intro hx
  obtain ⟨c, hc⟩ := h (BT.D 1 y) (by rw [hx]; exact List.Mem.head _)
  injection hc with h1 _
  exact Nat.noConfusion h1

/-- `BT.lt` から相異なることを取り出す。 -/
theorem bt_ne_of_lt98 {a b : BT} (h : BT.lt a b = true) : (a == b) = false := by
  cases hab : (a == b) with
  | false => rfl
  | true =>
      exfalso
      rw [bt_beq_eq77 hab] at h
      rw [lt_asymm74 h] at h
      exact Bool.noConfusion h

theorem btlt_zero_D98 (u : Nat) (a : BT) : BT.lt BT.zero (BT.D u a) = true := by
  show BT.ltL (BT.size BT.zero + BT.size (BT.D u a) + 2) [] [BT.D u a] = true
  exact ltL_nil_cons93 _ _ _

/-- 先頭が同じ和は尾で決まる。 -/
theorem btlt_cons_same98 {u : Nat} {a q q' : BT} (h : BT.lt q q' = true) :
    BT.lt (BT.sum (BT.D u a) q) (BT.sum (BT.D u a) q') = true := by
  show BT.ltL (BT.size (BT.sum (BT.D u a) q) + BT.size (BT.sum (BT.D u a) q') + 2)
      (BT.D u a :: q.toL) (BT.D u a :: q'.toL) = true
  rw [show BT.size (BT.sum (BT.D u a) q) + BT.size (BT.sum (BT.D u a) q') + 2
      = (BT.size (BT.sum (BT.D u a) q) + BT.size (BT.sum (BT.D u a) q') + 1) + 1 from rfl,
    ltL_DD93, if_neg (by omega), if_neg (by omega), if_pos (bt_beq_refl a)]
  refine ltL_fuel93 (BT.size q + BT.size q' + 2) _ _ _ ?_ h
  show BT.size q + BT.size q' + 2
      ≤ (1 + (1 + BT.size a) + BT.size q) + (1 + (1 + BT.size a) + BT.size q') + 1
  omega

/-! ### §98.2 段を一つ上げる作用素 -/

/-- 一段上げる作用素の引数 — `Ω^Ω ⊕ ψ₁(ψ₁ x)`。 -/
def bArg98 (x : BT) : BT := BT.sum bOO94 (BT.D 1 (BT.D 1 x))

/-- **一段上げる作用素。** `ψ₀(Ω^Ω ⊕ Ω^(dict x))`。 -/
def bStep98 (x : BT) : BT := BT.D 0 (bArg98 x)

/-- `Γ₀` の上の証人の族 — §94.6 の `bWitT94` を簡単にしたもの。 -/
def bTowG98 : Nat → BT
  | 0 => BT.D 0 bOO94
  | n + 1 => bStep98 (bTowG98 n)

theorem gb0_bArg98 (x : BT) : BT.GB 0 (bArg98 x) =
    [BT.D 1 (BT.D 1 BT.zero), BT.D 1 BT.zero, BT.zero, BT.D 1 x, x] ++ BT.GB 0 x := rfl

theorem gb0_bStep98 (x : BT) :
    BT.GB 0 (bStep98 x) = bArg98 x :: BT.GB 0 (bArg98 x) := rfl

/-- `bOO94` より下にいる 5 つ。 -/
theorem lt_bOO98 {x : BT} (hd : Hd085 x) :
    BT.lt (BT.D 1 (BT.D 1 BT.zero)) bOO94 = true ∧ BT.lt (BT.D 1 BT.zero) bOO94 = true ∧
    BT.lt BT.zero bOO94 = true ∧ BT.lt (BT.D 1 x) bOO94 = true ∧ BT.lt x bOO94 = true := by
  have hx : BT.lt x (BT.D 1 (BT.D 1 BT.zero)) = true := btlt_hd0_D1_98 hd _
  refine ⟨?_, ?_, btlt_zero_D98 _ _, ?_, btlt_hd0_D1_98 hd _⟩
  · exact btlt_arg98 (by rfl) (btlt_arg98 (by rfl) (btlt_zero_D98 1 BT.zero))
  · exact btlt_arg98 (by rfl) (btlt_zero_D98 1 (BT.D 1 BT.zero))
  · exact btlt_arg98 (bt_beq_false _ _ (ne_D1_hd098 hd _)) hx

/-- 段 1 の成分は `bOO94` より下。 -/
theorem lt_D1D1_bOO98 {x : BT} (hd : Hd085 x) :
    BT.lt (BT.D 1 (BT.D 1 x)) bOO94 = true :=
  btlt_arg98 (bt_beq_false _ _ (fun h => by
    injection h with _ h2; exact ne_D1_hd098 hd _ h2))
    (btlt_arg98 (bt_beq_false _ _ (ne_D1_hd098 hd _)) (btlt_hd0_D1_98 hd _))

/-- **引数は標準。** -/
theorem isStd_bArg98 {x : BT} (hd : Hd085 x) (hs : BT.isStd x = true) :
    BT.isStd (bArg98 x) = true := by
  have h1 : BT.isStd (BT.D 1 x) = true := by
    show (BT.isStd x && (BT.GB 1 x).all (fun e => BT.lt e x)) = true
    rw [hs, gb1_nil98 x hd]; rfl
  have h2 : BT.isStd (BT.D 1 (BT.D 1 x)) = true := by
    show (BT.isStd (BT.D 1 x) && (BT.GB 1 (BT.D 1 x)).all (fun e => BT.lt e (BT.D 1 x))) = true
    rw [h1, show BT.GB 1 (BT.D 1 x) = x :: BT.GB 1 x from rfl, gb1_nil98 x hd]
    show (BT.lt x (BT.D 1 x) && true) = true
    rw [btlt_hd0_D1_98 hd x]; rfl
  show (BT.isP bOO94 && BT.isStd bOO94 && BT.isStd (BT.D 1 (BT.D 1 x)) &&
    (BT.isP (BT.D 1 (BT.D 1 x)) && BT.le (BT.D 1 (BT.D 1 x)) bOO94)) = true
  rw [show BT.isP bOO94 = true from rfl, show BT.isStd bOO94 = true from rfl, h2,
    show BT.isP (BT.D 1 (BT.D 1 x)) = true from rfl,
    show BT.le (BT.D 1 (BT.D 1 x)) bOO94
      = ((BT.D 1 (BT.D 1 x) == bOO94) || BT.lt (BT.D 1 (BT.D 1 x)) bOO94) from rfl,
    lt_D1D1_bOO98 hd, Bool.or_true]
  rfl

theorem btlt_self_sum98 {u : Nat} {a : BT} (v : Nat) (b : BT) :
    BT.lt (BT.D u a) (BT.sum (BT.D u a) (BT.D v b)) = true := by
  show BT.ltL (BT.size (BT.D u a) + BT.size (BT.sum (BT.D u a) (BT.D v b)) + 2)
      [BT.D u a] (BT.D u a :: [BT.D v b]) = true
  rw [show BT.size (BT.D u a) + BT.size (BT.sum (BT.D u a) (BT.D v b)) + 2
      = (BT.size (BT.D u a) + BT.size (BT.sum (BT.D u a) (BT.D v b)) + 1) + 1 from rfl,
    ltL_DD93, if_neg (by omega), if_neg (by omega), if_pos (bt_beq_refl a)]
  exact ltL_nil_cons93 _ _ _

/-- 引数どうしの順序は `x` の順序で決まる。 -/
theorem lt_bArg98 {x y : BT} (h : BT.lt x y = true) : BT.lt (bArg98 x) (bArg98 y) = true :=
  btlt_cons_same98 (btlt_arg98 (bt_beq_false _ _ (fun hc => by
      injection hc with _ h2
      rw [h2, lt_asymm74 h] at h; exact Bool.noConfusion h))
    (btlt_arg98 (bt_ne_of_lt98 h) h))

/-- **不変量。** 正しい証人であることに、係数集合が次の引数より下という一条を足したもの。 -/
def Inv98 (x : BT) : Prop :=
  btLe72 1 x = true ∧ BT.isStd x = true ∧ Hd085 x ∧
    (∀ e ∈ BT.GB 0 x, BT.lt e (bArg98 x))

theorem hd0_bStep98 (x : BT) : Hd085 (bStep98 x) := by
  intro z hz
  exact ⟨bArg98 x, List.mem_singleton.mp hz⟩

theorem btLe_bStep98 {x : BT} (h : btLe72 1 x = true) : btLe72 1 (bStep98 x) = true := by
  show (decide (0 ≤ 1) && (btLe72 1 bOO94 && (decide (1 ≤ 1) &&
    (decide (1 ≤ 1) && btLe72 1 x)))) = true
  rw [h]; rfl

/-- 5 つの成分はどれも次の引数より下。 -/
theorem lt_five_bArg98 {x y : BT} (hd : Hd085 x) :
    ∀ e ∈ [BT.D 1 (BT.D 1 BT.zero), BT.D 1 BT.zero, BT.zero, BT.D 1 x, x],
      BT.lt e (bArg98 y) = true := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := lt_bOO98 hd
  intro e he
  rcases List.mem_cons.mp he with h | he
  · rw [h]; exact btlt_sum_r98 h1
  rcases List.mem_cons.mp he with h | he
  · rw [h]; exact btlt_sum_r98 h2
  rcases List.mem_cons.mp he with h | he
  · rw [h]; exact btlt_sum_r98 h3
  rcases List.mem_cons.mp he with h | he
  · rw [h]; exact btlt_sum_r98 h4
  rcases List.mem_cons.mp he with h | he
  · rw [h]; exact btlt_sum_r98 h5
  · cases he

/-- **一段上げた項は標準。** 効いているのは不変量の 4 番目の条だけ。 -/
theorem isStd_bStep98 {x : BT} (hd : Hd085 x) (hs : BT.isStd x = true)
    (hgb : ∀ e ∈ BT.GB 0 x, BT.lt e (bArg98 x)) : BT.isStd (bStep98 x) = true := by
  show (BT.isStd (bArg98 x) &&
    (BT.GB 0 (bArg98 x)).all (fun e => BT.lt e (bArg98 x))) = true
  rw [isStd_bArg98 hd hs, gb0_bArg98 x]
  show (List.all _ _) = true
  rw [List.all_eq_true]
  intro e he
  rcases List.mem_append.mp he with h1 | h1
  · exact lt_five_bArg98 (y := x) hd e h1
  · exact hgb e h1

/-- **一段上げても不変量は保たれる。** -/
theorem inv_bStep98 {x : BT} (H : Inv98 x) (hlt : BT.lt x (bStep98 x) = true) :
    Inv98 (bStep98 x) := by
  obtain ⟨hb, hs, hd, hgb⟩ := H
  have hstd : BT.isStd (bStep98 x) = true := isStd_bStep98 hd hs hgb
  refine ⟨btLe_bStep98 hb, hstd, hd0_bStep98 x, ?_⟩
  have hA : BT.lt (bArg98 x) (bArg98 (bStep98 x)) = true := lt_bArg98 hlt
  intro e he
  rcases List.mem_cons.mp (by rw [← gb0_bStep98 x]; exact he) with h1 | h1
  · rw [h1]; exact hA
  · rw [gb0_bArg98 x] at h1
    rcases List.mem_append.mp h1 with h2 | h2
    · exact lt_five_bArg98 (y := bStep98 x) hd e h2
    · exact lt_trans83 (hgb e h2) hA

/-- 塔は `BT.lt` で増える。 -/
theorem lt_bTowG98 : ∀ n, BT.lt (bTowG98 n) (bTowG98 (n + 1)) = true
  | 0 => by
      show BT.lt (BT.D 0 bOO94) (BT.D 0 (bArg98 (BT.D 0 bOO94))) = true
      exact btlt_arg98 (by rfl) (btlt_self_sum98 1 (BT.D 1 (BT.D 0 bOO94)))
  | n + 1 => by
      show BT.lt (BT.D 0 (bArg98 (bTowG98 n))) (BT.D 0 (bArg98 (bTowG98 (n + 1)))) = true
      have h := lt_bArg98 (lt_bTowG98 n)
      exact btlt_arg98 (bt_ne_of_lt98 h) h

/-- **塔の各段は不変量を満たす。** -/
theorem inv_bTowG98 : ∀ n, Inv98 (bTowG98 n)
  | 0 => by
      refine ⟨rfl, rfl, ?_, ?_⟩
      · intro z hz; exact ⟨bOO94, List.mem_singleton.mp hz⟩
      · intro e he
        rcases List.mem_cons.mp (show e ∈ bOO94 :: BT.GB 0 bOO94 from he) with h1 | h1
        · rw [h1]; exact btlt_self_sum98 1 (BT.D 1 (BT.D 0 bOO94))
        · rcases List.mem_cons.mp (show e ∈ BT.D 1 (BT.D 1 BT.zero) ::
              [BT.D 1 BT.zero, BT.zero] from h1) with h2 | h2
          · rw [h2]
            exact btlt_sum_r98 (btlt_arg98 (by rfl)
              (btlt_arg98 (by rfl) (btlt_zero_D98 1 BT.zero)))
          · rcases List.mem_cons.mp h2 with h3 | h3
            · rw [h3]
              exact btlt_sum_r98 (btlt_arg98 (by rfl) (btlt_zero_D98 1 (BT.D 1 BT.zero)))
            · rw [List.mem_singleton.mp h3]; exact btlt_sum_r98 (btlt_zero_D98 _ _)
  | n + 1 => inv_bStep98 (inv_bTowG98 n) (lt_bTowG98 n)

/-- **塔の各段は正しい証人である。** -/
theorem legal_bTowG98 (n : Nat) :
    btLe72 1 (bTowG98 n) = true ∧ BT.isStd (bTowG98 n) = true ∧ Hd085 (bTowG98 n) :=
  ⟨(inv_bTowG98 n).1, (inv_bTowG98 n).2.1, (inv_bTowG98 n).2.2.1⟩

end

/-! ### §98.2b どんな出発点からでも登れる -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg)
open TM TM.Term

theorem size_mem_toL98 : ∀ (x z : BT), z ∈ x.toL → BT.size z ≤ BT.size x
  | .zero, _, hz => by cases hz
  | .D u a, z, hz => by
      rw [List.mem_singleton.mp (show z ∈ [BT.D u a] from hz)]
      exact Nat.le_refl _
  | .sum p q, z, hz => by
      rcases List.mem_append.mp (show z ∈ p.toL ++ q.toL from hz) with h1 | h1
      · have := size_mem_toL98 p z h1
        show BT.size z ≤ 1 + BT.size p + BT.size q
        omega
      · have := size_mem_toL98 q z h1
        show BT.size z ≤ 1 + BT.size p + BT.size q
        omega

/-- 成分がすべて `D 0` なら、成分の引数は係数集合の元。 -/
theorem head_gb98 : ∀ (x : BT), Hd085 x → ∀ z ∈ x.toL, ∃ c, z = BT.D 0 c ∧ c ∈ BT.GB 0 x
  | .zero, _, _, hz => by cases hz
  | .D u a, h, z, hz => by
      have hu := hd085_D94 h
      subst hu
      exact ⟨a, List.mem_singleton.mp (show z ∈ [BT.D 0 a] from hz), List.Mem.head _⟩
  | .sum p q, h, z, hz => by
      obtain ⟨hp, hq⟩ := hd085_sum94 h
      rcases List.mem_append.mp (show z ∈ p.toL ++ q.toL from hz) with h1 | h1
      · obtain ⟨c, hc, hm⟩ := head_gb98 p hp z h1
        exact ⟨c, hc, List.mem_append_left _ hm⟩
      · obtain ⟨c, hc, hm⟩ := head_gb98 q hq z h1
        exact ⟨c, hc, List.mem_append_right _ hm⟩

/-- **一段上げると真に上がる。** 効いているのは不変量の 4 番目の条だけ。 -/
theorem lt_x_bStep98 {x : BT} (hd : Hd085 x)
    (hgb : ∀ e ∈ BT.GB 0 x, BT.lt e (bArg98 x)) : BT.lt x (bStep98 x) = true := by
  show BT.ltL (BT.size x + BT.size (BT.D 0 (bArg98 x)) + 2) x.toL [BT.D 0 (bArg98 x)] = true
  cases hx : x.toL with
  | nil => exact ltL_nil_cons93 _ _ _
  | cons z zs =>
      obtain ⟨c, hzc, hcm⟩ := head_gb98 x hd z (by rw [hx]; exact List.Mem.head _)
      have hsz : BT.size z ≤ BT.size x := size_mem_toL98 x z (by rw [hx]; exact List.Mem.head _)
      rw [hzc] at hsz
      have hlt := hgb c hcm
      rw [hzc,
        show BT.size x + BT.size (BT.D 0 (bArg98 x)) + 2
          = (BT.size x + BT.size (BT.D 0 (bArg98 x)) + 1) + 1 from rfl,
        ltL_DD93, if_neg (by omega), if_neg (by omega),
        if_neg (by rw [bt_ne_of_lt98 hlt]; exact Bool.noConfusion)]
      refine ltL_fuel93 (BT.size c + BT.size (bArg98 x) + 2) _ _ _ ?_ hlt
      have h1 : BT.size (BT.D 0 c) = 1 + BT.size c := rfl
      have h2 : BT.size (BT.D 0 (bArg98 x)) = 1 + BT.size (bArg98 x) := rfl
      omega

/-- 出発点を選べる塔。 -/
def bIter98 (x : BT) : Nat → BT
  | 0 => x
  | n + 1 => bStep98 (bIter98 x n)

theorem inv_bIter98 {x : BT} (H : Inv98 x) : ∀ n, Inv98 (bIter98 x n)
  | 0 => H
  | n + 1 => by
      have hI := inv_bIter98 H n
      exact inv_bStep98 hI (lt_x_bStep98 hI.2.2.1 hI.2.2.2)

theorem lt_bIter98 {x : BT} (H : Inv98 x) (n : Nat) :
    BT.lt (bIter98 x n) (bIter98 x (n + 1)) = true :=
  lt_x_bStep98 (inv_bIter98 H n).2.2.1 (inv_bIter98 H n).2.2.2

theorem lt_bIter98_mono {x : BT} (H : Inv98 x) :
    ∀ (k n : Nat), k < n → BT.lt (bIter98 x k) (bIter98 x n) = true
  | k, 0, h => absurd h (by omega)
  | k, n + 1, h => by
      rcases Nat.lt_or_ge k n with h1 | h1
      · exact lt_trans83 (lt_bIter98_mono H k n h1) (lt_bIter98 H n)
      · have hkn : k = n := by omega
        rw [hkn]; exact lt_bIter98 H n

theorem legal_bIter98 {x : BT} (H : Inv98 x) (n : Nat) :
    btLe72 1 (bIter98 x n) = true ∧ BT.isStd (bIter98 x n) = true ∧ Hd085 (bIter98 x n) :=
  ⟨(inv_bIter98 H n).1, (inv_bIter98 H n).2.1, (inv_bIter98 H n).2.2.1⟩

end

/-! ### §98.3 値 — `ψ₁` を二度重ねたところまで -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- `Γ₀ = ψ_Ω(0)` の上にいて、`Ω₁` より下にいる `ω` 冪の不動点。 -/
def Good98 (X : Term) : Prop :=
  inT X = true ∧ X.isAP = true ∧ (X == TM.Term.one) = false ∧ omegaNF X = X ∧
    lt X (reg 1) = true ∧ le G094 X = true

theorem lt_W_reg2_98 : lt (reg 1) (reg 2) = true := by decide

theorem ltM_W98 : lt (reg 1) M = true := ltM_W79

theorem good_ltM98 {X : Term} (h : Good98 X) : lt X M = true :=
  lt_trans_inT h.1 inT_W79 inT_M h.2.2.2.2.1 ltM_W98

theorem good_reg2_98 {X : Term} (h : Good98 X) : lt X (reg 2) = true :=
  lt_trans_inT h.1 inT_W79 (inT_reg 2) h.2.2.2.2.1 lt_W_reg2_98

theorem good_toList98 {X : Term} (h : Good98 X) : toList X = [X] := toList_isAP81 h.2.1

/-- `Ω₁ ⊕ X` は正規和そのもの。 -/
theorem plus_W_98 {X : Term} (h : Good98 X) : plus (reg 1) X = add (reg 1) X := by
  show (match toList X with
        | [] => reg 1
        | b1 :: _ => ofList ((toList (reg 1)).filter (fun a => le b1 a) ++ toList X)) = _
  rw [good_toList98 h]
  show ofList ((toList (reg 1)).filter (fun a => le X a) ++ [X]) = add (reg 1) X
  rw [show toList (reg 1) = [reg 1] from rfl,
    List.filter_cons_of_pos (by rw [le_of_lt h.2.2.2.2.1])]
  rfl

theorem inT_addWX98 {X : Term} (h : Good98 X) : inT (add (reg 1) X) = true := by
  rw [← plus_W_98 h]; exact inT_plus inT_W79 h.1

theorem ltM_addWX98 {X : Term} (h : Good98 X) : lt (add (reg 1) X) M = true := by
  rw [show add (reg 1) X = ofList [reg 1, X] from rfl]
  refine lt_ofList_M _ ?_
  intro z hz
  rcases List.mem_cons.mp hz with h1 | h1
  · rw [h1]; exact ltM_W98
  · rw [List.mem_singleton.mp h1]; exact good_ltM98 h

theorem splitFin_addWX98 {X : Term} (h : Good98 X) :
    splitFin (add (reg 1) X) = (add (reg 1) X, 0) := by
  unfold splitFin
  rw [show toList (add (reg 1) X) = [reg 1, X] from by
        show reg 1 :: toList X = _; rw [good_toList98 h]]
  show (ofList (List.take (2 - (List.takeWhile (fun x => x == TM.Term.one)
      ([reg 1, X].reverse)).length) [reg 1, X]),
    (List.takeWhile (fun x => x == TM.Term.one) ([reg 1, X].reverse)).length)
      = (add (reg 1) X, 0)
  rw [show ([reg 1, X].reverse) = [X, reg 1] from rfl,
    show (List.takeWhile (fun x => x == TM.Term.one) [X, reg 1]) = [] from by
      show (match (X == TM.Term.one) with
            | true => X :: List.takeWhile (fun x => x == TM.Term.one) [reg 1]
            | false => []) = []
      rw [h.2.2.1]]
  rfl

/-- **`ω^(Ω₁ ⊕ X)` は生の `φ̄0`。** -/
theorem omegaNF_addWX98 {X : Term} (h : Good98 X) :
    omegaNF (add (reg 1) X) = phi zero (add (reg 1) X) := by
  rw [omegaNF_of_le_M (lt_asymm_inT (inT_addWX98 h) inT_M (ltM_addWX98 h))]
  unfold phiNF
  rw [show ((add (reg 1) X).isSC && lt zero (add (reg 1) X)) = false from by
    rw [show (add (reg 1) X).isSC = false from rfl]; rfl]
  show phiNFsucc zero (add (reg 1) X) = phi zero (add (reg 1) X)
  unfold phiNFsucc
  rw [splitFin_addWX98 h]
  show phiNFdefault zero (add (reg 1) X) = phi zero (add (reg 1) X)
  exact phiNFdefault_zero94 _

/-- `ψ₁` を一度当てた形。 -/
def P98 (X : Term) : Term := phi zero (add (reg 1) X)
/-- `ψ₁` を二度当てた形。 -/
def Q98 (X : Term) : Term := phi zero (P98 X)

theorem collapse1_good98 {X : Term} (h : Good98 X) : collapse 1 X = P98 X := by
  rw [collapse1_eq77 X h.1 (by
      intro p hp
      rw [good_toList98 h] at hp
      rw [List.mem_singleton.mp hp]
      exact good_reg2_98 h),
    plus_W_98 h]
  exact omegaNF_addWX98 h

theorem isStd_D1_98 {x : BT} (hd : Hd085 x) (hs : BT.isStd x = true) :
    BT.isStd (BT.D 1 x) = true := by
  show (BT.isStd x && (BT.GB 1 x).all (fun e => BT.lt e x)) = true
  rw [hs, gb1_nil98 x hd]; rfl

theorem btLe_D1_98 {x : BT} (hb : btLe72 1 x = true) : btLe72 1 (BT.D 1 x) = true := by
  show (decide (1 ≤ 1) && btLe72 1 x) = true
  rw [hb]; rfl

/-- `ψ₁` を一度。 -/
theorem dict_D1x98 (Hp : PsiIdxOKStd172) {x : BT} (hb : btLe72 1 x = true)
    (hs : BT.isStd x = true) (hg : Good98 (dict x)) : dict (BT.D 1 x) = P98 (dict x) := by
  rw [dict_D1_eq77 Hp x hb hs, plus_W_98 hg]
  exact omegaNF_addWX98 hg

/-- `ψ₁` を二度。 -/
theorem dict_D1D1x98 (Hp : PsiIdxOKStd172) {x : BT} (hb : btLe72 1 x = true)
    (hs : BT.isStd x = true) (hd : Hd085 x) (hg : Good98 (dict x)) :
    dict (BT.D 1 (BT.D 1 x)) = Q98 (dict x) := by
  have hb1 := btLe_D1_98 hb
  have hs1 := isStd_D1_98 hd hs
  have hiP : inT (P98 (dict x)) = true := by
    rw [← dict_D1x98 Hp hb hs hg]
    exact (inT_dict_of_std172 Hp (BT.D 1 x) hb1 hs1).1
  have hlePW : le (reg 1) (P98 (dict x)) = true := by
    rw [← collapse1_good98 hg]
    refine le_reg1_collapse1_79 (dict x) hg.1 ?_
    intro p hp
    rw [good_toList98 hg] at hp
    rw [List.mem_singleton.mp hp]
    exact good_reg2_98 hg
  have hltPW : lt (P98 (dict x)) (reg 1) = false := by
    rcases (Bool.or_eq_true _ _).mp hlePW with h1 | h1
    · rw [← eq_of_beq h1]; exact lt_irrefl _
    · exact lt_asymm_inT inT_W79 hiP h1
  have hplus : plus (reg 1) (P98 (dict x)) = P98 (dict x) := by
    show (match toList (P98 (dict x)) with
          | [] => reg 1
          | b1 :: _ => ofList ((toList (reg 1)).filter (fun a => le b1 a) ++
              toList (P98 (dict x)))) = _
    rw [show toList (P98 (dict x)) = [P98 (dict x)] from rfl]
    show ofList ((toList (reg 1)).filter (fun a => le (P98 (dict x)) a) ++ [P98 (dict x)])
        = P98 (dict x)
    rw [show toList (reg 1) = [reg 1] from rfl,
      List.filter_cons_of_neg (by
        show ¬ (le (P98 (dict x)) (reg 1) = true)
        rw [show le (P98 (dict x)) (reg 1) = false from by
          show ((P98 (dict x) == reg 1) || lt (P98 (dict x)) (reg 1)) = false
          rw [show (P98 (dict x) == reg 1) = false from rfl, hltPW]; rfl]
        exact Bool.noConfusion)]
    rfl
  rw [dict_D1_eq77 Hp (BT.D 1 x) hb1 hs1, dict_D1x98 Hp hb hs hg, hplus]
  show omegaNF (phi zero (add (reg 1) (dict x))) = phi zero (phi zero (add (reg 1) (dict x)))
  rw [omegaNF_of_le_M (ltM_left_phi94 zero (add (reg 1) (dict x))),
    phiNF_zero_phi94 (show add (reg 1) (dict x) ≠ zero from by
      intro hc; exact Term.noConfusion hc)]

/-! ### §98.4 値 — `ψ₀` の畳み込み -/

theorem phiNF_G098 {X : Term} (h : lt X G094 = false) :
    phiNF X (plus G094 TM.Term.one) = phi X (plus G094 TM.Term.one) := by
  rw [show plus G094 TM.Term.one = add G094 TM.Term.one from rfl]
  unfold phiNF
  rw [show ((add G094 TM.Term.one).isSC && lt X (add G094 TM.Term.one)) = false from by
    rw [show (add G094 TM.Term.one).isSC = false from rfl]; rfl]
  show phiNFsucc X (add G094 TM.Term.one) = phi X (add G094 TM.Term.one)
  unfold phiNFsucc
  rw [show splitFin (add G094 TM.Term.one) = (G094, 1) from rfl]
  split
  rename_i g m hgm
  injection hgm with hg hm
  subst hg; subst hm
  rw [if_pos (show 1 ≥ 1 by omega)]
  show (if (G094.isSC && lt X G094) = true then _ else phiNFdefault X (add G094 TM.Term.one))
      = phi X (add G094 TM.Term.one)
  rw [if_neg (by rw [h]; rw [Bool.and_false]; exact Bool.noConfusion)]
  show phiNFdefault X (add G094 TM.Term.one) = phi X (add G094 TM.Term.one)
  unfold phiNFdefault
  rw [if_neg (by
    rw [show ((add G094 TM.Term.one == zero) && X.isSC) = false from by
      rw [show (add G094 TM.Term.one == zero) = false from rfl]; rfl]
    exact Bool.noConfusion)]

theorem omegaNF_phi98 {X Y : Term} (h : lt zero X = true) : omegaNF (phi X Y) = phi X Y := by
  rw [omegaNF_of_le_M (ltM_left_phi94 X Y)]
  unfold phiNF
  rw [show ((phi X Y).isSC && lt zero (phi X Y)) = false from by
    rw [show (phi X Y).isSC = false from rfl]; rfl]
  show (if lt zero X = true then phi X Y else phiNFsucc zero (phi X Y)) = phi X Y
  rw [if_pos h]

/-- `ψ₁` の像は `Ω₁` より下にはいない。 -/
theorem ltW_dictD1_false98 (Hp : PsiIdxOKStd172) {a : BT} (hb1 : btLe72 1 (BT.D 1 a) = true)
    (hs1 : BT.isStd (BT.D 1 a) = true) : lt (dict (BT.D 1 a)) (reg 1) = false := by
  have hb := (btLe72_D 1 1 a hb1).2
  have hs := isStd_of_D hs1
  have hia := (inT_dict_of_std172 Hp a hb hs).1
  have hle : le (reg 1) (dict (BT.D 1 a)) = true := by
    rw [Trans.Dict.dict_D]
    exact le_reg1_collapse1_79 (dict a) hia
      (fun p hp => lt_pure73_reg2 (pure73_toList _ (pure73_dict a hb) p hp))
  rcases (Bool.or_eq_true _ _).mp hle with h1 | h1
  · rw [← eq_of_beq h1]; exact lt_irrefl _
  · exact lt_asymm_inT inT_W79 (inT_dict_of_std172 Hp (BT.D 1 a) hb1 hs1).1 h1

theorem isStd_D1D1_98 {x : BT} (hd : Hd085 x) (hs : BT.isStd x = true) :
    BT.isStd (BT.D 1 (BT.D 1 x)) = true := by
  show (BT.isStd (BT.D 1 x) && (BT.GB 1 (BT.D 1 x)).all (fun e => BT.lt e (BT.D 1 x))) = true
  rw [isStd_D1_98 hd hs, show BT.GB 1 (BT.D 1 x) = x :: BT.GB 1 x from rfl, gb1_nil98 x hd]
  show (BT.lt x (BT.D 1 x) && true) = true
  rw [btlt_hd0_D1_98 hd x]; rfl

theorem lt_zero_good98 {X : Term} (hg : Good98 X) : lt zero X = true := by
  rcases (Bool.or_eq_true _ _).mp hg.2.2.2.2.2 with h1 | h1
  · rw [← eq_of_beq h1]; decide
  · exact lt_trans_inT inT_zero (by decide) hg.1 (by decide) h1

theorem lt_G0_false98 {X : Term} (hg : Good98 X) : lt X G094 = false := by
  rcases (Bool.or_eq_true _ _).mp hg.2.2.2.2.2 with h1 | h1
  · rw [← eq_of_beq h1]; exact lt_irrefl _
  · exact lt_asymm_inT (by decide) hg.1 h1

theorem ne_W_good98 {X : Term} (hg : Good98 X) : (reg 1 == X) = false := by
  cases hc : (reg 1 == X) with
  | false => rfl
  | true =>
      exfalso
      have h := hg.2.2.2.2.1
      rw [← eq_of_beq hc, lt_irrefl] at h
      exact Bool.noConfusion h

theorem le_W_false98 {X : Term} (hg : Good98 X) : le (reg 1) X = false := by
  show ((reg 1 == X) || lt (reg 1) X) = false
  rw [ne_W_good98 hg, lt_asymm_inT hg.1 inT_W79 hg.2.2.2.2.1]
  rfl

/-- **§98.4 の主定理。** 一段上げた証人の値は `φ̄(dict x, Γ₀ ⊕ 1)`。 -/
theorem dict_bStep98 (Hp : PsiIdxOKStd172) {x : BT} (hb : btLe72 1 x = true)
    (hs : BT.isStd x = true) (hd : Hd085 x) (hg : Good98 (dict x)) :
    dict (bStep98 x) = phi (dict x) (plus G094 TM.Term.one) := by
  have hb1 := btLe_D1_98 hb
  have hs1 := isStd_D1_98 hd hs
  have hb2 := btLe_D1_98 hb1
  have hs2 := isStd_D1D1_98 hd hs
  have hP : dict (BT.D 1 x) = P98 (dict x) := dict_D1x98 Hp hb hs hg
  have hQ : dict (BT.D 1 (BT.D 1 x)) = Q98 (dict x) := dict_D1D1x98 Hp hb hs hd hg
  have hltP : lt (P98 (dict x)) (reg 1) = false := by
    rw [← hP]; exact ltW_dictD1_false98 Hp hb1 hs1
  have hltQ : lt (Q98 (dict x)) (reg 1) = false := by
    rw [← hQ]; exact ltW_dictD1_false98 Hp hb2 hs2
  have hleQA : le (Q98 (dict x)) (dict bOO94) = true := by
    rw [← hQ]
    have h1 : le (dict x) (dict (BT.Om 1)) = true := by
      show le (dict x) (reg 1) = true
      exact le_of_lt hg.2.2.2.2.1
    exact le_collapse1_le96 Hp (BT.D 1 x) (BT.D 1 (BT.Om 1)) hb2 rfl hs2 rfl
      (le_collapse1_le96 Hp x (BT.Om 1) hb1 rfl hs1 rfl h1)
  have hdictArg : dict (bArg98 x) = add (dict bOO94) (Q98 (dict x)) := by
    show plus (dict bOO94) (dict (BT.D 1 (BT.D 1 x))) = _
    rw [hQ]
    show (match toList (Q98 (dict x)) with
          | [] => dict bOO94
          | b1 :: _ => ofList ((toList (dict bOO94)).filter (fun a => le b1 a) ++
              toList (Q98 (dict x)))) = add (dict bOO94) (Q98 (dict x))
    rw [show toList (Q98 (dict x)) = [Q98 (dict x)] from rfl]
    show ofList ((toList (dict bOO94)).filter (fun a => le (Q98 (dict x)) a)
        ++ [Q98 (dict x)]) = _
    rw [show toList (dict bOO94) = [dict bOO94] from rfl,
      List.filter_cons_of_pos (by rw [hleQA])]
    rfl
  have hwA : wA (reg 1) (Q98 (dict x)) = dict x := by
    show ofList (((toList (logOm (Q98 (dict x)))).filter (fun q => !lt q (reg 1))).map
      (divAP (reg 1))) = _
    rw [show logOm (Q98 (dict x)) = P98 (dict x) from rfl,
      show toList (P98 (dict x)) = [P98 (dict x)] from rfl,
      List.filter_cons_of_pos (by rw [hltP]; rfl)]
    show ofList [divAP (reg 1) (P98 (dict x))] = dict x
    show omegaNF (subAP (reg 1) (logOm (P98 (dict x)))) = dict x
    rw [show logOm (P98 (dict x)) = add (reg 1) (dict x) from by
        show (if phiShifted zero (add (reg 1) (dict x)) then _ else _) = _
        rw [show phiShifted zero (add (reg 1) (dict x)) = false from by
          show (isFP zero (splitFin (add (reg 1) (dict x))).1 ||
            ((add (reg 1) (dict x) == zero) && (zero : Term).isSC)) = false
          rw [splitFin_addWX98 hg]
          rfl]
        rfl,
      show subAP (reg 1) (add (reg 1) (dict x)) = dict x from by
        show (match toList (add (reg 1) (dict x)) with
              | [] => zero
              | p :: rest => if p == reg 1 then ofList rest else add (reg 1) (dict x)) = _
        rw [show toList (add (reg 1) (dict x)) = [reg 1, dict x] from by
              show reg 1 :: toList (dict x) = _; rw [good_toList98 hg]]
        show (if (reg 1 == reg 1) = true then ofList [dict x] else _) = dict x
        rw [if_pos (by rfl)]
        rfl]
    exact hg.2.2.2.1
  have hwC : wC (reg 1) (Q98 (dict x)) = TM.Term.one := by
    show omegaNF (ofList ((toList (logOm (Q98 (dict x)))).filter (fun q => lt q (reg 1)))) = _
    rw [show logOm (Q98 (dict x)) = P98 (dict x) from rfl,
      show toList (P98 (dict x)) = [P98 (dict x)] from rfl,
      List.filter_cons_of_neg (by rw [hltP]; exact Bool.noConfusion)]
    rfl
  have hwQ : wcnf (reg 1) [Q98 (dict x)] = ([(dict x, TM.Term.one)], zero) := by
    rw [wcnf_cons_ge hltQ, wcnf_nil]
    show ([(wA (reg 1) (Q98 (dict x)), wC (reg 1) (Q98 (dict x)))], (zero : Term)) = _
    rw [hwA, hwC]
  have hw : wcnf (reg 1) (toList (add (dict bOO94) (Q98 (dict x))))
      = ([(reg 1, TM.Term.one), (dict x, TM.Term.one)], zero) := by
    rw [show toList (add (dict bOO94) (Q98 (dict x))) = [dict bOO94, Q98 (dict x)] from rfl,
      wcnf_cons_ge (show lt (dict bOO94) (reg 1) = false from by decide), hwQ]
    show (if (wA (reg 1) (dict bOO94) == dict x) = true
          then ((wA (reg 1) (dict bOO94),
                 plus (wC (reg 1) (dict bOO94)) TM.Term.one) :: [], (zero : Term))
          else ((wA (reg 1) (dict bOO94), wC (reg 1) (dict bOO94)) ::
                 (dict x, TM.Term.one) :: [], (zero : Term))) = _
    rw [show wA (reg 1) (dict bOO94) = reg 1 from rfl,
      if_neg (by rw [ne_W_good98 hg]; exact Bool.noConfusion),
      show wC (reg 1) (dict bOO94) = TM.Term.one from rfl]
  have hfold : ([(reg 1, TM.Term.one), (dict x, TM.Term.one)].foldl
      (init := ((none : Option Term), (none : Option Term)))
      (stepF (reg 1) (baseOf 0))).2.getD zero = phiNF (dict x) (plus G094 TM.Term.one) := by
    show (stepF (reg 1) (baseOf 0) (stepF (reg 1) (baseOf 0) (none, none)
      (reg 1, TM.Term.one)) (dict x, TM.Term.one)).2.getD zero = _
    rw [show stepF (reg 1) (baseOf 0) (none, none) (reg 1, TM.Term.one)
        = (some zero, some G094) from rfl]
    show (if le (reg 1) (dict x) = true then _ else
      ((some zero : Option Term), some (phiNF (dict x) (plus G094 TM.Term.one)))).2.getD zero = _
    rw [if_neg (by rw [le_W_false98 hg]; exact Bool.noConfusion)]
    rfl
  have hiV : inT (phi (dict x) (plus G094 TM.Term.one)) = true := by
    show (inT (dict x) && inT (plus G094 TM.Term.one) && lt (dict x) M
      && lt (plus G094 TM.Term.one) M) = true
    rw [hg.1, good_ltM98 hg, show inT (plus G094 TM.Term.one) = true from by decide,
      show lt (plus G094 TM.Term.one) M = true from by decide]
    rfl
  show collapse 0 (dict (bArg98 x)) = _
  rw [hdictArg, collapse0_raw89]
  show omegaNF (plus (reg 0) (plus
    (((wcnf (reg 1) (toList (add (dict bOO94) (Q98 (dict x))))).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero)
    ((wcnf (reg 1) (toList (add (dict bOO94) (Q98 (dict x))))).2))) = _
  rw [hw]
  show omegaNF (plus (reg 0) (plus
    (([(reg 1, TM.Term.one), (dict x, TM.Term.one)].foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero) zero)) = _
  rw [hfold, phiNF_G098 (lt_G0_false98 hg)]
  show omegaNF (plus (reg 0) (plus (phi (dict x) (plus G094 TM.Term.one)) zero)) = _
  rw [show plus (phi (dict x) (plus G094 TM.Term.one)) zero
      = phi (dict x) (plus G094 TM.Term.one) from rfl,
    show plus (reg 0) (phi (dict x) (plus G094 TM.Term.one))
      = plus zero (phi (dict x) (plus G094 TM.Term.one)) from rfl,
    plus_zero_left_inT hiV, omegaNF_phi98 (lt_zero_good98 hg)]

end

/-! ### §98.5 塔 — 帰納法 -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg dictInv)
open TM TM.Term
open Evidence.WF

/-- **順序の順向きの移送。** 良い項どうしなら `BT.lt` は `dict` の順序へ運ばれる。
    `bOnto85` と `DictLtA74` だけを使う — §94.5 の `btlt_of_lt94` の逆向き。 -/
theorem lt_dict98 (H2 : DictLtA74) {p q : BT}
    (hp : btLe72 1 p = true) (hsp : BT.isStd p = true) (hdp : Hd085 p)
    (hq : btLe72 1 q = true) (hsq : BT.isStd q = true) (hdq : Hd085 q)
    (h : BT.lt p q = true) : lt (dict p) (dict q) = true := by
  obtain ⟨u, hu, hvu⟩ := bOnto85 p hp hdp hsp
  obtain ⟨t, ht, hvt⟩ := bOnto85 q hq hdq hsq
  have hx := H2 u t hu ht (by rw [hvu, hvt]; exact h)
  rw [hvu, hvt] at hx
  exact hx

theorem lt_bTowG98_mono : ∀ (k n : Nat), k < n → BT.lt (bTowG98 k) (bTowG98 n) = true
  | k, 0, h => absurd h (by omega)
  | k, n + 1, h => by
      rcases Nat.lt_or_ge k n with h1 | h1
      · exact lt_trans83 (lt_bTowG98_mono k n h1) (lt_bTowG98 n)
      · have : k = n := by omega
        rw [this]; exact lt_bTowG98 n

theorem dict_bTowG98_zero : dict (bTowG98 0) = G094 := rfl

theorem le_G0_bTowG98 (H2 : DictLtA74) : ∀ n, le G094 (dict (bTowG98 n)) = true
  | 0 => by decide
  | n + 1 => by
      refine le_of_lt ?_
      rw [← dict_bTowG98_zero]
      exact lt_dict98 H2 (legal_bTowG98 0).1 (legal_bTowG98 0).2.1 (legal_bTowG98 0).2.2
        (legal_bTowG98 (n+1)).1 (legal_bTowG98 (n+1)).2.1 (legal_bTowG98 (n+1)).2.2
        (lt_bTowG98_mono 0 (n+1) (by omega))

/-- **塔の各段は `Good98`。** -/
theorem good_bTowG98 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) :
    ∀ n, Good98 (dict (bTowG98 n)) := by
  intro n
  induction n with
  | zero =>
      rw [dict_bTowG98_zero]
      exact ⟨by decide, rfl, rfl, by decide, by decide, by decide⟩
  | succ m ih =>
      have hval : dict (bTowG98 (m + 1)) = phi (dict (bTowG98 m)) (plus G094 TM.Term.one) :=
        dict_bStep98 Hp (legal_bTowG98 m).1 (legal_bTowG98 m).2.1 (legal_bTowG98 m).2.2 ih
      refine ⟨(inT_dict_of_std172 Hp _ (legal_bTowG98 (m+1)).1 (legal_bTowG98 (m+1)).2.1).1,
        ?_, ?_, ?_,
        ltW_dict94 Hp _ (legal_bTowG98 (m+1)).1 (legal_bTowG98 (m+1)).2.1
          (legal_bTowG98 (m+1)).2.2,
        le_G0_bTowG98 H2 (m+1)⟩
      · rw [hval]; rfl
      · rw [hval, show plus G094 TM.Term.one = add G094 TM.Term.one from rfl]
        cases hc : (phi (dict (bTowG98 m)) (add G094 TM.Term.one) == TM.Term.one) with
        | false => rfl
        | true =>
            exact absurd (eq_of_beq hc)
              (by intro h; injection h with _ h2; exact Term.noConfusion h2)
      · rw [hval]; exact omegaNF_phi98 (lt_zero_good98 ih)

/-- 出発点を選べる塔でも `Γ₀` の上にとどまる。 -/
theorem le_G0_bIter98 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) {x : BT} (H : Inv98 x)
    (hg0 : le G094 (dict x) = true) : ∀ n, le G094 (dict (bIter98 x n)) = true
  | 0 => hg0
  | n + 1 => by
      have hlt := lt_dict98 H2 (legal_bIter98 H 0).1 (legal_bIter98 H 0).2.1
        (legal_bIter98 H 0).2.2 (legal_bIter98 H (n+1)).1 (legal_bIter98 H (n+1)).2.1
        (legal_bIter98 H (n+1)).2.2 (lt_bIter98_mono H 0 (n+1) (by omega))
      exact le_trans3 (inT_le_fragR _ (by decide : inT G094 = true))
        (inT_le_fragR _ (inT_dict_of_std172 Hp _ (legal_bIter98 H 0).1
          (legal_bIter98 H 0).2.1).1)
        (inT_le_fragR _ (inT_dict_of_std172 Hp _ (legal_bIter98 H (n+1)).1
          (legal_bIter98 H (n+1)).2.1).1)
        hg0 (le_of_lt hlt)

/-- **出発点を選べる塔の各段も `Good98`。** -/
theorem good_bIter98 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) {x : BT} (H : Inv98 x)
    (hg : Good98 (dict x)) : ∀ n, Good98 (dict (bIter98 x n)) := by
  intro n
  induction n with
  | zero => exact hg
  | succ m ih =>
      have hval : dict (bIter98 x (m + 1))
          = phi (dict (bIter98 x m)) (plus G094 TM.Term.one) :=
        dict_bStep98 Hp (legal_bIter98 H m).1 (legal_bIter98 H m).2.1
          (legal_bIter98 H m).2.2 ih
      refine ⟨(inT_dict_of_std172 Hp _ (legal_bIter98 H (m+1)).1
          (legal_bIter98 H (m+1)).2.1).1, ?_, ?_, ?_,
        ltW_dict94 Hp _ (legal_bIter98 H (m+1)).1 (legal_bIter98 H (m+1)).2.1
          (legal_bIter98 H (m+1)).2.2,
        le_G0_bIter98 Hp H2 H hg.2.2.2.2.2 (m+1)⟩
      · rw [hval]; rfl
      · rw [hval, show plus G094 TM.Term.one = add G094 TM.Term.one from rfl]
        cases hc : (phi (dict (bIter98 x m)) (add G094 TM.Term.one) == TM.Term.one) with
        | false => rfl
        | true =>
            exact absurd (eq_of_beq hc)
              (by intro h; injection h with _ h2; exact Term.noConfusion h2)
      · rw [hval]; exact omegaNF_phi98 (lt_zero_good98 ih)

/-- **§98.5 の主定理 (0)。** 出発点を選べる塔の値の閉じた形 — `φ̄` の段を一つずつ上げる。 -/
theorem dict_bIter98 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) {x : BT} (H : Inv98 x)
    (hg : Good98 (dict x)) (n : Nat) :
    dict (bIter98 x (n + 1)) = phi (dict (bIter98 x n)) (plus G094 TM.Term.one) :=
  dict_bStep98 Hp (legal_bIter98 H n).1 (legal_bIter98 H n).2.1 (legal_bIter98 H n).2.2
    (good_bIter98 Hp H2 H hg n)

/-- `Γ₀` から出発した塔がもとの `bTowG98`。 -/
theorem bTowG98_eq98 : ∀ n, bTowG98 n = bIter98 (BT.D 0 bOO94) n
  | 0 => rfl
  | n + 1 => by
      show bStep98 (bTowG98 n) = bStep98 (bIter98 (BT.D 0 bOO94) n)
      rw [bTowG98_eq98 n]

/-- **§98.5 の主定理 (1)。** 塔の値の閉じた形。 -/
theorem dict_bTowG98 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (n : Nat) :
    dict (bTowG98 (n + 1)) = phi (dict (bTowG98 n)) (plus G094 TM.Term.one) :=
  dict_bStep98 Hp (legal_bTowG98 n).1 (legal_bTowG98 n).2.1 (legal_bTowG98 n).2.2
    (good_bTowG98 Hp H2 n)

end

/-! ### §98.6 生の塔を上から押さえる -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg dictInv)
open TM TM.Term
open Evidence.WF

theorem inT_rawT98 : ∀ n, inT (rawT94 n) = true
  | 0 => by decide
  | n + 1 => by
      show (inT (rawT94 n) && inT zero && lt (rawT94 n) M && lt zero M) = true
      rw [inT_rawT98 n, inT_zero, lt_zero_M]
      cases n with
      | zero => rw [show rawT94 0 = phi G094 zero from rfl, lt_phi_M]; rfl
      | succ m => rw [show rawT94 (m+1) = phi (rawT94 m) zero from rfl, lt_phi_M]; rfl

theorem ltM_rawT98 : ∀ n, lt (rawT94 n) M = true
  | 0 => lt_phi_M _ _
  | _ + 1 => lt_phi_M _ _

/-- **§98.6 の主定理 (1)。** 生の塔の各段は、一段上の証人の値の下にいる。 -/
theorem lt_rawT_bTowG98 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) :
    ∀ n, lt (rawT94 n) (dict (bTowG98 (n + 1))) = true
  | 0 => by
      rw [dict_bTowG98 Hp H2 0, dict_bTowG98_zero]
      exact lt_phi_arg (by decide)
  | n + 1 => by
      have hih := lt_rawT_bTowG98 Hp H2 n
      have hne : ¬ (rawT94 n = dict (bTowG98 (n + 1))) := by
        intro hc
        rw [hc, lt_irrefl] at hih
        exact Bool.noConfusion hih
      rw [dict_bTowG98 Hp H2 (n + 1),
        show rawT94 (n + 1) = phi (rawT94 n) zero from rfl,
        lt_phi_phi (by intro hc; injection hc with h1 _; exact hne h1),
        if_neg hne, if_pos hih]
      exact lt_zero_ne76 (by intro hc; exact Term.noConfusion hc)

theorem hd0_bGam98 : Hd085 bGam85 := by
  intro z hz
  exact ⟨BT.sum (BT.D 1 (BT.D 1 (BT.Om 1))) (BT.D 1 (BT.D 1 (BT.Om 1))),
    List.mem_singleton.mp hz⟩

theorem btlt_bTowG_bGam98 : ∀ n, BT.lt (bTowG98 n) bGam85 = true
  | 0 => btlt_arg98 (by rfl) (btlt_self_sum98 1 (BT.D 1 (BT.Om 1)))
  | n + 1 => by
      have hd := (legal_bTowG98 n).2.2
      have hlt := lt_D1D1_bOO98 hd
      show BT.lt (BT.D 0 (bArg98 (bTowG98 n)))
        (BT.D 0 (BT.sum bOO94 bOO94)) = true
      refine btlt_arg98 (bt_beq_false _ _ (fun hc => ?_)) (btlt_cons_same98 hlt)
      injection hc with _ h2
      rw [h2, lt_asymm74 hlt] at hlt
      exact Bool.noConfusion hlt

/-- **§98.6 の主定理 (2)。** 塔の各段の値は `Γ₁ = ψ_Ω(1)` より下。 -/
theorem lt_bTowG_Gam98 (H2 : DictLtA74) (n : Nat) :
    lt (dict (bTowG98 n)) Gam1_94 = true :=
  lt_dict98 H2 (legal_bTowG98 n).1 (legal_bTowG98 n).2.1 (legal_bTowG98 n).2.2
    rfl rfl hd0_bGam98 (btlt_bTowG_bGam98 n)

/-- **§98.6 の主定理 (3)。** 生の塔の各段は `Γ₁` より下。 -/
theorem lt_rawT_Gam98 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (n : Nat) :
    lt (rawT94 n) Gam1_94 = true :=
  lt_trans_inT (inT_rawT98 n)
    (inT_dict_of_std172 Hp _ (legal_bTowG98 (n+1)).1 (legal_bTowG98 (n+1)).2.1).1
    (inT_dict_of_std172 Hp _ (rfl : btLe72 1 bGam85 = true) (rfl : BT.isStd bGam85 = true)).1
    (lt_rawT_bTowG98 Hp H2 n) (lt_bTowG_Gam98 H2 (n+1))

end

/-! ### §98.7 条項の切れ端 -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg)
open TM TM.Term
open Evidence.WF

/-- 一段上げた証人の値は `φ̄(dict x, 0)` より真に上。§85.7 が像に入らないと言った形が
    まさにこれである。 -/
theorem lt_phi0_bStep98 (Hp : PsiIdxOKStd172) {x : BT} (hb : btLe72 1 x = true)
    (hs : BT.isStd x = true) (hd : Hd085 x) (hg : Good98 (dict x)) :
    lt (phi (dict x) zero) (dict (bStep98 x)) = true := by
  rw [dict_bStep98 Hp hb hs hd hg]
  exact lt_phi_arg (by decide)

/-- **§98.7 の主定理。** `φ̄(dict x, 0)` 以下の挑戦者は、`bStep98 x` の上にある像点を
    目標とするかぎり、証人 `bStep98 x` を持つ。 -/
theorem denseHi_step98 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) {x q : BT}
    (hI : Inv98 x) (hg : Good98 (dict x))
    (hbq : btLe72 1 q = true) (hsq : BT.isStd q = true) (hdq : Hd085 q)
    (hlt : BT.lt (bStep98 x) q = true) {s : Term} (hs : inT s = true)
    (hle : le s (phi (dict x) zero) = true) :
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
      le s (dict b) = true ∧ lt (dict b) (dict q) = true := by
  obtain ⟨hb, hst, hd, hgb⟩ := hI
  have hbS := btLe_bStep98 hb
  have hsS := isStd_bStep98 hd hst hgb
  have hdS := hd0_bStep98 x
  have hiS := (inT_dict_of_std172 Hp _ hbS hsS).1
  have hiP : inT (phi (dict x) zero) = true := by
    show (inT (dict x) && inT zero && lt (dict x) M && lt zero M) = true
    rw [hg.1, inT_zero, good_ltM98 hg, lt_zero_M]; rfl
  refine ⟨bStep98 x, hbS, hsS, hdS, ?_, ?_⟩
  · exact le_of_lt (lt_of_le_of_lt3 (inT_le_fragR _ hs) (inT_le_fragR _ hiP)
      (inT_le_fragR _ hiS) hle (lt_phi0_bStep98 Hp hb hst hd hg))
  · exact lt_dict98 H2 hbS hsS hdS hbq hsq hdq hlt

/-- **§98.7 の系。**  出発点を選べる塔の各段で同じことが言える — `φ̄` の段を一つ上げる
    たびに、その一段下の `φ̄(·, 0)` 以下の挑戦者がまとめて片づく。 -/
theorem denseHi_iter98 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) {x : BT}
    (H : Inv98 x) (hg : Good98 (dict x)) (n : Nat) {q : BT}
    (hbq : btLe72 1 q = true) (hsq : BT.isStd q = true) (hdq : Hd085 q)
    (hlt : BT.lt (bIter98 x (n + 1)) q = true) {s : Term} (hs : inT s = true)
    (hle : le s (phi (dict (bIter98 x n)) zero) = true) :
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
      le s (dict b) = true ∧ lt (dict b) (dict q) = true :=
  denseHi_step98 Hp H2 (inv_bIter98 H n) (good_bIter98 Hp H2 H hg n) hbq hsq hdq hlt hs hle

/-- **生の塔のところでは `DictDenseHi94` の要求は満たせる。**  目標の値が `Γ₁` 以上なら、
    `rawT94 n` 以下の挑戦者は `bTowG98 (n+1)` が証人になる。 -/
theorem denseHi_rawT98 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) {v : Term}
    (hiv : inT v = true) (hv : le Gam1_94 v = true) (n : Nat) {s : Term}
    (hs : inT s = true) (hle : le s (rawT94 n) = true) :
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
      le s (dict b) = true ∧ lt (dict b) v = true := by
  have hL := legal_bTowG98 (n + 1)
  have hiS := (inT_dict_of_std172 Hp _ hL.1 hL.2.1).1
  have hiG : inT Gam1_94 = true :=
    (inT_dict_of_std172 Hp bGam85 (rfl : btLe72 1 bGam85 = true)
      (rfl : BT.isStd bGam85 = true)).1
  refine ⟨bTowG98 (n + 1), hL.1, hL.2.1, hL.2.2, ?_, ?_⟩
  · exact le_of_lt (lt_of_le_of_lt3 (inT_le_fragR _ hs) (inT_le_fragR _ (inT_rawT98 n))
      (inT_le_fragR _ hiS) hle (lt_rawT_bTowG98 Hp H2 n))
  · exact lt_of_lt_of_le3 (inT_le_fragR _ hiS) (inT_le_fragR _ hiG) (inT_le_fragR _ hiv)
      (lt_bTowG_Gam98 H2 (n + 1)) hv

/-- 部分領域の目標に当てはめた形。 -/
theorem denseHi_rawT_vOf98 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) {t : B}
    (ht : stdB1 t = true) (hv : le Gam1_94 (vOf t) = true) (n : Nat) {s : Term}
    (hs : inT s = true) (hle : le s (rawT94 n) = true) :
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
      le s (dict b) = true ∧ lt (dict b) (vOf t) = true :=
  denseHi_rawT98 Hp H2 (inT_vOf94 Hp t ht) hv n hs hle

end

/-! ### §98.8 残る一本を名指しし、四つを反証する -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg)
open TM TM.Term
open Evidence.WF

/-- **残る一本 — 𝔗(M) 側の `Γ₁` の共終性。証明しない。**
    `Γ₀` 以上 `Γ₁` 未満の項はどれも生の塔のどれかの段に押さえられる、という主張。 -/
def CofGam1_98 : Prop := ∀ s : Term, inT s = true → lt s Gam1_94 = true →
    le G094 s = true → ∃ n, le s (rawT94 n) = true

/-- **`Γ₁` より下の挑戦者・`Γ₁` 以上の目標のところでは、残るのは `CofGam1_98` だけ。** -/
theorem denseHi_below_Gam1_98 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HC : CofGam1_98)
    {v : Term} (hiv : inT v = true) (hv : le Gam1_94 v = true)
    {s : Term} (hs : inT s = true) (hlt : lt s Gam1_94 = true) :
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
      le s (dict b) = true ∧ lt (dict b) v = true := by
  have hiG0 : inT G094 = true := by decide
  have hiG : inT Gam1_94 = true :=
    (inT_dict_of_std172 Hp bGam85 (rfl : btLe72 1 bGam85 = true)
      (rfl : BT.isStd bGam85 = true)).1
  rcases Evidence.WF.lt_trichotomy_inT hs hiG0 with h | h | h
  · have hL := legal_bTowG98 0
    refine ⟨bTowG98 0, hL.1, hL.2.1, hL.2.2, ?_, ?_⟩
    · rw [dict_bTowG98_zero]; exact le_of_lt h.1
    · exact lt_of_lt_of_le3 (inT_le_fragR _ (by rw [dict_bTowG98_zero]; exact hiG0))
        (inT_le_fragR _ hiG) (inT_le_fragR _ hiv) (lt_bTowG_Gam98 H2 0) hv
  · obtain ⟨n, hn⟩ := HC s hs hlt (by rw [h.2.1]; exact le_self G094)
    exact denseHi_rawT98 Hp H2 hiv hv n hs hn
  · obtain ⟨n, hn⟩ := HC s hs hlt (le_of_lt h.2.2)
    exact denseHi_rawT98 Hp H2 hiv hv n hs hn

/-- **反証 1 — 一段上げる作用素は「正しい証人」だけでは閉じない。**
    段 1 以下・標準・成分が `D 0` の項で、一段上げると標準でなくなるものがある。
    効いているのは `Inv98` の 4 番目の条 (`GB 0 x` が新しい引数より下) である。 -/
def xBad98 : BT := BT.D 0 (BT.D 1 (BT.D 1 (BT.D 1 (BT.D 1 BT.zero))))

theorem legal_xBad98 :
    btLe72 1 xBad98 = true ∧ BT.isStd xBad98 = true ∧ hd085B xBad98 = true := ⟨rfl, rfl, rfl⟩

theorem bStep98_needs_gb98 : ¬ (∀ x : BT, btLe72 1 x = true → BT.isStd x = true →
    hd085B x = true → BT.isStd (bStep98 x) = true) := by
  intro h
  exact absurd (h xBad98 rfl rfl rfl) (by decide)

/-- **反証 2 — 値の閉じた形は `Γ₀ ≤ dict x` を要る。**  `dict x = ε₀` のところでは
    `φ̄(ε₀, Γ₀ ⊕ 1)` ではなく `φ̄(ε₀, Γ₀)` が出る — `phiNFsucc` が発火するからで、
    落ちるのはちょうど `⊕ 1` の一段である。 -/
def xEps98 : BT := BT.D 0 (BT.Om 1)

theorem dict_xEps98 : dict xEps98 = E081 := rfl

theorem dict_bStep_xEps98 : dict (bStep98 xEps98) = phi E081 G094 := rfl

theorem dict_bStep98_needs_G098 : ¬ (∀ x : BT, btLe72 1 x = true → BT.isStd x = true →
    hd085B x = true → dict (bStep98 x) = phi (dict x) (plus G094 TM.Term.one)) := by
  intro h
  exact absurd (h xEps98 rfl rfl rfl) (by decide)

/-- **反証 3 — `Γ₀ ≤ dict x` だけでは足りない。`dict x` は `ω` 冪の不動点でなければ
    ならない。**  `Γ₀ ⊕ Γ₀` は `Γ₀` より上だが加法主要ではなく、指数に入るのは
    `ω^(Γ₀ ⊕ Γ₀)` の方である。 -/
def xSum98 : BT := BT.sum (BT.D 0 bOO94) (BT.D 0 bOO94)

theorem le_G0_xSum98 : le G094 (dict xSum98) = true := by decide

theorem dict_bStep98_needs_fp98 : ¬ (∀ x : BT, btLe72 1 x = true → BT.isStd x = true →
    hd085B x = true → le G094 (dict x) = true →
    dict (bStep98 x) = phi (dict x) (plus G094 TM.Term.one)) := by
  intro h
  exact absurd (h xSum98 rfl rfl rfl le_G0_xSum98) (by decide)

/-- **反証 4 — 段は 0 では足りない。**  §97 の `btLe0_invE97` は像が段 0 から出ないことを
    言ったが、`Γ₀` の上ではそれは不可能である。一段上げた項はどの段でも `btLe72 0` を
    破る。段 2 へは一歩も行かない (`btLe72 1` は保たれる) — §85.6 が条項を反証するのは
    そこである。 -/
theorem btLe0_bStep98 (x : BT) : btLe72 0 (bStep98 x) = false := rfl

theorem btLe0_bTowG98 : ∀ n, btLe72 0 (bTowG98 n) = false
  | 0 => rfl
  | _ + 1 => rfl

/-- §94.6 の素朴な候補は段も頭も正しいが標準ではない — §98 の構成が `Ω^Ω` を
    先頭に置く理由。 -/
theorem naive_not_std98 :
    BT.isStd bNaive94 = false ∧ (btLe72 1 bNaive94 && hd085B bNaive94) = true := ⟨rfl, rfl⟩

end

/-! ### §98.9 測定 (凍結)

**構成を先に書く。**  §94.7 の 495 項の母集団をそのまま再利用し、そこへ `1` と `ε₀` の
逆像、塔の 6 段、そして「一段上げた」項をすべて足す。**仮説では濾さない** — だから
120 項のうち 19 項は正しい証人ですらない (一段上げる作用素は `Inv98` の 4 番目の条を
破る項の上では標準性を壊す)。仮説が母集団に見えていない一斉合格は証拠にならない
(§93 の教訓)。 -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg dictInv)
open TM TM.Term
open Evidence.WF

/-- `Inv98` の 4 番目の条を Bool で。 -/
def inv98B (x : BT) : Bool := (BT.GB 0 x).all (fun e => BT.lt e (bArg98 x))
/-- `Good98` を Bool で。 -/
def good98B (X : Term) : Bool :=
  X.isAP && !(X == TM.Term.one) && (omegaNF X == X) && lt X (reg 1) && le G094 X
/-- `Γ₀ ≤ ·` を落とした形 — 非退化の確認用。 -/
def good98noG (X : Term) : Bool :=
  X.isAP && !(X == TM.Term.one) && (omegaNF X == X) && lt X (reg 1)
/-- §98.4 の結論そのもの。 -/
def okStep98 (x : BT) : Bool := dict (bStep98 x) == phi (dict x) (plus G094 TM.Term.one)

def base98 : List BT := BT.D 0 BT.zero :: BT.D 0 (BT.Om 1) :: everyB94 9 pool94
def pop98 : List BT := (base98 ++ (List.range 6).map bTowG98 ++ base98.map bStep98).eraseDups

/-! 母集団。仮説で濾していないので、正しい証人でない項が 19 入っている。 -/
#guard pop98.length == 120
#guard pop98.countP bgood94 == 101
#guard pop98.all fun x => lt (dict x) (reg 1)

/-! **肯定 1 (構造) — 一段上げて標準になるのはちょうど `Inv98` の 4 番目の条が
    成り立つところ。**  §94.7 の 495 項すべてで一致、食い違い 0。324 が通り 171 が落ちる。 -/
#guard pool94.length == 495
#guard pool94.countP (fun x => bgood94 (bStep98 x) != inv98B x) == 0
#guard pool94.countP inv98B == 324

/-! **肯定 2 (値) — 閉じた形が成り立つのはちょうど `Good98` のところ。**
    120 項で 65 = 65、食い違い 0。 -/
#guard pop98.countP (fun x => good98B (dict x)) == 65
#guard pop98.countP okStep98 == 65
#guard pop98.countP (fun x => okStep98 x != good98B (dict x)) == 0

/-! **非退化 — `Γ₀ ≤ ·` を落とすと 70 になる。**  仮説の各条は母集団に見えている:
    加法主要でないものが 49、`ω` 冪の不動点でないものが 50、`Γ₀` より下が 36、`1` が 1。 -/
#guard pop98.countP (fun x => good98noG (dict x)) == 70
#guard pop98.countP (fun x => !((dict x).isAP)) == 49
#guard pop98.countP (fun x => (omegaNF (dict x) == dict x) == false) == 50
#guard pop98.countP (fun x => le G094 (dict x) == false) == 36
#guard pop98.countP (fun x => dict x == TM.Term.one) == 1

/-! **肯定 3 — 塔。**  各段は正しい証人、値は閉じた形、生の塔を上から押さえ、`Γ₁` より下。
    そして段 0 にはどの段も収まらない — §97 の `btLe0_invE97` と対照的である。 -/
#guard (List.range 6).all fun n => bgood94 (bTowG98 n) && (btLe72 0 (bTowG98 n) == false)
#guard (List.range 5).all fun n =>
  dict (bTowG98 (n+1)) == phi (dict (bTowG98 n)) (plus G094 TM.Term.one)
#guard (List.range 5).all fun n =>
  lt (rawT94 n) (dict (bTowG98 (n+1))) && lt (dict (bTowG98 (n+1))) Gam1_94

/-! **否定 — 母集団は生の塔のところで密ではない。**  §94.7 の 495 の値のうち
    `[rawT94 n, Γ₁)` に入るものは 0。塔の段はどれも `dict` の像に入らず、CN でもない
    (§97 の低い側は届かない)。 -/
#guard (List.range 5).all fun n => dpool94.countP (fun d => le (rawT94 n) d && lt d Gam1_94) == 0
#guard (List.range 8).all fun n =>
  inT (rawT94 n) && (dictInv (rawT94 n)).isNone && lt (rawT94 n) Gam1_94
#guard (List.range 8).all fun n => CN (rawT94 n) == false

/-! **否定 (作った項)。**  §98.8 の四つを数字で。`xBad98` は正しい証人だが一段上げると
    標準でない。`xEps98` の値は `φ̄(ε₀, Γ₀)` で `⊕ 1` が落ちる。`xSum98` は `Γ₀` より
    上だが加法主要でなく、指数に入るのは `ω^(Γ₀ ⊕ Γ₀)` の方。 -/
#guard bgood94 xBad98 && (BT.isStd (bStep98 xBad98) == false) && (inv98B xBad98 == false)
#guard bgood94 xEps98 && (okStep98 xEps98 == false)
#guard dict (bStep98 xEps98) == phi E081 G094
#guard bgood94 xSum98 && le G094 (dict xSum98) && (okStep98 xSum98 == false)
#guard (BT.isStd bNaive94 == false) && btLe72 1 bNaive94 && hd085B bNaive94

end

end Evidence.Region
