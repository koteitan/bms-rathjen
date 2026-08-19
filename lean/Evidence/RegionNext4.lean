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

/-! ## §101 THE VEBLEN GATE IS NOT A `K`-CONDITION ON 𝔗(M) — AND THE BRIDGE'S FREE HALF

§99 collapsed the whole Veblen fold onto one clause (`gate_iff_hiMono99` :
`CollapseMono0Hi81 ↔ HiMono89`) and named the two ways at it:

> **(i) Express the `K`-condition on the 𝔗(M) side.**  If there is a 𝔗(M)-side predicate
> that (a) follows from `BT.isStd (ψ₀ a)` without the bridge and (b) rules out `cexA89`,
> the clause becomes a statement about `Kset` and the fold, and the bridge drops out.
> **(ii) Push §99's asymmetric trick further.**

**§101 takes (i), and (i) does not close.**  What §101 proves is that the two candidate
predicates — the only two the file's own vocabulary offers — are **not enough**, and it
proves it with a BUILT pair, not a sweep.  It also takes the one piece of the bridge that
is free and proves it outright.

WHAT IS PROVED.

  §101.1  **THE BRIDGE'S FREE HALF.**  `mem_toList_dict_ofL101` :
          every component of `dict (ofL l)` is `dict p` for a component `p ∈ l` — because
          `toList (plus s t)` is a FILTER of `toList s` followed by `toList t`, so `plus`
          can only DROP.  §93.3's bridge is the equality, and it is the "nothing is dropped"
          half that costs `CollapseMono0Hi81`; the inclusion costs nothing.  Hence
          `mem_toList_hiW_dict101` (`hi (dict a)`'s components are `dict (ψ₁ c)` with
          `ψ₁ c` a component of `a`) and `mem_toList_loW_dict101` (`lo`'s are `dict (ψ₀ c)`),
          both gate-free.  **§99.4 obtained the `lo` version through `bridge99`, i.e.
          through the gate at smaller symbol counts; only membership was ever used there.**

  §101.2  **THE FOLD'S VEBLEN BRANCH, NAMED.**  `vArg101` is the argument the Veblen branch
          of `stepF` hands to `phiNF`, `collAt101` says that step COLLAPSES
          (`phiNF a v = v`), and `foldNF101` says no step does.  `phiNF` collapses in
          exactly two ways (`phiNF a b = b` when `b = φ̄γδ` with `α < γ`, or when `b ∈ SC`
          with `α < b`), and **both occur inside `dict`'s image**:
          `veblenColl101` is §81's `cexA89` — `φ̄₁(φ̄₂0) = φ̄₂0` — and `scColl101` is NEW,
          `φ̄₁(ψ_{Ω₁}1) = ψ_{Ω₁}1`, at the BUILT term
          `ψ₁ψ₁ψ₁0 ⊕ ψ₁ψ₀(ψ₁ψ₁ψ₁0 ⊕ ψ₁ψ₁ψ₁0)`, whose partner `ψ₁ψ₁ψ₁0 ⊕ ψ₁ψ₁ψ₁0` is
          `K`-standard and carries the SAME `ψ₀`-value.  `foldNF101` is `true` at both
          `cexB89` and that partner and `false` at both offenders: **the detector is exactly
          §99's clause (b).**

  §101.3  **APPROACH (i), STATED ABSTRACTLY.**  `HiMonoP101 P` is `HiMono89` with the
          `K`-condition `BT.isStd (ψ₀ ·)` replaced by a 𝔗(M)-side `P (hi (dict ·))`, and
          `hiMono_of_P101` : a `P` with the translation property gives `HiMono89` — **with
          no bridge anywhere**.  `certIn_t326_P101` re-hangs row 326 on any such `P`.
          That is the exact shape §99 asked for.

  §101.4  **AND IT IS FALSE FOR BOTH CANDIDATES.**  `not_hiMonoP_foldNF101`,
          `not_hiMonoP_ksetOK101` and `not_hiMonoP_both101` — ONE built pair refutes all
          three, and it refutes them by REVERSING the order, not by a tie:

              a = ψ₁ψ₁0 ⊕ ψ₁ψ₁0 ⊕ ψ₁ψ₀(ψ₁ψ₁ψ₁0 ⊕ ψ₁0)      (17 symbols)
              b = ψ₁ψ₁ψ₁0 ⊕ ψ₁ψ₀(ψ₁0 ⊕ ψ₁0)                 (12 symbols)

          both `BT.isStd`, both `Ω₁ ≤ dict ·`, both `foldNF101`, both `inT (ψ_{Ω₁} ·)`
          (Rathjen 2.1(vi), the `K_κ γ < γ` clause itself), `hi (dict a) < hi (dict b)`, and
          `ψ₀(hi (dict a)) > ψ₀(hi (dict b))`.  `b` IS `K`-standard; `a` is not, and that is
          the only hypothesis of `HiMono89` it fails.  **So no predicate built from the fold's
          own collapses plus Rathjen's own coefficient condition can be §99's (i).**  The
          `K`-condition itself does reach the 𝔗(M) side without the bridge as far as the
          COMPONENTS go — `hiArg_lt101` / `loArg_lt101` (§101.1) give `c < a` for every
          `dict (ψ₁ c)`, `dict (ψ₀ c)` occurring in `hi`, `lo` — and that is not enough:
          what the witness needs bounded is the argument of a `ψ₀`-value occurring as a
          COEFFICIENT, and the inclusion never names it.

  §101.5  **THE FIRING CASE IS FREE OF ALL OF IT.**  `foldNF_of_allFire101` : a fold whose
          every pair fires cannot collapse — `collAt101` is about the Veblen branch and there
          is none.  And there `HiMono89`'s conclusion IS the collapse-index comparison:
          `hiMono_eq_idx101` (`lastFire_hiW101`, `idxF_hiW101`, §92.2's `collapse0_hi_psi92`
          and §69.4b's `lt_psi_same`), so `IdxMono101 → HiMonoFire101` — **gate-free, and in
          §92's own language.**  The residue of `HiMono89` is the Veblen branch and nothing
          else.

WHAT IS **NOT** CLAIMED.  `HiMono89` is NOT proved and NOT refuted; row 326 still rests on
`PsiIdxOKStd172`, `HiMono89`, `DictDenseHi94` exactly as §99 left it.  §101 does not prove
`IdxMono101` either.  The negatives of §101.4 are about the two candidate predicates, **not
about `HiMono89`** — every witness there fails `BT.isStd (ψ₀ ·)` at `a`, as it must.

**WHERE §101 STOPPED, PRECISELY.**  Approach (i) needs a 𝔗(M)-side `P` with the translation
property, and §101.4 shows the two available ones do not carry the conclusion.  What the
witness shows is missing is a comparison BETWEEN the two folds, not a condition on either:
`a`'s coefficient at its last pair is a `ψ₀`-value manufactured from an argument that is
LARGER than `a` itself, and the `BT` side sees that as `G(a,0) ∋ z` with `z > a` while the
𝔗(M) side sees only that `z` is some coefficient below `Ω₁`.  Recovering "`z < a`" on the
𝔗(M) side is exactly the bridge again — the same circle §99 named.  §101.1 breaks the easy
half of it and no more: the inclusion is free, the surjection is not, and the surjection is
what names `z`.

WHAT THE MEASUREMENT SAYS (§101.6 gives the construction).  The population is BUILT to
collapse, following §97's and §99's model: 33 inner terms whose `ψ₀`-values are Veblen
fixed points or `ψ_{Ω₁}`-values, capped as `ψ₁ψ₀ z`, and prefixed by 0-3 copies of a
principal `ψ₁`-term — **627 terms, of which 305 actually collapse.**  Nothing is filtered.

  * **The `K`-condition kills EVERY constructed collapse: 305 collapse, 263 are
    `K`-standard, and the intersection is EMPTY.**  The family was built to defeat exactly
    that, one shape at a time (raise the coefficient above the accumulator, and the `ψ₀`
    argument that raises it climbs above the whole term); it never once got through.
  * **The two candidate predicates are implied by the `K`-condition on the corpus and still
    do not suffice.**  On the 76 `BT.isStd` terms of the sample: `foldNF101` fails on 0 of
    the 39 `K`-standard ones and `inT (ψ_{Ω₁} ·)` on 0 — **clause (a) holds for both.**  But
    of the 2850 residual pairs, 645 break the conclusion; filtering by `foldNF101` leaves
    **89 of 990**, by `inT (ψ_{Ω₁} ·)` **85 of 1485**, by BOTH **13 of 861** — and by the
    `K`-condition **0 of 741**.  The gap shrinks and stays open.
  * **The 13 survivors are not junk, and the smallest is the pair frozen in §101.4**
    (17 + 12 symbols; the guard checks both that it is in the list and that nothing in the
    list is smaller).
  * **All 645 breaks are in the Veblen branch.**  On the capped population the last pair
    never fires (0 of 76), because the cap `ψ₁ψ₀ z` always has base-`Ω₁` exponent 1.
  * **The firing case is populated, and there the clause holds.**  A second, cap-free
    population — 27 terms, all `K`-standard — has **14 whose every pair fires**, and on
    their 91 residual pairs the conclusion breaks **0 times**: §101.5's equivalence is
    seeing `IdxMono101`, not a vacuum.
-/

/-! ### §101.1 橋の只の半分 — `plus` は落とすことしかできない -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1)
open TM TM.Term
open Evidence.WF

theorem toList_eq_nil101 : ∀ {x : Term}, toList x = [] → x = zero
  | zero, _ => rfl
  | M, h => by rw [show toList M = [M] from rfl] at h; exact absurd h (List.cons_ne_nil _ _)
  | add a b, h => by
      rw [show toList (add a b) = a :: toList b from rfl] at h
      exact absurd h (List.cons_ne_nil _ _)
  | omg a, h => by
      rw [show toList (omg a) = [omg a] from rfl] at h; exact absurd h (List.cons_ne_nil _ _)
  | phi a b, h => by
      rw [show toList (phi a b) = [phi a b] from rfl] at h
      exact absurd h (List.cons_ne_nil _ _)
  | psi k a, h => by
      rw [show toList (psi k a) = [psi k a] from rfl] at h
      exact absurd h (List.cons_ne_nil _ _)
  | Z a, h => by
      rw [show toList (Z a) = [Z a] from rfl] at h; exact absurd h (List.cons_ne_nil _ _)

/-- **橋の只の半分。**  `dict (ofL l)` の成分は必ず `l` の成分の像である。証明は
    `toList (plus s t) = (toList s).filter (·) ++ toList t` の一行 — `plus` は
    **落とすことしかできない**。§93.3 の橋は等号で、`CollapseMono0Hi81` を食うのは
    「何も落ちない」の側だけであって、包含の側ではない。 -/
theorem mem_toList_dict_ofL101 (Hp : PsiIdxOKStd172) :
    ∀ (l : List BT), GoodL77 l → ∀ z ∈ toList (dict (BT.ofL l)), ∃ p ∈ l, z = dict p
  | [], _, z, hz => by
      exact absurd hz (by
        show z ∈ toList (dict BT.zero) → False
        intro hc; exact List.not_mem_nil hc)
  | [p], hg, z, hz => by
      obtain ⟨u, a, rfl⟩ := hg.1 p (List.Mem.head _)
      refine ⟨BT.D u a, List.Mem.head _, ?_⟩
      have h1 : toList (dict (BT.D u a)) = [dict (BT.D u a)] :=
        toList_of_isAP (isAP_dict_D76 u a)
      show z = dict (BT.D u a)
      rw [show BT.ofL [BT.D u a] = BT.D u a from rfl, h1] at hz
      exact List.mem_singleton.mp hz
  | p :: q :: t, hg, z, hz => by
      obtain ⟨u, a, rfl⟩ := hg.1 p (List.Mem.head _)
      have hgt : GoodL77 (q :: t) := goodL77_tail hg
      have hiP : inT (dict (BT.D u a)) = true :=
        (inT_dict_of_std172 Hp (BT.D u a) (hg.2.2.1 _ (List.Mem.head _))
          (hg.2.1 _ (List.Mem.head _))).1
      have hiT : inT (dict (BT.ofL (q :: t))) = true :=
        (inT_dict_of_std172 Hp _ (btLe_ofL77 hgt) (isStd_ofL77 hgt)).1
      obtain ⟨v, b, hq⟩ := hgt.1 q (List.Mem.head _)
      have hnz : dict (BT.ofL (q :: t)) ≠ zero :=
        dict_ne_zero76 Hp _ (btLe_ofL77 hgt) (isStd_ofL77 hgt) (ofL_ne_zero77 ⟨v, b, hq⟩)
      have hne : toList (dict (BT.ofL (q :: t))) ≠ [] := by
        intro hc; exact hnz (toList_eq_nil101 hc)
      cases hcl : toList (dict (BT.ofL (q :: t))) with
      | nil => exact absurd hcl hne
      | cons b1 rest =>
        rw [show BT.ofL (BT.D u a :: q :: t) = BT.sum (BT.D u a) (BT.ofL (q :: t)) from rfl,
          Trans.Dict.dict_sum, toList_plus_inT hiP hiT hcl,
          toList_of_isAP (isAP_dict_D76 u a)] at hz
        rcases List.mem_append.mp hz with h | h
        · exact ⟨BT.D u a, List.Mem.head _, (List.mem_singleton.mp (List.mem_filter.mp h).1)⟩
        · obtain ⟨p', hp', he⟩ := mem_toList_dict_ofL101 Hp (q :: t) hgt z h
          exact ⟨p', List.Mem.tail _ hp', he⟩

/-- 項について。 -/
theorem mem_toList_dict101 (Hp : PsiIdxOKStd172) {a : BT} (hb : btLe72 1 a = true)
    (hs : BT.isStd a = true) : ∀ z ∈ toList (dict a), ∃ p ∈ BT.toL a, z = dict p := by
  intro z hz
  have h := mem_toList_dict_ofL101 Hp (BT.toL a) (good_toL77 a hs hb) z
  rw [ofL_toL77 a hs] at h
  exact h hz

/-- **`hi` の側の包含 — 門なし。** `hi (dict a)` の成分は `a` の添字 1 の成分の像。 -/
theorem mem_toList_hiW_dict101 (Hp : PsiIdxOKStd172) {a : BT} (hb : btLe72 1 a = true)
    (hs : BT.isStd a = true) :
    ∀ z ∈ toList (hiW89 (dict a)), ∃ c : BT, BT.D 1 c ∈ BT.toL a ∧ z = dict (BT.D 1 c) := by
  intro z hz
  have hia := (inT_dict_of_std172 Hp a hb hs).1
  rw [toList_hiW89 hia] at hz
  have hzm := (List.mem_filter.mp hz).1
  have hzf := (List.mem_filter.mp hz).2
  obtain ⟨p, hp, rfl⟩ := mem_toList_dict101 Hp hb hs z hzm
  have hgood : GoodL77 (BT.toL a) := good_toL77 a hs hb
  obtain ⟨u, c, rfl⟩ := hgood.1 p hp
  have he := hiA_dict93 Hp u c (hgood.2.2.1 _ hp) (hgood.2.1 _ hp)
  rw [hzf] at he
  have hu0 : 1 ≤ u := of_decide_eq_true (show hiA93 (BT.D u c) = true from he.symm)
  have hu1 : u ≤ 1 := (btLe72_D 1 u c (hgood.2.2.1 _ hp)).1
  have : u = 1 := by omega
  subst this
  exact ⟨c, hp, rfl⟩

/-- **`lo` の側の包含 — 門なし。** §99.4 はここを `bridge99` (小さい記号数の門) から
    出していたが、そこで使われるのは所属だけである。 -/
theorem mem_toList_loW_dict101 (Hp : PsiIdxOKStd172) {a : BT} (hb : btLe72 1 a = true)
    (hs : BT.isStd a = true) :
    ∀ z ∈ toList (loW89 (dict a)), ∃ c : BT, BT.D 0 c ∈ BT.toL a ∧ z = dict (BT.D 0 c) := by
  intro z hz
  have hia := (inT_dict_of_std172 Hp a hb hs).1
  rw [toList_loW89 hia] at hz
  have hzm := (List.mem_filter.mp hz).1
  have hzf := (List.mem_filter.mp hz).2
  obtain ⟨p, hp, rfl⟩ := mem_toList_dict101 Hp hb hs z hzm
  have hgood : GoodL77 (BT.toL a) := good_toL77 a hs hb
  obtain ⟨u, c, rfl⟩ := hgood.1 p hp
  have he := hiA_dict93 Hp u c (hgood.2.2.1 _ hp) (hgood.2.1 _ hp)
  rw [hzf] at he
  have hu0 : ¬ (1 ≤ u) := of_decide_eq_false (show (decide (1 ≤ u)) = false from he.symm)
  have : u = 0 := by omega
  subst this
  exact ⟨c, hp, rfl⟩

/-- **`K` の条件は `hi` の側の引数に届く — 門も橋も要らない。**  `hi (dict a)` の
    成分は `dict (ψ₁ c)` で、その `c` は `G(a,0)` の元だから `K` の条件で `c < a`。
    §93.2 の `hiStd93` は `BT` の側の話で、これはその 𝔗(M) 側への渡し口の**只の半分**
    である。足りないのは「係数として現れる `ψ₀`-値の引数」の側で、そこは包含では
    届かない (§101.4 の反例はまさにそこで破れている)。 -/
theorem hiArg_lt101 (Hp : PsiIdxOKStd172) {a : BT} (hb : btLe72 1 (BT.D 0 a) = true)
    (hs : BT.isStd (BT.D 0 a) = true) :
    ∀ z ∈ toList (hiW89 (dict a)), ∃ c : BT, BT.lt c a = true ∧ z = dict (BT.D 1 c) := by
  intro z hz
  obtain ⟨c, hmem, he⟩ :=
    mem_toList_hiW_dict101 Hp (btLe72_D 1 0 a hb).2 (isStd_of_D hs) z hz
  exact ⟨c, (std0_split82 hs).2 c (arg_mem_GB0_82 a 1 c hmem), he⟩

/-- 同じことを `lo` の側で。§99.4 の中心の一歩の、門を使わない形。 -/
theorem loArg_lt101 (Hp : PsiIdxOKStd172) {a : BT} (hb : btLe72 1 (BT.D 0 a) = true)
    (hs : BT.isStd (BT.D 0 a) = true) :
    ∀ z ∈ toList (loW89 (dict a)), ∃ c : BT, BT.lt c a = true ∧ z = dict (BT.D 0 c) := by
  intro z hz
  obtain ⟨c, hmem, he⟩ :=
    mem_toList_loW_dict101 Hp (btLe72_D 1 0 a hb).2 (isStd_of_D hs) z hz
  exact ⟨c, (std0_split82 hs).2 c (arg_mem_GB0_82 a 0 c hmem), he⟩

end

/-! ### §101.2 折り畳みの Veblen 枝が潰れるところ -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1)
open TM TM.Term
open Evidence.WF

/-- Veblen 枝が `phiNF` に渡す引数 — `stepF` の定義を写したもの。 -/
def vArg101 (s : Option Term × Option Term) (ac : Term × Term) : Term :=
  plus (match s.2 with | none => baseOf 0 | some v => v)
       (match s.2 with | none => sub1 ac.2 | some _ => ac.2)

/-- 折り畳みが実際に通る (状態, 対) の並び — 添字 0 の場合。 -/
def steps101 (x : Term) : List ((Option Term × Option Term) × (Term × Term)) :=
  scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList x)).1

/-- **その段が潰れるか。** `phiNF α β = β` — `phiNF` はこれを 2 通りでやる。 -/
def collAt101 (p : (Option Term × Option Term) × (Term × Term)) : Bool :=
  !(le (reg 1) p.2.1) && (phiNF p.2.1 (vArg101 p.1 p.2) == vArg101 p.1 p.2)

/-- **どの段も潰れない。** §99 の (b) の候補 — `cexA89` をちょうど落とす。 -/
def foldNF101 (x : Term) : Bool := !((steps101 x).any collAt101)

/-- Rathjen 2.1(vi) の係数条件そのもの — `K_κ γ < γ`。もう一つの候補。 -/
def ksetOK101 (x : Term) : Bool := inT (psi (reg 1) x)

/-- `phiNF` の潰れ方 (1) — Veblen 枝。§81 の `cexA89` が通る道。 -/
theorem phiNF_coll_veblen101 : phiNF TM.Term.one (phi (plus TM.Term.one TM.Term.one) zero)
    = phi (plus TM.Term.one TM.Term.one) zero := rfl

/-- `cexA89` の折り畳みは潰れ、`cexB89` のは潰れない。**検出器は §81 の反例を見る。** -/
theorem veblenColl101 :
    (foldNF101 (hiW89 (dict cexA89)), foldNF101 (hiW89 (dict cexB89)),
     ksetOK101 (hiW89 (dict cexA89)), ksetOK101 (hiW89 (dict cexB89)))
    = (false, true, true, true) := rfl

/-- `ψ₁ψ₁ψ₁0` — 段 1 の塔。`dict` は `ω^(ω^(Ω₁ ⊕ Ω₁))`、対の指数は `Ω₁` で発火する。 -/
def w3_101 : BT := BT.D 1 (BT.D 1 (BT.D 1 BT.zero))
/-- `ψ₁ψ₁0`。 -/
def w2_101 : BT := BT.D 1 (BT.D 1 BT.zero)
/-- `Ω₁ = ψ₁0`。 -/
def w1_101 : BT := BT.D 1 BT.zero

/-- **潰れ方 (2) — 強臨界枝。§81 の反例と違う道で、こちらは組んだ。**
    `a = ψ₁ψ₁ψ₁0 ⊕ ψ₁ψ₀(ψ₁ψ₁ψ₁0 ⊕ ψ₁ψ₁ψ₁0)`。第 1 の対は発火して累算器を
    `ψ_{Ω₁}0` にし、第 2 の対の係数 `ψ_{Ω₁}1` がそれを追い越すので `plus` が
    累算器を落とし、`φ̄₁(ψ_{Ω₁}1) = ψ_{Ω₁}1` になる。 -/
def scBadA101 : BT := BT.sum w3_101 (BT.D 1 (BT.D 0 (BT.sum w3_101 w3_101)))
/-- その相棒 — こちらは `K` 標準。 -/
def scBadB101 : BT := BT.sum w3_101 w3_101

/-- **強臨界枝の潰れ、凍結。** `a` は `BT.isStd` だが `K` 標準でなく、`b` は `K` 標準。
    `hi (dict a) < hi (dict b)` なのに `ψ₀` の値は**同じ**。 -/
theorem scColl101 :
    (btLe72 1 scBadA101, BT.isStd scBadA101, BT.isStd (BT.D 0 scBadA101),
     btLe72 1 scBadB101, BT.isStd scBadB101, BT.isStd (BT.D 0 scBadB101),
     foldNF101 (hiW89 (dict scBadA101)), foldNF101 (hiW89 (dict scBadB101)),
     lt (hiW89 (dict scBadA101)) (hiW89 (dict scBadB101)),
     collapse 0 (hiW89 (dict scBadA101)) == collapse 0 (hiW89 (dict scBadB101)))
    = (true, true, false, true, true, true, false, true, true, true) := rfl

/-- どちらの潰れも `ψ_{Ω₁}(1)` を吐く。 -/
theorem scColl_value101 :
    collapse 0 (hiW89 (dict scBadA101)) = psi (reg 1) TM.Term.one := rfl

end

/-! ### §101.3 手 (i) — 𝔗(M) 側の述語に置き換えた形 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1)
open TM TM.Term
open Evidence.WF

/-- **`HiMono89` の `K` の条件を 𝔗(M) 側の述語 `P` に取り替えた条項。**
    `BT` の側に残るのは形の条件 (`btLe72`・`BT.isStd`) だけで、`K` の条件は
    `P (hi (dict ·))` が担う。**橋はどこにも現れない。** -/
def HiMonoP101 (P : Term → Bool) : Prop :=
  ∀ (a b : BT), btLe72 1 a = true → btLe72 1 b = true →
    BT.isStd a = true → BT.isStd b = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    P (hiW89 (dict a)) = true → P (hiW89 (dict b)) = true →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true

/-- `P` が `K` の条件から出るという条項 — §99 の (a)。 -/
def TransP101 (P : Term → Bool) : Prop :=
  ∀ (a : BT), btLe72 1 (BT.D 0 a) = true → BT.isStd (BT.D 0 a) = true →
    le (reg 1) (dict a) = true → P (hiW89 (dict a)) = true

/-- **手 (i) の形。** (a) と (b) が揃えば `HiMono89` — 橋なしで。 -/
theorem hiMono_of_P101 (P : Term → Bool) (Htr : TransP101 P) (H : HiMonoP101 P) :
    HiMono89 := by
  intro a b hbA hbB hsA hsB hWa hWb hlt
  exact H a b (btLe72_D 1 0 a hbA).2 (btLe72_D 1 0 b hbB).2 (isStd_of_D hsA) (isStd_of_D hsB)
    hWa hWb (Htr a hbA hsA hWa) (Htr b hbB hsB hWb) hlt

/-- **326 行目を任意の適格な `P` に架け替える。** -/
theorem certIn_t326_P101 (Hp : PsiIdxOKStd172) (P : Term → Bool)
    (Htr : TransP101 P) (H : HiMonoP101 P) (HH : DictDenseHi94)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_99 Hp (hiMono_of_P101 P Htr H) HH hacc

end

/-! ### §101.4 否定 — 候補の述語は二つとも足りない、しかも順序が**逆転**する -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1)
open TM TM.Term
open Evidence.WF

/-- `a = ψ₁ψ₁0 ⊕ ψ₁ψ₁0 ⊕ ψ₁ψ₀(ψ₁ψ₁ψ₁0 ⊕ ψ₁0)` — 17 記号。組んだもので、掃いて
    見つけたものではない。累算器を `φ̄₂0` の高さに置き、最後の対の係数がそれを
    追い越すように内側を選んである。 -/
def bothBadA101 : BT :=
  BT.sum w2_101 (BT.sum w2_101 (BT.D 1 (BT.D 0 (BT.sum w3_101 w1_101))))
/-- `b = ψ₁ψ₁ψ₁0 ⊕ ψ₁ψ₀(ψ₁0 ⊕ ψ₁0)` — 12 記号。**こちらは `K` 標準。** -/
def bothBadB101 : BT := BT.sum w3_101 (BT.D 1 (BT.D 0 (BT.sum w1_101 w1_101)))

/-- **§101.4 の反例、凍結。**  仮説はすべて満たし — `foldNF101` も
    `inT (ψ_{Ω₁} ·)` も両辺で真 — `hi (dict a) < hi (dict b)` なのに
    `ψ₀(hi (dict a)) > ψ₀(hi (dict b))`。落ちているのは `a` の `K` の条件ただ一つ。 -/
theorem bothBad101_facts :
    (btLe72 1 bothBadA101, btLe72 1 bothBadB101,
     BT.isStd bothBadA101, BT.isStd bothBadB101,
     le (reg 1) (dict bothBadA101), le (reg 1) (dict bothBadB101),
     foldNF101 (hiW89 (dict bothBadA101)), foldNF101 (hiW89 (dict bothBadB101)),
     ksetOK101 (hiW89 (dict bothBadA101)), ksetOK101 (hiW89 (dict bothBadB101)),
     lt (hiW89 (dict bothBadA101)) (hiW89 (dict bothBadB101)),
     lt (collapse 0 (hiW89 (dict bothBadA101))) (collapse 0 (hiW89 (dict bothBadB101))),
     le (collapse 0 (hiW89 (dict bothBadA101))) (collapse 0 (hiW89 (dict bothBadB101))),
     BT.isStd (BT.D 0 bothBadA101), BT.isStd (BT.D 0 bothBadB101))
    = (true, true, true, true, true, true, true, true, true, true, true,
       false, false, false, true) := rfl

theorem not_hiMonoP101 (P : Term → Bool)
    (hA : P (hiW89 (dict bothBadA101)) = true) (hB : P (hiW89 (dict bothBadB101)) = true) :
    ¬ HiMonoP101 P := by
  intro H
  have h := H bothBadA101 bothBadB101
    (show btLe72 1 bothBadA101 = true from rfl) (show btLe72 1 bothBadB101 = true from rfl)
    (show BT.isStd bothBadA101 = true from rfl) (show BT.isStd bothBadB101 = true from rfl)
    (show le (reg 1) (dict bothBadA101) = true from rfl)
    (show le (reg 1) (dict bothBadB101) = true from rfl) hA hB
    (show lt (hiW89 (dict bothBadA101)) (hiW89 (dict bothBadB101)) = true from rfl)
  rw [show lt (collapse 0 (hiW89 (dict bothBadA101)))
        (collapse 0 (hiW89 (dict bothBadB101))) = false from rfl] at h
  exact Bool.noConfusion h

/-- **候補 1 は足りない。** 折り畳みのどの段も潰れないのに結論が破れる。 -/
theorem not_hiMonoP_foldNF101 : ¬ HiMonoP101 foldNF101 := not_hiMonoP101 foldNF101 rfl rfl

/-- **候補 2 も足りない。** Rathjen 自身の `K_κ γ < γ` でも同じ対が通る。 -/
theorem not_hiMonoP_ksetOK101 : ¬ HiMonoP101 ksetOK101 := not_hiMonoP101 ksetOK101 rfl rfl

/-- **二つ合わせても足りない。** 手 (i) は、この二つより真に強い述語を要る。 -/
theorem not_hiMonoP_both101 : ¬ HiMonoP101 (fun x => foldNF101 x && ksetOK101 x) :=
  not_hiMonoP101 _ rfl rfl

/-- 対照 — 同じ対で `K` の条件は `a` で落ちる。だから `HiMono89` は**反証されていない**。 -/
theorem bothBad_notK101 : BT.isStd (BT.D 0 bothBadA101) = false := rfl

end

/-! ### §101.5 発火だけの折り畳みには Veblen 枝がない — そこは指数の比較そのもの -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1)
open TM TM.Term
open Evidence.WF

/-- どの対も発火する折り畳み。 -/
def allFire101 (x : Term) : Bool :=
  (wcnf (reg 1) (toList x)).1.all (fun ac => le (reg 1) ac.1)

/-- **発火だけなら潰れようがない。** `collAt101` は Veblen 枝の話で、そこには無い。 -/
theorem foldNF_of_allFire101 {x : Term} (h : allFire101 x = true) : foldNF101 x = true := by
  show (!((steps101 x).any collAt101)) = true
  rw [show (steps101 x).any collAt101 = false from ?_]
  · rfl
  · cases hc : (steps101 x).any collAt101 with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨p, hp, hcp⟩ := List.any_eq_true.mp hc
      have hmem : p.2 ∈ (wcnf (reg 1) (toList x)).1 :=
        scanSt_mem_snd (reg 1) (baseOf 0) (none, none) _ p hp
      have hfire : le (reg 1) p.2.1 = true := List.all_eq_true.mp h p.2 hmem
      rw [show collAt101 p = (!le (reg 1) p.2.1 &&
        (phiNF p.2.1 (vArg101 p.1 p.2) == vArg101 p.1 p.2)) from rfl, hfire] at hcp
      exact Bool.noConfusion hcp

/-- `hi` は対の列を変えない — §89.1 の `wcnf_split89` のそのままの読み方。 -/
theorem wcnfFst_hiW101 {x : Term} (hx : inT x = true) :
    (wcnf (reg 1) (toList (hiW89 x))).1 = (wcnf (reg 1) (toList x)).1 := by
  rw [wcnf_split89 hx]

theorem lastFire_hiW101 {x : Term} (hx : inT x = true) :
    lastFire92 (hiW89 x) = lastFire92 x := by
  show (match (wcnf (reg 1) (toList (hiW89 x))).1.reverse with
        | [] => false | ac :: _ => le (reg 1) ac.1) = _
  rw [wcnfFst_hiW101 hx]
  rfl

theorem idxF_hiW101 {x : Term} (hx : inT x = true) :
    idxF88 0 (hiW89 x) = idxF88 0 x := by
  show ((wcnf (reg 1) (toList (hiW89 x))).1.foldl
    (init := ((none : Option Term), (none : Option Term))) (stepF (reg 1) (baseOf 0))).1 = _
  rw [wcnfFst_hiW101 hx]
  rfl

/-- **発火する側では `HiMono89` の結論は崩壊指数の比較そのもの。**  §92.2 の
    `collapse0_hi_psi92` が値を `ψ_{Ω₁}(j)` と名指し、§69.4b の `lt_psi_same` が
    `ψ_{Ω₁}` の単調性を無条件に渡す。**門も橋も要らない。** -/
theorem hiMono_eq_idx101 (Hp : PsiIdxOKStd172) {a b : BT}
    (hba : btLe72 1 a = true) (hsa : BT.isStd a = true)
    (hbb : btLe72 1 b = true) (hsb : BT.isStd b = true)
    (hfa : lastFire92 (dict a) = true) (hfb : lastFire92 (dict b) = true)
    {ja jb : Term} (hja : idxF88 0 (dict a) = some ja) (hjb : idxF88 0 (dict b) = some jb) :
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = lt ja jb := by
  rw [collapse0_hi_psi92 (inT_dict_of_std172 Hp a hba hsa).1 hfa hja,
    collapse0_hi_psi92 (inT_dict_of_std172 Hp b hbb hsb).1 hfb hjb, lt_psi_same]

/-- 崩壊指数の単調性 — §92 が `K` の門のために要ったのと同じ形。 -/
def IdxMono101 : Prop :=
  ∀ (a b : BT) (ja jb : Term), btLe72 1 a = true → btLe72 1 b = true →
    BT.isStd a = true → BT.isStd b = true →
    lastFire92 (dict a) = true → lastFire92 (dict b) = true →
    idxF88 0 (dict a) = some ja → idxF88 0 (dict b) = some jb →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true → lt ja jb = true

/-- **発火する側の `HiMono89` は `IdxMono101` そのもの。** -/
theorem hiMonoFire_of_idxMono101 (Hp : PsiIdxOKStd172) (H : IdxMono101) {a b : BT}
    (hba : btLe72 1 a = true) (hsa : BT.isStd a = true)
    (hbb : btLe72 1 b = true) (hsb : BT.isStd b = true)
    (hfa : lastFire92 (dict a) = true) (hfb : lastFire92 (dict b) = true)
    {ja jb : Term} (hja : idxF88 0 (dict a) = some ja) (hjb : idxF88 0 (dict b) = some jb)
    (hlt : lt (hiW89 (dict a)) (hiW89 (dict b)) = true) :
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true := by
  rw [hiMono_eq_idx101 Hp hba hsa hbb hsb hfa hfb hja hjb]
  exact H a b ja jb hba hbb hsa hsb hfa hfb hja hjb hlt

end

/-! ### §101.6 測定 (凍結)

**構成 — 潰れるように組み、濾さない。** §97・§99 の作り方に倣う。潰れが起こる条件は
「Veblen 段の引数が、その段の指数より高い階の不動点になる」ことなので、母集団は
それを**狙って**作る:

    seedsP101   段 1 の主要項 6 個 (`ψ₁0` から `ψ₁ψ₁ψ₁ψ₁0` まで)
    innerP101   その降べき 2 項和・3 項和も入れた 33 個 — `ψ₀` の引数になる線
    capsP101    `ψ₁ψ₀ z` の形 33 個 — **係数を高い階の不動点にする帽子**
    preP101     前置き 0〜3 成分 (累算器をどこまで上げるかを振る) 19 通り
    candP101    627 項  濾さない

対の母集団は 7 つに 1 つ間引いて `Ω₁ ≤ dict a` で絞った `sampP101` (90 項) と、
その `BT.isStd` な部分 `stdP101` (76 項)。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1)
open TM TM.Term
open Evidence.WF

private def dedupL101 (l : List BT) : List BT :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []
private def everyL101 (k : Nat) (l : List BT) : List BT :=
  (l.zipIdx.filter (fun p => p.2 % k == 0)).map (·.1)

private def seedsP101 : List BT :=
  [w1_101, w2_101, w3_101,
   BT.D 1 (BT.sum w1_101 w1_101),
   BT.D 1 (BT.sum w2_101 w2_101),
   BT.D 1 w3_101]
private def innerP101 : List BT :=
  dedupL101 (seedsP101
    ++ seedsP101.flatMap (fun a => (seedsP101.filter (fun b => BT.le b a)).map (BT.sum a))
    ++ seedsP101.map (fun a => BT.sum a (BT.sum a a)))
private def capsP101 : List BT := innerP101.map (fun z => BT.D 1 (BT.D 0 z))
private def preP101 : List (List BT) :=
  [[]] ++ seedsP101.map (fun p => [p]) ++ seedsP101.map (fun p => [p, p])
       ++ seedsP101.map (fun p => [p, p, p])
private def candP101 : List BT :=
  dedupL101 (preP101.flatMap (fun l => capsP101.map (fun w => BT.ofL (l ++ [w]))))

private def kstdP101 (a : BT) : Bool := btLe72 1 a && BT.isStd a && BT.isStd (BT.D 0 a)
private def hiP101 (a : BT) : Bool := le (reg 1) (dict a)
private def collP101 (a : BT) : Bool := !(foldNF101 (hiW89 (dict a)))

private def sampP101 : List BT := (everyL101 7 candP101).filter hiP101
private def stdP101 : List BT := sampP101.filter (fun a => btLe72 1 a && BT.isStd a)
private def nfP101 : List BT := stdP101.filter (fun a => foldNF101 (hiW89 (dict a)))
private def ksP101 : List BT := stdP101.filter (fun a => ksetOK101 (hiW89 (dict a)))
private def bothP101 : List BT :=
  stdP101.filter (fun a => foldNF101 (hiW89 (dict a)) && ksetOK101 (hiW89 (dict a)))
private def kP101 : List BT := stdP101.filter kstdP101

private def pairsP101 (l : List BT) : List (BT × BT) :=
  l.flatMap (fun a => l.map (fun b => (a, b)))
private def residP101 (l : List BT) : List (BT × BT) :=
  (pairsP101 l).filter (fun p => lt (hiW89 (dict p.1)) (hiW89 (dict p.2)))
private def monoBadP101 (l : List BT) : List (BT × BT) :=
  (residP101 l).filter (fun p =>
    !(lt (collapse 0 (hiW89 (dict p.1))) (collapse 0 (hiW89 (dict p.2)))))

/-! 母集団の形。**627 項のうち 305 項の折り畳みは実際に潰れる** — 濾していない。 -/
#guard (innerP101.length, capsP101.length, preP101.length, candP101.length)
        == (33, 33, 19, 627)

/-! **受領 1 — `K` の条件は、組んだ潰れを一つ残らず落とす。** 627 項のうち
    潰れるのが 305、`K` 標準が 263、**その積は空**。母集団はこの積を作るために
    組んだ (係数を累算器より上げると、それを作る `ψ₀` の引数が項全体を追い越す)
    のであって、掃いて出なかったのではない。 -/
#guard (candP101.countP collP101, candP101.countP kstdP101,
        candP101.countP (fun a => kstdP101 a && collP101 a)) == (305, 263, 0)

/-! **受領 2 — §99 の (a) は候補の二つとも満たす。** 標本の `K` 標準な項では
    `foldNF101` も `inT (ψ_{Ω₁} ·)` も一度も落ちない。**足りないのは (a) ではない。** -/
#guard (sampP101.length, stdP101.length, nfP101.length, ksP101.length,
        bothP101.length, kP101.length) == (90, 76, 45, 55, 42, 39)
#guard (kP101.countP (fun a => !(foldNF101 (hiW89 (dict a)))),
        kP101.countP (fun a => !(ksetOK101 (hiW89 (dict a))))) == (0, 0)

/-! **受領 3 — それでも結論は破れる。** `BT.isStd` な 76 項の 2850 対のうち残余は
    以下のとおりで、破れは述語を強めても**残る**。`K` の条件だけが 0 にする。 -/
#guard ((residP101 stdP101).length, (monoBadP101 stdP101).length) == (2850, 645)
#guard ((residP101 nfP101).length, (monoBadP101 nfP101).length) == (990, 89)
#guard ((residP101 ksP101).length, (monoBadP101 ksP101).length) == (1485, 85)
#guard ((residP101 bothP101).length, (monoBadP101 bothP101).length) == (861, 13)
#guard ((residP101 kP101).length, (monoBadP101 kP101).length) == (741, 0)

/-! **受領 4 — 13 の生き残りの最小が §101.4 の対。** 記号数の和 29。 -/
#guard (monoBadP101 bothP101).all
        (fun p => BT.size p.1 + BT.size p.2 ≥ BT.size bothBadA101 + BT.size bothBadB101)
#guard (BT.size bothBadA101, BT.size bothBadB101) == (17, 12)
#guard (monoBadP101 bothP101).contains (bothBadA101, bothBadB101)

/-! **受領 5 — 帽子つきの 627 項では最後の対は一度も発火しない。** 帽子 `ψ₁ψ₀ z` の
    対の指数は必ず 1 だからで、**§101.4 の破れはすべて Veblen 枝で起きている。** -/
#guard (stdP101.countP (fun a => lastFire92 (dict a)),
        stdP101.countP (fun a => allFire101 (dict a))) == (0, 0)

/-! **受領 6 — §101.5 は空虚ではない。** 帽子を外した第二の母集団 (`fireP101`、
    27 項、すべて `K` 標準) では **14 項で全部の対が発火し**、その 91 の残余の対で
    `HiMono89` の結論は**破れ 0** — §101.5 の同値のとおり `IdxMono101` の側で
    見えている。 -/
private def fireSeedP101 : List BT :=
  [w1_101, w2_101, w3_101, BT.D 1 w3_101,
   BT.D 1 (BT.sum w2_101 w2_101), BT.D 1 (BT.sum w3_101 w3_101)]
private def fireP101 : List BT :=
  (fireSeedP101 ++ fireSeedP101.flatMap
      (fun a => (fireSeedP101.filter (fun b => BT.le b a)).map (BT.sum a))).filter
    (fun a => btLe72 1 a && BT.isStd a && BT.isStd (BT.D 0 a) && le (reg 1) (dict a))
private def fireOnlyP101 : List BT := fireP101.filter (fun a => allFire101 (dict a))
#guard (fireP101.length, fireOnlyP101.length,
        fireP101.countP (fun a => lastFire92 (dict a))) == (27, 14, 14)
#guard ((residP101 fireOnlyP101).length, (monoBadP101 fireOnlyP101).length) == (91, 0)

end

/-! ## §100 EVERY `K`-ELEMENT BELOW `Ω₁` IS FREE, AND THE GATE ASKS ONLY ABOUT `Ω₁` AND ABOVE

§95 took §92's measured residue to zero and then, by BUILDING a family the corpus could not
reach, showed the residue was not empty: **50 obligations survive both §92's clause and §95's,
and every one of them has the same shape** — a term's FIRST firing step, `aV = Ω₁` EXACTLY (so
`subAP Ω₁ aV = 0` and §90.3's exemption cannot fire), the element on the `cV` side, and
`lastFire92` false (so §92.2's road is shut).  At such a step `Δ = cV` and what is being asked
is `K_{Ω₁}(cV) < cV ⊖ 1` — §78's `LocalK2Snd_78` restricted to the steps §90.3 cannot reach.

**§100 proves it, and proves more than the 50 need.**  The 50 all have `y < Ω₁`, and §100
closes that case at EVERY step, with no side condition at all:

    **`lt_idxOf_of_lt_reg100` : at any firing step of any term of the sub-region, every
    element of `K_{Ω₁} aV ∪ K_{Ω₁} cV` that is below `Ω₁` is below the index the step
    emits.  No `lastFire92`, no `aV ⊖ Ω₁ ≠ 0`, no measurement.**

That is §90.3 with its side condition removed, and it is the whole low half of the `K`-gate.
What is left of the gate is one shape: **the elements at or above `Ω₁`.**

THE FIRST HALF IS 2.3.4 AND 2.3.5, READ AT `Ω₁`.  A term `c < Ω₁` of `𝔗(M)` has, in the
`⊕`/`φ̄` decomposition, only `0` and `ψ_{Ω₁}·` at its leaves — `M`, `ω̄^·` and `Zα` are all at or
above `Ω₁`, and 2.3.8 forces the subscript of a `ψ` below `Ω₁` to be `Ω₁` itself.  The argument
of every such leaf is IN `K_{Ω₁} c` (2.2(vi), third branch, because `Ω₁⁻ = 0`), so 2.1(vi)'s own
conjunct — the one that says `ψ_{Ω₁}β` is a term at all — bounds it.  Running 2.3.5 and 2.3.14
down the term then gives

    **`lt_psi_of_kset100` : `y < Ω₁` and `K_{Ω₁} y < B` ⟹ `y < ψ_{Ω₁}B`**  (`ψ` is expansive
    exactly where the formation condition holds), and, with `K` closed under itself
    (`mem_Kset_Kset100`),

    **`ltKset100` : `c < Ω₁` and `c ∈ 𝔗(M)` ⟹ every element of `K_{Ω₁} c` that is below `Ω₁`
    is below `c`.**

`c = ψ_{Ω₁}(Ω₁)` — a genuine `𝔗(M)` term, and `dict (ψ₀ ψ₁(ψ₁ψ₁0 ⊕ ψ₁0))` really is it — has
`K_{Ω₁} c = {Ω₁}` and `Ω₁ > c`, so the `y < Ω₁` hypothesis is NOT decoration.  On the way §100
proves 2.3.4 in the general form the repo did not have (`lt_phi_of_le100`: `γ ≤ α ∨ γ ≤ β ⟹
γ < φ̄αβ` for every term of `𝔗(M)`, not just `CNV` ones).

THE SECOND HALF IS ONE ARITHMETIC IDENTITY.  At `aV = Ω₁` the step's material is
`Δ = (Ω₁·(aV ⊖ Ω₁))·cV = (Ω₁·0)·cV = 0·cV`, and `0·cV` is `cV` only because `ω^(log p) = p`.
That inverse — `logOm` lifts the argument of `φ̄0·` by 2.7's shift and `omegaNF` puts it back —
was not in the repository: `mulL`'s `w = 0` case had never been needed.  §100.2 proves it
(`omegaNF_logOm100`, and `mulL_zero100`, `ddOf_eq_snd100`), and with it `Δ = cV` is a theorem,
not a guard.

WHAT IS PROVED, UNCONDITIONALLY.

  §100.1  **THE LOW PART OF A TERM IS ABOVE ITS OWN `K`.**  `lt_add_nsum100`, `lt_nsum_add100`,
          `lt_M_reg1_false100`, `lt_omg_reg1_false100`, `lt_Z_reg1_false100`,
          `lt_psi_phi_of_le1_100`, `lt_Z_phi_of_le1_100`, `lt_phi_of_le100` (2.3.4, general),
          `kset_psi_reg1_100`, `kset_psi_lo100`, `lt_psi_psi100` (2.3.14, three branches),
          `lt_phi_reg1_100`, `lt_psi_reg1_100`, `lt_psi_of_kset100`, `mem_Kset_Kset100`,
          `ltKset100`, `ltKset_gen100`.

  §100.2  **`0·c = c`, AND THE STEP.**  `take_append_le100`, `length_takeWhile_le100`,
          `phiShifted_zero100`, `dnArg_recount100`, `dnArg_id_of_not_isFP100`,
          `splitFin_succ100`, `omegaNF_logOm100`, `mulL_zero100`, `ddOf_eq_snd100`;
          `mem_Kset_sub1_conv100` (`⊖ 1` does not drop a `K`-element, because what it drops
          is a `1`), `kset_nil_of_subAP_zero100` (`aV ⊖ Ω₁ = 0` ⟹ `K_{Ω₁} aV = ∅`), and the
          main theorem `lt_idxOf_of_lt_reg100`, and its §78 form `localK2Snd_lo100` :
          **the half of `LocalK2Snd_78` that lives below `Ω₁` is a theorem.**

  §100.3  **THE RESIDUE, WITH THE LOW HALF GONE.**  `IdxK100` is `IdxK95` with §90's disjunct
          `lt y Ω₁ = false ∨ subAP Ω₁ aV = 0` replaced by the single `lt y Ω₁ = false` and
          with `zeroFree95` dropped (`0 < Ω₁`, so that case is inside the new theorem).
          `gateStd87_of_idxK100` consumes it at ONE term, `idxStd100_of_step073` is the
          converse (so `IdxStd100` is still EXACTLY the gate), and
          `psiIdxStep073_of_idxStd100` / `certIn_t326_idx100` re-hang row 326 — still on
          `DictLtStd92`, `HiMono89` and `LeIdxSelf95`, and now on `IdxStd100`.

WHAT IS **NOT** CLAIMED.  The gate is NOT closed.  `IdxStd100` is EQUIVALENT to
`PsiIdxStep073`, as `IdxStd95`, `IdxStd92` and `IdxStd90` were.  `LeIdxSelf95`, `HiMono89` and
`DictLtStd92` are untouched and still unproved.  §100 does not touch `LocalK2Snd_78` in full —
it proves the part of it that lives below `Ω₁`, which is what §95's 50 needed, and the `Ω₁ ≤ y`
part of that clause stands.  `IdxLtStd92`, `SplitK86`, `ArgStd87`, `CofDenseS1`, `BCofIn71` are
untouched.  §86's wall stands: `lt_idxOf_of_lt_reg100` compares `y` against `Ω₁`, not against
`i₀` or `Δ`, so it is not a seventh single-summand clause.

WHAT THE MEASUREMENT SAYS (§100.4 gives the construction).  §95's `corpus95` — all 244 terms —
reused verbatim, plus **6 qualifying terms of 9 built for §100** (`slotOK100`), and four more
that qualify for nothing: they are the negatives.  250 terms, 358 firing steps.

  * **§95's 50 go to 0.**  219 obligations under §90's clause, 63 under §92's, 50 under §95's,
    **0 under §100's.**  Of the 219, exactly **50 have `y < Ω₁`** — and those are exactly
    §95's 50.  So §100's exemption does precisely the work its statement claims and no more.
  * **The other 169 are the `Ω₁ ≤ y` shape, and they are not new.**  90 go to §92.1's
    `freePrev92b`, 66 to §92.2's `monoClosed95`, 13 to §95's `freeSelf95`; 3 of the 169 sit at
    a term's first firing step.  **`IdxK100` is therefore not vacuous — it is exactly the
    clause for elements at or above `Ω₁`** — but on this corpus every one of them is already
    discharged, so the measurement CANNOT exhibit a surviving obligation.  That is recorded
    as a limit of the measurement, not as a closure.
  * **`Ω₁ ≤ y` is reachable, and `BT.isStd` is what keeps it out.**  `ehi100 k` has
    `idxF88 0 (dict ·)` NOT below `Ω₁` (`dict (ψ₀ (ehi100 0))` is literally `ψ_{Ω₁}(Ω₁)`), so
    the `K`-element it contributes is at or above `Ω₁`.  `slotHi100 k`, which puts it at an
    `aV = Ω₁` step, satisfies `inT (dict ·)` and `btLe72 1` — and **the gate is FALSE there**
    (`stepOKb` fails) while `BT.isStd (ψ₀ ·)` is false.  Move the same `ψ₀`-argument behind a
    tower (`slotOK100`) and it becomes standard, but then the previous index already covers
    `Ω₁` and §92.1 takes it; the three attempts to lower that tower (`tryA100`, `tryB100`,
    `tryC100`) are all rejected by `BT.isStd`.  **So the `Ω₁ ≤ y` half of the gate is where
    standardness is doing the work, and no clause blind to `BT.isStd` can close it.**
  * **The identity is not a guard.**  `mulL zero z = z` holds at all 498 terms the corpus
    produces, and §100.2 PROVES it — the guard is a check, not a licence.  At all 52 steps
    with `aV ⊖ Ω₁ = 0` the exponent is `Ω₁` exactly and `Δ = cV`, as `ddOf_eq_snd100` says.
  * **The `y < Ω₁` hypothesis of `ltKset100` is real.**  `ψ_{Ω₁}(Ω₁)` is a term of `𝔗(M)`
    below `Ω₁` whose `K_{Ω₁}` is `{Ω₁}` — above itself.  Frozen.
  * **The gate does not fail anywhere in the population.**  `stepOKb`, `idxb84`, `splitb86`,
    `idxLt90b`, `ltArg90b` : 0 failures on all 250.  §100 is not an eighth refutation — the
    one place the gate does fail, `slotHi100`, is outside the population by `BT.isStd`, and
    that is the point.
-/

/-! ### §100.1 `Ω₁` の下では、項は自分の `K` の上にある -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 2.3.10 を `lt` の高さで — 和は頭で決まる (非和の相手ぜんぶ)。 -/
theorem lt_add_nsum100 {a b t : Term} (h0 : t ≠ zero) (ht : NSum t = true) :
    lt (add a b) t = lt a t := by
  have hb := deg_pos b
  show ltF (fuelOf (add a b) t) (add a b) t = _
  rw [show fuelOf (add a b) t = (2 * ((add a b).deg + t.deg) + 7) + 1 from by
      show 2 * ((add a b).deg + t.deg) + 8 = _; omega,
    ltF_succ_add_nsum _ h0 ht]
  exact (lt_eq_ltF a t _
    (by show a.deg + t.deg ≤ 2 * ((1 + a.deg + b.deg) + t.deg) + 7; omega)).symm

/-- 2.3.11 を `lt` の高さで — 非和が和より下なのは頭以下のときだけ。 -/
theorem lt_nsum_add100 {s c d : Term} (h0 : s ≠ zero) (hs : NSum s = true) :
    lt s (add c d) = le s c := by
  have hd := deg_pos d
  show ltF (fuelOf s (add c d)) s (add c d) = _
  rw [show fuelOf s (add c d) = (2 * (s.deg + (add c d).deg) + 7) + 1 from by
      show 2 * (s.deg + (add c d).deg) + 8 = _; omega,
    ltF_succ_nsum_add _ h0 hs]
  rw [show ltF (2 * (s.deg + (add c d).deg) + 7) s c = lt s c from
    (lt_eq_ltF s c _ (by
      show s.deg + c.deg ≤ 2 * (s.deg + (1 + c.deg + d.deg)) + 7; omega)).symm]
  rfl

/-- `Ω₁` は `Z 0`。`M`・`ω̄^·`・`Z ·` はどれも `Ω₁` の下にない。 -/
theorem reg1_eq100 : (reg 1 : Term) = Z zero := rfl

theorem lt_M_reg1_false100 : lt M (reg 1) = false := by
  rw [reg1_eq100]
  show ltF (fuelOf M (Z zero)) M (Z zero) = false
  rw [show fuelOf M (Z zero) = (2 * ((M : Term).deg + (Z zero).deg) + 7) + 1 from by
      show 2 * _ + 8 = _; omega]
  exact ltF_succ_M_Z _ _

theorem lt_omg_reg1_false100 (x : Term) : lt (omg x) (reg 1) = false := by
  rw [reg1_eq100]
  show ltF (fuelOf (omg x) (Z zero)) (omg x) (Z zero) = false
  rw [show fuelOf (omg x) (Z zero)
        = (2 * ((omg x).deg + (Z zero).deg) + 7) + 1 from by
      show 2 * _ + 8 = _; omega]
  exact ltF_succ_omg_Z _ _ _

theorem lt_Z_reg1_false100 (a : Term) : lt (Z a) (reg 1) = false := by
  rw [reg1_eq100]
  by_cases h : a = zero
  · rw [h]; exact lt_irrefl _
  · have hne : (Z a : Term) ≠ Z zero := by
      intro hc; injection hc with h1; exact h h1
    show ltF (fuelOf (Z a) (Z zero)) (Z a) (Z zero) = false
    rw [show fuelOf (Z a) (Z zero)
          = (2 * ((Z a).deg + (Z zero).deg) + 7) + 1 from by
        show 2 * _ + 8 = _; omega,
      ltF_succ_Z_Z _ hne, ltF_right_zero, if_neg (by exact Bool.noConfusion),
      show starF (2 * ((Z a).deg + (Z zero).deg) + 7) zero = zero from rfl,
      show ((Z a : Term) == zero) = false from rfl, ltF_right_zero]
    rfl


/-- `ω̄^x` は `M` の下にない。 -/
theorem lt_omg_M_false100 (x : Term) : lt (omg x) M = false := by
  show ltF (fuelOf (omg x) M) (omg x) M = false
  rw [show fuelOf (omg x) M = (2 * ((omg x).deg + (M : Term).deg) + 7) + 1 from by
      show 2 * _ + 8 = _; omega]
  exact ltF_succ_omg_M _ _

/-- 2.3.4 の第一引数側 — `ψκw ≤ a` なら `ψκw < φ̄ab`。 -/
theorem lt_psi_phi_of_le1_100 {k w a b : Term} (h : le (psi k w) a = true) :
    lt (psi k w) (phi a b) = true := by
  rw [lt_eq_ltF_succ, ltF_succ_psi_phi,
    show ltF (2 * ((psi k w).deg + (phi a b).deg) + 7) (psi k w) a = lt (psi k w) a from
      (lt_eq_ltF (psi k w) a _ (by
        show (1 + k.deg + w.deg) + a.deg
          ≤ 2 * ((1 + k.deg + w.deg) + (1 + a.deg + b.deg)) + 7
        omega)).symm]
  rcases (Bool.or_eq_true _ _).mp h with he | hl
  · rw [he, Bool.true_or, Bool.true_or, Bool.true_or]
  · rw [hl, Bool.or_true, Bool.true_or]

theorem lt_Z_phi_of_le1_100 {e a b : Term} (h : le (Z e) a = true) :
    lt (Z e) (phi a b) = true := by
  rw [lt_eq_ltF_succ, ltF_succ_Z_phi,
    show ltF (2 * ((Z e).deg + (phi a b).deg) + 7) (Z e) a = lt (Z e) a from
      (lt_eq_ltF (Z e) a _ (by
        show (1 + e.deg) + a.deg ≤ 2 * ((1 + e.deg) + (1 + a.deg + b.deg)) + 7
        omega)).symm]
  rcases (Bool.or_eq_true _ _).mp h with he | hl
  · rw [he, Bool.true_or, Bool.true_or, Bool.true_or]
  · rw [hl, Bool.or_true, Bool.true_or]

/-- **§100.1 の第一の道具 — 2.3.4 を一般形で。**  `γ ≤ α ∨ γ ≤ β ⟹ γ < φ̄αβ`。
    repo にあるのは `CNV` 版 (`lt_phi_of_le`) と、`ψ`・`Z` の形だけを見る版で、
    𝔗(M) の項ぜんぶを相手にする形は無かった。 -/
theorem lt_phi_of_le100 : ∀ (n : Nat) (y a b : Term), y.deg ≤ n → inT y = true →
    lt y M = true → inT (phi a b) = true →
    (le y a = true ∨ le y b = true) → lt y (phi a b) = true := by
  intro n
  induction n with
  | zero => intro y a b hn _ _ _ _; exact absurd hn (by have := deg_pos y; omega)
  | succ n ih =>
    intro y a b hn hy hyM hab hle
    have hia : inT a = true := (inT_phi hab).1
    have hib : inT b = true := (inT_phi hab).2
    have hiab : inT (phi a b) = true := hab
    cases y with
    | zero => exact lt_zero_left (by intro hc; exact Term.noConfusion hc)
    | M => rw [lt_irrefl] at hyM; exact absurd hyM Bool.noConfusion
    | omg x => rw [lt_omg_M_false100] at hyM; exact absurd hyM Bool.noConfusion
    | Z d =>
      rcases hle with h | h
      · exact lt_Z_phi_of_le1_100 h
      · exact lt_Z_phi_of_le h
    | psi k w =>
      rcases hle with h | h
      · exact lt_psi_phi_of_le1_100 h
      · exact lt_psi_phi_of_le h
    | add u v =>
      obtain ⟨hapu, hiu, hiv⟩ := Evidence.WF.inT_add hy
      have hdeg : (add u v).deg = 1 + u.deg + v.deg := rfl
      have hlu : le u (add u v) = true := le_left_add97 hy
      have huM : lt u M = true :=
        lt_of_le_of_lt3 (inT_le_fragR _ hiu) (inT_le_fragR _ hy) (inT_le_fragR _ inT_M)
          hlu hyM
      rw [lt_add_phi]
      refine ih u a b (by have h9 := deg_pos v; omega) hiu huM hab ?_
      rcases hle with h | h
      · exact Or.inl (le_trans3 (inT_le_fragR _ hiu) (inT_le_fragR _ hy)
          (inT_le_fragR _ hia) hlu h)
      · exact Or.inr (le_trans3 (inT_le_fragR _ hiu) (inT_le_fragR _ hy)
          (inT_le_fragR _ hib) hlu h)
    | phi u v =>
      obtain ⟨hiu, hiv⟩ := Evidence.WF.inT_phi hy
      have hdeg : (phi u v).deg = 1 + u.deg + v.deg := rfl
      have hdu : u.deg ≤ n := by have h9 := deg_pos v; omega
      have hdv : v.deg ≤ n := by have h9 := deg_pos u; omega
      have huM : lt u M = true := ((Bool.and_eq_true _ _).mp
        ((Bool.and_eq_true _ _).mp (show (inT u && inT v && lt u M && lt v M) = true from hy)).1).2
      have hvM : lt v M = true :=
        ((Bool.and_eq_true _ _).mp (show (inT u && inT v && lt u M && lt v M) = true from hy)).2
      have hua : lt u (phi u v) = true :=
        ih u u v hdu hiu huM hy (Or.inl (Evidence.WF.le_self _))
      have hva : lt v (phi u v) = true :=
        ih v u v hdv hiv hvM hy (Or.inr (Evidence.WF.le_self _))
      have hkill : ∀ w : Term, inT w = true → lt w (phi u v) = true →
          le (phi u v) w = true → False := by
        intro w hiw hw hle2
        rcases (Bool.or_eq_true _ _).mp hle2 with h1 | h1
        · rw [eq_of_beq h1, lt_irrefl] at hw; exact Bool.noConfusion hw
        · rw [lt_asymm3 (inT_le_fragR _ hiw) (inT_le_fragR _ hy) hw] at h1
          exact Bool.noConfusion h1
      by_cases heq : phi u v = phi a b
      · exfalso
        injection heq with h1 h2
        subst h1; subst h2
        rcases hle with h | h
        · exact hkill u hiu hua h
        · exact hkill v hiv hva h
      · rw [lt_phi_phi heq]
        rcases hle with hA | hB
        · by_cases hua2 : u = a
          · exact absurd hA (fun hc => (hkill a hia (by rw [← hua2]; exact hua) hc).elim)
          · rw [if_neg hua2]
            have hlt : lt u a = true :=
              lt_of_lt_of_le3 (inT_le_fragR _ hiu) (inT_le_fragR _ hy)
                (inT_le_fragR _ hia) hua hA
            rw [if_pos hlt]
            have hva2 : lt v a = true :=
              lt_of_lt_of_le3 (inT_le_fragR _ hiv) (inT_le_fragR _ hy)
                (inT_le_fragR _ hia) hva hA
            exact ih v a b hdv hiv hvM hab (Or.inl (le_of_lt hva2))
        · have hvb : lt v b = true :=
            lt_of_lt_of_le3 (inT_le_fragR _ hiv) (inT_le_fragR _ hy)
              (inT_le_fragR _ hib) hva hB
          by_cases hua2 : u = a
          · rw [if_pos hua2]; exact hvb
          · rw [if_neg hua2]
            by_cases hlt : lt u a = true
            · rw [if_pos hlt]
              exact ih v a b hdv hiv hvM hab (Or.inr (le_of_lt hvb))
            · rw [if_neg hlt]; exact hB

/-! `K` の展開と `ψ` どうしの比較 — §100.1 の続き -/

theorem le_zero_right_false100 {x : Term} (h : x ≠ zero) : le x zero = false := by
  show ((x == zero) || lt x zero) = false
  rw [show (x == zero) = false from by
        cases hq : (x == zero) with
        | false => rfl
        | true => exact absurd (eq_of_beq hq) h]
  show (false || ltF (fuelOf x zero) x zero) = false
  rw [ltF_right_zero]; rfl

theorem kminus_reg1_100 : kminus (reg 1) = zero := rfl

/-- `Ω₁` の `K` の展開 — `κ⁻ = 0` なので枝は必ず第三のもの。 -/
theorem kset_psi_reg1_100 (w : Term) :
    Kset (reg 1) (psi (reg 1) w) = w :: (Kset (reg 1) (reg 1) ++ Kset (reg 1) w) := by
  show (if le (psi (reg 1) w) (kminus (reg 1)) then ([] : List Term) else
        if lt (reg 1) (reg 1) then Kset (reg 1) (reg 1) else
        w :: (Kset (reg 1) (reg 1) ++ Kset (reg 1) w)) = _
  rw [kminus_reg1_100,
    le_zero_right_false100 (show (psi (reg 1) w) ≠ zero from by intro hc; exact Term.noConfusion hc),
    lt_irrefl]
  rfl

theorem kset_psi_lo100 {k : Term} (hk : lt k (reg 1) = true) (w : Term) :
    Kset (reg 1) (psi k w) = Kset (reg 1) k := by
  show (if le (psi k w) (kminus (reg 1)) then ([] : List Term) else
        if lt k (reg 1) then Kset (reg 1) k else
        w :: (Kset (reg 1) k ++ Kset (reg 1) w)) = _
  rw [kminus_reg1_100,
    le_zero_right_false100 (show (psi k w) ≠ zero from by intro hc; exact Term.noConfusion hc),
    hk]
  rfl

/-- 2.3.14 を `lt` の高さで、三枝そろえて。 -/
theorem lt_psi_psi100 {k a p b : Term} (h : psi k a ≠ psi p b) :
    lt (psi k a) (psi p b) =
      (if k = p then lt a b
       else if lt k p = true then lt k (psi p b) else lt (psi k a) p) := by
  have hk := deg_pos k; have ha := deg_pos a; have hp := deg_pos p; have hb := deg_pos b
  show ltF (fuelOf (psi k a) (psi p b)) (psi k a) (psi p b) = _
  rw [show fuelOf (psi k a) (psi p b) = (2 * ((psi k a).deg + (psi p b).deg) + 7) + 1 from by
      show 2 * ((psi k a).deg + (psi p b).deg) + 8 = _; omega,
    ltF_succ_psi_psi _ h]
  by_cases hkp : k = p
  · rw [if_pos hkp, if_pos hkp]
    exact (lt_eq_ltF a b _
      (by show a.deg + b.deg ≤ 2 * ((1 + k.deg + a.deg) + (1 + p.deg + b.deg)) + 7; omega)).symm
  · rw [if_neg hkp, if_neg hkp,
      show ltF (2 * ((psi k a).deg + (psi p b).deg) + 7) k p = lt k p from
        (lt_eq_ltF k p _
          (by show k.deg + p.deg ≤ 2 * ((1 + k.deg + a.deg) + (1 + p.deg + b.deg)) + 7;
              omega)).symm]
    by_cases hlt : lt k p = true
    · rw [if_pos hlt, if_pos hlt]
      exact (lt_eq_ltF k (psi p b) _
        (by show k.deg + (1 + p.deg + b.deg)
              ≤ 2 * ((1 + k.deg + a.deg) + (1 + p.deg + b.deg)) + 7; omega)).symm
    · rw [if_neg hlt, if_neg hlt]
      exact (lt_eq_ltF (psi k a) p _
        (by show (1 + k.deg + a.deg) + p.deg
              ≤ 2 * ((1 + k.deg + a.deg) + (1 + p.deg + b.deg)) + 7; omega)).symm

/-- `φ̄uv < Ω₁` はどちらの引数も `Ω₁` より下ということ (2.3.5)。 -/
theorem lt_phi_reg1_100 (u v : Term) :
    lt (phi u v) (reg 1) = (lt u (reg 1) && lt v (reg 1)) := by
  rw [reg1_eq100, lt_eq_ltF_succ, ltF_succ_phi_Z,
    show ltF (2 * ((phi u v).deg + (Z zero).deg) + 7) u (Z zero) = lt u (Z zero) from
      (lt_eq_ltF u (Z zero) _ (by
        show u.deg + (1 + (zero : Term).deg) ≤ 2 * ((1 + u.deg + v.deg) + (1 + (zero : Term).deg)) + 7
        omega)).symm,
    show ltF (2 * ((phi u v).deg + (Z zero).deg) + 7) v (Z zero) = lt v (Z zero) from
      (lt_eq_ltF v (Z zero) _ (by
        show v.deg + (1 + (zero : Term).deg) ≤ 2 * ((1 + u.deg + v.deg) + (1 + (zero : Term).deg)) + 7
        omega)).symm]

/-- `ψκw < Ω₁` なら `κ = Ω₁` か `κ < Ω₁`。`κ` は `Z ·` だから実は前者しかないが、
    ここではどちらでもよい。 -/
theorem lt_psi_reg1_100 {k w : Term} (h : lt (psi k w) (reg 1) = true) :
    k = reg 1 ∨ lt k (reg 1) = true := by
  rw [reg1_eq100, lt_eq_ltF_succ, ltF_succ_psi_Z,
    show starF (2 * ((psi k w).deg + (Z zero).deg) + 7) zero = zero from rfl,
    show ((psi k w) == (zero : Term)) = false from rfl, ltF_right_zero,
    show ltF (2 * ((psi k w).deg + (Z zero).deg) + 7) k (Z zero) = lt k (Z zero) from
      (lt_eq_ltF k (Z zero) _ (by
        show k.deg + (1 + (zero : Term).deg)
          ≤ 2 * ((1 + k.deg + w.deg) + (1 + (zero : Term).deg)) + 7
        omega)).symm] at h
  by_cases hk : (k == (Z zero : Term)) = true
  · exact Or.inl (by rw [reg1_eq100]; exact eq_of_beq hk)
  · rw [show (k == (Z zero : Term)) = false from by
        cases hq : (k == (Z zero : Term)) with
        | false => rfl
        | true => exact absurd hq hk, Bool.false_or] at h
    by_cases hl : lt k (Z zero) = true
    · exact Or.inr (by rw [reg1_eq100]; exact hl)
    · rw [show lt k (Z zero) = false from by
          cases hq : lt k (Z zero) with
          | false => rfl
          | true => exact absurd hq hl] at h
      rw [if_neg (by exact Bool.noConfusion)] at h
      exact absurd h (by rw [Bool.or_self]; exact Bool.noConfusion)


theorem reg1_ne_zero100 : (reg 1 : Term) ≠ zero := by
  rw [reg1_eq100]; intro hc; exact Term.noConfusion hc

theorem nsum_reg1_100 : NSum (reg 1) = true := rfl

/-- **§100.1 の第二の道具 — `ψ_{Ω₁}` は自分の `K` の上に伸びる。**
    `y < Ω₁` で `K_{Ω₁} y` がまるごと `B` より下なら `y < ψ_{Ω₁}B`。
    `y < Ω₁` の項の「葉」は `0` か `ψ_{Ω₁}·` しかなく、その引数はどれも `K_{Ω₁} y`
    に入っている、というのが中身。 -/
theorem lt_psi_of_kset100 : ∀ (n : Nat) (y B : Term), y.deg ≤ n →
    lt y (reg 1) = true → (∀ z ∈ Kset (reg 1) y, lt z B = true) →
    lt y (psi (reg 1) B) = true := by
  intro n
  induction n with
  | zero => intro y B hn _ _; exact absurd hn (by have := deg_pos y; omega)
  | succ n ih =>
    intro y B hn hlo hK
    cases y with
    | zero => exact lt_zero_left (by intro hc; exact Term.noConfusion hc)
    | M => rw [lt_M_reg1_false100] at hlo; exact absurd hlo Bool.noConfusion
    | omg x => rw [lt_omg_reg1_false100] at hlo; exact absurd hlo Bool.noConfusion
    | Z d => rw [lt_Z_reg1_false100] at hlo; exact absurd hlo Bool.noConfusion
    | add u v =>
      have hdeg : (add u v).deg = 1 + u.deg + v.deg := rfl
      rw [lt_add_nsum100 (show (psi (reg 1) B) ≠ zero from by
        intro hc; exact Term.noConfusion hc) (show NSum (psi (reg 1) B) = true from rfl)]
      rw [lt_add_nsum100 reg1_ne_zero100 nsum_reg1_100] at hlo
      refine ih u B (by have h9 := deg_pos v; omega) hlo ?_
      intro z hz
      exact hK z (show z ∈ Kset (reg 1) u ++ Kset (reg 1) v from List.mem_append_left _ hz)
    | phi u v =>
      have hdeg : (phi u v).deg = 1 + u.deg + v.deg := rfl
      rw [lt_phi_reg1_100] at hlo
      obtain ⟨hu, hv⟩ := (Bool.and_eq_true _ _).mp hlo
      refine lt_phi_psi_of (ih u B (by have h9 := deg_pos v; omega) hu ?_)
        (ih v B (by have h9 := deg_pos u; omega) hv ?_)
      · intro z hz
        exact hK z (show z ∈ Kset (reg 1) u ++ Kset (reg 1) v from List.mem_append_left _ hz)
      · intro z hz
        exact hK z (show z ∈ Kset (reg 1) u ++ Kset (reg 1) v from List.mem_append_right _ hz)
    | psi k w =>
      have hdeg : (psi k w).deg = 1 + k.deg + w.deg := rfl
      rcases lt_psi_reg1_100 hlo with hk | hk
      · subst hk
        rw [lt_psi_same]
        exact hK w (by rw [kset_psi_reg1_100]; exact List.Mem.head _)
      · have hne : k ≠ reg 1 := by
          intro hc; rw [hc, lt_irrefl] at hk; exact Bool.noConfusion hk
        have hne2 : psi k w ≠ psi (reg 1) B := by
          intro hc; injection hc with h1 _; exact hne h1
        rw [lt_psi_psi100 hne2, if_neg hne, if_pos hk]
        refine ih k B (by have h9 := deg_pos w; omega) hk ?_
        intro z hz
        exact hK z (by rw [kset_psi_lo100 hk]; exact hz)


/-- **`K` は自分自身で閉じている。**  `y ∈ K_κ x` なら `K_κ y ⊆ K_κ x` — `ψ` の枝が
    引数 `b` を入れるとき `K_κ b` も一緒に入れるから。 -/
theorem mem_Kset_Kset100 {k z : Term} : ∀ (x y : Term), z ∈ Kset k y → y ∈ Kset k x →
    z ∈ Kset k x := by
  intro x
  induction x with
  | zero => intro y _ h; cases h
  | M => intro y _ h; cases h
  | add a b iha ihb =>
    intro y hz hy
    rcases List.mem_append.mp (show y ∈ Kset k a ++ Kset k b from hy) with h | h
    · exact List.mem_append_left _ (iha y hz h)
    · exact List.mem_append_right _ (ihb y hz h)
  | omg a iha => intro y hz hy; exact iha y hz hy
  | phi a b iha ihb =>
    intro y hz hy
    rcases List.mem_append.mp (show y ∈ Kset k a ++ Kset k b from hy) with h | h
    · exact List.mem_append_left _ (iha y hz h)
    · exact List.mem_append_right _ (ihb y hz h)
  | psi p b ihp ihb =>
    intro y hz hy
    show z ∈ (if le (psi p b) (kminus k) then ([] : List Term)
              else if lt p k then Kset k p
              else b :: (Kset k p ++ Kset k b))
    rw [show Kset k (psi p b) = (if le (psi p b) (kminus k) then ([] : List Term)
              else if lt p k then Kset k p
              else b :: (Kset k p ++ Kset k b)) from rfl] at hy
    by_cases h1 : le (psi p b) (kminus k) = true
    · rw [if_pos h1] at hy; cases hy
    · rw [if_neg h1] at hy ⊢
      by_cases h2 : lt p k = true
      · rw [if_pos h2] at hy ⊢; exact ihp y hz hy
      · rw [if_neg h2] at hy ⊢
        rcases List.mem_cons.mp hy with h | h
        · subst h
          exact List.Mem.tail _ (List.mem_append_right _ hz)
        · rcases List.mem_append.mp h with h3 | h3
          · exact List.Mem.tail _ (List.mem_append_left _ (ihp y hz h3))
          · exact List.Mem.tail _ (List.mem_append_right _ (ihb y hz h3))
  | Z a iha => intro y hz hy; exact iha y hz hy

theorem kset_reg1_reg1_100 : Kset (reg 1) (reg 1) = [] := rfl

/-- **§100.1 の主定理 — `Ω₁` の下の項は自分の `K` の上にある。**
    `c < Ω₁` で `c ∈ 𝔗(M)` なら、`K_{Ω₁} c` の元で `Ω₁` より下のものは `c` より下。
    `c = ψ_{Ω₁}(Ω₁)` は `K = {Ω₁}` で結論が偽になる — だから `y < Ω₁` は外せない。 -/
theorem ltKset100 : ∀ (n : Nat) (c : Term), c.deg ≤ n → inT c = true →
    lt c (reg 1) = true → ∀ y, y ∈ Kset (reg 1) c → lt y (reg 1) = true →
    lt y c = true := by
  intro n
  induction n with
  | zero => intro c hn _ _ _ _ _; exact absurd hn (by have := deg_pos c; omega)
  | succ n ih =>
    intro c hn hic hlo y hy hylo
    have hiy : inT y = true := inT_mem_Kset75 c hic (reg 1) y hy
    cases c with
    | zero => cases hy
    | M => cases hy
    | omg x => rw [lt_omg_reg1_false100] at hlo; exact absurd hlo Bool.noConfusion
    | Z d => rw [lt_Z_reg1_false100] at hlo; exact absurd hlo Bool.noConfusion
    | add u v =>
      have hdeg : (add u v).deg = 1 + u.deg + v.deg := rfl
      obtain ⟨hapu, hiu, hiv⟩ := Evidence.WF.inT_add hic
      have hlou : lt u (reg 1) = true := by
        rw [lt_add_nsum100 reg1_ne_zero100 nsum_reg1_100] at hlo; exact hlo
      have hlov : lt v (reg 1) = true :=
        lt_of_le_of_lt3 (inT_le_fragR _ hiv) (inT_le_fragR _ hic)
          (inT_le_fragR _ (inT_reg 1)) (le_right_add97 hic) hlo
      rcases List.mem_append.mp (show y ∈ Kset (reg 1) u ++ Kset (reg 1) v from hy) with h | h
      · exact lt_trans3 (inT_le_fragR _ hiy) (inT_le_fragR _ hiu) (inT_le_fragR _ hic)
          (ih u (by have h9 := deg_pos v; omega) hiu hlou y h hylo) (lt_left_add97 hic)
      · exact lt_trans3 (inT_le_fragR _ hiy) (inT_le_fragR _ hiv) (inT_le_fragR _ hic)
          (ih v (by have h9 := deg_pos u; omega) hiv hlov y h hylo) (lt_right_add97 hic)
    | phi u v =>
      have hdeg : (phi u v).deg = 1 + u.deg + v.deg := rfl
      obtain ⟨hiu, hiv⟩ := Evidence.WF.inT_phi hic
      rw [lt_phi_reg1_100] at hlo
      obtain ⟨hlou, hlov⟩ := (Bool.and_eq_true _ _).mp hlo
      have hyM : lt y M = true :=
        lt_trans3 (inT_le_fragR _ hiy) (inT_le_fragR _ (inT_reg 1)) (inT_le_fragR _ inT_M)
          hylo (ltM_reg 1)
      rcases List.mem_append.mp (show y ∈ Kset (reg 1) u ++ Kset (reg 1) v from hy) with h | h
      · exact lt_phi_of_le100 y.deg y u v (Nat.le_refl _) hiy hyM hic
          (Or.inl (le_of_lt (ih u (by have h9 := deg_pos v; omega) hiu hlou y h hylo)))
      · exact lt_phi_of_le100 y.deg y u v (Nat.le_refl _) hiy hyM hic
          (Or.inr (le_of_lt (ih v (by have h9 := deg_pos u; omega) hiv hlov y h hylo)))
    | psi k w =>
      have hkR : k.isR = true :=
        ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp
          ((Bool.and_eq_true _ _).mp (show (k.isR && inT k && inT w && lt w M
            && (Kset k w).all (fun x => lt x w)) = true from hic)).1).1).1).1
      have hk1 : k = reg 1 := by
        rcases lt_psi_reg1_100 hlo with h | h
        · exact h
        · exfalso
          cases k with
          | Z d => rw [lt_Z_reg1_false100] at h; exact Bool.noConfusion h
          | zero => exact Bool.noConfusion hkR
          | M => exact Bool.noConfusion hkR
          | add _ _ => exact Bool.noConfusion hkR
          | omg _ => exact Bool.noConfusion hkR
          | phi _ _ => exact Bool.noConfusion hkR
          | psi _ _ => exact Bool.noConfusion hkR
      subst hk1
      have hall : ∀ z, z ∈ Kset (reg 1) w → lt z w = true := fun z hz =>
        List.all_eq_true.mp (ksetAll_of_inT_psi hic) z hz
      rw [kset_psi_reg1_100, kset_reg1_reg1_100, List.nil_append] at hy
      rcases List.mem_cons.mp hy with h | h
      · rw [h]
        exact lt_psi_of_kset100 w.deg w w (Nat.le_refl _) (by rw [← h]; exact hylo) hall
      · refine lt_psi_of_kset100 y.deg y w (Nat.le_refl _) hylo ?_
        intro z hz
        exact hall z (mem_Kset_Kset100 w y hz h)


/-- **`Ω₁` の下の元は項そのものより下** — `c < Ω₁` の仮定なしの形。
    `Ω₁ ≤ c` なら `y < Ω₁ ≤ c` で只。 -/
theorem ltKset_gen100 {c y : Term} (hic : inT c = true) (hy : y ∈ Kset (reg 1) c)
    (hylo : lt y (reg 1) = true) : lt y c = true := by
  have hiy : inT y = true := inT_mem_Kset75 c hic (reg 1) y hy
  cases hlo : lt c (reg 1) with
  | true => exact ltKset100 c.deg c (Nat.le_refl _) hic hlo y hy hylo
  | false =>
    exact lt_of_lt_of_le3 (inT_le_fragR _ hiy) (inT_le_fragR _ (inT_reg 1))
      (inT_le_fragR _ hic) hylo (le_of_not_lt3 (inT_le_fragR _ hic) (inT_le_fragR _ (inT_reg 1)) hlo)

end

/-! ### §100.2 係数 `0` の乗算は恒等 — `Δ = cV` -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

theorem take_append_le100 {α : Type} : ∀ (n : Nat) (l1 l2 : List α), n ≤ l1.length →
    (l1 ++ l2).take n = l1.take n := by
  intro n
  induction n with
  | zero => intro l1 l2 _; rfl
  | succ k ih =>
    intro l1 l2 h
    cases l1 with
    | nil => exact absurd h (by simp)
    | cons a t =>
      show a :: (t ++ l2).take k = a :: t.take k
      rw [ih t l2 (by simpa using h)]

theorem phiShifted_zero100 (d : Term) :
    TM.Term.phiShifted zero d = TM.Term.isFP zero (splitFin d).1 := by
  show (TM.Term.isFP zero (splitFin d).1 || (d == zero && (zero : Term).isSC)) = _
  rw [show ((zero : Term).isSC) = false from rfl, Bool.and_false, Bool.or_false]

theorem length_takeWhile_le100 {α : Type} (p : α → Bool) : ∀ (l : List α),
    (l.takeWhile p).length ≤ l.length := by
  intro l
  induction l with
  | nil => exact Nat.le_refl _
  | cons a t ih =>
    by_cases h : p a = true
    · rw [List.takeWhile_cons_of_pos h]
      show (t.takeWhile p).length + 1 ≤ t.length + 1
      omega
    · rw [List.takeWhile_cons_of_neg (by cases hq : p a with
        | false => exact Bool.noConfusion
        | true => exact absurd hq h)]
      exact Nat.zero_le _

/-- `dnArg` の数え直しの枝 — `g` が `ω^·` の不動点なら発火する。 -/
theorem dnArg_recount100 {x g : Term} {k : Nat} (hs : splitFin x = (g, k + 1))
    (h : TM.Term.isFP zero g = true) : dnArg x = plus g (ofNat k) := by
  unfold dnArg
  rw [hs]
  dsimp only
  rw [if_pos (show 1 ≤ k + 1 from by omega), show k + 1 - 1 = k from rfl]
  cases g with
  | zero =>
    rw [show TM.Term.isFP zero (zero : Term) = false from rfl] at h
    exact Bool.noConfusion h
  | add u v =>
    rw [show TM.Term.isFP zero (add u v) = false from rfl] at h
    exact Bool.noConfusion h
  | omg y =>
    rw [show TM.Term.isFP zero (omg y) = false from rfl] at h
    exact Bool.noConfusion h
  | M =>
    refine if_pos ?_
    rw [show TM.Term.isFP zero (M : Term) = (((M : Term).isSC && lt zero M) || false) from rfl,
      Bool.or_false] at h
    exact h
  | psi k' a =>
    refine if_pos ?_
    rw [show TM.Term.isFP zero (psi k' a)
          = (((psi k' a).isSC && lt zero (psi k' a)) || false) from rfl, Bool.or_false] at h
    exact h
  | Z a =>
    refine if_pos ?_
    rw [show TM.Term.isFP zero (Z a) = (((Z a).isSC && lt zero (Z a)) || false) from rfl,
      Bool.or_false] at h
    exact h
  | phi c e =>
    refine if_pos ?_
    rw [show TM.Term.isFP zero (phi c e) = lt zero c from rfl] at h
    exact h

/-- 不動点でなければ `dnArg` は恒等。 -/
theorem dnArg_id_of_not_isFP100 {x g : Term} {m : Nat} (hs : splitFin x = (g, m))
    (h : TM.Term.isFP zero g = false) : dnArg x = x := by
  unfold dnArg
  rw [hs]
  dsimp only
  by_cases hm : 1 ≤ m
  · rw [if_pos hm]
    cases g with
    | zero => exact if_neg (by exact Bool.noConfusion)
    | add u v => exact if_neg (by exact Bool.noConfusion)
    | omg y => exact if_neg (by exact Bool.noConfusion)
    | M =>
      refine if_neg ?_
      rw [show TM.Term.isFP zero (M : Term) = (((M : Term).isSC && lt zero M) || false) from rfl,
        Bool.or_false] at h
      rw [h]; exact Bool.noConfusion
    | psi k' a =>
      refine if_neg ?_
      rw [show TM.Term.isFP zero (psi k' a)
            = (((psi k' a).isSC && lt zero (psi k' a)) || false) from rfl, Bool.or_false] at h
      rw [h]; exact Bool.noConfusion
    | Z a =>
      refine if_neg ?_
      rw [show TM.Term.isFP zero (Z a) = (((Z a).isSC && lt zero (Z a)) || false) from rfl,
        Bool.or_false] at h
      rw [h]; exact Bool.noConfusion
    | phi c e =>
      refine if_neg ?_
      rw [show TM.Term.isFP zero (phi c e) = lt zero c from rfl] at h
      rw [h]; exact Bool.noConfusion
  · rw [if_neg hm]

/-- `d ⊕ 1` の有限部と有限数 — `1` を一つ足すと `m` が一つ増える。 -/
theorem splitFin_succ100 {d : Term} (hd : inT d = true) :
    splitFin (plus d TM.Term.one) = ((splitFin d).1, (splitFin d).2 + 1) := by
  have hl : toList (plus d TM.Term.one) = toList d ++ [TM.Term.one] := by
    have h := toList_plus_ofNat_inT hd 1
    rw [show (ofNat 1 : Term) = TM.Term.one from rfl] at h
    rw [h]; rfl
  have hrev : (toList d ++ [TM.Term.one]).reverse = TM.Term.one :: (toList d).reverse := by
    rw [List.reverse_append]; rfl
  have hm : ((toList d ++ [TM.Term.one]).reverse.takeWhile (fun x => x == TM.Term.one)).length
      = ((toList d).reverse.takeWhile (fun x => x == TM.Term.one)).length + 1 := by
    rw [hrev, List.takeWhile_cons_of_pos (by exact beq_self_eq_true _)]
    show ((toList d).reverse.takeWhile (fun x => x == TM.Term.one)).length + 1 = _
    rfl
  have hlen : (toList d ++ [TM.Term.one]).length = (toList d).length + 1 := by
    rw [List.length_append]; rfl
  have hmle : ((toList d).reverse.takeWhile (fun x => x == TM.Term.one)).length
      ≤ (toList d).length := by
    have h1 := length_takeWhile_le100 (fun x => x == TM.Term.one) (toList d).reverse
    rw [List.length_reverse] at h1
    exact h1
  show (ofList ((toList (plus d TM.Term.one)).take
        ((toList (plus d TM.Term.one)).length
          - ((toList (plus d TM.Term.one)).reverse.takeWhile
              (fun x => x == TM.Term.one)).length)),
      ((toList (plus d TM.Term.one)).reverse.takeWhile (fun x => x == TM.Term.one)).length)
    = _
  rw [hl, hm, hlen,
    show (toList d).length + 1
        - (((toList d).reverse.takeWhile (fun x => x == TM.Term.one)).length + 1)
      = (toList d).length - ((toList d).reverse.takeWhile (fun x => x == TM.Term.one)).length
      from by omega,
    take_append_le100 _ _ _ (by omega)]
  rfl

/-- **§100.2 の算術 — `ω^(log p) = p`。**  `logOm` は `φ̄0·` の引数を `2.7` の
    ずれこみぶんだけ持ち上げ、`omegaNF` はそれをちょうど戻す。repo にはこの逆向きが
    無かった (`mulL` の `w = 0` の場合が誰にも要らなかったから)。 -/
theorem omegaNF_logOm100 {p : Term} (hip : inT p = true) (hap : p.isAP = true)
    (hlt : lt p M = true) : omegaNF (logOm p) = p := by
  cases p with
  | zero => exact Bool.noConfusion hap
  | add u v => exact Bool.noConfusion hap
  | M => rw [lt_irrefl] at hlt; exact absurd hlt Bool.noConfusion
  | omg x =>
    rw [show lt (omg x) M = false from by
      show ltF (fuelOf (omg x) M) (omg x) M = false
      rw [show fuelOf (omg x) M = (2 * ((omg x).deg + (M : Term).deg) + 7) + 1 from by
          show 2 * _ + 8 = _; omega]
      exact ltF_succ_omg_M _ _] at hlt
    exact absurd hlt Bool.noConfusion
  | psi k a =>
    rw [show logOm (psi k a) = psi k a from rfl, omegaNF_eq_gen,
      show lt M (psi k a) = false from by rw [lt_eq_ltF_succ]; exact ltF_succ_M_psi _ _ _,
      if_neg (by exact Bool.noConfusion),
      show TM.Term.isFP zero (psi k a) = (((psi k a).isSC && lt zero (psi k a)) || false)
        from rfl,
      show ((psi k a).isSC && lt zero (psi k a)) = true from by
        rw [show ((psi k a).isSC) = true from rfl,
          lt_zero_left (show (psi k a) ≠ zero from by intro hc; exact Term.noConfusion hc)]
        rfl]
    rfl
  | Z a =>
    rw [show logOm (Z a) = Z a from rfl, omegaNF_eq_gen,
      show lt M (Z a) = false from by rw [lt_eq_ltF_succ]; exact ltF_succ_M_Z _ _,
      if_neg (by exact Bool.noConfusion),
      show TM.Term.isFP zero (Z a) = (((Z a).isSC && lt zero (Z a)) || false) from rfl,
      show ((Z a).isSC && lt zero (Z a)) = true from by
        rw [show ((Z a).isSC) = true from rfl,
          lt_zero_left (show (Z a) ≠ zero from by intro hc; exact Term.noConfusion hc)]
        rfl]
    rfl
  | phi c d =>
    obtain ⟨hic, hid⟩ := Evidence.WF.inT_phi hip
    have hdM : lt d M = true :=
      ((Bool.and_eq_true _ _).mp
        (show (inT c && inT d && lt c M && lt d M) = true from hip)).2
    have hMp : lt M (phi c d) = false := by
      rw [lt_eq_ltF_succ]; exact ltF_succ_M_phi _ _ _
    by_cases hc0 : c = zero
    · subst hc0
      by_cases hsh : TM.Term.phiShifted zero d = true
      · -- 2.7 のずれこみ: logOm = d ⊕ 1
        have hfp : TM.Term.isFP zero (splitFin d).1 = true := by
          rw [← phiShifted_zero100]; exact hsh
        have hlog : logOm (phi zero d) = plus d TM.Term.one := by
          show (if TM.Term.phiShifted zero d = true then plus d TM.Term.one else d) = _
          rw [hsh, if_pos rfl]
        have hdz : d ≠ zero := by
          intro hcc
          rw [hcc] at hsh
          exact Bool.noConfusion
            (show (false : Bool) = true from by
              rw [← hsh]; rw [phiShifted_zero100]; rfl)
        have hpl : inT (plus d TM.Term.one) = true := inT_plus hid inT_one
        have hplM : lt (plus d TM.Term.one) M = true := lt_plus_M hid inT_one hdM lt_one_M
        have hnotFP : TM.Term.isFP zero (plus d TM.Term.one) = false := by
          cases hl : toList d with
          | nil => exact absurd (toList_eq_nil d hl) hdz
          | cons h1 r =>
            have hlp : toList (plus d TM.Term.one) = h1 :: (r ++ [TM.Term.one]) := by
              have h := toList_plus_ofNat_inT hid 1
              rw [show (ofNat 1 : Term) = TM.Term.one from rfl] at h
              rw [h, hl]; rfl
            have hAP : ∀ q ∈ h1 :: (r ++ [TM.Term.one]), q.isAP = true := by
              intro q hq
              exact inTL_isAP hpl q (by rw [hlp]; exact hq)
            have heq : plus d TM.Term.one = add h1 (ofList (r ++ [TM.Term.one])) := by
              rw [← inT_ofList_toList _ hpl, hlp]
              cases r with
              | nil => rfl
              | cons z t => rfl
            rw [heq]
            rfl
        rw [hlog, omegaNF_eq_gen,
          if_neg (by rw [lt_asymm_inT hpl inT_M hplM]; exact Bool.noConfusion),
          if_neg (by rw [hnotFP]; exact Bool.noConfusion),
          dnArg_recount100 (splitFin_succ100 hid) hfp,
          splitFin_rebuild_inT d hid]
      · have hfp : TM.Term.isFP zero (splitFin d).1 = false := by
          rw [← phiShifted_zero100]
          cases hq : TM.Term.phiShifted zero d with
          | false => rfl
          | true => exact absurd hq hsh
        have hlog : logOm (phi zero d) = d := by
          show (if TM.Term.phiShifted zero d = true then plus d TM.Term.one else d) = _
          rw [show TM.Term.phiShifted zero d = false from by
            cases hq : TM.Term.phiShifted zero d with
            | false => rfl
            | true => exact absurd hq hsh, if_neg (by exact Bool.noConfusion)]
        have hnotFP : TM.Term.isFP zero d = false := by
          cases hq : TM.Term.isFP zero d with
          | false => rfl
          | true =>
            exfalso
            have hs0 : (splitFin d).1 = d := by
              cases d with
              | zero => rw [show TM.Term.isFP zero (zero : Term) = false from rfl] at hq
                        exact Bool.noConfusion hq
              | add u v => rw [show TM.Term.isFP zero (add u v) = false from rfl] at hq
                           exact Bool.noConfusion hq
              | omg y => rw [show TM.Term.isFP zero (omg y) = false from rfl] at hq
                         exact Bool.noConfusion hq
              | M => rfl
              | psi k' a => rfl
              | Z a => rfl
              | phi c' e' =>
                show ofList ((toList (phi c' e')).take
                    ((toList (phi c' e')).length
                      - ((toList (phi c' e')).reverse.takeWhile
                          (fun x => x == TM.Term.one)).length)) = _
                rw [show toList (phi c' e') = [phi c' e'] from rfl]
                rw [show ([phi c' e'].reverse.takeWhile (fun x => x == TM.Term.one)).length = 0
                  from by
                    rw [show ([phi c' e'] : List Term).reverse = [phi c' e'] from rfl]
                    rw [show TM.Term.isFP zero (phi c' e') = lt zero c' from rfl] at hq
                    rw [List.takeWhile_cons_of_neg (by
                      cases hb : ((phi c' e' : Term) == TM.Term.one) with
                      | false => exact Bool.noConfusion
                      | true =>
                        exfalso
                        have := eq_of_beq hb
                        injection this with h1 h2
                        rw [h1, lt_irrefl] at hq
                        exact Bool.noConfusion hq)]
                    rfl]
                rfl
            rw [hs0, hq] at hfp
            exact Bool.noConfusion hfp
        rw [hlog, omegaNF_eq_gen,
          if_neg (by rw [lt_asymm_inT hid inT_M hdM]; exact Bool.noConfusion),
          if_neg (by rw [hnotFP]; exact Bool.noConfusion),
          dnArg_id_of_not_isFP100 (show splitFin d = ((splitFin d).1, (splitFin d).2) from rfl)
            hfp]
    · rw [show logOm (phi c d) = phi c d from
        logOm_eq_self_of_ne (phi c d) (by
          intro b hcc
          injection hcc with h1 _
          exact hc0 h1),
        omegaNF_eq_gen, if_neg (by rw [hMp]; exact Bool.noConfusion),
        show TM.Term.isFP zero (phi c d) = lt zero c from rfl,
        if_pos (lt_zero_left hc0)]

/-- 各成分で恒等なら写像は恒等。 -/
theorem map_self_of_all100 {α : Type} (f : α → α) : ∀ (l : List α),
    (∀ x ∈ l, f x = x) → l.map f = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    show f a :: t.map f = a :: t
    rw [h a (List.Mem.head _), ih (fun x hx => h x (List.Mem.tail _ hx))]

/-- **§100.2 の主定理 — 係数 `0` の乗算は恒等。**  `Δ = W^(aV ⊖ W)·cV` は
    `aV = Ω₁` ちょうどの歩で `cV` そのものになる。 -/
theorem mulL_zero100 {z : Term} (hz : inT z = true) (hlz : lt z M = true) :
    mulL zero z = z := by
  show ofList ((toList z).map (fun p => omegaNF (plus zero (logOm p)))) = z
  rw [map_self_of_all100 _ (toList z) ?_, inT_ofList_toList z hz]
  intro q hq
  have hiq : inT q = true := inTL_inT hz q hq
  have hapq : q.isAP = true := inTL_isAP hz q hq
  have hlq : lt q M = true := ltM_toList z hz hlz q hq
  rw [plus_zero_left_inT (inT_logOm hiq)]
  exact omegaNF_logOm100 hiq hapq hlq

/-- **`aV ⊖ Ω₁ = 0` の歩では `Δ = cV`。** -/
theorem ddOf_eq_snd100 {ac : Term × Term} (h3 : inT ac.2 = true) (hl3 : lt ac.2 M = true)
    (hs : subAP (reg 1) ac.1 = zero) : ddOf75 (reg 1) ac = ac.2 := by
  show mulL (mulL (reg 1) (subAP (reg 1) ac.1)) ac.2 = ac.2
  rw [hs, show mulL (reg 1) (zero : Term) = zero from rfl]
  exact mulL_zero100 h3 hl3

theorem kset_one100 : Kset (reg 1) TM.Term.one = [] := rfl

/-- `⊖ 1` は `K` を落とさない — 落ちる成分は `1` で、`K_{Ω₁} 1 = ∅` だから。 -/
theorem mem_Kset_sub1_conv100 {c y : Term} (hy : y ∈ Kset (reg 1) c) :
    y ∈ Kset (reg 1) (sub1 c) := by
  cases hl : toList c with
  | nil =>
    exfalso
    rw [toList_eq_nil c hl] at hy; cases hy
  | cons p rest =>
    have hs : sub1 c = (if p == TM.Term.one then ofList rest else c) := by
      show (match toList c with
            | [] => zero
            | q :: r => if q == TM.Term.one then ofList r else c) = _
      rw [hl]
    by_cases hp : (p == TM.Term.one) = true
    · rw [hs, if_pos hp, Kset_ofList]
      rw [Kset_eq_KsetL, hl] at hy
      rcases List.mem_append.mp
        (show y ∈ Kset (reg 1) p ++ KsetL (reg 1) rest from hy) with h | h
      · rw [eq_of_beq hp, kset_one100] at h; cases h
      · exact h
    · rw [hs, if_neg hp]; exact hy

/-- **§100.2 の主定理 — 係数がそのまま `Δ` になる歩では、`Ω₁` より下の `K_{Ω₁} cV` の
    元はぜんぶ只。**  §90.3 は `aV ⊖ Ω₁ ≠ 0` の歩しか届かず、`aV = Ω₁` ちょうどの歩を
    残していた。そこが §95 の残余 50 のいる場所である。 -/
theorem lt_idxOf_of_ltReg_eq100 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (h1 : inT ac.1 = true) (h3 : inT ac.2 = true)
    (hdd : ddOf75 (reg 1) ac = ac.2) {y : Term}
    (hy : y ∈ Kset (reg 1) ac.2) (hlt : lt y (reg 1) = true)
    (hidxT : inT (idxOf (reg 1) s ac) = true) :
    lt y (idxOf (reg 1) s ac) = true := by
  have hiy : inT y = true := inT_mem_Kset75 ac.2 h3 (reg 1) y hy
  have hdT : inT (ddOf75 (reg 1) ac) = true := inT_ddOf75 (inT_reg 1) h1 h3
  have hsT : inT (sub1 (ddOf75 (reg 1) ac)) = true := inT_sub1 hdT
  have hstep : lt y (sub1 (ddOf75 (reg 1) ac)) = true := by
    rw [hdd]
    exact ltKset_gen100 (inT_sub1 h3) (mem_Kset_sub1_conv100 hy) hlt
  exact lt_of_lt_of_le3 (inT_le_fragR _ hiy) (inT_le_fragR _ hsT) (inT_le_fragR _ hidxT)
    hstep (le_sub1dd_idxOf75 (inT_reg 1) hst h1 h3)

/-- `subAP Ω₁ h = 0` なら `K_{Ω₁} h` は空 — `h` は `0` か `Ω₁` そのもの。 -/
theorem kset_nil_of_subAP_zero100 {h : Term} (hh : inT h = true)
    (hs : subAP (reg 1) h = zero) {y : Term} (hy : y ∈ Kset (reg 1) h) : False := by
  cases hl : toList h with
  | nil => rw [toList_eq_nil h hl] at hy; cases hy
  | cons p rest =>
    have h1 : (if p == reg 1 then ofList rest else h) = zero := by
      rw [show subAP (reg 1) h = (match toList h with
            | [] => zero
            | q :: r => if q == reg 1 then ofList r else h) from rfl, hl] at hs
      exact hs
    by_cases hp : (p == reg 1) = true
    · rw [if_pos hp] at h1
      have hr : rest = [] := by
        cases rest with
        | nil => rfl
        | cons a t =>
          exfalso
          cases t with
          | nil =>
            have hap : a.isAP = true := inTL_isAP hh a (by rw [hl]; exact List.Mem.tail _ (List.Mem.head _))
            rw [show ofList [a] = a from rfl] at h1
            rw [h1] at hap
            exact Bool.noConfusion hap
          | cons b u =>
            rw [show ofList (a :: b :: u) = add a (ofList (b :: u)) from rfl] at h1
            exact Term.noConfusion h1
      have hhe : h = reg 1 := by
        rw [← inT_ofList_toList h hh, hl, hr, eq_of_beq hp]
        rfl
      rw [hhe, kset_reg1_reg1_100] at hy
      cases hy
    · rw [if_neg hp] at h1
      rw [h1] at hl
      exact List.cons_ne_nil p rest (by rw [← hl]; rfl)



/-- **§100.2 の主定理 — `Ω₁` の下の `K` の元は、どの歩でも只。**
    §90.3 は `aV ⊖ Ω₁ ≠ 0` の歩にしか届かなかった。残っていた `aV = Ω₁` ちょうどの歩では
    `Δ = cV` (§100.2 の算術) で、`K_{Ω₁} aV` は空、`K_{Ω₁} cV` の元は §100.1 が片づける。
    **側条件はいっさい無い。** -/
theorem lt_idxOf_of_lt_reg100 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hl3 : lt ac.2 M = true)
    (hz : ac.2 ≠ zero) {y : Term}
    (hy : y ∈ Kset (reg 1) ac.1 ∨ y ∈ Kset (reg 1) ac.2)
    (hyi : inT y = true) (hlt : lt y (reg 1) = true)
    (hidxT : inT (idxOf (reg 1) s ac) = true) :
    lt y (idxOf (reg 1) s ac) = true := by
  by_cases hsub : subAP (reg 1) ac.1 = zero
  · rcases hy with hy1 | hy2
    · exact (kset_nil_of_subAP_zero100 h1 hsub hy1).elim
    · exact lt_idxOf_of_ltReg_eq100 hst h1 h3 (ddOf_eq_snd100 h3 hl3 hsub) hy2 hlt hidxT
  · exact lt_idxOf_of_lt_reg90 hst h1 h3 hz hsub hyi hlt hidxT


/-- **§78 の `LocalK2Snd_78` の、`Ω₁` より下の半分は定理。**  §95 の残る 50 は
    ちょうどこの形だった。残るのは `Ω₁ ≤ y` の半分である。 -/
theorem localK2Snd_lo100 {ac : Term × Term} (h1 : inT ac.1 = true) (hl1 : lt ac.1 M = true)
    (h3 : inT ac.2 = true) (hl3 : lt ac.2 M = true) (hz : ac.2 ≠ zero) {y : Term}
    (hy : y ∈ Kset (reg 1) ac.1 ∨ y ∈ Kset (reg 1) ac.2) (hlt : lt y (reg 1) = true) :
    lt y (ddOf75 (reg 1) ac) = true := by
  have hyi : inT y = true := by
    rcases hy with h | h
    · exact inT_mem_Kset75 ac.1 h1 (reg 1) y h
    · exact inT_mem_Kset75 ac.2 h3 (reg 1) y h
  have hdT : inT (ddOf75 (reg 1) ac) = true := inT_ddOf75 (inT_reg 1) h1 h3
  have hidxT : inT (idxOf (reg 1) ((none : Option Term), (none : Option Term)) ac) = true :=
    (inT_idxOf mulDescInT (inT_reg 1) (ltM_reg 1) stInv_none h1 hl1 h3 hl3).1
  have hstep :
      lt y (idxOf (reg 1) ((none : Option Term), (none : Option Term)) ac) = true :=
    lt_idxOf_of_lt_reg100 stInv_none h1 h3 hl3 hz hy hyi hlt hidxT
  have hidxe : idxOf (reg 1) ((none : Option Term), (none : Option Term)) ac
      = sub1 (ddOf75 (reg 1) ac) := rfl
  rw [hidxe] at hstep
  exact lt_of_lt_of_le3 (inT_le_fragR _ hyi) (inT_le_fragR _ (inT_sub1 hdT))
    (inT_le_fragR _ hdT) hstep (le_sub1_self75 hdT)

end

/-! ### §100.3 条項 — 残るのは `Ω₁` 以上の元だけ -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§100 の条項。** §95 の `IdxK95` から
    (i) §90 の選言 `lt y Ω₁ = false ∨ subAP Ω₁ aV = 0` を `lt y Ω₁ = false` ひとつに縮め、
    (ii) `zeroFree95` の側条件を落とした (`0 < Ω₁` だから新しい定理の中にある) 形。
    落としたものはどれも定理だから、門との同値は保たれる
    (`idxStd100_of_step073` が逆向き)。 -/
def IdxK100 (a : BT) : Prop :=
  ∀ p ∈ scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1,
    le (reg 1) p.2.1 = true → inT (idxOf (reg 1) p.1 p.2) = true →
      ∀ (y : Term) (c e : BT) (j : Term),
        BT.D 1 c ∈ BT.toL a → BT.isStd (BT.D 1 c) = true → BT.lt c a = true →
        e ∈ d0Args88 c → BT.isStd (BT.D 0 e) = true → btLe72 1 e = true →
        BT.lt e a = true → BT.size e < BT.size a →
        idxF88 0 (dict e) = some j → inT j = true → inT (psi (reg 1) j) = true →
        le y j = true → inT y = true → y ∈ Kset (reg 1) (dict c) →
        lt y (reg 1) = false →
        (∀ i0, p.1.1 = some i0 → lt i0 y = true) →
        monoClosed95 a p e = false → freeSelf95 p e = false →
        (y ∈ Kset (reg 1) p.2.1 ∨ y ∈ Kset (reg 1) p.2.2) →
        lt y (idxOf (reg 1) p.1 p.2) = true

/-- §95 の条項は §100 の条項を出す — 仮説が減っただけだから。 -/
theorem idxK100_of_idxK95 {a : BT} (H : IdxK95 a) : IdxK100 a := by
  intro p hp hle hidxT y c e j hc hstd hltc he hse hbe hlte hsz hj hjT hpsiT hlej hyT hyk hlo
    hgt hmono hsf hy
  refine H p hp hle hidxT y c e j hc hstd hltc he hse hbe hlte hsz hj hjT hpsiT hlej hyT hyk
    (Or.inl hlo) hgt hmono hsf ?_ hy
  show ((y == zero) && !(idxOf (reg 1) p.1 p.2 == zero)) = false
  rw [show (y == zero) = false from by
    cases hq : (y == zero) with
    | false => rfl
    | true =>
      exfalso
      rw [eq_of_beq hq] at hlo
      rw [lt_zero_left (show (reg 1 : Term) ≠ zero from reg1_ne_zero100)] at hlo
      exact Bool.noConfusion hlo]
  rfl

/-- **§100 の残る仮説。** 部分領域の項について §100 の条項。**証明しない。** -/
def IdxStd100 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → IdxK100 a

/-- **§100.3 の主定理。** 一項ぶんの門は §100 の条項と、326 行目が既に抱えている
    二つの条項と、§95 が名指しした算術ひとつから出る。 -/
theorem gateStd87_of_idxK100 (HD : DictLtStd92) (HM : HiMono89) (HL : LeIdxSelf95) (a : BT)
    (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b)
    (H : btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → IdxK100 a) : GateStd87 a := by
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
    cases hlty : lt y (reg 1) with
    | true => exact lt_idxOf_of_lt_reg100 hst hi1 hi2 hl2 hnz2 hy hyT hlty hidxT
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
      exact H hb hs q hq hle2 hidxT y c e j hc hstd hltc he hse hbe hlte hsze
        hj hjT hpsiT hlej hyT hyk hlty hgt hmono hsf hy
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

/-- **§100 の第一の結論。** -/
theorem psiIdxStep073_of_idxStd100 (HD : DictLtStd92) (HM : HiMono89) (HL : LeIdxSelf95)
    (H : IdxStd100) : PsiIdxStep073 :=
  step073_of_gate87 (fun a ih => gateStd87_of_idxK100 HD HM HL a ih (fun hb hs => H a hb hs))

/-- **逆向き。** 足した仮説も外した義務もすべて落ちるので、分解は過不足がない。 -/
theorem idxStd100_of_step073 (H : PsiIdxStep073) : IdxStd100 := by
  intro a hb hs p hp hle
  intro _ y _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hy
  exact (H a hb hs p hp hle).2 y hy

/-- **§100 の第二の結論。** 326 行目の証明書が `K` の側で待つのは §100 の条項ひとつと、
    §74/§89 が既に名指ししている二つと、§95 が名指しした算術ひとつである。 -/
theorem certIn_t326_idx100 (HD : DictLtStd92) (HM : HiMono89) (HL : LeIdxSelf95)
    (H : IdxStd100) (HDe : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_step73 (psiIdxStep073_of_idxStd100 HD HM HL H) HDe HI HC hacc

end

/-! ### §100.4 測定 (凍結) -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- §100 の条項が訊く組 — §92.1・§92.2・§95 の `freeSelf95` と §100 の
    「`Ω₁` より下」を引いたもの。`zeroFree95` は要らない (`0 < Ω₁`)。 -/
def oblPost100 (a : BT) :
    List (((Option Term × Option Term) × (Term × Term)) × Term × BT × Term) :=
  (oblPre92 a).filter fun w =>
    !(freePrev92b w.1 w.2.1) && !(monoClosed95 a w.1 w.2.2.1) && !(freeSelf95 w.1 w.2.2.1)
      && !(lt w.2.1 (reg 1))

/-- 崩壊指数が `Ω₁` 以上になる `ψ₀` の引数。`dict (ψ₀ (ehi100 0)) = ψ_{Ω₁}(Ω₁)`。 -/
def ehi100 (k : Nat) : BT := BT.D 1 (BT.sum (BT.D 1 (BT.D 1 BT.zero)) (twr86 (k+1)))

/-- それを `aV = Ω₁` ちょうどの成分に差し込んだもの。**標準ではない。** -/
def slotHi100 (k : Nat) : BT := BT.D 1 (BT.sum (BT.D 1 (BT.D 1 BT.zero)) (BT.D 0 (ehi100 k)))

/-- 同じものを塔の後ろに置いたもの。**標準で、門も落ちない** — 直前の指数が `Ω₁` を
    覆うから。 -/
def slotOK100 (n k : Nat) : BT := BT.sum (twr86 (n+4)) (slotHi100 k)

/-- 直前の指数を小さくして §92.1 を外そうとした三つ。**どれも標準でない。** -/
def tryA100 (k : Nat) : BT := BT.sum (twr86 3) (slotHi100 k)
def tryB100 (k : Nat) : BT := BT.sum (slotHi100 k) (twr86 3)
def tryC100 (k : Nat) : BT := BT.D 1 (BT.sum (BT.D 1 (BT.D 1 BT.zero))
  (BT.sum (BT.D 0 (ehi100 k)) (BT.D 0 BT.zero)))

def pop100 : List BT :=
  ((List.range 3).flatMap fun n => (List.range 3).map fun k => slotOK100 n k).eraseDups
def qual100 : List BT := pop100.filter okHyp84

/-- 測る母集団ぜんぶ — §95 の 244 項に §100 の 6 項を足したもの。 -/
def corpus100 : List BT := corpus95 ++ qual100

-- 母集団の大きさと形。
#guard (pop100.length, qual100.length, corpus100.length) == (9, 6, 250)

/-! **肯定 — §95 の残余 50 は 0 になる。**  219 の義務のうち 90 は §92.1、66 は §92.2、
13 は §95、そして残る 50 は §100 が持っていく。 -/

#guard ((corpus100.flatMap oblPre92).length, (corpus100.flatMap oblPost92).length,
        (corpus100.flatMap oblPost95).length,
        (corpus100.flatMap oblPost100).length) == (219, 63, 50, 0)

/-! **§95 の残余 50 は、ちょうど「`Ω₁` より下」の 50 である。**  §100 の免除は
その 50 に効いて、それ以外には効かない。 -/

#guard
  (let o := corpus100.flatMap fun a => (oblPre92 a).map fun w => (a, w)
   (o.length,
    (o.countP fun w => lt w.2.2.1 (reg 1)),
    (o.countP fun w => !(lt w.2.2.1 (reg 1))))) == (219, 50, 169)
#guard
  (let o := corpus100.flatMap fun a => (oblPost95 a).map fun w => (a, w)
   (o.length, (o.countP fun w => lt w.2.2.1 (reg 1)))) == (50, 50)

/-! **残る形は `Ω₁ ≤ y` ただ一つ、そしてこの母集団ではそれが立ったままにならない。**
169 の義務のうち 90 は §92.1、66 は §92.2、13 は §95 が持っていく。3 つは最初の発火歩に
ある。**だから `IdxK100` は空虚ではない — 測定が生き残りを出せないだけである。** -/

#guard
  (let o := corpus100.flatMap fun a => (oblPre92 a).map fun w => (a, w)
   let hi := o.filter fun w => !(lt w.2.2.1 (reg 1))
   (hi.length,
    (hi.countP fun w => w.2.1.1.1 == none),
    (hi.countP fun w => freePrev92b w.2.1 w.2.2.1),
    (hi.countP fun w => !(freePrev92b w.2.1 w.2.2.1) && monoClosed95 w.1 w.2.1 w.2.2.2.1),
    (hi.countP fun w => !(freePrev92b w.2.1 w.2.2.1) && !(monoClosed95 w.1 w.2.1 w.2.2.2.1)
        && freeSelf95 w.2.1 w.2.2.2.1))) == (169, 3, 90, 66, 13)

/-! **否定 — `Ω₁ ≤ y` は届く形で、そこを止めているのは `BT.isStd` である。**
`ehi100 k` の崩壊指数は `Ω₁` の下にない。だから `dict (ψ₀ (ehi100 k))` の `K_{Ω₁}` は
`Ω₁` 以上の元を持つ。それを `aV = Ω₁` ちょうどの成分に置いた `slotHi100 k` は
`inT (dict ·)` を満たし、**門はそこで落ちる** — そして `BT.isStd (ψ₀ ·)` が偽である。
標準性を見ない条項では `Ω₁ ≤ y` の側は閉じない。 -/

#guard (List.range 4).all fun k =>
  match idxF88 0 (dict (ehi100 k)) with
  | none => false
  | some j => !(lt j (reg 1)) && inT j
#guard dict (BT.D 0 (ehi100 0)) == psi (reg 1) (reg 1)
#guard (List.range 4).all fun k =>
  inT (dict (slotHi100 k)) && btLe72 1 (slotHi100 k)
    && !(BT.isStd (BT.D 0 (slotHi100 k))) && !(stepOKb 0 (dict (slotHi100 k)))
    && !(okHyp84 (slotHi100 k))

/-! **同じ引数を標準な項に移すと、直前の指数が `Ω₁` を覆ってしまう。**  `slotOK100` は
標準で門も落ちない。前に置く塔を低くして §92.1 を外そうとした三つは、どれも標準でない。 -/

#guard (List.range 2).all fun k =>
  okHyp84 (slotOK100 0 k) && stepOKb 0 (dict (slotOK100 0 k))
#guard (List.range 2).all fun k =>
  !(okHyp84 (tryA100 k)) && !(okHyp84 (tryB100 k)) && !(okHyp84 (tryC100 k))
#guard (List.range 2).all fun k =>
  inT (dict (tryA100 k)) && inT (dict (tryB100 k)) && inT (dict (tryC100 k))
    && !(BT.isStd (BT.D 0 (tryA100 k))) && !(BT.isStd (BT.D 0 (tryB100 k)))
    && !(BT.isStd (BT.D 0 (tryC100 k)))

/-! **`0·c = c` は測定ではなく定理 (§100.2)。** 母集団の 498 項での確認。 -/

#guard
  (let zs := ((corpus100.flatMap fun a => (fireSt90 a).map fun p => p.2.2)
                ++ (corpus100.flatMap fun a => (fireSt90 a).map fun p => p.2.1)
                ++ (corpus100.map dict)
                ++ (corpus100.flatMap fun a => (BT.toL a).map dict)).eraseDups
   (zs.length, zs.countP fun z => !((mulL zero z == z)))) == (498, 0)

/-! **`aV ⊖ Ω₁ = 0` の歩ではいつも `aV = Ω₁` ちょうどで `Δ = cV`** — §100.2 の
`ddOf_eq_snd100` の確認。母集団の 358 の発火歩のうち 52 がそれ。 -/

#guard
  (let ps := corpus100.flatMap fireSt90
   (ps.length,
    (ps.countP fun p => subAP (reg 1) p.2.1 == zero),
    (ps.countP fun p => (subAP (reg 1) p.2.1 == zero) && !((p.2.1 == reg 1))),
    (ps.countP fun p => (subAP (reg 1) p.2.1 == zero)
        && !((ddOf75 (reg 1) p.2 == p.2.2))))) == (358, 52, 0, 0)

/-! **門はどこでも落ちない。** §100 は八つ目の反証を出していない (標準でない
`slotHi100` を除く — あれは母集団の外である)。 -/

#guard ((corpus100.filter fun a => !(stepOKb 0 (dict a))).length,
        (corpus100.filter fun a => !(idxb84 0 (dict a))).length,
        (corpus100.filter fun a => !(splitb86 0 (dict a))).length,
        (corpus100.filter fun a => !(idxLt90b a)).length,
        (corpus100.filter fun a => !(ltArg90b a)).length) == (0, 0, 0, 0, 0)

/-! **`ltKset100` の `y < Ω₁` は飾りではない。** `ψ_{Ω₁}(Ω₁)` は `𝔗(M)` の項で
`Ω₁` の下にあるが、その `K_{Ω₁}` は `Ω₁` — 自分より上である。 -/

#guard inT (psi (reg 1) (reg 1)) && lt (psi (reg 1) (reg 1)) (reg 1)
        && (Kset (reg 1) (psi (reg 1) (reg 1)) == [reg 1])
        && !(lt (reg 1) (psi (reg 1) (reg 1)))

end

/-! ## §102 `cof_eps0` ONE AND TWO LEVELS UP — THE `Γ₁` COFINALITY CLAUSE IS A THEOREM

§98 reduced the high half of row 326's density gate, below `Γ₁`, to ONE named clause and
left it as a hypothesis:

> `CofGam1_98` : every term of 𝔗(M) in `[Γ₀, Γ₁)` is at or below some rung of the raw
> tower `rawT94` — the `Γ₁` analogue of §9's `cof_eps0`.

and it said, in its own words, why it stopped there:

> `WF.lean` §15's combinators only climb `φ̄ a ·` in the SECOND argument; the tower climbs
> in the FIRST (`TM/FS.lean`'s `iterGamma`), and there is no Evidence-level cofinality
> theorem for it.

**§102 builds the first-argument climb, and `CofGam1_98` is now a theorem
(`CofGam1_102`).**  It costs one structural induction and eleven clause-readings of 2.3.
No `Frag`, no transitivity, no comparability — for exactly §9's reason: §7 has to compare
two arbitrary terms, §9 and §102 only have to compare an arbitrary term with a tower.

WHAT MADE IT SHORT.  §9's shape analysis is "a term below `ε₀` is a CNF term".  The
analogue here is read off 2.3 the same way and is nearly as small: a term of 𝔗(M) below
`ψ_Ω(q)` is built from `0`, `⊕` and `φ̄` **and at most `ψ`s whose index is `Ω`** — 2.3.2 and
2.3.3 kill `M` and `ω̄^·`, 2.3.9 kills every `Z`, and 2.3.14(iii) kills every `ψ` whose index
is not `Ω`, because `Ω = Z0` is the least regular term and 2.3.15 says so.  Only the `ψ`
clause depends on which `q` one is below, so §102 proves the induction ONCE with that clause
as a hypothesis (`towBound102`) and pays it twice:

  * at `q = 1` (`Γ₁`) the one surviving `ψ` is `Γ₀` itself — 2.3.14(ii) sends the comparison
    down to `α < 1` and §9's `below_one` finishes it;
  * at `q = 0` (`Γ₀`) NO `ψ` survives at all, since `α < 0` is false.

  §102.1  **THE CLAUSES OF 2.3, AS REWRITE RULES AT `ψ_Ω(q)`.**  `lt_M_psi102`,
          `lt_omg_psi102`, `lt_Z_psiOm102`, `lt_psi_Om102`, `lt_psiZ_psiOm102`,
          `lt_hd_of_phi_lt_psi102` (the FIRST component of 2.3.5; §65 already had the second),
          `lt_psi_phi_eq102` / `lt_psi_phi_of_le_fst102` (2.3.4), `lt_add_psi102` and
          `lt_add_ap102` (2.3.10), and `lt_Z_Om102` / `lt_Om_Z102` (`Ω` is the least `Z`).
          All at the default fuel; the only new fact about `starF` is `starF f 0 = 0`.

  §102.2  **THE TOWER, THE HEIGHT, AND THE INDUCTION.**  `vTow102 c` is `c`, `φ̄(c,0)`,
          `φ̄(φ̄(c,0),0)`, …; `htG102` reads the overtaking index off the term's own syntax
          (`⊕` takes its head, `φ̄` takes `max(htG a + 1, htG b)`, a `ψ` takes 1).
          `towBound102` : `s ∈ 𝔗(M)`, `s < ψ_Ω(q)` and `htG102 s ≤ m` give
          `s < vTow102 c m`.

  §102.3  **`Γ₁`.**  `rawT_eq102` (§94.6's raw tower is `vTow102 Γ₀` shifted by one),
          `hpsi_Gam1_102`, and `cofGam1_102` — **which does not need `Γ₀ ≤ s`**, so it is
          strictly stronger than the clause §98 asked for.  `CofGam1_102 : CofGam1_98`.

  §102.4  **`Γ₀`, FOR FREE.**  `cofGam0_102` : every term of 𝔗(M) below `Γ₀` is at or below
          a rung of `gTow102 = 1, ε₀, φ̄(ε₀,0), …`.  And `iterGamma_gTow102` proves that
          tower IS `TM/FS.lean`'s `iterGamma 1` — i.e. **this repository's own fundamental
          sequence of `Γ₀`**, `fsN Γ₀ ·` (also kernel-checked at 8 rungs).  So it is the
          cofinality clause of the `Γ₀` row, not merely an auxiliary of §102.3.

  §102.5  **WHAT THAT BUYS.**  `denseHi_below_Gam1_102` : §98's `denseHi_below_Gam1_98` with
          its third hypothesis discharged.  Every challenger below `Γ₁` is witnessed at
          every target at or above `Γ₁`, from `PsiIdxOKStd172` and `DictLtA74` and nothing
          else — the two clauses row 326 already carries.

  §102.6  **`DictDenseHi94`, DECOMPOSED — AND THREE CLAUSES REMAIN.**  `dictDenseHi_of102`
          splits the gate into (a) target `≥ Γ₁`, challenger `< Γ₁` — now a theorem;
          (b1) target in `(ε₀, Γ₀]`; (b2) target in `(Γ₀, Γ₁)`; (c) target and challenger
          both `≥ Γ₁`.  (b1) is reduced further, to `DictOntoMid102` alone
          (`denseMid_of_onto102`: a challenger is witnessed by its own preimage, with the
          single point `s = ε₀` handled by §94.3's `bE94`), which is §97 transposed one
          level up.  (b2) is `DictDenseMid102` and (c) is `DictDenseAbove102`; all three are
          HYPOTHESES and are marked as such.  `certIn_t326_102` is row 326 through them.

  §102.7  **TWO REFUTATIONS, AND THEY BREAK DIFFERENT CONJUNCTS.**  `cofGam1_needs_inT102`:
          delete the formation condition and `ψ_Ω(0 ⊕ M)` is a counterexample — above `Γ₀`,
          below `Γ₁`, and above EVERY rung of the raw tower.  It fails 2.1(iii) at
          `isAP 0 = false`, exactly like §9's `φ̄(0 ⊕ M)0` and §97's `junk97`.
          `cofGam0_needs_inT102`: at `Γ₀` that shape no longer works and the counterexample
          is `ψ_1(0)`, which breaks **2.1(vi), `κ ∈ R`** instead.  Worth recording because
          the tower that climbs the FIRST argument is coarser than §9's ω-tower: `φ̄(0 ⊕ M)0`
          is below `ε₀`, hence below `gTow102 1`, so §9's own junk cannot break it
          (`#guard`ed both ways).

WHAT IS **NOT** CLAIMED.  `DictDenseHi94` is NOT proved, `DictDense85` is NOT proved and
`CofDenseS1` is NOT closed.  Row 326 still waits on `PsiIdxOKStd172`, `HiMono89` and — on
the density side — the three clauses of §102.6 in place of `DictDenseHi94`.  §102 does not
shorten the list of clauses row 326 carries; what it changes is INSIDE the density gate.
`PsiIdxOKStd172` and `DictLtA74` are used, not proved.

**Where §102 stopped, precisely.**  Case (a) is closed.  Of the rest, (c) is untouched here
exactly as in §98.  For (b) the measurement (§102.9) says the segment splits at `Γ₀` and
the two halves are NOT alike, so they are two problems and not one:

  * Below `Γ₀` every one of 129 terms of `(ε₀, Γ₀)` has a preimage under `dictInv`, and
    every one of those preimages is a LEGAL witness (level ≤ 1, standard, head `D 0`).  So
    there the witness is the challenger's own preimage and what is missing is a PROOF —
    `DictOntoMid102`, which is §97 (`dict` onto below `ε₀`) one level up.  **§102.4's tower
    is inside that image too**, with legal witnesses at all 6 rungs measured, so §102.4 and
    `DictOntoMid102` are the two halves of a density theorem at the target `Γ₀`.
  * Above `Γ₀` it is a different story.  Of 94 terms of `[Γ₀, Γ₁)` only 56 have any preimage
    and only 35 a legal one, and §94.6's raw tower has none at any rung.  There the witness
    must be BUILT, which is what §98's `bStep98` does — but §98's step lands at
    `φ̄(dict x, Γ₀ ⊕ 1)`, a whole Veblen step above its input, so that family cannot be dense
    inside a segment.  **(b2) needs a finer step operator than §98's, and this file does not
    have one.**

So the answer to "does the same climb cover the targets in `(ε₀, Γ₁)`" is NO, and the two
halves need different things: below `Γ₀` the analogue of §97 one level down from `Γ₁`, above
`Γ₀` a new construction.

WHAT THE MEASUREMENT SAYS (§102.8 gives the construction).  One population, 102 terms, built
so that BOTH hypotheses stay visible and NEITHER is filtered — §97's model, and the failure
mode §93 fell into (a bridge that held 292/292 where its own hypothesis failed).  Nineteen
of the 102 are below `Γ₁` and are NOT terms of 𝔗(M); they are in on purpose.

  * **The claim is exact at both levels.**  `inT s` and `s < Γ₁` give `s ≤ rawT94 (htG102 s)`
    with 0 misses; `inT s` and `s < Γ₀` give `s ≤ gTow102 (htG102 s)` with 0 misses.
  * **The formation condition is load-bearing and its failure is visible.**  Drop `inT` and
    5 terms miss at `Γ₁` and 5 at `Γ₀` — and they are not the same 5: the first five are
    `ψ_Ω(0 ⊕ M)` and four shapes built on it, the second five `ψ_1(0)` and its four.
  * **But the hypothesis is not a restatement of the conclusion.**  The other 14 of the 19
    ill-formed terms below `Γ₁` ARE still dominated by the tower.
  * **The height is doing work.**  24 terms sit at `gTow102 (htG102 s)` and NOT at the rung
    below it; the heights realised run 0 … 5.  Control: replace `htG102` by the constant 0
    and the `Γ₀` claim breaks.
  * **The towers behave.**  Eight rungs of each: all in 𝔗(M), strictly increasing, all below
    their limit.
  * **The named witnesses are in the population**, and two further `#guard`s say which
    conjunct each one breaks — `isAP 0 = false` for one, `isR 1 = false` for the other. -/


/-! ### §102.1 `ψ_Ω(q)` の下にいる形 — 2.3 の節をそのまま読む -/

section
open TM TM.Term
open Evidence.WF

/-- `Γ₁ = ψ_Ω(1)`。§94 の `Gam1_94 = dict bGam85` は文字どおりこれである。 -/
theorem Gam1_eq102 : Gam1_94 = psi (Z zero) TM.Term.one := rfl

/-- `Γ₀ = ψ_Ω(0)`。 -/
theorem G094_eq102 : G094 = psi (Z zero) zero := rfl

theorem starF_zero102 : ∀ f : Nat, starF f zero = zero
  | 0 => rfl
  | _ + 1 => rfl

theorem lt_right_zero102 (t : Term) : lt t zero = false := ltF_right_zero _ t

/-- 2.3.2 — `M` は `ψ` の下にいない。 -/
theorem lt_M_psi102 (k a : Term) : lt M (psi k a) = false := by
  rw [lt_eq_ltF_succ]; exact ltF_succ_M_psi _ k a

/-- 2.3.2/2.3.3 — `ω̄^·` は `ψ` の下にいない。 -/
theorem lt_omg_psi102 (x k a : Term) : lt (omg x) (psi k a) = false := by
  rw [lt_eq_ltF_succ]; exact ltF_succ_omg_psi _ x k a

/-- 2.3.15 — `Ω = Z0` は `Z` の最小元。 -/
theorem lt_Z_Om102 : ∀ e : Term, lt (Z e) (Z zero) = false := by
  intro e
  by_cases h : e = zero
  · subst h; exact lt_irrefl _
  · rw [lt_eq_ltF_succ, ltF_succ_Z_Z _ (by intro hc; injection hc with h1; exact h h1),
      ltF_right_zero, if_neg (by intro hc; exact Bool.noConfusion hc), starF_zero102,
      ltF_right_zero]
    rfl

theorem lt_Om_Z102 {e : Term} (h : e ≠ zero) : lt (Z zero) (Z e) = true := by
  rw [lt_eq_ltF_succ,
    ltF_succ_Z_Z _ (by intro hc; injection hc with h1; exact h h1.symm),
    if_pos (ltF_left_zero (by omega) h), starF_zero102]
  exact ltF_left_zero (by omega) (by intro hc; exact Term.noConfusion hc)

/-- 2.3.9 — `Z e` は `ψ_Ω(q)` の下にいない。`e` が何であれ、`q` が何であれ。 -/
theorem lt_Z_psiOm102 (e q : Term) : lt (Z e) (psi (Z zero) q) = false := by
  have hq := deg_pos q
  rw [lt_eq_ltF_succ, ltF_succ_Z_psi]
  by_cases h : e = zero
  · subst h; rw [if_pos (by rw [show ((Z zero : Term) == Z zero) = true from rfl]; rfl)]
  · rw [if_pos ?_]
    rw [show ltF (2 * ((Z e).deg + (psi (Z zero) q).deg) + 7) (Z zero) (Z e)
          = lt (Z zero) (Z e) from
        (lt_eq_ltF (Z zero) (Z e) _ (by
          show (1 + (zero : Term).deg) + (1 + e.deg)
            ≤ 2 * ((1 + e.deg) + (1 + (Z zero).deg + q.deg)) + 7
          simp only [TM.Term.deg]; omega)).symm, lt_Om_Z102 h, Bool.or_true]

/-- 2.3.6 — 添字が `Ω` でない `ψ` は `Ω` の下にいない。 -/
theorem lt_psi_Om102 {e a : Term} (h : e ≠ zero) : lt (psi (Z e) a) (Z zero) = false := by
  rw [lt_eq_ltF_succ, ltF_succ_psi_Z,
    show ltF (2 * ((psi (Z e) a).deg + (Z zero).deg) + 7) (Z e) (Z zero) = lt (Z e) (Z zero) from
      (lt_eq_ltF (Z e) (Z zero) _ (by
        show (1 + e.deg) + (1 + (zero : Term).deg)
          ≤ 2 * ((1 + (1 + e.deg) + a.deg) + (1 + (zero : Term).deg)) + 7
        simp only [TM.Term.deg]; omega)).symm, lt_Z_Om102 e,
    if_neg (by
      rw [show ((Z e : Term) == Z zero) = false from by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro hc; injection hc with h1; exact h h1]
      intro hc; exact Bool.noConfusion hc),
    starF_zero102, ltF_right_zero]
  rfl

/-- 2.3.14(iii) — 添字が `Ω` でない `ψ` は `ψ_Ω(q)` の下にいない。 -/
theorem lt_psiZ_psiOm102 {e a : Term} (h : e ≠ zero) (q : Term) :
    lt (psi (Z e) a) (psi (Z zero) q) = false := by
  have hq := deg_pos q
  have hne : psi (Z e) a ≠ psi (Z zero) q := by
    intro hc; injection hc with h1 _; injection h1 with h2; exact h h2
  rw [lt_eq_ltF_succ, ltF_succ_psi_psi _ hne,
    if_neg (by intro hc; injection hc with h1; exact h h1),
    show ltF (2 * ((psi (Z e) a).deg + (psi (Z zero) q).deg) + 7) (Z e) (Z zero)
        = lt (Z e) (Z zero) from
      (lt_eq_ltF (Z e) (Z zero) _ (by
        show (1 + e.deg) + (1 + (zero : Term).deg)
          ≤ 2 * ((1 + (1 + e.deg) + a.deg) + (1 + (1 + (zero : Term).deg) + q.deg)) + 7
        simp only [TM.Term.deg]; omega)).symm, lt_Z_Om102 e,
    if_neg (by intro hc; exact Bool.noConfusion hc),
    show ltF (2 * ((psi (Z e) a).deg + (psi (Z zero) q).deg) + 7)
          (psi (Z e) a) (Z zero) = lt (psi (Z e) a) (Z zero) from
      (lt_eq_ltF (psi (Z e) a) (Z zero) _ (by
        show (1 + (1 + e.deg) + a.deg) + (1 + (zero : Term).deg)
          ≤ 2 * ((1 + (1 + e.deg) + a.deg) + (1 + (1 + (zero : Term).deg) + q.deg)) + 7
        simp only [TM.Term.deg]; omega)).symm]
  exact lt_psi_Om102 h

/-- 2.3.5 の第 1 成分。§65 の `lt_arg_of_phi_lt_psi` が第 2 成分である。 -/
theorem lt_hd_of_phi_lt_psi102 {a b k c : Term} (h : lt (phi a b) (psi k c) = true) :
    lt a (psi k c) = true := by
  rw [lt_eq_ltF_succ, ltF_succ_phi_psi,
    show ltF (2 * ((phi a b).deg + (psi k c).deg) + 7) a (psi k c) = lt a (psi k c) from
      (lt_eq_ltF a (psi k c) _ (by
        show a.deg + (1 + k.deg + c.deg)
          ≤ 2 * ((1 + a.deg + b.deg) + (1 + k.deg + c.deg)) + 7
        omega)).symm] at h
  exact ((Bool.and_eq_true _ _).mp h).1

/-- 2.3.4 を `lt` の高さで — `ψ` と `φ̄` の比較はそのまま 4 つの選言。 -/
theorem lt_psi_phi_eq102 (k a c d : Term) :
    lt (psi k a) (phi c d)
      = ((psi k a == c) || (psi k a == d) || lt (psi k a) c || lt (psi k a) d) := by
  rw [lt_eq_ltF_succ, ltF_succ_psi_phi,
    show ltF (2 * ((psi k a).deg + (phi c d).deg) + 7) (psi k a) c = lt (psi k a) c from
      (lt_eq_ltF (psi k a) c _ (by
        show (1 + k.deg + a.deg) + c.deg
          ≤ 2 * ((1 + k.deg + a.deg) + (1 + c.deg + d.deg)) + 7
        omega)).symm,
    show ltF (2 * ((psi k a).deg + (phi c d).deg) + 7) (psi k a) d = lt (psi k a) d from
      (lt_eq_ltF (psi k a) d _ (by
        show (1 + k.deg + a.deg) + d.deg
          ≤ 2 * ((1 + k.deg + a.deg) + (1 + c.deg + d.deg)) + 7
        omega)).symm]

/-- 2.3.4 の第 1 成分。 -/
theorem lt_psi_phi_of_le_fst102 {k a c d : Term} (h : le (psi k a) c = true) :
    lt (psi k a) (phi c d) = true := by
  rw [lt_psi_phi_eq102]
  rcases (Bool.or_eq_true _ _).mp h with he | hl
  · rw [he, Bool.true_or, Bool.true_or, Bool.true_or]
  · rw [hl, Bool.or_true, Bool.true_or]

/-- 2.3.10 を `ψ` の的で。 -/
theorem lt_add_psi102 (a b k c : Term) : lt (add a b) (psi k c) = lt a (psi k c) := by
  have hb := deg_pos b
  show ltF (fuelOf (add a b) (psi k c)) (add a b) (psi k c) = _
  rw [show fuelOf (add a b) (psi k c)
        = (2 * ((add a b).deg + (psi k c).deg) + 7) + 1 from by
      show 2 * ((add a b).deg + (psi k c).deg) + 8 = _; omega,
    show ltF ((2 * ((add a b).deg + (psi k c).deg) + 7) + 1) (add a b) (psi k c)
        = ltF (2 * ((add a b).deg + (psi k c).deg) + 7) a (psi k c) from rfl]
  exact (lt_eq_ltF a (psi k c) _
    (by show a.deg + (psi k c).deg ≤ 2 * ((1 + a.deg + b.deg) + (psi k c).deg) + 7;
        omega)).symm

theorem ltF_succ_add_ap102 (f : Nat) (a b : Term) : ∀ {t : Term}, isAP t = true →
    ltF (f + 1) (add a b) t = ltF f a t
  | zero, h => Bool.noConfusion h
  | add _ _, h => Bool.noConfusion h
  | M, _ => rfl
  | omg _, _ => rfl
  | phi _ _, _ => rfl
  | psi _ _, _ => rfl
  | Z _, _ => rfl

/-- 2.3.10 を任意の加法主要項の的で。 -/
theorem lt_add_ap102 (a b : Term) {t : Term} (ht : isAP t = true) :
    lt (add a b) t = lt a t := by
  have hb := deg_pos b
  show ltF (fuelOf (add a b) t) (add a b) t = _
  rw [show fuelOf (add a b) t = (2 * ((add a b).deg + t.deg) + 7) + 1 from by
      show 2 * ((add a b).deg + t.deg) + 8 = _; omega,
    ltF_succ_add_ap102 _ a b ht]
  exact (lt_eq_ltF a t _
    (by show a.deg + t.deg ≤ 2 * ((1 + a.deg + b.deg) + t.deg) + 7; omega)).symm

theorem inT_psi102 {k a : Term} (h : inT (psi k a) = true) :
    k.isR = true ∧ inT k = true ∧ inT a = true := by
  simp only [inT, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2⟩

end

/-! ### §102.2 第 1 引数を登る塔と、項から読む高さ -/

section
open TM TM.Term
open Evidence.WF

/-- **第 1 引数を登る `φ̄` の塔** — 種 `c` から。
    `vTow102 c 0 = c`, `vTow102 c (n+1) = φ̄(vTow102 c n, 0)`。 -/
def vTow102 (c : Term) : Nat → Term
  | 0 => c
  | n + 1 => phi (vTow102 c n) zero

/-- **項の構文から読む塔の高さ。**  §9 の `ht` の第 1 引数版:
    `⊕` は頭だけ、`φ̄` は第 1 引数で一段上がる。`ψ` は 1 (塔の種の分)。 -/
def htG102 : Term → Nat
  | zero => 0
  | M => 0
  | add a _ => htG102 a
  | omg _ => 0
  | phi a b => max (htG102 a + 1) (htG102 b)
  | psi _ _ => 1
  | Z _ => 0

theorem isAP_vTow102 {c : Term} (hc : isAP c = true) : ∀ m, isAP (vTow102 c m) = true
  | 0 => hc
  | _ + 1 => rfl

theorem vTow_ne_zero102 {c : Term} (hc : isAP c = true) : ∀ m, vTow102 c m ≠ zero
  | 0 => by
      intro h
      have hz : c = zero := h
      rw [hz] at hc
      exact Bool.noConfusion hc
  | _ + 1 => by intro h; exact Term.noConfusion h

/-- **§102 の中核。**  `ψ_Ω(q)` より下の 𝔗(M) の項はどれも、第 1 引数を登る塔の
    `htG102` 段目で押さえられる。`ψ` の節だけが実例ごとに違うので、そこは仮説にしてある
    (`Γ₁` では `Γ₀` そのもの、`Γ₀` では空)。証明は 1 本の構造帰納で、
    移行律も比較可能性も `Frag` も使わない — §9 とまったく同じ理由による。 -/
theorem towBound102 {c q : Term} (hc : isAP c = true)
    (hpsi : ∀ (k a : Term), inT (psi k a) = true →
      lt (psi k a) (psi (Z zero) q) = true → ∀ m, 1 ≤ m →
      lt (psi k a) (vTow102 c m) = true) :
    ∀ (s : Term), inT s = true → lt s (psi (Z zero) q) = true →
    ∀ m, htG102 s ≤ m → lt s (vTow102 c m) = true := by
  intro s
  induction s with
  | zero => intro _ _ m _; exact lt_zero_ne76 (vTow_ne_zero102 hc m)
  | M => intro _ h _ _; rw [lt_M_psi102] at h; exact Bool.noConfusion h
  | omg x _ => intro _ h _ _; rw [lt_omg_psi102] at h; exact Bool.noConfusion h
  | Z e _ => intro _ h _ _; rw [lt_Z_psiOm102] at h; exact Bool.noConfusion h
  | add a b iha _ =>
      intro hin h m hm
      obtain ⟨_, hina, _⟩ := inT_add hin
      rw [lt_add_psi102] at h
      rw [lt_add_ap102 a b (isAP_vTow102 hc m)]
      exact iha hina h m hm
  | phi u d ihu ihd =>
      intro hin h m hm
      obtain ⟨hinu, hind⟩ := inT_phi hin
      have hu1 : lt u (psi (Z zero) q) = true := lt_hd_of_phi_lt_psi102 h
      have hd1 : lt d (psi (Z zero) q) = true := lt_arg_of_phi_lt_psi h
      have hm2 : max (htG102 u + 1) (htG102 d) ≤ m := hm
      cases m with
      | zero => omega
      | succ m' =>
          have hcc : lt u (vTow102 c m') = true := ihu hinu hu1 m' (by omega)
          have hne : u ≠ vTow102 c m' := by
            intro hh; rw [hh, lt_irrefl] at hcc; exact Bool.noConfusion hcc
          rw [show vTow102 c (m' + 1) = phi (vTow102 c m') zero from rfl,
            lt_phi_phi (by intro hh; injection hh with h1 _; exact hne h1),
            if_neg hne, if_pos hcc]
          exact ihd hind hd1 (m' + 1) (by omega)
  | psi k a _ _ =>
      intro hin h m hm
      exact hpsi k a hin h m hm

end

/-! ### §102.3 実例 1 — `Γ₁`、そして §98 が名指しした条項 -/

section
open TM TM.Term
open Evidence.WF

theorem le_G0_vTow102 : ∀ m, le G094 (vTow102 G094 m) = true
  | 0 => le_self G094
  | m + 1 => le_of_lt (lt_psi_phi_of_le_fst102 (le_G0_vTow102 m))

/-- §94.6 の生の塔は、種を `Γ₀` にした一般の塔の 1 段ずらしである。 -/
theorem rawT_eq102 : ∀ n, rawT94 n = vTow102 G094 (n + 1)
  | 0 => rfl
  | n + 1 => by
      show phi (rawT94 n) zero = phi (vTow102 G094 (n + 1)) zero
      rw [rawT_eq102 n]

/-- `Γ₁` の下に生き残る `ψ` は `Γ₀` ただ 1 つ。`κ ∈ R` と `α ∈ 𝔗(M)` の両方を使う。 -/
theorem hpsi_Gam1_102 : ∀ (k a : Term), inT (psi k a) = true →
    lt (psi k a) (psi (Z zero) TM.Term.one) = true → ∀ m, 1 ≤ m →
    lt (psi k a) (vTow102 G094 m) = true := by
  intro k a hin h m hm
  obtain ⟨hisR, _, hina⟩ := inT_psi102 hin
  cases k with
  | zero => exact Bool.noConfusion hisR
  | M => exact Bool.noConfusion hisR
  | add _ _ => exact Bool.noConfusion hisR
  | omg _ => exact Bool.noConfusion hisR
  | phi _ _ => exact Bool.noConfusion hisR
  | psi _ _ => exact Bool.noConfusion hisR
  | Z e =>
      by_cases he : e = zero
      · subst he
        rw [lt_psi_same] at h
        have haz : a = zero := below_one a hina (fuelOf a TM.Term.one) h
        subst haz
        cases m with
        | zero => omega
        | succ m' =>
            rw [show vTow102 G094 (m' + 1) = phi (vTow102 G094 m') zero from rfl]
            exact lt_psi_phi_of_le_fst102 (le_G0_vTow102 m')
      · rw [lt_psiZ_psiOm102 he] at h; exact Bool.noConfusion h

/-- **§102 の主定理 (1) — 𝔗(M) 側の `Γ₁` の共終性。**
    `Γ₁` より下の 𝔗(M) の項はどれも §94.6 の生の塔のどれかの段以下にいる。
    §9 の `cof_eps0` の `Γ₁` 版で、`Γ₀ ≤ s` は要らない。 -/
theorem cofGam1_102 (s : Term) (hs : inT s = true) (h : lt s Gam1_94 = true) :
    ∃ n, le s (rawT94 n) = true := by
  refine ⟨htG102 s, ?_⟩
  rw [rawT_eq102 (htG102 s)]
  exact le_of_lt (towBound102 (show isAP G094 = true from rfl) hpsi_Gam1_102 s hs
    (by rw [← Gam1_eq102]; exact h) (htG102 s + 1) (by omega))

/-- **§98 が名指しした条項は定理である。** -/
theorem CofGam1_102 : CofGam1_98 := fun s hs hlt _ => cofGam1_102 s hs hlt

end

/-! ### §102.4 実例 2 — `Γ₀`、そしてそれは repo 自身の基本列である -/

section
open TM TM.Term
open Evidence.WF

/-- **`Γ₀` の塔** — `1, ε₀, φ̄(ε₀,0), …`。 -/
def gTow102 : Nat → Term := vTow102 TM.Term.one

/-- `Γ₀` の下には `ψ` が 1 つも生き残らない。効いているのは `κ ∈ R` である。 -/
theorem hpsi_Gam0_102 : ∀ (k a : Term), inT (psi k a) = true →
    lt (psi k a) (psi (Z zero) zero) = true → ∀ m, 1 ≤ m →
    lt (psi k a) (vTow102 TM.Term.one m) = true := by
  intro k a hin h m _
  obtain ⟨hisR, _, _⟩ := inT_psi102 hin
  cases k with
  | zero => exact Bool.noConfusion hisR
  | M => exact Bool.noConfusion hisR
  | add _ _ => exact Bool.noConfusion hisR
  | omg _ => exact Bool.noConfusion hisR
  | phi _ _ => exact Bool.noConfusion hisR
  | psi _ _ => exact Bool.noConfusion hisR
  | Z e =>
      by_cases he : e = zero
      · subst he; rw [lt_psi_same, lt_right_zero102] at h; exact Bool.noConfusion h
      · rw [lt_psiZ_psiOm102 he] at h; exact Bool.noConfusion h

/-- **§102 の主定理 (2) — 𝔗(M) 側の `Γ₀` の共終性。** -/
theorem cofGam0_102 (s : Term) (hs : inT s = true) (h : lt s G094 = true) :
    ∃ n, le s (gTow102 n) = true :=
  ⟨htG102 s, le_of_lt (towBound102 (show isAP TM.Term.one = true from rfl) hpsi_Gam0_102 s hs
    (show lt s (psi (Z zero) zero) = true from h) (htG102 s) (Nat.le_refl _))⟩

/-- `φ̄(φ̄uv, 0)` のところで `phiNF` は飛ばさない — 第 2 引数が `0` で、第 1 引数が `SC` でない。 -/
theorem phiNF_phi_zero102 (u v : Term) : phiNF (phi u v) zero = phi (phi u v) zero := rfl

theorem vTow_one_phi102 : ∀ n, ∃ u v, vTow102 TM.Term.one n = phi u v
  | 0 => ⟨zero, zero, rfl⟩
  | n + 1 => ⟨vTow102 TM.Term.one n, zero, rfl⟩

/-- **`Γ₀` の塔は `TM/FS.lean` の `iterGamma` そのもの。** -/
theorem iterGamma_gTow102 : ∀ n, iterGamma TM.Term.one n = gTow102 n
  | 0 => rfl
  | n + 1 => by
      obtain ⟨u, v, huv⟩ := vTow_one_phi102 n
      show phiNF (iterGamma TM.Term.one n) zero = phi (vTow102 TM.Term.one n) zero
      rw [show iterGamma TM.Term.one n = vTow102 TM.Term.one n from iterGamma_gTow102 n,
        huv, phiNF_phi_zero102]

/-! `Γ₀` の塔は repo の基本列 `fsN Γ₀ ·` と項ごとに一致する (核で確認)。 -/
#guard (List.range 8).all fun n => gTow102 n == fsN G094 n

end

/-! ### §102.5 条項が買うもの -/

section
open Trans.Recal
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

/-- **`Γ₁` より下の挑戦者・`Γ₁` 以上の目標のところは、もう仮説なしで閉じる。**
    §98 の `denseHi_below_Gam1_98` から `CofGam1_98` が落ちた形。
    残るのは 326 行目がすでに抱えている 2 つだけである。 -/
theorem denseHi_below_Gam1_102 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    {v : Term} (hiv : inT v = true) (hv : le Gam1_94 v = true)
    {s : Term} (hs : inT s = true) (hlt : lt s Gam1_94 = true) :
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
      le s (dict b) = true ∧ lt (dict b) v = true :=
  denseHi_below_Gam1_98 Hp H2 CofGam1_102 hiv hv hs hlt

end

/-! ### §102.6 `DictDenseHi94` の分解 — 残っているのはあと三本 -/

section
open Trans.Recal
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

/-- **(b1)** 目標が `(ε₀, Γ₀]` にあるところ — `dict` が `(ε₀, Γ₀)` に全射であること。
    **証明しない。**  §97 (`dict` は `ε₀` より下で全射) をちょうど一段上げたものである。 -/
def DictOntoMid102 : Prop := ∀ s : Term, inT s = true → lt E081 s = true → lt s G094 = true →
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧ dict b = s

/-- **(b2)** 目標が `(Γ₀, Γ₁)` にあるところ。**証明しない。**  ここは全射ではない
    (§102.9 の測定) ので、形は「全射」ではなく「稠密」でなければならない。 -/
def DictDenseMid102 : Prop := ∀ v : Term, inT v = true → lt G094 v = true →
    lt v Gam1_94 = true → ∀ s : Term, inT s = true → lt s v = true →
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
      le s (dict b) = true ∧ lt (dict b) v = true

/-- **(c)** 目標も挑戦者も `Γ₁` 以上のところ。**証明しない。**  §98 も触れていない。 -/
def DictDenseAbove102 : Prop := ∀ v : Term, inT v = true → le Gam1_94 v = true →
    ∀ s : Term, inT s = true → le Gam1_94 s = true → lt s v = true →
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
      le s (dict b) = true ∧ lt (dict b) v = true

theorem inT_G094_102 : inT G094 = true := by decide

theorem inT_Gam1_102 (Hp : PsiIdxOKStd172) : inT Gam1_94 = true :=
  (inT_dict_of_std172 Hp bGam85 (rfl : btLe72 1 bGam85 = true)
    (rfl : BT.isStd bGam85 = true)).1

/-- **`(ε₀, Γ₀]` の目標は (b1) ひとつで片づく。**  挑戦者は自分の逆像が証人になる
    (§97 の低い側と同じ理屈)、ただ 1 点 `s = ε₀` だけ §94.3 の `bE94` を使う。 -/
theorem denseMid_of_onto102 (H : DictOntoMid102) {v : Term} (hiv : inT v = true)
    (hvG : le v G094 = true) (hvE : lt E081 v = true)
    {s : Term} (hs : inT s = true) (hlt : lt s v = true) :
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
      le s (dict b) = true ∧ lt (dict b) v = true := by
  have hsG : lt s G094 = true :=
    lt_of_lt_of_le3 (inT_le_fragR _ hs) (inT_le_fragR _ hiv) (inT_le_fragR _ inT_G094_102)
      hlt hvG
  rcases lt_trichotomy_inT hs inT_E81 with h | h | h
  · exact ⟨bE94, rfl, rfl, hd0_bE94, by rw [dict_bE94]; exact le_of_lt94 h.1,
      by rw [dict_bE94]; exact hvE⟩
  · exact ⟨bE94, rfl, rfl, hd0_bE94, by rw [dict_bE94, h.2.1]; exact le_self E081,
      by rw [dict_bE94]; exact hvE⟩
  · obtain ⟨b, hb, hsb, hdb, hval⟩ := H s hs h.2.2 hsG
    exact ⟨b, hb, hsb, hdb, by rw [hval]; exact le_self s, by rw [hval]; exact hlt⟩

/-- **§102.6 の主定理。**  `DictDenseHi94` は (a) + (b1) + (b2) + (c) で、
    (a) — 目標が `Γ₁` 以上・挑戦者が `Γ₁` より下 — は §102.5 で定理になった。
    残るのは (b1)(b2)(c) の三本である。 -/
theorem dictDenseHi_of102 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (H1 : DictOntoMid102) (H3 : DictDenseMid102) (H4 : DictDenseAbove102) :
    DictDenseHi94 := by
  intro t ht _ hvE s hs _ hlt
  have hiv : inT (vOf t) = true := inT_vOf94 Hp t ht
  have hiG1 : inT Gam1_94 = true := inT_Gam1_102 Hp
  rcases lt_trichotomy_inT hiv hiG1 with hv | hv | hv
  · rcases lt_trichotomy_inT hiv inT_G094_102 with hg | hg | hg
    · exact denseMid_of_onto102 H1 hiv (le_of_lt94 hg.1) hvE hs hlt
    · exact denseMid_of_onto102 H1 hiv (by rw [hg.2.1]; exact le_self G094) hvE hs hlt
    · exact H3 (vOf t) hiv hg.2.2 hv.1 s hs hlt
  · rcases lt_trichotomy_inT hs hiG1 with hsg | hsg | hsg
    · exact denseHi_below_Gam1_102 Hp H2 hiv (by rw [hv.2.1]; exact le_self Gam1_94) hs hsg.1
    · exact H4 (vOf t) hiv (by rw [hv.2.1]; exact le_self Gam1_94) s hs
        (by rw [hsg.2.1]; exact le_self Gam1_94) hlt
    · exact H4 (vOf t) hiv (by rw [hv.2.1]; exact le_self Gam1_94) s hs
        (le_of_lt94 hsg.2.2) hlt
  · rcases lt_trichotomy_inT hs hiG1 with hsg | hsg | hsg
    · exact denseHi_below_Gam1_102 Hp H2 hiv (le_of_lt94 hv.2.2) hs hsg.1
    · exact H4 (vOf t) hiv (le_of_lt94 hv.2.2) s hs (by rw [hsg.2.1]; exact le_self Gam1_94) hlt
    · exact H4 (vOf t) hiv (le_of_lt94 hv.2.2) s hs (le_of_lt94 hsg.2.2) hlt

/-- 326 行目の証明書 — 密度の側で待つのは §102.6 の三本だけ。 -/
theorem certIn_t326_102 (Hp : PsiIdxOKStd172) (H : HiMono89)
    (H1 : DictOntoMid102) (H3 : DictDenseMid102) (H4 : DictDenseAbove102)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_99 Hp H (dictDenseHi_of102 Hp (dictLtA74_99 Hp H) H1 H3 H4) hacc

end

/-! ### §102.7 二つの反証 — `inT` は飾りではなく、落ちる条は場所ごとに違う -/

section
open TM TM.Term
open Evidence.WF

/-- **`Γ₁` 側の junk** — `ψ_Ω(0 ⊕ M)`。2.1(iii) の `isAP 0 = false` で落ちる。 -/
def junk1_102 : Term := psi (Z zero) (add zero M)

/-- **`Γ₀` 側の junk** — `ψ_1(0)`。2.1(vi) の `κ ∈ R` で落ちる。 -/
def junk0_102 : Term := psi TM.Term.one zero

#guard inT junk1_102 == false
#guard inT (add zero M) == false
#guard inT junk0_102 == false
#guard Term.isR TM.Term.one == false

theorem lt_junk1_Gam102 : lt junk1_102 Gam1_94 = true := by decide
theorem le_G0_junk1_102 : le G094 junk1_102 = true := by decide
theorem lt_junk0_G0_102 : lt junk0_102 G094 = true := by decide

theorem lt_junk1_rawT102 : ∀ n, lt junk1_102 (rawT94 n) = false
  | 0 => by decide
  | n + 1 => by
      rw [show junk1_102 = psi (Z zero) (add zero M) from rfl,
        show rawT94 (n + 1) = phi (rawT94 n) zero from rfl, lt_psi_phi_eq102,
        show lt (psi (Z zero) (add zero M)) (rawT94 n) = false from lt_junk1_rawT102 n,
        lt_right_zero102,
        show ((psi (Z zero) (add zero M) == rawT94 n) : Bool) = false from by cases n <;> rfl,
        show ((psi (Z zero) (add zero M) == (zero : Term)) : Bool) = false from rfl]
      rfl

theorem lt_junk0_gTow102 : ∀ n, lt junk0_102 (gTow102 n) = false
  | 0 => by decide
  | n + 1 => by
      rw [show junk0_102 = psi TM.Term.one zero from rfl,
        show gTow102 (n + 1) = phi (gTow102 n) zero from rfl, lt_psi_phi_eq102,
        show lt (psi TM.Term.one zero) (gTow102 n) = false from lt_junk0_gTow102 n,
        lt_right_zero102,
        show ((psi TM.Term.one zero == gTow102 n) : Bool) = false from by cases n <;> rfl,
        show ((psi TM.Term.one zero == (zero : Term)) : Bool) = false from rfl]
      rfl

/-- **反証 1。**  `cofGam1_102` から形成条件を削ると偽になる。`ψ_Ω(0 ⊕ M)` は
    `Γ₀` 以上・`Γ₁` 未満で、生の塔のどの段より上にいる。 -/
theorem cofGam1_needs_inT102 :
    ¬ (∀ s : Term, lt s Gam1_94 = true → le G094 s = true → ∃ n, le s (rawT94 n) = true) := by
  intro hcof
  obtain ⟨n, hn⟩ := hcof junk1_102 lt_junk1_Gam102 le_G0_junk1_102
  rw [show le junk1_102 (rawT94 n) = ((junk1_102 == rawT94 n) || lt junk1_102 (rawT94 n)) from rfl,
    lt_junk1_rawT102 n,
    show ((junk1_102 == rawT94 n) : Bool) = false from by cases n <;> rfl] at hn
  exact Bool.noConfusion hn

/-- **反証 2、そして落ちる条は別のものである。**  `Γ₀` のところで形成条件を削ると
    `ψ_1(0)` が反例になる — こちらが破るのは `κ ∈ R` (2.1(vi)) であって、
    §9 の junk や `junk1_102` が破る `isAP` (2.1(iii)) ではない。 -/
theorem cofGam0_needs_inT102 :
    ¬ (∀ s : Term, lt s G094 = true → ∃ n, le s (gTow102 n) = true) := by
  intro hcof
  obtain ⟨n, hn⟩ := hcof junk0_102 lt_junk0_G0_102
  rw [show le junk0_102 (gTow102 n) = ((junk0_102 == gTow102 n) || lt junk0_102 (gTow102 n)) from rfl,
    lt_junk0_gTow102 n,
    show ((junk0_102 == gTow102 n) : Bool) = false from by cases n <;> rfl] at hn
  exact Bool.noConfusion hn

/-! **§9 の junk はここでは反例にならない。**  `φ̄(0 ⊕ M, 0)` は ε₀ より下で、
    `Γ₀` の塔の 1 段目 (= ε₀) に捕まる。第 1 引数を登る塔は ω 塔より粗い。 -/
#guard le (phi (add zero M) zero) (gTow102 1) == true
#guard le (phi (add zero M) zero) (gTow102 0) == false

end

/-! ### §102.8 測定 — 母集団の作り方と、両方の仮説が見えていること -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv)
open TM TM.Term
open Evidence.WF

/-- **種。**  ill-formed な形を意図的に入れてある — `0 ⊕ M` (2.1(iii) を破る)、
    `ψ_1(0)`・`ψ_M(0)` (2.1(vi) を破る)、`ψ_Ω(0 ⊕ M)` (引数が 2.1(iii) を破る)、
    そして `M`・`Z ·`・`ω̄^·` (どれも `Γ₁` の下にいない形)。**濾さない。** -/
private def seed102 : List Term :=
  [zero, TM.Term.one, TM.Term.omega, ofNat 2, phi TM.Term.one zero,
   phi TM.Term.one TM.Term.one, phi (ofNat 2) zero, phi TM.Term.omega zero,
   phi (phi TM.Term.one zero) zero, G094, Gam1_94,
   M, Z zero, omg (Z zero), add zero M,
   psi TM.Term.one zero, psi M zero, psi (Z zero) (add zero M)]

/-- **母集団。**  種と、種から作った 6 種類の形。 -/
def pool102 : List Term :=
  (seed102
    ++ (seed102.map fun x => phi x zero)
    ++ (seed102.map fun x => phi zero x)
    ++ (seed102.map fun x => phi (phi x zero) zero)
    ++ (seed102.map fun x => add x TM.Term.one)
    ++ (seed102.map fun x => psi (Z zero) x)
    ++ (seed102.map fun x => plus G094 x)).eraseDups

#eval pool102.length
/-! 母集団の内訳 — `inT`、`Γ₁` の下、`Γ₀` の下。 -/
#eval (pool102.countP fun s => inT s,
       pool102.countP fun s => lt s Gam1_94,
       pool102.countP fun s => inT s && lt s Gam1_94,
       pool102.countP fun s => inT s && lt s G094)

/-! **主張はぴったり。**  `inT` かつ `Γ₁` の下なら、生の塔の `htG102` 段目で押さえられる。
    外れは 0。 -/
#guard pool102.countP (fun s => inT s && lt s Gam1_94 && !(le s (rawT94 (htG102 s)))) == 0
#guard pool102.countP (fun s => inT s && lt s G094 && !(le s (gTow102 (htG102 s)))) == 0

/-! **`inT` は飾りではない。**  形成条件を落とすと、`Γ₁` の下でも `Γ₀` の下でも外れが出る。
    出る数がここに見えていることが肝心で、0 なら母集団が届いていないという意味になる。 -/
#eval (pool102.countP fun s => lt s Gam1_94 && !(le s (rawT94 (htG102 s))),
       pool102.countP fun s => lt s G094 && !(le s (gTow102 (htG102 s))))

/-! **しかし仮説は結論の言い換えではない。**  `Γ₁` の下にいる ill-formed な項の総数と、
    そのうち塔に押さえられてしまうものの数。後者が 0 でないことが肝心である。 -/
#eval (pool102.countP fun s => !(inT s) && lt s Gam1_94,
       pool102.countP fun s => !(inT s) && lt s Gam1_94 && le s (rawT94 (htG102 s)))
#guard (pool102.countP fun s => !(inT s) && lt s Gam1_94 && le s (rawT94 (htG102 s))) > 0

/-! 実際に出てくる高さの上限 — 高さが 0/1 に潰れていないこと。 -/
#eval ((pool102.filter fun s => inT s && lt s Gam1_94).map fun s => htG102 s).foldl max 0
#guard (((pool102.filter fun s => inT s && lt s Gam1_94).map fun s => htG102 s).foldl max 0) ≥ 4
#guard pool102.countP (fun s => lt s Gam1_94 && !(le s (rawT94 (htG102 s)))) > 0
#guard pool102.countP (fun s => lt s G094 && !(le s (gTow102 (htG102 s)))) > 0

/-! **高さは仕事をしている。**  `Γ₀` の塔で、`htG102 s` 段目には入るが 1 つ下の段には
    入らない項の数。0 なら高さは飾りである。 -/
#eval pool102.countP fun s => inT s && lt s G094 && 1 ≤ htG102 s
    && le s (gTow102 (htG102 s)) && !(le s (gTow102 (htG102 s - 1)))
#guard (pool102.countP fun s => inT s && lt s G094 && 1 ≤ htG102 s
    && le s (gTow102 (htG102 s)) && !(le s (gTow102 (htG102 s - 1)))) > 0

/-! **負の対照。**  高さを定数 0 にすると `Γ₀` の側で外れが出る。 -/
#guard pool102.countP (fun s => inT s && lt s G094 && !(le s (gTow102 0))) > 0

/-! **名指しの証人。**  二つの junk は母集団に入っていて、それぞれ別の条を破る。 -/
#guard pool102.contains junk1_102
#guard pool102.contains junk0_102
#guard lt junk1_102 Gam1_94 && le G094 junk1_102 && !(inT junk1_102)
#guard (List.range 12).all fun n => le junk1_102 (rawT94 n) == false
#guard lt junk0_102 G094 && !(inT junk0_102)
#guard (List.range 12).all fun n => le junk0_102 (gTow102 n) == false

/-! 塔そのもの — 段はどれも 𝔗(M) の項で、真に上がる。 -/
#guard (List.range 8).all fun n => inT (gTow102 n) && inT (rawT94 n)
#guard (List.range 8).all fun n => lt (gTow102 n) (gTow102 (n + 1))
#guard (List.range 8).all fun n => lt (rawT94 n) (rawT94 (n + 1))
#guard (List.range 8).all fun n => lt (gTow102 n) G094 && lt (rawT94 n) Gam1_94

end

/-! ### §102.9 どこで止まったか — `(ε₀, Γ₁)` の目標 -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv)
open TM TM.Term
open Evidence.WF

private def vseed102 : List Term :=
  [zero, TM.Term.one, TM.Term.omega, phi TM.Term.one zero, phi TM.Term.one TM.Term.one,
   phi (ofNat 2) zero, phi TM.Term.omega zero, phi (phi TM.Term.one zero) zero,
   ofNat 2, ofNat 3]

private def vgrow102 (p : List Term) : List Term :=
  (p ++ (p.flatMap fun x => p.map fun y => phi x y)
     ++ (p.flatMap fun x => p.map fun y => plus x y)).eraseDups

/-- `(ε₀, Γ₀)` の中の 𝔗(M) の項。 -/
def midPool102 : List Term :=
  (vgrow102 vseed102).filter fun t => inT t && lt E081 t && lt t G094

/-- `[Γ₀, Γ₁)` の中の 𝔗(M) の項。 -/
def hiPool102 : List Term :=
  (vgrow102 (vseed102 ++ [G094, phi G094 zero, plus G094 TM.Term.one])).filter
    fun t => inT t && le G094 t && lt t Gam1_94

/-! **`(ε₀, Γ₀)` では `dict` は全射に見える** — 母集団のすべてが合法な逆像を持つ。
    だから目標が `(ε₀, Γ₀)` にあるところは「作れない」のではなく「証明がない」。
    §97 をちょうど一段上げたものが要る。 -/
#eval (midPool102.length,
       midPool102.countP fun t => match dictInv t with
         | some b => dict b == t && btLe72 1 b && BT.isStd b && hd085B b
         | none => false)
#guard midPool102.length > 100
#guard midPool102.countP (fun t => match dictInv t with
         | some b => dict b == t && btLe72 1 b && BT.isStd b && hd085B b
         | none => false) == midPool102.length

/-! **`[Γ₀, Γ₁)` では全射ではない。**  逆像がある項・合法な逆像がある項の数を並べる。
    生の塔はその極端な場合で、どの段も逆像を持たない (§94.6)。 -/
#eval (hiPool102.length,
       hiPool102.countP fun t => (dictInv t).isSome,
       hiPool102.countP fun t => match dictInv t with
         | some b => dict b == t && btLe72 1 b && BT.isStd b && hd085B b
         | none => false)
#guard hiPool102.countP (fun t => (dictInv t).isSome) < hiPool102.length
#guard (List.range 8).all fun n => (dictInv (rawT94 n)).isNone

/-! `Γ₀` の塔のほうは逆像を持ち、しかも合法である — §102.4 の塔は `dict` の像の中にいる。
    ここが `(ε₀, Γ₀)` と `[Γ₀, Γ₁)` を分ける。 -/
#guard (List.range 6).all fun n => match dictInv (gTow102 n) with
  | some b => dict b == gTow102 n && btLe72 1 b && BT.isStd b && hd085B b
  | none => false

end

/-! ## §103 THE `Γ₀` TOWER IS INSIDE `dict`'s IMAGE — AND THE FRAGMENT BELOW `Γ₀` IS `CNV`

§102 decomposed the high half of row 326's density gate into four cases, closed one of them,
and named the second `DictOntoMid102`: `dict` is onto the segment `(ε₀, Γ₀)` with legal
witnesses.  It called that case "§97 transposed one level up" and measured 129 of 129.

**§103 does not close `DictOntoMid102`.**  What it closes is the case §102 said was the
other half of the same statement — the single target `v = Γ₀` — and it does so with no new
hypothesis at all, by **building the Buchholz preimage of §102.4's tower and proving it is
one**.  Along the way it corrects the oracle §102's 129/129 was measured with.

  §103.1  **THE FRAGMENT — `inT` AND `CNV` ARE THE SAME CONDITION BELOW `Γ₀`.**  This is
          §97.3 one level up, and it is where §102.4 pays off.  `ltG0_cnv103` : every Veblen
          normal form is below `Γ₀` (2.3.5 read as an equation, `lt_phi_psi103`).
          `cnv_of_ltG0_103` : every term of 𝔗(M) below `Γ₀` is a Veblen normal form — §102.4's
          cofinality puts it under a rung of `gTow102`, every rung is `CNV` (`cnv_gTow103`),
          and §15.1's `cnv_of_lt_cnv` closes downwards.  Below `ε₀` §97 had `CN`; here the
          fragment is `CNV`, and the proof is the same two steps.

  §103.2  **`Good98` CARRIES A CONJUNCT ITS OWN `ψ₁` LEMMAS DO NOT USE.**  `Good103` is
          §98.3's package with `Γ₀ ≤ X` deleted.  Every one of `dict_D1x98` / `dict_D1D1x98`'s
          steps goes through unchanged — `plus_W_103`, `splitFin_addWX103`,
          `omegaNF_addWX103`, `collapse1_good103` — which is what lets §98's `ψ₁` machinery be
          used BELOW `Γ₀`, where §98 itself never goes.  The two `ψ₁` lemmas are re-proved
          against the weaker package as `dict_D1x103` and `dict_D1D1x103`.

  §103.3  **THE FOLD AT ONE PAIR.**  `collapse0_Q103` : for `X` in `Good103` and not strongly
          critical, `ψ₀(ω^(ω^(Ω₁ ⊕ X))) = φ̄(X, 0)`.  The base-`Ω₁` decomposition of the
          argument is the single pair `(X, 1)` (`wA`/`wC` computed, exactly as in §98.4), the
          fold takes its Veblen branch once with `base = 0` and `c ⊖ 1 = 0`, and `ω^·` does
          not skip on the way out.  Where §98.4's fold fires the strongly critical branch and
          lands ABOVE `Γ₀`, this one never does and lands strictly below it.

  §103.4  **THE TOWER'S PREIMAGE.**  `gInv103` : `ψ₀0`, `ψ₀Ω₁`, `ψ₀ψ₁ψ₁(·)`, …  and
          `dict_gInv103 : dict (gInv103 n) = gTow102 n` for EVERY `n` — §102.4's tower, which
          `iterGamma_gTow102` proves is this repository's own fundamental sequence `fsN Γ₀`,
          is inside `dict`'s image at every rung.  Legality is proved, not measured:
          `btLe1_gInv103`, `isStd_gInv103`, `hd085_gInv103`, and the `BT`-order fact the
          standardness induction needs, `btlt_mono103` and `cov103`.

  §103.5  **WHAT THAT BUYS THE GATE.**  `denseAtGam0_103` : every challenger of 𝔗(M) below
          `Γ₀` is witnessed at the target `Γ₀`, from `PsiIdxOKStd172` and nothing else.  So
          §102.6's (b1) splits again: `DictOntoMidOpen103` is (b1) with the target restricted
          to `(ε₀, Γ₀)` — **strictly weaker than `DictOntoMid102`, which implies it**
          (`open_of_ontoMid103`) — and `dictDenseHi_of103` / `certIn_t326_103` put row 326
          through it.  The endpoint `v = Γ₀` is no longer a hypothesis.

  §103.6  **LEVEL HONESTY, BOTH WAYS.**  `btLe1_gInv103` : the construction never emits an
          index above 1, so §85.6's level-two refutation stays out of reach — §97's
          `btLe0_invE97` discipline, one level up.  `btLe0_gInv103` : it leaves level 0 at
          every rung from the first on.  And it HAS to: `noLevel0_inMid103` — by §81.6's
          `lt_dict_E81`, no level-0 standard term has a value above `ε₀` at all, so **not one
          witness of this whole region is reachable by §97's construction.**  That is the
          precise sense in which the two halves are different problems.

  §103.7  **THE JUNK ANALOGUE, BUILT FOR THIS INTERVAL.**  §97's `junk97 = φ̄(0 ⊕ M, 0)` is
          below `ε₀`; §102's `junk1_102` is above `Γ₀`; §102's `junk0_102 = ψ_1(0)` is in this
          interval but was used there against a cofinality clause.  The Veblen-shaped
          analogue is `junkV103 = φ̄(1, ψ_1(0))` — it LOOKS like a term of the fragment and
          its defect is one level in, in the Veblen ARGUMENT, at 2.1(vi).  Both dominate the
          whole fragment (`le_junk0_cnv103`, `le_junkV_cnv103`, by one induction each through
          2.3.4 and 2.3.10), and since §103.1 says the fragment is exactly what lies below
          `Γ₀`, `denseAtGam0_needs_inT103` follows: **delete `inT` from §103.5 and it is
          FALSE.**  This is §97.8's `denseLo_needs_inT97` one floor up, with a different junk
          term breaking a different conjunct.

  §103.8  **THE MEASUREMENT, AND WHAT IT CORRECTS.**  §102's 129/129 for `DictOntoMid102` was
          taken with `dictInv` as the oracle.  **`dictInv` is not a complete oracle.**  On a
          population built to be adversarial where §102's was not — 359 terms of `(ε₀, Γ₀)`,
          seeded with fixed-point arguments `φ̄(a, φ̄(a₁, ·))` — `dictInv` finds a legal
          preimage for only 354.  The five it misses are all of one family, `φ̄(a, φ̄(a, ·))`
          with the SAME first argument, which `vebPairs`' peel test (`lt a a₁`, strict) does
          not reach; it returns a term with the right VALUE that is not standard.  **For
          every one of the five a legal witness exists and is built here**
          (`witMiss103`, five frozen `#guard`s).  So the five are an incompleteness of the
          inverse, NOT a gap in `dict`, and `DictOntoMid102` is not refuted — but the
          evidence for it is weaker than 129/129 made it look, and any future proof has to
          handle the family `dictInv` cannot.

WHAT IS **NOT** CLAIMED.  `DictOntoMid102` is NOT proved and NOT refuted.  `DictDenseMid102`
and `DictDenseAbove102` are untouched.  `DictDenseHi94` is NOT proved, `DictDense85` is NOT
proved, `CofDenseS1` is NOT closed.  `PsiIdxOKStd172` and `DictLtA74` are used, not proved.
`dictInv` is used only as a measurement oracle and §103.8 says exactly where it is wrong.

**Where §103 stopped, precisely.**  The tower is a chain: `gInv103 (n+1)` is built from
`gInv103 n` and its value is `φ̄(dict (gInv103 n), 0)`.  That covers the targets `Γ₀` and the
rungs, and nothing between them.  To reach an arbitrary target of `(ε₀, Γ₀)` the fold has to
be inverted with MORE than one pair, and §103.3 computes it with exactly one.  The general
case is a mutual recursion (`arg` for the base-`Ω₁` digits, `inv` for the term) whose value
half needs `wcnf ∘ xOf = id` and whose standardness half cannot use §94.5's `btlt_of_lt94` at
all — that lemma requires `Hd085` on both sides, and the arguments this construction has to
compare are `ψ₁`-headed.  §103 does not attempt it.

WHAT THE MEASUREMENT SAYS (§103.8 gives the construction).  Two populations.  §102.8's
`pool102` is reused verbatim so the fragment claim is tested where BOTH hypotheses are
visible and neither is filtered; the second is new and adversarial.

  * **The fragment claim is exact.**  On `pool102`'s 102 terms `CNV` calls 30 and
    `inT ∧ · < Γ₀` calls the SAME 30 — 0 disagreements in either direction.
  * **`inT` is load-bearing and its failure is visible.**  12 of the 102 are below `Γ₀` and
    are NOT terms of 𝔗(M), and none of the 12 is `CNV`; `junkV103` and `junk0_102` are two
    of them and each is above EVERY one of 12 rungs of the tower.
  * **But the hypothesis is not a restatement of the conclusion.**  7 of those same 12
    ill-formed terms ARE dominated by the tower — `φ̄(1, 0 ⊕ M)` is one, and it is guarded
    by name.
  * **The tower, computed.**  Eight rungs: value exactly `gTow102 n`, level ≤ 1 at all of
    them, level 0 at none of them from rung 1 on, standard and head `D 0` at all of them,
    strictly increasing, all in 𝔗(M) and all below `Γ₀`.
  * **The onto measurement, redone adversarially.**  359 terms of `(ε₀, Γ₀)`, 359 with a
    `dictInv` preimage, 354 with a LEGAL one.  The 5 misses are guarded to be exactly the
    `φ̄(a, φ̄(a, ·))` family, guarded to be misses for the reason claimed (right value, not
    standard), and each is given a hand-built legal witness (`witMiss103`), guarded to
    exhaust the miss list. -/

/-! ### §103.1 `Γ₀` の下の断片 — `inT` と `CNV` は同じ条件 -/

section
open TM TM.Term
open Evidence.WF

/-- 2.3.5 を等式で — `φ̄αβ < ψκγ` はちょうど両成分が下にいること。§102.1 の
    `lt_hd_of_phi_lt_psi102` はこの片側だけを取り出したものである。 -/
theorem lt_phi_psi103 (a b k c : Term) :
    lt (phi a b) (psi k c) = (lt a (psi k c) && lt b (psi k c)) := by
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
        omega)).symm]

/-- 2.3.9 を等式で — `φ̄αβ < Zδ` も同じ形。 -/
theorem lt_phi_Z103 (a b d : Term) :
    lt (phi a b) (Z d) = (lt a (Z d) && lt b (Z d)) := by
  rw [lt_eq_ltF_succ, ltF_succ_phi_Z,
    show ltF (2 * ((phi a b).deg + (Z d).deg) + 7) a (Z d) = lt a (Z d) from
      (lt_eq_ltF a (Z d) _ (by
        show a.deg + (1 + d.deg) ≤ 2 * ((1 + a.deg + b.deg) + (1 + d.deg)) + 7
        omega)).symm,
    show ltF (2 * ((phi a b).deg + (Z d).deg) + 7) b (Z d) = lt b (Z d) from
      (lt_eq_ltF b (Z d) _ (by
        show b.deg + (1 + d.deg) ≤ 2 * ((1 + a.deg + b.deg) + (1 + d.deg)) + 7
        omega)).symm]

/-- **Veblen 標準形はみな `Γ₀` より下。** §97 の `lt_E081_cn97` を一段上げたもの。 -/
theorem ltG0_cnv103 : ∀ (s : Term), CNV s = true → lt s G094 = true
  | zero, _ => lt_zero_ne76 (by intro h; exact Term.noConfusion h)
  | M, h => Bool.noConfusion h
  | omg _, h => Bool.noConfusion h
  | psi _ _, h => Bool.noConfusion h
  | Z _, h => Bool.noConfusion h
  | phi a b, h => by
      obtain ⟨ha, hb⟩ := cnv_phi h
      show lt (phi a b) (psi (Z zero) zero) = true
      rw [lt_phi_psi103,
        show lt a (psi (Z zero) zero) = true from ltG0_cnv103 a ha,
        show lt b (psi (Z zero) zero) = true from ltG0_cnv103 b hb]
      rfl
  | add a b, h => by
      obtain ⟨_, ha, _, _⟩ := cnv_add h
      show lt (add a b) (psi (Z zero) zero) = true
      rw [lt_add_psi102]
      exact ltG0_cnv103 a ha

/-- `Γ₀` の塔の段はみな Veblen 標準形。 -/
theorem cnv_gTow103 : ∀ n, CNV (gTow102 n) = true
  | 0 => rfl
  | n + 1 => by
      show (CNV (gTow102 n) && CNV zero) = true
      rw [cnv_gTow103 n]; rfl

/-- **`Γ₀` より下の 𝔗(M) の項はみな Veblen 標準形。** §97 の `cn_of_ltE97` の `Γ₀` 版で、
    §102.4 の共終性と §15.1 の下方閉性のふたつだけを使う。 -/
theorem cnv_of_ltG0_103 {s : Term} (hs : inT s = true) (h : lt s G094 = true) :
    CNV s = true :=
  cnv_of_lt_cnv hs (cnv_gTow103 (htG102 s))
    (towBound102 (show isAP TM.Term.one = true from rfl) hpsi_Gam0_102 s hs
      (show lt s (psi (Z zero) zero) = true from h) (htG102 s) (Nat.le_refl _))

end

/-! ### §103.2 `Good98` から `Γ₀ ≤ X` を落とす -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- §98.3 の `Good98` から最後の条 `Γ₀ ≤ X` を落としたもの。`ψ₁` の 2 本の補題は
    その条をひとつも使っていない — だから `Γ₀` の下でも通る。 -/
def Good103 (X : Term) : Prop :=
  inT X = true ∧ X.isAP = true ∧ (X == TM.Term.one) = false ∧ omegaNF X = X ∧
    lt X (reg 1) = true

theorem good103_of_good98 {X : Term} (h : Good98 X) : Good103 X :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem good_toList103 {X : Term} (h : Good103 X) : toList X = [X] := toList_isAP81 h.2.1

theorem good_ltM103 {X : Term} (h : Good103 X) : lt X M = true :=
  lt_trans_inT h.1 inT_W79 inT_M h.2.2.2.2 ltM_W98

theorem good_reg2_103 {X : Term} (h : Good103 X) : lt X (reg 2) = true :=
  lt_trans_inT h.1 inT_W79 (inT_reg 2) h.2.2.2.2 lt_W_reg2_98

theorem plus_W_103 {X : Term} (h : Good103 X) : plus (reg 1) X = add (reg 1) X := by
  show (match toList X with
        | [] => reg 1
        | b1 :: _ => ofList ((toList (reg 1)).filter (fun a => le b1 a) ++ toList X)) = _
  rw [good_toList103 h]
  show ofList ((toList (reg 1)).filter (fun a => le X a) ++ [X]) = add (reg 1) X
  rw [show toList (reg 1) = [reg 1] from rfl,
    List.filter_cons_of_pos (by rw [le_of_lt h.2.2.2.2])]
  rfl

theorem inT_addWX103 {X : Term} (h : Good103 X) : inT (add (reg 1) X) = true := by
  rw [← plus_W_103 h]; exact inT_plus inT_W79 h.1

theorem ltM_addWX103 {X : Term} (h : Good103 X) : lt (add (reg 1) X) M = true := by
  rw [show add (reg 1) X = ofList [reg 1, X] from rfl]
  refine lt_ofList_M _ ?_
  intro z hz
  rcases List.mem_cons.mp hz with h1 | h1
  · rw [h1]; exact ltM_W98
  · rw [List.mem_singleton.mp h1]; exact good_ltM103 h

theorem splitFin_addWX103 {X : Term} (h : Good103 X) :
    splitFin (add (reg 1) X) = (add (reg 1) X, 0) := by
  unfold splitFin
  rw [show toList (add (reg 1) X) = [reg 1, X] from by
        show reg 1 :: toList X = _; rw [good_toList103 h]]
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

theorem omegaNF_addWX103 {X : Term} (h : Good103 X) :
    omegaNF (add (reg 1) X) = phi zero (add (reg 1) X) := by
  rw [omegaNF_of_le_M (lt_asymm_inT (inT_addWX103 h) inT_M (ltM_addWX103 h))]
  unfold phiNF
  rw [show ((add (reg 1) X).isSC && lt zero (add (reg 1) X)) = false from by
    rw [show (add (reg 1) X).isSC = false from rfl]; rfl]
  show phiNFsucc zero (add (reg 1) X) = phi zero (add (reg 1) X)
  unfold phiNFsucc
  rw [splitFin_addWX103 h]
  show phiNFdefault zero (add (reg 1) X) = phi zero (add (reg 1) X)
  exact phiNFdefault_zero94 _

theorem collapse1_good103 {X : Term} (h : Good103 X) : collapse 1 X = P98 X := by
  rw [collapse1_eq77 X h.1 (by
      intro p hp
      rw [good_toList103 h] at hp
      rw [List.mem_singleton.mp hp]
      exact good_reg2_103 h),
    plus_W_103 h]
  exact omegaNF_addWX103 h

/-- `ψ₁` を一度 — `Γ₀` の下でも通る。 -/
theorem dict_D1x103 (Hp : PsiIdxOKStd172) {x : BT} (hb : btLe72 1 x = true)
    (hs : BT.isStd x = true) (hg : Good103 (dict x)) : dict (BT.D 1 x) = P98 (dict x) := by
  rw [dict_D1_eq77 Hp x hb hs, plus_W_103 hg]
  exact omegaNF_addWX103 hg

/-- `ψ₁` を二度。 -/
theorem dict_D1D1x103 (Hp : PsiIdxOKStd172) {x : BT} (hb : btLe72 1 x = true)
    (hs : BT.isStd x = true) (hd : Hd085 x) (hg : Good103 (dict x)) :
    dict (BT.D 1 (BT.D 1 x)) = Q98 (dict x) := by
  have hb1 := btLe_D1_98 hb
  have hs1 := isStd_D1_98 hd hs
  have hiP : inT (P98 (dict x)) = true := by
    rw [← dict_D1x103 Hp hb hs hg]
    exact (inT_dict_of_std172 Hp (BT.D 1 x) hb1 hs1).1
  have hlePW : le (reg 1) (P98 (dict x)) = true := by
    rw [← collapse1_good103 hg]
    refine le_reg1_collapse1_79 (dict x) hg.1 ?_
    intro p hp
    rw [good_toList103 hg] at hp
    rw [List.mem_singleton.mp hp]
    exact good_reg2_103 hg
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
  rw [dict_D1_eq77 Hp (BT.D 1 x) hb1 hs1, dict_D1x103 Hp hb hs hg, hplus]
  show omegaNF (phi zero (add (reg 1) (dict x))) = phi zero (phi zero (add (reg 1) (dict x)))
  rw [omegaNF_of_le_M (ltM_left_phi94 zero (add (reg 1) (dict x))),
    phiNF_zero_phi94 (show add (reg 1) (dict x) ≠ zero from by
      intro hc; exact Term.noConfusion hc)]

end

/-! ### §103.3 畳み込みを一組だけ回す -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

theorem ltW_P103 (X : Term) : lt (P98 X) (reg 1) = false := by
  show lt (phi zero (add (reg 1) X)) (Z zero) = false
  rw [lt_phi_Z103, show lt (add (reg 1) X) (Z zero) = lt (reg 1) (Z zero) from
      lt_add_ap102 _ _ (show isAP (Z zero) = true from rfl),
    show lt (reg 1) (Z zero) = false from lt_irrefl _, Bool.and_false]

theorem ltW_Q103 (X : Term) : lt (Q98 X) (reg 1) = false := by
  show lt (phi zero (P98 X)) (Z zero) = false
  rw [lt_phi_Z103, show lt (P98 X) (Z zero) = false from ltW_P103 X, Bool.and_false]

theorem le_W_false103 {X : Term} (h : Good103 X) : le (reg 1) X = false := by
  have hlt := h.2.2.2.2
  show ((reg 1 == X) || lt (reg 1) X) = false
  rw [show (reg 1 == X) = false from by
      cases hc : (reg 1 == X) with
      | false => rfl
      | true =>
          exfalso
          rw [← eq_of_beq hc, lt_irrefl] at hlt
          exact Bool.noConfusion hlt,
    lt_asymm_inT h.1 inT_W79 hlt]
  rfl

/-- `SC` でない頭なら `φ̄α0` は飛ばさない。 -/
theorem phiNF_zero_right103 {X : Term} (h : X.isSC = false) : phiNF X zero = phi X zero := by
  unfold phiNF
  rw [show ((zero : Term).isSC && lt X zero) = false from rfl]
  show phiNFsucc X zero = phi X zero
  unfold phiNFsucc
  rw [show splitFin (zero : Term) = (zero, 0) from rfl]
  show phiNFdefault X zero = phi X zero
  unfold phiNFdefault
  rw [if_neg (by rw [show ((zero : Term) == zero) = true from rfl, Bool.true_and, h]
                 exact Bool.noConfusion)]

/-- **§103.3 の主定理。**  `ψ₀(ω^(ω^(Ω₁ ⊕ X))) = φ̄(X,0)`。
    底 `Ω₁` の展開はただ一組 `(X, 1)` で、畳み込みは Veblen 枝を一度だけ通る。
    §98.4 の `dict_bStep98` が強臨界枝を一度通って `Γ₀` の上へ出るのに対し、
    こちらは強臨界枝を一度も通らないので `Γ₀` の下に留まる。 -/
theorem collapse0_Q103 {X : Term} (h : Good103 X) (hSC : X.isSC = false) :
    collapse 0 (Q98 X) = phi X zero := by
  have hap := h.2.1
  have hXnz : X ≠ zero := by intro hz; rw [hz] at hap; exact Bool.noConfusion hap
  have hltP : lt (P98 X) (reg 1) = false := ltW_P103 X
  have hltQ : lt (Q98 X) (reg 1) = false := ltW_Q103 X
  have hwA : wA (reg 1) (Q98 X) = X := by
    show ofList (((toList (logOm (Q98 X))).filter (fun q => !lt q (reg 1))).map
      (divAP (reg 1))) = _
    rw [show logOm (Q98 X) = P98 X from rfl,
      show toList (P98 X) = [P98 X] from rfl,
      List.filter_cons_of_pos (by rw [hltP]; rfl)]
    show ofList [divAP (reg 1) (P98 X)] = X
    show omegaNF (subAP (reg 1) (logOm (P98 X))) = X
    rw [show logOm (P98 X) = add (reg 1) X from by
        show (if phiShifted zero (add (reg 1) X) then _ else _) = _
        rw [show phiShifted zero (add (reg 1) X) = false from by
          show (isFP zero (splitFin (add (reg 1) X)).1 ||
            ((add (reg 1) X == zero) && (zero : Term).isSC)) = false
          rw [splitFin_addWX103 h]
          rfl]
        rfl,
      show subAP (reg 1) (add (reg 1) X) = X from by
        show (match toList (add (reg 1) X) with
              | [] => zero
              | p :: rest => if p == reg 1 then ofList rest else add (reg 1) X) = _
        rw [show toList (add (reg 1) X) = [reg 1, X] from by
              show reg 1 :: toList X = _; rw [good_toList103 h]]
        show (if (reg 1 == reg 1) = true then ofList [X] else _) = X
        rw [if_pos (by rfl)]
        rfl]
    exact h.2.2.2.1
  have hwC : wC (reg 1) (Q98 X) = TM.Term.one := by
    show omegaNF (ofList ((toList (logOm (Q98 X))).filter (fun q => lt q (reg 1)))) = _
    rw [show logOm (Q98 X) = P98 X from rfl,
      show toList (P98 X) = [P98 X] from rfl,
      List.filter_cons_of_neg (by rw [hltP]; exact Bool.noConfusion)]
    rfl
  have hw : wcnf (reg 1) (toList (Q98 X)) = ([(X, TM.Term.one)], zero) := by
    rw [show toList (Q98 X) = [Q98 X] from rfl, wcnf_cons_ge hltQ, wcnf_nil]
    show ([(wA (reg 1) (Q98 X), wC (reg 1) (Q98 X))], (zero : Term)) = _
    rw [hwA, hwC]
  have hfold : ([(X, TM.Term.one)].foldl
      (init := ((none : Option Term), (none : Option Term)))
      (stepF (reg 1) (baseOf 0))).2.getD zero = phi X zero := by
    show (stepF (reg 1) (baseOf 0) (none, none) (X, TM.Term.one)).2.getD zero = _
    show (if le (reg 1) X = true then _ else
      ((none : Option Term), some (phiNF X zero))).2.getD zero = _
    rw [if_neg (by rw [le_W_false103 h]; exact Bool.noConfusion)]
    show phiNF X zero = phi X zero
    exact phiNF_zero_right103 hSC
  have hiV : inT (phi X zero) = true := by
    show (inT X && inT zero && lt X M && lt (zero : Term) M) = true
    rw [h.1, show inT (zero : Term) = true from rfl, good_ltM103 h,
      show lt (zero : Term) M = true from by decide]
    rfl
  rw [collapse0_raw89]
  show omegaNF (plus (reg 0) (plus
    (((wcnf (reg 1) (toList (Q98 X))).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero)
    ((wcnf (reg 1) (toList (Q98 X))).2))) = _
  rw [hw]
  show omegaNF (plus (reg 0) (plus
    (([(X, TM.Term.one)].foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero) zero)) = _
  rw [hfold]
  show omegaNF (plus (reg 0) (plus (phi X zero) zero)) = _
  rw [show plus (phi X zero) zero = phi X zero from rfl,
    show plus (reg 0) (phi X zero) = plus zero (phi X zero) from rfl,
    plus_zero_left_inT hiV, omegaNF_phi98 (lt_zero_ne76 hXnz)]

end

/-! ### §103.4 塔の原像 -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg)
open TM TM.Term
open Evidence.WF

theorem ltM_gTow103 (n : Nat) : lt (gTow102 n) M = true := by
  obtain ⟨u, v, huv⟩ := vTow_one_phi102 n
  rw [show gTow102 n = vTow102 TM.Term.one n from rfl, huv]
  exact lt_phi_M u v

theorem inT_gTow103 : ∀ n, inT (gTow102 n) = true
  | 0 => rfl
  | n + 1 => by
      show (inT (gTow102 n) && inT zero && lt (gTow102 n) M && lt (zero : Term) M) = true
      rw [inT_gTow103 n, ltM_gTow103 n]; rfl

theorem gTow_ne_zero103 (n : Nat) : gTow102 n ≠ zero :=
  vTow_ne_zero102 (show isAP TM.Term.one = true from rfl) n

theorem ltW_gTow103 (n : Nat) : lt (gTow102 n) (reg 1) = true :=
  lt_trans_inT (inT_gTow103 n) (show inT G094 = true from by decide) inT_W79
    (ltG0_cnv103 _ (cnv_gTow103 n)) (show lt G094 (reg 1) = true from by decide)

/-- **`Γ₀` の塔は 1 段目から上が `Good103`。**  `Γ₀ ≤ ·` は成り立たないので `Good98` では
    ない — §103.2 で条を落としてあるのはこのためである。 -/
theorem good103_gTow103 (n : Nat) : Good103 (gTow102 (n + 1)) := by
  refine ⟨inT_gTow103 (n + 1), rfl, ?_, ?_, ltW_gTow103 (n + 1)⟩
  · show (phi (gTow102 n) zero == phi zero zero) = false
    cases hc : (phi (gTow102 n) zero == phi zero zero) with
    | false => rfl
    | true =>
        exfalso
        have hq := eq_of_beq hc
        injection hq with h1 _
        exact gTow_ne_zero103 n h1
  · show omegaNF (phi (gTow102 n) zero) = phi (gTow102 n) zero
    exact omegaNF_phi98 (lt_zero_ne76 (gTow_ne_zero103 n))

theorem isSC_gTow103 (n : Nat) : (gTow102 (n + 1)).isSC = false := rfl

/-- **`Γ₀` の塔の Buchholz 側の原像。**  `ψ₀0`, `ψ₀Ω₁`, `ψ₀ψ₁ψ₁(·)`, …
    1 段目だけが別扱いなのは `Good103` の `X ≠ 1` がそこで初めて立つからである。 -/
def gInv103 : Nat → BT
  | 0 => BT.D 0 BT.zero
  | 1 => BT.D 0 (BT.D 1 BT.zero)
  | n + 2 => BT.D 0 (BT.D 1 (BT.D 1 (gInv103 (n + 1))))

theorem hd085_gInv103 : ∀ n, Hd085 (gInv103 n)
  | 0 => fun _ hx => ⟨BT.zero, List.mem_singleton.mp hx⟩
  | 1 => fun _ hx => ⟨BT.D 1 BT.zero, List.mem_singleton.mp hx⟩
  | n + 2 => fun _ hx => ⟨BT.D 1 (BT.D 1 (gInv103 (n + 1))), List.mem_singleton.mp hx⟩

/-- **段は 1 を超えない。** -/
theorem btLe1_gInv103 : ∀ n, btLe72 1 (gInv103 n) = true
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      show (decide (0 ≤ 1) && (decide (1 ≤ 1) &&
        (decide (1 ≤ 1) && btLe72 1 (gInv103 (n + 1))))) = true
      rw [btLe1_gInv103 (n + 1)]; rfl

/-- 塔は `BT.lt` で真に上がる。 -/
theorem btlt_mono103 : ∀ n, BT.lt (gInv103 n) (gInv103 (n + 1)) = true
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
      have ih := btlt_mono103 (n + 1)
      have h1 : BT.lt (BT.D 1 (gInv103 (n + 1))) (BT.D 1 (gInv103 (n + 2))) = true :=
        btlt_arg98 (bt_ne_of_lt98 ih) ih
      have h2 : BT.lt (BT.D 1 (BT.D 1 (gInv103 (n + 1))))
          (BT.D 1 (BT.D 1 (gInv103 (n + 2)))) = true :=
        btlt_arg98 (bt_ne_of_lt98 h1) h1
      exact btlt_arg98 (bt_ne_of_lt98 h2) h2

/-- `GB 0` の元はみな一段上の `ψ₁ψ₁` の下 — 標準性の帰納法の核。 -/
theorem cov103 : ∀ n, ∀ e ∈ BT.GB 0 (gInv103 n),
    BT.lt e (BT.D 1 (BT.D 1 (gInv103 n))) = true
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
      intro e he
      have hd := hd085_gInv103 (n + 1)
      have hmono := btlt_mono103 (n + 1)
      have hz1 : BT.lt (BT.D 1 (gInv103 (n + 1))) (BT.D 1 (gInv103 (n + 2))) = true :=
        btlt_arg98 (bt_ne_of_lt98 hmono) hmono
      have hz : BT.lt (BT.D 1 (BT.D 1 (gInv103 (n + 1))))
          (BT.D 1 (BT.D 1 (gInv103 (n + 2)))) = true :=
        btlt_arg98 (bt_ne_of_lt98 hz1) hz1
      have hmem : e ∈ BT.D 1 (BT.D 1 (gInv103 (n + 1))) ::
          BT.D 1 (gInv103 (n + 1)) :: gInv103 (n + 1) :: BT.GB 0 (gInv103 (n + 1)) := he
      rcases List.mem_cons.mp hmem with h1 | h1
      · rw [h1]; exact hz
      rcases List.mem_cons.mp h1 with h2 | h2
      · rw [h2]
        exact btlt_arg98 (bt_ne_of_lt98 (btlt_hd0_D1_98 hd (gInv103 (n + 2))))
          (btlt_hd0_D1_98 hd (gInv103 (n + 2)))
      rcases List.mem_cons.mp h2 with h3 | h3
      · rw [h3]; exact btlt_hd0_D1_98 hd _
      · exact lt_trans83 (cov103 (n + 1) e h3) hz

/-- **塔の原像はどれも標準。** -/
theorem isStd_gInv103 : ∀ n, BT.isStd (gInv103 n) = true
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      have hd := hd085_gInv103 (n + 1)
      have hs := isStd_gInv103 (n + 1)
      show (BT.isStd (BT.D 1 (BT.D 1 (gInv103 (n + 1)))) &&
        (BT.GB 0 (BT.D 1 (BT.D 1 (gInv103 (n + 1))))).all
          (fun e => BT.lt e (BT.D 1 (BT.D 1 (gInv103 (n + 1)))))) = true
      rw [isStd_D1D1_98 hd hs, Bool.true_and, List.all_eq_true]
      intro x hx
      have hmem : x ∈ BT.D 1 (gInv103 (n + 1)) :: gInv103 (n + 1) ::
          BT.GB 0 (gInv103 (n + 1)) := hx
      rcases List.mem_cons.mp hmem with h1 | h1
      · rw [h1]
        exact btlt_arg98 (bt_ne_of_lt98 (btlt_hd0_D1_98 hd (gInv103 (n + 1))))
          (btlt_hd0_D1_98 hd (gInv103 (n + 1)))
      rcases List.mem_cons.mp h1 with h2 | h2
      · rw [h2]; exact btlt_hd0_D1_98 hd _
      · exact cov103 (n + 1) x h2

/-- **§103.4 の主定理 — `Γ₀` の塔はどの段も `dict` の像である。**
    §102.4 が `iterGamma_gTow102` で「これは repo 自身の基本列 `fsN Γ₀` である」と言った
    その塔が、まるごと `dict` の像の中にいる。 -/
theorem dict_gInv103 (Hp : PsiIdxOKStd172) : ∀ n, dict (gInv103 n) = gTow102 n
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
      have ih := dict_gInv103 Hp (n + 1)
      have hg : Good103 (dict (gInv103 (n + 1))) := by rw [ih]; exact good103_gTow103 n
      have hSC : (dict (gInv103 (n + 1))).isSC = false := by rw [ih]; exact isSC_gTow103 n
      show collapse 0 (dict (BT.D 1 (BT.D 1 (gInv103 (n + 1))))) = phi (gTow102 (n + 1)) zero
      rw [dict_D1D1x103 Hp (btLe1_gInv103 (n + 1)) (isStd_gInv103 (n + 1))
          (hd085_gInv103 (n + 1)) hg,
        collapse0_Q103 hg hSC, ih]

end

/-! ### §103.5 密度の門に何が効いたか — 目標 `Γ₀` は仮説ではなくなる -/

section
open Trans.Recal
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

/-- **目標が `Γ₀` ちょうどのところは定理である。**  `Γ₀` より下の挑戦者はどれも
    §102.4 の塔のある段以下にいて、その段は §103.4 で `dict` の像だから、その原像が証人に
    なる。仮説は `PsiIdxOKStd172` ひとつだけ。 -/
theorem denseAtGam0_103 (Hp : PsiIdxOKStd172) {s : Term} (hs : inT s = true)
    (hlt : lt s G094 = true) :
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
      le s (dict b) = true ∧ lt (dict b) G094 = true := by
  obtain ⟨n, hn⟩ := cofGam0_102 s hs hlt
  refine ⟨gInv103 n, btLe1_gInv103 n, isStd_gInv103 n, hd085_gInv103 n, ?_, ?_⟩
  · rw [dict_gInv103 Hp n]; exact hn
  · rw [dict_gInv103 Hp n]; exact ltG0_cnv103 _ (cnv_gTow103 n)

/-- **§102.6 の (b1) から端点 `v = Γ₀` を外したもの。**  `DictOntoMid102` より真に弱い
    — `open_of_ontoMid103` が一方向で、逆は全射性と稠密性の差だけ強い。**証明しない。** -/
def DictOntoMidOpen103 : Prop := ∀ v : Term, inT v = true → lt E081 v = true →
    lt v G094 = true → ∀ s : Term, inT s = true → lt s v = true →
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
      le s (dict b) = true ∧ lt (dict b) v = true

/-- `DictOntoMid102` は `DictOntoMidOpen103` を含む。 -/
theorem open_of_ontoMid103 (H : DictOntoMid102) : DictOntoMidOpen103 :=
  fun _ hiv hvE hvG _ hs hlt => denseMid_of_onto102 H hiv (le_of_lt94 hvG) hvE hs hlt

/-- **(b1) は端点と内部に分かれ、端点はもう定理である。** -/
theorem denseMid_of_open103 (Hp : PsiIdxOKStd172) (H : DictOntoMidOpen103) {v : Term}
    (hiv : inT v = true) (hvG : le v G094 = true) (hvE : lt E081 v = true)
    {s : Term} (hs : inT s = true) (hlt : lt s v = true) :
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
      le s (dict b) = true ∧ lt (dict b) v = true := by
  rcases (Bool.or_eq_true _ _).mp hvG with h1 | h1
  · have hv : v = G094 := eq_of_beq h1
    subst hv
    exact denseAtGam0_103 Hp hs hlt
  · exact H v hiv hvE h1 s hs hlt

/-- **§102.6 の主定理を弱い仮説で。**  (a) は §102.5、(b1) の端点は §103.5、
    残るのは (b1) の内部・(b2)・(c) の三本である。 -/
theorem dictDenseHi_of103 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (H1 : DictOntoMidOpen103) (H3 : DictDenseMid102) (H4 : DictDenseAbove102) :
    DictDenseHi94 := by
  intro t ht _ hvE s hs _ hlt
  have hiv : inT (vOf t) = true := inT_vOf94 Hp t ht
  have hiG1 : inT Gam1_94 = true := inT_Gam1_102 Hp
  rcases lt_trichotomy_inT hiv hiG1 with hv | hv | hv
  · rcases lt_trichotomy_inT hiv inT_G094_102 with hg | hg | hg
    · exact denseMid_of_open103 Hp H1 hiv (le_of_lt94 hg.1) hvE hs hlt
    · exact denseMid_of_open103 Hp H1 hiv (by rw [hg.2.1]; exact le_self G094) hvE hs hlt
    · exact H3 (vOf t) hiv hg.2.2 hv.1 s hs hlt
  · rcases lt_trichotomy_inT hs hiG1 with hsg | hsg | hsg
    · exact denseHi_below_Gam1_102 Hp H2 hiv (by rw [hv.2.1]; exact le_self Gam1_94) hs hsg.1
    · exact H4 (vOf t) hiv (by rw [hv.2.1]; exact le_self Gam1_94) s hs
        (by rw [hsg.2.1]; exact le_self Gam1_94) hlt
    · exact H4 (vOf t) hiv (by rw [hv.2.1]; exact le_self Gam1_94) s hs
        (le_of_lt94 hsg.2.2) hlt
  · rcases lt_trichotomy_inT hs hiG1 with hsg | hsg | hsg
    · exact denseHi_below_Gam1_102 Hp H2 hiv (le_of_lt94 hv.2.2) hs hsg.1
    · exact H4 (vOf t) hiv (le_of_lt94 hv.2.2) s hs (by rw [hsg.2.1]; exact le_self Gam1_94) hlt
    · exact H4 (vOf t) hiv (le_of_lt94 hv.2.2) s hs (le_of_lt94 hsg.2.2) hlt

/-- 326 行目の証明書 — 密度の側で待つのは (b1) の**内部**と (b2)・(c) の三本。 -/
theorem certIn_t326_103 (Hp : PsiIdxOKStd172) (H : HiMono89)
    (H1 : DictOntoMidOpen103) (H3 : DictDenseMid102) (H4 : DictDenseAbove102)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_99 Hp H (dictDenseHi_of103 Hp (dictLtA74_99 Hp H) H1 H3 H4) hacc

end

/-! ### §103.6 段の正直さ — 上へは 1 まで、下へは 0 では届かない -/

section
open Trans.Recal
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

/-- **構成は 1 段目から上で段 0 を離れる。**  §98.8 の `btLe0_bTowG98` と同じ規律。 -/
theorem btLe0_gInv103 : ∀ n, btLe72 0 (gInv103 (n + 1)) = false
  | 0 => rfl
  | _ + 1 => rfl

/-- **そして離れるほかない。**  §81.6 の `lt_dict_E81` により段 0 の標準項の値は
    `ε₀` より下にしかないので、`(ε₀, Γ₀]` の証人は**一つも**段 0 では作れない。
    §97 の構成がこの区間に届かないのは偶然ではない。 -/
theorem noLevel0_inMid103 (Hp : PsiIdxOKStd172) {s : Term} (h : lt E081 s = true) :
    ¬ ∃ b : BT, btLe72 0 b = true ∧ BT.isStd b = true ∧ dict b = s := by
  rintro ⟨b, hb, hst, hd⟩
  have h1 : lt (dict b) E081 = true := lt_dict_E81 Hp b hb hst
  have his : inT s = true := by
    rw [← hd]; exact (inT_dict_of_std172 Hp b (btLe72_mono81 b hb) hst).1
  rw [hd, lt_asymm_inT inT_E81 his h] at h1
  exact Bool.noConfusion h1

end

/-! ### §103.7 この区間の junk — Veblen の形をしていて、欠陥は一段内側にある -/

section
open Trans.Recal
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

/-- **`(ε₀, Γ₀)` の junk。**  `φ̄(1, ψ_1(0))`。Veblen の形をしているのに 2.1(vi) の
    `κ ∈ R` を Veblen の**引数**の中で破る。§97 の `junk97 = φ̄(0 ⊕ M, 0)` は `ε₀` より
    下、§102 の `junk1_102` は `Γ₀` より上、§102 の `junk0_102 = ψ_1(0)` はこの区間に
    いるが 2.1(vi) を最上位で破る — 三つとも別の項で、別の場所で効く。 -/
def junkV103 : Term := phi TM.Term.one (psi TM.Term.one zero)

theorem lt_zero_psi103 (k c : Term) : lt zero (psi k c) = true :=
  lt_zero_ne76 (by intro h; exact Term.noConfusion h)

theorem lt_zero_Z103 (d : Term) : lt zero (Z d) = true :=
  lt_zero_ne76 (by intro h; exact Term.noConfusion h)

theorem lt_one_G0_103 : lt TM.Term.one G094 = true := by
  show lt (phi zero zero) (psi (Z zero) zero) = true
  rw [lt_phi_psi103, lt_zero_psi103]; rfl

theorem lt_one_Om103 : lt TM.Term.one (Z zero) = true := by
  show lt (phi zero zero) (Z zero) = true
  rw [lt_phi_Z103, lt_zero_Z103]; rfl

/-- `ψ_1(0) < Γ₀` — 2.3.14(ii) を一歩だけ。`decide` は `starF` の層で走り切らないので
    節を手で当てる。 -/
theorem lt_junk0_G0_103 : lt junk0_102 G094 = true := by
  have hne : psi TM.Term.one zero ≠ psi (Z zero) zero := by
    intro h; injection h with h1 _; exact Term.noConfusion h1
  show lt (psi TM.Term.one zero) (psi (Z zero) zero) = true
  rw [lt_eq_ltF_succ, ltF_succ_psi_psi _ hne,
    if_neg (by intro h; exact Term.noConfusion h),
    show ltF (2 * ((psi TM.Term.one zero).deg + (psi (Z zero) zero).deg) + 7)
        TM.Term.one (Z zero) = lt TM.Term.one (Z zero) from
      (lt_eq_ltF TM.Term.one (Z zero) _ (by
        show (1 + (zero : Term).deg + (zero : Term).deg) + (1 + (zero : Term).deg)
          ≤ 2 * ((1 + (1 + (zero : Term).deg + (zero : Term).deg) + (zero : Term).deg)
              + (1 + (1 + (zero : Term).deg) + (zero : Term).deg)) + 7
        simp only [TM.Term.deg]; omega)).symm,
    lt_one_Om103, if_pos rfl,
    show ltF (2 * ((psi TM.Term.one zero).deg + (psi (Z zero) zero).deg) + 7)
        TM.Term.one (psi (Z zero) zero) = lt TM.Term.one (psi (Z zero) zero) from
      (lt_eq_ltF TM.Term.one (psi (Z zero) zero) _ (by
        show (1 + (zero : Term).deg + (zero : Term).deg)
            + (1 + (1 + (zero : Term).deg) + (zero : Term).deg)
          ≤ 2 * ((1 + (1 + (zero : Term).deg + (zero : Term).deg) + (zero : Term).deg)
              + (1 + (1 + (zero : Term).deg) + (zero : Term).deg)) + 7
        simp only [TM.Term.deg]; omega)).symm]
  exact lt_one_G0_103

theorem lt_junkV_G0_103 : lt junkV103 G094 = true := by
  show lt (phi TM.Term.one (psi TM.Term.one zero)) (psi (Z zero) zero) = true
  rw [lt_phi_psi103,
    show lt TM.Term.one (psi (Z zero) zero) = true from lt_one_G0_103,
    show lt (psi TM.Term.one zero) (psi (Z zero) zero) = true from lt_junk0_G0_103]
  rfl

/-- **`ψ_1(0)` は Veblen 標準形をすべて超える。**  2.3.4 と 2.3.10 の二節だけを使う。 -/
theorem le_junk0_cnv103 : ∀ (y : Term), CNV y = true → le junk0_102 y = false
  | zero, _ => by
      show ((junk0_102 == zero) || lt junk0_102 zero) = false
      rw [show (junk0_102 == zero) = false from rfl, lt_right_zero102]
      rfl
  | M, h => Bool.noConfusion h
  | omg _, h => Bool.noConfusion h
  | psi _ _, h => Bool.noConfusion h
  | Z _, h => Bool.noConfusion h
  | phi c d, h => by
      obtain ⟨hc, hd⟩ := cnv_phi h
      obtain ⟨hec, hlc⟩ := Bool.or_eq_false_iff.mp (le_junk0_cnv103 c hc)
      obtain ⟨hed, hld⟩ := Bool.or_eq_false_iff.mp (le_junk0_cnv103 d hd)
      show ((junk0_102 == phi c d) || lt junk0_102 (phi c d)) = false
      rw [show (junk0_102 == phi c d) = false from rfl,
        show lt junk0_102 (phi c d) = _ from lt_psi_phi_eq102 TM.Term.one zero c d,
        show (psi TM.Term.one zero == c) = false from hec,
        show (psi TM.Term.one zero == d) = false from hed,
        show lt (psi TM.Term.one zero) c = false from hlc,
        show lt (psi TM.Term.one zero) d = false from hld]
      rfl
  | add a b, h => by
      obtain ⟨_, ha, _, _⟩ := cnv_add h
      show ((junk0_102 == add a b) || lt junk0_102 (add a b)) = false
      rw [show (junk0_102 == add a b) = false from rfl,
        Cert.lt_ap_add (show isAP junk0_102 = true from rfl) a b,
        le_junk0_cnv103 a ha]
      rfl

/-- **`φ̄(1, ψ_1(0))` も Veblen 標準形をすべて超える。**  2.3.13 の三節はどれも
    `ψ_1(0)` 側か第 2 引数側へ落ちるので、帰納法はそのまま回る。 -/
theorem le_junkV_cnv103 : ∀ (y : Term), CNV y = true → le junkV103 y = false
  | zero, _ => by
      show ((junkV103 == zero) || lt junkV103 zero) = false
      rw [show (junkV103 == zero) = false from rfl, lt_right_zero102]
      rfl
  | M, h => Bool.noConfusion h
  | omg _, h => Bool.noConfusion h
  | psi _ _, h => Bool.noConfusion h
  | Z _, h => Bool.noConfusion h
  | phi c d, h => by
      obtain ⟨_, hd⟩ := cnv_phi h
      have hne : junkV103 ≠ phi c d := by
        intro hq
        have hq2 : phi TM.Term.one (psi TM.Term.one zero) = phi c d := hq
        injection hq2 with _ h2
        rw [← h2] at hd
        exact Bool.noConfusion hd
      have hJd : lt junk0_102 d = false :=
        (Bool.or_eq_false_iff.mp (le_junk0_cnv103 d hd)).2
      have hJy : lt junk0_102 (phi c d) = false :=
        (Bool.or_eq_false_iff.mp (le_junk0_cnv103 (phi c d) h)).2
      have hVd : le junkV103 d = false := le_junkV_cnv103 d hd
      show ((junkV103 == phi c d) || lt junkV103 (phi c d)) = false
      rw [show (junkV103 == phi c d) = false from by
            cases hcc : (junkV103 == phi c d) with
            | false => rfl
            | true => exact absurd (eq_of_beq hcc) hne,
        show lt junkV103 (phi c d) = _ from lt_phi_phi hne]
      by_cases h1 : TM.Term.one = c
      · rw [if_pos h1, show lt (psi TM.Term.one zero) d = false from hJd]; rfl
      · rw [if_neg h1]
        by_cases h2 : lt TM.Term.one c = true
        · rw [if_pos h2, show lt (psi TM.Term.one zero) (phi c d) = false from hJy]; rfl
        · rw [if_neg h2,
            show le (phi TM.Term.one (psi TM.Term.one zero)) d = false from hVd]; rfl
  | add a b, h => by
      obtain ⟨_, ha, _, _⟩ := cnv_add h
      show ((junkV103 == add a b) || lt junkV103 (add a b)) = false
      rw [show (junkV103 == add a b) = false from rfl,
        Cert.lt_ap_add (show isAP junkV103 = true from rfl) a b,
        le_junkV_cnv103 a ha]
      rfl

/-- **§103.5 から `inT` を落とすと偽。**  junk は `(ε₀, Γ₀)` にいて、しかも `dict` の
    像 (= §103.1 により `Γ₀` より下の 𝔗(M) の項ぜんぶ = Veblen 標準形ぜんぶ) を
    **すべて超える**から、証人が 1 つも取れない。§97.8 の `denseLo_needs_inT97` の
    一階上で、破れる条は 2.1(iii) ではなく 2.1(vi) である。 -/
theorem denseAtGam0_needs_inT103 (Hp : PsiIdxOKStd172) :
    ¬ (∀ s : Term, lt s G094 = true →
        ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
          le s (dict b) = true ∧ lt (dict b) G094 = true) := by
  intro H
  obtain ⟨b, hb, hst, _, hle, hlt⟩ := H junkV103 lt_junkV_G0_103
  have hi := (inT_dict_of_std172 Hp b hb hst).1
  rw [le_junkV_cnv103 _ (cnv_of_ltG0_103 hi hlt)] at hle
  exact Bool.noConfusion hle

/-- 同じことを §102 の `junk0_102` で。破れる条は同じ 2.1(vi) だが、こちらは
    Veblen の形すらしていない。 -/
theorem denseAtGam0_needs_inT_psi103 (Hp : PsiIdxOKStd172) :
    ¬ (∀ s : Term, lt s G094 = true →
        ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
          le s (dict b) = true ∧ lt (dict b) G094 = true) := by
  intro H
  obtain ⟨b, hb, hst, _, hle, hlt⟩ := H junk0_102 lt_junk0_G0_103
  have hi := (inT_dict_of_std172 Hp b hb hst).1
  rw [le_junk0_cnv103 _ (cnv_of_ltG0_103 hi hlt)] at hle
  exact Bool.noConfusion hle

end

/-! ### §103.8 測定 — 母集団の作り方と、`dictInv` が神託ではないこと -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv)
open TM TM.Term
open Evidence.WF

/-! **断片の主張はぴったり。**  §102.8 の母集団をそのまま使う — ill-formed な形が
    18 個の種のうちに入っていて、濾していない。`CNV s` が成り立つのはちょうど
    `inT s && s < Γ₀` のとき。食い違いは両向きとも 0。 -/
#eval (pool102.length,
       pool102.countP fun s => CNV s,
       pool102.countP fun s => inT s && lt s G094)
#guard pool102.countP (fun s => CNV s && !(inT s && lt s G094)) == 0
#guard pool102.countP (fun s => (inT s && lt s G094) && !(CNV s)) == 0

/-! **`inT` は飾りではなく、落ちるところが見えている。**  `Γ₀` より下で `inT` でない
    項の数と、そのうち §102.4 の塔に押さえられてしまう数。 -/
#eval (pool102.countP fun s => !(inT s) && lt s G094,
       pool102.countP fun s => !(inT s) && lt s G094 && le s (gTow102 (htG102 s)))
#guard (pool102.countP fun s => !(inT s) && lt s G094) > 0
/-! 後者が 0 でないので、仮説は結論の言い換えではない。 -/
#guard (pool102.countP fun s => !(inT s) && lt s G094 && le s (gTow102 (htG102 s))) > 0

/-! **名指しの junk。**  区間の中にいて、`inT` でなく、`CNV` でもなく、塔のどの段も
    超え、`dictInv` の像でもない。 -/
#guard lt E081 junkV103 && lt junkV103 G094 && !(inT junkV103) && !(CNV junkV103)
#guard lt E081 junk0_102 && lt junk0_102 G094 && !(inT junk0_102) && !(CNV junk0_102)
#guard (List.range 12).all fun n => le junkV103 (gTow102 n) == false
#guard (List.range 12).all fun n => le junk0_102 (gTow102 n) == false
#guard (dictInv junkV103).isNone
/-! それぞれが破る条 — どちらも 2.1(vi) の `κ ∈ R` だが、`junkV103` は Veblen の
    引数の中で破る。 -/
#guard isR TM.Term.one == false
#guard inT (psi TM.Term.one zero) == false

/-! **ill-formed でも塔に押さえられるものはある** — `φ̄(1, 0 ⊕ M)`。
    2.1(iii) を破るが、値は小さい。 -/
def junkDom103 : Term := phi TM.Term.one (add zero M)
#guard !(inT junkDom103) && lt E081 junkDom103 && lt junkDom103 G094
#guard (List.range 12).any fun n => le junkDom103 (gTow102 n)

/-! **塔、計算。**  8 段：値はぴったり `gTow102 n`、段は 1 以下、1 段目から上は
    段 0 では書けない、標準で頭は `D 0`。 -/
#guard (List.range 8).all fun n => dict (gInv103 n) == gTow102 n
#guard (List.range 8).all fun n =>
  btLe72 1 (gInv103 n) && BT.isStd (gInv103 n) && hd085B (gInv103 n)
#guard (List.range 8).all fun n => btLe72 0 (gInv103 (n + 1)) == false
#guard (List.range 8).all fun n => inT (gTow102 n) && lt (gTow102 n) G094
#guard (List.range 8).all fun n => lt (gTow102 n) (gTow102 (n + 1))

/-! ### 全射の測定をやり直す — §102.9 より意地悪な母集団で

§102.9 は `midPool102` の 129 項すべてに合法な `dictInv` 逆像があると報告した。
その母集団は `φ̄(x,y)` と `plus` の一段の閉包で、**固定点を第 2 引数に持つ形が
ほとんど入っていない**。種にそれを入れて作り直すと、`dictInv` は取りこぼす。 -/

private def aseed103 : List Term :=
  [zero, TM.Term.one, TM.Term.omega, ofNat 2, ofNat 3,
   phi TM.Term.one zero,
   phi (ofNat 2) zero,
   phi TM.Term.omega zero,
   phi (phi TM.Term.one zero) zero,
   phi TM.Term.one TM.Term.one,
   phi zero (phi TM.Term.one zero),
   phi TM.Term.one (phi (ofNat 2) zero),
   phi TM.Term.one (plus (phi (ofNat 2) zero) TM.Term.one),
   plus (phi (ofNat 2) zero) (phi TM.Term.one zero),
   phi TM.Term.one (plus (phi (ofNat 2) zero) TM.Term.omega),
   phi zero (plus (phi TM.Term.one zero) TM.Term.one)]

private def agrow103 (p : List Term) : List Term :=
  (p ++ (p.flatMap fun x => p.map fun y => phi x y)
     ++ (p.flatMap fun x => p.map fun y => plus x y)).eraseDups

/-- `(ε₀, Γ₀)` の中の 𝔗(M) の項 — 敵対的な種から。 -/
def aPool103 : List Term :=
  (agrow103 aseed103).filter fun t => inT t && lt E081 t && lt t G094

/-- 「合法な逆像がある」を `dictInv` を神託にして測る述語。 -/
def legalPre103 (t : Term) : Bool :=
  match dictInv t with
  | some b => dict b == t && btLe72 1 b && BT.isStd b && hd085B b
  | none => false

/-! 母集団の大きさ、合法な逆像の数、逆像そのものの数。**逆像は全部にあるのに
    合法なのは全部ではない。** -/
#eval (aPool103.length, aPool103.countP legalPre103,
       aPool103.countP fun t => (dictInv t).isSome)
#guard aPool103.length > 300
#guard aPool103.countP (fun t => (dictInv t).isSome) == aPool103.length
#guard aPool103.countP legalPre103 < aPool103.length

/-! 取りこぼしはどれも `φ̄(a, φ̄(a, ·))` — 第 1 引数が**同じ**入れ子。
    `vebPairs` の剥がし判定は `lt a a₁` で真に大きいときしか働かない。 -/
#eval ((aPool103.filter fun t => !(legalPre103 t)).map fun t => t.toStr)
#guard (aPool103.filter fun t => !(legalPre103 t)).all fun t => match t with
  | phi a (phi a1 _) => a == a1
  | phi a (add (phi a1 _) _) => a == a1
  | _ => false
/-! 値は合っているのに標準でない、が取りこぼしの中身である。 -/
#guard (aPool103.filter fun t => !(legalPre103 t)).all fun t => match dictInv t with
  | some b => dict b == t && !(BT.isStd b)
  | none => false

/-! **取りこぼした 5 項には合法な証人が実在する — 手で作った。**
    だから 5 項は `dict` の穴ではなく `dictInv` の不完全さであり、
    `DictOntoMid102` は反証されていない。 -/
private def bOne103 : BT := BT.D 0 BT.zero                     -- 1
private def bOm103 : BT := BT.D 1 BT.zero                      -- Ω₁
private def bOO103 : BT := BT.D 1 (BT.D 1 BT.zero)             -- Ω₁²
private def bE1_103 : BT := BT.D 0 (BT.sum bOO103 bOm103)      -- ε_{ζ₀+1}
private def bE2_103 : BT := BT.D 0 (BT.sum bOO103 (BT.sum bOm103 bOm103))
private def bE3_103 : BT := BT.D 0 (BT.sum bOO103 (BT.D 1 bOne103))

/-- `dictInv` が取りこぼす 5 項と、手で作った合法な証人。 -/
def witMiss103 : List (Term × BT) :=
  [(phi zero (phi zero (phi TM.Term.one zero)),
      BT.D 0 (BT.sum bOm103 (BT.D 0 (BT.sum bOm103 bOne103)))),
   (phi zero (phi zero (plus (phi TM.Term.one zero) TM.Term.one)),
      BT.D 0 (BT.sum bOm103 (BT.D 0 (BT.sum bOm103 (BT.sum bOne103 bOne103))))),
   (phi TM.Term.one (phi TM.Term.one (phi (ofNat 2) zero)),
      BT.D 0 (BT.sum bOO103 (BT.D 1 bE1_103))),
   (phi TM.Term.one (phi TM.Term.one (plus (phi (ofNat 2) zero) TM.Term.one)),
      BT.D 0 (BT.sum bOO103 (BT.D 1 bE2_103))),
   (phi TM.Term.one (phi TM.Term.one (plus (phi (ofNat 2) zero) TM.Term.omega)),
      BT.D 0 (BT.sum bOO103 (BT.D 1 bE3_103)))]

#guard witMiss103.all fun p =>
  dict p.2 == p.1 && btLe72 1 p.2 && BT.isStd p.2 && hd085B p.2
#guard witMiss103.all fun p => !(legalPre103 p.1)
#guard witMiss103.all fun p => inT p.1 && lt E081 p.1 && lt p.1 G094
#guard (aPool103.filter fun t => !(legalPre103 t)).all fun t =>
  witMiss103.any fun p => p.1 == t
#guard witMiss103.length == (aPool103.filter fun t => !(legalPre103 t)).length

end

/-! ## §104 THE COEFFICIENT'S `z` IS NAMEABLE, AND NAMING IT IS FREE

§99 collapsed row 326's whole Veblen fold onto `HiMono89`; §101 took §99's approach (i) —
replace the `K`-condition by a 𝔗(M)-side predicate — and showed the two predicates its
vocabulary could express are not enough, with a BUILT pair that REVERSES the order.  Its
closing diagnosis was sharp:

> What breaks is a COEFFICIENT, not a component.  `hiArg_lt101` / `loArg_lt101` push the
> `K`-condition across for the components free of charge, but a coefficient is not a
> component: naming the `z` inside it needs the SURJECTIVE half of the bridge — §99's
> circle, unbroken.

**§104 answers that question, and the answer is that the surjective half is not needed at a
coefficient.**  The diagnosis is right about a 𝔗(M)-side predicate — a function of
`hi (dict a)` alone genuinely cannot see `z` — and wrong about the clause: `HiMono89` is
stated on `BT` terms, and from the `BT` side §101.1's own free inclusion, applied ONE LEVEL
DOWN, names `z` and §82's `G(·,0)` bounds it.  What that costs is one lemma the repository
did not have, and it is the converse of one §100 proved.

WHAT IS PROVED.

  §104.1  **`logOm ∘ ω^· = id` BELOW `M`** (`logOm_omegaNF104`).  §100 proved
          `omegaNF_logOm100` (`p ∈ AP ⟹ ω^(logOm p) = p`); the other direction was absent
          (searched: `logOm` carries `inT_logOm`, `ltM_logOm`, `logOm_eq_self_of_ne`,
          `logOm_mono_*`, `lt_logOm_of_sc`, `mem_Kset_logOm`, `pure73_logOm` and nothing
          else).  The content is that [Rathjen, 1991] 2.7's recalibration is an involution
          on the nose: `phiNF_zero_eq104` says `φ̄0` has exactly two branches — `isFP 0 t`
          returns `t`, otherwise `φ̄(0, dnArg t)` — `dnArg_eq104` names the step-down, and
          `splitFin_ap_ofNat104` (`splitFin (g ⊕ k) = (g, k)` for `g ∈ AP`, `g ≠ 1`) puts
          the trailing `1` back exactly where `phiShifted` looks for it.

  §104.2  **THE `ψ₁`-IMAGE'S EXPONENT AND COEFFICIENT, IN CLOSED FORM.**
          `logOm_dict_D1_104` : `logOm (dict (ψ₁ c)) = Ω₁ ⊕ dict c`, and hence
          `wC_dict_D1_104` : the coefficient the base-`Ω₁` decomposition hands to the fold
          at that component is `ω^(lo (dict c))` — **the `ω`-power of the part of `c`'s own
          image below `Ω₁`, and nothing else.**  §98.3's `dict_D1x98` had the value under
          `Good98` (`X < Ω₁`, `Γ₀ ≤ X`); this is the `logOm` of it with no guard at all.

  §104.3  **THE COEFFICIENT'S `z`, NAMED — GATE-FREE** (`coefArg104`).  For `ψ₀a` standard:
          every `p ∈ hi (dict a)` is `dict (ψ₁ c)` with `c < a` (§101.1), its coefficient is
          `ω^(lo (dict c))` (§104.2), every component of `lo (dict c)` is `dict (ψ₀ d)`
          (§101.1 again, at `c`), and every such `d` is in `G(a,0)`, hence `d < a`
          (`sub_GB0_104` + §82's `arg_mem_GB0_82` + `std0_split82`).  **The whole chain uses
          only the INCLUSION half of the bridge, which §101.1 proved outright.**

  §104.4  **APPROACH (i), REDONE ON THE `BT` SIDE.**  `CoefOK104 a` — every `ψ₀`-argument
          occurring in a coefficient of `a` is `< a` — is decidable, local, and a free
          consequence of the `K`-condition (`coefOK104_of_std`, no gate, no `PsiIdxOKStd172`).
          `HiMonoCoef104` is `HiMono89` with `BT.isStd (ψ₀ ·)` replaced by
          `BT.isStd · ∧ CoefOK104 ·`, `hiMono_of_coef104` gives `HiMono89` from it and
          `certIn_t326_coef104` re-hangs row 326 on it.  **And §101's witnesses do not reach
          it**: `CoefOK104 bothBadA101 = false` and `CoefOK104 scBadA101 = false`
          (`coefOK_kills101_104`), while `foldNF101` and `ksetOK101` are both TRUE there —
          so the pair that refutes both of §101's candidates refutes neither this one.

WHAT IS **NOT** CLAIMED.  `HiMono89` is NOT proved and NOT refuted.  **§104 MOVES the
residue, it does not remove it**, and it moves it to a STRICTLY STRONGER statement:
`sepA104` is a BUILT term with `CoefOK104` true and `BT.isStd (ψ₀ ·)` false (10 symbols,
`ψ₁ψ₀Ω₁ ⊕ ψ₀ψ₁ψ₁Ω₁`), so `HiMonoCoef104` asks for strictly more than `HiMono89`.  What is
bought is that the hypothesis is now a local decidable condition naming exactly the objects
the fold consumes, and that §101's negative — the only thing standing against approach (i) —
does not apply to it.  Row 326 still rests on `PsiIdxOKStd172`, `HiMono89`,
`DictOntoMidOpen103`, `DictDenseMid102`, `DictDenseAbove102`.

**WHERE §104 STOPPED, PRECISELY.**  Naming the coefficient is not yet comparing two folds.
The Veblen branch needs `φ̄(α,γ) < φ̄(β,δ)` for `α < β`, which holds iff `γ < φ̄(β,δ)` — i.e.
`a`'s coefficient below `b`'s VALUE — and §104 delivers `a`'s coefficient below `a` as a `BT`
term.  Turning `d < a` into `dict (ψ₀ d) < ψ₀(hi (dict b))` is an instance of the gate at
`(d, b)` with `size d < size a` (§93.1's `size_GB93`) but with no relation between `d` and
`b`; that is §99.4's measure again, and §104 does not run it.  What §104.6 does establish is
that the 𝔗(M)-side reading of the same bound is the WRONG one.

WHAT THE MEASUREMENT SAYS (§104.6 gives the construction).  Two populations, both BUILT to
offend, neither filtered.

  * **The hypothesis is visible.**  Of 220 constructed terms, 128 fail `CoefOK104` and 88
    are `K`-standard; **no `K`-standard term fails `CoefOK104`** — §104.4's theorem, seen.
  * **The first population is BLIND, and it says so.**  On its 60-term sample `CoefOK104`
    and the `K`-condition hold on the SAME 30 terms and give the SAME 643 pairs with the
    SAME 0 breaks.  §96's mistake, recognised rather than repeated: that sweep is not
    evidence, so a second family was BUILT for the difference.
  * **The separating family separates.**  71 terms, of which **21 satisfy `CoefOK104` and
    fail the `K`-condition**; 2462 residual pairs, 677 breaks; filtering by `CoefOK104` on
    the LEFT term alone leaves **887 pairs and 0 breaks**, against the `K`-condition's 184
    pairs and 0 breaks.  The weaker hypothesis carries the conclusion on 4.8× the pairs.
  * **Width, and the merging case.**  A third family puts TWO caps on each term, so the
    coefficient arguments come in pairs and the base-`Ω₁` decomposition MERGES two
    components into one pair whose coefficient is a `plus` — the case §104.3's per-component
    statement has to survive.  95 terms, 4465 residual pairs, 1384 breaks; `CoefOK104`
    leaves **604 pairs and 0 breaks**.
  * **The 𝔗(M)-side reading of the same bound is NOT the condition.**  `coefLt104` —
    every low component of `a`'s exponents below `ψ₀(hi (dict b))`, which is what a
    predicate on 𝔗(M) terms can say — leaves **27 breaks of 1370** on the first population,
    **71 of 1856** on the second and **265 of 3346** on the third.  §101's diagnosis,
    measured: the 𝔗(M) side cannot say it, and the `BT` side can.
  * **Nothing is vacuous.**  Every term of all three populations has at least one
    coefficient argument, so `CoefOK104` is never satisfied by having nothing to check.
-/

/-! ### §104.1 `logOm ∘ ω^·` は `M` の下では恒等 — §100 の逆 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

theorem takeWhile_replicate_one104 (g : Term) (hg : (g == one) = false) : ∀ k : Nat,
    (List.replicate k one ++ [g]).takeWhile (fun x => x == one) = List.replicate k one
  | 0 => by
      show (match (g == one) with | true => _ | false => []) = _
      rw [hg]; rfl
  | k + 1 => by
      rw [List.replicate_succ, List.cons_append,
        List.takeWhile_cons_of_pos (p := fun x => x == one) (by simp),
        takeWhile_replicate_one104 g hg k, ← List.replicate_succ]

/-- `splitFin` を成分列の言葉で書き直したもの。 -/
theorem splitFin_eq104 (b : Term) :
    splitFin b =
      (ofList ((toList b).take ((toList b).length -
          ((toList b).reverse.takeWhile (fun x => x == one)).length)),
       ((toList b).reverse.takeWhile (fun x => x == one)).length) := rfl

/-- **`splitFin` は `g ⊕ k` をそのまま割る** — `g` が `1` でない AP なら。 -/
theorem splitFin_ap_ofNat104 {g : Term} (hi : inT g = true) (ha : g.isAP = true)
    (hne : (g == one) = false) (k : Nat) : splitFin (plus g (ofNat k)) = (g, k) := by
  have hl : toList (plus g (ofNat k)) = g :: List.replicate k one := by
    rw [toList_plus_ofNat_inT hi k, toList_of_isAP ha]; rfl
  rw [splitFin_eq104, hl, List.reverse_cons, List.reverse_replicate,
    takeWhile_replicate_one104 g hne k, List.length_replicate,
    show (g :: List.replicate k one).length = k + 1 from by
      rw [List.length_cons, List.length_replicate],
    show k + 1 - k = 1 from by omega]
  rfl


/-- `phiNF zero` は二枝しかない — `φ̄0` の不動点ならそのまま、さもなくば数え直した `φ̄0`。 -/
theorem phiNF_zero_eq104 : ∀ (t : Term),
    phiNF zero t = if isFP zero t = true then t else phi zero (dnArg t)
  | .zero => by
      rw [if_neg (show ¬ (isFP zero (zero : Term) = true) from by
        show ¬ (((zero : Term).isSC && lt zero zero) || false) = true
        rw [show ((zero : Term).isSC && lt zero zero) = false from rfl]
        exact Bool.noConfusion)]
      show phiNFsucc zero zero = _
      exact phiNFsucc_zero_eq _
  | .M => by
      rw [if_pos (show isFP zero (M : Term) = true from by
        show (((M : Term).isSC && lt zero M) || false) = true
        rw [show ((M : Term).isSC && lt zero M) = true from rfl]; rfl)]
      show (if ((M : Term).isSC && lt zero M) = true then (M : Term) else _) = M
      rw [if_pos (show ((M : Term).isSC && lt zero M) = true from rfl)]
  | .add a b => by
      rw [if_neg (show ¬ (isFP zero (add a b) = true) from by
        show ¬ (((add a b).isSC && lt zero (add a b)) || false) = true
        rw [show ((add a b).isSC && lt zero (add a b)) = false from by
          rw [show (add a b).isSC = false from rfl]; rfl]
        exact Bool.noConfusion)]
      show (if ((add a b).isSC && lt zero (add a b)) = true then _ else
        phiNFsucc zero (add a b)) = _
      rw [if_neg (by rw [show ((add a b).isSC && lt zero (add a b)) = false from by
          rw [show (add a b).isSC = false from rfl]; rfl]; exact Bool.noConfusion)]
      exact phiNFsucc_zero_eq _
  | .omg a => by
      rw [if_neg (show ¬ (isFP zero (omg a) = true) from by
        show ¬ (((omg a).isSC && lt zero (omg a)) || false) = true
        rw [show ((omg a).isSC && lt zero (omg a)) = false from by
          rw [show (omg a).isSC = false from rfl]; rfl]
        exact Bool.noConfusion)]
      show (if ((omg a).isSC && lt zero (omg a)) = true then _ else
        phiNFsucc zero (omg a)) = _
      rw [if_neg (by rw [show ((omg a).isSC && lt zero (omg a)) = false from by
          rw [show (omg a).isSC = false from rfl]; rfl]; exact Bool.noConfusion)]
      exact phiNFsucc_zero_eq _
  | .psi k a => by
      have hz : lt zero (psi k a) = true :=
        lt_zero_left (by intro hc; exact Term.noConfusion hc)
      rw [if_pos (show isFP zero (psi k a) = true from by
        show (((psi k a).isSC && lt zero (psi k a)) || _) = true
        rw [show (psi k a).isSC = true from rfl, hz]; rfl)]
      show (if ((psi k a).isSC && lt zero (psi k a)) = true then psi k a else _) = _
      rw [if_pos (by rw [show (psi k a).isSC = true from rfl, hz]; rfl)]
  | .Z a => by
      have hz : lt zero (Z a) = true :=
        lt_zero_left (by intro hc; exact Term.noConfusion hc)
      rw [if_pos (show isFP zero (Z a) = true from by
        show (((Z a).isSC && lt zero (Z a)) || _) = true
        rw [show (Z a).isSC = true from rfl, hz]; rfl)]
      show (if ((Z a).isSC && lt zero (Z a)) = true then Z a else _) = _
      rw [if_pos (by rw [show (Z a).isSC = true from rfl, hz]; rfl)]
  | .phi c d => by
      have hfp : isFP zero (phi c d) = lt zero c := by
        show (((phi c d).isSC && lt zero (phi c d)) || lt zero c) = _
        rw [show (phi c d).isSC = false from rfl]; rfl
      show (if ((phi c d).isSC && lt zero (phi c d)) = true then _ else
        (if lt zero c = true then phi c d else phiNFsucc zero (phi c d))) = _
      rw [if_neg (by rw [show (phi c d).isSC = false from rfl]; exact Bool.noConfusion), hfp]
      cases hc : lt zero c with
      | true => rw [if_pos rfl, if_pos rfl]
      | false =>
        rw [if_neg (by exact Bool.noConfusion), if_neg (by exact Bool.noConfusion)]
        exact phiNFsucc_zero_eq _


theorem isFP_zero_notPhi104 {g : Term} (h : ∀ c d, g ≠ phi c d) :
    isFP zero g = (g.isSC && lt zero g) := by
  cases g with
  | phi c d => exact absurd rfl (h c d)
  | _ => show ((_ && _) || false) = _; rw [Bool.or_false]

/-- `dnArg` の枝分けを `isFP` ひとつにまとめたもの。 -/
theorem dnArg_eq104 (x : Term) : dnArg x =
    if (splitFin x).2 ≥ 1 ∧ isFP zero (splitFin x).1 = true
    then plus (splitFin x).1 (ofNat ((splitFin x).2 - 1)) else x := by
  unfold dnArg
  cases hs : splitFin x with
  | mk g m =>
    dsimp only
    by_cases hm : m ≥ 1
    · rw [if_pos hm]
      cases g with
      | phi c d =>
        show (if lt zero c = true then plus (phi c d) (ofNat (m - 1)) else x) = _
        rw [show isFP zero (phi c d) = lt zero c from by
          show (((phi c d).isSC && lt zero (phi c d)) || lt zero c) = _
          rw [show (phi c d).isSC = false from rfl]; rfl]
        cases hc : lt zero c with
        | true => rw [if_pos rfl, if_pos ⟨hm, rfl⟩]
        | false =>
          rw [if_neg (by exact Bool.noConfusion),
            if_neg (by intro hcc; exact Bool.noConfusion hcc.2)]
      | zero =>
        show (if (((zero : Term).isSC && lt zero zero) = true) then _ else x) = _
        rw [isFP_zero_notPhi104 (g := (zero : Term)) (by intro c d hc; exact Term.noConfusion hc),
          show ((zero : Term).isSC && lt zero (zero : Term)) = false from rfl,
          if_neg (by exact Bool.noConfusion), if_neg (by intro hcc; exact Bool.noConfusion hcc.2)]
      | M =>
        show (if (((M : Term).isSC && lt zero M) = true) then plus M (ofNat (m - 1)) else x) = _
        rw [isFP_zero_notPhi104 (g := (M : Term)) (by intro c d hc; exact Term.noConfusion hc),
          show ((M : Term).isSC && lt zero (M : Term)) = true from by
            rw [show (M : Term).isSC = true from rfl, lt_zero_M]; rfl,
          if_pos rfl, if_pos ⟨hm, rfl⟩]
      | add a b =>
        show (if (((add a b).isSC && lt zero (add a b)) = true) then _ else x) = _
        rw [isFP_zero_notPhi104 (g := add a b) (by intro c d hc; exact Term.noConfusion hc),
          show ((add a b).isSC && lt zero (add a b)) = false from by
            rw [show (add a b).isSC = false from rfl]; rfl,
          if_neg (by exact Bool.noConfusion), if_neg (by intro hcc; exact Bool.noConfusion hcc.2)]
      | omg a =>
        show (if (((omg a).isSC && lt zero (omg a)) = true) then _ else x) = _
        rw [isFP_zero_notPhi104 (g := omg a) (by intro c d hc; exact Term.noConfusion hc),
          show ((omg a).isSC && lt zero (omg a)) = false from by
            rw [show (omg a).isSC = false from rfl]; rfl,
          if_neg (by exact Bool.noConfusion), if_neg (by intro hcc; exact Bool.noConfusion hcc.2)]
      | psi k a =>
        show (if (((psi k a).isSC && lt zero (psi k a)) = true) then
          plus (psi k a) (ofNat (m - 1)) else x) = _
        rw [isFP_zero_notPhi104 (g := psi k a) (by intro c d hc; exact Term.noConfusion hc),
          show ((psi k a).isSC && lt zero (psi k a)) = true from by
            rw [show (psi k a).isSC = true from rfl,
              lt_zero_left (show psi k a ≠ zero from by intro hc; exact Term.noConfusion hc)]
            rfl,
          if_pos rfl, if_pos ⟨hm, rfl⟩]
      | Z a =>
        show (if (((Z a).isSC && lt zero (Z a)) = true) then plus (Z a) (ofNat (m - 1)) else x) = _
        rw [isFP_zero_notPhi104 (g := Z a) (by intro c d hc; exact Term.noConfusion hc),
          show ((Z a).isSC && lt zero (Z a)) = true from by
            rw [show (Z a).isSC = true from rfl,
              lt_zero_left (show Z a ≠ zero from by intro hc; exact Term.noConfusion hc)]
            rfl,
          if_pos rfl, if_pos ⟨hm, rfl⟩]
    · rw [if_neg hm, if_neg (by intro hcc; exact hm hcc.1)]


theorem logOm_phi_zero104 (b : Term) :
    logOm (phi zero b) = if isFP zero (splitFin b).1 = true then plus b one else b := by
  show (if phiShifted zero b = true then plus b one else b) = _
  rw [show phiShifted zero b = isFP zero (splitFin b).1 from by
    show (isFP zero (splitFin b).1 || ((b == zero) && (zero : Term).isSC)) = _
    rw [show (zero : Term).isSC = false from rfl, Bool.and_false, Bool.or_false]]

theorem isAP_of_isFP104 : ∀ {g : Term}, isFP zero g = true → g.isAP = true
  | .zero, h => by
      exact absurd h (by
        rw [show isFP zero (zero : Term) = false from rfl]; exact Bool.noConfusion)
  | .add a b, h => by
      exact absurd h (by
        rw [show isFP zero (add a b) = false from by
          show (((add a b).isSC && lt zero (add a b)) || false) = false
          rw [show (add a b).isSC = false from rfl]; rfl]
        exact Bool.noConfusion)
  | .omg _, _ => rfl
  | .M, _ => rfl
  | .psi _ _, _ => rfl
  | .Z _, _ => rfl
  | .phi _ _, _ => rfl

theorem ne_one_of_isFP104 {g : Term} (h : isFP zero g = true) : (g == one) = false := by
  cases hb : (g == one) with
  | false => rfl
  | true =>
    exfalso
    have hg : g = one := eq_of_beq hb
    rw [hg, show isFP zero (one : Term) = false from by
      show (((one : Term).isSC && lt zero one) || lt zero zero) = false
      rw [show (one : Term).isSC = false from rfl]; rfl] at h
    exact Bool.noConfusion h

theorem ne_phi_zero_of_isFP104 {t : Term} (h : isFP zero t = true) : ∀ b, t ≠ phi zero b := by
  intro b hc
  rw [hc, show isFP zero (phi zero b) = false from by
    show (((phi zero b).isSC && lt zero (phi zero b)) || lt zero zero) = false
    rw [show (phi zero b).isSC = false from rfl]; rfl] at h
  exact Bool.noConfusion h

/-- 発火した枝の `logOm` — 数え直しはちょうど元に戻る。 -/
theorem logOm_dn_fire104 {g : Term} (hig : inT g = true) (hfpg : isFP zero g = true) (k : Nat) :
    logOm (phi zero (plus g (ofNat k))) = plus (plus g (ofNat k)) one := by
  rw [logOm_phi_zero104,
    splitFin_ap_ofNat104 hig (isAP_of_isFP104 hfpg) (ne_one_of_isFP104 hfpg) k, if_pos hfpg]

/-- **§100 の `omegaNF_logOm100` の逆。** `logOm ∘ ω^·` は `M` 以下では恒等。 -/
theorem logOm_omegaNF104 {t : Term} (ht : inT t = true) (hM : lt M t = false) :
    logOm (omegaNF t) = t := by
  by_cases hMe : (t == M) = true
  · have he : t = M := eq_of_beq hMe
    rw [he]
    show logOm (if lt M M = true then omg M else if (M == M) = true then M else phiNF zero M) = M
    rw [if_neg (by rw [lt_irrefl]; exact Bool.noConfusion), if_pos (by rfl)]
    rfl
  · rw [omegaNF_of_le_M hM, phiNF_zero_eq104 t]
    cases hfp : isFP zero t with
    | true =>
      rw [if_pos rfl]
      exact logOm_eq_self_of_ne t (ne_phi_zero_of_isFP104 hfp)
    | false =>
      have hrb : plus (splitFin t).1 (ofNat (splitFin t).2) = t := splitFin_rebuild_inT t ht
      have hig : inT (splitFin t).1 = true := inT_splitFin ht
      rw [if_neg (by exact Bool.noConfusion), dnArg_eq104 t]
      by_cases hcond : (splitFin t).2 ≥ 1 ∧ isFP zero (splitFin t).1 = true
      · rw [if_pos hcond, logOm_dn_fire104 hig hcond.2 ((splitFin t).2 - 1),
          plus_assoc_inT _ _ _ hig (inT_ofNat _) inT_one,
          show plus (ofNat ((splitFin t).2 - 1)) one = ofNat (((splitFin t).2 - 1) + 1) from rfl,
          show ((splitFin t).2 - 1) + 1 = (splitFin t).2 from by omega]
        exact hrb
      · have hgfalse : isFP zero (splitFin t).1 = false := by
          by_cases hm1 : (splitFin t).2 ≥ 1
          · cases hg : isFP zero (splitFin t).1 with
            | false => rfl
            | true => exact absurd ⟨hm1, hg⟩ hcond
          · have hz : (splitFin t).2 = 0 := by omega
            have hzz := hrb
            rw [hz] at hzz
            have h1 : (splitFin t).1 = t := hzz
            rw [h1, hfp]
        rw [if_neg hcond, logOm_phi_zero104, hgfalse, if_neg (by exact Bool.noConfusion)]

end

/-! ### §104.2 `ψ₁` の像の指数と係数 — 閉じた形 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- `Ω₁` を頭に足しても `Ω₁` 未満の成分は変わらない。 -/
theorem filter_lt_reg1_plusW104 {X : Term} (hX : inT X = true) :
    (toList (plus (reg 1) X)).filter (fun q => lt q (reg 1))
      = (toList X).filter (fun q => lt q (reg 1)) := by
  cases hl : toList X with
  | nil =>
    rw [show plus (reg 1) X = reg 1 from by
      show (match toList X with
            | [] => reg 1
            | b1 :: _ => ofList ((toList (reg 1)).filter (fun a => le b1 a) ++ toList X)) = _
      rw [hl]]
    rw [show toList (reg 1) = [reg 1] from rfl,
      List.filter_cons_of_neg (by rw [lt_irrefl]; exact Bool.noConfusion)]
  | cons b1 rest =>
    rw [toList_plus_inT inT_W79 hX hl, List.filter_append,
      show ((toList (reg 1)).filter (fun a => le b1 a)).filter (fun q => lt q (reg 1)) = [] from by
        rw [show toList (reg 1) = [reg 1] from rfl]
        cases hc : le b1 (reg 1) with
        | true =>
          rw [List.filter_cons_of_pos (by rw [hc]),
            List.filter_cons_of_neg (by rw [lt_irrefl]; exact Bool.noConfusion)]
          rfl
        | false => rw [List.filter_cons_of_neg (by rw [hc]; exact Bool.noConfusion)]; rfl]
    rw [List.nil_append, hl]

/-- **`ψ₁` の像の `ω` 冪指数 — 門なしの閉じた形。** -/
theorem logOm_dict_D1_104 (Hp : PsiIdxOKStd172) {c : BT} (hb : btLe72 1 c = true)
    (hs : BT.isStd c = true) : logOm (dict (BT.D 1 c)) = plus (reg 1) (dict c) := by
  have hd := inT_dict_of_std172 Hp c hb hs
  have hi : inT (plus (reg 1) (dict c)) = true := inT_plus inT_W79 hd.1
  have hlm : lt (plus (reg 1) (dict c)) M = true := lt_plus_M inT_W79 hd.1 ltM_W79 hd.2
  rw [dict_D1_eq77 Hp c hb hs]
  exact logOm_omegaNF104 hi (lt_asymm_inT hi (show inT (M : Term) = true from rfl) hlm)

/-- **底 `Ω₁` の分解が `ψ₁` の像に付ける係数 — 閉じた形。**  `ω^(lo (dict c))`、
    すなわち `c` の像の `Ω₁` より下の部分の `ω` 冪、それだけ。 -/
theorem wC_dict_D1_104 (Hp : PsiIdxOKStd172) {c : BT} (hb : btLe72 1 c = true)
    (hs : BT.isStd c = true) :
    wC (reg 1) (dict (BT.D 1 c)) = omegaNF (loW89 (dict c)) := by
  show omegaNF (ofList ((toList (logOm (dict (BT.D 1 c)))).filter (fun q => lt q (reg 1)))) = _
  rw [logOm_dict_D1_104 Hp hb hs,
    filter_lt_reg1_plusW104 (inT_dict_of_std172 Hp c hb hs).1]
  rfl

end

/-! ### §104.3 係数の中の `z` は只で名指しできる -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- `G(·,0)` は成分の中へ遺伝する。 -/
theorem sub_GB0_104 : ∀ (a : BT) (u : Nat) (c : BT),
    BT.D u c ∈ BT.toL a → ∀ d ∈ BT.GB 0 c, d ∈ BT.GB 0 a := by
  intro a
  induction a with
  | zero => intro u c h; cases h
  | D v e _ =>
    intro u c h d hd
    have he : BT.D u c = BT.D v e := List.mem_singleton.mp (show BT.D u c ∈ [BT.D v e] from h)
    have hce : c = e := by injection he
    have hgb : BT.GB 0 (BT.D v e) = e :: BT.GB 0 e := by
      show (if 0 ≤ v then e :: BT.GB 0 e else []) = _
      rw [if_pos (Nat.zero_le v)]
    rw [hgb]
    exact List.Mem.tail _ (hce ▸ hd)
  | sum s t ihs iht =>
    intro u c h d hd
    have hgb : BT.GB 0 (BT.sum s t) = BT.GB 0 s ++ BT.GB 0 t := rfl
    rw [hgb]
    rcases List.mem_append.mp (show BT.D u c ∈ BT.toL s ++ BT.toL t from h) with h1 | h1
    · exact List.mem_append.mpr (Or.inl (ihs u c h1 d hd))
    · exact List.mem_append.mpr (Or.inr (iht u c h1 d hd))

/-- **§104 の主定理 (1) — 係数の中の `ψ₀` の引数は名指しできる。橋の全射側は要らない。**

    `hi (dict a)` の各成分は `dict (ψ₁ c)` (§101.1 の只の包含)、その底 `Ω₁` の係数は
    `ω^(lo (dict c))` (§104.2)、そしてその `lo` の各成分は `dict (ψ₀ d)` で
    `d ∈ G(a,0)`、したがって `K` の条件で `d < a`。**使ったのは §101.1 の包含だけで、
    §96 の橋 (全射側) はどこにも現れない。** -/
theorem coefArg104 (Hp : PsiIdxOKStd172) {a : BT} (hb : btLe72 1 (BT.D 0 a) = true)
    (hs : BT.isStd (BT.D 0 a) = true) :
    ∀ p ∈ toList (hiW89 (dict a)), ∃ c : BT,
      BT.lt c a = true ∧ p = dict (BT.D 1 c) ∧
      wC (reg 1) p = omegaNF (loW89 (dict c)) ∧
      ∀ q ∈ toList (loW89 (dict c)), ∃ d : BT, BT.lt d a = true ∧ q = dict (BT.D 0 d) := by
  intro p hp
  have hba := (btLe72_D 1 0 a hb).2
  have hsa := isStd_of_D hs
  obtain ⟨c, hmem, hpe⟩ := mem_toList_hiW_dict101 Hp hba hsa p hp
  have hgood : GoodL77 (BT.toL a) := good_toL77 a hsa hba
  have hb1 : btLe72 1 (BT.D 1 c) = true := hgood.2.2.1 _ hmem
  have hs1 : BT.isStd (BT.D 1 c) = true := hgood.2.1 _ hmem
  have hbc : btLe72 1 c = true := (btLe72_D 1 1 c hb1).2
  have hsc : BT.isStd c = true := isStd_of_D hs1
  refine ⟨c, (std0_split82 hs).2 c (arg_mem_GB0_82 a 1 c hmem), hpe, ?_, ?_⟩
  · rw [hpe]; exact wC_dict_D1_104 Hp hbc hsc
  · intro q hq
    obtain ⟨d, hd, hqe⟩ := mem_toList_loW_dict101 Hp hbc hsc q hq
    exact ⟨d, (std0_split82 hs).2 d
      (sub_GB0_104 a 1 c hmem d (arg_mem_GB0_82 c 0 d hd)), hqe⟩

end

/-! ### §104.4 手 (i) を `BT` の側の述語でやり直す -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 一成分ぶんの係数の引数 — `ψ₁ c` の `c` の段 0 の成分の引数。 -/
def coefArgL104 (p : BT) : List BT :=
  match p with
  | .D 1 c => (BT.toL c).flatMap (fun q => match q with | .D 0 d => [d] | _ => [])
  | _ => []

/-- 係数に現れる `ψ₀` の引数、ぜんぶ。 -/
def coefArgs104 (a : BT) : List BT := (BT.toL a).flatMap coefArgL104

/-- **係数の条件。** `hi (dict a)` の折り畳みが見る係数の `ψ₀` の引数が、みな `a` より下。 -/
def CoefOK104 (a : BT) : Bool := (coefArgs104 a).all (fun d => BT.lt d a)

theorem mem_coefArgs104 {a d : BT} (h : d ∈ coefArgs104 a) :
    ∃ c : BT, BT.D 1 c ∈ BT.toL a ∧ BT.D 0 d ∈ BT.toL c := by
  obtain ⟨p, hp, hd⟩ := List.mem_flatMap.mp h
  cases p with
  | zero => exact absurd hd (by intro hc; cases hc)
  | sum s t => exact absurd hd (by intro hc; cases hc)
  | D u c =>
    cases u with
    | zero => exact absurd hd (by intro hc; cases hc)
    | succ u' =>
      cases u' with
      | succ _ => exact absurd hd (by intro hc; cases hc)
      | zero =>
        obtain ⟨q, hq, hdq⟩ := List.mem_flatMap.mp
          (show d ∈ (BT.toL c).flatMap (fun q => match q with | .D 0 d => [d] | _ => [])
            from hd)
        cases q with
        | zero => exact absurd hdq (by intro hc; cases hc)
        | sum _ _ => exact absurd hdq (by intro hc; cases hc)
        | D v e =>
          cases v with
          | succ _ => exact absurd hdq (by intro hc; cases hc)
          | zero =>
            have : d = e := List.mem_singleton.mp (show d ∈ [e] from hdq)
            exact ⟨c, hp, this ▸ hq⟩

/-- **係数の条件は `K` の条件の帰結。** §101.1 の包含と §82 の `G(·,0)` だけで出る。 -/
theorem coefOK104_of_std {a : BT} (hs : BT.isStd (BT.D 0 a) = true) :
    CoefOK104 a = true := by
  refine List.all_eq_true.mpr ?_
  intro d hd
  obtain ⟨c, hc, hdc⟩ := mem_coefArgs104 hd
  exact (std0_split82 hs).2 d (sub_GB0_104 a 1 c hc d (arg_mem_GB0_82 c 0 d hdc))

/-- **`HiMono89` の `K` の条件を係数の条件に取り替えた条項。**  §101.3 の `HiMonoP101`
    と同じ形だが、述語は 𝔗(M) の項の関数ではなく `BT` の項の関数である — §101 が
    「係数の中の `z` は 𝔗(M) の側から名指しできない」と言ったのはそこで、
    `BT` の側からは §104.3 のとおり**只で**名指しできる。 -/
def HiMonoCoef104 : Prop :=
  ∀ (a b : BT), btLe72 1 a = true → btLe72 1 b = true →
    BT.isStd a = true → BT.isStd b = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    CoefOK104 a = true →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true

/-- **手 (i) の形、`BT` の側で。** -/
theorem hiMono_of_coef104 (H : HiMonoCoef104) : HiMono89 := by
  intro a b hbA hbB hsA hsB hWa hWb hlt
  exact H a b (btLe72_D 1 0 a hbA).2 (btLe72_D 1 0 b hbB).2 (isStd_of_D hsA) (isStd_of_D hsB)
    hWa hWb (coefOK104_of_std hsA) hlt

/-- **326 行目を係数の条項に架け替える。** -/
theorem certIn_t326_coef104 (Hp : PsiIdxOKStd172) (H : HiMonoCoef104)
    (H1 : DictOntoMidOpen103) (H3 : DictDenseMid102) (H4 : DictDenseAbove102)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_103 Hp (hiMono_of_coef104 H) H1 H3 H4 hacc

end

/-! ### §104.5 否定 — 係数の条件は飾りではなく、`K` の条件より真に弱い -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- **否定 1 — 係数の条件を外すと条項は偽。**  §101.4 の組んだ対がそのまま効く。 -/
theorem not_hiMonoCoefFree104 :
    ¬ (∀ (a b : BT), btLe72 1 a = true → btLe72 1 b = true →
        BT.isStd a = true → BT.isStd b = true →
        le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
        lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
        lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true) := by
  intro H
  have h := H bothBadA101 bothBadB101
    (show btLe72 1 bothBadA101 = true from rfl) (show btLe72 1 bothBadB101 = true from rfl)
    (show BT.isStd bothBadA101 = true from rfl) (show BT.isStd bothBadB101 = true from rfl)
    (show le (reg 1) (dict bothBadA101) = true from rfl)
    (show le (reg 1) (dict bothBadB101) = true from rfl)
    (show lt (hiW89 (dict bothBadA101)) (hiW89 (dict bothBadB101)) = true from rfl)
  rw [show lt (collapse 0 (hiW89 (dict bothBadA101)))
        (collapse 0 (hiW89 (dict bothBadB101))) = false from rfl] at h
  exact Bool.noConfusion h

/-- **否定 2 — §101 の二つの反例は、どちらも係数の条件が落とす。**  §101.4 の
    `bothBadA101` でも §101.2 の `scBadA101` でも `CoefOK104` は偽、一方 §101 の
    候補の述語 `foldNF101`・`ksetOK101` はそこで真。**§101 の否定は §104.4 の条項に
    届かない** — それが `HiMonoCoef104` を立てる理由である。 -/
theorem coefOK_kills101_104 :
    (foldNF101 (hiW89 (dict bothBadA101)), ksetOK101 (hiW89 (dict bothBadA101)),
     CoefOK104 bothBadA101, CoefOK104 bothBadB101,
     CoefOK104 scBadA101, CoefOK104 scBadB101)
    = (true, true, false, true, false, true) := rfl

/-- 分離の証人 — `ψ₁ψ₀Ω₁ ⊕ ψ₀ψ₁ψ₁Ω₁`、10 記号。組んだもので、掃いて出したのではない。 -/
def sepA104 : BT :=
  BT.sum (BT.D 1 (BT.D 0 (BT.D 1 BT.zero))) (BT.D 0 (BT.D 1 (BT.D 1 (BT.D 1 BT.zero))))

/-- **否定 3 — 段の正直さ。**  `CoefOK104` は `K` の条件より**真に弱い**: この項は
    形の条件をすべて満たし `CoefOK104` は真、`BT.isStd (ψ₀ ·)` は偽。したがって
    `HiMonoCoef104` は `HiMono89` より**真に強い主張**であって、§104 は残余を
    取り除いたのではなく**動かした**。落ちているのは `hi` が捨てる段 0 の成分の
    引数で、`ψ₁ψ₁ψ₁0` が項全体を追い越している。 -/
theorem sepA104_facts :
    (btLe72 1 sepA104, BT.isStd sepA104, le (reg 1) (dict sepA104),
     CoefOK104 sepA104, BT.isStd (BT.D 0 sepA104), BT.size sepA104)
    = (true, true, true, true, false, 10) := rfl

end

/-! ### §104.6 測定 (凍結)

**構成 — 係数が悪さをするように組み、濾さない。**  §97・§99・§101 の作り方に倣う。

    seed104    段 1 の主要項 5 個 — 深さ (`ψ₁0` 〜 `ψ₁ψ₁ψ₁0`) と幅 (`ψ₁(Ω₁⊕Ω₁)` など)
    inner104   その降べき 2 項和も入れた 20 個 — `ψ₀` の引数になる線
    cap104     `ψ₁ψ₀ z` の形 20 個 — **係数を運ぶ帽子**
    pre104     前置き 0〜2 成分 11 通り
    cand104    220 項  濾さない

第一の母集団は `CoefOK104` と `K` の条件を**見分けられない** (30 項で一致)。それは
§96 の盲点そのものなので、**差を作るために第二の族を組む**:

    fam1_104   `hi` が捨てる段 0 の成分 `ψ₀ z` で `K` を壊す (`z` が項を追い越す)
    fam2_104   係数の中の係数 (深さ 2) で壊す
    sep104     567 項、そこから 8 個に 1 つ間引いて 71 項 — うち **21 項が分離する**
-/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

private def dedup104 (l : List BT) : List BT :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []
private def every104 (k : Nat) (l : List BT) : List BT :=
  (l.zipIdx.filter (fun p => p.2 % k == 0)).map (·.1)

private def seed104 : List BT :=
  [BT.D 1 BT.zero,
   BT.D 1 (BT.D 1 BT.zero),
   BT.D 1 (BT.D 1 (BT.D 1 BT.zero)),
   BT.D 1 (BT.sum (BT.D 1 BT.zero) (BT.D 1 BT.zero)),
   BT.D 1 (BT.sum (BT.D 1 (BT.D 1 BT.zero)) (BT.D 1 BT.zero))]
private def inner104 : List BT :=
  dedup104 (seed104 ++
    seed104.flatMap (fun a => (seed104.filter (fun b => BT.le b a)).map (BT.sum a)))
private def cap104 : List BT := inner104.map (fun z => BT.D 1 (BT.D 0 z))
private def pre104 : List (List BT) :=
  [[]] ++ seed104.map (fun p => [p]) ++ seed104.map (fun p => [p, p])
private def cand104 : List BT :=
  dedup104 (pre104.flatMap (fun l => cap104.map (fun w => BT.ofL (l ++ [w]))))

private def kstd104 (a : BT) : Bool := btLe72 1 a && BT.isStd a && BT.isStd (BT.D 0 a)
private def shape104 (a : BT) : Bool := btLe72 1 a && BT.isStd a && le (reg 1) (dict a)
private def samp104 : List BT := cand104.filter shape104
private def thin104 : List BT := every104 3 samp104

/-- 𝔗(M) の側からしか見えない係数の読み — §101 の手 (i) が言えるのはこれだけ。 -/
private def coefsOf104 (a : BT) : List Term :=
  (toList (hiW89 (dict a))).flatMap
    (fun p => (toList (logOm p)).filter (fun q => lt q (reg 1)))
private def coefLt104 (a b : BT) : Bool :=
  (coefsOf104 a).all (fun q => lt q (collapse 0 (hiW89 (dict b))))

private def pairs104 (l : List BT) : List (BT × BT) :=
  l.flatMap (fun a => l.map (fun b => (a, b)))
private def resid104 (l : List BT) : List (BT × BT) :=
  (pairs104 l).filter (fun p => lt (hiW89 (dict p.1)) (hiW89 (dict p.2)))
private def bad104 (l : List BT) : List (BT × BT) :=
  (resid104 l).filter (fun p =>
    !(lt (collapse 0 (hiW89 (dict p.1))) (collapse 0 (hiW89 (dict p.2)))))

private def big104 : List BT :=
  [BT.D 1 (BT.D 1 (BT.D 1 BT.zero)),
   BT.D 1 (BT.sum (BT.D 1 (BT.D 1 BT.zero)) (BT.D 1 BT.zero)),
   BT.D 1 (BT.D 1 (BT.D 1 (BT.D 1 BT.zero)))]
private def fam1_104 : List BT :=
  dedup104 (pre104.flatMap (fun l =>
    big104.flatMap (fun z => cap104.map (fun w => BT.ofL (l ++ [w, BT.D 0 z])))))
private def fam2_104 : List BT :=
  dedup104 (pre104.flatMap (fun l =>
    big104.flatMap (fun z => seed104.map (fun s =>
      BT.ofL (l ++ [BT.D 1 (BT.D 0 (BT.sum s (BT.D 1 (BT.D 0 z))))])))))
private def sep104 : List BT := (fam1_104 ++ fam2_104).filter shape104
private def thinS104 : List BT := every104 8 sep104

/-! 母集団の形。 -/
#guard (seed104.length, inner104.length, cap104.length, pre104.length, cand104.length)
        == (5, 20, 20, 11, 220)

/-! **受領 1 — 仮説は見えている、そして §104.4 の定理はそのとおり。**  220 項のうち
    `CoefOK104` が落ちるのは 128、`K` 標準は 88、**`K` 標準で `CoefOK104` が落ちるのは
    ゼロ** (`coefOK104_of_std`)。 -/
#guard (cand104.countP kstd104, cand104.countP (fun a => !(CoefOK104 a)),
        cand104.countP (fun a => kstd104 a && !(CoefOK104 a))) == (88, 128, 0)

/-! **受領 2 — 第一の母集団は盲目である。**  60 項の標本で `CoefOK104` と `K` の条件は
    同じ 30 項で成り立ち、同じ 643 対を残し、同じ 0 の破れを出す。**この掃き出しは
    証拠ではない** (§96 の盲点)。だから第二の族を組む。 -/
#guard (samp104.length, thin104.length, thin104.countP CoefOK104, thin104.countP kstd104)
        == (180, 60, 30, 30)
#guard ((resid104 thin104).length, (bad104 thin104).length,
        (resid104 thin104).countP (fun p => CoefOK104 p.1),
        (bad104 thin104).countP (fun p => CoefOK104 p.1),
        (resid104 thin104).countP (fun p => kstd104 p.1),
        (bad104 thin104).countP (fun p => kstd104 p.1)) == (1770, 427, 643, 0, 643, 0)

/-! **受領 3 — 𝔗(M) の側から読んだ係数の条件では足りない。**  `coefLt104` は
    「`a` の指数の低い成分がすべて `ψ₀(hi (dict b))` より下」— 手 (i) の述語が言える
    範囲そのもの — で、1370 対のうち **27 が破れる**。 -/
#guard ((resid104 thin104).countP (fun p => coefLt104 p.1 p.2),
        (bad104 thin104).countP (fun p => coefLt104 p.1 p.2)) == (1370, 27)

/-! **受領 4 — 分離する族。**  71 項のうち **21 項が `CoefOK104` を満たして `K` の条件を
    満たさない**。2462 の残余対に 677 の破れがあり、左の項の `CoefOK104` だけで濾すと
    **887 対・破れ 0**、`K` の条件で濾すと 184 対・破れ 0。**弱いほうの仮説が 4.8 倍の
    対で結論を運ぶ。** -/
#guard (fam1_104.length, fam2_104.length, sep104.length, thinS104.length,
        thinS104.countP CoefOK104, thinS104.countP kstd104,
        thinS104.countP (fun a => CoefOK104 a && !(kstd104 a)))
        == (660, 165, 567, 71, 35, 14, 21)
#guard ((resid104 thinS104).length, (bad104 thinS104).length,
        (resid104 thinS104).countP (fun p => CoefOK104 p.1),
        (bad104 thinS104).countP (fun p => CoefOK104 p.1),
        (resid104 thinS104).countP (fun p => kstd104 p.1),
        (bad104 thinS104).countP (fun p => kstd104 p.1)) == (2462, 677, 887, 0, 184, 0)

/-! **受領 5 — 𝔗(M) の側の読みは第二の母集団でも足りない。** 1856 対に 71 の破れ。 -/
#guard ((resid104 thinS104).countP (fun p => coefLt104 p.1 p.2),
        (bad104 thinS104).countP (fun p => coefLt104 p.1 p.2)) == (1856, 71)

/-! **受領 6 — 分離の証人は母集団の中にいる。** -/
#guard sep104.contains sepA104

/-! **受領 7 — 幅。**  帽子を**二つ**載せた第三の母集団 (`wide104`、1890 項、20 個に 1 つ
    間引いて 95 項) は、係数の引数を 2 個持ち、底 `Ω₁` の対も 2 個持つ — 対が**併合**され、
    係数が `plus` の和になる場合をここで踏む。4465 の残余対に 1384 の破れ、
    `CoefOK104` で濾すと **604 対・破れ 0**、𝔗(M) の側の読みでは 3346 対に **265 の破れ**。
    この族は `CoefOK104` と `K` の条件を見分けない (どちらも 28 項) ので、分離の証拠は
    受領 4 のほうにある。 -/
private def wideRaw104 : List BT :=
  dedup104 (pre104.flatMap (fun l =>
    cap104.flatMap (fun w1 => (cap104.filter (fun w2 => BT.le w2 w1)).map
      (fun w2 => BT.ofL (l ++ [w1, w2])))))
private def wide104 : List BT := wideRaw104.filter shape104
private def thinW104 : List BT := every104 20 wide104

#guard (wideRaw104.length, wide104.length, thinW104.length,
        thinW104.countP CoefOK104, thinW104.countP kstd104,
        (thinW104.map (fun a => (coefArgs104 a).length)).foldl
          (fun m n => if n > m then n else m) 0,
        (thinW104.map (fun a => ((wcnf (reg 1) (toList (hiW89 (dict a)))).1).length)).foldl
          (fun m n => if n > m then n else m) 0)
        == (2310, 1890, 95, 28, 28, 2, 2)
#guard ((resid104 thinW104).length, (bad104 thinW104).length,
        (resid104 thinW104).countP (fun p => CoefOK104 p.1),
        (bad104 thinW104).countP (fun p => CoefOK104 p.1),
        (resid104 thinW104).countP (fun p => coefLt104 p.1 p.2),
        (bad104 thinW104).countP (fun p => coefLt104 p.1 p.2))
        == (4465, 1384, 604, 0, 3346, 265)

/-! **受領 8 — 係数は空ではない。**  三つの母集団のどの項にも係数の引数が少なくとも
    一つある (`coefArgs104` が空の項は 0 個) ので、`CoefOK104` はどこでも空虚ではない。 -/
#guard (cand104.countP (fun a => (coefArgs104 a).isEmpty),
        sep104.countP (fun a => (coefArgs104 a).isEmpty),
        wide104.countP (fun a => (coefArgs104 a).isEmpty)) == (0, 0, 0)

end

/-! ## §105 THE STEP THAT SUBTRACTS FROM `Ω₁` DOMINATES `Ω₁^(aV ⊖ Ω₁)` — AND THE SURVIVOR
       §100 COULD NOT EXHIBIT

§100 closed the whole low half of the `K`-gate (`lt_idxOf_of_lt_reg100`: every element of
`K_{Ω₁}(aV) ∪ K_{Ω₁}(cV)` BELOW `Ω₁` is below the index, at every firing step, no side
condition) and then recorded an honest limit: `IdxK100` — the clause for elements AT or ABOVE
`Ω₁` — could not be shown non-vacuous, because on its 250-term corpus every such obligation was
already taken by §92.1, §92.2 or §95.  §100's own hint was that the only way it found to produce
one is a `ψ₀`-argument whose collapse index reaches `Ω₁`, "which `BT.isStd` rejects".

**THAT HINT IS FALSE, AND §105 PROVES IT FALSE.**  `ehi100 0 = ψ₁(ψ₁ψ₁0 ⊕ ψ₁0)` is standard as
a `ψ₀`-argument (`BT.isStd (ψ₀ ·) = true`), is at level `≤ 1`, and its collapse index is `Ω₁`
exactly (`notLowIdx105`).  So the clause "standardness forces the `ψ₀`-argument's collapse index
below `Ω₁`" — the theorem that would have closed the `Ω₁ ≤ y` half outright — **is refuted.**
What `BT.isStd` rejects is not the argument; it is the SLOT §100 tried to put it in.

**AND THE SURVIVOR EXISTS.**  Move the same argument one `Ω₁`-power up — put it behind TWO
copies of `ψ₁ψ₁0` instead of one, so the step's base-`Ω₁` exponent is `aV = Ω₁·2` rather than
`Ω₁` exactly — and the term becomes standard while §92.1's previous index stays absent (the step
is the first firing one) and §92.2's road stays shut (a Veblen tail makes `lastFire92` false):

    `survA105 = ψ₁(ψ₁ψ₁0 ⊕ ψ₁ψ₁0 ⊕ ψ₀ψ₁(ψ₁ψ₁0 ⊕ ψ₁0)) ⊕ ψ₁ψ₁0`            (21 symbols)

satisfies every hypothesis, the gate holds on it, and it carries **one obligation that survives
§92.1, §92.2, all three of §95's exemptions AND §100's `y < Ω₁`** — with `y = Ω₁` exactly.
`IdxK100` is not vacuous, and the measurement now exhibits it (`survAB105_counts`).

**THE ARITHMETIC THAT KILLS IT IS ONE STRICT INEQUALITY.**  §80.1 and §86.3 got `Ω₁ ≤ Δ` at
every step with `aV ⊖ Ω₁ ≠ 0` (`le_reg_powOf80`, `le_powOf_ddOf80`) and stopped, because
`y < Ω₁` never needed more.  At `y = Ω₁` the non-strict bound is worth nothing.  §105 proves the
strict one, and the equality case is exactly where there is no obligation to prove:

    **`mulL_gt105` : `z ≠ 0`, `z ≠ 1` ⟹ `ω^e < e·z`** — two components put the head strictly
    below the sum; one component puts `logOm q ≠ 0` (because `logOm q = 0` forces `q = 1`) into
    a strictly monotone `ω^(e ⊕ ·)` (`plus_smono_right_inT79`, `lt_omegaNF_inT79`);

    **`lt_reg_ddOf105` : `aV ⊖ Ω₁ ≠ 0` and `K_{Ω₁} aV ∪ K_{Ω₁} cV ≠ ∅` ⟹ `Ω₁ < Δ`.**  The two
    ways `Δ` can BE `Ω₁` are `cV = 1` and `aV ⊖ Ω₁ = 1`, and both of them empty the two `K`-sets
    (`kset_nil_of_subAP_one105` : `aV = Ω₁ ⊕ 1` has `K_{Ω₁} aV = ∅`; `K_{Ω₁} 1 = ∅`).  The
    hypothesis that there is an obligation at all is what makes the inequality strict.

    **`lt_idxOf_of_le_reg105` : at a firing step with `aV ⊖ Ω₁ ≠ 0`, every `K`-element `y ≤ Ω₁`
    is below the index.**  §100.2 read `y < Ω₁`; this reads `y ≤ Ω₁`.

**AND THE SAME `mulL_gt105` REACHES MUCH FURTHER THAN `Ω₁`.**  The bound `Ω₁ ≤ Δ` came from
`Ω₁ ≤ Ω₁^(aV ⊖ Ω₁) ≤ Δ`, and only the first `≤` was ever used.  Reading the second one strictly
gives a second, sharper exemption that does not look at `Ω₁` at all:

    **`lt_idxOf_of_powFree105` : `aV ⊖ Ω₁ ≠ 0` and `y ≤ Ω₁^(aV ⊖ Ω₁)` ⟹ `y` is below the
    index** — with equality allowed whenever `cV ≠ 1`, which is the case that matters.
    `powFree105` is its decidable form.

That takes the second witness too:

    `survB105 = ψ₁(ψ₁ψ₁0 ⊕ ψ₁ψ₁0 ⊕ ψ₀ψ₁(ψ₁ψ₁0 ⊕ ψ₁ψ₁0)) ⊕ ψ₁ψ₁0`         (22 symbols)

whose obligation has `y = ω^(Ω₁²) = Ω₁^(aV ⊖ Ω₁)` EXACTLY — above `Ω₁`, so the first theorem
cannot see it, and on the nose, so the `le` in `powFree105` is not decoration.

WHAT IS PROVED, UNCONDITIONALLY.

  §105.1  `logOm_one105`, `mulL_one105` (`e·1 = ω^e`), `ofList_append_one_ne_zero105`,
          `plus_one_ne_zero105`, `eq_one_of_logOm_zero105` (§78's private lemma, re-proved where
          it can be used), `mulL_gt105`, `kset_nil_of_subAP_one105`, `lt_reg_ddOf105`,
          `lt_idxOf_of_le_reg105`, `powFree105` and `lt_idxOf_of_powFree105`.

  §105.2  `IdxK105` is `IdxK100` with TWO hypotheses added — `le y Ω₁ = false ∨ aV ⊖ Ω₁ = 0`,
          and `powFree105 p y = false` — so the clause is a SUBSET of §100's
          (`idxK105_of_idxK100`) and §105 demonstrably adds no obligation.
          `gateStd87_of_idxK105` consumes it at one term, `idxStd105_of_step073` is the converse
          (so `IdxStd105` is still EXACTLY the gate), and `psiIdxStep073_of_idxStd105` /
          `certIn_t326_idx105` re-hang row 326 — still on `DictLtStd92`, `HiMono89` and
          `LeIdxSelf95`, and now on `IdxStd105`.

WHAT IS **NOT** CLAIMED.  The gate is NOT closed.  `IdxStd105` is EQUIVALENT to
`PsiIdxStep073`, as `IdxStd100`, `IdxStd95`, `IdxStd92` and `IdxStd90` were.  `LeIdxSelf95`,
`HiMono89` and `DictLtStd92` are untouched and still unproved — §105 did NOT attempt
`LeIdxSelf95`, and the two pieces §100 named for it (a `wcnf` RECONSTRUCTION lemma and `mulL`'s
distributivity over `⊕`) are still absent; `mulL_gt105` is neither of them.  §105 does not touch
`LocalK2Snd_78` in full.  `IdxLtStd92`, `SplitK86`, `ArgStd87`, `CofDenseS1`, `BCofIn71` are
untouched.  §86's wall stands: both new theorems compare `y` against `Ω₁^(aV ⊖ Ω₁)`, never
against `i₀` alone or `Δ` alone, and both name the step.

**§105 MOVED THE RESIDUE; IT DID NOT REMOVE IT** — and unlike §100 the new residue is BUILT, so
the next section starts from a witness and not from a limit of measurement:

    `survC105 = ψ₁(ψ₁ψ₁0 ⊕ ψ₁ψ₁0 ⊕ ψ₀ψ₁(ψ₁ψ₁0 ⊕ ψ₁ψ₁0 ⊕ ψ₀0)) ⊕ ψ₁ψ₁0`   (25 symbols)

is standard, the gate holds on it, and its one obligation survives §92.1, §92.2, §95, §100 AND
both of §105's exemptions.  **The residual shape is now sharp, and it is a COEFFICIENT
comparison:** at the surviving steps `aV ⊖ Ω₁ ≠ 0`, the step builds `Δ = Ω₁^(aV ⊖ Ω₁)·cV`, and
the escaping element is `y ≤ j = Ω₁^(aV ⊖ Ω₁)·c` for the SAME power — the inner `ψ₀`-argument's
own collapse index — with `1 < c`.  So `y < Δ` reduces to `c < cV`.  At `survC105` that reads
`ω < ψ_{Ω₁}(j)`, and the reason it holds is that `BT.isStd` forces the `ψ₀`-component to sit
strictly after the `Ω₁`-part of the outer argument, which puts `ψ_{Ω₁}(j)` — a strongly critical
ordinal — into `cV`.  Nesting the slot one level deeper is exactly how `survC105` was built, and
it is what a `c < cV` clause will have to survive.

WHAT THE MEASUREMENT SAYS (§105.3 and §105.4 give the constructions).  §100's `corpus100` — all
250 terms — reused verbatim, plus **60 qualifying terms of 72 built for §105**.  310 terms.

  * **§100's clause is not vacuous.**  Over the 310 terms: 271 obligations under §90's clause,
    87 under §92's, 64 under §95's, **8 under §100's, 4 under §105's.**  All 8 are on the new
    terms — `corpus100` alone still gives 0, which is exactly §100's limit — and of the 8, 2 have
    `y ≤ Ω₁` (the first new theorem) and 4 more are `powFree105` (the second).
  * **The population is built, not swept.**  `slot105 n E` puts a `ψ₀`-argument `E` behind `n+1`
    copies of `ψ₁ψ₁0`, so the step's exponent is `aV = Ω₁·(n+1)` and `aV ⊖ Ω₁ = Ω₁·n`.  `n = 0`
    IS §100's `slotHi100` (`slot105 0 (ehi100 k) = slotHi100 k`, frozen), `n = 1` is where the
    survivors live, and `n = 2` is standard too but there §95's `freeSelf95` already takes the
    obligation — by then the step's index has outgrown `dict e`.  `E` ranges over five arguments
    whose collapse index is NOT below `Ω₁` — `ehi100 0` gives `Ω₁`, `ehi100 1` and `eHi2_105`
    give `Ω₁^{Ω₁}`, and `eNest105 z` (the slot itself, one level down) gives `Ω₁^{Ω₁}·c` with
    `c > 1` — and two controls whose index is below (`argB95 2`, `twr86 3`).
  * **The negatives.**  12 of the 72 fail `okHyp84`, and every one of them is an `n = 0` term
    over one of the five high arguments, in the three variants that do NOT put a tower in front
    (§100's `slotOK100` trick makes the fourth standard again — at the cost of §92.1 taking the
    obligation, which is precisely why §100 could not exhibit a survivor).  At `aV = Ω₁` the gate
    genuinely FAILS (`slotHi0_not_std105`), and the only thing keeping those terms out is
    `BT.isStd`.  That is why `IdxK105` keeps `aV ⊖ Ω₁ = 0` in its second disjunct rather than
    proving it away.
  * **The wide check (§105.4).**  Every descending arrangement of one, two or three `Ω₁`-towers
    in front of the `ψ₀`-slot, over ten arguments and four tails: **3360 terms built, 924
    qualifying, 0 gate failures**, 695 → 386 → 28 → 22 → **6** obligations.  All 6 survivors have
    `aV ⊖ Ω₁ = Ω₁` and `Ω₁^{Ω₁} < y`, with only three distinct values of `y` — the shape is one,
    not a family.  **And 213 of the built terms have `inT (dict ·)` and FAIL the gate**; every one
    of them is outside the population by `BT.isStd` alone.  §100 saw that with one term; here it
    is 213.  No clause blind to `BT.isStd` can close the `Ω₁ ≤ y` side.
  * **The gate does not fail anywhere in either population.**  `stepOKb`, `idxb84`, `splitb86`,
    `idxLt90b`, `ltArg90b` : 0 failures on all 60 and all 924.  §105 is not a refutation.
-/

/-! ### §105.1 `Ω₁` を引く歩は `Ω₁` を真に超える -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

theorem logOm_one105 : logOm TM.Term.one = zero := by rfl

theorem toList_one105 : toList TM.Term.one = [TM.Term.one] := by rfl

theorem mulL_one105 (e : Term) : mulL e TM.Term.one = omegaNF e := by
  show ofList ((toList TM.Term.one).map (fun p => omegaNF (plus e (logOm p)))) = _
  rw [toList_one105, List.map_cons, logOm_one105,
    plus_nil (show toList (zero : Term) = [] from rfl)]
  rfl

theorem ofList_append_one_ne_zero105 : ∀ (l : List Term),
    ofList (l ++ [TM.Term.one]) ≠ zero
  | [] => by intro h; exact Term.noConfusion h
  | [_] => by intro h; exact Term.noConfusion h
  | _ :: _ :: _ => by intro h; exact Term.noConfusion h

theorem plus_one_ne_zero105 (b : Term) : plus b TM.Term.one ≠ zero := by
  show (match toList TM.Term.one with
        | [] => b
        | b1 :: _ => ofList ((toList b).filter (fun a => le b1 a) ++ toList TM.Term.one))
      ≠ zero
  rw [toList_one105]
  exact ofList_append_one_ne_zero105 _

/-- `logOm q = 0` になる加法主要項は `1` だけ (§78 の private 版の再掲)。 -/
theorem eq_one_of_logOm_zero105 {q : Term} (hap : q.isAP = true) (h : logOm q = zero) :
    q = TM.Term.one := by
  by_cases hz : ∃ b, q = phi zero b
  · obtain ⟨b, hb⟩ := hz
    rw [hb] at h ⊢
    by_cases hs : phiShifted zero b = true
    · exfalso
      rw [show logOm (phi zero b) = (if phiShifted zero b then plus b TM.Term.one else b)
            from rfl, if_pos hs] at h
      exact plus_one_ne_zero105 b h
    · rw [show logOm (phi zero b) = (if phiShifted zero b then plus b TM.Term.one else b)
            from rfl, if_neg hs] at h
      rw [h]; rfl
  · rw [logOm_eq_self_of_ne q (fun b hc => hz ⟨b, hc⟩)] at h
    rw [h] at hap
    exact Bool.noConfusion hap

/-- **§105.1 の主定理 — 係数が `1` でなければ乗算は真に伸びる。**
    `ω^e ≤ e·z` (§80.1) の狭義版。成分が二つ以上なら頭より上、一つなら
    その指数が `0` でない (`logOm q = 0` は `q = 1` のときだけ) から。 -/
theorem mulL_gt105 {e z : Term} (he : inT e = true) (hz : inT z = true)
    (hz0 : z ≠ zero) (hz1 : z ≠ TM.Term.one) :
    lt (omegaNF e) (mulL e z) = true := by
  have hmulT : inT (mulL e z) = true := inT_mulL mulDescInT he hz
  cases hL : toList z with
  | nil => exact absurd (toList_eq_nil z hL) hz0
  | cons q rest =>
    have hqm : q ∈ toList z := by rw [hL]; exact List.Mem.head _
    have hq : inT q = true := inTL_inT hz q hqm
    have hqa : q.isAP = true := inTL_isAP hz q hqm
    have hmul : mulL e z
        = ofList ((q :: rest).map (fun p => omegaNF (plus e (logOm p)))) := by
      show ofList ((toList z).map _) = _
      rw [hL]
    cases rest with
    | nil =>
      have hzq : z = q := by
        rw [← inT_ofList_toList z hz, hL]; rfl
      have hqne : q ≠ TM.Term.one := by rw [← hzq]; exact hz1
      have hlog : logOm q ≠ zero := fun hc => hqne (eq_one_of_logOm_zero105 hqa hc)
      have h1 : lt e (plus e (logOm q)) = true := by
        have h2 := plus_smono_right_inT79 e he zero (logOm q) inT_zero (inT_logOm hq)
          (lt_zero_left hlog)
        rwa [plus_nil (show toList (zero : Term) = [] from rfl)] at h2
      rw [hmul, List.map_cons, List.map_nil]
      exact lt_omegaNF_inT79 he (inT_plus he (inT_logOm hq)) h1
    | cons q2 t =>
      have hle : le (omegaNF e) (omegaNF (plus e (logOm q))) = true := by
        refine omegaNF_mono_inT he (inT_plus he (inT_logOm hq)) ?_
        have h2 := plus_mono_right_inT e he zero (logOm q) inT_zero (inT_logOm hq)
          (le_zero_left _)
        rwa [plus_nil (show toList (zero : Term) = [] from rfl)] at h2
      have hlt : lt (omegaNF (plus e (logOm q)))
          (ofList (omegaNF (plus e (logOm q))
            :: ((q2 :: t).map (fun p => omegaNF (plus e (logOm p)))))) = true := by
        rw [List.map_cons]
        exact lt_head_add (isAP_omegaNF _) _
      have hmulT2 : inT (ofList (omegaNF (plus e (logOm q))
          :: ((q2 :: t).map (fun p => omegaNF (plus e (logOm p)))))) = true := by
        rw [hmul, List.map_cons] at hmulT
        exact hmulT
      rw [hmul, List.map_cons]
      exact lt_of_le_of_lt3 (inT_le_fragR _ (inT_omegaNF he))
        (inT_le_fragR _ (inT_omegaNF (inT_plus he (inT_logOm hq))))
        (inT_le_fragR _ hmulT2) hle hlt

/-- `subAP Ω₁ h = 1` なら `K_{Ω₁} h` は空 — `h` は `1` か `Ω₁ ⊕ 1` そのもの。
    §100.2 の `kset_nil_of_subAP_zero100` の隣。 -/
theorem kset_nil_of_subAP_one105 {h : Term} (hh : inT h = true)
    (hs : subAP (reg 1) h = TM.Term.one) {y : Term} (hy : y ∈ Kset (reg 1) h) : False := by
  cases hl : toList h with
  | nil => rw [toList_eq_nil h hl] at hy; cases hy
  | cons p rest =>
    have h1 : (if p == reg 1 then ofList rest else h) = TM.Term.one := by
      rw [show subAP (reg 1) h = (match toList h with
            | [] => zero
            | q :: r => if q == reg 1 then ofList r else h) from rfl, hl] at hs
      exact hs
    by_cases hp : (p == reg 1) = true
    · rw [if_pos hp] at h1
      have hr : rest = [TM.Term.one] := by
        cases rest with
        | nil => exact Term.noConfusion h1
        | cons a t =>
          cases t with
          | nil => rw [show ofList [a] = a from rfl] at h1; rw [h1]
          | cons _ _ => exact Term.noConfusion h1
      have hhe : h = add (reg 1) TM.Term.one := by
        rw [← inT_ofList_toList h hh, hl, hr, eq_of_beq hp]; rfl
      rw [hhe, show Kset (reg 1) (add (reg 1) TM.Term.one) = [] from rfl] at hy
      cases hy
    · rw [if_neg hp] at h1
      rw [h1, kset_one100] at hy
      cases hy

/-- **§105.1 の結論 — `aV ⊖ Ω₁ ≠ 0` の歩で `K` が空でなければ `Ω₁ < Δ`。**
    §80.1/§86.3 は `Ω₁ ≤ Δ` までしか届かなかった。等号が起こるのは
    `aV = Ω₁ ⊕ 1` かつ `cV = 1` の歩だけで、そこでは `K_{Ω₁} aV` も `K_{Ω₁} cV` も空である。 -/
theorem lt_reg_ddOf105 {ac : Term × Term} (h1 : inT ac.1 = true) (h3 : inT ac.2 = true)
    (hz : ac.2 ≠ zero) (hs : subAP (reg 1) ac.1 ≠ zero) {y : Term}
    (hy : y ∈ Kset (reg 1) ac.1 ∨ y ∈ Kset (reg 1) ac.2) :
    lt (reg 1) (ddOf75 (reg 1) ac) = true := by
  have hE : inT (mulL (reg 1) (subAP (reg 1) ac.1)) = true :=
    inT_mulL mulDescInT (inT_reg 1) (inT_subAP h1)
  by_cases hc1 : ac.2 = TM.Term.one
  · have hx1 : subAP (reg 1) ac.1 ≠ TM.Term.one := by
      intro hcc
      rcases hy with hk | hk
      · exact kset_nil_of_subAP_one105 h1 hcc hk
      · rw [hc1, kset_one100] at hk; cases hk
    have hltE : lt (reg 1) (mulL (reg 1) (subAP (reg 1) ac.1)) = true := by
      have hg := mulL_gt105 (inT_reg 1) (inT_subAP h1) hs hx1
      rwa [omegaNF_reg1_80] at hg
    have hom : lt (omegaNF (reg 1)) (omegaNF (mulL (reg 1) (subAP (reg 1) ac.1))) = true :=
      lt_omegaNF_inT79 (inT_reg 1) hE hltE
    rw [omegaNF_reg1_80] at hom
    show lt (reg 1) (mulL (mulL (reg 1) (subAP (reg 1) ac.1)) ac.2) = true
    rw [hc1, mulL_one105]
    exact hom
  · have hA : le (reg 1) (omegaNF (mulL (reg 1) (subAP (reg 1) ac.1))) = true :=
      le_reg_powOf80 (u := 0) omegaNF_reg1_80 h1 hs
    have hB : lt (omegaNF (mulL (reg 1) (subAP (reg 1) ac.1)))
        (mulL (mulL (reg 1) (subAP (reg 1) ac.1)) ac.2) = true :=
      mulL_gt105 hE h3 hz hc1
    exact lt_of_le_of_lt3 (inT_le_fragR _ (inT_reg 1)) (inT_le_fragR _ (inT_omegaNF hE))
      (inT_le_fragR _ (inT_ddOf75 (inT_reg 1) h1 h3)) hA hB

/-- **§105.1 の主定理 — `aV ⊖ Ω₁ ≠ 0` の歩では `Ω₁` 以下の `K` の元はぜんぶ只。**
    §100.2 は `y < Ω₁` までで、`y = Ω₁` を残していた。 -/
theorem lt_idxOf_of_le_reg105 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hl3 : lt ac.2 M = true)
    (hz : ac.2 ≠ zero) (hs : subAP (reg 1) ac.1 ≠ zero) {y : Term}
    (hy : y ∈ Kset (reg 1) ac.1 ∨ y ∈ Kset (reg 1) ac.2)
    (hyi : inT y = true) (hle : le y (reg 1) = true)
    (hidxT : inT (idxOf (reg 1) s ac) = true) :
    lt y (idxOf (reg 1) s ac) = true := by
  cases hlt : lt y (reg 1) with
  | true => exact lt_idxOf_of_lt_reg100 hst h1 h3 hl3 hz hy hyi hlt hidxT
  | false =>
    have hyeq : y = reg 1 := by
      rcases (Bool.or_eq_true _ _).mp hle with hq | hq
      · exact eq_of_beq hq
      · rw [hlt] at hq; exact Bool.noConfusion hq
    have hdT : inT (ddOf75 (reg 1) ac) = true := inT_ddOf75 (inT_reg 1) h1 h3
    have hd : lt (reg 1) (ddOf75 (reg 1) ac) = true := lt_reg_ddOf105 h1 h3 hz hs hy
    have hsub1 : sub1 (ddOf75 (reg 1) ac) = ddOf75 (reg 1) ac :=
      sub1_ddOf86 (u := 0) omegaNF_reg1_80 h1 h3 hz hs
    have hle2 : le (ddOf75 (reg 1) ac) (idxOf (reg 1) s ac) = true := by
      have hq := le_sub1dd_idxOf75 (inT_reg 1) hst h1 h3
      rwa [hsub1] at hq
    rw [hyeq]
    exact lt_of_lt_of_le3 (inT_le_fragR _ (inT_reg 1)) (inT_le_fragR _ hdT)
      (inT_le_fragR _ hidxT) hd hle2

/-- **`Ω₁` の冪そのものが上限になる歩の判定器。**  `aV ⊖ Ω₁ ≠ 0` で、逃げる元が
    `Ω₁^(aV ⊖ Ω₁)` を超えないなら、この歩は只である — 係数が `1` でなければ等号でもよい。 -/
def powFree105 (p : (Option Term × Option Term) × (Term × Term)) (y : Term) : Bool :=
  !(subAP (reg 1) p.2.1 == zero) && le y (powOf80 (reg 1) p.2)
    && (lt y (powOf80 (reg 1) p.2) || !(p.2.2 == TM.Term.one))

/-- **§105.1 の第二の主定理 — `Ω₁^(aV ⊖ Ω₁)` を超えない元はぜんぶ只。**
    `y` の出どころは訊かない。`Ω₁ ≤ Ω₁^(aV ⊖ Ω₁)` (§80.1) なので、これは
    `lt_idxOf_of_le_reg105` の言う範囲をすべて含む — ただし係数が `1` の歩では
    等号の場合に `K` の空を経由するので、両方を残してある。 -/
theorem lt_idxOf_of_powFree105 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hz : ac.2 ≠ zero)
    {y : Term} (hyi : inT y = true) (hpf : powFree105 (s, ac) y = true)
    (hidxT : inT (idxOf (reg 1) s ac) = true) :
    lt y (idxOf (reg 1) s ac) = true := by
  obtain ⟨hp1, hstrict⟩ := (Bool.and_eq_true _ _).mp hpf
  obtain ⟨hsb, hlep⟩ := (Bool.and_eq_true _ _).mp hp1
  have hsub : subAP (reg 1) ac.1 ≠ zero := by
    intro hcc
    rw [show (subAP (reg 1) ac.1 == zero) = true from by rw [hcc]; exact beq_self_eq_true _]
      at hsb
    exact Bool.noConfusion hsb
  have hE : inT (mulL (reg 1) (subAP (reg 1) ac.1)) = true :=
    inT_mulL mulDescInT (inT_reg 1) (inT_subAP h1)
  have hpowT : inT (powOf80 (reg 1) ac) = true := inT_powOf80 (inT_reg 1) h1
  have hdT : inT (ddOf75 (reg 1) ac) = true := inT_ddOf75 (inT_reg 1) h1 h3
  have hsub1 : sub1 (ddOf75 (reg 1) ac) = ddOf75 (reg 1) ac :=
    sub1_ddOf86 (u := 0) omegaNF_reg1_80 h1 h3 hz hsub
  have hled : le (ddOf75 (reg 1) ac) (idxOf (reg 1) s ac) = true := by
    have hq := le_sub1dd_idxOf75 (inT_reg 1) hst h1 h3
    rwa [hsub1] at hq
  have hyd : lt y (ddOf75 (reg 1) ac) = true := by
    rcases (Bool.or_eq_true _ _).mp hstrict with hlt | hne
    · exact lt_of_lt_of_le3 (inT_le_fragR _ hyi) (inT_le_fragR _ hpowT)
        (inT_le_fragR _ hdT) hlt (le_powOf_ddOf80 (inT_reg 1) h1 h3 hz)
    · have hc1 : ac.2 ≠ TM.Term.one := by
        intro hcc
        rw [show (ac.2 == TM.Term.one) = true from by rw [hcc]; exact beq_self_eq_true _]
          at hne
        exact Bool.noConfusion hne
      exact lt_of_le_of_lt3 (inT_le_fragR _ hyi) (inT_le_fragR _ hpowT)
        (inT_le_fragR _ hdT) hlep (mulL_gt105 hE h3 hz hc1)
  exact lt_of_lt_of_le3 (inT_le_fragR _ hyi) (inT_le_fragR _ hdT)
    (inT_le_fragR _ hidxT) hyd hled

end

/-! ### §105.2 条項 — 残るのは `Ω₁` より真に上の元と、`aV = Ω₁` ちょうどの歩だけ -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§105 の条項。** §100 の `IdxK100` から、§105.1 が片づける元 —
    `y ≤ Ω₁` かつ `aV ⊖ Ω₁ ≠ 0` — を義務から外した形。外したものは定理だから、
    門との同値は保たれる (`idxStd105_of_step073` が逆向き)。
    `lt y Ω₁ = false` は §100 のまま残してあるので、条項は §100 の条項の部分集合であり
    (`idxK105_of_idxK100`)、§105 が義務を足していないことがそのまま読める。 -/
def IdxK105 (a : BT) : Prop :=
  ∀ p ∈ scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1,
    le (reg 1) p.2.1 = true → inT (idxOf (reg 1) p.1 p.2) = true →
      ∀ (y : Term) (c e : BT) (j : Term),
        BT.D 1 c ∈ BT.toL a → BT.isStd (BT.D 1 c) = true → BT.lt c a = true →
        e ∈ d0Args88 c → BT.isStd (BT.D 0 e) = true → btLe72 1 e = true →
        BT.lt e a = true → BT.size e < BT.size a →
        idxF88 0 (dict e) = some j → inT j = true → inT (psi (reg 1) j) = true →
        le y j = true → inT y = true → y ∈ Kset (reg 1) (dict c) →
        lt y (reg 1) = false →
        (le y (reg 1) = false ∨ subAP (reg 1) p.2.1 = zero) →
        powFree105 p y = false →
        (∀ i0, p.1.1 = some i0 → lt i0 y = true) →
        monoClosed95 a p e = false → freeSelf95 p e = false →
        (y ∈ Kset (reg 1) p.2.1 ∨ y ∈ Kset (reg 1) p.2.2) →
        lt y (idxOf (reg 1) p.1 p.2) = true

/-- §100 の条項は §105 の条項を出す — 仮説がひとつ増えただけだから。 -/
theorem idxK105_of_idxK100 {a : BT} (H : IdxK100 a) : IdxK105 a := by
  intro p hp hle hidxT y c e j hc hstd hltc he hse hbe hlte hsz hj hjT hpsiT hlej hyT hyk
    hlty _ _ hgt hmono hsf hy
  exact H p hp hle hidxT y c e j hc hstd hltc he hse hbe hlte hsz hj hjT hpsiT hlej hyT hyk
    hlty hgt hmono hsf hy

/-- **§105 の残る仮説。** 部分領域の項について §105 の条項。**証明しない。** -/
def IdxStd105 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → IdxK105 a

/-- **§105.2 の主定理。** 一項ぶんの門は §105 の条項と、326 行目が既に抱えている
    二つの条項と、§95 が名指しした算術ひとつから出る。 -/
theorem gateStd87_of_idxK105 (HD : DictLtStd92) (HM : HiMono89) (HL : LeIdxSelf95) (a : BT)
    (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b)
    (H : btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → IdxK105 a) : GateStd87 a := by
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
    cases hlty : lt y (reg 1) with
    | true => exact lt_idxOf_of_lt_reg100 hst hi1 hi2 hl2 hnz2 hy hyT hlty hidxT
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
      cases hpw : powFree105 q y with
      | true => exact lt_idxOf_of_powFree105 hst hi1 hi2 hnz2 hyT hpw hidxT
      | false =>
      by_cases hsub : subAP (reg 1) q.2.1 = zero
      · exact H hb hs q hq hle2 hidxT y c e j hc hstd hltc he hse hbe hlte hsze
          hj hjT hpsiT hlej hyT hyk hlty (Or.inr hsub) hpw hgt hmono hsf hy
      · cases hley : le y (reg 1) with
        | true =>
          exact lt_idxOf_of_le_reg105 hst hi1 hi2 hl2 hnz2 hsub hy hyT hley hidxT
        | false =>
          exact H hb hs q hq hle2 hidxT y c e j hc hstd hltc he hse hbe hlte hsze
            hj hjT hpsiT hlej hyT hyk hlty (Or.inl hley) hpw hgt hmono hsf hy
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


/-- **§105 の第一の結論。** -/
theorem psiIdxStep073_of_idxStd105 (HD : DictLtStd92) (HM : HiMono89) (HL : LeIdxSelf95)
    (H : IdxStd105) : PsiIdxStep073 :=
  step073_of_gate87 (fun a ih => gateStd87_of_idxK105 HD HM HL a ih (fun hb hs => H a hb hs))

/-- **逆向き。** 足した仮説も外した義務もすべて落ちるので、分解は過不足がない。 -/
theorem idxStd105_of_step073 (H : PsiIdxStep073) : IdxStd105 := by
  intro a hb hs p hp hle
  intro _ y _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hy
  exact (H a hb hs p hp hle).2 y hy

/-- **§105 の第二の結論。** 326 行目の証明書が `K` の側で待つのは §105 の条項ひとつと、
    §74/§89 が既に名指ししている二つと、§95 が名指しした算術ひとつである。 -/
theorem certIn_t326_idx105 (HD : DictLtStd92) (HM : HiMono89) (HL : LeIdxSelf95)
    (H : IdxStd105) (HDe : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_step73 (psiIdxStep073_of_idxStd105 HD HM HL H) HDe HI HC hacc

end

/-! ### §105.3 測定 (凍結) -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- `ψ₀` の引数 `E` を `ψ₁ψ₁0` の `n+1` 個の後ろに差し込んだ発火成分。
    その歩の底 `Ω₁` の指数は `aV = Ω₁·(n+1)`、したがって `aV ⊖ Ω₁ = Ω₁·n`。
    `n = 0` は §100 の `slotHi100` そのもの (`slot105 0 (ehi100 k) = slotHi100 k`)。 -/
def slotArg105 : Nat → BT → BT
  | 0,   E => BT.D 0 E
  | n+1, E => BT.sum (BT.D 1 (BT.D 1 BT.zero)) (slotArg105 n E)

def slot105 (n : Nat) (E : BT) : BT :=
  BT.D 1 (BT.sum (BT.D 1 (BT.D 1 BT.zero)) (slotArg105 n E))

/-- 崩壊指数が `ω^(Ω₁²)` — `Ω₁` より真に上、しかも `Ω₁^(Ω₁)` ちょうど — になる引数。 -/
def eHi2_105 : BT := BT.D 1 (BT.sum (BT.D 1 (BT.D 1 BT.zero)) (BT.D 1 (BT.D 1 BT.zero)))

/-- 崩壊指数が `Ω₁^(Ω₁)·c` (`c > 1`) になる引数 — 枠をもう一段入れ子にしただけ。 -/
def eNest105 (z : BT) : BT := slot105 1 z

/-- **§105 の第一の証人 (21 記号)。** `y = Ω₁` ちょうどの義務が §100 の条項に残る。
    §105.1 の `lt_idxOf_of_le_reg105` が持っていく。 -/
def survA105 : BT := BT.sum (slot105 1 (ehi100 0)) vebTail95

/-- **§105 の第二の証人 (22 記号)。** `y = Ω₁^(aV ⊖ Ω₁)` ちょうど — `Ω₁` より上なので
    §105.1 の第一の定理は届かない。`powFree105` の等号の側が持っていく (係数が `1` でない)。 -/
def survB105 : BT := BT.sum (slot105 1 eHi2_105) vebTail95

/-- **§105 の第三の証人 (25 記号)。** `y = Ω₁^(aV ⊖ Ω₁)·ω > Ω₁^(aV ⊖ Ω₁)`。
    §92.1・§92.2・§95 の三つ・§100・§105 の二つ、どれも届かない。**新しい残余である。** -/
def survC105 : BT := BT.sum (slot105 1 (eNest105 BT.zero)) vebTail95

/-- §105 の条項が訊く組 — §100 の残余から §105.1 の二つの免除を引いたもの。 -/
def oblPost105 (a : BT) :
    List (((Option Term × Option Term) × (Term × Term)) × Term × BT × Term) :=
  (oblPost100 a).filter fun w =>
    (!(le w.2.1 (reg 1)) || (subAP (reg 1) w.1.2.1 == zero)) && !(powFree105 w.1 w.2.1)

/-- 崩壊指数が `Ω₁` の下にない五つの引数と、下にある二つの対照。 -/
def eHiList105 : List BT :=
  [ehi100 0, ehi100 1, eHi2_105, eNest105 BT.zero, eNest105 (twr86 1)]
def eList105 : List BT := eHiList105 ++ [argB95 2, twr86 3]

def pop105 : List BT :=
  ((List.range 3).flatMap fun n => eList105.flatMap fun E =>
    [slot105 n E, BT.sum (slot105 n E) vebTail95,
     BT.sum (slot105 n E) (BT.sum (twr86 3) vebTail95),
     BT.sum (twr86 4) (BT.sum (slot105 n E) vebTail95)]).eraseDups
def qual105 : List BT := pop105.filter okHyp84

/-- 測る母集団ぜんぶ — §100 の 250 項に §105 の 60 項を足したもの。 -/
def corpus105 : List BT := corpus100 ++ qual105

/-- **否定 — 「標準性が `ψ₀` の引数の崩壊指数を `Ω₁` の下に押し込む」は偽。**
    `ehi100 0` は段 1 以下で `BT.isStd (ψ₀ ·)` を満たし、その崩壊指数は `Ω₁` ちょうどである。
    だから `Ω₁ ≤ y` の側を「そんな引数は無い」で閉じることはできない。
    §100 が示唆した道はここで止まる。 -/
theorem notLowIdx105 :
    btLe72 1 (ehi100 0) = true ∧ BT.isStd (BT.D 0 (ehi100 0)) = true ∧
    (idxF88 0 (dict (ehi100 0)) == some (reg 1)) = true ∧ lt (reg 1) (reg 1) = false :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **`Ω₁` 以上の指数は五つの引数で本当に起きる。** -/
theorem eHi_facts105 :
    (eHiList105.all fun E => btLe72 1 E && BT.isStd (BT.D 0 E)
      && (match idxF88 0 (dict E) with
          | none => false
          | some j => inT j && !(lt j (reg 1)))) = true := by decide

/-- **`aV = Ω₁` ちょうどの枠は標準でない — そして門はそこで落ちる。**
    §100 の `slotHi100` の所見を五つの引数すべてに広げたもの。`IdxK105` の第二の選言
    (`aV ⊖ Ω₁ = 0`) を残してあるのはこのためである。 -/
theorem slotHi0_not_std105 :
    (eHiList105.all fun E => btLe72 1 (slot105 0 E) && inT (dict (slot105 0 E))
      && !(BT.isStd (BT.D 0 (slot105 0 E))) && !(stepOKb 0 (dict (slot105 0 E)))
      && !(okHyp84 (slot105 0 E))) = true := by decide

/-- 三つの証人は母集団の仮説をすべて満たし、門はそこで落ちない。 -/
theorem surv105_hyps :
    okHyp84 survA105 = true ∧ okHyp84 survB105 = true ∧ okHyp84 survC105 = true ∧
    stepOKb 0 (dict survA105) = true ∧ stepOKb 0 (dict survB105) = true ∧
    stepOKb 0 (dict survC105) = true ∧
    idxb84 0 (dict survC105) = true ∧ splitb86 0 (dict survC105) = true ∧
    idxLt90b survC105 = true ∧ ltArg90b survC105 = true :=
  ⟨by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide, by decide, by decide⟩

/-- **§100 の条項は空虚ではない。**  `survA105` と `survB105` は §92.1・§92.2・§95 の三つ・
    §100 のどれにも取られない義務をひとつずつ持ち、§105 の二つの免除がそれを持っていく。
    §100 が「測定では出せない」と書いた生き残りが、ここに出ている。 -/
theorem survAB105_counts :
    (oblPost95 survA105).length = 1 ∧ (oblPost100 survA105).length = 1 ∧
    (oblPost105 survA105).length = 0 ∧
    (oblPost95 survB105).length = 1 ∧ (oblPost100 survB105).length = 1 ∧
    (oblPost105 survB105).length = 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **§105 の条項も空虚ではない。**  `survC105` の義務は `Ω₁^(aV ⊖ Ω₁) < y` で、§105 も取らない。
    **これが §105 の残す残余である。** -/
theorem survC105_counts :
    (oblPost95 survC105).length = 1 ∧ (oblPost100 survC105).length = 1 ∧
    (oblPost105 survC105).length = 1 :=
  ⟨by decide, by decide, by decide⟩

/-- **三つの証人の形。**  どれも最初の発火歩、`aV ⊖ Ω₁ ≠ 0`、`lastFire92` は偽。
    違いは `y` の位置だけ — `Ω₁` ちょうど、`Ω₁^(aV ⊖ Ω₁)` ちょうど、その上。 -/
theorem surv105_shape :
    ((oblPost100 survA105).all fun w =>
      le w.2.1 (reg 1) && !(lt w.2.1 (reg 1)) && !(subAP (reg 1) w.1.2.1 == zero)
        && (w.1.1.1 == none)) = true ∧
    ((oblPost100 survB105).all fun w =>
      !(le w.2.1 (reg 1)) && (w.2.1 == powOf80 (reg 1) w.1.2)
        && (w.1.1.1 == none)) = true ∧
    ((oblPost105 survC105).all fun w =>
      !(le w.2.1 (reg 1)) && lt (powOf80 (reg 1) w.1.2) w.2.1
        && !(subAP (reg 1) w.1.2.1 == zero) && (w.1.1.1 == none)) = true ∧
    lastFire92 (dict survA105) = false ∧ lastFire92 (dict survB105) = false ∧
    lastFire92 (dict survC105) = false :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

-- 母集団の大きさと形。12 項が `okHyp84` に落ちる — それが上の否定である。
#guard (pop105.length, qual105.length, corpus105.length) == (72, 60, 310)
#guard ((pop105.map BT.size).foldl min 999, (pop105.map BT.size).foldl max 0) == (10, 37)
#guard (BT.size survA105, BT.size survB105, BT.size survC105) == (21, 22, 25)

/-! **§100 の残余は 0 ではない — 8 である。**  310 項で 271 の義務、§92 の後で 87、
§95 の後で 64、**§100 の後で 8、§105 の後で 4**。8 つはすべて §105 の新しい 60 項の上にある
(`corpus100` だけならやはり 0 で、これが §100 の測定の限界だった)。 -/

#guard ((corpus105.flatMap oblPre92).length, (corpus105.flatMap oblPost92).length,
        (corpus105.flatMap oblPost95).length,
        (corpus105.flatMap oblPost100).length,
        (corpus105.flatMap oblPost105).length) == (271, 87, 64, 8, 4)
#guard ((corpus100.flatMap oblPost100).length, (corpus100.flatMap oblPost105).length)
       == (0, 0)

/-! **内訳。**  §100 の残余 8 のうち 2 が `y ≤ Ω₁` (§105.1 の第一の定理)、
4 が `powFree105` (第二の定理)、残る 4 が新しい残余である。 -/

#guard
  (let o := corpus105.flatMap fun a => (oblPost100 a).map fun w => (a, w)
   (o.length,
    (o.countP fun w => le w.2.2.1 (reg 1)),
    (o.countP fun w => !(le w.2.2.1 (reg 1))),
    (o.countP fun w => powFree105 w.2.1 w.2.2.1))) == (8, 2, 6, 4)

/-! **残る 4 つは一つの形。**  `Ω₁^(aV ⊖ Ω₁) < y`、`aV ⊖ Ω₁ ≠ 0`、最初の発火歩。
`y` は `Ω₁^(aV ⊖ Ω₁)·c` (`c = ω` または `c = ω^ω`) で、歩が立てる `Δ` は
`Ω₁^(aV ⊖ Ω₁)·cV`。**次の条項が見なければならないのは係数である。** -/

#guard
  (let o := corpus105.flatMap fun a => (oblPost105 a).map fun w => (a, w)
   (o.length,
    (o.countP fun w => !(le w.2.2.1 (reg 1))),
    (o.countP fun w => lt (powOf80 (reg 1) w.2.1.2) w.2.2.1),
    (o.countP fun w => subAP (reg 1) w.2.1.2.1 == zero),
    (o.countP fun w => w.2.1.1.1 == none))) == (4, 4, 4, 0, 4)

/-! **門は母集団のどこでも落ちない。** -/

#guard ((qual105.filter fun a => !(stepOKb 0 (dict a))).length,
        (qual105.filter fun a => !(idxb84 0 (dict a))).length,
        (qual105.filter fun a => !(splitb86 0 (dict a))).length,
        (qual105.filter fun a => !(idxLt90b a)).length,
        (qual105.filter fun a => !(ltArg90b a)).length) == (0, 0, 0, 0, 0)

/-! **`n = 0` は §100 の枠そのもの。** -/

#guard (List.range 4).all fun k => slot105 0 (ehi100 k) == slotHi100 k

end

/-! ### §105.4 広い方の測定 — 塔の組み合わせを総当たりで作る (凍結) -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 崩壊指数が `Ω₁` の上にある引数をもうひとつ。 -/
def eHi3_105 : BT :=
  BT.D 1 (BT.sum (BT.D 1 (BT.D 1 (BT.D 1 BT.zero))) (BT.D 1 (BT.D 1 BT.zero)))
def eArgs105 : List BT :=
  eHiList105 ++ [ehi100 2, eHi3_105, eNest105 (twr86 2), argB95 2, twr86 3, twr86 4]

/-- 発火成分の `Ω₁` の部分に置ける塔。`divAP Ω₁` を通すと順に
    `Ω₁^{Ω₁^{Ω₁}}`・`Ω₁^{Ω₁}`・`Ω₁`・`1` になる。 -/
def hParts105 : List BT := [twr86 4, twr86 3, twr86 2, twr86 1]

/-- 長さ 1・2・3 の並びを総当たり (降順でないものは `okHyp84` が落とす)。 -/
def hLists105 : List (List BT) :=
  ((List.range 4).flatMap fun i => (List.range 4).flatMap fun j => (List.range 4).map fun k =>
     [hParts105.getD i BT.zero, hParts105.getD j BT.zero, hParts105.getD k BT.zero]).eraseDups
   ++ ((List.range 4).flatMap fun i => (List.range 4).map fun j =>
     [hParts105.getD i BT.zero, hParts105.getD j BT.zero]).eraseDups
   ++ (List.range 4).map (fun i => [hParts105.getD i BT.zero])

/-- `Ω₁` の部分を並べ、その後ろに `ψ₀ E` を置いた発火成分。 -/
def mix105 (hs : List BT) (E : BT) : BT := BT.D 1 (BT.ofL (hs ++ [BT.D 0 E]))

def tails105 : List (BT → BT) :=
  [ fun b => b, fun b => BT.sum b vebTail95,
    fun b => BT.sum b (BT.sum (twr86 3) vebTail95),
    fun b => BT.sum (twr86 5) (BT.sum b vebTail95) ]

def wide105 : List BT :=
  (hLists105.flatMap fun hs => eArgs105.flatMap fun E =>
     tails105.map fun f => f (mix105 hs E)).eraseDups
def wideQual105 : List BT := wide105.filter okHyp84

/-! **3360 項を作り、924 項が仮説を満たす。門はそのどこでも落ちない。**
義務は 695 → 386 (§92) → 28 (§95) → 22 (§100) → **6 (§105)**。 -/

#guard (wide105.length, wideQual105.length) == (3360, 924)

#guard ((wideQual105.filter fun a => !(stepOKb 0 (dict a))).length,
        (wideQual105.filter fun a => !(idxb84 0 (dict a))).length,
        (wideQual105.filter fun a => !(splitb86 0 (dict a))).length,
        (wideQual105.filter fun a => !(idxLt90b a)).length,
        (wideQual105.filter fun a => !(ltArg90b a)).length) == (0, 0, 0, 0, 0)

#guard ((wideQual105.flatMap oblPre92).length, (wideQual105.flatMap oblPost92).length,
        (wideQual105.flatMap oblPost95).length, (wideQual105.flatMap oblPost100).length,
        (wideQual105.flatMap oblPost105).length) == (695, 386, 28, 22, 6)

/-! **残る 6 つも同じ一つの形。**  どれも `aV ⊖ Ω₁ = Ω₁` の歩で、`y = Ω₁^{Ω₁}·c`
(`c = ω`, `ω^ω`, `ω^{φ̄(2,0)}`) — 係数だけが `1` を超えている。 -/

#guard
  (let o := wideQual105.flatMap fun a => (oblPost105 a).map fun w => (a, w)
   (o.length,
    (o.countP fun w => subAP (reg 1) w.2.1.2.1 == reg 1),
    (o.countP fun w => lt (powOf80 (reg 1) w.2.1.2) w.2.2.1),
    ((o.map fun w => w.2.2.1).eraseDups).length)) == (6, 6, 6, 3)

/-! **否定 — 門が落ちる場所は 213 ある。**  どれも `inT (dict ·)` を満たし、
`BT.isStd (ψ₀ ·)` だけで母集団の外に出ている。§100 が `slotHi100` ひとつで見たものが、
ここでは 213 個ある。**標準性を見ない条項では `Ω₁ ≤ y` の側は閉じない。** -/

#guard (wide105.filter fun a =>
    !(okHyp84 a) && inT (dict a) && !(stepOKb 0 (dict a))).length == 213

end

/-! ## §107 THE TARGET IS AN IMAGE POINT — `DictDenseAbove102` IS FALSE, AND THE FINER STEP
       OPERATOR CANNOT CROSS `Γ₀`

§102 split the high half of row 326's density gate by the target's interval and left three
clauses; §103 took the `(ε₀, Γ₀]` one down to its open part.  §107 was asked for the other
two — `DictDenseMid102` (target in `(Γ₀, Γ₁)`) and `DictDenseAbove102` (target and challenger
both `≥ Γ₁`) — and for the FINER STEP OPERATOR that §102 said (b2) needs:

> §98's `bStep98` builds them, but its step lands at `φ̄(dict x, Γ₀ ⊕ 1)` — a whole Veblen
> step above its input — so that family cannot be dense inside a segment.  (b2) needs a
> FINER step operator than §98's, and this file does not have one.

**Both answers are negative, and they are different kinds of negative.**  (c) is FALSE as
written and §107 proves it.  The finer operator EXISTS — it is §103.4's `ψ₀(ψ₁ψ₁ ·)` freed
from its one starting point — and §107 builds it in general, with its own invariant and its
own fold; but it provably cannot be used above `Γ₀`, for two independent reasons, so (b2) is
not the construction problem §102 took it for.  What (b2) actually is, §107.5 names and
measures but does not prove.

  §107.1  **(c) IS FALSE.**  `DictDenseAbove102` puts no ceiling on the target, so `v = M`
          and `s = Ω₁` is an instance of it — and §94.1's `ltW_dict94` says every legal
          witness has `dict b < Ω₁`, so no witness can be at or above the challenger.
          `dictDenseAbove_false107`.  The failure is the CLAUSE's, not the gate's: at the
          only place (c) is used the target is `vOf t`, which §94.1 puts below `Ω₁`.

  §107.2  **THE REPAIR — THE TARGET IS AN IMAGE POINT.**  `DictDenseMid107` and
          `DictDenseAbove107` are §102.6's (b2) and (c) with the target given as `dict b₀`
          for a legal `b₀`.  That is exactly what the use site has (`vOfIsDict76` plus
          §77's `btLeA77`/`stdA77` and §85's `hd085_bValA71_85`), and both are strictly
          weaker than §102's (`mid107_of_mid102`, `above107_of_above102`).
          `dictDenseHi_of107` and `certIn_t326_107` re-hang row 326 on them, so the
          certificate no longer rests on a hypothesis that is FALSE outright.  (§107.5 then
          says the repair is not enough either — but that is conditional on an unproved
          clause, and (c)'s falsity is not.)

  §107.3  **THE FINER OPERATOR, IN GENERAL.**  `vStep107 x = ψ₀(ψ₁ψ₁ x)` — §98's `bStep98`
          with the `Ω^Ω ⊕` prefix deleted.  `InvV107` is §98's `Inv98` with the fourth
          conjunct's target moved from `bArg98 x` down to `ψ₁ψ₁ x`; `isStd_vStep107`,
          `lt_x_vStep107` and `inv_vStep107` are the three lemmas that makes it run, and
          `dict_vStep107` is the fold: `dict (vStep107 x) = φ̄(dict x, 0)` — **one Veblen
          step, with no `⊕ 1`**, which is precisely what §102 asked for.  `vIter107` climbs
          from any starting point and `dict_vIter107` says the values are §102.2's tower
          `vTow102 (dict x) ·`.  §103.4's tower is the instance at `ψ₀Ω₁`
          (`gInv_eq_vIter107`), and `denseAtGam0_seed107` is §103.5 from any seed at all.

  §107.4  **AND IT STOPS AT `Γ₀`, TWICE OVER.**  (i) The VALUE degenerates:
          `phiNF_sc_zero107` — at a strongly critical head `φ̄(·,0)` is the identity — and
          `Γ₀ ∈ SC`, so `collapse0_Q_sc107` / `dict_vStep_sc107` give
          `dict (vStep107 x) = dict x` there.  The first rung of §94.6's raw tower,
          `φ̄(Γ₀,0)`, is not one step above `Γ₀` in this system; it is not reachable at all.
          (ii) The STANDARDNESS fails, and it fails at `Γ₀` itself:
          `invV_needs_ltOO107` — the invariant forces every element of `GB 0 x` below
          `Ω^Ω`, because §98's own `lt_D1D1_bOO98` puts every `ψ₁ψ₁` of a `D 0`-headed term
          there — so `invV_bG0_false107`: **`Γ₀`'s own witness `ψ₀(Ω^Ω)` already breaks it.**
          A fortiori the two operators never compose (`invV_bStep_false107`,
          `vStep_bStep_not_std107`, for EVERY `x`).  §94.6's remark that "dropping the
          `Ω^Ω ⊕` prefix breaks standardness once the argument reaches `Γ₀`" is now a
          theorem, and it is general.

  §107.5  **WHAT (b2) REALLY IS — A GAP, NOT A MISSING CONSTRUCTION.**  Above `Γ₀` the fold
          takes its strongly critical branch FIRST, so the accumulated base is `Γ₀` and
          every later Veblen digit lands at `φ̄(a, Γ₀ ⊕ c)` with `c ≥ 1`.  The consequence
          is `GapAtG0_107` : **no legal witness has a value in
          `[φ̄(Γ₀,0), φ̄(Γ₀,Γ₀⊕1))`** — between §94.6's first raw rung and §98's first tower
          value.  It is a HYPOTHESIS here, marked as such, measured in §107.7 on two
          populations (570 and 88 legal witnesses) with 0 exceptions.  If it is a theorem
          then EVERY ONE of `DictDenseMid107`, `DictDenseMid102`, `DictDenseHi94`,
          `DictDense85` and — by §85's equivalence — **`CofDenseS1`** is FALSE, each with
          its own one-line proof from the gap; the last of those is what row 326's
          cofinality side is built on.  The
          refuting pair is named and computed: the target is `vOf tGap107` where
          `tGap107 = bInv85 (bTowG98 1)` is a standard limit matrix of the sub-region
          (`stdB1_tGap107`, `kind_tGap107`, `bVal_tGap107`, all by computation), and the
          challenger is `rawT94 0`.  **This is why §102's diagnosis was wrong**: a finer
          operator cannot fill an interval that has no image point in it.

  §107.6  **LEVEL HONESTY.**  `btLe1_vIter107` — the finer construction never emits an index
          above 1, so §85.6's level-two refutation stays out of reach; `btLe0_vStep107` — it
          leaves level 0 at the first step, exactly like §98's and §103's.

WHAT IS **NOT** CLAIMED.  `GapAtG0_107` is NOT proved; §107 does not refute `DictDense85`
outright, it refutes it FROM the gap.  `certIn_t326_107` is a repair of the WIRING, not a
claim that its hypotheses hold: if the gap is a theorem then `DictDenseMid107` is false and
`certIn_t326_107` is as vacuous as `certIn_t326_103` already is.  `DictDenseMid107`, `DictDenseAbove107` and
`DictOntoMidOpen103` are NOT proved.  `PsiIdxOKStd172` and `DictLtA74` are used, not proved.
What §107 does settle unconditionally is that `DictDenseAbove102` is false and that the
finer operator cannot be pushed above `Γ₀`.

**Where §107 stopped, precisely.**  Proving `GapAtG0_107` needs what §89 needed and more: a
structural theorem about `collapse 0`'s fold saying that once the strongly critical branch
has fired, every subsequent Veblen digit's second argument is at or above `Γ₀ ⊕ 1`, and that
the leading digit cannot be `≥ Γ₀` without the argument being at or above `bArg98`'s.  §107
computes both halves on a population and states the consequence; it does not prove either.
The honest reading is that the residue MOVED: §102 left "build a finer operator", §107
returns "the operator is built, it cannot cross `Γ₀`, and the reason it cannot is that there
is nothing to build there".

WHAT THE MEASUREMENT SAYS (§107.7 gives the construction).  Two populations of legal
witnesses, neither filtered by the hypothesis.  The first is §94.7's `pool94`, thinned four to one,
closed once under §98's step, the finer step, `⊕`, and three `Ω^Ω`-prefixed shapes (570
legal terms);
the second is a small hand-built adversarial one whose seeds are exactly the shapes that
could land in the window — two Veblen digits, a doubled `Ω^Ω`, a `ψ₁` of a sum (88 legal
terms).

  * **The gap is exact — 0 exceptions in 1655 and 0 in 88.**  Not one legal witness has a
    value in `[φ̄(Γ₀,0), φ̄(Γ₀,Γ₀⊕1))`, at the first rung or at the second or the third.
  * **The hypothesis is visible.**  The premise `φ̄(Γ₀,0) ≤ dict b` holds of 163 of the
    570 and 58 of the 88; the sweep is not vacuous.  The 277 values in `[Γ₀,Γ₁)` split
    246 + 0 + 31: below the raw rung, in the window, at or above §98's rung.
  * **The window is full of CHALLENGERS.**  `φ̄(Γ₀,0)`, `φ̄(Γ₀,1)`, `φ̄(Γ₀,ω)`, `φ̄(Γ₀,ε₀)`
    and `φ̄(Γ₀,Γ₀)` are all in 𝔗(M) and all in it — and **25 of §94.7's own 221 challengers
    are in it**.  §94.7 missed them because its 495-term pool has no target inside the
    window either; the gap is a statement about the image, not about the order.
  * **The contrast one level down.**  The same measurement below `Γ₀` finds the image dense:
    the analogous window at the `Γ₀`-tower's rungs is populated, which is why §103's side
    of the gate is a proof problem and this one is not.
  * **The named endpoints.**  `dictInv` answers `none` at every rung of `rawT94`, and
    `bTowG98 1` is a legal witness whose value is the first thing above the window. -/

/-! ### §107.1 §102.6 の (c) は偽 — 目標に天井がない -/

section
open Trans.Recal
open Trans.Dict (BT dict reg)
open TM TM.Term
open Evidence.WF

/-- `Γ₁ < Ω₁`。§94.1 の `ltW_dict94` を §85.7 の `bGam85` に当てただけ。 -/
theorem ltW_Gam1_107 (Hp : PsiIdxOKStd172) : lt Gam1_94 (reg 1) = true :=
  ltW_dict94 Hp bGam85 (rfl : btLe72 1 bGam85 = true) (rfl : BT.isStd bGam85 = true) hd0_bGam98

theorem ltM_Gam1_107 (Hp : PsiIdxOKStd172) : lt Gam1_94 M = true :=
  lt_trans_inT (inT_Gam1_102 Hp) inT_W79 inT_M (ltW_Gam1_107 Hp) ltM_W79

/-- **§107.1 の主定理 — `DictDenseAbove102` は偽である。**
    目標 `v` に上限がないので `v = M`・挑戦者 `s = Ω₁` が条項の実例になってしまう。
    ところが §94.1 により正しい証人の値はどれも `Ω₁` より下なので、`Ω₁` 以上の
    挑戦者を押さえられる証人は一つもない。 -/
theorem dictDenseAbove_false107 (Hp : PsiIdxOKStd172) : ¬ DictDenseAbove102 := by
  intro H
  have hW : lt Gam1_94 (reg 1) = true := ltW_Gam1_107 Hp
  obtain ⟨b, hb, hst, hd, hle, _⟩ :=
    H M inT_M (le_of_lt (ltM_Gam1_107 Hp)) (reg 1) inT_W79 (le_of_lt hW) ltM_W79
  have h1 : lt (dict b) (reg 1) = true := ltW_dict94 Hp b hb hst hd
  rcases (Bool.or_eq_true _ _).mp hle with h2 | h2
  · rw [← eq_of_beq h2, lt_irrefl] at h1; exact Bool.noConfusion h1
  · rw [lt_asymm_inT inT_W79 (inT_dict_of_std172 Hp b hb hst).1 h2] at h1
    exact Bool.noConfusion h1

end

/-! ### §107.2 直した二本 — 目標は `dict` の像である -/

section
open Trans.Recal
open Trans.Dict (BT dict reg)
open TM TM.Term
open Evidence.WF

/-- **(b2) を直したもの。**  目標を `dict` の像に限る — §94.1 の `ltW_vOf94` が
    示すとおり、使う場所ではそれは自動的に成り立っている。**証明しない。** -/
def DictDenseMid107 : Prop := ∀ b0 : BT, btLe72 1 b0 = true → BT.isStd b0 = true → Hd085 b0 →
    lt G094 (dict b0) = true → lt (dict b0) Gam1_94 = true →
    ∀ s : Term, inT s = true → lt s (dict b0) = true →
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
      le s (dict b) = true ∧ lt (dict b) (dict b0) = true

/-- **(c) を直したもの。**  §107.1 が偽にしたのはちょうど「目標が像でなくてよい」
    という部分である。**証明しない。** -/
def DictDenseAbove107 : Prop := ∀ b0 : BT, btLe72 1 b0 = true → BT.isStd b0 = true → Hd085 b0 →
    le Gam1_94 (dict b0) = true →
    ∀ s : Term, inT s = true → le Gam1_94 s = true → lt s (dict b0) = true →
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
      le s (dict b) = true ∧ lt (dict b) (dict b0) = true

theorem mid107_of_mid102 (Hp : PsiIdxOKStd172) (H : DictDenseMid102) : DictDenseMid107 :=
  fun b0 hb hs _ h1 h2 s hsi hlt =>
    H (dict b0) (inT_dict_of_std172 Hp b0 hb hs).1 h1 h2 s hsi hlt

theorem above107_of_above102 (Hp : PsiIdxOKStd172) (H : DictDenseAbove102) : DictDenseAbove107 :=
  fun b0 hb hs _ h1 s hsi h2 hlt =>
    H (dict b0) (inT_dict_of_std172 Hp b0 hb hs).1 h1 s hsi h2 hlt

/-- **§107.2 の主定理。**  §103.5 の分解を、目標が像であることを使って書き直したもの。
    (a) は §102.5、(b1) の端点は §103.5、残るのは (b1) の内部と直した (b2)(c)。 -/
theorem dictDenseHi_of107 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (H1 : DictOntoMidOpen103) (H3 : DictDenseMid107) (H4 : DictDenseAbove107) :
    DictDenseHi94 := by
  intro t ht _ hvE s hs _ hlt
  have hb0 : vOf t = dict (bValA71 t) := vOfIsDict76 Hp t ht
  have hL1 : btLe72 1 (bValA71 t) = true := btLeA77 t ht
  have hL2 : BT.isStd (bValA71 t) = true := stdA77 t ht
  have hL3 : Hd085 (bValA71 t) := hd085_bValA71_85 t (nfB_of_stdB t (stdB_of_stdB1 t ht))
  have hiv : inT (vOf t) = true := inT_vOf94 Hp t ht
  have hiG1 : inT Gam1_94 = true := inT_Gam1_102 Hp
  rcases lt_trichotomy_inT hiv hiG1 with hv | hv | hv
  · rcases lt_trichotomy_inT hiv inT_G094_102 with hg | hg | hg
    · exact denseMid_of_open103 Hp H1 hiv (le_of_lt94 hg.1) hvE hs hlt
    · exact denseMid_of_open103 Hp H1 hiv (by rw [hg.2.1]; exact le_self G094) hvE hs hlt
    · have hx := H3 (bValA71 t) hL1 hL2 hL3 (by rw [← hb0]; exact hg.2.2)
        (by rw [← hb0]; exact hv.1) s hs (by rw [← hb0]; exact hlt)
      rw [← hb0] at hx; exact hx
  · rcases lt_trichotomy_inT hs hiG1 with hsg | hsg | hsg
    · exact denseHi_below_Gam1_102 Hp H2 hiv (by rw [hv.2.1]; exact le_self Gam1_94) hs hsg.1
    · have hx := H4 (bValA71 t) hL1 hL2 hL3 (by rw [← hb0, hv.2.1]; exact le_self Gam1_94)
        s hs (by rw [hsg.2.1]; exact le_self Gam1_94) (by rw [← hb0]; exact hlt)
      rw [← hb0] at hx; exact hx
    · have hx := H4 (bValA71 t) hL1 hL2 hL3 (by rw [← hb0, hv.2.1]; exact le_self Gam1_94)
        s hs (le_of_lt94 hsg.2.2) (by rw [← hb0]; exact hlt)
      rw [← hb0] at hx; exact hx
  · rcases lt_trichotomy_inT hs hiG1 with hsg | hsg | hsg
    · exact denseHi_below_Gam1_102 Hp H2 hiv (le_of_lt94 hv.2.2) hs hsg.1
    · have hx := H4 (bValA71 t) hL1 hL2 hL3 (by rw [← hb0]; exact le_of_lt94 hv.2.2)
        s hs (by rw [hsg.2.1]; exact le_self Gam1_94) (by rw [← hb0]; exact hlt)
      rw [← hb0] at hx; exact hx
    · have hx := H4 (bValA71 t) hL1 hL2 hL3 (by rw [← hb0]; exact le_of_lt94 hv.2.2)
        s hs (le_of_lt94 hsg.2.2) (by rw [← hb0]; exact hlt)
      rw [← hb0] at hx; exact hx

/-- 326 行目の証明書 — 密度の側で待つのは (b1) の内部と、直した (b2)(c) の三本。
    §103 の `certIn_t326_103` と違い、偽の仮説の上には乗っていない。 -/
theorem certIn_t326_107 (Hp : PsiIdxOKStd172) (H : HiMono89)
    (H1 : DictOntoMidOpen103) (H3 : DictDenseMid107) (H4 : DictDenseAbove107)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_99 Hp H (dictDenseHi_of107 Hp (dictLtA74_99 Hp H) H1 H3 H4) hacc

end

/-! ### §107.3 細かい段の作用素 — 不変量と畳み込み -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP)
open TM TM.Term
open Evidence.WF

/-- **細かい段の作用素。**  `ψ₀(ψ₁ψ₁ x)` — §98 の `bStep98` から前置の `Ω^Ω ⊕` を
    削ったもの。§103.4 の塔はこれを `ψ₀Ω₁` から回した一例である。 -/
def vStep107 (x : BT) : BT := BT.D 0 (BT.D 1 (BT.D 1 x))

/-- **細かい作用素の不変量。**  §98 の `Inv98` と同じ四条で、第 4 条の的が
    `bArg98 x` ではなく `ψ₁ψ₁ x` — そこが「細かい」ということであり、
    §107.4 が示すとおり、そこが天井でもある。 -/
def InvV107 (x : BT) : Prop :=
  btLe72 1 x = true ∧ BT.isStd x = true ∧ Hd085 x ∧
    (∀ e ∈ BT.GB 0 x, BT.lt e (BT.D 1 (BT.D 1 x)))

theorem gb0_vStep107 (x : BT) :
    BT.GB 0 (vStep107 x) = BT.D 1 (BT.D 1 x) :: BT.D 1 x :: x :: BT.GB 0 x := rfl

theorem hd0_vStep107 (x : BT) : Hd085 (vStep107 x) := by
  intro z hz; exact ⟨BT.D 1 (BT.D 1 x), List.mem_singleton.mp hz⟩

theorem btLe_vStep107 {x : BT} (h : btLe72 1 x = true) : btLe72 1 (vStep107 x) = true := by
  show (decide (0 ≤ 1) && (decide (1 ≤ 1) && (decide (1 ≤ 1) && btLe72 1 x))) = true
  rw [h]; rfl

/-- `ψ₁ψ₁` は `BT.lt` を保つ。 -/
theorem lt_D1D1_107 {x y : BT} (h : BT.lt x y = true) :
    BT.lt (BT.D 1 (BT.D 1 x)) (BT.D 1 (BT.D 1 y)) = true :=
  btlt_arg98 (bt_ne_of_lt98 (btlt_arg98 (bt_ne_of_lt98 h) h))
    (btlt_arg98 (bt_ne_of_lt98 h) h)

/-- **一段上げた項は標準。**  効いているのは不変量の第 4 条だけ — §103.4 の
    `isStd_gInv103` を任意の出発点へ一般化したもの。 -/
theorem isStd_vStep107 {x : BT} (hd : Hd085 x) (hs : BT.isStd x = true)
    (hgb : ∀ e ∈ BT.GB 0 x, BT.lt e (BT.D 1 (BT.D 1 x))) :
    BT.isStd (vStep107 x) = true := by
  show (BT.isStd (BT.D 1 (BT.D 1 x)) &&
    (BT.GB 0 (BT.D 1 (BT.D 1 x))).all (fun e => BT.lt e (BT.D 1 (BT.D 1 x)))) = true
  rw [isStd_D1D1_98 hd hs, Bool.true_and, List.all_eq_true]
  intro e he
  have hm : e ∈ BT.D 1 x :: x :: BT.GB 0 x := he
  rcases List.mem_cons.mp hm with h1 | h1
  · rw [h1]
    exact btlt_arg98 (bt_ne_of_lt98 (btlt_hd0_D1_98 hd x)) (btlt_hd0_D1_98 hd x)
  rcases List.mem_cons.mp h1 with h2 | h2
  · rw [h2]; exact btlt_hd0_D1_98 hd _
  · exact hgb e h2

/-- **一段上げると真に上がる。**  §98 の `lt_x_bStep98` の細かい版。 -/
theorem lt_x_vStep107 {x : BT} (hd : Hd085 x)
    (hgb : ∀ e ∈ BT.GB 0 x, BT.lt e (BT.D 1 (BT.D 1 x))) :
    BT.lt x (vStep107 x) = true := by
  show BT.ltL (BT.size x + BT.size (BT.D 0 (BT.D 1 (BT.D 1 x))) + 2) x.toL
    [BT.D 0 (BT.D 1 (BT.D 1 x))] = true
  cases hx : x.toL with
  | nil => exact ltL_nil_cons93 _ _ _
  | cons z zs =>
      obtain ⟨c, hzc, hcm⟩ := head_gb98 x hd z (by rw [hx]; exact List.Mem.head _)
      have hsz : BT.size z ≤ BT.size x := size_mem_toL98 x z (by rw [hx]; exact List.Mem.head _)
      rw [hzc] at hsz
      have hlt := hgb c hcm
      rw [hzc,
        show BT.size x + BT.size (BT.D 0 (BT.D 1 (BT.D 1 x))) + 2
          = (BT.size x + BT.size (BT.D 0 (BT.D 1 (BT.D 1 x))) + 1) + 1 from rfl,
        ltL_DD93, if_neg (by omega), if_neg (by omega),
        if_neg (by rw [bt_ne_of_lt98 hlt]; exact Bool.noConfusion)]
      refine ltL_fuel93 (BT.size c + BT.size (BT.D 1 (BT.D 1 x)) + 2) _ _ _ ?_ hlt
      have h1 : BT.size (BT.D 0 c) = 1 + BT.size c := rfl
      have h2 : BT.size (BT.D 0 (BT.D 1 (BT.D 1 x)))
          = 1 + BT.size (BT.D 1 (BT.D 1 x)) := rfl
      omega

/-- **不変量は一段上げても保たれる。** -/
theorem inv_vStep107 {x : BT} (H : InvV107 x) : InvV107 (vStep107 x) := by
  obtain ⟨hb, hs, hd, hgb⟩ := H
  have hlt : BT.lt x (vStep107 x) = true := lt_x_vStep107 hd hgb
  have hA : BT.lt (BT.D 1 (BT.D 1 x)) (BT.D 1 (BT.D 1 (vStep107 x))) = true := lt_D1D1_107 hlt
  refine ⟨btLe_vStep107 hb, isStd_vStep107 hd hs hgb, hd0_vStep107 x, ?_⟩
  intro e he
  have hm : e ∈ BT.D 1 (BT.D 1 x) :: BT.D 1 x :: x :: BT.GB 0 x := he
  rcases List.mem_cons.mp hm with h1 | h1
  · rw [h1]; exact hA
  rcases List.mem_cons.mp h1 with h2 | h2
  · rw [h2]
    exact btlt_arg98 (bt_ne_of_lt98 (btlt_hd0_D1_98 hd (vStep107 x)))
      (btlt_hd0_D1_98 hd (vStep107 x))
  rcases List.mem_cons.mp h2 with h3 | h3
  · rw [h3]; exact btlt_hd0_D1_98 hd _
  · exact lt_trans83 (hgb e h3) hA

/-- 出発点を選べる細かい塔。 -/
def vIter107 (x : BT) : Nat → BT
  | 0 => x
  | n + 1 => vStep107 (vIter107 x n)

theorem inv_vIter107 {x : BT} (H : InvV107 x) : ∀ n, InvV107 (vIter107 x n)
  | 0 => H
  | n + 1 => inv_vStep107 (inv_vIter107 H n)

theorem legal_vIter107 {x : BT} (H : InvV107 x) (n : Nat) :
    btLe72 1 (vIter107 x n) = true ∧ BT.isStd (vIter107 x n) = true ∧ Hd085 (vIter107 x n) :=
  ⟨(inv_vIter107 H n).1, (inv_vIter107 H n).2.1, (inv_vIter107 H n).2.2.1⟩

theorem lt_vIter107 {x : BT} (H : InvV107 x) (n : Nat) :
    BT.lt (vIter107 x n) (vIter107 x (n + 1)) = true :=
  lt_x_vStep107 (inv_vIter107 H n).2.2.1 (inv_vIter107 H n).2.2.2

/-- **§107.3 の主定理 (1) — 畳み込み。**  一段上げた証人の値は `φ̄(dict x, 0)`。
    §98.4 の `dict_bStep98` が `φ̄(dict x, Γ₀ ⊕ 1)` に着くのに対し、こちらは
    `⊕ 1` を持たない — §102 が要求した「細かさ」はこれである。 -/
theorem dict_vStep107 (Hp : PsiIdxOKStd172) {x : BT} (hb : btLe72 1 x = true)
    (hs : BT.isStd x = true) (hd : Hd085 x) (hg : Good103 (dict x))
    (hSC : (dict x).isSC = false) : dict (vStep107 x) = phi (dict x) zero := by
  show collapse 0 (dict (BT.D 1 (BT.D 1 x))) = phi (dict x) zero
  rw [dict_D1D1x103 Hp hb hs hd hg, collapse0_Q103 hg hSC]

/-- `Good103` は `φ̄(·,0)` で閉じている。 -/
theorem good103_phi107 {X : Term} (h : Good103 X) : Good103 (phi X zero) := by
  have hap := h.2.1
  have hXnz : X ≠ zero := by intro hz; rw [hz] at hap; exact Bool.noConfusion hap
  refine ⟨?_, rfl, ?_, omegaNF_phi98 (lt_zero_ne76 hXnz), ?_⟩
  · show (inT X && inT (zero : Term) && lt X M && lt (zero : Term) M) = true
    rw [h.1, inT_zero, good_ltM103 h, lt_zero_M]; rfl
  · cases hc : (phi X zero == TM.Term.one) with
    | false => rfl
    | true =>
        exfalso
        have hq : phi X zero = phi zero zero := eq_of_beq hc
        injection hq with h1 _
        exact hXnz h1
  · show lt (phi X zero) (Z zero) = true
    rw [lt_phi_Z103, show lt X (Z zero) = true from h.2.2.2.2,
      show lt (zero : Term) (Z zero) = true from lt_zero_Z103 zero]
    rfl

/-- 塔の各段は `Good103` で、しかも `SC` ではない — だから作用素はそのまま回る。 -/
theorem good103_vTow107 {X : Term} (h : Good103 X) (hSC : X.isSC = false) :
    ∀ n, Good103 (vTow102 X n) ∧ (vTow102 X n).isSC = false
  | 0 => ⟨h, hSC⟩
  | n + 1 => ⟨good103_phi107 (good103_vTow107 h hSC n).1, rfl⟩

/-- **§107.3 の主定理 (2) — 細かい塔の値の閉じた形。**  §102.2 の塔そのもの。 -/
theorem dict_vIter107 (Hp : PsiIdxOKStd172) {x : BT} (H : InvV107 x)
    (hg : Good103 (dict x)) (hSC : (dict x).isSC = false) :
    ∀ n, dict (vIter107 x n) = vTow102 (dict x) n
  | 0 => rfl
  | n + 1 => by
      have ih := dict_vIter107 Hp H hg hSC n
      have hL := inv_vIter107 H n
      have hgn : Good103 (dict (vIter107 x n)) := by
        rw [ih]; exact (good103_vTow107 hg hSC n).1
      have hsn : (dict (vIter107 x n)).isSC = false := by
        rw [ih]; exact (good103_vTow107 hg hSC n).2
      show dict (vStep107 (vIter107 x n)) = phi (vTow102 (dict x) n) zero
      rw [dict_vStep107 Hp hL.1 hL.2.1 hL.2.2.1 hgn hsn, ih]

/-- **§107.3 の主定理 (3) — 塔はまるごと `dict` の像の中にいる。** -/
theorem towInImage107 (Hp : PsiIdxOKStd172) {x : BT} (H : InvV107 x)
    (hg : Good103 (dict x)) (hSC : (dict x).isSC = false) (n : Nat) :
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
      dict b = vTow102 (dict x) n :=
  ⟨vIter107 x n, (legal_vIter107 H n).1, (legal_vIter107 H n).2.1, (legal_vIter107 H n).2.2,
    dict_vIter107 Hp H hg hSC n⟩

/-! §103.4 の塔はこの作用素の一例である。 -/

theorem invV_gInv1_107 : InvV107 (gInv103 1) := by
  refine ⟨rfl, rfl, hd085_gInv103 1, ?_⟩
  intro e he
  have hm : e ∈ BT.D 1 BT.zero :: BT.zero :: ([] : List BT) := he
  rcases List.mem_cons.mp hm with h1 | h1
  · rw [h1]; decide
  · rw [List.mem_singleton.mp h1]; decide

theorem gInv_eq_vIter107 : ∀ n, gInv103 (n + 1) = vIter107 (gInv103 1) n
  | 0 => rfl
  | n + 1 => by
      show BT.D 0 (BT.D 1 (BT.D 1 (gInv103 (n + 1)))) = vStep107 (vIter107 (gInv103 1) n)
      rw [gInv_eq_vIter107 n]; rfl

theorem vTow_shift107 : ∀ n, vTow102 (gTow102 1) n = gTow102 (n + 1)
  | 0 => rfl
  | n + 1 => by
      show phi (vTow102 (gTow102 1) n) zero = phi (gTow102 (n + 1)) zero
      rw [vTow_shift107 n]

/-! 出発点はどこでもよい — §103.5 を任意の種へ。 -/

/-- `Γ₀` の下には `ψ` が一つも生き残らない、を種によらず。§102.4 の `hpsi_Gam0_102`
    の種を一般化したもの (証明はどの節でも矛盾に落ちるので種を使わない)。 -/
theorem hpsi_Gam0_seed107 (c : Term) : ∀ (k a : Term), inT (psi k a) = true →
    lt (psi k a) (psi (Z zero) zero) = true → ∀ m, 1 ≤ m →
    lt (psi k a) (vTow102 c m) = true := by
  intro k a hin h m _
  obtain ⟨hisR, _, _⟩ := inT_psi102 hin
  cases k with
  | zero => exact Bool.noConfusion hisR
  | M => exact Bool.noConfusion hisR
  | add _ _ => exact Bool.noConfusion hisR
  | omg _ => exact Bool.noConfusion hisR
  | phi _ _ => exact Bool.noConfusion hisR
  | psi _ _ => exact Bool.noConfusion hisR
  | Z e =>
      by_cases he : e = zero
      · subst he; rw [lt_psi_same, lt_right_zero102] at h; exact Bool.noConfusion h
      · rw [lt_psiZ_psiOm102 he] at h; exact Bool.noConfusion h

/-- **`Γ₀` の共終性は、加法主要な種ならどれでもよい。** -/
theorem cofG0_seed107 {c : Term} (hc : isAP c = true) {s : Term} (hs : inT s = true)
    (h : lt s G094 = true) : lt s (vTow102 c (htG102 s)) = true :=
  towBound102 hc (hpsi_Gam0_seed107 c) s hs
    (show lt s (psi (Z zero) zero) = true from h) (htG102 s) (Nat.le_refl _)

/-- 種が `Γ₀` より下なら塔も `Γ₀` を越えない。 -/
theorem ltG0_vTow107 {X : Term} (h : lt X G094 = true) : ∀ n, lt (vTow102 X n) G094 = true
  | 0 => h
  | n + 1 => by
      show lt (phi (vTow102 X n) zero) (psi (Z zero) zero) = true
      rw [lt_phi_psi103, show lt (vTow102 X n) (psi (Z zero) zero) = true from ltG0_vTow107 h n,
        show lt (zero : Term) (psi (Z zero) zero) = true from lt_zero_psi103 (Z zero) zero]
      rfl

/-- **§103.5 を任意の種から。**  `Γ₀` より下の像点を一つ持てば、そこから回した細かい
    塔だけで目標 `Γ₀` の密度が出る。§103 が `ψ₀0` を使ったのは一例にすぎない。 -/
theorem denseAtGam0_seed107 (Hp : PsiIdxOKStd172) {x : BT} (H : InvV107 x)
    (hg : Good103 (dict x)) (hSC : (dict x).isSC = false) (hx : lt (dict x) G094 = true)
    {s : Term} (hs : inT s = true) (hlt : lt s G094 = true) :
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
      le s (dict b) = true ∧ lt (dict b) G094 = true := by
  refine ⟨vIter107 x (htG102 s), (legal_vIter107 H _).1, (legal_vIter107 H _).2.1,
    (legal_vIter107 H _).2.2, ?_, ?_⟩
  · rw [dict_vIter107 Hp H hg hSC]
    exact le_of_lt (cofG0_seed107 hg.2.1 hs hlt)
  · rw [dict_vIter107 Hp H hg hSC]
    exact ltG0_vTow107 hx _

end

/-! ### §107.4 そして `Γ₀` で止まる — 値の側と標準性の側から -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP)
open TM TM.Term
open Evidence.WF

/-- **`SC` の頭では `φ̄(·,0)` は恒等写像。**  2.6(vi) の既定枝がそこで発火する。 -/
theorem phiNF_sc_zero107 {X : Term} (h : X.isSC = true) : phiNF X zero = X := by
  unfold phiNF
  rw [show ((zero : Term).isSC && lt X zero) = false from rfl]
  show phiNFsucc X zero = X
  unfold phiNFsucc
  rw [show splitFin (zero : Term) = (zero, 0) from rfl]
  show phiNFdefault X zero = X
  unfold phiNFdefault
  rw [if_pos (by rw [show ((zero : Term) == zero) = true from rfl, Bool.true_and, h])]

/-- `Γ₀` はそのひとつ。 -/
theorem phiNF_G0_zero107 : phiNF G094 zero = G094 := phiNF_sc_zero107 rfl

theorem good103_G0_107 : Good103 G094 := ⟨by decide, rfl, rfl, by decide, by decide⟩

/-- **§103.3 の畳み込みを `SC` の頭で。**  Veblen 枝は通るが値は動かない。 -/
theorem collapse0_Q_sc107 {X : Term} (h : Good103 X) (hSC : X.isSC = true) :
    collapse 0 (Q98 X) = X := by
  have hltP : lt (P98 X) (reg 1) = false := ltW_P103 X
  have hltQ : lt (Q98 X) (reg 1) = false := ltW_Q103 X
  have hwA : wA (reg 1) (Q98 X) = X := by
    show ofList (((toList (logOm (Q98 X))).filter (fun q => !lt q (reg 1))).map
      (divAP (reg 1))) = _
    rw [show logOm (Q98 X) = P98 X from rfl,
      show toList (P98 X) = [P98 X] from rfl,
      List.filter_cons_of_pos (by rw [hltP]; rfl)]
    show ofList [divAP (reg 1) (P98 X)] = X
    show omegaNF (subAP (reg 1) (logOm (P98 X))) = X
    rw [show logOm (P98 X) = add (reg 1) X from by
        show (if phiShifted zero (add (reg 1) X) then _ else _) = _
        rw [show phiShifted zero (add (reg 1) X) = false from by
          show (isFP zero (splitFin (add (reg 1) X)).1 ||
            ((add (reg 1) X == zero) && (zero : Term).isSC)) = false
          rw [splitFin_addWX103 h]
          rfl]
        rfl,
      show subAP (reg 1) (add (reg 1) X) = X from by
        show (match toList (add (reg 1) X) with
              | [] => zero
              | p :: rest => if p == reg 1 then ofList rest else add (reg 1) X) = _
        rw [show toList (add (reg 1) X) = [reg 1, X] from by
              show reg 1 :: toList X = _; rw [good_toList103 h]]
        show (if (reg 1 == reg 1) = true then ofList [X] else _) = X
        rw [if_pos (by rfl)]
        rfl]
    exact h.2.2.2.1
  have hwC : wC (reg 1) (Q98 X) = TM.Term.one := by
    show omegaNF (ofList ((toList (logOm (Q98 X))).filter (fun q => lt q (reg 1)))) = _
    rw [show logOm (Q98 X) = P98 X from rfl,
      show toList (P98 X) = [P98 X] from rfl,
      List.filter_cons_of_neg (by rw [hltP]; exact Bool.noConfusion)]
    rfl
  have hw : wcnf (reg 1) (toList (Q98 X)) = ([(X, TM.Term.one)], zero) := by
    rw [show toList (Q98 X) = [Q98 X] from rfl, wcnf_cons_ge hltQ, wcnf_nil]
    show ([(wA (reg 1) (Q98 X), wC (reg 1) (Q98 X))], (zero : Term)) = _
    rw [hwA, hwC]
  have hfold : ([(X, TM.Term.one)].foldl
      (init := ((none : Option Term), (none : Option Term)))
      (stepF (reg 1) (baseOf 0))).2.getD zero = X := by
    show (stepF (reg 1) (baseOf 0) (none, none) (X, TM.Term.one)).2.getD zero = _
    show (if le (reg 1) X = true then _ else
      ((none : Option Term), some (phiNF X zero))).2.getD zero = _
    rw [if_neg (by rw [le_W_false103 h]; exact Bool.noConfusion)]
    exact phiNF_sc_zero107 hSC
  rw [collapse0_raw89]
  show omegaNF (plus (reg 0) (plus
    (((wcnf (reg 1) (toList (Q98 X))).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero)
    ((wcnf (reg 1) (toList (Q98 X))).2))) = _
  rw [hw]
  show omegaNF (plus (reg 0) (plus
    (([(X, TM.Term.one)].foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero) zero)) = _
  rw [hfold]
  show omegaNF (plus (reg 0) (plus X zero)) = _
  rw [show plus X zero = X from rfl, show plus (reg 0) X = plus zero X from rfl,
    plus_zero_left_inT h.1]
  exact h.2.2.2.1

/-- **§107.4 の主定理 (1) — 値の側。**  値が `SC` のところでは細かい作用素は
    何も動かさない。とくに `Γ₀` のところで値は `Γ₀` のまま — §94.6 の生の塔の
    第 1 段 `φ̄(Γ₀,0)` は「`Γ₀` の一段上」ではなく、この作用素では作れない。 -/
theorem dict_vStep_sc107 (Hp : PsiIdxOKStd172) {x : BT} (hb : btLe72 1 x = true)
    (hs : BT.isStd x = true) (hd : Hd085 x) (hg : Good103 (dict x))
    (hSC : (dict x).isSC = true) : dict (vStep107 x) = dict x := by
  show collapse 0 (dict (BT.D 1 (BT.D 1 x))) = dict x
  rw [dict_D1D1x103 Hp hb hs hd hg, collapse0_Q_sc107 hg hSC]

/-- `Γ₀` そのものでの実例。 -/
theorem dict_vStep_G0_107 (Hp : PsiIdxOKStd172) {x : BT} (hb : btLe72 1 x = true)
    (hs : BT.isStd x = true) (hd : Hd085 x) (hv : dict x = G094) :
    dict (vStep107 x) = G094 := by
  rw [dict_vStep_sc107 Hp hb hs hd (by rw [hv]; exact good103_G0_107)
    (by rw [hv]; rfl), hv]

/-- `Ω^Ω` は、頭が `D 0` の項の `ψ₁ψ₁` より上にいる — §98 の `lt_D1D1_bOO98` の
    読み替えで、これが細かい作用素の天井である。 -/
theorem lt_D1D1_bArg107 (x : BT) :
    BT.lt (BT.D 1 (BT.D 1 (bStep98 x))) (bArg98 x) = true :=
  lt_trans83 (lt_D1D1_bOO98 (hd0_bStep98 x)) (btlt_self_sum98 1 (BT.D 1 x))

/-- **§107.4 の主定理 (2) — 標準性の側。**  細かい作用素は §98 の段の上では
    不変量を満たせない。`bArg98 x` は `GB 0 (bStep98 x)` の元でありながら
    `ψ₁ψ₁(bStep98 x)` より上にいるからで、`x` に条件は要らない。 -/
theorem invV_bStep_false107 (x : BT) : ¬ InvV107 (bStep98 x) := by
  intro H
  have h4 := H.2.2.2 (bArg98 x) (by rw [gb0_bStep98]; exact List.Mem.head _)
  rw [lt_asymm74 (lt_D1D1_bArg107 x)] at h4
  exact Bool.noConfusion h4

/-- **そして実際に標準性が壊れる。**  二つの作用素は決して合成できない。 -/
theorem vStep_bStep_not_std107 (x : BT) : BT.isStd (vStep107 (bStep98 x)) = false := by
  cases h : BT.isStd (vStep107 (bStep98 x)) with
  | false => rfl
  | true =>
      exfalso
      have h' : (BT.isStd (BT.D 1 (BT.D 1 (bStep98 x))) &&
          (BT.GB 0 (BT.D 1 (BT.D 1 (bStep98 x)))).all
            (fun e => BT.lt e (BT.D 1 (BT.D 1 (bStep98 x))))) = true := h
      have hall := (Bool.and_eq_true _ _).mp h'
      rw [List.all_eq_true] at hall
      have hm : bArg98 x ∈ BT.GB 0 (BT.D 1 (BT.D 1 (bStep98 x))) := by
        show bArg98 x ∈ BT.D 1 (bStep98 x) :: bStep98 x :: BT.GB 0 (bStep98 x)
        refine List.Mem.tail _ (List.Mem.tail _ ?_)
        rw [gb0_bStep98]; exact List.Mem.head _
      have hx := hall.2 (bArg98 x) hm
      rw [lt_asymm74 (lt_D1D1_bArg107 x)] at hx
      exact Bool.noConfusion hx

/-- §98 の塔の各段に当てた形 — 段は正しい証人だが、細かい作用素は標準性を壊す。 -/
theorem vStep_bTowG_not_std107 (n : Nat) :
    BT.isStd (bTowG98 (n + 1)) = true ∧ BT.isStd (vStep107 (bTowG98 (n + 1))) = false :=
  ⟨(legal_bTowG98 (n + 1)).2.1, vStep_bStep_not_std107 (bTowG98 n)⟩

/-- **不変量は係数を `Ω^Ω` の下に閉じ込める。**  `e ∈ GB 0 x` はどれも `ψ₁ψ₁ x` より
    下、そして §98 の `lt_D1D1_bOO98` により `ψ₁ψ₁ x` は `Ω^Ω` より下だからである。
    `Γ₀ = ψ₀(Ω^Ω)` に届くには引数に `Ω^Ω` が要るので、これがそのまま天井になる。 -/
theorem invV_needs_ltOO107 {x : BT} (H : InvV107 x) :
    ∀ e ∈ BT.GB 0 x, BT.lt e bOO94 = true := by
  intro e he
  exact lt_trans83 (H.2.2.2 e he) (lt_D1D1_bOO98 H.2.2.1)

/-- **そして `Γ₀` 自身の証人で、もう不変量は破れている。**  `Γ₀ = ψ₀(Ω^Ω)` の
    係数集合は `Ω^Ω` を含む。細かい作用素は `Γ₀` から一歩も出られない。 -/
theorem invV_bG0_false107 : ¬ InvV107 (BT.D 0 bOO94) := by
  intro H
  have h := invV_needs_ltOO107 H bOO94 (by
    show bOO94 ∈ bOO94 :: BT.GB 0 bOO94
    exact List.Mem.head _)
  have hne := bt_ne_of_lt98 h
  rw [bt_beq_refl bOO94] at hne
  exact Bool.noConfusion hne

end

/-! ### §107.5 (b2) の正体 — 作用素が足りないのではなく、そこに像がない -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg)
open TM TM.Term
open Evidence.WF

/-- `bOnto85` の証人を名指しで取り出したもの — 計算事実 (`kindB` が極限であること) を
    使うために存在量化を外す必要がある。 -/
theorem stdB1_bInv107 (b : BT) (hb : btLe72 1 b = true) (hs : BT.isStd b = true)
    (hd : Hd085 b) : stdB1 (bInv85 b) = true := by
  obtain ⟨h1, h2⟩ := std_bInv85 (b.size + 1) b (Nat.lt_succ_self _) hb hs
  show ((nfB (bInv85 b) && nonIncr (bInv85 b) && stdIn (bInv85 b)) && lvlLe 1 (bInv85 b)) = true
  rw [nfB_bInv85 b hb hd, h1, h2, lvlLe_bInv85 b hb]
  rfl

/-- **隙間の上端に対応する行列。**  §98 の塔の第 1 段の逆像で、部分領域の標準な
    極限の添字である — 三つとも計算で確かめる。 -/
def tGap107 : B := bInv85 (bTowG98 1)

theorem stdB1_tGap107 : stdB1 tGap107 = true :=
  stdB1_bInv107 (bTowG98 1) (legal_bTowG98 1).1 (legal_bTowG98 1).2.1 (legal_bTowG98 1).2.2
theorem kind_tGap107 : kindB tGap107 = BMS.Kind.lim := rfl
theorem bVal_tGap107 : bValA71 tGap107 = bTowG98 1 := rfl
theorem mat_tGap107 : matB tGap107 0 =
    [[0,0],[1,1],[2,1],[3,1],[1,1],[2,1],[3,0],[4,1],[5,1],[6,1]] := rfl

theorem vOf_tGap107 (Hp : PsiIdxOKStd172) : vOf tGap107 = dict (bTowG98 1) := by
  rw [vOfIsDict76 Hp tGap107 stdB1_tGap107, bVal_tGap107]

/-- `Γ₀ < φ̄(Γ₀,0)` — 生の塔の第 1 段は `Γ₀` の真上にいる。 -/
theorem lt_G0_rawT0_107 : lt G094 (rawT94 0) = true :=
  lt_psi_phi_of_le_fst102 (le_self G094)

theorem lt_E81_G0_107 : lt E081 G094 = true := lt_E81_sc rfl

theorem lt_E81_rawT0_107 : lt E081 (rawT94 0) = true :=
  lt_trans_inT inT_E81 inT_G094_102 (inT_rawT98 0) lt_E81_G0_107 lt_G0_rawT0_107

theorem lt_G0_bTowG1_107 (H2 : DictLtA74) : lt G094 (dict (bTowG98 1)) = true := by
  have h := lt_dict98 H2 (legal_bTowG98 0).1 (legal_bTowG98 0).2.1 (legal_bTowG98 0).2.2
    (legal_bTowG98 1).1 (legal_bTowG98 1).2.1 (legal_bTowG98 1).2.2 (lt_bTowG98 0)
  rw [dict_bTowG98_zero] at h; exact h

/-- **測っただけで、証明していない条項。**  `Γ₀` の上で `dict` の像は
    `φ̄(Γ₀,0)` (§94.6 の生の塔の第 1 段) と `φ̄(Γ₀,Γ₀⊕1)` (§98 の塔の第 1 段) の
    あいだに**一つもない**という主張。理由は §107 の前文にある — 強臨界枝が先に
    発火するので、以後の Veblen 桁の第 2 引数は必ず `Γ₀ ⊕ c` (`c ≥ 1`) になる。
    §107.7 で 1655 項と 88 項の二つの母集団で外れ 0。**証明しない。** -/
def GapAtG0_107 : Prop := ∀ b : BT, btLe72 1 b = true → BT.isStd b = true → Hd085 b →
    le (rawT94 0) (dict b) = true → le (dict (bTowG98 1)) (dict b) = true

theorem gap_contra107 (Hp : PsiIdxOKStd172) {b : BT} (hb : btLe72 1 b = true)
    (hst : BT.isStd b = true) (hlt : lt (dict b) (dict (bTowG98 1)) = true)
    (hge : le (dict (bTowG98 1)) (dict b) = true) : False := by
  have hib := (inT_dict_of_std172 Hp b hb hst).1
  have hiv := (inT_dict_of_std172 Hp _ (legal_bTowG98 1).1 (legal_bTowG98 1).2.1).1
  rcases (Bool.or_eq_true _ _).mp hge with h | h
  · rw [← eq_of_beq h, lt_irrefl] at hlt; exact Bool.noConfusion hlt
  · rw [lt_asymm_inT hiv hib h] at hlt; exact Bool.noConfusion hlt

/-- **§107.5 の主定理 (1)。**  隙間があれば §107.2 の直した (b2) も偽である
    — 目標を像に限っても救えない。 -/
theorem denseMid107_false_of_gap107 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (HG : GapAtG0_107) : ¬ DictDenseMid107 := by
  intro H
  obtain ⟨b, hb, hst, hd, hle, hlt⟩ :=
    H (bTowG98 1) (legal_bTowG98 1).1 (legal_bTowG98 1).2.1 (legal_bTowG98 1).2.2
      (lt_G0_bTowG1_107 H2) (lt_bTowG_Gam98 H2 1)
      (rawT94 0) (inT_rawT98 0) (lt_rawT_bTowG98 Hp H2 0)
  exact gap_contra107 Hp hb hst hlt (HG b hb hst hd hle)

/-- **§107.5 の主定理 (2)。**  §102 のもとの (b2) も偽。 -/
theorem denseMid102_false_of_gap107 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (HG : GapAtG0_107) : ¬ DictDenseMid102 := fun H =>
  denseMid107_false_of_gap107 Hp H2 HG (mid107_of_mid102 Hp H)

/-- **§107.5 の主定理 (3)。**  そして密度の門そのものが偽になる。挑戦者は
    §94.6 の生の塔の第 1 段、目標は §98 の塔の第 1 段の値である。 -/
theorem dictDenseHi94_false_of_gap107 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (HG : GapAtG0_107) : ¬ DictDenseHi94 := by
  intro H
  have hv := vOf_tGap107 Hp
  have hiV : inT (dict (bTowG98 1)) = true :=
    (inT_dict_of_std172 Hp _ (legal_bTowG98 1).1 (legal_bTowG98 1).2.1).1
  have hEv : lt E081 (vOf tGap107) = true := by
    rw [hv]
    exact lt_trans_inT inT_E81 inT_G094_102 hiV lt_E81_G0_107 (lt_G0_bTowG1_107 H2)
  have hsv : lt (rawT94 0) (vOf tGap107) = true := by
    rw [hv]; exact lt_rawT_bTowG98 Hp H2 0
  obtain ⟨b, hb, hst, hd, hle, hlt⟩ :=
    H tGap107 stdB1_tGap107 kind_tGap107 hEv
      (rawT94 0) (inT_rawT98 0) (le_of_lt lt_E81_rawT0_107) hsv
  rw [hv] at hlt
  exact gap_contra107 Hp hb hst hlt (HG b hb hst hd hle)

/-- **§107.5 の主定理 (4)。**  `DictDense85` — したがって §85 の同値により
    `CofDenseS1` — も偽になる。326 行目の共終性の側が乗っている条項そのものである。 -/
theorem dictDense85_false_of_gap107 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (HG : GapAtG0_107) : ¬ DictDense85 := by
  intro H
  have hv := vOf_tGap107 Hp
  have hsv : lt (rawT94 0) (vOf tGap107) = true := by
    rw [hv]; exact lt_rawT_bTowG98 Hp H2 0
  obtain ⟨b, hb, hst, hd, hle, hlt⟩ :=
    H tGap107 stdB1_tGap107 kind_tGap107 (rawT94 0) (inT_rawT98 0) hsv
  rw [hv] at hlt
  exact gap_contra107 Hp hb hst hlt (HG b hb hst hd hle)

theorem cofDenseS1_false_of_gap107 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (HG : GapAtG0_107) : ¬ CofDenseS1 := fun H =>
  dictDense85_false_of_gap107 Hp H2 HG (dictDense85_of_cofDenseS1 Hp H)

end

/-! ### §107.6 段の正直さ -/

section
open Trans.Recal
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

/-- **細かい構成も段 1 を超えない。**  §85.6 が条項を反証する段 2 へは一歩も行かない。 -/
theorem btLe1_vIter107 {x : BT} (H : InvV107 x) (n : Nat) :
    btLe72 1 (vIter107 x n) = true := (legal_vIter107 H n).1

/-- **そして段 0 は一段目で離れる。**  §97 の `btLe0_invE97`、§98 の `btLe0_bTowG98`、
    §103 の `btLe0_gInv103` と同じ規律。 -/
theorem btLe0_vStep107 (x : BT) : btLe72 0 (vStep107 x) = false := rfl

theorem btLe0_vIter107 (x : BT) (n : Nat) : btLe72 0 (vIter107 x (n + 1)) = false := rfl

end

/-! ### §107.7 測定 (凍結)

**構成を先に書く。**  母集団は二つ、どちらも「正しい証人」だけで濾してあるが
**仮説では濾していない**。A は §94.7 の `pool94` を 4 つおきに間引いたものに §98 の塔と
§94.6 の手作りの族を足し、そこへ一段だけ閉包をかける — §98 の段、§107 の細かい段、
自分との和、そして `Ω^Ω` を前置した三つの形 (`ψ₁·`、`ψ₁ψ₁·` を二つ並べたもの、
`Ω^Ω` を二つ並べたもの)。B は小さい代わりに**窓に入りうる形だけ**を種にした
意地の悪いもの — Veblen の桁を二つ持つ形、`Ω^Ω` を重ねた形、`ψ₁` の中に和を入れた形。

**仮説が母集団に見えていること**が肝心である (§93 の教訓)。`φ̄(Γ₀,0) ≤ dict b` は
A の 163 項・B の 58 項で成り立つので、外れ 0 は空振りではない。 -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg)
open TM TM.Term
open Evidence.WF

/-- 窓の上端 — §98 の塔の第 1 段の値 `φ̄(Γ₀, Γ₀⊕1)`。 -/
def V1_107 : Term := dict (bTowG98 1)

def seedA107 : List BT :=
  everyB94 4 pool94 ++ (List.range 4).map bTowG98 ++ (List.range 3).map bWitT94
def growA107 (p : List BT) : List BT :=
  (p ++ p.map bStep98 ++ p.map vStep107 ++ p.map (fun x => BT.sum x x)
     ++ p.map (fun x => BT.D 0 (BT.sum bOO94 (BT.D 1 x)))
     ++ p.map (fun x => BT.D 0 (BT.sum bOO94 (BT.sum (BT.D 1 (BT.D 1 x)) (BT.D 1 (BT.D 1 x)))))
     ++ p.map (fun x => BT.D 0 (BT.sum bOO94 (BT.sum bOO94 (BT.D 1 (BT.D 1 x)))))).eraseDups
def popA107 : List BT := (growA107 seedA107).filter bgood94
def valA107 : List Term := popA107.map dict

def seedB107 : List BT :=
  [BT.zero, BT.D 0 BT.zero, BT.Om 1, bOO94, BT.D 0 bOO94, bTowG98 1, bTowG98 2,
   BT.D 0 (BT.D 1 (BT.Om 1)), BT.D 0 (BT.D 1 (BT.D 1 (BT.Om 1)))]
def growB107 (p : List BT) : List BT :=
  (p ++ (p.flatMap fun x => p.map fun y =>
        BT.D 0 (BT.sum bOO94 (BT.sum (BT.D 1 (BT.D 1 x)) (BT.D 1 (BT.D 1 y)))))
     ++ (p.flatMap fun x => p.map fun y =>
        BT.D 0 (BT.sum bOO94 (BT.D 1 (BT.sum (BT.D 1 x) y))))
     ++ (p.map fun x => BT.D 0 (BT.sum bOO94 (BT.sum bOO94 (BT.D 1 (BT.D 1 x)))))
     ++ (p.map fun x => BT.D 0 (BT.sum (BT.D 1 (BT.D 1 (BT.D 1 (BT.Om 1)))) (BT.D 1 (BT.D 1 x))))
     ++ (p.map vStep107)
     ++ (p.flatMap fun x => p.map fun y => BT.sum x y)).eraseDups
def popB107 : List BT := (growB107 seedB107).filter bgood94
def valB107 : List Term := popB107.map dict

#eval (popA107.length, popB107.length)
#guard popA107.length == 570
#guard popB107.length == 88

/-! **隙間はぴったり。**  `[rawT94 n, dict (bTowG98 (n+1)))` に入る値は、
    どちらの母集団でも、三つの段のどれでも 0。 -/
#guard (List.range 3).all fun n =>
  valA107.countP (fun d => le (rawT94 n) d && lt d (dict (bTowG98 (n + 1)))) == 0
#guard (List.range 3).all fun n =>
  valB107.countP (fun d => le (rawT94 n) d && lt d (dict (bTowG98 (n + 1)))) == 0

/-! **仮説は見えている。**  `GapAtG0_107` の前提が成り立つ項の数。0 なら空振りである。 -/
#eval (valA107.countP fun d => le (rawT94 0) d, valB107.countP fun d => le (rawT94 0) d)
#guard (valA107.countP fun d => le (rawT94 0) d) == 163
#guard (valB107.countP fun d => le (rawT94 0) d) == 58

/-! **`[Γ₀, Γ₁)` は 246 + 0 + 31 に割れる** — 生の段より下、窓の中、§98 の段より上。 -/
#eval (valA107.countP (fun d => le G094 d && lt d (rawT94 0)),
       valA107.countP (fun d => le (rawT94 0) d && lt d V1_107),
       valA107.countP (fun d => le V1_107 d && lt d Gam1_94),
       valA107.countP (fun d => le G094 d && lt d Gam1_94))
#guard (valA107.countP fun d => le G094 d && lt d (rawT94 0)) == 246
#guard (valA107.countP fun d => le V1_107 d && lt d Gam1_94) == 31
#guard (valA107.countP fun d => le G094 d && lt d Gam1_94) == 277

/-! **窓は項では埋まっている。**  §94.7 自身の 221 の挑戦者のうち 25 がそこにいて、
    どれも証人を持てない — §94.7 がそれを見逃したのは、目標の側が窓まで届いて
    いなかったからである。 -/
#eval chal94.countP fun s => inT s && le (rawT94 0) s && lt s V1_107
#guard (chal94.countP fun s => inT s && le (rawT94 0) s && lt s V1_107) == 25
#guard [phi G094 TM.Term.one, phi G094 TM.Term.omega, phi G094 E081, phi G094 G094,
        rawT94 0].all fun s => inT s && le (rawT94 0) s && lt s V1_107

/-! **対照 — `Γ₀` より下に隙間はない。**  §102.4 の塔の段のあいだはどこも像で埋まって
    いる。だから §103 の側は証明の問題で、こちらはそうではない。 -/
#eval (List.range 4).map fun n =>
  valA107.countP fun d => le (gTow102 n) d && lt d (gTow102 (n + 1))
#guard (List.range 4).all fun n =>
  (valA107.countP fun d => le (gTow102 n) d && lt d (gTow102 (n + 1))) > 0

/-! **端点。**  生の塔はどの段も `dict` の像に入らず、`bTowG98 1` は正しい証人で、
    その値は生の第 1 段より上にある。 -/
#guard (List.range 8).all fun n => inT (rawT94 n) && (dictInv (rawT94 n)).isNone
#guard bgood94 (bTowG98 1) && lt (rawT94 0) V1_107 && lt V1_107 Gam1_94

/-! **細かい作用素、計算。**  §103.4 の塔はこの作用素の一例で、値は §102.4 の塔、
    段は 1 以下、1 段目から上は段 0 では書けない。 -/
#guard (List.range 8).all fun n =>
  bgood94 (vIter107 (gInv103 1) n) && (dict (vIter107 (gInv103 1) n) == gTow102 (n + 1))
#guard (List.range 8).all fun n => btLe72 0 (vIter107 (gInv103 1) (n + 1)) == false

/-! **そして `Γ₀` で止まる、二通りに。**  値は動かず (`φ̄(Γ₀,0) = Γ₀` を畳み込みが返す)、
    標準性は `Γ₀` 自身の証人のところですでに壊れている。§98 の段の上でも同じ。 -/
#guard (phiNF G094 zero == G094) && (dict (vStep107 (BT.D 0 bOO94)) == G094)
#guard bgood94 (BT.D 0 bOO94) && (BT.isStd (vStep107 (BT.D 0 bOO94)) == false)
#guard (List.range 4).all fun n =>
  bgood94 (bTowG98 (n + 1)) && (BT.isStd (vStep107 (bTowG98 (n + 1))) == false)

end

/-! ## §106 THE FIRST VEBLEN ARGUMENT IS FREE — ONE PAIR OF THE FOLD, INVERTED IN GENERAL

§103 closed the ENDPOINT of §102's (b1) — the single target `Γ₀` — by BUILDING the Buchholz
preimage of §102.4's tower and proving it is one, and it named exactly what was left: the
OPEN interval `(ε₀, Γ₀)`, whose general case is a mutual recursion (digits + term) "whose
value half needs `wcnf ∘ xOf = id` and whose standardness half cannot use §94.5's
`btlt_of_lt94` at all — that lemma requires `Hd085` on both sides and the arguments this
construction has to compare are `ψ₁`-headed."

**§106 builds that mutual recursion and proves both halves — for ONE pair of the fold.**
`DictOntoMidOpen103` is NOT closed.  What is closed is the half §103 could not even state:
the FIRST Veblen argument.  §103.3's `collapse0_Q103` inverts the `ψ₀` fold at one base-`Ω₁`
pair only when the exponent is an ε-number in `Good103`, which is why §103's tower is the
single chain `φ̄(φ̄(…,0),0)` and nothing else.  §106.3's `collapse0_argV106` inverts it at one
pair with **no condition on the exponent at all**, and §106.4/§106.5 build the Buchholz
witness for the coefficient `1` and prove it legal — by an induction that carries its own
covering condition, since `btlt_of_lt94` really is out of reach.

  §106.1  **THE ROUND TRIP `wcnf` NEEDS.**  `logOm_omegaNF106 : logOm (ω^Y) = Y` for every
          term of 𝔗(M) below `M` — §100.2's `omegaNF_logOm100` read backwards, and only the
          forward direction was in the repository.  The proof is three lines and not a case
          analysis over `phiNF`'s five branches: `ω^·` is strictly monotone on 𝔗(M) (§79's
          `lt_omegaNF_inT79`), hence injective, and `ω^(log(ω^Y)) = ω^Y` then forces
          `log(ω^Y) = Y` by §8's trichotomy.  This is "`wcnf ∘ xOf = id`" in its smallest
          form.  `ltW_omegaNF106` is the side fact that `ω^·` does not fall below `Ω₁`.

  §106.2  **`divAP Ω₁` INVERTS `Ω₁ ·`, COMPONENT BY COMPONENT.**  `divAP_dig106` and
          `divAP_mulL106` : `ofList ((toList (Ω₁·A)).map (divAP Ω₁)) = A` for every `A` of
          𝔗(M) below `Ω₁`.  Nothing here mentions `dict`; it is the arithmetic of `mulL`,
          and it is what makes the digit half of the recursion one step rather than an
          induction.

  §106.3  **ONE PAIR, INVERTED IN GENERAL.**  `collapse0_one_pair106` reduces `collapse 0 V`
          for an additively principal `V ≥ Ω₁` to a single Veblen step with the exponent,
          the coefficient and the result all free — the modular form §103.3 did not have.
          `collapse0_argV106` : `ψ₀(Ω₁^A·c) = φ̄(A,B)` for the argument
          `argV106 A B = ω^(Ω₁·A ⊕ log B)`.  Two corollaries pin the two shapes the
          coefficient can take: `collapse0_mulL106` (`B = 0`, coefficient `1`) — **which is
          `collapse0_Q103` with its whole `Good103` hypothesis deleted** — and
          `collapse0_argAP106` (`B` additively principal and `≠ 1`, coefficient `B`).

  §106.4  **THE DIGITS, AND WHY THEY ARE LEGAL.**  `mulB106` lays the digits of `Ω₁·A` side
          by side as `ψ₁`-nodes, `powB106` and `vebB106` put `ψ₁` and `ψ₀` on top.  Legality
          is proved, not measured: `btLe_vebB106`, `isStd_vebB106`, `hd085_vebB106`, and the
          covering condition `cov_vebB106` that makes the construction ITERABLE — §103.4's
          `cov103` generalised from a chain to a list.  `Dig106` is the invariant the
          induction carries and `dig_zero106` starts it.  **`btlt_of_lt94` is not used
          anywhere in §106.4**, exactly as §103 predicted; what replaces it is
          `btlt_hd0_hd1_106` — a level-0-headed term is below every level-1-headed one — plus
          one `BT.le` transitivity and `btlt_of_hd106`, which says the tail of a sum is not
          read once the heads' arguments differ.

  §106.5  **THE MAIN THEOREM, AND THE STEP.**  `dict_vebB106` : `dict (vebB106 ls) =
          φ̄(1 ⊕ A, 0)` whenever `ls` is a descending list of `Dig106` witnesses whose values
          are the `logOm`s of `A`'s components.  `rch_step106` iterates it: `Rch106 s` and
          `CNV s` give `Rch106 (φ̄(1 ⊕ ω^s, 0))`.  From `0` that reaches `ε₀`, `ζ₀`,
          `φ̄(ε₀,0)`, … — §103.4's tower is the special case of a ONE-element list whose
          value is an ε-number.  `btLe0_vebB106` : the construction leaves level 0 at once,
          as §103.6's `noLevel0_inMid103` says it must, and `btLe1_vebB106` : it never goes
          above 1, so §85.6's level-two refutation stays out of reach.

  §106.6  **WHAT IT REACHES, AND WHAT IT DOES NOT.**  Two populations, neither filtered, and
          two named refutations.  The reach is stated as a number on §103.8's own adversarial
          pool and it is not a large one.

WHAT IS **NOT** CLAIMED.  **`DictOntoMidOpen103` is NOT proved and NOT refuted.**
`DictOntoMid102`, `DictDenseMid102` and `DictDenseAbove102` are untouched; `DictDenseHi94`,
`DictDense85` and `CofDenseS1` are exactly where §103 left them, and row 326 depends on the
same list as before — `certIn_t326_103` is unchanged and §106 adds no clause to it and
removes none.  `PsiIdxOKStd172` and `DictLtA74` are used, not proved (`DictLtA74` in fact is
not used at all in §106).

**Where §106 stopped, precisely, and what moved.**  §103's residue was the whole open
interval; §106's is the SECOND Veblen argument.  The fold's LATER pairs
(`acc := φ̄(a, acc ⊕ c)`) are not inverted here, and the Buchholz witness is built only for
the coefficient `1`, i.e. for the targets `φ̄(A,0)`.  On §103.8's adversarial pool `aPool103`
that is 14 of 359 terms as a BUILT witness and 171 of 359 as a proved VALUE formula; the
remaining 188 need a coefficient that is a sum, or `B = 1` — which one pair cannot express,
because the coefficient of a base-`Ω₁` digit is always additively principal and `sub1` sends
`1` to `0` — or a peel into more than one pair.  **This is a move of the residue, not a
removal of it, and the number says how far it moved.**

WHAT THE MEASUREMENT SAYS (§106.6 gives the construction).  Two populations, built on §97's
model so that the hypotheses stay VISIBLE and nothing is filtered out.

  * **The one-pair formula is exact where its hypothesis holds.**  144 `(A,B)` pairs, seeded
    with `0`, with `Γ₀` (strongly critical), with `1` (which no coefficient can be) and with
    sums; 65 satisfy the hypothesis and on all 65 `ψ₀(argV106 A B) = φ̄(A,B)`, 0 misses.
  * **The hypothesis is visible, and it is not a restatement of the conclusion.**  79 of the
    144 fail it — and 3 of those 79 satisfy the conclusion anyway.
  * **Two named refutations.**  `A = Γ₀`: `ψ₀(argV106 Γ₀ 0) = Γ₀`, NOT `φ̄(Γ₀,0)` — 2.6(vi)'s
    last line folds `φ̄(A,0)` to `A` for `A ∈ SC` and `dict` never emits the redundant term.
    `B = 1`: `ψ₀(argV106 ε₀ 1) = φ̄(ε₀,0)`, NOT `φ̄(ε₀,1)` — the coefficient is principal and
    `sub1 1 = 0`.
  * **The witness is exact where `Dig106` and the descending condition hold.**  43 lists, 21
    of them legal, and on all 21 the value, the level bound, standardness, the head condition
    AND the covering condition all hold; the other 22 are in on purpose and at least one of
    them really does produce a non-standard term.
  * **The covering condition cannot be found by enumeration — it has to be built.**  Sweeping
    289 Buchholz terms, all 19 that are standard, level ≤ 1 and `D 0`-headed also satisfy it:
    on that population the hypothesis is INVISIBLE, which is §93's failure mode.  `deep106 =
    ψ₀ψ₁ψ₁ψ₁ψ₁0` is built by hand, is standard, level ≤ 1 and `D 0`-headed, FAILS the
    covering condition, and `vebB106 [deep106]` is not standard.  §95's lesson, applied.
  * **§103.4's tower is a corollary.**  Eight rungs: `dict (vebB106 [gInv103 (n+1)]) =
    gTow102 (n+2)`, legal and `Dig106` at every rung, and level 0 at none of them.  The list
    form goes further than the chain: `φ̄(3,0)` and `φ̄(ε₀ ⊕ 1, 0)` are two-element lists and
    no chain produces them.
  * **The reach, on §103.8's own adversarial pool.**  359 terms of `(ε₀,Γ₀)`: 14 are `φ̄(A,0)`
    (the built witnesses), 171 satisfy the one-pair value hypothesis, and the value formula
    holds on all 171.  188 remain, and they are the second Veblen argument. -/

/-! ### §106.1 `logOm ∘ ω^· = id` — `wcnf` が要る往復 -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- 成分が `Ω₁` 以上の項の頭は `Ω₁` より下でない。 -/
theorem ltW_geW106 {Y : Term} (hne : Y ≠ zero)
    (hall : ∀ q ∈ toList Y, lt q (reg 1) = false) : lt Y (reg 1) = false := by
  cases Y with
  | zero => exact absurd rfl hne
  | add a b =>
      rw [lt_add_ap102 a b (show isAP (reg 1) = true from rfl)]
      exact hall a (by show a ∈ a :: toList b; exact List.Mem.head _)
  | M => exact hall M (List.Mem.head _)
  | omg x => exact hall (omg x) (List.Mem.head _)
  | phi a b => exact hall (phi a b) (List.Mem.head _)
  | psi k a => exact hall (psi k a) (List.Mem.head _)
  | Z d => exact hall (Z d) (List.Mem.head _)

theorem logOm_omegaNF106 {Y : Term} (hY : inT Y = true) (hYM : lt Y M = true) :
    logOm (omegaNF Y) = Y := by
  have hi : inT (omegaNF Y) = true := inT_omegaNF hY
  have hm : lt (omegaNF Y) M = true := ltM_omegaNF hY hYM
  have hround : omegaNF (logOm (omegaNF Y)) = omegaNF Y :=
    omegaNF_logOm100 hi (isAP_omegaNF Y) hm
  have hiL : inT (logOm (omegaNF Y)) = true := inT_logOm hi
  rcases lt_trichotomy_inT hiL hY with h | h | h
  · exfalso
    have h1 := lt_omegaNF_inT79 hiL hY h.1
    rw [hround, lt_irrefl] at h1
    exact Bool.noConfusion h1
  · exact h.2.1
  · exfalso
    have h1 := lt_omegaNF_inT79 hY hiL h.2.2
    rw [hround, lt_irrefl] at h1
    exact Bool.noConfusion h1

theorem ltW_omegaNF106 {Y : Term} (hY : inT Y = true) (hYW : lt Y (reg 1) = false) :
    lt (omegaNF Y) (reg 1) = false := by
  have hi : inT (omegaNF Y) = true := inT_omegaNF hY
  rcases lt_trichotomy_inT hY (inT_reg 1) with h | h | h
  · rw [h.1] at hYW; exact Bool.noConfusion hYW
  · rw [h.2.1, omegaNF_reg1_80, lt_irrefl]
  · have h1 := lt_omegaNF_inT79 (inT_reg 1) hY h.2.2
    rw [omegaNF_reg1_80] at h1
    exact lt_asymm_inT (inT_reg 1) hi h1


end

/-! ### §106.2 `Ω₁ ·` の逆はちょうど `divAP` -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- `Ω₁` より下の項を左から `Ω₁` で足すと、成分列は `Ω₁` を頭に置いただけ。 -/
theorem toList_plusW106 {g : Term} (hg : inT g = true)
    (hgW : ∀ q ∈ toList g, lt q (reg 1) = true) :
    toList (plus (reg 1) g) = reg 1 :: toList g := by
  cases hl : toList g with
  | nil =>
      rw [plus_nil hl]
      rfl
  | cons b1 r =>
      have hb1 : lt b1 (reg 1) = true := hgW b1 (by rw [hl]; exact List.Mem.head _)
      rw [plus_cons66 hl,
        show (toList (reg 1)).filter (fun a => le b1 a) = [reg 1] from by
          show (List.filter (fun a => le b1 a) [reg 1]) = [reg 1]
          rw [List.filter_cons_of_pos (by rw [le_of_lt94 hb1])]
          rfl]
      rw [show ([reg 1] ++ (b1 :: r)) = reg 1 :: (b1 :: r) from rfl,
        toList_ofList _ (by
          intro x hx
          rcases List.mem_cons.mp hx with h1 | h1
          · rw [h1]; rfl
          · exact inTL_isAP hg x (by rw [hl]; exact h1))]

theorem subAP_plusW106 {g : Term} (hg : inT g = true)
    (hgW : ∀ q ∈ toList g, lt q (reg 1) = true) :
    subAP (reg 1) (plus (reg 1) g) = g := by
  rw [subAP_cons (reg 1) _ (reg 1) (toList g) (toList_plusW106 hg hgW),
    if_pos (by rfl), inT_ofList_toList g hg]

/-- `Ω₁` より下の項の `logOm` も `Ω₁` より下。 -/
theorem ltW_logOm106 {p : Term} (hp : inT p = true) (hap : p.isAP = true)
    (hpM : lt p M = true) (hpW : lt p (reg 1) = true) : lt (logOm p) (reg 1) = true := by
  have hg : inT (logOm p) = true := inT_logOm hp
  have hpe : omegaNF (logOm p) = p := omegaNF_logOm100 hp hap hpM
  rcases lt_trichotomy_inT hg (inT_reg 1) with h | h | h
  · exact h.1
  · exfalso
    rw [h.2.1, omegaNF_reg1_80] at hpe
    rw [← hpe, lt_irrefl] at hpW
    exact Bool.noConfusion hpW
  · exfalso
    have h1 := lt_omegaNF_inT79 (inT_reg 1) hg h.2.2
    rw [omegaNF_reg1_80, hpe] at h1
    rw [lt_asymm_inT (inT_reg 1) hp h1] at hpW
    exact Bool.noConfusion hpW

/-- **一成分ぶんの割り算がちょうど戻る。**  `divAP Ω₁ (Ω₁ · p) = p`。 -/
theorem divAP_dig106 {p : Term} (hp : inT p = true) (hap : p.isAP = true)
    (hpM : lt p M = true) (hpW : lt p (reg 1) = true) :
    divAP (reg 1) (omegaNF (plus (reg 1) (logOm p))) = p := by
  have hg : inT (logOm p) = true := inT_logOm hp
  have hgM : lt (logOm p) M = true := ltM_logOm hp hpM
  have hgW : ∀ q ∈ toList (logOm p), lt q (reg 1) = true :=
    ltW_toList79 (logOm p) hg (ltW_logOm106 hp hap hpM hpW)
  have hY : inT (plus (reg 1) (logOm p)) = true := inT_plus (inT_reg 1) hg
  have hYM : lt (plus (reg 1) (logOm p)) M = true :=
    lt_plus_M (inT_reg 1) hg (ltM_reg 1) hgM
  show omegaNF (subAP (reg 1) (logOm (omegaNF (plus (reg 1) (logOm p))))) = p
  rw [logOm_omegaNF106 hY hYM, subAP_plusW106 hg hgW]
  exact omegaNF_logOm100 hp hap hpM

theorem ltW_plusW106 {g : Term} (hg : inT g = true) :
    lt (plus (reg 1) g) (reg 1) = false := by
  have hle : le (reg 1) (plus (reg 1) g) = true :=
    le_self_plus_ap81 (inT_reg 1) (show isAP (reg 1) = true from rfl) hg
  rcases (Bool.or_eq_true _ _).mp hle with h | h
  · rw [← eq_of_beq h]; exact lt_irrefl _
  · exact lt_asymm_inT (inT_reg 1) (inT_plus (inT_reg 1) hg) h

theorem toList_mulLW106 {A : Term} :
    toList (mulL (reg 1) A) = (toList A).map (fun p => omegaNF (plus (reg 1) (logOm p))) := by
  show toList (ofList ((toList A).map (fun p => omegaNF (plus (reg 1) (logOm p)))))
    = (toList A).map (fun p => omegaNF (plus (reg 1) (logOm p)))
  refine toList_ofList _ ?_
  intro x hx
  obtain ⟨p, _, hxp⟩ := List.mem_map.mp hx
  rw [← hxp]
  exact isAP_omegaNF _

/-- `Ω₁ · A` の成分はどれも `Ω₁` より下でない。 -/
theorem geW_mulL106 {A : Term} (hA : inT A = true) :
    ∀ q ∈ toList (mulL (reg 1) A), lt q (reg 1) = false := by
  intro q hq
  rw [toList_mulLW106] at hq
  obtain ⟨p, hp, hqp⟩ := List.mem_map.mp hq
  rw [← hqp]
  exact ltW_omegaNF106 (inT_plus (inT_reg 1) (inT_logOm (inTL_inT hA p hp)))
    (ltW_plusW106 (inT_logOm (inTL_inT hA p hp)))

/-- **`wcnf` は `Ω₁ · A` から `A` をそのまま戻す。** -/
theorem divAP_mulL106 {A : Term} (hA : inT A = true) (hAM : lt A M = true)
    (hAW : lt A (reg 1) = true) :
    ofList ((toList (mulL (reg 1) A)).map (divAP (reg 1))) = A := by
  have hpt : ∀ x ∈ toList A,
      (divAP (reg 1) ∘ fun p => omegaNF (plus (reg 1) (logOm p))) x = id x := by
    intro x hx
    exact divAP_dig106 (inTL_inT hA x hx) (inTL_isAP hA x hx)
      (ltM_toList A hA hAM x hx) (ltW_toList79 A hA hAW x hx)
  have hkey : (toList (mulL (reg 1) A)).map (divAP (reg 1)) = toList A := by
    rw [toList_mulLW106, List.map_map, List.map_congr_left hpt, List.map_id]
  rw [hkey, inT_ofList_toList A hA]


end

/-! ### §106.3 一組の畳み込み、第 1 引数も第 2 引数も一般に -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- 頭が `Ω₁` より下でなければ、項も `Ω₁` より下でない。 -/
theorem ltW_hd106 {Y q : Term} {rest : List Term} (hl : toList Y = q :: rest)
    (hq : lt q (reg 1) = false) : lt Y (reg 1) = false := by
  cases Y with
  | zero =>
      exfalso
      have h2 : ([] : List Term) = q :: rest := hl
      exact List.cons_ne_nil q rest h2.symm
  | add a b =>
      have h2 : a :: toList b = q :: rest := hl
      injection h2 with h1 _
      rw [lt_add_ap102 a b (show isAP (reg 1) = true from rfl), h1]
      exact hq
  | M =>
      have h2 : [M] = q :: rest := hl
      injection h2 with h1 _
      rw [h1]; exact hq
  | omg x =>
      have h2 : [omg x] = q :: rest := hl
      injection h2 with h1 _
      rw [h1]; exact hq
  | phi a b =>
      have h2 : [phi a b] = q :: rest := hl
      injection h2 with h1 _
      rw [h1]; exact hq
  | psi k a =>
      have h2 : [psi k a] = q :: rest := hl
      injection h2 with h1 _
      rw [h1]; exact hq
  | Z d =>
      have h2 : [Z d] = q :: rest := hl
      injection h2 with h1 _
      rw [h1]; exact hq

/-- **一組だけの畳み込み。**  `ψ₀` の引数が `Ω₁` 以上の加法主要項ひとつなら、`collapse 0`
    は `wcnf` が返す唯一の組 `(A, c)` に Veblen 枝を一度当てるだけである。§103.3 の
    `collapse0_Q103` はこの補題の `A` が ε 数・`c = 1` の場合にあたる。 -/
theorem collapse0_one_pair106 {V A c R : Term} (hVap : V.isAP = true)
    (hVW : lt V (reg 1) = false)
    (hwA : wA (reg 1) V = A) (hwC : wC (reg 1) V = c)
    (hAW : le (reg 1) A = false)
    (hiR : inT R = true) (hRnf : omegaNF R = R)
    (hacc : phiNF A (plus (baseOf 0) (sub1 c)) = R) :
    collapse 0 V = R := by
  have hw : wcnf (reg 1) (toList V) = ([(A, c)], zero) := by
    rw [toList_isAP81 hVap, wcnf_cons_ge hVW, wcnf_nil]
    show ([(wA (reg 1) V, wC (reg 1) V)], (zero : Term)) = _
    rw [hwA, hwC]
  have hfold : ([(A, c)].foldl
      (init := ((none : Option Term), (none : Option Term)))
      (stepF (reg 1) (baseOf 0))).2.getD zero = R := by
    show (stepF (reg 1) (baseOf 0) (none, none) (A, c)).2.getD zero = _
    show (if le (reg 1) A = true then _ else
      ((none : Option Term), some (phiNF A (plus (baseOf 0) (sub1 c))))).2.getD zero = _
    rw [if_neg (by rw [hAW]; exact Bool.noConfusion)]
    exact hacc
  rw [collapse0_raw89]
  show omegaNF (plus (reg 0) (plus
    (((wcnf (reg 1) (toList V)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero)
    ((wcnf (reg 1) (toList V)).2))) = _
  rw [hw]
  show omegaNF (plus (reg 0) (plus
    (([(A, c)].foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero) zero)) = _
  rw [hfold]
  show omegaNF (plus (reg 0) (plus R zero)) = _
  rw [show plus R zero = R from rfl,
    show plus (reg 0) R = plus zero R from rfl, plus_zero_left_inT hiR, hRnf]

theorem mulL_ne_zero106 {A : Term} (hAne : A ≠ zero) : mulL (reg 1) A ≠ zero := by
  intro hc
  have h1 : toList (mulL (reg 1) A) = [] := by rw [hc]; rfl
  rw [toList_mulLW106] at h1
  exact hAne (toList_eq_nil A (List.map_eq_nil_iff.mp h1))

theorem leW_false106 {A : Term} (hA : inT A = true) (hAW : lt A (reg 1) = true) :
    le (reg 1) A = false := by
  show ((reg 1 == A) || lt (reg 1) A) = false
  rw [show (reg 1 == A) = false from by
      cases hc : (reg 1 == A) with
      | false => rfl
      | true =>
          exfalso
          rw [← eq_of_beq hc, lt_irrefl] at hAW
          exact Bool.noConfusion hAW,
    lt_asymm_inT hA (inT_reg 1) hAW]
  rfl

theorem lt_of_ltW_geW106 {b q : Term} (hb : inT b = true) (hq : inT q = true)
    (h1 : lt b (reg 1) = true) (h2 : lt q (reg 1) = false) : lt b q = true := by
  rcases lt_trichotomy_inT hq (inT_reg 1) with h | h | h
  · rw [h.1] at h2; exact Bool.noConfusion h2
  · rw [h.2.1]; exact h1
  · exact lt_trans_inT hb (inT_reg 1) hq h1 h.2.2

/-- **一組の `ψ₀` 引数。**  `Ω₁^A · c` を `A` と第 2 引数 `B` から組み立てたもの。
    `B = 0` なら係数は `1`、`B` が加法主要なら係数は `B` である。 -/
def argV106 (A B : Term) : Term := omegaNF (plus (mulL (reg 1) A) (logOm B))

theorem toList_argY106 {A B : Term} (hA : inT A = true) (hB : inT B = true)
    (hgW0 : lt (logOm B) (reg 1) = true) :
    toList (plus (mulL (reg 1) A) (logOm B))
      = toList (mulL (reg 1) A) ++ toList (logOm B) := by
  have hg : inT (logOm B) = true := inT_logOm hB
  have hgW : ∀ q ∈ toList (logOm B), lt q (reg 1) = true :=
    ltW_toList79 (logOm B) hg hgW0
  have hmul : inT (mulL (reg 1) A) = true := inT_mulL mulDescInT (inT_reg 1) hA
  cases hl : toList (logOm B) with
  | nil => rw [plus_nil hl, List.append_nil]
  | cons b1 r =>
      have hb1W : lt b1 (reg 1) = true := hgW b1 (by rw [hl]; exact List.Mem.head _)
      have hb1T : inT b1 = true := inTL_inT hg b1 (by rw [hl]; exact List.Mem.head _)
      rw [plus_cons66 hl,
        show (toList (mulL (reg 1) A)).filter (fun a => le b1 a)
            = toList (mulL (reg 1) A) from by
          refine List.filter_eq_self.mpr ?_
          intro q hq
          exact le_of_lt94 (lt_of_ltW_geW106 hb1T (inTL_inT hmul q hq) hb1W
            (geW_mulL106 hA q hq)),
        toList_ofList _ (by
          intro x hx
          rcases List.mem_append.mp hx with h1 | h1
          · exact inTL_isAP hmul x h1
          · exact inTL_isAP hg x (by rw [hl]; exact h1))]

/-- **§106.3 の主定理 — 一組の Veblen 枝、第 1・第 2 引数とも一般。**
    `ψ₀(Ω₁^A · B) = φ̄(A,B)`。§103.3 は `B = 0` かつ `A` が ε 数の場合である。 -/
theorem collapse0_argV106 {A B : Term}
    (hA : inT A = true) (hAM : lt A M = true) (hAW : lt A (reg 1) = true)
    (hAne : A ≠ zero)
    (hB : inT B = true) (hBM : lt B M = true) (hgW0 : lt (logOm B) (reg 1) = true)
    (hacc : phiNF A (sub1 (omegaNF (logOm B))) = phi A B) :
    collapse 0 (argV106 A B) = phi A B := by
  have hg : inT (logOm B) = true := inT_logOm hB
  have hgM : lt (logOm B) M = true := ltM_logOm hB hBM
  have hgW : ∀ q ∈ toList (logOm B), lt q (reg 1) = true :=
    ltW_toList79 (logOm B) hg hgW0
  have hmul : inT (mulL (reg 1) A) = true := inT_mulL mulDescInT (inT_reg 1) hA
  have hmulM : lt (mulL (reg 1) A) M = true := ltM_mulL (inT_reg 1) hA (ltM_reg 1) hAM
  have hY : inT (plus (mulL (reg 1) A) (logOm B)) = true := inT_plus hmul hg
  have hYM : lt (plus (mulL (reg 1) A) (logOm B)) M = true :=
    lt_plus_M hmul hg hmulM hgM
  have hlist := toList_argY106 hA hB hgW0
  have hmulnil : toList (mulL (reg 1) A) ≠ [] := by
    intro hc
    exact mulL_ne_zero106 hAne (toList_eq_nil _ hc)
  have hYW : lt (plus (mulL (reg 1) A) (logOm B)) (reg 1) = false := by
    cases hm : toList (mulL (reg 1) A) with
    | nil => exact absurd hm hmulnil
    | cons q rest =>
        refine ltW_hd106 (q := q) (rest := rest ++ toList (logOm B)) ?_ ?_
        · rw [hlist, hm]; rfl
        · exact geW_mulL106 hA q (by rw [hm]; exact List.Mem.head _)
  have hlog : logOm (argV106 A B) = plus (mulL (reg 1) A) (logOm B) :=
    logOm_omegaNF106 hY hYM
  have hfil1 : (toList (plus (mulL (reg 1) A) (logOm B))).filter (fun q => !lt q (reg 1))
      = toList (mulL (reg 1) A) := by
    rw [hlist, List.filter_append,
      show (toList (mulL (reg 1) A)).filter (fun q => !lt q (reg 1))
          = toList (mulL (reg 1) A) from
        List.filter_eq_self.mpr (fun q hq => by rw [geW_mulL106 hA q hq]; rfl),
      show (toList (logOm B)).filter (fun q => !lt q (reg 1)) = [] from
        List.filter_eq_nil_iff.mpr (fun q hq => by rw [hgW q hq]; exact Bool.noConfusion),
      List.append_nil]
  have hfil2 : (toList (plus (mulL (reg 1) A) (logOm B))).filter (fun q => lt q (reg 1))
      = toList (logOm B) := by
    rw [hlist, List.filter_append,
      show (toList (mulL (reg 1) A)).filter (fun q => lt q (reg 1)) = [] from
        List.filter_eq_nil_iff.mpr (fun q hq => by
          rw [geW_mulL106 hA q hq]; exact Bool.noConfusion),
      show (toList (logOm B)).filter (fun q => lt q (reg 1)) = toList (logOm B) from
        List.filter_eq_self.mpr (fun q hq => hgW q hq),
      List.nil_append]
  refine collapse0_one_pair106 (V := argV106 A B) (A := A) (c := omegaNF (logOm B))
    (R := phi A B) (isAP_omegaNF _)
    (ltW_omegaNF106 hY hYW) ?_ ?_ (leW_false106 hA hAW) ?_ ?_ ?_
  · show ofList (((toList (logOm (argV106 A B))).filter
      (fun q => !lt q (reg 1))).map (divAP (reg 1))) = A
    rw [hlog, hfil1]
    exact divAP_mulL106 hA hAM hAW
  · show omegaNF (ofList ((toList (logOm (argV106 A B))).filter (fun q => lt q (reg 1))))
      = omegaNF (logOm B)
    rw [hlog, hfil2, inT_ofList_toList (logOm B) hg]
  · show inT (phi A B) = true
    show (inT A && inT B && lt A M && lt B M) = true
    rw [hA, hB, hAM, hBM]; rfl
  · exact omegaNF_phi98 (lt_zero_ne76 hAne)
  · rw [show plus (baseOf 0) (sub1 (omegaNF (logOm B)))
        = plus zero (sub1 (omegaNF (logOm B))) from rfl,
      plus_zero_left_inT (inT_sub1 (inT_omegaNF hg))]
    exact hacc


/-- `B = 0` の場合 — §103.3 の `collapse0_Q103` を `A` の条件なしに一般化したもの。 -/
theorem collapse0_mulL106 {A : Term} (hA : inT A = true) (hAM : lt A M = true)
    (hAW : lt A (reg 1) = true) (hAne : A ≠ zero) (hASC : A.isSC = false) :
    collapse 0 (omegaNF (mulL (reg 1) A)) = phi A zero := by
  have h := collapse0_argV106 hA hAM hAW hAne (show inT (zero : Term) = true from rfl)
    (show lt (zero : Term) M = true from by decide)
    (show lt (logOm (zero : Term)) (reg 1) = true from by decide)
    (by
      show phiNF A (sub1 (omegaNF (logOm (zero : Term)))) = phi A zero
      rw [show sub1 (omegaNF (logOm (zero : Term))) = zero from rfl]
      exact phiNF_zero_right103 hASC)
  rw [show argV106 A zero = omegaNF (mulL (reg 1) A) from by
    show omegaNF (plus (mulL (reg 1) A) (logOm zero)) = _
    rw [plus_nil (show toList (logOm (zero : Term)) = [] from rfl)]] at h
  exact h

/-- `B` が加法主要で `1` でない場合 — 係数がそのまま `B` になる。 -/
theorem collapse0_argAP106 {A B : Term}
    (hA : inT A = true) (hAM : lt A M = true) (hAW : lt A (reg 1) = true)
    (hAne : A ≠ zero)
    (hB : inT B = true) (hBM : lt B M = true) (hBW : lt B (reg 1) = true)
    (hBap : B.isAP = true) (hBne : (B == TM.Term.one) = false)
    (hnoskip : phiNF A B = phi A B) :
    collapse 0 (argV106 A B) = phi A B := by
  refine collapse0_argV106 hA hAM hAW hAne hB hBM
    (ltW_logOm106 hB hBap hBM hBW) ?_
  rw [show omegaNF (logOm B) = B from omegaNF_logOm100 hB hBap hBM,
    show sub1 B = B from by
      show (match toList B with
            | [] => zero
            | p :: rest => if p == TM.Term.one then ofList rest else B) = B
      rw [toList_isAP81 hBap]
      show (if (B == TM.Term.one) = true then ofList [] else B) = B
      rw [if_neg (by rw [hBne]; exact Bool.noConfusion)]]
  exact hnoskip

theorem divAP_W_W106 : divAP (reg 1) (reg 1) = TM.Term.one := rfl

theorem dig_eq_W_iff106 {p : Term} (hp : inT p = true) (hap : p.isAP = true)
    (hpM : lt p M = true) (hpW : lt p (reg 1) = true)
    (h : omegaNF (plus (reg 1) (logOm p)) = reg 1) : p = TM.Term.one := by
  have h1 := divAP_dig106 hp hap hpM hpW
  rw [h, divAP_W_W106] at h1
  exact h1.symm

theorem le_dig_W106 {p : Term} (hp : inT p = true) (hap : p.isAP = true)
    (hpM : lt p M = true) (hpW : lt p (reg 1) = true) :
    le (omegaNF (plus (reg 1) (logOm p))) (reg 1) = le p TM.Term.one := by
  have hpz : p ≠ zero := by intro hz; rw [hz] at hap; exact Bool.noConfusion hap
  have hlt1 : lt p TM.Term.one = false := by
    cases hc : lt p TM.Term.one with
    | false => rfl
    | true => exact absurd (below_one p hp (fuelOf p TM.Term.one) hc) hpz
  have hlt2 : lt (omegaNF (plus (reg 1) (logOm p))) (reg 1) = false :=
    ltW_omegaNF106 (inT_plus (inT_reg 1) (inT_logOm hp)) (ltW_plusW106 (inT_logOm hp))
  show ((omegaNF (plus (reg 1) (logOm p)) == reg 1) || _) = ((p == TM.Term.one) || _)
  rw [hlt1, hlt2, Bool.or_false, Bool.or_false]
  cases hc : (omegaNF (plus (reg 1) (logOm p)) == reg 1) with
  | true => rw [dig_eq_W_iff106 hp hap hpM hpW (eq_of_beq hc)]; rfl
  | false =>
      cases hd : (p == TM.Term.one) with
      | false => rfl
      | true =>
          exfalso
          rw [eq_of_beq hd] at hc
          rw [show omegaNF (plus (reg 1) (logOm TM.Term.one)) = reg 1 from rfl] at hc
          rw [show (reg 1 == reg 1) = true from rfl] at hc
          exact Bool.noConfusion hc

/-- **`Ω₁ + Ω₁·A = Ω₁·(1+A)`。**  §106.2 の主定理を `ψ₁` の像に載せるための橋。 -/
theorem plus_one_mulL106 {A : Term} (hA : inT A = true) (hAM : lt A M = true)
    (hAW : lt A (reg 1) = true) :
    plus (reg 1) (mulL (reg 1) A) = mulL (reg 1) (plus TM.Term.one A) := by
  cases hl : toList A with
  | nil =>
      rw [show A = zero from toList_eq_nil A hl]
      rfl
  | cons b1 r =>
      have hib1 : inT b1 = true := inTL_inT hA b1 (by rw [hl]; exact List.Mem.head _)
      have hab1 : b1.isAP = true := inTL_isAP hA b1 (by rw [hl]; exact List.Mem.head _)
      have hMb1 : lt b1 M = true := ltM_toList A hA hAM b1 (by rw [hl]; exact List.Mem.head _)
      have hWb1 : lt b1 (reg 1) = true := ltW_toList79 A hA hAW b1 (by rw [hl]; exact List.Mem.head _)
      have hmul : toList (mulL (reg 1) A)
          = (fun p => omegaNF (plus (reg 1) (logOm p))) b1
            :: r.map (fun p => omegaNF (plus (reg 1) (logOm p))) := by
        rw [toList_mulLW106, hl]; rfl
      have hone : toList (plus TM.Term.one A)
          = ([TM.Term.one].filter (fun a => le b1 a)) ++ (b1 :: r) := by
        rw [plus_cons66 hl]
        refine toList_ofList _ ?_
        intro x hx
        rcases List.mem_append.mp hx with h1 | h1
        · rw [List.mem_singleton.mp (List.mem_filter.mp h1).1]; rfl
        · exact inTL_isAP hA x (by rw [hl]; exact h1)
      show plus (reg 1) (mulL (reg 1) A)
        = ofList ((toList (plus TM.Term.one A)).map (fun p => omegaNF (plus (reg 1) (logOm p))))
      rw [plus_cons66 hmul, hone,
        show (toList (reg 1)).filter
            (fun a => le ((fun p => omegaNF (plus (reg 1) (logOm p))) b1) a)
          = ([TM.Term.one].filter (fun a => le b1 a)).map
              (fun p => omegaNF (plus (reg 1) (logOm p))) from by
          show (List.filter (fun a => le (omegaNF (plus (reg 1) (logOm b1))) a) [reg 1])
            = (List.filter (fun a => le b1 a) [TM.Term.one]).map _
          cases hc : le b1 TM.Term.one with
          | true =>
              rw [List.filter_cons_of_pos (by rw [show le (omegaNF (plus (reg 1) (logOm b1))) (reg 1) = true from by
                    rw [le_dig_W106 hib1 hab1 hMb1 hWb1, hc]]),
                List.filter_cons_of_pos (by rw [hc])]
              rw [show TM.Term.one = TM.Term.one from rfl]
              show [reg 1] = [omegaNF (plus (reg 1) (logOm TM.Term.one))]
              rfl
          | false =>
              rw [List.filter_cons_of_neg (by
                    rw [show le (omegaNF (plus (reg 1) (logOm b1))) (reg 1) = false from by
                      rw [le_dig_W106 hib1 hab1 hMb1 hWb1, hc]]
                    exact Bool.noConfusion),
                List.filter_cons_of_neg (by rw [hc]; exact Bool.noConfusion)]
              rfl,
        List.map_append]
      rfl

theorem inT_one106 : inT TM.Term.one = true := by decide
theorem ltM_one106 : lt TM.Term.one M = true := by decide
theorem ltW_one106 : lt TM.Term.one (reg 1) = true := lt_one_Om103

theorem ne_zero_plus_one106 {A : Term} (hA : inT A = true) :
    plus TM.Term.one A ≠ zero := by
  intro hz
  have h1 : le TM.Term.one (plus TM.Term.one A) = true :=
    le_self_plus_ap81 inT_one106 (show isAP TM.Term.one = true from rfl) hA
  rw [hz, show le TM.Term.one zero = false from by decide] at h1
  exact Bool.noConfusion h1

theorem isSC_plus_one106 {A : Term} (hA : inT A = true) (hASC : A.isSC = false) :
    (plus TM.Term.one A).isSC = false := by
  cases hl : toList A with
  | nil => rw [plus_nil hl]; rfl
  | cons b1 r =>
      rw [plus_cons66 hl]
      cases hc : (toList TM.Term.one).filter (fun a => le b1 a) with
      | nil =>
          rw [List.nil_append, show ofList (b1 :: r) = A from by
            rw [← hl, inT_ofList_toList A hA]]
          exact hASC
      | cons z zs =>
          show (ofList (z :: (zs ++ (b1 :: r)))).isSC = false
          cases zs with
          | nil => rfl
          | cons w ws => rfl


end

/-! ### §106.4 Buchholz 側の桁と、その合法性 -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF


def mulB106 : List BT → BT
  | [] => BT.zero
  | [l] => BT.D 1 l
  | l :: ls => BT.sum (BT.D 1 l) (mulB106 ls)

def powB106 (ls : List BT) : BT := BT.D 1 (mulB106 ls)
def vebB106 (ls : List BT) : BT := BT.D 0 (powB106 ls)

/-- 成分が `BT.le` で降順。 -/
def bdesc106 : List BT → Prop
  | [] => True
  | [_] => True
  | a :: b :: r => BT.le b a = true ∧ bdesc106 (b :: r)

theorem toL_mulB106 : ∀ (ls : List BT), BT.toL (mulB106 ls) = ls.map (BT.D 1)
  | [] => rfl
  | [_] => rfl
  | l :: l2 :: ls => by
      show BT.toL (BT.D 1 l) ++ BT.toL (mulB106 (l2 :: ls)) = _
      rw [toL_mulB106 (l2 :: ls)]
      rfl

theorem gb1_mulB106 : ∀ (ls : List BT), (∀ l ∈ ls, Hd085 l) → BT.GB 1 (mulB106 ls) = ls
  | [], _ => rfl
  | [l], h => by
      show (if 1 ≤ 1 then l :: BT.GB 1 l else []) = [l]
      rw [if_pos (Nat.le_refl 1), gb1_nil98 l (h l (List.Mem.head _))]
  | l :: l2 :: ls, h => by
      show BT.GB 1 (BT.D 1 l) ++ BT.GB 1 (mulB106 (l2 :: ls)) = _
      rw [gb1_mulB106 (l2 :: ls) (fun z hz => h z (List.Mem.tail _ hz)),
        show BT.GB 1 (BT.D 1 l) = [l] from by
          show (if 1 ≤ 1 then l :: BT.GB 1 l else []) = [l]
          rw [if_pos (Nat.le_refl 1), gb1_nil98 l (h l (List.Mem.head _))]]
      rfl

theorem gb0_mulB106 : ∀ (ls : List BT),
    BT.GB 0 (mulB106 ls) = ls.flatMap (fun l => l :: BT.GB 0 l)
  | [] => rfl
  | [l] => by
      show (if 0 ≤ 1 then l :: BT.GB 0 l else []) = _
      rw [if_pos (by omega), List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | l :: l2 :: ls => by
      show BT.GB 0 (BT.D 1 l) ++ BT.GB 0 (mulB106 (l2 :: ls)) = _
      rw [gb0_mulB106 (l2 :: ls),
        show BT.GB 0 (BT.D 1 l) = l :: BT.GB 0 l from by
          show (if 0 ≤ 1 then l :: BT.GB 0 l else []) = _
          rw [if_pos (by omega)]]
      rfl

theorem btLe_mulB106 : ∀ (ls : List BT), (∀ l ∈ ls, btLe72 1 l = true) →
    btLe72 1 (mulB106 ls) = true
  | [], _ => rfl
  | [l], h => by
      show (decide (1 ≤ 1) && btLe72 1 l) = true
      rw [h l (List.Mem.head _)]; rfl
  | l :: l2 :: ls, h => by
      show (btLe72 1 (BT.D 1 l) && btLe72 1 (mulB106 (l2 :: ls))) = true
      rw [btLe_mulB106 (l2 :: ls) (fun z hz => h z (List.Mem.tail _ hz)),
        show btLe72 1 (BT.D 1 l) = true from by
          show (decide (1 ≤ 1) && btLe72 1 l) = true
          rw [h l (List.Mem.head _)]; rfl]
      rfl

theorem btle_arg106 {u : Nat} {a b : BT} (h : BT.le a b = true) :
    BT.le (BT.D u a) (BT.D u b) = true := by
  rcases (Bool.or_eq_true _ _).mp h with h1 | h1
  · rw [bt_beq_eq77 h1]
    show ((BT.D u b == BT.D u b) || _) = true
    rw [bt_beq_refl]; rfl
  · show ((BT.D u a == BT.D u b) || BT.lt (BT.D u a) (BT.D u b)) = true
    rw [btlt_arg98 (bt_ne_of_lt98 h1) h1, Bool.or_true]

theorem isStd_mulB106 : ∀ (ls : List BT), (∀ l ∈ ls, BT.isStd l = true) →
    (∀ l ∈ ls, Hd085 l) → bdesc106 ls → BT.isStd (mulB106 ls) = true
  | [], _, _, _ => rfl
  | [l], hs, hd, _ => by
      show (BT.isStd l && (BT.GB 1 l).all (fun e => BT.lt e l)) = true
      rw [hs l (List.Mem.head _), gb1_nil98 l (hd l (List.Mem.head _))]
      rfl
  | l :: l2 :: ls, hs, hd, hde => by
      have hsr : ∀ z ∈ l2 :: ls, BT.isStd z = true := fun z hz => hs z (List.Mem.tail _ hz)
      have hdr : ∀ z ∈ l2 :: ls, Hd085 z := fun z hz => hd z (List.Mem.tail _ hz)
      have hstd1 : BT.isStd (BT.D 1 l) = true := by
        show (BT.isStd l && (BT.GB 1 l).all (fun e => BT.lt e l)) = true
        rw [hs l (List.Mem.head _), gb1_nil98 l (hd l (List.Mem.head _))]
        rfl
      have hle : BT.le (BT.D 1 l2) (BT.D 1 l) = true := btle_arg106 hde.1
      cases ls with
      | nil =>
          show (BT.isP (BT.D 1 l) && BT.isStd (BT.D 1 l) && BT.isStd (BT.D 1 l2) &&
            (BT.isP (BT.D 1 l2) && BT.le (BT.D 1 l2) (BT.D 1 l))) = true
          rw [hstd1, show BT.isStd (BT.D 1 l2) = true from
              isStd_mulB106 [l2] hsr hdr trivial, hle]
          rfl
      | cons l3 ls' =>
          show (BT.isP (BT.D 1 l) && BT.isStd (BT.D 1 l) &&
            BT.isStd (BT.sum (BT.D 1 l2) (mulB106 (l3 :: ls'))) &&
            BT.le (BT.D 1 l2) (BT.D 1 l)) = true
          rw [hstd1, show BT.isStd (BT.sum (BT.D 1 l2) (mulB106 (l3 :: ls'))) = true from
              isStd_mulB106 (l2 :: l3 :: ls') hsr hdr hde.2, hle]
          rfl

/-! `BT` の順序の小道具 — `btlt_of_lt94` が使えないところを埋める。 -/

theorem size_pos106 : ∀ (x : BT), 1 ≤ BT.size x
  | .zero => Nat.le_refl 1
  | .D _ a => by have := size_pos106 a; show 1 ≤ 1 + BT.size a; omega
  | .sum a b => by
      have := size_pos106 a; have := size_pos106 b
      show 1 ≤ 1 + BT.size a + BT.size b; omega

theorem size_toL106 : ∀ (x : BT), ∀ z ∈ BT.toL x, BT.size z ≤ BT.size x
  | .zero, _, hz => by cases hz
  | .D u a, z, hz => by
      rw [List.mem_singleton.mp (show z ∈ [BT.D u a] from hz)]
      exact Nat.le_refl _
  | .sum a b, z, hz => by
      rcases List.mem_append.mp (show z ∈ BT.toL a ++ BT.toL b from hz) with h | h
      · have := size_toL106 a z h
        show BT.size z ≤ 1 + BT.size a + BT.size b
        have := size_pos106 b; omega
      · have := size_toL106 b z h
        show BT.size z ≤ 1 + BT.size a + BT.size b
        have := size_pos106 a; omega

/-- 頭が同じ段で引数が真に小さいなら、尾は見ずに真に小さい。 -/
theorem btlt_of_hd106 {x y : BT} {u : Nat} {a b : BT} {ps qs : List BT}
    (hx : BT.toL x = BT.D u a :: ps) (hy : BT.toL y = BT.D u b :: qs)
    (hne : (a == b) = false) (h : BT.lt a b = true) : BT.lt x y = true := by
  have hsa : BT.size (BT.D u a) ≤ BT.size x := size_toL106 x _ (by rw [hx]; exact List.Mem.head _)
  have hsb : BT.size (BT.D u b) ≤ BT.size y := size_toL106 y _ (by rw [hy]; exact List.Mem.head _)
  have hsa' : 1 + BT.size a ≤ BT.size x := hsa
  have hsb' : 1 + BT.size b ≤ BT.size y := hsb
  show BT.ltL (BT.size x + BT.size y + 2) (BT.toL x) (BT.toL y) = true
  rw [hx, hy, show BT.size x + BT.size y + 2 = (BT.size x + BT.size y + 1) + 1 from rfl,
    ltL_DD93, if_neg (by omega), if_neg (by omega),
    if_neg (by rw [hne]; exact Bool.noConfusion)]
  exact ltL_fuel93 (BT.size a + BT.size b + 2) _ _ _ (by omega) h

/-- 成分がすべて `D 0` の項は、頭が段 1 の項より真に小さい。§98 の `btlt_hd0_D1_98` の
    的を一般の項にしたもの。 -/
theorem btlt_hd0_hd1_106 {x m : BT} (h : Hd085 x) {z : BT} {rest : List BT}
    (hm : BT.toL m = BT.D 1 z :: rest) : BT.lt x m = true := by
  show BT.ltL (BT.size x + BT.size m + 2) (BT.toL x) (BT.toL m) = true
  rw [hm]
  cases hx : BT.toL x with
  | nil =>
      rw [show BT.size x + BT.size m + 2 = (BT.size x + BT.size m + 1) + 1 from rfl]
      exact ltL_nil_cons93 _ _ _
  | cons y ys =>
      obtain ⟨c, hc⟩ := h y (by rw [hx]; exact List.Mem.head _)
      rw [hc,
        show BT.size x + BT.size m + 2 = (BT.size x + BT.size m + 1) + 1 from rfl,
        ltL_DD93, if_pos (by omega)]

theorem bt_le_trans106 {a b c : BT} (h1 : BT.le a b = true) (h2 : BT.le b c = true) :
    BT.le a c = true := by
  rcases (Bool.or_eq_true _ _).mp h1 with e1 | e1
  · rw [bt_beq_eq77 e1]; exact h2
  · rcases (Bool.or_eq_true _ _).mp h2 with e2 | e2
    · rw [← bt_beq_eq77 e2]
      show ((a == b) || BT.lt a b) = true
      rw [e1, Bool.or_true]
    · show ((a == c) || BT.lt a c) = true
      rw [lt_trans83 e1 e2, Bool.or_true]

theorem bdesc_tail106 {a : BT} {ls : List BT} (h : bdesc106 (a :: ls)) : bdesc106 ls := by
  cases ls with
  | nil => trivial
  | cons b r => exact h.2

theorem bdesc_head106 : ∀ (l : BT) (ls : List BT), bdesc106 (l :: ls) →
    ∀ z ∈ l :: ls, BT.le z l = true
  | l, [], _, z, hz => by
      rw [List.mem_singleton.mp hz]
      show ((l == l) || _) = true
      rw [bt_beq_refl]; rfl
  | l, b :: r, h, z, hz => by
      rcases List.mem_cons.mp hz with h1 | h1
      · rw [h1]
        show ((l == l) || _) = true
        rw [bt_beq_refl]; rfl
      · exact bt_le_trans106 (bdesc_head106 b r h.2 z h1) h.1

theorem le_D1_head_mulB106 : ∀ (l : BT) (ls : List BT),
    BT.le (BT.D 1 l) (mulB106 (l :: ls)) = true
  | l, [] => by
      show ((BT.D 1 l == BT.D 1 l) || _) = true
      rw [bt_beq_refl]; rfl
  | l, b :: r => by
      have hnn : BT.toL (mulB106 (b :: r)) ≠ [] := by
        rw [toL_mulB106 (b :: r)]
        exact List.cons_ne_nil _ _
      show ((BT.D 1 l == BT.sum (BT.D 1 l) (mulB106 (b :: r))) ||
        BT.lt (BT.D 1 l) (BT.sum (BT.D 1 l) (mulB106 (b :: r)))) = true
      have hlt : BT.lt (BT.D 1 l) (BT.sum (BT.D 1 l) (mulB106 (b :: r))) = true := by
        show BT.ltL (BT.size (BT.D 1 l) + BT.size (BT.sum (BT.D 1 l) (mulB106 (b :: r))) + 2)
          [BT.D 1 l] (BT.D 1 l :: BT.toL (mulB106 (b :: r))) = true
        rw [show BT.size (BT.D 1 l) + BT.size (BT.sum (BT.D 1 l) (mulB106 (b :: r))) + 2
            = (BT.size (BT.D 1 l) + BT.size (BT.sum (BT.D 1 l) (mulB106 (b :: r))) + 1) + 1
            from rfl,
          ltL_DD93, if_neg (by omega), if_neg (by omega), if_pos (bt_beq_refl l)]
        cases hq : BT.toL (mulB106 (b :: r)) with
        | nil => exact absurd hq hnn
        | cons q qs => exact ltL_nil_cons93 _ _ _
      rw [hlt, Bool.or_true]

theorem le_D1_mulB106 {l : BT} {ls : List BT} (hde : bdesc106 (l :: ls)) :
    ∀ z ∈ l :: ls, BT.le (BT.D 1 z) (mulB106 (l :: ls)) = true := by
  intro z hz
  exact bt_le_trans106 (btle_arg106 (bdesc_head106 l ls hde z hz))
    (le_D1_head_mulB106 l ls)

theorem mem_gb0_of_toL106 : ∀ (l : BT) (u : Nat) (a : BT),
    BT.D u a ∈ BT.toL l → a ∈ BT.GB 0 l
  | .zero, _, _, hz => by cases hz
  | .D v b, u, a, hz => by
      have h1 : BT.D u a = BT.D v b := List.mem_singleton.mp hz
      injection h1 with _ h2
      show a ∈ (if 0 ≤ v then b :: BT.GB 0 b else [])
      rw [if_pos (by omega), h2]
      exact List.Mem.head _
  | .sum x y, u, a, hz => by
      rcases List.mem_append.mp (show BT.D u a ∈ BT.toL x ++ BT.toL y from hz) with h | h
      · exact List.mem_append_left _ (mem_gb0_of_toL106 x u a h)
      · exact List.mem_append_right _ (mem_gb0_of_toL106 y u a h)

theorem btlt_of_lt_le106 {e x y : BT} (h1 : BT.lt e x = true) (h2 : BT.le x y = true) :
    BT.lt e y = true := by
  rcases (Bool.or_eq_true _ _).mp h2 with e2 | e2
  · rw [← bt_beq_eq77 e2]; exact h1
  · exact lt_trans83 h1 e2

/-- **桁として使える証人。**  段 1 以下・標準・成分は `D 0`・`GB 0` は一段上に収まる。 -/
def Dig106 (l : BT) : Prop :=
  btLe72 1 l = true ∧ BT.isStd l = true ∧ Hd085 l ∧
    ∀ e ∈ BT.GB 0 l, BT.lt e (BT.D 1 (BT.D 1 l)) = true

/-- `GB 0 (Ω₁·A)` の元はどれも `Ω₁^{1+A}` の下。 -/
theorem gb0_lt_powB106 {ls : List BT} (hD : ∀ l ∈ ls, Dig106 l) (hde : bdesc106 ls) :
    ∀ e ∈ BT.GB 0 (mulB106 ls), BT.lt e (BT.D 1 (mulB106 ls)) = true := by
  intro e he
  rw [gb0_mulB106 ls] at he
  obtain ⟨l, hl, he2⟩ := List.mem_flatMap.mp he
  rcases List.mem_cons.mp he2 with h1 | h1
  · rw [h1]; exact btlt_hd0_D1_98 (hD l hl).2.2.1 _
  · cases ls with
    | nil => cases hl
    | cons l0 rest =>
        exact btlt_of_lt_le106 ((hD l hl).2.2.2 e h1)
          (btle_arg106 (le_D1_mulB106 hde l hl))

/-- `GB 1 (Ω₁·A)` の元はどれも `Ω₁·A` の下。 -/
theorem gb1_lt_mulB106 {ls : List BT} (hD : ∀ l ∈ ls, Dig106 l) :
    ∀ e ∈ BT.GB 1 (mulB106 ls), BT.lt e (mulB106 ls) = true := by
  intro e he
  rw [gb1_mulB106 ls (fun l hl => (hD l hl).2.2.1)] at he
  cases ls with
  | nil => cases he
  | cons l0 rest =>
      refine btlt_hd0_hd1_106 (hD e he).2.2.1 (z := l0) (rest := rest.map (BT.D 1)) ?_
      rw [toL_mulB106 (l0 :: rest)]
      rfl

theorem btlt_mul_pow106 {ls : List BT} (hD : ∀ l ∈ ls, Dig106 l) :
    BT.lt (mulB106 ls) (BT.D 1 (mulB106 ls)) = true := by
  cases ls with
  | nil => exact btlt_zero_D98 1 BT.zero
  | cons l0 rest =>
      have hm : BT.toL (mulB106 (l0 :: rest)) = BT.D 1 l0 :: rest.map (BT.D 1) := by
        rw [toL_mulB106 (l0 :: rest)]; rfl
      have hlt : BT.lt l0 (mulB106 (l0 :: rest)) = true :=
        btlt_hd0_hd1_106 (hD l0 (List.Mem.head _)).2.2.1 hm
      exact btlt_of_hd106 hm rfl (bt_ne_of_lt98 hlt) hlt

theorem isStd_powB106 {ls : List BT} (hD : ∀ l ∈ ls, Dig106 l) (hde : bdesc106 ls) :
    BT.isStd (powB106 ls) = true := by
  show (BT.isStd (mulB106 ls) &&
    (BT.GB 1 (mulB106 ls)).all (fun e => BT.lt e (mulB106 ls))) = true
  rw [isStd_mulB106 ls (fun l hl => (hD l hl).2.1) (fun l hl => (hD l hl).2.2.1) hde,
    Bool.true_and, List.all_eq_true]
  intro x hx
  exact gb1_lt_mulB106 hD x hx

theorem isStd_vebB106 {ls : List BT} (hD : ∀ l ∈ ls, Dig106 l) (hde : bdesc106 ls) :
    BT.isStd (vebB106 ls) = true := by
  show (BT.isStd (powB106 ls) &&
    (BT.GB 0 (powB106 ls)).all (fun e => BT.lt e (powB106 ls))) = true
  rw [isStd_powB106 hD hde, Bool.true_and,
    show BT.GB 0 (powB106 ls) = mulB106 ls :: BT.GB 0 (mulB106 ls) from by
      show (if 0 ≤ 1 then mulB106 ls :: BT.GB 0 (mulB106 ls) else []) = _
      rw [if_pos (by omega)],
    List.all_eq_true]
  intro x hx
  rcases List.mem_cons.mp hx with h1 | h1
  · rw [h1]; exact btlt_mul_pow106 hD
  · exact gb0_lt_powB106 hD hde x h1

theorem btLe_vebB106 {ls : List BT} (hD : ∀ l ∈ ls, Dig106 l) :
    btLe72 1 (vebB106 ls) = true := by
  show (decide (0 ≤ 1) && (decide (1 ≤ 1) && btLe72 1 (mulB106 ls))) = true
  rw [btLe_mulB106 ls (fun l hl => (hD l hl).1)]
  rfl

theorem hd085_vebB106 (ls : List BT) : Hd085 (vebB106 ls) := by
  intro x hx
  exact ⟨powB106 ls, List.mem_singleton.mp hx⟩

/-- 桁は作った値より真に小さい。 -/
theorem btlt_dig_vebB106 {ls : List BT} (hD : ∀ l ∈ ls, Dig106 l) (hde : bdesc106 ls)
    {l : BT} (hl : l ∈ ls) : BT.lt l (vebB106 ls) = true := by
  cases hx : BT.toL l with
  | nil =>
      show BT.ltL (BT.size l + BT.size (vebB106 ls) + 2) (BT.toL l) (BT.toL (vebB106 ls)) = true
      rw [hx, show BT.size l + BT.size (vebB106 ls) + 2
          = (BT.size l + BT.size (vebB106 ls) + 1) + 1 from rfl]
      exact ltL_nil_cons93 _ _ _
  | cons y ys =>
      obtain ⟨c, hc⟩ := (hD l hl).2.2.1 y (by rw [hx]; exact List.Mem.head _)
      have hcg : c ∈ BT.GB 0 l := mem_gb0_of_toL106 l 0 c (by rw [hx, ← hc]; exact List.Mem.head _)
      have hcl : BT.lt c (BT.D 1 (mulB106 ls)) = true := by
        cases ls with
        | nil => cases hl
        | cons l0 rest =>
            exact btlt_of_lt_le106 ((hD l hl).2.2.2 c hcg)
              (btle_arg106 (le_D1_mulB106 hde l hl))
      refine btlt_of_hd106 (u := 0) (a := c) (b := powB106 ls) (ps := ys) (qs := [])
        (by rw [hx, hc]) rfl (bt_ne_of_lt98 hcl) hcl

theorem btlt_mul_D1veb106 {ls : List BT} (hD : ∀ l ∈ ls, Dig106 l) (hde : bdesc106 ls) :
    BT.lt (mulB106 ls) (BT.D 1 (vebB106 ls)) = true := by
  cases ls with
  | nil => exact btlt_zero_D98 1 (vebB106 [])
  | cons l0 rest =>
      have hl0 : l0 ∈ l0 :: rest := List.Mem.head _
      have hm : BT.toL (mulB106 (l0 :: rest)) = BT.D 1 l0 :: rest.map (BT.D 1) := by
        rw [toL_mulB106 (l0 :: rest)]; rfl
      have hlt : BT.lt l0 (vebB106 (l0 :: rest)) = true := btlt_dig_vebB106 hD hde hl0
      exact btlt_of_hd106 hm rfl (bt_ne_of_lt98 hlt) hlt

/-- **作った値も桁として使える。**  これが反復を可能にする条で、§103 の `cov103` を
    リストに広げたものである。 -/
theorem cov_vebB106 {ls : List BT} (hD : ∀ l ∈ ls, Dig106 l) (hde : bdesc106 ls) :
    ∀ e ∈ BT.GB 0 (vebB106 ls), BT.lt e (BT.D 1 (BT.D 1 (vebB106 ls))) = true := by
  intro e he
  have hmem : e ∈ powB106 ls :: (mulB106 ls :: BT.GB 0 (mulB106 ls)) := by
    have h0 : BT.GB 0 (vebB106 ls) = powB106 ls :: BT.GB 0 (powB106 ls) := by
      show (if 0 ≤ 0 then powB106 ls :: BT.GB 0 (powB106 ls) else []) = _
      rw [if_pos (by omega)]
    have h1 : BT.GB 0 (powB106 ls) = mulB106 ls :: BT.GB 0 (mulB106 ls) := by
      show (if 0 ≤ 1 then mulB106 ls :: BT.GB 0 (mulB106 ls) else []) = _
      rw [if_pos (by omega)]
    rw [h0, h1] at he
    exact he
  have hmv : BT.lt (mulB106 ls) (BT.D 1 (vebB106 ls)) = true := btlt_mul_D1veb106 hD hde
  rcases List.mem_cons.mp hmem with h1 | h1
  · rw [h1]
    exact btlt_arg98 (bt_ne_of_lt98 hmv) hmv
  rcases List.mem_cons.mp h1 with h2 | h2
  · rw [h2]
    have hvv : BT.lt (vebB106 ls) (BT.D 1 (vebB106 ls)) = true :=
      btlt_hd0_D1_98 (hd085_vebB106 ls) _
    exact lt_trans83 hmv (btlt_arg98 (bt_ne_of_lt98 hvv) hvv)
  · rw [gb0_mulB106 ls] at h2
    obtain ⟨l, hl, he2⟩ := List.mem_flatMap.mp h2
    have hlv : BT.lt l (vebB106 ls) = true := btlt_dig_vebB106 hD hde hl
    rcases List.mem_cons.mp he2 with h3 | h3
    · rw [h3]; exact btlt_hd0_D1_98 (hD l hl).2.2.1 _
    · have hstep : BT.lt (BT.D 1 (BT.D 1 l)) (BT.D 1 (BT.D 1 (vebB106 ls))) = true := by
        have h4 : BT.lt (BT.D 1 l) (BT.D 1 (vebB106 ls)) = true :=
          btlt_arg98 (bt_ne_of_lt98 hlv) hlv
        exact btlt_arg98 (bt_ne_of_lt98 h4) h4
      exact lt_trans83 ((hD l hl).2.2.2 e h3) hstep

theorem dig_vebB106 {ls : List BT} (hD : ∀ l ∈ ls, Dig106 l) (hde : bdesc106 ls) :
    Dig106 (vebB106 ls) :=
  ⟨btLe_vebB106 hD, isStd_vebB106 hD hde, hd085_vebB106 ls, cov_vebB106 hD hde⟩

theorem dig_zero106 : Dig106 BT.zero := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro x hx
    exact absurd hx (by intro h; cases h)
  · intro e he
    exact absurd he (by intro h; cases h)

end

/-! ### §106.5 値、そして主定理 -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- 桁の値の列。 -/
def digs106 (ls : List BT) : List Term :=
  ls.map (fun l => omegaNF (plus (reg 1) (dict l)))

theorem dict_mulB106 (Hp : PsiIdxOKStd172) : ∀ (ls : List BT),
    (∀ l ∈ ls, btLe72 1 l = true ∧ BT.isStd l = true) →
    descL (digs106 ls) = true →
    dict (mulB106 ls) = ofList (digs106 ls)
  | [], _, _ => rfl
  | [l], h, _ => by
      show dict (BT.D 1 l) = _
      rw [dict_D1_eq77 Hp l (h l (List.Mem.head _)).1 (h l (List.Mem.head _)).2]
      rfl
  | l :: l2 :: ls, h, hd => by
      have hrest : ∀ z ∈ l2 :: ls, btLe72 1 z = true ∧ BT.isStd z = true :=
        fun z hz => h z (List.Mem.tail _ hz)
      have hdr : descL (digs106 (l2 :: ls)) = true := descL_tail hd
      have hAP : ∀ x ∈ digs106 (l2 :: ls), x.isAP = true := by
        intro x hx
        obtain ⟨z, _, hxz⟩ := List.mem_map.mp hx
        rw [← hxz]; exact isAP_omegaNF _
      have htl : toList (ofList (digs106 (l2 :: ls)))
          = omegaNF (plus (reg 1) (dict l2)) :: digs106 ls := by
        rw [toList_ofList _ hAP]; rfl
      show plus (dict (BT.D 1 l)) (dict (mulB106 (l2 :: ls))) = _
      rw [dict_D1_eq77 Hp l (h l (List.Mem.head _)).1 (h l (List.Mem.head _)).2,
        dict_mulB106 Hp (l2 :: ls) hrest hdr, plus_cons66 htl,
        show toList (omegaNF (plus (reg 1) (dict l))) = [omegaNF (plus (reg 1) (dict l))] from
          toList_isAP81 (isAP_omegaNF _),
        List.filter_cons_of_pos (by
          have := descL_cons.mp hd
          exact this.1)]
      rfl

theorem digs_eq_map106 {A : Term} {ls : List BT}
    (hmap : ls.map dict = (toList A).map logOm) :
    digs106 ls = (toList A).map (fun p => omegaNF (plus (reg 1) (logOm p))) := by
  show ls.map (fun l => omegaNF (plus (reg 1) (dict l))) = _
  rw [show (fun l => omegaNF (plus (reg 1) (dict l)))
      = (fun g => omegaNF (plus (reg 1) g)) ∘ dict from rfl,
    ← List.map_map, hmap, List.map_map]
  rfl

theorem ofList_digs106 {A : Term} {ls : List BT}
    (hmap : ls.map dict = (toList A).map logOm) :
    ofList (digs106 ls) = mulL (reg 1) A := by
  rw [digs_eq_map106 hmap]; rfl

theorem dict_powB106 (Hp : PsiIdxOKStd172) {A : Term} {ls : List BT}
    (hD : ∀ l ∈ ls, Dig106 l) (hde : bdesc106 ls)
    (hA : inT A = true) (hAM : lt A M = true) (hAW : lt A (reg 1) = true)
    (hmap : ls.map dict = (toList A).map logOm) :
    dict (powB106 ls) = omegaNF (mulL (reg 1) (plus TM.Term.one A)) := by
  have hdesc : descL (digs106 ls) = true := by
    rw [digs_eq_map106 hmap]
    exact mulDescInT (reg 1) A (inT_reg 1) hA
  have hm : dict (mulB106 ls) = mulL (reg 1) A := by
    rw [dict_mulB106 Hp ls (fun l hl => ⟨(hD l hl).1, (hD l hl).2.1⟩) hdesc]
    exact ofList_digs106 hmap
  show dict (BT.D 1 (mulB106 ls)) = _
  rw [dict_D1_eq77 Hp (mulB106 ls) (btLe_mulB106 ls (fun l hl => (hD l hl).1))
      (isStd_mulB106 ls (fun l hl => (hD l hl).2.1) (fun l hl => (hD l hl).2.2.1) hde),
    hm, plus_one_mulL106 hA hAM hAW]

/-- **§106.5 の主定理 — `φ̄(1 ⊕ A, 0)` は `dict` の像で、証人は合法である。**
    §103.4 の `dict_gInv103` は `ls` が塔の一段ぶんの一元リストの場合にあたる。 -/
theorem dict_vebB106 (Hp : PsiIdxOKStd172) {A : Term} {ls : List BT}
    (hD : ∀ l ∈ ls, Dig106 l) (hde : bdesc106 ls)
    (hA : inT A = true) (hAM : lt A M = true) (hAW : lt A (reg 1) = true)
    (hASC : A.isSC = false) (hmap : ls.map dict = (toList A).map logOm) :
    dict (vebB106 ls) = phi (plus TM.Term.one A) zero := by
  show collapse 0 (dict (powB106 ls)) = _
  rw [dict_powB106 Hp hD hde hA hAM hAW hmap]
  exact collapse0_mulL106 (inT_plus inT_one106 hA) (lt_plus_M inT_one106 hA ltM_one106 hAM)
    (lt_plus_W79 inT_one106 hA ltW_one106 hAW) (ne_zero_plus_one106 hA)
    (isSC_plus_one106 hA hASC)

/-! 到達可能な類 — 反復できる形にして、`0` から登る。 -/

theorem cnv_not_sc106 : ∀ {s : Term}, CNV s = true → s.isSC = false
  | zero, _ => rfl
  | phi _ _, _ => rfl
  | add _ _, _ => rfl
  | M, h => Bool.noConfusion h
  | omg _, h => Bool.noConfusion h
  | psi _ _, h => Bool.noConfusion h
  | Z _, h => Bool.noConfusion h

theorem ltW_of_cnv106 {s : Term} (h : CNV s = true) : lt s (reg 1) = true :=
  lt_trans_inT (inT_of_cnv s h) (show inT G094 = true from by decide) (inT_reg 1)
    (ltG0_cnv103 s h) (show lt G094 (reg 1) = true from by decide)

/-- **到達可能** — 桁としても使える合法な証人がある。 -/
def Rch106 (s : Term) : Prop := ∃ b : BT, Dig106 b ∧ dict b = s

theorem rch_zero106 : Rch106 zero := ⟨BT.zero, dig_zero106, rfl⟩

theorem cnv_veb106 {A : Term} (h : CNV A = true) :
    CNV (phi (plus TM.Term.one A) zero) = true := by
  show (CNV (plus TM.Term.one A) && CNV zero) = true
  rw [cnv_plus (show CNV TM.Term.one = true from rfl) h]
  rfl

/-- **一段のぼる。**  `s` に到達できるなら `φ̄(1 ⊕ ω^s, 0)` にも到達できる。
    `s = 0` から始めて `ε₀`, `ζ₀`, `φ̄(ε₀,0)`, … と、`Γ₀` の塔だけでなく
    第 1 引数が何であってもよい。 -/
theorem rch_step106 (Hp : PsiIdxOKStd172) {s : Term} (h : Rch106 s) (hcnv : CNV s = true) :
    Rch106 (phi (plus TM.Term.one (omegaNF s)) zero) ∧
      CNV (phi (plus TM.Term.one (omegaNF s)) zero) = true := by
  obtain ⟨b, hb, hbs⟩ := h
  have hsingle : ∀ l ∈ [b], Dig106 l := by
    intro l hl; rw [List.mem_singleton.mp hl]; exact hb
  have his : inT s = true := inT_of_cnv s hcnv
  have hsM : lt s M = true := cnv_lt_M s hcnv
  have hsW : lt s (reg 1) = true := ltW_of_cnv106 hcnv
  have hAcnv : CNV (omegaNF s) = true := by
    rw [omegaNF_cnv hcnv]; exact cnv_phiNF_zero hcnv
  have hA : inT (omegaNF s) = true := inT_omegaNF his
  have hAM : lt (omegaNF s) M = true := ltM_omegaNF his hsM
  have hAW : lt (omegaNF s) (reg 1) = true := by
    have h1 := lt_omegaNF_inT79 his (inT_reg 1) hsW
    rw [omegaNF_reg1_80] at h1; exact h1
  refine ⟨⟨vebB106 [b], dig_vebB106 hsingle trivial, ?_⟩, cnv_veb106 hAcnv⟩
  refine dict_vebB106 Hp hsingle trivial hA hAM hAW (cnv_not_sc106 hAcnv) ?_
  show [dict b] = (toList (omegaNF s)).map logOm
  rw [hbs, toList_isAP81 (isAP_omegaNF s)]
  show [s] = [logOm (omegaNF s)]
  rw [logOm_omegaNF106 his hsM]

/-- **段の正直さ。**  上へは 1 まで。 -/
theorem btLe1_vebB106 {ls : List BT} (hD : ∀ l ∈ ls, Dig106 l) :
    btLe72 1 (vebB106 ls) = true := btLe_vebB106 hD

/-- **そして段 0 は 1 段目から離れる。**  §103.6 の `btLe0_gInv103` と同じ規律。 -/
theorem btLe0_vebB106 (ls : List BT) : btLe72 0 (vebB106 ls) = false := rfl

end


/-! ### §106.6 測定 — 何に届き、何に届かないか -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1 dictInv)
open TM TM.Term
open Evidence.WF

/-- `collapse0_argV106` の仮説をそのまま Bool にしたもの。 -/
def okAB106 (A B : Term) : Bool :=
  inT A && lt A M && lt A (reg 1) && !(A == zero) &&
  inT B && lt B M && lt (logOm B) (reg 1) &&
  (phiNF A (sub1 (omegaNF (logOm B))) == phi A B)

/-- 桁の条件をそのまま Bool にしたもの。 -/
def digB106 (l : BT) : Bool :=
  btLe72 1 l && BT.isStd l && hd085B l &&
    (BT.GB 0 l).all (fun e => BT.lt e (BT.D 1 (BT.D 1 l)))

/-- リストの降順条件。 -/
def bdescB106 : List BT → Bool
  | [] => true
  | [_] => true
  | a :: b :: r => BT.le b a && bdescB106 (b :: r)

/-! **母集団 1 — `(A,B)` の対。**  種に `0`、`Γ₀` (強臨界)、`1` (係数にできない)、
    和、`φ̄(1,1)` (第 2 引数が加法主要でない形の材料) を入れてある。**濾していない。** -/
private def abSeed106 : List Term :=
  [zero, TM.Term.one, TM.Term.omega, ofNat 2, ofNat 3,
   phi TM.Term.one zero, phi (ofNat 2) zero, phi TM.Term.one TM.Term.one,
   phi zero (phi TM.Term.one zero), G094, plus (phi TM.Term.one zero) TM.Term.one,
   plus (phi TM.Term.one zero) (phi TM.Term.one zero)]

def abPool106 : List (Term × Term) :=
  abSeed106.flatMap fun a => abSeed106.map fun b => (a, b)

#eval (abPool106.length, abPool106.countP fun p => okAB106 p.1 p.2)
/-! **仮説が立つところではぴったり。** -/
#guard abPool106.all fun p =>
  !(okAB106 p.1 p.2) || (collapse 0 (argV106 p.1 p.2) == phi p.1 p.2)
/-! **そして仮説は見えている** — 立たない対がちゃんとある。 -/
#guard (abPool106.countP fun p => !(okAB106 p.1 p.2)) > 0
/-! **仮説は結論の言い換えでもない** — 立たないのに式が合う対もある。 -/
#eval (abPool106.countP fun p =>
  !(okAB106 p.1 p.2) && (collapse 0 (argV106 p.1 p.2) == phi p.1 p.2))

/-! **名指しの否定 (1) — `A` が強臨界だと偽。**  `φ̄(Γ₀,0)` は 2.6(vi) 末尾が
    `Γ₀` そのものに畳む冗長な項で、`dict` は決して出さない。 -/
#guard G094.isSC
#guard collapse 0 (argV106 G094 zero) == G094
#guard !(collapse 0 (argV106 G094 zero) == phi G094 zero)

/-! **名指しの否定 (2) — `B = 1` は一組では届かない。**  係数は必ず加法主要なので
    `1 ⊕ 1` は書けず、`sub1` が `1` を `0` に落としてしまう。 -/
#guard collapse 0 (argV106 (phi TM.Term.one zero) TM.Term.one)
  == phi (phi TM.Term.one zero) zero
#guard !(collapse 0 (argV106 (phi TM.Term.one zero) TM.Term.one)
  == phi (phi TM.Term.one zero) TM.Term.one)

/-! **母集団 2 — 桁のリスト。**  昇順のものも `Dig106` を破るものも入れてある。 -/
private def lsSeed106 : List BT :=
  [BT.zero, BT.D 0 BT.zero, BT.D 0 (BT.D 1 BT.zero),
   BT.D 0 (BT.D 1 (BT.D 1 BT.zero)), BT.D 0 (BT.D 1 (BT.D 1 (BT.D 1 BT.zero))),
   BT.sum (BT.D 0 (BT.D 1 BT.zero)) (BT.D 0 BT.zero)]

def lsPool106 : List (List BT) :=
  [] :: lsSeed106.map (fun x => [x])
     ++ lsSeed106.flatMap (fun x => lsSeed106.map fun y => [x, y])

#eval (lsPool106.length,
       lsPool106.countP fun ls => ls.all digB106 && bdescB106 ls)
/-! **仮説が立つところでは値も合法性もぴったり。** -/
#guard lsPool106.all fun ls =>
  !(ls.all digB106 && bdescB106 ls) ||
    (dict (vebB106 ls) == phi (plus TM.Term.one (ofList (ls.map fun l => omegaNF (dict l)))) zero
     && BT.isStd (vebB106 ls) && btLe72 1 (vebB106 ls) && hd085B (vebB106 ls)
     && digB106 (vebB106 ls))
/-! **降順は飾りではない** — 昇順のリストは母集団に入っていて、実際に落ちる。 -/
#guard (lsPool106.countP fun ls => !(bdescB106 ls)) > 0
#guard (lsPool106.filter fun ls => !(bdescB106 ls)).any fun ls => !(BT.isStd (vebB106 ls))

/-! **`Dig106` の被覆条件も飾りではない — ただし列挙では出ない。**
    288 個の `BT` を掃いても段 1 以下・標準・頭 `D 0` の 19 個は全部条件を満たす。
    落ちる形は**作らないと出てこない**: `ψ₁` を四重に入れ子にすると `GB 0` の頭が
    一段上を追い越す。§95 の教訓 — 列挙ではなく組み立てる。 -/
def deep106 : BT := BT.D 0 (BT.D 1 (BT.D 1 (BT.D 1 (BT.D 1 BT.zero))))
#guard btLe72 1 deep106 && BT.isStd deep106 && hd085B deep106
#guard !(digB106 deep106)
#guard !(BT.isStd (vebB106 [deep106]))

/-! **塔、計算。**  §103.4 の `gInv103` は一元リストの特別な場合である。 -/
#guard (List.range 8).all fun n => dict (vebB106 [gInv103 (n+1)]) == gTow102 (n+2)
#guard (List.range 8).all fun n =>
  btLe72 1 (vebB106 [gInv103 (n+1)]) && BT.isStd (vebB106 [gInv103 (n+1)])
    && hd085B (vebB106 [gInv103 (n+1)]) && digB106 (vebB106 [gInv103 (n+1)])
#guard (List.range 8).all fun n => btLe72 0 (vebB106 [gInv103 (n+1)]) == false

/-! **リストは塔より広い。**  一元リストでは第 1 引数は加法主要なものだけだが、
    複数元なら和も出る。 -/
#guard dict (vebB106 [BT.zero, BT.zero]) == phi (ofNat 3) zero
#guard dict (vebB106 [BT.D 0 (BT.D 1 BT.zero), BT.zero])
  == phi (plus (phi TM.Term.one zero) TM.Term.one) zero
#guard BT.isStd (vebB106 [BT.zero, BT.zero])
  && BT.isStd (vebB106 [BT.D 0 (BT.D 1 BT.zero), BT.zero])

/-! **届く範囲、§103.8 の敵対的な母集団で。**  359 項のうち、証人まで作れているのは
    `φ̄(A,0)` の形の 14 項、値の式 (`collapse0_argV106`) が覆うのは 171 項。
    **残る 188 項が §106 の残余で、それは第 2 引数である。** -/
def builtShape106 (t : Term) : Bool :=
  match t with | phi a zero => !(a == zero) | _ => false
def valueShape106 (t : Term) : Bool :=
  match t with | phi a b => okAB106 a b | _ => false

#eval (aPool103.length, aPool103.countP builtShape106, aPool103.countP valueShape106)
#guard aPool103.countP builtShape106 == 14
#guard aPool103.countP valueShape106 == 171
#guard aPool103.all fun t => !(valueShape106 t) ||
  (match t with | phi a b => collapse 0 (argV106 a b) == t | _ => false)

end

end Evidence.Region
