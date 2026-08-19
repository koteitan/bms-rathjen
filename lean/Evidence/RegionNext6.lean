import Evidence.RegionNext5

/-
Evidence/RegionNext6.lean — ROW 326'S REMAINING HYPOTHESES, THIRD HALF (§111-)

Split out of `RegionNext5` when that file passed 12900 lines.  Section numbers are not in
file order — sections were appended as their agents finished.
-/

namespace Evidence.Region

open BMS
/-! ## §111 THE WINDOW HAS A SECOND CARRIER, AND ONE THEOREM CLOSES BOTH — THE
       ONE-COMPONENT REDUCTION IS FREE

§108 took `GapAtG0_107` down to one clause,

    `SCFirst108` :  once `ψ₀(Ω^Ω) < b`, the value of `ψ₀` jumps the window
                    `[φ̄(Γ₀,0), φ̄(Γ₀,Γ₀⊕1))`

proved the standardness half of the gap (`ooLead108`), refuted §107's stated reason for it,
and named two residues it could not pay: §93/§96's bridge `toList (dict a) = (toL a).map dict`
— needed, it said, to reach the one-component form of the clause — and §103's missing order
fact, needed to reach `FoldSkips108`.  §111 was asked to decide `SCFirst108`.

**The clause is not decided.  What §111 returns is a residue that turns out not to be owed, a
second family of near-misses that §108's populations could not produce, one theorem that
closes every one of them, and one named clause that removes the last shape restriction.**

  §111.1  **THE ONE-COMPONENT REDUCTION IS FREE, AND IT IS AN EQUIVALENCE.**  §108 said
          reducing `SCFirst108` to its one-`ψ₀` form needs §96's bridge, "to see that a
          standard sum's components cannot outrun its leading one".  **It does not need the
          bridge and it does not need the ordering of the components at all.**
          `scFirst_of_scFirstOne111` : `SCFirstOne111 → SCFirst108`, from §101.1's
          `mem_toList_dict101` (the bridge's FREE half — every component of `dict b` is
          `dict p` for SOME `p ∈ toL b`) and §109.1's two head lemmas.  The premise
          `φ̄(Γ₀,0) ≤ dict b` descends to the head of `toList (dict b)` because `φ̄(Γ₀,0)` is
          additively principal (`le_hd_of_le109`), and the conclusion lifts back from the
          head because the head is below the whole (`le_of_le_hd109`).  **So the clause is
          only ever asked about the head, and WHICH component the head came from never has
          to be decided** — that is the ordering fact §108 was paying for and does not need.
          `scFirstOne_of_scFirst111` is the converse, one line, so the two clauses are
          EQUIVALENT (`scFirst_iff_one111`): the reduction loses nothing.

  §111.2  **THE WINDOW HAS A SECOND CARRIER FAMILY, AND IT REACHES THE TOP RUNG.**
          §108.1's `bWin108 k = ψ₀(ψ₁ψ₁ψ₀Ω^Ω ⊕ … ⊕ ψ₁ψ₁ψ₀Ω^Ω)` climbs the window by
          repeating the digit and so reaches only the FINITE rungs `φ̄(Γ₀,k)`.  §111.2 builds
          the other route into the same digit — put the coefficient INSIDE the `ψ₁`:

              `cWin111 v = ψ₀( ψ₁( ψ₁(ψ₀ Ω^Ω) ⊕ v ) )`     value  `φ̄(Γ₀, ω^(dict v))`

          — the value formula being what §111.7 MEASURES, not a theorem; what is proved is
          three rungs by `rfl`.  `dict_cWin111_G0 : dict (ψ₀(ψ₁(ψ₁ψ₀Ω^Ω ⊕ ψ₀Ω^Ω))) =
          φ̄(Γ₀,Γ₀)` — **the top rung of the window**, one step below §98's `bTowG98 1` in the
          Veblen second argument, and `dictInv` names the term by `rfl`
          (`dictInv_cWin111_G0`).  `φ̄(Γ₀,ω)` and `φ̄(Γ₀,ε₀)` are the same construction at two
          lower rungs.  Every rung is level `≤ 1`, `D 0`-headed, `inT`, and — the point —
          **its `ψ₁`-argument is STANDARD** while the whole term is not.  The family fills
          the window exactly for coefficients up to `Γ₀` and jumps it above (7 of 10 tails
          in, 3 over).  **§108's populations C and D could not have found it**: all 13 of C's
          digit carriers have the shape `ψ₁ψ₁ z` and this one is `ψ₁(ψ₁ z ⊕ v)`, and neither
          C nor D is filtered by standardness, so this is a seed problem and not a filter
          problem (0 of 1463 and 0 of 1463 have the shape).  §108's own block theorem
          `lead_notStd108` does not cover it either — it is stated at `ψ₀(ψ₁ψ₁x ⊕ r)`, and it
          reaches 0 of the 13 terms of F that are in the window.

  §111.3  **ONE BLOCK FOR EVERY CARRIER.**  `lead_notStd111` : if the `ψ₀`-argument's leading
          component is `ψ₁ y` and `y`'s leading component is `ψ₁ z` with `z` `D 0`-headed and
          something at or above `Ω^Ω` in `G(0,z)`, the whole term is not standard — **for
          every tail on both levels.**  It subsumes §108's `lead_notStd108`
          (`lead_notStd108_of111`), §108's `notStd_bWin108` (`notStd_bWin108_of111`) and
          §111.2's new family (`notStd_cWin111`), and it is proved from §108.2's general
          `needOO108` plus one order lemma, `lt_lead_bOO111`, which is §106.4's `btlt_of_hd106`
          applied twice.  `notStd_of_le_bOO111` is the shapeless form underneath it.

  §111.4  **STANDARDNESS IS LOAD-BEARING ON THE PROVED HALF TOO, AND THAT IS WHERE `dict`
          INVERTS THE ORDER.**  §108 showed the clause's UNPROVED half cannot be stated
          without `isStd` (`scFirstNoStd_false108`).  Its PROVED half cannot either:
          `ooLeadNoStd_false111` refutes `ooLead108` minus its standardness hypothesis, with
          §111.2's top rung as the witness.  What the witness exhibits is sharper than the
          refutation — `lt_cWin_bTow111` / `dict_inverts_cWin111` : the whole family, and
          §108.1's too (`lt_bWin_bTow111`), sits BELOW `ψ₀(Ω^Ω)` in `BT.lt` while its value
          sits ABOVE `Γ₀` in 𝔗(M).  **`dict` inverts the order at all 30 of §111.7's F**,
          and it is allowed to, because order preservation is claimed only on standard terms
          (`Trans/Dict.lean` §4, `DictLtA74`).  So the clause's `ψ₀(Ω^Ω) < b` premise is not
          decoration: it removes every one of the near-misses on its own.

  §111.5  **WHAT IS LEFT, NAMED.**  `Gam0Drags111` : every standard level-`≤ 1` term whose
          value is `Γ₀` is `D 0`-headed and drags something at or above `Ω^Ω` into `G(0,·)`.
          It is implied by the uniqueness §108.6's population E measured
          (`drags_of_unique111`), and from it `carrier_notStd111` blocks the `Γ₀`-digit-leading
          route with **no shape restriction left anywhere** — the tails on both levels and the
          carrier's own shape are all free.  That is where §111 stops: what is still missing
          is the OTHER half, that a value in the window with a leading digit BELOW `Γ₀` needs a
          coefficient already in the window, which is an induction on the term's size.

WHAT IS **NOT** CLAIMED.  **`SCFirst108` is NOT proved and NOT refuted, and neither is
`GapAtG0_107`.**  `cWin111` is NOT a counterexample to anything: §111.3 proves it is not
standard, at every rung.  `Gam0Drags111` is measured (§108.6's E, 9992 terms at size `≤ 12`
and 58239 at size `≤ 14`), not proved.  `DictDenseMid107`, `DictDenseMid102`, `DictDenseHi94`,
`DictDense85`, `CofDenseS1` and row 326's certificate are exactly where §108 left them:
row 326 still depends on `SCFirst108` — now equivalently on `SCFirstOne111` — through
`gap_of108`, and `PsiIdxOKStd172` and `DictLtA74` are used, not proved.  §111 does not touch
§103's hole and does not reach `FoldSkips108`.

**Where §111 stopped, precisely, and what moved.**  §108 left two residues on the road to the
clause.  §111 pays one of them and finds it was never owed (§111.1), and shows the other one's
neighbourhood is wider than §108 measured (§111.2): the carrier of a `Γ₀` digit is unique as a
VALUE but not as a TERM SHAPE, and a block theorem written to a shape is therefore the wrong
kind of theorem.  §111.3 replaces it with one that is not.  **The residue itself did not
shrink**: `SCFirst108` still needs the size induction §108 described, and §111 states its two
halves — the carrier half is now `Gam0Drags111 + carrier_notStd111`, and the coefficient half
is untouched.  This moved the residue; it did not remove it, and the honest reading is that
§111 bought generality and one free reduction, not a decision.

**AND WHAT A REFUTATION WOULD STILL HAVE TO BE.**  §108 said "a `Γ₀`-digit carrier that
population E does not reach".  §111's reading of the fold — MEASURED, not proved — is that a
`Γ₀` digit needs a component of value `Ω₁^Γ₀`, that such a component is `ψ₁` of something led
by `ψ₁ z` with `dict z = Γ₀`, and that `z` is then `ψ₀(Ω^Ω)`; doing that puts `Ω^Ω` into
`G(0,·)` while leaving the whole `ψ₀`-argument BELOW `Ω^Ω`, and §111.3 proves those two facts
are incompatible **for every tail on both levels**.  So a refutation needs a standard term of
value `Γ₀` that is not `ψ₀(Ω^Ω)`, and §108.6's E says there is none up to size 14.  The one
escape §111 could not close is the one where the `ψ₀`-argument is at or above `Ω^Ω`:
§111.7's population G builds it, all 10 members ARE legal witnesses, and every one of them
jumps the window instead of entering it — §108.4's repair again, now with the new carrier.

WHAT THE MEASUREMENT SAYS (§111.7 gives the construction).  Two families are built, one
existing population is re-read, and one is grown for the reduction.  **F** is the new carrier
at 10 coefficient tails in three shapes — bare, with a lower digit after it, and (as a
CONTROL) the same tail moved from the coefficient position to `ρ` — 30 terms, **not filtered
by standardness**.  **G** is the repair: the same 10 tails with `Ω^Ω` prefixed, 10 terms.
**E** is §108.6's enumeration of every standard level-`≤ 1` term of size `≤ 12` (9992),
re-read.  **H** is 164 legal witnesses built as sums of §98's tower, §108's repair and small
witnesses, for the reduction.

  * **13 of F's 30 land in the window, and the control lands 0 — below it, all 10.**
    Moving the tail from the coefficient position to `ρ` takes the value OUT of the window
    downwards, so it is the coefficient and nothing else that enters.  The 3 of the new
    family's 10 that miss are exactly the tails whose value passes `Γ₀`, and those jump over.
  * **All 30 are level `≤ 1`, `D 0`-headed and `inT`; 0 are standard; and all 30 have a
    STANDARD `ψ₁`-argument.**  The single failure is at the outermost `ψ₀`, at every rung.
  * **§111.3's block reaches 30 of 30; §108.2's `lead_notStd108` reaches 10 of 30, and 0 of
    the 13 in the window** — the 10 it reaches are the control family.  The premise of the
    block (`blockOK111`) is not vacuous: it fires on all 30.
  * **§108's populations C and D contain 0 terms of the new shape, out of 1463 and 1463** —
    and neither is filtered by standardness, so this is the SEED and not the filter.  The
    top rung has 14 symbols, which E's size-14 sweep reaches; E never saw it because E only
    ever builds standard terms.
  * **`dict` inverts the order on all 30**: below `ψ₀(Ω^Ω)` in `BT.lt`, above `Γ₀` in 𝔗(M).
  * **The repair jumps the window with the new carrier too**: G is 10 legal witnesses out of
    10 and 10 of 10 are at or above `φ̄(Γ₀,Γ₀⊕1)`.
  * **E re-read.**  `Gam0Drags111`'s own premise fires exactly ONCE in 9992 — so **that
    population cannot test it**, and this is said rather than counted around.  The mechanism
    behind it is testable and was tested: of the **1164** standard terms whose value is in
    `[Γ₀, Ω₁)`, **all 1164** are `D 0`-headed and carry something at or above `Ω^Ω` in
    `G(0,·)`.
  * **The reduction is tested on sums.**  156 of H's 164 are genuine sums; the clause's
    premise fires on 109, **106 of them sums**.  On 164/164 the head of `dict b` is the
    image of the LEADING component, the premise descends to the head, and the clause holds. -/

/-! ### §111.1 1 成分への還元は只 — しかも同値

§108 は「和の成分が先頭成分を追い越せない」ことを見るために §93 の橋が要る、と書いた。
**要らない。**  条項の前提 `φ̄(Γ₀,0) ≤ dict b` は左辺が加法主要項なので頭部に降り
(§109.1 の `le_hd_of_le109`)、結論は頭部が全体以下だから頭部から持ち上がる
(`le_of_le_hd109`)。**つまり条項は頭部についてしか訊かれない。**  そして頭部が
**どの成分から来たか** は、§101.1 の只の半分 (`mem_toList_dict101`) が
「どれかの成分の像である」とだけ言えば足りて、どれかを決める必要がない。
§96 の残余はここでは払わなくてよい。 -/

section
open Trans.Recal
open Trans.Dict (BT dict reg collapse)
open TM TM.Term
open Evidence.WF

/-- `ψ₀` ひとつぶんの項は成分がひとつなので `Hd085` は只。 -/
theorem hd085_D0_111 (a : BT) : Hd085 (BT.D 0 a) := by
  intro z hz; exact ⟨a, List.mem_singleton.mp hz⟩

/-- **条項の 1 成分形。**  `SCFirst108` から和を外したもの。 -/
def SCFirstOne111 : Prop := ∀ a : BT, btLe72 1 (BT.D 0 a) = true → BT.isStd (BT.D 0 a) = true →
    BT.lt (bTowG98 0) (BT.D 0 a) = true → le (rawT94 0) (dict (BT.D 0 a)) = true →
    le (dict (bTowG98 1)) (dict (BT.D 0 a)) = true

/-- 只の向き。 -/
theorem scFirstOne_of_scFirst111 (H : SCFirst108) : SCFirstOne111 :=
  fun a hb hs hlt hle => H (BT.D 0 a) hb hs (hd085_D0_111 a) hlt hle

/-- **§111.1 の主定理。**  1 成分形から一般形が出る — 橋なしで。 -/
theorem scFirst_of_scFirstOne111 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (H : SCFirstOne111) :
    SCFirst108 := by
  intro b hb hs hd _ hle
  have hib : inT (dict b) = true := (inT_dict_of_std172 Hp b hb hs).1
  have hiV : inT (dict (bTowG98 1)) = true :=
    (inT_dict_of_std172 Hp _ (legal_bTowG98 1).1 (legal_bTowG98 1).2.1).1
  cases hl : toList (dict b) with
  | nil =>
      exfalso
      rw [toList_eq_nil101 hl, show le (rawT94 0) (zero : Term) = false from rfl] at hle
      exact Bool.noConfusion hle
  | cons z s =>
      have hzhd : le (rawT94 0) z = true :=
        le_hd_of_le109 (inT_rawT98 0) (show (rawT94 0).isAP = true from rfl) hib hl hle
      obtain ⟨p, hp, hzp⟩ := mem_toList_dict101 Hp hb hs z (by rw [hl]; exact List.Mem.head _)
      obtain ⟨c, hc⟩ := hd p hp
      subst hc
      have hgood : GoodL77 (BT.toL b) := good_toL77 b hs hb
      have hbp : btLe72 1 (BT.D 0 c) = true := hgood.2.2.1 _ hp
      have hsp : BT.isStd (BT.D 0 c) = true := hgood.2.1 _ hp
      have hlep : le (rawT94 0) (dict (BT.D 0 c)) = true := by rw [← hzp]; exact hzhd
      have hltp : BT.lt (bTowG98 0) (BT.D 0 c) = true :=
        ooLead108 Hp H2 hbp hsp (hd085_D0_111 c) hlep
      refine le_of_le_hd109 hiV hib hl ?_
      rw [hzp]; exact H c hbp hsp hltp hlep

/-- **二つの条項は同値である。**  還元で失うものはない。 -/
theorem scFirst_iff_one111 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) :
    SCFirst108 ↔ SCFirstOne111 :=
  ⟨scFirstOne_of_scFirst111, scFirst_of_scFirstOne111 Hp H2⟩

/-- 隙間はこの形からも出る。 -/
theorem gap_of_one111 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (H : SCFirstOne111) :
    GapAtG0_107 := gap_of108 Hp H2 (scFirst_of_scFirstOne111 Hp H2 H)

/-! §108.5 の 5 つの帰結を 1 成分形から書き直しておく — 326 行が何に乗っているかの記録。 -/

theorem denseMid107_false_of_one111 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (H : SCFirstOne111) : ¬ DictDenseMid107 :=
  denseMid107_false_of108 Hp H2 (scFirst_of_scFirstOne111 Hp H2 H)

theorem denseMid102_false_of_one111 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (H : SCFirstOne111) : ¬ DictDenseMid102 :=
  denseMid102_false_of108 Hp H2 (scFirst_of_scFirstOne111 Hp H2 H)

theorem dictDenseHi94_false_of_one111 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (H : SCFirstOne111) : ¬ DictDenseHi94 :=
  dictDenseHi94_false_of108 Hp H2 (scFirst_of_scFirstOne111 Hp H2 H)

theorem dictDense85_false_of_one111 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (H : SCFirstOne111) : ¬ DictDense85 :=
  dictDense85_false_of108 Hp H2 (scFirst_of_scFirstOne111 Hp H2 H)

/-- そして 326 行の共終性の側もここに乗る。 -/
theorem cofDenseS1_false_of_one111 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (H : SCFirstOne111) :
    ¬ CofDenseS1 := cofDenseS1_false_of108 Hp H2 (scFirst_of_scFirstOne111 Hp H2 H)

end

/-! ### §111.2 窓のもう一つの運び手 — 係数を `ψ₁` の中に入れる道

`Γ₀` の桁の**係数**は、`ψ₁` の引数のうち `Ω₁` より下の部分から出る。だから桁を並べる
かわりに、桁を運ぶ成分 `ψ₁(ψ₀Ω^Ω)` のうしろに `ψ₀` 成分をひとつ足して、その全体に
`ψ₁` を載せればよい。係数は `ω^(dict v)` になり、**有限段だけでなく超限段にも届く。**
`v = ψ₀Ω^Ω` のとき値は `φ̄(Γ₀,Γ₀)` — 窓の一番上の段である。 -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse)
open TM TM.Term
open Evidence.WF

/-- `Γ₀` を運ぶ核 — `ψ₀(Ω^Ω)`。§98 の塔の第 0 段そのもの。 -/
def cCar111 : BT := BT.D 0 bOO94

theorem cCar_eq_bTow111 : cCar111 = bTowG98 0 := rfl

theorem hd085_cCar111 : Hd085 cCar111 := hd085_D0bOO108

theorem memOO_cCar111 : bOO94 ∈ BT.GB 0 cCar111 := by
  show bOO94 ∈ bOO94 :: BT.GB 0 bOO94
  exact List.Mem.head _

/-- **係数を中に入れた引数。**  `ψ₁(ψ₁(ψ₀Ω^Ω) ⊕ v)`。 -/
def cArg111 (v : BT) : BT := BT.D 1 (BT.sum (BT.D 1 cCar111) v)

/-- **窓の中に値を持つ第二の族。** -/
def cWin111 (v : BT) : BT := BT.D 0 (cArg111 v)

/-- 値は `φ̄(Γ₀, ω^(dict v))`。三つの段を名指しで。 -/
theorem dict_cWin111_one : dict (cWin111 (BT.D 0 BT.zero))
    = phi G094 (phi zero TM.Term.one) := rfl

theorem dict_cWin111_e0 : dict (cWin111 (BT.D 0 (BT.Om 1)))
    = phi G094 (phi TM.Term.one zero) := rfl

/-- **窓の一番上の段。**  `dict (ψ₀(ψ₁(ψ₁ψ₀Ω^Ω ⊕ ψ₀Ω^Ω))) = φ̄(Γ₀,Γ₀)`。 -/
theorem dict_cWin111_G0 : dict (cWin111 cCar111) = phi G094 G094 := rfl

/-- `dict` 自身の逆引きが名指しで返す。§108.1 は `φ̄(Γ₀,1)` で、こちらは窓の上端。 -/
theorem dictInv_cWin111_G0 : dictInv (phi G094 G094) = some (cWin111 cCar111) := rfl

/-- 三段とも窓の中 — 下端以上、`bTowG98 1` の値より下。 -/
theorem inWin_cWin111_one :
    (le (rawT94 0) (dict (cWin111 (BT.D 0 BT.zero)))
      && lt (dict (cWin111 (BT.D 0 BT.zero))) (dict (bTowG98 1))) = true := rfl

theorem inWin_cWin111_e0 :
    (le (rawT94 0) (dict (cWin111 (BT.D 0 (BT.Om 1))))
      && lt (dict (cWin111 (BT.D 0 (BT.Om 1)))) (dict (bTowG98 1))) = true := rfl

theorem inWin_cWin111_G0 :
    (le (rawT94 0) (dict (cWin111 cCar111))
      && lt (dict (cWin111 cCar111)) (dict (bTowG98 1))) = true := rfl

/-- **`ψ₁` の引数までは標準である。**  壊れるのは一番外の `ψ₀` だけ。 -/
theorem isStd_cArg111_G0 : BT.isStd (cArg111 cCar111) = true := rfl
theorem isStd_cArg111_one : BT.isStd (cArg111 (BT.D 0 BT.zero)) = true := rfl

/-- 成分は `D 0` ひとつ。 -/
theorem hd085_cWin111 (v : BT) : Hd085 (cWin111 v) := hd085_D0_111 _

end

/-! ### §111.3 運び手がどんな形でも同じ一本で止まる

§108.2 の `needOO108` は一般の定理で、そこには形の制限がない。制限が入っているのは
その相方 — 「引数が `Ω^Ω` より下」の側で、§108 はそれを `ψ₀(ψ₁ψ₁x ⊕ r)` という形に
書いた。**その形は要らない。**  頭が `ψ₁ y`、`y` の頭が `ψ₁ z`、`z` の成分が `D 0` で
あれば、両側の尾が何であっても引数は `Ω^Ω` より下である (§106.4 の `btlt_of_hd106` を
二度使うだけ)。 -/

section
open Trans.Recal
open Trans.Dict (BT dict reg collapse)
open TM TM.Term
open Evidence.WF

/-- 成分の係数集合は全体の係数集合に入る。 -/
theorem mem_GB0_of_mem_toL111 : ∀ (x : BT), ∀ p ∈ BT.toL x, ∀ e ∈ BT.GB 0 p, e ∈ BT.GB 0 x
  | BT.zero, _, hp, _, _ => by cases hp
  | BT.D u a, p, hp, e, he => by
      rw [List.mem_singleton.mp (show p ∈ [BT.D u a] from hp)] at he
      exact he
  | BT.sum a b, p, hp, e, he => by
      rcases List.mem_append.mp (show p ∈ BT.toL a ++ BT.toL b from hp) with h | h
      · exact List.mem_append_left _ (mem_GB0_of_mem_toL111 a p h e he)
      · exact List.mem_append_right _ (mem_GB0_of_mem_toL111 b p h e he)

/-- **形なしの阻止。**  引数が `Ω^Ω` 以下なのに係数集合が `Ω^Ω` 以上の元を持てば標準でない。 -/
theorem notStd_of_le_bOO111 {b : BT} (hd : Hd085 b) {e : BT} (he : e ∈ BT.GB 0 (argHd108 b))
    (hle : BT.le bOO94 e = true) (hx : BT.lt (argHd108 b) bOO94 = true) :
    BT.isStd b = false := by
  cases h : BT.isStd b with
  | false => rfl
  | true =>
      exfalso
      have hy := needOO108 hd h he hle
      rw [lt_asymm74 hx] at hy
      exact Bool.noConfusion hy

/-- 頭が `ψ₁ y`・`y` の頭が `ψ₁ z`・`z` の成分が `D 0` なら、`x` は `Ω^Ω` より下 — 尾は自由。 -/
theorem lt_lead_bOO111 {x y z : BT} {tl rest : List BT}
    (hx : BT.toL x = BT.D 1 y :: tl) (hy : BT.toL y = BT.D 1 z :: rest) (hz : Hd085 z) :
    BT.lt x bOO94 = true := by
  have h1 : BT.lt y (BT.D 1 (BT.Om 1)) = true :=
    btlt_of_hd106 (u := 1) (a := z) (b := BT.Om 1) hy rfl
      (bt_beq_false _ _ (ne_D1_hd098 hz BT.zero)) (btlt_hd0_D1_98 hz BT.zero)
  refine btlt_of_hd106 (u := 1) (a := y) (b := BT.D 1 (BT.Om 1)) hx rfl ?_ h1
  refine bt_beq_false _ _ ?_
  intro hc
  rw [hc, show BT.toL (BT.D 1 (BT.Om 1)) = [BT.D 1 (BT.Om 1)] from rfl] at hy
  injection hy with h2 _
  injection h2 with _ h3
  exact ne_D1_hd098 hz BT.zero h3.symm

/-- **§111.3 の主定理。**  `Γ₀` の桁を先頭に置く道は、**どちらの段の尾が何であっても**
    閉じている。§108.2 の `lead_notStd108` の形の制限を外したもの。 -/
theorem lead_notStd111 {x y z : BT} {tl rest : List BT}
    (hx : BT.toL x = BT.D 1 y :: tl) (hy : BT.toL y = BT.D 1 z :: rest) (hz : Hd085 z)
    {e : BT} (he : e ∈ BT.GB 0 z) (hle : BT.le bOO94 e = true) :
    BT.isStd (BT.D 0 x) = false := by
  refine notStd_of_le_bOO111 (hd085_D0_111 x) ?_ hle (lt_lead_bOO111 hx hy hz)
  show e ∈ BT.GB 0 x
  refine mem_GB0_of_mem_toL111 x (BT.D 1 y) (by rw [hx]; exact List.Mem.head _) e ?_
  show e ∈ y :: BT.GB 0 y
  refine List.Mem.tail _ ?_
  refine mem_GB0_of_mem_toL111 y (BT.D 1 z) (by rw [hy]; exact List.Mem.head _) e ?_
  show e ∈ z :: BT.GB 0 z
  exact List.Mem.tail _ he

/-- §108.2 の `lead_notStd108` はその系。 -/
theorem lead_notStd108_of111 {x : BT} (hd : Hd085 x) {e : BT} (he : e ∈ BT.GB 0 x)
    (hle : BT.le bOO94 e = true) (r : BT) :
    BT.isStd (BT.D 0 (BT.sum (BT.D 1 (BT.D 1 x)) r)) = false :=
  lead_notStd111 (y := BT.D 1 x) (z := x) rfl rfl hd he hle

/-- §108.2 の `notStd_bWin108` もその系 — 引数が和でない段も同じ一本で止まる。 -/
theorem notStd_bWin108_of111 : ∀ k : Nat, BT.isStd (bWin108 k) = false
  | 0 =>
      lead_notStd111 (x := sumG0_108 0) (y := BT.D 1 cCar111) (z := cCar111)
        (tl := []) (rest := []) rfl rfl hd085_cCar111 memOO_cCar111 (bt_le_refl108 bOO94)
  | k + 1 =>
      lead_notStd111 (x := sumG0_108 (k + 1)) (y := BT.D 1 cCar111) (z := cCar111)
        (tl := BT.toL (sumG0_108 k)) (rest := []) rfl rfl hd085_cCar111 memOO_cCar111
        (bt_le_refl108 bOO94)

/-- **そして §111.2 の新しい族も同じ一本で止まる。**  `v` は何でもよい。 -/
theorem notStd_cWin111 (v : BT) : BT.isStd (cWin111 v) = false :=
  lead_notStd111 (x := cArg111 v) (y := BT.sum (BT.D 1 cCar111) v) (z := cCar111)
    rfl rfl hd085_cCar111 memOO_cCar111 (bt_le_refl108 bOO94)

end

/-! ### §111.4 標準性は「証明ずみの側」にも要る — そこで `dict` は順序を逆転する

§108 は条項の**証明していない側**から標準性を外せないことを `bad108` で示した
(`scFirstNoStd_false108`)。**証明ずみの側 `ooLead108` からも外せない。**  そして
外したときに何が起きるかが、この節の中身である: §111.2 の族も §108.1 の族も
`BT.lt` では §98 の塔の第 0 段 `ψ₀(Ω^Ω)` より**下**にいて、値は `Γ₀` より**上**にいる。
`dict` はこの対で順序を逆転する。逆転できるのは対が標準でないからで、`dict` の順序保存は
`Trans/Dict.lean` §4 でも `DictLtA74` でも**標準な項の上でしか主張されていない**。
**近い外れがなぜ外れなのかは、ここに一番はっきり出る。** -/

section
open Trans.Recal
open Trans.Dict (BT dict reg collapse)
open TM TM.Term
open Evidence.WF

theorem lt_cArg_bOO111 (v : BT) : BT.lt (cArg111 v) bOO94 = true :=
  lt_lead_bOO111 (x := cArg111 v) (y := BT.sum (BT.D 1 cCar111) v) (z := cCar111)
    (tl := []) (rest := BT.toL v) rfl rfl hd085_cCar111

/-- **新しい族は `BT.lt` で `ψ₀(Ω^Ω)` より下にいる。** -/
theorem lt_cWin_bTow111 (v : BT) : BT.lt (cWin111 v) (bTowG98 0) = true :=
  btlt_of_hd106 (u := 0) (a := cArg111 v) (b := bOO94) rfl rfl
    (bt_ne_of_lt98 (lt_cArg_bOO111 v)) (lt_cArg_bOO111 v)

theorem notLt_bTow_cWin111 (v : BT) : BT.lt (bTowG98 0) (cWin111 v) = false :=
  lt_asymm74 (lt_cWin_bTow111 v)

/-- §108.1 の族も同じ。 -/
theorem lt_bWin_bTow111 (k : Nat) : BT.lt (bWin108 k) (bTowG98 0) = true :=
  btlt_of_hd106 (u := 0) (a := sumG0_108 k) (b := bOO94) rfl rfl
    (bt_ne_of_lt98 (lt_sumG0_bOO108 k)) (lt_sumG0_bOO108 k)

theorem notLt_bTow_bWin111 (k : Nat) : BT.lt (bTowG98 0) (bWin108 k) = false :=
  lt_asymm74 (lt_bWin_bTow111 k)

/-- **`dict` はこの対で順序を逆転する。**  左は `BT.lt` で下、右は 𝔗(M) で上。
    標準でない対でだけ起きることで、`dict` の順序保存の主張と矛盾しない。 -/
theorem dict_inverts_cWin111 :
    (BT.lt (cWin111 cCar111) (bTowG98 0)
      && lt (dict (bTowG98 0)) (dict (cWin111 cCar111))) = true := rfl

theorem dict_inverts_bWin111 :
    (BT.lt (bWin108 1) (bTowG98 0) && lt (dict (bTowG98 0)) (dict (bWin108 1))) = true := rfl

/-- `ooLead108` から標準性を外した形。 -/
def OoLeadNoStd111 : Prop := ∀ b : BT, btLe72 1 b = true → Hd085 b →
    le (rawT94 0) (dict b) = true → BT.lt (bTowG98 0) b = true

/-- **§111.4 の主定理。**  外せない。手で作った証人は §111.2 の族の上端の段で、
    §108.1 の族の第 1 段でも同じことが起きる。§108 は条項の証明していない側について
    同じことを言った (`scFirstNoStd_false108`) — **両側とも標準性が要る。** -/
theorem ooLeadNoStd_false111 : ¬ OoLeadNoStd111 := by
  intro H
  have h := H (cWin111 cCar111) rfl (hd085_cWin111 cCar111)
    (rfl : le (rawT94 0) (dict (cWin111 cCar111)) = true)
  rw [notLt_bTow_cWin111 cCar111] at h
  exact Bool.noConfusion h

end

/-! ### §111.5 残っているものに名前をつける

`Γ₀` の桁の指数を作れるのは、値が `Ω₁^Γ₀` の成分だけである。その成分は `ψ₁` を二つ
かぶせた `ψ₁(ψ₁ z ⊕ …)` の形で、`z` の値は `Γ₀` でなければならない。**値が `Γ₀` の
標準な項が `ψ₀(Ω^Ω)` しかない**ことは §108.6 の母集団 E が大きさ 14 まで数え上げて
いる。それを条項として書き出すと、§111.3 の阻止から形の制限が完全に消える。 -/

section
open Trans.Recal
open Trans.Dict (BT dict reg collapse)
open TM TM.Term
open Evidence.WF

/-- **値が `Γ₀` の標準な項は `ψ₀(Ω^Ω)` しかない。**  §108.6 の E が測った。**証明しない。** -/
def Gam0Unique111 : Prop := ∀ z : BT, btLe72 1 z = true → BT.isStd z = true →
    dict z = G094 → z = bTowG98 0

/-- 実際に使うのはそのうち二つの性質だけ。 -/
def Gam0Drags111 : Prop := ∀ z : BT, btLe72 1 z = true → BT.isStd z = true →
    dict z = G094 → Hd085 z ∧ ∃ e ∈ BT.GB 0 z, BT.le bOO94 e = true

theorem drags_of_unique111 (H : Gam0Unique111) : Gam0Drags111 := by
  intro z hb hs hd
  have hz : z = bTowG98 0 := H z hb hs hd
  subst hz
  exact ⟨hd085_cCar111, ⟨bOO94, memOO_cCar111, bt_le_refl108 bOO94⟩⟩

/-- **§111.5 の主定理。**  条項ひとつを認めれば、`Γ₀` の桁を先頭に置く道は
    **形の制限なしで**閉じる — 運び手の形も、両段の尾も自由。 -/
theorem carrier_notStd111 (H : Gam0Drags111) {x y z : BT} {tl rest : List BT}
    (hx : BT.toL x = BT.D 1 y :: tl) (hy : BT.toL y = BT.D 1 z :: rest)
    (hbz : btLe72 1 z = true) (hsz : BT.isStd z = true) (hdz : dict z = G094) :
    BT.isStd (BT.D 0 x) = false := by
  obtain ⟨hz, e, he, hle⟩ := H z hbz hsz hdz
  exact lead_notStd111 hx hy hz he hle

end

/-! ### §111.6 段の正直さ

§98・§103・§107 と同じ規律。新しい構成も段 1 を超えず、段 0 は一歩目で離れる。 -/

section
open Trans.Recal
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

theorem btLe1_cWin111 {v : BT} (h : btLe72 1 v = true) : btLe72 1 (cWin111 v) = true := by
  show btLe72 1 v = true
  exact h

theorem btLe0_cWin111 (v : BT) : btLe72 0 (cWin111 v) = false := rfl

end

/-! ### §111.7 測定 (凍結)

**構成を先に書く。**  母集団は三つ。二つは新しく作り、一つは §108.6 のものを読み直す。

    F  係数の尾 10 個 (`tailF111` — どれも「正しい証人」) を三つの形にはめたもの、30 項。
       f1 = `ψ₀(ψ₁(ψ₁ψ₀Ω^Ω ⊕ v))`          §111.2 の新しい運び手
       f2 = `ψ₀(ψ₁(ψ₁ψ₀Ω^Ω ⊕ v) ⊕ ψ₁ψ₁ψ₀Ω^Ω)` 同じ運び手の後ろに低い桁を足したもの
       f3 = `ψ₀(ψ₁ψ₁ψ₀Ω^Ω ⊕ v)`             **対照** — `v` を係数ではなく尾 `ρ` に置く
       **標準性で濾さない。**  濾さないことがこの節の要点である。
    G  同じ 10 個に `Ω^Ω` を前置した修理形、10 項。**これは全部「正しい証人」である。**
    E  §108.6 の数え上げ (大きさ 12 までの標準・段 1 以下の項 9992 個) をそのまま読み直す。

**仮説が母集団に見えていること。**  §111.3 の阻止の前提 (`blockOK111`) は F の 30/30 で
成り立ち、`Gam0Drags111` の機構は E の 1164 項で成り立つ (下)。空振りではない。 -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse)
open TM TM.Term
open Evidence.WF

/-- 係数を運ぶ尾。どれも標準・段 1 以下・成分は `D 0`。 -/
def tailF111 : List BT :=
  [ BT.D 0 BT.zero, BT.sum (BT.D 0 BT.zero) (BT.D 0 BT.zero), BT.D 0 (BT.D 0 BT.zero),
    BT.D 0 (BT.Om 1), BT.D 0 (BT.D 1 (BT.Om 1)), cCar111,
    BT.sum cCar111 (BT.D 0 BT.zero), BT.D 0 (BT.sum bOO94 (BT.D 0 BT.zero)),
    BT.D 0 (BT.sum bOO94 (BT.Om 1)), BT.D 0 (BT.D 1 (BT.D 1 (BT.D 0 (BT.Om 1)))) ]

def f1_111 : List BT := tailF111.map cWin111
def f2_111 : List BT := tailF111.map fun v => BT.D 0 (BT.sum (cArg111 v) dgG0_108)
def f3_111 : List BT := tailF111.map fun v => BT.D 0 (BT.sum dgG0_108 v)
def popF111 : List BT := f1_111 ++ f2_111 ++ f3_111
def popG111 : List BT := tailF111.map fun v => BT.D 0 (BT.sum bOO94 (cArg111 v))

/-- §111.3 の阻止が使う前提を決定可能な形に書いたもの。 -/
def blockOK111 (b : BT) : Bool :=
  BT.lt (argHd108 b) bOO94 && (BT.GB 0 (argHd108 b)).any (fun e => BT.le bOO94 e)
/-- §108.2 の `lead_notStd108` が字面で届く形か。 -/
def sh108_111 (b : BT) : Bool :=
  match b with
  | BT.D 0 (BT.sum (BT.D 1 (BT.D 1 _)) _) => true
  | _ => false
/-- §111.3 の `lead_notStd111` が字面で届く形か。 -/
def sh111_111 (b : BT) : Bool :=
  match b with
  | BT.D 0 x =>
      match BT.toL x with
      | BT.D 1 y :: _ => match BT.toL y with
                         | BT.D 1 _ :: _ => true
                         | _ => false
      | _ => false
  | _ => false
/-- `ψ₁` の引数が和になっている形 — §111.2 の新しい運び手の目印。 -/
def sumUnderD1_111 (b : BT) : Bool :=
  match b with
  | BT.D 0 x => match BT.toL x with
                | BT.D 1 (BT.sum _ _) :: _ => true
                | _ => false
  | _ => false

#guard tailF111.all fun v => bgood94 v
#guard popF111.length == 30
#guard popG111.length == 10

/-! **F の 30 項のうち 13 項が窓の中に入る — 新しい運び手 7 項と、その低い桁つき 6 項。**
    対照の f3 は 0 項で、しかも 10 項とも窓の**下**にいる: `v` を尾 `ρ` に置いても
    窓には届かない。窓に入るのは係数だけである。 -/
#eval (popF111.countP fun b => inWin108 (dict b),
       f1_111.countP fun b => inWin108 (dict b),
       f2_111.countP fun b => inWin108 (dict b),
       f3_111.countP fun b => inWin108 (dict b))
#guard (popF111.countP fun b => inWin108 (dict b)) == 13
#guard (f1_111.countP fun b => inWin108 (dict b)) == 7
#guard (f2_111.countP fun b => inWin108 (dict b)) == 6
#guard (f3_111.countP fun b => inWin108 (dict b)) == 0
#guard f3_111.all fun b => lt (dict b) (rawT94 0)

/-! **入らない 3 項は「係数が `Γ₀` を越えた」ものだけである。**  つまり新しい族は
    窓の段 `φ̄(Γ₀,δ)` を `δ ≤ Γ₀` の範囲でちょうど埋め、そこを越えると窓をまたぐ。 -/
#guard (f1_111.countP fun b => le (dict (bTowG98 1)) (dict b)) == 3

/-! **30 項とも段 1 以下・成分は `D 0`・値は `inT`、そして 30 項とも標準ではない。
    しかも `ψ₀` の引数までは 30 項とも標準である** — 壊れるのは一番外の `ψ₀` だけ。 -/
#guard (popF111.countP fun b => btLe72 1 b && hd085B b && inT (dict b)) == 30
#guard (popF111.countP fun b => BT.isStd b) == 0
#guard (popF111.countP fun b => BT.isStd (argHd108 b)) == 30

/-! **§111.3 の阻止は 30/30 に届き、§108.2 の `lead_notStd108` は 10/30 にしか届かない。
    しかもその 10 項は対照 f3 — 窓に入る 13 項のうち §108 の形が字面で届くのは 0 項。** -/
#eval (popF111.countP blockOK111, popF111.countP sh111_111, popF111.countP sh108_111,
       f1_111.countP sh108_111, f2_111.countP sh108_111, f3_111.countP sh108_111)
#guard (popF111.countP blockOK111) == 30
#guard (popF111.countP sh111_111) == 30
#guard (popF111.countP sh108_111) == 10
#guard (f1_111.countP sh108_111) == 0
#guard (f2_111.countP sh108_111) == 0
#guard ((popF111.filter fun b => inWin108 (dict b)).countP sh108_111) == 0

/-! **そして §108.6 の母集団 C・D はこの形をひとつも含まない。**  C の運び手は 13 個とも
    `ψ₁ψ₁ z` で、新しい運び手は `ψ₁(ψ₁ z ⊕ v)` である。C も D も標準性で濾していない
    のだから、これは濾過の問題ではなく**種の問題**である。 -/
#eval (rawC108.countP sumUnderD1_111, rawD108.countP sumUnderD1_111,
       f1_111.countP sumUnderD1_111, f2_111.countP sumUnderD1_111)
#guard (rawC108.countP sumUnderD1_111) == 0
#guard (rawD108.countP sumUnderD1_111) == 0
#guard (f1_111.countP sumUnderD1_111) == 10
#guard (f2_111.countP sumUnderD1_111) == 10
#guard (rawC108.contains (cWin111 cCar111)) == false
#guard (rawD108.contains (cWin111 cCar111)) == false
/-! 大きさは 14 — E の数え上げが届く大きさである。届かなかったのは標準でないからで、
    E は標準な項しか作らない。 -/
#guard BT.size (cWin111 cCar111) == 14

/-! **`dict` の逆引きは新しい族を段ごとに名指しで返す。** -/
#guard f1_111.all fun b => dictInv (dict b) == some b

/-! **そして 30 項とも `BT.lt` では §98 の塔の第 0 段より下、値は `Γ₀` より上** —
    `dict` が順序を逆転する対が 30 組。標準でないから逆転できる (§111.4)。
    だから条項の前提 `ψ₀(Ω^Ω) < b` は空文句ではなく、F の 30 項をここで全部外す。 -/
#eval (popF111.countP fun b => BT.lt b (bTowG98 0),
       popF111.countP fun b => BT.lt (bTowG98 0) b,
       popF111.countP fun b => lt (dict (bTowG98 0)) (dict b))
#guard (popF111.countP fun b => BT.lt b (bTowG98 0)) == 30
#guard (popF111.countP fun b => BT.lt (bTowG98 0) b) == 0
#guard (popF111.countP fun b => lt (dict (bTowG98 0)) (dict b)) == 30

/-! **修理は新しい運び手でも窓をまたぐ。**  `Ω^Ω` を前に置くと 10 項とも「正しい証人」に
    なり、10 項とも値は窓の上端以上。§108.4 と同じことが第二の運び手でも起きる。 -/
#guard (popG111.countP bgood94) == 10
#guard (popG111.countP fun b => le (dict (bTowG98 1)) (dict b)) == 10
#guard (popG111.countP fun b => inWin108 (dict b)) == 0

/-! **E の読み直し — `Gam0Drags111` の機構は 1164 項で見えている。**
    値が `Γ₀` の標準な項は 9992 中ちょうど 1 個 (`ψ₀(Ω^Ω)`; §108.6 が大きさ 14 でも
    同じ答えを出している) なので、`Gam0Drags111` の前提そのものは 1 回しか発火しない。
    **だから前提を広げて機構のほうを測る**: 値が `[Γ₀, Ω₁)` にある標準な項は 1164 個で、
    **その 1164 項が全部**「成分は `D 0`」かつ「`G(0,·)` に `Ω^Ω` 以上の元を持つ」。 -/
#eval (allStd108.countP fun z => dict z == G094,
       allStd108.countP fun z => le G094 (dict z) && lt (dict z) (reg 1))
#guard (allStd108.countP fun z => dict z == G094) == 1
#guard (allStd108.countP fun z => le G094 (dict z) && lt (dict z) (reg 1)) == 1164
#guard (allStd108.countP fun z => le G094 (dict z) && lt (dict z) (reg 1) &&
          hd085B z && (BT.GB 0 z).any (fun e => BT.le bOO94 e)) == 1164
#guard (allStd108.countP fun z => dict z == G094 && hd085B z &&
          (BT.GB 0 z).any (fun e => BT.le bOO94 e)) == 1

/-! **§111.1 の還元が空振りでないこと。**  §98 の塔・§108 の修理形・小さい証人を種にして
    3 個までの和を取り、「正しい証人」で濾す (164 項、うち **156 項が本当の和**)。
    条項の前提は 109 項で発火し、**そのうち 106 項が和である** — つまり還元は和の上で
    試されている。そして 164/164 で:

      * `dict b` の頭部は**先頭成分の像**である (§101.1 の只の半分が実際に先頭を返す);
      * 前提が成り立つなら**頭部にも成り立つ** (§109.1 の頭部補題の中身);
      * 条項そのものも外れ 0。 -/
def seedH111 : List BT :=
  [ bTowG98 0, bTowG98 1, bTowG98 2, BT.D 0 (BT.Om 1), BT.D 0 BT.zero, smallB108,
    bWinOO108 0, bWinOO108 1, BT.D 0 (BT.D 1 (BT.Om 1)) ]
def popH111 : List BT := ((sumsC108 2 seedH111).eraseDups).filter bgood94

#eval (popH111.length, popH111.countP fun b => (BT.toL b).length ≥ 2,
       popH111.countP fun b => le (rawT94 0) (dict b),
       popH111.countP fun b => le (rawT94 0) (dict b) && (BT.toL b).length ≥ 2)
#guard popH111.length == 164
#guard (popH111.countP fun b => (BT.toL b).length ≥ 2) == 156
#guard (popH111.countP fun b => le (rawT94 0) (dict b)) == 109
#guard (popH111.countP fun b => le (rawT94 0) (dict b) && (BT.toL b).length ≥ 2) == 106
#guard (popH111.countP fun b =>
          (toList (dict b)).headD zero == dict ((BT.toL b).headD BT.zero)) == 164
#guard (popH111.countP fun b => !(le (rawT94 0) (dict b)) ||
          le (rawT94 0) ((toList (dict b)).headD zero)) == 164
#guard (popH111.countP fun b => !(le (rawT94 0) (dict b)) ||
          le (dict (bTowG98 1)) (dict b)) == 164

end

/-! ## §114 A VEBLEN TAIL DOES NOT REACH A STRONGLY CRITICAL TARGET — AND THAT SPLITS
        §109'S HARD HALF AT THE SHAPE OF `b`'s FOLD

§109 closed the half of `HiMono89` where `a`'s fold fires at its last pair, and handed on the
other half with the sentence this section starts from:

> `HiMonoVebA109` — the case where `a`'s fold does NOT fire — is the whole remaining
> difficulty … **every witness that has ever been built against this clause sits in the half
> §109 did not close.**

**§114 proves the arithmetic that half was missing — a Veblen tail cannot climb past a
`ψ_{Ω₁}`-value — and uses it to split `HiMonoVebA109` in two at the shape of `b`'s fold.**
`HiMonoVebA109` is NOT proved and NOT refuted; what §114 does is replace it by
`VebIngF114 ∧ VebRest114`, where the first has **no Veblen arithmetic left in it at all**
(it never compares two folds) and the second is the old clause verbatim on the rest.

WHAT IS PROVED.

  §114.1  **ONE `φ̄`-STEP DOES NOT CROSS A STRONGLY CRITICAL TARGET** (`lt_phiNF_ap114`,
          `lt_phiNF_psi114`).  The exact mirror of §109.3's `lt_psi_phiNF109`: there the
          target sits below and `φ̄` cannot drop past it, here the target sits above and `φ̄`
          cannot climb past it.  `phiNF` returns its second argument, its first argument, or
          a `φ̄`-term, and the `φ̄`-term is 2.3.5 (`lt_phi_psi103`) component by component.
          What the repository lacked and §114.1 supplies is the plumbing at a GENERAL
          additively principal target: `ltAP_of_hdLe114` and `ltAP_toList114` (the components
          of a term below an AP target are below it — §79.6's `ltW_toList79` with `Ω₁`
          replaced by anything AP), `lt_ofList_ap114`, `lt_plus_ap114`, `lt_ofNat_ap114`, and
          `lt_down_ap114` for the argument `phiNFsucc` steps down to.

  §114.2  **THE WHOLE FOLD STAYS BELOW** (`accW89_lt114`).  §109.1's prefix property splits
          the pair list into a firing part and a Veblen part; `fold_fire_state114` says the
          firing part leaves the accumulator at `ψ_{Ω₁}(i)` EXACTLY (that is what firing
          does), `fold_fst_veb114` says the Veblen part never touches the index slot, so the
          `i` it leaves is `idxF88 0 x` itself, and `ltS114_fold` carries §114.1 along the
          tail.  The hypothesis is `VebIng114 x S`, a DECIDABLE condition on ONE term:
          every non-firing pair's exponent and coefficient below `S`, and `ψ_{Ω₁}` of the
          index below `S`.  **Two folds are never compared here.**  The `K`-gate is not used;
          §66.1's `PsiIdxOK` is, and only to keep `StInv` across the firing prefix.

  §114.3  **THE SPLIT** (`hiMono_bIdx114`, `hiMonoVebA_of_two114`).  When `b` has a collapse
          index `j_b`, §95.1's `accGeb95` gives `ψ_{Ω₁}(j_b) ≤ ψ₀(hi b)`, so §114.2 with the
          target `ψ_{Ω₁}(j_b)` closes the case outright — `hiMono_bIdx114` does NOT read
          `lastFire92 (dict a)` at all.  The clause `VebIngF114` asks for the ingredient
          condition only where the target is EXACT, i.e. where `b` all-fires and
          `ψ₀(hi b) = ψ_{Ω₁}(j_b)` (§92.2); `VebRest114` is `HiMonoVebA109` itself on the
          rest.  Two side theorems: `fireHeadHd114` is §109.2's "firing travels right" with
          the hypothesis cut down to the HEAD pair (§109 took it from `lastFire`, but the
          proof only ever used the head), and `idxF_none_left114` reads it backwards — if `b`
          has no index then neither has `a`, so **the bottom of `VebRest114` is exactly the
          comparison of two pure Veblen folds**, which is §104's stopping point word for word.

  §114.4  **THE NEGATIVES.**  `revSep114` / `not_vebFireFreeA114` : a BUILT pair,
          `revA114 = ψ₁(ψ₁ψ₀ψ₁ψ₁ψ₁0 ⊕ ψ₁0)` (10 symbols, `dict` image `Ω₁^(Γ₀ ⊕ 1)`) and
          `revB114 = ψ₁ψ₁ψ₁0` (4 symbols, `dict` image `Ω₁^{Ω₁}`, value `Γ₀`).  Both satisfy
          every shape condition, `b` is `K`-standard, `hi (dict a) < hi (dict b)`, and
          `ψ₀(hi a) = φ̄(Γ₀ ⊕ 1, 0) > Γ₀ = ψ₀(hi b)` — **an order REVERSAL, and the first one
          ever built in this class**: §81's `cexA89`/`cexB89` and §101's
          `scBadA101`/`scBadB101` are TIES.  What keeps it out is `BT.isStd (ψ₀ a)` and
          nothing else, and what fails at it is exactly `VebIng114`.
          `sepR114` : the restriction to an all-firing `b` is NOT cosmetic —
          `(ψ₁ψ₁ψ₁0 ⊕ Ω₁, ψ₁ψ₁ψ₁0 ⊕ ψ₁ψ₁0)` is `K`-standard on both sides, the conclusion
          HOLDS, and `VebIng114` at the target `ψ_{Ω₁}(j_b)` is FALSE because the two indices
          are EQUAL.  With a Veblen tail on `b` the target is too small, and
          `hiMono_bIdx114` does not reach that pair.  `knownSplit114` says where the three
          known witnesses land: `cexA89` and `bothBadA101` in `VebRest114`, `scBadA101` in
          the `VebIngF114` half — **neither half is empty.**

WHAT IS **NOT** CLAIMED.  `HiMonoVebA109` is NOT proved and NOT refuted; **§114 MOVES the
residue and it moves the smaller part of it.**  `VebRest114` is `HiMonoVebA109` restricted to
`lastFire92 (dict b) = false`, unweakened and unproved, and on §114.5's population it carries
84 of the 99 breaks.  `VebIngF114` is new and unproved.  `IdxMono101` and `IdxLeMix109` are
§101's and §109's clauses untouched; `PsiIdxOKStd172`, `DictOntoMidOpen103`,
`DictDenseMid107`, `DictDenseAbove107` are untouched.  Row 326 rests on `PsiIdxOKStd172`,
`IdxMono101`, `IdxLeMix109`, **`VebIngF114`, `VebRest114`**, `DictOntoMidOpen103`,
`DictDenseMid107`, `DictDenseAbove107` (`certIn_t326_114`).

**WHERE §114 STOPPED, PRECISELY.**  The `b`-all-fires class is now a condition on ONE fold's
ingredients against ONE target, and the target is a `ψ_{Ω₁}`-image, so the whole of Veblen is
gone from it; what is left there is to prove that a `K`-standard `a` below such a `b` cannot
name an exponent at or above `Γ_{j_b}`, which is the `BT`-side fact §90.1 hands over
(`e < a` for every `ψ`-argument `e` inside `a`) translated into 𝔗(M) — and §90 says plainly
that this translation is what nobody has.  The other class is untouched: when `b`'s fold ends
in a `φ̄`-term the comparison is `φ̄(α,γ) < φ̄(β,δ)`, and §114 adds nothing to it.

WHAT THE MEASUREMENT SAYS (§114.5 gives the construction).  §109's two seed lines, trimmed,
plus a third BUILT from the statement, 65 terms, nothing filtered.

  * **All three cases occur and none is vacuous.**  1974 residual pairs with `a`'s last pair
    not firing: `b` all-fires 434, `b` has an index with a Veblen tail 945, `b` has no index
    595 — with 15 / 68 / 16 breaks on the shape-only population and **0 breaks on the 929
    `K`-standard ones.**
  * **`VebIngF114` is not overpayment.**  On the 434 all-fire pairs the ingredient condition
    and the conclusion **agree exactly** — 0 pairs where the conclusion holds and the
    condition fails, 0 the other way — and on the 263 `K`-standard ones the condition never
    fails.  In that class it is necessary as well as sufficient.
  * **And it would be overpayment one class over.**  Of the 546 `K`-standard pairs where `b`
    has an index and a Veblen tail, the same target closes 483 and misses 63; `sepR114` is
    the smallest of those 63 and it is `K`-standard on both sides.  That is why
    `VebIngF114` stops at `lastFire92 (dict b) = true`.
  * **The witness had to be BUILT.**  Drop the third line and the population has 35 terms,
    519 residual pairs, 194 of them with `b` all-firing — and **0 breaks there**, while the
    same population still shows 15 reversals in the other two classes.  §95's lesson: the
    shape at issue was invisible to the population until it was constructed.
  * **The reversal is the smallest one the population contains** — 14 symbols, and every
    all-fire reversal in it has at least that many.
  * **The breaks are reversals, not ties.**  92 of the 99 breaks reverse the order; 14 of the
    15 in the all-fire class do. -/

/-! ### §114.1 強臨界の的は `φ̄` の一歩で越えられない -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 的が加法主要なら、頭部が下にあれば全体も下にある。 -/
theorem ltAP_of_hdLe114 {a b S : Term} (hia : inT a = true) (hib : inT b = true)
    (hfS : FragR S = true) (hSap : S.isAP = true) (hhd : hdLe b a = true)
    (hla : lt a S = true) : lt b S = true := by
  cases b with
  | zero => exact Bool.noConfusion hhd
  | M => exact lt_of_le_of_lt3 (inT_le_fragR _ hib) (inT_le_fragR _ hia) hfS hhd hla
  | omg c => exact lt_of_le_of_lt3 (inT_le_fragR _ hib) (inT_le_fragR _ hia) hfS hhd hla
  | phi c d => exact lt_of_le_of_lt3 (inT_le_fragR _ hib) (inT_le_fragR _ hia) hfS hhd hla
  | psi c d => exact lt_of_le_of_lt3 (inT_le_fragR _ hib) (inT_le_fragR _ hia) hfS hhd hla
  | Z c => exact lt_of_le_of_lt3 (inT_le_fragR _ hib) (inT_le_fragR _ hia) hfS hhd hla
  | add c d =>
      obtain ⟨_, hic, _, _⟩ := inT_add hib
      rw [lt_add_ap102 c d hSap]
      exact lt_of_le_of_lt3 (inT_le_fragR _ hic) (inT_le_fragR _ hia) hfS hhd hla

/-- 加法主要な的の下にある項の成分は、みなその下。§79.6 の `ltW_toList79` を的一般で。 -/
theorem ltAP_toList114 {S : Term} (hfS : FragR S = true) (hSap : S.isAP = true) :
    ∀ (s : Term), inT s = true → lt s S = true → ∀ x ∈ toList s, lt x S = true := by
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
      have hla : lt a S = true := by rw [← lt_add_ap102 a b hSap]; exact hl
      have hlb : lt b S = true := ltAP_of_hdLe114 hia hib hfS hSap hhd hla
      rcases List.mem_cons.mp (show x ∈ a :: toList b from hx) with h1 | h1
      · rw [h1]; exact hla
      · exact ihb hib hlb x h1

/-- 成分がみな加法主要な的の下なら、組み立てた項も下。 -/
theorem lt_ofList_ap114 {S : Term} (hSap : S.isAP = true) (hSz : S ≠ zero) :
    ∀ (l : List Term), (∀ x ∈ l, lt x S = true) → lt (ofList l) S = true
  | [], _ => lt_zero_left hSz
  | [a], h => h a (List.Mem.head _)
  | a :: b :: t, h => by
      show lt (add a (ofList (b :: t))) S = true
      rw [lt_add_ap102 _ _ hSap]
      exact h a (List.Mem.head _)

/-- 加法主要な的の下では `⊕` は閉じている。 -/
theorem lt_plus_ap114 {s t S : Term} (hSap : S.isAP = true) (hSz : S ≠ zero)
    (hfS : FragR S = true) (hs : inT s = true) (ht : inT t = true)
    (hls : lt s S = true) (hlt : lt t S = true) : lt (plus s t) S = true := by
  cases hl : toList t with
  | nil => rw [show plus s t = s from by unfold TM.Term.plus; rw [hl]]; exact hls
  | cons b1 rest =>
      rw [plus_eq (s := s) hl]
      refine lt_ofList_ap114 hSap hSz _ ?_
      intro x hx
      rcases List.mem_append.mp hx with h1 | h1
      · exact ltAP_toList114 hfS hSap s hs hls x (List.mem_filter.mp h1).1
      · exact ltAP_toList114 hfS hSap t ht hlt x h1

/-- 自然数は加法主要な的の下 — `1` が下にあれば。 -/
theorem lt_ofNat_ap114 {S : Term} (hSap : S.isAP = true) (hSz : S ≠ zero)
    (hfS : FragR S = true) (h1 : lt TM.Term.one S = true) :
    ∀ n, lt (ofNat n) S = true
  | 0 => lt_zero_left hSz
  | n + 1 => lt_plus_ap114 hSap hSz hfS (inT_ofNat n) inT_one
      (lt_ofNat_ap114 hSap hSz hfS h1 n) h1

/-- `splitFin` の無限部の成分は元の成分。 -/
theorem lt_splitFin_ap114 {X S : Term} (hSap : S.isAP = true) (hSz : S ≠ zero)
    (hall : ∀ x ∈ toList X, lt x S = true) : lt (splitFin X).1 S = true := by
  have hsp : (splitFin X).1 = ofList ((toList X).take ((toList X).length
      - ((toList X).reverse.takeWhile (fun x => x == TM.Term.one)).length)) := rfl
  rw [hsp]
  exact lt_ofList_ap114 hSap hSz _ (fun x hx => hall x (List.mem_of_mem_take hx))

/-- `phiNFsucc` が下げた引数も的の下。 -/
theorem lt_down_ap114 {X S : Term} (hSap : S.isAP = true) (hSz : S ≠ zero)
    (hfS : FragR S = true) (hX : inT X = true) (h1 : lt TM.Term.one S = true)
    (hall : ∀ x ∈ toList X, lt x S = true) :
    lt (plus (splitFin X).1 (ofNat ((splitFin X).2 - 1))) S = true :=
  lt_plus_ap114 hSap hSz hfS (inT_splitFin hX) (inT_ofNat _)
    (lt_splitFin_ap114 hSap hSz hall) (lt_ofNat_ap114 hSap hSz hfS h1 _)

/-- **§114.1 の核 — `φ̄` の一歩は的を越えない。**  `phiNF` が返す枝は「引数そのもの」
    「第一引数そのもの」「`φ̄` の項」の三つしかなく、`φ̄` の項は 2.3.5 で成分ごとの
    比較に落ちる。§109.3 の `lt_psi_phiNF109` の**逆向き** — あちらは的が下から、
    こちらは的が上から。 -/
theorem lt_phiNF_ap114 {A X S : Term} (hSap : S.isAP = true) (hSz : S ≠ zero)
    (hfS : FragR S = true) (hX : inT X = true) (h1 : lt TM.Term.one S = true)
    (hphi : ∀ p q : Term, lt p S = true → lt q S = true → lt (phi p q) S = true)
    (hA : lt A S = true) (hXS : lt X S = true) : lt (phiNF A X) S = true := by
  have hall := ltAP_toList114 hfS hSap X hX hXS
  have hdown := lt_down_ap114 hSap hSz hfS hX h1 hall
  have hdef : lt (phiNFdefault A X) S = true := by
    unfold phiNFdefault
    split
    · exact hA
    · exact hphi A X hA hXS
  have hsucc : lt (phiNFsucc A X) S = true := by
    unfold phiNFsucc
    split
    rename_i heq
    rw [heq] at hdown
    split
    · split <;> (split <;> first | exact hphi _ _ hA hdown | exact hdef)
    · exact hdef
  unfold phiNF
  split
  · exact hXS
  · split
    · split
      · exact hXS
      · exact hsucc
    · exact hsucc

/-- 強臨界の的での形。 -/
theorem lt_phiNF_psi114 {A X k c : Term} (hfS : FragR (psi k c) = true) (hX : inT X = true)
    (hA : lt A (psi k c) = true) (hXS : lt X (psi k c) = true) :
    lt (phiNF A X) (psi k c) = true :=
  lt_phiNF_ap114 rfl (by intro hc; exact Term.noConfusion hc) hfS hX (lt_one_psi95 k c)
    (fun _ _ hp hq => lt_phi_psi_of hp hq) hA hXS

end

/-! ### §114.2 折り畳みの Veblen の尾は的の下に留まる -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 値が的の下にある状態。 -/
def LtS114 (S : Term) (s : Option Term × Option Term) : Prop :=
  ∀ v, s.2 = some v → lt v S = true

theorem ltS114_none {S : Term} : LtS114 S ((none : Option Term), (none : Option Term)) := by
  intro v h; cases h

/-- **Veblen の一歩は的を越えない。** -/
theorem ltS114_step {k c : Term} (hfS : FragR (psi k c) = true)
    {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (hL : LtS114 (psi k c) s) (h2 : inT ac.2 = true)
    (hf : le (reg 1) ac.1 = false)
    (hA : lt ac.1 (psi k c) = true) (hC : lt ac.2 (psi k c) = true) :
    LtS114 (psi k c) (stepF (reg 1) (baseOf 0) s ac) := by
  intro v hv
  rw [stepF_snd_veb88 hf] at hv
  rw [← Option.some.inj hv]
  have hSz : (psi k c) ≠ zero := by intro hcc; exact Term.noConfusion hcc
  have hCs : lt (sub1 ac.2) (psi k c) = true :=
    lt_of_le_of_lt3 (inT_le_fragR _ (inT_sub1 h2)) (inT_le_fragR _ h2) hfS
      (le_sub1_self75 h2) hC
  cases hs2 : s.2 with
  | none =>
      refine lt_phiNF_psi114 hfS (inT_plus (inT_baseOf 0) (inT_sub1 h2)) hA ?_
      refine lt_plus_ap114 rfl hSz hfS (inT_baseOf 0) (inT_sub1 h2) ?_ hCs
      exact show lt zero (psi k c) = true from lt_zero_left hSz
  | some v0 =>
      have hiv : inT v0 = true := (hst.2 v0 hs2).1
      exact lt_phiNF_psi114 hfS (inT_plus hiv h2) hA
        (lt_plus_ap114 rfl hSz hfS hiv h2 (hL v0 hs2) hC)

/-- **Veblen だけの尾を通しても的の下に留まる。**  発火する対が一つも無いので
    §66.1 の走査条件は要らない — 門はここでは使わない。 -/
theorem ltS114_fold {k c : Term} (hfS : FragR (psi k c) = true) :
    ∀ (l : List (Term × Term)) (s : Option Term × Option Term), StInv s →
      LtS114 (psi k c) s →
      (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
      (∀ ac ∈ l, le (reg 1) ac.1 = false ∧ lt ac.1 (psi k c) = true
        ∧ lt ac.2 (psi k c) = true) →
      LtS114 (psi k c) (l.foldl (stepF (reg 1) (baseOf 0)) s) := by
  intro l
  induction l with
  | nil => intro s _ hL _ _; exact hL
  | cons ac t ih =>
      intro s hst hL hall hveb
      have hac := hall ac (List.Mem.head _)
      have hv := hveb ac (List.Mem.head _)
      have h1 : StInv (stepF (reg 1) (baseOf 0) s ac) :=
        stepF_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0) hst hac
          (fun hcc => absurd hcc (by rw [hv.1]; exact Bool.noConfusion))
      exact ih _ h1 (ltS114_step hfS hst hL hac.2.2.1 hv.1 hv.2.1 hv.2.2)
        (fun a ha => hall a (List.Mem.tail _ ha)) (fun a ha => hveb a (List.Mem.tail _ ha))

/-- 発火だけの前置きが残す状態は「まだ何も無い」か「今の指数の `ψ_{Ω₁}` ちょうど」。 -/
theorem fold_fire_state114 : ∀ (F : List (Term × Term)) (s : Option Term × Option Term),
    (∀ ac ∈ F, le (reg 1) ac.1 = true) →
    ((s.1 = none ∧ s.2 = none) ∨ ∃ i, s.1 = some i ∧ s.2 = some (psi (reg 1) i)) →
    (((F.foldl (stepF (reg 1) (baseOf 0)) s).1 = none
        ∧ (F.foldl (stepF (reg 1) (baseOf 0)) s).2 = none)
      ∨ ∃ i, (F.foldl (stepF (reg 1) (baseOf 0)) s).1 = some i
          ∧ (F.foldl (stepF (reg 1) (baseOf 0)) s).2 = some (psi (reg 1) i)) := by
  intro F
  induction F with
  | nil => intro s _ h; exact h
  | cons ac t ih =>
      intro s hf _
      refine ih _ (fun a ha => hf a (List.Mem.tail _ ha)) (Or.inr ⟨idxOf (reg 1) s ac, ?_, ?_⟩)
      · rw [stepF_fst, if_pos (hf ac (List.Mem.head _))]
      · exact stepF_snd_fire88 (hf ac (List.Mem.head _))

/-- Veblen の歩は指数の枠を触らない。 -/
theorem fold_fst_veb114 : ∀ (V : List (Term × Term)) (s : Option Term × Option Term),
    (∀ ac ∈ V, le (reg 1) ac.1 = false) →
    (V.foldl (stepF (reg 1) (baseOf 0)) s).1 = s.1 := by
  intro V
  induction V with
  | nil => intro s _; rfl
  | cons ac t ih =>
      intro s hf
      show (t.foldl (stepF (reg 1) (baseOf 0)) (stepF (reg 1) (baseOf 0) s ac)).1 = s.1
      rw [ih _ (fun a ha => hf a (List.Mem.tail _ ha)), stepF_fst,
        if_neg (by rw [hf ac (List.Mem.head _)]; exact Bool.noConfusion)]

/-- **前置きと尾に分けた形。**  発火する前置き `F` のあとに Veblen だけの尾 `V` が
    来るなら、値は的の下に留まる — 要るのは `F` が出す指数の `ψ_{Ω₁}` が的の下に
    あることと、`V` の対の成分が的の下にあることだけ。 -/
theorem foldSplit_lt114 {k c : Term} (hfS : FragR (psi k c) = true)
    (F V : List (Term × Term))
    (hFfire : ∀ ac ∈ F, le (reg 1) ac.1 = true)
    (hVveb : ∀ ac ∈ V, le (reg 1) ac.1 = false)
    (hallOK : ∀ ac ∈ F ++ V,
      inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true)
    (hscan : ∀ p ∈ scanSt (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term)) F,
      le (reg 1) p.2.1 = true → inT (psi (reg 1) (idxOf (reg 1) p.1 p.2)) = true)
    (hVlt : ∀ ac ∈ V, lt ac.1 (psi k c) = true ∧ lt ac.2 (psi k c) = true)
    (hIdx : ∀ i, ((F ++ V).foldl (stepF (reg 1) (baseOf 0))
        ((none : Option Term), (none : Option Term))).1 = some i →
      lt (psi (reg 1) i) (psi k c) = true) :
    LtS114 (psi k c) ((F ++ V).foldl (stepF (reg 1) (baseOf 0))
      ((none : Option Term), (none : Option Term))) := by
  have hmemF : ∀ ac ∈ F, ac ∈ F ++ V := fun ac hac => List.mem_append_left _ hac
  have hmemV : ∀ ac ∈ V, ac ∈ F ++ V := fun ac hac => List.mem_append_right _ hac
  have hstF : StInv (F.foldl (stepF (reg 1) (baseOf 0)) (none, none)) :=
    fold_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0)
      F (none, none) stInv_none (fun z hz => hallOK z (hmemF z hz)) hscan
  have hfoldE : (F ++ V).foldl (stepF (reg 1) (baseOf 0))
      ((none : Option Term), (none : Option Term))
      = V.foldl (stepF (reg 1) (baseOf 0))
          (F.foldl (stepF (reg 1) (baseOf 0)) (none, none)) := List.foldl_append
  have hLF : LtS114 (psi k c) (F.foldl (stepF (reg 1) (baseOf 0)) (none, none)) := by
    rcases fold_fire_state114 F (none, none) hFfire (Or.inl ⟨rfl, rfl⟩) with h1 | ⟨i, hi1, hi2⟩
    · intro v hv; rw [h1.2] at hv; cases hv
    · intro v hv
      rw [hi2] at hv
      rw [← Option.some.inj hv]
      refine hIdx i ?_
      rw [hfoldE, fold_fst_veb114 V _ hVveb, hi1]
  rw [hfoldE]
  refine ltS114_fold hfS V _ hstF hLF (fun z hz => hallOK z (hmemV z hz)) ?_
  intro ac hac
  exact ⟨hVveb ac hac, (hVlt ac hac).1, (hVlt ac hac).2⟩

/-- **成分の条件。**  発火しない対の指数と係数、そして前置きが出す `ψ_{Ω₁}` が、
    みな的の下にあるか。判定できる。 -/
def VebIng114 (x S : Term) : Bool :=
  (wcnf (reg 1) (toList x)).1.all (fun ac => le (reg 1) ac.1 || (lt ac.1 S && lt ac.2 S))
    && (match idxF88 0 x with | none => true | some i => lt (psi (reg 1) i) S)

/-- **§114.2 の主定理 — 成分が的の下なら値も的の下。**  的は強臨界だから、
    Veblen の尾はそれを越えられない。**二つの折り畳みを比べていない** — 見ているのは
    `x` の側だけである。 -/
theorem accW89_lt114 {x : Term} (hx : inT x = true) (hlx : lt x M = true) (Hp : PsiIdxOK 0 x)
    {k c : Term} (hfS : FragR (psi k c) = true) (h : VebIng114 x (psi k c) = true) :
    lt (accW89 x) (psi k c) = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList x) hc hd
    (ltM_toList x hx hlx)
  obtain ⟨hIng, hIdx⟩ := (Bool.and_eq_true _ _).mp h
  have hFV : (wcnf (reg 1) (toList x)).1.takeWhile (fun z : Term × Term => le (reg 1) z.1)
      ++ (wcnf (reg 1) (toList x)).1.dropWhile (fun z : Term × Term => le (reg 1) z.1)
      = (wcnf (reg 1) (toList x)).1 := List.takeWhile_append_dropWhile
  have hVveb : ∀ ac ∈ (wcnf (reg 1) (toList x)).1.dropWhile
      (fun z : Term × Term => le (reg 1) z.1), le (reg 1) ac.1 = false :=
    fireSplit109 (isSC_reg_succ 0) (inT_reg 1) (show (reg 1).isAP = true from rfl)
      (toList x) hc hd
  have hIdx' : ∀ i, ((wcnf (reg 1) (toList x)).1.foldl
      (init := ((none : Option Term), (none : Option Term)))
      (stepF (reg 1) (baseOf 0))).1 = some i → lt (psi (reg 1) i) (psi k c) = true := by
    intro i hi
    have he : idxF88 0 x = some i := hi
    rw [he] at hIdx
    exact hIdx
  have hmain := foldSplit_lt114 hfS _ _
    (fun ac hac => mem_takeWhile109 (fun z : Term × Term => le (reg 1) z.1) _ ac hac)
    hVveb
    (by rw [hFV]; exact hallOK)
    (by
      intro p hp
      refine Hp p ?_
      rw [← hFV, scanSt_append109]
      exact List.mem_append_left _ hp)
    (by
      intro ac hac
      have hb := List.all_eq_true.mp hIng ac (by rw [← hFV]; exact List.mem_append_right _ hac)
      rcases (Bool.or_eq_true _ _).mp hb with h1 | h1
      · rw [hVveb ac hac] at h1; exact Bool.noConfusion h1
      · exact ⟨((Bool.and_eq_true _ _).mp h1).1, ((Bool.and_eq_true _ _).mp h1).2⟩)
    (by rw [hFV]; exact hIdx')
  rw [hFV] at hmain
  show lt (((wcnf (reg 1) (toList x)).1.foldl
    (init := ((none : Option Term), (none : Option Term)))
    (stepF (reg 1) (baseOf 0))).2.getD zero) (psi k c) = true
  cases hv : ((wcnf (reg 1) (toList x)).1.foldl
      (init := ((none : Option Term), (none : Option Term)))
      (stepF (reg 1) (baseOf 0))).2 with
  | none => exact lt_zero_left (by intro hcc; exact Term.noConfusion hcc)
  | some v => exact hmain v hv

end

/-! ### §114.3 分割 — `b` が指数を持つ半分と、両方が Veblen だけの半分 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 底 `Ω₁` の分解の**頭の対**が発火するか。 -/
def headFire114 (x : Term) : Bool :=
  match (wcnf (reg 1) (toList x)).1 with
  | [] => false
  | ac :: _ => le (reg 1) ac.1

/-- 頭が発火しないなら指数は出ない — 発火が前置きだから (§109.1)。 -/
theorem idxF_none_of_headFire114 {X : Term} (hX : inT X = true) (h : headFire114 X = false) :
    idxF88 0 X = none := by
  obtain ⟨hc, hd⟩ := inT_toList X hX
  have hsp := fireSplit109 (isSC_reg_succ 0) (inT_reg 1) (show (reg 1).isAP = true from rfl)
    (toList X) hc hd
  cases hl : (wcnf (reg 1) (toList X)).1 with
  | nil => exact idxF88_none_of_nil90 hl
  | cons ac ps =>
      have hf : le (reg 1) ac.1 = false := by
        unfold headFire114 at h
        rw [hl] at h
        exact h
      have hdw : (wcnf (reg 1) (toList X)).1.dropWhile (fun z : Term × Term => le (reg 1) z.1)
          = (wcnf (reg 1) (toList X)).1 := by
        rw [hl]
        exact List.dropWhile_cons_of_neg (by rw [hf]; exact Bool.noConfusion)
      have hall : ∀ ac' ∈ (wcnf (reg 1) (toList X)).1, le (reg 1) ac'.1 = false := by
        intro ac' hac'
        exact hsp ac' (by rw [hdw]; exact hac')
      show ((wcnf (reg 1) (toList X)).1.foldl
        (init := ((none : Option Term), (none : Option Term))) (stepF (reg 1) (baseOf 0))).1
          = none
      exact fold_fst_veb114 _ _ hall

/-- 頭が発火するなら指数が出る (§109.2 の `idxF_some_of_head109` の言い換え)。 -/
theorem idxF_some_of_headFire114 {X : Term} (h : headFire114 X = true) :
    ∃ j, idxF88 0 X = some j := by
  cases hl : (wcnf (reg 1) (toList X)).1 with
  | nil =>
      exfalso
      unfold headFire114 at h
      rw [hl] at h
      exact Bool.noConfusion h
  | cons ac ps =>
      refine idxF_some_of_head109 hl ?_
      unfold headFire114 at h
      rw [hl] at h
      exact h

/-- **§109.2 の主定理を頭だけで。**  `X` の**頭の**対が発火し `X < Y` なら `Y` の頭の対も
    発火する。`lastFire92` は要らない — §109.2 が全発火から取っていたものは、頭の
    発火そのものだった。 -/
theorem fireHeadHd114 {X Y : Term} (hX : inT X = true) (hY : inT Y = true)
    (hh : headFire114 X = true) (hlt : lt X Y = true) : headFire114 Y = true := by
  cases hXl : (wcnf (reg 1) (toList X)).1 with
  | nil =>
      exfalso
      unfold headFire114 at hh
      rw [hXl] at hh
      exact Bool.noConfusion hh
  | cons ac0 ps0 =>
      obtain ⟨p, s, hXt, hpw, hp1⟩ := wcnf_fst_cons109 (toList X) ac0 ps0 hXl
      have hfp : le (reg 1) (wA (reg 1) p) = true := by
        rw [← hp1]
        unfold headFire114 at hh
        rw [hXl] at hh
        exact hh
      have hYne : Y ≠ zero := by
        intro hcc; rw [hcc, lt_zero_right] at hlt; exact Bool.noConfusion hlt
      cases hYt : toList Y with
      | nil => exact absurd (toList_eq_nil Y hYt) hYne
      | cons q rest =>
          have hip : inT p = true := inTL_inT hX p (by rw [hXt]; exact List.Mem.head _)
          have hap : p.isAP = true := inTL_isAP hX p (by rw [hXt]; exact List.Mem.head _)
          have hiq : inT q = true := inTL_inT hY q (by rw [hYt]; exact List.Mem.head _)
          have haq : q.isAP = true := inTL_isAP hY q (by rw [hYt]; exact List.Mem.head _)
          have hpq : le p q = true := hd_mono_inT hX hY hXt hYt (le_of_lt94 hlt)
          have hqw : lt q (reg 1) = false := by
            cases hcq : lt q (reg 1) with
            | false => rfl
            | true =>
                exfalso
                have hh2 := lt_of_le_of_lt3 (inT_le_fragR p hip) (inT_le_fragR q hiq)
                  (inT_le_fragR _ inT_W79) hpq hcq
                rw [hh2] at hpw
                exact Bool.noConfusion hpw
          obtain ⟨c, ps, he⟩ := wcnfFstHd109 (w := reg 1) rest hqw
          show (match (wcnf (reg 1) (toList Y)).1 with
                | [] => false | ac :: _ => le (reg 1) ac.1) = true
          rw [hYt, he]
          exact fireMono109 (isSC_reg_succ 0) (inT_reg 1) (show (reg 1).isAP = true from rfl)
            haq hiq hqw hap hip hpw hpq hfp

/-- **`b` が指数を持たないなら `a` も持たない。**  §109.2 が右に伝えるのは発火だから、
    左に伝わるのは発火しないことである。**残る半分は「両方が Veblen だけ」に他ならない。** -/
theorem idxF_none_left114 {a b : Term} (ha : inT a = true) (hb : inT b = true)
    (hlt : lt (hiW89 a) (hiW89 b) = true) (h : idxF88 0 b = none) : idxF88 0 a = none := by
  cases hh : headFire114 (hiW89 a) with
  | false =>
      rw [← idxF_hiW101 ha]
      exact idxF_none_of_headFire114 (inT_hiW89 ha) hh
  | true =>
      exfalso
      obtain ⟨j, hj⟩ := idxF_some_of_headFire114
        (fireHeadHd114 (inT_hiW89 ha) (inT_hiW89 hb) hh hlt)
      rw [idxF_hiW101 hb, h] at hj
      cases hj

/-- **`b` が全発火する半分の条項。**  `a` の折り畳みの Veblen の対の指数と係数、
    そして `a` の前置きが出す `ψ_{Ω₁}` が、みな `ψ_{Ω₁}(j_b)` の下にある。
    **Veblen の算術はここに一つも残っていない** — 二つの折り畳みを比べる代わりに、
    `a` の側の成分を的と比べるだけである。  `b` が全発火するときに限るのは飾りでは
    ない: §114.4 の `sepR114` が、`b` に Veblen の尾があると的 `ψ_{Ω₁}(j_b)` は
    **狭すぎる**ことを `K` 標準な対で示す。 -/
def VebIngF114 : Prop :=
  ∀ (a b : BT) (jb : Term), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lastFire92 (dict a) = false → lastFire92 (dict b) = true →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    idxF88 0 (dict b) = some jb →
    VebIng114 (dict a) (psi (reg 1) jb) = true

/-- **`b` も全発火しない半分の条項。**  両辺の累算器が `φ̄` の項になる場合で、
    §104 が止まったところ — `φ̄(α,γ) < φ̄(β,δ)` の比較そのもの。 -/
def VebRest114 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lastFire92 (dict a) = false → lastFire92 (dict b) = false →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true

/-- **§114.3 の主定理 (1) — `b` が指数を持つ半分は成分の条件だけで閉じる。**
    `lastFire92 (dict a) = false` は**読んでいない**: §114.2 の折り畳みの定理は
    `a` の側の発火の有無に依らない。 -/
theorem hiMono_bIdx114 (Hp : PsiIdxOKStd172) {a b : BT} {jb : Term}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hbB : btLe72 1 (BT.D 0 b) = true)
    (hsA : BT.isStd (BT.D 0 a) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (hWa : le (reg 1) (dict a) = true) (hWb : le (reg 1) (dict b) = true)
    (hjb : idxF88 0 (dict b) = some jb)
    (h : VebIng114 (dict a) (psi (reg 1) jb) = true) :
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true := by
  have hba := (btLe72_D 1 0 a hbA).2
  have hbb := (btLe72_D 1 0 b hbB).2
  have hsa := isStd_of_D hsA
  have hsb := isStd_of_D hsB
  have hia := inT_dict_of_std172 Hp a hba hsa
  have hib := inT_dict_of_std172 Hp b hbb hsb
  have hpa : PsiIdxOK 0 (dict a) := Hp 0 a (by omega) hba hsA
  have hpb : PsiIdxOK 0 (dict b) := Hp 0 b (by omega) hbb hsB
  have hijb : inT jb = true := inT_idxF92 hib.1 hib.2 hjb
  have hfS : FragR (psi (reg 1) jb) = true := fragR_psi_reg92 (inT_le_fragR jb hijb)
  have hva : collapse 0 (hiW89 (dict a)) = accW89 (dict a) :=
    collapse0_hi89 (dict a) hia.1 hia.2 hpa hWa
  have hvb : collapse 0 (hiW89 (dict b)) = accW89 (dict b) :=
    collapse0_hi89 (dict b) hib.1 hib.2 hpb hWb
  have hle : le (psi (reg 1) jb) (accW89 (dict b)) = true :=
    le_psi_accW89_of_accGeb92 (accGeb95 hib.1 hib.2 hpb hjb) hjb
  have hlt : lt (accW89 (dict a)) (psi (reg 1) jb) = true :=
    accW89_lt114 hia.1 hia.2 hpa hfS h
  have haccb : inT (accW89 (dict b)) = true :=
    (accW89_facts (dict b) hib.1 hib.2 hpb hWb).1
  have hacca : inT (accW89 (dict a)) = true :=
    (accW89_facts (dict a) hia.1 hia.2 hpa hWa).1
  rw [hva, hvb]
  exact lt_of_lt_of_le3 (inT_le_fragR _ hacca) hfS (inT_le_fragR _ haccb) hlt hle

/-- **§114.3 の主定理 (2) — `HiMonoVebA109` は二つに割れる。**  切れ目は
    「`b` の折り畳みが `ψ_{Ω₁}` で終わるか `φ̄` で終わるか」である。 -/
theorem hiMonoVebA_of_two114 (Hp : PsiIdxOKStd172) (H1 : VebIngF114) (H2 : VebRest114) :
    HiMonoVebA109 := by
  intro a b hbA hbB hsA hsB hWa hWb hfa hlt
  cases hfb : lastFire92 (dict b) with
  | false => exact H2 a b hbA hbB hsA hsB hWa hWb hfa hfb hlt
  | true =>
      have hbb := (btLe72_D 1 0 b hbB).2
      have hib := inT_dict_of_std172 Hp b hbb (isStd_of_D hsB)
      obtain ⟨jb, hjb⟩ := idxF_some_of_lastFire109 hib.1 hfb
      exact hiMono_bIdx114 Hp hbA hbB hsA hsB hWa hWb hjb
        (H1 a b jb hbA hbB hsA hsB hWa hWb hfa hfb hlt hjb)

/-- **`HiMono89` を四つの条項に架け替える。** -/
theorem hiMono_of_four114 (Hp : PsiIdxOKStd172) (HA : IdxMono101) (HB : IdxLeMix109)
    (H1 : VebIngF114) (H2 : VebRest114) : HiMono89 :=
  hiMono_of_three109 Hp HA HB (hiMonoVebA_of_two114 Hp H1 H2)

/-- **326 行目を架け替える。** -/
theorem certIn_t326_114 (Hp : PsiIdxOKStd172) (HA : IdxMono101) (HB : IdxLeMix109)
    (H1 : VebIngF114) (H2 : VebRest114) (HD1 : DictOntoMidOpen103) (HD3 : DictDenseMid107)
    (HD4 : DictDenseAbove107) (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_109 Hp HA HB (hiMonoVebA_of_two114 Hp H1 H2) HD1 HD3 HD4 hacc

end

/-! ### §114.4 否定と段の正直さ -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 折り畳みが出す指数、読み出せる形。 -/
def jOf114 (a : BT) : Term := (idxF88 0 (dict a)).getD zero

/-- `Γ₀` の Buchholz 側の原像 `ψ₀ψ₁ψ₁ψ₁0` (§103.4 の塔の一段目)。 -/
def g0A114 : BT := BT.D 0 w3_101
/-- `ψ₁Γ₀ ⊕ Ω₁` — `dict` の像は `Ω₁·Γ₀ ⊕ Ω₁ = Ω₁·(Γ₀ ⊕ 1)`。 -/
def yA114 : BT := BT.sum (BT.D 1 g0A114) (BT.D 1 BT.zero)
/-- **組んだ証人 (a)** — `ψ₁(ψ₁ψ₀ψ₁ψ₁ψ₁0 ⊕ ψ₁0)`、10 記号。`dict` の像は
    `Ω₁^(Γ₀ ⊕ 1)` で、底 `Ω₁` の分解の唯一の対は `(Γ₀ ⊕ 1, 1)` — 発火しない。 -/
def revA114 : BT := BT.D 1 yA114
/-- **組んだ証人 (b)** — `ψ₁ψ₁ψ₁0`、4 記号。`dict` の像は `Ω₁^{Ω₁}`、`ψ₀` の値は
    `Γ₀ = ψ_{Ω₁}(0)`。 -/
def revB114 : BT := w3_101

/-- **否定 1 — `b` が全発火する半分は `K` の条件なしでは偽、しかも順序が逆転する。**
    形の条件はすべて満たし、`b` の側は `K` 標準、落ちているのは `a` の `K` の条件
    ただ一つ。値は `ψ₀(hi a) = φ̄(Γ₀ ⊕ 1, 0) > Γ₀ = ψ₀(hi b)`。
    §81 の `cexA89`/`cexB89` も §101 の `scBadA101`/`scBadB101` も**引き分け**
    (値が等しい) であって、この半分で順序が逆転する証人はこれが最初である。
    そして落ちているのは §114.2 の成分の条件そのもの: `VebIng114` は偽。 -/
theorem revSep114 :
    (btLe72 1 (BT.D 0 revA114), BT.isStd revA114, BT.isStd (BT.D 0 revA114),
     le (reg 1) (dict revA114), lastFire92 (dict revA114), (idxF88 0 (dict revA114)).isSome,
     btLe72 1 (BT.D 0 revB114), BT.isStd revB114, BT.isStd (BT.D 0 revB114),
     le (reg 1) (dict revB114), lastFire92 (dict revB114),
     lt (hiW89 (dict revA114)) (hiW89 (dict revB114)),
     lt (collapse 0 (hiW89 (dict revA114))) (collapse 0 (hiW89 (dict revB114))),
     lt (collapse 0 (hiW89 (dict revB114))) (collapse 0 (hiW89 (dict revA114))),
     VebIng114 (dict revA114) (psi (reg 1) (jOf114 revB114)),
     jOf114 revB114 == zero, BT.size revA114, BT.size revB114)
    = (true, true, false, true, false, false,
       true, true, true, true, true,
       true, false, true, false, true, 10, 4) := rfl

/-- **否定 1、条項の形。**  `BT.isStd (ψ₀ a)` を `BT.isStd a` に弱めると、`b` が
    全発火する半分は偽になる。`b` の側の `K` の条件は残したままである。 -/
theorem not_vebFireFreeA114 :
    ¬ (∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
        BT.isStd a = true → BT.isStd (BT.D 0 b) = true →
        le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
        lastFire92 (dict a) = false → lastFire92 (dict b) = true →
        lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
        lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true) := by
  intro H
  have h := H revA114 revB114
    (show btLe72 1 (BT.D 0 revA114) = true from rfl)
    (show btLe72 1 (BT.D 0 revB114) = true from rfl)
    (show BT.isStd revA114 = true from rfl)
    (show BT.isStd (BT.D 0 revB114) = true from rfl)
    (show le (reg 1) (dict revA114) = true from rfl)
    (show le (reg 1) (dict revB114) = true from rfl)
    (show lastFire92 (dict revA114) = false from rfl)
    (show lastFire92 (dict revB114) = true from rfl)
    (show lt (hiW89 (dict revA114)) (hiW89 (dict revB114)) = true from rfl)
  rw [show lt (collapse 0 (hiW89 (dict revA114)))
        (collapse 0 (hiW89 (dict revB114))) = false from rfl] at h
  exact Bool.noConfusion h

/-- 分離の対 (a) — `ψ₁ψ₁ψ₁0 ⊕ Ω₁`、7 記号 (§109 の `mixB109` そのもの)。 -/
def sepRA114 : BT := BT.sum w3_101 w1_101
/-- 分離の対 (b) — `ψ₁ψ₁ψ₁0 ⊕ ψ₁ψ₁0`、8 記号。 -/
def sepRB114 : BT := BT.sum w3_101 w2_101

/-- **段の正直さ — `b` が全発火するときに限る条件は飾りではない。**  この対は
    両辺とも `K` 標準で、`a` も `b` も最後の対が発火せず、`b` は指数を持ち、
    結論は**成り立つ**。それでも `VebIng114` は偽である: **指数が等しい**
    (`j_a = j_b`) ので `a` の側の値は `ψ_{Ω₁}(j_b)` をはじめから超えていて、
    的が狭すぎる。的が丁度になるのは `b` が全発火するときだけで、そのとき
    `ψ₀(hi b) = ψ_{Ω₁}(j_b)` である (§92.2)。
    §114.3 の `hiMono_bIdx114` はこの対には**届かない**。 -/
theorem sepR114 :
    (btLe72 1 (BT.D 0 sepRA114), BT.isStd (BT.D 0 sepRA114), le (reg 1) (dict sepRA114),
     lastFire92 (dict sepRA114), (idxF88 0 (dict sepRA114)).isSome,
     btLe72 1 (BT.D 0 sepRB114), BT.isStd (BT.D 0 sepRB114), le (reg 1) (dict sepRB114),
     lastFire92 (dict sepRB114), (idxF88 0 (dict sepRB114)).isSome,
     lt (hiW89 (dict sepRA114)) (hiW89 (dict sepRB114)),
     lt (collapse 0 (hiW89 (dict sepRA114))) (collapse 0 (hiW89 (dict sepRB114))),
     VebIng114 (dict sepRA114) (psi (reg 1) (jOf114 sepRB114)),
     jOf114 sepRA114 == jOf114 sepRB114, BT.size sepRA114, BT.size sepRB114)
    = (true, true, true, false, true,
       true, true, true, false, true,
       true, true, false, true, 7, 8) := rfl

/-- **既知の三つの証人はどちらの半分に落ちるか。**  §81 の `cexA89`、§101 の
    `bothBadA101` は `b` も全発火しないので `VebRest114` の側、§101 の `scBadA101`
    は `b` が全発火するので `VebIngF114` の側。**どちらの半分も空ではない。**
    そして `scBadA101` の側の破れは**引き分け** — 値が等しい。 -/
theorem knownSplit114 :
    (lastFire92 (dict cexB89), lastFire92 (dict bothBadB101), lastFire92 (dict scBadB101),
     collapse 0 (hiW89 (dict scBadA101)) == collapse 0 (hiW89 (dict scBadB101)),
     lt (collapse 0 (hiW89 (dict scBadB101))) (collapse 0 (hiW89 (dict scBadA101))),
     VebIng114 (dict scBadA101) (psi (reg 1) (jOf114 scBadB101)))
    = (false, false, true, true, false, false) := rfl

end

/-! ### §114.5 測定 (凍結)

**構成 — §109 の二本の線 (縮めたもの) に、三本目を組んで足す。**  §109 の母集団は「発火する線」と
「発火しない線」だけで、`a` の折り畳みが Veblen で終わりながら**指数の大きい**形が
入っていない。§114 の証人はまさにその形なので、それを種にした線を足す
(`mixSeed114`)。濾さない。

    fireSeed114  全発火する種 4 個 (§109 の `fireSeed109` の 4 個)
    vebSeed114   発火しない種 3 個 (§109 の `vebSeed109` の 3 個)
    mixSeed114   `revA114` とその親戚 3 個 (`ψ₁` の中に `ψ₀` を入れて指数を上げる)
    pop114       その 2 項和も入れた 65 項  濾さない

`popNo114` は `mixSeed114` を抜いた 35 項で、**組んだ線が要ることの受領**である。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

private def dedup114 (l : List BT) : List BT :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []
private def w4_114 : BT := BT.D 1 w3_101
private def fireSeed114 : List BT :=
  [w2_101, w3_101, w4_114, BT.D 1 (BT.sum w3_101 w3_101)]
private def vebSeed114 : List BT :=
  [w1_101, BT.D 1 (BT.D 0 w1_101), BT.D 1 (BT.D 0 (BT.sum w2_101 w1_101))]
private def mixSeed114 : List BT :=
  [revA114, BT.D 1 (BT.sum (BT.D 1 (BT.D 0 w1_101)) (BT.D 1 BT.zero)),
   BT.D 1 (BT.D 1 (BT.D 0 w3_101))]
private def seeds114 : List BT := fireSeed114 ++ vebSeed114 ++ mixSeed114
private def widen114 (l : List BT) : List BT :=
  dedup114 (l ++ l.flatMap (fun a => (l.filter (fun b => BT.le b a)).map (BT.sum a)))
private def pop114 : List BT := widen114 seeds114
private def popNo114 : List BT := widen114 (fireSeed114 ++ vebSeed114)

private def ok114 (a : BT) : Bool := btLe72 1 a && BT.isStd a && le (reg 1) (dict a)
private def kstd114 (a : BT) : Bool := ok114 a && BT.isStd (BT.D 0 a)
private def samp114 : List BT := pop114.filter ok114
private def ksamp114 : List BT := pop114.filter kstd114
private def sampNo114 : List BT := popNo114.filter ok114
private def hasIdx114 (a : BT) : Bool := (idxF88 0 (dict a)).isSome
private def pairs114 (l : List BT) : List (BT × BT) :=
  l.flatMap (fun a => l.map (fun b => (a, b)))
/-- 残余 — `hi` が狭義に増え、しかも `a` の最後の対が発火しない対。§114 の担当分。 -/
private def resid114 (l : List BT) : List (BT × BT) :=
  (pairs114 l).filter (fun p =>
    lt (hiW89 (dict p.1)) (hiW89 (dict p.2)) && !lastFire92 (dict p.1))
private def concl114 (p : BT × BT) : Bool :=
  lt (collapse 0 (hiW89 (dict p.1))) (collapse 0 (hiW89 (dict p.2)))
private def bad114 (l : List BT) : List (BT × BT) := (resid114 l).filter (fun p => !concl114 p)
private def rev114 (p : BT × BT) : Bool :=
  lt (collapse 0 (hiW89 (dict p.2))) (collapse 0 (hiW89 (dict p.1)))
private def ingOK114 (p : BT × BT) : Bool :=
  VebIng114 (dict p.1) (psi (reg 1) (jOf114 p.2))

/-! 母集団の形。**65 項のうち指数を持つのは 30 項、全発火は 9 項、指数を持たない
    のが 35 項**で、`K` 標準は 46 項。 -/
#guard (pop114.length, samp114.length, ksamp114.length,
        samp114.countP hasIdx114, samp114.countP (fun a => lastFire92 (dict a)),
        samp114.countP (fun a => !hasIdx114 a)) == (65, 65, 46, 30, 9, 35)

/-! **受領 1 — 三つの場合がぜんぶ入っている。**  `a` が Veblen で終わる残余は 1974 組で、
    `b` が全発火 434 組、`b` は指数を持つが Veblen の尾がある 945 組、`b` が指数を
    持たない 595 組。**どの場合にも破れがある** (15 / 68 / 16) から、条項はどれも空虚でない。 -/
#guard ((resid114 samp114).length,
        ((resid114 samp114).filter (fun p => allFire101 (dict p.2))).length,
        ((resid114 samp114).filter (fun p => !allFire101 (dict p.2) && hasIdx114 p.2)).length,
        ((resid114 samp114).filter (fun p => !hasIdx114 p.2)).length) == (1974, 434, 945, 595)
#guard ((bad114 samp114).length,
        ((bad114 samp114).filter (fun p => allFire101 (dict p.2))).length,
        ((bad114 samp114).filter (fun p => !allFire101 (dict p.2) && hasIdx114 p.2)).length,
        ((bad114 samp114).filter (fun p => !hasIdx114 p.2)).length) == (99, 15, 68, 16)

/-! **受領 2 — `K` 標準では破れない。**  929 組の `K` 標準な残余 (263 / 546 / 120) で
    破れは 0。 -/
#guard ((resid114 ksamp114).length,
        ((resid114 ksamp114).filter (fun p => allFire101 (dict p.2))).length,
        ((resid114 ksamp114).filter (fun p => !allFire101 (dict p.2) && hasIdx114 p.2)).length,
        ((resid114 ksamp114).filter (fun p => !hasIdx114 p.2)).length,
        (bad114 ksamp114).length) == (929, 263, 546, 120, 0)

/-! **受領 3 — `VebIngF114` は払い過ぎていない。**  `b` が全発火する 263 組の `K` 標準な
    残余で `VebIng114` は一度も破れず、形の条件だけの 434 組では **`VebIng114` と結論が
    完全に一致する**: 「結論は真だが条項が偽」も「結論が偽だが条項は真」も 0 組。
    この半分では条項は十分条件であるだけでなく**必要条件**でもある。 -/
#guard (((resid114 ksamp114).filter (fun p => allFire101 (dict p.2))).length,
        ((resid114 ksamp114).filter (fun p => allFire101 (dict p.2))).countP
          (fun p => !ingOK114 p),
        ((resid114 samp114).filter (fun p => allFire101 (dict p.2))).countP
          (fun p => concl114 p && !ingOK114 p),
        ((resid114 samp114).filter (fun p => allFire101 (dict p.2))).countP
          (fun p => !concl114 p && ingOK114 p)) == (263, 0, 0, 0)

/-! **受領 4 — 一般の道具 `hiMono_bIdx114` がどこまで届くか。**  `b` が指数を持ちながら
    Veblen の尾を持つ `K` 標準な 546 組のうち、`ψ_{Ω₁}(j_b)` を的にして閉じるのは 483 組。
    残る 63 組が `sepR114` の形 — 的が狭すぎるところである。 -/
#guard (((resid114 ksamp114).filter (fun p => !allFire101 (dict p.2) && hasIdx114 p.2)).length,
        ((resid114 ksamp114).filter (fun p => !allFire101 (dict p.2) && hasIdx114 p.2)).countP
          ingOK114) == (546, 483)

/-! **受領 5 — `b` が全発火する半分の破れは、ほとんどが順序の逆転。**  15 組のうち
    14 組が逆転で 1 組が引き分け (§101 の `scBadA101` の形)。母集団ぜんぶでは
    92 組が逆転、7 組が引き分け。 -/
#guard (((bad114 samp114).filter (fun p => allFire101 (dict p.2))).length,
        ((bad114 samp114).filter (fun p => allFire101 (dict p.2))).countP rev114,
        (bad114 samp114).countP rev114,
        (bad114 samp114).countP (fun p => !rev114 p)) == (15, 14, 92, 7)

/-! **受領 6 — 証人は掃いて出したのではなく、組んだものである。**  `mixSeed114` を
    抜いた 35 項の母集団では、`b` が全発火する 194 組の残余に**破れが一つも無い** —
    逆転どころか引き分けも無い。同じ母集団に逆転は 15 組あるが、ぜんぶ他の二つの場合。
    §95 の教訓をそのまま。 -/
#guard (sampNo114.length, (resid114 sampNo114).length,
        ((resid114 sampNo114).filter (fun p => allFire101 (dict p.2))).length,
        ((bad114 sampNo114).filter (fun p => allFire101 (dict p.2))).length,
        ((bad114 sampNo114).filter (fun p => allFire101 (dict p.2))).countP rev114,
        (bad114 sampNo114).countP rev114) == (35, 519, 194, 0, 0, 15)

/-! **受領 7 — 組んだ証人は母集団の中で最小。**  `b` が全発火する逆転はどれも
    記号数の和が 14 以上で、`(revA114, revB114)` はその 14 を実現している。 -/
#guard ((bad114 samp114).filter (fun p => allFire101 (dict p.2) && rev114 p)).all
  (fun p => 14 ≤ BT.size p.1 + BT.size p.2)
#guard ((bad114 samp114).filter (fun p => allFire101 (dict p.2) && rev114 p)).contains
  (revA114, revB114)

end

/-! ## §113 THE COEFFICIENT HALF IS A THEOREM — `Γ₀` IS CLOSED ALONG THE FOLD, AND THE
       WINDOW HAS A THIRD ROUTE

§108 reduced `GapAtG0_107` to one clause `SCFirst108`; §111 proved that clause EQUIVALENT to
its one-component form `SCFirstOne111`, closed the CARRIER half (`Gam0Drags111` +
`carrier_notStd111`, no shape restriction left) and left the other half named but untouched:

> a value in the window with a leading digit BELOW `Γ₀` needs a coefficient already in the
> window, which is an induction on the term's size.

**§113 proves that half.**  It is not an induction on the term's size: it is one closure
property of `Γ₀` along the fold, and the whole of it is `lt_phi_gT113` — 2.3.13(i) read at
the target `φ̄(Γ₀,R)`.  §113 then BUILDS the term §111 said might exist and could not find,
and that term refutes two things §108 and §111 had believed.

  §113.1  **THE TARGET IS `φ̄(Γ₀,R)` AND THE ARITHMETIC CLOSES UNDER IT.**  2.3.13(i) says
          `φ̄(a,b) < φ̄(Γ₀,R) ↔ b < φ̄(Γ₀,R)` as soon as `a < Γ₀` — the FIRST argument drops
          out of the comparison entirely (`lt_phi_gT113`).  With 2.3.10 (`lt_add_gT113`)
          that closes `ofList`, `plus`, `ofNat`, `sub1`, `splitFin`, `phiNFdefault`,
          `phiNFsucc`, `phiNF` and `ω^·` under "below `φ̄(Γ₀,R)`" — §79's development for
          `Ω₁`, repeated at a Veblen target.  `R` is free, so the same lemmas serve the
          window's BOTTOM (`R = 0`) and its TOP (`R = Γ₀⊕1`).

  §113.2  **THE FOLD NEVER LEAVES.**  `StG113` is the invariant "the accumulator is below the
          target"; `stepG113` proves one step keeps it, from `lt a Γ₀` on the pair's exponent
          — which also kills the strongly critical branch, since `Γ₀ < Ω₁` — and `lt c` on
          its coefficient.  `foldG113` runs it along the whole digit list.  **Nothing here
          is an induction on a Buchholz term.**

  §113.3  **AND `wcnf` DOES NOT EITHER.**  `wcnfG113` carries the same two conditions through
          the base-`Ω₁` decomposition, merging included, and `collapse0_facts113` closes the
          outer `ω^·`: **if every digit exponent is below `Γ₀` and every coefficient and the
          sub-`Ω₁` tail are below `φ̄(Γ₀,R)`, then `ψ₀`'s value is below `φ̄(Γ₀,R)`.**

  §113.4  **THE COEFFICIENT HALF, NAMED.**  At `R = 0` the target is the window's bottom
          `φ̄(Γ₀,0)`, and the contrapositive is the clause §111 asked for:
          `coefWin113` — a value that reaches the window forces one of exactly three things,
          and `badP113` decides which: a digit exponent at or above `Γ₀` (§111's carrier
          half, on the 𝔗(M) side — **the bridge from that to §111's Buchholz-side
          `carrier_notStd111` is NOT proved here**), a digit COEFFICIENT at or above the
          window's BOTTOM, or a sub-`Ω₁` component at or above it.  "In the window" is read
          as "at or above the window's bottom": the upper side would follow from `UpProp113`
          (§113.6) and is NOT claimed.  `scFirstOne_needs113` hands that witness to `SCFirstOne111` for
          free, and `winProp_iff_scFirstOne113` says the hand-over loses nothing: the clause
          may now ASSUME the witness.  **This removes residue rather than moving it** — the
          half is proved, not reduced to something else.

  §113.5  **THE THIRD ROUTE INTO THE WINDOW, BUILT.**  §111 warned that its two families
          might not be all of them.  They are not.  `cCoef113 w = ψ₀(ψ₁ w)` puts a
          window-valued term under a single `ψ₁`: at `w = bWin108 1` the digit is
          `Ω₁^1 · φ̄(Γ₀,1)` — **exponent `1`, far below `Γ₀`; the whole of the window value is
          in the COEFFICIENT** — and `dict (cCoef113 (bWin108 1)) = φ̄(Γ₀,1)`, inside the
          window.  §108's populations C and D, §111's F and G — 2966 terms — contain 0 of
          this shape.  And prefixing `Ω^Ω` does NOT repair it:
          `cJump113 = ψ₀(Ω^Ω ⊕ ψ₁(bWin108 1))` still has value `φ̄(Γ₀,1)`, **and it satisfies
          `ψ₀(Ω^Ω) < ·`.**  Two consequences:

            * `scFirstOneNoStd_false113` : the ONE-COMPONENT clause cannot be stated without
              `isStd` either.  §108 showed this for the sum form (`bad108`, two `ψ₀`
              components); §111 wrote that the premise `ψ₀(Ω^Ω) < b` "removes every one of
              the near-misses on its own".  **That was a statement about F, not about the
              shape**: `cJump113` satisfies the premise and sits in the window.
            * `leadSCJumps_false113` : `cJump113`'s leading base-`Ω₁` digit exponent IS at or
              above `Ω₁`, so the fold DOES take its strongly critical branch first — and the
              value is in the window anyway.  §107's reason, refuted a second time and now
              WITH the premise §108 added.  The mechanism is visible: `plus` drops the
              accumulator when the next coefficient is bigger, so "the base is `Γ₀`, hence
              later Veblen digits land at `φ̄(a,Γ₀⊕c)`" fails exactly when a coefficient
              outruns the base.

          What stops both is standardness, and §113.5 says where: `notStd_cCoef113` — the
          coefficient route needs a STANDARD term of window value inside the `ψ₁`, and
          `isStd` is hereditary, so **the coefficient route is literally the induction
          hypothesis.**  That is the honest content of "an induction on the term's size".

  §113.6  **WHAT IS LEFT, NAMED AND MEASURED.**  With the coefficient half proved, what
          `SCFirstOne111` still needs is one arithmetical clause, `UpProp113`: a `ψ₀`
          argument that carries something at or above the window's TOP has value at or above
          the window's top.  It is the propagation step the size induction consumes, and it
          is NOT proved here (30/30 and 9992/9992, premise firing 9 and 1718).

WHAT IS **NOT** CLAIMED.  **`SCFirstOne111` is NOT proved and NOT refuted, and neither is
`SCFirst108` or `GapAtG0_107`.**  `UpProp113` and `Gam0Drags111` are measured, not proved.
`cCoef113` and `cJump113` are NOT counterexamples to anything: §113.5 proves neither is
standard.  `DictDenseMid107`, `DictDenseMid102`, `DictDenseHi94`, `DictDense85`, `CofDenseS1`
and row 326's certificate are exactly where §111 left them — row 326 still depends on
`SCFirst108`, now equivalently on `WinProp113`, through `gap_of108`.  `PsiIdxOKStd172` and
`DictLtA74` are used, not proved.  §113 does not touch §103's hole and does not reach
`FoldSkips108`.

**Where §113 stopped, precisely, and what moved.**  §111 left two halves; §113 pays one of
them in full and finds it was cheaper than advertised — the `Γ₀`-closure of the Veblen layer,
not an induction — and then shows the neighbourhood is again wider than the last measurement
saw.  **The residue did shrink**: `SCFirstOne111` is now equivalent to a clause that may
assume a named, decidable witness, and the three shapes that witness can take are separated,
one of them blocked outright (the hereditary argument for the coefficient, §113.5) and one
matching §111's carrier half in content though not yet in form (the exponent at `Γ₀`; the
𝔗(M)-side clause and §111's Buchholz-side theorem are not bridged here).  What is genuinely left is `UpProp113` plus the bookkeeping
that turns "at or above the bottom" into "at or above the top" — and §113.5 says why that
bookkeeping is the induction and not an oversight.

**AND THE OVERPAYMENT LEDGER.**  §113 found one: §111's reading that the premise
`ψ₀(Ω^Ω) < b` "removes every one of the near-misses on its own" was paid for by F, and F
could not see the shape that breaks it.  The seventh entry.

WHAT THE MEASUREMENT SAYS (§113.7 gives the construction).  One population is BUILT and one
is re-read.  **Q** is the third route at 10 window-and-above seeds in three shapes — bare
`ψ₀(ψ₁ w)`, the `Ω^Ω` repair `ψ₀(Ω^Ω ⊕ ψ₁ w)`, and (as a CONTROL) `w` moved out of the `ψ₁`
into the tail `ψ₀(Ω^Ω ⊕ w)` — 30 terms, **not filtered by standardness**.  **E** is §108.6's
enumeration of every standard level-`≤ 1` term of size `≤ 12` (9992), re-read.

  * **12 of Q's 30 land in the window, 4 in each shape — and 8 of those 12 satisfy
    `ψ₀(Ω^Ω) < ·`.**  §111's F had 13 in the window and 0 with the premise.
  * **The coefficient clause fires ALONE on 7 of the 10 bare terms and on 0 of the other 20.**
    Moving `w` out of the `ψ₁` (the control) switches the clause from the coefficient to the
    tail: 0 coefficient-only, 7 tail.  So it is the `ψ₁` and nothing else that turns a window
    value into a coefficient.
  * **All 30 are level `≤ 1`, `D 0`-headed and `inT`; 7 are standard; and 0 of the 12 in the
    window are legal witnesses.**  The 6 that are legal AND satisfy the premise all have
    values BELOW the window's bottom.
  * **§108's populations C and D and §111's F and G contain 0 terms of the new shape, out of
    1463, 1463, 30 and 10.**  E contains 483 — and cannot contain a dangerous one, because
    the shape is dangerous exactly when the term inside the `ψ₁` is a window carrier, and
    those are not standard.  The seed problem, one level up from §111's.
  * **The two known families fire only the carrier clause.**  On §108.1's `bWin108` at four
    rungs and on all ten of §111.2's `cWin111`, the exponent clause fires and the coefficient
    and tail clauses do not.  **So the coefficient half is about a route neither family
    contains** — which is why it had to be built.
  * **The clause's hypothesis is visible on E, both ways.**  `badP113` fires on 4587 of E's
    9992 and does not on 5405.  Restricted to the 5318 that are legal `ψ₀` arguments it fires
    on 3 and fires ALONE on 0 — the coefficient route is nearly invisible among standard
    terms, exactly as the hereditary argument predicts.
  * **E confirms the clause it cannot test.**  2606 of E's terms give a legal `ψ₀(z)` with
    `ψ₀(Ω^Ω) < ψ₀(z)`; 0 land in the window and 0 break `SCFirstOne111`.
  * **`UpProp113` holds 30/30 on Q and 9992/9992 on E, with the premise firing 9 and 1718.**
    Not a clean sweep of a vacuous hypothesis.
  * **The digit exponents descend** on §108's family at four rungs, on all ten of §111's, on
    §98's tower and on the new family — so "the LEADING digit is below `Γ₀`" and "every digit
    is below `Γ₀`" are the same hypothesis on everything measured. -/

/-! ### §113.1 的 `φ̄(Γ₀,R)` の下で閉じる算術

2.3.13(i) は「指数が `Γ₀` より下なら、`φ̄(Γ₀,R)` との比較は第 2 引数だけで決まる」と言う。
第 1 引数は比較から**消える**。これと 2.3.10 だけで、`plus`・`ofList`・`sub1`・`phiNF`・
`ω^·` が全部この的の下で閉じる。§79 が `Ω₁` について書いたものを Veblen の的で書き直した
だけで、`R` は自由だから窓の下端と上端の両方に使える。 -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- 窓の下端・上端をまとめて扱う的 — `φ̄(Γ₀,R)`。 -/
def gT113 (R : Term) : Term := phi G094 R

theorem gT113_zero : gT113 zero = rawT94 0 := rfl
theorem gT113_top : gT113 (plus G094 TM.Term.one) = dict (bTowG98 1) := rfl

theorem isAP_gT113 (R : Term) : (gT113 R).isAP = true := rfl

theorem ne_G0_of_lt113 {a : Term} (ha : lt a G094 = true) : a ≠ G094 := by
  intro hc
  rw [hc, lt_irrefl] at ha
  exact Bool.noConfusion ha

/-- **2.3.13(i) を等式で。**  指数が `Γ₀` より下なら `φ̄(Γ₀,R)` との比較は第 2 引数だけで決まる。 -/
theorem lt_phi_gT113 {a b : Term} (R : Term) (ha : lt a G094 = true) :
    lt (phi a b) (gT113 R) = lt b (gT113 R) := by
  have hne : a ≠ G094 := ne_G0_of_lt113 ha
  have hne2 : phi a b ≠ phi G094 R := by
    intro hc; injection hc with h1 _; exact hne h1
  show lt (phi a b) (phi G094 R) = lt b (phi G094 R)
  rw [lt_eq_ltF_succ, ltF_succ_phi_phi _ hne2, if_neg hne,
    if_pos (by
      rw [show ltF (2 * ((phi a b).deg + (phi G094 R).deg) + 7) a G094 = lt a G094 from
        (lt_eq_ltF a G094 _ (by
          show a.deg + G094.deg ≤ 2 * ((1 + a.deg + b.deg) + (1 + G094.deg + R.deg)) + 7
          omega)).symm]
      exact ha),
    show ltF (2 * ((phi a b).deg + (phi G094 R).deg) + 7) b (phi G094 R)
        = lt b (phi G094 R) from
      (lt_eq_ltF b (phi G094 R) _ (by
        show b.deg + (1 + G094.deg + R.deg)
          ≤ 2 * ((1 + a.deg + b.deg) + (1 + G094.deg + R.deg)) + 7
        omega)).symm]

/-- 和は頭で決まる。 -/
theorem lt_add_gT113 (a b : Term) (R : Term) :
    lt (add a b) (gT113 R) = lt a (gT113 R) := lt_add_ap102 a b (isAP_gT113 R)

theorem lt_zero_gT113 (R : Term) : lt zero (gT113 R) = true :=
  lt_zero_left (by intro hc; exact Term.noConfusion hc)

theorem lt_ofList_gT113 (R : Term) : ∀ (l : List Term), (∀ x ∈ l, lt x (gT113 R) = true) →
    lt (ofList l) (gT113 R) = true
  | [], _ => lt_zero_gT113 R
  | [a], h => h a (List.Mem.head _)
  | a :: b :: t, h => by
    show lt (add a (ofList (b :: t))) (gT113 R) = true
    rw [lt_add_gT113]
    exact h a (List.Mem.head _)


/-- 的が 𝔗(M) の項であること。 -/
theorem inT_gT113 {R : Term} (hR : inT R = true) (hRM : lt R M = true) :
    inT (gT113 R) = true := by
  show (inT G094 && inT R && lt G094 M && lt R M) = true
  rw [inT_G094_102, hR, hRM, show lt G094 M = true from by decide]
  rfl

theorem ltG_of_le113 {R y a : Term} (hiT : inT (gT113 R) = true) (hy : inT y = true)
    (ha : inT a = true) (hle : le y a = true) (hla : lt a (gT113 R) = true) :
    lt y (gT113 R) = true :=
  lt_of_le_of_lt3 (inT_le_fragR y hy) (inT_le_fragR a ha) (inT_le_fragR _ hiT) hle hla

theorem ltG_of_hdLe113 {R : Term} (hiT : inT (gT113 R) = true) :
    ∀ {a b : Term}, inT a = true → inT b = true → hdLe b a = true →
      lt a (gT113 R) = true → lt b (gT113 R) = true := by
  intro a b hia hib hhd hla
  cases b with
  | zero => exact Bool.noConfusion hhd
  | M => exact ltG_of_le113 hiT hib hia hhd hla
  | omg c => exact ltG_of_le113 hiT hib hia hhd hla
  | phi c d => exact ltG_of_le113 hiT hib hia hhd hla
  | psi c d => exact ltG_of_le113 hiT hib hia hhd hla
  | Z c => exact ltG_of_le113 hiT hib hia hhd hla
  | add c d =>
    obtain ⟨_, hic, _, _⟩ := inT_add hib
    rw [lt_add_gT113]
    exact ltG_of_le113 hiT hic hia hhd hla

/-- 的より下の項の成分はすべて的より下。 -/
theorem ltG_toList113 {R : Term} (hiT : inT (gT113 R) = true) :
    ∀ (s : Term), inT s = true → lt s (gT113 R) = true →
      ∀ x ∈ toList s, lt x (gT113 R) = true := by
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
    have hla : lt a (gT113 R) = true := by rw [← lt_add_gT113 a b R]; exact hl
    have hlb : lt b (gT113 R) = true := ltG_of_hdLe113 hiT hia hib hhd hla
    rcases List.mem_cons.mp (show x ∈ a :: toList b from hx) with h1 | h1
    · rw [h1]; exact hla
    · exact ihb hib hlb x h1

/-- **`plus` は的の下で閉じる。** -/
theorem lt_plus_gT113 {R s t : Term} (hiT : inT (gT113 R) = true)
    (hs : inT s = true) (ht : inT t = true)
    (hls : lt s (gT113 R) = true) (hlt : lt t (gT113 R) = true) :
    lt (plus s t) (gT113 R) = true := by
  cases hl : toList t with
  | nil => rw [show plus s t = s from by unfold TM.Term.plus; rw [hl]]; exact hls
  | cons b1 rest =>
    rw [plus_eq (s := s) hl]
    refine lt_ofList_gT113 R _ ?_
    intro x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact ltG_toList113 hiT s hs hls x (List.mem_filter.mp h1).1
    · exact ltG_toList113 hiT t ht hlt x h1

theorem lt_zero_G0_113 : lt (zero : Term) G094 = true :=
  lt_zero_left (by intro hc; exact Term.noConfusion hc)

theorem lt_one_gT113 (R : Term) : lt TM.Term.one (gT113 R) = true := by
  show lt (phi zero zero) (gT113 R) = true
  rw [lt_phi_gT113 R lt_zero_G0_113]
  exact lt_zero_gT113 R

theorem lt_ofNat_gT113 {R : Term} (hiT : inT (gT113 R) = true) : ∀ n,
    lt (TM.Term.ofNat n) (gT113 R) = true
  | 0 => lt_zero_gT113 R
  | n + 1 => lt_plus_gT113 hiT (inT_ofNat n) inT_one (lt_ofNat_gT113 hiT n) (lt_one_gT113 R)


theorem lt_G0_gT113 (R : Term) : lt G094 (gT113 R) = true :=
  lt_psi_phi_of_le_fst102 (le_self G094)

theorem ltG_take_ofList113 {R b : Term} (hiT : inT (gT113 R) = true) (h : inT b = true)
    (hl : lt b (gT113 R) = true) (k : Nat) :
    lt (ofList ((toList b).take k)) (gT113 R) = true :=
  lt_ofList_gT113 R _ (fun x hx => ltG_toList113 hiT b h hl x (List.mem_of_mem_take hx))

theorem ltG_splitFin113 {R b : Term} (hiT : inT (gT113 R) = true) (h : inT b = true)
    (hl : lt b (gT113 R) = true) : lt (splitFin b).1 (gT113 R) = true :=
  ltG_take_ofList113 hiT h hl _

theorem lt_phiNFdefault113 {R a b : Term} (hiT : inT (gT113 R) = true) (hia : inT a = true)
    (ha : lt a G094 = true) (hb : lt b (gT113 R) = true) :
    lt (phiNFdefault a b) (gT113 R) = true := by
  unfold phiNFdefault
  split
  · exact lt_trans_inT hia inT_G094_102 hiT ha (lt_G0_gT113 R)
  · rw [lt_phi_gT113 R ha]; exact hb

theorem lt_phiNFsucc113 {R a b : Term} (hiT : inT (gT113 R) = true) (hia : inT a = true)
    (hib : inT b = true) (ha : lt a G094 = true) (hb : lt b (gT113 R) = true) :
    lt (phiNFsucc a b) (gT113 R) = true := by
  have hg : lt (splitFin b).1 (gT113 R) = true := ltG_splitFin113 hiT hib hb
  have hig : inT (splitFin b).1 = true := inT_splitFin hib
  have hdef := lt_phiNFdefault113 hiT hia ha hb
  have hdown : ∀ n : Nat, lt (phi a (plus (splitFin b).1 (TM.Term.ofNat n))) (gT113 R) = true := by
    intro n
    rw [lt_phi_gT113 R ha]
    exact lt_plus_gT113 hiT hig (inT_ofNat n) hg (lt_ofNat_gT113 hiT n)
  unfold phiNFsucc
  split
  rename_i heq
  rw [heq] at hdown
  split
  · split <;> (split <;> first | exact hdown _ | exact hdef)
  · exact hdef

/-- **`φ` の正規化は的の下で閉じる** — 指数が `Γ₀` より下なら。 -/
theorem lt_phiNF113 {R a b : Term} (hiT : inT (gT113 R) = true) (hia : inT a = true)
    (hib : inT b = true) (ha : lt a G094 = true) (hb : lt b (gT113 R) = true) :
    lt (phiNF a b) (gT113 R) = true := by
  unfold phiNF
  split
  · exact hb
  · split
    · split
      · exact hb
      · exact lt_phiNFsucc113 hiT hia hib ha hb
    · exact lt_phiNFsucc113 hiT hia hib ha hb

/-- **`ω^·` は的の下で閉じる。** -/
theorem lt_omegaNF113 {R x : Term} (hiT : inT (gT113 R) = true) (hix : inT x = true)
    (hxM : lt x M = true) (hx : lt x (gT113 R) = true) :
    lt (omegaNF x) (gT113 R) = true := by
  have hMx : lt M x = false := lt_asymm_inT hix (show inT (M : Term) = true from rfl) hxM
  have hxne : (x == M) = false := by
    cases hb : (x == M) with
    | false => rfl
    | true =>
        exfalso
        rw [eq_of_beq hb, lt_irrefl] at hxM
        exact Bool.noConfusion hxM
  show lt (if lt M x then omg x else if x == M then M else phiNF zero x) (gT113 R) = true
  rw [if_neg (by rw [hMx]; exact Bool.noConfusion),
    if_neg (by rw [hxne]; exact Bool.noConfusion)]
  exact lt_phiNF113 hiT inT_zero hix lt_zero_G0_113 hx

/-- `sub1` は的の下から出ない。 -/
theorem lt_sub1_113 {R c : Term} (hiT : inT (gT113 R) = true) (hic : inT c = true)
    (hc : lt c (gT113 R) = true) : lt (sub1 c) (gT113 R) = true := by
  show lt (match toList c with
           | [] => zero
           | p :: rest => if p == TM.Term.one then ofList rest else c) (gT113 R) = true
  cases hl : toList c with
  | nil => exact lt_zero_gT113 R
  | cons p rest =>
      show lt (if (p == TM.Term.one) = true then ofList rest else c) (gT113 R) = true
      by_cases hp : (p == TM.Term.one) = true
      · rw [if_pos hp]
        refine lt_ofList_gT113 R rest ?_
        intro x hx
        exact ltG_toList113 hiT c hic hc x (by rw [hl]; exact List.Mem.tail _ hx)
      · rw [if_neg hp]; exact hc


end

/-! ### §113.2 畳み込みは的の下から出ない

`stepF` の Veblen 枝は `phiNF a (前の値 ⊕ 係数)` を出す。指数が `Γ₀` より下なら
`Γ₀ < Ω₁` だから強臨界枝は死んでいて、あとは §113.1 の閉包がそのまま効く。 -/
section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

theorem lt_G0_W113 : lt G094 (reg 1) = true := lt_psi_W79 zero

/-- 畳み込みの累算器が満たす不変量 — 「的より下」を `inT` と `< M` と一緒に運ぶ。 -/
def StG113 (R : Term) (s : Option Term × Option Term) : Prop :=
  ∀ v, s.2 = some v → inT v = true ∧ lt v M = true ∧ lt v (gT113 R) = true

theorem stepVal113 {R a bse cc : Term} (hiT : inT (gT113 R) = true)
    (hia : inT a = true) (haM : lt a M = true) (haG : lt a G094 = true)
    (hib : inT bse = true) (hbM : lt bse M = true) (hbG : lt bse (gT113 R) = true)
    (hic : inT cc = true) (hcM : lt cc M = true) (hcG : lt cc (gT113 R) = true) :
    inT (phiNF a (plus bse cc)) = true ∧ lt (phiNF a (plus bse cc)) M = true
      ∧ lt (phiNF a (plus bse cc)) (gT113 R) = true := by
  have hip : inT (plus bse cc) = true := inT_plus hib hic
  have hpM : lt (plus bse cc) M = true := lt_plus_M hib hic hbM hcM
  have hpG : lt (plus bse cc) (gT113 R) = true := lt_plus_gT113 hiT hib hic hbG hcG
  exact ⟨inT_phiNF hia hip haM hpM, ltM_phiNF haM hpM,
    lt_phiNF113 hiT hia hip haG hpG⟩

/-- **畳み込みの一歩は的の下から出ない** — 指数が `Γ₀` より下で係数が的より下なら。 -/
theorem stepG113 {R : Term} (hiT : inT (gT113 R) = true) {s : Option Term × Option Term}
    {ac : Term × Term}
    (hia : inT ac.1 = true) (haM : lt ac.1 M = true) (haG : lt ac.1 G094 = true)
    (hic : inT ac.2 = true) (hcM : lt ac.2 M = true) (hcG : lt ac.2 (gT113 R) = true)
    (hs : StG113 R s) : StG113 R (stepF (reg 1) (baseOf 0) s ac) := by
  have hleW : le (reg 1) ac.1 = false :=
    leW_false106 hia (lt_trans_inT hia inT_G094_102 inT_W79 haG lt_G0_W113)
  unfold stepF
  split
  · rename_i hle
    exfalso; rw [hleW] at hle; exact Bool.noConfusion hle
  · cases hs2 : s.2 with
    | none =>
        intro v hv
        rw [← Option.some.inj
          (show some (phiNF ac.1 (plus (baseOf 0) (sub1 ac.2))) = some v from hv)]
        exact stepVal113 hiT hia haM haG (inT_baseOf 0) (ltM_baseOf 0)
          (show lt (baseOf 0) (gT113 R) = true from lt_zero_gT113 R)
          (inT_sub1 hic) (ltM_sub1 hic hcM) (lt_sub1_113 hiT hic hcG)
    | some v0 =>
        obtain ⟨hiv0, hv0M, hv0G⟩ := hs v0 hs2
        intro v hv
        rw [← Option.some.inj (show some (phiNF ac.1 (plus v0 ac.2)) = some v from hv)]
        exact stepVal113 hiT hia haM haG hiv0 hv0M hv0G hic hcM hcG

/-- 畳み込み全体。 -/
theorem foldG113 {R : Term} (hiT : inT (gT113 R) = true) :
    ∀ (l : List (Term × Term)) (s : Option Term × Option Term), StG113 R s →
      (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ lt ac.1 G094 = true ∧
        inT ac.2 = true ∧ lt ac.2 M = true ∧ lt ac.2 (gT113 R) = true) →
      StG113 R (l.foldl (stepF (reg 1) (baseOf 0)) s)
  | [], _, hs, _ => hs
  | ac :: t, s, hs, hall => by
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hall ac (List.Mem.head _)
      exact foldG113 hiT t (stepF (reg 1) (baseOf 0) s ac)
        (stepG113 hiT h1 h2 h3 h4 h5 h6 hs)
        (fun a ha => hall a (List.Mem.tail _ ha))


end

/-! ### §113.3 `wcnf` から `collapse 0` へ

底 `Ω₁` の分解も同じ二条件を運ぶ — 桁の併合 (`plus (wC w p) c'`) も的の下で閉じるから。
外側の `ω^·` を閉じれば `ψ₀` の値そのものが的の下に入る。 -/
section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- `wcnf` の対と尾が的の下にとどまる条件。 -/
theorem wcnfG113 {R : Term} (hiT : inT (gT113 R) = true) :
    ∀ (L : List Term), inTL L = true → descL L = true → (∀ x ∈ L, lt x M = true) →
      (∀ p ∈ L, lt p (reg 1) = true → lt p (gT113 R) = true) →
      (∀ p ∈ L, lt p (reg 1) = false →
        lt (wA (reg 1) p) G094 = true ∧ lt (wC (reg 1) p) (gT113 R) = true) →
      (∀ ac ∈ (wcnf (reg 1) L).1, lt ac.1 G094 = true ∧ lt ac.2 (gT113 R) = true)
        ∧ lt (wcnf (reg 1) L).2 (gT113 R) = true := by
  intro L
  induction L with
  | nil =>
    intro _ _ _ _ _
    exact ⟨(by intro ac hac; cases hac), lt_zero_gT113 R⟩
  | cons p rest ih =>
    intro hc hd hM hlo hhi
    obtain ⟨⟨hap, hip⟩, hcr⟩ := inTL_cons.mp hc
    have hdr := descL_tail hd
    by_cases hlp : lt p (reg 1) = true
    · rw [wcnf_cons_lt hlp]
      refine ⟨(by intro ac hac; cases hac), ?_⟩
      refine lt_ofList_gT113 R _ ?_
      intro x hx
      rcases List.mem_cons.mp hx with h1 | h1
      · rw [h1]; exact hlo p (List.Mem.head _) hlp
      · have hix : inT x = true := ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcr x h1)).2
        have hle := descL_bound_inT rest p hip hcr hd x h1
        exact hlo x (List.Mem.tail _ h1) (ltW_of_le79 hix hip hle hlp)
    · have hlp' : lt p (reg 1) = false := bool_false hlp
      obtain ⟨hwA, hwC⟩ := hhi p (List.Mem.head _) hlp'
      have IH := ih hcr hdr (fun q hq => hM q (List.Mem.tail _ hq))
        (fun q hq => hlo q (List.Mem.tail _ hq))
        (fun q hq => hhi q (List.Mem.tail _ hq))
      have hiwC : inT (wC (reg 1) p) = true := inT_wC hip
      rw [wcnf_cons_ge hlp']
      cases hr : wcnf (reg 1) rest with
      | mk fst snd =>
        rw [hr] at IH
        obtain ⟨hall, hsnd⟩ := IH
        cases fst with
        | nil =>
          refine ⟨?_, hsnd⟩
          intro ac hac
          rw [List.mem_singleton.mp hac]
          exact ⟨hwA, hwC⟩
        | cons ac0 ps =>
          cases ac0 with
          | mk a' c' =>
            have hac0 := hall (a', c') (List.Mem.head _)
            have hic' : inT c' = true := by
              have hPO := wcnf_spec_sc (inT_reg 1) (show (reg 1).isSC = true from rfl)
                rest hcr hdr (fun x hx => hM x (List.Mem.tail _ hx))
              rw [hr] at hPO
              exact (hPO.2 (a', c') (List.Mem.head _)).2.2.1
            show (∀ ac ∈ (if (wA (reg 1) p == a') = true
                then ((wA (reg 1) p, plus (wC (reg 1) p) c') :: ps, snd)
                else ((wA (reg 1) p, wC (reg 1) p) :: (a', c') :: ps, snd)).1,
                lt ac.1 G094 = true ∧ lt ac.2 (gT113 R) = true)
              ∧ lt (if (wA (reg 1) p == a') = true
                then ((wA (reg 1) p, plus (wC (reg 1) p) c') :: ps, snd)
                else ((wA (reg 1) p, wC (reg 1) p) :: (a', c') :: ps, snd)).2 (gT113 R) = true
            by_cases heq : (wA (reg 1) p == a') = true
            · rw [if_pos heq]
              refine ⟨?_, hsnd⟩
              intro ac hac
              rcases List.mem_cons.mp hac with h1 | h1
              · rw [h1]
                exact ⟨hwA, lt_plus_gT113 hiT hiwC hic' hwC hac0.2⟩
              · exact hall ac (List.Mem.tail _ h1)
            · rw [if_neg heq]
              refine ⟨?_, hsnd⟩
              intro ac hac
              rcases List.mem_cons.mp hac with h1 | h1
              · rw [h1]; exact ⟨hwA, hwC⟩
              · exact hall ac h1


/-- **§113 の主定理 (1)。**  底 `Ω₁` の展開の**桁の指数がどれも `Γ₀` より下**で、
    **係数と尾がどれも `φ̄(Γ₀,R)` より下**なら、`ψ₀` の値も `φ̄(Γ₀,R)` より下である。 -/
theorem collapse0_facts113 {R x : Term} (hiT : inT (gT113 R) = true)
    (hx : inT x = true) (hxM : lt x M = true)
    (hlo : ∀ p ∈ toList x, lt p (reg 1) = true → lt p (gT113 R) = true)
    (hhi : ∀ p ∈ toList x, lt p (reg 1) = false →
      lt (wA (reg 1) p) G094 = true ∧ lt (wC (reg 1) p) (gT113 R) = true) :
    inT (collapse 0 x) = true ∧ lt (collapse 0 x) (gT113 R) = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  have hM := ltM_toList x hx hxM
  obtain ⟨hallG, hrhoG⟩ := wcnfG113 hiT (toList x) hc hd hM hlo hhi
  obtain ⟨⟨hrhoT, hrhoM⟩, hallOK⟩ :=
    wcnf_spec_sc (inT_reg 1) (show (reg 1).isSC = true from rfl) (toList x) hc hd hM
  have hinit : StG113 R ((none : Option Term), (none : Option Term)) := by intro v h; cases h
  have hst := foldG113 hiT (wcnf (reg 1) (toList x)).1 (none, none) hinit
    (fun ac hac => ⟨(hallOK ac hac).1, (hallOK ac hac).2.1, (hallG ac hac).1,
      (hallOK ac hac).2.2.1, (hallOK ac hac).2.2.2, (hallG ac hac).2⟩)
  have hacc : inT (accW89 x) = true ∧ lt (accW89 x) M = true
      ∧ lt (accW89 x) (gT113 R) = true := by
    unfold accW89
    cases hg : ((wcnf (reg 1) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2 with
    | none => exact ⟨inT_zero, lt_zero_M, lt_zero_gT113 R⟩
    | some v => exact hst v hg
  have hrT : inT (rhoW89 x) = true := hrhoT
  have hrM : lt (rhoW89 x) M = true := hrhoM
  have hrG : lt (rhoW89 x) (gT113 R) = true := hrhoG
  have hs1 : inT (plus (accW89 x) (rhoW89 x)) = true := inT_plus hacc.1 hrT
  have hs2 : lt (plus (accW89 x) (rhoW89 x)) M = true := lt_plus_M hacc.1 hrT hacc.2.1 hrM
  have hs3 : lt (plus (accW89 x) (rhoW89 x)) (gT113 R) = true :=
    lt_plus_gT113 hiT hacc.1 hrT hacc.2.2 hrG
  rw [collapse0_raw89]
  exact ⟨inT_omegaNF (inT_plus inT_zero hs1),
    lt_omegaNF113 hiT (inT_plus inT_zero hs1)
      (lt_plus_M inT_zero hs1 lt_zero_M hs2)
      (lt_plus_gT113 hiT inT_zero hs1 (lt_zero_gT113 R) hs3)⟩


/-- 値の側だけ。 -/
theorem collapse0_ltG113 {R x : Term} (hiT : inT (gT113 R) = true)
    (hx : inT x = true) (hxM : lt x M = true)
    (hlo : ∀ p ∈ toList x, lt p (reg 1) = true → lt p (gT113 R) = true)
    (hhi : ∀ p ∈ toList x, lt p (reg 1) = false →
      lt (wA (reg 1) p) G094 = true ∧ lt (wC (reg 1) p) (gT113 R) = true) :
    lt (collapse 0 x) (gT113 R) = true := (collapse0_facts113 hiT hx hxM hlo hhi).2

theorem not_le_of_lt113 {a b : Term} (ha : inT a = true) (hb : inT b = true)
    (h : lt b a = true) : le a b = false := by
  show ((a == b) || lt a b) = false
  rw [show (a == b) = false from by
      cases hc : (a == b) with
      | false => rfl
      | true => exfalso; rw [← eq_of_beq hc, lt_irrefl] at h; exact Bool.noConfusion h,
    lt_asymm_inT hb ha h]
  rfl

end

/-! ### §113.4 係数の半分 — 名指しの形

`R = 0` にすると的は窓の下端 `φ̄(Γ₀,0)` そのものである。**対偶がそのまま §111 の求めた
条項で、起きうる形は三つしかない。** -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- **§113.4 の主定理 (1) — 係数の半分、対偶の形。**  桁の指数がどれも `Γ₀` より下で、
    係数も `Ω₁` より下の成分も窓の下端に届かなければ、`ψ₀` の値は窓に入らない。 -/
theorem notWin113 {x : Term} (hx : inT x = true) (hxM : lt x M = true)
    (hlo : ∀ p ∈ toList x, lt p (reg 1) = true → lt p (rawT94 0) = true)
    (hhi : ∀ p ∈ toList x, lt p (reg 1) = false →
      lt (wA (reg 1) p) G094 = true ∧ lt (wC (reg 1) p) (rawT94 0) = true) :
    le (rawT94 0) (collapse 0 x) = false := by
  have hiT : inT (gT113 zero) = true := inT_rawT98 0
  obtain ⟨hiC, hltC⟩ := collapse0_facts113 (R := zero) hiT hx hxM hlo hhi
  exact not_le_of_lt113 hiT hiC hltC

/-- 「この成分が窓の下端以上のものを持ち込んでいる」を決定可能な形で。
    `Ω₁` より下の成分なら値そのもの、桁なら指数が `Γ₀` 以上か係数が窓の下端以上か。 -/
def badP113 (p : Term) : Bool :=
  match lt p (reg 1) with
  | true => !(lt p (rawT94 0))
  | false => !(lt (wA (reg 1) p) G094) || !(lt (wC (reg 1) p) (rawT94 0))

/-- **§113.4 の主定理 (2) — 係数の半分。**  値が窓の下端に届いたなら、`ψ₀` の引数には
    「桁の指数が `Γ₀` 以上の成分」か「係数が窓の下端以上の成分」か
    「`Ω₁` より下で値が窓の下端以上の成分」が必ずある。**係数の側が名指しで出る。** -/
theorem coefWin113 {x : Term} (hx : inT x = true) (hxM : lt x M = true)
    (hle : le (rawT94 0) (collapse 0 x) = true) :
    (toList x).any badP113 = true := by
  cases hb : (toList x).any badP113 with
  | true => rfl
  | false =>
      exfalso
      have hall : ∀ p ∈ toList x, badP113 p = false := by
        intro p hp
        cases hbp : badP113 p with
        | false => rfl
        | true =>
            exfalso
            rw [List.any_eq_true.mpr ⟨p, hp, hbp⟩] at hb
            exact Bool.noConfusion hb
      have hlo : ∀ p ∈ toList x, lt p (reg 1) = true → lt p (rawT94 0) = true := by
        intro p hp h1
        have h := hall p hp
        unfold badP113 at h
        rw [h1] at h
        cases h2 : lt p (rawT94 0) with
        | true => rfl
        | false => rw [h2] at h; exact Bool.noConfusion h
      have hhi : ∀ p ∈ toList x, lt p (reg 1) = false →
          lt (wA (reg 1) p) G094 = true ∧ lt (wC (reg 1) p) (rawT94 0) = true := by
        intro p hp h1
        have h := hall p hp
        unfold badP113 at h
        rw [h1] at h
        constructor
        · cases h2 : lt (wA (reg 1) p) G094 with
          | true => rfl
          | false => rw [h2] at h; exact Bool.noConfusion h
        · cases h2 : lt (wC (reg 1) p) (rawT94 0) with
          | true => rfl
          | false =>
              rw [h2] at h
              cases h3 : lt (wA (reg 1) p) G094 with
              | true => rw [h3] at h; exact Bool.noConfusion h
              | false => rw [h3] at h; exact Bool.noConfusion h
      rw [notWin113 hx hxM hlo hhi] at hle
      exact Bool.noConfusion hle

/-- 存在の形で。 -/
theorem coefWinEx113 {x : Term} (hx : inT x = true) (hxM : lt x M = true)
    (hle : le (rawT94 0) (collapse 0 x) = true) :
    ∃ p ∈ toList x, badP113 p = true :=
  List.any_eq_true.mp (coefWin113 hx hxM hle)


/-- **§113.4 の主定理 (3) — 条項の前提に、名指しの証人が只でつく。** -/
theorem scFirstOne_needs113 (Hp : PsiIdxOKStd172) {a : BT}
    (hb : btLe72 1 (BT.D 0 a) = true) (hs : BT.isStd (BT.D 0 a) = true)
    (hle : le (rawT94 0) (dict (BT.D 0 a)) = true) :
    (toList (dict a)).any badP113 = true := by
  have hba : btLe72 1 a = true := by
    have h : (decide (0 ≤ 1) && btLe72 1 a) = true := hb
    exact ((Bool.and_eq_true _ _).mp h).2
  have hsa : BT.isStd a = true := by
    have h : (BT.isStd a && (BT.GB 0 a).all (fun e => BT.lt e a)) = true := hs
    exact ((Bool.and_eq_true _ _).mp h).1
  obtain ⟨hiA, hAM⟩ := inT_dict_of_std172 Hp a hba hsa
  exact coefWin113 hiA hAM hle

/-- **残っているもの、名指しで。**  `SCFirstOne111` に「引数が窓の下端以上のものを
    運んでいる」という前提を足しただけのもの。**証明しない。** -/
def WinProp113 : Prop := ∀ a : BT, btLe72 1 (BT.D 0 a) = true → BT.isStd (BT.D 0 a) = true →
    BT.lt (bTowG98 0) (BT.D 0 a) = true → le (rawT94 0) (dict (BT.D 0 a)) = true →
    (toList (dict a)).any badP113 = true →
    le (dict (bTowG98 1)) (dict (BT.D 0 a)) = true

/-- 只の向き。 -/
theorem winProp_of_scFirstOne113 (H : SCFirstOne111) : WinProp113 :=
  fun a hb hs hlt hle _ => H a hb hs hlt hle

/-- **§113.4 の主定理 (4) — 足した前提は只である。**  係数の半分が証明ずみだから、
    条項は「窓の下端以上のものを運んでいる成分がある」を**仮定してよい**。 -/
theorem scFirstOne_of_winProp113 (Hp : PsiIdxOKStd172) (H : WinProp113) : SCFirstOne111 :=
  fun a hb hs hlt hle => H a hb hs hlt hle (scFirstOne_needs113 Hp hb hs hle)

/-- **二つは同値。**  §113 は残余を動かしたのではなく、条項に只の情報を足した。 -/
theorem winProp_iff_scFirstOne113 (Hp : PsiIdxOKStd172) : WinProp113 ↔ SCFirstOne111 :=
  ⟨scFirstOne_of_winProp113 Hp, winProp_of_scFirstOne113⟩

/-- そして五つの帰結もそのまま乗る。 -/
theorem gap_of_winProp113 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (H : WinProp113) :
    GapAtG0_107 := gap_of_one111 Hp H2 (scFirstOne_of_winProp113 Hp H)

theorem denseMid107_false_of_winProp113 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (H : WinProp113) : ¬ DictDenseMid107 :=
  denseMid107_false_of_one111 Hp H2 (scFirstOne_of_winProp113 Hp H)

theorem cofDenseS1_false_of_winProp113 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (H : WinProp113) : ¬ CofDenseS1 :=
  cofDenseS1_false_of_one111 Hp H2 (scFirstOne_of_winProp113 Hp H)


end

/-! ### §113.5 第三の道 — 窓の値を `ψ₁` の中に入れる

§111 は「第三の道があるかもしれない、**作ってから**結論せよ」と書いた。**ある。**
窓の値を持つ項をひとつ `ψ₁` でくるむと、底 `Ω₁` の桁は指数 `1`・係数がその値そのもの
になる。指数は `Γ₀` よりはるかに下で、窓の値は全部**係数**の側にある。しかも `Ω^Ω` を
前置しても窓から出ない — `plus` は次の係数のほうが大きければ累算器を捨てるからで、
§107 の「基底が `Γ₀` になるので以後の Veblen 桁は `φ̄(a,Γ₀⊕c)` に着く」はそこで破れる。 -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- **第三の運び手。**  窓の値を持つ項を `ψ₁` ひとつでくるむ。 -/
def cCoef113 (w : BT) : BT := BT.D 0 (BT.D 1 w)

/-- **`Ω^Ω` を前置した形。**  §108.4 の修理をかけても窓から出ない。 -/
def cJump113 : BT := BT.D 0 (BT.sum bOO94 (BT.D 1 (bWin108 1)))

/-- 先頭の桁の指数。 -/
def leadExp113 (a : BT) : Term := ((wcnf (reg 1) (toList (dict a))).1.headD (zero, zero)).1
/-- 先頭の桁の係数。 -/
def leadCoef113 (a : BT) : Term := ((wcnf (reg 1) (toList (dict a))).1.headD (zero, zero)).2

set_option maxRecDepth 40000 in
/-- 値は `φ̄(Γ₀,1)` — §108.1 の第 1 段と同じ点。 -/
theorem dict_cCoef113 : dict (cCoef113 (bWin108 1)) = phi G094 TM.Term.one := rfl

set_option maxRecDepth 40000 in
theorem inWin_cCoef113 : (le (rawT94 0) (dict (cCoef113 (bWin108 1)))
    && lt (dict (cCoef113 (bWin108 1))) (dict (bTowG98 1))) = true := rfl

set_option maxRecDepth 40000 in
/-- **指数は `1`。**  `Γ₀` よりはるかに下 — 運び手ではなく係数が窓に入れている。 -/
theorem leadExp_cCoef113 : lt (leadExp113 (BT.D 1 (bWin108 1))) G094 = true := rfl

set_option maxRecDepth 40000 in
/-- **そして係数が窓の下端以上である。**  §113.4 の三つの形のうち係数の形。 -/
theorem leadCoef_cCoef113 : le (rawT94 0) (leadCoef113 (BT.D 1 (bWin108 1))) = true := rfl

set_option maxRecDepth 40000 in
theorem level_cCoef113 : (btLe72 1 (cCoef113 (bWin108 1)) && hd085B (cCoef113 (bWin108 1)))
    = true := rfl

set_option maxRecDepth 40000 in
/-- 裸の形は §111 の族と同じく `ψ₀(Ω^Ω)` より下にいる — だから条項の前提が外す。 -/
theorem notLt_bTow_cCoef113 : BT.lt (bTowG98 0) (cCoef113 (bWin108 1)) = false := rfl

set_option maxRecDepth 40000 in
/-- **前置しても値は動かない。** -/
theorem dict_cJump113 : dict cJump113 = phi G094 TM.Term.one := rfl

set_option maxRecDepth 40000 in
theorem inWin_cJump113 :
    (le (rawT94 0) (dict cJump113) && lt (dict cJump113) (dict (bTowG98 1))) = true := rfl

set_option maxRecDepth 40000 in
/-- **そして条項の前提を満たす。**  §111 の F は 30 項とも満たさなかった。 -/
theorem lt_bTow_cJump113 : BT.lt (bTowG98 0) cJump113 = true := rfl

set_option maxRecDepth 40000 in
/-- **窓の上端には届かない** — 条項の結論が破れている。 -/
theorem notLe_top_cJump113 : le (dict (bTowG98 1)) (dict cJump113) = false := rfl

set_option maxRecDepth 40000 in
theorem level_cJump113 :
    (btLe72 1 cJump113 && hd085B cJump113 && inT (dict cJump113)) = true := rfl

theorem hd085_cJump113 : Hd085 cJump113 := by
  intro z hz; exact ⟨_, List.mem_singleton.mp hz⟩

set_option maxRecDepth 40000 in
/-- **強臨界枝は先に発火している。**  それでも値は窓の中にいる。 -/
theorem leadSC_cJump113 : le (reg 1) (leadExp113 (BT.sum bOO94 (BT.D 1 (bWin108 1)))) = true :=
  rfl

/-! 標準性はどこで壊れるか — 遺伝である。 -/

theorem notStd_D1_113 {y : BT} (h : BT.isStd y = false) : BT.isStd (BT.D 1 y) = false := by
  show (BT.isStd y && (BT.GB 1 y).all (fun e => BT.lt e y)) = false
  rw [h]; rfl

theorem notStd_D0_113 {x : BT} (h : BT.isStd x = false) : BT.isStd (BT.D 0 x) = false := by
  show (BT.isStd x && (BT.GB 0 x).all (fun e => BT.lt e x)) = false
  rw [h]; rfl

theorem notStd_sumD1_113 {p y : BT} (h : BT.isStd y = false) :
    BT.isStd (BT.sum p (BT.D 1 y)) = false := by
  show (BT.isP p && BT.isStd p && BT.isStd (BT.D 1 y)
    && (BT.isP (BT.D 1 y) && BT.le (BT.D 1 y) p)) = false
  rw [notStd_D1_113 h, Bool.and_false, Bool.false_and]

/-- **§113.5 の主定理。**  係数の道は「窓の値を持つ**標準な**項」を `ψ₁` の中に要求する。
    `isStd` は遺伝するから、そこが立たなければ全体も立たない — **つまりこの道そのものが
    帰納法の仮定である。**  「大きさについての帰納」の中身はこれである。 -/
theorem notStd_cCoef113 {w : BT} (h : BT.isStd w = false) (r : BT) :
    BT.isStd (BT.D 0 (BT.sum r (BT.D 1 w))) = false :=
  notStd_D0_113 (notStd_sumD1_113 h)

theorem notStd_cCoefBare113 {w : BT} (h : BT.isStd w = false) :
    BT.isStd (cCoef113 w) = false := notStd_D0_113 (notStd_D1_113 h)

theorem notStd_cJump113 : BT.isStd cJump113 = false :=
  notStd_cCoef113 (notStd_bWin108 1) bOO94

/-- `SCFirstOne111` から標準性を外したもの — **前提 `ψ₀(Ω^Ω) < b` は残してある。** -/
def SCFirstOneNoStd113 : Prop := ∀ a : BT, btLe72 1 (BT.D 0 a) = true →
    BT.lt (bTowG98 0) (BT.D 0 a) = true → le (rawT94 0) (dict (BT.D 0 a)) = true →
    le (dict (bTowG98 1)) (dict (BT.D 0 a)) = true

set_option maxRecDepth 40000 in
/-- **§113.5 の主定理 (2)。**  1 成分形からも標準性は外せない。§108 は和の形で同じことを
    示し (`scFirstNoStd_false108`)、§111 は「前提が近い外れを全部外す」と書いた。
    **外さない。**  `cJump113` は前提を満たして窓の中にいる。 -/
theorem scFirstOneNoStd_false113 : ¬ SCFirstOneNoStd113 := by
  intro H
  have h : le (dict (bTowG98 1)) (dict cJump113) = true :=
    H (BT.sum bOO94 (BT.D 1 (bWin108 1))) rfl rfl rfl
  rw [notLe_top_cJump113] at h
  exact Bool.noConfusion h

/-- §107 の理由を「前提つき・先頭の桁が強臨界」で書き直したもの。 -/
def LeadSCJumps113 : Prop := ∀ a : BT, btLe72 1 (BT.D 0 a) = true → Hd085 (BT.D 0 a) →
    BT.lt (bTowG98 0) (BT.D 0 a) = true → le (reg 1) (leadExp113 a) = true →
    le (rawT94 0) (dict (BT.D 0 a)) = true →
    le (dict (bTowG98 1)) (dict (BT.D 0 a)) = true

set_option maxRecDepth 40000 in
/-- **§113.5 の主定理 (3)。**  「先に強臨界枝が発火すれば窓を飛び越す」も偽である。
    `cJump113` では実際に先に発火していて、値は窓の中にいる。仕掛けは `plus` で、
    次の係数が累算器より大きければ累算器は捨てられる。 -/
theorem leadSCJumps_false113 : ¬ LeadSCJumps113 := by
  intro H
  have h : le (dict (bTowG98 1)) (dict cJump113) = true :=
    H (BT.sum bOO94 (BT.D 1 (bWin108 1))) rfl hd085_cJump113 rfl rfl rfl
  rw [notLe_top_cJump113] at h
  exact Bool.noConfusion h

end

/-! ### §113.6 残っているもの、名指しで — と段の正直さ

係数の半分が定理になったので、`SCFirstOne111` に残るのは**持ち上げ**ひとつである:
運んでいるものが窓の**上端**以上なら値も上端以上、という算術。§113.4 が与えるのは
「下端以上」までで、下端から上端への差が大きさについての帰納法そのもの (§113.5)。 -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- 「この成分は窓の上端以上のものを運んでいる」。 -/
def upP113 (p : Term) : Bool :=
  match lt p (reg 1) with
  | true => le (dict (bTowG98 1)) p
  | false => le (dict (bTowG98 1)) (wC (reg 1) p)

/-- **残っているもの — 伝播。**  引数のどこかが窓の上端以上のものを運んでいるなら、
    `ψ₀` の値も窓の上端以上である。**証明しない** (§113.7 が測る)。 -/
def UpProp113 : Prop := ∀ x : Term, inT x = true → lt x M = true →
    (toList x).any upP113 = true → le (dict (bTowG98 1)) (collapse 0 x) = true

/-! 段の正直さ — §98・§103・§107・§111 と同じ規律。 -/

theorem btLe1_cCoef113 {w : BT} (h : btLe72 1 w = true) : btLe72 1 (cCoef113 w) = true := by
  show (decide (0 ≤ 1) && (decide (1 ≤ 1) && btLe72 1 w)) = true
  rw [h]; rfl

set_option maxRecDepth 40000 in
theorem btLe0_cJump113 : btLe72 0 cJump113 = false := rfl

end

/-! ### §113.7 測定 (凍結)

**構成を先に書く。**  母集団はふたつ。ひとつは新しく作り、ひとつは §108.6 のものを
読み直す。

    Q  窓の中と上に値を持つ種 10 個 (`seedW113`) を三つの形にはめたもの、30 項。
       q1 = `ψ₀(ψ₁ w)`            §113.5 の第三の運び手 (係数の道)
       q2 = `ψ₀(Ω^Ω ⊕ ψ₁ w)`      §108.4 の修理をかけた形
       q3 = `ψ₀(Ω^Ω ⊕ w)`         **対照** — `w` を `ψ₁` から出して尾に置く
       **標準性で濾さない。**
    E  §108.6 の数え上げ (大きさ 12 までの標準・段 1 以下の項 9992 個) をそのまま読み直す。

**仮説が母集団に見えていること。**  `badP113` は E の 4587 項で鳴り、5405 項で鳴らない
— 両側とも見えている。`UpProp113` の前提は Q で 9 項・E で 1718 項で発火する。 -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- 三つの節を別々に読むための道具。 -/
def prs113 (a : BT) : List (Term × Term) := (wcnf (reg 1) (toList (dict a))).1
def expGeG0_113 (a : BT) : Bool := (prs113 a).any (fun ac => !(lt ac.1 G094))
def coefHi113 (a : BT) : Bool := (prs113 a).any (fun ac => !(lt ac.2 (rawT94 0)))
def tailHi113 (a : BT) : Bool := !(lt (rhoW89 (dict a)) (rawT94 0))
def leadHiW113 (a : BT) : Bool := le (reg 1) (leadExp113 a)
def coefOnly113 (a : BT) : Bool := coefHi113 a && !(expGeG0_113 a) && !(tailHi113 a)
def anyBad113 (a : BT) : Bool := (toList (dict a)).any badP113
def anyUp113 (a : BT) : Bool := (toList (dict a)).any upP113
def argOf113 : BT → BT | BT.D _ a => a | b => b
/-- 指数が降順か。 -/
def expDesc113 (a : BT) : Bool :=
  let l := (prs113 a).map (·.1)
  (l.zip (l.drop 1)).all (fun q => lt q.2 q.1)
/-- 「`ψ₁` の直下が `ψ₀` 項」— 第三の運び手の目印。 -/
def d1OverD0_113 (b : BT) : Bool :=
  match b with
  | BT.D 0 x => (BT.toL x).any (fun p => match p with
                                 | BT.D 1 (BT.D 0 _) => true
                                 | _ => false)
  | _ => false

def seedW113 : List BT :=
  [ bWin108 1, bWin108 2, bTowG98 1, bTowG98 2, cWin111 cCar111,
    cWin111 (BT.D 0 BT.zero), bWinOO108 1, bTowG98 0, smallB108, BT.D 0 (BT.Om 1) ]
def q1_113 : List BT := seedW113.map fun w => cCoef113 w
def q2_113 : List BT := seedW113.map fun w => BT.D 0 (BT.sum bOO94 (BT.D 1 w))
def q3_113 : List BT := seedW113.map fun w => BT.D 0 (BT.sum bOO94 w)
def popQ113 : List BT := q1_113 ++ q2_113 ++ q3_113

#guard popQ113.length == 30

/-! **30 項のうち 12 項が窓の中に入る — 三つの形とも 4 項ずつ。**  そして **12 項のうち
    8 項が条項の前提 `ψ₀(Ω^Ω) < ·` を満たす。**  §111 の F は窓に 13 項入れて、前提を
    満たすものは 0 項だった。 -/
#eval (popQ113.countP fun b => inWin108 (dict b),
       q1_113.countP fun b => inWin108 (dict b),
       q2_113.countP fun b => inWin108 (dict b),
       q3_113.countP fun b => inWin108 (dict b),
       (popQ113.filter fun b => inWin108 (dict b)).countP fun b => BT.lt (bTowG98 0) b)
#guard (popQ113.countP fun b => inWin108 (dict b)) == 12
#guard (q1_113.countP fun b => inWin108 (dict b)) == 4
#guard (q2_113.countP fun b => inWin108 (dict b)) == 4
#guard (q3_113.countP fun b => inWin108 (dict b)) == 4
#guard ((popQ113.filter fun b => inWin108 (dict b)).countP fun b =>
          BT.lt (bTowG98 0) b) == 8

/-! **係数の節だけが鳴るのは裸の形の 7 項で、ほかの 20 項では 0 項。**  対照 q3 は
    `w` を `ψ₁` から出しただけで節が係数から尾に移る — **窓の値を係数に変えているのは
    `ψ₁` であって他ではない。** -/
#eval (popQ113.countP fun b => coefOnly113 (argOf113 b),
       q1_113.countP fun b => coefOnly113 (argOf113 b),
       q2_113.countP fun b => coefOnly113 (argOf113 b),
       q3_113.countP fun b => coefOnly113 (argOf113 b),
       q3_113.countP fun b => tailHi113 (argOf113 b))
#guard (popQ113.countP fun b => coefOnly113 (argOf113 b)) == 7
#guard (q1_113.countP fun b => coefOnly113 (argOf113 b)) == 7
#guard (q2_113.countP fun b => coefOnly113 (argOf113 b)) == 0
#guard (q3_113.countP fun b => coefOnly113 (argOf113 b)) == 0
#guard (q3_113.countP fun b => tailHi113 (argOf113 b)) == 7
#guard (popQ113.countP fun b => coefHi113 (argOf113 b)) == 14
#guard (popQ113.countP fun b => expGeG0_113 (argOf113 b)) == 20
#guard (popQ113.countP fun b => leadHiW113 (argOf113 b)) == 20

/-! **30 項とも段 1 以下・成分は `D 0`・値は `inT`。7 項は標準で、窓に入る 12 項のうち
    正しい証人は 0 項。**  正しい証人でしかも前提を満たす 6 項は、値がすべて窓の
    **下端より下**にいる。 -/
#eval (popQ113.countP fun b => btLe72 1 b && hd085B b && inT (dict b),
       popQ113.countP fun b => BT.isStd b,
       popQ113.countP fun b => inWin108 (dict b) && bgood94 b,
       popQ113.countP fun b => bgood94 b && BT.lt (bTowG98 0) b)
#guard (popQ113.countP fun b => btLe72 1 b && hd085B b && inT (dict b)) == 30
#guard (popQ113.countP fun b => BT.isStd b) == 7
#guard (popQ113.countP fun b => inWin108 (dict b) && bgood94 b) == 0
#guard (popQ113.countP fun b => bgood94 b && BT.lt (bTowG98 0) b) == 6
#guard (popQ113.countP fun b => bgood94 b && BT.lt (bTowG98 0) b
          && lt (dict b) (rawT94 0)) == 6

/-! **§108 の C・D と §111 の F・G はこの形をひとつも含まない** — 1463・1463・30・10 項中
    0 項。E は 483 項含むが、危ないものは含みえない: この形が危ないのは `ψ₁` の中身が
    窓の運び手のときで、それは標準ではなく、E は標準な項しか作らない。**§111 の種の問題が
    一段上でくり返している。** -/
#eval (rawC108.countP d1OverD0_113, rawD108.countP d1OverD0_113,
       popF111.countP d1OverD0_113, popG111.countP d1OverD0_113,
       allStd108.countP d1OverD0_113,
       q1_113.countP d1OverD0_113, q2_113.countP d1OverD0_113,
       q3_113.countP d1OverD0_113)
#guard (rawC108.countP d1OverD0_113) == 0
#guard (rawD108.countP d1OverD0_113) == 0
#guard (popF111.countP d1OverD0_113) == 0
#guard (popG111.countP d1OverD0_113) == 0
#guard (q1_113.countP d1OverD0_113) == 10
#guard (q2_113.countP d1OverD0_113) == 10
#guard (q3_113.countP d1OverD0_113) == 0

/-! **既知の二族は運び手の節しか鳴らさない。**  §108.1 の `bWin108` の 4 段でも
    §111.2 の `cWin111` の 10 項でも、指数の節が鳴って係数と尾の節は鳴らない。
    **だから係数の半分はどちらの族も含まない道についての話で、作るしかなかった。** -/
#guard (List.range 4).all fun k =>
  expGeG0_113 (sumG0_108 k) && !(coefHi113 (sumG0_108 k)) && !(tailHi113 (sumG0_108 k))
#guard tailF111.all fun v =>
  expGeG0_113 (cArg111 v) && !(coefHi113 (cArg111 v)) && !(tailHi113 (cArg111 v))

/-! **指数は降順である。**  だから「先頭の桁が `Γ₀` より下」と「どの桁も `Γ₀` より下」は
    測った範囲では同じ仮定である。 -/
#guard (List.range 4).all fun k => expDesc113 (sumG0_108 k)
#guard tailF111.all fun v => expDesc113 (cArg111 v)
#guard expDesc113 (bArg98 (bTowG98 1))
#guard popQ113.all fun b => expDesc113 (argOf113 b)

/-! **E の読み直し (1) — 条項の仮説は両側とも見えている。** -/
#eval (allStd108.length, allStd108.countP fun z => anyBad113 z,
       allStd108.countP fun z => !(anyBad113 z),
       allStd108.countP fun z => coefHi113 z, allStd108.countP fun z => coefOnly113 z)
#guard (allStd108.countP fun z => anyBad113 z) == 4587
#guard (allStd108.countP fun z => !(anyBad113 z)) == 5405
#guard (allStd108.countP fun z => coefHi113 z) == 513
#guard (allStd108.countP fun z => coefOnly113 z) == 501

/-! **E の読み直し (2) — 正しい `ψ₀` 引数の上では係数の道はほとんど見えない。**
    5318 項が `ψ₀` を載せて標準になり、そのうち係数の節が鳴るのは 3 項、
    **係数の節だけが鳴るものは 0 項。**  遺伝の議論 (§113.5) が言うとおりである。 -/
#eval (allStd108.countP fun z => BT.isStd (BT.D 0 z),
       (allStd108.filter fun z => BT.isStd (BT.D 0 z)).countP fun z => coefHi113 z,
       (allStd108.filter fun z => BT.isStd (BT.D 0 z)).countP fun z => coefOnly113 z)
#guard (allStd108.countP fun z => BT.isStd (BT.D 0 z)) == 5318
#guard ((allStd108.filter fun z => BT.isStd (BT.D 0 z)).countP fun z => coefHi113 z) == 3
#guard ((allStd108.filter fun z => BT.isStd (BT.D 0 z)).countP fun z => coefOnly113 z) == 0

/-! **E の読み直し (3) — 条項そのものは E で外れ 0。**  2606 項が「正しい証人でしかも
    `ψ₀(Ω^Ω) < ·`」を満たし、窓に入るのは 0 項、条項が破れるのも 0 項。 -/
#eval (allStd108.countP fun z => BT.isStd (BT.D 0 z) && BT.lt (bTowG98 0) (BT.D 0 z),
       allStd108.countP fun z => BT.isStd (BT.D 0 z) && BT.lt (bTowG98 0) (BT.D 0 z)
          && inWin108 (dict (BT.D 0 z)))
#guard (allStd108.countP fun z =>
  BT.isStd (BT.D 0 z) && BT.lt (bTowG98 0) (BT.D 0 z)) == 2606
#guard (allStd108.countP fun z => BT.isStd (BT.D 0 z) && BT.lt (bTowG98 0) (BT.D 0 z)
          && inWin108 (dict (BT.D 0 z))) == 0
#guard (allStd108.countP fun z => BT.isStd (BT.D 0 z) && BT.lt (bTowG98 0) (BT.D 0 z)
          && le (rawT94 0) (dict (BT.D 0 z))
          && !(le (dict (bTowG98 1)) (dict (BT.D 0 z)))) == 0

/-! **残った条項 `UpProp113` は Q で 30/30、E で 9992/9992、前提は 9 項と 1718 項で
    発火する。**  空振りの一掃ではない。 -/
#eval (popQ113.countP fun b => anyUp113 (argOf113 b),
       allStd108.countP fun z => anyUp113 z)
#guard (popQ113.countP fun b => anyUp113 (argOf113 b)) == 9
#guard (popQ113.countP fun b =>
  !(anyUp113 (argOf113 b)) || le (dict (bTowG98 1)) (dict b)) == 30
#guard (allStd108.countP fun z => anyUp113 z) == 1718
#guard (allStd108.countP fun z =>
  !(anyUp113 z) || le (dict (bTowG98 1)) (collapse 0 (dict z))) == 9992

end

/-! ## §115 `IdxStd110` IS **NOT** VACUOUS OVER STANDARD TERMS — THE COMPARISON IS NECESSARY
       TOO, AND WHAT §110 WAS SHORT OF IS THE DECIDER, NOT THE CLAUSE

§110 cut §105's residue with one unconditional strict monotonicity, took all 153 surviving
obligations over 599 standard terms, and then wrote down a limit in the words §100 had used
before it: it could not exhibit a surviving obligation on a standard term, and every term it
found with `cV ≤ c` was non-standard and failed the gate.  §115 answers that limit twice, and
the two answers are opposite.

**FIRST — THE VACUITY §110 SAW IS A THEOREM WHERE IT HOLDS, NOT A PROPERTY OF ITS
POPULATION.**  At a FIRST firing step the index is `Δ ⊖ 1`, so `Δ ≤ y` alone kills the
obligation (`not_lt_idxOf_of_le_dd115`: `Δ ⊖ 1 ≤ Δ ≤ y`, and the order is asymmetric).  Read
§110's own monotonicity in the non-strict direction (`le_mulL_mono115`) and that becomes the
CONVERSE of §110's exemption:

    **`lt_coef_of_lt_idxOf115` — at a first firing step, if `y = ω^E·c` ON THE NOSE, then the
    obligation IMPLIES `c < cV`.**

So there the coefficient comparison is not merely sufficient, it is NECESSARY, and
`coefFree110_of_lt_idxOf115` says the decidable form fires at every such step.  **No clause
can carry a surviving obligation at a first firing step with exact recovery, on ANY term
where the gate holds — standard or not.**  §110's 153-out-of-153 was forced, and so was
§110's 0-out-of-150 on the non-standard side.

**SECOND — THAT LEAVES EXACTLY ONE HOLE, AND THE SURVIVOR LIVES IN IT.**  The necessity proof
wants the recovery exact.  `coefOf110 E` peels `E` off each digit of `y`; a digit that does
not carry `E` as a prefix comes back whole.  If such a digit is BELOW `Ω₁` nothing breaks —
the recovered coefficient is still a term, only a little too big, and `coefFree110` checks
`y ≤ ω^E·c` rather than equality, so it still fires (`ctrl115`).  If such a digit is `Ω₁` or
above, the recovered coefficient is not a descending list at all: it is not a term of 𝔗(M),
`coefFree110` goes silently false, and the obligation stands.  Building that needs a `ψ₀`
argument whose OWN fold fires twice, which needs the argument to be a SUM:

    `carr115  = ψ₁(ψ₁ψ₁0 ⊕ ψ₁0)`                                            (7 symbols)
    `arg115   = eHi2_105 ⊕ carr115`                                         (16 symbols)
    `surv115  = ψ₁(ψ₁ψ₁0 ⊕ ψ₁ψ₁0 ⊕ ψ₀ arg115) ⊕ ψ₁ψ₁0`                      (30 symbols)

**`surv115` is standard, at level ≤ 1, its `dict` image is in 𝔗(M), the gate does not fail on
it, and its one obligation survives §92.1, §92.2, all three of §95, §100, both of §105 AND
§110's coefficient comparison** (`surv115_counts`).  There `E = ω^(Ω₁·2)` and

    `y = ω^E ⊕ Ω₁`  —  one digit AT the power, and one digit at `Ω₁`, which carries no `E`.

`coefOf110 E y = 1 ⊕ Ω₁`, which is not descending, so `inT` is false and §110 sees nothing
(`surv115_shape`).  **`IdxK110` is not vacuous over standard terms.**

**AND THE FIX IS ONE LINE OF ROUNDING.**  A digit `q ≤ ω^E` is covered by `ω^E·1` whatever it
is, so round its coefficient up to `1` and only peel the rest:

    `coef1U115 E q = if q ≤ ω^E then 1 else coef1_110 E q`,  `coefUp115`, `coefFreeU115`.

At `surv115` that gives `c = 2 < cV` and the obligation is free (`surv115_taken`).  No new
arithmetic is needed: `lt_idxOf_of_coef110` is already general in the coefficient, so
`lt_idxOf_of_coefFreeU115` is that theorem with a different witness plugged in.  **What §110
was short of is the DECIDER, not the clause** — `CoefK110`, §110's ∃-form, already covered
this obligation; `coefOf110` simply named the wrong `z`.

WHAT IS PROVED, UNCONDITIONALLY.

  §115.1  `not_lt_of_le115`, `le_mulL_mono115`, `idxOf_none115`,
          **`not_lt_idxOf_of_le_dd115`**, `not_lt_idxOf_of_le_coef115`,
          **`lt_coef_of_lt_idxOf115`** (the converse of §110's exemption at a first firing
          step), `coefFree110_of_lt_idxOf115` (its decidable form).

  §115.2  `coef1U115`, `coefUp115`, `coefFreeU115`, `lt_idxOf_of_coefFreeU115`.

  §115.3  `IdxK115` is `IdxK110` with ONE hypothesis added — `coefFreeU115 p y = false` — so
          the clause is a SUBSET of §110's (`idxK115_of_idxK110`) and §115 demonstrably adds
          no obligation.  `gateStd87_of_idxK115` consumes it at one term,
          `idxStd115_of_step073` is the converse (so `IdxStd115` is still EXACTLY the gate),
          and `psiIdxStep073_of_idxStd115` / `certIn_t326_idx115` re-hang row 326 — on
          `DictLtStd92`, `HiMono89` and `IdxStd115`, and on nothing else (`LeIdxSelf95` has
          been a theorem since §112).

WHAT IS **NOT** CLAIMED.  The gate is NOT closed.  `IdxStd115` is EQUIVALENT to
`PsiIdxStep073`, as `IdxStd110`, `IdxStd105`, `IdxStd100`, `IdxStd95`, `IdxStd92` and
`IdxStd90` were.  `HiMono89` and `DictLtStd92` are untouched and still unproved.
`LocalK2Snd_78`, `IdxLtStd92`, `SplitK86`, `ArgStd87`, `CofDenseS1`, `BCofIn71` are untouched.
§86's wall stands: every theorem here names the step and compares `y` against `ω^E·c`, never
against `i₀` alone or `Δ` alone.  **`lt_coef_of_lt_idxOf115` is proved only at a FIRST firing
step** — with a previous index `idxOf = i₀ ⊕ Δ` is strictly above `Δ` and the argument gives
nothing; §92.1 is still what covers that side, and 448 of the 920 obligations measured in
§110's populations are there.  And it is proved only for EXACT recovery: `surv115` is exactly
what the inexact case allows.  §115 does NOT prove `y < Δ ⟹ coefUp115 E y < cV`.

**§115 MOVED THE RESIDUE; IT DID NOT REMOVE IT** — and unlike §110 it can say precisely where
the next adversary has to live.  Over 423 standard terms BUILT here (896 constructed), 423
obligations, 97 after §95, 65 after §105, **47 after §110 and 0 after §115**; all 47 are true
obligations at a first firing step, all 47 have `inT (coefOf110 E y) = false`, and NONE of the
47 has an exact recovery — exactly as §115.1 forces.  On §110's own 599 terms the corrected
decider takes everything §110 took (574 of 920 against 534, and 0 the other way).  It is not
a tautology: over 1022 terms and 1343 obligations it never fires where the obligation is
false, and the only true obligations at a first firing step it misses are the three with
`cV = 1`, where nothing can be strictly below the coefficient and §105.2 takes them.

**AND THE MEASUREMENT POLICY IS THE POINT OF THIS SECTION.**  §110's populations were not
blind to the SHAPE: 35 of their 920 obligations already have a digit of `y` above the leading
one that is `Ω₁` or more, and 167 of their 1275 `ψ₀` arguments are already sums.  What they
never contained is that shape AT A STEP THAT SURVIVES §95 — the 35 go to 1 after §92 and to 0
after §95.  A clean sweep hid a survivor that the population could name but never carried far
enough, and only building the two halves together — the sum in the argument AND the carrier
that drops `Ω₁` into the second digit of the index — produced it.  The control is one symbol
away: `ctrl115` has the same sum, the same inexact recovery, and §110 takes it.

**THE HONEST LIMIT.**  `IdxK115` has no surviving obligation on the 1022 standard terms
measured here, so §115 is now where §110 was — with one difference: §115.1 names what an
adversary must look like.  At a first firing step the corrected comparison can only fail if
`y` agrees with `Δ` on its leading digit AND the last digit of `cV` is `1`; if the leading
digits differ the comparison is decided there, and if `cV` does not end in `1` the rounding
error (one unit per low digit of `y`) is absorbed.  Terms whose `cV` has two or more digits
are 381 of 1000 in the merged-coefficient family built for this, and 74 of them end in `1` —
but in every one of them `y` stayed below the leading digit of `Δ`.  Whether the outer
component ordering and `BT.isStd` together forbid the agreeing case is exactly the next
question.
-/

/-! ### §115.1 最初の発火歩では、係数の比較は十分であるだけでなく必要 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- `a ≤ b` なら `b < a` ではない。 -/
theorem not_lt_of_le115 {a b : Term} (ha : inT a = true) (hb : inT b = true)
    (h : le a b = true) : lt b a = false := by
  have h' : ((a == b) || lt a b) = true := h
  rcases (Bool.or_eq_true _ _).mp h' with hq | hq
  · rw [eq_of_beq hq]; exact lt_irrefl _
  · exact lt_asymm_inT ha hb hq

/-- `ω^E·` は非狭義でも単調 — §110.1 の狭義単調性に等号の場合を足しただけ。 -/
theorem le_mulL_mono115 {E c c' : Term} (hE : inT E = true) (hc : inT c = true)
    (hc' : inT c' = true) (hcM : lt c M = true) (hc'M : lt c' M = true)
    (h : le c c' = true) : le (mulL E c) (mulL E c') = true := by
  have h' : ((c == c') || lt c c') = true := h
  rcases (Bool.or_eq_true _ _).mp h' with hq | hq
  · rw [eq_of_beq hq]; exact Evidence.WF.le_self _
  · exact le_of_lt (mulL_smono_right110 hE hc hc' hcM hc'M hq)

/-- 最初の発火歩の指数は `Δ ⊖ 1` そのもの。 -/
theorem idxOf_none115 {w : Term} {s : Option Term × Option Term} {ac : Term × Term}
    (hs : s.1 = none) : idxOf w s ac = sub1 (ddOf75 w ac) := by
  show (match s.1 with
        | none => sub1 (mulL (mulL w (subAP w ac.1)) ac.2)
        | some j => plus j (mulL (mulL w (subAP w ac.1)) ac.2)) = _
  rw [hs]
  try rfl

/-- **§115.1 の第一の定理 — 最初の発火歩に余地はない。**  `Δ ≤ y` なら義務は偽である。
    指数は `Δ ⊖ 1 ≤ Δ` だから、`Δ` を超えない元しか只にならない。 -/
theorem not_lt_idxOf_of_le_dd115 {s : Option Term × Option Term} {ac : Term × Term}
    (hs : s.1 = none) (h1 : inT ac.1 = true) (h3 : inT ac.2 = true)
    {y : Term} (hyi : inT y = true) (hle : le (ddOf75 (reg 1) ac) y = true) :
    lt y (idxOf (reg 1) s ac) = false := by
  have hdT : inT (ddOf75 (reg 1) ac) = true := inT_ddOf75 (inT_reg 1) h1 h3
  have hsT : inT (sub1 (ddOf75 (reg 1) ac)) = true := inT_sub1 hdT
  rw [idxOf_none115 (w := reg 1) (ac := ac) hs]
  exact not_lt_of_le115 hsT hyi (le_trans_inT hsT hdT hyi (le_sub1_self75 hdT) hle)

/-- **係数で書いた形。**  復元がちょうどで `cV ≤ c` なら、最初の発火歩の義務は偽。 -/
theorem not_lt_idxOf_of_le_coef115 {s : Option Term × Option Term} {ac : Term × Term}
    (hs : s.1 = none) (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hl3 : lt ac.2 M = true)
    {y c : Term} (hyi : inT y = true) (hci : inT c = true) (hcM : lt c M = true)
    (hex : mulL (eOf110 ac) c = y) (hcv : le ac.2 c = true) :
    lt y (idxOf (reg 1) s ac) = false := by
  have hE : inT (eOf110 ac) = true := inT_mulL mulDescInT (inT_reg 1) (inT_subAP h1)
  have hstep : le (mulL (eOf110 ac) ac.2) (mulL (eOf110 ac) c) = true :=
    le_mulL_mono115 hE h3 hci hl3 hcM hcv
  rw [hex] at hstep
  refine not_lt_idxOf_of_le_dd115 hs h1 h3 hyi ?_
  rw [ddOf_eq_mulL_eOf110]
  exact hstep

/-- **§115.1 の主定理 — 係数の比較は必要条件である。**  最初の発火歩で復元がちょうどなら、
    義務が成り立つことと `c < cV` は同値になる。片側は §110 の
    `lt_idxOf_of_coef110`、もう片側がこれである。 -/
theorem lt_coef_of_lt_idxOf115 {s : Option Term × Option Term} {ac : Term × Term}
    (hs : s.1 = none) (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hl3 : lt ac.2 M = true)
    {y c : Term} (hyi : inT y = true) (hci : inT c = true) (hcM : lt c M = true)
    (hex : mulL (eOf110 ac) c = y) (hobl : lt y (idxOf (reg 1) s ac) = true) :
    lt c ac.2 = true := by
  rcases lt_trichotomy_inT hci h3 with hq | hq | hq
  · exact hq.1
  · exfalso
    rw [not_lt_idxOf_of_le_coef115 hs h1 h3 hl3 hyi hci hcM hex
      (by rw [hq.2.1]; exact Evidence.WF.le_self _)] at hobl
    exact Bool.noConfusion hobl
  · exfalso
    rw [not_lt_idxOf_of_le_coef115 hs h1 h3 hl3 hyi hci hcM hex (le_of_lt hq.2.2)] at hobl
    exact Bool.noConfusion hobl

/-- **判定できる形 — §110 の判定器は「最初の発火歩・復元ちょうど」では完全。**
    そこでは `IdxK110` の仮説 (`coefFree110 = false`) と結論 (義務) は両立しない。
    §110 が 599 項の測定で見た空虚さは、母集団の性質ではなく **定理** である。 -/
theorem coefFree110_of_lt_idxOf115 {s : Option Term × Option Term} {ac : Term × Term}
    (hs : s.1 = none) (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hl3 : lt ac.2 M = true)
    {y : Term} (hyi : inT y = true) (hsub : (subAP (reg 1) ac.1 == zero) = false)
    (hci : inT (coefOf110 (eOf110 ac) y) = true)
    (hcM : lt (coefOf110 (eOf110 ac) y) M = true)
    (hex : mulL (eOf110 ac) (coefOf110 (eOf110 ac) y) = y)
    (hobl : lt y (idxOf (reg 1) s ac) = true) :
    coefFree110 (s, ac) y = true := by
  have h5 : lt (coefOf110 (eOf110 ac) y) ac.2 = true :=
    lt_coef_of_lt_idxOf115 hs h1 h3 hl3 hyi hci hcM hex hobl
  have h4 : le y (mulL (eOf110 ac) (coefOf110 (eOf110 ac) y)) = true := by
    rw [hex]; exact Evidence.WF.le_self _
  show (!(subAP (reg 1) ac.1 == zero) && inT (coefOf110 (eOf110 ac) y)
        && lt (coefOf110 (eOf110 ac) y) M
        && le y (mulL (eOf110 ac) (coefOf110 (eOf110 ac) y))
        && lt (coefOf110 (eOf110 ac) y) ac.2) = true
  rw [hsub, hci, hcM, h4, h5]
  rfl

end

/-! ### §115.2 復元を直す — `ω^E` を超えない成分は係数 `1` に丸める -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 一桁ぶんの補正した割り算。`q ≤ ω^E` の桁は `ω^E·1` で覆えるので係数 `1` にする。
    `coef1_110` はそこで `E` の接頭辞を剥がせず桁をそのまま返すから、
    `Ω₁` 以上の桁が混じると復元が 𝔗(M) の項でなくなる — それがこの丸めの理由である。 -/
def coef1U115 (E q : Term) : Term :=
  if le q (omegaNF E) then TM.Term.one else coef1_110 E q

/-- **補正した係数。**  `coefOf110` の桁ごとの写像を `coef1U115` に取り替えただけ。 -/
def coefUp115 (E x : Term) : Term := ofList ((toList x).map (coef1U115 E))

/-- **判定器。**  §110 の `coefFree110` とまったく同じ形で、係数だけ差し替えたもの。
    `inT`・`lt · M`・`le y (ω^E·c)` を確かめるので、定理の側は何も借りない。 -/
def coefFreeU115 (p : (Option Term × Option Term) × (Term × Term)) (y : Term) : Bool :=
  !(subAP (reg 1) p.2.1 == zero)
    && inT (coefUp115 (eOf110 p.2) y) && lt (coefUp115 (eOf110 p.2) y) M
    && le y (mulL (eOf110 p.2) (coefUp115 (eOf110 p.2) y))
    && lt (coefUp115 (eOf110 p.2) y) p.2.2

/-- **判定器を通す形。**  §110 の `lt_idxOf_of_coef110` は係数について一般だから、
    そこに補正した係数を入れるだけでよい。新しい算術は要らない。 -/
theorem lt_idxOf_of_coefFreeU115 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hl3 : lt ac.2 M = true)
    (hz : ac.2 ≠ zero) {y : Term} (hyi : inT y = true)
    (hcf : coefFreeU115 (s, ac) y = true) (hidxT : inT (idxOf (reg 1) s ac) = true) :
    lt y (idxOf (reg 1) s ac) = true := by
  obtain ⟨hp1, hlt⟩ := (Bool.and_eq_true _ _).mp hcf
  obtain ⟨hp2, hle⟩ := (Bool.and_eq_true _ _).mp hp1
  obtain ⟨hp3, hcM⟩ := (Bool.and_eq_true _ _).mp hp2
  obtain ⟨hsb, hci⟩ := (Bool.and_eq_true _ _).mp hp3
  have hsub : subAP (reg 1) ac.1 ≠ zero := by
    intro hcc
    rw [show (subAP (reg 1) ac.1 == zero) = true from by rw [hcc]; exact beq_self_eq_true _]
      at hsb
    exact Bool.noConfusion hsb
  exact lt_idxOf_of_coef110 hst h1 h3 hl3 hz hsub hyi hci hcM hle hlt hidxT

end

/-! ### §115.3 条項 — 補正した係数の比較をひとつ足す -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§115 の条項。**  §110 の `IdxK110` に仮説をひとつ足しただけ
    (`coefFreeU115 p y = false`) なので、条項は §110 の条項の部分集合であり
    (`idxK115_of_idxK110`)、§115 は義務をひとつも増やさない。 -/
def IdxK115 (a : BT) : Prop :=
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
        powFree105 p y = false → coefFree110 p y = false → coefFreeU115 p y = false →
        (∀ i0, p.1.1 = some i0 → lt i0 y = true) →
        monoClosed95 a p e = false → freeSelf95 p e = false →
        (y ∈ Kset (reg 1) p.2.1 ∨ y ∈ Kset (reg 1) p.2.2) →
        lt y (idxOf (reg 1) p.1 p.2) = true

/-- §110 の条項は §115 の条項を出す — 仮説がひとつ増えただけだから。 -/
theorem idxK115_of_idxK110 {a : BT} (H : IdxK110 a) : IdxK115 a := by
  intro p hp hle hidxT y c e j hc hstd hltc he hse hbe hlte hsz hj hjT hpsiT hlej hyT hyk
    hlty hor hpw hcf _ hgt hmono hsf hy
  exact H p hp hle hidxT y c e j hc hstd hltc he hse hbe hlte hsz hj hjT hpsiT hlej hyT hyk
    hlty hor hpw hcf hgt hmono hsf hy

/-- **§115 の残る仮説。** 部分領域の項について §115 の条項。**証明しない。** -/
def IdxStd115 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → IdxK115 a

/-- **§115.3 の主定理。** 一項ぶんの門は §115 の条項と、326 行目が既に抱えている
    二つの条項から出る (`LeIdxSelf95` は §112 以来定理である)。 -/
theorem gateStd87_of_idxK115 (HD : DictLtStd92) (HM : HiMono89) (HL : LeIdxSelf95) (a : BT)
    (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b)
    (H : btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → IdxK115 a) : GateStd87 a := by
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
      cases hcf : coefFree110 q y with
      | true => exact lt_idxOf_of_coefFree110 hst hi1 hi2 hl2 hnz2 hyT hcf hidxT
      | false =>
      cases hcu : coefFreeU115 q y with
      | true => exact lt_idxOf_of_coefFreeU115 hst hi1 hi2 hl2 hnz2 hyT hcu hidxT
      | false =>
      by_cases hsub : subAP (reg 1) q.2.1 = zero
      · exact H hb hs q hq hle2 hidxT y c e j hc hstd hltc he hse hbe hlte hsze
          hj hjT hpsiT hlej hyT hyk hlty (Or.inr hsub) hpw hcf hcu hgt hmono hsf hy
      · cases hley : le y (reg 1) with
        | true =>
          exact lt_idxOf_of_le_reg105 hst hi1 hi2 hl2 hnz2 hsub hy hyT hley hidxT
        | false =>
          exact H hb hs q hq hle2 hidxT y c e j hc hstd hltc he hse hbe hlte hsze
            hj hjT hpsiT hlej hyT hyk hlty (Or.inl hley) hpw hcf hcu hgt hmono hsf hy
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

/-- **逆向き。** 足した仮説も外した義務もすべて落ちるので、分解は過不足がない
    — `IdxStd115` は依然として門とちょうど同値である。 -/
theorem idxStd115_of_step073 (H : PsiIdxStep073) : IdxStd115 := by
  intro a hb hs p hp hle
  intro _ y _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hy
  exact (H a hb hs p hp hle).2 y hy

/-- **§115 の第一の結論。** -/
theorem psiIdxStep073_of_idxStd115 (HD : DictLtStd92) (HM : HiMono89)
    (H : IdxStd115) : PsiIdxStep073 :=
  step073_of_gate87
    (fun a ih => gateStd87_of_idxK115 HD HM leIdxSelf112 a ih (fun hb hs => H a hb hs))

/-- **§115 の第二の結論 — 326 行目は §115 の条項と、§74/§89 の二つに載る。** -/
theorem certIn_t326_idx115 (HD : DictLtStd92) (HM : HiMono89) (H : IdxStd115)
    (HDe : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_step73 (psiIdxStep073_of_idxStd115 HD HM H) HDe HI HC hacc

end

/-! ### §115.4 測定 (凍結) — 標準な項の上の生き残りを組み立てる -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- §115 の条項が訊く組 — §110 の残余から補正した係数の比較で片づくぶんを引いたもの。 -/
def oblPost115 (a : BT) :
    List (((Option Term × Option Term) × (Term × Term)) × Term × BT × Term) :=
  (oblPost110 a).filter fun w => !(coefFreeU115 w.1 w.2.1)

/-- **`Ω₁` の担い手 (7 記号)。**  `ψ₀` の引数の側に足すと、その引数の畳み込みに
    二つ目の発火歩ができて、指数の第二成分が `Ω₁` になる — `ω^E` の接頭辞を持たない桁である。 -/
def carr115 : BT := BT.D 1 (BT.sum (BT.D 1 (BT.D 1 BT.zero)) (BT.D 1 BT.zero))

/-- **和になった `ψ₀` の引数 (16 記号)。**  §110 の引数はどれも `ψ₁(·)` 一本で、
    畳み込みの発火歩がひとつしかなかった。ここは和だから二つある。 -/
def arg115 : BT := BT.sum eHi2_105 carr115

/-- **§115 の証人 (30 記号)。**  標準で、段は 1 以下、`dict` の像は 𝔗(M) にいて、門は
    そこで落ちない。義務はひとつあり、§92.1・§92.2・§95 の三つ・§100・§105 の二つ・
    **§110 の係数の比較のどれにも取られない。** -/
def surv115 : BT := BT.sum (slot105 1 arg115) vebTail95

/-- **枠を一段下げたもの (26 記号)** — §110 の `advC110` と同じ操作。 -/
def advSlot115 : BT := BT.sum (slot105 0 arg115) vebTail95

/-- **対照 (27 記号)。**  引数は同じく和だが、担い手が `Ω₁` を落とさない。
    義務は §105 を生き延び、そこは §110 の係数の比較が持っていく。
    `surv115` との差は担い手ひとつしかない。 -/
def ctrl115 : BT := BT.sum (slot105 1 (BT.sum eHi2_105 (twr86 3))) vebTail95

/-- **§110 の条項は標準な項の上で空虚ではない。**  `surv115` の一本の義務は
    §110 のどの免除にも取られず、しかも義務そのものは真で、門はそこで落ちない。
    **§110 が「標準な項では生き残りを出せない」と書いた位置は、ここで破れる。** -/
theorem surv115_counts :
    okHyp84 surv115 = true ∧ BT.isStd (BT.D 0 surv115) = true ∧
    inT (dict surv115) = true ∧ stepOKb 0 (dict surv115) = true ∧
    idxb84 0 (dict surv115) = true ∧ splitb86 0 (dict surv115) = true ∧
    idxLt90b surv115 = true ∧ ltArg90b surv115 = true ∧
    lastFire92 (dict surv115) = false ∧
    (oblPre92 surv115).length = 1 ∧ (oblPost95 surv115).length = 1 ∧
    (oblPost105 surv115).length = 1 ∧ (oblPost110 surv115).length = 1 ∧
    ((oblPost110 surv115).all gOK110) = true :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **その一本の形。**  最初の発火歩・`aV ⊖ Ω₁ ≠ 0`・`Ω₁^(aV ⊖ Ω₁) < y`、そして
    **`y` は二成分で、二つ目が `Ω₁` — `ω^E` の接頭辞を持たない桁である。**
    だから `coefOf110` の復元は 𝔗(M) の項ですらなくなり (`inT` が偽)、
    §110 の判定器はそこで黙って偽になる。復元がちょうどでないことが、
    §115.1 の必要性の定理が残していた唯一の隙間である。 -/
theorem surv115_shape :
    ((oblPost110 surv115).all fun w =>
      (w.1.1.1 == none) && !(subAP (reg 1) w.1.2.1 == zero)
        && lt (powOf80 (reg 1) w.1.2) w.2.1
        && ((toList w.2.1).length == 2)
        && !(inT (coefOf110 (eOf110 w.1.2) w.2.1))
        && !(mulL (eOf110 w.1.2) (coefOf110 (eOf110 w.1.2) w.2.1) == w.2.1)
        && (match toList w.2.1 with
            | _ :: q :: _ => q == reg 1
            | _ => false)) = true :=
  by decide

/-- **そして補正した係数がそれを持っていく。**  丸めた復元は `2` で、歩の係数より真に下。
    `CoefLtStd110` の ∃ の形はもともとこの義務を覆っていた — 足りなかったのは
    **判定器のほう** であって、条項の考えではない。 -/
theorem surv115_taken :
    ((oblPost110 surv115).all fun w =>
      coefFreeU115 w.1 w.2.1 && (coefUp115 (eOf110 w.1.2) w.2.1 == plus one one)) = true ∧
    (oblPost115 surv115).length = 0 :=
  ⟨by decide, by decide⟩

/-- **否定その一 — 補正しても買っているのは標準性である。**  `advSlot115` は `surv115` の
    枠を一段下げただけで、段は 1 以下、`dict` の像は 𝔗(M) にいる。それでも
    `BT.isStd (ψ₀ ·)` は偽、門はそこで落ち、補正した係数の比較も破れ、
    **義務そのものも偽である。**  §110 の `advC110_not_std` と同じ壁が §115 にもある。 -/
theorem advSlot115_not_std :
    btLe72 1 advSlot115 = true ∧ inT (dict advSlot115) = true ∧
    BT.isStd (BT.D 0 advSlot115) = false ∧ stepOKb 0 (dict advSlot115) = false ∧
    (oblPost110 advSlot115).length = 1 ∧ (oblPost115 advSlot115).length = 1 ∧
    ((oblPost110 advSlot115).all fun w => !(coefFreeU115 w.1 w.2.1) && !(gOK110 w)) = true :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **否定その二 — 生き残りを作っているのは担い手ひとつであり、復元の不正確さではない。**
    `ctrl115` は引数が和であるところまで `surv115` と同じで、担い手だけが違う。
    そこでも `y` は二成分で復元はちょうどにならない (`ω^E·c` は `y` を真に超える) が、
    第二成分が `Ω₁` の下にとどまるので `coefOf110` の値は 𝔗(M) の項のままで、
    **§110 の係数の比較がそのまま持っていく。**  §110 を破るのは
    「`ω^E` の接頭辞を持たない `Ω₁` 以上の桁」であって、不正確さ一般ではない。 -/
theorem ctrl115_taken :
    okHyp84 ctrl115 = true ∧ (oblPost105 ctrl115).length = 1 ∧
    (oblPost110 ctrl115).length = 0 ∧
    ((oblPost105 ctrl115).all fun w =>
      ((toList w.2.1).length == 2)
        && !(mulL (eOf110 w.1.2) (coefOf110 (eOf110 w.1.2) w.2.1) == w.2.1)
        && inT (coefOf110 (eOf110 w.1.2) w.2.1)
        && coefFree110 w.1 w.2.1) = true :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- 担い手 — `Ω₁` を落とすものと、落とさない対照。 -/
def carrL115 : List BT :=
  [ carr115
  , BT.D 1 (BT.sum (BT.D 1 (BT.D 1 BT.zero)) (BT.D 0 BT.zero))
  , BT.D 1 (BT.sum (BT.D 1 (BT.D 1 BT.zero)) (BT.D 0 (BT.D 0 BT.zero)))
  , BT.D 1 (BT.sum (BT.D 1 (BT.D 1 BT.zero)) (BT.D 1 (BT.D 0 BT.zero)))
  , twr86 3, twr86 2, vebTail95, BT.D 1 BT.zero ]

/-- 頭 — 発火歩の `aV` を `Ω₁·2` にする引数たち。 -/
def headL115 : List BT := [eHi2_105, slot105 1 BT.zero, eHi3_105, ehi100 0, eNest105 BT.zero]

/-- **和になった `ψ₀` の引数を組み立てる。**  担い手を一つ足したものと二つ足したもの。 -/
def argSum115 : List BT :=
  (headL115.flatMap fun X => carrL115.map fun W => BT.sum X W)
  ++ (headL115.flatMap fun X => carrL115.flatMap fun W => carrL115.map fun V =>
        BT.sum X (BT.sum W V))

def wrapL115 : List (BT → BT) :=
  [ fun e => BT.sum (slot105 1 e) vebTail95, fun e => slot105 1 e
  , fun e => BT.sum (slot105 2 e) vebTail95
  , fun e => BT.sum (twr86 5) (BT.sum (slot105 1 e) vebTail95) ]

def pop115 : List BT := (wrapL115.flatMap fun f => argSum115.map f).eraseDups
def qual115 : List BT := pop115.filter okHyp84

-- 組み立てた母集団の大きさ。
#guard (pop115.length, qual115.length) == (896, 423)
#guard ((pop115.map BT.size).foldl min 999, (pop115.map BT.size).foldl max 0) == (20, 50)
#guard (BT.size surv115, BT.size advSlot115, BT.size ctrl115, BT.size arg115,
        BT.size carr115) == (30, 26, 27, 16, 7)

/-! **門は組み立てた母集団のどこでも落ちない。** -/

#guard ((qual115.filter fun a => !(stepOKb 0 (dict a))).length,
        (qual115.filter fun a => !(idxb84 0 (dict a))).length,
        (qual115.filter fun a => !(splitb86 0 (dict a))).length,
        (qual115.filter fun a => !(idxLt90b a)).length,
        (qual115.filter fun a => !(ltArg90b a)).length) == (0, 0, 0, 0, 0)

/-! **§110 の条項は空虚ではない — 47 である。**  標準な 423 項で 423 の義務、
§95 の後で 97、§105 の後で 65、**§110 の後で 47、§115 の後で 0**。
47 はすべて実際に成り立っている義務で (門はどこでも落ちない)、47 項に散らばっている。 -/

#guard ((qual115.flatMap oblPre92).length, (qual115.flatMap oblPost95).length,
        (qual115.flatMap oblPost105).length, (qual115.flatMap oblPost110).length,
        (qual115.flatMap oblPost115).length) == (423, 97, 65, 47, 0)
#guard ((qual115.filter fun a => !((oblPost110 a).isEmpty)).length,
        (qual115.flatMap oblPost110).countP gOK110) == (47, 47)

/-! **47 の形は一つ。**  どれも最初の発火歩で、**復元はどれもちょうどでなく、
`coefOf110` の値は 𝔗(M) の項ですらない。**  `y` の成分数は 2 が 21、3 が 26。
§115.1 の必要性の定理が言うとおり、生き残りは「復元がちょうどでない」ところにしか居ない。 -/

#guard (let o := qual115.flatMap oblPost110
        (o.length, o.countP (fun w => w.1.1.1 == none),
         o.countP (fun w => (toList w.2.1).length == 2),
         o.countP (fun w => (toList w.2.1).length == 3),
         o.countP (fun w => !(inT (coefOf110 (eOf110 w.1.2) w.2.1))),
         o.countP (fun w => mulL (eOf110 w.1.2) (coefOf110 (eOf110 w.1.2) w.2.1) == w.2.1)))
       == (47, 47, 21, 26, 47, 0)

/-! **§110 の母集団はこの形を出せなかった — 出せなかった理由は「無かった」ではない。**
`corpus105`・`wideAdvQ110`・`pairQ110` の 599 項が持つ 920 の義務のうち、`y` の先頭でない
成分が `Ω₁` 以上のものは **35 ある**。ところがその 35 は §92 で 1 に、§95 で 0 になる。
形は母集団の中に在ったが、**§95 を生き延びる歩の上には一度も現れなかった。**
`ψ₀` の引数が和になっているものも 1275 個中 167 個あった。足りなかったのは和でも形でもなく、
その形が §105 まで生き延びる組み合わせである。 -/

#guard (let big : (((Option Term × Option Term) × (Term × Term)) × Term × BT × Term) → Bool :=
          fun w => match toList w.2.1 with
                   | _ :: t => t.any (fun q => !(lt q (reg 1)))
                   | [] => false
        let P := corpus105 ++ wideAdvQ110 ++ pairQ110
        ((P.flatMap oblPre92).countP big, (P.flatMap oblPost92).countP big,
         (P.flatMap oblPost95).countP big, (P.flatMap oblPost105).countP big))
       == (35, 1, 0, 0)

/-! **補正した判定器は §110 の判定器を覆う。**  599 項の 920 の生の義務で、§110 が
取るのは 534、§115 が取るのは 574 — そして **§110 が取って §115 が取らないものは 0**。
`corpus105 ++ wideAdvQ110 ++ pairQ110` の 153 の残余も 153 すべて取る。 -/

#guard (let P := corpus105 ++ wideAdvQ110 ++ pairQ110
        let o := P.flatMap oblPre92
        (o.length, o.countP (fun w => coefFree110 w.1 w.2.1),
         o.countP (fun w => coefFreeU115 w.1 w.2.1),
         o.countP (fun w => coefFree110 w.1 w.2.1 && !(coefFreeU115 w.1 w.2.1)),
         (P.flatMap oblPost105).length,
         (P.flatMap oblPost105).countP (fun w => coefFreeU115 w.1 w.2.1)))
       == (920, 534, 574, 0, 153, 153)

/-! **そして判定器は恒真でない。**  1022 項の 1343 の生の義務のうち補正した比較が通るのは
962 で、**義務が偽なのに通るものは 0**。最初の発火歩・`aV ⊖ Ω₁ ≠ 0`・義務が真なのに
通らないものは 3 つあり、その 3 つはどれも `cV = 1` の歩である — `1` より真に下の係数は
無いのだから、係数の比較はそこでは原理的に使えない。**その 3 つは §105.2 の
`powFree105` が取る。** -/

#guard (let P := corpus105 ++ wideAdvQ110 ++ pairQ110 ++ qual115
        let o := P.flatMap oblPre92
        (P.length, o.length, o.countP (fun w => coefFreeU115 w.1 w.2.1),
         o.countP (fun w => coefFreeU115 w.1 w.2.1 && !(gOK110 w)),
         o.countP (fun w => (w.1.1.1 == none) && !(subAP (reg 1) w.1.2.1 == zero)
                     && gOK110 w && !(coefFreeU115 w.1 w.2.1)),
         o.countP (fun w => (w.1.1.1 == none) && !(subAP (reg 1) w.1.2.1 == zero)
                     && gOK110 w && !(coefFreeU115 w.1 w.2.1)
                     && (w.1.2.2 == TM.Term.one) && powFree105 w.1 w.2.1)))
       == (1022, 1343, 962, 0, 3, 3)

/-! **§115 の残余は、組み立てた 1022 項では 0 である。**  これは §110 が置かれていたのと
同じ位置であり、§110 のときと違って **何を作れば破れるかは §115.1 が名指ししている**：
最初の発火歩では、`y` が `Δ` と先頭成分まで一致していて、しかも `cV` の最後の成分が `1`
であるような義務でなければ、補正した比較は破れない。先頭成分が違えばそこで比較が決まり、
`cV` の最後が `1` でなければ丸めの誤差 (`y` の低い成分ひとつにつき `1`) が吸収される。
その形は組み立てても出なかった — `cV` が二成分以上の義務は 381、最後の成分が `1` の
ものは 74 あるが、そのどれも `y` は `Δ` の先頭成分より下だった。 -/

#guard ((corpus105 ++ wideAdvQ110 ++ pairQ110 ++ qual115).flatMap oblPost115).length == 0

end

/-! ## §118 THE FOLD'S LATER PAIRS, AND THE COEFFICIENT THAT IS NOT `1`

§103 closed the endpoint `Γ₀` of §102's (b1) and left the open interval `(ε₀, Γ₀)`.  §106 made
the FIRST Veblen argument a theorem — one pair of the fold, inverted in general, with a legal
iterable Buchholz witness — and named what was left in two words:

> the fold's LATER pairs (`acc := φ̄(a, acc ⊕ c)`), and the Buchholz witness for a COEFFICIENT
> other than `1` — a digit needs a sub-`Ω₁` tail inside the `ψ₁` sum, which `mulB106` does not
> carry.

**§118 does both, and a third thing §106 did not name.**  `DictOntoMidOpen103` is still NOT
closed; what is closed is the two items, plus the sub-`Ω₁` TAIL of `wcnf` — which is what
carries the first Veblen argument `0`, i.e. the `ω`-powers.  On §103.8's own adversarial pool
the number moves from §106's **14 built witnesses to 191**, every one of them checked against
the full hypothesis list of the theorem that proves its value.

  §118.1  **`BT.ofL` AS A TOOLKIT.**  §106 wrote `mulB106` as its own recursion and re-proved
          `toL`, `GB`, `btLe72`, `isStd` and `dict` for it by hand.  All five are facts about
          `BT.ofL` on a list of PRINCIPAL components (`toL_ofL118`, `gb_ofL118`,
          `btLe_ofL118`, `isStd_ofL118`, `dict_ofL118`), and `mulB106 ls = BT.ofL (ls.map
          (D 1))` (`mulB106_eq_ofL118`).  Everything below is that toolkit applied to a
          component list that is no longer homogeneous.

  §118.2  **THE COEFFICIENT THAT IS NOT `1`.**  `mixB118 ls ns` puts the digits `ls` as `ψ₁`
          nodes and then a tail `ns` of `ψ₀` nodes in the SAME sum; `powB118` and `vebB118`
          put `ψ₁` and `ψ₀` on top.  `dict_vebB118` : the value is `φ̄(1 ⊕ A, ω^ρ)` where `ρ`
          is the tail's value — **and `ω^ρ ≠ 1` exactly when the tail is not empty**
          (`omegaNF_ne_one118`).  §106's `collapse0_argAP106` had the value formula for a
          coefficient `B ≠ 1` but no witness; this is the witness.  Legality is proved, not
          measured: `isStd_vebB118`, `btLe1_vebB118`, `btLe0_vebB118`, `hd085_vebB118`, and
          `dig_vebB118` — the output is again a `Dig106`, so the construction still iterates.
          `mixB118 ls [] = mulB106 ls`, so §106 is the empty-tail case, verbatim.

  §118.3  **THE FOLD'S LATER PAIRS.**  `foldV118` is `acc := φ̄(a, acc ⊕ c)` as a function and
          `fold_some118` says the fold IS that function as soon as every exponent is below
          `Ω₁`; `fold_none118` starts it with `base` and `c ⊖ 1`.  `wcnf_argM118` runs the
          base-`Ω₁` decomposition backwards at `n` components at once — the merge test is
          killed by `descP118`, strict descent of the exponents — and `collapse0_argM118` is
          §106's `collapse0_one_pair106` with the number of pairs free.  §113's
          `collapse0_ltG113` reads the same fold for a BOUND with the target free; this reads
          it for the VALUE with the pair list free.

  §118.3c **AND THE TAIL `ρ`.**  `collapse0_pairsT118` deletes the hypothesis `ρ = 0`: the
          value is `ω^(acc ⊕ ρ)`.  That is the only route to a target whose first Veblen
          argument is `0`; 12 of §103.8's 359 are of that shape and 8 of them are delivered.
          §106 never mentions
          `ρ`; it is invisible when there is one pair and the target is an ε-number.

  §118.4  **THE WITNESS AT `n` PAIRS, AND IN GENERAL.**  `vebN118 ys = ψ₀(Σ ψ₁ yᵢ)` is the
          `n`-pair witness and `vebG118 ys ms = ψ₀(Σ ψ₁ yᵢ ⊕ Σ mⱼ)` adds the tail;
          `vebN118 ys = vebG118 ys []`, `vebB118 ls ns = vebN118 [mixB118 ls ns]`, and
          `vebB118 ls [] = vebB106 ls`.  One shape, three levels of §106, §118.2 and §118.4.
          `dict_vebN118` and `dict_vebG118` are the values.  **Neither uses
          `PsiIdxOKStd172`** — the second gate enters only where the components are computed
          by `dict_D1_eq77`, not in the fold.

  §118.5  **WHAT IS LEFT, NAMED.**  Two shapes, and they are not the same one.  A target that
          is a SUM needs `BT.sum` of witnesses (106 of 359) — the construction here is for
          additively principal targets only.  A digit COEFFICIENT that is a SUM needs several
          components with the SAME exponent, merged back by `wcnf` — and `descP118` forbids
          exactly that (62 of 359).  `noMerge118` is the built refutation: with the
          coefficient `2`, `argM118` computes `φ̄(1, ω²)` and not `φ̄(1,1)`.

  §118.6  **THE MEASUREMENT.**  Three populations, all BUILT, none filtered, and the
          covering condition is VISIBLE in this one — §106's blindness does not recur.

WHAT IS **NOT** CLAIMED.  **`DictOntoMidOpen103` is NOT proved and NOT refuted.**
`DictOntoMid102`, `DictDenseMid102`, `DictDenseAbove102`, `DictDenseMid107`,
`DictDenseAbove107`, `DictDenseHi94`, `DictDense85` and `CofDenseS1` are exactly where §106
and §113 left them; row 326's certificate is unchanged and §118 adds no clause to it and
removes none.  `PsiIdxOKStd172` is used, not proved; `DictLtA74` is not used at all.
`CovM118` / `CovG118` are HYPOTHESES — decidable ones, discharged in every instance below and
measured in §118.6, never assumed silently.  `GapAtG0_107` and `SCFirst108` are untouched.

**Where §118 stopped, precisely, and what moved.**  §106's residue was "the second Veblen
argument"; that is gone.  What is left is not a Veblen fact at all — it is two facts about
SUMS: a sum target (the witness is a `BT.sum`, and its legality is a descending condition
across two witnesses, not one), and a sum coefficient (the `wcnf` merge, which needs the
`n`-component induction run with EQUAL exponents allowed).  **This removes residue and also
names a different one**: §106's 14 built witnesses become 191 on the same pool, and the 173
that remain are 106 + 62 + 5 with the 5 being §103's known `dictInv` incompleteness, for
which §103's own hand-built witnesses satisfy §118's theorem in full.

**AND THE OVERPAYMENT LEDGER.**  §118 found two, the ninth and tenth.  `dict_mixB118` does
not read `lt A (reg 1)` — the digit/tail value formula never compares `A` with `Ω₁`, only the
`ψ₁` step does.  And `dict_vebN118` / `dict_vebG118` do not read `PsiIdxOKStd172`: the second
gate is paid at `dict_D1_eq77`, one layer below, and the fold theorem is free of it.

WHAT THE MEASUREMENT SAYS (§118.6 gives the construction).  Three populations, built on §97's
model so the hypotheses stay VISIBLE, plus §103.8's adversarial pool re-read.

  * **The `n`-pair value formula is exact where its hypothesis holds.**  156 pair lists, 32
    satisfy it, 0 misses — and **24 of the 32 have two pairs**, so the later pairs are
    actually exercised and not a vacuous generalisation.
  * **The hypothesis is visible and is not a restatement of the conclusion.**  124 of the 156
    fail it, and 24 of those 124 satisfy the conclusion anyway.
  * **The tail is exact too, and it is the only route to an `ω`-power.**  112 (pairs, `ρ`)
    cases, 40 satisfy the hypothesis, 0 misses; 30 have `ρ ≠ 0` and **all 30 land on a value
    whose first Veblen argument is `0`** — a shape no construction of §106 or §118.2 emits.
  * **The witness with a tail is exact.**  169 `(ls, ns)` pairs, 86 satisfy the hypothesis,
    and on all 86 the value, standardness, both level bounds, the head condition AND `Dig106`
    hold.  All 86 have a NON-EMPTY tail, i.e. all 86 are coefficients other than `1`.
  * **The covering condition is visible HERE.**  §106 swept 289 Buchholz terms and all 19
    legal ones satisfied its covering condition — the §93 failure mode — and had to build
    `deep106` by hand.  With a tail the condition fires inside the population: **4 of the 169
    have legal digits, a legal tail and a descending list and still FAIL `CovM118`**, and
    all 4 produce a non-standard term.  3 of the 4 have the right VALUE anyway, so the
    condition is about standardness and nothing else.  `deepC118 = ψ₀ψ₁ψ₀ψ₁ψ₁0` is the
    named one: its tail digit `ψ₀(Ω₁²) = ζ₀` is legal on its own.
  * **Descending is not decoration.**  69 of the 169 are not descending and 73 of the 169
    produce a non-standard term.
  * **The reach, on §103.8's own adversarial pool.**  359 terms of `(ε₀, Γ₀)`.  §106 built 14
    witnesses; §118 delivers **186** — and every one of the 186 is checked against the FULL
    hypothesis list of `dict_vebG118`, shape included, not merely against `dict b == t`.  12
    of the 186 use two or more pairs, 157 use a coefficient other than `1`, 8 use a non-zero
    tail.  §103's five `dictInv` misses are covered too, by §103's own `witMiss103` witnesses,
    which satisfy §118's hypotheses in full — **191 of 359**.
  * **The `ω`-powers, which only the tail reaches.**  12 of the 359 have first Veblen
    argument `0`; 8 are delivered, and every one of the 8 has `ρ ≠ 0`.  Nothing in §106 or
    §118.2 can emit one.
  * **And what the 173 are.**  106 are additive sums (the target is not principal), 62 have a
    digit coefficient that is not additively principal (the `wcnf` merge), 5 are §103's
    `dictInv` misses.  106 + 62 + 5 = 173, with nothing unaccounted for. -/


/-! ### §118.1 `BT.ofL` の道具 -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

theorem toL_isP118 : ∀ {x : BT}, BT.isP x = true → BT.toL x = [x]
  | .D _ _, _ => rfl
  | .zero, h => Bool.noConfusion h
  | .sum _ _, h => Bool.noConfusion h

theorem isP_D118 (u : Nat) (a : BT) : BT.isP (BT.D u a) = true := rfl

theorem toL_ofL118 : ∀ (l : List BT), (∀ x ∈ l, BT.isP x = true) → BT.toL (BT.ofL l) = l
  | [], _ => rfl
  | [a], h => toL_isP118 (h a (List.Mem.head _))
  | a :: b :: r, h => by
      show BT.toL a ++ BT.toL (BT.ofL (b :: r)) = _
      rw [toL_isP118 (h a (List.Mem.head _)),
        toL_ofL118 (b :: r) (fun z hz => h z (List.Mem.tail _ hz))]
      rfl

theorem gb_ofL118 (u : Nat) : ∀ (l : List BT), BT.GB u (BT.ofL l) = l.flatMap (BT.GB u)
  | [] => rfl
  | [a] => by
      show BT.GB u a = _
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | a :: b :: r => by
      show BT.GB u a ++ BT.GB u (BT.ofL (b :: r)) = _
      rw [gb_ofL118 u (b :: r)]
      rfl

theorem btLe_ofL118 (m : Nat) : ∀ (l : List BT), (∀ x ∈ l, btLe72 m x = true) →
    btLe72 m (BT.ofL l) = true
  | [], _ => rfl
  | [a], h => h a (List.Mem.head _)
  | a :: b :: r, h => by
      show (btLe72 m a && btLe72 m (BT.ofL (b :: r))) = true
      rw [h a (List.Mem.head _),
        btLe_ofL118 m (b :: r) (fun z hz => h z (List.Mem.tail _ hz))]
      rfl

theorem isStd_sum_D118 (a : BT) (u : Nat) (c : BT) :
    BT.isStd (BT.sum a (BT.D u c))
      = (BT.isP a && BT.isStd a && BT.isStd (BT.D u c) && BT.le (BT.D u c) a) := rfl

theorem isStd_sum_sum118 (a b c : BT) :
    BT.isStd (BT.sum a (BT.sum b c))
      = (BT.isP a && BT.isStd a && BT.isStd (BT.sum b c) && BT.le b a) := rfl

theorem isStd_ofL118 : ∀ (l : List BT), (∀ x ∈ l, BT.isP x = true) →
    (∀ x ∈ l, BT.isStd x = true) → bdesc106 l → BT.isStd (BT.ofL l) = true
  | [], _, _, _ => rfl
  | [a], _, hs, _ => hs a (List.Mem.head _)
  | a :: b :: r, hp, hs, hd => by
      have hsr : BT.isStd (BT.ofL (b :: r)) = true :=
        isStd_ofL118 (b :: r) (fun z hz => hp z (List.Mem.tail _ hz))
          (fun z hz => hs z (List.Mem.tail _ hz)) (bdesc_tail106 hd)
      have hpb : BT.isP b = true := hp b (List.Mem.tail _ (List.Mem.head _))
      cases r with
      | nil =>
          cases b with
          | zero => exact Bool.noConfusion hpb
          | sum _ _ => exact Bool.noConfusion hpb
          | D u c =>
              show BT.isStd (BT.sum a (BT.D u c)) = true
              rw [isStd_sum_D118, hp a (List.Mem.head _), hs a (List.Mem.head _),
                show BT.isStd (BT.D u c) = true from hsr, hd.1]
              rfl
      | cons c r' =>
          show BT.isStd (BT.sum a (BT.ofL (b :: c :: r'))) = true
          rw [show BT.ofL (b :: c :: r') = BT.sum b (BT.ofL (c :: r')) from rfl,
            isStd_sum_sum118, hp a (List.Mem.head _), hs a (List.Mem.head _), hd.1,
            show BT.isStd (BT.sum b (BT.ofL (c :: r'))) = true from hsr]
          rfl

theorem bdesc_append118 : ∀ (l1 l2 : List BT), bdesc106 l1 → bdesc106 l2 →
    (∀ y ∈ l2, ∀ x ∈ l1, BT.le y x = true) → bdesc106 (l1 ++ l2)
  | [], l2, _, h2, _ => h2
  | [a], l2, _, h2, hj => by
      cases l2 with
      | nil => trivial
      | cons b r => exact ⟨hj b (List.Mem.head _) a (List.Mem.head _), h2⟩
  | a :: b :: r, l2, h1, h2, hj => by
      show BT.le b a = true ∧ bdesc106 (b :: (r ++ l2))
      exact ⟨h1.1, bdesc_append118 (b :: r) l2 h1.2 h2
        (fun y hy x hx => hj y hy x (List.Mem.tail _ hx))⟩

/-- 主要成分の `dict` は加法主要。 -/
theorem isAP_dict_isP118 : ∀ {x : BT}, BT.isP x = true → (dict x).isAP = true
  | .D u a, _ => by
      show (collapse u (dict a)).isAP = true
      rw [collapse_eq]
      exact isAP_omegaNF _
  | .zero, h => Bool.noConfusion h
  | .sum _ _, h => Bool.noConfusion h

theorem dict_ofL118 : ∀ (l : List BT), (∀ x ∈ l, BT.isP x = true) →
    descL (l.map dict) = true → dict (BT.ofL l) = ofList (l.map dict)
  | [], _, _ => rfl
  | [a], _, _ => rfl
  | a :: b :: r, hp, hd => by
      have hAP : ∀ x ∈ (b :: r).map dict, x.isAP = true := by
        intro x hx
        obtain ⟨z, hz, hxz⟩ := List.mem_map.mp hx
        rw [← hxz]
        exact isAP_dict_isP118 (hp z (List.Mem.tail _ hz))
      have htl : toList (ofList ((b :: r).map dict)) = dict b :: r.map dict := by
        rw [toList_ofList _ hAP]; rfl
      show plus (dict a) (dict (BT.ofL (b :: r))) = _
      rw [dict_ofL118 (b :: r) (fun z hz => hp z (List.Mem.tail _ hz)) (descL_tail hd),
        plus_cons66 htl,
        show toList (dict a) = [dict a] from
          toList_isAP81 (isAP_dict_isP118 (hp a (List.Mem.head _))),
        List.filter_cons_of_pos (by exact (descL_cons.mp hd).1)]
      rfl

end

/-! ### §118.2 桁と尾をひとつの `ψ₁` に入れる -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- `Ω₁·A ⊕ ρ` の Buchholz 側 — 段 1 の桁 `ls` を並べ、そのうしろに段 0 の尾 `ns`。
    `ns = []` なら §106 の `mulB106 ls` そのものである。 -/
def mixB118 (ls ns : List BT) : BT := BT.ofL (ls.map (BT.D 1) ++ ns)
/-- `ω^(Ω₁·(1 ⊕ A) ⊕ ρ)`。 -/
def powB118 (ls ns : List BT) : BT := BT.D 1 (mixB118 ls ns)
/-- `φ̄(1 ⊕ A, ω^ρ)`。 -/
def vebB118 (ls ns : List BT) : BT := BT.D 0 (powB118 ls ns)

/-- 尾の桁 — 主要成分であることが余分に要る。 -/
def TDig118 (n : BT) : Prop :=
  BT.isP n = true ∧ btLe72 1 n = true ∧ BT.isStd n = true ∧ Hd085 n

/-- **被覆条件** — §106 の `cov_vebB106` にあたるもの。`ns = []` なら `Dig106` から出る
    (`covM_nil118`)。決定可能な条件で、使うたびに実際に確かめる。 -/
def CovM118 (ls ns : List BT) : Prop :=
  ∀ e ∈ BT.GB 0 (mixB118 ls ns), BT.lt e (powB118 ls ns) = true

theorem mulB106_eq_ofL118 : ∀ (ls : List BT), mulB106 ls = BT.ofL (ls.map (BT.D 1))
  | [] => rfl
  | [_] => rfl
  | l :: l2 :: ls => by
      show BT.sum (BT.D 1 l) (mulB106 (l2 :: ls)) = _
      rw [mulB106_eq_ofL118 (l2 :: ls)]
      rfl

theorem mixB118_nil118 (ls : List BT) : mixB118 ls [] = mulB106 ls := by
  rw [mulB106_eq_ofL118]
  show BT.ofL (ls.map (BT.D 1) ++ []) = _
  rw [List.append_nil]

/-- 主要かつ頭が段 0 の項は `D 0 c` そのもの。 -/
theorem eq_D0_of_isP118 {n : BT} (hp : BT.isP n = true) (hd : Hd085 n) :
    ∃ c, n = BT.D 0 c := hd n (by rw [toL_isP118 hp]; exact List.Mem.head _)

theorem gb1_nil_tail118 {n : BT} (hp : BT.isP n = true) (hd : Hd085 n) :
    BT.GB 1 n = [] := by
  obtain ⟨c, hc⟩ := eq_D0_of_isP118 hp hd
  rw [hc]
  show (if 1 ≤ 0 then c :: BT.GB 1 c else []) = []
  rw [if_neg (by omega)]

theorem isP_mem_mix118 {ls ns : List BT} (hT : ∀ n ∈ ns, TDig118 n) :
    ∀ x ∈ ls.map (BT.D 1) ++ ns, BT.isP x = true := by
  intro x hx
  rcases List.mem_append.mp hx with h1 | h1
  · obtain ⟨l, _, hxl⟩ := List.mem_map.mp h1
    rw [← hxl]; rfl
  · exact (hT x h1).1

theorem toL_mixB118 {ls ns : List BT} (hT : ∀ n ∈ ns, TDig118 n) :
    BT.toL (mixB118 ls ns) = ls.map (BT.D 1) ++ ns :=
  toL_ofL118 _ (isP_mem_mix118 hT)

theorem gb1_digs118 : ∀ (ls : List BT), (∀ l ∈ ls, Hd085 l) →
    (ls.map (BT.D 1)).flatMap (BT.GB 1) = ls
  | [], _ => rfl
  | l :: r, h => by
      show BT.GB 1 (BT.D 1 l) ++ (r.map (BT.D 1)).flatMap (BT.GB 1) = _
      rw [gb1_digs118 r (fun z hz => h z (List.Mem.tail _ hz)),
        show BT.GB 1 (BT.D 1 l) = [l] from by
          show (if 1 ≤ 1 then l :: BT.GB 1 l else []) = [l]
          rw [if_pos (Nat.le_refl 1), gb1_nil98 l (h l (List.Mem.head _))]]
      rfl

theorem gb1_tails118 : ∀ (ns : List BT), (∀ n ∈ ns, TDig118 n) →
    ns.flatMap (BT.GB 1) = []
  | [], _ => rfl
  | n :: r, h => by
      show BT.GB 1 n ++ r.flatMap (BT.GB 1) = _
      rw [gb1_tails118 r (fun z hz => h z (List.Mem.tail _ hz)),
        gb1_nil_tail118 (h n (List.Mem.head _)).1 (h n (List.Mem.head _)).2.2.2]
      rfl

theorem gb0_digs118 : ∀ (ls : List BT),
    (ls.map (BT.D 1)).flatMap (BT.GB 0) = ls.flatMap (fun l => l :: BT.GB 0 l)
  | [] => rfl
  | l :: r => by
      show BT.GB 0 (BT.D 1 l) ++ (r.map (BT.D 1)).flatMap (BT.GB 0) = _
      rw [gb0_digs118 r,
        show BT.GB 0 (BT.D 1 l) = l :: BT.GB 0 l from by
          show (if 0 ≤ 1 then l :: BT.GB 0 l else []) = _
          rw [if_pos (by omega)]]
      rfl

theorem gb1_mixB118 {ls ns : List BT} (hD : ∀ l ∈ ls, Dig106 l)
    (hT : ∀ n ∈ ns, TDig118 n) : BT.GB 1 (mixB118 ls ns) = ls := by
  show BT.GB 1 (BT.ofL (ls.map (BT.D 1) ++ ns)) = _
  rw [gb_ofL118, List.flatMap_append, gb1_digs118 ls (fun l hl => (hD l hl).2.2.1),
    gb1_tails118 ns hT, List.append_nil]

theorem gb0_mixB118 {ls ns : List BT} :
    BT.GB 0 (mixB118 ls ns)
      = ls.flatMap (fun l => l :: BT.GB 0 l) ++ ns.flatMap (BT.GB 0) := by
  show BT.GB 0 (BT.ofL (ls.map (BT.D 1) ++ ns)) = _
  rw [gb_ofL118, List.flatMap_append, gb0_digs118 ls]

theorem btLe_mixB118 {ls ns : List BT} (hD : ∀ l ∈ ls, Dig106 l)
    (hT : ∀ n ∈ ns, TDig118 n) : btLe72 1 (mixB118 ls ns) = true := by
  refine btLe_ofL118 1 _ ?_
  intro x hx
  rcases List.mem_append.mp hx with h1 | h1
  · obtain ⟨l, hl, hxl⟩ := List.mem_map.mp h1
    rw [← hxl]
    show (decide (1 ≤ 1) && btLe72 1 l) = true
    rw [(hD l hl).1]; rfl
  · exact (hT x h1).2.1

theorem isStd_mixB118 {ls ns : List BT} (hD : ∀ l ∈ ls, Dig106 l)
    (hT : ∀ n ∈ ns, TDig118 n) (hde : bdesc106 (ls.map (BT.D 1) ++ ns)) :
    BT.isStd (mixB118 ls ns) = true := by
  refine isStd_ofL118 _ (isP_mem_mix118 hT) ?_ hde
  intro x hx
  rcases List.mem_append.mp hx with h1 | h1
  · obtain ⟨l, hl, hxl⟩ := List.mem_map.mp h1
    rw [← hxl]
    show (BT.isStd l && (BT.GB 1 l).all (fun e => BT.lt e l)) = true
    rw [(hD l hl).2.1, gb1_nil98 l (hD l hl).2.2.1]
    rfl
  · exact (hT x h1).2.2.1

end

/-! ### §118.2b 合法性 — 標準形・段・被覆 -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

theorem toL_mix_cons118 {l0 : BT} {r ns : List BT} (hT : ∀ n ∈ ns, TDig118 n) :
    BT.toL (mixB118 (l0 :: r) ns) = BT.D 1 l0 :: (r.map (BT.D 1) ++ ns) := by
  rw [toL_mixB118 hT]; rfl

theorem hd085_mix_nil118 {ns : List BT} (hT : ∀ n ∈ ns, TDig118 n) :
    Hd085 (mixB118 [] ns) := by
  intro x hx
  rw [toL_mixB118 hT] at hx
  exact eq_D0_of_isP118 (hT x (by simpa using hx)).1 (hT x (by simpa using hx)).2.2.2

/-- 桁は作った和より真に小さい。 -/
theorem btlt_dig_mix118 {ls ns : List BT} (hD : ∀ l ∈ ls, Dig106 l)
    (hT : ∀ n ∈ ns, TDig118 n) {l : BT} (hl : l ∈ ls) :
    BT.lt l (mixB118 ls ns) = true := by
  cases ls with
  | nil => cases hl
  | cons l0 r => exact btlt_hd0_hd1_106 (hD l hl).2.2.1 (toL_mix_cons118 hT)

theorem isStd_powB118 {ls ns : List BT} (hD : ∀ l ∈ ls, Dig106 l)
    (hT : ∀ n ∈ ns, TDig118 n) (hde : bdesc106 (ls.map (BT.D 1) ++ ns)) :
    BT.isStd (powB118 ls ns) = true := by
  show (BT.isStd (mixB118 ls ns) &&
    (BT.GB 1 (mixB118 ls ns)).all (fun e => BT.lt e (mixB118 ls ns))) = true
  rw [isStd_mixB118 hD hT hde, Bool.true_and, gb1_mixB118 hD hT, List.all_eq_true]
  intro x hx
  exact btlt_dig_mix118 hD hT hx

/-- `Ω₁·A ⊕ ρ < ω^(Ω₁·(1⊕A) ⊕ ρ)`。 -/
theorem btlt_mix_pow118 {ls ns : List BT} (hD : ∀ l ∈ ls, Dig106 l)
    (hT : ∀ n ∈ ns, TDig118 n) :
    BT.lt (mixB118 ls ns) (powB118 ls ns) = true := by
  cases ls with
  | nil => exact btlt_hd0_D1_98 (hd085_mix_nil118 hT) _
  | cons l0 r =>
      have hm := toL_mix_cons118 (l0 := l0) (r := r) hT
      have hlt : BT.lt l0 (mixB118 (l0 :: r) ns) = true :=
        btlt_dig_mix118 hD hT (List.Mem.head _)
      exact btlt_of_hd106 hm rfl (bt_ne_of_lt98 hlt) hlt

theorem gb0_sub_mix118 {ls ns : List BT} {l : BT} (hl : l ∈ ls) :
    ∀ e ∈ BT.GB 0 l, e ∈ BT.GB 0 (mixB118 ls ns) := by
  intro e he
  rw [gb0_mixB118]
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨l, hl, List.Mem.tail _ he⟩)

theorem mem_gb0_mix_dig118 {ls ns : List BT} {l : BT} (hl : l ∈ ls) :
    l ∈ BT.GB 0 (mixB118 ls ns) := by
  rw [gb0_mixB118]
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨l, hl, List.Mem.head _⟩)

theorem gb0_sub_mix_tail118 {ls ns : List BT} {n : BT} (hn : n ∈ ns) :
    ∀ e ∈ BT.GB 0 n, e ∈ BT.GB 0 (mixB118 ls ns) := by
  intro e he
  rw [gb0_mixB118]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨n, hn, he⟩)

theorem hd085_vebB118 (ls ns : List BT) : Hd085 (vebB118 ls ns) := by
  intro x hx
  exact ⟨powB118 ls ns, List.mem_singleton.mp hx⟩

theorem gb0_powB118 (ls ns : List BT) :
    BT.GB 0 (powB118 ls ns) = mixB118 ls ns :: BT.GB 0 (mixB118 ls ns) := by
  show (if 0 ≤ 1 then mixB118 ls ns :: BT.GB 0 (mixB118 ls ns) else []) = _
  rw [if_pos (by omega)]

theorem gb0_vebB118 (ls ns : List BT) :
    BT.GB 0 (vebB118 ls ns) = powB118 ls ns :: BT.GB 0 (powB118 ls ns) := by
  show (if 0 ≤ 0 then powB118 ls ns :: BT.GB 0 (powB118 ls ns) else []) = _
  rw [if_pos (by omega)]

theorem isStd_vebB118 {ls ns : List BT} (hD : ∀ l ∈ ls, Dig106 l)
    (hT : ∀ n ∈ ns, TDig118 n) (hde : bdesc106 (ls.map (BT.D 1) ++ ns))
    (hC : CovM118 ls ns) : BT.isStd (vebB118 ls ns) = true := by
  show (BT.isStd (powB118 ls ns) &&
    (BT.GB 0 (powB118 ls ns)).all (fun e => BT.lt e (powB118 ls ns))) = true
  rw [isStd_powB118 hD hT hde, Bool.true_and, gb0_powB118, List.all_eq_true]
  intro x hx
  rcases List.mem_cons.mp hx with h1 | h1
  · rw [h1]; exact btlt_mix_pow118 hD hT
  · exact hC x h1

theorem btLe_vebB118 {ls ns : List BT} (hD : ∀ l ∈ ls, Dig106 l)
    (hT : ∀ n ∈ ns, TDig118 n) : btLe72 1 (vebB118 ls ns) = true := by
  show (decide (0 ≤ 1) && (decide (1 ≤ 1) && btLe72 1 (mixB118 ls ns))) = true
  rw [btLe_mixB118 hD hT]
  rfl

/-- **段の正直さ (上)。**  上へは 1 まで。§85.6 の段 2 の反証には届かない。 -/
theorem btLe1_vebB118 {ls ns : List BT} (hD : ∀ l ∈ ls, Dig106 l)
    (hT : ∀ n ∈ ns, TDig118 n) : btLe72 1 (vebB118 ls ns) = true := btLe_vebB118 hD hT

/-- **段の正直さ (下)。**  段 0 は最初の一歩で離れる。§103.6 の `noLevel0_inMid103` が
    そう要求する。 -/
theorem btLe0_vebB118 (ls ns : List BT) : btLe72 0 (vebB118 ls ns) = false := rfl

/-- 段 0 頭で `GB 0` が `mix` に収まる項は、作った値より真に小さい。 -/
theorem btlt_hd0_veb118 {ls ns : List BT} (hC : CovM118 ls ns) {x : BT} (hx : Hd085 x)
    (hsub : ∀ e ∈ BT.GB 0 x, e ∈ BT.GB 0 (mixB118 ls ns)) :
    BT.lt x (vebB118 ls ns) = true := by
  cases hxl : BT.toL x with
  | nil =>
      show BT.ltL (BT.size x + BT.size (vebB118 ls ns) + 2) (BT.toL x)
        (BT.toL (vebB118 ls ns)) = true
      rw [hxl, show BT.size x + BT.size (vebB118 ls ns) + 2
          = (BT.size x + BT.size (vebB118 ls ns) + 1) + 1 from rfl]
      exact ltL_nil_cons93 _ _ _
  | cons y ys =>
      obtain ⟨c, hc⟩ := hx y (by rw [hxl]; exact List.Mem.head _)
      have hcg : c ∈ BT.GB 0 x :=
        mem_gb0_of_toL106 x 0 c (by rw [hxl, ← hc]; exact List.Mem.head _)
      have hcl : BT.lt c (powB118 ls ns) = true := hC c (hsub c hcg)
      exact btlt_of_hd106 (u := 0) (a := c) (b := powB118 ls ns) (ps := ys) (qs := [])
        (by rw [hxl, hc]) rfl (bt_ne_of_lt98 hcl) hcl

theorem btlt_mix_D1veb118 {ls ns : List BT} (hD : ∀ l ∈ ls, Dig106 l)
    (hT : ∀ n ∈ ns, TDig118 n) (hC : CovM118 ls ns) :
    BT.lt (mixB118 ls ns) (BT.D 1 (vebB118 ls ns)) = true := by
  cases ls with
  | nil => exact btlt_hd0_D1_98 (hd085_mix_nil118 hT) _
  | cons l0 r =>
      have hlt : BT.lt l0 (vebB118 (l0 :: r) ns) = true :=
        btlt_hd0_veb118 hC (hD l0 (List.Mem.head _)).2.2.1 (gb0_sub_mix118 (List.Mem.head _))
      exact btlt_of_hd106 (toL_mix_cons118 hT) rfl (bt_ne_of_lt98 hlt) hlt

/-- **作った値も桁として使える** — §106 の `cov_vebB106` を尾つきに広げたもの。 -/
theorem cov_vebB118 {ls ns : List BT} (hD : ∀ l ∈ ls, Dig106 l)
    (hT : ∀ n ∈ ns, TDig118 n) (hC : CovM118 ls ns) :
    ∀ e ∈ BT.GB 0 (vebB118 ls ns),
      BT.lt e (BT.D 1 (BT.D 1 (vebB118 ls ns))) = true := by
  intro e he
  have hmv : BT.lt (mixB118 ls ns) (BT.D 1 (vebB118 ls ns)) = true :=
    btlt_mix_D1veb118 hD hT hC
  have hvv : BT.lt (vebB118 ls ns) (BT.D 1 (vebB118 ls ns)) = true :=
    btlt_hd0_D1_98 (hd085_vebB118 ls ns) _
  rw [gb0_vebB118, gb0_powB118] at he
  rcases List.mem_cons.mp he with h1 | h1
  · rw [h1]
    exact btlt_arg98 (bt_ne_of_lt98 hmv) hmv
  rcases List.mem_cons.mp h1 with h2 | h2
  · rw [h2]
    exact lt_trans83 hmv (btlt_arg98 (bt_ne_of_lt98 hvv) hvv)
  · exact lt_trans83 (hC e h2)
      (btlt_arg98 (bt_ne_of_lt98 hmv) hmv)

/-- **証人は次の桁になる** — 構成は反復できる。 -/
theorem dig_vebB118 {ls ns : List BT} (hD : ∀ l ∈ ls, Dig106 l)
    (hT : ∀ n ∈ ns, TDig118 n) (hde : bdesc106 (ls.map (BT.D 1) ++ ns))
    (hC : CovM118 ls ns) : Dig106 (vebB118 ls ns) :=
  ⟨btLe_vebB118 hD hT, isStd_vebB118 hD hT hde hC, hd085_vebB118 ls ns,
    cov_vebB118 hD hT hC⟩

/-- 主要成分でもある。 -/
theorem tdig_vebB118 {ls ns : List BT} (hD : ∀ l ∈ ls, Dig106 l)
    (hT : ∀ n ∈ ns, TDig118 n) (hde : bdesc106 (ls.map (BT.D 1) ++ ns))
    (hC : CovM118 ls ns) : TDig118 (vebB118 ls ns) :=
  ⟨rfl, btLe_vebB118 hD hT, isStd_vebB118 hD hT hde hC, hd085_vebB118 ls ns⟩

theorem le_of_btlt118 {a b : BT} (h : BT.lt a b = true) : BT.le a b = true := by
  show ((a == b) || BT.lt a b) = true
  rw [h, Bool.or_true]

theorem bdesc_map_D1_118 : ∀ (ls : List BT), bdesc106 ls → bdesc106 (ls.map (BT.D 1))
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: b :: r, h => ⟨btle_arg106 h.1, bdesc_map_D1_118 (b :: r) h.2⟩

/-- 桁の列と尾の列がそれぞれ降順なら、並べたものも降順 — 段 1 は段 0 より上。 -/
theorem bdesc_mix118 {ls ns : List BT} (hT : ∀ n ∈ ns, TDig118 n)
    (hdl : bdesc106 ls) (hdn : bdesc106 ns) : bdesc106 (ls.map (BT.D 1) ++ ns) := by
  refine bdesc_append118 _ _ (bdesc_map_D1_118 ls hdl) hdn ?_
  intro y hy x hx
  obtain ⟨l, _, hxl⟩ := List.mem_map.mp hx
  rw [← hxl]
  exact le_of_btlt118 (btlt_hd0_D1_98 (hT y hy).2.2.2 l)

/-- **`ns = []` では被覆条件は `Dig106` から出る** — §106 の場合をそのまま含む。 -/
theorem covM_nil118 {ls : List BT} (hD : ∀ l ∈ ls, Dig106 l)
    (hde : bdesc106 ls) : CovM118 ls [] := by
  intro e he
  show BT.lt e (BT.D 1 (mixB118 ls [])) = true
  rw [mixB118_nil118] at he ⊢
  exact gb0_lt_powB106 hD hde e he

end

/-! ### §118.2c 値 — 係数が `1` でない Buchholz 証人 -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

theorem descL_append118 : ∀ (l1 l2 : List Term), descL l1 = true → descL l2 = true →
    (∀ y ∈ l2, ∀ x ∈ l1, le y x = true) → descL (l1 ++ l2) = true
  | [], l2, _, h2, _ => h2
  | [a], l2, _, h2, hj => by
      cases l2 with
      | nil => rfl
      | cons b r =>
          show (le b a && descL (b :: r)) = true
          rw [hj b (List.Mem.head _) a (List.Mem.head _), h2]
          rfl
  | a :: b :: r, l2, h1, h2, hj => by
      show (le b a && descL ((b :: r) ++ l2)) = true
      rw [(descL_cons.mp h1).1,
        descL_append118 (b :: r) l2 (descL_cons.mp h1).2 h2
          (fun y hy x hx => hj y hy x (List.Mem.tail _ hx))]
      rfl

/-- 成分がすべて右の項の頭以上なら、`plus` はただの連結。 -/
theorem plus_concat118 {s t : Term} (hs : inT s = true)
    (hj : ∀ y ∈ toList t, ∀ x ∈ toList s, le y x = true) :
    plus s t = ofList (toList s ++ toList t) := by
  cases hl : toList t with
  | nil => rw [plus_nil hl, List.append_nil, inT_ofList_toList s hs]
  | cons b1 r =>
      rw [plus_cons66 hl,
        show (toList s).filter (fun a => le b1 a) = toList s from
          List.filter_eq_self.mpr (fun x hx => hj b1 (by rw [hl]; exact List.Mem.head _) x hx)]

/-- **桁と尾の値。**  `dict (Ω₁·A ⊕ ρ) = Ω₁·A ⊕ ρ`。 -/
theorem dict_mixB118 (Hp : PsiIdxOKStd172) {A rho : Term} {ls ns : List BT}
    (hD : ∀ l ∈ ls, Dig106 l) (hT : ∀ n ∈ ns, TDig118 n)
    (hA : inT A = true)
    (hmap : ls.map dict = (toList A).map logOm)
    (hrho : inT rho = true) (hrhoW : lt rho (reg 1) = true)
    (hns : ns.map dict = toList rho) :
    dict (mixB118 ls ns) = plus (mulL (reg 1) A) rho := by
  have hmulT : inT (mulL (reg 1) A) = true := inT_mulL mulDescInT (inT_reg 1) hA
  have hmulL : toList (mulL (reg 1) A)
      = (toList A).map (fun p => omegaNF (plus (reg 1) (logOm p))) := toList_mulLW106
  have hpt : ∀ l ∈ ls, (fun l => dict (BT.D 1 l)) l
      = ((fun g => omegaNF (plus (reg 1) g)) ∘ dict) l := by
    intro l hl
    exact dict_D1_eq77 Hp l (hD l hl).1 (hD l hl).2.1
  have hdigs : ls.map (fun l => dict (BT.D 1 l)) = toList (mulL (reg 1) A) := by
    rw [hmulL, List.map_congr_left hpt, ← List.map_map, hmap, List.map_map]
    rfl
  have hjoin : ∀ y ∈ toList rho, ∀ x ∈ toList (mulL (reg 1) A), le y x = true := by
    intro y hy x hx
    exact le_of_lt94 (lt_of_ltW_geW106 (inTL_inT hrho y hy) (inTL_inT hmulT x hx)
      (ltW_toList79 rho hrho hrhoW y hy) (geW_mulL106 hA x hx))
  have hdesc : descL ((ls.map (BT.D 1) ++ ns).map dict) = true := by
    rw [List.map_append, List.map_map,
      show (dict ∘ BT.D 1) = (fun l => dict (BT.D 1 l)) from rfl, hdigs, hns]
    exact descL_append118 _ _ (by rw [hmulL]; exact mulDescInT (reg 1) A (inT_reg 1) hA)
      (inT_toList rho hrho).2 hjoin
  show dict (BT.ofL (ls.map (BT.D 1) ++ ns)) = _
  rw [dict_ofL118 _ (isP_mem_mix118 hT) hdesc, List.map_append, List.map_map,
    show (dict ∘ BT.D 1) = (fun l => dict (BT.D 1 l)) from rfl, hdigs, hns,
    plus_concat118 hmulT hjoin]

theorem omegaNF_ne_one118 {rho : Term} (hrho : inT rho = true) (hrhoM : lt rho M = true)
    (hne : rho ≠ zero) : (omegaNF rho == TM.Term.one) = false := by
  cases hc : (omegaNF rho == TM.Term.one) with
  | false => rfl
  | true =>
      exfalso
      have h1 : logOm (omegaNF rho) = rho := logOm_omegaNF106 hrho hrhoM
      rw [eq_of_beq hc] at h1
      exact hne (h1.symm.trans (show logOm TM.Term.one = zero by decide))

theorem ltW_omegaNF_lt118 {rho : Term} (hrho : inT rho = true) (hrhoW : lt rho (reg 1) = true) :
    lt (omegaNF rho) (reg 1) = true := by
  have h1 := lt_omegaNF_inT79 hrho (inT_reg 1) hrhoW
  rw [omegaNF_reg1_80] at h1
  exact h1

/-- **`ψ₁` の中身の値。**  `dict (ψ₁ (Ω₁·A ⊕ ρ)) = ω^(Ω₁·(1⊕A) ⊕ ρ)`、つまり
    §106 の一組の引数 `argV106 (1⊕A) (ω^ρ)` そのもの。**尾 `ρ` が係数を `1` から動かす。** -/
theorem dict_powB118 (Hp : PsiIdxOKStd172) {A rho : Term} {ls ns : List BT}
    (hD : ∀ l ∈ ls, Dig106 l) (hT : ∀ n ∈ ns, TDig118 n)
    (hde : bdesc106 (ls.map (BT.D 1) ++ ns))
    (hA : inT A = true) (hAM : lt A M = true) (hAW : lt A (reg 1) = true)
    (hmap : ls.map dict = (toList A).map logOm)
    (hrho : inT rho = true) (hrhoM : lt rho M = true) (hrhoW : lt rho (reg 1) = true)
    (hns : ns.map dict = toList rho) :
    dict (powB118 ls ns) = argV106 (plus TM.Term.one A) (omegaNF rho) := by
  have hmulT : inT (mulL (reg 1) A) = true := inT_mulL mulDescInT (inT_reg 1) hA
  show dict (BT.D 1 (mixB118 ls ns)) = _
  rw [dict_D1_eq77 Hp (mixB118 ls ns) (btLe_mixB118 hD hT) (isStd_mixB118 hD hT hde),
    dict_mixB118 Hp hD hT hA hmap hrho hrhoW hns,
    ← plus_assoc_inT (reg 1) (mulL (reg 1) A) rho (inT_reg 1) hmulT hrho,
    plus_one_mulL106 hA hAM hAW]
  show _ = omegaNF (plus (mulL (reg 1) (plus TM.Term.one A)) (logOm (omegaNF rho)))
  rw [logOm_omegaNF106 hrho hrhoM]

/-- **§118.2 の主定理 — 係数が `1` でない目標に、作った合法な証人。**
    `dict (vebB118 ls ns) = φ̄(1 ⊕ A, ω^ρ)`。`ns = []` なら `ω^ρ = 1` で §106 に戻る。 -/
theorem dict_vebB118 (Hp : PsiIdxOKStd172) {A rho : Term} {ls ns : List BT}
    (hD : ∀ l ∈ ls, Dig106 l) (hT : ∀ n ∈ ns, TDig118 n)
    (hde : bdesc106 (ls.map (BT.D 1) ++ ns))
    (hA : inT A = true) (hAM : lt A M = true) (hAW : lt A (reg 1) = true)
    (hmap : ls.map dict = (toList A).map logOm)
    (hrho : inT rho = true) (hrhoM : lt rho M = true) (hrhoW : lt rho (reg 1) = true)
    (hrhone : rho ≠ zero) (hns : ns.map dict = toList rho)
    (hnoskip : phiNF (plus TM.Term.one A) (omegaNF rho)
      = phi (plus TM.Term.one A) (omegaNF rho)) :
    dict (vebB118 ls ns) = phi (plus TM.Term.one A) (omegaNF rho) := by
  show collapse 0 (dict (powB118 ls ns)) = _
  rw [dict_powB118 Hp hD hT hde hA hAM hAW hmap hrho hrhoM hrhoW hns]
  exact collapse0_argAP106 (inT_plus inT_one106 hA)
    (lt_plus_M inT_one106 hA ltM_one106 hAM)
    (lt_plus_W79 inT_one106 hA ltW_one106 hAW) (ne_zero_plus_one106 hA)
    (inT_omegaNF hrho) (ltM_omegaNF hrho hrhoM) (ltW_omegaNF_lt118 hrho hrhoW)
    (isAP_omegaNF _) (omegaNF_ne_one118 hrho hrhoM hrhone) hnoskip

end

/-! ### §118.3 折り畳みの**あとの**組 — `acc := φ̄(a, acc ⊕ c)` -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- 二組目からの積み上げ。**これが §106 に無かった部分である。** -/
def foldV118 (acc : Term) : List (Term × Term) → Term
  | [] => acc
  | ac :: r => foldV118 (phiNF ac.1 (plus acc ac.2)) r

/-- 組の列がぜんぶで作る値。最初の組だけ `base` と `c ⊖ 1` を使う。 -/
def valP118 : List (Term × Term) → Term
  | [] => zero
  | ac :: r => foldV118 (phiNF ac.1 (plus (baseOf 0) (sub1 ac.2))) r

/-- **Veblen 枝しか通らない折り畳みは `foldV118` そのもの。** -/
theorem fold_some118 : ∀ (prs : List (Term × Term)) (i : Option Term) (acc : Term),
    (∀ p ∈ prs, le (reg 1) p.1 = false) →
    prs.foldl (stepF (reg 1) (baseOf 0)) (i, some acc) = (i, some (foldV118 acc prs))
  | [], _, _, _ => rfl
  | ac :: r, i, acc, h => by
      have hstep : stepF (reg 1) (baseOf 0) (i, some acc) ac
          = (i, some (phiNF ac.1 (plus acc ac.2))) := by
        show (if le (reg 1) ac.1 = true then _ else (i, some (phiNF ac.1 (plus acc ac.2)))) = _
        rw [if_neg (by rw [h ac (List.Mem.head _)]; exact Bool.noConfusion)]
      show (r.foldl (stepF (reg 1) (baseOf 0)) (stepF (reg 1) (baseOf 0) (i, some acc) ac)) = _
      rw [hstep, fold_some118 r i _ (fun p hp => h p (List.Mem.tail _ hp))]
      rfl

theorem fold_none118 {ac : Term × Term} {r : List (Term × Term)}
    (h : ∀ p ∈ ac :: r, le (reg 1) p.1 = false) :
    ((ac :: r).foldl (stepF (reg 1) (baseOf 0))
      ((none : Option Term), (none : Option Term))).2 = some (valP118 (ac :: r)) := by
  have hstep : stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term)) ac
      = ((none : Option Term), some (phiNF ac.1 (plus (baseOf 0) (sub1 ac.2)))) := by
    show (if le (reg 1) ac.1 = true then _ else
      ((none : Option Term), some (phiNF ac.1 (plus (baseOf 0) (sub1 ac.2))))) = _
    rw [if_neg (by rw [h ac (List.Mem.head _)]; exact Bool.noConfusion)]
  show (r.foldl (stepF (reg 1) (baseOf 0))
    (stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term)) ac)).2 = _
  rw [hstep, fold_some118 r none _ (fun p hp => h p (List.Mem.tail _ hp))]
  rfl

/-- **`n` 組の折り畳みの値。**  §106 の `collapse0_one_pair106` を組の数について一般に
    したもの。尾 `ρ` が `0` で、指数がぜんぶ `Ω₁` より下という二つだけが条件である。 -/
theorem collapse0_pairs118 {x R : Term} {ac : Term × Term} {r : List (Term × Term)}
    (hw : wcnf (reg 1) (toList x) = (ac :: r, zero))
    (hlow : ∀ p ∈ ac :: r, le (reg 1) p.1 = false)
    (hiR : inT R = true) (hRnf : omegaNF R = R)
    (hval : valP118 (ac :: r) = R) : collapse 0 x = R := by
  rw [collapse0_raw89]
  show omegaNF (plus (reg 0) (plus
    (((wcnf (reg 1) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero)
    ((wcnf (reg 1) (toList x)).2))) = _
  rw [hw]
  show omegaNF (plus (reg 0) (plus
    (((ac :: r).foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero) zero)) = _
  rw [fold_none118 hlow]
  show omegaNF (plus (reg 0) (plus (valP118 (ac :: r)) zero)) = _
  rw [hval, show plus R zero = R from rfl,
    show plus (reg 0) R = plus zero R from rfl, plus_zero_left_inT hiR, hRnf]

end

/-! ### §118.3b `wcnf` を `n` 成分で読む -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- **一成分ぶんの分解。**  §106 の `collapse0_argV106` の中で計算されていた三つを
    取り出したもの — 一組では使い捨てだったが、`n` 組では帰納法の材料になる。 -/
theorem argV_facts118 {A B : Term} (hA : inT A = true) (hAM : lt A M = true)
    (hAW : lt A (reg 1) = true) (hAne : A ≠ zero)
    (hB : inT B = true) (hBM : lt B M = true) (hgW0 : lt (logOm B) (reg 1) = true) :
    lt (argV106 A B) (reg 1) = false ∧ wA (reg 1) (argV106 A B) = A
      ∧ wC (reg 1) (argV106 A B) = omegaNF (logOm B) := by
  have hg : inT (logOm B) = true := inT_logOm hB
  have hgM : lt (logOm B) M = true := ltM_logOm hB hBM
  have hgW : ∀ q ∈ toList (logOm B), lt q (reg 1) = true :=
    ltW_toList79 (logOm B) hg hgW0
  have hmul : inT (mulL (reg 1) A) = true := inT_mulL mulDescInT (inT_reg 1) hA
  have hmulM : lt (mulL (reg 1) A) M = true := ltM_mulL (inT_reg 1) hA (ltM_reg 1) hAM
  have hY : inT (plus (mulL (reg 1) A) (logOm B)) = true := inT_plus hmul hg
  have hYM : lt (plus (mulL (reg 1) A) (logOm B)) M = true := lt_plus_M hmul hg hmulM hgM
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
  refine ⟨ltW_omegaNF106 hY hYW, ?_, ?_⟩
  · show ofList (((toList (logOm (argV106 A B))).filter
      (fun q => !lt q (reg 1))).map (divAP (reg 1))) = A
    rw [hlog, hfil1]
    exact divAP_mulL106 hA hAM hAW
  · show omegaNF (ofList ((toList (logOm (argV106 A B))).filter (fun q => lt q (reg 1))))
      = omegaNF (logOm B)
    rw [hlog, hfil2, inT_ofList_toList (logOm B) hg]

/-- 組の列から `ψ₀` の引数を組み立てる — `Trans.Dict.xOf` の、係数が加法主要な場合。 -/
def argM118 (prs : List (Term × Term)) : Term :=
  ofList (prs.map (fun ac => argV106 ac.1 ac.2))

/-- 一組が満たすべき条件 — 指数は `0` でなく `Ω₁` より下、係数は加法主要で `Ω₁` より下。 -/
def OKP118 (ac : Term × Term) : Prop :=
  inT ac.1 = true ∧ lt ac.1 M = true ∧ lt ac.1 (reg 1) = true ∧ ac.1 ≠ zero ∧
    inT ac.2 = true ∧ lt ac.2 M = true ∧ lt ac.2 (reg 1) = true ∧ ac.2.isAP = true

/-- 指数は隣り合って真に降る — これが `wcnf` の併合を止める。 -/
def descP118 : List (Term × Term) → Prop
  | [] => True
  | [_] => True
  | a :: b :: r => lt b.1 a.1 = true ∧ descP118 (b :: r)

theorem descP_tail118 {a : Term × Term} {l : List (Term × Term)}
    (h : descP118 (a :: l)) : descP118 l := by
  cases l with
  | nil => trivial
  | cons b r => exact h.2

theorem toList_argM118 (prs : List (Term × Term)) :
    toList (argM118 prs) = prs.map (fun ac => argV106 ac.1 ac.2) := by
  refine toList_ofList _ ?_
  intro x hx
  obtain ⟨ac, _, hxa⟩ := List.mem_map.mp hx
  rw [← hxa]
  exact isAP_omegaNF _

theorem wC_eq_of_OKP118 {ac : Term × Term} (h : OKP118 ac) :
    omegaNF (logOm ac.2) = ac.2 :=
  omegaNF_logOm100 h.2.2.2.2.1 h.2.2.2.2.2.2.2 h.2.2.2.2.2.1

theorem ltW_logOm_of_OKP118 {ac : Term × Term} (h : OKP118 ac) :
    lt (logOm ac.2) (reg 1) = true :=
  ltW_logOm106 h.2.2.2.2.1 h.2.2.2.2.2.2.2 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1

/-- **`n` 成分の底 `Ω₁` 分解。**  組がそのまま戻る。尾は `0`。 -/
theorem wcnf_argM118 : ∀ (prs : List (Term × Term)), (∀ p ∈ prs, OKP118 p) →
    descP118 prs → wcnf (reg 1) (toList (argM118 prs)) = (prs, zero)
  | [], _, _ => rfl
  | ac :: r, hOK, hd => by
      have hac := hOK ac (List.Mem.head _)
      have hf := argV_facts118 hac.1 hac.2.1 hac.2.2.1 hac.2.2.2.1
        hac.2.2.2.2.1 hac.2.2.2.2.2.1 (ltW_logOm_of_OKP118 hac)
      have hih := wcnf_argM118 r (fun p hp => hOK p (List.Mem.tail _ hp)) (descP_tail118 hd)
      rw [toList_argM118] at hih ⊢
      show wcnf (reg 1) (argV106 ac.1 ac.2 :: r.map (fun ac => argV106 ac.1 ac.2)) = _
      rw [wcnf_cons_ge hf.1, hih, hf.2.1, hf.2.2, wC_eq_of_OKP118 hac]
      cases r with
      | nil => rfl
      | cons b r' =>
          have hlt : lt b.1 ac.1 = true := hd.1
          have hne : (ac.1 == b.1) = false := by
            cases hc : (ac.1 == b.1) with
            | false => rfl
            | true =>
                exfalso
                rw [← eq_of_beq hc, lt_irrefl] at hlt
                exact Bool.noConfusion hlt
          show (if (ac.1 == b.1) = true then _ else ((ac.1, ac.2) :: (b.1, b.2) :: r', zero))
            = _
          rw [if_neg (by rw [hne]; exact Bool.noConfusion)]

/-- **§118.3 の主定理 — `n` 組の値。**  `ψ₀(Σ ω^(Ω₁·aᵢ ⊕ log cᵢ))` は
    `φ̄(aₙ, … φ̄(a₁, c₁ ⊖ 1) ⊕ … ⊕ cₙ)`。**あとの組が読めるようになった。** -/
theorem collapse0_argM118 {ac : Term × Term} {r : List (Term × Term)} {R : Term}
    (hOK : ∀ p ∈ ac :: r, OKP118 p) (hd : descP118 (ac :: r))
    (hiR : inT R = true) (hRnf : omegaNF R = R)
    (hval : valP118 (ac :: r) = R) : collapse 0 (argM118 (ac :: r)) = R := by
  refine collapse0_pairs118 (wcnf_argM118 (ac :: r) hOK hd) ?_ hiR hRnf hval
  intro p hp
  exact leW_false106 (hOK p hp).1 (hOK p hp).2.2.1

end

/-! ### §118.4 `n` 組ぶんの Buchholz 証人 -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- `ψ₁` を横に並べたもの — 組ひとつにつき `ψ₁` ひとつ。 -/
def powN118 (ys : List BT) : BT := BT.ofL (ys.map (BT.D 1))
/-- そして `ψ₀` をかぶせる。 -/
def vebN118 (ys : List BT) : BT := BT.D 0 (powN118 ys)

/-- **被覆条件、`n` 組の形。** -/
def CovN118 (ys : List BT) : Prop :=
  ∀ e ∈ BT.GB 0 (powN118 ys), BT.lt e (powN118 ys) = true

/-- 一元リストなら §118.2 の構成そのもの。 -/
theorem vebN_one118 (ls ns : List BT) : vebN118 [mixB118 ls ns] = vebB118 ls ns := rfl

theorem gb0_powN118 (ys : List BT) :
    BT.GB 0 (powN118 ys) = ys.flatMap (fun y => y :: BT.GB 0 y) := by
  show BT.GB 0 (BT.ofL (ys.map (BT.D 1))) = _
  rw [gb_ofL118, gb0_digs118]

theorem gb0_vebN118 (ys : List BT) :
    BT.GB 0 (vebN118 ys) = powN118 ys :: BT.GB 0 (powN118 ys) := by
  show (if 0 ≤ 0 then powN118 ys :: BT.GB 0 (powN118 ys) else []) = _
  rw [if_pos (by omega)]

theorem btLe_powN118 {ys : List BT} (h : ∀ y ∈ ys, btLe72 1 y = true) :
    btLe72 1 (powN118 ys) = true := by
  refine btLe_ofL118 1 _ ?_
  intro x hx
  obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hx
  rw [← hxy]
  show (decide (1 ≤ 1) && btLe72 1 y) = true
  rw [h y hy]; rfl

theorem isStd_powN118 {ys : List BT} (h : ∀ y ∈ ys, BT.isStd (BT.D 1 y) = true)
    (hde : bdesc106 ys) : BT.isStd (powN118 ys) = true := by
  refine isStd_ofL118 _ ?_ ?_ (bdesc_map_D1_118 ys hde)
  · intro x hx
    obtain ⟨y, _, hxy⟩ := List.mem_map.mp hx
    rw [← hxy]; rfl
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hx
    rw [← hxy]
    exact h y hy

theorem hd085_vebN118 (ys : List BT) : Hd085 (vebN118 ys) := by
  intro x hx
  exact ⟨powN118 ys, List.mem_singleton.mp hx⟩

theorem btLe_vebN118 {ys : List BT} (h : ∀ y ∈ ys, btLe72 1 y = true) :
    btLe72 1 (vebN118 ys) = true := by
  show (decide (0 ≤ 1) && btLe72 1 (powN118 ys)) = true
  rw [btLe_powN118 h]; rfl

/-- **段の正直さ。**  上へは 1 まで、下は最初の一歩で 0 を離れる。 -/
theorem btLe1_vebN118 {ys : List BT} (h : ∀ y ∈ ys, btLe72 1 y = true) :
    btLe72 1 (vebN118 ys) = true := btLe_vebN118 h

theorem btLe0_vebN118 : ∀ (y : BT) (r : List BT), btLe72 0 (vebN118 (y :: r)) = false
  | _, [] => rfl
  | _, _ :: _ => rfl

theorem isStd_vebN118 {ys : List BT} (h : ∀ y ∈ ys, BT.isStd (BT.D 1 y) = true)
    (hde : bdesc106 ys) (hC : CovN118 ys) : BT.isStd (vebN118 ys) = true := by
  show (BT.isStd (powN118 ys) &&
    (BT.GB 0 (powN118 ys)).all (fun e => BT.lt e (powN118 ys))) = true
  rw [isStd_powN118 h hde, Bool.true_and, List.all_eq_true]
  intro x hx
  exact hC x hx

/-- **`n` 個の `ψ₁` の値。** -/
theorem dict_powN118 {ys : List BT}
    (hdesc : descL (ys.map (fun y => dict (BT.D 1 y))) = true) :
    dict (powN118 ys) = ofList (ys.map (fun y => dict (BT.D 1 y))) := by
  show dict (BT.ofL (ys.map (BT.D 1))) = _
  rw [dict_ofL118 _ (by
      intro x hx
      obtain ⟨y, _, hxy⟩ := List.mem_map.mp hx
      rw [← hxy]; rfl) (by
      rw [List.map_map]
      exact hdesc), List.map_map]
  rfl

/-- **§118.4 の主定理 — `n` 組の目標に、作った証人。**  `ψ₀` の下に `ψ₁` を `n` 個
    並べる。`ys` が一つなら §118.2、その `ns` が空なら §106 である。 -/
theorem dict_vebN118 {ys : List BT}
    {ac : Term × Term} {r : List (Term × Term)} {R : Term}
    (hdesc : descL (ys.map (fun y => dict (BT.D 1 y))) = true)
    (hcomp : ys.map (fun y => dict (BT.D 1 y))
      = (ac :: r).map (fun p => argV106 p.1 p.2))
    (hOK : ∀ p ∈ ac :: r, OKP118 p) (hd : descP118 (ac :: r))
    (hiR : inT R = true) (hRnf : omegaNF R = R)
    (hval : valP118 (ac :: r) = R) :
    dict (vebN118 ys) = R := by
  show collapse 0 (dict (powN118 ys)) = _
  rw [dict_powN118 hdesc, hcomp]
  exact collapse0_argM118 hOK hd hiR hRnf hval

end

/-! ### §118.3c 尾 `ρ` — `ω` 冪も同じ折り畳みで出る -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- 組の列と `Ω₁` より下の尾から `ψ₀` の引数を組み立てる。 -/
def argT118 (prs : List (Term × Term)) (rho : Term) : Term :=
  ofList (prs.map (fun ac => argV106 ac.1 ac.2) ++ toList rho)

theorem toList_argT118 {prs : List (Term × Term)} {rho : Term} (hrho : inT rho = true) :
    toList (argT118 prs rho) = prs.map (fun ac => argV106 ac.1 ac.2) ++ toList rho := by
  refine toList_ofList _ ?_
  intro x hx
  rcases List.mem_append.mp hx with h1 | h1
  · obtain ⟨ac, _, hxa⟩ := List.mem_map.mp h1
    rw [← hxa]
    exact isAP_omegaNF _
  · exact inTL_isAP hrho x h1

/-- **尾つきの底 `Ω₁` 分解。** -/
theorem wcnf_argT118 {rho : Term} (hrho : inT rho = true) (hrhoW : lt rho (reg 1) = true) :
    ∀ (prs : List (Term × Term)), (∀ p ∈ prs, OKP118 p) → descP118 prs →
      wcnf (reg 1) (prs.map (fun ac => argV106 ac.1 ac.2) ++ toList rho) = (prs, rho)
  | [], _, _ => by
      show wcnf (reg 1) (toList rho) = ([], rho)
      rw [wcnf_all_lt77 (reg 1) (toList rho) (ltW_toList79 rho hrho hrhoW),
        inT_ofList_toList rho hrho]
  | ac :: r, hOK, hd => by
      have hac := hOK ac (List.Mem.head _)
      have hf := argV_facts118 hac.1 hac.2.1 hac.2.2.1 hac.2.2.2.1
        hac.2.2.2.2.1 hac.2.2.2.2.2.1 (ltW_logOm_of_OKP118 hac)
      have hih := wcnf_argT118 hrho hrhoW r (fun p hp => hOK p (List.Mem.tail _ hp))
        (descP_tail118 hd)
      show wcnf (reg 1)
        (argV106 ac.1 ac.2 :: (r.map (fun ac => argV106 ac.1 ac.2) ++ toList rho)) = _
      rw [wcnf_cons_ge hf.1, hih, hf.2.1, hf.2.2, wC_eq_of_OKP118 hac]
      cases r with
      | nil => rfl
      | cons b r' =>
          have hlt : lt b.1 ac.1 = true := hd.1
          have hne : (ac.1 == b.1) = false := by
            cases hc : (ac.1 == b.1) with
            | false => rfl
            | true =>
                exfalso
                rw [← eq_of_beq hc, lt_irrefl] at hlt
                exact Bool.noConfusion hlt
          show (if (ac.1 == b.1) = true then _ else ((ac.1, ac.2) :: (b.1, b.2) :: r', rho))
            = _
          rw [if_neg (by rw [hne]; exact Bool.noConfusion)]

/-- **尾つきの折り畳みの値。**  `collapse0_pairs118` の `ρ = 0` を外したもの。
    ここで初めて第 1 Veblen 引数が `0` の目標 — `ω` 冪 — に届く。 -/
theorem collapse0_pairsT118 {x rho : Term} {ac : Term × Term} {r : List (Term × Term)}
    (hw : wcnf (reg 1) (toList x) = (ac :: r, rho))
    (hlow : ∀ p ∈ ac :: r, le (reg 1) p.1 = false)
    (hiS : inT (plus (valP118 (ac :: r)) rho) = true) :
    collapse 0 x = omegaNF (plus (valP118 (ac :: r)) rho) := by
  rw [collapse0_raw89]
  show omegaNF (plus (reg 0) (plus
    (((wcnf (reg 1) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero)
    ((wcnf (reg 1) (toList x)).2))) = _
  rw [hw]
  show omegaNF (plus (reg 0) (plus
    (((ac :: r).foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero) rho)) = _
  rw [fold_none118 hlow]
  show omegaNF (plus (reg 0) (plus (valP118 (ac :: r)) rho)) = _
  rw [show plus (reg 0) (plus (valP118 (ac :: r)) rho)
      = plus zero (plus (valP118 (ac :: r)) rho) from rfl, plus_zero_left_inT hiS]

/-- **§118.3c の主定理。**  組の列 + 尾から、`ψ₀` の値がそのまま読める。 -/
theorem collapse0_argT118 {rho : Term} {ac : Term × Term} {r : List (Term × Term)}
    (hOK : ∀ p ∈ ac :: r, OKP118 p) (hd : descP118 (ac :: r))
    (hrho : inT rho = true) (hrhoW : lt rho (reg 1) = true)
    (hiS : inT (plus (valP118 (ac :: r)) rho) = true) :
    collapse 0 (argT118 (ac :: r) rho)
      = omegaNF (plus (valP118 (ac :: r)) rho) := by
  refine collapse0_pairsT118 (rho := rho) ?_ ?_ hiS
  · rw [toList_argT118 hrho]
    exact wcnf_argT118 hrho hrhoW (ac :: r) hOK hd
  · intro p hp
    exact leW_false106 (hOK p hp).1 (hOK p hp).2.2.1

end

/-! ### §118.4b `ψ₁` の列と `ψ₀` の尾 — 一般の証人 -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- **一般の証人。**  `ψ₀` の下に `ψ₁` を `ys` 個並べ、そのうしろに段 0 の尾 `ms`。
    `ms = []` なら §118.4 の `vebN118`、`ys` が一元なら §118.2 の `vebB118` である。 -/
def vebG118 (ys ms : List BT) : BT := BT.D 0 (mixB118 ys ms)

/-- 被覆条件、一般の形 — 外側が `ψ₀` なので `mix` 自身より下でよい。 -/
def CovG118 (ys ms : List BT) : Prop :=
  ∀ e ∈ BT.GB 0 (mixB118 ys ms), BT.lt e (mixB118 ys ms) = true

theorem vebG_nil118 (ys : List BT) : vebG118 ys [] = vebN118 ys := by
  show BT.D 0 (BT.ofL (ys.map (BT.D 1) ++ [])) = _
  rw [List.append_nil]
  rfl

theorem btLe_mixG118 {ys ms : List BT} (hY : ∀ y ∈ ys, btLe72 1 y = true)
    (hM : ∀ m ∈ ms, TDig118 m) : btLe72 1 (mixB118 ys ms) = true := by
  refine btLe_ofL118 1 _ ?_
  intro x hx
  rcases List.mem_append.mp hx with h1 | h1
  · obtain ⟨y, hy, hxy⟩ := List.mem_map.mp h1
    rw [← hxy]
    show (decide (1 ≤ 1) && btLe72 1 y) = true
    rw [hY y hy]; rfl
  · exact (hM x h1).2.1

theorem isStd_mixG118 {ys ms : List BT} (hY : ∀ y ∈ ys, BT.isStd (BT.D 1 y) = true)
    (hM : ∀ m ∈ ms, TDig118 m) (hde : bdesc106 (ys.map (BT.D 1) ++ ms)) :
    BT.isStd (mixB118 ys ms) = true := by
  refine isStd_ofL118 _ (isP_mem_mix118 hM) ?_ hde
  intro x hx
  rcases List.mem_append.mp hx with h1 | h1
  · obtain ⟨y, hy, hxy⟩ := List.mem_map.mp h1
    rw [← hxy]
    exact hY y hy
  · exact (hM x h1).2.2.1

theorem isStd_vebG118 {ys ms : List BT} (hY : ∀ y ∈ ys, BT.isStd (BT.D 1 y) = true)
    (hM : ∀ m ∈ ms, TDig118 m) (hde : bdesc106 (ys.map (BT.D 1) ++ ms))
    (hC : CovG118 ys ms) : BT.isStd (vebG118 ys ms) = true := by
  show (BT.isStd (mixB118 ys ms) &&
    (BT.GB 0 (mixB118 ys ms)).all (fun e => BT.lt e (mixB118 ys ms))) = true
  rw [isStd_mixG118 hY hM hde, Bool.true_and, List.all_eq_true]
  intro x hx
  exact hC x hx

theorem hd085_vebG118 (ys ms : List BT) : Hd085 (vebG118 ys ms) := by
  intro x hx
  exact ⟨mixB118 ys ms, List.mem_singleton.mp hx⟩

/-- **段の正直さ (上)。** -/
theorem btLe1_vebG118 {ys ms : List BT} (hY : ∀ y ∈ ys, btLe72 1 y = true)
    (hM : ∀ m ∈ ms, TDig118 m) : btLe72 1 (vebG118 ys ms) = true := by
  show (decide (0 ≤ 1) && btLe72 1 (mixB118 ys ms)) = true
  rw [btLe_mixG118 hY hM]; rfl

theorem btLe0_ofL_D1_118 : ∀ (y : BT) (L : List BT), btLe72 0 (BT.ofL (BT.D 1 y :: L)) = false
  | _, [] => rfl
  | _, _ :: _ => rfl

/-- **段の正直さ (下)。**  `ψ₁` を一つでも使えば段 0 を離れる。 -/
theorem btLe0_vebG118 (y : BT) (r ms : List BT) :
    btLe72 0 (vebG118 (y :: r) ms) = false := by
  show (decide (0 ≤ 0) && btLe72 0 (BT.ofL (BT.D 1 y :: (r.map (BT.D 1) ++ ms)))) = false
  rw [btLe0_ofL_D1_118]
  rfl

/-- **§118.4b の主定理 — 一般の証人の値。** -/
theorem dict_vebG118 {ys ms : List BT} {ac : Term × Term} {r : List (Term × Term)}
    {rho : Term}
    (hM : ∀ m ∈ ms, TDig118 m)
    (hdesc : descL ((ys.map (BT.D 1) ++ ms).map dict) = true)
    (hcomp : (ys.map (BT.D 1) ++ ms).map dict
      = (ac :: r).map (fun p => argV106 p.1 p.2) ++ toList rho)
    (hOK : ∀ p ∈ ac :: r, OKP118 p) (hd : descP118 (ac :: r))
    (hrho : inT rho = true) (hrhoW : lt rho (reg 1) = true)
    (hiS : inT (plus (valP118 (ac :: r)) rho) = true) :
    dict (vebG118 ys ms) = omegaNF (plus (valP118 (ac :: r)) rho) := by
  have hx : dict (mixB118 ys ms) = argT118 (ac :: r) rho := by
    show dict (BT.ofL (ys.map (BT.D 1) ++ ms)) = _
    rw [dict_ofL118 _ (isP_mem_mix118 hM) hdesc, hcomp]
    rfl
  show collapse 0 (dict (mixB118 ys ms)) = _
  rw [hx]
  exact collapse0_argT118 hOK hd hrho hrhoW hiS

end

/-! ### §118.5 §106 を含むこと、そして残るものを名指す -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- **§106 はここの尾が空の場合である。** -/
theorem vebB118_nil118 (ls : List BT) : vebB118 ls [] = vebB106 ls := by
  show BT.D 0 (BT.D 1 (mixB118 ls [])) = _
  rw [mixB118_nil118]
  rfl

/-- **一元リストは §118.2 の構成である。** -/
theorem vebG_one118 (ls ns : List BT) : vebG118 [mixB118 ls ns] [] = vebB118 ls ns := by
  rw [vebG_nil118]
  rfl

/-- **名指しの否定 — 係数が加法主要でないと、一成分の形は別の値を計算する。**
    `argM118 [(1,2)]` の底 `Ω₁` 分解は `(1, ω²)` であって `(1,2)` ではない。和の係数は
    **同じ指数の成分をいくつも並べて `wcnf` に併合させる**ほかなく、それは `descP118` が
    禁じている形そのものである。§118 の残余の片方はこれで、`OKP118` の `isAP` は飾りでない。 -/
theorem noMerge118 :
    collapse 0 (argM118 [(TM.Term.one, ofNat 2)]) ≠ valP118 [(TM.Term.one, ofNat 2)] := by
  decide

end

/-! ### §118.6 測定 — 三つの母集団と、§103.8 の敵対的な母集団 -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1 dictInv)
open TM TM.Term
open Evidence.WF

/-- `OKP118` と `descP118` をそのまま Bool にしたもの。 -/
def okpB118 (ac : Term × Term) : Bool :=
  inT ac.1 && lt ac.1 M && lt ac.1 (reg 1) && !(ac.1 == zero) &&
    inT ac.2 && lt ac.2 M && lt ac.2 (reg 1) && ac.2.isAP

def descPB118 : List (Term × Term) → Bool
  | [] => true
  | [_] => true
  | a :: b :: r => lt b.1 a.1 && descPB118 (b :: r)

def hypP118 (prs : List (Term × Term)) : Bool :=
  !prs.isEmpty && prs.all okpB118 && descPB118 prs

def tdigB118 (n : BT) : Bool := BT.isP n && btLe72 1 n && BT.isStd n && hd085B n

def covMB118 (ls ns : List BT) : Bool :=
  (BT.GB 0 (mixB118 ls ns)).all (fun e => BT.lt e (powB118 ls ns))

/-! **母集団 1 — 組の列。**  種に `Γ₀` (強臨界) と `2` (係数が加法主要でない形) を
    入れてある。**濾していない。** -/
private def aS118 : List Term := [TM.Term.one, ofNat 2, phi TM.Term.one zero, G094]
private def cS118 : List Term := [TM.Term.one, TM.Term.omega, ofNat 2]

def pSeed118 : List (Term × Term) := aS118.flatMap fun a => cS118.map fun c => (a, c)

def pPool118 : List (List (Term × Term)) :=
  pSeed118.map (fun p => [p]) ++ (pSeed118.flatMap fun p => pSeed118.map fun q => [p, q])

#eval (pPool118.length, pPool118.countP hypP118,
       pPool118.countP fun prs => hypP118 prs && prs.length ≥ 2)
/-! **仮説が立つところではぴったり。** -/
#guard pPool118.all fun prs =>
  !(hypP118 prs) || (collapse 0 (argM118 prs) == valP118 prs)
/-! **あとの組が実際に効いている** — 仮説が立つものの多くは二組である。 -/
#guard (pPool118.countP fun prs => hypP118 prs && prs.length ≥ 2) == 24
/-! **仮説は見えていて、結論の言い換えでもない。** -/
#guard (pPool118.countP fun prs => !(hypP118 prs)) == 124
#guard (pPool118.countP fun prs =>
  !(hypP118 prs) && (collapse 0 (argM118 prs) == valP118 prs)) == 24

/-! **名指しの否定 — 係数 `2` は一成分では書けない。** -/
#guard !(collapse 0 (argM118 [(TM.Term.one, ofNat 2)]) == valP118 [(TM.Term.one, ofNat 2)])
#guard valP118 [(TM.Term.one, ofNat 2)] == phi TM.Term.one TM.Term.one
#guard collapse 0 (argM118 [(TM.Term.one, ofNat 2)])
  == phi TM.Term.one (omegaNF (plus TM.Term.one TM.Term.one))

/-! **母集団 2 — 尾 `ρ` つき。** -/
def rhoS118 : List Term := [zero, TM.Term.one, TM.Term.omega, plus TM.Term.omega TM.Term.one]

def tPool118 : List (List (Term × Term) × Term) :=
  ((pSeed118.map fun p => [p])
    ++ (pSeed118.take 4).flatMap (fun p => (pSeed118.take 4).map fun q => [p, q])).flatMap
      fun prs => rhoS118.map fun r => (prs, r)

def hypT118 (q : List (Term × Term) × Term) : Bool :=
  hypP118 q.1 && inT q.2 && lt q.2 (reg 1) && inT (plus (valP118 q.1) q.2)

#eval (tPool118.length, tPool118.countP hypT118)
#guard tPool118.all fun q =>
  !(hypT118 q) || (collapse 0 (argT118 q.1 q.2) == omegaNF (plus (valP118 q.1) q.2))
/-! **尾は `ω` 冪への唯一の道** — `ρ ≠ 0` の 30 件はどれも第 1 Veblen 引数が `0`。 -/
#guard (tPool118.countP fun q => hypT118 q && !(q.2 == zero)) == 30
#guard (tPool118.filter fun q => hypT118 q && !(q.2 == zero)).all fun q =>
  match omegaNF (plus (valP118 q.1) q.2) with | phi a _ => a == zero | _ => false

/-! **母集団 3 — 桁と尾の Buchholz 側。**  昇順のものも被覆条件を破るものも入れてある。 -/
private def dS118 : List BT := [BT.zero, BT.D 0 BT.zero, BT.D 0 (BT.D 1 BT.zero)]
private def tS118 : List BT :=
  [BT.D 0 BT.zero, BT.D 0 (BT.D 1 BT.zero), BT.D 0 (BT.D 1 (BT.D 1 BT.zero))]

def lsPool118 : List (List BT) :=
  [] :: dS118.map (fun x => [x]) ++ dS118.flatMap (fun x => dS118.map fun y => [x, y])
def nsPool118 : List (List BT) :=
  [] :: tS118.map (fun x => [x]) ++ tS118.flatMap (fun x => tS118.map fun y => [x, y])
def wPool118 : List (List BT × List BT) :=
  lsPool118.flatMap fun ls => nsPool118.map fun ns => (ls, ns)

def aOf118 (ls : List BT) : Term := ofList (ls.map fun l => omegaNF (dict l))
def rhoOf118 (ns : List BT) : Term := ofList (ns.map dict)

def hypW118 (ls ns : List BT) : Bool :=
  ls.all digB106 && ns.all tdigB118 && bdescB106 (ls.map (BT.D 1) ++ ns)
    && covMB118 ls ns && !(rhoOf118 ns == zero)
    && (phiNF (plus TM.Term.one (aOf118 ls)) (omegaNF (rhoOf118 ns))
        == phi (plus TM.Term.one (aOf118 ls)) (omegaNF (rhoOf118 ns)))

#eval (wPool118.length, wPool118.countP fun q => hypW118 q.1 q.2)
/-! **仮説が立つところでは値も合法性もぴったり。** -/
#guard wPool118.all fun q =>
  !(hypW118 q.1 q.2) ||
    ((dict (vebB118 q.1 q.2) == phi (plus TM.Term.one (aOf118 q.1)) (omegaNF (rhoOf118 q.2)))
      && BT.isStd (vebB118 q.1 q.2) && btLe72 1 (vebB118 q.1 q.2)
      && (btLe72 0 (vebB118 q.1 q.2) == false) && hd085B (vebB118 q.1 q.2)
      && digB106 (vebB118 q.1 q.2) && tdigB118 (vebB118 q.1 q.2))
/-! **どれも係数が `1` でない** — 尾が空でないものだけが仮説を満たす。 -/
#guard (wPool118.countP fun q => hypW118 q.1 q.2 && q.2.isEmpty) == 0
#guard (wPool118.countP fun q => hypW118 q.1 q.2) == 86

/-! **被覆条件は、この母集団では見える。**  §106 は 289 項を掃いて合法な 19 項が全部
    条件を満たし (§93 の失敗の形)、`deep106` を手で組むほかなかった。尾を付けると
    条件は母集団の中で発火する: 桁も尾も合法で降順なのに `CovM118` を破るものが 4 件、
    どれも標準形でない項を作る。**そのうち 3 件は値だけは合っている** — 被覆条件は
    標準形の話であって値の話ではない。 -/
#guard (wPool118.countP fun q => q.1.all digB106 && q.2.all tdigB118
  && bdescB106 (q.1.map (BT.D 1) ++ q.2) && !(covMB118 q.1 q.2)) == 4
#guard (wPool118.filter fun q => q.1.all digB106 && q.2.all tdigB118
  && bdescB106 (q.1.map (BT.D 1) ++ q.2) && !(covMB118 q.1 q.2)).all fun q =>
    !(BT.isStd (vebB118 q.1 q.2))
#guard (wPool118.countP fun q => q.1.all digB106 && q.2.all tdigB118
  && bdescB106 (q.1.map (BT.D 1) ++ q.2) && !(covMB118 q.1 q.2)
  && (dict (vebB118 q.1 q.2)
      == phi (plus TM.Term.one (aOf118 q.1)) (omegaNF (rhoOf118 q.2)))) == 3
/-! **降順も飾りではない。** -/
#guard (wPool118.countP fun q => !(bdescB106 (q.1.map (BT.D 1) ++ q.2))) == 69
#guard (wPool118.countP fun q => !(BT.isStd (vebB118 q.1 q.2))) == 73

/-! **名指しの被覆条件破り。**  尾の桁 `ψ₀(Ω₁²) = ζ₀` はそれ自体は合法である。 -/
def deepC118 : BT := vebB118 [] [BT.D 0 (BT.D 1 (BT.D 1 BT.zero))]
#guard tdigB118 (BT.D 0 (BT.D 1 (BT.D 1 BT.zero)))
#guard !(covMB118 [] [BT.D 0 (BT.D 1 (BT.D 1 BT.zero))])
#guard !(BT.isStd deepC118)

/-! **作った証人、名前つき。** -/
#guard dict (vebB118 [] [BT.D 0 BT.zero]) == phi TM.Term.one TM.Term.omega
#guard dict (vebB118 [BT.zero] [BT.D 0 (BT.D 1 BT.zero)])
  == phi (ofNat 2) (phi TM.Term.one zero)
#guard dict (vebN118 [BT.D 1 BT.zero, BT.zero])
  == phi TM.Term.one (phi (ofNat 2) zero)
#guard BT.isStd (vebN118 [BT.D 1 BT.zero, BT.zero])
  && btLe72 1 (vebN118 [BT.D 1 BT.zero, BT.zero])
  && (btLe72 0 (vebN118 [BT.D 1 BT.zero, BT.zero]) == false)
/-! §106 の塔は尾が空の場合。 -/
#guard (List.range 8).all fun n => vebB118 [gInv103 (n+1)] [] == vebB106 [gInv103 (n+1)]

/-! ### §103.8 の敵対的な母集団で測り直す

`dictInv` を証人の**神託**としてだけ使い、出てきた項を §118 の定理の仮説に
**全部**当てて確かめる — 形 (`vebG118 ys ms == b`) も含めて。値だけ合っている項を
数えているのではない。 -/

def isD1_118 (x : BT) : Bool := match x with | .D 1 _ => true | _ => false
def argD1_118 (x : BT) : BT := match x with | .D 1 y => y | _ => BT.zero
def legalB118 (b : BT) : Bool := btLe72 1 b && BT.isStd b && hd085B b

/-- 目標 `t` と証人 `b` に対して、`dict_vebG118` の仮説と結論を**全部**確かめる。 -/
def instOK118 (t : Term) (b : BT) : Bool :=
  match b with
  | BT.D 0 p =>
      let L := BT.toL p
      let ys := (L.takeWhile isD1_118).map argD1_118
      let ms := L.dropWhile isD1_118
      let pr := wcnf (reg 1) (toList (dict p))
      legalB118 b && (dict b == t) && (vebG118 ys ms == b)
        && ms.all tdigB118 && descL (L.map dict)
        && (L.map dict == pr.1.map (fun q => argV106 q.1 q.2) ++ toList pr.2)
        && !pr.1.isEmpty && pr.1.all okpB118 && descPB118 pr.1
        && inT pr.2 && lt pr.2 (reg 1) && inT (plus (valP118 pr.1) pr.2)
        && (omegaNF (plus (valP118 pr.1) pr.2) == t)
  | _ => false

def reach118 (t : Term) : Bool :=
  match dictInv t with | some b => instOK118 t b | none => false

def nPairs118 (t : Term) : Nat :=
  match dictInv t with
  | some (BT.D 0 p) => (wcnf (reg 1) (toList (dict p))).1.length
  | _ => 0
def bigCoef118 (t : Term) : Bool :=
  match dictInv t with
  | some (BT.D 0 p) => (wcnf (reg 1) (toList (dict p))).1.any fun ac => !(ac.2 == TM.Term.one)
  | _ => false
def tailRho118 (t : Term) : Bool :=
  match dictInv t with
  | some (BT.D 0 p) => !((wcnf (reg 1) (toList (dict p))).2 == zero)
  | _ => false
def badCoef118 (t : Term) : Bool :=
  match dictInv t with
  | some (BT.D 0 p) => !((wcnf (reg 1) (toList (dict p))).1.all fun ac => ac.2.isAP)
  | _ => false
def isAdd118 (t : Term) : Bool := match t with | add _ _ => true | _ => false
def isOmPow118 (t : Term) : Bool := match t with | phi a _ => a == zero | _ => false

def builtShape106_118 (t : Term) : Bool :=
  match t with | phi a zero => !(a == zero) | _ => false

#eval (aPool103.length, aPool103.countP builtShape106_118, aPool103.countP reach118)
#eval (aPool103.countP fun t => reach118 t && nPairs118 t ≥ 2,
       aPool103.countP fun t => reach118 t && bigCoef118 t,
       aPool103.countP fun t => reach118 t && tailRho118 t)
#eval (aPool103.countP isAdd118, aPool103.countP badCoef118,
       aPool103.countP fun t => !(reach118 t) && !(isAdd118 t) && !(badCoef118 t))

/-! **§106 は 14、§118 は 186。**  そして §103 が `dictInv` の取りこぼしとして名指した
    5 項は、§103 自身が手で作った証人が §118 の仮説を**全部**満たす — 合わせて 191。 -/
#guard aPool103.countP builtShape106_118 == 14
#guard aPool103.countP reach118 == 186
#guard aPool103.all fun t => !(builtShape106_118 t) || reach118 t
#guard witMiss103.all fun q => instOK118 q.1 q.2
#guard witMiss103.length == 5

/-! **`ω` 冪 — 尾 `ρ` が無ければ一つも届かない形。** -/
#eval (aPool103.countP isOmPow118, aPool103.countP fun t => isOmPow118 t && reach118 t)
#guard aPool103.countP isOmPow118 == 12
#guard (aPool103.countP fun t => isOmPow118 t && reach118 t) == 8
#guard aPool103.all fun t => !(isOmPow118 t && reach118 t) || tailRho118 t

/-! **残る 173 の内訳 — 和が 106、係数が加法主要でないものが 62、§103 の
    取りこぼしが 5。取り残しは無い。** -/
#guard aPool103.countP isAdd118 == 106
#guard aPool103.countP badCoef118 == 62
#guard (aPool103.countP fun t => !(reach118 t) && !(isAdd118 t) && !(badCoef118 t)) == 5
#guard aPool103.length - aPool103.countP reach118 == 173

/-! **これでも `DictOntoMidOpen103` は閉じていない。**  条項は 326 行目の証明書に
    そのまま残っている — §118 は条項を一本も足さず、一本も外していない。 -/
#guard aPool103.countP reach118 < aPool103.length

end

/-! ## §117 A VEBLEN TARGET, READ OFF THE OTHER FOLD — `VebRest114` SPLITS AT ONE
       DECIDABLE CONDITION, AND WHAT SURVIVES IS THE EQUAL-EXPONENT CASE

§114 split §109's hard half at the shape of `b`'s fold and closed the half where `b`
all-fires, by pointing §114.2's machinery at the target `ψ_{Ω₁}(j_b)`.  Its own closing
sentence names what that machinery could NOT reach:

> The other class is untouched: when `b`'s fold ends in a `φ̄`-term the comparison is
> `φ̄(α,γ) < φ̄(β,δ)`, and §114 adds nothing to it.

**§117 adds it.**  §114.1's target had to be strongly critical because `φ̄` is only known to be
harmless below a target closed under it; §113.1 had already shown that a `φ̄`-target works too
as soon as 2.3.13(i) applies, but it read that clause at the single point `Γ₀`.  §117 reads it
with the first argument FREE, and then the whole of §114.2 transposes: the fold stays below
`φ̄(A,R)` under a decidable condition on ONE side.  What is new on top of that is the other
direction — §117.3 proves the fold never goes DOWN, so any intermediate value of `b`'s own
fold is a legal target — and that is what lets the target be read off `b` when `b` has no
collapse index at all, which is exactly where §114's tool gives nothing.

WHAT IS PROVED.

  §117.1  **2.3.13(i) AT A FREE TARGET** (`lt_phi_vT117`).  `φ̄(a,b) < φ̄(A,R) ↔ b < φ̄(A,R)`
          whenever `a < A` — §113.1's `lt_phi_gT113` with `Γ₀` replaced by anything.
          `lt_phiNF_wk117` is §114.1's `lt_phiNF_ap114` with its `hphi` hypothesis cut down to
          the ONE exponent the proof actually applies it to (§114 asked for closure of the
          target under `φ̄` at every pair of arguments, which a Veblen target does NOT have),
          and `lt_phiNF_vT117` puts the two together.  **Everything else in §114.1 —
          `ltAP_of_hdLe114`, `ltAP_toList114`, `lt_ofList_ap114`, `lt_plus_ap114`,
          `lt_down_ap114` — was already stated at a general additively principal target and
          is reused unchanged.**

  §117.2  **THE FOLD STAYS BELOW A VEBLEN TARGET** (`accW89_ltV117`).  `VebIngV117 x A R n`
          is the transposed ingredient condition: every base-`Ω₁` pair from the `n`-th on is
          non-firing with exponent below `A` and coefficient below `φ̄(A,R)`, and the value the
          first `n` pairs leave is below `φ̄(A,R)`.  **The parameter `n` is the new part**:
          §114.2 had to start at the end of the firing prefix, §117.2 may start anywhere, so
          a common prefix of the two folds can be PEELED instead of bounded.  The split is
          `List.take_append_drop` and the non-firing of the tail is part of the decidable
          condition, so §109.1's prefix property is not used here at all.

  §117.3  **THE FOLD NEVER GOES DOWN** (`le_foldTake_accW89_117`).  `le_phiNF_ge117` : for
          `T` additively principal with `1 < T ≤ X`, `T ≤ φ̄-normalise(C,X)` — all five
          branches of `phiNF`, the step-down branch through §95's `le_hd_down95` and the
          `β = 0` branch killed by `T ≠ 0`.  With §81's `le_self_plus_ap81` that makes
          "the accumulator only grows" an invariant (`GeV117`), so the value after `k` steps
          of a fold is `≤` its final value whenever the remaining pairs are Veblen.
          §109.3's `accGt109` is the same statement for the ONE target `ψ_{Ω₁}(j)` and the
          LAST step; this is it for every intermediate value and the whole tail.

  §117.4  **THE SPLIT** (`hiMono_vebT117`, `hiMono_closed117`, `vebRest_of117`).  Put the two
          halves together at a target read off `b`: if `b`'s fold after `k` steps holds a term
          of the shape `φ̄(A,R)` and everything after step `k` is Veblen, then that term is
          below `ψ₀(hi b)` (§117.3) and `a`'s side needs only `VebIngV117` (§117.2).
          `closed117 a b` is the decidable disjunction of §114.3's `ψ_{Ω₁}(j_b)` route and
          this one; `VebRest117` is `VebRest114` restricted to `closed117 a b = false`, and
          `vebRest_of117` re-hangs `VebRest114`, `hiMono_of_four117` re-hangs `HiMono89` and
          `certIn_t326_117` re-hangs row 326.

  §117.5  **THE NEGATIVES, AND THE LEVEL HONESTY.**  `reachSep117` : `(ψ₁0, ψ₁ψ₁0)` is
          `K`-standard on both sides, `b` has **no collapse index at all**, so §114.3's tool
          says nothing — and §117.4 closes it.  `restSep117` : `(ψ₁0, ψ₁ψ₀ψ₁0)`, `K`-standard
          on both sides, conclusion TRUE, and `closed117 = false` — **the residual clause's
          hypothesis is not empty.**  What fails there is named: the two digit-exponent lists
          are EQUAL (`restExp117`), so no target of the shape `φ̄(A,·)` has `A` above `a`'s
          exponents.  `restTriv117` : letting `n` run to the FULL length of `a`'s pair list
          would close that pair — and would close it because at `n = |a|` the condition IS the
          conclusion.  **That is why `closed117` stops the range one short**, and §117.6
          measures the difference.  `knownSplit117` : §81's `cexA89` and §101's `bothBadA101`
          are both `closed117 = false`, i.e. the two known witnesses against this clause live
          in the part §117 does NOT close.

WHAT IS **NOT** CLAIMED.  **`VebRest114` is NOT proved and NOT refuted; §117 MOVES the
residue.**  `VebRest117` is `VebRest114` on the pairs `closed117` misses, unweakened and
unproved, and §117.6 exhibits 54 `K`-standard pairs where its hypothesis fires.  `VebIngF114`,
`IdxMono101`, `IdxLeMix109`, `PsiIdxOKStd172`, `DictOntoMidOpen103`, `DictDenseMid107`,
`DictDenseAbove107` are untouched.  Row 326 rests on `PsiIdxOKStd172`, `IdxMono101`,
`IdxLeMix109`, `VebIngF114`, **`VebRest117`**, `DictOntoMidOpen103`, `DictDenseMid107`,
`DictDenseAbove107` (`certIn_t326_117`).

**WHERE §117 STOPPED, PRECISELY.**  A target of the shape `φ̄(A,R)` separates two folds only
when `A` is STRICTLY above every exponent `a` still has to spend; 2.3.13 has a clause for
`A` equal to that exponent as well (`a = c ⟹ compare the second arguments`) and §117 does not
port it.  Every one of the 54 `K`-standard pairs §117 misses has `a`'s leading digit exponent
EQUAL to `b`'s — and the shape is not by itself the obstruction, since §117 closes 107 other
pairs that also have it.  Reading 2.3.13's first clause at the fold would need `phiNF` to be
monotone in its second argument, which the repository does not have; and past that first
difference what is left is `a`'s later COEFFICIENTS against `b`'s value, which is §104's
stopping point word for word.  So the residue has moved from "compare two Veblen folds" to
"compare two Veblen folds that agree on their leading exponent", and §117 has not removed it.

WHAT THE MEASUREMENT SAYS (§117.6 gives the construction).  §114.5's three seed lines plus a
fourth BUILT for this section: `ψ₁(ψ₀ z)` puts a large value in a digit's COEFFICIENT
(exponent `1`, coefficient `ω^(ψ₀ z)`, §104.2), and the coefficient is what a Veblen target
tests, while §114's population only ever produced small ones.  15 seeds, 135 terms with their
two-term sums, nothing filtered.

  * **The tool is sound where it could fail.**  4465 residual pairs of the shape `VebRest114`
    covers, **782 of them BREAK the conclusion**, and `closed117` fires on **0** of those 782
    while firing on 3523 pairs overall.  Not a vacuous sweep: the hypothesis is live on 79%
    of the pairs where the conclusion holds.
  * **The residual clause is not empty.**  Of 990 `K`-standard residual pairs `closed117`
    closes 936 and misses **54**; the smallest miss is `(ψ₁0, ψ₁ψ₀ψ₁0)` at 2 + 4 symbols.
  * **§117 reaches a class §114 could not.**  Of the 120 `K`-standard pairs where `b` has no
    collapse index, §114.3's `ψ_{Ω₁}` route closes **0** and §117.4's Veblen route closes 95.
    Where `b` does have an index the two routes together close 841 of 870.
  * **The restriction on `n` is what keeps the clause honest.**  Letting `n` reach the full
    length of `a`'s pair list closes all 990 — it adds exactly the 54 — and on the shape-only
    population that variant holds on 3523 of the 3683 pairs where the conclusion holds, i.e.
    it is the conclusion restated wherever `b`'s value is `φ̄`-shaped.
  * **The misses have one shape.**  All 54 have `a`'s leading digit exponent EQUAL to `b`'s;
    107 of the 936 §117 closes have it too, so the shape is necessary and not sufficient.
  * **The coefficient line had to be BUILT.**  Drop it and the population is §114.5's 65
    terms: 1540 residual pairs, **84 breaks** and 34 `K`-standard misses.  Adding the line
    multiplies the breaks by 9.3 — that is 9.3× the chances for the soundness check to fail,
    and it did not. -/


/-! ### §117.1 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- **2.3.13(i) を的自由で。** -/
theorem lt_phi_vT117 {a b A R : Term} (ha : lt a A = true) :
    lt (phi a b) (phi A R) = lt b (phi A R) := by
  have hne : a ≠ A := by
    intro hc; rw [hc, lt_irrefl] at ha; exact Bool.noConfusion ha
  have hne2 : phi a b ≠ phi A R := by
    intro hc; injection hc with h1 _; exact hne h1
  rw [lt_eq_ltF_succ, ltF_succ_phi_phi _ hne2, if_neg hne,
    if_pos (by
      rw [show ltF (2 * ((phi a b).deg + (phi A R).deg) + 7) a A = lt a A from
        (lt_eq_ltF a A _ (by
          show a.deg + A.deg ≤ 2 * ((1 + a.deg + b.deg) + (1 + A.deg + R.deg)) + 7
          omega)).symm]
      exact ha),
    show ltF (2 * ((phi a b).deg + (phi A R).deg) + 7) b (phi A R)
        = lt b (phi A R) from
      (lt_eq_ltF b (phi A R) _ (by
        show b.deg + (1 + A.deg + R.deg)
          ≤ 2 * ((1 + a.deg + b.deg) + (1 + A.deg + R.deg)) + 7
        omega)).symm]

theorem inT_phiT117 {A R : Term} (hiA : inT A = true) (hiR : inT R = true)
    (hAM : lt A M = true) (hRM : lt R M = true) : inT (phi A R) = true := by
  show (inT A && inT R && lt A M && lt R M) = true
  rw [hiA, hiR, hAM, hRM]; rfl

theorem phiT_ne_zero117 {A R : Term} : (phi A R) ≠ zero := by
  intro hc; exact Term.noConfusion hc

/-- **§114.1 の `lt_phiNF_ap114` を、指数一つぶんの弱い仮定で。** -/
theorem lt_phiNF_wk117 {A X S : Term} (hSap : S.isAP = true) (hSz : S ≠ zero)
    (hfS : FragR S = true) (hX : inT X = true) (h1 : lt TM.Term.one S = true)
    (hphi : ∀ q : Term, lt q S = true → lt (phi A q) S = true)
    (hA : lt A S = true) (hXS : lt X S = true) : lt (phiNF A X) S = true := by
  have hall := ltAP_toList114 hfS hSap X hX hXS
  have hdown := lt_down_ap114 hSap hSz hfS hX h1 hall
  have hdef : lt (phiNFdefault A X) S = true := by
    unfold phiNFdefault
    split
    · exact hA
    · exact hphi X hXS
  have hsucc : lt (phiNFsucc A X) S = true := by
    unfold phiNFsucc
    split
    rename_i heq
    rw [heq] at hdown
    split
    · split <;> (split <;> first | exact hphi _ hdown | exact hdef)
    · exact hdef
  unfold phiNF
  split
  · exact hXS
  · split
    · split
      · exact hXS
      · exact hsucc
    · exact hsucc

/-- **`φ̄` の正規化は Veblen の的の下で閉じる** — 指数が `A` より下なら。 -/
theorem lt_phiNF_vT117 {a X A R : Term} (hiA : inT A = true) (hiR : inT R = true)
    (hAM : lt A M = true) (hRM : lt R M = true) (hia : inT a = true) (haM : lt a M = true)
    (hX : inT X = true) (h1 : lt TM.Term.one (phi A R) = true)
    (ha : lt a A = true) (hXS : lt X (phi A R) = true) :
    lt (phiNF a X) (phi A R) = true := by
  have hiT : inT (phi A R) = true := inT_phiT117 hiA hiR hAM hRM
  refine lt_phiNF_wk117 (show (phi A R).isAP = true from rfl) phiT_ne_zero117
    (inT_le_fragR _ hiT) hX h1 (fun q hq => by rw [lt_phi_vT117 ha]; exact hq) ?_ hXS
  exact lt_phi_of_le100 a.deg a A R (Nat.le_refl _) hia haM hiT (Or.inl (le_of_lt94 ha))

end


/-! ### §117.2 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- **Veblen の一歩は Veblen の的を越えない** — 指数が `A` より下なら。 -/
theorem ltS117_step {A R : Term} (hiA : inT A = true) (hiR : inT R = true)
    (hAM : lt A M = true) (hRM : lt R M = true) (h1 : lt TM.Term.one (phi A R) = true)
    {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (hL : LtS114 (phi A R) s) (hi1 : inT ac.1 = true)
    (h1M : lt ac.1 M = true) (h2 : inT ac.2 = true) (hf : le (reg 1) ac.1 = false)
    (hA : lt ac.1 A = true) (hC : lt ac.2 (phi A R) = true) :
    LtS114 (phi A R) (stepF (reg 1) (baseOf 0) s ac) := by
  intro v hv
  rw [stepF_snd_veb88 hf] at hv
  rw [← Option.some.inj hv]
  have hiT : inT (phi A R) = true := inT_phiT117 hiA hiR hAM hRM
  have hfS : FragR (phi A R) = true := inT_le_fragR _ hiT
  have hSz : (phi A R) ≠ zero := phiT_ne_zero117
  have hCs : lt (sub1 ac.2) (phi A R) = true :=
    lt_of_le_of_lt3 (inT_le_fragR _ (inT_sub1 h2)) (inT_le_fragR _ h2) hfS
      (le_sub1_self75 h2) hC
  cases hs2 : s.2 with
  | none =>
      refine lt_phiNF_vT117 hiA hiR hAM hRM hi1 h1M
        (inT_plus (inT_baseOf 0) (inT_sub1 h2)) h1 hA ?_
      refine lt_plus_ap114 rfl hSz hfS (inT_baseOf 0) (inT_sub1 h2) ?_ hCs
      exact show lt zero (phi A R) = true from lt_zero_left hSz
  | some v0 =>
      have hiv : inT v0 = true := (hst.2 v0 hs2).1
      exact lt_phiNF_vT117 hiA hiR hAM hRM hi1 h1M (inT_plus hiv h2) h1 hA
        (lt_plus_ap114 rfl hSz hfS hiv h2 (hL v0 hs2) hC)

/-- **Veblen だけの尾を通しても Veblen の的の下に留まる。** -/
theorem ltS117_fold {A R : Term} (hiA : inT A = true) (hiR : inT R = true)
    (hAM : lt A M = true) (hRM : lt R M = true) (h1 : lt TM.Term.one (phi A R) = true) :
    ∀ (l : List (Term × Term)) (s : Option Term × Option Term), StInv s →
      LtS114 (phi A R) s →
      (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
      (∀ ac ∈ l, le (reg 1) ac.1 = false ∧ lt ac.1 A = true
        ∧ lt ac.2 (phi A R) = true) →
      LtS114 (phi A R) (l.foldl (stepF (reg 1) (baseOf 0)) s) := by
  intro l
  induction l with
  | nil => intro s _ hL _ _; exact hL
  | cons ac t ih =>
      intro s hst hL hall hveb
      have hac := hall ac (List.Mem.head _)
      have hv := hveb ac (List.Mem.head _)
      have hs1 : StInv (stepF (reg 1) (baseOf 0) s ac) :=
        stepF_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0) hst hac
          (fun hcc => absurd hcc (by rw [hv.1]; exact Bool.noConfusion))
      exact ih _ hs1
        (ltS117_step hiA hiR hAM hRM h1 hst hL hac.1 hac.2.1 hac.2.2.1 hv.1 hv.2.1 hv.2.2)
        (fun a ha => hall a (List.Mem.tail _ ha)) (fun a ha => hveb a (List.Mem.tail _ ha))

/-- **成分の条件、Veblen の的で。**  `n` 段だけ畳んでから始めてよい: 途中の値が的の下に
    あり、残りの対の指数が `A` より下、係数が的の下なら足りる。**見ているのは `x` の側
    だけ**である。 -/
def VebIngV117 (x A R : Term) (n : Nat) : Bool :=
  lt TM.Term.one (phi A R)
    && (((wcnf (reg 1) (toList x)).1.drop n).all
        (fun ac => !le (reg 1) ac.1 && lt ac.1 A && lt ac.2 (phi A R)))
    && (match (((wcnf (reg 1) (toList x)).1.take n).foldl (stepF (reg 1) (baseOf 0))
          ((none : Option Term), (none : Option Term))).2 with
        | none => true
        | some v => lt v (phi A R))

/-- **§117.2 の主定理 — 成分が Veblen の的の下なら値も下。** -/
theorem accW89_ltV117 {x A R : Term} (hx : inT x = true) (hlx : lt x M = true)
    (Hp : PsiIdxOK 0 x) (hiA : inT A = true) (hAM : lt A M = true)
    (hiR : inT R = true) (hRM : lt R M = true)
    (n : Nat) (h : VebIngV117 x A R n = true) :
    lt (accW89 x) (phi A R) = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList x) hc hd
    (ltM_toList x hx hlx)
  obtain ⟨h12, h3⟩ := (Bool.and_eq_true _ _).mp h
  obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h12
  have hsplit : (wcnf (reg 1) (toList x)).1.take n ++ (wcnf (reg 1) (toList x)).1.drop n
      = (wcnf (reg 1) (toList x)).1 := List.take_append_drop n _
  have hmemT : ∀ ac ∈ (wcnf (reg 1) (toList x)).1.take n,
      ac ∈ (wcnf (reg 1) (toList x)).1 := by
    intro ac hac; rw [← hsplit]; exact List.mem_append_left _ hac
  have hmemD : ∀ ac ∈ (wcnf (reg 1) (toList x)).1.drop n,
      ac ∈ (wcnf (reg 1) (toList x)).1 := by
    intro ac hac; rw [← hsplit]; exact List.mem_append_right _ hac
  have hstT : StInv (((wcnf (reg 1) (toList x)).1.take n).foldl (stepF (reg 1) (baseOf 0))
      ((none : Option Term), (none : Option Term))) :=
    fold_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0)
      _ (none, none) stInv_none (fun z hz => hallOK z (hmemT z hz))
      (by
        intro p hp
        refine Hp p ?_
        rw [← hsplit, scanSt_append109]
        exact List.mem_append_left _ hp)
  have hLT : LtS114 (phi A R) (((wcnf (reg 1) (toList x)).1.take n).foldl
      (stepF (reg 1) (baseOf 0)) ((none : Option Term), (none : Option Term))) := by
    intro v hv
    rw [hv] at h3
    exact h3
  have hveb : ∀ ac ∈ (wcnf (reg 1) (toList x)).1.drop n,
      le (reg 1) ac.1 = false ∧ lt ac.1 A = true ∧ lt ac.2 (phi A R) = true := by
    intro ac hac
    have hb := List.all_eq_true.mp h2 ac hac
    obtain ⟨hb12, hb3⟩ := (Bool.and_eq_true _ _).mp hb
    obtain ⟨hb1, hb2⟩ := (Bool.and_eq_true _ _).mp hb12
    exact ⟨by cases hq : le (reg 1) ac.1 with
             | false => rfl
             | true => rw [hq] at hb1; exact Bool.noConfusion hb1, hb2, hb3⟩
  have hmain := ltS117_fold hiA hiR hAM hRM h1 _ _ hstT hLT
    (fun z hz => hallOK z (hmemD z hz)) hveb
  have hfoldE : ((wcnf (reg 1) (toList x)).1.take n
        ++ (wcnf (reg 1) (toList x)).1.drop n).foldl (stepF (reg 1) (baseOf 0))
        ((none : Option Term), (none : Option Term))
      = ((wcnf (reg 1) (toList x)).1.drop n).foldl (stepF (reg 1) (baseOf 0))
          (((wcnf (reg 1) (toList x)).1.take n).foldl (stepF (reg 1) (baseOf 0))
            ((none : Option Term), (none : Option Term))) := List.foldl_append
  rw [hsplit] at hfoldE
  show lt (((wcnf (reg 1) (toList x)).1.foldl
    (init := ((none : Option Term), (none : Option Term)))
    (stepF (reg 1) (baseOf 0))).2.getD zero) (phi A R) = true
  rw [hfoldE]
  cases hv : (((wcnf (reg 1) (toList x)).1.drop n).foldl (stepF (reg 1) (baseOf 0))
      (((wcnf (reg 1) (toList x)).1.take n).foldl (stepF (reg 1) (baseOf 0))
        ((none : Option Term), (none : Option Term)))).2 with
  | none => exact lt_zero_left phiT_ne_zero117
  | some v => exact hmain v hv

end


/-! ### §117.3 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 加法主要な項との比較は頭で決まる。 -/
theorem lt_hd_ap117 {T X x : Term} {s : List Term} (hapT : T.isAP = true)
    (hl : toList X = x :: s) : lt X T = lt x T := by
  cases X with
  | zero => cases hl
  | add a b =>
      have hx : x = a := by
        have : (a :: toList b) = x :: s := hl
        exact (List.cons.inj this).1.symm
      rw [hx]; exact lt_add_ap102 a b hapT
  | M => rw [show x = M from ((List.cons.inj hl).1).symm]
  | omg c => rw [show x = omg c from ((List.cons.inj hl).1).symm]
  | phi c d => rw [show x = phi c d from ((List.cons.inj hl).1).symm]
  | psi c d => rw [show x = psi c d from ((List.cons.inj hl).1).symm]
  | Z c => rw [show x = Z c from ((List.cons.inj hl).1).symm]

/-- 加法主要な項が和以下なら、その頭以下でもある。 -/
theorem le_hd_of_le_ap117 {T X x : Term} {s : List Term} (hiT : inT T = true)
    (hapT : T.isAP = true) (hiX : inT X = true) (hl : toList X = x :: s)
    (hle : le T X = true) : le T x = true := by
  have hix : inT x = true := inTL_inT hiX x (by rw [hl]; exact List.Mem.head _)
  cases hb : le T x with
  | true => rfl
  | false =>
      exfalso
      have hxT : lt x T = true := lt_of_not_le_inT hiT hix hb
      have hXT : lt X T = true := by rw [lt_hd_ap117 hapT hl]; exact hxT
      rcases (Bool.or_eq_true _ _).mp hle with he | hlt
      · rw [eq_of_beq he, lt_irrefl] at hXT; exact Bool.noConfusion hXT
      · rw [lt_asymm_inT hiT hiX hlt] at hXT; exact Bool.noConfusion hXT

/-- **`φ̄` の正規化は第二引数を下げない。**  `T` が加法主要で `1 < T ≤ X` なら
    `T ≤ φ̄(C,X)` — `phiNF` が返す五つの枝すべてで。 -/
theorem le_phiNF_ge117 {T C X : Term} (hiT : inT T = true) (hapT : T.isAP = true)
    (h1T : lt TM.Term.one T = true) (hTM : lt T M = true)
    (hiC : inT C = true) (hCM : lt C M = true)
    (hiX : inT X = true) (hXM : lt X M = true)
    (hle : le T X = true) : le T (phiNF C X) = true := by
  have hTz : T ≠ zero := by
    intro hc; rw [hc, lt_zero_right] at h1T; exact Bool.noConfusion h1T
  have hXz : X ≠ zero := by
    intro hc
    rw [hc] at hle
    rcases (Bool.or_eq_true _ _).mp hle with he | hlt
    · exact hTz (eq_of_beq he)
    · rw [lt_zero_right] at hlt; exact Bool.noConfusion hlt
  have hstep : ∀ Y : Term, inT Y = true → lt Y M = true → le T Y = true →
      le T (phi C Y) = true := by
    intro Y hiY hYM hTY
    exact le_of_lt94 (lt_phi_of_le100 T.deg T C Y (Nat.le_refl _) hiT hTM
      (inT_phiT117 hiC hiY hCM hYM) (Or.inr hTY))
  have hphiX : le T (phi C X) = true := hstep X hiX hXM hle
  have hdef : le T (phiNFdefault C X) = true := by
    unfold phiNFdefault
    split
    · rename_i hh
      exact absurd (eq_of_beq ((Bool.and_eq_true _ _).mp hh).1) hXz
    · exact hphiX
  cases hl : toList X with
  | nil => exact absurd (toList_eq_nil X hl) hXz
  | cons x t =>
      have hix : inT x = true := inTL_inT hiX x (by rw [hl]; exact List.Mem.head _)
      have hTx : le T x = true := le_hd_of_le_ap117 hiT hapT hiX hl hle
      have h1x : lt TM.Term.one x = true :=
        lt_of_lt_of_le3 (show FragR TM.Term.one = true from rfl) (inT_le_fragR T hiT)
          (inT_le_fragR x hix) h1T hTx
      have hidown : inT (plus (splitFin X).1 (ofNat ((splitFin X).2 - 1))) = true :=
        inT_plus (inT_splitFin hiX) (inT_ofNat _)
      have hdownM : lt (plus (splitFin X).1 (ofNat ((splitFin X).2 - 1))) M = true :=
        lt_plus_M (inT_splitFin hiX) (inT_ofNat _) (ltM_splitFin hiX hXM) (ltM_ofNat _)
      have hdown : le T (plus (splitFin X).1 (ofNat ((splitFin X).2 - 1))) = true :=
        le_trans3 (inT_le_fragR T hiT) (inT_le_fragR x hix) (inT_le_fragR _ hidown)
          hTx (le_hd_down95 hiX hl h1x)
      have hsucc : le T (phiNFsucc C X) = true := by
        unfold phiNFsucc
        split
        rename_i heq
        rw [heq] at hdown hidown hdownM
        split
        · split <;> (split <;> first | exact hstep _ hidown hdownM hdown | exact hdef)
        · exact hdef
      unfold phiNF
      split
      · exact hle
      · split
        · split
          · exact hle
          · exact hsucc
        · exact hsucc

end


section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 累算器は加法主要 — 発火の枝でも Veblen の枝でも。 -/
def ApV117 (s : Option Term × Option Term) : Prop := ∀ v, s.2 = some v → v.isAP = true

theorem apV117_none : ApV117 ((none : Option Term), (none : Option Term)) := by
  intro v h; cases h

theorem apV117_step (s : Option Term × Option Term) (ac : Term × Term) :
    ApV117 (stepF (reg 1) (baseOf 0) s ac) := by
  intro v hv
  cases hf : le (reg 1) ac.1 with
  | true =>
      rw [stepF_snd_fire88 hf] at hv
      rw [← Option.some.inj hv]; rfl
  | false =>
      rw [stepF_snd_veb88 hf] at hv
      rw [← Option.some.inj hv]; exact isAP_phiNF _ _

theorem apV117_fold : ∀ (l : List (Term × Term)) (s : Option Term × Option Term),
    ApV117 s → ApV117 (l.foldl (stepF (reg 1) (baseOf 0)) s) := by
  intro l
  induction l with
  | nil => intro s h; exact h
  | cons ac t ih => intro s _; exact ih _ (apV117_step s ac)

/-- 「的は今の値以下」という不変量。 -/
def GeV117 (T : Term) (s : Option Term × Option Term) : Prop :=
  ∃ v, s.2 = some v ∧ le T v = true

/-- **Veblen の一歩は値を下げない。** -/
theorem geV117_step {T : Term} (hiT : inT T = true) (hapT : T.isAP = true)
    (h1T : lt TM.Term.one T = true) (hTM : lt T M = true)
    {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (hap : ApV117 s) (hge : GeV117 T s)
    (hi1 : inT ac.1 = true) (h1M : lt ac.1 M = true) (hi2 : inT ac.2 = true)
    (h2M : lt ac.2 M = true) (hf : le (reg 1) ac.1 = false) :
    GeV117 T (stepF (reg 1) (baseOf 0) s ac) := by
  obtain ⟨v, hv2, hTv⟩ := hge
  have hval : (stepF (reg 1) (baseOf 0) s ac).2 = some (phiNF ac.1 (plus v ac.2)) := by
    rw [stepF_snd_veb88 hf, hv2]
  refine ⟨_, hval, ?_⟩
  have hiv : inT v = true := (hst.2 v hv2).1
  have hvM : lt v M = true := (hst.2 v hv2).2
  have hapv : v.isAP = true := hap v hv2
  have hTplus : le T (plus v ac.2) = true :=
    le_trans3 (inT_le_fragR _ hiT) (inT_le_fragR _ hiv) (inT_le_fragR _ (inT_plus hiv hi2))
      hTv (le_self_plus_ap81 hiv hapv hi2)
  exact le_phiNF_ge117 hiT hapT h1T hTM hi1 h1M (inT_plus hiv hi2)
    (lt_plus_M hiv hi2 hvM h2M) hTplus

/-- **Veblen だけの尾を通しても値は下がらない。** -/
theorem geV117_fold {T : Term} (hiT : inT T = true) (hapT : T.isAP = true)
    (h1T : lt TM.Term.one T = true) (hTM : lt T M = true) :
    ∀ (l : List (Term × Term)) (s : Option Term × Option Term), StInv s → ApV117 s →
      GeV117 T s →
      (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
      (∀ ac ∈ l, le (reg 1) ac.1 = false) →
      GeV117 T (l.foldl (stepF (reg 1) (baseOf 0)) s) := by
  intro l
  induction l with
  | nil => intro s _ _ hge _ _; exact hge
  | cons ac t ih =>
      intro s hst hap hge hall hveb
      have hac := hall ac (List.Mem.head _)
      have hf := hveb ac (List.Mem.head _)
      have hs1 : StInv (stepF (reg 1) (baseOf 0) s ac) :=
        stepF_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0) hst hac
          (fun hcc => absurd hcc (by rw [hf]; exact Bool.noConfusion))
      exact ih _ hs1 (apV117_step s ac)
        (geV117_step hiT hapT h1T hTM hst hap hge hac.1 hac.2.1 hac.2.2.1 hac.2.2.2 hf)
        (fun a ha => hall a (List.Mem.tail _ ha)) (fun a ha => hveb a (List.Mem.tail _ ha))

/-- **§117.3 の主定理 — 途中の値は最後の値以下。**  `x` の側だけを見ている。 -/
theorem le_foldTake_accW89_117 {y T : Term} (hy : inT y = true) (hly : lt y M = true)
    (Hp : PsiIdxOK 0 y) (hiT : inT T = true) (hapT : T.isAP = true)
    (h1T : lt TM.Term.one T = true) (hTM : lt T M = true) (k : Nat)
    (hveb : ∀ ac ∈ (wcnf (reg 1) (toList y)).1.drop k, le (reg 1) ac.1 = false)
    (htk : (((wcnf (reg 1) (toList y)).1.take k).foldl (stepF (reg 1) (baseOf 0))
        ((none : Option Term), (none : Option Term))).2 = some T) :
    le T (accW89 y) = true := by
  obtain ⟨hc, hd⟩ := inT_toList y hy
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList y) hc hd
    (ltM_toList y hy hly)
  have hsplit : (wcnf (reg 1) (toList y)).1.take k ++ (wcnf (reg 1) (toList y)).1.drop k
      = (wcnf (reg 1) (toList y)).1 := List.take_append_drop k _
  have hmemT : ∀ ac ∈ (wcnf (reg 1) (toList y)).1.take k,
      ac ∈ (wcnf (reg 1) (toList y)).1 := by
    intro ac hac; rw [← hsplit]; exact List.mem_append_left _ hac
  have hmemD : ∀ ac ∈ (wcnf (reg 1) (toList y)).1.drop k,
      ac ∈ (wcnf (reg 1) (toList y)).1 := by
    intro ac hac; rw [← hsplit]; exact List.mem_append_right _ hac
  have hstT : StInv (((wcnf (reg 1) (toList y)).1.take k).foldl (stepF (reg 1) (baseOf 0))
      ((none : Option Term), (none : Option Term))) :=
    fold_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0)
      _ (none, none) stInv_none (fun z hz => hallOK z (hmemT z hz))
      (by
        intro p hp
        refine Hp p ?_
        rw [← hsplit, scanSt_append109]
        exact List.mem_append_left _ hp)
  have hmain := geV117_fold hiT hapT h1T hTM _ _ hstT
    (apV117_fold _ _ apV117_none) ⟨T, htk, Evidence.WF.le_self T⟩
    (fun z hz => hallOK z (hmemD z hz)) hveb
  have hfoldE : ((wcnf (reg 1) (toList y)).1.take k
        ++ (wcnf (reg 1) (toList y)).1.drop k).foldl (stepF (reg 1) (baseOf 0))
        ((none : Option Term), (none : Option Term))
      = ((wcnf (reg 1) (toList y)).1.drop k).foldl (stepF (reg 1) (baseOf 0))
          (((wcnf (reg 1) (toList y)).1.take k).foldl (stepF (reg 1) (baseOf 0))
            ((none : Option Term), (none : Option Term))) := List.foldl_append
  rw [hsplit] at hfoldE
  obtain ⟨v, hv2, hTv⟩ := hmain
  show le T (((wcnf (reg 1) (toList y)).1.foldl
    (init := ((none : Option Term), (none : Option Term)))
    (stepF (reg 1) (baseOf 0))).2.getD zero) = true
  rw [hfoldE, hv2]
  exact hTv

end


/-! ### §117.4 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 前から `k` 段だけ畳んだ値。 -/
def foldVal117 (y : Term) (k : Nat) : Option Term :=
  (((wcnf (reg 1) (toList y)).1.take k).foldl (stepF (reg 1) (baseOf 0))
    ((none : Option Term), (none : Option Term))).2

theorem foldVal_inT117 {y T : Term} (hy : inT y = true) (hly : lt y M = true)
    (Hp : PsiIdxOK 0 y) (k : Nat) (htk : foldVal117 y k = some T) :
    inT T = true ∧ lt T M = true := by
  obtain ⟨hc, hd⟩ := inT_toList y hy
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList y) hc hd
    (ltM_toList y hy hly)
  have hsplit : (wcnf (reg 1) (toList y)).1.take k ++ (wcnf (reg 1) (toList y)).1.drop k
      = (wcnf (reg 1) (toList y)).1 := List.take_append_drop k _
  have hmemT : ∀ ac ∈ (wcnf (reg 1) (toList y)).1.take k,
      ac ∈ (wcnf (reg 1) (toList y)).1 := by
    intro ac hac; rw [← hsplit]; exact List.mem_append_left _ hac
  have hstT : StInv (((wcnf (reg 1) (toList y)).1.take k).foldl (stepF (reg 1) (baseOf 0))
      ((none : Option Term), (none : Option Term))) :=
    fold_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0)
      _ (none, none) stInv_none (fun z hz => hallOK z (hmemT z hz))
      (by
        intro p hp
        refine Hp p ?_
        rw [← hsplit, scanSt_append109]
        exact List.mem_append_left _ hp)
  exact hstT.2 T htk

/-- **§117.4 の道具 — Veblen の的ひとつで一組を閉じる。**  `b` の折り畳みの途中の値が
    `φ̄(A,R)` の形をしていて、そこから先が全部 Veblen なら、その値は `b` の値以下
    (§117.3)。`a` の側は §117.2 の成分の条件だけを見る。**二つの折り畳みを比べていない。** -/
theorem hiMono_vebT117 (Hp : PsiIdxOKStd172) {a b : BT} {A R : Term} (n k : Nat)
    (hbA : btLe72 1 (BT.D 0 a) = true) (hbB : btLe72 1 (BT.D 0 b) = true)
    (hsA : BT.isStd (BT.D 0 a) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (hWa : le (reg 1) (dict a) = true) (hWb : le (reg 1) (dict b) = true)
    (hveb : ∀ ac ∈ (wcnf (reg 1) (toList (dict b))).1.drop k, le (reg 1) ac.1 = false)
    (htgt : foldVal117 (dict b) k = some (phi A R))
    (h : VebIngV117 (dict a) A R n = true) :
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true := by
  have hba := (btLe72_D 1 0 a hbA).2
  have hbb := (btLe72_D 1 0 b hbB).2
  have hia := inT_dict_of_std172 Hp a hba (isStd_of_D hsA)
  have hib := inT_dict_of_std172 Hp b hbb (isStd_of_D hsB)
  have hpa : PsiIdxOK 0 (dict a) := Hp 0 a (by omega) hba hsA
  have hpb : PsiIdxOK 0 (dict b) := Hp 0 b (by omega) hbb hsB
  obtain ⟨hiT, hTM⟩ := foldVal_inT117 hib.1 hib.2 hpb k htgt
  obtain ⟨hiA, hiR, hAM, hRM⟩ := inT_phi4 hiT
  have h1T : lt TM.Term.one (phi A R) = true :=
    ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).1).1
  have hle : le (phi A R) (accW89 (dict b)) = true :=
    le_foldTake_accW89_117 hib.1 hib.2 hpb hiT rfl h1T hTM k hveb htgt
  have hlt : lt (accW89 (dict a)) (phi A R) = true :=
    accW89_ltV117 hia.1 hia.2 hpa hiA hAM hiR hRM n h
  have hacca : inT (accW89 (dict a)) = true :=
    (accW89_facts (dict a) hia.1 hia.2 hpa hWa).1
  have haccb : inT (accW89 (dict b)) = true :=
    (accW89_facts (dict b) hib.1 hib.2 hpb hWb).1
  rw [collapse0_hi89 (dict a) hia.1 hia.2 hpa hWa,
    collapse0_hi89 (dict b) hib.1 hib.2 hpb hWb]
  exact lt_of_lt_of_le3 (inT_le_fragR _ hacca) (inT_le_fragR _ hiT)
    (inT_le_fragR _ haccb) hlt hle

/-- `b` の `k` 段目の値を的にして閉じられるか — 判定できる。 -/
def tgtOK117 (a b : BT) (k : Nat) : Bool :=
  ((wcnf (reg 1) (toList (dict b))).1.drop k).all (fun ac => !le (reg 1) ac.1)
    && (match foldVal117 (dict b) k with
        | some (TM.Term.phi A R) =>
            (List.range ((wcnf (reg 1) (toList (dict a))).1.length)).any
              (fun n => VebIngV117 (dict a) A R n)
        | _ => false)

/-- **§117 の道具が届く組。**  §114.3 の `ψ_{Ω₁}` の的か、§117.4 の Veblen の的か。
    `a` を全部畳んでしまう `n` は入れていない (`List.range` は長さちょうどまで) ので、
    **結論そのものを条項に紛れ込ませていない**。 -/
def closed117 (a b : BT) : Bool :=
  (match idxF88 0 (dict b) with
   | none => false
   | some jb => VebIng114 (dict a) (psi (reg 1) jb))
  || (List.range ((wcnf (reg 1) (toList (dict b))).1.length + 1)).any (tgtOK117 a b)

theorem hiMono_closed117 (Hp : PsiIdxOKStd172) {a b : BT}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hbB : btLe72 1 (BT.D 0 b) = true)
    (hsA : BT.isStd (BT.D 0 a) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (hWa : le (reg 1) (dict a) = true) (hWb : le (reg 1) (dict b) = true)
    (h : closed117 a b = true) :
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true := by
  rcases (Bool.or_eq_true _ _).mp h with h1 | h2
  · cases hjb : idxF88 0 (dict b) with
    | none => rw [hjb] at h1; exact Bool.noConfusion h1
    | some jb =>
        rw [hjb] at h1
        exact hiMono_bIdx114 Hp hbA hbB hsA hsB hWa hWb hjb h1
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.mp h2
    obtain ⟨hk1, hk2⟩ := (Bool.and_eq_true _ _).mp hk
    have hveb : ∀ ac ∈ (wcnf (reg 1) (toList (dict b))).1.drop k, le (reg 1) ac.1 = false := by
      intro ac hac
      have := List.all_eq_true.mp hk1 ac hac
      cases hq : le (reg 1) ac.1 with
      | false => rfl
      | true => rw [hq] at this; exact Bool.noConfusion this
    cases hfv : foldVal117 (dict b) k with
    | none => rw [hfv] at hk2; exact Bool.noConfusion hk2
    | some T =>
        cases T with
        | phi A R =>
            rw [hfv] at hk2
            obtain ⟨n, _, hn⟩ := List.any_eq_true.mp hk2
            exact hiMono_vebT117 Hp n k hbA hbB hsA hsB hWa hWb hveb hfv hn
        | zero => rw [hfv] at hk2; exact Bool.noConfusion hk2
        | M => rw [hfv] at hk2; exact Bool.noConfusion hk2
        | add _ _ => rw [hfv] at hk2; exact Bool.noConfusion hk2
        | omg _ => rw [hfv] at hk2; exact Bool.noConfusion hk2
        | psi _ _ => rw [hfv] at hk2; exact Bool.noConfusion hk2
        | Z _ => rw [hfv] at hk2; exact Bool.noConfusion hk2

/-- **`VebRest114` の残り — §117 の道具が届かない組だけ。** -/
def VebRest117 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lastFire92 (dict a) = false → lastFire92 (dict b) = false →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    closed117 a b = false →
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true

/-- **§117.4 の主定理 — `VebRest114` を架け替える。** -/
theorem vebRest_of117 (Hp : PsiIdxOKStd172) (H : VebRest117) : VebRest114 := by
  intro a b hbA hbB hsA hsB hWa hWb hfa hfb hlt
  cases hcl : closed117 a b with
  | true => exact hiMono_closed117 Hp hbA hbB hsA hsB hWa hWb hcl
  | false => exact H a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hcl

/-- **`HiMono89` を四つの条項に架け替える。** -/
theorem hiMono_of_four117 (Hp : PsiIdxOKStd172) (HA : IdxMono101) (HB : IdxLeMix109)
    (H1 : VebIngF114) (H2 : VebRest117) : HiMono89 :=
  hiMono_of_four114 Hp HA HB H1 (vebRest_of117 Hp H2)

/-- **326 行目を架け替える。** -/
theorem certIn_t326_117 (Hp : PsiIdxOKStd172) (HA : IdxMono101) (HB : IdxLeMix109)
    (H1 : VebIngF114) (H2 : VebRest117) (HD1 : DictOntoMidOpen103) (HD3 : DictDenseMid107)
    (HD4 : DictDenseAbove107) (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_114 Hp HA HB H1 (vebRest_of117 Hp H2) HD1 HD3 HD4 hacc

end

/-! ### §117.5 否定と段の正直さ -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- **§114 の道具が届かない組の証人 (a)** — `ψ₁0`、2 記号。 -/
def reachA117 : BT := w1_101
/-- **その相棒 (b)** — `ψ₁ψ₁0`、3 記号。**指数を持たない**ので §114.3 の
    `ψ_{Ω₁}(j_b)` の的は存在しない。 -/
def reachB117 : BT := w2_101

/-- **§117 は §114 が届かない場所に届く。**  `b` は指数を持たないので §114.3 の道具は
    何も言わないが、`b` の折り畳みの途中の値が `φ̄` の形をしているので §117.4 が閉じる。 -/
theorem reachSep117 :
    (btLe72 1 (BT.D 0 reachA117), BT.isStd (BT.D 0 reachA117),
     le (reg 1) (dict reachA117), lastFire92 (dict reachA117),
     btLe72 1 (BT.D 0 reachB117), BT.isStd (BT.D 0 reachB117),
     le (reg 1) (dict reachB117), lastFire92 (dict reachB117),
     (idxF88 0 (dict reachB117)).isSome,
     lt (hiW89 (dict reachA117)) (hiW89 (dict reachB117)),
     lt (collapse 0 (hiW89 (dict reachA117))) (collapse 0 (hiW89 (dict reachB117))),
     closed117 reachA117 reachB117, BT.size reachA117, BT.size reachB117)
    = (true, true, true, false, true, true, true, false, false, true, true, true, 2, 3) := rfl

/-- **残る条項の証人 (a)** — `ψ₁0`、2 記号。 -/
def restA117 : BT := w1_101
/-- **その相棒 (b)** — `ψ₁ψ₀ψ₁0`、4 記号。 -/
def restB117 : BT := BT.D 1 (BT.D 0 w1_101)

/-- **`VebRest117` の仮定は空でない。**  両辺とも `K` 標準、どちらの折り畳みも最後の対が
    発火せず、`hi` は狭義に増え、**結論は成り立つ**。それでも `closed117` は偽である。 -/
theorem restSep117 :
    (btLe72 1 (BT.D 0 restA117), BT.isStd (BT.D 0 restA117),
     le (reg 1) (dict restA117), lastFire92 (dict restA117),
     btLe72 1 (BT.D 0 restB117), BT.isStd (BT.D 0 restB117),
     le (reg 1) (dict restB117), lastFire92 (dict restB117),
     lt (hiW89 (dict restA117)) (hiW89 (dict restB117)),
     lt (collapse 0 (hiW89 (dict restA117))) (collapse 0 (hiW89 (dict restB117))),
     closed117 restA117 restB117, BT.size restA117, BT.size restB117)
    = (true, true, true, false, true, true, true, false, true, true, false, 2, 4) := rfl

/-- **何が足りないかは名前がついている — 指数が等しい。**  両辺の底 `Ω₁` の分解の
    指数の列が**同じ**なので、`a` の指数の上にある `φ̄(A,·)` の的は存在しない。 -/
theorem restExp117 :
    ((wcnf (reg 1) (toList (dict restA117))).1.map (fun ac => ac.1)
       == (wcnf (reg 1) (toList (dict restB117))).1.map (fun ac => ac.1),
     (wcnf (reg 1) (toList (dict restA117))).1.length,
     (wcnf (reg 1) (toList (dict restB117))).1.length) = (true, 1, 1) := rfl

/-- `n` を `a` の対の個数**ちょうど**まで許した形。 -/
def tgtOKtriv117 (a b : BT) (k : Nat) : Bool :=
  ((wcnf (reg 1) (toList (dict b))).1.drop k).all (fun ac => !le (reg 1) ac.1)
    && (match foldVal117 (dict b) k with
        | some (TM.Term.phi A R) =>
            (List.range ((wcnf (reg 1) (toList (dict a))).1.length + 1)).any
              (fun n => VebIngV117 (dict a) A R n)
        | _ => false)

def closedTriv117 (a b : BT) : Bool :=
  (match idxF88 0 (dict b) with
   | none => false
   | some jb => VebIng114 (dict a) (psi (reg 1) jb))
  || (List.range ((wcnf (reg 1) (toList (dict b))).1.length + 1)).any (tgtOKtriv117 a b)

/-- **段の正直さ — `n` の範囲を一つ短く止めているのは飾りではない。**  `a` を**全部**
    畳んでよいとすると `restSep117` の組は閉じる。閉じるのは、`n` が `a` の対の個数
    ちょうどのとき条件が**結論そのもの**になるからである。§117.6 の受領 4 が、その形が
    母集団の上で結論とほぼ同値であることを測る。 -/
theorem restTriv117 :
    (closed117 restA117 restB117, closedTriv117 restA117 restB117) = (false, true) := rfl

/-- **既知の証人はどちらの側に落ちるか。**  §81 の `cexA89` と §101 の `bothBadA101` は
    どちらも `closed117` が偽 — **この条項に対する既知の反例は、§117 が閉じない側に
    そのまま残っている**。§114.4 の `revA114` は `b` が全発火するので `VebIngF114` の側。 -/
theorem knownSplit117 :
    (closed117 cexA89 cexB89, closed117 bothBadA101 bothBadB101,
     lastFire92 (dict cexB89), lastFire92 (dict bothBadB101),
     lastFire92 (dict revB114)) = (false, false, false, false, true) := rfl

end


/-! ### §117.6 測定 (凍結)

**構成 — §114.5 の三本の線に、四本目を組んで足す。**  §117 の条項が見るのは指数と
**係数**であり、§114.5 の母集団は係数が小さい項ばかりだった。`ψ₁(ψ₀ z)` の底 `Ω₁` の
分解は指数 `1`・係数 `ω^(ψ₀ z)` (§104.2) だから、`z` を大きく取れば係数だけが大きい項に
なる。それを種にした線を足す (`coefSeed117`)。濾さない。

    fireSeed117  全発火する種 4 個 (§114.5 と同じ)
    vebSeed117   発火しない種 3 個 (§114.5 と同じ)
    mixSeed117   `revA114` とその親戚 3 個 (§114.5 と同じ)
    coefSeed117  係数が大きい種 5 個 (**組んだ線**)
    pop117       その 2 項和も入れた 135 項  濾さない

`popNo117` は `coefSeed117` を抜いた 65 項 (§114.5 の母集団そのもの) で、**組んだ線が
要ることの受領**である。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

private def dedup117 (l : List BT) : List BT :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []
private def w4_117 : BT := BT.D 1 w3_101
private def fireSeed117 : List BT :=
  [w2_101, w3_101, w4_117, BT.D 1 (BT.sum w3_101 w3_101)]
private def vebSeed117 : List BT :=
  [w1_101, BT.D 1 (BT.D 0 w1_101), BT.D 1 (BT.D 0 (BT.sum w2_101 w1_101))]
private def mixSeed117 : List BT :=
  [revA114, BT.D 1 (BT.sum (BT.D 1 (BT.D 0 w1_101)) (BT.D 1 BT.zero)),
   BT.D 1 (BT.D 1 (BT.D 0 w3_101))]
private def g0B117 : BT := BT.D 0 w3_101
private def coefSeed117 : List BT :=
  [BT.D 1 g0B117, BT.D 1 (BT.D 0 (BT.D 1 g0B117)), BT.D 1 (BT.sum g0B117 w1_101),
   BT.D 1 (BT.D 0 (BT.sum w3_101 w3_101)),
   BT.D 1 (BT.sum (BT.D 1 g0B117) (BT.D 0 w3_101))]
private def seeds117 : List BT := fireSeed117 ++ vebSeed117 ++ mixSeed117 ++ coefSeed117
private def widen117 (l : List BT) : List BT :=
  dedup117 (l ++ l.flatMap (fun a => (l.filter (fun b => BT.le b a)).map (BT.sum a)))
private def pop117 : List BT := widen117 seeds117
private def popNo117 : List BT := widen117 (fireSeed117 ++ vebSeed117 ++ mixSeed117)
private def ok117 (a : BT) : Bool := btLe72 1 a && BT.isStd a && le (reg 1) (dict a)
private def kstd117 (a : BT) : Bool := ok117 a && BT.isStd (BT.D 0 a)
private def samp117 : List BT := pop117.filter ok117
private def ksamp117 : List BT := pop117.filter kstd117
private def sampNo117 : List BT := popNo117.filter ok117
private def ksampNo117 : List BT := popNo117.filter kstd117
private def pairs117 (l : List BT) : List (BT × BT) :=
  l.flatMap (fun a => l.map (fun b => (a, b)))
/-- 残余 — `hi` が狭義に増え、**どちらの**折り畳みも最後の対が発火しない組。
    `VebRest114` の担当分そのもの。 -/
private def resid117 (l : List BT) : List (BT × BT) :=
  (pairs117 l).filter (fun p =>
    lt (hiW89 (dict p.1)) (hiW89 (dict p.2)) && !lastFire92 (dict p.1)
      && !lastFire92 (dict p.2))
private def concl117 (p : BT × BT) : Bool :=
  lt (collapse 0 (hiW89 (dict p.1))) (collapse 0 (hiW89 (dict p.2)))
private def hasIdx117 (a : BT) : Bool := (idxF88 0 (dict a)).isSome
private def psiRoute117 (p : BT × BT) : Bool :=
  match idxF88 0 (dict p.2) with
  | none => false
  | some jb => VebIng114 (dict p.1) (psi (reg 1) jb)
private def vebRoute117 (p : BT × BT) : Bool :=
  (List.range ((wcnf (reg 1) (toList (dict p.2))).1.length + 1)).any (tgtOK117 p.1 p.2)
private def hdExp117 (y : Term) : Term :=
  match (wcnf (reg 1) (toList y)).1 with | [] => zero | ac :: _ => ac.1

/-! 母集団の形。**135 項、形の条件を満たすのが 104 項、`K` 標準が 54 項。** -/
#guard (pop117.length, samp117.length, ksamp117.length) == (135, 104, 54)

/-! **受領 1 — 道具は破れる場所で破れない。**  §117 の担当する残余は 4465 組、うち
    **782 組が結論を破る**。`closed117` はその 782 組では**一度も真にならず**、
    それでいて母集団ぜんぶでは 3523 組で真になる — 空虚な掃き出しではない。 -/
#guard ((resid117 samp117).length, (resid117 ksamp117).length,
        (resid117 samp117).countP (fun p => !concl117 p),
        (resid117 ksamp117).countP (fun p => !concl117 p)) == (4465, 990, 782, 0)
#guard ((resid117 samp117).countP (fun p => closed117 p.1 p.2 && !concl117 p),
        (resid117 samp117).countP (fun p => closed117 p.1 p.2)) == (0, 3104)

/-! **受領 2 — 残る条項の仮定は空でない。**  `K` 標準な 990 組のうち `closed117` が
    閉じるのは 936 組、**残り 54 組**。§114.3 の `ψ_{Ω₁}` の道筋だけなら 744 組、
    §117.4 の Veblen の的だけなら 503 組。 -/
#guard ((resid117 ksamp117).countP (fun p => closed117 p.1 p.2),
        (resid117 ksamp117).countP (fun p => !closed117 p.1 p.2),
        (resid117 ksamp117).countP psiRoute117,
        (resid117 ksamp117).countP vebRoute117) == (936, 54, 744, 503)

/-! **受領 3 — §117 は §114 が届かない類に届く。**  `b` が指数を持たない `K` 標準な
    120 組では §114.3 の道筋は **0 組**しか閉じず、§117.4 が 95 組を閉じる。
    `b` が指数を持つ 870 組では二つ合わせて 841 組。 -/
#guard ((resid117 ksamp117).countP (fun p => hasIdx117 p.2),
        (resid117 ksamp117).countP (fun p => hasIdx117 p.2 && closed117 p.1 p.2),
        (resid117 ksamp117).countP (fun p => !hasIdx117 p.2),
        (resid117 ksamp117).countP (fun p => !hasIdx117 p.2 && closed117 p.1 p.2),
        (resid117 ksamp117).countP (fun p => !hasIdx117 p.2 && psiRoute117 p))
      == (870, 841, 120, 95, 0)

/-! **受領 4 — `n` を一つ短く止めているのは飾りではない。**  `n` を `a` の対の個数
    ちょうどまで許すと 990 組ぜんぶが閉じ (増えるのはちょうど例の 54 組)、しかも形の
    条件だけの母集団では**結論が成り立つ 3683 組のうち 3523 組**でその形が成り立つ。
    `b` の値が `φ̄` の形をしている限り、それは結論の言い換えである。 -/
#guard ((resid117 ksamp117).countP (fun p => closedTriv117 p.1 p.2),
        (resid117 ksamp117).countP (fun p => closedTriv117 p.1 p.2 && !closed117 p.1 p.2),
        (resid117 samp117).countP (fun p => concl117 p && closedTriv117 p.1 p.2),
        (resid117 samp117).countP (fun p => concl117 p && !closedTriv117 p.1 p.2))
      == (990, 54, 3523, 160)

/-! **受領 5 — 外した 54 組は一つの形をしている。**  どれも `a` の先頭の指数が `b` の
    先頭の指数と**等しい**。しかもその形そのものが障害なのではない: 閉じた 936 組にも
    107 組ある。 -/
#guard (((resid117 ksamp117).filter (fun p => !closed117 p.1 p.2)).countP
          (fun p => hdExp117 (dict p.1) == hdExp117 (dict p.2)),
        ((resid117 ksamp117).filter (fun p => !closed117 p.1 p.2)).length,
        ((resid117 ksamp117).filter (fun p => closed117 p.1 p.2)).countP
          (fun p => hdExp117 (dict p.1) == hdExp117 (dict p.2))) == (54, 54, 107)

/-! **受領 6 — 係数の線は組む必要があった。**  それを抜いた 65 項 (§114.5 の母集団) では
    残余 1540 組・破れ 84 組で、`K` 標準の外れは 34 組。線を足すと破れは 9.3 倍になり、
    健全性の検査はその分だけ落ちる機会が増えた — そして落ちなかった。 -/
#guard (popNo117.length, (resid117 sampNo117).length,
        (resid117 sampNo117).countP (fun p => !concl117 p),
        (resid117 ksampNo117).length,
        (resid117 ksampNo117).countP (fun p => !closed117 p.1 p.2)) == (65, 1540, 84, 666, 34)

end

/-! ## §116 `UpProp113` IS A THEOREM — AND THE HALF IT WAS PAIRED WITH IS THE WHOLE
       RESIDUE, WITH THE SIZE INDUCTION WRITTEN OUT

§113 closed the coefficient half of `GapAtG0_107` and named exactly two things left:

  * `UpProp113` — "a `ψ₀` argument carrying something at or above the window's TOP has value
    at or above the top" (measured 30/30 and 9992/9992, premise firing 9 and 1718), and
  * "the bookkeeping that turns *at or above the bottom* into *at or above the top*",
    which §113.5 said is the size induction and not an oversight.

**§116 proves the first and shows the pairing was misleading: the second is not bookkeeping,
it is the whole thing.**  `UpProp113`'s premise fires on **6** of the **2495** legal `ψ₀`
arguments of §108.6's population whose value clears the window's top.  It is a sufficient
condition that is almost never the mechanism.  The clause the residue actually needs
therefore cannot be written with `upP113` in it, and §116.5 proves that in the sharp form:
the one-clause reading is **FALSE**, with §98's own tower as the witness.

  §116.1  **THE TARGET'S ARITHMETIC, FROM ABOVE.**  §113.1 proved `plus`, `ofList`, `sub1`,
          `splitFin`, `phiNF` and `ω^·` all stay BELOW `φ̄(Γ₀,R)`.  §116.1 proves they all
          stay AT OR ABOVE it (`leG_plus_left116`, `leG_plus_right116`, `leG_phiNF116`,
          `leG_omegaNF116`).  The only new input is 2.3.4 in the general form §100.1 proved
          (`lt_phi_of_le100`), plus one small fact that §113 never needed: the `phiNFsucc`
          "down" branch is only dangerous when `splitFin`'s front half is `0`, and
          `1 < G ≤ b` forbids that (`splitFin_ne_zero116`) — a term all of whose components
          are `1` is finite.

  §116.2  **`wcnf` DOES NOT DROP THEM EITHER.**  `wcnf_tailG116` and `wcnf_coefG116` are the
          mirrors of §113.3's `wcnfG113`: a sub-`Ω₁` component at or above the target puts
          the tail `ρ` there, and a digit whose coefficient is at or above the target leaves
          a PAIR whose coefficient is — the merge `plus (wC w p) c'` keeping it on either
          side.

  §116.3  **AND THE FOLD DOES NOT — INCLUDING THE STRONGLY CRITICAL BRANCH.**  That branch
          THROWS THE ACCUMULATOR AWAY and writes `ψ_{Ω₁}(i)`, so the naive invariant is not
          preserved.  Two facts repair it.  First, `ψ_{Ω₁}(i)` is at or above the window's
          top as soon as `i ≠ 0` (`lt_wTop_psi116`) — 2.3.5 and 2.3.14(ii), and **no `inT`
          anywhere in it**.  Second, `i ≠ 0` holds whenever the step's coefficient is big:
          `Δ = ω^E·c` is not `1` when `1 < c` (`dd_ne_one116`, from §110's
          `mulL_smono_right110` and §9.3's `below_one`), and `sub1` only kills `0` and `1`.
          What forbids a firing step AFTER a Veblen step is §109.1's `fireSplit109`, carried
          into `foldU116` as an explicit hypothesis together with the state-side companion
          `VebFree116` — the two together are what make the induction go through in ONE pass,
          with no `takeWhile`/`dropWhile` splitting of the fold.

  §116.4  **`UpProp113`, WITH ONE GATE, AND THE GATE IS ALREADY IN THE CERTIFICATE.**
          `upPropIn116` is `UpProp113` for every `x` satisfying (G3) `PsiIdxOK 0 x`.  The gate
          is not decoration and it is not avoidable in this proof: without it `collapse 0 x`
          need not be a term of 𝔗(M) at all, and every order lemma used above is stated on
          𝔗(M).  **At the point of use it costs nothing**: `PsiIdxOKStd172` — already in row
          326's certificate — hands `PsiIdxOK 0 (dict a)` for exactly the `a` the clause is
          asked about.  `psiIdxOK_of_gateB116` makes the gate decidable, so `upPropIn116`
          applies to concrete terms with no hypothesis at all.

  §116.5  **THE ONE-CLAUSE READING OF WHAT IS LEFT IS FALSE.**  With §116.4 in hand the
          obvious residue is `MidUp116`: "`badP113` fires ⟹ `upP113` fires".  It reduces
          `WinProp113` (`winProp_of_midUp116`) and **it is false** (`midUp116_false`):
          `bTowG98 1 = ψ₀(Ω^Ω ⊕ ψ₁ψ₁ψ₀Ω^Ω)` is a legal witness, satisfies `ψ₀(Ω^Ω) < ·`,
          has value EXACTLY the window's top — and `upP113` fires nowhere in its argument
          (`notUp_bTow1_116`), while `badP113` does (`bad_bTow1_116`).  The same witness
          kills the clause-shaped version `ExpUpNaive116`.

  §116.6  **THE BOOKKEEPING IS AN INDUCTION, AND ONE OF ITS THREE SHAPES IS FREE.**
          `winUpAux116` is the size induction §113.5 described in prose, as a theorem: strong
          induction on `BT.size`, with §113.4's `coefWinEx113` splitting into the three shapes
          `badP113` can take.  **The sub-`Ω₁` shape is discharged by the induction hypothesis
          and nothing else** — §101.1's free half names the component, §98's
          `ltW_dictD1_false98` shows a sub-`Ω₁` component is `ψ₀`-headed, the component is
          smaller, and §116.4 lifts the result back.  What is left is one clause per remaining
          shape, both stated on the VALUE (not on `upP113`, §116.5): `ExpUp116` for a digit
          exponent at or above `Γ₀` — the 𝔗(M) side of §111's carrier half — and `CoefUp116`
          for a digit coefficient at or above the window's bottom — the 𝔗(M) side of §113.5's
          hereditary argument.  `winProp_of_two116` : the two together give `WinProp113`,
          hence `GapAtG0_107` and the five falsity corollaries, **with no `UpProp113` and no
          new gate**.

WHAT IS **NOT** CLAIMED.  **`UpProp113` verbatim — quantified over every `x : Term` — is NOT
proved**: `upPropIn116` assumes (G3), and §116.7 measures that (G3) genuinely fails (48 of
E's 9992), though never on a term whose `ψ₀` is standard (0 of 48) and never in a way that
breaks `UpProp113`'s own implication (48/48).  **`SCFirstOne111`, `SCFirst108` and
`GapAtG0_107` are NOT proved and NOT refuted.**  `ExpUp116` and `CoefUp116` are named and
unproved; so are `Gam0Drags111`, `PsiIdxOKStd172` and `DictLtA74`.  **The exponent BRIDGE
§113 asked for — from the 𝔗(M)-side exponent clause to §111's Buchholz-side
`carrier_notStd111` — is NOT proved here.**  What §116 does with it is give its 𝔗(M) side a
name inside a certificate that no longer contains `UpProp113`.  `DictDenseMid107`,
`DictDenseMid102`, `DictDenseHi94`, `DictDense85`, `CofDenseS1` and row 326's certificate are
exactly where §113 left them.  §116 does not touch §103's hole and does not reach
`FoldSkips108`.

**WHERE §116 STOPPED, PRECISELY, AND WHAT MOVED.**  One of §113's two named halves is
**removed**, not moved: the road from `WinProp113` to `GapAtG0_107` now runs through
`PsiIdxOKStd172 + DictLtA74 + ExpUp116 + CoefUp116` and mentions `UpProp113` nowhere.  The
other half turned out to be the whole residue, and §116 splits it by SHAPE rather than by
size: three shapes, one of them a theorem.  **The residue did shrink and it also changed
shape** — it is no longer "one arithmetical clause plus an induction" but "two clauses, each
about one digit shape, with the induction discharged".

**AND THE OVERPAYMENT LEDGER.**  The ninth entry, and it is §113's own: `UpProp113` was named
as one of the two halves left, and it is the smaller by a factor of four hundred.  Of the 2495
legal `ψ₀` arguments in E whose value clears the window's top, `upP113` fires on **6**.  The
clause is true, it is now proved, and the route through it reaches 6 cases out of 2495 —
which is why §116.5's one-clause reading of the rest is false rather than merely hard.

WHAT THE MEASUREMENT SAYS (§116.7 gives the construction).  One population is BUILT, one is
re-read, and one is re-built one size up.

  * **S is BUILT and it cannot test the two clauses.**  52 terms, 13 window-and-above seeds in
    four shapes, not filtered by standardness.  All three digit shapes are visible (exponent
    26, coefficient 27, tail 9); 24 land in the window; 7 are legal `ψ₀` arguments; **0 are
    both.**  §111's and §113's seed problem, a third time and at the same place: the shapes
    that matter live on terms that standardness removes.
  * **The gate is visible on both sides.**  It holds on 52 of S's 52, and on E it holds on
    9944 of 9992 and FAILS on 48.  **None of the 48 has a standard `ψ₀` on top** (0/48), so
    `PsiIdxOKStd172` is not touched; and `UpProp113`'s implication holds on all 48 anyway
    (premise firing 7).  The gate is a restriction on the PROOF, not — as far as measured — on
    the statement.
  * **`UpProp113` holds on S, 52/52, with the premise firing on 12.**
  * **The clause is asked at 2495 places in E and only ONE shape ever fires there.**  Of E's
    legal `ψ₀` arguments with value at or above the window's bottom (2495), the exponent
    clause fires 2495 times, the coefficient clause **0**, the tail clause 3, and the
    conclusion fails 0 times.
  * **`upP113` fires on 6 of the 2495 that clear the top** — the ledger entry above.
  * **E14 — one size up, and the coefficient shape appears.**  Rebuilding §108.6's
    enumeration to size 14 (58239 terms) gives 16425 places where the clause is asked: the
    exponent clause fires 16425 times, **the coefficient clause 11** (it was 0 at size 12),
    the tail clause 43, and the conclusion fails 0 times.  **`CoefUp116` is not vacuous — the
    size-12 population simply could not see it.** -/


section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- 窓の上端。 -/
def wTop116 : Term := dict (bTowG98 1)

theorem wTop_eq116 : wTop116 = phi G094 (plus G094 TM.Term.one) := rfl
theorem isAP_wTop116 : wTop116.isAP = true := rfl
theorem inT_wTop116 : inT wTop116 = true := by decide
theorem ltM_wTop116 : lt wTop116 M = true := by decide
theorem lt_one_wTop116 : lt TM.Term.one wTop116 = true := by decide

/-- 右の引数が的以上なら和も的以上。 -/
theorem leG_plus_right116 {G s t : Term} (hG : inT G = true) (hs : inT s = true)
    (ht : inT t = true) (h : le G t = true) : le G (plus s t) = true :=
  le_trans_inT hG ht (inT_plus hs ht) h (le_self_plus75 hs ht)

/-- 左の引数が的以上なら和も的以上 — 的が加法主要なとき。 -/
theorem leG_plus_left116 {G s t : Term} (hG : inT G = true) (hGap : G.isAP = true)
    (hs : inT s = true) (ht : inT t = true) (h : le G s = true) : le G (plus s t) = true := by
  cases hls : toList s with
  | nil =>
      rw [toList_eq_nil s hls] at h ⊢
      rw [show le G zero = ((G == zero) || lt G zero) from rfl,
        show lt G zero = false from ltF_right_zero _ _, Bool.or_false] at h
      rw [eq_of_beq h]
      exact le_zero_left _
  | cons b rest =>
      have hib : inT b = true := inTL_inT hs b (by rw [hls]; exact List.Mem.head _)
      have hGb : le G b = true := le_hd_of_le109 hG hGap hs hls h
      cases hlt : toList t with
      | nil => rw [plus_nil hlt]; exact h
      | cons b1 r =>
          have hib1 : inT b1 = true := inTL_inT ht b1 (by rw [hlt]; exact List.Mem.head _)
          have hp : inT (plus s t) = true := inT_plus hs ht
          have htl : toList (plus s t) = (toList s).filter (fun a => le b1 a) ++ toList t :=
            toList_plus_inT hs ht hlt
          by_cases hle : le b1 b = true
          · refine le_of_le_hd109 hG hp
              (show toList (plus s t) = b :: (rest.filter (fun a => le b1 a) ++ toList t)
                from ?_) hGb
            rw [htl, hls, List.filter_cons_of_pos hle, List.cons_append]
          · have hbb1 : lt b b1 = true := lt_of_not_le_inT hib1 hib (bool_false hle)
            have hnil : (toList s).filter (fun a => le b1 a) = [] := by
              rw [hls]
              refine List.filter_eq_nil_iff.mpr ?_
              intro x hx
              have hxb : le x b = true := by
                rcases List.mem_cons.mp hx with h1 | h1
                · rw [h1]; exact le_self _
                · obtain ⟨hc, hd⟩ := inT_toList s hs
                  rw [hls] at hc hd
                  exact descL_bound_inT rest b hib (inTL_cons.mp hc).2 hd x h1
              have hix : inT x = true := by
                rcases List.mem_cons.mp hx with h1 | h1
                · rw [h1]; exact hib
                · exact inTL_inT hs x (by rw [hls]; exact List.Mem.tail _ h1)
              have : lt x b1 = true :=
                lt_of_le_of_lt3 (inT_le_fragR _ hix) (inT_le_fragR _ hib)
                  (inT_le_fragR _ hib1) hxb hbb1
              intro hc
              rw [show le b1 x = ((b1 == x) || lt b1 x) from rfl] at hc
              rcases (Bool.or_eq_true _ _).mp hc with h1 | h1
              · rw [eq_of_beq h1, lt_irrefl] at this; exact Bool.noConfusion this
              · rw [lt_asymm_inT hib1 hix h1] at this; exact Bool.noConfusion this
            refine le_of_le_hd109 hG hp (show toList (plus s t) = b1 :: r from ?_) ?_
            · rw [htl, hnil, List.nil_append, hlt]
            · exact le_trans_inT hG hib hib1 hGb (le_of_lt hbb1)

/-- `φ̄` は第 2 引数を下から押さえる — 2.3.4 の一般形 (§100.1) の言い換え。 -/
theorem leG_phi116 {G a b : Term} (hG : inT G = true) (hGM : lt G M = true)
    (hia : inT a = true) (hib : inT b = true) (haM : lt a M = true) (hbM : lt b M = true)
    (h : le G b = true) : le G (phi a b) = true :=
  le_of_lt (lt_phi_of_le100 G.deg G a b (Nat.le_refl _) hG hGM
    (show inT (phi a b) = true from by
      show (inT a && inT b && lt a M && lt b M) = true
      rw [hia, hib, haM, hbM]; rfl) (Or.inr h))

/-- 先頭からの `takeWhile` が全長を取るなら、列は全部その述語を満たす。 -/
theorem all_of_takeWhile_len116 {P : Term → Bool} :
    ∀ (L : List Term), (L.takeWhile P).length = L.length → ∀ x ∈ L, P x = true
  | [], _, _, hx => by cases hx
  | a :: t, hlen, x, hx => by
      by_cases hp : P a = true
      · rw [List.takeWhile_cons_of_pos hp, List.length_cons, List.length_cons] at hlen
        rcases List.mem_cons.mp hx with h1 | h1
        · rw [h1]; exact hp
        · exact all_of_takeWhile_len116 t (by omega) x h1
      · exfalso
        rw [List.takeWhile_cons_of_neg hp, List.length_nil, List.length_cons] at hlen
        omega

theorem len_takeWhile_le116 {P : Term → Bool} :
    ∀ (L : List Term), (L.takeWhile P).length ≤ L.length
  | [] => Nat.le_refl 0
  | a :: t => by
      by_cases hp : P a = true
      · rw [List.takeWhile_cons_of_pos hp, List.length_cons, List.length_cons]
        exact Nat.succ_le_succ (len_takeWhile_le116 t)
      · rw [List.takeWhile_cons_of_neg hp]
        exact Nat.zero_le _

theorem take_eq_nil116 : ∀ (L : List Term) (K : Nat), L.take K = [] → K = 0 ∨ L = []
  | [], _, _ => Or.inr rfl
  | _ :: _, 0, _ => Or.inl rfl
  | a :: t, _ + 1, h => by
      rw [List.take_succ_cons] at h
      exact absurd h (List.cons_ne_nil _ _)

/-- `splitFin` を `take` の形で読み直したもの。 -/
theorem toList_splitFin116 {b : Term} (hb : inT b = true) :
    toList (splitFin b).1 = (toList b).take ((toList b).length -
      ((toList b).reverse.takeWhile (fun x => x == TM.Term.one)).length) := by
  rw [splitFin_eq104]
  exact toList_ofList _ (fun x hx => inTL_isAP hb x (List.mem_of_mem_take hx))

/-- `1 < G ≤ b` なら `splitFin` の前半は `0` ではない。 -/
theorem splitFin_ne_zero116 {G b : Term} (hG : inT G = true) (hGap : G.isAP = true)
    (hb : inT b = true) (hG1 : lt TM.Term.one G = true) (h : le G b = true) :
    (splitFin b).1 ≠ zero := by
  intro hc
  have hk := toList_splitFin116 hb
  rw [hc, show toList (zero : Term) = [] from rfl] at hk
  cases hlb : toList b with
  | nil =>
      rw [toList_eq_nil b hlb,
        show le G zero = ((G == zero) || lt G zero) from rfl,
        show lt G zero = false from ltF_right_zero _ _, Bool.or_false] at h
      rw [eq_of_beq h] at hG1
      exact Bool.noConfusion (hG1.symm.trans (ltF_right_zero _ _))
  | cons b0 r0 =>
      have hKz : (toList b).length -
          ((toList b).reverse.takeWhile (fun x => x == TM.Term.one)).length = 0 := by
        rcases take_eq_nil116 (toList b) _ hk.symm with h1 | h1
        · exact h1
        · exact absurd (h1.symm.trans hlb) (fun hcc => (List.cons_ne_nil b0 r0) hcc.symm)
      have hmle := len_takeWhile_le116 (P := fun x => x == TM.Term.one) (toList b).reverse
      rw [List.length_reverse] at hmle
      have hlen : ((toList b).reverse.takeWhile (fun x => x == TM.Term.one)).length
          = (toList b).reverse.length := by
        rw [List.length_reverse]; omega
      have hb0 : b0 = TM.Term.one := by
        have hh := all_of_takeWhile_len116 (P := fun x => x == TM.Term.one) _ hlen b0
          (by rw [List.mem_reverse, hlb]; exact List.Mem.head _)
        exact eq_of_beq hh
      have hGb0 : le G b0 = true := le_hd_of_le109 hG hGap hb hlb h
      rw [hb0, show le G TM.Term.one = ((G == TM.Term.one) || lt G TM.Term.one) from rfl] at hGb0
      rcases (Bool.or_eq_true _ _).mp hGb0 with h1 | h1
      · rw [eq_of_beq h1, lt_irrefl] at hG1; exact Bool.noConfusion hG1
      · rw [lt_asymm_inT hG inT_one h1] at hG1; exact Bool.noConfusion hG1

/-- `splitFin` の前半は的以上のまま — `0` に潰れないかぎり。 -/
theorem leG_splitFin116 {G b : Term} (hG : inT G = true) (hGap : G.isAP = true)
    (hb : inT b = true) (h : le G b = true) (hne : (splitFin b).1 ≠ zero) :
    le G (splitFin b).1 = true := by
  have hiS : inT (splitFin b).1 = true := inT_splitFin hb
  have hk := toList_splitFin116 hb
  cases hl : toList (splitFin b).1 with
  | nil => exact absurd (toList_eq_nil _ hl) hne
  | cons c rest =>
      refine le_of_le_hd109 hG hiS hl ?_
      have hkc : (toList b).take ((toList b).length -
          ((toList b).reverse.takeWhile (fun x => x == TM.Term.one)).length) = c :: rest := by
        rw [← hk]; exact hl
      cases hlb : toList b with
      | nil =>
          exfalso
          rw [hlb, List.take_nil] at hkc
          exact (List.cons_ne_nil c rest) hkc.symm
      | cons b0 r0 =>
          have hc : c = b0 := by
            rcases Nat.eq_zero_or_pos ((toList b).length -
                ((toList b).reverse.takeWhile (fun x => x == TM.Term.one)).length) with h1 | h1
            · exfalso
              rw [h1, List.take_zero] at hkc
              exact (List.cons_ne_nil c rest) hkc.symm
            · obtain ⟨j, hj⟩ : ∃ j, (toList b).length -
                  ((toList b).reverse.takeWhile (fun x => x == TM.Term.one)).length = j + 1 :=
                ⟨_, (Nat.succ_pred_eq_of_pos h1).symm⟩
              rw [hj, hlb, List.take_succ_cons] at hkc
              exact ((List.cons.inj hkc).1).symm
          rw [hc]
          exact le_hd_of_le109 hG hGap hb hlb h

/-- `phiNFdefault` は的の上側で閉じる。 -/
theorem leG_phiNFdefault116 {G a b : Term} (hG : inT G = true) (hGM : lt G M = true)
    (hGnz : lt zero G = true) (hia : inT a = true) (haM : lt a M = true)
    (hib : inT b = true) (hbM : lt b M = true) (h : le G b = true) :
    le G (phiNFdefault a b) = true := by
  unfold phiNFdefault
  split
  · rename_i heq
    exfalso
    have hb0 : b = zero := eq_of_beq ((Bool.and_eq_true _ _).mp heq).1
    rw [hb0, show le G zero = ((G == zero) || lt G zero) from rfl,
      show lt G zero = false from ltF_right_zero _ _, Bool.or_false] at h
    rw [eq_of_beq h, lt_irrefl] at hGnz
    exact Bool.noConfusion hGnz
  · exact leG_phi116 hG hGM hia hib haM hbM h

/-- `phiNFsucc` も — `splitFin` の前半が `0` でないかぎり。 -/
theorem leG_phiNFsucc116 {G a b : Term} (hG : inT G = true) (hGap : G.isAP = true)
    (hGM : lt G M = true) (hGnz : lt zero G = true) (hia : inT a = true) (haM : lt a M = true)
    (hib : inT b = true) (hbM : lt b M = true) (hne : (splitFin b).1 ≠ zero)
    (h : le G b = true) : le G (phiNFsucc a b) = true := by
  have hdef : le G (phiNFdefault a b) = true :=
    leG_phiNFdefault116 hG hGM hGnz hia haM hib hbM h
  have hiS : inT (splitFin b).1 = true := inT_splitFin hib
  have hSM : lt (splitFin b).1 M = true := ltM_splitFin hib hbM
  have hdown : ∀ n : Nat, le G (phi a (plus (splitFin b).1 (TM.Term.ofNat n))) = true := by
    intro n
    exact leG_phi116 hG hGM hia (inT_plus hiS (inT_ofNat n)) haM
      (lt_plus_M hiS (inT_ofNat n) hSM (ltM_ofNat n))
      (leG_plus_left116 hG hGap hiS (inT_ofNat n) (leG_splitFin116 hG hGap hib h hne))
  unfold phiNFsucc
  split
  rename_i heq
  rw [heq] at hdown
  split
  · split <;> (split <;> first | exact hdown _ | exact hdef)
  · exact hdef

/-- **`phiNF` は的の上側で閉じる。**  §113.1 の `lt_phiNF113` の逆向き。 -/
theorem leG_phiNF116 {G a b : Term} (hG : inT G = true) (hGap : G.isAP = true)
    (hGM : lt G M = true) (hG1 : lt TM.Term.one G = true) (hia : inT a = true)
    (haM : lt a M = true) (hib : inT b = true) (hbM : lt b M = true) (h : le G b = true) :
    le G (phiNF a b) = true := by
  have hGnz : lt zero G = true :=
    lt_trans_inT inT_zero inT_one hG (by decide) hG1
  have hne : (splitFin b).1 ≠ zero := splitFin_ne_zero116 hG hGap hib hG1 h
  have hsucc := leG_phiNFsucc116 hG hGap hGM hGnz hia haM hib hbM hne h
  unfold phiNF
  split
  · exact h
  · split
    · split
      · exact h
      · exact hsucc
    · exact hsucc

/-- **`ω^·` も。** -/
theorem leG_omegaNF116 {G x : Term} (hG : inT G = true) (hGap : G.isAP = true)
    (hGM : lt G M = true) (hG1 : lt TM.Term.one G = true) (hix : inT x = true)
    (hxM : lt x M = true) (h : le G x = true) : le G (omegaNF x) = true := by
  have hMx : lt M x = false := lt_asymm_inT hix (show inT (M : Term) = true from rfl) hxM
  have hxne : (x == M) = false := by
    cases hb : (x == M) with
    | false => rfl
    | true =>
        exfalso
        rw [eq_of_beq hb, lt_irrefl] at hxM
        exact Bool.noConfusion hxM
  show le G (if lt M x then omg x else if x == M then M else phiNF zero x) = true
  rw [if_neg (by rw [hMx]; exact Bool.noConfusion),
    if_neg (by rw [hxne]; exact Bool.noConfusion)]
  exact leG_phiNF116 hG hGap hGM hG1 inT_zero lt_zero_M hix hxM h

/-! ### §116.2 大きいものは `wcnf` を通って残る -/

/-- `Ω₁` より下の成分が的以上なら、尾も的以上。 -/
theorem wcnf_tailG116 {G : Term} (hG : inT G = true) (_hGap : G.isAP = true) :
    ∀ (L : List Term), inTL L = true → descL L = true →
      ∀ p ∈ L, lt p (reg 1) = true → le G p = true → le G (wcnf (reg 1) L).2 = true := by
  intro L
  induction L with
  | nil => intro _ _ p hp _ _; cases hp
  | cons q rest ih =>
    intro hc hd p hp hpw hGp
    obtain ⟨⟨hapq, hiq⟩, hcr⟩ := inTL_cons.mp hc
    have hdr := descL_tail hd
    by_cases hlq : lt q (reg 1) = true
    · rw [wcnf_snd_cons88, if_pos hlq]
      have hiO : inT (ofList (q :: rest)) = true := inT_ofList _ hc hd
      have hGq : le G q = true := by
        rcases List.mem_cons.mp hp with h1 | h1
        · rw [← h1]; exact hGp
        · have hip : inT p = true :=
            ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcr p h1)).2
          exact le_trans_inT hG hip hiq hGp (descL_bound_inT rest q hiq hcr hd p h1)
      exact le_of_le_hd109 hG hiO (toList_ofList89 hc) hGq
    · rw [wcnf_snd_cons88, if_neg hlq]
      refine ih hcr hdr p ?_ hpw hGp
      rcases List.mem_cons.mp hp with h1 | h1
      · exfalso; rw [h1] at hpw; exact hlq hpw
      · exact h1

/-- `Ω₁` 以上の成分の係数が的以上なら、対の列に的以上の係数を持つ対がある。 -/
theorem wcnf_coefG116 {G : Term} (hG : inT G = true) (hGap : G.isAP = true) :
    ∀ (L : List Term), inTL L = true → descL L = true → (∀ x ∈ L, lt x M = true) →
      ∀ p ∈ L, lt p (reg 1) = false → le G (wC (reg 1) p) = true →
        ∃ ac ∈ (wcnf (reg 1) L).1, le G ac.2 = true := by
  intro L
  induction L with
  | nil => intro _ _ _ p hp _ _; cases hp
  | cons q rest ih =>
    intro hc hd hM p hp hpw hGp
    obtain ⟨⟨hapq, hiq⟩, hcr⟩ := inTL_cons.mp hc
    have hdr := descL_tail hd
    have hMr : ∀ x ∈ rest, lt x M = true := fun x hx => hM x (List.Mem.tail _ hx)
    by_cases hlq : lt q (reg 1) = true
    · exfalso
      rcases List.mem_cons.mp hp with h1 | h1
      · rw [h1, hlq] at hpw; exact Bool.noConfusion hpw
      · have hip : inT p = true :=
          ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcr p h1)).2
        have hpw2 := ltW_of_le79 hip hiq (descL_bound_inT rest q hiq hcr hd p h1) hlq
        rw [hpw2] at hpw; exact Bool.noConfusion hpw
    · have hlq' : lt q (reg 1) = false := bool_false hlq
      have hiwCq : inT (wC (reg 1) q) = true := inT_wC hiq
      have hPO := wcnf_spec_sc (inT_reg 1) (show (reg 1).isSC = true from rfl) rest hcr hdr hMr
      rw [wcnf_cons_ge hlq']
      cases hr : wcnf (reg 1) rest with
      | mk fst snd =>
        rw [hr] at hPO
        cases fst with
        | nil =>
            refine ⟨(wA (reg 1) q, wC (reg 1) q), List.Mem.head _, ?_⟩
            rcases List.mem_cons.mp hp with h1 | h1
            · rw [← h1]; exact hGp
            · exfalso
              obtain ⟨ac, hac, _⟩ := ih hcr hdr hMr p h1 hpw hGp
              rw [hr] at hac; cases hac
        | cons ac0 ps =>
          cases ac0 with
          | mk a' c' =>
            have hic' : inT c' = true := (hPO.2 (a', c') (List.Mem.head _)).2.2.1
            have key : le G (wC (reg 1) q) = true ∨
                (∃ ac ∈ (a', c') :: ps, le G ac.2 = true) := by
              rcases List.mem_cons.mp hp with h1 | h1
              · exact Or.inl (by rw [← h1]; exact hGp)
              · obtain ⟨ac, hac, hGac⟩ := ih hcr hdr hMr p h1 hpw hGp
                rw [hr] at hac
                exact Or.inr ⟨ac, hac, hGac⟩
            show ∃ ac ∈ (if (wA (reg 1) q == a') = true
                then ((wA (reg 1) q, plus (wC (reg 1) q) c') :: ps, snd)
                else ((wA (reg 1) q, wC (reg 1) q) :: (a', c') :: ps, snd)).1, le G ac.2 = true
            by_cases heq : (wA (reg 1) q == a') = true
            · rw [if_pos heq]
              rcases key with h1 | ⟨ac, hac, hGac⟩
              · exact ⟨(wA (reg 1) q, plus (wC (reg 1) q) c'), List.Mem.head _,
                  leG_plus_left116 hG hGap hiwCq hic' h1⟩
              · rcases List.mem_cons.mp hac with h2 | h2
                · refine ⟨(wA (reg 1) q, plus (wC (reg 1) q) c'), List.Mem.head _, ?_⟩
                  refine leG_plus_right116 hG hiwCq hic' ?_
                  rw [h2] at hGac; exact hGac
                · exact ⟨ac, List.Mem.tail _ h2, hGac⟩
            · rw [if_neg heq]
              rcases key with h1 | ⟨ac, hac, hGac⟩
              · exact ⟨(wA (reg 1) q, wC (reg 1) q), List.Mem.head _, h1⟩
              · exact ⟨ac, List.Mem.tail _ hac, hGac⟩

/-! ### §116.3 畳み込みは大きいものを落とさない -/

theorem le_wTop_G0_false116 : le wTop116 G094 = false :=
  not_le_of_lt113 inT_wTop116 inT_G094_102 (lt_G0_gT113 zero)

/-- **`ψ_{Ω₁}(i)` は `i ≠ 0` なら窓の上端以上。**  `inT` を一切使わない。 -/
theorem lt_wTop_psi116 {i : Term} (hi : i ≠ zero) : lt wTop116 (psi (reg 1) i) = true := by
  have h1 : lt G094 (psi (reg 1) i) = true := by
    show lt (psi (Z zero) zero) (psi (Z zero) i) = true
    rw [lt_psi_same]
    exact lt_zero_left hi
  have h2 : lt (plus G094 TM.Term.one) (psi (reg 1) i) = true := by
    rw [show plus G094 TM.Term.one = add G094 TM.Term.one from rfl,
      lt_add_ap102 _ _ (show (psi (reg 1) i).isAP = true from rfl)]
    exact h1
  show lt (phi G094 (plus G094 TM.Term.one)) (psi (reg 1) i) = true
  exact lt_phi_psi_of h1 h2

theorem le_wTop_psi116 {i : Term} (hi : i ≠ zero) : le wTop116 (psi (reg 1) i) = true :=
  le_of_lt (lt_wTop_psi116 hi)

/-- 逆に `ψ_{Ω₁}(0) = Γ₀` は窓の上端に届かない。 -/
theorem psi_ne_zero_of_big116 {i : Term} (h : le wTop116 (psi (reg 1) i) = true) : i ≠ zero := by
  intro hc
  rw [hc, show psi (reg 1) zero = G094 from rfl, le_wTop_G0_false116] at h
  exact Bool.noConfusion h

/-- `1 < G ≤ c` なら `sub1` は何も削らない。 -/
theorem leG_sub1_116 {G c : Term} (hG : inT G = true) (hGap : G.isAP = true)
    (hic : inT c = true) (hG1 : lt TM.Term.one G = true) (h : le G c = true) : sub1 c = c := by
  show (match toList c with
        | [] => zero
        | p :: rest => if p == TM.Term.one then ofList rest else c) = c
  cases hl : toList c with
  | nil => exact (toList_eq_nil c hl).symm
  | cons p rest =>
      have hGp : le G p = true := le_hd_of_le109 hG hGap hic hl h
      show (if (p == TM.Term.one) = true then ofList rest else c) = c
      have hp : (p == TM.Term.one) = false := by
        cases hb : (p == TM.Term.one) with
        | false => rfl
        | true =>
            exfalso
            rw [eq_of_beq hb,
              show le G TM.Term.one = ((G == TM.Term.one) || lt G TM.Term.one) from rfl] at hGp
            rcases (Bool.or_eq_true _ _).mp hGp with h1 | h1
            · rw [eq_of_beq h1, lt_irrefl] at hG1; exact Bool.noConfusion hG1
            · rw [lt_asymm_inT hG inT_one h1] at hG1; exact Bool.noConfusion hG1
      rw [if_neg (by rw [hp]; exact Bool.noConfusion)]

/-- `sub1` が `0` を返すのは `0` と `1` からだけ。 -/
theorem sub1_ne_zero116 {d : Term} (hd : inT d = true) (hz : d ≠ zero)
    (h1 : d ≠ TM.Term.one) : sub1 d ≠ zero := by
  show (match toList d with
        | [] => zero
        | p :: rest => if p == TM.Term.one then ofList rest else d) ≠ zero
  cases hl : toList d with
  | nil => exact absurd (toList_eq_nil d hl) hz
  | cons p rest =>
      show (if (p == TM.Term.one) = true then ofList rest else d) ≠ zero
      by_cases hp : (p == TM.Term.one) = true
      · rw [if_pos hp]
        cases hr : rest with
        | nil =>
            exfalso
            refine h1 ?_
            rw [← inT_ofList_toList d hd, hl, hr, eq_of_beq hp]
            rfl
        | cons q r =>
            refine ofList_ne_zero81 (q :: r) (List.cons_ne_nil _ _) ?_
            intro x hx
            exact inTL_isAP hd x (by rw [hl, hr]; exact List.Mem.tail _ hx)
      · rw [if_neg hp]; exact hz

/-- `Δ = ω^E·c` は `c > 1` なら `1` ではない。 -/
theorem dd_ne_one116 {ac : Term × Term} (h1 : inT ac.1 = true) (h3 : inT ac.2 = true)
    (hcM : lt ac.2 M = true) (hgt : lt TM.Term.one ac.2 = true) :
    ddOf75 (reg 1) ac ≠ TM.Term.one := by
  intro hc
  have hE : inT (mulL (reg 1) (subAP (reg 1) ac.1)) = true :=
    inT_mulL mulDescInT (inT_reg 1) (inT_subAP h1)
  have hlt : lt (ddOf75 (reg 1) (ac.1, TM.Term.one)) (ddOf75 (reg 1) ac) = true :=
    mulL_smono_right110 hE inT_one h3 lt_one_M hcM hgt
  rw [hc] at hlt
  exact (ddOf_ne_zero84 (w := reg 1) (ac := (ac.1, TM.Term.one))
      (show ((ac.1, TM.Term.one) : Term × Term).2 ≠ zero from
        fun hcc => Term.noConfusion hcc))
    (below_one _ (inT_ddOf75 (inT_reg 1) h1 inT_one) _ hlt)

theorem le_zero_eq116 {x : Term} (h : le x zero = true) : x = zero := by
  rw [show le x zero = ((x == zero) || lt x zero) from rfl,
    show lt x zero = false from ltF_right_zero _ _, Bool.or_false] at h
  exact eq_of_beq h

/-- **強臨界枝の指数は `0` にならない** — 前の指数が `0` でないか、係数が `1` より上なら。 -/
theorem idxOf_ne_zero116 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hcM : lt ac.2 M = true)
    (h : lt TM.Term.one ac.2 = true ∨ (∃ i0, s.1 = some i0 ∧ i0 ≠ zero)) :
    idxOf (reg 1) s ac ≠ zero := by
  intro hc
  rcases h with hgt | ⟨i0, hs1, hi0⟩
  · have hz : ac.2 ≠ zero := by
      intro hcc; rw [hcc] at hgt
      exact Bool.noConfusion (hgt.symm.trans (ltF_right_zero _ _))
    have hdi : inT (ddOf75 (reg 1) ac) = true := inT_ddOf75 (inT_reg 1) h1 h3
    have hs1z : sub1 (ddOf75 (reg 1) ac) ≠ zero :=
      sub1_ne_zero116 hdi (ddOf_ne_zero84 hz) (dd_ne_one116 h1 h3 hcM hgt)
    have hle := le_sub1dd_idxOf75 (inT_reg 1) hst h1 h3
    rw [hc] at hle
    exact hs1z (le_zero_eq116 hle)
  · have hle := le_prev_idxOf75 (inT_reg 1) hst hs1 h1 h3
    rw [hc] at hle
    exact hi0 (le_zero_eq116 hle)

/-- 累算器が窓の上端以上であること。 -/
def BigU116 (s : Option Term × Option Term) : Prop :=
  ∃ v, s.2 = some v ∧ le wTop116 v = true

/-- 状態が「強臨界枝からしか来ていない」こと。 -/
def VebFree116 (s : Option Term × Option Term) : Prop :=
  s.2 = none ∨ ∃ i, s.1 = some i ∧ s.2 = some (psi (reg 1) i)

theorem mem_of_mem_dropWhile116 {α : Type} {p : α → Bool} :
    ∀ (l : List α) (x : α), x ∈ l.dropWhile p → x ∈ l
  | [], x, h => by rw [List.dropWhile_nil] at h; exact h
  | a :: t, x, h => by
      rw [List.dropWhile_cons] at h
      by_cases hp : p a = true
      · rw [if_pos hp] at h
        exact List.Mem.tail _ (mem_of_mem_dropWhile116 t x h)
      · rw [if_neg hp] at h; exact h


theorem lt_one_of_leTop116 {c : Term} (hic : inT c = true) (h : le wTop116 c = true) :
    lt TM.Term.one c = true :=
  lt_of_lt_of_le3 (inT_le_fragR _ inT_one) (inT_le_fragR _ inT_wTop116)
    (inT_le_fragR _ hic) lt_one_wTop116 h

/-- 強臨界枝の一歩 — 指数が `0` でなければ累算器は窓の上端以上になる。 -/
theorem stepBigFire116 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (hf : le (reg 1) ac.1 = true)
    (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (h4 : lt ac.2 M = true)
    (h : lt TM.Term.one ac.2 = true ∨ (∃ i0, s.1 = some i0 ∧ i0 ≠ zero)) :
    BigU116 (stepF (reg 1) (baseOf 0) s ac) :=
  ⟨psi (reg 1) (idxOf (reg 1) s ac), stepF_snd_fire88 hf,
    le_wTop_psi116 (idxOf_ne_zero116 hst h1 h3 h4 h)⟩

theorem vebFree_fire116 {s : Option Term × Option Term} {ac : Term × Term}
    (hf : le (reg 1) ac.1 = true) : VebFree116 (stepF (reg 1) (baseOf 0) s ac) :=
  Or.inr ⟨idxOf (reg 1) s ac, by rw [stepF_fst, if_pos hf], stepF_snd_fire88 hf⟩

/-- ヴェブレン枝の一歩 — 入ってきた値か係数のどちらかが窓の上端以上なら、出る値も。 -/
theorem stepBigNoFire116 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (hf : le (reg 1) ac.1 = false)
    (h1 : inT ac.1 = true) (h2 : lt ac.1 M = true) (h3 : inT ac.2 = true)
    (h4 : lt ac.2 M = true) (h : BigU116 s ∨ le wTop116 ac.2 = true) :
    BigU116 (stepF (reg 1) (baseOf 0) s ac) := by
  have hb : ∃ bse cc, (stepF (reg 1) (baseOf 0) s ac).2 = some (phiNF ac.1 (plus bse cc))
      ∧ inT bse = true ∧ lt bse M = true ∧ inT cc = true ∧ lt cc M = true
      ∧ le wTop116 (plus bse cc) = true := by
    cases hs2 : s.2 with
    | none =>
        refine ⟨baseOf 0, sub1 ac.2, ?_, inT_baseOf 0, ltM_baseOf 0,
          inT_sub1 h3, ltM_sub1 h3 h4, ?_⟩
        · rw [stepF_snd_veb88 hf, hs2]
        · have hc : le wTop116 ac.2 = true := by
            rcases h with ⟨v, hv, _⟩ | hc
            · exfalso; rw [hs2] at hv; exact absurd hv.symm (Option.some_ne_none v)
            · exact hc
          rw [leG_sub1_116 inT_wTop116 isAP_wTop116 h3 lt_one_wTop116 hc]
          exact leG_plus_right116 inT_wTop116 (inT_baseOf 0) h3 hc
    | some v =>
        obtain ⟨hiv, hvM⟩ := hst.2 v hs2
        refine ⟨v, ac.2, ?_, hiv, hvM, h3, h4, ?_⟩
        · rw [stepF_snd_veb88 hf, hs2]
        · rcases h with ⟨v', hv', hbig⟩ | hc
          · have hvv : v' = v := Option.some.inj (hv'.symm.trans hs2)
            rw [hvv] at hbig
            exact leG_plus_left116 inT_wTop116 isAP_wTop116 hiv h3 hbig
          · exact leG_plus_right116 inT_wTop116 hiv h3 hc
  obtain ⟨bse, cc, heq, hib, hbM, hic, hcM, hle⟩ := hb
  exact ⟨_, heq, leG_phiNF116 inT_wTop116 isAP_wTop116 ltM_wTop116 lt_one_wTop116 h1 h2
    (inT_plus hib hic) (lt_plus_M hib hic hbM hcM) hle⟩

/-- **§116.3 の主定理 — 畳み込みは大きいものを落とさない。**  対の列のどこかに窓の上端
    以上の係数があれば、畳み込みの最後の値も窓の上端以上である。強臨界枝が前置きである
    こと (§109.1 の `fireSplit109`) をそのまま仮定に書いてある。 -/
theorem foldU116 : ∀ (l : List (Term × Term)) (s : Option Term × Option Term),
    StInv s →
    (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
    (∀ p ∈ scanSt (reg 1) (baseOf 0) s l, le (reg 1) p.2.1 = true →
        inT (psi (reg 1) (idxOf (reg 1) p.1 p.2)) = true) →
    (∀ ac ∈ l.dropWhile (fun z => le (reg 1) z.1), le (reg 1) ac.1 = false) →
    ((∀ ac ∈ l, le (reg 1) ac.1 = false) ∨ VebFree116 s) →
    (BigU116 s ∨ ∃ ac ∈ l, le wTop116 ac.2 = true) →
    BigU116 (l.foldl (stepF (reg 1) (baseOf 0)) s) := by
  intro l
  induction l with
  | nil =>
      intro s _ _ _ _ _ hbig
      rcases hbig with h | ⟨ac, hac, _⟩
      · exact h
      · cases hac
  | cons ac t ih =>
    intro s hst hall hpsi hds hpre hbig
    obtain ⟨h1, h2, h3, h4⟩ := hall ac (List.Mem.head _)
    have hstep : StInv (stepF (reg 1) (baseOf 0) s ac) :=
      stepF_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0) hst
        ⟨h1, h2, h3, h4⟩ (hpsi (s, ac) (List.Mem.head _))
    refine ih _ hstep (fun a ha => hall a (List.Mem.tail _ ha))
      (fun p hp => hpsi p (List.Mem.tail _ hp)) ?_ ?_ ?_
    · by_cases hf : le (reg 1) ac.1 = true
      · intro x hx
        exact hds x (by rw [List.dropWhile_cons, if_pos hf]; exact hx)
      · intro x hx
        have hall2 : ∀ y ∈ ac :: t, le (reg 1) y.1 = false := by
          intro y hy
          exact hds y (by rw [List.dropWhile_cons, if_neg hf]; exact hy)
        exact hall2 x (List.Mem.tail _ (mem_of_mem_dropWhile116 t x hx))
    · by_cases hf : le (reg 1) ac.1 = true
      · exact Or.inr (vebFree_fire116 hf)
      · refine Or.inl ?_
        intro y hy
        exact hds y (by rw [List.dropWhile_cons, if_neg hf]; exact List.Mem.tail _ hy)
    · by_cases hf : le (reg 1) ac.1 = true
      · rcases hbig with hbg | ⟨ac0, hac0, hle0⟩
        · refine Or.inl (stepBigFire116 hst hf h1 h3 h4 (Or.inr ?_))
          rcases hpre with hno | hvf
          · exact absurd (hno ac (List.Mem.head _)) (by rw [hf]; exact Bool.noConfusion)
          · obtain ⟨v, hv, hbv⟩ := hbg
            rcases hvf with hn | ⟨i, hi1, hi2⟩
            · exfalso; rw [hn] at hv; exact absurd hv.symm (Option.some_ne_none v)
            · refine ⟨i, hi1, psi_ne_zero_of_big116 ?_⟩
              have : v = psi (reg 1) i := Option.some.inj (hv.symm.trans hi2)
              rw [this] at hbv; exact hbv
        · rcases List.mem_cons.mp hac0 with he | ht
          · refine Or.inl (stepBigFire116 hst hf h1 h3 h4 (Or.inl ?_))
            rw [he] at hle0
            exact lt_one_of_leTop116 h3 hle0
          · exact Or.inr ⟨ac0, ht, hle0⟩
      · have hf' : le (reg 1) ac.1 = false := bool_false hf
        rcases hbig with hbg | ⟨ac0, hac0, hle0⟩
        · exact Or.inl (stepBigNoFire116 hst hf' h1 h2 h3 h4 (Or.inl hbg))
        · rcases List.mem_cons.mp hac0 with he | ht
          · refine Or.inl (stepBigNoFire116 hst hf' h1 h2 h3 h4 (Or.inr ?_))
            rw [he] at hle0; exact hle0
          · exact Or.inr ⟨ac0, ht, hle0⟩

/-! ### §116.4 `UpProp113` — 門つきで -/

/-- **§116 の主定理 (1)。**  引数のどこかが窓の上端以上のものを運んでいるなら、
    `ψ₀` の値も窓の上端以上である。§113.6 の `UpProp113` そのもの — ただし畳み込みの
    強臨界枝が本当に 𝔗(M) の項を吐くこと (`PsiIdxOK 0 x`、(G3)) を仮定する。 -/
theorem upPropIn116 {x : Term} (hx : inT x = true) (hxM : lt x M = true)
    (Hp : PsiIdxOK 0 x) (h : (toList x).any upP113 = true) :
    le wTop116 (collapse 0 x) = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  have hM := ltM_toList x hx hxM
  obtain ⟨⟨hrT, hrM⟩, hallOK⟩ :=
    wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList x) hc hd hM
  have hstF : StInv ((wcnf (reg 1) (toList x)).1.foldl (stepF (reg 1) (baseOf 0)) (none, none)) :=
    fold_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0)
      (wcnf (reg 1) (toList x)).1 (none, none) stInv_none hallOK Hp
  have hacc : inT (accW89 x) = true ∧ lt (accW89 x) M = true := by
    unfold accW89
    cases hg : ((wcnf (reg 1) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2 with
    | none => exact ⟨inT_zero, lt_zero_M⟩
    | some v => exact hstF.2 v hg
  obtain ⟨p, hp, hup⟩ := List.any_eq_true.mp h
  have hbig : le wTop116 (plus (accW89 x) (rhoW89 x)) = true := by
    cases hpw : lt p (reg 1) with
    | true =>
        have hlep : le wTop116 p = true := by
          unfold upP113 at hup; rw [hpw] at hup; exact hup
        exact leG_plus_right116 inT_wTop116 hacc.1 hrT
          (wcnf_tailG116 inT_wTop116 isAP_wTop116 (toList x) hc hd p hp hpw hlep)
    | false =>
        have hlep : le wTop116 (wC (reg 1) p) = true := by
          unfold upP113 at hup; rw [hpw] at hup; exact hup
        obtain ⟨ac, hac, hle⟩ :=
          wcnf_coefG116 inT_wTop116 isAP_wTop116 (toList x) hc hd hM p hp hpw hlep
        have hfold := foldU116 (wcnf (reg 1) (toList x)).1 (none, none) stInv_none hallOK Hp
          (fireSplit109 (isSC_reg_succ 0) (inT_reg 1) (show (reg 1).isAP = true from rfl)
            (toList x) hc hd)
          (Or.inr (Or.inl rfl)) (Or.inr ⟨ac, hac, hle⟩)
        obtain ⟨v, hv, hbv⟩ := hfold
        have hav : accW89 x = v := by unfold accW89; rw [hv]; rfl
        rw [hav]
        exact leG_plus_left116 inT_wTop116 isAP_wTop116 (by rw [← hav]; exact hacc.1) hrT hbv
  have hsi : inT (plus (accW89 x) (rhoW89 x)) = true := inT_plus hacc.1 hrT
  have hsM : lt (plus (accW89 x) (rhoW89 x)) M = true :=
    lt_plus_M hacc.1 hrT hacc.2 hrM
  rw [collapse0_raw89]
  refine leG_omegaNF116 inT_wTop116 isAP_wTop116 ltM_wTop116 lt_one_wTop116
    (inT_plus (inT_reg 0) hsi) (lt_plus_M (inT_reg 0) hsi lt_zero_M hsM) ?_
  exact leG_plus_right116 inT_wTop116 (inT_reg 0) hsi hbig

/-! ### §116.5 残っているものに名前をつけ直す -/

/-- 門を全部の項について認めれば `UpProp113` そのもの。門は (G3) で、一般には偽である
    (§64.5 の `#guard`)。だから `UpProp113` を字面どおりに閉じたとは**言わない**。 -/
def PsiIdxAll116 : Prop := ∀ x : Term, inT x = true → lt x M = true → PsiIdxOK 0 x

theorem upProp113_of_all116 (H : PsiIdxAll116) : UpProp113 :=
  fun x hx hxM h => upPropIn116 hx hxM (H x hx hxM) h

/-- **残っているもの — 窓の下端から上端への持ち上げ、一本だけ。**  §113.6 が
    「`UpProp113` プラス下端から上端への帳簿」と書いたうちの、帳簿のほう。 -/
def MidUp116 : Prop := ∀ a : BT, btLe72 1 (BT.D 0 a) = true → BT.isStd (BT.D 0 a) = true →
    BT.lt (bTowG98 0) (BT.D 0 a) = true → le (rawT94 0) (dict (BT.D 0 a)) = true →
    (toList (dict a)).any badP113 = true → (toList (dict a)).any upP113 = true

/-- **§116 の主定理 (2)。**  `WinProp113` は `MidUp116` ひとつに落ちる。
    `UpProp113` はもう要らない — §116.4 が払った。 -/
theorem winProp_of_midUp116 (Hp : PsiIdxOKStd172) (H : MidUp116) : WinProp113 := by
  intro a hb hs hlt hle hbad
  have hba : btLe72 1 a = true := by
    have h : (decide (0 ≤ 1) && btLe72 1 a) = true := hb
    exact ((Bool.and_eq_true _ _).mp h).2
  have hsa : BT.isStd a = true := by
    have h : (BT.isStd a && (BT.GB 0 a).all (fun e => BT.lt e a)) = true := hs
    exact ((Bool.and_eq_true _ _).mp h).1
  obtain ⟨hiA, hAM⟩ := inT_dict_of_std172 Hp a hba hsa
  exact upPropIn116 hiA hAM (Hp 0 a (by omega) hba hs) (H a hb hs hlt hle hbad)

theorem scFirstOne_of_midUp116 (Hp : PsiIdxOKStd172) (H : MidUp116) : SCFirstOne111 :=
  scFirstOne_of_winProp113 Hp (winProp_of_midUp116 Hp H)

/-- そして 326 行の帰結もそのまま乗り換える。 -/
theorem gap_of_midUp116 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (H : MidUp116) :
    GapAtG0_107 := gap_of_winProp113 Hp H2 (winProp_of_midUp116 Hp H)

theorem denseMid107_false_of_midUp116 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (H : MidUp116) : ¬ DictDenseMid107 :=
  denseMid107_false_of_winProp113 Hp H2 (winProp_of_midUp116 Hp H)

theorem cofDenseS1_false_of_midUp116 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (H : MidUp116) : ¬ CofDenseS1 :=
  cofDenseS1_false_of_winProp113 Hp H2 (winProp_of_midUp116 Hp H)

/-! **そして `MidUp116` は偽である。**  §98 の塔の第 1 段がそのまま反例で、`upP113` は
    そこで一度も鳴らない。だから上の還元は空回りで、残っているものを `upP113` の言葉で
    書くことはできない — §116.6 が値そのもので書き直す理由がこれである。 -/

set_option maxRecDepth 40000 in
theorem bTow1_legal116 : (btLe72 1 (bTowG98 1) && BT.isStd (bTowG98 1)
    && BT.lt (bTowG98 0) (bTowG98 1) && le (rawT94 0) (dict (bTowG98 1))) = true := rfl

set_option maxRecDepth 40000 in
theorem bad_bTow1_116 : (toList (dict (bArg98 (bTowG98 0)))).any badP113 = true := rfl

set_option maxRecDepth 40000 in
/-- **窓の上端そのものが `upP113` を鳴らさない。**  値は `φ̄(Γ₀,Γ₀⊕1)` ちょうどである。 -/
theorem notUp_bTow1_116 : (toList (dict (bArg98 (bTowG98 0)))).any upP113 = false := rfl

set_option maxRecDepth 40000 in
theorem midUp116_false : ¬ MidUp116 := by
  intro H
  have h := H (bArg98 (bTowG98 0)) rfl rfl rfl rfl bad_bTow1_116
  rw [notUp_bTow1_116] at h
  exact Bool.noConfusion h

/-- 素朴な形 — §116.6 の条項の結論を `upP113` で書いたもの。**同じ反例で偽。** -/
def ExpUpNaive116 : Prop := ∀ a : BT, btLe72 1 (BT.D 0 a) = true → BT.isStd (BT.D 0 a) = true →
    le (rawT94 0) (dict (BT.D 0 a)) = true →
    (toList (dict a)).any (fun p => !(lt p (reg 1)) && !(lt (wA (reg 1) p) G094)) = true →
      (toList (dict a)).any upP113 = true

set_option maxRecDepth 40000 in
theorem expUpNaive116_false : ¬ ExpUpNaive116 := by
  intro H
  have h := H (bArg98 (bTowG98 0)) rfl rfl rfl rfl
  rw [notUp_bTow1_116] at h
  exact Bool.noConfusion h

/-! ### §116.6 帳簿は帰納法である — 三つの形のうち一つは只 -/

/-- 形 (2) — 桁の指数が `Γ₀` 以上の成分がある場合。§111 の運び手の半分
    (`Gam0Drags111` + `carrier_notStd111`) を 𝔗(M) 側で書いたもの。**証明しない。** -/
def ExpUp116 : Prop := ∀ a : BT, btLe72 1 (BT.D 0 a) = true → BT.isStd (BT.D 0 a) = true →
    le (rawT94 0) (dict (BT.D 0 a)) = true →
    ∀ p ∈ toList (dict a), lt p (reg 1) = false → lt (wA (reg 1) p) G094 = false →
      le wTop116 (dict (BT.D 0 a)) = true

/-- 形 (3) — 桁の係数が窓の下端以上の場合。§113.5 の遺伝の議論の 𝔗(M) 側。
    **証明しない。** -/
def CoefUp116 : Prop := ∀ a : BT, btLe72 1 (BT.D 0 a) = true → BT.isStd (BT.D 0 a) = true →
    le (rawT94 0) (dict (BT.D 0 a)) = true →
    ∀ p ∈ toList (dict a), lt p (reg 1) = false → lt (wA (reg 1) p) G094 = true →
      lt (wC (reg 1) p) (rawT94 0) = false →
      le wTop116 (dict (BT.D 0 a)) = true

/-- **§116 の主定理 (3) — 大きさについての帰納法、実物。**  §113.5 が散文で書いた
    「係数の道は帰納法の仮定そのもの」を定理にしたもの: 三つの形のうち
    **`Ω₁` より下の成分の形は帰納法の仮定が只で片づける**。残るのは (2) と (3)。 -/
theorem winUpAux116 (Hp : PsiIdxOKStd172) (HE : ExpUp116) (HC : CoefUp116) :
    ∀ (n : Nat) (a : BT), BT.size a ≤ n → btLe72 1 (BT.D 0 a) = true →
      BT.isStd (BT.D 0 a) = true → le (rawT94 0) (dict (BT.D 0 a)) = true →
      le wTop116 (dict (BT.D 0 a)) = true := by
  intro n
  induction n with
  | zero =>
      intro a hn _ _ _
      exact absurd hn (by have := size_pos87 a; omega)
  | succ n ih =>
    intro a hn hb hs hle
    have hba : btLe72 1 a = true := by
      have h : (decide (0 ≤ 1) && btLe72 1 a) = true := hb
      exact ((Bool.and_eq_true _ _).mp h).2
    have hsa : BT.isStd a = true := by
      have h : (BT.isStd a && (BT.GB 0 a).all (fun e => BT.lt e a)) = true := hs
      exact ((Bool.and_eq_true _ _).mp h).1
    obtain ⟨hiA, hAM⟩ := inT_dict_of_std172 Hp a hba hsa
    obtain ⟨p, hp, hbad⟩ := coefWinEx113 hiA hAM hle
    have hany : (toList (dict a)).any upP113 = true ∨
        le wTop116 (dict (BT.D 0 a)) = true := by
      cases hpw : lt p (reg 1) with
      | false =>
          unfold badP113 at hbad
          rw [hpw] at hbad
          cases hex : lt (wA (reg 1) p) G094 with
          | false => exact Or.inr (HE a hb hs hle p hp hpw hex)
          | true =>
              refine Or.inr (HC a hb hs hle p hp hpw hex ?_)
              rw [hex, Bool.not_true, Bool.false_or] at hbad
              cases hq : lt (wC (reg 1) p) (rawT94 0) with
              | false => rfl
              | true => rw [hq] at hbad; exact Bool.noConfusion hbad
      | true =>
          refine Or.inl ?_
          have hlep : le (rawT94 0) p = true := by
            unfold badP113 at hbad
            rw [hpw] at hbad
            cases hq : lt p (rawT94 0) with
            | true => rw [hq] at hbad; exact Bool.noConfusion hbad
            | false => exact le_of_not_lt3 (inT_le_fragR _
                (inTL_inT hiA p hp)) (inT_le_fragR _ (inT_rawT98 0)) hq
          obtain ⟨c, hc, hpc⟩ := mem_toList_dict101 Hp hba hsa p hp
          obtain ⟨hAt, hStd, hBt, _⟩ := good_toL77 a hsa hba
          obtain ⟨u, c', hcc⟩ := hAt c hc
          have hbc : btLe72 1 c = true := hBt c hc
          have hsc : BT.isStd c = true := hStd c hc
          subst hcc
          have hu : u = 0 := by
            rcases Nat.eq_zero_or_pos u with h0 | h1
            · exact h0
            · exfalso
              have hu1 : u = 1 := by
                have h := (btLe72_D 1 u c' hbc).1
                omega
              subst hu1
              have hcon := ltW_dictD1_false98 Hp hbc hsc
              rw [← hpc, hpw] at hcon
              exact Bool.noConfusion hcon
          subst hu
          have hsz : BT.size c' ≤ n := by
            have h1 : BT.size (BT.D 0 c') ≤ BT.size a := size_mem_toL87 a _ hc
            have h2 : BT.size (BT.D 0 c') = 1 + BT.size c' := size_D87 0 c'
            omega
          have hIH := ih c' hsz hbc hsc (by rw [← hpc]; exact hlep)
          refine List.any_eq_true.mpr ⟨p, hp, ?_⟩
          unfold upP113
          rw [hpw, hpc]
          exact hIH
    rcases hany with hq | hq
    · exact upPropIn116 hiA hAM (Hp 0 a (by omega) hba hs) hq
    · exact hq

/-- **`WinProp113` は二つの形の条項だけに落ちる。** -/
theorem winProp_of_two116 (Hp : PsiIdxOKStd172) (HE : ExpUp116) (HC : CoefUp116) :
    WinProp113 :=
  fun a hb hs _ hle _ => winUpAux116 Hp HE HC (BT.size a) a (Nat.le_refl _) hb hs hle

theorem gap_of_two116 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HE : ExpUp116)
    (HC : CoefUp116) : GapAtG0_107 :=
  gap_of_winProp113 Hp H2 (winProp_of_two116 Hp HE HC)

theorem denseMid107_false_of_two116 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HE : ExpUp116)
    (HC : CoefUp116) : ¬ DictDenseMid107 :=
  denseMid107_false_of_winProp113 Hp H2 (winProp_of_two116 Hp HE HC)

theorem cofDenseS1_false_of_two116 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HE : ExpUp116)
    (HC : CoefUp116) : ¬ CofDenseS1 :=
  cofDenseS1_false_of_winProp113 Hp H2 (winProp_of_two116 Hp HE HC)

end

/-! ### §116.7 測定 (凍結)

**構成を先に書く。**  母集団は三つ。ひとつは新しく作り、ひとつは §108.6 のものを読み直し、
ひとつは §108.6 の数え上げを一段伸ばして作り直す。

    S  窓のまわりの種 13 個 (`seedR116` — 塔・§108 の族・§111 の族・§113 の第三の運び手・
       小さい証人) を四つの形にはめたもの、52 項。
       s0 = `w` そのもの                 s1 = `ψ₁ w`
       s2 = `Ω^Ω ⊕ ψ₁ w`                s3 = `ψ₁ψ₁ψ₀Ω^Ω ⊕ ψ₁ w`
       **標準性で濾さない。**  測るのは「`ψ₀` の引数として」である。
    E  §108.6 の数え上げ (大きさ 12 までの標準・段 1 以下の項 9992 個) をそのまま読み直す。
    E14 同じ数え上げを大きさ 14 まで伸ばしたもの (58239 個)。§111 が「E は大きさ 14 まで
       同じ答えを出す」と書いた数え上げを、ここでは**係数の形が出るか**を訊くために引く。

**仮説が母集団に見えていること。**  §116.4 の門は S の 52/52 で成り立ち、E では 9992 中
9944 で成り立ち **48 項で破れる** — 空振りではない。破れる 48 項は**どれも `ψ₀` を載せると
標準でなくなる** (0/48) ので `PsiIdxOKStd172` とは矛盾しない。そしてその 48 項でも
`UpProp113` の含意は 48/48 で成り立つ (前提は 7 項で発火) — **門は証明の側の制限であって、
測った範囲では言明の側の制限ではない。** -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

set_option maxRecDepth 200000

/-- §116.4 の門を決定可能な形で。 -/
def gateB116 (x : Term) : Bool :=
  (scanSt (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
      (wcnf (reg 1) (toList x)).1).all
    (fun p => !(le (reg 1) p.2.1) || inT (psi (reg 1) (idxOf (reg 1) p.1 p.2)))

/-- **判定器は門を出す。**  だから `upPropIn116` は具体的な項の上では仮定なしで使える。 -/
theorem psiIdxOK_of_gateB116 {x : Term} (h : gateB116 x = true) : PsiIdxOK 0 x := by
  intro p hp hfire
  have hq := List.all_eq_true.mp h p hp
  rw [show le (reg 1) p.2.1 = true from hfire, Bool.not_true, Bool.false_or] at hq
  exact hq

/-- 三つの形を別々に読む道具。 -/
def expF116 (z : BT) : Bool :=
  (toList (dict z)).any (fun p => !(lt p (reg 1)) && !(lt (wA (reg 1) p) G094))
def coefF116 (z : BT) : Bool :=
  (toList (dict z)).any (fun p => !(lt p (reg 1)) && lt (wA (reg 1) p) G094
      && !(lt (wC (reg 1) p) (rawT94 0)))
def tailF116 (z : BT) : Bool :=
  (toList (dict z)).any (fun p => lt p (reg 1) && !(lt p (rawT94 0)))
/-- 「`ψ₀` の正しい引数で、値が窓の下端以上」 — 二つの条項が訊かれる場所。 -/
def base116 (z : BT) : Bool :=
  btLe72 1 (BT.D 0 z) && BT.isStd (BT.D 0 z) && le (rawT94 0) (dict (BT.D 0 z))
def conc116 (z : BT) : Bool := le (dict (bTowG98 1)) (dict (BT.D 0 z))
def upOK116 (z : BT) : Bool :=
  !((toList (dict z)).any upP113) || le (dict (bTowG98 1)) (collapse 0 (dict z))

def seedR116 : List BT :=
  [ bTowG98 0, bTowG98 1, bTowG98 2, bWin108 1, bWin108 2, cWin111 cCar111,
    cWin111 (BT.D 0 BT.zero), bWinOO108 1, smallB108, BT.D 0 (BT.Om 1),
    BT.D 0 BT.zero, cCoef113 (bWin108 1), cJump113 ]
def r1_116 : List BT := seedR116.map fun w => BT.D 1 w
def r2_116 : List BT := seedR116.map fun w => BT.sum bOO94 (BT.D 1 w)
def r3_116 : List BT := seedR116.map fun w => BT.sum dgG0_108 (BT.D 1 w)
def popR116 : List BT := seedR116 ++ r1_116 ++ r2_116 ++ r3_116

#guard popR116.length == 52

/-! **門は S の 52/52 で成り立つ。**  E の側は 9944/9992 で、破れる 48 項は `ψ₀` を
    載せると標準でない (上の前書き)。ここでは E の 20 項に 1 項の切片で確かめる。 -/
#eval (popR116.countP fun z => gateB116 (dict z),
       (everyB94 20 allStd108).countP fun z => gateB116 (dict z),
       (everyB94 20 allStd108).length)
#guard (popR116.countP fun z => gateB116 (dict z)) == 52
#guard (everyB94 20 allStd108).all fun z => gateB116 (dict z) || !(BT.isStd (BT.D 0 z))

/-! **`UpProp113` は S でも成り立ち、前提は空振りではない** — 52 項中 12 項で発火。 -/
#eval (popR116.countP fun z => (toList (dict z)).any upP113, popR116.countP upOK116)
#guard (popR116.countP fun z => (toList (dict z)).any upP113) == 12
#guard (popR116.countP upOK116) == 52

/-! **三つの形は S ではどれも見えている** — 指数 26・係数 27・尾 9。 -/
#eval (popR116.countP expF116, popR116.countP coefF116, popR116.countP tailF116)
#guard (popR116.countP expF116) == 26
#guard (popR116.countP coefF116) == 27
#guard (popR116.countP tailF116) == 9

/-! **しかし S は二つの条項を試せない。**  52 項のうち `ψ₀` の正しい引数になるのは 7 項、
    窓に入るのは 24 項、**その両方は 0 項**。§111 と §113 が名指しした種の問題が、
    ここでも同じ形で出る — 危ない形は標準でないから、標準性で濾すと消える。 -/
#eval (popR116.countP fun z => bgood94 (BT.D 0 z),
       popR116.countP fun z => inWin108 (dict (BT.D 0 z)),
       popR116.countP fun z => inWin108 (dict (BT.D 0 z)) && bgood94 (BT.D 0 z),
       popR116.countP base116)
#guard (popR116.countP fun z => bgood94 (BT.D 0 z), popR116.countP base116,
        popR116.countP fun z => inWin108 (dict (BT.D 0 z)),
        popR116.countP fun z => inWin108 (dict (BT.D 0 z)) && bgood94 (BT.D 0 z))
    == (7, 0, 24, 0)

/-! **E の読み直し (1) — 条項が訊かれる場所は 2495 項で、そこでは指数の形しか鳴らない。**
    `ψ₀` の正しい引数で値が窓の下端以上のものは 2495 項。指数の節は **2495/2495**、
    係数の節は **0**、尾の節は **3**。結論は 2495/2495 で成り立つ。 -/
#guard (fun L => (L.length, L.countP expF116, L.countP coefF116, L.countP tailF116,
          L.countP fun z => !(conc116 z))) (allStd108.filter base116)
    == (2495, 2495, 0, 3, 0)

/-! **E の読み直し (2) — §113 が名指しした `upP113` は、窓を越える項のほとんどで鳴らない。**
    値が窓の上端以上になる正しい `ψ₀` 引数は 2495 項で、そのうち `upP113` が鳴るのは
    **6 項**。`UpProp113` は真で (§116.4)、しかも**十分条件でしかない** — 2489 項は
    `upP113` を一度も鳴らさずに窓を越える。**だから §116.6 の二つの条項は
    `upP113` ではなく値そのもので書いてある。** -/
#guard (fun L => (L.length, L.countP fun z => (toList (dict z)).any upP113))
    (allStd108.filter fun z => BT.isStd (BT.D 0 z) && conc116 z) == (2495, 6)

/-! **E14 — 一段伸ばすと係数の形が出る。**  大きさ 14 まで 58239 項。条項が訊かれる場所は
    16425 項で、指数の節は **16425/16425**、**係数の節は 11 項** (大きさ 12 では 0 項)、
    尾の節は 43 項。結論は 16425/16425 で成り立つ。**係数の条項 `CoefUp116` は
    空振りではない — 大きさ 12 の母集団がそれを見られなかっただけである。** -/
def bigE116 : List BT := (lvBT108 13).flatten

#guard (fun L => (L.length, L.countP expF116, L.countP coefF116, L.countP tailF116,
          L.countP fun z => !(conc116 z))) (bigE116.filter base116)
    == (16425, 16425, 11, 43, 0)

/-! **段の正直さ。**  §116 は新しい項をひとつも段 1 の外に出さない。 -/
#guard popR116.all fun z => btLe72 1 z
#guard btLe72 1 (bTowG98 1) && !(btLe72 0 (bTowG98 1))

end

end Evidence.Region
