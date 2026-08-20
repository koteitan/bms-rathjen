import Evidence.RegionNext6

/-
Evidence/RegionNext7.lean — ROW 326'S REMAINING HYPOTHESES, FOURTH PART (§119-)

Split out of `RegionNext6` at 12500 lines.  Section numbers are not in file order —
sections were appended as their agents finished.
-/

namespace Evidence.Region

open BMS

/-! ## §119 NEITHER OF §116'S TWO CLAUSES IS A CLAUSE — WHAT IS LEFT IS ONE SHAPE OF PAIR
       LIST, AND THE FOLD READS NOTHING ELSE

§116 left row 326's gap resting on three named things: `CoefUp116`, `ExpUp116`, and — named
by §113 and not removed by §116 — the BRIDGE from the 𝔗(M)-side exponent clause to §111's
Buchholz-side `ψ₁(ψ₁ z ⊕ …)` shape.

**§119 removes all three.**  `CoefUp116` is not an independent clause: it is the induction
hypothesis §113.5 described in prose, and §119.1 runs it.  The bridge is a theorem (§119.3),
proved from §104.2's closed form for the `ψ₁` image and nothing else — no new gate, no
surjective half of §96's bridge.  And `ExpUp116` reduces to ONE clause about the SHAPE OF THE
PAIR LIST (§119.4–§119.5):

    `TightUp119` :  if every base-`Ω₁` pair is TAME — a firing pair is exactly `(Ω₁, 1)`,
                    a Veblen pair has exponent at most `Γ₀` — then a value at or above the
                    window's bottom is at or above its top.

`gap_of_tight119` : `PsiIdxOKStd172 + DictLtA74 + TightUp119 ⟹ GapAtG0_107`.  **`ExpUp116`,
`CoefUp116` and `Gam0Drags111` are all off the road.**

  §119.1  **THE COEFFICIENT SHAPE IS THE INDUCTION HYPOTHESIS.**  §116.6 discharged the
          sub-`Ω₁` shape by the size induction and put the coefficient shape outside as
          `CoefUp116`.  It did not have to.  §104.2's `wC_dict_D1_104` says the coefficient
          the base-`Ω₁` decomposition hands to the fold is `ω^(lo (dict c))` — the `ω`-power
          of the sub-`Ω₁` part of what sits inside the `ψ₁` — and §104.3's
          `mem_toList_loW_dict101` names each of ITS components as `dict (ψ₀ d)` with `ψ₀ d`
          a component of `c`.  So a coefficient at or above the window's bottom contains a
          strictly smaller standard `ψ₀` whose value is at or above the bottom; the induction
          hypothesis lifts it to the TOP, `ω^·` and the head both keep it there (§113.1,
          §116.1), and the component then fires `upP113`, which §116.4 already pays for.
          `coefUpStep119`; `coefUp116_of_tight119` derives `CoefUp116` outright.

  §119.2  **`Γ₀` IS AN ε-NUMBER, AND `Ω₁` DIVIDES THE `ψ₁` IMAGE EXACTLY.**  Three small
          facts the bridge needs and the repository did not have: `omegaNF G094 = G094` by
          `rfl`, hence `ltG0_omegaNF119` and its converse from §79's strict monotonicity of
          `ω^·`; `subAP_plusW119`, which is §106.2's `subAP_plusW106` **with its `g < Ω₁`
          hypothesis removed** — the hypothesis was never needed, since when `g`'s head passes
          `Ω₁` the sum `Ω₁ ⊕ g` simply IS `g`; and `divAP_dictD1_119` :
          `divAP Ω₁ (dict (ψ₁ e)) = ω^(dict e)`, the exponent-side mirror of §104.2's
          coefficient-side `wC_dict_D1_104`.

  §119.3  **THE BRIDGE.**  `expBridge119` : if a component `p` of `dict a` at or above `Ω₁`
          has base-`Ω₁` exponent at or above `Γ₀`, then `a` has a component `ψ₁ c`, `c` has a
          component `ψ₁ e`, and `Γ₀ ≤ dict e` — with the exponent's LEADING term named
          exactly, `toList (wA Ω₁ p) = ω^(dict e) :: t`.  §113 asked for the tie between its
          𝔗(M)-side exponent clause and §111's shape; this is it, with no restriction on
          either tail.  **The `Ω₁` summand of `logOm p` is what would break it, and it is the
          one case the exponent cannot use: `divAP Ω₁ Ω₁ = 1`, and `1 < Γ₀`.**

  §119.4  **ONE PAIR THAT IS NOT TAME IS ENOUGH, AND STANDARDNESS IS NOT USED.**
          `bigP119` names the negation of tame, and `expUpBig119` : if any base-`Ω₁` pair is
          not tame the `ψ₀` value is at or above the window's top.  Three step lemmas, three
          different reasons.  *Veblen with exponent above `Γ₀`* (`stepBigExp119`): the
          arithmetic is §117.1's `lt_phi_vT117` and §100.1's `lt_phi_of_le100`
          (`le_wTop_phi119`) carried through all five branches of `phiNF`
          (`le_wTop_phiNF119`) — the two branches that return a strongly critical term are
          settled by `le_wTop_SC119`, which is §116.3's `lt_wTop_psi116` read off the three
          shapes of `SC`.  *Firing with coefficient above `1`*: §116.3's `stepBigFire116`
          unchanged.  *Firing with exponent above `Ω₁`* (`stepBigFireExp119`): the collapse
          index cannot be `0`, because `Ω₁ · (a ⊖ Ω₁)` is not `0` and `ω^(that ⊕ …)` is not
          `1` (`dd_ne_one_exp119`) — the exponent-side companion of §116.3's `dd_ne_one116`,
          which could only see the coefficient.  `wcnf_coef_ne_zero119` supplies the one
          side condition, and `foldB119` is §116.3's fold with the three triggers in place of
          one.

  §119.5  **AND THAT IS THE WHOLE OF `ExpUp116`.**  `wcnf_expG119` puts a component's
          exponent into the pair list — **the merge never changes an exponent**, so the
          exponent side is cheaper than §116.2's coefficient side, which had to survive a
          `plus`.  `expUp116_of_tight119` is then two lines: either some pair is not tame
          (§119.4) or every pair is tame (`TightUp119`).  `tameExp119` says what tameness
          leaves: a digit exponent at or above `Γ₀` is EXACTLY `Γ₀` or EXACTLY `Ω₁`.  And at
          `Γ₀` the bridge pays off: `carrierOfExpG0_119` shows the carrier's value is exactly
          `Γ₀`, so with `Gam0Drags111` standardness forces `Ω^Ω < a`
          (`carrierAbove119`) — **§111's `carrier_notStd111` with the leading-component
          restriction gone**, at both levels and every tail.

  §119.6  **WHAT ROW 326 NOW RESTS ON.**  `winUpAux119` re-runs §116.6's induction with the
          coefficient shape inside; `gap_of_tight119` reaches `GapAtG0_107` from
          `PsiIdxOKStd172 + DictLtA74 + TightUp119`, and the four falsity corollaries come
          with it.

WHAT IS **NOT** CLAIMED.  **`TightUp119` is NOT proved and NOT refuted, and neither are
`ExpUp116`, `SCFirstOne111`, `SCFirst108` or `GapAtG0_107`.**  `PsiIdxOKStd172` and
`DictLtA74` are used, not proved; `Gam0Drags111` is used only in §119.5's shape account and
is **not** on the road to `GapAtG0_107`.  `DictDenseMid107`, `DictDenseMid102`,
`DictDenseHi94`, `DictDense85`, `CofDenseS1` and row 326's certificate are exactly where §116
left them.  §119 does not touch §103's hole and does not reach `FoldSkips108`.
**`TightUp119` is not vacuous and its standardness is load-bearing**: §119.7 measures the
TAME condition holding on 13 of S's 30 terms while the conclusion fails on 11 of those 13, so
tameness alone does not carry the conclusion; and S contains **2** places where the clause is
asked in full (legal `ψ₀` argument, value at or above the bottom, all pairs tame), where it
holds.

**WHERE §119 STOPPED, PRECISELY, AND WHAT MOVED.**  All three of §116's items are **removed**,
not moved, and what replaces them is one clause with a decidable hypothesis about the pair
list the fold actually reads.  The residue did shrink, and the measurement says by how much:
the clause is asked at **1** of E's 2495 places and **1** of E14's 16425, where §116's two
clauses were asked at all of them.  **That one place is `bTowG98 1` itself** — the window's
top — and its pair list is `[(Ω₁,1), (Γ₀,1)]`.  So what is left is exactly: a fold that fires
once with the smallest possible index, comes back down to `ψ_{Ω₁}(0) = Γ₀`, and then meets a
Veblen digit of exponent at most `Γ₀`.  `bTowG98 0 = ψ₀(Ω^Ω)` is the value `Γ₀` and
`bTowG98 1` is the top; **every unresolved case sits between them with the collapse index at
`0`, and standardness is the only thing that can decide it** — §119.5 says where it would
enter (`Ω^Ω < a`) and does not close the step from there to a firing digit.

**AND THE OVERPAYMENT LEDGER — TWO ENTRIES, AND THE SECOND IS §119'S OWN.**  The eleventh is
§116's: `CoefUp116` was named as one of two clauses left and it is not a clause at all; the
same induction §116.6 already ran for the sub-`Ω₁` shape pays it, one `wC` identity later.
**The twelfth is §119's.**  §119 first split `ExpUp116` by the VALUE of the bridge's subterm
`e` — `dict e = Γ₀`, `Γ₀ < dict e < Ω₁`, `Ω₁ ≤ dict e` — proved the middle case, and named the
other two.  Then it measured: **the middle case fires on 0 of E's 2495 legal places and 3 of
E14's 16425.**  The split was by the shape the BRIDGE produces, and the fold does not read
that shape — it reads the pair list.  Re-split by the pair list and the same three step
lemmas close 2494 of the 2495.  **Measure the split, not just the clause: a split that is
sound and honest can still put all of the population on one side.** -/

/-! ### §119.1 係数の形は帰納法の仮定そのもの -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- 窓の下端は `0` ではない。 -/
theorem lt_zero_rawT119 : lt zero (rawT94 0) = true := lt_zero_gT113 zero

/-- **§119.1 の主定理 — 係数の形は帰納法の仮定そのもの。**  `ψ₁` の中の標準な項の
    `Ω₁` より下の成分が窓の下端以上なら、その成分は `ψ₀` の像で、大きさが小さい。 -/
theorem coefUpStep119 (Hp : PsiIdxOKStd172) {n : Nat}
    (ih : ∀ d : BT, BT.size d ≤ n → btLe72 1 (BT.D 0 d) = true →
      BT.isStd (BT.D 0 d) = true → le (rawT94 0) (dict (BT.D 0 d)) = true →
      le wTop116 (dict (BT.D 0 d)) = true)
    {a : BT} (hn : BT.size a ≤ n + 1) (hba : btLe72 1 a = true) (hsa : BT.isStd a = true)
    {p : Term} (hp : p ∈ toList (dict a)) (hpw : lt p (reg 1) = false)
    (hcoef : lt (wC (reg 1) p) (rawT94 0) = false) :
    upP113 p = true := by
  obtain ⟨hiA, hAM⟩ := inT_dict_of_std172 Hp a hba hsa
  have hip : inT p = true := inTL_inT hiA p hp
  have hphi : p ∈ toList (hiW89 (dict a)) := by
    rw [toList_hiW89 hiA]
    refine List.mem_filter.mpr ⟨hp, ?_⟩
    show (!lt p (reg 1)) = true
    rw [hpw]; rfl
  obtain ⟨c, hmem, hpe⟩ := mem_toList_hiW_dict101 Hp hba hsa p hphi
  have hgood : GoodL77 (BT.toL a) := good_toL77 a hsa hba
  have hb1 : btLe72 1 (BT.D 1 c) = true := hgood.2.2.1 _ hmem
  have hs1 : BT.isStd (BT.D 1 c) = true := hgood.2.1 _ hmem
  have hbc : btLe72 1 c = true := (btLe72_D 1 1 c hb1).2
  have hsc : BT.isStd c = true := isStd_of_D hs1
  obtain ⟨hiC, hCM⟩ := inT_dict_of_std172 Hp c hbc hsc
  have hwc : wC (reg 1) p = omegaNF (loW89 (dict c)) := by
    rw [hpe]; exact wC_dict_D1_104 Hp hbc hsc
  have hiLo : inT (loW89 (dict c)) = true := inT_loW89 hiC
  have hLoM : lt (loW89 (dict c)) M = true := ltM_loW112 hiC hCM
  have hge : le (rawT94 0) (wC (reg 1) p) = true :=
    le_of_not_lt3 (inT_le_fragR _ (inT_wC hip)) (inT_le_fragR _ (inT_rawT98 0)) hcoef
  have hgeLo : le (rawT94 0) (loW89 (dict c)) = true := by
    cases hq : lt (loW89 (dict c)) (rawT94 0) with
    | false => exact le_of_not_lt3 (inT_le_fragR _ hiLo) (inT_le_fragR _ (inT_rawT98 0)) hq
    | true =>
        exfalso
        have hlt : lt (omegaNF (loW89 (dict c))) (rawT94 0) = true :=
          lt_omegaNF113 (R := zero) (inT_rawT98 0) hiLo hLoM hq
        rw [hwc, not_le_of_lt113 (inT_rawT98 0) (inT_omegaNF hiLo) hlt] at hge
        exact Bool.noConfusion hge
  cases hl : toList (loW89 (dict c)) with
  | nil =>
      exfalso
      rw [toList_eq_nil _ hl] at hgeLo
      have hz : lt zero (rawT94 0) = true := lt_zero_rawT119
      rw [le_zero_eq116 hgeLo, lt_irrefl] at hz
      exact Bool.noConfusion hz
  | cons q s =>
      have hqmem : q ∈ toList (loW89 (dict c)) := by rw [hl]; exact List.Mem.head _
      have hgeq : le (rawT94 0) q = true :=
        le_hd_of_le109 (inT_rawT98 0) (show (rawT94 0).isAP = true from rfl) hiLo hl hgeLo
      obtain ⟨d, hd, hqe⟩ := mem_toList_loW_dict101 Hp hbc hsc q hqmem
      have h1 : BT.size (BT.D 1 c) ≤ BT.size a := size_mem_toL87 a _ hmem
      have h2 : BT.size (BT.D 1 c) = 1 + BT.size c := size_D87 1 c
      have h3 : BT.size (BT.D 0 d) ≤ BT.size c := size_mem_toL87 c _ hd
      have h4 : BT.size (BT.D 0 d) = 1 + BT.size d := size_D87 0 d
      have hsz : BT.size d ≤ n := by omega
      have hgoodc : GoodL77 (BT.toL c) := good_toL77 c hsc hbc
      have hIH := ih d hsz (hgoodc.2.2.1 _ hd) (hgoodc.2.1 _ hd) (by rw [← hqe]; exact hgeq)
      have hqTop : le wTop116 q = true := by rw [hqe]; exact hIH
      have hLoTop : le wTop116 (loW89 (dict c)) = true :=
        le_of_le_hd109 inT_wTop116 hiLo hl hqTop
      show upP113 p = true
      unfold upP113
      rw [hpw, hwc]
      exact leG_omegaNF116 inT_wTop116 isAP_wTop116 ltM_wTop116 lt_one_wTop116 hiLo hLoM hLoTop

end

/-! ### §119.2 `Γ₀` は ε 数、`Ω₁` は `ψ₁` の像をちょうど割る -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

theorem toList_G0_119 : toList G094 = [G094] := rfl

theorem omegaNF_G0_119 : omegaNF G094 = G094 := rfl
theorem divAP_W_W_119 : divAP (reg 1) (reg 1) = TM.Term.one := rfl
theorem le_G0_one_false119 : le G094 TM.Term.one = false := by decide
theorem isAP_G0_119 : G094.isAP = true := rfl
theorem toList_W_119 : toList (reg 1) = [reg 1] := rfl

/-- `Γ₀` は ε 数 — `x < Γ₀` なら `ω^x < Γ₀`。 -/
theorem ltG0_omegaNF119 {x : Term} (hx : inT x = true) (h : lt x G094 = true) :
    lt (omegaNF x) G094 = true := by
  have hm := lt_omegaNF_inT79 hx inT_G094_102 h
  rw [omegaNF_G0_119] at hm
  exact hm

/-- 逆向き — `ω^x` が `Γ₀` 以上なら `x` も。 -/
theorem leG0_of_leG0_omegaNF119 {x : Term} (hx : inT x = true)
    (h : le G094 (omegaNF x) = true) : le G094 x = true := by
  cases hq : lt x G094 with
  | false => exact le_of_not_lt3 (inT_le_fragR _ hx) (inT_le_fragR _ inT_G094_102) hq
  | true =>
      exfalso
      have hlt := ltG0_omegaNF119 hx hq
      rw [not_le_of_lt113 inT_G094_102 (inT_omegaNF hx) hlt] at h
      exact Bool.noConfusion h

/-- `subAP (Ω₁) (Ω₁ ⊕ g) = g` — §106.2 の `subAP_plusW106` から `g < Ω₁` の仮定を外したもの。 -/
theorem subAP_plusW119 {g : Term} (hg : inT g = true) :
    subAP (reg 1) (plus (reg 1) g) = g := by
  cases hl : toList g with
  | nil =>
      rw [plus_nil hl, toList_eq_nil g hl,
        subAP_cons (reg 1) (reg 1) (reg 1) [] toList_W_119, if_pos (by rfl)]
      rfl
  | cons b1 r =>
      have htl : toList (plus (reg 1) g)
          = (toList (reg 1)).filter (fun a => le b1 a) ++ toList g :=
        toList_plus_inT (inT_reg 1) hg hl
      by_cases hb : le b1 (reg 1) = true
      · have hf : (toList (reg 1)).filter (fun a => le b1 a) = [reg 1] := by
          rw [toList_W_119, List.filter_cons_of_pos (by rw [hb])]
          rfl
        rw [subAP_cons (reg 1) _ (reg 1) (toList g) (by rw [htl, hf]; rfl),
          if_pos (by rfl), inT_ofList_toList g hg]
      · have hb' : le b1 (reg 1) = false := bool_false hb
        have hf : (toList (reg 1)).filter (fun a => le b1 a) = [] := by
          rw [toList_W_119, List.filter_cons_of_neg (by rw [hb']; exact Bool.noConfusion)]
          rfl
        have hpe : plus (reg 1) g = g := by
          have h1 : toList (plus (reg 1) g) = toList g := by rw [htl, hf]; rfl
          rw [← inT_ofList_toList (plus (reg 1) g) (inT_plus (inT_reg 1) hg), h1,
            inT_ofList_toList g hg]
        have hne : (b1 == reg 1) = false := by
          cases hc : (b1 == reg 1) with
          | false => rfl
          | true =>
              exfalso
              rw [eq_of_beq hc, le_self] at hb'
              exact Bool.noConfusion hb'
        rw [hpe, subAP_cons (reg 1) g b1 r hl, if_neg (by rw [hne]; exact Bool.noConfusion)]

/-- **`ψ₁` の像を `Ω₁` で割ると `ω^(引数の像)` — 閉じた形。** -/
theorem divAP_dictD1_119 (Hp : PsiIdxOKStd172) {e : BT} (hb : btLe72 1 e = true)
    (hs : BT.isStd e = true) :
    divAP (reg 1) (dict (BT.D 1 e)) = omegaNF (dict e) := by
  show omegaNF (subAP (reg 1) (logOm (dict (BT.D 1 e)))) = omegaNF (dict e)
  rw [logOm_dict_D1_104 Hp hb hs, subAP_plusW119 (inT_dict_of_std172 Hp e hb hs).1]

/-- `Ω₁ ⊕ g` の成分は `Ω₁` か `g` の成分。 -/
theorem mem_toList_plusW119 {g : Term} (hg : inT g = true) :
    ∀ q ∈ toList (plus (reg 1) g), q = reg 1 ∨ q ∈ toList g := by
  cases hl : toList g with
  | nil =>
      intro q hq
      rw [plus_nil hl, toList_W_119] at hq
      exact Or.inl (List.mem_singleton.mp hq)
  | cons b1 r =>
      intro q hq
      rw [toList_plus_inT (inT_reg 1) hg hl] at hq
      rcases List.mem_append.mp hq with h | h
      · have h1 : q ∈ [reg 1] := by
          rw [← toList_W_119]; exact (List.mem_filter.mp h).1
        exact Or.inl (List.mem_singleton.mp h1)
      · rw [hl] at h
        exact Or.inr h

/-- `wA` の成分列 — 定義を `toList` で開いたもの。 -/
theorem toList_wA119 {p : Term} :
    toList (wA (reg 1) p)
      = (((toList (logOm p)).filter (fun q => !lt q (reg 1))).map (divAP (reg 1))) := by
  refine toList_ofList _ ?_
  intro x hx
  obtain ⟨q, _, hxq⟩ := List.mem_map.mp hx
  rw [← hxq]
  exact isAP_divAP _ _

end

/-! ### §119.3 橋 — §113 が名指ししたもの -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- **§119.3 の主定理 — §113 が名指しした指数の橋。** -/
theorem expBridge119 (Hp : PsiIdxOKStd172) {a : BT} (hba : btLe72 1 a = true)
    (hsa : BT.isStd a = true) {p : Term} (hp : p ∈ toList (dict a))
    (hpw : lt p (reg 1) = false) (hex : lt (wA (reg 1) p) G094 = false) :
    ∃ c e : BT, ∃ t : List Term, BT.D 1 c ∈ BT.toL a ∧ BT.D 1 e ∈ BT.toL c ∧
      btLe72 1 e = true ∧ BT.isStd e = true ∧
      toList (wA (reg 1) p) = omegaNF (dict e) :: t ∧ le G094 (dict e) = true := by
  obtain ⟨hiA, hAM⟩ := inT_dict_of_std172 Hp a hba hsa
  have hip : inT p = true := inTL_inT hiA p hp
  have hiwA : inT (wA (reg 1) p) = true :=
    inT_wA109 (inT_reg 1) (show (reg 1).isSC = true from rfl) hip
  have hge : le G094 (wA (reg 1) p) = true :=
    le_of_not_lt3 (inT_le_fragR _ hiwA) (inT_le_fragR _ inT_G094_102) hex
  have hphi : p ∈ toList (hiW89 (dict a)) := by
    rw [toList_hiW89 hiA]
    refine List.mem_filter.mpr ⟨hp, ?_⟩
    show (!lt p (reg 1)) = true
    rw [hpw]; rfl
  obtain ⟨c, hmem, hpe⟩ := mem_toList_hiW_dict101 Hp hba hsa p hphi
  have hgood : GoodL77 (BT.toL a) := good_toL77 a hsa hba
  have hb1 : btLe72 1 (BT.D 1 c) = true := hgood.2.2.1 _ hmem
  have hs1 : BT.isStd (BT.D 1 c) = true := hgood.2.1 _ hmem
  have hbc : btLe72 1 c = true := (btLe72_D 1 1 c hb1).2
  have hsc : BT.isStd c = true := isStd_of_D hs1
  obtain ⟨hiC, hCM⟩ := inT_dict_of_std172 Hp c hbc hsc
  have hlog : logOm p = plus (reg 1) (dict c) := by
    rw [hpe]; exact logOm_dict_D1_104 Hp hbc hsc
  have hwa := toList_wA119 (p := p)
  cases hfl : (toList (logOm p)).filter (fun q => !lt q (reg 1)) with
  | nil =>
      exfalso
      have hz : wA (reg 1) p = zero := toList_eq_nil _ (by rw [hwa, hfl]; rfl)
      rw [hz] at hge
      have hz0 : lt zero G094 = true := by decide
      rw [le_zero_eq116 hge, lt_irrefl] at hz0
      exact Bool.noConfusion hz0
  | cons h t =>
      have hhm : h ∈ (toList (logOm p)).filter (fun q => !lt q (reg 1)) := by
        rw [hfl]; exact List.Mem.head _
      have hhl : h ∈ toList (logOm p) := (List.mem_filter.mp hhm).1
      have hhw : lt h (reg 1) = false := by
        have hb := (List.mem_filter.mp hhm).2
        cases hq : lt h (reg 1) with
        | false => rfl
        | true => rw [hq] at hb; exact Bool.noConfusion hb
      have hwa2 : toList (wA (reg 1) p) = divAP (reg 1) h :: t.map (divAP (reg 1)) := by
        rw [hwa, hfl]; rfl
      have hgeh : le G094 (divAP (reg 1) h) = true :=
        le_hd_of_le109 inT_G094_102 isAP_G0_119 hiwA hwa2 hge
      rw [hlog] at hhl
      rcases mem_toList_plusW119 hiC h hhl with hcase | hcase
      · exfalso
        rw [hcase, divAP_W_W_119, le_G0_one_false119] at hgeh
        exact Bool.noConfusion hgeh
      · have hhi : h ∈ toList (hiW89 (dict c)) := by
          rw [toList_hiW89 hiC]
          refine List.mem_filter.mpr ⟨hcase, ?_⟩
          show (!lt h (reg 1)) = true
          rw [hhw]; rfl
        obtain ⟨e, hmem2, hhe⟩ := mem_toList_hiW_dict101 Hp hbc hsc h hhi
        have hgoodc : GoodL77 (BT.toL c) := good_toL77 c hsc hbc
        have hbe1 : btLe72 1 (BT.D 1 e) = true := hgoodc.2.2.1 _ hmem2
        have hse1 : BT.isStd (BT.D 1 e) = true := hgoodc.2.1 _ hmem2
        have hbe : btLe72 1 e = true := (btLe72_D 1 1 e hbe1).2
        have hse : BT.isStd e = true := isStd_of_D hse1
        have hdiv : divAP (reg 1) h = omegaNF (dict e) := by
          rw [hhe]; exact divAP_dictD1_119 Hp hbe hse
        refine ⟨c, e, t.map (divAP (reg 1)), hmem, hmem2, hbe, hse, ?_, ?_⟩
        · rw [hwa2, hdiv]
        · refine leG0_of_leG0_omegaNF119 (inT_dict_of_std172 Hp e hbe hse).1 ?_
          rw [← hdiv]; exact hgeh

end

/-! ### §119.4 おとなしくない対はひとつで足りる -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- `Γ₀` より上の強臨界項は窓の上端以上。 -/
theorem le_wTop_SC119 {S : Term} (hSC : S.isSC = true) (hg : lt G094 S = true) :
    le wTop116 S = true := by
  cases S with
  | zero => exact Bool.noConfusion hSC
  | add _ _ => exact Bool.noConfusion hSC
  | omg _ => exact Bool.noConfusion hSC
  | phi _ _ => exact Bool.noConfusion hSC
  | M => exact le_of_lt94 ltM_wTop116
  | psi k c =>
      refine le_of_lt94 ?_
      show lt (phi G094 (plus G094 TM.Term.one)) (psi k c) = true
      refine lt_phi_psi_of hg ?_
      rw [show plus G094 TM.Term.one = add G094 TM.Term.one from rfl,
        lt_add_ap102 _ _ (show (psi k c).isAP = true from rfl)]
      exact hg
  | Z d =>
      refine le_of_lt94 ?_
      show lt (phi G094 (plus G094 TM.Term.one)) (Z d) = true
      refine lt_phi_Z_of hg ?_
      rw [show plus G094 TM.Term.one = add G094 TM.Term.one from rfl,
        lt_add_ap102 _ _ (show (Z d).isAP = true from rfl)]
      exact hg

/-- 指数が `Γ₀` より上なら `φ̄` の値は窓の上端以上 — 第 2 引数は自由。 -/
theorem le_wTop_phi119 {A Y : Term} (hiA : inT A = true) (hiY : inT Y = true)
    (hAM : lt A M = true) (hYM : lt Y M = true) (hg : lt G094 A = true) :
    le wTop116 (phi A Y) = true := by
  have hphiT : inT (phi A Y) = true := inT_phiT117 hiA hiY hAM hYM
  have hG0 : lt G094 (phi A Y) = true :=
    lt_phi_of_le100 G094.deg G094 A Y (Nat.le_refl _) inT_G094_102 (by decide) hphiT
      (Or.inl (le_of_lt94 hg))
  refine le_of_lt94 ?_
  show lt (phi G094 (plus G094 TM.Term.one)) (phi A Y) = true
  rw [lt_phi_vT117 hg, show plus G094 TM.Term.one = add G094 TM.Term.one from rfl,
    lt_add_ap102 _ _ (show (phi A Y).isAP = true from rfl)]
  exact hG0

/-- 正規化した `φ̄` でも同じ — 五つの枝ぜんぶ。 -/
theorem le_wTop_phiNF119 {A Y : Term} (hiA : inT A = true) (hiY : inT Y = true)
    (hAM : lt A M = true) (hYM : lt Y M = true) (hg : lt G094 A = true) :
    le wTop116 (phiNF A Y) = true := by
  have hidown : inT (plus (splitFin Y).1 (ofNat ((splitFin Y).2 - 1))) = true :=
    inT_plus (inT_splitFin hiY) (inT_ofNat _)
  have hdownM : lt (plus (splitFin Y).1 (ofNat ((splitFin Y).2 - 1))) M = true :=
    lt_plus_M (inT_splitFin hiY) (inT_ofNat _) (ltM_splitFin hiY hYM) (ltM_ofNat _)
  have hphiD : le wTop116 (phi A (plus (splitFin Y).1 (ofNat ((splitFin Y).2 - 1)))) = true :=
    le_wTop_phi119 hiA hidown hAM hdownM hg
  have hphiY : le wTop116 (phi A Y) = true := le_wTop_phi119 hiA hiY hAM hYM hg
  have hdef : le wTop116 (phiNFdefault A Y) = true := by
    unfold phiNFdefault
    split
    · rename_i hh
      exact le_wTop_SC119 ((Bool.and_eq_true _ _).mp hh).2 hg
    · exact hphiY
  have hsucc : le wTop116 (phiNFsucc A Y) = true := by
    unfold phiNFsucc
    split
    rename_i heq
    rw [heq] at hphiD hidown hdownM
    split
    · split <;> (split <;> first | exact hphiD | exact hdef)
    · exact hdef
  unfold phiNF
  split
  · rename_i hh
    exact le_wTop_SC119 ((Bool.and_eq_true _ _).mp hh).1
      (lt_trans_inT inT_G094_102 hiA hiY hg ((Bool.and_eq_true _ _).mp hh).2)
  · split
    · rename_i c d hYeq
      split
      · rename_i hAc
        have hall : (inT c && inT d && lt c M && lt d M) = true := hiY
        have h12 := (Bool.and_eq_true _ _).mp hall
        have h34 := (Bool.and_eq_true _ _).mp h12.1
        have h56 := (Bool.and_eq_true _ _).mp h34.1
        exact le_wTop_phi119 h56.1 h56.2 h34.2 h12.2
          (lt_trans_inT inT_G094_102 hiA h56.1 hg hAc)
      · exact hsucc
    · exact hsucc

/-- ヴェブレン枝の一歩 — 指数が `Γ₀` より上なら、入ってくる値に関係なく窓の上端以上。 -/
theorem stepBigExp119 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (hf : le (reg 1) ac.1 = false)
    (h1 : inT ac.1 = true) (h2 : lt ac.1 M = true) (h3 : inT ac.2 = true)
    (h4 : lt ac.2 M = true) (hg : lt G094 ac.1 = true) :
    BigU116 (stepF (reg 1) (baseOf 0) s ac) := by
  have hb : ∃ bse cc, (stepF (reg 1) (baseOf 0) s ac).2 = some (phiNF ac.1 (plus bse cc))
      ∧ inT bse = true ∧ lt bse M = true ∧ inT cc = true ∧ lt cc M = true := by
    cases hs2 : s.2 with
    | none =>
        exact ⟨baseOf 0, sub1 ac.2, by rw [stepF_snd_veb88 hf, hs2], inT_baseOf 0,
          ltM_baseOf 0, inT_sub1 h3, ltM_sub1 h3 h4⟩
    | some v =>
        obtain ⟨hiv, hvM⟩ := hst.2 v hs2
        exact ⟨v, ac.2, by rw [stepF_snd_veb88 hf, hs2], hiv, hvM, h3, h4⟩
  obtain ⟨bse, cc, heq, hib, hbM, hic, hcM⟩ := hb
  exact ⟨_, heq, le_wTop_phiNF119 h1 (inT_plus hib hic) h2 (lt_plus_M hib hic hbM hcM) hg⟩

/-- 左が `0` でなければ和も `0` でない。 -/
theorem plus_ne_zero119 {s t : Term} (hs : inT s = true) (ht : inT t = true)
    (hz : s ≠ zero) : plus s t ≠ zero := by
  cases hl : toList t with
  | nil => rw [plus_nil hl]; exact hz
  | cons b r =>
      have hpe : plus s t = ofList ((toList s).filter (fun a => le b a) ++ toList t) := by
        show (match toList t with
              | [] => s
              | b1 :: _ => ofList ((toList s).filter (fun a => le b1 a) ++ toList t)) = _
        rw [hl]
      rw [hpe]
      refine ofList_ne_zero81 _ (List.ne_nil_of_mem
        (List.mem_append_right _ (show b ∈ toList t from by rw [hl]; exact List.Mem.head _))) ?_
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact inTL_isAP hs x (List.mem_filter.mp h).1
      · exact inTL_isAP ht x h

/-- `Ω₁` より真に上なら `⊖ Ω₁` は `0` でない。 -/
theorem subAP_ne_zero119 {x : Term} (hx : inT x = true) (h : lt (reg 1) x = true) :
    subAP (reg 1) x ≠ zero := by
  cases hl : toList x with
  | nil =>
      exfalso
      rw [toList_eq_nil x hl, lt_zero_right] at h
      exact Bool.noConfusion h
  | cons b r =>
      rw [subAP_cons (reg 1) x b r hl]
      by_cases hb : (b == reg 1) = true
      · rw [if_pos hb]
        cases hr : r with
        | nil =>
            exfalso
            have hxe : x = reg 1 := by
              rw [← inT_ofList_toList x hx, hl, hr, eq_of_beq hb]; rfl
            rw [hxe, lt_irrefl] at h
            exact Bool.noConfusion h
        | cons q t =>
            refine ofList_ne_zero81 _ (List.cons_ne_nil _ _) ?_
            intro z hz
            exact inTL_isAP hx z (by rw [hl, hr]; exact List.Mem.tail _ hz)
      · rw [if_neg hb]
        intro hcc
        rw [hcc, lt_zero_right] at h
        exact Bool.noConfusion h

/-- **指数が `Ω₁` より真に上なら添字の一歩は `1` ではない。** -/
theorem dd_ne_one_exp119 {ac : Term × Term} (h1 : inT ac.1 = true) (h3 : inT ac.2 = true)
    (hz2 : ac.2 ≠ zero) (hgt : lt (reg 1) ac.1 = true) :
    ddOf75 (reg 1) ac ≠ TM.Term.one := by
  have hiE : inT (mulL (reg 1) (subAP (reg 1) ac.1)) = true :=
    inT_mulL mulDescInT (inT_reg 1) (inT_subAP h1)
  have hE : mulL (reg 1) (subAP (reg 1) ac.1) ≠ zero := by
    cases hl : toList (subAP (reg 1) ac.1) with
    | nil => exact absurd (toList_eq_nil _ hl) (subAP_ne_zero119 h1 hgt)
    | cons b r =>
        show ofList ((toList (subAP (reg 1) ac.1)).map
          (fun p => omegaNF (plus (reg 1) (logOm p)))) ≠ zero
        rw [hl]
        refine ofList_ne_zero81 _ (List.cons_ne_nil _ _) ?_
        intro x hx
        obtain ⟨s, _, hxs⟩ := List.mem_map.mp hx
        rw [← hxs]
        exact isAP_omegaNF _
  show ofList ((toList ac.2).map
    (fun p => omegaNF (plus (mulL (reg 1) (subAP (reg 1) ac.1)) (logOm p)))) ≠ TM.Term.one
  cases hl : toList ac.2 with
  | nil => exact absurd (toList_eq_nil _ hl) hz2
  | cons q r =>
      have hiq : inT q = true := inTL_inT h3 q (by rw [hl]; exact List.Mem.head _)
      cases r with
      | nil =>
          show omegaNF (plus (mulL (reg 1) (subAP (reg 1) ac.1)) (logOm q)) ≠ TM.Term.one
          exact omegaNF_ne_one76 _ (plus_ne_zero119 hiE (inT_logOm hiq) hE)
      | cons q2 r2 =>
          show add (omegaNF (plus (mulL (reg 1) (subAP (reg 1) ac.1)) (logOm q)))
            (ofList ((q2 :: r2).map
              (fun p => omegaNF (plus (mulL (reg 1) (subAP (reg 1) ac.1)) (logOm p)))))
            ≠ TM.Term.one
          intro hcc
          exact Term.noConfusion hcc

/-- **強臨界枝の添字は `0` にならない — 指数が `Ω₁` より真に上なら。** -/
theorem idxOf_ne_zero_exp119 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (h1 : inT ac.1 = true) (h3 : inT ac.2 = true)
    (hz2 : ac.2 ≠ zero) (hgt : lt (reg 1) ac.1 = true) :
    idxOf (reg 1) s ac ≠ zero := by
  intro hcc
  have hdi : inT (ddOf75 (reg 1) ac) = true := inT_ddOf75 (inT_reg 1) h1 h3
  have hs1z : sub1 (ddOf75 (reg 1) ac) ≠ zero :=
    sub1_ne_zero116 hdi (ddOf_ne_zero84 hz2) (dd_ne_one_exp119 h1 h3 hz2 hgt)
  have hle := le_sub1dd_idxOf75 (inT_reg 1) hst h1 h3
  rw [hcc] at hle
  exact hs1z (le_zero_eq116 hle)

/-- 発火の一歩 — 指数が `Ω₁` より真に上なら累算器は窓の上端以上。 -/
theorem stepBigFireExp119 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (hf : le (reg 1) ac.1 = true)
    (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hz2 : ac.2 ≠ zero)
    (hgt : lt (reg 1) ac.1 = true) :
    BigU116 (stepF (reg 1) (baseOf 0) s ac) :=
  ⟨psi (reg 1) (idxOf (reg 1) s ac), stepF_snd_fire88 hf,
    le_wTop_psi116 (idxOf_ne_zero_exp119 hst h1 h3 hz2 hgt)⟩

/-- `wcnf` の係数は `0` にならない。 -/
theorem wcnf_coef_ne_zero119 : ∀ (L : List Term), inTL L = true → descL L = true →
    (∀ x ∈ L, lt x M = true) → ∀ ac ∈ (wcnf (reg 1) L).1, ac.2 ≠ zero := by
  intro L
  induction L with
  | nil => intro _ _ _ ac hac; cases hac
  | cons q rest ih =>
    intro hc hd hM ac hac
    obtain ⟨⟨hapq, hiq⟩, hcr⟩ := inTL_cons.mp hc
    have hdr := descL_tail hd
    have hMr : ∀ x ∈ rest, lt x M = true := fun x hx => hM x (List.Mem.tail _ hx)
    by_cases hlq : lt q (reg 1) = true
    · rw [wcnf_cons_lt hlq] at hac; cases hac
    · have hlq' : lt q (reg 1) = false := bool_false hlq
      have hwc : wC (reg 1) q ≠ zero := omegaNF_ne_zero76 _
      have hiwc : inT (wC (reg 1) q) = true := inT_wC hiq
      have hPO := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) rest hcr hdr hMr
      rw [wcnf_cons_ge hlq'] at hac
      cases hr : wcnf (reg 1) rest with
      | mk fst snd =>
        rw [hr] at hac hPO
        cases fst with
        | nil =>
            have hac2 : ac ∈ [(wA (reg 1) q, wC (reg 1) q)] := hac
            rw [List.mem_singleton.mp hac2]
            exact hwc
        | cons ac0 ps =>
          cases ac0 with
          | mk a' c' =>
            have hic' : inT c' = true := (hPO.2 (a', c') (List.Mem.head _)).2.2.1
            have hac2 : ac ∈ (if (wA (reg 1) q == a') = true
                then (((wA (reg 1) q, plus (wC (reg 1) q) c') :: ps), snd)
                else (((wA (reg 1) q, wC (reg 1) q) :: (a', c') :: ps), snd)).1 := hac
            by_cases heq : (wA (reg 1) q == a') = true
            · rw [if_pos heq] at hac2
              rcases List.mem_cons.mp hac2 with h1 | h1
              · rw [h1]; exact plus_ne_zero119 hiwc hic' hwc
              · exact ih hcr hdr hMr ac (by rw [hr]; exact List.Mem.tail _ h1)
            · rw [if_neg heq] at hac2
              rcases List.mem_cons.mp hac2 with h1 | h1
              · rw [h1]; exact hwc
              · exact ih hcr hdr hMr ac (by rw [hr]; exact h1)

/-- 対が「おとなしくない」— 発火するなら指数が `Ω₁` より上か係数が `1` より上、
    Veblen なら指数が `Γ₀` より上。 -/
def bigP119 (ac : Term × Term) : Bool :=
  if le (reg 1) ac.1 then (lt (reg 1) ac.1 || lt TM.Term.one ac.2)
  else lt G094 ac.1

/-- **§119.5 の主定理 — おとなしくない対がひとつでもあれば値は窓の上端以上。** -/
theorem foldB119 : ∀ (l : List (Term × Term)) (s : Option Term × Option Term),
    StInv s →
    (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
    (∀ ac ∈ l, ac.2 ≠ zero) →
    (∀ p ∈ scanSt (reg 1) (baseOf 0) s l, le (reg 1) p.2.1 = true →
        inT (psi (reg 1) (idxOf (reg 1) p.1 p.2)) = true) →
    (∀ ac ∈ l.dropWhile (fun z => le (reg 1) z.1), le (reg 1) ac.1 = false) →
    ((∀ ac ∈ l, le (reg 1) ac.1 = false) ∨ VebFree116 s) →
    (BigU116 s ∨ ∃ ac ∈ l, bigP119 ac = true) →
    BigU116 (l.foldl (stepF (reg 1) (baseOf 0)) s) := by
  intro l
  induction l with
  | nil =>
      intro s _ _ _ _ _ _ hbig
      rcases hbig with h | ⟨ac, hac, _⟩
      · exact h
      · cases hac
  | cons ac t ih =>
    intro s hst hall hnz hpsi hds hpre hbig
    obtain ⟨h1, h2, h3, h4⟩ := hall ac (List.Mem.head _)
    have hstep : StInv (stepF (reg 1) (baseOf 0) s ac) :=
      stepF_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0) hst
        ⟨h1, h2, h3, h4⟩ (hpsi (s, ac) (List.Mem.head _))
    refine ih _ hstep (fun a ha => hall a (List.Mem.tail _ ha))
      (fun a ha => hnz a (List.Mem.tail _ ha))
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
              have hvi : v = psi (reg 1) i := Option.some.inj (hv.symm.trans hi2)
              rw [hvi] at hbv; exact hbv
        · rcases List.mem_cons.mp hac0 with he | ht
          · rw [he] at hle0
            have hb2 : (lt (reg 1) ac.1 || lt TM.Term.one ac.2) = true := by
              have : bigP119 ac = true := hle0
              unfold bigP119 at this
              rw [if_pos hf] at this
              exact this
            rcases (Bool.or_eq_true _ _).mp hb2 with hx | hx
            · exact Or.inl (stepBigFireExp119 hst hf h1 h3
                (hnz ac (List.Mem.head _)) hx)
            · exact Or.inl (stepBigFire116 hst hf h1 h3 h4 (Or.inl hx))
          · exact Or.inr ⟨ac0, ht, hle0⟩
      · have hf' : le (reg 1) ac.1 = false := bool_false hf
        rcases hbig with hbg | ⟨ac0, hac0, hle0⟩
        · exact Or.inl (stepBigNoFire116 hst hf' h1 h2 h3 h4 (Or.inl hbg))
        · rcases List.mem_cons.mp hac0 with he | ht
          · rw [he] at hle0
            have hgc : lt G094 ac.1 = true := by
              have : bigP119 ac = true := hle0
              unfold bigP119 at this
              rw [if_neg (by rw [hf']; exact Bool.noConfusion)] at this
              exact this
            exact Or.inl (stepBigExp119 hst hf' h1 h2 h3 h4 hgc)
          · exact Or.inr ⟨ac0, ht, hle0⟩

/-- **§119.5 の主定理 (2)。**  対の列におとなしくない対がひとつでもあれば
    `ψ₀` の値は窓の上端以上。**標準性も帰納法も使わない。** -/
theorem expUpBig119 {x : Term} (hx : inT x = true) (hxM : lt x M = true)
    (Hpx : PsiIdxOK 0 x)
    (h : ∃ ac ∈ (wcnf (reg 1) (toList x)).1, bigP119 ac = true) :
    le wTop116 (collapse 0 x) = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  have hM := ltM_toList x hx hxM
  obtain ⟨⟨hrT, hrM⟩, hallOK⟩ :=
    wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList x) hc hd hM
  have hacc : inT (accW89 x) = true ∧ lt (accW89 x) M = true := by
    have hstF : StInv ((wcnf (reg 1) (toList x)).1.foldl (stepF (reg 1) (baseOf 0)) (none, none)) :=
      fold_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0)
        (wcnf (reg 1) (toList x)).1 (none, none) stInv_none hallOK Hpx
    unfold accW89
    cases hg : ((wcnf (reg 1) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2 with
    | none => exact ⟨inT_zero, lt_zero_M⟩
    | some v => exact hstF.2 v hg
  have hfold := foldB119 (wcnf (reg 1) (toList x)).1 (none, none) stInv_none hallOK
    (wcnf_coef_ne_zero119 (toList x) hc hd hM) Hpx
    (fireSplit109 (isSC_reg_succ 0) (inT_reg 1) (show (reg 1).isAP = true from rfl)
      (toList x) hc hd)
    (Or.inr (Or.inl rfl)) (Or.inr h)
  obtain ⟨v, hv, hbv⟩ := hfold
  have hav : accW89 x = v := by unfold accW89; rw [hv]; rfl
  have hbig : le wTop116 (plus (accW89 x) (rhoW89 x)) = true := by
    rw [hav]
    exact leG_plus_left116 inT_wTop116 isAP_wTop116 (by rw [← hav]; exact hacc.1) hrT hbv
  have hsi : inT (plus (accW89 x) (rhoW89 x)) = true := inT_plus hacc.1 hrT
  have hsM : lt (plus (accW89 x) (rhoW89 x)) M = true := lt_plus_M hacc.1 hrT hacc.2 hrM
  rw [collapse0_raw89]
  refine leG_omegaNF116 inT_wTop116 isAP_wTop116 ltM_wTop116 lt_one_wTop116
    (inT_plus (inT_reg 0) hsi) (lt_plus_M (inT_reg 0) hsi lt_zero_M hsM) ?_
  exact leG_plus_right116 inT_wTop116 (inT_reg 0) hsi hbig

end

/-! ### §119.5 残っているものを、対の列の形ひとつで名指しする -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- `Ω₁` 以上の成分の指数は、対の列にそのまま現れる — 併合は指数を変えない。 -/
theorem wcnf_expG119 : ∀ (L : List Term), inTL L = true → descL L = true →
    ∀ p ∈ L, lt p (reg 1) = false →
      ∃ ac ∈ (wcnf (reg 1) L).1, ac.1 = wA (reg 1) p := by
  intro L
  induction L with
  | nil => intro _ _ p hp _; cases hp
  | cons q rest ih =>
    intro hc hd p hp hpw
    obtain ⟨⟨hapq, hiq⟩, hcr⟩ := inTL_cons.mp hc
    have hdr := descL_tail hd
    by_cases hlq : lt q (reg 1) = true
    · exfalso
      rcases List.mem_cons.mp hp with h1 | h1
      · rw [h1, hlq] at hpw; exact Bool.noConfusion hpw
      · have hip : inT p = true :=
          ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcr p h1)).2
        have hpw2 := ltW_of_le79 hip hiq (descL_bound_inT rest q hiq hcr hd p h1) hlq
        rw [hpw2] at hpw; exact Bool.noConfusion hpw
    · have hlq' : lt q (reg 1) = false := bool_false hlq
      rw [wcnf_cons_ge hlq']
      cases hr : wcnf (reg 1) rest with
      | mk fst snd =>
        cases fst with
        | nil =>
            refine ⟨(wA (reg 1) q, wC (reg 1) q), List.Mem.head _, ?_⟩
            rcases List.mem_cons.mp hp with h1 | h1
            · rw [h1]
            · exfalso
              obtain ⟨ac, hac, _⟩ := ih hcr hdr p h1 hpw
              rw [hr] at hac; cases hac
        | cons ac0 ps =>
          cases ac0 with
          | mk a' c' =>
            have key : wA (reg 1) p = wA (reg 1) q ∨
                (∃ ac ∈ (a', c') :: ps, ac.1 = wA (reg 1) p) := by
              rcases List.mem_cons.mp hp with h1 | h1
              · exact Or.inl (by rw [h1])
              · obtain ⟨ac, hac, hGac⟩ := ih hcr hdr p h1 hpw
                rw [hr] at hac
                exact Or.inr ⟨ac, hac, hGac⟩
            show ∃ ac ∈ (if (wA (reg 1) q == a') = true
                then ((wA (reg 1) q, plus (wC (reg 1) q) c') :: ps, snd)
                else ((wA (reg 1) q, wC (reg 1) q) :: (a', c') :: ps, snd)).1,
              ac.1 = wA (reg 1) p
            by_cases heq : (wA (reg 1) q == a') = true
            · rw [if_pos heq]
              rcases key with h1 | ⟨ac, hac, hGac⟩
              · exact ⟨(wA (reg 1) q, plus (wC (reg 1) q) c'), List.Mem.head _, h1.symm⟩
              · rcases List.mem_cons.mp hac with h2 | h2
                · refine ⟨(wA (reg 1) q, plus (wC (reg 1) q) c'), List.Mem.head _, ?_⟩
                  have hac1 : a' = wA (reg 1) p := by rw [← hGac, h2]
                  exact (eq_of_beq heq).trans hac1
                · exact ⟨ac, List.Mem.tail _ h2, hGac⟩
            · rw [if_neg heq]
              rcases key with h1 | ⟨ac, hac, hGac⟩
              · exact ⟨(wA (reg 1) q, wC (reg 1) q), List.Mem.head _, h1.symm⟩
              · exact ⟨ac, List.Mem.tail _ hac, hGac⟩

/-- **成分の言葉で。**  桁の指数が `Γ₀` より真に上で `Ω₁` より下なら、値は窓の上端以上。 -/
theorem expUpStrict119 {x : Term} (hx : inT x = true) (hxM : lt x M = true)
    (Hpx : PsiIdxOK 0 x) {p : Term} (hp : p ∈ toList x) (hpw : lt p (reg 1) = false)
    (hgt : lt G094 (wA (reg 1) p) = true) (hnf : le (reg 1) (wA (reg 1) p) = false) :
    le wTop116 (collapse 0 x) = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨ac, hac, hace⟩ := wcnf_expG119 (toList x) hc hd p hp hpw
  refine expUpBig119 hx hxM Hpx ⟨ac, hac, ?_⟩
  unfold bigP119
  rw [hace, if_neg (by rw [hnf]; exact Bool.noConfusion)]
  exact hgt

/-- **残っているもの、ぜんぶ。**  対の列がぜんぶおとなしいとき。**証明しない。** -/
def TightUp119 : Prop := ∀ a : BT, btLe72 1 (BT.D 0 a) = true → BT.isStd (BT.D 0 a) = true →
    le (rawT94 0) (dict (BT.D 0 a)) = true →
    ((wcnf (reg 1) (toList (dict a))).1).any bigP119 = false →
    le wTop116 (dict (BT.D 0 a)) = true

/-- **§119.5 の主定理 (3) — `ExpUp116` は `TightUp119` ひとつに落ちる。** -/
theorem expUp116_of_tight119 (Hp : PsiIdxOKStd172) (HT : TightUp119) : ExpUp116 := by
  intro a hb hs hle p hp hpw hex
  have hba : btLe72 1 a = true := by
    have h : (decide (0 ≤ 1) && btLe72 1 a) = true := hb
    exact ((Bool.and_eq_true _ _).mp h).2
  have hsa : BT.isStd a = true := by
    have h : (BT.isStd a && (BT.GB 0 a).all (fun e => BT.lt e a)) = true := hs
    exact ((Bool.and_eq_true _ _).mp h).1
  obtain ⟨hiA, hAM⟩ := inT_dict_of_std172 Hp a hba hsa
  cases hany : ((wcnf (reg 1) (toList (dict a))).1).any bigP119 with
  | false => exact HT a hb hs hle hany
  | true =>
      show le wTop116 (collapse 0 (dict a)) = true
      exact expUpBig119 hiA hAM (Hp 0 a (by omega) hba hs) (List.any_eq_true.mp hany)

/-- **§119.5 の主定理 (4) — `Γ₀` の運び手は `ψ₀` の引数を `Ω^Ω` の上へ押し上げる。**
    §111 の `carrier_notStd111` から「先頭成分」という形の制限を外したもの。どちらの段の
    どの位置に運び手がいても効く。 -/
theorem carrierAbove119 (Hg : Gam0Drags111) {a c e : BT}
    (hs : BT.isStd (BT.D 0 a) = true)
    (hmem : BT.D 1 c ∈ BT.toL a) (hmem2 : BT.D 1 e ∈ BT.toL c)
    (hbe : btLe72 1 e = true) (hse : BT.isStd e = true) (hdz : dict e = G094) :
    BT.lt bOO94 a = true := by
  obtain ⟨_, e', he', hle⟩ := Hg e hbe hse hdz
  have h1 : e' ∈ BT.GB 0 c := sub_GB0_104 c 1 e hmem2 e' he'
  have h2 : e' ∈ BT.GB 0 a := sub_GB0_104 a 1 c hmem e' h1
  exact needOO108 (hd085_D0_111 a) hs h2 hle

/-- **§119.5 の主定理 (5) — 橋は飾りではない。**  指数がちょうど `Γ₀` の桁があれば、
    その運び手の値はちょうど `Γ₀` で、標準性が `ψ₀` の引数を `Ω^Ω` の上へ押し上げる。 -/
theorem carrierOfExpG0_119 (Hp : PsiIdxOKStd172) (Hg : Gam0Drags111) {a : BT}
    (hba : btLe72 1 a = true) (hsa : BT.isStd a = true)
    (hs : BT.isStd (BT.D 0 a) = true) {p : Term} (hp : p ∈ toList (dict a))
    (hpw : lt p (reg 1) = false) (hEq : wA (reg 1) p = G094) :
    BT.lt bOO94 a = true := by
  have hex : lt (wA (reg 1) p) G094 = false := by rw [hEq, lt_irrefl]
  obtain ⟨c, e, t, hmem, hmem2, hbe, hse, htl, hleG⟩ := expBridge119 Hp hba hsa hp hpw hex
  have hide : inT (dict e) = true := (inT_dict_of_std172 Hp e hbe hse).1
  have hhd : G094 = omegaNF (dict e) := by
    have h2 : toList (wA (reg 1) p) = omegaNF (dict e) :: t := htl
    rw [hEq, toList_G0_119] at h2
    exact congrArg (fun l => List.headD l zero) h2
  have hdz : dict e = G094 := by
    rcases (Bool.or_eq_true _ _).mp hleG with heq | hgt
    · exact (eq_of_beq heq).symm
    · exfalso
      have hmono := lt_omegaNF_inT79 inT_G094_102 hide hgt
      rw [omegaNF_G0_119, ← hhd, lt_irrefl] at hmono
      exact Bool.noConfusion hmono
  exact carrierAbove119 Hg hs hmem hmem2 hbe hse hdz

/-- おとなしい対の列で `Γ₀` 以上の指数を持つ桁があるなら、その指数は `Γ₀` か `Ω₁` ちょうど。 -/
theorem tameExp119 {L : List Term} (hc : inTL L = true) (hd : descL L = true)
    {p : Term} (hp : p ∈ L) (hpw : lt p (reg 1) = false)
    (hex : lt (wA (reg 1) p) G094 = false)
    (htame : ((wcnf (reg 1) L).1).any bigP119 = false) :
    wA (reg 1) p = G094 ∨ wA (reg 1) p = reg 1 := by
  obtain ⟨ac, hac, hace⟩ := wcnf_expG119 L hc hd p hp hpw
  have hb : bigP119 ac = false := by
    cases hbb : bigP119 ac with
    | false => rfl
    | true => rw [List.any_eq_true.mpr ⟨ac, hac, hbb⟩] at htame; exact Bool.noConfusion htame
  have hip : inT p = true :=
    ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hc p hp)).2
  have hiwA : inT (wA (reg 1) p) = true :=
    inT_wA109 (inT_reg 1) (show (reg 1).isSC = true from rfl) hip
  have hge : le G094 (wA (reg 1) p) = true :=
    le_of_not_lt3 (inT_le_fragR _ hiwA) (inT_le_fragR _ inT_G094_102) hex
  unfold bigP119 at hb
  rw [hace] at hb
  by_cases hf : le (reg 1) (wA (reg 1) p) = true
  · rw [if_pos hf] at hb
    refine Or.inr ?_
    rcases (Bool.or_eq_true _ _).mp hf with h1 | h1
    · exact (eq_of_beq h1).symm
    · exfalso
      have h2 : lt (reg 1) (wA (reg 1) p) = false := by
        cases hq : lt (reg 1) (wA (reg 1) p) with
        | false => rfl
        | true => rw [hq] at hb; exact Bool.noConfusion hb
      rw [h1] at h2; exact Bool.noConfusion h2
  · rw [if_neg hf] at hb
    refine Or.inl ?_
    rcases (Bool.or_eq_true _ _).mp hge with h1 | h1
    · exact (eq_of_beq h1).symm
    · rw [h1] at hb; exact Bool.noConfusion hb

end

/-! ### §119.6 326 行が今よりかかっているもの -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- **§119.2 の主定理 — 帳簿の帰納法、係数の形も込みで。**  §116.6 の `winUpAux116` は
    三つの形のうち `Ω₁` より下の形だけを帰納法の仮定で片づけ、係数の形を条項
    `CoefUp116` として外へ出した。§119.1 がその形も帰納法の仮定で片づけるので、
    **残る条項は指数の形ひとつだけになる。** -/
theorem winUpAux119 (Hp : PsiIdxOKStd172) (HE : ExpUp116) :
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
              have hq : lt (wC (reg 1) p) (rawT94 0) = false := by
                rw [hex, Bool.not_true, Bool.false_or] at hbad
                cases hq : lt (wC (reg 1) p) (rawT94 0) with
                | false => rfl
                | true => rw [hq] at hbad; exact Bool.noConfusion hbad
              exact Or.inl (List.any_eq_true.mpr ⟨p, hp,
                coefUpStep119 Hp ih hn hba hsa hp hpw hq⟩)
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

/-- **`CoefUp116` は独立な条項ではない。**  指数の条項があれば定理として出る。 -/
theorem coefUp116_of_expUp119 (Hp : PsiIdxOKStd172) (HE : ExpUp116) : CoefUp116 :=
  fun a hb hs hle _ _ _ _ _ => winUpAux119 Hp HE (BT.size a) a (Nat.le_refl _) hb hs hle

/-- **`WinProp113` は指数の形の条項ひとつに落ちる。** -/
theorem winProp_of_expUp119 (Hp : PsiIdxOKStd172) (HE : ExpUp116) : WinProp113 :=
  fun a hb hs _ hle _ => winUpAux119 Hp HE (BT.size a) a (Nat.le_refl _) hb hs hle

theorem gap_of_expUp119 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HE : ExpUp116) :
    GapAtG0_107 := gap_of_winProp113 Hp H2 (winProp_of_expUp119 Hp HE)

theorem denseMid107_false_of_expUp119 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (HE : ExpUp116) : ¬ DictDenseMid107 :=
  denseMid107_false_of_winProp113 Hp H2 (winProp_of_expUp119 Hp HE)

theorem cofDenseS1_false_of_expUp119 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (HE : ExpUp116) : ¬ CofDenseS1 :=
  cofDenseS1_false_of_winProp113 Hp H2 (winProp_of_expUp119 Hp HE)

/-- **§119.6 の主定理 — 条項ひとつから 326 行の隙間まで。** -/
theorem gap_of_tight119 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HT : TightUp119) :
    GapAtG0_107 := gap_of_expUp119 Hp H2 (expUp116_of_tight119 Hp HT)

theorem winProp_of_tight119 (Hp : PsiIdxOKStd172) (HT : TightUp119) : WinProp113 :=
  winProp_of_expUp119 Hp (expUp116_of_tight119 Hp HT)

theorem denseMid107_false_of_tight119 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (HT : TightUp119) : ¬ DictDenseMid107 :=
  denseMid107_false_of_expUp119 Hp H2 (expUp116_of_tight119 Hp HT)

theorem cofDenseS1_false_of_tight119 (Hp : PsiIdxOKStd172) (H2 : DictLtA74)
    (HT : TightUp119) : ¬ CofDenseS1 :=
  cofDenseS1_false_of_expUp119 Hp H2 (expUp116_of_tight119 Hp HT)

theorem coefUp116_of_tight119 (Hp : PsiIdxOKStd172) (HT : TightUp119) : CoefUp116 :=
  coefUp116_of_expUp119 Hp (expUp116_of_tight119 Hp HT)

end

/-! ### §119.7 測定 (凍結)

**構成を先に書く。**  母集団は三つ。ひとつは新しく作り、ふたつは §108.6 / §116.7 のものを
読み直す。

    S  `Γ₀` の桁を運ぶ形 `ψ₁ψ₁ w` を 10 個の種 (§98 の塔の三段・§108 の族・§111 の族・
       `ψ₁0`・`Ω₁`・`ψ₀0`・`Ω^Ω`・`ψ₀Ω^Ω`) にはめ、さらに三つの形に置いたもの、30 項。
       t1 = `ψ₁ψ₁ w`               t2 = `Ω^Ω ⊕ ψ₁ψ₁ w`        t3 = `ψ₁ψ₁ w ⊕ ψ₀Ω^Ω`
       **標準性で濾さない。**  測るのは「`ψ₀` の引数として」である。
    E  §108.6 の数え上げ (大きさ 12 までの標準・段 1 以下の項 9992 個) をそのまま読み直す。
    E14 §116.7 の `bigE116` (大きさ 14 まで 58239 個) をそのまま読み直す。

**仮説が母集団に見えていること。**  `tame119` は S の 30 項中 13 項で成り立ち 17 項で
破れる — 両側とも見えている。E では条項が訊かれる 2495 項のうち 1 項で成り立ち 2494 項で
破れ、窓の下端に届かない 2823 項では **2823 項すべてで成り立つ**。 -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

set_option maxRecDepth 100000

/-- 「対の列がぜんぶおとなしい」— `TightUp119` の前提の判定器。 -/
def tame119 (z : BT) : Bool := !(((wcnf (reg 1) (toList (dict z))).1).any bigP119)
/-- 三つの場合を別々に読む道具 — 桁の指数が `Ω₁` 以上 / `Γ₀` より上で `Ω₁` より下 /
    ちょうど `Γ₀`。 -/
def hiE119 (z : BT) : Bool :=
  (toList (dict z)).any (fun p => !(lt p (reg 1)) && le (reg 1) (wA (reg 1) p))
def midE119 (z : BT) : Bool :=
  (toList (dict z)).any (fun p => !(lt p (reg 1)) && lt G094 (wA (reg 1) p)
      && !(le (reg 1) (wA (reg 1) p)))
def carE119 (z : BT) : Bool :=
  (toList (dict z)).any (fun p => !(lt p (reg 1)) && (wA (reg 1) p == G094))

/-- 手で作った運び手 — `ψ₁ψ₁ w`。 -/
def dg119 (w : BT) : BT := BT.D 1 (BT.D 1 w)

/-! **段の正直さ — 定理として。**  作った運び手は段 1 を超えず、段 0 は一歩目で離れる。 -/
theorem btLe1_dg119 {w : BT} (h : btLe72 1 w = true) : btLe72 1 (dg119 w) = true := by
  show (decide (1 ≤ 1) && (decide (1 ≤ 1) && btLe72 1 w)) = true
  rw [h]; rfl

theorem btLe0_dg119 (w : BT) : btLe72 0 (dg119 w) = false := by
  show (decide (1 ≤ 0) && (decide (1 ≤ 0) && btLe72 0 w)) = false
  rfl

theorem btLe1_D0dg119 {w : BT} (h : btLe72 1 w = true) :
    btLe72 1 (BT.D 0 (dg119 w)) = true := by
  show (decide (0 ≤ 1) && btLe72 1 (dg119 w)) = true
  rw [btLe1_dg119 h]; rfl

def seedE119 : List BT :=
  [ bTowG98 0, bTowG98 1, bTowG98 2, bWin108 1, cWin111 cCar111, BT.D 1 BT.zero,
    BT.Om 1, BT.D 0 BT.zero, bOO94, cCar111 ]
def argE119 : List BT :=
  (seedE119.map dg119) ++ (seedE119.map fun w => BT.sum bOO94 (dg119 w))
    ++ (seedE119.map fun w => BT.sum (dg119 w) (BT.D 0 bOO94))

#guard argE119.length == 30

/-! **S — 30 項。**  段 1 以下 30、`ψ₀` を載せて標準になるもの 14、条項が訊かれる場所
    (`base116`) 8、結論が成り立つもの 19、おとなしいもの 13。三つの場合は
    運び手 6・中間 12・強臨界 16 で、**どれも見えている**。 -/
#eval (argE119.length, argE119.countP fun z => btLe72 1 z,
       argE119.countP fun z => BT.isStd (BT.D 0 z), argE119.countP base116,
       argE119.countP conc116, argE119.countP tame119,
       argE119.countP carE119, argE119.countP midE119, argE119.countP hiE119)
#guard (argE119.length, argE119.countP fun z => btLe72 1 z,
       argE119.countP fun z => BT.isStd (BT.D 0 z), argE119.countP base116,
       argE119.countP conc116, argE119.countP tame119,
       argE119.countP carE119, argE119.countP midE119, argE119.countP hiE119)
    == (30, 30, 14, 8, 19, 13, 6, 12, 16)

/-! **S — `expUpBig119` は空振りではない。**  おとなしくない 17 項では結論が
    **17/17** で成り立つ (定理どおり)。おとなしい 13 項では **2 項しか**成り立たない —
    **`tame119` は結論を含意しない**ので、`TightUp119` は自明な条項ではない。
    そこが標準性の入る場所である。 -/
#guard (argE119.countP fun z => tame119 z && conc116 z,
        argE119.countP fun z => !(tame119 z) && conc116 z,
        argE119.countP fun z => !(tame119 z)) == (2, 17, 17)

/-! **E の読み直し (1) — 条項が訊かれる 2495 項のうち、おとなしいのは 1 項だけ。**
    その 1 項でも結論は成り立つ。運び手の場合は 1 項、**中間の場合は 0 項**、
    強臨界の場合は **2495 項**。 -/
#guard (fun L => (L.length, L.countP tame119, L.countP fun z => tame119 z && conc116 z,
        L.countP carE119, L.countP midE119, L.countP hiE119))
    (allStd108.filter base116) == (2495, 1, 1, 1, 0, 2495)

/-! **E の読み直し (2) — 分離は完全である。**  窓の下端に届かない正しい `ψ₀` 引数は
    2823 項で、**2823 項すべてがおとなしい**。だから `¬ tame119` は E の上で
    「窓を越える」ことと 2494/2495 対 0/2823 で一致する。 -/
#guard (fun L => (L.length, L.countP tame119))
    (allStd108.filter fun z => btLe72 1 (BT.D 0 z) && BT.isStd (BT.D 0 z)
       && !(le (rawT94 0) (dict (BT.D 0 z)))) == (2823, 2823)

/-! **E14 — 一段伸ばしても同じ。**  条項が訊かれる 16425 項のうちおとなしいのは 1 項、
    そこで結論は成り立つ。**中間の場合は 3 項** — 大きさ 12 では 0 項だったので
    `expUpStrict119` も空振りではないが、**仕事をしているのは強臨界の枝のほうである**。 -/
#guard (fun L => (L.length, L.countP tame119, L.countP fun z => tame119 z && conc116 z,
        L.countP midE119)) (bigE116.filter base116) == (16425, 1, 1, 3)

/-! **S は条項そのものを試せる。**  §116.7 の S は「窓に入る」と「正しい `ψ₀` 引数」が
    0 項で重なっていた。ここでは条項が訊かれる場所が 8 項あり、そのうち**おとなしいのは
    2 項**で、両方とも結論が成り立つ。結論が破れる場所は 0 項。**種の問題は、運び手を
    `ψ₁ψ₁ w` の `w` で振ることで消える。** -/
#guard (argE119.countP base116,
        argE119.countP fun z => base116 z && tame119 z,
        argE119.countP fun z => base116 z && tame119 z && conc116 z,
        argE119.countP fun z => base116 z && !(conc116 z)) == (8, 2, 2, 0)

/-! **おとなしい 1 項は §98 の塔の第 1 段そのもの。**  対の列は `[(Ω₁,1), (Γ₀,1)]` で、
    発火は指数ちょうど `Ω₁`・係数ちょうど `1`、その後の Veblen 桁の指数はちょうど `Γ₀`。
    値は窓の上端ちょうど。**残っている条項が訊かれる場所は、ここと同じ形である。** -/
#guard tame119 (bArg98 (bTowG98 0)) && conc116 (bArg98 (bTowG98 0))
#guard base116 (bArg98 (bTowG98 0))

end

/-! ## §124 THE DIVISION SURVIVES ON THE FIRING PREFIX — `IdxLeMix109` IS A THEOREM

§109 wrote the clause down and four sections carried it without touching it:

    `IdxLeMix109` :  `a`'s fold fires at its last pair, `b`'s does NOT, and
                     `hi (dict a) < hi (dict b)`  ⟹  the collapse indices satisfy
                     `ja ≤ jb` .

§120 closed its strict sibling `IdxMono101` by showing that the firing fold is a DIVISION,
`X = ω^(Ω₁·Ω₁)·(1 ⊕ j)` (`divOm120`), and taking the contrapositive of two NON-strict maps.
In §120.4 it also named, for whoever took this clause, the one route it could see:

> the firing pairs are a PREFIX (§109.1's `fireSplit109`), so the index is the prefix's
> index, and §120.1's induction run on that prefix gives `ω^(Ω₁·Ω₁)·(1 ⊕ j) ≤ X` for every
> `X` that has an index at all — `≤` where §120.1 has `=`.

**The route is right about the prefix and wrong about the `≤`.**  Running §120.1's induction
on the prefix does not weaken the identity.  It moves the RIGHT-HAND SIDE, and what comes out
is still an equality:

    **`ω^(Ω₁·Ω₁)·(1 ⊕ j) = ofList ((toList X).takeWhile fires)`**    (`divCut124`)

for every `X` whose components are all `≥ Ω₁` and which has an index at all — **with no
firing hypothesis on either side.**  When every component fires the right-hand side IS `X`
and this is §120's `divOm120`; when some component does not fire it is the firing prefix of
`X`, strictly below `X`.  Keeping the firing components is monotone (`cutMono124`), so §120's
contrapositive runs unchanged and the clause comes out needing neither `lastFire92 (dict a)`
nor `lastFire92 (dict b)`.

WHAT IS PROVED.

  §124.1  **THE IDENTITY, RESTRICTED TO THE PREFIX** (`cutFire124`).  §120.1's
          `mulL_sumDD120` assumed every pair fires; `cutFire124` assumes nothing and proves
          `ω^(Ω₁·Ω₁)·Σ{Δ over the firing pairs} = ofList (the firing components)`.  The
          induction is §120.1's with one branch added — the step where the head component
          does not fire, where `wcnfFstHd109` says the head PAIR does not fire either and
          both sides are `0`.  `wcnfTakeCons124` is §120.1's `wcnf_cons_sum120` with its
          "all pairs fire" hypothesis replaced by "the head component fires", which is the
          only thing that decomposition ever read.

  §124.2  **THE INDEX IS THE PREFIX'S INDEX** (`idxTake124`, `sumTake124`, `divCut124`).
          A non-firing pair leaves the index component of the fold alone (`foldNotFire124`),
          and §109.1's `fireSplit109` says the non-firing pairs are exactly the `dropWhile`,
          so the whole tail is silent.  `sumTake124` is §120.2's `plus_one_idx120` run on the
          prefix; `divCut124` puts the two together and adds the bound `1 ⊕ j < M` that the
          strict monotonicity lemmas need.

  §124.3  **THE CUT IS MONOTONE** (`lt_append_cut124`, `dropNotFire124`, `cutMono124`).
          §89.4's `lt_append_hi89` — "comparing the `≥ Ω₁` parts decides the comparison" — is
          stated at the one cut point `Ω₁`, and its proof uses that cut point in exactly one
          place: to see that the head of the tail is below the head of the big part.
          `lt_append_cut124` is the same proof with `reg 1` replaced by that hypothesis
          itself, and it then applies at the cut "does this component fire", which is a cut
          because firing is upward closed along the component list — `dropNotFire124`, which
          is §109.1's `fireMono109` read on components rather than on pairs.

  §124.4  **THE CLAUSE** (`idxLe_core124`, `IdxLeAny124`, `idxLeMix109_of_psi124`).
          `idxLe_core124` mentions no `dict`, no `BT`, no `K`-condition and **no firing**:
          two 𝔗(M) terms with all components `≥ Ω₁`, both with an index, and the order of the
          terms decides the order of the indices, non-strictly.  `IdxLeAny124` is the `BT`
          form, `idxLeMix109_of_psi124 : PsiIdxOKStd172 → IdxLeMix109`, and
          `hiMono_of_two124` / `certIn_t326_124` take `IdxLeMix109` off §120's list.

  §124.5  **THE STRICT FORM IS FALSE HERE TOO** (`not_idxLtAny124`) — §109's `mixA109`/
          `mixB109` refute it verbatim, since dropping hypotheses only makes the strict form
          harder.  `sepCutFacts124` freezes the BUILT witness `ψ₁⁴0 ⊕ ψ₁³0 ⊕ Ω₁` (13 symbols)
          on which the prefix is proper AND two components fire — the shape §124.6's first
          population does not contain.

  §124.6  the measurement.

WHAT IS **NOT** CLAIMED.  `IdxLeMix109` is delivered as `PsiIdxOKStd172 → IdxLeMix109`, not
as a bare theorem, for §120's reason word for word: every order lemma in the file is stated
on 𝔗(M) and without the gate `dict a` need not be a 𝔗(M) term.  At the point of use the
hypothesis is free — `hiMono_of_three120` and `certIn_t326_120` both take it already.
`VebIngF114` and `VebRest117` are untouched and unproved; `HiMono89` is not proved.  §124
REMOVES a residue rather than moving one.  Row 326's Veblen side is now `VebIngF114`,
`VebRest117` and `PsiIdxOKStd172`.

**WHERE §124 STOPPED.**  Nowhere on its own clause: it is closed, and it is closed in a
strictly stronger form than the one it was asked for (`IdxLeAny124` — no firing on either
side).  What it does NOT do is help the two Veblen clauses that remain, and the reason is
§120's, unchanged: the division has an inverse, `phiNF` does not.  §124 says one new thing
about that boundary — the division is not confined to the all-firing terms, it lives on the
firing PREFIX of every term — but the Veblen tail beyond that prefix is exactly what
`VebIngF114` and `VebRest117` are about, and nothing here touches it.

**THE LEDGER, thirteenth entry, and it is against a hand-off again.**  §120 named the route
out of its own `a`-side hypothesis and named it as a WEAKENING (`≤` where §120.1 has `=`).
The weakening is not needed: the equality holds once the right-hand side is read as the
prefix rather than the term.  **What was short was not an inequality.  It was the right
right-hand side.**  And the other half of the entry is against §109: `IdxLeMix109` carries
two firing hypotheses and the proof reads NEITHER — the second one (`lastFire92 (dict b) =
false`) is not even used to know that `b`'s fold has a Veblen tail, because §124 never asks.
The one lemma that had to be re-stated rather than re-used is §89.4's `lt_append_hi89`,
written at the single cut point `Ω₁` in a proof that never needed a particular cut point.

WHAT THE MEASUREMENT SAYS (§124.6 gives the construction).  Two populations, BUILT from a
firing line and a non-firing line, nothing filtered.

  * **120 terms, 89 of them `K`-standard, max 32 symbols.  70 have a collapse index, 24 of
    those fire at the last pair and 46 do not; 19 have no index at all.**
  * **The identity is the section.**  `ω^(Ω₁·Ω₁)·(1 ⊕ j) = the firing prefix` holds on
    **70 of 70** terms that have an index.  §120's `ω^(Ω₁·Ω₁)·ΣΔ = hi` holds on **24 of the
    same 70** — the firing ones, and no other.  The two numbers are the section in one line.
  * **The prefix is really proper.**  46 of the 89 have a firing prefix strictly inside their
    component list; on those 46, and only those, §120's identity fails and §124's holds.
  * **The clause, seen, and the strict form refuted by count.**  2415 residual pairs have an
    index on both sides: `ja ≤ jb` breaks **0** times and `ja < jb` breaks **289** times.
    By class — (fires, fires) 276/0/0, (fires, Veblen) 358/0/**46**, (Veblen, fires) 746/0/0,
    (Veblen, Veblen) **1035**/0/**243**.  The last class is the one NO clause in the file
    covered: `IdxMono101` wants both sides firing, `IdxLeMix109` wants `a` firing.
  * **A hypothesis this population cannot see.**  Of 3916 residual pairs over the 89, the
    number with an index on `a` and none on `b` is **0** — §109.2 as a count.  So "b has an
    index" is never a filter here; it is structural (without it there is no `jb` to compare),
    NOT empirically necessary, and §124 claims only the former.
  * **A shape this population cannot express, and it was not a size problem.**  All 46 proper
    prefixes have **exactly one** firing component: `≥ 2 firing components followed by a
    non-firing one` occurs **0 times in 120 terms of up to 32 symbols**.  The witness was
    BUILT from the statement — `sepCut124 = ψ₁⁴0 ⊕ ψ₁³0 ⊕ Ω₁`, **13 symbols**, two firing
    components and one not — and only then was the population widened.  Widening the SHAPE
    (three-term sums with three DISTINCT summands) and not the size — 363 terms, **the same
    maximum of 32 symbols** — gives **90** of them.  §116's failure mode was size; this one
    was shape, and a deeper sweep at the old shape would have found nothing.
  * **And the next shape up is still absent.**  `≥ 3 firing components before a non-firing
    one` occurs 0 times in both populations; `sepCut2124` (20 symbols) is built by hand and
    behaves the same. -/

/-! ### §124.1 発火する成分は前置き — そこだけで §120.1 の恒等式が立つ -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- `takeWhile` の要素はもとの列の要素。 -/
theorem mem_of_takeWhile124 {α : Type} (P : α → Bool) : ∀ (l : List α) (a : α),
    a ∈ l.takeWhile P → a ∈ l
  | [], a, h => by cases h
  | b :: t, a, h => by
      by_cases hb : P b = true
      · rw [List.takeWhile_cons_of_pos hb] at h
        rcases List.mem_cons.mp h with h1 | h1
        · rw [h1]; exact List.Mem.head _
        · exact List.Mem.tail _ (mem_of_takeWhile124 P t a h1)
      · rw [List.takeWhile_cons_of_neg (by simpa using hb)] at h; cases h

/-- `dropWhile` の要素はもとの列の要素。 -/
theorem mem_of_dropWhile124 {α : Type} (P : α → Bool) : ∀ (l : List α) (a : α),
    a ∈ l.dropWhile P → a ∈ l
  | [], a, h => by cases h
  | b :: t, a, h => by
      by_cases hb : P b = true
      · rw [List.dropWhile_cons_of_pos hb] at h
        exact List.Mem.tail _ (mem_of_dropWhile124 P t a h)
      · rw [List.dropWhile_cons_of_neg (by simpa using hb)] at h
        exact h

/-- 前置きの成分列は 𝔗(M) の並び。 -/
theorem inTL_takeWhile124 (P : Term → Bool) {l : List Term} (h : inTL l = true) :
    inTL (l.takeWhile P) = true := by
  show (l.takeWhile P).all _ = true
  rw [List.all_eq_true]
  intro x hx
  exact List.all_eq_true.mp h x (mem_of_takeWhile124 P l x hx)

/-- 後半の成分列も 𝔗(M) の並び。 -/
theorem inTL_dropWhile124 (P : Term → Bool) {l : List Term} (h : inTL l = true) :
    inTL (l.dropWhile P) = true := by
  show (l.dropWhile P).all _ = true
  rw [List.all_eq_true]
  intro x hx
  exact List.all_eq_true.mp h x (mem_of_dropWhile124 P l x hx)

/-- 前置きの成分列も降順。 -/
theorem descL_takeWhile124 (P : Term → Bool) : ∀ (l : List Term), inTL l = true →
    descL l = true → descL (l.takeWhile P) = true := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons a t ih =>
    intro hc hd
    obtain ⟨⟨_, hia⟩, hct⟩ := inTL_cons.mp hc
    have hdt := descL_tail hd
    have hbound := descL_bound_inT t a hia hct hd
    by_cases hp : P a = true
    · rw [List.takeWhile_cons_of_pos hp]
      cases hf : t.takeWhile P with
      | nil => rfl
      | cons b s =>
        refine descL_cons.mpr ⟨?_, by rw [← hf]; exact ih hct hdt⟩
        have hb : b ∈ t.takeWhile P := by rw [hf]; exact List.Mem.head _
        exact hbound b (mem_of_takeWhile124 P t b hb)
    · rw [List.takeWhile_cons_of_neg (by simpa using hp)]; rfl

/-- 前置きの `Δ` の総和はもとの総和以下。 -/
theorem le_sumDD_take124 {w : Term} (hw : inT w = true) (P : (Term × Term) → Bool) :
    ∀ (l : List (Term × Term)), (∀ ac ∈ l, inT ac.1 = true ∧ inT ac.2 = true) →
      le (sumDD112 w (l.takeWhile P)) (sumDD112 w l) = true := by
  intro l
  induction l with
  | nil => intro _; exact Evidence.WF.le_self _
  | cons ac t ih =>
    intro hin
    by_cases hp : P ac = true
    · rw [List.takeWhile_cons_of_pos hp, sumDD_cons112, sumDD_cons112]
      exact plus_mono_right_inT _ (inT_ddOf75 hw (hin ac (List.Mem.head _)).1
          (hin ac (List.Mem.head _)).2) _ _
        (inT_sumDD112 hw _ (fun a ha => hin a (List.Mem.tail _
          (mem_of_takeWhile124 P t a ha))))
        (inT_sumDD112 hw t (fun a ha => hin a (List.Mem.tail _ ha)))
        (ih (fun a ha => hin a (List.Mem.tail _ ha)))
    · rw [List.takeWhile_cons_of_neg (by simpa using hp)]
      exact Evidence.WF.le_zero_any _

/-- **一成分ぶんの分け方 — 発火する前置きだけを見た `wcnf_cons_sum120`。**
    §120.1 の `wcnf_cons_sum120` は「対がぜんぶ発火する」ことを要ったが、こちらは
    頭の成分が発火することしか要らない。 -/
theorem wcnfTakeCons124 {p : Term} (hip : inT p = true) (hpM : lt p M = true)
    (hlp : lt p (reg 1) = false) (hfire : le (reg 1) (wA (reg 1) p) = true)
    {rest : List Term} (hcr : inTL rest = true) (hdr : descL rest = true)
    (hmr : ∀ x ∈ rest, lt x M = true) :
    sumDD112 (reg 1) ((wcnf (reg 1) (p :: rest)).1.takeWhile (fun z => le (reg 1) z.1))
      = plus (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p))
          (sumDD112 (reg 1)
            ((wcnf (reg 1) rest).1.takeWhile (fun z => le (reg 1) z.1))) := by
  have hA : inT (wA (reg 1) p) = true := inT_wA109 (inT_reg 1) (isSC_reg_succ 0) hip
  have hC : inT (wC (reg 1) p) = true := inT_wC hip
  have hCM : lt (wC (reg 1) p) M = true := ltM_wC hip hpM
  have hE : inT (mulL (reg 1) (subAP (reg 1) (wA (reg 1) p))) = true :=
    inT_mulL mulDescInT (inT_reg 1) (inT_subAP hA)
  obtain ⟨_, hallR⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) rest hcr hdr hmr
  cases hr : wcnf (reg 1) rest with
  | mk fst snd =>
    have hRl : (wcnf (reg 1) rest).1 = fst := by rw [hr]
    cases fst with
    | nil =>
        have hW : (wcnf (reg 1) (p :: rest)).1 = [(wA (reg 1) p, wC (reg 1) p)] := by
          rw [wcnf_cons_ge hlp, hr]
        rw [hW,
          show ([(wA (reg 1) p, wC (reg 1) p)] : List (Term × Term)).takeWhile
              (fun z => le (reg 1) z.1)
            = (wA (reg 1) p, wC (reg 1) p) :: ([] : List (Term × Term)).takeWhile
                (fun z => le (reg 1) z.1) from List.takeWhile_cons_of_pos hfire]
        rfl
    | cons ac0 ps =>
        cases ac0 with
        | mk a' c' =>
          have hmem0 : ((a', c') : Term × Term) ∈ (wcnf (reg 1) rest).1 := by
            rw [hRl]; exact List.Mem.head _
          have hmemT : ∀ ac ∈ ps.takeWhile (fun z => le (reg 1) z.1),
              ac ∈ (wcnf (reg 1) rest).1 := by
            intro ac hac
            rw [hRl]
            exact List.Mem.tail _ (mem_of_takeWhile124 _ ps ac hac)
          have hc'i : inT c' = true := (hallR (a', c') hmem0).2.2.1
          have hc'M : lt c' M = true := (hallR (a', c') hmem0).2.2.2
          have hSps : inT (sumDD112 (reg 1) (ps.takeWhile (fun z => le (reg 1) z.1)))
              = true :=
            inT_sumDD112 (inT_reg 1) _ (fun ac hac =>
              ⟨(hallR ac (hmemT ac hac)).1, (hallR ac (hmemT ac hac)).2.2.1⟩)
          by_cases heq : (wA (reg 1) p == a') = true
          · have hpa' : a' = wA (reg 1) p := (eq_of_beq heq).symm
            subst hpa'
            have hW : (wcnf (reg 1) (p :: rest)).1
                = (wA (reg 1) p, plus (wC (reg 1) p) c') :: ps := by
              rw [wcnf_cons_ge hlp, hr]
              show ((if (wA (reg 1) p == wA (reg 1) p) = true
                     then ((wA (reg 1) p, plus (wC (reg 1) p) c') :: ps, snd)
                     else ((wA (reg 1) p, wC (reg 1) p) :: (wA (reg 1) p, c') :: ps, snd))
                    : List (Term × Term) × Term).1 = _
              rw [if_pos heq]
            have hdist : ddOf75 (reg 1) (wA (reg 1) p, plus (wC (reg 1) p) c')
                = plus (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p))
                    (ddOf75 (reg 1) (wA (reg 1) p, c')) :=
              mulL_distrib112 hE hC hc'i hCM hc'M
            show sumDD112 (reg 1) ((wcnf (reg 1) (p :: rest)).1.takeWhile
                (fun z => le (reg 1) z.1))
              = plus (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p))
                  (sumDD112 (reg 1) (((wA (reg 1) p, c') :: ps).takeWhile
                    (fun z => le (reg 1) z.1)))
            rw [hW,
              show ((wA (reg 1) p, plus (wC (reg 1) p) c') :: ps).takeWhile
                  (fun z => le (reg 1) z.1)
                = (wA (reg 1) p, plus (wC (reg 1) p) c')
                    :: ps.takeWhile (fun z => le (reg 1) z.1) from
                List.takeWhile_cons_of_pos hfire,
              show ((wA (reg 1) p, c') :: ps).takeWhile (fun z => le (reg 1) z.1)
                = (wA (reg 1) p, c') :: ps.takeWhile (fun z => le (reg 1) z.1) from
                List.takeWhile_cons_of_pos hfire,
              sumDD_cons112, sumDD_cons112, hdist]
            exact plus_assoc_inT _ _ _ (inT_ddOf75 (inT_reg 1) hA hC)
              (inT_ddOf75 (inT_reg 1) hA hc'i) hSps
          · have hW : (wcnf (reg 1) (p :: rest)).1
                = (wA (reg 1) p, wC (reg 1) p) :: (a', c') :: ps := by
              rw [wcnf_cons_ge hlp, hr]
              show ((if (wA (reg 1) p == a') = true
                     then ((wA (reg 1) p, plus (wC (reg 1) p) c') :: ps, snd)
                     else ((wA (reg 1) p, wC (reg 1) p) :: (a', c') :: ps, snd))
                    : List (Term × Term) × Term).1 = _
              rw [if_neg heq]
            show sumDD112 (reg 1) ((wcnf (reg 1) (p :: rest)).1.takeWhile
                (fun z => le (reg 1) z.1))
              = plus (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p))
                  (sumDD112 (reg 1) (((a', c') :: ps).takeWhile
                    (fun z => le (reg 1) z.1)))
            rw [hW,
              show ((wA (reg 1) p, wC (reg 1) p) :: (a', c') :: ps).takeWhile
                  (fun z => le (reg 1) z.1)
                = (wA (reg 1) p, wC (reg 1) p)
                    :: ((a', c') :: ps).takeWhile (fun z => le (reg 1) z.1) from
                List.takeWhile_cons_of_pos hfire]
            rfl

/-- **§124.1 の主定理 — 発火する成分の前置きは、その対の `Δ` の総和を `ω^{Ω₁·Ω₁}`
    倍したものそのもの。**  §120.1 の `mulL_sumDD120` は「対がぜんぶ発火する」ことを
    要ったが、こちらは要らない。発火しないところで両辺とも止まる。 -/
theorem cutFire124 : ∀ (L : List Term), inTL L = true → descL L = true →
    (∀ x ∈ L, lt x M = true) → (∀ p ∈ L, lt p (reg 1) = false) →
    mulL E120 (sumDD112 (reg 1)
        ((wcnf (reg 1) L).1.takeWhile (fun z => le (reg 1) z.1)))
      = ofList (L.takeWhile (fun q => le (reg 1) (wA (reg 1) q))) := by
  intro L
  induction L with
  | nil => intro _ _ _ _; rfl
  | cons p rest ih =>
    intro hc hd hm hge
    obtain ⟨⟨hap, hip⟩, hcr⟩ := inTL_cons.mp hc
    have hdr := descL_tail hd
    have hmr : ∀ x ∈ rest, lt x M = true := fun x hx => hm x (List.Mem.tail p hx)
    have hger : ∀ x ∈ rest, lt x (reg 1) = false := fun x hx => hge x (List.Mem.tail p hx)
    have hpM : lt p M = true := hm p (List.Mem.head _)
    have hlp : lt p (reg 1) = false := hge p (List.Mem.head _)
    have hA : inT (wA (reg 1) p) = true := inT_wA109 (inT_reg 1) (isSC_reg_succ 0) hip
    have hC : inT (wC (reg 1) p) = true := inT_wC hip
    by_cases hfire : le (reg 1) (wA (reg 1) p) = true
    · obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) rest hcr hdr hmr
      have hD : inT (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p)) = true :=
        inT_ddOf75 (inT_reg 1) hA hC
      have hDM : lt (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p)) M = true :=
        lt_of_le_of_lt3 (inT_le_fragR _ hD) (inT_le_fragR _ hip)
          (inT_le_fragR _ (show inT (M : Term) = true from rfl))
          (le_ddOf_self112 hap hip hpM) hpM
      have hSfull : inT (sumDD112 (reg 1) (wcnf (reg 1) rest).1) = true :=
        inT_sumDD112 (inT_reg 1) _ (fun ac hac => ⟨(hallOK ac hac).1, (hallOK ac hac).2.2.1⟩)
      have hS : inT (sumDD112 (reg 1)
          ((wcnf (reg 1) rest).1.takeWhile (fun z => le (reg 1) z.1))) = true :=
        inT_sumDD112 (inT_reg 1) _ (fun ac hac =>
          ⟨(hallOK ac (mem_of_takeWhile124 _ _ ac hac)).1,
           (hallOK ac (mem_of_takeWhile124 _ _ ac hac)).2.2.1⟩)
      have hSfullM : lt (sumDD112 (reg 1) (wcnf (reg 1) rest).1) M = true :=
        lt_of_le_of_lt3 (inT_le_fragR _ hSfull)
          (inT_le_fragR _ (inT_ofList rest hcr hdr))
          (inT_le_fragR _ (show inT (M : Term) = true from rfl))
          (le_sumDD_wcnf112 rest hcr hdr hmr) (lt_ofList_M _ hmr)
      have hSM : lt (sumDD112 (reg 1)
          ((wcnf (reg 1) rest).1.takeWhile (fun z => le (reg 1) z.1))) M = true :=
        lt_of_le_of_lt3 (inT_le_fragR _ hS) (inT_le_fragR _ hSfull)
          (inT_le_fragR _ (show inT (M : Term) = true from rfl))
          (le_sumDD_take124 (inT_reg 1) _ _
            (fun ac hac => ⟨(hallOK ac hac).1, (hallOK ac hac).2.2.1⟩)) hSfullM
      have hcT : inTL ((p :: rest).takeWhile (fun q => le (reg 1) (wA (reg 1) q))) = true :=
        inTL_takeWhile124 _ hc
      have hdT : descL ((p :: rest).takeWhile (fun q => le (reg 1) (wA (reg 1) q)))
          = true := descL_takeWhile124 _ (p :: rest) hc hd
      have hsp : (p :: rest).takeWhile (fun q => le (reg 1) (wA (reg 1) q))
          = p :: rest.takeWhile (fun q => le (reg 1) (wA (reg 1) q)) :=
        List.takeWhile_cons_of_pos hfire
      rw [hsp] at hcT hdT
      rw [hsp, wcnfTakeCons124 hip hpM hlp hfire hcr hdr hmr,
        mulL_distrib112 inT_E120 hD hS hDM hSM,
        mulL_ddOf_self120 hap hip hpM (lt_false_of_le120 (inT_reg 1) hA hfire),
        ih hcr hdr hmr hger]
      exact plus_ofList_cons112 p _ hcT hdT
    · obtain ⟨c, ps, he⟩ := wcnfFstHd109 rest hlp
      rw [show (p :: rest).takeWhile (fun q => le (reg 1) (wA (reg 1) q))
            = [] from List.takeWhile_cons_of_neg
              (show ¬ ((fun q => le (reg 1) (wA (reg 1) q)) p = true) from hfire), he,
        show ((wA (reg 1) p, c) :: ps).takeWhile (fun z => le (reg 1) z.1)
            = [] from List.takeWhile_cons_of_neg
              (show ¬ ((fun z : Term × Term => le (reg 1) z.1)
                ((wA (reg 1) p, c) : Term × Term) = true) from hfire)]
      rfl

end

/-! ### §124.2 折り畳みが持つ指数は、発火する前置きの指数 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 発火しない対の並びでは、折り畳みの指数はまったく動かない。 -/
theorem foldNotFire124 {w base : Term} : ∀ (t : List (Term × Term)),
    (∀ ac ∈ t, le w ac.1 = false) →
    ∀ (s : Option Term × Option Term), (t.foldl (stepF w base) s).1 = s.1 := by
  intro t
  induction t with
  | nil => intro _ s; rfl
  | cons ac r ih =>
    intro hnf s
    rw [List.foldl_cons, ih (fun a ha => hnf a (List.Mem.tail _ ha)), stepF_fst,
      if_neg (by rw [hnf ac (List.Mem.head _)]; exact fun hcon => Bool.noConfusion hcon)]

/-- 折り畳みは `takeWhile` と `dropWhile` に割れる。 -/
theorem foldl_split124 {α β : Type} (f : β → α → β) (P : α → Bool) :
    ∀ (l : List α) (b : β),
      l.foldl f b = (l.dropWhile P).foldl f ((l.takeWhile P).foldl f b) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro b
    by_cases h : P a = true
    · rw [List.takeWhile_cons_of_pos h, List.dropWhile_cons_of_pos h,
        List.foldl_cons, List.foldl_cons]
      exact ih (f b a)
    · rw [List.takeWhile_cons_of_neg (show ¬ (P a = true) from h),
        List.dropWhile_cons_of_neg (show ¬ (P a = true) from h)]
      rfl

/-- **指数は前置きだけで決まる。**  §109.1 の `fireSplit109` が後半をぜんぶ黙らせる。 -/
theorem idxTake124 {X : Term} (hX : inT X = true) :
    idxF88 0 X
      = (((wcnf (reg 1) (toList X)).1.takeWhile (fun z => le (reg 1) z.1)).foldl
          (stepF (reg 1) (baseOf 0))
          ((none : Option Term), (none : Option Term))).1 := by
  obtain ⟨hc, hd⟩ := inT_toList X hX
  have hfold : (wcnf (reg 1) (toList X)).1.foldl (stepF (reg 1) (baseOf 0))
        ((none : Option Term), (none : Option Term))
      = ((wcnf (reg 1) (toList X)).1.dropWhile (fun z => le (reg 1) z.1)).foldl
          (stepF (reg 1) (baseOf 0))
          (((wcnf (reg 1) (toList X)).1.takeWhile (fun z => le (reg 1) z.1)).foldl
            (stepF (reg 1) (baseOf 0))
            ((none : Option Term), (none : Option Term))) :=
    foldl_split124 (stepF (reg 1) (baseOf 0)) (fun z => le (reg 1) z.1)
      (wcnf (reg 1) (toList X)).1 ((none : Option Term), (none : Option Term))
  show ((wcnf (reg 1) (toList X)).1.foldl
    (init := ((none : Option Term), (none : Option Term)))
    (stepF (reg 1) (baseOf 0))).1 = _
  rw [hfold]
  exact foldNotFire124 _
    (fireSplit109 (show (reg 1).isSC = true from isSC_reg_succ 0) (inT_reg 1)
      (show (reg 1).isAP = true from rfl) (toList X) hc hd) _

/-- **`1 ⊕ j` は前置きの `Δ` の総和。**  §120.2 の `plus_one_idx120` の、
    前置きだけを見た形。 -/
theorem sumTake124 {X : Term} (hX : inT X = true) (hXM : lt X M = true)
    {ac : Term × Term} {t : List (Term × Term)}
    (hps : (wcnf (reg 1) (toList X)).1.takeWhile (fun z => le (reg 1) z.1) = ac :: t)
    {j : Term} (hj : idxF88 0 X = some j) :
    inT j = true ∧ plus TM.Term.one j
      = sumDD112 (reg 1)
          ((wcnf (reg 1) (toList X)).1.takeWhile (fun z => le (reg 1) z.1)) := by
  obtain ⟨hc, hd⟩ := inT_toList X hX
  have hmL := ltM_toList X hX hXM
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList X) hc hd hmL
  have hmem : ∀ x ∈ ac :: t, x ∈ (wcnf (reg 1) (toList X)).1 := by
    intro x hx
    exact mem_of_takeWhile124 _ _ x (by rw [hps]; exact hx)
  have hin : ∀ x ∈ ac :: t, inT x.1 = true ∧ inT x.2 = true := by
    intro x hx
    exact ⟨(hallOK x (hmem x hx)).1, (hallOK x (hmem x hx)).2.2.1⟩
  have hfire : ∀ x ∈ ac :: t, le (reg 1) x.1 = true := by
    intro x hx
    exact mem_takeWhile109 _ _ x (by rw [hps]; exact hx)
  have hD : inT (ddOf75 (reg 1) ac) = true :=
    inT_ddOf75 (inT_reg 1) (hin ac (List.Mem.head _)).1 (hin ac (List.Mem.head _)).2
  have hS : inT (sumDD112 (reg 1) t) = true :=
    inT_sumDD112 (inT_reg 1) t (fun a ha => hin a (List.Mem.tail _ ha))
  have hfold : idxF88 0 X
      = some (plus (sub1 (ddOf75 (reg 1) ac)) (sumDD112 (reg 1) t)) := by
    rw [idxTake124 hX, hps]
    exact foldNone120 (inT_reg 1) ac t hin hfire
  have hjeq : j = plus (sub1 (ddOf75 (reg 1) ac)) (sumDD112 (reg 1) t) :=
    Option.some.inj (hj.symm.trans hfold)
  have hcnz : ac.2 ≠ zero :=
    wcnf_cnz109 (inT_reg 1) (isSC_reg_succ 0) (toList X) hc hd hmL ac
      (hmem ac (List.Mem.head _))
  have hDnz : ddOf75 (reg 1) ac ≠ zero := ddOf_ne_zero84 hcnz
  have hD1 : lt (ddOf75 (reg 1) ac) TM.Term.one = false := by
    cases hcc : lt (ddOf75 (reg 1) ac) TM.Term.one with
    | false => rfl
    | true =>
        exact absurd (below_one _ hD (fuelOf (ddOf75 (reg 1) ac) TM.Term.one) hcc) hDnz
  refine ⟨by rw [hjeq]; exact inT_plus (inT_sub1 hD) hS, ?_⟩
  rw [hjeq,
    ← plus_assoc_inT TM.Term.one (sub1 (ddOf75 (reg 1) ac)) (sumDD112 (reg 1) t)
      inT_one (inT_sub1 hD) hS,
    sub1_eq_subAP112,
    plus_subAP112 inT_one (show (TM.Term.one).isAP = true from rfl) hD hD1,
    hps, sumDD_cons112]

/-- **§124.2 の主定理 — 割り算は前置きの上で成り立つ。**  発火の仮定は一つも要らず、
    指数を持ってさえいればよい。§120.4 が名指しした「`=` を `≤` に緩める」道は、
    実は緩めなくてよい: 右辺を項そのものではなく**発火する前置き**にすれば等式である。 -/
theorem divCut124 {X j : Term} (hX : inT X = true) (hXM : lt X M = true)
    (hXh : ∀ p ∈ toList X, lt p (reg 1) = false) (hj : idxF88 0 X = some j) :
    inT j = true ∧ lt (plus TM.Term.one j) M = true
      ∧ mulL E120 (plus TM.Term.one j)
        = ofList ((toList X).takeWhile (fun q => le (reg 1) (wA (reg 1) q))) := by
  obtain ⟨hc, hd⟩ := inT_toList X hX
  have hmL := ltM_toList X hX hXM
  have hne : ∃ ac t,
      (wcnf (reg 1) (toList X)).1.takeWhile (fun z => le (reg 1) z.1) = ac :: t := by
    cases hps : (wcnf (reg 1) (toList X)).1.takeWhile (fun z => le (reg 1) z.1) with
    | nil =>
        exfalso
        rw [idxTake124 hX, hps] at hj
        exact Option.some_ne_none j (show (some j : Option Term) = none from hj.symm)
    | cons ac t => exact ⟨ac, t, rfl⟩
  obtain ⟨ac, t, hps⟩ := hne
  obtain ⟨hij, hsum⟩ := sumTake124 hX hXM hps hj
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList X) hc hd hmL
  have hSfull : inT (sumDD112 (reg 1) (wcnf (reg 1) (toList X)).1) = true :=
    inT_sumDD112 (inT_reg 1) _ (fun z hz => ⟨(hallOK z hz).1, (hallOK z hz).2.2.1⟩)
  have hS : inT (sumDD112 (reg 1)
      ((wcnf (reg 1) (toList X)).1.takeWhile (fun z => le (reg 1) z.1))) = true :=
    inT_sumDD112 (inT_reg 1) _ (fun z hz =>
      ⟨(hallOK z (mem_of_takeWhile124 _ _ z hz)).1,
       (hallOK z (mem_of_takeWhile124 _ _ z hz)).2.2.1⟩)
  have hSfullX : le (sumDD112 (reg 1) (wcnf (reg 1) (toList X)).1) X = true := by
    have h2 := le_sumDD_wcnf112 (toList X) hc hd hmL
    rw [inT_ofList_toList X hX] at h2
    exact h2
  have hSfullM : lt (sumDD112 (reg 1) (wcnf (reg 1) (toList X)).1) M = true :=
    lt_of_le_of_lt3 (inT_le_fragR _ hSfull) (inT_le_fragR _ hX)
      (inT_le_fragR _ (show inT (M : Term) = true from rfl)) hSfullX hXM
  have hSM : lt (sumDD112 (reg 1)
      ((wcnf (reg 1) (toList X)).1.takeWhile (fun z => le (reg 1) z.1))) M = true :=
    lt_of_le_of_lt3 (inT_le_fragR _ hS) (inT_le_fragR _ hSfull)
      (inT_le_fragR _ (show inT (M : Term) = true from rfl))
      (le_sumDD_take124 (inT_reg 1) _ _
        (fun z hz => ⟨(hallOK z hz).1, (hallOK z hz).2.2.1⟩)) hSfullM
  refine ⟨hij, by rw [hsum]; exact hSM, ?_⟩
  rw [hsum]
  exact cutFire124 (toList X) hc hd hmL hXh

end

/-! ### §124.3 切り口はどこでも順序を保つ -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- **§89.4 の `lt_append_hi89` を、切り口を `Ω₁` に固定しない形に引き直す。**
    元の証明が `reg 1` を使うのは「尾の頭 < 頭部の頭」を出す一箇所だけなので、
    そこを交叉の仮定そのものに置き換える。 -/
theorem lt_append_cut124 : ∀ (Hy Hx : List Term), inTL Hy = true → inTL Hx = true →
    descL Hy = true → descL Hx = true →
    ∀ (Ly Lx : List Term), inTL Ly = true → inTL Lx = true →
    descL (Hy ++ Ly) = true → descL (Hx ++ Lx) = true →
    (∀ p ∈ Hx, ∀ q ∈ Ly, lt q p = true) →
    lt (ofList Hy) (ofList Hx) = true →
    lt (ofList (Hy ++ Ly)) (ofList (Hx ++ Lx)) = true := by
  intro Hy
  induction Hy with
  | nil =>
    intro Hx _ hcx _ hdx Ly Lx hcLy hcLx hdyL hdxL hcross hlt
    cases Hx with
    | nil =>
      exfalso
      rw [show ofList ([] : List Term) = zero from rfl, lt_irrefl] at hlt
      exact Bool.noConfusion hlt
    | cons cx Hx' =>
      have hcxL : inTL (cx :: (Hx' ++ Lx)) = true := inTL_append89 hcx hcLx
      have hiT : inT (ofList (cx :: (Hx' ++ Lx))) = true := inT_ofList _ hcxL hdxL
      cases Ly with
      | nil =>
        show lt (ofList ([] : List Term)) (ofList (cx :: (Hx' ++ Lx))) = true
        exact lt_zero_left (ofList_ne_zero81 _ (List.cons_ne_nil _ _) (fun z hz =>
          ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcxL z hz)).1))
      | cons l1 Ly' =>
        have hcyL : inTL (l1 :: Ly') = true := hcLy
        have hiS : inT (ofList (l1 :: Ly')) = true := inT_ofList _ hcyL hdyL
        refine lt_of_hd_lt hiS hiT (toList_ofList89 hcyL) (toList_ofList89 hcxL) ?_
        exact hcross cx (List.Mem.head _) l1 (List.Mem.head _)
  | cons cy Hy' ih =>
    intro Hx hcy hcx hdy hdx Ly Lx hcLy hcLx hdyL hdxL hcross hlt
    cases Hx with
    | nil =>
      exfalso
      rw [show ofList ([] : List Term) = zero from rfl, lt_zero_right] at hlt
      exact Bool.noConfusion hlt
    | cons cx Hx' =>
      obtain ⟨⟨_, hicy⟩, hcy'⟩ := inTL_cons.mp hcy
      obtain ⟨⟨_, hicx⟩, hcx'⟩ := inTL_cons.mp hcx
      have hdy' := descL_tail hdy
      have hdx' := descL_tail hdx
      have hdyL' := descL_tail hdyL
      have hdxL' := descL_tail hdxL
      have hcyL : inTL (cy :: (Hy' ++ Ly)) = true := inTL_append89 hcy hcLy
      have hcxL : inTL (cx :: (Hx' ++ Lx)) = true := inTL_append89 hcx hcLx
      have hiSL : inT (ofList (cy :: (Hy' ++ Ly))) = true := inT_ofList _ hcyL hdyL
      have hiTL : inT (ofList (cx :: (Hx' ++ Lx))) = true := inT_ofList _ hcxL hdxL
      by_cases hcc : cy = cx
      · subst hcc
        have hiHy : inT (ofList (cy :: Hy')) = true := inT_ofList _ hcy hdy
        have hiHx : inT (ofList (cy :: Hx')) = true := inT_ofList _ hcx hdx
        have hiHy' : inT (ofList Hy') = true := inT_ofList _ hcy' hdy'
        have hiHx' : inT (ofList Hx') = true := inT_ofList _ hcx' hdx'
        have hrec : lt (ofList Hy') (ofList Hx') = true :=
          lt_hd_eq_inv89 hiHy hiHx (toList_ofList89 hcy) (toList_ofList89 hcx)
            hiHy' hiHx' (toList_ofList89 hcy') (toList_ofList89 hcx') hlt
        have hIH := ih Hx' hcy' hcx' hdy' hdx' Ly Lx hcLy hcLx hdyL' hdxL'
          (fun p hp q hq => hcross p (List.Mem.tail _ hp) q hq) hrec
        exact lt_of_hd_eq77 hiSL hiTL (toList_ofList89 hcyL) (toList_ofList89 hcxL) hIH
      · have hiHy : inT (ofList (cy :: Hy')) = true := inT_ofList _ hcy hdy
        have hiHx : inT (ofList (cx :: Hx')) = true := inT_ofList _ hcx hdx
        have hle : le cy cx = true := hd_mono_inT hiHy hiHx
          (toList_ofList89 hcy) (toList_ofList89 hcx) (le_of_lt hlt)
        have hlcc : lt cy cx = true := by
          rcases (Bool.or_eq_true _ _).mp hle with hq | hl
          · exact absurd (eq_of_beq hq) hcc
          · exact hl
        exact lt_of_hd_lt hiSL hiTL (toList_ofList89 hcyL) (toList_ofList89 hcxL) hlcc

/-- **発火しない成分は後ろにまとまる。**  §109.1 の `fireMono109` を成分の側で使う。 -/
theorem dropNotFire124 : ∀ (L : List Term), inTL L = true → descL L = true →
    (∀ p ∈ L, lt p (reg 1) = false) →
    ∀ q ∈ L.dropWhile (fun z => le (reg 1) (wA (reg 1) z)),
      le (reg 1) (wA (reg 1) q) = false := by
  intro L
  induction L with
  | nil => intro _ _ _ q hq; cases hq
  | cons p rest ih =>
    intro hc hd hge q hq
    obtain ⟨⟨hap, hip⟩, hcr⟩ := inTL_cons.mp hc
    have hdr := descL_tail hd
    have hger : ∀ x ∈ rest, lt x (reg 1) = false := fun x hx => hge x (List.Mem.tail p hx)
    have hlp : lt p (reg 1) = false := hge p (List.Mem.head _)
    by_cases hf : le (reg 1) (wA (reg 1) p) = true
    · rw [show (p :: rest).dropWhile (fun z => le (reg 1) (wA (reg 1) z))
          = rest.dropWhile (fun z => le (reg 1) (wA (reg 1) z)) from
        List.dropWhile_cons_of_pos hf] at hq
      exact ih hcr hdr hger q hq
    · rw [show (p :: rest).dropWhile (fun z => le (reg 1) (wA (reg 1) z))
          = p :: rest from List.dropWhile_cons_of_neg
            (show ¬ ((fun z => le (reg 1) (wA (reg 1) z)) p = true) from hf)] at hq
      rcases List.mem_cons.mp hq with h1 | h1
      · rw [h1]; exact bool_false hf
      · cases hq2 : le (reg 1) (wA (reg 1) q) with
        | false => rfl
        | true =>
            exfalso
            have hiq : inT q = true :=
              ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcr q h1)).2
            have haq : q.isAP = true :=
              ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcr q h1)).1
            have hqp : le q p = true := descL_bound_inT rest p hip hcr hd q h1
            exact absurd (fireMono109 (show (reg 1).isSC = true from isSC_reg_succ 0)
              (inT_reg 1) (show (reg 1).isAP = true from rfl) hap hip hlp haq hiq
              (hger q h1) hqp hq2) hf

/-- **§124.3 の主定理 — 「発火する成分だけを残す」写像は順序を保つ。** -/
theorem cutMono124 {X Y : Term} (hX : inT X = true) (hY : inT Y = true)
    (hXh : ∀ p ∈ toList X, lt p (reg 1) = false)
    (hYh : ∀ p ∈ toList Y, lt p (reg 1) = false)
    (h : lt X Y = true) :
    le (ofList ((toList X).takeWhile (fun q => le (reg 1) (wA (reg 1) q))))
       (ofList ((toList Y).takeWhile (fun q => le (reg 1) (wA (reg 1) q)))) = true := by
  obtain ⟨hcX, hdX⟩ := inT_toList X hX
  obtain ⟨hcY, hdY⟩ := inT_toList Y hY
  have hsX : (toList X).takeWhile (fun q => le (reg 1) (wA (reg 1) q))
      ++ (toList X).dropWhile (fun q => le (reg 1) (wA (reg 1) q)) = toList X :=
    List.takeWhile_append_dropWhile
  have hsY : (toList Y).takeWhile (fun q => le (reg 1) (wA (reg 1) q))
      ++ (toList Y).dropWhile (fun q => le (reg 1) (wA (reg 1) q)) = toList Y :=
    List.takeWhile_append_dropWhile
  have hiCX : inT (ofList ((toList X).takeWhile (fun q => le (reg 1) (wA (reg 1) q))))
      = true := inT_ofList _ (inTL_takeWhile124 _ hcX) (descL_takeWhile124 _ _ hcX hdX)
  have hiCY : inT (ofList ((toList Y).takeWhile (fun q => le (reg 1) (wA (reg 1) q))))
      = true := inT_ofList _ (inTL_takeWhile124 _ hcY) (descL_takeWhile124 _ _ hcY hdY)
  cases hcc : le (ofList ((toList X).takeWhile (fun q => le (reg 1) (wA (reg 1) q))))
      (ofList ((toList Y).takeWhile (fun q => le (reg 1) (wA (reg 1) q)))) with
  | true => rfl
  | false =>
      exfalso
      have h2 := lt_of_not_le_inT hiCX hiCY hcc
      have hcross : ∀ p ∈ (toList X).takeWhile (fun q => le (reg 1) (wA (reg 1) q)),
          ∀ q ∈ (toList Y).dropWhile (fun q => le (reg 1) (wA (reg 1) q)),
            lt q p = true := by
        intro p hp q hq
        have hpm : p ∈ toList X := mem_of_takeWhile124 _ _ p hp
        have hqm : q ∈ toList Y := mem_of_dropWhile124 _ _ q hq
        have hfp : le (reg 1) (wA (reg 1) p) = true := mem_takeWhile109 _ _ p hp
        have hfq : le (reg 1) (wA (reg 1) q) = false := dropNotFire124 (toList Y) hcY hdY hYh q hq
        have hip : inT p = true :=
          ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcX p hpm)).2
        have hap : p.isAP = true :=
          ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcX p hpm)).1
        have hiq : inT q = true :=
          ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcY q hqm)).2
        have haq : q.isAP = true :=
          ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcY q hqm)).1
        cases hlq : lt q p with
        | true => rfl
        | false =>
            exfalso
            have hpq : le p q = true :=
              le_of_not_lt3 (inT_le_fragR _ hiq) (inT_le_fragR _ hip) hlq
            have hfq2 : le (reg 1) (wA (reg 1) q) = true :=
              fireMono109 (show (reg 1).isSC = true from isSC_reg_succ 0)
                (inT_reg 1) (show (reg 1).isAP = true from rfl) haq hiq (hYh q hqm)
                hap hip (hXh p hpm) hpq hfp
            rw [hfq] at hfq2
            exact Bool.noConfusion hfq2
      have h3 := lt_append_cut124
        ((toList Y).takeWhile (fun q => le (reg 1) (wA (reg 1) q)))
        ((toList X).takeWhile (fun q => le (reg 1) (wA (reg 1) q)))
        (inTL_takeWhile124 _ hcY) (inTL_takeWhile124 _ hcX)
        (descL_takeWhile124 _ _ hcY hdY) (descL_takeWhile124 _ _ hcX hdX)
        ((toList Y).dropWhile (fun q => le (reg 1) (wA (reg 1) q)))
        ((toList X).dropWhile (fun q => le (reg 1) (wA (reg 1) q)))
        (inTL_dropWhile124 _ hcY) (inTL_dropWhile124 _ hcX)
        (by rw [hsY]; exact hdY) (by rw [hsX]; exact hdX)
        hcross h2
      rw [hsY, hsX, inT_ofList_toList Y hY, inT_ofList_toList X hX] at h3
      rw [lt_asymm_inT hX hY h] at h3
      exact Bool.noConfusion h3

end

/-! ### §124.4 条項 — 逆写像は前置きの上にある -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- **§124 の主定理 — 指数を持つ二つの折り畳みでは、`hi` の比較が指数の比較。**
    §120.3 の `idxMono_core120` と同じ形だが、**発火の仮定がどちらの側にも無い**。
    結論が非狭義になるのがその代償で、§109 の `not_idxLtMix109` がそれが代償では
    なく真実であることを言っている。 -/
theorem idxLe_core124 {X Y jX jY : Term}
    (hX : inT X = true) (hXM : lt X M = true) (hY : inT Y = true) (hYM : lt Y M = true)
    (hXh : ∀ p ∈ toList X, lt p (reg 1) = false)
    (hYh : ∀ p ∈ toList Y, lt p (reg 1) = false)
    (hjX : idxF88 0 X = some jX) (hjY : idxF88 0 Y = some jY)
    (h : lt X Y = true) : le jX jY = true := by
  obtain ⟨hijX, hMX, hcx⟩ := divCut124 hX hXM hXh hjX
  obtain ⟨hijY, hMY, hcy⟩ := divCut124 hY hYM hYh hjY
  have hmono := cutMono124 hX hY hXh hYh h
  rw [← hcx, ← hcy] at hmono
  cases hcc : le jX jY with
  | true => rfl
  | false =>
      exfalso
      have hlt : lt jY jX = true := lt_of_not_le_inT hijX hijY hcc
      have h1 : lt (plus TM.Term.one jY) (plus TM.Term.one jX) = true :=
        plus_smono_right_inT79 TM.Term.one inT_one jY jX hijY hijX hlt
      have h2 : lt (mulL E120 (plus TM.Term.one jY))
          (mulL E120 (plus TM.Term.one jX)) = true :=
        mulL_smono_right110 inT_E120 (inT_plus inT_one hijY) (inT_plus inT_one hijX)
          hMY hMX h1
      have hiA : inT (mulL E120 (plus TM.Term.one jX)) = true :=
        inT_mulL mulDescInT inT_E120 (inT_plus inT_one hijX)
      have hiB : inT (mulL E120 (plus TM.Term.one jY)) = true :=
        inT_mulL mulDescInT inT_E120 (inT_plus inT_one hijY)
      rcases (Bool.or_eq_true _ _).mp hmono with he | hl2
      · rw [eq_of_beq he, lt_irrefl] at h2; exact Bool.noConfusion h2
      · rw [lt_asymm_inT hiA hiB hl2] at h2; exact Bool.noConfusion h2

/-- `hi` を戻した形。 -/
theorem idxLe_hiW124 {X Y jX jY : Term} (hX : inT X = true) (hXM : lt X M = true)
    (hY : inT Y = true) (hYM : lt Y M = true)
    (hjX : idxF88 0 X = some jX) (hjY : idxF88 0 Y = some jY)
    (h : lt (hiW89 X) (hiW89 Y) = true) : le jX jY = true :=
  idxLe_core124 (inT_hiW89 hX) (ltM_hiW112 hX hXM) (inT_hiW89 hY) (ltM_hiW112 hY hYM)
    (hiW89_ge89 hX) (hiW89_ge89 hY)
    (by rw [idxF_hiW101 hX]; exact hjX) (by rw [idxF_hiW101 hY]; exact hjY) h

/-- **発火の条件をどちらの側にも課さない条項。**  §109 の `IdxLeMix109` も
    §120 が閉じた `IdxMono101` の非狭義版も、これの特別な場合である。 -/
def IdxLeAny124 : Prop :=
  ∀ (a b : BT) (ja jb : Term), btLe72 1 a = true → btLe72 1 b = true →
    BT.isStd a = true → BT.isStd b = true →
    idxF88 0 (dict a) = some ja → idxF88 0 (dict b) = some jb →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true → le ja jb = true

/-- **`IdxLeAny124` は定理である。**  `PsiIdxOKStd172` は `dict a` が 𝔗(M) の項で
    あることにだけ使う — §120 の `idxMono101_of_psi120` と同じ理由。 -/
theorem idxLeAny124_of_psi124 (Hp : PsiIdxOKStd172) : IdxLeAny124 := by
  intro a b ja jb hba hbb hsa hsb hja hjb hlt
  obtain ⟨hia, hiaM⟩ := inT_dict_of_std172 Hp a hba hsa
  obtain ⟨hib, hibM⟩ := inT_dict_of_std172 Hp b hbb hsb
  exact idxLe_hiW124 hia hiaM hib hibM hja hjb hlt

/-- **§109 の `IdxLeMix109` は定理である。**  発火の仮定は二つとも使わない。 -/
theorem idxLeMix109_of_psi124 (Hp : PsiIdxOKStd172) : IdxLeMix109 := by
  intro a b ja jb hba hbb hsa hsb _hfa _hfb hja hjb hlt
  exact idxLeAny124_of_psi124 Hp a b ja jb hba hbb hsa hsb hja hjb hlt

/-- **`HiMono89` は二つの条項に架け替わる。**  §120 の三つから `IdxLeMix109` が落ちる。 -/
theorem hiMono_of_two124 (Hp : PsiIdxOKStd172) (H1 : VebIngF114) (H2 : VebRest117) :
    HiMono89 :=
  hiMono_of_three120 Hp (idxLeMix109_of_psi124 Hp) H1 H2

/-- **326 行目を架け替える。** -/
theorem certIn_t326_124 (Hp : PsiIdxOKStd172) (H1 : VebIngF114) (H2 : VebRest117)
    (HD1 : DictOntoMidOpen103) (HD3 : DictDenseMid107) (HD4 : DictDenseAbove107)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_120 Hp (idxLeMix109_of_psi124 Hp) H1 H2 HD1 HD3 HD4 hacc

end

/-! ### §124.5 否定と段の正直さ -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 発火の条件を課さないまま**狭義**を求めた条項。 -/
def IdxLtAny124 : Prop :=
  ∀ (a b : BT) (ja jb : Term), btLe72 1 a = true → btLe72 1 b = true →
    BT.isStd a = true → BT.isStd b = true →
    idxF88 0 (dict a) = some ja → idxF88 0 (dict b) = some jb →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true → lt ja jb = true

/-- **狭義は偽 — §109 の証人がそのまま効く。**  `IdxLeAny124` が非狭義なのは
    弱めたのではない。 -/
theorem not_idxLtAny124 : ¬ IdxLtAny124 := by
  intro H
  exact not_idxLtMix109 (fun a b ja jb h1 h2 h3 h4 _ _ h7 h8 h9 =>
    H a b ja jb h1 h2 h3 h4 h7 h8 h9)

/-- **組んだ証人 — 発火する成分が二つ、そのあとに発火しない成分。**
    `ψ₁⁴0 ⊕ ψ₁³0 ⊕ Ω₁`、13 記号。`K` 標準で `Ω₁ ≤ dict`、最後の対は発火せず、
    指数はあり、成分 3 個のうち**前の 2 個が発火する**。§124 の恒等式
    `ω^{Ω₁·Ω₁}·(1 ⊕ j) = 前置き` はここで成り立ち、§120 の恒等式
    `ω^{Ω₁·Ω₁}·ΣΔ = hi` はここで**成り立たない**。§124.6 の母集団はこの形を
    一つも含まない (`noTwoCut124`) ので、これは組んだのであって拾ったのではない。 -/
def sepCut124 : BT := BT.sum (wt120 3) (BT.sum (wt120 2) w1_101)

/-- 成分の前置き — 測定と証人が見る量。 -/
def cutL124 (x : Term) : List Term :=
  (toList x).takeWhile (fun q => le (reg 1) (wA (reg 1) q))

set_option maxRecDepth 10000 in
/-- **証人の性質、凍結。** -/
theorem sepCutFacts124 :
    (btLe72 1 sepCut124, BT.isStd sepCut124, BT.isStd (BT.D 0 sepCut124),
     le (reg 1) (dict sepCut124), lastFire92 (dict sepCut124),
     (idxF88 0 (dict sepCut124)).isSome,
     (cutL124 (hiW89 (dict sepCut124))).length,
     (toList (hiW89 (dict sepCut124))).length,
     mulL E120 (plus TM.Term.one ((idxF88 0 (dict sepCut124)).getD zero))
       == ofList (cutL124 (hiW89 (dict sepCut124))),
     mulL E120 (sumDD112 (reg 1) (wcnf (reg 1) (toList (dict sepCut124))).1)
       == hiW89 (dict sepCut124),
     BT.size sepCut124)
    = (true, true, true, true, false, true, 2, 3, true, false, 13) := rfl
/-- **一段上の証人 — 発火する成分が三つ。**  `ψ₁⁵0 ⊕ ψ₁⁴0 ⊕ ψ₁³0 ⊕ Ω₁`、20 記号。
    §124.6 の**どちらの**母集団もこの形を含まない。 -/
def sepCut2124 : BT := BT.sum (wt120 4) (BT.sum (wt120 3) (BT.sum (wt120 2) w1_101))

set_option maxRecDepth 10000 in
/-- **一段上の証人の性質、凍結。** -/
theorem sepCut2Facts124 :
    (btLe72 1 sepCut2124, BT.isStd sepCut2124, BT.isStd (BT.D 0 sepCut2124),
     le (reg 1) (dict sepCut2124), lastFire92 (dict sepCut2124),
     (idxF88 0 (dict sepCut2124)).isSome,
     (cutL124 (hiW89 (dict sepCut2124))).length,
     (toList (hiW89 (dict sepCut2124))).length,
     mulL E120 (plus TM.Term.one ((idxF88 0 (dict sepCut2124)).getD zero))
       == ofList (cutL124 (hiW89 (dict sepCut2124))),
     mulL E120 (sumDD112 (reg 1) (wcnf (reg 1) (toList (dict sepCut2124))).1)
       == hiW89 (dict sepCut2124),
     BT.size sepCut2124)
    = (true, true, true, true, false, true, 3, 4, true, false, 20) := rfl

end

/-! ### §124.6 測定 (凍結)

**構成 — 発火する線と発火しない線を両方組み、濾さない。**  §109.5 の作り方をそのまま
借りる。発火するのは `ψ₁` の塔で、発火しないのは帽子 `ψ₁ψ₀ z` と `Ω₁` 自身。

    fireSeed124  発火する側の種 5 個
    vebSeed124   発火しない側の種 5 個 (`Ω₁` と帽子 4 個)
    pop124       その 2 項和・`a ⊕ b ⊕ b` の形の 3 項和も入れた 120 項  濾さない
    popB124      3 項和を**三つとも別**にし、種を 1 個足した 363 項 — 大きさは同じ
                 (どちらも最大 32 記号) で、**形だけ**を広げた対照

`pop124` は「発火する成分が二つ続いてから発火しない成分が来る」形を一つも含まない。
`popB124` はそれを 90 項含む。**足りなかったのは深さではなく形である。** -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

def dedup124 (l : List BT) : List BT :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []

def fireSeed124 : List BT :=
  [w2_101, w3_101, BT.D 1 w3_101, BT.D 1 (BT.sum w2_101 w2_101),
   BT.D 1 (BT.sum w3_101 w3_101)]
def vebSeed124 : List BT :=
  [w1_101, BT.D 1 (BT.D 0 w1_101), BT.D 1 (BT.D 0 w2_101),
   BT.D 1 (BT.D 0 (BT.sum w2_101 w1_101)), BT.D 1 (BT.D 0 (BT.sum w3_101 w2_101))]
def seeds124 : List BT := fireSeed124 ++ vebSeed124

def pop124 : List BT :=
  dedup124 (seeds124
    ++ seeds124.flatMap (fun a => (seeds124.filter (fun b => BT.le b a)).map (BT.sum a))
    ++ seeds124.flatMap (fun a => (seeds124.filter (fun b => BT.le b a)).map
         (fun b => BT.sum a (BT.sum b b))))

def ok124 (a : BT) : Bool :=
  btLe72 1 a && BT.isStd a && BT.isStd (BT.D 0 a) && le (reg 1) (dict a)
def hasIdx124 (a : BT) : Bool := (idxF88 0 (dict a)).isSome
def fr124 (a : BT) : Bool := lastFire92 (dict a)
def jOf124 (a : BT) : Term := (idxF88 0 (dict a)).getD zero
/-- §124 の恒等式 — `ω^{Ω₁·Ω₁}·(1 ⊕ j)` は発火する成分の前置きか。 -/
def divOK124 (a : BT) : Bool :=
  mulL E120 (plus TM.Term.one (jOf124 a)) == ofList (cutL124 (hiW89 (dict a)))
/-- §120 の恒等式 — `ω^{Ω₁·Ω₁}·ΣΔ` は `hi` そのものか。 -/
def recOK124 (a : BT) : Bool :=
  mulL E120 (sumDD112 (reg 1) (wcnf (reg 1) (toList (dict a))).1) == hiW89 (dict a)
def nCut124 (a : BT) : Nat := (cutL124 (hiW89 (dict a))).length
def nComp124 (a : BT) : Nat := (toList (hiW89 (dict a))).length
def properCut124 (a : BT) : Bool := 0 < nCut124 a && nCut124 a < nComp124 a

def samp124 : List BT := pop124.filter ok124
def fireS124 : List BT := samp124.filter fr124
def vebS124 : List BT := samp124.filter (fun a => !fr124 a)
def idxS124 : List BT := samp124.filter hasIdx124
def vebI124 : List BT := vebS124.filter hasIdx124
def noIdx124 : List BT := samp124.filter (fun a => !hasIdx124 a)

def pairs124 (l l' : List BT) : List (BT × BT) :=
  l.flatMap (fun a => l'.map (fun b => (a, b)))
def resid124 (l l' : List BT) : List (BT × BT) :=
  (pairs124 l l').filter (fun p => lt (hiW89 (dict p.1)) (hiW89 (dict p.2)))
def leBad124 (l l' : List BT) : List (BT × BT) :=
  (resid124 l l').filter (fun p => !(le (jOf124 p.1) (jOf124 p.2)))
def ltBad124 (l l' : List BT) : List (BT × BT) :=
  (resid124 l l').filter (fun p => !(lt (jOf124 p.1) (jOf124 p.2)))

def seedB124 : List BT := fireSeed124 ++ vebSeed124 ++ [wt120 4]
def popB124 : List BT :=
  dedup124 (seedB124
    ++ seedB124.flatMap (fun a => (seedB124.filter (fun b => BT.le b a)).map (BT.sum a))
    ++ seedB124.flatMap (fun a => (seedB124.filter (fun b => BT.le b a)).flatMap
         (fun b => (seedB124.filter (fun c => BT.le c b)).map
           (fun c => BT.sum a (BT.sum b c)))))
def sampB124 : List BT := popB124.filter ok124
def idxB124 : List BT := sampB124.filter hasIdx124

set_option maxRecDepth 100000 in
/-- **段の正直さ — 定理として。**  どちらの母集団も段 1 に収まり、段 0 に落ちるものは
    一つもない。 -/
theorem levelHonest124 :
    (pop124.all (fun a => btLe72 1 a), pop124.countP (fun a => btLe72 0 a),
     popB124.all (fun a => btLe72 1 a), popB124.countP (fun a => btLe72 0 a))
    = (true, 0, true, 0) := rfl

/-! 母集団の形。**120 項のうち `K` 標準は 89 項、最大 32 記号。指数を持つのは 70 項で、
    そのうち最後の対が発火するのは 24 項、しないのは 46 項。指数を持たないのが 19 項。** -/
set_option maxRecDepth 100000 in
#guard (pop124.length, samp124.length, fireS124.length, vebS124.length,
        idxS124.length, vebI124.length, noIdx124.length,
        (pop124.map BT.size).foldl (fun a b => if a < b then b else a) 0)
    == (120, 89, 24, 65, 70, 46, 19, 32)

/-! **受領 1 — この節そのものが一行で見える。**  §124 の恒等式は**指数を持つ 70 項で
    70 回**成り立つ。§120 の恒等式は**同じ 70 項で 24 回** — 発火する側だけ。
    掃いても仮定が見えない (§93 の失敗) のではない。**§124 には仮定が無い。** -/
set_option maxRecDepth 100000 in
#guard (idxS124.countP divOK124, idxS124.countP recOK124,
        fireS124.countP recOK124, vebI124.countP recOK124, vebI124.countP divOK124)
    == (70, 24, 24, 0, 46)

/-! **受領 2 — 前置きは本当に真の前置き。**  89 項のうち 46 項で発火する成分が
    成分列の途中で切れる。**その 46 項でだけ** §120 の恒等式が破れ §124 のが成り立つ。 -/
set_option maxRecDepth 100000 in
#guard (samp124.countP properCut124, vebI124.countP properCut124,
        fireS124.countP properCut124) == (46, 46, 0)

/-! **受領 3 — 条項、見えている。狭義は数で反証されている。**  両側が指数を持つ残余の
    対は 2415 組、`ja ≤ jb` の破れ **0**、`ja < jb` の破れ **289**。四つの場合で
    (発火, 発火) 276/0/0、(発火, Veblen) 358/0/**46**、(Veblen, 発火) 746/0/0、
    (Veblen, Veblen) **1035**/0/**243**。**最後の場合はこの file のどの条項も
    覆っていなかった** — `IdxMono101` は両側の発火を、`IdxLeMix109` は `a` の発火を要る。 -/
set_option maxRecDepth 100000 in
#guard ((resid124 fireS124 fireS124).length, (leBad124 fireS124 fireS124).length,
        (ltBad124 fireS124 fireS124).length,
        (resid124 fireS124 vebI124).length, (leBad124 fireS124 vebI124).length,
        (ltBad124 fireS124 vebI124).length,
        (resid124 vebI124 fireS124).length, (leBad124 vebI124 fireS124).length,
        (ltBad124 vebI124 fireS124).length,
        (resid124 vebI124 vebI124).length, (leBad124 vebI124 vebI124).length,
        (ltBad124 vebI124 vebI124).length)
    == (276, 0, 0, 358, 0, 46, 746, 0, 0, 1035, 0, 243)

/-! **受領 4 — この母集団に見えない仮定を、見えると言わない。**  89 項の残余の対 3916 組の
    うち、`a` が指数を持ち `b` が持たないものは **0 組** (§109.2 が数として見えている)。
    「`b` が指数を持つ」は濾しになっていない。要るのは**構造上**の理由 —
    それが無ければ比べる `jb` が無い — であって、測定が必要性を示したのではない。 -/
set_option maxRecDepth 100000 in
#guard ((resid124 samp124 samp124).length,
        (resid124 samp124 samp124).countP (fun p => hasIdx124 p.1 && !hasIdx124 p.2),
        (resid124 idxS124 idxS124).length, (leBad124 idxS124 idxS124).length,
        (ltBad124 idxS124 idxS124).length)
    == (3916, 0, 2415, 0, 289)

/-! **受領 5 — 母集団が言えない形があり、それは大きさの話ではなかった (§111 と §116 の
    使い分け)。**  `pop124` の 46 の真の前置きは**すべて発火する成分がちょうど 1 個**で、
    「2 個以上発火してから発火しない成分が来る」形は **120 項・最大 32 記号で 0 回**。
    証人は文から**組んだ** (`sepCut124`、13 記号)。そのあとで形だけを広げた `popB124`
    — 363 項、**最大は同じ 32 記号** — がその形を **90 項**持つ。**深さを足しても
    出なかった。足りなかったのは形である。**  三つ以上はどちらの母集団にも無い。 -/
set_option maxRecDepth 100000 in
#guard (vebI124.countP (fun a => 2 ≤ nCut124 a),
        popB124.length, sampB124.length, idxB124.length,
        idxB124.countP divOK124, idxB124.countP recOK124,
        idxB124.countP (fun a => properCut124 a && 2 ≤ nCut124 a),
        idxB124.countP (fun a => properCut124 a && 3 ≤ nCut124 a),
        (popB124.map BT.size).foldl (fun a b => if a < b then b else a) 0)
    == (0, 363, 304, 274, 274, 55, 90, 0, 32)

end

/-! ## §123 THE DIVISION SURVIVES A VEBLEN TAIL ON THE LEFT — HALF OF `VebIngF114` IS A
       THEOREM, AND `§117` GAINS NOTHING HERE

§114 split §109's hard half at the shape of `b`'s fold and handed on two clauses.  `VebRest114`
got §117 and `IdxMono101` got §120.  **`VebIngF114` has had no section of its own**, and its
statement is a decidable condition on ONE term against ONE target:

    `VebIng114 (dict a) (ψ_{Ω₁} j_b)` = every non-firing pair's exponent and coefficient
      below the target,  AND  `ψ_{Ω₁}` of `a`'s own collapse index below the target.

**§123 proves the second conjunct and shows the first is the whole clause.**  `VebIngF114` is
NOT proved and NOT refuted; what §123 does is replace it by `VebPairs123` — the same statement
with the index conjunct deleted — and prove that the deletion is sound.  §123.4's
`vebIngF_iff_pairs123` states the honest half of that in one line: the two clauses are
**equivalent**, so §123 removes a conjunct, not a residue.

WHAT IS PROVED.

  §123.1  **THE DIVISION SURVIVES A PREFIX** (`preDiv123`).  §120.1 proved
          `ω^(Ω₁·Ω₁)·ΣΔ = X` when every base-`Ω₁` pair of `X` fires.  Run the same induction
          on the FIRING PREFIX alone and the equality becomes `≤`: `wcnf_cons_take123` is
          §120.1's `wcnf_cons_sum120` with "every pair fires" cut down to "the head pair
          fires" — which is all its two branches ever read — and the non-firing head simply
          empties the prefix.  `ltM_sumDD123` supplies the size bound §120 got for free from
          `le_sumDD_wcnf112`, which does not survive the cut.

  §123.2  **THE INDEX IS THE PREFIX'S INDEX** (`preIdx123`, `foldFst_take123`).  §114.2's
          `fold_fst_veb114` says the Veblen steps never touch the index slot, so `idxF88` is
          the prefix's fold; then §120.2's `foldNone120` and the `⊖ 1` payback give
          `1 ⊕ j = ΣΔ(prefix)` **without `lastFire92`**.

  §123.3  **THE CLAUSE** (`idxLtMixF123`).  Put the two together against a `b` that all-fires:
          `ω^(Ω₁·Ω₁)·(1 ⊕ j_a) ≤ hi a < hi b = ω^(Ω₁·Ω₁)·(1 ⊕ j_b)`, and the contrapositive
          of two non-strict maps gives `j_a < j_b` — §120.3's argument with `=` weakened to
          `≤` on one side.  **This is the route §120.4 named and declined**: "with that,
          `lastFire92 (dict a)` could be replaced by §109.2's free `idxF88 0 (dict a) ≠ none`
          … §120 does not run it: the clause it was asked to prove does not ask for it."  The
          clause §123 was asked to prove does ask for it.  `idxMono_noFireA123` is §120's own
          `IdxMono101` with the `a`-side firing hypothesis gone, which §120.5 measured as
          breaking 0 times in 388 pairs and claimed nothing about.

  §123.4  **THE SPLIT** (`vebIdx_true123`, `vebIngF_of_pairs123`).  `VebIng114` is
          `vebPair123 && vebIdx123` (`vebIng_eq123`, `rfl`), the second conjunct is §123.3,
          and `VebPairs123` is the first alone.  `hiMono_of_three123` and `certIn_t326_123`
          re-hang `HiMono89` and row 326.  `vebIngF_iff_pairs123` : the two clauses are
          equivalent — **§123 moves no residue.**

  §123.5  **§117's TOOL GIVES NOTHING HERE, AND THAT IS A THEOREM** (`tgtOK_false123`,
          `closed_eq123`).  §117 wrote that `hiMono_closed117` "could also be pointed at
          `VebIngF114`'s half but that doing so was out of its scope."  Pointing it there is
          free and worth nothing: when `b` all-fires, cutting its pair list anywhere leaves
          either a firing pair in the tail or the whole list, and the value at the end is a
          `ψ_{Ω₁}`, never a `φ̄` — so `tgtOK117 a b k = false` for EVERY `k`, and
          `closed117 a b` collapses to `VebIng114` itself.  With §123.4 it collapses further,
          to `vebPair123` (`closed_eq_pairs123`).

  §123.6  the negatives and the level honesty; §123.7 the measurement.

WHAT IS **NOT** CLAIMED.  **`VebIngF114` is NOT proved.**  `VebPairs123` is unproved, and by
`vebIngF_iff_pairs123` it is exactly as strong as `VebIngF114` was.  What §123 delivers is
that the clause's two conjuncts are not of equal difficulty: one is a theorem of the same
hypotheses, the other is the whole of it, and what the other needs is the `BT`-side fact §114
named — a `K`-standard `a` below such a `b` cannot name an exponent or a coefficient at or
above `ψ_{Ω₁}(j_b)` — which is §90.1 translated into 𝔗(M), and §90 says plainly that this
translation is what nobody has.  `IdxLeMix109`, `VebRest117`, `PsiIdxOKStd172`,
`DictOntoMidOpen103`, `DictDenseMid107`, `DictDenseAbove107` are untouched.  Row 326 rests on
`PsiIdxOKStd172`, `IdxLeMix109`, **`VebPairs123`**, `VebRest117`, `DictOntoMidOpen103`,
`DictDenseMid107`, `DictDenseAbove107` (`certIn_t326_123`).

**THE LEDGER, thirteenth entry, and it is against §114 — mildly.**  `VebIng114` was written as
one decidable condition and handed on as one clause.  Half of it never needed a clause: the
index conjunct follows from the hypotheses `VebIngF114` already carries, by machinery that
§120 built for a different branch and explicitly declined to generalise.  **Check what your
statement READS**: §114's own measurement said the condition and the conclusion "agree exactly"
on the all-fire class, which is true and which hid that one of its two conjuncts is free.

**WHERE §123 STOPPED, PRECISELY.**  At `vebPair123`.  §114's built reversal `revA114` fails it
at the exponent (`Γ₀ ⊕ 1 ≥ Γ₀ = ψ_{Ω₁}(0)`) and satisfies the index conjunct vacuously — it
has no collapse index at all — so §123's theorem does not touch the witness that made the
clause necessary, and §123.6 says so in the witness's own numbers.

WHAT THE MEASUREMENT SAYS (§123.7 gives the construction).  §114.5's three seed lines plus a
fourth BUILT for this section — a FIRING PREFIX carrying a VEBLEN TAIL, which is the exact
shape §123.3 reads and §120.3 cannot — 149 terms with their two-term sums, nothing filtered.

  * **The proved conjunct is not vacuous and not idle.**  Of the 815 residual pairs in the
    all-fire half, **325 have an `a` with a collapse index**, i.e. 325 where §123.4's
    conclusion says something and §120.3's theorem cannot be applied at all.  §114's own
    population already had 119 of them; the fourth line multiplies that by 2.7 but was **not**
    needed to see the shape — that is reported, not hidden.
  * **The split lands where it says.**  On the same 815 pairs `VebIng114` fails 15 times,
    **all 15 in `vebPair123` and 0 in `vebIdx123`** — as it must, `vebIdx123` being a theorem
    there.  On the 549 `K`-standard ones nothing fails at all.
  * **And one class over the other conjunct is the one that fails.**  Where `b` has an index
    but a Veblen tail — §117's class, where §123.3's hypothesis is absent — `vebIdx123` fails
    **96** times in 2255 pairs and `vebPair123` 106 times.  `sepR114` is the smallest of the
    96, and it is `K`-standard on both sides.  **The `b`-side all-fire hypothesis is exactly
    what makes §123.4 a theorem**, and dropping it makes the statement false.
  * **§117's route fires 0 times here and 1154 times next door.**  `tgtOK117` is true at no
    `k` on any of the 815 all-fire pairs, and true on 1154 of the 2850 other residual pairs.
    Not a sweep that could not see its subject: `closed117` equals `VebIng114` on all 815 and
    is true on 800 of them.
  * **The breaks have no index.**  All 15 breaks in the all-fire half have an `a` with NO
    collapse index, so §123's theorem is vacuous at every one of them — the residue is in
    `vebPair123` and nowhere else.  14 of the 15 reverse the order.
  * **The induction is not about singletons, and the merge branch is not idle.**  64 terms
    have two or more base-`Ω₁` pairs and 10 have three or more; **10 carry a firing prefix of
    length ≥ 2 under a Veblen tail** (the shape §123.1's induction actually walks), and
    `wcnf` really merges components on 19, four of them in that class.
  * **Size, checked.**  A second population up to 49 symbols (272 terms, against 31 and 149)
    has 3383 pairs in the all-fire half, **1843 of them with an `a`-side index**, and still
    **0 `vebIdx123` failures and 0 `tgtOK117` firings**; 29 terms carry three or more pairs
    where the first population had 10.  Depth is added; behaviour is not. -/

/-! ### §123.1 発火する前置きだけの割り算 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 発火する対の前置き。 -/
abbrev fireTake123 (l : List (Term × Term)) : List (Term × Term) :=
  l.takeWhile (fun z => le (reg 1) z.1)

/-- 発火する頭は前置きに入る。 -/
theorem fireTake_cons123 (ac : Term × Term) (t : List (Term × Term))
    (h : le (reg 1) ac.1 = true) : fireTake123 (ac :: t) = ac :: fireTake123 t :=
  List.takeWhile_cons_of_pos h

/-- 発火しない頭で前置きは切れる。 -/
theorem fireTake_cons_neg123 (ac : Term × Term) (t : List (Term × Term))
    (h : le (reg 1) ac.1 = false) : fireTake123 (ac :: t) = [] :=
  List.takeWhile_cons_of_neg (by rw [h]; exact Bool.noConfusion)

/-- 前置きの元は元の列の元。 -/
theorem mem_of_takeWhile123 {a : Type} (p : a → Bool) : ∀ (l : List a) (x : a),
    x ∈ l.takeWhile p → x ∈ l
  | [], x, h => by cases h
  | b :: t, x, h => by
      by_cases hb : p b = true
      · rw [List.takeWhile_cons_of_pos hb] at h
        rcases List.mem_cons.mp h with h1 | h1
        · rw [h1]; exact List.Mem.head _
        · exact List.Mem.tail _ (mem_of_takeWhile123 p t x h1)
      · rw [List.takeWhile_cons_of_neg hb] at h; cases h

/-- 前置きの `Δ` の総和を頭の成分で割る。§120.1 の `wcnf_cons_sum120` を、
    「全部の対が発火する」ではなく「頭の対が発火する」だけで。 -/
theorem wcnf_cons_take123 {p : Term} (hip : inT p = true) (hpM : lt p M = true)
    (hlp : lt p (reg 1) = false) {rest : List Term} (hcr : inTL rest = true)
    (hdr : descL rest = true) (hmr : ∀ x ∈ rest, lt x M = true)
    (hfire : le (reg 1) (wA (reg 1) p) = true) :
    sumDD112 (reg 1) (fireTake123 (wcnf (reg 1) (p :: rest)).1)
      = plus (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p))
          (sumDD112 (reg 1) (fireTake123 (wcnf (reg 1) rest).1)) := by
  have hA : inT (wA (reg 1) p) = true := inT_wA109 (inT_reg 1) (isSC_reg_succ 0) hip
  have hC : inT (wC (reg 1) p) = true := inT_wC hip
  have hCM : lt (wC (reg 1) p) M = true := ltM_wC hip hpM
  have hE : inT (mulL (reg 1) (subAP (reg 1) (wA (reg 1) p))) = true :=
    inT_mulL mulDescInT (inT_reg 1) (inT_subAP hA)
  obtain ⟨_, hallR⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) rest hcr hdr hmr
  cases hr : wcnf (reg 1) rest with
  | mk fst snd =>
    have hRl : (wcnf (reg 1) rest).1 = fst := by rw [hr]
    cases fst with
    | nil =>
        have hW : (wcnf (reg 1) (p :: rest)).1 = [(wA (reg 1) p, wC (reg 1) p)] := by
          rw [wcnf_cons_ge hlp, hr]
        show sumDD112 (reg 1) (fireTake123 (wcnf (reg 1) (p :: rest)).1)
            = plus (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p))
                (sumDD112 (reg 1) (fireTake123 ([] : List (Term × Term))))
        rw [hW, fireTake_cons123 (wA (reg 1) p, wC (reg 1) p) [] hfire]
        rfl
    | cons ac0 ps =>
        cases ac0 with
        | mk a' c' =>
          have hmem0 : ((a', c') : Term × Term) ∈ (wcnf (reg 1) rest).1 := by
            rw [hRl]; exact List.Mem.head _
          have hc'i : inT c' = true := (hallR (a', c') hmem0).2.2.1
          have hc'M : lt c' M = true := (hallR (a', c') hmem0).2.2.2
          have hSps : inT (sumDD112 (reg 1) (fireTake123 ps)) = true :=
            inT_sumDD112 (inT_reg 1) _ (fun ac hac =>
              ⟨(hallR ac (by rw [hRl]
                             exact List.Mem.tail _ (mem_of_takeWhile123 _ _ _ hac))).1,
               (hallR ac (by rw [hRl]
                             exact List.Mem.tail _ (mem_of_takeWhile123 _ _ _ hac))).2.2.1⟩)
          by_cases heq : (wA (reg 1) p == a') = true
          · have hpa' : a' = wA (reg 1) p := (eq_of_beq heq).symm
            subst hpa'
            have hW : (wcnf (reg 1) (p :: rest)).1
                = (wA (reg 1) p, plus (wC (reg 1) p) c') :: ps := by
              rw [wcnf_cons_ge hlp, hr]
              show ((if (wA (reg 1) p == wA (reg 1) p) = true
                     then ((wA (reg 1) p, plus (wC (reg 1) p) c') :: ps, snd)
                     else ((wA (reg 1) p, wC (reg 1) p) :: (wA (reg 1) p, c') :: ps, snd))
                    : List (Term × Term) × Term).1 = _
              rw [if_pos heq]
            have hdist : ddOf75 (reg 1) (wA (reg 1) p, plus (wC (reg 1) p) c')
                = plus (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p))
                    (ddOf75 (reg 1) (wA (reg 1) p, c')) :=
              mulL_distrib112 hE hC hc'i hCM hc'M
            show sumDD112 (reg 1) (fireTake123 (wcnf (reg 1) (p :: rest)).1)
                = plus (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p))
                    (sumDD112 (reg 1) (fireTake123 ((wA (reg 1) p, c') :: ps)))
            rw [hW, fireTake_cons123 (wA (reg 1) p, plus (wC (reg 1) p) c') ps hfire,
              fireTake_cons123 (wA (reg 1) p, c') ps hfire,
              sumDD_cons112, sumDD_cons112, hdist]
            exact plus_assoc_inT _ _ _ (inT_ddOf75 (inT_reg 1) hA hC)
              (inT_ddOf75 (inT_reg 1) hA hc'i) hSps
          · have hW : (wcnf (reg 1) (p :: rest)).1
                = (wA (reg 1) p, wC (reg 1) p) :: (a', c') :: ps := by
              rw [wcnf_cons_ge hlp, hr]
              show ((if (wA (reg 1) p == a') = true
                     then ((wA (reg 1) p, plus (wC (reg 1) p) c') :: ps, snd)
                     else ((wA (reg 1) p, wC (reg 1) p) :: (a', c') :: ps, snd))
                    : List (Term × Term) × Term).1 = _
              rw [if_neg heq]
            show sumDD112 (reg 1) (fireTake123 (wcnf (reg 1) (p :: rest)).1)
                = plus (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p))
                    (sumDD112 (reg 1) (fireTake123 ((a', c') :: ps)))
            rw [hW, fireTake_cons123 (wA (reg 1) p, wC (reg 1) p) ((a', c') :: ps) hfire,
              sumDD_cons112]

/-- `Δ` は `M` の下。 -/
theorem ltM_ddOf123 {ac : Term × Term} (h1 : inT ac.1 = true) (h1M : lt ac.1 M = true)
    (h2 : inT ac.2 = true) (h2M : lt ac.2 M = true) :
    lt (ddOf75 (reg 1) ac) M = true :=
  ltM_mulL (inT_mulL mulDescInT (inT_reg 1) (inT_subAP h1)) h2
    (ltM_mulL (inT_reg 1) (inT_subAP h1) (ltM_reg 1) (ltM_subAP h1 h1M)) h2M

/-- `Δ` の総和も `M` の下 — 対の列がどれでも。 -/
theorem ltM_sumDD123 : ∀ (l : List (Term × Term)),
    (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
    lt (sumDD112 (reg 1) l) M = true
  | [], _ => lt_zero_left (by intro hcc; exact Term.noConfusion hcc)
  | ac :: t, h => by
      rw [sumDD_cons112]
      have h0 := h ac (List.Mem.head _)
      have ht : ∀ z ∈ t, inT z.1 = true ∧ lt z.1 M = true ∧ inT z.2 = true
          ∧ lt z.2 M = true := fun z hz => h z (List.Mem.tail _ hz)
      exact lt_plus_M (inT_ddOf75 (inT_reg 1) h0.1 h0.2.2.1)
        (inT_sumDD112 (inT_reg 1) t (fun z hz => ⟨(ht z hz).1, (ht z hz).2.2.1⟩))
        (ltM_ddOf123 h0.1 h0.2.1 h0.2.2.1 h0.2.2.2) (ltM_sumDD123 t ht)

/-- **§123.1 の主定理 — 発火する前置きだけを割っても、`Ω₁^{Ω₁}` 倍は項を超えない。**
    §120.1 の等号は「対がぜんぶ発火する」ときのもの。前置きだけなら **`≤`** になる
    — それが `lastFire92` を仮定しない側で要るものである。 -/
theorem preDiv123 : ∀ (L : List Term), inTL L = true → descL L = true →
    (∀ x ∈ L, lt x M = true) →
    le (mulL E120 (sumDD112 (reg 1) (fireTake123 (wcnf (reg 1) L).1))) (ofList L) = true := by
  intro L
  induction L with
  | nil =>
      intro _ _ _
      show le (mulL E120 zero) (ofList ([] : List Term)) = true
      rw [mulL_zero112]
      exact Evidence.Region.le_zero_left _
  | cons p rest ih =>
    intro hc hd hm
    obtain ⟨⟨hap, hip⟩, hcr⟩ := inTL_cons.mp hc
    have hdr := descL_tail hd
    have hmr : ∀ x ∈ rest, lt x M = true := fun x hx => hm x (List.Mem.tail p hx)
    have hpM : lt p M = true := hm p (List.Mem.head _)
    by_cases hlp : lt p (reg 1) = true
    · have hW : (wcnf (reg 1) (p :: rest)).1 = [] := by rw [wcnf_cons_lt hlp]
      rw [hW]
      show le (mulL E120 zero) (ofList (p :: rest)) = true
      rw [mulL_zero112]
      exact Evidence.Region.le_zero_left _
    · have hlp' : lt p (reg 1) = false := bool_false hlp
      have hA : inT (wA (reg 1) p) = true := inT_wA109 (inT_reg 1) (isSC_reg_succ 0) hip
      have hC : inT (wC (reg 1) p) = true := inT_wC hip
      by_cases hf : le (reg 1) (wA (reg 1) p) = true
      · obtain ⟨_, hallR⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) rest hcr hdr hmr
        have hSmem : ∀ ac ∈ fireTake123 (wcnf (reg 1) rest).1,
            inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true :=
          fun ac hac => hallR ac (mem_of_takeWhile123 _ _ _ hac)
        have hS : inT (sumDD112 (reg 1) (fireTake123 (wcnf (reg 1) rest).1)) = true :=
          inT_sumDD112 (inT_reg 1) _ (fun ac hac => ⟨(hSmem ac hac).1, (hSmem ac hac).2.2.1⟩)
        have hSM : lt (sumDD112 (reg 1) (fireTake123 (wcnf (reg 1) rest).1)) M = true :=
          ltM_sumDD123 _ hSmem
        have hD : inT (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p)) = true :=
          inT_ddOf75 (inT_reg 1) hA hC
        have hDM : lt (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p)) M = true :=
          lt_of_le_of_lt3 (inT_le_fragR _ hD) (inT_le_fragR _ hip)
            (inT_le_fragR _ (show inT (M : Term) = true from rfl))
            (le_ddOf_self112 hap hip hpM) hpM
        rw [wcnf_cons_take123 hip hpM hlp' hcr hdr hmr hf,
          mulL_distrib112 inT_E120 hD hS hDM hSM,
          mulL_ddOf_self120 hap hip hpM (lt_false_of_le120 (inT_reg 1) hA hf),
          ← plus_ofList_cons112 p rest hc hd]
        exact plus_mono_right_inT p hip _ _ (inT_mulL mulDescInT inT_E120 hS)
          (inT_ofList rest hcr hdr) (ih hcr hdr hmr)
      · obtain ⟨c, ps, he⟩ := wcnfFstHd109 (w := reg 1) rest hlp'
        have hW : fireTake123 (wcnf (reg 1) (p :: rest)).1 = [] := by
          rw [he]
          exact fireTake_cons_neg123 (wA (reg 1) p, c) ps (bool_false hf)
        rw [hW]
        show le (mulL E120 zero) (ofList (p :: rest)) = true
        rw [mulL_zero112]
        exact Evidence.Region.le_zero_left _

/-! ### §123.2 前置きが出す指数 -/

/-- **Veblen の尾は指数の枠を触らないから、指数は前置きだけで決まる。** -/
theorem foldFst_take123 (l : List (Term × Term))
    (hV : ∀ ac ∈ l.dropWhile (fun z : Term × Term => le (reg 1) z.1),
      le (reg 1) ac.1 = false) :
    (l.foldl (stepF (reg 1) (baseOf 0)) ((none : Option Term), (none : Option Term))).1
      = ((fireTake123 l).foldl (stepF (reg 1) (baseOf 0))
          ((none : Option Term), (none : Option Term))).1 := by
  have hFV : fireTake123 l ++ l.dropWhile (fun z : Term × Term => le (reg 1) z.1) = l :=
    List.takeWhile_append_dropWhile
  have h1 : (l.foldl (stepF (reg 1) (baseOf 0))
        ((none : Option Term), (none : Option Term))).1
      = ((fireTake123 l ++ l.dropWhile (fun z : Term × Term => le (reg 1) z.1)).foldl
          (stepF (reg 1) (baseOf 0)) ((none : Option Term), (none : Option Term))).1 := by
    rw [hFV]
  rw [h1, List.foldl_append]
  exact fold_fst_veb114 _ _ hV

/-- 前置きの総和の型と大きさ。 -/
theorem sumFire_facts123 {X : Term} (hX : inT X = true) (hXM : lt X M = true) :
    inT (sumDD112 (reg 1) (fireTake123 (wcnf (reg 1) (toList X)).1)) = true
      ∧ lt (sumDD112 (reg 1) (fireTake123 (wcnf (reg 1) (toList X)).1)) M = true := by
  obtain ⟨hc, hd⟩ := inT_toList X hX
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList X) hc hd
    (ltM_toList X hX hXM)
  have hmem : ∀ ac ∈ fireTake123 (wcnf (reg 1) (toList X)).1,
      inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true :=
    fun ac hac => hallOK ac (mem_of_takeWhile123 _ _ _ hac)
  exact ⟨inT_sumDD112 (inT_reg 1) _ (fun ac hac => ⟨(hmem ac hac).1, (hmem ac hac).2.2.1⟩),
    ltM_sumDD123 _ hmem⟩

/-- **§123.2 の主定理 — `1 ⊕ j` は発火する前置きの `Δ` の総和そのもの。**
    §120.2 の `plus_one_idx120` は「対がぜんぶ発火する」ときのもの。折り畳みの
    Veblen の尾は指数の枠を触らない (§114.2 の `fold_fst_veb114`) から、
    **発火が前置きでありさえすれば同じ等式が立つ** — `lastFire92` は要らない。 -/
theorem preIdx123 {X : Term} (hX : inT X = true) (hXM : lt X M = true)
    {j : Term} (hj : idxF88 0 X = some j) :
    inT j = true ∧ plus TM.Term.one j
      = sumDD112 (reg 1) (fireTake123 (wcnf (reg 1) (toList X)).1) := by
  obtain ⟨hc, hd⟩ := inT_toList X hX
  have hmL := ltM_toList X hX hXM
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList X) hc hd hmL
  have hVveb : ∀ ac ∈ (wcnf (reg 1) (toList X)).1.dropWhile
      (fun z : Term × Term => le (reg 1) z.1), le (reg 1) ac.1 = false :=
    fireSplit109 (isSC_reg_succ 0) (inT_reg 1) (show (reg 1).isAP = true from rfl)
      (toList X) hc hd
  have hidx : idxF88 0 X
      = ((fireTake123 (wcnf (reg 1) (toList X)).1).foldl (stepF (reg 1) (baseOf 0))
          ((none : Option Term), (none : Option Term))).1 :=
    foldFst_take123 _ hVveb
  cases hFT : fireTake123 (wcnf (reg 1) (toList X)).1 with
  | nil =>
      exfalso
      have hnone : idxF88 0 X = none := by rw [hidx, hFT]; rfl
      rw [hnone] at hj
      cases hj
  | cons ac t =>
      have hFT' : (wcnf (reg 1) (toList X)).1.takeWhile
          (fun z : Term × Term => le (reg 1) z.1) = ac :: t := hFT
      have hfire : ∀ x ∈ ac :: t, le (reg 1) x.1 = true := by
        intro x hx
        exact mem_takeWhile109 (fun z : Term × Term => le (reg 1) z.1)
          (wcnf (reg 1) (toList X)).1 x (by rw [hFT']; exact hx)
      have hin : ∀ x ∈ ac :: t, inT x.1 = true ∧ inT x.2 = true := by
        intro x hx
        have h2 := hallOK x (mem_of_takeWhile123 (fun z : Term × Term => le (reg 1) z.1)
          (wcnf (reg 1) (toList X)).1 x (by rw [hFT']; exact hx))
        exact ⟨h2.1, h2.2.2.1⟩
      have hD : inT (ddOf75 (reg 1) ac) = true :=
        inT_ddOf75 (inT_reg 1) (hin ac (List.Mem.head _)).1 (hin ac (List.Mem.head _)).2
      have hS : inT (sumDD112 (reg 1) t) = true :=
        inT_sumDD112 (inT_reg 1) t (fun a ha => hin a (List.Mem.tail _ ha))
      have hfold : idxF88 0 X
          = some (plus (sub1 (ddOf75 (reg 1) ac)) (sumDD112 (reg 1) t)) := by
        rw [hidx, hFT]
        exact foldNone120 (inT_reg 1) ac t hin hfire
      have hjeq : j = plus (sub1 (ddOf75 (reg 1) ac)) (sumDD112 (reg 1) t) :=
        Option.some.inj (hj.symm.trans hfold)
      have hcnz : ac.2 ≠ zero :=
        wcnf_cnz109 (inT_reg 1) (isSC_reg_succ 0) (toList X) hc hd hmL ac
          (mem_of_takeWhile123 (fun z : Term × Term => le (reg 1) z.1)
            (wcnf (reg 1) (toList X)).1 ac (by rw [hFT']; exact List.Mem.head _))
      have hDnz : ddOf75 (reg 1) ac ≠ zero := ddOf_ne_zero84 hcnz
      have hD1 : lt (ddOf75 (reg 1) ac) TM.Term.one = false := by
        cases hcc : lt (ddOf75 (reg 1) ac) TM.Term.one with
        | false => rfl
        | true =>
            exact absurd (below_one _ hD (fuelOf (ddOf75 (reg 1) ac) TM.Term.one) hcc) hDnz
      refine ⟨by rw [hjeq]; exact inT_plus (inT_sub1 hD) hS, ?_⟩
      rw [hjeq,
        ← plus_assoc_inT TM.Term.one (sub1 (ddOf75 (reg 1) ac)) (sumDD112 (reg 1) t)
          inT_one (inT_sub1 hD) hS,
        sub1_eq_subAP112,
        plus_subAP112 inT_one (show (TM.Term.one).isAP = true from rfl) hD hD1,
        sumDD_cons112]

/-! ### §123.3 条項 — 逆写像は Veblen の尾を左に残しても効く -/

/-- **§123.3 の主定理 — 割り算の逆は Veblen の尾を左に残しても効く。**
    §120.3 の `idxMono_core120` は両側が全発火することを仮定する。
    `X` の側は「指数を持つ」だけでよい: 等号が `≤` になるだけで、対偶は同じに通る。
    **§120.4 が名指しして走らなかった道である。** -/
theorem idxLtMixF123 {X Y jX jY : Term}
    (hX : inT X = true) (hXM : lt X M = true) (hY : inT Y = true) (hYM : lt Y M = true)
    (hYh : ∀ p ∈ toList Y, lt p (reg 1) = false)
    (hfY : lastFire92 Y = true)
    (hjX : idxF88 0 X = some jX) (hjY : idxF88 0 Y = some jY)
    (h : lt X Y = true) : lt jX jY = true := by
  obtain ⟨hijX, hsumX⟩ := preIdx123 hX hXM hjX
  obtain ⟨hSX, hSXM⟩ := sumFire_facts123 hX hXM
  obtain ⟨hijY, hSY, hSYM, hsumY, hrecY⟩ := allFireData120 hY hYM hYh hfY hjY
  obtain ⟨hc, hd⟩ := inT_toList X hX
  have hleX : le (mulL E120 (sumDD112 (reg 1) (fireTake123 (wcnf (reg 1) (toList X)).1)))
      X = true := by
    have h2 := preDiv123 (toList X) hc hd (ltM_toList X hX hXM)
    rw [inT_ofList_toList X hX] at h2
    exact h2
  cases hcc : lt jX jY with
  | true => rfl
  | false =>
      exfalso
      have hle : le jY jX = true :=
        le_of_not_lt3 (inT_le_fragR _ hijX) (inT_le_fragR _ hijY) hcc
      have h1 : le (plus TM.Term.one jY) (plus TM.Term.one jX) = true :=
        plus_mono_right_inT TM.Term.one inT_one jY jX hijY hijX hle
      rw [hsumX, hsumY] at h1
      have h2 := mulL_mono_right112 inT_E120 hSY hSX hSYM hSXM h1
      rw [hrecY] at h2
      have h3 : le Y X = true :=
        le_trans3 (inT_le_fragR _ hY)
          (inT_le_fragR _ (inT_mulL mulDescInT inT_E120 hSX))
          (inT_le_fragR _ hX) h2 hleX
      rcases (Bool.or_eq_true _ _).mp h3 with he | hl
      · rw [eq_of_beq he, lt_irrefl] at h; exact Bool.noConfusion h
      · rw [lt_asymm_inT hX hY h] at hl; exact Bool.noConfusion hl

end

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-! ### §123.4 分割 — `VebIng114` の二つの連言 -/

/-- `hi` を付けた形 — §120.3 の `idxMono_hiW120` から `a` 側の全発火の仮定を外したもの。 -/
theorem idxLtMixF_hiW123 {X Y jX jY : Term} (hX : inT X = true) (hXM : lt X M = true)
    (hY : inT Y = true) (hYM : lt Y M = true) (hfY : lastFire92 Y = true)
    (hjX : idxF88 0 X = some jX) (hjY : idxF88 0 Y = some jY)
    (h : lt (hiW89 X) (hiW89 Y) = true) : lt jX jY = true :=
  idxLtMixF123 (inT_hiW89 hX) (ltM_hiW112 hX hXM) (inT_hiW89 hY) (ltM_hiW112 hY hYM)
    (hiW89_ge89 hY) (by rw [lastFire_hiW101 hY]; exact hfY)
    (by rw [idxF_hiW101 hX]; exact hjX) (by rw [idxF_hiW101 hY]; exact hjY) h

/-- `VebIng114` の第一連言 — 発火しない対の指数と係数が的の下にあるか。 -/
def vebPair123 (x S : Term) : Bool :=
  (wcnf (reg 1) (toList x)).1.all (fun ac => le (reg 1) ac.1 || (lt ac.1 S && lt ac.2 S))

/-- `VebIng114` の第二連言 — 発火する前置きが出す `ψ_{Ω₁}` が的の下にあるか。 -/
def vebIdx123 (x S : Term) : Bool :=
  match idxF88 0 x with | none => true | some i => lt (psi (reg 1) i) S

/-- §114 の成分の条件は、この二つの連言そのもの。 -/
theorem vebIng_eq123 (x S : Term) : VebIng114 x S = (vebPair123 x S && vebIdx123 x S) := rfl

/-- **§123.4 の主定理 — `VebIng114` の第二連言は定理である。**  `b` が全発火する
    ところでは `ψ_{Ω₁}` の的は割り算の像そのもので、`a` の指数は前置きだけで
    決まる。`a` の側の全発火も `K` の条件も**一度も読まない**。 -/
theorem vebIdx_true123 (Hp : PsiIdxOKStd172) {a b : BT} {jb : Term}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hbB : btLe72 1 (BT.D 0 b) = true)
    (hsA : BT.isStd (BT.D 0 a) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (hfb : lastFire92 (dict b) = true)
    (hlt : lt (hiW89 (dict a)) (hiW89 (dict b)) = true)
    (hjb : idxF88 0 (dict b) = some jb) :
    vebIdx123 (dict a) (psi (reg 1) jb) = true := by
  have hba := (btLe72_D 1 0 a hbA).2
  have hbb := (btLe72_D 1 0 b hbB).2
  have hia := inT_dict_of_std172 Hp a hba (isStd_of_D hsA)
  have hib := inT_dict_of_std172 Hp b hbb (isStd_of_D hsB)
  show (match idxF88 0 (dict a) with
        | none => true
        | some i => lt (psi (reg 1) i) (psi (reg 1) jb)) = true
  cases hja : idxF88 0 (dict a) with
  | none => rfl
  | some ja =>
      show lt (psi (reg 1) ja) (psi (reg 1) jb) = true
      rw [lt_psi_same]
      exact idxLtMixF_hiW123 hia.1 hia.2 hib.1 hib.2 hfb hja hjb hlt

/-- **残る条項 — 対の側だけ。**  §114 の `VebIngF114` から第二連言を外したもの。 -/
def VebPairs123 : Prop :=
  ∀ (a b : BT) (jb : Term), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lastFire92 (dict a) = false → lastFire92 (dict b) = true →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    idxF88 0 (dict b) = some jb →
    vebPair123 (dict a) (psi (reg 1) jb) = true

/-- **§123.4 の系 — `VebIngF114` は対の側の条項だけで出る。** -/
theorem vebIngF_of_pairs123 (Hp : PsiIdxOKStd172) (H : VebPairs123) : VebIngF114 := by
  intro a b jb hbA hbB hsA hsB hWa hWb hfa hfb hlt hjb
  rw [vebIng_eq123, H a b jb hbA hbB hsA hsB hWa hWb hfa hfb hlt hjb,
    vebIdx_true123 Hp hbA hbB hsA hsB hfb hlt hjb]
  rfl

/-- **§123 は残余を動かしていない — 定理として。**  `VebPairs123` は `VebIngF114` と
    **同値**である。§123 が外したのは条項ではなく、条項の中の**只の連言**である。 -/
theorem vebIngF_iff_pairs123 (Hp : PsiIdxOKStd172) : VebIngF114 ↔ VebPairs123 :=
  ⟨fun H a b jb hbA hbB hsA hsB hWa hWb hfa hfb hlt hjb => by
      have h := H a b jb hbA hbB hsA hsB hWa hWb hfa hfb hlt hjb
      rw [vebIng_eq123] at h
      exact ((Bool.and_eq_true _ _).mp h).1,
   vebIngF_of_pairs123 Hp⟩

/-- **§120.3 の一般化 — `a` の側の全発火は要らなかった。**  §120.5 は「その仮定を
    落としても 388 組で一度も破れない」と測り、必要性については**何も主張しない**と
    書いた。§123.3 はそれを定理にする。 -/
theorem idxMono_noFireA123 (Hp : PsiIdxOKStd172) {a b : BT} {ja jb : Term}
    (hba : btLe72 1 a = true) (hbb : btLe72 1 b = true)
    (hsa : BT.isStd a = true) (hsb : BT.isStd b = true)
    (hfb : lastFire92 (dict b) = true)
    (hja : idxF88 0 (dict a) = some ja) (hjb : idxF88 0 (dict b) = some jb)
    (hlt : lt (hiW89 (dict a)) (hiW89 (dict b)) = true) : lt ja jb = true := by
  obtain ⟨hia, hiaM⟩ := inT_dict_of_std172 Hp a hba hsa
  obtain ⟨hib, hibM⟩ := inT_dict_of_std172 Hp b hbb hsb
  exact idxLtMixF_hiW123 hia hiaM hib hibM hfb hja hjb hlt

/-- その系 — §101 の条項をもう一度 (§120.3 の `idxMono101_of_psi120` の弱い仮定版)。 -/
theorem idxMono101_of_noFireA123 (Hp : PsiIdxOKStd172) : IdxMono101 :=
  fun _ _ _ _ hba hbb hsa hsb _ hfb hja hjb hlt =>
    idxMono_noFireA123 Hp hba hbb hsa hsb hfb hja hjb hlt

/-- **`HiMono89` を三つの条項に架け替える。**  §120 の三つのうち `VebIngF114` が
    `VebPairs123` に痩せる。 -/
theorem hiMono_of_three123 (Hp : PsiIdxOKStd172) (HB : IdxLeMix109) (H1 : VebPairs123)
    (H2 : VebRest117) : HiMono89 :=
  hiMono_of_three120 Hp HB (vebIngF_of_pairs123 Hp H1) H2

/-- **326 行目を架け替える。** -/
theorem certIn_t326_123 (Hp : PsiIdxOKStd172) (HB : IdxLeMix109) (H1 : VebPairs123)
    (H2 : VebRest117) (HD1 : DictOntoMidOpen103) (HD3 : DictDenseMid107)
    (HD4 : DictDenseAbove107) (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_120 Hp HB (vebIngF_of_pairs123 Hp H1) H2 HD1 HD3 HD4 hacc

end

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-! ### §123.5 §117 の道具はこの半分では何も出さない -/

/-- **§117.4 の的はこの半分には一つも無い。**  `b` が全発火するなら、途中で切っても
    残りは発火するか、切り口が末尾で値が `ψ_{Ω₁}` になるかのどちらかで、
    `φ̄` の形をした途中値は**存在しない**。 -/
theorem tgtOK_false123 {a b : BT} (hib : inT (dict b) = true)
    (hfb : lastFire92 (dict b) = true) (k : Nat) : tgtOK117 a b k = false := by
  have hall : ∀ ac ∈ (wcnf (reg 1) (toList (dict b))).1, le (reg 1) ac.1 = true :=
    fun ac hac => List.all_eq_true.mp (allFire_of_lastFire109 hib hfb) ac hac
  have hsp : (wcnf (reg 1) (toList (dict b))).1.take k
      ++ (wcnf (reg 1) (toList (dict b))).1.drop k = (wcnf (reg 1) (toList (dict b))).1 :=
    List.take_append_drop k _
  cases hd : (wcnf (reg 1) (toList (dict b))).1.drop k with
  | cons ac t =>
      have hf : le (reg 1) ac.1 = true :=
        hall ac (by rw [← hsp, hd]; exact List.mem_append_right _ (List.Mem.head _))
      have h1 : (((wcnf (reg 1) (toList (dict b))).1.drop k).all
          (fun z : Term × Term => !le (reg 1) z.1)) = false := by
        rw [hd, List.all_cons, hf]
        rfl
      unfold tgtOK117
      rw [h1]
      rfl
  | nil =>
      have htake : (wcnf (reg 1) (toList (dict b))).1.take k
          = (wcnf (reg 1) (toList (dict b))).1 := by
        have h := hsp
        rw [hd, List.append_nil] at h
        exact h
      obtain ⟨jb, hjb⟩ := idxF_some_of_lastFire109 hib hfb
      have hstate := fold_fire_state114 (wcnf (reg 1) (toList (dict b))).1
        ((none : Option Term), (none : Option Term)) hall (Or.inl ⟨rfl, rfl⟩)
      have hfv : ∃ i, foldVal117 (dict b) k = some (psi (reg 1) i) := by
        rcases hstate with h1 | ⟨i, _, hi2⟩
        · exfalso
          have : idxF88 0 (dict b) = none := h1.1
          rw [this] at hjb
          cases hjb
        · exact ⟨i, by
            show (((wcnf (reg 1) (toList (dict b))).1.take k).foldl
              (stepF (reg 1) (baseOf 0))
              ((none : Option Term), (none : Option Term))).2 = _
            rw [htake]
            exact hi2⟩
      obtain ⟨i, hi⟩ := hfv
      unfold tgtOK117
      rw [hi]
      exact Bool.and_false _

/-- **§123.5 の主定理 — この半分では §117 の判定は §114 の条件そのもの。**
    §117 は「`hiMono_closed117` は `VebIngF114` の側にも向けられる」と書いたが、
    向けても得るものは無い: `closed117` の第二の選択肢は `b` が全発火するところでは
    **一度も真にならない**。 -/
theorem closed_eq123 {a b : BT} {jb : Term} (hib : inT (dict b) = true)
    (hfb : lastFire92 (dict b) = true) (hjb : idxF88 0 (dict b) = some jb) :
    closed117 a b = VebIng114 (dict a) (psi (reg 1) jb) := by
  have h2 : (List.range ((wcnf (reg 1) (toList (dict b))).1.length + 1)).any (tgtOK117 a b)
      = false := by
    cases hq : (List.range ((wcnf (reg 1) (toList (dict b))).1.length + 1)).any
        (tgtOK117 a b) with
    | false => rfl
    | true =>
        exfalso
        obtain ⟨k, _, hk⟩ := List.any_eq_true.mp hq
        rw [tgtOK_false123 hib hfb k] at hk
        exact Bool.noConfusion hk
  show ((match idxF88 0 (dict b) with
         | none => false
         | some j => VebIng114 (dict a) (psi (reg 1) j))
        || (List.range ((wcnf (reg 1) (toList (dict b))).1.length + 1)).any (tgtOK117 a b))
      = VebIng114 (dict a) (psi (reg 1) jb)
  rw [hjb, h2, Bool.or_false]

/-- **§123.5 の系 — 残余は対の側ちょうど。**  §117 の判定は、この半分では
    §123.4 で定理になった連言を落として、**第一連言そのもの**になる。 -/
theorem closed_eq_pairs123 (Hp : PsiIdxOKStd172) {a b : BT} {jb : Term}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hbB : btLe72 1 (BT.D 0 b) = true)
    (hsA : BT.isStd (BT.D 0 a) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (hfb : lastFire92 (dict b) = true)
    (hlt : lt (hiW89 (dict a)) (hiW89 (dict b)) = true)
    (hjb : idxF88 0 (dict b) = some jb) :
    closed117 a b = vebPair123 (dict a) (psi (reg 1) jb) := by
  have hbb := (btLe72_D 1 0 b hbB).2
  have hib := inT_dict_of_std172 Hp b hbb (isStd_of_D hsB)
  rw [closed_eq123 hib.1 hfb hjb, vebIng_eq123,
    vebIdx_true123 Hp hbA hbB hsA hsB hfb hlt hjb]
  exact Bool.and_true _

end

/-! ### §123.6 否定と段の正直さ -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- `ψ₁ψ₁ψ₁ψ₁0`、5 記号 — 全発火する `b` の一番小さいもの。 -/
def w4_123 : BT := BT.D 1 w3_101

/-- **否定 1 — §114 の逆転はまるごと第一連言の側にある。**  `revA114`/`revB114` は
    `VebIng114` を破るが、破っているのは**指数と係数の条項だけ**で、第二連言は
    真である。しかも `revA114` は崩壊指数を**持たない**ので、§123.4 の定理は
    この証人では空虚である。**§123 は条項を必要にした証人に触っていない。** -/
theorem revSplit123 :
    (VebIng114 (dict revA114) (psi (reg 1) (jOf114 revB114)),
     vebPair123 (dict revA114) (psi (reg 1) (jOf114 revB114)),
     vebIdx123 (dict revA114) (psi (reg 1) (jOf114 revB114)),
     (idxF88 0 (dict revA114)).isSome, lastFire92 (dict revB114))
    = (false, false, true, false, true) := rfl

/-- **否定 2 — 一つ隣では、破れるのは反対の連言である。**  §114 の `sepR114` の対は
    `b` に Veblen の尾があり、そこでは `vebIdx123` が**偽**で `vebPair123` は真:
    指数が等しい (`j_a = j_b`) ので `ψ_{Ω₁}` の比較が狭義にならない。
    **`b` が全発火するという仮定が §123.4 を定理にしているものそのもので、
    外すと文は偽になる。** -/
theorem sepSplit123 :
    (VebIng114 (dict sepRA114) (psi (reg 1) (jOf114 sepRB114)),
     vebPair123 (dict sepRA114) (psi (reg 1) (jOf114 sepRB114)),
     vebIdx123 (dict sepRA114) (psi (reg 1) (jOf114 sepRB114)),
     lastFire92 (dict sepRB114), jOf114 sepRA114 == jOf114 sepRB114)
    = (false, true, false, false, true) := rfl

/-- **否定 3 — §114 の `knownSplit114` がこちらの半分に置いた証人も第一連言で破れる。** -/
theorem scSplit123 :
    (VebIng114 (dict scBadA101) (psi (reg 1) (jOf114 scBadB101)),
     vebPair123 (dict scBadA101) (psi (reg 1) (jOf114 scBadB101)),
     vebIdx123 (dict scBadA101) (psi (reg 1) (jOf114 scBadB101)),
     (idxF88 0 (dict scBadA101)).isSome, lastFire92 (dict scBadB101))
    = (false, false, true, true, true) := rfl

/-- **§123.3 が §120.3 より広いことの証人 — §120 自身の証人の裏返し。**
    `mixB109` (`= sepRA114`、`ψ₁ψ₁ψ₁0 ⊕ ψ₁0`、7 記号) は §120.4 が
    「`b` の側の全発火は要る」と言うために使った項である。それを **`a` の側**に置くと、
    折り畳みは発火する前置きと Veblen の尾を持ち、崩壊指数を持ちながら
    `lastFire92 = false` — **`idxMono_core120` は届かず、§123.3 は届く。**
    両辺とも `K` 標準で、`hi` は狭義に増え、`b` は全発火する。
    そして §117 の道具はここでも何も出さない (`tgtOK117` はどの `k` でも偽)。 -/
theorem preSep123 :
    (btLe72 1 (BT.D 0 mixB109), BT.isStd (BT.D 0 mixB109), le (reg 1) (dict mixB109),
     lastFire92 (dict mixB109), (idxF88 0 (dict mixB109)).isSome,
     btLe72 1 (BT.D 0 w4_123), BT.isStd (BT.D 0 w4_123), le (reg 1) (dict w4_123),
     lastFire92 (dict w4_123),
     lt (hiW89 (dict mixB109)) (hiW89 (dict w4_123)),
     vebIdx123 (dict mixB109) (psi (reg 1) (jOf114 w4_123)),
     VebIng114 (dict mixB109) (psi (reg 1) (jOf114 w4_123)),
     (List.range ((wcnf (reg 1) (toList (dict w4_123))).1.length + 1)).any
       (tgtOK117 mixB109 w4_123),
     closed117 mixB109 w4_123, BT.size mixB109, BT.size w4_123)
    = (true, true, true, false, true, true, true, true, true, true, true, true,
       false, true, 7, 5) := rfl

/-- **段の正直さ。**  §123 が組んだ項も、§114 から借りた証人も、`ψ₁` の段を出ず
    (`btLe72 1` が真)、`ψ₀` の段には**落ちない** (`btLe72 0` が偽)。 -/
theorem levelHonest123 :
    (btLe72 1 mixB109, btLe72 0 mixB109, btLe72 1 w4_123, btLe72 0 w4_123,
     btLe72 1 revA114, btLe72 0 revA114, btLe72 1 sepRA114, btLe72 0 sepRA114)
    = (true, false, true, false, true, false, true, false) := rfl

end

/-! ### §123.7 測定 (凍結)

**構成 — §114.5 の三本の線に、四本目を組んで足す。**  §123.3 が読む形は
「折り畳みに**発火する前置きがあり、しかも Veblen の尾が続く**」項で、その上に
全発火する `b` を置いた対である。§114.5 の母集団はその形を持ってはいるが (119 組)、
狙って作られてはいない。四本目 `preSeed123` はそれを狙って作る — `Ω₁^{Ω₁}` の塔に
`Ω₁` や `ψ₀` を継ぎ足して、前置きの長さを 1 から 2 に伸ばす。濾さない。

    fireSeed123  全発火する種 4 個 (§114.5 の `fireSeed114`)
    vebSeed123   発火しない種 3 個 (§114.5 の `vebSeed114`)
    mixSeed123   §114 の逆転とその親戚 3 個 (§114.5 の `mixSeed114`)
    preSeed123   **前置き + Veblen の尾** 6 個 (§123 が組んだ線)
    pop123       その 2 項和も入れた 149 項  濾さない

`pop114_123` は `preSeed123` を抜いた §114.5 の 65 項ちょうど、`popDeep123` は
`ψ₁` の塔を二段深くして最大 49 記号まで伸ばした 272 項である。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

private def dedup123 (l : List BT) : List BT :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []
private def w5_123 : BT := BT.D 1 w4_123
private def w6_123 : BT := BT.D 1 w5_123
private def fireSeed123 : List BT :=
  [w2_101, w3_101, w4_123, BT.D 1 (BT.sum w3_101 w3_101)]
private def vebSeed123 : List BT :=
  [w1_101, BT.D 1 (BT.D 0 w1_101), BT.D 1 (BT.D 0 (BT.sum w2_101 w1_101))]
private def mixSeed123 : List BT :=
  [revA114, BT.D 1 (BT.sum (BT.D 1 (BT.D 0 w1_101)) (BT.D 1 BT.zero)),
   BT.D 1 (BT.D 1 (BT.D 0 w3_101))]
/-- **§123 が組んだ線** — 発火する前置きと Veblen の尾を同じ項に持たせる。 -/
private def preSeed123 : List BT :=
  [BT.sum w3_101 w1_101, BT.sum w4_123 w2_101,
   BT.D 1 (BT.sum w3_101 (BT.D 0 w3_101)), BT.sum w4_123 (BT.D 1 (BT.D 0 w3_101)),
   BT.sum w4_123 (BT.sum w3_101 w1_101),
   BT.sum w4_123 (BT.sum w3_101 (BT.D 1 (BT.D 0 w1_101)))]
private def deepSeed123 : List BT :=
  [w5_123, w6_123, BT.D 1 (BT.sum w4_123 w4_123), BT.sum w5_123 (BT.sum w4_123 w1_101),
   BT.sum w6_123 (BT.sum w5_123 (BT.D 1 (BT.D 0 (BT.sum w3_101 w1_101)))),
   BT.D 1 (BT.D 0 (BT.sum w3_101 w1_101))]
private def widen123 (l : List BT) : List BT :=
  dedup123 (l ++ l.flatMap (fun a => (l.filter (fun b => BT.le b a)).map (BT.sum a)))
private def pop123 : List BT :=
  widen123 (fireSeed123 ++ vebSeed123 ++ mixSeed123 ++ preSeed123)
private def pop114_123 : List BT := widen123 (fireSeed123 ++ vebSeed123 ++ mixSeed123)
private def popDeep123 : List BT :=
  widen123 (fireSeed123 ++ vebSeed123 ++ mixSeed123 ++ preSeed123 ++ deepSeed123)

private def ok123 (a : BT) : Bool := btLe72 1 a && BT.isStd a && le (reg 1) (dict a)
private def kstd123 (a : BT) : Bool := ok123 a && BT.isStd (BT.D 0 a)
private def samp123 : List BT := pop123.filter ok123
private def ksamp123 : List BT := pop123.filter kstd123
private def samp114_123 : List BT := pop114_123.filter ok123
private def sampD123 : List BT := popDeep123.filter ok123
private def ksampD123 : List BT := popDeep123.filter kstd123
private def hasIdx123 (a : BT) : Bool := (idxF88 0 (dict a)).isSome
private def pairsA123 (l : List BT) : List (BT × BT) :=
  l.flatMap (fun a => l.map (fun b => (a, b)))
/-- 残余 — `hi` が狭義に増え、`a` の最後の対が発火しない対。§114 の担当分。 -/
private def resid123 (l : List BT) : List (BT × BT) :=
  (pairsA123 l).filter (fun p =>
    lt (hiW89 (dict p.1)) (hiW89 (dict p.2)) && !lastFire92 (dict p.1))
/-- そのうち `b` が全発火する半分 — `VebIngF114` の担当分。 -/
private def af123 (l : List BT) : List (BT × BT) :=
  (resid123 l).filter (fun p => allFire101 (dict p.2))
private def concl123 (p : BT × BT) : Bool :=
  lt (collapse 0 (hiW89 (dict p.1))) (collapse 0 (hiW89 (dict p.2)))
private def rev123 (p : BT × BT) : Bool :=
  lt (collapse 0 (hiW89 (dict p.2))) (collapse 0 (hiW89 (dict p.1)))
private def ing123 (p : BT × BT) : Bool := VebIng114 (dict p.1) (psi (reg 1) (jOf114 p.2))
private def pairOK123 (p : BT × BT) : Bool := vebPair123 (dict p.1) (psi (reg 1) (jOf114 p.2))
private def idxOK123 (p : BT × BT) : Bool := vebIdx123 (dict p.1) (psi (reg 1) (jOf114 p.2))
private def tgtAny123 (p : BT × BT) : Bool :=
  (List.range ((wcnf (reg 1) (toList (dict p.2))).1.length + 1)).any (tgtOK117 p.1 p.2)
private def merge123 (a : BT) : Bool :=
  (wcnf (reg 1) (toList (dict a))).1.length < (toList (hiW89 (dict a))).length
private def preLen123 (a : BT) : Nat :=
  ((wcnf (reg 1) (toList (dict a))).1.takeWhile
    (fun z : Term × Term => le (reg 1) z.1)).length

/-! 母集団の形。**149 項のうち形の条件を満たすのが 90 項、`K` 標準が 71 項**で、
    崩壊指数を持つのが 55 項、全発火が 14 項、**指数を持ちながら全発火しないのが 41 項**
    — 最後のものが §123.3 が読み §120.3 が読めない類である。 -/
#guard (pop123.length, samp123.length, ksamp123.length,
        samp123.countP hasIdx123, samp123.countP (fun a => lastFire92 (dict a)),
        samp123.countP (fun a => hasIdx123 a && !lastFire92 (dict a)))
  == (149, 90, 71, 55, 14, 41)

/-! §114.5 の母集団そのもの (65 項) では、その類は 21 項。 -/
#guard (pop114_123.length, samp114_123.length,
        samp114_123.countP (fun a => hasIdx123 a && !lastFire92 (dict a))) == (65, 65, 21)

/-! **受領 1 — 担当する半分は空でない。**  残余 3665 組のうち `b` が全発火するのは
    815 組、`K` 標準では 2145 組のうち 549 組。 -/
#guard ((resid123 samp123).length, (af123 samp123).length,
        (resid123 ksamp123).length, (af123 ksamp123).length) == (3665, 815, 2145, 549)

/-! **受領 2 — 分割はちょうど言った場所に落ちる。**  `b` が全発火する 815 組で
    `VebIng114` は 15 回破れ、**その 15 回はぜんぶ第一連言、第二連言は 0 回**。
    `K` 標準の 549 組では何も破れない。 -/
#guard ((af123 samp123).countP (fun p => !ing123 p),
        (af123 samp123).countP (fun p => !pairOK123 p),
        (af123 samp123).countP (fun p => !idxOK123 p),
        (af123 ksamp123).countP (fun p => !ing123 p),
        (af123 ksamp123).countP (fun p => !idxOK123 p)) == (15, 15, 0, 0, 0)

/-! **受領 3 — 一つ隣では破れるのは反対の連言である。**  `b` が指数を持ちながら
    Veblen の尾を持つ 2255 組 (§117 の担当分、§123.3 の仮定が無いところ) では
    **第二連言が 96 回破れ**、第一連言は 106 回。`b` が全発火するという仮定が
    §123.4 を定理にしているものそのものである。 -/
#guard (((resid123 samp123).filter
           (fun p => !allFire101 (dict p.2) && hasIdx123 p.2)).length,
        ((resid123 samp123).filter
           (fun p => !allFire101 (dict p.2) && hasIdx123 p.2)).countP
          (fun p => !idxOK123 p),
        ((resid123 samp123).filter
           (fun p => !allFire101 (dict p.2) && hasIdx123 p.2)).countP
          (fun p => !pairOK123 p)) == (2255, 96, 106)

/-! **受領 4 — 証明した連言は空虚でない。**  815 組のうち **325 組で `a` が崩壊指数を
    持つ** — そこでは §123.4 の結論は本当に何かを言い、§120.3 の定理は
    (`lastFire92 (dict a)` が偽なので) 一度も適用できない。§114.5 の母集団だけでも
    119 組あるので、**この形は組まなくても見えていた** — 四本目の線は 2.7 倍にした
    だけである。隠さずに書く。 -/
#guard ((af123 samp123).countP (fun p => hasIdx123 p.1),
        (af123 ksamp123).countP (fun p => hasIdx123 p.1),
        (af123 samp114_123).countP (fun p => hasIdx123 p.1)) == (325, 325, 119)

/-! **受領 5 — 破れには指数が無い。**  全発火の半分の破れ 15 組はどれも `a` が
    崩壊指数を持たず、§123.4 の定理はそこで空虚である。**残余は第一連言にしか無い。**
    14 組が順序の逆転。 -/
#guard ((af123 samp123).countP (fun p => !concl123 p),
        (af123 samp123).countP (fun p => !concl123 p && rev123 p),
        (af123 samp123).countP (fun p => !concl123 p && hasIdx123 p.1),
        (af123 ksamp123).countP (fun p => !concl123 p)) == (15, 14, 0, 0)

/-! **受領 6 — §117 の道具はここでは 0 回、隣では 1154 回。**  空虚な掃き出しでは
    ない: 同じ判定が全発火でない残余 2850 組のうち 1154 組で発火する。 -/
#guard ((af123 samp123).countP tgtAny123,
        ((resid123 samp123).filter (fun p => !allFire101 (dict p.2))).countP tgtAny123,
        ((resid123 samp123).filter (fun p => !allFire101 (dict p.2))).length)
  == (0, 1154, 2850)

/-! **受領 7 — `closed117` はこの半分では `VebIng114` そのもの (§123.5 の定理)。**
    815 組すべてで一致し、そのうち 800 組で真。 -/
#guard ((af123 samp123).countP (fun p => closed117 p.1 p.2 == ing123 p),
        (af123 samp123).length,
        (af123 samp123).countP (fun p => closed117 p.1 p.2)) == (815, 815, 800)

/-! **受領 8 — §123.1 の帰納法は一成分の話ではなく、併合の枝も遊んでいない。**
    64 項が対を二つ以上、10 項が三つ以上持ち、**10 項が Veblen の尾の下に長さ 2 以上の
    発火する前置きを持つ**。`wcnf` が成分を実際に併合するのは 19 項、そのうち 4 項が
    その類にある。 -/
#guard (samp123.countP (fun a => 2 ≤ (wcnf (reg 1) (toList (dict a))).1.length),
        samp123.countP (fun a => 3 ≤ (wcnf (reg 1) (toList (dict a))).1.length),
        samp123.countP (fun a => hasIdx123 a && !lastFire92 (dict a) && 2 ≤ preLen123 a),
        samp123.countP merge123,
        samp123.countP (fun a => hasIdx123 a && !lastFire92 (dict a) && merge123 a))
  == (64, 10, 10, 19, 4)

/-! **受領 9 — 段の正直さ。**  母集団は `ψ₁` の段を出ず、`ψ₀` の段には落ちない。
    最大 31 記号。 -/
#guard (pop123.all (fun a => btLe72 1 a), pop123.countP (fun a => btLe72 0 a),
        pop123.foldl (fun m a => max m (BT.size a)) 0) == (true, 0, 31)

/-! **受領 10 — 大きさを確かめる。**  塔を二段深くした 272 項 (最大 49 記号、対を
    三つ以上持つ項が 29 — 最初の母集団では 10) でも、全発火の半分 3383 組のうち
    **1843 組で `a` が指数を持ちながら第二連言の破れは 0、`tgtOK117` の発火も 0**。
    破れは第一連言に 24 組で、`K` 標準の 2403 組では 0。深さは足した。振舞いは変わらない。 -/
#guard (popDeep123.length, sampD123.length, ksampD123.length,
        popDeep123.foldl (fun m a => max m (BT.size a)) 0,
        sampD123.countP (fun a => hasIdx123 a && !lastFire92 (dict a)),
        sampD123.countP (fun a => 3 ≤ (wcnf (reg 1) (toList (dict a))).1.length))
  == (272, 167, 139, 49, 88, 29)
#guard ((resid123 sampD123).length, (af123 sampD123).length,
        (af123 sampD123).countP (fun p => !idxOK123 p),
        (af123 sampD123).countP (fun p => !pairOK123 p),
        (af123 sampD123).countP (fun p => hasIdx123 p.1),
        (af123 sampD123).countP tgtAny123) == (12029, 3383, 0, 24, 1843, 0)
#guard ((af123 ksampD123).length, (af123 ksampD123).countP (fun p => !ing123 p),
        ((resid123 sampD123).filter
           (fun p => !allFire101 (dict p.2) && hasIdx123 p.2)).countP
          (fun p => !idxOK123 p)) == (2403, 0, 217)

end

/-! ## §122 THE ONE MISSING STEP IS A THEOREM, AND `TightUp119` GOES WITH IT — THE WINDOW
       IS DECIDED, ON `Gam0Drags111`

§119 reduced row 326's density side to one clause and named, in one sentence, the one step
inside it that was not closed:

> `carrierOfExpG0_119` shows where standardness would enter (`Ω^Ω < a`) and I did NOT close
> the step from "`Ω^Ω < a`" to "some digit fires" — that is the whole remaining gap.

**§122 closes that step (§122.1–§122.2) and then closes the clause.**

    `tightUp122` :  `PsiIdxOKStd172` → `DictLtStd92` → `Gam0Drags111` → `TightUp119` .

`DictLtStd92` costs row 326 nothing new: §121's `dictLtStd_of_four121` gets it from the three
Veblen clauses row 326 already carries plus §120's `idxMono101_of_psi120`
(`tight_of_four122`).  So `GapAtG0_107` follows (`gap122`, `gap_of_four122`), and with it
**`DictDenseMid107`, `DictDenseMid102`, `DictDenseHi94`, `DictDense85` and `CofDenseS1` are
all FALSE** — one line each, §107.5's corollaries, now with no window clause in front of
them.  `SCFirst108`, `SCFirstOne111`, `WinProp113`, `ExpUp116`, `CoefUp116` and `ExpUp116`'s
whole family are theorems too.

**WHAT MOVED AND WHAT DID NOT.**  The residue did NOT vanish: it **moved from `TightUp119`
to `Gam0Drags111`**, which §111.5 named and §111.7 measured and nobody has proved.  That is
said here rather than counted around.  What changed is the SHAPE of what is owed: `TightUp119`
was a statement about the fold, about every standard argument whose value reaches the window;
`Gam0Drags111` is a statement about ONE value — every standard level-`≤ 1` term whose value is
exactly `Γ₀` is `D 0`-headed and drags something at or above `Ω^Ω` into `G(0,·)`.  §111.7
measured its mechanism on **1164 of 1164** standard terms of value in `[Γ₀, Ω₁)`.

  §122.1  **A DIGIT AT OR ABOVE `dict Ω^Ω` FIRES.**  `dict Ω^Ω = ω^(Ω₁·Ω₁)` and `Ω₁·Ω₁`
          is `ω^(Ω₁ ⊕ Ω₁)`, so `fireP122` is three small facts: `ω^·` is strictly monotone,
          so `ω^E ≤ p` descends to `E ≤ logOm p` (`le_logOm_of_le122`); the head of a term
          at or above an ADDITIVELY PRINCIPAL bound is itself at or above it (§109.1's
          `le_hd_of_le109`, twice); and `Ω₁ ⊕ Ω₁ ≤ h ⟹ Ω₁ ≤ h ⊖ Ω₁` (`le_subAP_W122`).
          **The last one is the only one with a case split**, and it is the one place the
          `⊖` can throw material away: if the head of `h` is above `Ω₁` then `⊖ Ω₁` does
          nothing, and if it IS `Ω₁` then what is left must still be at or above `Ω₁`,
          because `Ω₁ ⊕ ·` is strictly monotone (§79's `plus_smono_right_inT79`).

  §122.2  **THE STEP.**  `fireBig122` : `PsiIdxOKStd172 + DictLtStd92 + Ω^Ω < a ⟹` some
          component of `dict a` fires.  `DictLtStd92` turns `Ω^Ω < a` into
          `ω^(Ω₁·Ω₁) < dict a`; the head of `toList (dict a)` is at or above `ω^(Ω₁·Ω₁)`
          because that bound is additively principal; §122.1 fires it.  `fireBigPair122`
          puts it into the pair list through §119's `wcnf_expG119`.  **No induction, no
          size, no `Hd085`.**

  §122.3  **THE `Γ₀` DIGIT'S ARITHMETIC.**  `lt_phiG0_snd122` : with the same first argument
          the `φ̄` comparison is the comparison of the second arguments (2.3.13 read at
          `a = c`, which §113.1 did not need).  `le_wTop_phiNFG0_122` carries
          `Γ₀ ⊕ 1 ≤ Y ⟹ φ̄(Γ₀,Y) ≥ φ̄(Γ₀,Γ₀⊕1)` through all five branches of `phiNF`.
          **The two step-down branches are where the branch condition is load-bearing**: at
          `Y = Γ₀ ⊕ 1` the step down would land on `φ̄(Γ₀,Γ₀)`, which is BELOW the top, and
          it is exactly `Γ₀ < g` — false there — that excludes it.

  §122.4  **THE CARRIER BRANCH.**  After one tame firing the accumulator is exactly
          `ψ_{Ω₁}(0) = Γ₀`; every later Veblen digit keeps the value at or above `Γ₀`
          (§117's `le_phiNF_ge117`), and the digit whose exponent is exactly `Γ₀` then lands
          at `φ̄(Γ₀, Γ₀ ⊕ c)` with `c ≥ 1`, which is at or above the window's top.
          `foldBigCar122` splits the pair list at §109.1's firing prefix; `scanSt_append122`
          — the fold's own scan splits along `++` — is the one piece of bookkeeping the
          repository did not have.  `carrierUp122` is the branch, end to end.

  §122.5  **THE OTHER BRANCH, AND WHY IT NEEDS NO "AT MOST ONE FIRING PAIR".**
          `collapse0_tame122` : if every digit's coefficient and every sub-`Ω₁` component is
          below the window's bottom, every pair is tame and NO digit has exponent exactly
          `Γ₀`, then the value is **below the bottom or at or above the top** — never inside.
          It is §113.1–§113.3's arithmetic with the firing branch admitted: a tame firing
          pair is `(Ω₁,1)`, its `Δ` is `1`, `sub1 1 = 0`, so the value it writes is
          `ψ_{Ω₁}(0) = Γ₀`, still below the bottom.  A SECOND firing pair would write
          `ψ_{Ω₁}(i)` with `i ≠ 0`, which is at or above the top (§116.3's
          `le_wTop_psi116`).  **So the invariant is a disjunction and "the merge leaves at
          most one pair per exponent" never has to be proved** — the case that would break
          the bound proves the conclusion instead.

  §122.6  **THE ASSEMBLY.**  `winUpAux122` re-runs §119.6's induction with four branches —
          not tame (§119.4's `expUpBig119`), a sub-`Ω₁` component at or above the bottom
          (the induction hypothesis, §116), a coefficient at or above the bottom (§119.1's
          `coefUpStep119`), a digit of exponent exactly `Γ₀` (§122.4 through §119.5's
          `carrierOfExpG0_119`) — and §122.5 says the remainder cannot reach the bottom.
          **No clause is left in it.**

WHAT IS **NOT** CLAIMED.  **`Gam0Drags111` is NOT proved**, and neither are
`PsiIdxOKStd172`, `DictLtA74`, `IdxLeMix109`, `VebIngF114`, `VebRest117`.  §122 does not
touch §103's hole (`DictOntoMidOpen103`) and does not reach `FoldSkips108`.  The `K` side
(`IdxStd121`) is untouched.  §69's cofinality argument runs on `TowerVal` and is untouched;
what §122 gives it is that `CofDenseS1` — the density statement that would have supplied the
other route — is false.

**THE SIXTH FAMILY EXISTS, AND IT WAS BUILT.**  §119 said "assume a sixth family reaches the
window until proved otherwise".  There is one, and §122.7 builds it:

    `cSix122 w = ψ₁ψ₁ w ⊕ ψ₁ψ₁ w`      value of `ψ₀` of it:  `φ̄(Γ₀, 1)`

— **two copies of the same digit, so `wcnf`'s MERGE makes the coefficient `1 ⊕ 1 = 2`, the
fold never fires, `sub1 2 = 1`, and the value is `φ̄(Γ₀,1)`, strictly inside the window.**
4 of the 30 land inside the window, **all 4 are tame and all 4 fail `BT.isStd` at the outermost
`ψ₀`**; for the first one `six_facts122` proves that the `ψ₀`-ARGUMENT itself is standard, so
the single failure is at the outermost `ψ₀` — the same one as §108's, §111's, §113's, §116's
and §119's families.  `tightUpNoStd122_false` refutes `TightUp119`
minus its standardness hypothesis with it.  And the reason it is not a counterexample is
exactly §122.2's premise: **`Ω^Ω < a` is FALSE on all 4**, because `ψ₁ψ₁(ψ₀ Ω^Ω) < Ω^Ω` in
`BT.lt` while its value is above `Γ₀` — §111.4's order inversion again.  §119's own S never
produced it (0 of 30 land in the window) and the enumerations could not: the first member has
**size 16**, and E stops at 12, E14 at 14.

**AND THE OVERPAYMENT LEDGER — ENTRY THIRTEEN, AND IT IS A CREDIT AND A DEBIT AT ONCE.**
§119 named the missing step and named it EXACTLY right: the step from `Ω^Ω < a` to a firing
digit is the whole of the carrier branch, and §122.1–§122.2 is that step and nothing else.
**What §119's account missed is that the clause has a SECOND branch** — the one where no
digit has exponent `Γ₀` at all, so the value cannot even reach the bottom (§122.5).  §119
described the residue as one shape ("a fold that fires once, returns to `Γ₀`, and then meets
a Veblen digit of exponent at most `Γ₀`") because that is the shape E's ONE tame place has.
The second branch fires **0 times on E's 2495 places and 0 times on E14's 16425 — and 7 times
on §119's own built S**.  **The branch the enumeration cannot see was visible in the built
population all along, and the prose read the enumeration.** -/

/-! ### §122.1 `Ω₁·Ω₁` の上の桁は必ず発火する -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

/-- `Ω₁·Ω₁ = ω^(Ω₁ ⊕ Ω₁)`。`dict bOO94 = ω^(Ω₁·Ω₁)` の指数そのもの。 -/
def W2_122 : Term := omegaNF (plus (reg 1) (reg 1))

theorem inT_W2_122 : inT W2_122 = true := rfl
theorem isAP_W2_122 : W2_122.isAP = true := rfl
theorem ltM_W2_122 : lt W2_122 M = true := rfl
theorem toList_W2_122 : toList W2_122 = [W2_122] := rfl
theorem dict_bOO_122 : dict bOO94 = omegaNF W2_122 := rfl
theorem logOm_bOO_122 : logOm (dict bOO94) = W2_122 := rfl
theorem omegaNF_W_122 : omegaNF (reg 1) = reg 1 := rfl
theorem toList_WW_122 : toList (plus (reg 1) (reg 1)) = [reg 1, reg 1] := rfl
theorem le_W_WW_122 : le (reg 1) (plus (reg 1) (reg 1)) = true := rfl
theorem le_WW_W_122 : le (plus (reg 1) (reg 1)) (reg 1) = false := rfl
theorem inT_WW_122 : inT (plus (reg 1) (reg 1)) = true := rfl
theorem le_WW_zero_122 : le (plus (reg 1) (reg 1)) zero = false := rfl

/-- `ω^·` は狭義単調だから `ω^E ≤ p` は `E ≤ logOm p` に降りる。 -/
theorem le_logOm_of_le122 {E p : Term} (hE : inT E = true) (hp : inT p = true)
    (hap : p.isAP = true) (hpM : lt p M = true) (h : le (omegaNF E) p = true) :
    le E (logOm p) = true := by
  have hlp : inT (logOm p) = true := inT_logOm hp
  cases hq : lt (logOm p) E with
  | false => exact le_of_not_lt3 (inT_le_fragR _ hlp) (inT_le_fragR _ hE) hq
  | true =>
      exfalso
      have h1 : lt (omegaNF (logOm p)) (omegaNF E) = true := lt_omegaNF_inT79 hlp hE hq
      rw [omegaNF_logOm100 hp hap hpM] at h1
      rw [not_le_of_lt113 (inT_omegaNF hE) hp h1] at h
      exact Bool.noConfusion h

/-- `w = ω^w` なら `w ≤ x` は `ω^·` を通る。 -/
theorem le_omegaNF122 {w x : Term} (hw : inT w = true) (hx : inT x = true)
    (hwe : omegaNF w = w) (h : le w x = true) : le w (omegaNF x) = true := by
  rcases (Bool.or_eq_true _ _).mp h with he | hlt
  · rw [← eq_of_beq he, hwe]; exact le_self _
  · have h1 := lt_omegaNF_inT79 hw hx hlt
    rw [hwe] at h1
    exact le_of_lt h1

/-- **`Ω₁ ⊕ Ω₁ ≤ h` なら `h ⊖ Ω₁` は `Ω₁` 以上。** -/
theorem le_subAP_W122 {h : Term} (hh : inT h = true)
    (hge : le (plus (reg 1) (reg 1)) h = true) : le (reg 1) (subAP (reg 1) h) = true := by
  obtain ⟨hc, hd⟩ := inT_toList h hh
  have hWh : le (reg 1) h = true :=
    le_trans_inT (inT_reg 1) inT_WW_122 hh le_W_WW_122 hge
  cases hl : toList h with
  | nil =>
      exfalso
      rw [toList_eq_nil h hl] at hge
      rw [le_WW_zero_122] at hge
      exact Bool.noConfusion hge
  | cons b r =>
      have hib : inT b = true := inTL_inT hh b (by rw [hl]; exact List.Mem.head _)
      rw [subAP_cons (reg 1) h b r hl]
      by_cases hbe : (b == reg 1) = true
      · rw [if_pos hbe]
        have hbW : b = reg 1 := eq_of_beq hbe
        obtain ⟨_, hcr⟩ := inTL_cons.mp (by rw [← hl]; exact hc)
        cases hr : r with
        | nil =>
            exfalso
            have hhe : h = reg 1 := by
              rw [← inT_ofList_toList h hh, hl, hr, hbW]; rfl
            rw [hhe, le_WW_W_122] at hge
            exact Bool.noConfusion hge
        | cons b1 rest =>
            rw [← hr]
            have hdr : descL r = true := descL_tail (show descL (b :: r) = true by
              rw [← hl]; exact hd)
            have hiR : inT (ofList r) = true := inT_ofList r hcr hdr
            have hlR : toList (ofList r) = r := toList_ofList89 hcr
            have hb1 : le b1 (reg 1) = true := by
              have h0 := descL_bound_inT r b hib hcr (show descL (b :: r) = true by
                rw [← hl]; exact hd) b1 (by rw [hr]; exact List.Mem.head _)
              rw [hbW] at h0; exact h0
            have hfl : (toList (reg 1)).filter (fun a => le b1 a) = [reg 1] := by
              rw [toList_W_119, List.filter_cons_of_pos (by rw [hb1])]
              rfl
            have htl : toList (plus (reg 1) (ofList r)) = toList h := by
              rw [toList_plus_inT (inT_reg 1) hiR (by rw [hlR, hr]), hfl, hlR, hl, hbW]
              rfl
            have hpe : plus (reg 1) (ofList r) = h := by
              rw [← inT_ofList_toList (plus (reg 1) (ofList r)) (inT_plus (inT_reg 1) hiR),
                htl, inT_ofList_toList h hh]
            cases hq : lt (ofList r) (reg 1) with
            | false => exact le_of_not_lt3 (inT_le_fragR _ hiR) (inT_le_fragR _ (inT_reg 1)) hq
            | true =>
                exfalso
                have h1 : lt (plus (reg 1) (ofList r)) (plus (reg 1) (reg 1)) = true :=
                  plus_smono_right_inT79 (reg 1) (inT_reg 1) (ofList r) (reg 1) hiR
                    (inT_reg 1) hq
                rw [hpe] at h1
                rw [not_le_of_lt113 inT_WW_122 hh h1] at hge
                exact Bool.noConfusion hge
      · rw [if_neg (by cases hq : (b == reg 1) with
          | false => exact Bool.noConfusion
          | true => exact absurd hq hbe)]
        exact hWh

/-- **`Ω₁·Ω₁ ≤ q` なら `q / Ω₁` は `Ω₁` 以上。** -/
theorem le_divAP_W122 {q : Term} (hq : inT q = true) (haq : q.isAP = true)
    (hqM : lt q M = true) (hge : le W2_122 q = true) :
    le (reg 1) (divAP (reg 1) q) = true := by
  have hge' : le (omegaNF (plus (reg 1) (reg 1))) q = true := hge
  have h1 : le (plus (reg 1) (reg 1)) (logOm q) = true :=
    le_logOm_of_le122 inT_WW_122 hq haq hqM hge'
  have h2 := le_subAP_W122 (inT_logOm hq) h1
  show le (reg 1) (omegaNF (subAP (reg 1) (logOm q))) = true
  exact le_omegaNF122 (inT_reg 1) (inT_subAP (inT_logOm hq)) omegaNF_W_122 h2

/-- **§122.1 の主定理 — `ω^(Ω₁·Ω₁) = dict Ω^Ω` 以上の桁は発火する。**
    §119 が閉じられなかった一歩の、成分ひとつぶんの形。 -/
theorem fireP122 {p : Term} (hp : inT p = true) (hap : p.isAP = true) (hpM : lt p M = true)
    (h : le (dict bOO94) p = true) : le (reg 1) (wA (reg 1) p) = true := by
  have h' : le (omegaNF W2_122) p = true := by rw [← dict_bOO_122]; exact h
  have hlp : inT (logOm p) = true := inT_logOm hp
  have hlpM : lt (logOm p) M = true := ltM_logOm hp hpM
  have hge : le W2_122 (logOm p) = true := le_logOm_of_le122 inT_W2_122 hp hap hpM h'
  cases hl : toList (logOm p) with
  | nil =>
      exfalso
      rw [toList_eq_nil _ hl, show le W2_122 zero = false from rfl] at hge
      exact Bool.noConfusion hge
  | cons q0 r =>
      have hmem : q0 ∈ toList (logOm p) := by rw [hl]; exact List.Mem.head _
      have hq0 : le W2_122 q0 = true := le_hd_of_le109 inT_W2_122 isAP_W2_122 hlp hl hge
      have hiq0 : inT q0 = true := inTL_inT hlp q0 hmem
      have haq0 : q0.isAP = true := inTL_isAP hlp q0 hmem
      have hq0M : lt q0 M = true := ltM_toList _ hlp hlpM q0 hmem
      have hWq0 : le (reg 1) q0 = true :=
        le_trans_inT (inT_reg 1) inT_W2_122 hiq0
          (le_of_lt (show lt (reg 1) W2_122 = true from rfl)) hq0
      have hfl : lt q0 (reg 1) = false := by
        cases hx : lt q0 (reg 1) with
        | false => rfl
        | true => rw [not_le_of_lt113 (inT_reg 1) hiq0 hx] at hWq0; exact Bool.noConfusion hWq0
      have hwl : toList (wA (reg 1) p)
          = divAP (reg 1) q0 :: (r.filter (fun x => !lt x (reg 1))).map (divAP (reg 1)) := by
        rw [toList_wA119, hl, List.filter_cons_of_pos (by rw [hfl]; rfl)]
        rfl
      exact le_of_le_hd109 (inT_reg 1)
        (inT_wA109 (inT_reg 1) (show (reg 1).isSC = true from rfl) hp) hwl
        (le_divAP_W122 hiq0 haq0 hq0M hq0)

end

/-! ### §122.2 §119 が閉じられなかった一歩 -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

theorem inT_dict_bOO122 : inT (dict bOO94) = true := rfl
theorem isAP_dict_bOO122 : (dict bOO94).isAP = true := rfl
theorem lt_W_dict_bOO122 : lt (reg 1) (dict bOO94) = true := rfl
theorem legal_bOO122 : btLe72 1 bOO94 = true := rfl
theorem std_bOO122 : BT.isStd bOO94 = true := rfl

/-- **§122.2 の主定理 — `Ω^Ω < a` なら `dict a` の桁がひとつ発火する。**
    §119 が「閉じていない一歩はこれだ」と名指しした一歩、そのもの。 -/
theorem fireBig122 (Hp : PsiIdxOKStd172) (HD : DictLtStd92) {a : BT}
    (hba : btLe72 1 a = true) (hsa : BT.isStd a = true) (hlt : BT.lt bOO94 a = true) :
    ∃ p ∈ toList (dict a), lt p (reg 1) = false ∧ le (reg 1) (wA (reg 1) p) = true := by
  obtain ⟨hiA, hAM⟩ := inT_dict_of_std172 Hp a hba hsa
  have hlt2 : lt (dict bOO94) (dict a) = true :=
    HD bOO94 a legal_bOO122 hba std_bOO122 hsa hlt
  cases hl : toList (dict a) with
  | nil =>
      exfalso
      rw [toList_eq_nil _ hl, show lt (dict bOO94) zero = false from ltF_right_zero _ _] at hlt2
      exact Bool.noConfusion hlt2
  | cons p0 t =>
      rw [← hl]
      have hmem : p0 ∈ toList (dict a) := by rw [hl]; exact List.Mem.head _
      have hge : le (dict bOO94) p0 = true :=
        le_hd_of_le109 inT_dict_bOO122 isAP_dict_bOO122 hiA hl (le_of_lt hlt2)
      have hip : inT p0 = true := inTL_inT hiA p0 hmem
      have hap : p0.isAP = true := inTL_isAP hiA p0 hmem
      have hpM : lt p0 M = true := ltM_toList _ hiA hAM p0 hmem
      have hWp : le (reg 1) p0 = true :=
        le_trans_inT (inT_reg 1) inT_dict_bOO122 hip (le_of_lt lt_W_dict_bOO122) hge
      refine ⟨p0, hmem, ?_, fireP122 hip hap hpM hge⟩
      cases hx : lt p0 (reg 1) with
      | false => rfl
      | true => rw [not_le_of_lt113 (inT_reg 1) hip hx] at hWp; exact Bool.noConfusion hWp

/-- 対の列の言葉で。 -/
theorem fireBigPair122 (Hp : PsiIdxOKStd172) (HD : DictLtStd92) {a : BT}
    (hba : btLe72 1 a = true) (hsa : BT.isStd a = true) (hlt : BT.lt bOO94 a = true) :
    ∃ ac ∈ (wcnf (reg 1) (toList (dict a))).1, le (reg 1) ac.1 = true := by
  obtain ⟨hiA, _⟩ := inT_dict_of_std172 Hp a hba hsa
  obtain ⟨hc, hd⟩ := inT_toList _ hiA
  obtain ⟨p, hp, hpw, hfire⟩ := fireBig122 Hp HD hba hsa hlt
  obtain ⟨ac, hac, hace⟩ := wcnf_expG119 (toList (dict a)) hc hd p hp hpw
  exact ⟨ac, hac, by rw [hace]; exact hfire⟩

end

/-! ### §122.3 指数がちょうど `Γ₀` の Veblen 桁 -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

theorem wTop_eq122 : wTop116 = phi G094 (plus G094 TM.Term.one) := rfl
theorem le_G01_wTop122 : le (plus G094 TM.Term.one) wTop116 = true := rfl
theorem isSC_G0_122 : G094.isSC = true := rfl

/-- 第 1 引数が同じなら `φ̄` の比較は第 2 引数だけで決まる。 -/
theorem lt_phiG0_snd122 {b d : Term} : lt (phi G094 b) (phi G094 d) = lt b d := by
  by_cases h : b = d
  · rw [h, lt_irrefl, lt_irrefl]
  · have hne2 : phi G094 b ≠ phi G094 d := by
      intro hc; injection hc with _ h2; exact h h2
    rw [lt_eq_ltF_succ, ltF_succ_phi_phi _ hne2, if_pos rfl,
      show ltF (2 * ((phi G094 b).deg + (phi G094 d).deg) + 7) b d = lt b d from
        (lt_eq_ltF b d _ (by
          show b.deg + d.deg ≤ 2 * ((1 + G094.deg + b.deg) + (1 + G094.deg + d.deg)) + 7
          omega)).symm]

/-- 第 2 引数が `Γ₀ ⊕ 1` 以上なら `φ̄(Γ₀,·)` は窓の上端以上。 -/
theorem le_wTop_phiG0_122 {Y : Term} (h : le (plus G094 TM.Term.one) Y = true) :
    le wTop116 (phi G094 Y) = true := by
  rw [wTop_eq122]
  rcases (Bool.or_eq_true _ _).mp h with he | hlt
  · rw [eq_of_beq he]; exact le_self _
  · exact le_of_lt (by rw [lt_phiG0_snd122]; exact hlt)

/-- 窓の上端以上のものに有限個の `1` を足しても `φ̄(Γ₀,·)` は窓の上端以上。 -/
theorem le_wTop_phiG0_down122 {g : Term} (hig : inT g = true) (hbig : le wTop116 g = true)
    (n : Nat) : le wTop116 (phi G094 (plus g (ofNat n))) = true :=
  le_wTop_phiG0_122
    (le_trans_inT (inT_plus inT_G094_102 inT_one) inT_wTop116
      (inT_plus hig (inT_ofNat n)) le_G01_wTop122
      (leG_plus_left116 inT_wTop116 isAP_wTop116 hig (inT_ofNat n) hbig))

/-- `φ̄` の項の四つ組を取り出す。 -/
theorem inT_phi_parts122 {d e : Term} (h : inT (phi d e) = true) :
    inT d = true ∧ inT e = true ∧ lt d M = true ∧ lt e M = true := by
  have hall : (inT d && inT e && lt d M && lt e M) = true := h
  have h12 := (Bool.and_eq_true _ _).mp hall
  have h34 := (Bool.and_eq_true _ _).mp h12.1
  have h56 := (Bool.and_eq_true _ _).mp h34.1
  exact ⟨h56.1, h56.2, h34.2, h12.2⟩

/-- 正規化した `φ̄(Γ₀,·)` — 五つの枝ぜんぶ。 -/
theorem le_wTop_phiNFG0_122 {Y : Term} (hiY : inT Y = true) (hYM : lt Y M = true)
    (hge : le (plus G094 TM.Term.one) Y = true) : le wTop116 (phiNF G094 Y) = true := by
  have hYz : Y ≠ zero := by
    intro hc
    rw [hc, show le (plus G094 TM.Term.one) zero = false from rfl] at hge
    exact Bool.noConfusion hge
  have hphiY : le wTop116 (phi G094 Y) = true := le_wTop_phiG0_122 hge
  have hdef : le wTop116 (phiNFdefault G094 Y) = true := by
    unfold phiNFdefault
    rw [if_neg (by
      cases hb : (Y == zero) with
      | false => rw [Bool.false_and]; exact Bool.noConfusion
      | true => exact absurd (eq_of_beq hb) hYz)]
    exact hphiY
  have hig : inT (splitFin Y).1 = true := inT_splitFin hiY
  have hsucc : le wTop116 (phiNFsucc G094 Y) = true := by
    unfold phiNFsucc
    split
    rename_i heq
    split
    · split
      · rename_i d e
        rw [heq] at hig
        have hig2 : inT (phi d e) = true := hig
        obtain ⟨hid, hie, hdM, heM⟩ := inT_phi_parts122 hig2
        split
        · rename_i hlt
          exact le_wTop_phiG0_down122 hig2 (le_wTop_phi119 hid hie hdM heM hlt) _
        · exact hdef
      · split
        · rename_i hcond
          rw [heq] at hig
          exact le_wTop_phiG0_down122 hig
            (le_wTop_SC119 ((Bool.and_eq_true _ _).mp hcond).1
              ((Bool.and_eq_true _ _).mp hcond).2) _
        · exact hdef
    · exact hdef
  unfold phiNF
  split
  · rename_i hh
    exact le_wTop_SC119 ((Bool.and_eq_true _ _).mp hh).1 ((Bool.and_eq_true _ _).mp hh).2
  · split
    · rename_i c d hYeq
      split
      · rename_i hAc
        obtain ⟨hic, hid, hcM, hdM⟩ := inT_phi_parts122 (show inT (phi c d) = true from hiY)
        exact le_wTop_phi119 hic hid hcM hdM hAc
      · exact hsucc
    · exact hsucc

end

/-! ### §122.4 発火のあとで `Γ₀` の桁に会えば窓の上端を越える -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

theorem leW_G0_false122 : le (reg 1) G094 = false := rfl

/-- `ψ_{Ω₁}` の値は `Γ₀` 以上。 -/
theorem le_G0_psi122 (i : Term) : le G094 (psi (reg 1) i) = true := by
  by_cases h : i = zero
  · rw [h]; exact le_self _
  · refine le_of_lt94 ?_
    show lt (psi (reg 1) zero) (psi (reg 1) i) = true
    rw [lt_psi_same]
    exact lt_zero_left h

/-- 指数がちょうど `Γ₀` の Veblen 桁 — 入ってきた値が `Γ₀` 以上なら窓の上端を越える。 -/
theorem stepBigVebG0_122 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (hf : le (reg 1) ac.1 = false) (heA : ac.1 = G094)
    (h3 : inT ac.2 = true) (h4 : lt ac.2 M = true) (hz : ac.2 ≠ zero)
    {v : Term} (hs2 : s.2 = some v) (hv : le G094 v = true) :
    BigU116 (stepF (reg 1) (baseOf 0) s ac) := by
  obtain ⟨hiv, hvM⟩ := hst.2 v hs2
  refine ⟨phiNF ac.1 (plus v ac.2), by rw [stepF_snd_veb88 hf, hs2], ?_⟩
  rw [heA]
  refine le_wTop_phiNFG0_122 (inT_plus hiv h3) (lt_plus_M hiv h3 hvM h4) ?_
  refine le_trans_inT (inT_plus inT_G094_102 inT_one) (inT_plus hiv inT_one)
    (inT_plus hiv h3) (plus_mono_left112 inT_G094_102 hiv inT_one hv) ?_
  exact plus_mono_right_inT v hiv TM.Term.one ac.2 inT_one h3 (le_one_inT h3 hz)

/-- 指数が `Γ₀` より下の Veblen 桁 — 値は `Γ₀` 以上のまま。 -/
theorem stepG0Keep122 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (hf : le (reg 1) ac.1 = false)
    (h1 : inT ac.1 = true) (h2 : lt ac.1 M = true) (h3 : inT ac.2 = true)
    (h4 : lt ac.2 M = true) {v : Term} (hs2 : s.2 = some v) (hv : le G094 v = true) :
    ∃ v', (stepF (reg 1) (baseOf 0) s ac).2 = some v' ∧ le G094 v' = true := by
  obtain ⟨hiv, hvM⟩ := hst.2 v hs2
  refine ⟨phiNF ac.1 (plus v ac.2), by rw [stepF_snd_veb88 hf, hs2], ?_⟩
  exact le_phiNF_ge117 inT_G094_102 isAP_G0_119 (by decide) (show lt G094 M = true from by decide) h1 h2
    (inT_plus hiv h3) (lt_plus_M hiv h3 hvM h4)
    (leG_plus_left116 inT_G094_102 isAP_G0_119 hiv h3 hv)

/-- 「発火ずみ」の不変量。 -/
def CarSt122 (s : Option Term × Option Term) : Prop :=
  BigU116 s ∨ ∃ v, s.2 = some v ∧ le G094 v = true

/-- 発火する対だけの空でない列を畳むと、値は `ψ_{Ω₁}` の像。 -/
theorem foldFire122 : ∀ (l : List (Term × Term)) (s : Option Term × Option Term),
    l ≠ [] → (∀ ac ∈ l, le (reg 1) ac.1 = true) →
    ∃ i, (l.foldl (stepF (reg 1) (baseOf 0)) s).2 = some (psi (reg 1) i) := by
  intro l
  induction l with
  | nil => intro _ hne _; exact absurd rfl hne
  | cons ac t ih =>
    intro s _ hall
    cases t with
    | nil =>
        refine ⟨idxOf (reg 1) s ac, ?_⟩
        show (stepF (reg 1) (baseOf 0) s ac).2 = _
        exact stepF_snd_fire88 (hall ac (List.Mem.head _))
    | cons b r =>
        exact ih (stepF (reg 1) (baseOf 0) s ac) (List.cons_ne_nil b r)
          (fun x hx => hall x (List.Mem.tail _ hx))

/-- **§122.4 の主定理 — 発火のあとの Veblen 側。** -/
theorem foldCar122 : ∀ (l : List (Term × Term)) (s : Option Term × Option Term),
    StInv s →
    (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
    (∀ ac ∈ l, ac.2 ≠ zero) →
    (∀ ac ∈ l, le (reg 1) ac.1 = false) →
    (∀ p ∈ scanSt (reg 1) (baseOf 0) s l, le (reg 1) p.2.1 = true →
        inT (psi (reg 1) (idxOf (reg 1) p.1 p.2)) = true) →
    CarSt122 s →
    (BigU116 s ∨ ∃ ac ∈ l, ac.1 = G094) →
    BigU116 (l.foldl (stepF (reg 1) (baseOf 0)) s) := by
  intro l
  induction l with
  | nil =>
      intro s _ _ _ _ _ _ hbig
      rcases hbig with h | ⟨ac, hac, _⟩
      · exact h
      · cases hac
  | cons ac t ih =>
    intro s hst hall hnz hnf hpsi hcar hbig
    obtain ⟨h1, h2, h3, h4⟩ := hall ac (List.Mem.head _)
    have hf : le (reg 1) ac.1 = false := hnf ac (List.Mem.head _)
    have hstep : StInv (stepF (reg 1) (baseOf 0) s ac) :=
      stepF_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0) hst
        ⟨h1, h2, h3, h4⟩ (hpsi (s, ac) (List.Mem.head _))
    refine ih _ hstep (fun x hx => hall x (List.Mem.tail _ hx))
      (fun x hx => hnz x (List.Mem.tail _ hx)) (fun x hx => hnf x (List.Mem.tail _ hx))
      (fun p hp => hpsi p (List.Mem.tail _ hp)) ?_ ?_
    · rcases hcar with hb | ⟨v, hs2, hv⟩
      · exact Or.inl (stepBigNoFire116 hst hf h1 h2 h3 h4 (Or.inl hb))
      · by_cases hG : ac.1 = G094
        · exact Or.inl (stepBigVebG0_122 hst hf hG h3 h4 (hnz ac (List.Mem.head _)) hs2 hv)
        · exact Or.inr (stepG0Keep122 hst hf h1 h2 h3 h4 hs2 hv)
    · rcases hbig with hb | ⟨ac0, hac0, hG0⟩
      · exact Or.inl (stepBigNoFire116 hst hf h1 h2 h3 h4 (Or.inl hb))
      · rcases List.mem_cons.mp hac0 with he | ht
        · rcases hcar with hb | ⟨v, hs2, hv⟩
          · exact Or.inl (stepBigNoFire116 hst hf h1 h2 h3 h4 (Or.inl hb))
          · refine Or.inl (stepBigVebG0_122 hst hf (by rw [← he]; exact hG0) h3 h4
              (hnz ac (List.Mem.head _)) hs2 hv)
        · exact Or.inr ⟨ac0, ht, hG0⟩

/-- `scanSt` は連結で割れる。 -/
theorem scanSt_append122 (w base : Term) : ∀ (l1 l2 : List (Term × Term))
    (s : Option Term × Option Term),
    scanSt w base s (l1 ++ l2)
      = scanSt w base s l1 ++ scanSt w base (l1.foldl (stepF w base) s) l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 s; rfl
  | cons ac t ih =>
    intro l2 s
    show (s, ac) :: scanSt w base (stepF w base s ac) (t ++ l2) = _
    rw [ih l2 (stepF w base s ac)]
    rfl

/-- **§122.4 の主定理 (2) — 対の列に発火する対と `Γ₀` の対があれば畳み込みは窓の上端以上。** -/
theorem foldBigCar122 (P : List (Term × Term))
    (hallOK : ∀ ac ∈ P, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true)
    (hnz : ∀ ac ∈ P, ac.2 ≠ zero)
    (hpsi : ∀ p ∈ scanSt (reg 1) (baseOf 0) (none, none) P, le (reg 1) p.2.1 = true →
        inT (psi (reg 1) (idxOf (reg 1) p.1 p.2)) = true)
    (hds : ∀ ac ∈ P.dropWhile (fun z => le (reg 1) z.1), le (reg 1) ac.1 = false)
    (hfire : ∃ ac ∈ P, le (reg 1) ac.1 = true)
    (hG0 : ∃ ac ∈ P, ac.1 = G094) :
    BigU116 (P.foldl (stepF (reg 1) (baseOf 0)) (none, none)) := by
  have hsplit : P.takeWhile (fun z => le (reg 1) z.1) ++ P.dropWhile (fun z => le (reg 1) z.1)
      = P := List.takeWhile_append_dropWhile
  have hpre_ne : P.takeWhile (fun z => le (reg 1) z.1) ≠ [] := by
    intro hnil
    obtain ⟨ac, hac, hfa⟩ := hfire
    have hin : ac ∈ P.dropWhile (fun z => le (reg 1) z.1) := by
      rw [← hsplit, hnil, List.nil_append] at hac; exact hac
    rw [hds ac hin] at hfa
    exact Bool.noConfusion hfa
  have hscan := scanSt_append122 (reg 1) (baseOf 0)
    (P.takeWhile (fun z => le (reg 1) z.1)) (P.dropWhile (fun z => le (reg 1) z.1)) (none, none)
  rw [hsplit] at hscan
  have hpsiPre : ∀ p ∈ scanSt (reg 1) (baseOf 0) (none, none)
      (P.takeWhile (fun z => le (reg 1) z.1)), le (reg 1) p.2.1 = true →
        inT (psi (reg 1) (idxOf (reg 1) p.1 p.2)) = true := by
    intro p hp
    exact hpsi p (by rw [hscan]; exact List.mem_append_left _ hp)
  have hpsiPost : ∀ p ∈ scanSt (reg 1) (baseOf 0)
      ((P.takeWhile (fun z => le (reg 1) z.1)).foldl (stepF (reg 1) (baseOf 0)) (none, none))
      (P.dropWhile (fun z => le (reg 1) z.1)), le (reg 1) p.2.1 = true →
        inT (psi (reg 1) (idxOf (reg 1) p.1 p.2)) = true := by
    intro p hp
    exact hpsi p (by rw [hscan]; exact List.mem_append_right _ hp)
  have hStInv0 : StInv ((P.takeWhile (fun z => le (reg 1) z.1)).foldl
      (stepF (reg 1) (baseOf 0)) (none, none)) :=
    fold_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0)
      _ (none, none) stInv_none
      (fun x hx => hallOK x (by rw [← hsplit]; exact List.mem_append_left _ hx)) hpsiPre
  have hcar0 : CarSt122 ((P.takeWhile (fun z => le (reg 1) z.1)).foldl
      (stepF (reg 1) (baseOf 0)) (none, none)) := by
    obtain ⟨i, hi⟩ := foldFire122 (P.takeWhile (fun z => le (reg 1) z.1)) (none, none)
      hpre_ne (fun x hx => mem_takeWhile109 _ _ x hx)
    exact Or.inr ⟨psi (reg 1) i, hi, le_G0_psi122 i⟩
  have hG0post : ∃ ac ∈ P.dropWhile (fun z => le (reg 1) z.1), ac.1 = G094 := by
    obtain ⟨ac, hac, he⟩ := hG0
    rw [← hsplit] at hac
    rcases List.mem_append.mp hac with h | h
    · exfalso
      have h2 := mem_takeWhile109 _ _ ac h
      rw [he, leW_G0_false122] at h2
      exact Bool.noConfusion h2
    · exact ⟨ac, h, he⟩
  rw [← hsplit, List.foldl_append]
  exact foldCar122 (P.dropWhile (fun z => le (reg 1) z.1)) _ hStInv0
    (fun x hx => hallOK x (by rw [← hsplit]; exact List.mem_append_right _ hx))
    (fun x hx => hnz x (by rw [← hsplit]; exact List.mem_append_right _ hx))
    hds hpsiPost hcar0 (Or.inr hG0post)

/-- **§122.4 の主定理 (3) — `Ω^Ω < a` と `Γ₀` の桁から、値は窓の上端以上。** -/
theorem carrierUp122 (Hp : PsiIdxOKStd172) (HD : DictLtStd92) {a : BT}
    (hba : btLe72 1 a = true) (hsa : BT.isStd a = true)
    (hs0 : BT.isStd (BT.D 0 a) = true) (hlt : BT.lt bOO94 a = true)
    (hG0 : ∃ ac ∈ (wcnf (reg 1) (toList (dict a))).1, ac.1 = G094) :
    le wTop116 (dict (BT.D 0 a)) = true := by
  obtain ⟨hiA, hAM⟩ := inT_dict_of_std172 Hp a hba hsa
  obtain ⟨hc, hd⟩ := inT_toList _ hiA
  have hM := ltM_toList _ hiA hAM
  obtain ⟨⟨hrT, hrM⟩, hallOK⟩ :=
    wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList (dict a)) hc hd hM
  have Hpx : PsiIdxOK 0 (dict a) := Hp 0 a (by omega) hba hs0
  have hfold := foldBigCar122 (wcnf (reg 1) (toList (dict a))).1 hallOK
    (wcnf_coef_ne_zero119 (toList (dict a)) hc hd hM) Hpx
    (fireSplit109 (isSC_reg_succ 0) (inT_reg 1) (show (reg 1).isAP = true from rfl)
      (toList (dict a)) hc hd)
    (fireBigPair122 Hp HD hba hsa hlt) hG0
  have hacc : inT (accW89 (dict a)) = true ∧ lt (accW89 (dict a)) M = true := by
    have hstF : StInv ((wcnf (reg 1) (toList (dict a))).1.foldl
        (stepF (reg 1) (baseOf 0)) (none, none)) :=
      fold_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0)
        (wcnf (reg 1) (toList (dict a))).1 (none, none) stInv_none hallOK Hpx
    unfold accW89
    cases hg : ((wcnf (reg 1) (toList (dict a))).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2 with
    | none => exact ⟨inT_zero, lt_zero_M⟩
    | some v => exact hstF.2 v hg
  obtain ⟨v, hv, hbv⟩ := hfold
  have hav : accW89 (dict a) = v := by unfold accW89; rw [hv]; rfl
  have hbig : le wTop116 (plus (accW89 (dict a)) (rhoW89 (dict a))) = true := by
    rw [hav]
    exact leG_plus_left116 inT_wTop116 isAP_wTop116 (by rw [← hav]; exact hacc.1) hrT hbv
  have hsi : inT (plus (accW89 (dict a)) (rhoW89 (dict a))) = true := inT_plus hacc.1 hrT
  have hsM : lt (plus (accW89 (dict a)) (rhoW89 (dict a))) M = true :=
    lt_plus_M hacc.1 hrT hacc.2 hrM
  show le wTop116 (collapse 0 (dict a)) = true
  rw [collapse0_raw89]
  refine leG_omegaNF116 inT_wTop116 isAP_wTop116 ltM_wTop116 lt_one_wTop116
    (inT_plus (inT_reg 0) hsi) (lt_plus_M (inT_reg 0) hsi lt_zero_M hsM) ?_
  exact leG_plus_right116 inT_wTop116 (inT_reg 0) hsi hbig

end

/-! ### §122.5 おとなしい対の列で `Γ₀` の桁がなければ窓に入れない -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

theorem lt_G0_bot122 : lt G094 (gT113 zero) = true := by decide
theorem inT_gT0_122 : inT (gT113 zero) = true := by decide

/-- **§113.3 の `wcnfG113`、指数の条件を「`Γ₀` より下か発火する」に緩めたもの。** -/
theorem wcnfG122 {R : Term} (hiT : inT (gT113 R) = true) :
    ∀ (L : List Term), inTL L = true → descL L = true → (∀ x ∈ L, lt x M = true) →
      (∀ p ∈ L, lt p (reg 1) = true → lt p (gT113 R) = true) →
      (∀ p ∈ L, lt p (reg 1) = false →
        (lt (wA (reg 1) p) G094 = true ∨ le (reg 1) (wA (reg 1) p) = true)
          ∧ lt (wC (reg 1) p) (gT113 R) = true) →
      (∀ ac ∈ (wcnf (reg 1) L).1,
          (lt ac.1 G094 = true ∨ le (reg 1) ac.1 = true) ∧ lt ac.2 (gT113 R) = true)
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
                (lt ac.1 G094 = true ∨ le (reg 1) ac.1 = true) ∧ lt ac.2 (gT113 R) = true)
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

/-- おとなしい畳み込みの不変量 — 「窓の上端以上で発火ずみ」か「窓の下端より下で指数 `0`」。 -/
def TmSt122 (s : Option Term × Option Term) : Prop :=
  (BigU116 s ∧ ∃ i, s.1 = some i) ∨ (StG113 zero s ∧ ∀ i, s.1 = some i → i = zero)

theorem tmSt_none122 : TmSt122 ((none : Option Term), (none : Option Term)) :=
  Or.inr ⟨(by intro v hv; cases hv), (by intro i hi; cases hi)⟩

/-- 発火する対がおとなしいと `Δ = 1`。 -/
theorem dd_one122 {ac : Term × Term} (hA : ac.1 = reg 1) (hc : ac.2 = TM.Term.one) :
    ddOf75 (reg 1) ac = TM.Term.one := by
  show mulL (mulL (reg 1) (subAP (reg 1) ac.1)) ac.2 = TM.Term.one
  rw [hA, hc]
  rfl

/-- おとなしい発火の一歩。 -/
theorem stepTmFire122 {s : Option Term × Option Term} {ac : Term × Term}
    (hA : ac.1 = reg 1) (hc : ac.2 = TM.Term.one)
    (hs : StG113 zero s ∧ ∀ i, s.1 = some i → i = zero) :
    TmSt122 (stepF (reg 1) (baseOf 0) s ac) := by
  have hf : le (reg 1) ac.1 = true := by rw [hA]; exact le_self _
  cases hs1 : s.1 with
  | none =>
      have hidx : idxOf (reg 1) s ac = zero := by
        show (match s.1 with
              | none => sub1 (mulL (mulL (reg 1) (subAP (reg 1) ac.1)) ac.2)
              | some j => plus j (mulL (mulL (reg 1) (subAP (reg 1) ac.1)) ac.2)) = zero
        rw [hs1]
        show sub1 (ddOf75 (reg 1) ac) = zero
        rw [dd_one122 hA hc]
        rfl
      refine Or.inr ⟨?_, ?_⟩
      · intro v hv
        have hve : v = psi (reg 1) (idxOf (reg 1) s ac) :=
          (Option.some.inj ((stepF_snd_fire88 hf).symm.trans hv)).symm
        rw [hve, hidx]
        exact ⟨inT_G094_102, by decide, lt_G0_bot122⟩
      · intro i hi
        have h2 : (if le (reg 1) ac.1 = true then some (idxOf (reg 1) s ac) else s.1) = some i := by
          rw [← stepF_fst]; exact hi
        rw [if_pos hf] at h2
        rw [← Option.some.inj h2, hidx]
  | some i0 =>
      have hi0 : i0 = zero := hs.2 i0 hs1
      have hidx : idxOf (reg 1) s ac = TM.Term.one := by
        rw [idxOf_some92 hs1, dd_one122 hA hc, hi0]
        exact plus_zero_left_inT inT_one
      refine Or.inl ⟨⟨psi (reg 1) (idxOf (reg 1) s ac), stepF_snd_fire88 hf, ?_⟩, ?_⟩
      · rw [hidx]
        exact le_wTop_psi116 (fun hcc => Term.noConfusion hcc)
      · exact ⟨idxOf (reg 1) s ac, by rw [stepF_fst, if_pos hf]⟩

/-- **§122.5 の主定理 (1) — おとなしい対の列の畳み込み。** -/
theorem foldT122 : ∀ (l : List (Term × Term)) (s : Option Term × Option Term),
    StInv s → TmSt122 s →
    (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
    (∀ ac ∈ l, (lt ac.1 G094 = true ∨ (ac.1 = reg 1 ∧ ac.2 = TM.Term.one))
        ∧ lt ac.2 (gT113 zero) = true) →
    (∀ p ∈ scanSt (reg 1) (baseOf 0) s l, le (reg 1) p.2.1 = true →
        inT (psi (reg 1) (idxOf (reg 1) p.1 p.2)) = true) →
    TmSt122 (l.foldl (stepF (reg 1) (baseOf 0)) s) := by
  intro l
  induction l with
  | nil => intro s _ hs _ _ _; exact hs
  | cons ac t ih =>
    intro s hst hs hall hgood hpsi
    obtain ⟨h1, h2, h3, h4⟩ := hall ac (List.Mem.head _)
    obtain ⟨hshape, hcG⟩ := hgood ac (List.Mem.head _)
    have hstep : StInv (stepF (reg 1) (baseOf 0) s ac) :=
      stepF_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0) hst
        ⟨h1, h2, h3, h4⟩ (hpsi (s, ac) (List.Mem.head _))
    refine ih _ hstep ?_ (fun x hx => hall x (List.Mem.tail _ hx))
      (fun x hx => hgood x (List.Mem.tail _ hx)) (fun p hp => hpsi p (List.Mem.tail _ hp))
    rcases hshape with hveb | ⟨hA, hcone⟩
    · have hf : le (reg 1) ac.1 = false :=
        leW_false106 h1 (lt_trans_inT h1 inT_G094_102 inT_W79 hveb lt_G0_W113)
      rcases hs with ⟨hb, i, hi⟩ | ⟨hg, hidx⟩
      · refine Or.inl ⟨stepBigNoFire116 hst hf h1 h2 h3 h4 (Or.inl hb), ?_⟩
        exact ⟨i, by rw [stepF_fst, if_neg (by rw [hf]; exact Bool.noConfusion)]; exact hi⟩
      · refine Or.inr ⟨stepG113 inT_gT0_122 h1 h2 hveb h3 h4 hcG hg, ?_⟩
        intro i hi
        refine hidx i ?_
        have h5 : (if le (reg 1) ac.1 = true then some (idxOf (reg 1) s ac) else s.1)
            = some i := by rw [← stepF_fst]; exact hi
        rw [if_neg (by rw [hf]; exact Bool.noConfusion)] at h5
        exact h5
    · have hf : le (reg 1) ac.1 = true := by rw [hA]; exact le_self _
      rcases hs with ⟨hb, i, hi⟩ | hg
      · have hdz : ddOf75 (reg 1) ac ≠ zero :=
          ddOf_ne_zero84 (by rw [hcone]; exact fun hcc => Term.noConfusion hcc)
        have hidxne : idxOf (reg 1) s ac ≠ zero := by
          rw [idxOf_some92 hi]
          intro hcc
          exact hdz (le_zero_eq116 (by
            rw [← hcc]
            exact le_self_plus75 (hst.1 i hi).1 (inT_ddOf75 (inT_reg 1) h1 h3)))
        exact Or.inl ⟨⟨psi (reg 1) (idxOf (reg 1) s ac), stepF_snd_fire88 hf,
          le_wTop_psi116 hidxne⟩, ⟨idxOf (reg 1) s ac, by rw [stepF_fst, if_pos hf]⟩⟩
      · exact stepTmFire122 hA hcone hg

/-- **§122.5 の主定理 (2) — おとなしくて `Γ₀` の桁がなければ、窓の下端に届かないか
    窓の上端を越えるかのどちらかで、窓の中には入れない。** -/
theorem collapse0_tame122 {x : Term} (hx : inT x = true) (hxM : lt x M = true)
    (Hpx : PsiIdxOK 0 x)
    (hlo : ∀ p ∈ toList x, lt p (reg 1) = true → lt p (rawT94 0) = true)
    (hhi : ∀ p ∈ toList x, lt p (reg 1) = false →
      (lt (wA (reg 1) p) G094 = true ∨ le (reg 1) (wA (reg 1) p) = true)
        ∧ lt (wC (reg 1) p) (rawT94 0) = true)
    (htame : ((wcnf (reg 1) (toList x)).1).any bigP119 = false) :
    lt (collapse 0 x) (rawT94 0) = true ∨ le wTop116 (collapse 0 x) = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  have hM := ltM_toList x hx hxM
  obtain ⟨hallG, hrhoG⟩ := wcnfG122 (R := zero) inT_gT0_122 (toList x) hc hd hM hlo hhi
  obtain ⟨⟨hrhoT, hrhoM⟩, hallOK⟩ :=
    wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList x) hc hd hM
  have hnz := wcnf_coef_ne_zero119 (toList x) hc hd hM
  have hgood : ∀ ac ∈ (wcnf (reg 1) (toList x)).1,
      (lt ac.1 G094 = true ∨ (ac.1 = reg 1 ∧ ac.2 = TM.Term.one))
        ∧ lt ac.2 (gT113 zero) = true := by
    intro ac hac
    obtain ⟨hsh, hcG⟩ := hallG ac hac
    refine ⟨?_, hcG⟩
    rcases hsh with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      have hb : bigP119 ac = false := by
        cases hbb : bigP119 ac with
        | false => rfl
        | true => rw [List.any_eq_true.mpr ⟨ac, hac, hbb⟩] at htame; exact Bool.noConfusion htame
      unfold bigP119 at hb
      rw [if_pos h] at hb
      have hb2 := Bool.or_eq_false_iff.mp hb
      have hA : ac.1 = reg 1 := by
        rcases (Bool.or_eq_true _ _).mp h with he | hlt
        · exact (eq_of_beq he).symm
        · exfalso; rw [hlt] at hb2; exact Bool.noConfusion hb2.1
      have hic : inT ac.2 = true := (hallOK ac hac).2.2.1
      have hcone : ac.2 = TM.Term.one := by
        have hle : le ac.2 TM.Term.one = true :=
          le_of_not_lt3 (inT_le_fragR _ inT_one) (inT_le_fragR _ hic) hb2.2
        rcases (Bool.or_eq_true _ _).mp hle with he | hlt
        · exact eq_of_beq he
        · exact absurd (below_one _ hic (fuelOf ac.2 TM.Term.one) hlt) (hnz ac hac)
      exact ⟨hA, hcone⟩
  have hfold := foldT122 (wcnf (reg 1) (toList x)).1 (none, none) stInv_none tmSt_none122
    hallOK hgood Hpx
  rcases hfold with ⟨hb, _⟩ | ⟨hg, _⟩
  · refine Or.inr ?_
    have hacc : inT (accW89 x) = true ∧ lt (accW89 x) M = true := by
      have hstF : StInv ((wcnf (reg 1) (toList x)).1.foldl
          (stepF (reg 1) (baseOf 0)) (none, none)) :=
        fold_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0)
          (wcnf (reg 1) (toList x)).1 (none, none) stInv_none hallOK Hpx
      unfold accW89
      cases hgg : ((wcnf (reg 1) (toList x)).1.foldl
          (init := ((none : Option Term), (none : Option Term)))
          (stepF (reg 1) (baseOf 0))).2 with
      | none => exact ⟨inT_zero, lt_zero_M⟩
      | some v => exact hstF.2 v hgg
    obtain ⟨v, hv, hbv⟩ := hb
    have hav : accW89 x = v := by unfold accW89; rw [hv]; rfl
    have hbig : le wTop116 (plus (accW89 x) (rhoW89 x)) = true := by
      rw [hav]
      exact leG_plus_left116 inT_wTop116 isAP_wTop116 (by rw [← hav]; exact hacc.1) hrhoT hbv
    have hsi : inT (plus (accW89 x) (rhoW89 x)) = true := inT_plus hacc.1 hrhoT
    have hsM : lt (plus (accW89 x) (rhoW89 x)) M = true :=
      lt_plus_M hacc.1 hrhoT hacc.2 hrhoM
    rw [collapse0_raw89]
    refine leG_omegaNF116 inT_wTop116 isAP_wTop116 ltM_wTop116 lt_one_wTop116
      (inT_plus (inT_reg 0) hsi) (lt_plus_M (inT_reg 0) hsi lt_zero_M hsM) ?_
    exact leG_plus_right116 inT_wTop116 (inT_reg 0) hsi hbig
  · refine Or.inl ?_
    have hacc : inT (accW89 x) = true ∧ lt (accW89 x) M = true
        ∧ lt (accW89 x) (gT113 zero) = true := by
      unfold accW89
      cases hgg : ((wcnf (reg 1) (toList x)).1.foldl
          (init := ((none : Option Term), (none : Option Term)))
          (stepF (reg 1) (baseOf 0))).2 with
      | none => exact ⟨inT_zero, lt_zero_M, lt_zero_gT113 zero⟩
      | some v => exact hg v hgg
    have hs1 : inT (plus (accW89 x) (rhoW89 x)) = true := inT_plus hacc.1 hrhoT
    have hs2 : lt (plus (accW89 x) (rhoW89 x)) M = true :=
      lt_plus_M hacc.1 hrhoT hacc.2.1 hrhoM
    have hs3 : lt (plus (accW89 x) (rhoW89 x)) (gT113 zero) = true :=
      lt_plus_gT113 inT_gT0_122 hacc.1 hrhoT hacc.2.2 hrhoG
    rw [collapse0_raw89]
    exact lt_omegaNF113 inT_gT0_122 (inT_plus inT_zero hs1)
      (lt_plus_M inT_zero hs1 lt_zero_M hs2)
      (lt_plus_gT113 inT_gT0_122 inT_zero hs1 (lt_zero_gT113 zero) hs3)

end

/-! ### §122.6 `TightUp119` は定理である -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

theorem all_false_of_any122 {l : List Term} {f : Term → Bool} (h : l.any f = false) :
    ∀ p ∈ l, f p = false := by
  intro p hp
  cases hb : f p with
  | false => rfl
  | true => rw [List.any_eq_true.mpr ⟨p, hp, hb⟩] at h; exact Bool.noConfusion h

/-- `Ω₁` より下で窓の下端以上の成分。 -/
def loBad122 (p : Term) : Bool := lt p (reg 1) && !(lt p (rawT94 0))
/-- 係数が窓の下端以上の桁。 -/
def coefBad122 (p : Term) : Bool := !(lt p (reg 1)) && !(lt (wC (reg 1) p) (rawT94 0))
/-- 指数がちょうど `Γ₀` の桁。 -/
def carr122 (p : Term) : Bool := !(lt p (reg 1)) && (wA (reg 1) p == G094)

/-- **§122.6 の主定理 — 帳簿の帰納法、条項なし。** -/
theorem winUpAux122 (Hp : PsiIdxOKStd172) (HD : DictLtStd92) (Hg : Gam0Drags111) :
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
    obtain ⟨hcL, hdL⟩ := inT_toList _ hiA
    cases hany : ((wcnf (reg 1) (toList (dict a))).1).any bigP119 with
    | true => exact expUpBig119 hiA hAM (Hp 0 a (by omega) hba hs) (List.any_eq_true.mp hany)
    | false =>
      cases hlo : (toList (dict a)).any loBad122 with
      | true =>
          obtain ⟨p, hp, hbad⟩ := List.any_eq_true.mp hlo
          have hpw : lt p (reg 1) = true := ((Bool.and_eq_true _ _).mp hbad).1
          have hlep : le (rawT94 0) p = true := by
            have h2 := ((Bool.and_eq_true _ _).mp hbad).2
            have h3 : lt p (rawT94 0) = false := by
              cases hq : lt p (rawT94 0) with
              | false => rfl
              | true => rw [hq] at h2; exact Bool.noConfusion h2
            exact le_of_not_lt3 (inT_le_fragR _ (inTL_inT hiA p hp))
              (inT_le_fragR _ (inT_rawT98 0)) h3
          refine upPropIn116 hiA hAM (Hp 0 a (by omega) hba hs) ?_
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
      | false =>
        have hloAll : ∀ p ∈ toList (dict a), lt p (reg 1) = true →
            lt p (rawT94 0) = true := by
          intro p hp h1
          have h2 := all_false_of_any122 hlo p hp
          unfold loBad122 at h2
          rw [h1, Bool.true_and] at h2
          cases hq : lt p (rawT94 0) with
          | true => rfl
          | false => rw [hq] at h2; exact Bool.noConfusion h2
        cases hcf : (toList (dict a)).any coefBad122 with
        | true =>
            obtain ⟨p, hp, hbad⟩ := List.any_eq_true.mp hcf
            have hpw : lt p (reg 1) = false := by
              have h1 := ((Bool.and_eq_true _ _).mp hbad).1
              cases hq : lt p (reg 1) with
              | false => rfl
              | true => rw [hq] at h1; exact Bool.noConfusion h1
            have hq : lt (wC (reg 1) p) (rawT94 0) = false := by
              have h2 := ((Bool.and_eq_true _ _).mp hbad).2
              cases hq2 : lt (wC (reg 1) p) (rawT94 0) with
              | false => rfl
              | true => rw [hq2] at h2; exact Bool.noConfusion h2
            refine upPropIn116 hiA hAM (Hp 0 a (by omega) hba hs) ?_
            exact List.any_eq_true.mpr ⟨p, hp, coefUpStep119 Hp ih hn hba hsa hp hpw hq⟩
        | false =>
          have hcfAll : ∀ p ∈ toList (dict a), lt p (reg 1) = false →
              lt (wC (reg 1) p) (rawT94 0) = true := by
            intro p hp h1
            have h2 := all_false_of_any122 hcf p hp
            unfold coefBad122 at h2
            rw [h1, Bool.not_false, Bool.true_and] at h2
            cases hq : lt (wC (reg 1) p) (rawT94 0) with
            | true => rfl
            | false => rw [hq] at h2; exact Bool.noConfusion h2
          cases hcr : (toList (dict a)).any carr122 with
          | true =>
              obtain ⟨p, hp, hbad⟩ := List.any_eq_true.mp hcr
              have hpw : lt p (reg 1) = false := by
                have h1 := ((Bool.and_eq_true _ _).mp hbad).1
                cases hq : lt p (reg 1) with
                | false => rfl
                | true => rw [hq] at h1; exact Bool.noConfusion h1
              have hEq : wA (reg 1) p = G094 := eq_of_beq ((Bool.and_eq_true _ _).mp hbad).2
              have hOO : BT.lt bOO94 a = true :=
                carrierOfExpG0_119 Hp Hg hba hsa hs hp hpw hEq
              obtain ⟨ac, hac, hace⟩ := wcnf_expG119 (toList (dict a)) hcL hdL p hp hpw
              exact carrierUp122 Hp HD hba hsa hs hOO ⟨ac, hac, by rw [hace, hEq]⟩
          | false =>
              have hcrAll : ∀ p ∈ toList (dict a), lt p (reg 1) = false →
                  (wA (reg 1) p == G094) = false := by
                intro p hp h1
                have h2 := all_false_of_any122 hcr p hp
                unfold carr122 at h2
                rw [h1, Bool.not_false, Bool.true_and] at h2
                exact h2
              have hhi : ∀ p ∈ toList (dict a), lt p (reg 1) = false →
                  (lt (wA (reg 1) p) G094 = true ∨ le (reg 1) (wA (reg 1) p) = true)
                    ∧ lt (wC (reg 1) p) (rawT94 0) = true := by
                intro p hp hpw
                refine ⟨?_, hcfAll p hp hpw⟩
                cases hex : lt (wA (reg 1) p) G094 with
                | true => exact Or.inl rfl
                | false =>
                    rcases tameExp119 hcL hdL hp hpw hex hany with h1 | h1
                    · exfalso
                      have h3 := hcrAll p hp hpw
                      rw [h1, beq_self_eq_true] at h3
                      exact Bool.noConfusion h3
                    · exact Or.inr (by rw [h1]; exact le_self _)
              rcases collapse0_tame122 hiA hAM (Hp 0 a (by omega) hba hs) hloAll hhi hany with
                hlt | hbig
              · exfalso
                rw [not_le_of_lt113 (inT_rawT98 0)
                  (inT_dict_of_std172 Hp (BT.D 0 a) hb hs).1 hlt] at hle
                exact Bool.noConfusion hle
              · exact hbig

/-- **§122.6 の主定理 (2) — `TightUp119` は定理。** -/
theorem tightUp122 (Hp : PsiIdxOKStd172) (HD : DictLtStd92) (Hg : Gam0Drags111) :
    TightUp119 :=
  fun a hb hs hle _ => winUpAux122 Hp HD Hg (BT.size a) a (Nat.le_refl _) hb hs hle

/-- **`TightUp119` は row 326 の証明書の外から一つも新しい条項を要らない。**
    `DictLtStd92` は §121 の `dictLtStd_of_four121` が Veblen の三条項と §120 の
    `idxMono101_of_psi120` から出す。 -/
theorem tight_of_four122 (Hp : PsiIdxOKStd172) (HB : IdxLeMix109) (H1 : VebIngF114)
    (H2 : VebRest117) (Hg : Gam0Drags111) : TightUp119 :=
  tightUp122 Hp (dictLtStd_of_four121 Hp (idxMono101_of_psi120 Hp) HB H1 H2) Hg

/-- **§122.6 の主定理 (3) — `GapAtG0_107`。** -/
theorem gap122 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HD : DictLtStd92)
    (Hg : Gam0Drags111) : GapAtG0_107 := gap_of_tight119 Hp H2 (tightUp122 Hp HD Hg)

theorem gap_of_four122 (Hp : PsiIdxOKStd172) (HA : DictLtA74) (HB : IdxLeMix109)
    (H1 : VebIngF114) (H2 : VebRest117) (Hg : Gam0Drags111) : GapAtG0_107 :=
  gap122 Hp HA (dictLtStd_of_four121 Hp (idxMono101_of_psi120 Hp) HB H1 H2) Hg

/-! **五つの密度の主張はすべて偽。** -/

theorem denseMid107_false122 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HD : DictLtStd92)
    (Hg : Gam0Drags111) : ¬ DictDenseMid107 :=
  denseMid107_false_of_gap107 Hp H2 (gap122 Hp H2 HD Hg)

theorem denseMid102_false122 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HD : DictLtStd92)
    (Hg : Gam0Drags111) : ¬ DictDenseMid102 :=
  denseMid102_false_of_gap107 Hp H2 (gap122 Hp H2 HD Hg)

theorem dictDenseHi94_false122 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HD : DictLtStd92)
    (Hg : Gam0Drags111) : ¬ DictDenseHi94 :=
  dictDenseHi94_false_of_gap107 Hp H2 (gap122 Hp H2 HD Hg)

theorem dictDense85_false122 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HD : DictLtStd92)
    (Hg : Gam0Drags111) : ¬ DictDense85 :=
  dictDense85_false_of_gap107 Hp H2 (gap122 Hp H2 HD Hg)

theorem cofDenseS1_false122 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HD : DictLtStd92)
    (Hg : Gam0Drags111) : ¬ CofDenseS1 :=
  cofDenseS1_false_of_gap107 Hp H2 (gap122 Hp H2 HD Hg)

/-! **§111 と §108 の条項も定理になる。** -/

theorem winProp122 (Hp : PsiIdxOKStd172) (HD : DictLtStd92) (Hg : Gam0Drags111) :
    WinProp113 := winProp_of_tight119 Hp (tightUp122 Hp HD Hg)

theorem scFirstOne122 (Hp : PsiIdxOKStd172) (HD : DictLtStd92) (Hg : Gam0Drags111) :
    SCFirstOne111 := scFirstOne_of_winProp113 Hp (winProp122 Hp HD Hg)

theorem scFirst122 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HD : DictLtStd92)
    (Hg : Gam0Drags111) : SCFirst108 :=
  scFirst_of_scFirstOne111 Hp H2 (scFirstOne122 Hp HD Hg)

theorem expUp122 (Hp : PsiIdxOKStd172) (HD : DictLtStd92) (Hg : Gam0Drags111) : ExpUp116 :=
  expUp116_of_tight119 Hp (tightUp122 Hp HD Hg)

theorem coefUp122 (Hp : PsiIdxOKStd172) (HD : DictLtStd92) (Hg : Gam0Drags111) : CoefUp116 :=
  coefUp116_of_tight119 Hp (tightUp122 Hp HD Hg)

end

/-! ### §122.7 測定 (凍結)

**構成を先に書く。**  母集団は三つ。ひとつは新しく作り、ふたつは §108.6 / §116.7 のものを
読み直す。

    S122  **第六の族。**  `Γ₀` の桁を運ぶ形を `ψ₁ψ₁ w` から
          `ψ₁ψ₁ w ⊕ ψ₁ψ₁ w` に変えたもの — 併合が係数を `2` にするので、
          発火なしで `φ̄(Γ₀, c ⊖ 1)` に着く。§119.7 の 10 個の種にはめ、
          さらに三つの形に置いて 30 項。**標準性で濾さない。**
    E     §108.6 の `allStd108` (大きさ 12 までの標準・段 1 以下の項 9992 個)。
    E14   §116.7 の `bigE116` (大きさ 14 まで 58239 個)。 -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

set_option maxRecDepth 100000

/-- **第六の族の運び手。**  §111 の `cWin111` は係数を `ψ₁` の中に入れたが、
    こちらは同じ桁を**二つ並べる** — `wcnf` の併合が係数を `1 ⊕ 1 = 2` にする。 -/
def cSix122 (w : BT) : BT := BT.sum (BT.D 1 (BT.D 1 w)) (BT.D 1 (BT.D 1 w))

def argS122 : List BT :=
  (seedE119.map cSix122) ++ (seedE119.map fun w => BT.sum bOO94 (cSix122 w))
    ++ (seedE119.map fun w => BT.sum (cSix122 w) (BT.D 0 bOO94))

#guard argS122.length == 30

/-! **段の正直さ — 定理として。**  作った運び手は段 1 を超えず、段 0 は一歩目で離れる。 -/
theorem btLe1_cSix122 {w : BT} (h : btLe72 1 w = true) : btLe72 1 (cSix122 w) = true := by
  show ((decide (1 ≤ 1) && (decide (1 ≤ 1) && btLe72 1 w))
    && (decide (1 ≤ 1) && (decide (1 ≤ 1) && btLe72 1 w))) = true
  rw [h]; rfl

theorem btLe0_cSix122 (w : BT) : btLe72 0 (cSix122 w) = false := by
  show ((decide (1 ≤ 0) && (decide (1 ≤ 0) && btLe72 0 w))
    && (decide (1 ≤ 0) && (decide (1 ≤ 0) && btLe72 0 w))) = false
  rfl

theorem btLe1_D0cSix122 {w : BT} (h : btLe72 1 w = true) :
    btLe72 1 (BT.D 0 (cSix122 w)) = true := by
  show (decide (0 ≤ 1) && btLe72 1 (cSix122 w)) = true
  rw [btLe1_cSix122 h]; rfl

/-- **第六の族の第一項の値は `φ̄(Γ₀,1)` — 窓のちょうど内側。** -/
theorem dict_cSix122 : dict (BT.D 0 (cSix122 (bTowG98 0))) = phi G094 TM.Term.one := rfl

/-- **第六の族は窓に入り、対の列はおとなしく、`ψ₁` の引数は標準で、
    破れるのは外側の `ψ₀` の標準性だけ — そして `Ω^Ω < a` がそこで破れている。** -/
theorem six_facts122 :
    btLe72 1 (BT.D 0 (cSix122 (bTowG98 0))) = true
    ∧ le (rawT94 0) (dict (BT.D 0 (cSix122 (bTowG98 0)))) = true
    ∧ le wTop116 (dict (BT.D 0 (cSix122 (bTowG98 0)))) = false
    ∧ ((wcnf (reg 1) (toList (dict (cSix122 (bTowG98 0))))).1).any bigP119 = false
    ∧ BT.isStd (cSix122 (bTowG98 0)) = true
    ∧ BT.isStd (BT.D 0 (cSix122 (bTowG98 0))) = false
    ∧ BT.lt bOO94 (cSix122 (bTowG98 0)) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `TightUp119` から標準性を外したもの。 -/
def TightUpNoStd122 : Prop := ∀ a : BT, btLe72 1 (BT.D 0 a) = true →
    le (rawT94 0) (dict (BT.D 0 a)) = true →
    ((wcnf (reg 1) (toList (dict a))).1).any bigP119 = false →
    le wTop116 (dict (BT.D 0 a)) = true

/-- **`TightUp119` の標準性は運んでいる。**  外すと第六の族が反例になる。 -/
theorem tightUpNoStd122_false : ¬ TightUpNoStd122 := by
  intro H
  have h := H (cSix122 (bTowG98 0)) rfl rfl rfl
  rw [show le wTop116 (dict (BT.D 0 (cSix122 (bTowG98 0)))) = false from rfl] at h
  exact Bool.noConfusion h

/-- 窓の中 — 標準性で濾さない版。 -/
def winNoStd122 (z : BT) : Bool :=
  btLe72 1 (BT.D 0 z) && le (rawT94 0) (dict (BT.D 0 z)) && !(le wTop116 (dict (BT.D 0 z)))
/-- §122.2 の前提。 -/
def ooLt122 (z : BT) : Bool := BT.lt bOO94 z
/-- 運び手の枝の判定器 — §122.6 の場合分けの第四の枝。 -/
def brCar122 (z : BT) : Bool := (toList (dict z)).any carr122

/-! **S122 — 第六の族は本物で、止めているのは標準性ひとつである。**  30 項のうち
    **4 項が窓のちょうど内側**に入り、**その 4 項はすべておとなしく**、**4 項すべてが
    標準でなく**、**4 項すべてで `Ω^Ω < a` が破れている** — §122.2 の前提が破れる場所と
    第六の族が一致する。そして標準なもののなかに窓に入るものは **0 項** (定理どおり)。 -/
#guard (argS122.length, argS122.countP winNoStd122,
        argS122.countP fun z => winNoStd122 z && tame119 z,
        argS122.countP fun z => winNoStd122 z && tame119 z && !(BT.isStd (BT.D 0 z)),
        argS122.countP fun z => winNoStd122 z && tame119 z && !(ooLt122 z),
        argS122.countP fun z => base116 z && !(conc116 z)) == (30, 4, 4, 4, 4, 0)

/-! **母集団は形を表現できていなかった (失敗様式 2)。**  §119.7 の S (30 項) には
    窓の内側に入る項が **0 項**しかない。第六の族は §119 の種からは出てこない。 -/
#guard (argE119.countP winNoStd122, argE119.countP fun z => base116 z && !(conc116 z))
    == (0, 0)

/-! **大きさの問題でもある (失敗様式 4)。**  第六の族の第一項は大きさ **16** で、
    E は 12 まで、E14 は 14 までしか作らない。 -/
#guard BT.size (BT.D 0 (cSix122 (bTowG98 0))) == 16

/-! **分割を測る。**  §122.6 の場合分けは四つ (おとなしくない / `Ω₁` より下の成分 /
    係数 / 運び手 / どれでもない)。E で条項が訊かれる 2495 項のうちおとなしいのは 1 項で、
    その 1 項は**運び手の枝**を通る。`Ω₁` より下の成分の枝・係数の枝・どれでもない枝は
    **0 項**。E14 でも同じ。**畳み込みの側で仕事をしているのは運び手の枝ひとつである。** -/
#guard (fun L => (L.length, L.countP fun z => tame119 z && brCar122 z,
        L.countP fun z => tame119 z && !(brCar122 z)))
    (allStd108.filter base116) == (2495, 1, 0)

#guard (fun L => (L.length, L.countP fun z => tame119 z && brCar122 z,
        L.countP fun z => tame119 z && !(brCar122 z)))
    (bigE116.filter base116) == (16425, 1, 0)

/-! **その 1 項では §122.2 の前提が成り立つ。**  `bTowG98 1` の `ψ₀` 引数は
    `Ω^Ω` より上で、運び手の桁を持つ — `carrierUp122` がそのまま走る場所である。 -/
#guard ooLt122 (bArg98 (bTowG98 0)) && brCar122 (bArg98 (bTowG98 0))

/-! **`collapse0_tame122` (どれでもない枝) は空振りではない — が、それを見せるのは
    数え上げではなく作った母集団のほうである。**  §119.7 の S の 30 項では
    おとなしい 13 項のうち **7 項**がこの枝を通り、**6 項**が運び手の枝を通る。
    E と E14 では 0 項。**枝が要らないのではなく、E がその形を作らない。** -/
#guard (argE119.countP fun z => tame119 z && brCar122 z,
        argE119.countP fun z => tame119 z && !(brCar122 z)
          && !((toList (dict z)).any loBad122) && !((toList (dict z)).any coefBad122),
        argE119.countP tame119) == (6, 7, 13)

/-! **`Ω^Ω` を前置する修理は窓を跳び越す (§108.4 の再現)。**  S122 で
    `Ω^Ω < z` は 16 項、そのうち **15 項**が窓の上端以上。 -/
#guard (argS122.countP ooLt122, argS122.countP fun z => ooLt122 z && conc116 z) == (16, 15)

end

/-! ## §125 `Gam0Drags111` IS NOT A CLAUSE — AND ROW 326'S CERTIFICATE IS VACUOUS
       UNDER EXACTLY THE HYPOTHESES IT CARRIES

§111.5 named

    `Gam0Drags111` :  ∀ z, `btLe72 1 z` → `isStd z` → `dict z = Γ₀` →
                      `Hd085 z` ∧ ∃ e ∈ `G(z,0)`, `Ω^Ω ≤ e`

and measured it.  §122 then proved `tightUp122` and `cofDenseS1_false122` on it, which put
**the whole density side of row 326 on this one clause**.  §125 takes it off the list.

  §125.1  **THE FIRST CONJUNCT IS A THEOREM.**  `hd085_of_gam0_125` — and the only thing
          about `Γ₀` it uses is `Γ₀ < Ω₁`.  Weaken the premise `dict z = Γ₀` to
          `lt (dict z) (reg 1) = true` and the recursion into a sum goes through; §94.1's
          `ltW_dict94` is the converse and was already there.  Cost: `PsiIdxOKStd172`,
          which every consumer of `Gam0Drags111` already takes.

  §125.2  **THE SECOND CONJUNCT IS THE ORDER GATE AT ONE POINT.**  `reachOO_of_gam0_125`
          — `ψ₀(Ω^Ω)` is standard with value exactly `Γ₀` (three `rfl`s), so if `z`'s head
          argument were below `Ω^Ω` then `z < ψ₀(Ω^Ω)`, and `DictLtStd92` would give
          `Γ₀ < Γ₀`.  Cost: `DictLtStd92`, which §121 derives from `PsiIdxOKStd172` and the
          Veblen clauses row 326 already carries.

  §125.3  **THE HUNT.**  2 096 684 standard level-`≤ 1` terms up to size 18 hold exactly
          ONE term of value `Γ₀`, and it is `ψ₀(Ω^Ω)`.  Drop standardness and uniqueness is
          FALSE at size 9 (`gam0UniqueNoStd125_false`), by `plus` absorption — the same
          break as §122's sixth family.  What blocks the repair is a theorem, not a sweep:
          `carrierHead125` says a term that carries `Ω^Ω` behind the head must put a
          level-1 digit in front, and that digit fires.

  §125.4  **THE COMPOSITION, AND WHAT IT COSTS ROW 326.**

    `gam0Drags_of_three125`  :  `PsiIdxOKStd172` → `VebIngF114` → `VebRest117` → `Gam0Drags111`
    `denseMid107_false125`   :  the same three  →  `¬ DictDenseMid107`
    `certHyp_absurd125`      :  those three together with `DictDenseMid107` give `False`

`certIn_t326_124` takes `PsiIdxOKStd172`, `VebIngF114`, `VebRest117`, `DictOntoMidOpen103`,
`DictDenseMid107`, `DictDenseAbove107`.  Its first three prove its fifth false.  **The
certificate cannot be applied to anything: its hypotheses are contradictory.**
`certIn_t326_vacuous125` states that with §124's exact argument list and concludes `False`.

WHAT IS **NOT** CLAIMED.  This does not show the table entry for row 326 is wrong.  It shows
this ROUTE to certifying it is dead — the density argument and the certificate cannot both
stand.  `PsiIdxOKStd172`, `VebIngF114` (= `VebPairs123`) and `VebRest117` are still
unproved; if one of them is false the argument above says nothing at all.  `DictOntoMidOpen103`
is untouched and is now beside the point on this route.  §69's cofinality reading is
untouched.

**THE LEDGER, fourteenth entry, and it is against §111.**  §111.5 wrote the residue as ONE
clause with two conjuncts and measured the conjunction.  The conjuncts have nothing to do
with each other: the first needs only `Γ₀ < Ω₁` and no gate at all beyond `Hp`, the second
is `DictLtStd92` evaluated at a single pair.  Fourteen sections carried both because they
were written on one line.  **Measure the conjuncts, not the conjunction.**

**AND A FIFTH WAY A SWEEP LIES.**  §111.7 swept 9992 terms where the premise fired once.
§125.3 swept 2 096 684 and built a population of 4526 where the premise really fires.  Both
came back clean, and both were RIGHT — the clause is true.  Neither told anybody it was
PROVABLE, and neither pointed at the proof.  A sweep measures truth; it says nothing about
where the proof is.  Here the proof came from reading the two conjuncts apart. -/

/-! ### §125.1 THE FIRST CONJUNCT IS A THEOREM — IT NEEDS ONLY `Γ₀ < Ω₁`

`Gam0Drags111` (§111.5) is a conjunction.  Its first conjunct — `Hd085 z`, "every
component of `z` is a level-0 node `ψ₀ c`" — needs nothing about `Γ₀` beyond the fact
that `Γ₀ < Ω₁`.  So it is not a measurement: it is a theorem, and the only hypothesis
it costs is `PsiIdxOKStd172`, which every consumer of `Gam0Drags111` in §122 already
carries.

The route.

  * §94.1 の `ltW_dict94` は逆向き — 成分が全部 `D 0` なら値は `Ω₁` より下。
    ここで要るのはその**対偶の一般形**である: 値が `Ω₁` より下なら成分は全部 `D 0`。
  * 段 1 の節ひとつは `Ω₁` を下回れない (§98.3 の `ltW_dictD1_false98`)。
  * 和は両側を下から押さえる (`le_self_plus_ap81` と `le_self_plus75`)。主要成分の
    `dict` は加法主要 (§118 の `isAP_dict_isP118`) なので左側にも使える。

そこで `dict z = G094` は `lt (dict z) (reg 1) = true` へ弱めてよく、その形なら
和の再帰がそのまま通る。**残るのは第二の連言だけ** (`drags_of_second_125`)。 -/

/-! #### §125.1a Below `Ω₁` forces every component to level 0 -/

section
open Trans.Recal
open Trans.Dict (BT dict reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§125.1a の主定理。**  値が `Ω₁` より下の標準・段 1 以下の項は、成分がすべて
    `D 0` である。§94.1 の `ltW_dict94` の逆。 -/
theorem hd085_of_ltW125 (Hp : PsiIdxOKStd172) : ∀ (z : BT), btLe72 1 z = true →
    BT.isStd z = true → lt (dict z) (reg 1) = true → Hd085 z
  | .zero, _, _, _ => by
      intro w hw
      exact absurd hw List.not_mem_nil
  | .D u c, hb, hs, hlt => by
      obtain ⟨hu, _⟩ := btLe72_D 1 u c hb
      have hu01 : u = 0 ∨ u = 1 := by omega
      rcases hu01 with rfl | rfl
      · exact hd085_D0_111 c
      · rw [ltW_dictD1_false98 Hp hb hs] at hlt
        exact Bool.noConfusion hlt
  | .sum x y, hb, hs, hlt => by
      obtain ⟨hbx, hby⟩ := btLe72_sum 1 x y hb
      obtain ⟨hsx, hsy⟩ := isStd_of_sum hs
      have hpx : BT.isP x = true := isP_of_isStd_sum hs
      have hix : inT (dict x) = true := (inT_dict_of_std172 Hp x hbx hsx).1
      have hiy : inT (dict y) = true := (inT_dict_of_std172 Hp y hby hsy).1
      rw [Trans.Dict.dict_sum] at hlt
      have hlx : lt (dict x) (reg 1) = true :=
        lt_of_le_of_lt3 (inT_le_fragR _ hix) (inT_le_fragR _ (inT_plus hix hiy))
          (inT_le_fragR _ inT_W79)
          (le_self_plus_ap81 hix (isAP_dict_isP118 hpx) hiy) hlt
      have hly : lt (dict y) (reg 1) = true :=
        lt_of_le_of_lt3 (inT_le_fragR _ hiy) (inT_le_fragR _ (inT_plus hix hiy))
          (inT_le_fragR _ inT_W79) (le_self_plus75 hix hiy) hlt
      intro w hw
      rcases List.mem_append.mp hw with h1 | h1
      · exact hd085_of_ltW125 Hp x hbx hsx hlx w h1
      · exact hd085_of_ltW125 Hp y hby hsy hly w h1

/-- `Γ₀ < Ω₁` — `Γ₀` は可算側にいる。 -/
theorem ltW_G0_125 : lt G094 (reg 1) = true := rfl

/-- **§125.1 の主定理。**  `Gam0Drags111` の第一の連言は定理である。 -/
theorem hd085_of_gam0_125 (Hp : PsiIdxOKStd172) {z : BT} (hb : btLe72 1 z = true)
    (hs : BT.isStd z = true) (hd : dict z = G094) : Hd085 z :=
  hd085_of_ltW125 Hp z hb hs (by rw [hd]; exact ltW_G0_125)

end

/-! #### §125.1b What is left of `Gam0Drags111`

第一の連言が定理になったので、§111.5 の条項は**第二の連言だけ**になる。 -/

section
open Trans.Recal
open Trans.Dict (BT dict reg collapse)
open TM TM.Term
open Evidence.WF

/-- `Gam0Drags111` に残るもの — `G(0, z)` に `Ω^Ω` 以上の元があること。 -/
def Gam0Carr125 : Prop := ∀ z : BT, btLe72 1 z = true → BT.isStd z = true →
    dict z = G094 → ∃ e ∈ BT.GB 0 z, BT.le bOO94 e = true

/-- **半分は済んだ。**  `Gam0Drags111` は `PsiIdxOKStd172` と `Gam0Carr125` から出る。 -/
theorem drags_of_carr125 (Hp : PsiIdxOKStd172) (H : Gam0Carr125) : Gam0Drags111 :=
  fun z hb hs hd => ⟨hd085_of_gam0_125 Hp hb hs hd, H z hb hs hd⟩

end

/-! #### §125.1c 測定 — 仮説が母集団に見えていること

§111.7 の反省。`dict z = G094` は 9992 項中 1 回しか発火しない。§125.1a の仮説
`lt (dict z) (reg 1)` はそうではない — §108.6 の同じ母集団 (大きさ 12 までの標準・
段 1 以下の項) で 2923 回発火し、しかも `hd085B` と**完全に一致する**。つまり
§125.1a は両向きに正しく、空振りの掃き掃除ではない。 -/

section
open Trans.Recal
open Trans.Dict (BT dict reg collapse)
open TM TM.Term
open Evidence.WF

/-! 段 1 以下の標準項では `hd085B` と「`Ω₁` より下」は同値 — §125.1a とその逆 (§94.1)
    を母集団で見たもの。 -/
#guard allStd108.all fun z => (btLe72 1 z && BT.isStd z) == false ||
  (hd085B z == lt (dict z) (reg 1))

/-! 仮説の発火数。`dict z = G094` は 1 回、`lt (dict z) (reg 1)` は 2923 回。 -/
#guard (allStd108.countP fun z => btLe72 1 z && BT.isStd z && lt (dict z) (reg 1)) == 2923
#guard (allStd108.countP fun z => btLe72 1 z && BT.isStd z && dict z == G094) == 1

end

/-! ### §125.2 THE SECOND CONJUNCT IS THE ORDER GATE, AND NOTHING MORE

`Gam0Drags111` は二つの連言である。

    ∀ z, btLe72 1 z → BT.isStd z → dict z = Γ₀ → Hd085 z ∧ ∃ e ∈ G(z,0), Ω^Ω ≤ e

第一 (`Hd085 z`) はここでは扱わない — **仮定として受け取る。**  §125.2 が示すのは第二

    ∃ e ∈ G(z,0), Ω^Ω ≤ e                                  (`reachOO_of_gam0_125`)

で、使う条項は `DictLtStd92` ただ一つである。`DictLtStd92` は §92 が名指しし、§121 の
`dictLtStd_of_four121` が `PsiIdxOKStd172` と Veblen の三条項 (`IdxLeMix109`・
`VebIngF114`・`VebRest117`) から出す、**326 行がすでに抱えている門**である。§122 の
`tightUp122`・`cofDenseS1_false122` はどれも `Hp` と `HD` を引数に取っている。だから

  * `Gam0Drags111` の第二の連言は **326 行の証明書に新しい印を一つも足さない**。
  * `Hg` を消費する側 (`tight_of_four122` など) は、第一の連言を渡すだけでよくなる
    (`gam0Drags_of_hd125`・`gam0Drags_of_four125`)。

**筋。**  `ψ₀(Ω^Ω)` は標準・段 1 以下で、値はちょうど `Γ₀` — 三つとも `rfl`
(§125.2a)。`Hd085 z` なので `z` の先頭成分は `ψ₀ c` の形である。もし `c < Ω^Ω` なら、
頭が同じ段で引数が真に小さいので `z < ψ₀(Ω^Ω)` (§106 の `btlt_of_hd106`)、したがって
`DictLtStd92` から `dict z < Γ₀`。ところが `dict z = Γ₀` なので `Γ₀ < Γ₀` になり、これは
成り立たない。§74 の三分律より `Ω^Ω ≤ c` であり、その `c` は `G(z,0)` の元である
(§125.2b の `mem_GB0_125`)。`z = 0` の場合も同じ一撃で外れる — 成分列が空なら
`z < ψ₀(Ω^Ω)` が只で立つ。

**測定はしていない。**  §111.7 は大きさ 12 までの標準・段 1 以下の項 9992 個を掃いて、
前提 `dict z = Γ₀` が 1 回しか発火しなかった。掃き出しはここでは一度も使わない。

**外せなかったもの、その理由。**  `DictLtStd92` の使いどころは一箇所

    BT.lt z (ψ₀ Ω^Ω) = true  →  lt (dict z) Γ₀ = true

だけである。これは `collapse 0` の狭義単調性そのもので、§96 の `CollapseLe0_96`
(「残る一本。**証明しない。**」) と同じ内容である。値の側から回る道 — `collapse 0 x = Γ₀`
を `x` について解く — も試したが、`ω^` の ε 数の議論で潰せるのは `x < Ω₁` の場合だけで、
`Ω₁ ≤ x` の場合は畳み込みの累算器が `Γ₀` になる形を全部数える必要があり、それは §122 の
`winUpAux122` と同じ大きさの場合分けになる。ここでは踏み込まない。 -/

/-! #### §125.2a The anchor: `ψ₀(Ω^Ω)` is standard, level `≤ 1`, and its value is `Γ₀` -/

section
open Trans.Recal
open Trans.Dict (BT dict reg collapse)
open TM TM.Term
open Evidence.WF

/-- `ψ₀(Ω^Ω)` の値は `Γ₀`。 -/
theorem dict_bOOD0_125 : dict (BT.D 0 bOO94) = G094 := rfl

/-- `ψ₀(Ω^Ω)` は標準。 -/
theorem isStd_bOOD0_125 : BT.isStd (BT.D 0 bOO94) = true := rfl

/-- `ψ₀(Ω^Ω)` は段 1 以下。 -/
theorem btLe_bOOD0_125 : btLe72 1 (BT.D 0 bOO94) = true := rfl

/-- `ψ₀(Ω^Ω)` の成分列は一つ。 -/
theorem toL_bOOD0_125 : BT.toL (BT.D 0 bOO94) = [BT.D 0 bOO94] := rfl

/-- `Ω^Ω = ψ₁ψ₁Ω₁` 自身も標準。 -/
theorem isStd_bOO125 : BT.isStd bOO94 = true := rfl

/-! 見本の側では結論がそのまま見える — `Ω^Ω` は `G(ψ₀ Ω^Ω, 0)` の元である。 -/
#guard (BT.GB 0 (BT.D 0 bOO94)).any (fun e => BT.le bOO94 e)

end

/-! #### §125.2b Housekeeping: standard terms are `ofL`-normal, hereditarily -/

section
open Trans.Recal
open Trans.Dict (BT dict reg collapse)
open TM TM.Term
open Evidence.WF

/-- 標準な和の先頭は主成分。 -/
theorem isP_hd125 {a b : BT} (h : BT.isStd (BT.sum a b) = true) : BT.isP a = true := by
  obtain ⟨h1, _⟩ := (Bool.and_eq_true _ _).mp h
  obtain ⟨h2, _⟩ := (Bool.and_eq_true _ _).mp h1
  exact ((Bool.and_eq_true _ _).mp h2).1

/-- 標準な和の後ろの項は `0` ではない。 -/
theorem ne_zero_snd125 {a b : BT} (h : BT.isStd (BT.sum a b) = true) : b ≠ BT.zero := by
  intro hb
  subst hb
  obtain ⟨_, h4⟩ := (Bool.and_eq_true _ _).mp h
  have h5 : (BT.isP BT.zero && BT.le BT.zero a) = true := h4
  rw [show BT.isP BT.zero = false from rfl, Bool.false_and] at h5
  exact Bool.noConfusion h5

/-- `0` でない標準な項は成分を持つ。 -/
theorem toL_ne_nil125 : ∀ z : BT, BT.isStd z = true → z ≠ BT.zero → BT.toL z ≠ []
  | BT.zero, _, hne => absurd rfl hne
  | BT.D u a, _, _ => by
      show [BT.D u a] ≠ []
      exact List.cons_ne_nil _ _
  | BT.sum a b, hs, _ => by
      rw [show BT.toL (BT.sum a b) = BT.toL a ++ BT.toL b from rfl, toL_isP118 (isP_hd125 hs)]
      show a :: BT.toL b ≠ []
      exact List.cons_ne_nil _ _

/-- 標準な項は自分の成分列から組み直せる (§53 の `NfSum`)。 -/
theorem nfSum_isStd125 : ∀ z : BT, BT.isStd z = true → NfSum z
  | BT.zero, _ => rfl
  | BT.D _ _, _ => rfl
  | BT.sum a b, hs => by
      have hsb : BT.isStd b = true := (isStd_of_sum hs).2
      have hnb : NfSum b := nfSum_isStd125 b hsb
      have htb : BT.toL b ≠ [] := toL_ne_nil125 b hsb (ne_zero_snd125 hs)
      show BT.ofL (BT.toL a ++ BT.toL b) = BT.sum a b
      rw [toL_isP118 (isP_hd125 hs)]
      cases hq : BT.toL b with
      | nil => exact absurd hq htb
      | cons x xs =>
          show BT.sum a (BT.ofL (x :: xs)) = BT.sum a b
          rw [← hq, show BT.ofL (BT.toL b) = b from hnb]

/-- 標準な項は遺伝的に `ofL` 正規 (§74 の `Hwf74`) — 三分律の前提。 -/
theorem hwf74_isStd125 : ∀ z : BT, BT.isStd z = true → Hwf74 z
  | BT.zero, _ => trivial
  | BT.D _ a, h => ⟨nfSum_isStd125 a (isStd_of_D h), hwf74_isStd125 a (isStd_of_D h)⟩
  | BT.sum a b, h =>
      ⟨hwf74_isStd125 a (isStd_of_sum h).1, hwf74_isStd125 b (isStd_of_sum h).2⟩

/-- 成分の引数はその項の `G(·,0)` の元。§104 の `sub_GB0_104` の頭の側。 -/
theorem mem_GB0_125 : ∀ (a : BT) (u : Nat) (c : BT), BT.D u c ∈ BT.toL a → c ∈ BT.GB 0 a := by
  intro a
  induction a with
  | zero => intro u c h; cases h
  | D v e _ =>
      intro u c h
      have he : BT.D u c = BT.D v e := List.mem_singleton.mp (show BT.D u c ∈ [BT.D v e] from h)
      have hce : c = e := by injection he
      have hgb : BT.GB 0 (BT.D v e) = e :: BT.GB 0 e := by
        show (if 0 ≤ v then e :: BT.GB 0 e else []) = _
        rw [if_pos (Nat.zero_le v)]
      rw [hgb, hce]
      exact List.Mem.head _
  | sum s t ihs iht =>
      intro u c h
      have hgb : BT.GB 0 (BT.sum s t) = BT.GB 0 s ++ BT.GB 0 t := rfl
      rw [hgb]
      rcases List.mem_append.mp (show BT.D u c ∈ BT.toL s ++ BT.toL t from h) with h1 | h1
      · exact List.mem_append.mpr (Or.inl (ihs u c h1))
      · exact List.mem_append.mpr (Or.inr (iht u c h1))

end

/-! #### §125.2c The second conjunct, from the order gate alone -/

section
open Trans.Recal
open Trans.Dict (BT dict reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§125.2 の主定理。**  値が `Γ₀` の標準な段 1 以下の項は、`G(z,0)` のどこかで
    `Ω^Ω = ψ₁ψ₁Ω₁` 以上のものに触る — `Hd085 z` を仮定して。 -/
theorem reachOO_of_gam0_125 (HD : DictLtStd92) {z : BT} (hb : btLe72 1 z = true)
    (hs : BT.isStd z = true) (hd : dict z = G094) (hh : Hd085 z) :
    ∃ e ∈ BT.GB 0 z, BT.le bOO94 e = true := by
  have key : BT.lt z (BT.D 0 bOO94) = false := by
    cases hq : BT.lt z (BT.D 0 bOO94) with
    | false => rfl
    | true =>
        exfalso
        have h := HD z (BT.D 0 bOO94) hb btLe_bOOD0_125 hs isStd_bOOD0_125 hq
        rw [hd, dict_bOOD0_125, lt_irrefl] at h
        exact Bool.noConfusion h
  cases hz : BT.toL z with
  | nil =>
      exfalso
      have hlt : BT.lt z (BT.D 0 bOO94) = true := by
        show BT.ltL (BT.size z + BT.size (BT.D 0 bOO94) + 2)
            (BT.toL z) (BT.toL (BT.D 0 bOO94)) = true
        rw [hz, toL_bOOD0_125,
          show BT.size z + BT.size (BT.D 0 bOO94) + 2
            = (BT.size z + BT.size (BT.D 0 bOO94) + 1) + 1 from rfl]
        exact ltL_nil_cons93 _ _ _
      rw [hlt] at key
      exact Bool.noConfusion key
  | cons y ys =>
      have hmem : y ∈ BT.toL z := by rw [hz]; exact List.Mem.head _
      obtain ⟨c, hc⟩ := hh y hmem
      subst hc
      obtain ⟨_, hStd, _, _⟩ := good_toL77 z hs hb
      have hsc : BT.isStd c = true := isStd_of_D (hStd _ hmem)
      refine ⟨c, mem_GB0_125 z 0 c hmem, ?_⟩
      rcases lt_tricho74 c bOO94 (hwf74_isStd125 c hsc) (hwf74_isStd125 bOO94 isStd_bOO125)
          (nfSum_isStd125 c hsc) (nfSum_isStd125 bOO94 isStd_bOO125) with h | h | h
      · exfalso
        have hne : (c == bOO94) = false :=
          bt_beq_false _ _ (fun he => by rw [he, lt_irrefl74] at h; exact Bool.noConfusion h)
        rw [btlt_of_hd106 hz toL_bOOD0_125 hne h] at key
        exact Bool.noConfusion key
      · rw [h]; exact bt_le_refl108 bOO94
      · show ((bOO94 == c) || BT.lt bOO94 c) = true
        rw [h]; exact Bool.or_true _

end

/-! #### §125.2d What the consumers now need

第一の連言に名前をつけて、§122 の消費者を組み直す。`Gam0Drags111` は
`Gam0Hd125` に縮む。 -/

section
open Trans.Recal
open Trans.Dict (BT dict reg collapse)
open TM TM.Term
open Evidence.WF

/-- **`Gam0Drags111` の第一の連言だけ。**  §125.2 は証明しない — 受け取るだけ。 -/
def Gam0Hd125 : Prop := ∀ z : BT, btLe72 1 z = true → BT.isStd z = true →
    dict z = G094 → Hd085 z

/-- **§125.2 の主定理 (2)。**  `Gam0Drags111` は第一の連言と門ひとつに縮む。 -/
theorem gam0Drags_of_hd125 (HD : DictLtStd92) (HH : Gam0Hd125) : Gam0Drags111 :=
  fun z hb hs hd => ⟨HH z hb hs hd, reachOO_of_gam0_125 HD hb hs hd (HH z hb hs hd)⟩

/-- **§125.2 の主定理 (3)。**  326 行がすでに抱えている四条項で書き直したもの。
    `Gam0Drags111` は新しい印を一つも足さない。 -/
theorem gam0Drags_of_four125 (Hp : PsiIdxOKStd172) (HB : IdxLeMix109)
    (H1 : VebIngF114) (H2 : VebRest117) (HH : Gam0Hd125) : Gam0Drags111 :=
  gam0Drags_of_hd125 (dictLtStd_of_four121 Hp (idxMono101_of_psi120 Hp) HB H1 H2) HH

/-! §122 の消費者を組み直したもの。`Hg` の代わりに `Gam0Hd125` を渡す。 -/

theorem tightUp125 (Hp : PsiIdxOKStd172) (HD : DictLtStd92) (HH : Gam0Hd125) :
    TightUp119 := tightUp122 Hp HD (gam0Drags_of_hd125 HD HH)

theorem cofDenseS1_false125 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HD : DictLtStd92)
    (HH : Gam0Hd125) : ¬ CofDenseS1 :=
  cofDenseS1_false122 Hp H2 HD (gam0Drags_of_hd125 HD HH)

theorem gap125 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HD : DictLtStd92)
    (HH : Gam0Hd125) : GapAtG0_107 := gap122 Hp H2 HD (gam0Drags_of_hd125 HD HH)

theorem tight_of_four125 (Hp : PsiIdxOKStd172) (HB : IdxLeMix109) (H1 : VebIngF114)
    (H2 : VebRest117) (HH : Gam0Hd125) : TightUp119 :=
  tight_of_four122 Hp HB H1 H2 (gam0Drags_of_four125 Hp HB H1 H2 HH)

end

/-! ### §125.3 THE HUNT FOR A SECOND WITNESS — WHAT BLOCKS IT IS ONE ORDER FACT

§111.5 の `Gam0Unique111` / `Gam0Drags111` を反証しにいった記録である。**反証は出て
いない。**  出たのは三つ。

  §125.3a **値が `Γ₀` の項は一意ではない — 標準性を外せば。**  `plus` の吸収
          ([Rathjen, 1991] 2.6(ii)) と `wcnf` の尾 `ρ` を使うと、`ψ₀` の引数の
          **後ろに** 運び手 `ψ₀(Ω^Ω)` を置くだけで値は `Γ₀` に戻る。前に置いた桁は
          `1 ⊕ Γ₀ = Γ₀` で消えるか、畳み込みの Veblen 側の値 `v < Γ₀` として
          `plus v Γ₀ = Γ₀` で消える。最小の証人は**大きさ 9**:

              zAbs125  = ψ₀(Ω₁ ⊕ ψ₀(Ω^Ω))      `dict = Γ₀`、引数は標準、外側だけ標準でない
              zPlus125 = ψ₀(1  ⊕ ψ₀(Ω^Ω))      `dict = Γ₀`、`1 + Γ₀ = Γ₀` そのもの

          `gam0UniqueNoStd125_false` が「標準性を外した `Gam0Unique111`」を反証する。
          §122 の `tightUpNoStd122_false` と同じ形の結果である。

  §125.3b **止めているものは一箇所しかない。**  `carrierHead125` — `ψ₀(x)` が標準で
          `Ω^Ω ∈ G(x,0)` なら、`x` の先頭成分の段は 0 ではない (`notHd085_carrier125`)。
          運び手を後ろに置く形は、先頭に段 1 の桁を必ず要求する。ところがその桁は
          `wcnf` で発火して `v ≥ Γ₀` を出すので、`plus v Γ₀ ≠ Γ₀` になる。逃げ道は
          「`Ω^Ω ≤ a` なのに `dict a < Ω^Ω`」という**順序の逆転**ひとつだけである。

  §125.3c **その一箇所を測った — 数え上げで。**  母集団は大きさ 16 までの標準・
          段 1 以下の項 **346487 個** (E は 12 まで 9992 個、E14 は 14 まで 58239 個)。
          `Ω^Ω ≤ a` を満たす主成分は **71950 個**あり、逆転は **0 個**。
          `dict` の `Ω^Ω` の逆像も `Γ₀` の逆像も、大きさ 16 までちょうど 1 つずつ。
          (`Sweep18.lean` は同じ数え上げを大きさ 18・**2096684 項**まで延ばした。
          `dict z = Γ₀` はやはり大きさ 5 の 1 項だけである。)

  §125.3.4 **同じ一箇所を作って測った — 数え上げでは届かない大きさで。**  段 1 の桁を
          **7454 個**作った (大きさ 89 まで、§122 の第六の族の 16 をはるかに超える)。
          `Ω^Ω ≤ a` は **5955 個**で成り立ち、逆転は **0 個**。そして
          `ψ₀(a ⊕ ψ₀(Ω^Ω))` は、**先頭の条件を通る 5955 個では値が `Γ₀` にならず、
          値が `Γ₀` になる 210 個では先頭の条件を通らない** — 重なりは 0 個である。
          §125.3b の二つの要求はこの母集団の上でちょうど排反している。

**測定の母集団について (§111.7 の失敗様式の修理)。**  §111.7 は「9992 項のうち前提
`dict z = G094` が 1 回だけ発火した」と書いた。仮説の見えない母集団である。ここでは
前提が**発火する項を作った** — `absFam125` の 6483 項のうち **2933 項**が
`dict z = G094` を満たし、そのうち **1656 項**は `ψ₀` の引数まで標準で、
**2933 項すべてが `Gam0Drags111` の結論を満たす**。二桁の族 `absFam2_125` でも
1593/1593。**`Gam0Drags111` は、前提が本当に発火する 4526 項の上で成り立っている。**

**まだ定理ではない。**  §125.3b の還元は紙の議論で、Lean にあるのは
`carrierHead125` / `notHd085_carrier125` だけである。残りは `NoInvOO125` —
`dict` が `Ω^Ω` のところで順序を保つこと。それは `DictLtStd92` の一点版である。
**`Gam0Unique111` も `Gam0Drags111` も反証できなかった。**  行 326 の密度の側は
`Gam0Drags111` に懸かったままで、この節はそれを外していない。 -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

set_option maxRecDepth 1000000

/-! #### §125.3a Two witnesses of value `Γ₀` -/

/-- **吸収の証人。**  `ψ₀(Ω₁ ⊕ ψ₀(Ω^Ω))` — 前の桁 `Ω₁` は `wcnf` の Veblen 側で
    `v = φ̄(1,0) = ε₀ < Γ₀` になり、`plus v Γ₀ = Γ₀` で消える。 -/
def zAbs125 : BT := BT.D 0 (BT.sum (BT.Om 1) (BT.D 0 bOO94))

/-- **`plus` そのものの証人。**  `ψ₀(1 ⊕ ψ₀(Ω^Ω))` — `1 + Γ₀ = Γ₀`。 -/
def zPlus125 : BT := BT.D 0 (BT.sum BT.one (BT.D 0 bOO94))

theorem dict_zAbs125 : dict zAbs125 = G094 := rfl
theorem dict_zPlus125 : dict zPlus125 = G094 := rfl
theorem btLe1_zAbs125 : btLe72 1 zAbs125 = true := rfl
theorem btLe1_zPlus125 : btLe72 1 zPlus125 = true := rfl
theorem notStd_zAbs125 : BT.isStd zAbs125 = false := rfl
theorem notStd_zPlus125 : BT.isStd zPlus125 = false := rfl

/-- **`zAbs125` は外側の `ψ₀` だけで標準性を外れる。**  引数は標準である。 -/
theorem std_arg_zAbs125 : BT.isStd (BT.sum (BT.Om 1) (BT.D 0 bOO94)) = true := rfl

/-- 外れる理由は係数の条件ひとつ — `Ω^Ω` が引数より小さくない。 -/
theorem why_notStd_zAbs125 : BT.lt bOO94 (BT.sum (BT.Om 1) (BT.D 0 bOO94)) = false := rfl

theorem ne_zAbs125 : zAbs125 ≠ bTowG98 0 := by decide
theorem ne_zPlus125 : zPlus125 ≠ bTowG98 0 := by decide

theorem size_zAbs125 : BT.size zAbs125 = 9 := rfl
theorem size_zPlus125 : BT.size zPlus125 = 9 := rfl

/-- `Gam0Unique111` から標準性を外したもの。 -/
def Gam0UniqueNoStd125 : Prop :=
  ∀ z : BT, btLe72 1 z = true → dict z = G094 → z = bTowG98 0

/-- **`Gam0Unique111` の標準性は運んでいる。**  外すと吸収の族が反例になる。 -/
theorem gam0UniqueNoStd125_false : ¬ Gam0UniqueNoStd125 := fun H =>
  ne_zAbs125 (H zAbs125 btLe1_zAbs125 dict_zAbs125)

/-! #### §125.3b The drag conclusion survives on the witnesses -/

theorem hd085_zAbs125 : Hd085 zAbs125 := by
  intro z hz
  exact ⟨BT.sum (BT.Om 1) (BT.D 0 bOO94), List.mem_singleton.mp hz⟩

theorem hd085_zPlus125 : Hd085 zPlus125 := by
  intro z hz
  exact ⟨BT.sum BT.one (BT.D 0 bOO94), List.mem_singleton.mp hz⟩

theorem memOO_absArg125 (a : BT) : bOO94 ∈ BT.GB 0 (BT.sum a (BT.D 0 bOO94)) := by
  show bOO94 ∈ BT.GB 0 a ++ (bOO94 :: BT.GB 0 bOO94)
  exact List.mem_append.mpr (Or.inr (List.Mem.head _))

/-- **`Gam0Drags111` の結論は証人の上で成り立つ。**  反例ではない。 -/
theorem drags_zAbs125 : Hd085 zAbs125 ∧ ∃ e ∈ BT.GB 0 zAbs125, BT.le bOO94 e = true :=
  ⟨hd085_zAbs125, ⟨bOO94, List.Mem.tail _ (memOO_absArg125 (BT.Om 1)), bt_le_refl108 bOO94⟩⟩

theorem drags_zPlus125 : Hd085 zPlus125 ∧ ∃ e ∈ BT.GB 0 zPlus125, BT.le bOO94 e = true :=
  ⟨hd085_zPlus125, ⟨bOO94, List.Mem.tail _ (memOO_absArg125 BT.one), bt_le_refl108 bOO94⟩⟩

/-! #### §125.3c What blocks the family — a theorem, not a measurement -/

/-- 先頭の成分の段は 0 ではない — `Ω^Ω` が `ψ₀` の引数より小さいことの内訳。 -/
theorem headHi_of_ltOO125 : ∀ (n : Nat) (l : List BT),
    BT.ltL n (BT.toL bOO94) l = true → ∃ v w tl, l = BT.D v w :: tl ∧ v ≠ 0
  | 0, l, h => by
      have e : BT.ltL 0 (BT.toL bOO94) l = false := rfl
      rw [e] at h; exact Bool.noConfusion h
  | n + 1, [], h => by
      have e : BT.ltL (n + 1) (BT.toL bOO94) ([] : List BT) = false := rfl
      rw [e] at h; exact Bool.noConfusion h
  | n + 1, BT.zero :: qs, h => by
      have e : BT.ltL (n + 1) (BT.toL bOO94) (BT.zero :: qs) = false := rfl
      rw [e] at h; exact Bool.noConfusion h
  | n + 1, BT.sum a b :: qs, h => by
      have e : BT.ltL (n + 1) (BT.toL bOO94) (BT.sum a b :: qs) = false := rfl
      rw [e] at h; exact Bool.noConfusion h
  | n + 1, BT.D 0 c :: qs, h => by
      have e : BT.ltL (n + 1) (BT.toL bOO94) (BT.D 0 c :: qs) = false := rfl
      rw [e] at h; exact Bool.noConfusion h
  | _ + 1, BT.D (v + 1) c :: qs, _ => ⟨v + 1, c, qs, rfl, Nat.succ_ne_zero v⟩

/-- **§125.3b の主定理。**  `ψ₀(x)` が標準で `Ω^Ω ∈ G(x,0)` なら、`x` の先頭成分は
    段 1 以上の桁である。運び手を後ろに置く形は、必ず段 1 の桁を先頭に呼ぶ。 -/
theorem carrierHead125 {x : BT} (hs : BT.isStd (BT.D 0 x) = true)
    (hm : bOO94 ∈ BT.GB 0 x) : ∃ v w tl, BT.toL x = BT.D v w :: tl ∧ v ≠ 0 :=
  headHi_of_ltOO125 _ _ ((std0_split82 hs).2 bOO94 hm)

/-- 同じことを `Hd085` で。 -/
theorem notHd085_carrier125 {x : BT} (hs : BT.isStd (BT.D 0 x) = true)
    (hm : bOO94 ∈ BT.GB 0 x) : ¬ Hd085 x := by
  obtain ⟨v, w, tl, he, hv⟩ := carrierHead125 hs hm
  intro hd
  obtain ⟨c, hc⟩ := hd (BT.D v w) (by rw [he]; exact List.Mem.head tl)
  injection hc with hv0 _
  exact hv hv0

/-- 吸収の族に当てた形 — どの `a` でも先頭は段 1 の桁でなければならない。 -/
theorem absFam_head125 (a : BT)
    (hs : BT.isStd (BT.D 0 (BT.sum a (BT.D 0 bOO94))) = true) :
    ∃ v w tl, BT.toL (BT.sum a (BT.D 0 bOO94)) = BT.D v w :: tl ∧ v ≠ 0 :=
  carrierHead125 hs (memOO_absArg125 a)

/-- **残った一点。**  `dict` が `Ω^Ω` のところで順序を保つこと。**証明しない。**
    これが成り立てば §125.3b の議論で `Gam0Unique111` が閉じる。 -/
def NoInvOO125 : Prop := ∀ a : BT, btLe72 1 a = true → BT.isStd a = true →
    BT.isP a = true → BT.le bOO94 a = true → le (dict bOO94) (dict a) = true

/-! #### §125.3d Measurement (frozen)

**構成を先に書く。**  母集団は三つ。ひとつは数え上げ、ふたつは作ったもの。

    E16   大きさ 16 までの標準・段 1 以下の項を全部 (`lvBT108 15`、346487 項)。
          `isStd` は部分項へ遺伝するので数え落としはない。E は 12 まで 9992 項、
          E14 は 14 まで 58239 項なので、これは E14 の 5.95 倍である。
    A     吸収の族 `absFam125` — `ψ₀(a ⊕ ψ₀(Ω^Ω))`、`a` は E の主成分 6483 個。
          **標準性で濾さない。**  濾さないことがこの節の要点である。
    A2    同じ形の二桁版 `absFam2_125` — `ψ₀(a ⊕ b ⊕ ψ₀(Ω^Ω))`、2500 項。
    A3    **対照** — 運び手を**前**に置いた `ψ₀(Ω^Ω ⊕ a)`、6483 項。 -/

def prinE125 : List BT := allStd108.filter BT.isP
def absArg125 : List BT := prinE125.map fun a => BT.sum a (BT.D 0 bOO94)
def absFam125 : List BT := absArg125.map (BT.D 0 ·)
def prinS125 : List BT := allStd108.filter fun a => BT.isP a && BT.size a <= 6
def absFam2_125 : List BT :=
  prinS125.flatMap fun a => prinS125.map fun b => BT.D 0 (BT.sum a (BT.sum b (BT.D 0 bOO94)))
def absFam3_125 : List BT := prinE125.map fun a => BT.D 0 (BT.sum bOO94 a)

/-- `Gam0Drags111` の結論の判定器。 -/
def dragB125 (z : BT) : Bool := hd085B z && (BT.GB 0 z).any (fun e => BT.le bOO94 e)

/-! **A — 前提が発火する母集団は作れる。**  6483 項のうち **2933 項**で
    `dict z = G094` が成り立ち、**1656 項**は `ψ₀` の引数まで標準で、
    外側の `ψ₀` ひとつで標準性を外れる。標準なものは **0 項** (§125.3b のとおり)。
    そして **2933 項すべてが `Gam0Drags111` の結論を満たす**。 -/
#guard (prinE125.length, absFam125.length,
        absFam125.countP fun z => dict z == G094,
        absFam125.countP fun z => dict z == G094 && dragB125 z,
        absFam125.countP fun z => dict z == G094 && BT.isStd z,
        absArg125.countP fun x => dict (BT.D 0 x) == G094 && BT.isStd x)
    == (6483, 6483, 2933, 2933, 0, 1656)

/-! **A2 — 桁を二つ前に置いても同じ。**  1593/2500 が値 `Γ₀`、結論は 1593/1593、
    標準は 0。 -/
#guard (absFam2_125.length,
        absFam2_125.countP fun z => dict z == G094,
        absFam2_125.countP fun z => dict z == G094 && dragB125 z,
        absFam2_125.countP fun z => dict z == G094 && BT.isStd z)
    == (2500, 1593, 1593, 0)

/-! **A3 — 運び手を前に置く修理は値を外す。**  標準なものは 3033 項あるが、
    値が `Γ₀` のものは **0 項** — 発火した畳み込みは `Γ₀` を返し、そのうしろに
    `ρ` が付くので `Γ₀ ⊕ ρ ≠ Γ₀` になる。**位置が全部である。** -/
#guard (absFam3_125.length, absFam3_125.countP fun z => dict z == G094,
        absFam3_125.countP BT.isStd) == (6483, 0, 3033)

/-- 各大きさで (項数, `dict z = Γ₀`, `dict z = Ω^Ω`, `Ω^Ω ≤ z` の主成分, 順序の逆転)。 -/
def scan125 (L : List BT) : Nat × Nat × Nat × Nat × Nat :=
  let w := dict bOO94
  L.foldl (init := (0, 0, 0, 0, 0)) fun s z =>
    let d := dict z
    let hi := BT.isP z && BT.le bOO94 z
    (s.1 + 1,
     s.2.1 + (if d == G094 then 1 else 0),
     s.2.2.1 + (if d == w then 1 else 0),
     s.2.2.2.1 + (if hi then 1 else 0),
     s.2.2.2.2 + (if (hi && lt d w) || (BT.isP z && BT.lt z bOO94 && le w d) then 1 else 0))

/-! **E16 — 数え上げ、大きさ 1 から 16 まで。**  `Γ₀` の逆像も `Ω^Ω` の逆像も
    ちょうど 1 つずつ (大きさ 5 と 4)。**そして `Ω^Ω ≤ a` の主成分 71950 個の上で
    順序の逆転は 0 個** — §125.3b が残した一点は、正しい母集団の上で測って空である。
    §111.7 は前提が 1 回しか発火しない母集団を測った。ここは違う。 -/
#guard ((lvBT108 15).map scan125) ==
  [(1, 0, 0, 0, 0), (2, 0, 0, 0, 0), (4, 0, 0, 0, 0), (7, 0, 1, 1, 0),
   (15, 1, 0, 2, 0), (33, 0, 0, 4, 0), (79, 0, 0, 11, 0), (184, 0, 0, 29, 0),
   (432, 0, 0, 72, 0), (1013, 0, 0, 181, 0), (2418, 0, 0, 446, 0), (5804, 0, 0, 1109, 0),
   (14063, 0, 0, 2764, 0), (34184, 0, 0, 6908, 0), (83497, 0, 0, 17251, 0),
   (204751, 0, 0, 43172, 0)]

/-! #### §125.3e The built digit pool — do not enumerate, build

数え上げは大きさ 16 で止まる。§122 の第六の族の第一項は大きさ 16 だった。ここでは
段 1 の桁を **大きさ 89 まで**作って、§125.3b が残した一点をそこで測る。 -/

def seed125 : List BT :=
  [BT.zero, BT.one, BT.Om 1, BT.D 1 (BT.D 1 BT.zero), bOO94, BT.D 0 bOO94,
   bTowG98 1, bTowG98 2, cSix122 (bTowG98 0), BT.D 1 (BT.D 1 (BT.D 0 bOO94)),
   BT.D 1 (BT.sum (BT.Om 1) (BT.Om 1)), BT.sum bOO94 bOO94,
   BT.D 1 (BT.D 1 (BT.sum (BT.D 1 BT.zero) BT.one))]

def grow125 (P : List BT) : List BT :=
  ((P.map (BT.D 1 ·)) ++ (P.map (BT.D 0 ·)) ++
   (P.flatMap fun a => P.map fun b => BT.sum a b)).filter
     fun t => btLe72 1 t && BT.isStd t

def pool125 : List BT := (seed125 ++ grow125 seed125).eraseDups
def poolB125 : List BT := (pool125 ++ grow125 pool125).eraseDups

/-- 作った段 1 の桁。 -/
def dig125 : List BT :=
  ((poolB125.map (BT.D 1 ·)) ++
   (poolB125.flatMap fun a => pool125.map fun b => BT.D 1 (BT.sum a b))).filter
     fun t => btLe72 1 t && BT.isStd t

/-- 運び手を後ろに置いた `ψ₀` の引数。 -/
def carrArg125 (a : BT) : BT := BT.sum a (BT.D 0 bOO94)

/-! **母集団の大きさ。**  7454 個の段 1 の桁、大きさは 89 まで。 -/
#guard (pool125.length, poolB125.length, dig125.length,
        (dig125.map BT.size).foldl max 0) == (87, 1160, 7454, 89)

/-! **順序の逆転は作っても出ない。**  `Ω^Ω ≤ a` は 5955 個で成り立ち、
    `dict a < Ω^Ω` になるものは **0 個**。逆向きも 0 個。 -/
#guard (dig125.countP fun a => BT.le bOO94 a,
        dig125.countP fun a => BT.le bOO94 a && lt (dict a) (dict bOO94),
        dig125.countP fun a => BT.lt a bOO94 && le (dict bOO94) (dict a))
    == (5955, 0, 0)

/-! **二つの要求はちょうど排反している。**  `carrierHead125` の必要条件
    `Ω^Ω < a ⊕ ψ₀(Ω^Ω)` を通るのは 5955 個、値が `Γ₀` になるのは 210 個、
    **両方を満たすものは 0 個**。標準で値が `Γ₀` のものも 0 個。 -/
#guard (dig125.countP fun a => BT.lt bOO94 (carrArg125 a),
        dig125.countP fun a => dict (BT.D 0 (carrArg125 a)) == G094,
        dig125.countP fun a => BT.lt bOO94 (carrArg125 a)
                               && dict (BT.D 0 (carrArg125 a)) == G094,
        dig125.countP fun a => BT.isStd (BT.D 0 (carrArg125 a))
                               && dict (BT.D 0 (carrArg125 a)) == G094)
    == (5955, 210, 0, 0)

/-! **作った母集団のなかで値が `Γ₀` の標準な `ψ₀` の項は `ψ₀(Ω^Ω)` ひとつ。** -/
#guard (poolB125.map (BT.D 0 ·)).filter (fun z => BT.isStd z && dict z == G094)
    == [bTowG98 0]

end

/-! ### §125.4 THE COMPOSITION — `Gam0Drags111` LEAVES, AND THE CERTIFICATE DIES WITH IT

§125.1 は第一の連言を `PsiIdxOKStd172` から出し、§125.2 は第二の連言を `DictLtStd92` から
出す。二つを繋ぐと `Gam0Drags111` は仮定ではなくなる。そして §121 が `DictLtStd92` を
326 行がすでに抱えている三つから出すので、条項は一つも増えない。

その先が問題である。§122 は `Gam0Drags111` から `¬ DictDenseMid107` を出していた。
いま `Gam0Drags111` はその三つから出る。ところが `certIn_t326_124` はその三つ**と**
`DictDenseMid107` を同時に取る。**両立しない。** -/

section
open Trans.Recal
open Trans.Dict (BT dict reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§125 の主定理 (1)。**  第一の連言は `PsiIdxOKStd172` だけで出る (§125.1a)。 -/
theorem gam0Hd_of_psi125 (Hp : PsiIdxOKStd172) : Gam0Hd125 :=
  fun _ hb hs hd => hd085_of_gam0_125 Hp hb hs hd

/-- **§125 の主定理 (2)。**  `Gam0Drags111` は条項ではない — 二つの門から出る。 -/
theorem gam0Drags125 (Hp : PsiIdxOKStd172) (HD : DictLtStd92) : Gam0Drags111 :=
  gam0Drags_of_hd125 HD (gam0Hd_of_psi125 Hp)

/-- §121 の `DictLtStd92`、326 行の三条項から。 -/
theorem dictLtStd125 (Hp : PsiIdxOKStd172) (H1 : VebIngF114) (H2 : VebRest117) :
    DictLtStd92 := dictLtStd121 Hp (hiMono_of_two124 Hp H1 H2)

/-- 同じ三つから `DictLtA74` も出る (§81 と §99)。 -/
theorem dictLtA74_125 (Hp : PsiIdxOKStd172) (H1 : VebIngF114) (H2 : VebRest117) :
    DictLtA74 :=
  dictLtA74_81 Hp (collapseMono0Hi_of_hiMono99 Hp (hiMono_of_two124 Hp H1 H2))

/-- **§125 の主定理 (3)。**  326 行がすでに抱えている三つだけで `Gam0Drags111` が出る。
    §111.5 が命名し §111.7 が測り §122 が全体を乗せた条項は、条項ではなかった。 -/
theorem gam0Drags_of_three125 (Hp : PsiIdxOKStd172) (H1 : VebIngF114) (H2 : VebRest117) :
    Gam0Drags111 :=
  gam0Drags125 Hp (dictLtStd125 Hp H1 H2)

/-! **五つの密度の主張は、326 行の仮定だけで偽になる。** -/

theorem denseMid107_false125 (Hp : PsiIdxOKStd172) (H1 : VebIngF114) (H2 : VebRest117) :
    ¬ DictDenseMid107 :=
  denseMid107_false122 Hp (dictLtA74_125 Hp H1 H2) (dictLtStd125 Hp H1 H2)
    (gam0Drags_of_three125 Hp H1 H2)

theorem denseMid102_false125 (Hp : PsiIdxOKStd172) (H1 : VebIngF114) (H2 : VebRest117) :
    ¬ DictDenseMid102 :=
  denseMid102_false122 Hp (dictLtA74_125 Hp H1 H2) (dictLtStd125 Hp H1 H2)
    (gam0Drags_of_three125 Hp H1 H2)

theorem dictDenseHi94_false125 (Hp : PsiIdxOKStd172) (H1 : VebIngF114) (H2 : VebRest117) :
    ¬ DictDenseHi94 :=
  dictDenseHi94_false122 Hp (dictLtA74_125 Hp H1 H2) (dictLtStd125 Hp H1 H2)
    (gam0Drags_of_three125 Hp H1 H2)

theorem dictDense85_false125 (Hp : PsiIdxOKStd172) (H1 : VebIngF114) (H2 : VebRest117) :
    ¬ DictDense85 :=
  dictDense85_false122 Hp (dictLtA74_125 Hp H1 H2) (dictLtStd125 Hp H1 H2)
    (gam0Drags_of_three125 Hp H1 H2)

theorem cofDenseS1_false_three125 (Hp : PsiIdxOKStd172) (H1 : VebIngF114)
    (H2 : VebRest117) : ¬ CofDenseS1 :=
  cofDenseS1_false122 Hp (dictLtA74_125 Hp H1 H2) (dictLtStd125 Hp H1 H2)
    (gam0Drags_of_three125 Hp H1 H2)

/-- §108 と §111 と §113 の条項も、同じ三つから出る。 -/
theorem gapAtG0_125 (Hp : PsiIdxOKStd172) (H1 : VebIngF114) (H2 : VebRest117) :
    GapAtG0_107 :=
  gap122 Hp (dictLtA74_125 Hp H1 H2) (dictLtStd125 Hp H1 H2)
    (gam0Drags_of_three125 Hp H1 H2)

theorem tightUp_of_three125 (Hp : PsiIdxOKStd172) (H1 : VebIngF114) (H2 : VebRest117) :
    TightUp119 :=
  tightUp122 Hp (dictLtStd125 Hp H1 H2) (gam0Drags_of_three125 Hp H1 H2)

/-- **§125 の帰結。**  `certIn_t326_124` の第一・第二・第三の仮定は、その第五の仮定を
    偽にする。 -/
theorem certHyp_absurd125 (Hp : PsiIdxOKStd172) (H1 : VebIngF114) (H2 : VebRest117)
    (HD3 : DictDenseMid107) : False :=
  denseMid107_false125 Hp H1 H2 HD3

end

/-! ### §125.5 The same thing written on §124's own argument list

`certIn_t326_124` の引数をそのまま並べて `False` を出す。証明書が空虚であるとは
この形のことである。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- **326 行の証明書は適用できない。**  `certIn_t326_124` と同じ仮定を取り、`False` を
    返す。仮定が両立しないので、あの証明書からは何も出ない。 -/
theorem certIn_t326_vacuous125 (Hp : PsiIdxOKStd172) (H1 : VebIngF114) (H2 : VebRest117)
    (_HD1 : DictOntoMidOpen103) (HD3 : DictDenseMid107) (_HD4 : DictDenseAbove107)
    (_hacc : Acc Evidence.WF.RT (vOf t326)) : False :=
  certHyp_absurd125 Hp H1 H2 HD3

end
end Evidence.Region
