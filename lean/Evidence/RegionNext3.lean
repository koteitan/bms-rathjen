import Evidence.RegionNext2

/-
Evidence/RegionNext3.lean — THE GATES ROW 326 STILL WAITS ON

`RegionNext2` took the region as far as `Hclosed`, `Hzero`, the value, and the order
theory (§61-§79).  This file is the part that is still moving: the K-gate (§80, §82,
§84, §86, §87), the Veblen fold (§81), and cofinality (§83, §85).
-/

namespace Evidence.Region

open BMS

/-! ## §80 THE `aV` SIDE — THE COEFFICIENT DROPS OUT, AND WHAT IS LEFT SITS ABOVE `Ω₁`

§78 proved (K4), narrowed the whole `K`-gate to one clause `LocalK2_78`, split it at `aV` and
`cV`, and measured that **all 87 failures are the `aV` side**.  §80 attacks that side.  It
does not close it.  What it does is take the clause apart until the part that is genuinely
open is one comparison about one `ψ`-argument, prove everything else, and say — with a
theorem, not a measurement — that nothing was given away in the taking apart.

WHAT IS PROVED, UNCONDITIONALLY.

  §80.1  **THE COEFFICIENT DROPS OUT.**  `Δ = W^(aV ⊖ W)·cV`, and the coefficient never
         contributes: `le_powOf_ddOf80` is `W^(aV ⊖ W) ≤ Δ` and needs nothing but `cV ≠ 0`.
         The proof is `ω^·` monotone (§65.3) under `e ≤ e ⊕ log cV₀` (§65.4), then "a sum
         dominates its HEAD" — which is `lt_atom_add`, clause 2.3.11, and **not** §75.1's
         `le_ofList_append75`: §75 needed the tail dominated, here it is the head.
         `wcnf_snd_ne_zero80` supplies `cV ≠ 0` for every pair the scan emits — `wC` is an
         `ω`-power, and the merging branch `plus (wC w p) c'` survives because `s ⊕ t = 0`
         forces `s = 0` (§78.1's argument, re-derived).  **Measured: 0 disagreements on 635
         firing pairs.**  `localK2Fst_of_pow80` is the resulting coefficient-free residual.

  §80.2  **THE RESIDUAL, COEFFICIENT-FREE.**  `LocalK2Pow_80` is `LocalK2Fst_78` with `Δ`
         replaced by `W^(aV ⊖ W)`, and `localK2Fst_of_pow80` is the implication.  One of the
         two factors of the right-hand side is gone for good.

  §80.3  **EVERY `K`-ELEMENT BELOW `Ω₁` IS FREE.**  `lt_dd_of_lt_reg80` — no side condition at
         all: if `y ∈ K_{Ω₁} aV` and `y < Ω₁` then `y < Δ`.  Two cases, and both are
         forcings: either `aV ⊖ Ω₁ = 0`, and then §78.1's `subAP`/`Kset` forcing makes
         `K_{Ω₁} aV` EMPTY, or it is not, and then `Ω₁ = ω^{Ω₁} ≤ W^(aV ⊖ Ω₁) ≤ Δ`.
         **458 of the 635 firing steps, and 89 of the 102 inside the region, close on this
         lemma alone.**  The same lemma NAMES the `cV` side: `localK2Snd_of_below80` derives
         §78's `LocalK2Snd_78` from `LocalKSndBelow_80` — *if `K_{Ω₁} cV` is non-empty then
         `aV ⊖ Ω₁ ≠ 0` and its elements lie below `Ω₁`* — which is a HYPOTHESIS, not a
         theorem, and §80.7 measures where it breaks.

  §80.4  **SO THE `aV` SIDE IS EXACTLY ITS RESTRICTION TO `Ω₁ ≤ y`.**  `localK2Fst_iff_big80`
         is an **equivalence**, not a reduction: `LocalK2Fst_78 ↔ LocalK2Big_80`.  What is
         left to prove has shrunk from every `K`-element of 635 pairs to the 177 steps that
         carry an element `≥ Ω₁` — and an element of `K_{Ω₁}` above `Ω₁` is, by
         [Rathjen, 1991] 2.2(vi), the ARGUMENT of a `ψ_π` with `Ω₁ ≤ π` sitting inside `aV`.
         The open statement is therefore exactly: *a collapsing function occurring inside `aV`
         has its argument below `Ω₁^{aV ⊖ Ω₁}`* — the transport of Buchholz's `G(a,0) < a`
         that §68, §72, §73, §75 and §78 all named, now with nothing else attached to it.
         `LocalK2BigPow_80` applies both reductions at once and is the smallest residual;
         `certIn_t326_big80` re-derives row 326's certificate on top of it.

  §80.5  **THE COEFFICIENT-FREE DECIDER.**  `k2fb80` never looks at `cV`, and
         `localK2FstT_of_b80` turns it into the `aV` half of the clause for one term — a guard
         IS a proof, as in §78.4.  Frozen on §78's two witnesses, both with a non-empty
         `K_{Ω₁} aV`: a `ψ`-nesting-9 tower and a width-2 sum.

  §80.6  **THE NEGATIVE THEOREM.**  `not_pow80_bad80` — see the measurement below.

WHAT IS **NOT** CLAIMED.  `LocalK2Fst_78` is NOT proved; neither is `LocalK2Snd_78`, and
`LocalKSndBelow_80` is a hypothesis.  `certIn_t326_big80` re-derives row 326's certificate
from `LocalK2Big_80` and `LocalK2Snd_78` in place of §78's `LocalK2_78`, and that is the same
strength, not less: the equivalence above says so.  What §80 changes is the SHAPE of what is
left, and how much of the corpus still has to be looked at.  Nothing here proves
`DictHeadLt77`, `CofDenseS1` or `BCofIn71`.

WHAT THE MEASUREMENT SAYS (§80.7 gives the construction: §78.5's three populations verbatim,
plus one new group built to answer §80's own question).  **The negative results first.**

  * **The residual is not a fact about 𝔗(M).**  `bad80 = Ω₁ ⊕ ψ_{Ω₁}(Ω₂)` is a 𝔗(M) term
    with `Ω₁ ≤ bad80` and `K_{Ω₁} bad80 = {Ω₂}`, and `Ω₂` reaches neither `W^(bad80 ⊖ Ω₁)`
    nor `Δ`.  `not_pow80_bad80` freezes it.  **So no proof of `LocalK2Big_80` can go through
    the pair `(aV, cV)` alone** — it must consume `dict` and `BT.isStd`, and §80 says exactly
    which consumption is left.
  * **The residual cannot be sharpened.**  On the 635 steps, `y < ω^{Ω₁·(aV ⊖ Ω₁)}` fails 87
    times — all outside the region — while dropping the `ω^·` costs 40 more: both
    `y < Ω₁·(aV ⊖ Ω₁)` and §73.7's `y < aV` fail **127** times.  The exponentiation is
    load-bearing, and §73's comparison against `aV` is still the wrong one.
  * **The `Ω₁`-bound on the `cV` side breaks the moment the level bound does.**
    `LocalKSndBelow_80` holds at all 443 firing steps whose term satisfies `btLe72 1` and
    fails at 3 of the 206 new steps, every one of them on a term with `btLe72 1 = false` and
    `btLe72 2 = true`.  The `cV` clause ITSELF (`K_{Ω₁} cV < Δ`) still holds at all 635.
  * **The level bound is not what carries (K2').**  The new group is 223 Buchholz-standard
    terms, and 192 of them have `ψ₂` inside, so they break `btLe72 1`; (K2') and (K4) fail at
    **0** of their 206 firing steps, while §73.7's (K2) fails at 35.  §78 saw this on 51
    bumped terms; at 223, with three widths, it is not an artefact.  **`BT.isStd` is the side
    condition; the level bound is scaffolding.**

  The positive side.  The `K`-sets are not idle anywhere the theorems are used: `K_{Ω₁} aV` is
  non-empty at 68 of the 206 new steps and at every one of them carries an element `≥ Ω₁`;
  the residual is non-vacuous at 177 of the 635 steps and at 13 of the region's 102.  The 11
  steps with `aV ⊖ Ω₁ = 0` — the branch §80.2 forces — have BOTH `K`-sets empty, which is why
  §80.4's hypothesis is not contradictory.  Replacing `Δ` by `W^(aV ⊖ Ω₁)` changes no verdict
  at any of the 635.
-/

/-! ### §80.1 係数は落ちる — `W^(aV ⊖ W) ≤ Δ` -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- `ofList l = 0` は列が空か `[0]` のときだけ (§78.1 と同じ、`private` なので引き直す)。 -/
private theorem ofList_eq_zero80 : ∀ (l : List Term), ofList l = zero → l = [] ∨ l = [zero]
  | [], _ => Or.inl rfl
  | [a], h => Or.inr (by rw [show a = zero from h])
  | _ :: _ :: _, h => absurd h (by intro hc; exact Term.noConfusion hc)

/-- `s ⊕ t = 0` なら両方 `0` (§78.1 と同じ)。 -/
private theorem plus_eq_zero80 {s t : Term} (ht : inT t = true) (h : plus s t = zero) :
    s = zero ∧ t = zero := by
  cases hl : toList t with
  | nil => rw [plus_nil hl] at h; exact ⟨h, toList_eq_nil t hl⟩
  | cons b1 r =>
    exfalso
    rw [plus_cons66 hl] at h
    have hb1 : b1 ∈ (toList s).filter (fun a => le b1 a) ++ (b1 :: r) :=
      List.mem_append.mpr (Or.inr (List.Mem.head _))
    rcases ofList_eq_zero80 _ h with h2 | h2
    · rw [h2] at hb1; cases hb1
    · rw [h2] at hb1
      have hz : b1 = zero := List.mem_singleton.mp hb1
      have hap : b1.isAP = true := inTL_isAP ht b1 (by rw [hl]; exact List.Mem.head _)
      rw [hz] at hap
      exact Bool.noConfusion hap

/-- **和はその先頭成分以上。** §12 の 2.3.11 (`lt_atom_add`) そのもの — §75.1 が要った
    「和は右の被加数以上」の反対側で、こちらは 1 行で済む。 -/
private theorem le_head_ofList80 {x : Term} (hx : x.isAP = true) :
    ∀ (r : List Term), le x (ofList (x :: r)) = true
  | [] => Evidence.WF.le_self x
  | y :: t => by
      show ((x == add x (ofList (y :: t))) || lt x (add x (ofList (y :: t)))) = true
      rw [lt_atom_add (isAtom_of_isAP hx), Evidence.WF.le_self]
      exact Bool.or_true _

/-- **`ω^e ≤ e·c`。** 係数が `0` でなければ、`e·c` の先頭成分が `ω^e` を超える。 -/
theorem le_pow_mulL80 {e c : Term} (he : inT e = true) (hc : inT c = true) (hcz : c ≠ zero) :
    le (omegaNF e) (mulL e c) = true := by
  cases hl : toList c with
  | nil => exact absurd (toList_eq_nil c hl) hcz
  | cons p rest =>
    have hp : inT p = true := inTL_inT hc p (by rw [hl]; exact List.Mem.head _)
    have hmul : mulL e c = ofList (omegaNF (plus e (logOm p)) ::
        rest.map (fun q => omegaNF (plus e (logOm q)))) := by
      show ofList ((toList c).map _) = _
      rw [hl, List.map_cons]
    have h1 : le (omegaNF e) (omegaNF (plus e (logOm p))) = true := by
      refine omegaNF_mono_inT he (inT_plus he (inT_logOm hp)) ?_
      have h2 := plus_mono_right_inT e he zero (logOm p) inT_zero (inT_logOm hp)
        (le_zero_left _)
      rwa [plus_nil (show toList (zero : Term) = [] from rfl)] at h2
    have h3 : le (omegaNF (plus e (logOm p))) (mulL e c) = true := by
      rw [hmul]; exact le_head_ofList80 (isAP_omegaNF _) _
    exact le_trans_inT (inT_omegaNF he) (inT_omegaNF (inT_plus he (inT_logOm hp)))
      (inT_mulL mulDescInT he hc) h1 h3

/-- `w` が `ω^w = w` を満たすなら `w ≤ w·s`。 -/
theorem le_self_mulL80 {w s : Term} (hw : inT w = true) (hnf : omegaNF w = w)
    (hs : inT s = true) (hsz : s ≠ zero) : le w (mulL w s) = true := by
  have h := le_pow_mulL80 hw hs hsz
  rwa [hnf] at h

/-- `Δ` から係数を落とした量 `W^(aV ⊖ W)`。 -/
def powOf80 (w : Term) (ac : Term × Term) : Term := omegaNF (mulL w (subAP w ac.1))

theorem inT_powOf80 {w : Term} (hw : inT w = true) {ac : Term × Term} (h1 : inT ac.1 = true) :
    inT (powOf80 w ac) = true :=
  inT_omegaNF (inT_mulL mulDescInT hw (inT_subAP h1))

/-- **§80.1 の主定理 — 係数は落ちる。** `W^(aV ⊖ W) ≤ Δ`。 -/
theorem le_powOf_ddOf80 {w : Term} (hw : inT w = true) {ac : Term × Term}
    (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hz : ac.2 ≠ zero) :
    le (powOf80 w ac) (ddOf75 w ac) = true :=
  le_pow_mulL80 (inT_mulL mulDescInT hw (inT_subAP h1)) h3 hz

/-- **`wcnf` の係数は `0` にならない。** `wC` は `ω^·`、併合の枝は `s ⊕ t = 0 → s = 0`。 -/
theorem wcnf_snd_ne_zero80 {w : Term} : ∀ (L : List Term), inTL L = true →
    ∀ ac ∈ (wcnf w L).1, inT ac.2 = true ∧ ac.2 ≠ zero := by
  intro L
  induction L with
  | nil => intro _ ac hac; cases hac
  | cons p rest ih =>
    intro hc ac hac
    obtain ⟨⟨_, hip⟩, hcr⟩ := inTL_cons.mp hc
    have IH := ih hcr
    have hC : inT (wC w p) = true := inT_wC hip
    have hCz : wC w p ≠ zero :=
      show omegaNF (ofList ((toList (logOm p)).filter (fun q => lt q w))) ≠ zero from
        omegaNF_ne_zero76 _
    by_cases hlp : lt p w = true
    · rw [wcnf_cons_lt hlp] at hac; cases hac
    · have hlp' : lt p w = false := bool_false hlp
      rw [wcnf_cons_ge hlp'] at hac
      cases hr : wcnf w rest with
      | mk fst snd =>
        rw [hr] at hac IH
        cases fst with
        | nil =>
          rw [List.mem_singleton.mp hac]
          exact ⟨hC, hCz⟩
        | cons ac0 ps =>
          cases ac0 with
          | mk a' c' =>
            have hac0 := IH (a', c') (List.Mem.head _)
            by_cases heq : (wA w p == a') = true
            · rw [show ((if (wA w p == a') = true
                  then ((wA w p, plus (wC w p) c') :: ps, snd)
                  else ((wA w p, wC w p) :: (a', c') :: ps, snd))).1
                = ((wA w p, plus (wC w p) c') :: ps) from by rw [if_pos heq]] at hac
              rcases List.mem_cons.mp hac with h | h
              · rw [h]
                exact ⟨inT_plus hC hac0.1, fun hz => hCz (plus_eq_zero80 hac0.1 hz).1⟩
              · exact IH ac (List.Mem.tail _ h)
            · rw [show ((if (wA w p == a') = true
                  then ((wA w p, plus (wC w p) c') :: ps, snd)
                  else ((wA w p, wC w p) :: (a', c') :: ps, snd))).1
                = ((wA w p, wC w p) :: (a', c') :: ps) from by rw [if_neg heq]] at hac
              rcases List.mem_cons.mp hac with h | h
              · rw [h]; exact ⟨hC, hCz⟩
              · exact IH ac h

end

/-! ### §80.2 係数なしの残余 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 残る条項の `aV` 側、`Δ` の代わりに `W^(aV ⊖ W)` と比べる形。 -/
def LocalK2Pow_80 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true →
    inT (dict a) = true → lt (dict a) M = true →
    ∀ ac ∈ (wcnf (reg 1) (toList (dict a))).1, le (reg 1) ac.1 = true →
      ∀ y, y ∈ Kset (reg 1) ac.1 → lt y (powOf80 (reg 1) ac) = true

/-- **係数なしの形で十分。** §78 の `LocalK2Fst_78` が出る。 -/
theorem localK2Fst_of_pow80 (H : LocalK2Pow_80) : LocalK2Fst_78 := by
  intro a hb hs hi hl ac hac hle y hy
  obtain ⟨hc, hd⟩ := inT_toList (dict a) hi
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList (dict a)) hc hd
    (ltM_toList (dict a) hi hl)
  obtain ⟨hi1, _, hi2, _⟩ := hallOK ac hac
  have hz := (wcnf_snd_ne_zero80 (toList (dict a)) hc ac hac).2
  exact lt_of_lt_of_le3 (inT_le_fragR y (inT_mem_Kset75 ac.1 hi1 _ y hy))
    (inT_le_fragR _ (inT_powOf80 (inT_reg 1) hi1))
    (inT_le_fragR _ (inT_ddOf75 (inT_reg 1) hi1 hi2))
    (H a hb hs hi hl ac hac hle y hy)
    (le_powOf_ddOf80 (inT_reg 1) hi1 hi2 hz)

end

/-! ### §80.3 `Ω₁` より下の `K` の元はただ -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

private theorem ofList_eq_zero80' : ∀ (l : List Term), ofList l = zero → l = [] ∨ l = [zero]
  | [], _ => Or.inl rfl
  | [a], h => Or.inr (by rw [show a = zero from h])
  | _ :: _ :: _, h => absurd h (by intro hc; exact Term.noConfusion hc)

/-- `subAP w h = 0` なら成分列は空か `[w]` (§78.1 と同じ)。 -/
private theorem subAP_eq_zero80 {w t : Term} (ht : inT t = true) (h : subAP w t = zero) :
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
      rcases ofList_eq_zero80' r h1 with h2 | h2
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

/-- 成分列が空か `[Ω_{u+1}]` なら `K_{Ω_{u+1}}` は空 (§78.1 と同じ)。 -/
private theorem kset_nil_of_toList80 {u : Nat} {t : Term}
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

/-- `ω^{Ω₁} = Ω₁`。 -/
theorem omegaNF_reg1_80 : omegaNF (reg 1) = reg 1 := by rfl

/-- `aV ⊖ W ≠ 0` なら `Ω_{u+1} ≤ W^(aV ⊖ W)`。 -/
theorem le_reg_powOf80 {u : Nat} {ac : Term × Term} (hnf : omegaNF (reg (u+1)) = reg (u+1))
    (h1 : inT ac.1 = true) (hs : subAP (reg (u+1)) ac.1 ≠ zero) :
    le (reg (u+1)) (powOf80 (reg (u+1)) ac) = true := by
  have h2 : le (reg (u+1)) (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) = true :=
    le_self_mulL80 (inT_reg (u+1)) hnf (inT_subAP h1) hs
  have h3 := omegaNF_mono_inT (inT_reg (u+1))
    (inT_mulL mulDescInT (inT_reg (u+1)) (inT_subAP h1)) h2
  rwa [hnf] at h3

/-- **§80.3 の主定理 — `Ω_{u+1}` より下の `K` の元はただ。**  側条件はいっさい要らない。
    `aV ⊖ W = 0` なら `K_{Ω_{u+1}} aV` はそもそも空、そうでなければ `Ω_{u+1} ≤ W^(aV ⊖ W) ≤ Δ`。 -/
theorem lt_dd_of_lt_reg80 {u : Nat} {ac : Term × Term} (hnf : omegaNF (reg (u+1)) = reg (u+1))
    (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hz : ac.2 ≠ zero) {y : Term}
    (hy : y ∈ Kset (reg (u+1)) ac.1) (hlt : lt y (reg (u+1)) = true) :
    lt y (ddOf75 (reg (u+1)) ac) = true := by
  by_cases hs : subAP (reg (u+1)) ac.1 = zero
  · exact (kset_nil_of_toList80 (subAP_eq_zero80 h1 hs) y hy).elim
  · have hyi : inT y = true := inT_mem_Kset75 ac.1 h1 _ y hy
    have hleT : le (reg (u+1)) (ddOf75 (reg (u+1)) ac) = true :=
      le_trans_inT (inT_reg (u+1)) (inT_powOf80 (inT_reg (u+1)) h1)
        (inT_ddOf75 (inT_reg (u+1)) h1 h3)
        (le_reg_powOf80 hnf h1 hs) (le_powOf_ddOf80 (inT_reg (u+1)) h1 h3 hz)
    exact lt_of_lt_of_le3 (inT_le_fragR y hyi) (inT_le_fragR _ (inT_reg (u+1)))
      (inT_le_fragR _ (inT_ddOf75 (inT_reg (u+1)) h1 h3)) hlt hleT

/-- `cV` 側を落とすための仮説 — `K_{Ω₁} cV` が空でないなら `aV ⊖ Ω₁ ≠ 0` で、しかも
    その元は `Ω₁` より下。**定理ではない** — §80.7 が段の上限を外すと 3 歩で破れることを測る。 -/
def LocalKSndBelow_80 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true →
    inT (dict a) = true → lt (dict a) M = true →
    ∀ ac ∈ (wcnf (reg 1) (toList (dict a))).1, le (reg 1) ac.1 = true →
      ∀ y, y ∈ Kset (reg 1) ac.2 →
        subAP (reg 1) ac.1 ≠ zero ∧ lt y (reg 1) = true

/-- **`cV` 側は「`Ω₁` より下」から出る。** §78 が測った易しい方の半分の、正確な内訳。 -/
theorem localK2Snd_of_below80 (H : LocalKSndBelow_80) : LocalK2Snd_78 := by
  intro a hb hs hi hl ac hac hle y hy
  obtain ⟨hc, hd⟩ := inT_toList (dict a) hi
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList (dict a)) hc hd
    (ltM_toList (dict a) hi hl)
  obtain ⟨hi1, _, hi2, _⟩ := hallOK ac hac
  have hz := (wcnf_snd_ne_zero80 (toList (dict a)) hc ac hac).2
  obtain ⟨hsz, hlt⟩ := H a hb hs hi hl ac hac hle y hy
  have hyi : inT y = true := inT_mem_Kset75 ac.2 hi2 _ y hy
  have hleT : le (reg 1) (ddOf75 (reg 1) ac) = true :=
    le_trans_inT (inT_reg 1) (inT_powOf80 (inT_reg 1) hi1)
      (inT_ddOf75 (inT_reg 1) hi1 hi2)
      (le_reg_powOf80 omegaNF_reg1_80 hi1 hsz) (le_powOf_ddOf80 (inT_reg 1) hi1 hi2 hz)
  exact lt_of_lt_of_le3 (inT_le_fragR y hyi) (inT_le_fragR _ (inT_reg 1))
    (inT_le_fragR _ (inT_ddOf75 (inT_reg 1) hi1 hi2)) hlt hleT

end

/-! ### §80.4 残るのは `Ω₁` 以上の `ψ` の引数ひとつ -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 残る条項 — `K` の元のうち `Ω₁` 以上のものだけ。**結論は `Δ` のまま**なので、
    これは `LocalK2Fst_78` を弱めた形になっている。 -/
def LocalK2Big_80 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true →
    inT (dict a) = true → lt (dict a) M = true →
    ∀ ac ∈ (wcnf (reg 1) (toList (dict a))).1, le (reg 1) ac.1 = true →
      ∀ y, y ∈ Kset (reg 1) ac.1 → le (reg 1) y = true →
        lt y (ddOf75 (reg 1) ac) = true

/-- 両方の縮約をかけた最小の残余 — `Ω₁` 以上の元だけ、しかも係数なし。 -/
def LocalK2BigPow_80 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true →
    inT (dict a) = true → lt (dict a) M = true →
    ∀ ac ∈ (wcnf (reg 1) (toList (dict a))).1, le (reg 1) ac.1 = true →
      ∀ y, y ∈ Kset (reg 1) ac.1 → le (reg 1) y = true →
        lt y (powOf80 (reg 1) ac) = true

/-- `Ω₁` 以上でない元は §80.3 が片づける。 -/
private theorem k2Fst_of_big_aux80 {x : Term} (hi : inT x = true) (hl : lt x M = true)
    {ac : Term × Term} (hac : ac ∈ (wcnf (reg 1) (toList x)).1)
    {y : Term} (hy : y ∈ Kset (reg 1) ac.1)
    (Hbig : le (reg 1) y = true → lt y (ddOf75 (reg 1) ac) = true) :
    lt y (ddOf75 (reg 1) ac) = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hi
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList x) hc hd
    (ltM_toList x hi hl)
  obtain ⟨hi1, _, hi2, _⟩ := hallOK ac hac
  have hz := (wcnf_snd_ne_zero80 (toList x) hc ac hac).2
  have hyi : inT y = true := inT_mem_Kset75 ac.1 hi1 _ y hy
  by_cases hlt : lt y (reg 1) = true
  · exact lt_dd_of_lt_reg80 omegaNF_reg1_80 hi1 hi2 hz hy hlt
  · refine Hbig ?_
    rcases lt_comparable_inT hyi (inT_reg 1) with h | h | h
    · exact absurd h hlt
    · rw [h]; exact Evidence.WF.le_self _
    · show ((reg 1 == y) || lt (reg 1) y) = true
      rw [h]; exact Bool.or_true _

/-- **§80.4 の主定理。** `Ω₁` 以上の元だけ相手にすれば `aV` 側は出る。 -/
theorem localK2Fst_of_big80 (H : LocalK2Big_80) : LocalK2Fst_78 := fun a hb hs hi hl ac hac hle y hy =>
  k2Fst_of_big_aux80 hi hl hac hy (H a hb hs hi hl ac hac hle y hy)

/-- 逆も自明 — だから残余は `Ω₁` 以上の元についての条項と**同値**。 -/
theorem localK2Big_of_fst80 (H : LocalK2Fst_78) : LocalK2Big_80 :=
  fun a hb hs hi hl ac hac hle y hy _ => H a hb hs hi hl ac hac hle y hy

/-- **`aV` 側は `Ω₁` 以上の `K` の元についての条項と同値。** -/
theorem localK2Fst_iff_big80 : LocalK2Fst_78 ↔ LocalK2Big_80 :=
  ⟨localK2Big_of_fst80, localK2Fst_of_big80⟩

/-- 最小の残余からも `aV` 側は出る — 係数を落とした形。 -/
theorem localK2Fst_of_bigPow80 (H : LocalK2BigPow_80) : LocalK2Fst_78 := by
  intro a hb hs hi hl ac hac hle y hy
  refine k2Fst_of_big_aux80 hi hl hac hy (fun hge => ?_)
  obtain ⟨hc, hd⟩ := inT_toList (dict a) hi
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList (dict a)) hc hd
    (ltM_toList (dict a) hi hl)
  obtain ⟨hi1, _, hi2, _⟩ := hallOK ac hac
  have hz := (wcnf_snd_ne_zero80 (toList (dict a)) hc ac hac).2
  exact lt_of_lt_of_le3 (inT_le_fragR y (inT_mem_Kset75 ac.1 hi1 _ y hy))
    (inT_le_fragR _ (inT_powOf80 (inT_reg 1) hi1))
    (inT_le_fragR _ (inT_ddOf75 (inT_reg 1) hi1 hi2))
    (H a hb hs hi hl ac hac hle y hy hge)
    (le_powOf_ddOf80 (inT_reg 1) hi1 hi2 hz)

/-- 二つに割った残余から §78 の一条項。 -/
theorem localK2_of_big80 (H1 : LocalK2Big_80) (H2 : LocalK2Snd_78) : LocalK2_78 :=
  localK2_of_split78 (localK2Fst_of_big80 H1) H2

/-- 326 行目の証明書 — `K` の側で待つのは `Ω₁` 以上の元についての条項と、
    §78 が「破れない」と測った `cV` 側だけ。 -/
theorem certIn_t326_big80 (H1 : LocalK2Big_80) (H2 : LocalK2Snd_78) (HD : DictHeadLt77)
    (HCD : CofDenseS1) (HBC : BCofIn71) (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_k2_78 (localK2_of_big80 H1 H2) HD HCD HBC hacc

end

/-! ### §80.5 判定器 — 係数を見ない形 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 係数を見ない判定器 — `aV` 側だけ。 -/
def k2fb80 (u : Nat) (x : Term) : Bool :=
  (wcnf (reg (u+1)) (toList x)).1.all fun ac =>
    !(le (reg (u+1)) ac.1) ||
      ((Kset (reg (u+1)) ac.1).all fun y => lt y (powOf80 (reg (u+1)) ac))

/-- 一項ぶんの `aV` 側の条項。 -/
def LocalK2FstT_80 (u : Nat) (x : Term) : Prop :=
  ∀ ac ∈ (wcnf (reg (u+1)) (toList x)).1, le (reg (u+1)) ac.1 = true →
    ∀ y, y ∈ Kset (reg (u+1)) ac.1 → lt y (ddOf75 (reg (u+1)) ac) = true

/-- **判定器は証明。** 係数を見ない判定器から `aV` 側の条項が出る。 -/
theorem localK2FstT_of_b80 {u : Nat} {x : Term} (hx : inT x = true) (hlx : lt x M = true)
    (h : k2fb80 u x = true) : LocalK2FstT_80 u x := by
  intro ac hac hle y hy
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg (u+1)) (isSC_reg_succ u) (toList x) hc hd
    (ltM_toList x hx hlx)
  obtain ⟨hi1, _, hi2, _⟩ := hallOK ac hac
  have hz := (wcnf_snd_ne_zero80 (toList x) hc ac hac).2
  have hall := List.all_eq_true.mp h ac hac
  rw [hle, Bool.not_true, Bool.false_or] at hall
  exact lt_of_lt_of_le3 (inT_le_fragR y (inT_mem_Kset75 ac.1 hi1 _ y hy))
    (inT_le_fragR _ (inT_powOf80 (inT_reg (u+1)) hi1))
    (inT_le_fragR _ (inT_ddOf75 (inT_reg (u+1)) hi1 hi2))
    (List.all_eq_true.mp hall y hy)
    (le_powOf_ddOf80 (inT_reg (u+1)) hi1 hi2 hz)

/-- 凍結 (深さ) — §78.5 の `ψ` の入れ子 9 段の塔。`K_{Ω₁} aV` は空でない。 -/
theorem localK2FstT_wOK78 : LocalK2FstT_80 0 (dict wOK78) :=
  localK2FstT_of_b80 (by decide) (by decide) (by decide)

/-- 凍結 (幅) — §78.5 の二項和。 -/
theorem localK2FstT_wWide78 : LocalK2FstT_80 0 (dict wWide78) :=
  localK2FstT_of_b80 (by decide) (by decide) (by decide)

end

/-! ### §80.6 否定 — 残る条項は 𝔗(M) の項だけの事実ではない -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- `Ω₁ ⊕ ψ_{Ω₁}(Ω₂)` — 𝔗(M) の項で `Ω₁ ≤ ·`、`K_{Ω₁}` は `{Ω₂}`。 -/
def bad80 : Term := add (reg 1) (psi (reg 1) (reg 2))

/-- **§80.6 の主定理 — 残る条項は「対 `(aV, cV)`」だけからは出ない。**
    `bad80` は 𝔗(M) の項で `Ω₁ ≤ bad80` だが `K_{Ω₁} bad80 = {Ω₂}` で、`Ω₂` は
    `W^(bad80 ⊖ Ω₁)` にも `Δ` にも届かない。だから `LocalK2Big_80` の証明は
    どこかで `dict`・`BT.isStd` を使わねばならない。 -/
theorem not_pow80_bad80 :
    inT bad80 = true ∧ le (reg 1) bad80 = true ∧
    (Kset (reg 1) bad80 == [reg 2]) = true ∧
    lt (reg 2) (powOf80 (reg 1) (bad80, TM.Term.one)) = false ∧
    lt (reg 2) (ddOf75 (reg 1) (bad80, TM.Term.one)) = false :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

end


/-! ### §80.7 測定 (凍結)

**構成を先に書く。**  §78.5 の三つの母集団 — `pop78` (領域の中、129 個・102 歩)、
`bmp78` (`ψ₀` を `ψ₂`・`ψ₃` に差し替えた 217 個・217 歩)、`nst78` (段の上限は満たすが
標準でない 118 個・110 歩) — をそのまま使い、**§80 の問いに合わせて一群だけ足す**。

`tri80 n` は長さ `n` の `{0,1,2}` 列、`T80 n` はそこから作った塔 `ψ_{p₁}…ψ_{p_n}0`。

    H1  深さ  `T80 5` の塔ぜんぶ                       243 個  `ψ` の入れ子 5 段, 幅 1
    H2  幅 2   `ψ₂ψ₁(x ⊕ y)`,  x,y ∈ T80 3            729 個  入れ子 5 段, 幅 2
    H3  幅 3   `ψ₁(x ⊕ y ⊕ z)`,  x,y,z ∈ T80 2        729 個  入れ子 3 段, 幅 3
    ------------------------------------------------------------------------------
    hi80 = H1 ++ H2 ++ H3 のうち `ψ₀` をかぶせて標準なもの (重複を除く)
                                                       223 個, 発火 206 歩

**この群の狙いは段の上限を外すこと**で、`bmp78` と違って標準性は保つ。223 個のうち
`btLe72 1` を満たすのは 31 個だけ — 残り 192 個は `ψ₂` を内側に持つ。四群あわせて
**635 歩**、うち残余 (`Ω₁` 以上の `K` の元がある歩) は 177 歩。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 長さ `n` の `{0,1,2}` 列。 -/
def tri80 : Nat → List (List Nat)
  | 0 => [[]]
  | k+1 => (tri80 k).flatMap fun l => [0 :: l, 1 :: l, 2 :: l]

/-- `{0,1,2}` 列から作った塔。 -/
def T80 (n : Nat) : List BT := (tri80 n).map tw78

/-- **段の上限を外し、標準性は保つ群。** -/
def hi80 : List BT := ((T80 5 ++ (sums2_78 (T80 3)).map (fun s => BT.D 2 (BT.D 1 s))
  ++ (sums3_78 (T80 2)).map (fun s => BT.D 1 s)).filter std78).eraseDups
def hip80 : List (Term × Term) := hi80.flatMap fire78
def all80 : List (Term × Term) := allp78 ++ hip80

def k2fst80 (ac : Term × Term) : Bool := (Kset (reg 1) ac.1).all fun y => lt y (dd78 ac)
def k2pow80 (ac : Term × Term) : Bool :=
  (Kset (reg 1) ac.1).all fun y => lt y (powOf80 (reg 1) ac)
/-- 残余が語る元 — `Ω₁` 以上の `K` の元。 -/
def big80 (ac : Term × Term) : List Term := (Kset (reg 1) ac.1).filter fun y => le (reg 1) y

-- 母集団の大きさ。
#guard hi80.length == 223
#guard hip80.length == 206
#guard (hi80.filter (btLe72 1)).length == 31
#guard all80.length == 635

/-! **肯定 1 — 係数は落ちる。** `Δ` を `W^(aV ⊖ Ω₁)` に取り替えても、635 歩で判定は
一度も変わらない。§80.1 の定理が捨てているものは無い。 -/

#guard (all80.filter fun ac => k2fst80 ac != k2pow80 ac).length == 0

/-! **肯定 2 — `Ω₁` より下の `K` の元はただ (§80.3)。** 635 歩のうち 458 歩は
それだけで片づき、領域の中の 102 歩では 89 歩。残余が語るのは 177 歩、領域の中では
13 歩で、そこは空回りではない。 -/

#guard (all80.filter fun ac => (Kset (reg 1) ac.1).all fun y => lt y (reg 1)).length == 458
#guard ((pop78.flatMap fire78).filter fun ac =>
  (Kset (reg 1) ac.1).all fun y => lt y (reg 1)).length == 89
#guard (all80.filter fun ac => !((big80 ac).isEmpty)).length == 177
#guard ((pop78.flatMap fire78).filter fun ac => !((big80 ac).isEmpty)).length == 13

/-! **肯定 3 — `aV ⊖ Ω₁ = 0` の歩では `K` は両方とも空。** §80.3 の場合分けが
空回りでないこと、そして `cV` 側の仮説が矛盾しないことの両方。 -/

#guard (all80.filter fun ac => subAP (reg 1) ac.1 == zero).length == 11
#guard (all80.filter fun ac => subAP (reg 1) ac.1 == zero &&
  !((Kset (reg 1) ac.1 ++ Kset (reg 1) ac.2).isEmpty)).length == 0

/-! **否定 1 — 段の上限は (K2') を担いでいない。** 新しい群 223 個のうち 192 個は
`ψ₂` を内側に持ち `btLe72 1` を破るが、標準ではある。その 206 歩で (K2') も (K4) も
**一度も落ちない**。`K` は空回りしていない — `K_{Ω₁} aV` は 68 歩で、`K_{Ω₁} cV` は
4 歩で空でなく、68 歩のすべてに `Ω₁` 以上の元がある。 -/

#guard (hip80.filter fun ac => !(k2fst80 ac)).length == 0
#guard (hip80.filter fun ac => !(k4b78 ac)).length == 0
#guard (hip80.filter fun ac => !((Kset (reg 1) ac.1).isEmpty)).length == 68
#guard (hip80.filter fun ac => !((Kset (reg 1) ac.2).isEmpty)).length == 4
#guard (hip80.filter fun ac => !((big80 ac).isEmpty)).length == 68

/-! **否定 2 — `cV` 側の「`Ω₁` より下」は段の上限を外すと破れる。**
`LocalKSndBelow_80` は段の上限を満たす 443 歩で 0 回、`ψ₂` を許すと 3 歩で落ちる。
`cV` 側の条項そのもの (`K_{Ω₁} cV < Δ`) は 635 歩すべてで成り立つ。 -/

#guard (all80.filter fun ac => !((Kset (reg 1) ac.2).all fun y =>
  (subAP (reg 1) ac.1 != zero) && lt y (reg 1))).length == 3
#guard ((allp78 ++ (hi80.filter (btLe72 1)).flatMap fire78).filter fun ac =>
  !((Kset (reg 1) ac.2).all fun y =>
    (subAP (reg 1) ac.1 != zero) && lt y (reg 1))).length == 0
#guard ((allp78 ++ (hi80.filter (btLe72 1)).flatMap fire78)).length == 443
#guard (all80.filter fun ac => !((Kset (reg 1) ac.2).all fun y => lt y (dd78 ac))).length == 0

/-! **否定 3 — 残余をこれ以上鋭くはできない。** `Ω₁` 以上の元 `y` について
`y < ω^{Ω₁·(aV ⊖ Ω₁)}` は 635 歩で 87 回落ちる (領域の外だけ) が、`ω^·` を外した
`y < Ω₁·(aV ⊖ Ω₁)` は 127 回、§73.7 の `y < aV` も 127 回落ちる。**`ω^·` は要る。** -/

#guard (all80.filter fun ac => !((big80 ac).all fun y => lt y (powOf80 (reg 1) ac))).length == 87
#guard (all80.filter fun ac =>
  !((big80 ac).all fun y => lt y (mulL (reg 1) (subAP (reg 1) ac.1)))).length == 127
#guard (all80.filter fun ac => !((big80 ac).all fun y => lt y ac.1)).length == 127

/-! **否定 4 — §73.7 の (K2) は新しい母集団でも別の条項。** `K_{Ω₁} aV < aV` は
206 歩のうち 35 歩で落ち、(K2') は 0 歩。 -/

#guard (hip80.filter fun ac => !(KOK73 ac.1)).length == 35

end

/-! ### §80.8 公理 -/

/-! ## §81 THE VEBLEN FOLD: EVERYTHING BELOW `Ω₁` AND EVERYTHING CROSSING IT IS A THEOREM

§79 left ONE statement between row 326 and its certificate: `CollapseMono0_79`, the
`u = v = 0` half of the head comparison — `ψ₀` preserving the order of its argument's
image.  It is the last order lemma in the file and the oldest unproved claim in it.

**§81 does not close it.  §81 splits it at `Ω₁` and closes two of the three pieces.**  The
split is forced by `collapse` itself: `Trans/Dict.lean`'s clause (D1) gives `ψ₀(α) = ω^α`
only while every component of `α` is below `Ω₁` (§77.7's `collapse0_eq77`), and above that
the base-`Ω₁` CNF is read and the fold runs — `φ̄(a_i, ·)` per component plus the `ψ_{Z0}`
branch.  What is left after §81 is the case where the fold runs on BOTH sides.

WHAT IS PROVED.

  §81.1  **BOTH ARGUMENTS BELOW `Ω₁`.**  `collapse0_mono_ltW81`.  §77.7's closed form turns
         both sides into `ω^·` and §79.2's strict monotonicity finishes.  No fold runs.

  §81.2  **THE `ε₀` FAMILY.**  §79.5 built the `ltM_·` family a second time at `Ω₁`; §81.2
         builds it a third time at `ε₀ = φ̄(1,0)`, and it is much shorter, because the one
         branch §79.5 needed a page for — `ω^·` — is now §79.2's STRICT monotonicity plus
         `ω^ε₀ = ε₀` in one line (`ltE_omegaNF81`).  The `φ̄` comparisons are 2.3.13
         (`le_E81_phi`, `lt_phi0_E81`) where §79.5's were 2.3.5.

  §81.3  **THE FOLD'S ACCUMULATOR IS `≥ ε₀`.**  `StE81` / `stepE81` / `foldE81`, run along
         the same fold as §64.5's `StInv` and §79.6's `StW79`.  The strongly critical branch
         emits `ψ_{Ω₁}(·)`, which is above `ε₀` by 2.3.5; the Veblen branch emits
         `φ̄(a, ·)`, which is above `ε₀` by 2.3.13 **provided `a ≠ 0`** — and that is
         `wA_ne_zero81`: a component at or above `Ω₁` has `logOm` at or above `Ω₁` (§64's
         `lt_logOm_of_sc`), so the sieve that builds the exponent cannot come out empty.
         `le_self_plus_ap81` — `v ≤ v ⊕ y` for additively principal `v`, the left-hand twin
         of §75.1 — carries the bound past the CNF tail.

  §81.4  **THE CASE THAT CROSSES `Ω₁`.**  `lt_collapse0_cross81` : `x < ε₀` and `Ω₁ ≤ y`
         give `ψ₀(x) < ψ₀(y)`, from §81.3 and §79.2.

  §81.5  **WHAT THE `K`-CONDITION SAYS.**  `btLe0_of_lowHd81` : if the head component of `a`
         has subscript `0` and every element of `G(a,0)` is below `a`, then EVERY subscript
         in `a` is `0`.  The whole content is that `ψ_v(·)` with `v ≥ 1` is above every
         `ψ_0(·)` in `BT.lt`, so it can appear neither as an argument nor as a later
         summand.  This is the point where `BT.isStd (ψ₀ ·)` — the hypothesis §79 said the
         proof must consume — is actually consumed.

  §81.6  **THE TWO BOUNDS ON `dict`.**  `lt_dict_E81` : all-subscript-`0` standard terms
         land below `ε₀`.  `le_reg1_dict_of_not_lowHd81` : a head subscript of `1` puts the
         image at or above `Ω₁` (§79.7's `le_reg1_collapse1_79` at the head, §81.3's
         `le_self_plus_ap81` for the sum).

  §81.7  **THE ASSEMBLY.**  `collapseMono0_of_hi81 (Hp) (H : CollapseMono0Hi81) :
         CollapseMono0_79`, and through §79: `dictHeadLt81`, `dictLtA74_81`, `vOfLtA71_81`,
         `limDecS1_81`, `limIncS1_81`, `certIn_t326_81`.

WHAT IS **NOT** CLAIMED.  `CollapseMono0Hi81` — both sides at or above `Ω₁`, so the fold
runs twice and the two runs must be compared — is NOT proved and is stated as a named
hypothesis, not smuggled in.  Nothing here proves `PsiIdxOKStd172`, `CofDenseS1` or
`BCofIn71`; §81 changes nothing about those three.  §79.6's `lt_collapse0_W79` is a bound on
`ψ₀` and §81.1 is a monotonicity below `Ω₁`; neither implies the other.

WHAT THE MEASUREMENT SAYS (§81.8 gives the construction).  The population is §79's with the
`K`-condition of the statement imposed: 49 of §79's 55 terms, nesting 9 deep, 24 principal /
20 two-term sums / 5 three-term sums.

  * **The split is 36 / 360 / 780.**  Of the 1176 ordered pairs with `dict a < dict b`, 36
    have both sides below `Ω₁`, 360 cross `Ω₁`, 780 have both at or above it.  So §81 turns
    396 of the 1176 into theorems and leaves 780 to the fold.
  * **No inversion anywhere on the `K`-standard population**, in any of the three cases.
  * **The negative: the `K`-condition is load-bearing, and it is load-bearing exactly where
    §81 spends it.**  Drop `BT.isStd (ψ₀ ·)` from the same 55-term population and `ψ₀`
    inverts 66 pairs (§79's number).  **65 of the 66 are in the case that crosses `Ω₁`**,
    1 in the both-above case, and **0 in the both-below case** — which is why §81.1 needs no
    `K`-condition and §81.4 needs it twice over.
  * **And the ε₀ bound is exactly what breaks.**  On the 49 `K`-standard terms, `dict a < Ω₁`
    and "every subscript is 0" agree exactly (9 terms each, 0 disagreements) and every such
    image is below `ε₀`.  Drop the `K`-condition and 5 terms of the same population have
    `dict a < Ω₁` with `dict a ≥ ε₀`.  The smallest is `a = ψ₀ψ₁0` with `dict a = ε₀`, and
    it is the witness that `ψ₀` is not injective off the region: `ψ₀(ψ₀ψ₁0)` and `ψ₀(ψ₁0)`
    are the same term `ε₀` while `dict (ψ₀ψ₁0) < dict (ψ₁0)`.  `BT.isStd (ψ₀ψ₀ψ₁0) = false`
    is what keeps it out.
  * **The `ε₀ ≤ ψ₀(·)` half needs no `K`-condition at all** (§81.3): 0 failures on all
    three of the 55-, 67- and 109-term populations.  It is the `< ε₀` half that does.
  * **And the residual is not a statement about 𝔗(M) alone.**  The one both-above inversion
    is `x = ω^(Ω₁ ⊕ ζ₀) < y = ω^(Ω₁ ⊕ Ω₁)` with `ψ₀(x) = ψ₀(y) = ζ₀` — both `dict` of
    `BT.isStd` terms (`ψ₁ψ₀ψ₁ψ₁0` and `ψ₁ψ₁0`), and the only thing keeping it out of
    `CollapseMono0Hi81` is `BT.isStd (ψ₀ ψ₁ψ₀ψ₁ψ₁0) = false`.  So `Ω₁ ≤ x < y ⟹
    ψ₀(x) < ψ₀(y)` is FALSE, and whatever closes §81's residual has to spend the
    `K`-condition too — comparing the two folds will not be enough by itself.
-/

/-! ### §81.1 両辺が `Ω₁` の下 — 折り畳みは一度も回らない

`Trans/Dict.lean` の (D1) は `α` の成分がすべて `Ω₁` より下のときだけ `ψ₀(α) = ω^α`
と言う (§77.7 の `collapse0_eq77`)。その範囲では `collapse 0` の `wcnf` は何も分解せず
畳み込みは空で回るので、単調性は `ω^·` の狭義単調性 (§79.2) そのものになる。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- **§81.1 の主定理。** 両辺が `Ω₁` の下にあるときの `collapse 0` の狭義単調性。 -/
theorem collapse0_mono_ltW81 {x y : Term} (hx : inT x = true) (hy : inT y = true)
    (hlx : lt x (reg 1) = true) (hly : lt y (reg 1) = true) (h : lt x y = true) :
    lt (collapse 0 x) (collapse 0 y) = true := by
  rw [collapse0_eq77 x hx (fun p hp => ltW_toList79 x hx hlx p hp),
    collapse0_eq77 y hy (fun p hp => ltW_toList79 y hy hly p hp)]
  exact lt_omegaNF_inT79 hx hy h

end

/-! ### §81.2 ε₀ の一族 — `Ω₁` の一族 (§79.5) を一段下で走らせる

`Ω₁` をまたぐ側を閉じるには「`Ω₁` の下にある `dict` の像は ε₀ の下」と
「`Ω₁` 以上の引数に対する `ψ₀` の像は ε₀ 以上」の 2 本が要る。前半のために
§79.5 の `ltW_·` の一族を `ε₀ = φ̄(1,0)` で走らせる。違いは 2 か所しかない:
`ω^·` の枝は §79.2 の**狭義**単調性と `ω^ε₀ = ε₀` で一撃 (`ltE_omegaNF81`)、
そして `φ̄` との比較は 2.3.5 ではなく 2.3.13 になる。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- ε₀ = φ̄(1,0)。 -/
def E081 : Term := phi TM.Term.one zero

theorem inT_E81 : inT E081 = true := by
  show (inT TM.Term.one && inT zero && lt TM.Term.one M && lt zero M) = true
  rw [inT_one, inT_zero, lt_one_M, lt_zero_M]; rfl

theorem ltM_E81 : lt E081 M = true := lt_phi_M _ _

theorem lt_zero_E81 : lt zero E081 = true :=
  lt_zero_left (by intro hc; exact Term.noConfusion hc)

theorem lt_zero_one81 : lt zero TM.Term.one = true :=
  lt_zero_left (by intro hc; exact Term.noConfusion hc)

/-- **ε₀ は強臨界項より下** (2.3.5 と 2.3.2)。SC = {M} ∪ {ψκα} ∪ {Zα} のどれでも。 -/
theorem lt_E81_sc {v : Term} (h : v.isSC = true) : lt E081 v = true := by
  cases v with
  | zero => exact Bool.noConfusion h
  | add _ _ => exact Bool.noConfusion h
  | omg _ => exact Bool.noConfusion h
  | phi _ _ => exact Bool.noConfusion h
  | M => exact lt_phi_M _ _
  | psi k c =>
      have hz : lt zero (psi k c) = true := lt_zero_left (by intro hc; exact Term.noConfusion hc)
      exact lt_phi_psi_of (lt_phi_psi_of hz hz) hz
  | Z d =>
      have hz : lt zero (Z d) = true := lt_zero_left (by intro hc; exact Term.noConfusion hc)
      exact lt_phi_Z_of (lt_phi_Z_of hz hz) hz

/-- **`φ̄(c,d)` は `c ≠ 0` なら ε₀ 以上** (2.3.13)。 -/
theorem le_E81_phi {c d : Term} (hic : inT c = true) (hz : c ≠ zero) :
    le E081 (phi c d) = true := by
  have h1 : le TM.Term.one c = true := le_one_inT hic hz
  show le (phi TM.Term.one zero) (phi c d) = true
  rcases (Bool.or_eq_true _ _).mp h1 with he | hl
  · have hce : c = TM.Term.one := (eq_of_beq he).symm
    subst hce
    by_cases hd : d = zero
    · subst hd; exact Evidence.WF.le_self _
    · refine le_of_lt ?_
      rw [lt_phi_phi (by intro hc; injection hc with _ h2; exact hd h2.symm), if_pos rfl]
      exact lt_zero_left hd
  · have hne : c ≠ TM.Term.one := by
      intro hc; rw [hc] at hl; rw [lt_irrefl] at hl; exact Bool.noConfusion hl
    refine le_of_lt ?_
    rw [lt_phi_phi (by intro hc; injection hc with h2 _; exact hne h2.symm),
      if_neg (fun hc => hne hc.symm), if_pos hl]
    exact lt_zero_left (by intro hc; exact Term.noConfusion hc)

/-- 2.3.13(i) の 1 本。 -/
theorem lt_phi0_E81 (t : Term) : lt (phi zero t) E081 = lt t E081 := by
  show lt (phi zero t) (phi TM.Term.one zero) = lt t (phi TM.Term.one zero)
  rw [lt_phi_phi (by intro hc; injection hc with h1 _; exact Term.noConfusion h1),
    if_neg (by intro hc; exact Term.noConfusion hc), if_pos lt_zero_one81]

theorem lt_phi0_E81' {t : Term} (h : lt t E081 = true) : lt (phi zero t) E081 = true := by
  rw [lt_phi0_E81]; exact h

theorem lt_add_E81 (a b : Term) : lt (add a b) E081 = lt a E081 :=
  lt_add_nsum (by intro hc; exact Term.noConfusion hc) rfl

theorem lt_one_E81 : lt TM.Term.one E081 = true := lt_phi0_E81' lt_zero_E81

theorem lt_ofList_E81 : ∀ (l : List Term), (∀ x ∈ l, lt x E081 = true) →
    lt (ofList l) E081 = true
  | [], _ => lt_zero_E81
  | [a], h => h a (List.Mem.head _)
  | a :: b :: t, h => by
    show lt (add a (ofList (b :: t))) E081 = true
    rw [lt_add_E81]
    exact h a (List.Mem.head _)

theorem ltE_of_le81 {y a : Term} (hy : inT y = true) (ha : inT a = true)
    (hle : le y a = true) (hla : lt a E081 = true) : lt y E081 = true :=
  lt_of_le_of_lt3 (inT_le_fragR y hy) (inT_le_fragR a ha) (inT_le_fragR _ inT_E81) hle hla

theorem ltE_of_hdLe81 : ∀ {a b : Term}, inT a = true → inT b = true →
    hdLe b a = true → lt a E081 = true → lt b E081 = true := by
  intro a b hia hib hhd hla
  cases b with
  | zero => exact Bool.noConfusion hhd
  | M => exact ltE_of_le81 hib hia hhd hla
  | omg c => exact ltE_of_le81 hib hia hhd hla
  | phi c d => exact ltE_of_le81 hib hia hhd hla
  | psi c d => exact ltE_of_le81 hib hia hhd hla
  | Z c => exact ltE_of_le81 hib hia hhd hla
  | add c d =>
    obtain ⟨_, hic, _, _⟩ := inT_add hib
    rw [lt_add_E81]
    exact ltE_of_le81 hic hia hhd hla

theorem ltE_toList81 : ∀ (s : Term), inT s = true → lt s E081 = true →
    ∀ x ∈ toList s, lt x E081 = true := by
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
    have hla : lt a E081 = true := by rw [← lt_add_E81 a b]; exact hl
    have hlb : lt b E081 = true := ltE_of_hdLe81 hia hib hhd hla
    rcases List.mem_cons.mp (show x ∈ a :: toList b from hx) with h1 | h1
    · rw [h1]; exact hla
    · exact ihb hib hlb x h1

theorem lt_plus_E81 {s t : Term} (hs : inT s = true) (ht : inT t = true)
    (hls : lt s E081 = true) (hlt : lt t E081 = true) :
    lt (plus s t) E081 = true := by
  cases hl : toList t with
  | nil => rw [show plus s t = s from by unfold TM.Term.plus; rw [hl]]; exact hls
  | cons b1 rest =>
    rw [plus_eq (s := s) hl]
    refine lt_ofList_E81 _ ?_
    intro x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact ltE_toList81 s hs hls x (List.mem_filter.mp h1).1
    · exact ltE_toList81 t ht hlt x h1

/-- `ω^ε₀ = ε₀`。 -/
theorem isFP_E81 : TM.Term.isFP zero E081 = true := by
  show ((E081.isSC && lt zero E081) || lt zero TM.Term.one) = true
  rw [lt_zero_one81]; exact Bool.or_true _

theorem omegaNF_E81 : omegaNF E081 = E081 := by
  rw [omegaNF_eq_gen,
    if_neg (by rw [lt_asymm_inT inT_E81 inT_M ltM_E81]; exact Bool.noConfusion),
    if_pos isFP_E81]

/-- **ε₀ は ε 数。** §79.2 の狭義単調性を ε₀ に当てるだけ。 -/
theorem ltE_omegaNF81 {x : Term} (hx : inT x = true) (hlx : lt x E081 = true) :
    lt (omegaNF x) E081 = true := by
  have h := lt_omegaNF_inT79 hx inT_E81 hlx
  rw [omegaNF_E81] at h
  exact h

/-- ε₀ は `Ω₁` の下 (2.3.5)。 -/
theorem lt_E81_W81 : lt E081 (reg 1) = true := lt_phi_W79 lt_one_W79 lt_zero_W79

theorem ltW_of_ltE81 {x : Term} (hx : inT x = true) (h : lt x E081 = true) :
    lt x (reg 1) = true := lt_trans_inT hx inT_E81 inT_W79 h lt_E81_W81

end

/-! ### §81.3 折り畳みの下界 — `Ω₁` 以上の引数では `ψ₀` の像は ε₀ 以上

`Ω₁ ≤ x` なら `wcnf` の底 `Ω₁` の分解は空でなく、畳み込みは必ず 1 歩は回る。
その 1 歩が吐くのは強臨界枝なら `ψ_{Ω₁}(·)` (ε₀ より上)、ヴェブレン枝なら
`φ̄(a, ·)` で、指数 `a` は 0 ではない (`wA_ne_zero81`) から φ̄(1,0) = ε₀ 以上。
`StE81` はそれを畳み込みに沿って運ぶ。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open Trans.Dict (sub1 subAP logOm divAP mulL)
open TM TM.Term
open Evidence.WF

theorem toList_isAP81 {v : Term} (h : v.isAP = true) : toList v = [v] := by
  cases v <;> first | exact Bool.noConfusion h | rfl

/-- **左の引数も和以下** — 左が加法主要なとき。§79.7 の `le_reg1_plus79` の一般形。 -/
theorem le_self_plus_ap81 {v y : Term} (hv : inT v = true) (hap : v.isAP = true)
    (hy : inT y = true) : le v (plus v y) = true := by
  cases hY : toList y with
  | nil => rw [plus_nil hY]; exact Evidence.WF.le_self _
  | cons y1 Y' =>
    have hiy1 : inT y1 = true := inTL_inT hy y1 (by rw [hY]; exact List.Mem.head _)
    rw [plus_cons hv hy (toList_isAP81 hap) rfl hY]
    by_cases hle : le y1 v = true
    · rw [if_pos hle]
      exact le_of_lt (lt_head_add hap _)
    · rw [if_neg hle]
      refine le_of_lt (lt_of_lt_of_le3 (inT_le_fragR _ hv) (inT_le_fragR y1 hiy1)
        (inT_le_fragR y hy) ?_ (le_hd_self_inT hy hY))
      exact lt_of_not_le_inT hiy1 hv (bool_false hle)

theorem ofList_ne_zero81 : ∀ (l : List Term), l ≠ [] → (∀ x ∈ l, x.isAP = true) →
    ofList l ≠ zero
  | [], h, _ => absurd rfl h
  | [a], _, hA => by
      show a ≠ zero
      intro hc
      have h2 := hA a (List.Mem.head _)
      rw [hc] at h2
      exact Bool.noConfusion h2
  | _ :: _ :: _, _, _ => by intro hc; exact Term.noConfusion hc

/-- **`wcnf` の指数は 0 でない。** 成分が `Ω₁` 以上なら `logOm` も `Ω₁` 以上
    (§64 の `lt_logOm_of_sc`) なので、`Ω₁` 以上の部分を拾うふるいが空にならない。 -/
theorem wA_ne_zero81 {p : Term} (hap : p.isAP = true) (hp : inT p = true)
    (h : lt p (reg 1) = false) : wA (reg 1) p ≠ zero := by
  have hlog : lt (logOm p) (reg 1) = false :=
    lt_logOm_of_sc (show (reg 1).isSC = true from rfl) inT_W79 hap hp h
  have hne : ((toList (logOm p)).filter (fun q => !lt q (reg 1))) ≠ [] := by
    intro hnil
    have hall : ∀ q ∈ toList (logOm p), lt q (reg 1) = true := by
      intro q hq
      cases hlq : lt q (reg 1) with
      | true => rfl
      | false =>
        exfalso
        have hm : q ∈ (toList (logOm p)).filter (fun q => !lt q (reg 1)) :=
          List.mem_filter.mpr ⟨hq, by rw [hlq]; rfl⟩
        rw [hnil] at hm; cases hm
    have h2 := lt_ofList_W79 (toList (logOm p)) hall
    rw [inT_ofList_toList _ (inT_logOm hp)] at h2
    rw [h2] at hlog
    exact Bool.noConfusion hlog
  refine ofList_ne_zero81 _ ?_ (fun x hx => by
    obtain ⟨q, _, hxe⟩ := List.mem_map.mp hx
    rw [← hxe]; exact isAP_divAP _ _)
  intro hc
  exact hne (List.map_eq_nil_iff.mp hc)

theorem le_E81_phiNFdefault81 {a b : Term} (hia : inT a = true) (hza : a ≠ zero) :
    le E081 (phiNFdefault a b) = true := by
  unfold phiNFdefault
  split
  · rename_i h
    exact le_of_lt (lt_E81_sc ((Bool.and_eq_true _ _).mp h).2)
  · exact le_E81_phi hia hza

theorem le_E81_phiNFsucc81 {a b : Term} (hia : inT a = true) (hza : a ≠ zero) :
    le E081 (phiNFsucc a b) = true := by
  have hdef := le_E81_phiNFdefault81 (a := a) (b := b) hia hza
  unfold phiNFsucc
  split
  split
  · split <;> (split <;> first | exact le_E81_phi hia hza | exact hdef)
  · exact hdef

/-- **ヴェブレン枝の出力は ε₀ 以上** — 指数が 0 でなければ。 -/
theorem le_E81_phiNF81 {a b : Term} (hia : inT a = true) (hza : a ≠ zero)
    (hib : inT b = true) : le E081 (phiNF a b) = true := by
  unfold phiNF
  split
  · rename_i h
    exact le_of_lt (lt_E81_sc ((Bool.and_eq_true _ _).mp h).1)
  · cases b with
    | zero => exact le_E81_phiNFsucc81 hia hza
    | M => exact le_E81_phiNFsucc81 hia hza
    | add _ _ => exact le_E81_phiNFsucc81 hia hza
    | omg _ => exact le_E81_phiNFsucc81 hia hza
    | psi _ _ => exact le_E81_phiNFsucc81 hia hza
    | Z _ => exact le_E81_phiNFsucc81 hia hza
    | phi c d =>
        show le E081 (if lt a c = true then phi c d else phiNFsucc a (phi c d)) = true
        by_cases hlt : lt a c = true
        · rw [if_pos hlt]
          refine le_E81_phi (inT_phi4 hib).1 ?_
          intro hc; rw [hc, lt_zero_right] at hlt; exact Bool.noConfusion hlt
        · rw [if_neg hlt]; exact le_E81_phiNFsucc81 hia hza

/-- `wcnf` の指数がどれも 0 でないこと。 -/
def PairNZ81 (r : List (Term × Term) × Term) : Prop := ∀ ac ∈ r.1, ac.1 ≠ zero

theorem wcnf_NZ81 : ∀ (L : List Term), inTL L = true → PairNZ81 (wcnf (reg 1) L) := by
  intro L
  induction L with
  | nil => intro _ ac hac; cases hac
  | cons p rest ih =>
    intro hc
    obtain ⟨⟨hap, hip⟩, hcr⟩ := inTL_cons.mp hc
    have IH := ih hcr
    by_cases hlp : lt p (reg 1) = true
    · rw [wcnf_cons_lt hlp]; intro ac hac; cases hac
    · have hlp' : lt p (reg 1) = false := bool_false hlp
      have hNZ := wA_ne_zero81 hap hip hlp'
      rw [wcnf_cons_ge hlp']
      cases hr : wcnf (reg 1) rest with
      | mk fst snd =>
        rw [hr] at IH
        cases fst with
        | nil => intro ac hac; rw [List.mem_singleton.mp hac]; exact hNZ
        | cons ac0 ps =>
          cases ac0 with
          | mk a' c' =>
            show PairNZ81 (if (wA (reg 1) p == a') = true
              then ((wA (reg 1) p, plus (wC (reg 1) p) c') :: ps, snd)
              else ((wA (reg 1) p, wC (reg 1) p) :: (a', c') :: ps, snd))
            by_cases heq : (wA (reg 1) p == a') = true
            · rw [if_pos heq]
              intro ac hac
              rcases List.mem_cons.mp hac with h | h
              · rw [h]; exact hNZ
              · exact IH ac (List.Mem.tail _ h)
            · rw [if_neg heq]
              intro ac hac
              rcases List.mem_cons.mp hac with h | h
              · rw [h]; exact hNZ
              · exact IH ac h

/-- 畳み込みの不変量、ε₀ の側。累算器は加法主要で ε₀ 以上。 -/
def StE81 (s : Option Term × Option Term) : Prop :=
  ∀ v, s.2 = some v →
    inT v = true ∧ lt v (reg 1) = true ∧ v.isAP = true ∧ le E081 v = true

theorem stepE81 {s : Option Term × Option Term} {ac : Term × Term}
    (hs : StE81 s) (h1 : inT ac.1 = true) (h2 : lt ac.1 M = true)
    (h3 : inT ac.2 = true) (h3w : lt ac.2 (reg 1) = true) (hz : ac.1 ≠ zero)
    (hpsi : le (reg 1) ac.1 = true → inT (psi (reg 1) (idxOf (reg 1) s ac)) = true) :
    StE81 (stepF (reg 1) (baseOf 0) s ac) := by
  unfold stepF
  split
  · rename_i hle
    intro v hq
    rw [← Option.some.inj (show some (psi (reg 1) (idxOf (reg 1) s ac)) = some v from hq)]
    exact ⟨hpsi hle, lt_psi_W79 _, rfl, le_of_lt (lt_E81_sc rfl)⟩
  · rename_i hle
    intro v hq
    have hbse : inT (match s.2 with | none => baseOf 0 | some v => v) = true ∧
        lt (match s.2 with | none => baseOf 0 | some v => v) (reg 1) = true := by
      cases hq2 : s.2 with
      | none => exact ⟨inT_baseOf 0, show lt (baseOf 0) (reg 1) = true from lt_zero_W79⟩
      | some v0 => exact ⟨(hs v0 hq2).1, (hs v0 hq2).2.1⟩
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
           ltW_phiNF79 (inT_plus hbse.1 hcc.1) hA hP,
           isAP_phiNF _ _,
           le_E81_phiNF81 h1 hz (inT_plus hbse.1 hcc.1)⟩

theorem foldE81 : ∀ (l : List (Term × Term)) (s : Option Term × Option Term), StE81 s →
    (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
    (∀ ac ∈ l, lt ac.2 (reg 1) = true) → (∀ ac ∈ l, ac.1 ≠ zero) →
    (∀ p ∈ scanSt (reg 1) (baseOf 0) s l, le (reg 1) p.2.1 = true →
        inT (psi (reg 1) (idxOf (reg 1) p.1 p.2)) = true) →
    StE81 (l.foldl (stepF (reg 1) (baseOf 0)) s) := by
  intro l
  induction l with
  | nil => intro s hs _ _ _ _; exact hs
  | cons ac t ih =>
    intro s hs hall hallw hallz hpsi
    have hstep : StE81 (stepF (reg 1) (baseOf 0) s ac) :=
      stepE81 hs (hall ac (List.Mem.head _)).1 (hall ac (List.Mem.head _)).2.1
        (hall ac (List.Mem.head _)).2.2.1 (hallw ac (List.Mem.head _))
        (hallz ac (List.Mem.head _)) (hpsi (s, ac) (List.Mem.head _))
    exact ih (stepF (reg 1) (baseOf 0) s ac) hstep
      (fun a ha => hall a (List.Mem.tail _ ha))
      (fun a ha => hallw a (List.Mem.tail _ ha))
      (fun a ha => hallz a (List.Mem.tail _ ha))
      (fun p hp => hpsi p (List.Mem.tail _ hp))

theorem stepF_some81 (w base : Term) (s : Option Term × Option Term) (ac : Term × Term) :
    (stepF w base s ac).2 ≠ none := by
  unfold stepF; split <;> exact Option.some_ne_none _

theorem fold_keeps_some81 : ∀ (l : List (Term × Term)) (s : Option Term × Option Term),
    s.2 ≠ none → (l.foldl (stepF (reg 1) (baseOf 0)) s).2 ≠ none
  | [], _, h => h
  | ac :: t, s, _ => fold_keeps_some81 t _ (stepF_some81 _ _ s ac)

theorem fold_some81 : ∀ (l : List (Term × Term)) (s : Option Term × Option Term),
    l ≠ [] → (l.foldl (stepF (reg 1) (baseOf 0)) s).2 ≠ none
  | [], _, h => absurd rfl h
  | ac :: t, s, _ => fold_keeps_some81 t _ (stepF_some81 _ _ s ac)

/-- `Ω₁ ≤ x` なら底 `Ω₁` の分解は空でない。 -/
theorem wcnf_fst_ne_nil81 {y : Term} (hy : inT y = true) (hW : le (reg 1) y = true) :
    (wcnf (reg 1) (toList y)).1 ≠ [] := by
  cases hY : toList y with
  | nil =>
    exfalso
    rw [toList_eq_nil y hY,
      show le (reg 1) zero = false from by
        show ((reg 1 == zero) || lt (reg 1) zero) = false
        rw [lt_zero_right]; rfl] at hW
    exact Bool.noConfusion hW
  | cons p rest =>
    have hlp : lt p (reg 1) = false := by
      cases hc : lt p (reg 1) with
      | false => rfl
      | true =>
        exfalso
        have h2 : lt y (reg 1) = true := by
          have h3 := lt_ofList_cons_W79 p rest hc
          rw [← hY, inT_ofList_toList y hy] at h3
          exact h3
        have hne : ((reg 1 : Term) == y) = false := by
          cases hb : ((reg 1 : Term) == y) with
          | false => rfl
          | true => rw [← eq_of_beq hb, lt_irrefl] at h2; exact Bool.noConfusion h2
        have h4 : le (reg 1) y = false := by
          show ((reg 1 == y) || lt (reg 1) y) = false
          rw [hne, lt_asymm_inT hy inT_W79 h2]; rfl
        rw [h4] at hW
        exact Bool.noConfusion hW
    rw [wcnf_cons_ge hlp]
    cases hr : wcnf (reg 1) rest with
    | mk fst snd =>
      cases fst with
      | nil => exact List.cons_ne_nil _ _
      | cons ac0 ps =>
        cases ac0 with
        | mk a' c' =>
          show (if (wA (reg 1) p == a') = true
            then ((wA (reg 1) p, plus (wC (reg 1) p) c') :: ps, snd)
            else ((wA (reg 1) p, wC (reg 1) p) :: (a', c') :: ps, snd)).1 ≠ []
          split <;> exact List.cons_ne_nil _ _

end

/-! ### §81.4 `Ω₁` をまたぐ側 — `ω^x < ε₀ ≤ ψ₀(y)`

`Ω₁ ≤ y` のとき `ψ₀(y) = ω^(V ⊕ ρ)` で、`V` は畳み込みの累算器 (§81.3 で ε₀ 以上)、
`ρ` は底 `Ω₁` の分解の尾。`V` は加法主要だから `V ≤ V ⊕ ρ` (§81.3 の
`le_self_plus_ap81`) で、`x < ε₀ ≤ V ≤ V ⊕ ρ`。あとは §79.2 の狭義単調性。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- **§81.4 の主定理。** 引数が ε₀ より下と `Ω₁` 以上に分かれていれば `ψ₀` は順序を保つ。 -/
theorem lt_collapse0_cross81 {x y : Term} (hx : inT x = true) (hlx : lt x E081 = true)
    (hy : inT y = true) (hly : lt y M = true) (Hp : PsiIdxOK 0 y)
    (hW : le (reg 1) y = true) : lt (collapse 0 x) (collapse 0 y) = true := by
  obtain ⟨hc, hd⟩ := inT_toList y hy
  obtain ⟨⟨h21, h22⟩, hallOK⟩ :=
    wcnf_spec_sc (inT_reg 1) (show (reg 1).isSC = true from rfl) (toList y) hc hd
      (ltM_toList y hy hly)
  have hWp := wcnf_W79 (toList y) hc
  have hNZ := wcnf_NZ81 (toList y) hc
  have hinit : StE81 ((none : Option Term), (none : Option Term)) := by intro v h; cases h
  have hst := foldE81 (wcnf (reg 1) (toList y)).1 (none, none) hinit hallOK
    (fun ac hac => (hWp.2 ac hac).2) hNZ Hp
  have hsome := fold_some81 (wcnf (reg 1) (toList y)).1 (none, none)
    (wcnf_fst_ne_nil81 hy hW)
  have hv : ∃ v, inT v = true ∧ v.isAP = true ∧ le E081 v = true ∧
      (((wcnf (reg 1) (toList y)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero) = v := by
    cases hg : ((wcnf (reg 1) (toList y)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2 with
    | none => exact absurd hg hsome
    | some v =>
        exact ⟨v, (hst v hg).1, (hst v hg).2.2.1, (hst v hg).2.2.2, rfl⟩
  obtain ⟨v, hiv, hapv, hlev, hgd⟩ := hv
  have hip : inT (plus v (wcnf (reg 1) (toList y)).2) = true := inT_plus hiv h21
  have hle1 : le E081 (plus v (wcnf (reg 1) (toList y)).2) = true :=
    le_trans_inT inT_E81 hiv hip hlev (le_self_plus_ap81 hiv hapv h21)
  have hlt1 : lt x (plus v (wcnf (reg 1) (toList y)).2) = true :=
    lt_of_lt_of_le3 (inT_le_fragR x hx) (inT_le_fragR _ inT_E81) (inT_le_fragR _ hip) hlx hle1
  rw [collapse0_eq77 x hx (fun p hp => ltW_toList79 x hx (ltW_of_ltE81 hx hlx) p hp)]
  show lt (omegaNF x) (omegaNF (plus (reg 0) (plus
      (((wcnf (reg 1) (toList y)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero)
      (wcnf (reg 1) (toList y)).2))) = true
  rw [hgd, show plus (reg 0) (plus v (wcnf (reg 1) (toList y)).2)
        = plus v (wcnf (reg 1) (toList y)).2 from plus_zero_left_inT hip]
  exact lt_omegaNF_inT79 hx hip hlt1

end

/-! ### §81.5 `K` の条件が言っていること — 先頭の添字が 0 なら添字はすべて 0

`BT.isStd (ψ₀ a)` は `G(a,0)` — `a` の中のすべての引数 — が `a` より下であることを
要求する。`a` の先頭成分の添字が 0 なら、添字 1 以上の項はどれも `a` より上だから、
引数にも成分にも現れられない。**これが `K` の条件の全部で、これが無いと ε₀ の下界が
破れる** (§81.8 の否定 1)。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- 成分列の先頭の添字が 0 か。 -/
def lowHdL81 : List BT → Bool
  | [] => true
  | (BT.D u _) :: _ => u == 0
  | _ => false

/-- 項の先頭成分の添字が 0 か。 -/
def lowHd81 (a : BT) : Bool := lowHdL81 a.toL

theorem toL_isP81 {c : BT} (h : BT.isP c = true) : BT.toL c = [c] := by
  cases c <;> first | exact Bool.noConfusion h | rfl

theorem lowHdL_append81 : ∀ (l1 l2 : List BT), lowHdL81 (l1 ++ l2) = true →
    lowHdL81 l1 = true
  | [], _, _ => rfl
  | p :: _, _, h => by cases p <;> exact h

theorem lowHdL_append_of81 : ∀ (l1 l2 : List BT), l1 ≠ [] → lowHdL81 l1 = true →
    lowHdL81 (l1 ++ l2) = true
  | [], _, h, _ => absurd rfl h
  | p :: _, _, _, h => by cases p <;> exact h

theorem lowHd_sum81 {x y : BT} (h : BT.isP x = true) :
    lowHd81 (BT.sum x y) = lowHd81 x := by
  cases x with
  | zero => exact Bool.noConfusion h
  | sum _ _ => exact Bool.noConfusion h
  | D u z => rfl

/-- **小さいほうの先頭も 0。** `ltL` は先頭の添字が違えば添字だけで決まる。 -/
theorem lowHdL_of_ltL81 : ∀ (f : Nat) (l1 l2 : List BT), BT.ltL f l1 l2 = true →
    lowHdL81 l2 = true → lowHdL81 l1 = true := by
  intro f
  cases f with
  | zero => intro l1 l2 h _; exact Bool.noConfusion h
  | succ g =>
    intro l1 l2 h h2
    cases l1 with
    | nil => rfl
    | cons p ps =>
      cases l2 with
      | nil => exact Bool.noConfusion h
      | cons q qs =>
        cases q with
        | zero => cases p <;> exact Bool.noConfusion h
        | sum _ _ => cases p <;> exact Bool.noConfusion h
        | D w y =>
          have hw : w = 0 := by
            cases w with
            | zero => rfl
            | succ k => exact Bool.noConfusion (show (false : Bool) = true from h2)
          subst hw
          cases p with
          | zero => exact Bool.noConfusion h
          | sum _ _ => exact Bool.noConfusion h
          | D u x =>
            show (u == 0) = true
            by_cases hu : u = 0
            · rw [hu]; rfl
            · exfalso
              rw [show BT.ltL (g+1) (BT.D u x :: ps) (BT.D 0 y :: qs)
                  = (if u < 0 then true else if 0 < u then false
                     else if x == y then BT.ltL g ps qs else BT.ltL g (BT.toL x) (BT.toL y))
                  from rfl,
                if_neg (Nat.not_lt_zero u), if_pos (Nat.pos_of_ne_zero hu)] at h
              exact Bool.noConfusion h

theorem lowHd_of_btLt81 {e a : BT} (h : BT.lt e a = true) (ha : lowHd81 a = true) :
    lowHd81 e = true := lowHdL_of_ltL81 _ _ _ h ha

theorem lowHd_of_btLe81 {e a : BT} (h : BT.le e a = true) (ha : lowHd81 a = true) :
    lowHd81 e = true := by
  rcases (Bool.or_eq_true _ _).mp h with he | hl
  · rw [bt_beq_eq77 he]; exact ha
  · exact lowHd_of_btLt81 hl ha

theorem isP_of_isStd_sum81 : ∀ {x y : BT}, BT.isStd (BT.sum x y) = true → BT.isP x = true := by
  intro x y h
  cases y <;> exact ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp
    ((Bool.and_eq_true _ _).mp h).1).1).1

/-- 和の残りの先頭も 0 — 成分が降順だから。 -/
theorem lowHd_tail81 : ∀ {x y : BT}, BT.isStd (BT.sum x y) = true → lowHd81 x = true →
    lowHd81 y = true := by
  intro x y hs hlx
  cases y with
  | zero => rfl
  | D v z =>
      have h4 : (BT.isP (BT.D v z) && BT.le (BT.D v z) x) = true :=
        ((Bool.and_eq_true _ _).mp hs).2
      exact lowHd_of_btLe81 ((Bool.and_eq_true _ _).mp h4).2 hlx
  | sum c d =>
      have h4 : BT.le c x = true := ((Bool.and_eq_true _ _).mp hs).2
      have hpc : BT.isP c = true := isP_of_isStd_sum81
        ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hs).1).2
      rw [lowHd_sum81 (y := d) hpc]
      exact lowHd_of_btLe81 h4 hlx

/-- **§81.5 の主定理。** 先頭の添字が 0 で `G(·,0)` がすべて先頭より下なら添字はすべて 0。 -/
theorem btLe0_of_lowHd81 : ∀ (a : BT), btLe72 1 a = true → BT.isStd a = true →
    lowHd81 a = true → (∀ e ∈ BT.GB 0 a, lowHd81 e = true) → btLe72 0 a = true
  | .zero, _, _, _, _ => rfl
  | .D u c, hb, hs, hl, hg => by
      have hu : u = 0 := by
        cases u with
        | zero => rfl
        | succ k => exact Bool.noConfusion (show (false : Bool) = true from hl)
      subst hu
      have hmem : ∀ e, e ∈ BT.GB 0 c → e ∈ BT.GB 0 (BT.D 0 c) := by
        intro e he
        show e ∈ c :: BT.GB 0 c
        exact List.Mem.tail _ he
      have hlc : lowHd81 c = true :=
        hg c (show c ∈ c :: BT.GB 0 c from List.Mem.head _)
      have hbc := (btLe72_D 1 0 c hb).2
      show (decide (0 ≤ 0) && btLe72 0 c) = true
      rw [btLe0_of_lowHd81 c hbc (isStd_of_D hs) hlc (fun e he => hg e (hmem e he))]
      rfl
  | .sum x y, hb, hs, hl, hg => by
      obtain ⟨hbx, hby⟩ := btLe72_sum 1 x y hb
      obtain ⟨hsx, hsy⟩ := isStd_of_sum hs
      have hpx : BT.isP x = true := isP_of_isStd_sum81 hs
      have hlx : lowHd81 x = true := by rw [← lowHd_sum81 (y := y) hpx]; exact hl
      have hly : lowHd81 y = true := lowHd_tail81 hs hlx
      have hgx : ∀ e ∈ BT.GB 0 x, lowHd81 e = true := by
        intro e he
        exact hg e (show e ∈ BT.GB 0 x ++ BT.GB 0 y from List.mem_append.mpr (Or.inl he))
      have hgy : ∀ e ∈ BT.GB 0 y, lowHd81 e = true := by
        intro e he
        exact hg e (show e ∈ BT.GB 0 x ++ BT.GB 0 y from List.mem_append.mpr (Or.inr he))
      show (btLe72 0 x && btLe72 0 y) = true
      rw [btLe0_of_lowHd81 x hbx hsx hlx hgx, btLe0_of_lowHd81 y hby hsy hly hgy]
      rfl

/-- `K` の条件から `G(a,0)` の元はすべて先頭の添字が 0。 -/
theorem lowHd_GB_of_std81 {a : BT} (hs : BT.isStd (BT.D 0 a) = true)
    (hl : lowHd81 a = true) : ∀ e ∈ BT.GB 0 a, lowHd81 e = true := by
  intro e he
  have hh : (BT.isStd a && (BT.GB 0 a).all (fun z => BT.lt z a)) = true := hs
  have h2 := List.all_eq_true.mp ((Bool.and_eq_true _ _).mp hh).2 e he
  exact lowHd_of_btLt81 h2 hl

end

/-! ### §81.6 `dict` の側 — ε₀ の下界と `Ω₁` の下界

添字がすべて 0 の標準項の像は ε₀ より下 (`lt_dict_E81`)、先頭の添字が 1 の標準項の
像は `Ω₁` 以上 (`le_reg1_dict_of_not_lowHd81`)。§81.5 とつなぐと `dict a < Ω₁` の側は
まるごと ε₀ の下に入り、§81.4 が使える形になる。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

theorem btLe72_mono81 : ∀ (a : BT), btLe72 0 a = true → btLe72 1 a = true
  | .zero, _ => rfl
  | .D u c, h => by
      obtain ⟨hu, hc⟩ := btLe72_D 0 u c h
      show (decide (u ≤ 1) && btLe72 1 c) = true
      rw [decide_eq_true (show u ≤ 1 by omega), btLe72_mono81 c hc]; rfl
  | .sum a b, h => by
      obtain ⟨ha, hb⟩ := btLe72_sum 0 a b h
      show (btLe72 1 a && btLe72 1 b) = true
      rw [btLe72_mono81 a ha, btLe72_mono81 b hb]; rfl

/-- **添字がすべて 0 なら像は ε₀ より下。** 像は `0`・`⊕`・`ω^·` だけで作られる。 -/
theorem lt_dict_E81 (Hp : PsiIdxOKStd172) : ∀ (a : BT), btLe72 0 a = true →
    BT.isStd a = true → lt (dict a) E081 = true
  | .zero, _, _ => by rw [Trans.Dict.dict_zero]; exact lt_zero_E81
  | .D u c, hb, hs => by
      obtain ⟨hu, hbc⟩ := btLe72_D 0 u c hb
      have hu0 : u = 0 := Nat.le_zero.mp hu
      subst hu0
      have ih := lt_dict_E81 Hp c hbc (isStd_of_D hs)
      have hic := (inT_dict_of_std172 Hp c (btLe72_mono81 c hbc) (isStd_of_D hs)).1
      rw [Trans.Dict.dict_D,
        collapse0_eq77 (dict c) hic
          (fun p hp => ltW_toList79 (dict c) hic (ltW_of_ltE81 hic ih) p hp)]
      exact ltE_omegaNF81 hic ih
  | .sum a b, hb, hs => by
      obtain ⟨hba, hbb⟩ := btLe72_sum 0 a b hb
      obtain ⟨hsa, hsb⟩ := isStd_of_sum hs
      have hia := (inT_dict_of_std172 Hp a (btLe72_mono81 a hba) hsa).1
      have hib := (inT_dict_of_std172 Hp b (btLe72_mono81 b hbb) hsb).1
      rw [Trans.Dict.dict_sum]
      exact lt_plus_E81 hia hib (lt_dict_E81 Hp a hba hsa) (lt_dict_E81 Hp b hbb hsb)

/-- **先頭の添字が 1 なら像は `Ω₁` 以上。** §79.7 の `le_reg1_collapse1_79` を頭に当てる。 -/
theorem le_reg1_dict_of_not_lowHd81 (Hp : PsiIdxOKStd172) : ∀ (a : BT), btLe72 1 a = true →
    BT.isStd a = true → lowHd81 a = false → le (reg 1) (dict a) = true
  | .zero, _, _, hl => absurd hl (by
      rw [show lowHd81 BT.zero = true from rfl]; exact Bool.noConfusion)
  | .D u c, hb, hs, hl => by
      obtain ⟨hu, hbc⟩ := btLe72_D 1 u c hb
      have hu1 : u = 1 := by
        cases u with
        | zero => exact Bool.noConfusion (show (true : Bool) = false from hl)
        | succ k => omega
      subst hu1
      rw [Trans.Dict.dict_D]
      exact le_reg1_collapse1_79 (dict c) (inT_dict_of_std172 Hp c hbc (isStd_of_D hs)).1
        (fun p hp => lt_pure73_reg2 (pure73_toList _ (pure73_dict c hbc) p hp))
  | .sum x y, hb, hs, hl => by
      obtain ⟨hbx, hby⟩ := btLe72_sum 1 x y hb
      obtain ⟨hsx, hsy⟩ := isStd_of_sum hs
      have hpx : BT.isP x = true := isP_of_isStd_sum81 hs
      have hlx : lowHd81 x = false := by rw [← lowHd_sum81 (y := y) hpx]; exact hl
      have h1 := le_reg1_dict_of_not_lowHd81 Hp x hbx hsx hlx
      have hix := (inT_dict_of_std172 Hp x hbx hsx).1
      have hiy := (inT_dict_of_std172 Hp y hby hsy).1
      have hapx : (dict x).isAP = true := by
        cases x with
        | zero => exact Bool.noConfusion hpx
        | sum _ _ => exact Bool.noConfusion hpx
        | D v z => rw [Trans.Dict.dict_D, collapse_eq]; exact isAP_omegaNF _
      rw [Trans.Dict.dict_sum]
      exact le_trans_inT inT_W79 hix (inT_plus hix hiy) h1
        (le_self_plus_ap81 hix hapx hiy)

end

/-! ### §81.7 組み立て — 残るのは両辺が `Ω₁` 以上の場合ひとつ

`dict b < Ω₁` なら §81.1、`dict a < Ω₁ ≤ dict b` なら §81.4 (`K` の条件で `dict a < ε₀`)。
残るのは `Ω₁ ≤ dict a < dict b` — 両辺で Veblen の折り畳みが回る場合だけである。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- **残る場合。** 両辺が `Ω₁` 以上のときの `collapse 0` の単調性。**証明していない。** -/
def CollapseMono0Hi81 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lt (dict a) (dict b) = true →
    lt (collapse 0 (dict a)) (collapse 0 (dict b)) = true

/-- **§81 の主定理。** §79 の `CollapseMono0_79` に残るのは両辺が `Ω₁` 以上の場合だけ。 -/
theorem collapseMono0_of_hi81 (Hp : PsiIdxOKStd172) (H : CollapseMono0Hi81) :
    CollapseMono0_79 := by
  intro a b hbA hbB hsA hsB h
  have hba := (btLe72_D 1 0 a hbA).2
  have hbb := (btLe72_D 1 0 b hbB).2
  have hsa := isStd_of_D hsA
  have hsb := isStd_of_D hsB
  have hia := inT_dict_of_std172 Hp a hba hsa
  have hib := inT_dict_of_std172 Hp b hbb hsb
  by_cases hWb : le (reg 1) (dict b) = true
  · by_cases hWa : le (reg 1) (dict a) = true
    · exact H a b hbA hbB hsA hsB hWa hWb h
    · have hlow : lowHd81 a = true := by
        cases hh : lowHd81 a with
        | true => rfl
        | false => exact absurd (le_reg1_dict_of_not_lowHd81 Hp a hba hsa hh) hWa
      have hb0 : btLe72 0 a = true :=
        btLe0_of_lowHd81 a hba hsa hlow (lowHd_GB_of_std81 hsA hlow)
      exact lt_collapse0_cross81 hia.1 (lt_dict_E81 Hp a hb0 hsa) hib.1 hib.2
        (Hp 0 b (by omega) hbb hsB) hWb
  · have hlb : lt (dict b) (reg 1) = true := lt_of_not_le_inT inT_W79 hib.1 (bool_false hWb)
    have hla : lt (dict a) (reg 1) = true := lt_trans_inT hia.1 hib.1 inT_W79 h hlb
    exact collapse0_mono_ltW81 hia.1 hib.1 hla hlb h

theorem dictHeadLt81 (Hp : PsiIdxOKStd172) (H : CollapseMono0Hi81) : DictHeadLt77 :=
  dictHeadLt79 Hp (collapseMono0_of_hi81 Hp H)

theorem dictLtA74_81 (Hp : PsiIdxOKStd172) (H : CollapseMono0Hi81) : DictLtA74 :=
  dictLtA74_79 Hp (collapseMono0_of_hi81 Hp H)

theorem vOfLtA71_81 (Hp : PsiIdxOKStd172) (H : CollapseMono0Hi81) : VOfLtA71 :=
  vOfLtA71_79 Hp (collapseMono0_of_hi81 Hp H)

theorem limDecS1_81 (Hp : PsiIdxOKStd172) (H : CollapseMono0Hi81) : LimDecS1 :=
  limDecS1_79 Hp (collapseMono0_of_hi81 Hp H)

theorem limIncS1_81 (Hp : PsiIdxOKStd172) (H : CollapseMono0Hi81) : LimIncS1 :=
  limIncS1_79 Hp (collapseMono0_of_hi81 Hp H)

/-- **326 行目の証明書。** §79 の 4 つのうち `CollapseMono0_79` が `CollapseMono0Hi81` に
    替わる。他の 3 つ (`PsiIdxOKStd172`・`CofDenseS1`・`BCofIn71`) は §81 では動かない。 -/
theorem certIn_t326_81 (Hp : PsiIdxOKStd172) (H : CollapseMono0Hi81)
    (HCD : CofDenseS1) (HBC : BCofIn71)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_79 Hp (collapseMono0_of_hi81 Hp H) HCD HBC hacc

end

/-! ### §81.8 測定 (凍結)

**構成。** §79.9 の構成をそのまま使う。種 `bs81` は段 1 以下の 6 項
(`0`・`1`・`ω`・`Ω₁`・`ψ₁ψ₁0`・`ψ₀ψ₁0`)。**深さの線** `deep81` は `ψ₀`・`ψ₁` を
1 段ずつかぶせて 2 つに 1 つ間引く操作を 7 回繰り返した層の合併 (入れ子は 10 段まで)。
**幅の線** `wide81` は成分が降順の 2 項和・3 項和。**領域の外** `out81` は添字 2・3 を
1 段/2 段かぶせたもの。合わせて 127 項。

§81 の仮説はそのうえに `K` の条件 — `BT.isStd (ψ₀ ·)` — を課す:

    popAll81   127 項
    popGood81   55 項  段 1 以下かつ `BT.isStd`      (§79 の母集団)
    popK81      49 項  さらに `BT.isStd (ψ₀ ·)`      (**§81 の仮説そのもの**)

変数は自分の走る形で振ってある: 対は `(a, b)` の順序対で `dict a < dict b` のものだけを
数え、`Ω₁` の上下で 3 つに分ける。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

private def dedup81 (l : List BT) : List BT :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []
private def every81 (k : Nat) (l : List BT) : List BT :=
  (l.zipIdx.filter (fun p => p.2 % k == 0)).map (·.1)
private def dep81 : BT → Nat
  | .zero => 0
  | .D _ a => 1 + dep81 a
  | .sum a b => max (dep81 a) (dep81 b)
private def wid81 : BT → Nat
  | .sum a b => wid81 a + wid81 b
  | _ => 1

private def bs81 : List BT :=
  [BT.zero, BT.D 0 BT.zero, BT.D 0 (BT.D 0 BT.zero), BT.D 1 BT.zero,
   BT.D 1 (BT.D 1 BT.zero), BT.D 0 (BT.D 1 BT.zero)]
private def cap01_81 (l : List BT) : List BT := l.map (BT.D 0) ++ l.map (BT.D 1)
private def cap23_81 (l : List BT) : List BT := l.map (BT.D 2) ++ l.map (BT.D 3)
private def lay81 : Nat → List BT → List BT
  | 0, l => l
  | n + 1, l => every81 2 (cap01_81 (lay81 n l))
private def deep81 : List BT :=
  dedup81 (bs81 ++ lay81 1 bs81 ++ lay81 2 bs81 ++ lay81 3 bs81 ++ lay81 4 bs81
            ++ lay81 5 bs81 ++ lay81 6 bs81 ++ lay81 7 bs81)
private def prin81 (l : List BT) : List BT := l.filter BT.isP
private def sums2_81 (l : List BT) : List BT :=
  (prin81 l).flatMap (fun a => ((prin81 l).filter (fun b => BT.le b a)).map (BT.sum a))
private def sums3_81 (l : List BT) : List BT :=
  (prin81 l).flatMap (fun a =>
    ((prin81 l).filter (fun b => BT.le b a)).flatMap (fun b =>
      ((prin81 l).filter (fun c => BT.le c b)).map (fun c => BT.sum a (BT.sum b c))))
private def wide81 : List BT :=
  dedup81 (every81 5 (sums2_81 (every81 2 deep81))
            ++ every81 31 (sums3_81 (every81 3 deep81)))
private def out81 : List BT :=
  dedup81 (every81 2 (cap23_81 (every81 3 deep81))
            ++ every81 3 (cap01_81 (every81 5 (cap23_81 (every81 5 deep81)))))

private def popAll81 : List BT := dedup81 (deep81 ++ wide81 ++ out81)
private def popGood81 : List BT := popAll81.filter (fun x => btLe72 1 x && BT.isStd x)
private def popStd81 : List BT := popAll81.filter BT.isStd
private def popLv81 : List BT := popAll81.filter (btLe72 1 ·)
/-- §81 の仮説そのもの — `K` の条件つき。 -/
private def popK81 : List BT := popGood81.filter (fun a => BT.isStd (BT.D 0 a))

private def lowW81 (a : BT) : Bool := TM.Term.lt (dict a) (reg 1)
private def pairs81 (l : List BT) : List (BT × BT) := l.flatMap (fun a => l.map (fun b => (a, b)))
private def inv0_81 (l : List (BT × BT)) : Nat :=
  l.countP (fun p => TM.Term.lt (dict p.1) (dict p.2) &&
    !(TM.Term.lt (collapse 0 (dict p.1)) (collapse 0 (dict p.2))))
private def cnt0_81 (l : List (BT × BT)) : Nat :=
  l.countP (fun p => TM.Term.lt (dict p.1) (dict p.2))
private def monoFail0_81 (l : List BT) : Nat := inv0_81 (pairs81 l)

/-! 母集団の形 — 深さも幅も。 -/
#guard (popAll81.length, popGood81.length, popStd81.length, popLv81.length, popK81.length)
        == (127, 55, 67, 109, 49)
#guard (popK81.foldl (fun m x => max m (dep81 x)) 0,
        popK81.countP (fun x => wid81 x == 1), popK81.countP (fun x => wid81 x == 2),
        popK81.countP (fun x => wid81 x == 3)) == (9, 24, 20, 5)

/-! **分割の内訳。** `dict a < dict b` の順序対 1176 のうち、両辺が `Ω₁` の下は 36
    (§81.1)、`Ω₁` をまたぐのが 360 (§81.4)、両辺が `Ω₁` 以上が 780 (残った場合)。
    逆向き — `dict a` が `Ω₁` 以上で `dict b` が下 — は 0 対 (推移律の確認)。 -/
#guard (cnt0_81 ((pairs81 popK81).filter (fun p => lowW81 p.1 && lowW81 p.2)),
        cnt0_81 ((pairs81 popK81).filter (fun p => lowW81 p.1 && !(lowW81 p.2))),
        cnt0_81 ((pairs81 popK81).filter (fun p => !(lowW81 p.1) && !(lowW81 p.2))),
        cnt0_81 ((pairs81 popK81).filter (fun p => !(lowW81 p.1) && lowW81 p.2)))
        == (36, 360, 780, 0)

/-! **肯定 1 — `K` の条件つきでは 3 つの場合すべてで反転 0。**
    最初の 2 つは §81.1・§81.4 が定理にした分 (定理なので確認)、3 つ目が残った分。 -/
#guard (inv0_81 ((pairs81 popK81).filter (fun p => lowW81 p.1 && lowW81 p.2)),
        inv0_81 ((pairs81 popK81).filter (fun p => lowW81 p.1 && !(lowW81 p.2))),
        inv0_81 ((pairs81 popK81).filter (fun p => !(lowW81 p.1) && !(lowW81 p.2))))
        == (0, 0, 0)

/-! **否定 1 — `K` の条件を落とすと 66 対反転し、その 65 対はまたぐ場合にある。**
    §79 は同じ母集団で 66 と測った。その内訳は (下,下) 0・(下,上) 65・(上,上) 1。
    **§81.1 が `K` の条件を使わないのも、§81.4 が二重に使うのも、この内訳のとおり。**
    段の上限だけ、標準性だけに緩めると 109 対・614 対。 -/
#guard (monoFail0_81 popK81, monoFail0_81 popGood81,
        monoFail0_81 popStd81, monoFail0_81 popLv81) == (0, 66, 109, 614)
#guard (inv0_81 ((pairs81 popGood81).filter (fun p => lowW81 p.1 && lowW81 p.2)),
        inv0_81 ((pairs81 popGood81).filter (fun p => lowW81 p.1 && !(lowW81 p.2))),
        inv0_81 ((pairs81 popGood81).filter (fun p => !(lowW81 p.1) && !(lowW81 p.2))))
        == (0, 65, 1)

/-! **肯定 2 — §81.5・§81.6 の 2 本。** `K` の条件のもとで `dict a < Ω₁` と
    「添字がすべて 0」は一致し (9 項ずつ、食い違い 0)、そのとき像は ε₀ より下。 -/
#guard (popK81.countP lowW81, popK81.countP (btLe72 0 ·),
        popK81.countP (fun a => lowW81 a && !(btLe72 0 a)),
        popK81.countP (fun a => btLe72 0 a && !(lowW81 a))) == (9, 9, 0, 0)
#guard popK81.countP (fun a => lowW81 a && !(TM.Term.lt (dict a) E081)) == 0

/-! **肯定 3 — §81.3 の下界は `K` の条件を要らない。** `Ω₁ ≤ dict a` なら
    `ε₀ ≤ ψ₀(dict a)`。3 つの母集団すべてで反例 0。 -/
#guard (popGood81.countP (fun a => !(lowW81 a) && !(TM.Term.le E081 (collapse 0 (dict a)))),
        popStd81.countP (fun a => !(lowW81 a) && !(TM.Term.le E081 (collapse 0 (dict a)))),
        popLv81.countP (fun a => !(lowW81 a) && !(TM.Term.le E081 (collapse 0 (dict a)))))
        == (0, 0, 0)

/-! **否定 2 — 破れるのは ε₀ の**上界**のほうで、それが `K` の条件の置き場所。**
    `K` の条件を外すと `dict a < Ω₁` なのに `dict a ≥ ε₀` の項が **5 つ**出る。
    最小の証人は `a = ψ₀ψ₁0` で `dict a = ε₀` ちょうど。そしてそれは `ψ₀` が
    単射でない対 `(ψ₀ψ₁0, ψ₁0)` — `ψ₀(ε₀) = ψ₀(Ω₁) = ε₀` — そのものである。
    `BT.isStd (ψ₀ψ₀ψ₁0) = false` がそれを外に置いている。 -/
#guard popGood81.countP (fun a => lowW81 a && !(TM.Term.lt (dict a) E081)) == 5
#guard collapse 0 (dict (BT.D 0 (BT.D 1 BT.zero))) == collapse 0 (dict (BT.D 1 BT.zero))
#guard TM.Term.lt (dict (BT.D 0 (BT.D 1 BT.zero))) (dict (BT.D 1 BT.zero))
#guard BT.isStd (BT.D 0 (BT.D 0 (BT.D 1 BT.zero))) == false
#guard dict (BT.D 0 (BT.D 1 BT.zero)) == E081

/-! **否定 3 — 残った場合は 𝔗(M) だけの主張ではない。** `Ω₁ ≤ x < y` から
    `ψ₀(x) < ψ₀(y)` は**出ない**。上の (上,上) の 1 対がその証人で、
    `x = ω^(Ω₁ ⊕ ζ₀)` と `y = ω^(Ω₁ ⊕ Ω₁)` はどちらも `ψ₀` で `ζ₀ = φ̄(2,0)` に潰れる
    (`a = ψ₁ψ₀ψ₁ψ₁0`・`b = ψ₁ψ₁0`、どちらも `BT.isStd`)。外に置いているのは
    `BT.isStd (ψ₀ a) = false` だけである。**したがって `CollapseMono0Hi81` の証明も
    `K` の条件を消費しなければならず、折り畳みの比較だけでは閉じない。** -/
private def cexA81 : BT := BT.D 1 (BT.D 0 (BT.D 1 (BT.D 1 BT.zero)))
private def cexB81 : BT := BT.D 1 (BT.D 1 BT.zero)
#guard BT.isStd cexA81 && BT.isStd cexB81 && btLe72 1 cexA81 && btLe72 1 cexB81
#guard TM.Term.le (reg 1) (dict cexA81) && TM.Term.le (reg 1) (dict cexB81)
#guard TM.Term.lt (dict cexA81) (dict cexB81)
#guard collapse 0 (dict cexA81) == collapse 0 (dict cexB81)
#guard collapse 0 (dict cexA81) == phi (TM.Term.ofNat 2) zero
#guard BT.isStd (BT.D 0 cexA81) == false

end

/-! ### §81.9 公理 -/

/-! ## §82 THE `K`-GATE'S RESIDUE IS FALSE, AND THE COUNTEREXAMPLE IS INSIDE THE SUB-REGION

§80 reduced the `K`-gate to one clause, `LocalK2Big_80`, and proved with `not_pow80_bad80`
that the clause is not a statement about 𝔗(M) terms: `Ω₁ ⊕ ψ_{Ω₁}(Ω₂)` is a 𝔗(M) term that
breaks it.  The conclusion drawn there was correct and its consequence was named exactly:
**any proof must consume `dict` and `BT.isStd`.**  §82 consumes them.  What comes out is not a
proof.

**`LocalK2Big_80` IS FALSE.**  `not_localK2Big_80` is a theorem, and with it
`not_localK2Fst_78`, `not_localK2_78`, `not_localK2Pow_80`, `not_localK2BigPow_80`.  The
witness is a Buchholz term of fifteen symbols,

    aBad82 = ψ₁ψ₁ψ₁ψ₁0 ⊕ ψ₁ψ₁ψ₁ψ₀ψ₁ψ₁ψ₁ψ₁0

which satisfies **every** hypothesis of the clause — `btLe72 1`, `BT.isStd (ψ₀ ·)`,
`inT (dict ·)`, `dict · < M` — and breaks its conclusion.  The reason fits on one line: the
`ψ₀` inside the tail has the HEAD as its argument, so its collapse index is
`y = ω^{ω^{ω^{Ω₁·2}}}`, while the `Δ` of the tail's own scan step is
`ω^{ω^{ω^{Ω₁ ⊕ ψ_{Ω₁}(y)}}}` and `ψ_{Ω₁}(y) < Ω₁`, so `Δ < y`.  Buchholz asks *argument <
whole sum*, which the head satisfies because it IS the head; Rathjen asks *index < Δ*, and
`Δ` is fixed by the TAIL alone.  **The two normal-form conditions genuinely differ, and the
transport §68/§72/§73/§75/§78/§80 kept naming does not exist in this form.**  So the `K`-gate
as §78 and §80
stated it cannot be closed, and `certIn_t326_k2_78`, `certIn_t326_big80` and this section's own
`certIn_t326_node82` are **vacuous**: their first hypothesis is refutable.  Row 326's
certificate now waits on a clause that does not yet exist as a proved statement — §82.7 says
which one it has to be.

HOW IT WAS FOUND, AND WHAT IS PROVED ON THE WAY.  The counterexample is not a lucky guess; it
is what the localization produces when it is pushed.

  §82.1  **THE SCAN LOCALIZES.**  `wcnf_fst_wA82` — every pair the base-`w` scan emits has
         `ac.1 = wA w p` for a SINGLE component `p` of the `bigPart`.  §66's `mem_Kset_wcnf`
         traced the `K`-sets to the whole big part; the merging branch keeps the first
         component's `wA`, so the exponent itself traces to one component.

  §82.2  **THE COMPONENTS OF `dict a` ARE THE IMAGES OF THE COMPONENTS OF `a`.**
         `toList_dict82` — every `p ∈ toList (dict a)` is additively principal AND equals
         `dict t` for some `t ∈ BT.toL a`.  `dict` of a `ψ`-node is an `ω`-power
         (`isAP_collapse82`); `dict` of a sum is `plus`, and `plus` only ever DROPS
         components.  No `inT`, no `isStd`, no level bound.

  §82.3  **WHAT `BT.isStd (ψ₀ a)` ACTUALLY HANDS OVER.**  `comp_facts82` : each component
         `ψ_u c` of `a` is itself Buchholz standard (`isStd_toL82`) and its argument `c` is
         below `a` (`arg_mem_GB0_82` puts `c` into `G(a,0)`, `std0_split82` bounds it).
         **That is all of it.**  `G(a,0) < a` bounds the arguments inside `a` by `a`; it does
         not bound the arguments inside a component by that component.

  §82.4  **SO THE RESIDUE IS A CLAUSE ABOUT ONE NODE.**  `NodeBigT_82 t` — for the exponent
         `wA Ω₁ (dict t)` of one node, every `y ∈ K_{Ω₁} (dict t)` with `Ω₁ ≤ y` is below
         `W^(wA Ω₁ (dict t) ⊖ Ω₁)`.  `NodeBig_82` asks it of every component the scan
         reaches, and `localK2BigPow_of_node82` carries it to §80's smallest residual and on
         to row 326.  **The scan, the pair `(aV, cV)` and the coefficient are gone.**

  §82.5  **THE PER-NODE DECIDER IS EXACT.**  `nodeBigT_of_b82` and its converse
         `nodeb82_of_nodeBigT82`: on a firing node the decider and the clause are equivalent,
         so a `false` is a REFUTATION and not a failure to prove.  That is the instrument
         §82.6 uses.  `nodeBigT_of_empty82` disposes of the nodes with an empty `K`-set (110
         of the 141 the measurement reaches), and the two frozen guards keep §78's
         `ψ`-nesting-9 tower and width-2 sum.

  §82.6  **THE REFUTATION.**  Point the exact decider at the node `nBad82 = ψ₁ψ₁ψ₁ψ₀ψ₁ψ₁ψ₁ψ₁0`
         — §78's `kBad78` phenomenon as a tower — and it says `false` (`not_nodeBigT_nBad82`).
         By itself `nBad82` is outside the region: `BT.isStd (ψ₀ nBad82) = false`.  §82.3 says
         why that does not save the clause: put a bigger head in front and the SUM becomes
         standard while the component does not change.  `aBad82` is that sum, and
         `not_inherit_std82` freezes the anatomy — standard whole, non-standard component,
         and the component is one the scan reaches.

  §82.7  **THE REPAIR, AND ITS REDUCTION.**  `LocalK2BigC_82` is §80's clause with the
         component condition added: every `t ∈ BT.toL a` satisfies `BT.isStd (ψ₀ t)`.
         `localK2BigC_of_nodeStd82` reduces it — through §82.1 and §82.2 unchanged — to
         `NodeBigStd_82`, the per-node clause with the RIGHT side condition, and
         `localK2FstC_of_bigC82` restores the `Ω₁ >` half by §80.3.  `NodeBigStd_82` is
         measured at 0 failures on 265 nodes and is the honest successor of §78's
         `LocalK2_78`.

WHAT IS **NOT** CLAIMED.  `NodeBigStd_82` and `LocalK2BigC_82` are NOT proved.  Worse for the
gate: **nothing here shows the repaired region contains row 326 or is closed under the
fundamental sequence**, and until that is done `LocalK2BigC_82` cannot be plugged into
`certIn_t326_*` at all.  `LocalK2Snd_78` is untouched — §82 refutes only the `aV` side, which
is the side §78 already identified as the hard one.  `DictHeadLt77`, `CofDenseS1`, `BCofIn71`
are untouched.  §82.8's closed form for `Ω₁ · wA Ω₁ p` is a MEASUREMENT, not a theorem.

WHAT THE MEASUREMENT SAYS (§82.8 gives the construction: §78.5's three groups and §80.7's
fourth verbatim, plus the subterm closure and one new family built to answer §82's question).

  * **The refutation is not rare and the old populations could not see it.**  The new family
    is `h ⊕ t` with `h` any level-≤1 `ψ₁`-node of the corpus and `t` one of the 38 nodes that
    are `BT.isStd` but not `BT.isStd (ψ₀ ·)`; 5949 of those sums satisfy every hypothesis of
    `LocalK2Big_80` and **528 of them refute it**.  Inside the four groups themselves — 201
    qualifying terms, 373 qualifying subterms — there is **not one** refutation.  §78's "on
    the standard population it never fails" and §80's "all 87 failures are outside the region"
    were true of their corpora and false as statements.
  * **Every refutation is a component-standardness failure.**  Not one of the 528 has all its
    components `BT.isStd (ψ₀ ·)`, which is exactly the hypothesis §82.7 adds.  And the failure
    reaches inside the four groups too: 1 of the 141 reached nodes there is a component of a
    standard term without being standard-under-`ψ₀` itself.
  * **With the right side condition nothing falls.**  Of the 729 level-≤1 subterms, the 265
    that fire and satisfy `BT.isStd (ψ₀ ·)` give 0 failures; relaxing to `BT.isStd` alone
    gives 10, the smallest of which is `nBad82`.

  The positive side.  The per-node clause is not vacuous where it is used: 13 of the reached
  nodes carry a `K`-element `≥ Ω₁`, and the move from `K_{Ω₁} (wA Ω₁ (dict t))` to
  `K_{Ω₁} (dict t)` — the one place §82.4 asks for more than §80 did — changes no verdict
  anywhere inside the level bound.  `Ω₁ · wA Ω₁ p` equals the `≥ Ω₁` part of `log p` at all
  518 big components measured, which is the closed form that says what the node clause is.
-/

/-! ### §82.1 走査は一成分に落ちる -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§82.1 の主定理。** 走査が吐く対の第一成分は、`bigPart` のただ一つの成分の `wA`。
    §66 の `mem_Kset_wcnf` は「大きい成分ぜんぶ」までしか追えなかった — 併合の枝が
    先頭の `wA` を残すので、指数そのものは一成分に落ちる。 -/
theorem wcnf_fst_wA82 {w : Term} : ∀ (L : List Term) (ac : Term × Term),
    ac ∈ (wcnf w L).1 → ∃ p, p ∈ bigPart w L ∧ ac.1 = wA w p := by
  intro L
  induction L with
  | nil => intro ac hac; cases hac
  | cons p rest ih =>
    intro ac hac
    by_cases hlp : lt p w = true
    · rw [wcnf_cons_lt hlp] at hac; cases hac
    · have hlp' : lt p w = false := bool_false hlp
      have hbig : bigPart w (p :: rest) = p :: bigPart w rest := by
        show (if lt p w = true then [] else p :: bigPart w rest) = _
        rw [if_neg hlp]
      rw [wcnf_cons_ge hlp'] at hac
      cases hr : wcnf w rest with
      | mk fst snd =>
        rw [hr] at hac
        have hmem0 : ∀ (q : Term × Term), q ∈ fst → q ∈ (wcnf w rest).1 := by
          intro q hq; rw [hr]; exact hq
        cases fst with
        | nil =>
          exact ⟨p, by rw [hbig]; exact List.Mem.head _,
            by rw [List.mem_singleton.mp hac]⟩
        | cons ac0 ps =>
          cases ac0 with
          | mk a' c' =>
            have hac' : ac ∈ (if (wA w p == a') = true
                then ((wA w p, plus (wC w p) c') :: ps, snd)
                else ((wA w p, wC w p) :: (a', c') :: ps, snd)).1 := hac
            by_cases heq : (wA w p == a') = true
            · rw [if_pos heq] at hac'
              rcases List.mem_cons.mp hac' with h1 | h1
              · exact ⟨p, by rw [hbig]; exact List.Mem.head _, by rw [h1]⟩
              · obtain ⟨q, hq, hqe⟩ := ih ac (hmem0 _ (List.Mem.tail _ h1))
                exact ⟨q, by rw [hbig]; exact List.Mem.tail _ hq, hqe⟩
            · rw [if_neg heq] at hac'
              rcases List.mem_cons.mp hac' with h1 | h1
              · exact ⟨p, by rw [hbig]; exact List.Mem.head _, by rw [h1]⟩
              · obtain ⟨q, hq, hqe⟩ := ih ac (hmem0 _ h1)
                exact ⟨q, by rw [hbig]; exact List.Mem.tail _ hq, hqe⟩

end

/-! ### §82.2 `dict a` の成分は `a` の成分の像 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- `collapse` は `ω^·` なので加法主要 — 節の像はいつも一成分。 -/
theorem isAP_collapse82 (u : Nat) (x : Term) : (collapse u x).isAP = true := isAP_omegaNF _

theorem toList_dict_D82 (u : Nat) (c : BT) :
    toList (dict (BT.D u c)) = [dict (BT.D u c)] :=
  toList_of_isAP (isAP_collapse82 u (dict c))

/-- **§82.2 の主定理。** `dict a` の成分はどれも加法主要で、しかも `a` のある成分の像。
    `inT` も `isStd` も段の上限も要らない — `plus` は成分を落とすだけだから。 -/
theorem toList_dict82 : ∀ (a : BT), ∀ p ∈ toList (dict a),
    p.isAP = true ∧ ∃ t, t ∈ BT.toL a ∧ p = dict t := by
  intro a
  induction a with
  | zero => intro p hp; cases hp
  | D u c _ =>
    intro p hp
    rw [toList_dict_D82 u c] at hp
    rw [List.mem_singleton.mp hp]
    exact ⟨isAP_collapse82 u (dict c), BT.D u c, List.Mem.head _, rfl⟩
  | sum s t ihs iht =>
    intro p hp
    have hd : dict (BT.sum s t) = plus (dict s) (dict t) := rfl
    rw [hd] at hp
    cases hl : toList (dict t) with
    | nil =>
      rw [plus_nil hl] at hp
      obtain ⟨h1, u, hu, he⟩ := ihs p hp
      exact ⟨h1, u, List.mem_append.mpr (Or.inl hu), he⟩
    | cons b1 r =>
      rw [plus_cons66 hl] at hp
      have hap2 : ∀ x ∈ (toList (dict s)).filter (fun a => le b1 a) ++ (b1 :: r),
          x.isAP = true := by
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact (ihs x (List.mem_filter.mp h).1).1
        · exact (iht x (by rw [hl]; exact h)).1
      rw [toList_ofList hap2] at hp
      rcases List.mem_append.mp hp with h | h
      · obtain ⟨h1, u, hu, he⟩ := ihs p (List.mem_filter.mp h).1
        exact ⟨h1, u, List.mem_append.mpr (Or.inl hu), he⟩
      · obtain ⟨h1, u, hu, he⟩ := iht p (by rw [hl]; exact h)
        exact ⟨h1, u, List.mem_append.mpr (Or.inr hu), he⟩

end


/-! ### §82.3 Buchholz 側が渡すもの — と渡さないもの -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 和が標準なら成分も標準。 -/
theorem isStd_toL82 : ∀ (a : BT), BT.isStd a = true → ∀ t, t ∈ BT.toL a → BT.isStd t = true := by
  intro a
  induction a with
  | zero => intro _ t ht; cases ht
  | D u c _ =>
    intro h t ht
    rw [List.mem_singleton.mp (show t ∈ [BT.D u c] from ht)]
    exact h
  | sum s t ihs iht =>
    intro h x hx
    have h1 : (BT.isP s && BT.isStd s && BT.isStd t) = true :=
      (Bool.and_eq_true _ _).mp h |>.1
    have hs : BT.isStd s = true := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h1).1).2
    have ht2 : BT.isStd t = true := ((Bool.and_eq_true _ _).mp h1).2
    rcases List.mem_append.mp (show x ∈ BT.toL s ++ BT.toL t from hx) with h2 | h2
    · exact ihs hs x h2
    · exact iht ht2 x h2

/-- 成分の引数は `G(a,0)` の中 — `u ≤ 0` の分岐がないから、`GB 0` は引数をぜんぶ拾う。 -/
theorem arg_mem_GB0_82 : ∀ (a : BT) (u : Nat) (c : BT),
    BT.D u c ∈ BT.toL a → c ∈ BT.GB 0 a := by
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

/-- `isStd (ψ₀ a)` を割る。 -/
theorem std0_split82 {a : BT} (h : BT.isStd (BT.D 0 a) = true) :
    BT.isStd a = true ∧ ∀ e ∈ BT.GB 0 a, BT.lt e a = true := by
  have h1 : (BT.isStd a && (BT.GB 0 a).all (fun e => BT.lt e a)) = true := h
  obtain ⟨h2, h3⟩ := (Bool.and_eq_true _ _).mp h1
  exact ⟨h2, fun e he => List.all_eq_true.mp h3 e he⟩

/-- **§82.3 の主定理 — 残余が使ってよい Buchholz の事実。** 部分領域の項 `a` の成分
    `ψ_u c` はそれ自身 Buchholz 標準で、しかもその引数 `c` は `a` より小さい。
    **これが `BT.isStd (ψ₀ a)` の渡すすべて** — §82.6 の否定 2 が、渡さないものを言う。 -/
theorem comp_facts82 {a : BT} (h : BT.isStd (BT.D 0 a) = true) {u : Nat} {c : BT}
    (ht : BT.D u c ∈ BT.toL a) : BT.isStd (BT.D u c) = true ∧ BT.lt c a = true :=
  ⟨isStd_toL82 a (std0_split82 h).1 _ ht,
   (std0_split82 h).2 c (arg_mem_GB0_82 a u c ht)⟩

end

/-! ### §82.4 残余は一節ぶんの条項 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- `powOf80` は対の第一成分しか見ない。 -/
theorem powOf80_congr82 {w : Term} {ac ac' : Term × Term} (h : ac.1 = ac'.1) :
    powOf80 w ac = powOf80 w ac' := by
  unfold powOf80
  rw [h]

/-- **一節ぶんの残余。** `t` の像の `K` のうち `Ω₁` 以上の元は `W^(wA Ω₁ (dict t) ⊖ Ω₁)`
    より下。走査も対も係数も出てこない。 -/
def NodeBigT_82 (t : BT) : Prop :=
  ∀ ac : Term × Term, ac.1 = wA (reg 1) (dict t) → le (reg 1) ac.1 = true →
    ∀ y, y ∈ Kset (reg 1) (dict t) → le (reg 1) y = true →
      lt y (powOf80 (reg 1) ac) = true

/-- **§82 の残余。** 部分領域の項の成分のうち**走査がほんとうに届くもの**について、
    一節ぶんの条項。 -/
def NodeBig_82 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true →
    inT (dict a) = true → lt (dict a) M = true →
    ∀ t, t ∈ BT.toL a → dict t ∈ bigPart (reg 1) (toList (dict a)) → NodeBigT_82 t

/-- **§82.4 の主定理。** 節ごとの条項から §80 の最小の残余が出る。 -/
theorem localK2BigPow_of_node82 (H : NodeBig_82) : LocalK2BigPow_80 := by
  intro a hb hs hi hl ac hac hle y hy hge
  obtain ⟨p, hp, hpe⟩ := wcnf_fst_wA82 (toList (dict a)) ac hac
  obtain ⟨_, t, ht, hte⟩ := toList_dict82 a p (bigPart_sub _ _ p hp)
  rw [hte] at hpe hp
  refine H a hb hs hi hl t ht hp ac hpe hle y ?_ hge
  refine mem_Kset_wA (w := reg 1) ?_
  rw [← hpe]; exact hy

/-- 系 — §80.4 の残余。 -/
theorem localK2Big_of_node82 (H : NodeBig_82) : LocalK2Big_80 :=
  localK2Big_of_fst80 (localK2Fst_of_bigPow80 (localK2BigPow_of_node82 H))

/-- 系 — §78 の一条項。 -/
theorem localK2_of_node82 (H1 : NodeBig_82) (H2 : LocalK2Snd_78) : LocalK2_78 :=
  localK2_of_big80 (localK2Big_of_node82 H1) H2

/-- **326 行目の証明書。** `K` の側で待つのは節ごとの条項と §78 の `cV` 側だけ。
    **§82.6 以後、この定理は空回りである** — `NodeBig_82` は `not_nodeBig_82` で偽。
    §80 の `certIn_t326_big80` も §78 の `certIn_t326_k2_78` も同じ理由で空回り。 -/
theorem certIn_t326_node82 (H1 : NodeBig_82) (H2 : LocalK2Snd_78) (HD : DictHeadLt77)
    (HCD : CofDenseS1) (HBC : BCofIn71) (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_big80 (localK2Big_of_node82 H1) H2 HD HCD HBC hacc

end


/-! ### §82.5 判定器 — 一節ぶん、しかも過不足なし -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 一節ぶんの判定器。 -/
def nodeb82 (t : BT) : Bool :=
  (Kset (reg 1) (dict t)).all fun y =>
    !(le (reg 1) y) || lt y (powOf80 (reg 1) (wA (reg 1) (dict t), TM.Term.one))

/-- **判定器は証明。** §78.4・§80.5 と同じ形。 -/
theorem nodeBigT_of_b82 {t : BT} (h : nodeb82 t = true) : NodeBigT_82 t := by
  intro ac hac _ y hy hge
  rw [powOf80_congr82 (ac' := (wA (reg 1) (dict t), TM.Term.one)) hac]
  have h1 := List.all_eq_true.mp h y hy
  rw [hge, Bool.not_true, Bool.false_or] at h1
  exact h1

/-- **逆も。** 発火する節では判定器は条項と同値 — だから `false` は反証である。 -/
theorem nodeb82_of_nodeBigT82 {t : BT} (hf : le (reg 1) (wA (reg 1) (dict t)) = true)
    (H : NodeBigT_82 t) : nodeb82 t = true := by
  refine List.all_eq_true.mpr ?_
  intro y hy
  cases hge : le (reg 1) y with
  | false => rfl
  | true =>
    rw [Bool.not_true, Bool.false_or]
    exact H (wA (reg 1) (dict t), TM.Term.one) rfl hf y hy hge

/-- `K` が空なら条項は只。§82.8 の測定では 141 節のうち 110 節がこれ。 -/
theorem nodeBigT_of_empty82 {t : BT} (h : Kset (reg 1) (dict t) = []) : NodeBigT_82 t := by
  intro _ _ _ y hy _
  rw [h] at hy
  cases hy

/-- 凍結 (深さ) — §78.5 の `ψ` の入れ子 9 段の塔。`K_{Ω₁}` に `Ω₁` 以上の元がある節。 -/
theorem nodeBigT_wOK78 : NodeBigT_82 wOK78 := nodeBigT_of_b82 (by decide)

/-- 凍結 (幅) — §78.5 の二項和。 -/
theorem nodeBigT_wWide78 : NodeBigT_82 wWide78 := nodeBigT_of_b82 (by decide)

end


/-! ### §82.6 否定 — 残る条項は部分領域の上で偽 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- `LocalK2Big_80` を一項ぶんに落とした判定器。 -/
def k2bigb82 (a : BT) : Bool :=
  ((wcnf (reg 1) (toList (dict a))).1).all fun ac =>
    !(le (reg 1) ac.1) ||
      ((Kset (reg 1) ac.1).all fun y => !(le (reg 1) y) || lt y (ddOf75 (reg 1) ac))

/-- 条項が成り立てば判定器も通る — だから判定器の `false` は反証。 -/
theorem k2bigb_of_localK2Big82 (H : LocalK2Big_80) {a : BT} (hb : btLe72 1 a = true)
    (hs : BT.isStd (BT.D 0 a) = true) (hi : inT (dict a) = true) (hl : lt (dict a) M = true) :
    k2bigb82 a = true := by
  refine List.all_eq_true.mpr ?_
  intro ac hac
  cases hle : le (reg 1) ac.1 with
  | false => rfl
  | true =>
    rw [Bool.not_true, Bool.false_or]
    refine List.all_eq_true.mpr ?_
    intro y hy
    cases hge : le (reg 1) y with
    | false => rfl
    | true =>
      rw [Bool.not_true, Bool.false_or]
      exact H a hb hs hi hl ac hac hle y hy hge

/-- 段 1 以下で Buchholz 標準、しかし `ψ₀` をかぶせると標準でなくなる塔
    `ψ₁ψ₁ψ₁ψ₀ψ₁ψ₁ψ₁ψ₁0`。§78 の `kBad78` の塔版で、これ一つでは領域の外。 -/
def nBad82 : BT :=
  BT.D 1 (BT.D 1 (BT.D 1 (BT.D 0 (BT.D 1 (BT.D 1 (BT.D 1 (BT.D 1 BT.zero)))))))

/-- **反証。** `ψ₁ψ₁ψ₁ψ₁0 ⊕ nBad82` — 大きい頭をかぶせると和ぜんたいは
    `BT.isStd (ψ₀ ·)` を満たし、**部分領域の中に入る**。成分 `nBad82` はそのままなので
    `K` の条項はそこで破れる。§82.8 の測定でこれが最小 (記号 15 個)。

    **破れる理由は一行で言える。**  `nBad82` の中の `ψ₀` の引数は頭とちょうど同じ
    `ψ₁ψ₁ψ₁ψ₁0` で、その像は `y = ω^{ω^{ω^{Ω₁·2}}}`。走査の第二の対では

        aV = ω^{ω^{Ω₁ ⊕ ψ_{Ω₁}(y)}},  cV = 1,  Δ = ω^{ω^{ω^{Ω₁ ⊕ ψ_{Ω₁}(y)}}},
        K_{Ω₁} aV = {y},  そして ψ_{Ω₁}(y) < Ω₁ だから **Δ < y**。

    Buchholz の条件が要るのは「引数 < 和ぜんたい」で、頭は和より小さいからそれは通る。
    Rathjen の条件が要るのは「指数 < Δ」で、`Δ` を決めるのは**尾の**指数だけ。
    二つの標準形条件はここで本当に食い違う。 -/
def aBad82 : BT := BT.sum (BT.D 1 (BT.D 1 (BT.D 1 (BT.D 1 BT.zero)))) nBad82

/-- **`aBad82` は `LocalK2Big_80` の仮説をぜんぶ満たし、結論を破る。** -/
theorem aBad82_hyps :
    btLe72 1 aBad82 = true ∧ BT.isStd (BT.D 0 aBad82) = true ∧
    inT (dict aBad82) = true ∧ lt (dict aBad82) M = true ∧
    nBad82 ∈ BT.toL aBad82 ∧ BT.isStd nBad82 = true ∧
    BT.isStd (BT.D 0 nBad82) = false ∧
    k2bigb82 aBad82 = false :=
  ⟨by decide, by decide, by decide, by decide,
   List.Mem.tail _ (List.Mem.head _), by decide, by decide, by decide⟩

/-- **§82 の主定理 — `K` 門の残余は偽。** §80 が「𝔗(M) の項だけの事実ではない」と
    言った条項は、`dict` と `BT.isStd` を足しても救えない。 -/
theorem not_localK2Big_80 : ¬ LocalK2Big_80 := by
  intro H
  have h := k2bigb_of_localK2Big82 H aBad82_hyps.1 aBad82_hyps.2.1 aBad82_hyps.2.2.1
    aBad82_hyps.2.2.2.1
  rw [aBad82_hyps.2.2.2.2.2.2.2] at h
  exact Bool.noConfusion h

/-- 系 — §78 の `aV` 側は偽。 -/
theorem not_localK2Fst_78 : ¬ LocalK2Fst_78 := fun H => not_localK2Big_80 (localK2Big_of_fst80 H)

/-- 系 — §78 が `K` 門ぜんぶを縮めた一条項は偽。 -/
theorem not_localK2_78 : ¬ LocalK2_78 :=
  fun H => not_localK2Fst_78 (fun a hb hs hi hl ac hac hle y hy =>
    H a hb hs hi hl ac hac hle y (Or.inl hy))

/-- 系 — §80 の二つの残余も偽。 -/
theorem not_localK2Pow_80 : ¬ LocalK2Pow_80 := fun H => not_localK2Fst_78 (localK2Fst_of_pow80 H)
theorem not_localK2BigPow_80 : ¬ LocalK2BigPow_80 :=
  fun H => not_localK2Fst_78 (localK2Fst_of_bigPow80 H)

/-- 系 — §82.4 の節ごとの形も偽。 -/
theorem not_nodeBig_82 : ¬ NodeBig_82 := fun H => not_localK2BigPow_80 (localK2BigPow_of_node82 H)

/-- **落ちる節そのもの。** `nBad82` は段 1 以下で `BT.isStd` を満たし、`wA` は
    発火するのに、節ごとの条項は偽。要る側条件は `BT.isStd (ψ₀ ·)` の方。 -/
theorem not_nodeBigT_nBad82 :
    btLe72 1 nBad82 = true ∧ BT.isStd nBad82 = true ∧
    BT.isStd (BT.D 0 nBad82) = false ∧
    le (reg 1) (wA (reg 1) (dict nBad82)) = true ∧
    ¬ NodeBigT_82 nBad82 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro H
  have h1 := nodeb82_of_nodeBigT82 (by decide) H
  rw [show nodeb82 nBad82 = false from by decide] at h1
  exact Bool.noConfusion h1

/-- **なぜ救えないかの正確な理由。** `aBad82` は `BT.isStd (ψ₀ aBad82)` を満たすのに
    成分 `nBad82` は `BT.isStd (ψ₀ nBad82)` を満たさない。`G(a,0) < a` は `a` の中の
    引数を `a` で抑えるだけで、**成分の中の引数をその成分で抑えはしない**。
    §82.3 が渡すもの (成分の `BT.isStd` と `c < a`) はここで足りない。 -/
theorem not_inherit_std82 :
    BT.isStd (BT.D 0 aBad82) = true ∧ nBad82 ∈ BT.toL aBad82 ∧
    BT.isStd nBad82 = true ∧ BT.isStd (BT.D 0 nBad82) = false ∧
    dict nBad82 ∈ bigPart (reg 1) (toList (dict aBad82)) :=
  ⟨by decide, List.Mem.tail _ (List.Mem.head _), by decide, by decide, by decide⟩

end

/-! ### §82.7 修理 — 成分にも `BT.isStd (ψ₀ ·)` を課す -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 段の上限は成分に降りる。 -/
theorem btLe72_toL82 : ∀ (m : Nat) (a : BT), btLe72 m a = true →
    ∀ t, t ∈ BT.toL a → btLe72 m t = true := by
  intro m a
  induction a with
  | zero => intro _ t ht; cases ht
  | D u c _ =>
    intro h t ht
    rw [List.mem_singleton.mp (show t ∈ [BT.D u c] from ht)]
    exact h
  | sum s t ihs iht =>
    intro h x hx
    obtain ⟨h1, h2⟩ := btLe72_sum m s t h
    rcases List.mem_append.mp (show x ∈ BT.toL s ++ BT.toL t from hx) with h3 | h3
    · exact ihs h1 x h3
    · exact iht h2 x h3

/-- **正しい側条件つきの節ごとの残余。** §82.6 が落とした `nBad82` はここに入らない。 -/
def NodeBigStd_82 : Prop :=
  ∀ t : BT, btLe72 1 t = true → BT.isStd (BT.D 0 t) = true → NodeBigT_82 t

/-- **修理した条項 (`Ω₁` 以上の元)。** §78 の `LocalK2Fst_78` に「成分ぜんぶが
    `BT.isStd (ψ₀ ·)`」を足したもの。**足りない分は §82.6 がちょうど言っている。** -/
def LocalK2BigC_82 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true →
    (BT.toL a).all (fun t => BT.isStd (BT.D 0 t)) = true →
    inT (dict a) = true → lt (dict a) M = true →
    ∀ ac ∈ (wcnf (reg 1) (toList (dict a))).1, le (reg 1) ac.1 = true →
      ∀ y, y ∈ Kset (reg 1) ac.1 → le (reg 1) y = true →
        lt y (ddOf75 (reg 1) ac) = true

/-- 修理した条項 (元ぜんぶ)。 -/
def LocalK2FstC_82 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true →
    (BT.toL a).all (fun t => BT.isStd (BT.D 0 t)) = true →
    inT (dict a) = true → lt (dict a) M = true →
    ∀ ac ∈ (wcnf (reg 1) (toList (dict a))).1, le (reg 1) ac.1 = true →
      ∀ y, y ∈ Kset (reg 1) ac.1 → lt y (ddOf75 (reg 1) ac) = true

/-- **§82.7 の主定理。** 正しい側条件つきの節ごとの残余から修理した条項が出る。
    §82.1・§82.2 の局所化がそのまま効き、成分の側条件は仮説から只で降りる。 -/
theorem localK2BigC_of_nodeStd82 (H : NodeBigStd_82) : LocalK2BigC_82 := by
  intro a hb hs hc hi hl ac hac hle y hy hge
  obtain ⟨p, hp, hpe⟩ := wcnf_fst_wA82 (toList (dict a)) ac hac
  obtain ⟨_, t, ht, hte⟩ := toList_dict82 a p (bigPart_sub _ _ p hp)
  rw [hte] at hpe
  have hyt : y ∈ Kset (reg 1) (dict t) := by
    refine mem_Kset_wA (w := reg 1) ?_
    rw [← hpe]; exact hy
  have hpow : lt y (powOf80 (reg 1) ac) = true :=
    H t (btLe72_toL82 1 a hb t ht) (List.all_eq_true.mp hc t ht) ac hpe hle y hyt hge
  obtain ⟨hcl, hd⟩ := inT_toList (dict a) hi
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList (dict a)) hcl hd
    (ltM_toList (dict a) hi hl)
  obtain ⟨hi1, _, hi2, _⟩ := hallOK ac hac
  have hz := (wcnf_snd_ne_zero80 (toList (dict a)) hcl ac hac).2
  exact lt_of_lt_of_le3 (inT_le_fragR y (inT_mem_Kset75 ac.1 hi1 _ y hy))
    (inT_le_fragR _ (inT_powOf80 (inT_reg 1) hi1))
    (inT_le_fragR _ (inT_ddOf75 (inT_reg 1) hi1 hi2))
    hpow (le_powOf_ddOf80 (inT_reg 1) hi1 hi2 hz)

/-- `Ω₁` より下の元は §80.3 が只で片づける — だから修理は両方の形で同じ。 -/
theorem localK2FstC_of_bigC82 (H : LocalK2BigC_82) : LocalK2FstC_82 := by
  intro a hb hs hc hi hl ac hac hle y hy
  obtain ⟨hcl, hd⟩ := inT_toList (dict a) hi
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList (dict a)) hcl hd
    (ltM_toList (dict a) hi hl)
  obtain ⟨hi1, _, hi2, _⟩ := hallOK ac hac
  have hz := (wcnf_snd_ne_zero80 (toList (dict a)) hcl ac hac).2
  have hyi : inT y = true := inT_mem_Kset75 ac.1 hi1 _ y hy
  by_cases hlt : lt y (reg 1) = true
  · exact lt_dd_of_lt_reg80 omegaNF_reg1_80 hi1 hi2 hz hy hlt
  · refine H a hb hs hc hi hl ac hac hle y hy ?_
    rcases lt_comparable_inT hyi (inT_reg 1) with h | h | h
    · exact absurd h hlt
    · rw [h]; exact Evidence.WF.le_self _
    · show ((reg 1 == y) || lt (reg 1) y) = true
      rw [h]; exact Bool.or_true _

end


/-! ### §82.8 測定 (凍結)

**構成を先に書く。**  母集団は §78.5 の三つと §80.7 の一つを**そのまま**使う —
`pop78` (領域の中、129 個)、`bmp78` (`ψ₀` を `ψ₂`・`ψ₃` に差し替えた 217 個)、
`nst78` (段の上限は満たすが標準でない 118 個)、`hi80` (標準のまま `ψ₂` を内側に持つ
223 個)。あわせて `grp82` は 687 項。§82 が語るのは項ではなく**節**なので、そこから
四つ導く。

    S82    = grp82 の各項の部分項をぜんぶ、重複を除いたもの           1722 節
    hypA82 = grp82 のうち `LocalK2Big_80` の仮説をぜんぶ満たすもの
             (`btLe72 1`・`BT.isStd (ψ₀ ·)`・`inT (dict ·)`・`dict · < M`)   201 項
    hypB82 = hypA82 の成分のうち**走査がほんとうに届くもの**          141 節、発火 100 歩
    BP82   = grp82 の像の `Ω₁` 以上の成分                             518 個

**反証はこの四群の中には無い** (201 項でも 373 部分項でも 0)。そこで**一群だけ足す**。
§82.6 の反証は「大きい頭 ⊕ 悪い節」の形なので、その形をぜんぶ作る。

    L1_82  = S82 の段 1 以下の `ψ₁` 節ぜんぶ                          421 節
    bad82  = そのうち `BT.isStd` は満たすが `BT.isStd (ψ₀ ·)` を満たさないもの  38 節
    refFam82 = `h ⊕ t` (h ∈ L1_82, t ∈ bad82) のうち仮説をぜんぶ満たすもの  5949 項

**`refFam82` の 5949 項のうち 528 項が `LocalK2Big_80` を破る**。最小は記号 15 個の
`aBad82`。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

def grp82 : List BT := pop78 ++ bmp78 ++ nst78 ++ hi80
def subs82 : BT → List BT
  | .zero => [BT.zero]
  | .D u a => BT.D u a :: subs82 a
  | .sum a b => BT.sum a b :: (subs82 a ++ subs82 b)
def S82 : List BT := (grp82.flatMap subs82).eraseDups
def std0_82 (t : BT) : Bool := BT.isStd (BT.D 0 t)
def fireN82 (t : BT) : Bool := le (reg 1) (wA (reg 1) (dict t))
def okHyp82 (a : BT) : Bool :=
  btLe72 1 a && std0_82 a && inT (dict a) && lt (dict a) M
/-- `K` を `wA` の側で見る形 — もとの条項が語るのはこちら。 -/
def nodeA82 (t : BT) : Bool :=
  (Kset (reg 1) (wA (reg 1) (dict t))).all fun y =>
    !(le (reg 1) y) || lt y (powOf80 (reg 1) (wA (reg 1) (dict t), TM.Term.one))
def hypA82 : List BT := grp82.filter okHyp82
def bigNodes82 (a : BT) : List BT :=
  (BT.toL a).filter fun t => (bigPart (reg 1) (toList (dict a))).contains (dict t)
def hypB82 : List BT := (hypA82.flatMap bigNodes82).eraseDups
def hypA82' : List BT := grp82.filter fun a => std0_82 a && inT (dict a) && lt (dict a) M
def hypB82' : List BT := (hypA82'.flatMap bigNodes82).eraseDups
def bigComps82 (a : BT) : List Term := (toList (dict a)).filter (fun p => !lt p (reg 1))
def BP82 : List Term := (grp82.flatMap bigComps82).eraseDups
def isD1_82 : BT → Bool | .D 1 _ => true | _ => false
def L1_82 : List BT := S82.filter fun t => btLe72 1 t && isD1_82 t
def bad82 : List BT := L1_82.filter fun t => BT.isStd t && !(std0_82 t)
def refFam82 : List BT := (L1_82.flatMap fun h => bad82.map fun t => BT.sum h t).filter okHyp82

-- 母集団の大きさ。
-- (重い測定。数は §82 の前書きに記録) #guard (grp82.length, S82.length) == (687, 1722)
#guard (hypA82.length, hypB82.length, (hypB82.filter fireN82).length) == (201, 141, 100)
#guard BP82.length == 518
-- (重い測定。数は §82 の前書きに記録) #guard (L1_82.length, bad82.length, refFam82.length) == (421, 38, 5949)

/-! **否定 1 — 残る条項は偽、しかも §78・§80 の母集団は一つも見ていない。**
`refFam82` の 5949 項のうち **528 項**で `LocalK2Big_80` が破れる。四群そのもの
(201 項) でも、その部分項ぜんぶ (373 項) でも反証は **0** — だから §78 の
「標準なら落ちない」も §80 の「87 の失敗はぜんぶ領域の外」も、母集団の形の話で
あって定理ではなかった。`not_localK2Big_80` が最小の反証を凍結する。 -/

-- (重い測定。数は §82 の前書きに記録) #guard (refFam82.filter fun a => !(k2bigb82 a)).length == 528
#guard (hypA82.filter fun a => !(k2bigb82 a)).length == 0
-- (重い測定。数は §82 の前書きに記録) #guard (S82.filter fun a => okHyp82 a).length == 373
-- (重い測定。数は §82 の前書きに記録) #guard ((S82.filter okHyp82).filter fun a => !(k2bigb82 a)).length == 0
-- (重い測定。数は §82 の前書きに記録) #guard (refFam82.filter fun a => !(k2bigb82 a) && BT.size a == 15).length == 1
-- (重い測定。数は §82 の前書きに記録) #guard (refFam82.filter fun a => !(k2bigb82 a) && BT.size a < 15).length == 0

/-! **否定 2 — 落ちるのはいつも成分の側。** 反証する 528 項はどれも
「成分のどれかが `BT.isStd (ψ₀ ·)` を満たさない」形で、**修理した条項 (§82.7) の
仮説を満たすものは一つも無い**。逆に、四群の中でも `hypB82` の 141 節のうち
1 節は `BT.isStd (ψ₀ ·)` を満たさない — 継承しないことは領域の中でも起きている。 -/

-- (重い測定。数は §82 の前書きに記録) #guard (refFam82.filter fun a => (BT.toL a).all std0_82).length == 0
#guard (hypB82.filter fun t => !(std0_82 t)).length == 1
#guard (hypB82.filter fun t => !(BT.isStd t)).length == 0

/-! **肯定 1 — 正しい側条件をつければ落ちない。** 段 1 以下の部分項 729 個のうち、
発火して `BT.isStd (ψ₀ ·)` を満たす 265 節で節ごとの条項は反例 0。`BT.isStd` だけに
ゆるめると 10 節で落ちる (`not_nodeBigT_nBad82` がその最小)。
`hypB82` の 100 歩でも反例 0 で、**空回りではない** — 13 節で `K_{Ω₁} (dict t)` に
`Ω₁` 以上の元があり、110 節では `K` が空 (`nodeBigT_of_empty82` が只で片づける分)。 -/

-- (重い測定。数は §82 の前書きに記録) #guard (S82.filter fun t => btLe72 1 t).length == 729
-- (重い測定。数は §82 の前書きに記録) #guard (S82.filter fun t => btLe72 1 t && fireN82 t && std0_82 t).length == 265
-- (重い測定。数は §82 の前書きに記録) #guard (S82.filter fun t => btLe72 1 t && fireN82 t && std0_82 t && !(nodeb82 t)).length == 0
-- (重い測定。数は §82 の前書きに記録) #guard (S82.filter fun t => btLe72 1 t && fireN82 t && BT.isStd t && !(nodeb82 t)).length == 10
#guard (hypB82.filter fun t => fireN82 t && !(nodeb82 t)).length == 0
#guard (hypB82.filter fun t =>
  ((Kset (reg 1) (dict t)).filter (le (reg 1))).length > 0).length == 13
#guard (hypB82.filter fun t => (Kset (reg 1) (dict t)).isEmpty).length == 110

/-! **肯定 2 — 節の形に移すのに払った代償は、段の上限の中では只。** §82.4 の条項は
`K_{Ω₁} (dict t)` を見るが、もとの条項が語るのは `K_{Ω₁} (wA Ω₁ (dict t))` だけ。
段 1 以下では判定は一度も食い違わない (`hypB82` の 100 歩でも、`S82` の標準な
265 節でも 0)。段の上限を外すと 3 歩だけ食い違い、そこは `wA` 側なら通る。 -/

#guard (hypB82.filter fun t => fireN82 t && (nodeb82 t != nodeA82 t)).length == 0
-- (重い測定。数は §82 の前書きに記録) #guard (S82.filter fun t =>
--     btLe72 1 t && fireN82 t && std0_82 t && (nodeb82 t != nodeA82 t)).length == 0
#guard hypB82'.length == 343
#guard (hypB82'.filter fun t => fireN82 t && !(nodeb82 t)).length == 3
#guard (hypB82'.filter fun t => fireN82 t && !(nodeA82 t)).length == 0
#guard (hypB82'.filter fun t => fireN82 t && !(nodeb82 t) && btLe72 1 t).length == 0

/-! **肯定 3 — 閉じた形 (測定のみ、証明ではない)。** 大きい成分 `p` について
`Ω₁ · wA Ω₁ p` は `log p` の `Ω₁` 以上の部分に**ぴったり等しい** — 518 個で反例 0。
だから節ごとの条項は「`p` の `K` の大きい元が `ω^(log p の大きい部分)` より下」と
読める。`W^(wA Ω₁ p ⊖ Ω₁) ≤ p` も 518 個で反例 0 で、逆向きは 83 個で落ちる。 -/

#guard (BP82.filter fun p => !(mulL (reg 1) (wA (reg 1) p)
  == ofList ((toList (logOm p)).filter (fun q => !lt q (reg 1))))).length == 0
#guard (BP82.filter fun p =>
  !(le (powOf80 (reg 1) (wA (reg 1) p, TM.Term.one)) p)).length == 0
#guard (BP82.filter fun p =>
  !(le p (powOf80 (reg 1) (wA (reg 1) p, TM.Term.one)))).length == 83

end

/-! ### §82.9 公理 -/

/-! ## §83 THE TWO HALVES OF COFINALITY — THE BUCHHOLZ SIDE IS A THEOREM

Row 326's certificate stands on four named hypotheses (§76.5b).  Two of them are the
cofinality clause, split by §71.4 into

    CofDenseS1   the 𝔗(M) side — the sub-region is dense below every limit value
    BCofIn71     the Buchholz side — pure `BT`, no `dict` anywhere

**§83 proves `BCofIn71`.**  Row 326's certificate loses a hypothesis; three remain.

WHAT THE PROOF IS.  `BCofIn71` asks for `∃ n` with `¬ (fs t n < u)`.  What is actually
proved is the STRICT form `mainDom83` — `∃ n, u < fs t n` — because that is the shape the
recursion needs: the sub-challenger produced at every step has to be strictly dominated,
not merely not-dominating.  The strict form implies the asked form by §74.4's asymmetry.

  §83.1  **THE ORDER THEORY `ltS` STILL LACKED.**  `ltS_trans83` (transitivity — §68/§74
         had irreflexivity, asymmetry and trichotomy but not this) and
         `ltS_prefix_indep83`: on a list that is NOT an extension of `P`, the comparison
         against `P ++ X` does not see `X` at all.  `splitP83` is the either/or that every
         later section opens with — either the challenger extends the prefix, or the prefix
         alone already decides.

  §83.2  **THE VALUE IS THE PLAIN MAP.**  `toL_bValA71_map83` : `(bValA71 x).toL =
         (toL x).map fB72`, unconditionally.  This is what carries §72's `descOK_map72`
         (`nonIncr` becomes descending) and §72.3's `key72` (every node's argument is below
         the tree) onto the `BT` side, and it is what turns "a component of the value" back
         into "a node of the index".

  §83.3  **THE CHALLENGER'S HEREDITARY STANDARDNESS.**  `GS83` — `nonIncr`, `stdIn`,
         `lvlLe 1` — is closed under taking a node's argument, and `stdIn` hands out
         `visOK v c c` for each node, which is exactly `key72`'s missing hypothesis.
         `subLt83` : every node's argument of a `GS83` index with `visOK 0` is strictly
         below it in `BT.lt`.

  §83.4  **THE COLLAPSING BASE.**  `iterDom83`.  `rwB`'s bottom branch replaces the last
         summand by the `iterD` tower, and the challenger has to be caught by some rung.
         The induction is on the SIZE OF THE CHALLENGER, not on the term: at the bottom of
         the level-one chain the challenger loses one `ψ₀` and the tower gains one rung.
         `subLt83` is what makes the challenger shrink — without `visOK` the statement is
         FALSE, and `ψ₀(Ω)` is the witness (it is below `Ω` and above every rung).

  §83.5  **THE `repNode` BASE.**  `repDomBase83`.  Here the head of the sequence is
         CONSTANT — `ψ_v(P)·(n+1)` — so no rung dominates by its head; what dominates is
         the LENGTH, and the challenger's tail is bounded by its own head because `nonIncr`
         makes the component list descending.  `lt_succ_le83` (`x < y ⊕ 1 → x ≤ y`) is the
         other half.

  §83.6  **THE TWO RECURSIONS.**  `repDom83` / `rwDom83`, the dominance twins of §71.7's
         `repB_dec_inc71` / `rwB_dec_inc71`, on the same two inductions with the same
         invariant `hasLowAnc w c ∨ v < w`.

  §83.7  **THE ASSEMBLY.**  `mainDom83`, `bCofIn71_thm : BCofIn71`, and the certificate
         forms `cofInS1_83`, `limCofS1_83`, `certIn_t326_83` / `certIn_t326_step83`.
         AND THE SPLIT HAS NOTHING LEFT TO GIVE.  `cofDenseS1_iff_limCofS1_83` : under the
         bridge, `CofDenseS1 ↔ LimCofS1` — the reverse direction is three lines, because with
         `LimCofS1` the witness `u` can be taken to be `fsB t n` itself and `LimDecS1` puts it
         below `vOf t`.  So §71.4's split bought exactly one thing, the Buchholz half, and
         §83 has spent it: what remains of row 326's cofinality clause is the WHOLE 𝔗(M)
         statement, and no further splitting of it is available.

  §83.8  **THE NEGATIVE RESULT.**  `not_iterDom_without_visOK83` — drop `visOK 0` from
         §83.4 and the statement becomes FALSE.  `sbad83 = ψ₀(Ω)` satisfies `nonIncr`,
         `stdIn` and `lvlLe 1`, sits strictly below `Ω`, and `sbad83_not_dominated` proves
         that NO rung of the tower reaches it — it is the supremum.  This is the Buchholz-side
         twin of §70.3's `sbad_not_witness`, and the same shape §69 used to refute the
         unrestricted clause.

  §83.9  The measurement (frozen).  §83.10 the axioms.

WHAT IS **NOT** CLAIMED.  `CofDenseS1` is NOT proved — §83 proves nothing about 𝔗(M) and
mentions `dict` only through §76's ready-made consumers.  Row 326 still needs
`PsiIdxOKStd172`, `DictLtA74` and `CofDenseS1`.  What §83.7 adds about it is a NEGATIVE
structural fact, not progress on it: `CofDenseS1` is now equivalent to the full cofinality
clause, so a proof has to move an arbitrary 𝔗(M) term `s` — one that is NOT in the image of
`vOf` and so cannot be carried across the bridge — and that needs a partial inverse of `dict`
on the initial segment, which no section of this file builds.
Nothing here says the `K`-gate is closed (§82 refuted the form it had), and nothing here is
a statement about `vOf`: the bridge `VOfLtA71'` is still what carries `BCofIn71` to `CofInS1`.
-/

/-! ### §83.1 `ltS` の推移律と前置きの独立性 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- 右が空なら小さくならない。 -/
theorem ltS_right_nil83 : ∀ (l : List BT), ltS l [] = false
  | [] => ltS_nil_nil
  | x :: xs => ltS_cons_nil x xs

/-- **`ltS` は推移的。** §68/§74 が持っていなかった唯一の順序律。 -/
theorem ltS_trans83 : ∀ (n : Nat) (x y z : List BT), Atoms x → Atoms y → Atoms z →
    sizeLB x + sizeLB y + sizeLB z ≤ n → ltS x y = true → ltS y z = true → ltS x z = true := by
  intro n
  induction n with
  | zero =>
    intro x y z _ _ _ hn _ h2
    cases z with
    | nil => exact absurd h2 (by rw [ltS_right_nil83]; exact fun hc => Bool.noConfusion hc)
    | cons z0 zs =>
      exact absurd hn (by have := one_le_size z0
                          show ¬ (sizeLB x + sizeLB y + (z0.size + sizeLB zs) ≤ 0); omega)
  | succ k ih =>
    intro x y z hax hay haz hn h1 h2
    cases z with
    | nil => exact absurd h2 (by rw [ltS_right_nil83]; exact fun hc => Bool.noConfusion hc)
    | cons z0 zs =>
      obtain ⟨p, c, rfl⟩ := haz z0 (List.Mem.head _)
      cases x with
      | nil => exact ltS_nil_cons _ _
      | cons x0 xs =>
        obtain ⟨u, a, rfl⟩ := hax x0 (List.Mem.head _)
        cases y with
        | nil => exact absurd h1 (by rw [ltS_right_nil83]; exact fun hc => Bool.noConfusion hc)
        | cons y0 ys =>
          obtain ⟨v, b, rfl⟩ := hay y0 (List.Mem.head _)
          have hsx : sizeLB (BT.D u a :: xs) = (1 + a.size) + sizeLB xs := rfl
          have hsy : sizeLB (BT.D v b :: ys) = (1 + b.size) + sizeLB ys := rfl
          have hsz : sizeLB (BT.D p c :: zs) = (1 + c.size) + sizeLB zs := rfl
          have hta := sizeLB_toL a
          have htb := sizeLB_toL b
          have htc := sizeLB_toL c
          have h1a := one_le_size a
          have h1b := one_le_size b
          have h1c := one_le_size c
          rw [ltS_cons u a xs v b ys] at h1
          rw [ltS_cons v b ys p c zs] at h2
          rw [ltS_cons u a xs p c zs]
          by_cases huv : u < v
          · have hpv : ¬ (p < v) := by
              intro hc
              rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt hc)), if_pos hc] at h2
              exact Bool.noConfusion h2
            exact if_pos (by omega)
          · rw [if_neg huv] at h1
            by_cases hvu : v < u
            · exact absurd h1 (by rw [if_pos hvu]; exact fun hc => Bool.noConfusion hc)
            · rw [if_neg hvu] at h1
              have huv' : u = v := by omega
              subst huv'
              by_cases hup : u < p
              · exact if_pos hup
              · rw [if_neg hup] at h2 ⊢
                by_cases hpu : p < u
                · exact absurd h2 (by rw [if_pos hpu]; exact fun hc => Bool.noConfusion hc)
                · rw [if_neg hpu] at h2 ⊢
                  by_cases hab : (a == b) = true
                  · have hab' : a = b := bt_eq_of_beq71 a b hab
                    subst hab'
                    rw [if_pos hab] at h1
                    by_cases hac : (a == c) = true
                    · rw [if_pos hac]
                      rw [if_pos hac] at h2
                      exact ih xs ys zs (fun w hw => hax w (List.Mem.tail _ hw))
                        (fun w hw => hay w (List.Mem.tail _ hw))
                        (fun w hw => haz w (List.Mem.tail _ hw)) (by omega) h1 h2
                    · rw [if_neg hac]
                      rw [if_neg hac] at h2
                      exact h2
                  · rw [if_neg hab] at h1
                    by_cases hbc : (b == c) = true
                    · have hbc' : b = c := bt_eq_of_beq71 b c hbc
                      subst hbc'
                      rw [if_neg hab]
                      exact h1
                    · rw [if_neg hbc] at h2
                      have hac : ¬ ((a == c) = true) := by
                        intro hc
                        have hac' : a = c := bt_eq_of_beq71 a c hc
                        subst hac'
                        rw [ltS_asymm74 (sizeLB b.toL + sizeLB a.toL) b.toL a.toL
                          (atoms_toL74 b) (atoms_toL74 a) (Nat.le_refl _) h2] at h1
                        exact Bool.noConfusion h1
                      rw [if_neg hac]
                      exact ih a.toL b.toL c.toL (atoms_toL74 a) (atoms_toL74 b)
                        (atoms_toL74 c) (by omega) h1 h2

/-- **`BT.lt` は推移的。** -/
theorem lt_trans83 {s t w : BT} (h1 : BT.lt s t = true) (h2 : BT.lt t w = true) :
    BT.lt s w = true := by
  rw [lt_eq_ltS] at h1 h2
  rw [lt_eq_ltS]
  exact ltS_trans83 (sizeLB s.toL + sizeLB t.toL + sizeLB w.toL) s.toL t.toL w.toL
    (atoms_toL74 s) (atoms_toL74 t) (atoms_toL74 w) (Nat.le_refl _) h1 h2

/-- **前置きの独立性。** `L` が `P` の延長でないなら、`P` の右に何を足しても比較は変わらない。 -/
theorem ltS_prefix_indep83 : ∀ (P L : List BT), Atoms P → Atoms L → (∀ R, L ≠ P ++ R) →
    ∀ X, ltS L (P ++ X) = ltS L P := by
  intro P
  induction P with
  | nil => intro L _ _ hne _; exact absurd rfl (hne L)
  | cons p0 ps ih =>
    intro L hap haL hne X
    obtain ⟨q, e, rfl⟩ := hap p0 (List.Mem.head _)
    cases L with
    | nil => rfl
    | cons l0 ls =>
      obtain ⟨u, a, rfl⟩ := haL l0 (List.Mem.head _)
      show ltS (BT.D u a :: ls) (BT.D q e :: (ps ++ X)) = ltS (BT.D u a :: ls) (BT.D q e :: ps)
      rw [ltS_cons u a ls q e (ps ++ X), ltS_cons u a ls q e ps]
      by_cases h1 : u < q
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : q < u
        · rw [if_pos h2, if_pos h2]
        · rw [if_neg h2, if_neg h2]
          by_cases h3 : (a == e) = true
          · rw [if_pos h3, if_pos h3]
            refine ih ls (fun z hz => hap z (List.Mem.tail _ hz))
              (fun z hz => haL z (List.Mem.tail _ hz)) ?_ X
            intro R hc
            refine hne R ?_
            have hae : a = e := bt_eq_of_beq71 a e h3
            have huq : u = q := Nat.le_antisymm (Nat.not_lt.mp h2) (Nat.not_lt.mp h1)
            rw [hae, huq, hc]
            rfl
          · rw [if_neg h3, if_neg h3]

/-- **§83.1 の主定理。** 前置きで割る。延長であるか、前置きだけで決まるかのどちらか。 -/
theorem splitP83 (P L : List BT) (hap : Atoms P) (haL : Atoms L) :
    (∃ R, L = P ++ R) ∨ (∀ X, ltS L (P ++ X) = ltS L P) := by
  by_cases h : ∃ R, L = P ++ R
  · exact Or.inl h
  · exact Or.inr (ltS_prefix_indep83 P L hap haL (fun R hc => h ⟨R, hc⟩))

end

/-! ### §83.2 値の成分列は節の列の像そのもの

`bValA71` の成分列は `toL` の `map fB72` である — 前置きも崩れも入らない。これで §72 の
道具 (`descOK_map72`・`key72`・`argTransfer72`) がそのまま `bValA71` の側で使える。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- **§83.2 の主定理。** 無条件。 -/
theorem toL_bValA71_map83 : ∀ (x : B), (bValA71 x).toL = (toL x).map fB72
  | .nil => rfl
  | .nd w r c => by
      rw [toL_bValA71_nd w r c, toL_nd w r c, List.map_append, toL_bValA71_map83 r]
      rfl

/-- 値の成分は `.D` の列。 -/
theorem atoms_bValA71_83 (x : B) : Atoms (bValA71 x).toL := atoms_toL74 (bValA71 x)

/-- 一節の値。段が 1 以下なら `bArg` は `bValA71`。 -/
theorem toL_bValA71_nd83 (v : Nat) (r c : B) (hc : lvlLe 1 c = true) :
    (bValA71 (.nd v r c)).toL = (bValA71 r).toL ++ [BT.D v (bValA71 c)] := by
  rw [toL_bValA71_nd v r c, bArg_eq_bValA71_71 c v hc]

/-- 成分から節へ戻る。段が 1 以下なら成分の引数は部分木の値。 -/
theorem mem_toL_bValA71_83 (x : B) (hx : lvlLe 1 x = true) (v : Nat) (z : BT)
    (h : BT.D v z ∈ (bValA71 x).toL) : ∃ ξ : B, (v, ξ) ∈ toL x ∧ z = bValA71 ξ := by
  rw [toL_bValA71_map83 x] at h
  obtain ⟨q, hq, he⟩ := List.mem_map.mp h
  have he' : BT.D q.1 (bArg q.1 q.2) = BT.D v z := he
  have h1 : q.1 = v := by injection he'
  have h2 : bArg q.1 q.2 = z := by injection he'
  refine ⟨q.2, ?_, ?_⟩
  · rw [← h1]; exact hq
  · rw [← h2, h1, bArg_eq_bValA71_71 q.2 v (lvlL72_of_lvlLe x hx q hq).2]

/-- 段の上限は最後の節の段を縛る。 -/
theorem lastLvl_le83 : ∀ (t : B) (m : Nat), lvlLe m t = true → lastLvl t ≤ m := by
  intro t
  induction t with
  | nil => intro m _; exact Nat.zero_le m
  | nd v r c _ ihc =>
    intro m h
    obtain ⟨h1, _, h3⟩ := (lvlLe_nd_iff m v r c).mp h
    cases c with
    | nil => exact h1
    | nd u s d => exact ihc m h3

end

/-! ### §83.3 挑戦者の遺伝的な標準性

挑戦者 `u` について要るのは 3 つだけ — 和が降べき (`nonIncr`)、各節の中が良い (`stdIn`)、
段が 1 以下 (`lvlLe 1`)。`stdIn` は節の引数ごとにこの 3 つと `visOK` を配る (`stdIn_mem83`)
ので、`GS83` は「節の引数を取る」操作で閉じている。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- **挑戦者の遺伝的な標準性。** `nfB` は要らない — 節の引数の段は 1 でもよい。 -/
def GS83 (x : B) : Prop := nonIncr x = true ∧ stdIn x = true ∧ lvlLe 1 x = true

theorem gs83_of_std83 (x : B) (h : stdB1 x = true) : GS83 x := by
  have hs := stdB_of_stdB1 x h
  have hs' : ((nfB x && nonIncr x) && stdIn x) = true := hs
  obtain ⟨h1, h3⟩ := (Bool.and_eq_true _ _).mp hs'
  obtain ⟨_, h2⟩ := (Bool.and_eq_true _ _).mp h1
  exact ⟨h2, h3, lvlLe1_of_stdB1 x h⟩

/-- `stdIn` は節ごとに `nonIncr`・`visOK`・`stdIn` を配る。 -/
theorem stdIn_mem83 : ∀ (t : B), stdIn t = true → ∀ q ∈ toL t,
    nonIncr q.2 = true ∧ visOK q.1 q.2 q.2 = true ∧ stdIn q.2 = true := by
  intro t
  induction t with
  | nil => intro _ q hq; cases hq
  | nd v r c ihr _ =>
    intro h q hq
    obtain ⟨h1, h2, h3, h4⟩ := stdIn_nd h
    rw [toL_nd] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ihr h1 q hq
    · rw [List.mem_singleton.mp hq]; exact ⟨h2, h3, h4⟩

/-- **`GS83` は節の引数を取る操作で閉じている。** -/
theorem gs83_mem83 (x : B) (hx : GS83 x) (q : Nat × B) (hq : q ∈ toL x) :
    GS83 q.2 ∧ visOK q.1 q.2 q.2 = true := by
  obtain ⟨h2, h3, h4⟩ := stdIn_mem83 x hx.2.1 q hq
  exact ⟨⟨h2, h4, (lvlL72_of_lvlLe x hx.2.2 q hq).2⟩, h3⟩

/-- 節の列は部分木を取っても増えない。 -/
theorem nodes72_trans83 : ∀ (t : B) (q : Nat × B), q ∈ nodes72 t →
    ∀ q', q' ∈ nodes72 q.2 → q' ∈ nodes72 t := by
  intro t
  induction t with
  | nil => intro q hq; cases hq
  | nd v r c ihr ihc =>
    intro q hq q' hq'
    have hq2 : q ∈ nodes72 r ++ ((v, c) :: nodes72 c) := hq
    show q' ∈ nodes72 r ++ ((v, c) :: nodes72 c)
    rcases List.mem_append.mp hq2 with h | h
    · exact List.mem_append.mpr (Or.inl (ihr q h q' hq'))
    · rcases List.mem_cons.mp h with h | h
      · rw [h] at hq'
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hq')))
      · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr (ihc q h q' hq'))))

/-- 段の上限は節の列に伝わる。 -/
theorem lvlLe_nodes83 : ∀ (t : B), lvlLe 1 t = true → ∀ q ∈ nodes72 t,
    q.1 ≤ 1 ∧ lvlLe 1 q.2 = true := by
  intro t
  induction t with
  | nil => intro _ q hq; cases hq
  | nd v r c ihr ihc =>
    intro h q hq
    obtain ⟨h1, h2, h3⟩ := (lvlLe_nd_iff 1 v r c).mp h
    have hq2 : q ∈ nodes72 r ++ ((v, c) :: nodes72 c) := hq
    rcases List.mem_append.mp hq2 with hh | hh
    · exact ihr h2 q hh
    · rcases List.mem_cons.mp hh with hh | hh
      · rw [hh]; exact ⟨h1, h3⟩
      · exact ihc h3 q hh

/-- **§83.3 の主定理。** 良い添字のどの節の引数も、その添字より真に小さい。
    §72.3 の `key72` を `bValA71` の側へ移したもの。**`visOK 0` が要る。** -/
theorem subLt83 (x : B) (hx : GS83 x) (hv : visOK 0 x x = true) :
    ∀ q ∈ nodes72 x, BT.lt (bValA71 q.2) (bValA71 x) = true := by
  intro q hq
  have hc := key72 x hx.2.2 hx.1 hv hx.2.1 q hq
  have hl := (lvlLe_nodes83 x hx.2.2 q hq).2
  have h := argTransfer72 0 0 q.2 x hl hx.2.2 hc
  rw [bArg_eq_bValA71_71 q.2 0 hl, bArg_eq_bValA71_71 x 0 hx.2.2] at h
  exact h

/-- 値の成分列は降べき。§72.4a の `descOK_map72`。 -/
theorem descOK_bValA71_83 (x : B) (hx : GS83 x) : descOK72 ((bValA71 x).toL) = true := by
  rw [toL_bValA71_map83 x]
  exact descOK_map72 (toL x) (lvlL72_of_lvlLe x hx.2.2) hx.1

end

/-! ### §83.4 崩れの枝の底 — `iterD` の塔は挑戦者を捕まえる

`rwB` の底の枝は最後の加数を `iterD` の塔で置き換える。挑戦者をどの段が捕まえるかは
項の形では決まらない — **挑戦者の大きさ**で決まる。段 1 の鎖の底まで降りると挑戦者は
`ψ₀` を一つ失い、塔は一段伸びる。それが `subLt83` の役目で、`visOK` を落とすとこの
主張は**偽になる** (`ψ₀(Ω)` は `Ω` より下だがどの段よりも上)。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- 段 1 の鎖。`hasLowAnc 1 c = false` と `lastLvl c = 1` は「節がぜんぶ段 1」と同じ。 -/
def Chain83 (c : B) : Prop :=
  c ≠ .nil ∧ lvlLe 1 c = true ∧ lastLvl c = 1 ∧ hasLowAnc 1 c = false

theorem plugB_leaf83 (v : Nat) (r y : B) : plugB (.nd v r .nil) y = appB r y := rfl

theorem plugB_nd83 (v : Nat) (r : B) (u : Nat) (s d y : B) :
    plugB (.nd v r (.nd u s d)) y = .nd v r (plugB (.nd u s d) y) := rfl

/-- 鎖の底の節の段は 1。 -/
theorem chainLeaf83 (u : Nat) (Q : B) (h : Chain83 (.nd u Q .nil)) : u = 1 := h.2.2.1

/-- 鎖の引数はまた鎖。 -/
theorem chainArg83 (u : Nat) (Q d : B) (h : Chain83 (.nd u Q d)) (hd : d ≠ .nil) :
    u = 1 ∧ Chain83 d := by
  obtain ⟨_, hlv, hll, hlow⟩ := h
  obtain ⟨h1, _, h3⟩ := (lvlLe_nd_iff 1 u Q d).mp hlv
  rw [hasLowAnc_nd71 1 u Q d hd] at hlow
  obtain ⟨hu, hd2⟩ := Bool.or_eq_false_iff.mp hlow
  have hu1 : u = 1 := by
    have : ¬ (u < 1) := by intro hcc; rw [decide_eq_true hcc] at hu; exact Bool.noConfusion hu
    omega
  exact ⟨hu1, ⟨hd, h3, by rw [← hll]; exact (lastLvl_nd71 u Q d hd).symm, hd2⟩⟩

/-- 一節どうしの比較の分解。 -/
theorem ltS_cons_single83 (p : Nat) (z : BT) (rest : List BT) (v : Nat) (A : BT)
    (h : ltS (BT.D p z :: rest) [BT.D v A] = true) : p < v ∨ (p = v ∧ BT.lt z A = true) := by
  rw [ltS_cons p z rest v A []] at h
  by_cases h1 : p < v
  · exact Or.inl h1
  · rw [if_neg h1] at h
    by_cases h2 : v < p
    · exact absurd h (by rw [if_pos h2]; exact fun hc => Bool.noConfusion hc)
    · rw [if_neg h2] at h
      by_cases h3 : (z == A) = true
      · rw [if_pos h3, ltS_right_nil83] at h
        exact absurd h (fun hc => Bool.noConfusion hc)
      · rw [if_neg h3] at h
        exact Or.inr ⟨Nat.le_antisymm (Nat.not_lt.mp h2) (Nat.not_lt.mp h1),
          by rw [lt_eq_ltS]; exact h⟩

/-- 引数が真に小さければ一節は小さい。 -/
theorem ltS_single83 (p : Nat) (z T : BT) (rest : List BT) (h : BT.lt z T = true) :
    ltS (BT.D p z :: rest) [BT.D p T] = true := by
  have hne : ¬ ((z == T) = true) := by
    intro hcc
    rw [bt_eq_of_beq71 z T hcc, lt_irrefl74] at h
    exact Bool.noConfusion h
  rw [ltS_cons p z rest p T [], if_neg (Nat.lt_irrefl p), if_neg (Nat.lt_irrefl p),
    if_neg hne, ← lt_eq_ltS]
  exact h

/-- 段が小さい方が小さい。 -/
theorem ltS_lvl83 (p q : Nat) (z T : BT) (rest ys : List BT) (h : p < q) :
    ltS (BT.D p z :: rest) (BT.D q T :: ys) = true := by
  rw [ltS_cons p z rest q T ys, if_pos h]

theorem toL_iterD_zero83 (c : B) (hc : lvlLe 1 c = true) :
    (bValA71 (iterD 0 c 0)).toL = [BT.D 0 (bValA71 (plugB c .nil))] :=
  toL_bValA71_nd83 0 .nil (plugB c .nil) (lvlLe_plugB c 1 .nil hc rfl)

theorem toL_iterD_succ83 (c : B) (hc : lvlLe 1 c = true) (m : Nat) :
    (bValA71 (iterD 0 c (m + 1))).toL = [BT.D 0 (bValA71 (plugB c (iterD 0 c m)))] :=
  toL_bValA71_nd83 0 .nil (plugB c (iterD 0 c m))
    (lvlLe_plugB c 1 _ hc (lvlLe_iterD m 0 c 1 (Nat.zero_le 1) hc))

/-- **§83.4 の主定理。** 挑戦者の大きさについての強い帰納法。`c` は塔を作る鎖 (固定)、
    `d` はいま見ている鎖の尻尾。 -/
theorem iterDom83 (c : B) (hc : Chain83 c) : ∀ (N : Nat) (η : B), sizeB η < N →
    lvlLe 1 η = true → (∀ q ∈ nodes72 η, BT.lt (bValA71 q.2) (bValA71 c) = true) →
    ∀ (d : B), Chain83 d → BT.lt (bValA71 η) (bValA71 d) = true →
    ∃ n, BT.lt (bValA71 η) (bValA71 (plugB d (iterD 0 c n))) = true := by
  intro N
  induction N with
  | zero => intro η hsz; exact absurd hsz (Nat.not_lt_zero _)
  | succ k ih =>
    intro η hsz hlv hsub d hd hlt
    obtain ⟨hdne, hdlv, hdll, hdlow⟩ := hd
    cases d with
    | nil => exact absurd rfl hdne
    | nd u Q e =>
      obtain ⟨hu1, hQ, he⟩ := (lvlLe_nd_iff 1 u Q e).mp hdlv
      have hatP : Atoms (bValA71 Q).toL := atoms_bValA71_83 Q
      have hatL : Atoms (bValA71 η).toL := atoms_bValA71_83 η
      cases e with
      | nil =>
        -- 鎖の底。塔が一段伸びる。
        have hu : u = 1 := chainLeaf83 u Q ⟨hdne, hdlv, hdll, hdlow⟩
        subst hu
        rw [lt_eq_ltS, toL_bValA71_nd83 1 Q .nil rfl] at hlt
        rcases splitP83 (bValA71 Q).toL (bValA71 η).toL hatP hatL with ⟨R, hR⟩ | hind
        · rw [hR, ltS_append_left71 _ hatP] at hlt
          have hatR : Atoms R := by
            intro z hz
            exact hatL z (by rw [hR]; exact List.mem_append.mpr (Or.inr hz))
          cases hRc : R with
          | nil =>
            refine ⟨0, ?_⟩
            rw [lt_eq_ltS, plugB_leaf83, toL_bValA71_appB71, hR, hRc,
              ltS_append_left71 _ hatP, toL_iterD_zero83 c hc.2.1]
            exact ltS_nil_cons _ _
          | cons z0 zs =>
            obtain ⟨p, ζ, hz0⟩ := hatR z0 (by rw [hRc]; exact List.Mem.head _)
            rw [hRc, hz0] at hlt
            have hp : p = 0 := by
              rcases ltS_cons_single83 p ζ zs 1 (bValA71 B.nil) hlt with h | h
              · omega
              · exact absurd h.2 (by
                  rw [lt_eq_ltS, show (bValA71 B.nil).toL = [] from rfl, ltS_right_nil83]
                  exact fun hcc => Bool.noConfusion hcc)
            subst hp
            obtain ⟨ξ, hξm, hξv⟩ := mem_toL_bValA71_83 η hlv 0 ζ
              (by rw [hR, hRc, hz0]; exact List.mem_append.mpr (Or.inr (List.Mem.head _)))
            have hξn : (0, ξ) ∈ nodes72 η := toL_sub_nodes72 η (0, ξ) hξm
            have hξc : BT.lt (bValA71 ξ) (bValA71 c) = true := hsub (0, ξ) hξn
            have hξsz : sizeB ξ < k := by
              have := sizeB_mem72 η (0, ξ) hξm
              show sizeB ((0, ξ) : Nat × B).2 < k
              omega
            have hξlv : lvlLe 1 ξ = true := (lvlL72_of_lvlLe η hlv (0, ξ) hξm).2
            have hξsub : ∀ q ∈ nodes72 ξ, BT.lt (bValA71 q.2) (bValA71 c) = true :=
              fun q hq => hsub q (nodes72_trans83 η (0, ξ) hξn q hq)
            obtain ⟨m, hm⟩ := ih ξ hξsz hξlv hξsub c hc hξc
            refine ⟨m + 1, ?_⟩
            rw [lt_eq_ltS, plugB_leaf83, toL_bValA71_appB71, hR, hRc, hz0,
              ltS_append_left71 _ hatP, toL_iterD_succ83 c hc.2.1 m]
            rw [hξv]
            exact ltS_single83 0 _ _ zs hm
        · refine ⟨0, ?_⟩
          rw [lt_eq_ltS, plugB_leaf83, toL_bValA71_appB71, hind]
          rw [hind] at hlt
          exact hlt
      | nd u2 s2 d2 =>
        -- 鎖を一つ降りる。挑戦者も一つ小さくなる。
        have hene : (B.nd u2 s2 d2) ≠ .nil := by intro hcc; exact B.noConfusion hcc
        obtain ⟨hu, hch⟩ := chainArg83 u Q _ ⟨hdne, hdlv, hdll, hdlow⟩ hene
        subst hu
        rw [lt_eq_ltS, toL_bValA71_nd83 1 Q _ he] at hlt
        rcases splitP83 (bValA71 Q).toL (bValA71 η).toL hatP hatL with ⟨R, hR⟩ | hind
        · rw [hR, ltS_append_left71 _ hatP] at hlt
          have hatR : Atoms R := by
            intro z hz
            exact hatL z (by rw [hR]; exact List.mem_append.mpr (Or.inr hz))
          have hplug : ∀ n : Nat, (bValA71 (plugB (B.nd 1 Q (B.nd u2 s2 d2)) (iterD 0 c n))).toL
              = (bValA71 Q).toL ++ [BT.D 1 (bValA71 (plugB (B.nd u2 s2 d2) (iterD 0 c n)))] := by
            intro n
            rw [plugB_nd83 1 Q u2 s2 d2 (iterD 0 c n)]
            exact toL_bValA71_nd83 1 Q _ (lvlLe_plugB _ 1 _ he
              (lvlLe_iterD n 0 c 1 (Nat.zero_le 1) hc.2.1))
          cases hRc : R with
          | nil =>
            refine ⟨0, ?_⟩
            rw [lt_eq_ltS, hplug 0, hR, hRc, ltS_append_left71 _ hatP]
            exact ltS_nil_cons _ _
          | cons z0 zs =>
            obtain ⟨p, ζ, hz0⟩ := hatR z0 (by rw [hRc]; exact List.Mem.head _)
            rw [hRc, hz0] at hlt
            rcases ltS_cons_single83 p ζ zs 1 (bValA71 (B.nd u2 s2 d2)) hlt with hp | hp
            · refine ⟨0, ?_⟩
              rw [lt_eq_ltS, hplug 0, hR, hRc, hz0, ltS_append_left71 _ hatP]
              exact ltS_lvl83 p 1 ζ _ zs [] hp
            · obtain ⟨hpv, hζ⟩ := hp
              subst hpv
              obtain ⟨ξ, hξm, hξv⟩ := mem_toL_bValA71_83 η hlv 1 ζ
                (by rw [hR, hRc, hz0]; exact List.mem_append.mpr (Or.inr (List.Mem.head _)))
              have hξn : (1, ξ) ∈ nodes72 η := toL_sub_nodes72 η (1, ξ) hξm
              have hξsz : sizeB ξ < k := by
                have := sizeB_mem72 η (1, ξ) hξm
                show sizeB ((1, ξ) : Nat × B).2 < k
                omega
              have hξlv : lvlLe 1 ξ = true := (lvlL72_of_lvlLe η hlv (1, ξ) hξm).2
              have hξsub : ∀ q ∈ nodes72 ξ, BT.lt (bValA71 q.2) (bValA71 c) = true :=
                fun q hq => hsub q (nodes72_trans83 η (1, ξ) hξn q hq)
              obtain ⟨m, hm⟩ := ih ξ hξsz hξlv hξsub _ hch (by rw [← hξv]; exact hζ)
              refine ⟨m, ?_⟩
              rw [lt_eq_ltS, hplug m, hR, hRc, hz0, ltS_append_left71 _ hatP, hξv]
              exact ltS_single83 1 _ _ zs hm
        · refine ⟨0, ?_⟩
          rw [lt_eq_ltS, plugB_nd83 1 Q u2 s2 d2 (iterD 0 c 0),
            toL_bValA71_nd83 1 Q _ (lvlLe_plugB _ 1 _ he
              (lvlLe_iterD 0 0 c 1 (Nat.zero_le 1) hc.2.1)), hind]
          rw [hind] at hlt
          exact hlt

end

/-! ### §83.5 `repNode` の枝の底 — 頭は動かない、伸びるのは長さ

段 0 の葉の枝では列の頭が `ψ_v(P)` で固定される。だから「頭で追い抜く」ことはできず、
挑戦者を捕まえるのは**成分の個数**である。挑戦者の尻尾が頭で押さえられているのが
`nonIncr`、すなわち §72 の `descOK_map72` で、`x < y ⊕ 1 → x ≤ y` (`lt_succ_le83`) が
残りの半分。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- 引数が真に小さければ、その先の成分によらず小さい。 -/
theorem ltS_arg83 (p : Nat) (z T : BT) (rest ys : List BT) (h : BT.lt z T = true) :
    ltS (BT.D p z :: rest) (BT.D p T :: ys) = true := by
  have hne : ¬ ((z == T) = true) := by
    intro hcc
    rw [bt_eq_of_beq71 z T hcc, lt_irrefl74] at h
    exact Bool.noConfusion h
  rw [ltS_cons p z rest p T ys, if_neg (Nat.lt_irrefl p), if_neg (Nat.lt_irrefl p),
    if_neg hne, ← lt_eq_ltS]
  exact h

/-- `BT.le` は推移的。 -/
theorem le_trans83 {a b c : BT} (h1 : BT.le a b = true) (h2 : BT.le b c = true) :
    BT.le a c = true := by
  have h1' : ((a == b) || BT.lt a b) = true := h1
  have h2' : ((b == c) || BT.lt b c) = true := h2
  show ((a == c) || BT.lt a c) = true
  rcases (Bool.or_eq_true _ _).mp h1' with e1 | e1
  · rw [bt_eq_of_beq71 a b e1]; exact h2
  · rcases (Bool.or_eq_true _ _).mp h2' with e2 | e2
    · rw [← bt_eq_of_beq71 b c e2, e1, Bool.or_true]
    · rw [lt_trans83 e1 e2, Bool.or_true]

/-- 降べきの列は尻尾を落としても降べき。 -/
theorem descOK_tail83 (x : BT) : ∀ (l : List BT), descOK72 (x :: l) = true →
    descOK72 l = true
  | [], _ => rfl
  | y :: r, h => ((Bool.and_eq_true _ _).mp h).2

theorem descOK_suffix83 : ∀ (a b : List BT), descOK72 (a ++ b) = true → descOK72 b = true
  | [], _, h => h
  | x :: a', b, h => descOK_suffix83 a' b (descOK_tail83 x (a' ++ b) h)

/-- 降べきの列では頭がすべてを押さえる。 -/
theorem descOK_head83 : ∀ (l : List BT) (x : BT), descOK72 (x :: l) = true →
    ∀ y ∈ l, BT.le y x = true := by
  intro l
  induction l with
  | nil => intro _ _ y hy; cases hy
  | cons y0 l' ih =>
    intro x h y hy
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
    rcases List.mem_cons.mp hy with hy | hy
    · rw [hy]; exact h1
    · exact le_trans83 (ih y0 h2 y hy) h1

/-- `ψ_u(P)` の並びの成分列。 -/
theorem replicate_snoc83 (X : BT) : ∀ n : Nat,
    List.replicate n X ++ [X] = List.replicate (n + 1) X
  | 0 => rfl
  | k + 1 => by
      show X :: (List.replicate k X ++ [X]) = X :: List.replicate (k + 1) X
      rw [replicate_snoc83 X k]

theorem toL_repNode83 (u : Nat) (P : B) (hP : lvlLe 1 P = true) : ∀ n : Nat,
    (bValA71 (repNode u P n)).toL = List.replicate (n + 1) (BT.D u (bValA71 P))
  | 0 => by
      show (bValA71 (B.nd u B.nil P)).toL = _
      rw [toL_bValA71_nd83 u .nil P hP]
      rfl
  | k + 1 => by
      show (bValA71 (B.nd u (repNode u P k) P)).toL = _
      rw [toL_bValA71_nd83 u (repNode u P k) P hP, toL_repNode83 u P hP k,
        replicate_snoc83 (BT.D u (bValA71 P)) (k + 1)]

/-- **頭で押さえられた列は、十分長い並びに追い越される。** -/
theorem ltS_replicate83 : ∀ (l : List BT) (u : Nat) (A : BT) (n : Nat), Atoms l →
    (∀ y ∈ l, BT.le y (BT.D u A) = true) → l.length < n →
    ltS l (List.replicate n (BT.D u A)) = true := by
  intro l
  induction l with
  | nil =>
    intro u A n _ _ hn
    cases n with
    | zero => exact absurd hn (Nat.not_lt_zero _)
    | succ m =>
      show ltS [] (BT.D u A :: List.replicate m (BT.D u A)) = true
      exact ltS_nil_cons _ _
  | cons y0 l' ih =>
    intro u A n hat hle hn
    obtain ⟨q, b, rfl⟩ := hat y0 (List.Mem.head _)
    cases n with
    | zero => exact absurd hn (Nat.not_lt_zero _)
    | succ m =>
      show ltS (BT.D q b :: l') (BT.D u A :: List.replicate m (BT.D u A)) = true
      have h := hle (BT.D q b) (List.Mem.head _)
      have h' : ((BT.D q b == BT.D u A) || BT.lt (BT.D q b) (BT.D u A)) = true := h
      rcases (Bool.or_eq_true _ _).mp h' with e | e
      · have he : BT.D q b = BT.D u A := bt_eq_of_beq71 _ _ e
        have hq : q = u := by injection he
        have hb : b = A := by injection he
        subst hq; subst hb
        rw [ltS_cons q b l' q b (List.replicate m (BT.D q b)),
          if_neg (Nat.lt_irrefl q), if_neg (Nat.lt_irrefl q), if_pos (bt_beq_self71 b)]
        refine ih q b m (fun z hz => hat z (List.Mem.tail _ hz))
          (fun z hz => hle z (List.Mem.tail _ hz)) ?_
        have : (BT.D q b :: l').length = l'.length + 1 := rfl
        omega
      · rw [lt_eq_ltS] at e
        rcases ltS_cons_single83 q b [] u A e with h1 | h1
        · exact ltS_lvl83 q u b A l' _ h1
        · obtain ⟨hqu, hba⟩ := h1
          subst hqu
          exact ltS_arg83 q b A l' _ hba

/-- **`x < y ⊕ 1` なら `x ≤ y`。** 部分領域の値の上で。 -/
theorem lt_succ_le83 (z P : B)
    (h : BT.lt (bValA71 z) (bValA71 (.nd 0 P .nil)) = true) :
    bValA71 z = bValA71 P ∨ BT.lt (bValA71 z) (bValA71 P) = true := by
  rw [lt_eq_ltS, toL_bValA71_nd83 0 P .nil rfl] at h
  rcases splitP83 (bValA71 P).toL (bValA71 z).toL (atoms_bValA71_83 P)
      (atoms_bValA71_83 z) with ⟨R, hR⟩ | hind
  · rw [hR, ltS_append_left71 _ (atoms_bValA71_83 P)] at h
    cases hRc : R with
    | nil =>
      refine Or.inl ?_
      have he : (bValA71 z).toL = (bValA71 P).toL := by
        rw [hR, hRc, List.append_nil]
      rw [← show BT.ofL (bValA71 z).toL = bValA71 z from nfSum_bValA7174 z,
        ← show BT.ofL (bValA71 P).toL = bValA71 P from nfSum_bValA7174 P, he]
    | cons z0 zs =>
      have hatR : Atoms R := by
        intro w hw
        exact atoms_bValA71_83 z w (by rw [hR]; exact List.mem_append.mpr (Or.inr hw))
      obtain ⟨p, ζ, hz0⟩ := hatR z0 (by rw [hRc]; exact List.Mem.head _)
      rw [hRc, hz0] at h
      rcases ltS_cons_single83 p ζ zs 0 (bValA71 B.nil) h with h1 | h1
      · exact absurd h1 (Nat.not_lt_zero _)
      · exact absurd h1.2 (by
          rw [lt_eq_ltS, show (bValA71 B.nil).toL = [] from rfl, ltS_right_nil83]
          exact fun hcc => Bool.noConfusion hcc)
  · refine Or.inr ?_
    rw [lt_eq_ltS, ← hind [BT.D 0 (bValA71 B.nil)]]
    exact h

/-- **§83.5 の主定理。** 最後の加数が `ψ₀(0)` の枝の底。 -/
theorem repDomBase83 (v : Nat) (r P : B) (hP : lvlLe 1 P = true)
    (η : B) (hη : GS83 η)
    (hlt : BT.lt (bValA71 η) (bValA71 (.nd v r (.nd 0 P .nil))) = true) :
    ∃ n, BT.lt (bValA71 η) (bValA71 (appB r (repNode v P n))) = true := by
  have hatP : Atoms (bValA71 r).toL := atoms_bValA71_83 r
  have hatL : Atoms (bValA71 η).toL := atoms_bValA71_83 η
  have hlvc : lvlLe 1 (B.nd 0 P .nil) = true :=
    (lvlLe_nd_iff 1 0 P .nil).mpr ⟨Nat.zero_le 1, hP, rfl⟩
  rw [lt_eq_ltS, toL_bValA71_nd83 v r _ hlvc] at hlt
  have htgt : ∀ n : Nat, (bValA71 (appB r (repNode v P n))).toL
      = (bValA71 r).toL ++ List.replicate (n + 1) (BT.D v (bValA71 P)) := by
    intro n
    rw [toL_bValA71_appB71 (repNode v P n) r, toL_repNode83 v P hP n]
  rcases splitP83 (bValA71 r).toL (bValA71 η).toL hatP hatL with ⟨R, hR⟩ | hind
  · rw [hR, ltS_append_left71 _ hatP] at hlt
    have hatR : Atoms R := by
      intro w hw
      exact hatL w (by rw [hR]; exact List.mem_append.mpr (Or.inr hw))
    cases hRc : R with
    | nil =>
      refine ⟨0, ?_⟩
      rw [lt_eq_ltS, htgt 0, hR, hRc, ltS_append_left71 _ hatP]
      exact ltS_nil_cons _ _
    | cons z0 zs =>
      obtain ⟨p, ζ, hz0⟩ := hatR z0 (by rw [hRc]; exact List.Mem.head _)
      rw [hRc, hz0] at hlt
      rcases ltS_cons_single83 p ζ zs v (bValA71 (B.nd 0 P .nil)) hlt with h1 | h1
      · refine ⟨0, ?_⟩
        rw [lt_eq_ltS, htgt 0, hR, hRc, hz0, ltS_append_left71 _ hatP]
        exact ltS_lvl83 p v ζ _ zs _ h1
      · obtain ⟨hpv, hζ⟩ := h1
        subst hpv
        obtain ⟨ξ, hξm, hξv⟩ := mem_toL_bValA71_83 η hη.2.2 p ζ
          (by rw [hR, hRc, hz0]; exact List.mem_append.mpr (Or.inr (List.Mem.head _)))
        subst hξv
        rcases lt_succ_le83 ξ P hζ with he | he
        · -- 頭が一致する。長さで追い越す。
          refine ⟨zs.length + 1, ?_⟩
          rw [lt_eq_ltS, htgt (zs.length + 1), hR, hRc, hz0, ltS_append_left71 _ hatP, he,
            show List.replicate (zs.length + 1 + 1) (BT.D p (bValA71 P))
              = BT.D p (bValA71 P) :: List.replicate (zs.length + 1) (BT.D p (bValA71 P)) from rfl,
            ltS_cons p (bValA71 P) zs p (bValA71 P) _, if_neg (Nat.lt_irrefl p),
            if_neg (Nat.lt_irrefl p), if_pos (bt_beq_self71 (bValA71 P))]
          have hdesc : descOK72 (BT.D p (bValA71 P) :: zs) = true := by
            have hd := descOK_bValA71_83 η hη
            rw [hR, hRc, hz0, he] at hd
            exact descOK_suffix83 _ _ hd
          refine ltS_replicate83 zs p (bValA71 P) (zs.length + 1)
            (fun w hw => hatR w (by rw [hRc, hz0]; exact List.Mem.tail _ hw))
            (descOK_head83 zs _ hdesc) (Nat.lt_succ_self _)
        · refine ⟨0, ?_⟩
          rw [lt_eq_ltS, htgt 0, hR, hRc, hz0, ltS_append_left71 _ hatP]
          exact ltS_arg83 p _ _ zs _ he
  · refine ⟨0, ?_⟩
    rw [lt_eq_ltS, htgt 0, hind]
    rw [hind] at hlt
    exact hlt

end

/-! ### §83.6 二つの再帰 — §71.7 の減少・増加の双子

`fsB` の枝は §71.7 と同じ二つ。前置きで割って最後の加数に降りる操作は両方に共通なので
`descend83` にまとめる — そこで挑戦者は「成分の引数」に置き換わり、一段小さくなる。
不変量 `hasLowAnc w c = true ∨ v < w` も §71.7 のまま。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- **一段降りる。** 前置きで割り、成分の引数を新しい挑戦者にする。 -/
theorem descend83 (v : Nat) (r c : B) (hc : lvlLe 1 c = true)
    (g : Nat → B) (hg : ∀ n, lvlLe 1 (g n) = true)
    (η : B) (hlv : lvlLe 1 η = true)
    (hlt : BT.lt (bValA71 η) (bValA71 (.nd v r c)) = true)
    (HIH : ∀ ξ : B, (v, ξ) ∈ toL η → BT.lt (bValA71 ξ) (bValA71 c) = true →
       ∃ n, BT.lt (bValA71 ξ) (bValA71 (g n)) = true) :
    ∃ n, BT.lt (bValA71 η) (bValA71 (.nd v r (g n))) = true := by
  have hatP : Atoms (bValA71 r).toL := atoms_bValA71_83 r
  have hatL : Atoms (bValA71 η).toL := atoms_bValA71_83 η
  have htgt : ∀ n, (bValA71 (B.nd v r (g n))).toL
      = (bValA71 r).toL ++ [BT.D v (bValA71 (g n))] :=
    fun n => toL_bValA71_nd83 v r (g n) (hg n)
  rw [lt_eq_ltS, toL_bValA71_nd83 v r c hc] at hlt
  rcases splitP83 (bValA71 r).toL (bValA71 η).toL hatP hatL with ⟨R, hR⟩ | hind
  · rw [hR, ltS_append_left71 _ hatP] at hlt
    have hatR : Atoms R := by
      intro w hw
      exact hatL w (by rw [hR]; exact List.mem_append.mpr (Or.inr hw))
    cases hRc : R with
    | nil =>
      refine ⟨0, ?_⟩
      rw [lt_eq_ltS, htgt 0, hR, hRc, ltS_append_left71 _ hatP]
      exact ltS_nil_cons _ _
    | cons z0 zs =>
      obtain ⟨p, ζ, hz0⟩ := hatR z0 (by rw [hRc]; exact List.Mem.head _)
      rw [hRc, hz0] at hlt
      rcases ltS_cons_single83 p ζ zs v (bValA71 c) hlt with h1 | h1
      · refine ⟨0, ?_⟩
        rw [lt_eq_ltS, htgt 0, hR, hRc, hz0, ltS_append_left71 _ hatP]
        exact ltS_lvl83 p v ζ _ zs _ h1
      · obtain ⟨hpv, hζ⟩ := h1
        subst hpv
        obtain ⟨ξ, hξm, hξv⟩ := mem_toL_bValA71_83 η hlv p ζ
          (by rw [hR, hRc, hz0]; exact List.mem_append.mpr (Or.inr (List.Mem.head _)))
        subst hξv
        obtain ⟨n, hn⟩ := HIH ξ hξm hζ
        refine ⟨n, ?_⟩
        rw [lt_eq_ltS, htgt n, hR, hRc, hz0, ltS_append_left71 _ hatP]
        exact ltS_arg83 p _ _ zs _ hn
  · refine ⟨0, ?_⟩
    rw [lt_eq_ltS, htgt 0, hind]
    rw [hind] at hlt
    exact hlt

/-- **段 0 の葉の枝の支配。** §71.7 の `repB_dec_inc71` の双子。 -/
theorem repDom83 : ∀ (c : B), c ≠ .nil → lastLvl c = 0 → ∀ (v : Nat) (r : B),
    lvlLe 1 (.nd v r c) = true → ∀ (η : B), GS83 η →
    BT.lt (bValA71 η) (bValA71 (.nd v r c)) = true →
    ∃ n, BT.lt (bValA71 η) (bValA71 (repB (.nd v r c) n)) = true := by
  intro c
  induction c with
  | nil => intro h; exact absurd rfl h
  | nd u P d _ ihd =>
    intro _ hll v r hlv η hη hlt
    obtain ⟨_, _, hc⟩ := (lvlLe_nd_iff 1 v r (.nd u P d)).mp hlv
    obtain ⟨_, hP, _⟩ := (lvlLe_nd_iff 1 u P d).mp hc
    cases d with
    | nil =>
      have hu0 : u = 0 := hll
      subst hu0
      obtain ⟨n, hn⟩ := repDomBase83 v r P hP η hη hlt
      refine ⟨n, ?_⟩
      rw [repB_base71 v r P n]
      exact hn
    | nd u2 s2 d2 =>
      have hdne : (B.nd u2 s2 d2) ≠ .nil := by intro hcc; exact B.noConfusion hcc
      have hlld : lastLvl (B.nd u2 s2 d2) = 0 := by
        rw [← lastLvl_nd71 u P _ hdne]; exact hll
      obtain ⟨n, hn⟩ := descend83 v r (B.nd u P (B.nd u2 s2 d2)) hc
        (fun n => repB (B.nd u P (B.nd u2 s2 d2)) n) (fun n => lvlLe_repB _ 1 n hc)
        η hη.2.2 hlt
        (fun ξ hξm hξlt => ihd hdne hlld u P hc ξ (gs83_mem83 η hη (v, ξ) hξm).1 hξlt)
      refine ⟨n, ?_⟩
      rw [repB_deep71 v r u P _ n hdne]
      exact hn

/-- **段 `w ≥ 1` の葉の枝の支配。** §71.7 の `rwB_dec_inc71` の双子。底では §83.4。 -/
theorem rwDom83 : ∀ (c : B), c ≠ .nil → ∀ (w : Nat), lastLvl c = w →
    ∀ (v : Nat) (r : B), (hasLowAnc w c = true ∨ v < w) → lvlLe 1 (.nd v r c) = true →
    ∀ (η : B), GS83 η → BT.lt (bValA71 η) (bValA71 (.nd v r c)) = true →
    ∃ n, BT.lt (bValA71 η) (bValA71 (rwB w n (.nd v r c))) = true := by
  intro c
  induction c with
  | nil => intro h; exact absurd rfl h
  | nd u P d _ ihd =>
    intro _ w hll v r hdis hlv η hη hlt
    obtain ⟨hv1, _, hc⟩ := (lvlLe_nd_iff 1 v r (.nd u P d)).mp hlv
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
      obtain ⟨n, hn⟩ := descend83 v r (B.nd u P d) hc
        (fun n => rwB w n (B.nd u P d)) (fun n => lvlLe_rwB _ w n 1 hc)
        η hη.2.2 hlt
        (fun ξ hξm hξlt => ihd hdne w hll2 u P hdis2 hc ξ (gs83_mem83 η hη (v, ξ) hξm).1 hξlt)
      refine ⟨n, ?_⟩
      rw [rwB_nd71 w n v r u P d, if_pos hla]
      exact hn
    · have hvw : v < w := by
        rcases hdis with h | h
        · exact absurd h hla
        · exact h
      have hlow : hasLowAnc w (.nd u P d) = false := by
        cases hcc : hasLowAnc w (.nd u P d) with
        | false => rfl
        | true => exact absurd hcc hla
      have hwle : w ≤ 1 := by rw [← hll]; exact lastLvl_le83 _ 1 hc
      have hv0 : v = 0 := by omega
      have hw1 : w = 1 := by omega
      subst hv0; subst hw1
      have hchain : Chain83 (B.nd u P d) := ⟨hcne, hc, hll, hlow⟩
      obtain ⟨m, hm⟩ := descend83 0 r (B.nd u P d) hc
        (fun m => plugB (B.nd u P d) (iterD 0 (B.nd u P d) m))
        (fun m => lvlLe_plugB _ 1 _ hc (lvlLe_iterD m 0 _ 1 (Nat.zero_le 1) hc))
        η hη.2.2 hlt
        (fun ξ hξm hξlt => by
          have hgs := gs83_mem83 η hη (0, ξ) hξm
          have hsub : ∀ q ∈ nodes72 ξ, BT.lt (bValA71 q.2) (bValA71 (B.nd u P d)) = true :=
            fun q hq => lt_trans83 (subLt83 ξ hgs.1 hgs.2 q hq) hξlt
          exact iterDom83 _ hchain (sizeB ξ + 1) ξ (Nat.lt_succ_self _) hgs.1.2.2 hsub
            _ hchain hξlt)
      refine ⟨m + 1, ?_⟩
      rw [rwB_nd71 1 (m + 1) 0 r u P d, if_neg hla, if_pos hvw]
      exact hm

end

/-! ### §83.7 組み立て — `BCofIn71` は定理である

§71.1 が「基本列は前置きに触らない」を言い、`fsB` の枝は §71.7 と同じ二つなので、
支配は §83.6 の二つで尽きる。強い形 (`mainDom83`) から求められた形へは §74.4 の
反対称律ひとつ。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- **強い形。** 極限の添字の基本列は、下にあるどの部分領域の値も**真に追い越す**。 -/
theorem mainDom83 (t : B) (ht : stdB1 t = true) (hk : kindB t = BMS.Kind.lim)
    (η : B) (hη : GS83 η) (hlt : BT.lt (bValA71 η) (bValA71 t) = true) :
    ∃ n, BT.lt (bValA71 η) (bValA71 (fsB t n)) = true := by
  obtain ⟨r, a, ha, rfl⟩ := kindB_lim_std t (stdB_of_stdB1 t ht) hk
  have hlv : lvlLe 1 (B.nd 0 r a) = true := lvlLe1_of_stdB1 _ ht
  by_cases hz : (lastLvl a == 0) = true
  · obtain ⟨n, hn⟩ := repDom83 a ha (eq_of_beq hz) 0 r hlv η hη hlt
    refine ⟨n, ?_⟩
    rw [fsB_ne_nil71 0 r a n ha, if_pos hz]
    exact hn
  · obtain ⟨n, hn⟩ := rwDom83 a ha (lastLvl a) rfl 0 r (Or.inr (lastLvl_pos71 a hz)) hlv η hη hlt
    refine ⟨n, ?_⟩
    rw [fsB_ne_nil71 0 r a n ha, if_neg hz]
    exact hn

/-- **§83 の主定理。`BCofIn71` は定理である。** 仮説なし。 -/
theorem bCofIn71_thm : BCofIn71 := by
  intro t ht hk u hu hlt
  obtain ⟨n, hn⟩ := mainDom83 t ht hk u (gs83_of_std83 u hu) hlt
  exact ⟨n, lt_asymm74 hn⟩

/-- §71.4 の内側の共終性。橋の逆向きだけになる。 -/
theorem cofInS1_83 (Hp : PsiIdxOKStd172) (HV : VOfLtA71') : CofInS1 :=
  cofInS1_172_76 Hp HV bCofIn71_thm

/-- 同じものを §71.4 の絞らない形の仮説で。 -/
theorem cofInS1_of71_83 (Hp : PsiIdxOKStd) (Hr : RegionStd) (HV : VOfLtA71') : CofInS1 :=
  cofInS1_of71 Hp Hr HV bCofIn71_thm

/-- **共終性に残るのは `CofDenseS1` だけ。** -/
theorem limCofS1_83 (Hp : PsiIdxOKStd172) (HV : VOfLtA71') (HD : CofDenseS1) : LimCofS1 :=
  limCofS1_172_76 Hp HD (cofInS1_83 Hp HV)

/-- **§83 の最終形。326 行目の証明書に残る仮説は 3 つ** —
    `PsiIdxOKStd172` (§72 の門)、`DictLtA74` (`dict` の順序保存)、`CofDenseS1` (密度)。
    §76.5b の最良は 4 つで、4 つめが `BCofIn71` だった。 -/
theorem certIn_t326_83 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HCD : CofDenseS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_dict76 Hp H2 HCD bCofIn71_thm hacc

/-- 同じものを §73 の一歩ぶんの門で。 -/
theorem certIn_t326_step83 (Hs : PsiIdxStep073) (H2 : DictLtA74) (HCD : CofDenseS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_step76 Hs H2 HCD bCofIn71_thm hacc

/-- **逆向き。** `LimCofS1` が言えれば `CofDenseS1` はただで出る — 証人に `fsB t n` を
    取ればよく、`LimDecS1` がそれを `vOf t` の下に置く。 -/
theorem cofDenseS1_of_limCofS1_83 (HL : LimCofS1) (HD : LimDecS1) : CofDenseS1 := by
  intro t ht hk s hs hlt
  obtain ⟨n, hn⟩ := HL t ht hk s hs hlt
  exact ⟨fsB t n, stdB1_fsB t ht n, hn, HD t ht hk n⟩

/-- **§71.4 の分割はもう縮まない。** `BCofIn71` が定理になったので、残る半分は
    共終性そのものと**同値**である。橋 (`VOfLtA71`) の下で。 -/
theorem cofDenseS1_iff_limCofS1_83 (Hp : PsiIdxOKStd172) (HV : VOfLtA71) :
    CofDenseS1 ↔ LimCofS1 :=
  ⟨fun H => limCofS1_83 Hp (vOfLtA71'_76 Hp HV) H,
   fun H => cofDenseS1_of_limCofS1_83 H (limDecS1_of_bridge71 HV)⟩

/-- 同じことを `dict` の順序保存から。 -/
theorem cofDenseS1_iff_dict83 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) :
    CofDenseS1 ↔ LimCofS1 :=
  cofDenseS1_iff_limCofS1_83 Hp (vOfLtA71_of_dictLt76 Hp H2)

end

/-! ### §83.8 `visOK` は外せない — `ψ₀(Ω)` が反例

§83.4 の `iterDom83` から `visOK 0` を落とすと**偽になる**。`sbad83 = ψ₀(Ω)` は
`nonIncr`・`stdIn`・`lvlLe 1` をすべて満たし (`GS83`)、`Ω` より真に下にあるが、`ψ₀` の塔の
どの段にも届かない — それが上限だからである。これは §69 が使った形そのもので、§70.3 の
`sbad_not_witness` の Buchholz 側の相方である。`visOK 0 sbad83 sbad83 = false` は
`cmpS` が整礎再帰で書かれていて `rfl` では簡約しないので、§83.9 の `#guard` で押さえる。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- `Ω = ψ₁(0)`。 -/
def om83 : B := .nd 1 .nil .nil

/-- `ψ₀(Ω)` — 塔の上限そのもの。 -/
def sbad83 : B := .nd 0 .nil om83

theorem plugB_om83 (Y : B) : plugB om83 Y = Y := appB_nil Y

theorem chain83_om83 : Chain83 om83 :=
  ⟨by intro hc; exact B.noConfusion hc, rfl, rfl, rfl⟩

theorem gs83_sbad83 : GS83 sbad83 := ⟨rfl, rfl, rfl⟩

/-- `ψ₀(Ω)` は `Ω` より下。 -/
theorem lt_sbad83_om83 : BT.lt (bValA71 sbad83) (bValA71 om83) = true := rfl

/-- 塔の各段は `ψ₀` の一節で、その引数は `Ω` を含まない。 -/
theorem tower_shape83 : ∀ n : Nat, ∃ Z, bValA71 (iterD 0 om83 n) = BT.D 0 Z
    ∧ ltS [BT.D 1 BT.zero] Z.toL = false
  | 0 => ⟨bArg 0 (plugB om83 .nil), rfl, by
      rw [plugB_om83]
      show ltS [BT.D 1 BT.zero] (BT.zero).toL = false
      exact ltS_right_nil83 _⟩
  | k + 1 => by
      obtain ⟨Z, hZ, _⟩ := tower_shape83 k
      refine ⟨bArg 0 (plugB om83 (iterD 0 om83 k)), rfl, ?_⟩
      rw [plugB_om83, bArg_eq_bValA71_71 _ 0 (lvlLe_iterD k 0 om83 1 (Nat.zero_le 1) rfl), hZ]
      show ltS [BT.D 1 BT.zero] [BT.D 0 Z] = false
      rw [ltS_cons 1 BT.zero [] 0 Z [], if_neg (by omega), if_pos (by omega)]

/-- **反例。** どの段も `ψ₀(Ω)` に届かない。 -/
theorem sbad83_not_dominated : ∀ n : Nat,
    BT.lt (bValA71 sbad83) (bValA71 (plugB om83 (iterD 0 om83 n))) = false := by
  intro n
  rw [plugB_om83]
  obtain ⟨Z, hZ, hZlt⟩ := tower_shape83 n
  rw [hZ, lt_eq_ltS]
  show ltS [BT.D 0 (BT.D 1 BT.zero)] [BT.D 0 Z] = false
  rw [ltS_cons 0 (BT.D 1 BT.zero) [] 0 Z []]
  rw [if_neg (Nat.lt_irrefl 0), if_neg (Nat.lt_irrefl 0)]
  by_cases h : (BT.D 1 BT.zero == Z) = true
  · rw [if_pos h]; exact ltS_nil_nil
  · rw [if_neg h]; exact hZlt

/-- **§83.8 の主定理。`GS83` だけでは §83.4 は成り立たない。** -/
theorem not_iterDom_without_visOK83 :
    ¬ (∀ (η : B), GS83 η → ∀ (c : B), Chain83 c → BT.lt (bValA71 η) (bValA71 c) = true →
       ∃ n, BT.lt (bValA71 η) (bValA71 (plugB c (iterD 0 c n))) = true) := by
  intro H
  obtain ⟨n, hn⟩ := H sbad83 gs83_sbad83 om83 chain83_om83 lt_sbad83_om83
  rw [sbad83_not_dominated n] at hn
  exact Bool.noConfusion hn

end

/-! ### §83.9 測定 (凍結)

母集団の作り方を先に書く。**主定理は定理なので、以下は根拠ではなく受領である。**

    subP n = (popNFB 2 n).filter stdB1      節は 0 … n-1 個、段は 0 と 1
    pairs83 l = { (t, u) | t ∈ l, kindB t = lim, u ∈ l, bValA71 u < bValA71 t }

**核は `subP 4` (13 個、極限 8 個、対 63 個)。**深さは節 3 個ぶん、幅は `fsB` の二つの枝の
両方 — `repB` の枝が 34 対、`rwB` の枝 (崩れ、§83.4 が支える側) が 29 対。`subP 5`
(45 個、799 対) は同じ掃きを一行で広げたもの。

**そこに一つ族を足す。** それが要点である。`subP` の中では必要な添字は `n ≤ 3` で収まり、
「定数で足りる」ように見えてしまう。`t = ψ₀(Ω) = sbad83` と挑戦者 `tow83 k = ψ₀ᵏ(0)` の
族では必要な添字はちょうど `k`、すなわち**挑戦者の節の個数そのもの**で、上に有界でない。
これが「項についての帰納法ではなく挑戦者の大きさについての帰納法」を強いる形であり、
§83.4 の設計はここから来ている。10 個。

**負の結果 (24 個)。** `sbad83` は `GS83` を満たすが `visOK 0` を満たさず、塔のどの段にも
届かない — §83.8 の定理の受領。`visOK 0 sbad83 sbad83 = false` は `cmpS` が整礎再帰なので
定理にできず、ここで測る。

**§69 の反例は覆っていない。** `tdiag = (0,0)(1,1)(2,2)` は段 2 の節を持つので `stdB1` では
なく、§83 の主定理の仮説を満たさない (§70.3 の `not_stdB1_tdiag` と同じこと)。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

def tow83 : Nat → B
  | 0 => .nil
  | k + 1 => .nd 0 .nil (tow83 k)

def limOf83 (l : List B) : List B := l.filter (fun t => kindB t == BMS.Kind.lim)

def leastN83 (t u : B) (K : Nat) : Option Nat :=
  (List.range K).find? (fun n => BT.lt (bValA71 u) (bValA71 (fsB t n)))

def pairs83 (l : List B) : List (B × B) :=
  (limOf83 l).flatMap fun t => l.filterMap fun u =>
    if BT.lt (bValA71 u) (bValA71 t) then some (t, u) else none

/-- `fsB` の第 2 の枝 (`rwB`、崩れ) に落ちる添字か。 -/
def rwBranch83 (t : B) : Bool := match t with
  | .nd _ _ a => !(lastLvl a == 0)
  | _ => false

-- 核の母集団。
#guard (subP 4).length == 13
#guard (limOf83 (subP 4)).length == 8
#guard (pairs83 (subP 4)).length == 63
#guard (pairs83 (subP 4)).all fun p => (leastN83 p.1 p.2 16).isSome
#guard ((pairs83 (subP 4)).map fun p => (leastN83 p.1 p.2 16).getD 99).foldl max 0 == 3
#guard ((pairs83 (subP 4)).filter fun p => (leastN83 p.1 p.2 16).getD 99 ≥ 1).length == 29
-- 二つの枝の幅。
#guard ((pairs83 (subP 4)).filter fun p => rwBranch83 p.1).length == 29
#guard ((pairs83 (subP 4)).filter fun p => !(rwBranch83 p.1)).length == 34
-- `BCofIn71` が求める形そのもの (含意ではなく等式)。
#guard (pairs83 (subP 4)).all fun p =>
  match leastN83 p.1 p.2 16 with
  | none => false
  | some n => BT.lt (bValA71 (fsB p.1 n)) (bValA71 p.2) == false
-- 広い側、一行。
#guard (subP 5).length == 45
#guard (pairs83 (subP 5)).length == 799
#guard (pairs83 (subP 5)).all fun p =>
  match leastN83 p.1 p.2 16 with
  | none => false
  | some n => BT.lt (bValA71 (fsB p.1 n)) (bValA71 p.2) == false

/-! **必要な添字は挑戦者の大きさそのもの。** `subP` の中では `n ≤ 3` に見えるが、
    塔の族では `n = k = sizeB (tow83 k)` で上に有界でない。 -/
#guard stdB1 sbad83 && (kindB sbad83 == BMS.Kind.lim)
#guard (List.range 10).all fun k => stdB1 (tow83 k)
#guard (List.range 10).all fun k => sizeB (tow83 k) == k
#guard (List.range 10).all fun k => leastN83 sbad83 (tow83 k) 24 == some k
-- 定数の添字では足りない。`n = 3` は `k ≤ 3` しか捕まえない。
#guard (List.range 10).all fun k =>
  (BT.lt (bValA71 (tow83 k)) (bValA71 (fsB sbad83 3)) == decide (k ≤ 3))

/-! **負の結果。** `visOK 0` を落とすと §83.4 は偽になる (§83.8 の定理の受領)。 -/
#guard nonIncr sbad83 && stdIn sbad83 && lvlLe 1 sbad83
#guard visOK 0 sbad83 sbad83 == false
#guard BT.lt (bValA71 sbad83) (bValA71 om83)
#guard (List.range 24).all fun n =>
  BT.lt (bValA71 sbad83) (bValA71 (plugB om83 (iterD 0 om83 n))) == false

/-! **§69 の反例は覆っていない。** 段 2 の節があるので部分領域の外。 -/
#guard stdB1 tdiag == false
#guard lvlLe 1 tdiag == false
#guard kindB tdiag == BMS.Kind.lim

end

/-! ### §83.10 公理 -/

/-! ## §84 THE `K`-GATE RELOCALISED — WHAT ESCAPES `Δ` IS WHAT THE HEAD ALREADY PUT IN THE INDEX

§82 refuted §78's and §80's residue and diagnosed it exactly: the `ψ₀` inside a TAIL summand
can have the HEAD as its argument, so its collapse index is fixed by the head while the `Δ`
of the tail's own scan step is fixed by the tail.  Buchholz asks *argument < whole sum*;
Rathjen asks *index < Δ*.  §84 takes the diagnosis at its word and moves the comparison off
`Δ`.

**FIRST, ONE MORE THING IS FALSE.**  `not_localStd75` — §75's own remaining hypothesis
`LocalStd75`, the state-free per-pair clause, **is refutable too**, by the same `aBad82`.
§82 refuted `LocalK2_78`, which is STRONGER (`localStd75_of_k2_78` goes that way), so this did
not follow from §82 and is new here.  With it `LocalStdFacts75` and `LocalStdFacts2_75` fall,
and `certIn_t326_local75` joins `certIn_t326_k2_78`, `certIn_t326_big80` and
`certIn_t326_node82` in the vacuous column.  **Every localisation from §73.6 onwards that
compares a `K`-element against `Δ` alone is false.**

**AND THE REPLACEMENT IS TRUE WHERE THEY ARE FALSE.**  `SplitK84` asks, of each element `y`
of `K_{Ω₁} aV ∪ K_{Ω₁} cV` at a firing step,

    y < Δ ⊖ 1        OR        y ≤ i₀   (the index the scan has accumulated so far)

and `ksetStepOK_of_split84` turns it into the gate.  Neither disjunct mentions the sum
`i₀ ⊕ Δ`: the two comparisons are against single objects, which is what "local" can still
mean after §82 showed it cannot mean per-pair.  The left disjunct is §75's clause verbatim —
everything §73–§80 built for it still applies.  The right disjunct is a statement about the
PREFIX of the sum, which is exactly where Buchholz's `G(a,0) < a` lives.

WHAT IS PROVED, UNCONDITIONALLY.

  §84.1  **THE GATE'S FIRST CONJUNCT IS FREE.**  `KsetStepOK` has two conjuncts — the previous
         index's `K`, and the current pair's `K`.  `scan_idx84` runs `StInv` and `KInv75` along
         the scan and gets the first from the second, so `ksetStepOK_of_idxK84 : IdxK84 → KsetStepOK`
         where `IdxK84` is the second conjunct alone.  `idxK84_of_ksetStepOK` is the converse,
         so the reduction is exact and a `false` from `idxb84` would be a refutation of the
         gate itself.  The hypothesis is handed `StInv p.1` at each entry, which is what lets
         §84.3 convert it pointwise; nothing else about the scan leaks out.

  §84.2  **THE STRONGLY CRITICAL BRANCH ALWAYS ADVANCES THE INDEX.**  Three lemmas, no order
         theory: `wcnf_snd_ne_zero84` (the coefficient of a `wcnf` pair is never `0` — the
         single branch is an `ω`-power, the merging branch is a `⊕` whose right summand is one),
         `ddOf_ne_zero84` (`Δ = W^(aV ⊖ W)·cV ≠ 0`), and `ne_plus_self84` (`v ⊕ d ≠ v` for
         `d ≠ 0`, by filtering both sides of `toList v = filter(toList v) ++ toList d` and
         counting).  Together: `lt_prev_idxOf84 : i₀ < i₀ ⊕ Δ`, the strict form of §75.2's
         `le_prev_idxOf75`.  **This is the whole reason `y ≤ i₀` suffices and not just
         `y < i₀`,** and §84.7 says it is needed at 8 of 893 measured escapes.

  §84.3  **THE SPLIT.**  `idx_of_split84` translates one pair — left disjunct through §75.2's
         `le_sub1dd_idxOf75`, right disjunct through §84.2 — and `ksetStepOK_of_split84`
         feeds it to §84.1's induction.  `split84_of_local75` records that §75's clause is
         the left disjunct on its own, so `SplitK84` is weaker than what §75 asked for.

  §84.4  **THE DECIDERS ARE EXACT.**  `idxb84`/`splitb84` with `idxK84_of_b84`,
         `b84_of_idxK84` (both directions for the state-aware clause) and `splitK84_of_b84`.

  §84.5  **THE REFUTATION AND THE RESCUE, SIDE BY SIDE.**  `b73_of_localK75` is the converse of
         §75.3's `localK75_of_b`, so `localOKb73 = false` is a refutation; `not_localStd75`
         uses it on `aBad82`.  `split84_saves_aBad82` freezes all four verdicts on the same
         term: §75's clause `false`, §78's clause `false`, `splitb84` `true`, `idxb84` `true`.

  §84.6  **THE ASSEMBLY.**  `SplitStd84` (and `IdxStd84`) → `PsiIdxStep073` → row 326.
         `idxStd84_of_step073` is the converse for the state-aware form, so `IdxStd84` and
         §73's gate are the same statement; `SplitStd84` is the sufficient condition proper.

WHAT IS **NOT** CLAIMED.  `SplitStd84` and `IdxStd84` are NOT proved.  `IdxStd84` is EQUAL in
strength to `PsiIdxStep073` — it is a repackaging that discharges one conjunct, not progress on
the gate.  The progress claimed is `SplitStd84`, and it is progress in SHAPE only: **no
measured term separates `splitb84` from `idxb84`**, so the extra strength is not visible
anywhere in the corpora and could in principle be vacuous.  §82's own repair `LocalK2BigC_82`
is not resurrected here — §84.7 measures again that it dies on row 326.  `LocalK2Snd_78`,
`DictHeadLt77`, `CofDenseS1`, `BCofIn71` are untouched.  The right disjunct is the open
direction: it asks that a `ψ₀`-argument's collapse index be at most what the EARLIER summands
already contributed, which is where `G(a,0) < a` has to be spent, and §84 does not spend it.

WHAT THE MEASUREMENT SAYS (§84.7 gives the construction).  §82.8's four groups are built by
capping and summing uniformly, so no component of one of their terms ever mentions another.
§84's population is built the other way round: `ψ₀`'s argument is made to BE another summand.

  * **§75's clause falls on 3 of the 53 qualifying constructed terms** (all in the family
    `h ⊕ ψ₁^m(ψ₀ h)`, of which `aBad82` is the smallest) and on **690 of §82.8's 5949
    `refFam82` terms**.
  * **`splitb84` falls on none of them** — 0 failures on the 53, 0 on all 5949, 0 on the 690
    refuters.  `idxb84` and `stepOKb` likewise.
  * **The escapes are covered by the right disjunct with room to spare, but not everywhere.**
    893 escaping elements over the 690 refuters: 885 satisfy `y < i₀` strictly, **8 satisfy only
    `y = i₀`** — and those 8 are exactly what §84.2's `Δ ≠ 0` is for.  All 3 escapes in the
    constructed population are of the equality kind.
  * **Row 326 and its whole fundamental sequence pass, and §82's repair does not.**  Over the
    41 indices of `regPairs72 ([t326] ++ exp72)`: `splitb84`, `idxb84`, `stepOKb` and even
    `localOKb73` fail 0 times, while the component-standardness condition of `LocalK2BigC_82`
    fails **30** times — and on `bVal t326` itself.  Over the sub-region
    `regPairs72 (sub72 8)` (1908 indices) the same: 0 failures for `splitb84`, 319 for
    component standardness.
-/

/-! ### §84.1 状態つきの条項 — 門の第一連言は只で来る -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **状態つきの `K` 条項。** `KsetStepOK` の**第二**連言だけ — 今の対の材料の `K` が、
    実際に吐かれる指数より下。`Δ` ではなく `idxOf` と比べるのがすべての違い。 -/
def IdxK84 (u : Nat) (x : Term) : Prop :=
  ∀ p ∈ scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1,
    le (reg (u+1)) p.2.1 = true →
      ∀ y, (y ∈ Kset (reg (u+1)) p.2.1 ∨ y ∈ Kset (reg (u+1)) p.2.2) →
        lt y (idxOf (reg (u+1)) p.1 p.2) = true

/-- 状態つきの局所条件から、吐かれた指数についての 2.1(vi) の `K` の連言。
    §75.2 の `kall_idxOf75` と違い `le_sub1dd_idxOf75` を通らない。 -/
private theorem kall_idx84 {u : Nat} {s : Option Term × Option Term} {ac : Term × Term}
    (hs : StInv s) (hk : KInv75 u s)
    (h1 : inT ac.1 = true) (h2 : lt ac.1 M = true)
    (h3 : inT ac.2 = true) (h4 : lt ac.2 M = true)
    (hloc : ∀ y, (y ∈ Kset (reg (u+1)) ac.1 ∨ y ∈ Kset (reg (u+1)) ac.2) →
        lt y (idxOf (reg (u+1)) s ac) = true) :
    ∀ y, y ∈ Kset (reg (u+1)) (idxOf (reg (u+1)) s ac) →
      lt y (idxOf (reg (u+1)) s ac) = true := by
  have hw : inT (reg (u+1)) = true := inT_reg (u+1)
  have hlw : lt (reg (u+1)) M = true := ltM_reg (u+1)
  obtain ⟨hidxT, _⟩ := inT_idxOf mulDescInT hw hlw hs h1 h2 h3 h4
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
    exact hloc y (mem_Kset_ddOf75 (mem_Kset_sub1 hy))
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
    · exact hloc y (mem_Kset_ddOf75 h5)

/-- **§84.1 の心臓。** 走査に沿って `StInv` と `KInv75` を回し、状態つきの条項から
    一歩ぶんの**両方**の連言を出す。第一連言 — 直前の指数の `K` — は仮説ではない。 -/
theorem scan_idx84 {u : Nat} :
    ∀ (l : List (Term × Term)) (s : Option Term × Option Term), StInv s → KInv75 u s →
      (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
      (∀ p ∈ scanSt (reg (u+1)) (baseOf u) s l, le (reg (u+1)) p.2.1 = true → StInv p.1 →
          ∀ y, (y ∈ Kset (reg (u+1)) p.2.1 ∨ y ∈ Kset (reg (u+1)) p.2.2) →
            lt y (idxOf (reg (u+1)) p.1 p.2) = true) →
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
    have hmemhead : ((s, ac) : (Option Term × Option Term) × (Term × Term)) ∈
        scanSt (reg (u+1)) (baseOf u) s (ac :: t) :=
      show ((s, ac) : (Option Term × Option Term) × (Term × Term)) ∈
        (s, ac) :: scanSt (reg (u+1)) (baseOf u) (stepF (reg (u+1)) (baseOf u) s ac) t from
        List.Mem.head _
    rcases List.mem_cons.mp (show p ∈ (s, ac) :: scanSt (reg (u+1)) (baseOf u)
        (stepF (reg (u+1)) (baseOf u) s ac) t from hp) with h | h
    · subst h
      refine ⟨?_, hloc _ hmemhead hle hs⟩
      intro i0 hs1 y hy
      obtain ⟨hidxT, _⟩ := inT_idxOf mulDescInT hw hlw hs hac.1 hac.2.1 hac.2.2.1 hac.2.2.2
      have hi0 : inT i0 = true := (hs.1 i0 hs1).1
      have hyi : inT y = true := inT_mem_Kset75 i0 hi0 _ y hy
      exact lt_of_lt_of_le3 (inT_le_fragR y hyi) (inT_le_fragR i0 hi0)
        (inT_le_fragR _ hidxT) (hk i0 hs1 y hy)
        (le_prev_idxOf75 hw hs hs1 hac.1 hac.2.2.1)
    · have hkall : le (reg (u+1)) ac.1 = true →
          ∀ y, y ∈ Kset (reg (u+1)) (idxOf (reg (u+1)) s ac) →
            lt y (idxOf (reg (u+1)) s ac) = true := fun hle2 =>
        kall_idx84 hs hk hac.1 hac.2.1 hac.2.2.1 hac.2.2.2 (hloc _ hmemhead hle2 hs)
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
        (fun q hq hle3 hst => hloc q (show q ∈ (s, ac) :: scanSt (reg (u+1)) (baseOf u)
          (stepF (reg (u+1)) (baseOf u) s ac) t from List.Mem.tail _ hq) hle3 hst) p h hle

/-- **§84.1 の主定理。** 状態つきの条項から `KsetStepOK`。 -/
theorem ksetStepOK_of_idxK84 (u : Nat) (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (H : IdxK84 u x) : KsetStepOK u x := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨_, hallOK⟩ :=
    wcnf_spec_sc (inT_reg (u+1)) (isSC_reg_succ u) (toList x) hc hd (ltM_toList x hx hlx)
  intro p hp hle
  exact scan_idx84 (wcnf (reg (u+1)) (toList x)).1 (none, none)
    stInv_none (kInv75_none u) hallOK (fun q hq hle2 _ y hy => H q hq hle2 y hy) p hp hle

/-- **逆も。** `IdxK84` は門の第二連言そのものなので、これは過不足のない分解である。 -/
theorem idxK84_of_ksetStepOK {u : Nat} {x : Term} (H : KsetStepOK u x) : IdxK84 u x :=
  fun p hp hle y hy => (H p hp hle).2 y hy

/-- §75 の対ごとの条件は状態つきの条項より**強い**。 -/
theorem idxK84_of_local75 (u : Nat) (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (H : LocalK75 u x) : IdxK84 u x :=
  idxK84_of_ksetStepOK (ksetStepOK_of_local75 u x hx hlx H)

end

/-! ### §84.2 走査は必ず前へ進む — `i0 < i0 ⊕ Δ` -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **`v ⊕ d ≠ v`。** `plus` の成分列は「`v` の成分のふるい ++ `d` の成分」なので、
    等しければ長さが合わない。順序の理論は要らない。 -/
theorem ne_plus_self84 {v d : Term} (hv : inT v = true) (hd : inT d = true)
    (hdz : d ≠ zero) : plus v d ≠ v := by
  cases hD : toList d with
  | nil => exact absurd (toList_eq_nil d hD) hdz
  | cons d1 D' =>
    intro hc
    have hT : toList (plus v d) = (toList v).filter (fun a => le d1 a) ++ toList d :=
      toList_plus_inT hv hd hD
    rw [hc] at hT
    have hFself : ((toList v).filter (fun a => le d1 a)).filter (fun a => le d1 a)
        = (toList v).filter (fun a => le d1 a) :=
      filter_self_of_all _ _ (fun x hx => (List.mem_filter.mp hx).2)
    have h2 : (toList v).filter (fun a => le d1 a)
        = (((toList v).filter (fun a => le d1 a)) ++ toList d).filter (fun a => le d1 a) := by
      rw [← hT]
    rw [List.filter_append, hFself] at h2
    have h3 := congrArg List.length h2
    rw [List.length_append] at h3
    have h4 : ((toList d).filter (fun a => le d1 a)).length = 0 := by omega
    have h5 : d1 ∈ (toList d).filter (fun a => le d1 a) :=
      List.mem_filter.mpr ⟨by rw [hD]; exact List.Mem.head _, Evidence.WF.le_self d1⟩
    rw [List.eq_nil_of_length_eq_zero h4] at h5
    cases h5

/-- **`Δ` は 0 でない。** 係数が 0 でなければ、`mulL` は空でない `ω` 冪の列を作る。 -/
theorem ddOf_ne_zero84 {w : Term} {ac : Term × Term} (h : ac.2 ≠ zero) :
    ddOf75 w ac ≠ zero := by
  have hm : ddOf75 w ac
      = ofList ((toList ac.2).map
          (fun p => omegaNF (plus (mulL w (subAP w ac.1)) (logOm p)))) := rfl
  cases hL : toList ac.2 with
  | nil => exact absurd (toList_eq_nil _ hL) h
  | cons q r =>
    rw [hm, hL]
    refine ofList_ne_zero81 _ (by rw [List.map_cons]; exact List.cons_ne_nil _ _) ?_
    intro x hx
    obtain ⟨p, _, hp⟩ := List.mem_map.mp hx
    rw [← hp]
    exact isAP_omegaNF _

/-- **`wcnf` の係数は 0 でない。** 単独の枝は `ω` 冪、併合の枝は `⊕` で、どちらも
    0 にならない。**これが「強臨界枝は指数を必ず伸ばす」の中身である。** -/
theorem wcnf_snd_ne_zero84 {w : Term} (hw : inT w = true) (hsc : w.isSC = true) :
    ∀ (L : List Term), inTL L = true → descL L = true → (∀ x ∈ L, lt x M = true) →
      ∀ ac ∈ (wcnf w L).1, ac.2 ≠ zero := by
  intro L
  induction L with
  | nil => intro _ _ _ ac hac; cases hac
  | cons p rest ih =>
    intro hc hd hm ac hac
    obtain ⟨⟨hap, hip⟩, hcr⟩ := inTL_cons.mp hc
    have hdr := descL_tail hd
    have hmr : ∀ x ∈ rest, lt x M = true := fun x hx => hm x (List.Mem.tail p hx)
    by_cases hlp : lt p w = true
    · rw [wcnf_cons_lt hlp] at hac; cases hac
    · have hlp' : lt p w = false := bool_false hlp
      have hrestOK := wcnf_spec_sc hw hsc rest hcr hdr hmr
      rw [wcnf_cons_ge hlp'] at hac
      cases hr : wcnf w rest with
      | mk fst snd =>
        rw [hr] at hac
        cases fst with
        | nil =>
          rw [List.mem_singleton.mp hac]
          exact omegaNF_ne_zero _
        | cons ac0 ps =>
          cases ac0 with
          | mk a' c' =>
            have hic' : inT c' = true :=
              (hrestOK.2 (a', c') (by rw [hr]; exact List.Mem.head _)).2.2.1
            have hac' : ac ∈ (if (wA w p == a') = true
                then ((wA w p, plus (wC w p) c') :: ps, snd)
                else ((wA w p, wC w p) :: (a', c') :: ps, snd)).1 := hac
            by_cases heq : (wA w p == a') = true
            · rw [if_pos heq] at hac'
              rcases List.mem_cons.mp hac' with h1 | h1
              · rw [h1]
                show plus (wC w p) c' ≠ zero
                cases hC : toList c' with
                | nil => rw [plus_nil hC]; exact omegaNF_ne_zero _
                | cons b1 rr =>
                  intro hz
                  have h2 : ((toList (wC w p)).filter (fun a => le b1 a)
                      ++ toList c').length = 0 := by
                    rw [← toList_plus_inT (inT_wC hip) hic' hC, hz]; rfl
                  rw [List.length_append, hC, List.length_cons] at h2
                  omega
              · exact ih hcr hdr hmr ac (by rw [hr]; exact List.Mem.tail _ h1)
            · rw [if_neg heq] at hac'
              rcases List.mem_cons.mp hac' with h1 | h1
              · rw [h1]; exact omegaNF_ne_zero _
              · exact ih hcr hdr hmr ac (by rw [hr]; exact h1)

/-- **直前の指数は今の指数より真に小さい。** §75.2 の `le_prev_idxOf75` の狭義版。 -/
theorem lt_prev_idxOf84 {w : Term} (hw : inT w = true) {s : Option Term × Option Term}
    {ac : Term × Term} {i0 : Term} (hs : StInv s) (hs1 : s.1 = some i0)
    (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hz : ac.2 ≠ zero) :
    lt i0 (idxOf w s ac) = true := by
  have hi0 : inT i0 = true := (hs.1 i0 hs1).1
  have hdT : inT (ddOf75 w ac) = true := inT_ddOf75 hw h1 h3
  have hle := le_prev_idxOf75 hw hs hs1 h1 h3
  have hidx : idxOf w s ac = plus i0 (ddOf75 w ac) := by
    show (match s.1 with
          | none => sub1 (mulL (mulL w (subAP w ac.1)) ac.2)
          | some j => plus j (mulL (mulL w (subAP w ac.1)) ac.2)) = _
    rw [hs1]
    try rfl
  have hne : (i0 == idxOf w s ac) = false := by
    cases hb : (i0 == idxOf w s ac) with
    | false => rfl
    | true =>
      exfalso
      have heq : i0 = idxOf w s ac := eq_of_beq hb
      rw [hidx] at heq
      exact ne_plus_self84 hi0 hdT (ddOf_ne_zero84 hz) heq.symm
  have h2 : ((i0 == idxOf w s ac) || lt i0 (idxOf w s ac)) = true := hle
  rw [hne, Bool.false_or] at h2
  exact h2

end

/-! ### §84.3 分割条項 — `Δ` か、直前の指数か -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§84 の条項。** 一つの元 `y` について、**今の対の `Δ ⊖ 1`** が抑えるか、
    **直前の指数**が抑えるか、どちらか。比較の相手はどちらも単体の項で、和
    `i0 ⊕ Δ` は現れない。§82 が落とした `aBad82` は右の枝で通る — 逃げる元は
    頭が積んだ指数と**ちょうど等しい**。 -/
def SplitK84 (u : Nat) (x : Term) : Prop :=
  ∀ p ∈ scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1,
    le (reg (u+1)) p.2.1 = true →
      ∀ y, (y ∈ Kset (reg (u+1)) p.2.1 ∨ y ∈ Kset (reg (u+1)) p.2.2) →
        lt y (sub1 (ddOf75 (reg (u+1)) p.2)) = true ∨
        ∃ i0, p.1.1 = some i0 ∧ le y i0 = true

/-- 対ひとつぶんの翻訳。左の枝は §75.2 の `le_sub1dd_idxOf75`、右の枝は §84.2 の
    `lt_prev_idxOf84`。 -/
theorem idx_of_split84 {u : Nat} {s : Option Term × Option Term} {ac : Term × Term}
    (hs : StInv s) (h1 : inT ac.1 = true) (h2 : lt ac.1 M = true)
    (h3 : inT ac.2 = true) (h4 : lt ac.2 M = true) (hz : ac.2 ≠ zero)
    (hsp : ∀ y, (y ∈ Kset (reg (u+1)) ac.1 ∨ y ∈ Kset (reg (u+1)) ac.2) →
        lt y (sub1 (ddOf75 (reg (u+1)) ac)) = true ∨
        ∃ i0, s.1 = some i0 ∧ le y i0 = true) :
    ∀ y, (y ∈ Kset (reg (u+1)) ac.1 ∨ y ∈ Kset (reg (u+1)) ac.2) →
      lt y (idxOf (reg (u+1)) s ac) = true := by
  have hw : inT (reg (u+1)) = true := inT_reg (u+1)
  have hlw : lt (reg (u+1)) M = true := ltM_reg (u+1)
  have hdT : inT (ddOf75 (reg (u+1)) ac) = true := inT_ddOf75 hw h1 h3
  obtain ⟨hidxT, _⟩ := inT_idxOf mulDescInT hw hlw hs h1 h2 h3 h4
  intro y hy
  have hyi : inT y = true := by
    rcases hy with hy | hy
    · exact inT_mem_Kset75 ac.1 h1 _ y hy
    · exact inT_mem_Kset75 ac.2 h3 _ y hy
  rcases hsp y hy with hL | ⟨i0, hs1, hle⟩
  · exact lt_of_lt_of_le3 (inT_le_fragR y hyi) (inT_le_fragR _ (inT_sub1 hdT))
      (inT_le_fragR _ hidxT) hL (le_sub1dd_idxOf75 hw hs h1 h3)
  · have hi0 : inT i0 = true := (hs.1 i0 hs1).1
    exact lt_of_le_of_lt3 (inT_le_fragR y hyi) (inT_le_fragR i0 hi0)
      (inT_le_fragR _ hidxT) hle (lt_prev_idxOf84 hw hs hs1 h1 h3 hz)

/-- **§84.3 の主定理。** 分割条項から `KsetStepOK`。 -/
theorem ksetStepOK_of_split84 (u : Nat) (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (H : SplitK84 u x) : KsetStepOK u x := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨_, hallOK⟩ :=
    wcnf_spec_sc (inT_reg (u+1)) (isSC_reg_succ u) (toList x) hc hd (ltM_toList x hx hlx)
  have hnz := wcnf_snd_ne_zero84 (inT_reg (u+1)) (isSC_reg_succ u) (toList x) hc hd
    (ltM_toList x hx hlx)
  intro p hp hle
  refine scan_idx84 (wcnf (reg (u+1)) (toList x)).1 (none, none)
    stInv_none (kInv75_none u) hallOK ?_ p hp hle
  intro q hq hle2 hst
  have hmem : q.2 ∈ (wcnf (reg (u+1)) (toList x)).1 :=
    scanSt_mem_snd _ _ _ _ q hq
  obtain ⟨hi1, hl1, hi2, hl2⟩ := hallOK q.2 hmem
  exact idx_of_split84 hst hi1 hl1 hi2 hl2 (hnz q.2 hmem) (H q hq hle2)

/-- 系 — 分割条項は状態つきの条項より強い。 -/
theorem idxK84_of_split84 (u : Nat) (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (H : SplitK84 u x) : IdxK84 u x :=
  idxK84_of_ksetStepOK (ksetStepOK_of_split84 u x hx hlx H)

/-- §75 の対ごとの条件は分割条項の**左の枝だけ**を使ったもの。 -/
theorem split84_of_local75 {u : Nat} {x : Term} (H : LocalK75 u x) : SplitK84 u x := by
  intro p hp hle y hy
  exact Or.inl (H p.2 (scanSt_mem_snd _ _ _ _ p hp) hle y hy)

end

/-! ### §84.4 判定器 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 状態つきの条項の判定器。 -/
def idxb84 (u : Nat) (x : Term) : Bool :=
  (scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1).all fun p =>
    !(le (reg (u+1)) p.2.1) ||
      ((Kset (reg (u+1)) p.2.1 ++ Kset (reg (u+1)) p.2.2).all fun y =>
        lt y (idxOf (reg (u+1)) p.1 p.2))

/-- 分割条項の判定器。 -/
def splitb84 (u : Nat) (x : Term) : Bool :=
  (scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1).all fun p =>
    !(le (reg (u+1)) p.2.1) ||
      ((Kset (reg (u+1)) p.2.1 ++ Kset (reg (u+1)) p.2.2).all fun y =>
        lt y (sub1 (ddOf75 (reg (u+1)) p.2)) ||
          (match p.1.1 with | none => false | some i0 => le y i0))

theorem idxK84_of_b84 {u : Nat} {x : Term} (h : idxb84 u x = true) : IdxK84 u x := by
  intro p hp hle y hy
  have h1 := List.all_eq_true.mp
    (show (scanSt (reg (u+1)) (baseOf u) (none, none)
        (wcnf (reg (u+1)) (toList x)).1).all (fun p =>
      !(le (reg (u+1)) p.2.1) ||
        ((Kset (reg (u+1)) p.2.1 ++ Kset (reg (u+1)) p.2.2).all fun y =>
          lt y (idxOf (reg (u+1)) p.1 p.2))) = true from h) p hp
  rw [hle, Bool.not_true, Bool.false_or] at h1
  refine List.all_eq_true.mp h1 y ?_
  rcases hy with hy | hy
  · exact List.mem_append.mpr (Or.inl hy)
  · exact List.mem_append.mpr (Or.inr hy)

/-- **判定器は条項と過不足なく同値。** だから `false` は反証である。 -/
theorem b84_of_idxK84 {u : Nat} {x : Term} (H : IdxK84 u x) : idxb84 u x = true := by
  show (scanSt (reg (u+1)) (baseOf u) (none, none)
      (wcnf (reg (u+1)) (toList x)).1).all (fun p =>
    !(le (reg (u+1)) p.2.1) ||
      ((Kset (reg (u+1)) p.2.1 ++ Kset (reg (u+1)) p.2.2).all fun y =>
        lt y (idxOf (reg (u+1)) p.1 p.2))) = true
  refine List.all_eq_true.mpr ?_
  intro p hp
  cases hle : le (reg (u+1)) p.2.1 with
  | false => rfl
  | true =>
    rw [Bool.not_true, Bool.false_or]
    refine List.all_eq_true.mpr ?_
    intro y hy
    refine H p hp hle y ?_
    rcases List.mem_append.mp hy with h | h
    · exact Or.inl h
    · exact Or.inr h

theorem splitK84_of_b84 {u : Nat} {x : Term} (h : splitb84 u x = true) : SplitK84 u x := by
  intro p hp hle y hy
  have h1 := List.all_eq_true.mp
    (show (scanSt (reg (u+1)) (baseOf u) (none, none)
        (wcnf (reg (u+1)) (toList x)).1).all (fun p =>
      !(le (reg (u+1)) p.2.1) ||
        ((Kset (reg (u+1)) p.2.1 ++ Kset (reg (u+1)) p.2.2).all fun y =>
          lt y (sub1 (ddOf75 (reg (u+1)) p.2)) ||
            (match p.1.1 with | none => false | some i0 => le y i0))) = true from h) p hp
  rw [hle, Bool.not_true, Bool.false_or] at h1
  have h2 := List.all_eq_true.mp h1 y (by
    rcases hy with hy | hy
    · exact List.mem_append.mpr (Or.inl hy)
    · exact List.mem_append.mpr (Or.inr hy))
  cases h3 : lt y (sub1 (ddOf75 (reg (u+1)) p.2)) with
  | true => exact Or.inl rfl
  | false =>
    rw [h3, Bool.false_or] at h2
    cases hq : p.1.1 with
    | none => rw [hq] at h2; exact Bool.noConfusion h2
    | some i0 => rw [hq] at h2; exact Or.inr ⟨i0, rfl, h2⟩

end

/-! ### §84.5 §75 の対ごとの条件は**偽** -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- §75.3 の `localK75_of_b` の逆。判定器は条項と同値なので `false` は反証。 -/
theorem b73_of_localK75 {u : Nat} {x : Term} (H : LocalK75 u x) : localOKb73 u x = true := by
  show (wcnf (reg (u+1)) (toList x)).1.all (fun ac =>
    !(le (reg (u+1)) ac.1) ||
      ((Kset (reg (u+1)) ac.1 ++ Kset (reg (u+1)) ac.2).all fun y =>
        lt y (sub1 (mulL (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) ac.2)))) = true
  refine List.all_eq_true.mpr ?_
  intro ac hac
  cases hle : le (reg (u+1)) ac.1 with
  | false => rfl
  | true =>
    rw [Bool.not_true, Bool.false_or]
    refine List.all_eq_true.mpr ?_
    intro y hy
    refine H ac hac hle y ?_
    rcases List.mem_append.mp hy with h | h
    · exact Or.inl h
    · exact Or.inr h

/-- **§84 の否定。** §75 が残した仮説 `LocalStd75` — 状態を見ない対ごとの条件 —
    も `aBad82` で落ちる。§82 は §78 の `LocalK2_78` (より強い方) しか反証して
    いなかった。だから `certIn_t326_local75` も**空回り**である。 -/
theorem not_localStd75 : ¬ LocalStd75 := by
  intro H
  have h := H aBad82 aBad82_hyps.1 aBad82_hyps.2.1 aBad82_hyps.2.2.1 aBad82_hyps.2.2.2.1
  have h2 := b73_of_localK75 h
  rw [show localOKb73 0 (dict aBad82) = false from by decide] at h2
  exact Bool.noConfusion h2

theorem not_localStdFacts75 : ¬ LocalStdFacts75 := fun H => not_localStd75 (localStd75_of_facts75 H)

theorem not_localStdFacts2_75 : ¬ LocalStdFacts2_75 :=
  fun H => not_localStd75 (localStd75_of_facts2_75 H)

/-- **落ちない方。** 同じ `aBad82` で分割条項は通る。 -/
theorem splitK84_aBad82 : SplitK84 0 (dict aBad82) := splitK84_of_b84 (by decide)

/-- **落ちる理由と落ちない理由が一つの定理に。** -/
theorem split84_saves_aBad82 :
    localOKb73 0 (dict aBad82) = false ∧ k2b78 0 (dict aBad82) = false ∧
    splitb84 0 (dict aBad82) = true ∧ idxb84 0 (dict aBad82) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end

/-! ### §84.6 組み立て — 326 行目が待つのは分割条項ひとつ -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§84 の残る仮説。** 部分領域の項について分割条項。**証明しない。** -/
def SplitStd84 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true →
    inT (dict a) = true → lt (dict a) M = true → SplitK84 0 (dict a)

/-- 状態つきの条項の側の形。 -/
def IdxStd84 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true →
    inT (dict a) = true → lt (dict a) M = true → IdxK84 0 (dict a)

theorem idxStd84_of_split84 (H : SplitStd84) : IdxStd84 :=
  fun a hb hs hi hl => idxK84_of_split84 0 (dict a) hi hl (H a hb hs hi hl)

/-- 分割条項だけで `dict` の像は 𝔗(M) の中。`u = 1` は §73.4 が閉じている。 -/
theorem inT_dict_of_idx84 (H : IdxStd84) : ∀ a : BT, btLe72 1 a = true →
    BT.isStd a = true → inT (dict a) = true ∧ lt (dict a) M = true
  | .zero, _, _ => ⟨inT_zero, lt_zero_M⟩
  | .D u a, hb, h => by
    obtain ⟨hu, hba⟩ := btLe72_D 1 u a hb
    have ih := inT_dict_of_idx84 H a hba (isStd_of_D h)
    refine inT_collapse_gap3 u (dict a) ih.1 ih.2
      (psiIdxOK_of_stepOK u (dict a) ih.1 ih.2 ?_)
    cases u with
    | zero => exact ksetStepOK_of_idxK84 0 (dict a) ih.1 ih.2 (H a hba h ih.1 ih.2)
    | succ u' =>
      cases u' with
      | zero => exact ksetStepOK_one73 a hba
      | succ u'' => exact absurd hu (by omega)
  | .sum a b, hb, h => by
    obtain ⟨hba, hbb⟩ := btLe72_sum 1 a b hb
    have iha := inT_dict_of_idx84 H a hba (isStd_of_sum h).1
    have ihb := inT_dict_of_idx84 H b hbb (isStd_of_sum h).2
    exact ⟨inT_plus iha.1 ihb.1, lt_plus_M iha.1 ihb.1 iha.2 ihb.2⟩

/-- **§84 の第一の結論。** §73 の残る門は状態つきの条項から出る。 -/
theorem psiIdxStep073_of_idx84 (H : IdxStd84) : PsiIdxStep073 := by
  intro a hb h
  have ih := inT_dict_of_idx84 H a hb (isStd_of_D h)
  exact ksetStepOK_of_idxK84 0 (dict a) ih.1 ih.2 (H a hb h ih.1 ih.2)

/-- 分割条項からも。 -/
theorem psiIdxStep073_of_split84 (H : SplitStd84) : PsiIdxStep073 :=
  psiIdxStep073_of_idx84 (idxStd84_of_split84 H)

/-- **逆向き。** 状態つきの条項は門と同値 — 分解は過不足がない。 -/
theorem idxStd84_of_step073 (H : PsiIdxStep073) : IdxStd84 :=
  fun a hb hs _ _ => idxK84_of_ksetStepOK (H a hb hs)

/-- **§84 の第二の結論。** 326 行目の証明書が `K` の側で待つのは分割条項ひとつ。 -/
theorem certIn_t326_split84 (H : SplitStd84)
    (HD : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_step73 (psiIdxStep073_of_split84 H) HD HI HC hacc

theorem certIn_t326_idx84 (H : IdxStd84)
    (HD : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_step73 (psiIdxStep073_of_idx84 H) HD HI HC hacc

end


/-! ### §84.7 測定 (凍結)

**構成を先に書く。**  §82.8 の四群は「上限で切って一様に足す」作り方なので、
**成分どうしが相互作用する項が一つも入っていない**。§84 の母集団は逆から作る —
`ψ₀` の引数が**和の別の成分そのもの**になるように、手で組む。

    tw84 k       = ψ₁^k 0                      (段 1 の塔)
    cap84 m a    = ψ₁^m a
    famA84  h ⊕ ψ₁^m(ψ₀ h),  h = tw84 (k+2)          16 個  ← `aBad82` はここの (k,m)=(2,2)
    famB84  ψ₁^m(ψ₀ t) ⊕ t                            9 個  (`ψ₀` が頭、引数が尾)
    famC84  h ⊕ ψ₁^m(ψ₀ (h ⊕ 別の塔))                12 個
    famD84  h ⊕ h' ⊕ ψ₁^m(ψ₀ h)                       6 個  (三項和、引数は先頭)
    famE84  h ⊕ h' ⊕ ψ₁^m(ψ₀ h')                      6 個  (三項和、引数は中項)
    famF84  h ⊕ ψ₁^m(ψ₀ (h ⊕ ψ₀ h))                   6 個  (`ψ₀` が二重)
    famG84  ψ₁(h ⊕ h') ⊕ ψ₁(ψ₀ (h ⊕ h'))              6 個
    famH84  h ⊕ ψ₁^m(ψ₀ (h の真の部分塔))            18 個
    pop84   = 上の和集合、重複を除いて                77 個
    qual84  = そのうち条項の仮説をぜんぶ満たすもの    53 個

  比較の相手として §82.8 の `refFam82` (5949 項) をそのまま使う。

**測定の結果。**

  * **§75 の対ごとの条件は偽。**  `qual84` の 53 項のうち **3 項**で `localOKb73` が
    落ちる (ぜんぶ `famA84`)。`refFam82` の 5949 項では **690 項**。
    §82 は §78 の `LocalK2_78` (より強い方) しか反証していなかったので、
    `LocalStd75` の反証は §84 が初めてである (`not_localStd75`)。
  * **分割条項はそのぜんぶを救う。**  `splitb84` は `qual84` の 53 項でも、
    `refFam82` の 5949 項 (690 の反証項をぜんぶ含む) でも、失敗 **0**。
    `idxb84` と `stepOKb` も失敗 0。
  * **逃げる元は直前の指数が抑える。しかも等号が出る。**  左の枝が落ちる箇所
    (以下「逃げる元」) は `qual84` の 57 の発火歩で 3 つ、`refFam82` の 690 の
    反証項で 893 つ。**そのぜんぶで `le y i0` が成り立つ。**  さらに内訳が
    §82 の診断の算術的な中身になっている — `refFam82` の 893 のうち **885 は
    `y < i0` (真に小さい)** が、**8 つは `y = i0` (等号)** で、`qual84` の 3 つは
    ぜんぶ等号。等号が出るのは `ψ₀` の引数が**頭そのもの**のときで、そのとき
    その崩壊指数は頭が走査に積んだ指数と一致する (`aBad82` がそれ)。
    **だから `Δ` では足りず `i0 ⊕ Δ` では足りる。足りる理由は `Δ ≠ 0` (§84.2)
    ただ一つで、それが要るのは 893 のうち 8 箇所だけである。**
  * **326 行目とその基本列。**  `regPairs72 ([t326] ++ exp72)` の 41 個の添字で
    `splitb84`・`idxb84`・`stepOKb`・`localOKb73` はぜんぶ失敗 0。326 行目の値
    `bVal t326` 自身 (`BT` の大きさ 13) も同じ。**§82 の修理はここで死ぬ** —
    成分ぜんぶが `BT.isStd (ψ₀ ·)` を満たすという条件は 41 個のうち **30 個**で
    落ち、`bVal t326` 自身でも落ちる。
  * **部分領域。**  `regPairs72 (sub72 8)` の 1908 個の添字でも失敗 0
    (成分標準性は 319 個で落ちる)。
  * **分離は見つからなかった。**  `splitb84` が落ちて `idxb84` が通る例は
    どの母集団にも無い。強めたのは**形**であって、測れる範囲では強さではない。 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- `ψ₁` の塔。 -/
def tw84 : Nat → BT
  | 0 => BT.zero
  | k+1 => BT.D 1 (tw84 k)
/-- `ψ₁^m a`。 -/
def cap84 : Nat → BT → BT
  | 0, a => a
  | m+1, a => BT.D 1 (cap84 m a)
def d0_84 (a : BT) : BT := BT.D 0 a
def s3_84 (a b c : BT) : BT := BT.sum a (BT.sum b c)

def famA84 : List BT :=
  (List.range 4).flatMap fun k => (List.range 4).map fun m =>
    BT.sum (tw84 (k+2)) (cap84 (m+1) (d0_84 (tw84 (k+2))))
def famB84 : List BT :=
  (List.range 3).flatMap fun k => (List.range 3).map fun m =>
    BT.sum (cap84 (m+1) (d0_84 (tw84 (k+2)))) (tw84 (k+2))
def famC84 : List BT :=
  (List.range 3).flatMap fun k => (List.range 2).flatMap fun j => (List.range 2).map fun m =>
    BT.sum (tw84 (k+2)) (cap84 (m+1) (d0_84 (BT.sum (tw84 (k+2)) (tw84 (j+1)))))
def famD84 : List BT :=
  (List.range 3).flatMap fun k => (List.range 2).map fun m =>
    s3_84 (tw84 (k+2)) (tw84 (k+1)) (cap84 (m+1) (d0_84 (tw84 (k+2))))
def famE84 : List BT :=
  (List.range 3).flatMap fun k => (List.range 2).map fun m =>
    s3_84 (tw84 (k+2)) (tw84 (k+1)) (cap84 (m+1) (d0_84 (tw84 (k+1))))
def famF84 : List BT :=
  (List.range 3).flatMap fun k => (List.range 2).map fun m =>
    BT.sum (tw84 (k+2))
      (cap84 (m+1) (d0_84 (BT.sum (tw84 (k+2)) (d0_84 (tw84 (k+2))))))
def famG84 : List BT :=
  (List.range 3).flatMap fun k => (List.range 2).map fun j =>
    BT.sum (BT.D 1 (BT.sum (tw84 (k+2)) (tw84 (j+1))))
      (BT.D 1 (d0_84 (BT.sum (tw84 (k+2)) (tw84 (j+1)))))
def famH84 : List BT :=
  (List.range 3).flatMap fun k => (List.range 3).flatMap fun j => (List.range 2).map fun m =>
    BT.sum (tw84 (k+3)) (cap84 (m+1) (d0_84 (tw84 (j+1))))

def pop84 : List BT :=
  (famA84 ++ famB84 ++ famC84 ++ famD84 ++ famE84 ++ famF84 ++ famG84 ++ famH84).eraseDups
def okHyp84 (a : BT) : Bool :=
  btLe72 1 a && BT.isStd (BT.D 0 a) && inT (dict a) && lt (dict a) M
def qual84 : List BT := pop84.filter okHyp84
/-- 326 行目とその基本列 (二重に 6 段まで) の添字ぜんぶ。 -/
def r326_84 : List (Nat × BT) := regPairs72 ([t326] ++ exp72)

-- 母集団の大きさ。
#guard (pop84.length, qual84.length) == (77, 53)
#guard r326_84.length == 41

/-! **否定 — §75 の対ごとの条件は相互作用する項で落ちる。** 落ちるのは `famA84`
(`ψ₀` の引数が頭そのもの) だけで、`aBad82` はそこの最小。 -/

#guard (qual84.filter fun a => !(localOKb73 0 (dict a))).length == 3
#guard (qual84.filter fun a => !(k2b78 0 (dict a))).length == 3
#guard (famA84.filter fun a => okHyp84 a && !(localOKb73 0 (dict a))).length == 3

/-! **肯定 1 — 分割条項は同じ母集団で落ちない。** 門 `stepOKb` も、状態つきの
条項 `idxb84` も同じ。 -/

#guard (qual84.filter fun a => !(splitb84 0 (dict a))).length == 0
#guard (qual84.filter fun a => !(idxb84 0 (dict a))).length == 0
#guard (qual84.filter fun a => !(stepOKb 0 (dict a))).length == 0

/-! **肯定 2 — 326 行目とその基本列。** 分割条項は落ちない。**§82 の修理は
ここで死ぬ** — 成分ぜんぶが `BT.isStd (ψ₀ ·)` という条件は 41 個中 30 個で落ちる。 -/

#guard (r326_84.filter fun q => !(splitb84 q.1 (dict q.2))).length == 0
#guard (r326_84.filter fun q => !(idxb84 q.1 (dict q.2))).length == 0
#guard (r326_84.filter fun q => !((BT.toL q.2).all fun t => BT.isStd (BT.D 0 t))).length == 30
#guard splitb84 0 (dict (bVal t326))
#guard !((BT.toL (bVal t326)).all fun t => BT.isStd (BT.D 0 t))

/-! **肯定 3 — 逃げる元は直前の指数と等号で並ぶ。** `qual84` の 57 の発火歩で
左の枝が落ちる元は 3 つ、そのどれでも `y = i0` (等号)。`refFam82` の側では
893 のうち 885 が真に小さく、等号は 8 つ — その 8 つが §84.2 の `Δ ≠ 0` を
要求する箇所である。 -/

#guard
  (let fires := qual84.flatMap fun a =>
     (scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1).filter
       (fun p => le (reg 1) p.2.1)
   let bad := fires.flatMap fun p =>
     (Kset (reg 1) p.2.1 ++ Kset (reg 1) p.2.2).filterMap fun y =>
       if lt y (sub1 (ddOf75 (reg 1) p.2)) then none else some (p, y)
   (fires.length, bad.length,
    (bad.filter fun q => match q.1.1.1 with
      | none => false | some i0 => q.2 == i0).length)) == (57, 3, 3)

-- (重い測定。数は §84 の前書きに記録)
-- #guard (refFam82.filter fun a => !(localOKb73 0 (dict a))).length == 690
-- #guard (refFam82.filter fun a => !(splitb84 0 (dict a))).length == 0
-- #guard ((regPairs72 (sub72 8)).filter fun q => !(splitb84 q.1 (dict q.2))).length == 0
-- #guard ((regPairs72 (sub72 8)).filter fun q =>
--   !((BT.toL q.2).all fun t => BT.isStd (BT.D 0 t))).length == 319

end

/-! ### §84.8 公理 -/

/-! ## §86 THE SPLIT IS FALSE TOO — THE SUM `i₀ ⊕ Δ` IS NOT AN ARTEFACT OF THE FOLD

§84 replaced §75's refuted per-pair clause by a disjunction of two comparisons against
SINGLE objects,

    y < Δ ⊖ 1        OR        y ≤ i₀,

and reported that no measured term separated it from the gate.  **It is false.**  The term

    bad86 = ψ₁ψ₁ψ₁ψ₁0 ⊕ ψ₁ψ₁ψ₁ψ₀(ψ₁ψ₁ψ₁ψ₁0 ⊕ ψ₁ψ₁ψ₁0)

satisfies every hypothesis of `SplitStd84` — `btLe72 1`, `BT.isStd (ψ₀ ·)`, `inT (dict ·)`,
`dict · < M` — and breaks `SplitK84`.  `not_splitStd84` is a theorem, so
`certIn_t326_split84` joins `certIn_t326_local75`, `certIn_t326_k2_78`, `certIn_t326_big80`
and `certIn_t326_node82` in the vacuous column.

**THE ANATOMY IS ONE LINE, AND IT IS THE `+1` §84 DID NOT LOOK FOR.**  `aBad82` put the
head itself under the `ψ₀`; `bad86` puts the head PLUS one more firing summand under it.  At
the tail's scan step,

    i₀ = ω^{ω^{ω^{Ω₁·2}}},        y = i₀ ⊕ 1,        Δ = ω^{ω^{ω^{Ω₁ ⊕ ψ_{Ω₁}(y)}}},

so `y > i₀` (the right disjunct fails **by exactly `1`**) and `ψ_{Ω₁}(y) < Ω₁` gives `Δ < y`
(the left disjunct fails, as it already did for `aBad82`).  The gate itself is untouched:
`y = i₀ ⊕ 1 < i₀ ⊕ Δ` because `1 < Δ`.  **Both summands of `i₀ ⊕ Δ` are needed at the same
element, so the sum is not an artefact of the fold and no clause that compares a `K`-element
against `Δ` alone or against `i₀` alone can close the gate.**  §84 saw only the two extreme
cases — `y < i₀` (885 escapes) and `y = i₀` (8 escapes) — because its `famC84`, which is the
right SHAPE, ran both the cap `ψ₁^m` and the second summand of the `ψ₀`-argument only to two
levels, and a `ψ₁`-tower needs THREE before its own scan step fires.

WHAT IS PROVED, UNCONDITIONALLY.

  §86.1  **THE DECIDER IS EXACT IN BOTH DIRECTIONS.**  `b86_of_splitK84` is the converse of
         §84.4's `splitK84_of_b84`, so `splitb84 = false` is a refutation and not a failure
         to prove.  That is the instrument §86.2 uses.

  §86.2  **THE REFUTATION.**  `not_splitK84_bad86`, `not_splitStd84`, and
         `split84_dies_bad86` freezing the four verdicts on one term: §75's clause `false`,
         §84's clause `false`, §84's state-aware clause `true`, the gate `true`.  The last
         two matter: `IdxStd84` is NOT refuted — it is equal in strength to
         `PsiIdxStep073` — so what §86 kills is the localisation, not the gate.

  §86.3  **EVERYTHING BELOW `Ω₁` IS FREE, `⊖ 1` INCLUDED.**  §80.3's `lt_dd_of_lt_reg80`
         bounds a `K`-element below `Ω₁` by `Δ`, which is one `⊖ 1` short of the left
         disjunct.  `sub1_ddOf86` closes the gap outright: when `aV ⊖ Ω₁ ≠ 0` the head
         component of `Δ` is an `ω`-power at or above `Ω₁`, hence never `1`, hence
         `Δ ⊖ 1 = Δ`; and when `aV ⊖ Ω₁ = 0` the set `K_{Ω₁} aV` is empty.  So
         `lt_sub1dd_of_lt_reg86` : **every `K_{Ω₁} aV`-element below `Ω₁` satisfies the LEFT
         disjunct, with no side condition at all.**  §80.7 measured that branch at 458 of 635
         firing steps.

  §86.4  **THE REPLACEMENT — SPLIT THE ELEMENT, NOT THE BOUND.**  `SplitK86` asks, of the
         same `y`,

             y < Δ ⊖ 1     OR     y ≤ i₀ ⊕ (y ⊖ i₀)  and  y ⊖ i₀ < Δ,

         where `remOf86 i0 y` is `0` when `y ≤ i₀` and otherwise the components of `y` past
         the length of `i₀`.  `split86_of_split84` shows it is WEAKER than §84's clause (take
         the remainder `0`; `Δ ≠ 0` is §84.2), it survives `bad86` (remainder `1`), and
         `ksetStepOK_of_split86` still delivers the gate — through §79.3's
         `plus_smono_right_inT79`, which is the only new order fact the reduction needs.
         §86.5 re-hangs row 326 on it: `psiIdxStep073_of_split86` and `certIn_t326_split86`.

WHAT IS **NOT** CLAIMED.  `SplitStd86` is NOT proved, and the honest reading of §86 is that
the shape is now as local as it can get: the comparison `y ⊖ i₀ < Δ` is against a single
object, but the decomposition `y = i₀ ⊕ (y ⊖ i₀)` is exactly the arithmetic §82 diagnosed and
§84 tried to avoid.  `IdxStd84` is untouched — it IS the gate, and `bad86` does not dent it.
`LocalK2Snd_78`, `DictHeadLt77`, `CofDenseS1`, `BCofIn71` are untouched.

WHAT THE MEASUREMENT SAYS (§86.6 gives the construction).  §84's `famC84` is the right shape
with the wrong range: it runs the cap `ψ₁^m` only to `m ≤ 2` and the second summand `g` of the
`ψ₀`-argument only to `ψ₁ψ₁0`, and **a `ψ₁`-tower does not fire as a scan step until its third
level** (`wA (ψ₁ψ₁ψ₁0) = Ω₁` exactly).  So in §84's corpus the argument's own scan could never
step past the head's contribution, and no escape could exceed `i₀`.  §86 opens both to three.

  * **§84's clause is false on 10 of 53 qualifying terms.**  The refuters sit in the families
    where the `ψ₀`-argument carries a firing second summand — `famU86` 4, `famV86` 2,
    `famW86` 2, `famX86` 2, and 0 in the two families where it does not (`famY86`, `famZ86`).
    §75's per-pair clause falls on 31 of the same 53.  `bad86` is the smallest refuter in
    `pop86`, 20 symbols against `aBad82`'s 15.
  * **The gate does not fall with it.**  `idxb84` and `stepOKb` fail 0 times on all 53.
  * **The breakdown of the escapes is what refutes §84's arithmetic.**  Over the 95 firing
    steps there are 31 escapes: 3 with `y < i₀`, 18 with `y = i₀` — and **10 with `y > i₀`**.
    §84 measured only the first two kinds and concluded `y ≤ i₀` sufficed.  **All 31 satisfy
    §86's split**, and `splitb86` fails 0 times on all 53.
  * **All 31 escapes are at or above `Ω₁`,** so §86.3's free half is vacuous on THIS
    population; the 458 of 635 steps it settles are the ones §80.7 counted, not these.
  * **Row 326 sees none of it.**  Over the 41 indices of `regPairs72 ([t326] ++ exp72)`,
    `splitb84`, `splitb86`, `idxb84` and `stepOKb` all fail 0 times, and over §84's own
    `qual84` both `splitb84` and `splitb86` fail 0 times.  The refutation is a statement
    about the CLAUSE, not about the row.
  * **And the old corpora still cannot see it, which is why §84 could not.**  Over §82.8's
    5949 `refFam82` terms `splitb84` fails 0 times (§75's clause fails 690, reproducing §84's
    count exactly) and `splitb86` fails 0 times; over the 1908 indices of
    `regPairs72 (sub72 8)` both fail 0 times.  Uniformly-capped-and-summed corpora contain no
    term whose `ψ₀`-argument carries a firing second summand.
-/

/-! ### §86.1 判定器の逆 — `splitb84 = false` は反証である -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- §84.4 の `splitK84_of_b84` の逆。判定器は条項と過不足なく同値なので、
    `splitb84 = false` は**反証**である。 -/
theorem b86_of_splitK84 {u : Nat} {x : Term} (H : SplitK84 u x) : splitb84 u x = true := by
  show (scanSt (reg (u+1)) (baseOf u) (none, none)
      (wcnf (reg (u+1)) (toList x)).1).all (fun p =>
    !(le (reg (u+1)) p.2.1) ||
      ((Kset (reg (u+1)) p.2.1 ++ Kset (reg (u+1)) p.2.2).all fun y =>
        lt y (sub1 (ddOf75 (reg (u+1)) p.2)) ||
          (match p.1.1 with | none => false | some i0 => le y i0))) = true
  refine List.all_eq_true.mpr ?_
  intro p hp
  cases hle : le (reg (u+1)) p.2.1 with
  | false => rfl
  | true =>
    rw [Bool.not_true, Bool.false_or]
    refine List.all_eq_true.mpr ?_
    intro y hy
    have hy' : (y ∈ Kset (reg (u+1)) p.2.1 ∨ y ∈ Kset (reg (u+1)) p.2.2) := by
      rcases List.mem_append.mp hy with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases H p hp hle y hy' with h | ⟨i0, hs1, hle2⟩
    · rw [h]; rfl
    · rw [hs1]
      show (lt y (sub1 (ddOf75 (reg (u+1)) p.2)) || le y i0) = true
      rw [hle2]
      exact Bool.or_true _

end

/-! ### §86.2 反証 — 逃げる元は直前の指数を **1 だけ** はみ出す -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **反証項。** `ψ₁ψ₁ψ₁ψ₁0 ⊕ ψ₁ψ₁ψ₁ψ₀(ψ₁ψ₁ψ₁ψ₁0 ⊕ ψ₁ψ₁ψ₁0)`。
    `aBad82` は `ψ₀` の引数を**頭そのもの**にしたが、こちらは**頭 ⊕ もう一段**にする。
    その一段 `ψ₁ψ₁ψ₁0` は、走査の歩として発火する最小の `ψ₁` の塔である
    (`wA` がちょうど `Ω₁`)。だから引数の走査は頭ぶんの指数の**先**へ一歩進み、
    出てくる崩壊指数は `i0 ⊕ 1`。§84 の右の枝 `y ≤ i0` はここで、ちょうど `1` だけ足りない。 -/
def bad86 : BT :=
  BT.sum (BT.D 1 (BT.D 1 (BT.D 1 (BT.D 1 BT.zero))))
    (BT.D 1 (BT.D 1 (BT.D 1 (BT.D 0
      (BT.sum (BT.D 1 (BT.D 1 (BT.D 1 (BT.D 1 BT.zero))))
        (BT.D 1 (BT.D 1 (BT.D 1 BT.zero))))))))

/-- **`bad86` は `SplitStd84` の仮説をぜんぶ満たす。** -/
theorem bad86_hyps :
    btLe72 1 bad86 = true ∧ BT.isStd (BT.D 0 bad86) = true ∧
    inT (dict bad86) = true ∧ lt (dict bad86) M = true :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **§86 の否定 — §84 の分割条項は偽。** -/
theorem not_splitK84_bad86 : ¬ SplitK84 0 (dict bad86) := by
  intro H
  have h := b86_of_splitK84 H
  rw [show splitb84 0 (dict bad86) = false from by decide] at h
  exact Bool.noConfusion h

/-- **§86 の主定理。** 326 行目が §84 で待っていた仮説は偽。 -/
theorem not_splitStd84 : ¬ SplitStd84 := fun H =>
  not_splitK84_bad86
    (H bad86 bad86_hyps.1 bad86_hyps.2.1 bad86_hyps.2.2.1 bad86_hyps.2.2.2)

/-- **落ちるものと落ちないものが一つの定理に。** §75 の対ごとの条件も §84 の分割条項も
    `false`、しかし状態つきの条項も門も `true` — 消えたのは局所化であって門ではない。 -/
theorem split84_dies_bad86 :
    localOKb73 0 (dict bad86) = false ∧ splitb84 0 (dict bad86) = false ∧
    idxb84 0 (dict bad86) = true ∧ stepOKb 0 (dict bad86) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end

/-! ### §86.3 `Ω₁` より下の元は左の枝で只 — `⊖ 1` ごと -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

private theorem ofList_eq_zero86 : ∀ (l : List Term), ofList l = zero → l = [] ∨ l = [zero]
  | [], _ => Or.inl rfl
  | [a], h => Or.inr (by rw [show a = zero from h])
  | _ :: _ :: _, h => absurd h (by intro hc; exact Term.noConfusion hc)

/-- `subAP w h = 0` なら成分列は空か `[w]` (§80.3 と同じ、`private` なので引き直す)。 -/
private theorem subAP_eq_zero86 {w t : Term} (ht : inT t = true) (h : subAP w t = zero) :
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
      rcases ofList_eq_zero86 r h1 with h2 | h2
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

/-- 成分列が空か `[Ω_{u+1}]` なら `K_{Ω_{u+1}}` は空 (§80.3 と同じ)。 -/
private theorem kset_nil_of_toList86 {u : Nat} {t : Term}
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

/-- `0 < Ω_{u+1}`。 -/
theorem lt_zero_reg86 (u : Nat) : lt zero (reg (u+1)) = true :=
  lt_zero_left (show reg (u+1) ≠ zero from by intro hc; exact Term.noConfusion hc)

/-- `1 < Ω_{u+1}`。§79.5 の `lt_one_W79` を段について一般化しただけ。 -/
theorem lt_one_reg86 (u : Nat) : lt TM.Term.one (reg (u+1)) = true := by
  show lt (phi zero zero) (Z (TM.Term.ofNat u)) = true
  exact lt_phi_Z_of (lt_zero_reg86 u) (lt_zero_reg86 u)

/-- だから `Ω_{u+1} ≤ 1` は偽。 -/
theorem le_reg_one_false86 (u : Nat) : le (reg (u+1)) TM.Term.one = false := by
  have h1 : lt (reg (u+1)) TM.Term.one = false :=
    lt_asymm_inT inT_one (inT_reg (u+1)) (lt_one_reg86 u)
  show ((reg (u+1) == TM.Term.one) || lt (reg (u+1)) TM.Term.one) = false
  rw [h1, show (reg (u+1) == TM.Term.one) = false from by
    show ((Z (TM.Term.ofNat u) : Term) == TM.Term.one) = false
    rfl]
  rfl

/-- `Δ` の成分列。`mulL` は係数の成分ごとに `ω` 冪を並べるだけ。 -/
private theorem toList_ddOf86 {w : Term} {ac : Term × Term} {p1 : Term} {rest : List Term}
    (hL : toList ac.2 = p1 :: rest) :
    toList (ddOf75 w ac) =
      (p1 :: rest).map (fun p => omegaNF (plus (mulL w (subAP w ac.1)) (logOm p))) := by
  have hm : ddOf75 w ac
      = ofList ((toList ac.2).map
          (fun p => omegaNF (plus (mulL w (subAP w ac.1)) (logOm p)))) := rfl
  have hap : ∀ x ∈ ((p1 :: rest).map
      (fun p => omegaNF (plus (mulL w (subAP w ac.1)) (logOm p)))), x.isAP = true := by
    intro x hx
    obtain ⟨p, _, hp⟩ := List.mem_map.mp hx
    rw [← hp]
    exact isAP_omegaNF _
  rw [hm, hL]
  exact toList_ofList hap

/-- **§86.3 の心臓 — `aV ⊖ Ω₁ ≠ 0` なら `Δ ⊖ 1 = Δ`。**  `Δ` の先頭成分は
    `ω^(Ω_{u+1}·(aV ⊖ Ω_{u+1}) ⊕ …)` で、`Ω_{u+1}` 以上だから決して `1` にならない。 -/
theorem sub1_ddOf86 {u : Nat} {ac : Term × Term} (hnf : omegaNF (reg (u+1)) = reg (u+1))
    (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hz : ac.2 ≠ zero)
    (hs : subAP (reg (u+1)) ac.1 ≠ zero) :
    sub1 (ddOf75 (reg (u+1)) ac) = ddOf75 (reg (u+1)) ac := by
  have hwT : inT (reg (u+1)) = true := inT_reg (u+1)
  have heT : inT (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) = true :=
    inT_mulL mulDescInT hwT (inT_subAP h1)
  cases hL : toList ac.2 with
  | nil => exact absurd (toList_eq_nil _ hL) hz
  | cons p1 rest =>
    have hp1 : inT p1 = true := inTL_inT h3 p1 (by rw [hL]; exact List.Mem.head _)
    have hq : le (reg (u+1))
        (omegaNF (plus (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) (logOm p1))) = true := by
      have hA : le (reg (u+1))
          (omegaNF (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1))) = true :=
        le_reg_powOf80 hnf h1 hs
      have hB : le (omegaNF (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)))
          (omegaNF (plus (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) (logOm p1))) = true := by
        refine omegaNF_mono_inT heT (inT_plus heT (inT_logOm hp1)) ?_
        have h2 := plus_mono_right_inT _ heT zero (logOm p1) inT_zero (inT_logOm hp1)
          (le_zero_left _)
        rwa [plus_nil (show toList (zero : Term) = [] from rfl)] at h2
      exact le_trans_inT hwT (inT_omegaNF heT)
        (inT_omegaNF (inT_plus heT (inT_logOm hp1))) hA hB
    have hne : (omegaNF (plus (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) (logOm p1))
        == TM.Term.one) = false := by
      cases hb : (omegaNF (plus (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) (logOm p1))
          == TM.Term.one) with
      | false => rfl
      | true =>
        exfalso
        rw [eq_of_beq hb, le_reg_one_false86 u] at hq
        exact Bool.noConfusion hq
    show (match toList (ddOf75 (reg (u+1)) ac) with
        | [] => zero
        | p :: r => if p == TM.Term.one then ofList r else ddOf75 (reg (u+1)) ac)
      = ddOf75 (reg (u+1)) ac
    rw [toList_ddOf86 hL, List.map_cons]
    exact if_neg (fun hc => by rw [hne] at hc; exact Bool.noConfusion hc)

/-- **`aV ⊖ Ω₁ ≠ 0` なら、`Ω_{u+1}` より下の項はどちらの `K` から来ても左の枝で只。**
    §80.3 は `K_{Ω_{u+1}} aV` の元にしか言えず、しかも `Δ` までしか届かなかった。 -/
theorem lt_sub1dd_of_ltW86 {u : Nat} {ac : Term × Term}
    (hnf : omegaNF (reg (u+1)) = reg (u+1))
    (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hz : ac.2 ≠ zero)
    (hs : subAP (reg (u+1)) ac.1 ≠ zero) {y : Term}
    (hyi : inT y = true) (hlt : lt y (reg (u+1)) = true) :
    lt y (sub1 (ddOf75 (reg (u+1)) ac)) = true := by
  have hleT : le (reg (u+1)) (ddOf75 (reg (u+1)) ac) = true :=
    le_trans_inT (inT_reg (u+1)) (inT_powOf80 (inT_reg (u+1)) h1)
      (inT_ddOf75 (inT_reg (u+1)) h1 h3)
      (le_reg_powOf80 hnf h1 hs) (le_powOf_ddOf80 (inT_reg (u+1)) h1 h3 hz)
  rw [sub1_ddOf86 hnf h1 h3 hz hs]
  exact lt_of_lt_of_le3 (inT_le_fragR y hyi) (inT_le_fragR _ (inT_reg (u+1)))
    (inT_le_fragR _ (inT_ddOf75 (inT_reg (u+1)) h1 h3)) hlt hleT

/-- **§86.3 の主定理 — `Ω_{u+1}` より下の `K_{Ω_{u+1}} aV` の元は左の枝で只。**
    §80.3 の `lt_dd_of_lt_reg80` は `Δ` までしか届かなかった。側条件はいっさい要らない —
    `aV ⊖ Ω_{u+1} = 0` の枝では `K_{Ω_{u+1}} aV` がそもそも空だから。
    **残るのは `Ω_{u+1} ≤ y` の元と、`aV = Ω_{u+1}` の歩の `K_{Ω_{u+1}} cV` だけ**
    (後者はちょうど §80.4 の `LocalKSndBelow_80` が言っていた穴)。 -/
theorem lt_sub1dd_of_lt_reg86 {u : Nat} {ac : Term × Term}
    (hnf : omegaNF (reg (u+1)) = reg (u+1))
    (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hz : ac.2 ≠ zero) {y : Term}
    (hy : y ∈ Kset (reg (u+1)) ac.1) (hlt : lt y (reg (u+1)) = true) :
    lt y (sub1 (ddOf75 (reg (u+1)) ac)) = true := by
  by_cases hs : subAP (reg (u+1)) ac.1 = zero
  · exact (kset_nil_of_toList86 (subAP_eq_zero86 h1 hs) y hy).elim
  · exact lt_sub1dd_of_ltW86 hnf h1 h3 hz hs (inT_mem_Kset75 ac.1 h1 _ y hy) hlt

end

/-! ### §86.4 置き換え — 抑える相手ではなく、逃げる元の方を割る -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **逃げる元から直前の指数を引いた残り。** `y ≤ i0` なら `0`、そうでなければ
    `y` の成分列から `i0` の成分列ぶんを落としたもの。 -/
def remOf86 (i0 y : Term) : Term :=
  if le y i0 then zero else ofList ((toList y).drop (toList i0).length)

theorem remOf86_le86 {i0 y : Term} (h : le y i0 = true) : remOf86 i0 y = zero := by
  show (if le y i0 then zero else ofList ((toList y).drop (toList i0).length)) = zero
  rw [h]
  rfl

private theorem descL_drop86 : ∀ (k : Nat) (l : List Term), descL l = true →
    descL (l.drop k) = true
  | 0, _, h => h
  | _+1, [], h => h
  | k+1, a :: r, h => by
      show descL ((a :: r).drop (k+1)) = true
      rw [List.drop_succ_cons]
      exact descL_drop86 k r (descL_tail h)

private theorem inTL_drop86 (k : Nat) (l : List Term) (h : inTL l = true) :
    inTL (l.drop k) = true := by
  show (l.drop k).all _ = true
  rw [List.all_eq_true]
  intro x hx
  exact List.all_eq_true.mp h x (List.mem_of_mem_drop hx)

theorem inT_remOf86 {i0 y : Term} (hy : inT y = true) : inT (remOf86 i0 y) = true := by
  show inT (if le y i0 then zero else ofList ((toList y).drop (toList i0).length)) = true
  cases hb : le y i0 with
  | true => exact inT_zero
  | false =>
    obtain ⟨hc, hd⟩ := inT_toList y hy
    exact inT_ofList _ (inTL_drop86 _ _ hc) (descL_drop86 _ _ hd)

/-- **§86 の条項。** 一つの元 `y` について、**今の対の `Δ ⊖ 1`** が抑えるか、
    **`y` を直前の指数とその先の残りに割ったときの残りが `Δ` より下**か。
    比較の相手はどちらも単体の項のまま — 割るのは抑える相手ではなく `y` の方である。 -/
def SplitK86 (u : Nat) (x : Term) : Prop :=
  ∀ p ∈ scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1,
    le (reg (u+1)) p.2.1 = true →
      ∀ y, (y ∈ Kset (reg (u+1)) p.2.1 ∨ y ∈ Kset (reg (u+1)) p.2.2) →
        lt y (sub1 (ddOf75 (reg (u+1)) p.2)) = true ∨
        ∃ i0, p.1.1 = some i0 ∧ le y (plus i0 (remOf86 i0 y)) = true ∧
          lt (remOf86 i0 y) (ddOf75 (reg (u+1)) p.2) = true

/-- 対ひとつぶんの翻訳。左の枝は §75.2 の `le_sub1dd_idxOf75`、右の枝は §79.3 の
    `plus_smono_right_inT79` — 新しく要る順序の事実はこれ一つだけ。 -/
theorem idx_of_split86 {u : Nat} {s : Option Term × Option Term} {ac : Term × Term}
    (hs : StInv s) (h1 : inT ac.1 = true) (h2 : lt ac.1 M = true)
    (h3 : inT ac.2 = true) (h4 : lt ac.2 M = true)
    (hsp : ∀ y, (y ∈ Kset (reg (u+1)) ac.1 ∨ y ∈ Kset (reg (u+1)) ac.2) →
        lt y (sub1 (ddOf75 (reg (u+1)) ac)) = true ∨
        ∃ i0, s.1 = some i0 ∧ le y (plus i0 (remOf86 i0 y)) = true ∧
          lt (remOf86 i0 y) (ddOf75 (reg (u+1)) ac) = true) :
    ∀ y, (y ∈ Kset (reg (u+1)) ac.1 ∨ y ∈ Kset (reg (u+1)) ac.2) →
      lt y (idxOf (reg (u+1)) s ac) = true := by
  have hw : inT (reg (u+1)) = true := inT_reg (u+1)
  have hlw : lt (reg (u+1)) M = true := ltM_reg (u+1)
  have hdT : inT (ddOf75 (reg (u+1)) ac) = true := inT_ddOf75 hw h1 h3
  obtain ⟨hidxT, _⟩ := inT_idxOf mulDescInT hw hlw hs h1 h2 h3 h4
  intro y hy
  have hyi : inT y = true := by
    rcases hy with hy | hy
    · exact inT_mem_Kset75 ac.1 h1 _ y hy
    · exact inT_mem_Kset75 ac.2 h3 _ y hy
  rcases hsp y hy with hL | ⟨i0, hs1, hle, hlr⟩
  · exact lt_of_lt_of_le3 (inT_le_fragR y hyi) (inT_le_fragR _ (inT_sub1 hdT))
      (inT_le_fragR _ hidxT) hL (le_sub1dd_idxOf75 hw hs h1 h3)
  · have hi0 : inT i0 = true := (hs.1 i0 hs1).1
    have hr : inT (remOf86 i0 y) = true := inT_remOf86 hyi
    have hidx : idxOf (reg (u+1)) s ac = plus i0 (ddOf75 (reg (u+1)) ac) := by
      show (match s.1 with
            | none => sub1 (mulL (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) ac.2)
            | some j => plus j (mulL (mulL (reg (u+1)) (subAP (reg (u+1)) ac.1)) ac.2)) = _
      rw [hs1]
      try rfl
    rw [hidx]
    exact lt_of_le_of_lt3 (inT_le_fragR y hyi) (inT_le_fragR _ (inT_plus hi0 hr))
      (inT_le_fragR _ (inT_plus hi0 hdT)) hle
      (plus_smono_right_inT79 i0 hi0 _ _ hr hdT hlr)

/-- **§86.4 の主定理。** 置き換えた条項から `KsetStepOK`。 -/
theorem ksetStepOK_of_split86 (u : Nat) (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (H : SplitK86 u x) : KsetStepOK u x := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨_, hallOK⟩ :=
    wcnf_spec_sc (inT_reg (u+1)) (isSC_reg_succ u) (toList x) hc hd (ltM_toList x hx hlx)
  intro p hp hle
  refine scan_idx84 (wcnf (reg (u+1)) (toList x)).1 (none, none)
    stInv_none (kInv75_none u) hallOK ?_ p hp hle
  intro q hq hle2 hst
  have hmem : q.2 ∈ (wcnf (reg (u+1)) (toList x)).1 :=
    scanSt_mem_snd _ _ _ _ q hq
  obtain ⟨hi1, hl1, hi2, hl2⟩ := hallOK q.2 hmem
  exact idx_of_split86 hst hi1 hl1 hi2 hl2 (H q hq hle2)

theorem idxK84_of_split86 (u : Nat) (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (H : SplitK86 u x) : IdxK84 u x :=
  idxK84_of_ksetStepOK (ksetStepOK_of_split86 u x hx hlx H)

/-- **置き換えは §84 の条項より弱い。** 右の枝は残り `0` を取ればよく、
    `lt 0 Δ` は §84.2 の `ddOf_ne_zero84` である。 -/
theorem split86_of_split84 {u : Nat} {x : Term} (hx : inT x = true) (hlx : lt x M = true)
    (H : SplitK84 u x) : SplitK86 u x := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  have hnz := wcnf_snd_ne_zero84 (inT_reg (u+1)) (isSC_reg_succ u) (toList x) hc hd
    (ltM_toList x hx hlx)
  intro p hp hle y hy
  rcases H p hp hle y hy with h | ⟨i0, hs1, hle2⟩
  · exact Or.inl h
  · refine Or.inr ⟨i0, hs1, ?_, ?_⟩
    · rw [remOf86_le86 hle2, plus_nil (show toList (zero : Term) = [] from rfl)]
      exact hle2
    · rw [remOf86_le86 hle2]
      exact lt_zero_left
        (ddOf_ne_zero84 (hnz p.2 (scanSt_mem_snd _ _ _ _ p hp)))

/-- §75 の対ごとの条件も、もちろん置き換えた条項より強い。 -/
theorem split86_of_local75 {u : Nat} {x : Term} (hx : inT x = true) (hlx : lt x M = true)
    (H : LocalK75 u x) : SplitK86 u x :=
  split86_of_split84 hx hlx (split84_of_local75 H)

/-- 置き換えた条項の判定器。 -/
def splitb86 (u : Nat) (x : Term) : Bool :=
  (scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1).all fun p =>
    !(le (reg (u+1)) p.2.1) ||
      ((Kset (reg (u+1)) p.2.1 ++ Kset (reg (u+1)) p.2.2).all fun y =>
        lt y (sub1 (ddOf75 (reg (u+1)) p.2)) ||
          (match p.1.1 with
           | none => false
           | some i0 => le y (plus i0 (remOf86 i0 y)) &&
               lt (remOf86 i0 y) (ddOf75 (reg (u+1)) p.2)))

theorem splitK86_of_b86 {u : Nat} {x : Term} (h : splitb86 u x = true) : SplitK86 u x := by
  intro p hp hle y hy
  have h1 := List.all_eq_true.mp
    (show (scanSt (reg (u+1)) (baseOf u) (none, none)
        (wcnf (reg (u+1)) (toList x)).1).all (fun p =>
      !(le (reg (u+1)) p.2.1) ||
        ((Kset (reg (u+1)) p.2.1 ++ Kset (reg (u+1)) p.2.2).all fun y =>
          lt y (sub1 (ddOf75 (reg (u+1)) p.2)) ||
            (match p.1.1 with
             | none => false
             | some i0 => le y (plus i0 (remOf86 i0 y)) &&
                 lt (remOf86 i0 y) (ddOf75 (reg (u+1)) p.2)))) = true from h) p hp
  rw [hle, Bool.not_true, Bool.false_or] at h1
  have h2 := List.all_eq_true.mp h1 y (by
    rcases hy with hy | hy
    · exact List.mem_append.mpr (Or.inl hy)
    · exact List.mem_append.mpr (Or.inr hy))
  cases h3 : lt y (sub1 (ddOf75 (reg (u+1)) p.2)) with
  | true => exact Or.inl rfl
  | false =>
    rw [h3, Bool.false_or] at h2
    cases hq : p.1.1 with
    | none => rw [hq] at h2; exact Bool.noConfusion h2
    | some i0 =>
      rw [hq] at h2
      exact Or.inr ⟨i0, rfl, ((Bool.and_eq_true _ _).mp h2).1,
        ((Bool.and_eq_true _ _).mp h2).2⟩

/-- **判定器は条項と過不足なく同値。** だから `false` は反証である。 -/
theorem b86_of_splitK86 {u : Nat} {x : Term} (H : SplitK86 u x) : splitb86 u x = true := by
  show (scanSt (reg (u+1)) (baseOf u) (none, none)
      (wcnf (reg (u+1)) (toList x)).1).all (fun p =>
    !(le (reg (u+1)) p.2.1) ||
      ((Kset (reg (u+1)) p.2.1 ++ Kset (reg (u+1)) p.2.2).all fun y =>
        lt y (sub1 (ddOf75 (reg (u+1)) p.2)) ||
          (match p.1.1 with
           | none => false
           | some i0 => le y (plus i0 (remOf86 i0 y)) &&
               lt (remOf86 i0 y) (ddOf75 (reg (u+1)) p.2)))) = true
  refine List.all_eq_true.mpr ?_
  intro p hp
  cases hle : le (reg (u+1)) p.2.1 with
  | false => rfl
  | true =>
    rw [Bool.not_true, Bool.false_or]
    refine List.all_eq_true.mpr ?_
    intro y hy
    have hy' : (y ∈ Kset (reg (u+1)) p.2.1 ∨ y ∈ Kset (reg (u+1)) p.2.2) := by
      rcases List.mem_append.mp hy with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases H p hp hle y hy' with h | ⟨i0, hs1, hle2, hlr⟩
    · rw [h]; rfl
    · rw [hs1]
      show (lt y (sub1 (ddOf75 (reg (u+1)) p.2)) ||
        (le y (plus i0 (remOf86 i0 y)) && lt (remOf86 i0 y) (ddOf75 (reg (u+1)) p.2))) = true
      rw [hle2, hlr]
      exact Bool.or_true _

end

/-! ### §86.5 組み立て — 326 行目は置き換えた条項ひとつを待つ -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§86 の残る仮説。** 部分領域の項について置き換えた条項。**証明しない。** -/
def SplitStd86 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true →
    inT (dict a) = true → lt (dict a) M = true → SplitK86 0 (dict a)

theorem idxStd84_of_split86 (H : SplitStd86) : IdxStd84 :=
  fun a hb hs hi hl => idxK84_of_split86 0 (dict a) hi hl (H a hb hs hi hl)

/-- **§86 の第一の結論。** §73 の残る門は置き換えた条項から出る。 -/
theorem psiIdxStep073_of_split86 (H : SplitStd86) : PsiIdxStep073 :=
  psiIdxStep073_of_idx84 (idxStd84_of_split86 H)

/-- **§86 の第二の結論。** 326 行目の証明書が `K` の側で待つのは置き換えた条項ひとつ。 -/
theorem certIn_t326_split86 (H : SplitStd86)
    (HD : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_step73 (psiIdxStep073_of_split86 H) HD HI HC hacc

/-- **落ちない方。** `bad86` でも `aBad82` でも置き換えた条項は通る。 -/
theorem split86_bad86 : SplitK86 0 (dict bad86) := splitK86_of_b86 (by decide)
theorem split86_aBad82 : SplitK86 0 (dict aBad82) := splitK86_of_b86 (by decide)

end

/-! ### §86.6 測定 (凍結)

**構成を先に書く。**  §84 の `famC84` — `h ⊕ ψ₁^m(ψ₀(h ⊕ g))` — は**形は正しく、幅が
足りなかった**。そこでは帽子 `ψ₁^m` が `m ≤ 2` まで、引数の第二成分 `g` が `ψ₁ψ₁0` まで
しか動かない。ところが `ψ₁` の塔は**三段目からしか走査の歩として発火しない**
(`ψ₁ψ₁ψ₁0` の `wA` がちょうど `Ω₁`)。だから §84 の母集団では、`ψ₀` の引数の走査は
頭ぶんの指数から一歩も先へ進めず、逃げる元は `y ≤ i0` を超えられなかった。
§86 の母集団は両方を三段目まで開ける。

    twr86 k      = ψ₁^k 0
    cp86 m a     = ψ₁^m a          (h = twr86 k, g = twr86 j と書く)
    famU86  h ⊕ ψ₁^m(ψ₀(h ⊕ g))                     24 個  ← `bad86` は (k,m,j)=(4,3,3)
    famV86  h ⊕ ψ₁^m(ψ₀(h ⊕ g)) ⊕ g                 16 個  (三項和)
    famW86  h ⊕ ψ₁^m(ψ₀(h ⊕ g ⊕ g))                 16 個  (引数が三成分)
    famX86  h ⊕ h ⊕ ψ₁^m(ψ₀(h ⊕ h ⊕ g))             16 個  (走査が併合する枝)
    famY86  h ⊕ h' ⊕ ψ₁^m(ψ₀(h ⊕ g))                18 個  (引数が中項を飛ばす)
    famZ86  h ⊕ ψ₁^m(ψ₀(h ⊕ ψ₀(h ⊕ g)))              6 個  (`ψ₀` が二重)
    pop86   = 上の和集合、重複を除いて                96 個
    qual86  = そのうち条項の仮説をぜんぶ満たすもの    53 個

**測定の結果。**

  * **§84 の分割条項は偽。**  `qual86` の 53 項のうち **10 項**で `splitb84` が落ちる
    (`famU86` 4・`famV86` 2・`famW86` 2・`famX86` 2、`famY86` と `famZ86` は 0)。
    `bad86` はその最小 (記号 20 個、`aBad82` は 15 個)。§75 の対ごとの条件は同じ母集団で
    31 項落ちる。
  * **門は落ちない。**  `idxb84` と `stepOKb` は `qual86` の 53 項で失敗 **0**。
    消えたのは局所化であって門ではない。
  * **逃げる元の内訳が §84 の想定を割る。**  53 項の 95 の発火歩で、左の枝が落ちる元は
    31。うち **`y < i0` が 3、`y = i0` が 18、そして `y > i0` が 10** —
    §84 の右の枝 `y ≤ i0` はその 10 で足りない。**31 のぜんぶが §86 の割り方
    (`y ≤ i0 ⊕ (y ⊖ i0)` かつ `y ⊖ i0 < Δ`) を満たす。**  `splitb86` は 53 項で失敗 0。
  * **`Ω₁` より下の元はこの母集団に一つも無い。**  31 の逃げる元はぜんぶ `Ω₁` 以上で、
    §86.3 が只で片づける枝はここでは空回りする。§86.3 が効くのは §80.7 が数えた
    458/635 の歩の方であって、この母集団ではない。
  * **326 行目は何も変わらない。**  `regPairs72 ([t326] ++ exp72)` の 41 個の添字で
    `splitb84`・`splitb86`・`idxb84`・`stepOKb` はぜんぶ失敗 0。§84 の母集団 `qual84`
    の 53 項でも `splitb84`・`splitb86` はどちらも失敗 0 — **反証は条項についてであって、
    行についてではない。** -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

def twr86 : Nat → BT
  | 0 => BT.zero
  | k+1 => BT.D 1 (twr86 k)
def cp86 : Nat → BT → BT
  | 0, a => a
  | m+1, a => BT.D 1 (cp86 m a)

def famU86 : List BT :=
  (List.range 2).flatMap fun k => (List.range 3).flatMap fun m => (List.range 4).map fun j =>
    BT.sum (twr86 (k+4)) (cp86 (m+2) (BT.D 0 (BT.sum (twr86 (k+4)) (twr86 (j+1)))))
def famV86 : List BT :=
  (List.range 2).flatMap fun k => (List.range 2).flatMap fun m => (List.range 4).map fun j =>
    BT.sum (twr86 (k+4)) (BT.sum (cp86 (m+2) (BT.D 0 (BT.sum (twr86 (k+4)) (twr86 (j+1)))))
      (twr86 (j+1)))
def famW86 : List BT :=
  (List.range 2).flatMap fun k => (List.range 2).flatMap fun m => (List.range 4).map fun j =>
    BT.sum (twr86 (k+4)) (cp86 (m+2) (BT.D 0
      (BT.sum (twr86 (k+4)) (BT.sum (twr86 (j+1)) (twr86 (j+1))))))
def famX86 : List BT :=
  (List.range 2).flatMap fun k => (List.range 2).flatMap fun m => (List.range 4).map fun j =>
    BT.sum (twr86 (k+4)) (BT.sum (twr86 (k+4)) (cp86 (m+2) (BT.D 0
      (BT.sum (twr86 (k+4)) (BT.sum (twr86 (k+4)) (twr86 (j+1)))))))
def famY86 : List BT :=
  (List.range 2).flatMap fun m => (List.range 3).flatMap fun i => (List.range 3).map fun j =>
    BT.sum (twr86 5) (BT.sum (twr86 (i+2))
      (cp86 (m+2) (BT.D 0 (BT.sum (twr86 5) (twr86 (j+1))))))
def famZ86 : List BT :=
  (List.range 2).flatMap fun m => (List.range 3).map fun j =>
    BT.sum (twr86 5) (cp86 (m+2) (BT.D 0
      (BT.sum (twr86 5) (BT.D 0 (BT.sum (twr86 5) (twr86 (j+1)))))))

def pop86 : List BT :=
  (famU86 ++ famV86 ++ famW86 ++ famX86 ++ famY86 ++ famZ86).eraseDups
def qual86 : List BT := pop86.filter okHyp84

-- 母集団の大きさ。
#guard (pop86.length, qual86.length) == (96, 53)
#guard (bad86.size, aBad82.size) == (20, 15)

/-! **否定 — §84 の分割条項は落ちる。** 落ちるのは `ψ₀` の引数の第二成分が発火する塔の
ときだけで、`bad86` はそこの最小。§75 の対ごとの条件も同じところで落ちる。 -/

#guard splitb84 0 (dict bad86) == false
#guard localOKb73 0 (dict bad86) == false
#guard (qual86.filter fun a => !(splitb84 0 (dict a))).length == 10
#guard (qual86.filter fun a => !(localOKb73 0 (dict a))).length == 31
#guard ((famU86.filter fun a => okHyp84 a && !(splitb84 0 (dict a))).length,
        (famV86.filter fun a => okHyp84 a && !(splitb84 0 (dict a))).length,
        (famW86.filter fun a => okHyp84 a && !(splitb84 0 (dict a))).length,
        (famX86.filter fun a => okHyp84 a && !(splitb84 0 (dict a))).length,
        (famY86.filter fun a => okHyp84 a && !(splitb84 0 (dict a))).length,
        (famZ86.filter fun a => okHyp84 a && !(splitb84 0 (dict a))).length)
       == (4, 2, 2, 2, 0, 0)

/-! **肯定 1 — 門は落ちない。置き換えた条項も落ちない。** -/

#guard (idxb84 0 (dict bad86), stepOKb 0 (dict bad86), splitb86 0 (dict bad86))
       == (true, true, true)
#guard (qual86.filter fun a => !(idxb84 0 (dict a))).length == 0
#guard (qual86.filter fun a => !(stepOKb 0 (dict a))).length == 0
#guard (qual86.filter fun a => !(splitb86 0 (dict a))).length == 0

/-! **肯定 2 — 逃げる元の内訳。** 95 の発火歩に 31 の逃げる元。`y < i0` が 3、
`y = i0` が 18、**`y > i0` が 10** — §84 の右の枝はその 10 で足りない。
31 のぜんぶが §86 の割り方を満たし、31 のぜんぶが `Ω₁` 以上 (だから §86.3 の枝は
この母集団では空回りする)。 -/

#guard
  (let fires := qual86.flatMap fun a =>
     (scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1).filter
       (fun p => le (reg 1) p.2.1)
   let bad := fires.flatMap fun p =>
     (Kset (reg 1) p.2.1 ++ Kset (reg 1) p.2.2).filterMap fun y =>
       if lt y (sub1 (ddOf75 (reg 1) p.2)) then none else some (p, y)
   (fires.length, bad.length,
    (bad.filter fun q => match q.1.1.1 with
      | none => false | some i0 => lt q.2 i0).length,
    (bad.filter fun q => match q.1.1.1 with
      | none => false | some i0 => q.2 == i0).length,
    (bad.filter fun q => match q.1.1.1 with
      | none => false | some i0 => lt i0 q.2).length,
    (bad.filter fun q => match q.1.1.1 with
      | none => false
      | some i0 => le q.2 (plus i0 (remOf86 i0 q.2)) &&
          lt (remOf86 i0 q.2) (ddOf75 (reg 1) q.1.2)).length,
    (bad.filter fun q => le (reg 1) q.2).length)) == (95, 31, 3, 18, 10, 31, 31)

/-! **肯定 3 — 326 行目とその基本列、そして §84 の母集団。** どちらでも
`splitb84` も `splitb86` も落ちない。反証は条項についてであって、行についてではない。 -/

#guard (r326_84.filter fun q => !(splitb84 q.1 (dict q.2))).length == 0
#guard (r326_84.filter fun q => !(splitb86 q.1 (dict q.2))).length == 0
#guard (r326_84.filter fun q => !(stepOKb q.1 (dict q.2))).length == 0
#guard (qual84.filter fun a => !(splitb86 0 (dict a))).length == 0
#guard (qual84.filter fun a => !(splitb84 0 (dict a))).length == 0

-- (重い測定。数は §86 の前書きに記録。凍結すると library の build が伸びるので外す。)
-- #guard (refFam82.filter fun a => !(splitb84 0 (dict a))).length == 0
-- #guard (refFam82.filter fun a => !(splitb86 0 (dict a))).length == 0
-- #guard (refFam82.filter fun a => !(localOKb73 0 (dict a))).length == 690
-- #guard ((regPairs72 (sub72 8)).filter fun q => !(splitb86 q.1 (dict q.2))).length == 0

end

/-! ### §86.7 公理 -/

/-! ## §85 THE DENSITY CLAUSE IS THE DENSITY OF `dict`'S IMAGE — THE BMS SIDE IS A THEOREM

Row 326's certificate stands on three hypotheses (§83.7): `PsiIdxOKStd172`, `DictLtA74` and
`CofDenseS1`.  §83 proved the Buchholz half of §71.4's split and then proved that the split
has nothing left to give — under the bridge, `CofDenseS1` and `LimCofS1` are the same
statement.  What §83 named as the missing thing was **a partial inverse of `dict` on the
initial segment below a region value**: given `s < vOf t` with `t` in the sub-region, produce
a Buchholz term whose image dominates `s`, or produce the index directly.

That map has two halves — 𝔗(M) → Buchholz and Buchholz → BMS.  §85 builds the SECOND half
and proves it correct, and what is left over is the first half and nothing else.

  §85.1  **THE INVERSE OF `bValA71`.**  `bInv85 : BT → B` reads a Buchholz term as an index:
         a component `D u a` becomes a block of level `u` whose argument is `bInv85 a`, and a
         sum becomes the blocks side by side.  `toL_bInv85` says the node list of the result
         is the component list of the input, node for node, and `bVal_bInv85` says
         `bValA71 (bInv85 b) = b` for every standard `b` of level ≤ 1.  The level bound is
         what makes that work, and it is §71.6's fact: at level ≤ 1 the collapsing branch of
         `bK` is dead, so `bArg w c = bValA71 c` and a block's value is the block.

  §85.2  **THE TWO TRANSFERS OF §72, BACKWARDS.**  §72.2 carried the `cmpS` order to the `BT`
         order and §72.4 carried `visOK` to the `GB` condition; the inverse needs both the
         other way.  `argTransfer85` is §72.2 run backwards — by trichotomy, on §74's
         asymmetry — and `gb_bArg85` is `mem_GB_bArg72` backwards: every node `gbL72`
         descends through contributes its argument to `GB`.  `visOK_of_gb85` rebuilds
         `visOK` from the node-by-node statement, and it is cheaper than the forward
         direction because `GB v` collects every node of level ≥ v while `visOK v` asks
         about the nodes of level exactly `v`.

  §85.3  **STANDARDNESS TRANSFERS BACKWARDS TOO — AND THAT IS THE THEOREM.**
         `bOnto85`, **with no unproved hypothesis**: if `b` is a standard Buchholz term of
         level ≤ 1 whose components are all `D 0`, then `b = bValA71 u` for an index `u` that
         is IN THE SUB-REGION, `stdB1 u = true`.  `nfB` comes from the head condition,
         `nonIncr` from the descending components, `stdIn` from the `GB` condition
         through §85.2.  This is
         the converse of §67's `RegionStd`, which is still an unproved hypothesis in the
         forward direction; backwards, at level one, it is a theorem.

  §85.4  **THE HEAD CONDITION IS FREE.**  `Hd085 b` — every component of `b` is a `D 0` — is
         not an extra assumption on a challenger: a value of the region has it
         (`hd085_bValA71_85`, straight from `nfB`), and anything standard and `BT.lt`-below
         such a value has it too (`hd085_of_lt85`), because `D 0` is the smallest head and
         the components descend.

  §85.5  **THE EQUIVALENCE.**  `cofDenseS1_iff_dictDense85 (Hp : PsiIdxOKStd172) :
         CofDenseS1 ↔ DictDense85`, where `DictDense85` says: for every limit index `t` of
         the sub-region and every `s` of 𝔗(M) below `vOf t` there is a standard Buchholz
         term `b` of level ≤ 1, head `D 0`, with `s ≤ dict b` and `dict b < vOf t`.
         **No BMS standardness, no fundamental sequence and no `bValA71` occurs in it** —
         only `dict`, `inT`, `lt`, and the single term `vOf t`.  Neither direction uses the
         bridge: `PsiIdxOKStd172` enters only through §76's `vOfIsDict76`
         (`vOf = dict ∘ bValA71` on the sub-region).  `certIn_t326_85` is row 326's
         certificate with `DictDense85` in place of `CofDenseS1`, still three hypotheses.

  §85.6  **WHAT CANNOT BE DROPPED.**  `Ω = ψ₁(0)` is a standard Buchholz term of level ≤ 1
         and it is the value of NO index at all (`not_bValA71_om85`), so the head condition
         is not removable from `bOnto85`.  One level up the clause itself is false:
         `not_cofDense_and_cofIn85` proves from §69's `CofGap` that the unrestricted density
         and the unrestricted inner cofinality cannot both hold, and `sbad_no_witness85`
         localises the failure at §69's own witness — given inner cofinality, no standard
         index has a value in `[sbad, vOf tdiag)`.  The level bound is therefore not
         decoration: §85 spends it twice, at `bArg = bValA71` and in the §72 transfers, and
         one level up the statement it is proving a half of is refuted.  §85.7 measures the
         sharp form of that: `dictInv sbad = ψ₀(ψ₁(Ω₂))`, so §69's escaping term DOES have a
         Buchholz preimage and the preimage **carries a level-2 node** (and is not even
         standard).  That is precisely why `bOnto85` cannot reach it.

  §85.7  The measurement (frozen), and the one place it earns its keep: `φ̄(ψ_Ω(0),0)` is a
         term of 𝔗(M) that `dict` does not produce at all (`dictInv` answers `none`) and that
         sits below a limit value of the sub-region.  No index of the 609-term enumeration
         `subP 7` dominates it below that value — and `bInv85` builds one anyway, from the
         Buchholz side, in one line: `(0,0)(1,1)(2,1)(3,1)(1,1)(2,1)(3,1)`, value `ψ_Ω(1)`.
         That is the whole point of the map, and it is also why `DictDense85` says
         `s ≤ dict b` and not `s = dict b`: `dict` is not onto 𝔗(M).  §85.8 the axioms.

WHAT IS **NOT** CLAIMED.  `DictDense85` is NOT proved, `CofDenseS1` is NOT closed, and row
326 still stands on three hypotheses.  §85 MOVES the open clause; it does not discharge it.
What used to be a statement about BMS indices, their standardness and their fundamental
sequences is now a statement about the image of `dict` and nothing else — and the direction
that remains is the one that has to read an arbitrary term of 𝔗(M), which is exactly where
§83 stopped.  Nothing here says `dict` is onto anything: `Trans/DictInv.lean` builds a
candidate partial inverse `dictInv` and measures it (336 Buchholz terms exact, 60 table rows,
750 CNV terms), and that record is evidence for `DictDense85`, not a proof of it.  Nothing
here is a statement about level two, where the clause is false. -/

/-! ### §85.1 `bValA71` の逆写像

段 1 以下では `bArg` の潰す枝が死んでいる (§71.6) ので、成分 `D u a` は「段 `u` の節、
引数は `a` の逆像」にそのまま戻る。和は節を横に並べたものになる。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

def bInvA85 : B → BT → B
  | acc, .zero => acc
  | acc, .D u a => .nd u acc (bInvA85 .nil a)
  | acc, .sum x y => bInvA85 (bInvA85 acc x) y

def bInv85 (b : BT) : B := bInvA85 .nil b

def g85 : BT → Nat × B
  | .D u a => (u, bInv85 a)
  | _ => (0, .nil)

theorem toL_bInvA85 : ∀ (b : BT) (acc : B),
    toL (bInvA85 acc b) = toL acc ++ b.toL.map g85
  | .zero, acc => by
      show toL acc = toL acc ++ ([] : List (Nat × B))
      rw [List.append_nil]
  | .D u a, acc => by
      show toL (B.nd u acc (bInv85 a)) = toL acc ++ [(u, bInv85 a)]
      rw [toL_nd]
  | .sum x y, acc => by
      show toL (bInvA85 (bInvA85 acc x) y) = toL acc ++ (x.toL ++ y.toL).map g85
      rw [toL_bInvA85 y (bInvA85 acc x), toL_bInvA85 x acc, List.map_append,
        List.append_assoc]

theorem toL_bInv85 (b : BT) : toL (bInv85 b) = b.toL.map g85 := by
  show toL (bInvA85 .nil b) = _
  rw [toL_bInvA85 b .nil]
  rfl

theorem lvlLe_bInvA85 : ∀ (b : BT) (acc : B), btLe72 1 b = true → lvlLe 1 acc = true →
    lvlLe 1 (bInvA85 acc b) = true
  | .zero, acc, _, ha => ha
  | .D u a, acc, hb, ha => by
      obtain ⟨hu, hba⟩ := btLe72_D 1 u a hb
      exact (lvlLe_nd_iff 1 u acc (bInvA85 .nil a)).mpr ⟨hu, ha, lvlLe_bInvA85 a .nil hba rfl⟩
  | .sum x y, acc, hb, ha => by
      have hb' : (btLe72 1 x && btLe72 1 y) = true := hb
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hb'
      exact lvlLe_bInvA85 y _ h2 (lvlLe_bInvA85 x acc h1 ha)

theorem lvlLe_bInv85 (b : BT) (hb : btLe72 1 b = true) : lvlLe 1 (bInv85 b) = true :=
  lvlLe_bInvA85 b .nil hb rfl

/-! 大きさ — 成分の引数は元の項より小さい。強い帰納法の尺度。 -/

theorem size_mem_toL85 : ∀ (b x : BT), x ∈ b.toL → x.size ≤ b.size
  | .zero, x, hx => by cases hx
  | .D u a, x, hx => by
      rw [List.mem_singleton.mp hx]
      exact Nat.le_refl _
  | .sum p q, x, hx => by
      have hx' : x ∈ p.toL ++ q.toL := hx
      have e : (BT.sum p q).size = 1 + p.size + q.size := rfl
      rcases List.mem_append.mp hx' with h | h
      · have := size_mem_toL85 p x h; omega
      · have := size_mem_toL85 q x h; omega

theorem mapmap85 : ∀ (l : List BT), (∀ x ∈ l, fB72 (g85 x) = x) → (l.map g85).map fB72 = l
  | [], _ => rfl
  | x :: r, h => by
      show fB72 (g85 x) :: (r.map g85).map fB72 = x :: r
      rw [h x (List.mem_cons.mpr (Or.inl rfl)),
        mapmap85 r (fun z hz => h z (List.mem_cons.mpr (Or.inr hz)))]

/-- **右逆。** 段 1 以下の標準な Buchholz 項は、部分領域の形の添字の値として現れる。 -/
theorem bVal_bInv85 : ∀ (n : Nat) (b : BT), b.size < n → btLe72 1 b = true →
    BT.isStd b = true → bValA71 (bInv85 b) = b
  | 0, _, hs, _, _ => absurd hs (Nat.not_lt_zero _)
  | n + 1, b, hsz, hb, hstd => by
      obtain ⟨hat, hcs, hcb, _⟩ := good_toL77 b hstd hb
      have hpt : ∀ x ∈ b.toL, fB72 (g85 x) = x := by
        intro x hx
        obtain ⟨u, a, rfl⟩ := hat x hx
        obtain ⟨_, hba⟩ := btLe72_D 1 u a (hcb _ hx)
        have hsa : BT.isStd a = true := isStd_of_D (hcs _ hx)
        have hszx : (BT.D u a).size ≤ b.size := size_mem_toL85 b _ hx
        have hsza : a.size < n := by
          have e : (BT.D u a).size = 1 + a.size := rfl
          omega
        show BT.D u (bArg u (bInv85 a)) = BT.D u a
        rw [bArg_eq_bValA71_71 (bInv85 a) u (lvlLe_bInv85 a hba),
          bVal_bInv85 n a hsza hba hsa]
      have h1 : (bValA71 (bInv85 b)).toL = b.toL := by
        rw [toL_bValA71_map83, toL_bInv85 b, mapmap85 b.toL hpt]
      calc bValA71 (bInv85 b) = BT.ofL ((bValA71 (bInv85 b)).toL) := (nfSum_bValA7174 _).symm
        _ = BT.ofL b.toL := by rw [h1]
        _ = b := ofL_toL77 b hstd

end

/-! ### §85.2 §72 の二つの移送を逆向きに

§72.2 は `cmpS` の順序を `BT` の順序へ、§72.4 は `visOK` を `GB` の条項へ運んだ。
逆写像はその両方を逆に要る。順序の側は三分法で出る (§74 の反対称律)。`GB` の側は
`gbL72` が降りる節の引数が `GB` に入ることで、`visOK` はそこから組み直せる。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- **移送の逆向き。** 段 1 以下なら `BT.lt` は `cmpS` の `lt` に戻る。 -/
theorem argTransfer85 (w1 w2 : Nat) (c1 c2 : B)
    (h1 : lvlLe 1 c1 = true) (h2 : lvlLe 1 c2 = true)
    (h : BT.lt (bArg w1 c1) (bArg w2 c2) = true) : cmpS (toL c1) (toL c2) = Ordering.lt := by
  cases hc : cmpS (toL c1) (toL c2) with
  | lt => rfl
  | eq =>
      have he : c1 = c2 := toL_inj c1 c2 (cmpS_eq_imp _ _ hc)
      rw [he, bArg_indep72 w1 w2 c2 h2, lt_irrefl74] at h
      exact absurd h (by intro hcc; exact Bool.noConfusion hcc)
  | gt =>
      have hb := argTransfer72 w2 w1 c2 c1 h2 h1 (cmpS_gt_lt hc)
      rw [lt_asymm74 hb] at h
      exact absurd h (by intro hcc; exact Bool.noConfusion hcc)

/-- `GB` は和の成分から上へ。`mem_GB_ofL72` の逆向き。 -/
theorem GB_ofL_mem85 : ∀ (w : Nat) (l : List BT) (x : BT), x ∈ l →
    ∀ e ∈ BT.GB w x, e ∈ BT.GB w (BT.ofL l)
  | _, [], _, hx, _, _ => by cases hx
  | w, [a], x, hx, e, he => by
      rw [List.mem_singleton.mp hx] at he
      exact he
  | w, a :: y :: r, x, hx, e, he => by
      show e ∈ BT.GB w a ++ BT.GB w (BT.ofL (y :: r))
      rcases List.mem_cons.mp hx with h | h
      · rw [h] at he; exact List.mem_append.mpr (Or.inl he)
      · exact List.mem_append.mpr (Or.inr (GB_ofL_mem85 w (y :: r) x h e he))

/-- **`gbL72` の節は `GB` に入る。** `mem_GB_bArg72` の逆向き。 -/
theorem gb_bArg85 : ∀ (w : Nat) (c : B), lvlLe 1 c = true → ∀ q ∈ gbL72 w c,
    ∃ x ∈ (toL c).map fB72, bArg q.1 q.2 ∈ BT.GB w x := by
  intro w c
  induction c with
  | nil => intro _ q hq; cases hq
  | nd u r a ihr iha =>
      intro hl q hq
      obtain ⟨hu, hlr, hla⟩ := (lvlLe_nd_iff 1 u r a).mp hl
      have hq2 : q ∈ gbL72 w r ++ (if w ≤ u then (u, a) :: gbL72 w a else []) := hq
      rw [toL_nd, List.map_append]
      rcases List.mem_append.mp hq2 with h | h
      · obtain ⟨x, hxm, hex⟩ := ihr hlr q h
        exact ⟨x, List.mem_append.mpr (Or.inl hxm), hex⟩
      · by_cases hw : w ≤ u
        · rw [if_pos hw] at h
          refine ⟨fB72 (u, a), List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))), ?_⟩
          rw [show fB72 (u, a) = BT.D u (bArg u a) from rfl, GB_D72, if_pos hw]
          rcases List.mem_cons.mp h with h | h
          · rw [h]; exact List.mem_cons.mpr (Or.inl rfl)
          · obtain ⟨x', hx', he'⟩ := iha hla q h
            refine List.mem_cons.mpr (Or.inr ?_)
            rw [ofL_bArg72 u a hla]
            exact GB_ofL_mem85 w _ x' hx' _ he'
        · rw [if_neg hw] at h; cases h

/-- 節の条件から `visOK`。`visOK1_mem72` の逆向き、段によらない。 -/
theorem visOK_of_gb85 : ∀ (v : Nat) (c t : B),
    (∀ q ∈ gbL72 v t, cmpS (toL q.2) (toL c) = Ordering.lt) → visOK v c t = true := by
  intro v c t
  induction t with
  | nil => intro _; rfl
  | nd u r a ihr iha =>
      intro h
      have hr : ∀ q ∈ gbL72 v r, cmpS (toL q.2) (toL c) = Ordering.lt := by
        intro q hq
        exact h q (List.mem_append.mpr (Or.inl hq))
      show (visOK v c r &&
        (if u < v then true
         else (if u == v then cmpS (toL a) (toL c) == Ordering.lt else true)
              && visOK v c a)) = true
      rw [ihr hr, Bool.true_and]
      by_cases hlt : u < v
      · rw [if_pos hlt]
      · rw [if_neg hlt]
        have hw : v ≤ u := by omega
        have hmem : ∀ q : Nat × B, q ∈ (u, a) :: gbL72 v a →
            cmpS (toL q.2) (toL c) = Ordering.lt := by
          intro q hq
          refine h q (List.mem_append.mpr (Or.inr ?_))
          rw [if_pos hw]
          exact hq
        have ha : ∀ q ∈ gbL72 v a, cmpS (toL q.2) (toL c) = Ordering.lt :=
          fun q hq => hmem q (List.mem_cons.mpr (Or.inr hq))
        rw [iha ha, Bool.and_true]
        by_cases he : (u == v) = true
        · rw [if_pos he]
          have hkey := hmem (u, a) (List.mem_cons.mpr (Or.inl rfl))
          rw [show ((u, a) : Nat × B).2 = a from rfl] at hkey
          rw [hkey]
          rfl
        · rw [if_neg he]


end

/-! ### §85.3 標準性も逆向きに運ばれる

`stdB` の三つ — `nfB`・`nonIncr`・`stdIn` — をそれぞれ Buchholz 側の条項から取り戻す。
`nfB` は先頭の段の条件から、`nonIncr` は成分が降べきであることから、`stdIn` は `GB` の
条項から §85.2 を通して。**仮説は無い。** -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

/-- 先頭の節の段は 0 — `nfB` の最上位の条件を成分列で。 -/
def Hd085 (b : BT) : Prop := ∀ x ∈ b.toL, ∃ c, x = BT.D 0 c

theorem nfLe_bInvA85 : ∀ (b : BT) (acc : B), btLe72 1 b = true → Hd085 b →
    nfLe 0 acc = true → nfLe 0 (bInvA85 acc b) = true
  | .zero, acc, _, _, ha => ha
  | .D u a, acc, hb, hd, ha => by
      obtain ⟨_, hba⟩ := btLe72_D 1 u a hb
      obtain ⟨c, hc⟩ := hd (BT.D u a) (List.mem_cons.mpr (Or.inl rfl))
      injection hc with hu _
      subst hu
      exact (nfLe_nd_iff 0 0 acc (bInvA85 .nil a)).mpr
        ⟨Nat.le_refl 0, ha, nfLe_of_lvlLe72 _ 1 (Nat.le_refl 1) (lvlLe_bInv85 a hba)⟩
  | .sum x y, acc, hb, hd, ha => by
      obtain ⟨h1, h2⟩ := btLe72_sum 1 x y hb
      have hdx : Hd085 x := fun z hz => hd z (List.mem_append.mpr (Or.inl hz))
      have hdy : Hd085 y := fun z hz => hd z (List.mem_append.mpr (Or.inr hz))
      exact nfLe_bInvA85 y _ h2 hdy (nfLe_bInvA85 x acc h1 hdx ha)

theorem nfB_bInv85 (b : BT) (hb : btLe72 1 b = true) (hd : Hd085 b) :
    nfB (bInv85 b) = true := nfLe_bInvA85 b .nil hb hd rfl

/-- `stdIn` は節ごとの条件に分かれる。`stdIn_mem72` の逆向き。 -/
theorem stdIn_of_toL85 : ∀ (t : B),
    (∀ q ∈ toL t, nonIncr q.2 = true ∧ visOK q.1 q.2 q.2 = true ∧ stdIn q.2 = true) →
    stdIn t = true
  | .nil, _ => rfl
  | .nd v r c, h => by
      have he : toL (B.nd v r c) = toL r ++ [(v, c)] := toL_nd v r c
      have hr : ∀ q ∈ toL r, nonIncr q.2 = true ∧ visOK q.1 q.2 q.2 = true ∧
          stdIn q.2 = true := by
        intro q hq
        refine h q ?_
        rw [he]
        exact List.mem_append.mpr (Or.inl hq)
      have hcm : (v, c) ∈ toL (B.nd v r c) := by
        rw [he]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      have hc := h (v, c) hcm
      show (stdIn r && nonIncr c && visOK v c c && stdIn c) = true
      rw [stdIn_of_toL85 r hr, hc.1, hc.2.1, hc.2.2]
      rfl

/-- 降べきは節の広義単調減少に戻る。`descOK_map72` の逆向き。 -/
theorem nonIncrL_map85 : ∀ (l : List BT), Atoms l → (∀ x ∈ l, btLe72 1 x = true) →
    (∀ x ∈ l, fB72 (g85 x) = x) → descOK72 l = true → nonIncrL (l.map g85) = true
  | [], _, _, _, _ => rfl
  | [x], _, _, _, _ => by
      show (hdOK (g85 x) [] && nonIncrL []) = true
      rfl
  | x :: y :: r, hat, hbt, hpt, hd => by
      obtain ⟨hle, hd2⟩ := (Bool.and_eq_true _ _).mp hd
      have hmx : x ∈ x :: y :: r := List.mem_cons.mpr (Or.inl rfl)
      have hmy : y ∈ x :: y :: r := List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      obtain ⟨ux, ax, hxe⟩ := hat x hmx
      obtain ⟨uy, ay, hye⟩ := hat y hmy
      have hlx : (g85 x).1 ≤ 1 ∧ lvlLe 1 (g85 x).2 = true := by
        subst hxe
        obtain ⟨h1, h2⟩ := btLe72_D 1 ux ax (hbt _ hmx)
        exact ⟨h1, lvlLe_bInv85 ax h2⟩
      have hly : (g85 y).1 ≤ 1 ∧ lvlLe 1 (g85 y).2 = true := by
        subst hye
        obtain ⟨h1, h2⟩ := btLe72_D 1 uy ay (hbt _ hmy)
        exact ⟨h1, lvlLe_bInv85 ay h2⟩
      have hne : cmpS [g85 x] [g85 y] ≠ Ordering.lt := by
        intro hc
        have hlt := lt_fB72 (g85 x) (g85 y) hlx.1 hlx.2 hly.1 hly.2 hc
        rw [hpt x hmx, hpt y hmy] at hlt
        have hle' : ((y == x) || BT.lt y x) = true := hle
        rcases (Bool.or_eq_true _ _).mp hle' with he | hlt2
        · rw [eq_of_beq72 _ _ he, lt_irrefl74] at hlt
          exact Bool.noConfusion hlt
        · rw [lt_asymm74 hlt2] at hlt
          exact Bool.noConfusion hlt
      have hrest : nonIncrL (g85 y :: r.map g85) = true :=
        nonIncrL_map85 (y :: r)
          (fun z hz => hat z (List.mem_cons.mpr (Or.inr hz)))
          (fun z hz => hbt z (List.mem_cons.mpr (Or.inr hz)))
          (fun z hz => hpt z (List.mem_cons.mpr (Or.inr hz))) hd2
      show (hdOK (g85 x) (g85 y :: r.map g85) && nonIncrL (g85 y :: r.map g85)) = true
      rw [hdOK_cons72, hrest]
      cases hcc : cmpS [g85 x] [g85 y] with
      | lt => exact absurd hcc hne
      | eq => rfl
      | gt => rfl

/-! 主定理。 -/

/-- 成分ひとつぶんの往復。 -/
theorem fB72_g85_85 (u : Nat) (a : BT) (hb : btLe72 1 a = true) (hs : BT.isStd a = true) :
    fB72 (g85 (BT.D u a)) = BT.D u a := by
  show BT.D u (bArg u (bInv85 a)) = BT.D u a
  rw [bArg_eq_bValA71_71 (bInv85 a) u (lvlLe_bInv85 a hb),
    bVal_bInv85 (a.size + 1) a (Nat.lt_succ_self _) hb hs]

/-- **`visOK` は `GB` の条項そのもの。** `argStd72` の逆向き。 -/
theorem visOK_bInv85 (u : Nat) (a : BT) (hb : btLe72 1 (BT.D u a) = true)
    (hs : BT.isStd (BT.D u a) = true) : visOK u (bInv85 a) (bInv85 a) = true := by
  obtain ⟨_, hba⟩ := btLe72_D 1 u a hb
  have hlc : lvlLe 1 (bInv85 a) = true := lvlLe_bInv85 a hba
  have hva : bArg u (bInv85 a) = a := by
    rw [bArg_eq_bValA71_71 (bInv85 a) u hlc,
      bVal_bInv85 (a.size + 1) a (Nat.lt_succ_self _) hba (isStd_of_D hs)]
  have hgb : ((BT.GB u a).all (fun e => BT.lt e a)) = true :=
    ((Bool.and_eq_true _ _).mp hs).2
  refine visOK_of_gb85 u (bInv85 a) (bInv85 a) ?_
  intro q hq
  obtain ⟨x, hxm, hex⟩ := gb_bArg85 u (bInv85 a) hlc q hq
  have hmem : bArg q.1 q.2 ∈ BT.GB u (bArg u (bInv85 a)) := by
    rw [ofL_bArg72 u (bInv85 a) hlc]
    exact GB_ofL_mem85 u _ x hxm _ hex
  rw [hva] at hmem
  have hlt : BT.lt (bArg q.1 q.2) a = true := (List.all_eq_true.mp hgb) _ hmem
  rw [← hva] at hlt
  exact argTransfer85 q.1 u q.2 (bInv85 a) (gbL72_lvl72 u (bInv85 a) hlc q hq).2 hlc hlt

/-- **標準性は往復する。** 段 1 以下の標準な Buchholz 項の逆像は BMS 標準。 -/
theorem std_bInv85 : ∀ (n : Nat) (b : BT), b.size < n → btLe72 1 b = true →
    BT.isStd b = true → nonIncr (bInv85 b) = true ∧ stdIn (bInv85 b) = true
  | 0, _, hsz, _, _ => absurd hsz (Nat.not_lt_zero _)
  | n + 1, b, hsz, hb, hstd => by
      obtain ⟨hat, hcs, hcb, hdesc⟩ := good_toL77 b hstd hb
      have hpt : ∀ x ∈ b.toL, fB72 (g85 x) = x := by
        intro x hx
        obtain ⟨u, a, rfl⟩ := hat x hx
        obtain ⟨_, hba⟩ := btLe72_D 1 u a (hcb _ hx)
        exact fB72_g85_85 u a hba (isStd_of_D (hcs _ hx))
      constructor
      · show nonIncrL (toL (bInv85 b)) = true
        rw [toL_bInv85 b]
        exact nonIncrL_map85 b.toL hat hcb hpt hdesc
      · refine stdIn_of_toL85 (bInv85 b) ?_
        intro q hq
        rw [toL_bInv85 b] at hq
        obtain ⟨x, hxm, hxq⟩ := List.mem_map.mp hq
        obtain ⟨u, a, rfl⟩ := hat x hxm
        obtain ⟨_, hba⟩ := btLe72_D 1 u a (hcb _ hxm)
        have hsa : BT.isStd a = true := isStd_of_D (hcs _ hxm)
        have hszx : (BT.D u a).size ≤ b.size := size_mem_toL85 b _ hxm
        have hsza : a.size < n := by
          have e : (BT.D u a).size = 1 + a.size := rfl
          omega
        obtain ⟨h1, h2⟩ := std_bInv85 n a hsza hba hsa
        rw [← hxq]
        exact ⟨h1, visOK_bInv85 u a (hcb _ hxm) (hcs _ hxm), h2⟩

/-- **§85.2 の主定理。** 段 1 以下・先頭の段 0 の標準な Buchholz 項は、
    部分領域の添字の値としてちょうど現れる。 -/
theorem bOnto85 (b : BT) (hb : btLe72 1 b = true) (hd : Hd085 b) (hs : BT.isStd b = true) :
    ∃ u : B, stdB1 u = true ∧ bValA71 u = b := by
  obtain ⟨h1, h2⟩ := std_bInv85 (b.size + 1) b (Nat.lt_succ_self _) hb hs
  refine ⟨bInv85 b, ?_, bVal_bInv85 (b.size + 1) b (Nat.lt_succ_self _) hb hs⟩
  show ((nfB (bInv85 b) && nonIncr (bInv85 b) && stdIn (bInv85 b)) && lvlLe 1 (bInv85 b)) = true
  rw [nfB_bInv85 b hb hd, h1, h2, lvlLe_bInv85 b hb]
  rfl

end

/-! ### §85.4 先頭の段は仮定ではない

`Hd085` — 成分がどれも `D 0` — は挑戦者に余計に課す条件ではない。領域の値はそれを持ち
(`nfB` そのもの)、その下にある標準な項もそれを持つ。`D 0` が最小の頭で、成分は降べきだから
である。 -/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term

theorem lt_D_lvl85 {u v : Nat} {a c : BT} (h : BT.lt (BT.D u a) (BT.D v c) = true) :
    ¬ (v < u) := by
  intro hvu
  rw [lt_eq_ltS] at h
  rw [show (BT.D u a).toL = [BT.D u a] from rfl, show (BT.D v c).toL = [BT.D v c] from rfl,
    ltS_cons u a [] v c [], if_neg (by omega), if_pos hvu] at h
  exact Bool.noConfusion h

theorem nfLe_mem85 : ∀ (t : B) (m : Nat), nfLe m t = true → ∀ q ∈ toL t, q.1 ≤ m
  | .nil, _, _ => by intro q hq; cases hq
  | .nd v r c, m, h => by
      obtain ⟨h1, h2, _⟩ := (nfLe_nd_iff m v r c).mp h
      intro q hq
      rw [toL_nd] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact nfLe_mem85 r m h2 q hq
      · rw [List.mem_singleton.mp hq]; exact h1

/-- 領域の値の成分はどれも `D 0`。`nfB` そのもの。 -/
theorem hd085_bValA71_85 (t : B) (h : nfB t = true) : Hd085 (bValA71 t) := by
  intro x hx
  rw [toL_bValA71_map83] at hx
  obtain ⟨q, hqm, hq⟩ := List.mem_map.mp hx
  have hq0 : q.1 = 0 := Nat.le_zero.mp (nfLe_mem85 t 0 h q hqm)
  refine ⟨bArg q.1 q.2, ?_⟩
  rw [← hq, show fB72 q = BT.D q.1 (bArg q.1 q.2) from rfl, hq0]

/-- 頭が `D 0` の項より下なら、頭は `D 0`。 -/
theorem head_hd085 : ∀ (x : BT) (xs : List BT) (c : BT), Atoms (x :: xs) → Hd085 c →
    ltS (x :: xs) c.toL = true → ∃ e, x = BT.D 0 e := by
  intro x xs c hat hd h
  obtain ⟨u, a, rfl⟩ := hat x (List.mem_cons.mpr (Or.inl rfl))
  cases hc : c.toL with
  | nil => rw [hc, ltS_cons_nil] at h; exact Bool.noConfusion h
  | cons y ys =>
      obtain ⟨e, rfl⟩ := hd y (by rw [hc]; exact List.mem_cons.mpr (Or.inl rfl))
      rw [hc, ltS_cons u a xs 0 e ys, if_neg (by omega)] at h
      by_cases hu : 0 < u
      · rw [if_pos hu] at h; exact Bool.noConfusion h
      · exact ⟨a, by rw [Nat.eq_zero_of_not_pos hu]⟩

/-- 降べきなら先頭の段が全体を決める。 -/
theorem descOK_hd085 : ∀ (l : List BT) (e : BT), Atoms (BT.D 0 e :: l) →
    descOK72 (BT.D 0 e :: l) = true → ∀ x ∈ (BT.D 0 e :: l), ∃ c, x = BT.D 0 c := by
  intro l
  induction l with
  | nil =>
      intro e _ _ x hx
      rcases List.mem_cons.mp hx with h | h
      · exact ⟨e, h⟩
      · cases h
  | cons y r ih =>
      intro e hat hd x hx
      obtain ⟨hle, hd2⟩ := (Bool.and_eq_true _ _).mp hd
      obtain ⟨uy, ay, hye⟩ := hat y (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
      have hy0 : y = BT.D 0 ay := by
        rw [hye]
        have hle' : ((y == BT.D 0 e) || BT.lt y (BT.D 0 e)) = true := hle
        rcases (Bool.or_eq_true _ _).mp hle' with hb | hb
        · have := eq_of_beq72 _ _ hb
          rw [hye] at this
          injection this with h1 _
          rw [h1]
        · rw [hye] at hb
          have := lt_D_lvl85 hb
          rw [Nat.eq_zero_of_not_pos this]
      have hat2 : Atoms (BT.D 0 ay :: r) := by
        intro z hz
        rcases List.mem_cons.mp hz with h | h
        · exact ⟨0, ay, h⟩
        · exact hat z (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h))))
      have hd3 : descOK72 (BT.D 0 ay :: r) = true := by rw [← hy0]; exact hd2
      rcases List.mem_cons.mp hx with h | h
      · exact ⟨e, h⟩
      · rw [hy0] at h
        exact ih ay hat2 hd3 x h

/-- **下にある標準な項の成分はどれも `D 0`。** -/
theorem hd085_of_lt85 (b c : BT) (hbt : btLe72 1 b = true) (hs : BT.isStd b = true)
    (hd : Hd085 c) (h : BT.lt b c = true) : Hd085 b := by
  intro x hx
  cases hb : b.toL with
  | nil => rw [hb] at hx; cases hx
  | cons y ys =>
      have hat : Atoms (y :: ys) := by rw [← hb]; exact atoms_toL74 b
      have hlt : ltS (y :: ys) c.toL = true := by rw [← hb, ← lt_eq_ltS]; exact h
      obtain ⟨e, hye⟩ := head_hd085 y ys c hat hd hlt
      have hdesc : descOK72 (BT.D 0 e :: ys) = true := by
        rw [← hye, ← hb]
        exact (good_toL77 b hs hbt).2.2.2
      exact descOK_hd085 ys e (by rw [← hye]; exact hat) hdesc x (by rw [← hye, ← hb]; exact hx)

end

/-! ### §85.5 分割 — 密度は `dict` の像の稠密性と同値

`bOnto85` が「添字を作る」側を閉じたので、残るのは「Buchholz 項を作る」側だけになる。
橋 (`VOfLtA71`) は要らない: `PsiIdxOKStd172` は §76 の `vOfIsDict76`
(`vOf = dict ∘ bValA71`) を通してしか使わない。 -/

section
open Trans.Recal
open Trans.Dict (BT dict)
open TM TM.Term

/-- **密度の Buchholz 側。** -/
def DictOnto85 : Prop := ∀ (t : B), stdB1 t = true → kindB t = BMS.Kind.lim →
    ∀ s, inT s = true → lt s (vOf t) = true →
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧
      le s (dict b) = true ∧ BT.lt b (bValA71 t) = true

/-- **密度の 𝔗(M) 側。** -/
def DictDense85 : Prop := ∀ (t : B), stdB1 t = true → kindB t = BMS.Kind.lim →
    ∀ s, inT s = true → lt s (vOf t) = true →
    ∃ b : BT, btLe72 1 b = true ∧ BT.isStd b = true ∧ Hd085 b ∧
      le s (dict b) = true ∧ lt (dict b) (vOf t) = true

theorem cofDenseS1_of_dictDense85 (Hp : PsiIdxOKStd172) (H : DictDense85) : CofDenseS1 := by
  intro t ht hk s hs hlt
  obtain ⟨b, hb, hbs, hbd, hle, hblt⟩ := H t ht hk s hs hlt
  obtain ⟨u, hu, hvu⟩ := bOnto85 b hb hbd hbs
  have hv : vOf u = dict b := by rw [vOfIsDict76 Hp u hu, hvu]
  exact ⟨u, hu, by rw [hv]; exact hle, by rw [hv]; exact hblt⟩

theorem dictDense85_of_cofDenseS1 (Hp : PsiIdxOKStd172) (H : CofDenseS1) : DictDense85 := by
  intro t ht hk s hs hlt
  obtain ⟨u, hu, hle, hult⟩ := H t ht hk s hs hlt
  have hv : vOf u = dict (bValA71 u) := vOfIsDict76 Hp u hu
  refine ⟨bValA71 u, btLeA77 u hu, stdA77 u hu,
    hd085_bValA71_85 u (nfB_of_stdB u (stdB_of_stdB1 u hu)), ?_, ?_⟩
  · rw [← hv]; exact hle
  · rw [← hv]; exact hult

/-- **§85 の主定理。** 密度の条項は `dict` の像の稠密性と**同値**である。 -/
theorem cofDenseS1_iff_dictDense85 (Hp : PsiIdxOKStd172) : CofDenseS1 ↔ DictDense85 :=
  ⟨dictDense85_of_cofDenseS1 Hp, cofDenseS1_of_dictDense85 Hp⟩

theorem dictDense85_of_dictOnto85 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (H : DictOnto85) :
    DictDense85 := by
  intro t ht hk s hs hlt
  obtain ⟨b, hb, hbs, hle, hblt⟩ := H t ht hk s hs hlt
  have hdt : Hd085 (bValA71 t) := hd085_bValA71_85 t (nfB_of_stdB t (stdB_of_stdB1 t ht))
  have hdb : Hd085 b := hd085_of_lt85 b (bValA71 t) hb hbs hdt hblt
  obtain ⟨u, hu, hvu⟩ := bOnto85 b hb hdb hbs
  refine ⟨b, hb, hbs, hdb, hle, ?_⟩
  rw [vOfIsDict76 Hp t ht, ← hvu]
  exact H2 u t hu ht (by rw [hvu]; exact hblt)

theorem cofDenseS1_of_dictOnto85 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (H : DictOnto85) :
    CofDenseS1 := cofDenseS1_of_dictDense85 Hp (dictDense85_of_dictOnto85 Hp H2 H)

/-- 326 行目の証明書に残る仮説は 3 つ、そのうち共終性のぶんは `DictDense85` ただ 1 つ。 -/
theorem certIn_t326_85 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (HD : DictDense85)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_83 Hp H2 (cofDenseS1_of_dictDense85 Hp HD) hacc

end

/-! ### §85.6 外せないもの

`Ω = ψ₁(0)` は標準で段 1 以下だが、どの添字の値でもない — `Hd085` は `bOnto85` から
外せない。そして段 2 では条項そのものが偽である: §69 の `CofGap` から、絞らない密度と
絞らない内側の共終性は両立しない。破れる場所は一点で、§69 の逃げる項 `sbad` である。 -/

section
open Trans.Recal
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

/-- `Ω = ψ₁(0)` は標準だが、どの添字の値でもない。`Hd085` は `bOnto85` から外せない。 -/
theorem not_bValA71_om85 (u : B) (h : nfB u = true) : bValA71 u ≠ BT.Om 1 := by
  intro hc
  obtain ⟨c, hcc⟩ := hd085_bValA71_85 u h (BT.Om 1)
    (by rw [hc]; exact List.mem_cons.mpr (Or.inl rfl))
  injection hcc with h1 _
  exact Nat.noConfusion h1

theorem isStd_om85 : BT.isStd (BT.Om 1) = true := rfl
theorem btLe72_om85 : btLe72 1 (BT.Om 1) = true := rfl

/-- §69 の逃げる項 `sbad` の Buchholz 逆像 — `ψ₀(ψ₁(Ω₂))`。`dictInv` が返すもの
    (§85.7 で測る)。 -/
def sbadB85 : BT := BT.D 0 (BT.D 1 (BT.D 2 BT.zero))

/-- **その逆像は段 2 を持つ。** `bOnto85` の仮説を満たさない — 段の上限を落とすと
    §69 の反例がそのまま入り口に立つ。 -/
theorem not_btLe72_sbadB85 : btLe72 1 sbadB85 = false := rfl

theorem btLe72_two_sbadB85 : btLe72 2 sbadB85 = true := rfl

/-- しかも標準形ですらない。 -/
theorem not_isStd_sbadB85 : BT.isStd sbadB85 = false := rfl

/-! 段 2 — 条項そのものが偽になる側。 -/

def CofDenseS85 : Prop := ∀ (t : B), stdB t = true → kindB t = BMS.Kind.lim →
    ∀ s, inT s = true → lt s (vOf t) = true →
    ∃ u : B, stdB u = true ∧ le s (vOf u) = true ∧ lt (vOf u) (vOf t) = true

def CofInS85 : Prop := ∀ (t : B), stdB t = true → kindB t = BMS.Kind.lim →
    ∀ u : B, stdB u = true → lt (vOf u) (vOf t) = true →
    ∃ n, le (vOf u) (vOf (fsB t n)) = true

theorem limCofS_of85 (Hp : PsiIdxOKStd) (Hr : RegionStd) (HD : CofDenseS85) (HI : CofInS85) :
    LimCofS := by
  intro t ht hk s hs hlt
  obtain ⟨u, hu, hle, hult⟩ := HD t ht hk s hs hlt
  obtain ⟨n, hn⟩ := HI t ht hk u hu hult
  exact ⟨n, le_trans_inT hs (inT_vOf_std Hp Hr u hu)
    (inT_vOf_std Hp Hr _ (stdB_fsB t ht n)) hle hn⟩

theorem not_cofDense_and_cofIn85 (H : CofGap) (Hp : PsiIdxOKStd) (Hr : RegionStd) :
    ¬ (CofDenseS85 ∧ CofInS85) := fun h => not_limCofS H (limCofS_of85 Hp Hr h.1 h.2)

theorem not_cofDenseS85 (H : CofGap) (Hp : PsiIdxOKStd) (Hr : RegionStd) (HI : CofInS85) :
    ¬ CofDenseS85 := fun hd => not_cofDense_and_cofIn85 H Hp Hr ⟨hd, HI⟩

/-- **壊れる場所は一点。** §69 の逃げる項 `sbad` を上から押さえる標準な値は、
    対角の下には無い。 -/
theorem sbad_no_witness85 (H : CofGap) (Hp : PsiIdxOKStd) (Hr : RegionStd) (HI : CofInS85) :
    ¬ (∃ u : B, stdB u = true ∧ le sbad (vOf u) = true ∧ lt (vOf u) (vOf tdiag) = true) := by
  intro h
  obtain ⟨u, hu, hle, hult⟩ := h
  obtain ⟨n, hn⟩ := HI tdiag stdB_tdiag kindB_tdiag u hu hult
  have := le_trans_inT inT_sbad (inT_vOf_std Hp Hr u hu)
    (inT_vOf_std Hp Hr _ (stdB_fsB tdiag stdB_tdiag n)) hle hn
  rw [H n] at this
  exact Bool.noConfusion this

end

/-! ### §85.7 測定 (凍結)

母集団の作り方を先に書く。**§85.1〜§85.6 は定理なので、以下は根拠ではなく受領である。**
ただし最後の 3 行だけは違う — そこは開いている条項の形を測っている。

    subP n   = (popNFB 2 n).filter stdB1        節は 0 … n-1 個、段は 0 と 1 (§70.6)
    subLim n = (subP n).filter (kindB · = lim)
    pool85   = `seeds85 = [0, 1, Ω]` を `bgrow85` (`D 0 ·`・`D 1 ·`・`·+·`) で 2 回育て、
               `isStd` かつ `btLe72 1` かつ先頭の段 0 で絞ったもの。20 個。
    chal85   = §70.6 の `outP70 2 5` — **標準でない** 正規形の添字の値のうち `inT` のもの。

**`pool85` が要点である。** `subP` から取った項では値の集合がもともと領域の像なので、
`bOnto85` の中身が見えない。`pool85` は Buchholz 側で独立に育てた項で、BMS は育て方に
一切入っていない。そこから `bInv85` が添字を作れることを測る。

**負の結果 (3 個)。** `Ω = ψ₁(0)` は `isStd` と `btLe72 1` を満たすが先頭の段が 0 でなく、
その逆像は `nfB` を落とす。`bOnto85` から先頭の段の条件は外せない (§85.6 の定理の受領)。

**段 2 の破れ (§85.6 の定理の受領)。** `sbad` は `vOf tdiag` より下だが、部分領域の値は
どれもその下で止まり、`popS 3 5` の 55 個の標準な添字にも `[sbad, vOf tdiag)` に入る値は
無い。`tdiag` 自身は段 2 の節を持つので部分領域の外である。

**開いている側 (最後の 3 行)。** 挑戦者 `chal85` は 11 個、そのうち 10 個は部分領域の値
そのものなので、この掃きは `DictDense85` の**強い試験ではない** — 本当に難しい挑戦者は
どの添字の像でもない 𝔗(M) の項で、それを覆うのは §70 の 36 951 項の掃きの方である。
ここで測るのは**形**である: 証人は挑戦者とともに大きくなる。`t = ψ₀(Ω)` (値は ε₀) と
挑戦者 `vOf (tow83 k) = ω↑↑k` の族で、固定の 20 個の Buchholz 母集団は `k = 3` で尽き、
必要な添字の節の個数はちょうど `k` である。§83.9 が `iterD` の塔で見たのと同じ形で、
「定数個の証人で足りる」という読み方をここで潰しておく。

**最後の 2 組が §85 の足したものである。** `sPhi85 = φ̄(ψ_Ω(0),0)` は `inT` を満たし、
部分領域の極限値 `ψ_Ω(ω)` より下にあり、`dict` の像には**入っていない** (`dictInv` は
`none`)。609 個の列挙 `subP 7` にはこれを上から押さえる添字が無い。ところが Buchholz 側で
`ψ₀(Ω^Ω·2)` を書いて `bInv85` に通すと、7 列の標準な添字
`(0,0)(1,1)(2,1)(3,1)(1,1)(2,1)(3,1)` — 値は `Γ₁ = ψ_Ω(1)` — がそのまま出てくる。
「添字を直接作る」とはこのことで、列挙では届かない証人が一行で出る。 -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv)
open TM TM.Term

def seeds85 : List BT := [BT.zero, BT.one, BT.Om 1]

def bgrow85 (p : List BT) : List BT :=
  (p ++ (p.flatMap fun x => [BT.D 0 x, BT.D 1 x])
     ++ (p.flatMap fun x => p.map fun y => BT.add x y)).eraseDups

def hd085B (b : BT) : Bool := b.toL.all fun x => match x with | .D 0 _ => true | _ => false

def pool85 : List BT :=
  (bgrow85 (bgrow85 seeds85)).filter fun b => BT.isStd b && btLe72 1 b && hd085B b

def vals85 : List Term := pool85.map dict

def chal85 : List Term := outP70 2 5

/-- `dict` の像に入らない挑戦者 — `φ̄(Γ₀,0)`。 -/
def sPhi85 : Term := phi (psi (Z zero) zero) zero

/-- その挑戦者の上に立つ部分領域の極限、`ψ_Ω(ω)` の添字。 -/
def tGw85 : B := .nd 0 .nil (.nd 1 .nil (.nd 0 (.nd 1 .nil (.nd 1 .nil .nil)) .nil))

/-- 証人の Buchholz 側 — `ψ₀(Ω^Ω·2)`、その値は `Γ₁ = ψ_Ω(1)`。 -/
def bGam85 : BT :=
  BT.D 0 (BT.sum (BT.D 1 (BT.D 1 (BT.Om 1))) (BT.D 1 (BT.D 1 (BT.Om 1))))

-- 逆写像は部分領域の上で両側の逆。右側は §85.1 の定理、左側はここで測る。
#guard (subP 4).length == 13
#guard (subP 4).all fun u => bInv85 (bValA71 u) == u

-- `bOnto85` の受領。母集団は Buchholz 側で独立に育てたもの。
#guard pool85.length == 20
#guard pool85.all fun b => bValA71 (bInv85 b) == b
#guard pool85.all fun b => stdB1 (bInv85 b)

-- 先頭の段の条件は外せない。
#guard BT.isStd (BT.Om 1) && btLe72 1 (BT.Om 1)
#guard hd085B (BT.Om 1) == false
#guard nfB (bInv85 (BT.Om 1)) == false

-- 段 2 の破れ。部分領域の値は `sbad` の下で止まる (§70.3 の `BelowGap` の受領)。
#guard lt sbad (vOf tdiag)
#guard (subP 4).all fun u => lt (vOf u) sbad
-- 標準な添字にも `[sbad, vOf tdiag)` の値は無い。
#guard (popS 3 5).length == 55
#guard (popS 3 5).all fun u => !(le sbad (vOf u) && lt (vOf u) (vOf tdiag))
-- §69 の反例は部分領域の外。
#guard stdB1 tdiag == false

/-! **開いている側。** 挑戦者は 11 個、非空な対は 42 個。10 個は領域の値そのもので、
    この母集団は難しい挑戦者に届いていない。 -/
#guard chal85.length == 11
#guard (chal85.countP fun s => (subP 5).any fun u => vOf u == s) == 10
#guard ((subLim 4).flatMap fun t => chal85.filter fun s => lt s (vOf t)).length == 42
#guard (subLim 4).all fun t => chal85.all fun s =>
  !(lt s (vOf t)) || ((subP 6).any fun u => le s (vOf u) && lt (vOf u) (vOf t))

/-! **証人は挑戦者とともに大きくなる。** 固定の母集団は `k = 3` で尽きる。 -/
#guard (List.range 8).all fun k => sizeB (tow83 k) == k
#guard (List.range 8).all fun k => lt (vOf (tow83 k)) (vOf sbad83)
#guard (List.range 8).all fun k =>
  (vals85.any fun d => le (vOf (tow83 k)) d && lt d (vOf sbad83)) == decide (k ≤ 3)

/-! **§69 の逃げる項の逆像は段 2 を持つ。** `bOnto85` が届かない理由はこれで、
    §85.6 の 3 つの `rfl` はこの `dictInv` の答えについてのものである。 -/
#guard dictInv sbad == some sbadB85
#guard dict sbadB85 == sbad

/-! **`dict` は 𝔗(M) の上へではない。** `sPhi85 = φ̄(ψ_Ω(0),0)` は `inT` を満たし、
    部分領域の極限値 `ψ_Ω(ω)` (`tGw85`) より下にあるが、Buchholz の逆像を持たない
    (`dictInv` は `none`)。`DictDense85` が `s = dict b` ではなく `s ≤ dict b` と
    言うのはこのためである。 -/
#guard inT sPhi85 && (dictInv sPhi85).isNone
#guard matB tGw85 0 == [[0,0],[1,1],[2,1],[3,1],[2,0]]
#guard stdB1 tGw85 && (kindB tGw85 == BMS.Kind.lim)
#guard lt sPhi85 (vOf tGw85)

/-! **そして証人は `bInv85` が作る。** 609 個の列挙 `subP 7` には無い添字である。
    これが「添字を直接作る」ということで、§85 が足したのはこの一行である。 -/
#guard BT.isStd bGam85 && btLe72 1 bGam85 && hd085B bGam85
#guard stdB1 (bInv85 bGam85)
#guard matB (bInv85 bGam85) 0 == [[0,0],[1,1],[2,1],[3,1],[1,1],[2,1],[3,1]]
#guard vOf (bInv85 bGam85) == dict bGam85
#guard le sPhi85 (vOf (bInv85 bGam85)) && lt (vOf (bInv85 bGam85)) (vOf tGw85)
#guard (subP 7).all fun u => !(vOf u == dict bGam85)
#guard (subP 7).all fun u => !(le sPhi85 (vOf u) && lt (vOf u) (vOf tGw85))

end

/-! ### §85.8 公理 -/


/-! ## §87 THE GATE ITSELF — THE SCAN SEES ONLY THE `ψ₁` COMPONENTS, AND `G(a,0) < a` IS IN HAND

Four sections in a row have died the same death.  §75's `LocalStd75` was refuted by §84,
§78/§80's `LocalK2_78` by §82, §84's `SplitStd84` by §86 — and §86 proved WHY: at the failing
step **both** summands of `i₀ ⊕ Δ` are needed at one and the same element, so no clause
comparing a `K`-element against `Δ` alone or against `i₀` alone can close the gate.  §86's
replacement `SplitK86` splits the ELEMENT instead and measures clean, but its right disjunct
`y ≤ i₀ ⊕ (y ⊖ i₀)` is exactly the arithmetic §82 diagnosed, written out; §86 says so itself.

**§87 stops proposing sufficient conditions.**  §84 proved `IdxStd84` IS `PsiIdxStep073`
(`idxStd84_of_step073`), so there is nothing to lose by working with the gate itself, and
four attempts at localisation have now cost four sections.  What has never been spent is
Buchholz's `G(a,0) < a` — §82.3 packaged it as `comp_facts82` and no section since has used
it.  §87 spends it as far as it goes: it puts `BT.lt c a` in hand AT the `K`-element, it
removes the `ψ₀` components and the elements below `Ω₁` from the gate's reach, and it proves
the gate outright on the layer where what is left is empty.

WHAT IS PROVED, UNCONDITIONALLY.

  §87.1  **THE GATE MAY BE PROVED BY INDUCTION, AND THE INDUCTION IS FREE.**  `GateStd87 a`
         is `PsiIdxStep073` at one term and `step073_of_gate87` reduces the gate to
         "`GateStd87 a` from `GateStd87 b` for every `b` with `BT.size b < BT.size a`".
         `inT_dict_ih87` re-proves §84.6's `inT_dict_of_idx84` from that induction hypothesis
         ALONE — so `inT (dict a)` and `lt (dict a) < M`, which every clause from §75 to §86
         carried as hypotheses of its residue, are now theorems and disappear from the
         statement.

  §87.2  **THE SCAN SEES ONLY THE SUBSCRIPT-`1` COMPONENTS.**  `lt_reg1_dict_D0_87` puts every
         subscript-`0` component of `a` below `Ω₁`: §82.3 hands the component's own Buchholz
         standardness, §87.1's induction hypothesis hands its gate, §79.6's
         `lt_collapse0_W79` turns that into `ψ₀(·) < Ω₁`.  Hence `big_D1_87` — **every element
         of `bigPart Ω₁ (toList (dict a))`, i.e. everything `wcnf` ever splits into a pair, is
         `dict (ψ₁ c)` for a component `ψ₁ c` of `a`.**  The `ψ₀` components are invisible to
         the gate, and the `ψ₀` that matters is the one at the TOP of `dict a`, not the ones
         inside it.

  §87.3  **EVERY `K`-ELEMENT IS A `K`-ELEMENT OF A BUCHHOLZ ARGUMENT, WITH `c < a` ATTACHED.**
         `kset_arg87` : for every `y ∈ K_{Ω₁} aV ∪ K_{Ω₁} cV` at every step there is a
         component `ψ₁ c` of `a` with

             y ∈ K_{Ω₁}(dict c),    BT.isStd (ψ₁ c),    **BT.lt c a**.

         §66's `mem_Kset_wcnf` carries the element back to `bigPart`, §87.2 names the
         component, §77.7's `ψ₁(α) = ω^(Ω₁ ⊕ α)` strips the `ω^(Ω₁ ⊕ ·)` outright
         (`kset_strip_D1_87`; `K_{Ω₁} Ω₁ = ∅`), and §82.3's `comp_facts82` attaches Buchholz's
         two facts.  **`wA`, `wC`, `divAP`, `mulL`, `subAP` are gone from the statement.**
         And on the `aV` side — the side §86's counterexample lives on — the component is not
         merely SOME component: `kset_fst_arg87` adds

             aV = wA Ω₁ (dict (ψ₁ c)),

         by §82.1, so the element is tied to the very component that built this step's
         exponent.  §82.1 was proved for exactly this and never used again.

  §87.4  **THE RESIDUE, IN TWO CLAUSES.**  `ArgK87` splits §84's `IdxK84` at the side the
         element comes from.  The `aV` clause is handed the four Buchholz facts, the exponent
         identity `aV = wA Ω₁ (dict (ψ₁ c))`, and only the elements NOT below `Ω₁` — the ones
         below are closed outright by §86.3's `lt_sub1dd_of_lt_reg86` with §75.2's
         `le_sub1dd_idxOf75`.  The `cV` clause is handed the four facts.
         `psiIdxStep073_of_arg87` and `certIn_t326_arg87` re-hang row 326 on it;
         `arg87_of_step073` is the converse, so the reduction is exact and a refutation of
         `ArgStd87` would be a refutation of the gate.

  §87.5  **A FRAGMENT OF THE LEVEL-ZERO GATE, PROVED OUTRIGHT.**  `noD0_87 c` says `c`
         mentions no `ψ₀`; `flat87 a` says no ARGUMENT of a component of `a` mentions one.
         Then `inT_dict_noD0_87` (no gate, no standardness — at level one the strongly
         critical branch never fires, §73.4), `kset_nil_noD0_87` (`K_{Ω₁}(dict c) = ∅`, by
         §77.7 again) and `ksetStepOK_noD0_87` give

             ksetStepOK_flat87 : flat87 a → btLe72 1 a → KsetStepOK 0 (dict a)

         — the gate, as a theorem, with no hypothesis beyond the shape and no standardness at
         all.  §73.4's `ksetStepOK_one73` had the LEVEL-ONE gate for free; this is the first
         piece of the LEVEL-ZERO gate `PsiIdxStep073` that is proved and not assumed.
         §87.6 measures how thin it is: 10 of row 326's own 41 indices, and 0 of the 131
         terms of the three adversarial populations.

WHAT IS **NOT** CLAIMED.  `ArgStd87` is NOT proved, and it is EQUIVALENT to `PsiIdxStep073`,
not weaker: `arg87_of_step073` goes back.  So §87 is, like §84's `IdxStd84`, a repackaging;
what it repackages is different.  It discharges the ambient `inT` hypotheses (§87.1), the
`ψ₀` components (§87.2) and the `K`-elements below `Ω₁` (§87.4), and it delivers `BT.lt c a`
and `BT.isStd (ψ₁ c)` at the element (§87.3).  **What remains open is one step and it is
named: from `c < a` in Buchholz's order to `y < i₀ ⊕ Δ` in `𝔗(M)` — a monotonicity of the
collapse index — and §87 does not take it.**  `SplitK86` is NOT refuted here: §87.6 measures
it clean on a population opened one level past §86's.  `LocalK2Snd_78`, `DictHeadLt77`,
`CofDenseS1`, `BCofIn71` are untouched.

WHAT THE MEASUREMENT SAYS (§87.6 gives the construction: §86's `pop86`/`qual86` reused
verbatim, plus 72 terms opened one level further and widened in three directions — a
three-summand `ψ₀`-argument, a doubly nested `ψ₀` whose inner copy also fires, and two firing
`ψ₀` summands side by side).  172 terms in all.

  * **§84's clause does not merely fail somewhere — at four levels it fails EVERYWHERE.**
    `splitb84` is false on all 25 qualifying terms of `pop87` (§75's per-pair clause likewise).
    §86 found 10 of 53 at three levels; the exceptions vanish at four.
  * **`splitb86`, `idxb84` and `stepOKb` fail 0 times on the same 25.**  §87 is not a fourth
    refutation.
  * **§87.2 and §87.3 hold on all 172.**  `d0Below87` (the `ψ₀` components sit below `Ω₁`),
    `kInArg87` (every `K`-element of a firing step lies in `K_{Ω₁}(dict c)` for a
    subscript-`1` component `ψ₁ c`) and `fstArg87` (on the `aV` side that component is the one
    whose `wA` IS this step's `aV`) are true everywhere, `bad86` and `aBad82` included.
  * **The step-blind form is FALSE.**  Cut the correspondence between the `K`-element and the
    step it is asked at, and the clause fails 25 times on `pop87`, 31 on `qual86`, 3 on
    `qual84`.  `ArgK87`'s per-step shape is not decoration.
  * **§86.3's free branch is vacuous on all of this.**  All 31 escapes on `pop87` and all 31
    on `qual86` are at or above `Ω₁`, and all are on the `K_{Ω₁} aV` side; over `r326_84` the
    firing steps have an EMPTY `K_{Ω₁} aV`.  §80.7's 458 of 635 live in a different corpus.
-/

/-! ### §87.1 門は帰納法で証明してよい -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **一項ぶんの門。** `PsiIdxStep073` は「すべての `a` について `GateStd87 a`」。 -/
def GateStd87 (a : BT) : Prop :=
  btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → KsetStepOK 0 (dict a)

theorem step073_iff_gate87 : PsiIdxStep073 ↔ ∀ a : BT, GateStd87 a :=
  ⟨fun H a hb hs => H a hb hs, fun H a hb hs => H a hb hs⟩

theorem size_D87 (u : Nat) (c : BT) : BT.size (BT.D u c) = 1 + BT.size c := rfl
theorem size_sum87 (x y : BT) : BT.size (BT.sum x y) = 1 + BT.size x + BT.size y := rfl
theorem size_pos87 : ∀ c : BT, 0 < BT.size c
  | .zero => by rw [show BT.size BT.zero = 1 from rfl]; omega
  | .D u c => by rw [size_D87]; have := size_pos87 c; omega
  | .sum x y => by rw [size_sum87]; have := size_pos87 x; omega

/-- 成分は自分より大きくない。 -/
theorem size_mem_toL87 : ∀ (a t : BT), t ∈ BT.toL a → BT.size t ≤ BT.size a := by
  intro a
  induction a with
  | zero => intro t h; cases h
  | D u c _ =>
    intro t h
    rw [List.mem_singleton.mp (show t ∈ [BT.D u c] from h)]
    exact Nat.le_refl _
  | sum x y ihx ihy =>
    intro t h
    rw [size_sum87]
    rcases List.mem_append.mp (show t ∈ BT.toL x ++ BT.toL y from h) with h1 | h1
    · have := ihx t h1; have := size_pos87 y; omega
    · have := ihy t h1; have := size_pos87 x; omega

/-- 成分はどれも `ψ_u c` の形。 -/
theorem mem_toL_D87 : ∀ (a t : BT), t ∈ BT.toL a → ∃ u c, t = BT.D u c := by
  intro a
  induction a with
  | zero => intro t h; cases h
  | D u c _ => intro t h; exact ⟨u, c, List.mem_singleton.mp (show t ∈ [BT.D u c] from h)⟩
  | sum x y ihx ihy =>
    intro t h
    rcases List.mem_append.mp (show t ∈ BT.toL x ++ BT.toL y from h) with h1 | h1
    · exact ihx t h1
    · exact ihy t h1

/-- 段の上限は成分に降りる。 -/
theorem btLe72_toL87 : ∀ (a t : BT), btLe72 1 a = true → t ∈ BT.toL a → btLe72 1 t = true := by
  intro a
  induction a with
  | zero => intro t _ h; cases h
  | D u c _ =>
    intro t hb h
    rw [List.mem_singleton.mp (show t ∈ [BT.D u c] from h)]
    exact hb
  | sum x y ihx ihy =>
    intro t hb h
    obtain ⟨hbx, hby⟩ := btLe72_sum 1 x y hb
    rcases List.mem_append.mp (show t ∈ BT.toL x ++ BT.toL y from h) with h1 | h1
    · exact ihx t hbx h1
    · exact ihy t hby h1

/-- **帰納法の仮説だけで `dict` の像は 𝔗(M) の中。** §84.6 の `inT_dict_of_idx84` の、
    大域の仮説を「自分より小さい項の門」に取り替えた形。 -/
theorem inT_dict_ih87 : ∀ (c : BT), (∀ b : BT, BT.size b < BT.size c → GateStd87 b) →
    btLe72 1 c = true → BT.isStd c = true → inT (dict c) = true ∧ lt (dict c) M = true
  | .zero, _, _, _ => ⟨inT_zero, lt_zero_M⟩
  | .D u x, ih, hb, h => by
      obtain ⟨hu, hbx⟩ := btLe72_D 1 u x hb
      have hsz : BT.size x < BT.size (BT.D u x) := by rw [size_D87]; omega
      have ihx : ∀ b : BT, BT.size b < BT.size x → GateStd87 b :=
        fun b hbz => ih b (by omega)
      have ihh := inT_dict_ih87 x ihx hbx (isStd_of_D h)
      refine inT_collapse_gap3 u (dict x) ihh.1 ihh.2 ?_
      cases u with
      | zero => exact psiIdxOK_of_stepOK 0 (dict x) ihh.1 ihh.2 (ih x hsz hbx h)
      | succ u' =>
        cases u' with
        | zero => exact psiIdxOK_of_stepOK 1 (dict x) ihh.1 ihh.2 (ksetStepOK_one73 x hbx)
        | succ u'' => exact absurd hu (by omega)
  | .sum x y, ih, hb, h => by
      obtain ⟨hbx, hby⟩ := btLe72_sum 1 x y hb
      have hsx : BT.size x < BT.size (BT.sum x y) := by
        rw [size_sum87]; have := size_pos87 y; omega
      have hsy : BT.size y < BT.size (BT.sum x y) := by
        rw [size_sum87]; have := size_pos87 x; omega
      have ihx := inT_dict_ih87 x (fun b hbz => ih b (by omega)) hbx (isStd_of_sum h).1
      have ihy := inT_dict_ih87 y (fun b hbz => ih b (by omega)) hby (isStd_of_sum h).2
      exact ⟨inT_plus ihx.1 ihy.1, lt_plus_M ihx.1 ihy.1 ihx.2 ihy.2⟩

/-- **§87.1 の主定理。** 門は「自分より小さい項の門」を仮定して一項ずつ示してよい。 -/
theorem step073_of_gate87
    (H : ∀ a : BT, (∀ b : BT, BT.size b < BT.size a → GateStd87 b) → GateStd87 a) :
    PsiIdxStep073 := by
  have key : ∀ n : Nat, ∀ a : BT, BT.size a ≤ n → GateStd87 a := by
    intro n
    induction n with
    | zero =>
      intro a ha
      exact H a (fun b hbz => absurd (Nat.lt_of_lt_of_le hbz ha) (Nat.not_lt_zero _))
    | succ n ih =>
      intro a ha
      exact H a (fun b hbz => ih b (by omega))
  intro a hb hs
  exact key (BT.size a) a (Nat.le_refl _) hb hs

end

/-! ### §87.2 走査が見る成分は添字 1 のものだけ -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- `bigPart` の元は `w` より下ではない。 -/
theorem bigPart_ge87 (w : Term) : ∀ (L : List Term) (q : Term),
    q ∈ bigPart w L → lt q w = false := by
  intro L
  induction L with
  | nil => intro q h; cases h
  | cons p rest ih =>
    intro q h
    by_cases hlp : lt p w = true
    · rw [show bigPart w (p :: rest) = [] from by
        show (if lt p w = true then [] else p :: bigPart w rest) = []
        rw [if_pos hlp]] at h
      cases h
    · rw [show bigPart w (p :: rest) = p :: bigPart w rest from by
        show (if lt p w = true then [] else p :: bigPart w rest) = _
        rw [if_neg hlp]] at h
      rcases List.mem_cons.mp h with h1 | h1
      · rw [h1]; exact bool_false hlp
      · exact ih q h1

/-- **添字 0 の成分は `Ω₁` の下。** 帰納法の仮説 (自分より小さい項の門) と §79.6。 -/
theorem lt_reg1_dict_D0_87 {a : BT} (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b)
    (hb : btLe72 1 a = true) (hs : BT.isStd (BT.D 0 a) = true)
    {c : BT} (ht : BT.D 0 c ∈ BT.toL a) : lt (dict (BT.D 0 c)) (reg 1) = true := by
  have hsz : BT.size (BT.D 0 c) ≤ BT.size a := size_mem_toL87 a _ ht
  have hszc : BT.size c < BT.size a := by rw [size_D87] at hsz; omega
  have hbc : btLe72 1 (BT.D 0 c) = true := btLe72_toL87 a _ hb ht
  have hbc2 : btLe72 1 c = true := (btLe72_D 1 0 c hbc).2
  have hsc : BT.isStd (BT.D 0 c) = true := (comp_facts82 hs ht).1
  have ihc : ∀ b : BT, BT.size b < BT.size c → GateStd87 b := fun b hz => ih b (by omega)
  have hin := inT_dict_ih87 c ihc hbc2 (isStd_of_D hsc)
  exact lt_collapse0_W79 (dict c) hin.1 hin.2
    (psiIdxOK_of_stepOK 0 (dict c) hin.1 hin.2 (ih c hszc hbc2 hsc))

/-- **§87.2 の主定理。** 走査が見る成分 (`bigPart` の元) はどれも添字 1 の成分の像。 -/
theorem big_D1_87 {a : BT} (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b)
    (hb : btLe72 1 a = true) (hs : BT.isStd (BT.D 0 a) = true) :
    ∀ q ∈ bigPart (reg 1) (toList (dict a)),
      ∃ c, BT.D 1 c ∈ BT.toL a ∧ q = dict (BT.D 1 c) := by
  intro q hq
  have hqne : lt q (reg 1) = false := bigPart_ge87 (reg 1) _ q hq
  obtain ⟨_, t, ht, hte⟩ := toList_dict82 a q (bigPart_sub _ _ q hq)
  obtain ⟨u, c, hue⟩ := mem_toL_D87 a t ht
  subst hue
  have hbt : btLe72 1 (BT.D u c) = true := btLe72_toL87 a _ hb ht
  have hu : u ≤ 1 := (btLe72_D 1 u c hbt).1
  cases u with
  | zero =>
    exfalso
    have h0 : lt q (reg 1) = true := by
      rw [hte]; exact lt_reg1_dict_D0_87 ih hb hs ht
    rw [h0] at hqne
    exact Bool.noConfusion hqne
  | succ u' =>
    cases u' with
    | zero => exact ⟨c, ht, hte⟩
    | succ u'' => exact absurd hu (by omega)

end

/-! ### §87.3 `K` の元は Buchholz の引数の `K` -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **`ω^(Ω₁ ⊕ ·)` をはがす。** `ψ₁(α) = ω^(Ω₁ ⊕ α)` (§77.7) と `K_{Ω₁} Ω₁ = ∅`。 -/
theorem kset_strip_D1_87 {a : BT} (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b)
    (hb : btLe72 1 a = true) (hs : BT.isStd (BT.D 0 a) = true)
    {c : BT} (hc : BT.D 1 c ∈ BT.toL a) {y : Term}
    (h : y ∈ Kset (reg 1) (dict (BT.D 1 c))) : y ∈ Kset (reg 1) (dict c) := by
  have hsz : BT.size (BT.D 1 c) ≤ BT.size a := size_mem_toL87 a _ hc
  have hszc : BT.size c < BT.size a := by rw [size_D87] at hsz; omega
  have hbc : btLe72 1 (BT.D 1 c) = true := btLe72_toL87 a _ hb hc
  have hbc2 : btLe72 1 c = true := (btLe72_D 1 1 c hbc).2
  have ihc : ∀ b : BT, BT.size b < BT.size c → GateStd87 b := fun b hz => ih b (by omega)
  have hin := inT_dict_ih87 c ihc hbc2 (isStd_of_D (comp_facts82 hs hc).1)
  have hcol : dict (BT.D 1 c) = omegaNF (plus (reg 1) (dict c)) := by
    rw [Trans.Dict.dict_D]
    exact collapse1_eq77 (dict c) hin.1
      (fun z hz => lt_pure73_reg2 (pure73_toList _ (pure73_dict c hbc2) z hz))
  rw [hcol] at h
  rcases mem_Kset_plus (mem_Kset_omegaNF h) with h2 | h2
  · exact (mem_Kset_reg 1 h2).elim
  · exact h2

/-- **§87.3 の主定理。** 走査の一歩の `K` の元は、`a` のある添字 1 の成分 `ψ₁ c` の
    引数 `c` の像の `K` の元であり、しかも Buchholz は `c < a` と `ψ₁ c` の標準性を渡す。 -/
theorem kset_arg87 {a : BT} (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b)
    (hb : btLe72 1 a = true) (hs : BT.isStd (BT.D 0 a) = true)
    {p : (Option Term × Option Term) × (Term × Term)}
    (hp : p ∈ scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1)
    {y : Term} (hy : y ∈ Kset (reg 1) p.2.1 ∨ y ∈ Kset (reg 1) p.2.2) :
    ∃ c, BT.D 1 c ∈ BT.toL a ∧ BT.isStd (BT.D 1 c) = true ∧ BT.lt c a = true ∧
      y ∈ Kset (reg 1) (dict c) := by
  have hmem : p.2 ∈ (wcnf (reg 1) (toList (dict a))).1 := scanSt_mem_snd _ _ _ _ p hp
  have h1 : y ∈ KsetL (reg 1) (bigPart (reg 1) (toList (dict a))) :=
    mem_Kset_wcnf (toList (dict a)) p.2 hmem hy
  obtain ⟨q, hq, hyq⟩ := (mem_KsetL_iff (reg 1) y _).mp h1
  obtain ⟨c, hc, hqe⟩ := big_D1_87 ih hb hs q hq
  refine ⟨c, hc, (comp_facts82 hs hc).1, (comp_facts82 hs hc).2, ?_⟩
  rw [hqe] at hyq
  exact kset_strip_D1_87 ih hb hs hc hyq

/-- **§87.3 の第二の定理 — `aV` の側は歩の指数そのものにつながる。**  §82.1 は
    `aV = wA Ω₁ q` を**一つの成分**まで落とした。その `q` は §87.2 で `dict (ψ₁ c)` だから、
    `K_{Ω₁} aV` の元については **その歩の `aV` を作った成分そのもの**が名指しできる。
    §86 が「両方の和が要る」と言った箇所は `K_{Ω₁} aV` の側だから、効くのはここ。 -/
theorem kset_fst_arg87 {a : BT} (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b)
    (hb : btLe72 1 a = true) (hs : BT.isStd (BT.D 0 a) = true)
    {p : (Option Term × Option Term) × (Term × Term)}
    (hp : p ∈ scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1)
    {y : Term} (hy : y ∈ Kset (reg 1) p.2.1) :
    ∃ c, BT.D 1 c ∈ BT.toL a ∧ BT.isStd (BT.D 1 c) = true ∧ BT.lt c a = true ∧
      p.2.1 = wA (reg 1) (dict (BT.D 1 c)) ∧ y ∈ Kset (reg 1) (dict c) := by
  have hmem : p.2 ∈ (wcnf (reg 1) (toList (dict a))).1 := scanSt_mem_snd _ _ _ _ p hp
  obtain ⟨q, hq, hqe⟩ := wcnf_fst_wA82 (toList (dict a)) p.2 hmem
  obtain ⟨c, hc, hqd⟩ := big_D1_87 ih hb hs q hq
  refine ⟨c, hc, (comp_facts82 hs hc).1, (comp_facts82 hs hc).2, ?_, ?_⟩
  · rw [hqe, hqd]
  · rw [hqe] at hy
    have h2 : y ∈ Kset (reg 1) q := mem_Kset_wA hy
    rw [hqd] at h2
    exact kset_strip_D1_87 ih hb hs hc h2

end

/-! ### §87.4 残余 — Buchholz の `c < a` を手に持った門 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§87 の条項。** §84 の `IdxK84` を、`K` の元の出どころごと書いた形。
    追加の仮説 — `BT.D 1 c ∈ BT.toL a`・`BT.isStd (ψ₁ c)`・`BT.lt c a`・
    `y ∈ Kset Ω₁ (dict c)` — はすべて §87.3 が只で渡す。
    `Ω₁` より下の `K_{Ω₁} aV` の元は §86.3 が片づけるので、条項は
    `lt y Ω₁ = false` の元と `K_{Ω₁} cV` の元にしか課されない。 -/
def ArgK87 (a : BT) : Prop :=
  ∀ p ∈ scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1,
    le (reg 1) p.2.1 = true →
      (∀ (y : Term) (c : BT), BT.D 1 c ∈ BT.toL a → BT.isStd (BT.D 1 c) = true →
        BT.lt c a = true → p.2.1 = wA (reg 1) (dict (BT.D 1 c)) →
        y ∈ Kset (reg 1) (dict c) → lt y (reg 1) = false →
        y ∈ Kset (reg 1) p.2.1 → lt y (idxOf (reg 1) p.1 p.2) = true) ∧
      (∀ (y : Term) (c : BT), BT.D 1 c ∈ BT.toL a → BT.isStd (BT.D 1 c) = true →
        BT.lt c a = true → y ∈ Kset (reg 1) (dict c) →
        y ∈ Kset (reg 1) p.2.2 → lt y (idxOf (reg 1) p.1 p.2) = true)

/-- **§87 の残る仮説。** 部分領域の項について §87 の条項。**証明しない。** -/
def ArgStd87 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → ArgK87 a

/-- **§87.4 の主定理。** 一項ぶんの門は §87 の条項と帰納法の仮説から出る。 -/
theorem gate87_of_arg87 (H : ArgStd87) (a : BT)
    (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b) : GateStd87 a := by
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
  rcases hy with hy1 | hy2
  · cases hlty : lt y (reg 1) with
    | false =>
      obtain ⟨c, hc, hstd, hltc, heq, hyk⟩ := kset_fst_arg87 ih hb hs hq hy1
      exact (H a hb hs q hq hle2).1 y c hc hstd hltc heq hyk hlty hy1
    | true =>
      have hyi : inT y = true := inT_mem_Kset75 q.2.1 hi1 _ y hy1
      have hdT : inT (ddOf75 (reg 1) q.2) = true := inT_ddOf75 (inT_reg 1) hi1 hi2
      obtain ⟨hidxT, _⟩ :=
        inT_idxOf mulDescInT (inT_reg 1) (ltM_reg 1) hst hi1 hl1 hi2 hl2
      exact lt_of_lt_of_le3 (inT_le_fragR y hyi) (inT_le_fragR _ (inT_sub1 hdT))
        (inT_le_fragR _ hidxT)
        (lt_sub1dd_of_lt_reg86 omegaNF_reg1_79 hi1 hi2
          (hnz q.2 (scanSt_mem_snd _ _ _ _ q hq)) hy1 hlty)
        (le_sub1dd_idxOf75 (inT_reg 1) hst hi1 hi2)
  · obtain ⟨c, hc, hstd, hltc, hyk⟩ := kset_arg87 ih hb hs hq (Or.inr hy2)
    exact (H a hb hs q hq hle2).2 y c hc hstd hltc hyk hy2

/-- **§87 の第一の結論。** §73 の残る門は §87 の条項から出る。 -/
theorem psiIdxStep073_of_arg87 (H : ArgStd87) : PsiIdxStep073 :=
  step073_of_gate87 (gate87_of_arg87 H)

/-- **逆向き。** 門から §87 の条項 — 追加の仮説は使わずに落ちるので、分解は過不足がない。 -/
theorem arg87_of_step073 (H : PsiIdxStep073) : ArgStd87 :=
  fun a hb hs p hp hle =>
    ⟨fun y _ _ _ _ _ _ _ hy => (H a hb hs p hp hle).2 y (Or.inl hy),
     fun y _ _ _ _ _ hy => (H a hb hs p hp hle).2 y (Or.inr hy)⟩

/-- **§87 の第二の結論。** 326 行目の証明書が `K` の側で待つのは §87 の条項ひとつ。 -/
theorem certIn_t326_arg87 (H : ArgStd87)
    (HD : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_step73 (psiIdxStep073_of_arg87 H) HD HI HC hacc

end


/-! ### §87.5 引数に `ψ₀` を含まない層 — 門の最初の無条件な断片 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- `ψ₀` を一つも含まない項。 -/
def noD0_87 : BT → Bool
  | .zero => true
  | .D u c => !(u == 0) && noD0_87 c
  | .sum a b => noD0_87 a && noD0_87 b

theorem noD0_D87 {u : Nat} {c : BT} (h : noD0_87 (BT.D u c) = true) :
    u ≠ 0 ∧ noD0_87 c = true := by
  obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
  refine ⟨?_, h2⟩
  intro hc
  rw [hc] at h1
  exact Bool.noConfusion h1

theorem noD0_sum87 {a b : BT} (h : noD0_87 (BT.sum a b) = true) :
    noD0_87 a = true ∧ noD0_87 b = true := (Bool.and_eq_true _ _).mp h

/-- **`ψ₀` を含まない項の像は無条件に 𝔗(M) の中。** 段 1 の枝しか通らないので
    §73.4 の `ksetStepOK_one73` だけで足りる — 門も標準性も要らない。 -/
theorem inT_dict_noD0_87 : ∀ (c : BT), noD0_87 c = true → btLe72 1 c = true →
    inT (dict c) = true ∧ lt (dict c) M = true
  | .zero, _, _ => ⟨inT_zero, lt_zero_M⟩
  | .D u x, hn, hb => by
      obtain ⟨hu0, hnx⟩ := noD0_D87 hn
      obtain ⟨hu, hbx⟩ := btLe72_D 1 u x hb
      have ihh := inT_dict_noD0_87 x hnx hbx
      refine inT_collapse_gap3 u (dict x) ihh.1 ihh.2 ?_
      cases u with
      | zero => exact absurd rfl hu0
      | succ u' =>
        cases u' with
        | zero => exact psiIdxOK_of_stepOK 1 (dict x) ihh.1 ihh.2 (ksetStepOK_one73 x hbx)
        | succ u'' => exact absurd hu (by omega)
  | .sum x y, hn, hb => by
      obtain ⟨hnx, hny⟩ := noD0_sum87 hn
      obtain ⟨hbx, hby⟩ := btLe72_sum 1 x y hb
      have ihx := inT_dict_noD0_87 x hnx hbx
      have ihy := inT_dict_noD0_87 y hny hby
      exact ⟨inT_plus ihx.1 ihy.1, lt_plus_M ihx.1 ihy.1 ihx.2 ihy.2⟩

/-- **`ψ₀` を含まない項の像の `K_{Ω₁}` は空。** `ψ₁(α) = ω^(Ω₁ ⊕ α)` (§77.7) を
    はがすだけ — `K_{Ω₁} Ω₁ = ∅` だから何も残らない。 -/
theorem kset_nil_noD0_87 : ∀ (c : BT), noD0_87 c = true → btLe72 1 c = true →
    ∀ y, y ∈ Kset (reg 1) (dict c) → False
  | .zero, _, _ => by intro y h; cases h
  | .D u x, hn, hb => by
      obtain ⟨hu0, hnx⟩ := noD0_D87 hn
      obtain ⟨hu, hbx⟩ := btLe72_D 1 u x hb
      have hu1 : u = 1 := by omega
      subst hu1
      intro y hy
      have hin := inT_dict_noD0_87 x hnx hbx
      have hcol : dict (BT.D 1 x) = omegaNF (plus (reg 1) (dict x)) := by
        rw [Trans.Dict.dict_D]
        exact collapse1_eq77 (dict x) hin.1
          (fun z hz => lt_pure73_reg2 (pure73_toList _ (pure73_dict x hbx) z hz))
      rw [hcol] at hy
      rcases mem_Kset_plus (mem_Kset_omegaNF hy) with h2 | h2
      · exact mem_Kset_reg 1 h2
      · exact kset_nil_noD0_87 x hnx hbx y h2
  | .sum x y, hn, hb => by
      intro z hz
      obtain ⟨hnx, hny⟩ := noD0_sum87 hn
      obtain ⟨hbx, hby⟩ := btLe72_sum 1 x y hb
      rcases mem_Kset_plus (show z ∈ Kset (reg 1) (plus (dict x) (dict y)) from hz) with h | h
      · exact kset_nil_noD0_87 x hnx hbx z h
      · exact kset_nil_noD0_87 y hny hby z h

/-- **`ψ₀` を含まない項では門は空回り。** 標準性はいっさい要らない。 -/
theorem ksetStepOK_noD0_87 {c : BT} (hn : noD0_87 c = true) (hb : btLe72 1 c = true) :
    KsetStepOK 0 (dict c) := by
  have hin := inT_dict_noD0_87 c hn hb
  refine ksetStepOK_of_idxK84 0 (dict c) hin.1 hin.2 ?_
  intro p hp _ y hy
  exfalso
  have h1 : y ∈ KsetL (reg 1) (bigPart (reg 1) (toList (dict c))) :=
    mem_Kset_wcnf (toList (dict c)) p.2 (scanSt_mem_snd _ _ _ _ p hp) hy
  obtain ⟨q, hq, hyq⟩ := (mem_KsetL_iff (reg 1) y _).mp h1
  refine kset_nil_noD0_87 c hn hb y ?_
  rw [Kset_eq_KsetL]
  exact (mem_KsetL_iff (reg 1) y _).mpr ⟨q, bigPart_sub _ _ q hq, hyq⟩

theorem gate_noD0_87 {c : BT} (hn : noD0_87 c = true) : GateStd87 c :=
  fun hb _ => ksetStepOK_noD0_87 hn hb

/-- どの成分の引数にも `ψ₀` が無い項。`ψ₀` は先頭の一段にしか現れない。 -/
def flat87 : BT → Bool
  | .zero => true
  | .D _ c => noD0_87 c
  | .sum a b => flat87 a && flat87 b

theorem flat87_toL87 : ∀ (a : BT), flat87 a = true → ∀ (u : Nat) (c : BT),
    BT.D u c ∈ BT.toL a → noD0_87 c = true := by
  intro a
  induction a with
  | zero => intro _ u c h; cases h
  | D v e _ =>
    intro hf u c h
    have he : BT.D u c = BT.D v e := List.mem_singleton.mp (show BT.D u c ∈ [BT.D v e] from h)
    have hce : c = e := by injection he
    rw [hce]
    exact hf
  | sum x y ihx ihy =>
    intro hf u c h
    obtain ⟨hfx, hfy⟩ := (Bool.and_eq_true _ _).mp (show (flat87 x && flat87 y) = true from hf)
    rcases List.mem_append.mp (show BT.D u c ∈ BT.toL x ++ BT.toL y from h) with h1 | h1
    · exact ihx hfx u c h1
    · exact ihy hfy u c h1

theorem inT_dict_flat87 : ∀ (a : BT), flat87 a = true → btLe72 1 a = true →
    inT (dict a) = true ∧ lt (dict a) M = true
  | .zero, _, _ => ⟨inT_zero, lt_zero_M⟩
  | .D u x, hf, hb => by
      obtain ⟨hu, hbx⟩ := btLe72_D 1 u x hb
      have hnx : noD0_87 x = true := hf
      have ihh := inT_dict_noD0_87 x hnx hbx
      refine inT_collapse_gap3 u (dict x) ihh.1 ihh.2 ?_
      cases u with
      | zero => exact psiIdxOK_of_stepOK 0 (dict x) ihh.1 ihh.2 (ksetStepOK_noD0_87 hnx hbx)
      | succ u' =>
        cases u' with
        | zero => exact psiIdxOK_of_stepOK 1 (dict x) ihh.1 ihh.2 (ksetStepOK_one73 x hbx)
        | succ u'' => exact absurd hu (by omega)
  | .sum x y, hf, hb => by
      obtain ⟨hfx, hfy⟩ := (Bool.and_eq_true _ _).mp (show (flat87 x && flat87 y) = true from hf)
      obtain ⟨hbx, hby⟩ := btLe72_sum 1 x y hb
      have ihx := inT_dict_flat87 x hfx hbx
      have ihy := inT_dict_flat87 y hfy hby
      exact ⟨inT_plus ihx.1 ihy.1, lt_plus_M ihx.1 ihy.1 ihx.2 ihy.2⟩

/-- **§87.5 の主定理 — 門の最初の無条件な断片。** どの成分の引数にも `ψ₀` が
    無ければ門は定理である。`ψ₀` の成分は §79.6 で `Ω₁` の下に落ちて走査から消え、
    残る添字 1 の成分は `K_{Ω₁}` が空。標準性も帰納法の仮説も要らない。 -/
theorem ksetStepOK_flat87 {a : BT} (hf : flat87 a = true) (hb : btLe72 1 a = true) :
    KsetStepOK 0 (dict a) := by
  have hin := inT_dict_flat87 a hf hb
  refine ksetStepOK_of_idxK84 0 (dict a) hin.1 hin.2 ?_
  intro p hp _ y hy
  exfalso
  have h1 : y ∈ KsetL (reg 1) (bigPart (reg 1) (toList (dict a))) :=
    mem_Kset_wcnf (toList (dict a)) p.2 (scanSt_mem_snd _ _ _ _ p hp) hy
  obtain ⟨q, hq, hyq⟩ := (mem_KsetL_iff (reg 1) y _).mp h1
  have hqne : lt q (reg 1) = false := bigPart_ge87 (reg 1) _ q hq
  obtain ⟨_, t, ht, hte⟩ := toList_dict82 a q (bigPart_sub _ _ q hq)
  obtain ⟨u, c, hue⟩ := mem_toL_D87 a t ht
  subst hue
  have hbt : btLe72 1 (BT.D u c) = true := btLe72_toL87 a _ hb ht
  have hu : u ≤ 1 := (btLe72_D 1 u c hbt).1
  have hbc : btLe72 1 c = true := (btLe72_D 1 u c hbt).2
  have hnc : noD0_87 c = true := flat87_toL87 a hf u c ht
  cases u with
  | zero =>
    have hin2 := inT_dict_noD0_87 c hnc hbc
    have h0 : lt q (reg 1) = true := by
      rw [hte]
      exact lt_collapse0_W79 (dict c) hin2.1 hin2.2
        (psiIdxOK_of_stepOK 0 (dict c) hin2.1 hin2.2 (ksetStepOK_noD0_87 hnc hbc))
    rw [h0] at hqne
    exact Bool.noConfusion hqne
  | succ u' =>
    cases u' with
    | zero =>
      rw [hte] at hyq
      refine kset_nil_noD0_87 (BT.D 1 c) ?_ hbt y hyq
      show (!(1 == 0) && noD0_87 c) = true
      rw [hnc]
      rfl
    | succ u'' => exact absurd hu (by omega)

/-- **§87.5 の系。** その層では §87 の条項も只で通る。 -/
theorem gateStd87_of_flat87 {a : BT} (hf : flat87 a = true) : GateStd87 a :=
  fun hb _ => ksetStepOK_flat87 hf hb

theorem argK87_of_flat87 {a : BT} (hf : flat87 a = true) (hb : btLe72 1 a = true) :
    ArgK87 a :=
  fun p hp hle =>
    ⟨fun y _ _ _ _ _ _ _ hy =>
       (idxK84_of_ksetStepOK (ksetStepOK_flat87 hf hb)) p hp hle y (Or.inl hy),
     fun y _ _ _ _ _ hy =>
       (idxK84_of_ksetStepOK (ksetStepOK_flat87 hf hb)) p hp hle y (Or.inr hy)⟩

end


/-! ### §87.6 測定 (凍結)

**構成を先に書く。**  母集団は §86 のもの (`pop86` 96 個・`qual86` 53 個) を**そのまま使い、
その上にもう一段開けた群を足す**。§86 は「`ψ₁` の塔は三段目からしか発火しない」を見つけて
§84 の二段の母集団を三段に開けた。§87 は同じ操作をもう一度やる — 帽子 `ψ₁^m` を四段以上、
`ψ₀` の引数の第二成分を四段以上に取り、さらに**引数の成分を三つにする**・**`ψ₀` を二重に
入れ子にして内側も発火させる**・**発火する `ψ₀` の項を二つ並べる**、の三方向に広げる。

    twr86 k = ψ₁^k 0,  cp86 m a = ψ₁^m a          (§86 の記法をそのまま使う)
    famP87  h ⊕ ψ₁^m(ψ₀(h ⊕ g)),  h = ψ₁^{k+5}0, m = 4..6, g = ψ₁^{j+4}0    27 個
    famQ87  h ⊕ ψ₁^m(ψ₀(h ⊕ g₁ ⊕ g₂))       (引数が三成分、二つとも別の塔)  27 個
    famR87  h ⊕ ψ₁^m(ψ₀(h ⊕ ψ₁^m(ψ₀(h ⊕ g))))   (`ψ₀` が二重、内側も発火)     9 個
    famS87  h ⊕ ψ₁^m(ψ₀(h ⊕ g)) ⊕ ψ₁^m(ψ₀(h ⊕ g'))  (発火する項が二つ)        9 個
    pop87   = 上の和集合、重複を除いて                                       72 個
    qual87  = そのうち §84 の `okHyp84` をぜんぶ満たすもの                    25 個

測るのは `qual87` 25 個・§86 の `qual86` 53 個・§84 の `qual84` 53 個・326 行目とその
基本列の `r326_84` 41 個の、あわせて 172 項。

**測定の結果。**

  * **§84 の分割条項は四段目で全滅する。**  `qual87` の 25 項**すべて**で `splitb84` が
    落ちる (§75 の対ごとの条件も同じ 25 項で落ちる)。§86 は三段目の母集団で 53 中 10 を
    見つけた。四段目まで開けると例外がなくなる — **`SplitStd84` の反証は §86 の一項だけの
    話ではない。**
  * **`SplitK86` は落ちない。**  `splitb86` は `qual87` の 25 項で失敗 0。§87 は
    「四つ目の反証」を出していない。門 (`idxb84`・`stepOKb`) も失敗 0。
  * **§87.2 は測定でも正しい。**  `d0Below87` — `a` の添字 0 の成分の像が `Ω₁` の下か —
    は `qual87`・`qual86`・`qual84`・`r326_84` の 172 項すべてで真。走査は添字 1 の成分
    しか見ない。
  * **§87.3 も測定でも正しい。**  `kInArg87` — 発火歩の `K` の元が `a` のどれかの添字 1 の
    成分 `ψ₁ c` について `K_{Ω₁}(dict c)` に入っているか — も 159 項 (`r326_84` を除く
    三つ) すべてで真。
  * **否定 — 歩を問わない形は偽。**  `anyStep87` (「どの発火歩の指数より下か」を、`K` の元の
    出どころと歩の対応を切って訊く形) は `qual87` で 25、`qual86` で 31、`qual84` で 3 落ちる。
    **§87 の条項が歩ごとの対応を保つのは飾りではない** — 切ると偽になる。
  * **否定 — §87.5 の無条件な層は薄い。**  `flat87` は `qual87`・`qual86`・`qual84` の
    131 項で **0 個**しか成り立たない。成り立つのは `r326_84` の 41 個の添字のうち **10 個**。
    §87.5 が閉じるのは行の側の一部であって、反例を作るために組んだ母集団の側ではない。
  * **§86.3 の「`Ω₁` より下は只」の枝は、この母集団では空回りする。**  `qual87` の 31 の
    逃げる元も `qual86` の 31 も、ぜんぶ `Ω₁` 以上で、しかもぜんぶ `K_{Ω₁} aV` の側。
    `r326_84` の添字では発火歩の `K_{Ω₁} aV` がそもそも空 (0 個)。§80.7 が数えた
    458/635 はこの母集団ではない。 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

def famP87 : List BT :=
  (List.range 3).flatMap fun k => (List.range 3).flatMap fun m => (List.range 3).map fun j =>
    BT.sum (twr86 (k+5)) (cp86 (m+4) (BT.D 0 (BT.sum (twr86 (k+5)) (twr86 (j+4)))))
def famQ87 : List BT :=
  (List.range 3).flatMap fun m => (List.range 3).flatMap fun i => (List.range 3).map fun j =>
    BT.sum (twr86 5) (cp86 (m+2) (BT.D 0
      (BT.sum (twr86 5) (BT.sum (twr86 (i+3)) (twr86 (j+1))))))
def famR87 : List BT :=
  (List.range 3).flatMap fun m => (List.range 3).map fun j =>
    BT.sum (twr86 5) (cp86 (m+2) (BT.D 0
      (BT.sum (twr86 5) (cp86 (m+2) (BT.D 0 (BT.sum (twr86 5) (twr86 (j+3))))))))
def famS87 : List BT :=
  (List.range 3).flatMap fun m => (List.range 3).map fun j =>
    BT.sum (twr86 5) (BT.sum (cp86 (m+2) (BT.D 0 (BT.sum (twr86 5) (twr86 (j+3)))))
      (cp86 (m+2) (BT.D 0 (BT.sum (twr86 5) (twr86 (j+1))))))

def pop87 : List BT := (famP87 ++ famQ87 ++ famR87 ++ famS87).eraseDups
def qual87 : List BT := pop87.filter okHyp84

/-- §87.2 の中身の判定器 — `a` の添字 0 の成分の像は `Ω₁` の下か。 -/
def d0Below87 (a : BT) : Bool :=
  (BT.toL a).all fun t => match t with
    | BT.D 0 c => lt (dict (BT.D 0 c)) (reg 1)
    | _ => true

/-- §87.3 の中身の判定器 — 発火歩の `K` の元は、`a` のどれかの添字 1 の成分の引数の `K`。 -/
def kInArg87 (a : BT) : Bool :=
  (scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1).all fun p =>
    !(le (reg 1) p.2.1) ||
      ((Kset (reg 1) p.2.1 ++ Kset (reg 1) p.2.2).all fun y =>
        (BT.toL a).any fun t => match t with
          | BT.D 1 c => (Kset (reg 1) (dict c)).contains y
          | _ => false)

/-- §87.3 の第二の定理の中身の判定器 — `K_{Ω₁} aV` の元は、**その歩の `aV` を作った**
    成分の引数の `K` に入っているか。 -/
def fstArg87 (a : BT) : Bool :=
  (scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1).all fun p =>
    !(le (reg 1) p.2.1) ||
      ((Kset (reg 1) p.2.1).all fun y =>
        (BT.toL a).any fun t => match t with
          | BT.D 1 c => (p.2.1 == wA (reg 1) (dict (BT.D 1 c))) &&
              (Kset (reg 1) (dict c)).contains y
          | _ => false)

/-- 歩と `K` の元の対応を切った形。**定理ではない** — 下の否定 2 が偽であることを測る。 -/
def anyStep87 (a : BT) : Bool :=
  let fires := (scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1).filter
    (fun p => le (reg 1) p.2.1)
  fires.all fun p =>
    (fires.flatMap fun q => Kset (reg 1) q.2.1 ++ Kset (reg 1) q.2.2).all fun y =>
      lt y (idxOf (reg 1) p.1 p.2)

-- 母集団の大きさと形。
#guard (pop87.length, qual87.length) == (72, 25)
#guard ((famP87.filter okHyp84).length, (famQ87.filter okHyp84).length,
        (famR87.filter okHyp84).length, (famS87.filter okHyp84).length) == (10, 9, 3, 3)
#guard ((pop87.map BT.size).foldl min 999, (pop87.map BT.size).foldl max 0) == (24, 42)

/-! **否定 1 — §84 の分割条項は四段目で全滅する。** §86 は三段目で 53 中 10 を見つけた。
四段目まで開けると例外がない。 -/

#guard (qual87.filter fun a => !(splitb84 0 (dict a))).length == 25
#guard (qual87.filter fun a => !(localOKb73 0 (dict a))).length == 25
#guard ((famP87.filter fun a => okHyp84 a && !(splitb84 0 (dict a))).length,
        (famQ87.filter fun a => okHyp84 a && !(splitb84 0 (dict a))).length,
        (famR87.filter fun a => okHyp84 a && !(splitb84 0 (dict a))).length,
        (famS87.filter fun a => okHyp84 a && !(splitb84 0 (dict a))).length) == (10, 9, 3, 3)

/-! **肯定 1 — 門も §86 の条項も落ちない。** §87 は四つ目の反証を出していない。 -/

#guard ((qual87.filter fun a => !(splitb86 0 (dict a))).length,
        (qual87.filter fun a => !(idxb84 0 (dict a))).length,
        (qual87.filter fun a => !(stepOKb 0 (dict a))).length) == (0, 0, 0)

/-! **肯定 2 — §87.2 と §87.3 の中身。** 走査は添字 1 の成分しか見ず、`K` の元は
その成分の引数の `K` に入っている。172 項で失敗 0。 -/

#guard ((qual87.filter fun a => !(d0Below87 a)).length,
        (qual86.filter fun a => !(d0Below87 a)).length,
        (qual84.filter fun a => !(d0Below87 a)).length,
        (r326_84.filter fun q => !(d0Below87 q.2)).length) == (0, 0, 0, 0)
#guard ((qual87.filter fun a => !(kInArg87 a)).length,
        (qual86.filter fun a => !(kInArg87 a)).length,
        (qual84.filter fun a => !(kInArg87 a)).length) == (0, 0, 0)
#guard ((qual87.filter fun a => !(fstArg87 a)).length,
        (qual86.filter fun a => !(fstArg87 a)).length,
        (qual84.filter fun a => !(fstArg87 a)).length,
        (r326_84.filter fun q => !(fstArg87 q.2)).length) == (0, 0, 0, 0)
#guard (d0Below87 bad86, kInArg87 bad86, fstArg87 bad86,
        d0Below87 aBad82, kInArg87 aBad82, fstArg87 aBad82)
       == (true, true, true, true, true, true)

/-! **否定 2 — 歩と `K` の元の対応を切ると偽。** §87 の条項が歩ごとの形をしているのは
飾りではない。 -/

#guard ((qual87.filter fun a => !(anyStep87 a)).length,
        (qual86.filter fun a => !(anyStep87 a)).length,
        (qual84.filter fun a => !(anyStep87 a)).length) == (25, 31, 3)

/-! **否定 3 — §87.5 の無条件な層は薄い。** 反例を作るために組んだ三つの母集団 131 項では
一つも成り立たず、成り立つのは 326 行目とその基本列の 41 添字のうち 10。 -/

#guard ((qual87.filter fun a => flat87 a).length,
        (qual86.filter fun a => flat87 a).length,
        (qual84.filter fun a => flat87 a).length,
        (r326_84.filter fun q => flat87 q.2).length, r326_84.length) == (0, 0, 0, 10, 41)
#guard (flat87 bad86, flat87 aBad82) == (false, false)

/-! **肯定 3 — 逃げる元の位置。** `qual87` の 31 も `qual86` の 31 も、ぜんぶ `Ω₁` 以上で
`K_{Ω₁} aV` の側。だから §86.3 の「`Ω₁` より下は只」の枝はこの母集団では空回りする。
326 行目の添字では発火歩の `K_{Ω₁} aV` がそもそも空。 -/

#guard
  (let esc := fun (l : List BT) => l.flatMap fun a =>
     ((scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1).filter
        (fun p => le (reg 1) p.2.1)).flatMap fun p =>
       (Kset (reg 1) p.2.1 ++ Kset (reg 1) p.2.2).filterMap fun y =>
         if lt y (sub1 (ddOf75 (reg 1) p.2)) then none else some (p, y)
   let e := esc qual87
   (e.length, (e.filter fun q => lt q.2 (reg 1)).length,
    (e.filter fun q => !((Kset (reg 1) q.1.2.1).contains q.2)).length,
    (esc qual86).length, ((esc qual86).filter fun q => lt q.2 (reg 1)).length))
  == (31, 0, 0, 31, 0)

#guard
  (r326_84.flatMap fun q =>
    ((scanSt (reg (q.1+1)) (baseOf q.1) (none, none)
       (wcnf (reg (q.1+1)) (toList (dict q.2))).1).filter
       (fun p => le (reg (q.1+1)) p.2.1)).flatMap fun p =>
      Kset (reg (q.1+1)) p.2.1).length == 0

end

/-! ### §87.7 公理 -/


/-! ## §88 THE `K`-ELEMENT IS A COLLAPSE INDEX — AND THE STEP-BLIND FORM OF THAT IS FALSE

§87 stopped proposing sufficient conditions, spent Buchholz's `G(a,0) < a` as far as it goes,
and left the gate as ONE implication, named: from `c < a` in Buchholz's order to
`y < i₀ ⊕ Δ` in `𝔗(M)`, at a `K`-element `y` of `dict c`.  §88 takes the `𝔗(M)` side of that
implication apart.  **It does not close the gate.**  What it does is say what `y` IS.

`K_κ` is not hereditary: `K_{Ω₁}(α)` can dwarf `α` — that is the whole reason 2.1(vi)'s last
conjunct is a condition and not a triviality, and it is why five sections' worth of clauses
comparing `y` against `Δ`, against `i₀`, or against a split of the two have all died.  But the
terms the gate meets are not arbitrary elements of `𝔗(M)`: they are `dict`-images, and in a
`dict`-image the only source of a `K_{Ω₁}`-element is a `ψ_{Ω₁}` emitted by the fold — that
is, a `ψ₀` of the Buchholz side.  §88.1 traces `K_{Ω₁}` through `collapse` itself; §88.2 runs
the trace down the Buchholz term.  The result is that **every `K_{Ω₁}`-element of `dict c` is
bounded by the collapse index of a `ψ₀` occurring inside `c`** — so `y` is never an arbitrary
ordinal, it sits under an index of the very kind the scan is building, and the gate is an
inequality between two collapse indices and nothing else.

WHAT IS PROVED, UNCONDITIONALLY.

  §88.1  **THE TRACEBACK THROUGH `collapse`.**  `mem_Kset_collapse88` : for `x ∈ 𝔗(M)` below
         `M` whose gate holds,

             y ∈ K_{Ω_{u+1}}(ψ_u x)  →  y ≤ idxF88 u x   or   y ∈ K_{Ω_{u+1}}(x).

         `idxF88 u x` is the index the fold ends holding (`none` if the strongly critical
         branch never fires).  Three pieces carry it.  `mem_Kset_psi_reg88` : `K_κ(ψ_κ i)` is inside
         `{i} ∪ K_κ(i)`, because the other two branches of 2.2(vi) give the empty list and
         `K_κ Ω_{u+1} = ∅`.  `le_idx_fold88` : **the scan's index only grows** — every index it ever
         emits is `≤` the one it ends with (§75.2's `le_prev_idxOf75` run along the fold, with
         §64.5's `fold_inv` for the state invariant, which §66.1's `PsiIdxOK` supplies).
         `Kset_fold_snd88` : the fold's accumulated VALUE has `K_κ` inside
         `{≤ the running index} ∪ K_κ(incoming value) ∪ K_κ(the pairs)` — the Veblen branch
         adds only its pair and the base (whose `K_κ` is empty), and the strongly critical
         branch adds `ψ_κ i`, whose `K_κ` is `{i} ∪ K_κ i` and whose `K_κ i` is below `i` for
         free, since `inT (ψ_κ i)` says so.  `mem_Kset_wcnf_snd88` handles the tail `ρ`.

  §88.2  **THE `K`-ELEMENT IS A `ψ₀` INDEX.**  `d0Args88 c` is the list of arguments of the
         `ψ₀`s occurring anywhere in `c`.  `kset_dict_idx88` :

             y ∈ K_{Ω₁}(dict c)  →  ∃ e ∈ d0Args88 c, ∃ j, idxF88 0 (dict e) = some j
                                     ∧ y ≤ j ∧ inT j.

         The induction is on `c` with §87.1's gate-induction hypothesis: the `ψ₁` components
         strip by §77.7 (`kset_strip_D1_88`), the `ψ₁` layer contributes nothing of its own,
         and the `ψ₀` components hand over §88.1.  Standardness comes along for free — a `ψ₀`
         subterm of a standard term is standard AT SUBSCRIPT `0`, which is exactly what
         §87.1's gate wants, so no extra hypothesis appears.

  §88.3  **THE RESIDUE, AND IT IS POINTWISE.**  `IdxK88 a` is §87's `ArgK87` with §88.2's
         output added as hypotheses (`e`, `j`, `y ≤ j`, `inT j`).  Everything added is a
         theorem, so `idxStd88_of_step073` gives the converse and the reduction is exact.
         `gateStd87_of_idxK88` is sharper than §87.4's `gate87_of_arg87` in one further way:
         **it consumes the condition at ONE term**, not globally, so any per-term sufficient
         condition now plugs straight in (§88.5 uses that twice).  `IdxLtK88` is the sharp
         form — same hypotheses, conclusion `j < i₀ ⊕ Δ` instead of `y < i₀ ⊕ Δ` — and it
         implies `IdxK88`.  It is a SUFFICIENT condition, not an equivalent one; §88.6
         measures it clean on all 199 terms.

  §88.4  **THE STEP-BLIND SHARP FORM IS FALSE, AS A THEOREM.**  Drop from `IdxLtK88` the one
         link that ties the index `j` to the step it is asked at — that `j` actually bounds a
         `K`-element of THIS step — and ask instead about every `ψ₀` inside every subscript-`1`
         component of `a`.  `not_idxLtBlindStd88` refutes it, and the counterexample is §82's
         `aBad82` (15 symbols), the same term that killed §75's per-pair clause.  §87.6
         measured the same wall for `K`-elements (`anyStep87`); §88 shows it does not move
         when the `K`-element is replaced by the index that bounds it.

  §88.5  **A WIDER UNCONDITIONAL LAYER THAN §87.5's.**  `flatD1_88 a` asks only that the
         arguments of the SUBSCRIPT-`1` components of `a` mention no `ψ₀`; the `ψ₀` components
         may carry anything, because §87.2 has already put them below `Ω₁` and out of the
         scan's sight.  `gateStd87_of_flatD1_88` proves the gate there.  `flat87 → flatD1_88`
         (`flatD1_of_flat87_88`) and the inclusion is strict — `wid88 = ψ₁ψ₁0 ⊕ ψ₀ψ₀0` is in
         the new layer and not the old (`flat87_lt_flatD1_88`).  `NoIdx88` is the second
         pointwise layer: if none of those `ψ₀`s ever fires, the clause is vacuous.

WHAT IS **NOT** CLAIMED.  The gate is NOT closed.  `IdxStd88` is EQUIVALENT to
`PsiIdxStep073`, so §88 is again a repackaging — what it repackages is the `K`-element itself,
which every section from §75 to §87 treated as an opaque ordinal.  `IdxLtStd88` is not proved
either, and it is not known to follow from the gate (only to imply it).  §86's `SplitK86`,
§87's `ArgStd87`, `LocalK2Snd_78`, `DictHeadLt77`, `CofDenseS1`, `BCofIn71`, `DictLtA74` are
untouched; §76's bridge `dictLtA74_iff76` is NOT used anywhere in §88 — the reduction spends
only Buchholz standardness and the fold's own arithmetic.

WHAT THE MEASUREMENT SAYS (§88.6 gives the construction: §87's `qual87`, §86's `qual86`,
§84's `qual84` and row 326's `r326_84` reused verbatim, plus 27 terms built to fire a branch
none of them ever fired).  199 terms in all.

  * **The new population fires the OTHER clause.**  Over `qual88`'s 54 firing steps the
    `K_{Ω₁} aV` side is EMPTY and the `K_{Ω₁} cV` side has 45 elements; over `qual87`'s 53
    firing steps it is exactly the other way round, 31 and **0**.  **§87's second clause was
    vacuous on every population measured up to now.**  The construction that reaches it is to
    put the `ψ₀` in the summand list of the firing component's argument instead of under its
    `ψ₁` cap.
  * **§88.2 holds on all 199.**  `kLeIdxb88` — every `K_{Ω₁}`-element of a subscript-`1`
    component's argument is under some `ψ₀` index inside it — never fails.
  * **The sharp clause holds on all 199, the step-blind one fails on 127.**
    `idxLtb88` : 0 failures everywhere including all 41 of row 326's indices.
    `idxLtBlindb88` : 27 of `qual88`, 25 of `qual87`, 53 of `qual86`, 22 of `qual84`, 0 of
    `r326_84`.  §88.4 turns that into a theorem.
  * **§84's split clause fails on the `cV` side too.**  `splitb84` is false on 18 of the 27
    (`famG88` 3, `famH88` 6, `famI88` 9) and §75's per-pair clause on all 27.  §86 refuted
    `SplitStd84` on the `aV` side; the refutation is not one-sided.
  * **The gate does not fail.**  `stepOKb`, `idxb84`, `splitb86` : 0 failures on `qual88`.
    §88 is not a fifth refutation of a clause the gate needs.
  * **The wider layer is wider in theory only.**  `flatD1_88` covers the same 10 of row 326's
    41 indices that `flat87` covered, and 0 of the 158 adversarial terms.  `wid88` witnesses
    that the inclusion is strict; the corpus does not.
-/

/-! ### §88.1 崩壊を通した `K` の追跡 — 最後の指数と、その先 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **`ψ_{Ω_{u+1}}` の `K` は引数そのものか引数の `K`。** `K_κ Ω_{u+1} = ∅` だけ使う。 -/
theorem mem_Kset_psi_reg88 {u : Nat} {i y : Term}
    (h : y ∈ Kset (reg (u+1)) (psi (reg (u+1)) i)) : y = i ∨ y ∈ Kset (reg (u+1)) i := by
  rw [show Kset (reg (u+1)) (psi (reg (u+1)) i)
      = (if le (psi (reg (u+1)) i) (kminus (reg (u+1))) then [] else
         if lt (reg (u+1)) (reg (u+1)) then Kset (reg (u+1)) (reg (u+1))
         else i :: (Kset (reg (u+1)) (reg (u+1)) ++ Kset (reg (u+1)) i)) from rfl] at h
  split at h
  · cases h
  · split at h
    · exact absurd h (fun hc => mem_Kset_reg (u+1) hc)
    · rcases List.mem_cons.mp h with h1 | h1
      · exact Or.inl h1
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact absurd h2 (fun hc => mem_Kset_reg (u+1) hc)
        · exact Or.inr h2

/-- 段の底の `K` は空。 -/
theorem mem_Kset_baseOf88 {k y : Term} (u : Nat) (h : y ∈ Kset k (baseOf u)) : False := by
  unfold baseOf at h
  split at h
  · cases h
  · rcases mem_Kset_plus h with h1 | h1
    · exact mem_Kset_reg u h1
    · rw [Kset_one] at h1; cases h1

/-- `wcnf` の尾は「先頭を捨てた列」そのもの。 -/
theorem wcnf_snd_cons88 (w p : Term) (rest : List Term) :
    (wcnf w (p :: rest)).2 = if lt p w = true then ofList (p :: rest) else (wcnf w rest).2 := by
  by_cases hlp : lt p w = true
  · rw [wcnf_cons_lt hlp, if_pos hlp]
  · have hlp' : lt p w = false := bool_false hlp
    rw [wcnf_cons_ge hlp', if_neg hlp]
    cases hr : wcnf w rest with
    | mk fst snd =>
      cases fst with
      | nil => rfl
      | cons ac0 ps =>
        cases ac0 with
        | mk a' c' =>
          show (if (wA w p == a') = true then ((wA w p, plus (wC w p) c') :: ps, snd)
                else ((wA w p, wC w p) :: (a', c') :: ps, snd)).2 = snd
          split <;> rfl

/-- **`wcnf` の尾の `K` は元の列の `K`。** -/
theorem mem_Kset_wcnf_snd88 {k w y : Term} : ∀ (L : List Term),
    y ∈ Kset k (wcnf w L).2 → y ∈ KsetL k L := by
  intro L
  induction L with
  | nil => intro h; cases h
  | cons p rest ih =>
    intro h
    rw [wcnf_snd_cons88] at h
    split at h
    · rw [Kset_ofList] at h; exact h
    · exact mem_KsetL_of_sub (fun a ha => List.Mem.tail _ ha) (ih h)


/-- **走査の指数は伸びる一方。** 入ってきた指数も、途中で吐かれた指数も、
    畳み込みが最後に残す指数以下にある。`ψ` が 𝔗(M) の項であることだけ要る
    (§66.1 の `PsiIdxOK`、門から只で出る)。 -/
theorem le_idx_fold88 {u : Nat} :
    ∀ (l : List (Term × Term)) (s : Option Term × Option Term), StInv s →
      (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
      (∀ p ∈ scanSt (reg (u+1)) (baseOf u) s l, le (reg (u+1)) p.2.1 = true →
          inT (psi (reg (u+1)) (idxOf (reg (u+1)) p.1 p.2)) = true) →
      (∀ i0, s.1 = some i0 → ∃ j, (l.foldl (stepF (reg (u+1)) (baseOf u)) s).1 = some j ∧
          le i0 j = true) ∧
      (∀ p ∈ scanSt (reg (u+1)) (baseOf u) s l, le (reg (u+1)) p.2.1 = true →
          ∃ j, (l.foldl (stepF (reg (u+1)) (baseOf u)) s).1 = some j ∧
            le (idxOf (reg (u+1)) p.1 p.2) j = true) := by
  have hw : inT (reg (u+1)) = true := inT_reg (u+1)
  have hlw : lt (reg (u+1)) M = true := ltM_reg (u+1)
  intro l
  induction l with
  | nil =>
    intro s hs _ _
    refine ⟨?_, ?_⟩
    · intro i0 hi0
      exact ⟨i0, hi0, Evidence.WF.le_self _⟩
    · intro p hp; cases hp
  | cons ac t ih =>
    intro s hs hall hpsi
    have hfoldInv : StInv ((ac :: t).foldl (stepF (reg (u+1)) (baseOf u)) s) :=
      fold_inv mulDescInT hw hlw (inT_baseOf u) (ltM_baseOf u) (ac :: t) s hs hall hpsi
    have hac := hall ac (List.Mem.head _)
    have hmemhead : ((s, ac) : (Option Term × Option Term) × (Term × Term)) ∈
        scanSt (reg (u+1)) (baseOf u) s (ac :: t) := List.Mem.head _
    have hs' : StInv (stepF (reg (u+1)) (baseOf u) s ac) :=
      stepF_inv mulDescInT hw hlw (inT_baseOf u) (ltM_baseOf u) hs hac
        (hpsi (s, ac) hmemhead)
    obtain ⟨IH1, IH2⟩ := ih (stepF (reg (u+1)) (baseOf u) s ac) hs'
      (fun a ha => hall a (List.Mem.tail _ ha))
      (fun p hp => hpsi p (List.Mem.tail _ hp))
    have hfold : ((ac :: t).foldl (stepF (reg (u+1)) (baseOf u)) s)
        = t.foldl (stepF (reg (u+1)) (baseOf u)) (stepF (reg (u+1)) (baseOf u) s ac) := rfl
    have hfire : le (reg (u+1)) ac.1 = true →
        (stepF (reg (u+1)) (baseOf u) s ac).1 = some (idxOf (reg (u+1)) s ac) := by
      intro hle
      rw [stepF_fst, if_pos hle]
    have hstep : ∀ i0, s.1 = some i0 → ∃ i1,
        (stepF (reg (u+1)) (baseOf u) s ac).1 = some i1 ∧ le i0 i1 = true := by
      intro i0 hi0
      cases hle : le (reg (u+1)) ac.1 with
      | true =>
        exact ⟨idxOf (reg (u+1)) s ac, hfire hle,
          le_prev_idxOf75 hw hs hi0 hac.1 hac.2.2.1⟩
      | false =>
        refine ⟨i0, ?_, Evidence.WF.le_self _⟩
        rw [stepF_fst, if_neg (by rw [hle]; exact Bool.noConfusion), hi0]
    refine ⟨?_, ?_⟩
    · intro i0 hi0
      obtain ⟨i1, hi1, hle1⟩ := hstep i0 hi0
      obtain ⟨j, hj, hle2⟩ := IH1 i1 hi1
      refine ⟨j, by rw [hfold]; exact hj, ?_⟩
      have hjT : inT j = true := (hfoldInv.1 j (by rw [hfold]; exact hj)).1
      exact le_trans3 (inT_le_fragR _ (hs.1 i0 hi0).1) (inT_le_fragR _ (hs'.1 i1 hi1).1)
        (inT_le_fragR _ hjT) hle1 hle2
    · intro p hp hle
      rcases List.mem_cons.mp (show p ∈ (s, ac) :: scanSt (reg (u+1)) (baseOf u)
          (stepF (reg (u+1)) (baseOf u) s ac) t from hp) with h | h
      · subst h
        obtain ⟨j, hj, hle2⟩ := IH1 (idxOf (reg (u+1)) s ac) (hfire hle)
        exact ⟨j, by rw [hfold]; exact hj, hle2⟩
      · obtain ⟨j, hj, hle2⟩ := IH2 p h hle
        exact ⟨j, by rw [hfold]; exact hj, hle2⟩


theorem opt_cases88 {a : Type} (o : Option a) : o = none ∨ ∃ v, o = some v := by
  cases o with
  | none => exact Or.inl rfl
  | some v => exact Or.inr ⟨v, rfl⟩

theorem stepF_snd_fire88 {w base : Term} {s : Option Term × Option Term} {ac : Term × Term}
    (h : le w ac.1 = true) :
    (stepF w base s ac).2 = some (psi w (idxOf w s ac)) := by
  unfold stepF; rw [if_pos h]

theorem stepF_snd_veb88 {w base : Term} {s : Option Term × Option Term} {ac : Term × Term}
    (h : le w ac.1 = false) :
    (stepF w base s ac).2 = some (phiNF ac.1
      (plus (match s.2 with | none => base | some v => v)
            (match s.2 with | none => sub1 ac.2 | some _ => ac.2))) := by
  unfold stepF; rw [if_neg (by rw [h]; exact Bool.noConfusion)]; rfl

/-- **畳み込みが最後に持っている値の `K` は三つのどれか。** 指数以下か、入ってきた値の
    `K` か、成分の `K`。ヴェブレン枝は成分と底しか足さず、強臨界枝が足す `ψ_{Ω_{u+1}}` の
    `K` は「指数そのもの」と「指数の `K`」で、どちらも指数以下 (§66.1 の `ψ` が項である
    ことから)。 -/
theorem Kset_fold_snd88 {u : Nat} :
    ∀ (l : List (Term × Term)) (s : Option Term × Option Term), StInv s →
      (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
      (∀ p ∈ scanSt (reg (u+1)) (baseOf u) s l, le (reg (u+1)) p.2.1 = true →
          inT (psi (reg (u+1)) (idxOf (reg (u+1)) p.1 p.2)) = true) →
      ∀ y, y ∈ Kset (reg (u+1))
            ((l.foldl (stepF (reg (u+1)) (baseOf u)) s).2.getD zero) →
        (∃ j, (l.foldl (stepF (reg (u+1)) (baseOf u)) s).1 = some j ∧ le y j = true)
        ∨ (∃ v, s.2 = some v ∧ y ∈ Kset (reg (u+1)) v)
        ∨ (∃ ac, ac ∈ l ∧ (y ∈ Kset (reg (u+1)) ac.1 ∨ y ∈ Kset (reg (u+1)) ac.2)) := by
  have hw : inT (reg (u+1)) = true := inT_reg (u+1)
  have hlw : lt (reg (u+1)) M = true := ltM_reg (u+1)
  intro l
  induction l with
  | nil =>
    intro s _ _ _ y hy
    have hy2 : y ∈ Kset (reg (u+1)) (s.2.getD zero) := hy
    rcases opt_cases88 s.2 with hs2 | ⟨v, hs2⟩
    · rw [hs2] at hy2; cases hy2
    · exact Or.inr (Or.inl ⟨v, hs2, by rw [hs2] at hy2; exact hy2⟩)
  | cons ac t ih =>
    intro s hs hall hpsi y hy
    have hac := hall ac (List.Mem.head _)
    have hmemhead : ((s, ac) : (Option Term × Option Term) × (Term × Term)) ∈
        scanSt (reg (u+1)) (baseOf u) s (ac :: t) := List.Mem.head _
    have hs' : StInv (stepF (reg (u+1)) (baseOf u) s ac) :=
      stepF_inv mulDescInT hw hlw (inT_baseOf u) (ltM_baseOf u) hs hac
        (hpsi (s, ac) hmemhead)
    have hfold : ((ac :: t).foldl (stepF (reg (u+1)) (baseOf u)) s)
        = t.foldl (stepF (reg (u+1)) (baseOf u)) (stepF (reg (u+1)) (baseOf u) s ac) := rfl
    have halls : ∀ a ∈ t, inT a.1 = true ∧ lt a.1 M = true ∧ inT a.2 = true ∧ lt a.2 M = true :=
      fun a ha => hall a (List.Mem.tail _ ha)
    have hpsis : ∀ p ∈ scanSt (reg (u+1)) (baseOf u)
        (stepF (reg (u+1)) (baseOf u) s ac) t, le (reg (u+1)) p.2.1 = true →
          inT (psi (reg (u+1)) (idxOf (reg (u+1)) p.1 p.2)) = true :=
      fun p hp => hpsi p (List.Mem.tail _ hp)
    have hmono := (le_idx_fold88 t (stepF (reg (u+1)) (baseOf u) s ac) hs' halls hpsis).1
    rw [hfold] at hy
    rcases ih (stepF (reg (u+1)) (baseOf u) s ac) hs' halls hpsis y hy with h | h | h
    · exact Or.inl ⟨h.choose, by rw [hfold]; exact h.choose_spec.1, h.choose_spec.2⟩
    · obtain ⟨v, hv, hyv⟩ := h
      cases hle : le (reg (u+1)) ac.1 with
      | true =>
        rw [stepF_snd_fire88 hle] at hv
        have hve : v = psi (reg (u+1)) (idxOf (reg (u+1)) s ac) := (Option.some.inj hv).symm
        rw [hve] at hyv
        have hfst : (stepF (reg (u+1)) (baseOf u) s ac).1
            = some (idxOf (reg (u+1)) s ac) := by rw [stepF_fst, if_pos hle]
        obtain ⟨j, hj, hlej⟩ := hmono (idxOf (reg (u+1)) s ac) hfst
        have hjT : inT j = true :=
          ((fold_inv mulDescInT hw hlw (inT_baseOf u) (ltM_baseOf u) t
            (stepF (reg (u+1)) (baseOf u) s ac) hs' halls hpsis).1 j hj).1
        have hiT : inT (idxOf (reg (u+1)) s ac) = true :=
          (inT_idxOf mulDescInT hw hlw hs hac.1 hac.2.1 hac.2.2.1 hac.2.2.2).1
        refine Or.inl ⟨j, by rw [hfold]; exact hj, ?_⟩
        rcases mem_Kset_psi_reg88 hyv with h1 | h1
        · rw [h1]; exact hlej
        · have hall2 := ksetAll_of_inT_psi (hpsi (s, ac) hmemhead hle)
          have hlty : lt y (idxOf (reg (u+1)) s ac) = true := List.all_eq_true.mp hall2 y h1
          have hyT : inT y = true := inT_mem_Kset75 _ hiT _ y h1
          exact le_trans3 (inT_le_fragR _ hyT) (inT_le_fragR _ hiT) (inT_le_fragR _ hjT)
            (le_of_lt hlty) hlej
      | false =>
        rw [stepF_snd_veb88 hle] at hv
        have hve : v = phiNF ac.1
            (plus (match s.2 with | none => baseOf u | some v => v)
                  (match s.2 with | none => sub1 ac.2 | some _ => ac.2)) :=
          (Option.some.inj hv).symm
        rw [hve] at hyv
        rcases mem_Kset_phiNF hyv with h1 | h1
        · exact Or.inr (Or.inr ⟨ac, List.Mem.head _, Or.inl h1⟩)
        · rcases mem_Kset_plus h1 with h2 | h2
          · rcases opt_cases88 s.2 with hs2 | ⟨v0, hs2⟩
            · rw [hs2] at h2
              exact absurd h2 (fun hc => mem_Kset_baseOf88 u hc)
            · rw [hs2] at h2
              exact Or.inr (Or.inl ⟨v0, hs2, h2⟩)
          · refine Or.inr (Or.inr ⟨ac, List.Mem.head _, Or.inr ?_⟩)
            rcases opt_cases88 s.2 with hs2 | ⟨v0, hs2⟩
            · rw [hs2] at h2; exact mem_Kset_sub1 h2
            · rw [hs2] at h2; exact h2
    · obtain ⟨a2, ha2, hy2⟩ := h
      exact Or.inr (Or.inr ⟨a2, List.Mem.tail _ ha2, hy2⟩)

/-- **畳み込みが最後に持っている指数。** `none` なら強臨界枝は一度も発火していない。 -/
def idxF88 (u : Nat) (x : Term) : Option Term :=
  ((wcnf (reg (u+1)) (toList x)).1.foldl (init := ((none : Option Term), (none : Option Term)))
    (stepF (reg (u+1)) (baseOf u))).1

/-- 最後の指数は 𝔗(M) の項。 -/
theorem inT_idxF88 {u : Nat} {x : Term} (hx : inT x = true) (hlx : lt x M = true)
    (Hp : PsiIdxOK u x) {j : Term} (hj : idxF88 u x = some j) :
    inT j = true ∧ lt j M = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨_, hallOK⟩ :=
    wcnf_spec_sc (inT_reg (u+1)) (isSC_reg_succ u) (toList x) hc hd (ltM_toList x hx hlx)
  exact (fold_inv mulDescInT (inT_reg (u+1)) (ltM_reg (u+1)) (inT_baseOf u) (ltM_baseOf u)
    (wcnf (reg (u+1)) (toList x)).1 (none, none) stInv_none hallOK Hp).1 j hj

/-- **§88.1 の主定理 — 崩壊の像の `K` の追跡。** `ψ_u` の像の `K` の元は、その崩壊が
    最後に持つ指数以下であるか、引数の `K` の元であるかのどちらか。前者が
    「この `ψ` が生んだ分」、後者が「引数から持ち越された分」。 -/
theorem mem_Kset_collapse88 {u : Nat} {x y : Term} (hx : inT x = true) (hlx : lt x M = true)
    (Hp : PsiIdxOK u x) (h : y ∈ Kset (reg (u+1)) (collapse u x)) :
    (∃ j, idxF88 u x = some j ∧ le y j = true) ∨ y ∈ Kset (reg (u+1)) x := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨_, hallOK⟩ :=
    wcnf_spec_sc (inT_reg (u+1)) (isSC_reg_succ u) (toList x) hc hd (ltM_toList x hx hlx)
  rw [collapse_eq] at h
  rcases mem_Kset_plus (mem_Kset_omegaNF h) with h2 | h2
  · exact absurd h2 (fun hc2 => mem_Kset_reg u hc2)
  · rcases mem_Kset_plus h2 with h3 | h3
    · rcases Kset_fold_snd88 (wcnf (reg (u+1)) (toList x)).1 (none, none) stInv_none
        hallOK Hp y h3 with h4 | h4 | h4
      · exact Or.inl h4
      · obtain ⟨v, hv, _⟩ := h4; cases hv
      · obtain ⟨ac, hac, hy⟩ := h4
        refine Or.inr ?_
        rw [Kset_eq_KsetL]
        exact mem_KsetL_of_sub (fun a ha => bigPart_sub _ _ a ha)
          (mem_Kset_wcnf (toList x) ac hac hy)
    · refine Or.inr ?_
      rw [Kset_eq_KsetL]
      exact mem_Kset_wcnf_snd88 (toList x) h3

end

/-! ### §88.2 `K` の元は `ψ₀` の指数 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **`ψ₀` の引数を全部集める。** 深さは問わない。 -/
def d0Args88 : BT → List BT
  | .zero => []
  | .D u c => if u == 0 then c :: d0Args88 c else d0Args88 c
  | .sum a b => d0Args88 a ++ d0Args88 b

theorem d0Args88_D0 (c : BT) : d0Args88 (BT.D 0 c) = c :: d0Args88 c := by
  show (if (0 : Nat) == 0 then c :: d0Args88 c else d0Args88 c) = _
  rfl

theorem d0Args88_D1 (c : BT) : d0Args88 (BT.D 1 c) = d0Args88 c := by
  show (if (1 : Nat) == 0 then c :: d0Args88 c else d0Args88 c) = _
  rfl

/-- `ψ₀` を含まない項には `ψ₀` の引数が無い。 -/
theorem d0Args88_noD0_87 : ∀ (c : BT), noD0_87 c = true → d0Args88 c = []
  | .zero, _ => rfl
  | .D u x, hn => by
      obtain ⟨hu0, hnx⟩ := noD0_D87 hn
      show (if u == 0 then x :: d0Args88 x else d0Args88 x) = []
      rw [if_neg (by
        intro hc
        exact hu0 (by
          have := (beq_iff_eq (a := u) (b := 0)).mp hc
          exact this))]
      exact d0Args88_noD0_87 x hnx
  | .sum x y, hn => by
      obtain ⟨hnx, hny⟩ := noD0_sum87 hn
      show d0Args88 x ++ d0Args88 y = []
      rw [d0Args88_noD0_87 x hnx, d0Args88_noD0_87 y hny]
      rfl

/-- `ψ₁` の像から `ω^(Ω₁ ⊕ ·)` をはがす、単独版 (§87.3 の `kset_strip_D1_87`)。 -/
theorem kset_strip_D1_88 {c : BT} (ih : ∀ b : BT, BT.size b < BT.size c → GateStd87 b)
    (hbc : btLe72 1 c = true) (hsc : BT.isStd c = true) {y : Term}
    (h : y ∈ Kset (reg 1) (dict (BT.D 1 c))) : y ∈ Kset (reg 1) (dict c) := by
  have hin := inT_dict_ih87 c ih hbc hsc
  have hcol : dict (BT.D 1 c) = omegaNF (plus (reg 1) (dict c)) := by
    rw [Trans.Dict.dict_D]
    exact collapse1_eq77 (dict c) hin.1
      (fun z hz => lt_pure73_reg2 (pure73_toList _ (pure73_dict c hbc) z hz))
  rw [hcol] at h
  rcases mem_Kset_plus (mem_Kset_omegaNF h) with h2 | h2
  · exact (mem_Kset_reg 1 h2).elim
  · exact h2

/-- **§88.2 の主定理 — `K` の元はどれも `ψ₀` の指数以下。**  `dict c` の `K_{Ω₁}` の元は、
    `c` のどこかに現れる `ψ₀ e` について、その崩壊が最後に持つ指数以下にある。
    §87.3 が「`K` の元は成分の引数の `K`」まで落としたところを、`ψ₀` の指数まで落とす。 -/
theorem kset_dict_idx88 : ∀ (c : BT), (∀ b : BT, BT.size b < BT.size c → GateStd87 b) →
    btLe72 1 c = true → BT.isStd c = true →
    ∀ y ∈ Kset (reg 1) (dict c),
      ∃ e ∈ d0Args88 c, ∃ j, idxF88 0 (dict e) = some j ∧ le y j = true ∧ inT j = true
  | .zero, _, _, _ => by intro y hy; cases hy
  | .D u x, ih, hb, hs => by
      intro y hy
      obtain ⟨hu, hbx⟩ := btLe72_D 1 u x hb
      have hsx : BT.isStd x = true := isStd_of_D hs
      have hsz : BT.size x < BT.size (BT.D u x) := by rw [size_D87]; omega
      have ihx : ∀ b : BT, BT.size b < BT.size x → GateStd87 b := fun b hz => ih b (by omega)
      cases u with
      | zero =>
        have hin := inT_dict_ih87 x ihx hbx hsx
        have hgate : KsetStepOK 0 (dict x) := ih x hsz hbx hs
        have hpi : PsiIdxOK 0 (dict x) := psiIdxOK_of_stepOK 0 (dict x) hin.1 hin.2 hgate
        rw [Trans.Dict.dict_D] at hy
        rcases mem_Kset_collapse88 hin.1 hin.2 hpi hy with h1 | h1
        · obtain ⟨j, hj, hlej⟩ := h1
          exact ⟨x, by rw [d0Args88_D0]; exact List.Mem.head _, j, hj, hlej,
            (inT_idxF88 hin.1 hin.2 hpi hj).1⟩
        · obtain ⟨e, he, hj⟩ := kset_dict_idx88 x ihx hbx hsx y h1
          exact ⟨e, by rw [d0Args88_D0]; exact List.Mem.tail _ he, hj⟩
      | succ u' =>
        cases u' with
        | zero =>
          have h1 := kset_strip_D1_88 ihx hbx hsx hy
          obtain ⟨e, he, hj⟩ := kset_dict_idx88 x ihx hbx hsx y h1
          exact ⟨e, by rw [d0Args88_D1]; exact he, hj⟩
        | succ u'' => exact absurd hu (by omega)
  | .sum x z, ih, hb, hs => by
      intro y hy
      obtain ⟨hbx, hbz⟩ := btLe72_sum 1 x z hb
      obtain ⟨hsx, hsz2⟩ := isStd_of_sum hs
      have hzx : BT.size x < BT.size (BT.sum x z) := by
        rw [size_sum87]; have := size_pos87 z; omega
      have hzz : BT.size z < BT.size (BT.sum x z) := by
        rw [size_sum87]; have := size_pos87 x; omega
      rw [Trans.Dict.dict_sum] at hy
      rcases mem_Kset_plus hy with h1 | h1
      · obtain ⟨e, he, hj⟩ := kset_dict_idx88 x (fun b hb2 => ih b (by omega)) hbx hsx y h1
        exact ⟨e, List.mem_append.mpr (Or.inl he), hj⟩
      · obtain ⟨e, he, hj⟩ := kset_dict_idx88 z (fun b hb2 => ih b (by omega)) hbz hsz2 y h1
        exact ⟨e, List.mem_append.mpr (Or.inr he), hj⟩

end



/-! ### §88.3 残余 — ふたつの崩壊の指数の比較 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§88 の条項。** §87 の `ArgK87` に §88.2 が只で渡すもの — 「`K` の元 `y` は `c` の
    どこかの `ψ₀ e` の崩壊指数 `j` 以下」 — を足した形。足したものはすべて定理だから、
    門との同値は保たれる (`idxStd88_of_step073` が逆向き)。 -/
def IdxK88 (a : BT) : Prop :=
  ∀ p ∈ scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1,
    le (reg 1) p.2.1 = true → inT (idxOf (reg 1) p.1 p.2) = true →
      ∀ (y : Term) (c e : BT) (j : Term),
        BT.D 1 c ∈ BT.toL a → BT.isStd (BT.D 1 c) = true → BT.lt c a = true →
        e ∈ d0Args88 c → idxF88 0 (dict e) = some j → inT j = true → le y j = true →
        inT y = true → y ∈ Kset (reg 1) (dict c) →
        (y ∈ Kset (reg 1) p.2.1 ∨ y ∈ Kset (reg 1) p.2.2) →
        lt y (idxOf (reg 1) p.1 p.2) = true

/-- **鋭い形 — `y` を落として指数どうしを比べる。**  仮説は `IdxK88` と同じ (歩と成分の
    結びつき `y ∈ K_{Ω₁}(dict c)` と `y ∈ K_{Ω₁} aV ∪ K_{Ω₁} cV` を含む) で、結論だけ
    `j < i₀ ⊕ Δ` に強めたもの。`IdxK88` を出す。**門から出るとは限らない** —
    十分条件であって同値ではない。§88.5 が 199 項で測る。 -/
def IdxLtK88 (a : BT) : Prop :=
  ∀ p ∈ scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1,
    le (reg 1) p.2.1 = true → inT (idxOf (reg 1) p.1 p.2) = true →
      ∀ (y : Term) (c e : BT) (j : Term),
        BT.D 1 c ∈ BT.toL a → BT.isStd (BT.D 1 c) = true → BT.lt c a = true →
        e ∈ d0Args88 c → idxF88 0 (dict e) = some j → inT j = true → le y j = true →
        inT y = true → y ∈ Kset (reg 1) (dict c) →
        (y ∈ Kset (reg 1) p.2.1 ∨ y ∈ Kset (reg 1) p.2.2) →
        lt j (idxOf (reg 1) p.1 p.2) = true

theorem idxK88_of_idxLtK88 {a : BT} (H : IdxLtK88 a) : IdxK88 a := by
  intro p hp hle hidxT y c e j hc hstd hltc he hj hjT hlej hyT hyk hy
  exact lt_of_le_of_lt3 (inT_le_fragR _ hyT) (inT_le_fragR _ hjT) (inT_le_fragR _ hidxT)
    hlej (H p hp hle hidxT y c e j hc hstd hltc he hj hjT hlej hyT hyk hy)

/-- **§88 の残る仮説。** 部分領域の項について §88 の条項。**証明しない。** -/
def IdxStd88 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → IdxK88 a

/-- 鋭い形の大域版。**証明しない。** -/
def IdxLtStd88 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → IdxLtK88 a

theorem idxStd88_of_idxLtStd88 (H : IdxLtStd88) : IdxStd88 :=
  fun a hb hs => idxK88_of_idxLtK88 (H a hb hs)

/-- **§88.3 の主定理。** 一項ぶんの門は §88 の条項と帰納法の仮説から出る。
    §87.4 の `gate87_of_arg87` と違い、条項が要るのは**その項ひとつ**だけ。 -/
theorem gateStd87_of_idxK88 (a : BT)
    (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b)
    (H : btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → IdxK88 a) : GateStd87 a := by
  intro hb hs
  have hin := inT_dict_ih87 a ih hb (isStd_of_D hs)
  obtain ⟨hcL, hdL⟩ := inT_toList (dict a) hin.1
  obtain ⟨_, hallOK⟩ :=
    wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList (dict a)) hcL hdL
      (ltM_toList (dict a) hin.1 hin.2)
  intro p hp hle
  refine scan_idx84 (wcnf (reg 1) (toList (dict a))).1 (none, none)
    stInv_none (kInv75_none 0) hallOK ?_ p hp hle
  intro q hq hle2 hst y hy
  obtain ⟨hi1, hl1, hi2, hl2⟩ := hallOK q.2 (scanSt_mem_snd _ _ _ _ q hq)
  obtain ⟨hidxT, _⟩ := inT_idxOf mulDescInT (inT_reg 1) (ltM_reg 1) hst hi1 hl1 hi2 hl2
  obtain ⟨c, hc, hstd, hltc, hyk⟩ := kset_arg87 ih hb hs hq hy
  have hszc0 : BT.size (BT.D 1 c) ≤ BT.size a := size_mem_toL87 a _ hc
  have hszc : BT.size c < BT.size a := by rw [size_D87] at hszc0; omega
  have hbc : btLe72 1 c = true := (btLe72_D 1 1 c (btLe72_toL87 a _ hb hc)).2
  have hsc : BT.isStd c = true := isStd_of_D hstd
  have ihc : ∀ b : BT, BT.size b < BT.size c → GateStd87 b := fun b hz => ih b (by omega)
  have hinc := inT_dict_ih87 c ihc hbc hsc
  have hyT : inT y = true := inT_mem_Kset75 (dict c) hinc.1 _ y hyk
  obtain ⟨e, he, j, hj, hlej, hjT⟩ := kset_dict_idx88 c ihc hbc hsc y hyk
  exact H hb hs q hq hle2 hidxT y c e j hc hstd hltc he hj hjT hlej hyT hyk hy

/-- **§88 の第一の結論。** §73 の残る門は §88 の条項から出る。 -/
theorem psiIdxStep073_of_idxStd88 (H : IdxStd88) : PsiIdxStep073 :=
  step073_of_gate87 (fun a ih => gateStd87_of_idxK88 a ih (fun hb hs => H a hb hs))

theorem psiIdxStep073_of_idxLtStd88 (H : IdxLtStd88) : PsiIdxStep073 :=
  psiIdxStep073_of_idxStd88 (idxStd88_of_idxLtStd88 H)

/-- **逆向き。** 足した仮説はすべて落ちるので、分解は過不足がない。 -/
theorem idxStd88_of_step073 (H : PsiIdxStep073) : IdxStd88 := by
  intro a hb hs p hp hle _ y _ _ _ _ _ _ _ _ _ _ _ _ hy
  exact (H a hb hs p hp hle).2 y hy

/-- **§88 の第二の結論。** 326 行目の証明書が `K` の側で待つのは §88 の条項ひとつ。 -/
theorem certIn_t326_idx88 (H : IdxStd88)
    (HD : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_step73 (psiIdxStep073_of_idxStd88 H) HD HI HC hacc

end

/-! ### §88.4 否定 — 歩と成分の結びつきを切ると鋭い形は偽 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **結びつきを切った鋭い形。** `IdxLtK88` から「`j` はこの歩の `K` の元 `y` を実際に
    押さえている」を落として、`a` のどの添字 1 の成分の、どの `ψ₀` の指数についても
    訊く形。**偽** — `not_idxLtBlindStd88`。 -/
def IdxLtBlind88 (a : BT) : Prop :=
  ∀ p ∈ scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1,
    le (reg 1) p.2.1 = true →
      ∀ (c e : BT) (j : Term), BT.D 1 c ∈ BT.toL a → e ∈ d0Args88 c →
        idxF88 0 (dict e) = some j → lt j (idxOf (reg 1) p.1 p.2) = true

def IdxLtBlindStd88 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → IdxLtBlind88 a

/-- 判定器。 -/
def idxLtBlindb88 (a : BT) : Bool :=
  (scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1).all fun p =>
    !(le (reg 1) p.2.1) ||
      ((BT.toL a).all fun t => match t with
        | BT.D 1 c => (d0Args88 c).all fun e =>
            match idxF88 0 (dict e) with
            | none => true
            | some j => lt j (idxOf (reg 1) p.1 p.2)
        | _ => true)

theorem b88_of_idxLtBlind88 {a : BT} (H : IdxLtBlind88 a) : idxLtBlindb88 a = true := by
  show ((scanSt (reg 1) (baseOf 0) (none, none)
    (wcnf (reg 1) (toList (dict a))).1).all _) = true
  rw [List.all_eq_true]
  intro p hp
  cases hle : le (reg 1) p.2.1 with
  | false => rfl
  | true =>
    rw [Bool.not_true, Bool.false_or, List.all_eq_true]
    intro t ht
    cases t with
    | zero => rfl
    | sum x z => rfl
    | D u c =>
      cases u with
      | zero => rfl
      | succ u' =>
        cases u' with
        | zero =>
          show ((d0Args88 c).all _) = true
          rw [List.all_eq_true]
          intro e he
          cases hj : idxF88 0 (dict e) with
          | none => rfl
          | some j => exact H p hp hle c e j ht he hj
        | succ u'' => rfl

/-- **§88.4 の主定理 — 結びつきを切った鋭い形は偽。**  反証項は §82 の `aBad82`
    (記号 15 個) で足りる。§87.6 の `anyStep87` が「歩を問わない形は偽」と測ったのと
    同じ壁が、`K` の元を指数に置き換えても残る。 -/
theorem not_idxLtBlind88_aBad82 : ¬ IdxLtBlind88 aBad82 := by
  intro H
  have h := b88_of_idxLtBlind88 H
  rw [show idxLtBlindb88 aBad82 = false from by decide] at h
  exact Bool.noConfusion h

theorem not_idxLtBlindStd88 : ¬ IdxLtBlindStd88 := fun H =>
  not_idxLtBlind88_aBad82 (H aBad82 aBad82_hyps.1 aBad82_hyps.2.1)

end

/-! ### §88.5 無条件に通る層 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 添字 1 の成分の引数にだけ `ψ₀` が無いこと。§87.5 の `flat87` より弱い —
    `ψ₀` の成分の引数には何を入れてもよい。 -/
def flatD1_88 (a : BT) : Bool :=
  (BT.toL a).all fun t => match t with
    | BT.D 1 c => noD0_87 c
    | _ => true

theorem noD0_of_flatD1_88 {a : BT} (hf : flatD1_88 a = true) {c : BT}
    (hc : BT.D 1 c ∈ BT.toL a) : noD0_87 c = true :=
  List.all_eq_true.mp hf (BT.D 1 c) hc

/-- §87.5 の層は §88.5 の層に含まれる。 -/
theorem flatD1_of_flat87_88 {a : BT} (hf : flat87 a = true) : flatD1_88 a = true := by
  unfold flatD1_88
  rw [List.all_eq_true]
  intro t ht
  cases t with
  | zero => rfl
  | sum x y => rfl
  | D u c =>
    cases u with
    | zero => rfl
    | succ u' =>
      cases u' with
      | zero => exact flat87_toL87 a hf 1 c ht
      | succ u'' => rfl

/-- §88.5 の層が §87.5 の層より真に広いことの証人。 -/
def wid88 : BT := BT.sum (BT.D 1 (BT.D 1 BT.zero)) (BT.D 0 (BT.D 0 BT.zero))

/-- **包含は真に広い。** `wid88 = ψ₁ψ₁0 ⊕ ψ₀ψ₀0` は §88.5 の層に入り §87.5 の層に入らない。 -/
theorem flat87_lt_flatD1_88 :
    flat87 wid88 = false ∧ flatD1_88 wid88 = true ∧
    btLe72 1 wid88 = true ∧ BT.isStd (BT.D 0 wid88) = true :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem idxK88_of_flatD1_88 {a : BT} (hf : flatD1_88 a = true) : IdxK88 a := by
  intro p hp hle hidxT y c e j hc hstd hltc he hj hjT hlej hyT hyk hy
  rw [d0Args88_noD0_87 c (noD0_of_flatD1_88 hf hc)] at he
  cases he

/-- **§88.5 の主定理 — §87.5 より広い無条件の層。**  添字 1 の成分の引数に `ψ₀` が
    無ければ門は定理。`ψ₀` の成分の引数には何を入れてもよい (そこは §87.2 が `Ω₁` の
    下に落として走査から消す)。 -/
theorem gateStd87_of_flatD1_88 {a : BT}
    (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b) (hf : flatD1_88 a = true) :
    GateStd87 a :=
  gateStd87_of_idxK88 a ih (fun _ _ => idxK88_of_flatD1_88 hf)

/-- 添字 1 の成分の中の `ψ₀` が一つも発火しない層。 -/
def NoIdx88 (a : BT) : Prop :=
  ∀ c : BT, BT.D 1 c ∈ BT.toL a → ∀ e ∈ d0Args88 c, idxF88 0 (dict e) = none

theorem idxK88_of_noIdx88 {a : BT} (H : NoIdx88 a) : IdxK88 a := by
  intro p hp hle hidxT y c e j hc hstd hltc he hj hjT hlej hyT hyk hy
  rw [H c hc e he] at hj
  cases hj

theorem gateStd87_of_noIdx88 {a : BT}
    (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b) (H : NoIdx88 a) : GateStd87 a :=
  gateStd87_of_idxK88 a ih (fun _ _ => idxK88_of_noIdx88 H)

end


/-! ### §88.6 測定 (凍結)

**構成を先に書く。**  母集団は §87 のもの (`qual87` 25 個)・§86 の `qual86` 53 個・
§84 の `qual84` 53 個・326 行目とその基本列 `r326_84` 41 個を**そのまま使い**、その上に
**§87 までのどの母集団も一度も踏んでいない枝**を足す。§87.6 が数えた 31 個の逃げる元は
ぜんぶ `K_{Ω₁} aV` の側だった。`K_{Ω₁} cV` の側が発火するには、発火する成分 `ψ₁ c` の
引数 `c` が「発火するだけの `ψ₁` の塔」と「尾に `ψ₀`」を**同時に**持たねばならない。
§86・§87 の族は `ψ₀` を帽子 `ψ₁^m` の**内側**に置くので、その `ψ₀` は `wA` の側へ回り、
`wC` はいつも `1` だった。§88 の族は `ψ₀` を発火する成分の引数の**直下の和**に置く。

    twr86 k = ψ₁^k 0                                  (§86 の記法)
    famG88  h ⊕ ψ₁(ψ₁^{k+2}0 ⊕ ψ₀(h ⊕ g))                             9 個
    famH88  h ⊕ ψ₁(ψ₁^{k+3}0 ⊕ ψ₀(h ⊕ g') ⊕ ψ₀(h ⊕ g))  (尾が二つ)      9 個
    famI88  h ⊕ ψ₁(ψ₁^{k+2}0 ⊕ ψ₀(h ⊕ ψ₁(ψ₁^{k+2}0 ⊕ ψ₀(h ⊕ g))))     9 個
                                                       (`ψ₀` が二重、内側も同じ形)
    pop88 = 上の和集合 27 個、qual88 = §84 の `okHyp84` を満たすもの 27 個 (全部)

測るのは `qual88` 27・`qual87` 25・`qual86` 53・`qual84` 53・`r326_84` 41 の
あわせて **199 項**。

**測定の結果。**

  * **母集団は新しい枝に当たっている。**  `qual88` の 54 の発火歩で `K_{Ω₁} aV` の元は
    **0 個**、`K_{Ω₁} cV` の元は **45 個**。`qual87` はちょうど裏返しで、53 の発火歩に
    `aV` が 31・`cV` が **0**。§87 の残余の**第二連言は §87 までのどの母集団でも空回り
    していた** — `cvFire88` は `qual87`・`qual86`・`qual84`・`r326_84` の 172 項で 0、
    `qual88` の 27 項で全部真。
  * **§88.2 は測定でも正しい。**  `kLeIdxb88` — 添字 1 の成分の引数の像の `K` の元が、
    その中の `ψ₀` の崩壊指数のどれか以下か — は 199 項すべてで真。
  * **鋭い条項は落ちない。**  `idxLtb88` (歩と成分の結びつきを保った形) は 199 項すべてで
    真。`r326_84` の 41 添字も含む。
  * **否定 1 — 結びつきを切ると偽。**  `idxLtBlindb88` は `qual88` で 27、`qual87` で 25、
    `qual86` で 53、`qual84` で 22 落ちる (`r326_84` では 0)。**§88.4 はこれを定理に
    している** (`not_idxLtBlindStd88`、反証項は §82 の `aBad82`、記号 15 個)。
    §87.6 の `anyStep87` と同じ壁が、`K` の元を指数に置き換えても残る。
  * **否定 2 — §84 の分割条項は `cV` の側でも落ちる。**  `splitb84` は `qual88` の 27 項
    のうち **18 項**で落ちる (`famG88` 3・`famH88` 6・`famI88` 9)、§75 の対ごとの条件は
    27 項全部で落ちる。§86 は `aV` の側で `SplitStd84` を反証した。**同じ条項が `cV` の
    側でも落ちる** — 反証は片側の話ではない。
  * **肯定 — 門は落ちない。**  `stepOKb`・`idxb84`・`splitb86` は `qual88` の 27 項で
    失敗 0。§88 は四つ目の反証を出していない (`SplitK86` も無傷)。
  * **§88.5 の層は §87.5 の層より真に広い。**  `wid88 = ψ₁ψ₁0 ⊕ ψ₀ψ₀0` は
    `flat87` が偽で `flatD1_88` が真。ただし**測定では広がりが見えない**:
    `flatD1_88` は `qual88`・`qual87`・`qual86`・`qual84` の 158 項で 0、
    `r326_84` の 41 添字で 10 — §87.5 とちょうど同じ 10 個である。
    層が広がったのは定理の側であって、行の側ではない。 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

def famG88 : List BT :=
  (List.range 3).flatMap fun k => (List.range 3).map fun j =>
    BT.sum (twr86 (k+5)) (BT.D 1 (BT.sum (twr86 (k+2))
      (BT.D 0 (BT.sum (twr86 (k+5)) (twr86 (j+1))))))
def famH88 : List BT :=
  (List.range 3).flatMap fun k => (List.range 3).map fun j =>
    BT.sum (twr86 (k+5)) (BT.D 1 (BT.sum (twr86 (k+3))
      (BT.sum (BT.D 0 (BT.sum (twr86 (k+5)) (twr86 (j+2))))
              (BT.D 0 (BT.sum (twr86 (k+5)) (twr86 (j+1)))))))
def famI88 : List BT :=
  (List.range 3).flatMap fun k => (List.range 3).map fun j =>
    BT.sum (twr86 (k+5)) (BT.D 1 (BT.sum (twr86 (k+2))
      (BT.D 0 (BT.sum (twr86 (k+5)) (BT.D 1 (BT.sum (twr86 (k+2))
        (BT.D 0 (BT.sum (twr86 (k+5)) (twr86 (j+1))))))))))

def pop88 : List BT := (famG88 ++ famH88 ++ famI88).eraseDups
def qual88 : List BT := pop88.filter okHyp84

/-- §88.2 の中身の判定器 — 添字 1 の成分の引数の像の `K` の元は、その中の `ψ₀` の
    崩壊指数のどれか以下か。 -/
def kLeIdxb88 (a : BT) : Bool :=
  (BT.toL a).all fun t => match t with
    | BT.D 1 c => (Kset (reg 1) (dict c)).all fun y =>
        (d0Args88 c).any fun e => match idxF88 0 (dict e) with
          | none => false
          | some j => le y j
    | _ => true

/-- §88.3 の鋭い条項 `IdxLtK88` の判定器 — 歩と成分の結びつきを保った形。 -/
def idxLtb88 (a : BT) : Bool :=
  (scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1).all fun p =>
    !(le (reg 1) p.2.1) ||
      ((BT.toL a).all fun t => match t with
        | BT.D 1 c => (d0Args88 c).all fun e => match idxF88 0 (dict e) with
            | none => true
            | some j =>
              !((Kset (reg 1) p.2.1 ++ Kset (reg 1) p.2.2).any fun y =>
                  (Kset (reg 1) (dict c)).contains y && le y j) ||
              lt j (idxOf (reg 1) p.1 p.2)
        | _ => true)

/-- 発火歩で `K_{Ω₁} cV` が空でないか — §88 の母集団が新しく踏む枝。 -/
def cvFire88 (a : BT) : Bool :=
  (scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1).any fun p =>
    le (reg 1) p.2.1 && !((Kset (reg 1) p.2.2).isEmpty)

-- 母集団の大きさと形。
#guard (pop88.length, qual88.length) == (27, 27)
#guard ((famG88.filter okHyp84).length, (famH88.filter okHyp84).length,
        (famI88.filter okHyp84).length) == (9, 9, 9)
#guard ((pop88.map BT.size).foldl min 999, (pop88.map BT.size).foldl max 0) == (22, 47)

/-! **肯定 1 — 母集団は `cV` の側の枝に当たっている。** `qual88` の発火歩の `K` は
ぜんぶ `cV` の側、`qual87` の発火歩の `K` はぜんぶ `aV` の側。§87 の残余の第二連言は
§87 までのどの母集団でも空回りしていた。 -/

#guard
  (let fires := qual88.flatMap fun a =>
     (scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1).filter
       (fun p => le (reg 1) p.2.1)
   (fires.length, (fires.flatMap fun p => Kset (reg 1) p.2.1).length,
    (fires.flatMap fun p => Kset (reg 1) p.2.2).length)) == (54, 0, 45)
#guard
  (let fires := qual87.flatMap fun a =>
     (scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1).filter
       (fun p => le (reg 1) p.2.1)
   (fires.length, (fires.flatMap fun p => Kset (reg 1) p.2.1).length,
    (fires.flatMap fun p => Kset (reg 1) p.2.2).length)) == (53, 31, 0)
#guard ((qual88.filter fun a => cvFire88 a).length,
        (qual87.filter fun a => cvFire88 a).length,
        (qual86.filter fun a => cvFire88 a).length,
        (qual84.filter fun a => cvFire88 a).length,
        (r326_84.filter fun q => cvFire88 q.2).length) == (27, 0, 0, 0, 0)

/-! **肯定 2 — §88.2 の中身と鋭い条項。** どちらも 199 項で失敗 0。 -/

#guard ((qual88.filter fun a => !(kLeIdxb88 a)).length,
        (qual87.filter fun a => !(kLeIdxb88 a)).length,
        (qual86.filter fun a => !(kLeIdxb88 a)).length,
        (qual84.filter fun a => !(kLeIdxb88 a)).length,
        (r326_84.filter fun q => !(kLeIdxb88 q.2)).length) == (0, 0, 0, 0, 0)
#guard ((qual88.filter fun a => !(idxLtb88 a)).length,
        (qual87.filter fun a => !(idxLtb88 a)).length,
        (qual86.filter fun a => !(idxLtb88 a)).length,
        (qual84.filter fun a => !(idxLtb88 a)).length,
        (r326_84.filter fun q => !(idxLtb88 q.2)).length) == (0, 0, 0, 0, 0)

/-! **否定 1 — 歩と成分の結びつきを切ると偽。** §88.4 が定理にしている分の測定。 -/

#guard ((qual88.filter fun a => !(idxLtBlindb88 a)).length,
        (qual87.filter fun a => !(idxLtBlindb88 a)).length,
        (qual86.filter fun a => !(idxLtBlindb88 a)).length,
        (qual84.filter fun a => !(idxLtBlindb88 a)).length,
        (r326_84.filter fun q => !(idxLtBlindb88 q.2)).length) == (27, 25, 53, 22, 0)
#guard (idxLtBlindb88 aBad82, idxLtBlindb88 bad86, idxLtb88 aBad82, idxLtb88 bad86,
        kLeIdxb88 aBad82, kLeIdxb88 bad86) == (false, false, true, true, true, true)
#guard (qual88.filter fun a => !(anyStep87 a)).length == 27

/-! **否定 2 — §84 の分割条項は `cV` の側でも落ちる。** §86 の反証は片側の話ではない。 -/

#guard ((qual88.filter fun a => !(splitb84 0 (dict a))).length,
        (qual88.filter fun a => !(localOKb73 0 (dict a))).length) == (18, 27)
#guard ((famG88.filter fun a => !(splitb84 0 (dict a))).length,
        (famH88.filter fun a => !(splitb84 0 (dict a))).length,
        (famI88.filter fun a => !(splitb84 0 (dict a))).length) == (3, 6, 9)

/-! **肯定 3 — 門は落ちない。** §88 は四つ目の反証を出していない。 -/

#guard ((qual88.filter fun a => !(stepOKb 0 (dict a))).length,
        (qual88.filter fun a => !(idxb84 0 (dict a))).length,
        (qual88.filter fun a => !(splitb86 0 (dict a))).length) == (0, 0, 0)

/-! **肯定 4 と否定 3 — 層の広さ。** `wid88` は §88.5 の層に入って §87.5 の層に入らない。
だが母集団と行の上では広がりが見えない — `r326_84` で覆えるのは §87.5 と同じ 10 個。 -/

#guard (okHyp84 wid88, flat87 wid88, flatD1_88 wid88, stepOKb 0 (dict wid88))
       == (true, false, true, true)
#guard ((qual88.filter fun a => flatD1_88 a).length,
        (qual87.filter fun a => flatD1_88 a).length,
        (qual86.filter fun a => flatD1_88 a).length,
        (qual84.filter fun a => flatD1_88 a).length,
        (r326_84.filter fun q => flatD1_88 q.2).length, r326_84.length)
       == (0, 0, 0, 0, 10, 41)

end

/-! ### §88.7 公理 -/

section
open Trans.Recal (bplus)
open Evidence.Region
open Trans.Dict (BT dict)
open TM TM.Term

end

/-! ## §89 THE FOLD ONLY SEES THE PART AT OR ABOVE `Ω₁`, AND WHAT IS LEFT IS TWO CLAUSES

§81 split `CollapseMono0_79` at `Ω₁`, proved the both-below case and the crossing case, and
left one: both arguments at or above `Ω₁`, where the Veblen fold runs on both sides.  §81
also priced that residual — `cexA81 / cexB81` are two `dict` images of Buchholz-standard
terms with `Ω₁ ≤ x < y` and `ψ₀(x) = ψ₀(y) = ζ₀`, so `Ω₁ ≤ x < y ⟹ ψ₀(x) < ψ₀(y)` is FALSE
as a statement about 𝔗(M) and any proof must consume `BT.isStd (ψ₀ ·)`.

**§89 does not close it.  §89 finds the closed form the fold has on that region, uses it to
strip off the part of the residual that has nothing to do with the fold, and leaves TWO
named clauses in place of one — the second of which is not about a pair at all.**  The
closed form is the whole of §89:

        ψ₀(x)  =  ω^( ψ₀(hi x) ⊕ lo x )        for `Ω₁ ≤ x`,

where `hi x` collects the components of `x` at or above `Ω₁` and `lo x` the ones below.
Both halves of it are new here.

WHAT IS PROVED.

  §89.1  **THE BASE-`Ω₁` CNF SPLITS AT `Ω₁`.**  `filter_split89` — a descending component
         list is its big part followed by its small part — then `wcnf_append89` and
         `wcnf_split89`: the pair list of `x` is the pair list of `hi x`, and the tail `ρ`
         is exactly `lo x`.  So `accW89 x = accW89 (hi x)` and `rhoW89 x = lo x`, and the
         fold never looks at `lo x`.

  §89.2  **EVERY VALUE THE FOLD EMITS IS AN ε-NUMBER.**  `isFP_phiNF89` : `φ̄(a,b)` is a
         fixed point of `ω^·` as soon as `a ≠ 0`, in every branch of `phiNF` / `phiNFsucc`
         / `phiNFdefault`; `a ≠ 0` is §81.3's `wcnf_NZ81`.  The strongly critical branch
         emits `ψ_{Ω₁}(·)`, which is strongly critical, hence also a fixed point.
         `StF89` / `foldF89` carry it along the fold, `accW89_facts` bundles it with
         §81.3's `ε₀ ≤ ·` and §79.6's `· < Ω₁`.

  §89.3  **THE CLOSED FORM.**  `collapse0_hi89 : ψ₀(hi x) = accW89 x` — the outer `ω^·` of
         `collapse` is the identity on the accumulator, by §89.2 — and
         `collapse0_split89 : ψ₀(x) = ω^(ψ₀(hi x) ⊕ lo x)`.  The accumulator, which §81
         could only bound from below, now has a name in the language of `dict` itself.

  §89.4  **THE SPLIT IS ORDER-COMPATIBLE.**  `lo_lt_of_lt89` (equal big parts: the small
         parts decide) and `lt_hi89` (unequal big parts: the big parts decide), the latter
         through `lt_append_hi89`, a lexicographic induction along the two component lists:
         at the first genuine mismatch the big parts decide it, and where one big part runs
         out the other side's next component is at or above `Ω₁` while every remaining
         component of the first is below it.

  §89.5  **THE CASE WHERE THE BIG PARTS AGREE IS A THEOREM.**  `lt_collapse0_sameHi89`.
         The fold emits the same accumulator on both sides and what is left is §79.3's
         strict monotonicity of `plus e ·` under §79.2's `ω^·`.  No `K`-condition is spent
         and no two folds are compared.  `lt_collapse0_diffHi89` is the other half, with
         its two inputs named.

  §89.6  **THE ASSEMBLY.**  `collapseMono0Hi_of_89 (Hp) (H : HiMono89) (L : LoDom89) :
         CollapseMono0Hi81`, and through §81: `dictLtA74_89`, `vOfLtA71_89`, `limDecS1_89`,
         `limIncS1_89`, `certIn_t326_89`.  `LoDom89` is discharged on principal terms
         (`loDom_of_sum89` — a principal `dict` image is additively principal, so it has no
         tail) and wherever the tail stays below `ε₀` (`loDom_of_ltE89`).

  §89.7  **THE NEGATIVE THEOREMS.**  `not_hiMonoNoK89` and `not_loDomNoK89` — see the
         measurement below.

WHAT IS **NOT** CLAIMED.  `HiMono89` — §81's residual restricted to TAIL-FREE arguments —
is NOT proved, and is stated as a named hypothesis.  `LoDom89` — every component of `lo x`
is at most `ψ₀(hi x)` — is NOT proved either; it is a NEW hypothesis, not a piece of §81's,
and §89.7 shows it is a real one.  Nothing here proves `PsiIdxOKStd172`, `CofDenseS1` or
`BCofIn71`; §89 changes nothing about those three.  §89 proves nothing at all about the
comparison of two folds: `HiMono89` is exactly as open as `CollapseMono0Hi81` was, on the
sub-class where the tail is empty.  What §89 removes is everything else.

WHAT THE MEASUREMENT SAYS (§89.8 gives the construction).  §81's population opened further:
the same six level-one seeds, the depth line run to eleven layers (nesting 13 deep, 12 on
the `K`-standard part) instead of §81's seven, the same two- and three-term width line, the
same subscript-2/3 line outside the region.  229 terms, 81 of them `K`-standard, and **69 of
those 81 are the residual** — `Ω₁ ≤ dict a`.

  * **The split is 66 / 828 / 2346.**  Of 3240 ordered pairs with `dict a < dict b` on the
    81 `K`-standard terms, 66 are both below `Ω₁` (§81.1), 828 cross (§81.4), 2346 are the
    residual.  §81 measured 36 / 360 / 780 on its smaller population.
  * **§89.5 closes 9 of the 2346, and that is the honest number.**  Exactly 9 of the
    residual pairs have equal big parts.  The point of §89 is not how many pairs it closes
    but what the other 2337 are now asking for: `ψ₀(hi a) < ψ₀(hi b)`, with the tails gone.
  * **`ψ₀(hi ·)` and the accumulator agree, and equal big parts and equal accumulators
    agree.**  0 disagreements on either, on all 69 terms and all 2346 pairs — the receipts
    for §89.3 and for the case split.
  * **1485 of the 2346 pairs are tail-free on BOTH sides**, and 55 of the 69 terms are
    tail-free.  On those `hi` is the identity (`hiW89_self89`), so `HiMono89` is literally
    §81's clause, unchanged, on 63% of the residual.
  * **`HiMono89` needs the `K`-condition, and the counterexample is tail-free.**
    `not_hiMonoNoK89`: weaken `BT.isStd (ψ₀ ·)` to `BT.isStd ·` and §81's `cexA81 / cexB81`
    — `ψ₁ψ₀ψ₁ψ₁0 < ψ₁ψ₁0`, both `BT.isStd`, both with empty tail, both collapsing to `ζ₀` —
    refute it.  Opening the population to depth 13 and width 3 finds **no other** inversion
    in the residual case: it is still the unique one, as it was for §81 at depth 10.
  * **`LoDom89` needs the `K`-condition too, and `BT.isStd` alone is NOT enough.**
    `not_loDomNoK89` : `a = Ω₁ ⊕ ψ₀(Ω₁ ⊕ Ω₁)` has `BT.isStd a = true`, `btLe72 1 a = true`,
    `Ω₁ ≤ dict a`, and `lo (dict a) = ε₁ > ε₀ = ψ₀(hi (dict a))`.  What keeps it out is
    `BT.isStd (ψ₀ a) = false`, and nothing else.  **The 105-term standard corpus does not
    contain it and shows 0 failures**, so this is a case where the population would have
    lied; the witness was built from the statement, not found by search.
  * **And the tail clause must be read component by component.**  `a = Ω₁ ⊕ ψ₀Ω₁ ⊕ ψ₀Ω₁`
    is `K`-standard, satisfies `LoDom89`, and has `lo (dict a) = ε₀ ⊕ ε₀ > ε₀ = ψ₀(hi …)`.
    The clause `le (lo x) (ψ₀ (hi x))` — the shape one writes first — is FALSE inside the
    region.  Only `∀ p ∈ lo x, p ≤ ψ₀(hi x)` is right, and that is what §89.6 uses.
  * **`LoDom89` is free on 60 of the 69 residual terms** by `loDom_of_ltE89` (the tail
    below `ε₀`), and on 22 of them by `loDom_of_sum89` (principal).  0 failures on the
    residual population, and 17 failures once `BT.isStd` is dropped and only the level cap
    is kept.
-/

/-! ### §89.1 底 `Ω₁` の分解は `Ω₁` で切れる

成分列は降順だから、`Ω₁` 以上の成分がぜんぶ前に、下の成分がぜんぶ後ろに並ぶ
(`filter_split89`)。`wcnf` はその切れ目で完全に分かれる — 対の列は前半だけで決まり、
尾は後半そのもの。**畳み込みが見るのは前半だけである。** -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open Trans.Dict (sub1 subAP logOm divAP mulL)
open TM TM.Term
open Evidence.WF

/-- 底 `Ω₁` の畳み込みの累算器。 -/
def accW89 (x : Term) : Term :=
  (((wcnf (reg 1) (toList x)).1.foldl
      (init := ((none : Option Term), (none : Option Term)))
      (stepF (reg 1) (baseOf 0))).2.getD zero)

/-- 底 `Ω₁` の分解の尾。 -/
def rhoW89 (x : Term) : Term := (wcnf (reg 1) (toList x)).2

/-- `Ω₁` 以上の成分だけ集めた項。 -/
def hiW89 (x : Term) : Term := ofList ((toList x).filter (fun p => !lt p (reg 1)))

/-- `Ω₁` より下の成分だけ集めた項。 -/
def loW89 (x : Term) : Term := ofList ((toList x).filter (fun p => lt p (reg 1)))

/-- `collapse 0` は累算器と尾の和の `ω` 冪 — 定義そのもの。 -/
theorem collapse0_raw89 (x : Term) :
    collapse 0 x = omegaNF (plus (reg 0) (plus (accW89 x) (rhoW89 x))) := collapse_eq 0 x

theorem collapse0_acc89 {x : Term} (h : inT (plus (accW89 x) (rhoW89 x)) = true) :
    collapse 0 x = omegaNF (plus (accW89 x) (rhoW89 x)) := by
  rw [collapse0_raw89, show plus (reg 0) (plus (accW89 x) (rhoW89 x))
      = plus zero (plus (accW89 x) (rhoW89 x)) from rfl, plus_zero_left_inT h]

/-- **成分列は `Ω₁` で切れる。** 降順なので `Ω₁` 以上の成分が前、下の成分が後ろ。 -/
theorem filter_split89 : ∀ (l : List Term), inTL l = true → descL l = true →
    l = l.filter (fun p => !lt p (reg 1)) ++ l.filter (fun p => lt p (reg 1)) := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons p t ih =>
    intro hc hd
    obtain ⟨⟨_, hip⟩, hct⟩ := inTL_cons.mp hc
    have hdt := descL_tail hd
    by_cases hlp : lt p (reg 1) = true
    · have hall : ∀ q ∈ t, lt q (reg 1) = true := by
        intro q hq
        have hle := descL_bound_inT t p hip hct hd q hq
        have hiq : inT q = true := inTL_inT (by
          exact inT_ofList (p :: t) hc hd) q (by
          rw [toList_ofList (p :: t) (fun z hz =>
            ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hc z hz)).1)]
          exact List.Mem.tail _ hq)
        exact lt_of_le_of_lt3 (inT_le_fragR q hiq) (inT_le_fragR p hip)
          (inT_le_fragR _ inT_W79) hle hlp
      have h1 : t.filter (fun p => !lt p (reg 1)) = [] := by
        refine List.filter_eq_nil_iff.mpr ?_
        intro q hq
        rw [hall q hq]
        exact Bool.noConfusion
      have h2 : t.filter (fun p => lt p (reg 1)) = t := by
        refine List.filter_eq_self.mpr ?_
        intro q hq; exact hall q hq
      rw [List.filter_cons_of_neg (by rw [hlp]; exact Bool.noConfusion),
        List.filter_cons_of_pos (by rw [hlp]), h1, h2]
      rfl
    · have hlp' : lt p (reg 1) = false := bool_false hlp
      rw [List.filter_cons_of_pos (by rw [hlp']; rfl),
        List.filter_cons_of_neg (by rw [hlp']; exact Bool.noConfusion)]
      exact congrArg (p :: ·) (ih hct hdt)

theorem toList_hiW89 {x : Term} (hx : inT x = true) :
    toList (hiW89 x) = (toList x).filter (fun p => !lt p (reg 1)) := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  exact toList_ofList _ (fun z hz => ((Bool.and_eq_true _ _).mp
    (List.all_eq_true.mp (inTL_filter _ hc) z hz)).1)

theorem toList_loW89 {x : Term} (hx : inT x = true) :
    toList (loW89 x) = (toList x).filter (fun p => lt p (reg 1)) := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  exact toList_ofList _ (fun z hz => ((Bool.and_eq_true _ _).mp
    (List.all_eq_true.mp (inTL_filter _ hc) z hz)).1)

theorem inT_hiW89 {x : Term} (hx : inT x = true) : inT (hiW89 x) = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  exact inT_filter_ofList hc hd _

theorem inT_loW89 {x : Term} (hx : inT x = true) : inT (loW89 x) = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  exact inT_filter_ofList hc hd _

theorem toList_split89 {x : Term} (hx : inT x = true) :
    toList x = toList (hiW89 x) ++ toList (loW89 x) := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  rw [toList_hiW89 hx, toList_loW89 hx]
  exact filter_split89 (toList x) hc hd

/-- **`Ω₁` 以上の並びの後ろに下の並びを継いでも、対の列は変わらず尾はその並び。** -/
theorem wcnf_append89 : ∀ (H L : List Term), (∀ p ∈ H, lt p (reg 1) = false) →
    (∀ p ∈ L, lt p (reg 1) = true) →
    wcnf (reg 1) (H ++ L) = ((wcnf (reg 1) H).1, ofList L) := by
  intro H
  induction H with
  | nil =>
    intro L _ hL
    show wcnf (reg 1) L = ([], ofList L)
    exact wcnf_all_lt77 (reg 1) L hL
  | cons p H' ih =>
    intro L hH hL
    have hp : lt p (reg 1) = false := hH p (List.Mem.head _)
    have IH := ih L (fun q hq => hH q (List.Mem.tail _ hq)) hL
    show wcnf (reg 1) (p :: (H' ++ L)) = ((wcnf (reg 1) (p :: H')).1, ofList L)
    rw [wcnf_cons_ge hp, wcnf_cons_ge hp, IH]
    cases hr : wcnf (reg 1) H' with
    | mk fst snd =>
      cases fst with
      | nil => rfl
      | cons ac0 ps =>
        cases ac0 with
        | mk a' c' =>
          show (if (wA (reg 1) p == a') = true
              then ((wA (reg 1) p, plus (wC (reg 1) p) c') :: ps, ofList L)
              else ((wA (reg 1) p, wC (reg 1) p) :: (a', c') :: ps, ofList L))
            = ((if (wA (reg 1) p == a') = true
              then ((wA (reg 1) p, plus (wC (reg 1) p) c') :: ps, snd)
              else ((wA (reg 1) p, wC (reg 1) p) :: (a', c') :: ps, snd)).1, ofList L)
          by_cases heq : (wA (reg 1) p == a') = true
          · rw [if_pos heq, if_pos heq]
          · rw [if_neg heq, if_neg heq]

/-- `Ω₁` 以上の並びなら尾は `0`。 -/
theorem wcnf_snd_ge89 : ∀ (H : List Term), (∀ p ∈ H, lt p (reg 1) = false) →
    (wcnf (reg 1) H).2 = zero := by
  intro H
  induction H with
  | nil => intro _; rfl
  | cons p H' ih =>
    intro hH
    have hp : lt p (reg 1) = false := hH p (List.Mem.head _)
    have IH := ih (fun q hq => hH q (List.Mem.tail _ hq))
    rw [wcnf_cons_ge hp]
    cases hr : wcnf (reg 1) H' with
    | mk fst snd =>
      rw [hr] at IH
      cases fst with
      | nil => exact IH
      | cons ac0 ps =>
        cases ac0 with
        | mk a' c' =>
          show (if (wA (reg 1) p == a') = true
              then ((wA (reg 1) p, plus (wC (reg 1) p) c') :: ps, snd)
              else ((wA (reg 1) p, wC (reg 1) p) :: (a', c') :: ps, snd)).2 = zero
          by_cases heq : (wA (reg 1) p == a') = true
          · rw [if_pos heq]; exact IH
          · rw [if_neg heq]; exact IH

theorem hiW89_ge89 {x : Term} (hx : inT x = true) :
    ∀ p ∈ toList (hiW89 x), lt p (reg 1) = false := by
  intro p hp
  rw [toList_hiW89 hx] at hp
  have := (List.mem_filter.mp hp).2
  cases hc : lt p (reg 1) with
  | false => rfl
  | true => rw [hc] at this; exact Bool.noConfusion this

theorem loW89_lt89 {x : Term} (hx : inT x = true) :
    ∀ p ∈ toList (loW89 x), lt p (reg 1) = true := by
  intro p hp
  rw [toList_loW89 hx] at hp
  exact (List.mem_filter.mp hp).2

/-- **分解。** `wcnf` の対の列は `Ω₁` 以上の部分だけで決まり、尾は下の部分そのもの。 -/
theorem wcnf_split89 {x : Term} (hx : inT x = true) :
    wcnf (reg 1) (toList x) = ((wcnf (reg 1) (toList (hiW89 x))).1, loW89 x) := by
  rw [toList_split89 hx,
    wcnf_append89 _ _ (hiW89_ge89 hx) (loW89_lt89 hx),
    inT_ofList_toList _ (inT_loW89 hx)]

theorem accW89_hi89 {x : Term} (hx : inT x = true) : accW89 x = accW89 (hiW89 x) := by
  unfold accW89
  rw [wcnf_split89 hx]

theorem rhoW89_lo89 {x : Term} (hx : inT x = true) : rhoW89 x = loW89 x := by
  unfold rhoW89
  rw [wcnf_split89 hx]

theorem rhoW89_hi_zero89 {x : Term} (hx : inT x = true) : rhoW89 (hiW89 x) = zero :=
  wcnf_snd_ge89 _ (hiW89_ge89 hx)

/-! ### 累算器は ε 数 -/

end

/-! ### §89.2 畳み込みが吐くものはすべて ε 数

ヴェブレン枝の出力は `φ̄(a, ·)` で、指数 `a` は 0 でない (§81.3 の `wcnf_NZ81`)。
`phiNF` の 6 つの枝のどれを通っても結果は `ω^·` の不動点になる (`isFP_phiNF89`)。
強臨界枝の出力 `ψ_{Ω₁}(·)` は強臨界だからやはり不動点。だから累算器に外から
`ω^·` をかけても何も変わらない — これが §89.3 の閉じた形の理由である。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open Trans.Dict (sub1 subAP logOm divAP mulL)
open TM TM.Term
open Evidence.WF

theorem isFP_phi89 {a : Term} (hza : a ≠ zero) (d : Term) :
    TM.Term.isFP zero (phi a d) = true := by
  show ((_ && _) || lt zero a) = true
  rw [lt_zero_left hza]; exact Bool.or_true _

theorem isFP_phiNFdefault89 {a b : Term} (hza : a ≠ zero) :
    TM.Term.isFP zero (phiNFdefault a b) = true := by
  unfold phiNFdefault
  split
  · rename_i h
    show ((a.isSC && lt zero a) || _) = true
    rw [((Bool.and_eq_true _ _).mp h).2, lt_zero_left hza]; rfl
  · exact isFP_phi89 hza b

theorem isFP_phiNFsucc89 {a b : Term} (hza : a ≠ zero) :
    TM.Term.isFP zero (phiNFsucc a b) = true := by
  have hdef := isFP_phiNFdefault89 (a := a) (b := b) hza
  unfold phiNFsucc
  split
  split
  · split <;> (split <;> first | exact isFP_phi89 hza _ | exact hdef)
  · exact hdef

/-- **指数が `0` でないヴェブレン枝の出力は ε 数。** -/
theorem isFP_phiNF89 {a b : Term} (hza : a ≠ zero) :
    TM.Term.isFP zero (phiNF a b) = true := by
  unfold phiNF
  split
  · rename_i h
    have hsc := ((Bool.and_eq_true _ _).mp h).1
    have hb := ((Bool.and_eq_true _ _).mp h).2
    have hne : b ≠ zero := by
      intro hc; rw [hc, lt_zero_right] at hb; exact Bool.noConfusion hb
    show ((b.isSC && lt zero b) || _) = true
    rw [hsc, lt_zero_left hne]; rfl
  · cases b with
    | zero => exact isFP_phiNFsucc89 hza
    | M => exact isFP_phiNFsucc89 hza
    | add _ _ => exact isFP_phiNFsucc89 hza
    | omg _ => exact isFP_phiNFsucc89 hza
    | psi _ _ => exact isFP_phiNFsucc89 hza
    | Z _ => exact isFP_phiNFsucc89 hza
    | phi c d =>
        show TM.Term.isFP zero (if lt a c = true then phi c d else phiNFsucc a (phi c d)) = true
        by_cases hlt : lt a c = true
        · rw [if_pos hlt]
          refine isFP_phi89 ?_ d
          intro hc; rw [hc, lt_zero_right] at hlt; exact Bool.noConfusion hlt
        · rw [if_neg hlt]; exact isFP_phiNFsucc89 hza

/-- 畳み込みの不変量、ε 数の側。 -/
def StF89 (s : Option Term × Option Term) : Prop :=
  ∀ v, s.2 = some v → TM.Term.isFP zero v = true

theorem stepF89 {s : Option Term × Option Term} {ac : Term × Term}
    (hz : ac.1 ≠ zero) : StF89 (stepF (reg 1) (baseOf 0) s ac) := by
  unfold stepF
  split
  · intro v hq
    rw [← Option.some.inj (show some (psi (reg 1) (idxOf (reg 1) s ac)) = some v from hq)]
    exact isFP_zero_of_sc79 rfl (lt_zero_left (by intro hc; exact Term.noConfusion hc))
  · intro v hq
    rw [← Option.some.inj (show some (phiNF ac.1
      (plus (match s.2 with | none => baseOf 0 | some v => v)
            (match s.2 with | none => sub1 ac.2 | some _ => ac.2))) = some v from hq)]
    exact isFP_phiNF89 hz

theorem foldF89 : ∀ (l : List (Term × Term)) (s : Option Term × Option Term), StF89 s →
    (∀ ac ∈ l, ac.1 ≠ zero) → StF89 (l.foldl (stepF (reg 1) (baseOf 0)) s)
  | [], _, hs, _ => hs
  | ac :: t, s, _, hz =>
      foldF89 t (stepF (reg 1) (baseOf 0) s ac) (stepF89 (hz ac (List.Mem.head _)))
        (fun a ha => hz a (List.Mem.tail _ ha))

/-- **累算器の性質、ひとまとめ。** `Ω₁ ≤ x` なら畳み込みは必ず 1 歩は回る。 -/
theorem accW89_facts (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (Hp : PsiIdxOK 0 x) (hW : le (reg 1) x = true) :
    inT (accW89 x) = true ∧ lt (accW89 x) (reg 1) = true ∧ (accW89 x).isAP = true
      ∧ le E081 (accW89 x) = true ∧ TM.Term.isFP zero (accW89 x) = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨⟨h21, h22⟩, hallOK⟩ :=
    wcnf_spec_sc (inT_reg 1) (show (reg 1).isSC = true from rfl) (toList x) hc hd
      (ltM_toList x hx hlx)
  have hWp := wcnf_W79 (toList x) hc
  have hNZ := wcnf_NZ81 (toList x) hc
  have hinit : StE81 ((none : Option Term), (none : Option Term)) := by intro v h; cases h
  have hst := foldE81 (wcnf (reg 1) (toList x)).1 (none, none) hinit hallOK
    (fun ac hac => (hWp.2 ac hac).2) hNZ Hp
  have hinitF : StF89 ((none : Option Term), (none : Option Term)) := by intro v h; cases h
  have hstF := foldF89 (wcnf (reg 1) (toList x)).1 (none, none) hinitF hNZ
  have hsome := fold_some81 (wcnf (reg 1) (toList x)).1 (none, none)
    (wcnf_fst_ne_nil81 hx hW)
  cases hg : ((wcnf (reg 1) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2 with
  | none => exact absurd hg hsome
  | some v =>
      have hv := hst v hg
      have hvF := hstF v hg
      show inT (accW89 x) = true ∧ lt (accW89 x) (reg 1) = true ∧ (accW89 x).isAP = true
        ∧ le E081 (accW89 x) = true ∧ TM.Term.isFP zero (accW89 x) = true
      unfold accW89
      rw [hg]
      exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, hvF⟩

theorem ltM_accW89 {x : Term} (hi : inT (accW89 x) = true)
    (hlw : lt (accW89 x) (reg 1) = true) : lt M (accW89 x) = false :=
  lt_asymm_inT hi inT_M (lt_trans_inT hi inT_W79 inT_M hlw ltM_W79)

end

/-! ### §89.3 閉じた形 — `ψ₀(x) = ω^(ψ₀(hi x) ⊕ lo x)`

`hi x` の分解は `x` の分解と同じ対の列を持ち、尾は `0`。だから
`ψ₀(hi x) = ω^(累算器) = 累算器` (§89.2)。あとは §89.1 の分解をそのまま書けば
`ψ₀(x) = ω^(ψ₀(hi x) ⊕ lo x)` になる。**折り畳みはこれ以上ほどかない。** -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open Trans.Dict (sub1 subAP logOm divAP mulL)
open TM TM.Term
open Evidence.WF

/-- **§89 の閉じた形 (1)。** `Ω₁` 以上の部分に `ψ₀` を当てたものが累算器そのもの。 -/
theorem collapse0_hi89 (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (Hp : PsiIdxOK 0 x) (hW : le (reg 1) x = true) :
    collapse 0 (hiW89 x) = accW89 x := by
  obtain ⟨hi, hlw, hap, hle, hfp⟩ := accW89_facts x hx hlx Hp hW
  rw [collapse0_raw89, ← accW89_hi89 hx, rhoW89_hi_zero89 hx,
    show plus (accW89 x) zero = accW89 x from plus_nil rfl,
    show plus (reg 0) (accW89 x) = plus zero (accW89 x) from rfl,
    plus_zero_left_inT hi, omegaNF_eq_gen,
    if_neg (by rw [ltM_accW89 hi hlw]; exact Bool.noConfusion), if_pos hfp]

/-- **§89 の閉じた形 (2)。** `ψ₀(x) = ω^(ψ₀(hi x) ⊕ lo x)`。 -/
theorem collapse0_split89 (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (Hp : PsiIdxOK 0 x) (hW : le (reg 1) x = true) :
    collapse 0 x = omegaNF (plus (collapse 0 (hiW89 x)) (loW89 x)) := by
  obtain ⟨hi, hlw, hap, hle, hfp⟩ := accW89_facts x hx hlx Hp hW
  rw [collapse0_acc89 (inT_plus hi (by rw [rhoW89_lo89 hx]; exact inT_loW89 hx)),
    rhoW89_lo89 hx, collapse0_hi89 x hx hlx Hp hW]

/-! ### 順序 — 頭が同じなら尾が決める -/

end

/-! ### §89.4 `Ω₁` での切り分けは順序を保つ

`hi` が同じなら `lo` が決め (`lo_lt_of_lt89`)、`hi` が違えば `hi` が決める
(`lt_hi89`)。後者は成分列の辞書式の帰納で、最初に食い違うところで `hi` が決まり、
片方の `hi` が尽きるところでは相手の成分が `Ω₁` 以上・こちらの残りが `Ω₁` より下
だから、やはり `hi` の側が決める。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open Trans.Dict (sub1 subAP logOm divAP mulL)
open TM TM.Term
open Evidence.WF

theorem inTL_append89 {L1 L2 : List Term} (h1 : inTL L1 = true) (h2 : inTL L2 = true) :
    inTL (L1 ++ L2) = true := by
  show (L1 ++ L2).all _ = true
  rw [List.all_eq_true]
  intro z hz
  rcases List.mem_append.mp hz with h | h
  · exact List.all_eq_true.mp h1 z h
  · exact List.all_eq_true.mp h2 z h

theorem toList_ofList89 {l : List Term} (h : inTL l = true) : toList (ofList l) = l :=
  toList_ofList l (fun z hz => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h z hz)).1)

/-- **共通の前置きを付けても順序は変わらない** (継ぐ側)。 -/
theorem lt_append_eq89 : ∀ (H : List Term), inTL H = true → ∀ (X Y : Term),
    inT X = true → inT Y = true →
    descL (H ++ toList X) = true → descL (H ++ toList Y) = true →
    lt X Y = true → lt (ofList (H ++ toList X)) (ofList (H ++ toList Y)) = true := by
  intro H
  induction H with
  | nil =>
    intro _ X Y hX hY _ _ h
    rw [List.nil_append, List.nil_append, inT_ofList_toList X hX, inT_ofList_toList Y hY]
    exact h
  | cons c H' ih =>
    intro hc X Y hX hY hdx hdy h
    obtain ⟨⟨hapc, hic⟩, hcH⟩ := inTL_cons.mp hc
    have hdx' := descL_tail hdx
    have hdy' := descL_tail hdy
    have hIH := ih hcH X Y hX hY hdx' hdy' h
    have hcX : inTL (c :: (H' ++ toList X)) = true := inTL_append89 hc (inT_toList X hX).1
    have hcY : inTL (c :: (H' ++ toList Y)) = true := inTL_append89 hc (inT_toList Y hY).1
    exact lt_of_hd_eq77 (inT_ofList _ hcX hdx) (inT_ofList _ hcY hdy)
      (toList_ofList89 hcX) (toList_ofList89 hcY) hIH

/-- 分解して戻す。 -/
theorem eq_of_split89 {x y : Term} (hx : inT x = true) (hy : inT y = true)
    (h1 : hiW89 x = hiW89 y) (h2 : loW89 x = loW89 y) : x = y := by
  have e1 := toList_split89 hx
  have e2 := toList_split89 hy
  rw [h1, h2] at e1
  rw [← inT_ofList_toList x hx, ← inT_ofList_toList y hy, e1, e2]

/-- **頭部が同じなら尾が決める** — `lo` から `x` へ。 -/
theorem lt_of_lo_lt89 {x y : Term} (hx : inT x = true) (hy : inT y = true)
    (heq : hiW89 x = hiW89 y) (h : lt (loW89 x) (loW89 y) = true) : lt x y = true := by
  obtain ⟨hcx, hdx⟩ := inT_toList x hx
  obtain ⟨hcy, hdy⟩ := inT_toList y hy
  have hH : toList (hiW89 y) = toList (hiW89 x) := by rw [heq]
  have e1 : toList x = toList (hiW89 x) ++ toList (loW89 x) := toList_split89 hx
  have e2 : toList y = toList (hiW89 x) ++ toList (loW89 y) := by
    rw [toList_split89 hy, hH]
  have h1 := lt_append_eq89 (toList (hiW89 x)) (inT_toList _ (inT_hiW89 hx)).1
    (loW89 x) (loW89 y) (inT_loW89 hx) (inT_loW89 hy)
    (by rw [← e1]; exact hdx) (by rw [← e2]; exact hdy) h
  rw [← e1, ← e2, inT_ofList_toList x hx, inT_ofList_toList y hy] at h1
  exact h1

/-- **その逆。** 三分律で戻す。 -/
theorem lo_lt_of_lt89 {x y : Term} (hx : inT x = true) (hy : inT y = true)
    (heq : hiW89 x = hiW89 y) (h : lt x y = true) : lt (loW89 x) (loW89 y) = true := by
  by_cases hle : le (loW89 x) (loW89 y) = true
  · rcases (Bool.or_eq_true _ _).mp hle with he | hl
    · exfalso
      have hxy : x = y := eq_of_split89 hx hy heq (eq_of_beq he)
      rw [hxy, lt_irrefl] at h
      exact Bool.noConfusion h
    · exact hl
  · exfalso
    have h2 : lt (loW89 y) (loW89 x) = true :=
      lt_of_not_le_inT (inT_loW89 hx) (inT_loW89 hy) (bool_false hle)
    have h3 : lt y x = true := lt_of_lo_lt89 hy hx heq.symm h2
    rw [lt_asymm_inT hx hy h] at h3
    exact Bool.noConfusion h3

/-- **加法主要な頭が決める。** 尾の成分が頭以下なら、頭の比較がそのまま和の比較。 -/
theorem lt_plus_ap89 {V W r s : Term} (hiV : inT V = true) (hiW : inT W = true)
    (hir : inT r = true) (his : inT s = true)
    (hapV : V.isAP = true) (hapW : W.isAP = true)
    (hhd : ∀ p ∈ toList r, le p V = true)
    (hVW : lt V W = true) : lt (plus V r) (plus W s) = true := by
  have h1 : lt (plus V r) W = true := by
    cases hr : toList r with
    | nil => rw [plus_nil hr]; exact hVW
    | cons r1 R' =>
      rw [plus_cons hiV hir (toList_isAP81 hapV) rfl hr,
        if_pos (hhd r1 (by rw [hr]; exact List.Mem.head _)),
        show ofList ([] : List Term) = zero from rfl, plus_zero_left_inT hir,
        lt_add_nsum (ne_zero_of_isAP hapW) (nsum_of_isAP hapW)]
      exact hVW
  exact lt_of_lt_of_le3 (inT_le_fragR _ (inT_plus hiV hir)) (inT_le_fragR W hiW)
    (inT_le_fragR _ (inT_plus hiW his)) h1 (le_self_plus_ap81 hiW hapW his)

/-! ### `Ω₁` 以上の部分は単調 -/

theorem le_reg1_of_not_lt89 {c : Term} (hic : inT c = true) (h : lt c (reg 1) = false) :
    le (reg 1) c = true := by
  by_cases hq : ((reg 1 : Term) == c) = true
  · show ((reg 1 == c) || lt (reg 1) c) = true
    rw [hq]; rfl
  · have hle : le c (reg 1) = false := by
      show ((c == reg 1) || lt c (reg 1)) = false
      rw [h, show (c == (reg 1 : Term)) = false from by
        cases hb : (c == (reg 1 : Term)) with
        | false => rfl
        | true => exact absurd (show ((reg 1 : Term) == c) = true from by
            rw [eq_of_beq hb]; exact beq_self_eq_true _) hq]
      rfl
    exact le_of_lt (lt_of_not_le_inT hic inT_W79 hle)

/-- **`lt_of_hd_eq77` の逆。** 三分律で戻す。 -/
theorem lt_hd_eq_inv89 {e y c : Term} {E' Y' : List Term} (he : inT e = true)
    (hy : inT y = true) (hE : toList e = c :: E') (hY : toList y = c :: Y')
    (hiE : inT (ofList E') = true) (hiY : inT (ofList Y') = true)
    (hE2 : toList (ofList E') = E') (hY2 : toList (ofList Y') = Y')
    (h : lt e y = true) : lt (ofList E') (ofList Y') = true := by
  by_cases hle : le (ofList E') (ofList Y') = true
  · rcases (Bool.or_eq_true _ _).mp hle with hq | hl
    · exfalso
      have hEY : E' = Y' := by rw [← hE2, ← hY2, eq_of_beq hq]
      have hxy : e = y := by
        rw [← inT_ofList_toList e he, ← inT_ofList_toList y hy, hE, hY, hEY]
      rw [hxy, lt_irrefl] at h
      exact Bool.noConfusion h
    · exact hl
  · exfalso
    have h2 : lt (ofList Y') (ofList E') = true :=
      lt_of_not_le_inT hiE hiY (bool_false hle)
    have h3 : lt y e = true := lt_of_hd_eq77 hy he hY hE h2
    rw [lt_asymm_inT he hy h] at h3
    exact Bool.noConfusion h3

/-- **`Ω₁` 以上の並びの比較は、下の尾を継いでも変わらない。** -/
theorem lt_append_hi89 : ∀ (Hy Hx : List Term), inTL Hy = true → inTL Hx = true →
    descL Hy = true → descL Hx = true →
    ∀ (Ly Lx : List Term), inTL Ly = true → inTL Lx = true →
    descL (Hy ++ Ly) = true → descL (Hx ++ Lx) = true →
    (∀ p ∈ Hx, lt p (reg 1) = false) → (∀ p ∈ Ly, lt p (reg 1) = true) →
    lt (ofList Hy) (ofList Hx) = true →
    lt (ofList (Hy ++ Ly)) (ofList (Hx ++ Lx)) = true := by
  intro Hy
  induction Hy with
  | nil =>
    intro Hx _ hcx _ hdx Ly Lx hcLy hcLx hdyL hdxL hHx hLy hlt
    cases Hx with
    | nil =>
      exfalso
      rw [show ofList ([] : List Term) = zero from rfl, lt_irrefl] at hlt
      exact Bool.noConfusion hlt
    | cons cx Hx' =>
      have hcxL : inTL (cx :: (Hx' ++ Lx)) = true := inTL_append89 hcx hcLx
      have hiT : inT (ofList (cx :: (Hx' ++ Lx))) = true := inT_ofList _ hcxL hdxL
      have hicx : inT cx = true := (inTL_cons.mp hcx).1.2
      have hgx : lt cx (reg 1) = false := hHx cx (List.Mem.head _)
      cases Ly with
      | nil =>
        show lt (ofList ([] : List Term)) (ofList (cx :: (Hx' ++ Lx))) = true
        exact lt_zero_left (ofList_ne_zero81 _ (List.cons_ne_nil _ _) (fun z hz =>
          ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcxL z hz)).1))
      | cons l1 Ly' =>
        have hcyL : inTL (l1 :: Ly') = true := hcLy
        have hiS : inT (ofList (l1 :: Ly')) = true := inT_ofList _ hcyL hdyL
        have hil1 : inT l1 = true := (inTL_cons.mp hcLy).1.2
        refine lt_of_hd_lt hiS hiT (toList_ofList89 hcyL) (toList_ofList89 hcxL) ?_
        exact lt_of_lt_of_le3 (inT_le_fragR l1 hil1) (inT_le_fragR _ inT_W79)
          (inT_le_fragR cx hicx) (hLy l1 (List.Mem.head _)) (le_reg1_of_not_lt89 hicx hgx)
  | cons cy Hy' ih =>
    intro Hx hcy hcx hdy hdx Ly Lx hcLy hcLx hdyL hdxL hHx hLy hlt
    cases Hx with
    | nil =>
      exfalso
      rw [show ofList ([] : List Term) = zero from rfl, lt_zero_right] at hlt
      exact Bool.noConfusion hlt
    | cons cx Hx' =>
      obtain ⟨⟨hapy, hicy⟩, hcy'⟩ := inTL_cons.mp hcy
      obtain ⟨⟨hapx, hicx⟩, hcx'⟩ := inTL_cons.mp hcx
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
          (fun p hp => hHx p (List.Mem.tail _ hp)) hLy hrec
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

/-- **§89 の第三の定理。** `Ω₁` での切り分けは順序を保つ。 -/
theorem lt_hi89 {x y : Term} (hx : inT x = true) (hy : inT y = true)
    (h : lt x y = true) (hne : hiW89 x ≠ hiW89 y) : lt (hiW89 x) (hiW89 y) = true := by
  by_cases hlt : lt (hiW89 x) (hiW89 y) = true
  · exact hlt
  · exfalso
    have hle : le (hiW89 x) (hiW89 y) = false := by
      show ((hiW89 x == hiW89 y) || lt (hiW89 x) (hiW89 y)) = false
      rw [bool_false hlt, show (hiW89 x == hiW89 y) = false from by
        cases hb : (hiW89 x == hiW89 y) with
        | false => rfl
        | true => exact absurd (eq_of_beq hb) hne]
      rfl
    have h2 : lt (hiW89 y) (hiW89 x) = true :=
      lt_of_not_le_inT (inT_hiW89 hx) (inT_hiW89 hy) hle
    have hey := toList_split89 hy
    have hex := toList_split89 hx
    have h2' : lt (ofList (toList (hiW89 y))) (ofList (toList (hiW89 x))) = true := by
      rw [inT_ofList_toList _ (inT_hiW89 hy), inT_ofList_toList _ (inT_hiW89 hx)]; exact h2
    have h3 := lt_append_hi89 (toList (hiW89 y)) (toList (hiW89 x))
      (inT_toList _ (inT_hiW89 hy)).1 (inT_toList _ (inT_hiW89 hx)).1
      (inT_toList _ (inT_hiW89 hy)).2 (inT_toList _ (inT_hiW89 hx)).2
      (toList (loW89 y)) (toList (loW89 x))
      (inT_toList _ (inT_loW89 hy)).1 (inT_toList _ (inT_loW89 hx)).1
      (by rw [← hey]; exact (inT_toList y hy).2)
      (by rw [← hex]; exact (inT_toList x hx).2)
      (hiW89_ge89 hx) (loW89_lt89 hy) h2'
    rw [← hey, ← hex, inT_ofList_toList x hx, inT_ofList_toList y hy] at h3
    rw [lt_asymm_inT hx hy h] at h3
    exact Bool.noConfusion h3

/-! ### 組み立て -/

end

/-! ### §89.5 場合 A は定理、場合 B の道具

`hi` が同じなら累算器も同じで、残るのは尾どうしの比較 — §79.3 の `plus e ·` の
狭義単調性そのもの。`hi` が違うときに要るのは、小さい側の尾がその累算器で
押さえられていること (`lt_plus_ap89`)。それは尾が ε₀ より下なら只である
(`loDom_of_ltE89`、§81.3 の下界)。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open Trans.Dict (sub1 subAP logOm divAP mulL)
open TM TM.Term
open Evidence.WF

/-- **場合 A — `Ω₁` 以上の部分が同じなら定理。** 折り畳みは両辺で同じものを吐き、
    残るのは尾どうしの比較で、それは §79.3 の狭義単調性そのもの。 -/
theorem lt_collapse0_sameHi89 {x y : Term} (hx : inT x = true) (hlx : lt x M = true)
    (Hpx : PsiIdxOK 0 x) (hWx : le (reg 1) x = true)
    (hy : inT y = true) (hly : lt y M = true) (Hpy : PsiIdxOK 0 y)
    (hWy : le (reg 1) y = true)
    (heq : hiW89 x = hiW89 y) (h : lt x y = true) :
    lt (collapse 0 x) (collapse 0 y) = true := by
  have hlo := lo_lt_of_lt89 hx hy heq h
  obtain ⟨hiB, _, _, _, _⟩ := accW89_facts y hy hly Hpy hWy
  rw [collapse0_split89 x hx hlx Hpx hWx, collapse0_split89 y hy hly Hpy hWy, heq,
    collapse0_hi89 y hy hly Hpy hWy]
  exact lt_omegaNF_inT79 (inT_plus hiB (inT_loW89 hx)) (inT_plus hiB (inT_loW89 hy))
    (plus_smono_right_inT79 (accW89 y) hiB (loW89 x) (loW89 y)
      (inT_loW89 hx) (inT_loW89 hy) hlo)

/-- **場合 B — `Ω₁` 以上の部分が違うとき。** 折り畳みの比較と、小さい側の尾が
    その累算器で押さえられていること、この 2 つで出る。 -/
theorem lt_collapse0_diffHi89 {x y : Term} (hx : inT x = true) (hlx : lt x M = true)
    (Hpx : PsiIdxOK 0 x) (hWx : le (reg 1) x = true)
    (hy : inT y = true) (hly : lt y M = true) (Hpy : PsiIdxOK 0 y)
    (hWy : le (reg 1) y = true)
    (hhd : ∀ p ∈ toList (loW89 x), le p (collapse 0 (hiW89 x)) = true)
    (hHi : lt (collapse 0 (hiW89 x)) (collapse 0 (hiW89 y)) = true) :
    lt (collapse 0 x) (collapse 0 y) = true := by
  obtain ⟨hiA, _, hapA, _, _⟩ := accW89_facts x hx hlx Hpx hWx
  obtain ⟨hiB, _, hapB, _, _⟩ := accW89_facts y hy hly Hpy hWy
  have hVx := collapse0_hi89 x hx hlx Hpx hWx
  have hVy := collapse0_hi89 y hy hly Hpy hWy
  rw [hVx] at hhd hHi
  rw [hVy] at hHi
  rw [collapse0_split89 x hx hlx Hpx hWx, collapse0_split89 y hy hly Hpy hWy, hVx, hVy]
  exact lt_omegaNF_inT79 (inT_plus hiA (inT_loW89 hx)) (inT_plus hiB (inT_loW89 hy))
    (lt_plus_ap89 hiA hiB (inT_loW89 hx) (inT_loW89 hy) hapA hapB hhd hHi)

/-- **尾の側条件は ε₀ より下なら只。** §81.3 の下界がそのまま効く。 -/
theorem loDom_of_ltE89 {x : Term} (hx : inT x = true) (hlx : lt x M = true)
    (Hpx : PsiIdxOK 0 x) (hWx : le (reg 1) x = true)
    (hlo : ∀ p ∈ toList (loW89 x), lt p E081 = true) :
    ∀ p ∈ toList (loW89 x), le p (collapse 0 (hiW89 x)) = true := by
  obtain ⟨hiA, _, _, hleA, _⟩ := accW89_facts x hx hlx Hpx hWx
  intro p hp
  have hip : inT p = true := inTL_inT (inT_loW89 hx) p hp
  rw [collapse0_hi89 x hx hlx Hpx hWx]
  exact le_of_lt (lt_of_lt_of_le3 (inT_le_fragR p hip) (inT_le_fragR _ inT_E81)
    (inT_le_fragR _ hiA) (hlo p hp) hleA)

end

/-! ### §89.6 組み立て — 残る条項は 2 つ

`HiMono89` は §81 の残余を**尾のない引数に絞ったもの** (`hiW89_self89` がそう言う)。
`LoDom89` は対ではなく**項ひとつ**についての条項で、主要項では只
(`loDom_of_sum89`)、尾が ε₀ より下でも只 (`loDom_of_ltE89`)。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open Trans.Dict (sub1 subAP logOm divAP mulL)
open TM TM.Term
open Evidence.WF

/-- **尾がなければ `hiW89` は恒等。** そこでは `HiMono89` は §81 の残余の文そのもの。 -/
theorem hiW89_self89 {x : Term} (hx : inT x = true) (h : loW89 x = zero) : hiW89 x = x := by
  have e1 := toList_split89 hx
  rw [h, show toList zero = ([] : List Term) from rfl, List.append_nil] at e1
  have h2 : ofList (toList (hiW89 x)) = ofList (toList x) := by rw [e1]
  rw [inT_ofList_toList _ (inT_hiW89 hx), inT_ofList_toList x hx] at h2
  exact h2

/-- **残余 (1) — 尾のない引数についての §81 の残余そのもの。** -/
def HiMono89 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true

/-- **残余 (2) — 尾は累算器で押さえられる。** 対ではなく**項ひとつ**についての主張。 -/
def LoDom89 : Prop :=
  ∀ (a : BT), btLe72 1 (BT.D 0 a) = true → BT.isStd (BT.D 0 a) = true →
    le (reg 1) (dict a) = true →
    ∀ p ∈ toList (loW89 (dict a)), le p (collapse 0 (hiW89 (dict a))) = true

/-- 主要項には尾がない。 -/
theorem isAP_dict_D89 (u : Nat) (c : BT) : (dict (BT.D u c)).isAP = true := by
  rw [Trans.Dict.dict_D, collapse_eq]; exact isAP_omegaNF _

theorem not_lt_of_le_reg1_89 {x : Term} (hx : inT x = true) (hW : le (reg 1) x = true) :
    lt x (reg 1) = false := by
  cases hc : lt x (reg 1) with
  | false => rfl
  | true =>
    exfalso
    rcases (Bool.or_eq_true _ _).mp hW with hq | hl
    · rw [← eq_of_beq hq, lt_irrefl] at hc; exact Bool.noConfusion hc
    · rw [lt_asymm_inT hx inT_W79 hc] at hl; exact Bool.noConfusion hl

theorem loW89_zero_of_isAP89 {x : Term} (hx : inT x = true) (hap : x.isAP = true)
    (hW : le (reg 1) x = true) : loW89 x = zero := by
  unfold loW89
  rw [toList_isAP81 hap,
    List.filter_cons_of_neg (by rw [not_lt_of_le_reg1_89 hx hW]; exact Bool.noConfusion)]
  rfl

/-- **残余 (2') — 和の形の項だけに絞った尾の条件。** -/
def LoDomSum89 : Prop :=
  ∀ (a : BT), BT.isP a = false → btLe72 1 (BT.D 0 a) = true → BT.isStd (BT.D 0 a) = true →
    le (reg 1) (dict a) = true →
    ∀ p ∈ toList (loW89 (dict a)), le p (collapse 0 (hiW89 (dict a))) = true

/-- **尾の条件は主要項では只。** 残るのは和の形だけ。 -/
theorem loDom_of_sum89 (Hp : PsiIdxOKStd172) (L : LoDomSum89) : LoDom89 := by
  intro a hbA hsA hWa
  cases a with
  | zero => exact L BT.zero rfl hbA hsA hWa
  | sum c d => exact L (BT.sum c d) rfl hbA hsA hWa
  | D u c =>
      have hba := (btLe72_D 1 0 (BT.D u c) hbA).2
      have hsa := isStd_of_D hsA
      have hia := inT_dict_of_std172 Hp (BT.D u c) hba hsa
      rw [loW89_zero_of_isAP89 hia.1 (isAP_dict_D89 u c) hWa,
        show toList zero = ([] : List Term) from rfl]
      intro p hp; cases hp

/-- **§89 の主定理。** §81 の残余は 2 つに割れる。 -/
theorem collapseMono0Hi_of_89 (Hp : PsiIdxOKStd172) (H : HiMono89) (L : LoDom89) :
    CollapseMono0Hi81 := by
  intro a b hbA hbB hsA hsB hWa hWb h
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
  · exact lt_collapse0_diffHi89 hia.1 hia.2 hpa hWa hib.1 hib.2 hpb hWb
      (L a hbA hsA hWa) (H a b hbA hbB hsA hsB hWa hWb (lt_hi89 hia.1 hib.1 h heq))

/-- 和の形だけの尾の条件からも同じ結論。 -/
theorem collapseMono0Hi_of_sum89 (Hp : PsiIdxOKStd172) (H : HiMono89) (L : LoDomSum89) :
    CollapseMono0Hi81 :=
  collapseMono0Hi_of_89 Hp H (loDom_of_sum89 Hp L)

/-- 326 行目までの繋ぎ。 -/
theorem dictLtA74_89 (Hp : PsiIdxOKStd172) (H : HiMono89) (L : LoDom89) : DictLtA74 :=
  dictLtA74_81 Hp (collapseMono0Hi_of_89 Hp H L)

theorem vOfLtA71_89 (Hp : PsiIdxOKStd172) (H : HiMono89) (L : LoDom89) : VOfLtA71 :=
  vOfLtA71_81 Hp (collapseMono0Hi_of_89 Hp H L)

theorem limDecS1_89 (Hp : PsiIdxOKStd172) (H : HiMono89) (L : LoDom89) : LimDecS1 :=
  limDecS1_81 Hp (collapseMono0Hi_of_89 Hp H L)

theorem limIncS1_89 (Hp : PsiIdxOKStd172) (H : HiMono89) (L : LoDom89) : LimIncS1 :=
  limIncS1_81 Hp (collapseMono0Hi_of_89 Hp H L)

theorem certIn_t326_89 (Hp : PsiIdxOKStd172) (H : HiMono89) (L : LoDom89)
    (HCD : CofDenseS1) (HBC : BCofIn71)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_81 Hp (collapseMono0Hi_of_89 Hp H L) HCD HBC hacc

end


/-! ### §89.7 否定 — 2 つの条項はどちらも `K` の条件を消費する

`HiMono89` から `BT.isStd (ψ₀ ·)` を `BT.isStd ·` に緩めると §81 の `cexA81`/`cexB81` が
そのまま反例になる。そして**その 2 つはどちらも尾がない**から、反例は `HiMono89` 自身の
形の中にある。`LoDom89` の方も同じで、しかもこちらは `BT.isStd ·` だけを満たす項が
落とす — 標準の母集団 105 項はその項を含まないので、母集団は嘘をつく側にいる。
最後に、尾の条項を「`lo x ≤ ψ₀(hi x)`」と書くと**領域の中で偽**であることも押さえる。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- §81 の `cexA81` — `ψ₁ψ₀ψ₁ψ₁0`。 -/
def cexA89 : BT := BT.D 1 (BT.D 0 (BT.D 1 (BT.D 1 BT.zero)))
/-- §81 の `cexB81` — `ψ₁ψ₁0`。 -/
def cexB89 : BT := BT.D 1 (BT.D 1 BT.zero)

/-- **どちらも尾がない。** だから反例は `HiMono89` 自身の形の中にある。 -/
theorem cex89_facts :
    btLe72 1 cexA89 = true ∧ btLe72 1 cexB89 = true ∧
    BT.isStd cexA89 = true ∧ BT.isStd cexB89 = true ∧
    le (reg 1) (dict cexA89) = true ∧ le (reg 1) (dict cexB89) = true ∧
    loW89 (dict cexA89) = zero ∧ loW89 (dict cexB89) = zero ∧
    lt (hiW89 (dict cexA89)) (hiW89 (dict cexB89)) = true ∧
    lt (collapse 0 (hiW89 (dict cexA89))) (collapse 0 (hiW89 (dict cexB89))) = false ∧
    BT.isStd (BT.D 0 cexA89) = false :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide, by decide, by decide⟩

/-- `HiMono89` の `K` の条件を `BT.isStd` に緩めた形。 -/
def HiMonoNoK89 : Prop :=
  ∀ (a b : BT), btLe72 1 a = true → btLe72 1 b = true →
    BT.isStd a = true → BT.isStd b = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true

/-- **§89.7 の第一の定理。** `HiMono89` は `K` の条件を消費しなければ偽。 -/
theorem not_hiMonoNoK89 : ¬ HiMonoNoK89 := by
  intro H
  have h := H cexA89 cexB89 cex89_facts.1 cex89_facts.2.1 cex89_facts.2.2.1
    cex89_facts.2.2.2.1 cex89_facts.2.2.2.2.1 cex89_facts.2.2.2.2.2.1
    cex89_facts.2.2.2.2.2.2.2.2.1
  rw [cex89_facts.2.2.2.2.2.2.2.2.2.1] at h
  exact Bool.noConfusion h

/-- 尾の条項の反例 — `Ω₁ ⊕ ψ₀(Ω₁ ⊕ Ω₁)`。`BT.isStd` は満たすが `K` の条件は満たさない。 -/
def loBad89 : BT :=
  BT.sum (BT.D 1 BT.zero) (BT.D 0 (BT.sum (BT.D 1 BT.zero) (BT.D 1 BT.zero)))

/-- `lo (dict loBad89) = ε₁`、`ψ₀(hi (dict loBad89)) = ε₀`。 -/
theorem loBad89_facts :
    btLe72 1 loBad89 = true ∧ BT.isStd loBad89 = true ∧
    BT.isStd (BT.D 0 loBad89) = false ∧ le (reg 1) (dict loBad89) = true ∧
    collapse 0 (hiW89 (dict loBad89)) = E081 ∧
    loW89 (dict loBad89) = phi TM.Term.one TM.Term.one ∧
    (phi TM.Term.one TM.Term.one) ∈ toList (loW89 (dict loBad89)) ∧
    le (phi TM.Term.one TM.Term.one) (collapse 0 (hiW89 (dict loBad89))) = false :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide⟩

/-- `LoDom89` の `K` の条件を `BT.isStd` に緩めた形。 -/
def LoDomNoK89 : Prop :=
  ∀ (a : BT), btLe72 1 a = true → BT.isStd a = true → le (reg 1) (dict a) = true →
    ∀ p ∈ toList (loW89 (dict a)), le p (collapse 0 (hiW89 (dict a))) = true

/-- **§89.7 の第二の定理。** 尾の条項も `K` の条件を消費しなければ偽。
    落とすのは `BT.isStd (ψ₀ ·)` ただ 1 つで、標準の母集団はこの項を含まない。 -/
theorem not_loDomNoK89 : ¬ LoDomNoK89 := by
  intro H
  have h := H loBad89 loBad89_facts.1 loBad89_facts.2.1 loBad89_facts.2.2.2.1
    (phi TM.Term.one TM.Term.one) loBad89_facts.2.2.2.2.2.2.1
  rw [loBad89_facts.2.2.2.2.2.2.2] at h
  exact Bool.noConfusion h

/-- 尾の条項を和のまま書くと**領域の中で**偽 — `Ω₁ ⊕ ψ₀Ω₁ ⊕ ψ₀Ω₁`。 -/
def loSum89 : BT :=
  BT.sum (BT.D 1 BT.zero) (BT.sum (BT.D 0 (BT.D 1 BT.zero)) (BT.D 0 (BT.D 1 BT.zero)))

/-- **§89.7 の第三の定理。** `K` の条件つきでも `lo x ≤ ψ₀(hi x)` は偽。
    成分ごとに読むのが正しく、§89.6 が使うのはそちらである。 -/
theorem not_le_lo_hi89 :
    btLe72 1 loSum89 = true ∧ BT.isStd (BT.D 0 loSum89) = true ∧
    le (reg 1) (dict loSum89) = true ∧
    ((toList (loW89 (dict loSum89))).all
      (fun p => le p (collapse 0 (hiW89 (dict loSum89))))) = true ∧
    le (loW89 (dict loSum89)) (collapse 0 (hiW89 (dict loSum89))) = false :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

end

/-! ### §89.8 測定 (凍結)

**構成を先に書く。**  §81.8 の構成をそのまま使い、**深さの線だけ開ける**。種 `bs89` は
§81 と同じ段 1 以下の 6 項 (`0`・`1`・`ω`・`Ω₁`・`ψ₁ψ₁0`・`ψ₀ψ₁0`)。**深さの線**
`deep89` は `ψ₀`・`ψ₁` を 1 段ずつかぶせて 2 つに 1 つ間引く操作を §81 の 7 回ではなく
**11 回**繰り返した層の合併 (入れ子は 13 段まで、`K` 標準の部分で 12 段)。**幅の線**
`wide89` は成分が降順の 2 項和・3 項和。**領域の外** `out89` は添字 2・3 を 1 段/2 段
かぶせたもの。合わせて 229 項。§87 が「3 段で綺麗に見えた条項が 4 段で落ちる」と
言ったので、`ψ₀` の下に `ψ₁` を 4 段以上重ねる形が層 4 以降にぜんぶ入る。

    popAll89   229 項
    popGood89   89 項  段 1 以下かつ `BT.isStd`
    popStd89   105 項  `BT.isStd` だけ
    popLv89    204 項  段 1 以下だけ
    popK89      81 項  さらに `BT.isStd (ψ₀ ·)`      (§81 の仮説そのもの)
    popHi89     69 項  さらに `Ω₁ ≤ dict a`          (**§89 が語る母集団**)

対は `(a, b)` の順序対で `dict a < dict b` のものだけを数える。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

private def dedup89 (l : List BT) : List BT :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []
private def every89 (k : Nat) (l : List BT) : List BT :=
  (l.zipIdx.filter (fun p => p.2 % k == 0)).map (·.1)
private def dep89 : BT → Nat
  | .zero => 0
  | .D _ a => 1 + dep89 a
  | .sum a b => max (dep89 a) (dep89 b)
private def wid89 : BT → Nat
  | .sum a b => wid89 a + wid89 b
  | _ => 1

private def bs89 : List BT :=
  [BT.zero, BT.D 0 BT.zero, BT.D 0 (BT.D 0 BT.zero), BT.D 1 BT.zero,
   BT.D 1 (BT.D 1 BT.zero), BT.D 0 (BT.D 1 BT.zero)]
private def cap01_89 (l : List BT) : List BT := l.map (BT.D 0) ++ l.map (BT.D 1)
private def cap23_89 (l : List BT) : List BT := l.map (BT.D 2) ++ l.map (BT.D 3)
private def lay89 : Nat → List BT → List BT
  | 0, l => l
  | n + 1, l => every89 2 (cap01_89 (lay89 n l))
private def deep89 : List BT :=
  dedup89 (bs89 ++ lay89 1 bs89 ++ lay89 2 bs89 ++ lay89 3 bs89 ++ lay89 4 bs89
            ++ lay89 5 bs89 ++ lay89 6 bs89 ++ lay89 7 bs89 ++ lay89 8 bs89
            ++ lay89 9 bs89 ++ lay89 10 bs89)
private def prin89 (l : List BT) : List BT := l.filter BT.isP
private def sums2_89 (l : List BT) : List BT :=
  (prin89 l).flatMap (fun a => ((prin89 l).filter (fun b => BT.le b a)).map (BT.sum a))
private def sums3_89 (l : List BT) : List BT :=
  (prin89 l).flatMap (fun a =>
    ((prin89 l).filter (fun b => BT.le b a)).flatMap (fun b =>
      ((prin89 l).filter (fun c => BT.le c b)).map (fun c => BT.sum a (BT.sum b c))))
private def wide89 : List BT :=
  dedup89 (every89 5 (sums2_89 (every89 2 deep89))
            ++ every89 31 (sums3_89 (every89 3 deep89)))
private def out89 : List BT :=
  dedup89 (every89 2 (cap23_89 (every89 3 deep89))
            ++ every89 3 (cap01_89 (every89 5 (cap23_89 (every89 5 deep89)))))

private def popAll89 : List BT := dedup89 (deep89 ++ wide89 ++ out89)
private def popGood89 : List BT := popAll89.filter (fun x => btLe72 1 x && BT.isStd x)
private def popStd89 : List BT := popAll89.filter BT.isStd
private def popLv89 : List BT := popAll89.filter (btLe72 1 ·)
private def popK89 : List BT := popGood89.filter (fun a => BT.isStd (BT.D 0 a))
private def lowW89 (a : BT) : Bool := TM.Term.lt (dict a) (reg 1)
/-- §89 が語る母集団 — §81 が残した場合。 -/
private def popHi89 : List BT := popK89.filter (fun a => !(lowW89 a))

private def pairs89 (l : List BT) : List (BT × BT) :=
  l.flatMap (fun a => l.map (fun b => (a, b)))
private def inv0_89 (l : List (BT × BT)) : Nat :=
  l.countP (fun p => TM.Term.lt (dict p.1) (dict p.2) &&
    !(TM.Term.lt (collapse 0 (dict p.1)) (collapse 0 (dict p.2))))
private def cnt0_89 (l : List (BT × BT)) : Nat :=
  l.countP (fun p => TM.Term.lt (dict p.1) (dict p.2))
private def hipairs89 : List (BT × BT) :=
  (pairs89 popHi89).filter (fun p => TM.Term.lt (dict p.1) (dict p.2))
private def loDomB89 (a : BT) : Bool :=
  (toList (loW89 (dict a))).all (fun p => TM.Term.le p (collapse 0 (hiW89 (dict a))))

/-! 母集団の形 — §81 より深く。 -/
#guard (popAll89.length, popGood89.length, popStd89.length, popLv89.length,
        popK89.length, popHi89.length) == (229, 89, 105, 204, 81, 69)
#guard (popAll89.foldl (fun m x => max m (dep89 x)) 0,
        popK89.foldl (fun m x => max m (dep89 x)) 0) == (13, 12)
#guard (popHi89.foldl (fun m x => max m (dep89 x)) 0,
        popHi89.countP (fun x => wid89 x == 1), popHi89.countP (fun x => wid89 x == 2),
        popHi89.countP (fun x => wid89 x == 3)) == (12, 22, 33, 14)

/-! **分割の内訳。** `dict a < dict b` の順序対 3240 のうち、両辺が `Ω₁` の下は 66
    (§81.1)、`Ω₁` をまたぐのが 828 (§81.4)、両辺が `Ω₁` 以上が 2346 (§89 が語る場合)。
    逆向きは 0 対。§81 は小さい母集団で 36 / 360 / 780 と測った。 -/
#guard (cnt0_89 ((pairs89 popK89).filter (fun p => lowW89 p.1 && lowW89 p.2)),
        cnt0_89 ((pairs89 popK89).filter (fun p => lowW89 p.1 && !(lowW89 p.2))),
        cnt0_89 ((pairs89 popK89).filter (fun p => !(lowW89 p.1) && !(lowW89 p.2))),
        cnt0_89 ((pairs89 popK89).filter (fun p => !(lowW89 p.1) && lowW89 p.2)))
        == (66, 828, 2346, 0)

/-! **肯定 1 — `K` の条件つきでは 3 つの場合すべてで反転 0。** -/
#guard (inv0_89 ((pairs89 popK89).filter (fun p => lowW89 p.1 && lowW89 p.2)),
        inv0_89 ((pairs89 popK89).filter (fun p => lowW89 p.1 && !(lowW89 p.2))),
        inv0_89 ((pairs89 popK89).filter (fun p => !(lowW89 p.1) && !(lowW89 p.2))))
        == (0, 0, 0)

/-! **肯定 2 — §89.3 の閉じた形の受領。** `ψ₀(hi x)` は累算器そのもので、
    `ψ₀(x) = ω^(ψ₀(hi x) ⊕ lo x)`。69 項すべてで食い違い 0 (定理なので確認)。
    主要項には尾がない (`loDom_of_sum89` の受領) のも 22 項すべてで確認。 -/
#guard (popHi89.countP (fun a => !(collapse 0 (hiW89 (dict a)) == accW89 (dict a))),
        popHi89.countP (fun a => !(collapse 0 (dict a)
          == omegaNF (plus (collapse 0 (hiW89 (dict a))) (loW89 (dict a))))),
        (popHi89.filter BT.isP).countP (fun a => !(loW89 (dict a) == zero)))
        == (0, 0, 0)

/-! **肯定 3 — 場合分けの受領。** `hi` が同じ対と違う対は 9 / 2337 に分かれ、
    「`hi` が同じ」と「累算器が同じ」は完全に一致する (食い違い 0)。
    `hi` が違う 2337 対では `hi` は順序を保ち (`lt_hi89` の受領)、
    `ψ₀(hi ·)` も順序を保つ — つまり `HiMono89` は母集団の上では真。 -/
#guard (hipairs89.countP (fun p => hiW89 (dict p.1) == hiW89 (dict p.2)),
        hipairs89.countP (fun p => !(hiW89 (dict p.1) == hiW89 (dict p.2))))
        == (9, 2337)
#guard hipairs89.countP (fun p => (hiW89 (dict p.1) == hiW89 (dict p.2))
        != (accW89 (dict p.1) == accW89 (dict p.2))) == 0
#guard (hipairs89.countP (fun p => !(hiW89 (dict p.1) == hiW89 (dict p.2))
          && !(TM.Term.lt (hiW89 (dict p.1)) (hiW89 (dict p.2)))),
        hipairs89.countP (fun p => !(hiW89 (dict p.1) == hiW89 (dict p.2))
          && !(TM.Term.lt (collapse 0 (hiW89 (dict p.1))) (collapse 0 (hiW89 (dict p.2))))))
        == (0, 0)

/-! **肯定 4 — 残余の 63% は尾がない。** 69 項のうち 55 項、2346 対のうち 1485 対が
    両辺とも尾なしで、そこでは `hiW89` は恒等 (`hiW89_self89`) だから `HiMono89` は
    §81 の残余の文そのものである。 -/
#guard (popHi89.countP (fun a => loW89 (dict a) == zero),
        hipairs89.countP (fun p => loW89 (dict p.1) == zero && loW89 (dict p.2) == zero))
        == (55, 1485)

/-! **肯定 5 — 尾の条項は母集団の上では真で、しかもほとんど只。** `K` 標準の 69 項で
    破れ 0、そのうち 60 項は尾が ε₀ より下 (`loDom_of_ltE89` が片づける)、
    22 項は主要項 (`loDom_of_sum89` が片づける)。和の形の 47 項でも破れ 0。 -/
#guard (popHi89.countP (fun a => !(loDomB89 a)),
        popHi89.countP (fun a => (toList (loW89 (dict a))).all (fun p => TM.Term.lt p E081)),
        popHi89.countP BT.isP,
        (popHi89.filter (fun a => !(BT.isP a))).countP (fun a => !(loDomB89 a)))
        == (0, 60, 22, 0)

/-! **否定 1 — `K` の条件を落とすと 149 対反転し、両辺 `Ω₁` 以上の場合の 1 対が
    `not_hiMonoNoK89` の証人。** 内訳は (下,下) 0・(下,上) 148・(上,上) 1。
    §81 は 66 対 (0 / 65 / 1) と測った。**深さを 10 段から 13 段へ、幅を 3 項へ
    開けても、両辺 `Ω₁` 以上の反転はやはりこの 1 対だけである。** -/
#guard (inv0_89 (pairs89 popK89), inv0_89 (pairs89 popGood89),
        inv0_89 (pairs89 popStd89), inv0_89 (pairs89 popLv89)) == (0, 149, 221, 2094)
#guard (inv0_89 ((pairs89 popGood89).filter (fun p => lowW89 p.1 && lowW89 p.2)),
        inv0_89 ((pairs89 popGood89).filter (fun p => lowW89 p.1 && !(lowW89 p.2))),
        inv0_89 ((pairs89 popGood89).filter (fun p => !(lowW89 p.1) && !(lowW89 p.2))))
        == (0, 148, 1)
#guard ((pairs89 popGood89).filter (fun p => !(lowW89 p.1) && !(lowW89 p.2) &&
          TM.Term.lt (dict p.1) (dict p.2) &&
          !(TM.Term.lt (collapse 0 (dict p.1)) (collapse 0 (dict p.2)))))
        == [(cexA89, cexB89)]

/-! **否定 2 — 尾の条項の反例は母集団の外にある。** `loBad89 = Ω₁ ⊕ ψ₀(Ω₁ ⊕ Ω₁)` は
    `BT.isStd` を満たすのに尾の条項を破る。**標準の 105 項はこの項を含まず、破れも
    見ない** — 母集団だけを見ていたら `BT.isStd` で足りると誤るところである。
    段の上限だけに緩めると 17 項が破る。 -/
#guard (popStd89.contains loBad89, popAll89.contains loBad89) == (false, false)
#guard ((popStd89.filter (fun a => !(lowW89 a))).countP (fun a => !(loDomB89 a)),
        (popLv89.filter (fun a => !(lowW89 a))).countP (fun a => !(loDomB89 a)))
        == (0, 17)

/-! **否定 3 — 和のまま書いた尾の条項は領域の中で偽。** `loSum89` は `K` 標準で
    成分ごとの条項を満たすのに `le (lo x) (ψ₀ (hi x))` は偽 (`not_le_lo_hi89`)。 -/
#guard (BT.isStd (BT.D 0 loSum89), loDomB89 loSum89,
        TM.Term.le (loW89 (dict loSum89)) (collapse 0 (hiW89 (dict loSum89))))
        == (true, true, false)

end

/-! ### §89.9 公理

§89 が足した公理はない。`HiMono89`・`LoDom89` はどちらも `Prop` の**仮説**であって
公理ではなく、`collapseMono0Hi_of_89` の引数として明示的に渡る。
`#print axioms` は下のとおり。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg)
open TM TM.Term

end

end Evidence.Region
