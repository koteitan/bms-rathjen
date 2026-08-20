import Evidence.RegionNext7

/-
Evidence/RegionNext8.lean — ROW 326'S REMAINING HYPOTHESES, FIFTH PART (§127-)

Split out of `RegionNext7` at 8600 lines.  Section numbers are not in file order — sections
were appended as their agents finished.
-/

namespace Evidence.Region

open BMS

/-! ## §128-§130 THREE ATTACKS ON THE TWO GATES §126 LEFT

§126 put the whole question on three branches: `PsiIdxOKStd172` is false, or `HiMono89` is
false, or the table's value is too big somewhere in the sub-region.  §128, §129 and §130
were run against the gates themselves, in parallel and independently, before §125 and §126
were written.  None of the three settles a branch.  What they do is narrow.

  §128  `VebPairs123` — the 𝔗(M) translation §90 said nobody had, BUILT, and the clause
        re-hung on `VebD0_128`, a statement about the `ψ₀`-arguments a non-firing pair names.
  §129  `VebRest117` — the residue is two `phiNF` facts, and BOTH ARE THEOREMS.  What is
        left is `VebRest129`, whose premise never fires anywhere reachable.
  §130  `PsiIdxOKStd172` — NOT refuted, but FALSE the moment `BT.isStd` is dropped, at
        level `≤ 1`, minimal witness at 9 symbols.  The `u = 1` half and the level-zero
        `u = 0` half are theorems.  What is left is one case.

**READ THEM AGAINST §126, NOT AGAINST ROW 326.**  §128 and §129 each end with a
`certIn_t326_*`, written before §125 and §126 existed.  Those certificates are VACUOUS —
§125 showed their hypotheses are contradictory and §126 showed the other route is too.  The
value of §128 and §129 is not the certificate.  It is that both clauses of `HiMono89` are
now narrow enough to be attacked directly, and `HiMono89` is one of the two gates that
decide which branch of §126 holds. -/
/-! ## §128 THE TRANSLATION §90 SAID NOBODY HAD — `VebPairs123` BECOMES A STATEMENT ABOUT
       `ψ₀`-VALUES, AND §90.1's FOUR FACTS LAND ON EXACTLY THE TERMS IT QUANTIFIES OVER

§123 left row 326 with one decidable clause, `VebPairs123`: at a residual step, every
NON-FIRING pair of the base-`Ω₁` decomposition of `dict a` has its exponent AND its
coefficient below the target `ψ_{Ω₁}(j_b)`.  §123 named what closes it — "what the other
needs is the `BT`-side fact §114 named … which is §90.1 translated into 𝔗(M), and §90 says
plainly that this translation is what nobody has."  §90's header says the same from the other
end: "§90 does not turn `e < a` in Buchholz's order into any statement about `𝔗(M)`."

**§128 builds that translation.**  It does not prove `VebPairs123`; it REPLACES it by a clause
about `ψ₀`-VALUES — `VebD0_128` — whose quantified terms are exactly §90.1's `e`, with all
four of §90.1's facts free at them (`vebArgs_lt128`, `vebArgs_isStd128`, `vebArgs_btLe128`,
`vebArgs_size128`).  §90.4's trap is avoided by construction: `e < a` is NOT transported and
hung on the clause as a guard — §90.6 proved that guard is vacuous on the sub-region — the
`ψ₀`-VALUE of `e` is compared against the target THE STEP produced, `ψ_{Ω₁}(j_b)`.

WHAT IS PROVED (every `dict` fact carries `PsiIdxOKStd172`, as everywhere in the file).

  §128.1  **THE TARGET IS CLOSED UNDER `ω^·`, AND `Ω₁` REFLECTS THROUGH IT.**
          `omegaNF_eq_phiNF128` (below `M`, `ω^·` is only `φ̄0·`) turns §114.1's
          `lt_phiNF_psi114` into `lt_omegaNF_psi128`; `ltW_of_ltW_omegaNF128` is the
          reflection `ω^X < Ω₁ ⟹ X < Ω₁`, which is §122's `le_omegaNF122` at `ω^{Ω₁} = Ω₁`.

  §128.2  **THE NAME LIST** (`vebArgs128`).  For a component `ψ₁c` of `a`: the coefficient
          names the `ψ₀`-arguments in `c`'s subscript-0 components (§104.2's `wC` in closed
          form), and the exponent names those in `x`'s subscript-0 components for `ψ₁x` a
          component of `c`.  **Depth 2, and it stops there** — §128.3 is why.

  §128.3  **BOTH HALVES OF A NON-FIRING PAIR ARE BELOW THE TARGET.**  `lt_wC_dict128` is
          §104.2's `wC_dict_D1_104` plus §101.1's `lo`-inclusion.  `lt_wA_dict128` is the
          half §104 did not do: `toList_wA119` + §119.2's `mem_toList_plusW119` and
          `divAP_dictD1_119` make every digit of the exponent either `1` (from `Ω₁`) or
          `ω^(dict x)`; NON-FIRING forces each `ω^(dict x) < Ω₁`, hence `dict x < Ω₁`, hence
          `x` has subscript-0 components only — **that is what closes the recursion at
          depth 2** — and `lt_dict_of_lo128` bounds it by the names.

  §128.4  **THE LIST LEVEL** (`vebPairL128`).  From the per-component condition `compOK128`
          to `vebPair123`'s `all`.  The only thing `wcnf`'s merge branch does to a pair is
          ADD coefficients, and §114.1's `lt_plus_ap114` says the target is closed under `⊕`.

  §128.5  **THE TRANSLATION** (`vebPair_of_vebArgs128`), and the sub-region it buys for
          nothing: where the name list is EMPTY, `vebPair123` is a theorem with no clause
          at all (`vebPair_of_nil128`, `vebPairs_nil128`) — 179 of the 2029 pairs §128.9
          measures, 162 of the 1045 `K`-standard ones.

  §128.6  **THE CLAUSE** (`VebD0_128`), `vebPairs123_of_vebD0_128`, `vebIngF114_of_vebD0_128`
          and `certIn_t326_128` — row 326 re-hung, with `IdxLeMix109`, `VebRest117`,
          `DictOntoMidOpen103`, `DictDenseMid107`, `DictDenseAbove107` untouched.

  §128.7  **THE NAMES ARE §90.1's.**  `vebArgs_sub_d0Args128 : vebArgs128 a ⊆ d0Args88 a`,
          so §90.1's `lt_d0Args_90`, `isStd_d0Args_90`, `btLe72_d0Args_90` and
          `size_d0Args_90` all apply verbatim: every `d` the clause quantifies over
          satisfies `d < a`, `isStd (ψ₀d)`, `btLe72 1 d` and `size d < size a`.

WHAT IS **NOT** CLAIMED.  **`VebD0_128` is NOT proved and NOT refuted, and `VebPairs123`
therefore still stands.**  §128 does not prove `dict` order-preserving and does not use
`DictLtA74` (which is a consequence of `HiMono89`, so using it would be circular).  The
clause is NOT proved equivalent to `VebPairs123`: only the direction `VebD0_128 ⟹
VebPairs123` is a theorem.  Outside the class the clause is stated on it is strictly
stronger, and §128.9 measures by how much.  `IdxLeMix109`, `VebRest117`, `PsiIdxOKStd172`,
`DictOntoMidOpen103`, `DictDenseMid107`, `DictDenseAbove107` are untouched.

WHAT THE MEASUREMENT SAYS (§128.9 gives the construction: §101/§104/§114's built witnesses —
`revA114`, `revB114`, `sepRA114`, `sepRB114`, `scBadA101`, `scBadB101`, `sepA104` — with
fourteen lines built here to put a `ψ₀` under a `ψ₁` at depth 1 and at depth 2, widened by
two-term sums and one `ψ₁` layer; 219 terms, nothing filtered).

  * **The shape is in the population before any sweep.**  Of the 146 terms meeting the shape
    condition, **118 have a non-empty name list** and **129 carry a non-firing pair**; the
    largest is 22 symbols.
  * **The half the clause is responsible for is not empty.**  10262 residual pairs, **2029**
    with `b` all-firing; `K`-standard, 3525 and **1045**.
  * **The translation moves no residue on its own class.**  On those 2029 pairs
    `vebPair123` fails **81** times and the clause fails **the same 81** — 0 violations of
    the implication and **0 of the converse**.  On the 1045 `K`-standard ones neither fails.
  * **And it is not a sweep that cannot see its subject.**  Unfiltered, on 21316 pairs
    `vebPair123` fails 5570 times and the clause 5687; the implication is violated **0**
    times and the converse **117** — the gap is outside the class, where the list also names
    the arguments of FIRING components.  Taking all of §90.1's `e` instead (`d0Args88`) keeps
    the implication but pushes the converse to **1277**: **stopping the list at depth 2 is
    worth a factor of ten**, and §128.3 is the theorem that says depth 2 is enough.
  * **Both negatives are built, not swept.**  `revA114`'s name list is exactly one term,
    `ψ₁ψ₁ψ₁0`, whose `ψ₀`-value is `Γ₀` and whose target is `Γ₀` — the clause and
    `vebPair123` break together at the witness §123 said its theorem could not touch
    (`revA_facts128`).  `posA128 = ψ₁ψ₀ψ₁ψ₀0` against `ψ₁ψ₁ψ₁ψ₁0` is `K`-standard, meets
    every hypothesis, has a non-empty list and satisfies both (`posA_facts128`).
-/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-! ### §128.1 THE TARGET IS CLOSED UNDER `ω^·`, AND `Ω₁` REFLECTS THROUGH IT -/

/-- `M` の下では `ω^·` は `φ̄0·` の枝しか通らない。 -/
theorem omegaNF_eq_phiNF128 {X : Term} (hX : inT X = true) (hXM : lt X M = true) :
    omegaNF X = phiNF zero X := by
  have h1 : lt M X = false := lt_asymm_inT hX (show inT (M : Term) = true from rfl) hXM
  have h2 : (X == M) = false := by
    cases hc : (X == M) with
    | false => rfl
    | true =>
        exfalso
        rw [eq_of_beq hc, lt_irrefl] at hXM
        exact Bool.noConfusion hXM
  show (if lt M X = true then omg X else if (X == M) = true then M else phiNF zero X) = _
  rw [if_neg (by rw [h1]; exact Bool.noConfusion),
    if_neg (by rw [h2]; exact Bool.noConfusion)]

/-- **強臨界の的は `ω^·` で閉じている。** -/
theorem lt_omegaNF_psi128 {X k c : Term} (hfS : FragR (psi k c) = true) (hX : inT X = true)
    (hXM : lt X M = true) (h : lt X (psi k c) = true) : lt (omegaNF X) (psi k c) = true := by
  rw [omegaNF_eq_phiNF128 hX hXM]
  exact lt_phiNF_psi114 hfS hX (lt_zero_left (fun hc => Term.noConfusion hc)) h

/-- `Ω₁ ≤ X` が偽なら `X < Ω₁`。 -/
theorem ltW_of_leW_false128 {X : Term} (hX : inT X = true) (h : le (reg 1) X = false) :
    lt X (reg 1) = true := by
  have hsplit := Bool.or_eq_false_iff.mp (show ((reg 1 == X) || lt (reg 1) X) = false from h)
  have hle : le X (reg 1) = true :=
    le_of_not_lt3 (inT_le_fragR _ (inT_reg 1)) (inT_le_fragR _ hX) hsplit.2
  have hne : (X == reg 1) = false := by
    cases hc : (X == reg 1) with
    | false => rfl
    | true =>
        exfalso
        rw [eq_of_beq hc, beq_self_eq_true] at hsplit
        exact Bool.noConfusion hsplit.1
  rcases (Bool.or_eq_true _ _).mp (show ((X == reg 1) || lt X (reg 1)) = true from hle) with h1 | h1
  · rw [hne] at h1; exact Bool.noConfusion h1
  · exact h1

/-- `ω^X < Ω₁` なら `X < Ω₁` — `Ω₁ = ω^{Ω₁}` だから。 -/
theorem ltW_of_ltW_omegaNF128 {X : Term} (hX : inT X = true)
    (h : lt (omegaNF X) (reg 1) = true) : lt X (reg 1) = true := by
  cases hc : le (reg 1) X with
  | false => exact ltW_of_leW_false128 hX hc
  | true =>
      exfalso
      have hge := le_omegaNF122 (inT_reg 1) hX (show omegaNF (reg 1) = reg 1 from rfl) hc
      rw [not_le_of_lt113 (inT_reg 1) (inT_omegaNF hX) h] at hge
      exact Bool.noConfusion hge

end

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-! ### §128.2 THE `ψ₀`-ARGUMENTS A NON-FIRING PAIR NAMES -/

/-- **非発火の対が名指す `ψ₀` の引数。**  添字 1 の成分 `ψ₁c` について、係数が名指すのは
    `c` の段 0 の成分の引数、指数が名指すのは `c` の添字 1 の成分 `ψ₁x` の `x` の段 0 の
    成分の引数 — 深さ 2 で止まる。 -/
def vebArgs128 (a : BT) : List BT :=
  coefArgs104 a ++ (BT.toL a).flatMap (fun p => match p with
    | BT.D 1 c => coefArgs104 c
    | _ => [])

/-- §104 の `mem_coefArgs104` の逆。 -/
theorem mem_coefArgs_of128 {a c d : BT} (hc : BT.D 1 c ∈ BT.toL a)
    (hd : BT.D 0 d ∈ BT.toL c) : d ∈ coefArgs104 a :=
  List.mem_flatMap.mpr ⟨BT.D 1 c, hc,
    List.mem_flatMap.mpr ⟨BT.D 0 d, hd, List.Mem.head _⟩⟩

/-- 係数の側の引数は名簿の中。 -/
theorem mem_vebArgs_coef128 {a c d : BT} (hc : BT.D 1 c ∈ BT.toL a)
    (hd : BT.D 0 d ∈ BT.toL c) : d ∈ vebArgs128 a :=
  List.mem_append_left _ (mem_coefArgs_of128 hc hd)

/-- 指数の側の引数も名簿の中。 -/
theorem mem_vebArgs_exp128 {a c x d : BT} (hc : BT.D 1 c ∈ BT.toL a)
    (hx : BT.D 1 x ∈ BT.toL c) (hd : BT.D 0 d ∈ BT.toL x) : d ∈ vebArgs128 a :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨BT.D 1 c, hc, mem_coefArgs_of128 hx hd⟩)

/-! ### §128.3 COEFFICIENT AND EXPONENT, BOTH BELOW THE TARGET -/

/-- **像が `Ω₁` の下にある項は、その段 0 の成分の値が的の下なら的の下。** -/
theorem lt_dict_of_lo128 (Hp : PsiIdxOKStd172) {x : BT} {k t : Term}
    (hbx : btLe72 1 x = true) (hsx : BT.isStd x = true)
    (hlow : lt (dict x) (reg 1) = true)
    (h : ∀ d : BT, BT.D 0 d ∈ BT.toL x → lt (dict (BT.D 0 d)) (psi k t) = true) :
    lt (dict x) (psi k t) = true := by
  obtain ⟨hix, hxM⟩ := inT_dict_of_std172 Hp x hbx hsx
  have hall : ∀ z ∈ toList (dict x), lt z (reg 1) = true :=
    ltAP_toList114 (inT_le_fragR _ (inT_reg 1)) (show (reg 1).isAP = true from rfl)
      _ hix hlow
  have hfil : toList (loW89 (dict x)) = toList (dict x) := by
    rw [toList_loW89 hix]
    exact List.filter_eq_self.mpr (fun z hz => by rw [hall z hz])
  rw [← inT_ofList_toList _ hix]
  refine lt_ofList_ap114 (show (psi k t).isAP = true from rfl)
    (fun hc => Term.noConfusion hc) _ ?_
  intro z hz
  obtain ⟨d, hd, hze⟩ := mem_toList_loW_dict101 Hp hbx hsx z (by rw [hfil]; exact hz)
  rw [hze]
  exact h d hd

/-- **係数は的の下** — 係数が名指す `ψ₀` の値が的の下なら。 -/
theorem lt_wC_dict128 (Hp : PsiIdxOKStd172) {c : BT} {k t : Term}
    (hbc : btLe72 1 c = true) (hsc : BT.isStd c = true)
    (hfS : FragR (psi k t) = true)
    (h : ∀ d : BT, BT.D 0 d ∈ BT.toL c → lt (dict (BT.D 0 d)) (psi k t) = true) :
    lt (wC (reg 1) (dict (BT.D 1 c))) (psi k t) = true := by
  obtain ⟨hic, hcM⟩ := inT_dict_of_std172 Hp c hbc hsc
  have hilo : inT (loW89 (dict c)) = true := inT_loW89 hic
  have hloM : lt (loW89 (dict c)) M = true := by
    show lt (ofList ((toList (dict c)).filter (fun p => lt p (reg 1)))) M = true
    exact lt_ofList_M _ (fun z hz => ltM_toList _ hic hcM z (List.mem_filter.mp hz).1)
  rw [wC_dict_D1_104 Hp hbc hsc]
  refine lt_omegaNF_psi128 hfS hilo hloM ?_
  rw [← inT_ofList_toList _ hilo]
  refine lt_ofList_ap114 (show (psi k t).isAP = true from rfl)
    (fun hcc => Term.noConfusion hcc) _ ?_
  intro z hz
  obtain ⟨d, hd, hze⟩ := mem_toList_loW_dict101 Hp hbc hsc z hz
  rw [hze]
  exact h d hd


/-- **指数も的の下** — 対が発火しないとき。  `Ω₁` 由来の桁は `1`、それ以外は
    `ω^(dict x)` で、非発火だから `dict x < Ω₁`、すなわち `x` は段 0 の成分だけである。 -/
theorem lt_wA_dict128 (Hp : PsiIdxOKStd172) {c : BT} {k t : Term}
    (hbD : btLe72 1 (BT.D 1 c) = true) (hsD : BT.isStd (BT.D 1 c) = true)
    (hfS : FragR (psi k t) = true)
    (hnf : le (reg 1) (wA (reg 1) (dict (BT.D 1 c))) = false)
    (h : ∀ x d : BT, BT.D 1 x ∈ BT.toL c → BT.D 0 d ∈ BT.toL x →
          lt (dict (BT.D 0 d)) (psi k t) = true) :
    lt (wA (reg 1) (dict (BT.D 1 c))) (psi k t) = true := by
  have hbc : btLe72 1 c = true := (btLe72_D 1 1 c hbD).2
  have hsc : BT.isStd c = true := isStd_of_D hsD
  obtain ⟨hic, hcM⟩ := inT_dict_of_std172 Hp c hbc hsc
  obtain ⟨hip, hpM⟩ := inT_dict_of_std172 Hp (BT.D 1 c) hbD hsD
  have hiwA : inT (wA (reg 1) (dict (BT.D 1 c))) = true :=
    inT_wA109 (inT_reg 1) (show (reg 1).isSC = true from rfl) hip
  have hltW : lt (wA (reg 1) (dict (BT.D 1 c))) (reg 1) = true :=
    ltW_of_leW_false128 hiwA hnf
  have hallW : ∀ z ∈ toList (wA (reg 1) (dict (BT.D 1 c))), lt z (reg 1) = true :=
    ltAP_toList114 (inT_le_fragR _ (inT_reg 1)) (show (reg 1).isAP = true from rfl)
      _ hiwA hltW
  have hgoodc : GoodL77 (BT.toL c) := good_toL77 c hsc hbc
  have key : ∀ z ∈ toList (wA (reg 1) (dict (BT.D 1 c))), lt z (psi k t) = true := by
    intro z hz
    have hzW := hallW z hz
    rw [toList_wA119] at hz
    obtain ⟨q, hq, hze⟩ := List.mem_map.mp hz
    have hqm : q ∈ toList (logOm (dict (BT.D 1 c))) := (List.mem_filter.mp hq).1
    have hqw : lt q (reg 1) = false := by
      have hb := (List.mem_filter.mp hq).2
      cases hcq : lt q (reg 1) with
      | false => rfl
      | true => rw [hcq] at hb; exact Bool.noConfusion hb
    rw [logOm_dict_D1_104 Hp hbc hsc] at hqm
    rcases mem_toList_plusW119 hic q hqm with hcase | hcase
    · rw [← hze, hcase, divAP_W_W_119]
      exact lt_one_psi95 k t
    · have hhi : q ∈ toList (hiW89 (dict c)) := by
        rw [toList_hiW89 hic]
        exact List.mem_filter.mpr ⟨hcase, by rw [hqw]; rfl⟩
      obtain ⟨x, hxm, hqe⟩ := mem_toList_hiW_dict101 Hp hbc hsc q hhi
      have hbx1 : btLe72 1 (BT.D 1 x) = true := hgoodc.2.2.1 _ hxm
      have hsx1 : BT.isStd (BT.D 1 x) = true := hgoodc.2.1 _ hxm
      have hbx : btLe72 1 x = true := (btLe72_D 1 1 x hbx1).2
      have hsx : BT.isStd x = true := isStd_of_D hsx1
      have hdiv : divAP (reg 1) q = omegaNF (dict x) := by
        rw [hqe]; exact divAP_dictD1_119 Hp hbx hsx
      obtain ⟨hix, hxM⟩ := inT_dict_of_std172 Hp x hbx hsx
      have hlowx : lt (dict x) (reg 1) = true := by
        refine ltW_of_ltW_omegaNF128 hix ?_
        rw [← hdiv, hze]; exact hzW
      rw [← hze, hdiv]
      exact lt_omegaNF_psi128 hfS hix hxM
        (lt_dict_of_lo128 Hp hbx hsx hlowx (fun d hd => h x d hxm hd))
  rw [← inT_ofList_toList _ hiwA]
  exact lt_ofList_ap114 (show (psi k t).isAP = true from rfl)
    (fun hcc => Term.noConfusion hcc) _ key


/-! ### §128.4 THE LIST LEVEL — merging only adds coefficients -/

/-- 一成分ぶんの条件 — 発火するか、指数も係数も的の下か。 -/
def compOK128 (S p : Term) : Bool :=
  le (reg 1) (wA (reg 1) p) || (lt (wA (reg 1) p) S && lt (wC (reg 1) p) S)

/-- **成分ごとの条件から対の列の条件へ。**  `wcnf` の併合は係数を足すだけで、
    加法主要な的の下では `⊕` は閉じている。 -/
theorem vebPairL128 {S : Term} (hSap : S.isAP = true) (hSz : S ≠ zero)
    (hfS : FragR S = true) :
    ∀ (L : List Term), inTL L = true → descL L = true → (∀ x ∈ L, lt x M = true) →
      (∀ p ∈ L, lt p (reg 1) = false → compOK128 S p = true) →
      ∀ ac ∈ (wcnf (reg 1) L).1, (le (reg 1) ac.1 || (lt ac.1 S && lt ac.2 S)) = true := by
  intro L
  induction L with
  | nil => intro _ _ _ _ ac hac; rw [wcnf_nil] at hac; cases hac
  | cons p rest ih =>
    intro hc hd hm hcomp
    obtain ⟨⟨_, hip⟩, hcr⟩ := inTL_cons.mp hc
    have hdr := descL_tail hd
    have hmr : ∀ x ∈ rest, lt x M = true := fun x hx => hm x (List.Mem.tail p hx)
    have IH := ih hcr hdr hmr (fun q hq => hcomp q (List.Mem.tail _ hq))
    by_cases hlp : lt p (reg 1) = true
    · intro ac hac; rw [wcnf_cons_lt hlp] at hac; cases hac
    · have hlp' : lt p (reg 1) = false := bool_false hlp
      have hpc := hcomp p (List.Mem.head _) hlp'
      have hiC : inT (wC (reg 1) p) = true := inT_wC hip
      obtain ⟨_, hallR⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) rest hcr hdr hmr
      intro ac hac
      rw [wcnf_cons_ge hlp'] at hac
      cases hr : wcnf (reg 1) rest with
      | mk fst snd =>
        rw [hr] at hac IH hallR
        cases fst with
        | nil => rw [List.mem_singleton.mp hac]; exact hpc
        | cons ac0 ps =>
          cases ac0 with
          | mk a' c' =>
            have h0 := IH (a', c') (List.Mem.head _)
            have hic' : inT c' = true := (hallR (a', c') (List.Mem.head _)).2.2.1
            have hac2 : ac ∈ (if (wA (reg 1) p == a') = true
                then ((wA (reg 1) p, plus (wC (reg 1) p) c') :: ps, snd)
                else ((wA (reg 1) p, wC (reg 1) p) :: (a', c') :: ps, snd)).1 := hac
            by_cases heq : (wA (reg 1) p == a') = true
            · rw [if_pos heq] at hac2
              rcases List.mem_cons.mp hac2 with h1 | h1
              · rw [h1]
                show (le (reg 1) (wA (reg 1) p)
                  || (lt (wA (reg 1) p) S && lt (plus (wC (reg 1) p) c') S)) = true
                rcases (Bool.or_eq_true _ _).mp hpc with hf | hf
                · rw [hf]; rfl
                · rcases (Bool.or_eq_true _ _).mp h0 with hf0 | hf0
                  · rw [eq_of_beq heq]
                    rw [show le (reg 1) a' = true from hf0]
                    rfl
                  · rw [((Bool.and_eq_true _ _).mp hf).1,
                      lt_plus_ap114 hSap hSz hfS hiC hic'
                        ((Bool.and_eq_true _ _).mp hf).2 ((Bool.and_eq_true _ _).mp hf0).2]
                    exact Bool.or_true _
              · exact IH ac (List.Mem.tail _ h1)
            · rw [if_neg heq] at hac2
              rcases List.mem_cons.mp hac2 with h1 | h1
              · rw [h1]; exact hpc
              · exact IH ac h1

/-! ### §128.5 THE TRANSLATION -/

/-- **§128 の翻訳定理 — §123 の対の条項は `ψ₀` の値の条項に翻訳される。**
    §90.1 が `BT` の順序で名指しした `e` の像 `dict (ψ₀ e)` が的の下にあれば、
    底 `Ω₁` の分解の非発火の対の指数も係数も的の下にある。 -/
theorem vebPair_of_vebArgs128 (Hp : PsiIdxOKStd172) {a : BT} {k t : Term}
    (hba : btLe72 1 a = true) (hsa : BT.isStd a = true)
    (hfS : FragR (psi k t) = true)
    (h : ∀ d ∈ vebArgs128 a, lt (dict (BT.D 0 d)) (psi k t) = true) :
    vebPair123 (dict a) (psi k t) = true := by
  obtain ⟨hia, haM⟩ := inT_dict_of_std172 Hp a hba hsa
  obtain ⟨hcL, hdL⟩ := inT_toList (dict a) hia
  refine List.all_eq_true.mpr ?_
  refine vebPairL128 (show (psi k t).isAP = true from rfl)
    (fun hcc => Term.noConfusion hcc) hfS (toList (dict a)) hcL hdL
    (ltM_toList _ hia haM) ?_
  intro p hp hpw
  have hphi : p ∈ toList (hiW89 (dict a)) := by
    rw [toList_hiW89 hia]
    exact List.mem_filter.mpr ⟨hp, by rw [hpw]; rfl⟩
  obtain ⟨c, hmem, hpe⟩ := mem_toList_hiW_dict101 Hp hba hsa p hphi
  have hgood : GoodL77 (BT.toL a) := good_toL77 a hsa hba
  have hb1 : btLe72 1 (BT.D 1 c) = true := hgood.2.2.1 _ hmem
  have hs1 : BT.isStd (BT.D 1 c) = true := hgood.2.1 _ hmem
  have hbc : btLe72 1 c = true := (btLe72_D 1 1 c hb1).2
  have hsc : BT.isStd c = true := isStd_of_D hs1
  subst hpe
  show (le (reg 1) (wA (reg 1) (dict (BT.D 1 c)))
    || (lt (wA (reg 1) (dict (BT.D 1 c))) (psi k t)
        && lt (wC (reg 1) (dict (BT.D 1 c))) (psi k t))) = true
  cases hfire : le (reg 1) (wA (reg 1) (dict (BT.D 1 c))) with
  | true => rfl
  | false =>
      rw [lt_wA_dict128 Hp hb1 hs1 hfS hfire
            (fun x d hx hdd => h d (mem_vebArgs_exp128 hmem hx hdd)),
        lt_wC_dict128 Hp hbc hsc hfS
            (fun d hdd => h d (mem_vebArgs_coef128 hmem hdd))]
      exact Bool.or_true _

/-- **§128 が只で買う一区画 — 名簿が空なら条項は要らない。**  `a` の添字 1 の成分の
    引数の中に (深さ 2 まで) `ψ₀` が一つも現れないところでは、`vebPair123` は
    条項なしの定理である。 -/
theorem vebPair_of_nil128 (Hp : PsiIdxOKStd172) {a : BT} {k t : Term}
    (hba : btLe72 1 a = true) (hsa : BT.isStd a = true) (hfS : FragR (psi k t) = true)
    (hnil : vebArgs128 a = []) : vebPair123 (dict a) (psi k t) = true :=
  vebPair_of_vebArgs128 Hp hba hsa hfS (fun d hd => by rw [hnil] at hd; cases hd)

/-- その区画を `VebPairs123` の仮定の形で。 -/
theorem vebPairs_nil128 (Hp : PsiIdxOKStd172) {a b : BT} {jb : Term}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hbB : btLe72 1 (BT.D 0 b) = true)
    (hsA : BT.isStd (BT.D 0 a) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (hjb : idxF88 0 (dict b) = some jb) (hnil : vebArgs128 a = []) :
    vebPair123 (dict a) (psi (reg 1) jb) = true := by
  have hbb := (btLe72_D 1 0 b hbB).2
  obtain ⟨hib, hibM⟩ := inT_dict_of_std172 Hp b hbb (isStd_of_D hsB)
  exact vebPair_of_nil128 Hp (btLe72_D 1 0 a hbA).2 (isStd_of_D hsA)
    (fragR_psi_reg92 (inT_le_fragR jb (inT_idxF92 hib hibM hjb))) hnil

/-! ### §128.6 THE REMAINING CLAUSE AND ROW 326 -/

/-- **残る条項 — `ψ₀` の値の側。**  §90.1 が `BT` の順序で `e < a` を出すその `e` に
    ついて、`ψ₀ e` の像が的 `ψ_{Ω₁}(j_b)` の下にあるか。**証明しない。** -/
def VebD0_128 : Prop :=
  ∀ (a b : BT) (jb : Term), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lastFire92 (dict a) = false → lastFire92 (dict b) = true →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    idxF88 0 (dict b) = some jb →
    ∀ d ∈ vebArgs128 a, lt (dict (BT.D 0 d)) (psi (reg 1) jb) = true

/-- **§128 の主定理 — 新しい条項は §123 の条項を出す。** -/
theorem vebPairs123_of_vebD0_128 (Hp : PsiIdxOKStd172) (H : VebD0_128) : VebPairs123 := by
  intro a b jb hbA hbB hsA hsB hWa hWb hfa hfb hlt hjb
  have hba := (btLe72_D 1 0 a hbA).2
  have hsa := isStd_of_D hsA
  have hbb := (btLe72_D 1 0 b hbB).2
  obtain ⟨hib, hibM⟩ := inT_dict_of_std172 Hp b hbb (isStd_of_D hsB)
  have hijb : inT jb = true := inT_idxF92 hib hibM hjb
  have hfS : FragR (psi (reg 1) jb) = true := fragR_psi_reg92 (inT_le_fragR jb hijb)
  exact vebPair_of_vebArgs128 Hp hba hsa hfS
    (H a b jb hbA hbB hsA hsB hWa hWb hfa hfb hlt hjb)

/-- 系 — §114 の条項も出る。 -/
theorem vebIngF114_of_vebD0_128 (Hp : PsiIdxOKStd172) (H : VebD0_128) : VebIngF114 :=
  vebIngF_of_pairs123 Hp (vebPairs123_of_vebD0_128 Hp H)

/-- **326 行目を架け替える。** -/
theorem certIn_t326_128 (Hp : PsiIdxOKStd172) (HB : IdxLeMix109) (H1 : VebD0_128)
    (H2 : VebRest117) (HD1 : DictOntoMidOpen103) (HD3 : DictDenseMid107)
    (HD4 : DictDenseAbove107) (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_123 Hp HB (vebPairs123_of_vebD0_128 Hp H1) H2 HD1 HD3 HD4 hacc


/-! ### §128.7 THE ARGUMENTS ARE §90.1's, AND §90.1's FOUR FACTS ARE FREE AT THEM -/

/-- `d0Args88` は成分の中へ遺伝する — §104 の `sub_GB0_104` と同じ形。 -/
theorem d0Args_toL128 : ∀ (a p : BT), p ∈ BT.toL a → ∀ e ∈ d0Args88 p, e ∈ d0Args88 a := by
  intro a
  induction a with
  | zero => intro p h; cases h
  | D v x _ =>
    intro p h e he
    rw [List.mem_singleton.mp (show p ∈ [BT.D v x] from h)] at he
    exact he
  | sum s t ihs iht =>
    intro p h e he
    show e ∈ d0Args88 s ++ d0Args88 t
    rcases List.mem_append.mp (show p ∈ BT.toL s ++ BT.toL t from h) with h1 | h1
    · exact List.mem_append.mpr (Or.inl (ihs p h1 e he))
    · exact List.mem_append.mpr (Or.inr (iht p h1 e he))

/-- 添字 1 の節は `d0Args88` を変えない。 -/
theorem d0Args_D1_128 (c : BT) : d0Args88 (BT.D 1 c) = d0Args88 c := by
  show (if (1 : Nat) == 0 then c :: d0Args88 c else d0Args88 c) = _
  rw [if_neg (by exact Bool.noConfusion)]

/-- 段 0 の成分の引数は `d0Args88` の中。 -/
theorem mem_d0Args_of_toL128 {x d : BT} (h : BT.D 0 d ∈ BT.toL x) : d ∈ d0Args88 x :=
  d0Args_toL128 x (BT.D 0 d) h d
    (by show d ∈ (if (0 : Nat) == 0 then d :: d0Args88 d else d0Args88 d)
        rw [if_pos (by rfl)]
        exact List.Mem.head _)

/-- **名簿は §90.1 の `e` の中にある。**  `vebArgs128 a` の元は `a` のどこかの
    `ψ₀` の引数である。 -/
theorem vebArgs_sub_d0Args128 {a d : BT} (h : d ∈ vebArgs128 a) : d ∈ d0Args88 a := by
  rcases List.mem_append.mp h with h1 | h1
  · obtain ⟨c, hc, hd⟩ := mem_coefArgs104 h1
    exact d0Args_toL128 a (BT.D 1 c) hc d
      (by rw [d0Args_D1_128]; exact mem_d0Args_of_toL128 hd)
  · obtain ⟨p, hp, hdp⟩ := List.mem_flatMap.mp h1
    cases p with
    | zero => exact absurd hdp (by intro hcc; cases hcc)
    | sum _ _ => exact absurd hdp (by intro hcc; cases hcc)
    | D u c =>
      cases u with
      | zero => exact absurd hdp (by intro hcc; cases hcc)
      | succ u' =>
        cases u' with
        | succ _ => exact absurd hdp (by intro hcc; cases hcc)
        | zero =>
          obtain ⟨x, hx, hd⟩ := mem_coefArgs104 (show d ∈ coefArgs104 c from hdp)
          refine d0Args_toL128 a (BT.D 1 c) hp d ?_
          rw [d0Args_D1_128]
          exact d0Args_toL128 c (BT.D 1 x) hx d
            (by rw [d0Args_D1_128]; exact mem_d0Args_of_toL128 hd)

/-- **§90.1 の事実 (1) — `d < a`。**  `K` の条件だけで只で出る。 -/
theorem vebArgs_lt128 {a d : BT} (hs : BT.isStd (BT.D 0 a) = true) (h : d ∈ vebArgs128 a) :
    BT.lt d a = true :=
  (std0_split82 hs).2 d (d0Args_sub_GB0_90 a d (vebArgs_sub_d0Args128 h))

/-- **§90.1 の事実 (2) — `ψ₀ d` は標準。** -/
theorem vebArgs_isStd128 {a d : BT} (hs : BT.isStd a = true) (h : d ∈ vebArgs128 a) :
    BT.isStd (BT.D 0 d) = true :=
  isStd_d0Args_90 a hs d (vebArgs_sub_d0Args128 h)

/-- **§90.1 の事実 (3) — `d` も段 1 以下。** -/
theorem vebArgs_btLe128 {a d : BT} (hb : btLe72 1 a = true) (h : d ∈ vebArgs128 a) :
    btLe72 1 d = true :=
  btLe72_d0Args_90 a hb d (vebArgs_sub_d0Args128 h)

/-- **§90.1 の事実 (4) — `d` は真に小さい項。** -/
theorem vebArgs_size128 {a d : BT} (h : d ∈ vebArgs128 a) : BT.size d < BT.size a :=
  size_d0Args_90 a d (vebArgs_sub_d0Args128 h)


/-! ### §128.8 THE NEGATIVES -/

/-- **否定 1 — 条項は空虚に真ではない。**  §114 が組んだ反転 `revA114` の名簿は
    ちょうど一つ `ψ₁ψ₁ψ₁0` で、その `ψ₀` の値は `Γ₀` そのもの、的も `Γ₀` である。
    だから条項は破れ、`vebPair123` も**同じところで**破れる。`K` の条件はそこで偽で、
    §123 が「この証人に触れていない」と書いた場所を §128 は名指しできる。 -/
theorem revA_facts128 :
    (vebArgs128 revA114, BT.isStd (BT.D 0 revA114),
     (vebArgs128 revA114).all
       (fun d => lt (dict (BT.D 0 d)) (psi (reg 1) (jOf114 revB114))),
     vebPair123 (dict revA114) (psi (reg 1) (jOf114 revB114)))
    = ([w3_101], false, false, false) := rfl

/-- 組んだ肯定の証人 (a) — `ψ₁ψ₀ψ₁ψ₀0`、5 記号。 -/
def posA128 : BT := BT.D 1 (BT.D 0 (BT.D 1 (BT.D 0 BT.zero)))
/-- 組んだ肯定の証人 (b) — `ψ₁ψ₁ψ₁ψ₁0`。 -/
def posB128 : BT := w4_123

/-- **否定 2 — 条項は空虚に偽でもない。**  この `K` 標準の対は `VebD0_128` の仮定を
    すべて満たし、名簿は空でなく、条項も `vebPair123` も真である。 -/
theorem posA_facts128 :
    (btLe72 1 (BT.D 0 posA128), BT.isStd (BT.D 0 posA128), le (reg 1) (dict posA128),
     lastFire92 (dict posA128), lastFire92 (dict posB128), allFire101 (dict posB128),
     lt (hiW89 (dict posA128)) (hiW89 (dict posB128)), (vebArgs128 posA128).length,
     (vebArgs128 posA128).all
       (fun d => lt (dict (BT.D 0 d)) (psi (reg 1) (jOf114 posB128))),
     vebPair123 (dict posA128) (psi (reg 1) (jOf114 posB128)))
    = (true, true, true, false, true, true, true, 1, true, true) := rfl

end

/-! ### §128.9 THE MEASUREMENT -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

private def seed128 : List BT :=
  [w1_101, w2_101, w3_101, w4_123,
   BT.D 1 (BT.D 0 BT.zero), BT.D 1 w1_101, BT.D 0 (BT.D 1 w1_101),
   BT.D 1 (BT.D 0 w1_101), BT.D 1 (BT.sum w1_101 (BT.D 0 BT.zero)),
   BT.D 1 (BT.D 0 (BT.D 1 (BT.D 0 BT.zero))),
   BT.D 1 (BT.D 1 (BT.D 0 w3_101)), BT.D 1 (BT.D 1 (BT.D 0 w1_101)),
   BT.D 1 (BT.D 0 w3_101), BT.D 1 (BT.D 0 w2_101),
   revA114, revB114, sepRA114, sepRB114, scBadA101, scBadB101, sepA104]
private def dedup128 (l : List BT) : List BT :=
  l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
private def pop128 : List BT :=
  dedup128 (seed128
    ++ seed128.flatMap (fun a => (seed128.filter (fun b => BT.le b a)).map (BT.sum a))
    ++ seed128.map (BT.D 1))
private def ok128 (a : BT) : Bool := btLe72 1 a && BT.isStd a && le (reg 1) (dict a)
private def kstd128 (a : BT) : Bool := ok128 a && BT.isStd (BT.D 0 a)
private def samp128 : List BT := pop128.filter ok128
private def ksamp128 : List BT := pop128.filter kstd128
private def prs128 (l : List BT) : List (BT × BT) := l.flatMap (fun a => l.map (fun b => (a, b)))
/-- 残余 — `hi` が狭義に増え、`a` の最後の対が発火しない対。 -/
private def resid128 (l : List BT) : List (BT × BT) :=
  (prs128 l).filter (fun p => lt (hiW89 (dict p.1)) (hiW89 (dict p.2)) && !lastFire92 (dict p.1))
/-- そのうち `b` が全発火する半分 — `VebPairs123` の担当分。 -/
private def af128 (l : List BT) : List (BT × BT) :=
  (resid128 l).filter (fun p => allFire101 (dict p.2))
private def tgt128 (b : BT) : Term := psi (reg 1) (jOf114 b)
private def pairOK128 (p : BT × BT) : Bool := vebPair123 (dict p.1) (tgt128 p.2)
private def clause128 (p : BT × BT) : Bool :=
  (vebArgs128 p.1).all (fun d => lt (dict (BT.D 0 d)) (tgt128 p.2))
private def clauseAll128 (p : BT × BT) : Bool :=
  (d0Args88 p.1).all (fun d => lt (dict (BT.D 0 d)) (tgt128 p.2))
private def hasVeb128 (a : BT) : Bool :=
  (wcnf (reg 1) (toList (dict a))).1.any (fun ac => !le (reg 1) ac.1)

/-! **受領 1 — 母集団は形を持っている。**  219 項のうち形の条件を満たすのが 146 項、
    `K` 標準が 88 項、**名簿が空でないのが 118 項**、**非発火の対を実際に持つのが
    129 項**、最大 22 記号。名簿も非発火の対も、掃く前から母集団の中にある。 -/
#guard (pop128.length, samp128.length, ksamp128.length,
        samp128.countP (fun a => 0 < (vebArgs128 a).length),
        samp128.countP hasVeb128,
        (samp128.map BT.size).foldl max 0) == (219, 146, 88, 118, 129, 22)

/-! **受領 2 — 担当する半分は空でない。**  残余 10262 組のうち `b` が全発火するのは
    2029 組、`K` 標準では 3525 組のうち 1045 組。 -/
#guard ((resid128 samp128).length, (af128 samp128).length,
        (resid128 ksamp128).length, (af128 ksamp128).length) == (10262, 2029, 3525, 1045)

/-! **受領 3 — 翻訳は残余を動かしていない。**  `b` が全発火する 2029 組で
    `vebPair123` は 81 回破れ、**条項もちょうど同じ 81 回破れる** — 含意の破れ 0、
    逆向きの破れ 0。`K` 標準の 1045 組ではどちらも 0 回。 -/
#guard ((af128 samp128).countP (fun p => !pairOK128 p),
        (af128 samp128).countP (fun p => !clause128 p),
        (af128 samp128).countP (fun p => clause128 p && !pairOK128 p),
        (af128 samp128).countP (fun p => pairOK128 p && !clause128 p),
        (af128 ksamp128).countP (fun p => !pairOK128 p),
        (af128 ksamp128).countP (fun p => !clause128 p)) == (81, 81, 0, 0, 0, 0)

/-! **受領 4 — 定理は空虚な掃き出しではない。**  絞りなしの 21316 組で `vebPair123` は
    5570 回、条項は 5687 回破れ、**含意の破れは 0**。逆向きは 117 回破れる (発火する
    成分の引数まで名簿が拾うところ) から、**担当の半分の外では条項は真に強い**。
    §90.1 の `e` をぜんぶ (`d0Args88`) 取ると含意はやはり成り立つが逆向きは 1277 回
    破れる — **深さ 2 で止める名簿がその 10 倍の差である。** -/
#guard ((prs128 samp128).length,
        (prs128 samp128).countP (fun p => !pairOK128 p),
        (prs128 samp128).countP (fun p => !clause128 p),
        (prs128 samp128).countP (fun p => clause128 p && !pairOK128 p),
        (prs128 samp128).countP (fun p => pairOK128 p && !clause128 p),
        (prs128 samp128).countP (fun p => clauseAll128 p && !pairOK128 p),
        (prs128 samp128).countP (fun p => pairOK128 p && !clauseAll128 p))
  == (21316, 5570, 5687, 0, 117, 0, 1277)


/-! **受領 5 — 翻訳は只で一区画を買う。**  名簿が空な `a` — 添字 1 の成分の引数の中に
    深さ 2 まで `ψ₀` が一つも無いもの — は 146 項のうち 28 項で、全発火の半分 2029 組の
    うち **179 組** (`K` 標準では 1045 組のうち 162 組) がそこに入る。そこでは
    `vebPair_of_nil128` により `vebPair123` は**条項なしの定理**であり、実際その 179 組で
    一度も破れない。 -/
#guard ((af128 samp128).countP (fun p => (vebArgs128 p.1).isEmpty),
        (af128 ksamp128).countP (fun p => (vebArgs128 p.1).isEmpty),
        samp128.countP (fun a => (vebArgs128 a).isEmpty),
        (af128 samp128).countP (fun p => (vebArgs128 p.1).isEmpty && !pairOK128 p))
  == (179, 162, 28, 0)

end

/-! ## §129 THE RESIDUE OF `VebRest117` IS TWO `phiNF` FACTS, AND BOTH ARE THEOREMS

§117 left `VebRest117` — `ψ₀` monotone on the high parts, for the pairs its own tools do not
reach.  §129 reads that residue, names it, and closes it down to one clause whose premise
never fires anywhere reachable.

  §129.1  **THE LAST VEBLEN STEP, IN CLOSED FORM.**  When the last base-`Ω₁` pair does not
          fire, the accumulator IS that one step: `accW89 y = φ̄(A,X)` with `(A,X) =
          lastStep129 y` (`accW89_last129`).  `A` and `X` are 𝔗(M) terms below `M`
          (`lastStep_inT129`), by the same fold invariant §117.4 used for `foldVal117`.

  §129.2  **THE TWO `phiNF` FACTS.**  `phiMono129`: `X < Y ⟹ φ̄(A,X) < φ̄(A,Y)`.
          `phiInfl129`: `T < Y ⟹ T < φ̄(A,Y)`.  Neither mentions `dict`, `BT`, or the fold.
          Both are proved.  The work is the fixed-point re-count: `phiNF` returns its own
          argument on `FixSh129` heads, steps DOWN through `phiNFsucc`, and `phiNFsucc`'s
          step-down is exactly the predecessor, so `le_of_lt_succT129` puts `X` at or below
          it.  The one case that is not bookkeeping is `X = Y⊖1`: there the head of `Y` is a
          `φ̄(A,·)` fixed-point shape, and `phiNF_fixD129` says `φ̄(A,·)` stays strictly
          below the raw `φ` on `g ⊕ k` for such a `g`.

  §129.3  **TWO NEW ROUTES.**  `rt1_129` — the two last steps have the SAME exponent and
          `a`'s argument is strictly smaller (this is `phiMono129`'s shape, and §117.6's
          receipt 5 already said the leftover pairs all have equal head exponents).
          `rt2_129` — `a`'s value is already below `b`'s last argument (this is
          `phiInfl129`'s shape).  `closed129 = closed117 ∨ rt1 ∨ rt2`.

  §129.4  **THE BRIDGE.**  `vebRest_of129 : VebRest129 → VebRest117`, with NO extra clause:
          the two `phiNF` facts are theorems, not hypotheses.  `VebRest129` is `VebRest117`
          restricted to `closed129 a b = false`, so `VebRest117 → VebRest129` too
          (`vebRest126_of117`) — the clause is strictly narrower.

  §129.5  **WHAT THE MEASUREMENT SAYS, AND WHAT IT DOES NOT.**  Two populations: every
          `K`-standard level-≤1 term up to 9 symbols (278 with a non-firing last pair), and
          §117.6's coefficient direction (2-term sums).  `closed117` leaves 8139 residual
          pairs open on the first and 8525 on the second.  `closed129` leaves **0** on both.
          That is the honest limit of this file: **the premise of `VebRest129` never fires
          anywhere reachable, so `VebRest129` is NOT measured.**  What IS measured is where
          it sits: §81's `cexA89`/`cexB89` and §101's `bothBadA101`/`bothBadB101` satisfy
          **every** hypothesis of `VebRest129` except `BT.isStd (BT.D 0 a)`, are left open by
          `closed129`, and break the conclusion.  `K`-standardness of the LEFT term is the
          only thing carrying the clause.
-/


/-! ### §129.1 The last Veblen step, in closed form -/


section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 折り畳みの**最後の一歩** — (指数, `φ̄` の第二引数)。最後の対がなければ `none`。 -/
def lastStep129 (y : Term) : Option (Term × Term) :=
  match (wcnf (reg 1) (toList y)).1.reverse with
  | [] => none
  | ac :: r =>
      match (r.reverse.foldl (stepF (reg 1) (baseOf 0))
              ((none : Option Term), (none : Option Term))).2 with
      | none => some (ac.1, plus (baseOf 0) (sub1 ac.2))
      | some v => some (ac.1, plus v ac.2)

/-- **最後の対が発火しないなら、累算器は最後の一歩の `φ̄` そのもの。** -/
theorem accW89_last129 {y A X : Term} (hf : lastFire92 y = false)
    (h : lastStep129 y = some (A, X)) : accW89 y = phiNF A X := by
  unfold lastStep129 at h
  unfold lastFire92 at hf
  cases hr : (wcnf (reg 1) (toList y)).1.reverse with
  | nil => rw [hr] at h; dsimp only at h; exact absurd h (by simp)
  | cons ac r =>
      rw [hr] at h hf
      dsimp only at h hf
      have hsplit : (wcnf (reg 1) (toList y)).1 = r.reverse ++ [ac] := by
        have h2 := congrArg List.reverse hr
        rw [List.reverse_reverse, List.reverse_cons] at h2
        exact h2
      show ((wcnf (reg 1) (toList y)).1.foldl (init := ((none : Option Term),
              (none : Option Term))) (stepF (reg 1) (baseOf 0))).2.getD zero = _
      rw [hsplit, List.foldl_append]
      show ((stepF (reg 1) (baseOf 0)) (r.reverse.foldl (stepF (reg 1) (baseOf 0))
              ((none : Option Term), (none : Option Term))) ac).2.getD zero = _
      rw [stepF_snd_veb88 hf]
      cases hs2 : (r.reverse.foldl (stepF (reg 1) (baseOf 0))
          ((none : Option Term), (none : Option Term))).2 with
      | none =>
          rw [hs2] at h
          dsimp only at h ⊢
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1, ← h.2]; rfl
      | some v =>
          rw [hs2] at h
          dsimp only at h ⊢
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1, ← h.2]; rfl

/-- 前半だけ畳んだ状態も対の並びも 𝔗(M) の中 — §117.4 の `foldVal_inT117` を
    任意の分割で書いたもの。 -/
theorem preSt_inv129 {y : Term} (hy : inT y = true) (hly : lt y M = true) (Hp : PsiIdxOK 0 y)
    (l r : List (Term × Term)) (hsplit : l ++ r = (wcnf (reg 1) (toList y)).1) :
    StInv (l.foldl (stepF (reg 1) (baseOf 0)) ((none : Option Term), (none : Option Term)))
      ∧ (∀ ac ∈ l ++ r, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true
          ∧ lt ac.2 M = true) := by
  obtain ⟨hc, hd⟩ := inT_toList y hy
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList y) hc hd
    (ltM_toList y hy hly)
  have hall2 : ∀ ac ∈ l ++ r, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true
      ∧ lt ac.2 M = true := by rw [hsplit]; exact hallOK
  refine ⟨?_, hall2⟩
  exact fold_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0)
    _ (none, none) stInv_none (fun z hz => hall2 z (List.mem_append_left _ hz))
    (by
      intro p hp
      refine Hp p ?_
      rw [← hsplit, scanSt_append109]
      exact List.mem_append_left _ hp)

/-- 最後の一歩の二つの成分は 𝔗(M) の項で `M` の下。 -/
theorem lastStep_inT129 {y A X : Term} (hy : inT y = true) (hly : lt y M = true)
    (Hp : PsiIdxOK 0 y) (h : lastStep129 y = some (A, X)) :
    (inT A = true ∧ lt A M = true) ∧ (inT X = true ∧ lt X M = true) := by
  unfold lastStep129 at h
  cases hr : (wcnf (reg 1) (toList y)).1.reverse with
  | nil => rw [hr] at h; dsimp only at h; exact absurd h (by simp)
  | cons ac r =>
      rw [hr] at h
      dsimp only at h
      have hsplit : r.reverse ++ [ac] = (wcnf (reg 1) (toList y)).1 := by
        have h2 := congrArg List.reverse hr
        rw [List.reverse_reverse, List.reverse_cons] at h2
        exact h2.symm
      obtain ⟨hst, hall⟩ := preSt_inv129 hy hly Hp r.reverse [ac] hsplit
      have hac := hall ac (List.mem_append_right _ (List.Mem.head _))
      cases hs2 : (r.reverse.foldl (stepF (reg 1) (baseOf 0))
          ((none : Option Term), (none : Option Term))).2 with
      | none =>
          rw [hs2] at h; dsimp only at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1, ← h.2]
          exact ⟨⟨hac.1, hac.2.1⟩,
            ⟨inT_plus (inT_baseOf 0) (inT_sub1 hac.2.2.1),
             lt_plus_M (inT_baseOf 0) (inT_sub1 hac.2.2.1) (ltM_baseOf 0)
               (ltM_sub1 hac.2.2.1 hac.2.2.2)⟩⟩
      | some v =>
          rw [hs2] at h; dsimp only at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hiv, hvM⟩ := hst.2 v hs2
          rw [← h.1, ← h.2]
          exact ⟨⟨hac.1, hac.2.1⟩,
            ⟨inT_plus hiv hac.2.2.1, lt_plus_M hiv hac.2.2.1 hvM hac.2.2.2⟩⟩

end

/-! ### §129.2 `phiNF` is strictly monotone, and inflationary -/


section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1)
open TM TM.Term
open Evidence.WF

theorem le_of_lt_succT129 {x y : Term} (hx : inT x = true) (hy : inT y = true)
    (h : lt x (succT y) = true) : le x y = true := by
  by_cases hle : le x y = true
  · exact hle
  · exfalso
    have hlt : lt y x = true := lt_of_not_le_inT hx hy (bool_false hle)
    have hs2 : le (succT y) x = true := le_succT_of_lt_inT y hy x hx hlt
    have hcon := lt_of_le_of_lt3 (inT_le_fragR _ (inT_succT_inT hy)) (inT_le_fragR _ hx)
      (inT_le_fragR _ (inT_succT_inT hy)) hs2 h
    rw [lt_irrefl] at hcon
    exact Bool.noConfusion hcon

/-- `φ̄(A,·)` の**不動点の形**。 -/
def FixSh129 (A g : Term) : Prop :=
  (g.isSC = true ∧ lt A g = true) ∨ (∃ d e, g = phi d e ∧ lt A d = true)

theorem phiNF_fixSh129 {A g : Term} (h : FixSh129 A g) : phiNF A g = g := by
  rcases h with ⟨hsc, hlt⟩ | ⟨d, e, he, hlt⟩
  · unfold phiNF; rw [if_pos (by rw [hsc, hlt]; rfl)]
  · subst he
    unfold phiNF
    rw [if_neg (by rw [show (phi d e).isSC = false from rfl]; exact Bool.noConfusion)]
    show (if lt A d = true then phi d e else phiNFsucc A (phi d e)) = phi d e
    rw [if_pos hlt]

theorem phiNF_notFix129 {A Y : Term} (h : ¬ FixSh129 A Y) : phiNF A Y = phiNFsucc A Y := by
  unfold phiNF
  rw [if_neg (by
    intro hc
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hc
    exact h (Or.inl ⟨h1, h2⟩))]
  cases Y with
  | zero => rfl
  | M => rfl
  | omg _ => rfl
  | add _ _ => rfl
  | psi _ _ => rfl
  | Z _ => rfl
  | phi c d =>
      show (if lt A c = true then phi c d else phiNFsucc A (phi c d)) = phiNFsucc A (phi c d)
      rw [if_neg (by intro hc2; exact h (Or.inr ⟨c, d, rfl, hc2⟩))]

/-- 不動点の形の頭を持つ引数では `phiNFsucc` は必ず一段下がる。 -/
theorem phiNFsucc_val129 {A Y g : Term} {m : Nat} (hs : splitFin Y = (g, m)) (hm : m ≥ 1)
    (hfx : FixSh129 A g) : phiNFsucc A Y = phi A (plus g (ofNat (m - 1))) := by
  unfold phiNFsucc
  rw [hs]
  dsimp only
  rw [if_pos hm]
  rcases hfx with ⟨hsc, hlt⟩ | ⟨d, e, he, hlt⟩
  · cases g with
    | zero => exact absurd hsc Bool.noConfusion
    | omg _ => exact absurd hsc Bool.noConfusion
    | phi _ _ => exact absurd hsc Bool.noConfusion
    | add _ _ => exact absurd hsc Bool.noConfusion
    | M =>
        show (if (true && lt A M) = true then phi A (plus M (ofNat (m - 1)))
              else phiNFdefault A Y) = _
        rw [Bool.true_and, if_pos hlt]
    | psi p q =>
        show (if (true && lt A (psi p q)) = true then phi A (plus (psi p q) (ofNat (m - 1)))
              else phiNFdefault A Y) = _
        rw [Bool.true_and, if_pos hlt]
    | Z p =>
        show (if (true && lt A (Z p)) = true then phi A (plus (Z p) (ofNat (m - 1)))
              else phiNFdefault A Y) = _
        rw [Bool.true_and, if_pos hlt]
  · subst he
    show (if lt A d = true then phi A (plus (phi d e) (ofNat (m - 1)))
          else phiNFdefault A Y) = _
    rw [if_pos hlt]

/-- 不動点の形でない頭では `phiNFsucc` は既定の枝。 -/
theorem phiNFsucc_def129 {A Y g : Term} {m : Nat} (hs : splitFin Y = (g, m))
    (hfx : ¬ FixSh129 A g) : phiNFsucc A Y = phiNFdefault A Y := by
  unfold phiNFsucc
  rw [hs]
  dsimp only
  split
  · cases g with
    | zero =>
        show (if (false && lt A zero) = true then phi A (plus zero (ofNat (m - 1)))
              else phiNFdefault A Y) = _
        rw [Bool.false_and, if_neg Bool.noConfusion]
    | omg x =>
        show (if (false && lt A (omg x)) = true then phi A (plus (omg x) (ofNat (m - 1)))
              else phiNFdefault A Y) = _
        rw [Bool.false_and, if_neg Bool.noConfusion]
    | add x y =>
        show (if (false && lt A (add x y)) = true then phi A (plus (add x y) (ofNat (m - 1)))
              else phiNFdefault A Y) = _
        rw [Bool.false_and, if_neg Bool.noConfusion]
    | M =>
        show (if (true && lt A M) = true then phi A (plus M (ofNat (m - 1)))
              else phiNFdefault A Y) = _
        rw [Bool.true_and, if_neg (by intro hc; exact hfx (Or.inl ⟨rfl, hc⟩))]
    | psi p q =>
        show (if (true && lt A (psi p q)) = true then phi A (plus (psi p q) (ofNat (m - 1)))
              else phiNFdefault A Y) = _
        rw [Bool.true_and, if_neg (by intro hc; exact hfx (Or.inl ⟨rfl, hc⟩))]
    | Z p =>
        show (if (true && lt A (Z p)) = true then phi A (plus (Z p) (ofNat (m - 1)))
              else phiNFdefault A Y) = _
        rw [Bool.true_and, if_neg (by intro hc; exact hfx (Or.inl ⟨rfl, hc⟩))]
    | phi d e =>
        show (if lt A d = true then phi A (plus (phi d e) (ofNat (m - 1)))
              else phiNFdefault A Y) = _
        rw [if_neg (by intro hc; exact hfx (Or.inr ⟨d, e, rfl, hc⟩))]
  · rfl

theorem phiNFsucc_lo129 {A Y g : Term} {m : Nat} (hs : splitFin Y = (g, m))
    (hm : ¬ (m ≥ 1)) : phiNFsucc A Y = phiNFdefault A Y := by
  unfold phiNFsucc
  rw [hs]
  dsimp only
  rw [if_neg hm]

theorem succT_add129 : ∀ (W : Term), W ≠ zero → ∃ a b, succT W = add a b := by
  intro W hz
  cases W with
  | zero => exact absurd rfl hz
  | M => exact ⟨M, one, rfl⟩
  | omg x => exact ⟨omg x, one, rfl⟩
  | phi p q => exact ⟨phi p q, one, rfl⟩
  | psi p q => exact ⟨psi p q, one, rfl⟩
  | Z p => exact ⟨Z p, one, rfl⟩
  | add a b => exact ⟨a, succT b, rfl⟩

/-- **`φ̄` の正規化は生の `φ` を越えない。** -/
theorem phiNF_le_phi129 {A X : Term} (hiA : inT A = true) (hAM : lt A M = true)
    (hiX : inT X = true) (hXM : lt X M = true) : le (phiNF A X) (phi A X) = true := by
  have hiPT : ∀ Z : Term, inT Z = true → lt Z M = true → inT (phi A Z) = true :=
    fun Z hZ hZM => inT_phiT117 hiA hZ hAM hZM
  have hself : lt X (phi A X) = true :=
    lt_phi_of_le100 X.deg X A X (Nat.le_refl _) hiX hXM (hiPT X hiX hXM) (Or.inr (le_self X))
  have hAlt : lt A (phi A X) = true :=
    lt_phi_of_le100 A.deg A A X (Nat.le_refl _) hiA hAM (hiPT X hiX hXM) (Or.inl (le_self A))
  have hdef : le (phiNFdefault A X) (phi A X) = true := by
    unfold phiNFdefault
    split
    · exact le_of_lt hAlt
    · exact le_self _
  have hsucc : le (phiNFsucc A X) (phi A X) = true := by
    cases hs : splitFin X with
    | mk g m =>
      by_cases hm : m ≥ 1
      · by_cases hfx : FixSh129 A g
        · rw [phiNFsucc_val129 hs hm hfx]
          obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
          have hig : inT g = true := by
            have h0 := inT_splitFin hiX; rw [hs] at h0; exact h0
          have hreb : plus g (ofNat m) = X := by
            have h0 := splitFin_rebuild_inT X hiX; rw [hs] at h0; exact h0
          have hidn : inT (plus g (ofNat (m - 1))) = true := inT_plus hig (inT_ofNat _)
          have hmk : m - 1 = k := by omega
          have hXs : X = succT (plus g (ofNat (m - 1))) := by
            rw [hmk, ← hreb, hk]; exact plus_ofNat_step_inT hig k
          exact le_of_lt (lt_phi_arg (by rw [hXs]; exact lt_succT_inT _ hidn))
        · rw [phiNFsucc_def129 hs hfx]; exact hdef
      · rw [phiNFsucc_lo129 hs hm]; exact hdef
  by_cases hfx : FixSh129 A X
  · rw [phiNF_fixSh129 hfx]; exact le_of_lt hself
  · rw [phiNF_notFix129 hfx]; exact hsucc

/-- **不動点の形の上では `φ̄` は生の `φ` に届かない。** -/
theorem phiNF_fixD129 {A g : Term} (hiA : inT A = true) (hAM : lt A M = true)
    (hig : inT g = true) (hgM : lt g M = true)
    (hlast : ∀ a, ((toList g).reverse).head? = some a → (a == one) = false)
    (hgz : g ≠ zero) (hfx : FixSh129 A g) : ∀ k : Nat,
    lt (phiNF A (plus g (ofNat k))) (phi A (plus g (ofNat k))) = true := by
  intro k
  have hiPT : ∀ Z : Term, inT Z = true → lt Z M = true → inT (phi A Z) = true :=
    fun Z hZ hZM => inT_phiT117 hiA hZ hAM hZM
  cases k with
  | zero =>
      show lt (phiNF A g) (phi A g) = true
      rw [phiNF_fixSh129 hfx]
      exact lt_phi_of_le100 g.deg g A g (Nat.le_refl _) hig hgM (hiPT g hig hgM)
        (Or.inr (le_self g))
  | succ j =>
      have hiW : inT (plus g (ofNat j)) = true := inT_plus hig (inT_ofNat j)
      have hWz : plus g (ofNat j) ≠ zero := by
        intro hc
        have h0 : toList g ++ List.replicate j one = ([] : List Term) := by
          rw [← toList_plus_ofNat_inT hig j, hc]; exact rfl
        cases hgl : toList g with
        | nil => exact toList_ne_nil_inT hgz hgl
        | cons x t => rw [hgl] at h0; simp at h0
      have hDs : plus g (ofNat (j + 1)) = succT (plus g (ofNat j)) := plus_ofNat_step_inT hig j
      obtain ⟨p, q, hadd⟩ := succT_add129 _ hWz
      have hDadd : plus g (ofNat (j + 1)) = add p q := by rw [hDs, hadd]
      have hsplitD : splitFin (plus g (ofNat (j + 1))) = (g, j + 1) :=
        splitFin_plus_ofNat79 hig hlast (j + 1)
      have hnf : ¬ FixSh129 A (plus g (ofNat (j + 1))) := by
        rw [hDadd]
        rintro (⟨hsc, _⟩ | ⟨d, e, he, _⟩)
        · exact Bool.noConfusion hsc
        · exact Term.noConfusion he
      have hval : phiNF A (plus g (ofNat (j + 1))) = phi A (plus g (ofNat j)) := by
        rw [phiNF_notFix129 hnf, phiNFsucc_val129 hsplitD (by omega) hfx]
        exact rfl
      rw [hval]
      exact lt_phi_arg (by rw [hDs]; exact lt_succT_inT _ hiW)

/-- **条項 1 は定理。**  `φ̄(A,·)` は第二引数について狭義単調。 -/
theorem phiMono129 : ∀ (A X Y : Term), inT A = true → lt A M = true → inT X = true →
    lt X M = true → inT Y = true → lt Y M = true → lt X Y = true →
    lt (phiNF A X) (phiNF A Y) = true := by
  intro A X Y hiA hAM hiX hXM hiY hYM hXY
  have hiPT : ∀ Z : Term, inT Z = true → lt Z M = true → inT (phi A Z) = true :=
    fun Z hZ hZM => inT_phiT117 hiA hZ hAM hZM
  have hiPX : inT (phiNF A X) = true := inT_phiNF hiA hiX hAM hXM
  have hleX : le (phiNF A X) (phi A X) = true := phiNF_le_phi129 hiA hAM hiX hXM
  have key : ∀ D : Term, inT D = true → lt D M = true → le X D = true →
      lt (phiNF A D) (phi A D) = true → lt (phiNF A X) (phi A D) = true := by
    intro D hiD hDM hXD hfix
    rcases (Bool.or_eq_true _ _).mp hXD with he | hlt
    · rw [← eq_of_beq he] at hfix ⊢; exact hfix
    · exact lt_of_le_of_lt3 (inT_le_fragR _ hiPX) (inT_le_fragR _ (hiPT X hiX hXM))
        (inT_le_fragR _ (hiPT D hiD hDM)) hleX (lt_phi_arg hlt)
  have hdefY : lt (phiNF A X) (phiNFdefault A Y) = true := by
    unfold phiNFdefault
    split
    · rename_i hh
      have hz : Y = zero := eq_of_beq ((Bool.and_eq_true _ _).mp hh).1
      rw [hz, lt_zero_right] at hXY; exact absurd hXY Bool.noConfusion
    · exact lt_of_le_of_lt3 (inT_le_fragR _ hiPX) (inT_le_fragR _ (hiPT X hiX hXM))
        (inT_le_fragR _ (hiPT Y hiY hYM)) hleX (lt_phi_arg hXY)
  have hsuccY : lt (phiNF A X) (phiNFsucc A Y) = true := by
    cases hs : splitFin Y with
    | mk g m =>
      by_cases hm : m ≥ 1
      · by_cases hfx : FixSh129 A g
        · rw [phiNFsucc_val129 hs hm hfx]
          obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
          have hig : inT g = true := by
            have h0 := inT_splitFin hiY; rw [hs] at h0; exact h0
          have hgM : lt g M = true := by
            have h0 := ltM_splitFin hiY hYM; rw [hs] at h0; exact h0
          have hreb : plus g (ofNat m) = Y := by
            have h0 := splitFin_rebuild_inT Y hiY; rw [hs] at h0; exact h0
          have hlast := splitFin_fst_last79 hiY hs
          have hidn : inT (plus g (ofNat (m - 1))) = true := inT_plus hig (inT_ofNat _)
          have hdnM : lt (plus g (ofNat (m - 1))) M = true :=
            lt_plus_M hig (inT_ofNat _) hgM (ltM_ofNat _)
          have hmk : m - 1 = k := by omega
          have hYs : Y = succT (plus g (ofNat (m - 1))) := by
            rw [hmk, ← hreb, hk]; exact plus_ofNat_step_inT hig k
          have hle : le X (plus g (ofNat (m - 1))) = true :=
            le_of_lt_succT129 hiX hidn (by rw [← hYs]; exact hXY)
          have hgz : g ≠ zero := by
            rcases hfx with ⟨hsc, _⟩ | ⟨d, e, he, _⟩
            · intro hc; rw [hc] at hsc; exact Bool.noConfusion hsc
            · rw [he]; intro hc; exact Term.noConfusion hc
          exact key _ hidn hdnM hle (phiNF_fixD129 hiA hAM hig hgM hlast hgz hfx (m - 1))
        · rw [phiNFsucc_def129 hs hfx]; exact hdefY
      · rw [phiNFsucc_lo129 hs hm]; exact hdefY
  by_cases hfY : FixSh129 A Y
  · rw [phiNF_fixSh129 hfY]
    rcases hfY with ⟨hsc, hAY⟩ | ⟨c, d, hcd, hAc⟩
    · cases Y with
      | zero => exact absurd hsc Bool.noConfusion
      | omg _ => exact absurd hsc Bool.noConfusion
      | phi _ _ => exact absurd hsc Bool.noConfusion
      | add _ _ => exact absurd hsc Bool.noConfusion
      | M =>
          exact lt_phiNF_wk117 rfl (by intro hc; exact Term.noConfusion hc)
            (inT_le_fragR _ hiY) hiX lt_one_M (fun q _ => lt_phi_M A q) hAY hXY
      | psi k c =>
          exact lt_phiNF_wk117 rfl (by intro hc; exact Term.noConfusion hc)
            (inT_le_fragR _ hiY) hiX (lt_one_psi95 k c)
            (fun q hq => lt_phi_psi_of hAY hq) hAY hXY
      | Z d =>
          exact lt_phiNF_wk117 rfl (by intro hc; exact Term.noConfusion hc)
            (inT_le_fragR _ hiY) hiX
            (lt_phi_Z_of (lt_zero_left (by intro hc; exact Term.noConfusion hc))
              (lt_zero_left (by intro hc; exact Term.noConfusion hc)))
            (fun q hq => lt_phi_Z_of hAY hq) hAY hXY
    · subst hcd
      have hcz : c ≠ zero := by
        intro hc; rw [hc, lt_zero_right] at hAc; exact Bool.noConfusion hAc
      have hAY : lt A (phi c d) = true :=
        lt_phi_of_le100 A.deg A c d (Nat.le_refl _) hiA hAM hiY (Or.inl (le_of_lt hAc))
      exact lt_phiNF_wk117 rfl (by intro hc; exact Term.noConfusion hc)
        (inT_le_fragR _ hiY) hiX
        (by rw [show one = phi zero zero from rfl, lt_phi_vT117 (lt_zero_left hcz)]
            exact lt_zero_left (by intro hc; exact Term.noConfusion hc))
        (fun q hq => by rw [lt_phi_vT117 hAc]; exact hq) hAY hXY
  · rw [phiNF_notFix129 hfY]; exact hsuccY

end


section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1)
open TM TM.Term
open Evidence.WF

/-- **条項 2 は定理。**  `φ̄(A,Y)` は `Y` より下のものを越える。 -/
theorem phiInfl129 : ∀ (A T Y : Term), inT A = true → lt A M = true → inT T = true →
    lt T M = true → inT Y = true → lt Y M = true → lt T Y = true →
    lt T (phiNF A Y) = true := by
  intro A T Y hiA hAM hiT hTM hiY hYM hTY
  have hiPT : ∀ Z : Term, inT Z = true → lt Z M = true → inT (phi A Z) = true :=
    fun Z hZ hZM => inT_phiT117 hiA hZ hAM hZM
  have hdef : lt T (phiNFdefault A Y) = true := by
    unfold phiNFdefault
    split
    · rename_i hh
      have hz : Y = zero := eq_of_beq ((Bool.and_eq_true _ _).mp hh).1
      rw [hz, lt_zero_right] at hTY; exact absurd hTY Bool.noConfusion
    · exact lt_trans_inT hiT hiY (hiPT Y hiY hYM) hTY
        (lt_phi_of_le100 Y.deg Y A Y (Nat.le_refl _) hiY hYM (hiPT Y hiY hYM)
          (Or.inr (le_self Y)))
  have hsucc : lt T (phiNFsucc A Y) = true := by
    unfold phiNFsucc
    cases hs : splitFin Y with
    | mk g m =>
      dsimp only
      split
      · rename_i hm
        have hig : inT g = true := by
          have h0 := inT_splitFin hiY; rw [hs] at h0; exact h0
        have hgM : lt g M = true := by
          have h0 := ltM_splitFin hiY hYM; rw [hs] at h0; exact h0
        have hreb : plus g (ofNat m) = Y := by
          have h0 := splitFin_rebuild_inT Y hiY; rw [hs] at h0; exact h0
        obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        have hidn : inT (plus g (ofNat k)) = true := inT_plus hig (inT_ofNat k)
        have hdnM : lt (plus g (ofNat k)) M = true :=
          lt_plus_M hig (inT_ofNat k) hgM (ltM_ofNat k)
        have hY : Y = succT (plus g (ofNat k)) := by
          rw [← hreb, hk, plus_ofNat_step_inT hig k]
        have hle : le T (plus g (ofNat k)) = true :=
          le_of_lt_succT129 hiT hidn (by rw [← hY]; exact hTY)
        have hlt : lt T (phi A (plus g (ofNat k))) = true :=
          lt_phi_of_le100 T.deg T A (plus g (ofNat k)) (Nat.le_refl _) hiT hTM
            (hiPT _ hidn hdnM) (Or.inr hle)
        have hmk : m - 1 = k := by omega
        rw [hmk]
        split
        · split
          · exact hlt
          · exact hdef
        · split
          · exact hlt
          · exact hdef
      · exact hdef
  unfold phiNF
  split
  · exact hTY
  · split
    · split
      · exact hTY
      · exact hsucc
    · exact hsucc

end

/-! ### §129.3 Two new routes and the wider decision procedure -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- **経路 1** — 最後の一歩の指数が等しく、第二引数が狭義に小さい。§129.2 の
    `phiMono129` の形。 -/
def rt1_129 (a b : BT) : Bool :=
  match lastStep129 (dict a), lastStep129 (dict b) with
  | some pa, some pb => (pa.1 == pb.1) && lt pa.2 pb.2
  | _, _ => false

/-- **経路 2** — `a` の値そのものが `b` の最後の一歩の第二引数より狭義に小さい。
    §129.2 の `phiInfl129` の形。 -/
def rt2_129 (a b : BT) : Bool :=
  match lastStep129 (dict b) with
  | some pb => lt (accW89 (dict a)) pb.2
  | none => false

/-- **§117 の道具に二本足したもの。** -/
def closed129 (a b : BT) : Bool := closed117 a b || rt1_129 a b || rt2_129 a b

theorem closed126_of117 {a b : BT} (h : closed117 a b = true) : closed129 a b = true := by
  unfold closed129; rw [h]; rfl

end

/-! ### §129.4 The bridge -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- `dict a` が 𝔗(M) の項で `M` の下、そして `PsiIdxOK`。 -/
private theorem dictFacts129 (Hp : PsiIdxOKStd172) {a : BT}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hsA : BT.isStd (BT.D 0 a) = true) :
    inT (dict a) = true ∧ lt (dict a) M = true ∧ PsiIdxOK 0 (dict a) := by
  have hba := (btLe72_D 1 0 a hbA).2
  have hia := inT_dict_of_std172 Hp a hba (isStd_of_D hsA)
  exact ⟨hia.1, hia.2, Hp 0 a (by omega) hba hsA⟩

/-- **経路 1 が閉じる。**  両方の累算器が同じ指数の `φ̄` で、第二引数が狭義に小さい。 -/
theorem hiMono_rt1_129 (Hp : PsiIdxOKStd172) {a b : BT}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hbB : btLe72 1 (BT.D 0 b) = true)
    (hsA : BT.isStd (BT.D 0 a) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (hWa : le (reg 1) (dict a) = true) (hWb : le (reg 1) (dict b) = true)
    (hfa : lastFire92 (dict a) = false) (hfb : lastFire92 (dict b) = false)
    (h : rt1_129 a b = true) :
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true := by
  obtain ⟨hia, hlaM, hpa⟩ := dictFacts129 Hp hbA hsA
  obtain ⟨hib, hlbM, hpb⟩ := dictFacts129 Hp hbB hsB
  rw [collapse0_hi89 (dict a) hia hlaM hpa hWa, collapse0_hi89 (dict b) hib hlbM hpb hWb]
  unfold rt1_129 at h
  cases hla : lastStep129 (dict a) with
  | none => rw [hla] at h; exact absurd h (by cases lastStep129 (dict b) <;> simp)
  | some pa =>
      cases hlb : lastStep129 (dict b) with
      | none => rw [hla, hlb] at h; exact absurd h (by simp)
      | some pb =>
          rw [hla, hlb] at h
          dsimp only at h
          obtain ⟨heq, hlt⟩ := (Bool.and_eq_true _ _).mp h
          have hA := eq_of_beq heq
          have ha2 : accW89 (dict a) = phiNF pa.1 pa.2 :=
            accW89_last129 hfa (by rw [hla])
          have hb2 : accW89 (dict b) = phiNF pa.1 pb.2 := by
            rw [hA]; exact accW89_last129 hfb (by rw [hlb])
          obtain ⟨hAf, hXf⟩ := lastStep_inT129 hia hlaM hpa (show lastStep129 (dict a)
            = some (pa.1, pa.2) from by rw [hla])
          obtain ⟨_, hYf⟩ := lastStep_inT129 hib hlbM hpb (show lastStep129 (dict b)
            = some (pb.1, pb.2) from by rw [hlb])
          rw [ha2, hb2]
          exact phiMono129 pa.1 pa.2 pb.2 hAf.1 hAf.2 hXf.1 hXf.2 hYf.1 hYf.2 hlt

/-- **経路 2 が閉じる。**  `a` の値が `b` の最後の一歩の第二引数より下なら、
    その一歩の `φ̄` はそれを越える。 -/
theorem hiMono_rt2_129 (Hp : PsiIdxOKStd172) {a b : BT}
    (hbA : btLe72 1 (BT.D 0 a) = true) (hbB : btLe72 1 (BT.D 0 b) = true)
    (hsA : BT.isStd (BT.D 0 a) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (hWa : le (reg 1) (dict a) = true) (hWb : le (reg 1) (dict b) = true)
    (hfb : lastFire92 (dict b) = false)
    (h : rt2_129 a b = true) :
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true := by
  obtain ⟨hia, hlaM, hpa⟩ := dictFacts129 Hp hbA hsA
  obtain ⟨hib, hlbM, hpb⟩ := dictFacts129 Hp hbB hsB
  rw [collapse0_hi89 (dict a) hia hlaM hpa hWa, collapse0_hi89 (dict b) hib hlbM hpb hWb]
  obtain ⟨hTi, hTW, _, _, _⟩ := accW89_facts (dict a) hia hlaM hpa hWa
  have hTM : lt (accW89 (dict a)) M = true :=
    lt_trans_inT hTi (inT_reg 1) inT_M hTW (ltM_reg 1)
  unfold rt2_129 at h
  cases hlb : lastStep129 (dict b) with
  | none => rw [hlb] at h; exact absurd h (by simp)
  | some pb =>
      rw [hlb] at h
      dsimp only at h
      have hb2 : accW89 (dict b) = phiNF pb.1 pb.2 :=
        accW89_last129 hfb (by rw [hlb])
      obtain ⟨hBf, hYf⟩ := lastStep_inT129 hib hlbM hpb (show lastStep129 (dict b)
        = some (pb.1, pb.2) from by rw [hlb])
      rw [hb2]
      exact phiInfl129 pb.1 (accW89 (dict a)) pb.2 hBf.1 hBf.2 hTi hTM hYf.1 hYf.2 h

/-- **三本合わせた道具が閉じる。** -/
theorem hiMono_closed129 (Hp : PsiIdxOKStd172)
    {a b : BT} (hbA : btLe72 1 (BT.D 0 a) = true) (hbB : btLe72 1 (BT.D 0 b) = true)
    (hsA : BT.isStd (BT.D 0 a) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (hWa : le (reg 1) (dict a) = true) (hWb : le (reg 1) (dict b) = true)
    (hfa : lastFire92 (dict a) = false) (hfb : lastFire92 (dict b) = false)
    (h : closed129 a b = true) :
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true := by
  unfold closed129 at h
  rcases (Bool.or_eq_true _ _).mp h with h1 | h2
  · rcases (Bool.or_eq_true _ _).mp h1 with h3 | h4
    · exact hiMono_closed117 Hp hbA hbB hsA hsB hWa hWb h3
    · exact hiMono_rt1_129 Hp hbA hbB hsA hsB hWa hWb hfa hfb h4
  · exact hiMono_rt2_129 Hp hbA hbB hsA hsB hWa hWb hfb h2

/-- **`VebRest117` の残り — 三本の道具が届かない組だけ。** -/
def VebRest129 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lastFire92 (dict a) = false → lastFire92 (dict b) = false →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    closed129 a b = false →
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true

/-- **§129 の主定理 — `VebRest117` を狭い条項ひとつに架け替える。**  余分な仮定は無い。 -/
theorem vebRest_of129 (Hp : PsiIdxOKStd172) (H : VebRest129) : VebRest117 := by
  intro a b hbA hbB hsA hsB hWa hWb hfa hfb hlt _
  cases hcl : closed129 a b with
  | true => exact hiMono_closed129 Hp hbA hbB hsA hsB hWa hWb hfa hfb hcl
  | false => exact H a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hcl

/-- **残る条項は真に狭い。**  `closed129` が偽なら `closed117` も偽。 -/
theorem vebRest126_of117 (H : VebRest117) : VebRest129 := by
  intro a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hcl
  refine H a b hbA hbB hsA hsB hWa hWb hfa hfb hlt ?_
  cases hc : closed117 a b with
  | false => rfl
  | true => rw [closed126_of117 hc] at hcl; exact Bool.noConfusion hcl

/-- **`HiMono89` を架け替える。** -/
theorem hiMono_of_four129 (Hp : PsiIdxOKStd172) (HA : IdxMono101) (HB : IdxLeMix109)
    (H1 : VebIngF114) (H2 : VebRest129) : HiMono89 :=
  hiMono_of_four117 Hp HA HB H1 (vebRest_of129 Hp H2)

/-- **326 行目を架け替える。** -/
theorem certIn_t326_129 (Hp : PsiIdxOKStd172) (HA : IdxMono101) (HB : IdxLeMix109)
    (H1 : VebIngF114) (H2 : VebRest129)
    (HD1 : DictOntoMidOpen103) (HD3 : DictDenseMid107) (HD4 : DictDenseAbove107)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_117 Hp HA HB H1 (vebRest_of129 Hp H2) HD1 HD3 HD4 hacc

end

/-! ### §129.5 Measurement (frozen)

**母集団 1 — 段 1 以下の項を記号数で総当たり。**  `K` 標準で `dict` が `Ω₁` 以上、
最後の対が発火しないもの。濾さない。
**母集団 2 — §117.6 の係数の方向。**  母集団 1 の 6 記号までを 2 項和で広げたもの。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1)
open TM TM.Term
open Evidence.WF

private def stepL129 (acc : List (List BT)) : List (List BT) :=
  let n := acc.length + 1
  let getS : Nat → List BT := fun k => if k == 0 then [] else acc.getD (k-1) []
  let ds := (getS (n-1)).flatMap (fun a => [BT.D 0 a, BT.D 1 a])
  let sums := (List.range (n-1)).flatMap (fun i =>
      let p := i + 1
      let q := n - 1 - p
      ((getS p).filter BT.isP).flatMap (fun a => (getS q).map (fun b => BT.sum a b)))
  acc ++ [(ds ++ sums).filter BT.isStd]
private def layers129 (n : Nat) : List (List BT) :=
  (List.range n).foldl (fun acc _ => stepL129 acc) [[BT.zero]]
private def okK129 (a : BT) : Bool :=
  btLe72 1 (BT.D 0 a) && BT.isStd (BT.D 0 a) && le (reg 1) (dict a)
private def hot129 (a : BT) : Bool := okK129 a && !lastFire92 (dict a)
private def poolAt129 (n : Nat) : List (List BT) :=
  (layers129 n).map (fun l => l.filter okK129)
private def hotL129 (n : Nat) : List BT :=
  ((layers129 n).map (fun l => l.filter hot129)).flatMap id
private def dedup129 (l : List BT) : List BT :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []
private def widen129 (l : List BT) : List BT :=
  dedup129 (l ++ l.flatMap (fun a => (l.filter (fun b => BT.le b a)).map (BT.sum a)))
private structure Rec126 where
  t  : BT
  sz : Nat
  wn : Nat
  hi : Term
  cv : Term
private def mkRec129 (a : BT) : Rec126 :=
  let y := dict a
  { t := a, sz := BT.size a, wn := (wcnf (reg 1) (toList y)).1.length,
    hi := hiW89 y, cv := collapse 0 (hiW89 y) }
private def recs129 : List Rec126 := (hotL129 8).map mkRec129
private def resid129 (l : List Rec126) : List (Rec126 × Rec126) :=
  (l.flatMap (fun a => l.map (fun b => (a, b)))).filter (fun p => lt p.1.hi p.2.hi)
private def rowOf129 (l : List Rec126) : Nat × Nat × Nat × Nat × Nat × Nat :=
  let R := resid129 l
  let O := R.filter (fun p => !closed117 p.1.t p.2.t)
  (l.length, R.length, O.length,
   R.countP (fun p => !closed129 p.1.t p.2.t),
   R.countP (fun p => !lt p.1.cv p.2.cv),
   O.countP (fun p => rt1_129 p.1.t p.2.t))
private def sizedRows129 : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  (List.range 10).map (fun N => rowOf129 (recs129.filter (fun r => r.sz ≤ N)))
private def census129 : (Nat × Nat × Nat) × (Nat × Nat × Nat) :=
  let R := resid129 recs129
  let O := R.filter (fun p => !closed117 p.1.t p.2.t)
  ((R.countP (fun p => p.1.wn < p.2.wn), R.countP (fun p => p.1.wn == p.2.wn),
    R.countP (fun p => p.1.wn > p.2.wn)),
   (O.countP (fun p => p.1.wn < p.2.wn), O.countP (fun p => p.1.wn == p.2.wn),
    O.countP (fun p => p.1.wn > p.2.wn)))
private def coefRow129 : Nat × Nat × Nat × Nat × Nat × Nat :=
  rowOf129 (((widen129 (hotL129 5)).filter hot129).map mkRec129)
private def hypsOf129 (a b : BT) : List Bool :=
  [btLe72 1 (BT.D 0 a), btLe72 1 (BT.D 0 b), BT.isStd (BT.D 0 a), BT.isStd (BT.D 0 b),
   le (reg 1) (dict a), le (reg 1) (dict b), !lastFire92 (dict a), !lastFire92 (dict b),
   lt (hiW89 (dict a)) (hiW89 (dict b)), !closed129 a b,
   lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b)))]

/-! **母集団の形。**  記号数 1..9 の `K` 標準な項は 0,1,2,4,8,19,44,102,233 個。 -/
#guard ((poolAt129 8).map List.length) == [0, 1, 2, 4, 8, 19, 44, 102, 233]

/-! **受領 1 — 記号数ごとの数。**  各行は (項数, 残余の組, `closed117` が外す組,
    `closed129` が外す組, 結論を破る組, 外した組のうち経路 1 が閉じる分)。
    **`closed129` が外す組は 0、結論を破る組も 0。** -/
#guard sizedRows129 == [(0, 0, 0, 0, 0, 0), (0, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0),
  (3, 3, 1, 0, 0, 1), (6, 15, 6, 0, 0, 6), (12, 65, 27, 0, 0, 27), (27, 343, 117, 0, 0, 115),
  (59, 1686, 513, 0, 0, 503), (128, 8048, 2106, 0, 0, 2062), (278, 38262, 8139, 0, 0, 7959)]

/-! **受領 2 — 残余は三つの形をぜんぶ持っている。**  `a` の対の数が `b` より少ない・
    等しい・多いの三通りが母集団に出る。§117 が外すのは前の二つだけで、
    「`a` の方が長い」組は §117 が全部閉じている。 -/
#guard census129 == ((7820, 28545, 1897), (180, 7959, 0))

/-! **受領 3 — 係数の方向でも 0。**  §117.6 の広げ方 (2 項和) で作った母集団。 -/
#guard coefRow129 == (336, 56139, 8525, 0, 0, 8248)

/-! **受領 4 — 新しい二本は §117 が届かないところに届く。**  §117.5 の `restA117`/
    `restB117` は `closed117` が偽、`closed129` が真 (経路 1)。 -/
#guard (closed117 restA117 restB117, closed129 restA117 restB117,
        rt1_129 restA117 restB117, rt2_129 restA117 restB117) == (false, true, true, false)

/-! **受領 5 — 残る条項がどこに座っているか。**  §81 の `cexA89`/`cexB89` と §101 の
    `bothBadA101`/`bothBadB101` は `VebRest129` の仮定を**左辺の `K` 標準性以外ぜんぶ**
    満たし、`closed129` も外し、**結論を破る**。並びは
    `[btLe72 a, btLe72 b, K a, K b, Ω₁≤dict a, Ω₁≤dict b, ¬fire a, ¬fire b, hi<hi,
      ¬closed129, 結論]`。 -/
#guard (hypsOf129 cexA89 cexB89, hypsOf129 bothBadA101 bothBadB101)
  == ([true, true, false, true, true, true, true, true, true, true, false],
      [true, true, false, true, true, true, true, true, true, true, false])

end

/-
g126f.lean — §130: an attack on the FIRST gate, `PsiIdxOKStd172`.
-/


/-! ## §130 THE FIRST GATE IS FALSE THE MOMENT `BT.isStd` IS DROPPED — AND WHAT IS LEFT
       OF IT LIVES ONLY AT `u = 0` ON ARGUMENTS THAT CARRY A LEVEL-ONE NODE

`PsiIdxOKStd172` (§72.8) has been used by every conditional result in
`Evidence/RegionNext3`–`RegionNext7` and has only ever been MEASURED.  §130 attacks it.

WHAT IS PROVED, UNCONDITIONALLY.

  §130.1  **DROPPING `BT.isStd` MAKES THE GATE FALSE AT LEVEL ≤ 1.**

               min130 = ψ₁ψ₁ψ₁(ψ₀(ψ₁ψ₁ψ₁ψ₁0))          `BT` の大きさ 9

           satisfies `btLe72 1 min130` and `BT.isStd min130`, and

               not_psiIdxOK_min130 : ¬ PsiIdxOK 0 (dict min130)

           so `not_psiIdxOK_le1_130` refutes `PsiIdxOKStd172` with the `BT.isStd` clause
           removed.  §66's counterexample `badArg` needed index 3, so it says nothing about
           the level-one sub-region; §73's `wKOK73` breaks only the `K`-transport
           `KOK73`, not the gate.  **This is the first refutation of the gate itself inside
           the sub-region.**  What saves `PsiIdxOKStd172` is exactly one Boolean:
           `BT.isStd (BT.D 0 min130) = false`, while `BT.isStd min130 = true`.

           THE MECHANISM.  Once `z`'s own fold fires, `dict (ψ₀ z)` is `ψ_{Ω₁}(β)` itself,
           with `β = dict z` at or ABOVE `Ω₁` — the smallest such `z` is `ψ₁ψ₁ψ₁ψ₁0`.  That
           `ψ_{Ω₁}(β)` is below `Ω₁`, so it rides in the low half of the `ψ₁`-exponent, and
           `mulL` copies it verbatim into the emitted index.  For `min130` the emitted index
           is `dict min130` itself; `K_{Ω₁}` of it is `{β}`; and `dict min130` is `β`'s own
           tower with `Ω₁` replaced by the strictly smaller `ψ_{Ω₁}(β)`, so `β > i` and
           2.1(vi)'s last conjunct fails.  Nothing here needs an index above 1.  Buchholz's
           `G(a,0) < a` is exactly the condition that caps `β`, which is why
           `BT.isStd (BT.D 0 min130)` is the one Boolean that is false.

  §130.2  **ON LEVEL-ZERO ARGUMENTS THE GATE IS A THEOREM.**  `pure0130` is §73's `pure73`
           with `Z` removed altogether; `lt_pure0126_reg1` says such a term is below `Ω₁`;
           `pure0126_dict` says the image of a `btLe72 0` tree stays there.  Hence
           `wcnf_reg1_nil130`: at `u = 0` the base-`Ω₁` decomposition of such an image
           returns NO pairs, so

               psiIdxOK_zero130 : btLe72 0 a → PsiIdxOK 0 (dict a)

           with no hypothesis at all — `BT.isStd` included.  With §73.4's `u = 1` half
           (restated as `psiIdxOK_one130`, now through `psiIdxOK_of_noSC`, so it does not
           pass through `inT`), this gives

               psiIdxOKStd172_of_lvl1_130 :
                 (∀ a, btLe72 1 a → btLe72 0 a = false → BT.isStd (ψ₀ a) → PsiIdxOK 0 (dict a))
                 → PsiIdxOKStd172

           **The gate now quantifies over `u = 0` and arguments that really carry a
           level-one node.**  `lvl1_of_psiIdxOKStd172_130` records that this is a split and
           not a weakening.

  §130.3  **THE SWEEP, WITH ITS SPLIT.**  Every level-≤1 tree by SIZE, not by width.
           Without `BT.isStd` the first failure is at size 9 (one of 4862), then 3 at size
           10 and 30 at size 11.  With `BT.isStd (BT.D 0 ·)` there is no failure through
           size 15 (40 381 trees at that size alone).  **And the sweep is not idle**: the
           number of standard trees whose firing step emits an index with a NON-EMPTY
           `K_{Ω₁}` — the only place 2.1(vi)'s last conjunct can say anything — is
           1, 2, 7, 28, 91, 273, 838, 2494 at sizes 8…15.  §72's `btPool72` has 378 firing
           steps and ZERO of them: that sweep never touched the conjunct at all.  The two
           branches that broke other clauses in this file are live here too — `wcnf`'s
           coefficient MERGING on 1398 of the 29 338 standard trees of size ≤ 14, and a
           SECOND firing step (so `idxOf` runs `plus i0 …`) on 270 of them.

WHAT IS NOT CLAIMED.  The gate itself is NOT refuted and NOT proved.  Every counterexample
found here is caught by `BT.isStd (BT.D 0 ·)`.  §130.3's sweep is a sweep, and this file
has been wrong four times about sweeps; what it is worth is the SPLIT recorded there, not
the clean column.
-/

/-! ### §130.1 The gate is false without `BT.isStd`, at level ≤ 1 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- `ψ₁` の入れ子。 -/
def nest130 : Nat → BT
  | 0 => .zero
  | n+1 => .D 1 (nest130 n)

/-- **段 1 以下での最小の反例。** `ψ₁ψ₁ψ₁(ψ₀(ψ₁ψ₁ψ₁ψ₁0))`、`BT` の大きさ 9。 -/
def min130 : BT := .D 1 (.D 1 (.D 1 (.D 0 (nest130 4))))

/-- 吐かれた指数だけを取り出す。 -/
def emit130 (u : Nat) (x : Term) : List Term :=
  ((scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1).filter
    (fun p => le (reg (u+1)) p.2.1)).map (fun p => idxOf (reg (u+1)) p.1 p.2)

theorem size_min130 : min130.size = 9 := rfl
theorem btLe_min130 : btLe72 1 min130 = true := by decide
theorem std_min130 : BT.isStd min130 = true := by decide
/-- 救っているのはこの一つの Boolean。 -/
theorem not_std_D0_min130 : BT.isStd (BT.D 0 min130) = false := by decide

/-- **§130.1 の主定理。** 段 1 以下で第三の穴が開く。 -/
theorem not_psiIdxOK_min130 : ¬ PsiIdxOK 0 (dict min130) := fun H =>
  Bool.noConfusion ((psiIdxOKb_of_psiIdxOK H).symm.trans
    (show psiIdxOKb 0 (dict min130) = false from rfl))

/-- **`BT.isStd` を外した §72.8 の門は、段 1 以下でも偽。** -/
theorem not_psiIdxOK_le1_130 :
    ¬ (∀ (u : Nat) (a : BT), u ≤ 1 → btLe72 1 a = true → PsiIdxOK u (dict a)) :=
  fun H => not_psiIdxOK_min130 (H 0 min130 (by omega) btLe_min130)

/-- 一歩ぶんの形も同じところで外れる。 -/
theorem not_ksetStepOK_min130 : ¬ KsetStepOK 0 (dict min130) := fun H =>
  Bool.noConfusion ((stepOKb_of_ksetStepOK H).symm.trans
    (show stepOKb 0 (dict min130) = false from rfl))

/-! **機構。** `z` 自身の畳み込みが発火すると `dict (ψ₀ z) = ψ_{Ω₁}(β)` そのもので、
`β = dict z` は `Ω₁` **以上**になる (`nest130 4` から先がそう)。この `ψ_{Ω₁}(β)` は
`Ω₁` の下なので `ψ₁` の指数の低い側に座り、`mulL` がそれをそのまま吐かれる指数に運ぶ。
`min130` では吐かれる指数は `dict min130` **そのもの**で、`K_{Ω₁}` はその中の `β` を
返す。`i` は `β` の塔の `Ω₁` を、より小さい `ψ_{Ω₁}(β)` に取り替えたものだから
`β > i`、2.1(vi) の最後の連言が外れる。添字 2 以上はどこにも要らない。
Buchholz の標準性 `G(a,0) < a` がまさに `β` の大きさを止める条件で、
`BT.isStd (ψ₀ min130)` が偽なのはその一点である。 -/

#guard dict (BT.D 0 (nest130 4)) == psi (reg 1) (dict (nest130 4))
#guard !(lt (dict (nest130 4)) (reg 1))
#guard (emit130 0 (dict min130)).length == 1
#guard (emit130 0 (dict min130)).map (Kset (reg 1)) == [[dict (nest130 4)]]
#guard ((emit130 0 (dict min130)).all fun i => !(lt (dict (nest130 4)) i))
#guard (fires73 min130).map (fun p => p.2.1) == [logOm (dict min130)]
#guard (fires73 min130).map (fun p => p.2.2) == [TM.Term.one]
#guard emit130 0 (dict min130) == [dict min130]

/-! **なぜ既存の反例では届かないか、なぜ既存の母集団では出ないか。**
§66 の `badArg` は添字 3 が要る。§73 の `wKOK73` が外すのは移送 `KOK73` だけで、門は
通る。`aBad73` は `ψ₀` の引数が一段浅く、`β = 0` になるので通る。そして `min130` は
§72 の `btPool72` にも §73 の `hotB73` にも入っていない。 -/

#guard !(btLe72 1 badArg)
#guard psiIdxOKb 0 (dict wKOK73) && !(KOK73 (dict wKOK73))
#guard psiIdxOKb 0 (dict aBad73)
#guard (emit130 0 (dict aBad73)).map (Kset (reg 1)) == [[zero]]
#guard !(btPool72.contains min130)
#guard !(hotB73.contains min130)

end

/-! ### §130.2 Level-zero arguments: the gate is a theorem -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **段 0 純粋** — §73 の `pure73` から `Z` を外したもの。`Z 0` すら許さない。 -/
def pure0130 : Term → Bool
  | zero => true
  | M => false
  | omg _ => false
  | add a b => pure0130 a && pure0130 b
  | phi a b => pure0130 a && pure0130 b
  | psi _ _ => false
  | Z _ => false

theorem pure0126_zero : pure0130 zero = true := rfl
theorem pure0126_one : pure0130 TM.Term.one = true := rfl

theorem pure0126_add {a b : Term} (ha : pure0130 a = true) (hb : pure0130 b = true) :
    pure0130 (add a b) = true := by
  show (pure0130 a && pure0130 b) = true
  rw [ha, hb]; rfl

theorem pure0126_add_iff {a b : Term} (h : pure0130 (add a b) = true) :
    pure0130 a = true ∧ pure0130 b = true := (Bool.and_eq_true _ _).mp h

theorem pure0126_phi {a b : Term} (ha : pure0130 a = true) (hb : pure0130 b = true) :
    pure0130 (phi a b) = true := by
  show (pure0130 a && pure0130 b) = true
  rw [ha, hb]; rfl

/-- 段 0 純粋なら §73 の意味でも純粋。`lt M ·` と `· == M` は §73 から借りる。 -/
theorem pure73_of_pure0130 : ∀ (t : Term), pure0130 t = true → pure73 t = true
  | zero, _ => rfl
  | M, h => Bool.noConfusion h
  | omg _, h => Bool.noConfusion h
  | psi _ _, h => Bool.noConfusion h
  | Z _, h => Bool.noConfusion h
  | add a b, h => by
    obtain ⟨ha, hb⟩ := pure0126_add_iff h
    exact pure73_add (pure73_of_pure0130 a ha) (pure73_of_pure0130 b hb)
  | phi a b, h => by
    obtain ⟨ha, hb⟩ := (Bool.and_eq_true _ _).mp (show (pure0130 a && pure0130 b) = true from h)
    exact pure73_phi (pure73_of_pure0130 a ha) (pure73_of_pure0130 b hb)

/-! ### The order fact: a level-zero pure term is below `Ω₁` -/

theorem ltF_pure0126_Z0 : ∀ (f : Nat) (t : Term), t.deg + 2 ≤ f + 1 → pure0130 t = true →
    ltF (f + 1) t (Z zero) = true := by
  intro f
  induction f with
  | zero => intro t hf _; exact absurd hf (by have := deg_pos73 t; omega)
  | succ f ih =>
    intro t hf hp
    cases t with
    | zero => exact ltF_succ_zero_Z73 _ _
    | M => exact Bool.noConfusion hp
    | omg a => exact Bool.noConfusion hp
    | psi k a => exact Bool.noConfusion hp
    | Z a => exact Bool.noConfusion hp
    | add a b =>
      rw [ltF_succ_add_Z73]
      refine ih a ?_ (pure0126_add_iff hp).1
      have h1 : (add a b).deg = 1 + a.deg + b.deg := rfl
      have := deg_pos73 b
      omega
    | phi a b =>
      obtain ⟨ha, hb⟩ := (Bool.and_eq_true _ _).mp (show (pure0130 a && pure0130 b) = true from hp)
      have h1 : (phi a b).deg = 1 + a.deg + b.deg := rfl
      have h2 := deg_pos73 a
      have h3 := deg_pos73 b
      rw [ltF_succ_phi_Z, ih a (by omega) ha, ih b (by omega) hb]
      rfl

/-- **段 0 純粋な項は `Ω₁ = reg 1` より小さい。** -/
theorem lt_pure0126_reg1 {t : Term} (h : pure0130 t = true) : lt t (reg 1) = true := by
  show lt t (Z zero) = true
  rw [lt_eq_ltF t (Z zero) (2 * (t.deg + (Z zero : Term).deg) + 7 + 1) (by omega)]
  refine ltF_pure0126_Z0 _ t ?_ h
  have h1 : (Z zero : Term).deg = 2 := rfl
  omega


/-! ### Level-zero purity passes through the dictionary -/

theorem pure0126_ofList : ∀ (l : List Term), (∀ p ∈ l, pure0130 p = true) →
    pure0130 (ofList l) = true
  | [], _ => rfl
  | [a], h => h a (List.mem_cons.mpr (Or.inl rfl))
  | a :: b :: r, h => by
    show pure0130 (add a (ofList (b :: r))) = true
    exact pure0126_add (h a (List.mem_cons.mpr (Or.inl rfl)))
      (pure0126_ofList (b :: r) fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))

theorem pure0126_toList : ∀ (t : Term), pure0130 t = true → ∀ p ∈ toList t, pure0130 p = true
  | zero, _, _, hp => by cases hp
  | M, h, _, _ => Bool.noConfusion h
  | omg _, h, _, _ => Bool.noConfusion h
  | psi _ _, h, _, _ => Bool.noConfusion h
  | Z _, h, _, _ => Bool.noConfusion h
  | add a b, h, p, hp => by
    rcases List.mem_cons.mp (show p ∈ a :: toList b from hp) with h1 | h1
    · rw [h1]; exact (pure0126_add_iff h).1
    · exact pure0126_toList b (pure0126_add_iff h).2 p h1
  | phi a b, h, p, hp => by
    rw [List.mem_singleton.mp (show p ∈ [phi a b] from hp)]; exact h

theorem pure0126_plus {s t : Term} (hs : pure0130 s = true) (ht : pure0130 t = true) :
    pure0130 (plus s t) = true := by
  show pure0130 (match toList t with
    | [] => s
    | b1 :: _ => ofList ((toList s).filter (fun a => le b1 a) ++ toList t)) = true
  cases hl : toList t with
  | nil => exact hs
  | cons b1 r =>
    refine pure0126_ofList _ ?_
    intro x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact pure0126_toList s hs x (List.mem_filter.mp h1).1
    · exact pure0126_toList t ht x (by rw [hl]; exact h1)

theorem pure0126_ofNat : ∀ n, pure0130 (TM.Term.ofNat n) = true
  | 0 => rfl
  | n + 1 => pure0126_plus (pure0126_ofNat n) pure0126_one

theorem pure0126_take_ofList {b : Term} (h : pure0130 b = true) (k : Nat) :
    pure0130 (ofList ((toList b).take k)) = true :=
  pure0126_ofList _ fun x hx => pure0126_toList b h x (List.mem_of_mem_take hx)

theorem pure0126_splitFin {b : Term} (h : pure0130 b = true) :
    pure0130 (splitFin b).1 = true := pure0126_take_ofList h _

theorem pure0126_phiNFdefault {a b : Term} (ha : pure0130 a = true) (hb : pure0130 b = true) :
    pure0130 (phiNFdefault a b) = true := by
  unfold TM.Term.phiNFdefault
  split
  · exact ha
  · exact pure0126_phi ha hb

theorem pure0126_phiNFsucc {a b : Term} (ha : pure0130 a = true) (hb : pure0130 b = true) :
    pure0130 (phiNFsucc a b) = true := by
  have hdef := pure0126_phiNFdefault ha hb
  have hg : pure0130 (splitFin b).1 = true := pure0126_splitFin hb
  unfold TM.Term.phiNFsucc
  split
  rename_i heq
  rw [heq] at hg
  split
  · split <;> (split <;>
      first
        | exact pure0126_phi ha (pure0126_plus hg (pure0126_ofNat _))
        | exact hdef)
  · exact hdef

theorem pure0126_phiNF {a b : Term} (ha : pure0130 a = true) (hb : pure0130 b = true) :
    pure0130 (phiNF a b) = true := by
  unfold TM.Term.phiNF
  split
  · exact hb
  · split
    · split
      · exact hb
      · exact pure0126_phiNFsucc ha hb
    · exact pure0126_phiNFsucc ha hb

theorem pure0126_omegaNF {x : Term} (h : pure0130 x = true) : pure0130 (omegaNF x) = true := by
  show pure0130 (if lt M x then omg x else if x == M then M else phiNF zero x) = true
  rw [if_neg (by rw [lt_M_pure73 (pure73_of_pure0130 x h)]; exact Bool.noConfusion),
    if_neg (by rw [beq_M_pure73 (pure73_of_pure0130 x h)]; exact Bool.noConfusion)]
  exact pure0126_phiNF pure0126_zero h

/-! ### The `u = 0` gate is unconditional on level-zero arguments -/

/-- 成分がすべて `w` より小さければ `wcnf` は対を出さず、末尾は成分列そのもの。
    §73 の `wcnf_nil73` の、返り値の第 2 成分まで言う形。 -/
theorem wcnf_all_lt130 {w : Term} : ∀ (L : List Term), (∀ p ∈ L, lt p w = true) →
    wcnf w L = ([], ofList L)
  | [], _ => rfl
  | p :: _rest, h => wcnf_cons_lt (h p (List.Mem.head _))

theorem pure0126_reg0 : pure0130 (reg 0) = true := rfl

theorem pure0126_collapse0_130 {x : Term} (hx : pure0130 x = true) :
    pure0130 (collapse 0 x) = true := by
  have hall : ∀ p ∈ toList x, lt p (reg (0+1)) = true :=
    fun p hp => lt_pure0126_reg1 (pure0126_toList x hx p hp)
  have hnil : (wcnf (reg (0+1)) (toList x)).1 = [] := wcnf_nil73 _ hall
  have htl : (wcnf (reg (0+1)) (toList x)).2 = ofList (toList x) := by
    rw [wcnf_all_lt130 _ hall]
  rw [collapse_eq, hnil, htl]
  exact pure0126_omegaNF (pure0126_plus pure0126_reg0
    (pure0126_plus pure0126_zero (pure0126_ofList _ (pure0126_toList x hx))))

/-- **段 0 だけの `BT` の像は段 0 純粋。** §73.4 の `pure73_dict` の一段下。 -/
theorem pure0126_dict : ∀ (a : BT), btLe72 0 a = true → pure0130 (dict a) = true
  | .zero, _ => rfl
  | .D u a, hb => by
    obtain ⟨hu, hba⟩ := btLe72_D 0 u a hb
    have hu0 : u = 0 := Nat.le_zero.mp hu
    subst hu0
    rw [Trans.Dict.dict_D]
    exact pure0126_collapse0_130 (pure0126_dict a hba)
  | .sum a b, hb => by
    obtain ⟨ha, hbb⟩ := btLe72_sum 0 a b hb
    rw [Trans.Dict.dict_sum]
    exact pure0126_plus (pure0126_dict a ha) (pure0126_dict b hbb)

/-- **段 0 だけなら `u = 0` でも `wcnf` は対を出さない** — 走査そのものが空。 -/
theorem wcnf_reg1_nil130 (a : BT) (hb : btLe72 0 a = true) :
    (wcnf (reg (0+1)) (toList (dict a))).1 = [] :=
  wcnf_nil73 _ fun p hp => lt_pure0126_reg1 (pure0126_toList _ (pure0126_dict a hb) p hp)

/-- **第三の穴は段 0 の引数では無条件に閉じる。** `BT.isStd` は要らない。 -/
theorem psiIdxOK_zero130 (a : BT) (hb : btLe72 0 a = true) : PsiIdxOK 0 (dict a) :=
  psiIdxOK_of_noSC 0 (dict a) (by
    intro ac hac
    rw [wcnf_reg1_nil130 a hb] at hac
    cases hac)

theorem ksetStepOK_zero130 (a : BT) (hb : btLe72 0 a = true) : KsetStepOK 0 (dict a) := by
  intro p hp _
  rw [wcnf_reg1_nil130 a hb] at hp
  cases hp

/-- §73.4 の `u = 1` を `PsiIdxOK` の形で。`inT` も `lt · M` も経由しない。 -/
theorem psiIdxOK_one130 (a : BT) (hb : btLe72 1 a = true) : PsiIdxOK 1 (dict a) :=
  psiIdxOK_of_noSC 1 (dict a) (by
    intro ac hac
    rw [wcnf_reg2_nil73 a hb] at hac
    cases hac)

/-- **§130 の主定理。** §72.8 の第二の門に残るのは `u = 0` かつ**段 1 の節を実際に
    持つ**引数だけ。段 0 だけの引数と `u = 1` はどちらも無条件の定理になった。 -/
theorem psiIdxOKStd172_of_lvl1_130
    (H : ∀ a : BT, btLe72 1 a = true → btLe72 0 a = false →
          BT.isStd (BT.D 0 a) = true → PsiIdxOK 0 (dict a)) :
    PsiIdxOKStd172 := by
  intro u a hu hb hs
  cases u with
  | zero =>
    cases h0 : btLe72 0 a with
    | true => exact psiIdxOK_zero130 a h0
    | false => exact H a hb h0 hs
  | succ u' =>
    cases u' with
    | zero => exact psiIdxOK_one130 a hb
    | succ u'' => exact absurd hu (by omega)

/-- 逆向き — 分割が本当に分割であることの記録。 -/
theorem lvl1_of_psiIdxOKStd172_130 (H : PsiIdxOKStd172) :
    ∀ a : BT, btLe72 1 a = true → btLe72 0 a = false →
      BT.isStd (BT.D 0 a) = true → PsiIdxOK 0 (dict a) :=
  fun a hb _ hs => H 0 a (by omega) hb hs

end

/-! ### §130.3 Measurement (frozen)

母集団の作り方を先に書く。§72 の `btPool72` も §73 の `hotB73` も**幅**で作った袋で、
どちらにも `min130` は入っていない。ここでは**大きさで全数**を作る。

    allTab130 n  第 k 成分が `BT.size = k+1` の段 1 以下の木**全部**。絞らない。
    stdTab130 n  同じものを各段で `BT.isStd` で絞ったもの。`isStd` は部分項に遺伝する
                 (`isStd (ψ_u a) = isStd a && …`、`isStd (a ⊕ b) = … && isStd a && isStd b`)
                 ので、途中で絞っても標準な木は一つも取りこぼさない。
    fires73      §73 のもの — `u = 0` の走査のうち強臨界枝を取る歩。
    emit130      その歩が吐く指数。 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 段 1 以下の木を大きさごとに全部 (絞らない)。 -/
def allTab130 : Nat → List (List BT)
  | 0 => [[BT.zero]]
  | n+1 =>
    let prev := allTab130 n
    let ds := [0,1].flatMap fun u => (prev.getD n []).map fun a => BT.D u a
    let ss := (List.range n).flatMap fun i =>
                (prev.getD i []).flatMap fun a => (prev.getD (n-1-i) []).map fun b => BT.sum a b
    prev ++ [ds ++ ss]

/-- 同じものを `BT.isStd` で絞ったもの。 -/
def stdTab130 : Nat → List (List BT)
  | 0 => [[BT.zero]]
  | n+1 =>
    let prev := stdTab130 n
    let ds := [0,1].flatMap fun u => (prev.getD n []).map fun a => BT.D u a
    let ss := (List.range n).flatMap fun i =>
                (prev.getD i []).flatMap fun a => (prev.getD (n-1-i) []).map fun b => BT.sum a b
    prev ++ [(ds ++ ss).filter BT.isStd]

/-- 一段ぶんの数え上げ — (標準な `ψ₀` 引数, 発火するもの, 発火して `K` が空でない歩を
    持つもの, 判定器を満たさないもの)。 -/
def row130 (l : List BT) : Nat × Nat × Nat × Nat :=
  (l.countP fun a => BT.isStd (BT.D 0 a),
   l.countP fun a => BT.isStd (BT.D 0 a) && !((fires73 a).isEmpty),
   l.countP fun a => BT.isStd (BT.D 0 a) &&
      (emit130 0 (dict a)).any (fun i => !((Kset (reg 1) i).isEmpty)),
   l.countP fun a => BT.isStd (BT.D 0 a) && !(psiIdxOKb 0 (dict a)))

-- 母集団の大きさ。
#guard (allTab130 10).map List.length ==
  [1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786]
#guard (stdTab130 12).map List.length ==
  [1, 2, 4, 7, 15, 33, 79, 184, 432, 1013, 2418, 5804, 14063]

/-! **否定 1 — 標準性を外すと、大きさ 9 から反例が出る。** 段 1 以下の木**全部**の上で
`psiIdxOKb 0 ∘ dict` が外れる本数を大きさごとに。大きさ 8 まで 0、9 で 1 (それが
`min130`)、10 で 3、11 で 30。**§72 の `btPool72` (幅 3 段) も §73 の `hotB73` も
この形を持っていない。** -/

#guard ((allTab130 10).map fun l => l.countP fun a => !(psiIdxOKb 0 (dict a))) ==
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 30]
#guard ((allTab130 10).getD 8 []).filter (fun a => !(psiIdxOKb 0 (dict a))) == [min130]

/-! **肯定 1 — 標準なものでは 0 敗、そして空回りしていない。** 大きさ 13 まで、
`BT.isStd (ψ₀ a)` を満たすものを全数で。行は (標準, 発火, `K` が空でない歩を持つ,
判定器を外す)。**`K` が空でない歩を持つ本数が 0 でないことが要点** — §72 の
`btPool72` ではそこが 0 で、その掃除は 2.1(vi) の最後の連言を一度も動かしていない。 -/

#guard ((stdTab130 12).map row130) ==
  [(1, 0, 0, 0), (2, 0, 0, 0), (3, 0, 0, 0), (5, 1, 0, 0), (10, 2, 0, 0),
   (22, 4, 0, 0), (49, 13, 0, 0), (110, 37, 1, 0), (246, 94, 2, 0),
   (559, 244, 7, 0), (1288, 623, 28, 0), (3023, 1589, 91, 0), (7118, 4050, 273, 0)]

/-! さらに大きさ 14・15 まで。`K` が空でない歩は 838・2494 本あって、そのどれも
2.1(vi) を外さない。 -/

#guard row130 ((stdTab130 13).getD 13 []) == (16902, 10292, 838, 0)
#guard row130 ((stdTab130 14).getD 14 []) == (40381, 26009, 2494, 0)

/-! **他の二つの枝も空回りしていない。** §122 が別の節を外した `wcnf` の**係数の併合**
(指数の等しい桁がひとつにまとまる) と、畳み込みが**二歩以上**発火して `idxOf` が
`plus i0 …` を通る枝。大きさ 14 までの標準な 29 338 本で、併合は 1398 本、二歩以上は
270 本、併合と発火が同時に起きるのは 164 本。§73 の `hotB73` では前の指数を持つ歩は
1 歩しかなかった。 -/

def stdU130 (n : Nat) : List BT := ((stdTab130 n).flatten).filter fun a => BT.isStd (BT.D 0 a)
/-- `wcnf` が併合した対の数 = (`Ω₁` 以上の成分の数) − (対の数)。 -/
def merged130 (a : BT) : Nat :=
  ((toList (dict a)).countP fun p => !(lt p (reg 1))) - (wcnf (reg 1) (toList (dict a))).1.length

#guard ((stdU130 13).length,
        (stdU130 13).countP fun a => 0 < merged130 a,
        (stdU130 13).countP fun a => 2 ≤ (fires73 a).length,
        (stdU130 13).countP fun a => (fires73 a).any fun p => p.1.1.isSome,
        (stdU130 13).countP fun a => 0 < merged130 a && !((fires73 a).isEmpty))
  == (29338, 1398, 270, 270, 164)

/-! **`btPool72` は 2.1(vi) の最後の連言を一度も動かさない。** 378 歩発火して、
`K` が空でない歩は 0。段 1 以下の全数のほうは大きさ 11 で初めて動く。 -/

#guard (btPool72.flatMap fires73).length == 378
#guard (btPool72.filter fun a =>
  (emit130 0 (dict a)).any fun i => !((Kset (reg 1) i).isEmpty)).length == 0

end
/-! ## §127 NAMING THE MATRIX BEHIND `¬ LimCofS1`

§126 proved `limCofS1_false126 : PsiIdxOKStd172 → HiMono89 → ¬ LimCofS1` by contradiction,
through `GapAtG0_107`, and said in so many words that it does not exhibit the matrix.
This section exhibits it.  The witness is already in the tree — it is §107's `tGap107`,
the index that sits at the TOP of the window, paired with the BOTTOM of the window as the
term it cannot reach.

    t  :=  `tGap107`  =  `bInv85 (bTowG98 1)`,  whose matrix is
           `(0,0)(1,1)(2,1)(3,1)(1,1)(2,1)(3,0)(4,1)(5,1)(6,1)`
           and whose value is  `vOf t = φ̄(Γ₀, Γ₀⊕1)`  (the window's upper end)

    s  :=  `rawT94 0`  =  `φ̄(Γ₀, 0)`  =  `phi (psi (Z zero) zero) zero`
           (the window's lower end, §94's tower of terms `dict` never produces)

`s` sits INSIDE `[φ̄(Γ₀,0), φ̄(Γ₀,Γ₀⊕1))`.  `GapAtG0_107` says no legitimate witness has a
value there; every `fsB t n` is a legitimate witness; so no term of the fundamental sequence
reaches `s`, while `s` is strictly below `vOf t`.  That is `LimCofS1` failing, with names on
it instead of a contradiction.

**WHAT NEEDS THE GATES AND WHAT DOES NOT.**  `stdB1 t`, `kindB t = lim`, `matB t 0`,
`inT s` and `lt s (vOf t)` are all gate-free — the last two by `decide`.  Only
`∀ n, le s (vOf (fsB t n)) = false` uses `PsiIdxOKStd172` and `HiMono89`, and it uses them
only through `GapAtG0_107` (`gap122`) and `LimDecS1` (`limDecS1_of_bridge71`).
§127.6 checks the first six steps of that ∀ by computation, gate-free.

Nothing here proves either gate, and nothing here says the table is wrong. -/

section
open Trans.Recal
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

/-! ### §127.1 二つの門から `GapAtG0_107` まで -/

/-- §126 の道をそのまま `GapAtG0_107` の形で止めたもの。 -/
theorem gapAtG0_127 (Hp : PsiIdxOKStd172) (HM : HiMono89) : GapAtG0_107 :=
  gap122 Hp (dictLtA74_126 Hp HM) (dictLtStd121 Hp HM) (gam0Drags_of_hiMono126 Hp HM)

/-- 基本列が `vOf t` の下に居ること。橋は `DictLtA74` から作る。 -/
theorem limDecS1_127 (Hp : PsiIdxOKStd172) (HM : HiMono89) : LimDecS1 :=
  limDecS1_of_bridge71 (vOfLtA71_of_dictLt76 Hp (dictLtA74_126 Hp HM))

/-! ### §127.2 名前のついた証人 — ここは門を使わない -/

/-- **添字は標準で、階数は 1 以下。** §107 の計算事実。 -/
theorem std127 : stdB1 tGap107 = true := stdB1_tGap107

/-- **添字は極限。** `rfl`。 -/
theorem lim127 : kindB tGap107 = BMS.Kind.lim := rfl

/-- **行列そのもの。** 列を並べたもの。`rfl`。 -/
theorem mat127 : matB tGap107 0 =
    [[0,0],[1,1],[2,1],[3,1],[1,1],[2,1],[3,0],[4,1],[5,1],[6,1]] := rfl

/-- **挑戦者の項は `φ̄(Γ₀,0)`。** `rfl`。 -/
theorem s127 : rawT94 0 = phi (psi (Z zero) zero) zero := rfl

/-- 挑戦者は 𝔗(M) の項。`decide`。 -/
theorem inT_s127 : inT (rawT94 0) = true := by decide

/-- **挑戦者は添字の値より真に下。** `decide`。門は要らない。 -/
theorem lt_s_vOf127 : lt (rawT94 0) (vOf tGap107) = true := by decide

/-- 添字の値は窓の上端 `φ̄(Γ₀, Γ₀⊕1)`。こちらは `dict` の像として書くので門が要る。 -/
theorem vOf127 (Hp : PsiIdxOKStd172) : vOf tGap107 = dict (bTowG98 1) :=
  vOf_tGap107 Hp

/-! ### §127.3 基本列は挑戦者に届かない — 門が要るのはここだけ -/

/-- **主補題。** 基本列のどの段も `φ̄(Γ₀,0)` を上から押さえない。
    段の値が `φ̄(Γ₀,0)` 以上なら §107 の窓の外、つまり窓の上端以上でなければならず、
    しかし段の値は窓の上端より真に下である。両立しない。 -/
theorem noReach127 (Hp : PsiIdxOKStd172) (HM : HiMono89) (n : Nat) :
    le (rawT94 0) (vOf (fsB tGap107 n)) = false := by
  cases hcase : le (rawT94 0) (vOf (fsB tGap107 n)) with
  | false => rfl
  | true =>
      exfalso
      have hu : stdB1 (fsB tGap107 n) = true := stdB1_fsB tGap107 std127 n
      have hv : vOf (fsB tGap107 n) = dict (bValA71 (fsB tGap107 n)) :=
        vOfIsDict76 Hp _ hu
      have hb : btLe72 1 (bValA71 (fsB tGap107 n)) = true := btLeA77 _ hu
      have hst : BT.isStd (bValA71 (fsB tGap107 n)) = true := stdA77 _ hu
      have hd : Hd085 (bValA71 (fsB tGap107 n)) :=
        hd085_bValA71_85 _ (nfB_of_stdB _ (stdB_of_stdB1 _ hu))
      have hle : le (rawT94 0) (dict (bValA71 (fsB tGap107 n))) = true := by
        rw [← hv]; exact hcase
      have hup : le (dict (bTowG98 1)) (dict (bValA71 (fsB tGap107 n))) = true :=
        gapAtG0_127 Hp HM _ hb hst hd hle
      have hdn : lt (dict (bValA71 (fsB tGap107 n))) (dict (bTowG98 1)) = true := by
        rw [← hv, ← vOf127 Hp]
        exact limDecS1_127 Hp HM tGap107 std127 lim127 n
      exact gap_contra107 Hp hb hst hdn hup

/-! ### §127.4 まとめ -/

/-- **§127 の主定理。**  二つの門のもとで `LimCofS1` を外す証人は具体的である。
    添字は `tGap107`、行列は `(0,0)(1,1)(2,1)(3,1)(1,1)(2,1)(3,0)(4,1)(5,1)(6,1)`、
    挑戦者は `φ̄(Γ₀,0)`。 -/
theorem limCofS1_witness127 (Hp : PsiIdxOKStd172) (HM : HiMono89) :
    stdB1 tGap107 = true
    ∧ kindB tGap107 = BMS.Kind.lim
    ∧ matB tGap107 0 = [[0,0],[1,1],[2,1],[3,1],[1,1],[2,1],[3,0],[4,1],[5,1],[6,1]]
    ∧ rawT94 0 = phi (psi (Z zero) zero) zero
    ∧ inT (rawT94 0) = true
    ∧ lt (rawT94 0) (vOf tGap107) = true
    ∧ ∀ n, le (rawT94 0) (vOf (fsB tGap107 n)) = false :=
  ⟨std127, lim127, mat127, s127, inT_s127, lt_s_vOf127, noReach127 Hp HM⟩

/-- **§126 の否定を、名前のついた証人だけから作り直したもの。**
    `cofDenseS1_iff_dict83` を通らない。 -/
theorem limCofS1_false127 (Hp : PsiIdxOKStd172) (HM : HiMono89) : ¬ LimCofS1 := by
  intro H
  obtain ⟨n, hn⟩ := H tGap107 std127 lim127 (rawT94 0) inT_s127 lt_s_vOf127
  rw [noReach127 Hp HM n] at hn
  exact Bool.noConfusion hn

/-- 密度の側も同じ二つの門で外れる。§83 の橋を一度だけ使う。 -/
theorem cofDenseS1_false127 (Hp : PsiIdxOKStd172) (HM : HiMono89) : ¬ CofDenseS1 :=
  fun H => limCofS1_false127 Hp HM
    ((cofDenseS1_iff_dict83 Hp (dictLtA74_126 Hp HM)).mp H)

/-! ### §127.5 証人の正体 — 窓の下端は `dict` の像にない項

`s = φ̄(Γ₀,0)` は §94 の「`dict` が一つも作らない項の塔」の第 0 段である。
`inT` は Rathjen 2.1(v) をそのまま実装していて Veblen の対に正規形の条件を課さないので、
`s` は 𝔗(M) の項であり、`lt` はそれを `Γ₀ = ψ_Ω(0)` の真上に置く。
外れているのは「`vOf` がここで大きすぎる」か「𝔗(M) の側がこの窓に項を持ちすぎる」かの
どちらかで、§127 はどちらとも言わない。 -/

theorem s_above_G0_127 : lt (psi (Z zero) zero) (rawT94 0) = true := lt_G0_rawT0_107

/-- 窓の下端が `s`、上端が `vOf tGap107`。両方とも門を使わない。 -/
theorem window127 :
    lt (psi (Z zero) zero) (rawT94 0) = true
    ∧ lt (rawT94 0) (vOf tGap107) = true :=
  ⟨s_above_G0_127, lt_s_vOf127⟩

/-! ### §127.6 測定 — ∀ の最初の六段を門なしで確かめる

`noReach127` の結論は門つきだが、各段は計算で確かめられる。行列は yaBMS の
`bms "(0,0)(1,1)(2,1)(3,1)(1,1)(2,1)(3,0)(4,1)(5,1)(6,1)[n]"` と一致する。 -/

#guard matB (fsB tGap107 0) 0 == [[0,0],[1,1],[2,1],[3,1],[1,1],[2,1],[3,0],[4,1],[5,1]]
#guard matB (fsB tGap107 1) 0 ==
  [[0,0],[1,1],[2,1],[3,1],[1,1],[2,1],[3,0],[4,1],[5,1],[6,0],[7,1],[8,1]]
#guard matB (fsB tGap107 2) 0 ==
  [[0,0],[1,1],[2,1],[3,1],[1,1],[2,1],[3,0],[4,1],[5,1],[6,0],[7,1],[8,1],[9,0],[10,1],[11,1]]

#guard le (rawT94 0) (vOf (fsB tGap107 0)) == false
#guard le (rawT94 0) (vOf (fsB tGap107 1)) == false
#guard le (rawT94 0) (vOf (fsB tGap107 2)) == false
#guard le (rawT94 0) (vOf (fsB tGap107 3)) == false
#guard le (rawT94 0) (vOf (fsB tGap107 4)) == false
#guard le (rawT94 0) (vOf (fsB tGap107 5)) == false

-- 段の値は挑戦者より真に下 — 追い越すどころか下にいる。
#guard lt (vOf (fsB tGap107 5)) (rawT94 0) == true

#print axioms limCofS1_witness127
#print axioms limCofS1_false127

end

/-! ### §127.7 A READING ERROR, RETRACTED — AND THE ONE REAL THING NEXT TO IT

**§127.7 AS FIRST WRITTEN WAS WRONG AND IS RETRACTED HERE.**  It claimed that `inT`'s clause
for `phi` is unfaithful to [Rathjen 1991] 2.1(v), that `φ̄(Γ₀,0)` and `Γ₀` are the same
ordinal sitting at two places in `lt`, and that §107's window might therefore be an artifact
of the port.  All three are false.  The error was reading `phiNF a b` as "the normal form of
the term `phi a b`".  It is not that.

    `phi a b`    is Rathjen's  **φ̄**αβ  — the raw CONSTRUCTOR of 2.1(v).  It RE-COUNTS:
                 it skips the values of `φ_α` that other terms already name.
    `phiNF a b`  is Rathjen's  **φ**αβ  — 2.6(vi), the operation taking a PAIR OF ARGUMENTS
                 to the term that denotes the true Veblen value `φ_α(β)`.

They are different functions of `(a, b)`, and comparing their outputs is a category error.
2.1(v) reads "α, β ∈ 𝔗(M), α, β < M ⇒ φ̄αβ ∈ AP" with no normal-form side condition, and
Remark (ii) of §2.1 spells out a side condition for `ψ` and for nothing else.
**`TM/NF.lean`'s clause is verbatim faithful and must be left alone.**

What `φ̄Γ₀0` denotes is settled by 2.7, which this repo already transcribes as `TM/FS.lean`'s
`phiShifted`: for `β = 0` and `α ∈ SC`, `φ̄α0 = φα1`.  So `φ̄Γ₀0` denotes `φ(Γ₀,1)`, which IS
strictly above `Γ₀`, and `lt G094 (phi G094 zero) = true` is right.  `phiNF G094 zero = G094`
says "the term for the ordinal `φ_{Γ₀}(0)` is `Γ₀` itself"; it never said anything about the
term `phi G094 zero`.

The 314 count below is therefore not a defect count.  `phiNF a b ≠ phi a b` is the normal
state of affairs for a constructor whose job is to skip indices, and the criterion misjudges
audited rows: `dict (ψ₀(Ω₁ ⊕ 1)) = φ̄(0, ε₀)` — table row `(0,0)(1,1)(1,0)`, which
`TM/Terms.lean`'s header states is `ω^(ε₀+1)` and NOT `ε₀` — is one of the 314.  The guards
are kept, relabelled: they measure how often the shift fires, not how often anything is broken.

**THE ONE REAL THING, AND IT IS NEXT DOOR.**  `TM/FS.lean:88-104` records a KNOWN GAP in 2.7
as printed: for `α ∈ SC`, clause 1 gives `φ̄α0 = φα1`, and at `β = 1` no clause fires, so
`φ̄α1 = φα1` as well — two terms, one ordinal, while 2.3.13(ii) orders `φ̄α0 < φ̄α1`.  The note
argues the second disjunct should read `a.isSC`, DID NOT PATCH IT, and justified that by
measurement: the shape `φ̄(A,B)` with `A ∈ SC` and `B ≠ 0` occurs in 0 of 51 table rows, 0 of
750 CNV-corpus terms, and 0 of a 336-term pool of `dict` values.

**§107's window reaches it.**  `dict (bTowG98 1) = φ̄(Γ₀, Γ₀⊕1)` — the window's UPPER endpoint
and §127's witness value — has `A = Γ₀ ∈ SC` and `B ≠ 0`.  That is precisely the shape the
note measured as unreachable.  So the gap's measured reach was SHORT: the pools it was
measured against do not contain the window's top.  Under the repaired reading the endpoint
denotes `φ(Γ₀,Γ₀+2)` instead of `φ(Γ₀,Γ₀+1)` — one index, and the window is not emptied
either way — but anything that computes the window's WIDTH or enumerates its top has to be
checked against both readings.  §122, §125 and §126 use neither, so they stand.

**WHAT ELSE SURVIVED THE CHECK.**  `dict` is injective on the 9992-term standard population.
The window `[φ̄(Γ₀,0), φ̄(Γ₀,Γ₀⊕1))` holds 0 values at every size from 1 to 14 over 58239
standard level-`≤ 1` terms, and the reason is structural, not a short sweep: `phiNFdefault`
returns `α` when `β = 0` and `α ∈ SC`, so `dict` can never emit the shape `φ̄(SC,0)` at all,
and that shape is exactly the window's lower endpoint.  `GapAtG0_107` is not refuted. -/

section
open Trans.Recal
open Trans.Dict (BT dict reg collapse)
open TM TM.Term
open Evidence.WF

/-- `inT` は 2.1(v) をそのまま実装している。生の `φ̄(Γ₀,0)` は 𝔗(M) の項である。 -/
theorem inT_raw127 : inT (phi G094 zero) = true := rfl

/-- 2.6(vi)。**引数の対から、真の Veblen 値 `φ_{Γ₀}(0)` を表す項へ。**
    「項 `phi G094 zero` の正規形」ではない。 -/
theorem phiNF_G0_zero127 : phiNF G094 zero = G094 := rfl

/-- 2.7 (`TM/FS.lean` の `phiShifted`)。`β = 0` かつ `α ∈ SC` なので飛ばしが発火する
    — つまり項 `φ̄(Γ₀,0)` が表すのは `φ(Γ₀,1)` であって `Γ₀` ではない。 -/
theorem phiShifted_G0_zero127 : TM.Term.phiShifted G094 zero = true := rfl

theorem isSC_G0_127 : G094.isSC = true := rfl

/-- だから `lt` が生の方を上に置くのは**正しい**。 -/
theorem lt_raw127 : lt G094 (phi G094 zero) = true := rfl

theorem lt_raw_rev127 : lt (phi G094 zero) G094 = false := rfl

theorem raw_ne127 : phi G094 zero ≠ G094 := by decide

/-- 窓の下端はその生の項そのもの。 -/
theorem rawT0_eq127 : rawT94 0 = phi G094 zero := rfl

/-! ### §127.8 `TM/FS.lean` の KNOWN GAP は窓の上端に届く

2.7 を字義どおり読むと、`α ∈ SC` のとき `φ̄α0` と `φ̄α1` が同じ順序数 `φ_α(1)` を表す
(下の 3 つ)。`TM/FS.lean:88-104` はこれを記録し、直さない理由を「その形が
51 行・750 項・336 個の `dict` 値のどれにも出ない」と測定で述べている。
**窓の上端はその形である。** -/

/-- 2.6(vi) は `φ(Γ₀,1)` の項として `phi G094 one` を返す。 -/
theorem phiNF_G0_one127 : phiNF G094 one = phi G094 one := rfl

/-- ところが 2.7 を字義どおり読むと `β = 1` では飛ばしが発火しない。
    だから `φ̄(Γ₀,0)` と `φ̄(Γ₀,1)` が同じ順序数を表す — 記録済みの穴。 -/
theorem phiShifted_G0_one127 : TM.Term.phiShifted G094 one = false := rfl

/-- **窓の上端は `φ̄(A,B)`・`A ∈ SC`・`B ≠ 0` の形。**  測定が「出ない」と言った形。 -/
theorem dictTop_shape127 : dict (bTowG98 1) = phi G094 (TM.Term.plus G094 one) := rfl

theorem phiShifted_top127 :
    TM.Term.phiShifted G094 (TM.Term.plus G094 one) = false := rfl

/-! ### §127.9 取り下げた判定基準が誤判定する監査済みの行

`(0,0)(1,1)(1,0)` は `ω^(ε₀+1)` であって `ε₀` ではない (`TM/Terms.lean` の冒頭)。
取り下げた基準はこの行を「正規形でない」と言う。 -/

theorem anchor_dict127 : dict (BT.D 0 (BT.sum (BT.Om 1) BT.one)) = phi zero E081 := rfl

theorem anchor_phiNF127 : phiNF zero E081 = E081 := rfl

theorem anchor_lt127 : lt E081 (phi zero E081) = true := rfl

/-! **飛ばしが発火する頻度** (欠陥の数ではない)。§108.6 の 9992 項のうち、`dict z` が
    最上位で `phi a b` になり `phiNF a b ≠ phi a b` となるのは 314 項。
    うち 130 項は不動点の枝。上の監査済みの行もこの 314 の中にいる。 -/

def rawImg127 : List BT := allStd108.filter fun z => btLe72 1 z && BT.isStd z &&
  (match dict z with | phi a b => !(phiNF a b == phi a b) | _ => false)

#guard rawImg127.length == 314
#guard (rawImg127.countP fun z => match dict z with
          | phi a b => lt (phiNF a b) (phi a b) | _ => false) == 314
#guard (rawImg127.countP fun z => match dict z with
          | phi a b => b.isSC && lt a b | _ => false) == 130
#guard (rawImg127.map BT.size).take 3 == [3, 6, 6]
#guard rawImg127.contains (BT.D 0 (BT.sum (BT.Om 1) BT.one)) == true
#guard (allStd108.countP fun z => btLe72 1 z && BT.isStd z && inT (dict z)) == 9992

end

/-! ## §132 THE FIRST GATE: THE `K`-FREE HALF IS AN UNCONDITIONAL THEOREM, AND THE
       RESIDUAL IS EXACTLY THE COLUMN §130 MEASURED

§130 split `PsiIdxOKStd172` into `u = 1` (a theorem), level-zero arguments (a theorem), and
one remaining case: `u = 0` on arguments that carry a level-one node.  §130 also measured,
on standard level-`≤ 1` trees, the number of firing steps whose materials carry a NON-EMPTY
`K_{Ω₁}` — "the only place 2.1(vi)'s last conjunct can say anything" — and found
1, 2, 7, 28, 91, 273, 838, 2494 at sizes 8…15.  §132 proves that this column IS the whole
residual: everything outside it is an unconditional theorem.

WHAT IS PROVED, UNCONDITIONALLY.

  §132.1  **WHEN NO FIRING PAIR CARRIES A `K`, THE STEP GATE IS FREE.**
          `Kset_scanSt_state132` is the missing half of §66.2's `Kset_scanSt`: it tracks the
          `K` of the index the fold is HOLDING, not only of the index it emits.  With it,

              ksetStepOK_of_fireNil132 :
                (∀ ac ∈ (wcnf (reg (u+1)) (toList x)).1, le (reg (u+1)) ac.1 = true →
                    ∀ y, (y ∈ Kset (reg (u+1)) ac.1 ∨ y ∈ Kset (reg (u+1)) ac.2) → False)
                → KsetStepOK u x

          with no hypothesis at all — no gate, no `BT.isStd`, no induction, and `x` need not
          be in the image of `dict`.  `ksetStepOK_of_bigNil132` (the big components carry no
          `K`) and `ksetStepOK_of_kNil132` (`K_{Ω_{u+1}} x` itself is empty) are the coarser
          corollaries.  The firing form is the sharp one, and it is what makes the residual
          coincide with §130's column instead of merely containing it.

  §132.2  **THE SPLIT.**  Combining with §130's level-zero half,

              step073_of_fireNe132 :
                (∀ a, btLe72 1 a → btLe72 0 a = false → BT.isStd (ψ₀ a)
                    → fireK132 a ≠ [] → KsetStepOK 0 (dict a))
                → PsiIdxStep073

          and hence `PsiIdxStepStd172` and `PsiIdxOKStd172` through §73's chain.
          `fireNe132_of_step073` is the converse, so this is a SPLIT and not a weakening.
          **The gate now quantifies over `u = 0`, arguments that really carry a level-one
          node, AND arguments whose firing steps really read a coefficient set.**

  §132.3  **THE OBVIOUS STRENGTHENING IS FALSE.**  The natural way to finish — "every
          element of `K_{Ω₁}(dict a)` is below every emitted index" (`KDom132`) — is
          refuted by a standard tree of size 10,

              kDomBad132 = ψ₁ψ₁ψ₁0 ⊕ ψ₀ψ₁ψ₁ψ₁0 ,

          whose image is `ω^(ω^(Ω₁⊕Ω₁)) ⊕ ψ_{Ω₁}0`, whose `K_{Ω₁}` is `{0}`, and whose one
          emitted index is `0` itself, so `0 < 0` is asked for and refused.  The step gate
          `stepOKb 0 (dict kDomBad132)` nevertheless holds: the `ψ_{Ω₁}0` sits in the TAIL
          `ρ < Ω₁`, which no firing step ever reads.  That is exactly why §132.1 is stated
          over the firing pairs and not over `Kset (dict a)`.

  §132.4  **THE RESIDUAL, MEASURED.**  On the 12 436 standard trees of size ≤ 13 with
          `BT.isStd (ψ₀ ·)`, §130's split leaves 12 182 and §132's leaves **402**, and the
          per-size row is `1, 2, 7, 28, 91, 273` at sizes 8…13 (838 at size 14) — §130's
          column verbatim.  `min130` is still inside, `kDomBad132` is outside.

  §132.5  **A NEGATIVE SEARCH BY CONSTRUCTION.**  §130 enumerated to size 15.  §132.5 builds
          nine parametrised families around the shape that DOES break the gate once
          `BT.isStd (ψ₀ ·)` is dropped, and pushes them to size 28: 8 962 trees, 4 033 of
          them standard, 2 455 of those in the residual, **0 breaks**.  On the two families
          §130 named, the two boundaries COINCIDE exactly:
          `ψ₁(ψ₁ψ₁0 ⊕ ψ₀(ψ₁^k 0))` breaks iff `k ≥ 4` and `BT.isStd (ψ₀ ·)` fails iff
          `k ≥ 4`; `ψ₁^m(ψ₀(ψ₁^k 0))` breaks iff `3 ≤ m < k` and `BT.isStd (ψ₀ ·)` holds
          iff `k ≤ m`.  `min130` is the corner `m = 3, k = 4`.

WHAT IS NOT CLAIMED.  The gate is NOT refuted and NOT proved.  §132 removes a population,
not the mechanism.  The residual is still §88's `IdxLtStd88` — "the index of an inner `ψ₀`
is below the index the outer fold emits" — and nothing here touches that.  In particular
the natural argument "`BT.isStd (ψ₀ a)` puts every `e ∈ GB 0 a` below `a`, and `dict` is
order preserving, so the inner index stays below the outer one" cannot be run here: every
order-preservation statement about `dict` in this repository (`DictLtA74`, `DictLtStd92`,
`dictLtStd121`, `DictLtAtom96`, `dictHeadLtUpTo96_of_hi`, …) is either an unproved
hypothesis or carries `PsiIdxOKStd172` as an argument, so that route is circular.
-/

/-! ### §132.1 The step gate is free when no firing pair carries a `K` -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 畳み込みが**持っている**指数の `K` も、発火する成分の `K` の外に出ない。
    §66.2 の `Kset_scanSt` は**吐かれる**指数について同じことを言う。 -/
theorem Kset_scanSt_state132 {k w base : Term} (hw : ∀ z, z ∈ Kset k w → False)
    (S : Term → Prop) :
    ∀ (l : List (Term × Term)) (s : Option Term × Option Term),
      (∀ i0, s.1 = some i0 → ∀ y, y ∈ Kset k i0 → S y) →
      (∀ ac ∈ l, le w ac.1 = true → ∀ y, (y ∈ Kset k ac.1 ∨ y ∈ Kset k ac.2) → S y) →
      ∀ p ∈ scanSt w base s l, ∀ i0, p.1.1 = some i0 → ∀ y, y ∈ Kset k i0 → S y := by
  intro l
  induction l with
  | nil => intro s _ _ p hp; cases hp
  | cons ac t ih =>
    intro s hs hall p hp i0 hi0 y hy
    rcases List.mem_cons.mp (show p ∈ (s, ac) :: scanSt w base (stepF w base s ac) t from hp)
      with h | h
    · subst h; exact hs i0 hi0 y hy
    · refine ih (stepF w base s ac) ?_ (fun a ha => hall a (List.Mem.tail _ ha)) p h i0 hi0 y hy
      intro j hj z hz
      rw [stepF_fst] at hj
      cases hle : le w ac.1 with
      | true =>
        rw [if_pos hle] at hj
        have hz2 : z ∈ Kset k (idxOf w s ac) := by rw [Option.some.inj hj]; exact hz
        rcases mem_Kset_idxOf hw hz2 with h1 | h1
        · obtain ⟨i1, hi1, hz1⟩ := h1
          exact hs i1 hi1 z hz1
        · exact hall ac (List.Mem.head _) hle z h1
      | false =>
        rw [if_neg (by rw [hle]; exact Bool.noConfusion)] at hj
        exact hs j hj z hz

/-- **§132.1 の主定理。** 発火する対の材料 (指数側 `a` と係数側 `c`) がどちらも
    `K_{Ω_{u+1}}` を持たないなら、一歩ぶんの残る仮定は無条件で成り立つ。仮定も標準性も
    帰納法も要らず、`x` が `dict` の像である必要もない。 -/
theorem ksetStepOK_of_fireNil132 (u : Nat) (x : Term)
    (h : ∀ ac ∈ (wcnf (reg (u+1)) (toList x)).1, le (reg (u+1)) ac.1 = true →
      ∀ y, (y ∈ Kset (reg (u+1)) ac.1 ∨ y ∈ Kset (reg (u+1)) ac.2) → False) :
    KsetStepOK u x := by
  intro p hp hfire
  refine ⟨?_, ?_⟩
  · intro i0 hi0 y hy
    exact (Kset_scanSt_state132 (fun z hz => mem_Kset_reg (u+1) hz) (fun _ => False)
      (wcnf (reg (u+1)) (toList x)).1 (none, none) (fun j hj => by cases hj) h
      p hp i0 hi0 y hy).elim
  · intro y hy
    exact (h p.2 (scanSt_mem_snd _ _ _ _ p hp) hfire y hy).elim

/-- 粗い形 1 — `x` の**大きい成分**の `K` が空なら同じ結論。 -/
theorem ksetStepOK_of_bigNil132 (u : Nat) (x : Term)
    (h : ∀ y, y ∈ KsetL (reg (u+1)) (bigPart (reg (u+1)) (toList x)) → False) :
    KsetStepOK u x :=
  ksetStepOK_of_fireNil132 u x
    (fun ac hac _ y hy => h y (mem_Kset_wcnf (toList x) ac hac hy))

/-- 粗い形 2 — `K_{Ω_{u+1}} x` そのものが空なら同じ結論。 -/
theorem ksetStepOK_of_kNil132 (u : Nat) (x : Term)
    (h : ∀ y, y ∈ Kset (reg (u+1)) x → False) : KsetStepOK u x :=
  ksetStepOK_of_bigNil132 u x (fun y hy => h y (by
    rw [Kset_eq_KsetL]
    exact mem_KsetL_of_sub (fun q hq => bigPart_sub _ _ q hq) hy))

theorem ksetStepOK_of_kset_eq_nil132 {u : Nat} {x : Term} (h : Kset (reg (u+1)) x = []) :
    KsetStepOK u x :=
  ksetStepOK_of_kNil132 u x (fun y hy => by rw [h] at hy; cases hy)

end

/-! ### §132.2 The split -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **発火する対が読む係数集合。**  §132 が残す条件はこれが空でないこと。
    §130 が「2.1(vi) の最後の連言が何かを言える唯一の場所」と測ったものと同じ。 -/
def fireK132 (a : BT) : List Term :=
  ((wcnf (reg 1) (toList (dict a))).1.filter (fun ac => le (reg 1) ac.1)).flatMap
    (fun ac => Kset (reg 1) ac.1 ++ Kset (reg 1) ac.2)

theorem mem_fireK132 {a : BT} {ac : Term × Term}
    (hac : ac ∈ (wcnf (reg 1) (toList (dict a))).1) (hfire : le (reg 1) ac.1 = true)
    {y : Term} (hy : y ∈ Kset (reg 1) ac.1 ∨ y ∈ Kset (reg 1) ac.2) : y ∈ fireK132 a := by
  refine List.mem_flatMap.mpr ⟨ac, List.mem_filter.mpr ⟨hac, by rw [hfire]⟩, ?_⟩
  rcases hy with h | h
  · exact List.mem_append.mpr (Or.inl h)
  · exact List.mem_append.mpr (Or.inr h)

/-- `fireK132 a` が空な引数では、一項ぶんの残る仮定は無条件の定理。 -/
theorem gateStd87_of_fireNil132 {a : BT} (h : fireK132 a = []) : GateStd87 a := by
  intro _ _
  exact ksetStepOK_of_fireNil132 0 (dict a) (fun ac hac hfire y hy => by
    have := mem_fireK132 hac hfire hy
    rw [h] at this
    cases this)

/-- **§132.2 の主定理。** §73 の残る仮定に残るのは、**段 1 の節を実際に持ち、かつ
    発火する対が実際に `K_{Ω₁}` を読む**引数だけ。 -/
theorem step073_of_fireNe132
    (H : ∀ a : BT, btLe72 1 a = true → btLe72 0 a = false → BT.isStd (BT.D 0 a) = true →
          fireK132 a ≠ [] → KsetStepOK 0 (dict a)) : PsiIdxStep073 := by
  intro a hb hs
  cases hk : fireK132 a with
  | nil => exact gateStd87_of_fireNil132 hk hb hs
  | cons z zs =>
    cases h0 : btLe72 0 a with
    | true => exact ksetStepOK_zero130 a h0
    | false => exact H a hb h0 hs (by rw [hk]; exact List.cons_ne_nil z zs)

theorem psiIdxStepStd172_of_fireNe132
    (H : ∀ a : BT, btLe72 1 a = true → btLe72 0 a = false → BT.isStd (BT.D 0 a) = true →
          fireK132 a ≠ [] → KsetStepOK 0 (dict a)) : PsiIdxStepStd172 :=
  psiIdxStepStd172_of_step073 (step073_of_fireNe132 H)

/-- **第一の残る仮定そのもの。** -/
theorem psiIdxOKStd172_of_fireNe132
    (H : ∀ a : BT, btLe72 1 a = true → btLe72 0 a = false → BT.isStd (BT.D 0 a) = true →
          fireK132 a ≠ [] → KsetStepOK 0 (dict a)) : PsiIdxOKStd172 :=
  psiIdxOKStd172_of_step073 (step073_of_fireNe132 H)

/-- 逆向き — 分割が本当に分割であることの記録。 -/
theorem fireNe132_of_step073 (H : PsiIdxStep073) :
    ∀ a : BT, btLe72 1 a = true → btLe72 0 a = false → BT.isStd (BT.D 0 a) = true →
      fireK132 a ≠ [] → KsetStepOK 0 (dict a) :=
  fun a hb _ hs _ => H a hb hs

/-- 粗い形の分割。`dict a` の大きい成分の `K_{Ω₁}` で切ったもの。 -/
def bigK132 (a : BT) : List Term := KsetL (reg 1) (bigPart (reg 1) (toList (dict a)))

theorem step073_of_bigNe132
    (H : ∀ a : BT, btLe72 1 a = true → btLe72 0 a = false → BT.isStd (BT.D 0 a) = true →
          bigK132 a ≠ [] → KsetStepOK 0 (dict a)) : PsiIdxStep073 := by
  intro a hb hs
  cases hk : bigK132 a with
  | nil =>
    refine ksetStepOK_of_bigNil132 0 (dict a) (fun y hy => ?_)
    rw [show KsetL (reg (0+1)) (bigPart (reg (0+1)) (toList (dict a))) = bigK132 a from rfl,
      hk] at hy
    cases hy
  | cons z zs =>
    cases h0 : btLe72 0 a with
    | true => exact ksetStepOK_zero130 a h0
    | false => exact H a hb h0 hs (by rw [hk]; exact List.cons_ne_nil z zs)

end

/-! ### §132.3 The obvious strengthening is false -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **素直な強化。** 「`K_{Ω₁}(dict a)` の元はどれも、吐かれるどの指数より小さい」。
    これが本当なら §132.2 の残りは只で閉じる。**偽である。** -/
def KDom132 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true →
    ∀ p ∈ scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1,
      le (reg 1) p.2.1 = true → ∀ y ∈ Kset (reg 1) (dict a),
        lt y (idxOf (reg 1) p.1 p.2) = true

/-- その判定器。 -/
def kDomb132 (a : BT) : Bool :=
  (scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1).all fun p =>
    !(le (reg 1) p.2.1) ||
      (Kset (reg 1) (dict a)).all (fun y => lt y (idxOf (reg 1) p.1 p.2))

theorem kDomb132_of_KDom132 (H : KDom132) {a : BT} (hb : btLe72 1 a = true)
    (hs : BT.isStd (BT.D 0 a) = true) : kDomb132 a = true := by
  show ((scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1).all fun p =>
    !(le (reg 1) p.2.1) ||
      (Kset (reg 1) (dict a)).all (fun y => lt y (idxOf (reg 1) p.1 p.2))) = true
  rw [List.all_eq_true]
  intro p hp
  cases hle : le (reg 1) p.2.1 with
  | false => rfl
  | true =>
    rw [Bool.not_true, Bool.false_or, List.all_eq_true]
    intro y hy
    exact H a hb hs p hp hle y hy

/-- **反例。** `ψ₁ψ₁ψ₁0 ⊕ ψ₀ψ₁ψ₁ψ₁0`、`BT` の大きさ 10。 -/
def kDomBad132 : BT := BT.sum (nest130 3) (BT.D 0 (nest130 3))

theorem size_kDomBad132 : kDomBad132.size = 10 := rfl
theorem btLe_kDomBad132 : btLe72 1 kDomBad132 = true := by decide
theorem std_kDomBad132 : BT.isStd (BT.D 0 kDomBad132) = true := by decide

/-- **§132.3 の主定理。** 素直な強化は標準な木で外れる。 -/
theorem not_KDom132 : ¬ KDom132 := fun H =>
  Bool.noConfusion ((kDomb132_of_KDom132 H btLe_kDomBad132 std_kDomBad132).symm.trans
    (show kDomb132 kDomBad132 = false from rfl))

/-- **しかし残る仮定そのものは満たされる。** 外れた `ψ_{Ω₁}0` は末尾 `ρ < Ω₁` に座っていて、
    発火する歩はそこを読まない。だから §132.1 は `Kset` ではなく発火する対で書いてある。 -/
theorem stepOKb_kDomBad132 : stepOKb 0 (dict kDomBad132) = true := by decide
theorem fireK_kDomBad132 : fireK132 kDomBad132 = [] := rfl
theorem bigK_kDomBad132 : bigK132 kDomBad132 = [] := rfl
theorem kset_kDomBad132 : Kset (reg 1) (dict kDomBad132) = [zero] := rfl

/-! 吐かれる指数は `0` そのもので、`0 < 0` が要求されて外れる。 -/
#guard ((scanSt (reg 1) (baseOf 0) (none, none)
    (wcnf (reg 1) (toList (dict kDomBad132))).1).filter
  (fun p => le (reg 1) p.2.1)).map (fun p => idxOf (reg 1) p.1 p.2) == [zero]

end

/-! ### §132.4 Measurement (frozen)

母集団は §130 の `stdTab130` — 段 1 以下の木を**大きさで全数**作り、各段で `BT.isStd`
で絞ったもの。ここで測るのは `BT.isStd (ψ₀ a)` を満たす木、大きさ 13 まで 12 436 本。 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

def stdU132 (n : Nat) : List BT :=
  ((stdTab130 n).flatten).filter fun a => BT.isStd (BT.D 0 a)

/-! **残る母集団の縮み。** 12 436 本のうち、§130 の分割が残すのは 12 182 本
(段 1 の節を持つもの)、§132 の分割が残すのは **402 本** — 3.2 %。
粗い形なら大きい成分で 415 本、`Kset (dict a)` で 447 本。 -/

#guard (stdU132 12).length == 12436
#guard ((stdU132 12).countP fun a => !(btLe72 0 a)) == 12182
#guard ((stdU132 12).countP fun a => !((fireK132 a).isEmpty)) == 402
#guard ((stdU132 12).countP fun a => !((bigK132 a).isEmpty)) == 415
#guard ((stdU132 12).countP fun a => !((Kset (reg 1) (dict a)).isEmpty)) == 447

/-! **大きさごと。行は大きさ 1…13。** 発火する対が `K` を読む本数は
`1, 2, 7, 28, 91, 273` (大きさ 8…13) — §130 が「2.1(vi) の最後の連言が何かを言える
唯一の場所」として測った列そのもの。**§132 はその列が残り全部であることを証明する。** -/

#guard ((stdTab130 12).map fun l =>
    l.countP fun a => BT.isStd (BT.D 0 a) && !((fireK132 a).isEmpty)) ==
  [0, 0, 0, 0, 0, 0, 0, 1, 2, 7, 28, 91, 273]
#guard ((stdTab130 12).map fun l =>
    l.countP fun a => BT.isStd (BT.D 0 a) && !((bigK132 a).isEmpty)) ==
  [0, 0, 0, 0, 0, 0, 0, 1, 2, 7, 29, 94, 282]
#guard ((stdTab130 12).map fun l =>
    l.countP fun a => BT.isStd (BT.D 0 a) && !((Kset (reg 1) (dict a)).isEmpty)) ==
  [0, 0, 0, 0, 0, 0, 0, 1, 2, 8, 31, 101, 304]

/-! 大きさ 14 の段だけでは 838 本 — これも §130 の列と一致する。 -/

#guard (((stdTab130 13).getD 13 []).countP fun a =>
  BT.isStd (BT.D 0 a) && !((fireK132 a).isEmpty)) == 838

/-! **空回りしていない。** §130 の反例 `min130` は残ったまま、`kDomBad132` は外れる。 -/

#guard !((fireK132 min130).isEmpty)
#guard (fireK132 kDomBad132).isEmpty
#guard !(BT.isStd (BT.D 0 min130))
#guard BT.isStd (BT.D 0 kDomBad132)

#print axioms ksetStepOK_of_fireNil132
#print axioms step073_of_fireNe132
#print axioms psiIdxOKStd172_of_fireNe132
#print axioms not_KDom132

end


/-! ### §132.5 A negative search BY CONSTRUCTION, not by enumeration (frozen)

§130 enumerated every standard level-`≤ 1` tree to size 15.  §132.5 does the opposite: it
builds nine parametrised families around the shape that DOES break the gate once
`BT.isStd (ψ₀ ·)` is dropped, and pushes the parameters to size 28.  Nothing breaks. -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- `ψ₁` を `n` 回かぶせる。 -/
def nst132 : Nat → BT → BT
  | 0, t => t
  | n+1, t => BT.D 1 (nst132 n t)

/-- 残る仮定を外すか (標準性つき)。 -/
def bad132 (a : BT) : Bool := btLe72 1 a && BT.isStd (BT.D 0 a) && !(stepOKb 0 (dict a))
/-- 残る仮定を外すか (`BT.isStd a` だけ — `ψ₀` の標準性は課さない)。 -/
def raw132 (a : BT) : Bool := btLe72 1 a && BT.isStd a && !(stepOKb 0 (dict a))
/-- §132 が残す方に居るか。 -/
def hot132 (a : BT) : Bool := btLe72 1 a && BT.isStd (BT.D 0 a) && !((fireK132 a).isEmpty)

/-! **§130 が名指しした族。**  `ψ₁(ψ₁ψ₁0 ⊕ ψ₀(ψ₁^k 0))` は `k ≥ 4` で残る仮定を外し、
`BT.isStd (ψ₀ ·)` は `k ≥ 4` をちょうど外す。**二つの境目が一致する。** -/

def famA132 (k : Nat) : BT := BT.D 1 (BT.sum (nst132 2 BT.zero) (BT.D 0 (nst132 k BT.zero)))

#guard (List.range 9).all fun k => raw132 (famA132 k) == decide (4 ≤ k)
#guard (List.range 9).all fun k => BT.isStd (BT.D 0 (famA132 k)) == decide (k ≤ 3)
#guard (List.range 12).all fun k => !(bad132 (famA132 k))

/-! **`min130` の族。**  `ψ₁^m(ψ₀(ψ₁^k 0))` は `3 ≤ m < k` でちょうど残る仮定を外し、
`BT.isStd (ψ₀ ·)` は `k ≤ m` でちょうど成り立つ。**やはり境目が一致する** —
`min130 = famB132 3 4` はその角である。 -/

def famB132 (m k : Nat) : BT := nst132 m (BT.D 0 (nst132 k BT.zero))

#guard famB132 3 4 == min130
#guard (List.range 8).all fun m => (List.range 8).all fun k =>
  raw132 (famB132 m k) == decide (3 ≤ m ∧ m < k)
#guard (List.range 8).all fun m => (List.range 8).all fun k =>
  BT.isStd (BT.D 0 (famB132 m k)) == decide (k ≤ m)
#guard (List.range 10).all fun m => (List.range 10).all fun k => !(bad132 (famB132 m k))

/-! **九つの族、8962 本、大きさ 28 まで。**  そのうち `btLe72 1` かつ
`BT.isStd (ψ₀ ·)` なのが 4033 本、§132 が残す方に居るのが 2455 本、
**残る仮定を外すものは 0 本。** -/

def famPool132 : List BT :=
  let R := List.range
  ((R 9).flatMap fun m => (R 9).flatMap fun p => (R 9).map fun k =>
      nst132 m (if p == 0 then BT.D 0 (nst132 k BT.zero)
             else BT.sum (nst132 p BT.zero) (BT.D 0 (nst132 k BT.zero)))) ++
  ((R 8).flatMap fun m => (R 8).flatMap fun k => (R 8).map fun j =>
      nst132 m (BT.D 0 (nst132 k (BT.D 0 (nst132 j BT.zero))))) ++
  ((R 6).flatMap fun m => (R 6).flatMap fun p => (R 6).flatMap fun k => (R 6).map fun j =>
      nst132 m (BT.sum (nst132 p BT.zero)
        (BT.D 0 (BT.sum (nst132 k BT.zero) (BT.D 0 (nst132 j BT.zero)))))) ++
  ((R 6).flatMap fun m => (R 6).flatMap fun p => (R 6).flatMap fun k => (R 6).map fun j =>
      nst132 m (BT.sum (nst132 p BT.zero)
        (BT.sum (BT.D 0 (nst132 k BT.zero)) (BT.D 0 (nst132 j BT.zero))))) ++
  ((R 6).flatMap fun m => (R 6).flatMap fun p => (R 6).flatMap fun q => (R 6).map fun k =>
      nst132 m (BT.sum (nst132 p BT.zero)
        (BT.sum (nst132 q BT.zero) (BT.D 0 (nst132 k BT.zero))))) ++
  ((R 8).flatMap fun m => (R 8).flatMap fun k => (R 8).map fun j =>
      nst132 m (BT.D 0 (BT.sum (nst132 k BT.zero) (nst132 j BT.zero)))) ++
  ((R 9).flatMap fun m => (R 9).flatMap fun p => (R 9).map fun k =>
      nst132 m (nst132 p (BT.D 0 (nst132 k BT.zero)))) ++
  ((R 6).flatMap fun m => (R 6).flatMap fun p => (R 6).flatMap fun k => (R 6).map fun j =>
      nst132 m (BT.sum (nst132 p (BT.D 0 (nst132 k BT.zero))) (BT.D 0 (nst132 j BT.zero)))) ++
  ((R 6).flatMap fun m => (R 6).flatMap fun k => (R 6).flatMap fun p => (R 6).map fun j =>
      nst132 m (BT.D 0 (nst132 k (BT.sum (nst132 p BT.zero) (BT.D 0 (nst132 j BT.zero))))))

#guard famPool132.length == 8962
#guard (famPool132.map BT.size).foldl max 0 == 28
#guard (famPool132.countP fun a => btLe72 1 a && BT.isStd (BT.D 0 a)) == 4033
#guard famPool132.countP hot132 == 2455
#guard famPool132.countP bad132 == 0

end


/-! ## §133 THE SECOND GATE RESTS ON A CLAUSE WITH NO ANALYTIC CONTENT

`HiMono89` (§89) is the second of the two gates carrying row 326 and the whole level-≤1
sub-region.  §129 left it standing on exactly one hypothesis: `BT.isStd (BT.D 0 a)` of the
LEFT term — §81's `cexA89`/`cexB89` and §101's `bothBadA101`/`bothBadB101` satisfy every
other hypothesis of `VebRest129`, are left open by `closed129`, and break the conclusion.
§133 asks what that one hypothesis is doing.

WHAT IS PROVED, UNCONDITIONALLY.

  §133.1  **THE DEFECT, LOCATED AND MEASURED.**  `BT.isStd (BT.D 0 a)` is
           `BT.isStd a && (G(a,0)).all (· < a)`.  Both near-misses pass the first conjunct.
           In the second conjunct each has **exactly one** offending coefficient, and in
           both cases that coefficient is the argument of the term's **unique `ψ₀` node**:

               cexA89      = ψ₁ψ₀ψ₁ψ₁0                    offender  E = ψ₁ψ₁0    = cexB89
               bothBadA101 = ψ₁ψ₁0 ⊕ ψ₁ψ₁0 ⊕ ψ₁ψ₀(ψ₁ψ₁ψ₁0 ⊕ ψ₁0)
                                                          offender  E = ψ₁ψ₁ψ₁0 ⊕ ψ₁0

           The amount is the same in both: **a < E ≤ b**.  A `ψ₀` node hides a value of any
           size inside a syntactically small component (`ψ₁ψ₀X < ψ₁ψ₁0` for every `X`), and
           `K`-standardness is exactly the clause that caps it.  Repairing `a` therefore
           means pushing `a` up to `b`'s own height — and that is where `hi a < hi b` dies.

  §133.2  **THE ANALYTIC CONTENT OF THE CLAUSE IS ALREADY TRUE AT BOTH NEAR-MISSES.**
           Every proof from `VebRest129` up to `HiMono89` consumes `BT.isStd (BT.D 0 a)`
           through one door only — `dictFacts129`, which extracts `inT (dict a)`,
           `lt (dict a) M` and `PsiIdxOK 0 (dict a)`.  All three HOLD at `cexA89` and at
           `bothBadA101`, and so does `PsiIdxOK 1 (dict a)`.  Hence the relaxation

               `HiMonoSem133` — `HiMono89` with `BT.isStd (BT.D 0 ·)` replaced by
                                `inT`, `< M`, `PsiIdxOK 0`, `PsiIdxOK 1`

           implies `HiMono89` (under `PsiIdxOKStd172`) and is **FALSE**, with no gate
           assumed.  Same for `VebRestSem133` against `VebRest129`.  So the clause carrying
           the second gate is purely syntactic: it cannot be traded for anything the
           machinery currently knows how to use.

  §133.3  **THE OBVIOUS REPAIR PROVABLY CANNOT WORK.**  Prepend independent heads `c`, `c'`
           to the two sides: 12 heads each, 144 combinations per pair.  Whenever the result
           satisfies every hypothesis of `HiMono89` — 66 of the 144 for the §81 pair, 44 for
           the §101 pair — `closed117` CLOSES it, so under `PsiIdxOKStd172` the conclusion
           is FORCED (`repair_forced133`).  And prepending on the LEFT only is dead for a
           different reason: for every head, either `ψ₀(c ⊕ a)` is still not `K`-standard,
           or `hi (c ⊕ a) < hi b` is gone (`repair_asym133`).  Standardising means clearing
           the coefficient `E`, and `E` sits at `b`'s own height.

  §133.4  **A BUILT FAMILY, 200× §129'S POOL, STILL EMPTY.**  A family of level-≤1 terms
           of the smuggling shape (`h ⊕ ψ₁ψ₀E`, `ψ₁(w ⊕ ψ₀E)`, and sums of these) —
           1853 terms, up to **41 symbols**, where §129's exhaustive sweep stopped at 9.
           Against the 871 of them that are `K`-standard: **262150 pairs break the
           conclusion, and 0 of those have a `K`-standard left term** (`census133`).

WHAT IS NOT PROVED.  §133 does NOT prove that `K`-standardness forces the conclusion.
The no-go of §133.3 covers one repair family, and §133.4 is measurement.  The three-way
reading of §125/§126 is unchanged; what §133 adds is that branch 2 cannot be reached by
weakening `BT.isStd (BT.D 0 a)` to its analytic consequences.
-/

/-! ### §133.1 The defect of the two near-misses, exactly -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- §81 の `cexA89` がただ一つ外す係数 — `ψ₁ψ₁0`。**これは `cexB89` そのもの。** -/
def offA133 : BT := BT.D 1 (BT.D 1 BT.zero)

/-- §101 の `bothBadA101` がただ一つ外す係数 — `ψ₁ψ₁ψ₁0 ⊕ ψ₁0`。 -/
def offB133 : BT := BT.sum (BT.D 1 (BT.D 1 (BT.D 1 BT.zero))) (BT.D 1 BT.zero)

/-- **`BT.isStd (ψ₀ a)` の二つの連言。**  定義そのもの。 -/
theorem isStd0_eq133 (a : BT) :
    BT.isStd (BT.D 0 a) = (BT.isStd a && (BT.GB 0 a).all (fun e => BT.lt e a)) := rfl

/-- **一般の形 — `K` 標準性は `ψ₀` の引数を項自身の下に抑える。**
    §82.3 の `std0_split82` と §90.1 の `d0Args_sub_GB0_90` の合成。
    `ψ₁ψ₀X < ψ₁ψ₁0` はどんな `X` でも成り立つから、`ψ₀` の節は好きなだけ大きい値を
    見た目の小さい成分に隠せる。それを止めているのがこの条項だけである。 -/
theorem d0Arg_cap133 {a e : BT} (h : BT.isStd (BT.D 0 a) = true) (he : e ∈ d0Args88 a) :
    BT.lt e a = true :=
  (std0_split82 h).2 e (d0Args_sub_GB0_90 a e he)

/-- **§133.1 の第一の定理 — §81 の左辺が外す条項はどれか。**
    `cexA89` 自身は Buchholz 標準。`G(cexA89, 0)` の 4 個の係数のうちちょうど 1 個だけが
    `< cexA89` を満たさない。その 1 個は `cexA89` の唯一の `ψ₀` の引数であり、
    **それは右辺 `cexB89` そのもの**である。外し方は最大で `cexA89 < offA133`。 -/
theorem cexA_defect133 :
    (BT.isStd cexA89,
     (BT.GB 0 cexA89).length,
     ((BT.GB 0 cexA89).filter (fun e => !BT.lt e cexA89) == [offA133]),
     (d0Args88 cexA89 == [offA133]),
     (offA133 == cexB89),
     BT.lt cexA89 offA133,
     BT.le offA133 cexB89,
     BT.isStd (BT.D 0 offA133),
     BT.isStd (BT.D 0 cexA89))
    = (true, 4, true, true, true, true, true, true, false) := rfl

/-- **§133.1 の第二の定理 — §101 の左辺が外す条項はどれか。**  同じ形。
    `G(bothBadA101, 0)` の 10 個の係数のうちちょうど 1 個、それは唯一の `ψ₀` の引数で、
    `bothBadA101 < offB133 ≤ bothBadB101`。 -/
theorem bothBadA_defect133 :
    (BT.isStd bothBadA101,
     (BT.GB 0 bothBadA101).length,
     ((BT.GB 0 bothBadA101).filter (fun e => !BT.lt e bothBadA101) == [offB133]),
     (d0Args88 bothBadA101 == [offB133]),
     BT.lt bothBadA101 offB133,
     BT.le offB133 bothBadB101,
     BT.isStd (BT.D 0 offB133),
     BT.isStd (BT.D 0 bothBadA101))
    = (true, 10, true, true, true, true, true, false) := rfl

/-- **どちらも同じ形の欠陥、同じ大きさ。**  唯一の `ψ₀` の引数 `E` が `a < E ≤ b` に
    座っている。`K` 標準性が要求するのは `E < a`、つまり `a` を `b` の高さまで
    押し上げることである。 -/
theorem gap133 :
    (BT.lt cexA89 offA133, BT.le offA133 cexB89,
     BT.lt bothBadA101 offB133, BT.le offB133 bothBadB101)
    = (true, true, true, true) := rfl

/-- **結論の破れ方は二通りある。**  §81 の対は `ψ₀(hi a) = ψ₀(hi b)` (φ̄ の飛ばしで
    止まる)、§101 の対は `ψ₀(hi a) > ψ₀(hi b)` (真の逆転)。 -/
theorem breakKinds133 :
    ((collapse 0 (hiW89 (dict cexA89)) == collapse 0 (hiW89 (dict cexB89))),
     le (collapse 0 (hiW89 (dict bothBadA101))) (collapse 0 (hiW89 (dict bothBadB101))),
     lt (collapse 0 (hiW89 (dict bothBadB101))) (collapse 0 (hiW89 (dict bothBadA101))))
    = (true, false, true) := rfl

end

/-! ### §133.2 The analytic content of the clause is already true at both near-misses -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

/-- `PsiIdxOK` の判定器 — 有限リストの `all` そのもの。 -/
def psiIdxB133 (u : Nat) (x : Term) : Bool :=
  (scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1).all
    (fun p => !(le (reg (u+1)) p.2.1) || inT (psi (reg (u+1)) (idxOf (reg (u+1)) p.1 p.2)))

theorem psiIdxOK_of_B133 {u : Nat} {x : Term} (h : psiIdxB133 u x = true) : PsiIdxOK u x := by
  intro p hp hle
  have h2 := List.all_eq_true.mp h p hp
  rw [hle] at h2
  simpa using h2

/-- `G(a,1) ⊆ G(a,0)` — `GB` は添字が小さいほど多く拾う。 -/
theorem GB1_sub_GB0_133 : ∀ (a : BT), ∀ e ∈ BT.GB 1 a, e ∈ BT.GB 0 a
  | .zero => by intro e he; cases he
  | .D v x => by
      intro e he
      have h0 : BT.GB 0 (BT.D v x) = x :: BT.GB 0 x := by
        show (if 0 ≤ v then x :: BT.GB 0 x else []) = _
        rw [if_pos (Nat.zero_le v)]
      by_cases hv : 1 ≤ v
      · have h1 : BT.GB 1 (BT.D v x) = x :: BT.GB 1 x := by
          show (if 1 ≤ v then x :: BT.GB 1 x else []) = _
          rw [if_pos hv]
        rw [h1] at he; rw [h0]
        rcases List.mem_cons.mp he with h | h
        · rw [h]; exact List.Mem.head _
        · exact List.Mem.tail _ (GB1_sub_GB0_133 x e h)
      · have h1 : BT.GB 1 (BT.D v x) = [] := by
          show (if 1 ≤ v then x :: BT.GB 1 x else []) = _
          rw [if_neg hv]
        rw [h1] at he; cases he
  | .sum x y => by
      intro e he
      have hm : e ∈ BT.GB 1 x ++ BT.GB 1 y := he
      show e ∈ BT.GB 0 x ++ BT.GB 0 y
      rcases List.mem_append.mp hm with h | h
      · exact List.mem_append.mpr (Or.inl (GB1_sub_GB0_133 x e h))
      · exact List.mem_append.mpr (Or.inr (GB1_sub_GB0_133 y e h))

/-- `ψ₀a` が `K` 標準なら `ψ₁a` も `K` 標準。 -/
theorem isStd1_of_isStd0_133 {a : BT} (h : BT.isStd (BT.D 0 a) = true) :
    BT.isStd (BT.D 1 a) = true := by
  obtain ⟨h1, h2⟩ := std0_split82 h
  show (BT.isStd a && (BT.GB 1 a).all (fun e => BT.lt e a)) = true
  rw [h1, Bool.true_and]
  exact List.all_eq_true.mpr (fun e he => h2 e (GB1_sub_GB0_133 a e he))

/-- **測定 (凍結) — 四つの証人はどれも判定器を通る。**  左辺の二つは `K` 標準では
    ないのに、`PsiIdxOKStd172` がそこから渡すはずの事実はぜんぶ成り立っている。 -/
theorem analytic_witnesses133 :
    (psiIdxB133 0 (dict cexA89), psiIdxB133 1 (dict cexA89),
     inT (dict cexA89), lt (dict cexA89) M,
     psiIdxB133 0 (dict bothBadA101), psiIdxB133 1 (dict bothBadA101),
     inT (dict bothBadA101), lt (dict bothBadA101) M)
    = (true, true, true, true, true, true, true, true) := rfl

/-- **`HiMono89` の意味論版。**  `BT.isStd (ψ₀ ·)` を、`dictFacts129` が実際に
    取り出す事実だけに置き換えたもの。 -/
def HiMonoSem133 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    inT (dict a) = true → lt (dict a) M = true →
    PsiIdxOK 0 (dict a) → PsiIdxOK 1 (dict a) →
    inT (dict b) = true → lt (dict b) M = true →
    PsiIdxOK 0 (dict b) → PsiIdxOK 1 (dict b) →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true

/-- **意味論版は本物より強い** — 第一の門を仮定すれば `HiMono89` が出る。 -/
theorem hiMono_of_sem133 (Hp : PsiIdxOKStd172) (H : HiMonoSem133) : HiMono89 := by
  intro a b hbA hbB hsA hsB hWa hWb hlt
  have hba := (btLe72_D 1 0 a hbA).2
  have hbb := (btLe72_D 1 0 b hbB).2
  have hia := inT_dict_of_std172 Hp a hba (isStd_of_D hsA)
  have hib := inT_dict_of_std172 Hp b hbb (isStd_of_D hsB)
  exact H a b hbA hbB hia.1 hia.2
    (Hp 0 a (by omega) hba hsA) (Hp 1 a (by omega) hba (isStd1_of_isStd0_133 hsA))
    hib.1 hib.2
    (Hp 0 b (by omega) hbb hsB) (Hp 1 b (by omega) hbb (isStd1_of_isStd0_133 hsB))
    hWa hWb hlt

/-- **§133.2 の主定理 (1) — 意味論版は偽。**  門は何も仮定していない。証人は §81 の対。 -/
theorem not_hiMonoSem133 : ¬ HiMonoSem133 := by
  intro H
  have h := H cexA89 cexB89
    (show btLe72 1 (BT.D 0 cexA89) = true from rfl)
    (show btLe72 1 (BT.D 0 cexB89) = true from rfl)
    (show inT (dict cexA89) = true from rfl) (show lt (dict cexA89) M = true from rfl)
    (psiIdxOK_of_B133 (show psiIdxB133 0 (dict cexA89) = true from rfl))
    (psiIdxOK_of_B133 (show psiIdxB133 1 (dict cexA89) = true from rfl))
    (show inT (dict cexB89) = true from rfl) (show lt (dict cexB89) M = true from rfl)
    (psiIdxOK_of_B133 (show psiIdxB133 0 (dict cexB89) = true from rfl))
    (psiIdxOK_of_B133 (show psiIdxB133 1 (dict cexB89) = true from rfl))
    (show le (reg 1) (dict cexA89) = true from rfl)
    (show le (reg 1) (dict cexB89) = true from rfl)
    (show lt (hiW89 (dict cexA89)) (hiW89 (dict cexB89)) = true from rfl)
  rw [show lt (collapse 0 (hiW89 (dict cexA89))) (collapse 0 (hiW89 (dict cexB89)))
        = false from rfl] at h
  exact Bool.noConfusion h

/-- **同じことを §101 の対で。**  こちらは真の逆転で外す。 -/
theorem not_hiMonoSem132' : ¬ HiMonoSem133 := by
  intro H
  have h := H bothBadA101 bothBadB101
    (show btLe72 1 (BT.D 0 bothBadA101) = true from rfl)
    (show btLe72 1 (BT.D 0 bothBadB101) = true from rfl)
    (show inT (dict bothBadA101) = true from rfl)
    (show lt (dict bothBadA101) M = true from rfl)
    (psiIdxOK_of_B133 (show psiIdxB133 0 (dict bothBadA101) = true from rfl))
    (psiIdxOK_of_B133 (show psiIdxB133 1 (dict bothBadA101) = true from rfl))
    (show inT (dict bothBadB101) = true from rfl)
    (show lt (dict bothBadB101) M = true from rfl)
    (psiIdxOK_of_B133 (show psiIdxB133 0 (dict bothBadB101) = true from rfl))
    (psiIdxOK_of_B133 (show psiIdxB133 1 (dict bothBadB101) = true from rfl))
    (show le (reg 1) (dict bothBadA101) = true from rfl)
    (show le (reg 1) (dict bothBadB101) = true from rfl)
    (show lt (hiW89 (dict bothBadA101)) (hiW89 (dict bothBadB101)) = true from rfl)
  rw [show lt (collapse 0 (hiW89 (dict bothBadA101)))
        (collapse 0 (hiW89 (dict bothBadB101))) = false from rfl] at h
  exact Bool.noConfusion h

/-- **`VebRest129` の意味論版。** -/
def VebRestSem133 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    inT (dict a) = true → lt (dict a) M = true →
    PsiIdxOK 0 (dict a) → PsiIdxOK 1 (dict a) →
    inT (dict b) = true → lt (dict b) M = true →
    PsiIdxOK 0 (dict b) → PsiIdxOK 1 (dict b) →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lastFire92 (dict a) = false → lastFire92 (dict b) = false →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    closed129 a b = false →
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true

theorem vebRest129_of_sem133 (Hp : PsiIdxOKStd172) (H : VebRestSem133) : VebRest129 := by
  intro a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hcl
  have hba := (btLe72_D 1 0 a hbA).2
  have hbb := (btLe72_D 1 0 b hbB).2
  have hia := inT_dict_of_std172 Hp a hba (isStd_of_D hsA)
  have hib := inT_dict_of_std172 Hp b hbb (isStd_of_D hsB)
  exact H a b hbA hbB hia.1 hia.2
    (Hp 0 a (by omega) hba hsA) (Hp 1 a (by omega) hba (isStd1_of_isStd0_133 hsA))
    hib.1 hib.2
    (Hp 0 b (by omega) hbb hsB) (Hp 1 b (by omega) hbb (isStd1_of_isStd0_133 hsB))
    hWa hWb hfa hfb hlt hcl

/-- **§133.2 の主定理 (2) — 残る条項の意味論版も偽。**  §129 が残した一節は、
    その意味論的な中身では支えられない。 -/
theorem not_vebRestSem133 : ¬ VebRestSem133 := by
  intro H
  have h := H cexA89 cexB89
    (show btLe72 1 (BT.D 0 cexA89) = true from rfl)
    (show btLe72 1 (BT.D 0 cexB89) = true from rfl)
    (show inT (dict cexA89) = true from rfl) (show lt (dict cexA89) M = true from rfl)
    (psiIdxOK_of_B133 (show psiIdxB133 0 (dict cexA89) = true from rfl))
    (psiIdxOK_of_B133 (show psiIdxB133 1 (dict cexA89) = true from rfl))
    (show inT (dict cexB89) = true from rfl) (show lt (dict cexB89) M = true from rfl)
    (psiIdxOK_of_B133 (show psiIdxB133 0 (dict cexB89) = true from rfl))
    (psiIdxOK_of_B133 (show psiIdxB133 1 (dict cexB89) = true from rfl))
    (show le (reg 1) (dict cexA89) = true from rfl)
    (show le (reg 1) (dict cexB89) = true from rfl)
    (show lastFire92 (dict cexA89) = false from rfl)
    (show lastFire92 (dict cexB89) = false from rfl)
    (show lt (hiW89 (dict cexA89)) (hiW89 (dict cexB89)) = true from rfl)
    (show closed129 cexA89 cexB89 = false from rfl)
  rw [show lt (collapse 0 (hiW89 (dict cexA89))) (collapse 0 (hiW89 (dict cexB89)))
        = false from rfl] at h
  exact Bool.noConfusion h

end

/-! ### §133.3 The obvious repair provably cannot work -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

def wv133 : Nat → BT
  | 0 => BT.zero
  | n+1 => BT.D 1 (wv133 n)

/-- 修理に使う頭 12 個 — `ψ₁` の塔と 2 項和。 -/
def hdList133 : List BT :=
  [wv133 1, wv133 2, wv133 3, wv133 4, wv133 5,
   BT.sum (wv133 2) (wv133 2), BT.sum (wv133 3) (wv133 2), BT.sum (wv133 3) (wv133 3),
   BT.sum (wv133 4) (wv133 3), BT.sum (wv133 4) (wv133 4),
   BT.sum (wv133 5) (wv133 4), BT.sum (wv133 5) (wv133 5)]

/-- 左右に**別々の**頭を足した 144 通り。 -/
def pairList133 (a b : BT) : List (BT × BT) :=
  hdList133.flatMap (fun c => hdList133.map (fun c' => (BT.add c a, BT.add c' b)))

/-- `HiMono89` の仮定 7 本。 -/
def hypOK133 (p : BT × BT) : Bool :=
  btLe72 1 (BT.D 0 p.1) && btLe72 1 (BT.D 0 p.2) &&
  BT.isStd (BT.D 0 p.1) && BT.isStd (BT.D 0 p.2) &&
  le (reg 1) (dict p.1) && le (reg 1) (dict p.2) &&
  lt (hiW89 (dict p.1)) (hiW89 (dict p.2))

/-- 仮定が揃うなら §117 の道具が届く。 -/
def repGood133 (p : BT × BT) : Bool := !(hypOK133 p) || closed117 p.1 p.2

set_option maxRecDepth 1000000 in
/-- **§81 の対の修理はぜんぶ §117 が閉じる。** -/
theorem repairA_all133 : (pairList133 cexA89 cexB89).all repGood133 = true := rfl

set_option maxRecDepth 1000000 in
/-- **§101 の対も同じ。** -/
theorem repairB_all133 : (pairList133 bothBadA101 bothBadB101).all repGood133 = true := rfl

set_option maxRecDepth 1000000 in
/-- 144 通りのうち、仮定が揃うのは §81 の対で 66 通り、§101 の対で 44 通り。
    空振りではない。 -/
theorem repair_count133 :
    ((pairList133 cexA89 cexB89).length,
     (pairList133 cexA89 cexB89).countP hypOK133,
     (pairList133 bothBadA101 bothBadB101).countP hypOK133) = (144, 66, 44) := rfl

/-- **§133.3 の主定理 — 頭を足す修理は結論を強いる。**  左右に好きな頭を足して
    `HiMono89` の仮定が揃ったなら、第一の門のもとで結論が出る。**反例にはならない。** -/
theorem repair_forced133 (Hp : PsiIdxOKStd172) {a b : BT}
    (Hall : (pairList133 a b).all repGood133 = true)
    (p : BT × BT) (hp : p ∈ pairList133 a b) (hh : hypOK133 p = true) :
    lt (collapse 0 (hiW89 (dict p.1))) (collapse 0 (hiW89 (dict p.2))) = true := by
  have h := List.all_eq_true.mp Hall p hp
  unfold repGood133 at h
  rw [hh] at h
  have hcl : closed117 p.1 p.2 = true := by simpa using h
  unfold hypOK133 at hh
  simp only [Bool.and_eq_true] at hh
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, _⟩ := hh
  exact hiMono_closed117 Hp h1 h2 h3 h4 h5 h6 hcl

set_option maxRecDepth 1000000 in
/-- **左だけに足す道も死んでいる。**  どの頭 `c` でも、`ψ₀(c ⊕ a)` が `K` 標準に
    ならないか、`hi (c ⊕ a) < hi b` が残らないかのどちらかである。
    標準にするには頭が係数 `E` を越えねばならず、そのとき左辺が右辺を追い越す。 -/
theorem repair_asym133 :
    (hdList133.all (fun c =>
        !(BT.isStd (BT.D 0 (BT.add c cexA89))) ||
        !(lt (hiW89 (dict (BT.add c cexA89))) (hiW89 (dict cexB89)))),
     hdList133.all (fun c =>
        !(BT.isStd (BT.D 0 (BT.add c bothBadA101))) ||
        !(lt (hiW89 (dict (BT.add c bothBadA101))) (hiW89 (dict bothBadB101)))))
    = (true, true) := rfl

end

/-! ### §133.4 Measurement (frozen) — a built family, not a sweep

母集団は「隠し持ち」の形を組んだもの: `h ⊕ ψ₁ψ₀E`、`ψ₁(w_j ⊕ ψ₀E)`、およびその和。
`h`, `E` は `ψ₁` だけでできた降順和 (添字 1..4、長さ 3 まで) の 34 項。
最大 41 記号 — §129 の総当たりは 9 記号で止まっている。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf)
open TM TM.Term
open Evidence.WF

private def sumOf133 : List Nat → BT
  | [] => BT.zero
  | [j] => wv133 j
  | j :: r => BT.sum (wv133 j) (sumOf133 r)

private def descAll133 (mx : Nat) : Nat → List (List Nat)
  | 0 => []
  | n+1 =>
      let ones := ((List.range mx).map (fun i => i+1))
      let prev := descAll133 mx n
      ones.map (fun j => [j]) ++
      prev.flatMap (fun l => match l with
        | [] => []
        | h :: _ => (ones.filter (fun j => h ≤ j)).map (fun j => j :: l))

private def poolL133 (mx n : Nat) : List BT :=
  ((descAll133 mx n).map sumOf133).filter (fun t => BT.isStd t)

private def okW133 (a : BT) : Bool :=
  btLe72 1 (BT.D 0 a) && BT.isStd a && le (reg 1) (dict a)
private def okK133 (a : BT) : Bool :=
  btLe72 1 (BT.D 0 a) && BT.isStd (BT.D 0 a) && le (reg 1) (dict a)
private def dedup133 (l : List BT) : List BT :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []

private def P133 : List BT := poolL133 4 3
private def T0_133 : List BT := P133.map (fun E => BT.D 1 (BT.D 0 E))
private def T1_133 : List BT := (List.range 4).flatMap (fun i =>
  P133.map (fun E => BT.D 1 (BT.add (wv133 (i+1)) (BT.D 0 E))))

private def fam133 : List BT :=
  dedup133 (P133 ++ T0_133 ++ T1_133
    ++ P133.flatMap (fun h => T0_133.map (fun t => BT.add h t))
    ++ P133.flatMap (fun h => T1_133.map (fun t => BT.add h t))
    ++ T0_133.flatMap (fun x => T0_133.map (fun y => BT.add x y))) |>.filter okW133

private def recs133 : List (Bool × Term × Term) :=
  fam133.map (fun t => (okK133 t, hiW89 (dict t), collapse 0 (hiW89 (dict t))))
private def recsK133 : List (Term × Term) :=
  (recs133.filter (fun r => r.1)).map (fun r => r.2)

/-- 結論を破る組。値は左辺が `K` 標準かどうか。 -/
private def bad133 : List Bool :=
  recs133.flatMap (fun a => recsK133.filterMap (fun b =>
    if lt a.2.1 b.1 && !(lt a.2.2 b.2) then some a.1 else none))

private def census133 : Nat × Nat × Nat × Nat × Nat :=
  (fam133.length, recsK133.length, (fam133.map BT.size).foldl max 0,
   bad133.length, bad133.countP id)

/-! **受領 — 組んだ母集団の勘定。**  並びは (項の数, うち `K` 標準の数, 最大の記号数,
    結論を破る組の数, そのうち左辺も `K` 標準の数)。
    **1853 項・最大 41 記号で 262150 組が結論を破り、そのうち左辺が `K` 標準なのは 0。** -/
#guard census133 == (1853, 871, 41, 262150, 0)

end


/-! ## §134 AN INDEPENDENT IMPLEMENTATION CONFIRMS BRANCH 3 AND NAMES THE VALUE

§126 left three branches.  §132 and §133 attacked the two gates and closed neither.  §134
asks the third branch of an instrument this repository does not control:
naruyoko's `padicBotRathjen/implementation.js`, an independent implementation of
P進大好きbot's Rathjen-type notation, with its own `inOT`, `lessThan` and `fund`, reached
through `scripts/padicbot-ref.js`.  Nothing external was copied into this repository; the
source is CC BY-SA 3.0 and cited by URL in that script's header.

**THE ANSWER.**  `vOf tGap107` OVERSHOOTS.  The BMS expansion of §127's witness matrix is,
term for term, the external implementation's canonical fundamental sequence for the window's
**BOTTOM**, not for the value this repository assigns it.

    `oR (witness[n])`  ==  `extFund (φ_{Γ₀}(1), n+1)`      10 of 10 steps, their `equal`
    `extFund (φ_{Γ₀}(Γ₀+1), n)` is a different sequence — `φ_{tow n}(φ_{Γ₀}(Γ₀)+1)` — every
    member of which is at or above `φ_{Γ₀}(1)`, while every step this repo produces is
    strictly below it (their `lessThan`, n ≤ 24; this repo's `lt`, n ≤ 40).

So the two sequences are separated by a fixed term and cannot share a supremum.

**THE CONTROL, and it is what makes this readable.**  Five neighbouring rows of the same
family are healthy under the same instrument and one is broken:

    `(0,0)(1,1)(2,1)(3,1)`                            `Γ₀`                 reached
    `(0,0)(1,1)(2,1)(3,1)(1,1)`                       `φ_1(Γ₀+1)`          reached
    `(0,0)(1,1)(2,1)(3,1)(1,1)(2,1)`                  `φ_2(Γ₀+1)`          reached
    `…(3,0)(4,1)`                                     `φ_{φ_1(0)}(Γ₀+1)`   reached
    `…(3,0)(4,1)(5,1)`                                `φ_{φ_2(0)}(Γ₀+1)`   reached
    `…(3,0)(4,1)(5,1)(6,1)`   ← §127's witness        `φ_{Γ₀}(Γ₀+1)`       **never**

The test is not vacuous and the break is exactly at the window, not everywhere.

**THREE THINGS THAT WERE RULED OUT BY THE SAME RUN.**

  * *"The window is empty because there is nothing there."*  No — enumerating 62 664 terms
    over `{1, W, ψ^W(0)}` up to size 5, 13 181 pass their `inOT` and **143 lie inside the
    window**.  The window is empty only in `dict`'s image, not in 𝔗(M).
  * *"This repo's order misplaces the window."*  No — 41 terms spanning `Γ₀`, the window and
    `Ω`, sorted by this repo's `lt`, handed to their `lessThan`: **0 of 40 adjacent pairs
    disagree**, with a working reverse control.  Under the literal reading of 2.7 there is
    exactly ONE disagreement and it is the collapse §127.8 already records.
  * *"The port of 2.1(v) is unfaithful"* — §127.7's retracted branch, refuted a second time
    and independently: their `inOT` ACCEPTS `φ^0_{Γ₀}(1)` and REJECTS `φ^0_{Γ₀}(0)`, which is
    this repo's picture with the 2.7 shift applied.

**WHAT §134 DOES NOT SETTLE.**  The external implementation carries no BMS translation, so it
cannot say which SIDE of the correspondence is wrong.  What it establishes is: *given `oR`'s
values on the expansions*, the limit's value must be `φ̄(Γ₀,0)`.  The logically open
alternative — that `oR` undershoots on the whole cofinal chain instead — is not excluded.
Both alternatives are `¬ LimCofS1`.  Branches 1 and 2 are untouched by this section.

**AND THE ONE OBLIGATION LEFT, WHICH IS WORTH MORE THAN THE REST.**  The closed form

    `vOf (fsB tGap107 n) = φ̄(tow n, Γ₀)`

is verified below for `n ≤ 40` and externally for `n ≤ 24`.  **Proving it for all `n` makes
§127's `noReach127` GATE-FREE** — and then the two gates are irrelevant to branch 3, which
would stand on its own.  The measurement below already is gate-free; only the induction is
missing.

**NO PUBLISHED ROW IS CONTRADICTED.**  `table-r1.md` runs from `(0,0)(1,1)(2,1)(3,1)(1,0)`
straight to `(0,0)(1,1)(2,2)`; the whole window region, the witness included, is skipped.
What §134 says is about the translation `oR` that produces the table's values, not about a
row that has been published. -/

section
open Trans.Recal
open Trans.Dict (BT dict reg collapse)
open TM TM.Term
open Evidence.WF

/-- Veblen の塔 — 外部実装の `fund(ψ^W(0), n+1)` と同じ列。 -/
def two134 : Term := TM.Term.plus one one

def tow134 : Nat → Term
  | 0 => phi two134 zero
  | n+1 => phi (tow134 n) zero

/-! **基本列の値の閉じた形** — `n ≤ 40` で計算により確認 (門を使わない)。
    これを全ての `n` で証明すると §127 の `noReach127` から門が消える。 -/

#guard (List.range 41).all fun n => vOf (fsB tGap107 n) == phi (tow134 n) G094

/-! 各段は窓の下端より真に下、狭義増加、そして標準・段 1 以下。 -/

#guard (List.range 41).all fun n => lt (vOf (fsB tGap107 n)) (rawT94 0)
#guard (List.range 40).all fun n => lt (vOf (fsB tGap107 n)) (vOf (fsB tGap107 (n+1)))
#guard (List.range 41).all fun n => stdB1 (fsB tGap107 n)

/-- **残る義務。**  上の閉じた形を全ての `n` で。**証明しない。** -/
def ClosedFS134 : Prop := ∀ n : Nat, vOf (fsB tGap107 n) = phi (tow134 n) G094

/-- **その形にすれば門は要らない。**  閉じた形と、塔についての門を使わない順序の事実
    だけで、`∀ n` が出る。残っているのはその二つを証明することだけである。 -/
theorem noReach_of_closed134 (H : ClosedFS134)
    (Htow : ∀ n, le (rawT94 0) (phi (tow134 n) G094) = false) :
    ∀ n, le (rawT94 0) (vOf (fsB tGap107 n)) = false :=
  fun n => by rw [H n]; exact Htow n

/-- 上の第二の仮定は `n ≤ 40` で計算により成立している (§134 の `#guard`)。 -/
def TowBelow134 : Prop := ∀ n, le (rawT94 0) (phi (tow134 n) G094) = false

end
/-! ## §135 THE COFINALITY FAILURE, WITHOUT ITS TWO REMAINING ASSUMPTIONS


§126 proved `¬ LimCofS1` from `PsiIdxOKStd172` and `HiMono89`.  §127 named the witness:
the standard level-≤1 limit index `tGap107`, matrix
`(0,0)(1,1)(2,1)(3,1)(1,1)(2,1)(3,0)(4,1)(5,1)(6,1)`, challenger `φ̄(Γ₀,0)`.  Everything
in §127's witness was already unconditional EXCEPT the `∀ n` clause, and §134 reduced that
clause to two statements it verified by computation for `n ≤ 40` and did not prove:

    ClosedFS134 : ∀ n, vOf (fsB tGap107 n) = φ̄(tow n, Γ₀)
    TowBelow134 : ∀ n, le (φ̄(Γ₀,0)) (φ̄(tow n, Γ₀)) = false

THIS SECTION PROVES BOTH, so `limCofS1_false_free135 : ¬ LimCofS1` carries no hypothesis at
all.  The route, in four moves:

  §135.1  THE BMS SIDE IS A ONE-STEP COMPUTATION.  `fsB tGap107 n` never inspects `n`
          except at the very last node, so `fsB_shape135` is the definitional unfolding
          plus `appB_nil`; `bVal_fsB135` then reads the value off as
          `ψ₀(Ω^Ω ⊕ ψ₁ψ₁(K n))` with `K` an explicit level-alternating tower.

  §135.2  THE ORDER FACTS ABOUT THE TOWER.  Four statements, each one induction on `n`
          with an inner case on the fuel, in the style of WF §9.5's `ltF_junk_tower`:
          `Ω₁ ≮ tow n`, `Γ₀ ≮ tow n`, `tow n < Ω₁`, `tow n < Γ₀`.  The last two are stated
          against an arbitrary strongly critical target (`SCTgt135`) so one induction
          serves `Ω₁`, `Ω₂` and `Γ₀`.  `TowBelow134` is this plus 2.3.13(iii).

  §135.3  THE DICTIONARY, SYMBOLICALLY.  `dict` is structural, so the whole chain is two
          applications of `collapse 1` and one of `collapse 0` around an opaque `t`.  The
          three are computed once and for all: `collapse 1 t = φ̄(0, Ω₁ ⊕ t)`,
          `collapse 1 (φ̄(0, Ω₁ ⊕ t)) = φ̄(0, φ̄(0, Ω₁ ⊕ t))`, and then two `ψ₀` folds —
          one whose base-Ω₁ expansion has a single Veblen digit (value `φ̄(t,0)`, which
          drives the tower) and one whose expansion has a strongly critical digit `Ω₁`
          first (value `φ̄(t,Γ₀)`, which is the fundamental sequence's value).  The second
          is where `Γ₀` comes from: the SC branch of the fold emits `ψ_{Z0}(0)`, and the
          Veblen branch that follows lands on `phiNFsucc`, whose `⊕ 1` is absorbed exactly
          because `t < Γ₀`.  That absorption is `dict_bStep98_needs_G098`'s counterexample
          read positively, and it is why the value is `φ̄(t,Γ₀)` and not `φ̄(t,Γ₀⊕1)`.

  §135.4  ASSEMBLY.  `vOf`'s `1 ⊕ ·` is absorbed, `ClosedFS134` follows, and
          `noReach_of_closed134` of §134 turns the pair into §127's `∀ n` clause.

WHAT IS NOT CLAIMED.  Nothing here says which SIDE of the correspondence is wrong; §134's
reading of that is untouched.  `PsiIdxOKStd172` and `HiMono89` are neither used nor proved.
-/
section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

set_option maxRecDepth 8000


/-- 段 1 の節を三つ重ねたもの — `tGap107` の悪い根の部分木。 -/
def T3g135 : B := .nd 1 .nil (.nd 1 .nil (.nd 1 .nil .nil))

/-- `iterD` が作る木の中身。 -/
def Hg135 : Nat → B
  | 0 => .nd 1 .nil (.nd 1 .nil .nil)
  | k + 1 => .nd 1 .nil (.nd 1 .nil (.nd 0 .nil (Hg135 k)))

theorem tGap_shape135 :
    tGap107 = .nd 0 .nil (.nd 1 T3g135 (.nd 1 .nil (.nd 0 .nil T3g135))) := rfl

theorem iterD_shape135 : ∀ n, iterD 0 T3g135 n = .nd 0 .nil (Hg135 n)
  | 0 => rfl
  | k + 1 => by
      show B.nd 0 .nil (.nd 1 .nil (.nd 1 .nil (appB .nil (iterD 0 T3g135 k)))) = _
      rw [appB_nil, iterD_shape135 k]
      rfl

theorem fsB_shape135 (n : Nat) :
    fsB tGap107 n = .nd 0 .nil (.nd 1 T3g135 (.nd 1 .nil (.nd 0 .nil (Hg135 n)))) := by
  show B.nd 0 .nil (.nd 1 T3g135 (.nd 1 .nil (appB .nil (iterD 0 T3g135 n)))) = _
  rw [appB_nil, iterD_shape135 n]

/-- 下の塔の Buchholz 側。 -/
def Kg135 : Nat → BT
  | 0 => BT.D 0 (BT.D 1 (BT.D 1 BT.zero))
  | k + 1 => BT.D 0 (BT.D 1 (BT.D 1 (Kg135 k)))

theorem bArg_Hg135 : ∀ n, bArg 1 (.nd 0 .nil (Hg135 n)) = Kg135 n
  | 0 => rfl
  | k + 1 => by
      show BT.D 0 (BT.D 1 (BT.D 1 (bArg 1 (.nd 0 .nil (Hg135 k))))) = _
      rw [bArg_Hg135 k]
      rfl

theorem bVal_fsB135 (n : Nat) :
    bVal (fsB tGap107 n) = BT.D 0 (BT.sum bOO94 (BT.D 1 (BT.D 1 (Kg135 n)))) := by
  rw [fsB_shape135 n]
  show BT.D 0 (BT.sum bOO94 (BT.D 1 (BT.D 1 (bArg 1 (.nd 0 .nil (Hg135 n)))))) = _
  rw [bArg_Hg135 n]


/-! 2.3 の節を、この節で使う形だけ取り出したもの。 -/

theorem ltF_succ_phi_Z135 (g : Nat) (a b e : Term) :
    ltF (g + 1) (phi a b) (Z e) = (ltF g a (Z e) && ltF g b (Z e)) := rfl

theorem ltF_succ_phi_psi135 (g : Nat) (a b k c : Term) :
    ltF (g + 1) (phi a b) (psi k c) = (ltF g a (psi k c) && ltF g b (psi k c)) := rfl

theorem ltF_succ_add_Z135 (g : Nat) (a b e : Term) :
    ltF (g + 1) (add a b) (Z e) = ltF g a (Z e) := rfl

theorem ltF_succ_add_psi135 (g : Nat) (a b k c : Term) :
    ltF (g + 1) (add a b) (psi k c) = ltF g a (psi k c) := rfl

theorem ltF_succ_Z_add135 (g : Nat) (e c d : Term) :
    ltF (g + 1) (Z e) (add c d) = ((Z e == c) || ltF g (Z e) c) := rfl

theorem ltF_succ_psi_add135 (g : Nat) (k a c d : Term) :
    ltF (g + 1) (psi k a) (add c d) = ((psi k a == c) || ltF g (psi k a) c) := rfl

theorem ltF_succ_Z_phi135 (g : Nat) (e c d : Term) :
    ltF (g + 1) (Z e) (phi c d)
      = ((Z e == c) || (Z e == d) || ltF g (Z e) c || ltF g (Z e) d) := rfl

theorem ltF_succ_psi_phi135 (g : Nat) (k a c d : Term) :
    ltF (g + 1) (psi k a) (phi c d)
      = ((psi k a == c) || (psi k a == d) || ltF g (psi k a) c || ltF g (psi k a) d) := rfl

theorem ltF_succ_Z_Z135 (g : Nat) (a b : Term) :
    ltF (g + 1) (Z a) (Z b)
      = (if (Z a == Z b) = true then false
         else if ltF g a b = true then ltF g (starF g a) (Z b)
         else ((Z a : Term) == starF g b || ltF g (Z a) (starF g b))) := rfl

theorem starF_zero135 : ∀ (f : Nat), starF f (zero : Term) = zero
  | 0 => rfl
  | _ + 1 => rfl

/-! ### `Ω₁` と `Γ₀` は塔の下にいない -/

theorem ltF_Om_one135 : ∀ (f : Nat), ltF f (Z zero) TM.Term.one = false
  | 0 => rfl
  | g + 1 => by
      show ((Z zero : Term) == zero || (Z zero : Term) == zero
            || ltF g (Z zero) zero || ltF g (Z zero) zero) = false
      rw [ltF_right_zero]
      rfl

theorem ltF_Om_two135 : ∀ (f : Nat), ltF f (Z zero) two134 = false
  | 0 => rfl
  | g + 1 => by
      show ((Z zero : Term) == TM.Term.one || ltF g (Z zero) TM.Term.one) = false
      rw [ltF_Om_one135 g]
      rfl

theorem ltF_G0_one135 : ∀ (f : Nat), ltF f G094 TM.Term.one = false
  | 0 => rfl
  | g + 1 => by
      show ((G094 == zero) || (G094 == zero) || ltF g G094 zero || ltF g G094 zero) = false
      rw [ltF_right_zero]
      rfl

theorem ltF_G0_two135 : ∀ (f : Nat), ltF f G094 two134 = false
  | 0 => rfl
  | g + 1 => by
      show ((G094 == TM.Term.one) || ltF g G094 TM.Term.one) = false
      rw [ltF_G0_one135 g]
      rfl

theorem ltF_Om_tow135 : ∀ (n f : Nat), ltF f (Z zero) (tow134 n) = false
  | 0, 0 => rfl
  | 0, g + 1 => by
      show ((Z zero : Term) == two134 || (Z zero : Term) == zero
            || ltF g (Z zero) two134 || ltF g (Z zero) zero) = false
      rw [ltF_Om_two135 g, ltF_right_zero]
      rfl
  | _ + 1, 0 => rfl
  | k + 1, g + 1 => by
      show ((Z zero : Term) == tow134 k || (Z zero : Term) == zero
            || ltF g (Z zero) (tow134 k) || ltF g (Z zero) zero) = false
      rw [ltF_Om_tow135 k g, ltF_right_zero,
        show ((Z zero : Term) == tow134 k) = false from by
          cases k <;> rfl]
      rfl

theorem ltF_G0_tow135 : ∀ (n f : Nat), ltF f G094 (tow134 n) = false
  | 0, 0 => rfl
  | 0, g + 1 => by
      show ((G094 == two134) || (G094 == zero) || ltF g G094 two134 || ltF g G094 zero) = false
      rw [ltF_G0_two135 g, ltF_right_zero]
      rfl
  | _ + 1, 0 => rfl
  | k + 1, g + 1 => by
      show ((G094 == tow134 k) || (G094 == zero)
            || ltF g G094 (tow134 k) || ltF g G094 zero) = false
      rw [ltF_G0_tow135 k g, ltF_right_zero,
        show (G094 == tow134 k) = false from by cases k <;> rfl]
      rfl

/-! ### 塔は `Ω₁`・`Ω₂`・`Γ₀` の下にいる -/

/-- 目標が強臨界 (`Z` か `ψ`) であるときの 2.3 の二つの節。 -/
def SCTgt135 (T : Term) : Prop :=
  T ≠ zero
    ∧ (∀ (g : Nat) (a b : Term), ltF (g + 1) (phi a b) T = (ltF g a T && ltF g b T))
    ∧ (∀ (g : Nat) (a b : Term), ltF (g + 1) (add a b) T = ltF g a T)

theorem scTgt_Om135 : SCTgt135 (Z zero) :=
  ⟨by intro hc; exact Term.noConfusion hc, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem scTgt_Om2_135 : SCTgt135 (Z TM.Term.one) :=
  ⟨by intro hc; exact Term.noConfusion hc, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem scTgt_G0_135 : SCTgt135 G094 :=
  ⟨by intro hc; exact Term.noConfusion hc, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem ltF_one_sc135 {T : Term} (h : SCTgt135 T) :
    ∀ (f : Nat), 2 ≤ f → ltF f TM.Term.one T = true := by
  intro f hf
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  show ltF (g + 1) (phi zero zero) T = true
  rw [h.2.1 g zero zero, ltF_left_zero (by omega) h.1]
  rfl

theorem ltF_two_sc135 {T : Term} (h : SCTgt135 T) :
    ∀ (f : Nat), 3 ≤ f → ltF f two134 T = true := by
  intro f hf
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  show ltF (g + 1) (add TM.Term.one TM.Term.one) T = true
  rw [h.2.2 g TM.Term.one TM.Term.one]
  exact ltF_one_sc135 h g (by omega)

theorem ltF_tow_sc135 {T : Term} (h : SCTgt135 T) :
    ∀ (n f : Nat), n + 4 ≤ f → ltF f (tow134 n) T = true
  | 0, f, hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      show ltF (g + 1) (phi two134 zero) T = true
      rw [h.2.1 g two134 zero, ltF_two_sc135 h g (by omega), ltF_left_zero (by omega) h.1]
      rfl
  | k + 1, f, hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      show ltF (g + 1) (phi (tow134 k) zero) T = true
      rw [h.2.1 g (tow134 k) zero, ltF_tow_sc135 h k g (by omega),
        ltF_left_zero (by omega) h.1]
      rfl

theorem deg_tow135 : ∀ (n : Nat), (tow134 n).deg = 2 * n + 9
  | 0 => rfl
  | k + 1 => by
      show 1 + (tow134 k).deg + 1 = 2 * (k + 1) + 9
      rw [deg_tow135 k]; omega

theorem lt_tow_sc135 {T : Term} (h : SCTgt135 T) (hT : T.deg ≤ 4) (n : Nat) :
    lt (tow134 n) T = true := by
  show ltF (fuelOf (tow134 n) T) (tow134 n) T = true
  refine ltF_tow_sc135 h n _ ?_
  show n + 4 ≤ 2 * ((tow134 n).deg + T.deg) + 8
  rw [deg_tow135 n]
  omega

theorem lt_tow_Om135 (n : Nat) : lt (tow134 n) (Z zero) = true :=
  lt_tow_sc135 scTgt_Om135 (by show 1 + 1 ≤ 4; omega) n

theorem lt_tow_Om2_135 (n : Nat) : lt (tow134 n) (Z TM.Term.one) = true :=
  lt_tow_sc135 scTgt_Om2_135 (by show 1 + (1 + 1 + 1) ≤ 4; omega) n

theorem lt_tow_G0_135 (n : Nat) : lt (tow134 n) G094 = true :=
  lt_tow_sc135 scTgt_G0_135 (by show 1 + (1 + 1) + 1 ≤ 4; omega) n

theorem lt_Om_tow135 (n : Nat) : lt (Z zero) (tow134 n) = false :=
  ltF_Om_tow135 n _

theorem lt_G0_tow135 (n : Nat) : lt G094 (tow134 n) = false :=
  ltF_G0_tow135 n _

theorem beq_tow_ne135 : ∀ (n : Nat), ((tow134 n) == (Z zero)) = false
  | 0 => rfl
  | _ + 1 => rfl

theorem le_tow_Om135 (n : Nat) : le (tow134 n) (Z zero) = true := by
  show ((tow134 n == Z zero) || lt (tow134 n) (Z zero)) = true
  rw [lt_tow_Om135 n]; exact Bool.or_true _

theorem le_Om_tow135 (n : Nat) : le (Z zero) (tow134 n) = false := by
  show (((Z zero : Term) == tow134 n) || lt (Z zero) (tow134 n)) = false
  rw [lt_Om_tow135 n, show ((Z zero : Term) == tow134 n) = false from by cases n <;> rfl]
  rfl

/-! ### `ψ₁` の値の側 — `t` に依らない事実 -/

theorem ltF_addOm_Om135 (t : Term) : ∀ (f : Nat), ltF f (add (Z zero) t) (Z zero) = false
  | 0 => rfl
  | g + 1 => by rw [ltF_succ_add_Z135]; exact ltF_irrefl g (Z zero)

theorem ltF_y1_Om135 (t : Term) :
    ∀ (f : Nat), ltF f (phi zero (add (Z zero) t)) (Z zero) = false
  | 0 => rfl
  | g + 1 => by
      rw [ltF_succ_phi_Z135, ltF_addOm_Om135 t g]
      exact Bool.and_false _

theorem ltF_y2_Om135 (t : Term) :
    ∀ (f : Nat), ltF f (phi zero (phi zero (add (Z zero) t))) (Z zero) = false
  | 0 => rfl
  | g + 1 => by
      rw [ltF_succ_phi_Z135, ltF_y1_Om135 t g]
      exact Bool.and_false _

theorem ltF_Om_Om2_135 : ∀ (f : Nat), 2 ≤ f → ltF f (Z zero) (Z TM.Term.one) = true := by
  intro f hf
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [ltF_succ_Z_Z135, if_neg (by intro hc; exact Bool.noConfusion hc),
    if_pos (ltF_left_zero (f := g) (by omega) (by intro hc; exact Term.noConfusion hc)),
    starF_zero135 g]
  exact ltF_left_zero (by omega) (by intro hc; exact Term.noConfusion hc)

theorem ltF_y1_Om2_135 (t : Term) :
    ∀ (f : Nat), 4 ≤ f → ltF f (phi zero (add (Z zero) t)) (Z TM.Term.one) = true := by
  intro f hf
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  obtain ⟨h, rfl⟩ : ∃ h, g = h + 1 := ⟨g - 1, by omega⟩
  rw [ltF_succ_phi_Z135,
    ltF_left_zero (f := h + 1) (by omega) (by intro hc; exact Term.noConfusion hc),
    ltF_succ_add_Z135, ltF_Om_Om2_135 h (by omega)]
  rfl

theorem lt_y1_Om2_135 (t : Term) : lt (phi zero (add (Z zero) t)) (Z TM.Term.one) = true := by
  show ltF (fuelOf (phi zero (add (Z zero) t)) (Z TM.Term.one))
    (phi zero (add (Z zero) t)) (Z TM.Term.one) = true
  refine ltF_y1_Om2_135 t _ ?_
  show 4 ≤ 2 * ((phi zero (add (Z zero) t)).deg + (Z TM.Term.one).deg) + 8
  omega

theorem le_y1_Om135 (t : Term) : le (phi zero (add (Z zero) t)) (Z zero) = false := by
  show ((phi zero (add (Z zero) t) == Z zero) || lt (phi zero (add (Z zero) t)) (Z zero)) = false
  rw [show lt (phi zero (add (Z zero) t)) (Z zero) = false from ltF_y1_Om135 t _]
  rfl

theorem lt_y2_W135 (t : Term) : lt (phi zero (phi zero (add (Z zero) t))) (reg 1) = false :=
  ltF_y2_Om135 t _

/-! ### `omegaNF` と `logOm` — この節が通る三つの形だけ -/

theorem ltF_M_Z135 (e : Term) : ∀ (f : Nat), ltF f M (Z e) = false
  | 0 => rfl
  | _ + 1 => rfl

theorem ltF_M_phi135 (a b : Term) : ∀ (f : Nat), ltF f M (phi a b) = false
  | 0 => rfl
  | _ + 1 => rfl

theorem ltF_M_addOm135 (X : Term) : ∀ (f : Nat), ltF f M (add (Z zero) X) = false
  | 0 => rfl
  | g + 1 => by
      show ((M : Term) == Z zero || ltF g M (Z zero)) = false
      rw [ltF_M_Z135 zero g]
      rfl

theorem beq_phi_one135 {c d : Term} (h : (c == zero) = false) :
    (phi c d == TM.Term.one) = false := by
  cases hcd : (phi c d == TM.Term.one) with
  | false => rfl
  | true =>
      exfalso
      have he : phi c d = phi zero zero := eq_of_beq hcd
      injection he with h1 _
      rw [h1] at h
      exact absurd h (by decide)

/-- `⊕` の形の項では末尾の `1` が無いので `splitFin` は動かない。 -/
theorem splitFin_addOm135 {c d : Term} (h : (phi c d == TM.Term.one) = false) :
    splitFin (add (Z zero) (phi c d)) = (add (Z zero) (phi c d), 0) := by
  show (ofList (List.take (List.length [Z zero, phi c d]
          - (List.takeWhile (fun x => x == TM.Term.one)
              (List.reverse [Z zero, phi c d])).length) [Z zero, phi c d]),
        (List.takeWhile (fun x => x == TM.Term.one)
          (List.reverse [Z zero, phi c d])).length) = _
  rw [show List.reverse [Z zero, phi c d] = [phi c d, Z zero] from rfl,
    show List.takeWhile (fun x => x == TM.Term.one) [phi c d, Z zero] = [] from by
      show (match (phi c d == TM.Term.one) with
            | true => phi c d :: List.takeWhile (fun x => x == TM.Term.one) [Z zero]
            | false => []) = []
      rw [h]]
  rfl

theorem omegaNF_addOm135 {c d : Term} (h : (phi c d == TM.Term.one) = false) :
    omegaNF (add (Z zero) (phi c d)) = phi zero (add (Z zero) (phi c d)) := by
  show (if lt M (add (Z zero) (phi c d)) = true then omg (add (Z zero) (phi c d))
        else if ((add (Z zero) (phi c d) : Term) == M) = true then M
        else phiNF zero (add (Z zero) (phi c d))) = _
  rw [if_neg (by rw [show lt M (add (Z zero) (phi c d)) = false from ltF_M_addOm135 _ _]
                 exact Bool.noConfusion),
    if_neg (by intro hc; exact Bool.noConfusion hc)]
  show phiNFsucc zero (add (Z zero) (phi c d)) = _
  unfold phiNFsucc
  rw [splitFin_addOm135 h]
  rfl

theorem omegaNF_phi0_135 {Y : Term} (h : (phi zero Y == TM.Term.one) = false) :
    omegaNF (phi zero Y) = phi zero (phi zero Y) := by
  show (if lt M (phi zero Y) = true then omg (phi zero Y)
        else if ((phi zero Y : Term) == M) = true then M
        else phiNF zero (phi zero Y)) = _
  rw [if_neg (by rw [show lt M (phi zero Y) = false from ltF_M_phi135 zero Y _]
                 exact Bool.noConfusion),
    if_neg (by intro hc; exact Bool.noConfusion hc)]
  show (if ((phi zero Y).isSC && lt zero (phi zero Y)) = true then phi zero Y
        else if lt zero zero = true then phi zero Y
        else phiNFsucc zero (phi zero Y)) = _
  rw [if_neg (by intro hc; exact Bool.noConfusion hc),
    if_neg (by rw [lt_irrefl]; exact Bool.noConfusion)]
  unfold phiNFsucc
  rw [show splitFin (phi zero Y) = (phi zero Y, 0) from by
    show (ofList (List.take (1 - (List.takeWhile (fun x => x == TM.Term.one)
            (List.reverse [phi zero Y])).length) [phi zero Y]),
          (List.takeWhile (fun x => x == TM.Term.one)
            (List.reverse [phi zero Y])).length) = _
    rw [show List.reverse [phi zero Y] = [phi zero Y] from rfl,
      show List.takeWhile (fun x => x == TM.Term.one) [phi zero Y] = [] from by
        show (match (phi zero Y == TM.Term.one) with
              | true => phi zero Y :: List.takeWhile (fun x => x == TM.Term.one) []
              | false => []) = []
        rw [h]]
    rfl]
  rfl

theorem omegaNF_phi135 {c d : Term} (h : lt zero c = true) :
    omegaNF (phi c d) = phi c d := by
  show (if lt M (phi c d) = true then omg (phi c d)
        else if ((phi c d : Term) == M) = true then M
        else phiNF zero (phi c d)) = _
  rw [if_neg (by rw [show lt M (phi c d) = false from ltF_M_phi135 c d _]
                 exact Bool.noConfusion),
    if_neg (by intro hc; exact Bool.noConfusion hc)]
  show (if ((phi c d).isSC && lt zero (phi c d)) = true then phi c d
        else if lt zero c = true then phi c d
        else phiNFsucc zero (phi c d)) = _
  rw [if_neg (by intro hc; exact Bool.noConfusion hc), if_pos h]

theorem ne_of_beq_false135 {a b : Term} (h : (a == b) = false) : a ≠ b := by
  intro hc
  rw [hc] at h
  exact absurd h (by simp)

theorem lt_zero_of_ne135 {c : Term} (h : (c == zero) = false) : lt zero c = true :=
  ltF_left_zero (by show 1 ≤ 2 * ((zero : Term).deg + c.deg) + 8; omega)
    (ne_of_beq_false135 h)

/-! ### `ψ₁` を二回 -/

theorem collapse1_t135 {c d : Term} (hone : (phi c d == TM.Term.one) = false)
    (hW2 : lt (phi c d) (reg 2) = true) (hleOm : le (phi c d) (Z zero) = true) :
    collapse 1 (phi c d) = phi zero (add (Z zero) (phi c d)) := by
  show omegaNF (plus (reg 1) (plus
    (((wcnf (reg 2) (toList (phi c d))).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 2) (baseOf 1))).2.getD zero)
    ((wcnf (reg 2) (toList (phi c d))).2))) = _
  rw [show toList (phi c d) = [phi c d] from rfl, wcnf_cons_lt hW2]
  show omegaNF (plus (reg 1) (plus zero (ofList [phi c d]))) = _
  rw [show plus (reg 1) (plus zero (ofList [phi c d])) = add (Z zero) (phi c d) from by
    show ofList (List.filter (fun a => le (phi c d) a) [Z zero] ++ [phi c d]) = _
    rw [show List.filter (fun a => le (phi c d) a) [Z zero] = [Z zero] from by
      show (match le (phi c d) (Z zero) with
            | true => Z zero :: List.filter (fun a => le (phi c d) a) []
            | false => List.filter (fun a => le (phi c d) a) []) = [Z zero]
      rw [hleOm]
      rfl]
    rfl]
  exact omegaNF_addOm135 hone

theorem collapse1_y1_135 {c d : Term}
    (hW2 : lt (phi zero (add (Z zero) (phi c d))) (reg 2) = true)
    (hleOm : le (phi zero (add (Z zero) (phi c d))) (Z zero) = false) :
    collapse 1 (phi zero (add (Z zero) (phi c d)))
      = phi zero (phi zero (add (Z zero) (phi c d))) := by
  show omegaNF (plus (reg 1) (plus
    (((wcnf (reg 2) (toList (phi zero (add (Z zero) (phi c d))))).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 2) (baseOf 1))).2.getD zero)
    ((wcnf (reg 2) (toList (phi zero (add (Z zero) (phi c d))))).2))) = _
  rw [show toList (phi zero (add (Z zero) (phi c d)))
        = [phi zero (add (Z zero) (phi c d))] from rfl, wcnf_cons_lt hW2]
  show omegaNF (plus (reg 1) (plus zero (ofList [phi zero (add (Z zero) (phi c d))]))) = _
  rw [show plus (reg 1) (plus zero (ofList [phi zero (add (Z zero) (phi c d))]))
        = phi zero (add (Z zero) (phi c d)) from by
    show ofList (List.filter (fun a => le (phi zero (add (Z zero) (phi c d))) a) [Z zero]
      ++ [phi zero (add (Z zero) (phi c d))]) = _
    rw [show List.filter (fun a => le (phi zero (add (Z zero) (phi c d))) a) [Z zero] = [] from by
      show (match le (phi zero (add (Z zero) (phi c d))) (Z zero) with
            | true => Z zero :: List.filter
                (fun a => le (phi zero (add (Z zero) (phi c d))) a) []
            | false => List.filter (fun a => le (phi zero (add (Z zero) (phi c d))) a) []) = []
      rw [hleOm]
      rfl]
    rfl]
  exact omegaNF_phi0_135 (by rfl)

/-! ### `logOm`・`wA`・`wC` -/

theorem splitFin_phi0_135 {Y : Term} (h : (phi zero Y == TM.Term.one) = false) :
    splitFin (phi zero Y) = (phi zero Y, 0) := by
  show (ofList (List.take (List.length [phi zero Y]
          - (List.takeWhile (fun x => x == TM.Term.one)
              (List.reverse [phi zero Y])).length) [phi zero Y]),
        (List.takeWhile (fun x => x == TM.Term.one)
          (List.reverse [phi zero Y])).length) = _
  rw [show List.reverse [phi zero Y] = [phi zero Y] from rfl,
    show List.takeWhile (fun x => x == TM.Term.one) [phi zero Y] = [] from by
      show (match (phi zero Y == TM.Term.one) with
            | true => phi zero Y :: List.takeWhile (fun x => x == TM.Term.one) []
            | false => []) = []
      rw [h]]
  rfl

theorem phiShifted_addOm135 {c d : Term} (h : (phi c d == TM.Term.one) = false) :
    phiShifted zero (add (Z zero) (phi c d)) = false := by
  show (isFP zero (splitFin (add (Z zero) (phi c d))).1
        || (((add (Z zero) (phi c d) : Term) == zero) && (zero : Term).isSC)) = false
  rw [splitFin_addOm135 h]
  rfl

theorem phiShifted_phi0_135 {Y : Term} (h : (phi zero Y == TM.Term.one) = false) :
    phiShifted zero (phi zero Y) = false := by
  show (isFP zero (splitFin (phi zero Y)).1
        || (((phi zero Y : Term) == zero) && (zero : Term).isSC)) = false
  rw [splitFin_phi0_135 h]
  show ((((phi zero Y).isSC && lt zero (phi zero Y)) || lt zero zero)
        || (((phi zero Y : Term) == zero) && (zero : Term).isSC)) = false
  rw [lt_irrefl]
  rfl

theorem logOm_phi0_135 {Y : Term} (h : phiShifted zero Y = false) :
    logOm (phi zero Y) = Y := by
  show (if phiShifted zero Y = true then plus Y TM.Term.one else Y) = _
  rw [if_neg (by rw [h]; exact Bool.noConfusion)]

theorem omegaNF_zero135 : omegaNF (zero : Term) = TM.Term.one := rfl

theorem wA_y2_135 {c d : Term} (hone : (phi c d == TM.Term.one) = false)
    (hy1Om : lt (phi zero (add (Z zero) (phi c d))) (Z zero) = false)
    (hzc : lt zero c = true) :
    wA (reg 1) (phi zero (phi zero (add (Z zero) (phi c d)))) = phi c d := by
  show ofList (List.map (divAP (reg 1)) (List.filter (fun q => !lt q (reg 1))
    (toList (logOm (phi zero (phi zero (add (Z zero) (phi c d)))))))) = _
  rw [logOm_phi0_135 (phiShifted_phi0_135 (by rfl)),
    show toList (phi zero (add (Z zero) (phi c d)))
      = [phi zero (add (Z zero) (phi c d))] from rfl,
    show (List.filter (fun q => !lt q (reg 1)) [phi zero (add (Z zero) (phi c d))])
      = [phi zero (add (Z zero) (phi c d))] from by
      show (match (!lt (phi zero (add (Z zero) (phi c d))) (reg 1)) with
            | true => phi zero (add (Z zero) (phi c d))
                :: List.filter (fun q => !lt q (reg 1)) []
            | false => List.filter (fun q => !lt q (reg 1)) []) = _
      rw [show lt (phi zero (add (Z zero) (phi c d))) (reg 1) = false from hy1Om]
      rfl]
  show divAP (reg 1) (phi zero (add (Z zero) (phi c d))) = _
  show omegaNF (subAP (reg 1) (logOm (phi zero (add (Z zero) (phi c d))))) = _
  rw [logOm_phi0_135 (phiShifted_addOm135 hone)]
  show omegaNF (if ((Z zero : Term) == reg 1) = true then ofList [phi c d]
    else add (Z zero) (phi c d)) = _
  rw [if_pos (by rfl)]
  exact omegaNF_phi135 hzc

theorem wC_y2_135 {c d : Term}
    (hy1Om : lt (phi zero (add (Z zero) (phi c d))) (Z zero) = false) :
    wC (reg 1) (phi zero (phi zero (add (Z zero) (phi c d)))) = TM.Term.one := by
  show omegaNF (ofList (List.filter (fun q => lt q (reg 1))
    (toList (logOm (phi zero (phi zero (add (Z zero) (phi c d)))))))) = _
  rw [logOm_phi0_135 (phiShifted_phi0_135 (by rfl)),
    show toList (phi zero (add (Z zero) (phi c d)))
      = [phi zero (add (Z zero) (phi c d))] from rfl,
    show (List.filter (fun q => lt q (reg 1)) [phi zero (add (Z zero) (phi c d))])
      = [] from by
      show (match (lt (phi zero (add (Z zero) (phi c d))) (reg 1)) with
            | true => phi zero (add (Z zero) (phi c d))
                :: List.filter (fun q => lt q (reg 1)) []
            | false => List.filter (fun q => lt q (reg 1)) []) = _
      rw [show lt (phi zero (add (Z zero) (phi c d))) (reg 1) = false from hy1Om]
      rfl]
  exact omegaNF_zero135

/-! ### `ψ₀` の畳み込み — 桁が一つだけの場合 -/

theorem collapse0_L1_135 {c d : Term}
    (hone : (phi c d == TM.Term.one) = false)
    (hy1Om : lt (phi zero (add (Z zero) (phi c d))) (Z zero) = false)
    (hy2W : lt (phi zero (phi zero (add (Z zero) (phi c d)))) (reg 1) = false)
    (hleWt : le (reg 1) (phi c d) = false)
    (hzc : lt zero c = true) (hzt : lt zero (phi c d) = true) :
    collapse 0 (phi zero (phi zero (add (Z zero) (phi c d)))) = phi (phi c d) zero := by
  show omegaNF (plus (reg 0) (plus
    (((wcnf (reg 1) (toList (phi zero (phi zero (add (Z zero) (phi c d)))))).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero)
    ((wcnf (reg 1) (toList (phi zero (phi zero (add (Z zero) (phi c d)))))).2))) = _
  rw [show toList (phi zero (phi zero (add (Z zero) (phi c d))))
        = [phi zero (phi zero (add (Z zero) (phi c d)))] from rfl,
    wcnf_cons_ge hy2W]
  show omegaNF (plus (reg 0) (plus
    (([(wA (reg 1) (phi zero (phi zero (add (Z zero) (phi c d)))),
        wC (reg 1) (phi zero (phi zero (add (Z zero) (phi c d)))))].foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero) zero)) = _
  rw [wA_y2_135 hone hy1Om hzc, wC_y2_135 hy1Om]
  show omegaNF (plus (reg 0) (plus
    ((stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (phi c d, TM.Term.one)).2.getD zero) zero)) = _
  rw [show stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (phi c d, TM.Term.one) = ((none : Option Term), some (phi (phi c d) zero)) from by
      show (if le (reg 1) (phi c d) = true
        then (some (idxOf (reg 1) ((none : Option Term), (none : Option Term))
                (phi c d, TM.Term.one)),
              some (psi (reg 1) (idxOf (reg 1) ((none : Option Term), (none : Option Term))
                (phi c d, TM.Term.one))))
        else ((none : Option Term),
              some (phiNF (phi c d) (plus (baseOf 0) (sub1 TM.Term.one))))) = _
      rw [if_neg (by rw [hleWt]; exact Bool.noConfusion)]
      rfl]
  show omegaNF (plus (reg 0) (plus (phi (phi c d) zero) zero)) = _
  rw [show plus (reg 0) (plus (phi (phi c d) zero) zero) = phi (phi c d) zero from rfl]
  exact omegaNF_phi135 hzt

/-! ### 塔の一段 -/

theorem tow_form135 : ∀ (n : Nat), ∃ c : Term, tow134 n = phi c zero ∧ (c == zero) = false
  | 0 => ⟨two134, rfl, rfl⟩
  | k + 1 => ⟨tow134 k, rfl, by cases k <;> rfl⟩

theorem tow_step135 (n : Nat) :
    collapse 0 (collapse 1 (collapse 1 (tow134 n))) = phi (tow134 n) zero := by
  obtain ⟨c, hc, hcz⟩ := tow_form135 n
  have hone : (phi c zero == TM.Term.one) = false := beq_phi_one135 hcz
  have h1 : lt (phi c zero) (reg 2) = true := by
    rw [show (reg 2 : Term) = Z TM.Term.one from rfl, ← hc]; exact lt_tow_Om2_135 n
  have h2 : le (phi c zero) (Z zero) = true := by rw [← hc]; exact le_tow_Om135 n
  have h3 : le (reg 1) (phi c zero) = false := by
    rw [show (reg 1 : Term) = Z zero from rfl, ← hc]; exact le_Om_tow135 n
  have h4 : lt (phi zero (add (Z zero) (phi c zero))) (reg 2) = true := by
    rw [show (reg 2 : Term) = Z TM.Term.one from rfl]; exact lt_y1_Om2_135 _
  rw [hc, collapse1_t135 hone h1 h2, collapse1_y1_135 h4 (le_y1_Om135 _),
    collapse0_L1_135 hone (ltF_y1_Om135 _ _) (lt_y2_W135 _) h3 (lt_zero_of_ne135 hcz)
      (lt_zero_of_ne135 (show ((phi c zero) == zero) = false from rfl))]

theorem dict_Kg135 : ∀ (n : Nat), dict (Kg135 n) = tow134 n
  | 0 => rfl
  | k + 1 => by
      show collapse 0 (collapse 1 (collapse 1 (dict (Kg135 k)))) = tow134 (k + 1)
      rw [dict_Kg135 k]
      exact tow_step135 k

/-! ### `ψ₀` の畳み込み — 桁が二つ、先頭が強臨界 -/

/-- `Ω^Ω = dict bOO94`。 -/
def bigA135 : Term := phi zero (phi zero (add (Z zero) (Z zero)))

theorem dict_bOO135 : dict bOO94 = bigA135 := rfl

theorem phiNF_G0succ135 {t : Term} (h : lt t G094 = true) :
    phiNF t (add G094 TM.Term.one) = phi t G094 := by
  show (if (((add G094 TM.Term.one : Term)).isSC && lt t (add G094 TM.Term.one)) = true
        then add G094 TM.Term.one else phiNFsucc t (add G094 TM.Term.one)) = _
  rw [if_neg (by intro hc; exact Bool.noConfusion hc)]
  unfold phiNFsucc
  rw [show splitFin (add G094 TM.Term.one) = (G094, 1) from rfl]
  show (if (1 : Nat) ≥ 1 then
          (if (G094.isSC && lt t G094) = true
            then phi t (plus G094 (ofNat (1 - 1)))
            else phiNFdefault t (add G094 TM.Term.one))
        else phiNFdefault t (add G094 TM.Term.one)) = _
  rw [if_pos (by omega), show (G094.isSC && lt t G094) = lt t G094 from rfl, if_pos h]
  rfl

theorem wcnf_y2_135 {c d : Term} (hone : (phi c d == TM.Term.one) = false)
    (hy1Om : lt (phi zero (add (Z zero) (phi c d))) (Z zero) = false)
    (hy2W : lt (phi zero (phi zero (add (Z zero) (phi c d)))) (reg 1) = false)
    (hzc : lt zero c = true) :
    wcnf (reg 1) [phi zero (phi zero (add (Z zero) (phi c d)))]
      = ([(phi c d, TM.Term.one)], zero) := by
  rw [wcnf_cons_ge hy2W]
  show ([(wA (reg 1) (phi zero (phi zero (add (Z zero) (phi c d)))),
          wC (reg 1) (phi zero (phi zero (add (Z zero) (phi c d)))))], zero) = _
  rw [wA_y2_135 hone hy1Om hzc, wC_y2_135 hy1Om]

theorem wcnf_big_135 {c d : Term} (hone : (phi c d == TM.Term.one) = false)
    (hy1Om : lt (phi zero (add (Z zero) (phi c d))) (Z zero) = false)
    (hy2W : lt (phi zero (phi zero (add (Z zero) (phi c d)))) (reg 1) = false)
    (hzc : lt zero c = true) :
    wcnf (reg 1) [bigA135, phi zero (phi zero (add (Z zero) (phi c d)))]
      = ([(Z zero, TM.Term.one), (phi c d, TM.Term.one)], zero) := by
  rw [wcnf_cons_ge (show lt bigA135 (reg 1) = false from rfl),
    wcnf_y2_135 hone hy1Om hy2W hzc]
  show (if (wA (reg 1) bigA135 == phi c d) = true
        then ((wA (reg 1) bigA135, plus (wC (reg 1) bigA135) TM.Term.one) :: [], zero)
        else ((wA (reg 1) bigA135, wC (reg 1) bigA135)
              :: (phi c d, TM.Term.one) :: [], zero)) = _
  rw [if_neg (by intro hc; exact Bool.noConfusion hc),
    show wA (reg 1) bigA135 = Z zero from rfl,
    show wC (reg 1) bigA135 = TM.Term.one from rfl]

theorem collapse0_L2_135 {c d : Term}
    (hone : (phi c d == TM.Term.one) = false)
    (hy1Om : lt (phi zero (add (Z zero) (phi c d))) (Z zero) = false)
    (hy2W : lt (phi zero (phi zero (add (Z zero) (phi c d)))) (reg 1) = false)
    (hleWt : le (reg 1) (phi c d) = false)
    (hzc : lt zero c = true) (hzt : lt zero (phi c d) = true)
    (hG0 : lt (phi c d) G094 = true)
    (hleA : le (phi zero (phi zero (add (Z zero) (phi c d)))) bigA135 = true) :
    collapse 0 (plus bigA135 (phi zero (phi zero (add (Z zero) (phi c d)))))
      = phi (phi c d) G094 := by
  rw [show plus bigA135 (phi zero (phi zero (add (Z zero) (phi c d))))
        = add bigA135 (phi zero (phi zero (add (Z zero) (phi c d)))) from by
      show ofList (List.filter
        (fun a => le (phi zero (phi zero (add (Z zero) (phi c d)))) a) [bigA135]
        ++ [phi zero (phi zero (add (Z zero) (phi c d)))]) = _
      rw [show List.filter (fun a => le (phi zero (phi zero (add (Z zero) (phi c d)))) a)
            [bigA135] = [bigA135] from by
        show (match le (phi zero (phi zero (add (Z zero) (phi c d)))) bigA135 with
              | true => bigA135 :: List.filter
                  (fun a => le (phi zero (phi zero (add (Z zero) (phi c d)))) a) []
              | false => List.filter
                  (fun a => le (phi zero (phi zero (add (Z zero) (phi c d)))) a) []) = _
        rw [hleA]
        rfl]
      rfl]
  show omegaNF (plus (reg 0) (plus
    (((wcnf (reg 1) (toList (add bigA135
        (phi zero (phi zero (add (Z zero) (phi c d))))))).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero)
    ((wcnf (reg 1) (toList (add bigA135
        (phi zero (phi zero (add (Z zero) (phi c d))))))).2))) = _
  rw [show toList (add bigA135 (phi zero (phi zero (add (Z zero) (phi c d)))))
        = [bigA135, phi zero (phi zero (add (Z zero) (phi c d)))] from rfl,
    wcnf_big_135 hone hy1Om hy2W hzc]
  show omegaNF (plus (reg 0) (plus
    (([(Z zero, TM.Term.one), (phi c d, TM.Term.one)].foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero) zero)) = _
  rw [show ([((Z zero : Term), TM.Term.one), (phi c d, TM.Term.one)].foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0)))
      = ((some zero : Option Term), some (phi (phi c d) G094)) from by
    show stepF (reg 1) (baseOf 0)
      ((some zero : Option Term), (some G094 : Option Term)) (phi c d, TM.Term.one) = _
    show (if le (reg 1) (phi c d) = true
          then (some (idxOf (reg 1) ((some zero : Option Term), (some G094 : Option Term))
                  (phi c d, TM.Term.one)),
                some (psi (reg 1) (idxOf (reg 1)
                  ((some zero : Option Term), (some G094 : Option Term))
                  (phi c d, TM.Term.one))))
          else ((some zero : Option Term),
                some (phiNF (phi c d) (plus G094 TM.Term.one)))) = _
    rw [if_neg (by rw [hleWt]; exact Bool.noConfusion),
      show plus G094 TM.Term.one = add G094 TM.Term.one from rfl, phiNF_G0succ135 hG0]]
  show omegaNF (plus (reg 0) (plus (phi (phi c d) G094) zero)) = _
  rw [show plus (reg 0) (plus (phi (phi c d) G094) zero) = phi (phi c d) G094 from rfl]
  exact omegaNF_phi135 hzt

/-! ### `Ω^Ω` との比較 -/

theorem beq_phi_false135 {a b c d : Term} (h : (a == c) = false) :
    (phi a b == phi c d) = false := by
  cases hcd : (phi a b == phi c d) with
  | false => rfl
  | true =>
      exfalso
      have he : phi a b = phi c d := eq_of_beq hcd
      injection he with h1 _
      rw [h1] at h
      exact absurd h (by simp)

theorem beq_tow_zero135 : ∀ (n : Nat), ((tow134 n) == zero) = false
  | 0 => rfl
  | _ + 1 => rfl

theorem ltF_y2_bigA135 {t : Term} (h : (t == (Z zero)) = false) :
    ∀ (i : Nat), ltF (i + 3) (phi zero (phi zero (add (Z zero) t))) bigA135
      = ltF i t (Z zero) := by
  intro i
  have h1 : t ≠ Z zero := ne_of_beq_false135 h
  have h2 : add (Z zero) t ≠ add (Z zero) (Z zero) := by
    intro hc; injection hc with _ hb; exact h1 hb
  have h3 : phi zero (add (Z zero) t) ≠ phi zero (add (Z zero) (Z zero)) := by
    intro hc; injection hc with _ hb; exact h2 hb
  have h4 : phi zero (phi zero (add (Z zero) t))
      ≠ phi zero (phi zero (add (Z zero) (Z zero))) := by
    intro hc; injection hc with _ hb; exact h3 hb
  show ltF ((i + 2) + 1) (phi zero (phi zero (add (Z zero) t)))
    (phi zero (phi zero (add (Z zero) (Z zero)))) = _
  rw [ltF_succ_phi_phi (i + 2) h4, if_pos rfl,
    ltF_succ_phi_phi (i + 1) h3, if_pos rfl,
    ltF_succ_add_add i h2, if_pos rfl]

theorem le_y2_bigA_tow135 (n : Nat) :
    le (phi zero (phi zero (add (Z zero) (tow134 n)))) bigA135 = true := by
  have hdy : (phi zero (phi zero (add (Z zero) (tow134 n)))).deg = 7 + (tow134 n).deg := by
    show 1 + 1 + (1 + 1 + (1 + (1 + 1) + (tow134 n).deg)) = 7 + (tow134 n).deg
    omega
  obtain ⟨i, hi, hib⟩ : ∃ i, fuelOf (phi zero (phi zero (add (Z zero) (tow134 n)))) bigA135
      = i + 3 ∧ n + 4 ≤ i := by
    refine ⟨2 * ((phi zero (phi zero (add (Z zero) (tow134 n)))).deg + bigA135.deg) + 5, ?_, ?_⟩
    · show 2 * ((phi zero (phi zero (add (Z zero) (tow134 n)))).deg + bigA135.deg) + 8 = _
      omega
    · rw [hdy, show bigA135.deg = 9 from rfl, deg_tow135 n]
      omega
  show ((phi zero (phi zero (add (Z zero) (tow134 n))) == bigA135)
        || lt (phi zero (phi zero (add (Z zero) (tow134 n)))) bigA135) = true
  rw [show lt (phi zero (phi zero (add (Z zero) (tow134 n)))) bigA135 = true from by
    show ltF (fuelOf (phi zero (phi zero (add (Z zero) (tow134 n)))) bigA135)
      (phi zero (phi zero (add (Z zero) (tow134 n)))) bigA135 = true
    rw [hi, ltF_y2_bigA135 (beq_tow_ne135 n) i]
    exact ltF_tow_sc135 scTgt_Om135 n i hib]
  exact Bool.or_true _

/-! ### §134 の二つの義務 -/

theorem big_step135 (n : Nat) :
    collapse 0 (plus bigA135 (collapse 1 (collapse 1 (tow134 n)))) = phi (tow134 n) G094 := by
  obtain ⟨c, hc, hcz⟩ := tow_form135 n
  have hone : (phi c zero == TM.Term.one) = false := beq_phi_one135 hcz
  have h1 : lt (phi c zero) (reg 2) = true := by
    rw [show (reg 2 : Term) = Z TM.Term.one from rfl, ← hc]; exact lt_tow_Om2_135 n
  have h2 : le (phi c zero) (Z zero) = true := by rw [← hc]; exact le_tow_Om135 n
  have h3 : le (reg 1) (phi c zero) = false := by
    rw [show (reg 1 : Term) = Z zero from rfl, ← hc]; exact le_Om_tow135 n
  have h4 : lt (phi zero (add (Z zero) (phi c zero))) (reg 2) = true := by
    rw [show (reg 2 : Term) = Z TM.Term.one from rfl]; exact lt_y1_Om2_135 _
  have h5 : lt (phi c zero) G094 = true := by rw [← hc]; exact lt_tow_G0_135 n
  have h6 : le (phi zero (phi zero (add (Z zero) (phi c zero)))) bigA135 = true := by
    rw [← hc]; exact le_y2_bigA_tow135 n
  rw [hc, collapse1_t135 hone h1 h2, collapse1_y1_135 h4 (le_y1_Om135 _),
    collapse0_L2_135 hone (ltF_y1_Om135 _ _) (lt_y2_W135 _) h3 (lt_zero_of_ne135 hcz)
      (lt_zero_of_ne135 (show ((phi c zero) == zero) = false from rfl)) h5 h6]

theorem ltF_phiG0_one135 (t : Term) : ∀ (f : Nat), ltF f (phi t G094) TM.Term.one = false
  | 0 => rfl
  | g + 1 => by
      show ltF (g + 1) (phi t G094) (phi zero zero) = false
      rw [ltF_succ_phi_phi g (by intro hc; injection hc with _ h2; exact Term.noConfusion h2)]
      by_cases hz : t = zero
      · rw [if_pos hz, ltF_right_zero g G094]
      · rw [if_neg hz, ltF_right_zero g t, ltF_right_zero g (phi t G094)]
        rfl

/-- **§134 の閉じた形 — `ClosedFS134`。** -/
theorem closedFS135 (n : Nat) : vOf (fsB tGap107 n) = phi (tow134 n) G094 := by
  have hv : vOf (fsB tGap107 n) = plus TM.Term.one (dict (bVal (fsB tGap107 n))) := by
    rw [fsB_shape135 n]; rfl
  rw [hv, bVal_fsB135 n]
  show plus TM.Term.one (collapse 0 (plus (dict bOO94)
    (collapse 1 (collapse 1 (dict (Kg135 n)))))) = _
  rw [dict_bOO135, dict_Kg135 n, big_step135 n]
  show ofList (List.filter (fun a => le (phi (tow134 n) G094) a) [TM.Term.one]
    ++ [phi (tow134 n) G094]) = _
  rw [show List.filter (fun a => le (phi (tow134 n) G094) a) [TM.Term.one] = [] from by
    show (match le (phi (tow134 n) G094) TM.Term.one with
          | true => TM.Term.one :: List.filter (fun a => le (phi (tow134 n) G094) a) []
          | false => List.filter (fun a => le (phi (tow134 n) G094) a) []) = _
    rw [show le (phi (tow134 n) G094) TM.Term.one = false from by
      show ((phi (tow134 n) G094 == phi zero zero)
            || lt (phi (tow134 n) G094) TM.Term.one) = false
      rw [beq_phi_false135 (beq_tow_zero135 n),
        show lt (phi (tow134 n) G094) TM.Term.one = false from ltF_phiG0_one135 _ _]
      rfl]
    rfl]
  rfl

theorem ltF_rawT_G0_135 : ∀ (f : Nat), ltF f (phi G094 zero) G094 = false
  | 0 => rfl
  | g + 1 => by
      show (ltF g G094 G094 && ltF g zero G094) = false
      rw [ltF_irrefl]
      rfl

/-- **§134 の順序の側 — `TowBelow134`。** -/
theorem towBelow135 (n : Nat) : le (rawT94 0) (phi (tow134 n) G094) = false := by
  have hne : (G094 == tow134 n) = false := by cases n <;> rfl
  have hlt : lt (phi G094 zero) (phi (tow134 n) G094) = false := by
    show ltF (fuelOf (phi G094 zero) (phi (tow134 n) G094))
      (phi G094 zero) (phi (tow134 n) G094) = false
    obtain ⟨g, hg⟩ : ∃ g, fuelOf (phi G094 zero) (phi (tow134 n) G094) = g + 1 := by
      refine ⟨2 * ((phi G094 zero).deg + (phi (tow134 n) G094).deg) + 7, ?_⟩
      show 2 * ((phi G094 zero).deg + (phi (tow134 n) G094).deg) + 8 = _
      omega
    rw [hg, ltF_succ_phi_phi g (by intro hc; injection hc with _ h2; exact Term.noConfusion h2),
      if_neg (ne_of_beq_false135 hne),
      if_neg (by rw [ltF_G0_tow135 n g]; exact Bool.noConfusion),
      ltF_rawT_G0_135 g]
    rfl
  show ((phi G094 zero == phi (tow134 n) G094)
        || lt (phi G094 zero) (phi (tow134 n) G094)) = false
  rw [beq_phi_false135 hne, hlt]
  rfl

/-! ### 残る仮定なしの結論 -/

theorem closedFS134_135 : ClosedFS134 := closedFS135

theorem towBelow134_135 : TowBelow134 := towBelow135

/-- **§127 の `noReach127` から残る仮定が消える。** -/
theorem noReach135 (n : Nat) : le (rawT94 0) (vOf (fsB tGap107 n)) = false :=
  noReach_of_closed134 closedFS134_135 towBelow134_135 n

/-- **§135 の主定理 — `LimCofS1` は無条件に偽。** -/
theorem limCofS1_false_free135 : ¬ LimCofS1 := by
  intro H
  obtain ⟨n, hn⟩ := H tGap107 std127 lim127 (rawT94 0) inT_s127 lt_s_vOf127
  rw [noReach135 n] at hn
  exact Bool.noConfusion hn

/-- **証人つきの形。残る仮定は一つも無い。** -/
theorem limCofS1_witness135 :
    stdB1 tGap107 = true
    ∧ kindB tGap107 = BMS.Kind.lim
    ∧ matB tGap107 0 = [[0,0],[1,1],[2,1],[3,1],[1,1],[2,1],[3,0],[4,1],[5,1],[6,1]]
    ∧ rawT94 0 = phi (psi (Z zero) zero) zero
    ∧ inT (rawT94 0) = true
    ∧ lt (rawT94 0) (vOf tGap107) = true
    ∧ ∀ n, le (rawT94 0) (vOf (fsB tGap107 n)) = false :=
  ⟨std127, lim127, mat127, s127, inT_s127, lt_s_vOf127, noReach135⟩

#print axioms closedFS135
#print axioms towBelow135
#print axioms limCofS1_false_free135
#print axioms limCofS1_witness135

/-! ### §135.5 測定 — §134 が測った 40 段の先も一致する

証明は全ての `n` について立っているので、これは確認であって根拠ではない。 -/

#guard (List.range 61).all fun n => dict (Kg135 n) == tow134 n
#guard (List.range 61).all fun n => vOf (fsB tGap107 n) == phi (tow134 n) G094
#guard (List.range 61).all fun n => le (rawT94 0) (vOf (fsB tGap107 n)) == false
#guard bVal (fsB tGap107 7) == BT.D 0 (BT.sum bOO94 (BT.D 1 (BT.D 1 (Kg135 7))))
#guard dict bOO94 == bigA135

end

/-! ## §136 THE FIRST GATE'S RESIDUAL IS EMPTY UNDER THE LIBRARY'S OWN EXEMPTIONS, AND THE
       ONE EXEMPTION IT STILL NEEDED IS A SPLIT AT THE PREVIOUS INDEX

§132 cut `PsiIdxOKStd172` to one residual — `u = 0`, an argument carrying a level-one node,
and a firing step whose materials really read a coefficient set — and measured it at 402 of
the 12 436 standard level-`≤ 1` trees of size `≤ 13`.  It then named two ways to finish and
ruled the first circular.  §136 takes the second way as far as it goes at the `Term` level.

**IT DOES NOT CLOSE THE GATE.**  What it does is put §132's split next to the pointwise
exemptions the repository has already PROVED — §92.1, §100.2, §105.1, §105.2, §110.2,
§115.2, every one of them an unconditional statement about one `K`-element at one step — and
measure what is left.  Nobody had done that: those exemptions were built for the `IdxK··`
clause lineage and §132's split was built from `Kset` alone, and the two were never applied
to the same population.

  §136.1  **THE BUNDLE, AND ONE NEW MEMBER.**  `freeb136` is the disjunction of the six
          deciders; `lt_idxOf_of_freeb136` discharges one `K`-element from it with no
          hypothesis beyond what `wcnf_spec_sc` and `wcnf_coef_ne_zero119` already give at a
          pair of the fold.  Five of the six are quotations.  The sixth,
          `splitFree136` / `lt_idxOf_of_splitFree136`, is new and is one line of arithmetic:

              y = i₀ ⊕ r  and  r < Δ   ⟹   y < i₀ ⊕ Δ = i .

          §84.3's `SplitK84` offered `y ≤ i₀` OR `y < Δ ⊖ 1` and had nothing for an element
          that STRADDLES `i₀`; `restAfter136` peels `i₀` off `y` as a prefix of the component
          list and the decider checks `plus i₀ r == y` on the nose, so no ordering argument
          about the list is needed.  §79's `plus_smono_right_inT79` does the rest.

  §136.2  **THE ONE-TERM GATE** (`gateStd87_of_free136`, `gateStd87_of_hotb136`).  On a term
          whose firing materials are all in the bundle, `GateStd87 a` is a theorem.
          `PsiIdxOKStd172` is NOT used: `inT (dict a)` comes from §87.1's `inT_dict_ih87`,
          i.e. from the size induction, which is what makes this route non-circular.

  §136.3  **THE SPLIT** (`step073_of_hot136`, `psiIdxOKStd172_of_hot136`).  §132's residual
          gains one more conjunct — `hotb136 a = true`, "some firing step has a material the
          bundle does not take".  `hot135_of_step073` is the converse, so this is again a
          SPLIT and not a weakening.

  §136.4  **THE MEASUREMENT, AND IT IS THE POINT.**  On every population anyone has
          enumerated, **the residual is empty**:

            * all standard level-`≤ 1` trees with `BT.isStd (ψ₀ ·)` to size 15 — §132 leaves
              402, 838, 2494 at sizes 13, 14, 15; §136 leaves **0** at every size;
            * §132.5's nine constructed families to size 28 — §132 leaves 2455, §136 leaves
              **0**;
            * `pool136`, 7120 terms to size 30 built here around `aBad82`'s shape — §132
              leaves 925, §136 leaves **0**;
            * 64 075 terms to size 21 obtained by adding one summand inside a node of each
              of §132's 1240 residual terms of size `≤ 14` — 13 590 of them in §132's
              residual, §136 leaves **0**.

          **AND IT IS NOT A CLEAN SWEEP BY LUCK.**  Drop any one member of the bundle and
          somebody comes back.  On `pool136` alone: without §92.1, 8 terms; **without
          §136.1's split, 4**; without §100.2/§105.1, 6; without §105.2, 506; without
          §115.2, 1 — and that one is `surv115`, exactly as §115 said.  Only §110.2 is
          redundant everywhere, and §115 says why: its corrected decider takes everything
          §110's takes.

          `bad136` (20 symbols) is the smallest of the four that need the split:

              ψ₁ψ₁ψ₁ψ₁0 ⊕ ψ₁ψ₁ψ₁ψ₀(ψ₁ψ₁ψ₁ψ₁0 ⊕ ψ₁ψ₁ψ₁0)

          — `aBad82` with the `ψ₀` argument turned into a sum.  Its second firing step has a
          `K`-element equal to the accumulated index **plus exactly one**: `y = i₀ ⊕ 1`.
          §92.1's `y ≤ i₀` misses it by one notch, and every other member of the bundle
          measures `y` against `Δ` or against `Ω₁` and sees nothing.  That is the whole
          content of §136.1's new exemption, and 4 standard terms out of 20 704 need it.

WHAT IS **NOT** CLAIMED.  **The gate is NOT proved and NOT refuted.**  `hotb136` is a
decider, not a lemma: an empty count over 20 704 terms is not a proof over all of them, and
§115's own history says why one should not read it as one — §110 swept its populations clean
and §115 then BUILT the survivor by putting two halves together that no population carried at
once.  §136 is the same kind of statement §130 and §132 made, one population narrower.
`HiMono89` is untouched, `IdxLtStd88` is untouched, and the order-preservation route §132
called circular is still circular — §136 never compares two `dict` images.  Nothing here
touches §126's `¬ LimCofS1` or §127's matrix.

**THE LEDGER.**  §132 said the residual was "still §88's `IdxLtStd88`".  It is not, on
anything measurable: on 20 704 standard terms the obligation never reaches `IdxLtStd88` at
all, because six one-line arithmetic facts about `i₀`, `Ω₁`, `Ω₁^(A ⊖ Ω₁)` and `Δ` already
cover every element that ever escapes.  What §136 cannot say is that they always will.
-/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- §92.1 の免除 — 直前の指数以下。 -/
def prevFree136 (p : (Option Term × Option Term) × (Term × Term)) (y : Term) : Bool :=
  match p.1.1 with
  | none => false
  | some i0 => le y i0

/-- §100.2・§105.1 の免除 — `Ω₁` 以下。 -/
def regFree136 (p : (Option Term × Option Term) × (Term × Term)) (y : Term) : Bool :=
  lt y (reg 1) || (le y (reg 1) && !(subAP (reg 1) p.2.1 == zero))

/-- `y` から直前の指数 `i₀` を前置きとして剥がした残り。前置きでなければ意味を持たない —
    判定器の側で `plus i₀ r == y` を確かめる。 -/
def restAfter136 (i0 y : Term) : Term := ofList ((toList y).drop (toList i0).length)

/-- **§136.1 の新しい免除 — 分割。**  `y = i₀ ⊕ r` と書けて `r < Δ` なら
    `y < i₀ ⊕ Δ = i`。§84.3 の `SplitK84` は `y ≤ i₀` か `y < Δ ⊖ 1` の二択だったが、
    こちらは `i₀` を跨ぐ元をそのまま扱う。 -/
def splitFree136 (p : (Option Term × Option Term) × (Term × Term)) (y : Term) : Bool :=
  match p.1.1 with
  | none => false
  | some i0 =>
    (plus i0 (restAfter136 i0 y) == y) && inT (restAfter136 i0 y)
      && lt (restAfter136 i0 y) (ddOf75 (reg 1) p.2)

theorem lt_idxOf_of_splitFree136 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (h1 : inT ac.1 = true) (h3 : inT ac.2 = true)
    {y : Term} (hf : splitFree136 (s, ac) y = true) :
    lt y (idxOf (reg 1) s ac) = true := by
  cases hs1 : s.1 with
  | none =>
    rw [show splitFree136 (s, ac) y = false from by
      show (match s.1 with
            | none => false
            | some i0 => (plus i0 (restAfter136 i0 y) == y) && inT (restAfter136 i0 y)
                && lt (restAfter136 i0 y) (ddOf75 (reg 1) ac)) = false
      rw [hs1]] at hf
    exact Bool.noConfusion hf
  | some i0 =>
    rw [show splitFree136 (s, ac) y
        = ((plus i0 (restAfter136 i0 y) == y) && inT (restAfter136 i0 y)
            && lt (restAfter136 i0 y) (ddOf75 (reg 1) ac)) from by
      show (match s.1 with
            | none => false
            | some j => (plus j (restAfter136 j y) == y) && inT (restAfter136 j y)
                && lt (restAfter136 j y) (ddOf75 (reg 1) ac)) = _
      rw [hs1]] at hf
    obtain ⟨hp1, hlt⟩ := (Bool.and_eq_true _ _).mp hf
    obtain ⟨heq, hrT⟩ := (Bool.and_eq_true _ _).mp hp1
    have hi0 : inT i0 = true := (hst.1 i0 hs1).1
    have hdT : inT (ddOf75 (reg 1) ac) = true := inT_ddOf75 (inT_reg 1) h1 h3
    rw [idxOf_some92 hs1, ← eq_of_beq heq]
    exact plus_smono_right_inT79 i0 hi0 _ _ hrT hdT hlt

/-- **既に証明済みの「この元は只」判定器と §136.1 の分割を一本に束ねたもの。**
    §92.1・§136.1・§100.2・§105.1・§105.2・§110.2・§115.2。 -/
def freeb136 (p : (Option Term × Option Term) × (Term × Term)) (y : Term) : Bool :=
  prevFree136 p y || splitFree136 p y || regFree136 p y
    || powFree105 p y || coefFree110 p y || coefFreeU115 p y

/-- **§136.1 の主定理。** 束ねた判定器が通れば、その元の義務は無条件で片づく。 -/
theorem lt_idxOf_of_freeb136 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hl3 : lt ac.2 M = true)
    (hz : ac.2 ≠ zero) {y : Term}
    (hy : y ∈ Kset (reg 1) ac.1 ∨ y ∈ Kset (reg 1) ac.2)
    (hf : freeb136 (s, ac) y = true) (hidxT : inT (idxOf (reg 1) s ac) = true) :
    lt y (idxOf (reg 1) s ac) = true := by
  have hyT : inT y = true := by
    rcases hy with h | h
    · exact inT_mem_Kset75 ac.1 h1 (reg 1) y h
    · exact inT_mem_Kset75 ac.2 h3 (reg 1) y h
  rcases (Bool.or_eq_true _ _).mp hf with hA | h115
  · rcases (Bool.or_eq_true _ _).mp hA with hB | h110
    · rcases (Bool.or_eq_true _ _).mp hB with hC | h105
      · rcases (Bool.or_eq_true _ _).mp hC with hD | hreg
        · rcases (Bool.or_eq_true _ _).mp hD with hprev | hsplit
          · -- §92.1
            cases hs1 : s.1 with
            | none =>
              rw [show prevFree136 (s, ac) y = false from by
                show (match s.1 with | none => false | some i0 => le y i0) = false
                rw [hs1]] at hprev
              exact Bool.noConfusion hprev
            | some i0 =>
              refine lt_idxOf_of_le_prev92 (inT_reg 1) hst hs1 h1 h3 hz hyT hidxT ?_
              rw [show prevFree136 (s, ac) y = le y i0 from by
                show (match s.1 with | none => false | some i0 => le y i0) = _
                rw [hs1]] at hprev
              exact hprev
          · -- §136.1
            exact lt_idxOf_of_splitFree136 hst h1 h3 hsplit
        · -- §100.2 / §105.1
          rcases (Bool.or_eq_true _ _).mp hreg with hlt | hand
          · exact lt_idxOf_of_lt_reg100 hst h1 h3 hl3 hz hy hyT hlt hidxT
          · obtain ⟨hle, hsb⟩ := (Bool.and_eq_true _ _).mp hand
            have hsub : subAP (reg 1) ac.1 ≠ zero := by
              intro hcc
              rw [show (subAP (reg 1) ac.1 == zero) = true from by
                rw [hcc]; exact beq_self_eq_true _] at hsb
              exact Bool.noConfusion hsb
            exact lt_idxOf_of_le_reg105 hst h1 h3 hl3 hz hsub hy hyT hle hidxT
      · exact lt_idxOf_of_powFree105 hst h1 h3 hz hyT h105 hidxT
    · exact lt_idxOf_of_coefFree110 hst h1 h3 hl3 hz hyT h110 hidxT
  · exact lt_idxOf_of_coefFreeU115 hst h1 h3 hl3 hz hyT h115 hidxT

end

/-! ### §136.2 一項ぶんの門 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 発火する歩の材料の `K` の元がぜんぶ只であること。 -/
def FreeStep136 (a : BT) : Prop :=
  ∀ p ∈ scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1,
    le (reg 1) p.2.1 = true →
      ∀ y, (y ∈ Kset (reg 1) p.2.1 ∨ y ∈ Kset (reg 1) p.2.2) → freeb136 p y = true

/-- その否定の判定器 — まだ何かを負っている項。 -/
def hotb136 (a : BT) : Bool :=
  (scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1).any fun p =>
    le (reg 1) p.2.1 &&
      (Kset (reg 1) p.2.1 ++ Kset (reg 1) p.2.2).any (fun y => !(freeb136 p y))

theorem freeStep135_of_b {a : BT} (h : hotb136 a = false) : FreeStep136 a := by
  intro p hp hle y hy
  cases hfb : freeb136 p y with
  | true => rfl
  | false =>
    exfalso
    have hcon : hotb136 a = true := by
      refine List.any_eq_true.mpr ⟨p, hp, ?_⟩
      rw [hle, Bool.true_and]
      refine List.any_eq_true.mpr ⟨y, ?_, by rw [hfb]; rfl⟩
      rcases hy with hy | hy
      · exact List.mem_append.mpr (Or.inl hy)
      · exact List.mem_append.mpr (Or.inr hy)
    rw [hcon] at h
    exact Bool.noConfusion h

/-- **§136.2 の主定理。** 材料がぜんぶ只な項では、一項ぶんの門は無条件の定理。
    `PsiIdxOKStd172` は使わない — `inT (dict a)` は §87.1 の帰納法の仮説から来る。 -/
theorem gateStd87_of_free136 (a : BT)
    (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b)
    (H : btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → FreeStep136 a) : GateStd87 a := by
  intro hb hs
  have hin := inT_dict_ih87 a ih hb (isStd_of_D hs)
  obtain ⟨hcL, hdL⟩ := inT_toList (dict a) hin.1
  have hML := ltM_toList (dict a) hin.1 hin.2
  obtain ⟨_, hallOK⟩ :=
    wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList (dict a)) hcL hdL hML
  intro p hp hle
  refine scan_idx84 (wcnf (reg 1) (toList (dict a))).1 (none, none)
    stInv_none (kInv75_none 0) hallOK ?_ p hp hle
  intro q hq hle2 hst y hy
  obtain ⟨hi1, hl1, hi2, hl2⟩ := hallOK q.2 (scanSt_mem_snd _ _ _ _ q hq)
  obtain ⟨hidxT, _⟩ := inT_idxOf mulDescInT (inT_reg 1) (ltM_reg 1) hst hi1 hl1 hi2 hl2
  have hz : q.2.2 ≠ zero :=
    wcnf_coef_ne_zero119 (toList (dict a)) hcL hdL hML q.2 (scanSt_mem_snd _ _ _ _ q hq)
  exact lt_idxOf_of_freeb136 hst hi1 hi2 hl2 hz hy (H hb hs q hq hle2 y hy) hidxT

/-- 判定器を通す形。 -/
theorem gateStd87_of_hotb136 {a : BT}
    (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b)
    (h : hotb136 a = false) : GateStd87 a :=
  gateStd87_of_free136 a ih (fun _ _ => freeStep135_of_b h)

end

/-! ### §136.3 分割 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§136.3 の主定理。** §132 の残る仮定に、さらに「束ねた免除を外す歩を実際に持つ」
    が加わる。§132 の三つの条件はそのまま残っている。 -/
theorem step073_of_hot136
    (H : ∀ a : BT, btLe72 1 a = true → btLe72 0 a = false → BT.isStd (BT.D 0 a) = true →
          fireK132 a ≠ [] → hotb136 a = true → KsetStepOK 0 (dict a)) : PsiIdxStep073 := by
  refine step073_of_gate87 (fun a ih => ?_)
  cases hh : hotb136 a with
  | false => exact gateStd87_of_hotb136 ih hh
  | true =>
    intro hb hs
    cases hk : fireK132 a with
    | nil => exact gateStd87_of_fireNil132 hk hb hs
    | cons z zs =>
      cases h0 : btLe72 0 a with
      | true => exact ksetStepOK_zero130 a h0
      | false => exact H a hb h0 hs (by rw [hk]; exact List.cons_ne_nil z zs) hh

theorem psiIdxStepStd172_of_hot136
    (H : ∀ a : BT, btLe72 1 a = true → btLe72 0 a = false → BT.isStd (BT.D 0 a) = true →
          fireK132 a ≠ [] → hotb136 a = true → KsetStepOK 0 (dict a)) : PsiIdxStepStd172 :=
  psiIdxStepStd172_of_step073 (step073_of_hot136 H)

/-- **第一の残る仮定そのもの。** -/
theorem psiIdxOKStd172_of_hot136
    (H : ∀ a : BT, btLe72 1 a = true → btLe72 0 a = false → BT.isStd (BT.D 0 a) = true →
          fireK132 a ≠ [] → hotb136 a = true → KsetStepOK 0 (dict a)) : PsiIdxOKStd172 :=
  psiIdxOKStd172_of_step073 (step073_of_hot136 H)

/-- 逆向き — 分割が本当に分割であることの記録。緩めてはいない。 -/
theorem hot135_of_step073 (H : PsiIdxStep073) :
    ∀ a : BT, btLe72 1 a = true → btLe72 0 a = false → BT.isStd (BT.D 0 a) = true →
      fireK132 a ≠ [] → hotb136 a = true → KsetStepOK 0 (dict a) :=
  fun a hb _ hs _ _ => H a hb hs

end

/-! ### §136.4 測定 (凍結)

母集団は三つ。§130 の `stdTab130` を大きさ 15 まで全数で絞ったもの (§132 の残りが
3734 本)、§132.5 の `famPool132` (同 2455 本)、そして §136.4 で新しく組んだ `pool136`
(同 925 本、大きさ 30 まで)。**三つ合わせて 7114 本、束ねた免除を外すものは 0 本。** -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- §132 が残す母集団の判定器。 -/
def resid136 (a : BT) : Bool :=
  btLe72 1 a && !(btLe72 0 a) && BT.isStd (BT.D 0 a) && !((fireK132 a).isEmpty)

/-- §136 が残す母集団の判定器 — §132 の残りのうち、束ねた免除を外す歩を持つもの。 -/
def hot136 (a : BT) : Bool := resid136 a && hotb136 a

/-- 免除を一つずつ外した判定器 — どれが効いているかを測る。 -/
def hotb135W (f : (Option Term × Option Term) × (Term × Term) → Term → Bool)
    (a : BT) : Bool :=
  (scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1).any fun p =>
    le (reg 1) p.2.1 && (Kset (reg 1) p.2.1 ++ Kset (reg 1) p.2.2).any (fun y => !(f p y))

def noPrev136 (p : (Option Term × Option Term) × (Term × Term)) (y : Term) : Bool :=
  splitFree136 p y || regFree136 p y || powFree105 p y || coefFree110 p y || coefFreeU115 p y
def noSplit136 (p : (Option Term × Option Term) × (Term × Term)) (y : Term) : Bool :=
  prevFree136 p y || regFree136 p y || powFree105 p y || coefFree110 p y || coefFreeU115 p y
def noReg136 (p : (Option Term × Option Term) × (Term × Term)) (y : Term) : Bool :=
  prevFree136 p y || splitFree136 p y || powFree105 p y || coefFree110 p y || coefFreeU115 p y
def noPow136 (p : (Option Term × Option Term) × (Term × Term)) (y : Term) : Bool :=
  prevFree136 p y || splitFree136 p y || regFree136 p y || coefFree110 p y || coefFreeU115 p y
def noC110_136 (p : (Option Term × Option Term) × (Term × Term)) (y : Term) : Bool :=
  prevFree136 p y || splitFree136 p y || regFree136 p y || powFree105 p y || coefFreeU115 p y
def noC115_136 (p : (Option Term × Option Term) × (Term × Term)) (y : Term) : Bool :=
  prevFree136 p y || splitFree136 p y || regFree136 p y || powFree105 p y || coefFree110 p y

/-- `ψ₁` の塔。 -/
def tow136 (k : Nat) : BT := nst132 k BT.zero

/-- **新しい母集団。**  `aBad82` の形 — 二つの `ψ₁` 成分の和で、後ろの `ψ₀` の引数が
    それ自身 `ψ₁` の塔 — を軸に、引数を和にする方向へ広げたもの。 -/
def pool136 : List BT :=
  let R := List.range
  ((R 7).flatMap fun p => (R 7).flatMap fun m => (R 7).map fun k =>
      BT.sum (tow136 p) (nst132 m (BT.D 0 (tow136 k)))) ++
  ((R 7).flatMap fun p => (R 7).flatMap fun m => (R 7).map fun k =>
      BT.sum (nst132 m (BT.D 0 (tow136 k))) (tow136 p)) ++
  ((R 6).flatMap fun p => (R 6).flatMap fun q => (R 6).flatMap fun m => (R 6).map fun k =>
      BT.sum (tow136 p) (nst132 m (BT.D 0 (BT.sum (tow136 q) (tow136 k))))) ++
  ((R 6).flatMap fun p => (R 6).flatMap fun q => (R 6).flatMap fun m => (R 6).map fun k =>
      nst132 m (BT.sum (tow136 p) (BT.D 0 (BT.sum (tow136 q) (tow136 k))))) ++
  ((R 6).flatMap fun p => (R 6).flatMap fun q => (R 6).flatMap fun m => (R 6).map fun k =>
      BT.sum (nst132 m (BT.sum (tow136 p) (BT.D 0 (tow136 k)))) (tow136 q)) ++
  ((R 6).flatMap fun p => (R 6).flatMap fun q => (R 6).flatMap fun m => (R 6).map fun k =>
      BT.sum (nst132 m (BT.sum (tow136 p) (BT.sum (tow136 q) (BT.D 0 (tow136 k)))))
        (tow136 2)) ++
  ((R 5).flatMap fun p => (R 5).flatMap fun q => (R 5).flatMap fun m => (R 5).map fun k =>
      BT.sum (nst132 m (BT.D 0 (BT.sum (tow136 p) (BT.D 0 (tow136 k))))) (tow136 q)) ++
  ((R 5).flatMap fun p => (R 5).flatMap fun q => (R 5).flatMap fun m => (R 5).map fun k =>
      nst132 m (BT.sum (BT.D 0 (tow136 p)) (BT.sum (tow136 q) (BT.D 0 (tow136 k)))))

/-! **母集団の大きさ。** §132 の残りは大きさ 13 まで 402 本、14 で 838、15 で 2494 —
§130・§132 の列そのもの。 -/

#guard ((stdTab130 12).map fun l => l.countP resid136) ==
  [0, 0, 0, 0, 0, 0, 0, 1, 2, 7, 28, 91, 273]
#guard (((stdTab130 13).getD 13 []).countP resid136) == 838
#guard (((stdTab130 14).getD 14 []).countP resid136) == 2494
#guard (pool136.length, (pool136.map BT.size).foldl max 0, pool136.countP resid136)
  == (7120, 30, 925)
#guard famPool132.countP resid136 == 2455

/-! **§136 が残す母集団は、測ったところ空。**  段 1 以下の標準な木を大きさ 15 まで
全数、§132.5 の九つの族を大きさ 28 まで、`pool136` を大きさ 30 まで。 -/

#guard ((stdTab130 12).map fun l => l.countP hot136) ==
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#guard (((stdTab130 13).getD 13 []).countP hot136) == 0
#guard (((stdTab130 14).getD 14 []).countP hot136) == 0
#guard famPool132.countP hot136 == 0
#guard pool136.countP hot136 == 0

/-! **空回りしていない — 免除を一つ外すと必ず誰かが残る。**  行は
(全部, −§92.1, −§136.1, −§100.2/§105.1, −§105.2, −§110.2, −§115.2)。
`pool136` の 925 本では §92.1 が 8 本、**§136.1 の分割が 4 本**、§115.2 が 1 本を
一手に引き受けている。§110.2 だけはどの母集団でも余っている — §115.2 がその上位互換
だからで、§115 自身がそう言っている。 -/

#guard (let P := ((stdTab130 14).flatten).filter resid136
        (P.countP hotb136, P.countP (hotb135W noPrev136), P.countP (hotb135W noSplit136),
         P.countP (hotb135W noReg136), P.countP (hotb135W noPow136),
         P.countP (hotb135W noC110_136), P.countP (hotb135W noC115_136)))
  == (0, 0, 0, 39, 1962, 0, 0)

#guard (let P := pool136.filter resid136
        (P.countP hotb136, P.countP (hotb135W noPrev136), P.countP (hotb135W noSplit136),
         P.countP (hotb135W noReg136), P.countP (hotb135W noPow136),
         P.countP (hotb135W noC110_136), P.countP (hotb135W noC115_136)))
  == (0, 8, 4, 6, 506, 0, 1)

#guard (let P := famPool132.filter resid136
        (P.countP hotb136, P.countP (hotb135W noPrev136), P.countP (hotb135W noSplit136),
         P.countP (hotb135W noReg136), P.countP (hotb135W noPow136),
         P.countP (hotb135W noC110_136), P.countP (hotb135W noC115_136)))
  == (0, 0, 0, 9, 1667, 0, 0)

/-- **分割がちょうど引き受ける 4 本のうち、いちばん小さいもの (記号 20 個)。**
    `aBad82` の `ψ₀` の引数を和にしたもの。逃げる元は直前の指数 `i₀` の**ちょうど
    一つ上** `i₀ ⊕ 1` で、§92.1 の `y ≤ i₀` を一目盛りだけ外す。 -/
def bad136 : BT :=
  BT.sum (tow136 4) (nst132 3 (BT.D 0 (BT.sum (tow136 4) (tow136 3))))

#guard bad136.size == 20
#guard resid136 bad136
#guard hotb136 bad136 == false
#guard hotb135W noSplit136 bad136 == true
#guard hotb135W noPrev136 bad136 == false
#guard stepOKb 0 (dict bad136) == true
#guard pool136.contains bad136

/-! §132・§115 の名前つきの証人はどちらも新しい母集団の内側にある。
`aBad82` (記号 15) は §132 の残りに居て、§92.1 でも §136.1 でも只になる。
`surv115` (記号 30) は §115.2 でしか只にならない。 -/

#guard (resid136 aBad82, hotb136 aBad82, hotb135W noSplit136 aBad82,
        hotb135W noPrev136 aBad82) == (true, false, false, false)
#guard (resid136 surv115, hotb136 surv115, hotb135W noC115_136 surv115)
  == (true, false, true)

/-! **否定的な探索 — 生き残った 4 本を作った操作そのものを全部に当てる。**
大きさ 14 までの §132 の残り 1240 本の、どこかの節の引数に `ψ₁^j 0` (`j = 1…5`) を
足したもの 64 075 本 (大きさ 21 まで)。**13 590 本が §132 の残りに入り、§136 が残すのは
0 本。** -/

/-- どこかの節の引数に `ψ₁^j 0` を足す。 -/
def addIn136 (j : Nat) : BT → List BT
  | .zero => []
  | .D u e => (BT.D u (BT.sum e (tow136 j))) :: (addIn136 j e).map (fun x => BT.D u x)
  | .sum a b =>
      (addIn136 j a).map (fun x => BT.sum x b) ++ (addIn136 j b).map (fun x => BT.sum a x)

def mut136 : List BT :=
  (((stdTab130 13).flatten).filter resid136).flatMap fun a =>
    (List.range 5).flatMap fun j => addIn136 (j+1) a

#guard (((stdTab130 13).flatten).filter resid136).length == 1240
#guard (mut136.length, (mut136.map BT.size).foldl max 0,
        mut136.countP resid136, mut136.countP hot136) == (64075, 21, 13590, 0)

/-! **これは門の反証ではない。** 判定器そのものも、どの母集団でも一度も外れない。 -/

#guard pool136.countP (fun a => resid136 a && !(stepOKb 0 (dict a))) == 0
#guard famPool132.countP (fun a => resid136 a && !(stepOKb 0 (dict a))) == 0

#print axioms lt_idxOf_of_splitFree136
#print axioms lt_idxOf_of_freeb136
#print axioms gateStd87_of_free136
#print axioms step073_of_hot136
#print axioms psiIdxOKStd172_of_hot136

end

/-! ## §137 THE PUBLISHED TABLE HAS FIVE BROKEN ROWS, AND THEY ARE ONE DEFECT

§134 found `oR` overshoots at one matrix that the table does not carry.  §137 asks the same
question of every row that IS carried.  All 60 rows of `Rows.rows` were put through the test
that found the §134 break: expand the matrix with `BMS.expand`, translate each step's `oR`
value into naruyoko's `padicBotRathjen` notation, and compare against THEIR `fund` of the
row's own claimed value, under THEIR `equal` and `lessThan`.  Both readings of [R91] 2.7 were
carried through and agreed on all 60.

**54 healthy, 5 broken, 0 undecided, 1 not applicable (the empty matrix).**

    row 37   `(0,0)(1,1)(2,2)`                          `ψ_Ω(Z 1)`
    row 47   `(0,0)(1,1)(2,2)(2,0)(3,1)(4,2)`
    row 52   `(0,0)(1,1)(2,2)(2,2)`                     `ψ_Ω(Z 1 ⊕ Z 1)`
    row 53   `(0,0)(1,1)(2,2)(2,2)(2,2)`
    row 58   `(0,0)(1,1)(2,2)(3,0)(4,1)(5,2)`

Each shows the §134 signature exactly: every `oR (m[n])` for `n ≤ 9` is strictly below the
external `fund(v,0)`, and every member of `fund(v,·)` is at or above it.  The two sequences
cannot share a supremum.

**THE FIVE ARE ONE DEFECT.**  Each is a place where the fundamental sequence has to descend
through `Z 1`.  The external implementation treats `Z 1` as an inaccessible, `χ^M_0(0)`, and
descends with `ψ^{χ^M_0(0)}`; the BMS expansion treats it as `Ω₂` and descends with an
`ω`-tower.  That one difference accounts for all five.  **The other 15 rows containing `Z 1`
are healthy** — in those the fundamental sequence does not pass through `Z 1`.

**THE EXTERNAL NAMES THE REPLACEMENT FOR TWO OF THE FIVE.**

    row 37  →  `ψ_Ω(φ̄(1,Ω))`   — which is §69's own `sbad`, already in this repository
    row 58  →  `ψ_Ω(φ̄(0, Z 1 ⊕ ψ_Ω(φ̄(1,Ω))))`

Row 37's replacement is a strong internal corroboration rather than a new claim: §69.4b
already proved `lt_TW` and `le_sbad_psi_TW` — that `sbad` is above every member of the
expansion's value sequence and below `vOf tdiag` — without any hypothesis.  §137 is the
outside agreeing with §69 two years of sections later.  Rows 47, 52 and 53 cannot be named
from this audit: the substituted value either fails the external `inOT` (47) or comes out
below the expansion's own values (52, 53), because those expansion values themselves contain
`Z 1`.

**WHAT WAS RULED OUT, AND HOW.**

  * *the translation* — the dictionary is the measured one from `scripts/padicbot-ref.js`,
    the same one §134 used, and every term on both sides passed `inT` and `inOT`; 0 terms
    were unreadable;
  * *the expander* — all 590 expansion matrices were checked against yaBMS, 590/590;
  * *a misreading of the table* — `Trans.oR r.m = some r.t` for all 60 rows, in Lean;
  * *a shallow search* — the 15 healthy rows with the least margin were re-run with 10
    fundamental-sequence steps; every reach grew one-for-one and no stall appeared;
  * *a blunt instrument* — four controls behaved as designed: silent on a healthy row,
    firing when a value is inflated to `Γ₀`, firing on §127's witness at this repo's value,
    and silent on it at §134's value.

**WHAT §137 IS NOT.**  It is not a proof that the five values are wrong — the external
implementation is an independent implementation, not an oracle, and it carries no BMS
translation, so it cannot say which SIDE of the correspondence to correct.  It is evidence
strong enough that the five rows must not be read as settled.  They are marked in
`Rows/TM.lean` and therefore in the generated table.  **No value was changed**: three of the
five have no named replacement, and changing a published value is a bigger step than marking
one.

The rows below `Γ₀` — 36 of them — are all healthy, and 30 of those agree with the external
fundamental sequence term for term. -/

section
open Trans.Recal
open Trans.Dict (BT dict reg collapse)
open TM TM.Term
open Evidence.WF

/-- §137 が壊れていると判定した 5 行の行列。 -/
def brokenRows137 : List (List (List Nat)) :=
  [ [[0,0],[1,1],[2,2]],
    [[0,0],[1,1],[2,2],[2,0],[3,1],[4,2]],
    [[0,0],[1,1],[2,2],[2,2]],
    [[0,0],[1,1],[2,2],[2,2],[2,2]],
    [[0,0],[1,1],[2,2],[3,0],[4,1],[5,2]] ]

/-! 5 行とも表に載っている行である。 -/
#guard brokenRows137.all fun m => (Rows.rows.map (·.m)).contains m

/-! 行 37 について外部が名指した値は §69 の `sbad` そのもの。 -/

theorem ext37_is_sbad137 : psi (Z zero) (phi (phi zero zero) (Z zero)) = sbad := rfl

/-- 外部の読みは表の値より真に下にある。 -/
theorem ext37_lt_table137 : lt sbad (psi (Z zero) (Z (phi zero zero))) = true := rfl

/-! 表の値がその行のものであることの確認 — 読み違いではない。 -/
#guard (Rows.rows.find? fun r => r.m == [[0,0],[1,1],[2,2]]).map (·.t)
       == some (psi (Z zero) (Z (phi zero zero)))

end
end Evidence.Region
