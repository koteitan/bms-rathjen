import Evidence.RegionNext4

/-
Evidence/RegionNext5.lean — ROW 326'S REMAINING HYPOTHESES, SECOND HALF (§104-)

Split out of `RegionNext4` when that file passed 14000 lines.  Section numbers are not
in file order — sections were appended as their agents finished.
-/

namespace Evidence.Region

open BMS
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

/-! ## §108 THE WINDOW IS INSIDE `dict`'s RAW IMAGE — WHAT KEEPS IT OUT IS THE NORMAL
       FORM, NOT THE FOLD

§107 proved `DictDenseAbove102` false, built the finer step operator, showed it cannot be
pushed above `Γ₀`, and then named the clause everything now hangs on:

    `GapAtG0_107` :  no legal witness has a value in  `[φ̄(Γ₀,0), φ̄(Γ₀,Γ₀⊕1))`

measured on 570 + 88 legal witnesses with 0 exceptions, and NOT proved.  §107 also wrote out
the reason it believed:

> Above `Γ₀` the fold takes its strongly critical branch FIRST, so the base is `Γ₀`, and
> every later Veblen digit lands at `φ̄(a, Γ₀ ⊕ c)` with `c ≥ 1`.

§108 was asked to decide the clause.  **The clause is not decided.  Its stated reason is
REFUTED, the true reason is identified and half of it is now a theorem, and what is left is
one clause with no standardness in it.**

  §108.1  **THE WINDOW IS NOT EMPTY OF PREIMAGES.**  `bWin108 k = ψ₀(ψ₁ψ₁ψ₀Ω^Ω ⊕ … ⊕
          ψ₁ψ₁ψ₀Ω^Ω)` (`k+1` copies).  Its `dict` value is `φ̄(Γ₀, k)` — for `k ≥ 1`
          strictly inside the window, at the rung `k`.  It is level `≤ 1`, its components
          are `D 0`-headed, its value is `inT`, and `dict`'s OWN inverse names it:
          `dictInv_win108 : dictInv (φ̄(Γ₀,1)) = some (bWin108 1)`.  §94.6's raw tower had NO
          preimage at all (`dictInv (rawT94 n) = none`); the rungs above it have one.
          The single thing wrong with it is `BT.isStd`.

  §108.2  **AND THE THING WRONG WITH IT IS ONE ELEMENT OF `G₀`, IN GENERAL.**
          `needOO108` — if an element at or above `Ω^Ω` sits in `G(0, ·)` of the leading
          component's argument, then that argument must itself be strictly above `Ω^Ω`,
          because that is what `isStandardBuchholz` says.  The Veblen digit `Γ₀` is carried
          by `ψ₁ψ₁(ψ₀ Ω^Ω)`, which is BELOW `Ω^Ω` (§98's `lt_D1D1_bOO98`), and it drags
          `Ω^Ω` into `G(0,·)` with it.  `lt_sumD1D1_bOO108` says a sum led by that shape is
          still below `Ω^Ω` whatever the tail is, so `lead_notStd108` closes the whole route
          — **for every `x` whose coefficient set reaches `Ω^Ω` and every tail `r`** — and
          `notStd_bWin108` is the family above as its instance, at every rung `k`.
          `vStep_notStd108` is the same theorem for §107's finer operator, and §107's
          `vStep_bStep_not_std107` drops out of it (`vStep_bStep_of108`).

  §108.3  **§107'S STATED REASON IS NOT THE REASON.**  `phiNF_G0_one108 : φ̄(Γ₀,1) = φ̄(Γ₀,1)`
          — 2.6(vi)'s strongly critical clause degenerates only at second argument `0`, so
          `φ̄(Γ₀,·)` is emitted freely above it — and `dict_bWin108_1` exhibits a term whose
          fold puts `Γ₀` FIRST as a VEBLEN digit with coefficient 2 and lands at `φ̄(Γ₀,1)`.
          So the fold does NOT have to take its strongly critical branch first above `Γ₀`.
          What forces it to is the normal-form condition, one level up.

  §108.4  **WHAT THE REPAIR COSTS.**  Prefixing `Ω^Ω` restores standardness — that is §98's
          `bStep98` — and it moves the value from `φ̄(Γ₀,k)` to `φ̄(Γ₀, Γ₀⊕(k+1))`
          (`bWinOO108`, `dict_bWinOO108_0/1`).  `bWinOO108 0` IS `bTowG98 1`, the top of the
          window.  **The repair does not step into the window; it steps over the whole of
          it.**  That is the quantitative content of the gap.

  §108.5  **THE REDUCTION — THE STANDARDNESS HALF IS NOW A THEOREM.**  `ooLead108` : a legal
          witness whose value reaches `φ̄(Γ₀,0)` is strictly above `ψ₀(Ω^Ω)` in `BT.lt`.  It
          is proved, from `PsiIdxOKStd172` and `DictLtA74` — the two hypotheses row 326
          already carries — through §94.5's `btlt_of_lt94` and §107.5's `lt_G0_rawT0_107`.
          What is left is ONE clause, `SCFirst108`:

              once `ψ₀(Ω^Ω) < b`, the value of `ψ₀` jumps the window.

          `gap_of108 : SCFirst108 → GapAtG0_107`.  **The clause cannot be stated without
          standardness, and §108.5 proves that too** (`scFirstNoStd_false108`): `bad108 =
          ψ₀(Ω^Ω ⊕ 1) ⊕ bWin108 1` has a leading component BELOW the window, `plus` absorbs
          that leading component, and the whole term's value is §108.1's `φ̄(Γ₀,1)` — inside
          the window, with the hypothesis `ψ₀(Ω^Ω) < b` satisfied.  Only `isStd` removes it,
          and it removes it at the SECOND component, by `notStd_bWin108`.  Reducing
          `SCFirst108` further to its one-component form needs §93's bridge
          `toList (dict a) = (toL a).map dict` — §96's named residue — to see that a standard
          sum's components cannot outrun its leading one.  `FoldSkips108` is the 𝔗(M)-level
          form of the same statement, about `collapse 0` alone, which is the shape §109 should
          aim at; the bridge to it is the one order fact §103 already named as missing
          (`BT.lt` transported through `dict` at a `ψ₁`-HEADED term, which `btlt_of_lt94`
          cannot do — it needs `Hd085` on both sides).

WHAT IS **NOT** CLAIMED.  **`GapAtG0_107` is NOT proved and NOT refuted.**  `SCFirst108` and
`FoldSkips108` are measured, not proved.  `DictDenseMid107`, `DictDenseAbove107`,
`DictOntoMidOpen103`, `DictDenseHi94`, `DictDense85` and `CofDenseS1` are exactly where §107
left them; row 326's certificate is unchanged (`certIn_t326_107` still stands, and it is
still vacuous if the gap is a theorem).  `PsiIdxOKStd172` and `DictLtA74` are used, not
proved.  `bWin108` is NOT a counterexample to anything: it is not a legal witness, and §108
proves it is not, at every rung.

**Where §108 stopped, precisely, and what moved.**  §107 left "prove the fold's strongly
critical branch fires first".  §108 returns: **the fold does not fire it first — the normal
form does**, the normal-form half is now a theorem, and the residue is one clause about what
`collapse 0` does once its argument passes `Ω^Ω`.  A proof of `SCFirst108` needs what §89
needed: the accumulator's shape after the first `ψ_{Ω₁}` step, an induction along the digit
list carrying the invariant "the accumulator never enters the window", and an outer induction
for the tail `ρ`, since a coefficient inside the window would propagate one.  **A refutation
now has a precise shape too, and §108.1 says what it is**: a term whose leading base-`Ω₁`
digit is exactly `Γ₀` with coefficient `≥ 2` (or with a lower digit after it), whose argument
is nevertheless at or above `Ω^Ω` in `BT.lt`.  §108.2 proves that the canonical carrier of a
`Γ₀` digit is below `Ω^Ω` and drags `Ω^Ω` into `G(0,·)` with it, and §108.6's population E
shows by enumeration that up to size 14 there is no other carrier; what is NOT proved is that
there is none at all.

**AND IT IS §69'S FINDING AGAIN, ONE LEVEL UP.**  §69 found that `vOf tdiag = ψ_{Ω₁}(Ω₂)` is
not the supremum of its own fundamental sequence — `sbad = ψ_{Ω₁}(φ̄(1,Ω₁))` sits in the gap
between the sequence's values and the value.  §108's window sits in the gap between §94.6's
first raw rung and §98's first tower rung.  Both have the same shape: **𝔗(M) has terms the
Buchholz side cannot name, at exactly the places where the Buchholz side's own normal-form
condition forbids the naming** — there the expansion, here `isStandardBuchholz`.  §69's gap
is at the index/expansion level and §108's at the `dict`-image level, and if `GapAtG0_107` is
a theorem the two are one phenomenon measured twice: the region's value is bigger than what
the region's own machinery can reach.  §108 does not prove they are the same; it records that
they have the same shape and the same cause, and that §69's is the earlier sighting.

WHAT THE MEASUREMENT SAYS (§108.6 gives the construction).  Five populations.  §107's two are
reused unchanged (570 and 88 legal witnesses).  Three are new.  **C** is built to hit the
window: 13 DIGIT CARRIERS `ψ₁ψ₁ z` chosen so that `dict z` is exactly a base-`Ω₁` digit
exponent — `Ω₁`, `Γ₀`, `ε₀`, `ζ₀`, `Γ₀⊕1`, `φ̄(Γ₀,Γ₀⊕1)` — summed up to three at a time and
put under one `ψ₀` (1463 terms, 155 legal).  **D** exists because C is BLIND: every term of C
has a single `ψ₀` component, so no term of C has the shape of §108.5's counterexample.  D
sums 11 `ψ₀`-components up to three at a time (1463 terms, 164 legal).  **Neither C nor D is
filtered by standardness, which is the whole point.**  **E** is not a sample at all: it is
every standard level-`≤ 1` Buchholz term of size `≤ 12`, 9992 of them (`isStd` is hereditary,
so pruning at each size loses nothing).

  * **23 of C's 1463 and 420 of D's land in the window; 0 of C's 155 and 0 of D's 164 do.**
    Standardness is the only filter that removes them: all 23 of C's are level `≤ 1` and
    `D 0`-headed, and every one has `argHd < Ω^Ω` with an element at or above `Ω^Ω` in
    `G(0, argHd)` — one uniform reason, the one §108.2 proves.
  * **The proved half is visible, and the raw population shows it is doing work.**  The
    standardness half `c1b` holds on 155/155, 570/570, 88/88 and 164/164 legal terms — and on
    only 874 of C's 1463 RAW ones.  Its premise holds for 42, 163, 58 and 81 of them, so it
    is not vacuous.
  * **The residual clause needs standardness, and D shows it.**  Without `isStd` the clause
    breaks on 102 of D's 1463 terms — C could not see a single one.  With it: 1463/1463 on D,
    164/164, 155/155, 570/570 and 88/88, the premise firing on 81 of D's raw terms.
  * **The 𝔗(M)-level form holds.**  `FoldSkips108` on the arguments' values: 1463/1463 with
    the premise on 116, and 455/455 with the premise on 121 on §107's own pool.
  * **The family climbs the whole window and the repair jumps it.**  `dict (bWin108 (k+1)) =
    φ̄(Γ₀,k+1)` for `k ≤ 5`, every rung in the window and every rung non-standard; with the
    `Ω^Ω` prefix every rung is legal and at or above `φ̄(Γ₀,Γ₀⊕1)`.
  * **E settles the two facts §108.2's argument needs, by enumeration.**  Not one of the 9992
    standard terms has a value in the window.  And the carrier is UNIQUE: `Γ₀`, `Ω₁^Ω₁`,
    `Ω₁·Γ₀` and `Ω₁^Γ₀` each have exactly ONE standard preimage — `ψ₀(Ω^Ω)`, `Ω^Ω`,
    `ψ₁ψ₀(Ω^Ω)` and `ψ₁ψ₁ψ₀(Ω^Ω)`.  So the `Γ₀` digit can only be carried by the term
    §108.2 proves is below `Ω^Ω`, and a refutation would have to be a carrier that this
    enumeration does not reach.  (Extending E to size 14 — 58239 terms — gives the same
    four answers and the same 0.)
  * **The named endpoints, again.**  `dictInv` answers `some` at every rung of the window and
    `none` at every rung of §94.6's raw tower. -/


/-! ### §108.1 窓の中に値を持つ項 — 足りないのは標準性だけ

`Γ₀` の桁を運ぶ成分は `ψ₁ψ₁(ψ₀ Ω^Ω)` である。その値は `Ω₁^Γ₀`、つまり底 `Ω₁` の展開で
指数 `Γ₀`・係数 1 の桁ひとつ。これを `k+1` 個ならべて `ψ₀` を載せると、係数が `k+1` に
なり、畳み込みの最初の Veblen 段が `φ̄(Γ₀, sub1(k+1)) = φ̄(Γ₀, k)` を返す。
**`k ≥ 1` のとき、それは窓のちょうど中である。** -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse)
open TM TM.Term
open Evidence.WF

/-- **`Γ₀` の桁を運ぶ成分。**  `ψ₁ψ₁(ψ₀ Ω^Ω)`。値は `Ω₁^Γ₀`。 -/
def dgG0_108 : BT := BT.D 1 (BT.D 1 (BT.D 0 bOO94))

theorem dict_dgG0_108 : dict dgG0_108 = phi zero (phi zero (add (Z zero) G094)) := rfl

/-- 桁を `k+1` 個ならべたもの。 -/
def sumG0_108 : Nat → BT
  | 0 => dgG0_108
  | n + 1 => BT.sum dgG0_108 (sumG0_108 n)

/-- **窓の中に値を持つ項の族。** -/
def bWin108 (k : Nat) : BT := BT.D 0 (sumG0_108 k)

theorem hd085_bWin108 (k : Nat) : Hd085 (bWin108 k) := by
  intro z hz; exact ⟨sumG0_108 k, List.mem_singleton.mp hz⟩

theorem hd085_D0bOO108 : Hd085 (BT.D 0 bOO94) := by
  intro z hz; exact ⟨bOO94, List.mem_singleton.mp hz⟩

theorem btLe_bWin108 : ∀ k, btLe72 1 (bWin108 k) = true
  | 0 => rfl
  | k + 1 => by
      show (decide (0 ≤ 1) && (btLe72 1 dgG0_108 && btLe72 1 (sumG0_108 k))) = true
      have h : btLe72 1 (BT.D 0 (sumG0_108 k)) = true := btLe_bWin108 k
      have h' : btLe72 1 (sumG0_108 k) = true := by
        rw [show btLe72 1 (BT.D 0 (sumG0_108 k))
              = (decide (0 ≤ 1) && btLe72 1 (sumG0_108 k)) from rfl] at h
        exact ((Bool.and_eq_true _ _).mp h).2
      rw [h']; rfl

/-- 値は `Γ₀` のすぐ上の段を順に登る。段 0 だけは 2.6(vi) が `Γ₀` に潰す。 -/
theorem dict_bWin108_0 : dict (bWin108 0) = G094 := rfl
theorem dict_bWin108_1 : dict (bWin108 1) = phi G094 TM.Term.one := rfl
theorem dict_bWin108_2 : dict (bWin108 2) = phi G094 (TM.Term.ofNat 2) := rfl
theorem dict_bWin108_3 : dict (bWin108 3) = phi G094 (TM.Term.ofNat 3) := rfl

/-- **`dict` 自身の逆引きが、その項を名指しで返す。**  §94.6 の生の塔は
    `dictInv` が `none` を返した。窓の中の段はそうではない。 -/
theorem dictInv_win108 : dictInv (phi G094 TM.Term.one) = some (bWin108 1) := rfl

end

/-! ### §108.2 障害は `G₀` の条件で、しかも一般の定理

`isStandardBuchholz` は「`G(u,a)` の元はどれも `a` より下」と言う。`Γ₀` の桁を運ぶ成分
`ψ₁ψ₁(ψ₀ Ω^Ω)` は `Ω^Ω` より下 (§98 の `lt_D1D1_bOO98`) なのに、`Ω^Ω` を `G(0,·)` に
引きずり込む。だから `ψ₀` を載せると条件が破れる — **尾が何であっても、`x` が何であっても
である。** -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse)
open TM TM.Term
open Evidence.WF

/-- 先頭成分の引数。 -/
def argHd108 : BT → BT
  | BT.zero => BT.zero
  | BT.D _ a => a
  | BT.sum p _ => argHd108 p

theorem argHd_bWin108 (k : Nat) : argHd108 (bWin108 k) = sumG0_108 k := rfl

/-- 標準性は先頭成分の引数のところで `GB 0` を押さえる。 -/
theorem gbLead108 : ∀ b : BT, Hd085 b → BT.isStd b = true →
    ∀ e ∈ BT.GB 0 (argHd108 b), BT.lt e (argHd108 b) = true
  | BT.zero, _, _ => by intro e he; exact absurd he (List.not_mem_nil)
  | BT.D u a, hd, hs => by
      have hu : u = 0 := hd085_D94 hd
      subst hu
      have h : (BT.isStd a && (BT.GB 0 a).all (fun e => BT.lt e a)) = true := hs
      intro e he
      exact List.all_eq_true.mp ((Bool.and_eq_true _ _).mp h).2 e he
  | BT.sum p q, hd, hs =>
      gbLead108 p (hd085_sum94 hd).1 (isStd_of_sum hs).1

theorem bt_le_refl108 (x : BT) : BT.le x x = true := by
  show ((x == x) || BT.lt x x) = true
  rw [bt_beq_refl x]; rfl

/-- **§108.2 の主定理 (1)。**  `Ω^Ω` 以上の元が先頭成分の引数の係数集合にいるなら、
    その引数は `Ω^Ω` より真に上でなければならない。標準形の条件そのもの。 -/
theorem needOO108 {b : BT} (hd : Hd085 b) (hs : BT.isStd b = true)
    {e : BT} (he : e ∈ BT.GB 0 (argHd108 b)) (hle : BT.le bOO94 e = true) :
    BT.lt bOO94 (argHd108 b) = true := by
  have h1 : BT.lt e (argHd108 b) = true := gbLead108 b hd hs e he
  rcases (Bool.or_eq_true _ _).mp hle with h2 | h2
  · rw [bt_beq_eq77 h2]; exact h1
  · exact lt_trans83 h2 h1

/-- 頭が `Γ₀` の桁を運ぶ形なら、尾が何であれ和の全体は `Ω^Ω` より下。 -/
theorem lt_sumD1D1_bOO108 {x : BT} (hd : Hd085 x) (r : BT) :
    BT.lt (BT.sum (BT.D 1 (BT.D 1 x)) r) bOO94 = true := by
  refine btlt_of_hd106 (u := 1) (a := BT.D 1 x) (b := BT.D 1 (BT.Om 1))
    (ps := BT.toL r) (qs := []) rfl rfl ?_ ?_
  · exact bt_beq_false _ _ (fun h => by
      injection h with _ h2; exact ne_D1_hd098 hd BT.zero h2)
  · exact btlt_arg98 (bt_beq_false _ _ (ne_D1_hd098 hd BT.zero)) (btlt_hd0_D1_98 hd BT.zero)

/-- 桁をいくつならべても `Ω^Ω` より下のまま。 -/
theorem lt_sumG0_bOO108 : ∀ k, BT.lt (sumG0_108 k) bOO94 = true
  | 0 => lt_D1D1_bOO98 hd085_D0bOO108
  | k + 1 => lt_sumD1D1_bOO108 hd085_D0bOO108 (sumG0_108 k)

/-- `Ω^Ω` は桁の係数集合に入っている。 -/
theorem memOO_dgG0_108 : bOO94 ∈ BT.GB 0 dgG0_108 := by
  show bOO94 ∈ BT.D 1 (BT.D 0 bOO94) :: BT.D 0 bOO94 :: bOO94 :: BT.GB 0 bOO94
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

theorem memOO_sumG0_108 : ∀ k, bOO94 ∈ BT.GB 0 (sumG0_108 k)
  | 0 => memOO_dgG0_108
  | _ + 1 => List.mem_append_left _ memOO_dgG0_108

/-- **§108.2 の主定理 (2)。**  窓の中に値を持つ族は、どの段でも標準ではない。
    理由は畳み込みと関係がなく、`Ω^Ω` が係数集合にいるのに引数がそれより下だから。 -/
theorem notStd_bWin108 (k : Nat) : BT.isStd (bWin108 k) = false := by
  cases h : BT.isStd (bWin108 k) with
  | false => rfl
  | true =>
      exfalso
      have hx := needOO108 (hd085_bWin108 k) h (memOO_sumG0_108 k) (bt_le_refl108 bOO94)
      rw [argHd_bWin108 k, lt_asymm74 (lt_sumG0_bOO108 k)] at hx
      exact Bool.noConfusion hx

/-- **§108.2 の主定理 (3)。**  `Γ₀` の桁を先頭に置く道は、尾が何であれ閉じている
    — `x` にも尾 `r` にも条件はない。 -/
theorem lead_notStd108 {x : BT} (hd : Hd085 x) {e : BT} (he : e ∈ BT.GB 0 x)
    (hle : BT.le bOO94 e = true) (r : BT) :
    BT.isStd (BT.D 0 (BT.sum (BT.D 1 (BT.D 1 x)) r)) = false := by
  cases h : BT.isStd (BT.D 0 (BT.sum (BT.D 1 (BT.D 1 x)) r)) with
  | false => rfl
  | true =>
      exfalso
      have hd0 : Hd085 (BT.D 0 (BT.sum (BT.D 1 (BT.D 1 x)) r)) := by
        intro z hz; exact ⟨_, List.mem_singleton.mp hz⟩
      have hm : e ∈ BT.GB 0 (argHd108 (BT.D 0 (BT.sum (BT.D 1 (BT.D 1 x)) r))) := by
        show e ∈ (BT.D 1 x :: x :: BT.GB 0 x) ++ BT.GB 0 r
        exact List.mem_append_left _ (List.Mem.tail _ (List.Mem.tail _ he))
      have hx := needOO108 hd0 h hm hle
      rw [show argHd108 (BT.D 0 (BT.sum (BT.D 1 (BT.D 1 x)) r))
            = BT.sum (BT.D 1 (BT.D 1 x)) r from rfl,
        lt_asymm74 (lt_sumD1D1_bOO108 hd r)] at hx
      exact Bool.noConfusion hx

/-- **細かい作用素は `Ω^Ω` 以上の係数を持つ項の上で標準性を壊す — `x` は一般。** -/
theorem vStep_notStd108 {x : BT} (hd : Hd085 x) {e : BT} (he : e ∈ BT.GB 0 x)
    (hle : BT.le bOO94 e = true) : BT.isStd (vStep107 x) = false := by
  cases h : BT.isStd (vStep107 x) with
  | false => rfl
  | true =>
      exfalso
      have hm : e ∈ BT.GB 0 (argHd108 (vStep107 x)) := by
        show e ∈ BT.D 1 x :: x :: BT.GB 0 x
        exact List.Mem.tail _ (List.Mem.tail _ he)
      have hx := needOO108 (hd0_vStep107 x) h hm hle
      rw [show argHd108 (vStep107 x) = BT.D 1 (BT.D 1 x) from rfl,
        lt_asymm74 (lt_D1D1_bOO98 hd)] at hx
      exact Bool.noConfusion hx

/-- §107 の `vStep_bStep_not_std107` はその系である。 -/
theorem vStep_bStep_of108 (x : BT) : BT.isStd (vStep107 (bStep98 x)) = false :=
  vStep_notStd108 (hd0_bStep98 x) (by rw [gb0_bStep98]; exact List.Mem.head _)
    (by
      show ((bOO94 == bArg98 x) || BT.lt bOO94 (bArg98 x)) = true
      rw [show BT.lt bOO94 (bArg98 x) = true from btlt_self_sum98 1 (BT.D 1 x)]
      exact Bool.or_true _)

end

/-! ### §108.3 §107 の言う理由は理由ではない

2.6(vi) の強臨界の枝が `φ̄(A,·)` を潰すのは第 2 引数が `0` のときだけである。`1` では
潰さない。だから `Γ₀` の上でも畳み込みは Veblen 枝を先に取れるし、実際に取る。 -/

section
open Trans.Recal
open Trans.Dict (BT dict reg collapse)
open TM TM.Term
open Evidence.WF

/-- **強臨界の枝は第 2 引数 `0` のところにしかない。** -/
theorem phiNF_G0_one108 : phiNF G094 TM.Term.one = phi G094 TM.Term.one := rfl

/-- そして畳み込みは実際に `Γ₀` を最初の Veblen 桁として取り、`φ̄(Γ₀,1)` に着く。
    §107.5 の「強臨界枝が先に発火する」は、畳み込みの性質ではない。 -/
theorem foldTakesVeblen108 : collapse 0 (dict (sumG0_108 1)) = phi G094 TM.Term.one := rfl

end

/-! ### §108.4 前置の代価 — 直すと窓をまたぐ

標準性を直す方法は `Ω^Ω` を前に置くことである (§98 の `bStep98` がそれ)。すると底 `Ω₁`
の展開の先頭桁の指数が `Ω₁` になり、強臨界枝が先に発火して基底が `Γ₀` になる。値は
`φ̄(Γ₀,k)` から `φ̄(Γ₀, Γ₀⊕(k+1))` へ飛ぶ — **窓の中に降りるのではなく、窓をまたぐ。** -/

section
open Trans.Recal
open Trans.Dict (BT dict reg)
open TM TM.Term
open Evidence.WF

/-- `Ω^Ω` を前に置いて標準性を直した族。段 0 は §98 の塔の第 1 段そのもの。 -/
def bWinOO108 (k : Nat) : BT := BT.D 0 (BT.sum bOO94 (sumG0_108 k))

theorem bWinOO_zero108 : bWinOO108 0 = bTowG98 1 := rfl

theorem dict_bWinOO108_0 : dict (bWinOO108 0) = phi G094 (plus G094 TM.Term.one) := rfl
theorem dict_bWinOO108_1 : dict (bWinOO108 1) = phi G094 (plus G094 (TM.Term.ofNat 2)) := rfl

end

/-! ### §108.5 還元 — 標準性の側は定理、残るのは畳み込みの側 1 条項

`φ̄(Γ₀,0) ≤ dict b` なら `Γ₀ < dict b`、つまり `dict (ψ₀Ω^Ω) < dict b`。§94.5 の
`btlt_of_lt94` はそれを `BT.lt` に戻す — 両辺とも `D 0` 成分だけなので使える。
**だから隙間の標準性の側は定理である。** 残るのは畳み込みの側だけで、そこには
`isStd` がひとつも残っていない。 -/

section
open Trans.Recal
open Trans.Dict (BT dict reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§108.5 の主定理 (1) — 標準性の側は定理。**  値が窓の下端に届く正しい証人は
    `ψ₀(Ω^Ω)` より `BT.lt` で真に上にいる。 -/
theorem ooLead108 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) {b : BT} (hb : btLe72 1 b = true)
    (hs : BT.isStd b = true) (hd : Hd085 b) (hle : le (rawT94 0) (dict b) = true) :
    BT.lt (bTowG98 0) b = true := by
  have hib : inT (dict b) = true := (inT_dict_of_std172 Hp b hb hs).1
  have hlt : lt G094 (dict b) = true := by
    rcases (Bool.or_eq_true _ _).mp hle with h | h
    · rw [← eq_of_beq h]; exact lt_G0_rawT0_107
    · exact lt_trans_inT inT_G094_102 (inT_rawT98 0) hib lt_G0_rawT0_107 h
  refine btlt_of_lt94 Hp H2 (legal_bTowG98 0).1 (legal_bTowG98 0).2.1 (legal_bTowG98 0).2.2
    hb hs hd ?_
  rw [dict_bTowG98_zero]; exact hlt

/-- **残る条項。**  引数が `ψ₀(Ω^Ω)` を越えたら、`ψ₀` の値は窓をまるごと飛び越す。
    §107.5 の「強臨界枝が先に発火するので以後の Veblen 桁は `Γ₀ ⊕ c` (`c ≥ 1`) に着く」
    はここに集約される。**証明しない。** -/
def SCFirst108 : Prop := ∀ b : BT, btLe72 1 b = true → BT.isStd b = true → Hd085 b →
    BT.lt (bTowG98 0) b = true → le (rawT94 0) (dict b) = true →
    le (dict (bTowG98 1)) (dict b) = true

/-- 同じ条項から標準性を外したもの。 -/
def SCFirstNoStd108 : Prop := ∀ b : BT, btLe72 1 b = true → Hd085 b →
    BT.lt (bTowG98 0) b = true → le (rawT94 0) (dict b) = true →
    le (dict (bTowG98 1)) (dict b) = true

/-- `ψ₀(Ω^Ω ⊕ 1)` — 値は `φ̄(0,Γ₀)`、窓の下端より下。 -/
def smallB108 : BT := BT.D 0 (BT.sum bOO94 (BT.D 0 BT.zero))

/-- **手で作った反例。**  先頭成分の値は窓より下、第 2 成分は §108.1 の窓の中の項。
    和を取ると `plus` が先頭を吸収して、全体の値がそのまま窓の中に入る。 -/
def bad108 : BT := BT.sum smallB108 (bWin108 1)

theorem hd085_bad108 : Hd085 bad108 := by
  intro z hz
  have hm : z ∈ smallB108 :: bWin108 1 :: ([] : List BT) := hz
  rcases List.mem_cons.mp hm with h | h
  · exact ⟨_, h⟩
  · exact ⟨_, List.mem_singleton.mp h⟩

theorem dict_bad108 : dict bad108 = phi G094 TM.Term.one := rfl
theorem inWin_bad108 :
    (le (rawT94 0) (dict bad108) && lt (dict bad108) (dict (bTowG98 1))) = true := rfl

/-- **§108.5 の主定理 (2) — 条項から標準性は外せない。**  母集団は `ψ₀` ひとつぶんの
    項しか含まないのでこれを見つけられない (§93 の失敗の形)。手で作るしかない。 -/
theorem scFirstNoStd_false108 : ¬ SCFirstNoStd108 := by
  intro H
  have h := H bad108 (rfl : btLe72 1 bad108 = true) hd085_bad108
    (rfl : BT.lt (bTowG98 0) bad108 = true) (rfl : le (rawT94 0) (dict bad108) = true)
  rw [show le (dict (bTowG98 1)) (dict bad108) = false from rfl] at h
  exact Bool.noConfusion h

/-- そして `bad108` が正しい証人でないのは §108.2 の理由による — 第 2 成分が
    標準でないからで、`notStd_bWin108` がそれを言っている。 -/
theorem notStd_bad108 : BT.isStd bad108 = false := rfl

/-- **同じ主張を 𝔗(M) の側で。**  `collapse 0` だけの話で、Buchholz 側の語がひとつも
    入っていない — §109 が証明すべきはこちらの形である。**証明しない。**
    ただし `SCFirst108` からこちらへ渡す橋は repository にない: `BT.lt` を `dict` で
    運ぶ §94.5 の `btlt_of_lt94` は両辺に `Hd085` を要求し、`Ω^Ω` は `ψ₁` が頭なので
    その仮定を満たさない (§103 が名指しした穴と同じ)。 -/
def FoldSkips108 : Prop := ∀ X : Term, inT X = true → lt X M = true →
    le (dict bOO94) X = true → le (rawT94 0) (collapse 0 X) = true →
    le (dict (bTowG98 1)) (collapse 0 X) = true

/-- **§108.5 の主定理 (2) — 隙間は 1 条項に還元される。** -/
theorem gap_of108 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (H : SCFirst108) : GapAtG0_107 :=
  fun b hb hs hd hle => H b hb hs hd (ooLead108 Hp H2 hb hs hd hle) hle

/-! §107.5 の 5 つの帰結を、条項 1 本の形で書き直しておく。 -/

theorem denseMid107_false_of108 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (H : SCFirst108) :
    ¬ DictDenseMid107 := denseMid107_false_of_gap107 Hp H2 (gap_of108 Hp H2 H)

theorem denseMid102_false_of108 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (H : SCFirst108) :
    ¬ DictDenseMid102 := denseMid102_false_of_gap107 Hp H2 (gap_of108 Hp H2 H)

theorem dictDenseHi94_false_of108 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (H : SCFirst108) :
    ¬ DictDenseHi94 := dictDenseHi94_false_of_gap107 Hp H2 (gap_of108 Hp H2 H)

theorem dictDense85_false_of108 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (H : SCFirst108) :
    ¬ DictDense85 := dictDense85_false_of_gap107 Hp H2 (gap_of108 Hp H2 H)

theorem cofDenseS1_false_of108 (Hp : PsiIdxOKStd172) (H2 : DictLtA74) (H : SCFirst108) :
    ¬ CofDenseS1 := cofDenseS1_false_of_gap107 Hp H2 (gap_of108 Hp H2 H)

end

/-! ### §108.6 測定 (凍結)

**構成を先に書く。**  母集団は 3 つ。§107 の 2 つ (`popA107` 570 項・`popB107` 88 項) は
そのまま使い、3 つ目を新しく作る。3 つ目の種は **桁を運ぶ成分 13 個** — `ψ₁ψ₁ z` の
`dict z` がちょうど底 `Ω₁` の桁の指数になるように選んだもので、指数は
`Ω₁`・`Γ₀`・`ε₀`・`ζ₀`・`Γ₀⊕1`・`φ̄(Γ₀,Γ₀⊕1)`、それに `ψ₀` 成分と裸の `ψ₁` 成分。
これを 3 個までの和にして `ψ₀` を載せる (1463 項)。**標準性で濾さない** — 濾さないことが
この節の要点である。濾すと 155 項になる。 -/

section
open Trans.Recal
open Trans.Dict (BT dict dictInv reg collapse)
open TM TM.Term
open Evidence.WF

/-- 桁を運ぶ成分 — `ψ₁ψ₁ z` の `dict z` が桁の指数を決める。 -/
def carr108 : List BT :=
  [ bOO94,
    BT.D 1 (BT.D 1 (BT.D 0 bOO94)),
    BT.D 1 (BT.D 1 (BT.D 0 (BT.Om 1))),
    BT.D 1 (BT.D 1 (BT.D 0 (BT.D 1 (BT.Om 1)))),
    BT.D 1 (BT.D 1 (BT.sum (BT.D 0 bOO94) (BT.D 0 BT.zero))),
    BT.D 1 (BT.D 1 (BT.D 0 (BT.sum bOO94 (BT.D 1 (BT.D 1 (BT.D 0 bOO94)))))),
    BT.D 1 (BT.D 1 BT.zero), BT.D 1 (BT.D 1 (BT.Om 1)), BT.D 1 BT.zero, BT.D 1 (BT.Om 1),
    BT.D 0 bOO94, BT.D 0 (BT.Om 1), BT.D 0 BT.zero ]

def sumsC108 : Nat → List BT → List BT
  | 0, base => base
  | n + 1, base => (base.flatMap fun x => (sumsC108 n base).map fun y => BT.sum x y)
                     ++ sumsC108 n base
def rawC108 : List BT := ((sumsC108 2 carr108).map (fun a => BT.D 0 a)).eraseDups
def popC108 : List BT := rawC108.filter bgood94

/-- 窓 `[φ̄(Γ₀,0), φ̄(Γ₀,Γ₀⊕1))`。 -/
def inWin108 (d : Term) : Bool := le (rawT94 0) d && lt d (dict (bTowG98 1))
/-- §108.5 の証明ずみの側。 -/
def c1b_108 (b : BT) : Bool :=
  !(le (rawT94 0) (dict b)) || BT.lt (bTowG98 0) b
/-- 残る条項。 -/
def c2b_108 (b : BT) : Bool :=
  !(BT.lt (bTowG98 0) b && le (rawT94 0) (dict b)) || le (dict (bTowG98 1)) (dict b)
/-- 𝔗(M) 側の条項。 -/
def fold108 (X : Term) : Bool :=
  !(le (dict bOO94) X && le (rawT94 0) (collapse 0 X)) || le (dict (bTowG98 1)) (collapse 0 X)

#eval (rawC108.length, popC108.length)
#guard rawC108.length == 1463
#guard popC108.length == 155

/-! **窓に入るのは 1463 中 23 項、正しい証人では 0 項。** -/
#eval (rawC108.countP (fun b => inWin108 (dict b)),
       popC108.countP (fun b => inWin108 (dict b)))
#guard (rawC108.countP fun b => inWin108 (dict b)) == 23
#guard (popC108.countP fun b => inWin108 (dict b)) == 0

/-! **23 項を落とすのは標準性だけで、理由は 1 つ。**  どれも段 1 以下・成分は `D 0`、
    引数は `Ω^Ω` より下、なのに `G(0,·)` に `Ω^Ω` 以上の元がいる — §108.2 の形。 -/
#guard (rawC108.filter fun b => inWin108 (dict b)).all fun b =>
  btLe72 1 b && hd085B b && (BT.isStd b == false)
#guard (rawC108.filter fun b => inWin108 (dict b)).all fun b =>
  BT.lt (argHd108 b) bOO94 && (BT.GB 0 (argHd108 b)).any (fun e => BT.le bOO94 e)

/-! **証明ずみの側は空振りではなく、しかも標準性が効いている。**
    正しい証人では 155/155・570/570・88/88、濾していない 1463 項では 874 しか通らない。 -/
#eval (popC108.countP (fun b => le (rawT94 0) (dict b)),
       popA107.countP (fun b => le (rawT94 0) (dict b)),
       popB107.countP (fun b => le (rawT94 0) (dict b)))
#eval (popC108.countP c1b_108, popA107.countP c1b_108, popB107.countP c1b_108,
       rawC108.countP c1b_108)
#guard (popC108.countP c1b_108) == 155
#guard (popA107.countP c1b_108) == 570
#guard (popB107.countP c1b_108) == 88
#guard (rawC108.countP c1b_108) == 874

/-! **母集団 C では、標準性を外した条項も通ってしまう** — C の項は `ψ₀` 成分がひとつ
    しかないので、§108.5 の反例の形が入っていない。D がそれを直す。 -/
#eval (popC108.countP c2b_108, popA107.countP c2b_108, popB107.countP c2b_108,
       rawC108.countP c2b_108,
       rawC108.countP fun b => BT.lt (bTowG98 0) b && le (rawT94 0) (dict b))
#guard (popC108.countP c2b_108) == 155
#guard (popA107.countP c2b_108) == 570
#guard (popB107.countP c2b_108) == 88
#guard (rawC108.countP c2b_108) == 1463
#guard (rawC108.countP fun b => BT.lt (bTowG98 0) b && le (rawT94 0) (dict b)) == 76

/-! **𝔗(M) の側の形も通る。** -/
def vpopC108 : List Term := (rawC108.map argHd108).eraseDups.map dict
def vpopA108 : List Term := (popA107.map argHd108).eraseDups.map dict
#eval (vpopC108.length, vpopC108.countP fold108,
       vpopC108.countP (fun X => le (dict bOO94) X && le (rawT94 0) (collapse 0 X)),
       vpopA108.length, vpopA108.countP fold108,
       vpopA108.countP (fun X => le (dict bOO94) X && le (rawT94 0) (collapse 0 X)))
#guard vpopC108.countP fold108 == vpopC108.length
#guard vpopA108.countP fold108 == vpopA108.length
#guard (vpopC108.countP fun X => le (dict bOO94) X && le (rawT94 0) (collapse 0 X)) == 116
#guard (vpopA108.countP fun X => le (dict bOO94) X && le (rawT94 0) (collapse 0 X)) == 121

/-! **窓の段は全部 `dict` の生の像で、全部標準ではない。** -/
#guard (List.range 6).all fun k => dict (bWin108 (k+1)) == phi G094 (TM.Term.ofNat (k+1))
#guard (List.range 6).all fun k =>
  btLe72 1 (bWin108 (k+1)) && hd085B (bWin108 (k+1)) && inT (dict (bWin108 (k+1)))
#guard (List.range 6).all fun k => inWin108 (dict (bWin108 (k+1)))
#guard (List.range 6).all fun k => BT.isStd (bWin108 (k+1)) == false

/-! **`Ω^Ω` を前に置くと正しい証人になり、値は窓をまたぐ。** -/
#guard (List.range 6).all fun k => bgood94 (bWinOO108 k)
#guard (List.range 6).all fun k =>
  dict (bWinOO108 k) == phi G094 (plus G094 (TM.Term.ofNat (k+1)))
#guard (List.range 6).all fun k => le (dict (bTowG98 1)) (dict (bWinOO108 k))

/-! **母集団 D — 成分をふたつ以上持つ項。**  C は `ψ₀` ひとつぶんの項しか含まないので
    §108.5 の反例 `bad108` の形が見えない (§93 の失敗の形)。11 個の `ψ₀` 成分の和を
    3 個まで取って 1463 項。窓に入るのは 420 項、正しい証人では 0 項。 -/

def seedD108 : List BT :=
  [ BT.D 0 bOO94, bWin108 0, bWin108 1, bWin108 2, bWinOO108 0, bWinOO108 1, smallB108,
    BT.D 0 (BT.sum bOO94 (BT.D 1 (BT.D 1 (BT.D 0 (BT.Om 1))))),
    BT.D 0 (BT.Om 1), BT.D 0 BT.zero, BT.D 0 (BT.D 1 (BT.Om 1)) ]
def rawD108 : List BT := (sumsC108 2 seedD108).eraseDups
def popD108 : List BT := rawD108.filter bgood94
/-- 標準性を入れた残る条項。 -/
def c2c_108 (b : BT) : Bool :=
  !(BT.isStd b && BT.lt (bTowG98 0) b && le (rawT94 0) (dict b)) ||
    le (dict (bTowG98 1)) (dict b)

#eval (rawD108.length, popD108.length,
       rawD108.countP (fun b => inWin108 (dict b)),
       popD108.countP (fun b => inWin108 (dict b)))
#guard rawD108.length == 1463
#guard popD108.length == 164
#guard (rawD108.countP fun b => inWin108 (dict b)) == 420
#guard (popD108.countP fun b => inWin108 (dict b)) == 0

/-! **標準性は外せない。**  標準性なしの条項は 1463 中 102 項で破れる — `bad108` は
    そのひとつで、`SCFirstNoStd108` の反証はそれを名指しで使う。入れれば 1463/1463。 -/
#eval (rawD108.countP c2b_108, rawD108.countP c2c_108, popD108.countP c2c_108,
       rawD108.countP (fun b => BT.isStd b && BT.lt (bTowG98 0) b && le (rawT94 0) (dict b)),
       rawD108.countP (fun b => BT.lt (bTowG98 0) b && le (rawT94 0) (dict b)))
#guard (rawD108.countP c2b_108) == 1361
#guard (rawD108.countP c2c_108) == 1463
#guard (popD108.countP c2c_108) == 164
#guard (rawD108.countP fun b => BT.isStd b && BT.lt (bTowG98 0) b && le (rawT94 0) (dict b)) == 81

/-! **証明ずみの側も D で通り、隙間そのものも D で外れ 0。** -/
#guard (popD108.countP c1b_108) == 164
#guard (popD108.countP fun b => le (rawT94 0) (dict b) && !(le (dict (bTowG98 1)) (dict b))) == 0
#guard rawD108.contains bad108

/-! **母集団 E — 数え上げ。**  段 1 以下・標準な Buchholz 項を大きさ 12 まで全部
    (9992 項)。`isStd` は部分項へ遺伝するので、各段で標準なものだけを残しても
    数え落としはない。**窓に入る値はひとつもなく、`Γ₀` の桁を運ぶ成分はただひとつ。** -/

/-- `lv` の第 `i` 成分 = 大きさ `i+1` の標準・段 1 以下の項。 -/
def stepBT108 (lv : List (List BT)) : List (List BT) :=
  let n := lv.length
  let prev := lv.getD (n - 1) []
  let ds := prev.map (fun a => BT.D 0 a) ++ prev.map (fun a => BT.D 1 a)
  let ss := (List.range (n - 1)).flatMap fun i =>
      (lv.getD i []).flatMap fun a => (lv.getD (n - 2 - i) []).map fun b => BT.sum a b
  lv ++ [(ds ++ ss).filter BT.isStd]

def lvBT108 : Nat → List (List BT)
  | 0 => [[BT.zero]]
  | n + 1 => stepBT108 (lvBT108 n)

def allStd108 : List BT := (lvBT108 11).flatten

#eval ((lvBT108 11).map List.length, allStd108.length,
       allStd108.countP (fun z => btLe72 1 z && hd085B z))
#guard allStd108.length == 9992
#guard (allStd108.countP fun z => btLe72 1 z && hd085B z) == 2923

/-! **窓に入る標準な項は 9992 中 0 項。** -/
#guard (allStd108.countP fun z => inWin108 (dict z)) == 0

/-! **そして桁を運ぶ成分は一意である。**  `Γ₀`・`Ω₁^Ω₁`・`Ω₁·Γ₀`・`Ω₁^Γ₀` の
    どれも、大きさ 12 までの標準な項のなかに逆像はちょうど 1 つ。
    (大きさ 14 まで 58239 項に広げても答えは同じ。) -/
#guard (allStd108.filter fun z => dict z == G094) == [BT.D 0 bOO94]
#guard (allStd108.filter fun z => dict z == dict bOO94) == [bOO94]
#guard (allStd108.filter fun z => dict z == phi zero (add (Z zero) G094))
        == [BT.D 1 (BT.D 0 bOO94)]
#guard (allStd108.filter fun z => dict z == dict dgG0_108) == [dgG0_108]

/-! **窓の中の項は 𝔗(M) の項として本物で、逆引きも答える。** -/
#guard (List.range 6).all fun k =>
  inT (phi G094 (TM.Term.ofNat (k+1))) && (dictInv (phi G094 (TM.Term.ofNat (k+1)))).isSome
#guard (List.range 6).all fun n => (dictInv (rawT94 n)).isNone

end

/-! ## §110 THE RESIDUE IS A COEFFICIENT COMPARISON — `ω^E·` IS STRICTLY MONOTONE, AND WHAT
       `BT.isStd` BUYS IS EXACTLY THAT COMPARISON

§105 cut §100's residue with two exemptions, BUILT the survivor §100 could not exhibit, and
named the shape of what was left in one sentence: at the surviving steps `aV ⊖ Ω₁ ≠ 0`, the step
builds `Δ = Ω₁^(aV ⊖ Ω₁)·cV`, the escaping element is `y ≤ j = Ω₁^(aV ⊖ Ω₁)·c` at the SAME
power, and so `y < Δ` reduces to the COEFFICIENT COMPARISON `c < cV`.  §110 states that
comparison, proves the arithmetic that turns it into the obligation, and measures exactly what
it is worth.

**THE ARITHMETIC IS ONE STRICT MONOTONICITY, AND IT IS UNCONDITIONAL.**

    **`mulL_smono_right110` : `c < c'` ⟹ `ω^E·c < ω^E·c'`** — for every `E`, over all of
    𝔗(M) below `M`, no side condition, no `dict`, no `BT`, no gate.  `mulL E` writes each
    component `p` of its argument as `ω^(E ⊕ logOm p)`; that map is strictly monotone on
    additively principal terms (`logOm` is strictly monotone because `ω^·` inverts it —
    `logOm_smono110`, from §100's `omegaNF_logOm100`), and the order on 𝔗(M) reads the
    component list lexicographically (2.3.16), so the induction on the two lists closes.
    This is the piece §100 and §105 both looked for and did not find: it is neither of the two
    they named (`wcnf` reconstruction, `mulL`'s distributivity over `⊕`), and it does not need
    either of them.

**AND THE COEFFICIENT IS NAMEABLE.**  `coefOf110 E` divides a term by `ω^E` digit by digit
(`dropPre110` peels `E`'s component list off each exponent) — §106's `divAP_mulL106` is the
same idea at `E = Ω₁`, one component at a time.  That it really inverts `mulL E` is MEASURED,
not proved: `coefFree110` therefore does not assume the round trip, it CHECKS `y ≤ ω^E·c`
(and `inT c`, `lt c M`) so the theorem borrows nothing.  What the decidable form checks is
exactly the two things `lt_idxOf_of_coef110` needs, `y ≤ ω^E·c` and `c < cV`, and nothing else.

WHAT IS PROVED, UNCONDITIONALLY.

  §110.1  `toList_mulL110`, `logOm_smono110`, `dig_smono110`, `lt_mulL_smono110`,
          `mulL_smono_right110`.

  §110.2  `dropPre110`, `coef1_110`, `coefOf110`, `eOf110`, `ddOf_eq_mulL_eOf110`,
          `powOf_eq_omegaNF_eOf110`, **`lt_idxOf_of_coef110`** (the coefficient comparison as
          an exemption at a firing step), `mulL_one_eq_powOf110`, `lt_one_of_ne110`,
          `lt_idxOf_of_le_powOf110` (§105's second exemption, in its `cV ≠ 1` half, is the
          case `c = 1`),
          `coefFree110` and `lt_idxOf_of_coefFree110`.

  §110.3  `IdxK110` is `IdxK105` with ONE hypothesis added — `coefFree110 p y = false` — so the
          clause is a SUBSET of §105's (`idxK110_of_idxK105`) and §110 demonstrably adds no
          obligation.  `gateStd87_of_idxK110` consumes it at one term, `idxStd110_of_step073`
          is the converse (so `IdxStd110` is still EXACTLY the gate), and
          `psiIdxStep073_of_idxStd110` / `certIn_t326_idx110` re-hang row 326 — still on
          `DictLtStd92`, `HiMono89` and `LeIdxSelf95`, and now on `IdxStd110`.
          `CoefK110` / `CoefLtStd110` is the SAME clause with the conclusion rewritten as the
          coefficient comparison itself (`∃ z < cV, y ≤ ω^E·z`), and
          `gateStd87_of_coefK110` / `psiIdxStep073_of_coefLt110` / `certIn_t326_coef110`
          hang row 326 on that instead.  **`CoefLtStd110` is SUFFICIENT for the gate and is
          NOT shown equivalent to it** — it may be strictly stronger; `IdxStd110` is the one
          that is exactly the gate.

WHAT IS **NOT** CLAIMED.  The gate is NOT closed.  `IdxStd110` is EQUIVALENT to
`PsiIdxStep073`, as `IdxStd105`, `IdxStd100`, `IdxStd95`, `IdxStd92` and `IdxStd90` were.
`LeIdxSelf95`, `HiMono89` and `DictLtStd92` are untouched and still unproved — §110 did NOT
attempt `LeIdxSelf95`, and neither of the two pieces §100 named for it is supplied here.
`LocalK2Snd_78`, `IdxLtStd92`, `SplitK86`, `ArgStd87`, `CofDenseS1`, `BCofIn71` are untouched.
§86's wall stands: `lt_idxOf_of_coef110` compares `y` against `ω^E·c` and names the step; it
says nothing about `i₀` alone or `Δ` alone.  §105's FIRST exemption is **not** absorbed —
`coef_not_subsume110` shows the `y = Ω₁` obligation of `survA105` fails the coefficient
comparison and is still true, so the two exemptions are different theorems.

**§110 MOVED THE RESIDUE; IT DID NOT REMOVE IT** — and it moved it to a strictly smaller
object.  At the surviving steps the obligation was a comparison of `y` (an ordinal above `Ω₁`)
with the whole index; it is now a comparison of two ordinals BELOW `Ω₁`, the recovered
coefficient `c` against the step's own coefficient `cV`, and `shape110` shows that reduction is
uniform: over the 153 obligations that survive §105 on the 599 standard terms measured here,
EVERY one is at a first firing step, has `Ω₁^(aV ⊖ Ω₁) < y`, has `y = ω^E·c` on the nose (the
recovery is exact, 153/153), and has BOTH `c < Ω₁` and `cV < Ω₁`.  §105 described its own ten
survivors by `cV = ψ_{Ω₁}(j)` and `y = j`; widening the population shows those two are NOT
general (110/153 and 43/153).  What is general is the shape above — and it says the residual
obligation is a comparison of two COUNTABLE ordinals, where it used to be a comparison against
the whole index.

**AND THE ADVERSARY IS BUILT, NOT SWEPT.**  §105 said a `c < cV` clause "will have to survive"
nesting the slot one level deeper.  It does: `deep110`, `multi110` and `two110` push the `ψ₀`
argument down four levels, give it two firing steps of its own, and put two slots side by side
so the second step carries a previous index — 630 terms built, 289 qualifying, 149 obligations
surviving §105, **all 149 taken by the coefficient comparison.**  What breaks it is not depth
but standardness:

    `advC110 = survC105` **with the slot one level LOWER** (`slot105 0` for `slot105 1`)

is at level ≤ 1, its `dict` image is in 𝔗(M), and there the coefficient comparison is FALSE —
and so is the obligation, and so is the gate (`advC110_not_std`).  On the 84 built terms that
are `inT (dict ·)` but not standard, §105 leaves 150 obligations and the coefficient comparison
agrees with the obligation on **all 150** — 18 where both hold, 132 where both fail, and ZERO
disagreements in either direction.  On the standard side it is not a tautology either: of the
570 raw obligations over `corpus105` and `wideAdvQ110`, only 267 pass it.

**THE HONEST LIMIT — §110 IS WHERE §100 WAS.**  Over the 599 standard terms measured here
(`corpus105`, `wideAdvQ110`, `pairQ110`), §105's residue is 153 and §110 takes every one of
them, so **§110 cannot exhibit a surviving obligation on a standard term.**  That is exactly
the position §100 recorded and §105 broke by building one; the next section has to do the same
here.  `advC110` says where to look: a standard term whose surviving obligation has `cV ≤ c`.
Every term with that property found so far is non-standard, and at each of them the gate itself
fails — which is the same wall §105 hit from the other side with its 213 terms.
-/

/-! ### §110.1 `ω^E·` は狭義単調 — 係数の比較がそのまま積の比較になる -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- `mulL E` の成分列。§106 の `toList_mulLW106` を `Ω₁` 以外の底へ広げただけ。 -/
theorem toList_mulL110 {E A : Term} :
    toList (mulL E A) = (toList A).map (fun p => omegaNF (plus E (logOm p))) := by
  show toList (ofList ((toList A).map (fun p => omegaNF (plus E (logOm p))))) = _
  refine toList_ofList _ ?_
  intro x hx
  obtain ⟨p, _, hxp⟩ := List.mem_map.mp hx
  rw [← hxp]
  exact isAP_omegaNF _

/-- `logOm` は加法主要項の上で狭義単調 — `ω^·` がその逆だから。 -/
theorem logOm_smono110 {p q : Term} (hp : inT p = true) (hap : p.isAP = true)
    (hpM : lt p M = true) (hq : inT q = true) (haq : q.isAP = true) (hqM : lt q M = true)
    (h : lt p q = true) : lt (logOm p) (logOm q) = true := by
  have hlp : inT (logOm p) = true := inT_logOm hp
  have hlq : inT (logOm q) = true := inT_logOm hq
  rcases lt_trichotomy_inT hlp hlq with hc | hc | hc
  · exact hc.1
  · exfalso
    have := congrArg omegaNF hc.2.1
    rw [omegaNF_logOm100 hp hap hpM, omegaNF_logOm100 hq haq hqM] at this
    rw [this, lt_irrefl] at h
    exact Bool.noConfusion h
  · exfalso
    have h2 := lt_omegaNF_inT79 hlq hlp hc.2.2
    rw [omegaNF_logOm100 hp hap hpM, omegaNF_logOm100 hq haq hqM] at h2
    rw [lt_asymm_inT hq hp h2] at h
    exact Bool.noConfusion h

/-- 一桁ぶんの狭義単調性 — `p ↦ ω^(E ⊕ logOm p)`。 -/
theorem dig_smono110 {E p q : Term} (hE : inT E = true) (hp : inT p = true)
    (hap : p.isAP = true) (hpM : lt p M = true) (hq : inT q = true) (haq : q.isAP = true)
    (hqM : lt q M = true) (h : lt p q = true) :
    lt (omegaNF (plus E (logOm p))) (omegaNF (plus E (logOm q))) = true :=
  lt_omegaNF_inT79 (inT_plus hE (inT_logOm hp)) (inT_plus hE (inT_logOm hq))
    (plus_smono_right_inT79 E hE (logOm p) (logOm q) (inT_logOm hp) (inT_logOm hq)
      (logOm_smono110 hp hap hpM hq haq hqM h))


/-- **§110.1 の主定理 — `ω^E·` は狭義単調。**  係数の比較がそのまま積の比較になる。
    成分列は一桁ずつ狭義単調な像に写り、順序は成分列の辞書式だから、
    長さの帰納で通る。§105 が名指しした「係数の比較」の算術は、これ一本である。 -/
theorem lt_mulL_smono110 : ∀ (n : Nat) (E c c' : Term),
    (toList c).length + (toList c').length ≤ n →
    inT E = true → inT c = true → inT c' = true → lt c M = true → lt c' M = true →
    lt c c' = true → lt (mulL E c) (mulL E c') = true := by
  intro n
  induction n with
  | zero =>
      intro E c c' hn _ _ _ _ _ h
      exfalso
      cases hl : toList c' with
      | nil => rw [toList_eq_nil c' hl, lt_zero_right] at h; exact Bool.noConfusion h
      | cons b B => rw [hl, List.length_cons] at hn; omega
  | succ n ih =>
      intro E c c' hn hE hc hc' hcM hc'M h
      have hmT : inT (mulL E c) = true := inT_mulL mulDescInT hE hc
      have hmT' : inT (mulL E c') = true := inT_mulL mulDescInT hE hc'
      cases hl2 : toList c' with
      | nil =>
          exfalso
          rw [toList_eq_nil c' hl2, lt_zero_right] at h
          exact Bool.noConfusion h
      | cons b B =>
        have hib : inT b = true := inTL_inT hc' b (by rw [hl2]; exact List.Mem.head _)
        have hapb : b.isAP = true := inTL_isAP hc' b (by rw [hl2]; exact List.Mem.head _)
        have hbM : lt b M = true := ltM_toList c' hc' hc'M b (by rw [hl2]; exact List.Mem.head _)
        have hT2 : toList (mulL E c')
            = (fun p => omegaNF (plus E (logOm p))) b
              :: B.map (fun p => omegaNF (plus E (logOm p))) := by
          rw [toList_mulL110, hl2, List.map_cons]
        cases hl1 : toList c with
        | nil =>
            have hz : c = zero := toList_eq_nil c hl1
            subst hz
            rw [show mulL E (zero : Term) = zero from rfl]
            refine lt_zero_left ?_
            intro hcc
            rw [hcc, show toList (zero : Term) = [] from rfl] at hT2
            exact List.cons_ne_nil _ _ hT2.symm
        | cons a A =>
          have hia : inT a = true := inTL_inT hc a (by rw [hl1]; exact List.Mem.head _)
          have hapa : a.isAP = true := inTL_isAP hc a (by rw [hl1]; exact List.Mem.head _)
          have haM : lt a M = true := ltM_toList c hc hcM a (by rw [hl1]; exact List.Mem.head _)
          have hT1 : toList (mulL E c)
              = (fun p => omegaNF (plus E (logOm p))) a
                :: A.map (fun p => omegaNF (plus E (logOm p))) := by
            rw [toList_mulL110, hl1, List.map_cons]
          rcases lt_trichotomy_inT hia hib with hab | hab | hab
          · exact lt_of_hd_lt hmT hmT' hT1 hT2
              (dig_smono110 hE hia hapa haM hib hapb hbM hab.1)
          · -- 頭が同じ — 尾部へ落ちる
            have hEq := hab.2.1
            subst hEq
            obtain ⟨hcl1, hdl1⟩ := inT_toList c hc
            obtain ⟨hcl2, hdl2⟩ := inT_toList c' hc'
            rw [hl1] at hcl1 hdl1
            rw [hl2] at hcl2 hdl2
            have hcA : inTL A = true := (inTL_cons.mp hcl1).2
            have hcB : inTL B = true := (inTL_cons.mp hcl2).2
            have hiA : inT (ofList A) = true := inT_ofList A hcA (descL_tail hdl1)
            have hiB : inT (ofList B) = true := inT_ofList B hcB (descL_tail hdl2)
            have htA : toList (ofList A) = A := toList_ofList89 hcA
            have htB : toList (ofList B) = B := toList_ofList89 hcB
            have hAM : lt (ofList A) M = true :=
              ltM_ofList99 A (fun x hx =>
                ltM_toList c hc hcM x (by rw [hl1]; exact List.Mem.tail _ hx))
            have hBM : lt (ofList B) M = true :=
              ltM_ofList99 B (fun x hx =>
                ltM_toList c' hc' hc'M x (by rw [hl2]; exact List.Mem.tail _ hx))
            have hAB : lt (ofList A) (ofList B) = true := by
              rcases lt_trichotomy_inT hiA hiB with hq | hq | hq
              · exact hq.1
              · exfalso
                have hAB2 : A = B := by rw [← htA, ← htB, hq.2.1]
                have hcc : c = c' := by
                  rw [← inT_ofList_toList c hc, ← inT_ofList_toList c' hc', hl1, hl2, hAB2]
                rw [hcc, lt_irrefl] at h
                exact Bool.noConfusion h
              · exfalso
                have h2 : lt c' c = true := lt_of_hd_eq77 hc' hc hl2 hl1 hq.2.2
                rw [lt_asymm_inT hc' hc h2] at h
                exact Bool.noConfusion h
            have hlen : A.length + B.length ≤ n := by
              rw [hl1, hl2, List.length_cons, List.length_cons] at hn
              omega
            have hkey := ih E (ofList A) (ofList B)
              (by rw [htA, htB]; exact hlen) hE hiA hiB hAM hBM hAB
            have hmA : mulL E (ofList A)
                = ofList (A.map (fun p => omegaNF (plus E (logOm p)))) := by
              show ofList ((toList (ofList A)).map _) = _
              rw [htA]
            have hmB : mulL E (ofList B)
                = ofList (B.map (fun p => omegaNF (plus E (logOm p)))) := by
              show ofList ((toList (ofList B)).map _) = _
              rw [htB]
            rw [hmA, hmB] at hkey
            exact lt_of_hd_eq77 hmT hmT' hT1 hT2 hkey
          · exfalso
            have h2 : lt c' c = true :=
              lt_of_hd_lt hc' hc hl2 hl1 hab.2.2
            rw [lt_asymm_inT hc' hc h2] at h
            exact Bool.noConfusion h

/-- **狭義単調性、量化子を外した形。** -/
theorem mulL_smono_right110 {E c c' : Term} (hE : inT E = true) (hc : inT c = true)
    (hc' : inT c' = true) (hcM : lt c M = true) (hc'M : lt c' M = true)
    (h : lt c c' = true) : lt (mulL E c) (mulL E c') = true :=
  lt_mulL_smono110 ((toList c).length + (toList c').length) E c c' (Nat.le_refl _)
    hE hc hc' hcM hc'M h

end

/-! ### §110.2 係数を復元する — `ω^E` で割る、判定できる形 -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- 成分列の先頭から `E` の成分列を剥がす。合わなければそこで止める。 -/
def dropPre110 : List Term → List Term → List Term
  | [], l => l
  | _ :: _, [] => []
  | a :: s, b :: t => if a == b then dropPre110 s t else b :: t

/-- 一桁ぶんの割り算 `ω^(E ⊕ g) ↦ ω^g`。§106 の `divAP` を、底が和でもよい形へ広げたもの。 -/
def coef1_110 (E q : Term) : Term :=
  omegaNF (ofList (dropPre110 (toList E) (toList (logOm q))))

/-- **`ω^E ·` の逆。**  `mulL E` が桁ごとに `E` を足すだけなので、桁ごとに剥がせば戻る。 -/
def coefOf110 (E x : Term) : Term := ofList ((toList x).map (coef1_110 E))

/-- 一歩が立てる冪の指数 `E = Ω₁·(aV ⊖ Ω₁)` — `Δ = mulL E cV`、`Ω₁^(aV ⊖ Ω₁) = ω^E`。 -/
def eOf110 (ac : Term × Term) : Term := mulL (reg 1) (subAP (reg 1) ac.1)

theorem ddOf_eq_mulL_eOf110 (ac : Term × Term) : ddOf75 (reg 1) ac = mulL (eOf110 ac) ac.2 := rfl

theorem powOf_eq_omegaNF_eOf110 (ac : Term × Term) :
    powOf80 (reg 1) ac = omegaNF (eOf110 ac) := rfl

/-- **§110 の主定理 — 係数の比較。**  逃げる元が `ω^E·c` を超えず、その係数 `c` が
    歩の係数 `cV` より真に下なら、この歩は只である。`y` の出どころは訊かない。
    §105 の `lt_idxOf_of_powFree105` は `c = 1` の場合そのものだから、これはその一般化である。 -/
theorem lt_idxOf_of_coef110 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hl3 : lt ac.2 M = true)
    (hz : ac.2 ≠ zero) (hsub : subAP (reg 1) ac.1 ≠ zero)
    {y c : Term} (hyi : inT y = true) (hci : inT c = true) (hcM : lt c M = true)
    (hle : le y (mulL (eOf110 ac) c) = true) (hlt : lt c ac.2 = true)
    (hidxT : inT (idxOf (reg 1) s ac) = true) :
    lt y (idxOf (reg 1) s ac) = true := by
  have hE : inT (eOf110 ac) = true := inT_mulL mulDescInT (inT_reg 1) (inT_subAP h1)
  have hmc : inT (mulL (eOf110 ac) c) = true := inT_mulL mulDescInT hE hci
  have hdT : inT (ddOf75 (reg 1) ac) = true := inT_ddOf75 (inT_reg 1) h1 h3
  have hstep : lt (mulL (eOf110 ac) c) (ddOf75 (reg 1) ac) = true :=
    mulL_smono_right110 hE hci h3 hcM hl3 hlt
  have hyd : lt y (ddOf75 (reg 1) ac) = true :=
    lt_of_le_of_lt3 (inT_le_fragR _ hyi) (inT_le_fragR _ hmc) (inT_le_fragR _ hdT) hle hstep
  have hsub1 : sub1 (ddOf75 (reg 1) ac) = ddOf75 (reg 1) ac :=
    sub1_ddOf86 (u := 0) omegaNF_reg1_80 h1 h3 hz hsub
  have hled : le (ddOf75 (reg 1) ac) (idxOf (reg 1) s ac) = true := by
    have hq := le_sub1dd_idxOf75 (inT_reg 1) hst h1 h3
    rwa [hsub1] at hq
  exact lt_of_lt_of_le3 (inT_le_fragR _ hyi) (inT_le_fragR _ hdT) (inT_le_fragR _ hidxT)
    hyd hled


/-- `c = 1` のとき `ω^E·c` はちょうど `Ω₁^(aV ⊖ Ω₁)`。 -/
theorem mulL_one_eq_powOf110 (ac : Term × Term) :
    mulL (eOf110 ac) TM.Term.one = powOf80 (reg 1) ac := mulL_one105 _

/-- `𝔗(M)` には `0` と `1` のあいだに何もない。 -/
theorem lt_one_of_ne110 {z : Term} (hz : inT z = true) (h0 : z ≠ zero)
    (h1 : z ≠ TM.Term.one) : lt TM.Term.one z = true := by
  rcases lt_trichotomy_inT hz inT_one with hq | hq | hq
  · exact absurd (below_one z hz (fuelOf z TM.Term.one) hq.1) h0
  · exact absurd hq.2.1 h1
  · exact hq.2.2

/-- **§105 の第二の免除の `cV ≠ 1` の側は、係数 `c = 1` の場合そのものである。**
    `y ≤ Ω₁^(aV ⊖ Ω₁) = ω^E·1` で `1 < cV`。`powFree105` の残り半分 (`cV = 1` で
    `y < Ω₁^(aV ⊖ Ω₁)`) はここには入らない — そこは §105 のままである。 -/
theorem lt_idxOf_of_le_powOf110 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hl3 : lt ac.2 M = true)
    (hz : ac.2 ≠ zero) (hz1 : ac.2 ≠ TM.Term.one) (hsub : subAP (reg 1) ac.1 ≠ zero)
    {y : Term} (hyi : inT y = true) (hle : le y (powOf80 (reg 1) ac) = true)
    (hidxT : inT (idxOf (reg 1) s ac) = true) :
    lt y (idxOf (reg 1) s ac) = true :=
  lt_idxOf_of_coef110 hst h1 h3 hl3 hz hsub hyi inT_one lt_one_M
    (by rw [mulL_one_eq_powOf110]; exact hle) (lt_one_of_ne110 h3 hz hz1) hidxT

/-- **判定器。**  係数を `coefOf110` で名指しし、その一本を確かめる。
    `inT` と `lt · M` を条件に入れてあるので、復元が 𝔗(M) の項でない歩では黙って偽になる
    — 定理の側で仮定を借りない。 -/
def coefFree110 (p : (Option Term × Option Term) × (Term × Term)) (y : Term) : Bool :=
  !(subAP (reg 1) p.2.1 == zero)
    && inT (coefOf110 (eOf110 p.2) y) && lt (coefOf110 (eOf110 p.2) y) M
    && le y (mulL (eOf110 p.2) (coefOf110 (eOf110 p.2) y))
    && lt (coefOf110 (eOf110 p.2) y) p.2.2

/-- **判定器を通す形。** -/
theorem lt_idxOf_of_coefFree110 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (h1 : inT ac.1 = true) (h3 : inT ac.2 = true) (hl3 : lt ac.2 M = true)
    (hz : ac.2 ≠ zero) {y : Term} (hyi : inT y = true)
    (hcf : coefFree110 (s, ac) y = true) (hidxT : inT (idxOf (reg 1) s ac) = true) :
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

/-! ### §110.3 条項 — 残るのは係数の比較ひとつ -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§110 の条項。** §105 の `IdxK105` から、§110.2 が片づける歩 — 係数が `cV` より
    真に下になる歩 — を義務から外した形。外したものは定理だから、門との同値は保たれる
    (`idxStd110_of_step073` が逆向き)。仮説がひとつ増えただけなので、条項は §105 の
    条項の部分集合である (`idxK110_of_idxK105`)。 -/
def IdxK110 (a : BT) : Prop :=
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
        powFree105 p y = false → coefFree110 p y = false →
        (∀ i0, p.1.1 = some i0 → lt i0 y = true) →
        monoClosed95 a p e = false → freeSelf95 p e = false →
        (y ∈ Kset (reg 1) p.2.1 ∨ y ∈ Kset (reg 1) p.2.2) →
        lt y (idxOf (reg 1) p.1 p.2) = true

/-- §105 の条項は §110 の条項を出す — 仮説がひとつ増えただけだから。 -/
theorem idxK110_of_idxK105 {a : BT} (H : IdxK105 a) : IdxK110 a := by
  intro p hp hle hidxT y c e j hc hstd hltc he hse hbe hlte hsz hj hjT hpsiT hlej hyT hyk
    hlty hor hpw _ hgt hmono hsf hy
  exact H p hp hle hidxT y c e j hc hstd hltc he hse hbe hlte hsz hj hjT hpsiT hlej hyT hyk
    hlty hor hpw hgt hmono hsf hy

/-- **§110 の残る仮説。** 部分領域の項について §110 の条項。**証明しない。** -/
def IdxStd110 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → IdxK110 a

/-- **§110.3 の主定理。** 一項ぶんの門は §110 の条項と、326 行目が既に抱えている
    二つの条項と、§95 が名指しした算術ひとつから出る。 -/
theorem gateStd87_of_idxK110 (HD : DictLtStd92) (HM : HiMono89) (HL : LeIdxSelf95) (a : BT)
    (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b)
    (H : btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → IdxK110 a) : GateStd87 a := by
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
      by_cases hsub : subAP (reg 1) q.2.1 = zero
      · exact H hb hs q hq hle2 hidxT y c e j hc hstd hltc he hse hbe hlte hsze
          hj hjT hpsiT hlej hyT hyk hlty (Or.inr hsub) hpw hcf hgt hmono hsf hy
      · cases hley : le y (reg 1) with
        | true =>
          exact lt_idxOf_of_le_reg105 hst hi1 hi2 hl2 hnz2 hsub hy hyT hley hidxT
        | false =>
          exact H hb hs q hq hle2 hidxT y c e j hc hstd hltc he hse hbe hlte hsze
            hj hjT hpsiT hlej hyT hyk hlty (Or.inl hley) hpw hcf hgt hmono hsf hy
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


/-- **§110 の残余を、係数だけで書いた形。**  仮説は `IdxK110` とまったく同じで、
    結論だけが違う — `aV ⊖ Ω₁ ≠ 0` の歩では、指数の比較ではなく
    「`y ≤ ω^E·z` になる係数 `z < cV` が在る」になっている。§105 が名指しした残余そのもの。
    **測定はこの形が 599 項の 153 の義務すべてで成り立つと言う** (`shape110`・`coefFree110`)。
    `IdxK110` と違って門と同値であることは示していない — 門より強い可能性がある。
    **証明しない。** -/
def CoefK110 (a : BT) : Prop :=
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
        powFree105 p y = false → coefFree110 p y = false →
        (∀ i0, p.1.1 = some i0 → lt i0 y = true) →
        monoClosed95 a p e = false → freeSelf95 p e = false →
        (y ∈ Kset (reg 1) p.2.1 ∨ y ∈ Kset (reg 1) p.2.2) →
        (subAP (reg 1) p.2.1 = zero → lt y (idxOf (reg 1) p.1 p.2) = true) ∧
        (subAP (reg 1) p.2.1 ≠ zero →
          ∃ z, inT z = true ∧ lt z M = true ∧ le y (mulL (eOf110 p.2) z) = true ∧
            lt z p.2.2 = true)

/-- **係数だけの仮説。証明しない。** -/
def CoefLtStd110 : Prop :=
  ∀ a : BT, btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → CoefK110 a

theorem gateStd87_of_coefK110 (HD : DictLtStd92) (HM : HiMono89) (HL : LeIdxSelf95) (a : BT)
    (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b)
    (H : btLe72 1 a = true → BT.isStd (BT.D 0 a) = true → CoefK110 a) : GateStd87 a := by
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
      by_cases hsub : subAP (reg 1) q.2.1 = zero
      · exact (H hb hs q hq hle2 hidxT y c e j hc hstd hltc he hse hbe hlte hsze
          hj hjT hpsiT hlej hyT hyk hlty (Or.inr hsub) hpw hcf hgt hmono hsf hy).1 hsub
      · cases hley : le y (reg 1) with
        | true =>
          exact lt_idxOf_of_le_reg105 hst hi1 hi2 hl2 hnz2 hsub hy hyT hley hidxT
        | false =>
          obtain ⟨z, hzi, hzM, hzle, hzlt⟩ :=
            (H hb hs q hq hle2 hidxT y c e j hc hstd hltc he hse hbe hlte hsze
              hj hjT hpsiT hlej hyT hyk hlty (Or.inl hley) hpw hcf hgt hmono hsf hy).2 hsub
          exact lt_idxOf_of_coef110 hst hi1 hi2 hl2 hnz2 hsub hyT hzi hzM hzle hzlt hidxT
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

/-- **§110 の第一の結論。** -/
theorem psiIdxStep073_of_idxStd110 (HD : DictLtStd92) (HM : HiMono89) (HL : LeIdxSelf95)
    (H : IdxStd110) : PsiIdxStep073 :=
  step073_of_gate87 (fun a ih => gateStd87_of_idxK110 HD HM HL a ih (fun hb hs => H a hb hs))

/-- **逆向き。** 足した仮説も外した義務もすべて落ちるので、分解は過不足がない。 -/
theorem idxStd110_of_step073 (H : PsiIdxStep073) : IdxStd110 := by
  intro a hb hs p hp hle
  intro _ y _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hy
  exact (H a hb hs p hp hle).2 y hy

/-- **§110 の第二の結論。** 326 行目の証明書が `K` の側で待つのは §110 の条項ひとつと、
    §74/§89 が既に名指ししている二つと、§95 が名指しした算術ひとつである。 -/
theorem certIn_t326_idx110 (HD : DictLtStd92) (HM : HiMono89) (HL : LeIdxSelf95)
    (H : IdxStd110) (HDe : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_step73 (psiIdxStep073_of_idxStd110 HD HM HL H) HDe HI HC hacc

/-- **§110 の第三の結論 — 326 行目は係数の比較ひとつに載る。**
    `CoefLtStd110` は「歩ごとに、逃げる `K` の元は `ω^E` の何倍かで、その倍率が
    歩の係数より真に下」としか言っていない。§105 が名指しした残余そのものである。 -/
theorem psiIdxStep073_of_coefLt110 (HD : DictLtStd92) (HM : HiMono89) (HL : LeIdxSelf95)
    (H : CoefLtStd110) : PsiIdxStep073 :=
  step073_of_gate87 (fun a ih => gateStd87_of_coefK110 HD HM HL a ih (fun hb hs => H a hb hs))

theorem certIn_t326_coef110 (HD : DictLtStd92) (HM : HiMono89) (HL : LeIdxSelf95)
    (H : CoefLtStd110) (HDe : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_step73 (psiIdxStep073_of_coefLt110 HD HM HL H) HDe HI HC hacc

end

/-! ### §110.4 測定 (凍結) -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- §110 の条項が訊く組 — §105 の残余から係数の比較で片づくぶんを引いたもの。 -/
def oblPost110 (a : BT) :
    List (((Option Term × Option Term) × (Term × Term)) × Term × BT × Term) :=
  (oblPost105 a).filter fun w => !(coefFree110 w.1 w.2.1)

/-- 義務そのものの真偽 — 門が実際にそこで通っているか。 -/
def gOK110 (w : ((Option Term × Option Term) × (Term × Term)) × Term × BT × Term) : Bool :=
  lt w.2.1 (idxOf (reg 1) w.1.1 w.1.2)

/-- 枠をどこまでも入れ子にする — 係数を大きくしようとする方向。 -/
def deep110 : Nat → BT
  | 0 => BT.zero
  | n+1 => eNest105 (deep110 n)

/-- `ψ₀` の引数の側で発火が二度起きる形 — 指数 `j` が和になる。 -/
def multi110 (k : Nat) : BT :=
  BT.D 1 (BT.sum (BT.D 1 (BT.D 1 BT.zero))
    (BT.sum (BT.D 0 (deep110 k)) (BT.sum (BT.D 1 (BT.D 1 BT.zero)) (BT.D 0 BT.zero))))

def argsX110 : List BT :=
  ((List.range 4).map deep110) ++ [eHi2_105, eHi3_105, ehi100 0, ehi100 1,
    multi110 0, multi110 1, eNest105 (twr86 1), eNest105 (twr86 2), slot105 2 BT.zero]

def tails110 : List (BT → BT) :=
  [ fun b => b, fun b => BT.sum b vebTail95,
    fun b => BT.sum b (BT.sum (twr86 3) vebTail95),
    fun b => BT.sum (twr86 5) (BT.sum b vebTail95),
    fun b => BT.sum (twr86 5) (BT.sum b (BT.sum (twr86 3) vebTail95)),
    fun b => BT.sum b (BT.sum b vebTail95) ]

def wideAdv110 : List BT :=
  ((List.range 3).flatMap fun n => argsX110.flatMap fun E =>
     tails110.map fun f => f (slot105 n E)).eraseDups
def wideAdvQ110 : List BT := wideAdv110.filter okHyp84

/-- 枠を二つ並べる — 二段目の歩には直前の指数がある。 -/
def two110 (n m : Nat) (E F : BT) : BT :=
  BT.sum (slot105 n E) (BT.sum (slot105 m F) vebTail95)
def pairPop110 : List BT :=
  ((List.range 3).flatMap fun n => (List.range 3).flatMap fun m =>
     argsX110.flatMap fun E => [two110 n m E BT.zero, two110 n m E (deep110 1),
       two110 n m BT.zero E, BT.sum (twr86 5) (two110 n m E BT.zero)]).eraseDups
def pairQ110 : List BT := pairPop110.filter okHyp84

/-- 標準でないが `dict` の像は 𝔗(M) にいる項 — §105 が 213 個数えた側。 -/
def junk110 : List BT :=
  ((wideAdv110 ++ pop105).filter fun a => !(okHyp84 a) && inT (dict a)).eraseDups

/-- **組み立てた敵 — `survC105` の枠を一段だけ下げたもの (21 記号)。**
    `slot105 1` を `slot105 0` にする、それだけである。 -/
def advC110 : BT := BT.sum (slot105 0 (eNest105 BT.zero)) vebTail95

/-- **同じことを §105 の第一の証人でやったもの (17 記号)。** -/
def advA110 : BT := BT.sum (slot105 0 (ehi100 0)) vebTail95

/-- **否定 — 係数の比較は `BT.isStd` なしでは偽。**  `advC110` は `survC105` の枠を
    一段下げただけで、段は 1 以下、`dict` の像は 𝔗(M) にいる。それでも
    `BT.isStd (ψ₀ ·)` は偽、門はそこで落ち、§105 を生き延びる義務の係数は `cV` より
    下でない — そして義務そのものも偽である。**係数の比較が買っているのは標準性であり、
    標準性を見ない条項では閉じない。** -/
theorem advC110_not_std :
    btLe72 1 advC110 = true ∧ inT (dict advC110) = true ∧
    BT.isStd (BT.D 0 advC110) = false ∧ stepOKb 0 (dict advC110) = false ∧
    (oblPost105 advC110).length = 1 ∧ (oblPost110 advC110).length = 1 ∧
    ((oblPost105 advC110).all fun w => !(coefFree110 w.1 w.2.1) && !(gOK110 w)) = true :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- 同じことが §105 の第一の証人の側でも起きる。 -/
theorem advA110_not_std :
    btLe72 1 advA110 = true ∧ inT (dict advA110) = true ∧
    BT.isStd (BT.D 0 advA110) = false ∧ stepOKb 0 (dict advA110) = false ∧
    (oblPost110 advA110).length = 1 ∧
    ((oblPost105 advA110).all fun w => !(coefFree110 w.1 w.2.1) && !(gOK110 w)) = true :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **§105 が残した残余は係数の比較で消える。**  `survC105` の一本の義務は
    `coefFree110` が真であり、義務そのものも真である。枠が一段上がっただけで
    `advC110` との差はそこにしかない。 -/
theorem survC110_free :
    (oblPost105 survC105).length = 1 ∧ (oblPost110 survC105).length = 0 ∧
    ((oblPost105 survC105).all fun w => coefFree110 w.1 w.2.1 && gOK110 w) = true :=
  ⟨by decide, by decide, by decide⟩

/-- **§110 は §105.1 の第一の定理を飲み込まない。**  `survA105` の義務 (`y = Ω₁` ちょうど)
    では係数の比較は偽で、それでも義務は真である。二つの免除は別物である。 -/
theorem coef_not_subsume110 :
    ((oblPost100 survA105).all fun w => !(coefFree110 w.1 w.2.1) && gOK110 w) = true := by
  decide

-- 組み立てた母集団の大きさと形。
#guard (wideAdv110.length, wideAdvQ110.length,
        (wideAdv110.map BT.size).foldl min 999, (wideAdv110.map BT.size).foldl max 0)
       == (216, 132, 7, 95)
#guard (pairPop110.length, pairQ110.length) == (414, 157)
#guard (BT.size advC110, BT.size advA110, BT.size survC105) == (21, 17, 25)

/-! **門は組み立てた母集団のどこでも落ちない。** -/

#guard ((wideAdvQ110.filter fun a => !(stepOKb 0 (dict a))).length,
        (wideAdvQ110.filter fun a => !(idxb84 0 (dict a))).length,
        (wideAdvQ110.filter fun a => !(splitb86 0 (dict a))).length,
        (wideAdvQ110.filter fun a => !(idxLt90b a)).length,
        (wideAdvQ110.filter fun a => !(ltArg90b a)).length) == (0, 0, 0, 0, 0)
#guard (pairQ110.filter fun a => !(stepOKb 0 (dict a))).length == 0

/-! **義務の数。**  入れ子を深くする 132 項で 299 → 174 (§92) → 90 (§95) → 90 (§100)
→ 78 (§105) → **0 (§110)**。枠を二つ並べる 157 項で 350 → 77 (§95) → 71 (§105) →
**0 (§110)**。§105 の 310 項 (`corpus105`) の残り 4 も 0 になる。 -/

#guard ((wideAdvQ110.flatMap oblPre92).length, (wideAdvQ110.flatMap oblPost92).length,
        (wideAdvQ110.flatMap oblPost95).length, (wideAdvQ110.flatMap oblPost100).length,
        (wideAdvQ110.flatMap oblPost105).length,
        (wideAdvQ110.flatMap oblPost110).length) == (299, 174, 90, 90, 78, 0)
#guard ((pairQ110.flatMap oblPre92).length, (pairQ110.flatMap oblPost95).length,
        (pairQ110.flatMap oblPost105).length, (pairQ110.flatMap oblPost110).length)
       == (350, 77, 71, 0)
#guard ((corpus105.flatMap oblPost105).length, (corpus105.flatMap oblPost110).length)
       == (4, 0)

/-! **直前の指数のある歩は §92.1 が全部持っていく。**  枠を二つ並べた 157 項で、
直前の指数のある義務は 170 あるが、§105 を生き延びるものは 0 である。
そして生き残る義務の `y` はどれも `K_{Ω₁}(cV)` の側から来る — `K_{Ω₁}(aV)` からは 0。 -/

#guard ((pairQ110.flatMap oblPre92).countP (fun w => !(w.1.1.1 == none)),
        (pairQ110.flatMap oblPost105).countP (fun w => !(w.1.1.1 == none)),
        ((corpus105 ++ wideAdvQ110 ++ pairQ110).flatMap oblPost105).countP
          (fun w => (Kset (reg 1) w.1.2.1).contains w.2.1)) == (170, 0, 0)


/-- 残る義務の形を一本で読む述語 — 最初の発火歩・`aV ⊖ Ω₁ ≠ 0`・`Ω₁^(aV ⊖ Ω₁) < y`・
    `y = ω^E·c` ちょうど・`c` も `cV` も `Ω₁` より下・`c ≤ j`。 -/
def shape110 (w : ((Option Term × Option Term) × (Term × Term)) × Term × BT × Term) : Bool :=
  (w.1.1.1 == none) && !(subAP (reg 1) w.1.2.1 == zero)
    && lt (powOf80 (reg 1) w.1.2) w.2.1
    && (mulL (eOf110 w.1.2) (coefOf110 (eOf110 w.1.2) w.2.1) == w.2.1)
    && lt (coefOf110 (eOf110 w.1.2) w.2.1) (reg 1) && lt w.1.2.2 (reg 1)
    && le (coefOf110 (eOf110 w.1.2) w.2.1) w.2.2.2

/-- **§105 の残余の形は一つ、そして係数はどれも `Ω₁` より下。**
    `survC105` の義務がその形をしている。 -/
theorem survC110_shape : ((oblPost105 survC105).all shape110) = true := by decide

/-! **形は 153 の義務すべてで同じ。**  599 項で §105 を生き延びる義務は 153 あり、
そのどれもが最初の発火歩で、`Ω₁^(aV ⊖ Ω₁) < y`、`y = ω^E·c` ちょうど、そして
`c < Ω₁` かつ `cV < Ω₁`。**残余は `Ω₁` より下の順序数二つの比較ひとつに揃っている。**
§105 は自分の 10 個について `cV = ψ_{Ω₁}(j)`・`y = j` と書いたが、母集団を広げると
それは一般ではない — `y = j` は 110/153、`cV = ψ_{Ω₁}(j)` は 43/153 である。
一般に成り立つのは上の形のほうである。 -/

#guard (let P := corpus105 ++ wideAdvQ110 ++ pairQ110
        let o := P.flatMap oblPost105
        (o.length, o.countP shape110,
         o.countP (fun w => w.2.1 == w.2.2.2),
         o.countP (fun w => w.1.2.2 == psi (reg 1) w.2.2.2),
         o.countP (fun w => le w.2.1 (reg 1)))) == (153, 153, 110, 43, 0)

/-! **判定器は恒真ではない。**  `corpus105` と `wideAdvQ110` の生の義務 570 のうち、
係数の比較が通るのは 267 だけである。残る 303 は §92・§95・§100・§105 が持っていく。 -/

#guard (let o := (corpus105 ++ wideAdvQ110).flatMap oblPre92
        (o.length, o.countP (fun w => coefFree110 w.1 w.2.1))) == (570, 267)

/-! **標準でない側では、係数の比較は義務そのものと一致する。**  `dict` の像は 𝔗(M) に
いるが標準でない 84 項で、§105 を生き延びる義務は 150。そのうち係数の比較が真なのは 18、
偽なのは 132 — そして **(真, 義務が偽) も (偽, 義務が真) も 0 である。**
係数の比較は、そこでは十分条件ではなく門そのものである。 -/

#guard (let o := junk110.flatMap oblPost105
        (junk110.length, o.length,
         o.countP (fun w => coefFree110 w.1 w.2.1 && gOK110 w),
         o.countP (fun w => coefFree110 w.1 w.2.1 && !(gOK110 w)),
         o.countP (fun w => !(coefFree110 w.1 w.2.1) && gOK110 w),
         o.countP (fun w => !(coefFree110 w.1 w.2.1) && !(gOK110 w))))
       == (84, 150, 18, 0, 0, 132)

/-! **標準な項の上では §110 の条項は空虚である — 組み立てた 599 項の範囲で。**
`corpus105` (310) ・`wideAdvQ110` (132)・`pairQ110` (157) を合わせて、§105 の残余は
153 あり、§110 はその 153 をすべて持っていく。**§110 は生き残る義務を一つも出せていない。**
これは §100 が置かれていたのと同じ位置であり、§105 がそれを破ったのと同じことを
次の節がしなければならない。上の `advC110` が、その形を名指ししている — 標準性を
一段だけ落とすと、係数の比較は破れ、義務も偽になる。 -/

#guard (let P := corpus105 ++ wideAdvQ110 ++ pairQ110
        (P.length, (P.flatMap oblPost105).length, (P.flatMap oblPost110).length))
       == (599, 153, 0)

end

/-! ## §109 THE FOLD'S FIRING PAIRS ARE A PREFIX — AND THE `a`-FIRES HALF NEEDS ONLY `≤`

§104 named the coefficient's `z` and then stopped at the sentence this section starts from:

> Naming the coefficient is not yet COMPARING TWO FOLDS. … `lastFire92` forces ALL pairs to
> fire (exponents descend), so that branch is the "divide by `Ω₁^Ω₁`" map and is disjoint from
> the Veblen residue; **the repository has no descending-exponent lemma for `wcnf` yet, which
> is what such a proof would need first.**

**§109 proves that lemma, and then uses it to close the `a`-fires half of `HiMono89` down to
one comparison of collapse INDICES — with no Veblen arithmetic left in it at all.**  What the
closing costs is one clause, and the clause is **non-strict**: the strict form is refuted here
by a 11-symbol witness that the section's own population hands over.

WHAT IS PROVED.

  §109.1  **FIRING IS A PREFIX PROPERTY** (`fireSplit109`).  The pairs of `wcnf w L` split as
          "all firing" then "none firing": every pair in `dropWhile (fires)` fails to fire.
          The content is `fireMono109` — `q ≤ p ⟹ (q's pair fires ⟹ p's pair fires)` — which
          needs only the HEAD of `logOm`, so §65.5's `divDescSC` (`logOm` mono → `subAP` mono →
          `ω^·` mono) does the work and the full lexicographic monotonicity of `wA` is never
          needed.  `inT_wA109` re-derives `inT (wA w p)` from `divDescSC`, since §64.4's
          `inT_wA` assumed the FALSE `DivDescInT`.  Corollary
          `allFire_of_lastFire109` : `lastFire92 x ⟹ allFire101 x` — §104's missing lemma —
          and its converse `lastFire_of_allFire109`.

  §109.2  **FIRING TRAVELS RIGHT** (`fireHead109`, `idxF_some109`).  If `X`'s fold fires at its
          last pair and `X < Y`, then `Y`'s fold fires at its FIRST pair, hence `Y` HAS a
          collapse index.  Proof: §109.1 makes `X`'s head pair fire, §65.1's `hd_mono_inT`
          carries `X`'s head component below `Y`'s, and `fireMono109` carries the firing across.
          **No gate, no bridge.**

  §109.3  **THE VEBLEN TAIL IS STRICTLY ABOVE THE PREFIX'S `ψ_{Ω₁}`** (`accGt109`).  §95.1's
          `accGeb95` proves `ψ_{Ω₁}(j) ≤ acc`; §109.3 proves `<` whenever the last pair does
          not fire.  Two ingredients, both new: `lt_psi_phiNF109` (the strict form of §95.1's
          `le_psi_phiNF95` — `phiNF` returns either its own argument or a `φ̄`-term, and
          `lt_psi_phi_of_le` is already strict) and `wcnf_cnz109` (**the base-`w`
          COEFFICIENTS are never `0`**), which is what makes `acc ⊕ c` overtake `acc` at the
          first Veblen step.

  §109.4  **THE PAYOFF** (`hiMono_fireA109`).  When `a`'s fold fires at its last pair,
          `HiMono89`'s conclusion follows from the index comparison alone: `b` also has an
          index (§109.2), `ψ₀(hi (dict a)) = ψ_{Ω₁}(ja)` (§92.2), and either `b` fires too —
          §101.5's `IdxMono101`, verbatim — or `b` has a Veblen tail and §109.3 supplies the
          strictness, so the clause only has to say `ja ≤ jb`.  `IdxLeMix109` is that clause;
          `hiMono_of_three109` puts `HiMono89` on `IdxMono101 ∧ IdxLeMix109 ∧ HiMonoVebA109`
          and `certIn_t326_109` re-hangs row 326 on them.
          **And the strict clause is FALSE** (`not_idxLtMix109`): `mixA109 = ψ₁ψ₁ψ₁0`,
          `mixB109 = ψ₁ψ₁ψ₁0 ⊕ Ω₁` are both `K`-standard, `hi (dict a) < hi (dict b)`, and
          **their indices are EQUAL** — the conclusion still holds, and it holds because of
          the Veblen tail, not because of the index.  The non-strictness of `IdxLeMix109` is
          therefore not a weakening but the truth.

WHAT IS **NOT** CLAIMED.  `HiMono89` is NOT proved and NOT refuted.  **§109 MOVES the residue
and it moves the SMALLER half of it.**  `IdxMono101` is §101's clause untouched and unproved;
`IdxLeMix109` is new and unproved; `HiMonoVebA109` — the case where `a`'s fold does NOT fire —
is the whole remaining difficulty, and `knownAreVeb109` says plainly where the known
counterexamples live: `bothBadA101` (§101.4), `scBadA101` (§101.2) and `cexA89` (§81) ALL have
`lastFire92 (dict ·) = false`, so **every witness that has ever been built against this clause
sits in the half §109 did not close.**  On §109.5's own population the `a`-fires half carries
636 of 7140 residual pairs and **0 of the 388 breaks.**  Row 326 rests on `PsiIdxOKStd172`,
`IdxMono101`, `IdxLeMix109`, `HiMonoVebA109`, `DictOntoMidOpen103`, `DictDenseMid107`,
`DictDenseAbove107`.

**WHERE §109 STOPPED, PRECISELY.**  The `a`-fires half is now pure index arithmetic: the map
`(A, c) ↦ Ω₁^(A ⊖ Ω₁)·c` summed along the fold, compared against the same map on a longer or
taller list.  That is §92's `IdxMono101` and §109 does not run it — it is the "divide by
`Ω₁^Ω₁`" map §104 named, and the repository still has no lemma that it preserves the order of
`hi`.  The other half is untouched: when `a`'s fold has a Veblen tail its value is a `φ̄`-term
and comparing two `φ̄`-terms is §104's stopping point word for word, `φ̄(α,γ) < φ̄(β,δ)` at
`α < β` iff `γ < φ̄(β,δ)`.

WHAT THE MEASUREMENT SAYS (§109.5 gives the construction).  One population, BUILT from a
firing line and a non-firing line so that all four combinations occur, and nothing filtered.

  * **The population is not blind to any of the three theorems.**  48 of its 120 terms have no
    collapse index at all, 48 have one without firing at the last pair, 24 fire everywhere;
    12 of those 24 have two or more pairs, so §109.1 is not a statement about singletons.
  * **§109.2's hypothesis does all the work.**  1128 residual pairs have a `b` with NO index —
    and in every one of them `a` fails to fire.  Drop the hypothesis and the conclusion breaks
    1128 times.
  * **§109.3's hypothesis does all the work.**  On the 48 terms with an index and a Veblen tail
    the strict inequality holds 48 times out of 48; on the 24 that fire everywhere it holds
    0 times out of 24, because there the value IS `ψ_{Ω₁}(j)`.
  * **The four cases, and where the breaks are.**  (fire, fire) 276 pairs / 0 breaks,
    (fire, Veblen) 360 / 0, (Veblen, fire) 1944 / 13, (Veblen, Veblen) 4560 / 375.  Every
    break is on the side §109 did not close.
  * **The non-strict clause is exactly right.**  Over the 636 residual pairs with `a` firing,
    `ja ≤ jb` never fails and `ja < jb` fails 48 times (46 of them `K`-standard);
    **all 48 failures are `ja = jb`** and none reverses the order.
  * **The witness is the smallest one the population contains** — 11 symbols, and every
    `K`-standard failure has at least that many. -/

/-! ### §109.1 発火は前置き — 対の指数は降る -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- `w` が加法主要なら `w ≤ ·` は頭部だけを見る (⇒)。 -/
theorem le_hd_of_le109 {w Y b : Term} {s : List Term} (hw : inT w = true)
    (hwap : w.isAP = true) (hY : inT Y = true) (hl : toList Y = b :: s)
    (h : le w Y = true) : le w b = true := by
  have hib : inT b = true := inTL_inT hY b (by rw [hl]; exact List.Mem.head _)
  cases hc : le w b with
  | true => rfl
  | false =>
      exfalso
      have hbw : lt b w = true := lt_of_not_le_inT hw hib hc
      have hYw : lt Y w = true := by
        rw [← inT_ofList_toList Y hY, hl, lt_ofList_nsum hwap]; exact hbw
      rcases (Bool.or_eq_true _ _).mp h with he | hlt
      · rw [eq_of_beq he, lt_irrefl] at hYw; exact Bool.noConfusion hYw
      · rw [lt_asymm_inT hw hY hlt] at hYw; exact Bool.noConfusion hYw

/-- 逆向き (⇐)。 -/
theorem le_of_le_hd109 {w Y b : Term} {s : List Term} (hw : inT w = true)
    (hY : inT Y = true) (hl : toList Y = b :: s) (h : le w b = true) : le w Y = true :=
  le_trans_inT hw (inTL_inT hY b (by rw [hl]; exact List.Mem.head _)) hY h
    (le_hd_self_inT hY hl)

/-- `wA` は `𝔗(M)` の項 — §64.4 の `inT_wA` は偽の (G1) を仮定していたので引き直す。 -/
theorem inT_wA109 {w p : Term} (hw : inT w = true) (hsc : w.isSC = true)
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
    have h2 := (List.mem_filter.mp hq).2
    cases hlq : lt q w with
    | false => rfl
    | true => rw [hlq] at h2; exact Bool.noConfusion h2

/-- `wA` の成分列の頭は、`logOm` の成分列の頭の `divAP`。 -/
theorem toList_wA109 {w p b : Term} {s : List Term}
    (hl : toList (logOm p) = b :: s) (hbw : lt b w = false) :
    toList (wA w p) = divAP w b :: ((s.filter (fun q => !lt q w)).map (divAP w)) := by
  show toList (ofList (((toList (logOm p)).filter (fun q => !lt q w)).map (divAP w))) = _
  rw [hl, List.filter_cons_of_pos (by rw [hbw]; rfl), List.map_cons]
  refine toList_ofList _ ?_
  intro x hx
  rcases List.mem_cons.mp hx with h1 | h1
  · rw [h1]; exact isAP_divAP _ _
  · obtain ⟨q, _, hxe⟩ := List.mem_map.mp h1
    rw [← hxe]; exact isAP_divAP _ _

/-- `w` 以上の加法主要項の `logOm` の成分列は空でなく、その頭も `w` 以上。 -/
theorem hd_logOm109 {w p : Term} (hsc : w.isSC = true) (hw : inT w = true)
    (hwap : w.isAP = true) (hap : p.isAP = true) (hp : inT p = true)
    (hpw : lt p w = false) : ∃ b s, toList (logOm p) = b :: s ∧ lt b w = false := by
  have hgw : lt (logOm p) w = false := lt_logOm_of_sc hsc hw hap hp hpw
  cases hl : toList (logOm p) with
  | nil =>
      exfalso
      have hz : logOm p = zero := toList_eq_nil _ hl
      have hwz : w ≠ zero := by
        intro hc; rw [hc] at hsc; exact Bool.noConfusion hsc
      rw [hz, lt_zero_left hwz] at hgw
      exact Bool.noConfusion hgw
  | cons b s =>
      refine ⟨b, s, rfl, ?_⟩
      rw [← lt_ofList_nsum hwap b s, ← hl, inT_ofList_toList _ (inT_logOm hp)]
      exact hgw

/-- `divAP w` は `{x : w ≤ x}` の上で単調 — §65.5 の `divDescSC` の中身そのもの。 -/
theorem divAP_mono109 {w x y : Term} (hsc : w.isSC = true) (hw : inT w = true)
    (hax : x.isAP = true) (hix : inT x = true) (hxw : lt x w = false)
    (hay : y.isAP = true) (hiy : inT y = true) (h : le x y = true) :
    le (divAP w x) (divAP w y) = true := by
  refine omegaNF_mono_inT (inT_subAP (inT_logOm hix)) (inT_subAP (inT_logOm hiy)) ?_
  refine subAP_mono_inT (inT_logOm hix) (inT_logOm hiy) (lt_logOm_of_sc hsc hw hax hix hxw) ?_
  exact logOm_mono_inT hax hay hix hiy h

/-- **§109.1 の第一の定理 — 「発火する」は上向きに閉じている。**
    `q ≤ p` で `q` の対が発火するなら `p` の対も発火する。 -/
theorem fireMono109 {w p q : Term} (hsc : w.isSC = true) (hw : inT w = true)
    (hwap : w.isAP = true)
    (hap : p.isAP = true) (hip : inT p = true) (hpw : lt p w = false)
    (haq : q.isAP = true) (hiq : inT q = true) (hqw : lt q w = false)
    (hqp : le q p = true) (h : le w (wA w q) = true) : le w (wA w p) = true := by
  obtain ⟨bq, sq, hlq, hbqw⟩ := hd_logOm109 hsc hw hwap haq hiq hqw
  obtain ⟨bp, sp, hlp, hbpw⟩ := hd_logOm109 hsc hw hwap hap hip hpw
  have hgq : inT (logOm q) = true := inT_logOm hiq
  have hgp : inT (logOm p) = true := inT_logOm hip
  have hibq : inT bq = true := inTL_inT hgq bq (by rw [hlq]; exact List.Mem.head _)
  have hibp : inT bp = true := inTL_inT hgp bp (by rw [hlp]; exact List.Mem.head _)
  have habq : bq.isAP = true := inTL_isAP hgq bq (by rw [hlq]; exact List.Mem.head _)
  have habp : bp.isAP = true := inTL_isAP hgp bp (by rw [hlp]; exact List.Mem.head _)
  have hbb : le bq bp = true :=
    hd_mono_inT hgq hgp hlq hlp (logOm_mono_inT haq hap hiq hip hqp)
  have hdd : le (divAP w bq) (divAP w bp) = true :=
    divAP_mono109 hsc hw habq hibq hbqw habp hibp hbb
  have h1 : le w (divAP w bq) = true :=
    le_hd_of_le109 hw hwap (inT_wA109 hw hsc hiq) (toList_wA109 hlq hbqw) h
  exact le_of_le_hd109 hw (inT_wA109 hw hsc hip) (toList_wA109 hlp hbpw)
    (le_trans_inT hw (inT_divAP hibq) (inT_divAP hibp) h1 hdd)

/-- `wcnf` の対の列の頭の指数は、成分列の頭の `wA`。 -/
theorem wcnfFstHd109 {w q : Term} (rest : List Term) (hq : lt q w = false) :
    ∃ c ps, (wcnf w (q :: rest)).1 = (wA w q, c) :: ps := by
  rw [wcnf_cons_ge hq]
  cases hr : wcnf w rest with
  | mk fst snd =>
    cases fst with
    | nil => exact ⟨wC w q, [], rfl⟩
    | cons ac0 ps =>
      cases ac0 with
      | mk a' c' =>
        by_cases heq : (wA w q == a') = true
        · refine ⟨plus (wC w q) c', ps, ?_⟩
          show ((if (wA w q == a') = true
                 then ((wA w q, plus (wC w q) c') :: ps, snd)
                 else ((wA w q, wC w q) :: (a', c') :: ps, snd))
                : List (Term × Term) × Term).1 = _
          rw [if_pos heq]
        · refine ⟨wC w q, (a', c') :: ps, ?_⟩
          show ((if (wA w q == a') = true
                 then ((wA w q, plus (wC w q) c') :: ps, snd)
                 else ((wA w q, wC w q) :: (a', c') :: ps, snd))
                : List (Term × Term) × Term).1 = _
          rw [if_neg heq]

/-- 対の列が空でないなら、成分列の頭は `w` 以上でその `wA` が頭の指数。 -/
theorem wcnf_fst_cons109 {w : Term} : ∀ (L : List Term) (ac0 : Term × Term)
    (ps : List (Term × Term)), (wcnf w L).1 = ac0 :: ps →
    ∃ q rest, L = q :: rest ∧ lt q w = false ∧ ac0.1 = wA w q := by
  intro L
  cases L with
  | nil => intro ac0 ps h; exact absurd h (by intro hc; cases hc)
  | cons q rest =>
      intro ac0 ps h
      by_cases hlq : lt q w = true
      · rw [wcnf_cons_lt hlq] at h; exact absurd h (by intro hc; cases hc)
      · have hq := bool_false hlq
        obtain ⟨c, ps', he⟩ := wcnfFstHd109 rest hq
        rw [he] at h
        injection h with h1 _
        exact ⟨q, rest, rfl, hq, by rw [← h1]⟩

theorem mem_takeWhile109 {α : Type} (p : α → Bool) : ∀ (l : List α) (a : α),
    a ∈ l.takeWhile p → p a = true
  | [], a, h => by cases h
  | b :: t, a, h => by
      by_cases hb : p b = true
      · rw [List.takeWhile_cons_of_pos hb] at h
        rcases List.mem_cons.mp h with h1 | h1
        · rw [h1]; exact hb
        · exact mem_takeWhile109 p t a h1
      · rw [List.takeWhile_cons_of_neg (by simpa using hb)] at h; cases h

/-- **§109.1 の主定理 — 発火する対は前置きをなす。**  `dropWhile` の側には
    発火する対は一つもない。§104 が「この repo に無い」と名指しした補題である。 -/
theorem fireSplit109 {w : Term} (hsc : w.isSC = true) (hw : inT w = true)
    (hwap : w.isAP = true) : ∀ (L : List Term), inTL L = true → descL L = true →
      ∀ ac ∈ (wcnf w L).1.dropWhile (fun z => le w z.1), le w ac.1 = false := by
  intro L
  induction L with
  | nil => intro _ _ ac hac; exact absurd hac (by intro hc; cases hc)
  | cons p rest ih =>
    intro hc hd ac hac
    obtain ⟨⟨hap, hip⟩, hcr⟩ := inTL_cons.mp hc
    have hdr := descL_tail hd
    have hR := ih hcr hdr
    by_cases hlp : lt p w = true
    · rw [wcnf_cons_lt hlp] at hac; exact absurd hac (by intro hcc; cases hcc)
    · have hlp' : lt p w = false := bool_false hlp
      cases hr : wcnf w rest with
      | mk fst snd =>
        have hRl : (wcnf w rest).1 = fst := by rw [hr]
        cases fst with
        | nil =>
            have hW : (wcnf w (p :: rest)).1 = [(wA w p, wC w p)] := by
              rw [wcnf_cons_ge hlp', hr]
            rw [hW] at hac
            by_cases hf : le w (wA w p) = true
            · rw [List.dropWhile_cons_of_pos (p := fun z : Term × Term => le w z.1) hf] at hac
              exact absurd hac (by intro hcc; cases hcc)
            · rw [List.dropWhile_cons_of_neg (p := fun z : Term × Term => le w z.1) (by simpa using hf)] at hac
              rw [List.mem_singleton.mp hac]
              exact bool_false hf
        | cons ac0 ps =>
            cases ac0 with
            | mk a' c' =>
              obtain ⟨q, rest', hrest, hqw, ha'⟩ :=
                wcnf_fst_cons109 rest (a', c') ps (by rw [hRl])
              have hcr' : inTL (q :: rest') = true := by rw [← hrest]; exact hcr
              obtain ⟨⟨haq, hiq⟩, _⟩ := inTL_cons.mp hcr'
              have hd' : descL (p :: q :: rest') = true := by rw [← hrest]; exact hd
              have hqp : le q p = true := (descL_cons.mp hd').1
              have hmono : le w a' = true → le w (wA w p) = true := by
                intro hfa
                exact fireMono109 hsc hw hwap hap hip hlp' haq hiq hqw hqp
                  (by rw [← show a' = wA w q from ha']; exact hfa)
              by_cases heq : (wA w p == a') = true
              · have hpa' : a' = wA w p := (eq_of_beq heq).symm
                have hW : (wcnf w (p :: rest)).1 = (wA w p, plus (wC w p) c') :: ps := by
                  rw [wcnf_cons_ge hlp', hr]
                  show ((if (wA w p == a') = true
                         then ((wA w p, plus (wC w p) c') :: ps, snd)
                         else ((wA w p, wC w p) :: (a', c') :: ps, snd))
                        : List (Term × Term) × Term).1 = _
                  rw [if_pos heq]
                rw [hW] at hac
                by_cases hf : le w (wA w p) = true
                · rw [List.dropWhile_cons_of_pos (p := fun z : Term × Term => le w z.1) hf] at hac
                  refine hR ac ?_
                  rw [hRl, List.dropWhile_cons_of_pos (p := fun z : Term × Term => le w z.1)
                    (show le w ((a', c') : Term × Term).1 = true from by rw [hpa']; exact hf)]
                  exact hac
                · rw [List.dropWhile_cons_of_neg (p := fun z : Term × Term => le w z.1) (by simpa using hf)] at hac
                  rcases List.mem_cons.mp hac with h1 | h1
                  · rw [h1]; exact bool_false hf
                  · refine hR ac ?_
                    rw [hRl, List.dropWhile_cons_of_neg (p := fun z : Term × Term => le w z.1)
                      (show ¬ (le w ((a', c') : Term × Term).1 = true) from by
                        rw [hpa']; simpa using hf)]
                    exact List.Mem.tail _ h1
              · have hW : (wcnf w (p :: rest)).1
                    = (wA w p, wC w p) :: (a', c') :: ps := by
                  rw [wcnf_cons_ge hlp', hr]
                  show ((if (wA w p == a') = true
                         then ((wA w p, plus (wC w p) c') :: ps, snd)
                         else ((wA w p, wC w p) :: (a', c') :: ps, snd))
                        : List (Term × Term) × Term).1 = _
                  rw [if_neg heq]
                rw [hW] at hac
                by_cases hf : le w (wA w p) = true
                · rw [List.dropWhile_cons_of_pos (p := fun z : Term × Term => le w z.1) hf] at hac
                  refine hR ac ?_
                  rw [hRl]; exact hac
                · have hfa' : ¬ (le w a' = true) := fun hx => hf (hmono hx)
                  rw [List.dropWhile_cons_of_neg (p := fun z : Term × Term => le w z.1) (by simpa using hf)] at hac
                  rcases List.mem_cons.mp hac with h1 | h1
                  · rw [h1]; exact bool_false hf
                  · refine hR ac ?_
                    rw [hRl, List.dropWhile_cons_of_neg (p := fun z : Term × Term => le w z.1)
                      (show ¬ (le w ((a', c') : Term × Term).1 = true) from hfa')]
                    exact h1

theorem reverse_append_cons109 {α : Type} (A D : List α) {e : α} {es : List α}
    (hD : D.reverse = e :: es) : (A ++ D).reverse = e :: (es ++ A.reverse) := by
  rw [List.reverse_append, hD]; rfl

/-- 列の言葉での「最後が発火するならぜんぶ発火する」。 -/
theorem allFire_of_lastFireL109 {w : Term} (hsc : w.isSC = true) (hw : inT w = true)
    (hwap : w.isAP = true) (L : List Term) (hc : inTL L = true) (hd : descL L = true)
    {ac0 : Term × Term} {t : List (Term × Term)}
    (hrev : (wcnf w L).1.reverse = ac0 :: t) (hfire : le w ac0.1 = true) :
    ∀ ac ∈ (wcnf w L).1, le w ac.1 = true := by
  intro ac hac
  cases hf : le w ac.1 with
  | true => rfl
  | false =>
      exfalso
      have hsp := fireSplit109 hsc hw hwap L hc hd
      have hmemD : ac ∈ (wcnf w L).1.dropWhile (fun z => le w z.1) := by
        have he : ((wcnf w L).1.takeWhile (fun z : Term × Term => le w z.1))
            ++ ((wcnf w L).1.dropWhile (fun z : Term × Term => le w z.1)) = (wcnf w L).1 :=
          List.takeWhile_append_dropWhile
        rcases List.mem_append.mp (show ac ∈ _ ++ _ from by rw [he]; exact hac) with h1 | h1
        · exact absurd (mem_takeWhile109 _ _ _ h1) (by rw [hf]; exact Bool.noConfusion)
        · exact h1
      cases hDr : ((wcnf w L).1.dropWhile (fun z : Term × Term => le w z.1)).reverse with
      | nil =>
          have hDn : (wcnf w L).1.dropWhile (fun z : Term × Term => le w z.1) = [] := by
            rw [← List.reverse_reverse
              ((wcnf w L).1.dropWhile (fun z : Term × Term => le w z.1)), hDr]
            rfl
          rw [hDn] at hmemD; cases hmemD
      | cons e es =>
          have hAD : ((wcnf w L).1.takeWhile (fun z : Term × Term => le w z.1))
              ++ ((wcnf w L).1.dropWhile (fun z : Term × Term => le w z.1)) = (wcnf w L).1 :=
            List.takeWhile_append_dropWhile
          have hrev2 := reverse_append_cons109
            ((wcnf w L).1.takeWhile (fun z : Term × Term => le w z.1))
            ((wcnf w L).1.dropWhile (fun z : Term × Term => le w z.1)) hDr
          rw [hAD] at hrev2
          have hee : e = ac0 := by
            rw [hrev] at hrev2; injection hrev2 with h1 _; exact h1.symm
          have hmem0 : ac0 ∈ (wcnf w L).1.dropWhile (fun z : Term × Term => le w z.1) := by
            rw [← hee, ← List.mem_reverse, hDr]; exact List.Mem.head _
          rw [hsp ac0 hmem0] at hfire
          exact Bool.noConfusion hfire

/-- **§104 が名指しした欠けている補題。**  最後の対が発火するなら**どの対も**発火する。 -/
theorem allFire_of_lastFire109 {x : Term} (hx : inT x = true) (h : lastFire92 x = true) :
    allFire101 x = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  refine List.all_eq_true.mpr ?_
  unfold lastFire92 at h
  cases hrev : (wcnf (reg 1) (toList x)).1.reverse with
  | nil => rw [hrev] at h; exact absurd h Bool.noConfusion
  | cons ac0 t =>
      rw [hrev] at h
      exact allFire_of_lastFireL109 (isSC_reg_succ 0) (inT_reg 1)
        (show (reg 1).isAP = true from rfl) (toList x) hc hd hrev h

/-- 逆 — `Ω₁ ≤ x` なら対の列は空でないので、全発火は最後の発火。 -/
theorem lastFire_of_allFire109 {x : Term} (hx : inT x = true) (hW : le (reg 1) x = true)
    (h : allFire101 x = true) : lastFire92 x = true := by
  have hne := wcnf_fst_ne_nil81 hx hW
  unfold lastFire92
  cases hrev : (wcnf (reg 1) (toList x)).1.reverse with
  | nil =>
      exact absurd (by
        rw [← List.reverse_reverse ((wcnf (reg 1) (toList x)).1), hrev]; rfl) hne
  | cons ac0 t =>
      exact List.all_eq_true.mp h ac0 (by rw [← List.mem_reverse, hrev]; exact List.Mem.head _)

end

/-! ### §109.2 `a` の折り畳みが発火するなら `b` の折り畳みも頭で発火する -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 指数の枠はいちど `some` になったら `some` のまま。 -/
theorem fold_fst_some109 : ∀ (l : List (Term × Term)) (s : Option Term × Option Term),
    s.1 ≠ none → (l.foldl (stepF (reg 1) (baseOf 0)) s).1 ≠ none
  | [], _, h => h
  | ac :: t, s, h => fold_fst_some109 t _ (by
      rw [stepF_fst]
      split
      · intro hc; cases hc
      · exact h)

/-- 頭の対が発火すれば指数が出る。 -/
theorem idxF_some_of_head109 {Y : Term} {ac0 : Term × Term} {ps : List (Term × Term)}
    (hW : (wcnf (reg 1) (toList Y)).1 = ac0 :: ps)
    (hfq : le (reg 1) ac0.1 = true) : ∃ j, idxF88 0 Y = some j := by
  have hne : idxF88 0 Y ≠ none := by
    show ((wcnf (reg 1) (toList Y)).1.foldl
      (init := ((none : Option Term), (none : Option Term)))
      (stepF (reg 1) (baseOf 0))).1 ≠ none
    rw [hW]
    refine fold_fst_some109 ps _ ?_
    rw [stepF_fst, if_pos hfq]
    intro hc; cases hc
  cases hj : idxF88 0 Y with
  | none => exact absurd hj hne
  | some j => exact ⟨j, rfl⟩

/-- **§109.2 の主定理 — 発火は右に伝わる。**  `X` の折り畳みが最後の対で発火し
    `X < Y` なら、`Y` の折り畳みは**頭の対で**発火する。証明は §109.1 の
    `fireMono109` と頭部の単調性だけ — 門も橋も使わない。 -/
theorem fireHead109 {X Y : Term} (hX : inT X = true) (hY : inT Y = true)
    (hfa : lastFire92 X = true) (hlt : lt X Y = true) :
    ∃ q c ps, (wcnf (reg 1) (toList Y)).1 = (wA (reg 1) q, c) :: ps ∧
      le (reg 1) (wA (reg 1) q) = true := by
  have hall := allFire_of_lastFire109 hX hfa
  cases hXl : (wcnf (reg 1) (toList X)).1 with
  | nil =>
      exfalso
      unfold lastFire92 at hfa
      rw [hXl] at hfa
      exact Bool.noConfusion hfa
  | cons ac0 ps0 =>
      obtain ⟨p, s, hXt, hpw, hp1⟩ := wcnf_fst_cons109 (toList X) ac0 ps0 hXl
      have hfp : le (reg 1) (wA (reg 1) p) = true := by
        rw [← hp1]
        exact List.all_eq_true.mp hall ac0 (by rw [hXl]; exact List.Mem.head _)
      have hYne : Y ≠ zero := by
        intro hc; rw [hc, lt_zero_right] at hlt; exact Bool.noConfusion hlt
      cases hYt : toList Y with
      | nil => exact absurd (toList_eq_nil Y hYt) hYne
      | cons q rest =>
          have hip : inT p = true := inTL_inT hX p (by rw [hXt]; exact List.Mem.head _)
          have hap : p.isAP = true := inTL_isAP hX p (by rw [hXt]; exact List.Mem.head _)
          have hiq : inT q = true := inTL_inT hY q (by rw [hYt]; exact List.Mem.head _)
          have haq : q.isAP = true := inTL_isAP hY q (by rw [hYt]; exact List.Mem.head _)
          have hpq : le p q = true := hd_mono_inT hX hY hXt hYt (le_of_lt94 hlt)
          have hqw : lt q (reg 1) = false := by
            cases hc : lt q (reg 1) with
            | false => rfl
            | true =>
                exfalso
                have := lt_of_le_of_lt3 (inT_le_fragR p hip) (inT_le_fragR q hiq)
                  (inT_le_fragR _ inT_W79) hpq hc
                rw [this] at hpw
                exact Bool.noConfusion hpw
          obtain ⟨c, ps, he⟩ := wcnfFstHd109 (w := reg 1) rest hqw
          refine ⟨q, c, ps, he, ?_⟩
          exact fireMono109 (isSC_reg_succ 0) (inT_reg 1) (show (reg 1).isAP = true from rfl)
            haq hiq hqw hap hip hpw hpq hfp

/-- **系 — 発火する `X` の上に `Y` があれば `Y` は指数を出す。** -/
theorem idxF_some109 {X Y : Term} (hX : inT X = true) (hY : inT Y = true)
    (hfa : lastFire92 X = true) (hlt : lt X Y = true) : ∃ j, idxF88 0 Y = some j := by
  obtain ⟨q, c, ps, hW, hfq⟩ := fireHead109 hX hY hfa hlt
  exact idxF_some_of_head109 hW hfq

end

/-! ### §109.3 Veblen の尾は前置きの `ψ_{Ω₁}` を狭義に超える -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- **§95.1 の `le_psi_phiNF95` の狭義版。**  入口が狭義なら出口も狭義 — `phiNF` が
    値を返す枝は「引数そのもの」か「`φ̄` の項」しかなく、前者は仮定が狭義、
    後者は `lt_psi_phi_of_le` が狭義を返すからである。 -/
theorem lt_psi_phiNF109 {k c a X x : Term} {s : List Term}
    (hfw : FragR (psi k c) = true) (hX : inT X = true)
    (hl : toList X = x :: s) (hwx : le (psi k c) x = true)
    (hlt : lt (psi k c) X = true) : lt (psi k c) (phiNF a X) = true := by
  have hix : inT x = true := inTL_inT hX x (by rw [hl]; exact List.Mem.head _)
  have h1x : lt TM.Term.one x = true :=
    lt_of_lt_of_le3 (show FragR TM.Term.one = true from rfl) hfw (inT_le_fragR x hix)
      (lt_one_psi95 k c) hwx
  have hwX : le (psi k c) X = true := le_of_lt94 hlt
  have hXne : X ≠ zero := by
    intro hc; rw [hc] at hl; exact List.cons_ne_nil x s hl.symm
  have hdown : le (psi k c) (plus (splitFin X).1 (ofNat ((splitFin X).2 - 1))) = true :=
    le_trans3 hfw (inT_le_fragR x hix)
      (inT_le_fragR _ (inT_plus (inT_splitFin hX) (inT_ofNat _))) hwx
      (le_hd_down95 hX hl h1x)
  have hdef : lt (psi k c) (phiNFdefault a X) = true := by
    unfold phiNFdefault
    split
    · rename_i h
      exact absurd (eq_of_beq ((Bool.and_eq_true _ _).mp h).1) hXne
    · exact lt_psi_phi_of_le hwX
  have hsucc : lt (psi k c) (phiNFsucc a X) = true := by
    unfold phiNFsucc
    split
    rename_i heq
    rw [heq] at hdown
    split
    · split <;> (split <;> first | exact lt_psi_phi_of_le hdown | exact hdef)
    · exact hdef
  unfold phiNF
  split
  · exact hlt
  · split
    · split
      · exact hlt
      · exact hsucc
    · exact hsucc

/-- `v` が加法主要で `c ≠ 0` なら `v < v ⊕ c`。 -/
theorem lt_self_plus109 {v cc : Term} (hv : inT v = true) (hap : v.isAP = true)
    (hcc : inT cc = true) (hne : cc ≠ zero) : lt v (plus v cc) = true := by
  cases hl : toList cc with
  | nil => exact absurd (toList_eq_nil cc hl) hne
  | cons c1 r =>
      have hic1 : inT c1 = true := inTL_inT hcc c1 (by rw [hl]; exact List.Mem.head _)
      rw [plus_cons66 hl, toList_isAP81 hap]
      by_cases hf : le c1 v = true
      · rw [List.filter_cons_of_pos hf]
        show lt v (add v (ofList (c1 :: r))) = true
        exact lt_head_add hap _
      · rw [List.filter_cons_of_neg (by simpa using hf),
          show (List.filter (fun a => le c1 a) ([] : List Term)) = [] from rfl,
          List.nil_append, ← hl, inT_ofList_toList cc hcc]
        exact lt_of_lt_of_le3 (inT_le_fragR v hv) (inT_le_fragR c1 hic1) (inT_le_fragR cc hcc)
          (lt_of_not_le_inT hic1 hv (bool_false hf)) (le_hd_self_inT hcc hl)

/-- **底 `w` の分解の係数は `0` でない。**  `wcnf` の係数は `ω` 冪か、その `plus`。 -/
theorem wcnf_cnz109 {w : Term} (hw : inT w = true) (hsc : w.isSC = true) : ∀ (L : List Term),
    inTL L = true → descL L = true → (∀ x ∈ L, lt x M = true) →
    ∀ ac ∈ (wcnf w L).1, ac.2 ≠ zero := by
  intro L
  induction L with
  | nil => intro _ _ _ ac hac; cases hac
  | cons p rest ih =>
    intro hc hd hm ac hac
    obtain ⟨⟨hap, hip⟩, hcr⟩ := inTL_cons.mp hc
    have hdr := descL_tail hd
    have hmr : ∀ x ∈ rest, lt x M = true := fun x hx => hm x (List.Mem.tail p hx)
    have hIH := ih hcr hdr hmr
    have hCne : wC w p ≠ zero := by
      intro hcc
      have hA : (wC w p).isAP = true :=
        isAP_omegaNF (ofList ((toList (logOm p)).filter (fun q => lt q w)))
      rw [hcc] at hA
      exact Bool.noConfusion hA
    by_cases hlp : lt p w = true
    · rw [wcnf_cons_lt hlp] at hac; cases hac
    · have hlp' : lt p w = false := bool_false hlp
      rw [wcnf_cons_ge hlp'] at hac
      cases hr : wcnf w rest with
      | mk fst snd =>
        rw [hr] at hac
        cases fst with
        | nil => rw [List.mem_singleton.mp hac]; exact hCne
        | cons ac0 ps =>
          cases ac0 with
          | mk a' c' =>
            have hmem0 : ((a', c') : Term × Term) ∈ (wcnf w rest).1 := by
              rw [hr]; exact List.Mem.head _
            have hc'inT : inT c' = true := by
              obtain ⟨_, hall⟩ := wcnf_spec_sc hw hsc rest hcr hdr hmr
              exact (hall _ hmem0).2.2.1
            have hplus : plus (wC w p) c' ≠ zero := by
              intro hcc
              have h1 : le (wC w p) (plus (wC w p) c') = true :=
                le_self_plus_ap81 (inT_wC hip) (isAP_omegaNF _) hc'inT
              rw [hcc] at h1
              rcases (Bool.or_eq_true _ _).mp h1 with he | hl2
              · exact hCne (eq_of_beq he)
              · rw [lt_zero_right] at hl2; exact Bool.noConfusion hl2
            have hac' : ac ∈ (if (wA w p == a') = true
                then ((wA w p, plus (wC w p) c') :: ps, snd)
                else ((wA w p, wC w p) :: (a', c') :: ps, snd)).1 := hac
            by_cases heq : (wA w p == a') = true
            · rw [if_pos heq] at hac'
              rcases List.mem_cons.mp hac' with h1 | h1
              · rw [h1]; exact hplus
              · exact hIH ac (by rw [hr]; exact List.Mem.tail _ h1)
            · rw [if_neg heq] at hac'
              rcases List.mem_cons.mp hac' with h1 | h1
              · rw [h1]; exact hCne
              · exact hIH ac (by rw [hr]; exact h1)

/-- 折り畳みの累算器は「今の指数の `ψ_{Ω₁}` そのもの」か「それより狭義に上」。 -/
def AccSt109 (s : Option Term × Option Term) : Prop :=
  (∀ v, s.2 = some v → v.isAP = true) ∧
  (∀ i, s.1 = some i → ∃ v, s.2 = some v ∧
      (v = psi (reg 1) i ∨ lt (psi (reg 1) i) v = true))

theorem accSt109_none : AccSt109 ((none : Option Term), (none : Option Term)) := by
  constructor
  · intro v h; cases h
  · intro i h; cases h

/-- **Veblen の一歩は狭義に上げる。**  係数が `0` でないので、累算器が
    `ψ_{Ω₁}(i)` ちょうどでも一歩で追い越す。 -/
theorem vebStrict109 {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (hidx : IdxInv92 s) (hg : AccSt109 s)
    (h3 : inT ac.2 = true) (hne : ac.2 ≠ zero) (hf : le (reg 1) ac.1 = false)
    {i : Term} (hi : s.1 = some i) :
    ∃ v, (stepF (reg 1) (baseOf 0) s ac).2 = some v ∧ lt (psi (reg 1) i) v = true := by
  obtain ⟨v, hv2, hdisj⟩ := hg.2 i hi
  have hapv : v.isAP = true := hg.1 v hv2
  have hiv : inT v = true := (hst.2 v hv2).1
  have hii : inT i = true := hidx i hi
  have hfw : FragR (psi (reg 1) i) = true := fragR_psi_reg92 (inT_le_fragR i hii)
  have hX : inT (plus v ac.2) = true := inT_plus hiv h3
  have hwv : le (psi (reg 1) i) v = true := by
    rcases hdisj with he | hlt
    · rw [he]; exact Evidence.WF.le_self _
    · exact le_of_lt94 hlt
  have hltX : lt (psi (reg 1) i) (plus v ac.2) = true := by
    rcases hdisj with he | hlt
    · rw [he]
      exact lt_self_plus109 (by rw [← he]; exact hiv)
        (show (psi (reg 1) i).isAP = true from rfl) h3 hne
    · exact lt_of_lt_of_le3 hfw (inT_le_fragR v hiv) (inT_le_fragR _ hX) hlt
        (le_self_plus_ap81 hiv hapv h3)
  obtain ⟨y, s', hyl, hwy⟩ := le_psi_hd_plus95 hfw hiv hapv h3 hwv
  refine ⟨phiNF ac.1 (plus v ac.2), ?_, lt_psi_phiNF109 hfw hX hyl hwy hltX⟩
  rw [stepF_snd_veb88 hf, hv2]

theorem accSt109_step {s : Option Term × Option Term} {ac : Term × Term}
    (hst : StInv s) (hidx : IdxInv92 s) (hg : AccSt109 s)
    (h3 : inT ac.2 = true) (hne : ac.2 ≠ zero) :
    AccSt109 (stepF (reg 1) (baseOf 0) s ac) := by
  cases hf : le (reg 1) ac.1 with
  | true =>
    constructor
    · intro v hv
      rw [stepF_snd_fire88 hf] at hv
      rw [← Option.some.inj hv]; rfl
    · intro i hi
      rw [stepF_fst, if_pos hf] at hi
      refine ⟨psi (reg 1) (idxOf (reg 1) s ac), stepF_snd_fire88 hf, Or.inl ?_⟩
      rw [← Option.some.inj hi]
  | false =>
    have hnf : ¬ (le (reg 1) ac.1 = true) := by rw [hf]; exact Bool.noConfusion
    constructor
    · intro v hv
      rw [stepF_snd_veb88 hf] at hv
      rw [← Option.some.inj hv]
      exact isAP_phiNF _ _
    · intro i hi
      have hs1 : s.1 = some i := by
        have h : (stepF (reg 1) (baseOf 0) s ac).1 = s.1 := by rw [stepF_fst, if_neg hnf]
        rw [← h]; exact hi
      obtain ⟨v, hv2, hlt⟩ := vebStrict109 hst hidx hg h3 hne hf hs1
      exact ⟨v, hv2, Or.inr hlt⟩

theorem accSt109_fold : ∀ (l : List (Term × Term)) (s : Option Term × Option Term),
    StInv s → IdxInv92 s → AccSt109 s →
      (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
      (∀ ac ∈ l, ac.2 ≠ zero) →
      (∀ p ∈ scanSt (reg 1) (baseOf 0) s l, le (reg 1) p.2.1 = true →
          inT (psi (reg 1) (idxOf (reg 1) p.1 p.2)) = true) →
      AccSt109 (l.foldl (stepF (reg 1) (baseOf 0)) s) := by
  intro l
  induction l with
  | nil => intro s _ _ hg _ _ _; exact hg
  | cons ac t ih =>
    intro s hst hidx hg hall hnz hpsi
    have hac := hall ac (List.Mem.head _)
    have h1 : StInv (stepF (reg 1) (baseOf 0) s ac) :=
      stepF_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0) hst hac
        (hpsi (s, ac) (List.Mem.head _))
    have h2 : IdxInv92 (stepF (reg 1) (baseOf 0) s ac) :=
      idxInv92_step (inT_reg 1) hidx hac.1 hac.2.2.1
    have h3 : AccSt109 (stepF (reg 1) (baseOf 0) s ac) :=
      accSt109_step hst hidx hg hac.2.2.1 (hnz ac (List.Mem.head _))
    exact ih _ h1 h2 h3 (fun a ha => hall a (List.Mem.tail _ ha))
      (fun a ha => hnz a (List.Mem.tail _ ha))
      (fun p hp => hpsi p (List.Mem.tail _ hp))

theorem scanSt_append109 {w base : Term} : ∀ (l1 l2 : List (Term × Term))
    (s : Option Term × Option Term),
    scanSt w base s (l1 ++ l2)
      = scanSt w base s l1 ++ scanSt w base (l1.foldl (stepF w base) s) l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 s; rfl
  | cons ac t ih =>
    intro l2 s
    show (s, ac) :: scanSt w base (stepF w base s ac) (t ++ l2)
      = ((s, ac) :: scanSt w base (stepF w base s ac) t) ++ _
    rw [ih l2 (stepF w base s ac)]
    rfl

/-- **§109.3 の主定理 — 最後の対が発火しないなら、値は指数の `ψ_{Ω₁}` を狭義に超える。**
    §95.1 の `accGeb95` は `≤` までしか言わない。狭義の差は「係数は `0` でない」
    (§109.3 の `wcnf_cnz109`) 一点から出る。 -/
theorem accGt109 {x : Term} (hx : inT x = true) (hlx : lt x M = true) (Hp : PsiIdxOK 0 x)
    {j : Term} (hj : idxF88 0 x = some j) (hnf : lastFire92 x = false) :
    lt (psi (reg 1) j) (accW89 x) = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨_, hallOK⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList x) hc hd
    (ltM_toList x hx hlx)
  have hnzAll := wcnf_cnz109 (inT_reg 1) (isSC_reg_succ 0) (toList x) hc hd
    (ltM_toList x hx hlx)
  cases hrev : (wcnf (reg 1) (toList x)).1.reverse with
  | nil =>
      exfalso
      have hnil : (wcnf (reg 1) (toList x)).1 = [] := by
        rw [← List.reverse_reverse ((wcnf (reg 1) (toList x)).1), hrev]; rfl
      rw [idxF88_none_of_nil90 hnil] at hj
      cases hj
  | cons ac t =>
      have hfl : le (reg 1) ac.1 = false := by
        unfold lastFire92 at hnf; rw [hrev] at hnf; exact hnf
      have hsplit : (wcnf (reg 1) (toList x)).1 = t.reverse ++ [ac] := by
        rw [← List.reverse_reverse ((wcnf (reg 1) (toList x)).1), hrev, List.reverse_cons]
      have hmemL : ∀ z ∈ t.reverse, z ∈ (wcnf (reg 1) (toList x)).1 := by
        intro z hz; rw [hsplit]; exact List.mem_append_left _ hz
      have hmemAc : ac ∈ (wcnf (reg 1) (toList x)).1 := by
        rw [hsplit]; exact List.mem_append_right _ (List.Mem.head _)
      have hscan : ∀ p ∈ scanSt (reg 1) (baseOf 0) (none, none) t.reverse,
          le (reg 1) p.2.1 = true →
          inT (psi (reg 1) (idxOf (reg 1) p.1 p.2)) = true := by
        intro p hp
        refine Hp p ?_
        rw [hsplit, scanSt_append109]
        exact List.mem_append_left _ hp
      have hstS : StInv (t.reverse.foldl (stepF (reg 1) (baseOf 0)) (none, none)) :=
        fold_inv mulDescInT (inT_reg 1) (ltM_reg 1) (inT_baseOf 0) (ltM_baseOf 0)
          t.reverse (none, none) stInv_none (fun z hz => hallOK z (hmemL z hz)) hscan
      have hidxS : IdxInv92 (t.reverse.foldl (stepF (reg 1) (baseOf 0)) (none, none)) :=
        idxInv92_fold (inT_reg 1) t.reverse (none, none) idxInv92_none
          (fun z hz => ⟨(hallOK z (hmemL z hz)).1, (hallOK z (hmemL z hz)).2.2.1⟩)
      have hgS : AccSt109 (t.reverse.foldl (stepF (reg 1) (baseOf 0)) (none, none)) :=
        accSt109_fold t.reverse (none, none) stInv_none idxInv92_none accSt109_none
          (fun z hz => hallOK z (hmemL z hz)) (fun z hz => hnzAll z (hmemL z hz)) hscan
      have hfold : (wcnf (reg 1) (toList x)).1.foldl
            (init := ((none : Option Term), (none : Option Term)))
            (stepF (reg 1) (baseOf 0))
          = stepF (reg 1) (baseOf 0)
              (t.reverse.foldl (stepF (reg 1) (baseOf 0)) (none, none)) ac := by
        rw [hsplit, List.foldl_append]; rfl
      have hs1 : (t.reverse.foldl (stepF (reg 1) (baseOf 0)) (none, none)).1 = some j := by
        have h : (((wcnf (reg 1) (toList x)).1.foldl
            (init := ((none : Option Term), (none : Option Term)))
            (stepF (reg 1) (baseOf 0))).1) = some j := hj
        rw [hfold, stepF_fst, if_neg (by rw [hfl]; exact Bool.noConfusion)] at h
        exact h
      obtain ⟨v, hv2, hlt⟩ := vebStrict109 hstS hidxS hgS
        (hallOK ac hmemAc).2.2.1 (hnzAll ac hmemAc) hfl hs1
      show lt (psi (reg 1) j) (((wcnf (reg 1) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero) = true
      rw [hfold, hv2]
      exact hlt

/-- 最後の対が発火するなら指数は出る — §109.1 の全発火から頭の対が発火するので。 -/
theorem idxF_some_of_lastFire109 {x : Term} (hx : inT x = true) (h : lastFire92 x = true) :
    ∃ j, idxF88 0 x = some j := by
  cases hl : (wcnf (reg 1) (toList x)).1 with
  | nil =>
      exfalso
      unfold lastFire92 at h
      rw [hl] at h
      exact Bool.noConfusion h
  | cons ac0 ps =>
      refine idxF_some_of_head109 hl ?_
      exact List.all_eq_true.mp (allFire_of_lastFire109 hx h) ac0
        (by rw [hl]; exact List.Mem.head _)

end

/-! ### §109.4 `a` の側が発火する半分は、指数の**非狭義**の比較しか要らない -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- **混ざった場合の条項 — 非狭義。**  `a` の折り畳みは全発火、`b` のはそうでない。
    狭義の差は §109.3 の `accGt109` が Veblen の尾から只で出す。 -/
def IdxLeMix109 : Prop :=
  ∀ (a b : BT) (ja jb : Term), btLe72 1 a = true → btLe72 1 b = true →
    BT.isStd a = true → BT.isStd b = true →
    lastFire92 (dict a) = true → lastFire92 (dict b) = false →
    idxF88 0 (dict a) = some ja → idxF88 0 (dict b) = some jb →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true → le ja jb = true

/-- **§109.4 の主定理 — `a` の折り畳みが発火する半分は指数の比較だけで閉じる。**
    `b` が全発火なら §101.5 の `IdxMono101`、そうでなければ §109.2 が `b` の指数の
    存在を保証し、§109.3 が狭義の差を供給するので条項は非狭義で足りる。 -/
theorem hiMono_fireA109 (Hp : PsiIdxOKStd172) (H1 : IdxMono101) (H2 : IdxLeMix109)
    {a b : BT} (hbA : btLe72 1 (BT.D 0 a) = true) (hbB : btLe72 1 (BT.D 0 b) = true)
    (hsA : BT.isStd (BT.D 0 a) = true) (hsB : BT.isStd (BT.D 0 b) = true)
    (_hWa : le (reg 1) (dict a) = true) (hWb : le (reg 1) (dict b) = true)
    (hfa : lastFire92 (dict a) = true)
    (hlt : lt (hiW89 (dict a)) (hiW89 (dict b)) = true) :
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true := by
  have hba := (btLe72_D 1 0 a hbA).2
  have hbb := (btLe72_D 1 0 b hbB).2
  have hsa := isStd_of_D hsA
  have hsb := isStd_of_D hsB
  have hia := inT_dict_of_std172 Hp a hba hsa
  have hib := inT_dict_of_std172 Hp b hbb hsb
  obtain ⟨ja, hja⟩ := idxF_some_of_lastFire109 hia.1 hfa
  obtain ⟨jb, hjb⟩ : ∃ jb, idxF88 0 (dict b) = some jb := by
    have h := idxF_some109 (inT_hiW89 hia.1) (inT_hiW89 hib.1)
      (by rw [lastFire_hiW101 hia.1]; exact hfa) hlt
    rw [idxF_hiW101 hib.1] at h
    exact h
  cases hfb : lastFire92 (dict b) with
  | true => exact hiMonoFire_of_idxMono101 Hp H1 hba hsa hbb hsb hfa hfb hja hjb hlt
  | false =>
      have hpb : PsiIdxOK 0 (dict b) := Hp 0 b (by omega) hbb hsB
      have hva : collapse 0 (hiW89 (dict a)) = psi (reg 1) ja :=
        collapse0_hi_psi92 hia.1 hfa hja
      have hvb : collapse 0 (hiW89 (dict b)) = accW89 (dict b) :=
        collapse0_hi89 (dict b) hib.1 hib.2 hpb hWb
      have hgt : lt (psi (reg 1) jb) (accW89 (dict b)) = true :=
        accGt109 hib.1 hib.2 hpb hjb hfb
      have hle : le ja jb = true := H2 a b ja jb hba hbb hsa hsb hfa hfb hja hjb hlt
      have hija : inT ja = true := inT_idxF92 hia.1 hia.2 hja
      have hijb : inT jb = true := inT_idxF92 hib.1 hib.2 hjb
      have hacc : inT (accW89 (dict b)) = true :=
        (accW89_facts (dict b) hib.1 hib.2 hpb hWb).1
      have hpsle : le (psi (reg 1) ja) (psi (reg 1) jb) = true := by
        rcases (Bool.or_eq_true _ _).mp hle with he | hl2
        · rw [eq_of_beq he]; exact Evidence.WF.le_self _
        · exact le_of_lt94 (by rw [lt_psi_same]; exact hl2)
      rw [hva, hvb]
      exact lt_of_le_of_lt3 (fragR_psi_reg92 (inT_le_fragR ja hija))
        (fragR_psi_reg92 (inT_le_fragR jb hijb)) (inT_le_fragR _ hacc) hpsle hgt

/-- 残る半分 — `a` の折り畳みの最後の対が発火しない場合。 -/
def HiMonoVebA109 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lastFire92 (dict a) = false →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true

/-- **`HiMono89` は三つに割れる。** -/
theorem hiMono_of_three109 (Hp : PsiIdxOKStd172) (H1 : IdxMono101) (H2 : IdxLeMix109)
    (H3 : HiMonoVebA109) : HiMono89 := by
  intro a b hbA hbB hsA hsB hWa hWb hlt
  cases hfa : lastFire92 (dict a) with
  | true => exact hiMono_fireA109 Hp H1 H2 hbA hbB hsA hsB hWa hWb hfa hlt
  | false => exact H3 a b hbA hbB hsA hsB hWa hWb hfa hlt

/-- **326 行目を三つの条項に架け替える。** -/
theorem certIn_t326_109 (Hp : PsiIdxOKStd172) (H1 : IdxMono101) (H2 : IdxLeMix109)
    (H3 : HiMonoVebA109) (HD1 : DictOntoMidOpen103) (HD3 : DictDenseMid107)
    (HD4 : DictDenseAbove107) (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_107 Hp (hiMono_of_three109 Hp H1 H2 H3) HD1 HD3 HD4 hacc

/-- 混ざった場合に**狭義**の比較を課した条項。 -/
def IdxLtMix109 : Prop :=
  ∀ (a b : BT) (ja jb : Term), btLe72 1 a = true → btLe72 1 b = true →
    BT.isStd a = true → BT.isStd b = true →
    lastFire92 (dict a) = true → lastFire92 (dict b) = false →
    idxF88 0 (dict a) = some ja → idxF88 0 (dict b) = some jb →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true → lt ja jb = true

/-- 分離の証人 — `ψ₁ψ₁ψ₁0` と `ψ₁ψ₁ψ₁0 ⊕ Ω₁`、記号数 4 + 7。組んだのではなく
    §109.5 の母集団の中の**最小**のもの (`minSep109`)。 -/
def mixA109 : BT := w3_101
/-- その相棒 — 尾に `Ω₁` を一つ足しただけ。対の指数は `1` で、発火しない。 -/
def mixB109 : BT := BT.sum w3_101 w1_101

/-- **証人の性質、凍結。**  形の条件も `K` の条件も両方満たし、`a` は全発火、
    `b` は最後の対が発火せず、`hi` は狭義に増え、**指数は等しい**。それでも
    結論は成り立つ — 狭義の差は Veblen の尾が出している。 -/
theorem mixSep109 :
    (btLe72 1 mixA109, BT.isStd mixA109, BT.isStd (BT.D 0 mixA109),
     le (reg 1) (dict mixA109), lastFire92 (dict mixA109), allFire101 (dict mixA109),
     btLe72 1 mixB109, BT.isStd mixB109, BT.isStd (BT.D 0 mixB109),
     le (reg 1) (dict mixB109), lastFire92 (dict mixB109),
     lt (hiW89 (dict mixA109)) (hiW89 (dict mixB109)),
     idxF88 0 (dict mixA109) == idxF88 0 (dict mixB109),
     lt (collapse 0 (hiW89 (dict mixA109))) (collapse 0 (hiW89 (dict mixB109))),
     BT.size mixA109, BT.size mixB109)
    = (true, true, true, true, true, true,
       true, true, true, true, false, true, true, true, 4, 7) := rfl

/-- **否定 — 混ざった場合に狭義を課すと偽。**  §109.4 の条項が非狭義なのは
    弱めたのではなく、狭義では**成り立たない**からである。 -/
theorem not_idxLtMix109 : ¬ IdxLtMix109 := by
  intro H
  cases hj : idxF88 0 (dict mixA109) with
  | none =>
      have h : (idxF88 0 (dict mixA109)).isSome = true := rfl
      rw [hj] at h
      exact Bool.noConfusion h
  | some j0 =>
      have hjb : idxF88 0 (dict mixB109) = some j0 := by
        rw [← hj]
        exact eq_of_beq (show (idxF88 0 (dict mixB109) == idxF88 0 (dict mixA109)) = true from rfl)
      have h := H mixA109 mixB109 j0 j0 rfl rfl rfl rfl rfl rfl hj hjb rfl
      rw [lt_irrefl] at h
      exact Bool.noConfusion h

/-- **段の正直さ — 既知の反例はすべて `§109` が閉じなかった半分にいる。**  §101.4 の
    `bothBadA101`、§101.2 の `scBadA101`、§81 の `cexA89` はどれも最後の対が発火しない。 -/
theorem knownAreVeb109 :
    (lastFire92 (dict bothBadA101), lastFire92 (dict scBadA101), lastFire92 (dict cexA89))
    = (false, false, false) := rfl

end

/-! ### §109.5 測定 (凍結)

**構成 — 発火する線と発火しない線を両方組み、濾さない。**  §101・§104 の作り方に倣う。
発火するのは `ψ₁` の塔 (`ψ₁ψ₁0` 以上) で、発火しないのは帽子 `ψ₁ψ₀ z` と `Ω₁` 自身。

    fireSeed109  発火する種 5 個  (`ψ₁ψ₁0` 〜 `ψ₁ψ₁ψ₁ψ₁0`、幅つきも)
    vebSeed109   発火しない種 5 個 (`Ω₁` と帽子 4 個)
    pop109       その 2 項和・3 項和も入れた 120 項  濾さない

四つの場合がすべて母集団に入っていて、破れは `a` が発火しない側だけに出る。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

private def dedup109 (l : List BT) : List BT :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []

private def w4_109 : BT := BT.D 1 w3_101

private def fireSeed109 : List BT :=
  [w2_101, w3_101, w4_109, BT.D 1 (BT.sum w2_101 w2_101), BT.D 1 (BT.sum w3_101 w3_101)]
private def vebSeed109 : List BT :=
  [w1_101, BT.D 1 (BT.D 0 w1_101), BT.D 1 (BT.D 0 w2_101),
   BT.D 1 (BT.D 0 (BT.sum w2_101 w1_101)), BT.D 1 (BT.D 0 (BT.sum w3_101 w2_101))]
private def seeds109 : List BT := fireSeed109 ++ vebSeed109

private def pop109 : List BT :=
  dedup109 (seeds109
    ++ seeds109.flatMap (fun a => (seeds109.filter (fun b => BT.le b a)).map (BT.sum a))
    ++ seeds109.flatMap (fun a => (seeds109.filter (fun b => BT.le b a)).map
         (fun b => BT.sum a (BT.sum b b))))

private def ok109 (a : BT) : Bool := btLe72 1 a && BT.isStd a && le (reg 1) (dict a)
private def kstd109 (a : BT) : Bool := ok109 a && BT.isStd (BT.D 0 a)
private def samp109 : List BT := pop109.filter ok109
private def ksamp109 : List BT := pop109.filter kstd109

private def pairs109 (l : List BT) : List (BT × BT) :=
  l.flatMap (fun a => l.map (fun b => (a, b)))
private def resid109 (l : List BT) : List (BT × BT) :=
  (pairs109 l).filter (fun p => lt (hiW89 (dict p.1)) (hiW89 (dict p.2)))
private def bad109 (l : List BT) : List (BT × BT) :=
  (resid109 l).filter (fun p =>
    !(lt (collapse 0 (hiW89 (dict p.1))) (collapse 0 (hiW89 (dict p.2)))))
private def fr109 (a : BT) : Bool := allFire101 (dict a)
private def cls109 (l : List (BT × BT)) (x y : Bool) : List (BT × BT) :=
  l.filter (fun p => fr109 p.1 == x && fr109 p.2 == y)
private def hasIdx109 (a : BT) : Bool := (idxF88 0 (dict a)).isSome
private def jOf109 (a : BT) : Term := (idxF88 0 (dict a)).getD zero
private def idxBad109 (l : List BT) : List (BT × BT) :=
  (resid109 l).filter (fun p => fr109 p.1 && hasIdx109 p.2 && !(lt (jOf109 p.1) (jOf109 p.2)))

/-! 母集団の形。**120 項のうち全発火は 24 項**で、`K` 標準は 89 項。 -/
#guard (pop109.length, samp109.length, ksamp109.length,
        (pop109.map BT.size).foldl (fun a b => if a < b then b else a) 0) == (120, 120, 89, 32)

/-! **受領 1 — §109.1、見えている。**  `lastFire` と `allFire` は 120 項で一度も食い違わず、
    しかも全発火の 24 項のうち **12 項は対が 2 個以上**あるから、主張は空虚でない。 -/
#guard (samp109.countP (fun a => lastFire92 (dict a)),
        samp109.countP (fun a => allFire101 (dict a)),
        samp109.countP (fun a => lastFire92 (dict a) != allFire101 (dict a)),
        (samp109.filter fr109).countP
          (fun b => 2 ≤ (wcnf (reg 1) (toList (dict b))).1.length)) == (24, 24, 0, 12)

/-! **受領 2 — §109.2、見えている。**  120 項のうち **48 項は指数を持たない**。
    残余の対のうち `b` が指数を持たないものは 1128 組あり、**そのすべてで `a` は
    発火していない** — 仮定を外すと結論は 1128 回破れる。 -/
#guard (samp109.countP (fun b => !hasIdx109 b),
        ((resid109 samp109).filter (fun p => !hasIdx109 p.2)).length,
        ((resid109 samp109).filter (fun p => fr109 p.1 && !hasIdx109 p.2)).length)
        == (48, 1128, 0)

/-! **受領 3 — §109.3、見えている。**  指数を持ち全発火でない 48 項では
    `ψ_{Ω₁}(j) <` 値が**例外なく狭義**、全発火の 24 項では**一度も狭義でない**
    (値は `ψ_{Ω₁}(j)` そのもの)。 -/
#guard ((samp109.filter (fun b => hasIdx109 b && !fr109 b)).length,
        (samp109.filter (fun b => hasIdx109 b && !fr109 b)).countP
          (fun b => !(lt (psi (reg 1) (jOf109 b)) (collapse 0 (hiW89 (dict b))))),
        (samp109.filter fr109).countP
          (fun b => lt (psi (reg 1) (jOf109 b)) (collapse 0 (hiW89 (dict b))))) == (48, 0, 0)

/-! **受領 4 — 四つの場合の内訳。**  破れは `a` が発火しない側にしか出ない。
    形の条件だけの 120 項では (発火,発火) 276 組・破れ 0、(発火,Veblen) 360 組・破れ 0、
    (Veblen,発火) 1944 組・破れ 13、(Veblen,Veblen) 4560 組・破れ 375。 -/
#guard ([(true, true), (true, false), (false, true), (false, false)].map (fun c =>
    ((cls109 (resid109 samp109) c.1 c.2).length, (cls109 (bad109 samp109) c.1 c.2).length)))
    == [(276, 0), (360, 0), (1944, 13), (4560, 375)]
#guard ([(true, true), (true, false), (false, true), (false, false)].map (fun c =>
    ((cls109 (resid109 ksamp109) c.1 c.2).length, (cls109 (bad109 ksamp109) c.1 c.2).length)))
    == [(276, 0), (358, 0), (1202, 0), (2080, 0)]

/-! **受領 5 — §109.4 の非狭義は弱めではない。**  `a` が発火する残余は 636 組で、
    そこでは `ja ≤ jb` が**一度も破れない**が、`ja < jb` は **48 組で破れる**
    (`K` 標準に絞っても 46 組)。**その 48 組はすべて `ja = jb`** であって、
    順序が逆転しているものは一つもない。 -/
#guard (((resid109 samp109).filter (fun p => fr109 p.1)).length,
        ((resid109 samp109).filter (fun p => fr109 p.1)).countP
          (fun p => !(le (jOf109 p.1) (jOf109 p.2))),
        (idxBad109 samp109).length, (idxBad109 ksamp109).length,
        (idxBad109 samp109).countP (fun p => jOf109 p.1 == jOf109 p.2),
        (idxBad109 samp109).countP (fun p => lt (jOf109 p.2) (jOf109 p.1)))
        == (636, 0, 48, 46, 48, 0)

/-! **受領 6 — §109.4 の証人は掃いて出した最小のもの。**  46 組の `K` 標準な破れの
    どれも記号数の和は 11 以上で、`(mixA109, mixB109)` はその 11 を実現している。 -/
#guard (idxBad109 ksamp109).all (fun p => 11 ≤ BT.size p.1 + BT.size p.2)
#guard (idxBad109 ksamp109).contains (mixA109, mixB109)

end

/-! ## §112 `LeIdxSelf95` IS A THEOREM — THE COLLAPSE INDEX NEVER EXCEEDS ITS ARGUMENT

§95 hung ONE named piece of pure arithmetic on row 326 and nobody has attacked it since:

    `LeIdxSelf95` : `∀ x, inT x → x < M → PsiIdxOK 0 x → ∀ j, idxF88 0 x = some j → j ≤ x`

**§112 proves it.**  It also drops `PsiIdxOK 0 x` on the way — the fold's `.1` slot never
looks at the Veblen branch, so the (G3) side condition was never doing any work here.  There
is no `dict`, no `BT`, no gate in the section, exactly as §95 promised.

WHAT THE PROOF ACTUALLY NEEDED, AGAINST WHAT WAS NAMED AS MISSING.  §100 searched and named
two absent pieces for this clause; §105 searched independently and confirmed the same two: a
RECONSTRUCTION lemma for `wcnf`, and the distributivity of `mulL` in its right argument.
The score is one for two, plus one nobody named:

  * **The distributivity is genuinely required** and is proved here (`mulL_distrib112`, §112.3).
    `wcnf`'s merge branch replaces two components by one pair with coefficient `c ⊕ c'`, and
    without `ω^E·(c ⊕ c') = ω^E·c ⊕ ω^E·c'` the induction on the component list does not line
    up with the fold over the pair list at all.  21 of §112.7's 103 terms merge, so this is
    not a formality.
  * **The reconstruction is NOT required, and as an EQUATION it is FALSE.**  What §112.2 needs
    is one-sided: `Δ = ω^(Ω₁·(A ⊖ Ω₁))·C ≤ p`, the component the pair came from
    (`le_ddOf_self112`).  On §112.7's population 79 of 178 components have `Δ < p` STRICTLY
    (`lt_ddOf_recWit112` names one), so no equation of that shape can be proved.
  * **And it needed a third thing neither section named**: `plus` is monotone in its LEFT
    argument (`plus_mono_left112`, §112.1).  §65.6 has `plus_mono_right_inT` — with no side
    condition — but its twin was simply not in the repository, and it is spent three times
    (once per section).  This is §110's lesson word for word: identifying what is ABSENT is
    easier than identifying what is REQUIRED.

WHAT IS PROVED.

  §112.1  **`plus` IS MONOTONE ON THE LEFT.**  `le_tail_ofList112`, `le_subAP112`,
          `le_sub1_112` (`sub1` IS `subAP 1`), `le_tail_of_le_hd112`, and
          `plus_mono_left112` by induction on the length of the left component list,
          following `plus_cons`'s own branching.  No side condition, as on the right.

  §112.2  **ONE COMPONENT'S `Δ` DOES NOT EXCEED THAT COMPONENT.**  `plus_subAP112`
          (`w ⊕ (h ⊖ w) = h` for additively principal `w ≤ h`), `mulL_dig112` (the digitwise
          round trip `Ω₁·(q/Ω₁) = q`, the converse of §106's `divAP_dig106`), `mulL_wA112`
          (`Ω₁ · wA(p) = hi(logOm p)` — the whole high part comes back), `plus_hiW_loW112`,
          and `le_ddOf_self112`.  The inequality is the ONLY place `subAP` is used, and it is
          used only as "`subAP` goes down".  **The hypothesis `Ω₁ ≤ p` is not needed** — the
          bound holds at every additively principal component of 𝔗(M).

  §112.3  **`ω^E·` DISTRIBUTES OVER `⊕`.**  `dig_le112` (one digit's comparison is preserved
          exactly, from §110's `dig_smono110`), `map_filter112`, and `mulL_distrib112`.

  §112.4  **THE SUM OF THE `Δ`s DOES NOT EXCEED THE TERM.**  `sumDD112` and
          `le_sumDD_wcnf112`, by induction on the component list; the merge branch is exactly
          where §112.3 is spent and the other two branches are `rfl`.

  §112.5  **THE FOLD DOES NOT EXCEED THE SUM.**  `fold_idx_le112` (an index is already in the
          accumulator) and `fold_idx_le_none112` (none yet — the first firing step spends
          `⊖ 1`, and that is the second place §112.1 is spent).  `leIdxSelf112` is the
          conclusion, and `PsiIdxOK` appears in neither.

  §112.6  **ROW 326.**  `psiIdxStep073_of_idxStd112`, `certIn_t326_idx112`,
          `certIn_t326_coef112` and `certIn_t326_idx112'` are §110's and §105's conclusions
          with `LeIdxSelf95` discharged.

WHAT IS **NOT** CLAIMED.  The gate is NOT closed.  `IdxStd110` / `CoefLtStd110` are §110's
clause untouched and unproved, and `DictLtStd92` and `HiMono89` are untouched too.  §112
REMOVES a residue rather than moving one — `LeIdxSelf95` is discharged outright and nothing
takes its place — but it removes only its own, the smallest of the four the `idx` line
carried.  On the `idx`/`coef` line row 326 now rests on `DictLtStd92`, `HiMono89`,
`IdxStd110` (or `CoefLtStd110`) and `LimDecS1` / `LimIncS1` / `LimCofS1`, and on nothing
else on the `K` side; §109's line is untouched.

WHAT THE MEASUREMENT SAYS (§112.7 gives the construction).  The population is BUILT, not
enumerated: nine additively principal terms mixing `Ω₁`-digits and `Ω₂`-digits, then all
2-term sums, the singletons, the triples `a ⊕ a ⊕ a`, and four hand-built deep terms — 103
terms, all legal.

  * **The population is blind to no branch of the proof.**  95 have a collapse index; 21 make
    `wcnf` MERGE; 29 have two or more pairs and the deepest has four; 8 mix a firing pair
    with a non-firing one; 7 have the `⊖ 1` of the first firing step actually bite.
  * **`j ≤ x` : 0 failures on 103.**  That is a consistency check, not evidence — it is a
    theorem now.  All 103 also pass `psiIdxOKb`, which is why dropping `PsiIdxOK` had to be
    justified by reading the proof and not by the sweep.
  * **`j < x` FAILS 33 times**, and the smallest witness is `Ω₂ = Z1` — **4 symbols**, where
    the collapse index is the term ITSELF (`not_ltIdxSelf112`).  Every one of the 33 has an
    `A` whose head is above `Ω₁`, so `A ⊖ Ω₁ = A` and the step is the identity.  The `≤` in
    §95's clause is not a weakening; it is the truth.
  * **The reconstruction equation fails on 79 of 178 components** and the inequality fails on
    none.  `Δ = p` exactly at 99, `Δ < p` at 79, `Δ > p` never. -/

/-! ### §112.1 和の左単調性 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 先頭を落とすと下がる。 -/
theorem le_tail_ofList112 {b : Term} : ∀ (s : List Term), inT (ofList (b :: s)) = true →
    le (ofList s) (ofList (b :: s)) = true
  | [], _ => Evidence.Region.le_zero_left _
  | c :: r, h => by
      rw [show ofList (b :: c :: r) = add b (ofList (c :: r)) from rfl] at h ⊢
      exact le_right_add97 h

/-- `subAP` は下げるだけ。 -/
theorem le_subAP112 {w x : Term} (hx : inT x = true) : le (subAP w x) x = true := by
  cases hl : toList x with
  | nil => rw [subAP_nil w x hl]; exact Evidence.Region.le_zero_left _
  | cons b s =>
      have heq : ofList (b :: s) = x := by rw [← hl]; exact inT_ofList_toList x hx
      rw [subAP_cons w x b s hl]
      by_cases hb : (b == w) = true
      · rw [if_pos hb]
        have h2 := le_tail_ofList112 (b := b) s (by rw [heq]; exact hx)
        rw [heq] at h2
        exact h2
      · rw [if_neg hb]; exact Evidence.WF.le_self x

theorem sub1_eq_subAP112 (c : Term) : sub1 c = subAP TM.Term.one c := rfl

theorem le_sub1_112 {c : Term} (hc : inT c = true) : le (sub1 c) c = true := by
  rw [sub1_eq_subAP112]; exact le_subAP112 hc

/-- 尾の `𝔗(M)` 性。 -/
theorem inT_tail112 {a c : Term} {E : List Term} (ha : inT a = true)
    (hE : toList a = c :: E) : inT (ofList E) = true := by
  obtain ⟨hc, hd⟩ := inT_toList a ha
  rw [hE] at hc hd
  exact inT_ofList E (inTL_cons.mp hc).2 (descL_tail hd)

/-- 頭が同じなら尾も比べられる。 -/
theorem le_tail_of_le_hd112 {a a' c : Term} {E F : List Term} (ha : inT a = true)
    (ha' : inT a' = true) (hE : toList a = c :: E) (hF : toList a' = c :: F)
    (h : le a a' = true) : le (ofList E) (ofList F) = true := by
  have hiE := inT_tail112 ha hE
  have hiF := inT_tail112 ha' hF
  rcases lt_trichotomy_inT hiE hiF with hq | hq | hq
  · exact le_of_lt hq.1
  · rw [hq.2.1]; exact Evidence.WF.le_self _
  · exfalso
    have h2 : lt a' a = true := lt_of_hd_eq77 ha' ha hF hE hq.2.2
    rcases (Bool.or_eq_true _ _).mp h with he | hl
    · rw [eq_of_beq he, lt_irrefl] at h2; exact Bool.noConfusion h2
    · rw [lt_asymm_inT ha ha' hl] at h2; exact Bool.noConfusion h2

/-- **§112.1 の主定理 — `· ⊕ c` は単調。**  §65.6 の `plus_mono_right_inT` の左側の双子で、
    こちらは repo に無かった。左の成分列の長さについての帰納で、`plus_cons` の分岐を
    そのままなぞる。 -/
theorem plus_mono_left_aux112 : ∀ (n : Nat) (a a' c : Term), (toList a).length ≤ n →
    inT a = true → inT a' = true → inT c = true → le a a' = true →
    le (plus a c) (plus a' c) = true := by
  intro n
  induction n with
  | zero =>
      intro a a' c hn ha ha' hc h
      have haz : a = zero := by
        cases hl : toList a with
        | nil => exact toList_eq_nil a hl
        | cons b s => exfalso; rw [hl, List.length_cons] at hn; omega
      subst haz
      rw [plus_zero_left_inT hc]
      exact le_self_plus75 ha' hc
  | succ n ih =>
      intro a a' c hn ha ha' hc h
      cases hX : toList c with
      | nil => rw [plus_nil hX, plus_nil hX]; exact h
      | cons x1 X' =>
        cases hE : toList a with
        | nil => rw [toList_eq_nil a hE, plus_zero_left_inT hc]; exact le_self_plus75 ha' hc
        | cons e1 E' =>
          cases hF : toList a' with
          | nil =>
              exfalso
              have haz : a = zero := by
                have hz : a' = zero := toList_eq_nil a' hF
                rw [hz] at h
                rcases (Bool.or_eq_true _ _).mp h with he | hl
                · exact eq_of_beq he
                · rw [lt_zero_right] at hl; exact Bool.noConfusion hl
              rw [haz] at hE
              exact List.cons_ne_nil e1 E' hE.symm
          | cons f1 F' =>
            have hie1 : inT e1 = true := inTL_inT ha e1 (by rw [hE]; exact List.Mem.head _)
            have hif1 : inT f1 = true := inTL_inT ha' f1 (by rw [hF]; exact List.Mem.head _)
            have hix1 : inT x1 = true := inTL_inT hc x1 (by rw [hX]; exact List.Mem.head _)
            have hle1 : le e1 f1 = true := hd_mono_inT ha ha' hE hF h
            have hia : inT (plus a c) = true := inT_plus ha hc
            have hia' : inT (plus a' c) = true := inT_plus ha' hc
            by_cases hx1 : le x1 e1 = true
            · have hx1' : le x1 f1 = true := le_trans_inT hix1 hie1 hif1 hx1 hle1
              have hpa : plus a c = add e1 (plus (ofList E') c) := by
                rw [plus_cons ha hc hE rfl hX, if_pos hx1]
              have hpa' : plus a' c = add f1 (plus (ofList F') c) := by
                rw [plus_cons ha' hc hF rfl hX, if_pos hx1']
              by_cases heq : e1 = f1
              · subst heq
                rw [hpa, hpa']
                refine le_add_tail ?_
                have hiE : inT (ofList E') = true := inT_tail112 ha hE
                have hiF : inT (ofList F') = true := inT_tail112 ha' hF
                have hlen : (toList (ofList E')).length ≤ n := by
                  have : toList (ofList E') = E' :=
                    toList_ofList89 (inTL_cons.mp (by rw [← hE]; exact (inT_toList a ha).1)).2
                  rw [this]
                  rw [hE, List.length_cons] at hn
                  omega
                exact ih (ofList E') (ofList F') c hlen hiE hiF hc
                  (le_tail_of_le_hd112 ha ha' hE hF h)
              · have hlt : lt e1 f1 = true := by
                  rcases (Bool.or_eq_true _ _).mp hle1 with he | hl
                  · exact absurd (eq_of_beq he) heq
                  · exact hl
                refine le_of_lt (lt_of_hd_lt (E' := toList (plus (ofList E') c))
                  (Y' := toList (plus (ofList F') c)) hia hia' ?_ ?_ hlt)
                · rw [hpa]; rfl
                · rw [hpa']; rfl
            · have hpa : plus a c = c := by
                rw [plus_cons ha hc hE rfl hX, if_neg hx1]
              rw [hpa]
              exact le_self_plus75 ha' hc

theorem plus_mono_left112 {a a' c : Term} (ha : inT a = true) (ha' : inT a' = true)
    (hc : inT c = true) (h : le a a' = true) : le (plus a c) (plus a' c) = true :=
  plus_mono_left_aux112 (toList a).length a a' c (Nat.le_refl _) ha ha' hc h

end

/-! ### §112.2 一成分ぶんの上界 — `Δ ≤ その成分` -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 各点で自分に戻る写像は列を動かさない。 -/
theorem map_self112 {f : Term → Term} : ∀ (l : List Term), (∀ t ∈ l, f t = t) → l.map f = l
  | [], _ => rfl
  | a :: r, h => by
      rw [List.map_cons, h a (List.Mem.head _),
        map_self112 r (fun t ht => h t (List.Mem.tail _ ht))]

/-- 全体が通る述語での `filter` は恒等。 -/
theorem filter_all112 {P : Term → Bool} : ∀ (l : List Term), (∀ a ∈ l, P a = true) →
    l.filter P = l
  | [], _ => rfl
  | a :: r, h => by
      rw [List.filter_cons_of_pos (h a (List.Mem.head _)),
        filter_all112 r (fun t ht => h t (List.Mem.tail _ ht))]

/-- `b ⊕ (残り) = 元の列`。 -/
theorem plus_ofList_cons112 : ∀ (b : Term) (s : List Term), inTL (b :: s) = true →
    descL (b :: s) = true → plus b (ofList s) = ofList (b :: s)
  | b, [], _, _ => by
      rw [show ofList ([] : List Term) = zero from rfl,
        plus_nil (show toList (zero : Term) = [] from rfl)]
      rfl
  | b, t :: r, hc, hd => by
      have hts : toList (ofList (t :: r)) = t :: r := toList_ofList89 (inTL_cons.mp hc).2
      have hbap : b.isAP = true := (inTL_cons.mp hc).1.1
      have hlt : le t b = true := (descL_cons.mp hd).1
      rw [plus_cons66 hts, toList_isAP81 hbap,
        show List.filter (fun a => le t a) [b] = [b] from by
          rw [List.filter_cons_of_pos (by rw [hlt])]; rfl]
      rfl

/-- **`w ⊕ (h ⊖ w) = h`。**  `w` が加法主要で `w ≤ h` なら `subAP` はちょうど引き算。 -/
theorem plus_subAP112 {w h : Term} (hw : inT w = true) (hwap : w.isAP = true)
    (hh : inT h = true) (hhw : lt h w = false) : plus w (subAP w h) = h := by
  have hlew : le w h = true :=
    le_of_not_lt3 (inT_le_fragR h hh) (inT_le_fragR w hw) hhw
  cases hl : toList h with
  | nil =>
      exfalso
      have hz : h = zero := toList_eq_nil h hl
      have hwz : w ≠ zero := by intro hc; rw [hc] at hwap; exact Bool.noConfusion hwap
      rw [hz, lt_zero_left hwz] at hhw
      exact Bool.noConfusion hhw
  | cons b s =>
      have heq : ofList (b :: s) = h := by rw [← hl]; exact inT_ofList_toList h hh
      have hleb : le w b = true := le_hd_of_le109 hw hwap hh hl hlew
      have hcs : inTL (b :: s) = true := by rw [← hl]; exact (inT_toList h hh).1
      have hds : descL (b :: s) = true := by rw [← hl]; exact (inT_toList h hh).2
      rw [subAP_cons w h b s hl]
      by_cases hb : (b == w) = true
      · rw [if_pos hb]
        have hbw : b = w := eq_of_beq hb
        rw [← hbw, plus_ofList_cons112 b s hcs hds, heq]
      · rw [if_neg hb]
        have hbne : b ≠ w := by intro hc; exact hb (by rw [hc]; exact beq_self_eq_true _)
        have hltwb : lt w b = true := by
          rcases (Bool.or_eq_true _ _).mp hleb with he | hl2
          · exact absurd (eq_of_beq he).symm hbne
          · exact hl2
        have hib : inT b = true := inTL_inT hh b (by rw [hl]; exact List.Mem.head _)
        have hnb : le b w = false := by
          cases hcc : le b w with
          | false => rfl
          | true =>
              exfalso
              rcases (Bool.or_eq_true _ _).mp hcc with he | hl2
              · exact hbne (eq_of_beq he)
              · rw [lt_asymm_inT hib hw hl2] at hltwb; exact Bool.noConfusion hltwb
        rw [plus_cons66 hl, toList_isAP81 hwap,
          show List.filter (fun a => le b a) [w] = [] from by
            rw [List.filter_cons_of_neg (by rw [hnb]; exact Bool.noConfusion)]; rfl,
          List.nil_append, heq]

/-- **一成分ぶんの往復 — `Ω₁ · (q / Ω₁) = q`。**  §106 の `divAP_dig106` の逆向きで、
    こちらは `Ω₁` 以上の成分についての等式である。 -/
theorem mulL_dig112 {q : Term} (hap : q.isAP = true) (hq : inT q = true)
    (hqM : lt q M = true) (hqw : lt q (reg 1) = false) :
    omegaNF (plus (reg 1) (logOm (divAP (reg 1) q))) = q := by
  have hg : inT (logOm q) = true := inT_logOm hq
  have hgM : lt (logOm q) M = true := ltM_logOm hq hqM
  have hY : inT (subAP (reg 1) (logOm q)) = true := inT_subAP hg
  have hYM : lt (subAP (reg 1) (logOm q)) M = true := ltM_subAP hg hgM
  show omegaNF (plus (reg 1) (logOm (omegaNF (subAP (reg 1) (logOm q))))) = q
  rw [logOm_omegaNF106 hY hYM,
    plus_subAP112 (inT_reg 1) (show isAP (reg 1) = true from rfl) hg
      (lt_logOm_of_sc (isSC_reg_succ 0) (inT_reg 1) hap hq hqw)]
  exact omegaNF_logOm100 hq hap hqM

theorem ltM_hiW112 {x : Term} (hx : inT x = true) (hxM : lt x M = true) :
    lt (hiW89 x) M = true := by
  refine lt_ofList_M _ ?_
  intro z hz
  exact ltM_toList x hx hxM z (List.mem_filter.mp hz).1

theorem ltM_loW112 {x : Term} (hx : inT x = true) (hxM : lt x M = true) :
    lt (loW89 x) M = true := by
  refine lt_ofList_M _ ?_
  intro z hz
  exact ltM_toList x hx hxM z (List.mem_filter.mp hz).1

/-- **§112.2 の第一の定理 — `Ω₁ · wA = hi`。**  対の指数に `Ω₁` を掛け戻すと、
    `logOm` の `Ω₁` 以上の部分がそのまま出る。 -/
theorem mulL_wA112 {p : Term} (hp : inT p = true) (hpM : lt p M = true) :
    mulL (reg 1) (wA (reg 1) p) = hiW89 (logOm p) := by
  have hg : inT (logOm p) = true := inT_logOm hp
  have hgM : lt (logOm p) M = true := ltM_logOm hp hpM
  have hH : inT (hiW89 (logOm p)) = true := inT_hiW89 hg
  have hA : inT (wA (reg 1) p) = true := inT_wA109 (inT_reg 1) (isSC_reg_succ 0) hp
  have htA : toList (wA (reg 1) p) = (toList (hiW89 (logOm p))).map (divAP (reg 1)) := by
    rw [toList_hiW89 hg]
    show toList (ofList (((toList (logOm p)).filter (fun q => !lt q (reg 1))).map
      (divAP (reg 1)))) = _
    refine toList_ofList _ ?_
    intro x hx
    obtain ⟨q, _, hxe⟩ := List.mem_map.mp hx
    rw [← hxe]; exact isAP_divAP _ _
  have hpt : ∀ t ∈ toList (hiW89 (logOm p)),
      ((fun r => omegaNF (plus (reg 1) (logOm r))) ∘ divAP (reg 1)) t = t := by
    intro t ht
    have hit : inT t = true := inTL_inT hH t ht
    have hat : t.isAP = true := inTL_isAP hH t ht
    have htM : lt t M = true := ltM_toList _ hH (ltM_hiW112 hg hgM) t ht
    exact mulL_dig112 hat hit htM (hiW89_ge89 hg t ht)
  have htM : toList (mulL (reg 1) (wA (reg 1) p)) = toList (hiW89 (logOm p)) := by
    rw [toList_mulLW106, htA, List.map_map]
    exact map_self112 _ hpt
  rw [← inT_ofList_toList _ (inT_mulL mulDescInT (inT_reg 1) hA), htM,
    inT_ofList_toList _ hH]

/-- `hi ⊕ lo = 元の項`。 -/
theorem plus_hiW_loW112 {x : Term} (hx : inT x = true) :
    plus (hiW89 x) (loW89 x) = x := by
  have hsp := toList_split89 hx
  cases hl : toList (loW89 x) with
  | nil =>
      rw [plus_nil hl]
      rw [hl, List.append_nil] at hsp
      have h2 := congrArg ofList hsp.symm
      rw [inT_ofList_toList _ (inT_hiW89 hx), inT_ofList_toList x hx] at h2
      exact h2
  | cons b1 r =>
      have hb1 : lt b1 (reg 1) = true :=
        loW89_lt89 hx b1 (by rw [hl]; exact List.Mem.head _)
      have hfil : (toList (hiW89 x)).filter (fun a => le b1 a) = toList (hiW89 x) := by
        refine filter_all112 _ ?_
        intro a ha
        have hia : inT a = true := inTL_inT (inT_hiW89 hx) a ha
        have haw : lt a (reg 1) = false := hiW89_ge89 hx a ha
        have hwa : le (reg 1) a = true :=
          le_of_not_lt3 (inT_le_fragR a hia) (inT_le_fragR _ (inT_reg 1)) haw
        exact le_trans_inT (inTL_inT (inT_loW89 hx) b1 (by rw [hl]; exact List.Mem.head _))
          (inT_reg 1) hia (le_of_lt hb1) hwa
      rw [plus_cons66 hl, hfil, ← hl, ← hsp, inT_ofList_toList x hx]

/-- `mulL E ·` は非狭義でも単調。 -/
theorem mulL_mono_right112 {E c c' : Term} (hE : inT E = true) (hc : inT c = true)
    (hc' : inT c' = true) (hcM : lt c M = true) (hc'M : lt c' M = true)
    (h : le c c' = true) : le (mulL E c) (mulL E c') = true := by
  rcases (Bool.or_eq_true _ _).mp h with he | hl
  · rw [eq_of_beq he]; exact Evidence.WF.le_self _
  · exact le_of_lt (mulL_smono_right110 hE hc hc' hcM hc'M hl)

/-- 加法主要な係数での積は一桁。 -/
theorem mulL_ap112 {E C : Term} (hC : C.isAP = true) :
    mulL E C = omegaNF (plus E (logOm C)) := by
  show ofList ((toList C).map (fun q => omegaNF (plus E (logOm q)))) = _
  rw [toList_isAP81 hC]
  rfl

/-- **§112.2 の主定理 — 一成分が立てる `Δ` はその成分を超えない。**
    `Δ = ω^(Ω₁·(A ⊖ Ω₁)) · C` で `p = ω^(Ω₁·A ⊕ lo)`、`C = ω^lo`。
    `subAP` は下げるだけだから `Ω₁·(A ⊖ Ω₁) ≤ Ω₁·A = hi` で、あとは
    `⊕ lo` の左単調性と `ω^·` の単調性である。 -/
theorem le_ddOf_self112 {p : Term} (hap : p.isAP = true) (hp : inT p = true)
    (hpM : lt p M = true) :
    le (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p)) p = true := by
  have hg : inT (logOm p) = true := inT_logOm hp
  have hgM : lt (logOm p) M = true := ltM_logOm hp hpM
  have hH : inT (hiW89 (logOm p)) = true := inT_hiW89 hg
  have hLo : inT (loW89 (logOm p)) = true := inT_loW89 hg
  have hLoM : lt (loW89 (logOm p)) M = true := ltM_loW112 hg hgM
  have hA : inT (wA (reg 1) p) = true := inT_wA109 (inT_reg 1) (isSC_reg_succ 0) hp
  have hAM : lt (wA (reg 1) p) M = true := ltM_wA hp hpM
  have hsA : inT (subAP (reg 1) (wA (reg 1) p)) = true := inT_subAP hA
  have hsAM : lt (subAP (reg 1) (wA (reg 1) p)) M = true := ltM_subAP hA hAM
  have hE : inT (mulL (reg 1) (subAP (reg 1) (wA (reg 1) p))) = true :=
    inT_mulL mulDescInT (inT_reg 1) hsA
  have hCeq : wC (reg 1) p = omegaNF (loW89 (logOm p)) := rfl
  have hlogC : logOm (wC (reg 1) p) = loW89 (logOm p) := by
    rw [hCeq]; exact logOm_omegaNF106 hLo hLoM
  have hdd : ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p)
      = omegaNF (plus (mulL (reg 1) (subAP (reg 1) (wA (reg 1) p))) (loW89 (logOm p))) := by
    show mulL (mulL (reg 1) (subAP (reg 1) (wA (reg 1) p))) (wC (reg 1) p) = _
    rw [mulL_ap112 (by rw [hCeq]; exact isAP_omegaNF _), hlogC]
  have hleE : le (mulL (reg 1) (subAP (reg 1) (wA (reg 1) p))) (hiW89 (logOm p)) = true := by
    rw [← mulL_wA112 hp hpM]
    exact mulL_mono_right112 (inT_reg 1) hsA hA hsAM hAM (le_subAP112 hA)
  have hstep : le (plus (mulL (reg 1) (subAP (reg 1) (wA (reg 1) p))) (loW89 (logOm p)))
      (logOm p) = true := by
    have h1 := plus_mono_left112 hE hH hLo hleE
    rw [plus_hiW_loW112 hg] at h1
    exact h1
  have hfin : le (omegaNF (plus (mulL (reg 1) (subAP (reg 1) (wA (reg 1) p)))
      (loW89 (logOm p)))) (omegaNF (logOm p)) = true :=
    omegaNF_mono_inT (inT_plus hE hLo) hg hstep
  rw [omegaNF_logOm100 hp hap hpM] at hfin
  rw [hdd]
  exact hfin

end

/-! ### §112.3 `ω^E ·` は和を割る -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 各点で同値な述語なら `filter` と `map` は交換する。 -/
theorem map_filter112 {f : Term → Term} {P Q : Term → Bool} : ∀ (l : List Term),
    (∀ a ∈ l, Q (f a) = P a) → (l.filter P).map f = (l.map f).filter Q
  | [], _ => rfl
  | a :: r, h => by
      have hIH := map_filter112 (f := f) (P := P) (Q := Q) r
        (fun t ht => h t (List.Mem.tail _ ht))
      cases hp : P a with
      | true =>
          rw [List.filter_cons_of_pos hp, List.map_cons, List.map_cons,
            List.filter_cons_of_pos (by rw [h a (List.Mem.head _), hp]), hIH]
      | false =>
          rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.noConfusion), List.map_cons,
            List.filter_cons_of_neg (by rw [h a (List.Mem.head _), hp]; exact Bool.noConfusion),
            hIH]

/-- **一桁ぶんの比較はそのまま。**  `p ↦ ω^(E ⊕ logOm p)` は狭義単調だから、
    `≤` の値そのものが等しい。 -/
theorem dig_le112 {E a b : Term} (hE : inT E = true) (ha : inT a = true) (hapa : a.isAP = true)
    (haM : lt a M = true) (hb : inT b = true) (hapb : b.isAP = true) (hbM : lt b M = true) :
    le (omegaNF (plus E (logOm b))) (omegaNF (plus E (logOm a))) = le b a := by
  have hfa : inT (omegaNF (plus E (logOm a))) = true := inT_omegaNF (inT_plus hE (inT_logOm ha))
  have hfb : inT (omegaNF (plus E (logOm b))) = true := inT_omegaNF (inT_plus hE (inT_logOm hb))
  cases hba : le b a with
  | true =>
      rcases (Bool.or_eq_true _ _).mp hba with he | hl
      · rw [eq_of_beq he]; exact Evidence.WF.le_self _
      · exact le_of_lt (dig_smono110 hE hb hapb hbM ha hapa haM hl)
  | false =>
      have hab : lt a b = true := lt_of_not_le_inT hb ha hba
      have hff : lt (omegaNF (plus E (logOm a))) (omegaNF (plus E (logOm b))) = true :=
        dig_smono110 hE ha hapa haM hb hapb hbM hab
      cases hc : le (omegaNF (plus E (logOm b))) (omegaNF (plus E (logOm a))) with
      | false => rfl
      | true =>
          exfalso
          rcases (Bool.or_eq_true _ _).mp hc with he | hl
          · rw [eq_of_beq he, lt_irrefl] at hff; exact Bool.noConfusion hff
          · rw [lt_asymm_inT hfa hfb hff] at hl; exact Bool.noConfusion hl

theorem mulL_zero112 {E : Term} : mulL E zero = zero := rfl

/-- **§112.3 の主定理 — `ω^E·` は和について分配する。**  §100 が「この repo に無い」と
    名指しした二つのうちの一つ。`mulL` は桁ごとの写像で、その写像は狭義単調だから、
    `plus` の切り落としと交換する。 -/
theorem mulL_distrib112 {E c c' : Term} (hE : inT E = true) (hc : inT c = true)
    (hc' : inT c' = true) (hcM : lt c M = true) (hc'M : lt c' M = true) :
    mulL E (plus c c') = plus (mulL E c) (mulL E c') := by
  cases hX : toList c' with
  | nil =>
      have hz : c' = zero := toList_eq_nil c' hX
      subst hz
      rw [plus_nil (show toList (zero : Term) = [] from rfl), mulL_zero112,
        plus_nil (show toList (zero : Term) = [] from rfl)]
  | cons b1 r =>
      have hib1 : inT b1 = true := inTL_inT hc' b1 (by rw [hX]; exact List.Mem.head _)
      have hapb1 : b1.isAP = true := inTL_isAP hc' b1 (by rw [hX]; exact List.Mem.head _)
      have hb1M : lt b1 M = true := ltM_toList c' hc' hc'M b1 (by rw [hX]; exact List.Mem.head _)
      have hT' : toList (mulL E c')
          = omegaNF (plus E (logOm b1)) :: r.map (fun q => omegaNF (plus E (logOm q))) := by
        rw [toList_mulL110, hX, List.map_cons]
      have hpt : ∀ a ∈ toList c,
          (fun q => le (omegaNF (plus E (logOm b1))) q)
            ((fun q => omegaNF (plus E (logOm q))) a) = (fun q => le b1 q) a := by
        intro a ha
        exact dig_le112 hE (inTL_inT hc a ha) (inTL_isAP hc a ha) (ltM_toList c hc hcM a ha)
          hib1 hapb1 hb1M
      show ofList ((toList (plus c c')).map (fun q => omegaNF (plus E (logOm q)))) = _
      rw [toList_plus_inT hc hc' hX, List.map_append,
        map_filter112 (f := fun q => omegaNF (plus E (logOm q)))
          (P := fun q => le b1 q) (Q := fun q => le (omegaNF (plus E (logOm b1))) q)
          (toList c) hpt,
        plus_cons66 hT', toList_mulL110, hX, List.map_cons]

end

/-! ### §112.4 対の列が立てる `Δ` の総和は元の項を超えない -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 対の列が立てる `Δ` の総和。畳み込みが積む順そのまま (右結合)。 -/
def sumDD112 (w : Term) : List (Term × Term) → Term
  | [] => zero
  | ac :: t => plus (ddOf75 w ac) (sumDD112 w t)

theorem sumDD_cons112 (w : Term) (ac : Term × Term) (t : List (Term × Term)) :
    sumDD112 w (ac :: t) = plus (ddOf75 w ac) (sumDD112 w t) := rfl

theorem inT_sumDD112 {w : Term} (hw : inT w = true) : ∀ (ps : List (Term × Term)),
    (∀ ac ∈ ps, inT ac.1 = true ∧ inT ac.2 = true) → inT (sumDD112 w ps) = true
  | [], _ => inT_zero
  | ac :: t, h => by
      refine inT_plus (inT_ddOf75 hw (h ac (List.Mem.head _)).1 (h ac (List.Mem.head _)).2) ?_
      exact inT_sumDD112 hw t (fun a ha => h a (List.Mem.tail _ ha))

/-- **§112.4 の主定理 — 総和は元の項以下。**  一成分ぶんの上界 (§112.2) を成分列に沿って
    足し合わせるだけだが、`wcnf` の併合枝でだけ `ω^E·` の分配則 (§112.3) が要る。 -/
theorem le_sumDD_wcnf112 : ∀ (L : List Term), inTL L = true → descL L = true →
    (∀ x ∈ L, lt x M = true) →
    le (sumDD112 (reg 1) (wcnf (reg 1) L).1) (ofList L) = true := by
  intro L
  induction L with
  | nil => intro _ _ _; exact Evidence.Region.le_zero_left _
  | cons p rest ih =>
    intro hc hd hm
    obtain ⟨⟨hap, hip⟩, hcr⟩ := inTL_cons.mp hc
    have hdr := descL_tail hd
    have hmr : ∀ x ∈ rest, lt x M = true := fun x hx => hm x (List.Mem.tail p hx)
    have hpM : lt p M = true := hm p (List.Mem.head _)
    have IH := ih hcr hdr hmr
    have hiR : inT (ofList rest) = true := inT_ofList _ hcr hdr
    obtain ⟨_, hallR⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) rest hcr hdr hmr
    have hSum : inT (sumDD112 (reg 1) (wcnf (reg 1) rest).1) = true :=
      inT_sumDD112 (inT_reg 1) _ (fun ac hac => ⟨(hallR ac hac).1, (hallR ac hac).2.2.1⟩)
    by_cases hlp : lt p (reg 1) = true
    · rw [wcnf_cons_lt hlp]
      exact Evidence.Region.le_zero_left _
    · have hlp' : lt p (reg 1) = false := bool_false hlp
      have hA : inT (wA (reg 1) p) = true := inT_wA109 (inT_reg 1) (isSC_reg_succ 0) hip
      have hAM : lt (wA (reg 1) p) M = true := ltM_wA hip hpM
      have hC : inT (wC (reg 1) p) = true := inT_wC hip
      have hCM : lt (wC (reg 1) p) M = true := ltM_wC hip hpM
      have hE : inT (mulL (reg 1) (subAP (reg 1) (wA (reg 1) p))) = true :=
        inT_mulL mulDescInT (inT_reg 1) (inT_subAP hA)
      have hD : inT (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p)) = true :=
        inT_ddOf75 (inT_reg 1) hA hC
      have hsum : sumDD112 (reg 1) (wcnf (reg 1) (p :: rest)).1
          = plus (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p))
              (sumDD112 (reg 1) (wcnf (reg 1) rest).1) := by
        cases hr : wcnf (reg 1) rest with
        | mk fst snd =>
          have hRl : (wcnf (reg 1) rest).1 = fst := by rw [hr]
          cases fst with
          | nil =>
              have hW : (wcnf (reg 1) (p :: rest)).1 = [(wA (reg 1) p, wC (reg 1) p)] := by
                rw [wcnf_cons_ge hlp', hr]
              rw [hW]
              rfl
          | cons ac0 ps =>
              cases ac0 with
              | mk a' c' =>
                have hc'i : inT c' = true := by
                  have := hallR (a', c') (by rw [hRl]; exact List.Mem.head _); exact this.2.2.1
                have hc'M : lt c' M = true := by
                  have := hallR (a', c') (by rw [hRl]; exact List.Mem.head _); exact this.2.2.2
                by_cases heq : (wA (reg 1) p == a') = true
                · have hpa' : a' = wA (reg 1) p := (eq_of_beq heq).symm
                  have hW : (wcnf (reg 1) (p :: rest)).1
                      = (wA (reg 1) p, plus (wC (reg 1) p) c') :: ps := by
                    rw [wcnf_cons_ge hlp', hr]
                    show ((if (wA (reg 1) p == a') = true
                           then ((wA (reg 1) p, plus (wC (reg 1) p) c') :: ps, snd)
                           else ((wA (reg 1) p, wC (reg 1) p) :: (a', c') :: ps, snd))
                          : List (Term × Term) × Term).1 = _
                    rw [if_pos heq]
                  have hdist : ddOf75 (reg 1) (wA (reg 1) p, plus (wC (reg 1) p) c')
                      = plus (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p))
                          (ddOf75 (reg 1) (wA (reg 1) p, c')) :=
                    mulL_distrib112 hE hC hc'i hCM hc'M
                  rw [hW]
                  show plus (ddOf75 (reg 1) (wA (reg 1) p, plus (wC (reg 1) p) c'))
                      (sumDD112 (reg 1) ps)
                    = plus (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p))
                      (plus (ddOf75 (reg 1) (a', c')) (sumDD112 (reg 1) ps))
                  rw [hdist, hpa']
                  exact plus_assoc_inT _ _ _ hD
                    (inT_ddOf75 (inT_reg 1) hA hc'i)
                    (inT_sumDD112 (inT_reg 1) ps (fun ac hac =>
                      ⟨(hallR ac (by rw [hRl]; exact List.Mem.tail _ hac)).1,
                       (hallR ac (by rw [hRl]; exact List.Mem.tail _ hac)).2.2.1⟩))
                · have hW : (wcnf (reg 1) (p :: rest)).1
                      = (wA (reg 1) p, wC (reg 1) p) :: (a', c') :: ps := by
                    rw [wcnf_cons_ge hlp', hr]
                    show ((if (wA (reg 1) p == a') = true
                           then ((wA (reg 1) p, plus (wC (reg 1) p) c') :: ps, snd)
                           else ((wA (reg 1) p, wC (reg 1) p) :: (a', c') :: ps, snd))
                          : List (Term × Term) × Term).1 = _
                    rw [if_neg heq]
                  rw [hW]
                  rfl
      rw [hsum]
      have h1 : le (plus (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p))
            (sumDD112 (reg 1) (wcnf (reg 1) rest).1))
          (plus (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p)) (ofList rest)) = true :=
        plus_mono_right_inT _ hD _ _ hSum hiR IH
      have h2 : le (plus (ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p)) (ofList rest))
          (plus p (ofList rest)) = true :=
        plus_mono_left112 hD hip hiR (le_ddOf_self112 hap hip hpM)
      have h3 : plus p (ofList rest) = ofList (p :: rest) := plus_ofList_cons112 p rest hc hd
      rw [h3] at h2
      exact le_trans_inT (inT_plus hD hSum) (inT_plus hD hiR) (inT_ofList _ hc hd) h1 h2

end

/-! ### §112.5 畳み込みは総和を超えない — `LeIdxSelf95` -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

theorem idxOf_some112 {w : Term} {s : Option Term × Option Term} {ac : Term × Term} {i0 : Term}
    (hs1 : s.1 = some i0) : idxOf w s ac = plus i0 (ddOf75 w ac) := by
  show (match s.1 with
        | none => sub1 (mulL (mulL w (subAP w ac.1)) ac.2)
        | some j => plus j (mulL (mulL w (subAP w ac.1)) ac.2)) = _
  rw [hs1]
  rfl

theorem idxOf_none112 {w : Term} {s : Option Term × Option Term} {ac : Term × Term}
    (hs1 : s.1 = none) : idxOf w s ac = sub1 (ddOf75 w ac) := by
  show (match s.1 with
        | none => sub1 (mulL (mulL w (subAP w ac.1)) ac.2)
        | some j => plus j (mulL (mulL w (subAP w ac.1)) ac.2)) = _
  rw [hs1]
  rfl

/-- **指数が入っているときの畳み込みの上界。**  入ってきた指数に、対の列が立てる `Δ` の
    総和を足したものを超えない。`PsiIdxOK` は要らない — `.1` の枠しか触らないから、
    ヴェブレン枝の `𝔗(M)` 性はどこにも要らない。 -/
theorem fold_idx_le112 {w base : Term} (hw : inT w = true) :
    ∀ (ps : List (Term × Term)) (s : Option Term × Option Term) (i0 : Term),
      s.1 = some i0 → inT i0 = true →
      (∀ ac ∈ ps, inT ac.1 = true ∧ inT ac.2 = true) →
      ∀ j, (ps.foldl (stepF w base) s).1 = some j →
        inT j = true ∧ le j (plus i0 (sumDD112 w ps)) = true := by
  intro ps
  induction ps with
  | nil =>
      intro s i0 hs1 hi0 _ j hj
      have hji : j = i0 := by
        have hj2 : s.1 = some j := hj
        rw [hs1] at hj2
        exact (Option.some.inj hj2).symm
      subst hji
      refine ⟨hi0, ?_⟩
      rw [show sumDD112 w [] = zero from rfl,
        plus_nil (show toList (zero : Term) = [] from rfl)]
      exact Evidence.WF.le_self _
  | cons ac t ih =>
      intro s i0 hs1 hi0 hall j hj
      have hac := hall ac (List.Mem.head _)
      have hdd : inT (ddOf75 w ac) = true := inT_ddOf75 hw hac.1 hac.2
      have hSt : inT (sumDD112 w t) = true :=
        inT_sumDD112 hw t (fun a ha => hall a (List.Mem.tail _ ha))
      have hfold : ((ac :: t).foldl (stepF w base) s)
          = t.foldl (stepF w base) (stepF w base s ac) := rfl
      rw [hfold] at hj
      by_cases hfire : le w ac.1 = true
      · have hs1' : (stepF w base s ac).1 = some (idxOf w s ac) := by
          rw [stepF_fst, if_pos hfire]
        have heq : idxOf w s ac = plus i0 (ddOf75 w ac) := idxOf_some112 hs1
        obtain ⟨hij, h2⟩ := ih (stepF w base s ac) (idxOf w s ac) hs1'
          (by rw [heq]; exact inT_plus hi0 hdd)
          (fun a ha => hall a (List.Mem.tail _ ha)) j hj
        refine ⟨hij, ?_⟩
        rw [heq] at h2
        rw [sumDD_cons112, ← plus_assoc_inT _ _ _ hi0 hdd hSt]
        exact h2
      · have hs1' : (stepF w base s ac).1 = some i0 := by
          rw [stepF_fst, if_neg hfire]; exact hs1
        obtain ⟨hij, h2⟩ := ih (stepF w base s ac) i0 hs1' hi0
          (fun a ha => hall a (List.Mem.tail _ ha)) j hj
        refine ⟨hij, ?_⟩
        rw [sumDD_cons112]
        exact le_trans_inT hij (inT_plus hi0 hSt) (inT_plus hi0 (inT_plus hdd hSt)) h2
          (plus_mono_right_inT i0 hi0 _ _ hSt (inT_plus hdd hSt) (le_self_plus75 hdd hSt))

/-- **指数がまだ無いときの畳み込みの上界。**  最初の発火で `⊖ 1` が入るぶんだけ
    総和より下がる。 -/
theorem fold_idx_le_none112 {w base : Term} (hw : inT w = true) :
    ∀ (ps : List (Term × Term)) (s : Option Term × Option Term),
      s.1 = none →
      (∀ ac ∈ ps, inT ac.1 = true ∧ inT ac.2 = true) →
      ∀ j, (ps.foldl (stepF w base) s).1 = some j →
        inT j = true ∧ le j (sumDD112 w ps) = true := by
  intro ps
  induction ps with
  | nil =>
      intro s hs1 _ j hj
      exfalso
      have hj2 : s.1 = some j := hj
      rw [hs1] at hj2
      exact Option.some_ne_none j hj2.symm
  | cons ac t ih =>
      intro s hs1 hall j hj
      have hac := hall ac (List.Mem.head _)
      have hdd : inT (ddOf75 w ac) = true := inT_ddOf75 hw hac.1 hac.2
      have hSt : inT (sumDD112 w t) = true :=
        inT_sumDD112 hw t (fun a ha => hall a (List.Mem.tail _ ha))
      have hfold : ((ac :: t).foldl (stepF w base) s)
          = t.foldl (stepF w base) (stepF w base s ac) := rfl
      rw [hfold] at hj
      by_cases hfire : le w ac.1 = true
      · have hs1' : (stepF w base s ac).1 = some (sub1 (ddOf75 w ac)) := by
          rw [stepF_fst, if_pos hfire, idxOf_none112 hs1]
        obtain ⟨hij, h2⟩ := fold_idx_le112 hw t (stepF w base s ac) (sub1 (ddOf75 w ac))
          hs1' (inT_sub1 hdd) (fun a ha => hall a (List.Mem.tail _ ha)) j hj
        refine ⟨hij, ?_⟩
        rw [sumDD_cons112]
        exact le_trans_inT hij (inT_plus (inT_sub1 hdd) hSt) (inT_plus hdd hSt) h2
          (plus_mono_left112 (inT_sub1 hdd) hdd hSt (le_sub1_112 hdd))
      · have hs1' : (stepF w base s ac).1 = none := by
          rw [stepF_fst, if_neg hfire]; exact hs1
        obtain ⟨hij, h2⟩ := ih (stepF w base s ac) hs1'
          (fun a ha => hall a (List.Mem.tail _ ha)) j hj
        refine ⟨hij, ?_⟩
        rw [sumDD_cons112]
        exact le_trans_inT hij hSt (inT_plus hdd hSt) h2 (le_self_plus75 hdd hSt)

/-- **§112 の主定理 — `LeIdxSelf95` は定理である。**  §95 が名指しした残る算術ひとつ。
    `dict` も `BT` も門も出てこないし、`PsiIdxOK` も要らない。 -/
theorem leIdxSelf112 : LeIdxSelf95 := by
  intro x hx hlx _ j hj
  obtain ⟨hcx, hdx⟩ := inT_toList x hx
  have hmx := ltM_toList x hx hlx
  obtain ⟨_, hall⟩ := wcnf_spec_sc (inT_reg 1) (isSC_reg_succ 0) (toList x) hcx hdx hmx
  have hj' : ((wcnf (reg 1) (toList x)).1.foldl (stepF (reg 1) (baseOf 0))
      ((none : Option Term), (none : Option Term))).1 = some j := hj
  obtain ⟨hij, h1⟩ := fold_idx_le_none112 (w := reg 1) (base := baseOf 0) (inT_reg 1)
    (wcnf (reg 1) (toList x)).1 ((none : Option Term), (none : Option Term)) rfl
    (fun ac hac => ⟨(hall ac hac).1, (hall ac hac).2.2.1⟩) j hj'
  have h2 := le_sumDD_wcnf112 (toList x) hcx hdx hmx
  rw [inT_ofList_toList x hx] at h2
  exact le_trans_inT hij
    (inT_sumDD112 (inT_reg 1) _ (fun ac hac => ⟨(hall ac hac).1, (hall ac hac).2.2.1⟩)) hx h1 h2

end

/-! ### §112.6 326 行目 — `LeIdxSelf95` を外す -/

section
open Evidence.Region
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-- **§112 の第一の帰結。** §110 の第一の結論から `LeIdxSelf95` が外れる。 -/
theorem psiIdxStep073_of_idxStd112 (HD : DictLtStd92) (HM : HiMono89) (H : IdxStd110) :
    PsiIdxStep073 :=
  psiIdxStep073_of_idxStd110 HD HM leIdxSelf112 H

/-- 係数版も同じ。 -/
theorem psiIdxStep073_of_coefLt112 (HD : DictLtStd92) (HM : HiMono89) (H : CoefLtStd110) :
    PsiIdxStep073 :=
  psiIdxStep073_of_coefLt110 HD HM leIdxSelf112 H

/-- **§112 の第二の帰結 — 326 行目は `LeIdxSelf95` を待たない。**
    `K` の側で残るのは §110 の条項ひとつと、§74/§89 が名指しした二つだけである。 -/
theorem certIn_t326_idx112 (HD : DictLtStd92) (HM : HiMono89) (H : IdxStd110)
    (HDe : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_idx110 HD HM leIdxSelf112 H HDe HI HC hacc

/-- 係数の比較に載せた形も同じ。 -/
theorem certIn_t326_coef112 (HD : DictLtStd92) (HM : HiMono89) (H : CoefLtStd110)
    (HDe : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_coef110 HD HM leIdxSelf112 H HDe HI HC hacc

/-- §95・§100・§105 の系列も同じように外れる。 -/
theorem certIn_t326_idx112' (HD : DictLtStd92) (HM : HiMono89) (H : IdxStd105)
    (HDe : LimDecS1) (HI : LimIncS1) (HC : LimCofS1)
    (hacc : Acc Evidence.WF.RT (vOf t326)) :
    Evidence.Cert.CertifiedIn Evidence.Cert.DomI (matB t326 0) (vOf t326) :=
  certIn_t326_idx105 HD HM leIdxSelf112 H HDe HI HC hacc

end

/-! ### §112.7 測定 (凍結) と、狭義版の反証 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 判定器は `PsiIdxOK` と同値 — §66.1 は必要条件しか言っていなかった。 -/
theorem psiIdxOK_of_psiIdxOKb112 {u : Nat} {x : Term} (h : psiIdxOKb u x = true) :
    PsiIdxOK u x := by
  intro p hp hle
  have h2 := (List.all_eq_true.mp h) p hp
  rw [hle, Bool.not_true, Bool.false_or] at h2
  exact h2

/-- 狭義版の証人 — `Ω₂ = Z1`、4 記号。 -/
def ltWit112 : Term := reg 2

/-- **§112 の第一の否定 — 狭義版は偽。**  `Ω₂` の畳み込みが吐く指数は `Ω₂` そのもの。
    `LeIdxSelf95` の `≤` は弱めたのではなく、これがちょうど真である。 -/
theorem not_ltIdxSelf112 :
    ¬ (∀ x : Term, inT x = true → lt x M = true → PsiIdxOK 0 x →
        ∀ j, idxF88 0 x = some j → lt j x = true) := by
  intro H
  have h := H ltWit112 (by rfl) (by rfl)
    (psiIdxOK_of_psiIdxOKb112 (show psiIdxOKb 0 ltWit112 = true from rfl))
    ltWit112 (show idxF88 0 ltWit112 = some ltWit112 from rfl)
  rw [lt_irrefl] at h
  exact Bool.noConfusion h

/-- 復元の証人 — `ω^(Ω₁·Ω₁)`。 -/
def recWit112 : Term := omegaNF (mulL (reg 1) (reg 1))

/-- **§112 の第二の否定 — `wcnf` の復元「等式」は偽。**  §100 と §105 が名指しした
    「`wcnf` の復元補題」がもし `Δ = p` の形だとすれば、それは成り立たない。
    §112.2 が要ったのは片側の不等式だけである。 -/
theorem lt_ddOf_recWit112 :
    lt (ddOf75 (reg 1) (wA (reg 1) recWit112, wC (reg 1) recWit112)) recWit112 = true := rfl

/-! **母集団 — 組み立てた。**  `Ω₁` の桁と `Ω₂` の桁を混ぜた 9 個の加法主要項から、
    2 項和・3 項和・4 段の深い項を作る。列挙ではない。 -/

def W1_112 : Term := reg 1
def W2_112 : Term := reg 2

def expo112 : List Term :=
  [ mulL W1_112 W1_112
  , plus (mulL W1_112 W1_112) W1_112
  , plus (mulL W1_112 W1_112) TM.Term.one
  , mulL W1_112 (plus W1_112 TM.Term.one)
  , plus (mulL W1_112 W2_112) W1_112
  , W2_112
  , plus W2_112 TM.Term.one
  , W1_112
  , TM.Term.one ]

def ap112 : List Term := expo112.map omegaNF

def deep112 : List Term :=
  [ plus (plus (omegaNF W2_112) (omegaNF (mulL W1_112 (plus W1_112 TM.Term.one))))
      (omegaNF (mulL W1_112 W1_112))
  , plus (plus (plus (omegaNF (plus W2_112 TM.Term.one)) (omegaNF W2_112))
      (omegaNF (mulL W1_112 (plus W1_112 TM.Term.one)))) (omegaNF (mulL W1_112 W1_112))
  , plus (plus (plus (omegaNF W2_112) (omegaNF (mulL W1_112 (plus W1_112 TM.Term.one))))
      (omegaNF (mulL W1_112 W1_112))) W1_112
  , plus (plus (plus (omegaNF W2_112) (omegaNF (mulL W1_112 (plus W1_112 TM.Term.one))))
      (omegaNF (mulL W1_112 W1_112))) (omegaNF TM.Term.one) ]

def pop112 : List Term :=
  (ap112.flatMap fun a => ap112.flatMap fun b => [plus a b]) ++ ap112
    ++ (ap112.flatMap fun a => [plus (plus a a) a]) ++ deep112

def comps112 : List Term := pop112.flatMap toList

def npair112 (x : Term) : Nat := (wcnf (reg 1) (toList x)).1.length
def nfire112 (x : Term) : Nat :=
  ((wcnf (reg 1) (toList x)).1.filter (fun ac => le (reg 1) ac.1)).length
def ncomp112 (x : Term) : Nat := (toList x).length
def legal112 (x : Term) : Bool := inT x && lt x M
def hasIdx112 (x : Term) : Bool := (idxF88 0 x).isSome
def okLe112 (x : Term) : Bool :=
  match idxF88 0 x with | none => true | some j => le j x
def okLt112 (x : Term) : Bool :=
  match idxF88 0 x with | none => true | some j => lt j x
/-- `wcnf` の併合枝が実際に働いた項か。 -/
def merged112 (x : Term) : Bool :=
  npair112 x < ((toList x).filter (fun p => !lt p (reg 1))).length
/-- 発火する対と発火しない対が混ざった項か。 -/
def mixed112 (x : Term) : Bool := (0 < nfire112 x) && (nfire112 x < npair112 x)
/-- 最初の発火で `⊖ 1` が実際に効いた項か。 -/
def sub1bit112 (x : Term) : Bool :=
  match (wcnf (reg 1) (toList x)).1.filter (fun ac => le (reg 1) ac.1) with
  | [] => false
  | ac :: _ => !(sub1 (ddOf75 (reg 1) ac) == ddOf75 (reg 1) ac)
/-- 一成分ぶんの `Δ`。 -/
def ddp112 (p : Term) : Term := ddOf75 (reg 1) (wA (reg 1) p, wC (reg 1) p)

/-! 母集団の大きさ、合法性、指数を持つ項の数。 -/
#guard (pop112.length, (pop112.filter legal112).length,
        (pop112.filter hasIdx112).length) == (103, 103, 95)

/-! **母集団は証明のどの枝にも盲でない。**  併合枝 21、対が 2 つ以上 29、
    発火と非発火が混ざる 8、`⊖ 1` が効く 7、対の数の最大 4、成分の数の最大 4。 -/
#guard ((pop112.filter merged112).length, (pop112.filter (fun x => 2 ≤ npair112 x)).length,
        (pop112.filter mixed112).length, (pop112.filter sub1bit112).length) == (21, 29, 8, 7)
#guard (pop112.foldl (fun m x => max m (npair112 x)) 0,
        pop112.foldl (fun m x => max m (ncomp112 x)) 0) == (4, 4)

/-! **定理の確認。** `le` は 103 項で 0 敗。母集団はすべて `psiIdxOKb` を通る
    (`PsiIdxOK` を仮説から外したので、通らない項でも定理は同じことを言う)。 -/
#guard (pop112.filter (fun x => !(okLe112 x))).length == 0
#guard (pop112.filter (fun x => !(psiIdxOKb 0 x))).length == 0

/-! **狭義版は 33 回破れる。**  最小は `Ω₂` (4 記号、`not_ltIdxSelf112`)。 -/
#guard (pop112.filter (fun x => hasIdx112 x && !(okLt112 x))).length == 33
#guard (pop112.filter (fun x => hasIdx112 x && !(okLt112 x))).all
        (fun x => 4 ≤ x.deg)

/-! **復元「等式」は成分の 79/178 で破れる。**  上からの押さえは一度も破れない。 -/
#guard (comps112.length, (comps112.filter (fun p => ddp112 p == p)).length,
        (comps112.filter (fun p => lt (ddp112 p) p)).length,
        (comps112.filter (fun p => !(le (ddp112 p) p))).length) == (178, 99, 79, 0)

end

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

end Evidence.Region
