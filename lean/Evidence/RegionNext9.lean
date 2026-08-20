import Evidence.RegionNext8

/-
Evidence/RegionNext9.lean — THE TABLE'S FIVE BROKEN ROWS AND THE TWO REPAIRS (§139-)

Split out of `RegionNext8` at 7450 lines.  Section numbers are not in file order — sections
were appended as their agents finished.
-/

namespace Evidence.Region

open BMS

/-! ## §139 THE FIVE BROKEN ROWS OF §137, AS THEOREMS

§137 put all 60 rows of `Rows.rows` through an external fundamental-sequence test — naruyoko's
`padicBotRathjen`, an INDEPENDENT implementation — and found five broken: rows 37, 47, 52, 53,
58.  That was EVIDENCE, not a proof.  This section turns all five into Lean theorems.

For a row with matrix `m` and published value `v` the claim proved here is

    there is an `s` with `inT s`, `lt s v`, and `lt (oR (m[n])) s` for EVERY `n`,

so `v` is strictly above the supremum of the values of its own expansion.  §69 proved exactly
this shape for `tdiag = (0,0)(1,1)(2,2)` — row 37's matrix — but left ONE named hypothesis,
`TowerVal`, the closed form of `vOf (fsB tdiag (j+3))`, measured to `j ≤ 9` and unproved.

  §139.1-3  THE FIVE INDICES AND THE LINK TO THE TABLE.  `i47139`, `i52139`, `i53139`,
            `i58139` and §69's `tdiag`; `matB` reads off exactly the five published matrices
            and `vOf` exactly the five published values.  `row37_is_tdiag139` and
            `rowval37_139 … rowval58_139` make the link to `Rows.rows` a THEOREM, not a
            remark.  `oR_expand139` connects `BMS.expand` to `fsB` from `topOKB` and `nfB`
            alone — no `stdB`, hence no `cmpS`.

  §139.4-7  **`TowerVal` IS A THEOREM.**  The route is §135.3's: `dict` is structural, so the
            chain is `collapse 1` iterated on a φ̄0-tower (`collapse1_phi0_139`,
            `dict_psiTow139`) and one `collapse 0` on top whose base-`Ω₁` digit has exponent
            `≥ Ω₁`, so the fold takes its strongly critical branch (`collapse0_tower139`,
            `collapse0_TW139`).  `towerVal139 : TowerVal`, hence `cofGap139 : CofGap`,
            `not_limCofS139 : ¬ LimCofS` and `not_hlimS139` — all with NO hypothesis.
            §69.5's measurement of `TowerVal` is superseded.

  §139.8    ROW 37.  `lt_fs_sbad139` and `row37_gap139`, with §69's own
            `sbad = ψ_{Ω₁}(φ̄(1,Ω₁))` — the term §137's external implementation named.

  §139.11-12 ROWS 58 AND 47.  Their fundamental sequences carry §69's ψ₁-tower INSIDE a fixed
            context (`fsB_i58139`, `fsB_i47139`), so the value is `ψ_Ω(F(ψ_Ω(TW n)))` for a
            fixed `F` and the witness is `F(sbad)`.  The `dict` work is `collapse 2` on a
            `ψ_{Ω₁}` term, `collapse 1` on `Ω₂ ⊕ ψ_{Ω₁}(·)` (whose Veblen branch produces
            `W139 = φ̄(1,Ω₁)`, the table's `ψ₁(Ω₂)`), and two `collapse 0` folds — one digit
            for row 58, two for row 47.

  §139.13-15 ROWS 52 AND 53.  Here the tower is not §69's: `TWG139 c j` is the same φ̄0-tower
            with base `φ̄(1,c) ⊕ φ̄(1,c)`, and `TowC138 c` is the four conditions on `c` that
            make it work.  Row 52 is `c = Ω₁`, row 53 is `c = Ω₁ ⊕ 1` (the coefficient 2 in
            the base-`Ω₂` CNF of `Ω₂ ⊕ Ω₂` is what shifts the Veblen branch).  The witnesses
            are `ψ_Ω(Ω₂ ⊕ φ̄(1, φ̄(1,Ω₁)))` and `ψ_Ω(Ω₂ ⊕ Ω₂ ⊕ φ̄(1, φ̄(1, Ω₁ ⊕ 1)))` —
            neither was nameable from §137's audit, and both are named here.

NONE OF THE FIVE SURVIVED.  Every one of them has a gap, proved.  If one of them had turned
out not to be refutable this is where it would have shown; it did not happen.

WHAT IS NOT CLAIMED.  Nothing here says which SIDE of the correspondence is wrong.  The
theorem is that the published value and the matrix's own expansion do not agree — which is
what §69 said about the diagonal and what §137 measured from outside about all five.  No
published value is changed by this section. -/

section
open Trans.Recal
open Trans.Dict (BT dict collapse reg wcnf logOm divAP subAP mulL sub1)
open TM TM.Term
open Evidence.WF

set_option maxRecDepth 40000

/-! ### §139.1 五つの添字

`nd v r a` は `r ⊕ ψ_v(a)`。行列は `matB` が読む。`topOKB` (最上位の節の段が全部 0) だけで
`expand_matB` が使えるので、`stdB` は要らない。 -/

/-- 段 2 の葉。行列では列が 1 本。 -/
def q139 : B := .nd 2 .nil .nil

/-- 行 47 の添字。 -/
def i47139 : B := .nd 0 .nil (.nd 1 .nil (.nd 0 q139 (.nd 1 .nil q139)))
/-- 行 52 の添字。 -/
def i52139 : B := .nd 0 .nil (.nd 1 .nil (.nd 2 q139 .nil))
/-- 行 53 の添字。 -/
def i53139 : B := .nd 0 .nil (.nd 1 .nil (.nd 2 (.nd 2 q139 .nil) .nil))
/-- 行 58 の添字。 -/
def i58139 : B := .nd 0 .nil (.nd 1 .nil (.nd 2 .nil tdiag))

theorem matB_i47139 : matB i47139 0 = [[0,0],[1,1],[2,2],[2,0],[3,1],[4,2]] := rfl
theorem matB_i52139 : matB i52139 0 = [[0,0],[1,1],[2,2],[2,2]] := rfl
theorem matB_i53139 : matB i53139 0 = [[0,0],[1,1],[2,2],[2,2],[2,2]] := rfl
theorem matB_i58139 : matB i58139 0 = [[0,0],[1,1],[2,2],[3,0],[4,1],[5,2]] := rfl

theorem topOKB_tdiag139 : topOKB tdiag = true := rfl
theorem topOKB_i47139 : topOKB i47139 = true := rfl
theorem topOKB_i52139 : topOKB i52139 = true := rfl
theorem topOKB_i53139 : topOKB i53139 = true := rfl
theorem topOKB_i58139 : topOKB i58139 = true := rfl

theorem nfB_tdiag139 : nfB tdiag = true := rfl
theorem nfB_i47139 : nfB i47139 = true := rfl
theorem nfB_i52139 : nfB i52139 = true := rfl
theorem nfB_i53139 : nfB i53139 = true := rfl
theorem nfB_i58139 : nfB i58139 = true := rfl

theorem kindB_i47139 : kindB i47139 = BMS.Kind.lim := rfl
theorem kindB_i52139 : kindB i52139 = BMS.Kind.lim := rfl
theorem kindB_i53139 : kindB i53139 = BMS.Kind.lim := rfl
theorem kindB_i58139 : kindB i58139 = BMS.Kind.lim := rfl

/-- 行 47 の値。 -/
theorem vOf_i47139 : vOf i47139
    = psi (Z zero) (add (Z TM.Term.one)
        (phi zero (add (phi TM.Term.one (Z zero)) (psi (Z zero) (Z TM.Term.one))))) := rfl
/-- 行 52 の値。 -/
theorem vOf_i52139 : vOf i52139
    = psi (Z zero) (add (Z TM.Term.one) (Z TM.Term.one)) := rfl
/-- 行 53 の値。 -/
theorem vOf_i53139 : vOf i53139
    = psi (Z zero) (add (Z TM.Term.one) (add (Z TM.Term.one) (Z TM.Term.one))) := rfl
/-- 行 58 の値。 -/
theorem vOf_i58139 : vOf i58139
    = psi (Z zero) (phi zero (add (Z TM.Term.one) (psi (Z zero) (Z TM.Term.one)))) := rfl

/-! ### §139.2 表との突き合わせ — 覚え書きではなく定理

`Rows.rows` の中の行そのものを指して、その行列が上の添字のもの、その値が `vOf` である
ことを言う。 -/

/-- **§69 の対角は表の 37 行目そのもの。** -/
theorem row37_is_tdiag139 :
    (Rows.rows.find? fun r => r.m == [[0,0],[1,1],[2,2]]).map (·.m) = some (matB tdiag 0) := rfl

theorem rowval37_139 :
    (Rows.rows.find? fun r => r.m == matB tdiag 0).map (·.t) = some (vOf tdiag) := rfl
theorem rowval47_139 :
    (Rows.rows.find? fun r => r.m == matB i47139 0).map (·.t) = some (vOf i47139) := rfl
theorem rowval52_139 :
    (Rows.rows.find? fun r => r.m == matB i52139 0).map (·.t) = some (vOf i52139) := rfl
theorem rowval53_139 :
    (Rows.rows.find? fun r => r.m == matB i53139 0).map (·.t) = some (vOf i53139) := rfl
theorem rowval58_139 :
    (Rows.rows.find? fun r => r.m == matB i58139 0).map (·.t) = some (vOf i58139) := rfl

/-! ### §139.3 展開と `oR` — `topOKB` と `nfB` だけで足りる -/

/-- **展開の値は基本列の値。** `stdB` は要らない (§13 の `expand_matB` と §19 の
    `nfB_fsB`)。 -/
theorem oR_expand139 (t : B) (htop : topOKB t = true) (hne : t ≠ .nil) (hnf : nfB t = true)
    (n : Nat) : Trans.Recal.oR (BMS.expand (matB t 0) n) = some (vOf (fsB t n)) := by
  rw [show BMS.expand (matB t 0) n = matB (fsB t n) 0 from by
    show (BMS.expand? (matB t 0) n).getD [] = _
    rw [expand_matB t htop hne n]
    rfl]
  exact oR_vOf (fsB t n) (nfB_fsB t n hnf)

/-! ### §139.4 塔の順序 — `TW` は `Ω₁` の上、`Ω₂` の下

`TW` は §69.4b のもの: `TW 0 = Ω₁ ⊕ Ω₁`、`TW (j+1) = φ̄(0, TW j)`。ここで要るのは
`Ω₁ < TW j < Ω₂` と次数だけ。どれも `ltF` の燃料を合わせた素朴な帰納法。 -/

theorem deg_TW139 : ∀ (m : Nat), (TW m).deg = 2 * m + 5
  | 0 => rfl
  | m + 1 => by
      show 1 + 1 + (TW m).deg = 2 * (m + 1) + 5
      rw [deg_TW139 m]
      omega

theorem beq_TW_zero139 : ∀ (m : Nat), ((TW m : Term) == zero) = false
  | 0 => rfl
  | _ + 1 => rfl

theorem beq_TW_Om139 : ∀ (m : Nat), ((TW m : Term) == Z zero) = false
  | 0 => rfl
  | _ + 1 => rfl

theorem beq_TWs_one139 : ∀ (m : Nat), ((phi zero (TW m) : Term) == TM.Term.one) = false
  | 0 => rfl
  | _ + 1 => rfl

theorem ltF_Om_TW139 : ∀ (m f : Nat), m + 1 ≤ f → ltF f (Z zero) (TW m) = true
  | 0, 0, h => absurd h (by omega)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (by omega)
  | m + 1, g + 1, h => by
      show ((Z zero : Term) == zero || (Z zero : Term) == TW m
            || ltF g (Z zero) zero || ltF g (Z zero) (TW m)) = true
      rw [ltF_Om_TW139 m g (by omega)]
      exact Bool.or_true _

theorem ltF_TW_Om139 : ∀ (m f : Nat), ltF f (TW m) (Z zero) = false
  | _, 0 => rfl
  | 0, g + 1 => by
      show ltF g (Z zero) (Z zero) = false
      exact ltF_irrefl g _
  | m + 1, g + 1 => by
      show (ltF g zero (Z zero) && ltF g (TW m) (Z zero)) = false
      rw [ltF_TW_Om139 m g]
      exact Bool.and_false _

theorem lt_Om_TW139 (m : Nat) : lt (Z zero) (TW m) = true := by
  rw [lt_eq_ltF (Z zero) (TW m) (3 * m + 8)
    (by rw [deg_TW139 m]; show 2 + (2 * m + 5) ≤ 3 * m + 8; omega)]
  exact ltF_Om_TW139 m (3 * m + 8) (by omega)

theorem lt_TW_Om138' (m : Nat) : lt (TW m) (Z zero) = false := ltF_TW_Om139 m _

theorem le_TW_reg1_139 (m : Nat) : le (TW m) (reg 1) = false := by
  show (((TW m : Term) == Z zero) || lt (TW m) (Z zero)) = false
  rw [beq_TW_Om139 m, lt_TW_Om138' m]
  rfl

theorem lt_TW_reg1_139 (m : Nat) : lt (TW m) (reg 1) = false := lt_TW_Om138' m

theorem le_reg1_TW_139 (m : Nat) : le (reg 1) (TW m) = true := by
  show (((Z zero : Term) == TW m) || lt (Z zero) (TW m)) = true
  rw [lt_Om_TW139 m]
  exact Bool.or_true _

theorem ltF_Om_Om2_139 : ∀ (f : Nat), 2 ≤ f → ltF f (Z zero) (Z TM.Term.one) = true := by
  intro f hf
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  show (if ltF g zero TM.Term.one = true then ltF g (starF g zero) (Z TM.Term.one)
        else (((Z zero : Term) == starF g TM.Term.one)
              || ltF g (Z zero) (starF g TM.Term.one))) = true
  rw [if_pos (ltF_left_zero (show 1 ≤ g by omega)
        (show (TM.Term.one : Term) ≠ zero from by intro hc; exact Term.noConfusion hc)),
    starF_zero135 g]
  exact ltF_left_zero (show 1 ≤ g by omega)
    (show (Z TM.Term.one : Term) ≠ zero from by intro hc; exact Term.noConfusion hc)

theorem ltF_TW_Om2_139 : ∀ (m f : Nat), m + 3 ≤ f → ltF f (TW m) (Z TM.Term.one) = true
  | 0, 0, h => absurd h (by omega)
  | 0, g + 1, h => by
      show ltF g (Z zero) (Z TM.Term.one) = true
      exact ltF_Om_Om2_139 g (by omega)
  | _ + 1, 0, h => absurd h (by omega)
  | m + 1, g + 1, h => by
      show (ltF g zero (Z TM.Term.one) && ltF g (TW m) (Z TM.Term.one)) = true
      rw [ltF_TW_Om2_139 m g (by omega),
        ltF_left_zero (show 1 ≤ g by omega)
          (show (Z TM.Term.one : Term) ≠ zero from by intro hc; exact Term.noConfusion hc)]
      rfl

theorem lt_TW_reg2_139 (m : Nat) : lt (TW m) (reg 2) = true := by
  rw [show (reg 2 : Term) = Z TM.Term.one from rfl,
    lt_eq_ltF (TW m) (Z TM.Term.one) (3 * m + 12)
      (by rw [deg_TW139 m]; show (2 * m + 5) + 4 ≤ 3 * m + 12; omega)]
  exact ltF_TW_Om2_139 m (3 * m + 12) (by omega)

/-! ### §139.5 `ψ₁` の側 — `collapse 1` は φ̄0 を 1 段積むだけ

§135.3 の `collapse1_y1_135` を引数について一般化したもの。`Ω₁ < φ̄(0,Y) < Ω₂` なら
`ψ₁` の畳み込みは何も起こらず、`ω^·` が 1 段乗る。 -/

theorem collapse1_phi0_139 {Y : Term}
    (hone : ((phi zero Y : Term) == TM.Term.one) = false)
    (hW2 : lt (phi zero Y) (reg 2) = true)
    (hleOm : le (phi zero Y) (reg 1) = false) :
    collapse 1 (phi zero Y) = phi zero (phi zero Y) := by
  show omegaNF (plus (reg 1) (plus
    (((wcnf (reg 2) (toList (phi zero Y))).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 2) (baseOf 1))).2.getD zero)
    ((wcnf (reg 2) (toList (phi zero Y))).2))) = _
  rw [show toList (phi zero Y) = [phi zero Y] from rfl, wcnf_cons_lt hW2]
  show omegaNF (plus (reg 1) (plus zero (ofList [phi zero Y]))) = _
  rw [show plus (reg 1) (plus zero (ofList [phi zero Y])) = phi zero Y from by
    show ofList (List.filter (fun a => le (phi zero Y) a) [Z zero] ++ [phi zero Y]) = _
    rw [show List.filter (fun a => le (phi zero Y) a) [Z zero] = [] from by
      show (match le (phi zero Y) (Z zero) with
            | true => Z zero :: List.filter (fun a => le (phi zero Y) a) []
            | false => List.filter (fun a => le (phi zero Y) a) []) = []
      rw [show le (phi zero Y) (Z zero) = false from hleOm]
      rfl]
    rfl]
  exact omegaNF_phi0_135 hone

/-- **`ψ₁` の塔の閉じた形。** `dict (ψ₁^{m+2} 0) = TW (m+1)`。**証明済み** — §69.5 では
    `m ≤ 7` の測定だった。 -/
theorem dict_psiTow139 : ∀ (m : Nat), dict (psiTow (m + 2)) = TW (m + 1)
  | 0 => rfl
  | m + 1 => by
      show collapse 1 (dict (psiTow (m + 2))) = TW (m + 2)
      rw [dict_psiTow139 m]
      show collapse 1 (phi zero (TW m)) = phi zero (phi zero (TW m))
      exact collapse1_phi0_139 (beq_TWs_one139 m) (lt_TW_reg2_139 (m + 1))
        (le_TW_reg1_139 (m + 1))

/-! ### §139.6 `ψ₀` の側 — 桁が一つ、強臨界の枝

引数が φ̄0 の三重塔なら、基底 `Ω₁` の桁は 1 つで、その指数は `Ω₁` 以上。だから畳み込みは
強臨界の枝を通り、値は `ψ_{Ω₁}` を頭に持つ。§135.3 の `collapse0_L1_135` と同じ形だが、
そちらは指数が `Ω₁` より下だったのでヴェブレン枝だった。 -/

theorem ltF_M_psi139 : ∀ (f : Nat) (k a : Term), ltF f M (psi k a) = false
  | 0, _, _ => rfl
  | _ + 1, _, _ => rfl

theorem lt_zero_psi139 (k a : Term) : lt zero (psi k a) = true :=
  ltF_left_zero (by show 1 ≤ 2 * ((zero : Term).deg + (psi k a).deg) + 8; omega)
    (by intro hc; exact Term.noConfusion hc)

theorem omegaNF_psi139 (k a : Term) : omegaNF (psi k a) = psi k a := by
  show (if lt M (psi k a) = true then omg (psi k a)
        else if ((psi k a : Term) == M) = true then M else phiNF zero (psi k a)) = _
  rw [if_neg (by rw [show lt M (psi k a) = false from ltF_M_psi139 _ k a]
                 exact Bool.noConfusion),
    if_neg (by intro hc; exact Bool.noConfusion hc)]
  show (if ((psi k a).isSC && lt zero (psi k a)) = true then psi k a
        else phiNFsucc zero (psi k a)) = _
  rw [if_pos (by show (true && lt zero (psi k a)) = true; rw [lt_zero_psi139 k a]; rfl)]

theorem lt_psi_one139 (k a : Term) : lt (psi k a) TM.Term.one = false := by
  rw [lt_eq_ltF (psi k a) TM.Term.one ((psi k a).deg + 3 + 1)
    (by show (psi k a).deg + 3 ≤ (psi k a).deg + 3 + 1; omega)]
  show (((psi k a : Term) == zero) || ((psi k a : Term) == zero)
        || ltF ((psi k a).deg + 3) (psi k a) zero
        || ltF ((psi k a).deg + 3) (psi k a) zero) = false
  rw [ltF_right_zero]
  rfl

theorem le_psi_one139 (k a : Term) : le (psi k a) TM.Term.one = false := by
  show lt (psi k a) TM.Term.one = false
  exact lt_psi_one139 k a

theorem plus_one_psi139 (k a : Term) : plus TM.Term.one (psi k a) = psi k a := by
  show ofList (List.filter (fun x => le (psi k a) x) [TM.Term.one] ++ [psi k a]) = _
  rw [show List.filter (fun x => le (psi k a) x) [TM.Term.one] = [] from by
    show (match le (psi k a) TM.Term.one with
          | true => TM.Term.one :: List.filter (fun x => le (psi k a) x) []
          | false => List.filter (fun x => le (psi k a) x) []) = []
    rw [le_psi_one139 k a]
    rfl]
  rfl

theorem wA_tower139 {X : Term}
    (hX1 : ((phi zero X : Term) == TM.Term.one) = false)
    (hX2 : ((phi zero (phi zero X) : Term) == TM.Term.one) = false)
    (hY1Om : lt (phi zero (phi zero X)) (reg 1) = false) :
    wA (reg 1) (phi zero (phi zero (phi zero X))) = phi zero (phi zero X) := by
  show ofList (List.map (divAP (reg 1)) (List.filter (fun q => !lt q (reg 1))
    (toList (logOm (phi zero (phi zero (phi zero X))))))) = _
  rw [logOm_phi0_135 (phiShifted_phi0_135 hX2),
    show toList (phi zero (phi zero X)) = [phi zero (phi zero X)] from rfl,
    show (List.filter (fun q => !lt q (reg 1)) [phi zero (phi zero X)])
      = [phi zero (phi zero X)] from by
      show (match (!lt (phi zero (phi zero X)) (reg 1)) with
            | true => phi zero (phi zero X) :: List.filter (fun q => !lt q (reg 1)) []
            | false => List.filter (fun q => !lt q (reg 1)) []) = _
      rw [hY1Om]
      rfl]
  show divAP (reg 1) (phi zero (phi zero X)) = _
  show omegaNF (subAP (reg 1) (logOm (phi zero (phi zero X)))) = _
  rw [logOm_phi0_135 (phiShifted_phi0_135 hX1)]
  show omegaNF (if ((phi zero X : Term) == reg 1) = true then ofList []
    else phi zero X) = _
  rw [if_neg (by intro hc; exact Bool.noConfusion hc)]
  exact omegaNF_phi0_135 hX1

theorem wC_tower139 {X : Term}
    (hX2 : ((phi zero (phi zero X) : Term) == TM.Term.one) = false)
    (hY1Om : lt (phi zero (phi zero X)) (reg 1) = false) :
    wC (reg 1) (phi zero (phi zero (phi zero X))) = TM.Term.one := by
  show omegaNF (ofList (List.filter (fun q => lt q (reg 1))
    (toList (logOm (phi zero (phi zero (phi zero X))))))) = _
  rw [logOm_phi0_135 (phiShifted_phi0_135 hX2),
    show toList (phi zero (phi zero X)) = [phi zero (phi zero X)] from rfl,
    show (List.filter (fun q => lt q (reg 1)) [phi zero (phi zero X)]) = [] from by
      show (match (lt (phi zero (phi zero X)) (reg 1)) with
            | true => phi zero (phi zero X) :: List.filter (fun q => lt q (reg 1)) []
            | false => List.filter (fun q => lt q (reg 1)) []) = _
      rw [hY1Om]
      rfl]
  exact omegaNF_zero135

theorem idx_tower139 {X : Term}
    (hX1 : ((phi zero X : Term) == TM.Term.one) = false)
    (hX2 : ((phi zero (phi zero X) : Term) == TM.Term.one) = false)
    (hX3 : ((phi zero (phi zero (phi zero X)) : Term) == TM.Term.one) = false)
    (hXOm : le (phi zero X) (reg 1) = false) :
    idxOf (reg 1) ((none : Option Term), (none : Option Term))
        (phi zero (phi zero X), TM.Term.one)
      = phi zero (phi zero (phi zero X)) := by
  show sub1 (mulL (mulL (reg 1) (subAP (reg 1) (phi zero (phi zero X)))) TM.Term.one) = _
  rw [show subAP (reg 1) (phi zero (phi zero X)) = phi zero (phi zero X) from by
    show (if ((phi zero (phi zero X) : Term) == reg 1) = true then ofList []
          else phi zero (phi zero X)) = _
    rw [if_neg (by intro hc; exact Bool.noConfusion hc)]]
  rw [show mulL (reg 1) (phi zero (phi zero X)) = phi zero (phi zero X) from by
    show ofList (List.map (fun p => omegaNF (plus (reg 1) (logOm p)))
      [phi zero (phi zero X)]) = _
    show omegaNF (plus (reg 1) (logOm (phi zero (phi zero X)))) = _
    rw [logOm_phi0_135 (phiShifted_phi0_135 hX1),
      show plus (reg 1) (phi zero X) = phi zero X from by
        show ofList (List.filter (fun a => le (phi zero X) a) [Z zero] ++ [phi zero X]) = _
        rw [show List.filter (fun a => le (phi zero X) a) [Z zero] = [] from by
          show (match le (phi zero X) (Z zero) with
                | true => Z zero :: List.filter (fun a => le (phi zero X) a) []
                | false => List.filter (fun a => le (phi zero X) a) []) = []
          rw [show le (phi zero X) (Z zero) = false from hXOm]
          rfl]
        rfl]
    exact omegaNF_phi0_135 hX1]
  rw [show mulL (phi zero (phi zero X)) TM.Term.one
        = phi zero (phi zero (phi zero X)) from by
    show ofList (List.map (fun p => omegaNF (plus (phi zero (phi zero X)) (logOm p)))
      [TM.Term.one]) = _
    show omegaNF (plus (phi zero (phi zero X)) (logOm TM.Term.one)) = _
    rw [show logOm TM.Term.one = zero from rfl,
      show plus (phi zero (phi zero X)) zero = phi zero (phi zero X) from rfl]
    exact omegaNF_phi0_135 hX2]
  show (if ((phi zero (phi zero (phi zero X)) : Term) == TM.Term.one) = true then ofList []
        else phi zero (phi zero (phi zero X))) = _
  rw [if_neg (by rw [hX3]; exact Bool.noConfusion)]

/-- **`ψ₀` の畳み込み — 三重の φ̄0 塔。** `Ω₁ ≤ 指数` なので強臨界の枝が動き、
    値は `ψ_{Ω₁}(その塔)`。 -/
theorem collapse0_tower139 {X : Term}
    (hX1 : ((phi zero X : Term) == TM.Term.one) = false)
    (hX2 : ((phi zero (phi zero X) : Term) == TM.Term.one) = false)
    (hX3 : ((phi zero (phi zero (phi zero X)) : Term) == TM.Term.one) = false)
    (hXOm : le (phi zero X) (reg 1) = false)
    (hY1Om : lt (phi zero (phi zero X)) (reg 1) = false)
    (hleW : le (reg 1) (phi zero (phi zero X)) = true)
    (hPW : lt (phi zero (phi zero (phi zero X))) (reg 1) = false) :
    collapse 0 (phi zero (phi zero (phi zero X)))
      = psi (Z zero) (phi zero (phi zero (phi zero X))) := by
  show omegaNF (plus (reg 0) (plus
    (((wcnf (reg 1) (toList (phi zero (phi zero (phi zero X))))).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero)
    ((wcnf (reg 1) (toList (phi zero (phi zero (phi zero X))))).2))) = _
  rw [show toList (phi zero (phi zero (phi zero X)))
        = [phi zero (phi zero (phi zero X))] from rfl, wcnf_cons_ge hPW]
  show omegaNF (plus (reg 0) (plus
    (([(wA (reg 1) (phi zero (phi zero (phi zero X))),
        wC (reg 1) (phi zero (phi zero (phi zero X))))].foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero) zero)) = _
  rw [wA_tower139 hX1 hX2 hY1Om, wC_tower139 hX2 hY1Om]
  show omegaNF (plus (reg 0) (plus
    ((stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (phi zero (phi zero X), TM.Term.one)).2.getD zero) zero)) = _
  rw [show stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (phi zero (phi zero X), TM.Term.one)
      = ((some (phi zero (phi zero (phi zero X))) : Option Term),
         some (psi (reg 1) (phi zero (phi zero (phi zero X))))) from by
    show (if le (reg 1) (phi zero (phi zero X)) = true
      then (some (idxOf (reg 1) ((none : Option Term), (none : Option Term))
              (phi zero (phi zero X), TM.Term.one)),
            some (psi (reg 1) (idxOf (reg 1) ((none : Option Term), (none : Option Term))
              (phi zero (phi zero X), TM.Term.one))))
      else ((none : Option Term),
            some (phiNF (phi zero (phi zero X)) (plus (baseOf 0) (sub1 TM.Term.one))))) = _
    rw [if_pos hleW, idx_tower139 hX1 hX2 hX3 hXOm]]
  show omegaNF (plus (reg 0) (plus
    (psi (Z zero) (phi zero (phi zero (phi zero X)))) zero)) = _
  rw [show plus (reg 0) (plus (psi (Z zero) (phi zero (phi zero (phi zero X)))) zero)
        = psi (Z zero) (phi zero (phi zero (phi zero X))) from rfl]
  exact omegaNF_psi139 _ _

/-- **塔の頭。** `collapse 0 (TW (j+3)) = ψ_{Ω₁}(TW (j+3))`。 -/
theorem collapse0_TW139 (j : Nat) :
    collapse 0 (TW (j + 3)) = psi (Z zero) (TW (j + 3)) :=
  collapse0_tower139 (X := TW j) (beq_TWs_one139 j) (beq_TWs_one139 (j + 1))
    (beq_TWs_one139 (j + 2)) (le_TW_reg1_139 (j + 1)) (lt_TW_reg1_139 (j + 2))
    (le_reg1_TW_139 (j + 2)) (lt_TW_reg1_139 (j + 3))

/-! ### §139.7 `TowerVal` は定理

§69.4b が残した唯一の仮説がこれで消える。 -/

theorem vOf_nd139 (v : Nat) (r a : B) :
    vOf (.nd v r a) = plus TM.Term.one (dict (bVal (.nd v r a))) := rfl

/-- **§69 の `TowerVal`、証明済み。** -/
theorem towerVal139 : TowerVal := by
  intro j
  have h1 : vOf (fsB tdiag (j + 3))
      = plus TM.Term.one (dict (bVal (fsB tdiag (j + 3)))) := by
    rw [fsB_tdiag (j + 3)]
    exact vOf_nd139 _ _ _
  rw [h1, bVal_fsB_tdiag (j + 3)]
  show plus TM.Term.one (collapse 0 (dict (psiTow (j + 2 + 2)))) = psi (Z zero) (TW (j + 3))
  rw [dict_psiTow139 (j + 2)]
  show plus TM.Term.one (collapse 0 (TW (j + 3))) = psi (Z zero) (TW (j + 3))
  rw [collapse0_TW139 j]
  exact plus_one_psi139 (Z zero) (TW (j + 3))

/-- **§69 の `CofGap`、仮説なし。** -/
theorem cofGap139 : CofGap := cofGap_of towerVal139

/-- **§69 の主定理、仮説なし。** 共終性の条項は領域の上で偽。 -/
theorem not_limCofS139 : ¬ LimCofS := not_limCofS cofGap139

/-! ### §139.8 行 37 — 隙間そのもの -/

/-- **基本列の値はどれも `sbad` より真に下。** `n ≤ 2` は計算、`n ≥ 3` は塔の閉じた形。 -/
theorem lt_fs_sbad139 : ∀ (n : Nat), lt (vOf (fsB tdiag n)) sbad = true
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | j + 3 => by
      rw [towerVal139 j, sbad_eq, lt_psi_same]
      exact lt_TW (j + 3)

/-- **行 37 の主定理。** 表の値 `ψ_Ω(Ω₂)` は自分の展開の値の上限より真に上にある。
    証人は §69 の `sbad = ψ_{Ω₁}(φ̄(1,Ω₁))` — §137 で外部が名指した項そのもの。
    **仮説なし。** -/
theorem row37_gap139 :
    (Rows.rows.find? fun r => r.m == matB tdiag 0).map (·.t) = some (vOf tdiag)
  ∧ inT sbad = true
  ∧ lt sbad (vOf tdiag) = true
  ∧ ∀ n, Trans.Recal.oR (BMS.expand (matB tdiag 0) n) = some (vOf (fsB tdiag n))
       ∧ lt (vOf (fsB tdiag n)) sbad = true :=
  ⟨rowval37_139, inT_sbad, lt_sbad_tdiag, fun n =>
    ⟨oR_expand139 tdiag topOKB_tdiag139 (by intro hc; exact B.noConfusion hc) nfB_tdiag139 n,
     lt_fs_sbad139 n⟩⟩

/-! ### §139.9 一般の順序の道具 — `φ̄` と `⊕` の「同じ頭」の比較 -/

/-- **2.3.13(ii)。** 第 1 引数が同じ `φ̄` の比較は引数の比較。 -/
theorem lt_phi_same139 (c a b : Term) : lt (phi c a) (phi c b) = lt a b := by
  by_cases h : a = b
  · subst h; rw [lt_irrefl, lt_irrefl]
  · have hne : ((phi c a : Term) == phi c b) = false := by
      cases hq : ((phi c a : Term) == phi c b) with
      | false => rfl
      | true =>
        exfalso
        have he : (phi c a : Term) = phi c b := of_decide_eq_true hq
        injection he with _ h2
        exact h h2
    have hd : (phi c a).deg + (phi c b).deg = (c.deg + c.deg + a.deg + b.deg + 1) + 1 := by
      show (1 + c.deg + a.deg) + (1 + c.deg + b.deg) = _
      omega
    rw [lt_eq_ltF (phi c a) (phi c b) ((phi c a).deg + (phi c b).deg) (Nat.le_refl _), hd]
    show (if ((phi c a : Term) == phi c b) = true then false
          else if ((c : Term) == c) = true then
            ltF (c.deg + c.deg + a.deg + b.deg + 1) a b
          else if ltF (c.deg + c.deg + a.deg + b.deg + 1) c c = true then
            ltF (c.deg + c.deg + a.deg + b.deg + 1) a (phi c b)
          else (((phi c a : Term) == b)
                || ltF (c.deg + c.deg + a.deg + b.deg + 1) (phi c a) b)) = _
    rw [hne, if_neg (fun hc => Bool.noConfusion hc),
      if_pos (show ((c : Term) == c) = true from beq_self_eq_true c)]
    exact (lt_eq_ltF a b (c.deg + c.deg + a.deg + b.deg + 1) (by omega)).symm

/-- **2.3.16。** 先頭成分が同じ和の比較は残りの比較。 -/
theorem lt_add_same139 (p a b : Term) : lt (add p a) (add p b) = lt a b := by
  by_cases h : a = b
  · subst h; rw [lt_irrefl, lt_irrefl]
  · have hne : ((add p a : Term) == add p b) = false := by
      cases hq : ((add p a : Term) == add p b) with
      | false => rfl
      | true =>
        exfalso
        have he : (add p a : Term) = add p b := of_decide_eq_true hq
        injection he with _ h2
        exact h h2
    have hd : (add p a).deg + (add p b).deg = (p.deg + p.deg + a.deg + b.deg + 1) + 1 := by
      show (1 + p.deg + a.deg) + (1 + p.deg + b.deg) = _
      omega
    rw [lt_eq_ltF (add p a) (add p b) ((add p a).deg + (add p b).deg) (Nat.le_refl _), hd]
    show (if ((add p a : Term) == add p b) = true then false
          else if ((p : Term) == p) = true then
            ltF (p.deg + p.deg + a.deg + b.deg + 1) a b
          else ltF (p.deg + p.deg + a.deg + b.deg + 1) p p) = _
    rw [hne, if_neg (fun hc => Bool.noConfusion hc),
      if_pos (show ((p : Term) == p) = true from beq_self_eq_true p)]
    exact (lt_eq_ltF a b (p.deg + p.deg + a.deg + b.deg + 1) (by omega)).symm

/-! ### §139.10 `Ω₁`・`Ω₂`・`Ω₃` と `ψ_{Ω₁}` の位置 -/

theorem ltF_Om_Z139 {c : Term} (hbeq : ((Z zero : Term) == Z c) = false) (hc : c ≠ zero) :
    ∀ (f : Nat), 2 ≤ f → ltF f (Z zero) (Z c) = true := by
  intro f hf
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  show (if ((Z zero : Term) == Z c) = true then false
        else if ltF g zero c = true then ltF g (starF g zero) (Z c)
        else (((Z zero : Term) == starF g c) || ltF g (Z zero) (starF g c))) = true
  rw [hbeq, if_neg (fun hcc => Bool.noConfusion hcc),
    if_pos (ltF_left_zero (show 1 ≤ g by omega) hc), starF_zero135 g]
  exact ltF_left_zero (show 1 ≤ g by omega)
    (show (Z c : Term) ≠ zero from by intro hcc; exact Term.noConfusion hcc)

theorem lt_Om_Om2_139 : lt (Z zero) (Z TM.Term.one) = true := by
  rw [lt_eq_ltF (Z zero) (Z TM.Term.one) 8 (by show 2 + 4 ≤ 8; omega)]
  exact ltF_Om_Z139 rfl (by intro hc; exact Term.noConfusion hc) 8 (by omega)

theorem ltF_Om2_Om139 : ∀ (f : Nat), ltF f (Z TM.Term.one) (Z zero) = false
  | 0 => rfl
  | g + 1 => by
      show (if ltF g TM.Term.one zero = true then ltF g (starF g TM.Term.one) (Z zero)
            else (((Z TM.Term.one : Term) == starF g zero)
                  || ltF g (Z TM.Term.one) (starF g zero))) = false
      rw [if_neg (by rw [ltF_right_zero]; exact Bool.noConfusion), starF_zero135 g,
        ltF_right_zero]
      rfl

theorem lt_Om2_reg1_139 : lt (Z TM.Term.one) (reg 1) = false := ltF_Om2_Om139 _

theorem le_Om2_reg1_139 : le (Z TM.Term.one) (reg 1) = false := by
  show lt (Z TM.Term.one) (Z zero) = false
  exact ltF_Om2_Om139 _

theorem le_reg1_Om2_139 : le (reg 1) (Z TM.Term.one) = true := by
  show lt (Z zero) (Z TM.Term.one) = true
  exact lt_Om_Om2_139

theorem lt_psiOm_reg1_139 (A : Term) : lt (psi (Z zero) A) (reg 1) = true := by
  rw [show (reg 1 : Term) = Z zero from rfl,
    lt_eq_ltF (psi (Z zero) A) (Z zero) ((psi (Z zero) A).deg + 2 + 1)
    (by show (psi (Z zero) A).deg + 2 ≤ (psi (Z zero) A).deg + 2 + 1; omega)]
  rfl

theorem lt_psiOm_Om2_139 (A : Term) : lt (psi (Z zero) A) (Z TM.Term.one) = true := by
  rw [lt_eq_ltF (psi (Z zero) A) (Z TM.Term.one) ((psi (Z zero) A).deg + 4 + 1)
    (by show (psi (Z zero) A).deg + 4 ≤ (psi (Z zero) A).deg + 4 + 1; omega)]
  show (if (((Z zero : Term) == Z TM.Term.one)
        || ltF ((psi (Z zero) A).deg + 4) (Z zero) (Z TM.Term.one)) = true then true
        else (((psi (Z zero) A : Term) == starF ((psi (Z zero) A).deg + 4) TM.Term.one)
              || ltF ((psi (Z zero) A).deg + 4) (psi (Z zero) A)
                   (starF ((psi (Z zero) A).deg + 4) TM.Term.one))) = true
  rw [ltF_Om_Z139 rfl (by intro hc; exact Term.noConfusion hc)
    ((psi (Z zero) A).deg + 4) (by omega)]
  rfl

theorem le_psiOm_Om2_139 (A : Term) : le (psi (Z zero) A) (Z TM.Term.one) = true := by
  show lt (psi (Z zero) A) (Z TM.Term.one) = true
  exact lt_psiOm_Om2_139 A

theorem lt_psiOm_reg3_139 (A : Term) : lt (psi (Z zero) A) (reg 3) = true := by
  rw [show (reg 3 : Term) = Z (add TM.Term.one TM.Term.one) from rfl,
    lt_eq_ltF (psi (Z zero) A) (Z (add TM.Term.one TM.Term.one))
      ((psi (Z zero) A).deg + 8 + 1)
      (by show (psi (Z zero) A).deg + 8 ≤ (psi (Z zero) A).deg + 8 + 1; omega)]
  show (if (((Z zero : Term) == Z (add TM.Term.one TM.Term.one))
        || ltF ((psi (Z zero) A).deg + 8) (Z zero) (Z (add TM.Term.one TM.Term.one)))
        = true then true
        else (((psi (Z zero) A : Term)
                == starF ((psi (Z zero) A).deg + 8) (add TM.Term.one TM.Term.one))
              || ltF ((psi (Z zero) A).deg + 8) (psi (Z zero) A)
                   (starF ((psi (Z zero) A).deg + 8) (add TM.Term.one TM.Term.one)))) = true
  rw [ltF_Om_Z139 rfl (by intro hc; exact Term.noConfusion hc)
    ((psi (Z zero) A).deg + 8) (by omega)]
  rfl

theorem omegaNF_Z139 (a : Term) : omegaNF (Z a) = Z a := by
  show (if lt M (Z a) = true then omg (Z a)
        else if ((Z a : Term) == M) = true then M else phiNF zero (Z a)) = _
  rw [if_neg (by rw [show lt M (Z a) = false from ltF_M_Z135 a _]; exact Bool.noConfusion),
    if_neg (by intro hc; exact Bool.noConfusion hc)]
  show (if ((Z a).isSC && lt zero (Z a)) = true then Z a else phiNFsucc zero (Z a)) = _
  rw [if_pos (by
    show (true && lt zero (Z a)) = true
    rw [show lt zero (Z a) = true from ltF_left_zero
      (by show 1 ≤ 2 * ((zero : Term).deg + (Z a).deg) + 8; omega)
      (by intro hc; exact Term.noConfusion hc)]
    rfl)]

/-! ### §139.11 行 58 — 基本列は §69 の塔をそのまま内側に持つ -/

theorem fsB_i58139 (n : Nat) :
    fsB i58139 n = .nd 0 .nil (.nd 1 .nil (.nd 2 .nil (fsB tdiag n))) := rfl

theorem fs_tdiag_shape139 (n : Nat) : ∃ x, fsB tdiag n = .nd 0 .nil (.nd 1 .nil x) := by
  obtain ⟨x, hx⟩ := bTow_shape n
  exact ⟨x, by rw [fsB_tdiag n, hx]⟩

theorem bArg2_fs_tdiag139 (n : Nat) : bArg 2 (fsB tdiag n) = BT.D 0 (psiTow (n + 1)) := by
  rw [fsB_tdiag n]
  obtain ⟨x, hx⟩ := bTow_shape n
  have h : bArg 2 (B.nd 0 .nil (bTow n)) = BT.D 0 (bArg 0 (bTow n)) := by
    rw [hx]; rfl
  rw [h, bArg0_bTow n]

theorem bVal_fs_i58139 (n : Nat) :
    bVal (fsB i58139 n) = BT.D 0 (BT.D 2 (BT.D 0 (psiTow (n + 1)))) := by
  obtain ⟨x, hx⟩ := fs_tdiag_shape139 n
  rw [fsB_i58139 n]
  have h : bVal (B.nd 0 .nil (.nd 1 .nil (.nd 2 .nil (fsB tdiag n))))
      = BT.D 0 (BT.D 2 (bArg 2 (fsB tdiag n))) := by
    rw [hx]; rfl
  rw [h, bArg2_fs_tdiag139 n]

/-! `ψ₂` の畳み込み — 引数が `Ω₂` より下なら `Ω₂ ⊕ ·` を `ω^·` で包むだけ。 -/

theorem ltF_M_addOm2_139 (A : Term) : ∀ (f : Nat),
    ltF f M (add (Z TM.Term.one) (psi (Z zero) A)) = false
  | 0 => rfl
  | g + 1 => by
      show (((M : Term) == Z TM.Term.one) || ltF g M (Z TM.Term.one)) = false
      rw [ltF_M_Z135 TM.Term.one g]
      rfl

theorem omegaNF_addOm2psi139 (A : Term) :
    omegaNF (add (Z TM.Term.one) (psi (Z zero) A))
      = phi zero (add (Z TM.Term.one) (psi (Z zero) A)) := by
  show (if lt M (add (Z TM.Term.one) (psi (Z zero) A)) = true
          then omg (add (Z TM.Term.one) (psi (Z zero) A))
        else if ((add (Z TM.Term.one) (psi (Z zero) A) : Term) == M) = true then M
        else phiNF zero (add (Z TM.Term.one) (psi (Z zero) A))) = _
  rw [if_neg (by
      rw [show lt M (add (Z TM.Term.one) (psi (Z zero) A)) = false from
        ltF_M_addOm2_139 A _]
      exact Bool.noConfusion),
    if_neg (by intro hc; exact Bool.noConfusion hc)]
  show phiNFsucc zero (add (Z TM.Term.one) (psi (Z zero) A)) = _
  unfold phiNFsucc
  rw [show splitFin (add (Z TM.Term.one) (psi (Z zero) A))
        = (add (Z TM.Term.one) (psi (Z zero) A), 0) from rfl]
  rfl

theorem collapse2_psi139 (A : Term) :
    collapse 2 (psi (Z zero) A) = phi zero (add (Z TM.Term.one) (psi (Z zero) A)) := by
  show omegaNF (plus (reg 2) (plus
    (((wcnf (reg 3) (toList (psi (Z zero) A))).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 3) (baseOf 2))).2.getD zero)
    ((wcnf (reg 3) (toList (psi (Z zero) A))).2))) = _
  rw [show toList (psi (Z zero) A) = [psi (Z zero) A] from rfl,
    wcnf_cons_lt (lt_psiOm_reg3_139 A)]
  show omegaNF (plus (reg 2) (plus zero (ofList [psi (Z zero) A]))) = _
  rw [show plus (reg 2) (plus zero (ofList [psi (Z zero) A]))
        = add (Z TM.Term.one) (psi (Z zero) A) from by
    show ofList (List.filter (fun a => le (psi (Z zero) A) a) [Z TM.Term.one]
      ++ [psi (Z zero) A]) = _
    rw [show List.filter (fun a => le (psi (Z zero) A) a) [Z TM.Term.one]
          = [Z TM.Term.one] from by
      show (match le (psi (Z zero) A) (Z TM.Term.one) with
            | true => Z TM.Term.one
                :: List.filter (fun a => le (psi (Z zero) A) a) []
            | false => List.filter (fun a => le (psi (Z zero) A) a) []) = _
      rw [le_psiOm_Om2_139 A]
      rfl]
    rfl]
  exact omegaNF_addOm2psi139 A

/-! `ψ₀` の畳み込み — 桁が一つ、指数 `Ω₂`、係数が `ψ_{Ω₁}` の項。 -/

theorem ltF_addOm2_Om139 (A : Term) : ∀ (f : Nat),
    ltF f (add (Z TM.Term.one) (psi (Z zero) A)) (Z zero) = false
  | 0 => rfl
  | g + 1 => by
      show ltF g (Z TM.Term.one) (Z zero) = false
      exact ltF_Om2_Om139 g

theorem ltF_Q_Om139 (A : Term) : ∀ (f : Nat),
    ltF f (phi zero (add (Z TM.Term.one) (psi (Z zero) A))) (Z zero) = false
  | 0 => rfl
  | g + 1 => by
      show (ltF g zero (Z zero)
            && ltF g (add (Z TM.Term.one) (psi (Z zero) A)) (Z zero)) = false
      rw [ltF_addOm2_Om139 A g]
      exact Bool.and_false _

theorem lt_Q_reg1_139 (A : Term) :
    lt (phi zero (add (Z TM.Term.one) (psi (Z zero) A))) (reg 1) = false :=
  ltF_Q_Om139 A _

theorem beq_Q_one139 (A : Term) :
    ((phi zero (add (Z TM.Term.one) (psi (Z zero) A)) : Term) == TM.Term.one) = false := rfl

theorem wA_Q139 (A : Term) :
    wA (reg 1) (phi zero (add (Z TM.Term.one) (psi (Z zero) A))) = Z TM.Term.one := by
  show ofList (List.map (divAP (reg 1)) (List.filter (fun q => !lt q (reg 1))
    (toList (logOm (phi zero (add (Z TM.Term.one) (psi (Z zero) A))))))) = _
  rw [logOm_phi0_135 (show phiShifted zero (add (Z TM.Term.one) (psi (Z zero) A)) = false
        from rfl),
    show toList (add (Z TM.Term.one) (psi (Z zero) A))
      = [Z TM.Term.one, psi (Z zero) A] from rfl,
    show (List.filter (fun q => !lt q (reg 1)) [Z TM.Term.one, psi (Z zero) A])
      = [Z TM.Term.one] from by
      show (match (!lt (Z TM.Term.one) (reg 1)) with
            | true => Z TM.Term.one
                :: List.filter (fun q => !lt q (reg 1)) [psi (Z zero) A]
            | false => List.filter (fun q => !lt q (reg 1)) [psi (Z zero) A]) = _
      rw [lt_Om2_reg1_139]
      show (Z TM.Term.one : Term) :: (match (!lt (psi (Z zero) A) (reg 1)) with
            | true => psi (Z zero) A :: List.filter (fun q => !lt q (reg 1)) []
            | false => List.filter (fun q => !lt q (reg 1)) []) = _
      rw [lt_psiOm_reg1_139 A]
      rfl]
  show divAP (reg 1) (Z TM.Term.one) = _
  show omegaNF (subAP (reg 1) (logOm (Z TM.Term.one))) = _
  rw [show logOm (Z TM.Term.one) = Z TM.Term.one from rfl]
  show omegaNF (if ((Z TM.Term.one : Term) == reg 1) = true then ofList []
    else Z TM.Term.one) = _
  rw [if_neg (by intro hc; exact Bool.noConfusion hc)]
  exact omegaNF_Z139 TM.Term.one

theorem wC_Q139 (A : Term) :
    wC (reg 1) (phi zero (add (Z TM.Term.one) (psi (Z zero) A))) = psi (Z zero) A := by
  show omegaNF (ofList (List.filter (fun q => lt q (reg 1))
    (toList (logOm (phi zero (add (Z TM.Term.one) (psi (Z zero) A))))))) = _
  rw [logOm_phi0_135 (show phiShifted zero (add (Z TM.Term.one) (psi (Z zero) A)) = false
        from rfl),
    show toList (add (Z TM.Term.one) (psi (Z zero) A))
      = [Z TM.Term.one, psi (Z zero) A] from rfl,
    show (List.filter (fun q => lt q (reg 1)) [Z TM.Term.one, psi (Z zero) A])
      = [psi (Z zero) A] from by
      show (match (lt (Z TM.Term.one) (reg 1)) with
            | true => Z TM.Term.one
                :: List.filter (fun q => lt q (reg 1)) [psi (Z zero) A]
            | false => List.filter (fun q => lt q (reg 1)) [psi (Z zero) A]) = _
      rw [lt_Om2_reg1_139]
      show (match (lt (psi (Z zero) A) (reg 1)) with
            | true => psi (Z zero) A :: List.filter (fun q => lt q (reg 1)) []
            | false => List.filter (fun q => lt q (reg 1)) []) = _
      rw [lt_psiOm_reg1_139 A]
      rfl]
  exact omegaNF_psi139 (Z zero) A

theorem idx_Q139 (A : Term) :
    idxOf (reg 1) ((none : Option Term), (none : Option Term))
        (Z TM.Term.one, psi (Z zero) A)
      = phi zero (add (Z TM.Term.one) (psi (Z zero) A)) := by
  show sub1 (mulL (mulL (reg 1) (subAP (reg 1) (Z TM.Term.one))) (psi (Z zero) A)) = _
  rw [show subAP (reg 1) (Z TM.Term.one) = Z TM.Term.one from by
    show (if ((Z TM.Term.one : Term) == reg 1) = true then ofList []
          else Z TM.Term.one) = _
    rw [if_neg (by intro hc; exact Bool.noConfusion hc)]]
  rw [show mulL (reg 1) (Z TM.Term.one) = Z TM.Term.one from by
    show ofList (List.map (fun p => omegaNF (plus (reg 1) (logOm p))) [Z TM.Term.one]) = _
    show omegaNF (plus (reg 1) (logOm (Z TM.Term.one))) = _
    rw [show logOm (Z TM.Term.one) = Z TM.Term.one from rfl,
      show plus (reg 1) (Z TM.Term.one) = Z TM.Term.one from by
        show ofList (List.filter (fun a => le (Z TM.Term.one) a) [Z zero]
          ++ [Z TM.Term.one]) = _
        rw [show List.filter (fun a => le (Z TM.Term.one) a) [Z zero] = [] from by
          show (match le (Z TM.Term.one) (Z zero) with
                | true => Z zero :: List.filter (fun a => le (Z TM.Term.one) a) []
                | false => List.filter (fun a => le (Z TM.Term.one) a) []) = []
          rw [show le (Z TM.Term.one) (Z zero) = false from le_Om2_reg1_139]
          rfl]
        rfl]
    exact omegaNF_Z139 TM.Term.one]
  rw [show mulL (Z TM.Term.one) (psi (Z zero) A)
        = phi zero (add (Z TM.Term.one) (psi (Z zero) A)) from by
    show ofList (List.map (fun p => omegaNF (plus (Z TM.Term.one) (logOm p)))
      [psi (Z zero) A]) = _
    show omegaNF (plus (Z TM.Term.one) (logOm (psi (Z zero) A))) = _
    rw [show logOm (psi (Z zero) A) = psi (Z zero) A from rfl,
      show plus (Z TM.Term.one) (psi (Z zero) A)
          = add (Z TM.Term.one) (psi (Z zero) A) from by
        show ofList (List.filter (fun a => le (psi (Z zero) A) a) [Z TM.Term.one]
          ++ [psi (Z zero) A]) = _
        rw [show List.filter (fun a => le (psi (Z zero) A) a) [Z TM.Term.one]
              = [Z TM.Term.one] from by
          show (match le (psi (Z zero) A) (Z TM.Term.one) with
                | true => Z TM.Term.one
                    :: List.filter (fun a => le (psi (Z zero) A) a) []
                | false => List.filter (fun a => le (psi (Z zero) A) a) []) = _
          rw [le_psiOm_Om2_139 A]
          rfl]
        rfl]
    exact omegaNF_addOm2psi139 A]
  show (if ((phi zero (add (Z TM.Term.one) (psi (Z zero) A)) : Term) == TM.Term.one) = true
        then ofList [] else phi zero (add (Z TM.Term.one) (psi (Z zero) A))) = _
  rw [if_neg (by rw [beq_Q_one139 A]; exact Bool.noConfusion)]

theorem collapse0_Q139 (A : Term) :
    collapse 0 (phi zero (add (Z TM.Term.one) (psi (Z zero) A)))
      = psi (Z zero) (phi zero (add (Z TM.Term.one) (psi (Z zero) A))) := by
  show omegaNF (plus (reg 0) (plus
    (((wcnf (reg 1) (toList (phi zero (add (Z TM.Term.one) (psi (Z zero) A))))).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero)
    ((wcnf (reg 1) (toList (phi zero (add (Z TM.Term.one) (psi (Z zero) A))))).2))) = _
  rw [show toList (phi zero (add (Z TM.Term.one) (psi (Z zero) A)))
        = [phi zero (add (Z TM.Term.one) (psi (Z zero) A))] from rfl,
    wcnf_cons_ge (lt_Q_reg1_139 A)]
  show omegaNF (plus (reg 0) (plus
    (([(wA (reg 1) (phi zero (add (Z TM.Term.one) (psi (Z zero) A))),
        wC (reg 1) (phi zero (add (Z TM.Term.one) (psi (Z zero) A))))].foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 1) (baseOf 0))).2.getD zero) zero)) = _
  rw [wA_Q139 A, wC_Q139 A]
  show omegaNF (plus (reg 0) (plus
    ((stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (Z TM.Term.one, psi (Z zero) A)).2.getD zero) zero)) = _
  rw [show stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term))
        (Z TM.Term.one, psi (Z zero) A)
      = ((some (phi zero (add (Z TM.Term.one) (psi (Z zero) A))) : Option Term),
         some (psi (reg 1) (phi zero (add (Z TM.Term.one) (psi (Z zero) A))))) from by
    show (if le (reg 1) (Z TM.Term.one) = true
      then (some (idxOf (reg 1) ((none : Option Term), (none : Option Term))
              (Z TM.Term.one, psi (Z zero) A)),
            some (psi (reg 1) (idxOf (reg 1) ((none : Option Term), (none : Option Term))
              (Z TM.Term.one, psi (Z zero) A))))
      else ((none : Option Term),
            some (phiNF (Z TM.Term.one) (plus (baseOf 0) (sub1 (psi (Z zero) A)))))) = _
    rw [if_pos le_reg1_Om2_139, idx_Q139 A]]
  show omegaNF (plus (reg 0) (plus
    (psi (Z zero) (phi zero (add (Z TM.Term.one) (psi (Z zero) A)))) zero)) = _
  rw [show plus (reg 0) (plus
        (psi (Z zero) (phi zero (add (Z TM.Term.one) (psi (Z zero) A)))) zero)
      = psi (Z zero) (phi zero (add (Z TM.Term.one) (psi (Z zero) A))) from rfl]
  exact omegaNF_psi139 _ _

/-- **行 58 の基本列の値、閉じた形。** -/
theorem vOf_fs_i58139 (j : Nat) :
    vOf (fsB i58139 (j + 3))
      = psi (Z zero) (phi zero (add (Z TM.Term.one) (psi (Z zero) (TW (j + 3))))) := by
  have h1 : vOf (fsB i58139 (j + 3))
      = plus TM.Term.one (dict (bVal (fsB i58139 (j + 3)))) := by
    rw [fsB_i58139 (j + 3)]
    exact vOf_nd139 _ _ _
  rw [h1, bVal_fs_i58139 (j + 3)]
  show plus TM.Term.one
    (collapse 0 (collapse 2 (collapse 0 (dict (psiTow (j + 2 + 2)))))) = _
  rw [dict_psiTow139 (j + 2)]
  show plus TM.Term.one (collapse 0 (collapse 2 (collapse 0 (TW (j + 3))))) = _
  rw [collapse0_TW139 j, collapse2_psi139 (TW (j + 3)), collapse0_Q139 (TW (j + 3))]
  exact plus_one_psi139 _ _

/-- 行 58 の証人。表の値の内側の `ψ_Ω(Ω₂)` を `sbad` に置き換えたもの — §137 で外部が
    名指した項そのもの。 -/
def s58139 : Term := psi (Z zero) (phi zero (add (Z TM.Term.one) sbad))

theorem inT_s58139 : inT s58139 = true := rfl
theorem lt_s58_i58139 : lt s58139 (vOf i58139) = true := rfl

theorem lt_fs_s58139 : ∀ (n : Nat), lt (vOf (fsB i58139 n)) s58139 = true
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | j + 3 => by
      rw [vOf_fs_i58139 j]
      show lt (psi (Z zero) (phi zero (add (Z TM.Term.one) (psi (Z zero) (TW (j + 3))))))
        (psi (Z zero) (phi zero (add (Z TM.Term.one) sbad))) = true
      rw [lt_psi_same, lt_phi_same139, lt_add_same139, sbad_eq, lt_psi_same]
      exact lt_TW (j + 3)

/-- **行 58 の主定理。仮説なし。** -/
theorem row58_gap139 :
    (Rows.rows.find? fun r => r.m == matB i58139 0).map (·.t) = some (vOf i58139)
  ∧ inT s58139 = true
  ∧ lt s58139 (vOf i58139) = true
  ∧ ∀ n, Trans.Recal.oR (BMS.expand (matB i58139 0) n) = some (vOf (fsB i58139 n))
       ∧ lt (vOf (fsB i58139 n)) s58139 = true :=
  ⟨rowval58_139, inT_s58139, lt_s58_i58139, fun n =>
    ⟨oR_expand139 i58139 topOKB_i58139 (by intro hc; exact B.noConfusion hc) nfB_i58139 n,
     lt_fs_s58139 n⟩⟩


/-! ### §139.12 行 47 — 内側に §69 の塔、外側に `Ω₂` の桁

`W139 = φ̄(1,Ω₁)` は表が `ψ₁(Ω₂)` と呼ぶ項。`collapse 1` のヴェブレン枝がこれを作る。 -/

/-- `φ̄(1, Ω₁)` = 表の `ψ₁(Ω₂)`。 -/
def W139 : Term := phi TM.Term.one (Z zero)

theorem ltF_psi_Om139 (A : Term) : ∀ (f : Nat), 1 ≤ f →
    ltF f (psi (Z zero) A) (Z zero) = true
  | 0, h => absurd h (by omega)
  | _ + 1, _ => rfl

theorem ltF_one_Z139 {c : Term} (_hc : c ≠ zero) : ∀ (f : Nat), 2 ≤ f →
    ltF f TM.Term.one (Z c) = true := by
  intro f hf
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  show (ltF g zero (Z c) && ltF g zero (Z c)) = true
  rw [ltF_left_zero (show 1 ≤ g by omega)
    (show (Z c : Term) ≠ zero from by intro hcc; exact Term.noConfusion hcc)]
  rfl

theorem ltF_W_Om2_139 : ∀ (f : Nat), 3 ≤ f → ltF f W139 (Z TM.Term.one) = true := by
  intro f hf
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  show (ltF g TM.Term.one (Z TM.Term.one) && ltF g (Z zero) (Z TM.Term.one)) = true
  rw [ltF_one_Z139 (show (TM.Term.one : Term) ≠ zero from by
        intro hc; exact Term.noConfusion hc) g (by omega),
    ltF_Om_Z139 rfl (show (TM.Term.one : Term) ≠ zero from by
        intro hc; exact Term.noConfusion hc) g (by omega)]
  rfl

theorem ltF_addW_Om2_139 (A : Term) : ∀ (f : Nat), 4 ≤ f →
    ltF f (add W139 (psi (Z zero) A)) (Z TM.Term.one) = true := by
  intro f hf
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  show ltF g W139 (Z TM.Term.one) = true
  exact ltF_W_Om2_139 g (by omega)

theorem ltF_R_Om2_139 (A : Term) : ∀ (f : Nat), 5 ≤ f →
    ltF f (phi zero (add W139 (psi (Z zero) A))) (Z TM.Term.one) = true := by
  intro f hf
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  show (ltF g zero (Z TM.Term.one)
        && ltF g (add W139 (psi (Z zero) A)) (Z TM.Term.one)) = true
  rw [ltF_addW_Om2_139 A g (by omega),
    ltF_left_zero (show 1 ≤ g by omega)
      (show (Z TM.Term.one : Term) ≠ zero from by intro hc; exact Term.noConfusion hc)]
  rfl

theorem le_R_Om2_139 (A : Term) :
    le (phi zero (add W139 (psi (Z zero) A))) (Z TM.Term.one) = true := by
  show lt (phi zero (add W139 (psi (Z zero) A))) (Z TM.Term.one) = true
  rw [lt_eq_ltF (phi zero (add W139 (psi (Z zero) A))) (Z TM.Term.one)
    ((phi zero (add W139 (psi (Z zero) A))).deg + 4 + 1)
    (by show (phi zero (add W139 (psi (Z zero) A))).deg + 4
             ≤ (phi zero (add W139 (psi (Z zero) A))).deg + 4 + 1; omega)]
  exact ltF_R_Om2_139 A _ (by
    show 5 ≤ (phi zero (add W139 (psi (Z zero) A))).deg + 4 + 1
    omega)

theorem ltF_W_Om139 : ∀ (f : Nat), ltF f W139 (Z zero) = false
  | 0 => rfl
  | g + 1 => by
      show (ltF g TM.Term.one (Z zero) && ltF g (Z zero) (Z zero)) = false
      rw [ltF_irrefl g (Z zero)]
      exact Bool.and_false _

theorem ltF_addW_Om139 (A : Term) : ∀ (f : Nat),
    ltF f (add W139 (psi (Z zero) A)) (Z zero) = false
  | 0 => rfl
  | g + 1 => by
      show ltF g W139 (Z zero) = false
      exact ltF_W_Om139 g

theorem ltF_R_Om139 (A : Term) : ∀ (f : Nat),
    ltF f (phi zero (add W139 (psi (Z zero) A))) (Z zero) = false
  | 0 => rfl
  | g + 1 => by
      show (ltF g zero (Z zero) && ltF g (add W139 (psi (Z zero) A)) (Z zero)) = false
      rw [ltF_addW_Om139 A g]
      exact Bool.and_false _

theorem lt_R_reg1_139 (A : Term) :
    lt (phi zero (add W139 (psi (Z zero) A))) (reg 1) = false := ltF_R_Om139 A _

theorem le_W_reg1_139 : le W139 (reg 1) = false := rfl
theorem le_reg1_W139 : le (reg 1) W139 = true := rfl

theorem lt_psi_W139 (A : Term) : lt (psi (Z zero) A) W139 = true := by
  show lt (psi (Z zero) A) (phi TM.Term.one (Z zero)) = true
  rw [lt_eq_ltF (psi (Z zero) A) (phi TM.Term.one (Z zero))
    ((psi (Z zero) A).deg + 6 + 1)
    (by show (psi (Z zero) A).deg + 6 ≤ (psi (Z zero) A).deg + 6 + 1; omega)]
  show (((psi (Z zero) A : Term) == TM.Term.one) || ((psi (Z zero) A : Term) == Z zero)
        || ltF ((psi (Z zero) A).deg + 6) (psi (Z zero) A) TM.Term.one
        || ltF ((psi (Z zero) A).deg + 6) (psi (Z zero) A) (Z zero)) = true
  rw [ltF_psi_Om139 A ((psi (Z zero) A).deg + 6) (by omega)]
  exact Bool.or_true _

theorem le_psi_W139 (A : Term) : le (psi (Z zero) A) W139 = true := by
  show lt (psi (Z zero) A) W139 = true
  exact lt_psi_W139 A

theorem ltF_M_add139 {p : Term} (hp : ∀ (f : Nat), ltF f M p = false)
    (hbe : ((M : Term) == p) = false) (A : Term) : ∀ (f : Nat),
    ltF f M (add p (psi (Z zero) A)) = false
  | 0 => rfl
  | g + 1 => by
      show (((M : Term) == p) || ltF g M p) = false
      rw [hbe, hp g]
      rfl

theorem omegaNF_add_psi139 {p A : Term}
    (hM : ∀ (f : Nat), ltF f M (add p (psi (Z zero) A)) = false) :
    omegaNF (add p (psi (Z zero) A)) = phi zero (add p (psi (Z zero) A)) := by
  show (if lt M (add p (psi (Z zero) A)) = true then omg (add p (psi (Z zero) A))
        else if ((add p (psi (Z zero) A) : Term) == M) = true then M
        else phiNF zero (add p (psi (Z zero) A))) = _
  rw [if_neg (by rw [show lt M (add p (psi (Z zero) A)) = false from hM _]
                 exact Bool.noConfusion),
    if_neg (by intro hc; exact Bool.noConfusion hc)]
  show phiNFsucc zero (add p (psi (Z zero) A)) = _
  unfold phiNFsucc
  rw [show splitFin (add p (psi (Z zero) A)) = (add p (psi (Z zero) A), 0) from rfl]
  rfl

theorem omegaNF_addW_psi139 (A : Term) :
    omegaNF (add W139 (psi (Z zero) A)) = phi zero (add W139 (psi (Z zero) A)) :=
  omegaNF_add_psi139 (p := W139) (A := A)
    (ltF_M_add139 (p := W139) (fun f => ltF_M_phi135 TM.Term.one (Z zero) f) rfl A)

theorem plus_W_psi139 (A : Term) :
    plus W139 (psi (Z zero) A) = add W139 (psi (Z zero) A) := by
  show ofList (List.filter (fun a => le (psi (Z zero) A) a) [W139] ++ [psi (Z zero) A]) = _
  rw [show List.filter (fun a => le (psi (Z zero) A) a) [W139] = [W139] from by
    show (match le (psi (Z zero) A) W139 with
          | true => W139 :: List.filter (fun a => le (psi (Z zero) A) a) []
          | false => List.filter (fun a => le (psi (Z zero) A) a) []) = _
    rw [le_psi_W139 A]
    rfl]
  rfl

theorem plus_Om1_addW139 (A : Term) :
    plus (reg 1) (add W139 (psi (Z zero) A)) = add W139 (psi (Z zero) A) := by
  show ofList (List.filter (fun a => le W139 a) [Z zero] ++ [W139, psi (Z zero) A]) = _
  rw [show List.filter (fun a => le W139 a) [Z zero] = [] from by
    show (match le W139 (Z zero) with
          | true => Z zero :: List.filter (fun a => le W139 a) []
          | false => List.filter (fun a => le W139 a) []) = []
    rw [show le W139 (Z zero) = false from le_W_reg1_139]
    rfl]
  rfl

theorem plus_Om2_psi139 (A : Term) :
    plus (Z TM.Term.one) (psi (Z zero) A) = add (Z TM.Term.one) (psi (Z zero) A) := by
  show ofList (List.filter (fun a => le (psi (Z zero) A) a) [Z TM.Term.one]
    ++ [psi (Z zero) A]) = _
  rw [show List.filter (fun a => le (psi (Z zero) A) a) [Z TM.Term.one]
        = [Z TM.Term.one] from by
    show (match le (psi (Z zero) A) (Z TM.Term.one) with
          | true => Z TM.Term.one :: List.filter (fun a => le (psi (Z zero) A) a) []
          | false => List.filter (fun a => le (psi (Z zero) A) a) []) = _
    rw [le_psiOm_Om2_139 A]
    rfl]
  rfl

theorem plus_Om2_R139 (A : Term) :
    plus (Z TM.Term.one) (phi zero (add W139 (psi (Z zero) A)))
      = add (Z TM.Term.one) (phi zero (add W139 (psi (Z zero) A))) := by
  show ofList (List.filter (fun a => le (phi zero (add W139 (psi (Z zero) A))) a)
    [Z TM.Term.one] ++ [phi zero (add W139 (psi (Z zero) A))]) = _
  rw [show List.filter (fun a => le (phi zero (add W139 (psi (Z zero) A))) a)
        [Z TM.Term.one] = [Z TM.Term.one] from by
    show (match le (phi zero (add W139 (psi (Z zero) A))) (Z TM.Term.one) with
          | true => Z TM.Term.one :: List.filter
              (fun a => le (phi zero (add W139 (psi (Z zero) A))) a) []
          | false => List.filter
              (fun a => le (phi zero (add W139 (psi (Z zero) A))) a) []) = _
    rw [le_R_Om2_139 A]
    rfl]
  rfl

/-- `ψ₁` の畳み込み — 桁が `Ω₂` 一つ、余りが `ψ_{Ω₁}` の項。ヴェブレン枝が `W139` を作る。 -/
theorem collapse1_Om2psi139 (A : Term) :
    collapse 1 (add (Z TM.Term.one) (psi (Z zero) A))
      = phi zero (add W139 (psi (Z zero) A)) := by
  rw [collapse_eq 1 (add (Z TM.Term.one) (psi (Z zero) A)),
    show toList (add (Z TM.Term.one) (psi (Z zero) A))
      = [Z TM.Term.one, psi (Z zero) A] from rfl,
    wcnf_cons_ge (show lt (Z TM.Term.one) (reg 2) = false from lt_irrefl _),
    wcnf_cons_lt (show lt (psi (Z zero) A) (reg 2) = true from lt_psiOm_Om2_139 A)]
  show omegaNF (plus (reg 1) (plus
    (([(wA (reg 2) (Z TM.Term.one), wC (reg 2) (Z TM.Term.one))].foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 2) (baseOf 1))).2.getD zero)
    (ofList [psi (Z zero) A]))) = _
  rw [show wA (reg 2) (Z TM.Term.one) = TM.Term.one from rfl,
    show wC (reg 2) (Z TM.Term.one) = TM.Term.one from rfl,
    show ([((TM.Term.one : Term), TM.Term.one)].foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 2) (baseOf 1))) = ((none : Option Term), some W139) from rfl]
  show omegaNF (plus (reg 1) (plus W139 (psi (Z zero) A))) = _
  rw [plus_W_psi139 A, plus_Om1_addW139 A]
  exact omegaNF_addW_psi139 A

/-! `ψ₀` の畳み込み — 桁が二つ、どちらも強臨界。 -/

theorem idxOf_none139 (a c : Term) :
    idxOf (reg 1) ((none : Option Term), (none : Option Term)) (a, c)
      = sub1 (mulL (mulL (reg 1) (subAP (reg 1) a)) c) := rfl

theorem stepF_sc139 {a c : Term} (h : le (reg 1) a = true) :
    stepF (reg 1) (baseOf 0) ((none : Option Term), (none : Option Term)) (a, c)
      = ((some (idxOf (reg 1) ((none : Option Term), (none : Option Term)) (a, c))
            : Option Term),
         some (psi (reg 1)
           (idxOf (reg 1) ((none : Option Term), (none : Option Term)) (a, c)))) := by
  show (if le (reg 1) a = true
        then ((some (idxOf (reg 1) ((none : Option Term), (none : Option Term)) (a, c))
                : Option Term),
              some (psi (reg 1)
                (idxOf (reg 1) ((none : Option Term), (none : Option Term)) (a, c))))
        else ((none : Option Term), some (phiNF a (plus (baseOf 0) (sub1 c))))) = _
  rw [if_pos h]

theorem stepF_sc2_139 {i0 v a c : Term} (h : le (reg 1) a = true) :
    stepF (reg 1) (baseOf 0) ((some i0 : Option Term), (some v : Option Term)) (a, c)
      = ((some (plus i0 (mulL (mulL (reg 1) (subAP (reg 1) a)) c)) : Option Term),
         some (psi (reg 1) (plus i0 (mulL (mulL (reg 1) (subAP (reg 1) a)) c)))) := by
  show (if le (reg 1) a = true
        then ((some (idxOf (reg 1) ((some i0 : Option Term), (some v : Option Term)) (a, c))
                : Option Term),
              some (psi (reg 1)
                (idxOf (reg 1) ((some i0 : Option Term), (some v : Option Term)) (a, c))))
        else ((some i0 : Option Term), some (phiNF a (plus v c)))) = _
  rw [if_pos h]
  rfl

theorem wA_R139 (A : Term) :
    wA (reg 1) (phi zero (add W139 (psi (Z zero) A))) = W139 := by
  show ofList (List.map (divAP (reg 1)) (List.filter (fun q => !lt q (reg 1))
    (toList (logOm (phi zero (add W139 (psi (Z zero) A))))))) = _
  rw [logOm_phi0_135 (show phiShifted zero (add W139 (psi (Z zero) A)) = false from rfl),
    show toList (add W139 (psi (Z zero) A)) = [W139, psi (Z zero) A] from rfl,
    show (List.filter (fun q => !lt q (reg 1)) [W139, psi (Z zero) A]) = [W139] from by
      show (match (!lt W139 (reg 1)) with
            | true => W139 :: List.filter (fun q => !lt q (reg 1)) [psi (Z zero) A]
            | false => List.filter (fun q => !lt q (reg 1)) [psi (Z zero) A]) = _
      rw [show lt W139 (reg 1) = false from ltF_W_Om139 _]
      show (W139 : Term) :: (match (!lt (psi (Z zero) A) (reg 1)) with
            | true => psi (Z zero) A :: List.filter (fun q => !lt q (reg 1)) []
            | false => List.filter (fun q => !lt q (reg 1)) []) = _
      rw [lt_psiOm_reg1_139 A]
      rfl]
  show divAP (reg 1) W139 = _
  show omegaNF (subAP (reg 1) (logOm W139)) = _
  rw [show logOm W139 = W139 from rfl]
  show omegaNF (if ((W139 : Term) == reg 1) = true then ofList [] else W139) = _
  rw [if_neg (by intro hc; exact Bool.noConfusion hc)]
  exact omegaNF_phi135 (show lt zero TM.Term.one = true from rfl)

theorem wC_R139 (A : Term) :
    wC (reg 1) (phi zero (add W139 (psi (Z zero) A))) = psi (Z zero) A := by
  show omegaNF (ofList (List.filter (fun q => lt q (reg 1))
    (toList (logOm (phi zero (add W139 (psi (Z zero) A))))))) = _
  rw [logOm_phi0_135 (show phiShifted zero (add W139 (psi (Z zero) A)) = false from rfl),
    show toList (add W139 (psi (Z zero) A)) = [W139, psi (Z zero) A] from rfl,
    show (List.filter (fun q => lt q (reg 1)) [W139, psi (Z zero) A])
      = [psi (Z zero) A] from by
      show (match (lt W139 (reg 1)) with
            | true => W139 :: List.filter (fun q => lt q (reg 1)) [psi (Z zero) A]
            | false => List.filter (fun q => lt q (reg 1)) [psi (Z zero) A]) = _
      rw [show lt W139 (reg 1) = false from ltF_W_Om139 _]
      show (match (lt (psi (Z zero) A) (reg 1)) with
            | true => psi (Z zero) A :: List.filter (fun q => lt q (reg 1)) []
            | false => List.filter (fun q => lt q (reg 1)) []) = _
      rw [lt_psiOm_reg1_139 A]
      rfl]
  exact omegaNF_psi139 (Z zero) A

theorem wcnf_R139 (A : Term) :
    wcnf (reg 1) [phi zero (add W139 (psi (Z zero) A))]
      = ([(W139, psi (Z zero) A)], zero) := by
  rw [wcnf_cons_ge (lt_R_reg1_139 A)]
  show ([(wA (reg 1) (phi zero (add W139 (psi (Z zero) A))),
          wC (reg 1) (phi zero (add W139 (psi (Z zero) A))))], zero) = _
  rw [wA_R139 A, wC_R139 A]

theorem wcnf_Om2R139 (A : Term) :
    wcnf (reg 1) [Z TM.Term.one, phi zero (add W139 (psi (Z zero) A))]
      = ([(Z TM.Term.one, TM.Term.one), (W139, psi (Z zero) A)], zero) := by
  rw [wcnf_cons_ge lt_Om2_reg1_139, wcnf_R139 A]
  show (if (wA (reg 1) (Z TM.Term.one) == W139) = true
        then ((wA (reg 1) (Z TM.Term.one),
               plus (wC (reg 1) (Z TM.Term.one)) (psi (Z zero) A)) :: [], zero)
        else ((wA (reg 1) (Z TM.Term.one), wC (reg 1) (Z TM.Term.one))
              :: (W139, psi (Z zero) A) :: [], zero)) = _
  rw [show wA (reg 1) (Z TM.Term.one) = Z TM.Term.one from rfl,
    show wC (reg 1) (Z TM.Term.one) = TM.Term.one from rfl,
    if_neg (by intro hc; exact Bool.noConfusion hc)]

theorem idx1_Om2_139 :
    idxOf (reg 1) ((none : Option Term), (none : Option Term))
      (Z TM.Term.one, TM.Term.one) = Z TM.Term.one := rfl

theorem d2_R139 (A : Term) :
    mulL (mulL (reg 1) (subAP (reg 1) W139)) (psi (Z zero) A)
      = phi zero (add W139 (psi (Z zero) A)) := by
  rw [show subAP (reg 1) W139 = W139 from rfl, show mulL (reg 1) W139 = W139 from rfl]
  show ofList (List.map (fun p => omegaNF (plus W139 (logOm p))) [psi (Z zero) A]) = _
  show omegaNF (plus W139 (logOm (psi (Z zero) A))) = _
  rw [show logOm (psi (Z zero) A) = psi (Z zero) A from rfl, plus_W_psi139 A]
  exact omegaNF_addW_psi139 A

theorem collapse0_R139 (A : Term) :
    collapse 0 (add (Z TM.Term.one) (phi zero (add W139 (psi (Z zero) A))))
      = psi (Z zero) (add (Z TM.Term.one) (phi zero (add W139 (psi (Z zero) A)))) := by
  rw [collapse_eq 0 (add (Z TM.Term.one) (phi zero (add W139 (psi (Z zero) A)))),
    show toList (add (Z TM.Term.one) (phi zero (add W139 (psi (Z zero) A))))
      = [Z TM.Term.one, phi zero (add W139 (psi (Z zero) A))] from rfl,
    wcnf_Om2R139 A]
  show omegaNF (plus (reg 0) (plus
    ((((stepF (reg 1) (baseOf 0))
        ((stepF (reg 1) (baseOf 0)) ((none : Option Term), (none : Option Term))
          (Z TM.Term.one, TM.Term.one)) (W139, psi (Z zero) A)).2).getD zero) zero)) = _
  rw [stepF_sc139 (show le (reg 1) (Z TM.Term.one) = true from le_reg1_Om2_139),
    idx1_Om2_139, stepF_sc2_139 (show le (reg 1) W139 = true from le_reg1_W139),
    d2_R139 A, plus_Om2_R139 A]
  show omegaNF (plus (reg 0) (plus
    (psi (Z zero) (add (Z TM.Term.one) (phi zero (add W139 (psi (Z zero) A))))) zero)) = _
  rw [show plus (reg 0) (plus
        (psi (Z zero) (add (Z TM.Term.one) (phi zero (add W139 (psi (Z zero) A))))) zero)
      = psi (Z zero) (add (Z TM.Term.one) (phi zero (add W139 (psi (Z zero) A))))
      from rfl]
  exact omegaNF_psi139 _ _

/-! 行 47 の基本列と値。 -/

theorem fsB_i47139 (n : Nat) :
    fsB i47139 n = .nd 0 .nil (.nd 1 .nil (.nd 0 q139 (bTow n))) := by
  show B.nd 0 .nil (.nd 1 .nil (.nd 0 q139 (appB .nil (iterD 1 (.nd 2 .nil .nil) n)))) = _
  rw [appB_nil, iterD_bTow n]

theorem bVal_fs_i47139 (n : Nat) :
    bVal (fsB i47139 n)
      = BT.D 0 (BT.sum (BT.D 2 BT.zero)
          (BT.D 1 (BT.sum (BT.D 2 BT.zero) (BT.D 0 (psiTow (n + 1)))))) := by
  rw [fsB_i47139 n]
  obtain ⟨x, hx⟩ := bTow_shape n
  have h : bVal (B.nd 0 .nil (.nd 1 .nil (.nd 0 q139 (bTow n))))
      = BT.D 0 (BT.sum (BT.D 2 BT.zero)
          (BT.D 1 (BT.sum (BT.D 2 BT.zero) (BT.D 0 (bArg 0 (bTow n)))))) := by
    rw [hx]; rfl
  rw [h, bArg0_bTow n]

theorem dict_Om2bt139 : dict (BT.D 2 BT.zero) = Z TM.Term.one := rfl

/-- **行 47 の基本列の値、閉じた形。** -/
theorem vOf_fs_i47139 (j : Nat) :
    vOf (fsB i47139 (j + 3))
      = psi (Z zero) (add (Z TM.Term.one)
          (phi zero (add W139 (psi (Z zero) (TW (j + 3)))))) := by
  have h1 : vOf (fsB i47139 (j + 3))
      = plus TM.Term.one (dict (bVal (fsB i47139 (j + 3)))) := by
    rw [fsB_i47139 (j + 3)]
    exact vOf_nd139 _ _ _
  rw [h1, bVal_fs_i47139 (j + 3)]
  show plus TM.Term.one (collapse 0 (plus (dict (BT.D 2 BT.zero))
    (collapse 1 (plus (dict (BT.D 2 BT.zero))
      (collapse 0 (dict (psiTow (j + 2 + 2)))))))) = _
  rw [dict_Om2bt139, dict_psiTow139 (j + 2)]
  show plus TM.Term.one (collapse 0 (plus (Z TM.Term.one)
    (collapse 1 (plus (Z TM.Term.one) (collapse 0 (TW (j + 3))))))) = _
  rw [collapse0_TW139 j, plus_Om2_psi139 (TW (j + 3)), collapse1_Om2psi139 (TW (j + 3)),
    plus_Om2_R139 (TW (j + 3)), collapse0_R139 (TW (j + 3))]
  exact plus_one_psi139 _ _

/-- 行 47 の証人。表の値の内側の `ψ_Ω(Ω₂)` を `sbad` に置き換えたもの。 -/
def s47139 : Term :=
  psi (Z zero) (add (Z TM.Term.one) (phi zero (add W139 sbad)))

theorem inT_s47139 : inT s47139 = true := rfl
theorem lt_s47_i47139 : lt s47139 (vOf i47139) = true := rfl

theorem lt_fs_s47139 : ∀ (n : Nat), lt (vOf (fsB i47139 n)) s47139 = true
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | j + 3 => by
      rw [vOf_fs_i47139 j]
      show lt (psi (Z zero) (add (Z TM.Term.one)
              (phi zero (add W139 (psi (Z zero) (TW (j + 3)))))))
        (psi (Z zero) (add (Z TM.Term.one) (phi zero (add W139 sbad)))) = true
      rw [lt_psi_same, lt_add_same139, lt_phi_same139, lt_add_same139, sbad_eq,
        lt_psi_same]
      exact lt_TW (j + 3)

/-- **行 47 の主定理。仮説なし。** -/
theorem row47_gap139 :
    (Rows.rows.find? fun r => r.m == matB i47139 0).map (·.t) = some (vOf i47139)
  ∧ inT s47139 = true
  ∧ lt s47139 (vOf i47139) = true
  ∧ ∀ n, Trans.Recal.oR (BMS.expand (matB i47139 0) n) = some (vOf (fsB i47139 n))
       ∧ lt (vOf (fsB i47139 n)) s47139 = true :=
  ⟨rowval47_139, inT_s47139, lt_s47_i47139, fun n =>
    ⟨oR_expand139 i47139 topOKB_i47139 (by intro hc; exact B.noConfusion hc) nfB_i47139 n,
     lt_fs_s47139 n⟩⟩



/-! ### §139.13 `φ̄(1,c)` の上の φ̄0 塔 — 行 52・53 が共通に使う

行 52・53 の基本列の値は §69 の `TW` と同じ形の塔で、底が `Ω₁ ⊕ Ω₁` ではなく
`P ⊕ P` (`P = φ̄(1,c)`) になったもの。`c` についての 4 つの条件だけで塔の性質が出る。 -/

/-- 塔の底に置ける `φ̄(1,c)` の条件。`c = Ω₁` と `c = Ω₁ ⊕ 1` が満たす。 -/
structure TowC138 (c : Term) : Prop where
  cOm : ∀ (f : Nat), ltF f c (Z zero) = false
  OmP : ∀ (f : Nat), 4 ≤ f → ltF f (Z zero) (phi TM.Term.one c) = true
  POm2 : ∀ (f : Nat), 4 ≤ f → ltF f (phi TM.Term.one c) (Z TM.Term.one) = true
  gap0 : lt (add (phi TM.Term.one c) (phi TM.Term.one c))
           (phi TM.Term.one (phi TM.Term.one c)) = true

/-- `P ⊕ P` の上に積んだ φ̄0 の塔。 -/
def TWG139 (c : Term) : Nat → Term
  | 0 => add (phi TM.Term.one c) (phi TM.Term.one c)
  | j + 1 => phi zero (TWG139 c j)

theorem deg_TWG139 (c : Term) : ∀ (j : Nat), (TWG139 c j).deg = 2 * j + 9 + 2 * c.deg
  | 0 => by show 1 + (1 + 3 + c.deg) + (1 + 3 + c.deg) = 2 * 0 + 9 + 2 * c.deg; omega
  | j + 1 => by
      show 1 + 1 + (TWG139 c j).deg = 2 * (j + 1) + 9 + 2 * c.deg
      rw [deg_TWG139 c j]
      omega

theorem beq_TWG_Om139 (c : Term) : ∀ (j : Nat), ((TWG139 c j : Term) == Z zero) = false
  | 0 => rfl
  | _ + 1 => rfl

theorem beq_Om2_TWG139 (c : Term) :
    ∀ (j : Nat), ((Z TM.Term.one : Term) == TWG139 c j) = false
  | 0 => rfl
  | _ + 1 => rfl

theorem beq_TWG_P139 (c : Term) :
    ∀ (j : Nat), ((TWG139 c j : Term) == phi TM.Term.one c) = false
  | 0 => rfl
  | _ + 1 => rfl

theorem beq_TWGs_one139 (c : Term) :
    ∀ (j : Nat), ((phi zero (TWG139 c j) : Term) == TM.Term.one) = false
  | 0 => rfl
  | _ + 1 => rfl

theorem ltF_P_Om139 {c : Term} (h : TowC138 c) :
    ∀ (f : Nat), ltF f (phi TM.Term.one c) (Z zero) = false
  | 0 => rfl
  | g + 1 => by
      show (ltF g TM.Term.one (Z zero) && ltF g c (Z zero)) = false
      rw [h.cOm g]
      exact Bool.and_false _

theorem lt_P_reg1_139 {c : Term} (h : TowC138 c) :
    lt (phi TM.Term.one c) (reg 1) = false := ltF_P_Om139 h _

theorem le_P_reg1_139 {c : Term} (h : TowC138 c) :
    le (phi TM.Term.one c) (reg 1) = false := by
  show lt (phi TM.Term.one c) (Z zero) = false
  exact ltF_P_Om139 h _

theorem le_P_Om2_139 {c : Term} (h : TowC138 c) :
    le (phi TM.Term.one c) (Z TM.Term.one) = true := by
  show (((phi TM.Term.one c : Term) == Z TM.Term.one)
        || lt (phi TM.Term.one c) (Z TM.Term.one)) = true
  rw [show lt (phi TM.Term.one c) (Z TM.Term.one) = true from by
    rw [lt_eq_ltF (phi TM.Term.one c) (Z TM.Term.one) (c.deg + 9)
      (by show (1 + 3 + c.deg) + 4 ≤ c.deg + 9; omega)]
    exact h.POm2 (c.deg + 9) (by omega)]
  exact Bool.or_true _

theorem ltF_TWG_Om139 {c : Term} (h : TowC138 c) :
    ∀ (j f : Nat), ltF f (TWG139 c j) (Z zero) = false
  | _, 0 => rfl
  | 0, g + 1 => by
      show ltF g (phi TM.Term.one c) (Z zero) = false
      exact ltF_P_Om139 h g
  | j + 1, g + 1 => by
      show (ltF g zero (Z zero) && ltF g (TWG139 c j) (Z zero)) = false
      rw [ltF_TWG_Om139 h j g]
      exact Bool.and_false _

theorem lt_TWG_reg1_139 {c : Term} (h : TowC138 c) (j : Nat) :
    lt (TWG139 c j) (reg 1) = false := ltF_TWG_Om139 h j _

theorem le_TWG_reg1_139 {c : Term} (h : TowC138 c) (j : Nat) :
    le (TWG139 c j) (reg 1) = false := by
  show (((TWG139 c j : Term) == Z zero) || lt (TWG139 c j) (Z zero)) = false
  rw [beq_TWG_Om139 c j, show lt (TWG139 c j) (Z zero) = false from ltF_TWG_Om139 h j _]
  rfl

theorem ltF_Om_TWG139 {c : Term} (h : TowC138 c) :
    ∀ (j f : Nat), j + 5 ≤ f → ltF f (Z zero) (TWG139 c j) = true
  | _, 0, hh => absurd hh (by omega)
  | 0, g + 1, _ => by
      show (((Z zero : Term) == phi TM.Term.one c)
            || ltF g (Z zero) (phi TM.Term.one c)) = true
      rw [h.OmP g (by omega)]
      exact Bool.or_true _
  | j + 1, g + 1, hh => by
      show ((Z zero : Term) == zero || (Z zero : Term) == TWG139 c j
            || ltF g (Z zero) zero || ltF g (Z zero) (TWG139 c j)) = true
      rw [ltF_Om_TWG139 h j g (by omega)]
      exact Bool.or_true _

theorem lt_Om_TWG139 {c : Term} (h : TowC138 c) (j : Nat) :
    lt (Z zero) (TWG139 c j) = true := by
  rw [lt_eq_ltF (Z zero) (TWG139 c j) (3 * j + 20 + 2 * c.deg)
    (by rw [deg_TWG139 c j]; show 2 + (2 * j + 9 + 2 * c.deg) ≤ 3 * j + 20 + 2 * c.deg; omega)]
  exact ltF_Om_TWG139 h j (3 * j + 20 + 2 * c.deg) (by omega)

theorem le_reg1_TWG139 {c : Term} (h : TowC138 c) (j : Nat) :
    le (reg 1) (TWG139 c j) = true := by
  show (((Z zero : Term) == TWG139 c j) || lt (Z zero) (TWG139 c j)) = true
  rw [lt_Om_TWG139 h j]
  exact Bool.or_true _

theorem ltF_TWG_Om2_139 {c : Term} (h : TowC138 c) :
    ∀ (j f : Nat), j + 5 ≤ f → ltF f (TWG139 c j) (Z TM.Term.one) = true
  | _, 0, hh => absurd hh (by omega)
  | 0, g + 1, _ => by
      show ltF g (phi TM.Term.one c) (Z TM.Term.one) = true
      exact h.POm2 g (by omega)
  | j + 1, g + 1, hh => by
      show (ltF g zero (Z TM.Term.one) && ltF g (TWG139 c j) (Z TM.Term.one)) = true
      rw [ltF_TWG_Om2_139 h j g (by omega),
        ltF_left_zero (show 1 ≤ g by omega)
          (show (Z TM.Term.one : Term) ≠ zero from by intro hc; exact Term.noConfusion hc)]
      rfl

theorem lt_TWG_Om2_139 {c : Term} (h : TowC138 c) (j : Nat) :
    lt (TWG139 c j) (Z TM.Term.one) = true := by
  rw [lt_eq_ltF (TWG139 c j) (Z TM.Term.one) (3 * j + 20 + 2 * c.deg)
    (by rw [deg_TWG139 c j]
        show (2 * j + 9 + 2 * c.deg) + 4 ≤ 3 * j + 20 + 2 * c.deg
        omega)]
  exact ltF_TWG_Om2_139 h j (3 * j + 20 + 2 * c.deg) (by omega)

theorem le_TWG_Om2_139 {c : Term} (h : TowC138 c) (j : Nat) :
    le (TWG139 c j) (Z TM.Term.one) = true := by
  show (((TWG139 c j : Term) == Z TM.Term.one) || lt (TWG139 c j) (Z TM.Term.one)) = true
  rw [lt_TWG_Om2_139 h j]
  exact Bool.or_true _

theorem lt_TWG_reg2_139 {c : Term} (h : TowC138 c) (j : Nat) :
    lt (TWG139 c j) (reg 2) = true := lt_TWG_Om2_139 h j

theorem ltF_addPP_P139 (c : Term) :
    ∀ (f : Nat), ltF f (add (phi TM.Term.one c) (phi TM.Term.one c)) (phi TM.Term.one c)
      = false
  | 0 => rfl
  | g + 1 => by
      show ltF g (phi TM.Term.one c) (phi TM.Term.one c) = false
      exact ltF_irrefl g _

theorem lt_TWG_P139 (c : Term) :
    ∀ (j : Nat), lt (TWG139 c j) (phi TM.Term.one c) = false
  | 0 => ltF_addPP_P139 c _
  | j + 1 => by
      show lt (phi zero (TWG139 c j)) (phi TM.Term.one c) = false
      rw [lt_phi_zero_one]
      exact lt_TWG_P139 c j

theorem le_TWG_P139 (c : Term) (j : Nat) :
    le (TWG139 c j) (phi TM.Term.one c) = false := by
  show (((TWG139 c j : Term) == phi TM.Term.one c)
        || lt (TWG139 c j) (phi TM.Term.one c)) = false
  rw [beq_TWG_P139 c j, lt_TWG_P139 c j]
  rfl

/-- **隙間の順序の側。** 塔はどれも `φ̄(1, φ̄(1,c))` の下。 -/
theorem lt_TWG_gap139 {c : Term} (h : TowC138 c) :
    ∀ (j : Nat), lt (TWG139 c j) (phi TM.Term.one (phi TM.Term.one c)) = true
  | 0 => h.gap0
  | j + 1 => by
      show lt (phi zero (TWG139 c j)) (phi TM.Term.one (phi TM.Term.one c)) = true
      rw [lt_phi_zero_one]
      exact lt_TWG_gap139 h j

theorem phiShifted_TWG139 (c : Term) :
    ∀ (j : Nat), phiShifted zero (TWG139 c j) = false
  | 0 => rfl
  | j + 1 => phiShifted_phi0_135 (beq_TWGs_one139 c j)

theorem ltF_M_addPP139 (c : Term) :
    ∀ (f : Nat), ltF f M (add (phi TM.Term.one c) (phi TM.Term.one c)) = false
  | 0 => rfl
  | g + 1 => by
      show (((M : Term) == phi TM.Term.one c) || ltF g M (phi TM.Term.one c)) = false
      rw [ltF_M_phi135 TM.Term.one c g]
      rfl

theorem omegaNF_addPP139 (c : Term) :
    omegaNF (add (phi TM.Term.one c) (phi TM.Term.one c))
      = phi zero (add (phi TM.Term.one c) (phi TM.Term.one c)) := by
  show (if lt M (add (phi TM.Term.one c) (phi TM.Term.one c)) = true
          then omg (add (phi TM.Term.one c) (phi TM.Term.one c))
        else if ((add (phi TM.Term.one c) (phi TM.Term.one c) : Term) == M) = true then M
        else phiNF zero (add (phi TM.Term.one c) (phi TM.Term.one c))) = _
  rw [if_neg (by
      rw [show lt M (add (phi TM.Term.one c) (phi TM.Term.one c)) = false from
        ltF_M_addPP139 c _]
      exact Bool.noConfusion),
    if_neg (by intro hc; exact Bool.noConfusion hc)]
  show phiNFsucc zero (add (phi TM.Term.one c) (phi TM.Term.one c)) = _
  unfold phiNFsucc
  rw [show splitFin (add (phi TM.Term.one c) (phi TM.Term.one c))
        = (add (phi TM.Term.one c) (phi TM.Term.one c), 0) from rfl]
  rfl

theorem omegaNF_TWG139 (c : Term) :
    ∀ (j : Nat), omegaNF (TWG139 c j) = TWG139 c (j + 1)
  | 0 => omegaNF_addPP139 c
  | j + 1 => omegaNF_phi0_135 (beq_TWGs_one139 c j)

theorem subAP_TWG139 (c : Term) :
    ∀ (j : Nat), subAP (reg 1) (TWG139 c j) = TWG139 c j
  | 0 => rfl
  | _ + 1 => rfl

theorem plus_Om1_P139 {c : Term} (h : TowC138 c) :
    plus (reg 1) (phi TM.Term.one c) = phi TM.Term.one c := by
  show ofList (List.filter (fun a => le (phi TM.Term.one c) a) [Z zero]
    ++ [phi TM.Term.one c]) = _
  rw [show List.filter (fun a => le (phi TM.Term.one c) a) [Z zero] = [] from by
    show (match le (phi TM.Term.one c) (Z zero) with
          | true => Z zero :: List.filter (fun a => le (phi TM.Term.one c) a) []
          | false => List.filter (fun a => le (phi TM.Term.one c) a) []) = []
    rw [show le (phi TM.Term.one c) (Z zero) = false from le_P_reg1_139 h]
    rfl]
  rfl

theorem plus_Om1_TWG139 {c : Term} (h : TowC138 c) :
    ∀ (j : Nat), plus (reg 1) (TWG139 c j) = TWG139 c j
  | 0 => by
      show ofList (List.filter (fun a => le (phi TM.Term.one c) a) [Z zero]
        ++ [phi TM.Term.one c, phi TM.Term.one c]) = _
      rw [show List.filter (fun a => le (phi TM.Term.one c) a) [Z zero] = [] from by
        show (match le (phi TM.Term.one c) (Z zero) with
              | true => Z zero :: List.filter (fun a => le (phi TM.Term.one c) a) []
              | false => List.filter (fun a => le (phi TM.Term.one c) a) []) = []
        rw [show le (phi TM.Term.one c) (Z zero) = false from le_P_reg1_139 h]
        rfl]
      rfl
  | j + 1 => by
      show ofList (List.filter (fun a => le (phi zero (TWG139 c j)) a) [Z zero]
        ++ [phi zero (TWG139 c j)]) = _
      rw [show List.filter (fun a => le (phi zero (TWG139 c j)) a) [Z zero] = [] from by
        show (match le (phi zero (TWG139 c j)) (Z zero) with
              | true => Z zero :: List.filter (fun a => le (phi zero (TWG139 c j)) a) []
              | false => List.filter (fun a => le (phi zero (TWG139 c j)) a) []) = []
        rw [show le (phi zero (TWG139 c j)) (Z zero) = false
              from le_TWG_reg1_139 h (j + 1)]
        rfl]
      rfl

theorem mulL_Om1_TWG139 {c : Term} (h : TowC138 c) :
    ∀ (j : Nat), mulL (reg 1) (TWG139 c j) = TWG139 c j
  | 0 => by
      show ofList [omegaNF (plus (reg 1) (logOm (phi TM.Term.one c))),
                   omegaNF (plus (reg 1) (logOm (phi TM.Term.one c)))] = _
      rw [show logOm (phi TM.Term.one c) = phi TM.Term.one c from rfl, plus_Om1_P139 h,
        omegaNF_phi135 (show lt zero TM.Term.one = true from rfl)]
      rfl
  | j + 1 => by
      show omegaNF (plus (reg 1) (logOm (phi zero (TWG139 c j)))) = _
      rw [logOm_phi0_135 (phiShifted_TWG139 c j), plus_Om1_TWG139 h j, omegaNF_TWG139 c j]

theorem mulL_TWG_one139 (c : Term) (j : Nat) :
    mulL (TWG139 c j) TM.Term.one = TWG139 c (j + 1) := by
  show omegaNF (plus (TWG139 c j) (logOm TM.Term.one)) = _
  rw [show logOm TM.Term.one = zero from rfl,
    show plus (TWG139 c j) zero = TWG139 c j from rfl]
  exact omegaNF_TWG139 c j

theorem divAP_P139 {c : Term} (_h : TowC138 c) :
    divAP (reg 1) (phi TM.Term.one c) = phi TM.Term.one c := by
  show omegaNF (subAP (reg 1) (logOm (phi TM.Term.one c))) = _
  rw [show logOm (phi TM.Term.one c) = phi TM.Term.one c from rfl,
    show subAP (reg 1) (phi TM.Term.one c) = phi TM.Term.one c from rfl]
  exact omegaNF_phi135 (show lt zero TM.Term.one = true from rfl)

theorem filter_ge_PP139 {c : Term} (h : TowC138 c) :
    List.filter (fun q => !lt q (reg 1)) [phi TM.Term.one c, phi TM.Term.one c]
      = [phi TM.Term.one c, phi TM.Term.one c] := by
  show (match (!lt (phi TM.Term.one c) (reg 1)) with
        | true => phi TM.Term.one c
            :: List.filter (fun q => !lt q (reg 1)) [phi TM.Term.one c]
        | false => List.filter (fun q => !lt q (reg 1)) [phi TM.Term.one c]) = _
  rw [lt_P_reg1_139 h]
  show (phi TM.Term.one c : Term) :: (match (!lt (phi TM.Term.one c) (reg 1)) with
        | true => phi TM.Term.one c :: List.filter (fun q => !lt q (reg 1)) []
        | false => List.filter (fun q => !lt q (reg 1)) []) = _
  rw [lt_P_reg1_139 h]
  rfl

theorem filter_lt_PP139 {c : Term} (h : TowC138 c) :
    List.filter (fun q => lt q (reg 1)) [phi TM.Term.one c, phi TM.Term.one c] = [] := by
  show (match (lt (phi TM.Term.one c) (reg 1)) with
        | true => phi TM.Term.one c
            :: List.filter (fun q => lt q (reg 1)) [phi TM.Term.one c]
        | false => List.filter (fun q => lt q (reg 1)) [phi TM.Term.one c]) = _
  rw [lt_P_reg1_139 h]
  show (match (lt (phi TM.Term.one c) (reg 1)) with
        | true => phi TM.Term.one c :: List.filter (fun q => lt q (reg 1)) []
        | false => List.filter (fun q => lt q (reg 1)) []) = _
  rw [lt_P_reg1_139 h]
  rfl

theorem filter_ge_TWG139 {c : Term} (h : TowC138 c) (j : Nat) :
    List.filter (fun q => !lt q (reg 1)) [TWG139 c (j + 1)] = [TWG139 c (j + 1)] := by
  show (match (!lt (TWG139 c (j + 1)) (reg 1)) with
        | true => TWG139 c (j + 1) :: List.filter (fun q => !lt q (reg 1)) []
        | false => List.filter (fun q => !lt q (reg 1)) []) = _
  rw [lt_TWG_reg1_139 h (j + 1)]
  rfl

theorem filter_lt_TWG139 {c : Term} (h : TowC138 c) (j : Nat) :
    List.filter (fun q => lt q (reg 1)) [TWG139 c (j + 1)] = [] := by
  show (match (lt (TWG139 c (j + 1)) (reg 1)) with
        | true => TWG139 c (j + 1) :: List.filter (fun q => lt q (reg 1)) []
        | false => List.filter (fun q => lt q (reg 1)) []) = _
  rw [lt_TWG_reg1_139 h (j + 1)]
  rfl

theorem wA_TWG139 {c : Term} (h : TowC138 c) :
    ∀ (j : Nat), wA (reg 1) (TWG139 c (j + 1)) = TWG139 c j
  | 0 => by
      show ofList (List.map (divAP (reg 1)) (List.filter (fun q => !lt q (reg 1))
        (toList (logOm (phi zero (TWG139 c 0)))))) = _
      rw [logOm_phi0_135 (phiShifted_TWG139 c 0),
        show toList (TWG139 c 0) = [phi TM.Term.one c, phi TM.Term.one c] from rfl,
        filter_ge_PP139 h]
      show ofList [divAP (reg 1) (phi TM.Term.one c), divAP (reg 1) (phi TM.Term.one c)] = _
      rw [divAP_P139 h]
      rfl
  | j + 1 => by
      show ofList (List.map (divAP (reg 1)) (List.filter (fun q => !lt q (reg 1))
        (toList (logOm (phi zero (TWG139 c (j + 1))))))) = _
      rw [logOm_phi0_135 (phiShifted_TWG139 c (j + 1)),
        show toList (TWG139 c (j + 1)) = [TWG139 c (j + 1)] from rfl,
        filter_ge_TWG139 h j]
      show divAP (reg 1) (TWG139 c (j + 1)) = _
      show omegaNF (subAP (reg 1) (logOm (TWG139 c (j + 1)))) = _
      rw [show logOm (TWG139 c (j + 1)) = TWG139 c j from
            logOm_phi0_135 (phiShifted_TWG139 c j),
        subAP_TWG139 c j]
      exact omegaNF_TWG139 c j

theorem wC_TWG139 {c : Term} (h : TowC138 c) :
    ∀ (j : Nat), wC (reg 1) (TWG139 c (j + 1)) = TM.Term.one
  | 0 => by
      show omegaNF (ofList (List.filter (fun q => lt q (reg 1))
        (toList (logOm (phi zero (TWG139 c 0)))))) = _
      rw [logOm_phi0_135 (phiShifted_TWG139 c 0),
        show toList (TWG139 c 0) = [phi TM.Term.one c, phi TM.Term.one c] from rfl,
        filter_lt_PP139 h]
      exact omegaNF_zero135
  | j + 1 => by
      show omegaNF (ofList (List.filter (fun q => lt q (reg 1))
        (toList (logOm (phi zero (TWG139 c (j + 1))))))) = _
      rw [logOm_phi0_135 (phiShifted_TWG139 c (j + 1)),
        show toList (TWG139 c (j + 1)) = [TWG139 c (j + 1)] from rfl,
        filter_lt_TWG139 h j]
      exact omegaNF_zero135

theorem wcnf_TWG139 {c : Term} (h : TowC138 c) (j : Nat) :
    wcnf (reg 1) [TWG139 c (j + 1)] = ([(TWG139 c j, TM.Term.one)], zero) := by
  rw [wcnf_cons_ge (lt_TWG_reg1_139 h (j + 1))]
  show ([(wA (reg 1) (TWG139 c (j + 1)), wC (reg 1) (TWG139 c (j + 1)))], zero) = _
  rw [wA_TWG139 h j, wC_TWG139 h j]

theorem d2_TWG139 {c : Term} (h : TowC138 c) (j : Nat) :
    mulL (mulL (reg 1) (subAP (reg 1) (TWG139 c j))) TM.Term.one = TWG139 c (j + 1) := by
  rw [subAP_TWG139 c j, mulL_Om1_TWG139 h j]
  exact mulL_TWG_one139 c j

theorem plus_Om2_TWG139 {c : Term} (h : TowC138 c) :
    ∀ (j : Nat), plus (Z TM.Term.one) (TWG139 c j) = add (Z TM.Term.one) (TWG139 c j)
  | 0 => by
      show ofList (List.filter (fun a => le (phi TM.Term.one c) a) [Z TM.Term.one]
        ++ [phi TM.Term.one c, phi TM.Term.one c]) = _
      rw [show List.filter (fun a => le (phi TM.Term.one c) a) [Z TM.Term.one]
            = [Z TM.Term.one] from by
        show (match le (phi TM.Term.one c) (Z TM.Term.one) with
              | true => Z TM.Term.one
                  :: List.filter (fun a => le (phi TM.Term.one c) a) []
              | false => List.filter (fun a => le (phi TM.Term.one c) a) []) = _
        rw [le_P_Om2_139 h]
        rfl]
      rfl
  | j + 1 => by
      show ofList (List.filter (fun a => le (phi zero (TWG139 c j)) a) [Z TM.Term.one]
        ++ [phi zero (TWG139 c j)]) = _
      rw [show List.filter (fun a => le (phi zero (TWG139 c j)) a) [Z TM.Term.one]
            = [Z TM.Term.one] from by
        show (match le (phi zero (TWG139 c j)) (Z TM.Term.one) with
              | true => Z TM.Term.one
                  :: List.filter (fun a => le (phi zero (TWG139 c j)) a) []
              | false => List.filter (fun a => le (phi zero (TWG139 c j)) a) []) = _
        rw [show le (phi zero (TWG139 c j)) (Z TM.Term.one) = true
              from le_TWG_Om2_139 h (j + 1)]
        rfl]
      rfl

theorem plus_P_TWG139 {c : Term} (j : Nat) :
    plus (phi TM.Term.one c) (TWG139 c (j + 1)) = TWG139 c (j + 1) := by
  show ofList (List.filter (fun a => le (phi zero (TWG139 c j)) a) [phi TM.Term.one c]
    ++ [phi zero (TWG139 c j)]) = _
  rw [show List.filter (fun a => le (phi zero (TWG139 c j)) a) [phi TM.Term.one c]
        = [] from by
    show (match le (phi zero (TWG139 c j)) (phi TM.Term.one c) with
          | true => phi TM.Term.one c
              :: List.filter (fun a => le (phi zero (TWG139 c j)) a) []
          | false => List.filter (fun a => le (phi zero (TWG139 c j)) a) []) = []
    rw [show le (phi zero (TWG139 c j)) (phi TM.Term.one c) = false
          from le_TWG_P139 c (j + 1)]
    rfl]
  rfl

/-- `ψ₁` の畳み込み — 桁が `Ω₂` 一つ、余りが塔。塔が一段伸びる。 -/
theorem collapse1_Om2_TWG139 {c : Term} (h : TowC138 c) (j : Nat)
    (hbase : ([((TM.Term.one : Term), TM.Term.one)].foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 2) (baseOf 1))) = ((none : Option Term), some (phi TM.Term.one c))) :
    collapse 1 (add (Z TM.Term.one) (TWG139 c (j + 1))) = TWG139 c (j + 2) := by
  rw [collapse_eq 1 (add (Z TM.Term.one) (TWG139 c (j + 1))),
    show toList (add (Z TM.Term.one) (TWG139 c (j + 1)))
      = [Z TM.Term.one, TWG139 c (j + 1)] from rfl,
    wcnf_cons_ge (show lt (Z TM.Term.one) (reg 2) = false from lt_irrefl _),
    wcnf_cons_lt (lt_TWG_reg2_139 h (j + 1))]
  show omegaNF (plus (reg 1) (plus
    (([(wA (reg 2) (Z TM.Term.one), wC (reg 2) (Z TM.Term.one))].foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 2) (baseOf 1))).2.getD zero)
    (ofList [TWG139 c (j + 1)]))) = _
  rw [show wA (reg 2) (Z TM.Term.one) = TM.Term.one from rfl,
    show wC (reg 2) (Z TM.Term.one) = TM.Term.one from rfl, hbase]
  show omegaNF (plus (reg 1) (plus (phi TM.Term.one c) (TWG139 c (j + 1)))) = _
  rw [plus_P_TWG139 j, plus_Om1_TWG139 h (j + 1)]
  exact omegaNF_TWG139 c (j + 1)

theorem wcnf_Om2TWG139 {c : Term} (h : TowC138 c) (j : Nat) :
    wcnf (reg 1) [Z TM.Term.one, TWG139 c (j + 1)]
      = ([(Z TM.Term.one, TM.Term.one), (TWG139 c j, TM.Term.one)], zero) := by
  rw [wcnf_cons_ge lt_Om2_reg1_139, wcnf_TWG139 h j]
  show (if (wA (reg 1) (Z TM.Term.one) == TWG139 c j) = true
        then ((wA (reg 1) (Z TM.Term.one),
               plus (wC (reg 1) (Z TM.Term.one)) TM.Term.one) :: [], zero)
        else ((wA (reg 1) (Z TM.Term.one), wC (reg 1) (Z TM.Term.one))
              :: (TWG139 c j, TM.Term.one) :: [], zero)) = _
  rw [show wA (reg 1) (Z TM.Term.one) = Z TM.Term.one from rfl,
    show wC (reg 1) (Z TM.Term.one) = TM.Term.one from rfl,
    if_neg (by rw [beq_Om2_TWG139 c j]; exact Bool.noConfusion)]

/-- `ψ₀` の畳み込み — 桁が二つ、どちらも強臨界。 -/
theorem collapse0_Om2_TWG139 {c : Term} (h : TowC138 c) (j : Nat) :
    collapse 0 (add (Z TM.Term.one) (TWG139 c (j + 1)))
      = psi (Z zero) (add (Z TM.Term.one) (TWG139 c (j + 1))) := by
  rw [collapse_eq 0 (add (Z TM.Term.one) (TWG139 c (j + 1))),
    show toList (add (Z TM.Term.one) (TWG139 c (j + 1)))
      = [Z TM.Term.one, TWG139 c (j + 1)] from rfl,
    wcnf_Om2TWG139 h j]
  show omegaNF (plus (reg 0) (plus
    (((stepF (reg 1) (baseOf 0))
        ((stepF (reg 1) (baseOf 0)) ((none : Option Term), (none : Option Term))
          (Z TM.Term.one, TM.Term.one)) (TWG139 c j, TM.Term.one)).2.getD zero) zero)) = _
  rw [stepF_sc139 (show le (reg 1) (Z TM.Term.one) = true from le_reg1_Om2_139),
    idx1_Om2_139, stepF_sc2_139 (le_reg1_TWG139 h j), d2_TWG139 h j,
    plus_Om2_TWG139 h (j + 1)]
  show omegaNF (plus (reg 0) (plus
    (psi (Z zero) (add (Z TM.Term.one) (TWG139 c (j + 1)))) zero)) = _
  rw [show plus (reg 0) (plus
        (psi (Z zero) (add (Z TM.Term.one) (TWG139 c (j + 1)))) zero)
      = psi (Z zero) (add (Z TM.Term.one) (TWG139 c (j + 1))) from rfl]
  exact omegaNF_psi139 _ _

/-! ### §139.14 行 52 -/

theorem towC_W139 : TowC138 (Z zero) where
  cOm := fun f => ltF_irrefl f (Z zero)
  OmP := by
    intro f hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rfl
  POm2 := fun f hf => ltF_W_Om2_139 f (by omega)
  gap0 := rfl

def Z52139 : Nat → B
  | 0 => q139
  | k + 1 => .nd 1 q139 (Z52139 k)

def A52139 : Nat → BT
  | 0 => BT.D 2 BT.zero
  | k + 1 => BT.sum (BT.D 2 BT.zero) (BT.D 1 (A52139 k))

theorem Z52_shape139 : ∀ (k : Nat), ∃ v r a, Z52139 k = .nd v r a
  | 0 => ⟨2, .nil, .nil, rfl⟩
  | k + 1 => ⟨1, q139, Z52139 k, rfl⟩

theorem iterD_Z52139 : ∀ (k : Nat),
    iterD 1 (.nd 2 q139 .nil) k = .nd 1 .nil (Z52139 k)
  | 0 => rfl
  | k + 1 => by
      show B.nd 1 .nil (appB q139 (iterD 1 (.nd 2 q139 .nil) k)) = _
      rw [iterD_Z52139 k]
      rfl

theorem fsB_i52139 (k : Nat) :
    fsB i52139 k = .nd 0 .nil (.nd 1 .nil (Z52139 k)) := by
  show B.nd 0 .nil (appB .nil (iterD 1 (.nd 2 q139 .nil) k)) = _
  rw [appB_nil, iterD_Z52139 k]

theorem bArg1_Z52139 : ∀ (k : Nat), bArg 1 (Z52139 k) = A52139 k
  | 0 => rfl
  | k + 1 => by
      obtain ⟨v, r, a, hva⟩ := Z52_shape139 k
      have hb : bArg 1 (B.nd 1 q139 (Z52139 k))
          = BT.sum (BT.D 2 BT.zero) (BT.D 1 (bArg 1 (Z52139 k))) := by
        rw [hva]; rfl
      show bArg 1 (B.nd 1 q139 (Z52139 k)) = _
      rw [hb, bArg1_Z52139 k]
      rfl

theorem bVal_fs_i52139 (k : Nat) :
    bVal (fsB i52139 (k + 1)) = BT.D 0 (A52139 (k + 2)) := by
  rw [fsB_i52139 (k + 1)]
  obtain ⟨v, r, a, hva⟩ := Z52_shape139 k
  have hb : bVal (B.nd 0 .nil (.nd 1 .nil (Z52139 (k + 1))))
      = BT.D 0 (BT.sum (BT.D 2 BT.zero)
          (BT.D 1 (BT.sum (BT.D 2 BT.zero) (BT.D 1 (bArg 1 (Z52139 k)))))) := by
    show bVal (B.nd 0 .nil (.nd 1 .nil (.nd 1 q139 (Z52139 k)))) = _
    rw [hva]; rfl
  rw [hb, bArg1_Z52139 k]
  rfl

theorem base52_139 : ([((TM.Term.one : Term), TM.Term.one)].foldl
    (init := ((none : Option Term), (none : Option Term)))
    (stepF (reg 2) (baseOf 1))) = ((none : Option Term), some (phi TM.Term.one (Z zero))) :=
  rfl

theorem dict_A52139 : ∀ (k : Nat),
    dict (A52139 (k + 2)) = add (Z TM.Term.one) (TWG139 (Z zero) (k + 1))
  | 0 => rfl
  | k + 1 => by
      show plus (dict (BT.D 2 BT.zero)) (collapse 1 (dict (A52139 (k + 2)))) = _
      rw [dict_Om2bt139, dict_A52139 k,
        collapse1_Om2_TWG139 towC_W139 k base52_139]
      exact plus_Om2_TWG139 towC_W139 (k + 2)

/-- **行 52 の基本列の値、閉じた形。** -/
theorem vOf_fs_i52139 (k : Nat) :
    vOf (fsB i52139 (k + 1))
      = psi (Z zero) (add (Z TM.Term.one) (TWG139 (Z zero) (k + 1))) := by
  have h1 : vOf (fsB i52139 (k + 1))
      = plus TM.Term.one (dict (bVal (fsB i52139 (k + 1)))) := by
    rw [fsB_i52139 (k + 1)]
    exact vOf_nd139 _ _ _
  rw [h1, bVal_fs_i52139 k]
  show plus TM.Term.one (collapse 0 (dict (A52139 (k + 2)))) = _
  rw [dict_A52139 k, collapse0_Om2_TWG139 towC_W139 k]
  exact plus_one_psi139 _ _

/-- 行 52 の証人。`ψ_Ω(Ω₂ ⊕ φ̄(1, φ̄(1,Ω₁)))`。 -/
def s52139 : Term :=
  psi (Z zero) (add (Z TM.Term.one) (phi TM.Term.one (phi TM.Term.one (Z zero))))

theorem inT_s52139 : inT s52139 = true := rfl
theorem lt_s52_i52139 : lt s52139 (vOf i52139) = true := rfl

theorem lt_fs_s52139 : ∀ (n : Nat), lt (vOf (fsB i52139 n)) s52139 = true
  | 0 => rfl
  | k + 1 => by
      rw [vOf_fs_i52139 k]
      show lt (psi (Z zero) (add (Z TM.Term.one) (TWG139 (Z zero) (k + 1))))
        (psi (Z zero) (add (Z TM.Term.one) (phi TM.Term.one (phi TM.Term.one (Z zero)))))
        = true
      rw [lt_psi_same, lt_add_same139]
      exact lt_TWG_gap139 towC_W139 (k + 1)

/-- **行 52 の主定理。仮説なし。** -/
theorem row52_gap139 :
    (Rows.rows.find? fun r => r.m == matB i52139 0).map (·.t) = some (vOf i52139)
  ∧ inT s52139 = true
  ∧ lt s52139 (vOf i52139) = true
  ∧ ∀ n, Trans.Recal.oR (BMS.expand (matB i52139 0) n) = some (vOf (fsB i52139 n))
       ∧ lt (vOf (fsB i52139 n)) s52139 = true :=
  ⟨rowval52_139, inT_s52139, lt_s52_i52139, fun n =>
    ⟨oR_expand139 i52139 topOKB_i52139 (by intro hc; exact B.noConfusion hc) nfB_i52139 n,
     lt_fs_s52139 n⟩⟩


/-! ### §139.15 行 53 — 接頭が `Ω₂ ⊕ Ω₂`、塔の底が `φ̄(1, Ω₁ ⊕ 1)` -/

/-- 段 2 の葉を二つ並べたもの。行列では `(d,2)(d,2)`。 -/
def qq139 : B := .nd 2 q139 .nil

/-- 行 53 の塔の底の添字。 -/
def c2139 : Term := add (Z zero) TM.Term.one

theorem towC_W2139 : TowC138 c2139 where
  cOm := by
    intro f
    cases f with
    | zero => rfl
    | succ g =>
        show ltF g (Z zero) (Z zero) = false
        exact ltF_irrefl g _
  OmP := by
    intro f hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    show (((Z zero : Term) == TM.Term.one) || ((Z zero : Term) == c2139)
          || ltF g (Z zero) TM.Term.one || ltF g (Z zero) c2139) = true
    rw [show ltF g (Z zero) c2139 = true from by
      obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      rfl]
    exact Bool.or_true _
  POm2 := by
    intro f hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    show (ltF g TM.Term.one (Z TM.Term.one) && ltF g c2139 (Z TM.Term.one)) = true
    rw [ltF_one_Z139 (show (TM.Term.one : Term) ≠ zero from by
          intro hc; exact Term.noConfusion hc) g (by omega),
      show ltF g c2139 (Z TM.Term.one) = true from by
        obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
        show ltF g' (Z zero) (Z TM.Term.one) = true
        exact ltF_Om_Z139 rfl (show (TM.Term.one : Term) ≠ zero from by
          intro hc; exact Term.noConfusion hc) g' (by omega)]
    rfl
  gap0 := rfl

def Z53139 : Nat → B
  | 0 => qq139
  | k + 1 => .nd 1 qq139 (Z53139 k)

def A53139 : Nat → BT
  | 0 => BT.sum (BT.D 2 BT.zero) (BT.D 2 BT.zero)
  | k + 1 => BT.sum (BT.D 2 BT.zero) (BT.sum (BT.D 2 BT.zero) (BT.D 1 (A53139 k)))

theorem Z53_shape139 : ∀ (k : Nat), ∃ v r a, Z53139 k = .nd v r a
  | 0 => ⟨2, q139, .nil, rfl⟩
  | k + 1 => ⟨1, qq139, Z53139 k, rfl⟩

theorem iterD_Z53139 : ∀ (k : Nat),
    iterD 1 (.nd 2 qq139 .nil) k = .nd 1 .nil (Z53139 k)
  | 0 => rfl
  | k + 1 => by
      show B.nd 1 .nil (appB qq139 (iterD 1 (.nd 2 qq139 .nil) k)) = _
      rw [iterD_Z53139 k]
      rfl

theorem fsB_i53139 (k : Nat) :
    fsB i53139 k = .nd 0 .nil (.nd 1 .nil (Z53139 k)) := by
  show B.nd 0 .nil (appB .nil (iterD 1 (.nd 2 qq139 .nil) k)) = _
  rw [appB_nil, iterD_Z53139 k]

theorem bArg1_Z53139 : ∀ (k : Nat), bArg 1 (Z53139 k) = A53139 k
  | 0 => rfl
  | k + 1 => by
      obtain ⟨v, r, a, hva⟩ := Z53_shape139 k
      have hb : bArg 1 (B.nd 1 qq139 (Z53139 k))
          = BT.sum (BT.D 2 BT.zero)
              (BT.sum (BT.D 2 BT.zero) (BT.D 1 (bArg 1 (Z53139 k)))) := by
        rw [hva]; rfl
      show bArg 1 (B.nd 1 qq139 (Z53139 k)) = _
      rw [hb, bArg1_Z53139 k]
      rfl

theorem bVal_fs_i53139 (k : Nat) :
    bVal (fsB i53139 (k + 1)) = BT.D 0 (A53139 (k + 2)) := by
  rw [fsB_i53139 (k + 1)]
  obtain ⟨v, r, a, hva⟩ := Z53_shape139 k
  have hb : bVal (B.nd 0 .nil (.nd 1 .nil (Z53139 (k + 1))))
      = BT.D 0 (BT.sum (BT.D 2 BT.zero) (BT.sum (BT.D 2 BT.zero)
          (BT.D 1 (BT.sum (BT.D 2 BT.zero) (BT.sum (BT.D 2 BT.zero)
            (BT.D 1 (bArg 1 (Z53139 k)))))))) := by
    show bVal (B.nd 0 .nil (.nd 1 .nil (.nd 1 qq139 (Z53139 k)))) = _
    rw [hva]; rfl
  rw [hb, bArg1_Z53139 k]
  rfl

theorem plus_Om2_Om2_TWG139 (c : Term) : ∀ (j : Nat),
    plus (Z TM.Term.one) (add (Z TM.Term.one) (TWG139 c j))
      = add (Z TM.Term.one) (add (Z TM.Term.one) (TWG139 c j))
  | 0 => rfl
  | _ + 1 => rfl

theorem plus_Om2Om2_TWG139 {c : Term} (h : TowC138 c) (j : Nat) :
    plus (add (Z TM.Term.one) (Z TM.Term.one)) (TWG139 c (j + 1))
      = add (Z TM.Term.one) (add (Z TM.Term.one) (TWG139 c (j + 1))) := by
  show ofList (List.filter (fun a => le (phi zero (TWG139 c j)) a)
    [Z TM.Term.one, Z TM.Term.one] ++ [phi zero (TWG139 c j)]) = _
  rw [show List.filter (fun a => le (phi zero (TWG139 c j)) a)
        [Z TM.Term.one, Z TM.Term.one] = [Z TM.Term.one, Z TM.Term.one] from by
    show (match le (phi zero (TWG139 c j)) (Z TM.Term.one) with
          | true => Z TM.Term.one :: List.filter
              (fun a => le (phi zero (TWG139 c j)) a) [Z TM.Term.one]
          | false => List.filter
              (fun a => le (phi zero (TWG139 c j)) a) [Z TM.Term.one]) = _
    rw [show le (phi zero (TWG139 c j)) (Z TM.Term.one) = true
          from le_TWG_Om2_139 h (j + 1)]
    show (Z TM.Term.one : Term) :: (match le (phi zero (TWG139 c j)) (Z TM.Term.one) with
          | true => Z TM.Term.one :: List.filter (fun a => le (phi zero (TWG139 c j)) a) []
          | false => List.filter (fun a => le (phi zero (TWG139 c j)) a) []) = _
    rw [show le (phi zero (TWG139 c j)) (Z TM.Term.one) = true
          from le_TWG_Om2_139 h (j + 1)]
    rfl]
  rfl

theorem wcnf2_TWG139 {c : Term} (h : TowC138 c) (j : Nat) :
    wcnf (reg 2) [TWG139 c (j + 1)] = ([], TWG139 c (j + 1)) := by
  rw [wcnf_cons_lt (lt_TWG_reg2_139 h (j + 1))]
  rfl

theorem wcnf2_Om2_TWG139 {c : Term} (h : TowC138 c) (j : Nat) :
    wcnf (reg 2) [Z TM.Term.one, TWG139 c (j + 1)]
      = ([(TM.Term.one, TM.Term.one)], TWG139 c (j + 1)) := by
  rw [wcnf_cons_ge (show lt (Z TM.Term.one) (reg 2) = false from lt_irrefl _),
    wcnf2_TWG139 h j]
  show ([(wA (reg 2) (Z TM.Term.one), wC (reg 2) (Z TM.Term.one))],
    TWG139 c (j + 1)) = _
  rw [show wA (reg 2) (Z TM.Term.one) = TM.Term.one from rfl,
    show wC (reg 2) (Z TM.Term.one) = TM.Term.one from rfl]

theorem wcnf2_Om2Om2_TWG139 {c : Term} (h : TowC138 c) (j : Nat) :
    wcnf (reg 2) [Z TM.Term.one, Z TM.Term.one, TWG139 c (j + 1)]
      = ([(TM.Term.one, add TM.Term.one TM.Term.one)], TWG139 c (j + 1)) := by
  rw [wcnf_cons_ge (show lt (Z TM.Term.one) (reg 2) = false from lt_irrefl _),
    wcnf2_Om2_TWG139 h j]
  show (if (wA (reg 2) (Z TM.Term.one) == TM.Term.one) = true
        then ((wA (reg 2) (Z TM.Term.one),
               plus (wC (reg 2) (Z TM.Term.one)) TM.Term.one) :: [], TWG139 c (j + 1))
        else ((wA (reg 2) (Z TM.Term.one), wC (reg 2) (Z TM.Term.one))
              :: (TM.Term.one, TM.Term.one) :: [], TWG139 c (j + 1))) = _
  rw [show wA (reg 2) (Z TM.Term.one) = TM.Term.one from rfl,
    show wC (reg 2) (Z TM.Term.one) = TM.Term.one from rfl, if_pos (by rfl)]
  rfl

/-- `ψ₁` の畳み込み — 桁が `Ω₂` 二つ、余りが塔。 -/
theorem collapse1_Om2Om2_TWG139 {c : Term} (h : TowC138 c) (j : Nat)
    (hbase : ([((TM.Term.one : Term), add TM.Term.one TM.Term.one)].foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg 2) (baseOf 1))) = ((none : Option Term), some (phi TM.Term.one c))) :
    collapse 1 (add (Z TM.Term.one) (add (Z TM.Term.one) (TWG139 c (j + 1))))
      = TWG139 c (j + 2) := by
  rw [collapse_eq 1 (add (Z TM.Term.one) (add (Z TM.Term.one) (TWG139 c (j + 1)))),
    show toList (add (Z TM.Term.one) (add (Z TM.Term.one) (TWG139 c (j + 1))))
      = [Z TM.Term.one, Z TM.Term.one, TWG139 c (j + 1)] from rfl,
    wcnf2_Om2Om2_TWG139 h j, hbase]
  show omegaNF (plus (reg 1) (plus (phi TM.Term.one c) (TWG139 c (j + 1)))) = _
  rw [plus_P_TWG139 j, plus_Om1_TWG139 h (j + 1)]
  exact omegaNF_TWG139 c (j + 1)

theorem idx1_Om2Om2_139 :
    idxOf (reg 1) ((none : Option Term), (none : Option Term))
      (Z TM.Term.one, add TM.Term.one TM.Term.one)
      = add (Z TM.Term.one) (Z TM.Term.one) := rfl

theorem wcnf_Om2Om2TWG139 {c : Term} (h : TowC138 c) (j : Nat) :
    wcnf (reg 1) [Z TM.Term.one, Z TM.Term.one, TWG139 c (j + 1)]
      = ([(Z TM.Term.one, add TM.Term.one TM.Term.one), (TWG139 c j, TM.Term.one)],
         zero) := by
  rw [wcnf_cons_ge lt_Om2_reg1_139, wcnf_Om2TWG139 h j]
  show (if (wA (reg 1) (Z TM.Term.one) == Z TM.Term.one) = true
        then ((wA (reg 1) (Z TM.Term.one),
               plus (wC (reg 1) (Z TM.Term.one)) TM.Term.one)
              :: [(TWG139 c j, TM.Term.one)], zero)
        else ((wA (reg 1) (Z TM.Term.one), wC (reg 1) (Z TM.Term.one))
              :: (Z TM.Term.one, TM.Term.one) :: [(TWG139 c j, TM.Term.one)], zero)) = _
  rw [show wA (reg 1) (Z TM.Term.one) = Z TM.Term.one from rfl,
    show wC (reg 1) (Z TM.Term.one) = TM.Term.one from rfl, if_pos (by rfl)]
  rfl

/-- `ψ₀` の畳み込み — 桁が二つ、先頭の係数が 2。 -/
theorem collapse0_Om2Om2_TWG139 {c : Term} (h : TowC138 c) (j : Nat) :
    collapse 0 (add (Z TM.Term.one) (add (Z TM.Term.one) (TWG139 c (j + 1))))
      = psi (Z zero) (add (Z TM.Term.one) (add (Z TM.Term.one) (TWG139 c (j + 1)))) := by
  rw [collapse_eq 0 (add (Z TM.Term.one) (add (Z TM.Term.one) (TWG139 c (j + 1)))),
    show toList (add (Z TM.Term.one) (add (Z TM.Term.one) (TWG139 c (j + 1))))
      = [Z TM.Term.one, Z TM.Term.one, TWG139 c (j + 1)] from rfl,
    wcnf_Om2Om2TWG139 h j]
  show omegaNF (plus (reg 0) (plus
    (((stepF (reg 1) (baseOf 0))
        ((stepF (reg 1) (baseOf 0)) ((none : Option Term), (none : Option Term))
          (Z TM.Term.one, add TM.Term.one TM.Term.one))
        (TWG139 c j, TM.Term.one)).2.getD zero) zero)) = _
  rw [stepF_sc139 (show le (reg 1) (Z TM.Term.one) = true from le_reg1_Om2_139),
    idx1_Om2Om2_139, stepF_sc2_139 (le_reg1_TWG139 h j), d2_TWG139 h j,
    plus_Om2Om2_TWG139 h j]
  show omegaNF (plus (reg 0) (plus
    (psi (Z zero) (add (Z TM.Term.one) (add (Z TM.Term.one) (TWG139 c (j + 1))))) zero)) = _
  rw [show plus (reg 0) (plus
        (psi (Z zero) (add (Z TM.Term.one) (add (Z TM.Term.one) (TWG139 c (j + 1))))) zero)
      = psi (Z zero) (add (Z TM.Term.one) (add (Z TM.Term.one) (TWG139 c (j + 1))))
      from rfl]
  exact omegaNF_psi139 _ _

theorem base53_139 : ([((TM.Term.one : Term), add TM.Term.one TM.Term.one)].foldl
    (init := ((none : Option Term), (none : Option Term)))
    (stepF (reg 2) (baseOf 1))) = ((none : Option Term), some (phi TM.Term.one c2139)) :=
  rfl

theorem dict_A53139 : ∀ (k : Nat),
    dict (A53139 (k + 2))
      = add (Z TM.Term.one) (add (Z TM.Term.one) (TWG139 c2139 (k + 1)))
  | 0 => rfl
  | k + 1 => by
      show plus (dict (BT.D 2 BT.zero))
        (plus (dict (BT.D 2 BT.zero)) (collapse 1 (dict (A53139 (k + 2))))) = _
      rw [dict_Om2bt139, dict_A53139 k,
        collapse1_Om2Om2_TWG139 towC_W2139 k base53_139,
        plus_Om2_TWG139 towC_W2139 (k + 2),
        plus_Om2_Om2_TWG139 c2139 (k + 2)]

/-- **行 53 の基本列の値、閉じた形。** -/
theorem vOf_fs_i53139 (k : Nat) :
    vOf (fsB i53139 (k + 1))
      = psi (Z zero) (add (Z TM.Term.one)
          (add (Z TM.Term.one) (TWG139 c2139 (k + 1)))) := by
  have h1 : vOf (fsB i53139 (k + 1))
      = plus TM.Term.one (dict (bVal (fsB i53139 (k + 1)))) := by
    rw [fsB_i53139 (k + 1)]
    exact vOf_nd139 _ _ _
  rw [h1, bVal_fs_i53139 k]
  show plus TM.Term.one (collapse 0 (dict (A53139 (k + 2)))) = _
  rw [dict_A53139 k, collapse0_Om2Om2_TWG139 towC_W2139 k]
  exact plus_one_psi139 _ _

/-- 行 53 の証人。`ψ_Ω(Ω₂ ⊕ Ω₂ ⊕ φ̄(1, φ̄(1, Ω₁ ⊕ 1)))`。 -/
def s53139 : Term :=
  psi (Z zero) (add (Z TM.Term.one)
    (add (Z TM.Term.one) (phi TM.Term.one (phi TM.Term.one c2139))))

theorem inT_s53139 : inT s53139 = true := rfl
theorem lt_s53_i53139 : lt s53139 (vOf i53139) = true := rfl

theorem lt_fs_s53139 : ∀ (n : Nat), lt (vOf (fsB i53139 n)) s53139 = true
  | 0 => rfl
  | k + 1 => by
      rw [vOf_fs_i53139 k]
      show lt (psi (Z zero) (add (Z TM.Term.one)
              (add (Z TM.Term.one) (TWG139 c2139 (k + 1)))))
        (psi (Z zero) (add (Z TM.Term.one)
          (add (Z TM.Term.one) (phi TM.Term.one (phi TM.Term.one c2139))))) = true
      rw [lt_psi_same, lt_add_same139, lt_add_same139]
      exact lt_TWG_gap139 towC_W2139 (k + 1)

/-- **行 53 の主定理。仮説なし。** -/
theorem row53_gap139 :
    (Rows.rows.find? fun r => r.m == matB i53139 0).map (·.t) = some (vOf i53139)
  ∧ inT s53139 = true
  ∧ lt s53139 (vOf i53139) = true
  ∧ ∀ n, Trans.Recal.oR (BMS.expand (matB i53139 0) n) = some (vOf (fsB i53139 n))
       ∧ lt (vOf (fsB i53139 n)) s53139 = true :=
  ⟨rowval53_139, inT_s53139, lt_s53_i53139, fun n =>
    ⟨oR_expand139 i53139 topOKB_i53139 (by intro hc; exact B.noConfusion hc) nfB_i53139 n,
     lt_fs_s53139 n⟩⟩


/-! ### §139.16 五行まとめ

§137 が外部の独立実装で見つけた 5 行が、ここで 5 つの定理になった。どの行についても
仮説は無い。**どれも反証できなかった行は無い** — 5 行とも隙間が実際にあり、表の値は
自分の展開の値の上限より真に上にある。

証人は 5 つとも同じ一つの欠陥を指している。行 37 は `sbad = ψ_Ω(φ̄(1,Ω₁))`、
行 47・58 はその `sbad` を表の値の内側の `ψ_Ω(Ω₂)` の場所に入れたもの、
行 52・53 は `Ω₂` の桁を残したまま塔の底を `φ̄(1,Ω₁)`・`φ̄(1,Ω₁⊕1)` に取り替えたもの。
どれも「基本列が `Z 1` を降りるときに `ω` の塔になり、`Ω₂` には届かない」という
同じ現象である。

**どちら側が誤りかは、ここでも言わない。** 言えるのは、表の値とその行列の展開が
合わないこと — §69 が対角について言ったことと同じことが、5 行すべてで定理になった
ということだけ。 -/

/-- **§137 の 5 行すべてで隙間がある。仮説なし。** -/
theorem five_rows_gap139 :
    ((Rows.rows.find? fun r => r.m == matB tdiag 0).map (·.t) = some (vOf tdiag)
      ∧ inT sbad = true ∧ lt sbad (vOf tdiag) = true
      ∧ ∀ n, Trans.Recal.oR (BMS.expand (matB tdiag 0) n) = some (vOf (fsB tdiag n))
           ∧ lt (vOf (fsB tdiag n)) sbad = true)
  ∧ ((Rows.rows.find? fun r => r.m == matB i47139 0).map (·.t) = some (vOf i47139)
      ∧ inT s47139 = true ∧ lt s47139 (vOf i47139) = true
      ∧ ∀ n, Trans.Recal.oR (BMS.expand (matB i47139 0) n) = some (vOf (fsB i47139 n))
           ∧ lt (vOf (fsB i47139 n)) s47139 = true)
  ∧ ((Rows.rows.find? fun r => r.m == matB i52139 0).map (·.t) = some (vOf i52139)
      ∧ inT s52139 = true ∧ lt s52139 (vOf i52139) = true
      ∧ ∀ n, Trans.Recal.oR (BMS.expand (matB i52139 0) n) = some (vOf (fsB i52139 n))
           ∧ lt (vOf (fsB i52139 n)) s52139 = true)
  ∧ ((Rows.rows.find? fun r => r.m == matB i53139 0).map (·.t) = some (vOf i53139)
      ∧ inT s53139 = true ∧ lt s53139 (vOf i53139) = true
      ∧ ∀ n, Trans.Recal.oR (BMS.expand (matB i53139 0) n) = some (vOf (fsB i53139 n))
           ∧ lt (vOf (fsB i53139 n)) s53139 = true)
  ∧ ((Rows.rows.find? fun r => r.m == matB i58139 0).map (·.t) = some (vOf i58139)
      ∧ inT s58139 = true ∧ lt s58139 (vOf i58139) = true
      ∧ ∀ n, Trans.Recal.oR (BMS.expand (matB i58139 0) n) = some (vOf (fsB i58139 n))
           ∧ lt (vOf (fsB i58139 n)) s58139 = true) :=
  ⟨row37_gap139, row47_gap139, row52_gap139, row53_gap139, row58_gap139⟩

/-- **§69 の `Hlim` の反証、仮説なし。** `TowerVal` が定理になったので
    `not_hlimS` はもう仮説を持たない。 -/
theorem not_hlimS139 :
    ¬ (∀ (S : BMS.Matrix) (v : TM.Term), RegS S → ValS S v → BMS.kind S = BMS.Kind.lim →
      ∃ f : Nat → TM.Term, inT v = true
        ∧ (∀ n, ValS (BMS.expand S n) (f n))
        ∧ (∀ n, inT (f n) = true)
        ∧ (∀ n, lt (f n) v = true)
        ∧ (∀ n, lt (f n) (f (n + 1)) = true)
        ∧ (∀ s, inT s = true → lt s v = true → ∃ n, le s (f n) = true)) :=
  not_hlimS cofGap139


end

/-! ## §140 THE CORRECTED VALUES, NAMED — MEASURED, NOT PROVED

§139 proves each of the five published values is strictly above the supremum of its own
expansion's values.  It does not say what the value SHOULD be.  §140 records what the
external implementation says, and it names all five, including the three §137 could not.

    row 37  `ψ_Ω(Z 1)`                            →  `ψ_Ω(φ̄(1,Ω))`
    row 47  `ψ_Ω(Z 1 ⊕ φ̄(0, φ̄(1,Ω) ⊕ ψ_Ω(Z 1)))`  →  same with the inner `ψ_Ω(Z 1)` replaced
                                                      by `ψ_Ω(φ̄(1,Ω))`
    row 52  `ψ_Ω(Z 1 ⊕ Z 1)`                      →  `ψ_Ω(Z 1 ⊕ φ̄(1, Ω⊕1))`
    row 53  `ψ_Ω(Z 1 ⊕ Z 1 ⊕ Z 1)`                →  `ψ_Ω(Z 1 ⊕ Z 1 ⊕ φ̄(1, Ω⊕1⊕1))`
    row 58  `ψ_Ω(φ̄(0, Z 1 ⊕ ψ_Ω(Z 1)))`           →  same with the inner `ψ_Ω(Z 1)` replaced

**IT IS NOT A UNIFORM SUBSTITUTION, and that is the point.**  What is wrong is only the
RIGHTMOST `Z 1` that the fundamental sequence actually descends through.  BMS climbs it with
an `ω`-tower whose base is the previous level's supremum, so the index walks:
base `Ω⊕Ω` gives `ε_{Ω+1}`, base `φ̄(1,Ω)·2` gives `ε_{Ω+2}`, base `φ̄(1,Ω+1)·2` gives
`ε_{Ω+3}`.  That is why rows 37, 52, 53 take three DIFFERENT replacements rather than one.
`Z 1` summands the sequence never opens are untouched — which is exactly why rows 38-46,
48-51, 54-57 and 59 keep theirs and are healthy.

**THE BRACKET IS REAL.**  For each row the external test was run against 6-8 candidates and
exactly one passed: one notch down fails "every step below `V`", one notch up fails "the
steps reach `fund(V,·)`".  The harness reproduces §137 exactly when run against the published
column — `54 healthy, 5 too big`, the same five rows — so it is calibrated.

**TWO MORE ROWS ARE IMPLICATED AND THE TEST IS BLIND TO THEM.**  Rows 38 and 39 carry
`ψ_Ω(Z 1)` inside a `φ̄`, and if row 37's value changes so must theirs; but their own
fundamental sequences never descend the `Z 1`, so the test says "healthy" for both the old
and the new value.  They are recorded here and NOT marked in the table, because nothing
measured them wrong.

WHAT IS PROVED BELOW is only the order relation: each candidate is a term of 𝔗(M) and lies
strictly below the published value.  That is `rfl`, and it is all that belongs in Lean until
someone proves a supremum.  **No value is changed.** -/

section
open Trans.Recal
open Trans.Dict (BT dict reg collapse)
open TM TM.Term
open Evidence.WF

/-- 外部が名指した値。**測定であって証明ではない。** -/
def corr37_140 : Term := psi (Z zero) (phi (phi zero zero) (Z zero))
def corr52_140 : Term :=
  psi (Z zero) (add (Z (phi zero zero))
    (phi (phi zero zero) (add (Z zero) (phi zero zero))))
def corr53_140 : Term :=
  psi (Z zero) (add (Z (phi zero zero)) (add (Z (phi zero zero))
    (phi (phi zero zero) (add (Z zero) (add (phi zero zero) (phi zero zero))))))
def corr47_140 : Term :=
  psi (Z zero) (add (Z (phi zero zero))
    (phi zero (add (phi (phi zero zero) (Z zero)) corr37_140)))
def corr58_140 : Term :=
  psi (Z zero) (phi zero (add (Z (phi zero zero)) corr37_140))

/-! 行 37 の候補は §69 の `sbad` そのもの。 -/
theorem corr37_is_sbad140 : corr37_140 = sbad := rfl

/-! 五つとも 𝔗(M) の項で、掲載値より真に下にある。ここまでが `rfl` で言えること。 -/

#guard inT corr37_140 && inT corr47_140 && inT corr52_140 && inT corr53_140 && inT corr58_140

#guard lt corr37_140 (psi (Z zero) (Z (phi zero zero)))
#guard lt corr52_140 (psi (Z zero) (add (Z (phi zero zero)) (Z (phi zero zero))))
#guard lt corr53_140 (psi (Z zero) (add (Z (phi zero zero))
         (add (Z (phi zero zero)) (Z (phi zero zero)))))

/-! 表の値がその行のものであることの確認 (読み違いではない)。 -/
#guard (Rows.rows.find? fun r => r.m == [[0,0],[1,1],[2,2],[2,2]]).map (·.t)
       == some (psi (Z zero) (add (Z (phi zero zero)) (Z (phi zero zero))))

end

/-! ## §141  IS THE DEFECT IN `oR`, OR IN `TM/FS.lean`?  BOTH, AND THEY ARE
             DIFFERENT DEFECTS — the two sequences at `ψ_Ω(Z 1)` do not even agree
             with each other.

§137 marked five published rows because `oR` of the expansion is not cofinal in the
external reading of the row's value, and named `Z 1` as the common step.  It did not ask
what `TM/FS.lean` — this repository's OWN fundamental sequences on the 𝔗(M) side — says
at that step.  §138c asks it.

WHAT `TM/FS.lean` SAYS.  `fsN (ψ_Ω(Z 1)) n` enters the `psi` / `.isLim` diagonalisation
(`cofT (Z 1) = Z 1`, not `ω`, and not below `κ = Ω`), and there `fsT (Z d) s = s` — the
"regular: κ[s] = s" clause — feeds the PREVIOUS term back as the index:

    fsN (ψ_Ω(Z 1)) 0     = ψ_Ω(0)                    = Γ₀
    fsN (ψ_Ω(Z 1)) (n+1) = ψ_Ω(fsN (ψ_Ω(Z 1)) n)

i.e. the ψ_Ω-TOWER.  The index it feeds back is a ψ_Ω-value.  That is right exactly when
`cof α = κ`; here `cof α = Z 1 > κ`, and `fsN` has no clause that produces a ψ_{Z 1}-value.
The visible consequence is `fsN_agree138`: **`fsN` returns the same sequence for
`ψ_Ω(Z 1)` and for `ψ_Ω(Ω)`**, two terms this repository's own order separates.

THE THREE SEQUENCES AT ROW 37, TERM BY TERM (the first two proved here, the third measured).

  (a) `TM/FS.lean`      ψ_Ω(0), ψ_Ω(ψ_Ω(0)), ψ_Ω(ψ_Ω(ψ_Ω(0))), …        bounded by ψ_Ω(Ω)
  (b) `oR ∘ BMS.expand` ε₀, ζ₀, Γ₀, ψ_Ω(φ̄0³(Ω⊕Ω)), ψ_Ω(φ̄0⁴(Ω⊕Ω)), …   bounded by ψ_Ω(φ̄(1,Ω))
  (c) external `fund`   ψ^W(ψ^I(0)), ψ^W(ψ^I(ψ^I(0))), …                 climbs to ψ^W(I)

(a) is not (b): `lt_wt_psiTW138` puts `ψ_Ω(Ω)` strictly BELOW every member of (b)'s tower,
and `lt_fsN_wt138` puts every member of (a) strictly below `ψ_Ω(Ω)`.  So `oR` and `fsN` are
NOT "consistent with each other and wrong together" — one change cannot repair both.

(a) is the external's answer for the WRONG TERM.  Measured with `scripts/padicbot-ref.js`
against naruyoko's `padicBotRathjen`, under the dictionary that file fixes
(`Ω = Z 0 ↔ W`, `Z 1 ↔ chi^{M}_{0}(0) = I`):

    fund(ψ^W(W), n)  = ψ^W(ψ^W(…ψ^W(0)…))   ← exactly (a), one index along
    fund(ψ^W(I), n)  = ψ^W(ψ^I(…ψ^I(0)…))   ← (c)

The external distinguishes the two terms; `fsN` does not.  Where the external and `fsN` are
looking at the SAME term they agree: at `sbad = ψ_Ω(φ̄(1,Ω))`, the value the external names
for row 37, `fund(sbad, n) = ψ^W(φ^0_0…(W+1))` is `fsN sbad (n+1)` term for term.

WHERE EACH DEFECT SITS.

  `TM/FS.lean`  the `psi` / `.isLim` diagonalisation when `cofT α ≠ κ`.  Unconditionally
                NOT cofinal at `ψ_Ω(Z 1)`: `ψ_Ω(Ω)` is `inT`, is strictly below the target
                (`lt_wt_zt138`), and is strictly above every member (`le_wt_fsN138`).
                This is the §69 gap shape, proved here with no hypothesis and with no
                `TowerVal`.

  `oR`          at the five matrices themselves.  On the EXPANSIONS `oR` is fine — its
                values are the φ̄0-tower over `Ω⊕Ω` (measured below; the same closed form
                `Rows/G4.lean` proves for all `n` as `oR_M`, and the same one §69 measures
                as `TowerVal`), whose supremum is `ψ_Ω(φ̄(1,Ω)) = sbad`, which is what the
                external names for row 37.  It is the value AT the matrix, `ψ_Ω(Z 1)`,
                that is too big.

WHAT A REPAIR COSTS.  `diagReach138` walks only the branches `fsN` actually takes and asks
whether the diagonalisation is ever asked to descend a regular strictly above `κ`.  Over
all 60 rows of `Rows.rows` it fires on EXACTLY §137's five, and on none of those five does
the expansion ride `fsN` at any uniform shift.  44 of the 60 rows do ride `fsN`; repairing
the clause touches none of them.  **No row's E3 evidence depends on the `Z 1` behaviour of
`fs`.**  Row 37's own E3 mark (`Rows/G4.lean`) is a closed form of the EXPANSION values,
not a statement about `fsN`, and `Rows/Selected.lean` already records row 37 as one of the
six rows that "do not ride `fsN`".

WHAT IS PROOF AND WHAT IS EVIDENCE.  Proved: the closed form of `fsN` at `ψ_Ω(Z 1)`, that
it coincides with `fsN` at `ψ_Ω(Ω)`, and the gap.  Measured (`#guard`, and `node` for the
external): `oR`'s tower on the expansions, the row scan, and the external's `fund`.  NOT
claimed: which of the two sides of the correspondence carries the "true" ordinal for the
matrix `(0,0)(1,1)(2,2)` — §137 says plainly that an independent implementation cannot
decide that, and nothing here changes it.
-/

section
open TM TM.Term

/-! ## §141c.1 THE CLOSED FORM OF `fsN` AT `ψ_Ω(Z 1)` -/

/-- `fsN` が ψ_Ω(Z 1) に与える列の閉じた形 — ψ_Ω の塔。 -/
def gTow141 : Nat → Term
  | 0 => psi (Z zero) zero
  | n + 1 => psi (Z zero) (gTow141 n)

/-- **`fsN` の ψ_Ω(Z 1) での閉じた形。** 対角化が前の項をそのまま添字に戻すので、
    出てくるのは ψ_Ω の塔である。 -/
theorem fsN_psiZ1_141 : ∀ n : Nat, fsN (psi (Z zero) (Z TM.Term.one)) n = gTow141 n
  | 0 => by
      rw [fsN]
      rfl
  | n + 1 => by
      rw [fsN]
      simp only [show kindT (Z TM.Term.one) = KindT.isLim from rfl,
        show cofT (Z TM.Term.one) = Z TM.Term.one from rfl,
        show ((Z TM.Term.one : Term) == omega) = false from rfl,
        Bool.false_eq_true, if_false,
        show lt (Z TM.Term.one) (Z zero) = false from rfl]
      rw [fsN_psiZ1_141 n]
      rfl

/-- **同じ列が ψ_Ω(Ω) にも出る。** `fsT (Z d) s = s` は `d` を見ない。 -/
theorem fsN_psiOm_141 : ∀ n : Nat, fsN (psi (Z zero) (Z zero)) n = gTow141 n
  | 0 => by
      rw [fsN]
      rfl
  | n + 1 => by
      rw [fsN]
      simp only [show kindT (Z zero) = KindT.isLim from rfl,
        show cofT (Z zero) = Z zero from rfl,
        show ((Z zero : Term) == omega) = false from rfl,
        Bool.false_eq_true, if_false,
        show lt (Z zero) (Z zero) = false from rfl]
      rw [fsN_psiOm_141 n]
      rfl

/-- **`fsN` は ψ_Ω(Z 1) と ψ_Ω(Ω) を区別しない。** 当方の順序は両者を分ける
    (`lt_wt_zt141`) のだから、基本列が両方で正しいことはあり得ない。 -/
theorem fsN_agree141 (n : Nat) :
    fsN (psi (Z zero) (Z TM.Term.one)) n = fsN (psi (Z zero) (Z zero)) n := by
  rw [fsN_psiZ1_141 n, fsN_psiOm_141 n]

/-! ## §141c.2 隙間 — `ψ_Ω(Ω)` が列の上・値の下に入る -/

/-- ψ_Ω(x) < Ω。[R91] 2.3.8。 -/
theorem psi_lt_Om141 (x : Term) : lt (psi (Z zero) x) (Z zero) = true := by
  unfold lt
  rw [show fuelOf (psi (Z zero) x) (Z zero)
      = (2 * ((psi (Z zero) x).deg + (Z zero).deg) + 7) + 1 from by unfold fuelOf; omega,
    Evidence.WF.ltF_succ_psi_Z, if_pos]
  simp only [show ((Z zero : Term) == Z zero) = true from rfl, Bool.true_or]

/-- Ω < ψ_Ω(y) は偽。[R91] 2.3.8 の逆向き。 -/
theorem lt_Om_psi141 (y : Term) : lt (Z zero) (psi (Z zero) y) = false := by
  unfold lt
  rw [show fuelOf (Z zero) (psi (Z zero) y)
      = (2 * ((Z zero).deg + (psi (Z zero) y).deg) + 7) + 1 from by unfold fuelOf; omega,
    Evidence.WF.ltF_succ_Z_psi, if_pos]
  simp only [show ((Z zero : Term) == Z zero) = true from rfl, Bool.true_or]

/-- ψ_Ω(Ω) は ψ_Ω(ψ_Ω(y)) ではない。 -/
theorem psi_ne_psi_psi141 (y : Term) :
    ((psi (Z zero) (Z zero) : Term) == psi (Z zero) (psi (Z zero) y)) = false := by
  cases h : ((psi (Z zero) (Z zero) : Term) == psi (Z zero) (psi (Z zero) y)) with
  | false => rfl
  | true =>
      exfalso
      have he : (psi (Z zero) (Z zero) : Term) = psi (Z zero) (psi (Z zero) y) :=
        of_decide_eq_true h
      injection he with _ h2
      exact Term.noConfusion h2

/-- 塔の各項の形。 -/
theorem gTow_shape141 : ∀ n : Nat,
    ∃ y : Term, gTow141 n = psi (Z zero) y
      ∧ ((psi (Z zero) (Z zero) : Term) == psi (Z zero) y) = false
      ∧ lt (Z zero) y = false
  | 0 => ⟨zero, rfl, rfl, rfl⟩
  | n + 1 => by
      obtain ⟨y, hy, _, _⟩ := gTow_shape141 n
      refine ⟨gTow141 n, rfl, ?_, ?_⟩
      · rw [hy]; exact psi_ne_psi_psi141 y
      · rw [hy]; exact lt_Om_psi141 y

theorem lt_gTow_Om141 : ∀ n : Nat, lt (gTow141 n) (Z zero) = true
  | 0 => psi_lt_Om141 zero
  | n + 1 => psi_lt_Om141 (gTow141 n)

/-- **塔はすべて ψ_Ω(Ω) の下。** -/
theorem lt_gTow_wt141 : ∀ n : Nat, lt (gTow141 n) (psi (Z zero) (Z zero)) = true
  | 0 => by
      show lt (psi (Z zero) zero) (psi (Z zero) (Z zero)) = true
      rw [lt_psi_same]
      rfl
  | n + 1 => by
      show lt (psi (Z zero) (gTow141 n)) (psi (Z zero) (Z zero)) = true
      rw [lt_psi_same]
      exact lt_gTow_Om141 n

/-- **`TM/FS.lean` の列は ψ_Ω(Ω) を超えない。** -/
theorem lt_fsN_wt141 (n : Nat) :
    lt (fsN (psi (Z zero) (Z TM.Term.one)) n) (psi (Z zero) (Z zero)) = true := by
  rw [fsN_psiZ1_141 n]
  exact lt_gTow_wt141 n

/-- **§69 の `CofGap` と同じ形。** ψ_Ω(Ω) は列のどの項以下でもない。 -/
theorem le_wt_fsN141 (n : Nat) :
    le (psi (Z zero) (Z zero)) (fsN (psi (Z zero) (Z TM.Term.one)) n) = false := by
  obtain ⟨y, hy, hne, hlt⟩ := gTow_shape141 n
  rw [fsN_psiZ1_141 n]
  show (((psi (Z zero) (Z zero) : Term) == gTow141 n)
      || lt (psi (Z zero) (Z zero)) (gTow141 n)) = false
  rw [hy, hne, lt_psi_same, hlt]
  rfl

/-- 隙間の項は 𝔗(M) の項である。 -/
theorem inT_wt141 : inT (psi (Z zero) (Z zero)) = true := rfl

/-- **ψ_Ω(Ω) は掲載値より真に下。** [R91] 2.3.14(ii) + 2.3.15。 -/
theorem lt_wt_zt141 : lt (psi (Z zero) (Z zero)) (psi (Z zero) (Z TM.Term.one)) = true := rfl

/-- **§141c の主定理 — `TM/FS.lean` の基本列は ψ_Ω(Z 1) に共終ではない。**
    仮定なし。`ψ_Ω(Ω)` が隙間に入る。 -/
theorem fsN_not_cofinal141 :
    inT (psi (Z zero) (Z zero)) = true
      ∧ lt (psi (Z zero) (Z zero)) (psi (Z zero) (Z TM.Term.one)) = true
      ∧ ∀ n : Nat, le (psi (Z zero) (Z zero)) (fsN (psi (Z zero) (Z TM.Term.one)) n) = false :=
  ⟨inT_wt141, lt_wt_zt141, le_wt_fsN141⟩

/-! ## §141c.3 `fsN` の列 対 展開の値の列 — 両者は互いに違う -/

/-- Ω は §69 の塔 `TW` のどの段よりも下。 -/
theorem lt_Om_TW141 : ∀ j : Nat, lt (Z zero) (TW j) = true
  | 0 => rfl
  | j + 1 => by
      have hd : (Z zero).deg + (phi zero (TW j)).deg = ((TW j).deg + 3) + 1 := by
        simp only [Term.deg]
        omega
      show lt (Z zero) (phi zero (TW j)) = true
      rw [Evidence.WF.lt_eq_ltF (Z zero) (phi zero (TW j))
            ((Z zero).deg + (phi zero (TW j)).deg) (Nat.le_refl _), hd,
        ltF_succ_Z_phi135,
        ← Evidence.WF.lt_eq_ltF (Z zero) (TW j) ((TW j).deg + 3) (by simp only [Term.deg]; omega),
        lt_Om_TW141 j]
      simp

/-- **隙間の項は展開の値の塔のどの段よりも下。** つまり `fsN` の列と `oR` の列は
    同じ上限を持ち得ない — 一方を直しても他方は直らない。 -/
theorem lt_wt_psiTW141 (j : Nat) :
    lt (psi (Z zero) (Z zero)) (psi (Z zero) (TW j)) = true := by
  rw [lt_psi_same]
  exact lt_Om_TW141 j

/-! ### 測定 — `oR` の側 (§69 の `TowerVal`、`Rows/G4.lean` の `oR_M` と同じ形) -/

-- 展開の値は 3 段目から φ̄0 の塔になる。
#guard (List.range 5).all fun n =>
  Trans.oR (BMS.expand [[0,0],[1,1],[2,2]] (n+3)) == some (psi (Z zero) (TW (n+3)))

-- どの段でも `fsN` の列と一致しない。
#guard (List.range 8).all fun n =>
  !(Trans.oR (BMS.expand [[0,0],[1,1],[2,2]] n)
    == some (fsN (psi (Z zero) (Z TM.Term.one)) n))

-- 一様なずらしを 0..7 まで探しても乗らない。
#guard (List.range 8).all fun j =>
  !((List.range 4).all fun n =>
      Trans.oR (BMS.expand [[0,0],[1,1],[2,2]] n)
        == some (fsN (psi (Z zero) (Z TM.Term.one)) (n+j)))

-- 掲載値と行列の確認 — 読み違いではない (§137 と同じ検査)。
#guard (Rows.rows.find? fun r => r.m == [[0,0],[1,1],[2,2]]).map (·.t)
       == some (psi (Z zero) (Z TM.Term.one))

/-! ## §141c.4 修理の代価 — どの行の E3 が `Z 1` の節に乗っているか -/

/-- `fsN` が実際に降りる枝だけを辿り、対角化が κ より真に上の正則を降りるよう
    求められる箇所に当たるか。節ごとに `fsN` の再帰をそのまま写したもの。 -/
def diagReach141 : Term → Bool
  | add _ b => diagReach141 b
  | omg g => if kindT g == KindT.isSucc then false else diagReach141 g
  | phi a b =>
      if phiShifted a b || kindT b == KindT.isSucc then
        (match kindT a with | KindT.isLim => diagReach141 a | _ => false)
      else if kindT b == KindT.isLim then diagReach141 b
      else (match kindT a with | KindT.isLim => diagReach141 a | _ => false)
  | psi k a =>
      (match kindT a with
       | KindT.isZero =>
           (match k with
            | Z d => if kindT d == KindT.isLim then diagReach141 d else false
            | _ => false)
       | KindT.isSucc => false
       | KindT.isLim =>
           let p := cofT a
           if p == omega then diagReach141 a
           else if lt p k then false
           else !(p == k))
  | _ => false

/-- 展開が `fsN` に一様なずらしで乗るか (`Rows/Selected.lean` の `hasShift` と同じ)。 -/
def hasShift141 (r : Rows.Row) : Bool :=
  (List.range 6).any fun j =>
    (List.range 4).all fun n => Trans.oR (BMS.expand r.m n) == some (fsN r.t (n + j))

-- **欠陥の節に届く行は、表 60 行のうちちょうど §137 の 5 行。**
#guard ((Rows.rows.filter fun r => diagReach141 r.t).map (·.m)) == brokenRows137

-- **その 5 行はどれも `fsN` に乗らない** — 修理はどの行の E3 も壊さない。
#guard (Rows.rows.filter fun r => diagReach141 r.t).all fun r => !(hasShift141 r)

-- 乗る行は 60 行中 44 行ある (検査が空回りしていないこと)。
#guard (Rows.rows.filter fun r => hasShift141 r).length == 44
#guard Rows.rows.length == 60

/-! ### 対照 -/

-- 対照 1 — 健全な行 60 `(0,0)(1,1)(2,2)(3,1)` は `fsN` に乗り (`Rows/G8.lean` の
-- `oR_M` は定理)、`diagReach141` は沈黙する。
#guard (Rows.rows.filter fun r => r.m == [[0,0],[1,1],[2,2],[3,1]]).all fun r =>
  hasShift141 r && !(diagReach141 r.t)

-- 対照 2 — 添字が κ 自身なら旗は立たない。欠陥は「κ より上の正則を降りる」ことに
-- 限られており、`Z` が出ること自体ではない。
#guard !(diagReach141 (psi (Z zero) (Z zero)))
#guard diagReach141 (psi (Z zero) (Z TM.Term.one))

-- 対照 3 — `fsN` は ψ_Ω(Ω) には正しい形の列を出しており、その列こそが
-- ψ_Ω(Z 1) にも出てしまっているもの。
#guard (List.range 5).all fun n =>
  fsN (psi (Z zero) (Z TM.Term.one)) n == fsN (psi (Z zero) (Z zero)) n

-- 対照 4 — 外部が行 37 に名指した値 `sbad` では、`fsN` は Ω+1 の上の ω 塔を出し、
-- その各項は `sbad` の下にある (ψ_Ω(Z 1) で起きた破れは起きない)。
#guard (List.range 6).all fun n => lt (fsN sbad n) sbad
#guard (List.range 6).all fun n => lt (psi (Z zero) (TW n)) sbad

/-! ### 公理 — `sorryAx` も `native_decide` も無いこと -/

#print axioms fsN_psiZ1_141
#print axioms fsN_agree141
#print axioms fsN_not_cofinal141
#print axioms lt_wt_psiTW141

end
/-! ## §143 ROUTE (b) OF `plan/chi-2ary.md`, PROTOTYPED — AND WHY IT DOES NOT WORK


WHAT THIS FILE IS.  A candidate replacement for `Trans.Dict.dict`, written BESIDE it under a
new name, together with every measurement the manager asked for.  Nothing in the library is
touched; `dict`, `reg` and `collapse` are used unchanged and are the control in every count.

THE REPAIR.  `plan/chi-2ary.md` route (b): stop being compositional at the Ω hierarchy.
`dict`'s clause `dict (D u a) = collapse u (dict a)` is kept verbatim for `u ≤ 1` and REPLACED
for `u ≥ 2` by the rule `Trans/Dict.lean` §5 read off Hexirp's 41-row table,

    dictB143 (D u a)            = φ̄(u-1, Ω ⊕ sub1(ω^(dictB143 a)))          (u ≥ 2)
    dictB143 (D u a ⊕ … ⊕ D u a) = φ̄(u-1, Ω ⊕ sub1(ω^(dictB143 a)) ⊕ (m-1))  (m copies)

so `Ω₂ = D 2 0 ↦ φ̄(1,Ω) = ε_{Ω+1}` and `Ω₂·(1+k) ↦ φ̄(1, Ω⊕k)`, and `Ω₃ ↦ φ̄(2,Ω)`.  The
run-counting is the non-compositional step: it needs the Buchholz SYNTAX, which is why the
rule sits in `dict` and not in `collapse` (§5 proves it cannot sit in `collapse`).  RAW `phi`
is used, never `phiNF`, because `phiNF 1 Ω = Ω`.

WHAT CAME OUT.  At the published table the repair is clean and it delivers §140's row 37
value exactly.  One level down it is not: `ψ₁(Ω₂)` and `Ω₂` receive the SAME term, and no
choice of the threshold `reg 2` repairs that — the two available choices break in two
different ways, both shown below as theorems.  Details in the report; the short version is

    reg 2 = Z 1 (kept)      `collapse 1`'s tail branch is ω^(Ω ⊕ ·), which is the identity on
                            ε-numbers above Ω, and every new surrogate IS such an ε-number;
    reg 2 = φ̄(1,Ω)          the strongly critical branch then emits `ψ_{φ̄(1,Ω)}(·)`, and
                            [Rathjen, 1991] 2.1(vi) requires the subscript to be in
                            R = {Zα}.  `isR (φ̄(1,Ω)) = false`, so the value is not a term
                            of 𝔗(M) at all (4164 of 11577 standard terms).

`sorry` and `native_decide` do not occur.  Everything below is either a `#guard`/`decide`
computation (marked 測定 where it is a count) or a `rfl` theorem.
-/

open TM TM.Term
open Trans.Dict (BT dict collapse reg sub1)

/-! ### §143.1 The repaired dictionary -/

/-- 成分列の連なりを数える (同じ `D u a` が何個並ぶか)。 -/
def rle143 : List BT → List (BT × Nat)
  | [] => []
  | c :: rest =>
    match rle143 rest with
    | (d, n) :: more => if c == d then (d, n+1) :: more else (c,1) :: (d,n) :: more
    | [] => [(c,1)]

/-- `Trans.Dict.reg` の対照版。`Ω₂` を `Z 1` ではなく `φ̄(1,Ω)` に送る。
    **これは反例のために置いてある**。§6 が 𝔗(M) の項でなくなることを示す。 -/
def regB143 : Nat → Term
  | 0 => zero
  | 1 => Z zero
  | u + 2 => phi (TM.Term.ofNat (u+1)) (Z zero)

/-- `Trans.Dict.collapse` の写し。違いは `reg` が引数 `rg` になっていることだけで、
    `rg = Trans.Dict.reg` を入れれば `collapse` と同じ関数である (§2 で測る)。 -/
def collV143 (rg : Nat → Term) (u : Nat) (x : Term) : Term :=
  let w := rg (u + 1)
  let b := rg u
  let base : Term := if u == 0 then zero else plus b TM.Term.one
  let pr := Trans.Dict.wcnf w (toList x)
  let st := pr.1.foldl (init := ((none : Option Term), (none : Option Term)))
    fun s ac =>
      let a := ac.1
      let c := ac.2
      if le w a then
        let e := Trans.Dict.mulL w (Trans.Dict.subAP w a)
        let d := Trans.Dict.mulL e c
        let i := match s.1 with
          | none => sub1 d
          | some i0 => plus i0 d
        (some i, some (psi w i))
      else
        let bse := match s.2 with | none => base | some v => v
        let cc := match s.2 with | none => sub1 c | some _ => c
        (s.1, some (phiNF a (plus bse cc)))
  omegaNF (plus b (plus (st.2.getD zero) pr.2))

/-- 本体。`dict` との違いは**この 1 節だけ**である: 成分が `D u a` で `u ≥ 2` のとき、
    `collapse u` を呼ばずに `φ̄(u-1, Ω ⊕ sub1(ω^(dictB143 a)) ⊕ (m-1))` を返す
    (`m` は同じ成分が並ぶ個数)。`u ≤ 1` の節と和の畳み込みは `dict` と同じ。 -/
def dB143 (rg : Nat → Term) : Nat → BT → Term
  | 0, _ => zero
  | fuel + 1, t =>
    (((rle143 (BT.toL t)).map fun p =>
        match p.1 with
        | .D u a =>
          if u ≤ 1 then
            (List.replicate p.2 (collV143 rg u (dB143 rg fuel a))).foldr plus zero
          else
            phi (TM.Term.ofNat (u-1))
              (plus (Z zero) (plus (sub1 (omegaNF (dB143 rg fuel a))) (TM.Term.ofNat (p.2-1))))
        | _ => zero).foldr plus zero)

/-- **修理された辞書。**  `reg` は動かさない。 -/
def dictB143 (t : BT) : Term := dB143 reg (BT.size t + 1) t

/-- 対照。`reg 2` も `φ̄(1,Ω)` に差し替えた版。§6 で反証する。 -/
def dictB143R (t : BT) : Term := dB143 regB143 (BT.size t + 1) t

/-- `Trans.Recal.oR` の修理版 (`1 ⊕ ·` の約束はそのまま)。 -/
def oR143 (m : BMS.Matrix) : Option Term :=
  if m.isEmpty then some TM.Term.zero
  else (Trans.Recal.oRB m).map (fun t => TM.Term.plus TM.Term.one (dictB143 t))

/-! 節ごとの形。`dict_zero` はそのまま残る。`dict_D` は開いた `a` では書けないが、
    それは燃料を `BT.size` から取っている実装の都合で、数学的な違いではない
    (燃料の補題を別に立てれば書ける)。**`dict_sum` は本当に残らない** — 同じ成分の
    連なりを 1 つの `φ̄` に束ねる規則と和への分配は両立しない (§5 の指摘どおり)。 -/

theorem dictB143_zero : dictB143 BT.zero = zero := rfl

/-! 開いた `a` では書けない (燃料が `BT.size` 由来なので節ごとに違う)。閉じた例で示す。
    `u ≤ 1` の節は `dict` と同じ `collapse`、`u ≥ 2` の節が新しい規則である。 -/
#guard dictB143 (.D 0 (.D 1 .zero)) == collapse 0 (dictB143 (.D 1 .zero))
#guard dictB143 (.D 1 (.D 1 .zero)) == collapse 1 (dictB143 (.D 1 .zero))
#guard dictB143 (.D 2 (.D 0 .zero))
       == phi TM.Term.one (plus (Z zero) (sub1 (omegaNF (dictB143 (.D 0 .zero)))))
#guard dictB143 (.D 3 .zero)
       == phi (TM.Term.ofNat 2) (plus (Z zero) (sub1 (omegaNF (dictB143 .zero))))

/-- **`dict_sum` は成り立たない。**  同じ成分が 2 つ並ぶと和にならない。 -/
theorem dictB143_sum_fails :
    dictB143 (.sum (BT.Om 2) (BT.Om 2)) ≠ plus (dictB143 (BT.Om 2)) (dictB143 (BT.Om 2)) := by
  decide

/-! ### §143.2 Where the repair does not bite: agreement with `dict`

§108.6 の凍結母集団 (大きさ 12 までの標準・段 1 以下の Buchholz 項 9992 個) では
`dictB143` は `dict` と完全に一致する。**理由は母集団に添字 2 以上が 1 つも無いから**で、
これも下で確かめる。だから「9992 個のうち何個動くか」の答えは 0 であり、
それは修理が小さいことの証拠ではない。段 3 まで広げた母集団は §4 で測る。 -/

#guard allStd108.length == 9992
#guard allStd108.all (fun z => btLe72 1 z)
#guard (allStd108.countP fun z => dictB143 z == dict z) == 9992
#guard (allStd108.countP fun z => dictB143R z == dict z) == 9992

/-! `collV143 reg` は `collapse` と同じもの (母集団で確認)。 -/
#guard allStd108.all fun z => collV143 reg 0 (dict z) == collapse 0 (dict z)

/-! ### §143.3 The published table

60 行のうち `oR143` が `Trans.oR` と違う値を出すのは 23 行 — 添字 37 から 59 まで、
`(0,0)(1,1)(2,2)` 以上の全部である。**§137 が壊れていると判定した 5 行だけではない。**
新しい 60 個の値は全部 𝔗(M) の項で、表の昇順も保たれ、値は 60 個とも相異なる。 -/

def valsNew143 : List Term := Rows.rows.map fun r => ((oR143 r.m).getD zero)

#guard Rows.rows.length == 60
#guard (Rows.rows.zipIdx.filter fun p => (oR143 p.1.m) != some p.1.t).map (·.2)
       == (List.range 23).map (37 + ·)
#guard (Rows.rows.countP fun r => (oR143 r.m) == some r.t) == 37
#guard (Rows.rows.countP fun r => ((oR143 r.m).map inT).getD false) == 60
#guard (valsNew143.zip valsNew143.tail).all fun p => lt p.1 p.2
#guard valsNew143.eraseDups.length == 60
/-! 掲載値も昇順・相異なる (対照)。 -/
#guard ((Rows.rows.map (·.t)).zip (Rows.rows.map (·.t)).tail).all fun p => lt p.1 p.2

/-! #### §143.3.1 五つの壊れた行、1 行ずつ

**行 37 は §140 の値そのもの。**  残る 4 行は §140 と違い、どれも §140 の値より真に下。
違いは 1 か所だけで、§140 が残す `Z 1` の和成分を route (b) は残さない
(route (b) では `Ω₂` の像が `Z 1` ではないから、`Z 1` はもう `Ω₂` の像ではない)。 -/

/-- 行 37 — **§140 と一致**。 -/
theorem row37_B143 : oR143 [[0,0],[1,1],[2,2]] = some corr37_140 := rfl

/-- 行 47 — §140 は先頭に `Z 1` を残す。 -/
theorem row47_B143 : oR143 [[0,0],[1,1],[2,2],[2,0],[3,1],[4,2]]
    = some (psi (Z zero) (phi zero (add (phi TM.Term.one (Z zero)) corr37_140))) := rfl

/-- 行 52 — §140 は `Z 1 ⊕ φ̄(1,Ω⊕1)`。 -/
theorem row52_B143 : oR143 [[0,0],[1,1],[2,2],[2,2]]
    = some (psi (Z zero) (phi TM.Term.one (add (Z zero) TM.Term.one))) := rfl

/-- 行 53 — §140 は `Z 1 ⊕ Z 1 ⊕ φ̄(1,Ω⊕1⊕1)`。 -/
theorem row53_B143 : oR143 [[0,0],[1,1],[2,2],[2,2],[2,2]]
    = some (psi (Z zero) (phi TM.Term.one (add (Z zero) (add TM.Term.one TM.Term.one)))) := rfl

/-- 行 58 — §140 は `φ̄(0, Z 1 ⊕ ψ_Ω(φ̄(1,Ω)))`。 -/
theorem row58_B143 : oR143 [[0,0],[1,1],[2,2],[3,0],[4,1],[5,2]]
    = some (psi (Z zero) (phi TM.Term.one (add (Z zero) corr37_140))) := rfl

/-! 4 行とも §140 の値より真に下にある。 -/
#guard lt ((oR143 [[0,0],[1,1],[2,2],[2,0],[3,1],[4,2]]).getD zero) corr47_140
#guard lt ((oR143 [[0,0],[1,1],[2,2],[2,2]]).getD zero) corr52_140
#guard lt ((oR143 [[0,0],[1,1],[2,2],[2,2],[2,2]]).getD zero) corr53_140
#guard lt ((oR143 [[0,0],[1,1],[2,2],[3,0],[4,1],[5,2]]).getD zero) corr58_140
/-! そして掲載値より真に下 (§139 が反証したのは掲載値が上すぎることだった)。 -/
#guard Rows.rows.all fun r => match oR143 r.m with
  | some v => le v r.t
  | none => true

/-! #### §143.3.2 展開の値との関係 (測定)

`oR143` で測り直しても、60 行すべてで展開の値は行の値より真に下にある (深さ 5)。
これは必要条件にすぎず §139 の反証を打ち消さない。**行 37 では意味がある**:
展開の値は段 1 以下なので `dict` と同じままで、行の値がちょうど §69 の `sbad`
(= `corr37_140`) になる — §139 が「列の上・掲載値の下」と証明したその項である。 -/

def expOK143 (m : BMS.Matrix) (k : Nat) : Bool :=
  match oR143 m with
  | none => false
  | some v => ((List.range k).map fun n => oR143 (BMS.expand m n)).all fun o =>
      match o with | none => false | some x => lt x v
#guard Rows.rows.all fun r => r.m.isEmpty || expOK143 r.m 5
#guard (List.range 5).all fun n =>
  oR143 (BMS.expand [[0,0],[1,1],[2,2]] n) == Trans.oR (BMS.expand [[0,0],[1,1],[2,2]] n)
theorem row37_is_sbad143 : oR143 [[0,0],[1,1],[2,2]] = some sbad := rfl


/-! #### §143.3.3 `Trans/Dict.lean` の (A) アンカー 28 個をそのまま `dictB143` にかける

前半 19 個 (`Γ₀` までと `ψ₀(Ω₂)` の手前) は 1 つも動かない。後半 9 個は全部動き、
9 個とも `Ω₂` を含む項である。v0.1.41 の負の対照も変わらず成り立つ。 -/

def e0_143 : Term := phi TM.Term.one zero
def z0_143 : Term := phi (TM.Term.ofNat 2) zero
def G0_143 : Term := psi (Z zero) zero
def w2_143 : Term := psi (Z zero) (Z TM.Term.one)

/-- `Trans/Dict.lean` の §3 (A) のアンカー。左が Buchholz 項、右が今の `dict` の値。 -/
def anchorsA143 : List (BT × Term) :=
  [ (.D 0 (BT.Om 1), e0_143),
    (BT.add (.D 0 (BT.Om 1)) BT.one, plus e0_143 TM.Term.one),
    (.D 0 (BT.add (BT.Om 1) BT.one), phi zero e0_143),
    (.D 0 (BT.add (BT.Om 1) (BT.Om 1)), phi TM.Term.one TM.Term.one),
    (.D 0 (.D 1 BT.one), phi TM.Term.one TM.Term.omega),
    (.D 0 (.D 1 (BT.ofNat 2)), phi TM.Term.one (phi zero (TM.Term.ofNat 2))),
    (.D 0 (.D 1 BT.omega), phi TM.Term.one (phi zero TM.Term.omega)),
    (.D 0 (.D 1 (.D 0 (BT.Om 1))), phi TM.Term.one e0_143),
    (.D 0 (.D 1 (BT.Om 1)), z0_143),
    (BT.add (.D 0 (.D 1 (BT.Om 1))) BT.one, plus z0_143 TM.Term.one),
    (.D 0 (BT.add (.D 1 (BT.Om 1)) BT.one), phi zero z0_143),
    (.D 0 (BT.add (.D 1 (BT.Om 1)) (BT.Om 1)), phi TM.Term.one z0_143),
    (.D 0 (.D 1 (BT.add (BT.Om 1) BT.one)), phi (TM.Term.ofNat 2) TM.Term.omega),
    (.D 0 (.D 1 (BT.add (BT.Om 1) (BT.Om 1))), phi (TM.Term.ofNat 3) zero),
    (.D 0 (.D 1 (.D 1 BT.one)), phi TM.Term.omega zero),
    (.D 0 (.D 1 (.D 1 (.D 0 (BT.Om 1)))), phi e0_143 zero),
    (.D 0 (.D 1 (.D 1 (BT.Om 1))), G0_143),
    (BT.add (.D 0 (.D 1 (.D 1 (BT.Om 1)))) BT.one, plus G0_143 TM.Term.one),
    (.D 0 (BT.add (.D 1 (.D 1 (BT.Om 1))) BT.one), phi zero G0_143),
    (.D 0 (BT.Om 2), w2_143),
    (.D 0 (BT.add (BT.Om 2) (BT.Om 1)), phi TM.Term.one w2_143),
    (.D 0 (BT.add (BT.Om 2) (.D 1 (BT.Om 1))), phi (TM.Term.ofNat 2) w2_143),
    (.D 0 (BT.add (BT.Om 2) (.D 1 (.D 1 (BT.Om 1)))),
      psi (Z zero) (plus (Z TM.Term.one) TM.Term.one)),
    (.D 0 (BT.add (BT.Om 2) (.D 1 (BT.Om 2))),
      psi (Z zero) (plus (Z TM.Term.one) (phi TM.Term.one (Z zero)))),
    (.D 0 (BT.add (BT.Om 2) (BT.Om 2)),
      psi (Z zero) (plus (Z TM.Term.one) (Z TM.Term.one))),
    (.D 0 (BT.add (BT.Om 2) (BT.add (BT.Om 2) (BT.Om 2))),
      psi (Z zero) (plus (Z TM.Term.one) (plus (Z TM.Term.one) (Z TM.Term.one)))),
    (.D 0 (.D 2 BT.one), psi (Z zero) (phi zero (Z TM.Term.one))),
    (.D 0 (.D 2 (BT.Om 1)), psi (Z zero) (phi zero (plus (Z TM.Term.one) (Z zero)))) ]

#guard anchorsA143.length == 28
/-! 対照 — 今の `dict` は 28 個とも通る (これは `Trans/Dict.lean` の #guard の写し)。 -/
#guard anchorsA143.all fun p => dict p.1 == p.2
/-! `dictB143` が通すのは前半 19 個ちょうど。 -/
#guard (anchorsA143.countP fun p => dictB143 p.1 == p.2) == 19
#guard (anchorsA143.take 19).all fun p => dictB143 p.1 == p.2
#guard (anchorsA143.drop 19).all fun p => !(dictB143 p.1 == p.2)
/-! 動く 9 個は 1 つ残らず `Ω₂` を含む。 -/
#guard (anchorsA143.drop 19).all fun p => !(btLe72 1 p.1)
#guard (anchorsA143.take 19).all fun p => btLe72 1 p.1

/-! 新しい 9 個の値のうち 2 つ。`Ω₂ ↦ φ̄(1,Ω)`、`Ω₂·2 ↦ φ̄(1,Ω⊕1)` である。 -/
#guard dictB143 (.D 0 (BT.Om 2)) == corr37_140
#guard dictB143 (.D 0 (BT.add (BT.Om 2) (BT.Om 2)))
       == psi (Z zero) (phi TM.Term.one (add (Z zero) TM.Term.one))

/-! v0.1.41 の負の対照 (誤った読み) は `dictB143` でも出ない。 -/
#guard dictB143 (.D 0 (.D 1 (BT.add (BT.Om 1) (BT.Om 1)))) != phi (TM.Term.ofNat 2) TM.Term.one
#guard dictB143 (.D 0 (.D 1 (BT.add (BT.Om 1) BT.one)))
       != phi TM.Term.one (phi zero (phi (TM.Term.ofNat 2) zero))
#guard dictB143 (.D 0 (BT.Om 2)) != phi TM.Term.omega zero

/-! ### §143.4 The wider populations

§108.6 の 9992 個は段 1 以下だけなので 0 個しか動かない。段 3・大きさ 7 までの標準な
Buchholz 項 11577 個で測り直すと、動かないのは 486 個 (4.2%)、動くのが 11091 個。
形は 3 つ: (a) `Z u (u≥1)` が `φ̄(u,Ω)` になる、(b) `ψ_u` の像が `plus` に吸収されて
和成分が消える、(c) 同じ成分の連なりが 1 つの `φ̄` に束ねられる。 -/

def stepBT143 (lv : List (List BT)) : List (List BT) :=
  let n := lv.length
  let prev := lv.getD (n - 1) []
  let ds := (List.range 4).flatMap fun u => prev.map (fun a => BT.D u a)
  let ss := (List.range (n - 1)).flatMap fun i =>
      (lv.getD i []).flatMap fun a => (lv.getD (n - 2 - i) []).map fun b => BT.sum a b
  lv ++ [(ds ++ ss).filter BT.isStd]
def lvBT143 : Nat → List (List BT)
  | 0 => [[BT.zero]]
  | n + 1 => stepBT143 (lvBT143 n)
/-- 段 3 以下・大きさ 7 までの標準な Buchholz 項。 -/
def allStd143 : List BT := (lvBT143 7).flatten

#guard allStd143.length == 11577
#guard (allStd143.countP fun z => btLe72 1 z) == 325
#guard (allStd143.countP fun z => btLe72 2 z) == 2390
#guard (allStd143.countP fun z => dictB143 z == dict z) == 486
#guard (allStd143.countP fun z => btLe72 1 z && dictB143 z == dict z) == 325
#guard (allStd143.countP fun z => inT (dict z)) == 11577

/-! **`dictB143` は 11577 個中 11576 個で 𝔗(M) の項を出す。**  外れる 1 個は
    `ψ_Ω` の引数が 2.1(vi) の `K` 条件を満たさない形で、下に名前をつけてある。 -/
#guard (allStd143.countP fun z => inT (dictB143 z)) == 11576

def bad143 : BT := .D 0 (.D 3 (.D 2 (.D 0 (.D 3 (.D 1 (.D 3 .zero))))))
#guard allStd143.contains bad143
theorem bad143_std : BT.isStd bad143 = true := rfl
theorem bad143_notInT : inT (dictB143 bad143) = false := rfl
theorem bad143_dict_inT : inT (dict bad143) = true := rfl

/-! ### §143.5 Order preservation

`Trans/Dict.lean` の (B)/(C) 母集団をそのまま組み直して `dictB143` にかける。
`dict` は 0 件、`dictB143` は多数の反転を出す。**これが route (b) の値段である。** -/

def dedup143 (l : List BT) : List BT :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []
def dsucc143 (n : Nat) (l : List BT) : List BT :=
  (List.range n).flatMap (fun u => l.map (fun a => BT.D u a))
def sums143 (l : List BT) : List BT := l.flatMap (fun a => l.map (fun b => BT.add a b))
def every143 (k : Nat) (l : List BT) : List BT :=
  (l.zipIdx.filter (fun p => p.2 % k == 0)).map (·.1)
def lvl0_143 : List BT := [.zero, BT.one, BT.ofNat 2, BT.omega, BT.Om 1, BT.Om 2, BT.Om 3]
def lvl1_143 : List BT := dedup143 ((lvl0_143 ++ dsucc143 4 lvl0_143).filter BT.isStd)
def lvl2_143 : List BT := dedup143 ((lvl1_143 ++ dsucc143 4 lvl1_143).filter BT.isStd)
def cD143 : List BT := every143 5 (dedup143 ((dsucc143 3 lvl2_143).filter BT.isStd))
def cS143 : List BT := every143 5 (dedup143 ((sums143 (every143 3 lvl2_143)).filter BT.isStd))

#guard (lvl2_143.length, cD143.length, cS143.length) == (112, 54, 149)

def okP143 (f : BT → Term) (a b : BT) : Bool := BT.lt a b == lt (f a) (f b)
def cntBad143 (f : BT → Term) (l : List BT) : Nat :=
  (l.flatMap fun a => l.map fun b => okP143 f a b).countP (· == false)
def cntInj143 (f : BT → Term) (l : List BT) : Nat :=
  (l.flatMap fun a => l.map fun b => (a == b) == (f a == f b)).countP (· == false)

-- (B) 𝔗(M) の項であること: この 3 つの母集団では `dictB143` も全部通る
#guard lvl2_143.all fun a => inT (dictB143 a)
#guard cD143.all fun a => inT (dictB143 a)
#guard cS143.all fun a => inT (dictB143 a)

-- (C) 順序保存: `dict` は 0 件、`dictB143` は 672 / 284 / 1993 件
#guard (cntBad143 dict lvl2_143, cntBad143 dict cD143, cntBad143 dict cS143) == (0, 0, 0)
#guard (cntBad143 dictB143 lvl2_143, cntBad143 dictB143 cD143, cntBad143 dictB143 cS143)
       == (672, 284, 1993)
-- (C) 単射性: `dict` は 0 件、`dictB143` は 40 / 4 / 26 件
#guard (cntInj143 dict lvl2_143, cntInj143 dict cD143, cntInj143 dict cS143) == (0, 0, 0)
#guard (cntInj143 dictB143 lvl2_143, cntInj143 dictB143 cD143, cntInj143 dictB143 cS143)
       == (40, 4, 26)

/-- 段 3 母集団からの抜き取り 313 個でも同じ。 -/
def samp143 : List BT := every143 37 allStd143
#guard samp143.length == 313
#guard cntBad143 dict samp143 == 0
#guard cntBad143 dictB143 samp143 == 14476
#guard cntInj143 dictB143 samp143 == 16

/-! ### §143.6 THE OBSTRUCTION

route (b) は**表の上では通る**が、その 1 段下で必ず壊れる。壊れ方は 2 つあり、
`reg 2` をどちらに選んでも一方に当たる。 -/

/-! #### §143.6.1 `reg 2` を残すと `Ω₂` と `ψ₁(Ω₂)` が同じ項になる

`collapse 1` の尾の枝は `ω^(Ω ⊕ ·)` で、`Ω` より上の ε 数の上では恒等写像である。
route (b) の代役 `φ̄(1,Ω)` はまさにその ε 数なので、`ψ₁(Ω₂)` は `Ω₂` と同じ項を受け取る。
両方とも標準な Buchholz 項で、Buchholz の順序は 2 つを分けている。 -/

def om2_143 : BT := BT.Om 2
def psi1om2_143 : BT := BT.D 1 (BT.Om 2)
def psi1om2s_143 : BT := BT.D 1 (BT.add (BT.Om 2) BT.one)

theorem std143 :
    BT.isStd om2_143 = true ∧ BT.isStd psi1om2_143 = true ∧ BT.isStd psi1om2s_143 = true := by
  refine ⟨rfl, rfl, rfl⟩

theorem btlt143 :
    BT.lt psi1om2_143 om2_143 = true ∧ BT.lt psi1om2s_143 om2_143 = true := by
  refine ⟨rfl, rfl⟩

/-! **衝突。**  `Ω₂` と `ψ₁(Ω₂)` の像が同じ。 -/
set_option maxHeartbeats 2000000 in
theorem collision143 : dictB143 om2_143 = dictB143 psi1om2_143 := by decide

/-- 対照: 今の `dict` は 2 つを分けている。 -/
theorem collision143_not_dict : dict om2_143 ≠ dict psi1om2_143 := by decide

/-- **反転。**  `ψ₁(Ω₂⊕1)` は Buchholz で `Ω₂` より下なのに、像は上になる。 -/
theorem inversion143 : lt (dictB143 om2_143) (dictB143 psi1om2s_143) = true := rfl

theorem inversion143_not_dict : lt (dict psi1om2s_143) (dict om2_143) = true := rfl

/-! **吸和。**  `Ω₂ ⊕ ψ₁(Ω₂⊕1)` の像から `Ω₂` の成分が消える (`plus` が捨てる)。
    表の行 43-50 はこの形である。 -/
set_option maxHeartbeats 2000000 in
theorem absorb143 :
    dictB143 (.sum om2_143 psi1om2s_143) = dictB143 psi1om2s_143 := by decide

theorem absorb143_not_dict :
    dict (.sum om2_143 psi1om2s_143) ≠ dict psi1om2s_143 := by decide

/-! 同じことは 1 段上でも起きる (`Ω₃` と `ψ₁(Ω₃)`)。 -/
set_option maxHeartbeats 2000000 in
theorem collision143_up : dictB143 (BT.Om 3) = dictB143 (BT.D 1 (BT.Om 3)) := by decide

/-! #### §143.6.2 `reg 2` を差し替えると 𝔗(M) の項でなくなる

しきい値を `φ̄(1,Ω)` にすれば `collapse 1` は強臨界の枝に入るが、その枝が作るのは
`ψ_w(·)` で、[Rathjen, 1991] 2.1(vi) は添字が `R = {Zα}` にあることを要求する。
`φ̄(1,Ω)` は `R` に無い。**これは翻訳の不備ではなく行き先の型の事実である** —
`plan/chi-2ary.md` が「`Ω₂` を正則基数として名指せない」と言っているその事実。 -/

theorem notR143 : isR (phi TM.Term.one (Z zero)) = false := by decide
theorem isR_Z143 : isR (Z TM.Term.one) = true := rfl

theorem regR_notInT143 : inT (dictB143R (BT.D 1 (BT.D 3 BT.zero))) = false := rfl

/-! 差し替えた版は段 3 母集団 11577 個のうち 4164 個で 𝔗(M) の外に出る。 -/
#guard (allStd143.countP fun z => !(inT (dictB143R z))) == 4164
#guard (allStd143.countP fun z => !(inT (dictB143 z))) == 1

/-! そして差し替えても 6.1 の衝突は直らない。 -/
set_option maxHeartbeats 2000000 in
theorem collision143R : dictB143R om2_143 = dictB143R psi1om2_143 := by decide

/-- 差し替えた版は表の 2 行を潰す — `(0,0)(1,1)(2,2)(2,1)(3,2)` と
    `(0,0)(1,1)(2,2)(2,2)` (行 51 と 52)。`dictB143` はこれは潰さない。 -/
def oR143R (m : BMS.Matrix) : Option Term :=
  if m.isEmpty then some TM.Term.zero
  else (Trans.Recal.oRB m).map (fun t => TM.Term.plus TM.Term.one (dictB143R t))
#guard oR143R [[0,0],[1,1],[2,2],[2,1],[3,2]] == oR143R [[0,0],[1,1],[2,2],[2,2]]
#guard oR143 [[0,0],[1,1],[2,2],[2,1],[3,2]] != oR143 [[0,0],[1,1],[2,2],[2,2]]
#guard Trans.oR [[0,0],[1,1],[2,2],[2,1],[3,2]] != Trans.oR [[0,0],[1,1],[2,2],[2,2]]

/-! #### §143.6.3 代役は `φ̄(1,Ω)` 以外に選べない (測定)

`collapse 0` を動かさないかぎり、行 37 の値 `ψ_Ω(φ̄(1,Ω))` を出す引数 `x` は
候補 18549 個のうち 14 個。そのうち段 1 以下の像を全部超えているのは 1 個 —
`φ̄(1,Ω)` だけである。`Ω₂` は Buchholz で段 1 以下の項を全部超えるので、
**代役は他に選べない**。 -/

def cands143 : List Term :=
  (allStd143.map dictB143 ++ allStd143.map dict ++
   [phi TM.Term.one (Z zero), plus (phi TM.Term.one (Z zero)) TM.Term.one,
    plus (phi TM.Term.one (Z zero)) (phi TM.Term.one (Z zero)),
    phi TM.Term.one (plus (Z zero) TM.Term.one), phi zero (phi TM.Term.one (Z zero)),
    Z TM.Term.one, psi (Z TM.Term.one) zero, phi (TM.Term.ofNat 2) (Z zero),
    omegaNF (plus (Z zero) (phi TM.Term.one (Z zero)))]).eraseDups
def lo143 : List BT := every143 11 (allStd108.filter fun z => btLe72 1 z)

#guard cands143.length == 18549
#guard (cands143.countP fun x => collapse 0 x == corr37_140) == 14
#guard (cands143.filter fun x => collapse 0 x == corr37_140 && lo143.all fun z => lt (dict z) x)
       == [phi TM.Term.one (Z zero)]
#guard lo143.length == 909
/-! `Z 1` は行 37 の値を出さない (今の掲載値が上すぎるという §139 の内容)。 -/
#guard collapse 0 (Z TM.Term.one) != corr37_140


/-! ## §144 THE `TM/FS.lean` REPAIR AT `Z 1`, PROTOTYPED — AND IT DOES WORK


**THIS FILE IS A PROTOTYPE AND TOUCHES NOTHING.**  It defines `fsN144` BESIDE `TM/FS.lean`'s
`fsN`, under a new name, so that the repair can be proved and priced without a rebuild of
everything above `TM/FS.lean`.  Integration is a separate decision.

WHAT §141 LEFT.  `fsN_not_cofinal141` proves, with no hypothesis, that `fsN` is not cofinal
at `ψ_Ω(Z 1)`: the term `ψ_Ω(Ω)` is `inT`, is strictly below `ψ_Ω(Z 1)`, and is strictly
above every member of `fsN (ψ_Ω(Z 1)) ·`.  §141 also located the cause — the `psi` /
`.isLim` diagonalisation feeds the PREVIOUS VALUE back as the index:

    fsN (psi k a) 0       = psi k (fsT a 0)
    fsN (psi k a) (m+1)   = psi k (fsT a (fsN (psi k a) m))

The index is therefore always a `ψ_κ`-value, hence below `κ`.  That is right when
`cof α = κ`.  When `cof α = π` is a regular strictly ABOVE `κ` the indices must climb
inside `π`, and nothing below `κ` ever does; the sequence stalls at `ψ_κ(κ)`.  The visible
symptom is `fsN_agree141` — `fsN` returns the SAME sequence for `ψ_Ω(Z 1)` and `ψ_Ω(Ω)`,
two terms this repository's own order separates (`lt_wt_zt141`).

THE REPAIR, IN ONE LINE.  Replace the fed-back index `fsN (psi k a) m` — a `ψ_κ`-value —
by the same recursion run at `π = cof α` instead of at `κ`:

    x 0        = 0
    x (m+1)    = psi π (fsT a (x m))            `diagIdx144`
    fsN144 (psi k a) n = psi k (fsT a (x n))

When `π = κ` this is the old clause verbatim — `fsN143_eq_fsN_diag` PROVES it, it is not
measured.  When `π > κ` the indices are `ψ_π`-values and they climb inside `π`.
`fsT`, `cofT`, `psiSeed`, `kindT`, `predT` are UNCHANGED and reused as they stand: `κ` is
not visible inside `fsT`, so the only place that can see "the cofinality is a regular above
the collapsing index" is the `fsN` call site, which is where the repair goes.

PROVENANCE OF THE NEW CLAUSE (`TM/FS.lean` is a design choice, so a clause without
provenance is not a repair).

  1. [Rathjen, 1990] 3.6 — `χ_α : M → M` is a NORMAL function.  A normal function is
     continuous, so a limit second argument is reached from below and needs no name; what a
     descent through a regular `π = χ_α(0)` needs is a cofinal supply of indices BELOW `π`,
     and `ψ_π` is the only operation of 𝔗(M) that produces them.  This is the same reading
     `plan/chi-2ary.md` records under "直し方は「完全な 2 引数」ではない".
  2. Community usage.  The rule "if `cof α = Ω_{μ+1}` with `μ ≥ ν` then
     `ψ_ν(α)[n] = ψ_ν(α[γ n])` with `γ 0 = 0`, `γ (m+1) = ψ_{μ+1}(γ m)`" is the standard
     fundamental-sequence clause for Buchholz-style `ψ`, and it is exactly the clause above
     with `π = Ω_{μ+1}`.  `TM/FS.lean`'s own header already describes its `ψ` clauses as
     "the cofinal sequence of the C-closure" of the same shape.
  3. The external implementation.  naruyoko's `padicBotRathjen` (through
     `scripts/padicbot-ref.js`, under the dictionary that file fixes, `Ω = Z 0 ↔ W`,
     `Z 1 ↔ chi^{M}_{0}(0) = I`) computes, MEASURED with `node`:

         fund(ψ^W(I),   n) = ψ^W(ψ^I(…ψ^I(0)…))      n+1 nestings of ψ^I
         fund(ψ^W(W),   n) = ψ^W(ψ^W(…ψ^W(0)…))      n+1 nestings of ψ^W
         fund(ψ^W(I⊕I), n) = ψ^W(I ⊕ ψ^I(I ⊕ … ψ^I(0)…))

     The first is `fsN144 (ψ_Ω(Z 1)) (n+1)` term for term (`fsN143_psiZ1_144` gives the
     closed form; the offset by one is the SAME offset `TM/FS.lean`'s provenance section
     already records for the Γ₀ row and for `fund(ψ^W(W), ·)`, and `fsN` has it too).
     The second is `fsN (ψ_Ω(Ω)) (n+1)`, i.e. the branch this file leaves alone.
     The third shows the index is fed through `α[·]` and not a bare tower, which is what
     `diagIdx144` does.
     `ψ^W(ω^I)` and `ψ^W(W ⊕ I)` are NOT terms over there (their `dom` raises), so they
     cannot arbitrate anything and are not used here.

WHAT IS PROVED AND WHAT IS MEASURED — stated once, plainly.

  PROVED (no hypothesis, no `sorry`, no `native_decide`):
    `fsN143_eq_fsN_of_silent144`
                             `diagReach141 t = false → ∀ n, fsN144 t n = fsN t n`.  ALL terms,
                             ALL indices, no corpus — by `TM.Term.fsN.induct`, so every case
                             is one of `fsN`'s own branches.  §141 MEASURED this over 60
                             rows; here it is a theorem, which is what makes "no row's E3
                             changes" checkable rather than sampled.
    `fsN143_sbad144`         hence `fsN144 sbad n = fsN sbad n` for every `n`.
    `sameFs143_of_silent144` the same fact in the form the row `#guard`s use.
    `fsN143_eq_fsN_diag`     `fsN144 = fsN` on the whole `π = κ` branch, all `k`, `a`, `n`.
    `fsN143_psiOm_144`       hence `fsN144 (ψ_Ω(Ω)) n = fsN (ψ_Ω(Ω)) n` for every `n`.
    `fsN143_psiZ1_144`       closed form at `ψ_Ω(Z 1)`: `ψ_Ω` of the `ψ_{Z 1}`-tower.
    `fsN143_gap_closed144`   §141's witness `ψ_Ω(Ω)` is `≤` the member at index 1, and
                             EVERY member of §141's old sequence is strictly below it.
    `fsN143_mono144`         the new sequence is strictly increasing,
    `fsN143_lt_target144`    every member is strictly below `ψ_Ω(Z 1)`,
    `fsN143_ne_144`          and it separates `ψ_Ω(Z 1)` from `ψ_Ω(Ω)` at every index ≥ 1
                             — the negation of `fsN_agree141`.

  MEASURED (`#guard`, and `node` for the external): the row scan, the corpus scan, the
  `inT` of the new members, and the external's `fund`.

  NOT CLAIMED.  `fsN144` is NOT proved cofinal at `ψ_Ω(Z 1)`; only that §141's witness and
  §141's whole sequence are passed.  A full cofinality proof needs the closure structure of
  `C_Ω(·)` and is not attempted here.  Also NOT claimed as a theorem: WHICH rows
  `diagReach141` flags — that is a `#guard` over `Rows.rows` (exactly §137's five), and the
  theorem then covers all the others.
-/


section
open TM TM.Term

/-! ### §144.1 THE REPAIRED DEFINITION, BESIDE THE OLD ONE -/

/-- 対角化の添字列。 -/
def diagIdx144 (p a : Term) : Nat → Term
  | 0 => zero
  | n + 1 => psi p (fsT a (diagIdx144 p a n))

/-- 修理版 `fsN`。 -/
def fsN144 : Term → Nat → Term
  | add a b, n => plus a (fsN144 b n)
  | omg g, n =>
    (match kindT g with
     | .isSucc => mulNat (omegaNF (predT g)) n
     | _ => omegaNF (fsN144 g n))
  | phi a b, n =>
    if phiShifted a b || kindT b == KindT.isSucc then
      let c := if phiShifted a b then b else predT b
      let base := plus (phiNF a c) one
      match kindT a with
      | .isZero => mulNat (omegaNF c) n
      | .isSucc => iterPhiAt (predT a) base n
      | .isLim => phiNF (fsN144 a n) base
    else if kindT b == KindT.isLim then phiNF a (fsN144 b n)
    else
      (match kindT a with
       | .isSucc => iterPhiAt (predT a) zero n
       | .isLim => phiNF (fsN144 a n) zero
       | .isZero => zero)
  | psi k a, n =>
    (match kindT a with
     | .isZero =>
       (match k with
        | Z d =>
          (match kindT d with
           | .isLim => Z (fsN144 d n)
           | _ => iterGamma (psiSeed k) n)
        | _ => zero)
     | .isSucc => iterGamma (plus (psi k (predT a)) one) n
     | .isLim =>
       let p := cofT a
       if p == omega then psi k (fsN144 a n)
       else if lt p k then zero
       else if p.isR then psi k (fsT a (diagIdx144 p a n))
       else
         (match n with
          | 0 => psi k (fsT a zero)
          | m + 1 => psi k (fsT a (fsN144 (psi k a) m))))
  | _, _ => zero
  termination_by t n => (sizeOf t, n)

/-! ### §144.2 CLAUSE LEMMAS

`rw [fsN]` picks the wrong equation at a `psi` (the definition matches `k` against `Z d`
inside the clause, so a generic `psi k a` matches no specialised equation and falls through
to the catch-all).  These lemmas state each clause once, from `eq_def`, so the induction
below can rewrite with `if_pos` / `if_neg` instead of fighting `simp`.
-/

theorem bf144 {b : Bool} (h : ¬ (b = true)) : b = false := by
  cases b with
  | true => exact absurd rfl h
  | false => rfl

theorem dR_add144 (a b : Term) : diagReach141 (add a b) = diagReach141 b := by
  rw [diagReach141.eq_def]; try rfl

theorem dR_omg144 (g : Term) :
    diagReach141 (omg g) = (if kindT g == KindT.isSucc then false else diagReach141 g) := by
  rw [diagReach141.eq_def]; try rfl

theorem dR_phi144 (a b : Term) :
    diagReach141 (phi a b)
      = (if phiShifted a b || kindT b == KindT.isSucc then
           (match kindT a with | KindT.isLim => diagReach141 a | _ => false)
         else if kindT b == KindT.isLim then diagReach141 b
         else (match kindT a with | KindT.isLim => diagReach141 a | _ => false)) := by
  rw [diagReach141.eq_def]; try rfl

theorem dR_psi144 (k a : Term) :
    diagReach141 (psi k a)
      = (match kindT a with
         | KindT.isZero =>
             (match k with
              | Z d => if kindT d == KindT.isLim then diagReach141 d else false
              | _ => false)
         | KindT.isSucc => false
         | KindT.isLim =>
             (let p := cofT a
              if p == omega then diagReach141 a
              else if lt p k then false
              else !(p == k))) := by
  rw [diagReach141.eq_def]; try rfl

theorem fsN_add144 (a b : Term) (n : Nat) : fsN (add a b) n = plus a (fsN b n) := by
  rw [TM.Term.fsN.eq_def]; try rfl
theorem fsN143_add144 (a b : Term) (n : Nat) : fsN144 (add a b) n = plus a (fsN144 b n) := by
  rw [fsN144.eq_def]; try rfl

theorem fsN_omg144 (g : Term) (n : Nat) :
    fsN (omg g) n = (match kindT g with
                     | KindT.isSucc => mulNat (omegaNF (predT g)) n
                     | _ => omegaNF (fsN g n)) := by
  rw [TM.Term.fsN.eq_def]; try rfl
theorem fsN143_omg144 (g : Term) (n : Nat) :
    fsN144 (omg g) n = (match kindT g with
                        | KindT.isSucc => mulNat (omegaNF (predT g)) n
                        | _ => omegaNF (fsN144 g n)) := by
  rw [fsN144.eq_def]; try rfl

theorem fsN_phi144 (a b : Term) (n : Nat) :
    fsN (phi a b) n
      = (if phiShifted a b || kindT b == KindT.isSucc then
           (match kindT a with
            | KindT.isZero => mulNat (omegaNF (if phiShifted a b then b else predT b)) n
            | KindT.isSucc =>
                iterPhiAt (predT a)
                  (plus (phiNF a (if phiShifted a b then b else predT b)) one) n
            | KindT.isLim =>
                phiNF (fsN a n) (plus (phiNF a (if phiShifted a b then b else predT b)) one))
         else if kindT b == KindT.isLim then phiNF a (fsN b n)
         else (match kindT a with
               | KindT.isSucc => iterPhiAt (predT a) zero n
               | KindT.isLim => phiNF (fsN a n) zero
               | KindT.isZero => zero)) := by
  rw [TM.Term.fsN.eq_def]; try rfl
theorem fsN143_phi144 (a b : Term) (n : Nat) :
    fsN144 (phi a b) n
      = (if phiShifted a b || kindT b == KindT.isSucc then
           (match kindT a with
            | KindT.isZero => mulNat (omegaNF (if phiShifted a b then b else predT b)) n
            | KindT.isSucc =>
                iterPhiAt (predT a)
                  (plus (phiNF a (if phiShifted a b then b else predT b)) one) n
            | KindT.isLim =>
                phiNF (fsN144 a n) (plus (phiNF a (if phiShifted a b then b else predT b)) one))
         else if kindT b == KindT.isLim then phiNF a (fsN144 b n)
         else (match kindT a with
               | KindT.isSucc => iterPhiAt (predT a) zero n
               | KindT.isLim => phiNF (fsN144 a n) zero
               | KindT.isZero => zero)) := by
  rw [fsN144.eq_def]; try rfl

theorem fsN_psi144 (k a : Term) (n : Nat) :
    fsN (psi k a) n
      = (match kindT a with
         | KindT.isZero =>
             (match k with
              | Z d => (match kindT d with
                        | KindT.isLim => Z (fsN d n)
                        | _ => iterGamma (psiSeed k) n)
              | _ => zero)
         | KindT.isSucc => iterGamma (plus (psi k (predT a)) one) n
         | KindT.isLim =>
             (let p := cofT a
              if p == omega then psi k (fsN a n)
              else if lt p k then zero
              else (match n with
                    | 0 => psi k (fsT a zero)
                    | m + 1 => psi k (fsT a (fsN (psi k a) m))))) := by
  rw [TM.Term.fsN.eq_def]; try rfl
theorem fsN143_psi144 (k a : Term) (n : Nat) :
    fsN144 (psi k a) n
      = (match kindT a with
         | KindT.isZero =>
             (match k with
              | Z d => (match kindT d with
                        | KindT.isLim => Z (fsN144 d n)
                        | _ => iterGamma (psiSeed k) n)
              | _ => zero)
         | KindT.isSucc => iterGamma (plus (psi k (predT a)) one) n
         | KindT.isLim =>
             (let p := cofT a
              if p == omega then psi k (fsN144 a n)
              else if lt p k then zero
              else if p.isR then psi k (fsT a (diagIdx144 p a n))
              else (match n with
                    | 0 => psi k (fsT a zero)
                    | m + 1 => psi k (fsT a (fsN144 (psi k a) m))))) := by
  rw [fsN144.eq_def]; try rfl

/-! ### §144.3 THE REPAIR CHANGES NOTHING WHERE `diagReach141` IS SILENT — A THEOREM

§141's `diagReach141` walks exactly the branches `fsN` takes and flags the one place the
repair touches.  The theorem below says the two definitions agree on EVERY term it does not
flag — all terms, all indices, no corpus.  §141 measured this over 60 rows; here it is
proved.  The proof is by `TM.Term.fsN.induct` (the functional induction principle of the
ORIGINAL `fsN`), so every case is one of `fsN`'s own branches.
-/

theorem fsN_zero144 (n : Nat) : fsN zero n = zero := by rw [TM.Term.fsN.eq_def]; try rfl
theorem fsN_M144 (n : Nat) : fsN M n = zero := by rw [TM.Term.fsN.eq_def]; try rfl
theorem fsN_Z144 (d : Term) (n : Nat) : fsN (Z d) n = zero := by rw [TM.Term.fsN.eq_def]; try rfl
theorem fsN143_zero144 (n : Nat) : fsN144 zero n = zero := by rw [fsN144.eq_def]; try rfl
theorem fsN143_M144 (n : Nat) : fsN144 M n = zero := by rw [fsN144.eq_def]; try rfl
theorem fsN143_Z144 (d : Term) (n : Nat) : fsN144 (Z d) n = zero := by
  rw [fsN144.eq_def]; try rfl

theorem diagIdx143_zero (p a : Term) : diagIdx144 p a 0 = zero := rfl
theorem diagIdx143_succ (p a : Term) (n : Nat) :
    diagIdx144 p a (n + 1) = psi p (fsT a (diagIdx144 p a n)) := rfl

theorem fsN_diag0_144 {k a : Term} (hlim : kindT a = KindT.isLim)
    (hom : ((cofT a : Term) == omega) = false) (hlt : lt (cofT a) k = false) :
    fsN (psi k a) 0 = psi k (fsT a zero) := by
  rw [TM.Term.fsN.eq_def]
  simp only [hlim, hom, Bool.false_eq_true, if_false, hlt]

theorem fsN_diagS_144 {k a : Term} (hlim : kindT a = KindT.isLim)
    (hom : ((cofT a : Term) == omega) = false) (hlt : lt (cofT a) k = false) (m : Nat) :
    fsN (psi k a) (m + 1) = psi k (fsT a (fsN (psi k a) m)) := by
  rw [TM.Term.fsN.eq_def]
  simp only [hlim, hom, Bool.false_eq_true, if_false, hlt]

theorem diagIdx143_eq_fsN {k a : Term} (hlim : kindT a = KindT.isLim) (hcof : cofT a = k)
    (hom : ((k : Term) == omega) = false) :
    ∀ n : Nat, diagIdx144 k a (n + 1) = fsN (psi k a) n
  | 0 => by
      rw [diagIdx143_succ, diagIdx143_zero,
        fsN_diag0_144 hlim (by rw [hcof]; exact hom)
          (by rw [hcof]; exact Evidence.WF.lt_irrefl k)]
  | m + 1 => by
      rw [diagIdx143_succ, diagIdx143_eq_fsN hlim hcof hom m,
        fsN_diagS_144 hlim (by rw [hcof]; exact hom)
          (by rw [hcof]; exact Evidence.WF.lt_irrefl k) m]

/-- **`diagReach141` が沈黙する項では、修理版と旧版は完全に同じ列を出す。**
    項も添字も自由。母集団ではなく定理。§141 の「44 行はどれも動かない」の証明版。 -/
theorem fsN143_eq_fsN_of_silent144 :
    ∀ (t : Term) (n : Nat), diagReach141 t = false → fsN144 t n = fsN t n := by
  intro t n
  induction t, n using TM.Term.fsN.induct with
  | case1 a b n ih =>
      intro h; rw [dR_add144] at h; rw [fsN_add144, fsN143_add144, ih h]
  | case2 g n hg => intro _; rw [fsN_omg144, fsN143_omg144]; simp only [hg]
  | case3 g n hg ih =>
      intro h
      rw [dR_omg144, if_neg (by intro hc; exact hg (eq_of_beq hc))] at h
      rw [fsN_omg144, fsN143_omg144]
      cases hk : kindT g with
      | isSucc => exact absurd hk hg
      | isLim => simp only [ih h]
      | isZero => simp only [ih h]
  | case4 a b n h1 h2 =>
      intro _; rw [fsN_phi144, fsN143_phi144, if_pos h1, if_pos h1]; simp only [h2]
  | case5 a b n h1 h2 =>
      intro _; rw [fsN_phi144, fsN143_phi144, if_pos h1, if_pos h1]; simp only [h2]
  | case6 a b n h1 h2 ih =>
      intro h
      rw [dR_phi144, if_pos h1] at h
      simp only [h2] at h
      rw [fsN_phi144, fsN143_phi144, if_pos h1, if_pos h1]
      simp only [h2, ih h]
  | case7 a b n h1 h2 ih =>
      intro h
      rw [dR_phi144, if_neg h1, if_pos h2] at h
      rw [fsN_phi144, fsN143_phi144, if_neg h1, if_neg h1, if_pos h2, if_pos h2, ih h]
  | case8 a b n h1 h2 h3 =>
      intro _
      rw [fsN_phi144, fsN143_phi144, if_neg h1, if_neg h1, if_neg h2, if_neg h2]
      simp only [h3]
  | case9 a b n h1 h2 h3 ih =>
      intro h
      rw [dR_phi144, if_neg h1, if_neg h2] at h
      simp only [h3] at h
      rw [fsN_phi144, fsN143_phi144, if_neg h1, if_neg h1, if_neg h2, if_neg h2]
      simp only [h3, ih h]
  | case10 a b n h1 h2 h3 =>
      intro _
      rw [fsN_phi144, fsN143_phi144, if_neg h1, if_neg h1, if_neg h2, if_neg h2]
      simp only [h3]
  | case11 a n ha d hd ih =>
      intro h
      rw [dR_psi144] at h
      simp only [ha, hd] at h
      rw [fsN_psi144, fsN143_psi144]
      simp only [ha, hd, ih h]
  | case12 a n ha d hd =>
      intro _
      rw [fsN_psi144, fsN143_psi144]
      cases hk : kindT d with
      | isLim => exact absurd hk hd
      | isSucc => simp only [ha, hk]
      | isZero => simp only [ha, hk]
  | case13 k a n ha hk =>
      intro _
      rw [fsN_psi144, fsN143_psi144]
      cases k with
      | Z d => exact (hk d rfl).elim
      | zero => simp only [ha]
      | M => simp only [ha]
      | add x y => simp only [ha]
      | omg x => simp only [ha]
      | phi x y => simp only [ha]
      | psi x y => simp only [ha]
  | case14 k a n ha => intro _; rw [fsN_psi144, fsN143_psi144]; simp only [ha]
  | case15 k a n ha p hp ih =>
      intro h
      rw [dR_psi144] at h
      simp only [ha] at h
      rw [if_pos hp] at h
      rw [fsN_psi144, fsN143_psi144]
      simp only [ha]
      rw [if_pos hp, if_pos hp, ih h]
  | case16 k a n ha p hp hlt =>
      intro _
      rw [fsN_psi144, fsN143_psi144]
      simp only [ha]
      rw [if_neg hp, if_neg hp, if_pos hlt, if_pos hlt]
  | case17 k a ha p hp hlt =>
      intro _
      rw [fsN_psi144, fsN143_psi144]
      simp only [ha]
      rw [if_neg hp, if_neg hp, if_neg hlt, if_neg hlt]
      by_cases hR : (cofT a).isR = true
      · rw [if_pos hR, diagIdx143_zero]
      · rw [if_neg hR]
  | case18 k a ha p hp hlt n ih =>
      intro h
      have hp' : ((cofT a : Term) == omega) = false := bf144 hp
      have hlt' : lt (cofT a) k = false := bf144 hlt
      have hcof : cofT a = k := by
        rw [dR_psi144] at h
        simp only [ha] at h
        rw [if_neg hp, if_neg hlt] at h
        exact eq_of_beq (by simpa using h)
      rw [fsN_psi144, fsN143_psi144]
      simp only [ha]
      rw [if_neg hp, if_neg hp, if_neg hlt, if_neg hlt]
      by_cases hR : (cofT a).isR = true
      · rw [if_pos hR, hcof, diagIdx143_eq_fsN ha hcof (by rw [← hcof]; exact hp') n,
          ← fsN_diagS_144 ha hp' hlt' n, fsN_psi144]
      · rw [if_neg hR, ih h]
  | case19 x m h1 h2 h3 h4 =>
      intro _
      cases x with
      | zero => rw [fsN_zero144, fsN143_zero144]
      | M => rw [fsN_M144, fsN143_M144]
      | Z d => rw [fsN_Z144, fsN143_Z144]
      | add a b => exact (h1 a b rfl).elim
      | omg g => exact (h2 g rfl).elim
      | phi a b => exact (h3 a b rfl).elim
      | psi k a => exact (h4 k a rfl).elim

/-- **系 — §137 が行 37 に名指した値 `sbad = ψ_Ω(φ̄(1,Ω))` では列は一切動かない。**
    すべての `n` について。測定ではなく定理。 -/
theorem fsN143_sbad144 (n : Nat) : fsN144 sbad n = fsN sbad n :=
  fsN143_eq_fsN_of_silent144 sbad n rfl

/-! ### §144.3b The `π = κ` diagonalisation, stated directly -/

theorem fsN143_diag_144 {k a : Term} (hlim : kindT a = KindT.isLim)
    (hom : ((cofT a : Term) == omega) = false) (hlt : lt (cofT a) k = false)
    (hR : (cofT a).isR = true) (n : Nat) :
    fsN144 (psi k a) n = psi k (fsT a (diagIdx144 (cofT a) a n)) := by
  rw [fsN144.eq_def]
  simp only [hlim, hom, Bool.false_eq_true, if_false, hlt, hR, if_true]

/-- **修理は cof α = κ の枝を一切動かさない。** 仮定は「α が極限」「cof α = κ」
    「κ ≠ ω」「κ が正則項」だけで、`k` も `a` も `n` も自由。 -/
theorem fsN143_eq_fsN_diag {k a : Term} (hlim : kindT a = KindT.isLim) (hcof : cofT a = k)
    (hom : ((k : Term) == omega) = false) (hR : k.isR = true) :
    ∀ n : Nat, fsN144 (psi k a) n = fsN (psi k a) n
  | 0 => by
      rw [fsN143_diag_144 hlim (by rw [hcof]; exact hom)
            (by rw [hcof]; exact Evidence.WF.lt_irrefl k) (by rw [hcof]; exact hR),
        hcof, diagIdx143_zero,
        fsN_diag0_144 hlim (by rw [hcof]; exact hom)
          (by rw [hcof]; exact Evidence.WF.lt_irrefl k)]
  | m + 1 => by
      rw [fsN143_diag_144 hlim (by rw [hcof]; exact hom)
            (by rw [hcof]; exact Evidence.WF.lt_irrefl k) (by rw [hcof]; exact hR),
        hcof, diagIdx143_eq_fsN hlim hcof hom m,
        fsN_diagS_144 hlim (by rw [hcof]; exact hom)
          (by rw [hcof]; exact Evidence.WF.lt_irrefl k) m]

/-- §141 が「壊れていない側」として名指した項。`fsN144` はここでは何もしていない。 -/
theorem fsN143_psiOm_144 (n : Nat) :
    fsN144 (psi (Z zero) (Z zero)) n = fsN (psi (Z zero) (Z zero)) n :=
  fsN143_eq_fsN_diag (a := Z zero) (k := Z zero) rfl rfl rfl rfl n

/-- ゆえに `ψ_Ω(Ω)` での閉じた形は §141 の `gTow141` のまま。 -/
theorem fsN143_psiOm_gTow144 (n : Nat) :
    fsN144 (psi (Z zero) (Z zero)) n = gTow141 n := by
  rw [fsN143_psiOm_144 n, fsN_psiOm_141 n]

/-- `TM/FS.lean` の `fsT (Z d) s = s` (「正則: κ[s] = s」) — 変えていない。 -/
theorem fsT_Z144 (d s : Term) : fsT (Z d) s = s := rfl

/-! ### §144.4 THE CLOSED FORM AT `ψ_Ω(Z 1)` -/

/-- `ψ_{Z 1}` の塔。`Z 1 = χ_1(0) = I` を正則として降りる列。 -/
def iTow144 : Nat → Term
  | 0 => zero
  | n + 1 => psi (Z TM.Term.one) (iTow144 n)

theorem diagIdx143_Z1_144 :
    ∀ n : Nat, diagIdx144 (Z TM.Term.one) (Z TM.Term.one) n = iTow144 n
  | 0 => rfl
  | n + 1 => by rw [diagIdx143_succ, fsT_Z144, diagIdx143_Z1_144 n]; rfl

/-- **修理版の `ψ_Ω(Z 1)` での閉じた形。** 添字が `ψ_Ω` の塔ではなく `ψ_{Z 1}` の塔になる。 -/
theorem fsN143_psiZ1_144 :
    ∀ n : Nat, fsN144 (psi (Z zero) (Z TM.Term.one)) n = psi (Z zero) (iTow144 n) := by
  intro n
  rw [fsN143_diag_144 (k := Z zero) (a := Z TM.Term.one) rfl rfl rfl rfl n]
  show psi (Z zero) (fsT (Z TM.Term.one) (diagIdx144 (Z TM.Term.one) (Z TM.Term.one) n)) = _
  rw [fsT_Z144, diagIdx143_Z1_144 n]

/-! ### §144.5 ORDER FACTS -/

/-- ψ_{Z d}(x) < Z d。[R91] 2.3.8。§141 の `psi_lt_Om141` を `Z d` 一般に。 -/
theorem psi_lt_Z144 (d x : Term) : lt (psi (Z d) x) (Z d) = true := by
  unfold lt
  rw [show fuelOf (psi (Z d) x) (Z d)
      = (2 * ((psi (Z d) x).deg + (Z d).deg) + 7) + 1 from by unfold fuelOf; omega,
    Evidence.WF.ltF_succ_psi_Z, if_pos]
  simp only [show ((Z d : Term) == Z d) = true from by simp, Bool.true_or]

/-- Ω < ψ_{Z 1}(0)。閉じた項なので計算で出る。 -/
theorem lt_Om_psiI144 : lt (Z zero) (psi (Z TM.Term.one) zero) = true := rfl

/-- `ψ_Ω` の値はどれも `ψ_{Z 1}(0)` より下 — 添字が違う ψ の比較 ([R91] 2.3.14)。 -/
theorem lt_psiOm_psiI144 (A : Term) :
    lt (psi (Z zero) A) (psi (Z TM.Term.one) zero) = true := by
  rw [lt_psi_psi100 (k := Z zero) (a := A) (p := Z TM.Term.one) (b := zero)
      (by intro hc; injection hc with h1 _; exact absurd h1 (by decide)),
    if_neg (by decide),
    if_pos (show lt (Z zero) (Z TM.Term.one) = true from lt_Om_Om2_139)]
  exact lt_Om_psiI144

/-- 塔は真に増える。 -/
theorem iTow143_mono : ∀ n : Nat, lt (iTow144 n) (iTow144 (n + 1)) = true
  | 0 => rfl
  | n + 1 => by
      show lt (psi (Z TM.Term.one) (iTow144 n)) (psi (Z TM.Term.one) (iTow144 (n + 1))) = true
      rw [lt_psi_same]
      exact iTow143_mono n

/-- 塔はどれも `Z 1` の下 — 添字として正しい (`s < π`)。 -/
theorem iTow143_lt_Z1 : ∀ n : Nat, lt (iTow144 n) (Z TM.Term.one) = true
  | 0 => rfl
  | n + 1 => psi_lt_Z144 TM.Term.one (iTow144 n)

/-! ### §144.6 THE §141 GAP IS CLOSED -/

/-- 修理後の列は真に増える。 -/
theorem fsN143_mono144 (n : Nat) :
    lt (fsN144 (psi (Z zero) (Z TM.Term.one)) n)
       (fsN144 (psi (Z zero) (Z TM.Term.one)) (n + 1)) = true := by
  rw [fsN143_psiZ1_144 n, fsN143_psiZ1_144 (n + 1), lt_psi_same]
  exact iTow143_mono n

/-- 修理後の列は目標より下に留まる。 -/
theorem fsN143_lt_target144 (n : Nat) :
    lt (fsN144 (psi (Z zero) (Z TM.Term.one)) n) (psi (Z zero) (Z TM.Term.one)) = true := by
  rw [fsN143_psiZ1_144 n, lt_psi_same]
  exact iTow143_lt_Z1 n

/-- §141 の旧列 (`gTow141`) はどの段も修理後の添字 1 の項より真に下。 -/
theorem lt_gTow_fsN143_144 : ∀ n : Nat,
    lt (gTow141 n) (psi (Z zero) (psi (Z TM.Term.one) zero)) = true
  | 0 => by
      show lt (psi (Z zero) zero) (psi (Z zero) (psi (Z TM.Term.one) zero)) = true
      rw [lt_psi_same]
      rfl
  | n + 1 => by
      show lt (psi (Z zero) (gTow141 n)) (psi (Z zero) (psi (Z TM.Term.one) zero)) = true
      rw [lt_psi_same]
      obtain ⟨y, hy, _, _⟩ := gTow_shape141 n
      rw [hy]
      exact lt_psiOm_psiI144 y

/-- **§144 の主定理 — §141 の隙間は塞がった。**
    仮定なし。`ψ_Ω(Ω)` は修理後の列の添字 1 の項以下であり、
    §141 の旧列は全段が添字 1 の項より真に下にある。 -/
theorem fsN143_gap_closed144 :
    inT (psi (Z zero) (Z zero)) = true
      ∧ lt (psi (Z zero) (Z zero)) (psi (Z zero) (Z TM.Term.one)) = true
      ∧ le (psi (Z zero) (Z zero)) (fsN144 (psi (Z zero) (Z TM.Term.one)) 1) = true
      ∧ ∀ n : Nat,
          lt (fsN (psi (Z zero) (Z TM.Term.one)) n)
             (fsN144 (psi (Z zero) (Z TM.Term.one)) 1) = true := by
  refine ⟨inT_wt141, lt_wt_zt141, ?_, ?_⟩
  · rw [fsN143_psiZ1_144 1]
    show (((psi (Z zero) (Z zero) : Term) == psi (Z zero) (iTow144 1))
      || lt (psi (Z zero) (Z zero)) (psi (Z zero) (iTow144 1))) = true
    rw [lt_psi_same]
    show (((psi (Z zero) (Z zero) : Term) == psi (Z zero) (psi (Z TM.Term.one) zero))
      || lt (Z zero) (psi (Z TM.Term.one) zero)) = true
    rw [lt_Om_psiI144, Bool.or_true]
  · intro n
    rw [fsN_psiZ1_141 n, fsN143_psiZ1_144 1]
    show lt (gTow141 n) (psi (Z zero) (psi (Z TM.Term.one) zero)) = true
    exact lt_gTow_fsN143_144 n

/-- **`fsN_agree141` の否定。** 修理後の列は `ψ_Ω(Z 1)` と `ψ_Ω(Ω)` を、
    添字 1 以上のどこでも区別する。 -/
theorem fsN143_ne_144 (n : Nat) :
    fsN144 (psi (Z zero) (Z TM.Term.one)) (n + 1)
      ≠ fsN144 (psi (Z zero) (Z zero)) (n + 1) := by
  rw [fsN143_psiZ1_144 (n + 1), fsN143_psiOm_gTow144 (n + 1)]
  show psi (Z zero) (iTow144 (n + 1)) ≠ psi (Z zero) (gTow141 n)
  intro hc
  injection hc with _ h2
  obtain ⟨y, hy, _, _⟩ := gTow_shape141 n
  rw [hy] at h2
  have h2' : (psi (Z TM.Term.one) (iTow144 n) : Term) = psi (Z zero) y := h2
  injection h2' with h3 _
  exact absurd h3 (by decide)

/-! ### §144.7 THE COST — WHICH ROWS CHANGE

`sameFs144` compares the two definitions term by term over `n < 8`; `hasShift144` is
`Rows/Selected.lean`'s `hasShift` (and §141's `hasShift141`) with `fsN144` in place of
`fsN`.  `hitM144` mirrors `diagReach141` but flags the OTHER branch — the one where the
cofinality is not a regular TERM (`p = M`), which `fsN144` deliberately leaves on the old
clause because `ψ_M` is not a term of 𝔗(M) (`isR M = false`).
-/

/-- 二つの定義が `n < 8` で一致するか。 -/
def sameFs144 (t : Term) : Bool := (List.range 8).all fun n => fsN144 t n == fsN t n

/-- 上の定理の `#guard` 用の形。 -/
theorem sameFs143_of_silent144 (t : Term) (h : diagReach141 t = false) : sameFs144 t = true := by
  unfold sameFs144
  refine List.all_eq_true.mpr ?_
  intro n _
  rw [fsN143_eq_fsN_of_silent144 t n h]
  exact beq_self_eq_true _

/-- 展開が `fsN144` に一様なずらしで乗るか。 -/
def hasShift144 (r : Rows.Row) : Bool :=
  (List.range 6).any fun j =>
    (List.range 4).all fun n => Trans.oR (BMS.expand r.m n) == some (fsN144 r.t (n + j))

/-- `p` が正則項でない (= M) 側の枝に届くか。`fsN144` はそこを旧のまま残している。 -/
def hitM144 : Term → Bool
  | add _ b => hitM144 b
  | omg g => if kindT g == KindT.isSucc then false else hitM144 g
  | phi a b =>
      if phiShifted a b || kindT b == KindT.isSucc then
        (match kindT a with | KindT.isLim => hitM144 a | _ => false)
      else if kindT b == KindT.isLim then hitM144 b
      else (match kindT a with | KindT.isLim => hitM144 a | _ => false)
  | psi k a =>
      (match kindT a with
       | KindT.isZero =>
           (match k with
            | Z d => if kindT d == KindT.isLim then hitM144 d else false
            | _ => false)
       | KindT.isSucc => false
       | KindT.isLim =>
           let p := cofT a
           if p == omega then hitM144 a
           else if lt p k then false
           else !(p.isR))
  | _ => false

-- 表は 60 行。
#guard Rows.rows.length == 60

-- **変わる行はちょうど 5 行**、しかもそれは §137 の 5 行そのもの。
#guard ((Rows.rows.filter fun r => !(sameFs144 r.t)).map (·.m)) == brokenRows137
#guard (Rows.rows.countP fun r => sameFs144 r.t) == 55

-- **`diagReach141` が発火する行と、実際に値が変わる行は同じ集合。**
#guard Rows.rows.all fun r => diagReach141 r.t == !(sameFs144 r.t)

-- **`fsN` に乗る行は 44 行のまま、乗る・乗らないが変わる行は一つも無い。**
#guard (Rows.rows.countP fun r => hasShift144 r) == 44
#guard (Rows.rows.countP fun r => hasShift141 r) == 44
#guard Rows.rows.all fun r => hasShift141 r == hasShift144 r

-- 変わる 5 行は修理の前も後も `fsN` に乗らない。E3 はどれも動かない。
#guard (Rows.rows.filter fun r => diagReach141 r.t).all fun r => !(hasShift144 r)

-- §137 が行 37 に名指した値 `sbad` では、`fsN144` は `fsN` と同じ列を出す。
#guard sameFs144 sbad
#guard (List.range 8).all fun n => fsN144 sbad n == fsN sbad n

-- `TM/FS.lean` の母集団 169 項でも、変わるのは `diagReach141` が発火する項だけ。
#guard TM.Term.domCorpus.all fun t => diagReach141 t == !(sameFs144 t)
#guard (TM.Term.domCorpus.countP fun t => sameFs144 t) == 165
#guard (TM.Term.domCorpus.countP fun t => diagReach141 t) == 4

-- `p = M` の枝は表にも母集団にも届かない。
#guard (Rows.rows.countP fun r => hitM144 r.t) == 0
#guard (TM.Term.domCorpus.countP fun t => hitM144 t) == 0

/-! ### 対照 (positive controls) — 上の 0 と「すべて一致」が空回りでないこと -/

-- `sameFs144` は発火する: 修理の対象そのもので偽になる。
#guard !(sameFs144 (psi (Z zero) (Z TM.Term.one)))
-- `hitM144` は発火する: `ψ_Ω(M)` で真 (この項は `inT` を通らない — だから到達しない)。
#guard hitM144 (psi (Z zero) M)
#guard inT (psi (Z zero) M) == false
#guard isR M == false
-- `hasShift144` は空回りしていない: 乗らない行が実在する。
#guard (Rows.rows.countP fun r => !(hasShift144 r)) == 16

/-! ### 測定 — 新しい列の各項 -/

-- 新しい列の各項は 𝔗(M) の項である (n < 6、測定)。
#guard (List.range 6).all fun n => inT (fsN144 (psi (Z zero) (Z TM.Term.one)) n)
-- 旧列は `ψ_Ω(Ω)` を超えないが、新列は添字 1 で超える (§141 との対比)。
#guard le (psi (Z zero) (Z zero)) (fsN144 (psi (Z zero) (Z TM.Term.one)) 1)
#guard (List.range 6).all fun n => !(le (psi (Z zero) (Z zero)) (fsN (psi (Z zero) (Z TM.Term.one)) n))
-- 新列は `ψ_Ω(Ω)` の列と添字 1 以上で違う。
#guard (List.range 6).all fun n =>
  !(fsN144 (psi (Z zero) (Z TM.Term.one)) (n+1) == fsN144 (psi (Z zero) (Z zero)) (n+1))
-- 添字 0 は両者で同じ (`x 0 = 0` なので、修理は n = 0 を動かさない)。
#guard fsN144 (psi (Z zero) (Z TM.Term.one)) 0 == fsN (psi (Z zero) (Z TM.Term.one)) 0

/-! ### 公理 — `sorryAx` も `native_decide` も無いこと -/

#print axioms fsN143_eq_fsN_of_silent144
#print axioms fsN143_sbad144
#print axioms sameFs143_of_silent144
#print axioms fsN143_eq_fsN_diag
#print axioms fsN143_psiOm_144
#print axioms fsN143_psiZ1_144
#print axioms fsN143_gap_closed144
#print axioms fsN143_ne_144
#print axioms fsN143_mono144
#print axioms fsN143_lt_target144

end


/-! ## §145 THE TWO GATES: THE FIRST TOOL OF ROUTE (b) IS NON-CIRCULAR, AND BOTH
       RESIDUALS SPLIT AT A NAMED PLACE

Nothing in the project is edited.  Every definition below lives beside the library under a
new name.

WHAT IS PROVED, UNCONDITIONALLY (no `PsiIdxOKStd172`, no `HiMono89`, no `sorry`,
no `native_decide`).

  §145.1  **`dict_D1_eq77` WITHOUT THE GATE.**  §77.7's `dict_D1_eq77` uses
           `PsiIdxOKStd172` for one thing only — `inT (dict a)`, through
           `inT_dict_of_std172`.  `dict_D1_inT145` takes that `inT` as a hypothesis instead,
           and `dict_D1_ih145` gets it from §87.1's `inT_dict_ih87`, i.e. from the size
           induction.  So `ψ₁(α) = ω^(Ω₁ ⊕ α)` is available inside `step073_of_gate87`
           with no gate.  This is the tool §136's closing note named.

  §145.2  **NO `ψ₀` NODE ⟹ NO `K_{Ω₁}`.**  `inT_dict_noD0145` and `kset_dict_noD0145`:
           for a level-`≤ 1` tree with no subscript-`0` node, `dict` lands in 𝔗(M) and
           `K_{Ω₁}(dict x)` is EMPTY, both with no hypothesis at all.  `inT` comes free
           here because `collapse 1`'s strongly critical branch never fires at level `≤ 1`
           (§73.4's `ksetStepOK_one73`), so no gate is consumed.

  §145.3  **THE FIRST GATE, READ OFF THE `BT` SHAPE.**  `hiPure145` is a decider on the
           Buchholz term alone: every subscript-`1` component's argument is free of
           subscript-`0` nodes; subscript-`0` components are unrestricted.  On such a term
           `gateStd87_of_hiPure145` proves `GateStd87 a` inside the size induction, and
           `fireK_nil_of_hiPure145` says honestly where that sits: `fireK132 a = []`, so
           §145.3 is a `BT`-side sufficient condition for the clause §132 had already
           closed, not new coverage.  It does explain §132.3's `kDomBad132` structurally:
           its `ψ₀` component sits in the tail `ρ < Ω₁`, which `bigPart` never reaches.

  §145.4  **THE FIRST GATE SPLITS AT THE FIRST FIRING STEP.**  `laterHotb145` asks whether
           any step that already HAS an accumulated index escapes §136.1's bundle.
           `gateStd87_of_first145`: if it does not, the whole one-term gate reduces to
           `FirstFire145 a` — the obligation at the steps where `p.1.1 = none`, where the
           index is `Δ ⊖ 1` and there is no prefix.  `step073_of_first145` is the split
           (`first143_of_step073`/`later143_of_step073` are the converses, so nothing is
           weakened).

  §145.6  **THE SECOND GATE SPLITS BY THE LAST VEBLEN EXPONENT.**  `XMono145` is §133's
           missing lemma, named: when the two last fold steps carry the SAME exponent,
           `hi a < hi b` forces `X_a < X_b`.  `vebRest129_of_xmono145` : `XMono145` plus
           `VebRestDiff145` (the different-exponent half) give `VebRest129`, because under
           `XMono145` an equal-exponent pair makes `rt1_129` fire and contradicts
           `closed129 a b = false`.  `hiMono_of_xmono145` carries it up to `HiMono89`.
           `not_XMonoLoose145` : dropping `BT.isStd (BT.D 0 a)` from the left term makes
           `XMono145` FALSE, and §101's pair is the witness — unconditionally.
           `nearMiss145` : **the two known near-misses are in different halves.**  §101's
           pair has equal exponents and reversed `X`; §81's pair has different exponents.

WHAT IS MEASURED, NOT PROVED (§145.5, §145.7).

  * **A new population for the first gate.**  `fm145`, 90117 terms up to **75 symbols**
    (§136.4's largest was 30), built around the shape that DOES break the gate once
    `BT.isStd (ψ₀ ·)` is dropped, with the `ψ₀` argument pushed to repeated sums of towers
    — the direction that makes the inner index as large as `K`-standardness allows.
    5281 are level-`≤ 1` and `K`-standard, 3371 are in §132's residual, **0 are in §136's,
    0 break the gate, and 0 have a later step that escapes the bundle.**

  * **THE FIRST GATE'S RESIDUAL LIVES AT THE FIRST FIRING STEP.**  Counting `(step, K-element)`
    obligations over §132's residual in four populations — `stdTab130` to 15 symbols,
    `famPool132`, `pool136`, `fm145` — there are **11245** of them, of which only **108**
    are at a step that already has an accumulated index, and **all 108** are discharged by
    §92.1 (`y ≤ i₀`) or §136.1 (`y = i₀ ⊕ r`, `r < Δ`) alone.  The other four members of
    §136.1's bundle (§100.2/§105.1, §105.2, §110.2, §115.2) never fire anywhere except at
    the first firing step.  `laterHotb145` is `false` on every residual term of all four
    populations, so `step073_of_first145`'s `H2` is vacuous on everything measured.

  * **AND AT THE FIRST FIRING STEP ONE EXEMPTION CARRIES IT.**  Of the 11137 first-step
    obligations, **6616 are accepted by §105.2 (`powFree105`) and by nothing else**; 86 by
    §100.2/§105.1 alone, 6 by §115.2 alone, **0 by §110.2 alone**, and 0 escape everything.
    So the first gate's residual is concentrated on one arithmetic fact —
    `y < Ω₁^(A ⊖ Ω₁)` at the step where the index is `Δ ⊖ 1`.

  * **`XMono145` IS TRUE AND NOT VACUOUS ON EVERYTHING MEASURED.**  Over the `K`-standard
    level-`≤ 1` terms with `Ω₁ ≤ dict` and a non-firing last pair, to 12 symbols (2962 of
    them; §129.5 stopped at 9 symbols and 278), **4377054** pairs satisfy `VebRest129`'s
    premise, **1336152** of them carry the same last exponent, and **`rt1_129` closes every
    one of those**.  The different-exponent half is NOT carried by `rt2_129` alone —
    2075886 of its 3040902 pairs need `closed117` — so the split puts the analytic weight
    on `XMono145`.

WHAT IS **NOT** CLAIMED.  Neither gate is proved and neither is refuted.  §145.3 does not
shrink §132's residual (`fireK_nil_of_hiPure145` says so in Lean).  §145.4 and §145.6 are
splits with converses, not weakenings; the counts around them are deciders over finite
populations, not proofs.  In particular `laterHotb145 = false` everywhere measured is the
same kind of statement §130, §132 and §136 made, and §115's history says why an empty
column is not a theorem.
-/


section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

/-! ### §145.1 非循環な `dict_D1_eq77` -/

/-- **`dict_D1_eq77` から門を外したもの。**  §77.7 の `dict_D1_eq77` は
    `PsiIdxOKStd172` を `inT (dict a)` を取り出すためだけに使っている
    (`inT_dict_of_std172` 一回)。その `inT` を仮定に出せば門は要らない。 -/
theorem dict_D1_inT145 (a : BT) (hb : btLe72 1 a = true) (hin : inT (dict a) = true) :
    dict (BT.D 1 a) = omegaNF (plus (reg 1) (dict a)) := by
  rw [Trans.Dict.dict_D]
  exact collapse1_eq77 (dict a) hin
    (fun p hp => lt_pure73_reg2 (pure73_toList _ (pure73_dict a hb) p hp))

/-- **大きさの帰納法の中で使う形。**  §87.1 の `inT_dict_ih87` がその `inT` を配るので、
    §132 が「循環」と呼んだ道を通らずに (D1) の等式が使える。 -/
theorem dict_D1_ih145 (a : BT) (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b)
    (hb : btLe72 1 a = true) (hs : BT.isStd a = true) :
    dict (BT.D 1 a) = omegaNF (plus (reg 1) (dict a)) :=
  dict_D1_inT145 a hb (inT_dict_ih87 a ih hb hs).1

/-! ### §145.2 添字 0 の節を持たない木 -/

/-- 添字 0 の節をひとつも持たない木。 -/
def noD0145 : BT → Bool
  | .zero => true
  | .D u a => !(u == 0) && noD0145 a
  | .sum a b => noD0145 a && noD0145 b

theorem noD0143_D {u : Nat} {a : BT} (h : noD0145 (BT.D u a) = true) :
    u ≠ 0 ∧ noD0145 a = true := by
  obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp (show (!(u == 0) && noD0145 a) = true from h)
  refine ⟨fun hc => ?_, h2⟩
  rw [hc] at h1
  exact Bool.noConfusion h1

theorem noD0143_sum {a b : BT} (h : noD0145 (BT.sum a b) = true) :
    noD0145 a = true ∧ noD0145 b = true :=
  (Bool.and_eq_true _ _).mp (show (noD0145 a && noD0145 b) = true from h)

/-- 添字 0 の節が無ければ `dict` の像は無条件に 𝔗(M) の中。門も帰納法の仮説も要らない —
    `collapse 1` の側は §73.4 の `ksetStepOK_one73` が無条件に閉じているから。 -/
theorem inT_dict_noD0145 : ∀ (x : BT), btLe72 1 x = true → noD0145 x = true →
    inT (dict x) = true ∧ lt (dict x) M = true
  | .zero, _, _ => ⟨inT_zero, lt_zero_M⟩
  | .D u x, hb, hn => by
      obtain ⟨hu, hbx⟩ := btLe72_D 1 u x hb
      obtain ⟨hu0, hnx⟩ := noD0143_D hn
      have hu1 : u = 1 := by omega
      subst hu1
      have ih := inT_dict_noD0145 x hbx hnx
      rw [Trans.Dict.dict_D]
      exact inT_collapse_gap3 1 (dict x) ih.1 ih.2
        (psiIdxOK_of_stepOK 1 (dict x) ih.1 ih.2 (ksetStepOK_one73 x hbx))
  | .sum x y, hb, hn => by
      obtain ⟨hbx, hby⟩ := btLe72_sum 1 x y hb
      obtain ⟨hnx, hny⟩ := noD0143_sum hn
      have ihx := inT_dict_noD0145 x hbx hnx
      have ihy := inT_dict_noD0145 y hby hny
      rw [Trans.Dict.dict_sum]
      exact ⟨inT_plus ihx.1 ihy.1, lt_plus_M ihx.1 ihy.1 ihx.2 ihy.2⟩

/-- **§145.2 の主定理。**  添字 0 の節が無ければ `K_{Ω₁}` は空。
    `K_{Ω₁}` の元は `ψ_π`-項 (`Ω₁ ≤ π`) の引数からしか出ないが、そういう項を作るのは
    `collapse 0` の強臨界の枝だけで、添字 0 の節が無ければその枝は一度も通らない。 -/
theorem kset_dict_noD0145 : ∀ (x : BT), btLe72 1 x = true → noD0145 x = true →
    ∀ y, y ∈ Kset (reg 1) (dict x) → False
  | .zero, _, _ => by rw [Trans.Dict.dict_zero]; intro y hy; cases hy
  | .D u x, hb, hn => by
      obtain ⟨hu, hbx⟩ := btLe72_D 1 u x hb
      obtain ⟨hu0, hnx⟩ := noD0143_D hn
      have hu1 : u = 1 := by omega
      subst hu1
      intro y hy
      rw [dict_D1_inT145 x hbx (inT_dict_noD0145 x hbx hnx).1] at hy
      rcases mem_Kset_plus (mem_Kset_omegaNF hy) with h1 | h1
      · exact mem_Kset_reg 1 h1
      · exact kset_dict_noD0145 x hbx hnx y h1
  | .sum x y, hb, hn => by
      obtain ⟨hbx, hby⟩ := btLe72_sum 1 x y hb
      obtain ⟨hnx, hny⟩ := noD0143_sum hn
      intro z hz
      rw [Trans.Dict.dict_sum] at hz
      rcases mem_Kset_plus hz with h1 | h1
      · exact kset_dict_noD0145 x hbx hnx z h1
      · exact kset_dict_noD0145 y hby hny z h1

/-! ### §145.3 形から読み取る門 -/

/-- **非循環な `ltW_dict94` の一節。**  §94.1 の `ltW_dict94` は `PsiIdxOKStd172` を
    `inT (dict z)` と `PsiIdxOK 0 (dict z)` のために使う。大きさの帰納法の中では
    どちらも手元にある。 -/
theorem ltW_D0_ih145 (z : BT) (ih : ∀ b : BT, BT.size b < BT.size (BT.D 0 z) → GateStd87 b)
    (hb : btLe72 1 (BT.D 0 z) = true) (hs : BT.isStd (BT.D 0 z) = true) :
    lt (dict (BT.D 0 z)) (reg 1) = true := by
  obtain ⟨_, hbz⟩ := btLe72_D 1 0 z hb
  have hsz : BT.size z < BT.size (BT.D 0 z) := by
    rw [size_D87]; have := size_pos87 z; omega
  have hiz := inT_dict_ih87 z (fun b hbb => ih b (by omega)) hbz (isStd_of_D hs)
  rw [Trans.Dict.dict_D]
  exact lt_collapse0_W79 (dict z) hiz.1 hiz.2
    (psiIdxOK_of_stepOK 0 (dict z) hiz.1 hiz.2 (ih z hsz hbz hs))

/-- `plus` は成分を作らない。 -/
theorem mem_toList_plus145 {s t : Term} (hs : inT s = true) (ht : inT t = true)
    {p : Term} (hp : p ∈ toList (plus s t)) : p ∈ toList s ∨ p ∈ toList t := by
  cases hl : toList t with
  | nil => rw [plus_nil hl] at hp; exact Or.inl hp
  | cons b1 rest =>
    rw [toList_plus_inT hs ht hl] at hp
    rcases List.mem_append.mp hp with h | h
    · exact Or.inl (List.mem_filter.mp h).1
    · exact Or.inr (by rw [← hl]; exact h)

/-- **読み取れる形。**  添字 1 の成分は引数に添字 0 の節を持たない。
    添字 0 の成分は何でもよい — その値は `Ω₁` より下で、走査は末尾を読まない。 -/
def hiPure145 : BT → Bool
  | .zero => true
  | .D u x => (u == 0) || ((u == 1) && noD0145 x)
  | .sum a b => hiPure145 a && hiPure145 b

theorem hiPure143_sum {a b : BT} (h : hiPure145 (BT.sum a b) = true) :
    hiPure145 a = true ∧ hiPure145 b = true :=
  (Bool.and_eq_true _ _).mp (show (hiPure145 a && hiPure145 b) = true from h)

/-- **§145.3 の中心。**  この形の項では、`Ω₁` より下にない成分の `K_{Ω₁}` は空。 -/
theorem comp145 : ∀ (a : BT), (∀ b : BT, BT.size b < BT.size a → GateStd87 b) →
    btLe72 1 a = true → BT.isStd a = true → hiPure145 a = true →
    ∀ p ∈ toList (dict a), lt p (reg 1) = false → ∀ y, y ∈ Kset (reg 1) p → False
  | .zero, _, _, _, _ => by rw [Trans.Dict.dict_zero]; intro p hp; cases hp
  | .D u x, ih, hb, hs, hp => by
      obtain ⟨hu, hbx⟩ := btLe72_D 1 u x hb
      intro p hpm hlp y hy
      cases u with
      | zero =>
          have hap : (dict (BT.D 0 x)).isAP = true := by
            rw [Trans.Dict.dict_D, collapse_eq]; exact isAP_omegaNF _
          rw [toList_isAP81 hap, List.mem_singleton] at hpm
          subst hpm
          rw [ltW_D0_ih145 x ih hb hs] at hlp
          exact Bool.noConfusion hlp
      | succ u' =>
          have hu1 : u' = 0 := by omega
          subst hu1
          have hnx : noD0145 x = true := by
            have : ((1 == 0) || ((1 == 1) && noD0145 x)) = true := hp
            simpa using this
          rw [dict_D1_inT145 x hbx (inT_dict_noD0145 x hbx hnx).1] at hpm
          rw [toList_isAP81 (isAP_omegaNF _), List.mem_singleton] at hpm
          subst hpm
          rcases mem_Kset_plus (mem_Kset_omegaNF hy) with h1 | h1
          · exact mem_Kset_reg 1 h1
          · exact kset_dict_noD0145 x hbx hnx y h1
  | .sum x z, ih, hb, hs, hp => by
      obtain ⟨hbx, hbz⟩ := btLe72_sum 1 x z hb
      obtain ⟨hsx, hsz⟩ := isStd_of_sum hs
      obtain ⟨hpx, hpz⟩ := hiPure143_sum hp
      have hszx : BT.size x < BT.size (BT.sum x z) := by
        rw [size_sum87]; have := size_pos87 z; omega
      have hszz : BT.size z < BT.size (BT.sum x z) := by
        rw [size_sum87]; have := size_pos87 x; omega
      have ihx : ∀ b : BT, BT.size b < BT.size x → GateStd87 b := fun b hbb => ih b (by omega)
      have ihz : ∀ b : BT, BT.size b < BT.size z → GateStd87 b := fun b hbb => ih b (by omega)
      have hix := inT_dict_ih87 x ihx hbx hsx
      have hiz := inT_dict_ih87 z ihz hbz hsz
      intro p hpm hlp y hy
      rw [Trans.Dict.dict_sum] at hpm
      rcases mem_toList_plus145 hix.1 hiz.1 hpm with h1 | h1
      · exact comp145 x ihx hbx hsx hpx p h1 hlp y hy
      · exact comp145 z ihz hbz hsz hpz p h1 hlp y hy

/-- **§145.3 の主定理。**  形が読み取れる項では第一の門は無条件の定理。
    門も帰納法の外の仮説も使わない — `ih` は §87.1 の大きさの帰納法そのもの。 -/
theorem gateStd87_of_hiPure145 (a : BT)
    (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b)
    (hp : hiPure145 a = true) : GateStd87 a := by
  intro hb hs
  refine ksetStepOK_of_bigNil132 0 (dict a) (fun y hy => ?_)
  obtain ⟨p, hpm, hyp⟩ := (mem_KsetL_iff _ _ _).mp hy
  exact comp145 a ih hb (isStd_of_D hs) hp p (bigPart_sub _ _ _ hpm)
    (bigPart_ge87 _ _ _ hpm) y hyp

/-! ### §145.4 最初に発火する歩とそれ以降 -/

/-- **最初に発火する歩の義務。**  直前の指数がまだ無い歩 — そこでは指数は `Δ ⊖ 1`。 -/
def FirstFire145 (a : BT) : Prop :=
  ∀ p ∈ scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1,
    p.1.1 = none → le (reg 1) p.2.1 = true →
      ∀ y, (y ∈ Kset (reg 1) p.2.1 ∨ y ∈ Kset (reg 1) p.2.2) →
        lt y (idxOf (reg 1) p.1 p.2) = true

/-- 直前の指数がある歩のうち、§136 の束ねた免除を外すものを持つか。 -/
def laterHotb145 (a : BT) : Bool :=
  (scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1).any fun p =>
    p.1.1.isSome && le (reg 1) p.2.1 &&
      (Kset (reg 1) p.2.1 ++ Kset (reg 1) p.2.2).any (fun y => !(freeb136 p y))

/-- **§145.4 の主定理。**  直前の指数がある歩がぜんぶ §136 の束で只なら、一項ぶんの門は
    **最初に発火する歩の義務だけ**に落ちる。`PsiIdxOKStd172` は使わない。 -/
theorem gateStd87_of_first145 (a : BT)
    (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b)
    (hl : laterHotb145 a = false) (H : FirstFire145 a) : GateStd87 a := by
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
  cases hq1 : q.1.1 with
  | none => exact H q hq hq1 hle2 y hy
  | some i0 =>
      obtain ⟨hi1, hl1, hi2, hl2⟩ := hallOK q.2 (scanSt_mem_snd _ _ _ _ q hq)
      obtain ⟨hidxT, _⟩ := inT_idxOf mulDescInT (inT_reg 1) (ltM_reg 1) hst hi1 hl1 hi2 hl2
      have hz : q.2.2 ≠ zero :=
        wcnf_coef_ne_zero119 (toList (dict a)) hcL hdL hML q.2 (scanSt_mem_snd _ _ _ _ q hq)
      have hsm : q.1.1.isSome = true := by rw [hq1]; rfl
      have hfb : freeb136 q y = true := by
        cases hf : freeb136 q y with
        | true => rfl
        | false =>
          exfalso
          have hcon : laterHotb145 a = true := by
            refine List.any_eq_true.mpr ⟨q, hq, ?_⟩
            show (q.1.1.isSome && le (reg 1) q.2.1 &&
              (Kset (reg 1) q.2.1 ++ Kset (reg 1) q.2.2).any (fun y => !(freeb136 q y))) = true
            rw [hsm, hle2]
            simp only [Bool.true_and]
            refine List.any_eq_true.mpr ⟨y, ?_, by rw [hf]; rfl⟩
            rcases hy with h | h
            · exact List.mem_append.mpr (Or.inl h)
            · exact List.mem_append.mpr (Or.inr h)
          rw [hcon] at hl
          exact Bool.noConfusion hl
      exact lt_idxOf_of_freeb136 hst hi1 hi2 hl2 hz hy hfb hidxT

/-- **§145.4 の分割。**  §136 の残る仮定に、さらに二つの条件が付く —
    形が読めないこと (`hiPure145 a = false`) と、後の歩が束を外すかどうか。
    `H1` は最初の歩の義務だけ、`H2` は後の歩が束を外す項の義務。 -/
theorem step073_of_first145
    (H1 : ∀ a : BT, btLe72 1 a = true → btLe72 0 a = false → BT.isStd (BT.D 0 a) = true →
          fireK132 a ≠ [] → hotb136 a = true → hiPure145 a = false →
          laterHotb145 a = false → FirstFire145 a)
    (H2 : ∀ a : BT, btLe72 1 a = true → btLe72 0 a = false → BT.isStd (BT.D 0 a) = true →
          fireK132 a ≠ [] → hotb136 a = true → hiPure145 a = false →
          laterHotb145 a = true → KsetStepOK 0 (dict a)) : PsiIdxStep073 := by
  refine step073_of_gate87 (fun a ih => ?_)
  cases hsh : hiPure145 a with
  | true => exact gateStd87_of_hiPure145 a ih hsh
  | false =>
      cases hh : hotb136 a with
      | false => exact gateStd87_of_hotb136 ih hh
      | true =>
          cases hlt : laterHotb145 a with
          | false =>
              intro hb hs
              cases hk : fireK132 a with
              | nil => exact gateStd87_of_fireNil132 hk hb hs
              | cons z zs =>
                  cases h0 : btLe72 0 a with
                  | true => exact ksetStepOK_zero130 a h0
                  | false =>
                      exact gateStd87_of_first145 a ih hlt
                        (H1 a hb h0 hs (by rw [hk]; exact List.cons_ne_nil z zs) hh hsh hlt)
                        hb hs
          | true =>
              intro hb hs
              cases hk : fireK132 a with
              | nil => exact gateStd87_of_fireNil132 hk hb hs
              | cons z zs =>
                  cases h0 : btLe72 0 a with
                  | true => exact ksetStepOK_zero130 a h0
                  | false =>
                      exact H2 a hb h0 hs (by rw [hk]; exact List.cons_ne_nil z zs) hh hsh hlt

/-- **§145.3 がどこに座っているか、正直な形。**  読み取れる形の項では
    §132 の `fireK132` が空になる。つまり §145.3 は §132 の分割が既に閉じている側の、
    `dict` を計算せずに `BT` の形だけで決まる十分条件である。 -/
theorem fireK_nil_of_hiPure145 (a : BT)
    (ih : ∀ b : BT, BT.size b < BT.size a → GateStd87 b)
    (hb : btLe72 1 a = true) (hs : BT.isStd a = true) (hp : hiPure145 a = true) :
    fireK132 a = [] := by
  cases hf : fireK132 a with
  | nil => rfl
  | cons z zs =>
      exfalso
      have hz : z ∈ fireK132 a := by rw [hf]; exact List.Mem.head _
      obtain ⟨ac, hac, hmem⟩ := List.mem_flatMap.mp
        (show z ∈ ((wcnf (reg 1) (toList (dict a))).1.filter
          (fun ac => le (reg 1) ac.1)).flatMap
          (fun ac => Kset (reg 1) ac.1 ++ Kset (reg 1) ac.2) from hz)
      have hac' : ac ∈ (wcnf (reg 1) (toList (dict a))).1 := (List.mem_filter.mp hac).1
      have hy : z ∈ Kset (reg 1) ac.1 ∨ z ∈ Kset (reg 1) ac.2 := List.mem_append.mp hmem
      obtain ⟨q, hq, hzq⟩ := (mem_KsetL_iff _ _ _).mp
        (mem_Kset_wcnf (k := reg 1) (toList (dict a)) ac hac' hy)
      exact comp145 a ih hb hs hp q (bigPart_sub _ _ _ hq) (bigPart_ge87 _ _ _ hq) z hzq

/-- 逆向き — §145.4 の分割が本当に分割であることの記録。緩めてはいない。 -/
theorem first143_of_step073 (H : PsiIdxStep073) (a : BT) (hb : btLe72 1 a = true)
    (_h0 : btLe72 0 a = false) (hs : BT.isStd (BT.D 0 a) = true) (_hk : fireK132 a ≠ [])
    (_hh : hotb136 a = true) (_hsh : hiPure145 a = false) (_hlt : laterHotb145 a = false) :
    FirstFire145 a := fun p hp _ hle y hy => (H a hb hs p hp hle).2 y hy

theorem later143_of_step073 (H : PsiIdxStep073) (a : BT) (hb : btLe72 1 a = true)
    (_h0 : btLe72 0 a = false) (hs : BT.isStd (BT.D 0 a) = true) (_hk : fireK132 a ≠ [])
    (_hh : hotb136 a = true) (_hsh : hiPure145 a = false) (_hlt : laterHotb145 a = true) :
    KsetStepOK 0 (dict a) := H a hb hs

/-- **第一の残る仮定そのもの、§145.4 の形で。** -/
theorem psiIdxStepStd172_of_first145
    (H1 : ∀ a : BT, btLe72 1 a = true → btLe72 0 a = false → BT.isStd (BT.D 0 a) = true →
          fireK132 a ≠ [] → hotb136 a = true → hiPure145 a = false →
          laterHotb145 a = false → FirstFire145 a)
    (H2 : ∀ a : BT, btLe72 1 a = true → btLe72 0 a = false → BT.isStd (BT.D 0 a) = true →
          fireK132 a ≠ [] → hotb136 a = true → hiPure145 a = false →
          laterHotb145 a = true → KsetStepOK 0 (dict a)) : PsiIdxStepStd172 :=
  psiIdxStepStd172_of_step073 (step073_of_first145 H1 H2)

theorem psiIdxOKStd172_of_first145
    (H1 : ∀ a : BT, btLe72 1 a = true → btLe72 0 a = false → BT.isStd (BT.D 0 a) = true →
          fireK132 a ≠ [] → hotb136 a = true → hiPure145 a = false →
          laterHotb145 a = false → FirstFire145 a)
    (H2 : ∀ a : BT, btLe72 1 a = true → btLe72 0 a = false → BT.isStd (BT.D 0 a) = true →
          fireK132 a ≠ [] → hotb136 a = true → hiPure145 a = false →
          laterHotb145 a = true → KsetStepOK 0 (dict a)) : PsiIdxOKStd172 :=
  psiIdxOKStd172_of_step073 (step073_of_first145 H1 H2)

#print axioms dict_D1_ih145
#print axioms kset_dict_noD0145
#print axioms gateStd87_of_hiPure145
#print axioms fireK_nil_of_hiPure145
#print axioms gateStd87_of_first145
#print axioms psiIdxOKStd172_of_first145

end

/-! ### §145.5 測定 (凍結)

母集団は四つ。§130 の `stdTab130` を大きさ 15 まで全数、§132.5 の `famPool132`、
§136.4 の `pool136`、そして §145.5 で新しく組んだ `fm145` (90117 本、大きさ 75 まで)。 -/

section
open Trans.Recal
open Trans.Dict (BT dict)
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse)
open TM TM.Term
open Evidence.WF

def tw145 (k : Nat) : BT := nst132 k BT.zero
def sm145 : List BT → BT
  | [] => BT.zero
  | [x] => x
  | x :: r => BT.sum x (sm145 r)
def rep145 (n : Nat) (t : BT) : BT := sm145 (List.replicate (n+1) t)

def zp145 : List BT :=
  let R := List.range
  ((R 7).flatMap fun k => (R 8).map fun n => rep145 n (tw145 k)) ++
  ((R 6).flatMap fun i => (R 6).flatMap fun j => (R 6).map fun k =>
      sm145 [tw145 i, tw145 j, tw145 k]) ++
  ((R 5).flatMap fun i => (R 5).flatMap fun j => (R 5).flatMap fun k => (R 5).map fun l =>
      sm145 [tw145 i, tw145 j, tw145 k, tw145 l]) ++
  ((R 6).flatMap fun i => (R 6).map fun j => sm145 [tw145 i, BT.D 0 (tw145 j)]) ++
  ((R 6).flatMap fun i => (R 6).map fun j => nst132 i (rep145 1 (tw145 j)))

def fm145 : List BT :=
  let R := List.range
  (zp145.flatMap fun z => (R 8).map fun m => nst132 m (BT.D 0 z)) ++
  (zp145.flatMap fun z => (R 6).flatMap fun m => (R 5).map fun p =>
      nst132 m (BT.sum (tw145 p) (BT.D 0 z))) ++
  (zp145.flatMap fun z => (R 6).flatMap fun m => (R 5).map fun p =>
      BT.sum (nst132 m (BT.D 0 z)) (tw145 p)) ++
  (zp145.flatMap fun z => (R 5).flatMap fun m => (R 5).map fun p =>
      BT.sum (tw145 p) (nst132 m (BT.D 0 z)))

def pys145 (a : BT) : List (((Option Term × Option Term) × (Term × Term)) × Term) :=
  ((scanSt (reg 1) (baseOf 0) (none, none) (wcnf (reg 1) (toList (dict a))).1).filter
      (fun p => le (reg 1) p.2.1)).flatMap
    (fun p => (Kset (reg 1) p.2.1 ++ Kset (reg 1) p.2.2).map (fun y => (p, y)))
def okY145 (q : (((Option Term × Option Term) × (Term × Term)) × Term)) : Bool :=
  lt q.2 (idxOf (reg 1) q.1.1 q.1.2)
def later145 (q : (((Option Term × Option Term) × (Term × Term)) × Term)) : Bool := q.1.1.1.isSome
def ps145 (q : (((Option Term × Option Term) × (Term × Term)) × Term)) : Bool :=
  prevFree136 q.1 q.2 || splitFree136 q.1 q.2

def cen145 (P : List BT) : Nat × Nat × Nat × Nat :=
  let L := P.flatMap pys145
  let La := L.filter later145
  (L.length, La.length, La.countP (fun q => !(ps145 q)), L.countP (fun q => !(okY145 q)))

/-! **新しい母集団。**  `ψ₀` の引数を「塔の反復和」にする方向へ広げたもの — §132.5 の
`famB132` が残る仮定を外す形 (`ψ₁^m(ψ₀(ψ₁^k 0))`, `3 ≤ m < k`) の、`K` 標準性が
許すぎりぎりを狙った族。**90117 本、大きさ 75 まで。§136.4 の母集団の 4 倍。** -/

#guard (zp145.length, fm145.length, (fm145.map BT.size).foldl max 0) == (969, 90117, 75)

/-! **そこでも残る仮定は一度も外れない。**  段 1 以下・`K` 標準が 5281 本、
§132 の残りが 3371 本、§136 が残すのは **0 本**、残る仮定を外すのも **0 本**、
そして後の歩が §136 の束を外すのも **0 本**。 -/

#guard (fm145.countP (fun a => btLe72 1 a && BT.isStd (BT.D 0 a)),
        fm145.countP resid136, fm145.countP hot136, fm145.countP bad132,
        fm145.countP (fun a => resid136 a && laterHotb145 a)) == (5281, 3371, 0, 0, 0)

/-! **§145.4 の測定 — 後の歩は既に片づいている。**  §132 の残りに居る項のうち、
「直前の指数がある歩で §136 の束を外す」ものは、四つの母集団のどれにも **1 本も無い**。
つまり測ったかぎり `laterHotb145` は常に `false` で、`step073_of_first145` の `H2` は
空回りし、第一の門は**最初に発火する歩の義務**に落ちる。 -/

#guard (pool136.countP (fun a => resid136 a && laterHotb145 a),
        famPool132.countP (fun a => resid136 a && laterHotb145 a),
        ((stdTab130 14).flatten).countP (fun a => resid136 a && laterHotb145 a)) == (0, 0, 0)

/-! **§145.3 の座り場所。**  読み取れる形の項は §132 の残りには一度も入らない
(`fireK_nil_of_hiPure145` の通り)。それでも空虚ではない — 大きさ 15 までの
段 1 以下・`K` 標準な木 12436+838+2494 本のうち **3961 本**がこの形である。 -/

#guard (pool136.countP (fun a => resid136 a && hiPure145 a),
        famPool132.countP (fun a => resid136 a && hiPure145 a),
        ((stdTab130 14).flatten).countP (fun a => resid136 a && hiPure145 a),
        fm145.countP (fun a => resid136 a && hiPure145 a)) == (0, 0, 0, 0)

#guard (pool136.countP (fun a => btLe72 1 a && BT.isStd (BT.D 0 a) && hiPure145 a),
        ((stdTab130 14).flatten).countP (fun a => btLe72 1 a && BT.isStd (BT.D 0 a) && hiPure145 a))
  == (67, 3961)

/-! **義務そのものを数える。**  行は (全部の (歩, 元) の組, そのうち直前の指数がある歩,
そのうち §92.1 の `y ≤ i₀` でも §136.1 の分割でも只にならないもの, `y < idx` を外すもの)。
**四つ合わせて 11245 組のうち、直前の指数がある歩に居るのは 108 組しかなく、
その 108 組はぜんぶ `prevFree136` か `splitFree136` で只になる。**
§136 の束の残り四つ (§100.2/§105.1・§105.2・§110.2・§115.2) は、測ったかぎり
**最初に発火する歩でしか働いていない**。 -/

/-- 最初に発火する歩の (歩, 元) を、束の残り四つのどれが受け取るかで数える。
    行は (総数, §100.2/§105.1 だけ, §105.2 だけ, §110.2 だけ, §115.2 だけ,
    ちょうど一つが受け取るもの, どれも受け取らないもの)。 -/
def who145 (P : List BT) : Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  let L := (P.flatMap pys145).filter (fun q => !q.1.1.1.isSome)
  let v := fun (q : (((Option Term × Option Term) × (Term × Term)) × Term)) =>
    [regFree136 q.1 q.2, powFree105 q.1 q.2, coefFree110 q.1 q.2, coefFreeU115 q.1 q.2]
  let cnt := fun (i : Nat) => L.countP (fun q =>
    let b := v q
    (b.getD i false) && ((b.eraseIdx i).all (fun x => !x)))
  (L.length, cnt 0, cnt 1, cnt 2, cnt 3,
   L.countP (fun q => ((v q).countP id) == 1),
   L.countP (fun q => (v q).all (fun x => !x)))

/-! **最初の歩を担いでいるのは §105.2 ひとつ。**  四つの母集団の最初の歩の義務
11137 組のうち、**6616 組は §105.2 (`powFree105`) だけが受け取る**。
§100.2/§105.1 だけが受け取るのは 86 組、§115.2 だけは 6 組、**§110.2 だけは 0 組**
(§115.2 が上位互換だという §115 の言い分がここでも出る)。どれも受け取らない組は 0。
つまり第一の門の残りは「最初に発火する歩で `y < Ω₁^(A ⊖ Ω₁)` を示すこと」に寄っている。 -/

#guard who145 (((stdTab130 14).flatten).filter resid136) == (3795, 39, 1976, 0, 0, 2015, 0)
#guard who145 (pool136.filter resid136) == (893, 6, 510, 0, 1, 517, 0)
#guard who145 (famPool132.filter resid136) == (2975, 11, 1885, 0, 0, 1896, 0)
#guard who145 (fm145.filter resid136) == (3474, 30, 2245, 0, 5, 2280, 0)

#guard cen145 (fm145.filter resid136) == (3530, 56, 0, 0)
#guard cen145 (pool136.filter resid136) == (940, 47, 0, 0)
#guard cen145 (famPool132.filter resid136) == (2975, 0, 0, 0)
#guard cen145 (((stdTab130 14).flatten).filter resid136) == (3800, 5, 0, 0)
#guard ((stdTab130 14).flatten).countP resid136 == 3734

end

/-! ### §145.6 第二の門 — 同じ指数の半分と違う指数の半分 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- 最後の一歩の指数が等しいか。 -/
def sameExp145 (a b : BT) : Bool :=
  match lastStep129 (dict a), lastStep129 (dict b) with
  | some pa, some pb => pa.1 == pb.1
  | _, _ => false

/-- 最後の一歩の第二引数が狭義に増えるか。 -/
def xok145 (a b : BT) : Bool :=
  match lastStep129 (dict a), lastStep129 (dict b) with
  | some pa, some pb => lt pa.2 pb.2
  | _, _ => false

theorem rt1_of_145 {a b : BT} (h1 : sameExp145 a b = true) (h2 : xok145 a b = true) :
    rt1_129 a b = true := by
  cases hla : lastStep129 (dict a) with
  | none =>
      have e1 : sameExp145 a b = false := by
        unfold sameExp145; rw [hla]
      rw [e1] at h1; exact Bool.noConfusion h1
  | some pa =>
      cases hlb : lastStep129 (dict b) with
      | none =>
          have e1 : sameExp145 a b = false := by unfold sameExp145; rw [hla, hlb]
          rw [e1] at h1; exact Bool.noConfusion h1
      | some pb =>
          have e1 : sameExp145 a b = (pa.1 == pb.1) := by unfold sameExp145; rw [hla, hlb]
          have e2 : xok145 a b = lt pa.2 pb.2 := by unfold xok145; rw [hla, hlb]
          have e3 : rt1_129 a b = ((pa.1 == pb.1) && lt pa.2 pb.2) := by
            unfold rt1_129; rw [hla, hlb]
          rw [e1] at h1
          rw [e2] at h2
          rw [e3, h1, h2]; rfl

/-- **§145.6 の名前つきの穴 — 同じ指数の半分。**  §133 が「`X_a` を `hi a` で
    押さえる補題がない」と言ったところ。最後の一歩の指数が両辺で等しいとき、
    `φ̄` の第二引数が `hi` に沿って動くこと。 -/
def XMono145 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lastFire92 (dict a) = false → lastFire92 (dict b) = false →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    sameExp145 a b = true → xok145 a b = true

/-- **残り半分 — 最後の一歩の指数が違う組。** -/
def VebRestDiff145 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd (BT.D 0 a) = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lastFire92 (dict a) = false → lastFire92 (dict b) = false →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    closed129 a b = false → sameExp145 a b = false →
    lt (collapse 0 (hiW89 (dict a))) (collapse 0 (hiW89 (dict b))) = true

/-- **§145.6 の橋。**  `VebRest129` は二つに割れて、同じ指数の側は `XMono145` が
    そのまま閉じる — `rt1_129` が発火して `closed129 a b = false` と食い違うから。 -/
theorem vebRest129_of_xmono145 (H1 : XMono145) (H2 : VebRestDiff145) : VebRest129 := by
  intro a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hcl
  cases hse : sameExp145 a b with
  | false => exact H2 a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hcl hse
  | true =>
      exfalso
      have hx := H1 a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hse
      have hr : closed129 a b = true := by
        unfold closed129
        rw [rt1_of_145 hse hx]
        cases closed117 a b <;> rfl
      rw [hr] at hcl
      exact Bool.noConfusion hcl

/-- **`HiMono89` を §145.6 の二つに架け替える。** -/
theorem hiMono_of_xmono145 (Hp : PsiIdxOKStd172) (HA : IdxMono101) (HB : IdxLeMix109)
    (HV : VebIngF114) (HX : XMono145) (HD : VebRestDiff145) : HiMono89 :=
  hiMono_of_four129 Hp HA HB HV (vebRest129_of_xmono145 HX HD)

/-- 逆向き — 分割が本当に分割であることの記録。 -/
theorem vebRestDiff143_of129 (H : VebRest129) : VebRestDiff145 :=
  fun a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hcl _ =>
    H a b hbA hbB hsA hsB hWa hWb hfa hfb hlt hcl

/-- **左辺の `K` 標準性を Buchholz 標準性に緩めた形。** -/
def XMonoLoose145 : Prop :=
  ∀ (a b : BT), btLe72 1 (BT.D 0 a) = true → btLe72 1 (BT.D 0 b) = true →
    BT.isStd a = true → BT.isStd (BT.D 0 b) = true →
    le (reg 1) (dict a) = true → le (reg 1) (dict b) = true →
    lastFire92 (dict a) = false → lastFire92 (dict b) = false →
    lt (hiW89 (dict a)) (hiW89 (dict b)) = true →
    sameExp145 a b = true → xok145 a b = true

/-- **緩めた形は偽 — §101 の対がそのまま反例。**  仮定は `BT.isStd (ψ₀ a)` 以外
    ぜんぶ成り立ち、最後の一歩の指数は等しく、第二引数は**逆向き**に動く。 -/
theorem not_XMonoLoose145 : ¬ XMonoLoose145 := fun H =>
  Bool.noConfusion
    ((H bothBadA101 bothBadB101 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm.trans
      (show xok145 bothBadA101 bothBadB101 = false from rfl))

/-- **二つの near-miss は別の半分に居る。**  §101 の対は同じ指数の側 (`XMono145` の反例)、
    §81 の対は違う指数の側。行は (§101 の対の指数一致, `X_a < X_b`, `X_b < X_a`,
    §81 の対の指数一致, §101 の左辺の `K` 標準性, §81 の左辺の `K` 標準性)。 -/
theorem nearMiss145 :
    (sameExp145 bothBadA101 bothBadB101, xok145 bothBadA101 bothBadB101,
     xok145 bothBadB101 bothBadA101, sameExp145 cexA89 cexB89,
     BT.isStd (BT.D 0 bothBadA101), BT.isStd (BT.D 0 cexA89))
    = (true, false, true, false, false, false) := rfl

end

/-! ### §145.7 第二の門の測定 (凍結) -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict collapse reg wcnf sub1 logOm divAP subAP mulL)
open TM TM.Term
open Evidence.WF

/-- `VebRest129` の仮定を満たす項 — 段 1 以下、`K` 標準、`Ω₁` 以上、最後の対が発火しない。 -/
def qual145 (n : Nat) : List BT :=
  ((stdTab130 n).flatten).filter (fun a =>
    btLe72 1 a && BT.isStd (BT.D 0 a) && le (reg 1) (dict a) && !(lastFire92 (dict a)))

def dat145 (a : BT) : Term × Option (Term × Term) × Term :=
  (hiW89 (dict a), lastStep129 (dict a), accW89 (dict a))

/-- (前提が成る組, 指数が違う組, そのうち経路 2 が閉じない組,
     指数が等しい組, そのうち経路 1 が閉じない組 = `XMono145` を外す組) -/
def cenW145 (P : List BT) : Nat × Nat × Nat × Nat × Nat :=
  let D := P.map dat145
  let prs := D.flatMap (fun x => D.map (fun y => (x, y)))
  let fire := prs.filter (fun q => lt q.1.1 q.2.1)
  let sameE : (Term × Option (Term × Term) × Term) × (Term × Option (Term × Term) × Term) → Bool :=
    fun q => match q.1.2.1, q.2.2.1 with | some pa, some pb => pa.1 == pb.1 | _, _ => false
  let rt2b : (Term × Option (Term × Term) × Term) × (Term × Option (Term × Term) × Term) → Bool :=
    fun q => match q.2.2.1 with | some pb => lt q.1.2.2 pb.2 | none => false
  let rt1b : (Term × Option (Term × Term) × Term) × (Term × Option (Term × Term) × Term) → Bool :=
    fun q => match q.1.2.1, q.2.2.1 with
             | some pa, some pb => (pa.1 == pb.1) && lt pa.2 pb.2 | _, _ => false
  (fire.length, fire.countP (fun q => !(sameE q)),
   fire.countP (fun q => !(sameE q) && !(rt2b q)),
   fire.countP sameE, fire.countP (fun q => sameE q && !(rt1b q)))

/-! **母集団の大きさ。**  記号数 9・11・12 まで全数。§129.5 の 278 本がいちばん小さい行。 -/

#guard ((qual145 8).length, (qual145 10).length, (qual145 11).length) == (278, 1327, 2962)

/-! **`XMono145` は測ったかぎり真、しかも空虚ではない。**  記号数 12 までの
`K` 標準な 2962 本から作れる 4377054 組が前提を満たし、そのうち **1336152 組**で
最後の一歩の指数が等しく、**その全部で経路 1 が閉じる**。
指数が違う 3040902 組のほうは経路 2 だけでは足りない (2075886 組が残り、
そこは `closed117` が拾う) — だから分割は `XMono145` の側に重みを寄せている。 -/

#guard cenW145 (qual145 8) == (38262, 25377, 21353, 12885, 0)
#guard cenW145 (qual145 10) == (877309, 601152, 444590, 276157, 0)
#guard cenW145 (qual145 11) == (4377054, 3040902, 2075886, 1336152, 0)

#print axioms vebRest129_of_xmono145
#print axioms not_XMonoLoose145
#print axioms nearMiss145

end
end Evidence.Region
