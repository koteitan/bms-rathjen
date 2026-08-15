import Evidence.WF
/-
Evidence/CNVOps.lean — `CNV` IS CLOSED UNDER `plus` AND `ω^·`

`Evidence/WF.lean` §7.6 proves the FRAGMENT closed under the operations its clients build
terms with (`frag_toList`, `frag_ofList`, `frag_plus`).  `CNV` is `Frag` plus [Rathjen,
1991] 2.1(iii)'s descending condition, and every client that builds a value out of `plus`
and `omegaNF` needs the same closure one notch up — `Evidence/RegionV.lean`'s `sumVal` is
built from exactly those two.

WHY IT IS NOT JUST `frag_*` AGAIN.  The descending condition is what `plus` exists to
maintain (2.6(ii): drop the components of α below β's head), so the proof has to see that
`filter (le b₁ ·)` over a DESCENDING list keeps a PREFIX — and that needs transitivity of
`le`, which `frag_plus` never had to touch.  `filter_eq_take` below is that step, and it is
the only place in the file where an order fact is used.

    descL       adjacent components descend
    cnvL        every component is additively principal and `CNV`
    cnv_plus    CNV s → CNV t → CNV (plus s t)
    cnv_omegaNF CNV a → CNV (ω^a)

`cnv_omegaNF` walks [Rathjen, 1991] 2.6(vi)–(vii) branch by branch; every branch lands on
either `a` itself, `φ̄0a`, or `φ̄0(γ ⊕ n)` with `γ` a PREFIX of `a`'s components, and the
prefix is `CNV` by the same two list lemmas.
-/

namespace Evidence.WF

open TM Term

/-! ## §16 The list view of a `CNV` term -/

/-- 成分が隣り合って降順か。 -/
def descL : List Term → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => le b a && descL (b :: t)

/-- 成分がすべて加法主要かつ `CNV` か。 -/
def cnvL (l : List Term) : Bool := l.all (fun x => x.isAP && CNV x)

theorem cnvL_cons {a : Term} {l : List Term} :
    cnvL (a :: l) = true ↔ (a.isAP = true ∧ CNV a = true) ∧ cnvL l = true := by
  constructor
  · intro h
    have h' := (List.all_cons ..).symm.trans h
    have h2 := (Bool.and_eq_true _ _).mp h'
    exact ⟨(Bool.and_eq_true _ _).mp h2.1, h2.2⟩
  · intro ⟨⟨h1, h2⟩, h3⟩
    show ((a.isAP && CNV a) && cnvL l) = true
    rw [h1, h2, h3]
    rfl

theorem descL_cons {a b : Term} {t : List Term} :
    descL (a :: b :: t) = true ↔ le b a = true ∧ descL (b :: t) = true := by
  constructor
  · intro h; exact (Bool.and_eq_true _ _).mp h
  · intro ⟨h1, h2⟩; show (_ && _) = true; rw [h1, h2]; rfl

/-- 先頭を落としても降順。 -/
theorem descL_tail : ∀ {a : Term} {l : List Term}, descL (a :: l) = true → descL l = true := by
  intro a l h
  cases l with
  | nil => rfl
  | cons b t => exact (descL_cons.mp h).2

theorem descL_take : ∀ (k : Nat) (l : List Term), descL l = true → descL (l.take k) = true := by
  intro k
  induction k with
  | zero => intro l _; rfl
  | succ j ih =>
    intro l h
    cases l with
    | nil => rfl
    | cons a t =>
      show descL (a :: t.take j) = true
      cases t with
      | nil => cases j <;> rfl
      | cons b u =>
        cases j with
        | zero => rfl
        | succ i =>
          refine descL_cons.mpr ⟨(descL_cons.mp h).1, ?_⟩
          exact ih (b :: u) (descL_cons.mp h).2

theorem cnvL_take : ∀ (k : Nat) (l : List Term), cnvL l = true → cnvL (l.take k) = true := by
  intro k l h
  show (l.take k).all _ = true
  rw [List.all_eq_true]
  intro x hx
  have := List.all_eq_true.mp h
  exact this x (List.mem_of_mem_take hx)

theorem hdLe_eq_of_toList {b a c : Term} {rest : List Term} (h : toList b = c :: rest) :
    hdLe b a = le c a := by
  cases b with
  | zero =>
    have hz : toList (zero : Term) = [] := rfl
    rw [hz] at h
    exact absurd h (by simp)
  | add u v => injection h with h1 _; show le u a = _; rw [h1]
  | M => injection h with h1 _; show le M a = _; rw [h1]
  | omg u => injection h with h1 _; show le (omg u) a = _; rw [h1]
  | phi u v => injection h with h1 _; show le (phi u v) a = _; rw [h1]
  | psi u v => injection h with h1 _; show le (psi u v) a = _; rw [h1]
  | Z u => injection h with h1 _; show le (Z u) a = _; rw [h1]

/-- `CNV` の項は、降順の加法主要成分の列。 -/
theorem cnv_toList : ∀ (t : Term), CNV t = true →
    cnvL (toList t) = true ∧ descL (toList t) = true := by
  intro t
  induction t with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | phi a b _ _ =>
    intro h
    refine ⟨?_, rfl⟩
    show cnvL [phi a b] = true
    rw [cnvL_cons]
    exact ⟨⟨rfl, h⟩, rfl⟩
  | add a b _ ihb =>
    intro h
    obtain ⟨hap, hca, hcb, hhd⟩ := cnv_add h
    obtain ⟨hcl, hdl⟩ := ihb hcb
    have he : toList (add a b) = a :: toList b := rfl
    rw [he]
    refine ⟨cnvL_cons.mpr ⟨⟨hap, hca⟩, hcl⟩, ?_⟩
    cases hb : toList b with
    | nil => rfl
    | cons c rest =>
      refine descL_cons.mpr ⟨?_, by rw [← hb]; exact hdl⟩
      rw [← hdLe_eq_of_toList (a := a) hb]
      exact hhd

theorem toList_ofList : ∀ (l : List Term), (∀ x ∈ l, x.isAP = true) → toList (ofList l) = l
  | [], _ => rfl
  | [a], h => by
    have ha := h a (by simp)
    show toList a = [a]
    cases a with
    | zero => exact Bool.noConfusion ha
    | add _ _ => exact Bool.noConfusion ha
    | M => rfl | omg _ => rfl | phi _ _ => rfl | psi _ _ => rfl | Z _ => rfl
  | a :: b :: t, h => by
    show toList (add a (ofList (b :: t))) = _
    show a :: toList (ofList (b :: t)) = _
    rw [toList_ofList (b :: t) (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem hdLe_ofList {a b : Term} {t : List Term} (hb : b.isAP = true) :
    hdLe (ofList (b :: t)) a = le b a := by
  cases t with
  | nil =>
    show hdLe b a = _
    cases b with
    | zero => exact Bool.noConfusion hb
    | add _ _ => exact Bool.noConfusion hb
    | M => rfl | omg _ => rfl | phi _ _ => rfl | psi _ _ => rfl | Z _ => rfl
  | cons c u => rfl

/-- 降順の加法主要成分の列は `CNV` の項を組み立てる。 -/
theorem cnv_ofList : ∀ (l : List Term), cnvL l = true → descL l = true →
    CNV (ofList l) = true
  | [], _, _ => rfl
  | [a], h, _ => (cnvL_cons.mp h).1.2
  | a :: b :: t, h, hd => by
    obtain ⟨⟨hap, hca⟩, hrest⟩ := cnvL_cons.mp h
    obtain ⟨hle, hd2⟩ := descL_cons.mp hd
    have hbap : b.isAP = true := (cnvL_cons.mp hrest).1.1
    show (a.isAP && CNV a && CNV (ofList (b :: t)) && hdLe (ofList (b :: t)) a) = true
    rw [hap, hca, cnv_ofList (b :: t) hrest hd2, hdLe_ofList hbap, hle]
    rfl

/-! ## §17 `plus` -/

/-- 降順の列で `le b₁ ·` を通すのは、前を切り取るのと同じ。 -/
theorem filter_eq_take : ∀ (b1 : Term) (l : List Term), cnvL l = true → descL l = true →
    CNV b1 = true → ∃ k, l.filter (fun a => le b1 a) = l.take k := by
  intro b1 l
  induction l with
  | nil => intro _ _ _; exact ⟨0, rfl⟩
  | cons a t ih =>
    intro hc hd hb1
    obtain ⟨⟨hap, hca⟩, hct⟩ := cnvL_cons.mp hc
    cases hle : le b1 a with
    | true =>
      obtain ⟨k, hk⟩ := ih hct (descL_tail hd) hb1
      refine ⟨k + 1, ?_⟩
      rw [List.filter_cons_of_pos (by rw [hle]), hk]
      rfl
    | false =>
      refine ⟨0, ?_⟩
      rw [List.filter_cons_of_neg (by rw [hle]; exact Bool.noConfusion)]
      -- everything after `a` is `≤ a`, so `b1 ≤ ·` fails there too
      have hnil : ∀ (u : List Term), cnvL u = true → descL (a :: u) = true →
          u.filter (fun x => le b1 x) = [] := by
        intro u
        induction u with
        | nil => intro _ _; rfl
        | cons c v ihv =>
          intro hcu hdu
          obtain ⟨⟨hcap, hccv⟩, hcv⟩ := cnvL_cons.mp hcu
          have hca' : le c a = true := (descL_cons.mp hdu).1
          have hnc : le b1 c = false := by
            cases hbc : le b1 c with
            | false => rfl
            | true =>
              exact absurd (le_trans (frag_of_cnv _ hb1) (frag_of_cnv _ hccv)
                (frag_of_cnv _ hca) hbc hca') (by rw [hle]; exact Bool.noConfusion)
          rw [List.filter_cons_of_neg (by rw [hnc]; exact Bool.noConfusion)]
          refine ihv hcv ?_
          cases v with
          | nil => rfl
          | cons d w =>
            refine descL_cons.mpr ⟨?_, descL_tail (descL_tail hdu)⟩
            exact le_trans (frag_of_cnv _ (cnvL_cons.mp hcv).1.2) (frag_of_cnv _ hccv)
              (frag_of_cnv _ hca) (descL_cons.mp (descL_tail hdu)).1 hca'
      exact hnil t hct hd

theorem getLast?_mem : ∀ {a : Term} {l : List Term}, l.getLast? = some a → a ∈ l := by
  intro a l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons c t ih =>
    intro h
    cases t with
    | nil =>
      have : ([c] : List Term).getLast? = some c := rfl
      rw [this] at h
      injection h with h1
      rw [← h1]
      exact List.Mem.head _
    | cons d u =>
      rw [List.getLast?_cons_of_ne_nil (by simp)] at h
      exact List.Mem.tail c (ih h)

theorem descL_append : ∀ (l1 l2 : List Term), descL l1 = true → descL l2 = true →
    (∀ a b t, l1.getLast? = some a → l2 = b :: t → le b a = true) →
    descL (l1 ++ l2) = true := by
  intro l1
  induction l1 with
  | nil => intro l2 _ h2 _; exact h2
  | cons a t ih =>
    intro l2 h1 h2 hj
    cases t with
    | nil =>
      cases l2 with
      | nil => exact h1
      | cons b u =>
        exact descL_cons.mpr ⟨hj a b u rfl rfl, h2⟩
    | cons c v =>
      refine descL_cons.mpr ⟨(descL_cons.mp h1).1, ?_⟩
      refine ih l2 (descL_cons.mp h1).2 h2 ?_
      intro x y w hx hy
      refine hj x y w ?_ hy
      rw [List.getLast?_cons_of_ne_nil (by simp)]
      exact hx

/-- **`CNV` は `plus` で閉じる。** -/
theorem cnv_plus {s t : Term} (hs : CNV s = true) (ht : CNV t = true) :
    CNV (plus s t) = true := by
  obtain ⟨hcs, hds⟩ := cnv_toList s hs
  obtain ⟨hct, hdt⟩ := cnv_toList t ht
  show CNV (match toList t with
            | [] => s
            | b1 :: _ => ofList ((toList s).filter (fun a => le b1 a) ++ toList t)) = true
  cases hl : toList t with
  | nil => exact hs
  | cons b1 rest =>
    rw [hl] at hct hdt
    obtain ⟨⟨hb1ap, hb1⟩, _⟩ := cnvL_cons.mp hct
    obtain ⟨k, hk⟩ := filter_eq_take b1 (toList s) hcs hds hb1
    show CNV (ofList ((toList s).filter (fun a => le b1 a) ++ (b1 :: rest))) = true
    rw [hk]
    refine cnv_ofList _ ?_ ?_
    · show ((toList s).take k ++ (b1 :: rest)).all _ = true
      rw [List.all_eq_true]
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact List.all_eq_true.mp (cnvL_take k (toList s) hcs) x h
      · exact List.all_eq_true.mp hct x h
    · refine descL_append _ _ (descL_take k (toList s) hds) hdt ?_
      intro a b w ha hb
      injection hb with hb1eq _
      rw [← hb1eq]
      have hmem : a ∈ (toList s).filter (fun x => le b1 x) := by
        rw [hk]; exact getLast?_mem ha
      exact (List.mem_filter.mp hmem).2

/-! ## §18 `ω^·`

`omegaNF a = φ̄0a` once `a` is `CNV` — the two guards `M < a` and `a = M` are both closed by
`cnv_lt_M` — and `phiNF 0 a` lands, branch by branch, on `a`, on `φ̄0a`, or on
`φ̄0(γ ⊕ n)` with `γ = (splitFin a).1` a PREFIX of `a`'s components. -/

theorem cnv_take_ofList {b : Term} (h : CNV b = true) (k : Nat) :
    CNV (ofList ((toList b).take k)) = true := by
  obtain ⟨hc, hd⟩ := cnv_toList b h
  exact cnv_ofList _ (cnvL_take k _ hc) (descL_take k _ hd)

theorem cnv_splitFin {b : Term} (h : CNV b = true) : CNV (splitFin b).1 = true :=
  cnv_take_ofList h _

theorem phiNFdefault_zero_eq (b : Term) : phiNFdefault zero b = phi zero b := by
  show (if (b == zero) && (zero : Term).isSC then zero else phi zero b) = _
  cases hb : (b == zero) with
  | true => rfl
  | false => rfl

theorem cnv_phi_zero {b : Term} (h : CNV b = true) : CNV (phi zero b) = true := by
  show (CNV zero && CNV b) = true
  rw [h]; rfl

theorem cnv_phiNFsucc {b : Term} (h : CNV b = true) : CNV (phiNFsucc zero b) = true := by
  have hg : CNV (splitFin b).1 = true := cnv_splitFin h
  have hdef : CNV (phiNFdefault zero b) = true := by
    rw [phiNFdefault_zero_eq]; exact cnv_phi_zero h
  unfold phiNFsucc
  split
  rename_i heq
  rw [heq] at hg
  split
  · split <;> (split <;>
      first | exact cnv_phi_zero (cnv_plus hg (cnv_ofNat _)) | exact hdef)
  · exact hdef

theorem cnv_phiNF_zero {b : Term} (h : CNV b = true) : CNV (phiNF zero b) = true := by
  unfold phiNF
  split
  · exact h
  · split
    · split
      · exact h
      · exact cnv_phiNFsucc h
    · exact cnv_phiNFsucc h

/-- **`CNV` は `ω^·` で閉じる。** -/
theorem cnv_omegaNF {a : Term} (h : CNV a = true) : CNV (omegaNF a) = true := by
  have hMa : lt M a = false :=
    lt_asymm_inT (inT_of_cnv a h) (show inT (M : Term) = true from rfl) (cnv_lt_M a h)
  have haM : (a == M) = false := by
    cases hb : (a == M) with
    | false => rfl
    | true => rw [eq_of_beq hb] at h; exact Bool.noConfusion h
  show CNV (if lt M a then omg a else if a == M then M else phiNF zero a) = true
  rw [if_neg (by rw [hMa]; exact Bool.noConfusion), if_neg (by rw [haM]; exact Bool.noConfusion)]
  exact cnv_phiNF_zero h

end Evidence.WF
