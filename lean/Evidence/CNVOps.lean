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

/-! ## §19 `plus` IS ASSOCIATIVE ON `CNV`

`plus` is [Rathjen, 1991] 2.6(ii): drop the components of `α` below `β`'s head, then
concatenate.  Associativity is therefore NOT formal — it is a statement about the two
filters, and it is FALSE without the descending condition.  With it, `filter_eq_take`'s
neighbour `filter_nil_of_head` splits the proof in two:

    c₁ ≤ b₁     the outer filter keeps everything the inner one kept
    c₁ > b₁     the inner filter is invisible — everything ≥ c₁ is already ≥ b₁

`Evidence/RegionV.lean` §14 needs it for `sumVal (app r s) = sumVal r ⊕ sumVal s`, without
which no `∀ n` fact about the region's value can be stated, `fs` being defined by `app`. -/

theorem toList_eq_nil : ∀ (t : Term), toList t = [] → t = zero := by
  intro t
  cases t with
  | zero => intro _; rfl
  | add u v => intro h; exact absurd (show u :: toList v = [] from h) (by simp)
  | M => intro h; exact absurd (show [(M : Term)] = [] from h) (by simp)
  | omg u => intro h; exact absurd (show [omg u] = [] from h) (by simp)
  | phi u v => intro h; exact absurd (show [phi u v] = [] from h) (by simp)
  | psi u v => intro h; exact absurd (show [psi u v] = [] from h) (by simp)
  | Z u => intro h; exact absurd (show [Z u] = [] from h) (by simp)

theorem cnv_ofList_toList : ∀ (t : Term), CNV t = true → ofList (toList t) = t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | phi _ _ _ _ => intro _; rfl
  | add a b _ ihb =>
    intro h
    obtain ⟨_, _, hcb, hhd⟩ := cnv_add h
    have hbz : b ≠ zero := by
      intro hz; rw [hz] at hhd; exact Bool.noConfusion hhd
    show ofList (a :: toList b) = add a b
    cases hbl : toList b with
    | nil => exact absurd (toList_eq_nil b hbl) hbz
    | cons c u =>
      show add a (ofList (c :: u)) = add a b
      rw [← hbl, ihb hcb]

theorem toList_plus {s t : Term} (hs : CNV s = true) (ht : CNV t = true)
    {b1 : Term} {rest : List Term} (hl : toList t = b1 :: rest) :
    toList (plus s t) = (toList s).filter (fun a => le b1 a) ++ toList t := by
  obtain ⟨hcs, _⟩ := cnv_toList s hs
  obtain ⟨hct, _⟩ := cnv_toList t ht
  have hall : ∀ x ∈ (toList s).filter (fun a => le b1 a) ++ toList t, x.isAP = true := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcs x ((List.mem_filter.mp h).1))).1
    · exact ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hct x h)).1
  show toList (match toList t with
      | [] => s
      | b :: _ => ofList ((toList s).filter (fun a => le b a) ++ toList t)) = _
  rw [hl]
  show toList (ofList ((toList s).filter (fun a => le b1 a) ++ (b1 :: rest))) = _
  rw [hl] at hall
  rw [toList_ofList _ hall]

/-- 先頭より上のものは、その後ろにも無い。 -/
theorem filter_nil_of_head {b1 : Term} (hb1 : CNV b1 = true) :
    ∀ (a : Term) (u : List Term), CNV a = true → cnvL u = true → descL (a :: u) = true →
      le b1 a = false → (a :: u).filter (fun x => le b1 x) = [] := by
  intro a u hca hcu hd hle
  rw [List.filter_cons_of_neg (by rw [hle]; exact Bool.noConfusion)]
  have hnil : ∀ (v : List Term), cnvL v = true → descL (a :: v) = true →
      v.filter (fun x => le b1 x) = [] := by
    intro v
    induction v with
    | nil => intro _ _; rfl
    | cons c w ihw =>
      intro hcv hdv
      obtain ⟨⟨_, hccv⟩, hcw⟩ := cnvL_cons.mp hcv
      have hca' : le c a = true := (descL_cons.mp hdv).1
      have hnc : le b1 c = false := by
        cases hbc : le b1 c with
        | false => rfl
        | true =>
          exact absurd (le_trans (frag_of_cnv _ hb1) (frag_of_cnv _ hccv)
            (frag_of_cnv _ hca) hbc hca') (by rw [hle]; exact Bool.noConfusion)
      rw [List.filter_cons_of_neg (by rw [hnc]; exact Bool.noConfusion)]
      refine ihw hcw ?_
      cases w with
      | nil => rfl
      | cons d z =>
        refine descL_cons.mpr ⟨?_, descL_tail (descL_tail hdv)⟩
        exact le_trans (frag_of_cnv _ (cnvL_cons.mp hcw).1.2) (frag_of_cnv _ hccv)
          (frag_of_cnv _ hca) (descL_cons.mp (descL_tail hdv)).1 hca'
  exact hnil u hcu hd

theorem filter_of_imp (p q : Term → Bool) : ∀ (l : List Term),
    (∀ x ∈ l, p x = true → q x = true) → (l.filter q).filter p = l.filter p := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    cases hq : q a with
    | true =>
      rw [List.filter_cons_of_pos (by rw [hq])]
      cases hp : p a with
      | true =>
        rw [List.filter_cons_of_pos (by rw [hp]), List.filter_cons_of_pos (by rw [hp])]
        rw [ih (fun x hx => h x (List.mem_cons_of_mem a hx))]
      | false =>
        rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.noConfusion),
          List.filter_cons_of_neg (by rw [hp]; exact Bool.noConfusion)]
        exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    | false =>
      rw [List.filter_cons_of_neg (by rw [hq]; exact Bool.noConfusion)]
      have hpa : p a = false := by
        cases hp : p a with
        | false => rfl
        | true => rw [h a (List.Mem.head _) hp] at hq; exact Bool.noConfusion hq
      rw [List.filter_cons_of_neg (by rw [hpa]; exact Bool.noConfusion)]
      exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

theorem filter_self_of_all (p : Term → Bool) : ∀ (l : List Term),
    (∀ x ∈ l, p x = true) → l.filter p = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    rw [List.filter_cons_of_pos (by rw [h a (List.Mem.head _)]),
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- 先頭が分かっているときの `plus` の展開。 -/
theorem plus_eq {s t d : Term} {rest : List Term} (hl : toList t = d :: rest) :
    plus s t = ofList ((toList s).filter (fun x => le d x) ++ toList t) := by
  show (match toList t with
    | [] => s
    | b :: _ => ofList ((toList s).filter (fun x => le b x) ++ toList t)) = _
  rw [hl]

/-- **`plus` は `CNV` 上で結合的。** -/
theorem plus_assoc {a b c : Term} (ha : CNV a = true) (hb : CNV b = true) (hc : CNV c = true) :
    plus (plus a b) c = plus a (plus b c) := by
  obtain ⟨hca, hda⟩ := cnv_toList a ha
  obtain ⟨hcb, hdb⟩ := cnv_toList b hb
  obtain ⟨hcc, hdc⟩ := cnv_toList c hc
  cases hC : toList c with
  | nil =>
    have hcz : c = zero := toList_eq_nil c hC
    rw [hcz]
    show plus (plus a b) zero = plus a (plus b zero)
    rfl
  | cons c1 C' =>
    rw [hC] at hcc hdc
    obtain ⟨⟨_, hcc1⟩, _⟩ := cnvL_cons.mp hcc
    cases hB : toList b with
    | nil =>
      have hbz : b = zero := toList_eq_nil b hB
      have h1 : plus a b = a := by rw [hbz]; rfl
      have h2 : plus b c = c := by
        rw [plus_eq (s := b) hC, hB]
        show ofList (([] : List Term) ++ toList c) = c
        show ofList (toList c) = c
        exact cnv_ofList_toList c hc
      rw [h1, h2]
    | cons b1 B' =>
      rw [hB] at hcb hdb
      obtain ⟨⟨_, hcb1⟩, hcB'⟩ := cnvL_cons.mp hcb
      have hab : toList (plus a b) = (toList a).filter (fun x => le b1 x) ++ toList b :=
        toList_plus ha hb hB
      have hbc : toList (plus b c) = (toList b).filter (fun x => le c1 x) ++ toList c :=
        toList_plus hb hc hC
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
          have hcx : CNV x = true :=
            ((Bool.and_eq_true _ _).mp
              (List.all_eq_true.mp hca x (List.mem_filter.mp hx).1)).2
          exact le_trans (frag_of_cnv _ hcc1) (frag_of_cnv _ hcb1) (frag_of_cnv _ hcx)
            hcb1' hbx
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
          rw [hB]; exact filter_nil_of_head hcc1 b1 B' hcb1 hcB' hdb hcb1'
        have hswap : ((toList a).filter (fun x => le b1 x)).filter (fun x => le c1 x)
            = (toList a).filter (fun x => le c1 x) := by
          refine filter_of_imp _ _ _ ?_
          intro x hx hcx
          have hxc : CNV x = true :=
            ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hca x hx)).2
          have hbc1 : le b1 c1 = true := by
            have h1 : lt b1 c1 = true :=
              lt_of_not_le (frag_of_cnv _ hcc1) (frag_of_cnv _ hcb1) hcb1'
            show (b1 == c1 || lt b1 c1) = true
            rw [h1]
            exact Bool.or_true _
          exact le_trans (frag_of_cnv _ hcb1) (frag_of_cnv _ hcc1) (frag_of_cnv _ hxc)
            hbc1 hcx
        have hbc' : toList (plus b c) = c1 :: C' := by
          rw [hbc, hbn, hC]; rfl
        rw [hL, plus_eq (s := a) hbc', hbc, List.filter_append, hswap, hbn,
          List.append_nil, List.nil_append]

/-! ## §20 THE ORDER, READ ON THE COMPONENT LIST

`TM/Order.lean` compares terms through the `add` constructor: `lt_add_add` is one
lexicographic step, `lt_phi_add` and `lt_add_phi` are the two ragged ends.  Since a `CNV`
term IS its descending component list (`cnv_ofList_toList`), those three facts assemble
into ONE equation — `lt` on terms is `ltL` on lists — and everything `plus` does is a list
operation, so every fact about `plus` below is proved on lists and read back.

This is the layer `Evidence/WF.lean` never needed: its clients build terms, they do not
take them apart.  `Evidence/RegionV.lean` §14's `PrefixLim` does. -/

/-- 成分列の辞書式順序。 -/
def ltL : List Term → List Term → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => if a = b then ltL s t else lt a b

theorem lt_zero_left {x : Term} (h : x ≠ zero) : lt zero x = true :=
  ltF_left_zero (by show 1 ≤ 2 * ((zero : Term).deg + x.deg) + 8; omega) h

theorem lt_zero_right (x : Term) : lt x zero = false := ltF_right_zero _ x

theorem ofList_ne_zero : ∀ (l : List Term), cnvL l = true → l ≠ [] → ofList l ≠ zero
  | [], _, h => absurd rfl h
  | [a], hc, _ => by
      have hap := (cnvL_cons.mp hc).1.1
      show a ≠ zero
      intro hz; rw [hz] at hap; exact Bool.noConfusion hap
  | _ :: _ :: _, _, _ => by intro hc; exact Term.noConfusion hc

/-- **順序は成分列で読める。** -/
theorem lt_ofList : ∀ (l1 l2 : List Term), cnvL l1 = true → cnvL l2 = true →
    lt (ofList l1) (ofList l2) = ltL l1 l2 := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 _ hc2
    cases l2 with
    | nil => exact lt_irrefl zero
    | cons b t =>
      show lt zero (ofList (b :: t)) = true
      exact lt_zero_left (ofList_ne_zero (b :: t) hc2 (by simp))
  | cons a s ih =>
    intro l2 hc1 hc2
    cases l2 with
    | nil => exact lt_zero_right _
    | cons b t =>
      obtain ⟨⟨hapa, hcna⟩, hcs⟩ := cnvL_cons.mp hc1
      obtain ⟨⟨hapb, hcnb⟩, hct⟩ := cnvL_cons.mp hc2
      cases s with
      | nil =>
        cases t with
        | nil =>
          show lt a b = (if a = b then ltL [] [] else lt a b)
          by_cases hab : a = b
          · rw [if_pos hab, hab]; exact lt_irrefl b
          · rw [if_neg hab]
        | cons c u =>
          obtain ⟨p, q, rfl⟩ := eq_phi_of_isAP_cnv hcna hapa
          show lt (phi p q) (add b (ofList (c :: u))) = (if phi p q = b then ltL [] (c :: u)
            else lt (phi p q) b)
          rw [lt_phi_add]
          by_cases hab : phi p q = b
          · rw [if_pos hab]
            show ((phi p q == b) || lt (phi p q) b) = true
            rw [hab]
            simp
          · rw [if_neg hab]
            show ((phi p q == b) || lt (phi p q) b) = _
            rw [show (phi p q == b) = false from by
              cases h : (phi p q == b) with
              | false => rfl
              | true => exact absurd (eq_of_beq h) hab]
            exact Bool.false_or _
      | cons c u =>
        cases t with
        | nil =>
          obtain ⟨p, q, rfl⟩ := eq_phi_of_isAP_cnv hcnb hapb
          show lt (add a (ofList (c :: u))) (phi p q)
            = (if a = phi p q then ltL (c :: u) [] else lt a (phi p q))
          rw [lt_add_phi]
          by_cases hab : a = phi p q
          · rw [if_pos hab, hab]; exact lt_irrefl _
          · rw [if_neg hab]
        | cons d v =>
          show lt (add a (ofList (c :: u))) (add b (ofList (d :: v)))
            = (if a = b then ltL (c :: u) (d :: v) else lt a b)
          by_cases heq : add a (ofList (c :: u)) = add b (ofList (d :: v))
          · injection heq with h1 h2
            rw [if_pos h1, ← ih (d :: v) hcs hct, ← h2, h1, lt_irrefl, lt_irrefl]
          · rw [lt_add_add heq, ih (d :: v) hcs hct]

theorem ltL_append_left : ∀ (Q X Y : List Term), ltL (Q ++ X) (Q ++ Y) = ltL X Y
  | [], _, _ => rfl
  | a :: Q, X, Y => by
    show (if a = a then ltL (Q ++ X) (Q ++ Y) else lt a a) = ltL X Y
    rw [if_pos rfl, ltL_append_left Q X Y]

theorem lt_eq_ltL {s t : Term} (hs : CNV s = true) (ht : CNV t = true) :
    lt s t = ltL (toList s) (toList t) := by
  obtain ⟨hcs, _⟩ := cnv_toList s hs
  obtain ⟨hct, _⟩ := cnv_toList t ht
  have h := lt_ofList (toList s) (toList t) hcs hct
  rw [cnv_ofList_toList s hs, cnv_ofList_toList t ht] at h
  exact h

/-- 左に足すと真に増える。 -/
theorem ltL_filter_append {x1 : Term} (hx1 : CNV x1 = true) :
    ∀ (A X' : List Term), cnvL A = true → descL A = true →
    ltL A (A.filter (fun y => le x1 y) ++ (x1 :: X')) = true := by
  intro A
  induction A with
  | nil => intro X' _ _; rfl
  | cons a A' ih =>
    intro X' hc hd
    obtain ⟨⟨_, hca⟩, hcA'⟩ := cnvL_cons.mp hc
    cases hle : le x1 a with
    | true =>
      rw [List.filter_cons_of_pos (by rw [hle])]
      show (if a = a then ltL A' (A'.filter (fun y => le x1 y) ++ (x1 :: X')) else lt a a) = true
      rw [if_pos rfl]
      exact ih X' hcA' (descL_tail hd)
    | false =>
      rw [filter_nil_of_head hx1 a A' hca hcA' hd hle]
      show (if a = x1 then ltL A' X' else lt a x1) = true
      have hne : a ≠ x1 := by
        intro hc'
        rw [hc', le_self x1] at hle
        exact Bool.noConfusion hle
      rw [if_neg hne]
      exact lt_of_not_le (frag_of_cnv _ hx1) (frag_of_cnv _ hca) hle

/-- 右の引数を上げると真に増える (成分列の側)。 -/
theorem ltL_filter_mono {x1 y1 : Term} (hx1 : CNV x1 = true) (hy1 : CNV y1 = true)
    (hlt : lt x1 y1 = true) :
    ∀ (A X' Y' : List Term), cnvL A = true → descL A = true →
    ltL (A.filter (fun z => le x1 z) ++ (x1 :: X'))
        (A.filter (fun z => le y1 z) ++ (y1 :: Y')) = true := by
  intro A
  induction A with
  | nil =>
    intro X' Y' _ _
    show (if x1 = y1 then ltL X' Y' else lt x1 y1) = true
    rw [if_neg (ne_of_ltF hlt)]
    exact hlt
  | cons a A' ih =>
    intro X' Y' hc hd
    obtain ⟨⟨_, hca⟩, hcA'⟩ := cnvL_cons.mp hc
    cases hley : le y1 a with
    | true =>
      have hlex : le x1 a = true :=
        le_trans (frag_of_cnv _ hx1) (frag_of_cnv _ hy1) (frag_of_cnv _ hca)
          (le_of_lt hlt) hley
      rw [List.filter_cons_of_pos (by rw [hlex]), List.filter_cons_of_pos (by rw [hley])]
      show (if a = a then ltL (A'.filter (fun z => le x1 z) ++ (x1 :: X'))
        (A'.filter (fun z => le y1 z) ++ (y1 :: Y')) else lt a a) = true
      rw [if_pos rfl]
      exact ih X' Y' hcA' (descL_tail hd)
    | false =>
      rw [filter_nil_of_head hy1 a A' hca hcA' hd hley]
      cases hlex : le x1 a with
      | true =>
        rw [List.filter_cons_of_pos (by rw [hlex])]
        show (if a = y1 then ltL (A'.filter (fun z => le x1 z) ++ (x1 :: X')) Y'
          else lt a y1) = true
        have hne : a ≠ y1 := by
          intro hc'
          rw [hc', le_self y1] at hley
          exact Bool.noConfusion hley
        rw [if_neg hne]
        exact lt_of_not_le (frag_of_cnv _ hy1) (frag_of_cnv _ hca) hley
      | false =>
        rw [filter_nil_of_head hx1 a A' hca hcA' hd hlex]
        show (if x1 = y1 then ltL X' Y' else lt x1 y1) = true
        rw [if_neg (ne_of_ltF hlt)]
        exact hlt

/-! ## §21 `plus` on the left: the two monotonicities -/

theorem lt_plus_left {P x : Term} (hP : CNV P = true) (hx : CNV x = true) (hxz : x ≠ zero) :
    lt P (plus P x) = true := by
  obtain ⟨hcP, hdP⟩ := cnv_toList P hP
  cases hX : toList x with
  | nil => exact absurd (toList_eq_nil x hX) hxz
  | cons x1 X' =>
    obtain ⟨hcx, _⟩ := cnv_toList x hx
    rw [hX] at hcx
    obtain ⟨⟨_, hcx1⟩, _⟩ := cnvL_cons.mp hcx
    rw [lt_eq_ltL hP (cnv_plus hP hx), toList_plus hP hx hX, hX]
    exact ltL_filter_append hcx1 (toList P) X' hcP hdP

theorem le_plus_left {P x : Term} (hP : CNV P = true) (hx : CNV x = true) :
    le P (plus P x) = true := by
  by_cases hz : x = zero
  · rw [hz]
    exact le_self P
  · exact le_of_lt (lt_plus_left hP hx hz)

/-- **`plus` は右の引数について真に単調。** -/
theorem lt_plus_right {P x y : Term} (hP : CNV P = true) (hx : CNV x = true)
    (hy : CNV y = true) (h : lt x y = true) : lt (plus P x) (plus P y) = true := by
  obtain ⟨hcP, hdP⟩ := cnv_toList P hP
  cases hY : toList y with
  | nil =>
    exfalso
    rw [toList_eq_nil y hY, lt_zero_right] at h
    exact Bool.noConfusion h
  | cons y1 Y' =>
    have hyz : y ≠ zero := by
      intro hc; rw [hc] at hY; exact absurd (show ([] : List Term) = y1 :: Y' from hY) (by simp)
    obtain ⟨hcy, _⟩ := cnv_toList y hy
    rw [hY] at hcy
    obtain ⟨⟨_, hcy1⟩, _⟩ := cnvL_cons.mp hcy
    cases hX : toList x with
    | nil =>
      rw [toList_eq_nil x hX]
      exact lt_plus_left hP hy hyz
    | cons x1 X' =>
      obtain ⟨hcx, _⟩ := cnv_toList x hx
      rw [hX] at hcx
      obtain ⟨⟨_, hcx1⟩, _⟩ := cnvL_cons.mp hcx
      have hxy : ltL (x1 :: X') (y1 :: Y') = true := by
        rw [← hX, ← hY, ← lt_eq_ltL hx hy]; exact h
      rw [lt_eq_ltL (cnv_plus hP hx) (cnv_plus hP hy),
        toList_plus hP hx hX, toList_plus hP hy hY, hX, hY]
      by_cases hxy1 : x1 = y1
      · subst hxy1
        rw [ltL_append_left]
        exact hxy
      · have hlt1 : lt x1 y1 = true := by
          have h2 : (if x1 = y1 then ltL X' Y' else lt x1 y1) = true := hxy
          rw [if_neg hxy1] at h2
          exact h2
        exact ltL_filter_mono hcx1 hcy1 hlt1 (toList P) X' Y' hcP hdP

theorem le_plus_right {P x y : Term} (hP : CNV P = true) (hx : CNV x = true)
    (hy : CNV y = true) (h : le x y = true) : le (plus P x) (plus P y) = true := by
  by_cases hxy : x = y
  · rw [hxy]; exact le_self _
  · have hlt : lt x y = true := by
      have h2 : ((x == y) || lt x y) = true := h
      rw [show (x == y) = false from by
        cases hb : (x == y) with
        | false => rfl
        | true => exact absurd (eq_of_beq hb) hxy, Bool.false_or] at h2
      exact h2
    exact le_of_lt (lt_plus_right hP hx hy hlt)

/-! ## §22 The list lemmas cofinality needs -/

theorem descL_head_ge : ∀ (l : List Term) (a : Term), cnvL (a :: l) = true →
    descL (a :: l) = true → ∀ x ∈ l, le x a = true := by
  intro l
  induction l with
  | nil => intro a _ _ x hx; exact absurd hx (by simp)
  | cons c v ih =>
    intro a hc hd x hx
    obtain ⟨⟨_, hca⟩, hcrest⟩ := cnvL_cons.mp hc
    have hcc : CNV c = true := (cnvL_cons.mp hcrest).1.2
    have hcv : cnvL v = true := (cnvL_cons.mp hcrest).2
    have hcle : le c a = true := (descL_cons.mp hd).1
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hcle
    · have hxc : le x c = true := ih c hcrest (descL_tail hd) x hx'
      have hcx : CNV x = true :=
        ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcv x hx')).2
      exact le_trans (frag_of_cnv _ hcx) (frag_of_cnv _ hcc) (frag_of_cnv _ hca) hxc hcle

theorem descL_of_append_right : ∀ (Q S : List Term), descL (Q ++ S) = true → descL S = true := by
  intro Q
  induction Q with
  | nil => intro S h; exact h
  | cons _ _ ih => intro S h; exact ih S (descL_tail h)

theorem cnvL_of_append_right (Q S : List Term) (h : cnvL (Q ++ S) = true) : cnvL S = true := by
  show S.all _ = true
  rw [List.all_eq_true]
  intro x hx
  exact List.all_eq_true.mp h x (List.mem_append.mpr (Or.inr hx))

/-- 左に足すと真に増える (成分列の側、前置きが任意)。 -/
theorem ltL_prefix_grow : ∀ (l mid : List Term), mid ≠ [] →
    cnvL (mid ++ l) = true → descL (mid ++ l) = true → ltL l (mid ++ l) = true := by
  intro l
  induction l with
  | nil =>
    intro mid hne _ _
    rw [List.append_nil]
    cases mid with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  | cons h l' ih =>
    intro mid hne hc hd
    cases mid with
    | nil => exact absurd rfl hne
    | cons m1 mid' =>
      show (if h = m1 then ltL l' (mid' ++ (h :: l')) else lt h m1) = true
      by_cases hhm : h = m1
      · rw [if_pos hhm]
        have hass : mid' ++ (h :: l') = (mid' ++ [h]) ++ l' := by
          rw [List.append_assoc]; rfl
        rw [hass]
        refine ih (mid' ++ [h]) (by simp) ?_ ?_
        · rw [← hass]; exact (cnvL_cons.mp hc).2
        · rw [← hass]; exact descL_tail hd
      · rw [if_neg hhm]
        have hle : le h m1 = true :=
          descL_head_ge (mid' ++ (h :: l')) m1 hc hd h (by simp)
        have h2 : ((h == m1) || lt h m1) = true := hle
        rw [show (h == m1) = false from by
          cases hb : (h == m1) with
          | false => rfl
          | true => exact absurd (eq_of_beq hb) hhm, Bool.false_or] at h2
        exact h2

/-- 前置きを剥がすか、前置きの中で決着するか。 -/
theorem ltL_split : ∀ (Q S W : List Term), ltL S (Q ++ W) = true →
    (∃ S', S = Q ++ S' ∧ ltL S' W = true) ∨ ltL S Q = true := by
  intro Q
  induction Q with
  | nil => intro S W h; exact Or.inl ⟨S, rfl, h⟩
  | cons q1 Q'' ih =>
    intro S W h
    cases S with
    | nil => exact Or.inr rfl
    | cons s1 S'' =>
      have h' : (if s1 = q1 then ltL S'' (Q'' ++ W) else lt s1 q1) = true := h
      by_cases hs : s1 = q1
      · rw [if_pos hs] at h'
        rcases ih S'' W h' with ⟨S', hS', hlt⟩ | hr
        · exact Or.inl ⟨S', by rw [hs, hS']; rfl, hlt⟩
        · refine Or.inr ?_
          show (if s1 = q1 then ltL S'' Q'' else lt s1 q1) = true
          rw [if_pos hs]; exact hr
      · rw [if_neg hs] at h'
        refine Or.inr ?_
        show (if s1 = q1 then ltL S'' Q'' else lt s1 q1) = true
        rw [if_neg hs]; exact h'

theorem ltL_append_of_lt : ∀ (S Q R : List Term), ltL S Q = true → ltL S (Q ++ R) = true := by
  intro S
  induction S with
  | nil =>
    intro Q R h
    cases Q with
    | nil => exact Bool.noConfusion h
    | cons _ _ => rfl
  | cons s1 S'' ih =>
    intro Q R h
    cases Q with
    | nil => exact Bool.noConfusion h
    | cons q1 Q'' =>
      have h' : (if s1 = q1 then ltL S'' Q'' else lt s1 q1) = true := h
      show (if s1 = q1 then ltL S'' (Q'' ++ R) else lt s1 q1) = true
      by_cases hs : s1 = q1
      · rw [if_pos hs] at h' ⊢; exact ih Q'' R h'
      · rw [if_neg hs] at h' ⊢; exact h'

theorem ltL_prefix_lt : ∀ (l R : List Term), R ≠ [] → ltL l (l ++ R) = true := by
  intro l R h
  have h2 := ltL_append_left l [] R
  rw [List.append_nil] at h2
  rw [h2]
  cases R with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem cnvL_filter (p : Term → Bool) (l : List Term) (hc : cnvL l = true) :
    cnvL (l.filter p) = true := by
  show (l.filter p).all _ = true
  rw [List.all_eq_true]
  intro x hx
  exact List.all_eq_true.mp hc x (List.mem_filter.mp hx).1

theorem descL_filter {b1 : Term} (hb1 : CNV b1 = true) (l : List Term)
    (hc : cnvL l = true) (hd : descL l = true) :
    descL (l.filter (fun z => le b1 z)) = true := by
  obtain ⟨k, hk⟩ := filter_eq_take b1 l hc hd hb1
  rw [hk]; exact descL_take k l hd

/-! ## §23 COFINALITY UNDER A PREFIX -/

theorem ltL_or_eq_of_le {S' M : List Term} (hcS' : cnvL S' = true) (hcM : cnvL M = true)
    (h : le (ofList S') (ofList M) = true) : ltL S' M = true ∨ S' = M := by
  have hapM : ∀ x ∈ M, x.isAP = true := fun x hx =>
    ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcM x hx)).1
  have hapS' : ∀ x ∈ S', x.isAP = true := fun x hx =>
    ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcS' x hx)).1
  cases hb : (ofList S' == ofList M) with
  | true =>
    refine Or.inr ?_
    have h2 := congrArg toList (eq_of_beq hb)
    rw [toList_ofList _ hapS', toList_ofList _ hapM] at h2
    exact h2
  | false =>
    refine Or.inl ?_
    have h3 : ((ofList S' == ofList M) || lt (ofList S') (ofList M)) = true := h
    rw [hb, Bool.false_or, lt_ofList S' M hcS' hcM] at h3
    exact h3

/-- **前置きの下でも共終。** `s` が前置きの中で決着するなら `s ≤ P` で済み、そうでなければ
    `s` は残った前置きを接頭辞として持つので、その尾を `g` 自身の共終性に渡せる。 -/
theorem cof_plus {P V : Term} (hP : CNV P = true) (hV : CNV V = true) (hVz : V ≠ zero)
    (g : Nat → Term) (hg1 : ∀ n, CNV (g n) = true) (hg2 : ∀ n, lt (g n) V = true)
    (hg4 : ∀ s, inT s = true → lt s V = true → ∃ n, le s (g n) = true) :
    ∀ s, inT s = true → lt s (plus P V) = true → ∃ n, le s (plus P (g n)) = true := by
  intro s hin hlt
  have hPV : CNV (plus P V) = true := cnv_plus hP hV
  have hcns : CNV s = true := cnv_of_lt_cnv hin hPV hlt
  obtain ⟨hcA, hdA⟩ := cnv_toList P hP
  obtain ⟨hcS, hdS⟩ := cnv_toList s hcns
  cases hVl : toList V with
  | nil => exact absurd (toList_eq_nil V hVl) hVz
  | cons v1 V' =>
    obtain ⟨hcV, _⟩ := cnv_toList V hV
    rw [hVl] at hcV
    have hcv1 : CNV v1 = true := (cnvL_cons.mp hcV).1.2
    obtain ⟨q, hq⟩ := filter_eq_take v1 (toList P) hcA hdA hcv1
    have hdrop : descL ((toList P).drop q) = true := by
      have h0 : descL ((toList P).take q ++ (toList P).drop q) = true := by
        rw [List.take_append_drop]; exact hdA
      exact descL_of_append_right _ _ h0
    have hcdrop : cnvL ((toList P).drop q) = true := by
      have h0 : cnvL ((toList P).take q ++ (toList P).drop q) = true := by
        rw [List.take_append_drop]; exact hcA
      exact cnvL_of_append_right _ _ h0
    have hplus : toList (plus P V) = (toList P).take q ++ (v1 :: V') := by
      rw [toList_plus hP hV hVl, hVl, hq]
    have hSlt : ltL (toList s) ((toList P).take q ++ (v1 :: V')) = true := by
      rw [← hplus, ← lt_eq_ltL hcns hPV]; exact hlt
    rcases ltL_split _ _ _ hSlt with ⟨S', hS, hS'lt⟩ | hr
    · have hcS' : cnvL S' = true := by rw [hS] at hcS; exact cnvL_of_append_right _ _ hcS
      have hdS' : descL S' = true := by rw [hS] at hdS; exact descL_of_append_right _ _ hdS
      have hapS' : ∀ x ∈ S', x.isAP = true := fun x hx =>
        ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcS' x hx)).1
      have hcns' : CNV (ofList S') = true := cnv_ofList S' hcS' hdS'
      have htoS' : toList (ofList S') = S' := toList_ofList S' hapS'
      have hs'V : lt (ofList S') V = true := by
        rw [lt_eq_ltL hcns' hV, htoS', hVl]; exact hS'lt
      obtain ⟨n, hn⟩ := hg4 (ofList S') (inT_of_cnv _ hcns') hs'V
      refine ⟨n, ?_⟩
      cases hZ : toList (g n) with
      | nil =>
        have hgz : g n = zero := toList_eq_nil _ hZ
        rw [hgz] at hn
        have hs'z : ofList S' = zero := by
          have h2 : ((ofList S' == zero) || lt (ofList S') zero) = true := hn
          rw [lt_zero_right, Bool.or_false] at h2
          exact eq_of_beq h2
        have hS'nil : S' = [] := by rw [← htoS', hs'z]; rfl
        have htoSq : toList s = (toList P).take q := by
          rw [hS, hS'nil, List.append_nil]
        have hA : toList P = toList s ++ (toList P).drop q := by
          rw [htoSq, List.take_append_drop]
        have hleP : le s P = true := by
          cases hd0 : (toList P).drop q with
          | nil =>
            have heq : toList s = toList P := by rw [hA, hd0, List.append_nil]
            have hsp : s = P := by
              rw [← cnv_ofList_toList s hcns, ← cnv_ofList_toList P hP, heq]
            rw [hsp]; exact le_self P
          | cons c t =>
            refine le_of_lt ?_
            rw [lt_eq_ltL hcns hP, hA, hd0]
            exact ltL_prefix_lt (toList s) (c :: t) (by simp)
        rw [hgz]
        exact hleP
      | cons w Z' =>
        obtain ⟨hcZ, hdZ⟩ := cnv_toList (g n) (hg1 n)
        have hcw : CNV w = true := by rw [hZ] at hcZ; exact (cnvL_cons.mp hcZ).1.2
        have hwv1 : le w v1 = true := by
          have h1 : ltL (toList (g n)) (toList V) = true := by
            rw [← lt_eq_ltL (hg1 n) hV]; exact hg2 n
          rw [hZ, hVl] at h1
          have h2 : (if w = v1 then ltL Z' V' else lt w v1) = true := h1
          by_cases hwv : w = v1
          · rw [hwv]; exact le_self v1
          · rw [if_neg hwv] at h2; exact le_of_lt h2
        have hQfall : ∀ x ∈ (toList P).take q, le w x = true := by
          intro x hx
          rw [← hq] at hx
          have hv1x : le v1 x = true := (List.mem_filter.mp hx).2
          have hcx : CNV x = true := ((Bool.and_eq_true _ _).mp
            (List.all_eq_true.mp hcA x (List.mem_filter.mp hx).1)).2
          exact le_trans (frag_of_cnv _ hcw) (frag_of_cnv _ hcv1) (frag_of_cnv _ hcx)
            hwv1 hv1x
        have hfilA : (toList P).filter (fun z => le w z)
            = (toList P).take q ++ ((toList P).drop q).filter (fun z => le w z) := by
          have h1 : (toList P).filter (fun z => le w z)
              = ((toList P).take q).filter (fun z => le w z)
                ++ ((toList P).drop q).filter (fun z => le w z) := by
            rw [← List.filter_append, List.take_append_drop]
          rw [h1, filter_self_of_all (fun z => le w z) _ hQfall]
        have htoPg : toList (plus P (g n))
            = (toList P).take q
              ++ (((toList P).drop q).filter (fun z => le w z) ++ toList (g n)) := by
          rw [toList_plus hP (hg1 n) hZ, hfilA, List.append_assoc]
        have hcmid : cnvL (((toList P).drop q).filter (fun z => le w z)) = true :=
          cnvL_filter _ _ hcdrop
        have hdmid : descL (((toList P).drop q).filter (fun z => le w z)) = true :=
          descL_filter hcw _ hcdrop hdrop
        have hcM : cnvL (((toList P).drop q).filter (fun z => le w z) ++ toList (g n))
            = true := by
          show (((toList P).drop q).filter (fun z => le w z) ++ toList (g n)).all
            (fun x => x.isAP && CNV x) = true
          rw [List.all_eq_true]
          intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact List.all_eq_true.mp hcmid x h
          · exact List.all_eq_true.mp hcZ x h
        have hdM : descL (((toList P).drop q).filter (fun z => le w z) ++ toList (g n))
            = true := by
          refine descL_append _ _ hdmid hdZ ?_
          intro a b t ha hb
          rw [hZ] at hb
          injection hb with hb1 _
          rw [← hb1]
          exact (List.mem_filter.mp (getLast?_mem ha)).2
        have hcofM : CNV (ofList (((toList P).drop q).filter (fun z => le w z)
            ++ toList (g n))) = true := cnv_ofList _ hcM hdM
        have hgM : le (g n) (ofList (((toList P).drop q).filter (fun z => le w z)
            ++ toList (g n))) = true := by
          by_cases hm : ((toList P).drop q).filter (fun z => le w z) = []
          · have h0 : ofList (((toList P).drop q).filter (fun z => le w z)
                ++ toList (g n)) = g n := by
              rw [hm]
              exact cnv_ofList_toList _ (hg1 n)
            rw [h0]
            exact le_self _
          · refine le_of_lt ?_
            have h1 := lt_ofList (toList (g n))
              (((toList P).drop q).filter (fun z => le w z) ++ toList (g n)) hcZ hcM
            rw [cnv_ofList_toList _ (hg1 n)] at h1
            rw [h1]
            exact ltL_prefix_grow (toList (g n)) _ hm hcM hdM
        have hkey : le (ofList S') (ofList (((toList P).drop q).filter (fun z => le w z)
            ++ toList (g n))) = true :=
          le_trans (frag_of_cnv _ hcns') (frag_of_cnv _ (hg1 n)) (frag_of_cnv _ hcofM) hn hgM
        rcases ltL_or_eq_of_le hcS' hcM hkey with h2 | h2
        · refine le_of_lt ?_
          rw [lt_eq_ltL hcns (cnv_plus hP (hg1 n)), hS, htoPg, ltL_append_left]
          exact h2
        · have hsp : s = plus P (g n) := by
            rw [← cnv_ofList_toList s hcns, ← cnv_ofList_toList _ (cnv_plus hP (hg1 n)),
              hS, htoPg, h2]
          rw [hsp]; exact le_self _
    · refine ⟨0, ?_⟩
      have hltP : lt s P = true := by
        rw [lt_eq_ltL hcns hP]
        have h2 := ltL_append_of_lt (toList s) ((toList P).take q) ((toList P).drop q) hr
        rw [List.take_append_drop] at h2
        exact h2
      exact le_trans (frag_of_cnv _ hcns) (frag_of_cnv _ hP)
        (frag_of_cnv _ (cnv_plus hP (hg1 0))) (le_of_lt hltP) (le_plus_left hP (hg1 0))

/-- **前置きの組み合わせ子。** `V` の 4 連言から `P ⊕ V` の 4 連言。側条件は無い。 -/
theorem lim_clauses_prefix {P V : Term} (hP : CNV P = true) (hV : CNV V = true)
    (g : Nat → Term) (h : LimClauses V g) :
    LimClauses (plus P V) (fun n => plus P (g n)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hVz : V ≠ zero := by
    intro hc
    have h0 := h2 0
    rw [hc, lt_zero_right] at h0
    exact Bool.noConfusion h0
  exact ⟨fun n => cnv_plus hP (h1 n),
    fun n => lt_plus_right hP (h1 n) hV (h2 n),
    fun n => lt_plus_right hP (h1 n) (h1 (n + 1)) (h3 n),
    cof_plus hP hV hVz g h1 h2 h4⟩

/-! ## §24 THE SHIFT IS ABSORBABLE

`Evidence/WF.lean` §15.33 discharges core (C)'s side condition internally and returns an
EXISTENTIAL sequence, because `hside_general` delivers `b < φ̄(a, g k)` at some index `k`
rather than at `0`.  A certificate cannot take that: `Certified.lim`'s identity premise
pins `fs' n` to the value of the n-th expansion, so a shifted sequence is a different
sequence and the row does not close.

IT DOES NOT HAVE TO BE SHIFTED.  Clauses 1–3 hold at every `n` on their own — they are
`lt_phi_arg` applied to `g`'s own clauses — and clause 4's index is EXISTENTIAL, so the
shifted sequence's witness `m` is read back as `m + k` in the original.  The shift was only
ever a device for the side condition, and it never had to reach the statement. -/

/-- **ずらしは吸収できる。** `lim_clauses_phi_arg_nf` は `hside` を添字 `k` で得るので
    ずれた列を返すが、第 4 連言の添字は存在量化されているので、ずれた列の証人 `m` を
    元の列の `m + k` として読み直せる。他の 3 連言は各 `n` で独立に成り立つ。 -/
theorem lim_clauses_phi_arg_nf' {a b : Term} (hcna : CNV a = true) (hcnb : CNV b = true)
    (hnf : ∀ c d, b = phi c d → phiNF a b = phi a b)
    (g : Nat → Term) (hg : LimClauses b g) :
    LimClauses (phi a b) (fun n => phi a (g n)) := by
  obtain ⟨k, hk⟩ := hside_general hcna hcnb hnf g hg
  obtain ⟨t1, t2, t3, t4⟩ := lim_clauses_shift_k hcnb hg k
  obtain ⟨h1, h2, h3, h4⟩ := hg
  obtain ⟨s1, s2, s3, s4⟩ :=
    lim_clauses_phi_arg (fun n => g (n + k)) hcna hcnb t1 t2 t3 t4
      (by show lt b (phi a (g (0 + k))) = true
          rw [show 0 + k = k from by omega]; exact hk)
  refine ⟨fun n => by show (CNV a && CNV (g n)) = true; rw [hcna, h1 n]; rfl,
    fun n => lt_phi_arg (h2 n), fun n => lt_phi_arg (h3 n), fun s hin hlt => ?_⟩
  obtain ⟨m, hm⟩ := s4 s hin hlt
  exact ⟨m + k, hm⟩

/-! ## §25 `ω^·` LANDS ON AN ADDITIVELY PRINCIPAL TERM

Three small facts `Evidence/RegionV.lean` §15.4 needs and `Rows/ProofsB.lean` already has —
but Rows is DOWNSTREAM of this file, so they are re-proved rather than imported. -/

theorem isAP_of_isSC {t : Term} (h : t.isSC = true) : t.isAP = true := by
  cases t <;> first | rfl | exact Bool.noConfusion h

theorem isAP_phiNF (a b : Term) : (phiNF a b).isAP = true := by
  unfold phiNF phiNFsucc phiNFdefault
  split
  · rename_i h
    exact isAP_of_isSC ((Bool.and_eq_true _ _).mp h).1
  · repeat' split
    all_goals first
      | rfl
      | (apply isAP_of_isSC; simp_all)

theorem isAP_omegaNF (t : Term) : (omegaNF t).isAP = true := by
  unfold omegaNF
  split
  · rfl
  · split
    · rfl
    · exact isAP_phiNF zero t

theorem plus_zero_left {X : Term} (h : X.isAP = true) : plus zero X = X := by
  have hl : toList X = [X] := by
    cases X <;> first | rfl | exact Bool.noConfusion h
  show (match toList X with
    | [] => zero
    | b1 :: _ => ofList ((toList (zero : Term)).filter (fun a => le b1 a) ++ toList X)) = X
  rw [hl]
  rfl

/-! ## §26 THE THREE SHAPES OF `ω^·`, AS ONE EQUATION

`omegaNF` on a `CNV` argument is `phiNF zero`, and `phiNF zero` is not one branch but
three.  `Evidence/RegionV.lean` §15.3 measures that on the region's arguments; this is the
equation behind it, and it is what a proof about `ω^·` has to case on:

    x = φ̄(c,d) with c ≠ 0    ω^x = x              `x` is already a fixed point of `ω^·`
    x = γ ⊕ m, γ a fixed
        point, m ≥ 1          ω^x = φ̄(0, γ ⊕ (m-1))   `phiNFsucc` RE-COUNTS
    otherwise                 ω^x = φ̄(0, x)

`dnArg` is the middle column's argument, written by copying `phiNFsucc zero`'s own branch
structure so that `phiNFsucc_zero_eq` is a case-by-case identity rather than a proof about
`splitFin`.  Measured (`Evidence/RegionSeq.lean`): 0 failures over 462 `CNV` terms, with all
three branches firing — 76 / 10 / 376. -/

/-- `ω^·` が引数をそのまま返す形 — `x` が `ω^·` の不動点。 -/
def isFixP (x : Term) : Bool := match x with | phi c _ => lt zero c | _ => false

/-- 数え直したあとの引数。`phiNFsucc zero` の枝分けをそのまま写したもの。 -/
def dnArg (x : Term) : Term :=
  let (g, m) := splitFin x
  if m ≥ 1 then
    let down := plus g (ofNat (m - 1))
    match g with
    | phi d _ => if lt zero d then down else x
    | _ => if g.isSC && lt zero g then down else x
  else x

theorem phiNFsucc_zero_eq (x : Term) : phiNFsucc zero x = phi zero (dnArg x) := by
  unfold phiNFsucc dnArg
  cases hs : splitFin x with
  | mk g m =>
    dsimp only
    split
    · cases g <;> dsimp only <;> split <;>
        first | rfl | exact phiNFdefault_zero_eq x
    · exact phiNFdefault_zero_eq x

theorem omegaNF_cnv {a : Term} (h : CNV a = true) : omegaNF a = phiNF zero a := by
  have hMa : lt M a = false :=
    lt_asymm_inT (inT_of_cnv a h) (show inT (M : Term) = true from rfl) (cnv_lt_M a h)
  have haM : (a == M) = false := by
    cases hb : (a == M) with
    | false => rfl
    | true => rw [eq_of_beq hb] at h; exact Bool.noConfusion h
  show (if lt M a then omg a else if a == M then M else phiNF zero a) = _
  rw [if_neg (by rw [hMa]; exact Bool.noConfusion),
    if_neg (by rw [haM]; exact Bool.noConfusion)]

/-- **`ω^·` の形は 3 つ。** 不動点をそのまま返すか、`φ̄(0, ·)` を返すか。 -/
theorem omegaNF_eq {x : Term} (h : CNV x = true) :
    omegaNF x = if isFixP x then x else phi zero (dnArg x) := by
  rw [omegaNF_cnv h]
  have hsc : x.isSC = false := by cases x <;> first | rfl | exact Bool.noConfusion h
  unfold phiNF isFixP
  simp only [hsc, Bool.false_and, Bool.false_eq_true, if_false]
  cases x <;> dsimp only <;>
    first
      | exact Bool.noConfusion h
      | exact phiNFsucc_zero_eq _
      | (split <;> first | rfl | exact phiNFsucc_zero_eq _)

/-! ## §27 `ω^·` IS STRICTLY MONOTONE, MODULO THREE `splitFin` FACTS

`Evidence/RegionV.lean` §15.4's `OmegaLim` needs it for clauses 2 and 3.  With §26's
equation the proof is four cases on whether each side is a fixed point, and every case
turns on the same three elementary facts about `dnArg` — that it only ever goes DOWN, that
it goes down by at most one, and that it cannot collapse two different arguments:

    D1   dnArg x ≤ x
    D2   x < y  →  x ≤ dnArg y
    D3   x not a fixed point, x < y  →  dnArg x ≠ dnArg y

They are bundled as `DnFacts` and left as the hypothesis, because each is a statement about
where `splitFin` puts the trailing `1`s and none of them is about `ω^·` at all.  Measured in
`Evidence/RegionSeq.lean`: 0 failures over 462 `CNV` terms and their 106491 ordered pairs,
with the `dnArg x ≠ x` control firing on 10.

The one fact proved outright here is `lt_self_phi_zero` — `z < φ̄(0,z)`, the reason a fixed
point on one side and an ordinary term on the other still compare the right way. -/

theorem lt_of_le_of_ne {a b : Term} (h : le a b = true) (hne : a ≠ b) : lt a b = true := by
  have h' : ((a == b) || lt a b) = true := h
  rw [show (a == b) = false from by
    cases hb : (a == b) with
    | false => rfl
    | true => exact absurd (eq_of_beq hb) hne, Bool.false_or] at h'
  exact h'

theorem cnv_dnArg {x : Term} (h : CNV x = true) : CNV (dnArg x) = true := by
  have hg : CNV (splitFin x).1 = true := cnv_splitFin h
  unfold dnArg
  cases hs : splitFin x with
  | mk g m =>
    rw [hs] at hg
    dsimp only
    split
    · cases g <;> dsimp only <;> split <;>
        first | exact h | exact cnv_plus hg (cnv_ofNat _)
    · exact h

/-- **`z < ω^z` の形** — `φ̄(0,z)` は `z` を真に超える。 -/
theorem lt_self_phi_zero : ∀ (z : Term), CNV z = true → lt z (phi zero z) = true := by
  intro z
  induction z with
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | zero => intro _; exact lt_zero_left (by intro hc; exact Term.noConfusion hc)
  | phi a b _ ihb =>
    intro h
    obtain ⟨hca, hcb⟩ := cnv_phi h
    have hne : phi a b ≠ phi zero (phi a b) := by
      intro hc
      injection hc with _ h2
      have hd := congrArg Term.deg h2
      have he : (phi a b).deg = 1 + a.deg + b.deg := rfl
      rw [he] at hd
      omega
    rw [lt_phi_phi hne]
    by_cases haz : a = zero
    · rw [if_pos haz, haz]
      exact ihb hcb
    · have hlz : ¬ (lt a zero = true) := by
        rw [show lt a zero = false from ltF_right_zero _ a]
        intro hc
        exact Bool.noConfusion hc
      rw [if_neg haz, if_neg hlz]
      exact le_self _
  | add u v ihu _ =>
    intro h
    obtain ⟨hap, hcu, hcv, _⟩ := cnv_add h
    obtain ⟨p, q, rfl⟩ := eq_phi_of_isAP_cnv hcu hap
    have huv : lt (phi p q) (add (phi p q) v) = true := by
      rw [lt_phi_add]; exact le_self _
    have hstep : lt (phi p q) (phi zero (add (phi p q) v)) = true := by
      have h1 : lt (phi p q) (phi zero (phi p q)) = true := ihu hcu
      have h2 : le (phi zero (phi p q)) (phi zero (add (phi p q) v)) = true :=
        le_of_lt (lt_phi_arg huv)
      exact lt_of_le_of_lt (frag_of_cnv _ hcu)
        (frag_of_cnv _ (by show (CNV zero && CNV (phi p q)) = true; rw [hcu]; rfl))
        (frag_of_cnv _ (by show (CNV zero && CNV (add (phi p q) v)) = true; rw [h]; rfl))
        (le_of_lt h1) (lt_of_le_of_ne h2 (by
          intro hc
          injection hc with _ h2'
          have hd := congrArg Term.deg h2'
          have he : (add (phi p q) v).deg = 1 + (phi p q).deg + v.deg := rfl
          have hv := deg_pos v
          rw [he] at hd
          omega))
    rw [lt_add_phi]
    exact hstep

/-- 数え直しの土台 3 つ。どれも `splitFin` についての初等的な事実である。 -/
def DnFacts : Prop :=
  (∀ x, CNV x = true → le (dnArg x) x = true)
  ∧ (∀ x y, CNV x = true → CNV y = true → lt x y = true → le x (dnArg y) = true)
  ∧ (∀ x y, CNV x = true → CNV y = true → isFixP x = false → lt x y = true →
      dnArg x ≠ dnArg y)

theorem bool_false {b : Bool} (h : ¬ (b = true)) : b = false := by
  cases hb : b with
  | false => rfl
  | true => exact absurd hb h

/-- **`ω^·` は狭義単調** — `dnArg` の 3 つの土台から。 -/
theorem omegaNF_mono (H : DnFacts) {x y : Term} (hx : CNV x = true) (hy : CNV y = true)
    (h : lt x y = true) : lt (omegaNF x) (omegaNF y) = true := by
  obtain ⟨D1, D2, D3⟩ := H
  rw [omegaNF_eq hx, omegaNF_eq hy]
  by_cases hfx : isFixP x = true
  · rw [if_pos hfx]
    by_cases hfy : isFixP y = true
    · rw [if_pos hfy]; exact h
    · rw [if_neg hfy]
      have hcp : CNV (phi zero (dnArg y)) = true := by
        show (CNV zero && CNV (dnArg y)) = true
        rw [cnv_dnArg hy]; rfl
      exact lt_of_le_of_lt (frag_of_cnv _ hx) (frag_of_cnv _ (cnv_dnArg hy))
        (frag_of_cnv _ hcp) (D2 x y hx hy h) (lt_self_phi_zero _ (cnv_dnArg hy))
  · rw [if_neg hfx]
    by_cases hfy : isFixP y = true
    · rw [if_pos hfy]
      cases y with
      | zero => exact Bool.noConfusion hfy
      | M => exact Bool.noConfusion hfy
      | omg _ => exact Bool.noConfusion hfy
      | psi _ _ => exact Bool.noConfusion hfy
      | Z _ => exact Bool.noConfusion hfy
      | add _ _ => exact Bool.noConfusion hfy
      | phi c d =>
        have hc : lt zero c = true := hfy
        have hzc : ¬ (zero = c) := by
          intro hcc
          rw [← hcc, lt_irrefl] at hc
          exact Bool.noConfusion hc
        have hne : phi zero (dnArg x) ≠ phi c d := by
          intro hcc
          injection hcc with h1 _
          exact hzc h1
        rw [lt_phi_phi hne, if_neg hzc, if_pos hc]
        exact lt_of_le_of_lt (frag_of_cnv _ (cnv_dnArg hx)) (frag_of_cnv _ hx)
          (frag_of_cnv _ hy) (D1 x hx) h
    · rw [if_neg hfy]
      refine lt_phi_arg ?_
      refine lt_of_le_of_ne ?_ (D3 x y hx hy (bool_false hfx) h)
      exact le_trans (frag_of_cnv _ (cnv_dnArg hx)) (frag_of_cnv _ hx)
        (frag_of_cnv _ (cnv_dnArg hy)) (D1 x hx) (D2 x y hx hy h)

/-! ## §28 `splitFin` REBUILDS ITS ARGUMENT, AND TWO OF `DnFacts` FALL OUT

`splitFin t = (γ, m)` means `t = γ ⊕ m`, and once that is an equation D1 and D2 are one step
each: `dnArg` is `γ ⊕ (m-1)`, so `t = succT (dnArg t)`, and `≤ succ` and `< succ → ≤` are
`Evidence/WF.lean` §15.4's `lt_succT` and `le_succT_of_lt`.

DUPLICATION, DELIBERATE AND TEMPORARY.  `Evidence/SqV.lean` §11 already proves
`trailing_ones` … `splitFin_rebuild`; SqV is not upstream of this file (SqV imports `Cert`,
which imports `WF` but not `CNVOps`), so they are re-proved here rather than imported.  When
`Cert.lean` imports `Evidence/RegionV.lean` to assemble the region's certificate, `CNVOps`
becomes upstream of SqV and **the SqV copy is the one to delete**.

`cnv_ofList_toList` and `cnv_take_ofList` are §19's and §18's, so only the `takeWhile` half
had to come across. -/

theorem cnvL_isAP {t : Term} (h : CNV t = true) : ∀ x ∈ toList t, x.isAP = true := by
  intro x hx
  exact ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp (cnv_toList t h).1 x hx)).1

theorem trailing_ones : ∀ (r : List Term),
    (r.dropWhile (fun x => x == one)).reverse
      ++ List.replicate ((r.takeWhile (fun x => x == one)).length) one = r.reverse := by
  intro r
  induction r with
  | nil => rfl
  | cons a t ih =>
    by_cases h : (a == one) = true
    · have ha : a = one := by simpa using h
      rw [List.dropWhile_cons_of_pos (p := fun x => x == one) h,
          List.takeWhile_cons_of_pos (p := fun x => x == one) h,
          List.length_cons, List.replicate_succ', ← List.append_assoc, ih,
          List.reverse_cons, ha]
    · rw [List.dropWhile_cons_of_neg (p := fun x => x == one) (by simpa using h),
          List.takeWhile_cons_of_neg (p := fun x => x == one) (by simpa using h),
          List.length_nil, show List.replicate 0 one = [] from rfl, List.append_nil]

theorem plus_ofNat_spec : ∀ (g : Term), CNV g = true → ∀ m,
    CNV (plus g (ofNat m)) = true ∧
      toList (plus g (ofNat m)) = toList g ++ List.replicate m one := by
  intro g hg m
  induction m with
  | zero => exact ⟨hg, (List.append_nil _).symm⟩
  | succ m ih =>
    have hEq : plus g (ofNat (m + 1)) = ofList (toList g ++ List.replicate (m + 1) one) := by
      rw [plus_ofNat_succ g hg m, toList_ofNat (m + 1)]
    have hAP : ∀ x ∈ toList g ++ List.replicate (m + 1) one, x.isAP = true := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact cnvL_isAP hg x h
      · rw [List.eq_of_mem_replicate h]; rfl
    have hSucc : plus g (ofNat (m + 1)) = succT (plus g (ofNat m)) := by
      rw [← ofList_toList_snoc (plus g (ofNat m)) ih.1, ih.2, hEq,
          List.append_assoc, ← List.replicate_succ']
    exact ⟨by rw [hSucc]; exact cnv_succT _ ih.1, by rw [hEq, toList_ofList _ hAP]⟩

theorem plus_ofNat_step (g : Term) (hg : CNV g = true) (m : Nat) :
    plus g (ofNat (m + 1)) = succT (plus g (ofNat m)) := by
  have ih := plus_ofNat_spec g hg m
  rw [← ofList_toList_snoc (plus g (ofNat m)) ih.1, ih.2,
      plus_ofNat_succ g hg m, toList_ofNat (m + 1), List.append_assoc, ← List.replicate_succ']

theorem take_of_append_replicate {X : List Term} {k : Nat} {l : List Term}
    (h : X ++ List.replicate k one = l) : l.take (l.length - k) = X := by
  subst h
  rw [List.length_append, List.length_replicate,
      show X.length + k - k = X.length from by omega, List.take_left]

theorem splitFin_fst (t : Term) :
    (splitFin t).1 = ofList (((toList t).reverse.dropWhile (fun x => x == one)).reverse) := by
  have hF1 : ((toList t).reverse.dropWhile (fun x => x == one)).reverse
      ++ List.replicate (((toList t).reverse.takeWhile (fun x => x == one)).length) one
      = toList t := by
    have h := trailing_ones (toList t).reverse
    rwa [List.reverse_reverse] at h
  show ofList ((toList t).take
      ((toList t).length - ((toList t).reverse.takeWhile (fun x => x == one)).length)) = _
  rw [take_of_append_replicate hF1]

/-- **`splitFin` は引数を組み立て直す** — `(γ, m) = splitFin t` なら `t = γ ⊕ m`。 -/
theorem splitFin_rebuild (t : Term) (ht : CNV t = true) :
    plus (splitFin t).1 (ofNat (splitFin t).2) = t := by
  have hcg : CNV (splitFin t).1 = true := cnv_splitFin ht
  have hF1 : ((toList t).reverse.dropWhile (fun x => x == one)).reverse
      ++ List.replicate (((toList t).reverse.takeWhile (fun x => x == one)).length) one
      = toList t := by
    have h := trailing_ones (toList t).reverse
    rwa [List.reverse_reverse] at h
  have hAP : ∀ x ∈ ((toList t).reverse.dropWhile (fun x => x == one)).reverse, x.isAP = true := by
    intro x hx
    exact cnvL_isAP ht x (by rw [← hF1]; exact List.mem_append_left _ hx)
  have hg : toList (splitFin t).1
      = ((toList t).reverse.dropWhile (fun x => x == one)).reverse := by
    rw [splitFin_fst t, toList_ofList _ hAP]
  have hspec := plus_ofNat_spec _ hcg (splitFin t).2
  have hto : toList (plus (splitFin t).1 (ofNat (splitFin t).2)) = toList t := by
    rw [hspec.2, hg]; exact hF1
  rw [← cnv_ofList_toList _ hspec.1, hto, cnv_ofList_toList t ht]

/-- `dnArg` は `x` そのものか、`splitFin` の finite 部を 1 下げたもの。 -/
theorem dnArg_or {x g : Term} {m : Nat} (hs : splitFin x = (g, m)) :
    dnArg x = x ∨ (1 ≤ m ∧ dnArg x = plus g (ofNat (m - 1))) := by
  unfold dnArg
  rw [hs]
  dsimp only
  split
  · rename_i hm
    cases g <;> dsimp only <;> split <;>
      first | exact Or.inr ⟨hm, rfl⟩ | exact Or.inl rfl
  · exact Or.inl rfl

/-- **D1** — `dnArg` は下げるだけ。 -/
theorem dnArg_le {x : Term} (hx : CNV x = true) : le (dnArg x) x = true := by
  cases hs : splitFin x with
  | mk g m =>
    rcases dnArg_or hs with h | ⟨hm, h⟩
    · rw [h]; exact le_self _
    · have hcg : CNV g = true := by
        have h0 := cnv_splitFin hx; rw [hs] at h0; exact h0
      have hreb : plus g (ofNat m) = x := by
        have h0 := splitFin_rebuild x hx; rw [hs] at h0; exact h0
      cases m with
      | zero => exact absurd hm (by omega)
      | succ k =>
        rw [h, ← hreb, show k + 1 - 1 = k from rfl, plus_ofNat_step g hcg k]
        exact le_of_lt (lt_succT _ (plus_ofNat_spec g hcg k).1)

/-- **D2** — 下げるのは高々 1。 -/
theorem dnArg_ge {x y : Term} (hx : CNV x = true) (hy : CNV y = true)
    (h : lt x y = true) : le x (dnArg y) = true := by
  cases hs : splitFin y with
  | mk g m =>
    rcases dnArg_or hs with hd | ⟨hm, hd⟩
    · rw [hd]; exact le_of_lt h
    · have hcg : CNV g = true := by
        have h0 := cnv_splitFin hy; rw [hs] at h0; exact h0
      have hreb : plus g (ofNat m) = y := by
        have h0 := splitFin_rebuild y hy; rw [hs] at h0; exact h0
      cases m with
      | zero => exact absurd hm (by omega)
      | succ k =>
        have hz : CNV (plus g (ofNat k)) = true := (plus_ofNat_spec g hcg k).1
        have hy' : y = succT (plus g (ofNat k)) := by
          rw [← hreb, plus_ofNat_step g hcg k]
        rw [hd, show k + 1 - 1 = k from rfl]
        by_cases hle : le x (plus g (ofNat k)) = true
        · exact hle
        · exfalso
          have hlt : lt (plus g (ofNat k)) x = true :=
            lt_of_not_le (frag_of_cnv _ hx) (frag_of_cnv _ hz) (bool_false hle)
          have hs2 : le (succT (plus g (ofNat k))) x = true :=
            le_succT_of_lt _ hz x hx hlt
          rw [hy'] at h
          have hcon := lt_of_le_of_lt (frag_of_cnv _ (cnv_succT _ hz)) (frag_of_cnv _ hx)
            (frag_of_cnv _ (cnv_succT _ hz)) hs2 h
          rw [lt_irrefl] at hcon
          exact Bool.noConfusion hcon

/-- **残るのは D3 だけ。** -/
theorem dnFacts_of
    (D3 : ∀ x y, CNV x = true → CNV y = true → isFixP x = false → lt x y = true →
      dnArg x ≠ dnArg y) : DnFacts :=
  ⟨fun _ hx => dnArg_le hx, fun _ _ hx hy h => dnArg_ge hx hy h, D3⟩

/-! ## §29 D3, AND `DnFacts` BECOMES A THEOREM

D3 says `dnArg` cannot send two different arguments to the same place.  Suppose it does, with
`x < y` and `x` not a fixed point.  D1 and D2 then squeeze `x` between `dnArg x` and
`dnArg y`, so both equal `x`; and `dnArg y = x` with `dnArg y ≠ y` means the RE-COUNT fired
at `y`, i.e. `splitFin y = (γ, m)` with `m ≥ 1` and `γ = φ̄(d,e)`, `d ≠ 0`, and `x = γ ⊕ (m-1)`.

Now compute `splitFin x`.  `splitFin_plus_ofNat` says `splitFin (γ ⊕ k) = (γ, k)` whenever
`γ`'s LAST component is not `1` — and `γ` came out of a `dropWhile`, so it is not
(`splitFin_fst_last`).  Two cases and both close:

    m - 1 = 0      `x = γ = φ̄(d,e)` with `d ≠ 0`, so `x` IS a fixed point — contradiction
    m - 1 = k+1    the re-count fires at `x` too, giving `dnArg x = γ ⊕ k`, but `dnArg x = x
                   = γ ⊕ (k+1)`, and those two have component lists of different LENGTHS

With D3 proved, `dnFacts` is a theorem and §27's `omegaNF_mono` carries no hypothesis. -/

theorem le_antisymm {a b : Term} (hfa : Frag a = true) (hfb : Frag b = true)
    (h1 : le a b = true) (h2 : le b a = true) : a = b := by
  by_cases hab : a = b
  · exact hab
  · exfalso
    have l1 : lt a b = true := lt_of_le_of_ne h1 hab
    have l2 : lt b a = true := lt_of_le_of_ne h2 (fun hc => hab hc.symm)
    rw [lt_asymm hfa hfb l1] at l2
    exact Bool.noConfusion l2

theorem head?_dropWhile {p : Term → Bool} : ∀ (l : List Term) (a : Term),
    (l.dropWhile p).head? = some a → p a = false := by
  intro l
  induction l with
  | nil => intro a h; exact absurd h (by simp)
  | cons c t ih =>
    intro a h
    by_cases hc : p c = true
    · rw [List.dropWhile_cons_of_pos hc] at h
      exact ih a h
    · rw [List.dropWhile_cons_of_neg (by simpa using hc)] at h
      have ha : a = c := by
        have hh : (c :: t).head? = some c := rfl
        rw [hh] at h
        exact (Option.some.inj h).symm
      rw [ha]
      exact bool_false hc

theorem takeWhile_replicate_append (r : List Term)
    (hr : ∀ a, r.head? = some a → (a == one) = false) :
    ∀ k, (List.replicate k one ++ r).takeWhile (fun x => x == one) = List.replicate k one := by
  intro k
  induction k with
  | zero =>
    show r.takeWhile (fun x => x == one) = []
    cases hh : r with
    | nil => rfl
    | cons a t =>
      refine List.takeWhile_cons_of_neg ?_
      rw [hr a (by rw [hh]; rfl)]
      exact Bool.noConfusion
  | succ j ih =>
    show ((one :: (List.replicate j one ++ r)).takeWhile (fun x => x == one))
      = one :: List.replicate j one
    rw [List.takeWhile_cons_of_pos (by simp), ih]

/-- **`γ ⊕ k` の `splitFin` は `(γ, k)`** — `γ` の末尾の成分が `1` でなければ。 -/
theorem splitFin_plus_ofNat {g : Term} (hg : CNV g = true)
    (hlast : ∀ a, ((toList g).reverse).head? = some a → (a == one) = false) (k : Nat) :
    splitFin (plus g (ofNat k)) = (g, k) := by
  have hspec := plus_ofNat_spec g hg k
  have hrev : (toList (plus g (ofNat k))).reverse
      = List.replicate k one ++ (toList g).reverse := by
    rw [hspec.2, List.reverse_append, List.reverse_replicate]
  have hm : ((toList (plus g (ofNat k))).reverse.takeWhile (fun x => x == one)).length = k := by
    rw [hrev, takeWhile_replicate_append _ hlast k, List.length_replicate]
  show (ofList ((toList (plus g (ofNat k))).take
      ((toList (plus g (ofNat k))).length
        - ((toList (plus g (ofNat k))).reverse.takeWhile (fun x => x == one)).length)),
    ((toList (plus g (ofNat k))).reverse.takeWhile (fun x => x == one)).length) = (g, k)
  rw [hm, take_of_append_replicate hspec.2.symm, cnv_ofList_toList g hg]

/-- `dnArg` の枝を、数え直しが起きた場合の形つきで。 -/
theorem dnArg_or' {x g : Term} {m : Nat} (hx : CNV x = true) (hs : splitFin x = (g, m)) :
    dnArg x = x ∨ (1 ≤ m ∧ (∃ d e, g = phi d e ∧ lt zero d = true)
                   ∧ dnArg x = plus g (ofNat (m - 1))) := by
  have hcg : CNV g = true := by have h0 := cnv_splitFin hx; rw [hs] at h0; exact h0
  unfold dnArg
  rw [hs]
  dsimp only
  split
  · rename_i hm
    cases g <;> dsimp only <;>
      first
        | exact Bool.noConfusion hcg
        | (split <;>
            first
              | exact Or.inr ⟨hm, ⟨_, _, rfl, by assumption⟩, rfl⟩
              | exact Or.inl rfl
              | (exfalso; simp_all [isSC]))
  · exact Or.inl rfl

/-- 数え直しが起きる形での `dnArg` の値。 -/
theorem dnArg_recount {x g d e : Term} {k : Nat} (hs : splitFin x = (g, k + 1))
    (hg : g = phi d e) (hd : lt zero d = true) : dnArg x = plus g (ofNat k) := by
  subst hg
  unfold dnArg
  rw [hs]
  dsimp only
  rw [if_pos (by omega : 1 ≤ k + 1)]
  rw [if_pos hd, show k + 1 - 1 = k from rfl]

/-- `splitFin` の第 1 成分の末尾は `1` ではない。 -/
theorem splitFin_fst_last {y g : Term} {m : Nat} (hy : CNV y = true)
    (hs : splitFin y = (g, m)) :
    ∀ a, ((toList g).reverse).head? = some a → (a == one) = false := by
  have hcg : CNV g = true := by have h0 := cnv_splitFin hy; rw [hs] at h0; exact h0
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
    exact cnvL_isAP hy x (by rw [← hF1]; exact List.mem_append_left _ hx)
  have hgl : toList g = ((toList y).reverse.dropWhile (fun x => x == one)).reverse := by
    rw [hgf, toList_ofList _ hAP]
  intro a ha
  rw [hgl, List.reverse_reverse] at ha
  exact head?_dropWhile _ a ha

/-- **D3** — `dnArg` は 2 つの引数を潰さない。 -/
theorem dnArg_ne {x y : Term} (hx : CNV x = true) (hy : CNV y = true)
    (hfx : isFixP x = false) (h : lt x y = true) : dnArg x ≠ dnArg y := by
  intro heq
  have hle1 : le (dnArg x) x = true := dnArg_le hx
  have hle2 : le x (dnArg y) = true := dnArg_ge hx hy h
  rw [← heq] at hle2
  have hxeq : dnArg x = x :=
    le_antisymm (frag_of_cnv _ (cnv_dnArg hx)) (frag_of_cnv _ hx) hle1 hle2
  have hdy : dnArg y = x := heq.symm.trans hxeq
  cases hs : splitFin y with
  | mk g m =>
    have hcg : CNV g = true := by have h0 := cnv_splitFin hy; rw [hs] at h0; exact h0
    rcases dnArg_or' hy hs with hd | ⟨hm, ⟨d, e, hgphi, hdlt⟩, hdny⟩
    · rw [hd] at hdy
      rw [← hdy, lt_irrefl] at h
      exact Bool.noConfusion h
    · have hxval : x = plus g (ofNat (m - 1)) := by rw [← hdy, hdny]
      have hlast := splitFin_fst_last hy hs
      have hsx : splitFin x = (g, m - 1) := by
        rw [hxval]; exact splitFin_plus_ofNat hcg hlast (m - 1)
      cases hk : m - 1 with
      | zero =>
        -- x = g = φ̄(d,e), a fixed point
        have hxg : x = g := by rw [hxval, hk]; rfl
        rw [hxg, hgphi] at hfx
        show False
        rw [show isFixP (phi d e) = lt zero d from rfl, hdlt] at hfx
        exact Bool.noConfusion hfx
      | succ k =>
        rw [hk] at hsx
        have hdx : dnArg x = plus g (ofNat k) := dnArg_recount hsx hgphi hdlt
        rw [hxeq, hxval, hk] at hdx
        -- plus g (ofNat (k+1)) = plus g (ofNat k) : impossible by length
        have h1 := (plus_ofNat_spec g hcg (k + 1)).2
        have h2 := (plus_ofNat_spec g hcg k).2
        rw [hdx, h2] at h1
        have hlen := congrArg List.length h1
        rw [List.length_append, List.length_append, List.length_replicate,
          List.length_replicate] at hlen
        omega

/-- **`DnFacts` は定理になった。** -/
theorem dnFacts : DnFacts :=
  ⟨fun _ hx => dnArg_le hx, fun _ _ hx hy h => dnArg_ge hx hy h,
   fun _ _ hx hy hfx h => dnArg_ne hx hy hfx h⟩

/-! ## §30 Two small facts about heads and `ω^·`

`Evidence/RegionV.lean` §15.6 needs them to peel a sum down to its head. -/

theorem isAP_hdOf {s : Term} (h : CNV s = true) (hz : s ≠ zero) : (hdOf s).isAP = true := by
  cases s with
  | zero => exact absurd rfl hz
  | M => exact Bool.noConfusion h
  | omg _ => exact Bool.noConfusion h
  | psi _ _ => exact Bool.noConfusion h
  | Z _ => exact Bool.noConfusion h
  | phi _ _ => rfl
  | add _ _ => exact (cnv_add h).1

theorem omegaNF_ne_zero (y : Term) : omegaNF y ≠ zero := by
  intro hc
  have h0 := isAP_omegaNF y
  rw [hc] at h0
  exact Bool.noConfusion h0

/-! ## §31 THE ORDER READ BACK THROUGH `ω^·`, AND THE TARGET IS A LIMIT

Three facts `Evidence/RegionV.lean` §15.7 needs to close cofinality:

    omegaNF_le_phi_zero   `ω^b ≤ φ̄(0,b)`             — `ω^·` never overshoots the plain `φ̄0`
    omegaNF_lt_reflect    `ω^x < ω^y → x < y`        — §27's monotonicity read backwards
    limClauses_succ_lt    `z < X → succT z < X`      — the four clauses force `X` to be a LIMIT

The last is the one worth naming: nothing in `LimClauses` SAYS `X` is a limit, but a strictly
increasing cofinal sequence below it cannot exist otherwise, and the proof is one line of that
argument — `z ≤ g n < g (n+1)`, so `succT z ≤ g (n+1) < X`. -/

theorem isFixP_succT (b : Term) : isFixP (succT b) = false := by
  cases b with
  | zero => show lt zero zero = false; exact lt_irrefl zero
  | add _ _ => rfl
  | M => rfl
  | omg _ => rfl
  | phi _ _ => rfl
  | psi _ _ => rfl
  | Z _ => rfl

/-- `ω^b` は `φ̄(0,b)` を超えない。 -/
theorem omegaNF_le_phi_zero {b : Term} (hb : CNV b = true) :
    le (omegaNF b) (phi zero b) = true := by
  rw [omegaNF_eq hb]
  by_cases hf : isFixP b = true
  · rw [if_pos hf]; exact le_of_lt (lt_self_phi_zero b hb)
  · rw [if_neg hf]
    have h := dnArg_le hb
    by_cases he : dnArg b = b
    · rw [he]; exact le_self _
    · exact le_of_lt (lt_phi_arg (lt_of_le_of_ne h he))

/-- **`ω^·` は順序を反射する。** 単調性と三分律から。 -/
theorem omegaNF_lt_reflect {x y : Term} (hx : CNV x = true) (hy : CNV y = true)
    (h : lt (omegaNF x) (omegaNF y) = true) : lt x y = true := by
  by_cases hlt : lt x y = true
  · exact hlt
  · exfalso
    have hle : le y x = true :=
      le_of_not_lt (frag_of_cnv _ hx) (frag_of_cnv _ hy) (bool_false hlt)
    by_cases hyx : y = x
    · rw [hyx, lt_irrefl] at h; exact Bool.noConfusion h
    · have h2 : lt y x = true := lt_of_le_of_ne hle hyx
      have h3 : lt (omegaNF y) (omegaNF x) = true := omegaNF_mono dnFacts hy hx h2
      rw [lt_asymm (frag_of_cnv _ (cnv_omegaNF hx)) (frag_of_cnv _ (cnv_omegaNF hy)) h] at h3
      exact Bool.noConfusion h3

/-- **`LimClauses` の目標は極限。** 下にあるものの後続もまだ下にある。 -/
theorem limClauses_succ_lt {X : Term} {g : Nat → Term} (hX : CNV X = true)
    (hlc : LimClauses X g) {z : Term} (hz : CNV z = true) (h : lt z X = true) :
    lt (succT z) X = true := by
  obtain ⟨h1, h2, h3, h4⟩ := hlc
  obtain ⟨n, hn⟩ := h4 z (inT_of_cnv _ hz) h
  have hzg : lt z (g (n + 1)) = true :=
    lt_of_le_of_lt (frag_of_cnv _ hz) (frag_of_cnv _ (h1 n)) (frag_of_cnv _ (h1 (n + 1)))
      hn (h3 n)
  have hs : le (succT z) (g (n + 1)) = true := le_succT_of_lt z hz (g (n + 1)) (h1 (n + 1)) hzg
  exact lt_of_le_of_lt (frag_of_cnv _ (cnv_succT _ hz)) (frag_of_cnv _ (h1 (n + 1)))
    (frag_of_cnv _ hX) hs (h2 (n + 1))

/-! ## §32 NOTHING ADDITIVELY PRINCIPAL SITS BETWEEN `ω^β` AND `ω^(β+1)`

Combinator (A) — `Evidence/WF.lean`'s `lim_clauses_repAdd`, which `ArgLimRep` needs — asks
for a BOUND: every additively principal term below the target is at most one copy of the
sequence's step.  Here the target is `ω^(β+1)` and the step is `ω^β`, so the bound says
`ω^(β+1)` is the NEXT additively principal term after `ω^β`.

The proof runs on §26's equation.  Suppose some AP `x` sits strictly between.  If `x` is a
fixed point it is its own `ω`-power, so the order reflects and `ω^(β+1) ≤ x`, contradicting
`x < ω^(β+1)`.  Otherwise `x = φ̄(0,b')`, and squeezing from both sides — `ω^b' ≤ x` and
`x ≤ ω^(succT b')` — forces `b' = β`; then `ω^(β+1) = φ̄(0,β) = x`, again a contradiction.

The step that makes the second half work is `splitFin_succT`: `succT` raises `splitFin`'s
finite part by exactly one and leaves its head alone, so the re-count that fails at `β` is
GUARANTEED to fire at `β+1` and land back on `β` (`dnArg_succT`). -/

theorem le_of_lt_succT {x y : Term} (hx : CNV x = true) (hy : CNV y = true)
    (h : lt x (succT y) = true) : le x y = true := by
  by_cases hle : le x y = true
  · exact hle
  · exfalso
    have hlt : lt y x = true := lt_of_not_le (frag_of_cnv _ hx) (frag_of_cnv _ hy) (bool_false hle)
    have hs2 : le (succT y) x = true := le_succT_of_lt y hy x hx hlt
    have hcon := lt_of_le_of_lt (frag_of_cnv _ (cnv_succT _ hy)) (frag_of_cnv _ hx)
      (frag_of_cnv _ (cnv_succT _ hy)) hs2 h
    rw [lt_irrefl] at hcon
    exact Bool.noConfusion hcon

theorem le_omegaNF_mono {a b : Term} (ha : CNV a = true) (hb : CNV b = true)
    (h : le a b = true) : le (omegaNF a) (omegaNF b) = true := by
  by_cases he : a = b
  · rw [he]; exact le_self _
  · exact le_of_lt (omegaNF_mono dnFacts ha hb (lt_of_le_of_ne h he))

/-- **`succT` は `splitFin` の finite 部を 1 上げるだけ。** -/
theorem splitFin_succT {b : Term} (hb : CNV b = true) :
    splitFin (succT b) = ((splitFin b).1, (splitFin b).2 + 1) := by
  cases hs : splitFin b with
  | mk g m =>
    have hcg : CNV g = true := by have h0 := cnv_splitFin hb; rw [hs] at h0; exact h0
    have hreb : plus g (ofNat m) = b := by
      have h0 := splitFin_rebuild b hb; rw [hs] at h0; exact h0
    have hlast := splitFin_fst_last hb hs
    have hsucc : succT b = plus g (ofNat (m + 1)) := by
      rw [plus_ofNat_step g hcg m, hreb]
    rw [hsucc, splitFin_plus_ofNat hcg hlast (m + 1)]

/-- 数え直しが `b` で起きるか `b` が不動点なら、`succT b` では必ず起きて `b` に戻る。 -/
theorem dnArg_succT {b : Term} (hcb : CNV b = true)
    (h : dnArg b ≠ b ∨ isFixP b = true) : dnArg (succT b) = b := by
  cases hs : splitFin b with
  | mk g m =>
    have hcg : CNV g = true := by have h0 := cnv_splitFin hcb; rw [hs] at h0; exact h0
    have hreb : plus g (ofNat m) = b := by
      have h0 := splitFin_rebuild b hcb; rw [hs] at h0; exact h0
    have hss : splitFin (succT b) = (g, m + 1) := by
      rw [splitFin_succT hcb, hs]
    have hshape : ∃ d e, g = phi d e ∧ lt zero d = true := by
      rcases h with hne | hf
      · rcases dnArg_or' hcb hs with hd | ⟨_, hg, _⟩
        · exact absurd hd hne
        · exact hg
      · cases hb' : b with
        | phi c d =>
          have hc : lt zero c = true := by rw [hb'] at hf; exact hf
          have hone : ((phi c d) == one) = false := by
            cases hq : ((phi c d) == one) with
            | false => rfl
            | true =>
              exfalso
              have h1 := eq_of_beq hq
              injection h1 with h2 _
              rw [h2, lt_irrefl] at hc
              exact Bool.noConfusion hc
          have hlast' : ∀ a, ((toList b).reverse).head? = some a → (a == one) = false := by
            intro a ha
            rw [hb', show toList (phi c d) = [phi c d] from rfl,
              show ([phi c d] : List Term).reverse.head? = some (phi c d) from rfl] at ha
            rw [(Option.some.inj ha).symm]
            exact hone
          have hb0 : splitFin b = (b, 0) := splitFin_plus_ofNat hcb hlast' 0
          rw [hs] at hb0
          injection hb0 with h1 _
          exact ⟨c, d, by rw [h1, hb'], hc⟩
        | zero => rw [hb'] at hf; exact Bool.noConfusion hf
        | M => rw [hb'] at hf; exact Bool.noConfusion hf
        | omg _ => rw [hb'] at hf; exact Bool.noConfusion hf
        | psi _ _ => rw [hb'] at hf; exact Bool.noConfusion hf
        | Z _ => rw [hb'] at hf; exact Bool.noConfusion hf
        | add _ _ => rw [hb'] at hf; exact Bool.noConfusion hf
    obtain ⟨d, e, hgphi, hd⟩ := hshape
    rw [dnArg_recount hss hgphi hd, hreb]

/-- `φ̄(0,b) ≤ ω^(succT b)` — D2 が「下げるのは高々 1」を言うので。 -/
theorem phi_zero_le_omegaNF_succT {b : Term} (hb : CNV b = true) :
    le (phi zero b) (omegaNF (succT b)) = true := by
  have hsc : CNV (succT b) = true := cnv_succT _ hb
  rw [omegaNF_eq hsc, if_neg (by rw [isFixP_succT]; intro hc; exact Bool.noConfusion hc)]
  have hd := dnArg_ge hb hsc (lt_succT b hb)
  by_cases he : b = dnArg (succT b)
  · rw [← he]; exact le_self _
  · exact le_of_lt (lt_phi_arg (lt_of_le_of_ne hd he))

/-- **`ω^(β+1)` の下にある加法主要な項は `ω^β` を超えない。** 組み合わせ子 (A) の上界。 -/
theorem ap_le_omegaNF_of_lt_succT {b x : Term} (hcb : CNV b = true) (hx : CNV x = true)
    (hapx : x.isAP = true) (h : lt x (omegaNF (succT b)) = true) :
    le x (omegaNF b) = true := by
  by_cases hle : le x (omegaNF b) = true
  · exact hle
  · exfalso
    have hcob : CNV (omegaNF b) = true := cnv_omegaNF hcb
    have hsb : CNV (succT b) = true := cnv_succT _ hcb
    have hlt : lt (omegaNF b) x = true :=
      lt_of_not_le (frag_of_cnv _ hx) (frag_of_cnv _ hcob) (bool_false hle)
    obtain ⟨a, b', hab⟩ := eq_phi_of_isAP_cnv hx hapx
    subst hab
    obtain ⟨hca, hcb'⟩ := cnv_phi hx
    by_cases haz : a = zero
    · subst haz
      have hsc' : CNV (succT b') = true := cnv_succT _ hcb'
      have h1 : lt (omegaNF b) (omegaNF (succT b')) = true :=
        lt_of_lt_of_le (frag_of_cnv _ hcob) (frag_of_cnv _ hx) (frag_of_cnv _ (cnv_omegaNF hsc'))
          hlt (phi_zero_le_omegaNF_succT hcb')
      have hbb' : le b b' = true :=
        le_of_lt_succT hcb hcb' (omegaNF_lt_reflect hcb hsc' h1)
      have h2 : lt (omegaNF b') (omegaNF (succT b)) = true :=
        lt_of_le_of_lt (frag_of_cnv _ (cnv_omegaNF hcb')) (frag_of_cnv _ hx)
          (frag_of_cnv _ (cnv_omegaNF hsb)) (omegaNF_le_phi_zero hcb') h
      have hb'b : le b' b = true :=
        le_of_lt_succT hcb' hcb (omegaNF_lt_reflect hcb' hsb h2)
      have heq : b = b' := le_antisymm (frag_of_cnv _ hcb) (frag_of_cnv _ hcb') hbb' hb'b
      subst heq
      have hcase : dnArg b ≠ b ∨ isFixP b = true := by
        by_cases hf : isFixP b = true
        · exact Or.inr hf
        · refine Or.inl ?_
          intro hdd
          rw [omegaNF_eq hcb, if_neg hf, hdd, lt_irrefl] at hlt
          exact Bool.noConfusion hlt
      have hom : omegaNF (succT b) = phi zero b := by
        rw [omegaNF_eq hsb, if_neg (by rw [isFixP_succT]; intro hc; exact Bool.noConfusion hc),
          dnArg_succT hcb hcase]
      rw [hom, lt_irrefl] at h
      exact Bool.noConfusion h
    · have hfx : isFixP (phi a b') = true := lt_zero_left haz
      have hxx : omegaNF (phi a b') = phi a b' := by rw [omegaNF_eq hx, if_pos hfx]
      have hbx : lt b (phi a b') = true :=
        omegaNF_lt_reflect hcb hx (by rw [hxx]; exact hlt)
      have hsx : le (succT b) (phi a b') = true := le_succT_of_lt b hcb _ hx hbx
      have h2 : le (omegaNF (succT b)) (phi a b') = true := by
        rw [← hxx]; exact le_omegaNF_mono hsb hx hsx
      have hcon := lt_of_le_of_lt (frag_of_cnv _ (cnv_omegaNF hsb)) (frag_of_cnv _ hx)
        (frag_of_cnv _ (cnv_omegaNF hsb)) h2 h
      rw [lt_irrefl] at hcon
      exact Bool.noConfusion hcon

/-! ## §33 `u·(k+1) ⊕ u = u·(k+2)`

The sequence identity `Evidence/RegionV.lean` §15.8 needs.  `plus` filters by the right
argument's head, and every component of `repAdd u k` IS that head, so nothing is dropped. -/

theorem toList_repAdd {u : Term} (hu : u.isAP = true) :
    ∀ n, toList (repAdd u n) = List.replicate (n + 1) u
  | 0 => by
    show toList u = [u]
    cases u <;> first | rfl | exact Bool.noConfusion hu
  | k + 1 => by
    show u :: toList (repAdd u k) = _
    rw [toList_repAdd hu k]
    rfl

/-- `u·(k+1) ⊕ u = u·(k+2)`。 -/
theorem plus_repAdd_self {u : Term} (hcu : CNV u = true) (hu : u.isAP = true) (k : Nat) :
    plus (repAdd u k) u = repAdd u (k + 1) := by
  have hto : toList u = [u] := by cases u <;> first | rfl | exact Bool.noConfusion hu
  have hcr : CNV (repAdd u (k + 1)) = true := by
    obtain ⟨p, q, hpq⟩ := eq_phi_of_isAP_cnv hcu hu
    rw [hpq]; exact cnv_repAdd (by rw [← hpq]; exact hcu) (k + 1)
  rw [plus_eq_of_toList (s := repAdd u k) (b1 := u) (rest := []) hto, hto,
    toList_repAdd hu k,
    filter_self_of_all _ _ (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact le_self _),
    ← List.replicate_succ' (n := k + 1) (a := u), ← toList_repAdd hu (k + 1),
    cnv_ofList_toList _ hcr]

end Evidence.WF
