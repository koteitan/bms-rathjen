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

end Evidence.WF
