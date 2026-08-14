import Trans.Pair
import Trans.Lemmas
/-
Evidence/StageA.lean — E3 in general form on the one-row region (Stage A)

(The import is deliberately on the first line: the kimina REPL used to verify this
file rejects a snippet whose `import` is preceded by a comment.)

WHAT IS PROVED.  For height-1 matrices (`oneRow s`, i.e. every column is a single
entry — the region where `Trans.oPr` is defined by `oPrAux` on row 0):

  e3_general  : stdSeq s → c ≠ 0 → s.getLast? = some c →
                ∀ n, o? (BMS.expand (oneRow s) n) = some (fsN (oPr (oneRow s)) (n+1))
  esucc_general : stdSeq s → s.getLast? = some 0 →
                ∀ n, o? (BMS.expand (oneRow s) n) = some (predT (oPr (oneRow s)))

(`e3_matrix` / `esucc_matrix` are the same statements for a matrix `X` given with
`X = oneRow (row0 X)`.)  The index shift by one is the convention of Trans/TM.lean:
`M[n]` lays down n+1 copies, so it corresponds to `t[n+1]`.

This subsumes and generalises the five per-row `e3` proofs and the two `esucc`
proofs of Rows/Proofs.lean: those rows are now instances (see §12), and so is every
other standard one-row matrix, e.g. `(0)(1)(2)(1)(2)`, `(0)(1)(2)(3)(3)(2)`, ….

THE INVARIANT (honest status).  The hypothesis is the syntactic predicate `stdSeq`
of §6: `s` is empty, or it starts with 0, each of its blocks (cut just before every
0) is again `stdSeq` after dropping the leading 0 and decrementing, and the block
values `ω^…` descend weakly (Cantor normal form).  It is decidable and computed by
`#guard` in §12.

  * `stdSeq` is NOT proved here to coincide with `BMS.Standard` (reachability from
    the initial matrix by expansions).  No such claim is made or used anywhere below.
  * Some hypothesis of this kind is unavoidable: `(0)(0)(1)` satisfies the naive
    condition `sᵢ₊₁ ≤ sᵢ + 1`, is rejected by `stdSeq`, and E3 genuinely fails for it
    (§12 checks the failure by computation).
  * Empirically `stdSeq` and BM4 standardness agree: over all 1364 one-row matrices
    of length ≤ 5 with entries ≤ 3 the yaBMS reference implementation
    (`c/bms -v 4 -s`) returns standard exactly on the `stdSeq`-true ones, and all 77
    `stdSeq`-true sequences of length ≤ 6 with entries ≤ 3 are standard for yaBMS.
    This is evidence, not a proof.

STRUCTURE.  §1–§3 blocks of a one-row sequence; §4–§5 the CNF shape of the terms
`Trans.oPr` produces and the behaviour of `plus`/`fsN` on them; §6 the standardness
predicate; §7–§8 the BM4 expansion on the one-row region (all ascension amounts
vanish there, so the rule is "copy the bad part n+1 times"); §9–§10 the induction on
the last block; §11 the two theorems; §12 checks.

References: [Rathjen, 1991] = M. Rathjen, "Proof-theoretic analysis of KPM", Arch. Math. Logic
30 (1991) 377–403 (term system 𝔗(M), normal operations 2.6); the BMS side follows
koteitan's formula-only definition of BM4 as transcribed in BMS/Expand.lean.
-/

namespace Evidence.StageA

open BMS (Matrix)
open TM (Term)
open TM.Term
open Trans

theorem blocks0_nil : blocks0 [] = [] := rfl

/-! ## §1 Blocks of a one-row sequence -/

/-- The sub-sequence encoded by a block: drop the leading 0, decrement. -/
def dec (b : List Nat) : List Nat := (b.drop 1).map (· - 1)

/-- `b` is a block: it starts with 0 and contains no further 0. -/
structure IsBlock (b : List Nat) : Prop where
  hd : b.head? = some 0
  tl : ∀ x ∈ b.drop 1, x ≠ 0

theorem headD_append_tail_flatten (l : List (List Nat)) :
    l.headD [] ++ l.tail.flatten = l.flatten := by
  cases l <;> rfl

theorem blocks0_flatten : ∀ s : List Nat, (blocks0 s).flatten = s
  | [] => rfl
  | x :: rest => by
    cases rest with
    | nil => rfl
    | cons y t =>
      by_cases hy : y = 0
      · subst hy
        rw [blocks0_cons_zero x (0 :: t) rfl]
        show x :: (blocks0 (0 :: t)).flatten = x :: 0 :: t
        rw [blocks0_flatten (0 :: t)]
      · have hb : blocks0 (x :: y :: t)
            = (x :: (blocks0 (y :: t)).headD []) :: (blocks0 (y :: t)).tail := by
          show (match blocks0 (y :: t), (y :: t).head? with
                | acc, some h => if h == 0 then [x] :: acc else (x :: acc.headD []) :: acc.tail
                | _, none => [[x]])
              = (x :: (blocks0 (y :: t)).headD []) :: (blocks0 (y :: t)).tail
          simp [hy]
        rw [hb]
        show (x :: (blocks0 (y :: t)).headD []) ++ (blocks0 (y :: t)).tail.flatten = x :: y :: t
        rw [List.cons_append, headD_append_tail_flatten, blocks0_flatten (y :: t)]

theorem blocks0_eq_nil_iff (s : List Nat) : blocks0 s = [] ↔ s = [] := by
  constructor
  · intro h
    have := blocks0_flatten s
    rw [h] at this
    exact this.symm
  · intro h; subst h; rfl

theorem length_le_of_mem_flatten :
    ∀ (l : List (List Nat)) (b : List Nat), b ∈ l → b.length ≤ l.flatten.length
  | [], _, h => absurd h (by simp)
  | c :: l', b, h => by
    rcases List.mem_cons.mp h with h | h
    · subst h
      show b.length ≤ (b ++ l'.flatten).length
      rw [List.length_append]
      omega
    · have := length_le_of_mem_flatten l' b h
      show b.length ≤ (c ++ l'.flatten).length
      rw [List.length_append]
      omega

theorem blocks0_length_le {s : List Nat} {b : List Nat} (h : b ∈ blocks0 s) :
    b.length ≤ s.length := by
  have := length_le_of_mem_flatten (blocks0 s) b h
  rwa [blocks0_flatten] at this

theorem dec_length (b : List Nat) : (dec b).length = b.length - 1 := by
  simp [dec]

/-- Splitting the concatenation: a new block starts exactly where `v` starts. -/
theorem blocks0_append :
    ∀ (u v : List Nat), (v = [] ∨ v.head? = some 0) →
      blocks0 (u ++ v) = blocks0 u ++ blocks0 v
  | [], v, _ => by simp [blocks0_nil]
  | x :: u', v, h => by
    cases u' with
    | nil =>
      rcases h with h | h
      · subst h; simp [blocks0_nil]
      · show blocks0 (x :: v) = blocks0 [x] ++ blocks0 v
        rw [blocks0_cons_zero x v h]
        rfl
    | cons y u'' =>
      have ih := blocks0_append (y :: u'') v h
      have hne : blocks0 (y :: u'') ≠ [] := fun hc =>
        absurd ((blocks0_eq_nil_iff _).mp hc) (by simp)
      by_cases hy : y = 0
      · subst hy
        have hcons : (x :: 0 :: u'') ++ v = x :: (0 :: (u'' ++ v)) := rfl
        have ih' : blocks0 (0 :: (u'' ++ v)) = blocks0 (0 :: u'') ++ blocks0 v := ih
        rw [hcons, blocks0_cons_zero x (0 :: (u'' ++ v)) rfl,
            blocks0_cons_zero x (0 :: u'') rfl, ih']
        rfl
      · have e1 : blocks0 (x :: ((y :: u'') ++ v))
            = (x :: (blocks0 ((y :: u'') ++ v)).headD []) :: (blocks0 ((y :: u'') ++ v)).tail := by
          show (match blocks0 ((y :: u'') ++ v), ((y :: u'') ++ v).head? with
                | acc, some hh => if hh == 0 then [x] :: acc else (x :: acc.headD []) :: acc.tail
                | _, none => [[x]])
              = (x :: (blocks0 ((y :: u'') ++ v)).headD []) :: (blocks0 ((y :: u'') ++ v)).tail
          simp [hy]
        have e2 : blocks0 (x :: (y :: u''))
            = (x :: (blocks0 (y :: u'')).headD []) :: (blocks0 (y :: u'')).tail := by
          show (match blocks0 (y :: u''), (y :: u'').head? with
                | acc, some hh => if hh == 0 then [x] :: acc else (x :: acc.headD []) :: acc.tail
                | _, none => [[x]])
              = (x :: (blocks0 (y :: u'')).headD []) :: (blocks0 (y :: u'')).tail
          simp [hy]
        rw [show (x :: (y :: u'')) ++ v = x :: ((y :: u'') ++ v) from rfl, e1, e2, ih]
        cases hbs : blocks0 (y :: u'') with
        | nil => exact absurd hbs hne
        | cons a l => simp

/-- A single block is its own block decomposition. -/
theorem blocks0_of_isBlock {b : List Nat} (h : IsBlock b) : blocks0 b = [b] := by
  cases b with
  | nil => exact absurd h.hd (by simp)
  | cons a t =>
    have ha : a = 0 := by simpa using h.hd
    subst ha
    exact blocks0_single 0 t (fun x hx => h.tl x (by simpa using hx))

/-- The block decomposition of a flattened list of blocks is that list. -/
theorem blocks0_flat :
    ∀ (bs : List (List Nat)), (∀ b ∈ bs, IsBlock b) → blocks0 bs.flatten = bs
  | [], _ => rfl
  | b :: bs', h => by
    have hb : IsBlock b := h b (by simp)
    have htail : bs'.flatten = [] ∨ bs'.flatten.head? = some 0 := by
      cases bs' with
      | nil => exact Or.inl rfl
      | cons c bs'' =>
        right
        have hc : IsBlock c := h c (by simp)
        cases c with
        | nil => exact absurd hc.hd (by simp)
        | cons a t =>
          have : a = 0 := by simpa using hc.hd
          subst this
          rfl
    show blocks0 (b ++ bs'.flatten) = b :: bs'
    rw [blocks0_append b bs'.flatten htail, blocks0_of_isBlock hb,
        blocks0_flat bs' (fun x hx => h x (by simp [hx]))]
    rfl

/-! ## §2 A fuel-free value function

`oPrAux` carries recursion fuel; as soon as the fuel is at least the length of the
sequence the result no longer depends on it, so on that range it is a genuine
function `oV` of the sequence alone, with the expected recursion equation.
-/

theorem oPrAux_fuel :
    ∀ (f g : Nat) (s : List Nat), s.length ≤ f → s.length ≤ g → oPrAux f s = oPrAux g s
  | 0, g, s, hf, _ => by
    have hs : s = [] := by
      cases s with
      | nil => rfl
      | cons a t => simp at hf
    subst hs
    rw [oPrAux_nil, oPrAux_nil]
  | f + 1, 0, s, _, hg => by
    have hs : s = [] := by
      cases s with
      | nil => rfl
      | cons a t => simp at hg
    subst hs
    rw [oPrAux_nil, oPrAux_nil]
  | f + 1, g + 1, s, hf, hg => by
    rw [oPrAux_unfold, oPrAux_unfold]
    refine congrArg _ (List.map_congr_left ?_)
    intro b hb
    have hbl : b.length ≤ s.length := blocks0_length_le hb
    refine congrArg _ (oPrAux_fuel f g (dec b) ?_ ?_) <;>
      · rw [dec_length]; simp at hf hg ⊢; omega

/-- The value of a one-row sequence, with the fuel fixed to a sufficient amount. -/
def oV (s : List Nat) : Term := oPrAux (s.length + 1) s

/-- The recursion equation of `oV`, free of fuel. -/
theorem oV_eq (s : List Nat) :
    oV s = ((blocks0 s).map (fun b => omegaNF (oV (dec b)))).foldr plus zero := by
  show oPrAux (s.length + 1) s = _
  rw [oPrAux_unfold]
  refine congrArg _ (List.map_congr_left ?_)
  intro b hb
  have hbl : b.length ≤ s.length := blocks0_length_le hb
  refine congrArg _ (oPrAux_fuel s.length ((dec b).length + 1) (dec b) ?_ ?_)
  · rw [dec_length]; omega
  · omega

theorem oV_nil : oV [] = zero := rfl

/-- `Trans.oPr` is `oV` of row 0. -/
theorem oPr_eq (M : Matrix) : oPr M = oV (row0 M) := by
  show oPrAux (M.length + 1) (row0 M) = oPrAux ((row0 M).length + 1) (row0 M)
  have : (row0 M).length = M.length := by simp [row0]
  rw [this]


/-! ## §3 Structure of the block decomposition

Every block produced by `blocks0` has no 0 after its first entry (blocks are cut
just before each 0), and every block but the first starts with 0.  Hence for a
sequence starting with 0 all blocks satisfy `IsBlock`.
-/

theorem blocks0_cons_nil (x : Nat) : blocks0 [x] = [[x]] := rfl

theorem blocks0_cons_nz (x y : Nat) (t : List Nat) (h : y ≠ 0) :
    blocks0 (x :: y :: t) = (x :: (blocks0 (y :: t)).headD []) :: (blocks0 (y :: t)).tail := by
  show (match blocks0 (y :: t), (y :: t).head? with
        | acc, some hh => if hh == 0 then [x] :: acc else (x :: acc.headD []) :: acc.tail
        | _, none => [[x]])
      = (x :: (blocks0 (y :: t)).headD []) :: (blocks0 (y :: t)).tail
  simp [h]

theorem mem_head_or_tail {α : Type _} [Inhabited α] (l : List α) (b : α) (h : b ∈ l) :
    b = l.headD default ∨ b ∈ l.tail := by
  cases l with
  | nil => exact absurd h (by simp)
  | cons a t => rcases List.mem_cons.mp h with h | h
                · exact Or.inl h
                · exact Or.inr h

/-- The first block of a nonempty sequence starts with its first entry. -/
theorem blocks0_head_cons (x : Nat) (s : List Nat) :
    ((blocks0 (x :: s)).headD []).head? = some x := by
  cases s with
  | nil => rfl
  | cons y t =>
    by_cases hy : y = 0
    · subst hy; rw [blocks0_cons_zero x (0 :: t) rfl]; rfl
    · rw [blocks0_cons_nz x y t hy]; rfl

/-- Every block but the first starts with 0. -/
theorem blocks0_tail_head : ∀ (s : List Nat), ∀ b ∈ (blocks0 s).tail, b.head? = some 0
  | [], b, hb => by simp [blocks0_nil] at hb
  | x :: s, b, hb => by
    cases s with
    | nil => simp [blocks0_cons_nil] at hb
    | cons y t =>
      by_cases hy : y = 0
      · subst hy
        rw [blocks0_cons_zero x (0 :: t) rfl] at hb
        have hb' : b ∈ blocks0 (0 :: t) := hb
        rcases mem_head_or_tail (blocks0 (0 :: t)) b hb' with h | h
        · rw [h]; exact blocks0_head_cons 0 t
        · exact blocks0_tail_head (0 :: t) b h
      · rw [blocks0_cons_nz x y t hy] at hb
        exact blocks0_tail_head (y :: t) b hb

/-- No block contains a 0 after its first entry. -/
theorem blocks0_tail_nz : ∀ (s : List Nat), ∀ b ∈ blocks0 s, ∀ x ∈ b.drop 1, x ≠ 0
  | [], b, hb, _, _ => by simp [blocks0_nil] at hb
  | x :: s, b, hb, z, hz => by
    cases s with
    | nil =>
      rw [blocks0_cons_nil] at hb
      have : b = [x] := by simpa using hb
      subst this; simp at hz
    | cons y t =>
      by_cases hy : y = 0
      · subst hy
        rw [blocks0_cons_zero x (0 :: t) rfl] at hb
        rcases List.mem_cons.mp hb with h | h
        · subst h; simp at hz
        · exact blocks0_tail_nz (0 :: t) b h z hz
      · rw [blocks0_cons_nz x y t hy] at hb
        rcases List.mem_cons.mp hb with h | h
        · subst h
          have hz' : z ∈ (blocks0 (y :: t)).headD [] := by simpa using hz
          have hne : blocks0 (y :: t) ≠ [] := fun hc =>
            absurd ((blocks0_eq_nil_iff _).mp hc) (by simp)
          have hmem : (blocks0 (y :: t)).headD [] ∈ blocks0 (y :: t) := by
            cases hbs : blocks0 (y :: t) with
            | nil => exact absurd hbs hne
            | cons a l => simp
          have hhd : ((blocks0 (y :: t)).headD []).head? = some y := blocks0_head_cons y t
          cases hc : (blocks0 (y :: t)).headD [] with
          | nil => rw [hc] at hhd; simp at hhd
          | cons a l =>
            rw [hc] at hhd hz'
            have ha : a = y := by simpa using hhd
            rcases List.mem_cons.mp hz' with h1 | h1
            · rw [h1, ha]; exact hy
            · refine blocks0_tail_nz (y :: t) (a :: l) ?_ z ?_
              · rw [← hc]; exact hmem
              · simpa using h1
        · exact blocks0_tail_nz (y :: t) b (List.mem_of_mem_tail h) z hz

/-- For a sequence starting with 0 every block is a genuine block. -/
theorem blocks0_isBlock {s : List Nat} (h : s = [] ∨ s.head? = some 0) :
    ∀ b ∈ blocks0 s, IsBlock b := by
  intro b hb
  refine ⟨?_, blocks0_tail_nz s b hb⟩
  rcases mem_head_or_tail (blocks0 s) b hb with h1 | h1
  · cases s with
    | nil => simp [blocks0_nil] at hb
    | cons x t =>
      have hx : x = 0 := by
        rcases h with h | h
        · simp at h
        · simpa using h
      subst hx
      rw [h1]; exact blocks0_head_cons 0 t
  · exact blocks0_tail_head s b h1


/-! ## §4 The shape of the terms produced by the translation

Every value of `oV` is a formal sum whose components are all of the form `φ̄0γ`
(this is exactly the CNF region below ε₀).  On such terms the normal operations
of [Rathjen, 1991] 2.6 collapse to the obvious ones: `ω^t = φ̄0t`.
-/

/-- Every additive component of `t` is of the form `φ̄0γ`. -/
def CompPhi0 (t : Term) : Prop := ∀ x ∈ toList t, ∃ c, x = phi zero c

theorem mem_take {α : Type _} : ∀ (l : List α) (k : Nat) (x : α), x ∈ l.take k → x ∈ l
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, h => by simp at h
  | a :: t, k + 1, x, h => by
    rcases List.mem_cons.mp h with h | h
    · exact h ▸ List.Mem.head _
    · exact List.mem_cons_of_mem a (mem_take t k x h)

theorem compPhi0_zero : CompPhi0 zero := by intro x hx; simp [toList] at hx

theorem compPhi0_phi0 (c : Term) : CompPhi0 (phi zero c) := by
  intro x hx
  have : x = phi zero c := by simpa [toList] using hx
  exact ⟨c, this⟩

theorem compPhi0_isAP {t : Term} (h : CompPhi0 t) : ∀ x ∈ toList t, x.isAP = true := by
  intro x hx
  obtain ⟨c, hc⟩ := h x hx
  subst hc; rfl

theorem compPhi0_ofList {l : List Term} (h : ∀ x ∈ l, ∃ c, x = phi zero c) :
    CompPhi0 (ofList l) := by
  intro x hx
  have hap : ∀ y ∈ l, y.isAP = true := by
    intro y hy; obtain ⟨c, hc⟩ := h y hy; subst hc; rfl
  rw [toList_ofList hap] at hx
  exact h x hx

theorem compPhi0_isSC {t : Term} (h : CompPhi0 t) : t.isSC = false := by
  cases t with
  | zero => rfl
  | M => obtain ⟨c, hc⟩ := h M (List.Mem.head _); exact absurd hc (by simp)
  | add a b => rfl
  | omg a => rfl
  | phi a b => rfl
  | psi k a => obtain ⟨c, hc⟩ := h (psi k a) (List.Mem.head _); exact absurd hc (by simp)
  | Z a => obtain ⟨c, hc⟩ := h (Z a) (List.Mem.head _); exact absurd hc (by simp)

theorem compPhi0_ne_M {t : Term} (h : CompPhi0 t) : (t == M) = false := by
  cases t with
  | M => obtain ⟨c, hc⟩ := h M (List.Mem.head _); exact absurd hc (by simp)
  | _ => rfl

theorem compPhi0_phi_arg {c d : Term} (h : CompPhi0 (phi c d)) : c = zero := by
  obtain ⟨e, he⟩ := h (phi c d) (List.Mem.head _)
  exact (Term.phi.injEq c d zero e ▸ he) |>.1

/-! ### `ω^·` is `φ̄0·` in this region -/

theorem ltF_M_phi (f : Nat) (a b : Term) : ltF f M (phi a b) = false := by
  cases f <;> rfl

theorem ltF_M_false : ∀ (f : Nat) (t : Term), CompPhi0 t → ltF f M t = false
  | 0, _, _ => rfl
  | _ + 1, zero, _ => rfl
  | _ + 1, M, h => by obtain ⟨c, hc⟩ := h M (List.Mem.head _); exact absurd hc (by simp)
  | f + 1, add a b, h => by
    obtain ⟨c, hc⟩ := h a (List.Mem.head _)
    subst hc
    show (M == phi zero c || ltF f M (phi zero c)) = false
    rw [ltF_M_phi]; rfl
  | _ + 1, omg a, h => by obtain ⟨c, hc⟩ := h (omg a) (List.Mem.head _); exact absurd hc (by simp)
  | _ + 1, phi a b, _ => rfl
  | _ + 1, psi k a, h => by
    obtain ⟨c, hc⟩ := h (psi k a) (List.Mem.head _); exact absurd hc (by simp)
  | _ + 1, Z a, h => by obtain ⟨c, hc⟩ := h (Z a) (List.Mem.head _); exact absurd hc (by simp)

theorem lt_M_of_compPhi0 {t : Term} (h : CompPhi0 t) : lt M t = false := ltF_M_false _ t h

theorem lt_zero_zero : lt zero zero = false := rfl

/-- `φ̄0·` on the CNF region: `phiNFdefault` is the raw constructor. -/
theorem phiNFdefault_zero (t : Term) : phiNFdefault zero t = phi zero t := by
  unfold phiNFdefault; simp [isSC]

theorem phiNFsucc_zero {t : Term} (h : CompPhi0 t) : phiNFsucc zero t = phi zero t := by
  have hdef : phiNFdefault zero t = phi zero t := phiNFdefault_zero t
  have hg : CompPhi0 (splitFin t).1 := by
    show CompPhi0 (ofList ((toList t).take ((toList t).length - _)))
    exact compPhi0_ofList (fun x hx => h x (mem_take _ _ x hx))
  rcases hsp : splitFin t with ⟨g, m⟩
  rw [hsp] at hg
  unfold phiNFsucc
  rw [hsp]
  by_cases hm : m ≥ 1
  · cases g with
    | phi d e =>
      have hd : d = zero := compPhi0_phi_arg hg
      subst hd
      simp only [hm, if_true, lt_zero_zero, Bool.false_eq_true, if_false]
      exact hdef
    | zero => simp only [hm, if_true]; simp [isSC, hdef]
    | add a b => simp only [hm, if_true]; simp [isSC, hdef]
    | omg a => simp only [hm, if_true]; simp [isSC, hdef]
    | M => exact absurd (compPhi0_isSC hg) (by simp [isSC])
    | psi k a => exact absurd (compPhi0_isSC hg) (by simp [isSC])
    | Z a => exact absurd (compPhi0_isSC hg) (by simp [isSC])
  · simp only [hm, if_false]
    exact hdef

theorem phiNF_zero_of_compPhi0 {t : Term} (h : CompPhi0 t) : phiNF zero t = phi zero t := by
  have hsc : t.isSC = false := compPhi0_isSC h
  have hsucc : phiNFsucc zero t = phi zero t := phiNFsucc_zero h
  unfold phiNF
  rw [hsc]
  simp only [Bool.false_and, Bool.false_eq_true, if_false]
  cases t with
  | phi c d =>
    have hc : c = zero := compPhi0_phi_arg h
    subst hc
    simp only [lt_zero_zero, Bool.false_eq_true, if_false]
    exact hsucc
  | _ => exact hsucc

theorem omegaNF_of_compPhi0 {t : Term} (h : CompPhi0 t) : omegaNF t = phi zero t := by
  unfold omegaNF
  rw [lt_M_of_compPhi0 h]
  simp only [Bool.false_eq_true, if_false]
  rw [compPhi0_ne_M h]
  simp only [Bool.false_eq_true, if_false]
  exact phiNF_zero_of_compPhi0 h


/-! ## §5 Formal sums with weakly descending components

In this region `plus` never has to filter anything away, so a fold of `plus` is
literally `ofList`, and the fundamental sequence of a sum propagates into the last
component.
-/

/-- The components of a list descend weakly. -/
def descB : List Term → Bool
  | x :: y :: r => le y x && descB (y :: r)
  | _ => true

theorem descB_cons2 (x y : Term) (r : List Term) :
    descB (x :: y :: r) = (le y x && descB (y :: r)) := rfl

theorem le_self (y : Term) : le y y = true := by simp [TM.Term.le]

theorem ofList_cons2 (x y : Term) (r : List Term) :
    ofList (x :: y :: r) = add x (ofList (y :: r)) := rfl

theorem plus_ofList_cons {x y : Term} {r : List Term} (hx : x.isAP = true)
    (hall : ∀ z ∈ y :: r, z.isAP = true) (hle : le y x = true) :
    plus x (ofList (y :: r)) = ofList (x :: y :: r) := by
  show (match toList (ofList (y :: r)) with
        | [] => x
        | b1 :: _ => ofList ((toList x).filter (fun a => le b1 a) ++ toList (ofList (y :: r))))
      = ofList (x :: y :: r)
  rw [toList_ofList hall, toList_of_isAP hx]
  show ofList ((match le y x with | true => [x] | false => []) ++ y :: r) = ofList (x :: y :: r)
  rw [hle]
  rfl

theorem foldr_plus_eq_ofList : ∀ (l : List Term), (∀ x ∈ l, x.isAP = true) → descB l = true →
    l.foldr plus zero = ofList l
  | [], _, _ => rfl
  | [x], _, _ => plus_zero x
  | x :: y :: r, hap, hd => by
    rw [descB_cons2] at hd
    have hle : le y x = true := (Bool.and_eq_true _ _).mp hd |>.1
    have hd' : descB (y :: r) = true := (Bool.and_eq_true _ _).mp hd |>.2
    have hap' : ∀ z ∈ y :: r, z.isAP = true := fun z hz => hap z (List.mem_cons_of_mem x hz)
    show plus x ((y :: r).foldr plus zero) = ofList (x :: y :: r)
    rw [foldr_plus_eq_ofList (y :: r) hap' hd']
    exact plus_ofList_cons (hap x (List.Mem.head _)) hap' hle

theorem descB_replicate (y : Term) : ∀ k, descB (List.replicate k y) = true
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
    show descB (y :: y :: List.replicate k y) = true
    rw [descB_cons2, le_self]
    have := descB_replicate y (k + 1)
    show (true && descB (y :: List.replicate k y)) = true
    simpa using this

theorem foldr_plus_replicate {y : Term} (hy : y.isAP = true) (k : Nat) :
    (List.replicate k y).foldr plus zero = mulNat y k := by
  rw [foldr_plus_eq_ofList _ (fun z hz => by rw [List.eq_of_mem_replicate hz]; exact hy)
      (descB_replicate y k)]
  rfl

theorem ofList_ne_zero {l : List Term} (hne : l ≠ []) (hap : ∀ x ∈ l, x.isAP = true) :
    ofList l ≠ zero := by
  cases l with
  | nil => exact absurd rfl hne
  | cons x r =>
    cases r with
    | nil =>
      have := hap x (List.Mem.head _)
      cases x <;> first | (intro hc; exact Term.noConfusion hc) | simp [isAP] at this
    | cons y r' => intro hc; exact Term.noConfusion hc

/-! ### Fundamental sequences of sums and of `φ̄0·` -/

theorem fsN_add (a b : Term) (n : Nat) : fsN (add a b) n = plus a (fsN b n) := by rw [fsN]

theorem fsN_ofList_append : ∀ (X : List Term) (z : Term) (n : Nat),
    fsN (ofList (X ++ [z])) n = X.foldr plus (fsN z n)
  | [], _, _ => rfl
  | x :: X', z, n => by
    have hcons : ofList (x :: (X' ++ [z])) = add x (ofList (X' ++ [z])) := by
      cases X' <;> rfl
    show fsN (ofList (x :: (X' ++ [z]))) n = _
    rw [hcons, fsN_add, fsN_ofList_append X' z n]
    rfl

theorem isFP_zero {g : Term} (hg : CompPhi0 g) : isFP zero g = false := by
  unfold isFP
  rw [compPhi0_isSC hg]
  simp only [Bool.false_and, Bool.false_or]
  cases g with
  | phi c d => have hc := compPhi0_phi_arg hg; subst hc; exact lt_zero_zero
  | _ => rfl

theorem phiShifted_zero_eq {X : Term} (h : CompPhi0 X) : phiShifted zero X = false := by
  have hg : CompPhi0 (splitFin X).1 := by
    show CompPhi0 (ofList ((toList X).take ((toList X).length - _)))
    exact compPhi0_ofList (fun x hx => h x (mem_take _ _ x hx))
  unfold phiShifted
  rw [isFP_zero hg]
  simp [isSC]

theorem fsN_phi0_succ {X : Term} (h : CompPhi0 X) (hk : kindT X = .isSucc) (n : Nat) :
    fsN (phi zero X) n = mulNat (omegaNF (predT X)) n := by
  rw [fsN]
  simp only [phiShifted_zero_eq h, hk, Bool.false_or, beq_self_eq_true, if_true,
    Bool.false_eq_true, if_false]
  rfl

theorem fsN_phi0_lim {X : Term} (h : CompPhi0 X) (hk : kindT X = .isLim) (n : Nat) :
    fsN (phi zero X) n = phiNF zero (fsN X n) := by
  rw [fsN]
  simp only [phiShifted_zero_eq h, hk, Bool.false_or, beq_self_eq_true, if_true,
    Bool.false_eq_true, if_false]
  rfl

theorem kindT_ne_zero {t : Term} (ht : t ≠ zero) :
    kindT t = if ((toList t).getLast? == some one) = true then .isSucc else .isLim := by
  cases t with
  | zero => exact absurd rfl ht
  | _ => rfl

theorem predT_eq {t : Term} (h : ((toList t).getLast? == some one) = true) :
    predT t = ofList (toList t).dropLast := by
  show (if ((toList t).getLast? == some one) = true then ofList (toList t).dropLast else zero)
      = ofList (toList t).dropLast
  rw [h]; rfl


/-! ## §6 Standard one-row sequences

`stdSeq` is the syntactic standard-form (Cantor normal form) predicate of the
primitive sequence system: a sequence is standard when it is empty, or it starts
with 0, each of its blocks is again standard after dropping the leading 0 and
decrementing, and the values of its blocks descend weakly.

HONESTY NOTE.  `stdSeq` is NOT proved here to coincide with `BMS.Standard`
(reachability from the initial matrix by expansions); that equivalence is stated
nowhere below and is not used.  Everything proved in this file is proved under
`stdSeq` as an explicit hypothesis.  For example `(0)(0)(1)` satisfies
`sᵢ₊₁ ≤ sᵢ + 1` but is rejected by `stdSeq` (its block values 1, ω ascend), and
E3 genuinely fails for it — so some such hypothesis is unavoidable.
-/

/-- The values of the blocks of `s`, in order. -/
def blockVals (s : List Nat) : List Term := (blocks0 s).map (fun b => omegaNF (oV (dec b)))

theorem oV_eq' (s : List Nat) : oV s = (blockVals s).foldr plus zero := oV_eq s

theorem all_congr {α : Type _} : ∀ (l : List α) (p q : α → Bool), (∀ a ∈ l, p a = q a) →
    l.all p = l.all q
  | [], _, _, _ => rfl
  | a :: t, p, q, h => by
    rw [List.all_cons, List.all_cons, h a (List.Mem.head _),
      all_congr t p q (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- Standard form, with recursion fuel. -/
def stdAux : Nat → List Nat → Bool
  | 0, s => s.isEmpty
  | f + 1, s =>
      (s.isEmpty || s.head? == some 0)
      && (blocks0 s).all (fun b => stdAux f (dec b))
      && descB (blockVals s)

theorem stdAux_nil : ∀ f, stdAux f [] = true
  | 0 => rfl
  | _ + 1 => rfl

theorem stdAux_fuel : ∀ (f g : Nat) (s : List Nat), s.length ≤ f → s.length ≤ g →
    stdAux f s = stdAux g s
  | 0, g, s, hf, _ => by
    have hs : s = [] := by cases s with | nil => rfl | cons a t => simp at hf
    subst hs; rw [stdAux_nil, stdAux_nil]
  | f + 1, 0, s, _, hg => by
    have hs : s = [] := by cases s with | nil => rfl | cons a t => simp at hg
    subst hs; rw [stdAux_nil, stdAux_nil]
  | f + 1, g + 1, s, hf, hg => by
    show ((s.isEmpty || s.head? == some 0) && (blocks0 s).all (fun b => stdAux f (dec b))
          && descB (blockVals s))
       = ((s.isEmpty || s.head? == some 0) && (blocks0 s).all (fun b => stdAux g (dec b))
          && descB (blockVals s))
    rw [all_congr (blocks0 s) _ _ ?_]
    intro b hb
    have hbl : b.length ≤ s.length := blocks0_length_le hb
    refine stdAux_fuel f g (dec b) ?_ ?_ <;>
      · rw [dec_length]; simp at hf hg ⊢; omega

/-- Standard form of a one-row sequence (see the honesty note above). -/
def stdSeq (s : List Nat) : Bool := stdAux (s.length + 1) s

theorem stdSeq_eq (s : List Nat) :
    stdSeq s = ((s.isEmpty || s.head? == some 0)
      && (blocks0 s).all (fun b => stdSeq (dec b))
      && descB (blockVals s)) := by
  show ((s.isEmpty || s.head? == some 0) && (blocks0 s).all (fun b => stdAux s.length (dec b))
        && descB (blockVals s)) = _
  rw [all_congr (blocks0 s) _ _ ?_]
  intro b hb
  have hbl : b.length ≤ s.length := blocks0_length_le hb
  exact stdAux_fuel s.length ((dec b).length + 1) (dec b) (by rw [dec_length]; omega) (by omega)

theorem stdSeq_nil : stdSeq [] = true := stdAux_nil _

theorem stdSeq_head {s : List Nat} (h : stdSeq s = true) : s = [] ∨ s.head? = some 0 := by
  rw [stdSeq_eq] at h
  have h1 : (s.isEmpty || s.head? == some 0) = true := by
    simp only [Bool.and_eq_true] at h; exact h.1.1
  cases s with
  | nil => exact Or.inl rfl
  | cons a t => right; simpa using h1

theorem stdSeq_blocks {s : List Nat} (h : stdSeq s = true) :
    ∀ b ∈ blocks0 s, stdSeq (dec b) = true := by
  rw [stdSeq_eq] at h
  simp only [Bool.and_eq_true] at h
  intro b hb
  exact List.all_eq_true.mp h.1.2 b hb

theorem stdSeq_desc {s : List Nat} (h : stdSeq s = true) : descB (blockVals s) = true := by
  rw [stdSeq_eq] at h
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem stdSeq_isBlock {s : List Nat} (h : stdSeq s = true) : ∀ b ∈ blocks0 s, IsBlock b :=
  blocks0_isBlock (stdSeq_head h)

/-! ### Every standard value is a CNF term -/

theorem compPhi0_plus {x Y : Term} (hx : ∃ c, x = phi zero c) (hY : CompPhi0 Y) :
    CompPhi0 (plus x Y) := by
  unfold plus
  cases hl : toList Y with
  | nil => obtain ⟨c, hc⟩ := hx; subst hc; exact compPhi0_phi0 c
  | cons b1 rest =>
    refine compPhi0_ofList ?_
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨c, hc⟩ := hx
      subst hc
      have hz' : z ∈ toList (phi zero c) := (List.mem_filter.mp hz).1
      exact ⟨c, by simpa [toList] using hz'⟩
    · exact hY z (by rw [hl]; exact hz)

theorem compPhi0_foldr : ∀ (l : List Term), (∀ x ∈ l, ∃ c, x = phi zero c) →
    CompPhi0 (l.foldr plus zero)
  | [], _ => compPhi0_zero
  | x :: r, h => by
    show CompPhi0 (plus x (r.foldr plus zero))
    exact compPhi0_plus (h x (List.Mem.head _))
      (compPhi0_foldr r (fun z hz => h z (List.mem_cons_of_mem x hz)))

theorem compPhi0_oV_aux : ∀ (f : Nat) (s : List Nat), s.length ≤ f →
    (∀ x ∈ blockVals s, ∃ c, x = phi zero c)
  | 0, s, hf => by
    have hs : s = [] := by cases s with | nil => rfl | cons a t => simp at hf
    subst hs
    intro x hx; simp [blockVals, blocks0_nil] at hx
  | f + 1, s, hf => by
    intro x hx
    have hx' : ∃ b ∈ blocks0 s, omegaNF (oV (dec b)) = x := by
      simpa [blockVals] using hx
    obtain ⟨b, hb, hbx⟩ := hx'
    have hbl : b.length ≤ s.length := blocks0_length_le hb
    have hlen : (dec b).length ≤ f := by rw [dec_length]; omega
    have hcp : CompPhi0 (oV (dec b)) := by
      rw [oV_eq' (dec b)]
      exact compPhi0_foldr _ (compPhi0_oV_aux f (dec b) hlen)
    exact ⟨oV (dec b), by rw [← hbx, omegaNF_of_compPhi0 hcp]⟩

/-- Every value of `oV` is a CNF term: no standardness needed. -/
theorem blockVals_phi0 (s : List Nat) : ∀ x ∈ blockVals s, ∃ c, x = phi zero c :=
  compPhi0_oV_aux s.length s (Nat.le_refl _)

theorem blockVals_isAP (s : List Nat) : ∀ x ∈ blockVals s, x.isAP = true := by
  intro x hx; obtain ⟨c, hc⟩ := blockVals_phi0 s x hx; subst hc; rfl

theorem compPhi0_oV (s : List Nat) : CompPhi0 (oV s) := by
  rw [oV_eq' s]; exact compPhi0_foldr _ (blockVals_phi0 s)

theorem blockVal_eq (b : List Nat) : omegaNF (oV (dec b)) = phi zero (oV (dec b)) :=
  omegaNF_of_compPhi0 (compPhi0_oV (dec b))

/-- For a standard sequence the fold of `plus` is a plain formal sum. -/
theorem oV_ofList {s : List Nat} (h : stdSeq s = true) : oV s = ofList (blockVals s) := by
  rw [oV_eq' s]
  exact foldr_plus_eq_ofList _ (blockVals_isAP s) (stdSeq_desc h)

theorem toList_oV {s : List Nat} (h : stdSeq s = true) : toList (oV s) = blockVals s := by
  rw [oV_ofList h, toList_ofList (blockVals_isAP s)]


/-! ## §7 Blocks, repetitions and small list lemmas -/

/-- The block encoding of a sub-sequence: `t ↦ (0)(t₁+1)(t₂+1)…`. -/
def mkBlock (t : List Nat) : List Nat := 0 :: t.map (· + 1)

/-- `B` repeated `k` times (the sequence-level version of `Trans.repM`). -/
def repL (B : List Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => B ++ repL B k

theorem dec_mkBlock (t : List Nat) : dec (mkBlock t) = t := by
  show ((0 :: t.map (· + 1)).drop 1).map (· - 1) = t
  simp [Function.comp_def]

theorem isBlock_mkBlock (t : List Nat) : IsBlock (mkBlock t) := by
  refine ⟨rfl, ?_⟩
  intro x hx
  have hx' : x ∈ t.map (· + 1) := by simpa [mkBlock] using hx
  obtain ⟨y, _, hy⟩ := List.mem_map.mp hx'
  omega

theorem head?_repL {B : List Nat} (h : B.head? = some 0) :
    ∀ k, repL B k = [] ∨ (repL B k).head? = some 0
  | 0 => Or.inl rfl
  | _ + 1 => by
    right
    cases B with
    | nil => simp at h
    | cons a t =>
      have ha : a = 0 := by simpa using h
      subst ha; rfl

theorem blocks0_repL {b : List Nat} (hb : IsBlock b) :
    ∀ k, blocks0 (repL b k) = List.replicate k b
  | 0 => rfl
  | k + 1 => by
    show blocks0 (b ++ repL b k) = b :: List.replicate k b
    rw [blocks0_append b (repL b k) (head?_repL hb.hd k), blocks0_of_isBlock hb,
        blocks0_repL hb k]
    rfl

theorem repL_map (f : Nat → Nat) (B : List Nat) : ∀ k, (repL B k).map f = repL (B.map f) k
  | 0 => rfl
  | k + 1 => by
    show (B ++ repL B k).map f = B.map f ++ repL (B.map f) k
    rw [List.map_append, repL_map f B k]

theorem blockVals_append (u v : List Nat) (h : v = [] ∨ v.head? = some 0) :
    blockVals (u ++ v) = blockVals u ++ blockVals v := by
  show ((blocks0 (u ++ v)).map _) = _
  rw [blocks0_append u v h]
  exact List.map_append

theorem descB_dropLast : ∀ (l : List Term), descB l = true → descB l.dropLast = true
  | [], _ => rfl
  | [_], _ => rfl
  | x :: y :: r, h => by
    rw [descB_cons2] at h
    have hle : le y x = true := (Bool.and_eq_true _ _).mp h |>.1
    have hd : descB (y :: r) = true := (Bool.and_eq_true _ _).mp h |>.2
    have ih := descB_dropLast (y :: r) hd
    cases r with
    | nil => rfl
    | cons z r' =>
      show descB (x :: y :: (z :: r').dropLast) = true
      rw [descB_cons2, hle]
      simpa using ih

theorem plus_phi0_ne_zero {c Y : Term} (hY : CompPhi0 Y) : plus (phi zero c) Y ≠ zero := by
  unfold plus
  cases hl : toList Y with
  | nil => intro hc; exact Term.noConfusion hc
  | cons b1 rest =>
    refine ofList_ne_zero (by simp) ?_
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · have hz' : z ∈ toList (phi zero c) := (List.mem_filter.mp hz).1
      have : z = phi zero c := by simpa [toList] using hz'
      subst this; rfl
    · have hz' : z ∈ toList Y := by rw [hl]; exact hz
      obtain ⟨e, he⟩ := hY z hz'
      subst he; rfl

theorem blockVals_ne_nil {s : List Nat} (h : s ≠ []) : blockVals s ≠ [] := by
  intro hc
  have hb : blocks0 s = [] := by simpa [blockVals] using hc
  exact h ((blocks0_eq_nil_iff s).mp hb)

theorem oV_ne_zero {s : List Nat} (h : s ≠ []) : oV s ≠ zero := by
  rw [oV_eq' s]
  have hne : blockVals s ≠ [] := blockVals_ne_nil h
  have hph := blockVals_phi0 s
  cases hbv : blockVals s with
  | nil => exact absurd hbv hne
  | cons x r =>
    obtain ⟨c, hc⟩ := hph x (by rw [hbv]; exact List.Mem.head _)
    show plus x (r.foldr plus zero) ≠ zero
    subst hc
    exact plus_phi0_ne_zero
      (compPhi0_foldr r (fun z hz => hph z (by rw [hbv]; exact List.mem_cons_of_mem _ hz)))

theorem getD_mem : ∀ (l : List Nat) (j : Nat), j < l.length → l.getD j 0 ∈ l
  | [], _, h => by simp at h
  | a :: t, 0, _ => List.Mem.head _
  | a :: t, j + 1, h => by
    rw [List.getD_cons_succ]
    exact List.mem_cons_of_mem a (getD_mem t j (by simp at h; omega))

theorem getD_append_lt (l r : List Nat) (p : Nat) (h : p < l.length) :
    (l ++ r).getD p 0 = l.getD p 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_ge (l r : List Nat) (p : Nat) (h : l.length ≤ p) :
    (l ++ r).getD p 0 = r.getD (p - l.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_concat (l : List Nat) (c : Nat) : (l ++ [c]).getD l.length 0 = c := by
  rw [getD_append_ge l [c] l.length (Nat.le_refl _)]
  simp

/-! ## §8 The BM4 expansion on the one-row region

For a matrix whose only nonzero row is row 0 the lowest nonzero row of the last
column is row 0, hence every ascension amount `Δ_y` vanishes and the expansion is
the plain "copy the bad part `n+1` times" rule:

    A B c  ↦  A B B … B   (n+1 copies of B)

where `c` is the last entry and `B` starts at the bad root.
-/

/-- A matrix of height 1 with the given row 0. -/
def oneRow (s : List Nat) : Matrix := s.map (fun a => [a])

theorem row0_oneRow (s : List Nat) : row0 (oneRow s) = s := by
  simp [row0, oneRow, Function.comp_def]

theorem onlyRow0_oneRow (s : List Nat) : onlyRow0 (oneRow s) = true := by
  simp [onlyRow0, oneRow]

theorem oneRow_append (u v : List Nat) : oneRow (u ++ v) = oneRow u ++ oneRow v :=
  List.map_append

theorem length_oneRow (s : List Nat) : (oneRow s).length = s.length := List.length_map _

theorem oneRow_repL (B : List Nat) : ∀ k, oneRow (repL B k) = repM (oneRow B) k
  | 0 => rfl
  | k + 1 => by
    show oneRow (B ++ repL B k) = oneRow B ++ repM (oneRow B) k
    rw [oneRow_append, oneRow_repL B k]

theorem ent_oneRow : ∀ (s : List Nat) (p : Nat), BMS.ent (oneRow s) p 0 = s.getD p 0
  | [], p => by cases p <;> rfl
  | _ :: _, 0 => rfl
  | a :: t, p + 1 => by
    have h1 : BMS.ent (oneRow (a :: t)) (p + 1) 0 = BMS.ent (oneRow t) p 0 := by
      show ((([a] : List Nat) :: oneRow t).getD (p + 1) []).getD 0 0
          = ((oneRow t).getD p []).getD 0 0
      rw [List.getD_cons_succ]
    rw [h1, ent_oneRow t p, List.getD_cons_succ]

/-- `o?` is defined on every one-row matrix and computes `oV` of its row 0. -/
theorem o?_oneRow (s : List Nat) : o? (oneRow s) = some (oV s) := by
  show (if onlyRow0 (oneRow s) = true then some (oPr (oneRow s)) else oPair? (oneRow s))
      = some (oV s)
  rw [onlyRow0_oneRow]
  simp only [if_true]
  rw [oPr_eq, row0_oneRow]

/-! ### The bad root -/

/-- The largest `x' < x` with `P x'`. -/
def lastSome (P : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | x + 1 => if P x then some x else lastSome P x

theorem foldl_max_le : ∀ (l : List Nat) (a x : Nat), a ≤ x → (∀ y ∈ l, y ≤ x) →
    l.foldl max a ≤ x
  | [], _, _, ha, _ => ha
  | b :: t, a, x, ha, h => by
    have hb : b ≤ x := h b (List.Mem.head _)
    show t.foldl max (max a b) ≤ x
    exact foldl_max_le t (max a b) x (by omega) (fun y hy => h y (List.mem_cons_of_mem b hy))

theorem max?_append_singleton : ∀ (l : List Nat) (x : Nat), (∀ y ∈ l, y ≤ x) →
    (l ++ [x]).max? = some x
  | [], _, _ => rfl
  | a :: t, x, h => by
    have ha : a ≤ x := h a (List.Mem.head _)
    have hb : t.foldl max a ≤ x :=
      foldl_max_le t a x ha (fun y hy => h y (List.mem_cons_of_mem a hy))
    show some ((t ++ [x]).foldl max a) = some x
    rw [List.foldl_append]
    show some (max (t.foldl max a) x) = some x
    rw [Nat.max_eq_right hb]

theorem max?_filter_range (P : Nat → Bool) : ∀ x, ((List.range x).filter P).max? = lastSome P x
  | 0 => rfl
  | x + 1 => by
    rw [List.range_succ, List.filter_append]
    cases hx : P x with
    | true =>
      have h1 : List.filter P [x] = [x] := by simp [hx]
      rw [h1, max?_append_singleton _ x ?_]
      · show some x = if P x = true then some x else lastSome P x
        rw [hx]; rfl
      · intro y hy
        have h2 := List.mem_range.mp (List.mem_filter.mp hy).1
        omega
    | false =>
      have h1 : List.filter P [x] = [] := by simp [hx]
      rw [h1, List.append_nil, max?_filter_range P x]
      show lastSome P x = if P x = true then some x else lastSome P x
      rw [hx]; rfl

theorem lastSome_spec (P : Nat → Bool) : ∀ (x r : Nat), r < x → P r = true →
    (∀ q, r < q → q < x → P q = false) → lastSome P x = some r
  | 0, _, h, _, _ => by omega
  | x + 1, r, hr, hP, hmax => by
    show (if P x = true then some x else lastSome P x) = some r
    cases hx : P x with
    | true =>
      have hrx : r = x := by
        rcases Nat.lt_or_ge r x with h | h
        · have hc : P x = false := hmax x h (by omega)
          rw [hx] at hc; exact Bool.noConfusion hc
        · omega
      simp [hrx]
    | false =>
      have hrx : r < x := by
        rcases Nat.lt_or_ge r x with h | h
        · exact h
        · have hrx' : r = x := by omega
          rw [hrx', hx] at hP; exact Bool.noConfusion hP
      simp only [Bool.false_eq_true, if_false]
      exact lastSome_spec P x r hrx hP (fun q h1 h2 => hmax q h1 (by omega))


theorem range_map_getD : ∀ (k : Nat) (l : List Nat), k ≤ l.length →
    (List.range k).map (fun x => l.getD x 0) = l.take k
  | 0, _, _ => rfl
  | k + 1, l, h => by
    have hk : k < l.length := by omega
    rw [List.range_succ, List.map_append, range_map_getD k l (by omega), List.take_add_one]
    congr 1
    show [l.getD k 0] = l[k]?.toList
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rfl

theorem delta_zero (M : Matrix) (r y : Nat) : BMS.delta M r 0 y = 0 := by
  simp [BMS.delta]

/-- The bad root of a one-row limit sequence `A ++ B ++ [c]` is `|A|`, provided the
    entry at `|A|` is `< c` and all entries strictly between it and `c` are `≥ c`. -/
theorem parent_oneRow {A B : List Nat} {c b0 : Nat} {B' : List Nat}
    (hB : B = b0 :: B') (hb0 : b0 < c) (hrest : ∀ x ∈ B', c ≤ x) :
    BMS.parent (oneRow ((A ++ B) ++ [c])) 0 ((oneRow ((A ++ B) ++ [c])).length - 1)
      = some A.length := by
  have hBlen : B.length = B'.length + 1 := by rw [hB]; simp
  have hx : (oneRow ((A ++ B) ++ [c])).length - 1 = A.length + B.length := by
    rw [length_oneRow, List.length_append, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega
  have hc' : ((A ++ B) ++ [c]).getD (A.length + B.length) 0 = c := by
    have hab : (A ++ B).length = A.length + B.length := List.length_append
    rw [← hab]; exact getD_concat (A ++ B) c
  have hgd : ∀ q, A.length ≤ q → q < A.length + B.length →
      ((A ++ B) ++ [c]).getD q 0 = B.getD (q - A.length) 0 := by
    intro q h1 h2
    rw [getD_append_lt (A ++ B) [c] q (by rw [List.length_append]; omega),
        getD_append_ge A B q h1]
  show (((List.range ((oneRow ((A ++ B) ++ [c])).length - 1)).filter
      (fun p => decide (BMS.ent (oneRow ((A ++ B) ++ [c])) p 0
        < BMS.ent (oneRow ((A ++ B) ++ [c])) ((oneRow ((A ++ B) ++ [c])).length - 1) 0))).max?)
      = some A.length
  simp only [ent_oneRow, hx, hc']
  rw [max?_filter_range]
  refine lastSome_spec _ (A.length + B.length) A.length (by omega) ?_ ?_
  · have h0 : ((A ++ B) ++ [c]).getD A.length 0 = b0 := by
      rw [hgd A.length (Nat.le_refl _) (by omega), Nat.sub_self, hB]; rfl
    rw [h0]
    exact decide_eq_true hb0
  · intro q h1 h2
    have hq : ((A ++ B) ++ [c]).getD q 0 = B'.getD (q - A.length - 1) 0 := by
      rw [hgd q (by omega) h2, hB]
      obtain ⟨j, hj⟩ : ∃ j, q - A.length = j + 1 := ⟨q - A.length - 1, by omega⟩
      rw [hj]
      show B'.getD j 0 = B'.getD (j + 1 - 1) 0
      simp
    rw [hq]
    refine decide_eq_false ?_
    have hmem : B'.getD (q - A.length - 1) 0 ∈ B' := getD_mem B' _ (by omega)
    have := hrest _ hmem
    omega

/-- **The BM4 expansion on the one-row region.**  If the last entry `c` is nonzero,
    the bad root is `|A|`, and the bad part is `B`, then the expansion lays down
    `n+1` copies of `B`. -/
theorem expand_oneRow {A B : List Nat} {c b0 : Nat} {B' : List Nat}
    (hB : B = b0 :: B') (hb0 : b0 < c) (hrest : ∀ x ∈ B', c ≤ x) (hc : c ≠ 0) (n : Nat) :
    BMS.expand? (oneRow ((A ++ B) ++ [c])) n = some (oneRow (A ++ repL B (n + 1))) := by
  have hBlen : B.length = B'.length + 1 := by rw [hB]; simp
  have hL : (oneRow ((A ++ B) ++ [c])).getLast? = some [c] := by
    rw [oneRow_append]
    exact List.getLast?_concat
  have hlnz : BMS.lnz [c] = some 0 := by
    cases c with
    | zero => exact absurd rfl hc
    | succ k => rfl
  have hpar := parent_oneRow (A := A) hB hb0 hrest
  have hlen : List.length (oneRow ((A ++ B) ++ [c])) - 1 - A.length = B.length := by
    rw [length_oneRow, List.length_append, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega
  have htake : List.take A.length (oneRow ((A ++ B) ++ [c])) = oneRow A := by
    rw [List.append_assoc, oneRow_append, ← length_oneRow A]
    exact List.take_left
  have hgd : ∀ x, x < B.length → ((A ++ B) ++ [c]).getD (A.length + x) 0 = B.getD x 0 := by
    intro x hx
    rw [getD_append_lt (A ++ B) [c] (A.length + x) (by rw [List.length_append]; omega),
        getD_append_ge A B (A.length + x) (by omega)]
    congr 1
    omega
  have hblk : List.map (fun x => List.map
        (fun y => BMS.ent (oneRow ((A ++ B) ++ [c])) (A.length + x) y)
        (List.range ([c] : List Nat).length)) (List.range B.length) = oneRow B := by
    have h1 : ∀ x ∈ List.range B.length,
        List.map (fun y => BMS.ent (oneRow ((A ++ B) ++ [c])) (A.length + x) y)
          (List.range ([c] : List Nat).length) = [B.getD x 0] := by
      intro x hx
      have hx' : x < B.length := List.mem_range.mp hx
      show [BMS.ent (oneRow ((A ++ B) ++ [c])) (A.length + x) 0] = [B.getD x 0]
      rw [ent_oneRow, hgd x hx']
    rw [List.map_congr_left h1]
    show (List.range B.length).map (fun x => [B.getD x 0]) = B.map (fun a => [a])
    calc (List.range B.length).map (fun x => [B.getD x 0])
        = ((List.range B.length).map (fun x => B.getD x 0)).map (fun a => [a]) := by
          rw [List.map_map]; rfl
      _ = (B.take B.length).map (fun a => [a]) := by rw [range_map_getD B.length B (Nat.le_refl _)]
      _ = B.map (fun a => [a]) := by rw [List.take_length]
  simp only [BMS.expand?, hL, Option.bind_eq_bind, Option.bind_some, hlnz, hpar, Option.pure_def,
    delta_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
  rw [hlen, htake, hblk, flat_range, ← oneRow_repL, ← oneRow_append]


/-! ## §9 The last block of a standard sequence -/

theorem getLast?_ne_nil {α : Type _} {l : List α} {z : α} (h : l.getLast? = some z) : l ≠ [] := by
  intro hc; rw [hc] at h; simp at h

theorem eq_concat_of_getLast? : ∀ (l : List Nat) (z : Nat), l.getLast? = some z →
    l = l.dropLast ++ [z]
  | [], _, h => by simp at h
  | [a], z, h => by
    have ha : a = z := by simpa using h
    subst ha; rfl
  | a :: b :: r, z, h => by
    have h' : (b :: r).getLast? = some z := h
    have ih := eq_concat_of_getLast? (b :: r) z h'
    show a :: b :: r = (a :: (b :: r).dropLast) ++ [z]
    rw [List.cons_append, ← ih]

theorem getLast?_append_right {α : Type _} (l l' : List α) (h : l' ≠ []) :
    (l ++ l').getLast? = l'.getLast? := by
  rw [List.getLast?_append]
  cases hl : l'.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hl) h
  | some _ => rfl

theorem head_flatten : ∀ (bs : List (List Nat)), (∀ b ∈ bs, IsBlock b) →
    bs.flatten = [] ∨ bs.flatten.head? = some 0
  | [], _ => Or.inl rfl
  | c :: _, h => by
    right
    have hc : IsBlock c := h c (by simp)
    cases c with
    | nil => exact absurd hc.hd (by simp)
    | cons a _ =>
      have ha : a = 0 := by simpa using hc.hd
      subst ha; rfl

/-- Split a nonempty standard sequence into everything but its last block, and that block. -/
theorem lastBlock_split {t : List Nat} (hstd : stdSeq t = true) (ht : t ≠ []) :
    ∃ G b, t = G ++ b ∧ IsBlock b ∧ (G = [] ∨ G.head? = some 0)
      ∧ blocks0 t = blocks0 G ++ [b] ∧ stdSeq (dec b) = true ∧ b.length ≤ t.length := by
  have hbs : blocks0 t ≠ [] := fun hc => ht ((blocks0_eq_nil_iff t).mp hc)
  obtain ⟨bsl, b, hsp⟩ : ∃ bsl b, blocks0 t = bsl ++ [b] := by
    cases hb : blocks0 t with
    | nil => exact absurd hb hbs
    | cons x l =>
      exact ⟨(x :: l).dropLast, (x :: l).getLast (by simp),
        (List.dropLast_concat_getLast (by simp)).symm⟩
  have hIsB : ∀ x ∈ blocks0 t, IsBlock x := stdSeq_isBlock hstd
  have hbmem : b ∈ blocks0 t := by rw [hsp]; simp
  have hGb : ∀ x ∈ bsl, IsBlock x := fun x hx => hIsB x (by rw [hsp]; simp [hx])
  have hG : blocks0 bsl.flatten = bsl := blocks0_flat _ hGb
  have htG : t = bsl.flatten ++ b := by
    have h1 : (blocks0 t).flatten = t := blocks0_flatten t
    rw [hsp, List.flatten_append] at h1
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at h1
    exact h1.symm
  exact ⟨bsl.flatten, b, htG, hIsB b hbmem, head_flatten _ hGb, by rw [hG]; exact hsp,
    stdSeq_blocks hstd b hbmem, blocks0_length_le hbmem⟩

theorem blocks0_dropLast_zero {t : List Nat} (ht : t.getLast? = some 0) :
    blocks0 t = blocks0 t.dropLast ++ [[0]] := by
  have h := eq_concat_of_getLast? t 0 ht
  have h2 : blocks0 (t.dropLast ++ [0]) = blocks0 t.dropLast ++ [[0]] := by
    rw [blocks0_append t.dropLast [0] (Or.inr rfl), blocks0_cons_nil]
  rw [← h] at h2
  exact h2

/-- A standard sequence ending in 0 is a successor, and its predecessor drops that 0. -/
theorem oV_succ {t : List Nat} (hstd : stdSeq t = true) (ht : t.getLast? = some 0) :
    kindT (oV t) = .isSucc ∧ predT (oV t) = oV t.dropLast := by
  have htne : t ≠ [] := getLast?_ne_nil ht
  have hbv : blockVals t = blockVals t.dropLast ++ [one] := by
    show (blocks0 t).map _ = _
    rw [blocks0_dropLast_zero ht, List.map_append]
    show blockVals t.dropLast ++ [omegaNF (oV (dec [0]))] = blockVals t.dropLast ++ [one]
    rw [blockVal_eq, show dec [0] = ([] : List Nat) from rfl, oV_nil]
    rfl
  have htl : toList (oV t) = blockVals t := toList_oV hstd
  have hlast : (toList (oV t)).getLast? = some one := by
    rw [htl, hbv]; exact List.getLast?_concat
  have hne : oV t ≠ zero := oV_ne_zero htne
  refine ⟨by rw [kindT_ne_zero hne]; simp [hlast], ?_⟩
  rw [predT_eq (by rw [hlast]; simp), htl, hbv, List.dropLast_concat, oV_eq' t.dropLast]
  refine (foldr_plus_eq_ofList _ (blockVals_isAP _) ?_).symm
  have hd := stdSeq_desc hstd
  rw [hbv] at hd
  have hd2 := descB_dropLast _ hd
  rwa [List.dropLast_concat] at hd2

/-- A standard sequence ending in a nonzero entry is a limit. -/
theorem oV_lim {t : List Nat} (hstd : stdSeq t = true) {d : Nat} (hd : d ≠ 0)
    (ht : t.getLast? = some d) : kindT (oV t) = .isLim := by
  have htne : t ≠ [] := getLast?_ne_nil ht
  obtain ⟨G, b, htG, hb, _, hbl, _, _⟩ := lastBlock_split hstd htne
  obtain ⟨v, hbv⟩ : ∃ v, b = 0 :: v := by
    cases b with
    | nil => exact absurd hb.hd (by simp)
    | cons a t' =>
      have ha : a = 0 := by simpa using hb.hd
      exact ⟨t', by rw [ha]⟩
  have hbne : b ≠ [] := by rw [hbv]; simp
  have hbLast : b.getLast? = some d := by
    rw [htG] at ht; rwa [getLast?_append_right G b hbne] at ht
  have hvne : v ≠ [] := by
    intro hc
    rw [hbv, hc] at hbLast
    have : d = 0 := by simpa using hbLast.symm
    exact hd this
  have hdecne : dec b ≠ [] := by
    rw [hbv]
    intro hc
    exact hvne (by simpa [dec] using hc)
  have hbvals : blockVals t = blockVals G ++ [phi zero (oV (dec b))] := by
    show (blocks0 t).map _ = _
    rw [hbl, List.map_append]
    show blockVals G ++ [omegaNF (oV (dec b))] = _
    rw [blockVal_eq]
  have hlast : (toList (oV t)).getLast? = some (phi zero (oV (dec b))) := by
    rw [toList_oV hstd, hbvals]; exact List.getLast?_concat
  have hne1 : phi zero (oV (dec b)) ≠ one := by
    intro hc
    have hc' : phi zero (oV (dec b)) = phi zero zero := hc
    injection hc' with _ h2
    exact oV_ne_zero hdecne h2
  rw [kindT_ne_zero (oV_ne_zero htne)]
  simp [hlast, hne1]


/-! ## §10 The core induction

For a standard one-row sequence `u` ending in `c ≠ 0` we produce the split
`u = A ++ B ++ [c]` at the bad root together with the identity

    oV (A ++ B^(n+1)) = (oV u)[n+1] .
-/

theorem core : ∀ (f : Nat) (u : List Nat), u.length ≤ f → stdSeq u = true →
    ∀ (c : Nat), c ≠ 0 → u.getLast? = some c →
    ∃ A B b0 B', B = b0 :: B' ∧ u = (A ++ B) ++ [c] ∧ b0 < c ∧ (∀ x ∈ B', c ≤ x) ∧
      ∀ n, oV (A ++ repL B (n + 1)) = fsN (oV u) (n + 1)
  | 0, u, hf, _, _, _, hlast => by
    have hu : u = [] := by cases u with | nil => rfl | cons a t => simp at hf
    subst hu; simp at hlast
  | f + 1, u, hf, hstd, c, hc, hlast => by
    have hune : u ≠ [] := getLast?_ne_nil hlast
    obtain ⟨G, b, huG, hb, hGh, hbl, hstdb, hblen⟩ := lastBlock_split hstd hune
    obtain ⟨w, hw⟩ : ∃ w, dec b = w := ⟨dec b, rfl⟩
    rw [hw] at hstdb
    obtain ⟨v, hbv⟩ : ∃ v, b = 0 :: v := by
      cases b with
      | nil => exact absurd hb.hd (by simp)
      | cons a t' =>
        have ha : a = 0 := by simpa using hb.hd
        exact ⟨t', by rw [ha]⟩
    have hbne : b ≠ [] := by rw [hbv]; simp
    have hbLast : b.getLast? = some c := by
      rw [huG] at hlast; rwa [getLast?_append_right G b hbne] at hlast
    have hvnz : ∀ x ∈ v, x ≠ 0 := fun x hx => hb.tl x (by rw [hbv]; simpa using hx)
    have hvne : v ≠ [] := by
      intro hcc
      rw [hbv, hcc] at hbLast
      exact hc (by simpa using hbLast.symm)
    have hvLast : v.getLast? = some c := by
      rw [hbv] at hbLast
      rwa [show (0 :: v) = [0] ++ v from rfl, getLast?_append_right [0] v hvne] at hbLast
    have hdecb : w = v.map (· - 1) := by rw [← hw, hbv]; rfl
    have hvw : w.map (· + 1) = v := by
      rw [hdecb, List.map_map]
      have hcg : ∀ x ∈ v, ((· + 1) ∘ (· - 1)) x = id x := by
        intro x hx
        have hx0 := hvnz x hx
        show (x - 1) + 1 = x
        omega
      rw [List.map_congr_left hcg, List.map_id]
    have hwLast : w.getLast? = some (c - 1) := by
      rw [hdecb, List.getLast?_map, hvLast]; rfl
    have hwlen : w.length ≤ f := by rw [← hw, dec_length]; omega
    have hbvals : blockVals u = blockVals G ++ [phi zero (oV w)] := by
      show (blocks0 u).map _ = _
      rw [hbl, List.map_append]
      show blockVals G ++ [omegaNF (oV (dec b))] = _
      rw [blockVal_eq, hw]
    have hfs : ∀ n : Nat, fsN (oV u) (n + 1)
        = (blockVals G).foldr plus (fsN (phi zero (oV w)) (n + 1)) := by
      intro n
      rw [oV_ofList hstd, hbvals, fsN_ofList_append]
    have hoV : ∀ (X : List Nat), (X = [] ∨ X.head? = some 0) →
        oV (G ++ X) = (blockVals G).foldr plus ((blockVals X).foldr plus zero) := by
      intro X hX
      rw [oV_eq' (G ++ X), blockVals_append G X hX, List.foldr_append]
    rcases Nat.lt_or_ge c 2 with hc2 | hc2
    · -- successor-shaped exponent: c = 1, so `w` ends in 0
      have hc1 : c = 1 := by omega
      subst hc1
      have hw0 : w.getLast? = some 0 := by simpa using hwLast
      obtain ⟨hkind, hpred⟩ := oV_succ hstdb hw0
      have hwcat : w = w.dropLast ++ [0] := eq_concat_of_getLast? w 0 hw0
      have hvcat : v = (w.dropLast).map (· + 1) ++ [1] := by
        have h1 : (w.dropLast ++ [0]).map (· + 1) = (w.dropLast).map (· + 1) ++ [1] := by
          rw [List.map_append]; rfl
        rw [← hwcat] at h1
        rw [← hvw]; exact h1
      refine ⟨G, mkBlock w.dropLast, 0, (w.dropLast).map (· + 1), rfl, ?_, by omega, ?_, ?_⟩
      · rw [huG, hbv, hvcat]
        show G ++ (0 :: ((w.dropLast).map (· + 1) ++ [1])) = (G ++ mkBlock w.dropLast) ++ [1]
        simp [mkBlock, List.append_assoc]
      · intro x hx
        obtain ⟨y, _, hy⟩ := List.mem_map.mp hx
        omega
      · intro n
        have hbvrep : blockVals (repL (mkBlock w.dropLast) (n + 1))
            = List.replicate (n + 1) (phi zero (oV w.dropLast)) := by
          show (blocks0 (repL (mkBlock w.dropLast) (n + 1))).map _ = _
          rw [blocks0_repL (isBlock_mkBlock _), List.map_replicate]
          show List.replicate (n + 1) (omegaNF (oV (dec (mkBlock w.dropLast)))) = _
          rw [dec_mkBlock, omegaNF_of_compPhi0 (compPhi0_oV w.dropLast)]
        have hkey : (blockVals (repL (mkBlock w.dropLast) (n + 1))).foldr plus zero
            = fsN (phi zero (oV w)) (n + 1) := by
          rw [hbvrep, foldr_plus_replicate (y := phi zero (oV w.dropLast)) rfl,
            fsN_phi0_succ (compPhi0_oV w) hkind, hpred,
            omegaNF_of_compPhi0 (compPhi0_oV w.dropLast)]
        rw [hoV _ (head?_repL (isBlock_mkBlock _).hd (n + 1)), hfs n, hkey]
    · -- limit-shaped exponent: c ≥ 2, so `w` ends in c-1 ≠ 0
      have hc1 : c - 1 ≠ 0 := by omega
      have hlim : kindT (oV w) = .isLim := oV_lim hstdb hc1 hwLast
      obtain ⟨Aw, Bw, b0w, B'w, hBw, hwsplit, hb0w, hrestw, heqw⟩ :=
        core f w hwlen hstdb (c - 1) hc1 hwLast
      refine ⟨G ++ mkBlock Aw, Bw.map (· + 1), b0w + 1, B'w.map (· + 1), by rw [hBw]; rfl,
        ?_, by omega, ?_, ?_⟩
      · have h1 : ((Aw ++ Bw) ++ [c - 1]).map (· + 1)
            = (Aw.map (· + 1) ++ Bw.map (· + 1)) ++ [c] := by
          rw [List.map_append, List.map_append]
          congr 1
          show [(c - 1) + 1] = [c]
          congr 1
          omega
        rw [← hwsplit] at h1
        rw [huG, hbv, ← hvw, h1]
        show G ++ (0 :: ((Aw.map (· + 1) ++ Bw.map (· + 1)) ++ [c]))
            = ((G ++ mkBlock Aw) ++ Bw.map (· + 1)) ++ [c]
        simp [mkBlock, List.append_assoc]
      · intro x hx
        obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hx
        have := hrestw y hy
        omega
      · intro n
        have hE : ((G ++ mkBlock Aw) ++ repL (Bw.map (· + 1)) (n + 1))
            = G ++ mkBlock (Aw ++ repL Bw (n + 1)) := by
          rw [← repL_map]
          show ((G ++ (0 :: Aw.map (· + 1))) ++ (repL Bw (n + 1)).map (· + 1))
              = G ++ (0 :: (Aw ++ repL Bw (n + 1)).map (· + 1))
          rw [List.map_append]
          simp [List.append_assoc]
        have hbvE : blockVals (mkBlock (Aw ++ repL Bw (n + 1)))
            = [phi zero (oV (Aw ++ repL Bw (n + 1)))] := by
          show (blocks0 (mkBlock (Aw ++ repL Bw (n + 1)))).map _ = _
          rw [blocks0_of_isBlock (isBlock_mkBlock _)]
          show [omegaNF (oV (dec (mkBlock (Aw ++ repL Bw (n + 1)))))] = _
          rw [dec_mkBlock, omegaNF_of_compPhi0 (compPhi0_oV _)]
        have hkey : (blockVals (mkBlock (Aw ++ repL Bw (n + 1)))).foldr plus zero
            = fsN (phi zero (oV w)) (n + 1) := by
          rw [hbvE, fsN_phi0_lim (compPhi0_oV w) hlim, ← heqw n,
            phiNF_zero_of_compPhi0 (compPhi0_oV _)]
          exact plus_zero _
        rw [hE, hoV _ (Or.inr rfl), hfs n, hkey]


/-! ## §11 E3 and the successor rule, in general, on the one-row region -/

/-- **E3, general form (limit case).**  For every standard one-row sequence `s`
    whose last entry is nonzero (a limit), the BM4 expansion of the height-1 matrix
    with row 0 = `s` translates to the fundamental sequence of its term, for every
    copy count `n` (index shift by one, as in `Trans/TM.lean`). -/
theorem e3_general {s : List Nat} (hstd : stdSeq s = true) {c : Nat} (hc : c ≠ 0)
    (hlast : s.getLast? = some c) (n : Nat) :
    o? (BMS.expand (oneRow s) n) = some (fsN (oPr (oneRow s)) (n + 1)) := by
  obtain ⟨A, B, b0, B', hBeq, hs, hb0, hrest, heq⟩ :=
    core s.length s (Nat.le_refl _) hstd c hc hlast
  have hexp : BMS.expand? (oneRow s) n = some (oneRow (A ++ repL B (n + 1))) := by
    rw [hs]; exact expand_oneRow hBeq hb0 hrest hc n
  have hE : BMS.expand (oneRow s) n = oneRow (A ++ repL B (n + 1)) := by
    show (BMS.expand? (oneRow s) n).getD [] = _
    rw [hexp]; rfl
  rw [hE, o?_oneRow, heq n, oPr_eq, row0_oneRow]

/-- **The successor counterpart.**  If the last column is 0 the expansion drops it,
    and the translation lands on the predecessor of the term. -/
theorem esucc_general {s : List Nat} (hstd : stdSeq s = true) (hlast : s.getLast? = some 0)
    (n : Nat) : o? (BMS.expand (oneRow s) n) = some (predT (oPr (oneRow s))) := by
  have hcat : s = s.dropLast ++ [0] := eq_concat_of_getLast? s 0 hlast
  have hL : (oneRow s).getLast? = some [0] := by
    rw [hcat, oneRow_append]
    exact List.getLast?_concat
  have hlnz : BMS.lnz ([0] : List Nat) = none := rfl
  have hexp : BMS.expand? (oneRow s) n = some ((oneRow s).dropLast) := by
    simp only [BMS.expand?, hL, Option.bind_eq_bind, Option.bind_some, hlnz, Option.pure_def]
  have hdl : (oneRow s).dropLast = oneRow s.dropLast := by
    have h1 : (oneRow (s.dropLast ++ [0])).dropLast = oneRow s.dropLast := by
      rw [oneRow_append]
      show (oneRow s.dropLast ++ [[0]]).dropLast = oneRow s.dropLast
      rw [List.dropLast_concat]
    rw [← hcat] at h1
    exact h1
  have hE : BMS.expand (oneRow s) n = oneRow s.dropLast := by
    show (BMS.expand? (oneRow s) n).getD [] = _
    rw [hexp, hdl]; rfl
  obtain ⟨_, hpred⟩ := oV_succ hstd hlast
  rw [hE, o?_oneRow, oPr_eq, row0_oneRow, hpred]

/-- The same statements for a height-1 matrix given as a matrix. -/
theorem e3_matrix {X : Matrix} (h1 : X = oneRow (row0 X)) (hstd : stdSeq (row0 X) = true)
    {c : Nat} (hc : c ≠ 0) (hlast : (row0 X).getLast? = some c) (n : Nat) :
    o? (BMS.expand X n) = some (fsN (oPr X) (n + 1)) := by
  have h := e3_general (s := row0 X) hstd hc hlast n
  rw [← h1] at h
  exact h

theorem esucc_matrix {X : Matrix} (h1 : X = oneRow (row0 X)) (hstd : stdSeq (row0 X) = true)
    (hlast : (row0 X).getLast? = some 0) (n : Nat) :
    o? (BMS.expand X n) = some (predT (oPr X)) := by
  have h := esucc_general (s := row0 X) hstd hlast n
  rw [← h1] at h
  exact h

/-! ## §12 Sanity checks

`stdSeq` accepts the standard rows of the table and rejects `(0)(0)(1)`, for which
E3 genuinely fails — this is why a standardness hypothesis is unavoidable. -/

#guard stdSeq [0] = true
#guard stdSeq [0, 1] = true
#guard stdSeq [0, 1, 1] = true
#guard stdSeq [0, 1, 0, 1] = true
#guard stdSeq [0, 1, 2] = true
#guard stdSeq [0, 1, 2, 3] = true
#guard stdSeq [0, 1, 2, 2] = true
#guard stdSeq [0, 1, 2, 1, 2] = true
#guard stdSeq [0, 0, 1] = false          -- 1 + ω is not a normal form
#guard stdSeq [0, 1, 0, 1, 1] = false    -- ω + ω² is not a normal form
#guard stdSeq [1] = false                -- does not start with 0

-- E3 fails for the non-standard `(0)(0)(1)`: the expansion gives k+2, the fs gives k+1.
#guard o? (BMS.expand (oneRow [0, 0, 1]) 2) != some (fsN (oPr (oneRow [0, 0, 1])) 3)

/-- E3 for the row `(0)(1)(2)`, obtained from the general theorem. -/
example (n : Nat) :
    o? (BMS.expand ([[0], [1], [2]] : Matrix) n)
      = some (fsN (oPr ([[0], [1], [2]] : Matrix)) (n + 1)) :=
  e3_matrix (X := [[0], [1], [2]]) rfl (by decide) (c := 2) (by decide) rfl n

/-- E3 for the row `(0)(1)(1)`, obtained from the general theorem. -/
example (n : Nat) :
    o? (BMS.expand ([[0], [1], [1]] : Matrix) n)
      = some (fsN (oPr ([[0], [1], [1]] : Matrix)) (n + 1)) :=
  e3_matrix (X := [[0], [1], [1]]) rfl (by decide) (c := 1) (by decide) rfl n

/-- A row not covered by `Rows/Proofs.lean`: `(0)(1)(2)(1)(2)` (= ω^(ω·2)). -/
example (n : Nat) :
    o? (BMS.expand ([[0], [1], [2], [1], [2]] : Matrix) n)
      = some (fsN (oPr ([[0], [1], [2], [1], [2]] : Matrix)) (n + 1)) :=
  e3_matrix (X := [[0], [1], [2], [1], [2]]) rfl (by decide) (c := 2) (by decide) rfl n

/-- The successor rule for `(0)(1)(0)`. -/
example (n : Nat) :
    o? (BMS.expand ([[0], [1], [0]] : Matrix) n)
      = some (predT (oPr ([[0], [1], [0]] : Matrix))) :=
  esucc_matrix (X := [[0], [1], [0]]) rfl (by decide) rfl n


end Evidence.StageA
