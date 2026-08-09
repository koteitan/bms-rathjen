import TM.NF
/-
Evidence/WF.lean — the well-foundedness stage (self-contained, no mathlib)

(The import is on the first line: the kimina server used to verify this file
mis-splits a snippet whose `import` is preceded by a comment.)

IMPORT DIRECTION (changed 2026-08-09, certificate lane).  This file used to
`import Evidence.Cert`, which it never used: §1–§4 speak only of `List Nat`, and
§5 only of `TM.Term`.  It now imports `TM.NF` instead, so that `Evidence/Cert.lean`
can import THIS file and use §5's `ltF_mono` — which is what Cert.lean's order
proofs need and currently work around.  Nothing imports `Evidence.WF`, so the
flip is safe; adding the one line `import Evidence.WF` to Cert.lean is left to a
lane that can run `lake build`, because until the oleans are rebuilt a snippet
that imports `Evidence.WF` still drags in the stale `Evidence.Cert` and every
declaration clashes.  That is a build-order artefact, not a proof gap.

WHAT THIS FILE IS FOR.  `Evidence/Cert.lean` builds certificate families by
recursion along the BM4 expansion.  Below ω² the recursion index is the pair
`(m, k)` of `cert_wm` and Lean's own `Prod.Lex` discharges termination.  One
level up the index is a VECTOR of counts, and Lean has no built-in order for
that, so the recursion needs a well-foundedness theorem of its own.  That is
what this file provides, in the form the certificate recursion actually
consumes.

THE ORDER.  A term of the CNF segment below ω^(k+1) is

    ω^k·c_k + ω^(k-1)·c_(k-1) + … + ω^0·c_0 ,

i.e. the vector `[c_k, …, c_0]`.  The BM4 expansion of such a term acts on the
lowest nonzero level j:

    j = 0 : successor, c_0 ↦ c_0 - 1
    j > 0 : limit,     c_j ↦ c_j - 1  and  c_(j-1) ↦ n+1   (the copy count)

Both steps leave the levels above j untouched and strictly decrease the entry at
level j, so both are instances of ONE lemma, `lexLt_at`: agree on a prefix, drop
at the next entry.  This is the Hydra/multiset ordering in the form that a fixed
level bound makes elementary — the bound is legitimate because no expansion step
ever raises the top level.

WHY THE LENGTH CONDITION IS IN THE `head` CONSTRUCTOR.  Lexicographic comparison
of arbitrary-length lists is NOT well-founded:

    [1] > [0,1] > [0,0,1] > [0,0,0,1] > …

is an infinite descent (each step compares 0 < 1 at the head, or equal heads and
recurses).  Requiring the two tails to have the same length in the `head`
constructor makes `LexLt` length-preserving, and then it is well-founded on ALL
of `List Nat` — no side condition at the use site.  `lexLt_wf` below.

SCOPE, HONESTLY (see also the design note at the end of Evidence/Cert.lean).

  * This is exactly what the certificate recursion for the region below ω^ω
    needs: the expansion steps are concrete, so `lexLt_at` + `lexLt_wf` supply
    the termination argument directly.  No statement about the T(M) order `lt`
    is required for that.
  * It is NOT the same thing as well-foundedness of `lt` itself on the inT terms
    below a bound.  That stronger statement is what the conditional main theorem
    MT wants, and it additionally needs the analytic direction of the order
    (inversion lemmas) plus transitivity of `lt`.  Both are now available ON THE
    φ̄-FRAGMENT — §7 proves transitivity (`lt_trans`) and the inversions
    (`le_of_not_lt`, `lt_of_not_le`, from comparability) — and, since §8.2, on the
    larger fragment `Frag2` = `Frag` ∪ {`M`, `ω̄^·`} as well (`lt_trans2`,
    `le_of_not_lt2`, `lt_of_not_le2`), still with no `inT` hypothesis.  Above THAT,
    i.e. once `ψ`/`Z` appear, they are still open; see §8 (Stage 3b).
  * The method here does NOT scale to ε₀: below ε₀ the exponents are themselves
    unbounded terms, so no fixed level bound exists and there is no vector to
    put a lexicographic order on.  ε₀ needs the classical structural argument
    (`Acc a → Acc b → Acc (ω^a + b)`), which is where transitivity becomes
    unavoidable.

    That remains true of the certificate RECURSION for ε₀.  It is NOT true of the
    cofinality clause: §9 (added by the certificate lane) proves that the ω-towers
    are cofinal in ε₀ among the terms of 𝔗(M) by one structural induction, with no
    well-foundedness, no transitivity and no `Frag` — only clause-by-clause
    analysis of 2.3 against a tower.  Comparing an arbitrary term with a TOWER is
    much cheaper than comparing two arbitrary terms, and that asymmetry is what
    §9 exploits.
-/

namespace Evidence.WF

/-! ## §1 The lexicographic order on count vectors -/

/-- Lexicographic order on `List Nat`, compared from the left.  The `head` case
    requires equal tail lengths, which makes the relation length-preserving —
    without that condition it is not well-founded (see the header). -/
inductive LexLt : List Nat → List Nat → Prop
  | head {a b : Nat} {l l' : List Nat} (hab : a < b) (hlen : l.length = l'.length) :
      LexLt (a :: l) (b :: l')
  | tail {a : Nat} {l l' : List Nat} (h : LexLt l l') : LexLt (a :: l) (a :: l')

theorem lexLt_length : ∀ {l l' : List Nat}, LexLt l l' → l.length = l'.length
  | _, _, .head _ h => by simp [h]
  | _, _, .tail h => by simp [lexLt_length h]

theorem not_lexLt_nil {l : List Nat} : ¬ LexLt l [] := by intro h; cases h

/-! ## §2 Well-foundedness

The standard proof: induction on the length; inside, induction on the head entry
(ordinary `Nat` recursion, strengthened to "for every `b ≤ a`"); inside that,
induction on the accessibility of the tail. -/

/-- One head entry, given that everything with a smaller head is accessible. -/
private theorem acc_cons_of (n b : Nat)
    (hlow : ∀ c, c < b → ∀ t', t'.length = n → Acc LexLt (c :: t')) :
    ∀ (t : List Nat), Acc LexLt t → t.length = n → Acc LexLt (b :: t) := by
  intro t hacc
  induction hacc with
  | intro u _ ih =>
    intro hlen
    refine Acc.intro _ (fun y hy => ?_)
    cases hy with
    | @head c d l l' hcd hll => exact hlow c hcd l (by rw [hll]; exact hlen)
    | @tail _ l _ h => exact ih l h (by rw [lexLt_length h]; exact hlen)

private theorem acc_cons_aux (n : Nat) (hn : ∀ l : List Nat, l.length = n → Acc LexLt l) :
    ∀ (a b : Nat), b ≤ a → ∀ (t : List Nat), t.length = n → Acc LexLt (b :: t)
  | 0, b, hb, t, ht => by
    have hb0 : b = 0 := by omega
    subst hb0
    exact acc_cons_of n 0 (fun c hc => absurd hc (by omega)) t (hn t ht) ht
  | a + 1, b, hb, t, ht => by
    rcases Nat.lt_or_ge b (a + 1) with h | h
    · exact acc_cons_aux n hn a b (by omega) t ht
    · have hb1 : b = a + 1 := by omega
      subst hb1
      refine acc_cons_of n (a+1)
        (fun c hc t' ht' => acc_cons_aux n hn a c (by omega) t' ht') t (hn t ht) ht

private theorem acc_lexLt : ∀ (n : Nat) (l : List Nat), l.length = n → Acc LexLt l
  | 0, l, hl => by
    cases l with
    | nil => exact Acc.intro [] (fun y hy => absurd hy not_lexLt_nil)
    | cons a t => simp at hl
  | n + 1, l, hl => by
    cases l with
    | nil => simp at hl
    | cons a t =>
      have ht : t.length = n := by simp only [List.length_cons] at hl; omega
      exact acc_cons_aux n (fun l' hl' => acc_lexLt n l' hl') a a (Nat.le_refl a) t ht

/-- **The order on count vectors is well-founded.**  No side condition: `LexLt`
    is length-preserving, so every list is accessible at its own length. -/
theorem lexLt_wf : WellFounded LexLt := ⟨fun l => acc_lexLt l.length l rfl⟩

/-- Deliberately `scoped`: a global `WellFoundedRelation (List Nat)` would change
    how Lean discharges termination for every list recursion in every file that
    imports this one.  Write `open Evidence.WF` in the client. -/
scoped instance : WellFoundedRelation (List Nat) := ⟨LexLt, lexLt_wf⟩

/-! ## §3 The step lemma the expansion uses

Both BM4 steps on a count vector — "successor: drop one unit" and "limit: drop
one ω^j and put `n+1` copies of ω^(j-1) below it" — keep the levels above `j`
and strictly decrease the entry at level `j`.  That is exactly `lexLt_at`. -/

/-- Agree on a prefix, drop at the next entry: the left vector is smaller. -/
theorem lexLt_at : ∀ (p : List Nat) {a b : Nat} {l l' : List Nat}, a < b →
    l.length = l'.length → LexLt (p ++ a :: l) (p ++ b :: l')
  | [], _, _, _, _, hab, hlen => .head hab hlen
  | _ :: p, _, _, _, _, hab, hlen => .tail (lexLt_at p hab hlen)

/-- The successor step: `… + c+1` ↦ `… + c` at the bottom level. -/
theorem lexLt_succ_step (p : List Nat) (c : Nat) : LexLt (p ++ [c]) (p ++ [c + 1]) :=
  lexLt_at p (by omega) rfl

/-- The limit step at level `j > 0`: one `ω^j` is replaced by `n+1` copies of
    `ω^(j-1)`, and everything below is cleared.  `r` is the (fixed-length) block
    of levels strictly below `j-1`. -/
theorem lexLt_lim_step (p : List Nat) (c cj n : Nat) (r r' : List Nat)
    (hlen : r.length = r'.length) :
    LexLt (p ++ c :: (n + 1) :: r) (p ++ (c + 1) :: cj :: r') :=
  lexLt_at p (by omega) (by simp [hlen])

/-! ## §4 Sanity checks -/

example : LexLt [0, 5] [1, 0] := .head (by omega) rfl
example : LexLt [1, 0, 7] [1, 1, 0] := .tail (.head (by omega) rfl)
example : ¬ LexLt [1, 0] [1, 0] := by
  intro h
  cases h with
  | head hab _ => omega
  | tail h =>
    cases h with
    | head hab _ => omega
    | tail h => cases h

-- ω²·2 + ω·0 + 3  ↦  ω²·2 + ω·0 + 2   (successor step at the bottom level)
example : LexLt ([2, 0] ++ [2]) ([2, 0] ++ [3]) := lexLt_succ_step [2, 0] 2
-- ω²·3  ↦  ω²·2 + ω·(n+1)              (limit step one level down)
example (n : Nat) : LexLt ([] ++ 2 :: (n + 1) :: [0]) ([] ++ 3 :: 0 :: [0]) :=
  lexLt_lim_step [] 2 0 n [0] [0] rfl


open TM (Term)
open TM.Term

/-! ## §5 Fuel-independence of the decision procedure  (D2, step 1)

`lt s t` is `ltF (fuelOf s t) s t`, and NOTHING in this repository says that the
answer does not change when the fuel changes.  That gap is why every order proof
in `Evidence/Cert.lean` has to be phrased as "for all sufficiently large fuel"
and why an order HYPOTHESIS can never be re-used at the fuel a goal happens to
want (see the note at the head of Cert.lean §5.7).

`ltF_stable` closes the gap: above the degree bound the answer is fixed.  It is
the prerequisite for transitivity of `lt` — a same-fuel transitivity statement
can be proved without it, but converting that into the user-facing
`lt a b → lt b c → lt a c` compares three DIFFERENT default fuels, which is
exactly what stability licenses.

The proof is one induction on a degree bound, and the only thing that makes it
work is that every recursive call of `ltF`/`starF` strictly decreases the sum of
the degrees of its arguments — including the calls through `starF`, because
`starF` returns a subterm (`deg_starF`). -/

theorem deg_pos : ∀ (t : Term), 1 ≤ t.deg
  | zero => by show (1 : Nat) ≤ 1; omega
  | M => by show (1 : Nat) ≤ 1; omega
  | add a b => by show 1 ≤ 1 + a.deg + b.deg; omega
  | omg a => by show 1 ≤ 1 + a.deg; omega
  | phi a b => by show 1 ≤ 1 + a.deg + b.deg; omega
  | psi a b => by show 1 ≤ 1 + a.deg + b.deg; omega
  | Z a => by show 1 ≤ 1 + a.deg; omega

/-- `α*` is a subterm of `α` (or `0`), so it never raises the degree.  This is
    what keeps the `ψ`/`Z` clauses of `ltF` inside the induction. -/
theorem deg_starF : ∀ (f : Nat) (t : Term), (starF f t).deg ≤ t.deg
  | 0, t => by show (1 : Nat) ≤ t.deg; exact deg_pos t
  | f + 1, t => by
    cases t with
    | zero => show (1 : Nat) ≤ 1; omega
    | M => show (1 : Nat) ≤ 1; omega
    | add a b =>
      show (if ltF f (starF f a) (starF f b) then starF f b else starF f a).deg ≤ 1 + a.deg + b.deg
      have h1 := deg_starF f a
      have h2 := deg_starF f b
      cases ltF f (starF f a) (starF f b) <;> simp <;> omega
    | omg a =>
      have := deg_starF f a
      show (starF f a).deg ≤ 1 + a.deg
      omega
    | phi a b =>
      show (if ltF f (starF f a) (starF f b) then starF f b else starF f a).deg ≤ 1 + a.deg + b.deg
      have h1 := deg_starF f a
      have h2 := deg_starF f b
      cases ltF f (starF f a) (starF f b) <;> simp <;> omega
    | psi k a => show 1 + k.deg + a.deg ≤ 1 + k.deg + a.deg; omega
    | Z a => show 1 + a.deg ≤ 1 + a.deg; omega

/-- **Fuel-independence.**  Above the degree bound, `ltF` and `starF` no longer
    depend on the fuel.  Proved together because the two are mutually
    recursive. -/
private theorem stable_aux : ∀ (n : Nat),
    (∀ (s t : Term), s.deg + t.deg ≤ n → ∀ f g, n ≤ f → n ≤ g → ltF f s t = ltF g s t) ∧
    (∀ (t : Term), t.deg ≤ n → ∀ f g, n ≤ f → n ≤ g → starF f t = starF g t)
  | 0 => ⟨by
      intro s t h
      have := deg_pos s
      have := deg_pos t
      omega, by
      intro t h
      have := deg_pos t
      omega⟩
  | n + 1 => by
    obtain ⟨IHl, IHs⟩ := stable_aux n
    constructor
    · intro s t hst f g hf hg
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      have hf' : n ≤ f' := by omega
      have hg' : n ≤ g' := by omega
      have R : ∀ (x y : Term), x.deg + y.deg ≤ n → ltF f' x y = ltF g' x y :=
        fun x y h => IHl x y h f' g' hf' hg'
      have RS : ∀ (x : Term), x.deg ≤ n → starF f' x = starF g' x :=
        fun x h => IHs x h f' g' hf' hg'
      cases s with
      | zero => cases t <;> rfl
      | M =>
        cases t <;> try rfl
        rename_i c d
        simp only [Term.deg] at hst
        show ((M : Term) == c || ltF f' M c) = ((M : Term) == c || ltF g' M c)
        rw [R M c (by show 1 + c.deg ≤ n; omega)]
      | add a b =>
        simp only [Term.deg] at hst
        cases t with
        | zero => rfl
        | M =>
          simp only [Term.deg] at hst
          show ltF f' a M = ltF g' a M
          rw [R a M (by show a.deg + 1 ≤ n; omega)]
        | add c d =>
          show (if (add a b == add c d) = true then false
                else if (a == c) = true then ltF f' b d else ltF f' a c)
              = (if (add a b == add c d) = true then false
                 else if (a == c) = true then ltF g' b d else ltF g' a c)
          simp only [Term.deg] at hst
          rw [R b d (by omega), R a c (by omega)]
        | omg x =>
          simp only [Term.deg] at hst
          show ltF f' a (omg x) = ltF g' a (omg x)
          rw [R a (omg x) (by show a.deg + (1 + x.deg) ≤ n; omega)]
        | phi c d =>
          simp only [Term.deg] at hst
          show ltF f' a (phi c d) = ltF g' a (phi c d)
          rw [R a (phi c d) (by show a.deg + (1 + c.deg + d.deg) ≤ n; omega)]
        | psi k c =>
          simp only [Term.deg] at hst
          show ltF f' a (psi k c) = ltF g' a (psi k c)
          rw [R a (psi k c) (by show a.deg + (1 + k.deg + c.deg) ≤ n; omega)]
        | Z c =>
          simp only [Term.deg] at hst
          show ltF f' a (Z c) = ltF g' a (Z c)
          rw [R a (Z c) (by show a.deg + (1 + c.deg) ≤ n; omega)]
      | omg x =>
        simp only [Term.deg] at hst
        cases t with
        | add c d =>
          simp only [Term.deg] at hst
          show (omg x == c || ltF f' (omg x) c) = (omg x == c || ltF g' (omg x) c)
          rw [R (omg x) c (by show (1 + x.deg) + c.deg ≤ n; omega)]
        | omg y =>
          simp only [Term.deg] at hst
          show (if (omg x == omg y) = true then false else ltF f' x y)
              = (if (omg x == omg y) = true then false else ltF g' x y)
          rw [R x y (by omega)]
        | zero => rfl
        | M => rfl
        | phi c d => rfl
        | psi k c => rfl
        | Z c => rfl
      | phi a b =>
        simp only [Term.deg] at hst
        cases t with
        | zero => rfl
        | M => rfl
        | omg y => rfl
        | add c d =>
          simp only [Term.deg] at hst
          show (phi a b == c || ltF f' (phi a b) c) = (phi a b == c || ltF g' (phi a b) c)
          rw [R (phi a b) c (by show (1 + a.deg + b.deg) + c.deg ≤ n; omega)]
        | phi c d =>
          simp only [Term.deg] at hst
          show (if (phi a b == phi c d) = true then false
                else if (a == c) = true then ltF f' b d
                else if ltF f' a c = true then ltF f' b (phi c d)
                else (phi a b == d || ltF f' (phi a b) d))
              = (if (phi a b == phi c d) = true then false
                 else if (a == c) = true then ltF g' b d
                 else if ltF g' a c = true then ltF g' b (phi c d)
                 else (phi a b == d || ltF g' (phi a b) d))
          rw [R b d (by omega), R a c (by omega),
            R b (phi c d) (by show b.deg + (1 + c.deg + d.deg) ≤ n; omega),
            R (phi a b) d (by show (1 + a.deg + b.deg) + d.deg ≤ n; omega)]
        | psi k c =>
          simp only [Term.deg] at hst
          show (ltF f' a (psi k c) && ltF f' b (psi k c))
              = (ltF g' a (psi k c) && ltF g' b (psi k c))
          rw [R a (psi k c) (by show a.deg + (1 + k.deg + c.deg) ≤ n; omega),
            R b (psi k c) (by show b.deg + (1 + k.deg + c.deg) ≤ n; omega)]
        | Z c =>
          simp only [Term.deg] at hst
          show (ltF f' a (Z c) && ltF f' b (Z c)) = (ltF g' a (Z c) && ltF g' b (Z c))
          rw [R a (Z c) (by show a.deg + (1 + c.deg) ≤ n; omega),
            R b (Z c) (by show b.deg + (1 + c.deg) ≤ n; omega)]
      | psi k a =>
        simp only [Term.deg] at hst
        cases t with
        | zero => rfl
        | M => rfl
        | omg y => rfl
        | add c d =>
          simp only [Term.deg] at hst
          show (psi k a == c || ltF f' (psi k a) c) = (psi k a == c || ltF g' (psi k a) c)
          rw [R (psi k a) c (by show (1 + k.deg + a.deg) + c.deg ≤ n; omega)]
        | phi c d =>
          simp only [Term.deg] at hst
          show (psi k a == c || psi k a == d || ltF f' (psi k a) c || ltF f' (psi k a) d)
              = (psi k a == c || psi k a == d || ltF g' (psi k a) c || ltF g' (psi k a) d)
          rw [R (psi k a) c (by show (1 + k.deg + a.deg) + c.deg ≤ n; omega),
            R (psi k a) d (by show (1 + k.deg + a.deg) + d.deg ≤ n; omega)]
        | psi p b =>
          simp only [Term.deg] at hst
          show (if (psi k a == psi p b) = true then false
                else if (k == p) = true then ltF f' a b
                else if ltF f' k p = true then ltF f' k (psi p b)
                else ltF f' (psi k a) p)
              = (if (psi k a == psi p b) = true then false
                 else if (k == p) = true then ltF g' a b
                 else if ltF g' k p = true then ltF g' k (psi p b)
                 else ltF g' (psi k a) p)
          rw [R a b (by omega), R k p (by omega),
            R k (psi p b) (by show k.deg + (1 + p.deg + b.deg) ≤ n; omega),
            R (psi k a) p (by show (1 + k.deg + a.deg) + p.deg ≤ n; omega)]
        | Z d =>
          simp only [Term.deg] at hst
          have hds := deg_starF g' d
          show (if (psi k a == Z d) = true then false
                else if (k == Z d || ltF f' k (Z d)) = true then true
                else (psi k a == starF f' d || ltF f' (psi k a) (starF f' d)))
              = (if (psi k a == Z d) = true then false
                 else if (k == Z d || ltF g' k (Z d)) = true then true
                 else (psi k a == starF g' d || ltF g' (psi k a) (starF g' d)))
          rw [R k (Z d) (by show k.deg + (1 + d.deg) ≤ n; omega), RS d (by omega),
            R (psi k a) (starF g' d) (by show (1 + k.deg + a.deg) + (starF g' d).deg ≤ n; omega)]
      | Z e =>
        simp only [Term.deg] at hst
        cases t with
        | zero => rfl
        | M => rfl
        | omg y => rfl
        | add c d =>
          simp only [Term.deg] at hst
          show (Z e == c || ltF f' (Z e) c) = (Z e == c || ltF g' (Z e) c)
          rw [R (Z e) c (by show (1 + e.deg) + c.deg ≤ n; omega)]
        | phi c d =>
          simp only [Term.deg] at hst
          show (Z e == c || Z e == d || ltF f' (Z e) c || ltF f' (Z e) d)
              = (Z e == c || Z e == d || ltF g' (Z e) c || ltF g' (Z e) d)
          rw [R (Z e) c (by show (1 + e.deg) + c.deg ≤ n; omega),
            R (Z e) d (by show (1 + e.deg) + d.deg ≤ n; omega)]
        | psi k b =>
          simp only [Term.deg] at hst
          have hds := deg_starF g' e
          show (if (Z e == psi k b) = true then false
                else if (k == Z e || ltF f' k (Z e)) = true then false
                else ltF f' (starF f' e) (psi k b))
              = (if (Z e == psi k b) = true then false
                 else if (k == Z e || ltF g' k (Z e)) = true then false
                 else ltF g' (starF g' e) (psi k b))
          rw [R k (Z e) (by show k.deg + (1 + e.deg) ≤ n; omega), RS e (by omega),
            R (starF g' e) (psi k b) (by show (starF g' e).deg + (1 + k.deg + b.deg) ≤ n; omega)]
        | Z b =>
          simp only [Term.deg] at hst
          have hds := deg_starF g' e
          have hdb := deg_starF g' b
          show (if (Z e == Z b) = true then false
                else if ltF f' e b = true then ltF f' (starF f' e) (Z b)
                else (Z e == starF f' b || ltF f' (Z e) (starF f' b)))
              = (if (Z e == Z b) = true then false
                 else if ltF g' e b = true then ltF g' (starF g' e) (Z b)
                 else (Z e == starF g' b || ltF g' (Z e) (starF g' b)))
          rw [R e b (by omega), RS e (by omega), RS b (by omega),
            R (starF g' e) (Z b) (by show (starF g' e).deg + (1 + b.deg) ≤ n; omega),
            R (Z e) (starF g' b) (by show (1 + e.deg) + (starF g' b).deg ≤ n; omega)]
    · intro t ht f g hf hg
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      have hf' : n ≤ f' := by omega
      have hg' : n ≤ g' := by omega
      have R : ∀ (x y : Term), x.deg + y.deg ≤ n → ltF f' x y = ltF g' x y :=
        fun x y h => IHl x y h f' g' hf' hg'
      have RS : ∀ (x : Term), x.deg ≤ n → starF f' x = starF g' x :=
        fun x h => IHs x h f' g' hf' hg'
      cases t with
      | zero => rfl
      | M => rfl
      | psi k a => rfl
      | Z a => rfl
      | omg a =>
        simp only [Term.deg] at ht
        show starF f' a = starF g' a
        rw [RS a (by omega)]
      | add a b =>
        simp only [Term.deg] at ht
        have h1 := deg_starF g' a
        have h2 := deg_starF g' b
        show (if ltF f' (starF f' a) (starF f' b) then starF f' b else starF f' a)
            = (if ltF g' (starF g' a) (starF g' b) then starF g' b else starF g' a)
        rw [RS a (by omega), RS b (by omega),
          R (starF g' a) (starF g' b) (by omega)]
      | phi a b =>
        simp only [Term.deg] at ht
        have h1 := deg_starF g' a
        have h2 := deg_starF g' b
        show (if ltF f' (starF f' a) (starF f' b) then starF f' b else starF f' a)
            = (if ltF g' (starF g' a) (starF g' b) then starF g' b else starF g' a)
        rw [RS a (by omega), RS b (by omega),
          R (starF g' a) (starF g' b) (by omega)]

/-- **`ltF` above the degree bound does not depend on the fuel.** -/
theorem ltF_stable (s t : Term) (f g : Nat) (hf : s.deg + t.deg ≤ f) (hg : s.deg + t.deg ≤ g) :
    ltF f s t = ltF g s t :=
  (stable_aux (s.deg + t.deg)).1 s t (Nat.le_refl _) f g hf hg

/-- **`starF` above the degree bound does not depend on the fuel.** -/
theorem starF_stable (t : Term) (f g : Nat) (hf : t.deg ≤ f) (hg : t.deg ≤ g) :
    starF f t = starF g t :=
  (stable_aux t.deg).2 t (Nat.le_refl _) f g hf hg

/-- The form the order proofs of `Evidence/Cert.lean` want: a single
    sufficiently-fuelled computation determines `lt`. -/
theorem lt_eq_ltF (s t : Term) (f : Nat) (hf : s.deg + t.deg ≤ f) : lt s t = ltF f s t :=
  ltF_stable s t _ f (by show s.deg + t.deg ≤ 2 * (s.deg + t.deg) + 8; omega) hf

/-- **Fuel monotonicity**, the corollary that was missing everywhere: an order
    fact established at one sufficient fuel holds at every sufficient fuel. -/
theorem ltF_mono {s t : Term} {f g : Nat} (hf : s.deg + t.deg ≤ f) (hg : s.deg + t.deg ≤ g)
    (h : ltF f s t = true) : ltF g s t = true := by
  rw [← ltF_stable s t f g hf hg]
  exact h

/-! ### Evidence that §5 has content

`ltF` really does change its answer with the fuel below the bound, so
`ltF_stable` is not a statement about nothing.  `3 < 4` is decided only from
fuel 3 upwards; the degree bound (26 for this pair) is generous but sound. -/

#guard ltF 2 (ofNat 3) (ofNat 4) == false
#guard ltF 3 (ofNat 3) (ofNat 4) == true
#guard lt (ofNat 3) (ofNat 4) == true
#guard (ofNat 3 : Term).deg + (ofNat 4 : Term).deg == 26
#guard (List.range 20).all (fun f => decide (3 ≤ f) == ltF f (ofNat 3) (ofNat 4))

/-! ## §6 TRANSITIVITY — the feasibility map  (D2, step 2)

STATUS.  §7 below EXECUTES the φ̄-fragment half of the staging plan of this map
(item 2 of "STAGING"), and §8.2 then extends all of it to `M` and `ω̄^·` (§8's
Stage 3a); item 3 (the `ψ`/`Z` clauses, §8's Stage 3b) is still open.  Item 1
(un-privating the `inT` destructors of `Evidence/Cert.lean`) turned out NOT to be
needed: the fragment results below hold with no `inT` hypothesis at all — see the
note at the head of §7.  The map is kept verbatim because it is still the plan
for item 3.

TARGET.  `∀ a b c, inT a = true → inT b = true → inT c = true →
          lt a b = true → lt b c = true → lt a c = true`.

WHY §5 COMES FIRST, and what it buys.  The three hypotheses live at three
DIFFERENT default fuels (`fuelOf a b`, `fuelOf b c`, `fuelOf a c`), so before §5
the statement could not even be attacked: there was no way to bring them to a
common fuel.  With `ltF_mono` the reduction is immediate — prove the SAME-FUEL
statement

    trans_ltF : ∀ n a b c, a.deg + b.deg + c.deg ≤ n →
        inT a = true → inT b = true → inT c = true →
        ∀ f, n ≤ f → ltF f a b = true → ltF f b c = true → ltF f a c = true

and lift it with `ltF_mono` at both ends.  Note that `trans_ltF` needs no
stability internally: at fuel `f+1` the clause bodies hand the sub-facts down at
fuel `f`, which is exactly what the induction hypothesis consumes.

WHICH CLAUSES NEED WHICH INVERSIONS (this is the part that decides the cost):

  * SUMS (2.3.10 / 2.3.11 / 2.3.16).  Every case in which any of `a b c` is a
    sum reduces to its HEAD component, because a sum is compared with a non-sum
    by its head alone.  The inversions needed are the two facts the formation
    conditions supply and which `Evidence/Cert.lean` already isolates (as
    `private`; they must be un-privated): `inT (add a b) → a.isAP ∧ inT a ∧ inT b`
    and `inT (add a b) → le ((toList b).headD zero) a`.  No new theory.
  * `M`, `ω̄` (2.3.2 / 2.3.3 / 2.3.12).  Constant clauses plus `M < ω̄^γ` and
    `φ̄, ψ, Z < M`.  Free.
  * `φ̄` (2.3.13) — THE HARD ONE, and the only one the certificate lane needs.
    Its three sub-clauses are not syntactically exclusive, so transitivity needs
    ASYMMETRY first:  `ltF f a b = true → ltF f b a = false` for `inT` terms.
    Asymmetry is a same-fuel induction of exactly the same shape as `trans_ltF`
    and is strictly easier (two terms, not three); it should be proved as its own
    lemma before transitivity is attempted.  `ltF_irrefl` (already in Cert.lean,
    `private`) is its base.
  * `ψ`, `Z` (2.3.6 / 2.3.8 / 2.3.9 / 2.3.14 / 2.3.15).  These route through
    `starF`, so they additionally need: `star d < Z d`, monotonicity of `star`,
    and the `K_κ` side conditions of `inT`.  This is the deepest part — and it is
    needed ONLY above `M`.  Nothing in the table's current region reaches it.

STAGING, cheapest-useful-first:

  1. Un-private `ltF_irrefl`, `ne_of_ltF`, `inT_add`, `inT_add_head_le`,
     `inT_add_ne_zero` in Cert.lean.  Mechanical.
  2. ASYMMETRY for the `φ̄`-fragment (terms built from `0`, `⊕`, `φ̄`), then
     TRANSITIVITY for the same fragment.  This is the ε₀ region and is ALL the
     certificate lane needs: it unblocks ω^(ω^ω) (see Cert.lean §5.8) and is the
     order half of ε₀.
  3. Full asymmetry + transitivity including `ψ`/`Z`, for `cert_sound`.

A STRICTLY CHEAPER UNBLOCK for ω^(ω^ω) specifically, which does NOT need any of
the above and can be done entirely inside Cert.lean: the level-1 order is the
LEXICOGRAPHIC order on exponent lists, so introduce

    inductive LexNat : List Nat → List Nat → Prop
      | nil  {y r}      : LexNat [] (y :: r)
      | head {x y r r'} : x < y → LexNat (x :: r) (y :: r')
      | tail {x r r'}   : LexNat r r' → LexNat (x :: r) (x :: r')

prove `LexNat → PwLt` (from `ltF_ofList_head` / `ltF_ofList_prefix`, both already
stated for arbitrary sums), `PwLt → LexNat` (a short fuel induction), and
transitivity of `LexNat` (structural).  Transitivity of `PwLt` then follows, and
that is exactly the step the level-2 classification is missing.  Roughly 250
lines, no dependence on §5 and no dependence on the general theory. -/

/-! ## §7 The φ̄-fragment: comparability, asymmetry, transitivity

WHAT IS PROVED.  On the fragment of `Term` built from `0`, `⊕` and `φ̄` alone
(`Frag` below), the decision procedure `lt` of `TM/Order.lean` is a strict LINEAR
order: irreflexive (§1 of Cert.lean, re-proved here), asymmetric
(`lt_asymm`), comparable (`lt_comparable`) and TRANSITIVE (`lt_trans`).

WHY THAT IS THE USEFUL FRAGMENT.  `ω^α` is `φ̄0α` and `1` is `φ̄00`, so the whole
CNF region — every term below ε₀, and in fact every Veblen term below Γ₀ — lives
in `Frag`.  That is exactly the region `Evidence/Cert.lean` certifies, so
`lt_trans` is what its order layer has been working around.

NO `inT` HYPOTHESIS.  §6's map budgeted the `inT` destructors of Cert.lean for
this stage.  They are not needed: the proofs below never inspect a formation
condition — only the shape of the term.  (Empirically checked first, on all 275
fragment terms of degree ≤ 9, with and without the `inT` filter; the `#guard`s at
the end of this section keep a sample of that check in the file.)  This makes the
result strictly stronger than the one §6 asked for, and it means Cert.lean needs
no edit at all to consume it.

THE THREE INDUCTIONS, and why they are staged this way.

  * `cmp_aux` proves ASYMMETRY and COMPARABILITY *simultaneously*, by induction
    on `a.deg + b.deg`.  They cannot be separated: clause 2.3.13's three
    sub-clauses are selected by `a = c` / `a < c` / neither, so reading the
    reverse comparison off the forward one needs to know that "neither" really
    means `c < a` — i.e. comparability.  Conversely the comparability proof, when
    it lands in sub-clause 13(i), must know that the reverse comparison does NOT
    also land in 13(i) — i.e. asymmetry.  Each direction consumes the other only
    at STRICTLY smaller degree, so one joint induction closes both.

  * `trans_aux` proves TRANSITIVITY, with `cmp_aux` already available.  Its
    induction is NOT on `a.deg + b.deg + c.deg`: that measure fails.  The
    offending configuration is 13(iii) against 13(iii) — `φ̄αβ ≤ δ` on the left
    and `φ̄γδ ≤ β` on the right — where the natural chain
    `β < φ̄αβ ≤ δ < φ̄γδ ≤ β` needs transitivity instances whose degree sums
    EXCEED the parent's.  The measure that does work is the lexicographic pair

        (b.deg,  a.deg + c.deg)

    — the middle term first.  Every recursive call either strictly shrinks the
    middle term (the calls that replace `b` by one of its own subterms) or keeps
    `b` and strictly shrinks `a.deg + c.deg` (the calls that replace `a` or `c`
    by a subterm).  With that measure the hard configuration is discharged
    without any subterm lemma at all: `q < B` and `B < C` compose directly,
    because `q` is a proper subterm of `A` while `B` is untouched.
    `trans_aux` is written as an outer recursion on the middle degree with an
    inner `induction` on `a.deg + c.deg`, which is that lex order spelled out
    (no `WellFoundedRelation` instance is needed, and none is exported).

  * Both same-fuel statements carry a fuel hypothesis `n ≤ f`, which is free:
    §5's `ltF_stable` moves any sub-fact to whatever fuel the clause bodies hand
    it at, and `lt_eq_ltF` lifts the finished statements to the user-facing `lt`.
-/

/-- The φ̄-fragment: terms built from `0`, `⊕` and `φ̄` alone — equivalently, the
    terms mentioning none of `M`, `ω̄`, `ψ`, `Z`.  `Frag` is hereditary
    (`frag_add`, `frag_phi`), which is all the induction below uses. -/
def Frag : Term → Bool
  | zero => true
  | M => false
  | add a b => Frag a && Frag b
  | omg _ => false
  | phi a b => Frag a && Frag b
  | psi _ _ => false
  | Z _ => false

theorem frag_add {a b : Term} (h : Frag (add a b) = true) :
    Frag a = true ∧ Frag b = true := by
  simp only [Frag, Bool.and_eq_true] at h; exact h

theorem frag_phi {a b : Term} (h : Frag (phi a b) = true) :
    Frag a = true ∧ Frag b = true := by
  simp only [Frag, Bool.and_eq_true] at h; exact h

/-! ### §7.1 Elementary facts about `ltF`

`Evidence/Cert.lean` has `ltF_irrefl` / `ne_of_ltF` / `ltF_lt_zero` too, but they
are `private` there and Cert.lean imports THIS file, so they are re-proved here
(three lines each) rather than un-privated — that keeps the import direction
fixed by the header. -/

theorem ltF_irrefl (f : Nat) (x : Term) : ltF f x x = false := by
  cases f with
  | zero => rfl
  | succ g =>
    show (if (x == x) = true then false else _) = false
    simp

theorem ne_of_ltF {f : Nat} {x y : Term} (h : ltF f x y = true) : x ≠ y := by
  intro hc; subst hc; rw [ltF_irrefl] at h; exact Bool.noConfusion h

/-- Nothing is below `0`. -/
theorem ltF_right_zero (f : Nat) (t : Term) : ltF f t zero = false := by
  cases f with
  | zero => rfl
  | succ g => cases t <;> rfl

/-- `0` is below everything else (2.3.1). -/
theorem ltF_left_zero {f : Nat} (hf : 1 ≤ f) {t : Term} (h : t ≠ zero) :
    ltF f zero t = true := by
  cases f with
  | zero => omega
  | succ g => cases t <;> first | (exact absurd rfl h) | rfl

/-! ### §7.2 The four clause bodies of the fragment, as rewrite rules

On `Frag` the 16 clauses of 2.3 collapse to these four plus the two `0` cases.
Stating them once keeps the case bashes below readable — and makes it visible
that NOTHING else of 2.3 is touched. -/

/-- 2.3.16: two sums compare along the spine. -/
theorem ltF_succ_add_add (f : Nat) {a b c d : Term} (h : add a b ≠ add c d) :
    ltF (f + 1) (add a b) (add c d) = (if a = c then ltF f b d else ltF f a c) := by
  show (if (add a b == add c d) = true then false
        else if (a == c) = true then ltF f b d else ltF f a c) = _
  rw [if_neg (by simpa using h)]
  by_cases hac : a = c
  · rw [if_pos (by simpa using hac), if_pos hac]
  · rw [if_neg (by simpa using hac), if_neg hac]

/-- 2.3.10: a sum is below a non-sum exactly when its head is. -/
theorem ltF_succ_add_phi (f : Nat) (a b c d : Term) :
    ltF (f + 1) (add a b) (phi c d) = ltF f a (phi c d) := rfl

/-- 2.3.11: a non-sum is below a sum exactly when it is `≤` the head. -/
theorem ltF_succ_phi_add (f : Nat) (a b c d : Term) :
    ltF (f + 1) (phi a b) (add c d) = ((phi a b == c) || ltF f (phi a b) c) := rfl

/-- 2.3.13, the three sub-clauses. -/
theorem ltF_succ_phi_phi (f : Nat) {a b c d : Term} (h : phi a b ≠ phi c d) :
    ltF (f + 1) (phi a b) (phi c d) =
      (if a = c then ltF f b d
       else if ltF f a c = true then ltF f b (phi c d)
       else ((phi a b == d) || ltF f (phi a b) d)) := by
  show (if (phi a b == phi c d) = true then false
        else if (a == c) = true then ltF f b d
        else if ltF f a c = true then ltF f b (phi c d)
        else ((phi a b == d) || ltF f (phi a b) d)) = _
  rw [if_neg (by simpa using h)]
  by_cases hac : a = c
  · rw [if_pos (by simpa using hac), if_pos hac]
  · rw [if_neg (by simpa using hac), if_neg hac]

/-! ### §7.3 Asymmetry and comparability, by one simultaneous induction

The two halves are proved together because each consumes the other — but always
at STRICTLY smaller degree, which is what makes the single induction on
`a.deg + b.deg` close.  See the section header for why they cannot be separated.

Reading the case analysis: `a` and `b` each range over `0`, `⊕`, `φ̄` (the other
four constructors are killed by `Frag`), so there are nine shape pairs; the ones
involving `0` are immediate and the remaining four are exactly §7.2's rewrite
rules. -/

private theorem cmp_aux : ∀ (n : Nat),
    (∀ (a b : Term), Frag a = true → Frag b = true → a.deg + b.deg ≤ n →
      ∀ f, n ≤ f → ltF f a b = true → ltF f b a = false)
  ∧ (∀ (a b : Term), Frag a = true → Frag b = true → a.deg + b.deg ≤ n →
      ∀ f, n ≤ f → (ltF f a b = true ∨ a = b ∨ ltF f b a = true))
  | 0 => ⟨by
      intro a b _ _ hd
      have := deg_pos a; have := deg_pos b; omega, by
      intro a b _ _ hd
      have := deg_pos a; have := deg_pos b; omega⟩
  | n + 1 => by
    obtain ⟨IHa, IHc⟩ := cmp_aux n
    constructor
    -- ============================ ASYMMETRY ============================
    · intro a b hfa hfb hd f hf h
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hf' : n ≤ f' := by omega
      have hab : a ≠ b := ne_of_ltF h
      cases a with
      | M => simp [Frag] at hfa
      | omg x => simp [Frag] at hfa
      | psi k x => simp [Frag] at hfa
      | Z x => simp [Frag] at hfa
      | zero => exact ltF_right_zero _ b
      | add p q =>
        obtain ⟨hfp, hfq⟩ := frag_add hfa
        cases b with
        | M => simp [Frag] at hfb
        | omg x => simp [Frag] at hfb
        | psi k x => simp [Frag] at hfb
        | Z x => simp [Frag] at hfb
        | zero => rw [ltF_right_zero] at h; exact Bool.noConfusion h
        | add r s =>
          obtain ⟨hfr, hfs⟩ := frag_add hfb
          rw [ltF_succ_add_add _ hab] at h
          rw [ltF_succ_add_add _ (Ne.symm hab)]
          simp only [Term.deg] at hd
          have dp := deg_pos p; have dq := deg_pos q
          have dr := deg_pos r; have ds := deg_pos s
          by_cases hpr : p = r
          · subst hpr
            rw [if_pos rfl] at h
            rw [if_pos rfl]
            exact IHa q s hfq hfs (by omega) f' hf' h
          · rw [if_neg hpr] at h
            rw [if_neg (Ne.symm hpr)]
            exact IHa p r hfp hfr (by omega) f' hf' h
        | phi r s =>
          obtain ⟨hfr, hfs⟩ := frag_phi hfb
          rw [ltF_succ_add_phi] at h
          rw [ltF_succ_phi_add]
          simp only [Term.deg] at hd
          have dp := deg_pos p; have dq := deg_pos q
          have dr := deg_pos r; have ds := deg_pos s
          have hne : phi r s ≠ p := by
            intro hc; rw [hc, ltF_irrefl] at h; exact Bool.noConfusion h
          have h2 : ltF f' (phi r s) p = false :=
            IHa p (phi r s) hfp hfb (by simp only [Term.deg]; omega) f' hf' h
          simp [hne, h2]
      | phi p q =>
        obtain ⟨hfp, hfq⟩ := frag_phi hfa
        cases b with
        | M => simp [Frag] at hfb
        | omg x => simp [Frag] at hfb
        | psi k x => simp [Frag] at hfb
        | Z x => simp [Frag] at hfb
        | zero => rw [ltF_right_zero] at h; exact Bool.noConfusion h
        | add r s =>
          obtain ⟨hfr, hfs⟩ := frag_add hfb
          rw [ltF_succ_phi_add] at h
          rw [ltF_succ_add_phi]
          simp only [Term.deg] at hd
          have dp := deg_pos p; have dq := deg_pos q
          have dr := deg_pos r; have ds := deg_pos s
          simp only [Bool.or_eq_true, beq_iff_eq] at h
          rcases h with h1 | h1
          · rw [← h1]; exact ltF_irrefl _ _
          · exact IHa (phi p q) r hfa hfr (by simp only [Term.deg]; omega) f' hf' h1
        | phi r s =>
          obtain ⟨hfr, hfs⟩ := frag_phi hfb
          rw [ltF_succ_phi_phi _ hab] at h
          rw [ltF_succ_phi_phi _ (Ne.symm hab)]
          simp only [Term.deg] at hd
          have dp := deg_pos p; have dq := deg_pos q
          have dr := deg_pos r; have ds := deg_pos s
          by_cases hpr : p = r
          · subst hpr
            rw [if_pos rfl] at h
            rw [if_pos rfl]
            exact IHa q s hfq hfs (by omega) f' hf' h
          · rw [if_neg hpr] at h
            rw [if_neg (Ne.symm hpr)]
            by_cases hlt : ltF f' p r = true
            · -- 13(i) forward: α < γ, so the reverse comparison lands in 13(iii)
              rw [if_pos hlt] at h
              have hrp : ltF f' r p = false := IHa p r hfp hfr (by omega) f' hf' hlt
              rw [if_neg (by simp [hrp])]
              have hne : phi r s ≠ q := by
                intro hc; rw [hc, ltF_irrefl] at h; exact Bool.noConfusion h
              have h2 : ltF f' (phi r s) q = false :=
                IHa q (phi r s) hfq hfb (by simp only [Term.deg]; omega) f' hf' h
              simp [hne, h2]
            · -- 13(iii) forward: THIS is the case that needs comparability —
              -- "not α = γ and not α < γ" has to be turned into "γ < α".
              rw [if_neg hlt] at h
              have hrp : ltF f' r p = true := by
                rcases IHc p r hfp hfr (by omega) f' hf' with h1 | h1 | h1
                · exact absurd h1 hlt
                · exact absurd h1 hpr
                · exact h1
              rw [if_pos hrp]
              simp only [Bool.or_eq_true, beq_iff_eq] at h
              rcases h with h1 | h1
              · rw [← h1]; exact ltF_irrefl _ _
              · exact IHa (phi p q) s hfa hfs (by simp only [Term.deg]; omega) f' hf' h1
    -- ========================== COMPARABILITY ==========================
    · intro a b hfa hfb hd f hf
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hf' : n ≤ f' := by omega
      by_cases hab : a = b
      · exact Or.inr (Or.inl hab)
      cases a with
      | M => simp [Frag] at hfa
      | omg x => simp [Frag] at hfa
      | psi k x => simp [Frag] at hfa
      | Z x => simp [Frag] at hfa
      | zero => exact Or.inl (ltF_left_zero (by omega) (Ne.symm hab))
      | add p q =>
        obtain ⟨hfp, hfq⟩ := frag_add hfa
        cases b with
        | M => simp [Frag] at hfb
        | omg x => simp [Frag] at hfb
        | psi k x => simp [Frag] at hfb
        | Z x => simp [Frag] at hfb
        | zero =>
          exact Or.inr (Or.inr
            (ltF_left_zero (by omega) (by intro hc; exact Term.noConfusion hc)))
        | add r s =>
          obtain ⟨hfr, hfs⟩ := frag_add hfb
          rw [ltF_succ_add_add _ hab, ltF_succ_add_add _ (Ne.symm hab)]
          simp only [Term.deg] at hd
          have dp := deg_pos p; have dq := deg_pos q
          have dr := deg_pos r; have ds := deg_pos s
          by_cases hpr : p = r
          · subst hpr
            rw [if_pos rfl, if_pos rfl]
            have hqs : q ≠ s := fun hc => hab (by rw [hc])
            rcases IHc q s hfq hfs (by omega) f' hf' with h1 | h1 | h1
            · exact Or.inl h1
            · exact absurd h1 hqs
            · exact Or.inr (Or.inr h1)
          · rw [if_neg hpr, if_neg (Ne.symm hpr)]
            rcases IHc p r hfp hfr (by omega) f' hf' with h1 | h1 | h1
            · exact Or.inl h1
            · exact absurd h1 hpr
            · exact Or.inr (Or.inr h1)
        | phi r s =>
          obtain ⟨hfr, hfs⟩ := frag_phi hfb
          rw [ltF_succ_add_phi, ltF_succ_phi_add]
          simp only [Term.deg] at hd
          have dp := deg_pos p; have dq := deg_pos q
          have dr := deg_pos r; have ds := deg_pos s
          rcases IHc p (phi r s) hfp hfb (by simp only [Term.deg]; omega) f' hf' with h1 | h1 | h1
          · exact Or.inl h1
          · exact Or.inr (Or.inr (by simp [h1]))
          · exact Or.inr (Or.inr (by simp [h1]))
      | phi p q =>
        obtain ⟨hfp, hfq⟩ := frag_phi hfa
        cases b with
        | M => simp [Frag] at hfb
        | omg x => simp [Frag] at hfb
        | psi k x => simp [Frag] at hfb
        | Z x => simp [Frag] at hfb
        | zero =>
          exact Or.inr (Or.inr
            (ltF_left_zero (by omega) (by intro hc; exact Term.noConfusion hc)))
        | add r s =>
          obtain ⟨hfr, hfs⟩ := frag_add hfb
          rw [ltF_succ_phi_add, ltF_succ_add_phi]
          simp only [Term.deg] at hd
          have dp := deg_pos p; have dq := deg_pos q
          have dr := deg_pos r; have ds := deg_pos s
          rcases IHc (phi p q) r hfa hfr (by simp only [Term.deg]; omega) f' hf' with h1 | h1 | h1
          · exact Or.inl (by simp [h1])
          · exact Or.inl (by simp [h1])
          · exact Or.inr (Or.inr h1)
        | phi r s =>
          obtain ⟨hfr, hfs⟩ := frag_phi hfb
          rw [ltF_succ_phi_phi _ hab, ltF_succ_phi_phi _ (Ne.symm hab)]
          simp only [Term.deg] at hd
          have dp := deg_pos p; have dq := deg_pos q
          have dr := deg_pos r; have ds := deg_pos s
          by_cases hpr : p = r
          · subst hpr
            rw [if_pos rfl, if_pos rfl]
            have hqs : q ≠ s := fun hc => hab (by rw [hc])
            rcases IHc q s hfq hfs (by omega) f' hf' with h1 | h1 | h1
            · exact Or.inl h1
            · exact absurd h1 hqs
            · exact Or.inr (Or.inr h1)
          · rw [if_neg hpr, if_neg (Ne.symm hpr)]
            rcases IHc p r hfp hfr (by omega) f' hf' with h1 | h1 | h1
            · -- α < γ: the reverse comparison cannot also be 13(i) — asymmetry
              have hrp : ltF f' r p = false := IHa p r hfp hfr (by omega) f' hf' h1
              rw [if_pos h1, if_neg (by simp [hrp])]
              rcases IHc q (phi r s) hfq hfb (by simp only [Term.deg]; omega) f' hf'
                with h2 | h2 | h2
              · exact Or.inl h2
              · exact Or.inr (Or.inr (by simp [h2]))
              · exact Or.inr (Or.inr (by simp [h2]))
            · exact absurd h1 hpr
            · have hpr2 : ltF f' p r = false := IHa r p hfr hfp (by omega) f' hf' h1
              rw [if_neg (by simp [hpr2]), if_pos h1]
              rcases IHc (phi p q) s hfa hfs (by simp only [Term.deg]; omega) f' hf'
                with h2 | h2 | h2
              · exact Or.inl (by simp [h2])
              · exact Or.inl (by simp [h2])
              · exact Or.inr (Or.inr h2)

/-- **ASYMMETRY on the φ̄-fragment**, same fuel.  (STAGE 1 of the §6 map, in the
    stronger `inT`-free form.) -/
theorem ltF_asymm {a b : Term} (hfa : Frag a = true) (hfb : Frag b = true)
    {f : Nat} (hf : a.deg + b.deg ≤ f) (h : ltF f a b = true) : ltF f b a = false :=
  (cmp_aux (a.deg + b.deg)).1 a b hfa hfb (Nat.le_refl _) f hf h

/-- **COMPARABILITY on the φ̄-fragment**, same fuel. -/
theorem ltF_comparable {a b : Term} (hfa : Frag a = true) (hfb : Frag b = true)
    {f : Nat} (hf : a.deg + b.deg ≤ f) :
    ltF f a b = true ∨ a = b ∨ ltF f b a = true :=
  (cmp_aux (a.deg + b.deg)).2 a b hfa hfb (Nat.le_refl _) f hf

/-- A `Frag` term is a `0`, a sum, or a `φ̄` — and the parts stay in the fragment.
    Packaging the four impossible constructors once keeps §7.4 readable. -/
theorem frag_cases {t : Term} (h : Frag t = true) :
    t = zero
    ∨ (∃ x y, t = add x y ∧ Frag x = true ∧ Frag y = true)
    ∨ (∃ x y, t = phi x y ∧ Frag x = true ∧ Frag y = true) := by
  cases t with
  | zero => exact Or.inl rfl
  | M => simp [Frag] at h
  | omg x => simp [Frag] at h
  | psi k x => simp [Frag] at h
  | Z x => simp [Frag] at h
  | add x y => exact Or.inr (Or.inl ⟨x, y, rfl, (frag_add h).1, (frag_add h).2⟩)
  | phi x y => exact Or.inr (Or.inr ⟨x, y, rfl, (frag_phi h).1, (frag_phi h).2⟩)

/-! ### §7.4 TRANSITIVITY

The measure is the lexicographic pair `(b.deg, a.deg + c.deg)` — see the section
header for why the flat sum `a.deg + b.deg + c.deg` cannot work.  It is spelled
out as an outer recursion on `n` (a bound on the MIDDLE degree) with an inner
`induction` on `m` (a bound on `a.deg + c.deg`), which gives exactly two induction
hypotheses:

  `TR1` — the middle term may be replaced by anything of smaller degree, and then
          `a` and `c` are unconstrained;
  `TR2` — the middle term stays `b`, and `a`, `c` may be replaced by anything with
          a smaller degree sum.

Every one of the nine shape combinations below is discharged by one of those two.
The `ψ`/`Z` clauses are never reached, which is why no `starF` reasoning appears. -/

private theorem trans_aux : ∀ (n : Nat) (m : Nat) (a b c : Term),
    Frag a = true → Frag b = true → Frag c = true →
    b.deg ≤ n → a.deg + c.deg ≤ m →
    ∀ f, a.deg + b.deg + c.deg ≤ f →
    ltF f a b = true → ltF f b c = true → ltF f a c = true
  | 0 => by
    intro _ _ b _ _ _ _ hb _ _ _ _ _
    exfalso; have := deg_pos b; omega
  | n + 1 => by
    intro m
    induction m with
    | zero =>
      intro a _ c _ _ _ _ hm _ _ _ _
      exfalso; have := deg_pos a; have := deg_pos c; omega
    | succ m ihm =>
      intro a b c hfa hfb hfc hb hm f hf h1 h2
      -- the two induction hypotheses, in the shape the case analysis wants
      have TR1 : ∀ (x y z : Term), Frag x = true → Frag y = true → Frag z = true →
          y.deg ≤ n → ∀ g, x.deg + y.deg + z.deg ≤ g →
          ltF g x y = true → ltF g y z = true → ltF g x z = true :=
        fun x y z hx hy hz hyd g hg =>
          trans_aux n (x.deg + z.deg) x y z hx hy hz hyd (Nat.le_refl _) g hg
      have TR2 : ∀ (x z : Term), Frag x = true → Frag z = true →
          x.deg + z.deg ≤ m → ∀ g, x.deg + b.deg + z.deg ≤ g →
          ltF g x b = true → ltF g b z = true → ltF g x z = true :=
        fun x z hx hz hd g hg => ihm x b z hx hfb hz hb hd g hg
      have da := deg_pos a; have db := deg_pos b; have dc := deg_pos c
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      -- §5 is what lets a sub-fact move between the two fuels in play
      have LOW : ∀ (x y : Term), x.deg + y.deg ≤ f' →
          ltF (f' + 1) x y = true → ltF f' x y = true := by
        intro x y hxy h
        rw [ltF_stable x y f' (f' + 1) hxy (by omega)]; exact h
      have UP : ∀ (x y : Term), x.deg + y.deg ≤ f' →
          ltF f' x y = true → ltF (f' + 1) x y = true := by
        intro x y hxy h
        rw [ltF_stable x y (f' + 1) f' (by omega) hxy]; exact h
      have hbz : b ≠ zero := by
        intro hc; rw [hc, ltF_right_zero] at h1; exact Bool.noConfusion h1
      have hcz : c ≠ zero := by
        intro hc; rw [hc, ltF_right_zero] at h2; exact Bool.noConfusion h2
      have hac : a ≠ c := by
        intro hc; subst hc
        rw [ltF_asymm hfa hfb (by omega) h1] at h2; exact Bool.noConfusion h2
      rcases frag_cases hfa with rfl | ⟨p, q, rfl, hfp, hfq⟩ | ⟨p, q, rfl, hfp, hfq⟩
      · exact ltF_left_zero (by omega) hcz
      · rcases frag_cases hfb with rfl | ⟨r, s, rfl, hfr, hfs⟩ | ⟨r, s, rfl, hfr, hfs⟩
        · exact absurd rfl hbz
        · rcases frag_cases hfc with rfl | ⟨t, u, rfl, hft, hfu⟩ | ⟨t, u, rfl, hft, hfu⟩
          · exact absurd rfl hcz
          · -- (1) ⊕ / ⊕ / ⊕ : 2.3.16 three times, along the spine
            have dp := deg_pos p; have dq := deg_pos q; have dr := deg_pos r
            have ds := deg_pos s; have dt := deg_pos t; have du := deg_pos u
            have eA : (add p q).deg = 1 + p.deg + q.deg := rfl
            have eB : (add r s).deg = 1 + r.deg + s.deg := rfl
            have eC : (add t u).deg = 1 + t.deg + u.deg := rfl
            have hab1 : add p q ≠ add r s := ne_of_ltF h1
            have hab2 : add r s ≠ add t u := ne_of_ltF h2
            rw [ltF_succ_add_add _ hab1] at h1
            rw [ltF_succ_add_add _ hab2] at h2
            rw [ltF_succ_add_add _ hac]
            by_cases hpr : p = r
            · subst hpr
              rw [if_pos rfl] at h1
              by_cases hrt : p = t
              · subst hrt
                rw [if_pos rfl] at h2
                rw [if_pos rfl]
                exact TR1 q s u hfq hfs hfu (by omega) f' (by omega) h1 h2
              · rw [if_neg hrt] at h2
                rw [if_neg hrt]
                exact h2
            · rw [if_neg hpr] at h1
              by_cases hrt : r = t
              · subst hrt
                rw [if_pos rfl] at h2
                rw [if_neg hpr]
                exact h1
              · rw [if_neg hrt] at h2
                have hpt : p ≠ t := by
                  intro hc; subst hc
                  rw [ltF_asymm hfp hfr (by omega) h1] at h2; exact Bool.noConfusion h2
                rw [if_neg hpt]
                exact TR1 p r t hfp hfr hft (by omega) f' (by omega) h1 h2
          · -- (2) ⊕ / ⊕ / φ̄
            have dp := deg_pos p; have dq := deg_pos q; have dr := deg_pos r
            have ds := deg_pos s; have dt := deg_pos t; have du := deg_pos u
            have eA : (add p q).deg = 1 + p.deg + q.deg := rfl
            have eB : (add r s).deg = 1 + r.deg + s.deg := rfl
            have eC : (phi t u).deg = 1 + t.deg + u.deg := rfl
            have hab1 : add p q ≠ add r s := ne_of_ltF h1
            rw [ltF_succ_add_add _ hab1] at h1
            rw [ltF_succ_add_phi] at h2
            rw [ltF_succ_add_phi]
            by_cases hpr : p = r
            · subst hpr; exact h2
            · rw [if_neg hpr] at h1
              exact TR1 p r (phi t u) hfp hfr hfc (by omega) f' (by omega) h1 h2
        · rcases frag_cases hfc with rfl | ⟨t, u, rfl, hft, hfu⟩ | ⟨t, u, rfl, hft, hfu⟩
          · exact absurd rfl hcz
          · -- (3) ⊕ / φ̄ / ⊕
            have dp := deg_pos p; have dq := deg_pos q; have dr := deg_pos r
            have ds := deg_pos s; have dt := deg_pos t; have du := deg_pos u
            have eA : (add p q).deg = 1 + p.deg + q.deg := rfl
            have eB : (phi r s).deg = 1 + r.deg + s.deg := rfl
            have eC : (add t u).deg = 1 + t.deg + u.deg := rfl
            rw [ltF_succ_add_phi] at h1
            rw [ltF_succ_phi_add] at h2
            rw [ltF_succ_add_add _ hac]
            simp only [Bool.or_eq_true, beq_iff_eq] at h2
            have hpt : ltF f' p t = true := by
              rcases h2 with h3 | h3
              · rw [← h3]; exact h1
              · exact TR2 p t hfp hft (by omega) f' (by omega) h1 h3
            rw [if_neg (ne_of_ltF hpt)]
            exact hpt
          · -- (4) ⊕ / φ̄ / φ̄
            have dp := deg_pos p; have dq := deg_pos q; have dr := deg_pos r
            have ds := deg_pos s; have dt := deg_pos t; have du := deg_pos u
            have eA : (add p q).deg = 1 + p.deg + q.deg := rfl
            have eB : (phi r s).deg = 1 + r.deg + s.deg := rfl
            have eC : (phi t u).deg = 1 + t.deg + u.deg := rfl
            have hBC : ltF f' (phi r s) (phi t u) = true :=
              LOW (phi r s) (phi t u) (by omega) h2
            rw [ltF_succ_add_phi] at h1
            rw [ltF_succ_add_phi]
            exact TR2 p (phi t u) hfp hfc (by omega) f' (by omega) h1 hBC
      · rcases frag_cases hfb with rfl | ⟨r, s, rfl, hfr, hfs⟩ | ⟨r, s, rfl, hfr, hfs⟩
        · exact absurd rfl hbz
        · rcases frag_cases hfc with rfl | ⟨t, u, rfl, hft, hfu⟩ | ⟨t, u, rfl, hft, hfu⟩
          · exact absurd rfl hcz
          · -- (5) φ̄ / ⊕ / ⊕
            have dp := deg_pos p; have dq := deg_pos q; have dr := deg_pos r
            have ds := deg_pos s; have dt := deg_pos t; have du := deg_pos u
            have eA : (phi p q).deg = 1 + p.deg + q.deg := rfl
            have eB : (add r s).deg = 1 + r.deg + s.deg := rfl
            have eC : (add t u).deg = 1 + t.deg + u.deg := rfl
            have hab2 : add r s ≠ add t u := ne_of_ltF h2
            rw [ltF_succ_phi_add] at h1
            rw [ltF_succ_add_add _ hab2] at h2
            rw [ltF_succ_phi_add]
            by_cases hrt : r = t
            · subst hrt; exact h1
            · rw [if_neg hrt] at h2
              simp only [Bool.or_eq_true, beq_iff_eq] at h1
              rcases h1 with h3 | h3
              · rw [h3]; simp [h2]
              · have h4 : ltF f' (phi p q) t = true :=
                  TR1 (phi p q) r t hfa hfr hft (by omega) f' (by omega) h3 h2
                simp [h4]
          · -- (6) φ̄ / ⊕ / φ̄
            have dp := deg_pos p; have dq := deg_pos q; have dr := deg_pos r
            have ds := deg_pos s; have dt := deg_pos t; have du := deg_pos u
            have eA : (phi p q).deg = 1 + p.deg + q.deg := rfl
            have eB : (add r s).deg = 1 + r.deg + s.deg := rfl
            have eC : (phi t u).deg = 1 + t.deg + u.deg := rfl
            rw [ltF_succ_phi_add] at h1
            rw [ltF_succ_add_phi] at h2
            simp only [Bool.or_eq_true, beq_iff_eq] at h1
            have h4 : ltF f' (phi p q) (phi t u) = true := by
              rcases h1 with h3 | h3
              · rw [h3]; exact h2
              · exact TR1 (phi p q) r (phi t u) hfa hfr hfc (by omega) f' (by omega) h3 h2
            exact UP (phi p q) (phi t u) (by omega) h4
        · rcases frag_cases hfc with rfl | ⟨t, u, rfl, hft, hfu⟩ | ⟨t, u, rfl, hft, hfu⟩
          · exact absurd rfl hcz
          · -- (7) φ̄ / φ̄ / ⊕
            have dp := deg_pos p; have dq := deg_pos q; have dr := deg_pos r
            have ds := deg_pos s; have dt := deg_pos t; have du := deg_pos u
            have eA : (phi p q).deg = 1 + p.deg + q.deg := rfl
            have eB : (phi r s).deg = 1 + r.deg + s.deg := rfl
            have eC : (add t u).deg = 1 + t.deg + u.deg := rfl
            have hAB : ltF f' (phi p q) (phi r s) = true :=
              LOW (phi p q) (phi r s) (by omega) h1
            rw [ltF_succ_phi_add] at h2
            rw [ltF_succ_phi_add]
            simp only [Bool.or_eq_true, beq_iff_eq] at h2
            rcases h2 with h3 | h3
            · rw [← h3]; simp [hAB]
            · have h4 : ltF f' (phi p q) t = true :=
                TR2 (phi p q) t hfa hft (by omega) f' (by omega) hAB h3
              simp [h4]
          · -- (8) φ̄ / φ̄ / φ̄ : the nine sub-clause combinations of 2.3.13
            have dp := deg_pos p; have dq := deg_pos q; have dr := deg_pos r
            have ds := deg_pos s; have dt := deg_pos t; have du := deg_pos u
            have eA : (phi p q).deg = 1 + p.deg + q.deg := rfl
            have eB : (phi r s).deg = 1 + r.deg + s.deg := rfl
            have eC : (phi t u).deg = 1 + t.deg + u.deg := rfl
            have hAB : ltF f' (phi p q) (phi r s) = true :=
              LOW (phi p q) (phi r s) (by omega) h1
            have hBC : ltF f' (phi r s) (phi t u) = true :=
              LOW (phi r s) (phi t u) (by omega) h2
            have hab1 : phi p q ≠ phi r s := ne_of_ltF h1
            have hab2 : phi r s ≠ phi t u := ne_of_ltF h2
            rw [ltF_succ_phi_phi _ hab1] at h1
            rw [ltF_succ_phi_phi _ hab2] at h2
            by_cases hpr : p = r
            · -- 13(ii) on the left: α = γ
              subst hpr
              rw [if_pos rfl] at h1
              by_cases hrt : p = t
              · subst hrt
                rw [if_pos rfl] at h2
                rw [ltF_succ_phi_phi _ hac, if_pos rfl]
                exact TR1 q s u hfq hfs hfu (by omega) f' (by omega) h1 h2
              · rw [if_neg hrt] at h2
                by_cases hrt2 : ltF f' p t = true
                · rw [if_pos hrt2] at h2
                  rw [ltF_succ_phi_phi _ hac, if_neg hrt, if_pos hrt2]
                  exact TR1 q s (phi t u) hfq hfs hfc (by omega) f' (by omega) h1 h2
                · rw [if_neg hrt2] at h2
                  rw [ltF_succ_phi_phi _ hac, if_neg hrt, if_neg hrt2]
                  simp only [Bool.or_eq_true, beq_iff_eq] at h2
                  rcases h2 with h3 | h3
                  · rw [← h3]; simp [hAB]
                  · have h4 : ltF f' (phi p q) u = true :=
                      TR2 (phi p q) u hfa hfu (by omega) f' (by omega) hAB h3
                    simp [h4]
            · rw [if_neg hpr] at h1
              by_cases hpr2 : ltF f' p r = true
              · -- 13(i) on the left: α < γ, and then β < φ̄γδ carries everything
                rw [if_pos hpr2] at h1
                by_cases hrt : r = t
                · subst hrt
                  rw [if_pos rfl] at h2
                  rw [ltF_succ_phi_phi _ hac, if_neg hpr, if_pos hpr2]
                  exact TR2 q (phi r u) hfq hfc (by omega) f' (by omega) h1 hBC
                · rw [if_neg hrt] at h2
                  by_cases hrt2 : ltF f' r t = true
                  · rw [if_pos hrt2] at h2
                    have hpt : ltF f' p t = true :=
                      TR1 p r t hfp hfr hft (by omega) f' (by omega) hpr2 hrt2
                    rw [ltF_succ_phi_phi _ hac, if_neg (ne_of_ltF hpt), if_pos hpt]
                    exact TR2 q (phi t u) hfq hfc (by omega) f' (by omega) h1 hBC
                  · rw [if_neg hrt2] at h2
                    -- α < γ and π < γ leaves α vs π open: comparability decides it
                    rcases ltF_comparable (f := f') hfp hft (by omega) with hc1 | hc1 | hc1
                    · rw [ltF_succ_phi_phi _ hac, if_neg (ne_of_ltF hc1), if_pos hc1]
                      exact TR2 q (phi t u) hfq hfc (by omega) f' (by omega) h1 hBC
                    · subst hc1
                      rw [ltF_succ_phi_phi _ hac, if_pos rfl]
                      simp only [Bool.or_eq_true, beq_iff_eq] at h2
                      rcases h2 with h3 | h3
                      · rw [← h3]; exact h1
                      · exact TR2 q u hfq hfu (by omega) f' (by omega) h1 h3
                    · have hpt : p ≠ t := by
                        intro hc; rw [hc, ltF_irrefl] at hc1; exact Bool.noConfusion hc1
                      have hnp : ltF f' p t = false := ltF_asymm hft hfp (by omega) hc1
                      rw [ltF_succ_phi_phi _ hac, if_neg hpt, if_neg (by simp [hnp])]
                      simp only [Bool.or_eq_true, beq_iff_eq] at h2
                      rcases h2 with h3 | h3
                      · rw [← h3]; simp [hAB]
                      · have h4 : ltF f' (phi p q) u = true :=
                          TR2 (phi p q) u hfa hfu (by omega) f' (by omega) hAB h3
                        simp [h4]
              · -- 13(iii) on the left: γ < α and φ̄αβ ≤ δ
                rw [if_neg hpr2] at h1
                have hrp : ltF f' r p = true := by
                  rcases ltF_comparable (f := f') hfp hfr (by omega) with h3 | h3 | h3
                  · exact absurd h3 hpr2
                  · exact absurd h3 hpr
                  · exact h3
                by_cases hrt : r = t
                · subst hrt
                  rw [if_pos rfl] at h2
                  rw [ltF_succ_phi_phi _ hac, if_neg hpr, if_neg hpr2]
                  simp only [Bool.or_eq_true, beq_iff_eq] at h1
                  rcases h1 with h3 | h3
                  · rw [h3]; simp [h2]
                  · have h4 : ltF f' (phi p q) u = true :=
                      TR1 (phi p q) s u hfa hfs hfu (by omega) f' (by omega) h3 h2
                    simp [h4]
                · rw [if_neg hrt] at h2
                  by_cases hrt2 : ltF f' r t = true
                  · -- φ̄αβ ≤ δ < φ̄πυ: no branch analysis needed at all
                    rw [if_pos hrt2] at h2
                    simp only [Bool.or_eq_true, beq_iff_eq] at h1
                    have h4 : ltF f' (phi p q) (phi t u) = true := by
                      rcases h1 with h3 | h3
                      · rw [h3]; exact h2
                      · exact TR1 (phi p q) s (phi t u) hfa hfs hfc
                          (by omega) f' (by omega) h3 h2
                    exact UP (phi p q) (phi t u) (by omega) h4
                  · rw [if_neg hrt2] at h2
                    have htr : ltF f' t r = true := by
                      rcases ltF_comparable (f := f') hfr hft (by omega) with h3 | h3 | h3
                      · exact absurd h3 hrt2
                      · exact absurd h3 hrt
                      · exact h3
                    have htp : ltF f' t p = true :=
                      TR1 t r p hft hfr hfp (by omega) f' (by omega) htr hrp
                    have hpt : p ≠ t := by
                      intro hc; rw [← hc, ltF_irrefl] at htp; exact Bool.noConfusion htp
                    have hnp : ltF f' p t = false := ltF_asymm hft hfp (by omega) htp
                    rw [ltF_succ_phi_phi _ hac, if_neg hpt, if_neg (by simp [hnp])]
                    simp only [Bool.or_eq_true, beq_iff_eq] at h2
                    rcases h2 with h3 | h3
                    · rw [← h3]; simp [hAB]
                    · have h4 : ltF f' (phi p q) u = true :=
                        TR2 (phi p q) u hfa hfu (by omega) f' (by omega) hAB h3
                      simp [h4]

/-- **TRANSITIVITY on the φ̄-fragment**, same fuel.  (STAGE 2 of the §6 map, in the
    stronger `inT`-free form.) -/
theorem trans_ltF {a b c : Term} (hfa : Frag a = true) (hfb : Frag b = true)
    (hfc : Frag c = true) {f : Nat} (hf : a.deg + b.deg + c.deg ≤ f)
    (h1 : ltF f a b = true) (h2 : ltF f b c = true) : ltF f a c = true :=
  trans_aux b.deg (a.deg + c.deg) a b c hfa hfb hfc (Nat.le_refl _) (Nat.le_refl _) f hf h1 h2

/-! ### §7.5 The user-facing statements, about `lt`

This is where §5 pays off: the three hypotheses of transitivity live at three
different default fuels, and `lt_eq_ltF` brings all of them to the single fuel
`a.deg + b.deg + c.deg` that `trans_ltF` wants. -/

theorem lt_irrefl (a : Term) : lt a a = false := ltF_irrefl _ a

/-- **ASYMMETRY.** -/
theorem lt_asymm {a b : Term} (hfa : Frag a = true) (hfb : Frag b = true)
    (h : lt a b = true) : lt b a = false := by
  rw [lt_eq_ltF a b (a.deg + b.deg) (Nat.le_refl _)] at h
  rw [lt_eq_ltF b a (a.deg + b.deg) (by omega)]
  exact ltF_asymm hfa hfb (Nat.le_refl _) h

/-- **COMPARABILITY.** -/
theorem lt_comparable {a b : Term} (hfa : Frag a = true) (hfb : Frag b = true) :
    lt a b = true ∨ a = b ∨ lt b a = true := by
  rw [lt_eq_ltF a b (a.deg + b.deg) (Nat.le_refl _),
      lt_eq_ltF b a (a.deg + b.deg) (by omega)]
  exact ltF_comparable hfa hfb (Nat.le_refl _)

/-- **TRANSITIVITY** — the keystone.  Three different default fuels, unified by §5. -/
theorem lt_trans {a b c : Term} (hfa : Frag a = true) (hfb : Frag b = true)
    (hfc : Frag c = true) (h1 : lt a b = true) (h2 : lt b c = true) : lt a c = true := by
  have da := deg_pos a; have db := deg_pos b; have dc := deg_pos c
  rw [lt_eq_ltF a b (a.deg + b.deg + c.deg) (by omega)] at h1
  rw [lt_eq_ltF b c (a.deg + b.deg + c.deg) (by omega)] at h2
  rw [lt_eq_ltF a c (a.deg + b.deg + c.deg) (by omega)]
  exact trans_ltF hfa hfb hfc (Nat.le_refl _) h1 h2

/-- **The fragment order is a strict LINEAR order**: exactly one of `<`, `=`, `>`. -/
theorem lt_trichotomy {a b : Term} (hfa : Frag a = true) (hfb : Frag b = true) :
    (lt a b = true ∧ a ≠ b ∧ lt b a = false)
  ∨ (lt a b = false ∧ a = b ∧ lt b a = false)
  ∨ (lt a b = false ∧ a ≠ b ∧ lt b a = true) := by
  rcases lt_comparable hfa hfb with h | h | h
  · exact Or.inl ⟨h, ne_of_ltF h, lt_asymm hfa hfb h⟩
  · subst h; exact Or.inr (Or.inl ⟨lt_irrefl a, rfl, lt_irrefl a⟩)
  · refine Or.inr (Or.inr ⟨lt_asymm hfb hfa h, ?_, h⟩)
    intro hc; rw [hc, lt_irrefl] at h; exact Bool.noConfusion h

/-! The `≤` forms.  `Evidence/Cert.lean` states almost every order fact with `le`
    (the classification lemmas produce `le s (fs n)`), so these are the shapes its
    proofs will actually apply. -/

theorem lt_of_le_of_lt {a b c : Term} (hfa : Frag a = true) (hfb : Frag b = true)
    (hfc : Frag c = true) (h1 : le a b = true) (h2 : lt b c = true) : lt a c = true := by
  simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with rfl | h1
  · exact h2
  · exact lt_trans hfa hfb hfc h1 h2

theorem lt_of_lt_of_le {a b c : Term} (hfa : Frag a = true) (hfb : Frag b = true)
    (hfc : Frag c = true) (h1 : lt a b = true) (h2 : le b c = true) : lt a c = true := by
  simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at h2
  rcases h2 with rfl | h2
  · exact h1
  · exact lt_trans hfa hfb hfc h1 h2

/-! The two INVERSION lemmas — the "analytic direction" the scope note at the head
    of this file listed as missing.  They turn a NEGATIVE order fact into a
    positive one, which is what a classification proof ("everything below `t` has
    shape …") needs and what no amount of computing `ltF` can supply.  Both are
    immediate from comparability, and both are false without `Frag`
    (`lt_comparable_needs_frag`). -/

theorem le_of_not_lt {a b : Term} (hfa : Frag a = true) (hfb : Frag b = true)
    (h : lt a b = false) : le b a = true := by
  simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq]
  rcases lt_comparable hfa hfb with h1 | h1 | h1
  · rw [h1] at h; exact Bool.noConfusion h
  · exact Or.inl h1.symm
  · exact Or.inr h1

theorem lt_of_not_le {a b : Term} (hfa : Frag a = true) (hfb : Frag b = true)
    (h : le a b = false) : lt b a = true := by
  simp only [TM.Term.le, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  rcases lt_comparable hfa hfb with h1 | h1 | h1
  · rw [h1] at h; exact absurd h.2 (by simp)
  · exact absurd h1 h.1
  · exact h1

theorem le_trans {a b c : Term} (hfa : Frag a = true) (hfb : Frag b = true)
    (hfc : Frag c = true) (h1 : le a b = true) (h2 : le b c = true) : le a c = true := by
  simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at h1 h2 ⊢
  rcases h1 with rfl | h1
  · exact h2
  · rcases h2 with rfl | h2
    · exact Or.inr h1
    · exact Or.inr (lt_trans hfa hfb hfc h1 h2)

/-! ### §7.6 The fragment is closed under the operations `Evidence/Cert.lean` uses

Without these the client would have to re-derive `Frag` for every term it builds.
`pwv e = ofList (e.map pw)` and `pw k = φ̄0(ofNat k)`, so `frag_ofList` +
`frag_mk_phi` + `frag_ofNat` cover the whole CNF layer of Cert.lean. -/

theorem frag_mk_add {a b : Term} (ha : Frag a = true) (hb : Frag b = true) :
    Frag (add a b) = true := by
  show (Frag a && Frag b) = true; rw [ha, hb]; rfl

theorem frag_mk_phi {a b : Term} (ha : Frag a = true) (hb : Frag b = true) :
    Frag (phi a b) = true := by
  show (Frag a && Frag b) = true; rw [ha, hb]; rfl

/-- `ω^α = φ̄0α` stays in the fragment. -/
theorem frag_omegaPow {a : Term} (ha : Frag a = true) : Frag (phi zero a) = true :=
  frag_mk_phi rfl ha

theorem frag_toList : ∀ (t : Term), Frag t = true → ∀ x ∈ toList t, Frag x = true
  | zero, _, x, hx => by simp [toList] at hx
  | M, h, _, _ => by simp [Frag] at h
  | omg _, h, _, _ => by simp [Frag] at h
  | psi _ _, h, _, _ => by simp [Frag] at h
  | Z _, h, _, _ => by simp [Frag] at h
  | phi a b, h, x, hx => by
    have he : toList (phi a b) = [phi a b] := rfl
    rw [he] at hx; simp at hx; subst hx; exact h
  | add a b, h, x, hx => by
    have hab := frag_add h
    have he : toList (add a b) = a :: toList b := rfl
    rw [he] at hx
    rcases List.mem_cons.mp hx with rfl | hx2
    · exact hab.1
    · exact frag_toList b hab.2 x hx2

theorem frag_ofList : ∀ (l : List Term), (∀ x ∈ l, Frag x = true) → Frag (ofList l) = true
  | [], _ => rfl
  | [a], h => h a (by simp)
  | a :: b :: t, h => by
    show (Frag a && Frag (ofList (b :: t))) = true
    rw [h a (by simp), frag_ofList (b :: t) (fun x hx => h x (List.mem_cons_of_mem a hx))]
    rfl

theorem frag_plus {s t : Term} (hs : Frag s = true) (ht : Frag t = true) :
    Frag (plus s t) = true := by
  show Frag (match toList t with
             | [] => s
             | b1 :: _ => ofList ((toList s).filter (fun a => le b1 a) ++ toList t)) = true
  cases hl : toList t with
  | nil => exact hs
  | cons b1 rest =>
    apply frag_ofList
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact frag_toList s hs x (List.mem_filter.mp hx).1
    · exact frag_toList t ht x (by rw [hl]; exact hx)

theorem frag_one : Frag one = true := rfl
theorem frag_omega : Frag omega = true := rfl

theorem frag_ofNat : ∀ n, Frag (ofNat n) = true
  | 0 => rfl
  | n + 1 => frag_plus (frag_ofNat n) rfl

/-- The whole CNF layer of `Evidence/Cert.lean` §5.7 is in the fragment.  That
    file's `pw k` is `φ̄0(ofNat k)` and its `pwv e` is `ofList (e.map pw)`, so this
    is literally `Frag (pwv e) = true` — stated here without those definitions,
    because the import goes the other way.  Together with §7.5 it gives the
    certificate lane transitivity of its exponent-list order for free. -/
theorem frag_cnf (e : List Nat) :
    Frag (ofList (e.map (fun k => phi zero (ofNat k)))) = true := by
  apply frag_ofList
  intro x hx
  rcases List.mem_map.mp hx with ⟨k, _, rfl⟩
  exact frag_omegaPow (frag_ofNat k)

/-! ### §7.7 Evidence that §7 has content, and two discriminating mutants

The doctrine of `plan/README.md`'s 較正事故 section: a theorem whose hypotheses are
never tested is a theorem about nothing.  Both hypotheses of `trans_ltF` are
tested below by an explicit counterexample to the statement with that hypothesis
removed.  (These `#guard`s are a sample of an exhaustive `#eval` sweep run before
the proofs were written: all 275 fragment terms of degree ≤ 9 for asymmetry and
comparability, all 51 of degree ≤ 7 for transitivity, each with and without the
`inT` filter.) -/

private def fragSample : List Term :=
  [zero, one, omega, ofNat 2, ofNat 3, phi one zero, phi zero (phi one zero),
   add omega one, add (phi one zero) one, phi one one]

#guard fragSample.all (fun t => Frag t)
#guard fragSample.all (fun s => fragSample.all (fun t => !(lt s t && lt t s)))
#guard fragSample.all (fun s => fragSample.all (fun t => lt s t || s == t || lt t s))
#guard fragSample.all (fun s => fragSample.all (fun t => fragSample.all (fun u =>
         !(lt s t && lt t u) || lt s u)))

/-! MUTANT 1 — DROP THE FUEL HYPOTHESIS of `trans_ltF`.  It is load-bearing, not
decoration: at fuel 2 this triple violates transitivity outright.  The hypothesis
`a.deg + b.deg + c.deg ≤ f` demands `f ≥ 15` here, and `lt` (whose default fuel is
`2*(deg+deg)+8`) gets the right answer. -/

#guard ltF 2 one (phi one zero) == true
#guard ltF 2 (phi one zero) (add (phi one zero) zero) == true
#guard ltF 2 one (add (phi one zero) zero) == false
#guard (one : Term).deg + (phi one zero).deg + (add (phi one zero) zero).deg == 15
#guard lt one (add (phi one zero) zero) == true

/-! MUTANT 2 — DROP `Frag`.  Outside the fragment the raw order is not even
comparable, so `ltF_comparable` (and with it the 13(iii) step of `ltF_asymm`)
genuinely needs the hypothesis: `ψ_M M` and `ψ_(ψ_M M) M` are distinct and neither
is below the other.  Note both fail `inT` — an exhaustive sweep of all 3042 terms
of degree ≤ 6 over ALL seven constructors found 792 incomparable pairs, and ZERO
of them among the 171 that satisfy `inT`.  That is the evidence that STAGE 3 (the
`ψ`/`Z` clauses, §6's item 3) is true but will need `inT`, exactly where the
fragment did not. -/

#guard lt (psi M M) (psi (psi M M) M) == false
#guard lt (psi (psi M M) M) (psi M M) == false
#guard ((psi M M : Term) == psi (psi M M) M) == false
#guard inT (psi M M) == false

/-! The same two mutants as THEOREMS, so that the kernel — not the evaluator —
certifies that neither hypothesis can be deleted.  Each is literally the statement
of the corresponding theorem of §7.4/§7.5 with one hypothesis removed. -/

/-- Deleting the fuel hypothesis from `trans_ltF` makes it FALSE. -/
theorem trans_ltF_needs_fuel :
    ¬ (∀ (a b c : Term), Frag a = true → Frag b = true → Frag c = true →
        ∀ f, ltF f a b = true → ltF f b c = true → ltF f a c = true) := by
  intro h
  have hbad := h one (phi one zero) (add (phi one zero) zero) rfl rfl rfl 2 rfl rfl
  have hc : ltF 2 one (add (phi one zero) zero) = false := rfl
  rw [hc] at hbad
  exact Bool.noConfusion hbad

/-- Deleting `Frag` from `lt_comparable` makes it FALSE. -/
theorem lt_comparable_needs_frag :
    ¬ (∀ (a b : Term), lt a b = true ∨ a = b ∨ lt b a = true) := by
  intro h
  rcases h (psi M M) (psi (psi M M) M) with h1 | h1 | h1
  · exact Bool.noConfusion h1
  · exact absurd h1 (by decide)
  · exact Bool.noConfusion h1

/-! ## §9 The segment below ε₀ — the ω-towers and their cofinality
    (STAGE 1 of the ε₀ certificate, certificate lane 2026-08-09)

WHY THIS SECTION EXISTS.  The row `(0,0)(1,1)` of the table is ε₀, and its BM4
expansions are the ω-TOWERS:

    (0,0)(1,1)[n] = (0,0)(1,0)(2,0)…(n,0)   with value   1, ω, ω^ω, ω^(ω^ω), …

Certifying that row with the `lim` constructor of `Evidence/Cert.lean` needs three
order facts about the towers: they lie below ε₀ (`lt_tower_eps0`), they increase
(`lt_tower_step`), and they are COFINAL among the terms of 𝔗(M) below ε₀
(`cof_eps0`).  The first two are short inductions; the third is the whole content
of this section and is the clause on which every attempt at the ε₀ row has to
stand or fall.

THE SHAPE ANALYSIS.  Clause 2.3.13 decides `s < φ̄10` by the head of `s`:

    0 < ε₀                            (2.3.1)
    ⊕(α₁,…) < ε₀   ⟺  α₁ < ε₀        (2.3.10 — the head alone)
    φ̄γδ < ε₀       ⟺  γ < 1 ∧ δ < ε₀  (13(i); 13(ii) and 13(iii) both give `false`)
    M, ω̄^·, ψ, Z   are never < ε₀     (2.3.2/2.3.3/2.3.5)

so a term below ε₀ is a CNF term — and the tower that overtakes it can be read
straight off its syntax.  `ht` below is that reading: `ht 0 = 0`,
`ht (⊕ a b) = ht a + 1`, `ht (φ̄ a b) = ht b + 1`.  The bound `s < tower (ht s)`
then needs NO transitivity, NO comparability and no `Frag` hypothesis: every
recursive step of the proof is a single clause of 2.3 applied to strictly smaller
subterms.  (This is why §9 is much shorter than §7 although it proves a statement
about all of 𝔗(M): §7 has to compare two arbitrary terms, §9 only has to compare
an arbitrary term with a tower.)

WHY `inT` IS UNAVOIDABLE HERE — the exact opposite of §7.  "γ < 1" in 13(i) is
decided by 2.3.10 on the HEAD of a sum, so the ill-formed `γ = 0 ⊕ M` passes it
(`0 < 1`), and the junk term `φ̄(0 ⊕ M)0` is put below ε₀ while 13(iii) sends every
comparison with a tower down the tower's exponent and never fires.  So that junk
term is below ε₀ and above EVERY tower: without a formation condition the
cofinality clause is FALSE, not merely unprovable.  `inT` kills it at
`isAP 0 = false` (2.1(iii)).  This is the ε₀-side reading of the DEFINITION CHANGE
recorded in the header of `Evidence/Cert.lean`, and `cof_eps0_needs_inT` at the end
of the section is its kernel-checked mutant. -/

/-- ε₀ = φ̄10.  (`φ̄` is the RAW Veblen function of [R91] 2.1(v), so `φ̄10 = φ₁(0)`;
    `phiNF` would return the same term here — `0` is not `SC` and has no fixed-point
    shape, so 2.6(vi) falls through to its default line.) -/
def eps0 : Term := phi one zero

/-- The ω-tower `ω↑↑n`: `tower 0 = 1`, `tower (n+1) = ω^(tower n) = φ̄0(tower n)`.
    These are exactly the values of the expansions of `(0,0)(1,1)`. -/
def tower : Nat → Term
  | 0 => one
  | n + 1 => phi zero (tower n)

/-- The tower height of a term: the index of a tower that overtakes it.  On the
    shapes 2.3 puts below ε₀ it counts the `⊕`/`φ̄` nesting along the head spine;
    on every other shape it is junk (and `tower_bound` never reaches it). -/
def ht : Term → Nat
  | zero => 0
  | add a _ => ht a + 1
  | phi _ b => ht b + 1
  | _ => 0

/-! ### §9.1 Elementary facts about the towers -/

theorem deg_tower : ∀ n, (tower n).deg = 2 * n + 3
  | 0 => rfl
  | n + 1 => by
    have ih := deg_tower n
    show 1 + 1 + (tower n).deg = 2 * (n + 1) + 3
    omega

theorem ht_tower : ∀ n, ht (tower n) = n + 1
  | 0 => rfl
  | n + 1 => by
    have ih := ht_tower n
    show ht (tower n) + 1 = n + 1 + 1
    omega

theorem frag_tower : ∀ n, Frag (tower n) = true
  | 0 => rfl
  | n + 1 => by
    show (Frag zero && Frag (tower n)) = true
    rw [frag_tower n]; rfl

theorem tower_ne_zero : ∀ n, tower n ≠ zero
  | 0 => by intro h; exact Term.noConfusion h
  | n + 1 => by intro h; exact Term.noConfusion h

/-- The default fuel of `lt` is above the degree bound, so a sufficiently fuelled
    `ltF` computation settles `lt`.  (`§5`'s `ltF_mono`, packaged.) -/
private theorem lt_of_ltF_deg {s t : Term} {f : Nat} (hf : s.deg + t.deg ≤ f)
    (h : ltF f s t = true) : lt s t = true := by
  show ltF (fuelOf s t) s t = true
  exact ltF_mono hf (by show s.deg + t.deg ≤ 2 * (s.deg + t.deg) + 8; omega) h

/-- **The towers increase.** -/
theorem ltF_tower_step : ∀ (n f : Nat), (tower n).deg + (tower (n + 1)).deg ≤ f →
    ltF f (tower n) (tower (n + 1)) = true := by
  intro n
  induction n with
  | zero =>
    intro f hf
    rw [deg_tower 0, deg_tower 1] at hf
    cases f with
    | zero => omega
    | succ g =>
      show ltF (g + 1) (phi zero zero) (phi zero one) = true
      rw [ltF_succ_phi_phi g (by decide), if_pos rfl]
      exact ltF_left_zero (by omega) (by decide)
  | succ n ih =>
    intro f hf
    rw [deg_tower (n + 1), deg_tower (n + 1 + 1)] at hf
    cases f with
    | zero => omega
    | succ g =>
      have hih : ltF g (tower n) (tower (n + 1)) = true :=
        ih g (by rw [deg_tower n, deg_tower (n + 1)]; omega)
      have hne : tower n ≠ tower (n + 1) := ne_of_ltF hih
      show ltF (g + 1) (phi zero (tower n)) (phi zero (tower (n + 1))) = true
      rw [ltF_succ_phi_phi g (by intro h; injection h with h1 h2; exact hne h2), if_pos rfl]
      exact hih

theorem lt_tower_step (n : Nat) : lt (tower n) (tower (n + 1)) = true :=
  lt_of_ltF_deg (Nat.le_refl _) (ltF_tower_step n _ (Nat.le_refl _))

/-- **Every tower is below ε₀.** -/
theorem ltF_tower_eps0 : ∀ (n f : Nat), (tower n).deg + eps0.deg ≤ f →
    ltF f (tower n) eps0 = true := by
  intro n
  induction n with
  | zero =>
    intro f hf
    rw [deg_tower 0] at hf
    cases f with
    | zero => omega
    | succ g =>
      show ltF (g + 1) (phi zero zero) (phi one zero) = true
      rw [ltF_succ_phi_phi g (by decide), if_neg (by decide),
        if_pos (show ltF g zero one = true from ltF_left_zero (by omega) (by decide))]
      exact ltF_left_zero (by omega) (by decide)
  | succ n ih =>
    intro f hf
    rw [deg_tower (n + 1)] at hf
    cases f with
    | zero => omega
    | succ g =>
      show ltF (g + 1) (phi zero (tower n)) (phi one zero) = true
      rw [ltF_succ_phi_phi g (by intro h; injection h with h1 h2; exact absurd h1 (by decide)),
        if_neg (by decide),
        if_pos (show ltF g zero one = true from ltF_left_zero (by omega) (by decide))]
      exact ih g (by rw [deg_tower n]; omega)

theorem lt_tower_eps0 (n : Nat) : lt (tower n) eps0 = true :=
  lt_of_ltF_deg (Nat.le_refl _) (ltF_tower_eps0 n _ (Nat.le_refl _))

/-! ### §9.2 The formation conditions, destructured

Only the two conjuncts the classification uses; `Evidence/Cert.lean` has the same
two but `private`, and it imports this file. -/

theorem inT_add {a b : Term} (h : inT (add a b) = true) :
    a.isAP = true ∧ inT a = true ∧ inT b = true := by
  simp only [inT, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

theorem inT_phi {a b : Term} (h : inT (phi a b) = true) : inT a = true ∧ inT b = true := by
  simp only [inT, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2⟩

/-! ### §9.3 Nothing but `0` is below `1` (for terms of 𝔗(M))

The `inT` hypothesis is the whole point: `0 ⊕ M` is below `1` for the decision
procedure (2.3.10 reads the head `0` and stops), and that junk term is exactly
what would break §9.4. -/

/-- A `ψ` or a `Z` is never below `1`: 2.3.4 asks whether it is `≤ 0`. -/
private theorem ltF_sc_one : ∀ (f : Nat) (s : Term), s.isSC = true → s ≠ M →
    ltF f s one = false := by
  intro f s hsc hM
  cases f with
  | zero => rfl
  | succ g =>
    cases s with
    | M => exact absurd rfl hM
    | psi k a =>
      show ((psi k a == zero) || (psi k a == zero) || ltF g (psi k a) zero
              || ltF g (psi k a) zero) = false
      rw [ltF_right_zero]; rfl
    | Z a =>
      show ((Z a == zero) || (Z a == zero) || ltF g (Z a) zero || ltF g (Z a) zero) = false
      rw [ltF_right_zero]; rfl
    | zero => exact Bool.noConfusion hsc
    | add a b => exact Bool.noConfusion hsc
    | omg a => exact Bool.noConfusion hsc
    | phi a b => exact Bool.noConfusion hsc

/-- **Below `1` there is only `0`** — on the terms of 𝔗(M). -/
theorem below_one : ∀ (s : Term), inT s = true → ∀ (f : Nat), ltF f s one = true → s = zero := by
  intro s
  induction s with
  | zero => intro _ _ _; rfl
  | M =>
    intro _ f h
    cases f with
    | zero => exact Bool.noConfusion h
    | succ g => exact Bool.noConfusion h
  | omg a _ =>
    intro _ f h
    cases f with
    | zero => exact Bool.noConfusion h
    | succ g => exact Bool.noConfusion h
  | psi k a _ _ =>
    intro _ f h
    rw [ltF_sc_one f (psi k a) rfl (by intro hc; exact Term.noConfusion hc)] at h
    exact Bool.noConfusion h
  | Z a _ =>
    intro _ f h
    rw [ltF_sc_one f (Z a) rfl (by intro hc; exact Term.noConfusion hc)] at h
    exact Bool.noConfusion h
  | add a b iha _ =>
    intro hin f h
    obtain ⟨hap, hina, _⟩ := inT_add hin
    cases f with
    | zero => exact Bool.noConfusion h
    | succ g =>
      have hz : a = zero := iha hina g h
      rw [hz] at hap
      exact Bool.noConfusion hap
  | phi c d _ _ =>
    intro _ f h
    cases f with
    | zero => exact Bool.noConfusion h
    | succ g =>
      by_cases hone : phi c d = one
      · rw [hone] at h
        rw [ltF_irrefl] at h
        exact Bool.noConfusion h
      · have h : ltF (g + 1) (phi c d) (phi zero zero) = true := h
        rw [ltF_succ_phi_phi g hone] at h
        by_cases hc : c = zero
        · rw [if_pos hc, ltF_right_zero] at h
          exact Bool.noConfusion h
        · rw [if_neg hc, if_neg (by rw [ltF_right_zero]; exact Bool.noConfusion),
            ltF_right_zero] at h
          exact Bool.noConfusion h

/-! ### §9.4 THE COFINALITY BOUND

`s < ε₀` and `s ∈ 𝔗(M)` imply `s < tower (ht s)`.  One structural induction; each
case is one clause of 2.3.  Note the `φ̄` case is where `below_one` is spent, and
the `⊕` case is where the head-only clause 2.3.10 makes the tail irrelevant. -/

private theorem tower_bound : ∀ (s : Term), inT s = true → ∀ (f m : Nat),
    ltF f s eps0 = true → ht s ≤ m → lt s (tower m) = true := by
  intro s
  induction s with
  | zero =>
    intro _ f m _ _
    show ltF (fuelOf zero (tower m)) zero (tower m) = true
    exact ltF_left_zero (by show 1 ≤ 2 * ((zero : Term).deg + (tower m).deg) + 8; omega)
      (tower_ne_zero m)
  | M =>
    intro _ f m h _
    cases f with
    | zero => exact Bool.noConfusion h
    | succ g => exact Bool.noConfusion h
  | omg a _ =>
    intro _ f m h _
    cases f with
    | zero => exact Bool.noConfusion h
    | succ g => exact Bool.noConfusion h
  | psi k a _ _ =>
    intro _ f m h _
    cases f with
    | zero => exact Bool.noConfusion h
    | succ g =>
      rw [show ltF (g + 1) (psi k a) eps0
            = ((psi k a == one) || (psi k a == zero) || ltF g (psi k a) one
                || ltF g (psi k a) zero) from rfl,
        ltF_sc_one g (psi k a) rfl (by intro hc; exact Term.noConfusion hc),
        ltF_right_zero] at h
      exact Bool.noConfusion h
  | Z a _ =>
    intro _ f m h _
    cases f with
    | zero => exact Bool.noConfusion h
    | succ g =>
      rw [show ltF (g + 1) (Z a) eps0
            = ((Z a == one) || (Z a == zero) || ltF g (Z a) one || ltF g (Z a) zero) from rfl,
        ltF_sc_one g (Z a) rfl (by intro hc; exact Term.noConfusion hc),
        ltF_right_zero] at h
      exact Bool.noConfusion h
  | add a b iha _ =>
    intro hin f m h hm
    obtain ⟨_, hina, _⟩ := inT_add hin
    cases f with
    | zero => exact Bool.noConfusion h
    | succ g =>
      cases m with
      | zero => exact absurd hm (by show ¬ (ht a + 1 ≤ 0); omega)
      | succ m' =>
        have h : ltF (g + 1) (add a b) (phi one zero) = true := h
        rw [ltF_succ_add_phi g a b one zero] at h
        have hm' : ht a + 1 ≤ m' + 1 := hm
        have hlt : lt a (tower (m' + 1)) = true :=
          iha hina g (m' + 1) h (by omega)
        refine lt_of_ltF_deg (f := a.deg + b.deg + (tower (m' + 1)).deg + 1)
          (by show 1 + a.deg + b.deg + (tower (m' + 1)).deg
                ≤ a.deg + b.deg + (tower (m' + 1)).deg + 1; omega) ?_
        show ltF (a.deg + b.deg + (tower (m' + 1)).deg + 1) (add a b) (phi zero (tower m')) = true
        rw [ltF_succ_add_phi]
        exact ltF_mono (by show a.deg + (tower (m' + 1)).deg
                              ≤ 2 * (a.deg + (tower (m' + 1)).deg) + 8; omega)
          (by show a.deg + (tower (m' + 1)).deg ≤ a.deg + b.deg + (tower (m' + 1)).deg;
              omega) hlt
  | phi c d _ ihd =>
    intro hin f m h hm
    obtain ⟨hinc, hind⟩ := inT_phi hin
    cases f with
    | zero => exact Bool.noConfusion h
    | succ g =>
      by_cases he : phi c d = eps0
      · rw [he, ltF_irrefl] at h; exact Bool.noConfusion h
      have hh : ltF (g + 1) (phi c d) (phi one zero) = true := h
      rw [ltF_succ_phi_phi g he] at hh
      by_cases hc1 : c = one
      · rw [if_pos hc1, ltF_right_zero] at hh; exact Bool.noConfusion hh
      rw [if_neg hc1] at hh
      by_cases hc0 : ltF g c one = true
      · rw [if_pos hc0] at hh
        have hcz : c = zero := below_one c hinc g hc0
        subst hcz
        cases m with
        | zero => exact absurd hm (by show ¬ (ht d + 1 ≤ 0); omega)
        | succ m' =>
          have hm' : ht d + 1 ≤ m' + 1 := hm
          have hmd : ht d ≤ m' := by omega
          have hlt : lt d (tower m') = true := ihd hind g m' hh hmd
          have hdne : d ≠ tower m' := by
            intro hc
            rw [hc, ht_tower] at hmd
            omega
          refine lt_of_ltF_deg (f := d.deg + (tower m').deg + 5)
            (by show 1 + 1 + d.deg + (1 + 1 + (tower m').deg) ≤ d.deg + (tower m').deg + 5;
                omega) ?_
          show ltF (d.deg + (tower m').deg + 5) (phi zero d) (phi zero (tower m')) = true
          rw [show d.deg + (tower m').deg + 5 = (d.deg + (tower m').deg + 4) + 1 from rfl,
            ltF_succ_phi_phi _ (by intro hcc; injection hcc with h1 h2; exact hdne h2), if_pos rfl]
          exact ltF_mono (by show d.deg + (tower m').deg ≤ 2 * (d.deg + (tower m').deg) + 8; omega)
            (by omega) hlt
      · rw [if_neg hc0, ltF_right_zero] at hh
        simp only [Bool.or_false] at hh
        exact Bool.noConfusion hh

/-- **THE COFINALITY CLAUSE FOR ε₀.**  Every term of 𝔗(M) below ε₀ is overtaken by
    a tower — with the overtaking index read off the term's own syntax.  This is
    the premise of `Certified.lim` that the row `(0,0)(1,1)` needs, and the only
    one of the five that is not a computation. -/
theorem cof_eps0 (s : Term) (hs : inT s = true) (h : lt s eps0 = true) :
    ∃ n, le s (tower n) = true := by
  refine ⟨ht s, ?_⟩
  show ((s == tower (ht s)) || lt s (tower (ht s))) = true
  rw [tower_bound s hs (fuelOf s eps0) (ht s) h (Nat.le_refl _)]
  exact Bool.or_true _

/-! ### §9.5 Evidence, and the mutant that shows `inT` is load-bearing

`φ̄(0 ⊕ M)0` is below ε₀ and above every tower.  It is not a term of 𝔗(M) — its
`0 ⊕ M` fails 2.1(iii) at `isAP 0 = false` — so `cof_eps0` is untouched; but delete
`inT` from the statement and it becomes FALSE, which is what
`cof_eps0_needs_inT` certifies in the kernel. -/

/-- The junk term of the mutant. -/
private def junk : Term := phi (add zero M) zero

#guard lt junk eps0 = true
#guard inT junk = false
#guard inT (add zero M) = false
#guard (List.range 12).all (fun n => le junk (tower n) == false)
#guard (List.range 8).all (fun n => lt (tower n) eps0 && lt (tower n) (tower (n + 1)))
#guard (List.range 8).all (fun n => ht (tower n) == n + 1)

private theorem ltF_junk_tower : ∀ (n f : Nat), ltF f junk (tower n) = false := by
  intro n
  induction n with
  | zero =>
    intro f
    cases f with
    | zero => rfl
    | succ g =>
      show (if (junk == one) = true then false
            else if ((add zero M : Term) == zero) = true then ltF g zero zero
            else if ltF g (add zero M) zero = true then ltF g zero one
            else ((junk == zero) || ltF g junk zero)) = false
      rw [if_neg (by intro hc; exact Bool.noConfusion hc), if_neg (by intro hc; exact Bool.noConfusion hc), ltF_right_zero]
      simp only [Bool.false_eq_true, if_false]
      rw [ltF_right_zero]
      rfl
  | succ n ih =>
    intro f
    cases f with
    | zero => rfl
    | succ g =>
      show (if (junk == tower (n + 1)) = true then false
            else if ((add zero M : Term) == zero) = true then ltF g zero (tower n)
            else if ltF g (add zero M) zero = true then ltF g zero (tower (n + 1))
            else ((junk == tower n) || ltF g junk (tower n))) = false
      rw [if_neg (by intro hc; exact Bool.noConfusion hc),
        if_neg (by intro hc; exact Bool.noConfusion hc), ltF_right_zero]
      simp only [Bool.false_eq_true, if_false]
      rw [ih g,
        show ((junk == tower n) : Bool) = false from by cases n <;> rfl]
      rfl

/-- **The mutant.**  `cof_eps0` with the formation condition deleted is FALSE. -/
theorem cof_eps0_needs_inT :
    ¬ (∀ s, lt s eps0 = true → ∃ n, le s (tower n) = true) := by
  intro hcof
  obtain ⟨n, hn⟩ := hcof junk (by decide)
  rw [show le junk (tower n) = ((junk == tower n) || lt junk (tower n)) from rfl,
    show lt junk (tower n) = false from ltF_junk_tower n _,
    show ((junk == tower n) : Bool) = false from by cases n <;> rfl] at hn
  exact Bool.noConfusion hn

/-! ## §10 The CNF segment below ε₀ is WELL-FOUNDED — the Gentzen argument
    (STAGE 2a of the ε₀ certificate, certificate lane 2026-08-09)

WHAT THIS IS FOR.  §9 settles the COFINALITY clause of the ε₀ row.  The other
open clause is `∀ n, Certified ((0,0)(1,1)[n]) (tower n)`, and the expansion
closure of the tower matrices is the WHOLE standard one-row region — every CNF
term below ε₀ — so the certificate family has to be built by a recursion along the
expansion, i.e. along the term order.  Nothing in §1–§4 supplies that: `LexLt` is
a fixed-length vector order, and below ε₀ the exponents are unbounded terms.  This
section supplies the missing recursion principle in the only form that exists,
the classical structural (Gentzen/Schütte) argument.

THE ORDER IS NOT WELL-FOUNDED WITHOUT THE DESCENDING CONDITION.  This is not a
technicality: clause 2.3.16 compares two sums along the spine, so with 2.3.10
reading only the head one gets the genuine infinite descent

    1 ⊕ ω  >  1 ⊕ 1 ⊕ ω  >  1 ⊕ 1 ⊕ 1 ⊕ ω  >  …

(each step: the heads `1` agree, so the tails are compared, and `1 ⊕ ω < ω`
because 2.3.10 sees only the head `1`).  Every one of those terms is in `Frag`.
So `Frag` alone — the hypothesis of §7 — is NOT enough for well-foundedness, and
`CN` below carries 2.1(iii)'s descending condition as well.  `cn_desc_needed`
keeps the descent as a kernel-checked mutant.

THE ARGUMENT.  `RC x y := CN x ∧ x < y`.  The theorem is `∀ t, CN t → Acc RC t`,
and the whole content is the single outer induction

    ∀ a, Acc RC a → Acc RC (ω^a) ∧ ∀ v, CN v → Acc RC v → Acc RC (ω^a ⊕ v)

whose step first proves, by a STRUCTURAL induction on `x`,

    C : ∀ x, CN x → x < ω^a → Acc RC x

(the `⊕` case of `C` is where §7's `lt_of_le_of_lt` — hence `lt_trans`, hence THE
KEYSTONE — is spent: the tail of a CNF sum is below `ω^a` because its head is `≤`
the head of the sum, which is `< ω^a`).  `Acc RC (ω^a)` is then literally `C`, and
the `⊕` half follows by an inner induction on `Acc v`.  The final theorem is a
recursion on the degree, because the `⊕` case needs the EXPONENT of the head, not
the head itself. -/

/-- `ω^·`-shape: the terms `φ̄0β`. -/
def isPow : Term → Bool
  | phi a _ => a == zero
  | _ => false

/-- The descending condition of 2.1(iii), read off the head of the tail: every
    component of `b` is `≤ a`.  `0` is excluded because a `⊕` has ≥ 2 components. -/
def hdLe (b a : Term) : Bool :=
  match b with
  | zero => false
  | add c _ => le c a
  | t => le t a

/-- **The Cantor normal forms below ε₀**: `0`, `ω^β = φ̄0β` with `β` in CNF, and
    formal sums of such with the components descending.  This is exactly `Frag`
    intersected with 2.1(iii)'s descending condition and `α = 0` in every `φ̄αβ`
    — i.e. the shapes §9 puts below ε₀, made honest. -/
def CN : Term → Bool
  | zero => true
  | phi a b => (a == zero) && CN b
  | add a b => isPow a && CN a && CN b && hdLe b a
  | _ => false

theorem cn_phi {a b : Term} (h : CN (phi a b) = true) : a = zero ∧ CN b = true := by
  simp only [CN, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem cn_add {a b : Term} (h : CN (add a b) = true) :
    isPow a = true ∧ CN a = true ∧ CN b = true ∧ hdLe b a = true := by
  simp only [CN, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem eq_pow_of_isPow : ∀ {a : Term}, isPow a = true → ∃ e, a = phi zero e
  | zero, h => Bool.noConfusion h
  | M, h => Bool.noConfusion h
  | add _ _, h => Bool.noConfusion h
  | omg _, h => Bool.noConfusion h
  | psi _ _, h => Bool.noConfusion h
  | Z _, h => Bool.noConfusion h
  | phi x y, h => ⟨y, by simp only [isPow, beq_iff_eq] at h; rw [h]⟩

theorem frag_of_cn : ∀ (t : Term), CN t = true → Frag t = true
  | zero, _ => rfl
  | M, h => Bool.noConfusion h
  | omg _, h => Bool.noConfusion h
  | psi _ _, h => Bool.noConfusion h
  | Z _, h => Bool.noConfusion h
  | phi a b, h => by
    obtain ⟨ha, hb⟩ := cn_phi h
    subst ha
    show (Frag zero && Frag b) = true
    rw [frag_of_cn b hb]
    rfl
  | add a b, h => by
    obtain ⟨_, ha, hb, _⟩ := cn_add h
    show (Frag a && Frag b) = true
    rw [frag_of_cn a ha, frag_of_cn b hb]
    rfl

/-! ### §10.1 The three clause bodies, at the DEFAULT fuel

§7.2 states them at `f + 1`; the Acc argument compares terms whose degrees are
unrelated, so it needs them for `lt` itself.  §5 is what makes that possible. -/

/-- 2.3.10 for `lt`: a sum is below a `φ̄` exactly when its head is. -/
theorem lt_add_phi (a b p q : Term) : lt (add a b) (phi p q) = lt a (phi p q) := by
  have hb := deg_pos b
  show ltF (fuelOf (add a b) (phi p q)) (add a b) (phi p q) = _
  rw [show fuelOf (add a b) (phi p q)
        = (2 * ((add a b).deg + (phi p q).deg) + 7) + 1 from by
      show 2 * ((add a b).deg + (phi p q).deg) + 8 = _; omega,
    ltF_succ_add_phi]
  exact (lt_eq_ltF a (phi p q) _
    (by show a.deg + (phi p q).deg ≤ 2 * ((1 + a.deg + b.deg) + (phi p q).deg) + 7; omega)).symm

/-- 2.3.11 for `lt`: a `φ̄` is below a sum exactly when it is `≤` the head. -/
theorem lt_phi_add (p q u v : Term) : lt (phi p q) (add u v) = le (phi p q) u := by
  have hv := deg_pos v
  show ltF (fuelOf (phi p q) (add u v)) (phi p q) (add u v) = _
  rw [show fuelOf (phi p q) (add u v)
        = (2 * ((phi p q).deg + (add u v).deg) + 7) + 1 from by
      show 2 * ((phi p q).deg + (add u v).deg) + 8 = _; omega,
    ltF_succ_phi_add]
  rw [show ltF (2 * ((phi p q).deg + (add u v).deg) + 7) (phi p q) u = lt (phi p q) u from
    (lt_eq_ltF (phi p q) u _
      (by show (phi p q).deg + u.deg ≤ 2 * ((phi p q).deg + (1 + u.deg + v.deg)) + 7;
          omega)).symm]
  rfl

/-- 2.3.16 for `lt`. -/
theorem lt_add_add {c d u v : Term} (h : add c d ≠ add u v) :
    lt (add c d) (add u v) = (if c = u then lt d v else lt c u) := by
  have hc := deg_pos c; have hd := deg_pos d; have hu := deg_pos u; have hv := deg_pos v
  show ltF (fuelOf (add c d) (add u v)) (add c d) (add u v) = _
  rw [show fuelOf (add c d) (add u v)
        = (2 * ((add c d).deg + (add u v).deg) + 7) + 1 from by
      show 2 * ((add c d).deg + (add u v).deg) + 8 = _; omega,
    ltF_succ_add_add _ h]
  by_cases hcu : c = u
  · rw [if_pos hcu, if_pos hcu]
    exact (lt_eq_ltF d v _
      (by show d.deg + v.deg ≤ 2 * ((1 + c.deg + d.deg) + (1 + u.deg + v.deg)) + 7; omega)).symm
  · rw [if_neg hcu, if_neg hcu]
    exact (lt_eq_ltF c u _
      (by show c.deg + u.deg ≤ 2 * ((1 + c.deg + d.deg) + (1 + u.deg + v.deg)) + 7; omega)).symm

/-- 2.3.13(ii) for `lt`: `ω^·` is strictly monotone, and reflects the order. -/
theorem lt_pow (e a : Term) : lt (phi zero e) (phi zero a) = lt e a := by
  by_cases hea : e = a
  · subst hea; rw [lt_irrefl, lt_irrefl]
  · have hne : phi zero e ≠ phi zero a := by
      intro h; injection h with h1 h2; exact hea h2
    show ltF (fuelOf (phi zero e) (phi zero a)) (phi zero e) (phi zero a) = _
    rw [show fuelOf (phi zero e) (phi zero a)
          = (2 * ((phi zero e).deg + (phi zero a).deg) + 7) + 1 from by
        show 2 * ((phi zero e).deg + (phi zero a).deg) + 8 = _; omega,
      ltF_succ_phi_phi _ hne, if_pos rfl]
    exact (lt_eq_ltF e a _
      (by show e.deg + a.deg ≤ 2 * ((1 + 1 + e.deg) + (1 + 1 + a.deg)) + 7; omega)).symm

/-- **The tail of a CNF sum inherits any `φ̄`-bound on its head.**  This is where
    §7's transitivity is spent, and it is the step the whole argument turns on. -/
theorem lt_tail {a b p q : Term} (h : CN (add a b) = true) (hfpq : Frag (phi p q) = true)
    (hlt : lt a (phi p q) = true) : lt b (phi p q) = true := by
  obtain ⟨_, hcna, hcnb, hdesc⟩ := cn_add h
  have hfa : Frag a = true := frag_of_cn a hcna
  cases b with
  | zero => exact Bool.noConfusion hdesc
  | M => exact Bool.noConfusion hcnb
  | omg _ => exact Bool.noConfusion hcnb
  | psi _ _ => exact Bool.noConfusion hcnb
  | Z _ => exact Bool.noConfusion hcnb
  | phi x y =>
    exact lt_of_le_of_lt (frag_of_cn _ hcnb) hfa hfpq hdesc hlt
  | add c d =>
    obtain ⟨_, hcnc, _, _⟩ := cn_add hcnb
    rw [lt_add_phi]
    exact lt_of_le_of_lt (frag_of_cn c hcnc) hfa hfpq hdesc hlt

/-! ### §10.2 Accessibility -/

/-- The relation the certificate recursion descends along. -/
def RC (x y : Term) : Prop := CN x = true ∧ lt x y = true

theorem acc_zero : Acc RC zero := by
  refine Acc.intro _ (fun x hx => ?_)
  have h := hx.2
  rw [show lt x zero = false from ltF_right_zero _ x] at h
  exact Bool.noConfusion h

/-- **THE GENTZEN STEP.**  Simultaneously: `ω^a` is accessible, and prefixing `ω^a`
    to an accessible CNF tail keeps it accessible. -/
private theorem acc_pow_aux : ∀ (a : Term), Acc RC a → CN a = true →
    Acc RC (phi zero a) ∧ ∀ v, CN v = true → Acc RC v → Acc RC (add (phi zero a) v) := by
  intro a ha
  induction ha with
  | intro a _ IH =>
    intro hcna
    have hfpa : Frag (phi zero a) = true := by
      show (Frag zero && Frag a) = true
      rw [frag_of_cn a hcna]
      rfl
    have C : ∀ x, CN x = true → lt x (phi zero a) = true → Acc RC x := by
      intro x
      induction x with
      | zero => intro _ _; exact acc_zero
      | M => intro hcn _; exact Bool.noConfusion hcn
      | omg _ _ => intro hcn _; exact Bool.noConfusion hcn
      | psi _ _ _ _ => intro hcn _; exact Bool.noConfusion hcn
      | Z _ _ => intro hcn _; exact Bool.noConfusion hcn
      | phi p q _ _ =>
        intro hcn hlt
        obtain ⟨hp, hq⟩ := cn_phi hcn
        subst hp
        rw [lt_pow] at hlt
        exact (IH q ⟨hq, hlt⟩ hq).1
      | add c d _ ihd =>
        intro hcn hlt
        obtain ⟨hpow, hcnc, hcnd, _⟩ := cn_add hcn
        obtain ⟨e, hce⟩ := eq_pow_of_isPow hpow
        subst hce
        have hhead : lt (phi zero e) (phi zero a) = true := by rw [← lt_add_phi]; exact hlt
        have htail : lt d (phi zero a) = true := lt_tail hcn hfpa hhead
        have hcne : CN e = true := (cn_phi hcnc).2
        have hea : lt e a = true := by rw [← lt_pow]; exact hhead
        exact (IH e ⟨hcne, hea⟩ hcne).2 d hcnd (ihd hcnd htail)
    refine ⟨Acc.intro _ (fun x hx => C x hx.1 hx.2), ?_⟩
    intro v hcnv hav
    revert hcnv
    induction hav with
    | intro v _ IHv =>
      intro hcnv
      refine Acc.intro _ (fun x hx => ?_)
      obtain ⟨hcn, hlt⟩ := hx
      cases x with
      | zero => exact acc_zero
      | M => exact Bool.noConfusion hcn
      | omg _ => exact Bool.noConfusion hcn
      | psi _ _ => exact Bool.noConfusion hcn
      | Z _ => exact Bool.noConfusion hcn
      | phi p q =>
        obtain ⟨hp, _⟩ := cn_phi hcn
        subst hp
        rw [lt_phi_add] at hlt
        simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at hlt
        rcases hlt with h1 | h1
        · rw [h1]
          exact Acc.intro _ (fun y hy => C y hy.1 hy.2)
        · exact C _ hcn h1
      | add c d =>
        obtain ⟨hpow, hcnc, hcnd, _⟩ := cn_add hcn
        by_cases heq : add c d = add (phi zero a) v
        · rw [heq, lt_irrefl] at hlt; exact Bool.noConfusion hlt
        rw [lt_add_add heq] at hlt
        by_cases hc : c = phi zero a
        · subst hc
          rw [if_pos rfl] at hlt
          exact IHv d ⟨hcnd, hlt⟩ hcnd
        · rw [if_neg hc] at hlt
          exact C _ hcn (by rw [lt_add_phi]; exact hlt)

private theorem acc_of_cn_aux : ∀ (n : Nat) (t : Term), t.deg ≤ n → CN t = true → Acc RC t := by
  intro n
  induction n with
  | zero => intro t hd _; have := deg_pos t; omega
  | succ n ih =>
    intro t hd hcn
    cases t with
    | zero => exact acc_zero
    | M => exact Bool.noConfusion hcn
    | omg _ => exact Bool.noConfusion hcn
    | psi _ _ => exact Bool.noConfusion hcn
    | Z _ => exact Bool.noConfusion hcn
    | phi p q =>
      obtain ⟨hp, hq⟩ := cn_phi hcn
      subst hp
      have hdq : q.deg ≤ n := by
        have : (1 : Nat) + 1 + q.deg ≤ n + 1 := hd
        omega
      exact (acc_pow_aux q (ih q hdq hq) hq).1
    | add c d =>
      obtain ⟨hpow, hcnc, hcnd, _⟩ := cn_add hcn
      obtain ⟨e, hce⟩ := eq_pow_of_isPow hpow
      subst hce
      have hcne : CN e = true := (cn_phi hcnc).2
      have hde : e.deg ≤ n := by
        have : 1 + (1 + 1 + e.deg) + d.deg ≤ n + 1 := hd
        omega
      have hdd : d.deg ≤ n := by
        have : 1 + (1 + 1 + e.deg) + d.deg ≤ n + 1 := hd
        omega
      exact (acc_pow_aux e (ih e hde hcne) hcne).2 d hcnd (ih d hdd hcnd)

/-- **WELL-FOUNDEDNESS OF THE CNF SEGMENT BELOW ε₀.**  Every Cantor normal form is
    accessible in the order of 𝔗(M).  This is the recursion principle the ε₀
    certificate family runs on. -/
theorem acc_cn (t : Term) (h : CN t = true) : Acc RC t := acc_of_cn_aux t.deg t (Nat.le_refl _) h

/-- The two-sided relation, so that the statement is a `WellFounded` on all of
    `Term` and can be handed to `WellFounded.fix` directly: outside the CNF
    segment a term simply has no predecessors. -/
def RCn (x y : Term) : Prop := CN x = true ∧ CN y = true ∧ lt x y = true

private theorem acc_rcn_of_acc_rc : ∀ (t : Term), Acc RC t → Acc RCn t := by
  intro t ht
  induction ht with
  | intro t _ ih => exact Acc.intro _ (fun y hy => ih y ⟨hy.1, hy.2.2⟩)

theorem wf_RCn : WellFounded RCn := by
  refine ⟨fun t => ?_⟩
  by_cases h : CN t = true
  · exact acc_rcn_of_acc_rc t (acc_cn t h)
  · exact Acc.intro _ (fun y hy => absurd hy.2.1 h)

/-! ### §10.3 The mutant: the descending condition is load-bearing

`Frag` alone does not give well-foundedness.  The witnesses are the terms
`1 ⊕ 1 ⊕ … ⊕ ω`, all in `Frag`, all failing `CN`, and each strictly below the
previous one. -/

private def desc : Nat → Term
  | 0 => omega
  | n + 1 => add one (desc n)

#guard (List.range 6).all (fun n => Frag (desc n))
#guard CN (desc 0) = true
#guard (List.range 6).all (fun n => !CN (desc (n + 1)))
#guard (List.range 6).all (fun n => lt (desc (n + 1)) (desc n))

private theorem lt_desc : ∀ n, lt (desc (n + 1)) (desc n) = true := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show lt (add one (desc (n + 1))) (add one (desc n)) = true
    rw [lt_add_add (by intro h; injection h with h1 h2; exact ne_of_ltF ih h2), if_pos rfl]
    exact ih

/-- **The mutant.**  Dropping the descending condition — i.e. asking for
    well-foundedness on `Frag` instead of on `CN` — makes the statement FALSE. -/
theorem cn_desc_needed : ¬ (∀ t, Frag t = true → Acc (fun x y => lt x y = true) t) := by
  intro hwf
  have key : ∀ t, Acc (fun x y => lt x y = true) t → ∀ n, t = desc n → False := by
    intro t ht
    induction ht with
    | intro t _ ih =>
      intro n hn
      subst hn
      exact ih (desc (n + 1)) (lt_desc n) (n + 1) rfl
  exact key (desc 0) (hwf (desc 0) rfl) 0 rfl

/-! ## §11 The fundamental sequence of a CNF term  (STAGE 2b of the ε₀ certificate)

`Certified.lim` takes an ARBITRARY sequence `fs'` — it does not have to be
`TM/FS.lean`'s `fsN`.  On the CNF segment that is a large saving: `fsN` routes
every `φ̄` through `phiShifted` / `isFP` / `splitFin` (the [R91] 2.7 recalibration,
which is about Veblen fixed points and does nothing at all when `α = 0`), so
proving anything about it below ε₀ means dragging that machinery along.  `fsC`
below is the Cantor-normal-form sequence written directly:

    (ξ ⊕ ρ)[n]   = ξ ⊕ ρ[n]                 (into the last component)
    (ω^0)[n]     = —                        (ω^0 = 1 is a successor)
    (ω^(β+1))[n] = ω^β · (n+1)              (`repAdd`)
    (ω^β)[n]     = ω^(β[n])                 (β a limit)

Matching `fsC` to what the BM4 expansion actually produces is Stage 2c's job;
this section is pure order theory and needs nothing from `BMS/` or `Trans/`.

WHAT IS PROVED HERE: the three clauses of `Certified.lim` that speak only about
the sequence — it stays in CNF (`cn_fsC`), it is below (`lt_fsC`), and it
increases (`lt_fsC_step`).  The fourth, COFINALITY, is the remaining frontier and
is mapped at the end of the section. -/

/-- `u · (n+1)`: `n+1` copies of `u` as a formal sum. -/
def repAdd (u : Term) : Nat → Term
  | 0 => u
  | n + 1 => add u (repAdd u n)

/-- Is a CNF term a successor?  Exactly when its last component is `ω^0 = 1`. -/
def kindC : Term → Bool
  | phi _ b => b == zero
  | add _ v => kindC v
  | _ => false

/-- The predecessor of a CNF successor: drop the trailing `1`. -/
def predC : Term → Term
  | add u v => if v == one then u else add u (predC v)
  | _ => zero

/-- The head component of a formal sum. -/
def hdOf : Term → Term
  | add u _ => u
  | t => t

/-- **The CNF fundamental sequence.** -/
def fsC : Term → Nat → Term
  | add u v, n => add u (fsC v n)
  | phi a b, n =>
      if b == zero then zero
      else if kindC b then repAdd (phi a (predC b)) n
      else phi a (fsC b n)
  | _, _ => zero

/-! ### §11.0 The three defining equations of `fsC`, as rewrite rules

Stating them once is not cosmetic: the `if`-chain of `fsC` appears twice in the
statement of `lt_fsC_step` (at `n` and at `n+1`) with different bodies, and `rw`
instantiates its metavariables from the first match, so an unfolding `show`
cannot reach the second. -/

theorem fsC_add (u v : Term) (n : Nat) : fsC (add u v) n = add u (fsC v n) := rfl

theorem fsC_phi_succ {x y : Term} (hy : (y == zero) = false) (hk : kindC y = true) (n : Nat) :
    fsC (phi x y) n = repAdd (phi x (predC y)) n := by
  show (if (y == zero) = true then zero
        else if kindC y then repAdd (phi x (predC y)) n else phi x (fsC y n)) = _
  rw [if_neg (by rw [hy]; exact Bool.noConfusion), if_pos hk]

theorem fsC_phi_lim {x y : Term} (hy : (y == zero) = false) (hk : kindC y = false) (n : Nat) :
    fsC (phi x y) n = phi x (fsC y n) := by
  show (if (y == zero) = true then zero
        else if kindC y then repAdd (phi x (predC y)) n else phi x (fsC y n)) = _
  rw [if_neg (by rw [hy]; exact Bool.noConfusion), if_neg (by rw [hk]; exact Bool.noConfusion)]

/-! ### §11.1 Bookkeeping -/

theorem le_self (u : Term) : le u u = true := by
  show ((u == u) || lt u u) = true
  simp

theorem hdLe_eq : ∀ (b a : Term), b ≠ zero → hdLe b a = le (hdOf b) a
  | zero, _, h => absurd rfl h
  | add _ _, _, _ => rfl
  | M, _, _ => rfl
  | omg _, _, _ => rfl
  | phi _ _, _, _ => rfl
  | psi _ _, _, _ => rfl
  | Z _, _, _ => rfl

theorem hdOf_repAdd (p q : Term) : ∀ n, hdOf (repAdd (phi p q) n) = phi p q
  | 0 => rfl
  | _ + 1 => rfl

theorem repAdd_ne_zero (p q : Term) : ∀ n, repAdd (phi p q) n ≠ zero
  | 0 => by intro h; exact Term.noConfusion h
  | _ + 1 => by intro h; exact Term.noConfusion h

theorem cn_repAdd {p q : Term} (h : CN (phi p q) = true) :
    ∀ n, CN (repAdd (phi p q) n) = true
  | 0 => h
  | n + 1 => by
    have hp : p = zero := (cn_phi h).1
    show (isPow (phi p q) && CN (phi p q) && CN (repAdd (phi p q) n)
            && hdLe (repAdd (phi p q) n) (phi p q)) = true
    rw [cn_repAdd h n, h, hdLe_eq _ _ (repAdd_ne_zero p q n), hdOf_repAdd,
      le_self, show isPow (phi p q) = true from by rw [hp]; rfl]
    rfl

/-- A sum built by `repAdd` is below a `φ̄` exactly when its single component is. -/
theorem lt_repAdd_phi (p q c d : Term) : ∀ n,
    lt (repAdd (phi p q) n) (phi c d) = lt (phi p q) (phi c d)
  | 0 => rfl
  | n + 1 => by
    show lt (add (phi p q) (repAdd (phi p q) n)) (phi c d) = _
    rw [lt_add_phi]

/-- `u·(n+1) < u·(n+2)`. -/
theorem lt_repAdd_step (p q : Term) : ∀ n,
    lt (repAdd (phi p q) n) (repAdd (phi p q) (n + 1)) = true
  | 0 => by
    show lt (phi p q) (add (phi p q) (phi p q)) = true
    rw [lt_phi_add]
    exact le_self _
  | n + 1 => by
    have ih := lt_repAdd_step p q n
    show lt (add (phi p q) (repAdd (phi p q) n)) (add (phi p q) (repAdd (phi p q) (n + 1))) = true
    rw [lt_add_add (by intro h; injection h with h1 h2; exact ne_of_ltF ih h2), if_pos rfl]
    exact ih

/-! ### §11.2 The predecessor of a CNF successor -/

theorem predC_ne_zero : ∀ (b : Term), CN b = true → kindC b = true → b ≠ one →
    predC b ≠ zero := by
  intro b hcn hk hne
  cases b with
  | zero => exact Bool.noConfusion hk
  | M => exact Bool.noConfusion hcn
  | omg _ => exact Bool.noConfusion hcn
  | psi _ _ => exact Bool.noConfusion hcn
  | Z _ => exact Bool.noConfusion hcn
  | phi x y =>
    have hx : x = zero := (cn_phi hcn).1
    have hy : y = zero := by
      have : (y == zero) = true := hk
      simpa using this
    exact absurd (by rw [hx, hy]; rfl) hne
  | add u v =>
    show (if (v == one) = true then u else add u (predC v)) ≠ zero
    obtain ⟨hpow, _, _, _⟩ := cn_add hcn
    obtain ⟨e, he⟩ := eq_pow_of_isPow hpow
    subst he
    by_cases hv : (v == one) = true
    · rw [if_pos hv]; intro h; exact Term.noConfusion h
    · rw [if_neg hv]; intro h; exact Term.noConfusion h

theorem cn_predC : ∀ (b : Term), CN b = true → kindC b = true → CN (predC b) = true := by
  intro b
  induction b with
  | zero => intro _ hk; exact Bool.noConfusion hk
  | M => intro hcn _; exact Bool.noConfusion hcn
  | omg _ _ => intro hcn _; exact Bool.noConfusion hcn
  | psi _ _ _ _ => intro hcn _; exact Bool.noConfusion hcn
  | Z _ _ => intro hcn _; exact Bool.noConfusion hcn
  | phi _ _ _ _ => intro _ _; exact rfl
  | add u v _ ihv =>
    intro hcn hk
    obtain ⟨hpow, hcnu, hcnv, hdesc⟩ := cn_add hcn
    show CN (if (v == one) = true then u else add u (predC v)) = true
    by_cases hv : (v == one) = true
    · rw [if_pos hv]; exact hcnu
    · rw [if_neg hv]
      have hkv : kindC v = true := hk
      have hvone : v ≠ one := by intro h; exact hv (by rw [h]; rfl)
      have hpz : predC v ≠ zero := predC_ne_zero v hcnv hkv hvone
      show (isPow u && CN u && CN (predC v) && hdLe (predC v) u) = true
      rw [ihv hcnv hkv, hcnu, hpow]
      have hvz : v ≠ zero := by intro h; rw [h] at hkv; exact Bool.noConfusion hkv
      rw [hdLe_eq _ _ hpz, show hdOf (predC v) = hdOf v from ?_]
      · rw [← hdLe_eq v u hvz, hdesc]
        rfl
      · cases v with
        | add w r =>
          show hdOf (if (r == one) = true then w else add w (predC r)) = w
          by_cases hr : (r == one) = true
          · rw [if_pos hr]
            cases w with
            | add _ _ => obtain ⟨hpw, _, _, _⟩ := cn_add hcnv; exact Bool.noConfusion hpw
            | _ => rfl
          · rw [if_neg hr]; rfl
        | phi x y =>
          exfalso
          apply hvone
          have hx : x = zero := (cn_phi hcnv).1
          have hy2 : y = zero := by
            have hh : (y == zero) = true := hkv
            simpa using hh
          rw [hx, hy2]
          rfl
        | zero => exact Bool.noConfusion hkv
        | M => exact Bool.noConfusion hcnv
        | omg _ => exact Bool.noConfusion hcnv
        | psi _ _ => exact Bool.noConfusion hcnv
        | Z _ => exact Bool.noConfusion hcnv

theorem lt_predC : ∀ (b : Term), CN b = true → kindC b = true → lt (predC b) b = true := by
  intro b
  induction b with
  | zero => intro _ hk; exact Bool.noConfusion hk
  | M => intro hcn _; exact Bool.noConfusion hcn
  | omg _ _ => intro hcn _; exact Bool.noConfusion hcn
  | psi _ _ _ _ => intro hcn _; exact Bool.noConfusion hcn
  | Z _ _ => intro hcn _; exact Bool.noConfusion hcn
  | phi x y _ _ =>
    intro hcn hk
    have hx : x = zero := (cn_phi hcn).1
    have hy : y = zero := by have : (y == zero) = true := hk; simpa using this
    subst hx; subst hy
    show lt zero (phi zero zero) = true
    exact ltF_left_zero (by show 1 ≤ 2 * ((zero : Term).deg + (one : Term).deg) + 8; omega)
      (by decide)
  | add u v _ ihv =>
    intro hcn hk
    obtain ⟨hpow, hcnu, hcnv, hdesc⟩ := cn_add hcn
    obtain ⟨e, he⟩ := eq_pow_of_isPow hpow
    subst he
    show lt (if (v == one) = true then phi zero e else add (phi zero e) (predC v))
        (add (phi zero e) v) = true
    by_cases hv : (v == one) = true
    · rw [if_pos hv, lt_phi_add]
      exact le_self _
    · rw [if_neg hv]
      have hkv : kindC v = true := hk
      have hlt : lt (predC v) v = true := ihv hcnv hkv
      rw [lt_add_add (by intro h; injection h with h1 h2; exact ne_of_ltF hlt h2), if_pos rfl]
      exact hlt

/-! ### §11.3 The three sequence clauses -/

theorem fsC_ne_zero : ∀ (t : Term), CN t = true → kindC t = false → t ≠ zero →
    ∀ n, fsC t n ≠ zero := by
  intro t
  induction t with
  | zero => intro _ _ hz; exact absurd rfl hz
  | M => intro hcn _ _; exact Bool.noConfusion hcn
  | omg _ _ => intro hcn _ _; exact Bool.noConfusion hcn
  | psi _ _ _ _ => intro hcn _ _; exact Bool.noConfusion hcn
  | Z _ _ => intro hcn _ _; exact Bool.noConfusion hcn
  | phi x y _ _ =>
    intro hcn hk _ n
    have hy : (y == zero) = false := hk
    by_cases hky : kindC y = true
    · rw [fsC_phi_succ hy hky]; exact repAdd_ne_zero _ _ n
    · rw [fsC_phi_lim hy (by simpa using hky)]; intro h; exact Term.noConfusion h
  | add u v _ _ =>
    intro _ _ _ _ h; exact Term.noConfusion h

/-- **The sequence is below its limit.** -/
theorem lt_fsC : ∀ (t : Term), CN t = true → kindC t = false → t ≠ zero →
    ∀ n, lt (fsC t n) t = true := by
  intro t
  induction t with
  | zero => intro _ _ hz; exact absurd rfl hz
  | M => intro hcn _ _; exact Bool.noConfusion hcn
  | omg _ _ => intro hcn _ _; exact Bool.noConfusion hcn
  | psi _ _ _ _ => intro hcn _ _; exact Bool.noConfusion hcn
  | Z _ _ => intro hcn _ _; exact Bool.noConfusion hcn
  | phi x y _ ihy =>
    intro hcn hk _ n
    have hx : x = zero := (cn_phi hcn).1
    have hcny : CN y = true := (cn_phi hcn).2
    subst hx
    have hy : (y == zero) = false := hk
    have hyz : y ≠ zero := by intro h; rw [h] at hy; exact Bool.noConfusion hy
    by_cases hky : kindC y = true
    · rw [fsC_phi_succ hy hky, lt_repAdd_phi, lt_pow]
      exact lt_predC y hcny hky
    · rw [fsC_phi_lim hy (by simpa using hky), lt_pow]
      exact ihy hcny (by simpa using hky) hyz n
  | add u v _ ihv =>
    intro hcn hk _ n
    obtain ⟨_, _, hcnv, hdesc⟩ := cn_add hcn
    have hvz : v ≠ zero := by intro h; rw [h] at hdesc; exact Bool.noConfusion hdesc
    have hlt : lt (fsC v n) v = true := ihv hcnv hk hvz n
    show lt (add u (fsC v n)) (add u v) = true
    rw [lt_add_add (by intro h; injection h with h1 h2; exact ne_of_ltF hlt h2), if_pos rfl]
    exact hlt

/-- **The sequence increases.** -/
theorem lt_fsC_step : ∀ (t : Term), CN t = true → kindC t = false → t ≠ zero →
    ∀ n, lt (fsC t n) (fsC t (n + 1)) = true := by
  intro t
  induction t with
  | zero => intro _ _ hz; exact absurd rfl hz
  | M => intro hcn _ _; exact Bool.noConfusion hcn
  | omg _ _ => intro hcn _ _; exact Bool.noConfusion hcn
  | psi _ _ _ _ => intro hcn _ _; exact Bool.noConfusion hcn
  | Z _ _ => intro hcn _ _; exact Bool.noConfusion hcn
  | phi x y _ ihy =>
    intro hcn hk _ n
    have hx : x = zero := (cn_phi hcn).1
    have hcny : CN y = true := (cn_phi hcn).2
    subst hx
    have hy : (y == zero) = false := hk
    have hyz : y ≠ zero := by intro h; rw [h] at hy; exact Bool.noConfusion hy
    by_cases hky : kindC y = true
    · rw [fsC_phi_succ hy hky, fsC_phi_succ hy hky]
      exact lt_repAdd_step zero (predC y) n
    · rw [fsC_phi_lim hy (by simpa using hky), fsC_phi_lim hy (by simpa using hky), lt_pow]
      exact ihy hcny (by simpa using hky) hyz n
  | add u v _ ihv =>
    intro hcn hk _ n
    obtain ⟨_, _, hcnv, hdesc⟩ := cn_add hcn
    have hvz : v ≠ zero := by intro h; rw [h] at hdesc; exact Bool.noConfusion hdesc
    have hlt : lt (fsC v n) (fsC v (n + 1)) = true := ihv hcnv hk hvz n
    show lt (add u (fsC v n)) (add u (fsC v (n + 1))) = true
    rw [lt_add_add (by intro h; injection h with h1 h2; exact ne_of_ltF hlt h2), if_pos rfl]
    exact hlt

/-- The head of the sequence never exceeds the head of the limit — the step the
    CNF-closure of `fsC` turns on. -/
theorem hdOf_fsC_le : ∀ (t : Term), CN t = true → kindC t = false → t ≠ zero →
    ∀ n, le (hdOf (fsC t n)) (hdOf t) = true := by
  intro t
  induction t with
  | zero => intro _ _ hz; exact absurd rfl hz
  | M => intro hcn _ _; exact Bool.noConfusion hcn
  | omg _ _ => intro hcn _ _; exact Bool.noConfusion hcn
  | psi _ _ _ _ => intro hcn _ _; exact Bool.noConfusion hcn
  | Z _ _ => intro hcn _ _; exact Bool.noConfusion hcn
  | phi x y _ _ =>
    intro hcn hk hz n
    have hlt : lt (fsC (phi x y) n) (phi x y) = true := lt_fsC _ hcn hk hz n
    have hx : x = zero := (cn_phi hcn).1
    subst hx
    have hy : (y == zero) = false := hk
    show le (hdOf (fsC (phi zero y) n)) (phi zero y) = true
    by_cases hky : kindC y = true
    · rw [fsC_phi_succ hy hky, hdOf_repAdd]
      show ((phi zero (predC y) == phi zero y) || lt (phi zero (predC y)) (phi zero y)) = true
      rw [lt_pow, lt_predC y (cn_phi hcn).2 hky]
      exact Bool.or_true _
    · rw [fsC_phi_lim hy (by simpa using hky)]
      show ((phi zero (fsC y n) == phi zero y) || lt (phi zero (fsC y n)) (phi zero y)) = true
      rw [fsC_phi_lim hy (by simpa using hky)] at hlt
      rw [hlt]
      exact Bool.or_true _
  | add u v _ _ =>
    intro _ _ _ _
    show le (hdOf (add u (fsC v _))) (hdOf (add u v)) = true
    exact le_self _

/-- **The sequence stays in CNF.** -/
theorem cn_fsC : ∀ (t : Term), CN t = true → kindC t = false → t ≠ zero →
    ∀ n, CN (fsC t n) = true := by
  intro t
  induction t with
  | zero => intro _ _ hz; exact absurd rfl hz
  | M => intro hcn _ _; exact Bool.noConfusion hcn
  | omg _ _ => intro hcn _ _; exact Bool.noConfusion hcn
  | psi _ _ _ _ => intro hcn _ _; exact Bool.noConfusion hcn
  | Z _ _ => intro hcn _ _; exact Bool.noConfusion hcn
  | phi x y _ ihy =>
    intro hcn hk _ n
    have hx : x = zero := (cn_phi hcn).1
    have hcny : CN y = true := (cn_phi hcn).2
    subst hx
    have hy : (y == zero) = false := hk
    have hyz : y ≠ zero := by intro h; rw [h] at hy; exact Bool.noConfusion hy
    by_cases hky : kindC y = true
    · rw [fsC_phi_succ hy hky]
      refine cn_repAdd ?_ n
      show (((zero : Term) == zero) && CN (predC y)) = true
      rw [cn_predC y hcny hky]
      rfl
    · rw [fsC_phi_lim hy (by simpa using hky)]
      show (((zero : Term) == zero) && CN (fsC y n)) = true
      rw [ihy hcny (by simpa using hky) hyz n]
      rfl
  | add u v _ ihv =>
    intro hcn hk _ n
    obtain ⟨hpow, hcnu, hcnv, hdesc⟩ := cn_add hcn
    have hvz : v ≠ zero := by intro h; rw [h] at hdesc; exact Bool.noConfusion hdesc
    have hcnfv : CN (fsC v n) = true := ihv hcnv hk hvz n
    have hfvz : fsC v n ≠ zero := fsC_ne_zero v hcnv hk hvz n
    have hhd : le (hdOf (fsC v n)) (hdOf v) = true := hdOf_fsC_le v hcnv hk hvz n
    have hfrag1 : Frag (hdOf (fsC v n)) = true := by
      have := frag_of_cn _ hcnfv
      cases hx : fsC v n with
      | add c d => rw [hx] at this; exact (frag_add this).1
      | _ => rw [hx] at this; exact this
    have hfrag2 : Frag (hdOf v) = true := by
      have := frag_of_cn _ hcnv
      cases hx : v with
      | add c d => rw [hx] at this; exact (frag_add this).1
      | _ => rw [hx] at this; exact this
    show (isPow u && CN u && CN (fsC v n) && hdLe (fsC v n) u) = true
    rw [hcnfv, hcnu, hpow, hdLe_eq _ _ hfvz]
    have hvu : le (hdOf v) u = true := by rw [← hdLe_eq v u hvz]; exact hdesc
    rw [le_trans hfrag1 hfrag2 (frag_of_cn u hcnu) hhd hvu]
    rfl

/-! ### §11.4 Evidence, and where the fourth clause went

MEASURED (not proved here).  `fsC t n = fsN t (n + 1)` for every term of the
sample below and every `n ≤ 5` — i.e. `fsC` IS `TM/FS.lean`'s fundamental
sequence on the CNF segment, with the index shift of `Trans/TM.lean`
(`M[n] ↦ t[n+1]`).  The check cannot be a `#guard` in THIS file: `fsN` lives in
`TM/FS.lean`, which `Evidence/WF.lean` does not import (and must not, to keep the
import direction that lets `Evidence/Cert.lean` import this file).  Stage 2c can
either prove that identity in `Cert.lean` — where `fsN` is in scope — or bypass
`fsN` completely, since `Certified.lim` takes an arbitrary `fs'`.

THE FOURTH CLAUSE, COFINALITY, is proved: `cof_fsC` in §14.  It needed three
auxiliaries, all in §12 — (J) `lt_junkAP_cn`, (K) `lt_pow_self`, (L)
`le_predC_of_lt` — and one structural theorem, §13's `cn_of_lt_cn`: below a
Cantor normal form there is nothing but Cantor normal forms.  §13 is what removed
the case bash: once every `s` in range is known to be `CN`, it is `Frag`, so §7's
transitivity applies to it and the seven-constructor analysis collapses to three
shapes.  `lim_clauses` (§14.1) packages all four. -/

private def cnSample : List Term :=
  [omega, phi zero omega, phi zero (ofNat 2), add omega omega, phi zero (phi zero omega),
   add (phi zero omega) omega, phi zero (add omega one), tower 3, tower 4,
   add (phi zero (phi zero omega)) (phi zero omega)]

#guard cnSample.all (fun t => CN t && !kindC t && !(t == zero))
#guard cnSample.all (fun t => (List.range 5).all (fun n =>
         CN (fsC t n) && lt (fsC t n) t && lt (fsC t n) (fsC t (n + 1))))
#guard (List.range 6).all (fun k => CN (tower k) && (fsC (tower (k + 1)) 0 == tower k))

/-- The towers are the values of `(0,0)(1,1)[n]`, and `fsC` reproduces them: the
    fundamental sequence of `tower (k+1) = ω^(tower k)` starts at `tower k`
    because `tower k` is a limit for `k ≥ 1`. -/
theorem fsC_tower_zero : ∀ k, fsC (tower (k + 1)) 0 = tower k
  | 0 => rfl
  | k + 1 => by
    have hne : (tower (k + 1) == zero) = false := by cases k <;> rfl
    have hk : kindC (tower (k + 1)) = false := by cases k <;> rfl
    show fsC (phi zero (tower (k + 1))) 0 = tower (k + 1)
    rw [fsC_phi_lim hne hk]
    show phi zero (fsC (tower (k + 1)) 0) = phi zero (tower k)
    rw [fsC_tower_zero k]

/-! ## §12 The three auxiliaries the cofinality clause needs  (STAGE 2b, part 2)

§11.4 named them (J), (K), (L).  All three are proved here; what is left after
this section is the cofinality induction itself. -/

/-- The shapes that are not CNF and not sums: `M`, `ω̄^·`, `ψ`, `Z`.  These are
    exactly the terms the `⊕`/`φ̄` clauses can never place below a CNF term. -/
def junkAP : Term → Bool
  | M => true
  | omg _ => true
  | psi _ _ => true
  | Z _ => true
  | _ => false

/-- Everything that is not `0` and not a sum: the left-hand shapes for which
    clause 2.3.11 decides `s < ⊕(…)` by `s ≤ α₁`. -/
def isAtom : Term → Bool
  | zero => false
  | add _ _ => false
  | _ => true

theorem cn_ne_junkAP {s b : Term} (hs : junkAP s = true) (hb : CN b = true) :
    (s == b) = false := by
  cases s <;> cases b <;>
    first
      | rfl
      | exact Bool.noConfusion hs
      | exact Bool.noConfusion hb

/-- 2.3.11 for `lt`, for every left-hand shape at once. -/
theorem lt_atom_add {s : Term} (hs : isAtom s = true) (u v : Term) :
    lt s (add u v) = le s u := by
  have hv := deg_pos v
  have key : ∀ (G : Nat), ltF (G + 1) s (add u v) = ((s == u) || ltF G s u) := by
    intro G
    cases s with
    | zero => exact Bool.noConfusion hs
    | add _ _ => exact Bool.noConfusion hs
    | M => rfl
    | omg _ => rfl
    | phi _ _ => rfl
    | psi _ _ => rfl
    | Z _ => rfl
  show ltF (fuelOf s (add u v)) s (add u v) = _
  rw [show fuelOf s (add u v) = (2 * (s.deg + (add u v).deg) + 7) + 1 from by
      show 2 * (s.deg + (add u v).deg) + 8 = _; omega, key]
  rw [show ltF (2 * (s.deg + (add u v).deg) + 7) s u = lt s u from
    (lt_eq_ltF s u _
      (by show s.deg + u.deg ≤ 2 * (s.deg + (1 + u.deg + v.deg)) + 7; omega)).symm]
  rfl

/-- **(J)** A `ψ`, `Z`, `M` or `ω̄^·` is never below a Cantor normal form. -/
theorem lt_junkAP_cn : ∀ (y : Term), CN y = true → ∀ (f : Nat) (s : Term),
    junkAP s = true → ltF f s y = false := by
  intro y
  induction y with
  | M => intro hb; exact Bool.noConfusion hb
  | omg _ _ => intro hb; exact Bool.noConfusion hb
  | psi _ _ _ _ => intro hb; exact Bool.noConfusion hb
  | Z _ _ => intro hb; exact Bool.noConfusion hb
  | zero =>
    intro _ f s hs
    cases f with
    | zero => rfl
    | succ g =>
      cases s with
      | zero => exact Bool.noConfusion hs
      | add _ _ => exact Bool.noConfusion hs
      | M => rfl
      | omg _ => rfl
      | phi _ _ => exact Bool.noConfusion hs
      | psi _ _ => rfl
      | Z _ => rfl
  | phi x b _ ihb =>
    intro hcn f s hs
    have hx : x = zero := (cn_phi hcn).1
    have hcnb : CN b = true := (cn_phi hcn).2
    subst hx
    cases f with
    | zero => rfl
    | succ g =>
      cases s with
      | zero => exact Bool.noConfusion hs
      | add _ _ => exact Bool.noConfusion hs
      | phi _ _ => exact Bool.noConfusion hs
      | M => rfl
      | omg _ => rfl
      | psi k a =>
        show ((psi k a == zero) || (psi k a == b) || ltF g (psi k a) zero
                || ltF g (psi k a) b) = false
        rw [cn_ne_junkAP (s := psi k a) rfl hcnb, ltF_right_zero, ihb hcnb g (psi k a) rfl]
        rfl
      | Z a =>
        show ((Z a == zero) || (Z a == b) || ltF g (Z a) zero || ltF g (Z a) b) = false
        rw [cn_ne_junkAP (s := Z a) rfl hcnb, ltF_right_zero, ihb hcnb g (Z a) rfl]
        rfl
  | add u v ihu _ =>
    intro hcn f s hs
    obtain ⟨_, hcnu, _, _⟩ := cn_add hcn
    cases f with
    | zero => rfl
    | succ g =>
      have hkey : ltF (g + 1) s (add u v) = ((s == u) || ltF g s u) := by
        cases s with
        | zero => exact Bool.noConfusion hs
        | add _ _ => exact Bool.noConfusion hs
        | phi _ _ => exact Bool.noConfusion hs
        | M => rfl
        | omg _ => rfl
        | psi _ _ => rfl
        | Z _ => rfl
      rw [hkey, cn_ne_junkAP hs hcnu, ihu hcnu g s hs]
      rfl

/-- **(K)** Every Cantor normal form is below `ω` raised to itself. -/
theorem lt_pow_self : ∀ (x : Term), CN x = true → lt x (phi zero x) = true := by
  intro x
  induction x with
  | M => intro hcn; exact Bool.noConfusion hcn
  | omg _ _ => intro hcn; exact Bool.noConfusion hcn
  | psi _ _ _ _ => intro hcn; exact Bool.noConfusion hcn
  | Z _ _ => intro hcn; exact Bool.noConfusion hcn
  | zero =>
    intro _
    exact ltF_left_zero (by show 1 ≤ 2 * ((zero : Term).deg + (one : Term).deg) + 8; omega)
      (by decide)
  | phi p q _ ihq =>
    intro hcn
    have hp : p = zero := (cn_phi hcn).1
    subst hp
    rw [lt_pow]
    exact ihq (cn_phi hcn).2
  | add u v ihu _ =>
    intro hcn
    obtain ⟨hpow, hcnu, hcnv, _⟩ := cn_add hcn
    obtain ⟨e, he⟩ := eq_pow_of_isPow hpow
    subst he
    have h1 : lt e (phi zero e) = true := by
      have := ihu hcnu
      rw [lt_pow] at this
      exact this
    have h2 : lt (phi zero e) (add (phi zero e) v) = true := by
      rw [lt_atom_add rfl]
      exact le_self _
    have hfrag : Frag (add (phi zero e) v) = true := frag_of_cn _ hcn
    rw [lt_add_phi, lt_pow]
    exact lt_trans (frag_of_cn e (cn_phi hcnu).2) (frag_of_cn _ hcnu) hfrag h1 h2

/-! ### §12.1 Two monotonicity steps for sums -/

theorem le_add_tail {u d e : Term} (h : le d e = true) : le (add u d) (add u e) = true := by
  simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at h ⊢
  rcases h with rfl | h
  · exact Or.inl rfl
  · refine Or.inr ?_
    rw [lt_add_add (by intro hc; injection hc with h1 h2; exact ne_of_ltF h h2), if_pos rfl]
    exact h

theorem lt_add_head {c d u v : Term} (h : c ≠ u) (hlt : lt c u = true) :
    lt (add c d) (add u v) = true := by
  rw [lt_add_add (by intro hc; injection hc with h1 h2; exact h h1), if_neg h]
  exact hlt

/-- The `⊕`-step both branches of `le_predC_of_lt` use on an atomic `q`: clause
    2.3.11 decides `q < ξ ⊕ ρ` and `q < ξ ⊕ ρ'` by the SAME test `q ≤ ξ`. -/
private theorem atom_step {q u v w : Term} (hs : isAtom q = true)
    (h : lt q (add u v) = true) : le q (add u w) = true := by
  rw [lt_atom_add hs] at h
  show ((q == add u w) || lt q (add u w)) = true
  rw [lt_atom_add hs, h]
  exact Bool.or_true _

/-- **(L)** The successor inversion: nothing of 𝔗(M) lies strictly between the
    predecessor of a CNF successor and the successor itself.  `below_one` (§9.3)
    is the instance `β = 1`. -/
theorem le_predC_of_lt : ∀ (b : Term), CN b = true → kindC b = true →
    ∀ (q : Term), inT q = true → lt q b = true → le q (predC b) = true := by
  intro b
  induction b with
  | M => intro hcn; exact Bool.noConfusion hcn
  | omg _ _ => intro hcn; exact Bool.noConfusion hcn
  | psi _ _ _ _ => intro hcn; exact Bool.noConfusion hcn
  | Z _ _ => intro hcn; exact Bool.noConfusion hcn
  | zero => intro _ hk; exact Bool.noConfusion hk
  | phi x y _ _ =>
    intro hcn hk q hq hlt
    have hx : x = zero := (cn_phi hcn).1
    have hy : y = zero := by
      have hh : (y == zero) = true := hk
      simpa using hh
    subst hx; subst hy
    have : q = zero := below_one q hq _ hlt
    subst this
    rfl
  | add u v _ ihv =>
    intro hcn hk q hq hlt
    obtain ⟨hpow, hcnu, hcnv, hdesc⟩ := cn_add hcn
    obtain ⟨e, he⟩ := eq_pow_of_isPow hpow
    subst he
    have hkv : kindC v = true := hk
    show le q (if (v == one) = true then phi zero e else add (phi zero e) (predC v)) = true
    by_cases hv : (v == one) = true
    · rw [if_pos hv]
      have hveq : v = one := by simpa using hv
      subst hveq
      cases q with
      | zero =>
        show ((zero == phi zero e) || lt zero (phi zero e)) = true
        rw [show lt zero (phi zero e) = true from
          ltF_left_zero (by show 1 ≤ 2 * ((zero : Term).deg + (phi zero e).deg) + 8; omega)
            (by intro hc; exact Term.noConfusion hc)]
        exact Bool.or_true _
      | M => rw [lt_atom_add rfl] at hlt; exact hlt
      | omg _ => rw [lt_atom_add rfl] at hlt; exact hlt
      | psi _ _ => rw [lt_atom_add rfl] at hlt; exact hlt
      | Z _ => rw [lt_atom_add rfl] at hlt; exact hlt
      | phi _ _ => rw [lt_atom_add rfl] at hlt; exact hlt
      | add c d =>
        obtain ⟨_, _, hind⟩ := inT_add hq
        by_cases heq : add c d = add (phi zero e) one
        · rw [heq, lt_irrefl] at hlt; exact Bool.noConfusion hlt
        rw [lt_add_add heq] at hlt
        by_cases hcu : c = phi zero e
        · rw [if_pos hcu] at hlt
          have hdz : d = zero := below_one d hind _ hlt
          subst hdz
          exfalso
          have hbad : inT (add c zero) = false := by
            show (c.isAP && inT c && inT zero && ((zero : Term).isAP && le zero c)) = false
            rw [show ((zero : Term).isAP && le zero c) = false from rfl, Bool.and_false]
          rw [hbad] at hq
          exact Bool.noConfusion hq
        · rw [if_neg hcu] at hlt
          show ((add c d == phi zero e) || lt (add c d) (phi zero e)) = true
          rw [lt_add_phi, hlt]
          exact Bool.or_true _
    · rw [if_neg hv]
      cases q with
      | zero =>
        show ((zero == add (phi zero e) (predC v)) || lt zero (add (phi zero e) (predC v))) = true
        rw [show lt zero (add (phi zero e) (predC v)) = true from
          ltF_left_zero
            (by show 1 ≤ 2 * ((zero : Term).deg + (add (phi zero e) (predC v)).deg) + 8; omega)
            (by intro hc; exact Term.noConfusion hc)]
        exact Bool.or_true _
      | M => exact atom_step rfl hlt
      | omg _ => exact atom_step rfl hlt
      | psi _ _ => exact atom_step rfl hlt
      | Z _ => exact atom_step rfl hlt
      | phi _ _ => exact atom_step rfl hlt
      | add c d =>
        obtain ⟨_, _, hind⟩ := inT_add hq
        by_cases heq : add c d = add (phi zero e) v
        · rw [heq, lt_irrefl] at hlt; exact Bool.noConfusion hlt
        rw [lt_add_add heq] at hlt
        by_cases hcu : c = phi zero e
        · rw [if_pos hcu] at hlt
          subst hcu
          exact le_add_tail (ihv hcnv hkv d hind hlt)
        · rw [if_neg hcu] at hlt
          show ((add c d == add (phi zero e) (predC v))
                  || lt (add c d) (add (phi zero e) (predC v))) = true
          rw [lt_add_head hcu hlt]
          exact Bool.or_true _

/-! ## §13 Below a Cantor normal form there is nothing but Cantor normal forms

This is the structural theorem the cofinality induction needs, and it is the
strongest form of §9's shape analysis: §9 showed that the terms 2.3 puts below ε₀
have CNF SHAPE along the head spine; here the whole term is pinned, with `inT` as
the only extra hypothesis (and it is indispensable for §9's reason — `0 ⊕ M` is
below `1`).

Once it is available every `s` occurring in a cofinality proof is `CN`, hence
`Frag`, hence §7's transitivity applies to it — which is what makes the remaining
clause tractable at all.

The induction is on `s.deg + c.deg`: the `φ̄` case keeps `s` and shrinks the bound
(2.3.13(iii) hands `φ̄pq ≤ δ` back with the SAME left-hand side), so no structural
induction on `s` alone can work. -/

/-- 2.3.13 for `lt`, all three sub-clauses. -/
theorem lt_phi_phi {a b c d : Term} (h : phi a b ≠ phi c d) :
    lt (phi a b) (phi c d) =
      (if a = c then lt b d
       else if lt a c = true then lt b (phi c d) else le (phi a b) d) := by
  have ha := deg_pos a; have hb := deg_pos b; have hc := deg_pos c; have hd := deg_pos d
  show ltF (fuelOf (phi a b) (phi c d)) (phi a b) (phi c d) = _
  rw [show fuelOf (phi a b) (phi c d) = (2 * ((phi a b).deg + (phi c d).deg) + 7) + 1 from by
      show 2 * ((phi a b).deg + (phi c d).deg) + 8 = _; omega,
    ltF_succ_phi_phi _ h]
  by_cases hac : a = c
  · rw [if_pos hac, if_pos hac]
    exact (lt_eq_ltF b d _
      (by show b.deg + d.deg ≤ 2 * ((1 + a.deg + b.deg) + (1 + c.deg + d.deg)) + 7; omega)).symm
  · rw [if_neg hac, if_neg hac,
      show ltF (2 * ((phi a b).deg + (phi c d).deg) + 7) a c = lt a c from
        (lt_eq_ltF a c _
          (by show a.deg + c.deg ≤ 2 * ((1 + a.deg + b.deg) + (1 + c.deg + d.deg)) + 7;
              omega)).symm]
    by_cases hlt : lt a c = true
    · rw [if_pos hlt, if_pos hlt]
      exact (lt_eq_ltF b (phi c d) _
        (by show b.deg + (1 + c.deg + d.deg)
              ≤ 2 * ((1 + a.deg + b.deg) + (1 + c.deg + d.deg)) + 7; omega)).symm
    · rw [if_neg hlt, if_neg hlt,
        show ltF (2 * ((phi a b).deg + (phi c d).deg) + 7) (phi a b) d = lt (phi a b) d from
          (lt_eq_ltF (phi a b) d _
            (by show (1 + a.deg + b.deg) + d.deg
                  ≤ 2 * ((1 + a.deg + b.deg) + (1 + c.deg + d.deg)) + 7; omega)).symm]
      rfl

theorem le_of_lt {x y : Term} (h : lt x y = true) : le x y = true := by
  show ((x == y) || lt x y) = true
  rw [h]; exact Bool.or_true _

theorem hdLe_of_isAP : ∀ {a : Term}, a.isAP = true → ∀ c, hdLe a c = le a c
  | zero, h, _ => Bool.noConfusion h
  | add _ _, h, _ => Bool.noConfusion h
  | M, _, _ => rfl
  | omg _, _, _ => rfl
  | phi _ _, _, _ => rfl
  | psi _ _, _, _ => rfl
  | Z _, _, _ => rfl

theorem isAtom_of_isAP : ∀ {a : Term}, a.isAP = true → isAtom a = true
  | zero, h => Bool.noConfusion h
  | add _ _, h => Bool.noConfusion h
  | M, _ => rfl
  | omg _, _ => rfl
  | phi _ _, _ => rfl
  | psi _ _, _ => rfl
  | Z _, _ => rfl

theorem isPow_of_cn_isAP : ∀ {a : Term}, CN a = true → a.isAP = true → isPow a = true
  | zero, _, h => Bool.noConfusion h
  | add _ _, _, h => Bool.noConfusion h
  | M, h, _ => Bool.noConfusion h
  | omg _, h, _ => Bool.noConfusion h
  | psi _ _, h, _ => Bool.noConfusion h
  | Z _, h, _ => Bool.noConfusion h
  | phi x _, h, _ => by
    have hx : x = zero := (cn_phi h).1
    rw [hx]; rfl

/-- The descending conjunct of 2.1(iii) IS `hdLe`. -/
theorem hdLe_of_inT_add : ∀ {a b : Term}, inT (add a b) = true → hdLe b a = true := by
  intro a b h
  simp only [inT, Bool.and_eq_true] at h
  have h4 := h.2
  cases b with
  | zero => exact Bool.noConfusion h4
  | add _ _ => exact h4
  | M => exact h4
  | omg _ => exact h4
  | phi _ _ => exact h4
  | psi _ _ => exact h4
  | Z _ => exact h4

/-- A strict bound turns into a `hdLe` bound (for a nonzero left-hand side). -/
theorem hdLe_of_lt_cn : ∀ (y : Term), CN y = true → ∀ (s : Term), s ≠ zero → inT s = true →
    lt s y = true → hdLe s y = true := by
  intro y hcn s hz hin hlt
  cases s with
  | zero => exact absurd rfl hz
  | M => exact le_of_lt hlt
  | omg _ => exact le_of_lt hlt
  | phi _ _ => exact le_of_lt hlt
  | psi _ _ => exact le_of_lt hlt
  | Z _ => exact le_of_lt hlt
  | add c d =>
    obtain ⟨hap, _, _⟩ := inT_add hin
    show le c y = true
    cases y with
    | zero =>
      rw [show lt (add c d) zero = false from ltF_right_zero _ _] at hlt
      exact Bool.noConfusion hlt
    | M => exact Bool.noConfusion hcn
    | omg _ => exact Bool.noConfusion hcn
    | psi _ _ => exact Bool.noConfusion hcn
    | Z _ => exact Bool.noConfusion hcn
    | phi p q =>
      rw [lt_add_phi] at hlt
      show ((c == phi p q) || lt c (phi p q)) = true
      rw [hlt]; exact Bool.or_true _
    | add u v =>
      show ((c == add u v) || lt c (add u v)) = true
      rw [lt_atom_add (isAtom_of_isAP hap)]
      by_cases heq : add c d = add u v
      · injection heq with h1 h2
        rw [h1]
        show ((u == add u v) || ((u == u) || lt u u)) = true
        simp
      · rw [lt_add_add heq] at hlt
        by_cases hcu : c = u
        · rw [hcu]
          show ((u == add u v) || ((u == u) || lt u u)) = true
          simp
        · rw [if_neg hcu] at hlt
          show ((c == add u v) || ((c == u) || lt c u)) = true
          rw [hlt]; simp

/-- **The structural theorem.**  A term of 𝔗(M) whose head does not exceed a
    Cantor normal form is itself a Cantor normal form. -/
theorem cn_of_inT_hdLe : ∀ (n : Nat) (s c : Term), s.deg + c.deg ≤ n →
    inT s = true → CN c = true → hdLe s c = true → CN s = true := by
  intro n
  induction n with
  | zero =>
    intro s c hd _ _ _
    have := deg_pos s; have := deg_pos c; omega
  | succ n ih =>
    intro s c hd hin hcn hle
    have hjunk : ∀ (x : Term), junkAP x = true → hdLe x c = true → False := by
      intro x hx hxc
      have hx' : le x c = true := by
        cases x with
        | M => exact hxc
        | omg _ => exact hxc
        | psi _ _ => exact hxc
        | Z _ => exact hxc
        | zero => exact Bool.noConfusion hx
        | add _ _ => exact Bool.noConfusion hx
        | phi _ _ => exact Bool.noConfusion hx
      simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at hx'
      rcases hx' with h1 | h1
      · rw [h1] at hx
        cases c <;> first | exact Bool.noConfusion hx | exact Bool.noConfusion hcn
      · rw [show lt x c = false from lt_junkAP_cn c hcn _ x hx] at h1
        exact Bool.noConfusion h1
    cases s with
    | zero => rfl
    | M => exact absurd (hjunk M rfl hle) (by simp)
    | omg a => exact absurd (hjunk (omg a) rfl hle) (by simp)
    | psi k a => exact absurd (hjunk (psi k a) rfl hle) (by simp)
    | Z a => exact absurd (hjunk (Z a) rfl hle) (by simp)
    | add c' d' =>
      obtain ⟨hap, hinc, hind⟩ := inT_add hin
      have hdd : hdLe d' c' = true := hdLe_of_inT_add hin
      have hcc : hdLe c' c = true := by rw [hdLe_of_isAP hap]; exact hle
      have hdegc : c'.deg + c.deg ≤ n := by
        have := deg_pos d'
        have h2 : 1 + c'.deg + d'.deg + c.deg ≤ n + 1 := hd
        omega
      have hcnc : CN c' = true := ih c' c hdegc hinc hcn hcc
      have hdegd : d'.deg + c'.deg ≤ n := by
        have := deg_pos c
        have h2 : 1 + c'.deg + d'.deg + c.deg ≤ n + 1 := hd
        omega
      have hcnd : CN d' = true := ih d' c' hdegd hind hcnc hdd
      show (isPow c' && CN c' && CN d' && hdLe d' c') = true
      rw [hcnc, hcnd, hdd, isPow_of_cn_isAP hcnc hap]
      rfl
    | phi p q =>
      obtain ⟨hinp, hinq⟩ := inT_phi hin
      have hle' : le (phi p q) c = true := hle
      simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at hle'
      rcases hle' with h1 | h1
      · rw [h1]; exact hcn
      · cases c with
        | zero =>
          rw [show lt (phi p q) zero = false from ltF_right_zero _ _] at h1
          exact Bool.noConfusion h1
        | M => exact Bool.noConfusion hcn
        | omg _ => exact Bool.noConfusion hcn
        | psi _ _ => exact Bool.noConfusion hcn
        | Z _ => exact Bool.noConfusion hcn
        | add u v =>
          obtain ⟨_, hcnu, _, _⟩ := cn_add hcn
          rw [lt_atom_add rfl] at h1
          have hdeg : (phi p q).deg + u.deg ≤ n := by
            have := deg_pos v
            have h2 : (phi p q).deg + (1 + u.deg + v.deg) ≤ n + 1 := hd
            omega
          exact ih (phi p q) u hdeg hin hcnu h1
        | phi x b =>
          have hx : x = zero := (cn_phi hcn).1
          have hcnb : CN b = true := (cn_phi hcn).2
          subst hx
          have hne : phi p q ≠ phi zero b := by
            intro hc; rw [hc, lt_irrefl] at h1; exact Bool.noConfusion h1
          rw [lt_phi_phi hne] at h1
          by_cases hpz : p = zero
          · rw [if_pos hpz] at h1
            have hdeg : q.deg + b.deg ≤ n := by
              have := deg_pos p
              have h2 : (1 + p.deg + q.deg) + (1 + 1 + b.deg) ≤ n + 1 := hd
              omega
            have hcnq : CN q = true := by
              by_cases hqz : q = zero
              · rw [hqz]; rfl
              · exact ih q b hdeg hinq hcnb (hdLe_of_lt_cn b hcnb q hqz hinq h1)
            show ((p == zero) && CN q) = true
            rw [hcnq, hpz]
            rfl
          · rw [if_neg hpz,
              if_neg (by rw [show lt p zero = false from ltF_right_zero _ _]
                         exact Bool.noConfusion)] at h1
            have hdeg : (phi p q).deg + b.deg ≤ n := by
              have h2 : (phi p q).deg + (1 + 1 + b.deg) ≤ n + 1 := hd
              omega
            exact ih (phi p q) b hdeg hin hcnb h1

/-- **The form the cofinality proof uses.** -/
theorem cn_of_lt_cn {s y : Term} (hin : inT s = true) (hcn : CN y = true)
    (hlt : lt s y = true) : CN s = true := by
  by_cases hz : s = zero
  · rw [hz]; rfl
  · exact cn_of_inT_hdLe (s.deg + y.deg) s y (Nat.le_refl _) hin hcn
      (hdLe_of_lt_cn y hcn s hz hin hlt)

/-- …hence `Frag`, hence §7's whole order theory applies to it. -/
theorem frag_of_lt_cn {s y : Term} (hin : inT s = true) (hcn : CN y = true)
    (hlt : lt s y = true) : Frag s = true :=
  frag_of_cn s (cn_of_lt_cn hin hcn hlt)

/-! ## §14 COFINALITY of the CNF fundamental sequence  (STAGE 2b, completed)

The fourth and last clause of `Certified.lim`, for every CNF limit below ε₀ at
once.  With §13 in hand the shape of `s` is no longer a case bash over the seven
constructors: `cn_of_lt_cn` says every `s` in range is already CNF, so only `0`,
`ω^ρ` and `ξ ⊕ ρ` occur, and §7's order theory applies to all of them.

The three cases of `t` are of quite different character:

  * `t = ξ ⊕ ρ` — hand the tail to the hypothesis at `ρ`, the rest to clause
    2.3.16; no counting, no arithmetic.
  * `t = ω^β` with `β` a limit — hand the exponent to the hypothesis at `β`.  The
    `⊕` case needs `lt_fsC_step` to convert the `≤` the hypothesis returns into
    the `<` that clause 2.3.10 wants (index `n+1` instead of `n`).
  * `t = ω^(β+1)` — the only case that COUNTS: `t[n] = ω^β·(n+1)`, and the index
    is the number of components of `s`.  This is `cof_repAdd`, a separate
    induction, and it is where §12's successor inversion `le_predC_of_lt` is
    spent. -/

theorem le_pow {e a : Term} (h : le e a = true) : le (phi zero e) (phi zero a) = true := by
  simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at h ⊢
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (by rw [lt_pow]; exact h)

theorem le_zero_left {x : Term} (h : x ≠ zero) : le zero x = true :=
  le_of_lt (ltF_left_zero (by show 1 ≤ 2 * ((zero : Term).deg + x.deg) + 8; omega) h)

/-- The counting case: a CNF term below `ω^(β+1)` is a sum of at most `n+1`
    components each `≤ ω^β`, hence `≤ ω^β·(n+1)`. -/
theorem cof_repAdd : ∀ (s : Term), CN s = true → inT s = true → ∀ (b : Term),
    CN b = true → kindC b = true → lt s (phi zero b) = true →
    ∃ n, le s (repAdd (phi zero (predC b)) n) = true := by
  intro s
  induction s with
  | M => intro hcn; exact Bool.noConfusion hcn
  | omg _ _ => intro hcn; exact Bool.noConfusion hcn
  | psi _ _ _ _ => intro hcn; exact Bool.noConfusion hcn
  | Z _ _ => intro hcn; exact Bool.noConfusion hcn
  | zero =>
    intro _ _ b _ _ _
    exact ⟨0, le_zero_left (by intro h; exact Term.noConfusion h)⟩
  | phi p r _ _ =>
    intro hcn hin b hcnb hkb hlt
    have hp : p = zero := (cn_phi hcn).1
    subst hp
    rw [lt_pow] at hlt
    exact ⟨0, le_pow (le_predC_of_lt b hcnb hkb r (inT_phi hin).2 hlt)⟩
  | add c d _ ihd =>
    intro hcn hin b hcnb hkb hlt
    obtain ⟨hpow, hcnc, hcnd, _⟩ := cn_add hcn
    obtain ⟨_, hinc, hind⟩ := inT_add hin
    obtain ⟨e, he⟩ := eq_pow_of_isPow hpow
    subst he
    have hfb : Frag (phi zero b) = true := frag_of_cn _ (by
      show (((zero : Term) == zero) && CN b) = true
      rw [hcnb]; rfl)
    have hhead : lt (phi zero e) (phi zero b) = true := by rw [← lt_add_phi]; exact hlt
    have htail : lt d (phi zero b) = true := lt_tail hcn hfb hhead
    obtain ⟨n, hn⟩ := ihd hcnd hind b hcnb hkb htail
    have hce : le (phi zero e) (phi zero (predC b)) = true := by
      refine le_pow (le_predC_of_lt b hcnb hkb e (inT_phi hinc).2 ?_)
      rw [← lt_pow]; exact hhead
    refine ⟨n + 1, ?_⟩
    show le (add (phi zero e) d) (add (phi zero (predC b)) (repAdd (phi zero (predC b)) n)) = true
    simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at hce
    rcases hce with hce | hce
    · rw [hce]
      exact le_add_tail hn
    · exact le_of_lt (lt_add_head (ne_of_ltF hce) hce)

/-- **THE COFINALITY CLAUSE, for every CNF limit below ε₀.** -/
theorem cof_fsC : ∀ (t : Term), CN t = true → kindC t = false → t ≠ zero →
    ∀ s, inT s = true → lt s t = true → ∃ n, le s (fsC t n) = true := by
  intro t
  induction t with
  | M => intro hcn; exact Bool.noConfusion hcn
  | omg _ _ => intro hcn; exact Bool.noConfusion hcn
  | psi _ _ _ _ => intro hcn; exact Bool.noConfusion hcn
  | Z _ _ => intro hcn; exact Bool.noConfusion hcn
  | zero => intro _ _ hz; exact absurd rfl hz
  | phi x b _ ihb =>
    intro hcn hk _ s hins hlt
    have hx : x = zero := (cn_phi hcn).1
    have hcnb : CN b = true := (cn_phi hcn).2
    subst hx
    have hy : (b == zero) = false := hk
    have hbz : b ≠ zero := by intro h; rw [h] at hy; exact Bool.noConfusion hy
    have hcns : CN s = true := cn_of_lt_cn hins hcn hlt
    by_cases hkb : kindC b = true
    · obtain ⟨n, hn⟩ := cof_repAdd s hcns hins b hcnb hkb hlt
      exact ⟨n, by rw [fsC_phi_succ hy hkb]; exact hn⟩
    · have hkb' : kindC b = false := by simpa using hkb
      cases s with
      | M => exact Bool.noConfusion hcns
      | omg _ => exact Bool.noConfusion hcns
      | psi _ _ => exact Bool.noConfusion hcns
      | Z _ => exact Bool.noConfusion hcns
      | zero =>
        exact ⟨0, by
          rw [fsC_phi_lim hy hkb']
          exact le_zero_left (by intro h; exact Term.noConfusion h)⟩
      | phi p r =>
        have hp : p = zero := (cn_phi hcns).1
        subst hp
        rw [lt_pow] at hlt
        obtain ⟨n, hn⟩ := ihb hcnb hkb' hbz r (inT_phi hins).2 hlt
        exact ⟨n, by rw [fsC_phi_lim hy hkb']; exact le_pow hn⟩
      | add c d =>
        obtain ⟨hpow, hcnc, hcnd, _⟩ := cn_add hcns
        obtain ⟨_, hinc, _⟩ := inT_add hins
        obtain ⟨e, he⟩ := eq_pow_of_isPow hpow
        subst he
        have hhead : lt (phi zero e) (phi zero b) = true := by rw [← lt_add_phi]; exact hlt
        have hlte : lt e b = true := by rw [← lt_pow]; exact hhead
        obtain ⟨n, hn⟩ := ihb hcnb hkb' hbz e (inT_phi hinc).2 hlte
        refine ⟨n + 1, ?_⟩
        rw [fsC_phi_lim hy hkb']
        refine le_of_lt ?_
        rw [lt_add_phi, lt_pow]
        exact lt_of_le_of_lt (frag_of_cn e (cn_phi hcnc).2)
          (frag_of_cn _ (cn_fsC b hcnb hkb' hbz n))
          (frag_of_cn _ (cn_fsC b hcnb hkb' hbz (n + 1))) hn
          (lt_fsC_step b hcnb hkb' hbz n)
  | add u v _ ihv =>
    intro hcn hk _ s hins hlt
    obtain ⟨hpow, hcnu, hcnv, hdesc⟩ := cn_add hcn
    have hkv : kindC v = false := hk
    have hvz : v ≠ zero := by intro h; rw [h] at hdesc; exact Bool.noConfusion hdesc
    obtain ⟨e, he⟩ := eq_pow_of_isPow hpow
    subst he
    have hfz : fsC v 0 ≠ zero := fsC_ne_zero v hcnv hkv hvz 0
    cases s with
    | zero =>
      exact ⟨0, le_zero_left (by intro h; exact Term.noConfusion h)⟩
    | M => exact ⟨0, atom_step rfl hlt⟩
    | omg _ => exact ⟨0, atom_step rfl hlt⟩
    | psi _ _ => exact ⟨0, atom_step rfl hlt⟩
    | Z _ => exact ⟨0, atom_step rfl hlt⟩
    | phi _ _ => exact ⟨0, atom_step rfl hlt⟩
    | add c d =>
      obtain ⟨_, _, hind⟩ := inT_add hins
      by_cases heq : add c d = add (phi zero e) v
      · rw [heq, lt_irrefl] at hlt; exact Bool.noConfusion hlt
      rw [lt_add_add heq] at hlt
      by_cases hcu : c = phi zero e
      · rw [if_pos hcu] at hlt
        obtain ⟨n, hn⟩ := ihv hcnv hkv hvz d hind hlt
        exact ⟨n, by rw [hcu]; exact le_add_tail hn⟩
      · rw [if_neg hcu] at hlt
        exact ⟨0, le_of_lt (lt_add_head hcu hlt)⟩

/-! ### §14.1 The four clauses of `Certified.lim`, assembled

For every CNF limit `t` below ε₀ the sequence `fsC t` satisfies every premise of
`Certified.lim` that does not mention a matrix.  What Stage 2c still owes is the
BMS side: that `BMS.expand` of the matrix of `t` is the matrix of `fsC t n`. -/

theorem lim_clauses (t : Term) (hcn : CN t = true) (hk : kindC t = false) (hz : t ≠ zero) :
    (∀ n, CN (fsC t n) = true)
  ∧ (∀ n, lt (fsC t n) t = true)
  ∧ (∀ n, lt (fsC t n) (fsC t (n + 1)) = true)
  ∧ (∀ s, inT s = true → lt s t = true → ∃ n, le s (fsC t n) = true) :=
  ⟨cn_fsC t hcn hk hz, lt_fsC t hcn hk hz, lt_fsC_step t hcn hk hz, cof_fsC t hcn hk hz⟩

/-- Specialised to the ω-towers: the values of `(0,0)(1,1)[n]`.  `tower (k+1)` is
    a CNF limit, so `lim_clauses` applies to it verbatim. -/
theorem cn_tower : ∀ k, CN (tower k) = true
  | 0 => rfl
  | k + 1 => by
    show (((zero : Term) == zero) && CN (tower k)) = true
    rw [cn_tower k]; rfl

theorem kindC_tower : ∀ k, kindC (tower (k + 1)) = false
  | 0 => rfl
  | _ + 1 => rfl

/-! ## §8 STAGE 3 — the `ψ`/`Z` clauses: what is left  (THE MAP; STAGE 3a IS DONE)

(§9 and §10 were added later and sit ABOVE this section on purpose; the numbering
therefore runs §1–§7, §9, §10, §8.  This map used to be the file tail and was
labelled "NOTHING PROVED BELOW".  That label is no longer true and has been
removed: §8.1 pre-proved the Stage-3a rule table, and §8.2 then EXECUTED Stage 3a
in full — `Frag2` carries a strict linear order, `inT`-free.  Nothing in the MAP
ITSELF is a theorem; that part is unchanged.  What is still open below is Stage 3b,
i.e. `ψ` and `Z`.)

This is a map in the style of §6, for §6's own item 3 — the version of §7 that
`cert_sound` needs.  It is not speculation: every claim marked MEASURED comes from
an exhaustive `#eval` sweep over ALL terms of degree ≤ 7 built from all seven
constructors — 16850 of them, of which 529 satisfy `inT` — and a sample of each is
kept as a `#guard` below.  Nothing in this MAP is a theorem — but §8.2 has since
turned its Stage 3a into one, and §8.2.5's independently written enumerator
reproduces every count quoted here exactly (3042 / 16850 / 529 / 556,
duplicate-free), so the measurements below have been re-checked once.

HOW THE SWEEP CERTIFIES TRANSITIVITY WITHOUT AN `n³` LOOP.  Worth recording,
because it is what makes extending the sweep feasible at all: the direct triple
loop is `n³` and dies well before n = 529.  Instead check three `n²` properties —
`lt` is asymmetric; `lt` is total on distinct terms; and the "number of
predecessors" scores of the n terms are exactly `0,1,…,n-1`.  A tournament whose
scores are all distinct is transitive, so the three together certify a STRICT
LINEAR ORDER.  All three hold on the 529 `inT` terms of degree ≤ 7, and the
enumeration is duplicate-free (`eraseDups` changes nothing).  Use this, not a
triple loop, when pushing to degree 8.

WHAT §7 HANDS OVER UNCHANGED.

  * The proof architecture.  `cmp_aux`'s simultaneous asymmetry+comparability and
    `trans_aux`'s lexicographic measure `(b.deg, a.deg + c.deg)` are not artefacts
    of the fragment: 2.3.14 (`ψκα < ψπβ`) has exactly the same three-sub-clause
    shape as 2.3.13, so the 13(i)/13(ii)/13(iii) arguments transcribe verbatim
    with `κ` in place of `α`.
  * §7.2's style: state each clause body as a `rfl` rewrite rule first, then bash.
  * §5, and now for a second reason.  `starF f d` DEPENDS ON THE FUEL, so once the
    `ψ`/`Z` clauses are in play "same fuel" is no longer a purely syntactic notion
    and `starF_stable` is what keeps the two fuels' `α*` equal.  §5 was needed at
    the END of §7 (to lift to `lt`); in §8 it is needed in the MIDDLE.
  * `deg_starF` (§5) is what keeps the measure working: `α*` is a subterm of `α`,
    so the clauses that recurse into `starF f d` do not raise any degree.

WHAT CHANGES, AND THE MEASUREMENTS THAT SAY SO.

 1. STAGE 3 IS TRUE.  MEASURED: the 529 terms of degree ≤ 7 satisfying `inT` carry
    a strict linear order under `lt` — asymmetric, total, and transitive (by the
    score argument above), with no exception.  It is a cost question, not a risk
    question.

 2. `inT` BECOMES NECESSARY — the situation inverts.  On `Frag`, `inT` is dead
    weight (§7 proves everything without it).  Off `Frag` it is indispensable:
    MEASURED, the raw language has 792 incomparable pairs among those 3042 terms,
    and ZERO of them satisfy `inT`.  (Asymmetry, by contrast, held everywhere,
    `inT` or not — but §7's route to asymmetry goes through comparability, so
    that observation does not by itself make asymmetry cheaper.)

    CORRECTION (2026-08-09, Phase B): the parenthetical is FALSE as stated.  It is
    a degree ≤ 6 measurement and it does not survive degree 7 — the gate sweep
    found 68 unordered violating pairs there, the smallest being `φ̄(ψ_M M)M` and
    `φ̄(ψ_(ψ_M M)0)M`, of degrees 5 and 7, which is exactly why a degree-6 sweep
    cannot see it.  Both are BELOW each other.  `lt_not_asymm_raw` in §8.5.5 is
    that witness as a theorem, and raw `lt` is not transitive either
    (`lt_not_trans_raw`, a degree ≤ 6 witness).  Every one of these terms fails
    `inT` — and fails `FragR` — at exactly the `κ ∈ R` conjunct, so nothing above
    or in §8.5 depends on the retracted sentence; it is further evidence that
    `κ ∈ R` is the right restriction.  Read the sentence as: "asymmetry held
    everywhere AT DEGREE ≤ 6".

 3. AND IT IS ESSENTIALLY ONE CLAUSE OF `inT`.  Re-running the sweep with single
    conditions of [R91] 2.1 deleted (terms admitted / incomparable pairs /
    transitivity violations):

        inT as written                        171 /   0 /  0
        2.1(vi) without  κ ∈ R                320 / 106 / 15     <-- load-bearing
        2.1(vi) without  α < M                193 /   0 /  0
        2.1(iii) without αₙ ≤ … ≤ α₁          263 /   0 /  0

    So the order theory of §8 needs `k.isR` from 2.1(vi) and, at this depth,
    nothing else.  That is much cheaper than §6 budgeted: the `inT` destructor
    actually required is the `κ ∈ R` conjunct, not the sum machinery.
    K_κ: THE CAVEAT IS NOW RESOLVED (2026-08-09, ψ/Z lane).  It used to read "the
    K_κ conjunct could not be tested this way — it removes no term at degree ≤ 6
    (171 either way) and still none at degree ≤ 7 (529 either way), so the sweep
    says NOTHING about K_κ; it is UNTESTED".  Pushing the sweep to degree 8 makes
    it bite, exactly as that note predicted it eventually would:

        degree ≤ 8:   95730 terms,  inT admits 1687,  inT-without-K_κ admits 1691

    so K_κ removes FOUR terms, the first four in the language.  All four have the
    shape ψ_κ(ψ_π γ) with κ, π ∈ {Z0, ZM}:

        ψ_(Z0)(ψ_(Z0)(Z0))   ψ_(Z0)(ψ_(Z0)(ZM))
        ψ_(Z0)(ψ_(ZM)(ZM))   ψ_(ZM)(ψ_(ZM)(ZM))

    and each is rejected for the same reason — e.g. for the first, `Kset (Z0) α`
    with α = ψ_(Z0)(Z0) is `[Z0]`, and `Z0 < α` is FALSE, so 2.1(vi)'s `K_κ α < α`
    fails.  K_κ is therefore NOT dead weight: it is load-bearing for ADMISSION.

    HONEST CAVEAT, in its new and weaker form: K_κ is not (yet) known to matter for
    the ORDER.  MEASURED at degree ≤ 8: those four extra terms create ZERO
    incomparable pairs and ZERO transitivity violations inside the K_κ-free
    language.  So Stage 3b may well go through without destructing K_κ — but that
    is a measurement at degree 8, not a theorem, and the conjunct now demonstrably
    does something, which it did not before.

 4. THE SPLIT THAT MAKES §8 TRACTABLE.  MEASURED: on the sub-language with `M`
    and `ω̄` but still no `ψ`/`Z` (556 terms of degree ≤ 6), asymmetry and
    comparability hold RAW — no `inT` needed, exactly as in `Frag`.  So:

      STAGE 3a  extend `Frag` to `Frag ∪ {M, ω̄}`, still `inT`-free.  DONE — §8.2.
                The prediction that it goes through `inT`-free was correct.  The
                cost prediction was PESSIMISTIC, and it is worth recording why, in
                case Stage 3b can use the same trick: the feared blow-up (`cmp_aux`
                from 9 shape pairs to 25, `trans_aux` from 27 triples to 125) does
                not happen, because neither number is forced.  2.3.10 / 2.3.11 do
                not look at WHICH non-sum they are handed, so the sum clauses are
                stated ONCE against an opaque non-sum and the case analysis still
                splits three ways (0 / sum / non-sum) exactly as §7 did; and among
                non-sums the order is by LEVEL, so `a < b < c` pins all three to one
                level and only 7 of the 27 shape triples are reachable, six of them
                with a constant-clause conclusion.  §7.4's eight sum-involving
                triples then transcribe verbatim with `φ̄rs` replaced by a variable.

      STAGE 3b  `ψ` and `Z`, with `inT`.  This is where the real work is: the
                clauses routing through `starF` (2.3.6 / 2.3.8 / 2.3.9 / 2.3.15)
                need, beyond §7's pattern, that `α*` behaves.  MEASURED on all 171
                `inT` terms: `le (star d) d` and `star d ≤ Z d` both hold — those
                are precisely the two `starF` facts §6's map asked for, and they
                are the first things to prove in 3b.

WHAT WOULD FALSIFY THIS MAP: a pair of `inT` terms of degree ≥ 8 that is
incomparable, or a `starF` counterexample to `le (star d) d`.

THE DEGREE-8 SWEEP HAS NOW BEEN RUN (2026-08-09, ψ/Z lane), as this paragraph asked
before 3b is started.  It PASSES: of the 95730 terms of degree ≤ 8, 1687 satisfy
`inT`, and on those 1687 `lt` is asymmetric, total on distinct terms, and its
predecessor-scores are the 1687 distinct values 0,…,1686 — the tournament
certificate for a strict linear order, with a duplicate-free enumeration.  So item
1 (STAGE 3 IS TRUE) survives its first real test above the degree it was calibrated
at, the term count having gone 529 → 1687.  Item 3's K_κ caveat did NOT survive
unchanged and has been rewritten above: at degree 8 K_κ finally bites. -/

/-! ### §8.1 The Stage-3a rewrite-rule table, pre-proved

§8 item 4 says the cost of Stage 3a is the shape matrix, not the mathematics, and
recommends factoring out the constant clauses before bashing.  Here is that
factoring, done and machine-checked, so 3a starts from a complete rule table
instead of re-deriving one: `M` and `ω̄` against every other shape.  Every rule
below is `rfl` — 2.3.2 / 2.3.3 / 2.3.12 really are constant clauses — except
`ω̄`-vs-`ω̄`, which needs distinctness exactly as `ltF_succ_add_add` does.

Read together they say: on non-sums the order is by LEVEL, `φ̄/ψ/Z  <  M  <  ω̄^·`,
with ties broken inside the level; and a sum still compares by its head.  That is
the shape of the 3a induction. -/

/-- The Stage-3a fragment: `Frag` plus `M` and `ω̄`, i.e. everything except `ψ`/`Z`.
    MEASURED (§8 item 4): on the 556 such terms of degree ≤ 6, `lt` is asymmetric
    and total with NO `inT` hypothesis — so 3a should go through `inT`-free, like
    §7 and unlike 3b. -/
def Frag2 : Term → Bool
  | zero => true
  | M => true
  | add a b => Frag2 a && Frag2 b
  | omg a => Frag2 a
  | phi a b => Frag2 a && Frag2 b
  | psi _ _ => false
  | Z _ => false

theorem frag_le_frag2 : ∀ (t : Term), Frag t = true → Frag2 t = true
  | zero, _ => rfl
  | M, h => by simp [Frag] at h
  | omg _, h => by simp [Frag] at h
  | psi _ _, h => by simp [Frag] at h
  | Z _, h => by simp [Frag] at h
  | add a b, h => by
    have hab := frag_add h
    show (Frag2 a && Frag2 b) = true
    rw [frag_le_frag2 a hab.1, frag_le_frag2 b hab.2]; rfl
  | phi a b, h => by
    have hab := frag_phi h
    show (Frag2 a && Frag2 b) = true
    rw [frag_le_frag2 a hab.1, frag_le_frag2 b hab.2]; rfl

/-! 2.3.3 and 2.3.2: `M` against everything.  `M < ω̄^γ`, and `φ̄ , ψ , Z < M`. -/
theorem ltF_succ_M_omg (f : Nat) (x : Term) : ltF (f + 1) M (omg x) = true := rfl
theorem ltF_succ_M_phi (f : Nat) (c d : Term) : ltF (f + 1) M (phi c d) = false := rfl
theorem ltF_succ_M_psi (f : Nat) (k a : Term) : ltF (f + 1) M (psi k a) = false := rfl
theorem ltF_succ_M_Z (f : Nat) (a : Term) : ltF (f + 1) M (Z a) = false := rfl
theorem ltF_succ_phi_M (f : Nat) (a b : Term) : ltF (f + 1) (phi a b) M = true := rfl
theorem ltF_succ_psi_M (f : Nat) (k a : Term) : ltF (f + 1) (psi k a) M = true := rfl
theorem ltF_succ_Z_M (f : Nat) (a : Term) : ltF (f + 1) (Z a) M = true := rfl
theorem ltF_succ_omg_M (f : Nat) (x : Term) : ltF (f + 1) (omg x) M = false := rfl

/-! `ω̄^·` sits above `M`, hence above every `φ̄`, `ψ`, `Z`. -/
theorem ltF_succ_omg_phi (f : Nat) (x c d : Term) : ltF (f + 1) (omg x) (phi c d) = false := rfl
theorem ltF_succ_omg_psi (f : Nat) (x k a : Term) : ltF (f + 1) (omg x) (psi k a) = false := rfl
theorem ltF_succ_omg_Z (f : Nat) (x a : Term) : ltF (f + 1) (omg x) (Z a) = false := rfl
theorem ltF_succ_phi_omg (f : Nat) (a b y : Term) : ltF (f + 1) (phi a b) (omg y) = true := rfl
theorem ltF_succ_psi_omg (f : Nat) (k a y : Term) : ltF (f + 1) (psi k a) (omg y) = true := rfl
theorem ltF_succ_Z_omg (f : Nat) (a y : Term) : ltF (f + 1) (Z a) (omg y) = true := rfl

/-- 2.3.12: `M < γ < δ ⟹ ω̄^γ < ω̄^δ`.  The one Stage-3a rule that is not `rfl`. -/
theorem ltF_succ_omg_omg (f : Nat) {x y : Term} (h : omg x ≠ omg y) :
    ltF (f + 1) (omg x) (omg y) = ltF f x y := by
  show (if (omg x == omg y) = true then false else ltF f x y) = _
  rw [if_neg (by simpa using h)]

/-! 2.3.10 / 2.3.11 for the two new shapes: a sum still compares by its head. -/
theorem ltF_succ_M_add (f : Nat) (c d : Term) :
    ltF (f + 1) M (add c d) = ((M : Term) == c || ltF f M c) := rfl
theorem ltF_succ_add_M (f : Nat) (a b : Term) : ltF (f + 1) (add a b) M = ltF f a M := rfl
theorem ltF_succ_omg_add (f : Nat) (x c d : Term) :
    ltF (f + 1) (omg x) (add c d) = ((omg x == c) || ltF f (omg x) c) := rfl
theorem ltF_succ_add_omg (f : Nat) (a b y : Term) :
    ltF (f + 1) (add a b) (omg y) = ltF f a (omg y) := rfl

/-! ### §8.2 STAGE 3a, EXECUTED: `Frag2` carries a strict linear order

WHAT IS PROVED.  Everything §7 proves for `Frag`, now for `Frag2` — §8.1's
fragment, i.e. `Frag` extended by `M` and `ω̄^·` — and still with NO `inT`
hypothesis, exactly as §8 item 4 predicted from the 556 terms of degree ≤ 6.  The
names carry the suffix `2`: `ltF_asymm2`, `ltF_comparable2`, `trans_ltF2`,
`lt_asymm2`, `lt_comparable2`, `lt_trans2`, `lt_trichotomy2`, `le_trans2`, and the
two inversions `le_of_not_lt2` / `lt_of_not_le2`.  §7's theorems are the special
case `Frag ⊆ Frag2` (`frag_le_frag2`), so nothing that consumes §7 changes.

HOW THE 25 SHAPE PAIRS AND 125 SHAPE TRIPLES ARE AVOIDED.  §8 item 4 warned that
a naive extension triples the file for no content.  Two observations collapse it.

  * 2.3.10 / 2.3.11 DO NOT LOOK AT WHICH non-sum they are handed — a sum is below
    a non-sum iff its head is, and a non-sum is below a sum iff it is `≤` the
    head.  So the sum clauses are stated ONCE against an opaque non-sum
    (`ltF_succ_add_nsum` / `ltF_succ_nsum_add`), and the case analysis still splits
    `a`, `b`, `c` only three ways — `0`, a sum, a non-sum — exactly as §7 did.  The
    eight sum-involving triples of §7.4 then transcribe verbatim, with `φ̄rs`
    replaced by a variable.
  * Among non-sums the order is by LEVEL (§8.1's table: `φ̄ < M < ω̄^·`), and the
    level is a function of the SHAPE alone.  In the transitivity case where all
    three are non-sums, `a < b < c` therefore pins all three to one level (the
    level can only go up, and it must return), so of the 27 shape triples only
    SEVEN are reachable and six of those have a constant-clause conclusion.  The
    only one with content is `φ̄/φ̄/φ̄` — §7.4's case (8), unchanged — plus
    `ω̄/ω̄/ω̄`, which is a single application of 2.3.12.

WHAT IS STILL OPEN: `ψ` and `Z`, i.e. §8's Stage 3b.  Those clauses route through
`starF` and, unlike everything here, genuinely need `inT` (§8 item 2). -/

/-- `t` is not a sum.  2.3.10 / 2.3.11 treat every non-sum alike, so this is the
    only distinction the sum clauses of 2.3 make, and stating them against `NSum`
    is what keeps the case analysis of §8.2 the same size as §7's. -/
def NSum : Term → Bool
  | zero => true
  | M => true
  | add _ _ => false
  | omg _ => true
  | phi _ _ => true
  | psi _ _ => true
  | Z _ => true

/-! `Frag2` is hereditary, exactly as `Frag` is (§7). -/

theorem frag2_add {a b : Term} (h : Frag2 (add a b) = true) :
    Frag2 a = true ∧ Frag2 b = true := by
  simp only [Frag2, Bool.and_eq_true] at h; exact h

theorem frag2_omg {a : Term} (h : Frag2 (omg a) = true) : Frag2 a = true := h

theorem frag2_phi {a b : Term} (h : Frag2 (phi a b) = true) :
    Frag2 a = true ∧ Frag2 b = true := by
  simp only [Frag2, Bool.and_eq_true] at h; exact h

/-- 2.3.10 against an ARBITRARY non-sum: the sum is decided by its head. -/
theorem ltF_succ_add_nsum (f : Nat) {a b t : Term} (h0 : t ≠ zero) (ht : NSum t = true) :
    ltF (f + 1) (add a b) t = ltF f a t := by
  cases t with
  | zero => exact absurd rfl h0
  | add c d => simp [NSum] at ht
  | M => rfl
  | omg _ => rfl
  | phi _ _ => rfl
  | psi _ _ => rfl
  | Z _ => rfl

/-- 2.3.11 against an ARBITRARY non-sum: it is below the sum iff it is `≤` the head. -/
theorem ltF_succ_nsum_add (f : Nat) {s c d : Term} (h0 : s ≠ zero) (hs : NSum s = true) :
    ltF (f + 1) s (add c d) = ((s == c) || ltF f s c) := by
  cases s with
  | zero => exact absurd rfl h0
  | add a b => simp [NSum] at hs
  | M => rfl
  | omg _ => rfl
  | phi _ _ => rfl
  | psi _ _ => rfl
  | Z _ => rfl

/-- The three-way split every induction of §8.2 begins with: `0`, a sum, or a
    non-sum.  This is the same trichotomy §7's `frag_cases` gave, with the four
    non-sum shapes of `Frag2` left packed. -/
theorem frag2_sum_cases {t : Term} (h : Frag2 t = true) :
    t = zero
    ∨ (∃ x y, t = add x y ∧ Frag2 x = true ∧ Frag2 y = true)
    ∨ (t ≠ zero ∧ NSum t = true) := by
  cases t with
  | zero => exact Or.inl rfl
  | add x y => exact Or.inr (Or.inl ⟨x, y, rfl, (frag2_add h).1, (frag2_add h).2⟩)
  | M => exact Or.inr (Or.inr ⟨by intro hc; exact Term.noConfusion hc, rfl⟩)
  | omg x => exact Or.inr (Or.inr ⟨by intro hc; exact Term.noConfusion hc, rfl⟩)
  | phi x y => exact Or.inr (Or.inr ⟨by intro hc; exact Term.noConfusion hc, rfl⟩)
  | psi k x => simp [Frag2] at h
  | Z x => simp [Frag2] at h

/-- Inside the non-zero non-sums of `Frag2` there are exactly three shapes, and
    §8.1's table orders them by level: `φ̄ < M < ω̄^·`. -/
theorem frag2_nsum_cases {t : Term} (h : Frag2 t = true) (h0 : t ≠ zero)
    (hn : NSum t = true) :
    t = M
    ∨ (∃ x, t = omg x ∧ Frag2 x = true)
    ∨ (∃ x y, t = phi x y ∧ Frag2 x = true ∧ Frag2 y = true) := by
  cases t with
  | zero => exact absurd rfl h0
  | add x y => simp [NSum] at hn
  | M => exact Or.inl rfl
  | omg x => exact Or.inr (Or.inl ⟨x, rfl, frag2_omg h⟩)
  | phi x y => exact Or.inr (Or.inr ⟨x, y, rfl, (frag2_phi h).1, (frag2_phi h).2⟩)
  | psi k x => simp [Frag2] at h
  | Z x => simp [Frag2] at h

/-! #### §8.2.1 Asymmetry and comparability on `Frag2`

The same simultaneous induction as §7.3, for the same reason (each half consumes
the other at strictly smaller degree).  Only the innermost block — the two terms
are non-sums of the same level — is new, and of its nine shape pairs seven are a
constant clause of §8.1. -/

private theorem cmp_aux2 : ∀ (n : Nat),
    (∀ (a b : Term), Frag2 a = true → Frag2 b = true → a.deg + b.deg ≤ n →
      ∀ f, n ≤ f → ltF f a b = true → ltF f b a = false)
  ∧ (∀ (a b : Term), Frag2 a = true → Frag2 b = true → a.deg + b.deg ≤ n →
      ∀ f, n ≤ f → (ltF f a b = true ∨ a = b ∨ ltF f b a = true))
  | 0 => ⟨by
      intro a b _ _ hd
      have := deg_pos a; have := deg_pos b; omega, by
      intro a b _ _ hd
      have := deg_pos a; have := deg_pos b; omega⟩
  | n + 1 => by
    obtain ⟨IHa, IHc⟩ := cmp_aux2 n
    constructor
    -- ============================ ASYMMETRY ============================
    · intro a b hfa hfb hd f hf h
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hf' : n ≤ f' := by omega
      have hab : a ≠ b := ne_of_ltF h
      have da := deg_pos a; have db := deg_pos b
      rcases frag2_sum_cases hfa with rfl | ⟨p, q, rfl, hfp, hfq⟩ | ⟨ha0, hna⟩
      · exact ltF_right_zero _ b
      · -- `a` is a sum
        have dp := deg_pos p; have dq := deg_pos q
        have eA : (add p q).deg = 1 + p.deg + q.deg := rfl
        rcases frag2_sum_cases hfb with rfl | ⟨r, s, rfl, hfr, hfs⟩ | ⟨hb0, hnb⟩
        · rw [ltF_right_zero] at h; exact Bool.noConfusion h
        · -- 2.3.16 against 2.3.16
          have dr := deg_pos r; have ds := deg_pos s
          have eB : (add r s).deg = 1 + r.deg + s.deg := rfl
          rw [ltF_succ_add_add _ hab] at h
          rw [ltF_succ_add_add _ (Ne.symm hab)]
          by_cases hpr : p = r
          · subst hpr
            rw [if_pos rfl] at h
            rw [if_pos rfl]
            exact IHa q s hfq hfs (by omega) f' hf' h
          · rw [if_neg hpr] at h
            rw [if_neg (Ne.symm hpr)]
            exact IHa p r hfp hfr (by omega) f' hf' h
        · -- 2.3.10 forward, 2.3.11 backward — `b` is opaque
          rw [ltF_succ_add_nsum _ hb0 hnb] at h
          rw [ltF_succ_nsum_add _ hb0 hnb]
          have hne : b ≠ p := by
            intro hc; rw [hc, ltF_irrefl] at h; exact Bool.noConfusion h
          have h2 : ltF f' b p = false := IHa p b hfp hfb (by omega) f' hf' h
          simp [hne, h2]
      · -- `a` is a non-sum
        rcases frag2_sum_cases hfb with rfl | ⟨r, s, rfl, hfr, hfs⟩ | ⟨hb0, hnb⟩
        · rw [ltF_right_zero] at h; exact Bool.noConfusion h
        · -- 2.3.11 forward, 2.3.10 backward
          have dr := deg_pos r; have ds := deg_pos s
          have eB : (add r s).deg = 1 + r.deg + s.deg := rfl
          rw [ltF_succ_nsum_add _ ha0 hna] at h
          rw [ltF_succ_add_nsum _ ha0 hna]
          simp only [Bool.or_eq_true, beq_iff_eq] at h
          rcases h with h1 | h1
          · rw [← h1]; exact ltF_irrefl _ _
          · exact IHa a r hfa hfr (by omega) f' hf' h1
        · -- both non-sums: §8.1's level table, then the two same-level clauses
          rcases frag2_nsum_cases hfa ha0 hna with rfl | ⟨x, rfl, hfx⟩ | ⟨p, q, rfl, hfp, hfq⟩
          · rcases frag2_nsum_cases hfb hb0 hnb with rfl | ⟨y, rfl, hfy⟩ | ⟨r, s, rfl, hfr, hfs⟩
            · exact absurd rfl hab
            · exact ltF_succ_omg_M _ _
            · rw [ltF_succ_M_phi] at h; exact Bool.noConfusion h
          · rcases frag2_nsum_cases hfb hb0 hnb with rfl | ⟨y, rfl, hfy⟩ | ⟨r, s, rfl, hfr, hfs⟩
            · rw [ltF_succ_omg_M] at h; exact Bool.noConfusion h
            · -- 2.3.12
              have dx := deg_pos x; have dy := deg_pos y
              have eA : (omg x).deg = 1 + x.deg := rfl
              have eB : (omg y).deg = 1 + y.deg := rfl
              rw [ltF_succ_omg_omg _ hab] at h
              rw [ltF_succ_omg_omg _ (Ne.symm hab)]
              exact IHa x y hfx hfy (by omega) f' hf' h
            · rw [ltF_succ_omg_phi] at h; exact Bool.noConfusion h
          · rcases frag2_nsum_cases hfb hb0 hnb with rfl | ⟨y, rfl, hfy⟩ | ⟨r, s, rfl, hfr, hfs⟩
            · exact ltF_succ_M_phi _ _ _
            · exact ltF_succ_omg_phi _ _ _ _
            · -- 2.3.13, exactly §7.3's block
              have dp := deg_pos p; have dq := deg_pos q
              have dr := deg_pos r; have ds := deg_pos s
              rw [ltF_succ_phi_phi _ hab] at h
              rw [ltF_succ_phi_phi _ (Ne.symm hab)]
              simp only [Term.deg] at hd
              by_cases hpr : p = r
              · subst hpr
                rw [if_pos rfl] at h
                rw [if_pos rfl]
                exact IHa q s hfq hfs (by omega) f' hf' h
              · rw [if_neg hpr] at h
                rw [if_neg (Ne.symm hpr)]
                by_cases hlt : ltF f' p r = true
                · rw [if_pos hlt] at h
                  have hrp : ltF f' r p = false := IHa p r hfp hfr (by omega) f' hf' hlt
                  rw [if_neg (by simp [hrp])]
                  have hne : phi r s ≠ q := by
                    intro hc; rw [hc, ltF_irrefl] at h; exact Bool.noConfusion h
                  have h2 : ltF f' (phi r s) q = false :=
                    IHa q (phi r s) hfq hfb (by simp only [Term.deg]; omega) f' hf' h
                  simp [hne, h2]
                · rw [if_neg hlt] at h
                  have hrp : ltF f' r p = true := by
                    rcases IHc p r hfp hfr (by omega) f' hf' with h1 | h1 | h1
                    · exact absurd h1 hlt
                    · exact absurd h1 hpr
                    · exact h1
                  rw [if_pos hrp]
                  simp only [Bool.or_eq_true, beq_iff_eq] at h
                  rcases h with h1 | h1
                  · rw [← h1]; exact ltF_irrefl _ _
                  · exact IHa (phi p q) s hfa hfs (by simp only [Term.deg]; omega) f' hf' h1
    -- ========================== COMPARABILITY ==========================
    · intro a b hfa hfb hd f hf
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hf' : n ≤ f' := by omega
      have da := deg_pos a; have db := deg_pos b
      by_cases hab : a = b
      · exact Or.inr (Or.inl hab)
      rcases frag2_sum_cases hfa with rfl | ⟨p, q, rfl, hfp, hfq⟩ | ⟨ha0, hna⟩
      · exact Or.inl (ltF_left_zero (by omega) (Ne.symm hab))
      · have dp := deg_pos p; have dq := deg_pos q
        have eA : (add p q).deg = 1 + p.deg + q.deg := rfl
        rcases frag2_sum_cases hfb with rfl | ⟨r, s, rfl, hfr, hfs⟩ | ⟨hb0, hnb⟩
        · exact Or.inr (Or.inr
            (ltF_left_zero (by omega) (by intro hc; exact Term.noConfusion hc)))
        · have dr := deg_pos r; have ds := deg_pos s
          have eB : (add r s).deg = 1 + r.deg + s.deg := rfl
          rw [ltF_succ_add_add _ hab, ltF_succ_add_add _ (Ne.symm hab)]
          by_cases hpr : p = r
          · subst hpr
            rw [if_pos rfl, if_pos rfl]
            have hqs : q ≠ s := fun hc => hab (by rw [hc])
            rcases IHc q s hfq hfs (by omega) f' hf' with h1 | h1 | h1
            · exact Or.inl h1
            · exact absurd h1 hqs
            · exact Or.inr (Or.inr h1)
          · rw [if_neg hpr, if_neg (Ne.symm hpr)]
            rcases IHc p r hfp hfr (by omega) f' hf' with h1 | h1 | h1
            · exact Or.inl h1
            · exact absurd h1 hpr
            · exact Or.inr (Or.inr h1)
        · rw [ltF_succ_add_nsum _ hb0 hnb, ltF_succ_nsum_add _ hb0 hnb]
          rcases IHc p b hfp hfb (by omega) f' hf' with h1 | h1 | h1
          · exact Or.inl h1
          · exact Or.inr (Or.inr (by simp [h1]))
          · exact Or.inr (Or.inr (by simp [h1]))
      · rcases frag2_sum_cases hfb with rfl | ⟨r, s, rfl, hfr, hfs⟩ | ⟨hb0, hnb⟩
        · exact Or.inr (Or.inr (ltF_left_zero (by omega) ha0))
        · have dr := deg_pos r; have ds := deg_pos s
          have eB : (add r s).deg = 1 + r.deg + s.deg := rfl
          rw [ltF_succ_nsum_add _ ha0 hna, ltF_succ_add_nsum _ ha0 hna]
          rcases IHc a r hfa hfr (by omega) f' hf' with h1 | h1 | h1
          · exact Or.inl (by simp [h1])
          · exact Or.inl (by simp [h1])
          · exact Or.inr (Or.inr h1)
        · -- both non-sums
          rcases frag2_nsum_cases hfa ha0 hna with rfl | ⟨x, rfl, hfx⟩ | ⟨p, q, rfl, hfp, hfq⟩
          · rcases frag2_nsum_cases hfb hb0 hnb with rfl | ⟨y, rfl, hfy⟩ | ⟨r, s, rfl, hfr, hfs⟩
            · exact absurd rfl hab
            · exact Or.inl (ltF_succ_M_omg _ _)
            · exact Or.inr (Or.inr (ltF_succ_phi_M _ _ _))
          · rcases frag2_nsum_cases hfb hb0 hnb with rfl | ⟨y, rfl, hfy⟩ | ⟨r, s, rfl, hfr, hfs⟩
            · exact Or.inr (Or.inr (ltF_succ_M_omg _ _))
            · have dx := deg_pos x; have dy := deg_pos y
              have eA : (omg x).deg = 1 + x.deg := rfl
              have eB : (omg y).deg = 1 + y.deg := rfl
              rw [ltF_succ_omg_omg _ hab, ltF_succ_omg_omg _ (Ne.symm hab)]
              have hxy : x ≠ y := fun hc => hab (by rw [hc])
              rcases IHc x y hfx hfy (by omega) f' hf' with h1 | h1 | h1
              · exact Or.inl h1
              · exact absurd h1 hxy
              · exact Or.inr (Or.inr h1)
            · exact Or.inr (Or.inr (ltF_succ_phi_omg _ _ _ _))
          · rcases frag2_nsum_cases hfb hb0 hnb with rfl | ⟨y, rfl, hfy⟩ | ⟨r, s, rfl, hfr, hfs⟩
            · exact Or.inl (ltF_succ_phi_M _ _ _)
            · exact Or.inl (ltF_succ_phi_omg _ _ _ _)
            · -- 2.3.13, exactly §7.3's block
              have dp := deg_pos p; have dq := deg_pos q
              have dr := deg_pos r; have ds := deg_pos s
              rw [ltF_succ_phi_phi _ hab, ltF_succ_phi_phi _ (Ne.symm hab)]
              simp only [Term.deg] at hd
              by_cases hpr : p = r
              · subst hpr
                rw [if_pos rfl, if_pos rfl]
                have hqs : q ≠ s := fun hc => hab (by rw [hc])
                rcases IHc q s hfq hfs (by omega) f' hf' with h1 | h1 | h1
                · exact Or.inl h1
                · exact absurd h1 hqs
                · exact Or.inr (Or.inr h1)
              · rw [if_neg hpr, if_neg (Ne.symm hpr)]
                rcases IHc p r hfp hfr (by omega) f' hf' with h1 | h1 | h1
                · have hrp : ltF f' r p = false := IHa p r hfp hfr (by omega) f' hf' h1
                  rw [if_pos h1, if_neg (by simp [hrp])]
                  rcases IHc q (phi r s) hfq hfb (by simp only [Term.deg]; omega) f' hf'
                    with h2 | h2 | h2
                  · exact Or.inl h2
                  · exact Or.inr (Or.inr (by simp [h2]))
                  · exact Or.inr (Or.inr (by simp [h2]))
                · exact absurd h1 hpr
                · have hpr2 : ltF f' p r = false := IHa r p hfr hfp (by omega) f' hf' h1
                  rw [if_neg (by simp [hpr2]), if_pos h1]
                  rcases IHc (phi p q) s hfa hfs (by simp only [Term.deg]; omega) f' hf'
                    with h2 | h2 | h2
                  · exact Or.inl (by simp [h2])
                  · exact Or.inl (by simp [h2])
                  · exact Or.inr (Or.inr h2)

/-- **ASYMMETRY on `Frag2`**, same fuel.  §7's `ltF_asymm` with `M` and `ω̄^·`
    admitted, still with no `inT` hypothesis. -/
theorem ltF_asymm2 {a b : Term} (hfa : Frag2 a = true) (hfb : Frag2 b = true)
    {f : Nat} (hf : a.deg + b.deg ≤ f) (h : ltF f a b = true) : ltF f b a = false :=
  (cmp_aux2 (a.deg + b.deg)).1 a b hfa hfb (Nat.le_refl _) f hf h

/-- **COMPARABILITY on `Frag2`**, same fuel. -/
theorem ltF_comparable2 {a b : Term} (hfa : Frag2 a = true) (hfb : Frag2 b = true)
    {f : Nat} (hf : a.deg + b.deg ≤ f) :
    ltF f a b = true ∨ a = b ∨ ltF f b a = true :=
  (cmp_aux2 (a.deg + b.deg)).2 a b hfa hfb (Nat.le_refl _) f hf

/-! #### §8.2.2 Transitivity on `Frag2`

The measure is §7.4's lexicographic pair `(b.deg, a.deg + c.deg)`, unchanged, and
for the same reason: the flat sum still fails on 13(iii)-against-13(iii).  `TR1`
and `TR2` are §7.4's two induction hypotheses verbatim.

The eight sum-involving shape triples of §7.4 reappear here with the non-sums left
as VARIABLES — that is the whole saving.  The all-non-sum case is new, and is
where §8.1's level table does the work: `a < b` forbids the level of `a` from
exceeding that of `b`, so `a < b < c` with `a`, `c` on the same level pins `b`
there too, and only `φ̄/φ̄/φ̄` and `ω̄/ω̄/ω̄` survive with anything to prove. -/

private theorem trans_aux2 : ∀ (n : Nat) (m : Nat) (a b c : Term),
    Frag2 a = true → Frag2 b = true → Frag2 c = true →
    b.deg ≤ n → a.deg + c.deg ≤ m →
    ∀ f, a.deg + b.deg + c.deg ≤ f →
    ltF f a b = true → ltF f b c = true → ltF f a c = true
  | 0 => by
    intro _ _ b _ _ _ _ hb _ _ _ _ _
    exfalso; have := deg_pos b; omega
  | n + 1 => by
    intro m
    induction m with
    | zero =>
      intro a _ c _ _ _ _ hm _ _ _ _
      exfalso; have := deg_pos a; have := deg_pos c; omega
    | succ m ihm =>
      intro a b c hfa hfb hfc hb hm f hf h1 h2
      have TR1 : ∀ (x y z : Term), Frag2 x = true → Frag2 y = true → Frag2 z = true →
          y.deg ≤ n → ∀ g, x.deg + y.deg + z.deg ≤ g →
          ltF g x y = true → ltF g y z = true → ltF g x z = true :=
        fun x y z hx hy hz hyd g hg =>
          trans_aux2 n (x.deg + z.deg) x y z hx hy hz hyd (Nat.le_refl _) g hg
      have TR2 : ∀ (x z : Term), Frag2 x = true → Frag2 z = true →
          x.deg + z.deg ≤ m → ∀ g, x.deg + b.deg + z.deg ≤ g →
          ltF g x b = true → ltF g b z = true → ltF g x z = true :=
        fun x z hx hz hd g hg => ihm x b z hx hfb hz hb hd g hg
      have da := deg_pos a; have db := deg_pos b; have dc := deg_pos c
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have LOW : ∀ (x y : Term), x.deg + y.deg ≤ f' →
          ltF (f' + 1) x y = true → ltF f' x y = true := by
        intro x y hxy h
        rw [ltF_stable x y f' (f' + 1) hxy (by omega)]; exact h
      have UP : ∀ (x y : Term), x.deg + y.deg ≤ f' →
          ltF f' x y = true → ltF (f' + 1) x y = true := by
        intro x y hxy h
        rw [ltF_stable x y (f' + 1) f' (by omega) hxy]; exact h
      have hbz : b ≠ zero := by
        intro hc; rw [hc, ltF_right_zero] at h1; exact Bool.noConfusion h1
      have hcz : c ≠ zero := by
        intro hc; rw [hc, ltF_right_zero] at h2; exact Bool.noConfusion h2
      have hac : a ≠ c := by
        intro hc; subst hc
        rw [ltF_asymm2 hfa hfb (by omega) h1] at h2; exact Bool.noConfusion h2
      rcases frag2_sum_cases hfa with rfl | ⟨p, q, rfl, hfp, hfq⟩ | ⟨ha0, hna⟩
      · exact ltF_left_zero (by omega) hcz
      · -- `a` is a sum
        have dp := deg_pos p; have dq := deg_pos q
        have eA : (add p q).deg = 1 + p.deg + q.deg := rfl
        rcases frag2_sum_cases hfb with rfl | ⟨r, s, rfl, hfr, hfs⟩ | ⟨hb0, hnb⟩
        · exact absurd rfl hbz
        · have dr := deg_pos r; have ds := deg_pos s
          have eB : (add r s).deg = 1 + r.deg + s.deg := rfl
          rcases frag2_sum_cases hfc with rfl | ⟨t, u, rfl, hft, hfu⟩ | ⟨hc0, hnc⟩
          · exact absurd rfl hcz
          · -- (1) ⊕ / ⊕ / ⊕ : 2.3.16 three times, along the spine
            have dt := deg_pos t; have du := deg_pos u
            have eC : (add t u).deg = 1 + t.deg + u.deg := rfl
            have hab1 : add p q ≠ add r s := ne_of_ltF h1
            have hab2 : add r s ≠ add t u := ne_of_ltF h2
            rw [ltF_succ_add_add _ hab1] at h1
            rw [ltF_succ_add_add _ hab2] at h2
            rw [ltF_succ_add_add _ hac]
            by_cases hpr : p = r
            · subst hpr
              rw [if_pos rfl] at h1
              by_cases hrt : p = t
              · subst hrt
                rw [if_pos rfl] at h2
                rw [if_pos rfl]
                exact TR1 q s u hfq hfs hfu (by omega) f' (by omega) h1 h2
              · rw [if_neg hrt] at h2
                rw [if_neg hrt]
                exact h2
            · rw [if_neg hpr] at h1
              by_cases hrt : r = t
              · subst hrt
                rw [if_pos rfl] at h2
                rw [if_neg hpr]
                exact h1
              · rw [if_neg hrt] at h2
                have hpt : p ≠ t := by
                  intro hc; subst hc
                  rw [ltF_asymm2 hfp hfr (by omega) h1] at h2; exact Bool.noConfusion h2
                rw [if_neg hpt]
                exact TR1 p r t hfp hfr hft (by omega) f' (by omega) h1 h2
          · -- (2) ⊕ / ⊕ / non-sum
            have hab1 : add p q ≠ add r s := ne_of_ltF h1
            rw [ltF_succ_add_add _ hab1] at h1
            rw [ltF_succ_add_nsum _ hc0 hnc] at h2
            rw [ltF_succ_add_nsum _ hc0 hnc]
            by_cases hpr : p = r
            · subst hpr; exact h2
            · rw [if_neg hpr] at h1
              exact TR1 p r c hfp hfr hfc (by omega) f' (by omega) h1 h2
        · rcases frag2_sum_cases hfc with rfl | ⟨t, u, rfl, hft, hfu⟩ | ⟨hc0, hnc⟩
          · exact absurd rfl hcz
          · -- (3) ⊕ / non-sum / ⊕
            have dt := deg_pos t; have du := deg_pos u
            have eC : (add t u).deg = 1 + t.deg + u.deg := rfl
            rw [ltF_succ_add_nsum _ hb0 hnb] at h1
            rw [ltF_succ_nsum_add _ hb0 hnb] at h2
            rw [ltF_succ_add_add _ hac]
            simp only [Bool.or_eq_true, beq_iff_eq] at h2
            have hpt : ltF f' p t = true := by
              rcases h2 with h3 | h3
              · rw [← h3]; exact h1
              · exact TR2 p t hfp hft (by omega) f' (by omega) h1 h3
            rw [if_neg (ne_of_ltF hpt)]
            exact hpt
          · -- (4) ⊕ / non-sum / non-sum
            have hBC : ltF f' b c = true := LOW b c (by omega) h2
            rw [ltF_succ_add_nsum _ hb0 hnb] at h1
            rw [ltF_succ_add_nsum _ hc0 hnc]
            exact TR2 p c hfp hfc (by omega) f' (by omega) h1 hBC
      · -- `a` is a non-sum
        rcases frag2_sum_cases hfb with rfl | ⟨r, s, rfl, hfr, hfs⟩ | ⟨hb0, hnb⟩
        · exact absurd rfl hbz
        · have dr := deg_pos r; have ds := deg_pos s
          have eB : (add r s).deg = 1 + r.deg + s.deg := rfl
          rcases frag2_sum_cases hfc with rfl | ⟨t, u, rfl, hft, hfu⟩ | ⟨hc0, hnc⟩
          · exact absurd rfl hcz
          · -- (5) non-sum / ⊕ / ⊕
            have dt := deg_pos t; have du := deg_pos u
            have eC : (add t u).deg = 1 + t.deg + u.deg := rfl
            have hab2 : add r s ≠ add t u := ne_of_ltF h2
            rw [ltF_succ_nsum_add _ ha0 hna] at h1
            rw [ltF_succ_add_add _ hab2] at h2
            rw [ltF_succ_nsum_add _ ha0 hna]
            by_cases hrt : r = t
            · subst hrt; exact h1
            · rw [if_neg hrt] at h2
              simp only [Bool.or_eq_true, beq_iff_eq] at h1
              rcases h1 with h3 | h3
              · rw [h3]; simp [h2]
              · have h4 : ltF f' a t = true :=
                  TR1 a r t hfa hfr hft (by omega) f' (by omega) h3 h2
                simp [h4]
          · -- (6) non-sum / ⊕ / non-sum
            rw [ltF_succ_nsum_add _ ha0 hna] at h1
            rw [ltF_succ_add_nsum _ hc0 hnc] at h2
            simp only [Bool.or_eq_true, beq_iff_eq] at h1
            have h4 : ltF f' a c = true := by
              rcases h1 with h3 | h3
              · rw [h3]; exact h2
              · exact TR1 a r c hfa hfr hfc (by omega) f' (by omega) h3 h2
            exact UP a c (by omega) h4
        · rcases frag2_sum_cases hfc with rfl | ⟨t, u, rfl, hft, hfu⟩ | ⟨hc0, hnc⟩
          · exact absurd rfl hcz
          · -- (7) non-sum / non-sum / ⊕
            have dt := deg_pos t; have du := deg_pos u
            have eC : (add t u).deg = 1 + t.deg + u.deg := rfl
            have hAB : ltF f' a b = true := LOW a b (by omega) h1
            rw [ltF_succ_nsum_add _ hb0 hnb] at h2
            rw [ltF_succ_nsum_add _ ha0 hna]
            simp only [Bool.or_eq_true, beq_iff_eq] at h2
            rcases h2 with h3 | h3
            · rw [← h3]; simp [hAB]
            · have h4 : ltF f' a t = true :=
                TR2 a t hfa hft (by omega) f' (by omega) hAB h3
              simp [h4]
          · -- (8) non-sum / non-sum / non-sum: §8.1's level table decides the shapes
            rcases frag2_nsum_cases hfa ha0 hna with rfl | ⟨x, rfl, hfx⟩ | ⟨p, q, rfl, hfp, hfq⟩
            · -- a = M : `M < b` forces `b = ω̄^y`, and then `ω̄^y < c` forces `c = ω̄^z`
              rcases frag2_nsum_cases hfb hb0 hnb with rfl | ⟨y, rfl, hfy⟩ | ⟨r, s, rfl, hfr, hfs⟩
              · rw [ltF_irrefl] at h1; exact Bool.noConfusion h1
              · rcases frag2_nsum_cases hfc hc0 hnc with rfl | ⟨z, rfl, hfz⟩ | ⟨t, u, rfl, hft, hfu⟩
                · rw [ltF_succ_omg_M] at h2; exact Bool.noConfusion h2
                · exact ltF_succ_M_omg _ _
                · rw [ltF_succ_omg_phi] at h2; exact Bool.noConfusion h2
              · rw [ltF_succ_M_phi] at h1; exact Bool.noConfusion h1
            · -- a = ω̄^x : nothing but an `ω̄` is above it
              rcases frag2_nsum_cases hfb hb0 hnb with rfl | ⟨y, rfl, hfy⟩ | ⟨r, s, rfl, hfr, hfs⟩
              · rw [ltF_succ_omg_M] at h1; exact Bool.noConfusion h1
              · rcases frag2_nsum_cases hfc hc0 hnc with rfl | ⟨z, rfl, hfz⟩ | ⟨t, u, rfl, hft, hfu⟩
                · rw [ltF_succ_omg_M] at h2; exact Bool.noConfusion h2
                · -- 2.3.12 three times
                  have dx := deg_pos x; have dy := deg_pos y; have dz := deg_pos z
                  have eA : (omg x).deg = 1 + x.deg := rfl
                  have eB : (omg y).deg = 1 + y.deg := rfl
                  have eC : (omg z).deg = 1 + z.deg := rfl
                  have hne1 : omg x ≠ omg y := ne_of_ltF h1
                  have hne2 : omg y ≠ omg z := ne_of_ltF h2
                  rw [ltF_succ_omg_omg _ hne1] at h1
                  rw [ltF_succ_omg_omg _ hne2] at h2
                  rw [ltF_succ_omg_omg _ hac]
                  exact TR1 x y z hfx hfy hfz (by omega) f' (by omega) h1 h2
                · rw [ltF_succ_omg_phi] at h2; exact Bool.noConfusion h2
              · rw [ltF_succ_omg_phi] at h1; exact Bool.noConfusion h1
            · -- a = φ̄pq : the bottom level, so `c` may be anything above it
              rcases frag2_nsum_cases hfb hb0 hnb with rfl | ⟨y, rfl, hfy⟩ | ⟨r, s, rfl, hfr, hfs⟩
              · rcases frag2_nsum_cases hfc hc0 hnc with rfl | ⟨z, rfl, hfz⟩ | ⟨t, u, rfl, hft, hfu⟩
                · rw [ltF_irrefl] at h2; exact Bool.noConfusion h2
                · exact ltF_succ_phi_omg _ _ _ _
                · rw [ltF_succ_M_phi] at h2; exact Bool.noConfusion h2
              · rcases frag2_nsum_cases hfc hc0 hnc with rfl | ⟨z, rfl, hfz⟩ | ⟨t, u, rfl, hft, hfu⟩
                · rw [ltF_succ_omg_M] at h2; exact Bool.noConfusion h2
                · exact ltF_succ_phi_omg _ _ _ _
                · rw [ltF_succ_omg_phi] at h2; exact Bool.noConfusion h2
              · rcases frag2_nsum_cases hfc hc0 hnc with rfl | ⟨z, rfl, hfz⟩ | ⟨t, u, rfl, hft, hfu⟩
                · exact ltF_succ_phi_M _ _ _
                · exact ltF_succ_phi_omg _ _ _ _
                · -- φ̄ / φ̄ / φ̄ : the nine sub-clause combinations of 2.3.13.
                  -- This is §7.4's case (8), unchanged apart from `Frag ↦ Frag2`.
                  have dp := deg_pos p; have dq := deg_pos q; have dr := deg_pos r
                  have ds := deg_pos s; have dt := deg_pos t; have du := deg_pos u
                  have eA : (phi p q).deg = 1 + p.deg + q.deg := rfl
                  have eB : (phi r s).deg = 1 + r.deg + s.deg := rfl
                  have eC : (phi t u).deg = 1 + t.deg + u.deg := rfl
                  have hAB : ltF f' (phi p q) (phi r s) = true :=
                    LOW (phi p q) (phi r s) (by omega) h1
                  have hBC : ltF f' (phi r s) (phi t u) = true :=
                    LOW (phi r s) (phi t u) (by omega) h2
                  have hab1 : phi p q ≠ phi r s := ne_of_ltF h1
                  have hab2 : phi r s ≠ phi t u := ne_of_ltF h2
                  rw [ltF_succ_phi_phi _ hab1] at h1
                  rw [ltF_succ_phi_phi _ hab2] at h2
                  by_cases hpr : p = r
                  · subst hpr
                    rw [if_pos rfl] at h1
                    by_cases hrt : p = t
                    · subst hrt
                      rw [if_pos rfl] at h2
                      rw [ltF_succ_phi_phi _ hac, if_pos rfl]
                      exact TR1 q s u hfq hfs hfu (by omega) f' (by omega) h1 h2
                    · rw [if_neg hrt] at h2
                      by_cases hrt2 : ltF f' p t = true
                      · rw [if_pos hrt2] at h2
                        rw [ltF_succ_phi_phi _ hac, if_neg hrt, if_pos hrt2]
                        exact TR1 q s (phi t u) hfq hfs hfc (by omega) f' (by omega) h1 h2
                      · rw [if_neg hrt2] at h2
                        rw [ltF_succ_phi_phi _ hac, if_neg hrt, if_neg hrt2]
                        simp only [Bool.or_eq_true, beq_iff_eq] at h2
                        rcases h2 with h3 | h3
                        · rw [← h3]; simp [hAB]
                        · have h4 : ltF f' (phi p q) u = true :=
                            TR2 (phi p q) u hfa hfu (by omega) f' (by omega) hAB h3
                          simp [h4]
                  · rw [if_neg hpr] at h1
                    by_cases hpr2 : ltF f' p r = true
                    · rw [if_pos hpr2] at h1
                      by_cases hrt : r = t
                      · subst hrt
                        rw [if_pos rfl] at h2
                        rw [ltF_succ_phi_phi _ hac, if_neg hpr, if_pos hpr2]
                        exact TR2 q (phi r u) hfq hfc (by omega) f' (by omega) h1 hBC
                      · rw [if_neg hrt] at h2
                        by_cases hrt2 : ltF f' r t = true
                        · rw [if_pos hrt2] at h2
                          have hpt : ltF f' p t = true :=
                            TR1 p r t hfp hfr hft (by omega) f' (by omega) hpr2 hrt2
                          rw [ltF_succ_phi_phi _ hac, if_neg (ne_of_ltF hpt), if_pos hpt]
                          exact TR2 q (phi t u) hfq hfc (by omega) f' (by omega) h1 hBC
                        · rw [if_neg hrt2] at h2
                          rcases ltF_comparable2 (f := f') hfp hft (by omega) with hc1 | hc1 | hc1
                          · rw [ltF_succ_phi_phi _ hac, if_neg (ne_of_ltF hc1), if_pos hc1]
                            exact TR2 q (phi t u) hfq hfc (by omega) f' (by omega) h1 hBC
                          · subst hc1
                            rw [ltF_succ_phi_phi _ hac, if_pos rfl]
                            simp only [Bool.or_eq_true, beq_iff_eq] at h2
                            rcases h2 with h3 | h3
                            · rw [← h3]; exact h1
                            · exact TR2 q u hfq hfu (by omega) f' (by omega) h1 h3
                          · have hpt : p ≠ t := by
                              intro hc; rw [hc, ltF_irrefl] at hc1; exact Bool.noConfusion hc1
                            have hnp : ltF f' p t = false := ltF_asymm2 hft hfp (by omega) hc1
                            rw [ltF_succ_phi_phi _ hac, if_neg hpt, if_neg (by simp [hnp])]
                            simp only [Bool.or_eq_true, beq_iff_eq] at h2
                            rcases h2 with h3 | h3
                            · rw [← h3]; simp [hAB]
                            · have h4 : ltF f' (phi p q) u = true :=
                                TR2 (phi p q) u hfa hfu (by omega) f' (by omega) hAB h3
                              simp [h4]
                    · rw [if_neg hpr2] at h1
                      have hrp : ltF f' r p = true := by
                        rcases ltF_comparable2 (f := f') hfp hfr (by omega) with h3 | h3 | h3
                        · exact absurd h3 hpr2
                        · exact absurd h3 hpr
                        · exact h3
                      by_cases hrt : r = t
                      · subst hrt
                        rw [if_pos rfl] at h2
                        rw [ltF_succ_phi_phi _ hac, if_neg hpr, if_neg hpr2]
                        simp only [Bool.or_eq_true, beq_iff_eq] at h1
                        rcases h1 with h3 | h3
                        · rw [h3]; simp [h2]
                        · have h4 : ltF f' (phi p q) u = true :=
                            TR1 (phi p q) s u hfa hfs hfu (by omega) f' (by omega) h3 h2
                          simp [h4]
                      · rw [if_neg hrt] at h2
                        by_cases hrt2 : ltF f' r t = true
                        · rw [if_pos hrt2] at h2
                          simp only [Bool.or_eq_true, beq_iff_eq] at h1
                          have h4 : ltF f' (phi p q) (phi t u) = true := by
                            rcases h1 with h3 | h3
                            · rw [h3]; exact h2
                            · exact TR1 (phi p q) s (phi t u) hfa hfs hfc
                                (by omega) f' (by omega) h3 h2
                          exact UP (phi p q) (phi t u) (by omega) h4
                        · rw [if_neg hrt2] at h2
                          have htr : ltF f' t r = true := by
                            rcases ltF_comparable2 (f := f') hfr hft (by omega) with h3 | h3 | h3
                            · exact absurd h3 hrt2
                            · exact absurd h3 hrt
                            · exact h3
                          have htp : ltF f' t p = true :=
                            TR1 t r p hft hfr hfp (by omega) f' (by omega) htr hrp
                          have hpt : p ≠ t := by
                            intro hc; rw [← hc, ltF_irrefl] at htp; exact Bool.noConfusion htp
                          have hnp : ltF f' p t = false := ltF_asymm2 hft hfp (by omega) htp
                          rw [ltF_succ_phi_phi _ hac, if_neg hpt, if_neg (by simp [hnp])]
                          simp only [Bool.or_eq_true, beq_iff_eq] at h2
                          rcases h2 with h3 | h3
                          · rw [← h3]; simp [hAB]
                          · have h4 : ltF f' (phi p q) u = true :=
                              TR2 (phi p q) u hfa hfu (by omega) f' (by omega) hAB h3
                            simp [h4]

/-- **TRANSITIVITY on `Frag2`**, same fuel.  STAGE 3a of the §8 map, executed. -/
theorem trans_ltF2 {a b c : Term} (hfa : Frag2 a = true) (hfb : Frag2 b = true)
    (hfc : Frag2 c = true) {f : Nat} (hf : a.deg + b.deg + c.deg ≤ f)
    (h1 : ltF f a b = true) (h2 : ltF f b c = true) : ltF f a c = true :=
  trans_aux2 b.deg (a.deg + c.deg) a b c hfa hfb hfc (Nat.le_refl _) (Nat.le_refl _) f hf h1 h2

/-! #### §8.2.3 The user-facing statements, about `lt`

§5 again: the three hypotheses live at three different default fuels and
`lt_eq_ltF` brings them to the common fuel `a.deg + b.deg + c.deg`. -/

/-- **ASYMMETRY.** -/
theorem lt_asymm2 {a b : Term} (hfa : Frag2 a = true) (hfb : Frag2 b = true)
    (h : lt a b = true) : lt b a = false := by
  rw [lt_eq_ltF a b (a.deg + b.deg) (Nat.le_refl _)] at h
  rw [lt_eq_ltF b a (a.deg + b.deg) (by omega)]
  exact ltF_asymm2 hfa hfb (Nat.le_refl _) h

/-- **COMPARABILITY.** -/
theorem lt_comparable2 {a b : Term} (hfa : Frag2 a = true) (hfb : Frag2 b = true) :
    lt a b = true ∨ a = b ∨ lt b a = true := by
  rw [lt_eq_ltF a b (a.deg + b.deg) (Nat.le_refl _),
      lt_eq_ltF b a (a.deg + b.deg) (by omega)]
  exact ltF_comparable2 hfa hfb (Nat.le_refl _)

/-- **TRANSITIVITY** on `Frag2` — §7.5's keystone, now with `M` and `ω̄^·`. -/
theorem lt_trans2 {a b c : Term} (hfa : Frag2 a = true) (hfb : Frag2 b = true)
    (hfc : Frag2 c = true) (h1 : lt a b = true) (h2 : lt b c = true) : lt a c = true := by
  have da := deg_pos a; have db := deg_pos b; have dc := deg_pos c
  rw [lt_eq_ltF a b (a.deg + b.deg + c.deg) (by omega)] at h1
  rw [lt_eq_ltF b c (a.deg + b.deg + c.deg) (by omega)] at h2
  rw [lt_eq_ltF a c (a.deg + b.deg + c.deg) (by omega)]
  exact trans_ltF2 hfa hfb hfc (Nat.le_refl _) h1 h2

/-- **`Frag2` is a strict LINEAR order**: exactly one of `<`, `=`, `>`. -/
theorem lt_trichotomy2 {a b : Term} (hfa : Frag2 a = true) (hfb : Frag2 b = true) :
    (lt a b = true ∧ a ≠ b ∧ lt b a = false)
  ∨ (lt a b = false ∧ a = b ∧ lt b a = false)
  ∨ (lt a b = false ∧ a ≠ b ∧ lt b a = true) := by
  rcases lt_comparable2 hfa hfb with h | h | h
  · exact Or.inl ⟨h, ne_of_ltF h, lt_asymm2 hfa hfb h⟩
  · subst h; exact Or.inr (Or.inl ⟨lt_irrefl a, rfl, lt_irrefl a⟩)
  · refine Or.inr (Or.inr ⟨lt_asymm2 hfb hfa h, ?_, h⟩)
    intro hc; rw [hc, lt_irrefl] at h; exact Bool.noConfusion h

/-! The `≤` forms and the two INVERSION lemmas, as in §7.5. -/

theorem lt_of_le_of_lt2 {a b c : Term} (hfa : Frag2 a = true) (hfb : Frag2 b = true)
    (hfc : Frag2 c = true) (h1 : le a b = true) (h2 : lt b c = true) : lt a c = true := by
  simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with rfl | h1
  · exact h2
  · exact lt_trans2 hfa hfb hfc h1 h2

theorem lt_of_lt_of_le2 {a b c : Term} (hfa : Frag2 a = true) (hfb : Frag2 b = true)
    (hfc : Frag2 c = true) (h1 : lt a b = true) (h2 : le b c = true) : lt a c = true := by
  simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at h2
  rcases h2 with rfl | h2
  · exact h1
  · exact lt_trans2 hfa hfb hfc h1 h2

theorem le_of_not_lt2 {a b : Term} (hfa : Frag2 a = true) (hfb : Frag2 b = true)
    (h : lt a b = false) : le b a = true := by
  simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq]
  rcases lt_comparable2 hfa hfb with h1 | h1 | h1
  · rw [h1] at h; exact Bool.noConfusion h
  · exact Or.inl h1.symm
  · exact Or.inr h1

theorem lt_of_not_le2 {a b : Term} (hfa : Frag2 a = true) (hfb : Frag2 b = true)
    (h : le a b = false) : lt b a = true := by
  simp only [TM.Term.le, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  rcases lt_comparable2 hfa hfb with h1 | h1 | h1
  · rw [h1] at h; exact absurd h.2 (by simp)
  · exact absurd h1 h.1
  · exact h1

theorem le_trans2 {a b c : Term} (hfa : Frag2 a = true) (hfb : Frag2 b = true)
    (hfc : Frag2 c = true) (h1 : le a b = true) (h2 : le b c = true) : le a c = true := by
  simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at h1 h2 ⊢
  rcases h1 with rfl | h1
  · exact h2
  · rcases h2 with rfl | h2
    · exact Or.inr h1
    · exact Or.inr (lt_trans2 hfa hfb hfc h1 h2)

/-! #### §8.2.4 `Frag2` is closed under the operations, and §7 is subsumed -/

theorem frag2_mk_add {a b : Term} (ha : Frag2 a = true) (hb : Frag2 b = true) :
    Frag2 (add a b) = true := by
  show (Frag2 a && Frag2 b) = true; rw [ha, hb]; rfl

theorem frag2_mk_phi {a b : Term} (ha : Frag2 a = true) (hb : Frag2 b = true) :
    Frag2 (phi a b) = true := by
  show (Frag2 a && Frag2 b) = true; rw [ha, hb]; rfl

theorem frag2_mk_omg {a : Term} (ha : Frag2 a = true) : Frag2 (omg a) = true := ha

theorem frag2_M : Frag2 M = true := rfl

/-- §7 is the special case: every `Frag` fact is a `Frag2` fact. -/
theorem lt_trans_of_frag {a b c : Term} (hfa : Frag a = true) (hfb : Frag b = true)
    (hfc : Frag c = true) (h1 : lt a b = true) (h2 : lt b c = true) : lt a c = true :=
  lt_trans2 (frag_le_frag2 a hfa) (frag_le_frag2 b hfb) (frag_le_frag2 c hfc) h1 h2

/-! #### §8.2.5 Evidence that §8.2 has content, and the mutants

Same doctrine as §7.7 (and as plan/README.md's 較正事故 section): a hypothesis
nobody can falsify is decoration.  The measurements quoted here were run on an
enumerator written independently for this section, which reproduces §8's published
counts EXACTLY — 3042 terms of degree ≤ 6, 16850 of degree ≤ 7, 529 of those `inT`,
556 in `Frag2`, all duplicate-free.  They are therefore a re-check of §8's numbers
as well as evidence for §8.2.

NON-VACUITY.  `Frag2` is not a rounding error on `Frag`: at degree ≤ 6 there are
556 `Frag2` terms and only ELEVEN `Frag` terms, so §8.2 is about fifty times as
much of the language as §7 at that depth.  MEASURED on all 556: `lt` is
asymmetric, it is total on distinct terms, and the predecessor-scores are the 556
DISTINCT values 0,…,555 — which is §8's tournament certificate for a strict linear
order.  §8.2 proves that, at every degree. -/

private def frag2Sample : List Term :=
  [zero, one, M, omg zero, omg M, omg (omg M), add M one, add (omg M) M,
   phi one M, add (omg M) (phi one zero)]

#guard frag2Sample.all (fun t => Frag2 t)
#guard !frag2Sample.all (fun t => Frag t)
#guard (frag2Sample.filter Frag).length == 2
#guard frag2Sample.all (fun s => frag2Sample.all (fun t => !(lt s t && lt t s)))
#guard frag2Sample.all (fun s => frag2Sample.all (fun t => lt s t || s == t || lt t s))
#guard frag2Sample.all (fun s => frag2Sample.all (fun t => frag2Sample.all (fun u =>
         !(lt s t && lt t u) || lt s u)))

/-! MUTANT 1 — DROP THE FUEL HYPOTHESIS of `trans_ltF2`.  §7.7 already has such a
mutant, but its witness lies in `Frag`, so re-using it would test nothing that §8.2
adds.  This one is chosen inside the NEW region: none of `M`, `ω̄^0`, `ω̄^0 ⊕ 0` is
a `Frag` term.  At fuel 1 the triple violates transitivity outright — the fuel
hypothesis demands `f ≥ 7` here — and `lt`, at its default fuel, gets it right.
(MEASURED: 140 such triples among the `Frag2` terms of degree ≤ 4 at fuel < 5, so
this is a family, not a curiosity.) -/

#guard Frag2 M && Frag2 (omg zero) && Frag2 (add (omg zero) zero)
#guard !(Frag M) && !(Frag (omg zero))
#guard ltF 1 M (omg zero) == true
#guard ltF 1 (omg zero) (add (omg zero) zero) == true
#guard ltF 1 M (add (omg zero) zero) == false
#guard (M : Term).deg + (omg zero).deg + (add (omg zero) zero).deg == 7
#guard lt M (add (omg zero) zero) == true

/-- Deleting the fuel hypothesis from `trans_ltF2` makes it FALSE, and the witness
    is in the region §8.2 adds to §7 (`M` and `ω̄`, neither of them `Frag`). -/
theorem trans_ltF2_needs_fuel :
    ¬ (∀ (a b c : Term), Frag2 a = true → Frag2 b = true → Frag2 c = true →
        ∀ f, ltF f a b = true → ltF f b c = true → ltF f a c = true) := by
  intro h
  have hbad := h M (omg zero) (add (omg zero) zero) rfl rfl rfl 1 rfl rfl
  have hc : ltF 1 M (add (omg zero) zero) = false := rfl
  rw [hc] at hbad
  exact Bool.noConfusion hbad

/-! MUTANT 2 — WIDEN `Frag2` TO ADMIT `ψ`.  This is precisely where the fragment
has to stop, and the witness is §8's own receipt pair: `ψ_M 0` and `ψ_(ψ_M 0) 0`
are distinct and NEITHER is below the other.  Comparability therefore fails, and
since §8.2's route to asymmetry and to the 13(iii) branch of transitivity both run
through `ltF_comparable2`, all three fail together.  Both witnesses fail `inT`, and
only at the `κ ∈ R` conjunct of 2.1(vi) — that is §8 item 3, and it is why Stage 3b
must carry `inT` exactly where §8.2 carries nothing.  (MEASURED: 40 incomparable
pairs among ALL 578 terms of degree ≤ 5, and 72 among the 628 ψ-headed terms of
degree ≤ 6; every one of them has this shape.) -/

/-- `Frag2` cannot be widened to admit `ψ`: the order is not even comparable there. -/
theorem frag2_stops_at_psi :
    Frag2 (psi M zero) = false
  ∧ Frag2 (psi (psi M zero) zero) = false
  ∧ psi M zero ≠ psi (psi M zero) zero
  ∧ lt (psi M zero) (psi (psi M zero) zero) = false
  ∧ lt (psi (psi M zero) zero) (psi M zero) = false :=
  ⟨rfl, rfl, by decide, rfl, rfl⟩

/-! WHAT IS *NOT* CONTROLLED HERE, HONESTLY.  There is no mutant deleting `Frag2`
from `trans_ltF2` alone, because no counterexample was found to delete it with.  An
exhaustive triple loop over ALL 114 terms of degree ≤ 4 finds NO transitivity
violation anywhere in the raw language; and at degree ≤ 5 and ≤ 6 no incomparable
pair (40 and 72 respectively) has any term of the language strictly between its two
members, which is the only way a violation could arise given that asymmetry holds
raw.  So at the depths that can be swept, raw `lt` is transitive even where it is
not comparable, and the `Frag2` hypothesis of `trans_ltF2` is load-bearing for the
PROOF — which consumes `ltF_comparable2` — but is not (as far as measured)
load-bearing for the STATEMENT.  Recorded rather than dressed up as a control.

This also sharpens §8's item 1 in a useful direction: what makes Stage 3b hard is
comparability, not transitivity.  Whatever `inT` has to buy, it has to buy it
there. -/

/-! ### §8.3 STAGE 3b, STARTED: the `ψ`/`Z` rule table and the `starF` layer

§8's Stage 3b says the real work is the clauses routing through `starF`, and names
the two facts to prove first: `le (star d) d` and `star d ≤ Z d`.  This section
supplies what comes before them — the complete rewrite-rule table for `ψ` and `Z`
(so 3b starts from a rule table, exactly as 3a started from §8.1's), the `starF`
unfolding rules, and the one `starF` fact that is `inT`-FREE.  It does NOT prove
`le (star d) d`; see the measurement note at the end for what that will cost and
why it cannot be done here.

THE SHAPE MATRIX IS ALREADY COMPLETE.  §8.2's `ltF_succ_add_nsum` /
`ltF_succ_nsum_add` were stated against an ARBITRARY non-sum, and `ψ` and `Z` are
non-sums, so every sum-vs-`ψ`/`Z` case is already covered.  §8.1 covers `M` and
`ω̄` against `ψ` and `Z`.  What is left is the eight rules below — `φ̄`, `ψ`, `Z`
against each other — and then 3b's inductions have a complete table. -/

/-! 2.3.5: `γ ∈ SC` and `α, β < γ` ⟹ `φ̄αβ < γ`.  Both `SC` shapes, same clause. -/
theorem ltF_succ_phi_psi (f : Nat) (a b k c : Term) :
    ltF (f + 1) (phi a b) (psi k c) = (ltF f a (psi k c) && ltF f b (psi k c)) := rfl

theorem ltF_succ_phi_Z (f : Nat) (a b d : Term) :
    ltF (f + 1) (phi a b) (Z d) = (ltF f a (Z d) && ltF f b (Z d)) := rfl

/-! 2.3.4: `γ ≤ α ∨ γ ≤ β` ⟹ `γ < φ̄αβ`. -/
theorem ltF_succ_psi_phi (f : Nat) (k a c d : Term) :
    ltF (f + 1) (psi k a) (phi c d) =
      ((psi k a == c) || (psi k a == d) || ltF f (psi k a) c || ltF f (psi k a) d) := rfl

theorem ltF_succ_Z_phi (f : Nat) (e c d : Term) :
    ltF (f + 1) (Z e) (phi c d) =
      ((Z e == c) || (Z e == d) || ltF f (Z e) c || ltF f (Z e) d) := rfl

/-- 2.3.14: `ψκα < ψπβ`, the three sub-clauses.  §8's observation that this has
    exactly the shape of 2.3.13 is visible here: compare with `ltF_succ_phi_phi`,
    which is the same `if`-tree with `κ` in place of `α`. -/
theorem ltF_succ_psi_psi (f : Nat) {k a p b : Term} (h : psi k a ≠ psi p b) :
    ltF (f + 1) (psi k a) (psi p b) =
      (if k = p then ltF f a b
       else if ltF f k p = true then ltF f k (psi p b)
       else ltF f (psi k a) p) := by
  show (if (psi k a == psi p b) = true then false
        else if (k == p) = true then ltF f a b
        else if ltF f k p = true then ltF f k (psi p b)
        else ltF f (psi k a) p) = _
  rw [if_neg (by simpa using h)]
  by_cases hkp : k = p
  · rw [if_pos (by simpa using hkp), if_pos hkp]
  · rw [if_neg (by simpa using hkp), if_neg hkp]

/-! `ψ` against `Z`: 2.3.8 (`κ ≤ γ ⟹ ψκα < γ`), else 2.3.6 / 2.3.9 through `δ*`.
    These need no distinctness hypothesis — a `ψ` is never a `Z`. -/
theorem ltF_succ_psi_Z (f : Nat) (k a d : Term) :
    ltF (f + 1) (psi k a) (Z d) =
      (if ((k == Z d) || ltF f k (Z d)) = true then true
       else ((psi k a == starF f d) || ltF f (psi k a) (starF f d))) := rfl

theorem ltF_succ_Z_psi (f : Nat) (e k b : Term) :
    ltF (f + 1) (Z e) (psi k b) =
      (if ((k == Z e) || ltF f k (Z e)) = true then false
       else ltF f (starF f e) (psi k b)) := rfl

/-- 2.3.15: `Zα < Zβ`. -/
theorem ltF_succ_Z_Z (f : Nat) {a b : Term} (h : Z a ≠ Z b) :
    ltF (f + 1) (Z a) (Z b) =
      (if ltF f a b = true then ltF f (starF f a) (Z b)
       else ((Z a == starF f b) || ltF f (Z a) (starF f b))) := by
  show (if (Z a == Z b) = true then false
        else if ltF f a b = true then ltF f (starF f a) (Z b)
        else ((Z a == starF f b) || ltF f (Z a) (starF f b))) = _
  rw [if_neg (by simpa using h)]

/-! #### §8.3.1 The `starF` unfolding rules ([R91] 2.2)

`starF` is where 3b differs from everything before it: the recursion of `ltF` goes
THROUGH it, so its clauses need the same treatment `ltF`'s got in §7.2 / §8.1. -/

theorem starF_succ_zero (f : Nat) : starF (f + 1) zero = zero := rfl
theorem starF_succ_M (f : Nat) : starF (f + 1) M = zero := rfl
theorem starF_succ_psi (f : Nat) (k a : Term) : starF (f + 1) (psi k a) = psi k a := rfl
theorem starF_succ_Z (f : Nat) (a : Term) : starF (f + 1) (Z a) = Z a := rfl
theorem starF_succ_omg (f : Nat) (a : Term) : starF (f + 1) (omg a) = starF f a := rfl

/-- 2.2(ii): `⊕(…)* = max(αᵢ*)`. -/
theorem starF_succ_add (f : Nat) (a b : Term) :
    starF (f + 1) (add a b)
      = (if ltF f (starF f a) (starF f b) then starF f b else starF f a) := rfl

/-- 2.2(iv): `(φ̄αβ)* = max(α*, β*)`. -/
theorem starF_succ_phi (f : Nat) (a b : Term) :
    starF (f + 1) (phi a b)
      = (if ltF f (starF f a) (starF f b) then starF f b else starF f a) := rfl

/-- **`α*` is `0` or strongly critical** — [R91] 2.2 read as a range statement.
    This is the one `starF` fact that needs NO formation condition: it is pure
    structure, and it is what tells 3b's `ψ`/`Z` clauses that the term they recurse
    into through `starF` is again one of the shapes the table above covers.
    MEASURED to hold on ALL 3042 terms of degree ≤ 6, `inT` or not — and here it is
    as a theorem, for every term. -/
theorem starF_zero_or_isSC : ∀ (f : Nat) (t : Term),
    starF f t = zero ∨ isSC (starF f t) = true
  | 0, _ => Or.inl rfl
  | f + 1, t => by
    cases t with
    | zero => exact Or.inl rfl
    | M => exact Or.inl rfl
    | psi k a => exact Or.inr rfl
    | Z a => exact Or.inr rfl
    | omg a => exact starF_zero_or_isSC f a
    | add a b =>
      rw [starF_succ_add]
      cases ltF f (starF f a) (starF f b)
      · show starF f a = zero ∨ (starF f a).isSC = true
        exact starF_zero_or_isSC f a
      · show starF f b = zero ∨ (starF f b).isSC = true
        exact starF_zero_or_isSC f b
    | phi a b =>
      rw [starF_succ_phi]
      cases ltF f (starF f a) (starF f b)
      · show starF f a = zero ∨ (starF f a).isSC = true
        exact starF_zero_or_isSC f a
      · show starF f b = zero ∨ (starF f b).isSC = true
        exact starF_zero_or_isSC f b

/-- The `star` form, at the default fuel. -/
theorem star_zero_or_isSC (t : Term) : star t = zero ∨ isSC (star t) = true :=
  starF_zero_or_isSC _ t

/-- **The range of `α*` is sharper than `{0} ∪ SC`: `M` is never a value.**  2.2(i)
    sends `M` to `0`, and no other clause can produce `M`, so `α*` lands in
    `{0} ∪ {ψκβ} ∪ {Zβ}` — the SC terms BELOW `M`.  This is the form 3b wants: the
    clauses that recurse into `δ*` (2.3.6 / 2.3.9 / 2.3.15) compare it against `ψ`
    terms, and `M` is exactly the shape that would make those comparisons behave
    differently (`M < φ̄` is false while `ψ < φ̄` need not be). -/
theorem starF_zero_or_psi_or_Z : ∀ (f : Nat) (t : Term),
    starF f t = zero ∨ (∃ k a, starF f t = psi k a) ∨ (∃ a, starF f t = Z a)
  | 0, _ => Or.inl rfl
  | f + 1, t => by
    cases t with
    | zero => exact Or.inl rfl
    | M => exact Or.inl rfl
    | psi k a => exact Or.inr (Or.inl ⟨k, a, rfl⟩)
    | Z a => exact Or.inr (Or.inr ⟨a, rfl⟩)
    | omg a => exact starF_zero_or_psi_or_Z f a
    | add a b =>
      rw [starF_succ_add]
      cases ltF f (starF f a) (starF f b)
      · exact starF_zero_or_psi_or_Z f a
      · exact starF_zero_or_psi_or_Z f b
    | phi a b =>
      rw [starF_succ_phi]
      cases ltF f (starF f a) (starF f b)
      · exact starF_zero_or_psi_or_Z f a
      · exact starF_zero_or_psi_or_Z f b

/-- `α*` is never `M`. -/
theorem starF_ne_M (f : Nat) (t : Term) : starF f t ≠ M := by
  rcases starF_zero_or_psi_or_Z f t with h | ⟨k, a, h⟩ | ⟨a, h⟩ <;>
    rw [h] <;> intro hc <;> exact Term.noConfusion hc

/-! #### §8.3.2 What `le (star d) d` will cost — MEASURED, not guessed

§8's Stage 3b names `le (star d) d` and `star d ≤ Z d` as the first things to prove,
on the evidence of the 171 `inT` terms of degree ≤ 6.  Re-measured here at degree
≤ 8, on the 1687 `inT` terms, BOTH still hold — the claim survives its first test
above its calibration depth.  Two further measurements say what the proof will look
like, and neither is in §8:

  * `le (star d) d` IS NOT `inT`-FREE, unlike everything in §8.2 and unlike
    `starF_zero_or_isSC` above.  MEASURED: 106 terms of degree ≤ 6 falsify it, the
    smallest being `0 ⊕ Z0`, whose `*` is `Z0` while its head component is `0`, so
    2.3.11 asks `Z0 ≤ 0` and gets `false`.  Every one of the 106 fails `inT`.  So
    this is the point at which 3b stops being able to copy §8.2's `inT`-free style,
    and the conjunct it needs is 2.1(iii) — components in AP and descending — NOT
    2.1(vi).  That is a DIFFERENT `inT` destructor from the one §8 item 3 predicted
    would be needed (`κ ∈ R`); both are needed, for different clauses.

  * K_κ IS NOT NEEDED FOR THIS LAYER.  MEASURED: with the K_κ conjunct of 2.1(vi)
    deleted, `le (star d) d` and `le (star d) (Z d)` still hold on all 1691 admitted
    terms of degree ≤ 8.  Since K_κ is the one conjunct with no cheap destructor
    (`Kset` is itself defined by recursion through `lt`), that is worth knowing
    before the work is planned: 3b should not budget for a K_κ destructor here.

CORRECTION TO §8's STAGING, and this one matters for planning.  §8 says of
`le (star d) d` and `le (star d) (Z d)` that "they are the first things to prove in
3b".  They cannot be proved FIRST: working the induction out, one case of
`le (star d) d` is entangled with the very theorem 3b is after.  Case by case, with
`α* ∈ {0} ∪ ψ ∪ Z` (`starF_zero_or_psi_or_Z`) in hand:

  * `0`, `M`, `ψκα`, `Zα` — immediate (`α*` is `0` or `α` itself).
  * `ω̄^α` — FREE, and it needs no induction hypothesis at all: `(ω̄^α)* = α*`, which
    is `0`, a `ψ` or a `Z`, and every one of those is below every `ω̄^·` by §8.1's
    constant rules (`ltF_succ_psi_omg`, `ltF_succ_Z_omg`, `ltF_left_zero`).
  * `φ̄αβ` — FREE given the induction hypothesis, in ONE step and with no
    transitivity: `(φ̄αβ)*` is `α*` or `β*`, the hypothesis gives `α* ≤ α`, and
    2.3.4 (`ltF_succ_psi_phi` / `ltF_succ_Z_phi`) turns `γ ≤ α` straight into
    `γ < φ̄αβ`.
  * `⊕(α₁,…,αₙ)` — ENTANGLED.  `⊕* = max(αᵢ*)` and 2.3.11 compares it with the HEAD
    `α₁` only.  For `α₁*` the hypothesis is exactly what 2.3.11 asks for; but for
    `αᵢ*` with `i > 1` the hypothesis gives `αᵢ* ≤ αᵢ`, while 2.1(iii) gives only
    `αᵢ ≤ α₁`, so the step needs `αᵢ* ≤ αᵢ ≤ α₁` — TRANSITIVITY of `≤`, on exactly
    the terms 3b is trying to order.  And transitivity's `ψ`/`Z` clauses recurse
    through `starF`, so it cannot be had first either.

SUPERSEDED CONCLUSION — CORRECTED IN §8.4(ii).  This note originally concluded from
the above that `le (star d) d`, comparability, asymmetry and transitivity therefore
have to close as ONE simultaneous induction.  That does not follow, and it is
wrong.  The entanglement above is a fact about `le (star d) d`; but the ORDER proofs
never need `le (star d) d` at all, because every clause that recurses through
`starF` (2.3.6 / 2.3.9 / 2.3.15) falls back on comparability, asymmetry or
transitivity at a STRICTLY SMALLER degree sum — `deg_starF` gives
`(starF f d).deg ≤ d.deg` while the clause has already stripped a `Z` or a `ψ`.  So
§7's two-stage architecture survives unchanged and §8's staging was right about the
shape, if not about this lemma's place in it.  Read the case analysis above as what
it is: a description of `le (star d) d` itself, which remains a genuine
theorem-in-waiting but is NOT on 3b's critical path.  §8.4 is the design that
replaces this paragraph. -/

-- receipts for §8.3.2 (samples of the measurements quoted above)
#guard star (add zero (Z zero)) == Z zero
#guard le (star (add zero (Z zero))) (add zero (Z zero)) == false
#guard inT (add zero (Z zero)) == false
#guard (zero : Term).isAP == false          -- ... and this is why: 2.1(iii) needs AP components
#guard le (star (add (Z zero) (Z zero))) (add (Z zero) (Z zero)) == true
#guard star (psi (Z zero) zero) == psi (Z zero) zero
#guard star M == zero
#guard star (phi zero (Z zero)) == Z zero

/-! ### §8.4 STAGE 3b, PHASE A: the fragment, the measure, and the interface

This section is a DESIGN, not a proof.  It fixes (i) the fragment Stage 3b should
target and why, (ii) the termination measure, (iii) the exact statements to be
produced, and (iv) the interface every case lemma is written against, so that the
cases can be proved independently and assembled.  Nothing below is asserted as an
order theorem; the only theorems here are the `FragR` destructors, which are one
line each and exist so the interface compiles.

Sweep evidence referenced throughout: `table/order-sweep-2026-08-09.txt` (four
agents, generators independent of §8's and of §8.2.5's, calibrated against §8's
published counts before running).  Numbers are cited there rather than restated.

────────────────────────────────────────────────────────────────────────────────
(i) THE FRAGMENT: `FragR`, and why it is NOT `inT`

§8 item 2 says Stage 3b needs `inT`, and §8 item 3 narrows that to ONE conjunct,
`κ ∈ R` of 2.1(vi).  Taking that seriously gives a fragment much better than `inT`:
keep only the `κ ∈ R` requirement, hereditarily, and drop everything else.  That is
`FragR` below — every `ψ`-subterm has a head in `R`.  It is worth the change:

  * `FragR` IS PURELY SYNTACTIC.  `inT` is not: it contains `lt a M`, `le c a`, and
    `Kset`, and `Kset` is itself defined by recursion through `lt`.  Carrying `inT`
    through an induction ON `lt` therefore risks circularity and certainly costs
    destructor work at every step; `FragR` is hereditary in the trivial way `Frag`
    and `Frag2` are, so §7.3/§7.4's inductions transcribe with no new machinery.
  * IT IS MUCH LARGER, so the theorem is much stronger.  MEASURED: at degree ≤ 6,
    1906 terms satisfy `FragR` against 171 for `inT`; at degree ≤ 7, 9410 against
    529 — 8881 of those are NOT `inT`.
  * IT SUBSUMES `inT`.  MEASURED: every one of the 529 `inT` terms of degree ≤ 7
    satisfies `FragR` (2.1(vi) demands `κ.isR` at each `ψ`, which is exactly what
    `FragR` collects).  So the `inT` forms are corollaries via `inT_le_fragR`
    (enumerated as a Phase-B case), and nothing that wants `inT` is lost.
  * IT IS THE MEASURED BOUNDARY.  §8.2.5 found every raw incomparable pair to be of
    the shape `ψ_M x` vs `ψ_(ψ_M x) y` — i.e. failing exactly `κ ∈ R`.  Removing
    precisely that restores the order: MEASURED, on all 1906 `FragR` terms of
    degree ≤ 6, `lt` is asymmetric, total on distinct terms, and its
    predecessor-scores are the 1906 distinct values 0,…,1905 — the §8 tournament
    certificate for a strict linear order, enumeration duplicate-free.

QUARANTINE, EXPLICITLY.  `FragR` reaches terms the sweeps never covered: it admits
K_κ-REJECTED terms (8881 non-`inT` terms already at degree ≤ 7), and
`table/order-sweep-2026-08-09.txt` records that mixed `⊕`/`φ̄`/`ω̄` K-rejected terms
first exist at degree ≥ 10 and were never swept.  The exhaustive `FragR` evidence
above stops at degree 6.  This design therefore ASSUMES that K_κ is
order-irrelevant — which the sweep supports as far as it looked, and which the
sweep explicitly does not certify above its depth.  THE FALLBACK IS NAMED: if any
case lemma below turns out to need K_κ, do not weaken the case — shrink the
fragment to `fun t => FragR t && inT t` and re-derive, which costs only the `inT`
destructors and loses only the non-`inT` terms.

────────────────────────────────────────────────────────────────────────────────
(ii) THE MEASURE: §7's, unchanged — and a CORRECTION to §8.3.2

§8.3.2 (written earlier in this lane) concluded that `le (star d) d`, comparability,
asymmetry and transitivity must close as ONE simultaneous induction, because
`le (star d) d` is entangled with transitivity at the `⊕` case.  THE ENTANGLEMENT IS
REAL BUT THE CONCLUSION WAS WRONG, and the error mattered enough to correct here:
`le (star d) d` IS NEVER NEEDED BY THE ORDER PROOFS.  Every clause that recurses
through `starF` — 2.3.6, 2.3.9, 2.3.15 — consumes only comparability, asymmetry or
transitivity at a STRICTLY SMALLER degree sum, because `deg_starF` gives
`(starF f d).deg ≤ d.deg` while the clause has already stripped a `Z` or a `ψ`
(degree `1 + d.deg`).  So `le (star d) d` is a fact about the system, not a
prerequisite of it, and §8's original two-stage staging survives:

    STAGE I   `cmp_aux3` — asymmetry and comparability, simultaneously,
              by induction on `a.deg + b.deg`   (§7.3's shape, unchanged)
    STAGE II  `trans_aux3` — transitivity, with Stage I available, by the
              lexicographic measure `(b.deg, a.deg + c.deg)`   (§7.4's, unchanged)

Worked instances of "smaller degree suffices", which is what makes this safe:
  * 2.3.6 `ψκα < Zδ` falls back on comparing `ψκα` with `δ*`, of degree sum
    `(1+κ+α) + (δ*).deg ≤ (1+κ+α) + δ.deg  <  (1+κ+α) + (1+δ)`.
  * 2.3.15 `Zα < Zβ` falls back on `α* vs Zβ` and `Zα vs β*`, both strictly below
    `(1+α) + (1+β)` for the same reason.
So the ONE genuinely new obligation the `starF` clauses create is not an order fact
at all but a CLOSURE fact — the fragment must contain `α*` (case S1 below), since
otherwise the induction hypothesis cannot be applied to it.

────────────────────────────────────────────────────────────────────────────────
(iii) WHERE `κ ∈ R` IS CONSUMED — the obligation map §8.2's mutants cannot cover

`Frag` and `Frag2` carried no side condition, so §7.7/§8.2.5 could test their
hypotheses by deletion.  `FragR` has a real side condition, so the file must say
where it is USED rather than only that it cannot be dropped:

  * COMPARABILITY of `ψ` against `ψ` (2.3.14) is the only place it is essential.
    2.3.14 selects on `κ = π` / `κ < π` / neither, so "neither" must mean `π < κ`,
    i.e. the two HEADS must be comparable.  With `κ, π ∈ R` both heads are `Z`
    terms and their comparison is 2.3.15, which the same induction is proving
    total.  Without it the heads can be `M` and `ψ_M 0`, which are incomparable —
    that is exactly `frag2_stops_at_psi`'s witness, and the reason it is a witness.
  * Everywhere else `FragR` is passed along unused, purely to keep the induction
    hypotheses applicable.  Case lemmas below that do not mention `isR` in their
    hint do not consume it.

────────────────────────────────────────────────────────────────────────────────
(iv) WHY THE CASE LIST IS EXHAUSTIVE

Shapes split as `0` / sum / non-sum, exactly as in §8.2, because §8.2's
`ltF_succ_add_nsum` and `ltF_succ_nsum_add` were already proved against an ARBITRARY
non-sum — `ψ` and `Z` included.  So all sum-involving cases transcribe from §8.2
with `Frag2 ↦ FragR` and nothing else.  Among non-sums, §8.1's table orders by
LEVEL — `φ̄, ψ, Z` at level 1, `M` at 2, `ω̄^·` at 3 — and level is a function of the
shape alone.  `a < b` forbids the level of `a` from exceeding that of `b`, so in the
all-non-sum transitivity case `a < b < c` either raises the level (conclusion
immediate from the level lemma) or pins all three to one level.  Level 2 forces
`a = b = M`, impossible; level 3 is one call of 2.3.12; level 1 leaves the 27 shape
triples over `{φ̄, ψ, Z}`, and MEASURED, all 27 are reachable — as are all 9 level-1
pairs for comparability — so no case in the list below is vacuous. -/

/-- The Stage-3b fragment: every `ψ`-subterm has a head in `R` ([R91] 2.1(vi)'s
    `κ ∈ R`, hereditarily, and nothing else).  Purely syntactic, unlike `inT`. -/
def FragR : Term → Bool
  | zero => true
  | M => true
  | add a b => FragR a && FragR b
  | omg a => FragR a
  | phi a b => FragR a && FragR b
  | psi k a => k.isR && FragR k && FragR a
  | Z a => FragR a

theorem fragR_add {a b : Term} (h : FragR (add a b) = true) :
    FragR a = true ∧ FragR b = true := by
  simp only [FragR, Bool.and_eq_true] at h; exact h

theorem fragR_omg {a : Term} (h : FragR (omg a) = true) : FragR a = true := h

theorem fragR_phi {a b : Term} (h : FragR (phi a b) = true) :
    FragR a = true ∧ FragR b = true := by
  simp only [FragR, Bool.and_eq_true] at h; exact h

theorem fragR_psi {k a : Term} (h : FragR (psi k a) = true) :
    k.isR = true ∧ FragR k = true ∧ FragR a = true := by
  simp only [FragR, Bool.and_eq_true] at h; exact ⟨h.1.1, h.1.2, h.2⟩

theorem fragR_Z {a : Term} (h : FragR (Z a) = true) : FragR a = true := h

/-- `Frag2` sits inside `FragR`: §8.2's fragment has no `ψ` at all. -/
theorem frag2_le_fragR : ∀ (t : Term), Frag2 t = true → FragR t = true
  | zero, _ => rfl
  | M, _ => rfl
  | psi _ _, h => by simp [Frag2] at h
  | Z _, h => by simp [Frag2] at h
  | omg a, h => frag2_le_fragR a h
  | add a b, h => by
    have hab := frag2_add h
    show (FragR a && FragR b) = true
    rw [frag2_le_fragR a hab.1, frag2_le_fragR b hab.2]; rfl
  | phi a b, h => by
    have hab := frag2_phi h
    show (FragR a && FragR b) = true
    rw [frag2_le_fragR a hab.1, frag2_le_fragR b hab.2]; rfl

/-- The LEVEL of a non-sum: `φ̄`, `ψ`, `Z` at 1, `M` at 2, `ω̄^·` at 3, `0` at 0
    (`⊕` gets 4 and is excluded by hypothesis).  §8.1's table says the order on
    non-sums is by level first, with ties broken inside the level.  Making that a
    function is what collapses the all-non-sum case from 125 shape triples to the
    27 of level 1 plus three schematic cases — without it the fan-out would have to
    grind out ~98 constant-clause triples by hand. -/
def lvl : Term → Nat
  | zero => 0
  | phi _ _ => 1
  | psi _ _ => 1
  | Z _ => 1
  | M => 2
  | omg _ => 3
  | add _ _ => 4

/-- Level strictly up ⟹ below.  Every instance is a constant clause of §8.1/§8.3. -/
def LvlUp : Prop :=
  ∀ (f : Nat) (x y : Term), NSum x = true → NSum y = true →
    lvl x < lvl y → ltF (f + 1) x y = true

/-- Level strictly down ⟹ not below.  Contrapositive: `a < b` forbids `lvl a` from
    exceeding `lvl b`, which is what pins `a < b < c` to one level. -/
def LvlDown : Prop :=
  ∀ (f : Nat) (x y : Term), NSum x = true → NSum y = true →
    lvl y < lvl x → ltF (f + 1) x y = false

/-- The fragment must contain `α*`, or the induction hypotheses cannot be applied to
    it — the one genuinely new obligation the `starF` clauses create (§8.4(ii)). -/
def StarClosed : Prop :=
  ∀ (f : Nat) (t : Term), FragR t = true → FragR (starF f t) = true

/-! #### §8.4.1 The exact statements Phase B must produce -/

/-- ASYMMETRY on `FragR`, same fuel. -/
def Asym3 : Prop :=
  ∀ (a b : Term), FragR a = true → FragR b = true → ∀ f, a.deg + b.deg ≤ f →
    ltF f a b = true → ltF f b a = false

/-- COMPARABILITY on `FragR`, same fuel. -/
def Comp3 : Prop :=
  ∀ (a b : Term), FragR a = true → FragR b = true → ∀ f, a.deg + b.deg ≤ f →
    ltF f a b = true ∨ a = b ∨ ltF f b a = true

/-- TRANSITIVITY on `FragR`, same fuel. -/
def Trans3 : Prop :=
  ∀ (a b c : Term), FragR a = true → FragR b = true → FragR c = true →
    ∀ f, a.deg + b.deg + c.deg ≤ f →
    ltF f a b = true → ltF f b c = true → ltF f a c = true

/-! #### §8.4.2 The interface every case lemma is written against

`IH_ASYM`/`IH_COMP` are §7.3's two simultaneous hypotheses at the bound `n`;
`IH_TR1`/`IH_TR2` are §7.4's two, spelled out.  A case lemma takes them as ordinary
parameters, so it is provable IN ISOLATION and Phase B only has to apply it. -/

def IH_ASYM (n : Nat) : Prop :=
  ∀ (x y : Term), FragR x = true → FragR y = true → x.deg + y.deg ≤ n →
    ∀ g, n ≤ g → ltF g x y = true → ltF g y x = false

def IH_COMP (n : Nat) : Prop :=
  ∀ (x y : Term), FragR x = true → FragR y = true → x.deg + y.deg ≤ n →
    ∀ g, n ≤ g → ltF g x y = true ∨ x = y ∨ ltF g y x = true

/-- `TR1`: the middle term may be replaced by anything of degree ≤ `n`. -/
def IH_TR1 (n : Nat) : Prop :=
  ∀ (x y z : Term), FragR x = true → FragR y = true → FragR z = true → y.deg ≤ n →
    ∀ g, x.deg + y.deg + z.deg ≤ g →
    ltF g x y = true → ltF g y z = true → ltF g x z = true

/-- `TR2`: the middle term stays `b`; `x` and `z` shrink in degree SUM. -/
def IH_TR2 (b : Term) (m : Nat) : Prop :=
  ∀ (x z : Term), FragR x = true → FragR z = true → x.deg + z.deg ≤ m →
    ∀ g, x.deg + b.deg + z.deg ≤ g →
    ltF g x b = true → ltF g b z = true → ltF g x z = true

/-- The shape of every ASYMMETRY case lemma. -/
def AsymCase (A B : Term) (n f' : Nat) : Prop :=
  FragR A = true → FragR B = true → A.deg + B.deg ≤ n + 1 → n ≤ f' →
  IH_ASYM n → IH_COMP n →
  ltF (f' + 1) A B = true → ltF (f' + 1) B A = false

/-- The shape of every COMPARABILITY case lemma.  `A ≠ B` is discharged by the
    caller, exactly as in §7.3. -/
def CompCase (A B : Term) (n f' : Nat) : Prop :=
  FragR A = true → FragR B = true → A.deg + B.deg ≤ n + 1 → n ≤ f' →
  IH_ASYM n → IH_COMP n → A ≠ B →
  (ltF (f' + 1) A B = true ∨ ltF (f' + 1) B A = true)

/-- The shape of every TRANSITIVITY case lemma.  `Asym3`/`Comp3` are available
    because Stage I completes before Stage II, exactly as in §8.2. -/
def TransCase (A B C : Term) (n m f' : Nat) : Prop :=
  FragR A = true → FragR B = true → FragR C = true →
  B.deg ≤ n + 1 → A.deg + C.deg ≤ m + 1 → A.deg + B.deg + C.deg ≤ f' + 1 →
  Asym3 → Comp3 → IH_TR1 n → IH_TR2 B m →
  ltF (f' + 1) A B = true → ltF (f' + 1) B C = true → ltF (f' + 1) A C = true

/-! The three worked shapes, type-checked, as the fan-out will see them.  (The full
    numbered enumeration is delivered as data in the lane report; these `#check`s
    exist so the interface itself is machine-verified, not prose.) -/

-- CASE T-14 (ψ/ψ/ψ), the analogue of §7.4's case (8):
#check (∀ (k a p b q c : Term) (n m f' : Nat),
          TransCase (psi k a) (psi p b) (psi q c) n m f' : Prop)
-- CASE T-27 (Z/Z/Z), the one that routes through `starF` twice:
#check (∀ (x y z : Term) (n m f' : Nat), TransCase (Z x) (Z y) (Z z) n m f' : Prop)
-- CASE C-ψψ, where `κ ∈ R` is consumed:
#check (∀ (k a p b : Term) (n f' : Nat), CompCase (psi k a) (psi p b) n f' : Prop)

/-! #### §8.4.3 Receipts for the design measurements -/

#guard FragR (psi (Z zero) zero) == true          -- an R head is admitted
#guard FragR (psi M zero) == false                -- ... and the §8 witness is not
#guard FragR (psi (psi M zero) zero) == false
#guard Frag2 (omg M) == true && FragR (omg M) == true
#guard FragR (Z (psi M zero)) == false            -- hereditary, not just top-level
#guard inT (psi (Z zero) zero) == true && FragR (psi (Z zero) zero) == true

/-! ### §8.5 STAGE 3b, EXECUTED: `FragR` carries a strict linear order

WHAT IS PROVED.  Everything §7 proves for `Frag` and §8.2 for `Frag2`, now for
`FragR` — §8.4's fragment, in which `ψ` and `Z` are admitted subject only to
[R91] 2.1(vi)'s `κ ∈ R`, hereditarily: `ltF_asymm3`, `ltF_comparable3`,
`trans_ltF3`, and the `lt` forms `lt_asymm3` / `lt_comparable3` / `lt_trans3` /
`lt_trichotomy3` / `le_trans3` / `le_of_not_lt3` / `lt_of_not_le3`.  Since
`inT ⊆ FragR` (`inT_le_fragR`), §8.5.4 reads all of it off for the genuine terms of
𝔗(M); `lt_trichotomy_inT` is the statement §6's map set as the target of D2.

HOW IT WAS PRODUCED, and what that means for reading it.  §8.4 decomposed the two
inductions into case lemmas provable IN ISOLATION, each taking its induction
hypotheses as ordinary parameters (`AsymCase` / `CompCase` / `TransCase`).  The
cases below were then proved independently and in parallel against that interface,
and this section is their assembly.  Each case therefore stands on its own and can
be re-checked on its own — which is the property that made the repair below
findable.

THE ONE REPAIR.  Of the cases returned as verified, `t28_psi_Z_Z` did NOT compile
on re-checking, alone or in company: it ended at `simp [h4]` with the goal at fuel
`f' + 1` while `h4` lives at `f'`, so clause 2.3.6 was never unfolded.  It is
repaired in place, the repair is marked in the proof, and everything else is as
returned.  Recorded because the claim was "80 of 80 verified" and 79 is the number
that survived re-checking; the assembly below is what re-checked them.

WHAT §8.4 PREDICTED, AND WHAT HELD.  The measure is §7.4's, unchanged; the two
stages are §7.3's and §7.4's, unchanged; `le (star d) d` was never needed anywhere,
as §8.4(ii) predicted against §8.3.2's earlier and withdrawn claim; `κ ∈ R` is
consumed only in the `ψ`-vs-`ψ` comparability case, as §8.4(iii) said; and no case
needed the K_κ conjunct, so the fragment never had to be shrunk to `FragR && inT`.
The empirical gate behind the design is `table/order-sweep-2026-08-09.txt` and its
Phase-B extension; what is below is a theorem and does not depend on either. -/

/-! #### §8.5.1 The case lemmas, as proved against §8.4's interface

Each block keeps the marker and verification note it was returned with, so a
per-case provenance trail survives in the file. -/

-- Stage 3b Phase B: collected case proofs from the fan-out (13 agents, 80 cases, 0 unproved).
-- Each block is the source an agent compiled against `import Evidence.WF` + `open TM TM.Term Evidence.WF`
-- on kimina 12346 at commit a4ef664 (v0.1.74). Assembly is psiz1's Phase B.

-- ===== [S1-S4] S1 : starClosed : StarClosed =====
-- verdict: kimina OK — POST http://localhost:12346/api/check, response.messages = [] (verified twice: alone as snippet id `s1a`, and jointly with S2/S3/S4/S1b as snippet id `final`)
-- notes: Induction on f, then cases on t, exactly as the assignment predicted. The two ite cases (add, phi) use §8.3's `starF_succ_add` / `starF_succ_phi` to expose the `if`, then `cases ltF g (starF g a) (starF g b)` followed by a defeq `show FragR (starF g _) = true` — i.e. verbatim the pattern of `starF_z

/-- **S1** `StarClosed` — the one genuinely new obligation of §8.4(ii): the
    fragment contains `α*`, so the induction hypotheses can be applied to it. -/
theorem starClosed : StarClosed := by
  intro f
  induction f with
  | zero => intro t _; rfl
  | succ g ih =>
    intro t h
    cases t with
    | zero => rfl
    | M => rfl
    | psi k a => exact h
    | Z a => exact h
    | omg a => exact ih a (fragR_omg h)
    | add a b =>
      rw [starF_succ_add]
      cases ltF g (starF g a) (starF g b)
      · show FragR (starF g a) = true
        exact ih a (fragR_add h).1
      · show FragR (starF g b) = true
        exact ih b (fragR_add h).2
    | phi a b =>
      rw [starF_succ_phi]
      cases ltF g (starF g a) (starF g b)
      · show FragR (starF g a) = true
        exact ih a (fragR_phi h).1
      · show FragR (starF g b) = true
        exact ih b (fragR_phi h).2

-- ===== [S1-S4] S1b : star_fragR (default-fuel corollary of S1) =====
-- verdict: kimina OK — snippet id `final`, response.messages = []
-- notes: One-line corollary at the default fuel (`star t = starF (2 * t.deg + 8) t`). Not requested, but every caller outside the fuel layer will want this form, and it costs nothing. Include or drop at the integrator's discretion.
theorem star_fragR (t : Term) (h : FragR t = true) : FragR (star t) = true :=
  starClosed _ t h

-- ===== [S1-S4] S2 : lvlUp : LvlUp =====
-- verdict: kimina OK — verified alone as snippet id `s2` and jointly as `final`; response.messages = []
-- notes: All 49 shape pairs written out. 13 are killed by NSum (`Bool.noConfusion hx/hy`), 29 by the level hypothesis, and the 7 that survive are: `0 < M/ω̄/φ̄/ψ/Z` (five uses of §7.1's `ltF_left_zero`) and the seven constant clauses `φ̄/ψ/Z < M`, `φ̄/ψ/Z < ω̄`, `M < ω̄` — every one of them `rfl`, i.e. liter

/-- **S2** `LvlUp` — level strictly up implies below (§8.4's level table). -/
theorem lvlUp : LvlUp := by
  intro f x y hx hy hlt
  cases x with
  | add a b => exact Bool.noConfusion hx
  | zero =>
    cases y with
    | add c d => exact Bool.noConfusion hy
    | zero => exact absurd hlt (by simp [lvl])
    | M => exact ltF_left_zero (by omega) (by intro hc; exact Term.noConfusion hc)
    | omg c => exact ltF_left_zero (by omega) (by intro hc; exact Term.noConfusion hc)
    | phi c d => exact ltF_left_zero (by omega) (by intro hc; exact Term.noConfusion hc)
    | psi p c => exact ltF_left_zero (by omega) (by intro hc; exact Term.noConfusion hc)
    | Z c => exact ltF_left_zero (by omega) (by intro hc; exact Term.noConfusion hc)
  | M =>
    cases y with
    | add c d => exact Bool.noConfusion hy
    | zero => exact absurd hlt (by simp [lvl])
    | M => exact absurd hlt (by simp [lvl])
    | omg c => rfl
    | phi c d => exact absurd hlt (by simp [lvl])
    | psi p c => exact absurd hlt (by simp [lvl])
    | Z c => exact absurd hlt (by simp [lvl])
  | omg a =>
    cases y with
    | add c d => exact Bool.noConfusion hy
    | zero => exact absurd hlt (by simp [lvl])
    | M => exact absurd hlt (by simp [lvl])
    | omg c => exact absurd hlt (by simp [lvl])
    | phi c d => exact absurd hlt (by simp [lvl])
    | psi p c => exact absurd hlt (by simp [lvl])
    | Z c => exact absurd hlt (by simp [lvl])
  | phi a b =>
    cases y with
    | add c d => exact Bool.noConfusion hy
    | zero => exact absurd hlt (by simp [lvl])
    | M => rfl
    | omg c => rfl
    | phi c d => exact absurd hlt (by simp [lvl])
    | psi p c => exact absurd hlt (by simp [lvl])
    | Z c => exact absurd hlt (by simp [lvl])
  | psi k a =>
    cases y with
    | add c d => exact Bool.noConfusion hy
    | zero => exact absurd hlt (by simp [lvl])
    | M => rfl
    | omg c => rfl
    | phi c d => exact absurd hlt (by simp [lvl])
    | psi p c => exact absurd hlt (by simp [lvl])
    | Z c => exact absurd hlt (by simp [lvl])
  | Z a =>
    cases y with
    | add c d => exact Bool.noConfusion hy
    | zero => exact absurd hlt (by simp [lvl])
    | M => rfl
    | omg c => rfl
    | phi c d => exact absurd hlt (by simp [lvl])
    | psi p c => exact absurd hlt (by simp [lvl])
    | Z c => exact absurd hlt (by simp [lvl])

-- ===== [S1-S4] S3 : lvlDown : LvlDown =====
-- verdict: kimina OK — verified alone as snippet id `s3` and jointly as `final`; response.messages = []
-- notes: Mirror image of S2, same 49-way enumeration. Surviving pairs: 5 uses of §7.1's `ltF_right_zero` (`x ≮ 0` for x = M/ω̄/φ̄/ψ/Z), plus the 7 constant clauses `M ≮ φ̄/ψ/Z`, `ω̄ ≮ φ̄/ψ/Z`, `ω̄ ≮ M` — again all `rfl`, i.e. §8.1's `ltF_succ_M_phi`, `ltF_succ_M_psi`, `ltF_succ_M_Z`, `ltF_succ_omg_phi`, `ltF

/-- **S3** `LvlDown` — level strictly down implies not below. -/
theorem lvlDown : LvlDown := by
  intro f x y hx hy hlt
  cases x with
  | add a b => exact Bool.noConfusion hx
  | zero =>
    cases y with
    | add c d => exact Bool.noConfusion hy
    | zero => exact absurd hlt (by simp [lvl])
    | M => exact absurd hlt (by simp [lvl])
    | omg c => exact absurd hlt (by simp [lvl])
    | phi c d => exact absurd hlt (by simp [lvl])
    | psi p c => exact absurd hlt (by simp [lvl])
    | Z c => exact absurd hlt (by simp [lvl])
  | M =>
    cases y with
    | add c d => exact Bool.noConfusion hy
    | zero => exact ltF_right_zero _ _
    | M => exact absurd hlt (by simp [lvl])
    | omg c => exact absurd hlt (by simp [lvl])
    | phi c d => rfl
    | psi p c => rfl
    | Z c => rfl
  | omg a =>
    cases y with
    | add c d => exact Bool.noConfusion hy
    | zero => exact ltF_right_zero _ _
    | M => rfl
    | omg c => exact absurd hlt (by simp [lvl])
    | phi c d => rfl
    | psi p c => rfl
    | Z c => rfl
  | phi a b =>
    cases y with
    | add c d => exact Bool.noConfusion hy
    | zero => exact ltF_right_zero _ _
    | M => exact absurd hlt (by simp [lvl])
    | omg c => exact absurd hlt (by simp [lvl])
    | phi c d => exact absurd hlt (by simp [lvl])
    | psi p c => exact absurd hlt (by simp [lvl])
    | Z c => exact absurd hlt (by simp [lvl])
  | psi k a =>
    cases y with
    | add c d => exact Bool.noConfusion hy
    | zero => exact ltF_right_zero _ _
    | M => exact absurd hlt (by simp [lvl])
    | omg c => exact absurd hlt (by simp [lvl])
    | phi c d => exact absurd hlt (by simp [lvl])
    | psi p c => exact absurd hlt (by simp [lvl])
    | Z c => exact absurd hlt (by simp [lvl])
  | Z a =>
    cases y with
    | add c d => exact Bool.noConfusion hy
    | zero => exact ltF_right_zero _ _
    | M => exact absurd hlt (by simp [lvl])
    | omg c => exact absurd hlt (by simp [lvl])
    | phi c d => exact absurd hlt (by simp [lvl])
    | psi p c => exact absurd hlt (by simp [lvl])
    | Z c => exact absurd hlt (by simp [lvl])

-- ===== [S1-S4] S4 : inT_le_fragR : ∀ (t : Term), inT t = true → FragR t = true =====
-- verdict: kimina OK — verified alone as snippet id `s4` and jointly as `final`; response.messages = []
-- notes: Structural, in the exact style of §8.4's `frag2_le_fragR`. THE Kset CONJUNCT IS NEVER TOUCHED, as instructed: in the `psi` case only `h.1.1.1.1 : k.isR = true`, `h.1.1.1.2 : inT k = true` and `h.1.1.2 : inT a = true` are taken, and `(Kset k a).all …` is left as `h.2`, untouched. FINDING WORTH RECORD

/-- **S4** `inT_le_fragR` — `𝔗(M)` sits inside the Stage-3b fragment, so every
    `inT` form is a corollary of the `FragR` order theory.  Only the `ψ` case has
    content: 2.1(vi)'s `κ.isR` is exactly `FragR`'s side condition, and the `Kset`
    conjunct is never touched. -/
theorem inT_le_fragR : ∀ (t : Term), inT t = true → FragR t = true
  | zero, _ => rfl
  | M, _ => rfl
  | add a b, h => by
    simp only [inT, Bool.and_eq_true] at h
    show (FragR a && FragR b) = true
    rw [inT_le_fragR a h.1.1.2, inT_le_fragR b h.1.2]; rfl
  | omg a, h => by
    simp only [inT, Bool.and_eq_true] at h
    exact inT_le_fragR a h.1
  | phi a b, h => by
    simp only [inT, Bool.and_eq_true] at h
    show (FragR a && FragR b) = true
    rw [inT_le_fragR a h.1.1.1, inT_le_fragR b h.1.1.2]; rfl
  | psi k a, h => by
    simp only [inT, Bool.and_eq_true] at h
    show (k.isR && FragR k && FragR a) = true
    rw [h.1.1.1.1, inT_le_fragR k h.1.1.1.2, inT_le_fragR a h.1.1.2]; rfl
  | Z a, h => inT_le_fragR a h

-- ===== [A1-A5] A1i : a1_zero_left =====
-- verdict: kimina OK (messages: [], both standalone and in the consolidated snippet)
-- notes: A1 の zero 側。§8.2 asym の `exact ltF_right_zero _ b` をそのまま転写。IH は一切消費しない。zero vs anything は左右で結論が別物なので 2 本に分けた (A1i / A1ii)。
theorem a1_zero_left : ∀ (b : Term) (n f' : Nat), AsymCase zero b n f' := by
  intro b n f' _ _ _ _ _ _ _
  exact ltF_right_zero _ b

-- ===== [A1-A5] A1ii : a1_zero_right =====
-- verdict: kimina OK (messages: [])
-- notes: 仮説 ltF (f'+1) a zero = true が ltF_right_zero と矛盾するので vacuous。§8.2 の `rw [ltF_right_zero] at h; exact Bool.noConfusion h` と同一。
theorem a1_zero_right : ∀ (a : Term) (n f' : Nat), AsymCase a zero n f' := by
  intro a n f' _ _ _ _ _ _ h
  rw [ltF_right_zero] at h; exact Bool.noConfusion h

-- ===== [A1-A5] C1i : c1_zero_left =====
-- verdict: kimina OK (messages: [])
-- notes: 2.3.1。CompCase は §8.2 の 3 択 (lt ∨ eq ∨ lt) ではなく A ≠ B 込みの 2 択なので、§8.2 の `Or.inl` 系がそのまま、`Or.inr (Or.inr _)` は `Or.inr _` に潰れる。ltF_left_zero の 1 ≤ f'+1 は omega。
theorem c1_zero_left : ∀ (b : Term) (n f' : Nat), CompCase zero b n f' := by
  intro b n f' _ _ _ _ _ _ hne
  exact Or.inl (ltF_left_zero (by omega) (Ne.symm hne))

-- ===== [A1-A5] C1ii : c1_zero_right =====
-- verdict: kimina OK (messages: [])
-- notes: 同上の右版。hne : a ≠ zero がそのまま ltF_left_zero の引数になる。
theorem c1_zero_right : ∀ (a : Term) (n f' : Nat), CompCase a zero n f' := by
  intro a n f' _ _ _ _ _ _ hne
  exact Or.inr (ltF_left_zero (by omega) hne)

-- ===== [A1-A5] A2 : a2_add_add =====
-- verdict: kimina OK (messages: [])
-- notes: 2.3.16 対 2.3.16。§8.2 cmp_aux2 の該当ブロックを frag2_add -> fragR_add に置換しただけ。hab は ne_of_ltF h から取る (§8.2 では外側で用意していたもの)。eA/eB/deg_pos は omega 用の帳簿で、これを落とすと omega が落ちることをミュータント mut_A2 で確認済み。
theorem a2_add_add : ∀ (p q r s : Term) (n f' : Nat),
    AsymCase (add p q) (add r s) n f' := by
  intro p q r s n f' hfa hfb hd hnf IHa _ h
  have hab : add p q ≠ add r s := ne_of_ltF h
  have hfp := (fragR_add hfa).1; have hfq := (fragR_add hfa).2
  have hfr := (fragR_add hfb).1; have hfs := (fragR_add hfb).2
  have dp := deg_pos p; have dq := deg_pos q
  have dr := deg_pos r; have ds := deg_pos s
  have eA : (add p q).deg = 1 + p.deg + q.deg := rfl
  have eB : (add r s).deg = 1 + r.deg + s.deg := rfl
  rw [ltF_succ_add_add _ hab] at h
  rw [ltF_succ_add_add _ (Ne.symm hab)]
  by_cases hpr : p = r
  · subst hpr
    rw [if_pos rfl] at h
    rw [if_pos rfl]
    exact IHa q s hfq hfs (by omega) f' hnf h
  · rw [if_neg hpr] at h
    rw [if_neg (Ne.symm hpr)]
    exact IHa p r hfp hfr (by omega) f' hnf h

-- ===== [A1-A5] C2 : c2_add_add =====
-- verdict: kimina OK (messages: [])
-- notes: A2 の comparability 版。hab は CompCase が引数として供給する (§8.2 では by_cases で作っていた) ので by_cases hab が不要になり、その分短い。
theorem c2_add_add : ∀ (p q r s : Term) (n f' : Nat),
    CompCase (add p q) (add r s) n f' := by
  intro p q r s n f' hfa hfb hd hnf _ IHc hab
  have hfp := (fragR_add hfa).1; have hfq := (fragR_add hfa).2
  have hfr := (fragR_add hfb).1; have hfs := (fragR_add hfb).2
  have dp := deg_pos p; have dq := deg_pos q
  have dr := deg_pos r; have ds := deg_pos s
  have eA : (add p q).deg = 1 + p.deg + q.deg := rfl
  have eB : (add r s).deg = 1 + r.deg + s.deg := rfl
  rw [ltF_succ_add_add _ hab, ltF_succ_add_add _ (Ne.symm hab)]
  by_cases hpr : p = r
  · subst hpr
    rw [if_pos rfl, if_pos rfl]
    have hqs : q ≠ s := fun hc => hab (by rw [hc])
    rcases IHc q s hfq hfs (by omega) f' hnf with h1 | h1 | h1
    · exact Or.inl h1
    · exact absurd h1 hqs
    · exact Or.inr h1
  · rw [if_neg hpr, if_neg (Ne.symm hpr)]
    rcases IHc p r hfp hfr (by omega) f' hnf with h1 | h1 | h1
    · exact Or.inl h1
    · exact absurd h1 hpr
    · exact Or.inr h1

-- ===== [A1-A5] A3 : a3_add_nsum =====
-- verdict: kimina OK (messages: [])
-- notes: 2.3.10 forward / 2.3.11 backward。t は OPAQUE な非和のまま (psi と Z も含む) — これが §8.2 の設計どおり、和がらみのケースを一切ばらさずに済む理由。t ≠ zero と NSum t は schema の前に通常の引数として置いた (§8.4 が「induction hypotheses as ordinary parameters」と言っているのと同じ扱い)。FragR q は使わない。
theorem a3_add_nsum : ∀ (p q t : Term) (n f' : Nat), t ≠ zero → NSum t = true →
    AsymCase (add p q) t n f' := by
  intro p q t n f' h0 ht hfa hfb hd hnf IHa _ h
  have hfp := (fragR_add hfa).1
  have dp := deg_pos p; have dq := deg_pos q; have dt := deg_pos t
  have eA : (add p q).deg = 1 + p.deg + q.deg := rfl
  rw [ltF_succ_add_nsum _ h0 ht] at h
  rw [ltF_succ_nsum_add _ h0 ht]
  have hne : t ≠ p := by
    intro hc; rw [hc, ltF_irrefl] at h; exact Bool.noConfusion h
  have h2 : ltF f' t p = false := IHa p t hfp hfb (by omega) f' hnf h
  simp [hne, h2]

-- ===== [A1-A5] C3 : c3_add_nsum =====
-- verdict: kimina OK (messages: [])
-- notes: A3 の comparability 版。A ≠ B は使わない (2.3.10/2.3.11 は頭部だけで決まるため)。
theorem c3_add_nsum : ∀ (p q t : Term) (n f' : Nat), t ≠ zero → NSum t = true →
    CompCase (add p q) t n f' := by
  intro p q t n f' h0 ht hfa hfb hd hnf _ IHc _
  have hfp := (fragR_add hfa).1
  have dp := deg_pos p; have dq := deg_pos q; have dt := deg_pos t
  have eA : (add p q).deg = 1 + p.deg + q.deg := rfl
  rw [ltF_succ_add_nsum _ h0 ht, ltF_succ_nsum_add _ h0 ht]
  rcases IHc p t hfp hfb (by omega) f' hnf with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (by simp [h1])
  · exact Or.inr (by simp [h1])

-- ===== [A1-A5] A4 : a4_nsum_add =====
-- verdict: kimina OK (messages: [])
-- notes: 2.3.11 forward / 2.3.10 backward。s は OPAQUE な非和。h1 : s = c の枝は ltF_irrefl で潰れる (§8.2 と同一)。
theorem a4_nsum_add : ∀ (s c d : Term) (n f' : Nat), s ≠ zero → NSum s = true →
    AsymCase s (add c d) n f' := by
  intro s c d n f' h0 hs hfa hfb hd hnf IHa _ h
  have hfc := (fragR_add hfb).1
  have dc := deg_pos c; have dd := deg_pos d; have ds := deg_pos s
  have eB : (add c d).deg = 1 + c.deg + d.deg := rfl
  rw [ltF_succ_nsum_add _ h0 hs] at h
  rw [ltF_succ_add_nsum _ h0 hs]
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h1 | h1
  · rw [← h1]; exact ltF_irrefl _ _
  · exact IHa s c hfa hfc (by omega) f' hnf h1

-- ===== [A1-A5] C4 : c4_nsum_add =====
-- verdict: kimina OK (messages: [])
-- notes: A4 の comparability 版。s = c でも s < c でも s <= c なので最初の 2 枝がともに Or.inl になる。
theorem c4_nsum_add : ∀ (s c d : Term) (n f' : Nat), s ≠ zero → NSum s = true →
    CompCase s (add c d) n f' := by
  intro s c d n f' h0 hs hfa hfb hd hnf _ IHc _
  have hfc := (fragR_add hfb).1
  have dc := deg_pos c; have dd := deg_pos d; have ds := deg_pos s
  have eB : (add c d).deg = 1 + c.deg + d.deg := rfl
  rw [ltF_succ_nsum_add _ h0 hs, ltF_succ_add_nsum _ h0 hs]
  rcases IHc s c hfa hfc (by omega) f' hnf with h1 | h1 | h1
  · exact Or.inl (by simp [h1])
  · exact Or.inl (by simp [h1])
  · exact Or.inr h1

-- ===== [A1-A5] A5 : a5_lvl =====
-- verdict: kimina OK (messages: [])
-- notes: レベルが異なる非和どうし。§8.4 の指示どおり S3 = LvlDown を仮説として取った。実測: 必要なのは S3 だけで S2 は不要 (lvl x < lvl y なら結論そのもの、lvl y < lvl x なら仮説 h が矛盾)。lvl x ≠ lvl y は load-bearing — 落とすと omega が破れることをミュータント mut_A5_drop_lvl_ne で確認済み。なお lvl zero = 0 なので本補題は zero がらみのレベル差も覆っており、A1/C1 と無害に重複する。
theorem a5_lvl : ∀ (x y : Term) (n f' : Nat), LvlDown →
    NSum x = true → NSum y = true → lvl x ≠ lvl y → AsymCase x y n f' := by
  intro x y n f' hdn hnx hny hlv _ _ _ _ _ _ h
  rcases Nat.lt_or_ge (lvl x) (lvl y) with hl | hl
  · exact hdn f' y x hny hnx hl
  · rw [hdn f' x y hnx hny (by omega)] at h; exact Bool.noConfusion h

-- ===== [A1-A5] C5 : c5_lvl =====
-- verdict: kimina OK (messages: [])
-- notes: C5 は対称に S2 = LvlUp だけを消費する。IH_ASYM / IH_COMP も A ≠ B も使わない。
theorem c5_lvl : ∀ (x y : Term) (n f' : Nat), LvlUp →
    NSum x = true → NSum y = true → lvl x ≠ lvl y → CompCase x y n f' := by
  intro x y n f' hup hnx hny hlv _ _ _ _ _ _ _
  rcases Nat.lt_or_ge (lvl x) (lvl y) with hl | hl
  · exact Or.inl (hup f' x y hnx hny hl)
  · exact Or.inr (hup f' y x hny hnx (by omega))

-- ===== [A1-A5] AUX-sum-cases : fragR_sum_cases =====
-- verdict: kimina OK (messages: []) — 担当外の補助。assembler がこれなしでは分岐できないので添付
-- notes: GAP の指摘でもある: WF.lean には frag2_sum_cases / frag2_nsum_cases はあるが FragR 版が存在しない (#check で確認)。Phase B の assembler は 0 / 和 / 非和 の三分岐にこれを必要とする。frag2 版と違い psi と Z も非和側に落ちる (Frag2 ではここが simp で潰れていた) 点だけが差分。
theorem fragR_sum_cases {t : Term} (h : FragR t = true) :
    t = zero
    ∨ (∃ x y, t = add x y ∧ FragR x = true ∧ FragR y = true)
    ∨ (t ≠ zero ∧ NSum t = true) := by
  cases t with
  | zero => exact Or.inl rfl
  | add x y => exact Or.inr (Or.inl ⟨x, y, rfl, (fragR_add h).1, (fragR_add h).2⟩)
  | M => exact Or.inr (Or.inr ⟨by intro hc; exact Term.noConfusion hc, rfl⟩)
  | omg x => exact Or.inr (Or.inr ⟨by intro hc; exact Term.noConfusion hc, rfl⟩)
  | phi x y => exact Or.inr (Or.inr ⟨by intro hc; exact Term.noConfusion hc, rfl⟩)
  | psi k x => exact Or.inr (Or.inr ⟨by intro hc; exact Term.noConfusion hc, rfl⟩)
  | Z x => exact Or.inr (Or.inr ⟨by intro hc; exact Term.noConfusion hc, rfl⟩)

-- ===== [A1-A5] AUX-nsum-cases : fragR_nsum_cases =====
-- verdict: kimina OK (messages: [])
-- notes: 担当外の補助。5 分岐 (M / omg / phi / psi / Z)。psi の枝が k.isR = true を運び出す点が重要 — §8.4(iii) が「kappa in R が本質的に効くのは 2.3.14 の comparability だけ」と言っている、その isR をここで取り出す。同レベル (level 1) の 9 組を担当するエージェントはこれを使うことになる。
theorem fragR_nsum_cases {t : Term} (h : FragR t = true) (h0 : t ≠ zero)
    (hn : NSum t = true) :
    t = M
    ∨ (∃ x, t = omg x ∧ FragR x = true)
    ∨ (∃ x y, t = phi x y ∧ FragR x = true ∧ FragR y = true)
    ∨ (∃ k x, t = psi k x ∧ k.isR = true ∧ FragR k = true ∧ FragR x = true)
    ∨ (∃ x, t = Z x ∧ FragR x = true) := by
  cases t with
  | zero => exact absurd rfl h0
  | add x y => simp [NSum] at hn
  | M => exact Or.inl rfl
  | omg x => exact Or.inr (Or.inl ⟨x, rfl, fragR_omg h⟩)
  | phi x y => exact Or.inr (Or.inr (Or.inl ⟨x, y, rfl, (fragR_phi h).1, (fragR_phi h).2⟩))
  | psi k x =>
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨k, x, rfl, (fragR_psi h).1, (fragR_psi h).2.1, (fragR_psi h).2.2⟩)))
  | Z x => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨x, rfl, fragR_Z h⟩)))

-- ===== [A1-A5] INTEG : cmp_aux3_skeleton =====
-- verdict: kimina OK (messages: []) — 統合テスト。A1..A5/C1..C5 が実際に組み上がることの受領証
-- notes: 担当外だが最も重要な受領証: 私の 12 本 + S2/S3 + fragR_sum_cases だけで Stage I 全体の骨格が実際に閉じ、残るのは SA/SC (レベルが等しい非和どうし) だけであることを機械検証した。これで「証明はできたが interface が噛み合わない」という失敗モードが排除される。IHa/IHc の型は IH_ASYM n / IH_COMP n と defeq なのでそのまま渡せる (unfold 不要)。CompCase は 2 択なので `wrap` で 3 択に持ち上げている。
theorem cmp_aux3_skeleton
    (SA : ∀ (x y : Term) (n f' : Nat), x ≠ zero → y ≠ zero →
            NSum x = true → NSum y = true → lvl x = lvl y → AsymCase x y n f')
    (SC : ∀ (x y : Term) (n f' : Nat), x ≠ zero → y ≠ zero →
            NSum x = true → NSum y = true → lvl x = lvl y → CompCase x y n f') :
    ∀ (n : Nat),
    (∀ (a b : Term), FragR a = true → FragR b = true → a.deg + b.deg ≤ n →
      ∀ f, n ≤ f → ltF f a b = true → ltF f b a = false)
  ∧ (∀ (a b : Term), FragR a = true → FragR b = true → a.deg + b.deg ≤ n →
      ∀ f, n ≤ f → (ltF f a b = true ∨ a = b ∨ ltF f b a = true)) := by
  intro n
  induction n with
  | zero =>
    exact ⟨by intro a b _ _ hd; have := deg_pos a; have := deg_pos b; omega,
           by intro a b _ _ hd; have := deg_pos a; have := deg_pos b; omega⟩
  | succ n IH =>
    obtain ⟨IHa, IHc⟩ := IH
    constructor
    · intro a b hfa hfb hd f hf h
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hf' : n ≤ f' := by omega
      rcases fragR_sum_cases hfa with rfl | ⟨p, q, rfl, hfp, hfq⟩ | ⟨ha0, hna⟩
      · exact a1_zero_left b n f' hfa hfb hd hf' IHa IHc h
      · rcases fragR_sum_cases hfb with rfl | ⟨r, s, rfl, hfr, hfs⟩ | ⟨hb0, hnb⟩
        · exact a1_zero_right _ n f' hfa hfb hd hf' IHa IHc h
        · exact a2_add_add p q r s n f' hfa hfb hd hf' IHa IHc h
        · exact a3_add_nsum p q b n f' hb0 hnb hfa hfb hd hf' IHa IHc h
      · rcases fragR_sum_cases hfb with rfl | ⟨r, s, rfl, hfr, hfs⟩ | ⟨hb0, hnb⟩
        · exact a1_zero_right _ n f' hfa hfb hd hf' IHa IHc h
        · exact a4_nsum_add a r s n f' ha0 hna hfa hfb hd hf' IHa IHc h
        · by_cases hlv : lvl a = lvl b
          · exact SA a b n f' ha0 hb0 hna hnb hlv hfa hfb hd hf' IHa IHc h
          · exact a5_lvl a b n f' lvlDown hna hnb hlv hfa hfb hd hf' IHa IHc h
    · intro a b hfa hfb hd f hf
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hf' : n ≤ f' := by omega
      by_cases hab : a = b
      · exact Or.inr (Or.inl hab)
      have wrap : (ltF (f' + 1) a b = true ∨ ltF (f' + 1) b a = true) →
          (ltF (f' + 1) a b = true ∨ a = b ∨ ltF (f' + 1) b a = true) := by
        rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
      rcases fragR_sum_cases hfa with rfl | ⟨p, q, rfl, hfp, hfq⟩ | ⟨ha0, hna⟩
      · exact wrap (c1_zero_left b n f' hfa hfb hd hf' IHa IHc hab)
      · rcases fragR_sum_cases hfb with rfl | ⟨r, s, rfl, hfr, hfs⟩ | ⟨hb0, hnb⟩
        · exact wrap (c1_zero_right _ n f' hfa hfb hd hf' IHa IHc hab)
        · exact wrap (c2_add_add p q r s n f' hfa hfb hd hf' IHa IHc hab)
        · exact wrap (c3_add_nsum p q b n f' hb0 hnb hfa hfb hd hf' IHa IHc hab)
      · rcases fragR_sum_cases hfb with rfl | ⟨r, s, rfl, hfr, hfs⟩ | ⟨hb0, hnb⟩
        · exact wrap (c1_zero_right _ n f' hfa hfb hd hf' IHa IHc hab)
        · exact wrap (c4_nsum_add a r s n f' ha0 hna hfa hfb hd hf' IHa IHc hab)
        · by_cases hlv : lvl a = lvl b
          · exact wrap (SC a b n f' ha0 hb0 hna hnb hlv hfa hfb hd hf' IHa IHc hab)
          · exact wrap (c5_lvl a b n f' lvlUp hna hnb hlv hfa hfb hd hf' IHa IHc hab)

-- ===== [A6-A10] A6 : a6 — AsymCase M M (M vs M, trivially excluded) =====
-- verdict: kimina OK (messages: [] apart from info); id a6.lean and again inside the combined all.lean run
-- notes: Verified snippet = the exact two header lines (import Evidence.WF / open TM TM.Term Evidence.WF) followed by this text and nothing else. Consumes no induction hypothesis: ltF_irrefl kills the hypothesis ltF (f'+1) M M = true. Scratch file /tmp/claude-1000/-home-koteitan-proofs-bms-rathjen/4fa63956-9
/-- CASE A-6 (M vs M): 2.3 is irreflexive, so the hypothesis is already absurd. -/
theorem a6 : ∀ (n f' : Nat), AsymCase M M n f' := by
  intro n f' _ _ _ _ _ _ h
  rw [ltF_irrefl] at h
  exact Bool.noConfusion h

-- ===== [A6-A10] C6 : c6 — CompCase M M (M vs M, trivially excluded) =====
-- verdict: kimina OK; id c6.lean and again inside all.lean
-- notes: Vacuous by the CompCase schema's own A ≠ B parameter (§8.4 says that hypothesis is discharged by the caller, exactly as in §7.3). Scratch file .../scratchpad/c6.lean.
/-- CASE C-6 (M vs M): excluded by the caller's `A ≠ B`. -/
theorem c6 : ∀ (n f' : Nat), CompCase M M n f' := by
  intro n f' _ _ _ _ _ _ hne
  exact absurd rfl hne

-- ===== [A6-A10] A7 : a7 — AsymCase (omg x) (omg y)  [2.3.12] =====
-- verdict: kimina OK; id a7.lean and again inside all.lean
-- notes: Transcription of §8.2.1's ω̄/ω̄ block with Frag2 ↦ FragR (frag2_omg ↦ fragR_omg). Uses ltF_succ_omg_omg (the one Stage-3a rule that is not rfl) and IH_ASYM at x,y; the degree drop is 2, supplied by the two rfl equations eA/eB plus deg_pos. IH_COMP unused. Reachability receipt (verified as a #guard):
/-- CASE A-7 (ω̄ vs ω̄): 2.3.12, one step of `IH_ASYM`. -/
theorem a7 : ∀ (x y : Term) (n f' : Nat), AsymCase (omg x) (omg y) n f' := by
  intro x y n f' hfa hfb hd hnf IHa _ h
  have hab : omg x ≠ omg y := ne_of_ltF h
  have dx := deg_pos x; have dy := deg_pos y
  have eA : (omg x).deg = 1 + x.deg := rfl
  have eB : (omg y).deg = 1 + y.deg := rfl
  rw [ltF_succ_omg_omg _ hab] at h
  rw [ltF_succ_omg_omg _ (Ne.symm hab)]
  exact IHa x y (fragR_omg hfa) (fragR_omg hfb) (by omega) f' hnf h

-- ===== [A6-A10] C7 : c7 — CompCase (omg x) (omg y)  [2.3.12] =====
-- verdict: kimina OK; id c7.lean and again inside all.lean
-- notes: §8.2.1's comparability ω̄/ω̄ block with Frag2 ↦ FragR and the three-way Or of IH_COMP collapsed onto CompCase's two-way Or (the middle branch is killed by hxy, derived from the schema's A ≠ B). IH_ASYM unused. Scratch file .../scratchpad/c7.lean.
/-- CASE C-7 (ω̄ vs ω̄): 2.3.12, one step of `IH_COMP`. -/
theorem c7 : ∀ (x y : Term) (n f' : Nat), CompCase (omg x) (omg y) n f' := by
  intro x y n f' hfa hfb hd hnf _ IHc hab
  have dx := deg_pos x; have dy := deg_pos y
  have eA : (omg x).deg = 1 + x.deg := rfl
  have eB : (omg y).deg = 1 + y.deg := rfl
  rw [ltF_succ_omg_omg _ hab, ltF_succ_omg_omg _ (Ne.symm hab)]
  have hxy : x ≠ y := fun hc => hab (by rw [hc])
  rcases IHc x y (fragR_omg hfa) (fragR_omg hfb) (by omega) f' hnf with h1 | h1 | h1
  · exact Or.inl h1
  · exact absurd h1 hxy
  · exact Or.inr h1

-- ===== [A6-A10] A8 : a8 — AsymCase (phi p q) (phi r s)  [2.3.13] =====
-- verdict: kimina OK; id a8.lean and again inside all.lean
-- notes: Line-for-line transcription of §8.2.1's φ̄/φ̄ asymmetry block (WF.lean:3865-3897), which is itself §7.3's; the only changes are Frag2 ↦ FragR (frag2_phi ↦ fragR_phi) and the schema's parameter names. Both IH_ASYM and IH_COMP are consumed (IH_COMP only in the 13(iii) branch, exactly as §7 explains). 
/-- CASE A-8 (φ̄ vs φ̄): 2.3.13's three sub-clauses, §8.2.1's block verbatim with
    `Frag2 ↦ FragR`.  13(iii) is where `IH_COMP` is consumed. -/
theorem a8 : ∀ (p q r s : Term) (n f' : Nat), AsymCase (phi p q) (phi r s) n f' := by
  intro p q r s n f' hfa hfb hd hnf IHa IHc h
  have hab : phi p q ≠ phi r s := ne_of_ltF h
  obtain ⟨hfp, hfq⟩ := fragR_phi hfa
  obtain ⟨hfr, hfs⟩ := fragR_phi hfb
  have dp := deg_pos p; have dq := deg_pos q
  have dr := deg_pos r; have ds := deg_pos s
  rw [ltF_succ_phi_phi _ hab] at h
  rw [ltF_succ_phi_phi _ (Ne.symm hab)]
  simp only [Term.deg] at hd
  by_cases hpr : p = r
  · subst hpr
    rw [if_pos rfl] at h
    rw [if_pos rfl]
    exact IHa q s hfq hfs (by omega) f' hnf h
  · rw [if_neg hpr] at h
    rw [if_neg (Ne.symm hpr)]
    by_cases hlt : ltF f' p r = true
    · -- 13(i) forward: the reverse comparison lands in 13(iii)
      rw [if_pos hlt] at h
      have hrp : ltF f' r p = false := IHa p r hfp hfr (by omega) f' hnf hlt
      rw [if_neg (by simp [hrp])]
      have hne : phi r s ≠ q := by
        intro hc; rw [hc, ltF_irrefl] at h; exact Bool.noConfusion h
      have h2 : ltF f' (phi r s) q = false :=
        IHa q (phi r s) hfq hfb (by simp only [Term.deg]; omega) f' hnf h
      simp [hne, h2]
    · -- 13(iii) forward: "neither `=` nor `<`" must be turned into `>` — comparability
      rw [if_neg hlt] at h
      have hrp : ltF f' r p = true := by
        rcases IHc p r hfp hfr (by omega) f' hnf with h1 | h1 | h1
        · exact absurd h1 hlt
        · exact absurd h1 hpr
        · exact h1
      rw [if_pos hrp]
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h1 | h1
      · rw [← h1]; exact ltF_irrefl _ _
      · exact IHa (phi p q) s hfa hfs (by simp only [Term.deg]; omega) f' hnf h1

-- ===== [A6-A10] C8 : c8 — CompCase (phi p q) (phi r s)  [2.3.13] =====
-- verdict: kimina OK; id c8.lean and again inside all.lean
-- notes: Transcription of §8.2.1's φ̄/φ̄ comparability block (WF.lean:3963-3992) with Frag2 ↦ FragR and IH_COMP's three-way Or mapped onto CompCase's two-way Or (Or.inr (Or.inr X) ↦ Or.inr X). Scratch file .../scratchpad/c8.lean.
/-- CASE C-8 (φ̄ vs φ̄): 2.3.13, §8.2.1's comparability block verbatim with
    `Frag2 ↦ FragR`.  `IH_ASYM` is consumed to know the reverse comparison does
    not also land in 13(i). -/
theorem c8 : ∀ (p q r s : Term) (n f' : Nat), CompCase (phi p q) (phi r s) n f' := by
  intro p q r s n f' hfa hfb hd hnf IHa IHc hab
  obtain ⟨hfp, hfq⟩ := fragR_phi hfa
  obtain ⟨hfr, hfs⟩ := fragR_phi hfb
  have dp := deg_pos p; have dq := deg_pos q
  have dr := deg_pos r; have ds := deg_pos s
  rw [ltF_succ_phi_phi _ hab, ltF_succ_phi_phi _ (Ne.symm hab)]
  simp only [Term.deg] at hd
  by_cases hpr : p = r
  · subst hpr
    rw [if_pos rfl, if_pos rfl]
    have hqs : q ≠ s := fun hc => hab (by rw [hc])
    rcases IHc q s hfq hfs (by omega) f' hnf with h1 | h1 | h1
    · exact Or.inl h1
    · exact absurd h1 hqs
    · exact Or.inr h1
  · rw [if_neg hpr, if_neg (Ne.symm hpr)]
    rcases IHc p r hfp hfr (by omega) f' hnf with h1 | h1 | h1
    · have hrp : ltF f' r p = false := IHa p r hfp hfr (by omega) f' hnf h1
      rw [if_pos h1, if_neg (by simp [hrp])]
      rcases IHc q (phi r s) hfq hfb (by simp only [Term.deg]; omega) f' hnf
        with h2 | h2 | h2
      · exact Or.inl h2
      · exact Or.inr (by simp [h2])
      · exact Or.inr (by simp [h2])
    · exact absurd h1 hpr
    · have hpr2 : ltF f' p r = false := IHa r p hfr hfp (by omega) f' hnf h1
      rw [if_neg (by simp [hpr2]), if_pos h1]
      rcases IHc (phi p q) s hfa hfs (by simp only [Term.deg]; omega) f' hnf
        with h2 | h2 | h2
      · exact Or.inl (by simp [h2])
      · exact Or.inl (by simp [h2])
      · exact Or.inr h2

-- ===== [A6-A10] A9a : a9_phi_psi — AsymCase (phi a b) (psi k c)  [2.3.5 forward, 2.3.4 backward] =====
-- verdict: kimina OK; id a9f.lean and again inside all.lean
-- notes: Uses ltF_succ_phi_psi (2.3.5) and ltF_succ_psi_phi (2.3.4) as the design named. NO K_kappa and no isR conjunct is touched — FragR is passed along unused except through fragR_phi, consistent with §8.4(iii) ('everywhere else FragR is passed along unused'). Degree bookkeeping: from (1+a+b)+(1+k+c) ≤ n+
/-- CASE A-9 (φ̄ vs ψ), forward direction.  2.3.5 says `φ̄αβ < ψκγ` iff BOTH
    components are below `ψκγ`; 2.3.4 says `ψκγ < φ̄αβ` iff it is `≤` one of them.
    Both components being strictly below kills all four disjuncts of 2.3.4 —
    two by irreflexivity, two by `IH_ASYM`. -/
theorem a9_phi_psi : ∀ (a b k c : Term) (n f' : Nat), AsymCase (phi a b) (psi k c) n f' := by
  intro a b k c n f' hfa hfb hd hnf IHa _ h
  obtain ⟨hfa1, hfa2⟩ := fragR_phi hfa
  have da := deg_pos a; have db := deg_pos b
  have dk := deg_pos k; have dc := deg_pos c
  rw [ltF_succ_phi_psi] at h
  rw [ltF_succ_psi_phi]
  simp only [Term.deg] at hd
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : ltF f' (psi k c) a = false :=
    IHa a (psi k c) hfa1 hfb (by simp only [Term.deg]; omega) f' hnf h1
  have e2 : ltF f' (psi k c) b = false :=
    IHa b (psi k c) hfa2 hfb (by simp only [Term.deg]; omega) f' hnf h2
  have n1 : psi k c ≠ a := Ne.symm (ne_of_ltF h1)
  have n2 : psi k c ≠ b := Ne.symm (ne_of_ltF h2)
  simp [n1, n2, e1, e2]

-- ===== [A6-A10] A9b : a9_psi_phi — AsymCase (psi k c) (phi a b)  [the other direction of the same pair] =====
-- verdict: kimina OK; id a9r.lean and again inside all.lean
-- notes: Supplied because AsymCase is a DIRECTED schema (ltF A B = true → ltF B A = false), so a caller that splits both a and b by shape gets the ordered pair (ψ, φ̄) as a separate obligation. Logically it is interderivable with a9_phi_psi (both say ¬(A<B ∧ B<A)), so Phase B may drop one and derive it, but 
/-- CASE A-9 (φ̄ vs ψ), reverse direction.  Each of 2.3.4's four disjuncts kills
    one conjunct of 2.3.5 — the two `=` disjuncts by irreflexivity, the two `<`
    disjuncts by `IH_ASYM`. -/
theorem a9_psi_phi : ∀ (k c a b : Term) (n f' : Nat), AsymCase (psi k c) (phi a b) n f' := by
  intro k c a b n f' hfa hfb hd hnf IHa _ h
  obtain ⟨hfb1, hfb2⟩ := fragR_phi hfb
  have da := deg_pos a; have db := deg_pos b
  have dk := deg_pos k; have dc := deg_pos c
  rw [ltF_succ_psi_phi] at h
  rw [ltF_succ_phi_psi]
  simp only [Term.deg] at hd
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h1 | h1) | h1) | h1
  · rw [← h1]; simp [ltF_irrefl]
  · rw [← h1]; simp [ltF_irrefl]
  · have e : ltF f' a (psi k c) = false :=
      IHa (psi k c) a hfa hfb1 (by simp only [Term.deg]; omega) f' hnf h1
    simp [e]
  · have e : ltF f' b (psi k c) = false :=
      IHa (psi k c) b hfa hfb2 (by simp only [Term.deg]; omega) f' hnf h1
    simp [e]

-- ===== [A6-A10] C9 : c9 — CompCase (phi a b) (psi k c)  [2.3.5 / 2.3.4] =====
-- verdict: kimina OK; id c9.lean and again inside all.lean
-- notes: Consumes only IH_COMP (IH_ASYM and the A ≠ B parameter are both unused, hence the two `_` binders — a φ̄ is never a ψ so distinctness is automatic). This is the whole content of §8.4(iii)'s claim that isR is essential ONLY at ψ-vs-ψ: the mixed level-1 pair needs nothing but comparability of a compon
/-- CASE C-9 (φ̄ vs ψ).  Compare each component of the `φ̄` with the `ψ`: if both
    are strictly below, 2.3.5 fires; the first one that is not gives 2.3.4.
    (`A ≠ B` is not needed — a `φ̄` is never a `ψ`.) -/
theorem c9 : ∀ (a b k c : Term) (n f' : Nat), CompCase (phi a b) (psi k c) n f' := by
  intro a b k c n f' hfa hfb hd hnf _ IHc _
  obtain ⟨hfa1, hfa2⟩ := fragR_phi hfa
  have da := deg_pos a; have db := deg_pos b
  have dk := deg_pos k; have dc := deg_pos c
  rw [ltF_succ_phi_psi, ltF_succ_psi_phi]
  simp only [Term.deg] at hd
  rcases IHc a (psi k c) hfa1 hfb (by simp only [Term.deg]; omega) f' hnf with h1 | h1 | h1
  · rcases IHc b (psi k c) hfa2 hfb (by simp only [Term.deg]; omega) f' hnf with h2 | h2 | h2
    · exact Or.inl (by simp [h1, h2])
    · exact Or.inr (by simp [h2])
    · exact Or.inr (by simp [h2])
  · exact Or.inr (by simp [h1])
  · exact Or.inr (by simp [h1])

-- ===== [A6-A10] A10a : a10_phi_Z — AsymCase (phi a b) (Z e)  [2.3.5 forward, 2.3.4 backward] =====
-- verdict: kimina OK; id a10f.lean and again inside all.lean
-- notes: a9_phi_psi with ltF_succ_phi_psi/ltF_succ_psi_phi replaced by ltF_succ_phi_Z/ltF_succ_Z_phi; no starF is reached (2.3.5/2.3.4 do not route through it), so nothing here touches the starF layer or needs StarClosed. Reachability receipt: FragR (phi zero zero) && FragR (Z zero) && lt (phi zero zero) (Z 
/-- CASE A-10 (φ̄ vs Z), forward direction.  Same clause pair as A-9 (2.3.5 /
    2.3.4) — `Z` is the other `SC` shape and 2.3 treats the two alike. -/
theorem a10_phi_Z : ∀ (a b e : Term) (n f' : Nat), AsymCase (phi a b) (Z e) n f' := by
  intro a b e n f' hfa hfb hd hnf IHa _ h
  obtain ⟨hfa1, hfa2⟩ := fragR_phi hfa
  have da := deg_pos a; have db := deg_pos b
  have de := deg_pos e
  rw [ltF_succ_phi_Z] at h
  rw [ltF_succ_Z_phi]
  simp only [Term.deg] at hd
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : ltF f' (Z e) a = false :=
    IHa a (Z e) hfa1 hfb (by simp only [Term.deg]; omega) f' hnf h1
  have e2 : ltF f' (Z e) b = false :=
    IHa b (Z e) hfa2 hfb (by simp only [Term.deg]; omega) f' hnf h2
  have n1 : Z e ≠ a := Ne.symm (ne_of_ltF h1)
  have n2 : Z e ≠ b := Ne.symm (ne_of_ltF h2)
  simp [n1, n2, e1, e2]

-- ===== [A6-A10] A10b : a10_Z_phi — AsymCase (Z e) (phi a b)  [the other direction of the same pair] =====
-- verdict: kimina OK; id a10r.lean and again inside all.lean
-- notes: Same remark as A9b: AsymCase is directed, so the ordered pair (Z, φ̄) is a separate obligation for a caller that splits both sides by shape. Reachability receipt: FragR (phi (Z zero) zero) && lt (Z zero) (phi (Z zero) zero). Scratch file .../scratchpad/a10r.lean.
/-- CASE A-10 (φ̄ vs Z), reverse direction. -/
theorem a10_Z_phi : ∀ (e a b : Term) (n f' : Nat), AsymCase (Z e) (phi a b) n f' := by
  intro e a b n f' hfa hfb hd hnf IHa _ h
  obtain ⟨hfb1, hfb2⟩ := fragR_phi hfb
  have da := deg_pos a; have db := deg_pos b
  have de := deg_pos e
  rw [ltF_succ_Z_phi] at h
  rw [ltF_succ_phi_Z]
  simp only [Term.deg] at hd
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h1 | h1) | h1) | h1
  · rw [← h1]; simp [ltF_irrefl]
  · rw [← h1]; simp [ltF_irrefl]
  · have hx : ltF f' a (Z e) = false :=
      IHa (Z e) a hfa hfb1 (by simp only [Term.deg]; omega) f' hnf h1
    simp [hx]
  · have hx : ltF f' b (Z e) = false :=
      IHa (Z e) b hfa hfb2 (by simp only [Term.deg]; omega) f' hnf h1
    simp [hx]

-- ===== [A6-A10] C10 : c10 — CompCase (phi a b) (Z e)  [2.3.5 / 2.3.4] =====
-- verdict: kimina OK; id c10.lean and again inside all.lean
-- notes: c9 with the Z rules. Consumes only IH_COMP; IH_ASYM and A ≠ B unused. Scratch file .../scratchpad/c10.lean.
/-- CASE C-10 (φ̄ vs Z). -/
theorem c10 : ∀ (a b e : Term) (n f' : Nat), CompCase (phi a b) (Z e) n f' := by
  intro a b e n f' hfa hfb hd hnf _ IHc _
  obtain ⟨hfa1, hfa2⟩ := fragR_phi hfa
  have da := deg_pos a; have db := deg_pos b
  have de := deg_pos e
  rw [ltF_succ_phi_Z, ltF_succ_Z_phi]
  simp only [Term.deg] at hd
  rcases IHc a (Z e) hfa1 hfb (by simp only [Term.deg]; omega) f' hnf with h1 | h1 | h1
  · rcases IHc b (Z e) hfa2 hfb (by simp only [Term.deg]; omega) f' hnf with h2 | h2 | h2
    · exact Or.inl (by simp [h1, h2])
    · exact Or.inr (by simp [h2])
    · exact Or.inr (by simp [h2])
  · exact Or.inr (by simp [h1])
  · exact Or.inr (by simp [h1])

-- ===== [A11-hard] A11 : a11 =====
-- verdict: kimina http://localhost:12346/api/check — snippet id "a11": {"env":6}, messages [] (no output at all). Re-verified in a combined snippet with C11: `#print axioms a11` reports [propext, Quot.sound] — n
-- notes: ASYMMETRY, ψ vs ψ, 2.3.14. Structure is §7.3's φ̄/φ̄ asymmetry block with `ltF_succ_phi_phi` replaced by `ltF_succ_psi_psi`, but the three sub-clauses of 2.3.14 recurse differently from 2.3.13 — 14(i) is `κ < ψπβ` (head vs WHOLE right) and 14(iii) is `ψκα < π` (whole left vs HEAD), with no `==` disj


theorem a11 : ∀ (k a p b : Term) (n f' : Nat), AsymCase (psi k a) (psi p b) n f' := by
  intro k a p b n f' hfa hfb hd hnf IHa IHc h
  have hab : psi k a ≠ psi p b := ne_of_ltF h
  obtain ⟨hkR, hfk, hfa'⟩ := fragR_psi hfa
  obtain ⟨hpR, hfp, hfb'⟩ := fragR_psi hfb
  have dk := deg_pos k; have da := deg_pos a
  have dp := deg_pos p; have db := deg_pos b
  simp only [Term.deg] at hd
  rw [ltF_succ_psi_psi _ hab] at h
  rw [ltF_succ_psi_psi _ (Ne.symm hab)]
  by_cases hkp : k = p
  · subst hkp
    rw [if_pos rfl] at h
    rw [if_pos rfl]
    exact IHa a b hfa' hfb' (by omega) f' hnf h
  · rw [if_neg hkp] at h
    rw [if_neg (Ne.symm hkp)]
    by_cases hlt : ltF f' k p = true
    · rw [if_pos hlt] at h
      have hpk : ltF f' p k = false := IHa k p hfk hfp (by omega) f' hnf hlt
      rw [if_neg (by simp [hpk])]
      exact IHa k (psi p b) hfk hfb (by simp only [Term.deg]; omega) f' hnf h
    · rw [if_neg hlt] at h
      have hpk : ltF f' p k = true := by
        rcases IHc k p hfk hfp (by omega) f' hnf with h1 | h1 | h1
        · exact absurd h1 hlt
        · exact absurd h1 hkp
        · exact h1
      rw [if_pos hpk]
      exact IHa (psi k a) p hfa hfp (by simp only [Term.deg]; omega) f' hnf h

-- ===== [A11-hard] C11 : c11 =====
-- verdict: kimina http://localhost:12346/api/check — snippet id "c11": {"env":9}, messages [] (no output at all). Re-verified in a combined snippet with A11: `#print axioms c11` reports [propext, Quot.sound] — n
-- notes: COMPARABILITY, ψ vs ψ, 2.3.14 — the C-ψψ of §8.4.2's third `#check`, and THE place κ ∈ R is consumed. It is consumed TWICE, once per head, and in a sharper way than §8.4(iii) describes.  §8.4(iii) says the role of κ ∈ R is to make the two heads comparable. That is NOT what the proof needs: head comp


theorem c11 : ∀ (k a p b : Term) (n f' : Nat), CompCase (psi k a) (psi p b) n f' := by
  intro k a p b n f' hfa hfb hd hnf IHa IHc hab
  obtain ⟨hkR, hfk, hfa'⟩ := fragR_psi hfa
  obtain ⟨hpR, hfp, hfb'⟩ := fragR_psi hfb
  have dk := deg_pos k; have da := deg_pos a
  have dp := deg_pos p; have db := deg_pos b
  simp only [Term.deg] at hd
  rw [ltF_succ_psi_psi _ hab, ltF_succ_psi_psi _ (Ne.symm hab)]
  by_cases hkp : k = p
  · subst hkp
    rw [if_pos rfl, if_pos rfl]
    have hne : a ≠ b := fun hc => hab (by rw [hc])
    rcases IHc a b hfa' hfb' (by omega) f' hnf with h1 | h1 | h1
    · exact Or.inl h1
    · exact absurd h1 hne
    · exact Or.inr h1
  · rw [if_neg hkp, if_neg (Ne.symm hkp)]
    rcases IHc k p hfk hfp (by omega) f' hnf with h1 | h1 | h1
    · have hpk : ltF f' p k = false := IHa k p hfk hfp (by omega) f' hnf h1
      rw [if_pos h1, if_neg (by simp [hpk])]
      have hne : k ≠ psi p b := by
        intro hc; rw [hc] at hkR; exact Bool.noConfusion hkR
      rcases IHc k (psi p b) hfk hfb (by simp only [Term.deg]; omega) f' hnf with h2 | h2 | h2
      · exact Or.inl h2
      · exact absurd h2 hne
      · exact Or.inr h2
    · exact absurd h1 hkp
    · have hkp2 : ltF f' k p = false := IHa p k hfp hfk (by omega) f' hnf h1
      rw [if_neg (by simp [hkp2]), if_pos h1]
      have hne : p ≠ psi k a := by
        intro hc; rw [hc] at hpR; exact Bool.noConfusion hpR
      rcases IHc (psi k a) p hfa hfp (by simp only [Term.deg]; omega) f' hnf with h2 | h2 | h2
      · exact Or.inl h2
      · exact absurd h2 (Ne.symm hne)
      · exact Or.inr h2

-- ===== [A12-hard] A12 : a12 — AsymCase (psi k a) (Z d) n f' =====
-- verdict: kimina http://localhost:12346/api/check — messages: [] (0 errors); #print axioms a12 → [propext, Quot.sound], no sorryAx
-- notes: The assigned forward/backward case. Structure exactly as specified: `by_cases` on the 2.3.8 test `(k == Z d) || ltF f' k (Z d)`. If it fires, `ltF_succ_Z_psi` reduces the goal to `false = false` and no IH is used at all (this is the `k ≤ Zd` immediate branch). Otherwise `ltF_succ_psi_Z` gives `(ψκα 
/-- CASE A12 — ASYMMETRY, `ψκα` against `Zδ`.
    Forward is 2.3.8 (`κ ≤ Zδ`) or 2.3.6 (`ψκα ≤ δ*`); backward is 2.3.8 or 2.3.9.
    Depends on S1 (`StarClosed`), taken as a hypothesis. -/
theorem a12 : ∀ (k a d : Term) (n f' : Nat), StarClosed →
    AsymCase (psi k a) (Z d) n f' := by
  intro k a d n f' hSC hFA hFB hd hnf IHa _IHc h
  have hFd : FragR d = true := fragR_Z hFB
  have hFs : FragR (starF f' d) = true := hSC f' d hFd
  have hds : (starF f' d).deg ≤ d.deg := deg_starF f' d
  have hbound : (psi k a).deg + (starF f' d).deg ≤ n := by
    simp only [Term.deg] at hd ⊢; omega
  by_cases hc : ((k == Z d) || ltF f' k (Z d)) = true
  · -- 2.3.8: `κ ≤ Zδ` makes the backward comparison `false` outright.
    rw [ltF_succ_Z_psi, if_pos hc]
  · rw [ltF_succ_psi_Z, if_neg hc] at h
    rw [ltF_succ_Z_psi, if_neg hc]
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h1 | h1
    · rw [← h1]; exact ltF_irrefl _ _
    · exact IHa (psi k a) (starF f' d) hFA hFs hbound f' hnf h1

-- ===== [A12-hard] A21 : a21 — AsymCase (Z d) (psi k a) n f' (mirror orientation) =====
-- verdict: kimina http://localhost:12346/api/check — messages: [] (0 errors); #print axioms a21 → [propext, Quot.sound], no sorryAx
-- notes: NOT literally in my assignment, but delivered because Stage I's `cases a; cases b` reaches BOTH orientations and AsymCase is not symmetric in its statement — A12 alone does not discharge `Zδ < ψκα ⟹ ¬(ψκα < Zδ)`. Same architecture: if the 2.3.8 test fires the hypothesis `ltF (f'+1) (Z d) (psi k a) =
/-- CASE A21 — ASYMMETRY, the mirror orientation `Zδ` against `ψκα`. -/
theorem a21 : ∀ (d k a : Term) (n f' : Nat), StarClosed →
    AsymCase (Z d) (psi k a) n f' := by
  intro d k a n f' hSC hFA hFB hd hnf IHa _IHc h
  have hFd : FragR d = true := fragR_Z hFA
  have hFs : FragR (starF f' d) = true := hSC f' d hFd
  have hds : (starF f' d).deg ≤ d.deg := deg_starF f' d
  have hbound : (starF f' d).deg + (psi k a).deg ≤ n := by
    simp only [Term.deg] at hd ⊢; omega
  by_cases hc : ((k == Z d) || ltF f' k (Z d)) = true
  · rw [ltF_succ_Z_psi, if_pos hc] at h; exact Bool.noConfusion h
  · rw [ltF_succ_Z_psi, if_neg hc] at h
    rw [ltF_succ_psi_Z, if_neg hc]
    have h2 : ltF f' (psi k a) (starF f' d) = false :=
      IHa (starF f' d) (psi k a) hFs hFB hbound f' hnf h
    have hne : psi k a ≠ starF f' d := by
      intro hcc; rw [← hcc, ltF_irrefl] at h; exact Bool.noConfusion h
    simp [hne, h2]

-- ===== [A12-hard] C12 : c12 — CompCase (psi k a) (Z d) n f' =====
-- verdict: kimina http://localhost:12346/api/check — messages: [] (0 errors); #print axioms c12 → [propext, Quot.sound], no sorryAx
-- notes: The assigned comparability case. The `A ≠ B` argument of CompCase is NOT needed (a ψ is never a Z), so it is bound as `_hne`. If the 2.3.8 test fires, 2.3.6's clause returns `true` unconditionally and the left disjunct is `rfl`. Otherwise one call of IH_COMP at (ψκα, δ*) decides everything: its firs
/-- CASE C12 — COMPARABILITY, `ψκα` against `Zδ`.  Either 2.3.8 fires, or both
    directions are decided by `IH_COMP` at `(ψκα, δ*)`, whose degree sum is strictly
    smaller (`deg_starF`, and the clause has stripped the `Z`). -/
theorem c12 : ∀ (k a d : Term) (n f' : Nat), StarClosed →
    CompCase (psi k a) (Z d) n f' := by
  intro k a d n f' hSC hFA hFB hd hnf _IHa IHc _hne
  have hFd : FragR d = true := fragR_Z hFB
  have hFs : FragR (starF f' d) = true := hSC f' d hFd
  have hds : (starF f' d).deg ≤ d.deg := deg_starF f' d
  have hbound : (psi k a).deg + (starF f' d).deg ≤ n := by
    simp only [Term.deg] at hd ⊢; omega
  by_cases hc : ((k == Z d) || ltF f' k (Z d)) = true
  · exact Or.inl (by rw [ltF_succ_psi_Z, if_pos hc])
  · rcases IHc (psi k a) (starF f' d) hFA hFs hbound f' hnf with h1 | h1 | h1
    · exact Or.inl (by rw [ltF_succ_psi_Z, if_neg hc]; simp [h1])
    · exact Or.inl (by rw [ltF_succ_psi_Z, if_neg hc]; simp [h1])
    · exact Or.inr (by rw [ltF_succ_Z_psi, if_neg hc]; exact h1)

-- ===== [A12-hard] C21 : c21 — CompCase (Z d) (psi k a) n f' (mirror orientation) =====
-- verdict: kimina http://localhost:12346/api/check — messages: [] (0 errors); #print axioms c21 → [propext, Quot.sound], no sorryAx
-- notes: Mirror of C12, delivered for the same reason as A21 (Stage I's double `cases` reaches `Z` on the left with `ψ` on the right). Identical proof with the two disjuncts swapped; note the FragR hypotheses swap roles (`hFA : FragR (Z d)`, `hFB : FragR (psi k a)`), which is why `fragR_Z hFA` and `IHc … hFB
/-- CASE C21 — COMPARABILITY, the mirror orientation `Zδ` against `ψκα`. -/
theorem c21 : ∀ (d k a : Term) (n f' : Nat), StarClosed →
    CompCase (Z d) (psi k a) n f' := by
  intro d k a n f' hSC hFA hFB hd hnf _IHa IHc _hne
  have hFd : FragR d = true := fragR_Z hFA
  have hFs : FragR (starF f' d) = true := hSC f' d hFd
  have hds : (starF f' d).deg ≤ d.deg := deg_starF f' d
  have hbound : (psi k a).deg + (starF f' d).deg ≤ n := by
    simp only [Term.deg] at hd ⊢; omega
  by_cases hc : ((k == Z d) || ltF f' k (Z d)) = true
  · exact Or.inr (by rw [ltF_succ_psi_Z, if_pos hc])
  · rcases IHc (psi k a) (starF f' d) hFB hFs hbound f' hnf with h1 | h1 | h1
    · exact Or.inr (by rw [ltF_succ_psi_Z, if_neg hc]; simp [h1])
    · exact Or.inr (by rw [ltF_succ_psi_Z, if_neg hc]; simp [h1])
    · exact Or.inl (by rw [ltF_succ_Z_psi, if_neg hc]; exact h1)

-- ===== [A13-hard] A13 : a13 — ASYMMETRY, Z vs Z (2.3.15) =====
-- verdict: kimina @ http://localhost:12346/api/check — snippet id a13_alone returned {"env":29} with NO messages (success). Also verified inside the combined snippet 'final' ({"env":5}, no messages).
-- notes: Statement is exactly §8.4's schema with StarClosed (case S1) added as an ordinary hypothesis, as assigned. Proof sketch: strip Z with ltF_succ_Z_Z (distinctness from ne_of_ltF). Forward in 15(i) (ltF f' x y = true): IH_ASYM on (x,y) kills the reverse branch condition, so the reverse is 15(ii), and i

/-- CASE A13 (§8.4, STAGE I): ASYMMETRY, `Z` against `Z` — clause 2.3.15. -/
theorem a13 : ∀ (x y : Term) (n f' : Nat), StarClosed → AsymCase (Z x) (Z y) n f' := by
  intro x y n f' S1 hfa hfb hd hnf IHa IHc h
  have hab : Z x ≠ Z y := ne_of_ltF h
  have hxy : x ≠ y := fun hc => hab (by rw [hc])
  have hdx : (Z x).deg = 1 + x.deg := rfl
  have hdy : (Z y).deg = 1 + y.deg := rfl
  have hfx : FragR x = true := fragR_Z hfa
  have hfy : FragR y = true := fragR_Z hfb
  have hsx : FragR (starF f' x) = true := S1 f' x hfx
  have hsy : FragR (starF f' y) = true := S1 f' y hfy
  have dsx := deg_starF f' x
  have dsy := deg_starF f' y
  rw [ltF_succ_Z_Z _ hab] at h
  rw [ltF_succ_Z_Z _ (Ne.symm hab)]
  by_cases hlt : ltF f' x y = true
  · -- 15(i) forward: α < β, so the reverse comparison lands in 15(ii)
    rw [if_pos hlt] at h
    have hyx : ltF f' y x = false := IHa x y hfx hfy (by omega) f' hnf hlt
    rw [if_neg (by simp [hyx])]
    have hne : Z y ≠ starF f' x := Ne.symm (ne_of_ltF h)
    have h2 : ltF f' (Z y) (starF f' x) = false :=
      IHa (starF f' x) (Z y) hsx hfb (by omega) f' hnf h
    simp [hne, h2]
  · -- 15(ii) forward: comparability turns "not α < β" into "β < α", so the
    -- reverse comparison lands in 15(i)
    rw [if_neg hlt] at h
    have hyx : ltF f' y x = true := by
      rcases IHc x y hfx hfy (by omega) f' hnf with h1 | h1 | h1
      · exact absurd h1 hlt
      · exact absurd h1 hxy
      · exact h1
    rw [if_pos hyx]
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h1 | h1
    · rw [← h1]; exact ltF_irrefl _ _
    · exact IHa (Z x) (starF f' y) hfa hsy (by omega) f' hnf h1

-- ===== [A13-hard] C13 : c13 — COMPARABILITY, Z vs Z (2.3.15) =====
-- verdict: kimina @ http://localhost:12346/api/check — snippet id c13_alone returned {"env":6} with NO messages (success). Also verified inside the combined snippet 'final' ({"env":5}, no messages).
-- notes: Statement is exactly §8.4's CompCase schema with StarClosed added as an ordinary hypothesis. Proof: Z x ≠ Z y gives x ≠ y, so IH_COMP on (x,y) splits into ltF f' x y or ltF f' y x (the middle disjunct is absurd). In the first branch IH_ASYM pins the reverse to 15(ii), and IH_COMP applied at (α*, Zβ)

/-- CASE C13 (§8.4, STAGE I): COMPARABILITY, `Z` against `Z` — clause 2.3.15. -/
theorem c13 : ∀ (x y : Term) (n f' : Nat), StarClosed → CompCase (Z x) (Z y) n f' := by
  intro x y n f' S1 hfa hfb hd hnf IHa IHc hab
  have hxy : x ≠ y := fun hc => hab (by rw [hc])
  have hdx : (Z x).deg = 1 + x.deg := rfl
  have hdy : (Z y).deg = 1 + y.deg := rfl
  have hfx : FragR x = true := fragR_Z hfa
  have hfy : FragR y = true := fragR_Z hfb
  have hsx : FragR (starF f' x) = true := S1 f' x hfx
  have hsy : FragR (starF f' y) = true := S1 f' y hfy
  have dsx := deg_starF f' x
  have dsy := deg_starF f' y
  rw [ltF_succ_Z_Z _ hab, ltF_succ_Z_Z _ (Ne.symm hab)]
  rcases IHc x y hfx hfy (by omega) f' hnf with h1 | h1 | h1
  · -- α < β: forward is 15(i), reverse is 15(ii); `α*` vs `Zβ` decides both
    have hyx : ltF f' y x = false := IHa x y hfx hfy (by omega) f' hnf h1
    rw [if_pos h1, if_neg (by simp [hyx])]
    rcases IHc (starF f' x) (Z y) hsx hfb (by omega) f' hnf with h2 | h2 | h2
    · exact Or.inl h2
    · exact Or.inr (by simp [h2])
    · exact Or.inr (by simp [h2])
  · exact absurd h1 hxy
  · -- β < α: the mirror image
    have hxy2 : ltF f' x y = false := IHa y x hfy hfx (by omega) f' hnf h1
    rw [if_pos h1, if_neg (by simp [hxy2])]
    rcases IHc (starF f' y) (Z x) hsy hfa (by omega) f' hnf with h2 | h2 | h2
    · exact Or.inr h2
    · exact Or.inl (by simp [h2])
    · exact Or.inl (by simp [h2])

-- ===== [T1-T10] T1 : t1 =====
-- verdict: kimina OK (messages [] — no error/warning), 0.19s standalone, 0.73s in the combined 10-theorem snippet
-- notes: Sum/Sum/Sum, i.e. §8.2 trans_aux2 case (1) (2.3.16 three times along the spine). Verbatim transcription of §8.2 with Frag2 destructors replaced by fragR_add and with the two uses of ltF_asymm2 replaced by the Asym3 PARAMETER (ASYM). NOTE the one non-cosmetic difference from §8.2: Asym3 takes its fue
theorem t1 : ∀ (p q r s t u : Term) (n m f' : Nat),
    TransCase (add p q) (add r s) (add t u) n m f' := by
  intro p q r s t u n m f' hfa hfb hfc hb hm hf ASYM COMP TR1 TR2 h1 h2
  have hfp := (fragR_add hfa).1; have hfq := (fragR_add hfa).2
  have hfr := (fragR_add hfb).1; have hfs := (fragR_add hfb).2
  have hft := (fragR_add hfc).1; have hfu := (fragR_add hfc).2
  have dp := deg_pos p; have dq := deg_pos q
  have dr := deg_pos r; have ds := deg_pos s
  have dt := deg_pos t; have du := deg_pos u
  have eA : (add p q).deg = 1 + p.deg + q.deg := rfl
  have eB : (add r s).deg = 1 + r.deg + s.deg := rfl
  have eC : (add t u).deg = 1 + t.deg + u.deg := rfl
  have hac : add p q ≠ add t u := by
    intro hcc
    rw [← hcc] at h2
    rw [ASYM _ _ hfa hfb (f' + 1) (by omega) h1] at h2
    exact Bool.noConfusion h2
  have hab1 : add p q ≠ add r s := ne_of_ltF h1
  have hab2 : add r s ≠ add t u := ne_of_ltF h2
  rw [ltF_succ_add_add _ hab1] at h1
  rw [ltF_succ_add_add _ hab2] at h2
  rw [ltF_succ_add_add _ hac]
  by_cases hpr : p = r
  · subst hpr
    rw [if_pos rfl] at h1
    by_cases hrt : p = t
    · subst hrt
      rw [if_pos rfl] at h2
      rw [if_pos rfl]
      exact TR1 q s u hfq hfs hfu (by omega) f' (by omega) h1 h2
    · rw [if_neg hrt] at h2
      rw [if_neg hrt]
      exact h2
  · rw [if_neg hpr] at h1
    by_cases hrt : r = t
    · subst hrt
      rw [if_pos rfl] at h2
      rw [if_neg hpr]
      exact h1
    · rw [if_neg hrt] at h2
      have hpt : p ≠ t := by
        intro hcc; subst hcc
        rw [ASYM _ _ hfp hfr f' (by omega) h1] at h2; exact Bool.noConfusion h2
      rw [if_neg hpt]
      exact TR1 p r t hfp hfr hft (by omega) f' (by omega) h1 h2

-- ===== [T1-T10] T2 : t2 =====
-- verdict: kimina OK (messages []), 0.07s
-- notes: Sum/Sum/non-sum, §8.2 case (2). The opaque non-sum C forces two EXTRA HYPOTHESES ahead of the schema — `c ≠ zero` and `NSum c = true` — exactly the pair that §8.2's frag2_sum_cases delivers in its third branch (⟨hc0, hnc⟩); the Stage-3b assembler will get them from the FragR analogue of frag2_sum_ca
theorem t2 : ∀ (p q r s c : Term) (n m f' : Nat),
    c ≠ zero → NSum c = true → TransCase (add p q) (add r s) c n m f' := by
  intro p q r s c n m f' hc0 hnc hfa hfb hfc hb hm hf ASYM COMP TR1 TR2 h1 h2
  have hfp := (fragR_add hfa).1; have hfq := (fragR_add hfa).2
  have hfr := (fragR_add hfb).1; have hfs := (fragR_add hfb).2
  have dp := deg_pos p; have dq := deg_pos q
  have dr := deg_pos r; have ds := deg_pos s; have dc := deg_pos c
  have eA : (add p q).deg = 1 + p.deg + q.deg := rfl
  have eB : (add r s).deg = 1 + r.deg + s.deg := rfl
  have hab1 : add p q ≠ add r s := ne_of_ltF h1
  rw [ltF_succ_add_add _ hab1] at h1
  rw [ltF_succ_add_nsum _ hc0 hnc] at h2
  rw [ltF_succ_add_nsum _ hc0 hnc]
  by_cases hpr : p = r
  · subst hpr; exact h2
  · rw [if_neg hpr] at h1
    exact TR1 p r c hfp hfr hfc (by omega) f' (by omega) h1 h2

-- ===== [T1-T10] T3 : t3 =====
-- verdict: kimina OK (messages []), 0.11s
-- notes: Sum/non-sum/Sum, §8.2 case (3). Extra hypotheses `b ≠ zero`, `NSum b = true` for the opaque middle non-sum (same provenance as T2). `hac` must be derived BEFORE h1/h2 are rewritten, since the derivation feeds h1 and h2 to Asym3 in their unrewritten form. Note the hypothesis name `hb` (B.deg ≤ n+1) c
theorem t3 : ∀ (p q b t u : Term) (n m f' : Nat),
    b ≠ zero → NSum b = true → TransCase (add p q) b (add t u) n m f' := by
  intro p q b t u n m f' hb0 hnb hfa hfb hfc hb hm hf ASYM COMP TR1 TR2 h1 h2
  have hfp := (fragR_add hfa).1; have hfq := (fragR_add hfa).2
  have hft := (fragR_add hfc).1; have hfu := (fragR_add hfc).2
  have dp := deg_pos p; have dq := deg_pos q
  have db := deg_pos b; have dt := deg_pos t; have du := deg_pos u
  have eA : (add p q).deg = 1 + p.deg + q.deg := rfl
  have eC : (add t u).deg = 1 + t.deg + u.deg := rfl
  have hac : add p q ≠ add t u := by
    intro hcc
    rw [← hcc] at h2
    rw [ASYM _ _ hfa hfb (f' + 1) (by omega) h1] at h2
    exact Bool.noConfusion h2
  rw [ltF_succ_add_nsum _ hb0 hnb] at h1
  rw [ltF_succ_nsum_add _ hb0 hnb] at h2
  rw [ltF_succ_add_add _ hac]
  simp only [Bool.or_eq_true, beq_iff_eq] at h2
  have hpt : ltF f' p t = true := by
    rcases h2 with h3 | h3
    · rw [← h3]; exact h1
    · exact TR2 p t hfp hft (by omega) f' (by omega) h1 h3
  rw [if_neg (ne_of_ltF hpt)]
  exact hpt

-- ===== [T1-T10] T4 : t4 =====
-- verdict: kimina OK (messages []), 0.09s
-- notes: Sum/non-sum/non-sum, §8.2 case (4). §8.2's local `LOW` abbreviation (fuel step-down via ltF_stable) is inlined as the `hBC` have, since a case lemma cannot share §8.2's local haves. This is the only place T1-T7 needs ltF_stable in the downward direction; the degree side conditions are discharged by 
theorem t4 : ∀ (p q b c : Term) (n m f' : Nat),
    b ≠ zero → NSum b = true → c ≠ zero → NSum c = true →
    TransCase (add p q) b c n m f' := by
  intro p q b c n m f' hb0 hnb hc0 hnc hfa hfb hfc hb hm hf ASYM COMP TR1 TR2 h1 h2
  have hfp := (fragR_add hfa).1; have hfq := (fragR_add hfa).2
  have dp := deg_pos p; have dq := deg_pos q
  have db := deg_pos b; have dc := deg_pos c
  have eA : (add p q).deg = 1 + p.deg + q.deg := rfl
  have hBC : ltF f' b c = true := by
    rw [ltF_stable b c f' (f' + 1) (by omega) (by omega)]; exact h2
  rw [ltF_succ_add_nsum _ hb0 hnb] at h1
  rw [ltF_succ_add_nsum _ hc0 hnc]
  exact TR2 p c hfp hfc (by omega) f' (by omega) h1 hBC

-- ===== [T1-T10] T5 : t5 =====
-- verdict: kimina OK (messages []), 0.07s
-- notes: non-sum/Sum/Sum, §8.2 case (5). Extra hypotheses `a ≠ zero`, `NSum a = true`. Verbatim §8.2; neither Asym3 nor Comp3 is consumed. Reachability witness: lt M (add (omg M) M) && lt (add (omg M) M) (add (omg (omg M)) M).
theorem t5 : ∀ (a r s t u : Term) (n m f' : Nat),
    a ≠ zero → NSum a = true → TransCase a (add r s) (add t u) n m f' := by
  intro a r s t u n m f' ha0 hna hfa hfb hfc hb hm hf ASYM COMP TR1 TR2 h1 h2
  have hfr := (fragR_add hfb).1; have hfs := (fragR_add hfb).2
  have hft := (fragR_add hfc).1; have hfu := (fragR_add hfc).2
  have da := deg_pos a
  have dr := deg_pos r; have ds := deg_pos s
  have dt := deg_pos t; have du := deg_pos u
  have eB : (add r s).deg = 1 + r.deg + s.deg := rfl
  have eC : (add t u).deg = 1 + t.deg + u.deg := rfl
  have hab2 : add r s ≠ add t u := ne_of_ltF h2
  rw [ltF_succ_nsum_add _ ha0 hna] at h1
  rw [ltF_succ_add_add _ hab2] at h2
  rw [ltF_succ_nsum_add _ ha0 hna]
  by_cases hrt : r = t
  · subst hrt; exact h1
  · rw [if_neg hrt] at h2
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with h3 | h3
    · rw [h3]; simp [h2]
    · have h4 : ltF f' a t = true :=
        TR1 a r t hfa hfr hft (by omega) f' (by omega) h3 h2
      simp [h4]

-- ===== [T1-T10] T6 : t6 =====
-- verdict: kimina OK (messages []), 0.08s
-- notes: non-sum/Sum/non-sum, §8.2 case (6). §8.2's local `UP` (fuel step-up) is inlined as the closing `rw [ltF_stable a c (f' + 1) f' …]` on the GOAL rather than as a separate have — same content, one line shorter. Both A and C are opaque non-sums, so this one statement covers all 25 ψ/Z-inclusive (A,C) sh
theorem t6 : ∀ (a r s c : Term) (n m f' : Nat),
    a ≠ zero → NSum a = true → c ≠ zero → NSum c = true →
    TransCase a (add r s) c n m f' := by
  intro a r s c n m f' ha0 hna hc0 hnc hfa hfb hfc hb hm hf ASYM COMP TR1 TR2 h1 h2
  have hfr := (fragR_add hfb).1; have hfs := (fragR_add hfb).2
  have da := deg_pos a; have dc := deg_pos c
  have dr := deg_pos r; have ds := deg_pos s
  have eB : (add r s).deg = 1 + r.deg + s.deg := rfl
  rw [ltF_succ_nsum_add _ ha0 hna] at h1
  rw [ltF_succ_add_nsum _ hc0 hnc] at h2
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  have h4 : ltF f' a c = true := by
    rcases h1 with h3 | h3
    · rw [h3]; exact h2
    · exact TR1 a r c hfa hfr hfc (by omega) f' (by omega) h3 h2
  rw [ltF_stable a c (f' + 1) f' (by omega) (by omega)]
  exact h4

-- ===== [T1-T10] T7 : t7 =====
-- verdict: kimina OK (messages []), 0.08s
-- notes: non-sum/non-sum/Sum, §8.2 case (7). Four extra hypotheses (A and B both opaque non-sums). §8.2's `LOW` is inlined as `hAB`. This is the last of the seven sum-involving triples; together T1-T7 plus the three zero cases (a = 0 immediate by ltF_left_zero, b = 0 / c = 0 contradictory by ltF_right_zero —
theorem t7 : ∀ (a b t u : Term) (n m f' : Nat),
    a ≠ zero → NSum a = true → b ≠ zero → NSum b = true →
    TransCase a b (add t u) n m f' := by
  intro a b t u n m f' ha0 hna hb0 hnb hfa hfb hfc hbd hm hf ASYM COMP TR1 TR2 h1 h2
  have hft := (fragR_add hfc).1; have hfu := (fragR_add hfc).2
  have da := deg_pos a; have db := deg_pos b
  have dt := deg_pos t; have du := deg_pos u
  have eC : (add t u).deg = 1 + t.deg + u.deg := rfl
  have hAB : ltF f' a b = true := by
    rw [ltF_stable a b f' (f' + 1) (by omega) (by omega)]; exact h1
  rw [ltF_succ_nsum_add _ hb0 hnb] at h2
  rw [ltF_succ_nsum_add _ ha0 hna]
  simp only [Bool.or_eq_true, beq_iff_eq] at h2
  rcases h2 with h3 | h3
  · rw [← h3]; simp [hAB]
  · have h4 : ltF f' a t = true :=
      TR2 a t hfa hft (by omega) f' (by omega) hAB h3
    simp [h4]

-- ===== [T1-T10] T8 : t8 =====
-- verdict: kimina OK (messages []), 0.01s
-- notes: THE LEVEL-RAISING CASE. Takes LvlUp (= case S2) as an ordinary parameter, exactly as TransCase takes Asym3/Comp3, and discharges the goal in one application: neither induction hypothesis, neither Stage-I fact, and neither h1 nor h2 is used. CHECKED NON-VACUOUS: LvlUp is genuinely provable — `example
theorem t8 : ∀ (a b c : Term) (n m f' : Nat),
    LvlUp → NSum a = true → NSum c = true → lvl a < lvl c →
    TransCase a b c n m f' := by
  intro a b c n m f' HLU hna hnc hlv hfa hfb hfc hbd hm hf ASYM COMP TR1 TR2 h1 h2
  exact HLU f' a c hna hnc hlv

-- ===== [T1-T10] T9 : t9 =====
-- verdict: kimina OK (messages []), 0.07s
-- notes: ω̄/ω̄/ω̄ (level 3), [R91] 2.3.12 three times — the transcription of §8.2 case (8)'s ω̄ sub-branch with frag2_omg replaced by fragR_omg. One call of IH_TR1; Comp3 unused, Asym3 used only for `hac`. Reachability witness: lt (omg M) (omg (omg M)) && lt (omg (omg M)) (omg (omg (omg M))).
theorem t9 : ∀ (x y z : Term) (n m f' : Nat),
    TransCase (omg x) (omg y) (omg z) n m f' := by
  intro x y z n m f' hfa hfb hfc hbd hm hf ASYM COMP TR1 TR2 h1 h2
  have hfx := fragR_omg hfa; have hfy := fragR_omg hfb; have hfz := fragR_omg hfc
  have dx := deg_pos x; have dy := deg_pos y; have dz := deg_pos z
  have eA : (omg x).deg = 1 + x.deg := rfl
  have eB : (omg y).deg = 1 + y.deg := rfl
  have eC : (omg z).deg = 1 + z.deg := rfl
  have hac : omg x ≠ omg z := by
    intro hcc
    rw [← hcc] at h2
    rw [ASYM _ _ hfa hfb (f' + 1) (by omega) h1] at h2
    exact Bool.noConfusion h2
  have hne1 : omg x ≠ omg y := ne_of_ltF h1
  have hne2 : omg y ≠ omg z := ne_of_ltF h2
  rw [ltF_succ_omg_omg _ hne1] at h1
  rw [ltF_succ_omg_omg _ hne2] at h2
  rw [ltF_succ_omg_omg _ hac]
  exact TR1 x y z hfx hfy hfz (by omega) f' (by omega) h1 h2

-- ===== [T1-T10] T10 : t10 =====
-- verdict: kimina OK (messages []), 0.00s
-- notes: M/M/M (level 2), the deliberately vacuous case: level 2 has exactly one inhabitant, so h1 : ltF (f'+1) M M = true contradicts ltF_irrefl and the goal is discharged from h1 alone. This is the ONE case in the batch that is vacuous, and by design — §8.4(iv) says 'level 2 forces a = b = M, impossible'. 
theorem t10 : ∀ (n m f' : Nat), TransCase M M M n m f' := by
  intro n m f' hfa hfb hfc hbd hm hf ASYM COMP TR1 TR2 h1 h2
  rw [ltF_irrefl] at h1
  exact Bool.noConfusion h1

-- ===== [T11-T19] T11 : t11 (φ̄/φ̄/φ̄) =====
-- verdict: kimina 12346: OK (no messages), 0.99s; #print axioms t11 = [propext, Quot.sound]
-- notes: Transcription of §8.2 case (8) (WF.lean lines 4218-4332) with three substitutions and nothing else: Frag2 destructors -> fragR_phi; ltF_comparable2 hfp hft (by omega) -> Comp p t hfp hft f' (by omega); ltF_asymm2 hft hfp (by omega) h -> Asym t p hft hfp f' (by omega) h. §8.2's ambient LOW/UP are re-
theorem t11 : ∀ (p q r s t u : Term) (n m f' : Nat),
    TransCase (phi p q) (phi r s) (phi t u) n m f' := by
  intro p q r s t u n m f' hfa hfb hfc hb hm hf Asym Comp TR1 TR2 h1 h2
  obtain ⟨hfp, hfq⟩ := fragR_phi hfa
  obtain ⟨hfr, hfs⟩ := fragR_phi hfb
  obtain ⟨hft, hfu⟩ := fragR_phi hfc
  have dp := deg_pos p; have dq := deg_pos q; have dr := deg_pos r
  have ds := deg_pos s; have dt := deg_pos t; have du := deg_pos u
  have eA : (phi p q).deg = 1 + p.deg + q.deg := rfl
  have eB : (phi r s).deg = 1 + r.deg + s.deg := rfl
  have eC : (phi t u).deg = 1 + t.deg + u.deg := rfl
  have LOW : ∀ (x y : Term), x.deg + y.deg ≤ f' →
      ltF (f' + 1) x y = true → ltF f' x y = true := by
    intro x y hxy h
    rw [ltF_stable x y f' (f' + 1) hxy (by omega)]; exact h
  have UP : ∀ (x y : Term), x.deg + y.deg ≤ f' →
      ltF f' x y = true → ltF (f' + 1) x y = true := by
    intro x y hxy h
    rw [ltF_stable x y (f' + 1) f' (by omega) hxy]; exact h
  have hac : phi p q ≠ phi t u := by
    intro hc
    have hno := Asym (phi r s) (phi t u) hfb hfc (f' + 1) (by omega) h2
    rw [hc, hno] at h1
    exact Bool.noConfusion h1
  have hAB : ltF f' (phi p q) (phi r s) = true := LOW (phi p q) (phi r s) (by omega) h1
  have hBC : ltF f' (phi r s) (phi t u) = true := LOW (phi r s) (phi t u) (by omega) h2
  have hab1 : phi p q ≠ phi r s := ne_of_ltF h1
  have hab2 : phi r s ≠ phi t u := ne_of_ltF h2
  rw [ltF_succ_phi_phi _ hab1] at h1
  rw [ltF_succ_phi_phi _ hab2] at h2
  by_cases hpr : p = r
  · subst hpr
    rw [if_pos rfl] at h1
    by_cases hrt : p = t
    · subst hrt
      rw [if_pos rfl] at h2
      rw [ltF_succ_phi_phi _ hac, if_pos rfl]
      exact TR1 q s u hfq hfs hfu (by omega) f' (by omega) h1 h2
    · rw [if_neg hrt] at h2
      by_cases hrt2 : ltF f' p t = true
      · rw [if_pos hrt2] at h2
        rw [ltF_succ_phi_phi _ hac, if_neg hrt, if_pos hrt2]
        exact TR1 q s (phi t u) hfq hfs hfc (by omega) f' (by omega) h1 h2
      · rw [if_neg hrt2] at h2
        rw [ltF_succ_phi_phi _ hac, if_neg hrt, if_neg hrt2]
        simp only [Bool.or_eq_true, beq_iff_eq] at h2
        rcases h2 with h3 | h3
        · rw [← h3]; simp [hAB]
        · have h4 : ltF f' (phi p q) u = true :=
            TR2 (phi p q) u hfa hfu (by omega) f' (by omega) hAB h3
          simp [h4]
  · rw [if_neg hpr] at h1
    by_cases hpr2 : ltF f' p r = true
    · rw [if_pos hpr2] at h1
      by_cases hrt : r = t
      · subst hrt
        rw [if_pos rfl] at h2
        rw [ltF_succ_phi_phi _ hac, if_neg hpr, if_pos hpr2]
        exact TR2 q (phi r u) hfq hfc (by omega) f' (by omega) h1 hBC
      · rw [if_neg hrt] at h2
        by_cases hrt2 : ltF f' r t = true
        · rw [if_pos hrt2] at h2
          have hpt : ltF f' p t = true :=
            TR1 p r t hfp hfr hft (by omega) f' (by omega) hpr2 hrt2
          rw [ltF_succ_phi_phi _ hac, if_neg (ne_of_ltF hpt), if_pos hpt]
          exact TR2 q (phi t u) hfq hfc (by omega) f' (by omega) h1 hBC
        · rw [if_neg hrt2] at h2
          rcases Comp p t hfp hft f' (by omega) with hc1 | hc1 | hc1
          · rw [ltF_succ_phi_phi _ hac, if_neg (ne_of_ltF hc1), if_pos hc1]
            exact TR2 q (phi t u) hfq hfc (by omega) f' (by omega) h1 hBC
          · subst hc1
            rw [ltF_succ_phi_phi _ hac, if_pos rfl]
            simp only [Bool.or_eq_true, beq_iff_eq] at h2
            rcases h2 with h3 | h3
            · rw [← h3]; exact h1
            · exact TR2 q u hfq hfu (by omega) f' (by omega) h1 h3
          · have hpt : p ≠ t := by
              intro hc; rw [hc, ltF_irrefl] at hc1; exact Bool.noConfusion hc1
            have hnp : ltF f' p t = false := Asym t p hft hfp f' (by omega) hc1
            rw [ltF_succ_phi_phi _ hac, if_neg hpt, if_neg (by simp [hnp])]
            simp only [Bool.or_eq_true, beq_iff_eq] at h2
            rcases h2 with h3 | h3
            · rw [← h3]; simp [hAB]
            · have h4 : ltF f' (phi p q) u = true :=
                TR2 (phi p q) u hfa hfu (by omega) f' (by omega) hAB h3
              simp [h4]
    · rw [if_neg hpr2] at h1
      have hrp : ltF f' r p = true := by
        rcases Comp p r hfp hfr f' (by omega) with h3 | h3 | h3
        · exact absurd h3 hpr2
        · exact absurd h3 hpr
        · exact h3
      by_cases hrt : r = t
      · subst hrt
        rw [if_pos rfl] at h2
        rw [ltF_succ_phi_phi _ hac, if_neg hpr, if_neg hpr2]
        simp only [Bool.or_eq_true, beq_iff_eq] at h1
        rcases h1 with h3 | h3
        · rw [h3]; simp [h2]
        · have h4 : ltF f' (phi p q) u = true :=
            TR1 (phi p q) s u hfa hfs hfu (by omega) f' (by omega) h3 h2
          simp [h4]
      · rw [if_neg hrt] at h2
        by_cases hrt2 : ltF f' r t = true
        · rw [if_pos hrt2] at h2
          simp only [Bool.or_eq_true, beq_iff_eq] at h1
          have h4 : ltF f' (phi p q) (phi t u) = true := by
            rcases h1 with h3 | h3
            · rw [h3]; exact h2
            · exact TR1 (phi p q) s (phi t u) hfa hfs hfc
                (by omega) f' (by omega) h3 h2
          exact UP (phi p q) (phi t u) (by omega) h4
        · rw [if_neg hrt2] at h2
          have htr : ltF f' t r = true := by
            rcases Comp r t hfr hft f' (by omega) with h3 | h3 | h3
            · exact absurd h3 hrt2
            · exact absurd h3 hrt
            · exact h3
          have htp : ltF f' t p = true :=
            TR1 t r p hft hfr hfp (by omega) f' (by omega) htr hrp
          have hpt : p ≠ t := by
            intro hc; rw [← hc, ltF_irrefl] at htp; exact Bool.noConfusion htp
          have hnp : ltF f' p t = false := Asym t p hft hfp f' (by omega) htp
          rw [ltF_succ_phi_phi _ hac, if_neg hpt, if_neg (by simp [hnp])]
          simp only [Bool.or_eq_true, beq_iff_eq] at h2
          rcases h2 with h3 | h3
          · rw [← h3]; simp [hAB]
          · have h4 : ltF f' (phi p q) u = true :=
              TR2 (phi p q) u hfa hfu (by omega) f' (by omega) hAB h3
            simp [h4]

-- ===== [T11-T19] T12 : t12 (φ̄/φ̄/ψ) =====
-- verdict: kimina 12346: OK (no messages), 0.37s; #print axioms t12 = [propext, Quot.sound]
-- notes: Hypothesis 1 by 2.3.13 (ltF_succ_phi_phi), hypothesis 2 by 2.3.5 (ltF_succ_phi_psi, giving r < C and s < C), goal by 2.3.5 again, i.e. componentwise p < C and q < C. 13(ii): p = r gives p < C free from h2, and q < s < C by IH_TR1 with middle s (s.deg ≤ n follows from B.deg = 1+r.deg+s.deg ≤ n+1 and 
theorem t12 : ∀ (p q r s k w : Term) (n m f' : Nat),
    TransCase (phi p q) (phi r s) (psi k w) n m f' := by
  intro p q r s k w n m f' hfa hfb hfc hb hm hf _Asym _Comp TR1 TR2 h1 h2
  obtain ⟨hfp, hfq⟩ := fragR_phi hfa
  obtain ⟨hfr, hfs⟩ := fragR_phi hfb
  have dp := deg_pos p; have dq := deg_pos q
  have dr := deg_pos r; have ds := deg_pos s
  have dk := deg_pos k; have dw := deg_pos w
  have eA : (phi p q).deg = 1 + p.deg + q.deg := rfl
  have eB : (phi r s).deg = 1 + r.deg + s.deg := rfl
  have eC : (psi k w).deg = 1 + k.deg + w.deg := rfl
  have hBC : ltF f' (phi r s) (psi k w) = true := by
    rw [ltF_stable _ _ f' (f' + 1) (by omega) (by omega)]; exact h2
  have hab1 : phi p q ≠ phi r s := ne_of_ltF h1
  have h2' : ltF f' r (psi k w) = true ∧ ltF f' s (psi k w) = true := by
    rw [ltF_succ_phi_psi] at h2; simpa only [Bool.and_eq_true] using h2
  rw [ltF_succ_phi_phi _ hab1] at h1
  by_cases hpr : p = r
  · subst hpr
    rw [if_pos rfl] at h1
    rw [ltF_succ_phi_psi]
    simp only [Bool.and_eq_true]
    exact ⟨h2'.1, TR1 q s (psi k w) hfq hfs hfc (by omega) f' (by omega) h1 h2'.2⟩
  · rw [if_neg hpr] at h1
    by_cases hpr2 : ltF f' p r = true
    · rw [if_pos hpr2] at h1
      rw [ltF_succ_phi_psi]
      simp only [Bool.and_eq_true]
      exact ⟨TR1 p r (psi k w) hfp hfr hfc (by omega) f' (by omega) hpr2 h2'.1,
             TR2 q (psi k w) hfq hfc (by omega) f' (by omega) h1 hBC⟩
    · rw [if_neg hpr2] at h1
      simp only [Bool.or_eq_true, beq_iff_eq] at h1
      have hAC : ltF f' (phi p q) (psi k w) = true := by
        rcases h1 with h3 | h3
        · rw [h3]; exact h2'.2
        · exact TR1 (phi p q) s (psi k w) hfa hfs hfc (by omega) f' (by omega) h3 h2'.2
      rw [ltF_stable _ _ (f' + 1) f' (by omega) (by omega)]
      exact hAC

-- ===== [T11-T19] T13 : t13 (φ̄/φ̄/Z) =====
-- verdict: kimina 12346: OK (no messages), 0.35s; #print axioms t13 = [propext, Quot.sound]
-- notes: T12 verbatim with the ψ endpoint replaced by a Z endpoint: ltF_succ_phi_psi -> ltF_succ_phi_Z. 2.3.5 has literally the same body for both SC shapes (§8.3's comment on ltF_succ_phi_psi / ltF_succ_phi_Z), so the proof text is identical modulo that rewrite name. Consumes IH_TR1 and IH_TR2 only.
theorem t13 : ∀ (p q r s d : Term) (n m f' : Nat),
    TransCase (phi p q) (phi r s) (Z d) n m f' := by
  intro p q r s d n m f' hfa hfb hfc hb hm hf _Asym _Comp TR1 TR2 h1 h2
  obtain ⟨hfp, hfq⟩ := fragR_phi hfa
  obtain ⟨hfr, hfs⟩ := fragR_phi hfb
  have dp := deg_pos p; have dq := deg_pos q
  have dr := deg_pos r; have ds := deg_pos s
  have dd := deg_pos d
  have eA : (phi p q).deg = 1 + p.deg + q.deg := rfl
  have eB : (phi r s).deg = 1 + r.deg + s.deg := rfl
  have eC : (Z d).deg = 1 + d.deg := rfl
  have hBC : ltF f' (phi r s) (Z d) = true := by
    rw [ltF_stable _ _ f' (f' + 1) (by omega) (by omega)]; exact h2
  have hab1 : phi p q ≠ phi r s := ne_of_ltF h1
  have h2' : ltF f' r (Z d) = true ∧ ltF f' s (Z d) = true := by
    rw [ltF_succ_phi_Z] at h2; simpa only [Bool.and_eq_true] using h2
  rw [ltF_succ_phi_phi _ hab1] at h1
  by_cases hpr : p = r
  · subst hpr
    rw [if_pos rfl] at h1
    rw [ltF_succ_phi_Z]
    simp only [Bool.and_eq_true]
    exact ⟨h2'.1, TR1 q s (Z d) hfq hfs hfc (by omega) f' (by omega) h1 h2'.2⟩
  · rw [if_neg hpr] at h1
    by_cases hpr2 : ltF f' p r = true
    · rw [if_pos hpr2] at h1
      rw [ltF_succ_phi_Z]
      simp only [Bool.and_eq_true]
      exact ⟨TR1 p r (Z d) hfp hfr hfc (by omega) f' (by omega) hpr2 h2'.1,
             TR2 q (Z d) hfq hfc (by omega) f' (by omega) h1 hBC⟩
    · rw [if_neg hpr2] at h1
      simp only [Bool.or_eq_true, beq_iff_eq] at h1
      have hAC : ltF f' (phi p q) (Z d) = true := by
        rcases h1 with h3 | h3
        · rw [h3]; exact h2'.2
        · exact TR1 (phi p q) s (Z d) hfa hfs hfc (by omega) f' (by omega) h3 h2'.2
      rw [ltF_stable _ _ (f' + 1) f' (by omega) (by omega)]
      exact hAC

-- ===== [T11-T19] T14 : t14 (φ̄/ψ/φ̄) =====
-- verdict: kimina 12346: OK (no messages), 0.43s; #print axioms t14 = [propext, Quot.sound]
-- notes: Hypothesis 1 by 2.3.5 (p < B and q < B), hypothesis 2 by 2.3.4 (ltF_succ_psi_phi: B ≤ t or B ≤ u), goal by 2.3.13. The whole case turns on one derived disjunction hPT: either p < t (when B ≤ t, by IH_TR2 with x = p, z = t) or both q < u and A < u (when B ≤ u, by IH_TR2 twice). Reading the goal's 13-
theorem t14 : ∀ (p q k w t u : Term) (n m f' : Nat),
    TransCase (phi p q) (psi k w) (phi t u) n m f' := by
  intro p q k w t u n m f' hfa hfb hfc hb hm hf Asym _Comp _TR1 TR2 h1 h2
  obtain ⟨hfp, hfq⟩ := fragR_phi hfa
  obtain ⟨hft, hfu⟩ := fragR_phi hfc
  have dp := deg_pos p; have dq := deg_pos q
  have dk := deg_pos k; have dw := deg_pos w
  have dt := deg_pos t; have du := deg_pos u
  have eA : (phi p q).deg = 1 + p.deg + q.deg := rfl
  have eB : (psi k w).deg = 1 + k.deg + w.deg := rfl
  have eC : (phi t u).deg = 1 + t.deg + u.deg := rfl
  have hAB : ltF f' (phi p q) (psi k w) = true := by
    rw [ltF_stable _ _ f' (f' + 1) (by omega) (by omega)]; exact h1
  have hBC : ltF f' (psi k w) (phi t u) = true := by
    rw [ltF_stable _ _ f' (f' + 1) (by omega) (by omega)]; exact h2
  have hac : phi p q ≠ phi t u := by
    intro hc
    have hno := Asym (psi k w) (phi t u) hfb hfc (f' + 1) (by omega) h2
    rw [hc, hno] at h1
    exact Bool.noConfusion h1
  have h1' : ltF f' p (psi k w) = true ∧ ltF f' q (psi k w) = true := by
    have h := h1; rw [ltF_succ_phi_psi] at h; simpa only [Bool.and_eq_true] using h
  have hB : psi k w = t ∨ psi k w = u ∨ ltF f' (psi k w) t = true
      ∨ ltF f' (psi k w) u = true := by
    have h := h2; rw [ltF_succ_psi_phi] at h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with ((h3 | h3) | h3) | h3
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr h3))
  have hqC : ltF f' q (phi t u) = true :=
    TR2 q (phi t u) hfq hfc (by omega) f' (by omega) h1'.2 hBC
  have hPT : ltF f' p t = true ∨ (ltF f' q u = true ∧ ltF f' (phi p q) u = true) := by
    rcases hB with h3 | h3 | h3 | h3
    · exact Or.inl (by rw [← h3]; exact h1'.1)
    · exact Or.inr ⟨by rw [← h3]; exact h1'.2, by rw [← h3]; exact hAB⟩
    · exact Or.inl (TR2 p t hfp hft (by omega) f' (by omega) h1'.1 h3)
    · exact Or.inr ⟨TR2 q u hfq hfu (by omega) f' (by omega) h1'.2 h3,
                    TR2 (phi p q) u hfa hfu (by omega) f' (by omega) hAB h3⟩
  rw [ltF_succ_phi_phi _ hac]
  by_cases hpt : p = t
  · rw [if_pos hpt]
    rcases hPT with h3 | h3
    · exfalso; rw [hpt, ltF_irrefl] at h3; exact Bool.noConfusion h3
    · exact h3.1
  · rw [if_neg hpt]
    by_cases hpt2 : ltF f' p t = true
    · rw [if_pos hpt2]; exact hqC
    · rw [if_neg hpt2]
      rcases hPT with h3 | h3
      · exact absurd h3 hpt2
      · simp [h3.2]

-- ===== [T11-T19] T15 : t15 (φ̄/ψ/ψ) =====
-- verdict: kimina 12346: OK (no messages), 0.25s; #print axioms t15 = [propext, Quot.sound]
-- notes: The φ̄-first / SC-SC pattern: hypothesis 1 by 2.3.5 makes A's two components sit below B, the goal by 2.3.5 asks for them below C, and IH_TR2 (middle stays B, the endpoints p and q are strict subterms of A so the degree sum drops) closes both. Hypothesis 2 is never unfolded — the ψ-vs-ψ clause 2.3.1
theorem t15 : ∀ (p q k w j v : Term) (n m f' : Nat),
    TransCase (phi p q) (psi k w) (psi j v) n m f' := by
  intro p q k w j v n m f' hfa hfb hfc hb hm hf _Asym _Comp _TR1 TR2 h1 h2
  obtain ⟨hfp, hfq⟩ := fragR_phi hfa
  have dp := deg_pos p; have dq := deg_pos q
  have dk := deg_pos k; have dw := deg_pos w
  have dj := deg_pos j; have dv := deg_pos v
  have eA : (phi p q).deg = 1 + p.deg + q.deg := rfl
  have eB : (psi k w).deg = 1 + k.deg + w.deg := rfl
  have eC : (psi j v).deg = 1 + j.deg + v.deg := rfl
  rw [ltF_succ_phi_psi] at h1
  simp only [Bool.and_eq_true] at h1
  have hBC : ltF f' (psi k w) (psi j v) = true := by
    rw [ltF_stable _ _ f' (f' + 1) (by omega) (by omega)]; exact h2
  rw [ltF_succ_phi_psi]
  simp only [Bool.and_eq_true]
  exact ⟨TR2 p (psi j v) hfp hfc (by omega) f' (by omega) h1.1 hBC,
         TR2 q (psi j v) hfq hfc (by omega) f' (by omega) h1.2 hBC⟩

-- ===== [T11-T19] T16 : t16 (φ̄/ψ/Z) =====
-- verdict: kimina 12346: OK (no messages), 0.20s; #print axioms t16 = [propext, Quot.sound]
-- notes: Same pattern as T15. Notably hypothesis 2 (the ψ-vs-Z clause 2.3.8/2.3.6, which is one of the three that recurse through starF) is used only as an opaque `ltF f' B C = true` — it is never destructured, so this case creates no starF obligation. Consumes IH_TR2 only.
theorem t16 : ∀ (p q k w d : Term) (n m f' : Nat),
    TransCase (phi p q) (psi k w) (Z d) n m f' := by
  intro p q k w d n m f' hfa hfb hfc hb hm hf _Asym _Comp _TR1 TR2 h1 h2
  obtain ⟨hfp, hfq⟩ := fragR_phi hfa
  have dp := deg_pos p; have dq := deg_pos q
  have dk := deg_pos k; have dw := deg_pos w
  have dd := deg_pos d
  have eA : (phi p q).deg = 1 + p.deg + q.deg := rfl
  have eB : (psi k w).deg = 1 + k.deg + w.deg := rfl
  have eC : (Z d).deg = 1 + d.deg := rfl
  rw [ltF_succ_phi_psi] at h1
  simp only [Bool.and_eq_true] at h1
  have hBC : ltF f' (psi k w) (Z d) = true := by
    rw [ltF_stable _ _ f' (f' + 1) (by omega) (by omega)]; exact h2
  rw [ltF_succ_phi_Z]
  simp only [Bool.and_eq_true]
  exact ⟨TR2 p (Z d) hfp hfc (by omega) f' (by omega) h1.1 hBC,
         TR2 q (Z d) hfq hfc (by omega) f' (by omega) h1.2 hBC⟩

-- ===== [T11-T19] T17 : t17 (φ̄/Z/φ̄) =====
-- verdict: kimina 12346: OK (no messages), 0.41s; #print axioms t17 = [propext, Quot.sound]
-- notes: T14 verbatim with the ψ middle replaced by a Z middle: ltF_succ_phi_psi -> ltF_succ_phi_Z and ltF_succ_psi_phi -> ltF_succ_Z_phi. 2.3.5 and 2.3.4 have the same body for both SC shapes, so nothing else changes. Consumes Asym3 (only for A ≠ C) and IH_TR2.
theorem t17 : ∀ (p q e t u : Term) (n m f' : Nat),
    TransCase (phi p q) (Z e) (phi t u) n m f' := by
  intro p q e t u n m f' hfa hfb hfc hb hm hf Asym _Comp _TR1 TR2 h1 h2
  obtain ⟨hfp, hfq⟩ := fragR_phi hfa
  obtain ⟨hft, hfu⟩ := fragR_phi hfc
  have dp := deg_pos p; have dq := deg_pos q
  have de := deg_pos e
  have dt := deg_pos t; have du := deg_pos u
  have eA : (phi p q).deg = 1 + p.deg + q.deg := rfl
  have eB : (Z e).deg = 1 + e.deg := rfl
  have eC : (phi t u).deg = 1 + t.deg + u.deg := rfl
  have hAB : ltF f' (phi p q) (Z e) = true := by
    rw [ltF_stable _ _ f' (f' + 1) (by omega) (by omega)]; exact h1
  have hBC : ltF f' (Z e) (phi t u) = true := by
    rw [ltF_stable _ _ f' (f' + 1) (by omega) (by omega)]; exact h2
  have hac : phi p q ≠ phi t u := by
    intro hc
    have hno := Asym (Z e) (phi t u) hfb hfc (f' + 1) (by omega) h2
    rw [hc, hno] at h1
    exact Bool.noConfusion h1
  have h1' : ltF f' p (Z e) = true ∧ ltF f' q (Z e) = true := by
    have h := h1; rw [ltF_succ_phi_Z] at h; simpa only [Bool.and_eq_true] using h
  have hB : Z e = t ∨ Z e = u ∨ ltF f' (Z e) t = true ∨ ltF f' (Z e) u = true := by
    have h := h2; rw [ltF_succ_Z_phi] at h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with ((h3 | h3) | h3) | h3
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr h3))
  have hqC : ltF f' q (phi t u) = true :=
    TR2 q (phi t u) hfq hfc (by omega) f' (by omega) h1'.2 hBC
  have hPT : ltF f' p t = true ∨ (ltF f' q u = true ∧ ltF f' (phi p q) u = true) := by
    rcases hB with h3 | h3 | h3 | h3
    · exact Or.inl (by rw [← h3]; exact h1'.1)
    · exact Or.inr ⟨by rw [← h3]; exact h1'.2, by rw [← h3]; exact hAB⟩
    · exact Or.inl (TR2 p t hfp hft (by omega) f' (by omega) h1'.1 h3)
    · exact Or.inr ⟨TR2 q u hfq hfu (by omega) f' (by omega) h1'.2 h3,
                    TR2 (phi p q) u hfa hfu (by omega) f' (by omega) hAB h3⟩
  rw [ltF_succ_phi_phi _ hac]
  by_cases hpt : p = t
  · rw [if_pos hpt]
    rcases hPT with h3 | h3
    · exfalso; rw [hpt, ltF_irrefl] at h3; exact Bool.noConfusion h3
    · exact h3.1
  · rw [if_neg hpt]
    by_cases hpt2 : ltF f' p t = true
    · rw [if_pos hpt2]; exact hqC
    · rw [if_neg hpt2]
      rcases hPT with h3 | h3
      · exact absurd h3 hpt2
      · simp [h3.2]

-- ===== [T11-T19] T18 : t18 (φ̄/Z/ψ) =====
-- verdict: kimina 12346: OK (no messages), 0.21s; #print axioms t18 = [propext, Quot.sound]
-- notes: Same pattern as T15/T16; hypothesis 2 (2.3.9, the Z-vs-ψ clause that goes through δ*) is used opaquely and never destructured. Consumes IH_TR2 only.
theorem t18 : ∀ (p q e k w : Term) (n m f' : Nat),
    TransCase (phi p q) (Z e) (psi k w) n m f' := by
  intro p q e k w n m f' hfa hfb hfc hb hm hf _Asym _Comp _TR1 TR2 h1 h2
  obtain ⟨hfp, hfq⟩ := fragR_phi hfa
  have dp := deg_pos p; have dq := deg_pos q
  have de := deg_pos e
  have dk := deg_pos k; have dw := deg_pos w
  have eA : (phi p q).deg = 1 + p.deg + q.deg := rfl
  have eB : (Z e).deg = 1 + e.deg := rfl
  have eC : (psi k w).deg = 1 + k.deg + w.deg := rfl
  rw [ltF_succ_phi_Z] at h1
  simp only [Bool.and_eq_true] at h1
  have hBC : ltF f' (Z e) (psi k w) = true := by
    rw [ltF_stable _ _ f' (f' + 1) (by omega) (by omega)]; exact h2
  rw [ltF_succ_phi_psi]
  simp only [Bool.and_eq_true]
  exact ⟨TR2 p (psi k w) hfp hfc (by omega) f' (by omega) h1.1 hBC,
         TR2 q (psi k w) hfq hfc (by omega) f' (by omega) h1.2 hBC⟩

-- ===== [T11-T19] T19 : t19 (φ̄/Z/Z) =====
-- verdict: kimina 12346: OK (no messages), 0.19s; #print axioms t19 = [propext, Quot.sound]
-- notes: Same pattern as T15/T16/T18; hypothesis 2 is 2.3.15 (the clause that routes through starF TWICE) and is used opaquely. Consumes IH_TR2 only.
theorem t19 : ∀ (p q e d : Term) (n m f' : Nat),
    TransCase (phi p q) (Z e) (Z d) n m f' := by
  intro p q e d n m f' hfa hfb hfc hb hm hf _Asym _Comp _TR1 TR2 h1 h2
  obtain ⟨hfp, hfq⟩ := fragR_phi hfa
  have dp := deg_pos p; have dq := deg_pos q
  have de := deg_pos e; have dd := deg_pos d
  have eA : (phi p q).deg = 1 + p.deg + q.deg := rfl
  have eB : (Z e).deg = 1 + e.deg := rfl
  have eC : (Z d).deg = 1 + d.deg := rfl
  rw [ltF_succ_phi_Z] at h1
  simp only [Bool.and_eq_true] at h1
  have hBC : ltF f' (Z e) (Z d) = true := by
    rw [ltF_stable _ _ f' (f' + 1) (by omega) (by omega)]; exact h2
  rw [ltF_succ_phi_Z]
  simp only [Bool.and_eq_true]
  exact ⟨TR2 p (Z d) hfp hfc (by omega) f' (by omega) h1.1 hBC,
         TR2 q (Z d) hfq hfc (by omega) f' (by omega) h1.2 hBC⟩

-- ===== [T20-T28] T20 : t20_psi_phi_phi =====
-- verdict: kimina http://localhost:12346/api/check — messages [] (clean); also clean in the combined 8-theorem snippet; #print axioms → [propext, Quot.sound]
-- notes: ψφφ. h1 read by 2.3.4 (ltF_succ_psi_phi), h2 by 2.3.13 (ltF_succ_phi_phi), goal emitted by 2.3.4. Three h2-branches: (ii) c=t → ψ≤c gives disjunct t, ψ≤d chains through d<u by IH_TR1 (middle d, d.deg ≤ n from hbn); (i) c<t → ψ≤c chains to t by IH_TR1 (middle c), ψ≤d gives ψ<φtu at f' then UP; (iii) 
theorem t20_psi_phi_phi : ∀ (k a c d t u : Term) (n m f' : Nat),
    TransCase (psi k a) (phi c d) (phi t u) n m f' := by
  intro k a c d t u n m f'
  intro hfa hfb hfc hbn hacm hf _hA _hC htr1 htr2 h1 h2
  obtain ⟨hfc0, hfd⟩ := fragR_phi hfb
  obtain ⟨hft, hfu⟩ := fragR_phi hfc
  have dk := deg_pos k; have da := deg_pos a
  have dc := deg_pos c; have dd := deg_pos d
  have dt := deg_pos t; have du := deg_pos u
  simp only [Term.deg] at hbn hacm hf
  have LOW : ∀ (x y : Term), x.deg + y.deg ≤ f' →
      ltF (f' + 1) x y = true → ltF f' x y = true := by
    intro x y hxy h
    rw [ltF_stable x y f' (f' + 1) hxy (by omega)]; exact h
  have UP : ∀ (x y : Term), x.deg + y.deg ≤ f' →
      ltF f' x y = true → ltF (f' + 1) x y = true := by
    intro x y hxy h
    rw [ltF_stable x y (f' + 1) f' (by omega) hxy]; exact h
  have hAB : ltF f' (psi k a) (phi c d) = true :=
    LOW _ _ (by simp only [Term.deg]; omega) h1
  have hne2 : phi c d ≠ phi t u := ne_of_ltF h2
  rw [ltF_succ_psi_phi] at h1
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  rw [ltF_succ_phi_phi _ hne2] at h2
  by_cases hct : c = t
  · subst hct
    rw [if_pos rfl] at h2
    rw [ltF_succ_psi_phi]
    rcases h1 with ((h3 | h3) | h3) | h3
    · simp [h3]
    · have h4 : ltF f' (psi k a) u = true := by rw [h3]; exact h2
      simp [h4]
    · simp [h3]
    · have h4 : ltF f' (psi k a) u = true :=
        htr1 (psi k a) d u hfa hfd hfu (by omega) f' (by simp only [Term.deg]; omega) h3 h2
      simp [h4]
  · rw [if_neg hct] at h2
    by_cases hlt : ltF f' c t = true
    · rw [if_pos hlt] at h2
      rcases h1 with ((h3 | h3) | h3) | h3
      · rw [ltF_succ_psi_phi]
        have h4 : ltF f' (psi k a) t = true := by rw [h3]; exact hlt
        simp [h4]
      · exact UP _ _ (by simp only [Term.deg]; omega) (by rw [h3]; exact h2)
      · rw [ltF_succ_psi_phi]
        have h4 : ltF f' (psi k a) t = true :=
          htr1 (psi k a) c t hfa hfc0 hft (by omega) f' (by simp only [Term.deg]; omega) h3 hlt
        simp [h4]
      · exact UP _ _ (by simp only [Term.deg]; omega)
          (htr1 (psi k a) d (phi t u) hfa hfd hfc (by omega) f'
            (by simp only [Term.deg]; omega) h3 h2)
    · rw [if_neg hlt] at h2
      simp only [Bool.or_eq_true, beq_iff_eq] at h2
      rw [ltF_succ_psi_phi]
      rcases h2 with h3 | h3
      · have h4 : ltF f' (psi k a) u = true := by rw [← h3]; exact hAB
        simp [h4]
      · have h4 : ltF f' (psi k a) u = true :=
          htr2 (psi k a) u hfa hfu (by simp only [Term.deg]; omega) f'
            (by simp only [Term.deg]; omega) hAB h3
        simp [h4]

-- ===== [T20-T28] T21 : t21_psi_phi_psi =====
-- verdict: kimina — messages [] (clean); clean in combined snippet; axioms [propext, Quot.sound]
-- notes: ψφψ. h1 by 2.3.4, h2 by 2.3.5 (ltF_succ_phi_psi) which hands over BOTH c<ψqe and d<ψqe. Whichever component of φcd dominates ψka, that component is already below ψqe, so one IH_TR1 (middle c or d, both of degree ≤ n) finishes at fuel f' and UP lifts it. Consumes IH_TR1 only.
theorem t21_psi_phi_psi : ∀ (k a c d q e : Term) (n m f' : Nat),
    TransCase (psi k a) (phi c d) (psi q e) n m f' := by
  intro k a c d q e n m f'
  intro hfa hfb hfc hbn hacm hf _hA _hC htr1 _htr2 h1 h2
  obtain ⟨hfc0, hfd⟩ := fragR_phi hfb
  have dk := deg_pos k; have da := deg_pos a
  have dc := deg_pos c; have dd := deg_pos d
  have dq := deg_pos q; have de := deg_pos e
  simp only [Term.deg] at hbn hacm hf
  have UP : ∀ (x y : Term), x.deg + y.deg ≤ f' →
      ltF f' x y = true → ltF (f' + 1) x y = true := by
    intro x y hxy h
    rw [ltF_stable x y (f' + 1) f' (by omega) hxy]; exact h
  rw [ltF_succ_psi_phi] at h1
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  rw [ltF_succ_phi_psi] at h2
  simp only [Bool.and_eq_true] at h2
  obtain ⟨h2c, h2d⟩ := h2
  refine UP _ _ (by simp only [Term.deg]; omega) ?_
  rcases h1 with ((h3 | h3) | h3) | h3
  · rw [h3]; exact h2c
  · rw [h3]; exact h2d
  · exact htr1 (psi k a) c (psi q e) hfa hfc0 hfc (by omega) f'
      (by simp only [Term.deg]; omega) h3 h2c
  · exact htr1 (psi k a) d (psi q e) hfa hfd hfc (by omega) f'
      (by simp only [Term.deg]; omega) h3 h2d

-- ===== [T20-T28] T22 : t22_psi_phi_Z =====
-- verdict: kimina — messages [] (clean); clean in combined snippet; axioms [propext, Quot.sound]
-- notes: ψφZ. Identical to T21 with the other SC shape: 2.3.5 is ltF_succ_phi_Z here. Note NO starF appears — the goal ψka < Zz is produced at fuel f' by IH_TR1 and lifted by UP, so 2.3.6/2.3.8 never has to be unfolded. Consumes IH_TR1 only.
theorem t22_psi_phi_Z : ∀ (k a c d z : Term) (n m f' : Nat),
    TransCase (psi k a) (phi c d) (Z z) n m f' := by
  intro k a c d z n m f'
  intro hfa hfb hfc hbn hacm hf _hA _hC htr1 _htr2 h1 h2
  obtain ⟨hfc0, hfd⟩ := fragR_phi hfb
  have dk := deg_pos k; have da := deg_pos a
  have dc := deg_pos c; have dd := deg_pos d
  have dz := deg_pos z
  simp only [Term.deg] at hbn hacm hf
  have UP : ∀ (x y : Term), x.deg + y.deg ≤ f' →
      ltF f' x y = true → ltF (f' + 1) x y = true := by
    intro x y hxy h
    rw [ltF_stable x y (f' + 1) f' (by omega) hxy]; exact h
  rw [ltF_succ_psi_phi] at h1
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  rw [ltF_succ_phi_Z] at h2
  simp only [Bool.and_eq_true] at h2
  obtain ⟨h2c, h2d⟩ := h2
  refine UP _ _ (by simp only [Term.deg]; omega) ?_
  rcases h1 with ((h3 | h3) | h3) | h3
  · rw [h3]; exact h2c
  · rw [h3]; exact h2d
  · exact htr1 (psi k a) c (Z z) hfa hfc0 hfc (by omega) f'
      (by simp only [Term.deg]; omega) h3 h2c
  · exact htr1 (psi k a) d (Z z) hfa hfd hfc (by omega) f'
      (by simp only [Term.deg]; omega) h3 h2d

-- ===== [T20-T28] T23 : t23_psi_psi_phi =====
-- verdict: kimina — messages [] (clean); clean in combined snippet; axioms [propext, Quot.sound]
-- notes: ψψφ. h2 by 2.3.4 says ψpb ≤ t or ψpb ≤ u; ψka < ψpb (h1, lowered by §5) then transports to the SAME component by IH_TR2 (middle stays ψpb; t resp. u replaces φtu, so a.deg+c.deg strictly drops), and the goal is emitted by 2.3.4. h1 is never unfolded, so 2.3.14 and κ∈R are not touched. Consumes IH_TR
theorem t23_psi_psi_phi : ∀ (k a p b t u : Term) (n m f' : Nat),
    TransCase (psi k a) (psi p b) (phi t u) n m f' := by
  intro k a p b t u n m f'
  intro hfa hfb hfc hbn hacm hf _hA _hC _htr1 htr2 h1 h2
  obtain ⟨hft, hfu⟩ := fragR_phi hfc
  have dk := deg_pos k; have da := deg_pos a
  have dp := deg_pos p; have db := deg_pos b
  have dt := deg_pos t; have du := deg_pos u
  simp only [Term.deg] at hbn hacm hf
  have LOW : ∀ (x y : Term), x.deg + y.deg ≤ f' →
      ltF (f' + 1) x y = true → ltF f' x y = true := by
    intro x y hxy h
    rw [ltF_stable x y f' (f' + 1) hxy (by omega)]; exact h
  have hAB : ltF f' (psi k a) (psi p b) = true :=
    LOW _ _ (by simp only [Term.deg]; omega) h1
  rw [ltF_succ_psi_phi] at h2
  simp only [Bool.or_eq_true, beq_iff_eq] at h2
  rw [ltF_succ_psi_phi]
  rcases h2 with ((h3 | h3) | h3) | h3
  · have h4 : ltF f' (psi k a) t = true := by rw [← h3]; exact hAB
    simp [h4]
  · have h4 : ltF f' (psi k a) u = true := by rw [← h3]; exact hAB
    simp [h4]
  · have h4 : ltF f' (psi k a) t = true :=
      htr2 (psi k a) t hfa hft (by simp only [Term.deg]; omega) f'
        (by simp only [Term.deg]; omega) hAB h3
    simp [h4]
  · have h4 : ltF f' (psi k a) u = true :=
      htr2 (psi k a) u hfa hfu (by simp only [Term.deg]; omega) f'
        (by simp only [Term.deg]; omega) hAB h3
    simp [h4]

-- ===== [T20-T28] T25 : t25_psi_psi_Z =====
-- verdict: kimina — messages [] (clean); clean in combined snippet; axioms [propext, Quot.sound]
-- notes: ψψZ. Split on WHICH clause h2 (ψpb < Zz) used. If 2.3.8 fired (p ≤ Zz) the proof never touches starF: 2.3.14 on h1 gives k=p (then the goal's own 2.3.8 guard is hpz verbatim), k<p (then k<p≤Zz by IH_TR1, middle p, and the goal fires 2.3.8), or ψka<p (then ψka<Zz at f' by IH_TR1 and UP). If 2.3.6 fir
theorem t25_psi_psi_Z : ∀ (k a p b z : Term) (n m f' : Nat),
    TransCase (psi k a) (psi p b) (Z z) n m f' := by
  intro k a p b z n m f'
  intro hfa hfb hfc hbn hacm hf _hA _hC htr1 htr2 h1 h2
  obtain ⟨_hkR, hfk, _hfa'⟩ := fragR_psi hfa
  obtain ⟨_hpR, hfp, _hfb'⟩ := fragR_psi hfb
  have hfz : FragR z = true := fragR_Z hfc
  have dk := deg_pos k; have da := deg_pos a
  have dp := deg_pos p; have db := deg_pos b
  have dz := deg_pos z
  simp only [Term.deg] at hbn hacm hf
  -- the fragment is closed under `α*` (§8.4(ii), case S1), inline
  have hstar : ∀ (g : Nat) (s : Term), FragR s = true → FragR (starF g s) = true := by
    intro g
    induction g with
    | zero => intro s _; rfl
    | succ g ih =>
      intro s hs
      cases s with
      | zero => exact rfl
      | M => exact rfl
      | psi kk aa => exact hs
      | Z aa => exact hs
      | omg aa => exact ih aa hs
      | add aa bb =>
        obtain ⟨ha', hb'⟩ := fragR_add hs
        rw [starF_succ_add]
        cases ltF g (starF g aa) (starF g bb)
        · show FragR (starF g aa) = true
          exact ih aa ha'
        · show FragR (starF g bb) = true
          exact ih bb hb'
      | phi aa bb =>
        obtain ⟨ha', hb'⟩ := fragR_phi hs
        rw [starF_succ_phi]
        cases ltF g (starF g aa) (starF g bb)
        · show FragR (starF g aa) = true
          exact ih aa ha'
        · show FragR (starF g bb) = true
          exact ih bb hb'
  have LOW : ∀ (x y : Term), x.deg + y.deg ≤ f' →
      ltF (f' + 1) x y = true → ltF f' x y = true := by
    intro x y hxy h
    rw [ltF_stable x y f' (f' + 1) hxy (by omega)]; exact h
  have UP : ∀ (x y : Term), x.deg + y.deg ≤ f' →
      ltF f' x y = true → ltF (f' + 1) x y = true := by
    intro x y hxy h
    rw [ltF_stable x y (f' + 1) f' (by omega) hxy]; exact h
  have hAB : ltF f' (psi k a) (psi p b) = true :=
    LOW _ _ (by simp only [Term.deg]; omega) h1
  rw [ltF_succ_psi_Z] at h2
  by_cases hpz : (p == Z z || ltF f' p (Z z)) = true
  · -- 2.3.8 on the right: `p ≤ Zz`, so everything below `p` is below `Zz`
    have key : ∀ (x : Term), FragR x = true → x.deg + p.deg + (Z z).deg ≤ f' →
        ltF f' x p = true → ltF f' x (Z z) = true := by
      intro x hx hxd hxp
      simp only [Bool.or_eq_true, beq_iff_eq] at hpz
      rcases hpz with h4 | h4
      · rw [← h4]; exact hxp
      · exact htr1 x p (Z z) hx hfp hfc (by omega) f' hxd hxp h4
    have hne1 : psi k a ≠ psi p b := ne_of_ltF h1
    rw [ltF_succ_psi_psi _ hne1] at h1
    by_cases hkp : k = p
    · subst hkp
      rw [ltF_succ_psi_Z, if_pos hpz]
    · rw [if_neg hkp] at h1
      by_cases hklt : ltF f' k p = true
      · rw [if_pos hklt] at h1
        have hkz : ltF f' k (Z z) = true :=
          key k hfk (by simp only [Term.deg]; omega) hklt
        rw [ltF_succ_psi_Z, if_pos (by simp [hkz])]
      · rw [if_neg hklt] at h1
        exact UP _ _ (by simp only [Term.deg]; omega)
          (key (psi k a) hfa (by simp only [Term.deg]; omega) h1)
  · -- 2.3.6 on the right: `ψpb ≤ z*`
    rw [if_neg hpz] at h2
    simp only [Bool.or_eq_true, beq_iff_eq] at h2
    by_cases hkz : (k == Z z || ltF f' k (Z z)) = true
    · rw [ltF_succ_psi_Z, if_pos hkz]
    · rw [ltF_succ_psi_Z, if_neg hkz]
      have hds := deg_starF f' z
      have h4 : ltF f' (psi k a) (starF f' z) = true := by
        rcases h2 with h3 | h3
        · rw [← h3]; exact hAB
        · exact htr2 (psi k a) (starF f' z) hfa (hstar f' z hfz)
            (by simp only [Term.deg]; omega) f' (by simp only [Term.deg]; omega) hAB h3
      simp [h4]

-- ===== [T20-T28] T26 : t26_psi_Z_phi =====
-- verdict: kimina — messages [] (clean); clean in combined snippet; axioms [propext, Quot.sound]
-- notes: ψZφ. Structurally identical to T23 with the middle SC shape swapped: h2 read by 2.3.4 (ltF_succ_Z_phi), h1 left folded and only lowered to fuel f', then IH_TR2 moves ψka past Zy to the dominating component of φtu. h1's ψ-vs-Z clause is never unfolded, so no starF. Consumes IH_TR2 only.
theorem t26_psi_Z_phi : ∀ (k a y t u : Term) (n m f' : Nat),
    TransCase (psi k a) (Z y) (phi t u) n m f' := by
  intro k a y t u n m f'
  intro hfa hfb hfc hbn hacm hf _hA _hC _htr1 htr2 h1 h2
  obtain ⟨hft, hfu⟩ := fragR_phi hfc
  have dk := deg_pos k; have da := deg_pos a
  have dy := deg_pos y
  have dt := deg_pos t; have du := deg_pos u
  simp only [Term.deg] at hbn hacm hf
  have LOW : ∀ (x w : Term), x.deg + w.deg ≤ f' →
      ltF (f' + 1) x w = true → ltF f' x w = true := by
    intro x w hxw h
    rw [ltF_stable x w f' (f' + 1) hxw (by omega)]; exact h
  have hAB : ltF f' (psi k a) (Z y) = true :=
    LOW _ _ (by simp only [Term.deg]; omega) h1
  rw [ltF_succ_Z_phi] at h2
  simp only [Bool.or_eq_true, beq_iff_eq] at h2
  rw [ltF_succ_psi_phi]
  rcases h2 with ((h3 | h3) | h3) | h3
  · have h4 : ltF f' (psi k a) t = true := by rw [← h3]; exact hAB
    simp [h4]
  · have h4 : ltF f' (psi k a) u = true := by rw [← h3]; exact hAB
    simp [h4]
  · have h4 : ltF f' (psi k a) t = true :=
      htr2 (psi k a) t hfa hft (by simp only [Term.deg]; omega) f'
        (by simp only [Term.deg]; omega) hAB h3
    simp [h4]
  · have h4 : ltF f' (psi k a) u = true :=
      htr2 (psi k a) u hfa hfu (by simp only [Term.deg]; omega) f'
        (by simp only [Term.deg]; omega) hAB h3
    simp [h4]

-- ===== [T20-T28] T27 : t27_psi_Z_psi =====
-- verdict: kimina — messages [] (clean); clean in combined snippet; axioms [propext, Quot.sound]
-- notes: ψZψ, the hardest of the eight. h2 (Zy < ψqe) can only be 2.3.9, so its guard q ≤ Zy is FALSE and h2 delivers y* < ψqe. Then h1 splits: (2.3.6) ψka ≤ y* chains to ψqe by IH_TR1 with middle y* — legal since (starF f' y).deg ≤ y.deg ≤ n — then UP; (2.3.8) k ≤ Zy, and here the goal must be emitted by 2.
theorem t27_psi_Z_psi : ∀ (k a y q e : Term) (n m f' : Nat),
    TransCase (psi k a) (Z y) (psi q e) n m f' := by
  intro k a y q e n m f'
  intro hfa hfb hfc hbn hacm hf _hA hC htr1 htr2 h1 h2
  obtain ⟨_hkR, hfk, _hfa'⟩ := fragR_psi hfa
  obtain ⟨_hqR, hfq, _hfe⟩ := fragR_psi hfc
  have hfy : FragR y = true := fragR_Z hfb
  have dk := deg_pos k; have da := deg_pos a
  have dy := deg_pos y
  have dq := deg_pos q; have de := deg_pos e
  simp only [Term.deg] at hbn hacm hf
  -- the fragment is closed under `α*` (§8.4(ii), case S1), inline
  have hstar : ∀ (g : Nat) (s : Term), FragR s = true → FragR (starF g s) = true := by
    intro g
    induction g with
    | zero => intro s _; rfl
    | succ g ih =>
      intro s hs
      cases s with
      | zero => exact rfl
      | M => exact rfl
      | psi kk aa => exact hs
      | Z aa => exact hs
      | omg aa => exact ih aa hs
      | add aa bb =>
        obtain ⟨ha', hb'⟩ := fragR_add hs
        rw [starF_succ_add]
        cases ltF g (starF g aa) (starF g bb)
        · show FragR (starF g aa) = true
          exact ih aa ha'
        · show FragR (starF g bb) = true
          exact ih bb hb'
      | phi aa bb =>
        obtain ⟨ha', hb'⟩ := fragR_phi hs
        rw [starF_succ_phi]
        cases ltF g (starF g aa) (starF g bb)
        · show FragR (starF g aa) = true
          exact ih aa ha'
        · show FragR (starF g bb) = true
          exact ih bb hb'
  have LOW : ∀ (x w : Term), x.deg + w.deg ≤ f' →
      ltF (f' + 1) x w = true → ltF f' x w = true := by
    intro x w hxw h
    rw [ltF_stable x w f' (f' + 1) hxw (by omega)]; exact h
  have UP : ∀ (x w : Term), x.deg + w.deg ≤ f' →
      ltF f' x w = true → ltF (f' + 1) x w = true := by
    intro x w hxw h
    rw [ltF_stable x w (f' + 1) f' (by omega) hxw]; exact h
  have hBC : ltF f' (Z y) (psi q e) = true :=
    LOW _ _ (by simp only [Term.deg]; omega) h2
  have hds := deg_starF f' y
  -- 2.3.9 on the right: the `κ ≤ γ` guard must have failed, or `Zy < ψqe` is false
  rw [ltF_succ_Z_psi] at h2
  by_cases hqy : (q == Z y || ltF f' q (Z y)) = true
  · rw [if_pos hqy] at h2; exact Bool.noConfusion h2
  · rw [if_neg hqy] at h2
    -- h2 : ltF f' (starF f' y) (psi q e) = true
    rw [ltF_succ_psi_Z] at h1
    by_cases hkY : (k == Z y || ltF f' k (Z y)) = true
    · -- 2.3.8 on the left: `k ≤ Zy`, and `Zy < q` because 2.3.9's guard failed
      have keyk : ∀ (w : Term), FragR w = true → k.deg + w.deg ≤ m →
          k.deg + (Z y).deg + w.deg ≤ f' → ltF f' (Z y) w = true → ltF f' k w = true := by
        intro w hw hwm hwf hzw
        simp only [Bool.or_eq_true, beq_iff_eq] at hkY
        rcases hkY with h5 | h5
        · rw [h5]; exact hzw
        · exact htr2 k w hfk hw hwm f' hwf h5 hzw
      have hZq : ltF f' (Z y) q = true := by
        rcases hC q (Z y) hfq hfb f' (by simp only [Term.deg]; omega) with h5 | h5 | h5
        · exact absurd (by simp [h5]) hqy
        · exact absurd (by simp [h5]) hqy
        · exact h5
      have hkq : ltF f' k q = true :=
        keyk q hfq (by omega) (by simp only [Term.deg]; omega) hZq
      have hkqe : ltF f' k (psi q e) = true :=
        keyk (psi q e) hfc (by simp only [Term.deg]; omega)
          (by simp only [Term.deg]; omega) hBC
      have hkqne : k ≠ q := ne_of_ltF hkq
      have hne : psi k a ≠ psi q e := by
        intro hc; injection hc with h5 _; exact hkqne h5
      rw [ltF_succ_psi_psi _ hne, if_neg hkqne, if_pos hkq]
      exact hkqe
    · -- 2.3.6 on the left: `ψka ≤ y*`, and `y* < ψqe` by 2.3.9
      rw [if_neg hkY] at h1
      simp only [Bool.or_eq_true, beq_iff_eq] at h1
      refine UP _ _ (by simp only [Term.deg]; omega) ?_
      rcases h1 with h3 | h3
      · rw [h3]; exact h2
      · exact htr1 (psi k a) (starF f' y) (psi q e) hfa (hstar f' y hfy) hfc
          (by omega) f' (by simp only [Term.deg]; omega) h3 h2

-- ===== [T20-T28] T28 : t28_psi_Z_Z =====
-- verdict: kimina — messages [] (clean); clean in combined snippet; axioms [propext, Quot.sound]
-- notes: ψZZ, the case that routes through starF on both sides. Split on h1's 2.3.8 guard first: if k ≤ Zy then k ≤ Zy < Zz gives k < Zz by IH_TR2 (middle Zy) and the goal fires its own 2.3.8 — no starF needed. Otherwise h1 gives ψka ≤ y* and h2 is 2.3.15: (i) y<z, y* < Zz, so ψka ≤ y* < Zz by IH_TR1 with mi
theorem t28_psi_Z_Z : ∀ (k a y z : Term) (n m f' : Nat),
    TransCase (psi k a) (Z y) (Z z) n m f' := by
  intro k a y z n m f'
  intro hfa hfb hfc hbn hacm hf _hA _hC htr1 htr2 h1 h2
  obtain ⟨_hkR, hfk, _hfa'⟩ := fragR_psi hfa
  have hfy : FragR y = true := fragR_Z hfb
  have hfz : FragR z = true := fragR_Z hfc
  have dk := deg_pos k; have da := deg_pos a
  have dy := deg_pos y; have dz := deg_pos z
  simp only [Term.deg] at hbn hacm hf
  -- the fragment is closed under `α*` (§8.4(ii), case S1), inline
  have hstar : ∀ (g : Nat) (s : Term), FragR s = true → FragR (starF g s) = true := by
    intro g
    induction g with
    | zero => intro s _; rfl
    | succ g ih =>
      intro s hs
      cases s with
      | zero => exact rfl
      | M => exact rfl
      | psi kk aa => exact hs
      | Z aa => exact hs
      | omg aa => exact ih aa hs
      | add aa bb =>
        obtain ⟨ha', hb'⟩ := fragR_add hs
        rw [starF_succ_add]
        cases ltF g (starF g aa) (starF g bb)
        · show FragR (starF g aa) = true
          exact ih aa ha'
        · show FragR (starF g bb) = true
          exact ih bb hb'
      | phi aa bb =>
        obtain ⟨ha', hb'⟩ := fragR_phi hs
        rw [starF_succ_phi]
        cases ltF g (starF g aa) (starF g bb)
        · show FragR (starF g aa) = true
          exact ih aa ha'
        · show FragR (starF g bb) = true
          exact ih bb hb'
  have LOW : ∀ (x w : Term), x.deg + w.deg ≤ f' →
      ltF (f' + 1) x w = true → ltF f' x w = true := by
    intro x w hxw h
    rw [ltF_stable x w f' (f' + 1) hxw (by omega)]; exact h
  have UP : ∀ (x w : Term), x.deg + w.deg ≤ f' →
      ltF f' x w = true → ltF (f' + 1) x w = true := by
    intro x w hxw h
    rw [ltF_stable x w (f' + 1) f' (by omega) hxw]; exact h
  have hAB : ltF f' (psi k a) (Z y) = true :=
    LOW _ _ (by simp only [Term.deg]; omega) h1
  have hBC : ltF f' (Z y) (Z z) = true :=
    LOW _ _ (by simp only [Term.deg]; omega) h2
  have hdsy := deg_starF f' y
  have hdsz := deg_starF f' z
  rw [ltF_succ_psi_Z] at h1
  by_cases hkY : (k == Z y || ltF f' k (Z y)) = true
  · -- 2.3.8 on the left: `k ≤ Zy < Zz`, so 2.3.8 fires for the conclusion too
    have hkz : ltF f' k (Z z) = true := by
      simp only [Bool.or_eq_true, beq_iff_eq] at hkY
      rcases hkY with h5 | h5
      · rw [h5]; exact hBC
      · exact htr2 k (Z z) hfk hfc (by simp only [Term.deg]; omega) f'
          (by simp only [Term.deg]; omega) h5 hBC
    rw [ltF_succ_psi_Z, if_pos (by simp [hkz])]
  · -- 2.3.6 on the left: `ψka ≤ y*`
    rw [if_neg hkY] at h1
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    have hne2 : Z y ≠ Z z := ne_of_ltF h2
    rw [ltF_succ_Z_Z _ hne2] at h2
    by_cases hyz : ltF f' y z = true
    · -- 2.3.15(i): `y* < Zz`, and `ψka ≤ y*`
      rw [if_pos hyz] at h2
      refine UP _ _ (by simp only [Term.deg]; omega) ?_
      rcases h1 with h3 | h3
      · rw [h3]; exact h2
      · exact htr1 (psi k a) (starF f' y) (Z z) hfa (hstar f' y hfy) hfc
          (by omega) f' (by simp only [Term.deg]; omega) h3 h2
    · -- 2.3.15(ii): `Zy ≤ z*`, and `ψka < Zy`
      rw [if_neg hyz] at h2
      simp only [Bool.or_eq_true, beq_iff_eq] at h2
      have h4 : ltF f' (psi k a) (starF f' z) = true := by
        rcases h2 with h3 | h3
        · rw [← h3]; exact hAB
        · exact htr2 (psi k a) (starF f' z) hfa (hstar f' z hfz)
            (by simp only [Term.deg]; omega) f' (by simp only [Term.deg]; omega) hAB h3
      -- PHASE B REPAIR (psiz1): the returned proof ended at `simp [h4]`, which cannot
      -- close the goal — it is at fuel `f' + 1` while `h4` lives at `f'`, so clause
      -- 2.3.6 has to be unfolded first.  Everything else in this proof is as returned.
      rw [ltF_succ_psi_Z]
      by_cases hkz : ((k == Z z) || ltF f' k (Z z)) = true
      · rw [if_pos hkz]
      · rw [if_neg hkz]; simp [h4]

-- ===== [T29-T36] T29 : c29 — Zφφ =====
-- verdict: kimina 12346: 0 errors (messages [] apart from none); also compiles in the combined 8-theorem snippet
-- notes: 2.3.4 on the left (ltF_succ_Z_phi: Zx ≤ c or Zx ≤ d) against the three branches of 2.3.13 on the right (ltF_succ_phi_phi). 13(ii) c=e: Zx ≤ c settles disjunct 1/3, Zx ≤ d goes through IH_TR1 with middle d. 13(i): Zx ≤ c uses IH_TR1 with middle c; Zx ≤ d gives Zx < φeg AT FUEL f' and is lifted by ltF
theorem c29 : ∀ (x c d e g : Term) (n m f' : Nat), TransCase (Z x) (phi c d) (phi e g) n m f' := by
  intro x c d e g n m f' hA hB hC hBn hACm hf hasym hcomp htr1 htr2 h1 h2
  have dx := deg_pos x; have dc := deg_pos c; have dd := deg_pos d
  have de := deg_pos e; have dg := deg_pos g
  have eA : (Z x).deg = 1 + x.deg := rfl
  have eB : (phi c d).deg = 1 + c.deg + d.deg := rfl
  have eC : (phi e g).deg = 1 + e.deg + g.deg := rfl
  obtain ⟨hFc, hFd⟩ := fragR_phi hB
  obtain ⟨hFe, hFg⟩ := fragR_phi hC
  have hAB : ltF f' (Z x) (phi c d) = true := by
    rw [ltF_stable (Z x) (phi c d) f' (f' + 1) (by omega) (by omega)]; exact h1
  have hBne : phi c d ≠ phi e g := ne_of_ltF h2
  rw [ltF_succ_phi_phi _ hBne] at h2
  rw [ltF_succ_Z_phi] at h1
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  by_cases hce : c = e
  · subst hce
    rw [if_pos rfl] at h2
    rw [ltF_succ_Z_phi]
    rcases h1 with ((h3 | h3) | h3) | h3
    · simp [h3]
    · have k : ltF f' (Z x) g = true := by rw [h3]; exact h2
      simp [k]
    · simp [h3]
    · have k : ltF f' (Z x) g = true :=
        htr1 (Z x) d g hA hFd hFg (by omega) f' (by omega) h3 h2
      simp [k]
  · rw [if_neg hce] at h2
    by_cases hce2 : ltF f' c e = true
    · rw [if_pos hce2] at h2
      rcases h1 with ((h3 | h3) | h3) | h3
      · rw [ltF_succ_Z_phi]
        have k : ltF f' (Z x) e = true := by rw [h3]; exact hce2
        simp [k]
      · have k : ltF f' (Z x) (phi e g) = true := by rw [h3]; exact h2
        rw [ltF_stable (Z x) (phi e g) (f' + 1) f' (by omega) (by omega)]
        exact k
      · rw [ltF_succ_Z_phi]
        have k : ltF f' (Z x) e = true :=
          htr1 (Z x) c e hA hFc hFe (by omega) f' (by omega) h3 hce2
        simp [k]
      · have k : ltF f' (Z x) (phi e g) = true :=
          htr1 (Z x) d (phi e g) hA hFd hC (by omega) f' (by omega) h3 h2
        rw [ltF_stable (Z x) (phi e g) (f' + 1) f' (by omega) (by omega)]
        exact k
    · rw [if_neg hce2] at h2
      simp only [Bool.or_eq_true, beq_iff_eq] at h2
      have k : ltF f' (Z x) g = true := by
        rcases h2 with h4 | h4
        · rw [← h4]; exact hAB
        · exact htr2 (Z x) g hA hFg (by omega) f' (by omega) hAB h4
      rw [ltF_succ_Z_phi]
      simp [k]

-- ===== [T29-T36] T30 : c30 — ZφZ =====
-- verdict: kimina 12346: 0 errors; also compiles in the combined 8-theorem snippet
-- notes: 2.3.5 on the right (ltF_succ_phi_Z) hands over BOTH components below Zz, and 2.3.4 on the left puts Zx ≤ c or ≤ d; one IH_TR1 with the matching component as middle finishes AT FUEL f', and ltF_stable lifts to f'+1 — the goal's 2.3.15 clause is never unfolded, so no starF reasoning at all. Consumes I
theorem c30 : ∀ (x c d z : Term) (n m f' : Nat), TransCase (Z x) (phi c d) (Z z) n m f' := by
  intro x c d z n m f' hA hB hC hBn hACm hf hasym hcomp htr1 htr2 h1 h2
  have dx := deg_pos x; have dc := deg_pos c; have dd := deg_pos d; have dz := deg_pos z
  have eA : (Z x).deg = 1 + x.deg := rfl
  have eB : (phi c d).deg = 1 + c.deg + d.deg := rfl
  have eC : (Z z).deg = 1 + z.deg := rfl
  obtain ⟨hFc, hFd⟩ := fragR_phi hB
  rw [ltF_succ_phi_Z] at h2
  simp only [Bool.and_eq_true] at h2
  obtain ⟨h2c, h2d⟩ := h2
  rw [ltF_succ_Z_phi] at h1
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  have key : ltF f' (Z x) (Z z) = true := by
    rcases h1 with ((h3 | h3) | h3) | h3
    · rw [h3]; exact h2c
    · rw [h3]; exact h2d
    · exact htr1 (Z x) c (Z z) hA hFc hC (by omega) f' (by omega) h3 h2c
    · exact htr1 (Z x) d (Z z) hA hFd hC (by omega) f' (by omega) h3 h2d
  rw [ltF_stable (Z x) (Z z) (f' + 1) f' (by omega) (by omega)]
  exact key

-- ===== [T29-T36] T31 : c31 — Zφψ =====
-- verdict: kimina 12346: 0 errors; also compiles in the combined 8-theorem snippet
-- notes: Literally T30 with the ψ form of 2.3.5 (ltF_succ_phi_psi); same route: 2.3.4 on the left + one IH_TR1 with middle c or d, result obtained at fuel f' and lifted by ltF_stable, so the goal's 2.3.9 clause (and its starF) is never unfolded. Asym3/Comp3/StarClosed NOT used; q.isR not consumed. Receipt: Z
theorem c31 : ∀ (x c d q e : Term) (n m f' : Nat), TransCase (Z x) (phi c d) (psi q e) n m f' := by
  intro x c d q e n m f' hA hB hC hBn hACm hf hasym hcomp htr1 htr2 h1 h2
  have dx := deg_pos x; have dc := deg_pos c; have dd := deg_pos d
  have dq := deg_pos q; have de := deg_pos e
  have eA : (Z x).deg = 1 + x.deg := rfl
  have eB : (phi c d).deg = 1 + c.deg + d.deg := rfl
  have eC : (psi q e).deg = 1 + q.deg + e.deg := rfl
  obtain ⟨hFc, hFd⟩ := fragR_phi hB
  rw [ltF_succ_phi_psi] at h2
  simp only [Bool.and_eq_true] at h2
  obtain ⟨h2c, h2d⟩ := h2
  rw [ltF_succ_Z_phi] at h1
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  have key : ltF f' (Z x) (psi q e) = true := by
    rcases h1 with ((h3 | h3) | h3) | h3
    · rw [h3]; exact h2c
    · rw [h3]; exact h2d
    · exact htr1 (Z x) c (psi q e) hA hFc hC (by omega) f' (by omega) h3 h2c
    · exact htr1 (Z x) d (psi q e) hA hFd hC (by omega) f' (by omega) h3 h2d
  rw [ltF_stable (Z x) (psi q e) (f' + 1) f' (by omega) (by omega)]
  exact key

-- ===== [T29-T36] T32 : c32 — Zψφ =====
-- verdict: kimina 12346: 0 errors; also compiles in the combined 8-theorem snippet
-- notes: 2.3.4 on the right (ltF_succ_psi_phi) gives B ≤ e or B ≤ g; A < B < (that component) is one IH_TR2 (middle stays B, z' is a proper subterm of C so A.deg+z'.deg ≤ m−1), and the conclusion is the matching disjunct of 2.3.4 for Z (ltF_succ_Z_phi). h1 is used ONLY through ltF_stable, so its 2.3.9 clause
theorem c32 : ∀ (x p b e g : Term) (n m f' : Nat), TransCase (Z x) (psi p b) (phi e g) n m f' := by
  intro x p b e g n m f' hA hB hC hBn hACm hf hasym hcomp htr1 htr2 h1 h2
  have dx := deg_pos x; have dp := deg_pos p; have db := deg_pos b
  have de := deg_pos e; have dg := deg_pos g
  have eA : (Z x).deg = 1 + x.deg := rfl
  have eB : (psi p b).deg = 1 + p.deg + b.deg := rfl
  have eC : (phi e g).deg = 1 + e.deg + g.deg := rfl
  obtain ⟨hFe, hFg⟩ := fragR_phi hC
  have hAB : ltF f' (Z x) (psi p b) = true := by
    rw [ltF_stable (Z x) (psi p b) f' (f' + 1) (by omega) (by omega)]; exact h1
  rw [ltF_succ_psi_phi] at h2
  simp only [Bool.or_eq_true, beq_iff_eq] at h2
  have key : ltF f' (Z x) e = true ∨ ltF f' (Z x) g = true := by
    rcases h2 with ((h3 | h3) | h3) | h3
    · exact Or.inl (by rw [← h3]; exact hAB)
    · exact Or.inr (by rw [← h3]; exact hAB)
    · exact Or.inl (htr2 (Z x) e hA hFe (by omega) f' (by omega) hAB h3)
    · exact Or.inr (htr2 (Z x) g hA hFg (by omega) f' (by omega) hAB h3)
  rw [ltF_succ_Z_phi]
  rcases key with k | k
  · simp [k]
  · simp [k]

-- ===== [T29-T36] T33 : c33 — Zψψ =====
-- verdict: kimina 12346: 0 errors; also compiles in the combined 8-theorem snippet
-- notes: Both halves of 2.3.9 for the goal. BODY (x* < ψπc): from h1's body x* < ψκb plus B < C, one IH_TR2 with x' = starF f' x — legal because deg_starF gives (starF f' x).deg ≤ x.deg = A.deg−1, so the degree SUM drops. GUARD (¬(π ≤ Zx)): 2.3.14 splits three ways — κ=π reuses h1's own guard verbatim (rw [←
theorem c33 : ∀ (x p b q c : Term) (n m f' : Nat), TransCase (Z x) (psi p b) (psi q c) n m f' := by
  intro x p b q c n m f' hA hB hC hBn hACm hf hasym hcomp htr1 htr2 h1 h2
  -- the fragment is closed under `α*` (§8.4's `StarClosed`), proved here in isolation
  have SC : StarClosed := by
    intro f
    induction f with
    | zero => intro t _; rfl
    | succ f ih =>
      intro t h
      cases t with
      | zero => exact rfl
      | M => exact rfl
      | psi k a => exact h
      | Z a => exact h
      | omg a => exact ih a h
      | add a b =>
        obtain ⟨ha, hb⟩ := fragR_add h
        show FragR (if ltF f (starF f a) (starF f b) then starF f b else starF f a) = true
        cases ltF f (starF f a) (starF f b)
        · show FragR (starF f a) = true
          exact ih a ha
        · show FragR (starF f b) = true
          exact ih b hb
      | phi a b =>
        obtain ⟨ha, hb⟩ := fragR_phi h
        show FragR (if ltF f (starF f a) (starF f b) then starF f b else starF f a) = true
        cases ltF f (starF f a) (starF f b)
        · show FragR (starF f a) = true
          exact ih a ha
        · show FragR (starF f b) = true
          exact ih b hb
  have dx := deg_pos x; have dp := deg_pos p; have db := deg_pos b
  have dq := deg_pos q; have dc := deg_pos c
  have eA : (Z x).deg = 1 + x.deg := rfl
  have eB : (psi p b).deg = 1 + p.deg + b.deg := rfl
  have eC : (psi q c).deg = 1 + q.deg + c.deg := rfl
  have hFx : FragR x = true := fragR_Z hA
  obtain ⟨hpR, hFp, hFb⟩ := fragR_psi hB
  obtain ⟨hqR, hFq, hFc⟩ := fragR_psi hC
  have dsx := deg_starF f' x
  have hAB : ltF f' (Z x) (psi p b) = true := by
    rw [ltF_stable (Z x) (psi p b) f' (f' + 1) (by omega) (by omega)]; exact h1
  have hBC : ltF f' (psi p b) (psi q c) = true := by
    rw [ltF_stable (psi p b) (psi q c) f' (f' + 1) (by omega) (by omega)]; exact h2
  rw [ltF_succ_Z_psi] at h1
  by_cases hp : ((p == Z x) || ltF f' p (Z x)) = true
  · rw [if_pos hp] at h1; exact Bool.noConfusion h1
  · rw [if_neg hp] at h1
    have hp1 : p ≠ Z x := fun hcc => hp (by simp [hcc])
    have hp2 : ltF f' p (Z x) ≠ true := fun hh => hp (by simp [hh])
    -- `Z x < κ`: comparability, with both alternatives excluded by the guard of 2.3.9
    have hAp : ltF f' (Z x) p = true := by
      rcases hcomp p (Z x) hFp hA f' (by omega) with k | k | k
      · exact absurd k hp2
      · exact absurd k hp1
      · exact k
    -- the body of the goal's clause: `x* < ψπc`, from `x* < ψκb < ψπc`
    have hSx : FragR (starF f' x) = true := SC f' x hFx
    have hsecond : ltF f' (starF f' x) (psi q c) = true :=
      htr2 (starF f' x) (psi q c) hSx hC (by omega) f' (by omega) h1 hBC
    -- the guard of the goal: either the two heads coincide, or `Z x < π`
    have hAq : ltF f' (Z x) q = true ∨ p = q := by
      have hne : psi p b ≠ psi q c := ne_of_ltF h2
      rw [ltF_succ_psi_psi _ hne] at h2
      by_cases hpq : p = q
      · exact Or.inr hpq
      · rw [if_neg hpq] at h2
        by_cases hpq2 : ltF f' p q = true
        · exact Or.inl (htr1 (Z x) p q hA hFp hFq (by omega) f' (by omega) hAp hpq2)
        · rw [if_neg hpq2] at h2
          exact Or.inl (htr2 (Z x) q hA hFq (by omega) f' (by omega) hAB h2)
    have hcond : ¬ (((q == Z x) || ltF f' q (Z x)) = true) := by
      rcases hAq with k | k
      · have hqx : ltF f' q (Z x) = false := hasym (Z x) q hA hFq f' (by omega) k
        have hqne : q ≠ Z x := fun hcc => (ne_of_ltF k) hcc.symm
        simp [hqx, hqne]
      · rw [← k]; exact hp
    rw [ltF_succ_Z_psi, if_neg hcond]
    exact hsecond

-- ===== [T29-T36] T34 : c34 — ZψZ =====
-- verdict: kimina 12346: 0 errors; also compiles in the combined 8-theorem snippet
-- notes: The one case where the goal is 2.3.15. Split on 2.3.8's guard in h2. GUARD TRUE (κ ≤ Zz): Comp3 turns h1's guard into Zx < κ, IH_TR1 with middle κ (proper subterm of B) gives Zx < Zz AT FUEL f', lifted by ltF_stable — 2.3.15 is never unfolded, which is what avoids having to compare x with z. GUARD F
theorem c34 : ∀ (x p b z : Term) (n m f' : Nat), TransCase (Z x) (psi p b) (Z z) n m f' := by
  intro x p b z n m f' hA hB hC hBn hACm hf hasym hcomp htr1 htr2 h1 h2
  -- the fragment is closed under `α*` (§8.4's `StarClosed`), proved here in isolation
  have SC : StarClosed := by
    intro f
    induction f with
    | zero => intro t _; rfl
    | succ f ih =>
      intro t h
      cases t with
      | zero => exact rfl
      | M => exact rfl
      | psi k a => exact h
      | Z a => exact h
      | omg a => exact ih a h
      | add a b =>
        obtain ⟨ha, hb⟩ := fragR_add h
        show FragR (if ltF f (starF f a) (starF f b) then starF f b else starF f a) = true
        cases ltF f (starF f a) (starF f b)
        · show FragR (starF f a) = true
          exact ih a ha
        · show FragR (starF f b) = true
          exact ih b hb
      | phi a b =>
        obtain ⟨ha, hb⟩ := fragR_phi h
        show FragR (if ltF f (starF f a) (starF f b) then starF f b else starF f a) = true
        cases ltF f (starF f a) (starF f b)
        · show FragR (starF f a) = true
          exact ih a ha
        · show FragR (starF f b) = true
          exact ih b hb
  have dx := deg_pos x; have dp := deg_pos p; have db := deg_pos b; have dz := deg_pos z
  have eA : (Z x).deg = 1 + x.deg := rfl
  have eB : (psi p b).deg = 1 + p.deg + b.deg := rfl
  have eC : (Z z).deg = 1 + z.deg := rfl
  have hFx : FragR x = true := fragR_Z hA
  have hFz : FragR z = true := fragR_Z hC
  obtain ⟨hpR, hFp, hFb⟩ := fragR_psi hB
  have dsx := deg_starF f' x
  have dsz := deg_starF f' z
  have hAB : ltF f' (Z x) (psi p b) = true := by
    rw [ltF_stable (Z x) (psi p b) f' (f' + 1) (by omega) (by omega)]; exact h1
  have hBC : ltF f' (psi p b) (Z z) = true := by
    rw [ltF_stable (psi p b) (Z z) f' (f' + 1) (by omega) (by omega)]; exact h2
  have hac : Z x ≠ Z z := by
    intro hcc
    rw [hcc] at hAB
    rw [hasym (Z z) (psi p b) hC hB f' (by omega) hAB] at hBC
    exact Bool.noConfusion hBC
  rw [ltF_succ_Z_psi] at h1
  by_cases hp : ((p == Z x) || ltF f' p (Z x)) = true
  · rw [if_pos hp] at h1; exact Bool.noConfusion h1
  · rw [if_neg hp] at h1
    have hp1 : p ≠ Z x := fun hcc => hp (by simp [hcc])
    have hp2 : ltF f' p (Z x) ≠ true := fun hh => hp (by simp [hh])
    -- `Z x < κ`: comparability, with both alternatives excluded by the guard of 2.3.9
    have hAp : ltF f' (Z x) p = true := by
      rcases hcomp p (Z x) hFp hA f' (by omega) with k | k | k
      · exact absurd k hp2
      · exact absurd k hp1
      · exact k
    rw [ltF_succ_psi_Z] at h2
    by_cases hpz : ((p == Z z) || ltF f' p (Z z)) = true
    · -- 2.3.8 on the right: `Z x < κ ≤ Z z`, so the conclusion needs no clause at all
      have k : ltF f' (Z x) (Z z) = true := by
        simp only [Bool.or_eq_true, beq_iff_eq] at hpz
        rcases hpz with h3 | h3
        · rw [← h3]; exact hAp
        · exact htr1 (Z x) p (Z z) hA hFp hC (by omega) f' (by omega) hAp h3
      rw [ltF_stable (Z x) (Z z) (f' + 1) f' (by omega) (by omega)]
      exact k
    · -- 2.3.6 on the right: `ψκb ≤ z*`
      rw [if_neg hpz] at h2
      rw [ltF_succ_Z_Z _ hac]
      by_cases hxz : ltF f' x z = true
      · -- 15(i): `x* < ψκb < Z z`
        rw [if_pos hxz]
        have hSx : FragR (starF f' x) = true := SC f' x hFx
        exact htr2 (starF f' x) (Z z) hSx hC (by omega) f' (by omega) h1 hBC
      · -- 15(ii): `Z x < ψκb ≤ z*`
        rw [if_neg hxz]
        have hSz : FragR (starF f' z) = true := SC f' z hFz
        simp only [Bool.or_eq_true, beq_iff_eq] at h2
        have k : ltF f' (Z x) (starF f' z) = true := by
          rcases h2 with h3 | h3
          · rw [← h3]; exact hAB
          · exact htr2 (Z x) (starF f' z) hA hSz (by omega) f' (by omega) hAB h3
        simp [k]

-- ===== [T29-T36] T35 : c35 — ZZφ =====
-- verdict: kimina 12346: 0 errors; also compiles in the combined 8-theorem snippet
-- notes: Same route as T32 with B = Z y: 2.3.4 on the right gives B ≤ e or B ≤ g, one IH_TR2 (middle B, z' a proper subterm of C) yields the matching disjunct of 2.3.4 on the left. h1's 2.3.15 clause is used only through ltF_stable, so no starF appears. Asym3/Comp3/StarClosed NOT used. Receipt: Z0 < Z(Z0) < 
theorem c35 : ∀ (x y e g : Term) (n m f' : Nat), TransCase (Z x) (Z y) (phi e g) n m f' := by
  intro x y e g n m f' hA hB hC hBn hACm hf hasym hcomp htr1 htr2 h1 h2
  have dx := deg_pos x; have dy := deg_pos y
  have de := deg_pos e; have dg := deg_pos g
  have eA : (Z x).deg = 1 + x.deg := rfl
  have eB : (Z y).deg = 1 + y.deg := rfl
  have eC : (phi e g).deg = 1 + e.deg + g.deg := rfl
  obtain ⟨hFe, hFg⟩ := fragR_phi hC
  have hAB : ltF f' (Z x) (Z y) = true := by
    rw [ltF_stable (Z x) (Z y) f' (f' + 1) (by omega) (by omega)]; exact h1
  rw [ltF_succ_Z_phi] at h2
  simp only [Bool.or_eq_true, beq_iff_eq] at h2
  have key : ltF f' (Z x) e = true ∨ ltF f' (Z x) g = true := by
    rcases h2 with ((h3 | h3) | h3) | h3
    · exact Or.inl (by rw [← h3]; exact hAB)
    · exact Or.inr (by rw [← h3]; exact hAB)
    · exact Or.inl (htr2 (Z x) e hA hFe (by omega) f' (by omega) hAB h3)
    · exact Or.inr (htr2 (Z x) g hA hFg (by omega) f' (by omega) hAB h3)
  rw [ltF_succ_Z_phi]
  rcases key with k | k
  · simp [k]
  · simp [k]

-- ===== [T29-T36] T36 : c36 — ZZψ =====
-- verdict: kimina 12346: 0 errors; also compiles in the combined 8-theorem snippet
-- notes: GUARD of the goal (¬(π ≤ Zx)) is proved WITHOUT transitivity through A: h2's own guard plus Comp3 give Zy < π, then IH_TR2 with z' = π (proper subterm of C) gives Zx < π, and Asym3 + ne_of_ltF close it. BODY: split h1 by 2.3.15. 15(i) (x* < Zy): IH_TR2 with x' = starF f' x, z' = C gives exactly the 
theorem c36 : ∀ (x y q c : Term) (n m f' : Nat), TransCase (Z x) (Z y) (psi q c) n m f' := by
  intro x y q c n m f' hA hB hC hBn hACm hf hasym hcomp htr1 htr2 h1 h2
  -- the fragment is closed under `α*` (§8.4's `StarClosed`), proved here in isolation
  have SC : StarClosed := by
    intro f
    induction f with
    | zero => intro t _; rfl
    | succ f ih =>
      intro t h
      cases t with
      | zero => exact rfl
      | M => exact rfl
      | psi k a => exact h
      | Z a => exact h
      | omg a => exact ih a h
      | add a b =>
        obtain ⟨ha, hb⟩ := fragR_add h
        show FragR (if ltF f (starF f a) (starF f b) then starF f b else starF f a) = true
        cases ltF f (starF f a) (starF f b)
        · show FragR (starF f a) = true
          exact ih a ha
        · show FragR (starF f b) = true
          exact ih b hb
      | phi a b =>
        obtain ⟨ha, hb⟩ := fragR_phi h
        show FragR (if ltF f (starF f a) (starF f b) then starF f b else starF f a) = true
        cases ltF f (starF f a) (starF f b)
        · show FragR (starF f a) = true
          exact ih a ha
        · show FragR (starF f b) = true
          exact ih b hb
  have dx := deg_pos x; have dy := deg_pos y; have dq := deg_pos q; have dc := deg_pos c
  have eA : (Z x).deg = 1 + x.deg := rfl
  have eB : (Z y).deg = 1 + y.deg := rfl
  have eC : (psi q c).deg = 1 + q.deg + c.deg := rfl
  have hFx : FragR x = true := fragR_Z hA
  have hFy : FragR y = true := fragR_Z hB
  obtain ⟨hqR, hFq, hFc⟩ := fragR_psi hC
  have dsx := deg_starF f' x
  have dsy := deg_starF f' y
  have hAB : ltF f' (Z x) (Z y) = true := by
    rw [ltF_stable (Z x) (Z y) f' (f' + 1) (by omega) (by omega)]; exact h1
  have hBC : ltF f' (Z y) (psi q c) = true := by
    rw [ltF_stable (Z y) (psi q c) f' (f' + 1) (by omega) (by omega)]; exact h2
  rw [ltF_succ_Z_psi] at h2
  by_cases hq : ((q == Z y) || ltF f' q (Z y)) = true
  · rw [if_pos hq] at h2; exact Bool.noConfusion h2
  · rw [if_neg hq] at h2
    have hq1 : q ≠ Z y := fun hcc => hq (by simp [hcc])
    have hq2 : ltF f' q (Z y) ≠ true := fun hh => hq (by simp [hh])
    -- `Z y < q`: comparability, with both alternatives excluded by the guard
    have hByq : ltF f' (Z y) q = true := by
      rcases hcomp q (Z y) hFq hB f' (by omega) with k | k | k
      · exact absurd k hq2
      · exact absurd k hq1
      · exact k
    have hAq : ltF f' (Z x) q = true :=
      htr2 (Z x) q hA hFq (by omega) f' (by omega) hAB hByq
    have hqx : ltF f' q (Z x) = false := hasym (Z x) q hA hFq f' (by omega) hAq
    have hqne : q ≠ Z x := fun hcc => (ne_of_ltF hAq) hcc.symm
    have hcond : ¬ (((q == Z x) || ltF f' q (Z x)) = true) := by simp [hqx, hqne]
    have hxy : Z x ≠ Z y := ne_of_ltF h1
    rw [ltF_succ_Z_Z _ hxy] at h1
    by_cases hxy2 : ltF f' x y = true
    · rw [if_pos hxy2] at h1
      have hSx : FragR (starF f' x) = true := SC f' x hFx
      have k : ltF f' (starF f' x) (psi q c) = true :=
        htr2 (starF f' x) (psi q c) hSx hC (by omega) f' (by omega) h1 hBC
      rw [ltF_succ_Z_psi, if_neg hcond]
      exact k
    · rw [if_neg hxy2] at h1
      have hSy : FragR (starF f' y) = true := SC f' y hFy
      simp only [Bool.or_eq_true, beq_iff_eq] at h1
      have k : ltF f' (Z x) (psi q c) = true := by
        rcases h1 with h3 | h3
        · rw [h3]; exact h2
        · exact htr1 (Z x) (starF f' y) (psi q c) hA hSy hC (by omega) f' (by omega) h3 h2
      rw [ltF_stable (Z x) (psi q c) (f' + 1) f' (by omega) (by omega)]
      exact k

-- ===== [T24-hard] T24 : ψ/ψ/ψ — three applications of 2.3.14 (§8.4 STAGE II; §8.4.2 lists this shape as "CASE T-14") =====
-- verdict: kimina http://localhost:12346/api/check — {"id":"t24-final","response":{"env":10}} : NO messages at all (not even a linter warning). Separate POST: `#print axioms t24` → 't24' depends on axioms: [prop
-- notes: SHAPE OF THE PROOF (9 leaves = 3 sub-clauses of 2.3.14 for A<B  x  3 for B<C). Write A = psi k a, B = psi p b, C = psi q c; L1/L2/L3 = which sub-clause decides A<B (L1 = 14(ii) k=p, L2 = 14(i) k<p, L3 = 14(iii) otherwise), R1/R2/R3 likewise for B<C.   L1R1 (k=p=q): goal is 14(ii); IH_TR1 a b c throu


/-- **CASE T24 (ψ/ψ/ψ)** of §8.4 — three applications of 2.3.14.  The analogue of
    §7.4's case (8), one level up. -/
theorem t24 : ∀ (k a p b q c : Term) (n m f' : Nat),
    TransCase (psi k a) (psi p b) (psi q c) n m f' := by
  intro k a p b q c n m f' hA hB hC hBn hACm hf ASYM COMP TR1 TR2 h1 h2
  obtain ⟨_, hFk, hFa⟩ := fragR_psi hA
  obtain ⟨_, hFp, hFb⟩ := fragR_psi hB
  obtain ⟨_, hFq, hFc⟩ := fragR_psi hC
  have dk := deg_pos k; have da := deg_pos a
  have dp := deg_pos p; have db := deg_pos b
  have dq := deg_pos q; have dc := deg_pos c
  have eA : (psi k a).deg = 1 + k.deg + a.deg := rfl
  have eB : (psi p b).deg = 1 + p.deg + b.deg := rfl
  have eC : (psi q c).deg = 1 + q.deg + c.deg := rfl
  -- the two hypotheses, moved down to the fuel the clause bodies hand out (§5)
  have hAB : ltF f' (psi k a) (psi p b) = true := ltF_mono (by omega) (by omega) h1
  have hBC : ltF f' (psi p b) (psi q c) = true := ltF_mono (by omega) (by omega) h2
  have hne1 : psi k a ≠ psi p b := ne_of_ltF h1
  have hne2 : psi p b ≠ psi q c := ne_of_ltF h2
  have hac : psi k a ≠ psi q c := by
    intro hcon
    rw [hcon] at h1
    rw [ASYM _ _ hC hB (f' + 1) (by omega) h1] at h2
    exact Bool.noConfusion h2
  rw [ltF_succ_psi_psi _ hne1] at h1
  rw [ltF_succ_psi_psi _ hne2] at h2
  by_cases hkp : k = p
  · -- 14(ii) on the left: κ = π
    subst hkp
    rw [if_pos rfl] at h1
    by_cases hkq : k = q
    · subst hkq
      rw [if_pos rfl] at h2
      rw [ltF_succ_psi_psi _ hac, if_pos rfl]
      exact TR1 a b c hFa hFb hFc (by omega) f' (by omega) h1 h2
    · rw [if_neg hkq] at h2
      by_cases hkq2 : ltF f' k q = true
      · rw [if_pos hkq2] at h2
        rw [ltF_succ_psi_psi _ hac, if_neg hkq, if_pos hkq2]
        exact h2
      · rw [if_neg hkq2] at h2
        rw [ltF_succ_psi_psi _ hac, if_neg hkq, if_neg hkq2]
        exact TR2 (psi k a) q hA hFq (by omega) f' (by omega) hAB h2
  · rw [if_neg hkp] at h1
    by_cases hkp2 : ltF f' k p = true
    · -- 14(i) on the left: κ < π, and then κ < ψπβ carries everything
      rw [if_pos hkp2] at h1
      have hkC : ltF f' k (psi q c) = true :=
        TR2 k (psi q c) hFk hC (by omega) f' (by omega) h1 hBC
      have hkq : ltF f' k q = true := by
        by_cases hpq : p = q
        · subst hpq; exact hkp2
        · rw [if_neg hpq] at h2
          by_cases hpq2 : ltF f' p q = true
          · rw [if_pos hpq2] at h2
            exact TR1 k p q hFk hFp hFq (by omega) f' (by omega) hkp2 hpq2
          · rw [if_neg hpq2] at h2
            exact TR2 k q hFk hFq (by omega) f' (by omega) h1 h2
      rw [ltF_succ_psi_psi _ hac, if_neg (ne_of_ltF hkq), if_pos hkq]
      exact hkC
    · -- 14(iii) on the left: π < κ and ψκα < π
      rw [if_neg hkp2] at h1
      by_cases hpq : p = q
      · subst hpq
        rw [ltF_succ_psi_psi _ hac, if_neg hkp, if_neg hkp2]
        exact h1
      · rw [if_neg hpq] at h2
        by_cases hpq2 : ltF f' p q = true
        · -- ψκα < π < ψπ'γ: no branch analysis at all
          rw [if_pos hpq2] at h2
          have hACf : ltF f' (psi k a) (psi q c) = true :=
            TR1 (psi k a) p (psi q c) hA hFp hC (by omega) f' (by omega) h1 h2
          exact ltF_mono (by omega) (by omega) hACf
        · rw [if_neg hpq2] at h2
          have hpk : ltF f' p k = true := by
            rcases COMP k p hFk hFp f' (by omega) with h | h | h
            · exact absurd h hkp2
            · exact absurd h hkp
            · exact h
          have hqp : ltF f' q p = true := by
            rcases COMP p q hFp hFq f' (by omega) with h | h | h
            · exact absurd h hpq2
            · exact absurd h hpq
            · exact h
          have hqk : ltF f' q k = true :=
            TR1 q p k hFq hFp hFk (by omega) f' (by omega) hqp hpk
          have hkq : k ≠ q := by
            intro hcon; rw [hcon, ltF_irrefl] at hqk; exact Bool.noConfusion hqk
          have hkq2 : ltF f' k q = false := ASYM q k hFq hFk f' (by omega) hqk
          rw [ltF_succ_psi_psi _ hac, if_neg hkq, if_neg (by simp [hkq2])]
          exact TR2 (psi k a) q hA hFq (by omega) f' (by omega) hAB h2

-- ===== [T37-hard] T37 : t37_Z_Z_Z =====
-- verdict: kimina http://localhost:12346/api/check — messages [] (0 errors, 0 warnings), time 0.31s; re-run twice with identical result. `#print axioms t37_Z_Z_Z` → `[propext, Quot.sound]` (no sorryAx).
-- notes: PROVED, first compile, no retries. The exact snippet verified is the two prescribed header lines (`import Evidence.WF` / `open TM TM.Term Evidence.WF`) followed verbatim by the `source` field; it is on disk at /tmp/claude-1000/t37/t37.lean (92 lines) and defines nothing of its own. S1 is taken as th
theorem t37_Z_Z_Z (hS1 : StarClosed) :
    ∀ (x y z : Term) (n m f' : Nat), TransCase (Z x) (Z y) (Z z) n m f' := by
  intro x y z n m f'
  intro hfa hfb hfc hb hm hf hasym hcomp hTR1 hTR2 h1 h2
  have hx : FragR x = true := fragR_Z hfa
  have hy : FragR y = true := fragR_Z hfb
  have hz : FragR z = true := fragR_Z hfc
  have dx := deg_pos x
  have dy := deg_pos y
  have dz := deg_pos z
  have dsx := deg_starF f' x
  have dsy := deg_starF f' y
  have dsz := deg_starF f' z
  simp only [Term.deg] at hb hm hf
  have LOW : ∀ (u v : Term), u.deg + v.deg ≤ f' →
      ltF (f' + 1) u v = true → ltF f' u v = true := by
    intro u v huv h
    rw [ltF_stable u v f' (f' + 1) huv (by omega)]; exact h
  have UP : ∀ (u v : Term), u.deg + v.deg ≤ f' →
      ltF f' u v = true → ltF (f' + 1) u v = true := by
    intro u v huv h
    rw [ltF_stable u v (f' + 1) f' (by omega) huv]; exact h
  have hne1 : Z x ≠ Z y := ne_of_ltF h1
  have hne2 : Z y ≠ Z z := ne_of_ltF h2
  have hne3 : Z x ≠ Z z := by
    intro hc
    have hcon := hasym (Z x) (Z y) hfa hfb (f' + 1) (by simp only [Term.deg]; omega) h1
    rw [hc] at hcon
    rw [hcon] at h2
    exact Bool.noConfusion h2
  have hAB : ltF f' (Z x) (Z y) = true := LOW _ _ (by simp only [Term.deg]; omega) h1
  have hBC : ltF f' (Z y) (Z z) = true := LOW _ _ (by simp only [Term.deg]; omega) h2
  -- the shared ending of the two 15(ii) branches: `Zx < Zy ≤ γ*` gives `Zx ≤ γ*`
  have KEY : ((Z y == starF f' z) || ltF f' (Z y) (starF f' z)) = true →
      ((Z x == starF f' z) || ltF f' (Z x) (starF f' z)) = true := by
    intro h
    simp only [Bool.or_eq_true, beq_iff_eq] at h ⊢
    rcases h with h3 | h3
    · exact Or.inr (by rw [← h3]; exact hAB)
    · exact Or.inr (hTR2 (Z x) (starF f' z) hfa (hS1 f' z hz)
        (by simp only [Term.deg]; omega) f' (by simp only [Term.deg]; omega) hAB h3)
  rw [ltF_succ_Z_Z _ hne1] at h1
  rw [ltF_succ_Z_Z _ hne2] at h2
  by_cases hP : ltF f' x y = true
  · -- 15(i) on the left: `α < β` and `α* < Zβ`
    rw [if_pos hP] at h1
    -- the first pass through `starF`: `α* < Zβ < Zγ`, middle `Zβ` unchanged
    have hstar : ltF f' (starF f' x) (Z z) = true :=
      hTR2 (starF f' x) (Z z) (hS1 f' x hx) hfc
        (by simp only [Term.deg]; omega) f' (by simp only [Term.deg]; omega) h1 hBC
    by_cases hR : ltF f' x z = true
    · rw [ltF_succ_Z_Z _ hne3, if_pos hR]
      exact hstar
    · rw [ltF_succ_Z_Z _ hne3, if_neg hR]
      have hQ : ¬ (ltF f' y z = true) := fun hq =>
        hR (hTR1 x y z hx hy hz (by omega) f' (by omega) hP hq)
      rw [if_neg hQ] at h2
      exact KEY h2
  · -- 15(ii) on the left: `Zα ≤ β*`
    rw [if_neg hP] at h1
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    by_cases hQ : ltF f' y z = true
    · -- 15(i) on the right: `β* < Zγ`.  `Zα ≤ β* < Zγ` composes with MIDDLE `β*`,
      -- which is legal for IH_TR1 because `deg_starF` keeps `β*.deg ≤ β.deg ≤ n`.
      rw [if_pos hQ] at h2
      have h4 : ltF f' (Z x) (Z z) = true := by
        rcases h1 with h3 | h3
        · rw [h3]; exact h2
        · exact hTR1 (Z x) (starF f' y) (Z z) hfa (hS1 f' y hy) hfc
            (by omega) f' (by simp only [Term.deg]; omega) h3 h2
      exact UP (Z x) (Z z) (by simp only [Term.deg]; omega) h4
    · -- neither: comparability turns `¬(α<β)`, `¬(β<γ)` into `γ < β < α`, so `¬(α<γ)`
      rw [if_neg hQ] at h2
      have hyx : ltF f' y x = true := by
        rcases hcomp x y hx hy f' (by omega) with h3 | h3 | h3
        · exact absurd h3 hP
        · exact absurd (by rw [h3]) hne1
        · exact h3
      have hzy : ltF f' z y = true := by
        rcases hcomp y z hy hz f' (by omega) with h3 | h3 | h3
        · exact absurd h3 hQ
        · exact absurd (by rw [h3]) hne2
        · exact h3
      have hzx : ltF f' z x = true :=
        hTR1 z y x hz hy hx (by omega) f' (by omega) hzy hyx
      have hxz : ltF f' x z = false := hasym z x hz hx f' (by omega) hzx
      have hR : ¬ (ltF f' x z = true) := by rw [hxz]; exact fun hc => Bool.noConfusion hc
      rw [ltF_succ_Z_Z _ hne3, if_neg hR]
      exact KEY h2

/-! #### §8.5.2 Assembly: closing `cmp_aux3` and `trans_aux3`

The case lemmas above are stated so that the two inductions are pure dispatch.  What
is left is exactly the routing: the three-way split `0` / sum / non-sum, and inside
the non-sums the level analysis of §8.4(iv).  `cmp_aux3_skeleton` already does
Stage I's routing down to the same-level non-sum pairs; `SA_all` / `SC_all` supply
those, and `trans_aux3` below does Stage II's routing in the same style. -/

/-- `CompCase` is symmetric up to `Or.symm`.  The fan-out returned one orientation
    for the `φ̄`-vs-`ψ` and `φ̄`-vs-`Z` pairs; this supplies the other. -/
theorem compCase_symm {A B : Term} {n f' : Nat} (h : CompCase A B n f') :
    CompCase B A n f' := by
  intro hB hA hd hnf IHa IHc hne
  exact (h hA hB (by omega) hnf IHa IHc (Ne.symm hne)).symm

/-! The level classifiers: a non-zero non-sum of `FragR` is `M` at level 2, an `ω̄`
    at level 3, and one of `φ̄` / `ψ` / `Z` at level 1.  Splitting by LEVEL first is
    what keeps the all-non-sum dispatch at 27 shape triples instead of 125. -/

private theorem fragR_lvl2_eq {t : Term} (h : FragR t = true) (h0 : t ≠ zero)
    (hn : NSum t = true) (hl : lvl t = 2) : t = M := by
  rcases fragR_nsum_cases h h0 hn with rfl | ⟨x, rfl, _⟩ | ⟨x, y, rfl, _, _⟩
    | ⟨k, x, rfl, _, _, _⟩ | ⟨x, rfl, _⟩
  · rfl
  · simp [lvl] at hl
  · simp [lvl] at hl
  · simp [lvl] at hl
  · simp [lvl] at hl

private theorem fragR_lvl3_cases {t : Term} (h : FragR t = true) (h0 : t ≠ zero)
    (hn : NSum t = true) (hl : lvl t = 3) : ∃ x, t = omg x ∧ FragR x = true := by
  rcases fragR_nsum_cases h h0 hn with rfl | ⟨x, rfl, hx⟩ | ⟨x, y, rfl, _, _⟩
    | ⟨k, x, rfl, _, _, _⟩ | ⟨x, rfl, _⟩
  · simp [lvl] at hl
  · exact ⟨x, rfl, hx⟩
  · simp [lvl] at hl
  · simp [lvl] at hl
  · simp [lvl] at hl

private theorem fragR_lvl1_cases {t : Term} (h : FragR t = true) (h0 : t ≠ zero)
    (hn : NSum t = true) (hl : lvl t = 1) :
    (∃ x y, t = phi x y ∧ FragR x = true ∧ FragR y = true)
    ∨ (∃ k x, t = psi k x ∧ k.isR = true ∧ FragR k = true ∧ FragR x = true)
    ∨ (∃ x, t = Z x ∧ FragR x = true) := by
  rcases fragR_nsum_cases h h0 hn with rfl | ⟨x, rfl, _⟩ | hp | hp | hp
  · simp [lvl] at hl
  · simp [lvl] at hl
  · exact Or.inl hp
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr hp)

/-! `SA_all` / `SC_all`: the same-level non-sum pairs, which is all
    `cmp_aux3_skeleton` still needs.  Of the 25 shape pairs, 14 are killed by the
    level equality and the remaining 11 are the case lemmas A6–A13 / C6–C13. -/

private theorem SA_all : ∀ (x y : Term) (n f' : Nat), x ≠ zero → y ≠ zero →
    NSum x = true → NSum y = true → lvl x = lvl y → AsymCase x y n f' := by
  intro x y n f' hx0 hy0 hnx hny hlv hfx hfy hd hnf IHa IHc h
  rcases fragR_nsum_cases hfx hx0 hnx with rfl | ⟨u, rfl, hfu⟩ | ⟨u, v, rfl, hfu, hfv⟩
    | ⟨k, u, rfl, hkR, hfk, hfu⟩ | ⟨u, rfl, hfu⟩
  · rcases fragR_nsum_cases hfy hy0 hny with rfl | ⟨w, rfl, _⟩ | ⟨w, z, rfl, _, _⟩
      | ⟨j, w, rfl, _, _, _⟩ | ⟨w, rfl, _⟩
    · exact a6 n f' hfx hfy hd hnf IHa IHc h
    · simp [lvl] at hlv
    · simp [lvl] at hlv
    · simp [lvl] at hlv
    · simp [lvl] at hlv
  · rcases fragR_nsum_cases hfy hy0 hny with rfl | ⟨w, rfl, _⟩ | ⟨w, z, rfl, _, _⟩
      | ⟨j, w, rfl, _, _, _⟩ | ⟨w, rfl, _⟩
    · simp [lvl] at hlv
    · exact a7 u w n f' hfx hfy hd hnf IHa IHc h
    · simp [lvl] at hlv
    · simp [lvl] at hlv
    · simp [lvl] at hlv
  · rcases fragR_nsum_cases hfy hy0 hny with rfl | ⟨w, rfl, _⟩ | ⟨w, z, rfl, _, _⟩
      | ⟨j, w, rfl, _, _, _⟩ | ⟨w, rfl, _⟩
    · simp [lvl] at hlv
    · simp [lvl] at hlv
    · exact a8 u v w z n f' hfx hfy hd hnf IHa IHc h
    · exact a9_phi_psi u v j w n f' hfx hfy hd hnf IHa IHc h
    · exact a10_phi_Z u v w n f' hfx hfy hd hnf IHa IHc h
  · rcases fragR_nsum_cases hfy hy0 hny with rfl | ⟨w, rfl, _⟩ | ⟨w, z, rfl, _, _⟩
      | ⟨j, w, rfl, _, _, _⟩ | ⟨w, rfl, _⟩
    · simp [lvl] at hlv
    · simp [lvl] at hlv
    · exact a9_psi_phi k u w z n f' hfx hfy hd hnf IHa IHc h
    · exact a11 k u j w n f' hfx hfy hd hnf IHa IHc h
    · exact a12 k u w n f' starClosed hfx hfy hd hnf IHa IHc h
  · rcases fragR_nsum_cases hfy hy0 hny with rfl | ⟨w, rfl, _⟩ | ⟨w, z, rfl, _, _⟩
      | ⟨j, w, rfl, _, _, _⟩ | ⟨w, rfl, _⟩
    · simp [lvl] at hlv
    · simp [lvl] at hlv
    · exact a10_Z_phi u w z n f' hfx hfy hd hnf IHa IHc h
    · exact a21 u j w n f' starClosed hfx hfy hd hnf IHa IHc h
    · exact a13 u w n f' starClosed hfx hfy hd hnf IHa IHc h

private theorem SC_all : ∀ (x y : Term) (n f' : Nat), x ≠ zero → y ≠ zero →
    NSum x = true → NSum y = true → lvl x = lvl y → CompCase x y n f' := by
  intro x y n f' hx0 hy0 hnx hny hlv hfx hfy hd hnf IHa IHc hne
  rcases fragR_nsum_cases hfx hx0 hnx with rfl | ⟨u, rfl, hfu⟩ | ⟨u, v, rfl, hfu, hfv⟩
    | ⟨k, u, rfl, hkR, hfk, hfu⟩ | ⟨u, rfl, hfu⟩
  · rcases fragR_nsum_cases hfy hy0 hny with rfl | ⟨w, rfl, _⟩ | ⟨w, z, rfl, _, _⟩
      | ⟨j, w, rfl, _, _, _⟩ | ⟨w, rfl, _⟩
    · exact c6 n f' hfx hfy hd hnf IHa IHc hne
    · simp [lvl] at hlv
    · simp [lvl] at hlv
    · simp [lvl] at hlv
    · simp [lvl] at hlv
  · rcases fragR_nsum_cases hfy hy0 hny with rfl | ⟨w, rfl, _⟩ | ⟨w, z, rfl, _, _⟩
      | ⟨j, w, rfl, _, _, _⟩ | ⟨w, rfl, _⟩
    · simp [lvl] at hlv
    · exact c7 u w n f' hfx hfy hd hnf IHa IHc hne
    · simp [lvl] at hlv
    · simp [lvl] at hlv
    · simp [lvl] at hlv
  · rcases fragR_nsum_cases hfy hy0 hny with rfl | ⟨w, rfl, _⟩ | ⟨w, z, rfl, _, _⟩
      | ⟨j, w, rfl, _, _, _⟩ | ⟨w, rfl, _⟩
    · simp [lvl] at hlv
    · simp [lvl] at hlv
    · exact c8 u v w z n f' hfx hfy hd hnf IHa IHc hne
    · exact c9 u v j w n f' hfx hfy hd hnf IHa IHc hne
    · exact c10 u v w n f' hfx hfy hd hnf IHa IHc hne
  · rcases fragR_nsum_cases hfy hy0 hny with rfl | ⟨w, rfl, _⟩ | ⟨w, z, rfl, _, _⟩
      | ⟨j, w, rfl, _, _, _⟩ | ⟨w, rfl, _⟩
    · simp [lvl] at hlv
    · simp [lvl] at hlv
    · exact compCase_symm (c9 w z k u n f') hfx hfy hd hnf IHa IHc hne
    · exact c11 k u j w n f' hfx hfy hd hnf IHa IHc hne
    · exact c12 k u w n f' starClosed hfx hfy hd hnf IHa IHc hne
  · rcases fragR_nsum_cases hfy hy0 hny with rfl | ⟨w, rfl, _⟩ | ⟨w, z, rfl, _, _⟩
      | ⟨j, w, rfl, _, _, _⟩ | ⟨w, rfl, _⟩
    · simp [lvl] at hlv
    · simp [lvl] at hlv
    · exact compCase_symm (c10 w z u n f') hfx hfy hd hnf IHa IHc hne
    · exact c21 u j w n f' starClosed hfx hfy hd hnf IHa IHc hne
    · exact c13 u w n f' starClosed hfx hfy hd hnf IHa IHc hne

/-- **STAGE I, closed.**  Asymmetry and comparability on `FragR`, simultaneously,
    by induction on `a.deg + b.deg` — §7.3's shape, as §8.4(ii) predicted. -/
private theorem cmp_aux3 : ∀ (n : Nat),
    (∀ (a b : Term), FragR a = true → FragR b = true → a.deg + b.deg ≤ n →
      ∀ f, n ≤ f → ltF f a b = true → ltF f b a = false)
  ∧ (∀ (a b : Term), FragR a = true → FragR b = true → a.deg + b.deg ≤ n →
      ∀ f, n ≤ f → (ltF f a b = true ∨ a = b ∨ ltF f b a = true)) :=
  cmp_aux3_skeleton SA_all SC_all

/-- **ASYMMETRY on `FragR`**, same fuel. -/
theorem ltF_asymm3 {a b : Term} (hfa : FragR a = true) (hfb : FragR b = true)
    {f : Nat} (hf : a.deg + b.deg ≤ f) (h : ltF f a b = true) : ltF f b a = false :=
  (cmp_aux3 (a.deg + b.deg)).1 a b hfa hfb (Nat.le_refl _) f hf h

/-- **COMPARABILITY on `FragR`**, same fuel. -/
theorem ltF_comparable3 {a b : Term} (hfa : FragR a = true) (hfb : FragR b = true)
    {f : Nat} (hf : a.deg + b.deg ≤ f) :
    ltF f a b = true ∨ a = b ∨ ltF f b a = true :=
  (cmp_aux3 (a.deg + b.deg)).2 a b hfa hfb (Nat.le_refl _) f hf

theorem asym3 : Asym3 := fun _ _ ha hb _ hf h => ltF_asymm3 ha hb hf h
theorem comp3 : Comp3 := fun _ _ ha hb _ hf => ltF_comparable3 ha hb hf

/-- **STAGE II, closed.**  Transitivity by §7.4's lexicographic measure
    `(b.deg, a.deg + c.deg)`, spelled out as an outer recursion on the middle
    degree with an inner induction on `a.deg + c.deg`. -/
private theorem trans_aux3 : ∀ (n : Nat) (m : Nat) (a b c : Term),
    FragR a = true → FragR b = true → FragR c = true →
    b.deg ≤ n → a.deg + c.deg ≤ m →
    ∀ f, a.deg + b.deg + c.deg ≤ f →
    ltF f a b = true → ltF f b c = true → ltF f a c = true
  | 0 => by
    intro _ _ b _ _ _ _ hb _ _ _ _ _
    exfalso; have := deg_pos b; omega
  | n + 1 => by
    intro m
    induction m with
    | zero =>
      intro a _ c _ _ _ _ hm _ _ _ _
      exfalso; have := deg_pos a; have := deg_pos c; omega
    | succ m ihm =>
      intro a b c hfa hfb hfc hb hm f hf h1 h2
      have TR1 : IH_TR1 n :=
        fun x y z hx hy hz hyd g hg =>
          trans_aux3 n (x.deg + z.deg) x y z hx hy hz hyd (Nat.le_refl _) g hg
      have TR2 : IH_TR2 b m :=
        fun x z hx hz hd g hg => ihm x b z hx hfb hz hb hd g hg
      have da := deg_pos a; have db := deg_pos b; have dc := deg_pos c
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hbz : b ≠ zero := by
        intro hc; rw [hc, ltF_right_zero] at h1; exact Bool.noConfusion h1
      have hcz : c ≠ zero := by
        intro hc; rw [hc, ltF_right_zero] at h2; exact Bool.noConfusion h2
      rcases fragR_sum_cases hfa with rfl | ⟨p, q, rfl, hfp, hfq⟩ | ⟨ha0, hna⟩
      · exact ltF_left_zero (by omega) hcz
      · rcases fragR_sum_cases hfb with rfl | ⟨r, s, rfl, hfr, hfs⟩ | ⟨hb0, hnb⟩
        · exact absurd rfl hbz
        · rcases fragR_sum_cases hfc with rfl | ⟨t, u, rfl, hft, hfu⟩ | ⟨hc0, hnc⟩
          · exact absurd rfl hcz
          · exact t1 p q r s t u n m f' hfa hfb hfc hb hm hf asym3 comp3 TR1 TR2 h1 h2
          · exact t2 p q r s c n m f' hc0 hnc hfa hfb hfc hb hm hf asym3 comp3 TR1 TR2 h1 h2
        · rcases fragR_sum_cases hfc with rfl | ⟨t, u, rfl, hft, hfu⟩ | ⟨hc0, hnc⟩
          · exact absurd rfl hcz
          · exact t3 p q b t u n m f' hb0 hnb hfa hfb hfc hb hm hf asym3 comp3 TR1 TR2 h1 h2
          · exact t4 p q b c n m f' hb0 hnb hc0 hnc hfa hfb hfc hb hm hf asym3 comp3 TR1 TR2 h1 h2
      · rcases fragR_sum_cases hfb with rfl | ⟨r, s, rfl, hfr, hfs⟩ | ⟨hb0, hnb⟩
        · exact absurd rfl hbz
        · rcases fragR_sum_cases hfc with rfl | ⟨t, u, rfl, hft, hfu⟩ | ⟨hc0, hnc⟩
          · exact absurd rfl hcz
          · exact t5 a r s t u n m f' ha0 hna hfa hfb hfc hb hm hf asym3 comp3 TR1 TR2 h1 h2
          · exact t6 a r s c n m f' ha0 hna hc0 hnc hfa hfb hfc hb hm hf asym3 comp3 TR1 TR2 h1 h2
        · rcases fragR_sum_cases hfc with rfl | ⟨t, u, rfl, hft, hfu⟩ | ⟨hc0, hnc⟩
          · exact absurd rfl hcz
          · exact t7 a b t u n m f' ha0 hna hb0 hnb hfa hfb hfc hb hm hf asym3 comp3 TR1 TR2 h1 h2
          · -- all three non-sums: §8.4(iv)'s level analysis
            by_cases hlv : lvl a < lvl c
            · exact t8 a b c n m f' lvlUp hna hnc hlv hfa hfb hfc hb hm hf
                asym3 comp3 TR1 TR2 h1 h2
            · have hab : ¬ (lvl b < lvl a) := by
                intro hcc
                rw [lvlDown f' a b hna hnb hcc] at h1; exact Bool.noConfusion h1
              have hbc : ¬ (lvl c < lvl b) := by
                intro hcc
                rw [lvlDown f' b c hnb hnc hcc] at h2; exact Bool.noConfusion h2
              rcases fragR_nsum_cases hfa ha0 hna with rfl | ⟨x, rfl, hfx⟩
                | ⟨p, q, rfl, hfp, hfq⟩ | ⟨k, u, rfl, hkR, hfk, hfu⟩ | ⟨x, rfl, hfx⟩
              · -- a = M, level 2 : `M < b` and `b < c` pin both to `M`
                have ea : lvl M = 2 := rfl
                obtain rfl : b = M := fragR_lvl2_eq hfb hb0 hnb (by omega)
                obtain rfl : c = M := fragR_lvl2_eq hfc hc0 hnc (by omega)
                exact t10 n m f' hfa hfb hfc hb hm hf asym3 comp3 TR1 TR2 h1 h2
              · -- a = ω̄^x, level 3
                have ea : lvl (omg x) = 3 := rfl
                obtain ⟨y, rfl, hfy⟩ := fragR_lvl3_cases hfb hb0 hnb (by omega)
                have eb : lvl (omg y) = 3 := rfl
                obtain ⟨z, rfl, hfz⟩ := fragR_lvl3_cases hfc hc0 hnc (by omega)
                exact t9 x y z n m f' hfa hfb hfc hb hm hf asym3 comp3 TR1 TR2 h1 h2
              · -- a = (phi p q), level 1
                have ea : lvl (phi p q) = 1 := rfl
                rcases fragR_lvl1_cases hfb hb0 hnb (by omega) with
                    ⟨r, s, rfl, hfr, hfs⟩ | ⟨j, w, rfl, hjR, hfj, hfw⟩ | ⟨w, rfl, hfw⟩
                · have eb : lvl (phi r s) = 1 := rfl
                  rcases fragR_lvl1_cases hfc hc0 hnc (by omega) with
                      ⟨t, u2, rfl, hft, hfu⟩ | ⟨j2, w2, rfl, _hj2, _hfj2, _hfw2⟩ | ⟨w2, rfl, _hfw2b⟩
                  · exact t11 p q r s t u2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                  · exact t12 p q r s j2 w2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                  · exact t13 p q r s w2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                · have eb : lvl (psi j w) = 1 := rfl
                  rcases fragR_lvl1_cases hfc hc0 hnc (by omega) with
                      ⟨t, u2, rfl, hft, hfu⟩ | ⟨j2, w2, rfl, _hj2, _hfj2, _hfw2⟩ | ⟨w2, rfl, _hfw2b⟩
                  · exact t14 p q j w t u2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                  · exact t15 p q j w j2 w2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                  · exact t16 p q j w w2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                · have eb : lvl (Z w) = 1 := rfl
                  rcases fragR_lvl1_cases hfc hc0 hnc (by omega) with
                      ⟨t, u2, rfl, hft, hfu⟩ | ⟨j2, w2, rfl, _hj2, _hfj2, _hfw2⟩ | ⟨w2, rfl, _hfw2b⟩
                  · exact t17 p q w t u2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                  · exact t18 p q w j2 w2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                  · exact t19 p q w w2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
              · -- a = (psi k u), level 1
                have ea : lvl (psi k u) = 1 := rfl
                rcases fragR_lvl1_cases hfb hb0 hnb (by omega) with
                    ⟨r, s, rfl, hfr, hfs⟩ | ⟨j, w, rfl, hjR, hfj, hfw⟩ | ⟨w, rfl, hfw⟩
                · have eb : lvl (phi r s) = 1 := rfl
                  rcases fragR_lvl1_cases hfc hc0 hnc (by omega) with
                      ⟨t, u2, rfl, hft, hfu⟩ | ⟨j2, w2, rfl, _hj2, _hfj2, _hfw2⟩ | ⟨w2, rfl, _hfw2b⟩
                  · exact t20_psi_phi_phi k u r s t u2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                  · exact t21_psi_phi_psi k u r s j2 w2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                  · exact t22_psi_phi_Z k u r s w2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                · have eb : lvl (psi j w) = 1 := rfl
                  rcases fragR_lvl1_cases hfc hc0 hnc (by omega) with
                      ⟨t, u2, rfl, hft, hfu⟩ | ⟨j2, w2, rfl, _hj2, _hfj2, _hfw2⟩ | ⟨w2, rfl, _hfw2b⟩
                  · exact t23_psi_psi_phi k u j w t u2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                  · exact t24 k u j w j2 w2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                  · exact t25_psi_psi_Z k u j w w2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                · have eb : lvl (Z w) = 1 := rfl
                  rcases fragR_lvl1_cases hfc hc0 hnc (by omega) with
                      ⟨t, u2, rfl, hft, hfu⟩ | ⟨j2, w2, rfl, _hj2, _hfj2, _hfw2⟩ | ⟨w2, rfl, _hfw2b⟩
                  · exact t26_psi_Z_phi k u w t u2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                  · exact t27_psi_Z_psi k u w j2 w2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                  · exact t28_psi_Z_Z k u w w2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
              · -- a = (Z x), level 1
                have ea : lvl (Z x) = 1 := rfl
                rcases fragR_lvl1_cases hfb hb0 hnb (by omega) with
                    ⟨r, s, rfl, hfr, hfs⟩ | ⟨j, w, rfl, hjR, hfj, hfw⟩ | ⟨w, rfl, hfw⟩
                · have eb : lvl (phi r s) = 1 := rfl
                  rcases fragR_lvl1_cases hfc hc0 hnc (by omega) with
                      ⟨t, u2, rfl, hft, hfu⟩ | ⟨j2, w2, rfl, _hj2, _hfj2, _hfw2⟩ | ⟨w2, rfl, _hfw2b⟩
                  · exact c29 x r s t u2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                  · exact c31 x r s j2 w2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                  · exact c30 x r s w2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                · have eb : lvl (psi j w) = 1 := rfl
                  rcases fragR_lvl1_cases hfc hc0 hnc (by omega) with
                      ⟨t, u2, rfl, hft, hfu⟩ | ⟨j2, w2, rfl, _hj2, _hfj2, _hfw2⟩ | ⟨w2, rfl, _hfw2b⟩
                  · exact c32 x j w t u2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                  · exact c33 x j w j2 w2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                  · exact c34 x j w w2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                · have eb : lvl (Z w) = 1 := rfl
                  rcases fragR_lvl1_cases hfc hc0 hnc (by omega) with
                      ⟨t, u2, rfl, hft, hfu⟩ | ⟨j2, w2, rfl, _hj2, _hfj2, _hfw2⟩ | ⟨w2, rfl, _hfw2b⟩
                  · exact c35 x w t u2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                  · exact c36 x w j2 w2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2
                  · exact t37_Z_Z_Z starClosed x w w2 n m f' hfa hfb hfc hb hm hf
                      asym3 comp3 TR1 TR2 h1 h2

/-- **TRANSITIVITY on `FragR`**, same fuel.  STAGE 3b, closed. -/
theorem trans_ltF3 {a b c : Term} (hfa : FragR a = true) (hfb : FragR b = true)
    (hfc : FragR c = true) {f : Nat} (hf : a.deg + b.deg + c.deg ≤ f)
    (h1 : ltF f a b = true) (h2 : ltF f b c = true) : ltF f a c = true :=
  trans_aux3 b.deg (a.deg + c.deg) a b c hfa hfb hfc (Nat.le_refl _) (Nat.le_refl _) f hf h1 h2

theorem trans3 : Trans3 := fun _ _ _ ha hb hc _ hf h1 h2 => trans_ltF3 ha hb hc hf h1 h2

/-! #### §8.5.3 The user-facing statements, about `lt` -/

/-- **ASYMMETRY.** -/
theorem lt_asymm3 {a b : Term} (hfa : FragR a = true) (hfb : FragR b = true)
    (h : lt a b = true) : lt b a = false := by
  rw [lt_eq_ltF a b (a.deg + b.deg) (Nat.le_refl _)] at h
  rw [lt_eq_ltF b a (a.deg + b.deg) (by omega)]
  exact ltF_asymm3 hfa hfb (Nat.le_refl _) h

/-- **COMPARABILITY.** -/
theorem lt_comparable3 {a b : Term} (hfa : FragR a = true) (hfb : FragR b = true) :
    lt a b = true ∨ a = b ∨ lt b a = true := by
  rw [lt_eq_ltF a b (a.deg + b.deg) (Nat.le_refl _),
      lt_eq_ltF b a (a.deg + b.deg) (by omega)]
  exact ltF_comparable3 hfa hfb (Nat.le_refl _)

/-- **TRANSITIVITY** on `FragR` — Stage 3b's keystone. -/
theorem lt_trans3 {a b c : Term} (hfa : FragR a = true) (hfb : FragR b = true)
    (hfc : FragR c = true) (h1 : lt a b = true) (h2 : lt b c = true) : lt a c = true := by
  have da := deg_pos a; have db := deg_pos b; have dc := deg_pos c
  rw [lt_eq_ltF a b (a.deg + b.deg + c.deg) (by omega)] at h1
  rw [lt_eq_ltF b c (a.deg + b.deg + c.deg) (by omega)] at h2
  rw [lt_eq_ltF a c (a.deg + b.deg + c.deg) (by omega)]
  exact trans_ltF3 hfa hfb hfc (Nat.le_refl _) h1 h2

/-- **`FragR` is a strict LINEAR order**: exactly one of `<`, `=`, `>`. -/
theorem lt_trichotomy3 {a b : Term} (hfa : FragR a = true) (hfb : FragR b = true) :
    (lt a b = true ∧ a ≠ b ∧ lt b a = false)
  ∨ (lt a b = false ∧ a = b ∧ lt b a = false)
  ∨ (lt a b = false ∧ a ≠ b ∧ lt b a = true) := by
  rcases lt_comparable3 hfa hfb with h | h | h
  · exact Or.inl ⟨h, ne_of_ltF h, lt_asymm3 hfa hfb h⟩
  · subst h; exact Or.inr (Or.inl ⟨lt_irrefl a, rfl, lt_irrefl a⟩)
  · refine Or.inr (Or.inr ⟨lt_asymm3 hfb hfa h, ?_, h⟩)
    intro hc; rw [hc, lt_irrefl] at h; exact Bool.noConfusion h

theorem lt_of_le_of_lt3 {a b c : Term} (hfa : FragR a = true) (hfb : FragR b = true)
    (hfc : FragR c = true) (h1 : le a b = true) (h2 : lt b c = true) : lt a c = true := by
  simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with rfl | h1
  · exact h2
  · exact lt_trans3 hfa hfb hfc h1 h2

theorem lt_of_lt_of_le3 {a b c : Term} (hfa : FragR a = true) (hfb : FragR b = true)
    (hfc : FragR c = true) (h1 : lt a b = true) (h2 : le b c = true) : lt a c = true := by
  simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at h2
  rcases h2 with rfl | h2
  · exact h1
  · exact lt_trans3 hfa hfb hfc h1 h2

theorem le_of_not_lt3 {a b : Term} (hfa : FragR a = true) (hfb : FragR b = true)
    (h : lt a b = false) : le b a = true := by
  simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq]
  rcases lt_comparable3 hfa hfb with h1 | h1 | h1
  · rw [h1] at h; exact Bool.noConfusion h
  · exact Or.inl h1.symm
  · exact Or.inr h1

theorem lt_of_not_le3 {a b : Term} (hfa : FragR a = true) (hfb : FragR b = true)
    (h : le a b = false) : lt b a = true := by
  simp only [TM.Term.le, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  rcases lt_comparable3 hfa hfb with h1 | h1 | h1
  · rw [h1] at h; exact absurd h.2 (by simp)
  · exact absurd h1 h.1
  · exact h1

theorem le_trans3 {a b c : Term} (hfa : FragR a = true) (hfb : FragR b = true)
    (hfc : FragR c = true) (h1 : le a b = true) (h2 : le b c = true) : le a c = true := by
  simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at h1 h2 ⊢
  rcases h1 with rfl | h1
  · exact h2
  · rcases h2 with rfl | h2
    · exact Or.inr h1
    · exact Or.inr (lt_trans3 hfa hfb hfc h1 h2)

/-! #### §8.5.4 The `inT` corollaries, and what subsumes what

`inT_le_fragR` (S4) makes every statement above apply to the genuine terms of
𝔗(M) — which is what `Evidence/Cert.lean`'s eventual `cert_sound` wants, and what
§6's map called for.  `Frag ⊆ Frag2 ⊆ FragR` (`frag_le_frag2`, `frag2_le_fragR`),
so §7 and §8.2 are both special cases; they are kept because their statements carry
no side condition at all and their mutants document that. -/

theorem lt_trans_inT {a b c : Term} (ha : inT a = true) (hb : inT b = true)
    (hc : inT c = true) (h1 : lt a b = true) (h2 : lt b c = true) : lt a c = true :=
  lt_trans3 (inT_le_fragR a ha) (inT_le_fragR b hb) (inT_le_fragR c hc) h1 h2

theorem lt_asymm_inT {a b : Term} (ha : inT a = true) (hb : inT b = true)
    (h : lt a b = true) : lt b a = false :=
  lt_asymm3 (inT_le_fragR a ha) (inT_le_fragR b hb) h

theorem lt_comparable_inT {a b : Term} (ha : inT a = true) (hb : inT b = true) :
    lt a b = true ∨ a = b ∨ lt b a = true :=
  lt_comparable3 (inT_le_fragR a ha) (inT_le_fragR b hb)

theorem le_trans_inT {a b c : Term} (ha : inT a = true) (hb : inT b = true)
    (hc : inT c = true) (h1 : le a b = true) (h2 : le b c = true) : le a c = true :=
  le_trans3 (inT_le_fragR a ha) (inT_le_fragR b hb) (inT_le_fragR c hc) h1 h2

/-- **The order on 𝔗(M) is a strict LINEAR order** — the statement §6's map set as
    the target of D2, now unconditional on anything but the formation conditions. -/
theorem lt_trichotomy_inT {a b : Term} (ha : inT a = true) (hb : inT b = true) :
    (lt a b = true ∧ a ≠ b ∧ lt b a = false)
  ∨ (lt a b = false ∧ a = b ∧ lt b a = false)
  ∨ (lt a b = false ∧ a ≠ b ∧ lt b a = true) :=
  lt_trichotomy3 (inT_le_fragR a ha) (inT_le_fragR b hb)

/-- §8.2 is subsumed: `Frag2 ⊆ FragR`. -/
theorem lt_trans_of_frag2 {a b c : Term} (ha : Frag2 a = true) (hb : Frag2 b = true)
    (hc : Frag2 c = true) (h1 : lt a b = true) (h2 : lt b c = true) : lt a c = true :=
  lt_trans3 (frag2_le_fragR a ha) (frag2_le_fragR b hb) (frag2_le_fragR c hc) h1 h2

/-! #### §8.5.5 Evidence, and the mutant that fixes a false caption of §8

§8 item 2 says of the raw language: "Asymmetry, by contrast, held everywhere, `inT`
or not".  THAT IS A DEGREE ≤ 6 MEASUREMENT AND IT IS FALSE IN GENERAL.  The
Phase-B gate sweep found 68 unordered violating pairs at degree 7; the smallest
witness is below, and Lean checks it here.  The two terms have degrees 5 and 7,
which is exactly why a degree-6 sweep cannot see it.

STAGE 3b IS UNAFFECTED: both witnesses fail `FragR` (and fail `inT`) at precisely
the `κ ∈ R` conjunct — `ψ_M M` and `ψ_(ψ_M M) 0` have head `M ∉ R`.  So this is one
more piece of evidence that `κ ∈ R` is the right restriction, which is why it is
recorded here rather than merely fixed in the prose. -/

#guard lt (phi (psi M M) M) (phi (psi (psi M M) zero) M) == true
#guard lt (phi (psi (psi M M) zero) M) (phi (psi M M) M) == true
#guard FragR (phi (psi M M) M) == false
#guard FragR (phi (psi (psi M M) zero) M) == false
#guard inT (phi (psi M M) M) == false
#guard inT (phi (psi (psi M M) zero) M) == false
#guard (phi (psi M M) M).deg == 5
#guard (phi (psi (psi M M) zero) M).deg == 7

/-- **Raw `lt` is NOT asymmetric**, contrary to §8 item 2's parenthetical, which was
    a degree ≤ 6 observation.  Both witnesses lie outside `FragR`. -/
theorem lt_not_asymm_raw :
    ¬ (∀ (a b : Term), lt a b = true → lt b a = false) := by
  intro h
  have hbad := h (phi (psi M M) M) (phi (psi (psi M M) zero) M) rfl
  have hc : lt (phi (psi (psi M M) zero) M) (phi (psi M M) M) = true := rfl
  rw [hc] at hbad
  exact Bool.noConfusion hbad

/-- **Raw `lt` is NOT transitive** either — a degree ≤ 6 witness, so this one the
    earlier sweeps could have seen but did not look for (§8.2.5 searched only for
    triples whose endpoints were incomparable, and these two ARE comparable).
    Both endpoints again fail `FragR` at `κ ∈ R`. -/
theorem lt_not_trans_raw :
    ¬ (∀ (a b c : Term), lt a b = true → lt b c = true → lt a c = true) := by
  intro h
  have hbad := h (Z (psi (psi M zero) zero)) (psi (psi M zero) M) (Z (psi M zero)) rfl rfl
  have hc : lt (Z (psi (psi M zero) zero)) (Z (psi M zero)) = false := rfl
  rw [hc] at hbad
  exact Bool.noConfusion hbad

#guard FragR (Z (psi (psi M zero) zero)) == false
#guard FragR (psi (psi M zero) M) == false

/-! NON-VACUITY of Stage 3b: a sample inside `FragR` that `Frag2` cannot reach,
    exercising `ψ` and `Z` and the `starF` clauses. -/

private def fragRSample : List Term :=
  [zero, one, M, omg M, Om, Z Om, psi Om zero, psi Om one, psi (Z Om) zero,
   add (psi Om zero) one, phi one (psi Om zero)]

#guard fragRSample.all (fun t => FragR t)
#guard !fragRSample.all (fun t => Frag2 t)
#guard fragRSample.all (fun s => fragRSample.all (fun t => !(lt s t && lt t s)))
#guard fragRSample.all (fun s => fragRSample.all (fun t => lt s t || s == t || lt t s))
#guard fragRSample.all (fun s => fragRSample.all (fun t => fragRSample.all (fun u =>
         !(lt s t && lt t u) || lt s u)))

/-! ### §8.6 MIXED transitivity: an unconstrained middle term, for the certificate lane

THE REQUEST (certificate lane, 2026-08-09): `le s x → lt x v → lt s v` with `s` and
`v` in the CNF region and `x` UNCONSTRAINED — because their bound (Cert.lean §15.7)
pins only a value's leftmost component, so they cannot show the middle term lies in
any fragment, and `Trans3`, which constrains all three terms, does not reach them.

THE ANSWER: they do not need a new theorem, and they do not need the middle term in
a fragment.  They need `inT x` — which every term of 𝔗(M) satisfies by
construction — and then §13 CONSTRAINS THE MIDDLE FOR THEM: `frag_of_lt_cn` says
that below a Cantor normal form there is nothing but Cantor normal forms, so `x`
lands in `Frag` on its own and §7's `lt_of_le_of_lt` closes the goal.  The whole
thing is the three lines below; no induction, no new measure, and no dependence on
§8.5.

WHY `inT` ON THE MIDDLE CANNOT BE DROPPED, and why that is not a real cost.  §13's
hypothesis is indispensable for its own reason (`0 ⊕ M` is below `1` but is not
CNF), so the `inT`-free statement does not follow by this route.  MEASURED at
degree ≤ 5: 34 terms are non-CNF and yet strictly below some CNF term, and ZERO of
them satisfy `inT` — i.e. `inT` is exactly the hypothesis that removes them.  The
fully unconstrained version was also swept (all 578 terms of degree ≤ 5 as the
middle, against `Frag2` endpoints and again against `CN` endpoints) and NO
counterexample was found; so it is plausibly true, but it is NOT proved here and
§13's route is closed to it.  If the lane ever needs the middle term without `inT`,
that is a separate lemma with its own argument — say so rather than assuming this
one covers it. -/

/-- **MIXED transitivity, CNF endpoints.**  The middle term `x` is constrained only
    by `inT`; §13 supplies the rest. -/
theorem lt_of_le_of_lt_cn {s x v : Term} (hs : CN s = true) (hx : inT x = true)
    (hv : CN v = true) (h1 : le s x = true) (h2 : lt x v = true) : lt s v = true :=
  lt_of_le_of_lt (frag_of_cn s hs) (frag_of_lt_cn hx hv h2) (frag_of_cn v hv) h1 h2

/-- The same with the left endpoint only assumed to be in `Frag2` (§8.2's fragment),
    which is the shape the certificate lane asked for. -/
theorem lt_of_le_of_lt_mixed {s x v : Term} (hs : Frag2 s = true) (hx : inT x = true)
    (hv : CN v = true) (h1 : le s x = true) (h2 : lt x v = true) : lt s v = true :=
  lt_of_le_of_lt2 hs (frag_le_frag2 x (frag_of_lt_cn hx hv h2))
    (frag_le_frag2 v (frag_of_cn v hv)) h1 h2

/-- The `lt`/`lt` form, for completeness. -/
theorem lt_trans_mixed {s x v : Term} (hs : Frag2 s = true) (hx : inT x = true)
    (hv : CN v = true) (h1 : lt s x = true) (h2 : lt x v = true) : lt s v = true :=
  lt_trans2 hs (frag_le_frag2 x (frag_of_lt_cn hx hv h2))
    (frag_le_frag2 v (frag_of_cn v hv)) h1 h2

/-! Receipts for the measurement quoted above: `0 ⊕ M` is the reason §13 needs
    `inT`, and it is exactly the kind of middle term the `inT`-free statement would
    have to survive. -/

#guard lt (add zero M) one == true          -- below a CNF term …
#guard CN (add zero M) == false             -- … without being one
#guard inT (add zero M) == false            -- … and this is what `inT` rules out
#guard CN one == true

/-! ### §8.7 SCOPING NOTE: why §8.5 does NOT extend §10, and what the sweeps cover

Recorded because it is the first thing anyone will try after Stage 3b, and it is
wrong.  Linearity and well-foundedness move in OPPOSITE directions along the
fragments of this file:

    Frag  ⊂  Frag2  ⊂  FragR          linearity WIDENS  (§7 → §8.2 → §8.5)
    CN    ⊂  Frag                     accessibility NARROWS  (§10)

§10.3's `cn_desc_needed` shows `Frag` is already too wide for well-foundedness: the
witnesses `1 ⊕ 1 ⊕ … ⊕ ω` descend forever and are all in `Frag`.  They are therefore
in `Frag2` and in `FragR` as well (guards below), so NO amount of Stage-3a/3b
widening helps — `∀ t, FragR t = true → Acc RC t` is FALSE, by the same witnesses.
What §10 needs is 2.1(iii)'s DESCENDING condition, which `CN` carries and none of
`Frag` / `Frag2` / `FragR` does.  Stage 3b's contribution to a future
well-foundedness result is therefore not its fragment but its ORDER THEORY: §10's
Gentzen step spends `lt_of_le_of_lt`, and past ε₀ the corresponding step would spend
`lt_trans3` / `lt_trichotomy3` on the wider region.

So the fragment for any accessibility result above ε₀ is "`FragR` ∩ descending",
i.e. essentially `inT` — NOT `FragR`. -/

#guard (List.range 6).all (fun n => Frag2 (desc n))
#guard (List.range 6).all (fun n => FragR (desc n))
#guard !inT (desc 1)

/-! WHAT THE UNCONSTRAINED-MIDDLE SWEEP COVERS (§8.6's open caveat).

§8.6 proves the mixed statement with `inT` on the middle.  The version with the
middle entirely unconstrained is still open, and the search behind "no
counterexample" is this, so that the claim is not read as wider than the check:

  * the test is EXACT per middle term, not sampled over endpoint pairs: because
    `Frag2` is linearly ordered (`lt_trichotomy2`), a middle `x` admits a violation
    iff the LARGEST `s` with `le s x` fails to be below the SMALLEST `v` with
    `lt x v`.  So one comparison per middle decides all |A|·|C| pairs at once.
  * coverage: ALL 578 middles of degree ≤ 5 and ALL 3042 of degree ≤ 6, against the
    154 resp. 556 `Frag2` endpoints of those degrees; plus a 1-in-20 sample, 843 of
    the 16850 middles of degree ≤ 7, against all 2278 `Frag2` endpoints there.
    Zero violations anywhere.
  * this is NOT vacuous: `lt_not_asymm_raw` and `lt_not_trans_raw` show the ambient
    raw order genuinely has 2- and 3-cycles, so the statement survives in spite of
    the surrounding order being neither asymmetric nor transitive — which is
    evidence that the `Frag2` endpoints are doing real work, not that the
    configuration is impossible.
  * degree ≥ 8 is NOT covered, and no proof is claimed. -/

/-! ## §15 THE VEBLEN SEGMENT BELOW Γ₀ IS WELL-FOUNDED  (STAGE 1 of the wf road)

WHAT THIS IS.  §10 proves accessibility for `CN` — the Cantor normal forms below ε₀,
i.e. `φ̄0β` and descending sums of them.  This section does the same one level up, for
the full BINARY VEBLEN fragment: `φ̄αβ` with α arbitrary, which reaches Γ₀.  §10 is
subsumed (`cnv_of_cn`), and the target of the road is (B) — the full R1 ordinal
ψ_{Ω₁}(ε_{M+1}) — so this is step 1, not the destination; see THE SEAM below.

THE FRAGMENT, AND WHY ONLY THE SUMS ARE RESTRICTED.  `CNV` is `Frag` plus 2.1(iii) on
sums (components additively principal, descending) and NOTHING else — in particular no
Veblen normal-form condition on `φ̄`.  That is not an oversight, and the evidence is a
CALIBRATED CONTRAST rather than an absence of evidence.  §10.3 shows what forces
2.1(iii): prefix-descent, `1 ⊕ 1 ⊕ … ⊕ ω`.  Testing for exactly that shape over the
COMPLETE corpus of all 1619 `Frag` terms of degree ≤ 12 (complete because `Frag` degrees
are odd, so the generator saturates):

      ∃ c u,  lt (add c u) u  =  true     →  1,224,175 witness pairs
      ∃ a u,  lt (phi a u) u  =  true     →  0 witnesses

The positive control fires massively, so the zero is informative: `⊕` admits
prefix-descent everywhere and `φ̄` admits it nowhere.  Inside `CNV` both counts are 0.
Sizes: `CNV` admits 89 of those 1619 terms against `CN`'s 14 — a 6.4x widening, exactly
the step ε₀ → Γ₀.

`CNV` CARRIES AN ORDER-VALUED CONJUNCT (`hdLe` calls `le`), exactly as `CN` already does.
That is safe HERE and would not be in §7/§8: the induction below is on `Acc`, not on
`lt`, so there is no circularity.  This is the one place where the trade-off that made
§8.4 choose the syntactic `FragR` over `inT` runs the other way.

WHAT CHANGED FROM §10's ARGUMENT, and why it had to.  §10 returns a PAIR — `Acc (ω^a)`
together with the `⊕` step for that head — because its `⊕` half needs the `C` lemma of
the same head.  With α = 0 fixed, the head of any smaller sum is `ω^e` with `e < a`, so
the outer induction always reaches it.  With BINARY Veblen it does not: 2.3.13(iii) lets
a head `φ̄pq` with `p > a` sit below `φ̄ab` (via `φ̄pq ≤ b`), and no induction hypothesis
of the (a, b) recursion reaches `(p, q)`.  THE FIX IS TO DECOUPLE: `acc_sum` below proves
"accessibility is closed under `⊕`" as a STANDALONE lemma, taking `Acc c` and `Acc d` as
hypotheses instead of deriving them from a pair.  Its own `u < c` case then needs the
tail `w` of a smaller sum to be accessible, and that is `lt_tail_of_lt`: `hdLe w u` bounds
`w`'s head by `u`, so `w < c` whenever `u < c` and `c` is additively principal.  With
`acc_sum` standalone, `C` never needs a pair at a head it cannot reach, and 13(iii)
becomes a one-liner (`x ≤ b`, so `Acc x` follows from `Acc b`).

THE SEAM — what survives into (B), stated because the next reader will otherwise assume
all of it does.
  SURVIVES: `CNV` and its destructors, `lt_tail_cnv`, `lt_tail_of_lt`, the relation, and
    `acc_sum`.  `acc_sum` is essentially generic — it uses only 2.3.11 and 2.3.16 and the
    fact that the head is additively principal, all of which hold verbatim with `ψ`/`Z`
    heads; adapting it means replacing `lt_phi_add` by the arbitrary-non-sum form (§8.2's
    `ltF_succ_nsum_add` is already proved for every non-sum) and `eq_phi_of_isAP_cnv` by
    "additively principal = non-sum, non-zero".  The top-level degree recursion is generic
    too.
  DOES NOT SURVIVE: `acc_phi_v`'s inner `C`.  It is a STRUCTURAL induction on `x` only
    because `x < φ̄ a b` bounds `x` structurally.  For `ψ_κ α` it does not — that is what
    collapsing means — and this is exactly where Rathjen 1994's distinguished-set / C_κ
    machinery has to enter.  It is a different method, not a further case.
  THE INITIAL-SEGMENT PROPERTY that makes this permanent (`inT x → CNV v → lt x v → CNV x`,
    the §13 analogue) IS PROVED, in §15.1 below, together with the upgrade of `acc_cnv`
    from the `CNV`-relation to the `inT`-relation.  Its ψ-analogue is probably FALSE —
    below `ψ_κ α` there are terms of essentially arbitrary shape — so that trick is a gift
    of the Veblen layer specifically; see §15.1. -/

def CNV : Term → Bool
  | zero => true
  | phi a b => CNV a && CNV b
  | add a b => a.isAP && CNV a && CNV b && hdLe b a
  | _ => false

theorem cnv_phi {a b : Term} (h : CNV (phi a b) = true) : CNV a = true ∧ CNV b = true := by
  simp only [CNV, Bool.and_eq_true] at h; exact h

theorem cnv_add {a b : Term} (h : CNV (add a b) = true) :
    a.isAP = true ∧ CNV a = true ∧ CNV b = true ∧ hdLe b a = true := by
  simp only [CNV, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem frag_of_cnv : ∀ (t : Term), CNV t = true → Frag t = true
  | zero, _ => rfl
  | M, h => Bool.noConfusion h
  | omg _, h => Bool.noConfusion h
  | psi _ _, h => Bool.noConfusion h
  | Z _, h => Bool.noConfusion h
  | phi a b, h => by
    obtain ⟨ha, hb⟩ := cnv_phi h
    show (Frag a && Frag b) = true
    rw [frag_of_cnv a ha, frag_of_cnv b hb]; rfl
  | add a b, h => by
    obtain ⟨_, ha, hb, _⟩ := cnv_add h
    show (Frag a && Frag b) = true
    rw [frag_of_cnv a ha, frag_of_cnv b hb]; rfl

/-- An additively principal `CNV` term is a `φ̄`. -/
theorem eq_phi_of_isAP_cnv : ∀ {c : Term}, CNV c = true → c.isAP = true → ∃ p q, c = phi p q
  | zero, _, h => Bool.noConfusion h
  | add _ _, _, h => Bool.noConfusion h
  | M, h, _ => Bool.noConfusion h
  | omg _, h, _ => Bool.noConfusion h
  | psi _ _, h, _ => Bool.noConfusion h
  | Z _, h, _ => Bool.noConfusion h
  | phi p q, _, _ => ⟨p, q, rfl⟩

/-- The tail of a `CNV` sum inherits any `φ̄`-bound on its head (§10's `lt_tail`). -/
theorem lt_tail_cnv {a b p q : Term} (h : CNV (add a b) = true) (hfpq : Frag (phi p q) = true)
    (hlt : lt a (phi p q) = true) : lt b (phi p q) = true := by
  obtain ⟨_, hcna, hcnb, hdesc⟩ := cnv_add h
  have hfa : Frag a = true := frag_of_cnv a hcna
  cases b with
  | zero => exact Bool.noConfusion hdesc
  | M => exact Bool.noConfusion hcnb
  | omg _ => exact Bool.noConfusion hcnb
  | psi _ _ => exact Bool.noConfusion hcnb
  | Z _ => exact Bool.noConfusion hcnb
  | phi x y => exact lt_of_le_of_lt (frag_of_cnv _ hcnb) hfa hfpq hdesc hlt
  | add c d =>
    obtain ⟨_, hcnc, _, _⟩ := cnv_add hcnb
    rw [lt_add_phi]
    exact lt_of_le_of_lt (frag_of_cnv c hcnc) hfa hfpq hdesc hlt

/-- THE NEW STEP the standalone `⊕` lemma needs: a `CNV` tail sits below anything its
    own component sits below, because `hdLe` bounds its head.  This is what removes the
    need for §10's coupled pair, and with it the 13(iii) obstruction. -/
theorem lt_tail_of_lt {w u c : Term} (hw : CNV w = true) (hu' : CNV u = true)
    (hd : hdLe w u = true) (hc : CNV c = true) (hAP : c.isAP = true)
    (hu : lt u c = true) : lt w c = true := by
  obtain ⟨p, q, rfl⟩ := eq_phi_of_isAP_cnv hc hAP
  have hfc : Frag (phi p q) = true := frag_of_cnv _ hc
  have hfu : Frag u = true := frag_of_cnv u hu'
  cases w with
  | zero => exact Bool.noConfusion hd
  | M => exact Bool.noConfusion hw
  | omg _ => exact Bool.noConfusion hw
  | psi _ _ => exact Bool.noConfusion hw
  | Z _ => exact Bool.noConfusion hw
  | phi x y => exact lt_of_le_of_lt (frag_of_cnv _ hw) hfu hfc hd hu
  | add s t =>
    obtain ⟨_, hcs, _, _⟩ := cnv_add hw
    rw [lt_add_phi]
    exact lt_of_le_of_lt (frag_of_cnv s hcs) hfu hfc hd hu

def RV (x y : Term) : Prop := CNV x = true ∧ lt x y = true

theorem acc_zero_v : Acc RV zero := by
  refine Acc.intro _ (fun x hx => ?_)
  have h := hx.2
  rw [show lt x zero = false from ltF_right_zero _ x] at h
  exact Bool.noConfusion h

/-- **Accessibility is closed under `⊕`** — standalone, unlike §10 where the `⊕` half is
    coupled to the `φ̄` half and returned as a pair.  Decoupling is what dissolves the
    13(iii) obstruction: `C` never needs the pair at a head it cannot reach. -/
private theorem acc_sum : ∀ (c : Term), Acc RV c → CNV c = true → c.isAP = true →
    ∀ (d : Term), Acc RV d → CNV d = true → hdLe d c = true → Acc RV (add c d) := by
  intro c hc
  induction hc with
  | intro c hc' IHc =>
    intro hcnc hAPc d hd
    induction hd with
    | intro d hd' IHd =>
      intro hcnd hdesc
      refine Acc.intro _ (fun x hx => ?_)
      obtain ⟨hcnx, hlt⟩ := hx
      cases x with
      | zero => exact acc_zero_v
      | M => exact Bool.noConfusion hcnx
      | omg _ => exact Bool.noConfusion hcnx
      | psi _ _ => exact Bool.noConfusion hcnx
      | Z _ => exact Bool.noConfusion hcnx
      | phi s t =>
        rw [lt_phi_add] at hlt
        simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at hlt
        rcases hlt with h1 | h1
        · rw [h1]; exact Acc.intro _ hc'
        · exact hc' _ ⟨hcnx, h1⟩
      | add u w =>
        obtain ⟨hAPu, hcnu, hcnw, hdw⟩ := cnv_add hcnx
        by_cases heq : add u w = add c d
        · rw [heq, lt_irrefl] at hlt; exact Bool.noConfusion hlt
        rw [lt_add_add heq] at hlt
        by_cases huc : u = c
        · subst huc
          rw [if_pos rfl] at hlt
          exact IHd w ⟨hcnw, hlt⟩ hcnw hdw
        · rw [if_neg huc] at hlt
          have hwc : lt w c = true := lt_tail_of_lt hcnw hcnu hdw hcnc hAPc hlt
          exact IHc u ⟨hcnu, hlt⟩ hcnu hAPu w (hc' w ⟨hcnw, hwc⟩) hcnw hdw

/-- **THE VEBLEN STEP.**  `φ̄ a b` is accessible whenever `a` and `b` are. -/
private theorem acc_phi_v : ∀ (a : Term), Acc RV a → CNV a = true →
    ∀ (b : Term), Acc RV b → CNV b = true → Acc RV (phi a b) := by
  intro a ha
  induction ha with
  | intro a ha' IHa =>
    intro hcna b hb
    induction hb with
    | intro b hb' IHb =>
      intro hcnb
      have hfab : Frag (phi a b) = true :=
        frag_of_cnv _ (by show (CNV a && CNV b) = true; rw [hcna, hcnb]; rfl)
      have C : ∀ x, CNV x = true → lt x (phi a b) = true → Acc RV x := by
        intro x
        induction x with
        | zero => intro _ _; exact acc_zero_v
        | M => intro h _; exact Bool.noConfusion h
        | omg _ _ => intro h _; exact Bool.noConfusion h
        | psi _ _ _ _ => intro h _; exact Bool.noConfusion h
        | Z _ _ => intro h _; exact Bool.noConfusion h
        | phi p q _ ihq =>
          intro hcn hlt
          obtain ⟨hcnp, hcnq⟩ := cnv_phi hcn
          by_cases heq : phi p q = phi a b
          · rw [heq, lt_irrefl] at hlt; exact Bool.noConfusion hlt
          rw [lt_phi_phi heq] at hlt
          by_cases hpa : p = a
          · subst hpa
            rw [if_pos rfl] at hlt
            exact IHb q ⟨hcnq, hlt⟩ hcnq
          · rw [if_neg hpa] at hlt
            by_cases hlt2 : lt p a = true
            · rw [if_pos hlt2] at hlt
              exact IHa p ⟨hcnp, hlt2⟩ hcnp q (ihq hcnq hlt) hcnq
            · rw [if_neg hlt2] at hlt
              simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at hlt
              rcases hlt with h1 | h1
              · rw [h1]; exact Acc.intro _ hb'
              · exact hb' _ ⟨hcn, h1⟩
        | add c d ihc ihd =>
          intro hcn hlt
          obtain ⟨hAPc, hcnc, hcnd, hdesc⟩ := cnv_add hcn
          have hhead : lt c (phi a b) = true := by rw [← lt_add_phi]; exact hlt
          have htail : lt d (phi a b) = true := lt_tail_cnv hcn hfab hhead
          exact acc_sum c (ihc hcnc hhead) hcnc hAPc d (ihd hcnd htail) hcnd hdesc
      exact Acc.intro _ (fun x hx => C x hx.1 hx.2)

private theorem acc_cnv_aux : ∀ (n : Nat) (t : Term), t.deg ≤ n → CNV t = true → Acc RV t := by
  intro n
  induction n with
  | zero => intro t hd _; have := deg_pos t; omega
  | succ n ih =>
    intro t hd hcn
    cases t with
    | zero => exact acc_zero_v
    | M => exact Bool.noConfusion hcn
    | omg _ => exact Bool.noConfusion hcn
    | psi _ _ => exact Bool.noConfusion hcn
    | Z _ => exact Bool.noConfusion hcn
    | phi p q =>
      obtain ⟨hp, hq⟩ := cnv_phi hcn
      have e : (phi p q).deg = 1 + p.deg + q.deg := rfl
      have h1 := deg_pos p; have h2 := deg_pos q
      exact acc_phi_v p (ih p (by omega) hp) hp q (ih q (by omega) hq) hq
    | add c d =>
      obtain ⟨hAP, hc, hd', hdesc⟩ := cnv_add hcn
      have e : (add c d).deg = 1 + c.deg + d.deg := rfl
      have h1 := deg_pos c; have h2 := deg_pos d
      exact acc_sum c (ih c (by omega) hc) hc hAP d (ih d (by omega) hd') hd' hdesc

/-- **WELL-FOUNDEDNESS OF THE VEBLEN SEGMENT BELOW Γ₀.** -/
theorem acc_cnv (t : Term) (h : CNV t = true) : Acc RV t :=
  acc_cnv_aux t.deg t (Nat.le_refl _) h

-- CN ⊆ CNV, so §10's segment is subsumed
theorem cnv_of_cn : ∀ (t : Term), CN t = true → CNV t = true
  | zero, _ => rfl
  | M, h => Bool.noConfusion h
  | omg _, h => Bool.noConfusion h
  | psi _ _, h => Bool.noConfusion h
  | Z _, h => Bool.noConfusion h
  | phi a b, h => by
    obtain ⟨ha, hb⟩ := cn_phi h
    subst ha
    show (CNV zero && CNV b) = true
    rw [cnv_of_cn b hb]; rfl
  | add a b, h => by
    obtain ⟨hpow, ha, hb, hd⟩ := cn_add h
    show (a.isAP && CNV a && CNV b && hdLe b a) = true
    have : a.isAP = true := by cases a <;> simp_all [isPow, Term.isAP]
    rw [this, cnv_of_cn a ha, cnv_of_cn b hb, hd]; rfl

/-! Receipts: the ε₀ → Γ₀ widening, and the calibrated contrast quoted above. -/

#guard CNV (phi one zero) == true      -- ε₀ = φ̄(1,0) is in CNV …
#guard CN  (phi one zero) == false     -- … and NOT in CN: this is the widening
#guard CNV omega == true
#guard CNV (add one omega) == false    -- §10.3's descent family is excluded
#guard lt (add one omega) omega == true                        -- ⊕ admits prefix-descent
#guard lt (phi zero (phi one zero)) (phi one zero) == false    -- φ̄ does not
#guard lt (phi one zero) (phi zero (phi one zero)) == true


/-! ### §15.1 THE INITIAL SEGMENT, AND THE RELATION AT ITS FINAL WIDTH

WHAT THIS ADDS.  §15 proves accessibility for `CNV` against the `CNV`-relation `RV`.
That is not yet a statement one can extend: the destination is (B), the full R1 ordinal,
and a later `ψ` layer must not have to restate step 1.  The fix is NOT to widen the
predicate — `ψ` and `Z` terms sit below `φ̄` terms (2.3.4: Γ₀ < φ̄Γ₀0), so an `inT`-stated
step 1 would drag the collapsing region into step 1 and leave no Veblen-first layer.  The
fix is to widen the RELATION and let the predicate narrow per layer:

    RT x y := inT x ∧ lt x y          -- final width, never changes again
    acc_cnv_inT : ∀ t, CNV t → Acc RT t

which is a LITERAL SUB-STATEMENT of the eventual `∀ t, inT t → Acc RT t`.  What licenses
it is `cnv_of_lt_cnv` — below a Veblen normal form there is nothing but Veblen normal
forms — so the `RT`-predecessors of a `CNV` term are all `CNV` and the two relations agree
there.  This is §13's theorem one level up, and it is proved here, not assumed.

CALIBRATION for the claim that `CNV` is an initial segment.  MEASURED over the 1687 `inT`
terms of degree ≤ 8 against the 89 `CNV` terms of degree ≤ 12:

    non-CNV `inT` terms below some CNV term           :   0
    `inT` terms below Γ₀ that are not CNV             :   0      -- so CNV = inT ∩ (< Γ₀)
    all 89 CNV terms are < Γ₀, and CNV Γ₀ = false     -- Γ₀ is the supremum, not a member
    POSITIVE CONTROL — the same sweep with `inT` dropped:  134 violations at degree ≤ 6

The control is what makes the zeros informative: without `inT` the property fails badly,
and the smallest witness is §13's own, `0 ⊕ M < 1` with `0 ⊕ M` not a normal form.  That
is exactly why `cnv_of_lt_cnv` carries `inT` and cannot be stated without it.

THE ψ-ANALOGUE IS PROBABLY FALSE, and that is worth writing down rather than leaving as a
silent gap: below `ψ_κ α` there are terms of essentially arbitrary shape — the same fact,
seen from the other side, that makes `acc_phi_v`'s `C` a structural induction for `φ̄` and
not for `ψ_κ`.  So the initial-segment trick that makes step 1 permanent is a gift of the
Veblen layer specifically, and whoever takes (B) should not plan on repeating it.  If it
turns out true, that is a discovery. -/

theorem cnv_ne_junkAP {s b : Term} (hs : junkAP s = true) (hb : CNV b = true) :
    (s == b) = false := by
  cases s <;> cases b <;>
    first
      | rfl
      | exact Bool.noConfusion hs
      | exact Bool.noConfusion hb

/-- No `M` / `ω̄` / `ψ` / `Z` term is below a `CNV` term.  §13's `lt_junkAP_cn` needs only
    ONE induction hypothesis because `CN` forces the first Veblen argument to be `0`;
    here both are live. -/
theorem lt_junkAP_cnv : ∀ (y : Term), CNV y = true → ∀ (f : Nat) (s : Term),
    junkAP s = true → ltF f s y = false := by
  intro y
  induction y with
  | M => intro hb; exact Bool.noConfusion hb
  | omg _ _ => intro hb; exact Bool.noConfusion hb
  | psi _ _ _ _ => intro hb; exact Bool.noConfusion hb
  | Z _ _ => intro hb; exact Bool.noConfusion hb
  | zero =>
    intro _ f s hs
    cases f with
    | zero => rfl
    | succ g =>
      cases s with
      | zero => exact Bool.noConfusion hs
      | add _ _ => exact Bool.noConfusion hs
      | phi _ _ => exact Bool.noConfusion hs
      | M => rfl
      | omg _ => rfl
      | psi _ _ => rfl
      | Z _ => rfl
  | phi x b ihx ihb =>
    intro hcn f s hs
    obtain ⟨hcx, hcb⟩ := cnv_phi hcn
    cases f with
    | zero => rfl
    | succ g =>
      cases s with
      | zero => exact Bool.noConfusion hs
      | add _ _ => exact Bool.noConfusion hs
      | phi _ _ => exact Bool.noConfusion hs
      | M => rfl
      | omg _ => rfl
      | psi k a =>
        rw [ltF_succ_psi_phi, cnv_ne_junkAP (s := psi k a) rfl hcx,
          cnv_ne_junkAP (s := psi k a) rfl hcb, ihx hcx g (psi k a) rfl,
          ihb hcb g (psi k a) rfl]
        rfl
      | Z a =>
        rw [ltF_succ_Z_phi, cnv_ne_junkAP (s := Z a) rfl hcx,
          cnv_ne_junkAP (s := Z a) rfl hcb, ihx hcx g (Z a) rfl, ihb hcb g (Z a) rfl]
        rfl
  | add u v ihu ihv =>
    intro hcn f s hs
    obtain ⟨_, hcu, _, _⟩ := cnv_add hcn
    cases f with
    | zero => rfl
    | succ g =>
      cases s with
      | zero => exact Bool.noConfusion hs
      | add _ _ => exact Bool.noConfusion hs
      | phi _ _ => exact Bool.noConfusion hs
      | M =>
        show ((M : Term) == u || ltF g M u) = false
        rw [cnv_ne_junkAP (s := M) rfl hcu, ihu hcu g M rfl]; rfl
      | omg a =>
        show ((omg a == u) || ltF g (omg a) u) = false
        rw [cnv_ne_junkAP (s := omg a) rfl hcu, ihu hcu g (omg a) rfl]; rfl
      | psi k a =>
        show ((psi k a == u) || ltF g (psi k a) u) = false
        rw [cnv_ne_junkAP (s := psi k a) rfl hcu, ihu hcu g (psi k a) rfl]; rfl
      | Z a =>
        show ((Z a == u) || ltF g (Z a) u) = false
        rw [cnv_ne_junkAP (s := Z a) rfl hcu, ihu hcu g (Z a) rfl]; rfl

theorem hdLe_of_lt_cnv : ∀ (y : Term), CNV y = true → ∀ (s : Term), s ≠ zero → inT s = true →
    lt s y = true → hdLe s y = true := by
  intro y hcn s hz hin hlt
  cases s with
  | zero => exact absurd rfl hz
  | M => exact le_of_lt hlt
  | omg _ => exact le_of_lt hlt
  | phi _ _ => exact le_of_lt hlt
  | psi _ _ => exact le_of_lt hlt
  | Z _ => exact le_of_lt hlt
  | add c d =>
    obtain ⟨hap, _, _⟩ := inT_add hin
    cases y with
    | zero =>
      rw [show lt (add c d) zero = false from ltF_right_zero _ _] at hlt
      exact Bool.noConfusion hlt
    | M => exact Bool.noConfusion hcn
    | omg _ => exact Bool.noConfusion hcn
    | psi _ _ => exact Bool.noConfusion hcn
    | Z _ => exact Bool.noConfusion hcn
    | phi p q =>
      rw [lt_add_phi] at hlt
      show ((c == phi p q) || lt c (phi p q)) = true
      rw [hlt]; exact Bool.or_true _
    | add u v =>
      show ((c == add u v) || lt c (add u v)) = true
      rw [lt_atom_add (isAtom_of_isAP hap)]
      by_cases heq : add c d = add u v
      · injection heq with h1 h2
        rw [h1]
        show ((u == add u v) || ((u == u) || lt u u)) = true
        simp
      · rw [lt_add_add heq] at hlt
        by_cases hcu : c = u
        · rw [hcu]
          show ((u == add u v) || ((u == u) || lt u u)) = true
          simp
        · rw [if_neg hcu] at hlt
          show ((c == add u v) || ((c == u) || lt c u)) = true
          rw [hlt]; simp

/-- **The structural theorem, one level up from §13.**  A term of 𝔗(M) whose head does
    not exceed a Veblen normal form is itself one. -/
theorem cnv_of_inT_hdLe : ∀ (n : Nat) (s c : Term), s.deg + c.deg ≤ n →
    inT s = true → CNV c = true → hdLe s c = true → CNV s = true := by
  intro n
  induction n with
  | zero =>
    intro s c hd _ _ _
    have := deg_pos s; have := deg_pos c; omega
  | succ n ih =>
    intro s c hd hin hcn hle
    have hjunk : ∀ (x : Term), junkAP x = true → hdLe x c = true → False := by
      intro x hx hxc
      have hx' : le x c = true := by
        cases x with
        | M => exact hxc
        | omg _ => exact hxc
        | psi _ _ => exact hxc
        | Z _ => exact hxc
        | zero => exact Bool.noConfusion hx
        | add _ _ => exact Bool.noConfusion hx
        | phi _ _ => exact Bool.noConfusion hx
      simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at hx'
      rcases hx' with h1 | h1
      · rw [h1] at hx
        cases c <;> first | exact Bool.noConfusion hx | exact Bool.noConfusion hcn
      · rw [show lt x c = false from lt_junkAP_cnv c hcn _ x hx] at h1
        exact Bool.noConfusion h1
    cases s with
    | zero => rfl
    | M => exact absurd (hjunk M rfl hle) (by simp)
    | omg a => exact absurd (hjunk (omg a) rfl hle) (by simp)
    | psi k a => exact absurd (hjunk (psi k a) rfl hle) (by simp)
    | Z a => exact absurd (hjunk (Z a) rfl hle) (by simp)
    | add c' d' =>
      obtain ⟨hap, hinc, hind⟩ := inT_add hin
      have hdd : hdLe d' c' = true := hdLe_of_inT_add hin
      have hcc : hdLe c' c = true := by rw [hdLe_of_isAP hap]; exact hle
      have hdegc : c'.deg + c.deg ≤ n := by
        have := deg_pos d'
        have h2 : 1 + c'.deg + d'.deg + c.deg ≤ n + 1 := hd
        omega
      have hcnc : CNV c' = true := ih c' c hdegc hinc hcn hcc
      have hdegd : d'.deg + c'.deg ≤ n := by
        have := deg_pos c
        have h2 : 1 + c'.deg + d'.deg + c.deg ≤ n + 1 := hd
        omega
      have hcnd : CNV d' = true := ih d' c' hdegd hind hcnc hdd
      show (c'.isAP && CNV c' && CNV d' && hdLe d' c') = true
      rw [hcnc, hcnd, hdd, hap]; rfl
    | phi p q =>
      obtain ⟨hinp, hinq⟩ := inT_phi hin
      have hle' : le (phi p q) c = true := hle
      simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at hle'
      rcases hle' with h1 | h1
      · rw [h1]; exact hcn
      · cases c with
        | zero =>
          rw [show lt (phi p q) zero = false from ltF_right_zero _ _] at h1
          exact Bool.noConfusion h1
        | M => exact Bool.noConfusion hcn
        | omg _ => exact Bool.noConfusion hcn
        | psi _ _ => exact Bool.noConfusion hcn
        | Z _ => exact Bool.noConfusion hcn
        | add u v =>
          obtain ⟨_, hcnu, _, _⟩ := cnv_add hcn
          rw [lt_atom_add rfl] at h1
          have hdeg : (phi p q).deg + u.deg ≤ n := by
            have := deg_pos v
            have h2 : (phi p q).deg + (1 + u.deg + v.deg) ≤ n + 1 := hd
            omega
          exact ih (phi p q) u hdeg hin hcnu h1
        | phi x b =>
          obtain ⟨hcx, hcb⟩ := cnv_phi hcn
          have hne : phi p q ≠ phi x b := by
            intro hc; rw [hc, lt_irrefl] at h1; exact Bool.noConfusion h1
          rw [lt_phi_phi hne] at h1
          have hdp := deg_pos p; have hdq := deg_pos q
          have hdx := deg_pos x; have hdb := deg_pos b
          have hdegs : (1 + p.deg + q.deg) + (1 + x.deg + b.deg) ≤ n + 1 := hd
          have epq : (phi p q).deg = 1 + p.deg + q.deg := rfl
          have exb : (phi x b).deg = 1 + x.deg + b.deg := rfl
          by_cases hpx : p = x
          · rw [if_pos hpx] at h1
            have hcnq : CNV q = true := by
              by_cases hqz : q = zero
              · rw [hqz]; rfl
              · exact ih q b (by omega) hinq hcb (hdLe_of_lt_cnv b hcb q hqz hinq h1)
            show (CNV p && CNV q) = true
            rw [hcnq, hpx, hcx]; rfl
          · rw [if_neg hpx] at h1
            by_cases hpl : lt p x = true
            · have hcnp : CNV p = true := by
                by_cases hpz : p = zero
                · rw [hpz]; rfl
                · exact ih p x (by omega) hinp hcx (hdLe_of_lt_cnv x hcx p hpz hinp hpl)
              rw [if_pos hpl] at h1
              have hcnq : CNV q = true := by
                by_cases hqz : q = zero
                · rw [hqz]; rfl
                · exact ih q (phi x b) (by omega) hinq hcn
                    (hdLe_of_lt_cnv (phi x b) hcn q hqz hinq h1)
              show (CNV p && CNV q) = true
              rw [hcnp, hcnq]; rfl
            · rw [if_neg hpl] at h1
              exact ih (phi p q) b (by omega) hin hcb (by rw [hdLe_of_isAP rfl]; exact h1)

/-- **BELOW A VEBLEN NORMAL FORM THERE IS NOTHING BUT VEBLEN NORMAL FORMS.** -/
theorem cnv_of_lt_cnv {s y : Term} (hin : inT s = true) (hcn : CNV y = true)
    (hlt : lt s y = true) : CNV s = true := by
  by_cases hz : s = zero
  · rw [hz]; rfl
  · exact cnv_of_inT_hdLe (s.deg + y.deg) s y (Nat.le_refl _) hin hcn
      (hdLe_of_lt_cnv y hcn s hz hin hlt)

/-- The relation at its FINAL width: `inT` on the predecessor, not `CNV`.  Fixing this
    now is what makes step 1 a literal sub-statement of the eventual
    `∀ t, inT t → Acc RT t`, so that the `ψ` steps extend it rather than restate it. -/
def RT (x y : Term) : Prop := inT x = true ∧ lt x y = true

private theorem acc_RT_of_acc_RV : ∀ (t : Term), Acc RV t → CNV t = true → Acc RT t := by
  intro t ht
  induction ht with
  | intro t _ IH =>
    intro hcnt
    exact Acc.intro _ (fun y hy =>
      IH y ⟨cnv_of_lt_cnv hy.1 hcnt hy.2, hy.2⟩ (cnv_of_lt_cnv hy.1 hcnt hy.2))

/-- **acc_cnv AT THE `inT` RELATION.** -/
theorem acc_cnv_inT (t : Term) (h : CNV t = true) : Acc RT t :=
  acc_RT_of_acc_RV t (acc_cnv t h) h

/-- **THE FORM THE ROAD CONSUMES:** every genuine term of 𝔗(M) below a Veblen normal
    form is accessible, with no fragment hypothesis on the term itself. -/
theorem acc_inT_below_cnv {v : Term} (hv : CNV v = true) (t : Term)
    (hin : inT t = true) (hlt : lt t v = true) : Acc RT t :=
  acc_cnv_inT t (cnv_of_lt_cnv hin hv hlt)

/-! Receipts for §15.1's calibration. -/

#guard CNV (psi (Z zero) zero) == false        -- Γ₀ is the supremum, not a member
#guard inT (psi (Z zero) zero) == true
#guard lt (phi one zero) (psi (Z zero) zero) == true          -- ε₀ < Γ₀
#guard CNV (phi (phi one zero) zero) == true                  -- φ̄(ε₀,0) is still CNV …
#guard lt (phi (phi one zero) zero) (psi (Z zero) zero) == true   -- … and still below Γ₀
#guard lt (add zero M) one == true             -- the positive control: without `inT` …
#guard inT (add zero M) == false               -- … `0 ⊕ M` is below `1` and not a CNV
#guard CNV (add zero M) == false

/-! ### §8 receipts (samples of the measurements quoted above) -/

-- STAGE 3 needs `inT`, and the conjunct it needs is `κ ∈ R` of 2.1(vi):
-- these two terms are distinct and incomparable, and they fail `inT` only there.
#guard lt (psi M zero) (psi (psi M zero) zero) == false
#guard lt (psi (psi M zero) zero) (psi M zero) == false
#guard (M : Term).isR == false
#guard inT (psi M zero) == false

-- With an `R` head the corresponding pair is `inT` and IS comparable.
#guard inT (psi (Z zero) zero) == true
#guard inT (psi (Z (Z zero)) zero) == true
#guard lt (psi (Z zero) zero) (psi (Z (Z zero)) zero) == true
#guard lt (psi (Z (Z zero)) zero) (psi (Z zero) zero) == false

-- K_κ (2.1(vi)) BITES at degree 8 — the first term of the language it rejects, and why.
-- (§8 item 3 used to record K_κ as UNTESTED; this is the receipt that it no longer is.)
#guard (psi (Z zero) (psi (Z zero) (Z zero)) : Term).deg == 8
#guard inT (psi (Z zero) (psi (Z zero) (Z zero))) == false
#guard inT (psi (Z zero) (Z zero)) == true            -- the argument is a legal term
#guard (Z zero : Term).isR == true                    -- ... and the head is regular
#guard Kset (Z zero) (psi (Z zero) (Z zero)) == [Z zero]
#guard lt (Z zero) (psi (Z zero) (Z zero)) == false    -- so 2.1(vi)'s `K_κ α < α` FAILS

end Evidence.WF
