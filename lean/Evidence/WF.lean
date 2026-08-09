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
    (`le_of_not_lt`, `lt_of_not_le`, from comparability).  Above the fragment,
    i.e. once `ψ`/`Z` appear, they are still open; see §8.
  * The method here does NOT scale to ε₀: below ε₀ the exponents are themselves
    unbounded terms, so no fixed level bound exists and there is no vector to
    put a lexicographic order on.  ε₀ needs the classical structural argument
    (`Acc a → Acc b → Acc (ω^a + b)`), which is where transitivity becomes
    unavoidable.
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
(items 2 of "STAGING"); item 3 (the `ψ`/`Z` clauses) is still open.  Item 1
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

/-! ## §8 STAGE 3 — the `ψ`/`Z` clauses: what is left  (NOTHING PROVED BELOW)

This is a map in the style of §6, for §6's own item 3 — the version of §7 that
`cert_sound` needs.  It is not speculation: every claim marked MEASURED comes from
an exhaustive `#eval` sweep over ALL 3042 terms of degree ≤ 6 built from all seven
constructors, and a sample of each is kept as a `#guard` below.  Nothing here is a
theorem.

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

 1. STAGE 3 IS TRUE.  MEASURED: on all 171 terms of degree ≤ 6 satisfying `inT`,
    asymmetry, comparability and transitivity all hold, with no exception.  It is
    a cost question, not a risk question.

 2. `inT` BECOMES NECESSARY — the situation inverts.  On `Frag`, `inT` is dead
    weight (§7 proves everything without it).  Off `Frag` it is indispensable:
    MEASURED, the raw language has 792 incomparable pairs among those 3042 terms,
    and ZERO of them satisfy `inT`.  (Asymmetry, by contrast, held everywhere,
    `inT` or not — but §7's route to asymmetry goes through comparability, so
    that observation does not by itself make asymmetry cheaper.)

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
    HONEST CAVEAT: the K_κ conjunct could not be tested this way — at degree ≤ 6
    it removes no term at all (171 either way), so the sweep says NOTHING about
    it.  Do not read the table as "K_κ is dispensable"; it is untested.

 4. THE SPLIT THAT MAKES §8 TRACTABLE.  MEASURED: on the sub-language with `M`
    and `ω̄` but still no `ψ`/`Z` (556 terms of degree ≤ 6), asymmetry and
    comparability hold RAW — no `inT` needed, exactly as in `Frag`.  So:

      STAGE 3a  extend `Frag` to `Frag ∪ {M, ω̄}`, still `inT`-free.  Pure case
                bash: clauses 2.3.2 / 2.3.3 / 2.3.12 are constant or a single
                recursive call, and 2.3.5 / 2.3.4 are the `φ̄`-vs-`SC` pair.  The
                cost is the shape matrix, not the mathematics — `cmp_aux` goes
                from 9 shape pairs to 25 and `trans_aux` from 27 triples to 125,
                so factor out a "constant clause" lemma before bashing or the
                file triples in size for no content.

      STAGE 3b  `ψ` and `Z`, with `inT`.  This is where the real work is: the
                clauses routing through `starF` (2.3.6 / 2.3.8 / 2.3.9 / 2.3.15)
                need, beyond §7's pattern, that `α*` behaves.  MEASURED on all 171
                `inT` terms: `le (star d) d` and `star d ≤ Z d` both hold — those
                are precisely the two `starF` facts §6's map asked for, and they
                are the first things to prove in 3b.

WHAT WOULD FALSIFY THIS MAP: a pair of `inT` terms of degree ≥ 7 that is
incomparable, or a `starF` counterexample to `le (star d) d`.  Extending the sweep
past degree 6 is the cheapest possible check and should be run before 3b is
started — the sweep is ~20 lines of `#eval` and costs seconds. -/

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

end Evidence.WF
