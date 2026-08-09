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
    (inversion lemmas) plus transitivity of `lt`, neither of which is proved
    anywhere in this repository yet.
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

/-! ## §6 TRANSITIVITY — the feasibility map  (D2, step 2; NOTHING PROVED BELOW)

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

end Evidence.WF
