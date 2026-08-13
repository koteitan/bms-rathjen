/-
TM/FS.lean — fundamental sequences for 𝔗(M)

IMPORTANT: [R91] contains no definition of fundamental sequences.  This file is a
design choice of this repository.  It follows the standard route of reading the
cofinal sequences off the closure structure of the sets C_κ(α,β) of [R90] (what
each set is closed under) — the same shape as Buchholz-style systems and as §4 of
p-adic-lover-bot's pair-sequence paper.  Checking E3 (the expansion of a matrix
against the fundamental sequence of its term) is what validates this definition.

Since 2026-08-13 there is also an EXTERNAL witness for the region below Γ₀: twelve
rows of the expansion column of P進大好きbot's "Rathjen-type Ordinal Notation" agree
with `fsN` here.  See the provenance section at the bottom of this file — including
the dictionary, which is not the identity.

Contents:
  kindT : classification into zero / successor / limit
          (a term is a successor when its additive tail is 1 = φ̄00)
  predT : predecessor of a successor
  cofT  : cofinality marker of a limit term
          (ω = countable; Z δ or M = uncountable regular)
  fsT   : term-indexed fundamental sequence t[s]
          (at a position of uncountable regular cofinality π one substitutes s < π)
  fsN   : Nat-indexed fundamental sequence t[n] (cofinality ω)

Rationale, case by case:
  ⊕      : propagate into the last component (the standard rule for sums).
  ω̄^γ   : γ successor → ω̄^{γ'}·n; γ limit → ω̄^{γ[·]} (propagate into the exponent).
  φ̄ a b : by the correspondence φ̄αβ = φα(β°) of [R91] 2.7, first recover the
           semantic argument
             β° = β+1  (b a fixed-point shape plus a finite part, or b = 0 ∧ a ∈ SC)
             β         (otherwise)
           and then apply the standard fundamental sequences of the Veblen hierarchy:
             φ_{α+1}(0)[n]   = φ_α^{(n)}(0)
             φ_α(β+1)[n]     = φ_{α'}^{(n)}(φ_α(β)+1)   (α = α'+1)
             φ_α(β+1)[n]     = φ_{α[n]}(φ_α(β)+1)       (α limit)
             φ_α(β)[·]       = φ_α(β[·])                 (β limit)
             φ_0(β+1)[n]     = ω^β · n
  ψ κ α : the cofinal sequence of the C-closure.
           α = 0    → iterate x ↦ φ_x(0) from the seed `seed(κ)` (Γ-closure),
                      where seed(Z0) = 1 and seed(Z(δ+1)) = Zδ + 1
                      (take the φ-closure above the largest regular term below κ).
                      For δ a limit, ψ_{Zδ}(0)[·] = Z(δ[·]) instead, since the
                      image of Z is cofinal (a φ-closure cannot cross the gap
                      between regulars).
           α successor → iterate x ↦ φ_x(0) from ψκα' + 1.
           α limit, cof α < κ → ψ κ (α[·]) (pass the index through).
           α limit, cof α ≥ κ → diagonalize: t[0] = ψκ(α[0]),
                      t[n+1] = ψκ(α[t[n]]) (feed the previous value as the index).
  Z δ, M : regular.  `fsT` is the identity (κ[s] = s); `fsN` is undefined (junk 0).

`fsN` returns junk 0 only when applied to a term whose cofinality is not countable.
The per-row checks (E3 together with `inT`) detect any such contamination.
-/
import TM.NF

namespace TM
namespace Term

/-- Classification into zero, successor and limit. -/
inductive KindT | isZero | isSucc | isLim
deriving DecidableEq, Repr

/-- A term is a successor exactly when the tail of its additive form is 1 (= φ̄00). -/
def kindT (t : Term) : KindT :=
  match t with
  | zero => .isZero
  | _ => if (toList t).getLast? == some one then .isSucc else .isLim

/-- The predecessor `s` of a successor t = s + 1 (zero on non-successors). -/
def predT (t : Term) : Term :=
  let l := toList t
  if l.getLast? == some one then ofList l.dropLast else zero

/-- Is `g` of a-fixed-point shape: g ∈ SC ∧ a < g, or g = φ̄cδ ∧ a < c ([R91] 2.6(vi))? -/
def isFP (a g : Term) : Bool :=
  (g.isSC && lt a g) ||
  (match g with
   | phi c _ => lt a c
   | _ => false)

/-- Does the semantic argument of φ̄ a b become a successor b+1 (case analysis of [R91] 2.7)?

    [R91] 2.7 verbatim, for α, β < M:

        φ̄αβ = φ_α(1)      if β = 0 and α ∈ SC
            = φ_α(β+1)    if β = γ+n and φ_αγ = γ
            = φ_α(β)      otherwise

    The two disjuncts below are those two cases, in that order.

    KNOWN GAP, recorded rather than patched.  Taken literally the lemma makes φ̄α0 and
    φ̄α1 denote the SAME ordinal φ_α(1) whenever α ∈ SC: case 1 gives φ_α(1) for β = 0,
    and case 2 does not fire at β = 1 because neither 0 nor 1 is a fixed point of φ_α.
    That cannot be right — 2.8's proof builds an F : 𝔗(M) → T(M) order-preserving for <
    and ∈, and 2.3.13(ii) makes φ̄α0 < φ̄α1 — so the shift must persist above β = 0, i.e.
    the second disjunct should read `a.isSC`.  Independent evidence: translating to
    naruyoko's implementation of P進大好きbot's Rathjen-type notation, the literal
    reading collapses six terms onto four and disagrees on 8 of 742 adjacent pairs,
    while `a.isSC` collapses none and disagrees on 0 of 742.

    NOT CHANGED, because the change is unreachable from R1 and `fsN` and some sixty
    StageB/ProofsB lemmas are built on this definition.  MEASURED (the guards live in
    `Trans/DictInv.lean`, the only file that can see all the populations at once): the
    two readings differ only on φ̄(A,B) with A ∈ SC and B ≠ 0, and that shape occurs in
    0 of the 51 table rows, 0 of the 750 CNV-corpus terms, and 0 of a 336-term pool of
    `dict` values.  It occurs in 12 of the 89 terms of a corpus above Ω, and 4 of those
    12 do have a Buchholz preimage — so the gap is not outside `dict`'s image, only
    above everything R1 measures.  `dict` itself cannot see it at all: its only route
    here is `logOm`'s `φ̄(0,·)` clause, and the two readings agree at α = 0. -/
def phiShifted (a b : Term) : Bool :=
  isFP a (splitFin b).1 || (b == zero && a.isSC)

/-- t · n (n copies of t as a formal sum; assumes t ∈ AP). -/
def mulNat (t : Term) (n : Nat) : Term := ofList (List.replicate n t)

/-- n-fold iteration of x ↦ φ_c(x) starting from `base`. -/
def iterPhiAt (c base : Term) : Nat → Term
  | 0 => base
  | n + 1 => phiNF c (iterPhiAt c base n)

/-- n-fold iteration of x ↦ φ_x(0) starting from `base`: the cofinal sequence of a Γ-closure. -/
def iterGamma (base : Term) : Nat → Term
  | 0 => base
  | n + 1 => phiNF (iterGamma base n) zero

/-- Cofinality marker of a limit term: `omega` (countable) or `Z δ` / `M` (uncountable regular). -/
def cofT : Term → Term
  | M => M
  | Z d => Z d
  | add _ b => cofT b
  | omg g => if kindT g == .isSucc then omega else cofT g
  | phi a b =>
    if phiShifted a b || kindT b == .isSucc then
      -- the semantic argument is a successor, so the cofinality is decided on the `a` side
      if kindT a == .isLim then cofT a else omega
    else if kindT b == .isLim then cofT b
    else -- b = 0 (a ≠ 0, a ∉ SC)
      if kindT a == .isLim then cofT a else omega
  | psi k a =>
    match kindT a with
    | .isLim => let p := cofT a; if lt p k then p else omega
    | _ =>
      -- α が零・後続でも ω とは限らない。ψκα の共終度は κ 自身の添字で決まる。
      -- P進大好きbot 氏の `dom` の ψ 節 (index(κ) = (λ,c), c ≠ 0 の場合) を当方の
      -- `Z δ` で読むと、**δ が極限なら cof(ψ_{Zδ}α) = cof δ** である。
      --     ψ_{Z Ω}(0)   cof = Ω     (2026-08-13 まで ω と答えていた)
      --     ψ_{Z (Ω+1)}(0), ψ_{Z ω}(0), ψ_{Z 2}(0), ψ_Ω(0)   cof = ω
      -- 19 例で同氏の独立実装と突き合わせ、現行 16/19 → 19/19。
      match k with
      | Z d => if kindT d == .isLim then (let p := cofT d; if lt p M then p else omega)
               else omega
      | _ => omega
  | _ => omega   -- never used on zero or successors

/-- Term-indexed fundamental sequence t[s]
    (for `cofT t` an uncountable regular π, with s < π intended). -/
def fsT : Term → Term → Term
  | add a b, s => plus a (fsT b s)
  | omg g, s => omegaNF (fsT g s)      -- γ limit; boundaries (exponent = M etc.) collapse via ω^
  | phi a b, s =>
    if phiShifted a b || kindT b == .isSucc then
      -- successor argument: the cofinality comes from `a` (a limit, uncountable)
      let c := if phiShifted a b then b else predT b
      phiNF (fsT a s) (plus (phiNF a c) one)
    else if kindT b == .isLim then phiNF a (fsT b s)
    else phiNF (fsT a s) zero          -- b = 0, a limit
  | psi k a, s => psi k (fsT a s)      -- propagation for cof α < κ
  | Z _, s => s                        -- regular: κ[s] = s
  | M, s => s
  | _, _ => zero                       -- junk (never used)

/-- Seed of the cofinal sequence of ψκ0: just above the largest regular term below κ. -/
def psiSeed : Term → Term
  | Z zero => one                      -- there is no regular term below Ω
  | Z d =>
    match kindT d with
    | .isSucc => plus (Z (predT d)) one
    | _ => zero                        -- for δ a limit, `fsN` uses Z(δ[n]) instead
  | _ => zero

/-- Nat-indexed fundamental sequence t[n] (assumes `cofT t = ω`). -/
def fsN : Term → Nat → Term
  | add a b, n => plus a (fsN b n)
  | omg g, n =>
    (match kindT g with
     | .isSucc => mulNat (omegaNF (predT g)) n   -- ω̄^{γ'+1}[n] = ω^{γ'}·n
     | _ => omegaNF (fsN g n))                   -- into the exponent (boundaries collapse via ω^)
  | phi a b, n =>
    if phiShifted a b || kindT b == .isSucc then
      -- the semantic argument is a successor c+1: base = φ_a(c) + 1
      let c := if phiShifted a b then b else predT b
      let base := plus (phiNF a c) one
      match kindT a with
      | .isZero => mulNat (omegaNF c) n          -- ω^{c+1}[n] = ω^c · n
      | .isSucc => iterPhiAt (predT a) base n    -- φ_{a'}^{(n)}(base)
      | .isLim => phiNF (fsN a n) base           -- φ_{a[n]}(base)
    else if kindT b == .isLim then phiNF a (fsN b n)
    else
      -- b = 0 (a ≠ 0, a ∉ SC): φ_a(0)
      (match kindT a with
       | .isSucc => iterPhiAt (predT a) zero n
       | .isLim => phiNF (fsN a n) zero
       | .isZero => zero)                        -- φ̄00 = 1 is a successor (unreachable)
  | psi k a, n =>
    (match kindT a with
     | .isZero =>
       (match k with
        | Z d =>
          (match kindT d with
           | .isLim => Z (fsN d n)               -- ψ_{Zδ}0[n] = Z(δ[n]) for δ a limit
           | _ => iterGamma (psiSeed k) n)       -- Γ-closure
        | _ => zero)
     | .isSucc => iterGamma (plus (psi k (predT a)) one) n
     | .isLim =>
       let p := cofT a
       if p == omega then psi k (fsN a n)        -- countable cofinality: propagate
       else if lt p k then zero                  -- cof α < κ: outside the scope of fsN (junk)
       else
         -- diagonalization: t[0] = ψκ(α[0]), t[n+1] = ψκ(α[t[n]])
         (match n with
          | 0 => psi k (fsT a zero)
          | m + 1 => psi k (fsT a (fsN (psi k a) m))))
  | _, _ => zero   -- never used on zero, successors, Z or M
  termination_by t n => (sizeOf t, n)
  decreasing_by all_goals simp_wf <;> omega

/-! ## Provenance check against an independent Rathjen-type notation (2026-08-13)

This file's header says [R91] has no fundamental sequences and that the definitions here
are a design choice of this repository.  They now have an external witness.

P進大好きbot, "Rathjen-type Ordinal Notation" (Googology Wiki, 2019, CC BY-SA 3.0),
<https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Rathjen-type_Ordinal_Notation>
defines `dom` and an expansion map for a system that extends Rathjen's, and its "Up to
Γ₀" analysis table lists (term, ordinal, expansion) triples.  Below `M` the systems should
agree, and on the twelve rows of that table where the expansion is unambiguous, they do.

DICTIONARY, and it is NOT the identity.  That source writes the PLAIN Veblen function
`φ⁰_a(b)`; this repository writes Rathjen's `φ̄`, which re-counts fixed points ([R91]
2.6(vi)).  The bridge is `phiNF`, verified here on three values whose answer is already
known — `phiNF 1 0 = φ̄(1,0) = ε₀`, `phiNF 0 (ε₀+1) = φ̄(0,ε₀)`, `phiNF 2 0 = φ̄(2,0) = ζ₀`.
Reading `φ⁰` as `φ̄` directly instead turns every fixed-point row into a spurious
disagreement; that mistake was made once here, see `Evidence/SqV.lean` §K3.20.

The right-hand sides below are HAND-TRANSLATED from that table's prose (`1+1+⋯`,
`φ⁰₀(⋯φ⁰₀(0)⋯)`), so they carry the risk of a reading error, not of a transcription error.
The Γ₀ row additionally required unfolding that source's `Γ⁰(s,n)` map, and its indices sit
one below ours (`ours[n] = Γ⁰(0, n+1)`).
-/

/-! ### The ψ region: the source's article agrees with this file

Its "Up to φ(1,0,0,0)" table gives `ψ_Ω(a)` for varying `a`, and its expansion column is
`Γ⁰(0, 1+1+⋯)` at `Γ₀`.  Unfolding its own `Γ⁰`:

    Γ⁰(0,0) = 0,  Γ⁰(0,1) = φ₀(0) = 1,  Γ⁰(0,2) = φ₁(0) = ε₀,  Γ⁰(0,3) = φ_{ε₀}(0)

which is `fsN` here, offset by one.  Pass-through (`ψ_Ω(ω)`), diagonalisation
(`ψ_Ω(Ω)`) and the successor seed (`ψ_Ω(Ω+1)`) agree as well.

The author's reference implementation (`padicBotRathjen`, reachable through
`scripts/padicbot-ref.js`) computes something else there — `fund(Γ₀, ·)` is
`2, ζ₀, φ_{ζ₀}(0), …`, two levels further along, and over 51 ψ-region terms it agrees
with `fsN` on 21.  Every difference is the Γ-closure seed.  Where the implementation and
the article disagree, the article is the definition, and it is the one that matches here.

Above `Ω` the implementation's sequences run through the `Ω` hierarchy
(`ψ_{χ₁(0)}(0)` expands by `φ¹_·(0)`), which this type cannot write at all: [R91] §2
collapses `χ` to `α ↦ χ_α(0)` so `Ω₂` has no term (`plan/chi-2ary.md`).  Nothing to adopt
there either.
-/

/-! ### `cofT` against the same source's `dom`

That source also defines a cofinality map `dom : OT → OT` with values `0` (zero), `1`
(successor), `ω` (countable limit) and `s` (uncountable regular).  This file splits the
same information across `kindT` and `cofT`, so put them back together and compare.

The `φ` clause must be read with the SEMANTIC second argument `β°` ([R91] 2.7), for the
usual reason.  The measurement below records what ignoring that costs, and the number is
the point: a rule that uses `b` instead of `β°` still agrees on 2460 of 2572 terms — it
breaks on 4%.  A corpus that did not reach fixed points would have certified it.

    our (kindT, cofT) against the source's rules    169 / 169,  0 unhandled
    CTRL "always ω"                                  99 / 169
    CTRL `b` in place of `β°`                       134 / 169
    CTRL `a` and `b` swapped                        149 / 169

  The corpus was 2572 terms until 2026-08-13 and agreed 2572/2572 — while `cofT` was
  wrong at `ψ_{Z Ω}(0)`.  The seeds had no composite `Z` index, so the defect was outside
  it.  It is smaller now and reaches further; the named guards below pin the witness.
-/

/-- The source's `dom`, rebuilt from `kindT` and `cofT`. -/
def domOf (t : Term) : Term :=
  if t == zero then zero
  else match kindT t with
       | .isSucc => one
       | .isZero => zero
       | .isLim  => cofT t

private def zeroOrOne (d : Term) : Bool := d == zero || d == one

/-- The source's clauses, written in this file's constructors.  `none` where the source
    says nothing about a shape this type has. -/
def domSpec (t : Term) : Option Term :=
  match t with
  | .zero => some zero
  | .add _ b => some (domOf b)
  | .Z _ => some t
  | .M => some t
  | .phi a b =>
      let bs := if phiShifted a b then plus b one else b
      let da := domOf a
      let db := domOf bs
      if zeroOrOne db then
        if zeroOrOne da then some (if da == zero && db == zero then one else omega)
        else some da
      else some db
  | .psi k a =>
      let da := domOf a
      if zeroOrOne da then
        -- α が零・後続の場合。κ = Z δ で δ が極限なら ω ではなく cof δ である。
        (match k with
         | .Z d => if kindT d == .isLim then (let p := cofT d; some (if lt p M then p else omega))
                   else some omega
         | _ => some omega)
      else if lt da k then some da else some omega
  | _ => none

-- **種に `Z` の複合添字を入れること。** 入れずに測ると `cofT` の ψ 節の欠陥
-- (`ψ_{Z Ω}(0)` の共終度が ω ではなく Ω) が corpus に現れず、2572/2572 が
-- 「合っている」ではなく「届いていない」を意味してしまう (2026-08-13 に実際そうなった)。
private def domPool0 : List Term :=
  [zero, one, phi one zero, phi zero one, Z zero, Z one, Z (Z zero),
   Z (plus (Z zero) one), Z (phi zero one), psi (Z zero) zero]
private def domGrow (p : List Term) : List Term :=
  (p ++ (p.flatMap fun x => p.map fun y => phi x y)
     ++ (p.flatMap fun x => p.map fun y => plus x y)
     ++ (p.map fun x => psi (Z zero) x) ++ (p.map fun x => psi (Z x) zero)).eraseDups
def domCorpus : List Term :=
  (domGrow domPool0).filter fun t => inT t && !(t == zero)

#guard domCorpus.all fun t => domSpec t == some (domOf t)

-- **名指しの証人。** 2026-08-13 まで `cofT` はここで `ω` と答えていた。
-- 独立実装 (`scripts/padicbot-ref.js`) は `Ω` と言う。corpus が届かなければ
-- 上の一致は「合っている」ではなく「見ていない」を意味するので、個別に固定する。
#guard cofT (psi (Z (Z zero)) zero) == Z zero          -- ψ_{Z Ω}(0) の共終度は Ω
#guard cofT (psi (Z zero) zero) == omega               -- ψ_Ω(0) は ω
#guard cofT (psi (Z (plus (Z zero) one)) zero) == omega -- ψ_{Z (Ω+1)}(0) は ω
#guard cofT (psi (Z (phi zero one)) zero) == omega      -- ψ_{Z ω}(0) は ω
#guard domCorpus.contains (psi (Z (Z zero)) zero)       -- 証人が母集団に居ること
#eval (domCorpus.length,
       domCorpus.countP fun t => domSpec t == some (domOf t),
       domCorpus.countP fun t => (domSpec t).isNone)
-- the three controls, as counts rather than as guards: each must be strictly below the
-- corpus size, and the middle one is the interesting number (see above).
#eval (domCorpus.countP fun t => omega == domOf t,
       domCorpus.countP fun t =>
         (match t with
          | .phi a b =>
              let da := domOf a; let db := domOf b
              if zeroOrOne db then
                (if zeroOrOne da then some (if da == zero && db == zero then one else omega)
                 else some da)
              else some db
          | _ => domSpec t) == some (domOf t),
       domCorpus.countP fun t =>
         (match t with | .phi a b => domSpec (phi b a) | _ => domSpec t) == some (domOf t))
#guard domCorpus.countP (fun t => omega == domOf t) < domCorpus.length

private def fsRow (t : Term) (l : List Term) : Bool :=
  (l.zipIdx.all fun p => fsN t p.2 == p.1)

-- The twelve rows of that table whose expansion column is unambiguous.
#guard
  let w := phi zero one
  let e0 := phi one zero
  let ww := phi zero w
  [ fsRow w [zero, one, ofNat 2, ofNat 3],                          -- ω        1+1+⋯
    fsRow (plus w one) [w, w, w],                                   -- ω+1      ω
    fsRow (plus w w) [w, plus w one, plus w (ofNat 2)],             -- ω+ω      ω+1+1+⋯
    fsRow (phi zero (ofNat 2)) [zero, w, plus w w],                 -- ω²       ω+ω+⋯
    fsRow ww [one, w, phi zero (ofNat 2), phi zero (ofNat 3)],      -- ω^ω      φ⁰₀(1+1+⋯)
    fsRow e0 [zero, one, w, ww],                                    -- ε₀       the tower
    fsRow (phi zero e0) [zero, e0, plus e0 e0],                     -- ω^(ε₀+1) ε₀+ε₀+⋯
    fsRow (phi one w) [e0, phi one one, phi one (ofNat 2)],         -- ε_ω      φ⁰₁(1+1+⋯)
    fsRow (phi one e0) [e0, phi one one, phi one w, phi one ww],    -- ε_{ε₀}   φ⁰₁(tower)
    fsRow (phi (ofNat 2) zero)                                      -- ζ₀       φ⁰₁(⋯φ⁰₁(0)⋯)
      [zero, e0, phi one e0, phi one (phi one e0)],
    fsRow (phi w zero)                                              -- φ_ω(0)   φ⁰_{1+1+⋯}(0)
      [one, e0, phi (ofNat 2) zero, phi (ofNat 3) zero],
    fsRow (psi (Z zero) zero)                                       -- Γ₀       Γ⁰(0,1+1+⋯)
      [one, e0, phi e0 zero, phi (phi e0 zero) zero] ].all id

-- Negative control.  Without it a `#guard` over `fsRow` cannot be told apart from one
-- that always says `true` — every list above could be empty and it would still pass.
#guard ! (fsRow (phi zero one) [one, one, one])

end Term
end TM
