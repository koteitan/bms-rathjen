/-
TM/FS.lean — fundamental sequences for 𝔗(M)

IMPORTANT: [R91] contains no definition of fundamental sequences.  This file is a
design choice of this repository.  It follows the standard route of reading the
cofinal sequences off the closure structure of the sets C_κ(α,β) of [R90] (what
each set is closed under) — the same shape as Buchholz-style systems and as §4 of
p-adic-lover-bot's pair-sequence paper.  Checking E3 (the expansion of a matrix
against the fundamental sequence of its term) is what validates this definition.

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

/-- Does the semantic argument of φ̄ a b become a successor b+1 (case analysis of [R91] 2.7)? -/
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

end Term
end TM
