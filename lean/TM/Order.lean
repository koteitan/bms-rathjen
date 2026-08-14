/-
TM/Order.lean — the order < and the map * of 𝔗(M) ([Rathjen, 1991] 2.2, 2.3)

The 16 clauses of [Rathjen, 1991] 2.3 are implemented as a recursive decision procedure by
case analysis on the shapes of the terms.  Since * ([Rathjen, 1991] 2.2) uses the order (max)
and the order uses * (κ⁻ = δ*), the two are mutually recursive.  Termination is
secured by fuel (an upper bound on the recursion depth): every recursive call
strictly decreases the sum of the degrees of the two arguments, so the sum of the
degrees is enough fuel.

The clause each branch implements is named in its comment.  Completeness of the
decision (trichotomy) corresponds to a theorem of [Rathjen, 1991] and is left as future work;
here the priority is a faithful transcription as a computation.
-/
import TM.Terms

namespace TM
namespace Term

mutual

/-- α* ([Rathjen, 1991] 2.2).  `fuel` bounds the depth of the mutual recursion. -/
def starF : Nat → Term → Term
  | 0, _ => zero
  | fuel + 1, t =>
    match t with
    | zero => zero                       -- 2.2(i): 0* = 0
    | M => zero                          -- 2.2(i): M* = 0
    | add a b =>                         -- 2.2(ii): ⊕(…)* = max(αᵢ*)
      let x := starF fuel a
      let y := starF fuel b
      if ltF fuel x y then y else x
    | omg a => starF fuel a              -- 2.2(iii): (ω̄^α)* = α*
    | phi a b =>                         -- 2.2(iv): (φ̄αβ)* = max(α*, β*)
      let x := starF fuel a
      let y := starF fuel b
      if ltF fuel x y then y else x
    | psi k a => psi k a                 -- 2.2(v): α* = α for α ∈ SC, α < M
    | Z a => Z a                         -- 2.2(v)

/-- Decision of the order s < t ([Rathjen, 1991] 2.3). -/
def ltF : Nat → Term → Term → Bool
  | 0, _, _ => false
  | fuel + 1, s, t =>
    if s == t then false else
    match s, t with
    -- 2.3.1: 0 ≠ α ⟹ 0 < α
    | zero, _ => true
    | _, zero => false
    -- 2.3.16: two sums compare lexicographically along the spine
    --         (on a common prefix the shorter one is smaller)
    | add a b, add c d => if a == c then ltF fuel b d else ltF fuel a c
    -- 2.3.10: α₁ < γ ⟹ ⊕ < γ (components descend, so the head α₁ decides)
    | add a _, t' => ltF fuel a t'
    -- 2.3.11: γ ≤ α₁ ⟹ γ < ⊕
    | s', add c _ => s' == c || ltF fuel s' c
    -- 2.3.3: M < ω̄^γ (given the formation condition M < γ)
    | M, omg _ => true
    -- 2.3.2: φ̄, ψ, Z < M
    | M, _ => false
    | omg _, M => false
    | _, M => true
    -- 2.3.12: M < γ < δ ⟹ ω̄^γ < ω̄^δ
    | omg g, omg d => ltF fuel g d
    -- φ̄, ψ, Z < M < ω̄^δ (2.3.2, 2.3.3)
    | omg _, _ => false
    | _, omg _ => true
    -- 2.3.13: φ̄αβ < φ̄γδ
    | phi a b, phi c d =>
      if a == c then ltF fuel b d                       -- 13(ii)
      else if ltF fuel a c then ltF fuel b (phi c d)    -- 13(i)
      else phi a b == d || ltF fuel (phi a b) d         -- 13(iii): φ̄αβ ≤ δ
    -- 2.3.5: γ ∈ SC, α, β < γ ⟹ φ̄αβ < γ (here t' is a ψ or a Z)
    | phi a b, t' => ltF fuel a t' && ltF fuel b t'
    -- 2.3.4: γ ≤ α ∨ γ ≤ β ⟹ γ < φ̄αβ
    | s', phi c d => s' == c || s' == d || ltF fuel s' c || ltF fuel s' d
    -- 2.3.14: ψκα < ψπβ
    | psi k a, psi p b =>
      if k == p then ltF fuel a b                       -- 14(ii)
      else if ltF fuel k p then ltF fuel k (psi p b)    -- 14(i)
      else ltF fuel (psi k a) p                         -- 14(iii)
    -- ψ against Z: 2.3.8 (κ ≤ γ ⟹ ψκα < γ), otherwise 2.3.6 / 2.3.9 (via δ*)
    | psi k a, Z d =>
      if k == Z d || ltF fuel k (Z d) then true         -- 8
      else
        let dm := starF fuel d
        psi k a == dm || ltF fuel (psi k a) dm          -- 6: γ ≤ π⁻ ⟹ γ < π
    | Z d, psi k a =>
      if k == Z d || ltF fuel k (Z d) then false        -- 8 (other direction)
      else ltF fuel (starF fuel d) (psi k a)            -- 9: π⁻ < ψκα ∧ π < κ ⟹ π < ψκα
    -- 2.3.15: Zα < Zβ
    | Z a, Z b =>
      if ltF fuel a b then ltF fuel (starF fuel a) (Z b)          -- 15(i)
      else Z a == starF fuel b || ltF fuel (Z a) (starF fuel b)   -- 15(ii)

end

/-- Default fuel: every step strictly decreases the sum of the degrees, so this suffices. -/
def fuelOf (s t : Term) : Nat := 2 * (s.deg + t.deg) + 8

/-- s < t -/
def lt (s t : Term) : Bool := ltF (fuelOf s t) s t

/-- s ≤ t -/
def le (s t : Term) : Bool := s == t || lt s t

/-- α* -/
def star (t : Term) : Term := starF (2 * t.deg + 8) t

/-- κ⁻ ([Rathjen, 1991] 2.3): δ* when κ = Zδ.  Never used on terms outside R (returns 0). -/
def kminus : Term → Term
  | Z d => star d
  | _ => zero

end Term
end TM
