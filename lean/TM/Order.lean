/-
TM/Order.lean — 𝔗(M) の順序 < と写像 * ([R91] 2.2, 2.3)

[R91] 2.3 の 16 clauses を、項の形の場合分けによる再帰的判定手続きとして
実装する。* ([R91] 2.2) が順序 (max) を使い、順序が * (κ⁻ = δ*) を使うため
相互再帰になる。停止性は fuel (再帰深度の上界) で保証する。
各再帰呼び出しで両引数の次数の和が真に減るので、fuel = deg の和 で十分。

clause との対応は各分岐のコメントに記す。判定の完全性 (三分律) は
[R91] の定理に対応する将来の証明課題であり、ここでは計算手続きとして
忠実に書き下すことを優先する。
-/
import TM.Terms

namespace TM
namespace Term

mutual

/-- α* ([R91] 2.2)。fuel は相互再帰の深度上界。 -/
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
    | psi k a => psi k a                 -- 2.2(v): α* = α (α ∈ SC, α < M)
    | Z a => Z a                         -- 2.2(v)

/-- 順序 s < t ([R91] 2.3) の判定 -/
def ltF : Nat → Term → Term → Bool
  | 0, _, _ => false
  | fuel + 1, s, t =>
    if s == t then false else
    match s, t with
    -- 2.3.1: 0 ≠ α ⟹ 0 < α
    | zero, _ => true
    | _, zero => false
    -- 2.3.16: ⊕ 同士はスパイン上の辞書式 (接頭辞なら短い方が小)
    | add a b, add c d => if a == c then ltF fuel b d else ltF fuel a c
    -- 2.3.10: α₁ < γ ⟹ ⊕ < γ (成分は降順なので先頭 α₁ だけ見ればよい)
    | add a _, t' => ltF fuel a t'
    -- 2.3.11: γ ≤ α₁ ⟹ γ < ⊕
    | s', add c _ => s' == c || ltF fuel s' c
    -- 2.3.3: M < ω̄^γ (形成条件 M < γ を前提)
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
    -- 2.3.5: γ ∈ SC, α, β < γ ⟹ φ̄αβ < γ (t' は ψ か Z)
    | phi a b, t' => ltF fuel a t' && ltF fuel b t'
    -- 2.3.4: γ ≤ α ∨ γ ≤ β ⟹ γ < φ̄αβ
    | s', phi c d => s' == c || s' == d || ltF fuel s' c || ltF fuel s' d
    -- 2.3.14: ψκα < ψπβ
    | psi k a, psi p b =>
      if k == p then ltF fuel a b                       -- 14(ii)
      else if ltF fuel k p then ltF fuel k (psi p b)    -- 14(i)
      else ltF fuel (psi k a) p                         -- 14(iii)
    -- ψ 対 Z: 2.3.8 (κ ≤ γ ⟹ ψκα < γ)、さもなくば 2.3.6/2.3.9 (δ* 経由)
    | psi k a, Z d =>
      if k == Z d || ltF fuel k (Z d) then true         -- 8
      else
        let dm := starF fuel d
        psi k a == dm || ltF fuel (psi k a) dm          -- 6: γ ≤ π⁻ ⟹ γ < π
    | Z d, psi k a =>
      if k == Z d || ltF fuel k (Z d) then false        -- 8 (逆向き)
      else ltF fuel (starF fuel d) (psi k a)            -- 9: π⁻ < ψκα ∧ π < κ ⟹ π < ψκα
    -- 2.3.15: Zα < Zβ
    | Z a, Z b =>
      if ltF fuel a b then ltF fuel (starF fuel a) (Z b)          -- 15(i)
      else Z a == starF fuel b || ltF fuel (Z a) (starF fuel b)   -- 15(ii)

end

/-- fuel の既定値: 再帰の各段で両引数の次数和が真に減るので、これで十分 -/
def fuelOf (s t : Term) : Nat := 2 * (s.deg + t.deg) + 8

/-- s < t -/
def lt (s t : Term) : Bool := ltF (fuelOf s t) s t

/-- s ≤ t -/
def le (s t : Term) : Bool := s == t || lt s t

/-- α* -/
def star (t : Term) : Term := starF (2 * t.deg + 8) t

/-- κ⁻ ([R91] 2.3): κ = Zδ のとき δ*。R の形でなければ使わない (0 を返す)。 -/
def kminus : Term → Term
  | Z d => star d
  | _ => zero

end Term
end TM
