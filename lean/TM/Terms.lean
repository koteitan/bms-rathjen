/-
TM/Terms.lean — the terms of Rathjen's notation system 𝔗(M)

Primary source: M. Rathjen, "Proof-theoretic analysis of KPM",
Archive for Mathematical Logic 30 (1991) 377–403, §2 (pp. 382–384).
Cited below as [R91]; definition numbers are those of that paper.

[R91] §2: 𝔗(M) is a lightweight variant of T(M) of [R90] in which
  1. the terms Φαβ are omitted, and
  2. the hierarchy χ is replaced by the single function Z (= α ↦ χ_α(0)).

Term constructors ([R91] 2.1):
  0, M
  ⊕(α₁,…,αₙ)   (n ≥ 2, αᵢ ∈ AP, αₙ ≤ … ≤ α₁)     formal sum
  ω̄^α          (M < α)                            additively principal above M
  φ̄αβ          (α, β < M)                         binary Veblen (raw)
  ψκα          (κ ∈ R, α < M, K_κ α < α)          collapsing function
  Zα                                               names of regulars (α ↦ χ_α(0))

⊕ is encoded by a right-nested binary `add`:
  ⊕(α₁,…,αₙ) = add α₁ (add α₂ (… (add α_{n-1} αₙ)))
The formation conditions (components in AP, descending) are checked by `inT`
in TM/NF.lean.
-/

namespace TM

inductive Term where
  | zero              -- 0
  | M                 -- M (the least weakly Mahlo cardinal)
  | add (a b : Term)  -- right-nested encoding of ⊕: `a` is an AP component, `b` the rest
  | omg (a : Term)    -- ω̄^a
  | phi (a b : Term)  -- φ̄ a b
  | psi (k a : Term)  -- ψ_k a
  | Z (a : Term)      -- Z a
deriving DecidableEq, Repr

namespace Term

/-- The degree Gα ([R91] 2.4): the number of symbols 0, M, ⊕, ω̄, φ̄, ψ, Z.
    Strictly, a chain of ⊕ counts as one symbol, but this is only used as an
    upper bound for recursion fuel, so counting one per `add` is fine
    (it only overestimates the true Gα). -/
def deg : Term → Nat
  | zero => 1
  | M => 1
  | add a b => 1 + a.deg + b.deg
  | omg a => 1 + a.deg
  | phi a b => 1 + a.deg + b.deg
  | psi k a => 1 + k.deg + a.deg
  | Z a => 1 + a.deg

/-- Shape of the additively principal terms AP
    ([R91] 2.1: AP = {M} ∪ {ω̄^α} ∪ {φ̄αβ} ∪ SC). -/
def isAP : Term → Bool
  | zero => false
  | add _ _ => false
  | _ => true

/-- Shape of the strongly critical terms SC ([R91] 2.1: SC = {M} ∪ {ψκα} ∪ {Zα}). -/
def isSC : Term → Bool
  | M => true
  | psi _ _ => true
  | Z _ => true
  | _ => false

/-- Shape of the regular terms R ([R91] 2.1 (vii): R = {Zα}). -/
def isR : Term → Bool
  | Z _ => true
  | _ => false

/-- Printing (for debugging and table generation): ⊕ as `+`, the rest as named forms. -/
def toStr : Term → String
  | zero => "0"
  | M => "M"
  | add a b => a.toStr ++ "+" ++ b.toStr
  | omg a => "w^(" ++ a.toStr ++ ")"
  | phi a b => "phi(" ++ a.toStr ++ "," ++ b.toStr ++ ")"
  | psi k a => "psi_(" ++ k.toStr ++ ")(" ++ a.toStr ++ ")"
  | Z a => "Z(" ++ a.toStr ++ ")"

end Term
end TM
