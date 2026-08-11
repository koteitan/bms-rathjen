/-
TM/Terms.lean — the terms of Rathjen's notation system 𝔗(M)

Primary source: M. Rathjen, "Proof-theoretic analysis of KPM",
Archive for Mathematical Logic 30 (1991) 377–403, §2 (pp. 382–384).
Cited below as [R91]; definition numbers are those of that paper.

[R91] §2: 𝔗(M) is a lightweight variant of T(M) of [R90] in which
  1. the terms Φαβ are omitted, and
  2. the hierarchy χ is replaced by the single function Z (= α ↦ χ_α(0)).

     **THIS SIMPLIFICATION LOSES THE Ω HIERARCHY, discovered 2026-08-12.**  In the
     source system χ is genuinely 2-ary and the two arguments do different jobs
     (P進大好きbot, "Cheatsheet on Properties of OCFs",
     <https://googology.fandom.com/wiki/User_blog:P進大好きbot/Cheatsheet_on_Properties_of_OCFs>):

         χ_0(α)   = Ω_{1+α}                    -- SECOND argument enumerates the Ω's
         χ_1(0)   = I, the least weakly inaccessible cardinal
         χ_1(1)   = I_2

     So the second argument walks the Ω hierarchy and the first walks degrees of
     inaccessibility.  Fixing the second to 0 keeps Ω = χ_0(0) = Z 0 and every
     χ_α(0), but **Ω_2 = χ_0(1) is not expressible**: `Z 1` is χ_1(0) = I, which is
     far larger.

     This is not hypothetical.  `Trans/Dict.lean` mapped Buchholz ψ₂(0) to `Z 1`
     where the sources say ε_{Ω+1}; §4 there proves the two differ.  Writing `Z 1`
     for "Ω_2" is the same confusion one level up.  Table rows at and above
     `(0,0)(1,1)(2,2)` live in the region that needs Ω_2, so their values cannot be
     stated correctly in this type as it stands.

     Repairing this means making χ 2-ary, which changes `Term` and therefore
     everything above it.  Not attempted here; recorded so that nobody reads
     `Z 1` as Ω_2.

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

**φ̄ ENUMERATES PAST ITS OWN FIXED POINTS, and this is the single fact in the file
that most often reads as a bug.**  φ̄0β is NOT ω^β in general: φ̄0 enumerates the
additively principal numbers SKIPPING the fixed points of ω^·, which is what gives
the notation system unique normal forms.  So

    φ̄(0,β) = ω^β        for β below the first fixed point
    φ̄(0,ε₀) = ω^(ε₀+1)  NOT ω^(ε₀) = ε₀
    lt ε₀ (φ̄(0,ε₀)) = true

BELOW A FIXED POINT THE TWO READINGS COINCIDE, so a function, a corpus or a reader
calibrated only there is insensitive to the difference and fails silently above it.
In one session (2026-08-10) this caused three separate defects, in three files, all
of which first looked like something else:
  * the table's row (0,0)(1,1)(1,0) reads as a duplicate of ε₀ unless you know it
    (Rows/TM.lean; the term is φ̄(0,ε₀) and the row is ω^(ε₀+1));
  * Evidence/WF.lean §15.18.2's split between `lim_clauses_repAdd` and core (C) is
    exactly "is the subscript a fixed point";
  * Evidence/SqV.lean's `omLog` encoded the ω-exponent WITHOUT the skip and was
    insensitive on all 234 corpus terms for the same reason.
Ask it of any new function whose domain reaches ε₀ — **and of any MEASURE you
induct on.**  A measure is the last place anyone thinks to check a notation
convention, and it was the fourth thing this fact broke: `Evidence/SqV.lean`'s
encoder needs an `omLog` clause BECAUSE of the skip, and that clause is exactly
the one on which `deg` — the obvious measure, and the one the repo's own
`ltF_stable` uses — fails.  It fails on four terms out of 169; the measure that
works is constructor nesting depth, whose worst margin on an adversarial corpus
is exactly 0.
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
