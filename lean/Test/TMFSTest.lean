/-
Test/TMFSTest.lean — checks of the fundamental sequences

Comparison against the known fundamental sequences:
  ω[n] = n
  (ω^ω)[n] = ω^n
  ε₀[n] = 0, 1, ω, ω^ω, …                   (iterating φ₀)
  ω^{ε₀+1}[n] = ε₀·n
  Γ₀[n] = ψ_Ω(0)[n] = 1, ε₀, φ_{ε₀}(0), …   (iterating x ↦ φ_x(0))
  ψ_Ω(Ω)[n] = ψ(0), ψ(ψ(0)), …              (diagonalization)
  ψ_Ω(Ω·2)[n] = ψ(Ω), ψ(Ω+ψ(Ω)), …
Monotonicity t[n] < t[n+1] < t is then checked exhaustively over a sample.
-/
import Test.TMTest

namespace TM.Test
open TM.Term

def G0 : Term := psi Om zero

-- classification
#guard kindT zero = .isZero
#guard kindT one = .isSucc
#guard kindT (ofNat 3) = .isSucc
#guard kindT omega = .isLim
#guard kindT (plus omega one) = .isSucc
#guard kindT e0 = .isLim
#guard kindT M = .isLim
#guard predT (ofNat 3) = ofNat 2
#guard predT (plus omega one) = omega

-- cofinality
#guard cofT omega = omega
#guard cofT e0 = omega
#guard cofT G0 = omega
#guard cofT Om = Om
#guard cofT (add Om Om) = Om
#guard cofT (psi Om Om) = omega            -- diagonalization brings the cofinality down to ω
#guard cofT (psi Om (add Om Om)) = omega
#guard cofT (phi zero (add Om Om)) = Om    -- ω^{Ω·2} has cofinality Ω
#guard cofT (omg (plus M one)) = omega     -- ω̄^{M+1}[n] = M·n
#guard cofT (psi (Z one) zero) = omega

-- ω[n] = n
#guard fsN omega 0 = zero
#guard fsN omega 1 = one
#guard fsN omega 3 = ofNat 3

-- (ω^ω)[n] = ω^n
#guard fsN (phi zero omega) 0 = one
#guard fsN (phi zero omega) 2 = phi zero (ofNat 2)

-- ε₀[n]: 0, 1, ω, ω^ω
#guard fsN e0 0 = zero
#guard fsN e0 1 = one
#guard fsN e0 2 = omega
#guard fsN e0 3 = phi zero omega

-- ω^{ε₀+1}[n] = ε₀·n
#guard fsN (phi zero e0) 2 = add e0 e0

-- Γ₀ = ψ_Ω(0): 1, ε₀, φ_{ε₀}(0)
#guard fsN G0 0 = one
#guard fsN G0 1 = e0
#guard fsN G0 2 = phi e0 zero

-- ψ_Ω(α+1): φ-closure starting from ψ_Ω(α)+1
#guard fsN (psi Om one) 0 = plus G0 one
#guard fsN (psi Om one) 1 = phi (plus G0 one) zero

-- diagonalization of ψ_Ω(Ω): ψ(0), ψ(ψ(0))
#guard fsN (psi Om Om) 0 = G0
#guard fsN (psi Om Om) 1 = psi Om G0
#guard fsN (psi Om Om) 2 = psi Om (psi Om G0)

-- diagonalization of ψ_Ω(Ω·2): ψ(Ω), ψ(Ω+ψ(Ω))
#guard fsN (psi Om (add Om Om)) 0 = psi Om Om
#guard fsN (psi Om (add Om Om)) 1 = psi Om (plus Om (psi Om Om))

-- ψ_Ω(ω): propagation at countable cofinality
#guard fsN (psi Om omega) 2 = psi Om (ofNat 2)

-- ψ_{Z1}(0): φ-closure from Ω+1 (a Γ_{Ω+1}-like point)
#guard fsN (psi (Z one) zero) 0 = plus Om one
#guard fsN (psi (Z one) zero) 1 = phi (plus Om one) zero

-- ω̄^{M+1}[n] = M·n
#guard fsN (omg (plus M one)) 2 = add M M

-- addition: propagate into the last component
#guard fsN (plus e0 omega) 3 = plus e0 (ofNat 3)

/-! ## Exhaustive monotonicity check: t[n] < t[n+1] < t -/

def fsSample : List Term :=
  [ omega, phi zero omega, e0, phi zero e0, phi omega zero, phi e0 zero,
    G0, psi Om one, psi Om omega, psi Om G0, psi Om Om,
    psi Om (add Om Om), psi Om (phi zero (add Om Om)),
    psi (Z one) zero, psi (Z omega) zero,
    plus e0 omega, omg (plus M one), omg (plus M omega) ]

/-- t[n] is an increasing sequence towards t (checked for n < 4). -/
def fsMono : Bool :=
  fsSample.all fun t =>
    (List.range 4).all fun n =>
      lt (fsN t n) (fsN t (n + 1)) && lt (fsN t n) t

/-- The values of the fundamental sequence are well-formed too. -/
def fsWF : Bool :=
  fsSample.all fun t =>
    inT t && (List.range 4).all fun n => inT (fsN t n)

#guard fsMono
#guard fsWF

end TM.Test
