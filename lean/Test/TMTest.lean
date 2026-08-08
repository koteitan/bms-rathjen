/-
Test/TMTest.lean — smoke tests for the order, formation conditions and normal
operations of 𝔗(M)

Known inequalities between ordinals are checked on the terms:
  0 < 1 < ω < ω+1 < ε₀ = φ̄10 < ψ_Ω(0) < Ω = Z0 < M < ω̄^(M+1)
-/
import TM

namespace TM.Test
open TM.Term

-- abbreviations
def e0 : Term := phi one zero          -- φ̄10 = ε₀
def psi0 : Term := psi Om zero         -- ψ_Ω(0)
def Mp1 : Term := plus M one           -- M + 1
def wMp1 : Term := omg Mp1             -- ω̄^(M+1)

-- formation conditions
#guard inT one
#guard inT omega
#guard inT e0
#guard inT Om
#guard inT psi0
#guard inT Mp1
#guard inT wMp1
#guard inT (psi Om (psi Om zero))      -- K_Ω(ψ_Ω 0) = {0} < ψ_Ω 0
-- ill-formed terms are rejected
#guard !(inT (omg one))                -- the exponent of ω̄ must exceed M
#guard !(inT (phi M zero))             -- the arguments of φ̄ must be below M
#guard !(inT (psi one zero))           -- the subscript of ψ must be in R (a Z term)
#guard !(inT (add one omega))          -- the components of ⊕ must descend

-- order: the basic chain
#guard lt zero one
#guard lt one omega
#guard lt omega (plus omega one)
#guard lt (plus omega one) e0
#guard lt e0 psi0
#guard lt psi0 Om
#guard lt Om M
#guard lt M wMp1

-- asymmetry (the converses are false)
#guard !(lt one zero)
#guard !(lt omega one)
#guard !(lt e0 omega)
#guard !(lt psi0 e0)
#guard !(lt Om psi0)
#guard !(lt M Om)
#guard !(lt wMp1 M)

-- 2.3.13(iii): another term for the same ordinal is larger as a term (φ̄0ε₀ > ε₀)
#guard lt e0 (phi zero e0)
#guard !(lt (phi zero e0) e0)

-- 2.3.16: lexicographic comparison of sums
#guard lt (ofNat 2) (ofNat 3)
#guard lt (ofNat 2) (plus omega one)
#guard lt omega (plus omega one)      -- proper prefix
#guard lt (plus omega one) (plus omega (ofNat 2))
#guard lt (plus e0 omega) (plus e0 e0)

-- nested ψ, and comparison against Z
#guard lt psi0 (psi Om (psi Om zero))
#guard lt (Z zero) (Z one)
#guard lt (Z one) (Z omega)
#guard lt Om (Z psi0)
#guard lt psi0 (Z psi0)                -- ψ_Ω0 = (Z ψ_Ω0)⁻ ≤ ψ_Ω0, hence ψ_Ω0 < Z(ψ_Ω0)

-- coefficient sets K
#guard Kset Om (psi Om zero) = [zero]
#guard Kset Om zero = []
#guard Kset Om e0 = []

-- the map *
#guard star e0 = zero
#guard star psi0 = psi0
#guard star (plus psi0 one) = psi0
#guard kminus (Z psi0) = psi0
#guard kminus Om = zero

-- normal operations
#guard plus zero omega = omega
#guard plus omega zero = omega
#guard plus one omega = omega          -- 1 + ω = ω (absorption)
#guard toList (plus omega one) = [omega, one]
#guard phiNF zero zero = one           -- the raw φ̄00 is 1 itself
#guard phiNF zero e0 = e0              -- φ0(ε₀) = ε₀ (a fixed point)
#guard phiNF one psi0 = psi0           -- ψ_Ω0 ∈ SC is a fixed point of φ
#guard phiNF zero omega = phi zero omega
#guard omegaNF M = M                   -- ω^M = M
#guard omegaNF Mp1 = wMp1
#guard omegaNF e0 = e0                 -- ω^ε₀ = ε₀
#guard omegaNF one = phi zero one      -- ω^1 = ω

-- the fixed-point shift of φαβ (middle of [R91] 2.6(vi)):
--   φ0(ε₀+1) steps down to φ̄0(ε₀+0) = φ̄0ε₀
#guard phiNF zero (plus e0 one) = phi zero e0

end TM.Test
