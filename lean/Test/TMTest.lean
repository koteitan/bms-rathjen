/-
Test/TMTest.lean — 𝔗(M) の順序・形成条件・正規操作のスモークテスト

既知の順序数の大小関係を項の上で検査する:
  0 < 1 < ω < ω+1 < ω·2? < ε₀ = φ̄10 < ψ_Ω(0) < Ω = Z0 < M < ω̄^(M+1)
-/
import TM

namespace TM.Test
open TM.Term

-- 略記
def e0 : Term := phi one zero          -- φ̄10 = ε₀
def psi0 : Term := psi Om zero         -- ψ_Ω(0)
def Mp1 : Term := plus M one           -- M + 1
def wMp1 : Term := omg Mp1             -- ω̄^(M+1)

-- 形成条件
#guard inT one
#guard inT omega
#guard inT e0
#guard inT Om
#guard inT psi0
#guard inT Mp1
#guard inT wMp1
#guard inT (psi Om (psi Om zero))      -- K_Ω(ψ_Ω 0) = {0} < ψ_Ω 0
-- 非正規な項は排除される
#guard !(inT (omg one))                -- ω̄ の指数は M より大でなければならない
#guard !(inT (phi M zero))             -- φ̄ の引数は M 未満
#guard !(inT (psi one zero))           -- ψ の添字は R (Z の形)
#guard !(inT (add one omega))          -- ⊕ は降順でなければならない

-- 順序: 基本の鎖
#guard lt zero one
#guard lt one omega
#guard lt omega (plus omega one)
#guard lt (plus omega one) e0
#guard lt e0 psi0
#guard lt psi0 Om
#guard lt Om M
#guard lt M wMp1

-- 非対称性 (逆向きは偽)
#guard !(lt one zero)
#guard !(lt omega one)
#guard !(lt e0 omega)
#guard !(lt psi0 e0)
#guard !(lt Om psi0)
#guard !(lt M Om)
#guard !(lt wMp1 M)

-- 2.3.13(iii): 同じ順序数の別表現は項としては大きくなる (φ̄0ε₀ > ε₀)
#guard lt e0 (phi zero e0)
#guard !(lt (phi zero e0) e0)

-- 2.3.16: 和の辞書式比較
#guard lt (ofNat 2) (ofNat 3)
#guard lt (ofNat 2) (plus omega one)
#guard lt omega (plus omega one)      -- 接頭辞
#guard lt (plus omega one) (plus omega (ofNat 2))
#guard lt (plus e0 omega) (plus e0 e0)

-- ψ の入れ子と Z の比較
#guard lt psi0 (psi Om (psi Om zero))
#guard lt (Z zero) (Z one)
#guard lt (Z one) (Z omega)
#guard lt Om (Z psi0)
#guard lt psi0 (Z psi0)                -- ψ_Ω0 = (Z ψ_Ω0)⁻ ≤ ψ_Ω0 → ψ_Ω0 < Z(ψ_Ω0)

-- K 係数集合
#guard Kset Om (psi Om zero) = [zero]
#guard Kset Om zero = []
#guard Kset Om e0 = []

-- * 写像
#guard star e0 = zero
#guard star psi0 = psi0
#guard star (plus psi0 one) = psi0
#guard kminus (Z psi0) = psi0
#guard kminus Om = zero

-- 正規操作
#guard plus zero omega = omega
#guard plus omega zero = omega
#guard plus one omega = omega          -- 1 + ω = ω (吸収)
#guard toList (plus omega one) = [omega, one]
#guard phiNF zero zero = one           -- 生の φ̄00 がそのまま 1
#guard phiNF zero e0 = e0              -- φ0(ε₀) = ε₀ (吸収)
#guard phiNF one psi0 = psi0           -- ψ_Ω0 ∈ SC は φ の不動点
#guard phiNF zero omega = phi zero omega
#guard omegaNF M = M                   -- ω^M = M
#guard omegaNF Mp1 = wMp1
#guard omegaNF e0 = e0                 -- ω^ε₀ = ε₀
#guard omegaNF one = phi zero one      -- ω^1 = ω

-- φαβ の不動点ずらし ([R91] 2.6(vi) 中段):
--   φ0(ε₀+1) = φ̄0(ε₀) ではなく…実際には φ̄0(ε₀+0) = φ̄0ε₀
#guard phiNF zero (plus e0 one) = phi zero e0

end TM.Test
