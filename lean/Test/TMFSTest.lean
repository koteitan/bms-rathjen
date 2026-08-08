/-
Test/TMFSTest.lean — 基本列の検証

既知の基本列と照合する:
  ω[n] = n
  (ω^ω)[n] = ω^n
  ε₀[n] = 0, 1, ω, ω^ω, …        (φ₀ の反復)
  ω^{ε₀+1}[n] = ε₀·n
  Γ₀[n] = ψ_Ω(0)[n] = 1, ε₀, φ_{ε₀}(0), …   (x ↦ φ_x(0) の反復)
  ψ_Ω(Ω)[n] = ψ(0), ψ(ψ(0)), …             (対角化)
  ψ_Ω(Ω·2)[n] = ψ(Ω), ψ(Ω+ψ(Ω)), …
さらに単調性 t[n] < t[n+1] < t をサンプルで総当たり検査する。
-/
import Test.TMTest

namespace TM.Test
open TM.Term

def G0 : Term := psi Om zero

-- 分類
#guard kindT zero = .isZero
#guard kindT one = .isSucc
#guard kindT (ofNat 3) = .isSucc
#guard kindT omega = .isLim
#guard kindT (plus omega one) = .isSucc
#guard kindT e0 = .isLim
#guard kindT M = .isLim
#guard predT (ofNat 3) = ofNat 2
#guard predT (plus omega one) = omega

-- 共終度
#guard cofT omega = omega
#guard cofT e0 = omega
#guard cofT G0 = omega
#guard cofT Om = Om
#guard cofT (add Om Om) = Om
#guard cofT (psi Om Om) = omega            -- 対角化で ω に落ちる
#guard cofT (psi Om (add Om Om)) = omega
#guard cofT (phi zero (add Om Om)) = Om    -- ω^{Ω·2} は Ω 共終
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

-- ψ_Ω(α+1): ψ_Ω(α)+1 から φ-閉包
#guard fsN (psi Om one) 0 = plus G0 one
#guard fsN (psi Om one) 1 = phi (plus G0 one) zero

-- ψ_Ω(Ω) の対角化: ψ(0), ψ(ψ(0))
#guard fsN (psi Om Om) 0 = G0
#guard fsN (psi Om Om) 1 = psi Om G0
#guard fsN (psi Om Om) 2 = psi Om (psi Om G0)

-- ψ_Ω(Ω·2) の対角化: ψ(Ω), ψ(Ω+ψ(Ω))
#guard fsN (psi Om (add Om Om)) 0 = psi Om Om
#guard fsN (psi Om (add Om Om)) 1 = psi Om (plus Om (psi Om Om))

-- ψ_Ω(ω) : 可算共終度の伝播
#guard fsN (psi Om omega) 2 = psi Om (ofNat 2)

-- ψ_{Z1}(0): Ω+1 から φ-閉包 (Γ_{Ω+1} 相当)
#guard fsN (psi (Z one) zero) 0 = plus Om one
#guard fsN (psi (Z one) zero) 1 = phi (plus Om one) zero

-- ω̄^{M+1}[n] = M·n
#guard fsN (omg (plus M one)) 2 = add M M

-- 加法: 最後の成分に伝播
#guard fsN (plus e0 omega) 3 = plus e0 (ofNat 3)

/-! ## 単調性の総当たり: t[n] < t[n+1] < t -/

def fsSample : List Term :=
  [ omega, phi zero omega, e0, phi zero e0, phi omega zero, phi e0 zero,
    G0, psi Om one, psi Om omega, psi Om G0, psi Om Om,
    psi Om (add Om Om), psi Om (phi zero (add Om Om)),
    psi (Z one) zero, psi (Z omega) zero,
    plus e0 omega, omg (plus M one), omg (plus M omega) ]

/-- t[n] が t への増加列になっている (n < 4 で検査) -/
def fsMono : Bool :=
  fsSample.all fun t =>
    (List.range 4).all fun n =>
      lt (fsN t n) (fsN t (n + 1)) && lt (fsN t n) t

/-- 基本列の値も形成条件を満たす -/
def fsWF : Bool :=
  fsSample.all fun t =>
    inT t && (List.range 4).all fun n => inT (fsN t n)

#guard fsMono
#guard fsWF

end TM.Test
