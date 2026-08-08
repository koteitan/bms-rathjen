/-
TM/Terms.lean — Rathjen の表記系 𝔗(M) の項

一次ソース: M. Rathjen, "Proof-theoretic analysis of KPM",
Archive for Mathematical Logic 30 (1991) 377–403, §2 (pp. 382–384)。
以下「[R91]」と略記し、定義番号は同論文のもの。

[R91] §2 冒頭: 𝔗(M) は T(M) ([R90]) の軽量版で、
  1. 項 Φαβ を落とし、
  2. χ の階層の代わりに単一関数 Z (= α ↦ χ_α(0)) を持つ。

項の構成子 ([R91] 2.1):
  0, M
  ⊕(α₁,…,αₙ)   (n ≥ 2, αᵢ ∈ AP, αₙ ≤ … ≤ α₁)     … 形式和
  ω̄^α          (M < α)                             … M 超の加法主要項
  φ̄αβ          (α, β < M)                          … 2 変数 Veblen (生)
  ψκα          (κ ∈ R, α < M, K_κ α < α)           … 崩壊関数
  Zα                                                … 正則基数の名前 (α ↦ χ_α(0))

⊕ は右結合の 2 項 add で符号化する:
  ⊕(α₁,…,αₙ) = add α₁ (add α₂ (… (add α_{n-1} αₙ)))
形成条件 (成分が AP・降順) は TM/NF.lean の inT で検査する。
-/

namespace TM

inductive Term where
  | zero              -- 0
  | M                 -- M (最小弱 Mahlo)
  | add (a b : Term)  -- ⊕ の右結合符号化: a は AP 成分、b は残り
  | omg (a : Term)    -- ω̄^a
  | phi (a b : Term)  -- φ̄ a b
  | psi (k a : Term)  -- ψ_k a
  | Z (a : Term)      -- Z a
deriving DecidableEq, Repr

namespace Term

/-- 次数 Gα ([R91] 2.4): 記号 0, M, ⊕, ω̄, φ̄, ψ, Z の総数。
    ⊕ は add の連鎖でも 1 個と数えるべきだが、fuel の上界として使うだけ
    なので add ごとに 1 と数えて構わない (真の Gα 以上になる)。 -/
def deg : Term → Nat
  | zero => 1
  | M => 1
  | add a b => 1 + a.deg + b.deg
  | omg a => 1 + a.deg
  | phi a b => 1 + a.deg + b.deg
  | psi k a => 1 + k.deg + a.deg
  | Z a => 1 + a.deg

/-- 加法主要項 AP の形 ([R91] 2.1: AP = {M} ∪ {ω̄^α} ∪ {φ̄αβ} ∪ SC) -/
def isAP : Term → Bool
  | zero => false
  | add _ _ => false
  | _ => true

/-- 強臨界項 SC の形 ([R91] 2.1: SC = {M} ∪ {ψκα} ∪ {Zα}) -/
def isSC : Term → Bool
  | M => true
  | psi _ _ => true
  | Z _ => true
  | _ => false

/-- 正則項 R の形 ([R91] 2.1 (vii): R = {Zα}) -/
def isR : Term → Bool
  | Z _ => true
  | _ => false

/-- 表示 (デバッグ・表生成用): ⊕ は + で、ω̄/φ̄/ψ/Z はそのまま -/
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
