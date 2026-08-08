/-
TM/NF.lean — 係数集合 K_κ、𝔗(M) の形成条件 (正規形)、正規操作

[R91] 2.2 (K_κ)、2.1 (形成条件)、2.6 (正規操作 +, φ, ω^·)。
-/
import TM.Order

namespace TM
namespace Term

/-- 係数集合 K_κ γ ([R91] 2.2)。有限集合をリストで表す (重複は無害)。 -/
def Kset (k : Term) : Term → List Term
  | zero => []                                   -- 2.2(i)
  | M => []                                      -- 2.2(i)
  | add a b => Kset k a ++ Kset k b              -- 2.2(ii)
  | omg a => Kset k a                            -- 2.2(iii)
  | phi a b => Kset k a ++ Kset k b              -- 2.2(iv)
  | psi p b =>                                   -- 2.2(vi)
    if le (psi p b) (kminus k) then []           --   γ ≤ κ⁻
    else if lt p k then Kset k p                 --   κ⁻ < γ ∧ π < κ
    else b :: (Kset k p ++ Kset k b)             --   κ⁻ < γ ∧ κ ≤ π
  | Z b => Kset k b                              -- 2.2(vii)

/-- 𝔗(M) の形成条件 ([R91] 2.1 と Remark (ii))。
    Term 型の自由な項のうち、実際に 𝔗(M) の項であるものを検査する。 -/
def inT : Term → Bool
  | zero => true                                                  -- 2.1(ii)
  | M => true                                                     -- 2.1(ii)
  | add a b =>                                                    -- 2.1(iii)
    a.isAP && inT a && inT b &&
    (match b with
     | add c _ => le c a                    -- 降順 αₙ ≤ … ≤ α₁ (残りは inT b が検査)
     | _ => b.isAP && le b a)
  | omg a => inT a && lt M a                                      -- 2.1(iv)
  | phi a b => inT a && inT b && lt a M && lt b M                 -- 2.1(v)
  | psi k a =>                                                    -- 2.1(vi)
    k.isR && inT k && inT a && lt a M && (Kset k a).all (fun x => lt x a)
  | Z a => inT a                                                  -- 2.1(vii)

/-! ## 正規操作 ([R91] 2.6) -/

/-- ⊕ のスパインを成分リストへ -/
def toList : Term → List Term
  | zero => []
  | add a b => a :: toList b
  | t => [t]

/-- 成分リスト (AP 降順) から項へ -/
def ofList : List Term → Term
  | [] => zero
  | [a] => a
  | a :: rest => add a (ofList rest)

/-- α + β ([R91] 2.6(ii)):
    β の先頭成分 β₁ より小さい α の成分を末尾から捨てて連結する。
    成分は降順なので「β₁ ≤ αᵢ なる先頭側の成分を残す」と同じ。 -/
def plus (s t : Term) : Term :=
  match toList t with
  | [] => s
  | b1 :: _ => ofList ((toList s).filter (fun a => le b1 a) ++ toList t)

/-- 1 := φ̄00, ω := φ̄01, Ω₁ := Z0 ([R91] 2.6(v)) -/
def one : Term := phi zero zero
def omega : Term := phi zero one
def Om : Term := Z zero

/-- 自然数 n の項 ([R91] 2.6(v)) -/
def ofNat : Nat → Term
  | 0 => zero
  | n + 1 => plus (ofNat n) one

/-- β の末尾の 1 (= φ̄00) の個数と、それを除いた γ: β = γ + m -/
def splitFin (b : Term) : Term × Nat :=
  let l := toList b
  let m := (l.reverse.takeWhile (· == one)).length
  (ofList (l.take (l.length - m)), m)

/-- φαβ の既定ケース ([R91] 2.6(vi) 下 2 行): β = 0 ∧ α ∈ SC なら α、
    それ以外は生の φ̄αβ -/
def phiNFdefault (a b : Term) : Term :=
  if b == zero && a.isSC then a
  else phi a b

/-- φαβ の「β = γ + n + 1 で γ が不動点形」のケース ([R91] 2.6(vi) 中 2 行):
    φ̄α(γ + n) に 1 つ下げる -/
def phiNFsucc (a b : Term) : Term :=
  let (g, m) := splitFin b
  if m ≥ 1 then
    let down := plus g (ofNat (m - 1))                -- γ + n
    match g with
    | phi d _ => if lt a d then phi a down else phiNFdefault a b
    | _ => if g.isSC && lt a g then phi a down else phiNFdefault a b
  else phiNFdefault a b

/-- φαβ ([R91] 2.6(vi)): 不動点を数え直す正規化された Veblen 関数。
    α, β < M を前提とする。 -/
def phiNF (a b : Term) : Term :=
  if b.isSC && lt a b then b                          -- β ∈ SC, α < β
  else
    match b with
    | phi c _ => if lt a c then b else phiNFsucc a b  -- β = φ̄γδ, α < γ
    | _ => phiNFsucc a b

/-- ω^α ([R91] 2.6(vii)) -/
def omegaNF (a : Term) : Term :=
  if lt M a then omg a
  else if a == M then M
  else phiNF zero a

end Term
end TM
