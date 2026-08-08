/-
TM/NF.lean — coefficient sets K_κ, formation conditions of 𝔗(M), and normal operations

[R91] 2.2 (K_κ), 2.1 (formation), 2.6 (the normal operations +, φ, ω^·).
-/
import TM.Order

namespace TM
namespace Term

/-- The coefficient set K_κ γ ([R91] 2.2).  Finite sets are lists (duplicates harmless). -/
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

/-- The formation conditions of 𝔗(M) ([R91] 2.1 and Remark (ii)):
    which terms of the free type `Term` are genuinely terms of 𝔗(M). -/
def inT : Term → Bool
  | zero => true                                                  -- 2.1(ii)
  | M => true                                                     -- 2.1(ii)
  | add a b =>                                                    -- 2.1(iii)
    a.isAP && inT a && inT b &&
    (match b with
     | add c _ => le c a          -- descending αₙ ≤ … ≤ α₁ (the rest is checked by `inT b`)
     | _ => b.isAP && le b a)
  | omg a => inT a && lt M a                                      -- 2.1(iv)
  | phi a b => inT a && inT b && lt a M && lt b M                 -- 2.1(v)
  | psi k a =>                                                    -- 2.1(vi)
    k.isR && inT k && inT a && lt a M && (Kset k a).all (fun x => lt x a)
  | Z a => inT a                                                  -- 2.1(vii)

/-! ## Normal operations ([R91] 2.6) -/

/-- The spine of a ⊕ as a list of components. -/
def toList : Term → List Term
  | zero => []
  | add a b => a :: toList b
  | t => [t]

/-- Rebuild a term from a list of components (AP, descending). -/
def ofList : List Term → Term
  | [] => zero
  | [a] => a
  | a :: rest => add a (ofList rest)

/-- α + β ([R91] 2.6(ii)): drop the trailing components of α that are smaller than the
    head component β₁ of β, then concatenate.  Since components descend, this is the
    same as keeping the leading components αᵢ with β₁ ≤ αᵢ. -/
def plus (s t : Term) : Term :=
  match toList t with
  | [] => s
  | b1 :: _ => ofList ((toList s).filter (fun a => le b1 a) ++ toList t)

/-- 1 := φ̄00, ω := φ̄01, Ω₁ := Z0 ([R91] 2.6(v)). -/
def one : Term := phi zero zero
def omega : Term := phi zero one
def Om : Term := Z zero

/-- The term for a natural number `n` ([R91] 2.6(v)). -/
def ofNat : Nat → Term
  | 0 => zero
  | n + 1 => plus (ofNat n) one

/-- Split β as γ + m: the number of trailing 1s (= φ̄00) and the rest. -/
def splitFin (b : Term) : Term × Nat :=
  let l := toList b
  let m := (l.reverse.takeWhile (· == one)).length
  (ofList (l.take (l.length - m)), m)

/-- Default case of φαβ (last two lines of [R91] 2.6(vi)): α when β = 0 and α ∈ SC,
    otherwise the raw φ̄αβ. -/
def phiNFdefault (a b : Term) : Term :=
  if b == zero && a.isSC then a
  else phi a b

/-- The case "β = γ + n + 1 with γ a fixed-point shape" of φαβ
    (middle two lines of [R91] 2.6(vi)): step down to φ̄α(γ + n). -/
def phiNFsucc (a b : Term) : Term :=
  let (g, m) := splitFin b
  if m ≥ 1 then
    let down := plus g (ofNat (m - 1))                -- γ + n
    match g with
    | phi d _ => if lt a d then phi a down else phiNFdefault a b
    | _ => if g.isSC && lt a g then phi a down else phiNFdefault a b
  else phiNFdefault a b

/-- φαβ ([R91] 2.6(vi)): the normalized Veblen function, which re-counts fixed points.
    Assumes α, β < M. -/
def phiNF (a b : Term) : Term :=
  if b.isSC && lt a b then b                          -- β ∈ SC, α < β
  else
    match b with
    | phi c _ => if lt a c then b else phiNFsucc a b  -- β = φ̄γδ with α < γ
    | _ => phiNFsucc a b

/-- ω^α ([R91] 2.6(vii)). -/
def omegaNF (a : Term) : Term :=
  if lt M a then omg a
  else if a == M then M
  else phiNF zero a

end Term
end TM
