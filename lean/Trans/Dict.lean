import TM
/-
Trans/Dict.lean — the Buchholz → 𝔗(M) dictionary  (candidate / 予想 tier)

Purpose.  The gold-standard reference implementation for the 2-row fragment of BMS is p-adic-lover-bot's
translation `Trans` from the PSS termination proof (naruyoko's implementation; the CLI
`pss2bp` in this workflow).  Its target is *Buchholz's* notation system OT_B, written
`D_u a` (= ψ_u(a) of Buchholz 1986), not Rathjen's 𝔗(M).  To compare the reference implementation with
this repository's 𝔗(M) side, one needs a dictionary

    dict : OT_B → 𝔗(M)      (an order-isomorphism onto its image, value-preserving)

and that is what this file provides, together with machine checks of its
order-preservation and of the anchor values recorded in `table/refimpl-audit-2026-08-09.txt`.

## The correspondence adopted, and why

Buchholz's D_u is NOT Rathjen's ψ_{Ω_{u+1}}.  The two systems have different "ground":

  * Buchholz OT_B has no Veblen function; the whole Veblen hierarchy is *encoded* by
    Ω-powers inside the argument of D_0 (ψ_0(Ω^{1+α}·(1+β)) = φ(1+α, β), …).
  * Rathjen's 𝔗(M) ([R91] 2.1) has the binary Veblen φ̄ as a primitive on all of (0,M),
    so its ψ_κ starts only where Veblen stops: ψ_{Z0}(0) = Γ₀ (this repository's own
    reading — see the Γ-closure clause of `psiSeed`/`iterGamma` in TM/FS.lean), and
    SC ∩ (Ω_u, Ω_{u+1}) = range(ψ_{Z u}) ([R91] 2.1: SC = {M} ∪ {ψκα} ∪ {Zα}).

So the dictionary is a genuine ordinal-value computation, not a homomorphism of the
term algebras.  It is fixed by the following facts, all of which are re-checked as
`#guard`s at the bottom:

  (D1)  ψ_u(a) = ω^(Ω_u + a)                     whenever a < Ω_{u+1}   (Ω_0 := 0)
        e.g. ψ_1(0) = Ω_1, ψ_1(1) = Ω_1·ω, ψ_1(Ω_1) = Ω_1², ψ_0(β) = ω^β (β < Ω_1).
  (D2)  For a ≥ Ω_{u+1} one reads the base-W CNF of a (W := Ω_{u+1}):
              a = W^{α₁}·c₁ + … + W^{α_k}·c_k + ρ,   α₁ > … > α_k ≥ 1,  ρ < W,
        and folds left to right, starting from
              base := 0 (u = 0)   |   Ω_u + 1 (u ≥ 1),
        with, for the i-th component (c = 1 + γ):
          * α < W  (Veblen range):  acc := φ(α, base + γ)      for i = 1
                                    acc := φ(α, acc + c)       for i > 1
          * α ≥ W  (strongly critical range): acc := ψ_{Z u}(idx) where, with the
            index step  Δ := W^(α ⊖ W) · c,
                                    idx := Δ ⊖ 1               for i = 1
                                    idx := idx + Δ             for i > 1
        and finally  ψ_u(a) = ω^(Ω_u + acc + ρ).
        (⊖ is left subtraction; components descend, so all α ≥ W come first.)

Why (D2)'s two ranges: ψ_u(W^α·c) is strongly critical exactly when α ≥ W, and the
strongly critical ordinals of (Ω_u, Ω_{u+1}) are, in 𝔗(M), exactly the ψ_{Z u}-terms.
The index step W^(α ⊖ W)·c is forced by the θ-picture ψ_0(Ω^x·(1+γ)) = θ(x, γ)
together with the fixed-point behaviour of ψ_{Z0} recorded in TM/FS.lean:
        θ(Ω, γ)   = Γ_γ                  = ψ_{Z0}(γ)                (W^0·(1+γ) ⊖ 1)
        θ(Ω+1, γ) = the (1+γ)-th fixed point of ξ ↦ Γ_ξ = ψ_{Z0}(Ω_1·(1+γ))
                    (`fsN`'s ψκα clause diagonalises exactly at these indices)
        θ(Ω·2, 0) = ψ_{Z0}(Ω_1^{Ω_1}),   θ(Ω_2, γ) = ψ_{Z0}(Ω_2·(1+γ)).
An index step by *multiplication* W·(α ⊖ W) instead would identify
D_0(Ω_2 × 2) with D_0(Ω_2 + D_1 D_1 Ω_1) — the injectivity `#guard`s at the bottom
are what caught this, and they keep the choice pinned.

The additive continuation `idx + Δ` for i > 1 (rather than the semantically equal
W^(α ⊖ W)·(acc + c)) is what the 𝔗(M) normal form demands: K_κ of the latter would
contain the argument of the previous ψ, violating the formation condition of
[R91] 2.1(vi).  Both denote the same ordinal; only the former is a term of 𝔗(M).

Sample values produced by `dict` (all in the `#guard` block; the Buchholz side is
verbatim `pss2bp` output for the matrix named in the comment):

    D_0 Ω_1            = φ̄(1,0)   = ε₀            (0,0)(1,1)
    D_0 D_1 Ω_1        = φ̄(2,0)   = ζ₀            (0,0)(1,1)(2,1)
    D_0 D_1(Ω_1+1)     = φ̄(2,ω)   = ζ_ω           (0,0)(1,1)(2,1)(2,0)   ← was ε_{ζ₀·ω}
    D_0 D_1(Ω_1×2)     = φ̄(3,0)                   (0,0)(1,1)(2,1)(2,1)   ← was ζ₁
    D_0 D_1 D_1 1      = φ̄(ω,0)                   (0,0)(1,1)(2,1)(3,0)
    D_0 D_1 D_1 Ω_1    = ψ_{Z0}(0) = Γ₀           (0,0)(1,1)(2,1)(3,1)   ← was φ̄(3,0)
    D_0 Ω_2            = ψ_{Z0}(Z 1)              (0,0)(1,1)(2,2)        ← was φ̄(ω,0)

## Status

Candidate (予想) tier.  `dict` is validated by (i) the anchor values above against the
reference-implementation audit, (ii) order-preservation over systematically generated term families
(which doubles as a cross-audit of the [R91] 2.3 transcription in TM/Order.lean), and
(iii) `inT`-wellformedness of every produced term.  No semantic proof is claimed.

Note: the import precedes this comment because the kimina server extracts the header
imports from the top of a posted snippet.
-/

namespace Trans
namespace Dict

open TM (Term)
open TM.Term

/-! ## 1. Buchholz terms (OT_B)

`D u a` is Buchholz's ψ_u(a); `sum` is the right-nested formal sum.  This mirrors the
representation of naruyoko's `common.js` (0 | {sub,inner} | array). -/

inductive BT where
  | zero
  | D (u : Nat) (a : BT)
  | sum (a b : BT)
deriving DecidableEq, Repr, BEq

namespace BT

/-- The components of a formal sum. -/
def toL : BT → List BT
  | .zero => []
  | .sum a b => toL a ++ toL b
  | t => [t]

/-- Rebuild a term from its components. -/
def ofL : List BT → BT
  | [] => .zero
  | [a] => a
  | a :: rest => .sum a (ofL rest)

/-- Symbol count (recursion fuel bound). -/
def size : BT → Nat
  | .zero => 1
  | .D _ a => 1 + size a
  | .sum a b => 1 + size a + size b

def isP : BT → Bool
  | .D _ _ => true
  | _ => false

/-- `lessThanBuchholz` of common.js, on the uniform component-list view:
    compare component-wise, and on a common prefix the shorter list is smaller.
    Principal components compare lexicographically on (subscript, argument). -/
def ltL : Nat → List BT → List BT → Bool
  | 0, _, _ => false
  | fuel + 1, l1, l2 =>
    match l1, l2 with
    | [], [] => false
    | [], _ :: _ => true
    | _ :: _, [] => false
    | .D u a :: ps, .D v b :: qs =>
      if u < v then true
      else if v < u then false
      else if a == b then ltL fuel ps qs
      else ltL fuel (toL a) (toL b)
    | _, _ => false            -- junk: a non-principal component

def lt (s t : BT) : Bool := ltL (size s + size t + 2) (toL s) (toL t)
def le (s t : BT) : Bool := s == t || lt s t

/-- `G(a,u)` of common.js (the coefficient set of the normal-form condition). -/
def GB (u : Nat) : BT → List BT
  | .zero => []
  | .sum a b => GB u a ++ GB u b
  | .D v a => if u ≤ v then a :: GB u a else []

/-- `isStandardBuchholz` of common.js: components nonzero and descending, and
    every element of G(a,u) below a. -/
def isStd : BT → Bool
  | .zero => true
  | .D u a => isStd a && (GB u a).all (fun e => lt e a)
  | .sum a b =>
    isP a && isStd a && isStd b &&
    (match b with
     | .sum c _ => le c a
     | _ => isP b && le b a)

/-! Abbreviations for the guards. -/

/-- 1 = D_0 0. -/
def one : BT := .D 0 .zero
/-- Ω_k = D_k 0 (k ≥ 1). -/
def Om (k : Nat) : BT := .D k .zero
/-- ω = D_0 1. -/
def omega : BT := .D 0 one
/-- The natural number n as a sum of 1s. -/
def ofNat (n : Nat) : BT := ofL (List.replicate n one)
/-- a + b. -/
def add (a b : BT) : BT := ofL (toL a ++ toL b)

end BT

/-! ## 2. 𝔗(M)-side ordinal arithmetic used by the dictionary -/

/-- Ω_u as a 𝔗(M) term: Ω_0 = 0 (a formal bottom for the uniform clauses),
    Ω_{u+1} = Z u ([R91] 2.1(vii): Z enumerates the regulars). -/
def reg : Nat → Term
  | 0 => zero
  | u + 1 => Z (TM.Term.ofNat u)

/-- The ω-exponent of an additively principal term: p = ω^(logOm p).
    φ̄0β denotes φ_0(β°) = ω^(β°) with the shift β° of [R91] 2.7; every other AP term
    (φ̄αβ with α ≠ 0, ψκα, Zα, M) is an ε-number, hence its own ω-exponent. -/
def logOm : Term → Term
  | phi zero b => if phiShifted zero b then plus b TM.Term.one else b
  | t => t

/-- h ⊖ w: the unique h' with w + h' = h (w ∈ AP, w ≤ h). -/
def subAP (w h : Term) : Term :=
  match toList h with
  | [] => zero
  | p :: rest => if p == w then ofList rest else h

/-- p / w for p ∈ AP with w ≤ p and w ∈ SC: p = ω^g gives p/w = ω^(g ⊖ w). -/
def divAP (w p : Term) : Term := omegaNF (subAP w (logOm p))

/-- w · y for w ∈ SC: w·ω^h = ω^(w+h), distributed over the components of y. -/
def mulL (w y : Term) : Term :=
  ofList ((toList y).map (fun p => omegaNF (plus w (logOm p))))

/-- The unique δ with 1 + δ = c (c ≠ 0). -/
def sub1 (c : Term) : Term :=
  match toList c with
  | [] => zero
  | p :: rest => if p == TM.Term.one then ofList rest else c

/-- Base-w Cantor normal form of a term given by its component list:
    the (exponent, coefficient) pairs with exponent ≥ 1 in descending order,
    together with the tail ρ < w.  Components with equal exponent are merged. -/
def wcnf (w : Term) : List Term → List (Term × Term) × Term
  | [] => ([], zero)
  | p :: rest =>
    if lt p w then ([], ofList (p :: rest))
    else
      let g := logOm p
      let l := toList g
      let a := ofList ((l.filter (fun q => !lt q w)).map (divAP w))
      let c := omegaNF (ofList (l.filter (fun q => lt q w)))
      match wcnf w rest with
      | ((a', c') :: ps, tl) =>
        if a == a' then ((a, plus c c') :: ps, tl) else ((a, c) :: (a', c') :: ps, tl)
      | ([], tl) => ([(a, c)], tl)

/-- Buchholz's ψ_u applied to an argument already translated to 𝔗(M) — clauses
    (D1)/(D2) of the header. -/
def collapse (u : Nat) (x : Term) : Term :=
  let w := reg (u + 1)
  let b := reg u
  let base : Term := if u == 0 then zero else plus b TM.Term.one
  let pr := wcnf w (toList x)
  let st := pr.1.foldl (init := ((none : Option Term), (none : Option Term)))
    fun s ac =>
      let a := ac.1
      let c := ac.2
      if le w a then
        -- strongly critical range: an index step Δ = W^(a ⊖ w)·c for ψ_{Z u}
        let e := mulL w (subAP w a)          -- w·(a ⊖ w), the ω-exponent of W^(a ⊖ w)
        let d := mulL e c                    -- Δ = ω^(w·(a ⊖ w))·c
        let i := match s.1 with
          | none => sub1 d
          | some i0 => plus i0 d
        (some i, some (psi w i))
      else
        -- Veblen range
        let bse := match s.2 with | none => base | some v => v
        let cc := match s.2 with | none => sub1 c | some _ => c
        (s.1, some (phiNF a (plus bse cc)))
  omegaNF (plus b (plus (st.2.getD zero) pr.2))

/-- The dictionary. -/
def dict : BT → Term
  | .zero => zero
  | .D u a => collapse u (dict a)
  | .sum a b => plus (dict a) (dict b)

/-! ## 3. Acceptance record

Three layers, all re-verified by a successful build:

  (A) anchors — every row of `table/refimpl-audit-2026-08-09.txt` (both sections),
      the Buchholz side being verbatim `pss2bp` output for the matrix in the comment;
  (B) wellformedness — every produced term satisfies `inT` ([R91] 2.1);
  (C) order-preservation and injectivity over systematically generated corpora.
      (C) is simultaneously a cross-audit of the [R91] 2.3 transcription in
      TM/Order.lean: a disagreement is either a `dict` bug or an `lt` bug.
      Result at the time of writing: no disagreement on 30k+ pairs. -/

namespace Test

open BT

private def e0 : Term := phi TM.Term.one zero                 -- ε₀  = φ̄(1,0)
private def z0 : Term := phi (TM.Term.ofNat 2) zero           -- ζ₀  = φ̄(2,0)
private def G0 : Term := psi (Z zero) zero                    -- Γ₀  = ψ_{Z0}(0)
private def w2 : Term := psi (Z zero) (Z TM.Term.one)         -- ψ_{Z0}(Ω₂)

/-! ### (A) anchors — audit section 1 (rows that survived v0.1.42) -/

#guard dict (D 0 (Om 1))                    == e0                              -- (0,0)(1,1)
#guard dict (add (D 0 (Om 1)) one)          == plus e0 TM.Term.one             -- …(0,0)
#guard dict (D 0 (add (Om 1) one))          == phi zero e0                     -- …(1,0)
#guard dict (D 0 (add (Om 1) (Om 1)))       == phi TM.Term.one TM.Term.one     -- …(1,1)
#guard dict (D 0 (D 1 one))                 == phi TM.Term.one TM.Term.omega   -- (2,0)
#guard dict (D 0 (D 1 (ofNat 2)))           == phi TM.Term.one (phi zero (TM.Term.ofNat 2))
#guard dict (D 0 (D 1 omega))               == phi TM.Term.one (phi zero TM.Term.omega)
#guard dict (D 0 (D 1 (D 0 (Om 1))))        == phi TM.Term.one e0              -- (2,0)(3,1)
#guard dict (D 0 (D 1 (Om 1)))              == z0                              -- (2,1)
#guard dict (add (D 0 (D 1 (Om 1))) one)    == plus z0 TM.Term.one             -- (2,1)(0,0)
#guard dict (D 0 (add (D 1 (Om 1)) one))    == phi zero z0                     -- (2,1)(1,0)
#guard dict (D 0 (add (D 1 (Om 1)) (Om 1))) == phi TM.Term.one z0              -- (2,1)(1,1)

/-! ### (A) anchors — audit section 2 (the region withdrawn in v0.1.41/42).

These are the values the miscalibrated `o?` got wrong; each line is the reference implementation's. -/

#guard dict (D 0 (D 1 (add (Om 1) one)))    == phi (TM.Term.ofNat 2) TM.Term.omega
                                            -- (2,1)(2,0) = ζ_ω   (o? said ε_{ζ₀·ω})
#guard dict (D 0 (D 1 (add (Om 1) (Om 1)))) == phi (TM.Term.ofNat 3) zero
                                            -- (2,1)(2,1) = φ̄(3,0) (o? said ζ₁)
#guard dict (D 0 (D 1 (D 1 one)))           == phi TM.Term.omega zero
                                            -- (2,1)(3,0) = φ̄(ω,0) (o? said ζ_ω)
#guard dict (D 0 (D 1 (D 1 (D 0 (Om 1)))))  == phi e0 zero                     -- (2,1)(3,0)(4,1)
#guard dict (D 0 (D 1 (D 1 (Om 1))))        == G0
                                            -- (2,1)(3,1) = Γ₀    (o? said φ̄(3,0))
#guard dict (add (D 0 (D 1 (D 1 (Om 1)))) one) == plus G0 TM.Term.one          -- (2,1)(3,1)(0,0)
#guard dict (D 0 (add (D 1 (D 1 (Om 1))) one)) == phi zero G0                  -- (2,1)(3,1)(1,0)
#guard dict (D 0 (Om 2))                    == w2
                                            -- (2,2) = ψ₀(Ω₂)     (o? said φ̄(ω,0))
#guard dict (D 0 (add (Om 2) (Om 1)))       == phi TM.Term.one w2              -- (2,2)(1,1)
#guard dict (D 0 (add (Om 2) (D 1 (Om 1)))) == phi (TM.Term.ofNat 2) w2        -- (2,2)(1,1)(2,1)
#guard dict (D 0 (add (Om 2) (D 1 (D 1 (Om 1)))))
                                            == psi (Z zero) (plus (Z TM.Term.one) TM.Term.one)
                                            -- (2,2)(1,1)(2,1)(3,1)
#guard dict (D 0 (add (Om 2) (D 1 (Om 2))))
       == psi (Z zero) (plus (Z TM.Term.one) (phi TM.Term.one (Z zero)))       -- (2,2)(1,1)(2,2)
#guard dict (D 0 (add (Om 2) (Om 2)))
       == psi (Z zero) (plus (Z TM.Term.one) (Z TM.Term.one))                  -- (2,2)(2,2)
#guard dict (D 0 (add (Om 2) (add (Om 2) (Om 2))))
       == psi (Z zero) (plus (Z TM.Term.one) (plus (Z TM.Term.one) (Z TM.Term.one)))
                                                                               -- (2,2)(2,2)(2,2)
#guard dict (D 0 (D 2 one))                 == psi (Z zero) (phi zero (Z TM.Term.one))
                                                                               -- (2,2)(3,0)
#guard dict (D 0 (D 2 (Om 1)))
       == psi (Z zero) (phi zero (plus (Z TM.Term.one) (Z zero)))              -- (2,2)(3,1)

-- the audit rows are standard Buchholz terms (`isStandardBuchholz` of common.js)
#guard [D 0 (Om 1), D 0 (add (Om 1) one), D 0 (D 1 (Om 1)), D 0 (D 1 (add (Om 1) one)),
        D 0 (D 1 (D 1 (Om 1))), D 0 (Om 2), D 0 (add (Om 2) (D 1 (Om 2))),
        D 0 (D 2 (Om 1))].all isStd

-- the miscalibrated readings are NOT produced (the memorial of the v0.1.41 incident)
#guard dict (D 0 (D 1 (add (Om 1) (Om 1)))) != phi (TM.Term.ofNat 2) TM.Term.one
#guard dict (D 0 (D 1 (add (Om 1) one)))
       != phi TM.Term.one (phi zero (phi (TM.Term.ofNat 2) zero))
#guard dict (D 0 (Om 2)) != phi TM.Term.omega zero

/-! ### (B)/(C) corpora -/

private def dedup (l : List BT) : List BT :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []
private def dsucc (n : Nat) (l : List BT) : List BT :=
  (List.range n).flatMap (fun u => l.map (fun a => BT.D u a))
private def sums (l : List BT) : List BT := l.flatMap (fun a => l.map (fun b => BT.add a b))
private def every (k : Nat) (l : List BT) : List BT :=
  (l.zipIdx.filter (fun p => p.2 % k == 0)).map (·.1)

private def lvl0 : List BT := [.zero, one, ofNat 2, omega, Om 1, Om 2, Om 3]
private def lvl1 : List BT := dedup ((lvl0 ++ dsucc 4 lvl0).filter isStd)
private def lvl2 : List BT := dedup ((lvl1 ++ dsucc 4 lvl1).filter isStd)
/-- Nesting corpus: D_u-towers of depth ≤ 3 over the seeds. -/
private def cD : List BT := every 5 (dedup ((dsucc 3 lvl2).filter isStd))
/-- Sum corpus: standard binary sums of the depth-2 terms. -/
private def cS : List BT := every 5 (dedup ((sums (every 3 lvl2)).filter isStd))

-- (B) every produced term is a term of 𝔗(M)
#guard lvl2.all fun a => TM.Term.inT (dict a)
#guard cD.all fun a => TM.Term.inT (dict a)
#guard cS.all fun a => TM.Term.inT (dict a)

-- (C) order preservation, both directions, over all pairs
private def okPair (a b : BT) : Bool := BT.lt a b == TM.Term.lt (dict a) (dict b)
#guard lvl2.all fun a => lvl2.all fun b => okPair a b
#guard cD.all fun a => cD.all fun b => okPair a b
#guard cS.all fun a => cS.all fun b => okPair a b

-- (C) injectivity (implied by the above under trichotomy, checked separately anyway)
#guard lvl2.all fun a => lvl2.all fun b => (a == b) == (dict a == dict b)
#guard cD.all fun a => cD.all fun b => (a == b) == (dict a == dict b)
#guard cS.all fun a => cS.all fun b => (a == b) == (dict a == dict b)

end Test

/-! ### The equational layer for `dict`

`dict` is a structural recursion, so each clause holds by `rfl`.  Stating them as named
theorems is not decoration: a proof about `dict (f n)` for an open `n` cannot unfold `dict`
by computation, and these are what `rw` fires on.  Same reason as `ofMatrix_append` in
`Trans/Recal.lean` — see the note there. -/

#guard dict BT.zero == TM.Term.zero
#guard dict (.D 0 .zero) == collapse 0 (dict .zero)
#guard dict (.D 2 (.D 1 .zero)) == collapse 2 (dict (.D 1 .zero))
#guard dict (.sum (.D 0 .zero) (.D 1 .zero)) ==
  TM.Term.plus (dict (.D 0 .zero)) (dict (.D 1 .zero))
#guard dict (.sum (.D 2 (.D 0 .zero)) (.D 0 (.D 1 .zero))) ==
  TM.Term.plus (dict (.D 2 (.D 0 .zero))) (dict (.D 0 (.D 1 .zero)))

theorem dict_zero : dict BT.zero = TM.Term.zero := rfl

theorem dict_D (u : Nat) (a : BT) :
    dict (.D u a) = collapse u (dict a) := rfl

theorem dict_sum (a b : BT) :
    dict (.sum a b) = TM.Term.plus (dict a) (dict b) := rfl


/-! ## §4 THE ANCHOR WHERE THIS DICTIONARY DISAGREES WITH ITS OWN SOURCES

This file's header states the dictionary's purpose: an order-isomorphism onto its image.
**That is a goal, not a theorem** — it is checked by the `#guard`s above and proved nowhere.
At one measured point the dictionary and the sources it was built from give DIFFERENT
ordinals, and the difference is not notation.

The point is BMS `(0,0)(1,1)(2,2)`.  Its Buchholz value is `ψ₀(ψ₂(0))`, and three
independent things agree on that: this repository's own port of naruyoko's pss2bp
(the `#guard` below computes it), Hexirp's published analysis, and the spreadsheet.
The disagreement is entirely in the step FROM Buchholz TO 𝔗(M):

    dict     ψ_Ω(Z 1)             = ψ_Ω(χ₁(0)) = ψ_Ω(Ω₂)
    sources  ψ_Ω(φ̄(1, Ω+1))       = ψ_Ω(ε_{Ω+1})

Both are `inT`-valid, they are not equal, and the sources' value is STRICTLY SMALLER.
The sources are P進大好きbot's diary and the BMS-vs-Rathjen spreadsheet — both unproved,
which is why this section proves only what is decidable here: that the two values differ
and how they compare.  Which is CORRECT is a separate question, and one this file cannot
settle.

**RETRACTED (2026-08-12): the order-inversion refutation that stood here.**  It claimed
281 inversions among 3174 standard Buchholz terms.  Every one of them was an artefact of
a WRONG CORPUS, and the section now records what actually happened, because the mistake
is more useful than the claim was.

The corpus was filtered by naruyoko's `isStandardBuchholz`, called as an external reference implementation.
Its helper has a callback-arity bug:

    function G(a,u){
      if (a instanceof Array) return a.flatMap(G);   // <-- flatMap passes (elem, INDEX, arr)
      ...u<=a.sub?[a.inner].concat(G(a.inner,u)):[];
    }

`Array.prototype.flatMap` hands its callback `(element, index, array)`, so on a sum the
parameter `u` receives the array INDEX.  The k-th summand is visited at level `k` instead
of the level being threaded through.  This repository's `BT.isStd` threads `u` correctly
and therefore disagreed — which is how the bug was found, from a worker's note that the
two predicates differed on one term.

Re-running the identical search with the corrected predicate:

    corpus            3193 standard terms (size ≤ 7, subscripts ≤ 3, sums ≤ 3 summands)
    ordered pairs     5096028
    dict inversions   0
    images ∉ inT      0
    control           a constant map inverts all 5096028 — the scan does fire

The two corpora differ by 25 terms: the bug wrongly ADMITTED 3 and wrongly REJECTED 22.
**All 281 reported inversions came from the 3 wrongly admitted terms**, which are not
Buchholz normal forms at all, so they were never evidence of anything.  They are pinned
below as negative controls.

So `dict`'s order-preservation is **not refuted, and not proved either**.  It survives a
5-million-pair search, which is what the `#guard`s above always claimed and no more.

What still stands is the anchor disagreement above: `anchorBT` IS a normal form
(`#guard` below), so `dict_anchor_ne_sources` is unaffected.  The table's values above
Γ₀ therefore rest on a translation that disagrees with both outside sources at its first
measured point — a reason to warn, but no longer a proof of defect.

`oRB` — the BMS → Buchholz half — was never in question; `scripts/xlsx-buchholz-check.py`
measures it against the spreadsheet's Buchholz column as terms.
-/

/-! The three terms the buggy reference implementation admitted.  Every retracted inversion involved one
    of them.  Kept as permanent negative controls: if `BT.isStd` ever starts accepting
    these, the corpus that refuted `dict` becomes reachable again. -/

def badStd1 : BT := .D 0 (.sum (.D 1 .zero) (.D 0 (.D 2 .zero)))
def badStd2 : BT := .D 0 (.sum (.D 1 .zero) (.D 0 (.D 3 .zero)))
def badStd3 : BT := .D 0 (.sum (.D 2 .zero) (.D 0 (.D 3 .zero)))

theorem badStd_not_standard :
    BT.isStd badStd1 = false ∧ BT.isStd badStd2 = false ∧ BT.isStd badStd3 = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- and the shape the reference implementation got right, for contrast: the anchor is a normal form.
#guard BT.isStd (BT.D 0 (BT.D 2 BT.zero))

def anchorBT : BT := BT.D 0 (BT.D 2 BT.zero)

/-- What the sources give for the same Buchholz value: `ψ_Ω(ε_{Ω+1})`. -/
def anchorSrc : TM.Term := TM.Term.psi (TM.Term.Z TM.Term.zero)
  (TM.Term.phi TM.Term.one (TM.Term.add (TM.Term.Z TM.Term.zero) TM.Term.one))

-- `anchorBT` は BMS `(0,0)(1,1)(2,2)` の Buchholz 値である。ここでは検算できない
-- (`Trans/Recal.lean` がこのファイルを import する側なので、依存が逆になる)。
-- 検算は `Trans/Recal.lean` 側の #guard と `scripts/external-check.py` にある。
#guard inT (dict anchorBT) && inT anchorSrc

theorem dict_anchor_ne_sources : dict anchorBT ≠ anchorSrc := by decide

theorem sources_lt_dict_anchor : TM.Term.lt anchorSrc (dict anchorBT) = true := by decide

theorem dict_anchor_both_inT : inT (dict anchorBT) = true ∧ inT anchorSrc = true := by
  constructor <;> decide

/-! ## 5. `reg 2` の測定 (2026-08-13) — 何が直り、何が直らないか

**`reg (u+1) = Z u` は $`u \geq 1`$ で誤っている。** Buchholz の $`\Omega_{u+1}`$ を
`Z u` に送るが、`Z 1` は $`\chi_1(0) = I`$ であって $`\Omega_2 = \chi_0(1)`$ では
ない。そして $`\Omega_2`$ は $`\mathfrak{T}(M)`$ に項を持たない ([R91] §2 が
$`\chi`$ を $`\alpha \mapsto \chi_\alpha(0)`$ に潰しているため; `plan/chi-2ary.md`)。

**測定。** 第三者の対応表 (Hexirp 氏。`scripts/hexirp-rathjen-check.py` で再実行できる)
と突き合わせられる表の行は 41。`reg 2` だけを差し替えて全行を計算した:

    reg 2                資料と一致した行
    Z 1 (現状)                 20 / 41
    φ̄(1,Ω) = ε_{Ω+1}          33 / 41      ← 13 行が直る
    φ̄(1,Ω+1)                  20 / 41
    (対照として 2 つ)

**残る 8 行は全部 $`\Omega_2`$ の倍数である。** 資料が言う対応は

    Ω₂     ↦ ε_{Ω+1} = φ̄(1,Ω)
    Ω₂·2   ↦ ε_{Ω+2} = φ̄(1,Ω+1)
    Ω₂·3   ↦ ε_{Ω+3}

で、これは $`\Omega_2`$ 単独の像から決まらない。`collapse` の強臨界枝は
$`d = \mathrm{mulL}\ e\ c`$ で和しか作れないので、$`\varepsilon_{\Omega+1}\cdot 2`$
は出せても $`\varepsilon_{\Omega+2}`$ は出せない。**`reg` の置換では原理的に届かない。**

**したがって直し方は「$`\Omega`$ 階層のところだけ compositional をやめる」ことになる。**
$`\Omega_2`$ の倍数を引数の中で見つけて $`\varepsilon`$ の添字に変換する必要があり、
それは `reg` ではなく `collapse` の側の変更である。

**41/41 まで届く規則をデータから読んだ。**

    dict (D 2 y)          = φ̄(1, Ω + sub1(ω^(dict y)))
    Ω₂·(1+k) (= 同じ `D 2 y` が k+1 個並ぶ和)  = φ̄(1, Ω + k)

`sub1` が `y = 0` の場合をちょうど拾い、φ̄ の不動点飛ばしが `Ω → ε_{Ω+1}` の +1 を出す。
**生の `phi` を使うこと**が要で、`phiNF 1 Ω = Ω` (素の Veblen 値) では潰れる。

**そしてこの規則は `collapse` には置けない。証明つきで置けない。**

    dict (Ω₂)      = φ̄(1,Ω)
    dict (ψ₁(Ω₂))  = ω^(Ω + φ̄(1,Ω)) = φ̄(1,Ω)      ← 同じ項

    資料は両者を区別する:
      Ω₂ + Ω₂        ↦ φ̄(1, Ω+1)          添字が進む
      Ω₂ + ψ₁(Ω₂)    ↦ φ̄(1,Ω) + φ̄(1,Ω)    和のまま

像が一致するので、**像の関数はこの 2 つを分離できない**。`collapse` は引数の像しか
見ないので、修理は Buchholz 側の構文が残っている `dict` に置くしかない。
実際 `collapse` 側に置いた版は 32/41 で止まり、落ちるのはちょうどこの区別である。

**代償は `dict_sum` である。** `dict (sum a b) = plus (dict a) (dict b)` は、
同じ `D 2 y` の連なりを束ねる規則と両立しない。`dict_zero` と `dict_D` は残せる
(`D 2` の式を `collapse 2` に置けばよい)。`dict_sum` は
`Evidence/Cert.lean:11538` の証明で使われている。

**実装して測った。入れられない。** 上の規則を `collapse 2` と `dict` の和の節に入れ、
`reg 2` も揃えた版を作ったところ:

    表 51 行のうち値が動く行  23   そのうち証明を持つ行 0 (全部 `ev := "oR"` の行)
    資料との一致              41/41
    しかし (C) 順序保存が破れる対   lvl2 976 / 112²、cD 296 / 54²、cS 3121 / 149²
                単射が破れる対      8

    最小の衝突: `D 2 0` と `D 1 (D 2 0)` がどちらも `φ̄(1,Ω)` になる。
    `collapse 1` が `phiNF 1 (Ω+1) = φ̄(1,Ω)` を出すため — また不動点飛ばしである。

**そして資料の側も順序を保っていない。** 訳せる 1249 行を我々の順序で測ると

    相異なる項 1244 / 1249      順序対のうち (潰れ, 反転) = (2, 1728)

我々の 51 行のうち 41 行で一致したのは事実だが、**1249 行に広げると資料の割り当ては
`TM.Term.lt` と整合しない**。原因は三つのどれかで、まだ切り分けていない:
資料が順序を保っていない / 我々の `lt` が ψ・Z の領域で誤っている /
`phiNF` の橋渡しが ψ・Z の引数で誤っている。

**したがって「資料の値に合わせる」は目標として成立しない。** 21 行が誤っていることは
変わらないが、正しい値が何かは 1 つの資料の値表では決まらない。決めるには
ψ・Z 領域で順序と値が同時に整合する情報源か、閉包集合の定義からの導出が要る。

判定器はすべて残してある (`scripts/hexirp-rathjen-check.py` と上の表)。
-/

end Dict
end Trans
