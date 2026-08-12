/-
Trans/DictInv.lean — the inverse of `dict`, on the Veblen fragment (2026-08-13)

WHY.  `dict : BT → Term` is the second stage of `oR` and the weakest link in this
repository: `Trans/Dict.lean` calls itself "candidate / 予想 tier", its order-preservation
is measurement rather than theorem, and at `(0,0)(1,1)(2,2)` it disagrees with every
external source that has been checked.  Every gate in `Evidence/SqV.lean` compares two
things built from each other — GATE 1 is a round trip through `oR`, GATES 2 and 3 match
`sqv` against the table — so none of them can see an error in `dict`.  A round trip
through an INVERSE is the first check on `dict` that needs no external oracle.

HOW IT WAS DERIVED — from `wcnf`/`collapse`, not guessed:

    wcnf w splits each AP component p of the argument as p = ω^g with g = w·a + r,
    and reports the pair (a, c) with c = ω^r; that is p = Ω^a·c.
    collapse 0 turns a single pair (a,c) into φ̄(a, c⊖1), so  φ̄(a,b) ↦ D 0 (Ω^a·(1+b)).
    dict (D 1 x) = ω^(Ω + dict x), measured; so  Ω^a·q = D 1 (inv (Ω·(a⊖1) + logOm q)).

TWO PLACES WHERE THE OBVIOUS READING IS WRONG, both found by the round trip failing:

  * An AP term ≥ Ω must NOT go through `D 0`.  `D 0` is ψ₀, which collapses there; the
    right clause is ω^(Ω+y) = `D 1 (inv y)`.  Without it `φ̄(ω,0)` fails.
  * The second argument of `φ̄` is not `b` but the SEMANTIC argument `β°` of [R91] 2.7,
    because `φ̄` re-counts fixed points.  `phiShifted` is exactly that test.  Without it
    every row of the shape `φ̄(1,ζ₀) = ε_{ζ₀+1}` fails — the same trap as §K3.20 and as
    `TM/FS.lean`'s provenance check, for the third time in one day.

SCOPE, and it is drawn where the derivation is verified rather than where it is
convenient.  The Veblen fragment, `Z δ` for a numeral δ, and `ψ_{Z δ}(i)` for `i < Z δ`.
Outside that it returns `none`, never a wrong answer.

The `ψ` branch above is derived by reading `collapse`'s strongly critical case at `a = w`,
which makes `e = 0`, `d = c` and `i = c ⊖ 1`.  That reading is only valid while `i < w`.
For `i ≥ w` the correct `a` is a different one — `ψ_Ω(Ω₂)` inverts to `D 0 (D 2 0)`, i.e.
`a = Ω₂`, not `a = Ω` — and a first version that ignored this produced twelve wrong table
rows, all differing in the same way (`Z(1)` against `φ̄(1,Ω)`).  It now returns `none`
there.  **That is the interesting region**: `(0,0)(1,1)(2,2)` and everything §Γ₀ of the
table warns about live in it, and the round trip cannot yet speak about them.

MEASURED (see the section at the bottom):
    generated CNV corpus, 750 terms      dict ∘ dictInv = id on 750, none on 0
    table rows, 51                       28 round trip, 23 none, 0 wrong
    BT pool, 117 standard terms          115 syntactically equal, 117 equal as values
-/
import Trans.Dict
import Rows.TM

namespace Trans
namespace Dict

open TM (Term)
open TM.Term


/-- The index of `Z d` / `ψ_{Z d}` as a numeral, when it is one. -/
def natOfT (t : Term) : Option Nat :=
  if t == zero then some 0
  else if (toList t).all (· == TM.Term.one) then some (toList t).length else none

/-- `dict` の逆。導出は `wcnf`/`collapse` の読みから:
      p = ω^g,  g = Ω·a + r   ⇒  p = Ω^a·ω^r
      dict (D 1 x) = ω^(Ω + dict x)  ⇒  Ω^a·q = D 1 (inv (Ω·(a⊖1) + logOm q))
      collapse 0 (Ω^a·c) = φ̄(a, c⊖1)  ⇒  φ̄(a,b) ↦ D 0 (Ω^a·(1+b)) -/
def invF : Nat → Term → Option BT
  | 0, _ => none
  | _+1, .zero => some BT.zero
  | _+1, .Z d => (natOfT d).map (fun u => BT.D (u+1) BT.zero)
  | f+1, .psi (.Z d) i =>
      -- collapse u の強臨界枝を a = w で読むと e = 0, d = c, i = c⊖1。
      -- よって ψ_w(i) ← x = w^w·(1+i)、成分ごとに w^w·q = ω^(w·w + logOm q)。
      -- i < w のときだけ。この枝の導出は `a = w`(⇒ e = 0, d = c) を仮定しており、
      -- i ≥ w では正しい `a` が違う: ψ_Ω(Ω₂) の逆は `D 0 (D 2 0)` で a = Ω₂ である。
      -- そこを埋めるまでは誤答ではなく `none` を返す。
      match (if lt i (Z d) then natOfT d else none) with
      | none => none
      | some u =>
        let w : Term := Z d
        let c := plus TM.Term.one i
        (((toList c).mapM (fun q =>
            (invF f (plus (mulL w w) (logOm q))).map (BT.D (u+1))))).map
          (fun l => BT.D u (BT.ofL l))
  | f+1, (.add u v) => ((toList (.add u v)).mapM (invF f)).map BT.ofL
  | f+1, (.phi a b) =>
      if !(lt (.phi a b) (Z .zero)) then
        -- Ω 以上の加法主要項は ω^(Ω+y)。D 0 は ψ₀ なのでここでは潰してしまう。
        (invF f (subAP (Z .zero) (logOm (.phi a b)))).map (BT.D 1)
      else if a == zero then (invF f (logOm (.phi a b))).map (BT.D 0)
      else
        -- 意味上の第 2 引数 (β° of [R91] 2.7)。φ̄ は不動点を飛ばすので b そのものではない。
        -- ここを b にすると φ̄(1,ζ₀) 型の行が全部落ちる (今日 3 度目の同じ罠)。
        let bs := if phiShifted a b then plus b TM.Term.one else b
        let c := plus TM.Term.one bs
        (((toList c).mapM (fun q =>
            (invF f (plus (mulL (Z .zero) (sub1 a)) (logOm q))).map (BT.D 1)))).map
          (fun l => BT.D 0 (BT.ofL l))
  | _+1, _ => none

def dictInv (t : Term) : Option BT := invF (2 * t.deg + 12) t


/-! ## Acceptance record.  Both controls are here: a perturbed target must never match,
    and the `none` count must be printed next to the success count so that "0 wrong" is
    never read as "everything covered". -/

def rt (t : Term) : Bool := match dictInv t with | some b => dict b == t | none => false

private def pool0 : List Term := [zero, TM.Term.one, phi TM.Term.one zero, phi zero TM.Term.one]
private def grow (p : List Term) : List Term :=
  (p ++ (p.flatMap fun x => p.map fun y => phi x y)
     ++ (p.flatMap fun x => p.map fun y => TM.Term.add x y)).eraseDups
def corpus : List Term := (grow (grow pool0)).filter fun t =>
  Evidence.WF.CNV t && !(t == zero)

-- the Veblen fragment: a right inverse, with nothing undefined
#guard corpus.all rt
#guard corpus.all fun t => (dictInv t).isSome
#eval (corpus.length, corpus.countP rt)
-- CTRL a perturbed target must never match
#guard corpus.all fun t => !(match dictInv t with
                             | some b => dict b == TM.Term.add t t
                             | none => false)

-- the table: everything it is defined on round-trips; the rest is honestly `none`
#eval (Rows.rows.countP fun r => rt r.t,
       Rows.rows.countP fun r => (dictInv r.t).isNone,
       Rows.rows.length)
#eval (Rows.rows.filter fun r => !(rt r.t) && (dictInv r.t).isSome).map fun r =>
  (r.name, r.t.toStr, ((dictInv r.t).map fun b => (dict b).toStr).getD "?")
#guard Rows.rows.all fun r => rt r.t || (dictInv r.t).isNone

-- the other direction, from the BT side
private def seeds : List BT := [BT.zero, BT.one, BT.Om 1, BT.omega]
private def bgrow (p : List BT) : List BT :=
  (p ++ (p.flatMap fun x => [BT.D 0 x, BT.D 1 x])
     ++ (p.flatMap fun x => p.map fun y => BT.add x y)).eraseDups
def btPool : List BT := (bgrow (bgrow seeds)).filter BT.isStd
-- as VALUES it is exact; syntactically two terms come back in a different representation,
-- which is what `dict` not being injective looks like and is not an error.
#guard btPool.all fun b => match dictInv (dict b) with
                           | some c => dict c == dict b
                           | none => false
#eval (btPool.length, btPool.countP fun b => dictInv (dict b) == some b)

end Dict
end Trans
