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

Three things were got wrong first and fixed by the round trip failing, in this order:

  * `i < w` (`a = w`, so `e = 0`, `d = c`, `i = c ⊖ 1`) is only one case.  For `i ≥ w`
    the pair `(a,c)` is exactly what `wcnf w (1+i)` reports: `a = w + A`, `c = C`.  A
    version that put the multiplicity into `a` instead of `c` missed eight rows.
  * an AP term above `Ω` is `ω^(Z u + y)` for SOME `u`, not always `u = 0`; applying
    `D 1` to a term above `Ω₂` turns `Ω₂` into `φ̄(1,Ω)` and missed six more.
  * `collapse` accumulates `i = (d₁ ⊖ 1) + d₂ + …` over several strongly critical pairs,
    so every pair `wcnf` reports is used, not just the first.

WHAT IS STILL `none`, and why it is the interesting part.  Twelve table rows, every one
with an index of the form `Ω₂ + …`.  They fail on an inner subterm, not on the index
decomposition: `invF` cannot yet name an ε-number strictly between `Z k` and `Z (k+1)`
that is not of the form `ω^(Z k + y)` — `φ̄(1,Ω)` is the smallest — because `logOm` of it
is itself, `subAP` has nothing to strip, and the recursion regresses to the same term
until the fuel runs out.  Such terms come out of `collapse`'s VEBLEN branch above `Ω`
(base `= Ω+1`), which this file does not invert yet.

`(0,0)(1,1)(2,2)` and everything §Γ₀ of the table warns about live in that region, so the
round trip still cannot speak about the place where `dict` is actually in doubt.

MEASURED (see the section at the bottom):
    generated CNV corpus, 750 terms      dict ∘ dictInv = id on 750, none on 0
    table rows, 51                       39 round trip, 12 none, 0 wrong
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
      match natOfT d with
      | none => none
      | some u =>
        let w : Term := Z d
        let P := plus TM.Term.one i
        if lt i w then
          -- `a = w` ⇒ e = 0, d = c, i = c ⊖ 1。成分ごとに w^w·q = ω^(w·w + logOm q)。
          (((toList P).mapM (fun q =>
              (invF f (plus (mulL w w) (logOm q))).map (BT.D (u+1))))).map
            (fun l => BT.D u (BT.ofL l))
        else
          -- i ≥ w。d = ω^(w·(a⊖w))·c を (a,c) について解くのは、まさに `wcnf` の逆である。
          -- `wcnf w (1+i)` が一組 (A,C) と空の尾部を返すなら a = w + A、c = C。
          -- 多重度は `a` ではなく `c` に入る — 最初に `a` へ入れて表を 8 行外した。
          -- 組は 1 つとは限らない。`collapse` の畳み込みは強臨界の組ごとに
          -- i = (d₁ ⊖ 1) + d₂ + … と積むので、1+i の組を全部使えばよい。
          match wcnf w (toList P) with
          | ([], _) => none
          | (ps, tl) =>
            if tl == zero then
              let x := ofList (ps.flatMap (fun AC =>
                (toList AC.2).map (fun q =>
                  omegaNF (plus (mulL w (plus w AC.1)) (logOm q)))))
              (invF f x).map (BT.D u)
            else none
  | f+1, (.add u v) => ((toList (.add u v)).mapM (invF f)).map BT.ofL
  | f+1, (.phi a b) =>
      if !(lt (.phi a b) (Z .zero)) then
        -- Ω 以上の加法主要項は ω^(Z u + y) で、BT では `D (u+1) (inv y)` である。
        -- どの階層かを探す必要がある: Ω₂ 以上の項に `D 1` を当てると Ω₂ が φ̄(1,Ω) に
        -- 化ける (表を 6 行外した)。上限 8 は表と併走コーパスの Z 添字より十分大きく、
        -- 外れたときは誤答ではなく `none` になる。`D 0` は ψ₀ なのでここでは潰す。
        let g := logOm (.phi a b)
        match (List.range 8).reverse.find? (fun k => le (Z (TM.Term.ofNat k)) g) with
        | some k => (invF f (subAP (Z (TM.Term.ofNat k)) g)).map (BT.D (k+1))
        | none => none
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
