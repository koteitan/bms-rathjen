import Trans.TM
import Trans.Pair
import TM.FS
import Evidence.WF
/-
Evidence/SqV.lean — the term-to-matrix map for the Veblen region (STARTED)

`Evidence/Cert.lean` §10's `sq` maps a Cantor normal form to a ONE-ROW BM4 sequence,
and §11–§12 turn that into the certificate families below ε₀.  The twelve rows above
ε₀ leave that region at the first expansion (Cert.lean §16), so they need the
two-row analogue.  This file is that map and, first of all, ITS GATE.

THE DISCIPLINE, decided by the coordinator and followed here: `sqv` is written and
`#eval`-GATED BEFORE ANYTHING IS PROVED ABOUT IT.  A map that fails the gate costs
nothing to discard; a map that is proved about before it is gated costs a section.

THE ROUTE, decided after two refuted attempts (Cert.lean §16.4, §16.5): a T(M)-side
recursion carrying a LEVEL PARAMETER, with the fixed-point split as a genuine third
clause.  This is `sq`'s own pattern made explicit — `sq (phi _ b) = 0 :: (sq b).map (· + 1)`
already carries a level, hard-coded at one because in the CNF region the first Veblen
argument is always `0`.  The corpus says the shift has to depend on that argument.

WHAT 273 `t2m` PAIRS ESTABLISH (Cert.lean §16.5), i.e. the specification:

  SUM        sqv (u ⊕ v) = sqv u ++ sqv v            — plain concatenation, ~100 pairs
  BASE       φ̄(0,b) for non-fixed-point b is `padRow ∘ sq`
  COLLAPSE   when `isFP a b` (Cert.lean §16.3's criterion) the matrix is `sqv b` with
             ONE column appended, and the column depends only on `a`:
                 φ̄(0,ε₀) ↦ sqv ε₀ ++ (1,0)      φ̄(1,ζ₀) ↦ sqv ζ₀ ++ (1,1)
  OPEN       φ̄(a,b) with `a ≠ 0` and NOT a fixed point — the clause the level
             parameter is for, and the one the gate below is here to discriminate.

TWO TESTS THAT DISCRIMINATE, both from the refutations, so a candidate that passes
the easy cases but repeats an old error is caught:
  φ̄(0, ε₀·2) ↦ (0,0)(1,1)(1,0)(2,1)   — kills `(0,0) :: shift₁ (sqv b)` as the base clause
  φ̄(1, ε₀)   ↦ (0,0)(1,1)(2,0)(3,1)   — kills "append the marker", since φ̄(1,ζ₀) does append it

`t2m` (the surveys' dictionary-inverse plus Buchholz-side encoder) is CANDIDATE TIER.
It appears nowhere in this file.  The gate below compares `sqv` against the
REPOSITORY's own instruments only: `Trans.o?` for the round trip, and the literal
matrices of the table's rows.
-/

namespace Evidence.SqV

open TM (Term)
open TM.Term

/-- A column of the two-row region, as a pair. -/
abbrev Col2 := Nat × Nat

def toMatrix (cs : List Col2) : BMS.Matrix := cs.map (fun c => [c.1, c.2])

/-- Shift a block to a greater first-row depth; the second row is untouched. -/
def shiftD (d : Nat) (cs : List Col2) : List Col2 := cs.map (fun c => (c.1 + d, c.2))

/-! ## §1 THE CANDIDATE

CANDIDATE 1.  The three established clauses, with the OPEN clause filled in by the
`a = 1` data read as "root, then a marker for `a`, then `b` one level deeper".

GATE RESULT FOR CANDIDATE 1 — IT FAILS, as expected, and the failures are the
specification of candidate 2.  Round trip: 90 of 234 corpus terms.  Table rows: 3 of
5.  Discriminators: 2 of 3.  The four failure classes, each with the witness the
gate printed:

  (a) THE TRAILING FINITE PART OF THE SUBSCRIPT IS ABSORBED AS REPEATS OF THE
      `a`-MARKER, at the SAME depth — not as a deeper block:
          φ̄(1,1) = (0,0)(1,1)(1,1)          candidate said (0,0)(1,1)(2,0)
          φ̄(1,2) = (0,0)(1,1)(1,1)(1,1)
          φ̄(1,ω+1) = (0,0)(1,1)(2,0)(1,1)   — infinite part, THEN one repeat
      This is `TM.Term.splitFin` (β = γ ⊕ m, the number of trailing `1`s) appearing
      in the encoding, and it is the same mechanism `sq` uses for finite exponents.

  (b) AN `φ̄(0,·)` SUBSCRIPT LOSES ITS ROOT COLUMN one level down:
          φ̄(1,ω) = (0,0)(1,1)(2,0)           candidate said (0,0)(1,1)(2,0)(3,0)
          φ̄(1,ω^ω) = (0,0)(1,1)(2,0)(3,0)
      i.e. the subscript contributes `sq`'s tail, not `sq` itself — whereas a
      subscript that is itself an ε-number keeps its full block:
          φ̄(1,ε₀) = (0,0)(1,1)(2,0)(3,1)

  (c) THE FIRST ARGUMENT NEEDS ITS OWN LADDER, which candidate 1 has not got at all:
          φ̄(2,0) = (0,0)(1,1)(2,1)           candidate said (0,0)(1,1)
          φ̄(3,0) = (0,0)(1,1)(2,1)(2,1)      — the repeat mechanism of (a), one level in
          φ̄(ω,0) = (0,0)(1,1)(2,1)(3,0)      — and the drop of (b), one level in

  (d) THE BASE CLAUSE IS WRONG WHEN THE EXPONENT CONTAINS AN ε-NUMBER — this is the
      §16.5 refutation, and candidate 1 walks into it:
          φ̄(0, ε₀·2) = (0,0)(1,1)(1,0)(2,1)  candidate said (0,0)(1,0)(2,1)(1,0)(2,1)

CANDIDATE 2 is therefore: the `a`-ladder of (c), the `splitFin`-driven marker repeats
of (a), the root-drop of (b) for `φ̄(0,·)` subscripts, and a base clause that respects
(d).  Note that (a) and (b) recur INSIDE (c) — the first argument is encoded by the
same rules one level in — which is what "carrying a level parameter" means here and
is the reason the parameter cannot be eliminated. -/

/-- `encv t d` : the columns of `t` at first-row depth `d`. -/
def encv : Term → Nat → List Col2
  | zero, _ => []
  | add u v, d => encv u d ++ encv v d
  | phi a b, d =>
      if TM.Term.isFP a b then
        -- COLLAPSE: `b`'s own block, then one column determined by `a`
        encv b d ++ [(d + 1, if a == zero then 0 else 1)]
      else if a == zero then
        -- BASE: the CNF clause of `sq`, padded
        (d, 0) :: shiftD 1 (encv b d)
      else
        -- OPEN: root, marker for `a`, then `b` one level deeper
        (d, 0) :: (d + 1, 1) :: shiftD (d + 1) (encv b 1)
  | _, _ => []

def sqv (t : Term) : BMS.Matrix := toMatrix (encv t 0)

/-! ## §2 THE GATE

Three checks, in increasing strength.  None of them may ever be used as the
justification of a certificate: they say what `sqv` computes, and a certificate has
to be PROVED, by the `sqv_decomp` this file does not have yet. -/

/-- The twelve rows above ε₀, with the matrices the table lists. -/
def twelveRows : List (BMS.Matrix × Term) :=
  [([[0,0],[1,1],[0,0]], plus (phi one zero) one),
   ([[0,0],[1,1],[1,0]], phi zero (phi one zero)),
   ([[0,0],[1,1],[1,1]], phi one one),
   ([[0,0],[1,1],[2,0]], phi one omega),
   ([[0,0],[1,1],[2,1]], phi (ofNat 2) zero)]

/-- The discriminating pairs of the two refutations. -/
def discriminators : List (BMS.Matrix × Term) :=
  [([[0,0],[1,1],[1,0],[2,1]], phi zero (plus (phi one zero) (phi one zero))),
   ([[0,0],[1,1],[2,0],[3,1]], phi one (phi one zero)),
   ([[0,0],[1,1],[2,1],[1,1]], phi one (phi (ofNat 2) zero))]

/-- A corpus of Veblen-region terms: `φ̄ a b` over a grid, plus sums. -/
def bases : List Term :=
  [zero, one, ofNat 2, ofNat 3, omega, plus omega one, phi zero (ofNat 2), phi zero omega,
   phi one zero, plus (phi one zero) one, plus (phi one zero) (phi one zero),
   phi one one, phi (ofNat 2) zero]

def corpus : List Term :=
  (bases.flatMap (fun b => [phi zero b, phi one b, phi (ofNat 2) b, phi omega b])) ++
  (bases.flatMap (fun a => bases.map (fun b => plus a b))) ++ bases

-- GATE 1: the round trip through the repository's own translation
#eval (corpus.filter (fun t => !(Trans.o? (sqv t) == some t))).length

-- GATE 2: the table's own rows, matched exactly
#eval (twelveRows.filter (fun p => !(sqv p.2 == p.1))).length

-- GATE 3: the two refutations, matched exactly
#eval (discriminators.filter (fun p => !(sqv p.2 == p.1))).length

-- the corpus size, so that "0 failures" is never read as "0 tested"
#eval corpus.length

end Evidence.SqV
