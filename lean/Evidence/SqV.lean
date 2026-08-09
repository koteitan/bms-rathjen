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

WHY THE FIXED-POINT MACHINERY IS UNAVOIDABLE HERE AND NOT ON THE OTHER SIDE
(measured by the coordinator, 2026-08-10, correcting a first guess that the two
sides were seeing one fact twice — they are not, and the asymmetry is the point).

`Evidence/WF.lean`'s Veblen templates — `lim_clauses_repAdd`, `lim_clauses_fsGen`,
`lim_clauses_phi_arg` — use `isFP` / `splitFin` / `phiShifted` NOWHERE; every
occurrence past its §15 is prose, in the §15.3 note explaining why a GENERAL `fsN`
theory would need them.  That lane escaped the machinery by going PER ROW with closed
forms: a closed form is written for one term, and no term has to ask whether it is a
fixed point of itself.

`sqv` cannot escape it, and not because of how it is written.  A TOTAL map over the
region must decide, for every input, which clause applies — and "is `b` a fixed point
of `φ̄a`" IS that decision (failure class (b) below).  So the `isFP` split is not an
artefact of this encoding that a cleverer definition might remove: it is the price of
TOTALITY, which the per-row route does not pay because it never generalises over the
region at all.  Route (ii) (a dictionary to Buchholz trees) would have moved the same
decision into the dictionary rather than removing it, since `enc` is total too.
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

GATE RESULT FOR CANDIDATE 1 — IT FAILED, as expected, and the failures were the
specification of candidate 2.  Round trip: 90 of 234 corpus terms.  Table rows: 3 of
5.  Discriminators: 2 of 3.  The four failure classes, each with the witness the
gate printed:

  (a) THE TRAILING FINITE PART OF THE SUBSCRIPT IS ABSORBED AS REPEATS OF THE
      `a`-MARKER, at the SAME depth — not as a deeper block:
          φ̄(1,1) = (0,0)(1,1)(1,1)          candidate 1 said (0,0)(1,1)(2,0)
          φ̄(1,ω+1) = (0,0)(1,1)(2,0)(1,1)   — infinite part, THEN one repeat
      This is `TM.Term.splitFin` (β = γ ⊕ m) appearing in the encoding.

  (b) AN `φ̄(0,·)` SUBSCRIPT LOSES A COLUMN one level down, where an ε-number
      subscript does not:
          φ̄(1,ω) = (0,0)(1,1)(2,0)           φ̄(1,ε₀) = (0,0)(1,1)(2,0)(3,1)

  (c) THE FIRST ARGUMENT NEEDS ITS OWN LADDER, recursively:
          φ̄(2,0) = (0,0)(1,1)(2,1)   φ̄(3,0) = (0,0)(1,1)(2,1)(2,1)
          φ̄(ω,0) = (0,0)(1,1)(2,1)(3,0)

  (d) the base clause walked into §16.5's refutation on φ̄(0, ε₀·2).

CANDIDATE 2 — below — takes (a) as `splitFin`-driven repeats, (c) as a recursive
`a`-ladder with the level bumped one depth in, and keeps the collapse and sum clauses.
IT IS A MEASURED IMPROVEMENT, WHICH IS THE POINT OF KEEPING THE BASELINE:

                        candidate 1   candidate 2
    round trip / 234         90            34
    table rows / 5            3             1
    discriminators / 3        2             2

TWO CLASSES REMAIN, and they are sharper than anything candidate 1 could have told us:

  (e) DEPTH OF THE SUBSCRIPT WHEN `a ≠ 0`.  `φ̄(1,ε₀)` wants `(0,0)(1,1)(2,0)(3,1)` —
      ε₀'s own two columns shifted by TWO — and candidate 2 puts them at depth 1.
      So the subscript of a Veblen term sits one level deeper than the `a = 0` case,
      which is the level parameter doing its job and is a one-line fix.

  (f) THE "1 +" CONVENTION IN SUBSCRIPT POSITION.  `φ̄(1,ω)` wants `(0,0)(1,1)(2,0)` —
      ONE column for the subscript ω — while ω's own encoding is `(0,0)(1,0)`, two
      columns.  A finite part in subscript position is off by one against the same
      part at the root.  This is the convention the surveys' own validation reported
      as its four mismatches, so it is a property of the ENCODING and not of this
      candidate; (e) and (f) interact, and the next iteration should fix (e) first
      and re-measure before touching (f).

-/

/-- Bump the columns that sit exactly at depth `d` to level 1. -/
def bumpAt (d : Nat) (cs : List Col2) : List Col2 :=
  cs.map (fun c => if c.1 == d then (c.1, 1) else c)

/-- `t` minus one when it has a trailing `1`; `t` itself otherwise. -/
def predOr (t : Term) : Term :=
  match TM.Term.splitFin t with
  | (_, 0) => t
  | (g, m + 1) => plus g (ofNat m)

/-- CANDIDATE 2 — `encvF f t d` : the columns of `t` at first-row depth `d`.
    Fuel, as `ltF`/`starF`/`iterParent` do it: the `predOr` recursion is not
    structural, and at the gate stage a termination proof would be premature. -/
def encvF : Nat → Term → Nat → List Col2
  | 0, _, _ => []
  | _ + 1, zero, _ => []
  | f + 1, add u v, d => encvF f u d ++ encvF f v d
  | f + 1, phi a b, d =>
      if TM.Term.isFP a b then
        encvF f b d ++ [(d + 1, if a == zero then 0 else 1)]
      else
        let bm := TM.Term.splitFin b
        let ladder : List Col2 :=
          if a == zero then [] else (d + 1, 1) :: bumpAt (d + 2) (encvF f (predOr a) (d + 2))
        let lvl : Nat := if a == zero then 0 else 1
        let sub : List Col2 :=
          match bm.1 with
          | zero => []
          | b' => shiftD (d + 1) (encvF f b' 0)
        let reps : List Col2 := List.replicate bm.2 (d + 1, lvl)
        (d, 0) :: (ladder ++ sub ++ reps)
  | _ + 1, _, _ => []

def encv (t : Term) (d : Nat) : List Col2 := encvF (2 * t.deg + 8) t d

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
