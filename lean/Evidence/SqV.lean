import Trans.TM
import Trans.Pair
import Trans.Recal
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

PRICED AGAINST veblen2's SYNTACTIC CRITERION (2026-08-10, at the coordinator's ask).
That lane decided the φ̄0 branch split — a fixed-point question — with a purely SYNTACTIC
test, 0 disagreements over 3723 terms and no `isFP`.  Does it transfer to the encoding?
MEASURED, and the answer is exactly half:

    at a = 0   `isFP zero b` agrees with the shape test
               `(isSC b ∧ b ≠ 0) ∨ (b = φ̄(c,·) ∧ c ≠ 0)`  on ALL 234 corpus terms
    at a = 1   the same shape test DISAGREES on 36 of 234, always by over-reporting

WHY, in one line: `isFP a g` tests `lt a c` for `g = φ̄(c,·)`, and at `a = 0` that
degenerates to `c ≠ 0` — a shape test — while at `a ≥ 1` it is a genuine comparison of
two terms.  The sharpest witness is the pair `isFP 1 (φ̄(1,0)) = false` against
`isFP 1 (φ̄(2,0)) = true`: ε₀ is not a fixed point of φ̄1 and ζ₀ is, the shape test cannot
tell them apart, and the difference is precisely whether `c > a`.

SO THE ENCODING NEEDS MORE THAN THE ROUTING DOES, and the reason is not that the encoding
is harder in general: the routing only ever asks the question AT a = 0, where it is
syntactic.  A total map asks it at every `a` it encounters.  That is the same
totality argument as below, now with the exact boundary measured rather than asserted.

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

(e) IS CANDIDATE 3 AND (f) IS CANDIDATE 4 (`omLog`, below).  §3 records what (f)
actually turned out to be, which is NOT specific to the finite part: at `a ≠ 0` the
whole subscript block denotes the ω-EXPONENT of the subscript.  Writing (f) down as a
statement about finite parts was reading the class off the smallest witness — right
about the rows it was measured on, and one generalisation short.

-/

/-- Bump the columns that sit exactly at depth `d` to level 1. -/
def bumpAt (d : Nat) (cs : List Col2) : List Col2 :=
  cs.map (fun c => if c.1 == d then (c.1, 1) else c)

/-- **The ω-exponent of an additively principal term.**  `ω^x ↦ x`; a term that is its
    own ω-power — every `φ̄(c,·)` with `c ≠ 0`, since `ω^ε₀ = ε₀` — goes to itself.
    §3's cause 1: at `a ≠ 0` the block after the ladder denotes the EXPONENT of the
    subscript, not the subscript.  At `a = 0` it does not, so this is applied on one
    side of that branch only. -/
def omLog : Term → Term
  | .phi .zero x => x
  | t => t

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
        let sub : List Col2 :=
          match bm.1 with
          | zero => []
          | b' =>
            -- CANDIDATE 4 (§3, cause 1): at `a ≠ 0` the block is the ω-EXPONENT
            let b'' := if a == zero then b' else omLog b'
            shiftD (if a == zero then d + 1 else d + 2) (encvF f b'' 0)
        -- the trailing finite part repeats the LADDER TAIL, not a single marker column
        let unit : List Col2 := if a == zero then [(d + 1, 0)] else ladder
        let reps : List Col2 := (List.replicate bm.2 unit).flatten
        (d, 0) :: (ladder ++ sub ++ reps)
  | _ + 1, _, _ => []

def encv (t : Term) (d : Nat) : List Col2 := encvF (2 * t.deg + 8) t d

def sqv (t : Term) : BMS.Matrix := toMatrix (encv t 0)

/-! ### §1.1 `Trans.o?` IS RETRACTED ABOVE A THRESHOLD — a permanent negative control
    (2026-08-10; my first reading of this was wrong, and the correction is the point)

Candidate 3 fixes failure class (e) and refines class (a) (the trailing finite part
repeats the LADDER TAIL, not a single marker column — four witnesses: `φ̄(1,1)`,
`φ̄(2,1)`, `φ̄(3,1)`, `φ̄(ω,1)`).  After both, `sqv` reproduces the `t2m` corpus exactly on
those rows — and the round-trip gate still failed them.

I REPORTED THAT AS A CONTRADICTION BETWEEN TWO PEER INSTRUMENTS.  IT IS NOT.
`Trans.o?` is the OLD, RETRACTED translation, and I was using it outside its validated
region.  Measured over the 51 rows of `Rows.rows` (by the coordinator, reproduced here
on my own guards):

    o? = none  (out of domain)                      23
    o? defined and AGREES with oR                   21
    o? defined and DISAGREES with oR                 7    ← silently wrong

The seven begin at exactly `(0,0)(1,1)(2,1)(2,0)`, which is the threshold named in the
table's own accident warning, and the values `o?` returns there are the RETRACTED ones
verbatim — `(0,0)(1,1)(2,1)(2,1) ↦ ζ₁` is the row on which the calibration accident was
FIRST DETECTED.  `t2m` agrees with `oR` and with the table on both witnesses.  So the
instruments were never peers: one is calibrated and one is withdrawn.

WHAT THE TWO `#guard`s BELOW NOW MEAN.  They are no longer evidence about a matrix's
value — banking a retracted value as a datum is exactly the accident's mechanism.  They
are a PERMANENT NEGATIVE CONTROL: they record that `o?` disagrees with `oR` above the
threshold, and they will fail if anyone ever "fixes" `o?` by making it agree, or reaches
for it in this region again.

THE INSTRUMENT RULE, so the next reader does not repeat it: `Trans.o?` is valid strictly
BELOW `(0,0)(1,1)(2,1)(2,0)`; `Trans.oR` is the instrument for the φ̄(a ≥ 2) region.  This
file's gate 1 now uses `oR`, and the number moved 31 → 16 — HALF THE FAILURES WERE THE
INSTRUMENT, not the map.

AUDIT OF MY OWN GUARDS, run after the correction: every matrix that `Evidence/Cert.lean`
§16.4, §16.5, §20.1 and §20.2 measure with `o?` agrees with `oR` — all eight named
matrices and all three expansion families, checked one by one.  None of them enforces a
retracted value.  The `t2m`-derived tables in §16.4/§16.5 are also safe, since `t2m`
agrees with `oR`.

WHAT SURFACED IT, and the part worth keeping: `sqv (o? (sqv t)) == sqv t` holds for 0 of
the 31 failures.  A gate that only confirmed agreement would have passed all of this
silently, and I would have tuned `sqv` toward the retracted values — reproducing the
calibration accident from the inside, on the row where it was first detected. -/

#guard !(Trans.o? [[0, 0], [1, 1], [2, 1], [2, 1]]
          == Trans.oR [[0, 0], [1, 1], [2, 1], [2, 1]])
#guard Trans.oR [[0, 0], [1, 1], [2, 1], [2, 1]] == some (phi (ofNat 3) zero)
#guard Trans.oR [[0, 0], [1, 1], [2, 1], [1, 1], [2, 1]] == some (phi (ofNat 2) one)

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

-- GATE 1: the round trip through the repository's CALIBRATED translation.
-- `Trans.oR`, NOT `Trans.o?` — see §1.1: `o?` is retracted above a threshold and
-- returns a wrong term there rather than `none`, so a gate built on it would have
-- been enforcing pre-accident values.
#eval (corpus.filter (fun t => !(Trans.oR (sqv t) == some t))).length

-- GATE 2: the table's own rows, matched exactly
#eval (twelveRows.filter (fun p => !(sqv p.2 == p.1))).length

-- GATE 3: the two refutations, matched exactly
#eval (discriminators.filter (fun p => !(sqv p.2 == p.1))).length

-- the corpus size, so that "0 failures" is never read as "0 tested"
#eval corpus.length

/-! ## §3 THE SIXTEEN, DECODED  (measurement, 2026-08-10)

Every earlier failure count was contaminated by the retracted oracle (§1.1), so these
sixteen are the first honest measurement of what `sqv` gets wrong.  They are separated
here by WHERE THE DISAGREEMENT LIVES, not by how hard they look.

    encoding-side   (the map is wrong and `oR` is right)     16
    routing-side    (a shape the branch table routes)         0
    undecided                                                 0

CANDIDATE 4 THEN FIXED CAUSE 1 AND THE RESIDUE IS EXACTLY WHAT THIS SECTION PREDICTED:

                        candidate 1   candidate 2   candidate 3   candidate 4
    round trip / 234         90            34            16             4
    table rows / 5            3             1             1             0
    discriminators / 3        2             2             1             1

The four survivors are the four members of cause 2, by name — `φ̄(0,ε₀+1)` and
`φ̄(a,ε₀+ε₀)` for `a ∈ {1,2,ω}` — and nothing that passed before broke.  That the
residue is the predicted SET and not merely the predicted COUNT is the check worth
having: a count can come out right by two errors cancelling.  Cause 2 is untouched.

ZERO ROUTING-SIDE, and the reason is structural rather than lucky: every failure is a
matrix that `oR` decodes to a DIFFERENT TERM, so the disagreement is always about what
the map computes, never about which clause a shape should take.  A routing-side failure
would have looked different — `sqv` producing the table's own matrix for a shape the
branch table sends elsewhere — and none of the sixteen does that.

THEY REDUCE TO TWO CAUSES, and both are the same mistake: the additive structure of the
SUBSCRIPT is not peeled before the clause is chosen.

CAUSE 1 (12 of 16) — AT `a ≠ 0` THE SUBSCRIPT BLOCK DENOTES THE ω-EXPONENT OF THE
SUBSCRIPT, and `sqv` writes the subscript itself.  This is failure class (f), which
turns out not to be about the finite part specially:

    sqv (φ̄(1,ω)) = (0,0)(1,1)(2,0)(3,0)   and  oR of that = φ̄(1,ω^ω)

i.e. `sqv` emits, verbatim, the matrix of a DIFFERENT TABLE ROW — the row whose
subscript is `ω^(mine)`.  The table's ε_ω row is (0,0)(1,1)(2,0), one column, and
(0,0)(1,1)(2,0)(3,0) is its ε_{ω^ω} row.  Eight `#guard`s below confirm the rule at
`a = 1, 2, ω` and at subscripts `ω, ω+1, ω², ω^ω, ε₀`; the ε₀ case is why the
discriminator passed all along — `ω^ε₀ = ε₀`, so the bug is invisible exactly there.
Members: `φ̄(a,b)` for `a ∈ {1,2,ω}` and `b ∈ {ω, ω+1, ω², ω^ω}`.

CAUSE 2 (4 of 16) — THE ADDITIVE SUMMANDS OF THE SUBSCRIPT MUST BE SEPARATED BY A
REPEAT OF THE LADDER, and `sqv` concatenates them bare.  `sqv`'s `reps` clause already
does exactly this for the FINITE part (`splitFin`'s `m`); the correction is that every
summand needs it, not only the finite ones:

    φ̄(1, ε₀+ε₀) = (0,0)(1,1)(2,0)(3,1) (1,1)(2,0)(3,1)     ← ladder column between
    sqv gives     (0,0)(1,1)(2,0)(3,1)      (2,0)(3,1)     ← read by oR as φ̄(1,ω^(ε₀·2))

This class was NOT an expressibility problem, which is what it looked like before the
matrix was measured: `ω^X` is always additively principal, so `φ̄(1,ε₀·2)` cannot be a
subscript block under Cause 1's rule, and the natural conclusion was that the region
cannot express it.  It can — the ladder repeat is the mechanism, and guessing instead
of asking `oR` would have produced a clause for a problem that does not exist.
Members: `φ̄(a, ε₀+ε₀)` for `a ∈ {1,2,ω}`, plus `φ̄(0, ε₀+1)` at `a = 0`, where the same
peel is missing in a different place — `isFP` is tested on `b` when it must be tested
on `b`'s infinite part, so an `add` never reaches the collapse clause at all.

AND A PROPERTY OF THE GATE SUITE ITSELF, which is the reason gate 3 exists.  Gate 3's
one failure is `φ̄(0, ε₀·2)`, and GATE 1 PASSES IT: `oR` sends the wrong matrix and the
right matrix to the SAME term, so a round trip cannot separate them, while `cmpM` says
they are different matrices (`.lt`).  The round-trip gate is blind to standard form.
Whether the one `sqv` produces is non-standard is not something this file can decide —
there is no Bool standard-form test in `BMS/` — and that is a question for the BMS
lane, not a claim about `oR`. -/

-- CAUSE 1, the rule: at `a ≠ 0` the block after the ladder is the ω-EXPONENT.
#guard Trans.oR [[0,0],[1,1],[2,0]]             == some (phi one omega)
#guard Trans.oR [[0,0],[1,1],[2,0],[1,1]]       == some (phi one (plus omega one))
#guard Trans.oR [[0,0],[1,1],[2,0],[2,0]]       == some (phi one (phi zero (ofNat 2)))
#guard Trans.oR [[0,0],[1,1],[2,0],[3,0]]       == some (phi one (phi zero omega))
#guard Trans.oR [[0,0],[1,1],[2,0],[3,1]]       == some (phi one (phi one zero))
#guard Trans.oR [[0,0],[1,1],[2,1],[2,0]]       == some (phi (ofNat 2) omega)
#guard Trans.oR [[0,0],[1,1],[2,1],[2,0],[2,0]] == some (phi (ofNat 2) (phi zero (ofNat 2)))
#guard Trans.oR [[0,0],[1,1],[2,1],[3,0],[2,0]] == some (phi omega omega)

-- CAUSE 1, FIXED (candidate 4).  The `#guard` two lines above is the baseline that
-- makes this one mean something: candidate 3 emitted (0,0)(1,1)(2,0)(3,0), which is the
-- ε_{ω^ω} row, and the map now emits the ε_ω row the table lists.
#guard sqv (phi one omega) == [[0,0],[1,1],[2,0]]
#guard Trans.oR (sqv (phi one omega)) == some (phi one omega)
#guard sqv (phi (ofNat 2) omega) == [[0,0],[1,1],[2,1],[2,0]]
#guard sqv (phi omega omega) == [[0,0],[1,1],[2,1],[3,0],[2,0]]
#guard sqv (phi one (plus omega one)) == [[0,0],[1,1],[2,0],[1,1]]

-- CAUSE 2: the ladder column separates the summands, and `sqv` omits it.
#guard Trans.oR [[0,0],[1,1],[2,0],[3,1],[1,1],[2,0],[3,1]]
         == some (phi one (plus (phi one zero) (phi one zero)))
#guard sqv (phi one (plus (phi one zero) (phi one zero)))
         == [[0,0],[1,1],[2,0],[3,1],[2,0],[3,1]]
#guard Trans.oR [[0,0],[1,1],[1,0],[1,0]] == some (phi zero (plus (phi one zero) one))
#guard sqv (phi zero (plus (phi one zero) one)) == [[0,0],[1,0],[2,1],[1,0]]

-- THE GATE SUITE'S OWN LIMIT: two distinct matrices, one term.  Gate 1 cannot see it.
#guard Trans.oR [[0,0],[1,0],[2,1],[1,0],[2,1]] == Trans.oR [[0,0],[1,1],[1,0],[2,1]]
#guard BMS.cmpM [[0,0],[1,0],[2,1],[1,0],[2,1]] [[0,0],[1,1],[1,0],[2,1]] == Ordering.lt
#guard !(Trans.oR (sqv (phi zero (plus (phi one zero) (phi one zero)))) == none)

end Evidence.SqV
