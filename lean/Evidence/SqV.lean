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

/-- The additive summands of a term, left to right; `0` has none.  §3's cause 2: the
    summands of a SUBSCRIPT are separated by a repeat of the ladder, so the encoder has
    to see them individually rather than encode the sum as one block. -/
def summands : Term → List Term
  | .zero => []
  | .add u v => summands u ++ summands v
  | t => [t]

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
      let bm := TM.Term.splitFin b
      let gs := summands bm.1
      let ladder : List Col2 :=
        if a == zero then [] else (d + 1, 1) :: bumpAt (d + 2) (encvF f (predOr a) (d + 2))
      -- the trailing finite part repeats the LADDER TAIL, not a single marker column
      let unit : List Col2 := if a == zero then [(d + 1, 0)] else ladder
      let reps : List Col2 := (List.replicate bm.2 unit).flatten
      -- CANDIDATE 4 (§3, cause 1): at `a ≠ 0` the sub-block is the ω-EXPONENT.
      -- CANDIDATE 5 (§3, cause 2): one LADDER per additive summand of the subscript.
      let mkBlocks : List Term → List Col2 := fun hs =>
        (hs.map (fun g =>
          ladder ++ shiftD (if a == zero then d + 1 else d + 2)
            (encvF f (if a == zero then g else omLog g) 0))).flatten
      -- CANDIDATE 7 (§3, cause 3): the fixed-point test is applied to the SUMMANDS of
      -- the subscript's infinite part, not to `b` — so `ε₀+1` and `ε₀·k` reach the
      -- collapse clause, which they never did while `isFP` saw only the `add`.  The
      -- FIRST fixed-point summand is collapsed (its own encoding becomes the head) and
      -- every later one is an ordinary summand block, exactly as in the else branch.
      -- CANDIDATE 8 (§4): the test is on the FIRST summand alone.  `gs.all` was the
      -- all-or-nothing reading of "only the first summand collapses", and it sent
      -- MIXED subscripts (`ε₀+ω`) to the else branch, where they round-tripped
      -- correctly and emitted a NON-STANDARD matrix.
      if TM.Term.isFP a (gs.headD zero) then
        encvF f (gs.headD zero) d
          ++ (if gs.length == 1 then [((d + 1, if a == zero then 0 else 1) : Col2)]
              else mkBlocks (gs.drop 1))
          ++ reps
      else
        (d, 0) :: ((match gs with | [] => ladder | _ => mkBlocks gs) ++ reps)
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

EACH CAUSE WAS FIXED SEPARATELY AND RE-MEASURED, AND EACH RESIDUE WAS THE PREDICTED
SET rather than merely the predicted count — a count comes out right when two errors
cancel, so the survivors were checked BY NAME every time:

                        cand 1   cand 2   cand 3   cand 4   cand 5   cand 6   cand 7   cand 8
    round trip / 234       90       34       16        4        1        0        0        0
    table rows / 5          3        1        1        0        0        0        0        0
    discriminators / 3      2        2        1        1        1        0        0        0
    NON-STANDARD / 234      ?        ?        2        2        2        0        0        0
    §4 open cases / 2       -        -        2        2        2        2        0        0
    §4.1 mixed / 5          -        -        ?        ?        ?        ?        5        0

  cand 4 = `omLog`      (cause 1)   residue: the 4 of causes 2 and 3, by name
  cand 5 = `summands`   (cause 2)   residue: the 1 of cause 3
  cand 6 = per-summand `isFP`       (cause 3), fitted to k ≤ 2 — WRONG at k = 3
  cand 7 = §4's rule: only the FIRST fixed-point summand collapses
  cand 8 = §4.1: test `isFP` on the first summand ALONE — `gs.all` emitted
           non-standard matrices on mixed subscripts while round-tripping correctly

THE NON-STANDARD ROW IS THE ONE THAT COULD NOT BE MEASURED IN LEAN, and it is the row
that matters most.  `BMS.Standard` is `Reach (init h) M`, a Prop with a positive route
only, so a matrix can be proved standard and not refuted.  The repo's instrument for
the negative direction is yaBMS `bms -s`, which `scripts/standard-audit.sh` runs in CI;
the coordinator ran it on the three bucket witnesses and I then ran it over all 234.
At candidate 5, TWO outputs were non-standard, and **one of them passed the round
trip** — `φ̄(0,ε₀·2)`, whose wrong matrix and right matrix have the same `oR` value.
That failure was visible to gate 3 and to `bms -s` and to nothing else.

A RULE FOUND FIVE MINUTES AGO IS A MEASUREMENT, NOT A LAW.  Cause 1's rule says the
subscript block is an ω-exponent; since `ω^X` is always additively principal, the rule
says `φ̄(1,ε₀·2)` cannot be written at all, and cause 2 was one sentence from being
filed as an expressibility limit of the region.  Asking `oR` for the matrix instead of
deriving from the fresh rule produced it immediately — the ladder repeat separates the
summands.  Deriving from a rule this young is the same error as deriving from the
order side, and it would have left the file carrying both a clause for a problem that
does not exist and a false limitation.

WHEN A DISCRIMINATOR PASSES, ASK WHAT ITS OWN PARAMETERS DEGENERATE.  Cause 1 survived
`φ̄(1,ε₀)` for three candidates because `ω^ε₀ = ε₀`: at an ε-number subscript the defect
is invisible, and ε₀ is exactly the subscript the discriminator was built from.  The
test was blind inside a region in the same way that `isFP` at `a = 0` and `kindC`'s
dropped conjunct are free inside one.

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
The one `sqv` produced WAS non-standard — `bms -s` says 0 — so gate 3 was catching a
matrix that is not a notation of the system at all, not merely one with a wrong value. -/

/-! ## §4 THE VALIDATED RANGE, and how the k ≥ 3 rule was MEASURED rather than guessed

The corpus carries at most TWO fixed-point summands in a subscript, so candidate 6's
collapse rule — first summand takes the marker, each further one a single column at
depth `d+2` — was fitted to k ≤ 2 and had no evidence beyond it.  This section is what
happened when the two witnesses outside the corpus were measured instead of designed.

CANDIDATE 6 WAS WRONG AT k = 3, AND WRONG IN THE WAY THE OBVIOUS EXTRAPOLATION IS:

    sqv (φ̄(0,ε₀·3)) = (0,0)(1,1)(1,0)(2,1)(2,1)     NON-STANDARD, and `oR` reads it as ε₁
    sqv (φ̄(1,ζ₀·2)) = (0,0)(1,1)(2,1)(1,1)(2,1)     standard, but it is φ̄(2,1)

Repeating the `(2,1)` is what k ≤ 2 suggests and it is not what the region does.

HOW THE TRUE MATRIX WAS FOUND, since guessing again was not available: enumerate every
matrix (0,0)(1,1)(1,0) ++ s with `s` up to three columns from a 6×3 grid — 6175 of them
— keep those `oR` sends to the target, then keep those `bms -s` calls STANDARD.  72
matrices decode to `φ̄(0,ε₀·3)` and exactly ONE of them is standard.  `oR` alone cannot
pick it out; it maps a non-standard matrix to the value of its standard form, which is
the same blindness §3 records for the round-trip gate.  The same search at `a = 1` gave
12 decodings and again exactly one standard.

    φ̄(0, ε₀·3)   (0,0)(1,1)(1,0)(2,1)(1,0)(2,1)
    φ̄(1, ζ₀·2)   (0,0)(1,1)(2,1)(1,1)(2,0)(3,1)(4,1)

AND THE TWO SIDES TURNED OUT TO BE ONE RULE.  Read against the clause that already
existed, the extra columns are not a new construct: `(1,0)(2,1)` is `shiftD 1 (encv ε₀ 0)`
and `(1,1)(2,0)(3,1)(4,1)` is `ladder ++ shiftD 2 (encv ζ₀ 0)` — i.e. each summand after
the first is an ORDINARY summand block, the same one cause 2 introduced.  Only the FIRST
fixed-point summand is collapsed.  Candidate 7 is that sentence, and it needed no new
machinery; what it needed was for k = 2 to stop being the whole evidence.

THE RANGE IT IS NOW VALIDATED ON: `a = 0` at k = 1,2,3,4,5 and `a ≠ 0` at k = 1,2,3, all
against the unique standard matrix, with k = 4 and k = 3 predicted by the clause BEFORE
they were looked up.  Beyond that it is untested, and the honest statement is the one
this section began with: a rule fitted to k ≤ 2 was wrong at k = 3, so a rule fitted to
k ≤ 5 is evidence and not a law. -/

def openCases : List Term :=
  [phi zero (plus (phi one zero) (plus (phi one zero) (phi one zero))),
   phi one (plus (phi (ofNat 2) zero) (phi (ofNat 2) zero))]

-- 0 since candidate 7; it was 2 under candidate 6, which is the point of the list
#eval (openCases.filter (fun t => !(Trans.oR (sqv t) == some t))).length

-- the two matrices the search found, and the two the clause then PREDICTED
#guard sqv (phi zero (plus (phi one zero) (plus (phi one zero) (phi one zero))))
         == [[0,0],[1,1],[1,0],[2,1],[1,0],[2,1]]
#guard sqv (phi one (plus (phi (ofNat 2) zero) (phi (ofNat 2) zero)))
         == [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1]]
#guard sqv (phi zero (plus (phi one zero) (plus (phi one zero)
           (plus (phi one zero) (phi one zero)))))
         == [[0,0],[1,1],[1,0],[2,1],[1,0],[2,1],[1,0],[2,1]]
#guard sqv (phi one (plus (phi (ofNat 2) zero) (plus (phi (ofNat 2) zero)
           (phi (ofNat 2) zero))))
         == [[0,0],[1,1],[2,1],[1,1],[2,0],[3,1],[4,1],[1,1],[2,0],[3,1],[4,1]]
-- and the candidate-6 outputs, kept so the improvement is not merely asserted
#guard Trans.oR [[0,0],[1,1],[1,0],[2,1],[2,1]] == some (phi one one)
#guard Trans.oR [[0,0],[1,1],[2,1],[1,1],[2,1]] == some (phi (ofNat 2) one)

/-! ### §4.1 MIXED SUBSCRIPTS — the class the round trip could not see

Candidate 7's collapse test was `gs.all isFP`, the all-or-nothing reading of "only the
first summand collapses".  A subscript with a fixed point AND a non-fixed point — `ε₀+ω`
— therefore failed the test entirely and fell to the else branch.  What that produced:

    sqv (φ̄(0,ε₀+ω)) = (0,0)(1,0)(2,1)(1,0)(2,0)          ROUND TRIP TRUE, NON-STANDARD
    sqv (φ̄(1,ζ₀+ω)) = (0,0)(1,1)(2,0)(3,1)(4,1)(1,1)(2,0)  ROUND TRIP TRUE, NON-STANDARD

BOTH ROUND-TRIP CORRECTLY.  Gates 1–3 were 0/0/0 and `openCases` was 0 while the map was
emitting matrices that are not notations of the system, and the class is not exotic —
it is any subscript mixing an ε-number with anything below it.  It was found only
because `bms -s` was run over the corpus rather than over the three witnesses that had
already failed something else.  **A gate suite reading all-zero is a statement about the
dimensions it measures.**

The same search that settled k = 3 settled these: 8 and 61 decodings respectively, one
standard each, and both are exactly what candidate 7's own sentence predicts —
`encv g₁ 0 ++ mkBlocks [ω]`.  So the sentence was right and the CONDITION was wrong;
candidate 8 tests `isFP` on the first summand alone.  Nothing else changed.

    φ̄(0, ε₀+ω)   (0,0)(1,1)(1,0)(2,0)
    φ̄(1, ζ₀+ω)   (0,0)(1,1)(2,1)(1,1)(2,0)

`mixed` is kept permanently: it is the smallest set that fails if the collapse test ever
goes back to reading all the summands. -/

def mixed : List Term :=
  [phi zero (plus (phi one zero) omega),
   phi one (plus (phi (ofNat 2) zero) omega),
   phi zero (plus (phi one zero) (plus omega one)),
   phi (ofNat 2) (plus (phi (ofNat 2) zero) omega),
   phi zero (plus (phi one zero) (plus (phi one zero) omega))]

#eval (mixed.filter (fun t => !(Trans.oR (sqv t) == some t))).length

#guard sqv (phi zero (plus (phi one zero) omega)) == [[0,0],[1,1],[1,0],[2,0]]
#guard sqv (phi one (plus (phi (ofNat 2) zero) omega)) == [[0,0],[1,1],[2,1],[1,1],[2,0]]
-- the candidate-7 outputs: right value, and NOT a notation of the system (`bms -s` = 0)
#guard Trans.oR [[0,0],[1,0],[2,1],[1,0],[2,0]] == some (phi zero (plus (phi one zero) omega))
#guard Trans.oR [[0,0],[1,1],[2,0],[3,1],[4,1],[1,1],[2,0]]
         == some (phi one (plus (phi (ofNat 2) zero) omega))

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

-- CAUSE 2 and CAUSE 3, FIXED (candidates 5 and 6).  Candidate 4 emitted
-- (0,0)(1,1)(2,0)(3,1)(2,0)(3,1) and (0,0)(1,0)(2,1)(1,0) for these two; the second of
-- those was NON-STANDARD, which is why the fix is checked against `bms -s` and not
-- only against the round trip.
#guard Trans.oR [[0,0],[1,1],[2,0],[3,1],[1,1],[2,0],[3,1]]
         == some (phi one (plus (phi one zero) (phi one zero)))
#guard sqv (phi one (plus (phi one zero) (phi one zero)))
         == [[0,0],[1,1],[2,0],[3,1],[1,1],[2,0],[3,1]]
#guard Trans.oR [[0,0],[1,1],[1,0],[1,0]] == some (phi zero (plus (phi one zero) one))
#guard sqv (phi zero (plus (phi one zero) one)) == [[0,0],[1,1],[1,0],[1,0]]
#guard sqv (phi zero (plus (phi one zero) (phi one zero))) == [[0,0],[1,1],[1,0],[2,1]]

-- THE GATE SUITE'S OWN LIMIT: two distinct matrices, one term.  Gate 1 cannot see it.
#guard Trans.oR [[0,0],[1,0],[2,1],[1,0],[2,1]] == Trans.oR [[0,0],[1,1],[1,0],[2,1]]
#guard BMS.cmpM [[0,0],[1,0],[2,1],[1,0],[2,1]] [[0,0],[1,1],[1,0],[2,1]] == Ordering.lt
#guard !(Trans.oR (sqv (phi zero (plus (phi one zero) (phi one zero)))) == none)

end Evidence.SqV
