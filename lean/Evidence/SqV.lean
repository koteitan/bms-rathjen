import Trans.TM
import Trans.Pair
import Trans.Recal
import TM.FS
import Evidence.WF
import Evidence.Cert
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

/-! READ THE DENOMINATORS AS LIST LENGTHS, NOT SET SIZES.  Every "of 234" / "of 269" /
"of 1076" below counts LIST ENTRIES, and the lists contain duplicates — `corpus` is 234
entries over 119 DISTINCT terms.  No verdict is affected (zero over a multiset is zero
over its set) but every COVERAGE claim is, and coverage is what this file is about.  §8
has the full table; the candidate comparison in §1/§3 keeps its original denominators
deliberately, so that candidates 1–13 stay comparable.  Everything from §5 on states the
distinct count.

## §1 THE CANDIDATE

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

/-- The additive summands of a term, left to right; `0` has none.  §3's cause 2: the
    summands of a SUBSCRIPT are separated by a repeat of the ladder, so the encoder has
    to see them individually rather than encode the sum as one block. -/
def summands : Term → List Term
  | .zero => []
  | .add u v => summands u ++ summands v
  | t => [t]

/-- **The ω-exponent of an additively principal term.**  `ω^x ↦ x`; a term that is its
    own ω-power — every `φ̄(c,·)` with `c ≠ 0`, since `ω^ε₀ = ε₀` — goes to itself.
    §3's cause 1: at `a ≠ 0` the block after the ladder denotes the EXPONENT of the
    subscript, not the subscript.  At `a = 0` it does not, so this is applied on one
    side of that branch only. -/
def omLog : Term → Term
  | .phi .zero x =>
      -- CANDIDATE 9 (§5.2): T(M)'s `φ̄(0,·)` SKIPS the fixed points, so `φ̄(0,ε₀)` is
      -- `ω^(ε₀+1)` and its ω-exponent is `ε₀+1`, not `ε₀`.  Below a fixed point the
      -- two agree, which is why every corpus term was insensitive to this.
      -- MEASURED, and the mathematically obvious refinement is REFUTED: replacing this
      -- summand test by `isFP zero x` — on the grounds that `ω^(ε₀·2) ≠ ε₀·2`, so a sum
      -- of fixed points is not one — improves D5 (51→35 pairs, 14→10 terms) and BREAKS
      -- D6 (0→6).  It also does not move the four D1 failures I predicted it would fix.
      -- Neither form dominates, so the skip condition is not settled and the next step
      -- on it is a search for those four matrices, not a third guess.  §5.2.
      -- MEASURED at three points that separate the two obvious readings:
      --   x = ε₀     +1   (both readings agree)
      --   x = ε₀+1   +1   (`isFP zero x` says no, and FAILS)
      --   x = ε₀·2   NO   (the summand test says yes, and FAILS)
      -- so the test is ONE fixed-point summand, not "any" and not "x itself".
      match summands (TM.Term.splitFin x).1 with
      | [g] => if TM.Term.isFP zero g then plus x one else x
      | _ => x
  | t => t

/-- **The fixed point a subscript collapses ON, found through `φ̄(0,·)` layers.**
    `isFP a t` sees only the top constructor, so `φ̄(0,ε₀)` — which is `ω^(ε₀+1)`, not a
    fixed point — hides the ε₀ that the matrix language collapses on.  §5's nesting
    defect is exactly that: the corpus is one Veblen application deep, so no term ever
    had a fixed point one layer down.  Fuel for the same reason `encvF` has it. -/
def fpDeepF : Nat → Term → Term → Option Term
  | 0, _, _ => none
  | f + 1, a, t =>
      if TM.Term.isFP a t then some t
      else match t with
        | .phi _ x => (summands (TM.Term.splitFin x).1).findSome? (fpDeepF f a)
        | _ => none

def fpDeep (a t : Term) : Option Term := fpDeepF (t.deg + 4) a t

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
          ++ (if gs.length == 1 then (if a == zero then [((d + 1, 0) : Col2)] else ladder)
              else mkBlocks (gs.drop 1))
          ++ reps
      else
        -- CANDIDATE 10 (§5.2): the head summand is not itself a fixed point, but one
        -- sits below it through `φ̄(0,·)` layers.  Then the collapse head is THAT fixed
        -- point and the subscript follows WHOLE — not with its first summand dropped,
        -- which is the difference from the direct-collapse branch above.
        match fpDeep a (gs.headD zero) with
        | some g => encvF f g d ++ mkBlocks gs ++ reps
        | none => (d, 0) :: ((match gs with | [] => ladder | _ => mkBlocks gs) ++ reps)
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

/-! ## §5 THE TWO DIMENSIONS `sqv_decomp` WILL USE  (measurement, 2026-08-10)

§4.1 established that a gate suite reading all-zero is a statement about the dimensions
it measures.  The coordinator named the two this file had not measured, and they are
the two a certificate actually consumes: `Certified.lim`'s identity premise is
`∀ n, Certified (expand M n) (fs' n)`, so the map must carry the T(M) sequence to the
BMS expansion, and the (B) family construction leans on order.  **Both were measured
BEFORE any proof was attempted, and they do not agree with each other.**

ORDER PRESERVATION — PASSES.  Over all 234² = 54756 corpus pairs,

    lt t u  =  (cmpM (sqv t) (sqv u) == .lt)          0 disagreements

with the CONTROL (the same claim with the matrices swapped) failing 53446 of 54756, so
the test discriminates rather than being satisfied by everything.

EXPANSION — FAILS, and this is why nothing is proved yet.  Stated without any
fundamental sequence, so that it is about `sqv` alone: is every expansion of an encoded
matrix again an encoding?

    oR (expand (sqv t) n) = some u   and   sqv u = expand (sqv t) n
                                                   83 of 936 pairs FAIL, over 21 terms

(t over the corpus, n ≤ 3; control: the same with `expand (sqv t) (n+1)` on the right,
which holds for 312, so a third of the pairs would accept a wrong matrix and the 853
that pass are not passing by accident.)  A worked failure:

    t = ε₁, n = 2   expand (sqv ε₁) 2 = (0,0)(1,1)(1,0)(2,1)(2,0)(3,1)
                    oR of it = φ̄(0, φ̄(0, ε₀·2))
                    sqv of THAT = (0,0)(1,0)(2,1)(2,0)(3,1)      one column short

So `sqv` is wrong on a NESTED `φ̄(0,·)` whose inner subscript collapses, even though it
is right on the inner term itself — `sqv (φ̄(0,ε₀·2))` is the discriminator and passes.
The corpus never nests that way, which is why every gate in §2–§4.1 is clean.

AND THE INDEX SHIFT IS MATRIX-DETERMINED — a THIRD instrument saying so.  Measuring
against `TM.Term.fsN` first gave 612 of 624 failures, which is what sent me to the
fs-free form above.  **That number says nothing about `fsN`**: it is a UNIFORM shift
measured against a phenomenon that is not uniform.  Asking instead which shift `s` makes

    oR (expand (sqv t) n) = some (fsN t (n+s))            hold for all n ≤ 3

gives, per row:

    ε_ω = φ̄(1,ω)       s = 0
    φ̄(ω,0)             s = 2
    ε₀, ω^ω, ζ₀        s = 1
    ε₁ = φ̄(1,1)        NO s in 0..3 works at all

Three different shifts and one row where no shift exists — and for that row the WF
lane's own sequence does fit, at shift 0: `oR (expand (sqv ε₁) n) = fsEsucc 0 n` for
n ≤ 3, so ε₁ is a DIFFERENT sequence rather than a displaced one.  `fsEW` likewise fits
ε_ω at shift 0, agreeing with `fsN` there.  So `fsN` is not the wrong instrument; the
shift is simply not a function of the term.

`Rows/Proofs.lean` says the same thing from a third side: its nine E3 proofs use FOUR
conventions — `fsN t (n+1)` four times, `fsN t (n+2)` once, `fsN t n` twice, and two
bespoke sequences.  An earlier version of this paragraph said the repo states every E3
row with `+1`, which is wrong; the headers of `Trans/TM.lean` and `Rows/TM.lean` said so
and were corrected in 37cd066.  It is kept as a correction rather than deleted because
reading the repo's own statement form is the right move and it was the statement form
that was wrong.

ε₁'S ROW HAS BEEN CARRYING THE EVIDENCE ALL ALONG.  `Rows`' R3 is the ε₁ row and it has
an E3 proof; its sequence is neither `fsN` nor a shift of it but a hand-written
recursion, `oval 0 = ε₀`, `oval (n+1) = tow P0 n`.  Whoever proved that row could not use
`fsN` either.  So "no `s` works, it is a different sequence rather than a displaced one"
is not a new fact about ε₁ — it is the reason R3 has the shape it has, arrived at from
the encoding side.

THE THREE LEGS, and which of them are independent — this matters because the temptation
is to count data sets.  WF §15.22's core-(C) shifts and `table/index-shift-2026-08-10.txt`'s
five pairs are both `oR` measurements, so they are not independent OF EACH OTHER; the
per-row table above is a further data set on that same leg, not a third instrument.  The
independent leg is the E3 STATEMENTS: they are PROVED rather than measured, and they are
stated with `o?` rather than `oR` — a different translation function and a different kind
of evidence.  What the two legs jointly support: **the index is matrix-determined and no
property of the term computes it.**  ε₁'s line above is `sqv`'s own defect (the nested
case), not a shift and not `fsEsucc`'s.

The four `#guard`s below are that table, including the NEGATIVE one: a check that
`fsEsucc 0` fits ε₁ cannot show that no `fsN` shift does, and it is the second claim
that carries the paragraph.

CONSEQUENCE: `sqv_decomp` is NOT started.  Proving the recursion against a map that
fails image closure on 21 corpus terms would prove something false or carry a hypothesis
excluding them, which is the same objection that stopped the proof at candidate 4. -/

/-! ### §5.1 THE WIDENED CORPUS — chosen to CONTAIN the failure class

§5's failure class is a nested `φ̄(0,·)` whose inner subscript collapses, and `corpus`
is structurally blind to it: every corpus term is one Veblen application deep, so no
gate could ever have seen it.  Widening the corpus is therefore not "adding more terms"
— a wider corpus that happens not to reach the class would give six green dimensions
again and mean nothing, which is exactly how candidates 1–8 passed.

So the class is given a SYNTACTIC predicate first, independent of what `sqv` does with
it, and the new terms are counted against that predicate rather than against the current
defect.  `nestedFP t` asks whether `t` contains a Veblen application whose subscript is
itself a `φ̄(0,·)` whose own subscript has a fixed-point summand.

    nestedFP over `corpus`    0 of 234       ← the blindness, as a number
    nestedFP over `nested`   25 of  35       ← the widening, as a number

The operational count is reported beside it: 17 of the 35 new terms fail image closure
under candidate 8, and 16 fail the round trip.  Two counts rather than one, because the
syntactic one says the corpus reaches the class and the operational one says the class
is still live — neither implies the other.

THE NEW BASELINE, all six dimensions, candidate 8 unchanged:

                              corpus (234)        corpusW (269)
    D1 round trip               0 / 234            16 / 269      all 16 in `nested`
    D2 table rows               0 / 5               0 / 5
    D3 discriminators           0 / 3               0 / 3
    D4 NON-STANDARD             0 / 232            12 / 267      (`bms -s`)
    D5 image closure           83 / 936           130 / 1076     21 → 51 terms
    D6 order preservation       0 / 54756        1923 / 72361

**D6 WENT FROM GREEN TO RED, and that is the point of the exercise.**  Checkpoint 40
reported order preservation as the dimension `sqv` HAS; it was as corpus-blind as the
gates were.  All 35 new terms are `inT`, checked, so the order failures are real terms
and not artefacts of illegal ones — and they are downstream of the same nesting defect
(`ε₀ < φ̄(0,φ̄(0,ε₀))` holds in 𝔗(M) while the matrices do not compare that way, because
the right-hand matrix is wrong), so D6 has to be re-measured after the fix rather than
attacked separately.

Nothing is fixed against this baseline yet.  It exists so that the fix has something to
be measured against, which is what candidates 1–8 each had and what a fix invented from
the 21 witnesses of §5 would not.

### §5.2 THE NESTING FIX — candidates 9 and 10, measured against that baseline

TWO CAUSES, both found by SEARCHING for the true matrix rather than reading a rule off
the failures.  The enumerate-then-`bms -s` method of §4 was reused: each target has many
decodings under `oR` and exactly one standard one.

  CAUSE A (`a ≠ 0`) — `omLog` ignored the SKIP.  T(M)'s `φ̄(0,·)` enumerates past its own
  fixed points, so `φ̄(0,ε₀)` is `ω^(ε₀+1)` and its ω-exponent is `ε₀+1`, not `ε₀`.  Below
  a fixed point the two coincide, which is why 234 corpus terms were insensitive.
      φ̄(1, φ̄(0,ε₀))  =  (0,0)(1,1)(2,0)(3,1)(2,0)        searched, unique standard

  CAUSE B (`a = 0`) — `isFP` sees only the top constructor, so a fixed point one
  `φ̄(0,·)` layer down is invisible and the subscript never collapses.  `fpDeep` descends
  through those layers; when it finds one, the collapse head is THAT fixed point and the
  subscript follows WHOLE — not with its first summand dropped, which is what separates
  this from the direct-collapse branch.
      φ̄(0, φ̄(0,ε₀))     =  (0,0)(1,1)(1,0)(2,1)(2,0)             searched
      φ̄(0, φ̄(0,ε₀·2))   =  (0,0)(1,1)(1,0)(2,1)(2,0)(3,1)        from §5's expansion
      φ̄(0, φ̄(0,φ̄(0,ε₀))) = (0,0)(1,1)(1,0)(2,1)(2,0)(3,1)(3,0)   PREDICTED, then checked
      φ̄(0, φ̄(0,ε₀+1))   =  (0,0)(1,1)(1,0)(2,1)(2,0)(2,0)        PREDICTED, then checked

  The last two were computed from the rule before being looked up, which is the only
  reason it is stated at four points rather than fitted to two.

RESULT ON THE WIDENED CORPUS:

                              baseline (cand 8)    cand 10
    D1 round trip               16 / 269            4 / 269
    D2 table rows                0 / 5              0 / 5
    D3 discriminators            0 / 3              0 / 3
    D4 NON-STANDARD             12 / 267            0 / 267
    D5 image closure           130 / 1076          51 / 1076    51 → 14 terms
    D6 order preservation     1923 / 72361          0 / 72361

D6 returning to 0 is the load-bearing line: §5.1 predicted the order failures were
DOWNSTREAM of the nesting defect rather than a second defect, and fixing the nesting
without touching order is what tests that.  D4 back to 0 says the map is again emitting
only notations.  Everything the old corpus measured is unchanged — 0/0/0/234, `openCases`
0, `mixed` 0 — so nothing that passed before broke.

### §5.3 THE SKIP CONDITION, SETTLED — and a count-versus-set error of my own

CANDIDATE 10's skip test fires when ANY summand of `x`'s infinite part is a fixed point.
The mathematically clean refinement tests `isFP zero x` itself, since `ω^(ε₀·2) ≠ ε₀·2`
means a sum of fixed points is not one.  Measured, it improves D5 (51 → 35 pairs) and
BREAKS D6 (0 → 6), so neither form dominates.

**I FIRST REPORTED THAT IT "DOES NOT MOVE THE FOUR D1 FAILURES AT ALL", AND THAT WAS
WRONG — I COMPARED COUNTS, NOT SETS.**  Both forms fail on four terms and the two sets
are DISJOINT:

    candidate 10 fails on   φ̄(a, φ̄(0, ε₀·2))      a ∈ {1, 2, ω}, and one with +1
    candidate 11 fails on   φ̄(a, φ̄(0, ε₀+1))      the same three shapes

This is the exact error this file has been insisting on since candidate 4 — "the residue
is the predicted SET and not merely the predicted COUNT" — committed by the author of
that sentence, one section later, on a number he had just been handed.  It is recorded
rather than corrected silently because the sentence is worth less than the demonstration
that it is easy to violate.

AND SEEING THE SETS GAVE THE CONDITION IMMEDIATELY.  Three points separate the readings:

    x = ε₀      +1     both readings agree
    x = ε₀+1    +1     `isFP zero x` says no, and fails
    x = ε₀·2    NO     the ANY-summand test says yes, and fails

so the test is ONE fixed-point summand — neither "any" nor "`x` itself".  CANDIDATE 12.

### §5.4 THE PREDICTION MADE BEFORE THE MEASUREMENT, AND WHAT IT SETTLED

The 4 (D1) and the 14 (D5) were decoded before either was counted.  D1 ⊆ D5, and the
14 split as

    α  4 terms   φ̄(a, φ̄(0,ε₀·2))            the skip condition — also all of D1
    β 10 terms   φ̄(a, b) with a ∈ {2, ω}    encoding correct, EXPANSION leaves the image

STATED BEFORE FIXING: if α and β are two causes rather than one seen through two
dimensions, then candidate 12 sends D1 to 0, leaves D6 at 0, and drops D5 from 14 terms
to exactly the 10 of β.  MEASURED AFTER: D1 = 0, D6 = 0, D5 = 35 pairs over 10 terms,
and the 10 are β by name.  **Two causes, and β is now isolated with nothing else in it.**

                              baseline (cand 8)   cand 10    cand 12
    D1 round trip               16 / 269           4 / 269    0 / 269
    D2 table rows                0 / 5             0 / 5      0 / 5
    D3 discriminators            0 / 3             0 / 3      0 / 3
    D4 NON-STANDARD             12 / 267           0 / 267    0 / 267
    D5 image closure           130 / 1076         51 / 1076  35 / 1076   → 10 terms
    D6 order preservation     1923 / 72361         0 / 72361  0 / 72361

The old corpus is unchanged throughout: 0/0/0/234, `openCases` 0, `mixed` 0.

### §5.5 β — WHAT IS LEFT, NOT YET DIAGNOSED

Ten terms, every one of the shape `φ̄(a, b)` with `a ∈ {2, ω}`: a LADDER of two or more
levels.  Their own encodings are right — they pass D1, D4 and D6 — and their expansions
leave the image of `sqv`.

### §5.6 β, DIAGNOSED AND FIXED — one predicted half and one that was not

STATED BEFORE THE SEARCH, as a prediction: β would be the failure-class-(a) mechanism
(the LADDER TAIL repeating) appearing at the ladder position rather than the subscript
position, with `sqv` emitting a single marker column where a repeat belongs.

HALF RIGHT, and the other half was the more interesting one.

  β2 — CONFIRMED.  The collapse clause appends `[(d+1, 0 or 1)]`, ONE column, where it
  must append the LADDER.  For `a ≤ 1` the ladder IS one column (`predOr 1 = 0`, so its
  tail is empty), which is why 234 corpus terms and every earlier candidate agreed with
  the single-column form.  The fifth appearance of the night's pattern: a distinction
  that a region collapses.
      φ̄(2, φ̄(ω,0))   wants (0,0)(1,1)(2,1)(3,0)(1,1)(2,1)   — `(1,1)(2,1)` is the ladder
      candidate 12 gave (0,0)(1,1)(2,1)(3,0)(1,1)

  β1 — NOT PREDICTED, and it is §5.2's cause B one layer up.  `fpDeep` descends only
  through `φ̄(0,·)`, so a fixed point sitting under a `φ̄(1,·)` is invisible:
      φ̄(1, φ̄(1,ζ₀))  wants (0,0)(1,1)(2,1)(1,1)(2,0)(3,1)(4,1)(3,1)
      candidate 12 gave (0,0)(1,1)(2,0)(3,1)(4,1)(3,1)
  Dropping the `c == zero` restriction — descend through ANY `φ̄` layer — finds ζ₀ and
  the existing branch produces the rest unchanged.  I had fixed cause B for the layer
  the corpus could see and stated it as if it were the rule.

ABLATION, because "both changes together fix it" does not say both were needed:

    β1 alone        D5  35 → 20 pairs, 10 → 5 terms
    β1 and β2       D5  35 →  0 pairs, 10 → 0 terms

CANDIDATE 13 — ALL SIX GREEN on `corpusW`:

                              cand 8      cand 12     cand 13
    D1 round trip             16 / 269    0 / 269     0 / 269
    D2 table rows              0 / 5      0 / 5       0 / 5
    D3 discriminators          0 / 3      0 / 3       0 / 3
    D4 NON-STANDARD           12 / 267    0 / 267     0 / 267
    D5 image closure         130 / 1076  35 / 1076    0 / 1076
    D6 order preservation   1923 / 72361  0 / 72361   0 / 72361

Old corpus unchanged: 0/0/0/234, `openCases` 0, `mixed` 0.

AND WHAT GREEN MEANS, MEASURED RATHER THAN ASSUMED (§5.1a).  `corpusW`'s fixed-point
depth distribution is `[169, 10, 5, 5, 0]`: it reaches depths 0–3 and stops at 4.  The
`deeper` probe supplies depth 4 — 5 such terms, all `inT` — and all six dimensions are
green there too, `bms -s` included.  **That is the first time in this file that widening
the corpus did not find something**, which is a weak positive and is reported as one:
five terms is a check, not a sweep. -/

def nestedFP : Term → Bool
  | .zero => false
  | .add u v => nestedFP u || nestedFP v
  | .phi a b =>
      (match b with
       | .phi .zero c => (summands (TM.Term.splitFin c).1).any (fun g => TM.Term.isFP zero g)
       | _ => false)
      || nestedFP a || nestedFP b
  | _ => false

/-- Inner subscripts that COLLAPSE at `a = 0`: `isFP zero` holds of each. -/
def inners : List Term :=
  [phi one zero, plus (phi one zero) (phi one zero), plus (phi one zero) one,
   phi (ofNat 2) zero, phi one one]

/-- One `φ̄(0,·)` wrapped around each, so the subscript of the next layer is a `φ̄(0,·)`
    with a collapsing inner subscript — the class itself. -/
def mids : List Term := inners.map (fun x => phi zero x)

def nested : List Term :=
  (mids.flatMap (fun m => [phi zero m, phi one m, phi (ofNat 2) m, phi omega m]))
  ++ mids.map (fun m => phi zero (phi zero m))
  ++ mids.map (fun m => plus m m)
  ++ mids.map (fun m => phi one (plus m one))

def corpusW : List Term := corpus ++ nested

/-! ### §5.1a THE DEEPER CLASS — where `corpusW` itself stops

`nestedFP` is a yes/no test, and answering it with 25 of 35 says the widened corpus
reaches the class the OLD one could not.  It says nothing about where the NEW one stops,
and every green suite in this file so far has been green because of exactly that.  So
the same question is asked one level up, as a NUMBER rather than a predicate:
`fpReach t` is how many `φ̄` layers you descend, through subscripts, before meeting a
fixed point of `φ̄0` — `none` if there is none.  The distribution over `corpusW` is the
map of what the corpus can and cannot see, and the smallest `k` whose count is 0 is the
first class no dimension of this file can currently reach. -/

def fpReachF : Nat → Term → Option Nat
  | 0, _ => none
  | f + 1, t =>
      if TM.Term.isFP zero t then some 0
      else match t with
        | .phi _ x => ((summands (TM.Term.splitFin x).1).findSome? (fpReachF f)).map (· + 1)
        | .add u v =>
            match fpReachF f u, fpReachF f v with
            | some a, some b => some (min a b)
            | some a, none => some a
            | none, some b => some b
            | none, none => none
        | _ => none

def fpReach (t : Term) : Option Nat := fpReachF (t.deg + 4) t

-- the distribution: how many corpusW terms reach a fixed point at depth 0, 1, 2, 3, 4
#eval (List.range 5).map (fun k => (corpusW.filter (fun t => fpReach t == some k)).length)

/-! `corpusW` gives `[169, 10, 5, 5, 0]` — it reaches depths 0 through 3 and STOPS AT 4,
so "all six green" means "green on depths 0–3" and nothing more.  `deeper` is the probe
at depth 4, kept OUTSIDE `corpusW` so the baseline table stays comparable.  It is 15
terms of which 5 are at depth 4, all `inT`, and it is a SMALL probe — five terms is a
check, not a sweep. -/

def deeper : List Term :=
  (mids.map (fun m => phi zero (phi zero (phi zero m))))
  ++ (mids.map (fun m => phi one (phi zero (phi zero m))))
  ++ (mids.map (fun m => phi (ofNat 2) (phi zero (phi zero m))))

#eval ((List.range 7).map (fun k => (deeper.filter (fun t => fpReach t == some k)).length),
       (deeper.filter (fun t => !(TM.Term.inT t))).length,
       (deeper.filter (fun t => !(Trans.oR (sqv t) == some t))).length)

#guard (deeper.filter (fun t => fpReach t == some 4)).length == 5
#guard (deeper.filter (fun t => !(TM.Term.inT t))).length == 0
#guard (deeper.filter (fun t => !(Trans.oR (sqv t) == some t))).length == 0

#eval (corpus.length, (corpus.filter nestedFP).length,
       nested.length, (nested.filter nestedFP).length)

-- the blindness and the widening, as guards: the OLD corpus cannot reach the class,
-- the new terms do, and every new term is a legal 𝔗(M) term
#guard (corpus.filter nestedFP).length == 0
#guard (nested.filter nestedFP).length == 25
#guard (nested.filter (fun t => !(TM.Term.inT t))).length == 0

/-! ## §6 ONE NOTATION FACT, THREE DEFECTS

`φ̄(0,·)` ENUMERATES PAST ITS OWN FIXED POINTS: `φ̄(0,ε₀)` is `ω^(ε₀+1)`, not `ω^(ε₀)`,
because `ω^(ε₀) = ε₀` is already `φ̄(1,0)` and the enumeration skips it.  In one night
that single fact caused three separate defects, in three lanes:

  * it made Row A's registered term look wrong — `Evidence.WF.rowA = φ̄(0,ε₀)` read
    naively as `ω^(ε₀) = ε₀` says the row is degenerate; `Rows/TM.lean` names it
    `ω^(ε₀+1)` and the registry is correct (Cert.lean checkpoint, 2026-08-10);
  * it is the veblen2 lane's 13-of-234 `repAdd`-versus-(C) split;
  * it is §5.2's cause A — `omLog` returning `x` where the skip makes the exponent
    `x+1`, invisible below the first fixed point and wrong above it.

A fact with three defects to its name in one night will have a fourth.  The question to
ask of any clause that touches `φ̄(0,·)`: does it assume `φ̄(0,x) = ω^x`?  Below ε₀ that
is true, which is exactly why it survives every test written below ε₀. -/

/-! ## §7 D7 — SEQUENCE AGREEMENT, the dimension `sqv_decomp` actually consumes

D5 says the expansion of an encoded matrix is again an encoding.  It does NOT say it is
the encoding of the RIGHT term: `u` there is whatever `oR` returns, so a map could be
perfectly closed under expansion and send every expansion to the wrong member of the
right shape with D5 reading 0 throughout.  `Certified.lim`'s identity premise is
`∀ n, Certified (expand M n) (fs' n)` — the n-th member of the FUNDAMENTAL SEQUENCE, so
what has to hold is

    oR (expand (sqv t) n) = some (fs t n)        for the CALIBRATED `fs`

ITS SCOPE, AND WHY THE RESTRICTION IS THE RIGHT ONE.  The calibrated sequence is per row,
not a function of the term — that is §5's index-shift result — so D7 is measurable only
where a bundle exists.  That set is exactly what `sqv_decomp` will be applied to, but it
is a minority of the corpus and the file should say so rather than let "D7 green" read as
"green everywhere":

    D7 domain          26 DISTINCT terms
      13 named rows    φ̄(0,ε₀), φ̄(0,ζ₀), φ̄(1,0), φ̄(1,1), φ̄(1,2), φ̄(1,3), φ̄(1,ω),
                       φ̄(1,ω²), φ̄(1,ω^ω), φ̄(1,ε₀), φ̄(2,0), φ̄(1,ζ₀), φ̄(ω,0)
                       — TERMS, not ordinal names.  An earlier draft called the tenth
                       `ε_{ζ₀}`; the table names that row `ε_{ζ₀+1}`, and under the skip
                       convention the table is right, since ζ₀ is already a fixed point
                       of `φ̄(1,·)` so `φ̄(1,ζ₀)` is the NEXT ε-number after it.  §6's
                       fact has caused three defects tonight; an off-by-one ordinal name
                       in a header is the fourth waiting to happen, so the domain is
                       written as terms throughout.
      13 CN limits     paired with `Evidence.WF.fsC` (37 entries)
    no bundle         143 of the 169 distinct terms

**WHICH TABLE ROWS THE THEOREM THEREFORE REACHES — the sentence that matters more than
the denominator.**  Of the twelve table rows above ε₀:

    9 LIMIT rows      all in the D7 domain, all green
                      φ̄(0,ε₀) [Row A], φ̄(0,ζ₀), φ̄(1,1), φ̄(1,ω), φ̄(1,ω²), φ̄(1,ω^ω),
                      φ̄(1,ε₀), φ̄(2,0), φ̄(1,ζ₀)
    3 SUCCESSOR rows  ε₀+1, φ̄(1,ω)+1, ζ₀+1 — no fundamental sequence exists or is
                      needed; `Certified.succ` takes them

So the domain covers EVERY row above ε₀ that needs a sequence.  `φ̄(0,ε₀)` and `φ̄(0,ζ₀)`
were outside the first draft of this list and are in it because the question "which rows
does it reach" was asked — their bundles (`fsA`, `fsZ`, both `repAdd`) existed and were
simply not paired here.  A domain stated as a count would not have found them.

**THE DISTINCT COUNT IS THE ONE THAT MEANS ANYTHING, AND IT IS NOT THE ONE THIS FILE HAS
BEEN REPORTING** — see §8.

RESULT: **0 failures, all at SHIFT 0**, with the shift-1 control failing on all 48 — so
the check discriminates rather than being satisfied by any pairing.

AND THAT SETTLES SOMETHING §5 LEFT AMBIGUOUS.  §5 measured three different `fsN` shifts
and one row where no shift exists, and read it as "the index is matrix-determined".  D7
says where that non-uniformity lives: **between `fsN` and the matrices, NOT between the
CALIBRATED bundles and the matrices** — every bundle pairs at shift 0, including φ̄(ω,0)
which needed `fsN` shifted by 2 and ε₁ for which no `fsN` shift exists at all.  The
bundles are calibrated against the matrices, so this is confirmation that they are, not a
new fact; but it means `sqv_decomp` will not have to carry a per-row index. -/

open Evidence.WF (fsC tower fsEW fsEW2 fsEWW fsEE fsZeta0 fsEZ fsEsucc fsA fsZ)

def bundles : List (Term × (Nat → Term)) :=
  [(phi zero (phi one zero), fsA),                    -- Row A, ω^(ε₀+1)
   (phi zero (phi (ofNat 2) zero), fsZ),              -- φ̄(0,ζ₀)
   (phi one zero, tower),
   (phi one one, fsEsucc 0),
   (phi one (ofNat 2), fsEsucc 1),
   (phi one (ofNat 3), fsEsucc 2),
   (phi one omega, fsEW),
   (phi one (phi zero (ofNat 2)), fsEW2),
   (phi one (phi zero omega), fsEWW),
   (phi one (phi one zero), fsEE),
   (phi (ofNat 2) zero, fsZeta0),
   (phi one (phi (ofNat 2) zero), fsEZ),
   (phi omega zero, fun n => phi (ofNat (n + 2)) zero)]

def cnLims : List Term :=
  corpusW.filter (fun t => Evidence.WF.CN t && !(t == zero) && Evidence.WF.kindC t == false)

-- D7, and the shift-1 CONTROL beside it: a pairing check that only confirms agreement
-- cannot say a wrong pairing was excluded
#eval (bundles.length, cnLims.length,
       (bundles.filter (fun p => !((List.range 4).all (fun n =>
          Trans.oR (BMS.expand (sqv p.1) n) == some (p.2 n))))).length,
       (cnLims.filter (fun t => !((List.range 4).all (fun n =>
          Trans.oR (BMS.expand (sqv t) n) == some (fsC t n))))).length)

#guard (bundles.filter (fun p => !((List.range 4).all (fun n =>
          Trans.oR (BMS.expand (sqv p.1) n) == some (p.2 n))))).length == 0
#guard (cnLims.filter (fun t => !((List.range 4).all (fun n =>
          Trans.oR (BMS.expand (sqv t) n) == some (fsC t n))))).length == 0
#guard (bundles.filter (fun p => !((List.range 4).all (fun n =>
          Trans.oR (BMS.expand (sqv p.1) n) == some (p.2 (n + 1)))))).length == 13
#guard (cnLims.filter (fun t => !((List.range 4).all (fun n =>
          Trans.oR (BMS.expand (sqv t) n) == some (fsC t (n + 1)))))).length == 37

-- §5.2's four searched/predicted witnesses, as guards
#guard sqv (phi one (phi zero (phi one zero))) == [[0,0],[1,1],[2,0],[3,1],[2,0]]
#guard sqv (phi zero (phi zero (phi one zero))) == [[0,0],[1,1],[1,0],[2,1],[2,0]]
#guard sqv (phi zero (phi zero (phi zero (phi one zero))))
         == [[0,0],[1,1],[1,0],[2,1],[2,0],[3,1],[3,0]]
#guard sqv (phi zero (phi zero (plus (phi one zero) one)))
         == [[0,0],[1,1],[1,0],[2,1],[2,0],[2,0]]

-- the per-row shift, and the row where none exists
#guard (List.range 4).all (fun n => Trans.oR (BMS.expand (sqv (phi one omega)) n)
          == some (TM.Term.fsN (phi one omega) n))
#guard (List.range 4).all (fun n => Trans.oR (BMS.expand (sqv (phi omega zero)) n)
          == some (TM.Term.fsN (phi omega zero) (n + 2)))
#guard (List.range 4).all (fun s => !((List.range 4).all (fun n =>
          Trans.oR (BMS.expand (sqv (phi one one)) n) == some (TM.Term.fsN (phi one one) (n + s)))))
#guard (List.range 4).all (fun n => Trans.oR (BMS.expand (sqv (phi one one)) n)
          == some (Evidence.WF.fsEsucc 0 n))


/-! ## §8 THE DENOMINATORS ARE LIST LENGTHS, NOT SET SIZES  (correction, 2026-08-10)

Every count in this file — "0 of 234", "130 of 1076", "48 of 269" — is over a LIST, and
the lists contain duplicates.  `corpus` is built by two `flatMap`s over `bases` and the
same term arises many ways:

    corpus        234 entries    119 DISTINCT
    nested         35 entries     35 distinct
    deeper         15 entries     15 distinct
    corpusW       269 entries    154 DISTINCT
    corpusW+deeper 284 entries   169 DISTINCT
    cnLims         37 entries     13 DISTINCT
    D7 domain      48 entries     24 DISTINCT

NO VERDICT CHANGES: zero failures over a multiset is zero failures over its underlying
set, and a failure count is an upper bound on distinct failures.  **What changes is every
COVERAGE claim**, which is what this whole file has been about.  "All six green on 269
terms" is really 154 terms tested 269 times, and "D7 green on 48" is 24 terms tested 48
times.  A denominator that looks like coverage and is not is the same species as counting
instead of comparing sets (§5.3) — a number that reads as a result.

The distinct `fpReach` distribution, which is the one §5.1a should have printed:

    depth   0    1   2   3   4   5
            111  10  5   5   5   0

— so the depth-4 probe is 5 distinct terms out of 169, and depth 5 is where the corpus
now stops.  The shape of §5.1a's conclusion is unchanged and its numbers were inflated.

I am NOT deduplicating the lists.  The candidate table in §3 compares candidates 1–13 on
the same denominators, and changing them now would break every historical row for no gain
— the correction is to READ them as list lengths, which is what this section is for. -/

#eval ("entries vs distinct",
       (corpus.length, corpus.eraseDups.length),
       (corpusW.length, corpusW.eraseDups.length),
       ((corpusW ++ deeper).length, (corpusW ++ deeper).eraseDups.length))

#guard corpus.eraseDups.length == 119
#guard corpusW.eraseDups.length == 154
#guard (corpusW ++ deeper).eraseDups.length == 169
#guard ((bundles.map (fun p => p.1)) ++ cnLims).eraseDups.length == 26
#guard ((List.range 6).map (fun k =>
  ((corpusW ++ deeper).eraseDups.filter (fun t => fpReach t == some k)).length))
    == [111, 10, 5, 5, 5, 0]


/-! ## §9 `sqv_decomp` STARTED, AND THE TWO THINGS IT IS BLOCKED ON

THE FIRST ROW.  `φ̄(1,ω)` is the cleanest: `sqv (φ̄(1,ω)) = (0,0)(1,1)(2,0)`, its
expansions are `(0,0)(1,1)(1,1)^n` (Cert.lean §20's `expand_epsOmega`, proved), and
`fsEW n = φ̄(1, ofNat n)` by definition, so D7 at this row reduces to one ENCODER fact:

    sqv (φ̄(1, ofNat n))  =  (0,0)(1,1) ++ (1,1)^n

Its `n = 0` case is `rfl`.  Its induction step does not go through, and the reason is not
about this row.

BLOCKER 1 — `sqv` IS DEFINED WITH FUEL AND NOTHING PROVES THE FUEL IS ENOUGH.
`encv t d = encvF (2 * t.deg + 8) t d`, so the fuel VARIES WITH THE TERM: at
`φ̄(1, ofNat n)` for n = 0,1,2,3 it is 18, 22, 30, 38.  An induction on `n` therefore
compares `encvF 22` against `encvF 30`, and no lemma relates them.  What is needed is

    encvF f t d = encvF (f+1) t d          for f at or above the chosen fuel

which is a structural induction over `f` and `t` together, with the `mkBlocks` closure
and `fpDeep`'s own fuel inside it.  It is provable and it is real work.

NO DIMENSION MEASURED THIS, so D8 now does — and it is green, with the controls firing:

    D8 fuel saturation    0 of 284 fail          `encvF (chosen + k) t 0 = encv t 0`, k ≤ 5
    control fuel 1        234 of 284 DIFFER
    control fuel 3         52 of 284 DIFFER

So the fuel is enough IN FACT on everything measured, and that is exactly the gap between
a measurement and a proof that this file exists to keep visible.  Note what the shape of
the blocker is: it is not a defect in the encoding — seven dimensions say the encoding is
right — it is that the DEFINITION is not in a form an induction can use.

**QUALIFIED LATER, AND THE QUALIFICATION BELONGS HERE RATHER THAN ONLY AT §20/§21: THE BLOCKER IS
REAL BUT NOT TOTAL.**  §16 retired it by redefining `encv` fuel-free, so the paragraph above stands
as history.  But §20 and §21 then unfolded `fpDeepF` — a fuel recursion — at a SYMBOLIC index
anyway, twice, and neither needed a saturation lemma:

  * §20 `fpDeep_none_of_empty`: **the branch is decided at the FIRST step**, so the fuel is `f + 1`
    for an arbitrary `f` and never has to be known.
  * §21 `fpDeepF_tower`: **induct on the FUEL with the term's index universally quantified**, so
    the two indices are stepped down together and never compared.

**Fuel obstructs only when the recursion must be FOLLOWED to a depth the fuel has to cover.**  A
clause that terminates immediately unfolds once at any positive fuel; a recursion whose parameter
is universally quantified inducts on the fuel instead.  What made §9's blocker bite was neither of
those — it was an induction on `n` that had to compare `encvF 22` against `encvF 30` for the SAME
term, and that is the one shape these two techniques do not cover.

BLOCKER 2 — RESOLVED, AND THE ARROW POINTS **SqV → Cert**, NEVER THE REVERSE.
`import Evidence.Cert` is now at the head of this file and the bridge to
`Certified (sqv t) t` will be written HERE.  It is more natural to put a theorem about
`Certified` next to `Certified`, so the reason not to is recorded:

**`Cert.lean` is the PROOF PATH — `certIn_rows_inT` is the gate that mints every ✅.
`SqV.lean` is CANDIDATE TIER.**  If `Cert` imported `SqV`, a candidate-tier measurement
file would sit inside the registry's dependency cone: these `#eval`s would run on every
`Cert` build, a change to a corpus could break the gate's build, and — the part that
matters — an `SqV` lemma would become CITABLE INSIDE A CERTIFICATE.  Pointing the arrow
this way makes that structurally impossible rather than a matter of remembering.  It is
the same reason `Trans.oR` may not appear in a certificate's justification, enforced by
the module graph instead of by a rule.

NEITHER IS A HYPOTHESIS I COULD ADD TO MAKE THE STATEMENT CLOSE, and I have not added
one.  A domain restriction that hides blocker 1 would be invisible at the use site, which
is the objection to narrowing rather than naming. -/

def sat (t : Term) (k : Nat) : Bool := encvF (2 * t.deg + 8 + k) t 0 == encv t 0

#eval (((corpusW ++ deeper).filter (fun t => !((List.range 6).all (sat t)))).length,
       ((corpusW ++ deeper).filter (fun t => !(encvF 1 t 0 == encv t 0))).length,
       ((corpusW ++ deeper).filter (fun t => !(encvF 3 t 0 == encv t 0))).length)

#guard ((corpusW ++ deeper).filter (fun t => !((List.range 6).all (sat t)))).length == 0
#guard ((corpusW ++ deeper).filter (fun t => !(encvF 1 t 0 == encv t 0))).length == 234
#guard ((corpusW ++ deeper).filter (fun t => !(encvF 3 t 0 == encv t 0))).length == 52

-- the ε_ω row's encoder fact at n = 0, 1, 2 — the `∀ n` form is what blocker 1 blocks
#guard sqv (phi one (ofNat 0)) == [[0,0],[1,1]]
#guard sqv (phi one (ofNat 1)) == [[0,0],[1,1],[1,1]]
#guard sqv (phi one (ofNat 2)) == [[0,0],[1,1],[1,1],[1,1]]


/-! ### §9.1 THE MEASURE FOR SATURATION — `deg` is the wrong one, and `tdepth` is right

The `ltF_stable` / `starF_stable` pair (WF §5) is the template: strong induction on a
BOUND, both fuels stepped down together, each recursive call justified by showing its
arguments stay under the bound.  Its measure is `deg`.  **`deg` DOES NOT WORK HERE**, and
the reason is measured rather than suspected:

    omLog raises `deg`      on 4 of 169 distinct terms      7→9, 11→13, 9→11
    predOr raises `deg`     on 0
    summands raise `deg`    on 0

`omLog (φ̄(0,x)) = x+1` in the skip case, and `deg (add x one)` exceeds `deg (φ̄(0,x))` by
a constant — so the one clause §6's notation fact forced into the encoder is also the one
that breaks the obvious measure.

WHAT THE FUEL IS ACTUALLY FOR.  Measured over all 169 distinct terms: the minimal
saturating fuel is at most **6**, while `encv` chooses `2 * deg + 8`, which ranges from 10
to 62 — a factor of ten of slack, which is why D8 is green everywhere.  The recursion is
shallow; `deg` is simply not what it is deep in.

THE MEASURE IS CONSTRUCTOR NESTING DEPTH, and it is exact:

    minFuel t ≤ tdepth t                      0 failures of 169   (equal on the samples)
    omLog does not raise `tdepth`             0 failures
    predOr does not raise `tdepth`            0 failures
    summands do not raise `tdepth`            0 failures

All three of `encvF`'s non-structural recursion targets are non-increasing in `tdepth`,
which is exactly what the `stable_aux` induction needs at each of its three sites.  So the
saturation proof is: induct on a bound `n ≥ tdepth t`, step both fuels, and discharge the
three sites with the three lemmas above — plus `tdepth t ≤ 2 * t.deg + 8`, so that the
fuel `encv` chooses is above the bound.

WHAT THE TEMPLATE DID NOT HAVE, named before working around it.  `ltF_stable`'s recursion
sites are all sub-terms; `encvF`'s `phi` clause has two that are not:

  * the head of `summands (splitFin b).1` — a computed term, needing `tdepth_headD`;
  * **`fpDeep`'s OUTPUT.**  `fpDeep` carries its OWN fuel, so it is fuel-independent of
    `encvF` and contributes no step-down obligation — but the term it RETURNS is fed to
    `encvF`, so its depth has to be bounded: `fpDeep a t = some g → tdepth g ≤ tdepth t`.
    Nothing in `ltF_stable` corresponds to this, because nothing there returns a term.

Both are measured 0-failure below.

STATE OF THE PROOF (not in this file, because it is not finished and `sorry` does not go
in): the induction skeleton is proved — `zero`, `M`, `omg`, `psi`, `Z` are `rfl` and `add`
closes from the IH.  The `phi` case unfolds cleanly under `simp only [encvF]`, exposing
exactly four fuel-dependent sites; three of them (`predOr a`, the `headD`, `fpDeep`'s `g`)
rewrite from the IH, and the fourth sits under a `List.map` binder where the congruence
step is still open plumbing.

AND 169 DISTINCT TERMS IS A REAL CORPUS BUT IT IS STILL A CORPUS, so the lemma most
likely to fail was attacked directly.  `tdepth_omLog` is the one at risk: `omLog` is the
clause §6's notation fact forced in, `omLog (φ̄(0,x)) = x+1` goes through `plus`, and
`plus` goes through `ofList`, whose depth GROWS WITH LIST LENGTH while `φ̄(0,·)` adds only
one.  `stress` below is 57 terms built to exploit exactly that — long additive spines of
`1`s under a `φ̄(0,·)`, at every length up to 8, with and without a nested layer.

    all six non-increase facts on `stress`      0 failures
    minFuel ≤ tdepth on `stress`                0 failures
    WORST `omLog` MARGIN                        0

**The margin is zero**: at the tightest point `tdepth (omLog t) = tdepth t` exactly.  So
`≤` is the right statement, there is no slack to give away, and a measure even slightly
coarser than `tdepth` would fail here.  That is worth knowing before the induction rather
than at the site.

AND A NOTE ON D8, which this measurement makes honest.  Minimal saturating fuel is ≤ 6
against a chosen fuel of 10–62 — tenfold slack — so "more fuel does not change the
answer" was nearly certain to pass, and **D8's information was carried by its CONTROLS
(fuel 1 differing on 234, fuel 3 on 52), not by the measurement.**  When a test's margin
is an order of magnitude, the control IS the measurement.  Contrast `tdepth_omLog` above,
whose margin is 0 and whose measurement therefore carries its own information.

### §9.2 `tdepth_omLog` IS FALSE — the measure is refuted, by a term the corpus cannot hold

Proved FIRST because it is the only one of the five that can refute the measure: its
margin is 0, so there is no slack anywhere.  It does not hold.

    φ̄(0, M)        tdepth = 1        `tdepth M = 0`, and `φ̄(0,·)` adds one
    omLog of it    M ⊕ 1             tdepth = 2
                                     2 > 1 — VIOLATION

The mechanism is the one §9.1 predicted and the corpus could not exhibit: `omLog` goes
through `plus`, `plus` through `ofList`, and `ofList` adds a level per list element.  `M`
is the one head with `tdepth 0` OTHER than `zero`, and `zero` never appears in a `toList`,
so `M` is the only witness — which is why 226 corpus, nested, deeper and stress terms all
passed.  **The corpus contains no `M`: the region this file measures stops below it.**
`inT (φ̄(0,M)) = false`, so the witness is not a legal 𝔗(M) term either.

A CANDIDATE FIX, MEASURED AND NOT APPLIED: give `M` depth 1 rather than 0.  Over 223
distinct terms (corpus + nested + deeper + stress + the probes, the counterexample
included) all six non-increase facts and `minFuel ≤ tdepth` hold with 0 violations, while
the current `tdepth` has exactly 1 on the same set — and the worst `omLog` margin is still
0, so the fix adds no slack and is minimal rather than coarsening.

WHY NOT THE OTHER FIX.  `inT` as a hypothesis would also exclude the witness, and it is
the wrong move: it narrows the induction, and every recursion site inside `encvF` would
then owe an `inT`-closure proof — `omLog g`, `predOr a`, each summand — which is a new
obligation nowhere in evidence, invisible at the use site.  Changing a constant in a
measure this file introduced is smaller than changing what the theorem is about.

NEITHER IS APPLIED HERE.  The measure is the object the whole §9 plan rests on and the
coordinator asked to hear before it changes.

THIS IS A PLAN, NOT A PROOF.  The seven facts are `#eval`-measured on 169 + 57 terms and
none of them is proved; `tdepth_omLog` is now known FALSE as stated.  They are stated here so that the proof is written against measured
lemmas rather than guessed ones — the same order this file has used for the encoding. -/

/-- Constructor nesting depth.  **`M` HAS DEPTH 1, NOT 0** — see §9.2: `M` is the only
    thing that can appear in a `toList` with depth 0, because `zero` never does, and
    `ofList` adds a level per element.  "Appears in a list" must imply "depth ≥ 1" for
    the measure to be sound under `ofList` at all.  `M` at 0 was an accident of treating
    it like `zero`: both are leaf constructors, but only one is ever a list element.

    AND WHAT IT MUST NOT DEPEND ON: **a termination lemma should not know what a legal
    term is.**  `inT` would also have excluded §9.2's counterexample, and it is the wrong
    kind of fix — it couples the fuel lemma to a property of 𝔗(M) that has nothing to do
    with fuel, and every consumer inherits the coupling.  `tdepth` is internal to this
    proof, with no consumer and no external calibration; changing it changes an
    instrument, where changing a hypothesis changes what is claimed. -/
def tdepth : Term → Nat
  | .zero => 0 | .M => 1
  | .omg a => 1 + tdepth a
  | .Z a => 1 + tdepth a
  | .psi a b => 1 + max (tdepth a) (tdepth b)
  | .phi a b => 1 + max (tdepth a) (tdepth b)
  | .add a b => 1 + max (tdepth a) (tdepth b)

def minFuel (t : Term) : Option Nat := (List.range 60).find? (fun f => encvF f t 0 == encv t 0)

def distinctTerms : List Term := (corpusW ++ deeper).eraseDups

#eval ("max minimal fuel, chosen fuel min/max",
       distinctTerms.foldl (fun m t => max m ((minFuel t).getD 99)) 0,
       distinctTerms.foldl (fun m t => min m (2 * t.deg + 8)) 999,
       distinctTerms.foldl (fun m t => max m (2 * t.deg + 8)) 0)

#guard (distinctTerms.filter (fun t => !((minFuel t).getD 99 <= tdepth t))).length == 0
#guard (distinctTerms.filter (fun t => !(tdepth (omLog t) <= tdepth t))).length == 0
#guard (distinctTerms.filter (fun t => !(tdepth (predOr t) <= tdepth t))).length == 0
#guard (distinctTerms.filter (fun t =>
          !((summands (TM.Term.splitFin t).1).all (fun g => tdepth g <= tdepth t)))).length == 0
#guard (distinctTerms.filter (fun t => !(tdepth t <= 2 * t.deg + 8))).length == 0
-- the two sites `ltF_stable` did not have: `headD` of the summands, and `fpDeep`'s OUTPUT
#guard (distinctTerms.filter (fun t =>
          !(tdepth ((summands (TM.Term.splitFin t).1).headD zero) <= tdepth t))).length == 0
#guard (distinctTerms.filter (fun t =>
          !((List.range 3).all (fun i =>
              match fpDeep (ofNat i) t with
              | none => true
              | some g => tdepth g <= tdepth t)))).length == 0
-- and the NEGATIVE control: `deg` really does fail, so §9.1 is not a statement about nothing
#guard (distinctTerms.filter (fun t => !((omLog t).deg <= t.deg))).length == 4


def stress : List Term :=
  ((List.range 9).flatMap (fun k =>
    [phi zero (plus (phi one zero) (ofNat k)),
     phi zero (plus (phi (ofNat 2) zero) (ofNat k)),
     phi zero (plus (plus (phi one zero) (phi one zero)) (ofNat k)),
     phi one (plus (phi one zero) (ofNat k)),
     phi zero (phi zero (plus (phi one zero) (ofNat k)))]))
  ++ ((List.range 6).map (fun k => phi zero (Evidence.WF.repAdd (phi one zero) k)))
  ++ ((List.range 6).map (fun k => phi zero (phi zero (Evidence.WF.repAdd (phi one zero) k))))

#eval (stress.length, stress.foldl (fun m t => min m (tdepth t - tdepth (omLog t))) 99)

#guard (stress.filter (fun t => !(tdepth (omLog t) <= tdepth t))).length == 0
#guard (stress.filter (fun t => !(tdepth (predOr t) <= tdepth t))).length == 0
#guard (stress.filter (fun t =>
          !((summands (TM.Term.splitFin t).1).all (fun g => tdepth g <= tdepth t)))).length == 0
#guard (stress.filter (fun t =>
          !(tdepth ((summands (TM.Term.splitFin t).1).headD zero) <= tdepth t))).length == 0
#guard (stress.filter (fun t => !((List.range 3).all (fun i =>
          match fpDeep (ofNat i) t with | none => true | some g => tdepth g <= tdepth t)))).length == 0
#guard (stress.filter (fun t =>
          !(((List.range 60).find? (fun f => encvF f t 0 == encv t 0)).getD 99 <= tdepth t))).length == 0
-- the margin is TIGHT: zero at the worst term, so `tdepth` is not merely sufficient
#guard stress.foldl (fun m t => min m (tdepth t - tdepth (omLog t))) 99 == 0


/-! ## §10 THE THREE DEFINING EQUATIONS OF `encvF`'s `phi` CLAUSE, AS REWRITE RULES

Written the way `Evidence/WF.lean` §11.0 writes `fsC`'s: **do not unfold — state one
named equation per branch, discharge the branch condition once, and let every consumer
rewrite with a left-hand side that is stable.**

The reason is the same one §11.0 gives, met here from the other side.  `simp only [encvF]`
unfolds the `phi` clause everywhere it occurs and then normalises the result; the `if`s
get pushed around and the `let`-bodies inlined, and a congruence lemma that is CORRECT no
longer matches syntactically.  Two rounds of `rw` ordering did not fix that and were not
going to: the problem is that the consumer sees the `if`-chain at all.  With these three,
no consumer ever does — and `sqv_decomp` can cite the branch it is in rather than
re-unfolding.

A GOTCHA WORTH THE LINE IT COSTS, found the expensive way while proving the map
congruence these equations replace: when a rewrite occurs BOTH at the head and under the
binder of a `List.map` in the tail, **apply the induction hypothesis FIRST**.  Rewriting
the head first also rewrites inside the tail map, and the induction hypothesis' left-hand
side is then gone.  `List.map_cons, List.map_cons, ih, …` — never `…, ih`. -/

def ladderOf (a : Term) (f d : Nat) : List Col2 :=
  if a == zero then [] else (d + 1, 1) :: bumpAt (d + 2) (encvF f (predOr a) (d + 2))

def unitOf (a : Term) (f d : Nat) : List Col2 :=
  if a == zero then [((d + 1, 0) : Col2)] else ladderOf a f d

def repsOf (a b : Term) (f d : Nat) : List Col2 :=
  (List.replicate (TM.Term.splitFin b).2 (unitOf a f d)).flatten

def blocksOf (a : Term) (f d : Nat) (hs : List Term) : List Col2 :=
  (hs.map (fun g => ladderOf a f d ++ shiftD (if a == zero then d + 1 else d + 2)
    (encvF f (if a == zero then g else omLog g) 0))).flatten

/-- The COLLAPSE branch: the head summand is a fixed point of `φ̄a`. -/
theorem encvF_phi_collapse (a b : Term) (f d : Nat)
    (h : TM.Term.isFP a ((summands (TM.Term.splitFin b).1).headD zero) = true) :
    encvF (f + 1) (TM.Term.phi a b) d
      = encvF f ((summands (TM.Term.splitFin b).1).headD zero) d
        ++ (if ((summands (TM.Term.splitFin b).1).length == 1) = true then unitOf a f d
            else blocksOf a f d ((summands (TM.Term.splitFin b).1).drop 1))
        ++ repsOf a b f d := by
  show (if TM.Term.isFP a ((summands (TM.Term.splitFin b).1).headD zero) = true then _ else _) = _
  rw [if_pos h]
  rfl

/-- The DEEP branch: not a fixed point at the top, but one sits below through `φ̄` layers. -/
theorem encvF_phi_deep (a b : Term) (f d : Nat) (z : Term)
    (h : TM.Term.isFP a ((summands (TM.Term.splitFin b).1).headD zero) = false)
    (hz : fpDeep a ((summands (TM.Term.splitFin b).1).headD zero) = some z) :
    encvF (f + 1) (TM.Term.phi a b) d
      = encvF f z d ++ blocksOf a f d (summands (TM.Term.splitFin b).1) ++ repsOf a b f d := by
  show (if TM.Term.isFP a ((summands (TM.Term.splitFin b).1).headD zero) = true then _ else _) = _
  rw [if_neg (by rw [h]; exact Bool.noConfusion), hz]
  rfl

/-- The BASE branch: no fixed point anywhere below the subscript. -/
theorem encvF_phi_base (a b : Term) (f d : Nat)
    (h : TM.Term.isFP a ((summands (TM.Term.splitFin b).1).headD zero) = false)
    (hz : fpDeep a ((summands (TM.Term.splitFin b).1).headD zero) = none) :
    encvF (f + 1) (TM.Term.phi a b) d
      = (d, 0) :: ((match summands (TM.Term.splitFin b).1 with
                    | [] => ladderOf a f d
                    | _ => blocksOf a f d (summands (TM.Term.splitFin b).1))
                   ++ repsOf a b f d) := by
  show (if TM.Term.isFP a ((summands (TM.Term.splitFin b).1).headD zero) = true then _ else _) = _
  rw [if_neg (by rw [h]; exact Bool.noConfusion), hz]
  rfl


/-! ### §10.1 The helpers' congruences, and what is left of `encvF_saturate`

Naming the branches forced four helpers into existence, and the fuel-independence of
each is now a one-line lemma instead of a rewrite buried in a page of `let`s.  That is
the return on naming a branch: the statement you can write is the statement you can
reason about.

WITH THESE, `encvF_saturate` ASSEMBLES COMPLETELY — the `stable_aux` induction on a
bound, every constructor, and the `phi` case's four fuel sites, all closed.  It is NOT in
this file, because it still depends on the five `tdepth` lemmas of §9.1 and those are
`sorry` stubs; a half-proof behind `sorry` builds green and reads as done.  What remains
between here and a proved `encvF_saturate` is exactly those five and nothing else:

    tdepth_predOr    tdepth (predOr a) ≤ tdepth a
    tdepth_omLog     tdepth (omLog g) ≤ tdepth g              margin 0 — the tight one
    tdepth_summands  g ∈ summands (splitFin b).1 → tdepth g ≤ tdepth b
    tdepth_headD     the same for the list's head
    tdepth_fpDeep    fpDeep a t = some g → tdepth g ≤ tdepth t

A `rfl` IS NEEDED AFTER EACH `rw` in §10's equations, and the reason reads as a failure
the second time someone meets it: the branch condition discharges the `if`, but the two
sides are then only DEFINITIONALLY equal, because the right-hand sides NAME the helpers
where the unfolded left-hand side has their bodies inline. -/

theorem ladderOf_congr (a : Term) (f g d : Nat)
    (h : encvF f (predOr a) (d + 2) = encvF g (predOr a) (d + 2)) :
    ladderOf a f d = ladderOf a g d := by simp only [ladderOf, h]

theorem unitOf_congr (a : Term) (f g d : Nat)
    (h : encvF f (predOr a) (d + 2) = encvF g (predOr a) (d + 2)) :
    unitOf a f d = unitOf a g d := by simp only [unitOf, ladderOf_congr a f g d h]

theorem repsOf_congr (a b : Term) (f g d : Nat)
    (h : encvF f (predOr a) (d + 2) = encvF g (predOr a) (d + 2)) :
    repsOf a b f d = repsOf a b g d := by simp only [repsOf, unitOf_congr a f g d h]

/-- The map congruence the assembly needs.  `ih` FIRST — see §10's header. -/
theorem blocksOf_congr (a : Term) (f g d : Nat)
    (h : encvF f (predOr a) (d + 2) = encvF g (predOr a) (d + 2)) :
    ∀ (hs : List Term),
      (∀ x ∈ hs, encvF f (if a == zero then x else omLog x) 0
               = encvF g (if a == zero then x else omLog x) 0) →
      blocksOf a f d hs = blocksOf a g d hs := by
  intro hs hx
  simp only [blocksOf]
  refine congrArg List.flatten ?_
  induction hs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.map_cons, ih (fun y hy => hx y (List.mem_cons_of_mem x hy)),
      ladderOf_congr a f g d h, hx x (List.mem_cons_self)]


-- §9.2's counterexample, banked as a LIVE NEGATIVE CONTROL rather than as prose:
-- `tdepthOld` is the refuted measure and exists only to keep the refutation checkable.
def tdepthOld : Term → Nat
  | .zero => 0 | .M => 0
  | .omg a => 1 + tdepthOld a
  | .Z a => 1 + tdepthOld a
  | .psi a b => 1 + max (tdepthOld a) (tdepthOld b)
  | .phi a b => 1 + max (tdepthOld a) (tdepthOld b)
  | .add a b => 1 + max (tdepthOld a) (tdepthOld b)

#guard !(tdepthOld (omLog (phi zero TM.Term.M)) <= tdepthOld (phi zero TM.Term.M))
#guard (tdepthOld (phi zero TM.Term.M), tdepthOld (omLog (phi zero TM.Term.M))) == (1, 2)
#guard tdepth (omLog (phi zero TM.Term.M)) <= tdepth (phi zero TM.Term.M)
#guard TM.Term.inT (phi zero TM.Term.M) == false
-- under the refuted measure `M` was the only head but `zero` with depth 0; under the
-- current one no head has depth 0 but `zero`, which is what makes it sound under `ofList`
#guard (tdepthOld TM.Term.M, tdepth TM.Term.M, tdepth (TM.Term.Z zero)) == (0, 1, 1)


/-! ### §9.3 The `M`-corpus — the blind region, now measured

§9.2's witness existed because no corpus in this file contained `M`.  That is now a KNOWN
blind region rather than an unknown one, so it is filled: 22 terms with `M` at every
position the encoder can reach — argument, subscript, summand, under `Z`/`psi`/`omg`, and
nested — of which only 6 are `inT`.  Illegal terms belong here: `encvF` is called on
intermediates that need not be legal, which is the whole reason §9.2's fix must not be an
`inT` hypothesis.

    all six non-increase facts        0 violations of 234 distinct terms
    minFuel ≤ tdepth                  0
    tdepth t ≤ 2 * t.deg + 8          0, worst slack 9 — IT SURVIVES BY ONE
    worst `omLog` margin              0

The BOUND is the one that gets harder when a measure goes up, so it was re-checked rather
than assumed: it survives with slack 9 against a constant of 8. -/

def mCorpus : List Term :=
  [TM.Term.M, phi zero TM.Term.M, phi one TM.Term.M, phi TM.Term.M zero,
   phi TM.Term.M TM.Term.M, plus TM.Term.M one, plus TM.Term.M (phi one zero),
   phi zero (plus TM.Term.M one), phi zero (plus TM.Term.M (phi one zero)),
   phi zero (phi zero TM.Term.M), phi zero (phi TM.Term.M zero),
   phi one (plus TM.Term.M one), phi (ofNat 2) TM.Term.M,
   plus (phi one zero) TM.Term.M, phi zero (plus (phi one zero) TM.Term.M),
   TM.Term.Z TM.Term.M, phi zero (TM.Term.Z TM.Term.M), TM.Term.psi TM.Term.M zero,
   phi zero (TM.Term.psi TM.Term.M zero), phi zero (TM.Term.omg TM.Term.M),
   phi zero (plus (phi TM.Term.M zero) one), phi zero (phi zero (phi zero TM.Term.M))]

def allM : List Term := (corpusW ++ deeper ++ stress ++ mCorpus).eraseDups

#eval (allM.length, (mCorpus.filter (fun t => TM.Term.inT t)).length,
       allM.foldl (fun m t => min m (2 * t.deg + 8 - tdepth t)) 999,
       allM.foldl (fun m t => min m (tdepth t - tdepth (omLog t))) 99)

#guard (allM.filter (fun t => !(tdepth (omLog t) <= tdepth t))).length == 0
#guard (allM.filter (fun t => !(tdepth (predOr t) <= tdepth t))).length == 0
#guard (allM.filter (fun t =>
          !((summands (TM.Term.splitFin t).1).all (fun g => tdepth g <= tdepth t)))).length == 0
#guard (allM.filter (fun t =>
          !(tdepth ((summands (TM.Term.splitFin t).1).headD zero) <= tdepth t))).length == 0
#guard (allM.filter (fun t => !((List.range 3).all (fun i =>
          match fpDeep (ofNat i) t with | none => true | some g => tdepth g <= tdepth t)))).length == 0
#guard (allM.filter (fun t =>
          !(((List.range 60).find? (fun f => encvF f t 0 == encv t 0)).getD 99 <= tdepth t))).length == 0
#guard (allM.filter (fun t => !(tdepth t <= 2 * t.deg + 8))).length == 0


/-! ## §11 TWO OF THE FIVE `tdepth` LEMMAS, PROVED

`tdepth_summands` and `tdepth_headD` — and `headD` falls out of `summands`, so it is two
statements for one proof, as expected.  The route avoids the `ofList (toList b) = b`
roundtrip entirely: `TM.Lemmas` has only the other direction and a `CNV`-restricted
version, and neither is needed if the bound is proved about `ofList ((toList b).take k)`
directly, by induction on `b`.  Naming what was NOT needed is worth as much here as
naming what was: the roundtrip would have been a lemma about normal forms inside a
lemma about termination, which is the coupling §9.2 rejected in a different place.

STILL OPEN: `tdepth_predOr`, `tdepth_omLog`, `tdepth_fpDeep`.  `tdepth_omLog` is the one
with margin 0 and it is the one already refuted once (§9.2); it is now a statement about
the CORRECTED measure and is unproved, not known true. -/

open TM.Term (toList ofList)
theorem tdepth_mem_summands : ∀ (t g : Term), g ∈ summands t → tdepth g ≤ tdepth t := by
  intro t
  induction t with
  | zero => intro g hg; simp only [summands] at hg; exact absurd hg (List.not_mem_nil)
  | M => intro g hg; simp only [summands, List.mem_singleton] at hg; rw [hg]; exact Nat.le_refl _
  | omg _ _ => intro g hg; simp only [summands, List.mem_singleton] at hg; rw [hg]; exact Nat.le_refl _
  | psi _ _ _ _ => intro g hg; simp only [summands, List.mem_singleton] at hg; rw [hg]; exact Nat.le_refl _
  | Z _ _ => intro g hg; simp only [summands, List.mem_singleton] at hg; rw [hg]; exact Nat.le_refl _
  | phi _ _ _ _ => intro g hg; simp only [summands, List.mem_singleton] at hg; rw [hg]; exact Nat.le_refl _
  | add u v ihu ihv =>
    intro g hg
    simp only [summands, List.mem_append] at hg
    simp only [tdepth]
    rcases hg with h | h
    · exact Nat.le_trans (ihu g h) (by omega)
    · exact Nat.le_trans (ihv g h) (by omega)

theorem tdepth_ofList_take : ∀ (b : Term) (k : Nat),
    tdepth (ofList ((toList b).take k)) ≤ tdepth b := by
  intro b
  induction b with
  | zero => intro k; simp only [toList, List.take_nil, ofList]; exact Nat.le_refl _
  | M => intro k; cases k <;> simp only [toList, List.take, List.take_nil, ofList, tdepth] <;> omega
  | omg _ _ => intro k; cases k <;> simp only [toList, List.take, List.take_nil, ofList, tdepth] <;> omega
  | psi _ _ _ _ => intro k; cases k <;> simp only [toList, List.take, List.take_nil, ofList, tdepth] <;> omega
  | Z _ _ => intro k; cases k <;> simp only [toList, List.take, List.take_nil, ofList, tdepth] <;> omega
  | phi _ _ _ _ => intro k; cases k <;> simp only [toList, List.take, List.take_nil, ofList, tdepth] <;> omega
  | add u v _ ihv =>
    intro k
    cases k with
    | zero => simp only [toList, List.take_zero, ofList, tdepth]; omega
    | succ j =>
      have hv := ihv j
      simp only [toList, List.take_succ_cons]
      cases h : (toList v).take j with
      | nil => simp only [ofList, tdepth]; omega
      | cons y ys =>
        show tdepth (TM.Term.add u (ofList (y :: ys))) ≤ tdepth (TM.Term.add u v)
        rw [h] at hv
        simp only [tdepth] at hv ⊢
        omega

theorem tdepth_splitFin_fst (b : Term) : tdepth ((TM.Term.splitFin b).1) ≤ tdepth b :=
  tdepth_ofList_take b _

theorem tdepth_summands (b : Term) :
    ∀ g ∈ summands (TM.Term.splitFin b).1, tdepth g ≤ tdepth b :=
  fun g hg => Nat.le_trans (tdepth_mem_summands _ g hg) (tdepth_splitFin_fst b)

theorem tdepth_headD (b : Term) :
    tdepth ((summands (TM.Term.splitFin b).1).headD zero) ≤ tdepth b := by
  cases h : summands (TM.Term.splitFin b).1 with
  | nil => exact Nat.zero_le _
  | cons y ys =>
    show tdepth y ≤ tdepth b
    exact tdepth_summands b y (by rw [h]; exact List.mem_cons_self)



/-! ### §11.1 `tdepth_predOr` — what it reduces to, and the lemma that does not exist

`predOr t` is `t` when `splitFin`'s finite part is 0, and `plus (splitFin t).1 (ofNat m)`
when it is `m+1`.  MEASURED, on the 40 terms of `allM` whose finite part is nonzero and
on a family with finite tails up to length 11:

    predOr t = ofList ((toList t).take ((toList t).length - 1))     0 violations
    predOr t = t                          when the finite part is 0, 0 violations

**With that identity, `tdepth_predOr` is `tdepth_ofList_take` and nothing else** — the
machinery of §11 is the right machinery, which is what proving this lemma second was
meant to find out.

WHAT IS MISSING IS THE IDENTITY, NOT THE BOUND.  Proving it needs two facts about `plus`
that the repo does not have: `toList (ofNat m) = List.replicate m one`, and that `plus`'s
`filter (le b1)` is the identity when every component of the left argument is `≥ 1` —
which is true because components are additively principal, but is a statement about
NORMAL FORMS.  So the direct route (W5) is not available here the way it was for
`tdepth_ofList_take`: there, inducting on the term avoided the roundtrip; here the
statement itself is about what `plus` computes.

NAMED RATHER THAN WORKED AROUND.  The cheap workaround would be to restate
`tdepth_predOr` with a hypothesis that `splitFin`'s finite part is 0 — true on most of
the corpus, and it would make the lemma close today.  It is the same invisible narrowing
as the `inT` fix: `encvF`'s ladder calls `predOr` precisely when there IS a finite part,
so the hypothesis would exclude the case the lemma exists for. -/

def dropLast1 (t : Term) : Term := ofList ((toList t).take ((toList t).length - 1))

#guard (allM.filter (fun t => (TM.Term.splitFin t).2 >= 1 && !(predOr t == dropLast1 t))).length == 0
#guard (allM.filter (fun t => (TM.Term.splitFin t).2 == 0 && !(predOr t == t))).length == 0
#guard (allM.filter (fun t => (TM.Term.splitFin t).2 >= 1)).length == 40
#guard (((List.range 12).map (fun k => plus (phi one zero) (ofNat k))).filter
          (fun t => if (TM.Term.splitFin t).2 >= 1 then !(predOr t == dropLast1 t)
                    else !(predOr t == t))).length == 0


/-! ### §11.2 `tdepth_omLog` REDUCED — and fix (a) is what makes its leaf case TRUE

`omLog` is the identity off `φ̄(0,·)`, and on it returns either `x` (bound immediate) or
`plus x one`.  So the whole lemma is

    tdepth (plus x one) ≤ 1 + tdepth x

and that goes by induction on `x`, with `plus x one = ofList ((toList x).filter (le 1) ++ [1])`:

  add u v   the head is kept or dropped; either way the IH on `v` gives it, since
            `1 + max (tdepth u) (1 + tdepth v)` ≤ `1 + tdepth (add u v)`
  LEAF      `ofList [x, 1]` is `add x 1`, of depth `1 + max (tdepth x) 1`.
            The bound needs **`max (tdepth x) 1 ≤ tdepth x`, i.e. `tdepth x ≥ 1`**

**THAT IS §9.2's FIX, AND THIS IS WHERE IT EARNS ITS NAME.** `tdepth_pos` below — every
term but `zero` has depth at least 1 — is exactly the leaf case's requirement, and under
the REFUTED measure it is FALSE at `M`, which is guarded.  So `tdepth M = 1` is not a
patch that removed one witness: it is the hypothesis the induction needs at every leaf,
and `φ̄(0,M)` was the one term the corpus could have shown it with.

WHAT REMAINS is the `plus`/`filter` reduction — the same family as §11.1's L1/L2, and
already routed.  The MATHEMATICS of `tdepth_omLog` is settled; the Lean is not.

A CORRECTION TO W5's TELL, from the coordinator and worth carrying: the tell is NOT "a
normal-form notion appears", it is "the hypothesis has nothing to do with what I am
proving".  `plus`'s filter tests `le 1 a`, which is **what `plus` is defined by** — a
statement about what `plus` computes must mention the condition `plus` branches on, so
nothing is being smuggled across a boundary and the answer is a missing lemma in the file
that owns the definition, not a direct proof.  §11's roundtrip was the other case:
`ofList (toList b) = b` is about normal forms and the goal never mentioned them. -/

theorem tdepth_pos : ∀ (t : Term), t ≠ zero → 1 ≤ tdepth t := by
  intro t ht
  cases t with
  | zero => exact absurd rfl ht
  | M => exact Nat.le_refl _
  | omg _ => simp only [tdepth]; omega
  | Z _ => simp only [tdepth]; omega
  | psi _ _ => simp only [tdepth]; omega
  | phi _ _ => simp only [tdepth]; omega
  | add _ _ => simp only [tdepth]; omega

-- the leaf case's requirement, and the refuted measure failing it at exactly `M`
#guard 1 <= tdepth TM.Term.M
#guard !(1 <= tdepthOld TM.Term.M)


/-! ### §11.3 `tdepth_fpDeep` — structural, as expected

`fpDeep` is fuel-recursive, so the induction is on the fuel; both of its steps are
already covered — `isFP` at the top returns `t` itself, and the descent goes through
`summands (splitFin x).1` of a `φ̄`'s subscript, which is `tdepth_summands` composed with
`tdepth x ≤ tdepth (φ̄(c,x))`.  No new machinery, which is what §9.1 predicted for this
one.  `findSome_mem` is the only general lemma it needed and core does not have it. -/

theorem findSome_mem {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (b : β), l.findSome? f = some b → ∃ a ∈ l, f a = some b := by
  intro l
  induction l with
  | nil => intro b h; simp only [List.findSome?] at h; exact absurd h (by simp)
  | cons x xs ih =>
    intro b h
    simp only [List.findSome?_cons] at h
    cases hx : f x with
    | some c =>
      rw [hx] at h
      exact ⟨x, List.mem_cons_self, by rw [hx]; exact h⟩
    | none =>
      rw [hx] at h
      obtain ⟨a, ha, hfa⟩ := ih b h
      exact ⟨a, List.mem_cons_of_mem x ha, hfa⟩

theorem tdepth_fpDeepF : ∀ (f : Nat) (a t g : Term),
    fpDeepF f a t = some g → tdepth g ≤ tdepth t := by
  intro f
  induction f with
  | zero => intro a t g h; simp only [fpDeepF] at h; exact absurd h (by simp)
  | succ f ih =>
    intro a t g h
    simp only [fpDeepF] at h
    split at h
    · injection h with h; rw [← h]; exact Nat.le_refl _
    · cases t with
      | phi c x =>
        obtain ⟨y, hy, hfy⟩ := findSome_mem _ _ g h
        exact Nat.le_trans (ih a y g hfy)
          (Nat.le_trans (tdepth_summands x y hy) (by simp only [tdepth]; omega))
      | zero => exact absurd h (by simp)
      | M => simp at h
      | omg _ => simp at h
      | psi _ _ => simp at h
      | Z _ => simp at h
      | add _ _ => simp at h

theorem tdepth_fpDeep (a t g : Term) (h : fpDeep a t = some g) : tdepth g ≤ tdepth t :=
  tdepth_fpDeepF _ a t g h


/-! ### §11.4 THE COORDINATOR'S ROUTE (S), MEASURED BEFORE IT IS PROVED

    (S)   L'.Sublist L  →  tdepth (ofList L') ≤ tdepth (ofList L)

(S) MENTIONS NO `isAP`, NO `CNV`, NO `le` — pure list combinatorics, which is what makes
it a candidate to replace both routed `plus` lemmas.  Measured over every order-preserving
sub-list of 16 base lists, including shapes built to attack the position argument (a
deep element LAST, where a positional model would weight it most; deep elements
interleaved; a seven-element list of `1`s):

    448 sublist pairs      0 violations
    control (reverse)      400 of 448 FAIL — the test discriminates
    tightest margin        0 — it is exact somewhere, so (S) is tight, not slack

**AND THE REASONING FIRST OFFERED FOR (S) IS FALSE, WHICH THE MEASUREMENT DID NOT SHOW.**
The proposed formula was `tdepth (ofList [a₁…aₙ]) = max over i of ((i−1) + tdepth aᵢ)`,
giving the head weight 0.  It is refuted — 44 of 578 for veblen2, and directly:

    tdepth (add deep M) = 6      with tdepth deep = 5, tdepth M = 1
    the formula gives     5

because `ofList [a,b] = add a b` has depth `1 + max (tdepth a) (tdepth b)` and the `1+`
sits on the `add` NODE, applying to BOTH branches.  (S) survives because the correct
weights are still monotone in position — a different argument from the one offered.

**THE GENERAL FORM, and it is the sharpest thing to come out of this exchange: A
MEASUREMENT THAT CONFIRMS A LEMMA DOES NOT CONFIRM THE REASONING OFFERED FOR IT.**  The
448 pairs were about (S).  The formula was never what was measured, and I reported the
numbers as showing it — attaching correct evidence to the wrong statement, which is the
count-versus-set error in a new place.  The proof of (S) in §11.5 does not use the
formula and never did.

**THE SECOND HALF DOES NEED THE ROUNDTRIP.**  `ofList (toList t) = t` is measured true on
all 234 terms of `allM`, so it is a fact — and it is a NORMAL-FORM fact, which means (S)
buys the LEFT side of `tdepth_predOr` only.  Relating `toList g ++ replicate (k+1) one`
back to `t` still wants it.

**AND THE `k = 0` BRANCH IS ALREADY CLOSED — neither routed lemma touches it.**
`ofNat 0 = zero`, `toList zero = []`, so `plus g zero = g` by `plus`'s own `[] => s`
branch, and the goal is then `tdepth_ofList_take`, which §11 proves.  Confirmed
computationally on all 234.  So what the other lane must deliver is the `k ≥ 1` branch
alone. -/

def subsOf {α : Type} (l : List α) : List (List α) :=
  (List.range (2 ^ l.length)).map (fun m =>
    (l.zipIdx.filter (fun p => (m / (2 ^ p.2)) % 2 == 1)).map (fun p => p.1))

def deepT : Term := phi (ofNat 2) (phi one (phi zero omega))

def sBases : List (List Term) :=
  [[one, phi one zero], [phi one zero, one, one], [TM.Term.M, one],
   [phi (ofNat 2) zero, phi one zero, one, one],
   [phi one zero, phi one zero, one], [TM.Term.Z zero, TM.Term.M, one],
   [phi zero omega, one, one, one], [phi one zero, TM.Term.M, one, one],
   [one, one, one, one, deepT], [deepT, one, one, one, one],
   [one, deepT, one, deepT, one], [TM.Term.M, one, one, one, deepT],
   [phi one zero, one, TM.Term.M, one, phi one zero, one],
   [one, one, one, one, one, one, one], [deepT, deepT, one, one],
   [one, one, deepT, TM.Term.Z zero, one]]

def sPairs : List (List Term × List Term) :=
  sBases.flatMap (fun l => (subsOf l).map (fun s => (s, l)))

#eval (sPairs.length,
       (sPairs.filter (fun p => !(tdepth (ofList p.1) <= tdepth (ofList p.2)))).length,
       (sPairs.filter (fun p => !(tdepth (ofList p.2) <= tdepth (ofList p.1)))).length,
       sPairs.foldl (fun m p => min m (tdepth (ofList p.2) - tdepth (ofList p.1))) 99)

#guard (sPairs.filter (fun p => !(tdepth (ofList p.1) <= tdepth (ofList p.2)))).length == 0
#guard (sPairs.filter (fun p => !(tdepth (ofList p.2) <= tdepth (ofList p.1)))).length == 400
#guard (allM.filter (fun t => !(ofList (toList t) == t))).length == 0
#guard (ofNat 0 == zero) && (allM.filter (fun t => !(plus t (ofNat 0) == t))).length == 0


/-! ### §11.5 THE SUBLIST BOUND — the coordinator's (S), proved, and without the roundtrip

veblen2 delivered `toList_ofNat`, `plus_eq_of_toList` and `plus_ofNat_succ` (WF §15.24) and
two corrections that between them close off both obvious routes to `tdepth_predOr`:

  * `ofList (toList t) = t` is FALSE — 30 of 578 for them, and 5 of the 14 zero-component
    terms I then built.  **My §11.4 "0 violations over `allM`" was measured on a corpus with
    NO zero-component terms at all** (0 of 234, checked).  Same blindness as `φ̄(0,M)`, in my
    own measurement, one section after I wrote the caution.
  * `plus_ofNat_succ` needs `CNV s`, and **none of the 14 zero-component terms is `CNV`** —
    so that hypothesis is not dischargeable where `encvF` actually calls `predOr`.

FIRST, THE GOOD NEWS, MEASURED ON EXACTLY THE BLIND REGION: all six `tdepth` facts hold on
those 14 terms — `predOr` 0 violations, `omLog` 0, summands/headD/fpDeep 0, minFuel 0.  There
is no second counterexample; what the region kills is the two ROUTES, not the lemma.

**AND THAT IS THE RULE TO TAKE FROM IT: WHEN A CORPUS TURNS OUT BLIND, RE-CHECK THE ROUTES
IT VALIDATED AS WELL AS THE CLAIMS.**  Someone re-checking only "does my lemma survive the
new region" gets a clean answer here — all six hold — and keeps a dead route: the roundtrip
and `plus_ofNat_succ`'s `CNV` are both refuted by the same 14 terms that refute nothing about
the lemmas.  A blind corpus validates the WAY you were going to prove something just as
silently as it validates what you were going to prove.

AND ON HOW THE ROUTE WAS CHOSEN, so the record is fair: L1/L2 were recommended over (S)
because they already existed, which was correct on the information both lanes had.  It was
overturned by a fact neither had — `CNV` is not dischargeable where `encvF` actually calls
`predOr`.  **"Already proved" is a COST argument; "usable here" is a FEASIBILITY one, and
the second decides.**  Neither lane was wrong; the corpus was.

SO THE ROUTE IS (S), AND IT IS PROVED HERE BY THE SAME MOVE AS `tdepth_ofList_take`:
induct on the TERM, not on the list, and the roundtrip never appears.  **Third use of that
move in this file — `tdepth_ofList_take`, `tdepth_summands`, and now (S) — and each time it
makes the normal-form fact UNNECESSARY rather than merely avoided.  It is the house
technique for any bound about `ofList` of something derived from `toList t`.**  `plus_eq_of_toList`
is unconditional, `toList_ofNat` is unconditional, and `filter` yields a sublist — so
`tdepth_predOr` needs no `CNV` and no normal-form fact at all. -/

theorem tdepth_ofList_sublist : ∀ (b : Term) (L : List Term),
    L.Sublist (toList b) → tdepth (ofList L) ≤ tdepth b := by
  intro b
  induction b with
  | zero => intro L hL; simp only [toList] at hL; cases hL; exact Nat.le_refl _
  | M => intro L hL; simp only [toList] at hL; cases hL <;> rename_i h <;> cases h <;> simp only [ofList, tdepth] <;> omega
  | omg _ _ => intro L hL; simp only [toList] at hL; cases hL <;> rename_i h <;> cases h <;> simp only [ofList, tdepth] <;> omega
  | psi _ _ _ _ => intro L hL; simp only [toList] at hL; cases hL <;> rename_i h <;> cases h <;> simp only [ofList, tdepth] <;> omega
  | Z _ _ => intro L hL; simp only [toList] at hL; cases hL <;> rename_i h <;> cases h <;> simp only [ofList, tdepth] <;> omega
  | phi _ _ _ _ => intro L hL; simp only [toList] at hL; cases hL <;> rename_i h <;> cases h <;> simp only [ofList, tdepth] <;> omega
  | add u v _ ihv =>
    intro L hL
    simp only [toList] at hL
    cases hL with
    | cons _ h => have := ihv _ h; simp only [tdepth]; omega
    | cons_cons _ h =>
      rename_i L'
      have hv := ihv L' h
      cases hL' : L' with
      | nil => simp only [ofList, tdepth]; omega
      | cons y ys =>
        show tdepth (TM.Term.add u (ofList (y :: ys))) ≤ tdepth (TM.Term.add u v)
        rw [hL'] at hv
        simp only [tdepth] at hv ⊢
        omega


-- the refuted formula, banked as a live control: it is NOT what the 448 pairs measured
def deepW : Term := phi (ofNat 2) (phi one (phi zero omega))
#guard (tdepth deepW, tdepth TM.Term.M, tdepth (TM.Term.add deepW TM.Term.M)) == (5, 1, 6)
#guard !(tdepth (TM.Term.add deepW TM.Term.M) == max (0 + tdepth deepW) (1 + tdepth TM.Term.M))


/-! ### §11.6 (W) IS FALSE — measured before anyone proved it, and the caution was the mechanism

The coordinator proposed weakening the missing fact from an equality to

    (W)   Sublist (toList ((splitFin a).1)) (toList a)

since `tdepth_ofList_sublist` only ever consumes a sublist — and cautioned that
`toList (ofList X)` might insert structure, saying to measure rather than take their word.
**IT DOES, AND (W) IS FALSE.**  4 violations of the 254-term sweep and 5 of the 8
`addHead` probes below — every one with an `add`-HEADED COMPONENT:

    t = ((1+1)+1)          toList t             = [(1+1), 1]
                           (splitFin t).1       = (1+1)
                           toList (splitFin t).1 = [1, 1]      NOT a sublist of [(1+1), 1]

`toList` recurses on the right, so a component can itself be `add`-headed, and then
`ofList` and `toList` do not agree on where the structure is.

THE SEPARATING HYPOTHESIS IS MEASURED, not guessed: every violation has a NON-AP component,
and restricted to terms all of whose components are additively principal, **(W) holds with
0 violations of 235**.  So the normal-form content does come back — as 2.1(iii)'s AP
condition rather than as the roundtrip.

**THE THIRD DISGUISE.  The same 2.1(iii) content has now arrived as `inT`, as `CNV`, and as
"AP components".**  Someone meeting it a fourth time should recognise it rather than
re-derive that it is not free, and the recognition test is the one that settled all three:
**is the hypothesis dischargeable where the function is actually CALLED?**  For a TOTAL
function the answer is usually no — `encvF` is total, the 8 witnesses are terms it can be
called on, so the hypothesis is not merely awkward, it is FALSE at the call site.  That is
a stronger objection than the earlier ones, which were "this would narrow invisibly"; this
one is "this would not apply".

**AND THE LEMMAS SURVIVE THE REGION THAT KILLS THE ROUTE — THIRD TIME TONIGHT.**  All six
`tdepth` facts hold on the 8 `add`-headed terms (0 violations), none of which is `inT` or
`CNV`.  §11.4's rule caught this one: I checked the routes as well as the claims, and the
route is what died.  A blind corpus had validated (W) exactly as it had validated the
roundtrip and `plus_ofNat_succ`'s `CNV`. -/

def isSubl : List Term → List Term → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x == y then isSubl xs ys else isSubl (x :: xs) ys

def addHead : List Term :=
  [TM.Term.add (TM.Term.add one one) one, TM.Term.add (TM.Term.add (phi one zero) one) one,
   TM.Term.add (TM.Term.add one one) (TM.Term.add one one),
   phi zero (TM.Term.add (TM.Term.add one one) one),
   TM.Term.add (TM.Term.add TM.Term.M one) one,
   TM.Term.add (TM.Term.add one (phi one zero)) one,
   TM.Term.add (TM.Term.add (TM.Term.add one one) one) one,
   phi one (TM.Term.add (TM.Term.add one one) one)]

-- (W) is FALSE, and the witness family is `add`-headed components
#guard !(isSubl (toList (TM.Term.splitFin (TM.Term.add (TM.Term.add one one) one)).1)
                (toList (TM.Term.add (TM.Term.add one one) one)))
#guard (addHead.filter (fun t => !(isSubl (toList (TM.Term.splitFin t).1) (toList t)))).length == 5
-- under the AP-components hypothesis it holds, and the lemmas hold regardless
#guard ((allM ++ addHead).eraseDups.filter (fun t => (toList t).all (fun c => TM.Term.isAP c)
          && !(isSubl (toList (TM.Term.splitFin t).1) (toList t)))).length == 0
#guard (addHead.filter (fun t => !(tdepth (predOr t) <= tdepth t))).length == 0
#guard (addHead.filter (fun t => !(tdepth (omLog t) <= tdepth t))).length == 0
#guard (addHead.filter (fun t => TM.Term.inT t)).length == 0


/-! ### §11.7 THE HOUSE TECHNIQUE ON `tdepth_predOr` — the recursion, measured

(W) is dropped: it gives `Sublist (toList g) (toList a)`, which is the half that was
already free, while the assembly also needs `replicate m one` positioned AFTER those
components — i.e. `toList a = toList g ++ replicate m one`, the decomposition, which is
the equality again.

SO: induct on `a`.  The `add` case's candidate recursion, measured on 15 pairs before
anything was designed:

    predOr (add x y) = add x (predOr y)          5 violations of 15
    (splitFin (add x y)).2 = (splitFin y).2      the same 5

**AND THE 5 ARE EXACTLY THE CASES WHERE `predOr y = zero`**, where the right-hand side
`add x zero` is a non-normal form and the left-hand side is plain `x`:

    x = 1, y = 1        predOr (x ⊕ y) = 1        x ⊕ predOr y = 1 ⊕ 0
    x = M, y = 1        predOr (x ⊕ y) = M        x ⊕ predOr y = M ⊕ 0

**THE BOUND SURVIVES THE DEGENERATE CASE EVEN THOUGH THE IDENTITY DOES NOT.**  But the
degenerate case splits FURTHER, and my first reading of it was wrong — corrected here
rather than built on:

    predOr y ≠ 0              predOr (add x y) = add x (predOr y)     0 violations
    predOr y = 0, y ≠ 0       predOr (add x y) = x                    0 of 4
    y = 0                     NEITHER — `predOr (1 ⊕ 0) = 0` but `predOr (ε₀ ⊕ 0) = ε₀ ⊕ 0`

I had written the degenerate branch as "`= x`" without the `y ≠ 0` side condition; `y = 0`
makes `add x y` a non-normal term whose trailing ones are `x`'s own, so `predOr` there
depends on `x` and not on the shape of the `add`.  The BOUND still holds in all three (0
violations everywhere measured) — **`tdepth (ε₀ ⊕ 0) = 3 = tdepth (add ε₀ 0)`, EXACTLY.
A zero margin in the awkward branch means what it meant for `tdepth_omLog`: no slack, so
the statement is right and nothing weaker will do.**  Second zero-margin case in this file,
and both times it was the branch that looked like it might not survive.

**AND THE THIRD BRANCH IS NOT THE AWKWARD ONE — IT COLLAPSES.**  It was expected to be most
of the work, being the only branch governed by the term being non-normal.  But
`toList (add x 0) = [x]`: `toList` DROPS the trailing zero, so the branch is the LEAF
computation with `x` in place of the leaf, and `tdepth_predOr_add_zero` below is the leaf
proof verbatim.  The property that made it look dangerous — non-normality — is exactly the
property that makes `toList` erase it.

**THE QUESTION TO ASK AT SUCH A BRANCH IS NOT "HOW BAD IS THE NON-NORMALITY" BUT "DOES
ANYTHING DOWNSTREAM STILL SEE IT?"**  Here nothing does, one step in.  The coordinator's
prediction picked the right branch — `y = 0` IS the distinctive one — and inverted what the
distinctiveness implies, which is worth recording because the next person meeting a
non-normal branch will budget for it the same way.

WHAT THIS ROUTE NEEDS, AND WHY IT IS THE RIGHT ONE: two facts about how `splitFin`
recurses through `add` — **facts about `splitFin`'s own definition, not about normal
forms**.  That is the coordinator's tell for this route being the right one; if the
induction turns out to need "components are AP", the route has collapsed into the one
being avoided and it stops there.

**AND THIS IS THE SECOND HALF OF THE HOUSE TECHNIQUE, on its fourth use tonight: PROVE THE
BOUND, NOT THE IDENTITY.**  `tdepth_ofList_take`, `tdepth_summands`, (S), and now this —
where the identity is not merely harder but FALSE on 5 of 15, and the bound goes through
anyway.  The two halves are complementary: **"induct on the term" says where to put the
induction; "prove the bound" says what to state**, and both have the same effect — the
normal-form fact becomes unnecessary rather than avoided.  Measuring the recursion before
designing is what turned a refutation into a case split rather than into a lost turn. -/

/-- Every LEAF case of `tdepth_predOr`.  `splitFin` of a non-`add` term has finite part 1
    exactly when the term IS `1`, and then `predOr` is `0`; otherwise the finite part is 0
    and `predOr` is the identity. -/
theorem tdepth_predOr_leaf (c d : Term) :
    tdepth (predOr (TM.Term.phi c d)) ≤ tdepth (TM.Term.phi c d) := by
  by_cases h : (TM.Term.phi c d == one) = true
  · have he : TM.Term.phi c d = one := by simpa using h
    rw [he]
    show tdepth (predOr one) ≤ tdepth one
    decide
  · simp only [predOr, TM.Term.splitFin, toList, List.reverse, List.reverseAux,
      List.takeWhile, h, List.length]
    exact Nat.le_refl _

theorem tdepth_predOr_zero : tdepth (predOr zero) ≤ tdepth zero := by
  simp only [predOr, TM.Term.splitFin, toList]; exact Nat.le_refl _

theorem tdepth_predOr_M : tdepth (predOr TM.Term.M) ≤ tdepth TM.Term.M := by
  simp only [predOr, TM.Term.splitFin, toList]; exact Nat.le_refl _

theorem tdepth_predOr_omg (c : Term) : tdepth (predOr (TM.Term.omg c)) ≤ tdepth (TM.Term.omg c) := by
  simp only [predOr, TM.Term.splitFin, toList]; exact Nat.le_refl _

theorem tdepth_predOr_psi (c e : Term) :
    tdepth (predOr (TM.Term.psi c e)) ≤ tdepth (TM.Term.psi c e) := by
  simp only [predOr, TM.Term.splitFin, toList]; exact Nat.le_refl _

theorem tdepth_predOr_Z (c : Term) : tdepth (predOr (TM.Term.Z c)) ≤ tdepth (TM.Term.Z c) := by
  simp only [predOr, TM.Term.splitFin, toList]; exact Nat.le_refl _

def probeXY : List (Term × Term) :=
  [(one, one), (one, plus one one), (phi one zero, one), (phi one zero, plus one one),
   (one, phi one zero), (one, plus (phi one zero) one), (TM.Term.M, one),
   (phi one zero, plus (phi one zero) one), (one, zero), (phi one zero, zero),
   (TM.Term.M, plus one one), (one, plus one (plus one one)),
   (phi (ofNat 2) zero, plus (phi one zero) (plus one one)),
   (TM.Term.add one one, one), (one, TM.Term.add one one)]

#guard (probeXY.filter (fun p =>
          !(predOr (TM.Term.add p.1 p.2) == TM.Term.add p.1 (predOr p.2)))).length == 5
-- and every violation is a `predOr y = zero` case, where the BOUND still holds
#guard (probeXY.filter (fun p =>
          !(predOr (TM.Term.add p.1 p.2) == TM.Term.add p.1 (predOr p.2)))).all
       (fun p => predOr p.2 == zero)
#guard (probeXY.filter (fun p =>
          !(tdepth (predOr (TM.Term.add p.1 p.2)) <= tdepth (TM.Term.add p.1 p.2)))).length == 0
-- off the degenerate case the identity holds
#guard (probeXY.filter (fun p => !(predOr p.2 == zero)
          && !(predOr (TM.Term.add p.1 p.2) == TM.Term.add p.1 (predOr p.2)))).length == 0


#guard (probeXY.filter (fun p => predOr p.2 == zero && !(p.2 == zero)
          && !(predOr (TM.Term.add p.1 p.2) == p.1))).length == 0
#guard !(predOr (TM.Term.add (phi one zero) zero) == phi one zero)
#guard tdepth (predOr (TM.Term.add (phi one zero) zero)) <= tdepth (TM.Term.add (phi one zero) zero)


/-- **BRANCH C of the `add` case.**  `toList (add x 0) = [x]`, so this is the leaf
    computation, not a new one: the finite part is 1 exactly when `x` IS `1`. -/
theorem tdepth_predOr_add_zero (x : Term) :
    tdepth (predOr (TM.Term.add x zero)) ≤ tdepth (TM.Term.add x zero) := by
  by_cases h : (x == one) = true
  · have he : x = one := by simpa using h
    rw [he]
    show tdepth (predOr (TM.Term.add one zero)) ≤ tdepth (TM.Term.add one zero)
    decide
  · simp only [predOr, TM.Term.splitFin, toList, List.reverse, List.reverseAux,
      List.takeWhile, h, List.length]
    exact Nat.le_refl _


/-! ### §11.8 THE ROUNDTRIP AS A BOUND — the AP condition does not appear after all

Branch A wants `toList (ofList prefix)`, and that is where the AP condition was expected
to arrive: the IDENTITY `ofList (toList t) = t` is false (4 violations of 251 here, 30 of
578 for veblen2) and its repair is 2.1(iii) in its third disguise.

**BUT THE ASSEMBLY CONSUMES A BOUND, NOT AN IDENTITY — house technique, FIFTH use:**

    identity   ofList (toList t) = t                        4 violations of 251
    BOUND      tdepth (ofList (toList t)) ≤ tdepth t        0 violations, margin 0
    the shape branch A needs                                0 violations
        tdepth (ofList (toList ((splitFin t).1))) ≤ tdepth t

**So the AP condition does not appear**, and `tdepth_ofList_toList` below is four lines by
induction on the term.  Third zero-margin case in this file: the bound is tight, so
nothing weaker would have done, and the identity — which is what everyone reaches for —
is strictly stronger than what is needed and false.

**AND THE THREE ZERO MARGINS ARE A PATTERN, NOT A COINCIDENCE.**  `tdepth_omLog`, branch C,
and this — each time the bound was tight, and each time it was the case that looked LEAST
likely to survive.  Tight bounds in the dangerous cases mean the statements are the right
ones: **there was no slack to have spent on a weaker formulation, so nothing weaker was
ever available.**  That is the strongest evidence this family of statements is correctly
shaped rather than merely provable.

THE PATTERN IS NOW WORTH STATING AS A RULE, since it has decided five separate obstacles:
**when a normal-form fact blocks you, check whether what you consume is the EQUALITY or
only a BOUND ON A MEASURE.  The bound survives the terms the equality dies on, because
the measure is what `toList`/`ofList` preserve and the structure is not.** -/

theorem tdepth_ofList_toList : ∀ (t : Term), tdepth (ofList (toList t)) ≤ tdepth t := by
  intro t
  induction t with
  | zero => simp only [toList, ofList]; exact Nat.le_refl _
  | M => simp only [toList, ofList]; exact Nat.le_refl _
  | omg _ _ => simp only [toList, ofList]; exact Nat.le_refl _
  | psi _ _ _ _ => simp only [toList, ofList]; exact Nat.le_refl _
  | Z _ _ => simp only [toList, ofList]; exact Nat.le_refl _
  | phi _ _ _ _ => simp only [toList, ofList]; exact Nat.le_refl _
  | add u v _ ihv =>
    simp only [toList]
    cases h : toList v with
    | nil => simp only [ofList, tdepth]; omega
    | cons y ys =>
      show tdepth (TM.Term.add u (ofList (y :: ys))) ≤ tdepth (TM.Term.add u v)
      rw [h] at ihv
      simp only [tdepth] at ihv ⊢
      omega

def wideAll : List Term := (allM ++ addHead ++ probeXY.map (fun p => TM.Term.add p.1 p.2)
  ++ [TM.Term.add zero zero, TM.Term.add TM.Term.M zero, TM.Term.add one zero,
      TM.Term.add (phi one zero) zero, TM.Term.add zero one]).eraseDups

-- the identity fails where the bound holds — banked so the distinction stays visible
#guard (wideAll.filter (fun t => !(ofList (toList t) == t))).length == 4
#guard (wideAll.filter (fun t => !(tdepth (ofList (toList t)) <= tdepth t))).length == 0
#guard wideAll.foldl (fun m t => min m (tdepth t - tdepth (ofList (toList t)))) 99 == 0


/-! ### §11.9 BRANCHES A AND B — three `plus` bounds measured, and why the true one is too weak

The remaining branches reduce to bounding `plus g (ofNat k)` where `(g, k+1) = splitFin a`
and `tdepth g ≤ tdepth a` is already proved (`tdepth_splitFin_fst`).  Three candidates,
measured over 1255 pairs before any was attempted:

    tdepth (plus s u) ≤ max (tdepth s) (tdepth u)             869 violations   FALSE
    tdepth (plus s u) ≤ 1 + max (tdepth s) (tdepth u)          77 violations   FALSE
    tdepth (plus s u) ≤ tdepth s + tdepth u                      0 violations   TRUE

**AND THE TRUE ONE IS TOO WEAK, WHICH IS THE POINT OF MEASURING ALL THREE.**  It gives
`tdepth (predOr a) ≤ tdepth a + tdepth (ofNat k)`, and that is `≤ tdepth a` only when
`k = 0`.  What the branches need is a bound that ties `k` BACK TO `a` — the `k` trailing
ones are components OF `a`, so `a` is deep enough to pay for them, and no bound stated in
terms of `s` and `u` alone can express that.  A `plus` lemma is the wrong shape here; the
lemma has to mention `splitFin`.

Recorded rather than attempted: two false candidates cost one `#eval` each, and the true
one would have cost a proof and then not closed the goal. -/

def pairsSU : List (Term × Term) :=
  wideAll.flatMap (fun s => [(s, one), (s, ofNat 2), (s, ofNat 3), (s, phi one zero), (s, zero)])

#guard (pairsSU.filter (fun p =>
          !(tdepth (TM.Term.plus p.1 p.2) <= max (tdepth p.1) (tdepth p.2)))).length == 869
#guard (pairsSU.filter (fun p =>
          !(tdepth (TM.Term.plus p.1 p.2) <= 1 + max (tdepth p.1) (tdepth p.2)))).length == 77
#guard (pairsSU.filter (fun p =>
          !(tdepth (TM.Term.plus p.1 p.2) <= tdepth p.1 + tdepth p.2))).length == 0


/-! ### §11.10 THE INTERMEDIATE IS NOT EXPRESSIBLE IN `g` AND `k` — five candidates, one true

The goal for branches A and B is `tdepth (plus g (ofNat k)) ≤ tdepth a`, where
`(g, k+1) = splitFin a`.  Two facts are in hand: `tdepth g ≤ tdepth a`
(`tdepth_splitFin_fst`, proved) and `(splitFin a).2 ≤ tdepth a` (measured, 0 violations —
the trailing ones are paid for by the depth).  Five candidate intermediates, all measured
before any was attempted:

    tdepth (plus s u) ≤ max (tdepth s) (tdepth u)                869 of 1255   FALSE
    tdepth (plus s u) ≤ 1 + max (tdepth s) (tdepth u)             77 of 1255   FALSE
    tdepth (plus s u) ≤ tdepth s + tdepth u                         0          TRUE, TOO WEAK
    tdepth (plus g (ofNat k)) ≤ max (tdepth g) (k+1)               12 of 51    FALSE
    tdepth (plus g (ofNat k)) ≤ max (tdepth g) (tdepth (ofNat (k+1)))  12 of 51 FALSE

**NOTHING STATED IN TERMS OF `g` AND `k` ALONE HAS HELD**, and the reason is visible in the
`add`-headed witnesses of §11.6: `toList (ofList X)` can be LONGER than `X`, so `|toList g|`
is not bounded by `a`'s component count, and the depth of the reassembled list is not
bounded by `a`'s.  The bound is true — `predOr` violations are 0 on every corpus measured —
but its proof needs the LENGTH relation between `toList g` and `toList a`, which is the
structural content the measure was supposed to let us avoid.

`tdepth (ofNat n) = n` exactly, measured for n ≤ 6, so the arithmetic is not the obstacle;
the obstacle is that `g` has forgotten how it sat inside `a`. -/

#guard (wideAll.filter (fun t => !((TM.Term.splitFin t).2 <= tdepth t))).length == 0
#guard ((List.range 7).map (fun n => tdepth (ofNat n))) == [0, 1, 2, 3, 4, 5, 6]
#guard (wideAll.filter (fun t => (TM.Term.splitFin t).2 >= 1 && (fun g k =>
          !(tdepth (TM.Term.plus g (ofNat k)) <= max (tdepth g) (k + 1)))
          (TM.Term.splitFin t).1 ((TM.Term.splitFin t).2 - 1))).length == 12


/-! ## §12 `tdepth_predOr` IS FALSE, AND WITH IT `tdepth` AS THE MEASURE  (2026-08-10)

The coordinator proposed measuring the goal itself, (D'), before choosing a decomposition.
**It is false**, and the witness kills more than the branch:

    t = (1 ⊕ (1⊕1)) ⊕ (1 ⊕ (1⊕1))        i.e. `add (ofNat 3) (ofNat 3)`
        tdepth t        = 4
        splitFin t      = (ofNat 3, 3)
        predOr t        = ofNat 5
        tdepth (predOr t) = 5              **5 > 4**

THE MECHANISM is §11.6's, one level up.  `toList t = [ofNat 3, 1, 1, 1]` — the FIRST
component is `add`-headed, so `splitFin` returns `g = ofNat 3` and `k = 2`, and
`plus (ofNat 3) (ofNat 2) = ofNat 5` is a FLAT chain of five, deeper than the balanced
`add` of two threes it came from.  **`predOr` can flatten, and flattening deepens.**

**AND IT REFUTES THE MEASURE, NOT ONLY THE LEMMA.**  Hosting the witness as a `φ̄`
argument breaks D8's key inequality directly:

    minFuel ≤ tdepth on 9 host terms       6 VIOLATIONS
    e.g. `φ̄(t, 0)` needs fuel 6 with tdepth 5

So `tdepth` is NOT a valid measure for `encvF_saturate`: the induction on a bound
`n ≥ tdepth t` cannot be discharged at the `predOr` site, and no repair of `tdepth_predOr`
alone would fix it — the site's obligation is false.

WHAT SURVIVES, and it is most of the work:
  * §10's three named equations and §10.1's four congruences — no `tdepth` in them;
  * `encvF_saturate`'s ASSEMBLY — every case, needing only that SOME measure works;
  * `tdepth_summands`, `tdepth_headD`, `tdepth_fpDeep`, `tdepth_ofList_take`,
    `tdepth_ofList_sublist`, `tdepth_ofList_toList`, `tdepth_pos` — all still true and
    proved; they are facts about `tdepth`, and `tdepth` is still a function.
WHAT DIES: `tdepth` as THE measure, and with it §9.1's plan and D8's green.

**THE SATURATION ITSELF IS NOT REFUTED.**  `encvF (2*deg+8+k) t 0 = encv t 0` still holds
on the host terms (0 violations, k ≤ 5).  The fuel `encv` chooses is still enough; what is
wrong is the claim that `tdepth` bounds what it needs to be.

NOTHING IS REPAIRED HERE.  The measure was changed once already (§9.2, `M` at depth 1) on
an argument that the proof then consumed; a second repair without the coordinator is
exactly what the standing instruction forbids. -/

def badPredOr : Term := TM.Term.add (ofNat 3) (ofNat 3)

def badHosts : List Term :=
  [phi badPredOr zero, phi badPredOr one, phi badPredOr (phi one zero),
   phi zero badPredOr, phi one badPredOr, phi badPredOr badPredOr,
   phi (phi badPredOr zero) zero, TM.Term.add badPredOr one, phi badPredOr (ofNat 2)]

-- the counterexample, banked as a live control
#guard (tdepth badPredOr, tdepth (predOr badPredOr)) == (4, 5)
#guard !(tdepth (predOr badPredOr) <= tdepth badPredOr)
#guard (TM.Term.splitFin badPredOr).2 == 3
#guard (TM.Term.inT badPredOr, Evidence.WF.CNV badPredOr,
        (toList badPredOr).all (fun c => TM.Term.isAP c)) == (false, false, false)
-- and the measure's own obligation failing at the host
#guard (badHosts.filter (fun t =>
          !(((List.range 80).find? (fun f => encvF f t 0 == encv t 0)).getD 199 <= tdepth t))).length == 6
-- while the SATURATION still holds there
#guard (badHosts.filter (fun t =>
          !((List.range 6).all (fun k => encvF (2 * t.deg + 8 + k) t 0 == encv t 0)))).length == 0


/-! ### §12.1 THE FOURTH OPTION IS REFUTED BY THE SAME WITNESS

The coordinator proposed closing A and B from §11.7's measured identities rather than from
a `plus` bound — `predOr (add x y) = add x (predOr y)` when `predOr y ≠ 0` — so that `g`
never appears and never has to remember where it sat.  The reasoning is right and the
identity is false:

    x = y = ofNat 3, and `predOr y = ofNat 2 ≠ 0`, so branch A applies
        LHS  predOr (add x y)     = ofNat 5                     tdepth 5
        RHS  add x (predOr y)     = ofNat 3 ⊕ ofNat 2           tdepth 4

**5 violations of the 8 applicable pairs** once `add`-headed components are in the corpus.
§11.7's "0 violations of 15" was measured on 15 pairs with none — the same blindness as
§11.4's roundtrip, now in the A/B measurement itself.

**AND THE TWO REFUTATIONS ARE ONE FACT.**  Note the tdepths: the RHS is 4 = `tdepth t`, so
IF the identity held the bound would follow.  The identity fails because `predOr` FLATTENS
— `plus (ofNat 3) (ofNat 2)` is a flat chain of five where `add x (predOr y)` keeps the
balanced shape — and flattening is exactly what deepens.  §12's counterexample and this one
are the same mechanism seen from the two sides of the equation.

SO ALL THREE ROUTES TO `tdepth_predOr` ARE CLOSED: the `plus` bound (forgetting), the
identity through `splitFin` (AP components), and the recursion identity (flattening).  The
statement is FALSE, so this is not a search for a fourth route — there is nothing to
prove. -/

#guard !(predOr (TM.Term.add (ofNat 3) (ofNat 3))
          == TM.Term.add (ofNat 3) (predOr (ofNat 3)))
#guard (tdepth (predOr (TM.Term.add (ofNat 3) (ofNat 3))),
        tdepth (TM.Term.add (ofNat 3) (predOr (ofNat 3))),
        tdepth (TM.Term.add (ofNat 3) (ofNat 3))) == (5, 4, 4)
#guard !(predOr (ofNat 3) == zero)


/-! ## §13 WHAT ACTUALLY DECREASES — the measure question, measured  (2026-08-10)

Two measures have died: `deg` at `omLog` (§9.2) and `tdepth` at `predOr` (§12).  Rather
than guess a third, the coordinator asked for the table — measure-before-designing applied
to the MEASURE.  Over 263 junk terms including both known witnesses, the `add`-headed
family, `φ̄(0,M)` and the zero-component terms, counting VIOLATIONS of "does not increase"
at each of `encvF`'s three non-structural recursion sites:

                       predOr     omLog     fpDeep out
    deg                   0         25          0
    tdepth                1          0          0
    size (constructors)   0         25          0
    ncomp (components)    3         44          0
    deg + tdepth          0         25          0
    size + tdepth         0         25          0
    lt, where it changes  0/55       6/78       8/74

**NO SINGLE MEASURE IN THIS FAMILY WORKS AT ALL THREE SITES**, and the failures are in
OPPOSITE DIRECTIONS, which is why sums do not rescue them: `predOr` FLATTENS (raises
nesting, lowers or preserves `deg` and `size`) and `omLog` NESTS (raises `deg` and `size`,
preserves nesting).  A sum inherits both failures; a lexicographic pair inherits whichever
component it tests first.  **The category is dead by measurement, not by two failures.**

THE ORDER — the coordinator's third direction — IS THE INTERESTING ROW.  `predOr` strictly
DECREASES `lt` whenever it changes the term: **0 violations of 55**.  That is the site
where every arithmetic measure struggles, and the order handles it exactly.  But `omLog`
violates on 6 of 78 and `fpDeep`'s output on 8 of 74, so `lt` is not a measure for the
recursion as a whole either — **and it fails at the two sites the arithmetic measures
handle.**  The three sites do not admit a common order.

WHAT THAT LEAVES, stated as measurement rather than as a plan: the recursion has three
sites with genuinely different behaviour, and `encvF`'s termination is currently carried by
the FUEL alone — which is why `encv` picks `2 * deg + 8` and why D8 measured that as
sufficient (0 violations over 234, and still 0 on the badHosts of §12).  **The fuel works;
what has no proof is that it works.** -/

def ncomp (t : Term) : Nat := (toList t).length

def tsize : Term → Nat
  | .zero => 1 | .M => 1
  | .omg a => 1 + tsize a | .Z a => 1 + tsize a
  | .psi a b => 1 + tsize a + tsize b
  | .phi a b => 1 + tsize a + tsize b
  | .add a b => 1 + tsize a + tsize b

def junk : List Term :=
  (wideAll ++ addHead ++ badHosts ++
   [badPredOr, phi zero TM.Term.M, TM.Term.add zero zero, TM.Term.add TM.Term.M zero,
    ofNat 3, ofNat 5, TM.Term.add (ofNat 3) (ofNat 2), TM.Term.add (ofNat 2) (ofNat 3),
    TM.Term.add (TM.Term.add one one) one, TM.Term.add (ofNat 3) (ofNat 3)]).eraseDups

#guard junk.length == 263
-- the row that decides it: every candidate fails at some site
#guard (junk.filter (fun t => !((omLog t).deg <= t.deg))).length == 25
#guard (junk.filter (fun t => !(tdepth (predOr t) <= tdepth t))).length == 1
#guard (junk.filter (fun t => !(tsize (omLog t) <= tsize t))).length == 25
#guard (junk.filter (fun t => !(ncomp (predOr t) <= ncomp t))).length == 3
#guard (junk.filter (fun t => !((omLog t).deg + tdepth (omLog t) <= t.deg + tdepth t))).length == 25
-- the order: perfect at `predOr`, and not at the other two
#guard (junk.filter (fun t => !(predOr t == t) && !(TM.Term.lt (predOr t) t))).length == 0
#guard (junk.filter (fun t => !(omLog t == t) && !(TM.Term.lt (omLog t) t))).length == 6
-- and the fuel still suffices everywhere, which is what has no proof
#guard (junk.filter (fun t =>
          !((List.range 4).all (fun k => encvF (2 * t.deg + 8 + k) t 0 == encv t 0)))).length == 0


/-! ## §14 THE RECURSION NEVER LEAVES 𝔗(M) FROM A LEGAL START  (2026-08-10)

**A DISCIPLINE WHOSE PAYOFF IS INVISIBLE UNTIL THE THING IT PROTECTS AGAINST HAPPENS IS
EXACTLY THE KIND NOBODY ADOPTS FROM REASONING.**  This file's measurements are `#eval`s and
`#guard`s rather than recorded numbers, and that looked like bookkeeping until the object
they measure was REDEFINED — at which point they re-run and nothing is lost, where a file
of prose numbers would have had to be re-measured or discarded.  The habit had to be paid
for once before it could be argued for.

The coordinator's assumption that `encvF`'s intermediates "need not be `inT`" was inferred
from `encvF` being TOTAL and not measured.  **Totality says `encvF` is DEFINED on junk; it
does not say a legal input produces junk arguments.**  Those are different claims, and the
measurement separates them.

`targetsF` below mirrors `encvF`'s recursion and collects every argument it recurses on,
over-approximating by taking ALL branches' targets rather than the one taken.  Over
**169 legal starting terms** — `corpusW ++ deeper`, all `inT` and all `CNV`, checked —
producing **40 distinct targets**:

    targets not `inT`        0
    targets not `lt` start   0
    targets not `CNV`        0

**CONTROL, and it fires: from the 42 JUNK starts, 10 DO produce non-`inT` targets.**  So
the property is not vacuous and not a quirk of the instrument — junk in, junk out; legal
in, legal out.  §12's and §9.2's counterexamples were terms fed to `encvF` DIRECTLY, which
is a different question from what `encvF` produces when fed a legal term, and that
distinction is the whole content of this section.

**CONSEQUENCE.**  `Evidence.WF.acc_inT_below_cnv` — every `inT` term below a `CNV` term is
accessible, with no fragment hypothesis on the term itself — applies to every recursion
target from a legal start.  **The termination `encvF_saturate` needs is already proved, and
no new order theory or arithmetic measure is required.**  §13's table stands as the record
that no measure in that family exists; it is no longer on the critical path.

WHAT IS STILL NOT PROVED: that the recursion stays inside 𝔗(M), which is measured here on
169 starts and is a THEOREM someone has to write.  It is a statement about `encvF`'s
clauses — `predOr`, `omLog`, `fpDeep` and the summands all landing in 𝔗(M) below the
input — and it is the shape §13 says no arithmetic measure can carry. -/

def targetsF : Nat → Term → List Term
  | 0, _ => []
  | _ + 1, .zero => []
  | f + 1, .add u v => [u, v] ++ targetsF f u ++ targetsF f v
  | f + 1, .phi a b =>
      let gs := summands (TM.Term.splitFin b).1
      let hd := gs.headD zero
      let lad : List Term := if a == zero then [] else [predOr a]
      let ladR : List Term := if a == zero then [] else targetsF f (predOr a)
      let blk : List Term := gs.map (fun g => if a == zero then g else omLog g)
      let blkR : List Term := (blk.map (fun g => targetsF f g)).flatten
      let cl : List Term := [hd] ++ targetsF f hd
      let dp : List Term := match fpDeep a hd with
        | some z => [z] ++ targetsF f z
        | none => []
      lad ++ ladR ++ blk ++ blkR ++ cl ++ dp
  | _ + 1, _ => []

def targets (t : Term) : List Term := (targetsF (2 * t.deg + 8) t).eraseDups

def startsW : List Term := (corpusW ++ deeper).eraseDups

#guard startsW.length == 169
#guard (startsW.filter (fun t => !(TM.Term.inT t))).length == 0
#guard (startsW.filter (fun t => !(Evidence.WF.CNV t))).length == 0
#guard (startsW.filter (fun t => !((targets t).all (fun u => TM.Term.inT u)))).length == 0
#guard (startsW.filter (fun t => !((targets t).all (fun u => TM.Term.lt u t)))).length == 0
#guard (startsW.filter (fun t => !((targets t).all (fun u => Evidence.WF.CNV u)))).length == 0
-- the CONTROL: junk starts DO produce non-`inT` targets, so the property is not vacuous
#guard ((junk.filter (fun t => !(TM.Term.inT t))).filter
          (fun t => !((targets t).all (fun u => TM.Term.inT u)))).length == 10


/-! ### §14.1 THE DISCRIMINATING QUESTION, AND ALL THREE SITES ON `inT` INPUTS

**(4) DO THE JUNK WITNESSES ARISE AS RECURSION TARGETS FROM A LEGAL ROOT?  NO — 0 of 13.**
`φ̄(0,M)`, `add (ofNat 3) (ofNat 3)`, the whole `add`-headed family, the zero-component
terms: none appears among the 40 targets of the 169 legal starts.  **§13's table describes
terms `encvF` never meets.**

AND THE SAME RUN SUPPLIES THE `inT`-ROOTED SAMPLE THAT FILTERING CANNOT REACH.  veblen2
cleared the `predOr` site on 5 movers out of a 1010-term corpus — `inT` is rare enough
(44 of 1010) that a wider corpus must be generated FOR the class rather than deeper.  The
call graph IS that generator: every target is `inT` by construction.  Over the pool of
169 (starts and targets, all `inT`):

                   movers   leave `inT`   fail the `lt`-step
    predOr           39          0                0
    omLog            28          0                0
    fpDeep           24          0                0

**ALL THREE SITES TAKE A GENUINE `RT`-STEP ON `inT` INPUTS** — target `inT`, target
strictly below.  §13 measured `omLog` violating `lt` on 6 of 78 and `fpDeep` on 8 of 74;
**those violations are junk-only and do not occur from a legal root.**  `predOr`'s positive
class goes from 5 to 39.

**SO THE MEASURE QUESTION IS CLOSED, NOT PARKED.**  `acc_inT_below_cnv` needs `inT` and
below a `CNV` bound; both hold at every site on every target measured.  No arithmetic
measure is required and §13's table is the record of why one was never going to work —
it was measuring the wrong domain, which is the same error as counting over the wrong
corpus, one level further out. -/

def allTargets : List Term := (startsW.flatMap targets).eraseDups

def witnesses : List Term :=
  [badPredOr, phi zero TM.Term.M] ++ addHead ++
  [TM.Term.add zero zero, TM.Term.add TM.Term.M zero, TM.Term.add (ofNat 3) (ofNat 3)]

def pool : List Term := (startsW ++ allTargets).eraseDups

#guard (witnesses.filter (fun w => allTargets.any (fun u => u == w))).length == 0
#guard (pool.filter (fun t => !(TM.Term.inT t))).length == 0
-- all three sites: they move, they stay in 𝔗(M), and they go strictly down
#guard (pool.filter (fun t => !(predOr t == t))).length == 39
#guard (pool.filter (fun t => !(predOr t == t) && !(TM.Term.inT (predOr t) && TM.Term.lt (predOr t) t))).length == 0
#guard (pool.filter (fun t => !(omLog t == t))).length == 28
#guard (pool.filter (fun t => !(omLog t == t) && !(TM.Term.inT (omLog t) && TM.Term.lt (omLog t) t))).length == 0
#guard (pool.filter (fun t => !((List.range 3).all (fun i =>
          match fpDeep (ofNat i) t with
          | none => true | some g => TM.Term.inT g && (g == t || TM.Term.lt g t))))).length == 0


/-! ## §15 THE CLAUSE-WISE LANDING THEOREM  (started)

What §14 measures and does not prove:

    ∀ t, inT t → CNV t → every argument `encvF` recurses on is `inT` and `lt t`

**Measured on 169 starts and 40 targets, 0 violations, with the junk control firing at
10 of 42.  NOT PROVED.  "The route is open" is not "the termination is proved"** — the
whole obligation is this theorem, and §13's table is the record that the arithmetic
alternative does not exist rather than that it was not looked for.

**THE SHAPE, NEGOTIATED WITH THE CONSUMER BEFORE ANYTHING WAS PROVED** — which is the
order that matters, since the producer adapting costs one statement and the consumer
adapting costs a proof:

    land_predOr {t} (inT t) (predOr t ≠ t)      : inT (predOr t) ∧ lt (predOr t) t
    land_omLog  {t} (inT t) (the site's guard)  : inT (omLog t)  ∧ lt (omLog t) t
    land_fpDeep {t x} (inT t) (x from fpDeep)   : inT x ∧ lt x t

Per site, one STEP, `lt` strictly, parent as literally passed.  **No `CNV` at the target**
and **no chain clause**: `belowC_step` (WF §15.25) takes a single step and returns carrier
membership, deriving `lt x v` against the ORIGINAL start through `lt_trans_inT`.  §15.2's
depth-≥2 measurement was worth running — it is the step-versus-chain check — and it came
back clean AND provable on the consumer's side, so the obligation is zero.

`CNV` IS REQUIRED ONCE, OF THE BOUND, at the top-level start, which the 169-term pool
satisfies.  **Nothing rests on the 2-mover `CNV`-preservation sample.**  Measured anyway,
since it was free:

**AND THE MIRROR OF THE RULE THIS FILE HAS ENFORCED SIX TIMES, because someone who has
absorbed those refusals will be tempted to trim conclusions by symmetry and the symmetry
is false:**

    STRENGTHENING A HYPOTHESIS narrows, is invisible at the use site, REFUSE IT.
    STRENGTHENING A CONCLUSION is free, and has OPTION VALUE.

An earlier draft of `landing` carried `CNV u` in the CONCLUSION, put there only because the
measurement said it cost nothing.  It turned out to be exactly what the consumer's
`CarrierV` form needed — that carrier does not transport `CNV`, so at a depth-2 step the
theorem's own `CNV t` hypothesis would have been unavailable — and without it the two
pieces would not have composed.  **The consumer then chose the BOUNDED form instead, so the
option was never exercised.**  That is not the rule failing; that is what an option is.  You
cannot know which consumer will need which conclusion, so when a measurement says a stronger
conclusion is free, take it and let the consumer discard it.

                          movers   `CNV` lost   `RT`-step failed
        predOr              39          0              0
        omLog               28          0              0
        fpDeep              24          0              0
        summands             —          0              0

**`CNV` survives every site.**  veblen2's own evidence was 2 movers from filtering; the
call graph gives 39, 28 and 24, on the sample that actually arises.  It is recorded rather
than relied on.

**AND `targets` IS A MEASUREMENT SCAFFOLD, NOT A STEP IN THE ARGUMENT.**  It is eyeballed
against §10's three equations and over-approximates; that caveat looks like an open hole in
the trusted path and is not one.  When `encv'` is defined by well-founded recursion, **Lean
generates a decrease obligation at each ACTUAL recursive call, from the syntax of the
definition** — not from `targets`.  If `targets` over-approximates, the extra entries were
only ever measured and go unused; **if it MISSED a call, the definition does not elaborate**
— loudly, not silently.  Its job was to say in advance whether those obligations would be
dischargeable, which is what it did.  The trusted statement is `landing`, and that is a
theorem.

FOUR CLAUSES, one per recursion site of §10's named equations:

    the summands   g ∈ summands (splitFin b).1        →  inT g,  lt g (φ̄(a,b))
    the head       (summands (splitFin b).1).headD 0  →  same
    predOr         predOr a                            →  inT,  lt · (φ̄(a,b))
    omLog          omLog g for a summand g             →  same
    fpDeep         fpDeep a hd = some z                →  inT z, lt z (φ̄(a,b))

`predOr`'s case is pre-cleared by veblen2's measurement (0 violations, `inT` and `CNV`
preserved, full `RT`-step on their 5 movers, thickened to 39 by §14.1's call graph) —
measured, not proved.

PROVED SO FAR: `inT` passes to the summands, structurally, the same shape as
`tdepth_mem_summands`.  The `add` case reads `inT (u ⊕ v) = isAP u && inT u && inT v && …`
straight off 2.1(iii) and takes the two conjuncts it needs. -/

theorem inT_mem_summands : ∀ (t g : Term),
    TM.Term.inT t = true → g ∈ summands t → TM.Term.inT g = true := by
  intro t
  induction t with
  | zero => intro g _ hg; simp only [summands] at hg; exact absurd hg (List.not_mem_nil)
  | M => intro g h hg; simp only [summands, List.mem_singleton] at hg; rw [hg]; exact h
  | omg _ _ => intro g h hg; simp only [summands, List.mem_singleton] at hg; rw [hg]; exact h
  | psi _ _ _ _ => intro g h hg; simp only [summands, List.mem_singleton] at hg; rw [hg]; exact h
  | Z _ _ => intro g h hg; simp only [summands, List.mem_singleton] at hg; rw [hg]; exact h
  | phi _ _ _ _ => intro g h hg; simp only [summands, List.mem_singleton] at hg; rw [hg]; exact h
  | add u v ihu ihv =>
    intro g h hg
    simp only [summands, List.mem_append] at hg
    have hd : TM.Term.inT u = true ∧ TM.Term.inT v = true := by
      simp only [TM.Term.inT, Bool.and_eq_true] at h
      exact ⟨h.1.1.2, h.1.2⟩
    rcases hg with hh | hh
    · exact ihu g hd.1 hh
    · exact ihv g hd.2 hh


def cnvPool : List Term := pool.filter (fun t => Evidence.WF.CNV t)

#guard cnvPool.length == 169
#guard (cnvPool.filter (fun t => !(predOr t == t))).length == 39
#guard (cnvPool.filter (fun t => !(predOr t == t) && !(Evidence.WF.CNV (predOr t)))).length == 0
#guard (cnvPool.filter (fun t => !(omLog t == t))).length == 28
#guard (cnvPool.filter (fun t => !(omLog t == t) && !(Evidence.WF.CNV (omLog t)))).length == 0
#guard (cnvPool.filter (fun t => !((List.range 3).all (fun i =>
          match fpDeep (ofNat i) t with | none => true | some g => Evidence.WF.CNV g)))).length == 0
#guard (cnvPool.filter (fun t =>
          !((summands (TM.Term.splitFin t).1).all (fun g =>
              Evidence.WF.CNV g && TM.Term.inT g)))).length == 0


/-! ### §15.1 `inT` UNDER `ofList ∘ take` — measured, and the proof's shape

The summands clause needs `inT ((splitFin b).1)`, and `(splitFin b).1` is
`ofList ((toList b).take j)`.  Measured before attempting, over 221 `inT` terms of
`startsW ++ junk`:

    inT b → inT (ofList ((toList b).take k)),  k ≤ 5      0 violations of 221
    the same for CNV                                       0 violations
    CONTROL: from the 42 NON-`inT` terms                  38 FAIL

**The hypothesis is load-bearing, not decoration** — without `inT b` the conclusion is
false on 38 of 42, which is the shape a corpus of legal terms alone could never have shown.

THE PROOF, by the house technique (induct on the TERM): `zero` and the five leaves close,
and so does the `add` case when the prefix is empty — `ofList [u] = u`, and `inT u` is the
second conjunct of 2.1(iii).  **What remains is the non-empty prefix**, where the goal is
2.1(iii) for `add u (ofList (y :: ys))` and the fourth conjunct needs the head `y` to be
additively principal and `≤ u`.  That is exactly what `inT (add u v)`'s own fourth conjunct
says about `v`'s head, and `y` IS `v`'s head — the bookkeeping is relating `take`'s first
element to `toList v`'s first element through the `cases` on `v`.

Not in the file until it closes; the measurement is.

**STATE OF THE PROOF (2026-08-10).**  `head_of_take` below is proved and is the bookkeeping
that relates `take`'s first element to `toList v`'s.  With it, the `add` case's structure is
complete: the `hyu` derivation — `y` additively principal and `≤ u` — closes in all six
sub-cases of `v`, reading 2.1(iii)'s fourth conjunct in the `add` case and its `isAP v && le v u`
form in the five leaf cases.

**AND IT CLOSED THE MOMENT THE CATEGORY CHANGED.**  Four attempts failed the same way:
`simp only [TM.Term.inT]` unfolds the INNER `inT y` as well as the outer so the hypothesis
stops matching, and a `show` cannot state the goal uniformly because 2.1(iii)'s fourth
conjunct branches on whether the tail is an `add`.  **Four tactic variations, one category —
"the goal's shape is not uniform" — and the rule says suspect the category after ONE.**  The
fix is the INTRODUCTION LEMMAS below, doing that case analysis once where the shape is known
rather than at every use:

    inT_add_intro      isAP u → inT u → inT y → isAP y → le y u → inT (u ⊕ y)
    inT_add_intro_add  isAP u → inT u → inT (y ⊕ z) → le y u → inT (u ⊕ (y ⊕ z))

The first kills the `add` case of `y` from `isAP y`; the second is 2.1(iii) read directly,
where the fourth conjunct is `le y u` with no branch.  With them, both branches of
`inT_ofList_take` are one `exact`. -/

theorem head_of_take {l : List Term} {j : Nat} {y : Term} {ys : List Term}
    (h : l.take j = y :: ys) : ∃ rest, l = y :: rest := by
  cases j with
  | zero => simp only [List.take_zero] at h; exact absurd h (by simp)
  | succ i =>
    cases l with
    | nil => simp only [List.take_nil] at h; exact absurd h (by simp)
    | cons z rest =>
      simp only [List.take_succ_cons] at h
      injection h with h1 _
      exact ⟨rest, by rw [h1]⟩

def inTpool : List Term := (startsW ++ junk).eraseDups

#guard ((inTpool.filter (fun t => TM.Term.inT t)).filter (fun t =>
          !((List.range 6).all (fun k => TM.Term.inT (ofList ((toList t).take k)))))).length == 0
#guard ((inTpool.filter (fun t => Evidence.WF.CNV t)).filter (fun t =>
          !((List.range 6).all (fun k => Evidence.WF.CNV (ofList ((toList t).take k)))))).length == 0
#guard ((inTpool.filter (fun t => !(TM.Term.inT t))).filter (fun t =>
          !((List.range 6).all (fun k => TM.Term.inT (ofList ((toList t).take k)))))).length == 38


/-! ### §15.2 THE CHAIN, MEASURED DIRECTLY — not step-by-step

veblen2's caution, and it is the sharpest of the exchange: `landing` gives `lt u t` for each
STEP, while `belowC_step` needs `lt u r` against the FIXED START.  Transitivity supplies it
— but **"a property measured on single steps and claimed for a chain" is the same shape of
error as "measured on a domain and claimed for what is reachable", which has cost this file
twice.**  So it is measured directly.

    169 starts | 40 distinct targets | 24 of them at DEPTH ≥ 2
    starts that actually HAVE a depth-≥2 target        145 of 169
    depth-≥2 targets failing `lt u start`                0
    depth-≥2 targets failing `inT u`                     0

**Not vacuous**: 145 of the 169 starts have a depth-≥2 target, up to 4 each.  The chain
property is measured as a chain, against the literal starting term, not inferred from the
steps.

**AND IT IS INSURANCE THAT TURNED OUT NOT TO BE NEEDED, NOT EVIDENCE THAT IS BEING USED.**
`belowC_step` takes a SINGLE step and derives `lt x v` against the original start itself,
through `lt_trans_inT` — so there is no chain obligation on this side and this measurement
discharges nothing.  **It is kept, labelled, rather than deleted**: the next person will
otherwise wonder whether a chain clause is owed and re-derive that it is not.  What it was
worth was the check itself — "measured on steps, claimed for chains" is the shape that has
cost this file twice, and it cost one `#eval` to rule out here. -/

def targets1F : Term → List Term
  | .add u v => [u, v]
  | .phi a b =>
      let gs := summands (TM.Term.splitFin b).1
      let hd := gs.headD zero
      (if a == zero then [] else [predOr a])
      ++ gs.map (fun g => if a == zero then g else omLog g)
      ++ [hd]
      ++ (match fpDeep a hd with | some z => [z] | none => [])
  | _ => []

def targets1 (t : Term) : List Term := (targets1F t).eraseDups

def deepTargets (t : Term) : List Term :=
  (targets t).filter (fun u => !((targets1 t).any (fun v => v == u)))

#guard (startsW.flatMap deepTargets).eraseDups.length == 24
#guard (startsW.filter (fun t => !((deepTargets t).isEmpty))).length == 145
#guard (startsW.filter (fun t => !((deepTargets t).all (fun u => TM.Term.lt u t)))).length == 0
#guard (startsW.filter (fun t => !((deepTargets t).all (fun u => TM.Term.inT u)))).length == 0



theorem inT_add_intro {u y : Term} (hu : TM.Term.isAP u = true) (hiu : TM.Term.inT u = true)
    (hiy : TM.Term.inT y = true) (hay : TM.Term.isAP y = true) (hle : TM.Term.le y u = true) :
    TM.Term.inT (TM.Term.add u y) = true := by
  cases y with
  | add c d => simp only [TM.Term.isAP] at hay; exact absurd hay (by simp)
  | zero => simp only [TM.Term.isAP] at hay; exact absurd hay (by simp)
  | M => show (TM.Term.isAP u && TM.Term.inT u && TM.Term.inT TM.Term.M &&
               (TM.Term.isAP TM.Term.M && TM.Term.le TM.Term.M u)) = true
         rw [hu, hiu, hiy, hay, hle]; rfl
  | omg a => show (TM.Term.isAP u && TM.Term.inT u && TM.Term.inT (TM.Term.omg a) &&
               (TM.Term.isAP (TM.Term.omg a) && TM.Term.le (TM.Term.omg a) u)) = true
             rw [hu, hiu, hiy, hay, hle]; rfl
  | psi a b => show (TM.Term.isAP u && TM.Term.inT u && TM.Term.inT (TM.Term.psi a b) &&
               (TM.Term.isAP (TM.Term.psi a b) && TM.Term.le (TM.Term.psi a b) u)) = true
               rw [hu, hiu, hiy, hay, hle]; rfl
  | Z a => show (TM.Term.isAP u && TM.Term.inT u && TM.Term.inT (TM.Term.Z a) &&
               (TM.Term.isAP (TM.Term.Z a) && TM.Term.le (TM.Term.Z a) u)) = true
           rw [hu, hiu, hiy, hay, hle]; rfl
  | phi a b => show (TM.Term.isAP u && TM.Term.inT u && TM.Term.inT (TM.Term.phi a b) &&
               (TM.Term.isAP (TM.Term.phi a b) && TM.Term.le (TM.Term.phi a b) u)) = true
               rw [hu, hiu, hiy, hay, hle]; rfl

theorem inT_add_intro_add {u y z : Term} (hu : TM.Term.isAP u = true)
    (hiu : TM.Term.inT u = true) (hiyz : TM.Term.inT (TM.Term.add y z) = true)
    (hle : TM.Term.le y u = true) :
    TM.Term.inT (TM.Term.add u (TM.Term.add y z)) = true := by
  show (TM.Term.isAP u && TM.Term.inT u && TM.Term.inT (TM.Term.add y z) && TM.Term.le y u) = true
  rw [hu, hiu, hiyz, hle]; rfl

/-- **`inT` SURVIVES `ofList ∘ take`** — the summands clause's first half. -/
theorem inT_ofList_take : ∀ (b : Term) (k : Nat),
    TM.Term.inT b = true → TM.Term.inT (ofList ((toList b).take k)) = true := by
  intro b
  induction b with
  | zero => intro k _; simp only [toList, List.take_nil, ofList]; rfl
  | M => intro k h; cases k <;> simp only [toList, List.take, List.take_nil, ofList] <;> first | rfl | exact h
  | omg _ _ => intro k h; cases k <;> simp only [toList, List.take, List.take_nil, ofList] <;> first | rfl | exact h
  | psi _ _ _ _ => intro k h; cases k <;> simp only [toList, List.take, List.take_nil, ofList] <;> first | rfl | exact h
  | Z _ _ => intro k h; cases k <;> simp only [toList, List.take, List.take_nil, ofList] <;> first | rfl | exact h
  | phi _ _ _ _ => intro k h; cases k <;> simp only [toList, List.take, List.take_nil, ofList] <;> first | rfl | exact h
  | add u v _ ihv =>
    intro k h
    simp only [TM.Term.inT, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hap, hiu⟩, hiv⟩, hlast⟩ := h
    cases k with
    | zero => simp only [toList, List.take_zero, ofList]; rfl
    | succ j =>
      simp only [toList, List.take_succ_cons]
      cases hL : (toList v).take j with
      | nil => simp only [ofList]; exact hiu
      | cons y ys =>
        have hiy : TM.Term.inT (ofList (y :: ys)) = true := by
          have := ihv j hiv; rwa [hL] at this
        obtain ⟨rest, hv⟩ := head_of_take hL
        have hyu : TM.Term.isAP y = true ∧ TM.Term.le y u = true := by
          cases v with
          | zero => simp only [toList] at hv; exact absurd hv (by simp)
          | add c d =>
            simp only [toList] at hv
            injection hv with h1 _
            subst h1
            refine ⟨?_, hlast⟩
            simp only [TM.Term.inT, Bool.and_eq_true] at hiv
            exact hiv.1.1.1
          | M => simp only [toList] at hv; injection hv with h1 _; subst h1
                 simp only [Bool.and_eq_true] at hlast; exact hlast
          | omg _ => simp only [toList] at hv; injection hv with h1 _; subst h1
                     simp only [Bool.and_eq_true] at hlast; exact hlast
          | psi _ _ => simp only [toList] at hv; injection hv with h1 _; subst h1
                       simp only [Bool.and_eq_true] at hlast; exact hlast
          | Z _ => simp only [toList] at hv; injection hv with h1 _; subst h1
                   simp only [Bool.and_eq_true] at hlast; exact hlast
          | phi _ _ => simp only [toList] at hv; injection hv with h1 _; subst h1
                       simp only [Bool.and_eq_true] at hlast; exact hlast
        cases ys with
        | nil =>
          simp only [ofList] at hiy ⊢
          exact inT_add_intro hap hiu hiy hyu.1 hyu.2
        | cons w ws =>
          simp only [ofList] at hiy ⊢
          exact inT_add_intro_add hap hiu hiy hyu.2


/-! ### §15.3 THE `lt` HALF — the sub-term facts every site needs, measured

Each `land_*` theorem's second conjunct is `lt <target> <parent as passed>`, and the parent
is the `φ̄(a,b)` the recursion was called on, not the site's own argument.  So every site
needs the sub-term facts first.  Over the 97 `φ̄`-headed terms of `startsW`:

    lt a (φ̄(a,b))                                      0 violations
    lt b (φ̄(a,b))                                      0 violations
    lt (predOr a) (φ̄(a,b))     where `predOr` moves    0 of 51
    lt g (φ̄(a,b))              g a summand of `(splitFin b).1`   0
    lt (omLog g) (φ̄(a,b))      same g                            0

**The first two are what the other three reduce to**: `lt (predOr a) a` composed with
`lt a (φ̄(a,b))` through `lt_trans_inT`, and likewise for the subscript side.

**AND ONE OF THE TWO IS ALREADY PROVED, THE OTHER IS NOT AND IS NOT MINE.**

  * SUBSCRIPT SIDE — `Evidence.WF.lt_phi_self (hx : CNV x) (u) : lt x (φ̄(u,x))`, WF §15.5.
    Exactly `lt b (φ̄(a,b))`, for every first argument, on all of `CNV`.  Available.
  * FIRST-ARGUMENT SIDE — `lt a (φ̄(a,b))` does NOT follow from what exists.
    `lt_phi_of_le` gives `lt x (φ̄(u,y))` from `le x y`, which here would need `le a b` —
    false in general (`φ̄(1,0)`: `a = 1`, `b = 0`).  Measured true at 0 of 97, but it is an
    ORDER fact about the Veblen hierarchy — "the value at level `a` exceeds `a`" — and
    order theory is the WF lane's, not this file's.

So the `lt` half is one available lemma and one routed request, rather than five clauses. -/

def phis : List (Term × Term) :=
  startsW.filterMap (fun t => match t with | .phi a b => some (a, b) | _ => none)

#guard phis.length == 97
#guard (phis.filter (fun p => !(TM.Term.lt p.1 (TM.Term.phi p.1 p.2)))).length == 0
#guard (phis.filter (fun p => !(TM.Term.lt p.2 (TM.Term.phi p.1 p.2)))).length == 0
#guard (phis.filter (fun p => !(predOr p.1 == p.1)
          && !(TM.Term.lt (predOr p.1) (TM.Term.phi p.1 p.2)))).length == 0
#guard (phis.filter (fun p => !(predOr p.1 == p.1))).length == 51
#guard (phis.filter (fun p => !((summands (TM.Term.splitFin p.2).1).all
          (fun g => TM.Term.lt g (TM.Term.phi p.1 p.2))))).length == 0
#guard (phis.filter (fun p => !((summands (TM.Term.splitFin p.2).1).all
          (fun g => TM.Term.lt (omLog g) (TM.Term.phi p.1 p.2))))).length == 0


/-! ### §15.4 `land_predOr`'s `inT` HALF — measured, with a control that fires on everything

`predOr t` is `plus ((splitFin t).1) (ofNat m)` when the finite part is `m+1`, so the site's
`inT` half is `inT_ofList_take` (proved, §15.1) composed with one `plus` fact.  Measured over
the 221 `inT` terms of `pool ++ junk`:

    inT g → inT (plus g (ofNat m)),  m ≤ 4         0 violations of 221
    inT ((splitFin t).1)                            0            (agrees with §15.1)
    inT t → inT (predOr t)                          0            the site itself
    CONTROL: the same from NON-`inT` g            42 of 42 FAIL

**The control fires on every member** — not most, all.  A hypothesis whose removal breaks
the conclusion on 100% of a 42-term class is as load-bearing as a hypothesis gets, and it is
the sharpest control in this file.  It is also the second time the junk corpus has been the
RIGHT corpus for a control while being the wrong one for a claim: a corpus of legal terms
cannot contain a single witness for either.

**AND THE CORPUS WAS NEVER THE ERROR; THE ROLE WAS.**  The 263-term junk corpus was the
wrong instrument for claims about what `encvF` meets (§14: 0 of 13 witnesses arise) and is
the RIGHT one for controls, twice — 38 of 42 at §15.1 and 42 of 42 here.  A corpus of legal
terms cannot contain a single witness for either control.  Both roles are now serving.

WHAT REMAINS FOR THIS SITE, AND IT REDUCES TO TWO ONE-STEP FACTS.  Measured over the same
221 `inT` terms before designing anything:

    plus g (ofNat (m+1)) = plus (plus g (ofNat m)) one        0 violations of 221
    inT s → inT (plus s one)                                  0 violations
    CONTROL: the second from NON-`inT` s                     37 of 42 FAIL

**So the `m`-indexed fact is an induction on `m` over a single-step lemma**, rather than a
statement about `ofList` of a filtered list with an appended tail.  That is the third time
a per-site obligation has collapsed to one shared fact plus a step, and the second time
measuring the recursion first turned a list-shaped problem into a numeric one.

**AND THAT IS A DIFFERENT RULE FROM THE MEASURE-FIRST ONE THIS FILE HAS BEEN APPLYING.**
Measure-first is about not building the wrong design: measure, then decide.  This is stronger —
**measuring the recursion does not only CONFIRM which shape the problem has, it can CHANGE it.**
I had budgeted an `ofList`-of-a-filtered-list-with-an-appended-tail problem and measured my way to
an induction on a natural number.  The first rule avoids a wrong answer; this one finds a CHEAPER
QUESTION than the one you were about to answer, and the two are worth keeping apart because the
second only pays off if you measure BEFORE designing rather than before building. -/

def gpool : List Term := (pool ++ junk).eraseDups

#guard ((gpool.filter (fun t => TM.Term.inT t)).filter (fun g =>
          !((List.range 5).all (fun m => TM.Term.inT (TM.Term.plus g (ofNat m)))))).length == 0
#guard ((gpool.filter (fun t => !(TM.Term.inT t))).filter (fun g =>
          !((List.range 5).all (fun m => TM.Term.inT (TM.Term.plus g (ofNat m)))))).length == 42
#guard (gpool.filter (fun t => !(TM.Term.inT t))).length == 42
#guard ((gpool.filter (fun t => TM.Term.inT t)).filter (fun t =>
          !(TM.Term.inT (predOr t)))).length == 0


#guard ((gpool.filter (fun t => TM.Term.inT t)).filter (fun g =>
          !((List.range 4).all (fun m =>
             TM.Term.plus g (ofNat (m+1)) == TM.Term.plus (TM.Term.plus g (ofNat m)) one)))).length == 0
#guard ((gpool.filter (fun t => TM.Term.inT t)).filter (fun s =>
          !(TM.Term.inT (TM.Term.plus s one)))).length == 0
#guard ((gpool.filter (fun t => !(TM.Term.inT t))).filter (fun s =>
          !(TM.Term.inT (TM.Term.plus s one)))).length == 37

/-! ### §15.5 `land_predOr` — BOTH HALVES PROVED, AND THE INTERFACE FINDING THAT CAME WITH THEM

**THE FINDING FIRST, BECAUSE IT IS A STRENGTHENED HYPOTHESIS AND THOSE GET REPORTED, NOT TAKEN.**
§15.3 routed `lt a (φ̄(a,b))` to the WF lane and it came back (`Evidence.WF.lt_phi_fst`, WF §15.26),
together with `lt_phi_of_le_fst`.  Both are `CNV`-GATED, and so is §15.5's `lt_phi_self`:

    lt_phi_self       (hx : CNV x)                         : lt x (φ̄(u,x))
    lt_phi_fst        (ha : CNV a)                         : lt a (φ̄(a,b))
    lt_phi_of_le_fst  (hx : CNV x) (ha : CNV a) (le x a)   : lt x (φ̄(a,b))

So `land_predOr`'s `lt` half needs `CNV` AT THE PARENT.  §15's negotiated shape has `inT t`, and
the `BelowC` carrier transports `inT t` and `lt t v` and NOT `CNV t` — so at a depth-2 step the
hypothesis is not there.  **The bounded form and the `lt` half do not compose** — or so it
looked.  That is a hypothesis strengthening on an interface the consumer already accepted, so it
went to veblen2 as a request rather than being taken.  Nothing here depended on the answer:
`lt (predOr a) a` is needed under every option.

**RESOLVED, AND NOT THE WAY EITHER LANE EXPECTED: THE PREMISE WAS FALSE.**  `cnv_of_lt_cnv`
(below) gives `CNV` on `BelowC` for free, so the `lt` half composes there after all and the
interface stands unchanged.  The carrier did move to `CarrierV` in the end — but for a
STRUCTURAL reason that has nothing to do with this paragraph: `encv'` recurses with no external
ceiling, so a bounded carrier would make it invent a `v` and thread `lt s v` through every clause
for nothing.  **Two different questions with two different answers**, which is why the file keeps
both rather than editing one into the other.  Not taking the strengthened hypothesis myself is
what left room for both answers to be found.

**AND I DID NOT ASSUME THE `inT` ANALOGUES ARE FALSE — I MEASURED THEM.**  The corpora hold
exactly ONE `inT`-non-`CNV` `φ̄`-headed term, so the class was GENERATED for the purpose rather
than sieved, which is the rule §15.25 states in WF and which this file has now used three times:

    generated `inT`-non-`CNV` `φ̄` terms                        40
    of those, `lt b (φ̄(a,b))` fails on                          0
    of those, `lt a (φ̄(a,b))` fails on                          0

They are TRUE and they do not EXIST.  So it is a cost question, not a truth question, and the
recommendation sent with it was `CNV` — not from preference but because **the repo's machinery is
all on the `CNV` side**: `plus_one_eq_succT`, `lt_succT`, `cnv_succT` (WF 11367 / 11920 / 11956)
are what turn both halves below into three lines, and the `inT` side has no `succT` chain at all.

**THE THIRD OPTION — AND IT WAS ALREADY A THEOREM, WHICH IS WHY THE INTERFACE NEVER CHANGED.**
I conjectured that `inT t → CNV v → lt t v → CNV t` would make the question disappear, and
measured it.  It is `Evidence.WF.cnv_of_lt_cnv` (WF §15.1), character for character, proved long
before I asked, and `cnv_of_belowC` is the accessor veblen2 named on top of it.  **So `CNV` is
FREE on `BelowC`, both A and B collapse, and the negotiated `inT` interface never had to move.**

**AND MY MEASUREMENT WAS VACUOUS — recorded because the number reads clean and is not.**

    generated `inT`-non-`CNV` terms   63  ×  `CNV` bounds  172   =  10836 pairs
    pairs with `lt t v`                                              0     ← ANTECEDENT count

Zero violations because **zero instances**.  The antecedent never fires, so the implication was
not confirmed on 10836 cases; there were no cases.  Under the control discipline this file
enforces — a test that only ever returns negatives is indistinguishable from one that always
returns false — it would need a positive control, and **no positive control can exist, because
`cnv_of_lt_cnv` forbids the instances one would need.**  THE VACUITY WAS THE THEOREM SHOWING
THROUGH THE MEASUREMENT.

THE DISCRIMINATOR, now `plan/constitutions.md` C4, because "0 violations" reads identically in the good
branch and the worthless one:

    on a vacuous result, ask whether THE VACUITY IS ITSELF PROVABLE
      provable  → the measurement confirmed a theorem, and no positive control can exist
      not       → the test is broken or the corpus cannot reach the case, and you know NOTHING;
                  report "my corpus cannot reach this", never "measured clean"

This is the good branch.  The targeted probes — `ψ_{Z0}(0)`, `ψ_{Z1}(0)`, `ψ_{Z(Z0)}(0)`, `Z0`,
`Z1`, `Zω`, none below `φ̄(1,0)` or `φ̄(φ̄(1,0),0)` — were me reading the theorem off the corpus
without knowing it was a theorem.  **What the route was worth is that conjecturing the statement
and measuring it FOUND a theorem no search phrased from my problem would have surfaced**:
`cnv_of_lt_cnv` does not read like an answer to "is `CNV` free on my carrier".  That works even
when the fact is not in the file, which is why it beat both lanes' greps.

**WHAT THE MEASUREMENT POINTED AT, AND WHAT THE PROOF ACTUALLY DID — they are not the same, and
the difference is worth recording.**  The measurement that opened the route was that `predOr`
IS the repo's own structural predecessor:

    `predOr t ≠ t`  ↔  `kindV t`                    0 violations of 169 + 215 `CNV` terms
    `predOr t = predC t`  where `kindV t`           0 violations of 39 + 40

That said "reuse `succT_predC`".  The proof below does NOT use `predC` — `succT (predOr t) = t`
comes out directly from `splitFin_rebuild`, so the bridge lemma was never needed.  The guards stay
as an independent cross-check that my `predOr` and WF's `predC` agree where both are defined; what
the measurement bought was the STRUCTURE (`predOr` is a successor's predecessor), not the route.

THE CHAIN, and every step of it is a fact about `plus`/`toList`, not about the order:

    trailing_ones            the trailing `1`s of a component list split off  (pure `List`)
    cnv_toList_isAP          every component of a `CNV` term is additively principal
    ofList_toList_cnv        `ofList` inverts `toList` on `CNV`
    cnv_ofList_take          §15.1's measurement, `CNV` side — and EASIER than the `inT` side,
                             because `CNV`'s `add` clause is uniform where 2.1(iii) branches
    plus_ofNat_spec          `plus g (ofNat m)` is `CNV` and its list is `toList g ++ 1ᵐ`
    plus_ofNat_step          `plus g (ofNat (m+1)) = succT (plus g (ofNat m))`  ← §15.4's fact
    splitFin_rebuild         `plus (splitFin t).1 (ofNat (splitFin t).2) = t`
    succT_predOr             `succT (predOr t) = t` when the finite part is a successor
    cnv_predOr / lt_predOr   the two halves

**§15.4's two measured facts are `plus_ofNat_step` and `plus_ofNat_spec.1`, and both are proved.**
The `m`-indexed one is the induction §15.4 predicted; the single step is `ofList_toList_snoc`. -/

section
open Evidence.WF (CNV cnv_add succT cnv_succT lt_succT plus_ofNat_succ toList_ofNat
  ofList_toList_snoc toList_ne_nil hdLe hdOf hdLe_eq hdLe_of_isAP)

/-- The trailing `1`s of a component list split off cleanly.  Pure `List`, no term content —
    it is the only place `splitFin`'s `takeWhile` has to be unfolded. -/
theorem trailing_ones : ∀ (r : List Term),
    (r.dropWhile (fun x => x == one)).reverse
      ++ List.replicate ((r.takeWhile (fun x => x == one)).length) one = r.reverse := by
  intro r
  induction r with
  | nil => rfl
  | cons a t ih =>
    by_cases h : (a == one) = true
    · have ha : a = one := by simpa using h
      rw [List.dropWhile_cons_of_pos (p := fun x => x == one) h,
          List.takeWhile_cons_of_pos (p := fun x => x == one) h,
          List.length_cons, List.replicate_succ', ← List.append_assoc, ih,
          List.reverse_cons, ha]
    · rw [List.dropWhile_cons_of_neg (p := fun x => x == one) (by simpa using h),
          List.takeWhile_cons_of_neg (p := fun x => x == one) (by simpa using h),
          List.length_nil, show List.replicate 0 one = [] from rfl, List.append_nil]

/-- Every component of a `CNV` term is additively principal. -/
theorem cnv_toList_isAP : ∀ (t : Term), CNV t = true → ∀ x ∈ toList t, x.isAP = true := by
  intro t
  induction t with
  | zero => intro _ x hx; simp only [toList] at hx; exact absurd hx (List.not_mem_nil)
  | M => intro h _ _; exact Bool.noConfusion h
  | omg _ _ => intro h _ _; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h _ _; exact Bool.noConfusion h
  | Z _ _ => intro h _ _; exact Bool.noConfusion h
  | phi p q _ _ => intro _ x hx; simp only [toList, List.mem_singleton] at hx; rw [hx]; rfl
  | add c d _ ihd =>
    intro h x hx
    obtain ⟨hAPc, _, hcnd, _⟩ := cnv_add h
    simp only [toList, List.mem_cons] at hx
    rcases hx with hx | hx
    · rw [hx]; exact hAPc
    · exact ihd hcnd x hx

/-- `ofList` inverts `toList` on `CNV`.  (`add u 0` is the counterexample off `CNV`.) -/
theorem ofList_toList_cnv : ∀ (t : Term), CNV t = true → ofList (toList t) = t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | phi _ _ _ _ => intro _; rfl
  | add c d _ ihd =>
    intro h
    obtain ⟨_, _, hcnd, hdesc⟩ := cnv_add h
    have hdz : d ≠ zero := by intro hc; rw [hc] at hdesc; exact Bool.noConfusion hdesc
    have hne := toList_ne_nil d hcnd hdz
    show ofList (c :: toList d) = TM.Term.add c d
    cases hl : toList d with
    | nil => exact absurd hl hne
    | cons e rest =>
      show TM.Term.add c (ofList (e :: rest)) = TM.Term.add c d
      rw [← hl, ihd hcnd]

theorem cnv_add_intro {u y : Term} (hu : u.isAP = true) (hcu : CNV u = true)
    (hcy : CNV y = true) (hhd : hdLe y u = true) : CNV (TM.Term.add u y) = true := by
  show (u.isAP && CNV u && CNV y && hdLe y u) = true
  rw [hu, hcu, hcy, hhd]; rfl

/-- The head of a component list IS the term's head component. -/
theorem hdOf_of_toList : ∀ {d e : Term} {rst : List Term},
    toList d = e :: rst → hdOf d = e := by
  intro d e rst h
  cases d with
  | zero => exact absurd h (by simp [toList])
  | add a b => injection h with h1 _
  | M => injection h with h1 _
  | omg _ => injection h with h1 _
  | psi _ _ => injection h with h1 _
  | Z _ => injection h with h1 _
  | phi _ _ => injection h with h1 _

theorem hdLe_ofList_cons {e : Term} (he : e.isAP = true) (rest : List Term) (c : Term) :
    hdLe (ofList (e :: rest)) c = TM.Term.le e c := by
  cases rest with
  | nil => exact hdLe_of_isAP he c
  | cons w ws => rfl

/-- **`CNV` SURVIVES `ofList ∘ take`** — §15.1's measurement, on the `CNV` side.  ONE
    introduction lemma suffices where the `inT` side needed two, because `CNV`'s `add` clause
    does not branch on the tail's shape. -/
theorem cnv_ofList_take : ∀ (b : Term) (k : Nat),
    CNV b = true → CNV (ofList ((toList b).take k)) = true := by
  intro b
  induction b with
  | zero => intro k _; simp only [toList, List.take_nil, ofList]; rfl
  | M => intro _ h; exact Bool.noConfusion h
  | omg _ _ => intro _ h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro _ h; exact Bool.noConfusion h
  | Z _ _ => intro _ h; exact Bool.noConfusion h
  | phi p q _ _ =>
    intro k h
    cases k <;> simp only [toList, List.take, List.take_nil, ofList] <;> first | rfl | exact h
  | add c d _ ihd =>
    intro k h
    obtain ⟨hAPc, hcnc, hcnd, hdesc⟩ := cnv_add h
    cases k with
    | zero => simp only [toList, List.take_zero, ofList]; rfl
    | succ j =>
      simp only [toList, List.take_succ_cons]
      cases hL : (toList d).take j with
      | nil => simp only [ofList]; exact hcnc
      | cons e rest =>
        have hce : CNV (ofList (e :: rest)) = true := by
          have := ihd j hcnd; rwa [hL] at this
        obtain ⟨rst, hd⟩ := head_of_take hL
        have hdz : d ≠ zero := by
          intro hc; rw [hc] at hd; simp only [toList] at hd; exact absurd hd (by simp)
        have hhd : hdOf d = e := hdOf_of_toList hd
        have hec : TM.Term.le e c = true := by
          rw [hdLe_eq d c hdz, hhd] at hdesc; exact hdesc
        have heAP : e.isAP = true := by
          have : e ∈ toList d := by rw [hd]; exact List.mem_cons_self
          exact cnv_toList_isAP d hcnd e this
        exact cnv_add_intro hAPc hcnc hce (by rw [hdLe_ofList_cons heAP rest c]; exact hec)

/-- `plus g (ofNat m)` is `CNV`, and its component list is `toList g` with `m` ones appended. -/
theorem plus_ofNat_spec : ∀ (g : Term), CNV g = true → ∀ m,
    CNV (plus g (ofNat m)) = true ∧
      toList (plus g (ofNat m)) = toList g ++ List.replicate m one := by
  intro g hg m
  induction m with
  | zero => exact ⟨hg, (List.append_nil _).symm⟩
  | succ m ih =>
    have hEq : plus g (ofNat (m + 1)) = ofList (toList g ++ List.replicate (m + 1) one) := by
      rw [plus_ofNat_succ g hg m, toList_ofNat (m + 1)]
    have hAP : ∀ x ∈ toList g ++ List.replicate (m + 1) one, x.isAP = true := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact cnv_toList_isAP g hg x h
      · rw [List.eq_of_mem_replicate h]; rfl
    have hSucc : plus g (ofNat (m + 1)) = succT (plus g (ofNat m)) := by
      rw [← ofList_toList_snoc (plus g (ofNat m)) ih.1, ih.2, hEq,
          List.append_assoc, ← List.replicate_succ']
    exact ⟨by rw [hSucc]; exact cnv_succT _ ih.1, by rw [hEq, TM.Term.toList_ofList hAP]⟩

/-- **§15.4'S `m`-INDEXED FACT** — the induction it predicted, over `ofList_toList_snoc`. -/
theorem plus_ofNat_step (g : Term) (hg : CNV g = true) (m : Nat) :
    plus g (ofNat (m + 1)) = succT (plus g (ofNat m)) := by
  have ih := plus_ofNat_spec g hg m
  rw [← ofList_toList_snoc (plus g (ofNat m)) ih.1, ih.2,
      plus_ofNat_succ g hg m, toList_ofNat (m + 1), List.append_assoc, ← List.replicate_succ']

theorem take_of_append_replicate {X : List Term} {k : Nat} {l : List Term}
    (h : X ++ List.replicate k one = l) : l.take (l.length - k) = X := by
  subst h
  rw [List.length_append, List.length_replicate,
      show X.length + k - k = X.length from by omega, List.take_left]

/-- `splitFin`'s first component, as a `dropWhile` on the reversed component list. -/
theorem splitFin_fst (t : Term) :
    (TM.Term.splitFin t).1
      = ofList (((toList t).reverse.dropWhile (fun x => x == one)).reverse) := by
  have hF1 : ((toList t).reverse.dropWhile (fun x => x == one)).reverse
      ++ List.replicate (((toList t).reverse.takeWhile (fun x => x == one)).length) one
      = toList t := by
    have h := trailing_ones (toList t).reverse
    rwa [List.reverse_reverse] at h
  show ofList ((toList t).take
      ((toList t).length - ((toList t).reverse.takeWhile (fun x => x == one)).length)) = _
  rw [take_of_append_replicate hF1]

/-- **`splitFin` REBUILDS ITS ARGUMENT** — `t = γ + m` for `(γ, m) = splitFin t`. -/
theorem splitFin_rebuild (t : Term) (ht : CNV t = true) :
    plus (TM.Term.splitFin t).1 (ofNat (TM.Term.splitFin t).2) = t := by
  have hcg : CNV (TM.Term.splitFin t).1 = true :=
    cnv_ofList_take t ((toList t).length
      - ((toList t).reverse.takeWhile (fun x => x == one)).length) ht
  have hF1 : ((toList t).reverse.dropWhile (fun x => x == one)).reverse
      ++ List.replicate (((toList t).reverse.takeWhile (fun x => x == one)).length) one
      = toList t := by
    have h := trailing_ones (toList t).reverse
    rwa [List.reverse_reverse] at h
  have hAP : ∀ x ∈ ((toList t).reverse.dropWhile (fun x => x == one)).reverse, x.isAP = true := by
    intro x hx
    exact cnv_toList_isAP t ht x (by rw [← hF1]; exact List.mem_append_left _ hx)
  have hg : toList (TM.Term.splitFin t).1
      = ((toList t).reverse.dropWhile (fun x => x == one)).reverse := by
    rw [splitFin_fst t, TM.Term.toList_ofList hAP]
  have hspec := plus_ofNat_spec _ hcg (TM.Term.splitFin t).2
  have hto : toList (plus (TM.Term.splitFin t).1 (ofNat (TM.Term.splitFin t).2)) = toList t := by
    rw [hspec.2, hg]; exact hF1
  rw [← ofList_toList_cnv _ hspec.1, hto, ofList_toList_cnv t ht]

theorem predOr_eq {t : Term} {m : Nat} (hm : (TM.Term.splitFin t).2 = m + 1) :
    predOr t = plus (TM.Term.splitFin t).1 (ofNat m) := by
  show (match TM.Term.splitFin t with | (_, 0) => t | (g, k + 1) => plus g (ofNat k)) = _
  cases hs : TM.Term.splitFin t with
  | mk g k =>
    rw [hs] at hm
    have hk : k = m + 1 := hm
    subst hk
    rfl

theorem predOr_eq_self {t : Term} (hm : (TM.Term.splitFin t).2 = 0) : predOr t = t := by
  show (match TM.Term.splitFin t with | (_, 0) => t | (g, k + 1) => plus g (ofNat k)) = _
  cases hs : TM.Term.splitFin t with
  | mk g k => rw [hs] at hm; have hk : k = 0 := hm; subst hk; rfl

/-- **`predOr` IS A SUCCESSOR'S PREDECESSOR** — the fact the `predC` measurement pointed at,
    proved without `predC`. -/
theorem succT_predOr {t : Term} (ht : CNV t = true) {m : Nat}
    (hm : (TM.Term.splitFin t).2 = m + 1) : succT (predOr t) = t := by
  have hcg : CNV (TM.Term.splitFin t).1 = true :=
    cnv_ofList_take t ((toList t).length
      - ((toList t).reverse.takeWhile (fun x => x == one)).length) ht
  rw [predOr_eq hm, ← plus_ofNat_step _ hcg m, ← hm]
  exact splitFin_rebuild t ht

/-- **`land_predOr`'s `CNV` HALF.**  No hypothesis that `predOr` moves — it holds either way. -/
theorem cnv_predOr {t : Term} (ht : CNV t = true) : CNV (predOr t) = true := by
  cases hm : (TM.Term.splitFin t).2 with
  | zero => rw [predOr_eq_self hm]; exact ht
  | succ m =>
    have hcg : CNV (TM.Term.splitFin t).1 = true :=
      cnv_ofList_take t ((toList t).length
        - ((toList t).reverse.takeWhile (fun x => x == one)).length) ht
    rw [predOr_eq hm]
    exact (plus_ofNat_spec _ hcg m).1

/-- **`land_predOr`'s `lt` HALF**, against the site's own argument.  The parent `φ̄(a,b)` is one
    `lt_phi_of_le_fst` away and that lemma is `CNV`-gated, which is the finding above. -/
theorem lt_predOr {t : Term} (ht : CNV t = true) (hmv : predOr t ≠ t) :
    lt (predOr t) t = true := by
  cases hm : (TM.Term.splitFin t).2 with
  | zero => exact absurd (predOr_eq_self hm) hmv
  | succ m =>
    have h := lt_succT (predOr t) (cnv_predOr ht)
    rwa [succT_predOr ht hm] at h

end

/-! The `predC` cross-check, kept because it is independent of the proof above: my `predOr` and
    WF's `predC` agree wherever both are defined, so the two lanes' notions of "step down by one"
    are the same notion. -/

#guard (cnvPool.filter (fun t => (!(predOr t == t)) != (Evidence.WF.kindV t))).length == 0
#guard ((gpool.filter (fun t => Evidence.WF.CNV t)).filter
          (fun t => (!(predOr t == t)) != (Evidence.WF.kindV t))).length == 0
#guard (gpool.filter (fun t => Evidence.WF.CNV t)).length == 215
#guard ((cnvPool.filter (fun t => Evidence.WF.kindV t)).filter
          (fun t => !(predOr t == Evidence.WF.predC t))).length == 0
#guard (cnvPool.filter (fun t => Evidence.WF.kindV t)).length == 39
#guard ((gpool.filter (fun t => Evidence.WF.CNV t && Evidence.WF.kindV t)).filter
          (fun t => !(predOr t == Evidence.WF.predC t))).length == 0
#guard (gpool.filter (fun t => Evidence.WF.CNV t && Evidence.WF.kindV t)).length == 40

/-! The finding's evidence: the `inT`-non-`CNV` class, GENERATED rather than sieved. -/

def ncArgs : List Term := [TM.Term.M, TM.Term.Z TM.Term.M, TM.Term.Z zero,
  TM.Term.omg TM.Term.M, TM.Term.psi TM.Term.M zero, TM.Term.psi (TM.Term.Z TM.Term.M) zero,
  TM.Term.add TM.Term.M one, phi zero (TM.Term.Z TM.Term.M)]

def ncSeeds : List Term := ncArgs ++ [zero, one, omega]

def ncPhis2 : List (Term × Term) :=
  (ncSeeds.flatMap (fun a => ncSeeds.map (fun b => (a, b)))).filter
    (fun p => TM.Term.inT (phi p.1 p.2) && !(Evidence.WF.CNV (phi p.1 p.2)))

def ncAll : List Term :=
  (((gpool ++ inTpool).eraseDups ++ ncArgs
    ++ ncSeeds.flatMap (fun a => ncSeeds.map (fun b => phi a b))
    ++ ncArgs.flatMap (fun a => ncArgs.map (fun b => TM.Term.add a b))).eraseDups).filter
  (fun t => TM.Term.inT t && !(Evidence.WF.CNV t))

def cnvBounds : List Term := cnvPool ++ [phi omega zero, phi (phi one zero) zero,
  phi (phi (phi one zero) zero) zero]

-- the corpora hold ONE such `phi` term, so the class is generated
#guard (((gpool ++ inTpool).eraseDups).filter
          (fun t => TM.Term.inT t && !(Evidence.WF.CNV t))).length == 6
#guard ((((gpool ++ inTpool).eraseDups).filter
          (fun t => TM.Term.inT t && !(Evidence.WF.CNV t))).filter
          (fun t => match t with | .phi _ _ => true | _ => false)).length == 1
#guard ncPhis2.eraseDups.length == 40
#guard (ncPhis2.eraseDups.filter (fun p => !(lt p.2 (phi p.1 p.2)))).length == 0
#guard (ncPhis2.eraseDups.filter (fun p => !(lt p.1 (phi p.1 p.2)))).length == 0
-- and the third option: no `inT`-non-`CNV` term is below ANY `CNV` term
#guard ncAll.length == 63
#guard cnvBounds.length == 172
#guard (cnvBounds.filter (fun v => Evidence.WF.CNV v)).length == 172
#guard (ncAll.flatMap (fun t => (cnvBounds.filter (fun v => lt t v)).map (fun v => (t, v)))).length == 0

/-! ### §15.6 `land_omLog` AND `land_fpDeep` — THE `CNV` HALVES

Both need NO order fact, which is why they are here while F1a/F1b/F2 are with the WF lane.

`omLog` lands on the ω-exponent `x` of `g = φ̄(0,x)`, or — at the fixed-point skip — on `x+1`.
`CNV x` is `cnv_phi`; `CNV (x+1)` is `plus_one_eq_succT` then `cnv_succT`, the same two WF lemmas
that closed `land_predOr`.  **The `succT` chain has now paid for the `CNV` recommendation twice.**

`fpDeep` descends through `φ̄` layers into the summands of a subscript's infinite part, so its
`CNV` half is the descent's two closure facts — `cnv_ofList_take` (§15.5) for `(splitFin x).1`,
and `cnv_mem_summands` for a summand of it — under `findSome_mem` (§11), which is already proved
and was written for the `tdepth` measure that died.  A lemma from an abandoned branch, reused
whole: that is the second time §11's `tdepth` work has been salvageable despite the measure it
was built for being refuted. -/

section
open Evidence.WF (CNV cnv_add cnv_phi succT cnv_succT plus_one_eq_succT)

theorem cnv_mem_summands : ∀ (t g : Term),
    CNV t = true → g ∈ summands t → CNV g = true := by
  intro t
  induction t with
  | zero => intro g _ hg; simp only [summands] at hg; exact absurd hg (List.not_mem_nil)
  | M => intro _ h _; exact Bool.noConfusion h
  | omg _ _ => intro _ h _; exact Bool.noConfusion h
  | psi _ _ _ _ => intro _ h _; exact Bool.noConfusion h
  | Z _ _ => intro _ h _; exact Bool.noConfusion h
  | phi _ _ _ _ => intro g h hg; simp only [summands, List.mem_singleton] at hg; rw [hg]; exact h
  | add u v ihu ihv =>
    intro g h hg
    obtain ⟨_, hcu, hcv, _⟩ := cnv_add h
    simp only [summands, List.mem_append] at hg
    rcases hg with hh | hh
    · exact ihu g hcu hh
    · exact ihv g hcv hh

/-- **`land_omLog`'s `CNV` HALF.**  `omLog` lands on the ω-exponent or on its successor, and
    both are `CNV` — `cnv_phi` for the first, `cnv_succT` for the second. -/
theorem cnv_omLog {g : Term} (hg : CNV g = true) : CNV (omLog g) = true := by
  cases g with
  | zero => exact hg
  | M => exact hg
  | omg _ => exact hg
  | psi _ _ => exact hg
  | Z _ => exact hg
  | add _ _ => exact hg
  | phi a x =>
    cases a with
    | zero =>
      have hx : CNV x = true := (cnv_phi hg).2
      show CNV (match summands (TM.Term.splitFin x).1 with
                | [c] => if TM.Term.isFP zero c then plus x one else x
                | _ => x) = true
      cases hs : summands (TM.Term.splitFin x).1 with
      | nil => exact hx
      | cons c rest =>
        cases rest with
        | nil =>
          show CNV (if TM.Term.isFP zero c then plus x one else x) = true
          by_cases h : TM.Term.isFP zero c = true
          · rw [if_pos h, plus_one_eq_succT x hx]; exact cnv_succT x hx
          · rw [if_neg h]; exact hx
        | cons _ _ => exact hx
    | M => exact hg
    | omg _ => exact hg
    | psi _ _ => exact hg
    | Z _ => exact hg
    | add _ _ => exact hg
    | phi _ _ => exact hg

/-- **`land_fpDeep`'s `CNV` HALF.**  The descent goes through `φ̄` layers into summands, and
    `CNV` survives both — `cnv_ofList_take` and `cnv_mem_summands`, under §11's `findSome_mem`. -/
theorem cnv_fpDeepF : ∀ (f : Nat) (a t z : Term), CNV t = true →
    fpDeepF f a t = some z → CNV z = true := by
  intro f
  induction f with
  | zero => intro a t z _ h; simp only [fpDeepF] at h; exact absurd h (by simp)
  | succ f ih =>
    intro a t z ht h
    simp only [fpDeepF] at h
    by_cases hfp : TM.Term.isFP a t = true
    · rw [if_pos hfp] at h; injection h with h1; rw [← h1]; exact ht
    · rw [if_neg hfp] at h
      cases t with
      | zero => exact absurd h (by simp)
      | M => exact absurd h (by simp)
      | omg _ => exact absurd h (by simp)
      | psi _ _ => exact absurd h (by simp)
      | Z _ => exact absurd h (by simp)
      | add _ _ => exact absurd h (by simp)
      | phi c x =>
        have hx : CNV x = true := (cnv_phi ht).2
        obtain ⟨g, hgm, hgf⟩ := findSome_mem (fpDeepF f a) _ z h
        exact ih a g z (cnv_mem_summands _ g (cnv_ofList_take x _ hx) hgm) hgf

theorem cnv_fpDeep {a t z : Term} (ht : CNV t = true) (h : fpDeep a t = some z) :
    CNV z = true := cnv_fpDeepF (t.deg + 4) a t z ht h

end

/-! The order facts the two `lt` halves still need, banked before they are proved.  `F2`'s side
    condition is MEASURED, not guessed — the control at `x = 0` fires, where both sides are `1`. -/

def cnvAll : List Term := (cnvPool ++ gpool.filter (fun t => Evidence.WF.CNV t)).eraseDups

#guard cnvAll.length == 215
#guard (cnvAll.filter (fun b => !(le (TM.Term.splitFin b).1 b))).length == 0
#guard (cnvAll.filter (fun s => !((summands s).all (fun g => le g s)))).length == 0
#guard ((cnvAll.filter (fun x => !(x == zero))).filter (fun x =>
          !(lt (Evidence.WF.succT x) (phi zero x)))).length == 0
#guard (cnvAll.filter (fun x => !(x == zero))).length == 214
#guard lt (Evidence.WF.succT zero) (phi zero zero) == false


/-! ### §15.7 WITHDRAWN — F1a AND F2 ARE WF §15.27's, AND THE DUPLICATION IS RECORDED IN §15.9

This section held `lt_succT_phi`, `le_plus_ofNat` and `le_splitFin_fst`: independent proofs of F2
and F1a, written while veblen2 was proving the same two facts in WF §15.27.  **They are deleted
rather than kept, because two lemmas with the same content and nothing saying which to use is
worse than either alone** — that is the exact cost I named when withdrawing the request.

WHAT IS KEPT IS THE COMPARISON, because the peer's statements are better and the reason is
transferable.  My F1a inducted on `splitFin`'s trailing-1 count `m`, through `plus_ofNat_step`;
`le_ofList_take` proves EVERY prefix of the component list is `le` the whole, at a general `k`,
and F1a is one instance.  **The arithmetic of `m` was never the content — the prefix structure
was**, and a statement at the general `k` serves the next caller too.  My F2 and theirs happen to
agree exactly on the obstruction: `le` comes from "nothing lies strictly between `a` and `a+1`",
and the step to `lt` is that `succT x` is `add`-headed while `phi zero x` is `phi`-headed, which
is precisely why `x = 0` — where the two ARE the same term — is the exception.

    F1a   `Evidence.WF.le_splitFin_fst`, and `le_ofList_take` for the general prefix
    F1b   `Evidence.WF.le_toList_self`, bridged to `summands` by §15.9
    F2    `Evidence.WF.lt_succT_phi_zero`, with `le_succT_phi_zero` as the unconditional form -/

/-! ### §15.8 `land_omLog`'s `lt` HALF — PROVED, AND IT NEEDED NEITHER F3 NOR F4

The remaining two order facts turned out not to gate this site.  `land_omLog`'s own statement is
`lt (omLog g) g` — against the SUMMAND, not against the parent `φ̄(a,b)` — and the step from `g`
to the parent is the consumer's composition, which is where F1b lives.  So the site itself closes
on `lt_phi_self` and §15.7's `lt_succT_phi`, both of which exist:

    omLog φ̄(0,x) = x        (ordinary)   `lt_phi_self`     lt x φ̄(0,x)
    omLog φ̄(0,x) = x+1      (FP skip)    `lt_succT_phi`    lt (x+1) φ̄(0,x)

**AND THE SKIP BRANCH'S GUARD DISCHARGES `lt_succT_phi`'s SIDE CONDITION FOR FREE.**  §15.7 needs
`x ≠ 0`, and the skip fires only when `summands ((splitFin x).1)` is a ONE-ELEMENT list.  At
`x = 0` that list is EMPTY — `splitFin 0 = (0, 0)` and `summands 0 = []` — so the guard cannot
hold.  The side condition that the measurement found and the syntax explained is discharged by
the definition's own branch condition.  Three independent things saying `x = 0` is the exception.

**THE `φ̄(0,·)` FORM NEEDS NO "IT MOVES" HYPOTHESIS AT ALL**, so it is stated separately: at that
shape BOTH branches descend, and `omLog g ≠ g` is only needed to rule out the shapes where `omLog`
is the identity.  Weakening a hypothesis where the proof permits it is the same option-value rule
as §15's, read in the other direction — the caller that has the shape should not have to supply a
disequality the shape already implies. -/

section
open Evidence.WF (CNV cnv_phi succT plus_one_eq_succT lt_phi_self)

/-- At `φ̄(0,x)` BOTH branches of `omLog` descend — no "it moves" hypothesis. -/
theorem lt_omLog_phi_zero {x : Term} (hx : CNV x = true) :
    lt (omLog (phi zero x)) (phi zero x) = true := by
  show lt (match summands (TM.Term.splitFin x).1 with
           | [c] => if TM.Term.isFP zero c then plus x one else x
           | _ => x) (phi zero x) = true
  cases hs : summands (TM.Term.splitFin x).1 with
  | nil => exact lt_phi_self hx zero
  | cons c rest =>
    cases rest with
    | nil =>
      show lt (if TM.Term.isFP zero c then plus x one else x) (phi zero x) = true
      by_cases h : TM.Term.isFP zero c = true
      · rw [if_pos h, plus_one_eq_succT x hx]
        refine Evidence.WF.lt_succT_phi_zero hx ?_
        intro hz
        rw [hz] at hs
        exact absurd hs (by simp [TM.Term.splitFin, toList, ofList, summands])
      · rw [if_neg h]; exact lt_phi_self hx zero
    | cons _ _ => exact lt_phi_self hx zero

/-- **`land_omLog`'s `lt` HALF.** -/
theorem lt_omLog {g : Term} (hg : CNV g = true) (hmv : omLog g ≠ g) :
    lt (omLog g) g = true := by
  cases g with
  | zero => exact absurd rfl hmv
  | M => exact absurd rfl hmv
  | omg _ => exact absurd rfl hmv
  | psi _ _ => exact absurd rfl hmv
  | Z _ => exact absurd rfl hmv
  | add _ _ => exact absurd rfl hmv
  | phi a x =>
    cases a with
    | zero => exact lt_omLog_phi_zero (cnv_phi hg).2
    | M => exact absurd rfl hmv
    | omg _ => exact absurd rfl hmv
    | psi _ _ => exact absurd rfl hmv
    | Z _ => exact absurd rfl hmv
    | add _ _ => exact absurd rfl hmv
    | phi _ _ => exact absurd rfl hmv

end


/-! ### §15.9 THE `summands`/`toList` BRIDGE — and a COLLISION worth recording

WF §15.27 landed F1a, F1b and F2 while §15.7 was being written, and §15.7 PROVES TWO OF THEM
INDEPENDENTLY.  That is a duplication, it is mine, and it is recorded rather than quietly tidied:
I sent five facts and only afterwards priced them against what WF already had, which is the wrong
order.  The withdrawal message went out after the peer had already started.  **The rule this
teaches is not "price before asking" — I did eventually price them — it is PRICE BEFORE SENDING,
because a request is not free to retract once the other lane has begun.**

The duplicates come out when WF §15.27 is built; the sections stay as they are until then, since
deleting a proof that currently compiles in favour of one that is not yet in an olean would leave
the file red.  WF's forms are the ones to keep — F1a through `le_ofList_take` at a GENERAL prefix
`k`, which removes `splitFin`'s trailing-1 count from the proof entirely, where §15.7's route
inducts on exactly that count.  The peer's statement is better than mine and the reason is
instructive: **the arithmetic of `m` was never the content, the prefix structure was.**

WHAT ONLY THIS FILE CAN PROVE, and WF §15.27 says so explicitly: F1b is stated there with
`toList`, because `summands` is defined HERE and WF is upstream.  Naming it there would invert
the import direction that Cert/SqV/WF have been careful about since 2026-08-09.  So the bridge is
the one piece of F1b that had to come back down. -/

theorem summands_of_isAP {t : Term} (h : t.isAP = true) : summands t = [t] := by
  cases t <;> first | rfl | (simp only [TM.Term.isAP] at h; exact absurd h (by simp))

/-- **THE BRIDGE WF §15.27 LEFT HERE, AND IT COULD ONLY BE HERE.**  `summands` is defined in
    this file, which imports WF, so WF cannot name it; F1b is stated there with `toList`.  The
    two definitions differ only at `add u v` — `summands` recurses into `u`, `toList` does not —
    and `CNV (add u v)` gives `u.isAP` while `isAP (add _ _) = false`, so `u` is never a sum and
    the extra recursion is the identity. -/
theorem summands_eq_toList : ∀ (t : Term), Evidence.WF.CNV t = true → summands t = toList t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | M => intro h; exact Bool.noConfusion h
  | omg _ _ => intro h; exact Bool.noConfusion h
  | psi _ _ _ _ => intro h; exact Bool.noConfusion h
  | Z _ _ => intro h; exact Bool.noConfusion h
  | phi _ _ _ _ => intro _; rfl
  | add u v _ ihv =>
    intro h
    obtain ⟨hAPu, _, hcnv, _⟩ := Evidence.WF.cnv_add h
    show summands u ++ summands v = u :: toList v
    rw [summands_of_isAP hAPu, ihv hcnv]
    rfl

/-! ### §15.10 `land_fpDeep`'s `lt` HALF — THE LAST CLAUSE, AND IT IS `le`, NOT `lt`

`fpDeep a t` returns `t` ITSELF when `t` is already a fixed point of `φ̄(a,·)` — 6 of the 24
triples in the call graph — so the honest conclusion at this site is `le`, not `lt`.  **Claiming
`lt` here would be an overclaim that the corpus itself refutes**, and the consumer loses nothing:
the parent of this recursion is `φ̄(a,b)`, not `t`, and the step from `t` to the parent is strict
by `lt_phi_of_le`.  This is the mirror of §15.8 — state each clause against its own argument and
let the composition to the parent supply the strictness.

THE DESCENT IS THE SAME INDUCTION AS `cnv_fpDeepF`, with one order fact per layer: a summand of
`(splitFin x).1` is `lt φ̄(c,x)`, which is F1b (bridged) composed with F1a and `lt_phi_of_le`.
**Every piece of that is now a theorem** — WF §15.27 for the two `le` facts, §15.9 for the bridge.

WHAT IT COST TO GET THE LAST CLAUSE: nothing new.  All three landing clauses now stand on the
same four WF facts (`lt_phi_self`, `lt_phi_of_le`, `le_toList_self`, `le_ofList_take`) plus the
`succT` chain, and no arithmetic measure anywhere — which was the whole point of abandoning §13's
family.  What remains for a fuel-free `encv'` is the `add` clause's F3/F4 and the carrier. -/

section
open Evidence.WF (CNV cnv_phi le_self le_of_lt le_trans_inT lt_trans_inT inT_of_cnv
  le_toList_self le_splitFin_fst lt_phi_of_le)

/-- F1b in the form this file's recursion uses, through §15.9's bridge. -/
theorem le_summands_self {s g : Term} (hs : CNV s = true) (hg : g ∈ summands s) :
    le g s = true := by
  rw [summands_eq_toList s hs] at hg
  exact le_toList_self s hs g hg

/-- A summand of the subscript's infinite part is strictly below the term it came from. -/
theorem lt_summand_phi {c x g : Term} (hcx : CNV (phi c x) = true)
    (hg : g ∈ summands ((TM.Term.splitFin x).1)) : lt g (phi c x) = true := by
  have hx : CNV x = true := (cnv_phi hcx).2
  have hsf : CNV (TM.Term.splitFin x).1 = true :=
    cnv_ofList_take x ((toList x).length
      - ((toList x).reverse.takeWhile (fun y => y == one)).length) hx
  have hg' : CNV g = true := cnv_mem_summands _ g hsf hg
  exact lt_phi_of_le hg' hx
    (le_trans_inT (inT_of_cnv _ hg') (inT_of_cnv _ hsf) (inT_of_cnv _ hx)
      (le_summands_self hsf hg) (le_splitFin_fst hx))

/-- **`land_fpDeep`'s `lt` HALF.**  `le`, because `fpDeep` can return its own argument. -/
theorem le_fpDeepF : ∀ (f : Nat) (a t z : Term), CNV t = true →
    fpDeepF f a t = some z → le z t = true := by
  intro f
  induction f with
  | zero => intro a t z _ h; simp only [fpDeepF] at h; exact absurd h (by simp)
  | succ f ih =>
    intro a t z ht h
    simp only [fpDeepF] at h
    by_cases hfp : TM.Term.isFP a t = true
    · rw [if_pos hfp] at h; injection h with h1; rw [← h1]; exact le_self t
    · rw [if_neg hfp] at h
      cases t with
      | zero => exact absurd h (by simp)
      | M => exact absurd h (by simp)
      | omg _ => exact absurd h (by simp)
      | psi _ _ => exact absurd h (by simp)
      | Z _ => exact absurd h (by simp)
      | add _ _ => exact absurd h (by simp)
      | phi c x =>
        have hx : CNV x = true := (cnv_phi ht).2
        have hsf : CNV (TM.Term.splitFin x).1 = true :=
          cnv_ofList_take x ((toList x).length
            - ((toList x).reverse.takeWhile (fun y => y == one)).length) hx
        obtain ⟨g, hgm, hgf⟩ := findSome_mem (fpDeepF f a) _ z h
        have hg' : CNV g = true := cnv_mem_summands _ g hsf hgm
        have hz : CNV z = true := cnv_fpDeepF f a g z hg' hgf
        exact le_trans_inT (inT_of_cnv _ hz) (inT_of_cnv _ hg') (inT_of_cnv _ ht)
          (ih a g z hg' hgf) (le_of_lt (lt_summand_phi ht hgm))

theorem le_fpDeep {a t z : Term} (ht : CNV t = true) (h : fpDeep a t = some z) :
    le z t = true := le_fpDeepF (t.deg + 4) a t z ht h

end

/-! `fpDeep` returns its own argument on 6 of the 24 call-graph triples `(z, hd, parent)` — 3 of
    the 18 distinct `(z, hd)` pairs — which is why the conclusion is `le` and not `lt`. -/

def fpTriples : List (Term × Term × Term) :=
  (cnvPool.filterMap (fun t => match t with
    | .phi a b => match fpDeep a ((summands (TM.Term.splitFin b).1).headD zero) with
                  | some z => some (z, (summands (TM.Term.splitFin b).1).headD zero, t)
                  | none => none
    | _ => none)).eraseDups

#guard fpTriples.length == 24
#guard (fpTriples.filter (fun p => p.1 == p.2.1)).length == 6
#guard ((fpTriples.map (fun p => (p.1, p.2.1))).eraseDups).length == 18
#guard (((fpTriples.map (fun p => (p.1, p.2.1))).eraseDups).filter (fun p => p.1 == p.2)).length == 3
-- and the two halves agree with the measurement: every target is `CNV` and `le` its argument
#guard (fpTriples.filter (fun p => !(Evidence.WF.CNV p.1 && le p.1 p.2.1))).length == 0

/-! ### §15.11 SUPERSEDED — WF §15.28 PROVES F3 AND F4 AS `lt`, AND MY REDUCTION WAS UNNEEDED

This section reduced F3 and F4 to one `le` fact plus two structural disequalities (`deg` decides
that a component is never its own sum) and routed the `le`.  **The reduction was correct and it
was unnecessary: `lt_head_add_cnv` and `lt_tail_add` were already proved as `lt`.**  They landed
before the de-scope message did, so I was one commit behind, not wrong — but the consumer needs
neither disequality, so `deg_pos`, `ne_add_left`, `ne_add_right` and my `lt_head_add` are deleted
rather than kept.

    F3   `Evidence.WF.lt_head_add_cnv` {u v} (CNV (u ⊕ v))  : lt u (u ⊕ v)
         `Evidence.WF.lt_head_add`     {u} (u.isAP) (v)     : lt u (u ⊕ v)   -- CNV not needed
    F4   `Evidence.WF.lt_tail_add`     (v u) (CNV (u ⊕ v))  : lt v (u ⊕ v)

**WHAT SURVIVES IS `lt_of_le_of_ne`, AND IT IS USED TWICE BELOW** — `lt_zero_phi` and
`lt_summand_add`.  `le s t` is literally `s == t || lt s t`, so this is Bool bookkeeping, not
order theory, which is why it belongs here and not upstream.

**THE CONTROL THAT DID NOT FIRE TURNED OUT TO BE A RESULT.**  I proposed `v ≠ 0` as F3's side
condition, probed it, found `lt u (u ⊕ 0)` returns TRUE — `lt` compares SYNTAX — and reported "my
control did not fire" rather than dressing the probe up.  veblen2's proof shows why it CANNOT
fire: `hdLe zero u = false` by `rfl`, so `CNV (u ⊕ 0) = false` and the hypothesis already excludes
the case.  **That is C4's discriminator applied to a CONTROL instead of a measurement**, and it
lands the same way: a control that fails to fire is worthless unless its failure is PROVABLE, in
which case it tells you the hypothesis is doing the work.  And the same `rfl` discharges F4's
`v = 0` case — second time in one batch that the probe finding a side condition and the case
discharging it were one fact seen from two sides. -/

section
open Evidence.WF (CNV)

/-- `le` plus a disequality is `lt` — `le` is literally `== || lt`.  Bool bookkeeping. -/
theorem lt_of_le_of_ne {a b : Term} (hle : le a b = true) (hne : a ≠ b) : lt a b = true := by
  simp only [TM.Term.le, Bool.or_eq_true, beq_iff_eq] at hle
  rcases hle with h | h
  · exact absurd h hne
  · exact h

end

-- the probe that could not fire, and why: `lt` compares syntax, but `CNV` excludes the term
#guard lt one (TM.Term.add one zero) == true
#guard Evidence.WF.CNV (TM.Term.add one zero) == false

/-! ### §15.12 THE `add` CLAUSE RECURSES ON SUMMANDS, NOT COMPONENTS — and F4 was the wrong question

§15.11 reduced F4 to one `le` fact and routed it.  **It should not have been routed at all**, and
the reason is a change to `encv'`, not to the order theory.

**F4 IS TRUE AND IS PROVED (`lt_tail_add`, WF §15.28), SO THIS IS NOT A CLAIM THAT THE FACT WAS
UNOBTAINABLE — the request was answerable and was still the wrong question.**  That is what makes
it the clean instance of the rule rather than the lucky one: a FALSE request would have proved
nothing about the pattern.  The restructure below is therefore a CHOICE, not a necessity; it is
kept because one uniform clause over `summands` is simpler than two over components, and because
its decrease is a constructor clash instead of an induction on the order.

`encvF`'s `add` clause is `encvF f u d ++ encvF f v d` — it recurses on the RAW components, so the
tail `v` is a target and `v` is not a component of `add u v` (§15.11: only 33 of 72).  But the
same output is produced by recursing on the SUMMANDS:

    encv t d  =  (summands t).flatMap (fun g => encv g d)

MEASURED over all 215 `CNV` terms at four depths — **0 violations**, not only on the 72 `add`s.
It is not a coincidence: `CNV (add u v)` forces `u.isAP`, so `summands u = [u]`, and the flatten
unrolls to exactly the same concatenation the two-component clause produces.

**AND EVERY SUMMAND IS ADDITIVELY PRINCIPAL, SO THE DECREASE IS FREE.**  `le` comes from
`le_summands_self` (§15.10); strictness needs `g ≠ add u v`, and `isAP (add _ _) = false` while
every summand of a `CNV` term is `isAP` — so the disequality is a CONSTRUCTOR clash, not a `deg`
argument and not an order fact.  `lt_summand_add` below.

WHAT THIS COSTS AND WHAT IT BUYS.  It costs one clause of `encv'` being written over `summands`
rather than over `u`/`v` — an EQUAL definition on `CNV`, measured.  It buys the deletion of the
last routed order fact.  **The general lesson is the one §15.8 and §15.10 already showed twice:
when a clause's decrease is hard, look at whether the clause is asking the right question before
asking the order lane to answer the wrong one.**  Three sites now, all closed by restating the
step rather than by strengthening the order theory:

    land_omLog    stated against the summand, not the parent   ⇒  F1b was never needed here
    land_fpDeep   `le`, because `fpDeep` can return its argument ⇒  no overclaim to defend
    the `add` clause  recurses on summands, not components      ⇒  F4 not needed at all

A caller who does want the two-component form has `lt_head_add_cnv` and `lt_tail_add` upstream;
§15.11's duplicate is deleted. -/

section
open Evidence.WF (CNV)

/-- Every summand of a `CNV` term is additively principal — §15.9's bridge plus §15.5. -/
theorem isAP_mem_summands {t g : Term} (ht : CNV t = true) (hg : g ∈ summands t) :
    g.isAP = true := by
  rw [summands_eq_toList t ht] at hg
  exact cnv_toList_isAP t ht g hg

/-- **THE `add` CLAUSE'S DECREASE, WITH NO ORDER FACT BEYOND F1b.**  A summand is additively
    principal, so it cannot BE the sum — a constructor clash, not an argument about size. -/
theorem lt_summand_add {u v g : Term} (h : CNV (TM.Term.add u v) = true)
    (hg : g ∈ summands (TM.Term.add u v)) : lt g (TM.Term.add u v) = true := by
  refine lt_of_le_of_ne (le_summands_self h hg) ?_
  intro he
  have hap := isAP_mem_summands h hg
  rw [he] at hap
  exact absurd hap (by simp [TM.Term.isAP])

end

/-- The restructured `add` clause, as a function, so the agreement is executable. -/
def encvFlat (t : Term) (d : Nat) : List Col2 := (summands t).flatMap (fun g => encv g d)

#guard (cnvAll.filter (fun t => !((List.range 4).all (fun d => encv t d == encvFlat t d)))).length == 0
#guard cnvAll.length == 215
#guard (cnvAll.filter (fun t => match t with | .add _ _ => true | _ => false)).length == 72
#guard (cnvAll.filter (fun t => !((summands t).all (fun g => TM.Term.isAP g)))).length == 0

/-! ### §15.13 THE OBLIGATIONS AS `encv'` WILL MEET THEM — one per recursion site, against
     THE PARENT

§15.5–§15.12 state each clause against its OWN argument, which is what made them provable
separately.  What Lean will actually generate at a fuel-free `encv'` is a decrease against the
PARENT `φ̄(a,b)` or `u ⊕ v`, so the compositions belong in the file rather than at the definition
site — otherwise the same three-line `lt_of_le_of_lt` chain gets rewritten six times.

    site                  target                              theorem
    add clause            g ∈ summands (u ⊕ v)                `lt_summand_add`      §15.12
    ladder                predOr a                            `lt_predOr_phi`
    head                  (summands (splitFin b).1).headD 0   `lt_headD_phi`
    mkBlocks              g or omLog g, per summand           `lt_blockArg_phi`
    collapse              same head                           `lt_headD_phi`
    fpDeep                z with fpDeep a hd = some z         `lt_fpDeep_phi`

**AND THE MACHINERY IS VERIFIED, NOT ASSUMED.**  A spike — a `CarrierV`-recursive function
descending through `summands` via `List.attach`, with the decrease discharged by
`lt_summand_add` — ELABORATES and EVALUATES.  That was the one thing no measurement could tell
me: whether Lean's well-founded recursion would accept the obligations in the shape these
theorems produce.  It does, and the pattern is `match hp : p.1 with … termination_by p …
decreasing_by rw [hp]; exact …`.

`le_predOr` and `le_omLog` are the unconditional `le` forms of §15.5 and §15.8 — the "it moves"
hypothesis disappears because the identity case gives `le_self`.  A caller at a recursion site
does not know whether the step moves, so the `le` form is the one it can use; the `lt` forms
stay because they are what the movement facts actually say. -/

section
open Evidence.WF (CNV cnv_phi le_self le_of_lt le_zero_any inT_of_cnv inT_le_fragR
  lt_of_le_of_lt3 lt_phi_of_le_fst)

private theorem lt_of_le_of_lt_cnv {a b c : Term} (ha : CNV a = true) (hb : CNV b = true)
    (hc : CNV c = true) (h1 : le a b = true) (h2 : lt b c = true) : lt a c = true :=
  lt_of_le_of_lt3 (inT_le_fragR a (inT_of_cnv a ha)) (inT_le_fragR b (inT_of_cnv b hb))
    (inT_le_fragR c (inT_of_cnv c hc)) h1 h2

theorem lt_zero_phi (a b : Term) : lt zero (phi a b) = true :=
  lt_of_le_of_ne (le_zero_any _) (by intro hc; exact absurd hc (by simp))

/-- `predOr` never ascends — the unconditional form the recursion site needs. -/
theorem le_predOr {t : Term} (ht : CNV t = true) : le (predOr t) t = true := by
  by_cases h : predOr t = t
  · rw [h]; exact le_self t
  · exact le_of_lt (lt_predOr ht h)

/-- `omLog` never ascends. -/
theorem le_omLog {g : Term} (hg : CNV g = true) : le (omLog g) g = true := by
  by_cases h : omLog g = g
  · rw [h]; exact le_self g
  · exact le_of_lt (lt_omLog hg h)

theorem cnv_headD {b : Term} (hb : CNV b = true) :
    CNV ((summands (TM.Term.splitFin b).1).headD zero) = true := by
  have hsf : CNV (TM.Term.splitFin b).1 = true :=
    cnv_ofList_take b ((toList b).length
      - ((toList b).reverse.takeWhile (fun y => y == one)).length) hb
  cases hg : summands (TM.Term.splitFin b).1 with
  | nil => rfl
  | cons c rest =>
    show CNV c = true
    exact cnv_mem_summands _ c hsf (by rw [hg]; exact List.mem_cons_self)

/-- **THE LADDER SITE.** -/
theorem lt_predOr_phi {a b : Term} (h : CNV (phi a b) = true) :
    lt (predOr a) (phi a b) = true :=
  lt_phi_of_le_fst (cnv_predOr (cnv_phi h).1) (cnv_phi h).1 (le_predOr (cnv_phi h).1)

/-- **THE HEAD SITE** — including the empty-summand case, where the head defaults to `0`. -/
theorem lt_headD_phi {a b : Term} (h : CNV (phi a b) = true) :
    lt ((summands (TM.Term.splitFin b).1).headD zero) (phi a b) = true := by
  cases hg : summands (TM.Term.splitFin b).1 with
  | nil => exact lt_zero_phi a b
  | cons c rest =>
    show lt c (phi a b) = true
    exact lt_summand_phi h (by rw [hg]; exact List.mem_cons_self)

/-- **THE `mkBlocks` SITE** — the argument is the summand at `a = 0` and its ω-exponent otherwise,
    and both descend. -/
theorem lt_blockArg_phi {a b g : Term} (h : CNV (phi a b) = true)
    (hg : g ∈ summands ((TM.Term.splitFin b).1)) :
    lt (if a == zero then g else omLog g) (phi a b) = true := by
  have hsf : CNV (TM.Term.splitFin b).1 = true :=
    cnv_ofList_take b ((toList b).length
      - ((toList b).reverse.takeWhile (fun y => y == one)).length) (cnv_phi h).2
  have hg' : CNV g = true := cnv_mem_summands _ g hsf hg
  by_cases hz : (a == zero) = true
  · rw [if_pos hz]; exact lt_summand_phi h hg
  · rw [if_neg hz]
    exact lt_of_le_of_lt_cnv (cnv_omLog hg') hg' h (le_omLog hg') (lt_summand_phi h hg)

/-- **THE `fpDeep` SITE.** -/
theorem lt_fpDeep_phi {a b z : Term} (h : CNV (phi a b) = true)
    (hz : fpDeep a ((summands (TM.Term.splitFin b).1).headD zero) = some z) :
    lt z (phi a b) = true :=
  lt_of_le_of_lt_cnv (cnv_fpDeep (cnv_headD (cnv_phi h).2) hz) (cnv_headD (cnv_phi h).2) h
    (le_fpDeep (cnv_headD (cnv_phi h).2) hz) (lt_headD_phi h)

/-- The same site, taking the target's `CNV` and `le` DIRECTLY rather than the `fpDeep` equation.
    This is the form `fpDeepC` hands over, and taking it this way is what keeps the dependent
    match out of `encvC`. -/
theorem lt_fpDeep_phi' {a b z : Term} (h : CNV (phi a b) = true) (hcz : CNV z = true)
    (hle : le z ((summands (TM.Term.splitFin b).1).headD zero) = true) :
    lt z (phi a b) = true :=
  lt_of_le_of_lt_cnv hcz (cnv_headD (cnv_phi h).2) h hle (lt_headD_phi h)

end

/-! ## §16 THE FUEL-FREE ENCODER — `encv'`, BY WELL-FOUNDED RECURSION ON THE ORDER

`encvF` carries fuel because "the `predOr` recursion is not structural, and at the gate stage a
termination proof would be premature" (§1's own comment).  §13 then showed no ARITHMETIC measure
in the `deg`/`tdepth`/`tsize`/`ncomp` family works — `deg` dies at `omLog`, `tdepth` at `predOr`,
and the 263-term table is the record that the family was searched, not that it was not tried.
The order itself is the measure: WF §15.25.1's `CarrierV` is the `CNV` terms under `lt`, well
founded by `acc_cnv_inT`, and §15.5–§15.13 supply a decrease at every recursion site.

**`encvC` ELABORATED ON THE FIRST ATTEMPT, with all five obligations discharged by §15.13.**
That is the part no measurement could have established: `targets` over-approximates the call
graph and was only ever evidence that the obligations would be DISCHARGEABLE.  Lean generates
the real obligations from the syntax of the definition, and if `targets` had MISSED a call the
definition would not have elaborated.  It did.

    site               obligation                    discharged by
    add                lt g (u ⊕ v)                  `lt_summand_add`     §15.12
    ladder             lt (predOr a) φ̄(a,b)          `lt_predOr_phi`      §15.13
    mkBlocks           lt (g | omLog g) φ̄(a,b)       `lt_blockArg_phi`    §15.13
    head / collapse    lt (headD gs) φ̄(a,b)          `lt_headD_phi`       §15.13
    fpDeep             lt z φ̄(a,b)                   `lt_fpDeep_phi`      §15.13

THE AGREEMENT, over the corpus the coordinator named, stated rather than summarised:

    corpusW ++ deeper ++ nested        319 entries,  169 distinct,  ALL 169 `CNV`
    encv' t d = encv t d,  d ∈ 0..3                                 0 violations
    the same over `cnvAll` (215 `CNV` terms)                         0 violations
    toMatrix (encv' t 0) = sqv t                                     0 violations

**AND THEY ARE `#guard`s IN THE FILE, NOT NUMBERS IN A MESSAGE — WHICH IS THE PROPERTY THAT PAID
OUT.**  §17's `fpDeepC` changed `encvC`'s `fpDeep` clause AFTER these were written.  The agreement
re-ran on the very check that verified the change: `agreeCorpus` is `corpusW ++ deeper ++ nested`
deduped, `cnvAll` is `cnvPool ++ gpool`-filtered-to-`CNV` deduped, both NAMED in the guards rather
than described, and both still 0 violations at `d ∈ 0..3`.  **A definition change cannot silently
invalidate a measurement that is executable and lives beside it** — it can only make the file red.
A measurement reported in prose would have gone stale and read as current.

**`encvF` STAYS.**  Thirteen candidates were compared on it, and the D1–D8 gate numbers
throughout this file are ITS numbers; deleting it would orphan every measurement above.  `encv'`
supersedes it as the definition to reason about, and the agreement above is what licenses reading
this file's earlier measurements as measurements of `encv'`.

**`encv'` IS TOTAL BUT SAYS NOTHING OFF `CNV`** — it returns `[]` there, where `encv` returns the
fuelled value.  That is a deliberate difference and not a defect: the Veblen-region encoder is
only ever applied inside `CNV`, and a function that is honest about its domain is better than one
that returns a value it cannot justify.  The agreement above is stated ON `CNV` for that reason.

**THE AXIOM SET DOES NOT CHANGE.  THE WHOLE FILE IS `[propext, Quot.sound]`, `encvC` AND `encv'`
INCLUDED, WITH NO EXCEPTION** — measured after WF's rebuild, not assumed from the recursion
principle.

IT BRIEFLY DID, AND THE REASON IS THE PART WORTH KEEPING.  When §16 was written, `encvC` and
`encv'` came out `[propext, Classical.choice, Quot.sound]`, and I recorded the growth as INHERITED
— `acc_cnv_inT` carried it, so `wf_lt_cnv` and the instance did, so anything recursing on them
must.  The inheritance was real.  **The SOURCE was not where the inheritance chain suggested.**
veblen2 found it: `acc_cnv_aux`'s base case closed the non-arithmetic goal `Acc RV t` with a bare
`omega` against contradictory hypotheses, and `exact absurd hd (by have := deg_pos t; omega)` is
otherwise identical and clean.  Two lines, and the whole chain below it went constructive.

**AND THE OBVIOUS EXPLANATION OF *WHY* IS WITHDRAWN, WHICH IS THE PART THAT NEEDS SAYING.**  Both
lanes wrote down "a decision tactic closing a NON-ARITHMETIC goal by contradiction imports choice"
— it is tidy, it fits the six real sites, and **it does not reproduce.**  Bare `simp`, `simpa`,
`omega`, `decide` and `simp at h` on a contradictory hypothesis with a non-arithmetic goal all come
back `[propext]` when probed directly.  The six sites were genuinely tainted; **the trigger is
uncharacterised.**  So there is no tactic-shape rule to follow while writing a proof, and looking
for one is the wrong move: **write the proof you want and MEASURE the result.**  The detector is
`#print axioms` and nothing else.

**A CLEAN DEPENDENCY SET IS NOT EVIDENCE THAT A THEOREM IS CLEAN.**  Every named thing
`acc_cnv_aux` uses — `acc_sum`, `acc_phi_v`, `acc_zero_v`, `cnv_phi`, `cnv_add`, `deg_pos` — was
`[propext, Quot.sound]` while `acc_cnv_aux` itself was not, **because the axiom entered through a
TACTIC, which has no name to bisect.**  Bisecting the dependency graph cannot reach it; the
technique that does is rebuilding the lemma line by line and printing axioms of the rebuild.
Recorded here because a file that reports axioms should also record how an axiom can appear from
nowhere — and because "all its dependencies are clean" is the reasoning that would have stopped
the search one step short.

**AND WELL-FOUNDED RECURSION DID NOT COST THE AXIOM.**  I wrote that `Classical.choice` was "the
price of well-founded recursion" and it was not — it was one tactic call in one base case.  A
price attributed to a technique, when it belonged to a line, is the same error as a name
attributed to a statement: **an explanation that fits is not an explanation that is true.**

**THE CARRIER IS `CarrierV`, DECIDED BY THE WF LANE, AND THE DECIDING REASON IS NOT THE ONE I
GAVE.**  I argued from WF §15.25.1's own criterion — the choice "depends only on whether `CNV` at
each target is cheap to PROVE, not on whether it is true" — and it was cheap: `cnv_predOr`,
`cnv_omLog`, `cnv_fpDeep`, `cnv_mem_summands`, none needing an order fact.  That criterion is
satisfied but it only says the bounded form's advantage buys nothing.  **The reason the unbounded
form WINS is structural and it is veblen2's: `encv'` recurses with NO EXTERNAL CEILING.**  Its
targets are `predOr a`, the summands of `splitFin b`, and the `omLog`/`fpDeep` outputs — sub-terms
of the input, bounded by nothing given to the function.  `BelowC v` would make it invent a `v`
(`succT t`, say) and thread `lt s v` through every clause via `belowC_step` for no return.
`wf_lt_cnv` needs no `v`, and `carrierV_step` takes exactly `CNV x` and `lt x y.1` — the pair the
landing theorems deliver.

**AND THE TWO CARRIER ANSWERS IN THIS FILE ARE NOT A CONTRADICTION, THEY ARE TWO QUESTIONS.**
§15.5's `cnv_of_belowC` answers "does a BOUNDED consumer need `inT`-gated order facts?" — no.
This answers "which carrier for an UNBOUNDED recursion?" — this one.  Both are recorded, because a
later reader meeting only one of them would draw the wrong conclusion from it. -/

/-- **`fpDeep`'s RESULT WITH ITS PROOFS ATTACHED** — the dependent match happens HERE, once, in a
    helper with no recursion in it, so `encvC` can match on an ordinary `Option`.  `List.attach`
    plays the same trick for the summands, which is why the `add` clause never had this problem. -/
def fpDeepC (a t : Term) (ht : Evidence.WF.CNV t = true) :
    Option {z : Term // Evidence.WF.CNV z = true ∧ le z t = true} :=
  match hfd : fpDeep a t with
  | some z => some ⟨z, cnv_fpDeep ht hfd, le_fpDeep ht hfd⟩
  | none => none

def encvC (p : Evidence.WF.CarrierV) (d : Nat) : List Col2 :=
  match hp : p.1 with
  | .zero => []
  | .add u v =>
      (summands (TM.Term.add u v)).attach.flatMap (fun g =>
        encvC ⟨g.1, cnv_mem_summands _ g.1 (hp ▸ p.2) g.2⟩ d)
  | .phi a b =>
      let ladder : List Col2 :=
        if a == zero then []
        else (d + 1, 1) :: bumpAt (d + 2)
          (encvC ⟨predOr a, cnv_predOr (Evidence.WF.cnv_phi (hp ▸ p.2)).1⟩ (d + 2))
      let unit : List Col2 := if a == zero then [(d + 1, 0)] else ladder
      let reps : List Col2 := (List.replicate (TM.Term.splitFin b).2 unit).flatten
      let mk : List {x // x ∈ summands (TM.Term.splitFin b).1} → List Col2 := fun hs =>
        (hs.map (fun g =>
          ladder ++ shiftD (if a == zero then d + 1 else d + 2)
            (encvC ⟨if a == zero then g.1 else omLog g.1,
              by
                by_cases hz : (a == zero) = true
                · rw [if_pos hz]
                  exact cnv_mem_summands _ g.1
                    (cnv_ofList_take b _ (Evidence.WF.cnv_phi (hp ▸ p.2)).2) g.2
                · rw [if_neg hz]
                  exact cnv_omLog (cnv_mem_summands _ g.1
                    (cnv_ofList_take b _ (Evidence.WF.cnv_phi (hp ▸ p.2)).2) g.2)⟩ 0))).flatten
      if TM.Term.isFP a ((summands (TM.Term.splitFin b).1).headD zero) then
        encvC ⟨(summands (TM.Term.splitFin b).1).headD zero,
                cnv_headD (Evidence.WF.cnv_phi (hp ▸ p.2)).2⟩ d
          ++ (if (summands (TM.Term.splitFin b).1).length == 1
              then (if a == zero then [((d + 1, 0) : Col2)] else ladder)
              else mk ((summands (TM.Term.splitFin b).1).attach.drop 1))
          ++ reps
      else
        match fpDeepC a ((summands (TM.Term.splitFin b).1).headD zero)
                (cnv_headD (Evidence.WF.cnv_phi (hp ▸ p.2)).2) with
        | some z =>
            encvC ⟨z.1, z.2.1⟩ d
              ++ mk (summands (TM.Term.splitFin b).1).attach ++ reps
        | none =>
            (d, 0) :: ((match summands (TM.Term.splitFin b).1 with
                        | [] => ladder
                        | _ => mk (summands (TM.Term.splitFin b).1).attach) ++ reps)
  | _ => []
termination_by p
decreasing_by
  · rw [hp]; exact lt_summand_add (hp ▸ p.2) g.2
  · rw [hp]; exact lt_predOr_phi (hp ▸ p.2)
  · rw [hp]; exact lt_blockArg_phi (hp ▸ p.2) g.2
  · rw [hp]; exact lt_headD_phi (hp ▸ p.2)
  · rw [hp]; exact lt_fpDeep_phi' (hp ▸ p.2) z.2.1 z.2.2

/-- The fuel-free encoder as a total function: `encvC` on `CNV`, `[]` elsewhere. -/
def encv' (t : Term) (d : Nat) : List Col2 :=
  if h : Evidence.WF.CNV t = true then encvC ⟨t, h⟩ d else []

def agreeCorpus : List Term := (corpusW ++ deeper ++ nested).eraseDups

#guard (corpusW ++ deeper ++ nested).length == 319
#guard agreeCorpus.length == 169
#guard (agreeCorpus.filter (fun t => Evidence.WF.CNV t)).length == 169
#guard (agreeCorpus.filter (fun t =>
          !((List.range 4).all (fun d => encv' t d == encv t d)))).length == 0
#guard (cnvAll.filter (fun t =>
          !((List.range 4).all (fun d => encv' t d == encv t d)))).length == 0
#guard (agreeCorpus.filter (fun t => !(toMatrix (encv' t 0) == sqv t))).length == 0

/-! ## §17 `sqv_decomp` — §9's BLOCKER 1 IS GONE, AND WHAT REPLACES IT IS SMALLER

§9 recorded two blockers.  Blocker 2 (import direction) was resolved there.  **Blocker 1 —
"`sqv` is defined with fuel and nothing proves the fuel is enough" — no longer exists**, because
§16's `encv'` has no fuel.  §9's own diagnosis was that the obstacle "is not a defect in the
encoding — seven dimensions say the encoding is right — it is that the DEFINITION is not in a
form an induction can use."  The definition is now in such a form.

**`encvF_saturate` NEVER HAS TO BE PROVED.**  §9 named it as the missing lemma
(`encvF f t d = encvF (f+1) t d` above the chosen fuel, "provable and real work") and WF §15.25
warned that accessibility gives no fuel bound, so a fuel-free redefinition and a saturation proof
are DIFFERENT obligations.  Redefining discharged the obligation instead of proving it.

WHAT IS ACTUALLY LEFT, and it is a layer rather than a theorem.  The ε_ω row's encoder fact is

    encv' (φ̄(1, ofNat n)) 0  =  (0,0) :: (1,1)ⁿ⁺¹

and its arithmetic is now available: `splitFin_ofNat` below says `splitFin (ofNat n) = (0, n)`,
so the subscript contributes no summands and `reps` is `n` copies of the ladder.  The row is then
one branch walk — `isFP 1 0 = false`, `fpDeep 1 0 = none`, both computed.

**BUT `encvC` CANNOT BE UNFOLDED BY `rw` AT A SPECIALISED ARGUMENT**, and the reason is structural,
not a tactic accident: the clause carries `CNV` PROOF TERMS whose TYPES mention `splitFin b`, so
rewriting `splitFin (ofNat n)` inside it fails with "motive is not type correct".  `simp only`
gets past the outer occurrences and stalls at the ones under `.attach`'s membership proof.

**THIS IS §10's PROBLEM AGAIN AND §10 ALREADY SOLVED IT — for `encvF`.**  §10 states
`encvF_phi_collapse`, `encvF_phi_deep`, `encvF_phi_base` as NAMED EQUATIONS, each proved by
`show (if … then _ else _) = _; rw [if_pos/if_neg, hz]; rfl`, precisely so that no consumer ever
unfolds the definition.  `encvC` needs the same three, stated with `splitFin b` left SYMBOLIC —
the branch conditions as hypotheses about `(summands (splitFin b).1).headD 0` rather than about a
specialised `b`, so nothing has to be rewritten under a dependent proof.  That is the next piece
of work, it is bounded, and it is the same shape as work already in this file.

**ONE THING IN `encvC` HAD TO CHANGE FIRST, AND WITH IT THE ROW CLOSES IN THREE TACTICS.**
§10's `rw [if_pos/if_neg]; rfl` idiom works on plain `if`s.  `encvC`'s `fpDeep` site was not an
`if` — it was

    match hfd : fpDeep a hd with | some z => encvC ⟨z, cnv_fpDeep … hfd⟩ d | none => …

**a match that BINDS its own equation, because the target's `CNV` proof is built from `hfd`.**  A
hypothesis `fpDeep a hd = none` cannot rewrite that scrutinee: the binder makes it dependent, and
the branch is exactly where the proof term lives.  Deciding the outer `isFP` `if` first does not
help — it lands you inside this match.

THE FIX IS TO PUSH THE PROOFS INTO THE DATA, so the clause matches non-dependently:

    def fpDeepC (a t) (ht : CNV t) : Option {z // CNV z = true ∧ le z t = true} :=
      match hfd : fpDeep a t with
      | some z => some ⟨z, cnv_fpDeep ht hfd, le_fpDeep ht hfd⟩
      | none   => none

The dependent match happens ONCE, inside a helper with no recursion in it, and `encvC` then
matches on an ordinary `Option` whose payload already carries what the recursive call needs —
the same trick `List.attach` plays for the summands, which is why the `add` clause has no such
problem.  `cnv_fpDeep` and `le_fpDeep` (§15.6, §15.10) are exactly the two facts the subtype
wants, so nothing new has to be proved to make the change.

**THE ROW IS PROVED.  `encvC_epsOmega` BELOW, FOR EVERY `n`, AND NO NAMED-EQUATION LAYER WAS
NEEDED IN THE END** — but the route is not the one I predicted twice, and both wrong predictions
named a real obstruction, so both stay.

`fpDeepC` removed ONE of two proof-carrying constructs.  The other is `List.attach`: the summands'
membership proof has a TYPE mentioning `summands (splitFin b).1`, so `rw [splitFin_ofNat]` under it
is still a dependent rewrite and still fails with "motive is not type correct".

**THE TRICK IS TO REWRITE THE DEPENDENT TERM ITSELF, NOT WHAT IT DEPENDS ON.**  `gs.attach` and
`([] : List {x // x ∈ gs})` have the SAME type, so replacing one by the other is not dependent —
and that equation is proved by a LENGTH argument, `(gs.attach).length = gs.length = 0`, which
touches only a `Nat`.  **Where a rewrite is blocked by a dependent type, rewrite the whole
dependent term to a value of the same type and prove THAT equation by a non-dependent route.**
The `fpDeepC` result and the `predOr` call go the same way: `encvC_predOr_one` rewrites the entire
`encvC ⟨predOr one, pf⟩` call rather than the `predOr one` inside it, with `Subtype.ext` supplying
the carrier equality.

    rw [encvC]; dsimp only; rw [hfp]; simp only […]; rw [hfd, hat, hm2, encvC_predOr_one]
    dsimp only; split

is the whole proof, plus `flatten_replicate_singleton` for the `reps` block and a `split` whose
second branch contradicts `summands (splitFin (ofNat n)).1 = []`.

**AND I BRIEFLY BELIEVED IT HAD CLOSED ONE ROUND EARLIER, WHEN IT HAD NOT.  I WAS ONE SENTENCE
FROM REPORTING SUCCESS, AND THE COORDINATOR WOULD HAVE COMMITTED IT.**  I filtered the checker's
messages by line number to isolate the new ones, the filter bound sat above the lines the test
occupied, and it reported CLEAN for three variants that all failed.  **A FILTERED GREEN IS NOT A
GREEN.**

**IT HAPPENED ON A THROWAWAY PROBE, AND THAT IS WHY IT HAPPENED.**  The whole-artifact rule was
never in doubt for a real check; I relaxed it for a disposable one and then believed the
disposable one's output exactly as much as a real check's.  **The status of a tool does not lower
how much its output gets believed.**  Filter by SEVERITY, never by line number or substring: a
line-number filter with a wrong bound does not fail, **it prints CLEAN**.

**AND THE ONLY SURVIVING TRACE WAS `#print axioms`.**  The build passed.  The file held no `sorry`
token — the failed proof was `sorry`-FREE in source; Lean had inserted `sorryAx` itself.  The line
count grew the way a successful edit grows.  `sorryAx` in the axiom print was the single signal
that anything was wrong, which makes the axiom print not an audit step but **the last line of
retreat when something that looks like it went through did not.**  The verdict here is from an
unfiltered full-file check, read by severity.

WHAT GENERALISES: `splitFin_ofNat` handles every `φ̄(a, ofNat n)` subscript, and the three
"rewrite the whole dependent term" moves are reusable as stated.  **The named-equation layer was
predicted here for the row whose `attach` list is REAL — §18 is that row, and the layer was not
needed there either.  It is RETIRED; see §18's closing note.** -/

theorem takeWhile_replicate_one : ∀ n,
    (List.replicate n one).takeWhile (fun x => x == one) = List.replicate n one := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ,
        List.takeWhile_cons_of_pos (p := fun x => x == one) (by simp), ih]

/-- **`ofNat n` IS ALL FINITE PART** — no infinite part, and the count is `n`.  The subscript
    arithmetic of every `φ̄(a, ofNat n)` row reduces to this. -/
theorem splitFin_ofNat (n : Nat) : TM.Term.splitFin (ofNat n) = (zero, n) := by
  show (ofList ((toList (ofNat n)).take ((toList (ofNat n)).length
          - ((toList (ofNat n)).reverse.takeWhile (fun x => x == one)).length)),
        ((toList (ofNat n)).reverse.takeWhile (fun x => x == one)).length) = _
  rw [Evidence.WF.toList_ofNat n, List.reverse_replicate, takeWhile_replicate_one,
      List.length_replicate, Nat.sub_self, List.take_zero]
  rfl

#guard (List.range 8).all (fun n => TM.Term.splitFin (ofNat n) == (zero, n))
-- the branch walk the ε_ω row takes, computed
#guard TM.Term.isFP one zero == false
#guard fpDeep one zero == none
-- and the row itself, at four points; the `∀ n` form is what the named-equation layer unlocks
#guard encv' (phi one (ofNat 0)) 0 == (0,0) :: List.replicate 1 ((1,1) : Col2)
#guard encv' (phi one (ofNat 1)) 0 == (0,0) :: List.replicate 2 ((1,1) : Col2)
#guard encv' (phi one (ofNat 2)) 0 == (0,0) :: List.replicate 3 ((1,1) : Col2)
#guard encv' (phi one (ofNat 5)) 0 == (0,0) :: List.replicate 6 ((1,1) : Col2)


theorem cnv_phi_one_ofNat (n : Nat) : Evidence.WF.CNV (phi one (ofNat n)) = true := by
  show (Evidence.WF.CNV one && Evidence.WF.CNV (ofNat n)) = true
  rw [Evidence.WF.cnv_ofNat n]; rfl


theorem flatten_replicate_singleton {α : Type} (x : α) : ∀ n,
    (List.replicate n [x]).flatten = List.replicate n x
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.flatten_cons, flatten_replicate_singleton x n,
        List.replicate_succ]
    rfl

theorem predOr_one : predOr one = zero := by
  show (match TM.Term.splitFin one with | (_, 0) => one | (g, k + 1) => plus g (ofNat k)) = _
  rw [show TM.Term.splitFin one = (zero, 1) from by
        have := splitFin_ofNat 1; rwa [show ofNat 1 = one from rfl] at this]
  rfl

theorem fpDeepC_none {a t : Term} (ht : Evidence.WF.CNV t = true) (h : fpDeep a t = none) :
    fpDeepC a t ht = none := by
  unfold fpDeepC
  split
  · rename_i z hx; rw [h] at hx; exact absurd hx (by simp)
  · rfl

/-- The `predOr` recursive call at `a = 1`, rewritten WHOLE — `Subtype.ext` supplies the carrier
    equality, so `predOr one` is never rewritten underneath its own `CNV` proof. -/
theorem encvC_predOr_one (pf : Evidence.WF.CNV (predOr one) = true) (d : Nat) :
    encvC ⟨predOr one, pf⟩ d = [] := by
  have hs : (⟨predOr one, pf⟩ : Evidence.WF.CarrierV)
      = ⟨zero, by rw [predOr_one] at pf; exact pf⟩ := Subtype.ext predOr_one
  rw [hs, encvC]

/-- **THE ε_ω ROW'S ENCODER FACT, FOR EVERY `n`** — §9's first row, and what blocker 1 blocked.
    No induction on `n`: `splitFin (ofNat n) = (0, n)` leaves the subscript with no summands, so
    the clause is one branch walk and `reps` is `n` copies of the ladder. -/
theorem encvC_epsOmega (n : Nat) (h : Evidence.WF.CNV (phi one (ofNat n)) = true) :
    encvC ⟨phi one (ofNat n), h⟩ 0 = (0, 0) :: List.replicate (n + 1) ((1, 1) : Col2) := by
  have hgs : summands (TM.Term.splitFin (ofNat n)).1 = [] := by rw [splitFin_ofNat]; rfl
  have hat : (summands (TM.Term.splitFin (ofNat n)).1).attach = [] :=
    List.eq_nil_of_length_eq_zero (by rw [List.length_attach, hgs]; rfl)
  have hm2 : (TM.Term.splitFin (ofNat n)).2 = n := by rw [splitFin_ofNat]
  have hfp : TM.Term.isFP one ((summands (TM.Term.splitFin (ofNat n)).1).headD zero) = false := by
    rw [hgs]; rfl
  have hfd : ∀ pf, fpDeepC one ((summands (TM.Term.splitFin (ofNat n)).1).headD zero) pf = none :=
    fun pf => fpDeepC_none pf (by rw [hgs]; rfl)
  rw [encvC]
  dsimp only
  rw [hfp]
  simp only [Bool.false_eq_true, if_false]
  rw [hfd, hat, hm2, encvC_predOr_one]
  dsimp only
  split
  · show (0, 0) :: ([((1, 1) : Col2)] ++ (List.replicate n [((1, 1) : Col2)]).flatten)
      = (0, 0) :: List.replicate (n + 1) ((1, 1) : Col2)
    rw [flatten_replicate_singleton, List.replicate_succ]
    rfl
  · exact absurd hgs (by simp_all)

theorem encv'_epsOmega (n : Nat) :
    encv' (phi one (ofNat n)) 0 = (0, 0) :: List.replicate (n + 1) ((1, 1) : Col2) := by
  show (if h : Evidence.WF.CNV (phi one (ofNat n)) = true
        then encvC ⟨phi one (ofNat n), h⟩ 0 else []) = _
  rw [dif_pos (cnv_phi_one_ofNat n)]
  exact encvC_epsOmega n _

-- The ε_ω row at eight points.  The `∀ n` form is NOT proved — §17 says why, and what is left.
#guard (List.range 8).all (fun n =>
  encv' (phi one (ofNat n)) 0 == (0,0) :: List.replicate (n+1) ((1,1) : Col2))
#guard (List.range 8).all (fun n => encv (phi one (ofNat n)) 0 == encv' (phi one (ofNat n)) 0)

/-! ## §18 THE PRINCIPLE, STATED FIRST BECAUSE IT WAS DISCOVERED FOUR TIMES

**IN ANY DEFINITION BY WELL-FOUNDED RECURSION, THE PROOFS THREADED THROUGH THE CARRIER ARE
LOAD-BEARING FOR TERMINATION AND NEVER FOR THE VALUE.  The definition discharged termination once,
at elaboration.  A consumer reasoning about the VALUE may leave those proofs behind rather than
route around them.**

`encvC_eq_encv'` is that sentence as a theorem: `encvC ⟨x, hx⟩ d = encv' x d` for ANY `hx`.  Four
obstructions that looked like four different problems are four applications of it, and the fourth
(§19) is why it now leads this section instead of concluding it:

    §17  ε_ω        empty `attach`         a length argument on a `Nat`
    §17  fpDeep     match binding its eq   `fpDeepC`, proofs pushed into the data
    §18  row A      real `attach`, `add`   `encv'_add`, the clause left proof-free
    §19  ε_{ω²}     real `attach`, `mk`    `encvC_eq_encv'` + `List.attach_map_val`

**A NAMED-EQUATION LAYER ROUTES AROUND THE PROOFS, WHICH IS WHY IT WAS PREDICTED THREE TIMES AND
NEEDED ZERO** — see the retirement at the end of this section.  A principle discovered four times
should be findable once, so it is here rather than at the bottom.

### §18.1 ROW A — THE FIRST ROW WHOSE SUBSCRIPT HAS SUMMANDS, AND THE `add` CLAUSE IS THE
    TWO-COMPONENT ONE AFTER ALL

§17 closed `ε_ω`, whose subscript `ofNat n` contributes NO summands, so the `attach` list was
empty and a length argument sufficed.  The coordinator's test for whether a named-equation layer
earns its place is a row where the list is REAL.  `ω^(ε₀+1)` is that row: its fundamental sequence
is `ε₀·(n+1) = repAdd ε₀ n` (WF's `fsA`), an `add`-headed term with `n+1` summands.

**THE LAYER IS REFUSED A THIRD TIME, AND THIS TIME FOR A BETTER REASON THAN THE OTHER TWO.**  What
the `add` clause needs is not a named equation for its branches — it is `encv'_add`:

    encv' (u ⊕ v) d  =  (summands (u ⊕ v)).flatMap (fun g => encv' g d)

**which converts the whole clause out of the proof-carrying world in one step.**  `attach`'s
membership proofs vanish because `encvC ⟨x, hx⟩ d = encv' x d` for ANY proof `hx` — `encv'` is the
total wrapper, so the subtype's payload is irrelevant to the VALUE — and then
`l.attach.flatMap (fun g => f g.1) = l.flatMap f` is a plain `List` fact.  **The dependent
structure is not reasoned about; it is left behind.**

That is the same move as §17's, one level up: §17 rewrote a dependent TERM to a same-typed value,
this rewrites a dependent CLAUSE to a proof-free function.  Both work because the proofs were
never load-bearing for the value — only for the termination, which the definition already
discharged.

**AND §15.12's RESTRUCTURE IS VINDICATED IN A WAY I DID NOT ANTICIPATE.**  I changed the `add`
clause from two components to `summands` to avoid needing F4, and recorded that F4 turned out to be
true and proved so the change was a CHOICE.  It buys something else: `encv'_add` is stated over
`summands`, so a row's subscript decomposes in ONE step regardless of how the sum is bracketed,
and `summands_repAdd` gives the whole list at once.  The two-component form would have needed an
induction over the bracketing here.  A choice made for one reason paying for a different one is
worth recording as luck rather than foresight — I did not see this when I made it.

**THE NAMED-EQUATION LAYER IS RETIRED, NOT DEFERRED.**  It was predicted three times and refused
three times, each refusal on a proof attempt rather than on an opinion:

    §17  `ε_ω`        the `attach` list is EMPTY      → a length argument on a `Nat`
    §17  `fpDeep`     the match BINDS its equation    → `fpDeepC`, proofs pushed into the data
    §18  row A        the `attach` list is REAL       → `encv'_add`, the clause left proof-free

**Each prediction named a real obstruction and got the route wrong**, which is why both wrong
predictions stay written down: the third attempt had somewhere to stand because the first two had
said exactly what was in the way.  What replaced the layer is one sentence rather than a
three-lemma apparatus: **THE PRINCIPLE AT THE HEAD OF THIS SECTION.**  A named-equation layer
routes AROUND the carrier's proofs; the principle says there is nothing to route around, because
the proofs are irrelevant to the value.  That is why `encvC ⟨x, hx⟩ d = encv' x d` holds for ANY
`hx` and why `attach`'s membership can be discarded rather than tracked.

A layer refused three times on measurement is a firmer record than one adopted once on prediction;
if a later row needs it, it will need it for a reason none of these three had, and that reason
should be stated before the layer is written. -/

theorem flatMap_attach {α β : Type} (l : List α) (f : α → List β) :
    l.attach.flatMap (fun g => f g.1) = l.flatMap f := by
  rw [← List.flatMap_map Subtype.val f l.attach]
  congr 1
  simp

theorem flatMap_replicate {α β : Type} (x : α) (f : α → List β) : ∀ m,
    (List.replicate m x).flatMap f = (List.replicate m (f x)).flatten
  | 0 => rfl
  | m + 1 => by
    rw [List.replicate_succ, List.flatMap_cons, flatMap_replicate x f m,
        List.replicate_succ, List.flatten_cons]

/-- **THE PROOF IS IRRELEVANT TO THE VALUE.**  `encv'` is `encvC` with the `CNV` proof supplied
    by `dif_pos`, so any two proofs give the same list — which is what lets `attach`'s membership
    proofs be discarded rather than reasoned about. -/
theorem encvC_eq_encv' {x : Term} (hx : Evidence.WF.CNV x = true) (d : Nat) :
    encvC ⟨x, hx⟩ d = encv' x d := by
  show _ = (if hh : Evidence.WF.CNV x = true then encvC ⟨x, hh⟩ d else [])
  rw [dif_pos hx]

/-- **THE `add` CLAUSE, PROOF-FREE** — the whole clause converted out of the dependent world. -/
theorem encv'_add {u v : Term} (h : Evidence.WF.CNV (TM.Term.add u v) = true) (d : Nat) :
    encv' (TM.Term.add u v) d
      = (summands (TM.Term.add u v)).flatMap (fun g => encv' g d) := by
  show (if hh : Evidence.WF.CNV (TM.Term.add u v) = true
        then encvC ⟨TM.Term.add u v, hh⟩ d else []) = _
  rw [dif_pos h, encvC]
  dsimp only
  simp only [encvC_eq_encv']
  exact flatMap_attach (summands (TM.Term.add u v)) (fun g => encv' g d)

theorem summands_repAdd {x : Term} (hx : x.isAP = true) : ∀ n,
    summands (Evidence.WF.repAdd x n) = List.replicate (n + 1) x
  | 0 => summands_of_isAP hx
  | n + 1 => by
    show summands x ++ summands (Evidence.WF.repAdd x n) = _
    rw [summands_of_isAP hx, summands_repAdd hx n, List.replicate_succ]
    rfl

theorem cnv_repAdd_eps0T : ∀ n, Evidence.WF.CNV (Evidence.WF.repAdd Evidence.WF.eps0T n) = true
  | 0 => rfl
  | n + 1 => by
    show (TM.Term.isAP Evidence.WF.eps0T && Evidence.WF.CNV Evidence.WF.eps0T
          && Evidence.WF.CNV (Evidence.WF.repAdd Evidence.WF.eps0T n)
          && Evidence.WF.hdLe (Evidence.WF.repAdd Evidence.WF.eps0T n) Evidence.WF.eps0T) = true
    have hh : Evidence.WF.hdLe (Evidence.WF.repAdd Evidence.WF.eps0T n) Evidence.WF.eps0T = true :=
      Evidence.WF.hdLe_repAdd_self (p := one) (q := zero) n
    rw [cnv_repAdd_eps0T n, hh]
    rfl

/-- `ε₀`'s own encoder value — `ε_ω`'s row at `n = 0`, since `φ̄(1, ofNat 0) = φ̄(1,0) = ε₀`. -/
theorem encv'_eps0T : encv' Evidence.WF.eps0T 0 = [((0, 0) : Col2), (1, 1)] :=
  encv'_epsOmega 0

/-- **ROW A's ENCODER FACT, FOR EVERY `n`** — `ω^(ε₀+1)`'s fundamental sequence is `ε₀·(n+1)`,
    so this is the first row that exercises the `add` clause with a NON-EMPTY `attach` list. -/
theorem encv'_rowA : ∀ n, encv' (Evidence.WF.fsA n) 0
    = (List.replicate (n + 1) [((0, 0) : Col2), (1, 1)]).flatten
  | 0 => encv'_eps0T
  | n + 1 => by
    show encv' (TM.Term.add Evidence.WF.eps0T (Evidence.WF.repAdd Evidence.WF.eps0T n)) 0 = _
    rw [encv'_add (cnv_repAdd_eps0T (n + 1)) 0,
        show summands (TM.Term.add Evidence.WF.eps0T (Evidence.WF.repAdd Evidence.WF.eps0T n))
             = List.replicate (n + 2) Evidence.WF.eps0T from summands_repAdd rfl (n + 1),
        flatMap_replicate, encv'_eps0T]

#guard (List.range 6).all (fun n =>
  encv' (Evidence.WF.fsA n) 0 == (List.replicate (n+1) [((0,0) : Col2), (1,1)]).flatten)
#guard (List.range 6).all (fun n => encv (Evidence.WF.fsA n) 0 == encv' (Evidence.WF.fsA n) 0)
#guard Evidence.WF.fsA 2 == TM.Term.add Evidence.WF.eps0T
         (TM.Term.add Evidence.WF.eps0T Evidence.WF.eps0T)

/-! ## §19 `ε_{ω²}` — THE `mkBlocks` SITE, AND THE FOURTH SHAPE TO FALL TO THE SAME SENTENCE

§17's subscript had no summands, §18's row went through the `add` clause.  This is the first row
where **`mkBlocks` actually runs** — it maps a proof-carrying lambda over the `attach` list and
emits one ladder-plus-block per summand of the subscript.

**IT FELL TO `encvC_eq_encv'` AGAIN, AND THAT IS THE FOURTH DISTINCT-LOOKING OBSTRUCTION THE SAME
ONE SENTENCE HAS DISSOLVED** (§18's principle: the carrier's proofs are load-bearing for
TERMINATION, never for the VALUE).  Here it is `encvC_eq_encv'` followed by
`List.attach_map_val` — the map over `attach` becomes a map over the plain list, and from there
`List.map_replicate` finishes it.  **Not one line of the dependent structure is reasoned about.**

    §17  ε_ω        empty `attach`          length argument on a `Nat`
    §17  fpDeep     match binding its eq    `fpDeepC`, proofs pushed into the data
    §18  row A      real `attach`, `add`    `encv'_add`, clause left proof-free
    §19  ε_{ω²}     real `attach`, `mk`     `encvC_eq_encv'` + `List.attach_map_val`

**AND THE ROW NEEDED NOTHING FROM THE 𝔗(M) SIDE, WHICH NEITHER LANE EXPECTED.**  The brief was to
have the Veblen lane characterise `summands (fsC ω² n)`.  Both lanes `#eval`ed before either
proved anything, and both found the same thing:

    fsC ω² n = repAdd ω n            ω²'s fundamental sequence is ω·(n+1)

so the subscript's summand list is a REPLICATE — the shape §18 already handles — and
`Evidence.WF.fsC_omegaSq` (theirs, §15.16) composes with `summands_repAdd` (mine, §18) with
nothing in between.  **A compound-looking argument `φ̄(0,1+1)` said nothing about the shape of its
fundamental sequence, and the brief treated it as if it did.**  One `#eval` on each side was worth
more than the theorem either of us was about to write.

THE ROW IS STATED THREE TIMES ON PURPOSE: `encvC_epsOmegaSq` against the carrier, `encv'_epsOmegaSq`
against the total wrapper, and **`encv'_fsEW2` against the table's own `fsEW2`** — the last is the
one `sqv_decomp` will cite, and it is the other two plus `fsC_omegaSq`. -/

theorem toList_repAdd {x : Term} (hx : x.isAP = true) : ∀ n,
    toList (Evidence.WF.repAdd x n) = List.replicate (n + 1) x
  | 0 => TM.Term.toList_of_isAP hx
  | n + 1 => by
    show x :: toList (Evidence.WF.repAdd x n) = _
    rw [toList_repAdd hx n]
    simp [List.replicate_succ]

theorem ofList_replicate {x : Term} : ∀ n, ofList (List.replicate (n + 1) x) = Evidence.WF.repAdd x n
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ]
    show TM.Term.add x (ofList (List.replicate (n + 1) x)) = _
    rw [ofList_replicate n]
    rfl

/-- A sum of copies of one non-`1` additively principal term has NO finite part. -/
theorem splitFin_repAdd {x : Term} (hx : x.isAP = true) (hne : (x == one) = false) (n : Nat) :
    TM.Term.splitFin (Evidence.WF.repAdd x n) = (Evidence.WF.repAdd x n, 0) := by
  have hl := toList_repAdd hx n
  have htw : ((toList (Evidence.WF.repAdd x n)).reverse.takeWhile (fun y => y == one)) = [] := by
    rw [hl, List.reverse_replicate, List.replicate_succ,
        List.takeWhile_cons_of_neg (p := fun y => y == one) (by simp [hne])]
  show (ofList ((toList (Evidence.WF.repAdd x n)).take
        ((toList (Evidence.WF.repAdd x n)).length
          - ((toList (Evidence.WF.repAdd x n)).reverse.takeWhile (fun y => y == one)).length)),
        ((toList (Evidence.WF.repAdd x n)).reverse.takeWhile (fun y => y == one)).length) = _
  rw [htw, List.length_nil, Nat.sub_zero, List.take_length, hl, ofList_replicate]

theorem cnv_repAdd_omega : ∀ n, Evidence.WF.CNV (Evidence.WF.repAdd omega n) = true
  | 0 => rfl
  | n + 1 => by
    show (TM.Term.isAP omega && Evidence.WF.CNV omega
          && Evidence.WF.CNV (Evidence.WF.repAdd omega n)
          && Evidence.WF.hdLe (Evidence.WF.repAdd omega n) omega) = true
    have hh : Evidence.WF.hdLe (Evidence.WF.repAdd omega n) omega = true :=
      Evidence.WF.hdLe_repAdd_self (p := zero) (q := one) n
    rw [cnv_repAdd_omega n, hh]
    rfl

theorem cnv_phi_one_repAdd_omega (n : Nat) :
    Evidence.WF.CNV (phi one (Evidence.WF.repAdd omega n)) = true := by
  show (Evidence.WF.CNV one && Evidence.WF.CNV (Evidence.WF.repAdd omega n)) = true
  rw [cnv_repAdd_omega n]; rfl

/-- `1 = φ̄(0,0)` encodes as a single column — the `a = 0`, empty-subscript clause. -/
theorem encvC_one (h : Evidence.WF.CNV (phi zero zero) = true) (d : Nat) :
    encvC ⟨phi zero zero, h⟩ d = [((d, 0) : Col2)] := by
  have hfd : ∀ pf, fpDeepC zero ((summands (TM.Term.splitFin zero).1).headD zero) pf = none :=
    fun pf => fpDeepC_none pf rfl
  rw [encvC]
  dsimp only
  rw [show TM.Term.isFP zero ((summands (TM.Term.splitFin zero).1).headD zero) = false from rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [hfd]
  dsimp only
  rfl

theorem encv'_one (d : Nat) : encv' (phi zero zero) d = [((d, 0) : Col2)] := by
  show (if h : Evidence.WF.CNV (phi zero zero) = true then encvC ⟨phi zero zero, h⟩ d else []) = _
  rw [dif_pos (show Evidence.WF.CNV (phi zero zero) = true from rfl)]
  exact encvC_one _ d

/-- **THE `ε_{ω²}` ROW'S ENCODER FACT, FOR EVERY `n`** — the first row where `mkBlocks` runs.
    `ω²`'s fundamental sequence is `ω·(n+1)`, so the subscript's summand list is a REPLICATE of
    `n+1` copies of `ω` and each one contributes one ladder-plus-block. -/
theorem encvC_epsOmegaSq (n : Nat)
    (h : Evidence.WF.CNV (phi one (Evidence.WF.repAdd omega n)) = true) :
    encvC ⟨phi one (Evidence.WF.repAdd omega n), h⟩ 0
      = (0, 0) :: (List.replicate (n + 1) [((1, 1) : Col2), (2, 0)]).flatten := by
  have hsf : TM.Term.splitFin (Evidence.WF.repAdd omega n)
      = (Evidence.WF.repAdd omega n, 0) := splitFin_repAdd rfl rfl n
  have hgs : summands (TM.Term.splitFin (Evidence.WF.repAdd omega n)).1
      = List.replicate (n + 1) omega := by rw [hsf]; exact summands_repAdd rfl n
  have hm2 : (TM.Term.splitFin (Evidence.WF.repAdd omega n)).2 = 0 := by rw [hsf]
  have hhd : (summands (TM.Term.splitFin (Evidence.WF.repAdd omega n)).1).headD zero = omega := by
    rw [hgs, List.replicate_succ]; rfl
  have hfp : TM.Term.isFP one
      ((summands (TM.Term.splitFin (Evidence.WF.repAdd omega n)).1).headD zero) = false := by
    rw [hhd]; rfl
  have hfd : ∀ pf, fpDeepC one
      ((summands (TM.Term.splitFin (Evidence.WF.repAdd omega n)).1).headD zero) pf = none :=
    fun pf => fpDeepC_none pf (by rw [hhd]; rfl)
  rw [encvC]
  dsimp only
  rw [hfp]
  simp only [Bool.false_eq_true, if_false]
  rw [hfd, hm2, encvC_predOr_one]
  simp only [encvC_eq_encv', show (one == zero) = false from rfl, Bool.false_eq_true, if_false]
  rw [List.attach_map_val
        (l := summands (TM.Term.splitFin (Evidence.WF.repAdd omega n)).1)
        (f := fun x => ((0 + 1, 1) :: bumpAt (0 + 2) ([] : List Col2))
                ++ shiftD (0 + 2) (encv' (omLog x) 0))]
  rw [hgs, List.map_replicate]
  simp only [List.replicate_succ]
  rw [show omLog omega = phi zero zero from rfl, encv'_one]
  simp only [List.replicate_zero, List.flatten_nil, List.append_nil]
  rfl

theorem encv'_epsOmegaSq (n : Nat) :
    encv' (phi one (Evidence.WF.repAdd omega n)) 0
      = (0, 0) :: (List.replicate (n + 1) [((1, 1) : Col2), (2, 0)]).flatten := by
  show (if h : Evidence.WF.CNV (phi one (Evidence.WF.repAdd omega n)) = true
        then encvC ⟨phi one (Evidence.WF.repAdd omega n), h⟩ 0 else []) = _
  rw [dif_pos (cnv_phi_one_repAdd_omega n)]
  exact encvC_epsOmegaSq n _

/-- The row as the table states it, through veblen2's `fsC_omegaSq` (WF §15.16). -/
theorem encv'_fsEW2 (n : Nat) :
    encv' (Evidence.WF.fsEW2 n) 0
      = (0, 0) :: (List.replicate (n + 1) [((1, 1) : Col2), (2, 0)]).flatten := by
  show encv' (phi one (Evidence.WF.fsC Evidence.WF.omegaSq n)) 0 = _
  rw [Evidence.WF.fsC_omegaSq]
  exact encv'_epsOmegaSq n

#guard (List.range 7).all (fun n =>
  encv' (Evidence.WF.fsEW2 n) 0 == (0,0) :: (List.replicate (n+1) [((1,1) : Col2),(2,0)]).flatten)
#guard (List.range 7).all (fun n => encv (Evidence.WF.fsEW2 n) 0 == encv' (Evidence.WF.fsEW2 n) 0)
#guard (List.range 7).all (fun n =>
  Evidence.WF.fsC Evidence.WF.omegaSq n == Evidence.WF.repAdd omega n)

/-! ## §20 `ε_{ω^ω}` — ONE SUMMAND, ONE `φ̄` DEEPER, AND THE FIRST UNFOLDING OF `fpDeepF`'s FUEL

`ω^ω`'s fundamental sequence is `ω^(n+1)`, not a repeated sum: `fsC ω^ω n = φ̄(0, ofNat (n+1))`
(WF §15.16's `fsC_omegaOmega`, already proved — I looked before asking, and it was there, which is
now the sixth time tonight).  So the subscript has exactly ONE summand and `mkBlocks` runs on a
SINGLETON, while the block's own encoding is `ω^(n+1)`'s rather than a leaf's.

**THE ONE GENUINELY NEW PIECE IS `fpDeep_none_of_empty`, AND IT IS THE FIRST TIME THIS FILE
UNFOLDS A FUEL RECURSION AT A SYMBOLIC INDEX.**  `fpDeep a t = fpDeepF (t.deg + 4) a t`, and
`t.deg` varies with `n`, so §9's original blocker — "an induction on `n` compares `encvF 22`
against `encvF 30`" — is exactly the shape one would fear here.  It does not bite, and the reason
is worth stating: **the branch is decided at the FIRST step, so the fuel is `f + 1` for an
arbitrary `f` and never has to be known.**  Fuel only obstructs when the recursion must be
followed; a clause that terminates immediately unfolds once at any positive fuel.

**AND §18's ROW A IS NOW AN INSTANCE OF A GENERAL LEMMA IT MOTIVATED.**  `encv'_repAdd` says a sum
of copies encodes as copies of the encoding, for ANY additively principal summand — and it needs
NO induction on the encoder, because `summands_repAdd` delivers the whole list and `encv'_add`
consumes it in one step.  `encv'_ofNat_succ` (`ω^(n+1)`'s block above) is the instance at `x = 1`;
row A is the instance at `x = ε₀`.

**AND THAT ORDER IS THE POINT, NOT AN ACCIDENT: THE GENERAL LEMMA WAS NOT VISIBLE FROM THE FIRST
INSTANCE AND WAS OBVIOUS FROM THE SECOND.**  Row A's proof is `encv'_add` plus `summands_repAdd`
at `ε₀`; nothing in it suggests the summand is a parameter, because with one caller there is no
evidence about which parts vary.  The second caller supplied that evidence for free.  **This is an
argument for writing the SPECIFIC lemma first and generalising when a second caller appears** — the
opposite of the instinct to generalise immediately, and this file has now done it deliberately
rather than by omission.

THE ROW IS STATED TWICE AND BRIDGED ONCE, as in §19: `encvC_epsOmegaOmega` against the carrier,
`encv'_epsOmegaOmega` against the total wrapper, and `encv'_fsEWW` against the table's own
`fsEWW` — the last is what `sqv_decomp` will cite. -/

theorem cnv_repAdd_one : ∀ n, Evidence.WF.CNV (Evidence.WF.repAdd one n) = true
  | 0 => rfl
  | n + 1 => by
    show (TM.Term.isAP one && Evidence.WF.CNV one
          && Evidence.WF.CNV (Evidence.WF.repAdd one n)
          && Evidence.WF.hdLe (Evidence.WF.repAdd one n) one) = true
    have hh : Evidence.WF.hdLe (Evidence.WF.repAdd one n) one = true :=
      Evidence.WF.hdLe_repAdd_self (p := zero) (q := zero) n
    rw [cnv_repAdd_one n, hh]
    rfl

/-- **A SUM OF COPIES ENCODES AS COPIES OF THE ENCODING** — no induction on the encoder, because
    `summands_repAdd` delivers the whole list and `encv'_add` consumes it in one step. -/
theorem encv'_repAdd {x : Term} (hx : x.isAP = true) (d : Nat) : ∀ n,
    Evidence.WF.CNV (Evidence.WF.repAdd x n) = true →
    encv' (Evidence.WF.repAdd x n) d = (List.replicate (n + 1) (encv' x d)).flatten
  | 0, _ => by show encv' x d = _; simp
  | n + 1, h => by
    show encv' (TM.Term.add x (Evidence.WF.repAdd x n)) d = _
    rw [encv'_add h d,
        show summands (TM.Term.add x (Evidence.WF.repAdd x n)) = List.replicate (n + 2) x
          from summands_repAdd hx (n + 1),
        flatMap_replicate]

theorem encv'_ofNat_succ (n : Nat) :
    encv' (ofNat (n + 1)) 0 = List.replicate (n + 1) ((0, 0) : Col2) := by
  rw [Evidence.WF.ofNat_succ_eq n, encv'_repAdd (x := one) rfl 0 n (cnv_repAdd_one n),
      show encv' one 0 = [((0, 0) : Col2)] from encv'_one 0, flatten_replicate_singleton]

/-- `fpDeep` stops immediately when the head is not a fixed point and the subscript's infinite
    part has no summands — one unfolding, no induction on the fuel. -/
theorem fpDeep_none_of_empty {a c x : Term} (hfp : TM.Term.isFP a (phi c x) = false)
    (hgs : summands (TM.Term.splitFin x).1 = []) : fpDeep a (phi c x) = none := by
  show (if TM.Term.isFP a (phi c x) then some (phi c x)
        else match (phi c x : Term) with
             | .phi _ y => (summands (TM.Term.splitFin y).1).findSome?
                             (fpDeepF ((phi c x).deg + 3) a)
             | _ => none) = none
  rw [hfp]
  simp only [Bool.false_eq_true, if_false]
  show (summands (TM.Term.splitFin x).1).findSome? (fpDeepF ((phi c x).deg + 3) a) = none
  rw [hgs]
  rfl

theorem cnv_phi_one_pow (n : Nat) :
    Evidence.WF.CNV (phi one (phi zero (ofNat (n + 1)))) = true := by
  show (Evidence.WF.CNV one && (Evidence.WF.CNV zero && Evidence.WF.CNV (ofNat (n + 1)))) = true
  rw [Evidence.WF.cnv_ofNat (n + 1)]; rfl

/-- **THE `ε_{ω^ω}` ROW'S ENCODER FACT, FOR EVERY `n`** — one summand, nested one `φ̄` deeper
    than §19's, so `mkBlocks` runs on a SINGLETON and the block's own encoding is `ω^(n+1)`'s. -/
theorem encvC_epsOmegaOmega (n : Nat)
    (h : Evidence.WF.CNV (phi one (phi zero (ofNat (n + 1)))) = true) :
    encvC ⟨phi one (phi zero (ofNat (n + 1))), h⟩ 0
      = (0, 0) :: (1, 1) :: List.replicate (n + 1) ((2, 0) : Col2) := by
  have hzz : ofNat (n + 1) ≠ zero := by
    intro hc
    have ht := Evidence.WF.toList_ofNat (n + 1)
    rw [hc] at ht
    simp [toList, List.replicate_succ] at ht
  have hne : (phi zero (ofNat (n + 1)) == one) = false := by
    have : phi zero (ofNat (n + 1)) ≠ one := by
      intro hc; injection hc with _ h2; exact hzz h2
    simpa using this
  have hsf : TM.Term.splitFin (phi zero (ofNat (n + 1)))
      = (phi zero (ofNat (n + 1)), 0) :=
    splitFin_repAdd (x := phi zero (ofNat (n + 1))) rfl hne 0
  have hgs : summands (TM.Term.splitFin (phi zero (ofNat (n + 1)))).1
      = [phi zero (ofNat (n + 1))] := by rw [hsf]; rfl
  have hm2 : (TM.Term.splitFin (phi zero (ofNat (n + 1)))).2 = 0 := by rw [hsf]
  have hhd : (summands (TM.Term.splitFin (phi zero (ofNat (n + 1)))).1).headD zero
      = phi zero (ofNat (n + 1)) := by rw [hgs]; rfl
  have hfp : TM.Term.isFP one
      ((summands (TM.Term.splitFin (phi zero (ofNat (n + 1)))).1).headD zero) = false := by
    rw [hhd]; rfl
  have hin : summands (TM.Term.splitFin (ofNat (n + 1))).1 = [] := by rw [splitFin_ofNat]; rfl
  have hfd : ∀ pf, fpDeepC one
      ((summands (TM.Term.splitFin (phi zero (ofNat (n + 1)))).1).headD zero) pf = none :=
    fun pf => fpDeepC_none pf (by rw [hhd]; exact fpDeep_none_of_empty (by rfl) hin)
  have hom : omLog (phi zero (ofNat (n + 1))) = ofNat (n + 1) := by
    show (match summands (TM.Term.splitFin (ofNat (n + 1))).1 with
          | [g] => if TM.Term.isFP zero g then plus (ofNat (n + 1)) one else ofNat (n + 1)
          | _ => ofNat (n + 1)) = _
    rw [hin]
  rw [encvC]
  dsimp only
  rw [hfp]
  simp only [Bool.false_eq_true, if_false]
  rw [hfd, hm2, encvC_predOr_one]
  simp only [encvC_eq_encv', show (one == zero) = false from rfl, Bool.false_eq_true, if_false]
  rw [List.attach_map_val
        (l := summands (TM.Term.splitFin (phi zero (ofNat (n + 1)))).1)
        (f := fun y => ((0 + 1, 1) :: bumpAt (0 + 2) ([] : List Col2))
                ++ shiftD (0 + 2) (encv' (omLog y) 0))]
  rw [hgs]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil]
  rw [hom, encv'_ofNat_succ]
  simp only [shiftD, List.map_replicate, List.replicate_zero, List.flatten_nil, List.append_nil]
  rfl

theorem encv'_epsOmegaOmega (n : Nat) :
    encv' (phi one (phi zero (ofNat (n + 1)))) 0
      = (0, 0) :: (1, 1) :: List.replicate (n + 1) ((2, 0) : Col2) := by
  show (if h : Evidence.WF.CNV (phi one (phi zero (ofNat (n + 1)))) = true
        then encvC ⟨phi one (phi zero (ofNat (n + 1))), h⟩ 0 else []) = _
  rw [dif_pos (cnv_phi_one_pow n)]
  exact encvC_epsOmegaOmega n _

#guard (List.range 8).all (fun n =>
  encv' (Evidence.WF.fsEWW n) 0 == (0,0) :: (1,1) :: List.replicate (n+1) ((2,0) : Col2))
#guard (List.range 8).all (fun n => encv (Evidence.WF.fsEWW n) 0 == encv' (Evidence.WF.fsEWW n) 0)
#guard (List.range 10).all (fun n =>
  Evidence.WF.fsC Evidence.WF.omegaOmega n == phi zero (ofNat (n+1)))

/-- The row as the table states it, through `fsC_omegaOmega` (WF §15.16, already proved). -/
theorem encv'_fsEWW (n : Nat) :
    encv' (Evidence.WF.fsEWW n) 0
      = (0, 0) :: (1, 1) :: List.replicate (n + 1) ((2, 0) : Col2) := by
  show encv' (phi one (Evidence.WF.fsC Evidence.WF.omegaOmega n)) 0 = _
  rw [Evidence.WF.fsC_omegaOmega]
  exact encv'_epsOmegaOmega n

/-! ## §21 `ε_{ε₀}` — THE FIRST ROW THAT GENUINELY NEEDS AN INDUCTION ON `n`

Four rows fell without one.  This one does not, and the reason is NOT the summand list — §20's
family finding says every Veblen row's subscript summand list is a replicate, `ε_{ε₀}`'s included
(a singleton).  **The difference is that the single summand is `tower (n+1)`, so the BLOCK's own
encoding grows with `n` rather than repeating**, and the value is an increasing ladder:

    encv' (tower n) d       = ladderCols d (n+1)              = (d,0), (d+1,0), …, (d+n,0)
    encv' (fsEE n)  0       = (0,0) :: (1,1) :: ladderCols 2 (n+1)

`ladderCols` exists so the index arithmetic lives in ONE place: `ladderCols_succ` and
`shiftD_ladderCols` are the only two lemmas that ever see a `+`, and every row proof composes them
instead of re-deriving `i + d + e = i + (d + e)`.

**AND THE FUEL RECURSION IS UNFOLDED AT A SYMBOLIC INDEX FOR THE SECOND TIME, BY THE OTHER OF THE
TWO TECHNIQUES.**  §20's `fpDeep_none_of_empty` worked because the branch is decided at the first
step.  Here `fpDeep` must DESCEND the whole tower, so that does not apply — and `fpDeepF_tower`
inducts on the FUEL with the tower's height universally quantified, so the fuel and the height are
stepped down together and never have to be related.  §9's blocker is qualified in place with both
techniques named; what it feared — comparing `encvF 22` against `encvF 30` for the same term — is
the one shape neither covers, and no row has needed it.

**`fpDeepF_tower` IS STATED OVER AN ARBITRARY FIRST ARGUMENT** with `isFP a (tower m) = false` as a
hypothesis, because `a = 0` (inside the tower) and `a = 1` (at the row's head) both occur and the
proof is identical.  Second-caller generality again, this time noticed before writing rather than
after — §20's note is what made me look. -/

theorem splitFin_isAP {x : Term} (hx : x.isAP = true) (hne : (x == one) = false) :
    TM.Term.splitFin x = (x, 0) := splitFin_repAdd hx hne 0

theorem isFP_zero_tower : ∀ n, TM.Term.isFP zero (Evidence.WF.tower n) = false
  | 0 => rfl
  | _ + 1 => rfl

theorem tower_ne_one : ∀ n, (Evidence.WF.tower (n + 1) == one) = false := by
  intro n
  have : Evidence.WF.tower (n + 1) ≠ one := by
    intro hc
    have h0 := Evidence.WF.tower_ne_zero n
    injection hc with _ h2
    exact h0 h2
  simpa using this

theorem summands_splitFin_tower_succ (k : Nat) :
    summands (TM.Term.splitFin (Evidence.WF.tower (k + 1))).1 = [Evidence.WF.tower (k + 1)] := by
  rw [splitFin_isAP (x := Evidence.WF.tower (k + 1)) rfl (tower_ne_one k)]; rfl

/-- **`fpDeep` NEVER FIRES INSIDE AN ω-TOWER** — induction on the FUEL with the height
    universally quantified, so the fuel never has to be related to the height. -/
theorem fpDeepF_tower (a : Term) (ha : ∀ m, TM.Term.isFP a (Evidence.WF.tower m) = false) :
    ∀ (f n : Nat), fpDeepF f a (Evidence.WF.tower n) = none
  | 0, _ => rfl
  | f + 1, 0 => by
    show (if TM.Term.isFP a (phi zero zero) then some (phi zero zero)
          else (summands (TM.Term.splitFin zero).1).findSome? (fpDeepF f a)) = none
    rw [show TM.Term.isFP a (phi zero zero) = false from ha 0]
    rfl
  | f + 1, n + 1 => by
    show (if TM.Term.isFP a (Evidence.WF.tower (n + 1)) then some (Evidence.WF.tower (n + 1))
          else (summands (TM.Term.splitFin (Evidence.WF.tower n)).1).findSome?
                 (fpDeepF f a)) = none
    rw [ha (n + 1)]
    simp only [Bool.false_eq_true, if_false]
    cases n with
    | zero => rfl
    | succ k =>
      rw [summands_splitFin_tower_succ k, List.findSome?_cons, fpDeepF_tower a ha f (k + 1)]
      rfl

theorem isFP_one_tower : ∀ n, TM.Term.isFP one (Evidence.WF.tower n) = false
  | 0 => rfl
  | _ + 1 => rfl

theorem fpDeep_zero_tower (n : Nat) : fpDeep zero (Evidence.WF.tower n) = none :=
  fpDeepF_tower zero isFP_zero_tower _ n

theorem fpDeep_one_tower (n : Nat) : fpDeep one (Evidence.WF.tower n) = none :=
  fpDeepF_tower one isFP_one_tower _ n

theorem cnv_tower : ∀ n, Evidence.WF.CNV (Evidence.WF.tower n) = true
  | 0 => rfl
  | n + 1 => by
    show (Evidence.WF.CNV zero && Evidence.WF.CNV (Evidence.WF.tower n)) = true
    rw [cnv_tower n]; rfl

/-- The increasing column ladder `(d,0), (d+1,0), …` of length `k` — the shape every
    tower-indexed row emits, kept as one definition so the arithmetic lives in one place. -/
def ladderCols (d k : Nat) : List Col2 := (List.range k).map (fun i => ((i + d, 0) : Col2))

theorem ladderCols_succ (d k : Nat) : ladderCols d (k + 1) = (d, 0) :: ladderCols (d + 1) k := by
  show (List.range (k + 1)).map (fun i => ((i + d, 0) : Col2)) = _
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  show ((0 + d, 0) : Col2) :: (List.range k).map (fun i => ((i + 1 + d, 0) : Col2))
     = ((d, 0) : Col2) :: (List.range k).map (fun i => ((i + (d + 1), 0) : Col2))
  simp only [Nat.zero_add]
  congr 1
  apply List.map_congr_left
  intro i _
  congr 1
  omega

theorem shiftD_ladderCols (e d k : Nat) : shiftD e (ladderCols d k) = ladderCols (d + e) k := by
  show ((List.range k).map (fun i => ((i + d, 0) : Col2))).map (fun c => (c.1 + e, c.2)) = _
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  show ((i + d + e, 0) : Col2) = ((i + (d + e), 0) : Col2)
  congr 1
  omega

theorem encv'_tower_succ (n d : Nat) :
    encv' (Evidence.WF.tower (n + 1)) d
      = (d, 0) :: shiftD (d + 1) (encv' (Evidence.WF.tower n) 0) := by
  show (if h : Evidence.WF.CNV (Evidence.WF.tower (n + 1)) = true
        then encvC ⟨Evidence.WF.tower (n + 1), h⟩ d else []) = _
  rw [dif_pos (cnv_tower (n + 1))]
  cases n with
  | zero =>
    show encvC ⟨phi zero one, cnv_tower 1⟩ d = _
    have hgs : summands (TM.Term.splitFin one).1 = [] := rfl
    have hat : (summands (TM.Term.splitFin one).1).attach = [] :=
      List.eq_nil_of_length_eq_zero (by rw [List.length_attach, hgs]; rfl)
    have hfd : ∀ pf, fpDeepC zero ((summands (TM.Term.splitFin one).1).headD zero) pf = none :=
      fun pf => fpDeepC_none pf rfl
    rw [encvC]
    dsimp only
    rw [show TM.Term.isFP zero ((summands (TM.Term.splitFin one).1).headD zero) = false from rfl]
    simp only [Bool.false_eq_true, if_false]
    rw [hfd, hat, show encv' (Evidence.WF.tower 0) 0 = [((0, 0) : Col2)] from encv'_one 0]
    dsimp only
    split
    · simp [shiftD, show (TM.Term.splitFin one).2 = 1 from rfl]
    · exact absurd hgs (by simp_all)
  | succ k =>
    show encvC ⟨phi zero (Evidence.WF.tower (k + 1)), cnv_tower (k + 2)⟩ d = _
    have hgs := summands_splitFin_tower_succ k
    have hm2 : (TM.Term.splitFin (Evidence.WF.tower (k + 1))).2 = 0 := by
      rw [splitFin_isAP (x := Evidence.WF.tower (k + 1)) rfl (tower_ne_one k)]
    have hhd : (summands (TM.Term.splitFin (Evidence.WF.tower (k + 1))).1).headD zero
        = Evidence.WF.tower (k + 1) := by rw [hgs]; rfl
    have hfp : TM.Term.isFP zero
        ((summands (TM.Term.splitFin (Evidence.WF.tower (k + 1))).1).headD zero) = false := by
      rw [hhd]; exact isFP_zero_tower (k + 1)
    have hfd : ∀ pf, fpDeepC zero
        ((summands (TM.Term.splitFin (Evidence.WF.tower (k + 1))).1).headD zero) pf = none :=
      fun pf => fpDeepC_none pf (by rw [hhd]; exact fpDeep_zero_tower (k + 1))
    rw [encvC]
    dsimp only
    rw [hfp]
    simp only [Bool.false_eq_true, if_false]
    rw [hfd, hm2]
    simp only [encvC_eq_encv', show (zero == zero) = true from rfl, if_true]
    rw [List.attach_map_val
          (l := summands (TM.Term.splitFin (Evidence.WF.tower (k + 1))).1)
          (f := fun y => ([] : List Col2) ++ shiftD (d + 1) (encv' y 0))]
    rw [hgs]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.nil_append, List.append_nil, List.replicate_zero]

/-- **THE ω-TOWER'S ENCODING IS THE INCREASING LADDER** — the first row family in this file that
    genuinely needs an induction on `n`, because the block's own encoding grows with `n` rather
    than repeating. -/
theorem encv'_tower : ∀ (n d : Nat), encv' (Evidence.WF.tower n) d = ladderCols d (n + 1)
  | 0, d => by
    rw [show encv' (Evidence.WF.tower 0) d = [((d, 0) : Col2)] from encv'_one d,
        ladderCols_succ d 0]
    rfl
  | n + 1, d => by
    rw [encv'_tower_succ n d, encv'_tower n 0, shiftD_ladderCols, Nat.zero_add,
        ladderCols_succ d (n + 1)]

theorem omLog_tower_succ : ∀ n, omLog (Evidence.WF.tower (n + 1)) = Evidence.WF.tower n
  | 0 => rfl
  | k + 1 => by
    show (match summands (TM.Term.splitFin (Evidence.WF.tower (k + 1))).1 with
          | [g] => if TM.Term.isFP zero g then plus (Evidence.WF.tower (k + 1)) one
                   else Evidence.WF.tower (k + 1)
          | _ => Evidence.WF.tower (k + 1)) = _
    rw [summands_splitFin_tower_succ k]
    show (if TM.Term.isFP zero (Evidence.WF.tower (k + 1)) then
            plus (Evidence.WF.tower (k + 1)) one else Evidence.WF.tower (k + 1)) = _
    rw [isFP_zero_tower (k + 1)]
    rfl

theorem cnv_phi_one_tower (n : Nat) :
    Evidence.WF.CNV (phi one (Evidence.WF.tower n)) = true := by
  show (Evidence.WF.CNV one && Evidence.WF.CNV (Evidence.WF.tower n)) = true
  rw [cnv_tower n]; rfl

/-- **THE `ε_{ε₀}` ROW'S ENCODER FACT, FOR EVERY `n`.** -/
theorem encv'_epsEps0 (n : Nat) :
    encv' (phi one (Evidence.WF.tower (n + 1))) 0
      = (0, 0) :: (1, 1) :: ladderCols 2 (n + 1) := by
  show (if h : Evidence.WF.CNV (phi one (Evidence.WF.tower (n + 1))) = true
        then encvC ⟨phi one (Evidence.WF.tower (n + 1)), h⟩ 0 else []) = _
  rw [dif_pos (cnv_phi_one_tower (n + 1))]
  have hgs := summands_splitFin_tower_succ n
  have hm2 : (TM.Term.splitFin (Evidence.WF.tower (n + 1))).2 = 0 := by
    rw [splitFin_isAP (x := Evidence.WF.tower (n + 1)) rfl (tower_ne_one n)]
  have hhd : (summands (TM.Term.splitFin (Evidence.WF.tower (n + 1))).1).headD zero
      = Evidence.WF.tower (n + 1) := by rw [hgs]; rfl
  have hfp : TM.Term.isFP one
      ((summands (TM.Term.splitFin (Evidence.WF.tower (n + 1))).1).headD zero) = false := by
    rw [hhd]; exact isFP_one_tower (n + 1)
  have hfd : ∀ pf, fpDeepC one
      ((summands (TM.Term.splitFin (Evidence.WF.tower (n + 1))).1).headD zero) pf = none :=
    fun pf => fpDeepC_none pf (by rw [hhd]; exact fpDeep_one_tower (n + 1))
  rw [encvC]
  dsimp only
  rw [hfp]
  simp only [Bool.false_eq_true, if_false]
  rw [hfd, hm2, encvC_predOr_one]
  simp only [encvC_eq_encv', show (one == zero) = false from rfl, Bool.false_eq_true, if_false]
  rw [List.attach_map_val
        (l := summands (TM.Term.splitFin (Evidence.WF.tower (n + 1))).1)
        (f := fun y => ((0 + 1, 1) :: bumpAt (0 + 2) ([] : List Col2))
                ++ shiftD (0 + 2) (encv' (omLog y) 0))]
  rw [hgs]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil]
  rw [omLog_tower_succ n, encv'_tower n 0, shiftD_ladderCols, Nat.zero_add]
  simp only [List.replicate_zero, List.flatten_nil, List.append_nil]
  rfl

/-- The row as the table states it: `fsEE n = φ̄(1, tower (n+1))` by definition. -/
theorem encv'_fsEE (n : Nat) :
    encv' (Evidence.WF.fsEE n) 0 = (0, 0) :: (1, 1) :: ladderCols 2 (n + 1) :=
  encv'_epsEps0 n

#guard (List.range 7).all (fun n => encv' (Evidence.WF.tower n) 0 == ladderCols 0 (n+1))
#guard (List.range 7).all (fun n =>
  encv' (Evidence.WF.fsEE n) 0 == (0,0) :: (1,1) :: ladderCols 2 (n+1))
#guard (List.range 7).all (fun n => encv (Evidence.WF.fsEE n) 0 == encv' (Evidence.WF.fsEE n) 0)
-- the family finding of §20, banked: every Veblen row's subscript summand list is a REPLICATE
#guard (List.range 5).all (fun n => (summands (TM.Term.splitFin (ofNat n)).1).length == 0)
#guard (List.range 5).all (fun n =>
  (summands (TM.Term.splitFin (Evidence.WF.fsC Evidence.WF.omegaSq n)).1).length == n + 1)
#guard (List.range 5).all (fun n =>
  (summands (TM.Term.splitFin (Evidence.WF.fsC Evidence.WF.omegaOmega n)).1).length == 1)
#guard (List.range 5).all (fun n =>
  (summands (TM.Term.splitFin (Evidence.WF.tower (n+1))).1).length == 1)
#guard (List.range 4).all (fun n =>
  (summands (TM.Term.splitFin (Evidence.WF.fsZeta0 n)).1).length == 1)

/-! ## §22 `sqv_decomp` — THE STATEMENT, AND ONE ROW CLOSED END TO END

Five rows had `∀ n` encoder facts and `sqv_decomp` had never been STATED.  Five suppliers and no
consumer is the same bet as predicting a shape without measuring it, and this file has lost that
bet five times tonight; the coordinator called it and was right.  **The statement first, then one
row against it.**

    SqvDecomp t fs'  :=  ∀ n, BMS.expand (sqv' t) n = sqv' (fs' n)

**THE ENCODER COMMUTES WITH EXPANSION.**  That is what `sqv_decomp` has to mean for the ceiling to
consume it: `Cert.lean`'s `Certified.lim` needs `∀ n, Certified (expand M n) (fs' n)`, and the
whole point of the encoder is that `expand` on the matrix side matches `fs` on the term side.

**IT IS STATED AGAINST `sqv'`, NOT `sqv`.**  `sqv` is `toMatrix ∘ encv`, and `encv` is fuelled;
`sqv'` is `toMatrix ∘ encv'`, fuel-free.  §16's agreement `#guard`s say they coincide on all 169
corpus terms and all 215 `CNV` terms at four depths — **measured, not proved**, so the two names
are kept apart and the theorems are about the one that has proofs.

**WHAT THE ROW ACTUALLY NEEDED, AND IT IS EXACTLY WHAT §9 SAID WAS MISSING.**  §9 listed four
pieces for `ε_ω` and called the encoder fact the blocker.  All four are now theorems:

    sqv' (φ̄(1,ω)) = (0,0)(1,1)(2,0)        `sqv'_epsOmega`   — from §19's row at n = 0
    expand … n = epsM n                      `Cert.expand_epsOmega`  (Cert §20, already proved)
    fsEW n = φ̄(1, ofNat n)                   by definition
    encv' (φ̄(1, ofNat n)) 0 = …              `encv'_epsOmega`  (§17)

and the bridge is `sqv'_fsEW : sqv' (fsEW n) = epsM n`, which is `toMatrix` over §17's list.
**Nothing on `Certified`'s side was needed and nothing had to be assumed as a hypothesis** — the
row is `SqvDecomp` for `ε_ω` outright.

**WHAT THIS DOES NOT YET GIVE, STATED SO THE GAP IS VISIBLE AT THE USE SITE.**  `SqvDecomp` is the
EXPANSION half.  `Certified M t` also needs `kind M = .lim` and the three order clauses, and those
are `Evidence.WF.lim_clauses_epsOmega` (proved) — but assembling them into `Certified` requires
`∀ n, Certified (expand M n) (fsEW n)`, i.e. the ε_n rows certified, which is a RECURSION down the
ladder and not part of this section.  **`sqv_decomp` is one input to that recursion, not the whole
of it**, and saying so here is cheaper than discovering it at the assembly. -/

def sqv' (t : Term) : BMS.Matrix := toMatrix (encv' t 0)

/-- **`sqv_decomp`, THE GENERAL STATEMENT.**  Proved per row; no general proof is claimed. -/
def SqvDecomp (t : Term) (fs' : Nat → Term) : Prop :=
  ∀ n, BMS.expand (sqv' t) n = sqv' (fs' n)

theorem sqv'_epsOmega : sqv' (phi one omega) = [[0, 0], [1, 1], [2, 0]] := by
  show toMatrix (encv' (phi one (Evidence.WF.repAdd omega 0)) 0) = _
  rw [encv'_epsOmegaSq 0]
  rfl

theorem sqv'_fsEW (n : Nat) : sqv' (Evidence.WF.fsEW n) = Evidence.Cert.epsM n := by
  show toMatrix (encv' (phi one (ofNat n)) 0) = _
  rw [encv'_epsOmega n]
  show ([0, 0] : List Nat) :: (List.replicate (n + 1) ((1, 1) : Col2)).map (fun c => [c.1, c.2])
     = [[0, 0], [1, 1]] ++ (List.replicate n ([[1, 1]] : BMS.Matrix)).flatten
  rw [List.map_replicate, flatten_replicate_singleton, List.replicate_succ]
  rfl

/-- **`ε_ω` CLOSED END TO END** — the encoder commutes with expansion on the row §9 called the
    cleanest, with nothing assumed. -/
theorem sqv_decomp_epsOmega : SqvDecomp (phi one omega) Evidence.WF.fsEW := by
  intro n
  rw [sqv'_epsOmega, sqv'_fsEW]
  show (BMS.expand? [[0, 0], [1, 1], [2, 0]] n).getD [] = _
  rw [Evidence.Cert.expand_epsOmega n]
  rfl

#guard (List.range 8).all (fun n =>
  BMS.expand (sqv' (phi one omega)) n == sqv' (Evidence.WF.fsEW n))
#guard sqv' (phi one omega) == sqv (phi one omega)
#guard (List.range 8).all (fun n => sqv' (Evidence.WF.fsEW n) == sqv (Evidence.WF.fsEW n))

/-! **THE PREDICTION TALLY, as a fact about the rule rather than about me.**  Six predictions of
mine tonight were refuted by measurement that cost one `#eval` each: `tdepth` at `predOr`, the
named-equation layer (three times), `ε_{ω^ω}`'s subscript being a new shape, and `ε_{ε₀}` needing
induction for the summand-list reason.  **All six were reasonable and all six were wrong, and the
`#eval` was free every time.**  That ratio is the argument for measuring first, stated by someone
who has now paid it six times — and the coordinator's *"a request to characterise something is
worth one `#eval` before it is worth one theorem"* is the same rule from the other side. -/

/-! ## §23 `Certified` FOR `ε_ω` — FOUR PREMISES DISCHARGED, THE FIFTH NAMED

`Certified.lim` has five premises.  Four are proved and the fifth is a whole sub-project, so it is
carried as an explicit HYPOTHESIS at the use site rather than hidden by a narrower statement —
§9's instruction, applied where it bites.

    kind (sqv' ε_ω) = .lim                     decidable
    ∀ n, Certified (expand … n) (fsEW n)       ← `cert_epsN`, THE HYPOTHESIS
    ∀ n, lt (fsEW n) ε_ω                       `Evidence.WF.lim_clauses_epsOmega`
    ∀ n, lt (fsEW n) (fsEW (n+1))              same
    cofinality                                 same

**AND THE MEASUREMENT THAT PUT THE HYPOTHESIS THERE RATHER THAN A RECURSION.**  I proposed
assembling this by recursion down the ε_n ladder.  One `#eval` refuted it before any statement was
written:

    expand (epsM (n+1)) k = epsM m  for some m       ONLY at k = 0, for n = 0,1,2
    expand (epsM 1) 1 = [[0,0],[1,1],[1,0],[2,1]]    oR = φ̄(0, ε₀ ⊕ ε₀) = ω^(ε₀·2)

**Each rung's own fundamental sequence LEAVES the ladder for a tower family one level down** — a
tower over `ε₀·2`, not over `ε₀`.  `Cert.lean` §20 says exactly this at line 8494 and neither lane
read it before proposing the recursion; the `#eval` found it in one step.  **A target written first
would have been wrong in the way that reads as correct**: the ladder is real and the rungs are
real, and only the rungs' fundamental sequences leave it.

`cert_epsN` is `Cert.lean`'s to hold, not this file's — the import arrow is `SqV → Cert`, so a
statement about `Certified` may be USED here and its proof may not cite anything from here. -/

/-- **`ε_ω`'s CERTIFICATE, MODULO THE RUNGS.**  The hypothesis is `cert_epsN`, stated in full at
    the use site so the residue is one named obligation rather than an invisible restriction. -/
theorem cert_epsOmega
    (h : ∀ n, Evidence.Cert.Certified (Evidence.Cert.epsM n) (Evidence.WF.fsEW n)) :
    Evidence.Cert.Certified (sqv' (phi one omega)) (phi one omega) := by
  rw [sqv'_epsOmega]
  obtain ⟨_, hlt, hmono, hcof⟩ := Evidence.WF.lim_clauses_epsOmega
  refine Evidence.Cert.Certified.lim Evidence.WF.fsEW (by decide) ?_ hlt hmono hcof
  intro n
  show Evidence.Cert.Certified ((BMS.expand? [[0, 0], [1, 1], [2, 0]] n).getD []) _
  rw [Evidence.Cert.expand_epsOmega n]
  exact h n

#guard BMS.kind (sqv' (phi one omega)) == BMS.Kind.lim
#guard (List.range 6).all (fun n => BMS.expand (sqv' (phi one omega)) n == Evidence.Cert.epsM n)
-- the rungs leave the ladder: `expand (epsM (n+1)) k` is an `epsM` only at k = 0
#guard (List.range 3).all (fun n => BMS.expand (Evidence.Cert.epsM (n+1)) 0 == Evidence.Cert.epsM n)
#guard (List.range 3).all (fun n => (List.range 3).all (fun k =>
  !((List.range 6).any (fun m => BMS.expand (Evidence.Cert.epsM (n+1)) (k+1) == Evidence.Cert.epsM m))))

/-! ## §24 `SqvDecomp` FOR THE REMAINING ROWS — ONE CLOSES, THREE ARE BLOCKED ON `Cert`

The task was `SqvDecomp` for the other four rows, with each row's `Certified` residue named so the
four residues could be compared.  **One row closes.  Three are blocked, and not on anything in this
file** — `SqvDecomp` needs a `Cert`-side EXPANSION IDENTITY per row, and three of them do not exist:

    row          sqv' t                        `Cert` expansion identity
    ε_ω          (0,0)(1,1)(2,0)               `expand_epsOmega`   ✓  §22
    ω^(ε₀+1)     (0,0)(1,1)(1,0)               `expand_rowA`       ✓  Cert:7831 — closed below
    ε_{ω²}       (0,0)(1,1)(2,0)(2,0)          — MISSING —
    ε_{ω^ω}      (0,0)(1,1)(2,0)(3,0)          — MISSING —
    ε_{ε₀}       (0,0)(1,1)(2,0)(3,1)          — MISSING —

**THE BINDING CONSTRAINT WAS NEVER THE ASSEMBLY'S SHAPE; IT IS THE PER-ROW EXPANSION IDENTITY.**
I had five encoder facts and assumed the consumer side was uniform across the rows they serve.  It
is not, and ONE GREP of `Cert.lean`'s `expand_` theorems showed it — cheaper than the `#eval` that
caught the ε_n ladder, and the same mistake one level up.

**NAMED, NOT SUBSTITUTED.**  The three missing facts are, in `Cert.lean`'s own idiom:

    expand? [[0,0],[1,1],[2,0],[2,0]] n = some …        for ε_{ω²}
    expand? [[0,0],[1,1],[2,0],[3,0]] n = some …        for ε_{ω^ω}
    expand? [[0,0],[1,1],[2,0],[3,1]] n = some …        for ε_{ε₀}

Proving substitutes here would put matrix-expansion facts in the candidate tier, which is what the
import arrow exists to prevent.  `Cert.lean` §7224–7225 already names the last two rows' matrices in
prose, so the shapes are agreed; only the identities are absent.

**TWO RESIDUES, SIDE BY SIDE, WHICH IS WHAT THE TASK WAS FOR.**  `ε_ω`'s residue is
`∀ n, Certified (epsM n) (fsEW n)` — the ε_n rungs, whose own expansions leave the ladder for a
two-column family.  `ω^(ε₀+1)`'s residue is `∀ n, Certified (eps0M n) (fsA n)`, and `eps0M n` is
`(n+1)` copies of `(0,0)(1,1)` — **the SAME block repeated, not a growing ladder.**  Two rows, two
residues, two different shapes already.  **That is one data point against "one family will cover
them", collected before any family was built**, which is exactly what the task was meant to
produce; three more await the missing identities. -/

/-- **THE COLLAPSE BRANCH, FOR THE FIRST TIME** — `ε₀` IS a fixed point of `ω^·`, so
    `isFP 0 ε₀` fires and the head is encoded whole rather than through `mkBlocks`. -/
theorem encv'_rowA_val : encv' Evidence.WF.rowA 0 = [((0, 0) : Col2), (1, 1), (1, 0)] := by
  show (if h : Evidence.WF.CNV (phi zero Evidence.WF.eps0T) = true
        then encvC ⟨phi zero Evidence.WF.eps0T, h⟩ 0 else []) = _
  rw [dif_pos (show Evidence.WF.CNV (phi zero Evidence.WF.eps0T) = true from rfl)]
  have hgs : summands (TM.Term.splitFin Evidence.WF.eps0T).1 = [Evidence.WF.eps0T] := by
    rw [splitFin_isAP (x := Evidence.WF.eps0T) rfl rfl]; rfl
  have hhd : (summands (TM.Term.splitFin Evidence.WF.eps0T).1).headD zero = Evidence.WF.eps0T := by
    rw [hgs]; rfl
  have hm2 : (TM.Term.splitFin Evidence.WF.eps0T).2 = 0 := by
    rw [splitFin_isAP (x := Evidence.WF.eps0T) rfl rfl]
  rw [encvC]
  dsimp only
  rw [show TM.Term.isFP zero ((summands (TM.Term.splitFin Evidence.WF.eps0T).1).headD zero) = true
        from by rw [hhd]; rfl]
  simp only [if_true]
  rw [hm2, encvC_eq_encv', hhd, encv'_eps0T,
      show ((summands (TM.Term.splitFin Evidence.WF.eps0T).1).length == 1) = true from by
        rw [hgs]; rfl]
  simp only [if_true, List.replicate_zero, List.flatten_nil, List.append_nil]
  rfl

theorem sqv'_rowA : sqv' Evidence.WF.rowA = [[0, 0], [1, 1], [1, 0]] := by
  show toMatrix (encv' Evidence.WF.rowA 0) = _
  rw [encv'_rowA_val]
  rfl

theorem sqv'_fsA (n : Nat) : sqv' (Evidence.WF.fsA n) = Evidence.Cert.eps0M n := by
  show toMatrix (encv' (Evidence.WF.fsA n) 0) = _
  rw [encv'_rowA n]
  show ((List.replicate (n + 1) [((0, 0) : Col2), (1, 1)]).flatten).map (fun c => [c.1, c.2])
     = (List.replicate (n + 1) ([[0, 0], [1, 1]] : BMS.Matrix)).flatten
  rw [List.map_flatten, List.map_replicate]
  rfl

/-- **`ω^(ε₀+1)` CLOSED END TO END** — the second row, by the same three lines as `ε_ω`. -/
theorem sqv_decomp_rowA : SqvDecomp Evidence.WF.rowA Evidence.WF.fsA := by
  intro n
  rw [sqv'_rowA, sqv'_fsA]
  show (BMS.expand? [[0, 0], [1, 1], [1, 0]] n).getD [] = _
  rw [Evidence.Cert.expand_rowA n]
  rfl

#guard sqv' Evidence.WF.rowA == [[0, 0], [1, 1], [1, 0]]
#guard (List.range 6).all (fun n => sqv' (Evidence.WF.fsA n) == Evidence.Cert.eps0M n)
#guard (List.range 6).all (fun n =>
  BMS.expand (sqv' Evidence.WF.rowA) n == sqv' (Evidence.WF.fsA n))
#guard sqv' Evidence.WF.epsOmegaSq == [[0, 0], [1, 1], [2, 0], [2, 0]]
#guard sqv' (phi one Evidence.WF.omegaOmega) == [[0, 0], [1, 1], [2, 0], [3, 0]]
#guard sqv' (phi one (phi one zero)) == [[0, 0], [1, 1], [2, 0], [3, 1]]
-- the two residues differ in shape: `epsM n` grows a ladder, `eps0M n` repeats one block
#guard Evidence.Cert.epsM 2 == [[0, 0], [1, 1], [1, 1], [1, 1]]
#guard Evidence.Cert.eps0M 2 == [[0, 0], [1, 1], [0, 0], [1, 1], [0, 0], [1, 1]]

/-! ## §24 THE REMAINING THREE ROWS — `SqvDecomp` FOR ALL FIVE

§22 closed `ε_ω` and §18.1's row A.  The other three waited on their `Cert`-side `expand?`
identity, which was the binding constraint rather than the shape of anything here; all five now
exist, so these are assembly.

**`sqv'` OF A ROW CANNOT BE PROVED BY `decide` OR `rfl`.**  `encv'` is defined by WELL-FOUNDED
RECURSION, so the kernel cannot unfold it — `#eval` prints a value because it runs compiled code,
and that is not the same thing.  Every `encv'` value in this file comes from a named equation, and
`sqv'_epsEps0` below needs one that did not exist: `encv'_epsEps0` is about the row's FUNDAMENTAL
SEQUENCE `φ̄(1, tower (n+1))`, and the row itself is `φ̄(1, ε₀)`, a different term.
-/

theorem sqv'_epsOmegaSq :
    sqv' Evidence.WF.epsOmegaSq = [[0, 0], [1, 1], [2, 0], [2, 0]] := by
  show toMatrix (encv' (phi one (phi zero (ofNat (1 + 1)))) 0) = _
  rw [encv'_epsOmegaOmega 1]
  rfl

theorem sqv'_fsEW2 (n : Nat) :
    sqv' (Evidence.WF.fsEW2 n)
      = [[0, 0]] ++ (List.replicate (n + 1) ([[1, 1], [2, 0]] : BMS.Matrix)).flatten := by
  show toMatrix (encv' (Evidence.WF.fsEW2 n) 0) = _
  rw [encv'_fsEW2 n]
  show ([0, 0] : List Nat) ::
      ((List.replicate (n + 1) [((1, 1) : Col2), (2, 0)]).flatten).map (fun c => [c.1, c.2])
    = [[0, 0]] ++ (List.replicate (n + 1) ([[1, 1], [2, 0]] : BMS.Matrix)).flatten
  rw [List.map_flatten, List.map_replicate]
  rfl

theorem sqv_decomp_epsOmegaSq : SqvDecomp Evidence.WF.epsOmegaSq Evidence.WF.fsEW2 := by
  intro n
  rw [sqv'_epsOmegaSq, sqv'_fsEW2]
  show (BMS.expand? [[0, 0], [1, 1], [2, 0], [2, 0]] n).getD [] = _
  rw [Evidence.Cert.expand_epsOmegaSq n]
  rfl

theorem sqv'_epsOmegaOmega :
    sqv' Evidence.WF.epsOmegaOmega = [[0, 0], [1, 1], [2, 0], [3, 0]] := by
  show toMatrix (encv' (phi one (Evidence.WF.tower (1 + 1))) 0) = _
  rw [encv'_epsEps0 1]
  rfl

theorem sqv'_fsEWW (n : Nat) :
    sqv' (Evidence.WF.fsEWW n)
      = [[0, 0], [1, 1]] ++ (List.replicate (n + 1) ([[2, 0]] : BMS.Matrix)).flatten := by
  show toMatrix (encv' (Evidence.WF.fsEWW n) 0) = _
  rw [encv'_fsEWW n]
  show ([0, 0] : List Nat) :: [1, 1] ::
      (List.replicate (n + 1) ((2, 0) : Col2)).map (fun c => [c.1, c.2])
    = [[0, 0], [1, 1]] ++ (List.replicate (n + 1) ([[2, 0]] : BMS.Matrix)).flatten
  rw [List.map_replicate, flatten_replicate_singleton]
  rfl

theorem sqv_decomp_epsOmegaOmega : SqvDecomp Evidence.WF.epsOmegaOmega Evidence.WF.fsEWW := by
  intro n
  rw [sqv'_epsOmegaOmega, sqv'_fsEWW]
  show (BMS.expand? [[0, 0], [1, 1], [2, 0], [3, 0]] n).getD [] = _
  rw [Evidence.Cert.expand_epsOmegaOmega n]
  rfl

/-- The encoder fact for the ROW `φ̄(1,ε₀)`, which no lemma supplied: `encv'_epsEps0` is about
    `φ̄(1, tower (n+1))`, and `epsEps0 == fsEE 0` is FALSE. -/
theorem encv'_epsEps0_row :
    encv' Evidence.WF.epsEps0 0 = [((0, 0) : Col2), (1, 1), (2, 0), (3, 1)] := by
  show (if h : Evidence.WF.CNV (phi one Evidence.WF.eps0T) = true
        then encvC ⟨phi one Evidence.WF.eps0T, h⟩ 0 else []) = _
  rw [dif_pos (show Evidence.WF.CNV (phi one Evidence.WF.eps0T) = true from rfl)]
  have hgs : summands (TM.Term.splitFin Evidence.WF.eps0T).1 = [Evidence.WF.eps0T] := by
    rw [splitFin_isAP (x := Evidence.WF.eps0T) rfl rfl]; rfl
  have hm2 : (TM.Term.splitFin Evidence.WF.eps0T).2 = 0 := by
    rw [splitFin_isAP (x := Evidence.WF.eps0T) rfl rfl]
  have hhd : (summands (TM.Term.splitFin Evidence.WF.eps0T).1).headD zero = Evidence.WF.eps0T := by
    rw [hgs]; rfl
  have hfp : TM.Term.isFP one
      ((summands (TM.Term.splitFin Evidence.WF.eps0T).1).headD zero) = false := by
    rw [hhd]; rfl
  have hfd : ∀ pf, fpDeepC one
      ((summands (TM.Term.splitFin Evidence.WF.eps0T).1).headD zero) pf = none :=
    fun pf => fpDeepC_none pf (by rw [hhd]; rfl)
  rw [encvC]
  dsimp only
  rw [hfp]
  simp only [Bool.false_eq_true, if_false]
  rw [hfd, hm2, encvC_predOr_one]
  simp only [encvC_eq_encv', show (one == zero) = false from rfl, Bool.false_eq_true, if_false]
  rw [List.attach_map_val
    (l := summands (TM.Term.splitFin Evidence.WF.eps0T).1)
    (f := fun y => ((0 + 1, 1) :: bumpAt (0 + 2) ([] : List Col2)) ++
      shiftD (0 + 2) (encv' (omLog y) 0))]
  rw [hgs]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil]
  rw [show omLog Evidence.WF.eps0T = Evidence.WF.eps0T from rfl, encv'_eps0T]
  rfl

theorem sqv'_epsEps0 :
    sqv' Evidence.WF.epsEps0 = [[0, 0], [1, 1], [2, 0], [3, 1]] := by
  show toMatrix (encv' Evidence.WF.epsEps0 0) = _
  rw [encv'_epsEps0_row]
  rfl

theorem sqv'_fsEE (n : Nat) :
    sqv' (Evidence.WF.fsEE n)
      = [[0, 0], [1, 1]] ++ ((List.range (n + 1)).map (fun a => [2 + a, 0])) := by
  show toMatrix (encv' (Evidence.WF.fsEE n) 0) = _
  rw [encv'_fsEE n]
  simp [toMatrix, ladderCols, List.map_map, Nat.add_comm]

theorem sqv_decomp_epsEps0 : SqvDecomp Evidence.WF.epsEps0 Evidence.WF.fsEE := by
  intro n
  rw [sqv'_epsEps0, sqv'_fsEE]
  show (BMS.expand? [[0, 0], [1, 1], [2, 0], [3, 1]] n).getD [] = _
  rw [Evidence.Cert.expand_epsEps0 n]
  rfl

#guard (List.range 6).all (fun n =>
  BMS.expand (sqv' Evidence.WF.epsOmegaSq) n == sqv' (Evidence.WF.fsEW2 n))
#guard (List.range 6).all (fun n =>
  BMS.expand (sqv' Evidence.WF.epsOmegaOmega) n == sqv' (Evidence.WF.fsEWW n))
#guard (List.range 6).all (fun n =>
  BMS.expand (sqv' Evidence.WF.epsEps0) n == sqv' (Evidence.WF.fsEE n))

/-! ## §25 THE GENERAL CERTIFICATE — what the route measurement says, and the one
    theorem that decides the architecture

The goal is `∀ t, CNV t → Certified (sqv' t) t`: one theorem instead of one per row.
Measured payoff at the time of writing: 13 unregistered table rows have `sqv' t = m`.

**MEASUREMENT 1 — `kind` agrees everywhere.**  One of `Certified.lim`'s five premises,
settled: `BMS.kind (sqv' t)` matches `Evidence.WF.kindV t` on all 169 terms of
`agreeCorpus`, 0 failures.

**MEASUREMENT 2 — `NfOK t` ⟺ `t` CONTAINS NO SKIP NODE**, exactly, on both corpora
(169 and 215, 0 disagreements).  A "skip node" is a `φ̄(a,b)` at which `phiNF` and the
raw constructor disagree — `φ̄` enumerates the additive principals SKIPPING the fixed
points of `ω^·`, so `φ̄(0,ε₀) = ω^(ε₀+1) ≠ ε₀ = phiNF 0 ε₀`.  34 of 169 are such terms,
and **`Evidence.WF.rowA` is one of them** — an already-registered ✅ whose certificate
does not go through the assembly.  So `NfOK` is *not* necessary for certification; it
is core (C)'s side condition.  Of the 13 target rows, **11 are `NfOK` and 2 are not**
(`ω^(ζ₀+1)`, `ε_{ζ₀+1}`), and those two are `rowA`'s shape.
See `table/nfok-reach-2026-08-10.txt`.

**AND THE ARCHITECTURAL FINDING, WHICH IS A THEOREM AND NOT A MEASUREMENT.**
`Evidence.WF.asm_generalB'` exports `∃ fs, LimClauses t fs`.  That existential
**cannot** discharge `SqvDecomp`'s identity premise, because `LimClauses` is closed
under a tail shift (`lim_clauses_shift_k`) while `SqvDecomp` is index-sensitive:

    LimClauses ε_ω (fun n => fsEW (n+1))        holds
    SqvDecomp  ε_ω (fun n => fsEW (n+1))        FAILS at n = 0

`limClauses_not_enough` below proves both halves.  Of the 95 `NfOK` limits in the
corpus, only 10 have a sequence the assembly interface determines; 85 are opaque to
it.  **So the general certificate needs a sequence FUNCTION that tracks expansion —
`fsV : Term → Nat → Term` with `expand (sqv' t) n = sqv' (fsV t n)` — and then a proof
that it satisfies `LimClauses`.  The existential interface is the wrong direction**,
and the five proved rows already work the right way round: each names its own `fs`
and proves the decomposition against that name.
-/

def kindAgrees (t : Term) : Bool :=
  if t == zero then BMS.kind (sqv' t) == BMS.Kind.zero
  else if Evidence.WF.kindV t then BMS.kind (sqv' t) == BMS.Kind.succ
  else BMS.kind (sqv' t) == BMS.Kind.lim

def kindFailures : List Term := agreeCorpus.filter (fun t => !(kindAgrees t))

def nfFailures : List Term := agreeCorpus.filter (fun t => !(Evidence.WF.NfOK t))

/-- A term contains a Veblen node whose argument is already a fixed-point shape
    for that node's index, so the raw constructor invokes the skip convention. -/
def hasSkip : Term → Bool
  | .zero | .M => false
  | .add u v => hasSkip u || hasSkip v
  | .omg a => hasSkip a
  | .phi a b => TM.Term.isFP a b || hasSkip a || hasSkip b
  | .psi k a => hasSkip k || hasSkip a
  | .Z a => hasSkip a

/-- Whether `asm_generalB'` reaches a branch whose returned sequence is hidden
    behind a propositional existential: `Hsucc`, or core (C)'s shifted tail. -/
def asmSequenceOpaque : Term → Bool
  | .phi p q =>
      if q == zero then
        if Evidence.WF.kindV p then false else asmSequenceOpaque p
      else true
  | .add _ v => asmSequenceOpaque v
  | _ => false

/-- The part of `asm_generalB'`'s witness that is computationally determined by
    its proof.  Opaque branches return `none`; no replacement sequence is guessed. -/
def asmSequence? : Term → Nat → Option Term
  | .phi p q, n =>
      if q == zero then
        if Evidence.WF.kindV p then
          some (Evidence.WF.fsGen
            (phi (Evidence.WF.predC p) zero)
            (Evidence.WF.predC p)
            (phi (Evidence.WF.predC p) zero) n)
        else (asmSequence? p n).map (fun x => phi x zero)
      else none
  | .add u v, n => (asmSequence? v n).map (fun x => add u x)
  | _, _ => none

def nfOKCorpus : List Term :=
  agreeCorpus.filter (fun t => Evidence.WF.NfOK t)

def nfOKLimitCorpus : List Term := nfOKCorpus.filter (fun t =>
  !(t == zero) && !(Evidence.WF.kindV t))

def opaqueAsmCorpus : List Term :=
  nfOKLimitCorpus.filter asmSequenceOpaque

def determinedAsmCorpus : List Term :=
  nfOKLimitCorpus.filter (fun t => !(asmSequenceOpaque t))

def determinedDecompFailures : List Term := determinedAsmCorpus.filter (fun t =>
  !((List.range 4).all (fun n => match asmSequence? t n with
    | some s => BMS.expand (sqv' t) n == sqv' s
    | none => false)))

-- Measurement corpus: `agreeCorpus`, 169 distinct CNV terms.
#guard agreeCorpus.length == 169
#guard kindFailures.length == 0
#guard nfFailures.length == 34
#guard nfFailures.head? == some Evidence.WF.rowA


-- First five corpus failures, rendered by the term system's own printer.
#guard (nfFailures.take 5).map (fun t => t.toStr) ==
  ["phi(0,phi(phi(0,0),0))",
   "phi(0,phi(phi(0,0),phi(0,0)))",
   "phi(0,phi(phi(0,0)+phi(0,0),0))",
   "phi(phi(0,0),phi(phi(0,0)+phi(0,0),0))",
   "phi(0,phi(0,phi(phi(0,0),0)))"]
#eval (nfFailures.take 5).map (fun t => t.toStr)

-- Exact measured separator on both existing CNV corpora:
-- `NfOK t` holds exactly when `t` contains no skip node.
#guard (agreeCorpus.filter (fun t =>
  !(Evidence.WF.NfOK t == !(hasSkip t)))).length == 0
#guard cnvAll.length == 215
#guard (cnvAll.filter (fun t => !(Evidence.WF.NfOK t))).length == 34
#guard (cnvAll.filter (fun t =>
  !(Evidence.WF.NfOK t == !(hasSkip t)))).length == 0

-- Route measurement for the requested general decomposition.
#guard nfOKCorpus.length == 135
#guard nfOKLimitCorpus.length == 95
#guard opaqueAsmCorpus.length == 85
#guard determinedAsmCorpus.length == 10
#guard determinedDecompFailures.length == 0
#eval (opaqueAsmCorpus.take 5).map (fun t => t.toStr)

-- `LimClauses` is closed under a tail shift (`lim_clauses_shift_k`), but
-- decomposition is index-sensitive.  Thus the existential assembly interface
-- does not determine the sequence needed by `SqvDecomp`.
#guard !(BMS.expand (sqv' Evidence.WF.epsOmega) 0 ==
  sqv' (Evidence.WF.fsEW (0 + 1)))

/-- The assembly's exported `LimClauses` predicate does not determine the
    index-sensitive sequence required by `SqvDecomp`: even a one-step tail of
    a valid sequence is still valid, but no longer matches expansion at zero. -/
theorem limClauses_not_enough :
    Evidence.WF.LimClauses Evidence.WF.epsOmega
      (fun n => Evidence.WF.fsEW (n + 1)) ∧
    ¬ SqvDecomp Evidence.WF.epsOmega
      (fun n => Evidence.WF.fsEW (n + 1)) := by
  constructor
  · exact Evidence.WF.lim_clauses_shift_k (by decide)
      Evidence.WF.lim_clauses_epsOmega 1
  · intro h
    have h0 := h 0
    change BMS.expand (sqv' (phi one omega)) 0 =
      sqv' (Evidence.WF.fsEW 1) at h0
    rw [sqv_decomp_epsOmega 0, sqv'_fsEW, sqv'_fsEW] at h0
    exact (by decide : Evidence.Cert.epsM 0 ≠ Evidence.Cert.epsM 1) h0

#print axioms limClauses_not_enough

/-! ### §25.1 NO EXISTING SEQUENCE TRACKS EXPANSION — the candidate table

§25 proves the assembly's existential cannot supply `SqvDecomp`'s sequence, so the
general certificate needs a FUNCTION `fsV : Term → Nat → Term` with
`expand (sqv' t) n = sqv' (fsV t n)`.  Every function this project already has was
measured against that, over `nfOKLimitCorpus` (95 terms):

    candidate                 failures / 95   first failure
    fsC                            54         ε₀
    fsN at shift 0                 92         ε₀
    fsN at shift +1                27         φ̄(ω,0)
    fsVDirect (WF §15.3's form)    54         ε₀

**NONE IS CLEAN.**  The best is `fsN`+1 at 27 failures, and it fails on a term this
table has a certified row for.

**AND THE FIRST FAILURE IS THE TELL.**  Three of the four fail first at ε₀ — a row
that IS certified (`cert_eps0`).  Its certificate uses `tower` as `fs'`, not `fsC`.
So the expansion-tracking sequence is **determined by the matrix**, and no
term-level fundamental-sequence function in this project computes it.

That is the specification of what must be defined, not a reason to stop: `fsV` has
to be built by the same case analysis `encv'` uses, and the five proved rows
(§17–§21) are its specification — each names its own sequence and proves the
decomposition against that name.
-/

def decompFailures (f : Term → Nat → Term) : List Term :=
  nfOKLimitCorpus.filter (fun t =>
    !((List.range 4).all (fun n =>
      BMS.expand (sqv' t) n == sqv' (f t n))))

def fsCFailures : List Term := decompFailures Evidence.WF.fsC

def fsN0Failures : List Term := decompFailures TM.Term.fsN

def fsN1Failures : List Term :=
  decompFailures (fun t n => TM.Term.fsN t (n + 1))

/-- The direct recursive Veblen sequence tested in WF §15.3.  This is the
    historical candidate verbatim, including its corrected zero-tail guard. -/
def fsVDirect : Term → Nat → Term
  | .add u v, n =>
      let w := fsVDirect v n
      if w == TM.Term.zero then u else .add u w
  | .phi a b, n =>
      if a == TM.Term.zero && b == TM.Term.zero then TM.Term.zero
      else if b == TM.Term.zero then
        if Evidence.WF.kindV a then
          Evidence.WF.iterPhi (Evidence.WF.predC a) TM.Term.zero n
        else .phi (fsVDirect a n) TM.Term.zero
      else if Evidence.WF.kindV b then
        if a == TM.Term.zero then
          Evidence.WF.repAdd (.phi TM.Term.zero (Evidence.WF.predC b)) n
        else if Evidence.WF.kindV a then
          Evidence.WF.iterPhi (Evidence.WF.predC a)
            (.add (.phi a (Evidence.WF.predC b)) TM.Term.one) n
        else
          .phi (fsVDirect a n)
            (.add (.phi a (Evidence.WF.predC b)) TM.Term.one)
      else .phi a (fsVDirect b n)
  | _, _ => TM.Term.zero

def fsVDirectFailures : List Term := decompFailures fsVDirect

def fiveBundles : List (Term × (Nat → Term)) :=
  [(Evidence.WF.epsOmega, Evidence.WF.fsEW),
   (Evidence.WF.rowA, Evidence.WF.fsA),
   (Evidence.WF.epsOmegaSq, Evidence.WF.fsEW2),
   (Evidence.WF.epsOmegaOmega, Evidence.WF.fsEWW),
   (Evidence.WF.epsEps0, Evidence.WF.fsEE)]

def fsVDirectBundleFailures : List Term :=
  fiveBundles.filterMap (fun p =>
    if (List.range 4).all (fun n => fsVDirect p.1 n == p.2 n)
    then none else some p.1)

#guard nfOKLimitCorpus.length == 95

#guard fsCFailures.length == 54
#guard fsCFailures.head? == some Evidence.WF.eps0T
#guard fsN0Failures.length == 92
#guard fsN0Failures.head? == some Evidence.WF.eps0T
#guard fsN1Failures.length == 27
#guard fsN1Failures.head? == some Evidence.WF.phiW0
#guard fsVDirectFailures.length == 54
#guard fsVDirectFailures.head? == some Evidence.WF.eps0T
#guard fsVDirectBundleFailures ==
  [Evidence.WF.epsOmega, Evidence.WF.rowA, Evidence.WF.epsEps0]

#guard !(BMS.expand (sqv' Evidence.WF.eps0T) 0 ==
  sqv' (Evidence.WF.fsC Evidence.WF.eps0T 0))
#guard !(BMS.expand (sqv' Evidence.WF.eps0T) 0 ==
  sqv' (TM.Term.fsN Evidence.WF.eps0T 0))
#guard !(BMS.expand (sqv' Evidence.WF.phiW0) 0 ==
  sqv' (TM.Term.fsN Evidence.WF.phiW0 1))
#guard !(BMS.expand (sqv' Evidence.WF.eps0T) 0 ==
  sqv' (fsVDirect Evidence.WF.eps0T 0))

#eval (fsCFailures.length,
  (fsCFailures.take 1).map TM.Term.toStr)
#eval (fsN0Failures.length,
  (fsN0Failures.take 1).map TM.Term.toStr)
#eval (fsN1Failures.length,
  (fsN1Failures.take 1).map TM.Term.toStr)
#eval (fsVDirectFailures.length,
  (fsVDirectFailures.take 1).map TM.Term.toStr)
#eval (fsVDirectBundleFailures.length,
  fsVDirectBundleFailures.map TM.Term.toStr)


/-! ### §25.2 `fsV` — THE SEQUENCE FUNCTION, MEASURED CLEAN ON ALL 95

§25 proves `LimClauses` cannot supply `SqvDecomp`'s sequence (`limClauses_not_enough`),
so it has to be computed from `t`.  §25.1 measured every existing fundamental-sequence
function and none was clean: `fsC` 54 failures of 95, `fsN` at shift 0 92, at shift +1
27, `fsVDirect` 54.

`fsV` is built from the case analysis `encv'` itself uses, and it is clean:

    #guard decompFailures fsV == []          -- 0 of 95

    fsV eps0T           = tower              #guard at n < 8
    fsV epsOmega        = fsEW
    fsV rowA            = fsA
    fsV epsOmegaSq      = fsEW2
    fsV epsOmegaOmega   = fsEWW
    fsV epsEps0         = fsEE

**It reproduces all six previously proved rows' sequences exactly** — they were its
specification and they are now its calibration points, so a future edit that breaks a
row breaks the build.

HOW IT GOT THERE, because the intermediate is the interesting part.  A first version
(`fsV1`) reached 22 failures of 95, and bucketing them by which `encv'` clause the
failing term takes localised the residue to ONE branch:

    collapse 1 · deep 3 · base-empty 0 · base-block 17 · add 1 · other 0

17 of 22 in the `mkBlocks` site, and `base-empty` — the clause four of the five proved
rows go through — already clean.  The fix is the `Bool` flag threaded through `fsVF`:
it records whether the term is at the ROOT or is the exponent encoded by a nonzero-index
`mkBlocks` site, and those two need different sequences.  **A single failure count would
not have shown that; the histogram did.**

**NOT PROVED.**  `decompFailures fsV == []` is a `#guard` over 95 terms, not
`∀ t, CNV t → ∀ n, expand (sqv' t) n = sqv' (fsV t n)`.  What exists is the function
the theorem needs, with its calibration pinned by executable checks.

KNOWN FOLLOW-UP: `fsVF` carries fuel (`2 * t.deg + 8`), exactly as `encvF` did before
§16 replaced it with the fuel-free `encv'`.  The same move is available here and the
same reason applies — a fuel-carrying definition cannot be inducted over.
-/

def unOmLogV : Term → Term
  | .zero => TM.Term.zero
  | t@(.phi a _) => if a == TM.Term.zero then .phi TM.Term.zero t else t
  | t => .phi TM.Term.zero t

/-- Expansion-tracking recursion.  The Boolean records whether the term is at
    the root or is the exponent encoded by a nonzero-index `mkBlocks` site. -/
def fsVF : Nat → Bool → Term → Nat → Term
  | 0, _, _, _ => TM.Term.zero
  | f + 1, true, .add u v, n =>
      let w := fsVF f true v n
      if w == TM.Term.zero then u else .add u w
  | f + 1, true, t, n =>
      if omLog t == t then unOmLogV (fsVF f false t n)
      else if t == TM.Term.omega then TM.Term.ofNat n
      else fsVF f false t n
  | f + 1, false, .add u v, n =>
      let w := fsVF f false v n
      if w == TM.Term.zero then u else .add u w
  | f + 1, false, .phi a b, n =>
      if a == TM.Term.zero && b == TM.Term.zero then TM.Term.zero
      else if b == TM.Term.zero then
        if Evidence.WF.kindV a then
          let p := Evidence.WF.predC a
          Evidence.WF.fsGen (.phi p TM.Term.zero) p (.phi p TM.Term.zero) n
        else .phi (fsVF f false a (n + 1)) TM.Term.zero
      else if Evidence.WF.kindV b then
        let c := .phi a (Evidence.WF.predC b)
        if a == TM.Term.zero then Evidence.WF.repAdd c n
        else if Evidence.WF.kindV a then
          let p := Evidence.WF.predC a
          let v := if p == TM.Term.zero then c else .phi p c
          let base := if p == TM.Term.zero then .add c c else v
          Evidence.WF.fsGen v p base n
        else .phi (fsVF f false a (n + 1)) c
      else
        let gs := summands (TM.Term.splitFin b).1
        let head := gs.headD TM.Term.zero
        if TM.Term.isFP a head then
          if gs.length == 1 then
            if a == TM.Term.zero then Evidence.WF.repAdd head n
            else .phi a (fsVF f false b n)
          else
            let tail : List Term := match n, gs.getLast? with
              | 0, _ => []
              | _, some g => [fsVF f false g n]
              | _, none => []
            .phi a (TM.Term.ofList (gs.dropLast ++ tail))
        else match fpDeep a head with
          | some _ => .phi a (fsVF f false b n)
          | none =>
              if a == TM.Term.zero || gs.isEmpty then
                .phi a (fsVF f false b n)
              else .phi a (fsVF f true b n)
  | _ + 1, false, _, _ => TM.Term.zero

/-- The term sequence selected by the expansion structure of `sqv' t`. -/
def fsV (t : Term) (n : Nat) : Term :=
  fsVF (2 * t.deg + 8) false t n

-- Measurement corpus: all 95 `NfOK` limits in `agreeCorpus`.
#guard nfOKLimitCorpus.length == 95
#guard decompFailures fsV == []

-- The six previously proved rows are the defining calibration points.
#guard (List.range 8).all (fun n =>
  fsV Evidence.WF.eps0T n == Evidence.WF.tower n)
#guard (List.range 8).all (fun n =>
  fsV Evidence.WF.epsOmega n == Evidence.WF.fsEW n)
#guard (List.range 8).all (fun n =>
  fsV Evidence.WF.rowA n == Evidence.WF.fsA n)
#guard (List.range 8).all (fun n =>
  fsV Evidence.WF.epsOmegaSq n == Evidence.WF.fsEW2 n)
#guard (List.range 8).all (fun n =>
  fsV Evidence.WF.epsOmegaOmega n == Evidence.WF.fsEWW n)
#guard (List.range 8).all (fun n =>
  fsV Evidence.WF.epsEps0 n == Evidence.WF.fsEE n)

/-! ### §25.3 TOWARD `sqvDecomp_general` — the ε₀ case and the `add` clause

The target is `∀ t, CNV t → kindV t = false → t ≠ 0 → ∀ n,
expand (sqv' t) n = sqv' (fsV t n)`.  §25.2 built `fsV` and measured it clean on all
95; this section proves the first cases against it.

**PROVED HERE:**

* `sqvDecomp_eps0_fsV` — the ε₀ case.  Not an arbitrary starting point: ε₀ is where
  three of the four candidate sequences of §25.1 failed FIRST, because `cert_eps0`
  uses `tower` and none of `fsC` / `fsN` / `fsVDirect` computes it.  `fsV_eps0` shows
  `fsV` does.
* `sqv'_add_append` and its two supporting lemmas — the `add` clause, i.e. the
  structural half of the sum branch.
* `encvC_head`, `fpDeepC_some_ne_zero` and the `fpDeepF` lemma under it —
  infrastructure the `φ̄` branches need.

**NOT PROVED:** the general statement.  The remaining clauses are the `φ̄` ones, which
is where §25.2's failure histogram put the last obstruction before `fsV` was fixed
(`base-block`, the `mkBlocks` site).

`fsV` still carries fuel through `fsVF`, and §25.2 records why that has to be dealt
with before an induction over the term can close: a fuel-carrying definition cannot
be inducted over, which is §9's blocker in its original form.  §16 solved that once by
redefining fuel-free rather than by proving a saturation lemma, and the same move is
available here.
-/

theorem fsGen_zero_one_eq_tower :
    ∀ n, Evidence.WF.fsGen one zero one n = Evidence.WF.tower n
  | 0 => rfl
  | n + 1 => by
      show Evidence.WF.iterPhi zero one (n + 1) = Evidence.WF.tower (n + 1)
      induction n with
      | zero => rfl
      | succ n ih =>
          show phi zero (Evidence.WF.iterPhi zero one (n + 1)) =
            phi zero (Evidence.WF.tower (n + 1))
          rw [ih]

theorem fsV_eps0 (n : Nat) :
    fsV Evidence.WF.eps0T n = Evidence.WF.tower n := by
  unfold fsV
  rw [show Evidence.WF.eps0T = phi one zero from rfl]
  change Evidence.WF.fsGen one zero one n = Evidence.WF.tower n
  exact fsGen_zero_one_eq_tower n

theorem sqv'_eps0 : sqv' Evidence.WF.eps0T = [[0, 0], [1, 1]] := by
  unfold sqv'
  rw [encv'_eps0T]
  rfl

theorem sqv'_tower (n : Nat) :
    sqv' (Evidence.WF.tower n) = Evidence.Cert.towerM n := by
  unfold sqv'
  rw [encv'_tower n 0]
  unfold toMatrix ladderCols Evidence.Cert.towerM
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  rfl

theorem sqvDecomp_eps0_fsV (n : Nat) :
    BMS.expand (sqv' Evidence.WF.eps0T) n =
      sqv' (fsV Evidence.WF.eps0T n) := by
  rw [sqv'_eps0, fsV_eps0, sqv'_tower]
  exact Evidence.Cert.expand_eps0_row n

theorem flatMap_encv'_summands {t : Term}
    (hcnv : Evidence.WF.CNV t = true) (d : Nat) :
    (summands t).flatMap (fun g => encv' g d) = encv' t d := by
  cases t with
  | zero =>
      unfold encv'
      rw [dif_pos hcnv, encvC]
      rfl
  | phi a b => simp only [summands, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | add u v => exact (encv'_add hcnv d).symm
  | M => exact Bool.noConfusion hcnv
  | omg a => exact Bool.noConfusion hcnv
  | psi k a => exact Bool.noConfusion hcnv
  | Z a => exact Bool.noConfusion hcnv

theorem encv'_add_append {u v : Term}
    (hcnv : Evidence.WF.CNV (add u v) = true) (d : Nat) :
    encv' (add u v) d = encv' u d ++ encv' v d := by
  obtain ⟨_, hu, hv, _⟩ := Evidence.WF.cnv_add hcnv
  rw [encv'_add hcnv d, summands, List.flatMap_append,
    flatMap_encv'_summands hu d, flatMap_encv'_summands hv d]

theorem sqv'_add_append {u v : Term}
    (hcnv : Evidence.WF.CNV (add u v) = true) :
    sqv' (add u v) = sqv' u ++ sqv' v := by
  unfold sqv' toMatrix
  rw [encv'_add_append hcnv 0, List.map_append]

/-- Fuel-free form of the expansion-tracking sequence.  The second component of
    the termination measure orders the same-term transition from block mode to
    ordinary mode. -/
def fsVC (p : Evidence.WF.CarrierV) (block : Bool) (n : Nat) : Term :=
  match hb : block with
  | true =>
      match hp : p.1 with
      | .add u v =>
          let w := fsVC ⟨v, (Evidence.WF.cnv_add (hp ▸ p.2)).2.2.1⟩ true n
          if w == zero then u else .add u w
      | t =>
          let w := fsVC p false n
          if omLog t == t then unOmLogV w
          else if t == omega then ofNat n
          else w
  | false =>
      match hp : p.1 with
      | .add u v =>
          let w := fsVC ⟨v, (Evidence.WF.cnv_add (hp ▸ p.2)).2.2.1⟩ false n
          if w == zero then u else .add u w
      | .phi a b =>
          let ha := (Evidence.WF.cnv_phi (hp ▸ p.2)).1
          let hbcn := (Evidence.WF.cnv_phi (hp ▸ p.2)).2
          if a == zero && b == zero then zero
          else if b == zero then
            if Evidence.WF.kindV a then
              let q := Evidence.WF.predC a
              Evidence.WF.fsGen (.phi q zero) q (.phi q zero) n
            else .phi (fsVC ⟨a, ha⟩ false (n + 1)) zero
          else if Evidence.WF.kindV b then
            let c := .phi a (Evidence.WF.predC b)
            if a == zero then Evidence.WF.repAdd c n
            else if Evidence.WF.kindV a then
              let q := Evidence.WF.predC a
              let v := if q == zero then c else .phi q c
              let base := if q == zero then .add c c else v
              Evidence.WF.fsGen v q base n
            else .phi (fsVC ⟨a, ha⟩ false (n + 1)) c
          else
            let gs := summands b.splitFin.1
            let head := gs.headD zero
            if TM.Term.isFP a head then
              if gs.length == 1 then
                if a == zero then Evidence.WF.repAdd head n
                else .phi a (fsVC ⟨b, hbcn⟩ false n)
              else
                let tail : List Term := match hn : n, hg : gs.getLast? with
                  | 0, _ => []
                  | _, some g =>
                      [fsVC ⟨g, cnv_mem_summands b.splitFin.1 g
                        (cnv_ofList_take b _ hbcn) (by
                          apply List.mem_of_mem_getLast?
                          rw [hg]
                          simp)⟩ false n]
                  | _, none => []
                .phi a (ofList (gs.dropLast ++ tail))
            else match fpDeep a head with
              | some _ => .phi a (fsVC ⟨b, hbcn⟩ false n)
              | none =>
                  if a == zero || gs.isEmpty then .phi a (fsVC ⟨b, hbcn⟩ false n)
                  else .phi a (fsVC ⟨b, hbcn⟩ true n)
      | _ => zero
termination_by (p, if block then 1 else 0)
decreasing_by
  · apply Prod.Lex.left
    change lt v p.1 = true
    exact hp.symm ▸ Evidence.WF.lt_tail_add v u (hp ▸ p.2)
  · apply Prod.Lex.right
    decide
  · apply Prod.Lex.left
    change lt v p.1 = true
    exact hp.symm ▸ Evidence.WF.lt_tail_add v u (hp ▸ p.2)
  · apply Prod.Lex.left
    change lt a p.1 = true
    exact hp.symm ▸ Evidence.WF.lt_phi_fst ha
  · apply Prod.Lex.left
    change lt a p.1 = true
    exact hp.symm ▸ Evidence.WF.lt_phi_fst ha
  · apply Prod.Lex.left
    change lt b p.1 = true
    exact hp.symm ▸ Evidence.WF.lt_phi_self hbcn a
  · apply Prod.Lex.left
    change lt g p.1 = true
    apply hp.symm ▸ lt_summand_phi (hp ▸ p.2)
    apply List.mem_of_mem_getLast?
    rw [hg]
    simp
  · apply Prod.Lex.left
    change lt b p.1 = true
    exact hp.symm ▸ Evidence.WF.lt_phi_self hbcn a
  · apply Prod.Lex.left
    change lt b p.1 = true
    exact hp.symm ▸ Evidence.WF.lt_phi_self hbcn a

/-- Total fuel-free sequence; outside `CNV` it returns zero, as `fsV` does on
    the region relevant to the theorem. -/
def fsV' (t : Term) (n : Nat) : Term :=
  if h : Evidence.WF.CNV t = true then fsVC ⟨t, h⟩ false n else zero

#guard nfOKLimitCorpus.all (fun t =>
  (List.range 8).all (fun n => fsV' t n == fsV t n))

theorem fpDeepF_some_ne_zero (f : Nat) (a t z : Term)
    (h : fpDeepF f a t = some z) : z ≠ zero := by
  induction f generalizing a t z with
  | zero => cases h
  | succ f ih =>
      simp only [fpDeepF] at h
      split at h
      · rename_i hfp
        injection h with hzt
        subst z
        intro ht
        subst t
        exact Bool.noConfusion hfp
      · split at h
        · rename_i c x ht
          obtain ⟨g, _, hg⟩ := List.exists_of_findSome?_eq_some h
          exact ih a g z hg
        · contradiction

theorem fpDeepC_some_ne_zero {a t : Term} (ht : Evidence.WF.CNV t = true)
    {z : {z : Term // Evidence.WF.CNV z = true ∧ le z t = true}}
    (h : fpDeepC a t ht = some z) : z.1 ≠ zero := by
  unfold fpDeepC at h
  split at h
  · rename_i w hfd
    injection h with hw
    exact hw ▸ fpDeepF_some_ne_zero _ a t w hfd
  · contradiction

private theorem head?_append_of_head {α : Type} {l r : List α} {x : α}
    (h : l.head? = some x) : (l ++ r).head? = some x := by
  cases l <;> simp_all

theorem encvC_head (p : Evidence.WF.CarrierV) (d : Nat)
    (hz : p.1 ≠ zero) : (encvC p d).head? = some (d, 0) := by
  fun_induction encvC p d
  case case1 hp => exact (hz hp).elim
  case case2 p d u v hp ih =>
    have hcnv : Evidence.WF.CNV (add u v) = true := hp ▸ p.2
    obtain ⟨huAP, hu, _, _⟩ := Evidence.WF.cnv_add hcnv
    have hu0 : u ≠ zero := by
      intro huz
      subst u
      exact Bool.noConfusion huAP
    have humem : u ∈ summands (add u v) := by
      rw [summands, summands_of_isAP huAP]
      simp
    have hhead := ih ⟨u, humem⟩ hu0
    rw [encvC_eq_encv'] at hhead
    simp only [encvC_eq_encv']
    rw [show (summands (add u v)).attach.flatMap (fun g => encv' g.1 d) =
        (summands (add u v)).flatMap (fun g => encv' g d) from
      flatMap_attach (summands (add u v)) (fun g => encv' g d)]
    rw [← encv'_add hcnv d, encv'_add_append hcnv d]
    exact head?_append_of_head hhead
  case case3 p d a b hp ladder unit reps mk hfp ih1 ih2 ih3 =>
    have hhead0 : (summands b.splitFin.1).headD zero ≠ zero := by
      intro hzero
      rw [hzero] at hfp
      exact Bool.noConfusion hfp
    exact head?_append_of_head (head?_append_of_head (ih3 hhead0))
  case case4 p d a b hp ladder unit reps mk hfp z hdeep ih1 ih2 ih3 =>
    have hz0 := fpDeepC_some_ne_zero _ hdeep
    exact head?_append_of_head (head?_append_of_head (ih3 hz0))
  case case5 => rfl
  case case6 p d hzero hadd hphi =>
    cases hpval : p.1 with
    | zero => exact (hzero hpval).elim
    | add u v => exact (hadd u v hpval).elim
    | phi a b => exact (hphi a b hpval).elim
    | M =>
        have hbad : Evidence.WF.CNV M = true := hpval ▸ p.2
        exact Bool.noConfusion hbad
    | omg a =>
        have hbad : Evidence.WF.CNV (omg a) = true := hpval ▸ p.2
        exact Bool.noConfusion hbad
    | psi k a =>
        have hbad : Evidence.WF.CNV (psi k a) = true := hpval ▸ p.2
        exact Bool.noConfusion hbad
    | Z a =>
        have hbad : Evidence.WF.CNV (Z a) = true := hpval ▸ p.2
        exact Bool.noConfusion hbad

#print axioms fsGen_zero_one_eq_tower
#print axioms fsV_eps0
#print axioms sqv'_eps0
#print axioms sqv'_tower
#print axioms sqvDecomp_eps0_fsV
#print axioms flatMap_encv'_summands
#print axioms encv'_add_append
#print axioms sqv'_add_append

/-! ### §25.4 `deg` FACTS FOR `summands` AND `splitFin`

Four order facts about the degree measure, salvaged from an attempt at a lemma this
project does not need (see below).  They are general and independently useful:
`summands` and `splitFin` never increase `deg`, and `ofList ∘ take` does not either.

**WHY THEY ARE HERE AND NOT IN A SATURATION PROOF.**  A worker built these to feed
`fsVF f block t n = fsVC p block n` — the fuel-saturation lemma for `fsV`.  §16
records that this project met exactly that obligation once, named it
`encvF_saturate`, called it "provable and real work", and then **never proved it,
because redefining fuel-free discharged the obligation instead.**  `fsVC` and `fsV'`
(§25.3) are that redefinition, so the lemma has no consumer.  It was attempted three
times anyway and did not close; the four `deg` facts are what survives, and they are
kept because they are true and cheap, not because the attempt was justified.
-/

theorem deg_mem_summands : ∀ (t g : Term), g ∈ summands t → g.deg ≤ t.deg := by
  intro t
  induction t with
  | zero => intro g hg; simp only [summands] at hg; contradiction
  | add u v ihu ihv =>
      intro g hg
      simp only [summands, List.mem_append] at hg
      rcases hg with hg | hg
      · exact Nat.le_trans (ihu g hg) (by simp only [Term.deg]; omega)
      · exact Nat.le_trans (ihv g hg) (by simp only [Term.deg]; omega)
  | phi a b => intro g hg; simp only [summands, List.mem_singleton] at hg; subst g; omega
  | M => intro g hg; simp only [summands, List.mem_singleton] at hg; subst g; omega
  | omg a => intro g hg; simp only [summands, List.mem_singleton] at hg; subst g; omega
  | psi k a => intro g hg; simp only [summands, List.mem_singleton] at hg; subst g; omega
  | Z a => intro g hg; simp only [summands, List.mem_singleton] at hg; subst g; omega

theorem deg_ofList_take : ∀ (t : Term) (k : Nat),
    (ofList ((toList t).take k)).deg ≤ t.deg := by
  intro t
  induction t with
  | zero => intro k; simp only [toList, List.take_nil, ofList, Term.deg]; exact Nat.le_refl _
  | M => intro k; cases k <;> simp only [toList, List.take, List.take_nil, ofList, Term.deg] <;> exact Nat.le_refl _
  | omg a => intro k; cases k <;> simp only [toList, List.take, List.take_nil, ofList, Term.deg] <;> omega
  | phi a b => intro k; cases k <;> simp only [toList, List.take, List.take_nil, ofList, Term.deg] <;> omega
  | psi q a => intro k; cases k <;> simp only [toList, List.take, List.take_nil, ofList, Term.deg] <;> omega
  | Z a => intro k; cases k <;> simp only [toList, List.take, List.take_nil, ofList, Term.deg] <;> omega
  | add u v _ ihv =>
      intro k
      cases k with
      | zero => simp only [toList, List.take_zero, ofList, Term.deg]; omega
      | succ j =>
          have hv := ihv j
          simp only [toList, List.take_succ_cons]
          cases h : (toList v).take j with
          | nil => simp only [ofList, Term.deg]; omega
          | cons y ys =>
              rw [h] at hv
              simp only [ofList, Term.deg] at hv ⊢
              omega

theorem deg_splitFin_fst (t : Term) : t.splitFin.1.deg ≤ t.deg :=
  deg_ofList_take t _

theorem deg_summands_splitFin (t g : Term)
    (hg : g ∈ summands t.splitFin.1) : g.deg ≤ t.deg :=
  Nat.le_trans (deg_mem_summands _ g hg) (deg_splitFin_fst t)

/-! ### §25.5 THE GENERAL STATEMENT OVER `CNV` ALONE IS FALSE — refuted, not unproved

`sqvDecomp_eps0_fsV'` is §25.3's ε₀ case restated against the FUEL-FREE `fsV'`, so the
form a proof can induct over is usable.

Then the general statement was attacked and **turned out to be false**:

    ¬ (∀ t, CNV t → kindV t = false → t ≠ 0 → ∀ n,
         expand (sqv' t) n = sqv' (fsV' t n))

`no_sqvDecomp_general` proves it with an explicit witness at `n = 0`:

    cexT = φ̄(1, ζ₀) = ε_{ζ₀+1}      CNV cexT = true      NfOK cexT = FALSE
    expand (sqv' cexT) 0 = (0,0)(1,1)(2,1)
    sqv' (fsV' cexT 0)   = (0,0)(1,1)(2,0)(3,1)

**That witness is one of the two rows `table/nfok-reach-2026-08-10.txt` had already
measured as outside the assembly's reach** — the fixed-point-skip shape, where `phiNF`
and `φ̄` disagree.  So the corpus measurement "11 of the 13 target rows are `NfOK`,
2 are not" now has a theorem on the other side: **without `NfOK`, the general
decomposition is not merely unproved, it is refuted, and the refuting term is one of
those 2.**

**CONSEQUENCE: the statement to prove carries `NfOK t = true`.** The two skip rows keep
the separate route `rowA` already demonstrates, whose first brick is `Cert` §22's
`expand_blockRow`.  That hypothesis was going to be added on the strength of a corpus
measurement; it is now added on the strength of a counterexample.
-/

theorem sqvDecomp_eps0_fsV' (n : Nat) :
    BMS.expand (Evidence.SqV.sqv' Evidence.WF.eps0T) n
      = Evidence.SqV.sqv' (Evidence.SqV.fsV' Evidence.WF.eps0T n) := by
  rw [Evidence.SqV.sqv'_eps0]
  unfold Evidence.SqV.fsV'
  rw [dif_pos (by decide)]
  unfold Evidence.SqV.fsVC
  change BMS.expand [[0, 0], [1, 1]] n =
    Evidence.SqV.sqv' (Evidence.WF.fsGen TM.Term.one TM.Term.zero TM.Term.one n)
  rw [Evidence.SqV.fsGen_zero_one_eq_tower, Evidence.SqV.sqv'_tower]
  exact Evidence.Cert.expand_eps0_row n

namespace Counterexample

def cexB : TM.Term := phi (add one one) zero
def cexT : TM.Term := phi one cexB

theorem encv_b :
    encv' cexB 0 = [((0, 0) : Col2), (1, 1), (2, 1)] := by
  unfold cexB encv'
  rw [dif_pos (show Evidence.WF.CNV (phi (add one one) zero) = true from rfl)]
  have hgs : summands (TM.Term.splitFin zero).1 = [] := rfl
  have hat : (summands (TM.Term.splitFin zero).1).attach = [] :=
    List.eq_nil_of_length_eq_zero (by rw [List.length_attach, hgs]; rfl)
  have hm2 : (TM.Term.splitFin zero).2 = 0 := rfl
  have hfp : TM.Term.isFP (add one one)
      ((summands (TM.Term.splitFin zero).1).headD zero) = false := rfl
  have hfd : ∀ pf, fpDeepC (add one one)
      ((summands (TM.Term.splitFin zero).1).headD zero) pf = none :=
    fun pf => fpDeepC_none pf (by rw [hgs]; rfl)
  rw [encvC]
  dsimp only
  rw [hfp]
  simp only [Bool.false_eq_true, if_false]
  rw [hfd, hat, hm2]
  simp only [encvC_eq_encv', show ((add one one) == zero) = false from rfl,
    Bool.false_eq_true, if_false]
  rw [show predOr (add one one) = one from rfl,
    show encv' one 2 = [((2, 0) : Col2)] from encv'_one 2]
  split
  · rfl
  · exact absurd hgs (by simp_all)

theorem encv_t :
    encv' cexT 0 = [((0, 0) : Col2), (1, 1), (2, 1), (1, 1)] := by
  unfold cexT encv'
  rw [dif_pos (show Evidence.WF.CNV (phi one cexB) = true from rfl)]
  have hgs : summands (TM.Term.splitFin cexB).1 = [cexB] := rfl
  have hhd : (summands (TM.Term.splitFin cexB).1).headD zero = cexB := by rw [hgs]; rfl
  have hm2 : (TM.Term.splitFin cexB).2 = 0 := rfl
  rw [encvC]
  dsimp only
  rw [show TM.Term.isFP one
      ((summands (TM.Term.splitFin cexB).1).headD zero) = true from by rw [hhd]; rfl]
  simp only [if_true]
  rw [hm2, encvC_eq_encv', hhd, encv_b,
    show ((summands (TM.Term.splitFin cexB).1).length == 1) = true from by rw [hgs]; rfl,
    Evidence.SqV.encvC_predOr_one]
  simp only [if_true, List.replicate_zero, List.flatten_nil, List.append_nil]
  rfl

theorem fs_b (h : Evidence.WF.CNV cexB = true) :
    fsVC ⟨cexB, h⟩ false 0 = Evidence.WF.eps0T := by
  unfold cexB
  rw [fsVC]
  dsimp only
  rfl

theorem fs_t : fsV' cexT 0 = Evidence.WF.epsEps0 := by
  unfold cexT fsV'
  rw [dif_pos (show Evidence.WF.CNV (phi one cexB) = true from rfl)]
  have hgs : summands (TM.Term.splitFin cexB).1 = [cexB] := rfl
  have hhd : (summands (TM.Term.splitFin cexB).1).headD zero = cexB := by rw [hgs]; rfl
  rw [fsVC]
  dsimp only
  rw [show TM.Term.isFP one
      ((summands (TM.Term.splitFin cexB).1).headD zero) = true from by rw [hhd]; rfl]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [show ((summands (TM.Term.splitFin cexB).1).length == 1) = true from by rw [hgs]; rfl]
  simp only [if_true]
  rw [fs_b]
  rfl

theorem sqv_t :
    sqv' cexT = [[0, 0], [1, 1], [2, 1], [1, 1]] := by
  unfold sqv' toMatrix
  rw [encv_t]
  rfl

theorem lhs_t :
    BMS.expand (sqv' cexT) 0 = [[0, 0], [1, 1], [2, 1]] := by
  rw [sqv_t]
  rfl

theorem rhs_t :
    sqv' (fsV' cexT 0) = [[0, 0], [1, 1], [2, 0], [3, 1]] := by
  rw [fs_t, Evidence.SqV.sqv'_epsEps0]

theorem refutes_general_at_zero :
    BMS.expand (sqv' cexT) 0 ≠ sqv' (fsV' cexT 0) := by
  rw [lhs_t, rhs_t]
  decide

theorem cnv_t : Evidence.WF.CNV cexT = true := rfl
theorem limit_t : Evidence.WF.kindV cexT = false := rfl
theorem nonzero_t : cexT ≠ zero := by decide

theorem no_sqvDecomp_general :
    ¬ (∀ {x : TM.Term}, Evidence.WF.CNV x = true →
      Evidence.WF.kindV x = false → x ≠ zero → ∀ n : Nat,
      BMS.expand (sqv' x) n = sqv' (fsV' x n)) := by
  intro h
  exact refutes_general_at_zero (h cnv_t limit_t nonzero_t 0)

end Counterexample

/-! ## §K1 `SqvDecomp` is false even under `NfOK` (worker cx10, landed 2026-08-12)

One of the three gaps for `certIn_cnv` was "the general `SqvDecomp` clause, perhaps
recoverable by adding `NfOK`".  It is not: the witness below is `CNV`, `NfOK`, a limit,
nonzero, and still breaks the clause at `n = 0`.  The existing `no_sqvDecomp_general`
above refutes the un-strengthened statement; this refutes the strengthened one, so the
route is closed rather than merely unproved.
-/

open TM.Term

/-!
The requested theorem is false even with `NfOK`.  The witness is a
multi-summand instance of the `collapse` clause.
-/

def nfCex : TM.Term :=
  phi zero (add Evidence.WF.eps0T
    (add Evidence.WF.eps0T Evidence.WF.eps0T))

def nfCexFs : TM.Term :=
  phi zero (add Evidence.WF.eps0T Evidence.WF.eps0T)

#guard Evidence.WF.NfOK nfCex
#guard Evidence.WF.CNV nfCex
#guard !(Evidence.WF.kindV nfCex)
#guard nfCex != zero
#guard BMS.expand (Evidence.SqV.sqv' Evidence.WF.eps0T) 0 ==
  Evidence.SqV.sqv' (Evidence.SqV.fsV' Evidence.WF.eps0T 0)
#guard BMS.expand (Evidence.SqV.sqv' nfCex) 0 !=
  Evidence.SqV.sqv' (Evidence.SqV.fsV' nfCex 0)

#eval (Evidence.SqV.summands
  (TM.Term.splitFin (add Evidence.WF.eps0T
    (add Evidence.WF.eps0T Evidence.WF.eps0T))).1).length
#eval BMS.expand (Evidence.SqV.sqv' nfCex) 0
#eval Evidence.SqV.sqv' (Evidence.SqV.fsV' nfCex 0)

theorem nfCex_cnv : Evidence.WF.CNV nfCex = true := by decide

theorem nfCex_nf : Evidence.WF.NfOK nfCex = true := by decide

theorem nfCex_lim : Evidence.WF.kindV nfCex = false := by decide

theorem nfCex_nz : nfCex ≠ zero := by decide

/-- The witness enters the `collapse` clause with three split summands. -/
theorem sqvDecomp_collapse_witness :
    let gs := Evidence.SqV.summands
      (TM.Term.splitFin (add Evidence.WF.eps0T
        (add Evidence.WF.eps0T Evidence.WF.eps0T))).1
    TM.Term.isFP zero (gs.headD zero) = true ∧ gs.length = 3 := by
  decide

theorem nfCex_sqv : Evidence.SqV.sqv' nfCex =
    [[0, 0], [1, 1], [1, 0], [2, 1], [1, 0], [2, 1]] := by
  have hgs : Evidence.SqV.summands
      (TM.Term.splitFin (add Evidence.WF.eps0T
        (add Evidence.WF.eps0T Evidence.WF.eps0T))).1 =
      [Evidence.WF.eps0T, Evidence.WF.eps0T, Evidence.WF.eps0T] := rfl
  have hhd : (Evidence.SqV.summands
      (TM.Term.splitFin (add Evidence.WF.eps0T
        (add Evidence.WF.eps0T Evidence.WF.eps0T))).1).headD zero =
      Evidence.WF.eps0T := by rw [hgs]; rfl
  have hm2 : (TM.Term.splitFin (add Evidence.WF.eps0T
      (add Evidence.WF.eps0T Evidence.WF.eps0T))).2 = 0 := rfl
  unfold nfCex Evidence.SqV.sqv' Evidence.SqV.encv'
  rw [dif_pos (show Evidence.WF.CNV (phi zero (add Evidence.WF.eps0T
      (add Evidence.WF.eps0T Evidence.WF.eps0T))) = true from rfl),
    Evidence.SqV.encvC]
  dsimp only
  rw [show TM.Term.isFP zero
      ((Evidence.SqV.summands
        (TM.Term.splitFin (add Evidence.WF.eps0T
          (add Evidence.WF.eps0T Evidence.WF.eps0T))).1).headD zero) = true by
        rw [hhd]; rfl]
  simp only [if_true]
  rw [hm2, Evidence.SqV.encvC_eq_encv', hhd, Evidence.SqV.encv'_eps0T]
  rw [show ((Evidence.SqV.summands
      (TM.Term.splitFin (add Evidence.WF.eps0T
        (add Evidence.WF.eps0T Evidence.WF.eps0T))).1).length == 1) = false by
        rw [hgs]; rfl]
  simp only [Bool.false_eq_true, if_false, Evidence.SqV.encvC_eq_encv',
    beq_self_eq_true, List.replicate_zero, List.flatten_nil, List.append_nil]
  simp only [if_pos True.intro, Nat.zero_add, List.nil_append]
  rw [List.map_drop, List.attach_map_val
    (l := Evidence.SqV.summands
      (TM.Term.splitFin (add Evidence.WF.eps0T
        (add Evidence.WF.eps0T Evidence.WF.eps0T))).1)
    (f := fun y => Evidence.SqV.shiftD 1 (Evidence.SqV.encv' y 0))]
  rw [hgs]
  simp only [List.drop, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, Evidence.SqV.encv'_eps0T, Evidence.SqV.shiftD]
  rfl

theorem nfCex_fs : Evidence.SqV.fsV' nfCex 0 = nfCexFs := by
  unfold nfCex Evidence.SqV.fsV'
  rw [dif_pos (show Evidence.WF.CNV (phi zero (add Evidence.WF.eps0T
      (add Evidence.WF.eps0T Evidence.WF.eps0T))) = true from rfl),
    Evidence.SqV.fsVC]
  dsimp only
  rfl

theorem nfCexFs_sqv : Evidence.SqV.sqv' nfCexFs =
    [[0, 0], [1, 1], [1, 0], [2, 1]] := by
  have hgs : Evidence.SqV.summands
      (TM.Term.splitFin (add Evidence.WF.eps0T Evidence.WF.eps0T)).1 =
      [Evidence.WF.eps0T, Evidence.WF.eps0T] := rfl
  have hhd : (Evidence.SqV.summands
      (TM.Term.splitFin (add Evidence.WF.eps0T Evidence.WF.eps0T)).1).headD zero =
      Evidence.WF.eps0T := by rw [hgs]; rfl
  have hm2 : (TM.Term.splitFin
      (add Evidence.WF.eps0T Evidence.WF.eps0T)).2 = 0 := rfl
  unfold nfCexFs Evidence.SqV.sqv' Evidence.SqV.encv'
  rw [dif_pos (show Evidence.WF.CNV
      (phi zero (add Evidence.WF.eps0T Evidence.WF.eps0T)) = true from rfl),
    Evidence.SqV.encvC]
  dsimp only
  rw [show TM.Term.isFP zero
      ((Evidence.SqV.summands
        (TM.Term.splitFin (add Evidence.WF.eps0T Evidence.WF.eps0T)).1).headD zero) = true by
        rw [hhd]; rfl]
  simp only [if_true]
  rw [hm2, Evidence.SqV.encvC_eq_encv', hhd, Evidence.SqV.encv'_eps0T]
  rw [show ((Evidence.SqV.summands
      (TM.Term.splitFin (add Evidence.WF.eps0T Evidence.WF.eps0T)).1).length == 1) = false by
        rw [hgs]; rfl]
  simp only [Bool.false_eq_true, if_false, Evidence.SqV.encvC_eq_encv',
    beq_self_eq_true, List.replicate_zero, List.flatten_nil, List.append_nil]
  simp only [if_pos True.intro, Nat.zero_add, List.nil_append]
  rw [List.map_drop, List.attach_map_val
    (l := Evidence.SqV.summands
      (TM.Term.splitFin (add Evidence.WF.eps0T Evidence.WF.eps0T)).1)
    (f := fun y => Evidence.SqV.shiftD 1 (Evidence.SqV.encv' y 0))]
  rw [hgs]
  simp only [List.drop, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, Evidence.SqV.encv'_eps0T, Evidence.SqV.shiftD]
  rfl

theorem nfCex_lhs :
    BMS.expand (Evidence.SqV.sqv' nfCex) 0 =
      [[0, 0], [1, 1], [1, 0], [2, 1], [1, 0]] := by
  rw [nfCex_sqv]
  rfl

theorem nfCex_rhs :
    Evidence.SqV.sqv' (Evidence.SqV.fsV' nfCex 0) =
      [[0, 0], [1, 1], [1, 0], [2, 1]] := by
  rw [nfCex_fs]
  exact nfCexFs_sqv

theorem nfCex_refutes :
    BMS.expand (Evidence.SqV.sqv' nfCex) 0 ≠
      Evidence.SqV.sqv' (Evidence.SqV.fsV' nfCex 0) := by
  rw [nfCex_lhs, nfCex_rhs]
  decide

/-- The exact requested statement, universally closed, is refuted. -/
theorem no_sqvDecomp_general_nfOK :
    ¬ (∀ {t : TM.Term}, Evidence.WF.NfOK t = true →
      Evidence.WF.CNV t = true → Evidence.WF.kindV t = false →
      t ≠ TM.Term.zero → ∀ n : Nat,
      BMS.expand (Evidence.SqV.sqv' t) n =
        Evidence.SqV.sqv' (Evidence.SqV.fsV' t n)) := by
  intro h
  exact nfCex_refutes (h nfCex_nf nfCex_cnv nfCex_lim nfCex_nz 0)

#print axioms nfCex_cnv
#print axioms nfCex_nf
#print axioms nfCex_lim
#print axioms nfCex_nz
#print axioms sqvDecomp_collapse_witness
#print axioms nfCex_sqv
#print axioms nfCex_fs
#print axioms nfCexFs_sqv
#print axioms nfCex_lhs
#print axioms nfCex_rhs
#print axioms nfCex_refutes
#print axioms no_sqvDecomp_general_nfOK


/-! ## §K2 `kind` agreement for `sqv'` (worker cx11, landed 2026-08-12)

The second of the three gaps: `sqv'` must send zero / successor / limit terms to matrices
of the matching `BMS.kind`.  Proved for every `CNV` term.  This is the half of
`certIn_cnv` that does NOT need the order clauses, and it is now closed.
-/

#guard agreeCorpus.length == 169
#guard kindFailures.length == 0


private theorem mem_bumpAt_fst {e : Nat} {cs : List Col2} {c : Col2}
    (hc : c ∈ bumpAt e cs) : ∃ z ∈ cs, c.1 = z.1 := by
  simp only [bumpAt, List.mem_map] at hc
  obtain ⟨z, hz, rfl⟩ := hc
  split <;> exact ⟨z, hz, rfl⟩

private theorem mem_shiftD_fst {e : Nat} {cs : List Col2} {c : Col2}
    (hc : c ∈ shiftD e cs) : ∃ z ∈ cs, c.1 = z.1 + e := by
  simp only [shiftD, List.mem_map] at hc
  obtain ⟨z, hz, rfl⟩ := hc
  exact ⟨z, hz, rfl⟩

private theorem ladder_fst_gt (a : TM.Term) (d : Nat) (cs : List Col2)
    (hcs : ∀ c ∈ cs, d + 2 ≤ c.1) :
    ∀ c ∈ (if a == TM.Term.zero then []
      else (d + 1, 1) :: bumpAt (d + 2) cs), d < c.1 := by
  intro c hc
  by_cases ha : (a == TM.Term.zero) = true
  · rw [if_pos ha] at hc
    exact absurd hc (by simp)
  · rw [if_neg ha] at hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · omega
    · obtain ⟨z, hz, heq⟩ := mem_bumpAt_fst hc
      rw [heq]
      exact Nat.lt_of_lt_of_le (by omega) (hcs z hz)

private theorem unit_fst_gt (a : TM.Term) (d : Nat) (ladder : List Col2)
    (hladder : ∀ c ∈ ladder, d < c.1) :
    ∀ c ∈ (if a == TM.Term.zero then [(d + 1, 0)] else ladder), d < c.1 := by
  intro c hc
  by_cases ha : (a == TM.Term.zero) = true
  · rw [if_pos ha] at hc
    have heq : c = (d + 1, 0) := by simpa using hc
    subst c
    omega
  · rw [if_neg ha] at hc
    exact hladder c hc

private theorem reps_fst_gt (d n : Nat) (unit : List Col2)
    (hunit : ∀ c ∈ unit, d < c.1) :
    ∀ c ∈ (List.replicate n unit).flatten, d < c.1 := by
  intro c hc
  obtain ⟨l, hl, hc⟩ := List.mem_flatten.mp hc
  have hlu : l = unit := List.eq_of_mem_replicate hl
  subst l
  exact hunit c hc

private theorem blocks_fst_gt {α : Type} (d e : Nat) (ladder : List Col2)
    (f : α → List Col2) (hs : List α)
    (hladder : ∀ c ∈ ladder, d < c.1) (he : d < e) :
    ∀ c ∈ (hs.map (fun g => ladder ++ shiftD e (f g))).flatten, d < c.1 := by
  intro c hc
  obtain ⟨block, hblock, hc⟩ := List.mem_flatten.mp hc
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp hblock
  simp only [List.mem_append] at hc
  rcases hc with hc | hc
  · exact hladder c hc
  · obtain ⟨z, _, heq⟩ := mem_shiftD_fst hc
    rw [heq]
    omega

private theorem eq_zero_of_cnv_summands_nil {t : TM.Term}
    (hcn : Evidence.WF.CNV t = true) (hs : summands t = []) : t = TM.Term.zero := by
  cases t with
  | zero => rfl
  | phi a b => simp [summands] at hs
  | add u v =>
      have hu := (Evidence.WF.cnv_add hcn).1
      rw [summands, summands_of_isAP hu] at hs
      simp at hs
  | M => exact Bool.noConfusion hcn
  | omg a => exact Bool.noConfusion hcn
  | psi k a => exact Bool.noConfusion hcn
  | Z a => exact Bool.noConfusion hcn

private theorem mem_summands_ne_zero {t g : TM.Term} (hg : g ∈ summands t) :
    g ≠ TM.Term.zero := by
  intro heq
  subst g
  induction t <;> simp_all [summands]

private theorem encvC_ne_nil (p : Evidence.WF.CarrierV) (d : Nat)
    (hz : p.1 ≠ TM.Term.zero) : encvC p d ≠ [] := by
  intro heq
  have hh := encvC_head p d hz
  rw [heq] at hh
  contradiction

private theorem reps_ne_nil (n : Nat) (unit : List Col2)
    (hn : n ≠ 0) (hu : unit ≠ []) : (List.replicate n unit).flatten ≠ [] := by
  cases n with
  | zero => exact absurd rfl hn
  | succ n =>
      cases unit with
      | nil => exact absurd rfl hu
      | cons c cs => simp

private theorem blocks_ne_nil {α : Type} (ladder : List Col2) (e : Nat)
    (f : α → List Col2) (hs : List α) (hhs : hs ≠ [])
    (hblock : ∀ g ∈ hs, ladder ++ shiftD e (f g) ≠ []) :
    (hs.map (fun g => ladder ++ shiftD e (f g))).flatten ≠ [] := by
  cases hs with
  | nil => exact absurd rfl hhs
  | cons g gs =>
      simp only [List.map_cons, List.flatten_cons]
      exact List.append_ne_nil_of_left_ne_nil (hblock g (by simp)) _

private theorem attach_drop_one_ne_nil {α : Type} {l : List α} (hlen : 2 ≤ l.length) :
    l.attach.drop 1 ≠ [] := by
  intro heq
  have hh := congrArg List.length heq
  simp only [List.length_drop, List.length_attach, List.length_nil] at hh
  omega

private theorem getLast_ne_base_of_suffix (d : Nat) (pre suf : List Col2)
    (hne : suf ≠ []) (hgt : ∀ c ∈ suf, d < c.1) :
    (pre ++ suf).getLast? ≠ some (d, 0) := by
  rw [Evidence.StageA.getLast?_append_right pre suf hne]
  intro hlast
  have hm : (d, 0) ∈ suf := List.mem_of_getLast? hlast
  have := hgt (d, 0) hm
  omega

theorem encvC_fst_ge (p : Evidence.WF.CarrierV) (d : Nat) :
    ∀ c ∈ encvC p d, d ≤ c.1 := by
  fun_induction encvC p d
  case case1 => simp
  case case2 p d u v hp ih =>
    intro c hc
    simp only [List.mem_flatMap] at hc
    obtain ⟨g, _, hc⟩ := hc
    exact ih g c hc
  case case3 p d a b hp ladder unit reps mk hfp ih1 ih2 ih3 =>
    have hladder : ∀ c ∈ ladder, d < c.1 := by
      simpa only [ladder] using ladder_fst_gt a d _ ih1
    have hunit : ∀ c ∈ unit, d < c.1 := by
      simpa only [unit] using unit_fst_gt a d ladder hladder
    have hreps : ∀ c ∈ reps, d < c.1 := by
      simpa only [reps] using reps_fst_gt d b.splitFin.2 unit hunit
    have he : d < (if a == TM.Term.zero then d + 1 else d + 2) := by
      split <;> omega
    have hmk (hs) : ∀ c ∈ mk hs, d < c.1 := by
      simpa only [mk] using blocks_fst_gt d
        (if a == TM.Term.zero then d + 1 else d + 2) ladder
        (fun g => encvC ⟨if a == TM.Term.zero then g.1 else omLog g.1, by
          split
          · exact cnv_mem_summands _ g.1
              (cnv_ofList_take b _ (Evidence.WF.cnv_phi (hp ▸ p.2)).2) g.2
          · exact cnv_omLog (cnv_mem_summands _ g.1
              (cnv_ofList_take b _ (Evidence.WF.cnv_phi (hp ▸ p.2)).2) g.2)⟩ 0)
        hs hladder he
    intro c hc
    simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact ih3 c hc
    · by_cases hlen : ((summands b.splitFin.1).length == 1) = true
      · rw [if_pos hlen] at hc
        exact Nat.le_of_lt (hunit c hc)
      · rw [if_neg hlen] at hc
        exact Nat.le_of_lt (hmk _ c hc)
    · exact Nat.le_of_lt (hreps c hc)
  case case4 p d a b hp ladder unit reps mk hfp z hdeep ih1 ih2 ih3 =>
    have hladder : ∀ c ∈ ladder, d < c.1 := by
      simpa only [ladder] using ladder_fst_gt a d _ ih1
    have hunit : ∀ c ∈ unit, d < c.1 := by
      simpa only [unit] using unit_fst_gt a d ladder hladder
    have hreps : ∀ c ∈ reps, d < c.1 := by
      simpa only [reps] using reps_fst_gt d b.splitFin.2 unit hunit
    have he : d < (if a == TM.Term.zero then d + 1 else d + 2) := by
      split <;> omega
    have hmk (hs) : ∀ c ∈ mk hs, d < c.1 := by
      simpa only [mk] using blocks_fst_gt d
        (if a == TM.Term.zero then d + 1 else d + 2) ladder
        (fun g => encvC ⟨if a == TM.Term.zero then g.1 else omLog g.1, by
          split
          · exact cnv_mem_summands _ g.1
              (cnv_ofList_take b _ (Evidence.WF.cnv_phi (hp ▸ p.2)).2) g.2
          · exact cnv_omLog (cnv_mem_summands _ g.1
              (cnv_ofList_take b _ (Evidence.WF.cnv_phi (hp ▸ p.2)).2) g.2)⟩ 0)
        hs hladder he
    intro c hc
    simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact ih3 c hc
    · exact Nat.le_of_lt (hmk _ c hc)
    · exact Nat.le_of_lt (hreps c hc)
  case case5 p d a b hp ladder unit reps mk hfp hdeep ih1 ih2 =>
    have hladder : ∀ c ∈ ladder, d < c.1 := by
      simpa only [ladder] using ladder_fst_gt a d _ ih1
    have hunit : ∀ c ∈ unit, d < c.1 := by
      simpa only [unit] using unit_fst_gt a d ladder hladder
    have hreps : ∀ c ∈ reps, d < c.1 := by
      simpa only [reps] using reps_fst_gt d b.splitFin.2 unit hunit
    have he : d < (if a == TM.Term.zero then d + 1 else d + 2) := by
      split <;> omega
    have hmk (hs) : ∀ c ∈ mk hs, d < c.1 := by
      simpa only [mk] using blocks_fst_gt d
        (if a == TM.Term.zero then d + 1 else d + 2) ladder
        (fun g => encvC ⟨if a == TM.Term.zero then g.1 else omLog g.1, by
          split
          · exact cnv_mem_summands _ g.1
              (cnv_ofList_take b _ (Evidence.WF.cnv_phi (hp ▸ p.2)).2) g.2
          · exact cnv_omLog (cnv_mem_summands _ g.1
              (cnv_ofList_take b _ (Evidence.WF.cnv_phi (hp ▸ p.2)).2) g.2)⟩ 0)
        hs hladder he
    intro c hc
    simp only [List.mem_cons, List.mem_append] at hc
    rcases hc with rfl | hc
    · exact Nat.le_refl d
    · rcases hc with hc | hc
      · split at hc
        · exact Nat.le_of_lt (hladder c hc)
        · exact Nat.le_of_lt (hmk _ c hc)
      · exact Nat.le_of_lt (hreps c hc)
  case case6 p d hzero hadd hphi =>
    intro c hc
    simp at hc

theorem encvC_phi_last_eq_base_iff {a b : TM.Term}
    (hcn : Evidence.WF.CNV (TM.Term.phi a b) = true) (d : Nat) :
    (encvC ⟨TM.Term.phi a b, hcn⟩ d).getLast? = some (d, 0) ↔
      Evidence.WF.kindV (TM.Term.phi a b) = true := by
  let ladder : List Col2 :=
    if a == TM.Term.zero then []
    else (d + 1, 1) :: bumpAt (d + 2)
      (encvC ⟨predOr a, cnv_predOr (Evidence.WF.cnv_phi hcn).1⟩ (d + 2))
  let unit : List Col2 := if a == TM.Term.zero then [(d + 1, 0)] else ladder
  let reps : List Col2 := (List.replicate b.splitFin.2 unit).flatten
  let mk : List {x // x ∈ summands b.splitFin.1} → List Col2 := fun hs =>
    (hs.map (fun g =>
      ladder ++ shiftD (if a == TM.Term.zero then d + 1 else d + 2)
        (encvC ⟨if a == TM.Term.zero then g.1 else omLog g.1,
          by
            split
            · exact cnv_mem_summands _ g.1
                (cnv_ofList_take b _ (Evidence.WF.cnv_phi hcn).2) g.2
            · exact cnv_omLog (cnv_mem_summands _ g.1
                (cnv_ofList_take b _ (Evidence.WF.cnv_phi hcn).2) g.2)⟩ 0))).flatten
  have hladder : ∀ c ∈ ladder, d < c.1 := by
    apply ladder_fst_gt a d _
    exact encvC_fst_ge _ _
  have hunit : ∀ c ∈ unit, d < c.1 := by
    simpa only [unit] using unit_fst_gt a d ladder hladder
  have hreps : ∀ c ∈ reps, d < c.1 := by
    simpa only [reps] using reps_fst_gt d b.splitFin.2 unit hunit
  have he : d < (if a == TM.Term.zero then d + 1 else d + 2) := by
    split <;> omega
  have hmk (hs) : ∀ c ∈ mk hs, d < c.1 := by
    simpa only [mk] using blocks_fst_gt d
      (if a == TM.Term.zero then d + 1 else d + 2) ladder
      (fun g => encvC ⟨if a == TM.Term.zero then g.1 else omLog g.1, by
        split
        · exact cnv_mem_summands _ g.1
            (cnv_ofList_take b _ (Evidence.WF.cnv_phi hcn).2) g.2
        · exact cnv_omLog (cnv_mem_summands _ g.1
            (cnv_ofList_take b _ (Evidence.WF.cnv_phi hcn).2) g.2)⟩ 0)
      hs hladder he
  have hunit_ne : unit ≠ [] := by
    by_cases ha : (a == TM.Term.zero) = true
    · simp [unit, ha]
    · simp [unit, ladder, ha]
  have hblock (g : {x // x ∈ summands b.splitFin.1}) :
      ladder ++ shiftD (if a == TM.Term.zero then d + 1 else d + 2)
        (encvC ⟨if a == TM.Term.zero then g.1 else omLog g.1, by
          split
          · exact cnv_mem_summands _ g.1
              (cnv_ofList_take b _ (Evidence.WF.cnv_phi hcn).2) g.2
          · exact cnv_omLog (cnv_mem_summands _ g.1
              (cnv_ofList_take b _ (Evidence.WF.cnv_phi hcn).2) g.2)⟩ 0) ≠ [] := by
    by_cases ha : (a == TM.Term.zero) = true
    · have hgcn : Evidence.WF.CNV g.1 = true := cnv_mem_summands _ g.1
          (cnv_ofList_take b _ (Evidence.WF.cnv_phi hcn).2) g.2
      have henc : encvC ⟨g.1, hgcn⟩ 0 ≠ [] :=
        encvC_ne_nil _ _ (mem_summands_ne_zero g.2)
      have hshift : shiftD (d + 1) (encvC ⟨g.1, hgcn⟩ 0) ≠ [] := by
        intro hmap
        exact henc (List.map_eq_nil_iff.mp hmap)
      have hshift' : shiftD (if a == TM.Term.zero then d + 1 else d + 2)
          (encvC ⟨if a == TM.Term.zero then g.1 else omLog g.1, by
            by_cases hh : (a == TM.Term.zero) = true
            · rw [if_pos hh]
              exact hgcn
            · rw [if_neg hh]
              exact cnv_omLog hgcn⟩ 0) ≠ [] := by
        simpa only [if_pos ha] using hshift
      exact List.append_ne_nil_of_right_ne_nil ladder hshift'
    · have hladder_ne : ladder ≠ [] := by simp [ladder, ha]
      exact List.append_ne_nil_of_left_ne_nil hladder_ne _
  have hmk_ne (hs : List {x // x ∈ summands b.splitFin.1}) (hhs : hs ≠ []) :
      mk hs ≠ [] := by
    simpa only [mk] using blocks_ne_nil ladder
      (if a == TM.Term.zero then d + 1 else d + 2)
      (fun g => encvC ⟨if a == TM.Term.zero then g.1 else omLog g.1, by
        split
        · exact cnv_mem_summands _ g.1
            (cnv_ofList_take b _ (Evidence.WF.cnv_phi hcn).2) g.2
        · exact cnv_omLog (cnv_mem_summands _ g.1
            (cnv_ofList_take b _ (Evidence.WF.cnv_phi hcn).2) g.2)⟩ 0)
      hs hhs (fun g _ => hblock g)
  rw [encvC]
  dsimp only
  split
  · rename_i hfp
    change ((encvC ⟨(summands b.splitFin.1).headD TM.Term.zero,
        cnv_headD (Evidence.WF.cnv_phi hcn).2⟩ d ++
        (if (summands b.splitFin.1).length == 1 then unit
         else mk ((summands b.splitFin.1).attach.drop 1)) ++ reps).getLast?
          = some (d, 0) ↔ Evidence.WF.kindV (TM.Term.phi a b) = true)
    have hsum : summands b.splitFin.1 ≠ [] := by
      intro hs
      rw [hs] at hfp
      exact Bool.noConfusion hfp
    have hkind : Evidence.WF.kindV (TM.Term.phi a b) ≠ true := by
      intro hk
      simp only [Evidence.WF.kindV, Bool.and_eq_true, beq_iff_eq] at hk
      rcases hk with ⟨ha, hb⟩
      subst a
      subst b
      exact Bool.noConfusion hfp
    let mid := if (summands b.splitFin.1).length == 1 then unit
      else mk ((summands b.splitFin.1).attach.drop 1)
    have hmid_gt : ∀ c ∈ mid, d < c.1 := by
      intro c hc
      dsimp only [mid] at hc
      split at hc
      · exact hunit c hc
      · exact hmk _ c hc
    have hmid_ne : mid ≠ [] := by
      dsimp only [mid]
      by_cases hlen : ((summands b.splitFin.1).length == 1) = true
      · rw [if_pos hlen]
        exact hunit_ne
      · rw [if_neg hlen]
        have hzero : (summands b.splitFin.1).length ≠ 0 := by
          intro hz
          exact hsum (List.length_eq_zero_iff.mp hz)
        have hone : (summands b.splitFin.1).length ≠ 1 := by
          intro ho
          apply hlen
          exact beq_iff_eq.mpr ho
        have htwo : 2 ≤ (summands b.splitFin.1).length := by omega
        exact hmk_ne _ (attach_drop_one_ne_nil htwo)
    have hsuf_ne : mid ++ reps ≠ [] :=
      List.append_ne_nil_of_left_ne_nil hmid_ne reps
    have hsuf_gt : ∀ c ∈ mid ++ reps, d < c.1 := by
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc
      · exact hmid_gt c hc
      · exact hreps c hc
    rw [show (if (summands b.splitFin.1).length == 1 then unit
        else mk ((summands b.splitFin.1).attach.drop 1)) = mid from rfl,
      List.append_assoc]
    constructor
    · intro hlast
      exact absurd hlast (getLast_ne_base_of_suffix d _ _ hsuf_ne hsuf_gt)
    · intro hk
      exact absurd hk hkind
  · split
    · rename_i z hdeep
      change ((encvC ⟨z.1, z.2.1⟩ d ++ mk (summands b.splitFin.1).attach ++ reps).getLast?
        = some (d, 0) ↔ Evidence.WF.kindV (TM.Term.phi a b) = true)
      have hsum : summands b.splitFin.1 ≠ [] := by
        intro hs
        have hhead : (summands b.splitFin.1).headD TM.Term.zero = TM.Term.zero := by
          rw [hs]
          rfl
        have hle : TM.Term.le z.1 TM.Term.zero = true := by
          simpa only [hhead] using z.2.2
        have hz : z.1 = TM.Term.zero := by
          simp only [TM.Term.le, show TM.Term.lt z.1 TM.Term.zero = false from
            Evidence.WF.ltF_right_zero _ _, Bool.or_false, beq_iff_eq] at hle
          exact hle
        exact (fpDeepC_some_ne_zero _ hdeep) hz
      have hkind : Evidence.WF.kindV (TM.Term.phi a b) ≠ true := by
        intro hk
        simp only [Evidence.WF.kindV, Bool.and_eq_true, beq_iff_eq] at hk
        rcases hk with ⟨ha, hb⟩
        subst a
        subst b
        exact hsum rfl
      have hatt : (summands b.splitFin.1).attach ≠ [] := by
        simpa using hsum
      have hmk_att_ne : mk (summands b.splitFin.1).attach ≠ [] := hmk_ne _ hatt
      have hsuf_ne : mk (summands b.splitFin.1).attach ++ reps ≠ [] :=
        List.append_ne_nil_of_left_ne_nil hmk_att_ne reps
      have hsuf_gt : ∀ c ∈ mk (summands b.splitFin.1).attach ++ reps, d < c.1 := by
        intro c hc
        simp only [List.mem_append] at hc
        rcases hc with hc | hc
        · exact hmk _ c hc
        · exact hreps c hc
      rw [List.append_assoc]
      constructor
      · intro hlast
        exact absurd hlast (getLast_ne_base_of_suffix d _ _ hsuf_ne hsuf_gt)
      · intro hk
        exact absurd hk hkind
    · change (((d, 0) :: ((match summands b.splitFin.1 with
          | [] => ladder
          | _ => mk (summands b.splitFin.1).attach) ++ reps)).getLast?
        = some (d, 0) ↔ Evidence.WF.kindV (TM.Term.phi a b) = true)
      let body := match summands b.splitFin.1 with
        | [] => ladder
        | _ => mk (summands b.splitFin.1).attach
      let rest := body ++ reps
      change (((d, 0) :: rest).getLast? = some (d, 0) ↔
        Evidence.WF.kindV (TM.Term.phi a b) = true)
      have hbody_gt : ∀ c ∈ body, d < c.1 := by
        intro c hc
        dsimp only [body] at hc
        split at hc
        · exact hladder c hc
        · exact hmk _ c hc
      have hrest_gt : ∀ c ∈ rest, d < c.1 := by
        intro c hc
        dsimp only [rest] at hc
        simp only [List.mem_append] at hc
        rcases hc with hc | hc
        · exact hbody_gt c hc
        · exact hreps c hc
      have hrest_of_kind (hk : Evidence.WF.kindV (TM.Term.phi a b) = true) : rest = [] := by
        simp only [Evidence.WF.kindV, Bool.and_eq_true, beq_iff_eq] at hk
        rcases hk with ⟨ha, hb⟩
        subst a
        subst b
        rfl
      have hkind_of_rest (hr : rest = []) :
          Evidence.WF.kindV (TM.Term.phi a b) = true := by
        have hh := List.append_eq_nil_iff.mp (show body ++ reps = [] from hr)
        have hbody_nil : body = [] := hh.1
        have hreps_nil : reps = [] := hh.2
        have hfin : b.splitFin.2 = 0 := by
          cases hn : b.splitFin.2 with
          | zero => rfl
          | succ n =>
              exact absurd hreps_nil
                (reps_ne_nil b.splitFin.2 unit (by rw [hn]; omega) hunit_ne)
        have ha_sum : a = TM.Term.zero ∧ summands b.splitFin.1 = [] := by
          dsimp only [body] at hbody_nil
          split at hbody_nil
          · rename_i hsum
            have ha : (a == TM.Term.zero) = true := by
              cases hane : (a == TM.Term.zero) with
              | true => rfl
              | false =>
                  exact absurd hbody_nil (by simp [ladder, hane])
            exact ⟨eq_of_beq ha, hsum⟩
          · rename_i g gs hsum
            have hatt : (summands b.splitFin.1).attach ≠ [] := by
              simpa using hsum
            exact absurd hbody_nil (hmk_ne _ hatt)
        have hbcn := (Evidence.WF.cnv_phi hcn).2
        have hbase : b.splitFin.1 = TM.Term.zero :=
          eq_zero_of_cnv_summands_nil (cnv_ofList_take b _ hbcn) ha_sum.2
        have hreb := splitFin_rebuild b hbcn
        have hb : b = TM.Term.zero := by
          rw [hbase, hfin] at hreb
          exact hreb.symm
        rw [ha_sum.1, hb]
        rfl
      constructor
      · intro hlast
        by_cases hr : rest = []
        · exact hkind_of_rest hr
        · exact absurd hlast
            (getLast_ne_base_of_suffix d [(d, 0)] rest hr hrest_gt)
      · intro hk
        rw [hrest_of_kind hk]
        rfl

theorem encv'_last_eq_base_iff : ∀ {t : TM.Term}, Evidence.WF.CNV t = true → ∀ d,
    (encv' t d).getLast? = some (d, 0) ↔ Evidence.WF.kindV t = true := by
  intro t hcn d
  induction t generalizing d with
  | zero =>
      unfold encv'
      rw [dif_pos hcn, encvC]
      dsimp only
      constructor
      · intro h
        contradiction
      · intro h
        exact Bool.noConfusion h
  | phi a b iha ihb =>
      unfold encv'
      rw [dif_pos hcn]
      exact encvC_phi_last_eq_base_iff hcn d
  | add u v ihu ihv =>
      obtain ⟨_, _, hcnv, hdesc⟩ := Evidence.WF.cnv_add hcn
      have hvz : v ≠ TM.Term.zero := by
        intro hv
        rw [hv, show Evidence.WF.hdLe TM.Term.zero u = false from rfl] at hdesc
        exact Bool.noConfusion hdesc
      have hvne : encv' v d ≠ [] := by
        unfold encv'
        rw [dif_pos hcnv]
        exact encvC_ne_nil _ d hvz
      rw [encv'_add_append hcn d,
        Evidence.StageA.getLast?_append_right (encv' u d) (encv' v d) hvne]
      exact ihv hcnv d
  | M => exact Bool.noConfusion hcn
  | omg a iha => exact Bool.noConfusion hcn
  | psi k a ihk iha => exact Bool.noConfusion hcn
  | Z a iha => exact Bool.noConfusion hcn

private theorem lnz_pair_eq_none_iff (x y : Nat) :
    BMS.lnz [x, y] = none ↔ x = 0 ∧ y = 0 := by
  cases x with
  | zero =>
      cases y with
      | zero =>
          have h : BMS.lnz [0, 0] = none := by rfl
          rw [h]
          simp
      | succ y =>
          have h : BMS.lnz [0, y + 1] = some 1 := by rfl
          rw [h]
          simp
  | succ x =>
      cases y with
      | zero =>
          have h : BMS.lnz [x + 1, 0] = some 0 := by rfl
          rw [h]
          simp
      | succ y =>
          have h : BMS.lnz [x + 1, y + 1] = some 1 := by rfl
          rw [h]
          simp

theorem kind_sqv'_zero : BMS.kind (sqv' TM.Term.zero) = BMS.Kind.zero := by
  unfold sqv' encv'
  rw [dif_pos (show Evidence.WF.CNV TM.Term.zero = true from rfl), encvC]
  dsimp only [toMatrix]
  rfl

theorem kind_sqv'_succ {t : TM.Term} (hcn : Evidence.WF.CNV t = true)
    (hk : Evidence.WF.kindV t = true) :
    BMS.kind (sqv' t) = BMS.Kind.succ := by
  have hlast : (encv' t 0).getLast? = some (0, 0) :=
    (encv'_last_eq_base_iff hcn 0).2 hk
  have hmatrix : (toMatrix (encv' t 0)).getLast? = some [0, 0] := by
    unfold toMatrix
    rw [List.getLast?_map, hlast]
    rfl
  unfold sqv' BMS.kind
  rw [hmatrix]
  rfl

theorem kind_sqv'_lim {t : TM.Term} (hcn : Evidence.WF.CNV t = true)
    (hk : Evidence.WF.kindV t = false) (hz : t ≠ TM.Term.zero) :
    BMS.kind (sqv' t) = BMS.Kind.lim := by
  have hne : encv' t 0 ≠ [] := by
    unfold encv'
    rw [dif_pos hcn]
    exact encvC_ne_nil _ 0 hz
  cases hlast : (encv' t 0).getLast? with
  | none =>
      exact absurd (List.getLast?_eq_none_iff.mp hlast) hne
  | some c =>
      have hcne : c ≠ (0, 0) := by
        intro hc
        subst c
        have hh := (encv'_last_eq_base_iff hcn 0).1 hlast
        rw [hk] at hh
        exact Bool.noConfusion hh
      have hlnz : BMS.lnz [c.1, c.2] ≠ none := by
        intro hh
        have hc := (lnz_pair_eq_none_iff c.1 c.2).1 hh
        exact hcne (Prod.ext hc.1 hc.2)
      cases heq : BMS.lnz [c.1, c.2] with
      | none => exact absurd heq hlnz
      | some n =>
          have hmatrix : (toMatrix (encv' t 0)).getLast? = some [c.1, c.2] := by
            unfold toMatrix
            rw [List.getLast?_map, hlast]
            rfl
          unfold sqv' BMS.kind
          rw [hmatrix]
          change (match BMS.lnz [c.1, c.2] with
            | none => BMS.Kind.succ
            | some _ => BMS.Kind.lim) = BMS.Kind.lim
          rw [heq]

theorem kind_sqv' {t : TM.Term} (hcn : Evidence.WF.CNV t = true) :
    BMS.kind (sqv' t) =
      (if t = TM.Term.zero then BMS.Kind.zero
       else if Evidence.WF.kindV t = true then BMS.Kind.succ else BMS.Kind.lim) := by
  by_cases hz : t = TM.Term.zero
  · rw [if_pos hz]
    subst t
    exact kind_sqv'_zero
  · rw [if_neg hz]
    cases hk : Evidence.WF.kindV t with
    | true =>
        rw [if_pos (by rfl)]
        exact kind_sqv'_succ hcn hk
    | false =>
        rw [if_neg (by intro h; exact Bool.noConfusion h)]
        exact kind_sqv'_lim hcn hk hz

example : BMS.kind (sqv' TM.Term.zero) = BMS.Kind.zero := kind_sqv'_zero

example : BMS.kind (sqv' TM.Term.one) = BMS.Kind.succ :=
  kind_sqv'_succ rfl rfl

example : BMS.kind (sqv' Evidence.WF.eps0T) = BMS.Kind.lim :=
  kind_sqv'_lim rfl rfl (by intro h; exact TM.Term.noConfusion h)

example {t : TM.Term} {fs : Nat → TM.Term}
    (hcn : Evidence.WF.CNV t = true) (hk : Evidence.WF.kindV t = false)
    (hz : t ≠ TM.Term.zero)
    (hrec : ∀ n, Evidence.Cert.Certified (BMS.expand (sqv' t) n) (fs n))
    (hlt : ∀ n, TM.Term.lt (fs n) t = true)
    (hstep : ∀ n, TM.Term.lt (fs n) (fs (n + 1)) = true)
    (hcof : ∀ s, TM.Term.inT s = true → TM.Term.lt s t = true →
      ∃ n, TM.Term.le s (fs n) = true) :
    Evidence.Cert.Certified (sqv' t) t :=
  Evidence.Cert.Certified.lim fs (kind_sqv'_lim hcn hk hz) hrec hlt hstep hcof

#print axioms mem_bumpAt_fst
#print axioms mem_shiftD_fst
#print axioms ladder_fst_gt
#print axioms unit_fst_gt
#print axioms reps_fst_gt
#print axioms blocks_fst_gt
#print axioms eq_zero_of_cnv_summands_nil
#print axioms mem_summands_ne_zero
#print axioms encvC_ne_nil
#print axioms reps_ne_nil
#print axioms blocks_ne_nil
#print axioms attach_drop_one_ne_nil
#print axioms getLast_ne_base_of_suffix
#print axioms encvC_fst_ge
#print axioms encvC_phi_last_eq_base_iff
#print axioms encv'_last_eq_base_iff
#print axioms lnz_pair_eq_none_iff
#print axioms kind_sqv'_zero
#print axioms kind_sqv'_succ
#print axioms kind_sqv'_lim
#print axioms kind_sqv'

end Evidence.SqV
