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

end Evidence.SqV
