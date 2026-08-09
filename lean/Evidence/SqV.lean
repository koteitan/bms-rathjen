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

    D7 domain          24 DISTINCT terms (48 list entries)
      11 named rows    φ̄(1,0), φ̄(1,1), φ̄(1,2), φ̄(1,3), φ̄(1,ω), φ̄(1,ω²), φ̄(1,ω^ω),
                       φ̄(1,ε₀), φ̄(2,0), φ̄(1,ζ₀), φ̄(ω,0)
                       — TERMS, not ordinal names.  An earlier draft called the tenth
                       `ε_{ζ₀}`; the table names that row `ε_{ζ₀+1}`, and under the skip
                       convention the table is right, since ζ₀ is already a fixed point
                       of `φ̄(1,·)` so `φ̄(1,ζ₀)` is the NEXT ε-number after it.  §6's
                       fact has caused three defects tonight; an off-by-one ordinal name
                       in a header is the fourth waiting to happen, so the domain is
                       written as terms throughout.
      13 CN limits     paired with `Evidence.WF.fsC` (37 entries)
    no bundle         145 of the 169 distinct terms

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

open Evidence.WF (fsC tower fsEW fsEW2 fsEWW fsEE fsZeta0 fsEZ fsEsucc)

def bundles : List (Term × (Nat → Term)) :=
  [(phi one zero, tower),
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
          Trans.oR (BMS.expand (sqv p.1) n) == some (p.2 (n + 1)))))).length == 11
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
#guard ((bundles.map (fun p => p.1)) ++ cnLims).eraseDups.length == 24
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

BLOCKER 2 — `Certified` IS IN `Evidence/Cert.lean`, WHICH DOES NOT IMPORT THIS FILE.
`sqv_decomp` as an expansion identity lives here and needs nothing from `Cert`.  The
bridge that turns it into `Certified (sqv t) t` needs both, and the import must therefore
run `Cert → SqV`, which changes `Cert`'s build dependencies.  That is a coordinator
decision, not one to take by writing an `import` line.

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

end Evidence.SqV
