---
name: bms-rathjen-lean
description: Repo-local conventions for Lean work on the BMS × Rathjen correspondence table in bms-rathjen — project layout, definition-fidelity rules for BMS and T(M), evidence lemma conventions (E1/E2/E3), table generation, yaBMS crosscheck, and this repo's kimina instance. Load whenever writing or verifying Lean, editing Rows/tables, or spawning agents for this repo. General kimina ops live in the global skill `use-kimina-lean-server`.
---

# bms-rathjen-lean

Goal of this repo: a correspondence table between BMS (as an ordinal notation;
activation function generalized away, so matrices are used without `[n]`) and
Rathjen's ordinal collapsing functions, with machine-checked Lean evidence.
Master plan: `plan/README.md`. Target list & staging: `rathjen-ordinals.md`
(R1 = T(M) first).

## Layout (see plan/README.md for the full tree)

- `lean/` — Lean 4 lake project, toolchain `leanprover/lean4:v4.30.0`
  (same as pss-proof; kimina repl binary is reused). **No mathlib** for now:
  E1–E3 are syntactic; only add mathlib (pinned v4.30.0) if E4 semantics starts.
- Libraries: `BMS/` (matrices, order, expand, standard form), `TM/` (Rathjen
  T(M): terms, order, NF, fundamental sequences), `Trans/` (map o : BMS → T(M)),
  `Rows/` (table row DB + per-row lemmas), `Evidence/` (general theorems).
- `table/*.md` is **generated** by `lake exe gentable` from `Rows/` — never
  hand-edit; edit `Rows/` and regenerate.
- **THE PROOF PATH MUST NOT IMPORT THE CANDIDATE TIER.** `Evidence/Cert.lean` is
  the proof path — `certIn_rows_inT` is the gate that mints every ✅.
  `Evidence/SqV.lean` and `Trans/Recal.lean` (`oR`) are candidate tier. The arrow
  runs **candidate → proof**, never the reverse: a bridge lemma relating `sqv` to
  `Certified` goes in `SqV.lean` (which imports `Cert.lean`), NOT in `Cert.lean`.
  Reason: if `Cert` imported `SqV`, a candidate-tier lemma would become citable
  inside a certificate and a corpus change could break the gate's build. This
  makes "`oR` must not appear in a certificate's justification" a property of the
  module graph instead of a rule someone has to remember. Putting the bridge next
  to `Certified` is the natural move and it is the wrong one.
- `Rows.version` in `Rows/TM.lean` is rendered into the table header; bump it
  together with every /commitbump and regenerate the table before committing.
- **ANY edit to `Rows/TM.lean` requires regenerating the table — including a
  COMMENT-ONLY edit.** The generated table deep-links every row to its source
  line (`../lean/Rows/TM.lean#L86`), so adding lines anywhere above the row list
  moves all of them. Six lines added to the header comment moved 102 table lines
  with no value, name or ✅ changing, and CI's "gentable up-to-date" step would
  have failed. "Only row changes change the table" is false.

## Definition-fidelity rules

- **TM/**: follow Rathjen's papers exactly; every definition carries a comment
  citing paper + section/definition number.
  Sources (local): `~/proofs/papers/rathjen/`
  - `1990-Rathjen-Ordinal-notations-based-on-a-weakly-Mahlo-cardinal.pdf` — T(M), χ, ψ
  - `1991-Rathjen-Proof-theoretic-analysis-of-KPM.pdf` — self-contained syntactic T(M); prefer this for the term system
  - `1994-Rathjen-Collapsing-functions-...-well-ordering-proof-for-KPM.pdf` — recursive reconstruction
- **TM/FS.lean** (fundamental sequences) is NOT in the papers — it is a design
  choice. Document provenance (community usage, e.g. UNOCF) in comments; changing
  FS invalidates E3 rows, so treat its definition as frozen once rows depend on it.
- **BMS/**: follow koteitan's 数式的定義 (Googology Wiki article; local HTML in
  `~/proofs/papers/koteitan/`). Behavior (expand / compare / standard form) must
  match the C reference implementation `~/proofs/yaBMS/c/`
  ([github.com/koteitan/yaBMS](https://github.com/koteitan/yaBMS)) —
  run `scripts/crosscheck.sh` after touching BMS/.

## Evidence conventions (what a table row means)

Per row (matrix `Mᵢ`, term `tᵢ`), lemmas in `Rows/`:

- **E1** `row_i_trans : o Mᵢ = tᵢ` — by `rfl`/`decide`.
- **E3** `row_i_fs (n) : o (expand Mᵢ n) = fs tᵢ n` — n stays universally
  quantified; prove by induction/`simp`, not by finite sampling.
- **E2** (general, `Evidence/`): order embedding `M₁ < M₂ ↔ o M₁ < o M₂` on
  standard matrices — long-term; per-row pairs may be `decide`d meanwhile.
- **G** (one-sided structure, `Evidence/`): expand/fs are decreasing and cofinal,
  stated per side without `o`. **MT** (main theorem): otype equality of below-sets,
  conditional on well-foundedness of T(M); needs mathlib, written last.
  Label conventions are fixed in plan/README.md (D is reserved for definitions).

No well-foundedness proofs are required or attempted; "matrix = ordinal" claims
are formalized conditionally on well-foundedness. A failing E2/E3 is a *finding*
(the conjectured table entry is wrong) — report it, don't force the proof.

## Verification workflow

- Verify snippets via **this repo's own kimina instance on port 12346**, NOT the
  pss-proof one: port 12345 serves pss-proof's project and cannot import
  `BMS.*`/`TM.*`. Launch (env vars override the shared `.env`; server body lives
  in the pss-proof checkout):

  ```sh
  cd ~/proofs/pss-proof/kimina-lean-server && \
  LEAN_SERVER_PORT=12346 LEAN_SERVER_PROJECT_DIR=$HOME/proofs/bms-rathjen/git/lean \
    setsid nohup .venv/bin/python -m server > /tmp/kimina-rathjen.log 2>&1 &
  ```

  **FRESHNESS CANARY: put `#check @<a name you know is NEW>` at the top of every
  snippet you send.** A canary on an OLD name passes against a stale environment
  and tells you nothing — the same inverted-check trap as health-checking by
  substring, in its other direction. Incident 6 was found exactly this way: a
  `#check` on a name committed minutes earlier came back `Unknown identifier`
  while every older name in the same snippet resolved, so :12346 had been serving
  a stale WF olean for the whole session's snippet checks. Full-file POSTs
  re-elaborate from source and were unaffected, which is that discipline's real
  reason for existing.
  **The canary name must be new RELATIVE TO THE ENVIRONMENT BEING CHECKED, not new
  in absolute terms** — pick the newest name you have just committed. Do NOT write
  a specific identifier into this file: whichever one is named here becomes an old
  name and canaries nothing, silently.
  Health check: POST `{"snippets":[{"id":"t","code":"import BMS\n#check @BMS.expand?"}]}`
  to `http://localhost:12346/api/check`. **Do NOT health-check by substring-matching
  the name in the response** — an "unknown identifier NAME" ERROR contains the name
  too, so the check reads "present" exactly when it is absent. Check the message
  `severity` instead, or match on the printed TYPE. Kill selectively by PID (check
  `/tmp/kimina-rathjen.log` vs `/tmp/kimina-pss.log` instances before pkill).
  General ops (start/health-check/restart rules, multi-agent verification
  discipline): global skill `use-kimina-lean-server`.
- **kimina CACHES HEADER ENVIRONMENTS, and a poisoned one makes CORRECT CODE LOOK
  BROKEN.** A cascade of `unknown constant`/`unknown namespace` on BASIC names
  (`String`, `TM`, core prelude) is the server, not your snippet: a genuine error
  names one identifier you wrote; a poisoned header fails on names nobody typed.
  Diagnosed on a report that three imports together fail while any two work —
  Lean imports are order-insensitive, which already rules out the project.
  **The decisive tell is TIMING: the failure returns in ~0.1 s (cache hit) and the
  success in ~0.4 s (fresh elaboration).** A restart clears it; the byte-identical
  file then passes. Distinguish the two cache faults, because they mislead in
  opposite directions — stale oleans make NEW names unknown, which reads as "not
  built yet"; a poisoned header makes code that already passed fail unchanged,
  which invites working around a problem that does not exist or blaming another
  lane's file. **If something that just passed now fails unchanged, suspect the
  cache before the code**, and never conclude a defect from a fast failure.
- **HTTP 500 at ~31 s is a TIMEOUT, not a crash.** The default per-request
  ceiling is ~30 s, which full-file POSTs of `Evidence/WF.lean` started hitting
  once it passed ~8700 lines. Add a `timeout` field alongside `snippets`:
  `{"snippets":[…], "timeout": 300}`. With it the same file checks in ~78 s.
  Do not restart the server or bisect the file on a 500 near 31 s — raise the
  timeout first.
- **USE `leanman`, NOT BARE `lake build` OR HAND-ROLLED kimina POSTs.** Global
  skill `leanman`. `leanman check -C <project> FILE.lean` takes a SHARED lock so
  parallel checks are safe; `leanman build` takes an EXCLUSIVE one, so a build
  can never race a check or another build. **Judge by the EXIT CODE, never the
  output** — 0 green, 1 `sorry`, 2 error, 124 timeout, 143 killed; `lean` prints
  nothing on success, so empty output proves nothing. `leanman kill <id>`, never
  `pkill -f lean`. Measured need: a bare `lake build` here blocked **9m20s at
  `user 0m0.5s`** — not computing, waiting on lake's lock while several kimina
  REPLs elaborated `Evidence/WF.lean` (13800 lines) concurrently. **Full-file
  POSTs on `WF.lean` are no longer cheap**, and they contend with the build.
  For a proof that might not terminate use `--backend lean`: on the kimina
  backend a timeout reaps the client while the elaboration runs on inside the
  resident REPL, slowing every other agent ~10x.
- After editing `BMS/ TM/ Trans/` libs: `leanman build` + restart the rathjen
  instance (header cache). `Rows/` snippets sent as full text need no restart.
- **A FILTERED GREEN IS NOT A GREEN.** Filtering the checker's messages by line
  number to isolate "the new ones" will hide real errors whenever the bound is
  wrong, and it reports CLEAN rather than reporting nothing. It happened on a
  throwaway probe of three tactic variants — all three printed clean, the
  theorem went into the file, and only `#print axioms` returning `sorryAx`
  caught it. **The rule about checking the whole artifact and reading the raw
  result applies to disposable probes too**: the status of the tool does not
  lower how much its output gets trusted. Filter by `severity`, never by line
  number or substring.
- **A `sorryAx` READING IS MEANINGLESS UNLESS THE ERROR COUNT IS 0.** Lean fills
  a FAILED ELABORATION with `sorryAx`, so a declaration whose elaboration errored
  prints `[propext, sorryAx, Quot.sound]` with no `sorry` anywhere in the file —
  observed from a missing type annotation on a bound function, in the same POST
  as the error. **`sorryAx > 0` is the one number this repo treats as an
  unconditional regression, and this is how it false-alarms.** Read the error
  count first; on a broken build the axiom figures mean nothing at all. Recorded
  in `lean/scripts/axiom_sweep.lean`'s reading rules too.
- **A `sorryAx` READING IS MEANINGLESS UNLESS THE ERROR COUNT IS 0.** Lean fills
  a FAILED ELABORATION with `sorryAx`, so a declaration whose elaboration errored
  prints `[propext, sorryAx, Quot.sound]` with **no `sorry` anywhere in the
  file** — observed from a missing type annotation on a bound function, in the
  same POST as the error. **`sorryAx > 0` is the one number this repo treats as
  an unconditional regression, and this is how it false-alarms.** Read the error
  count first; on a broken build the axiom figures mean nothing at all. Also in
  `lean/scripts/axiom_sweep.lean`'s reading rules.
- **`#print axioms` IS THE BACKSTOP, NOT JUST AN AUDIT.** In that incident the
  build passed, the file contained no `sorry` token, and the line count grew as
  expected; `sorryAx` in the axiom list was the only surviving trace. Print
  axioms BY NAME for every declaration a report claims, before believing the
  report — including your own.
- **`omega` CLOSING A NON-ARITHMETIC GOAL SILENTLY IMPORTS `Classical.choice`
  INTO THAT DECLARATION AND EVERYTHING DOWNSTREAM.** The base case of an
  accessibility induction typically has contradictory hypotheses and the goal
  `Acc R t`; `have := deg_pos t; omega` closes it through
  `Classical.byContradiction`. Write `exact absurd hd (by have := deg_pos t; omega)`
  — `omega` stays on an arithmetic goal, nothing else changes. Two sites in
  `Evidence/WF.lean` (`acc_of_cn_aux`, `acc_cnv_aux`) put choice into `acc_cnv`,
  `acc_cnv_inT`, `acc_inT_below_cnv`, `wf_lt_cnv`, `wf_lt_belowC`, `belowC_wf`
  and thence into `Evidence/SqV.lean`'s `encvC`/`encv'`; the fix was `+15/-2`
  and made all of them `[propext, Quot.sound]`. Four more sites followed
  (`cof_fsGen_aux`, `cof_phiArg_aux`, `cof_phiArg1_aux`, `acc_lexLt`); at
  `acc_lexLt` the tactic was `simp at hl`, not `omega`, and there **the fix
  pattern did not transfer** — `exact absurd hl (by simp)` was still classical
  and it took explicit `Nat.succ_ne_zero` / `Nat.noConfusion`.
  **THE TRIGGER IS NOT CHARACTERISED, AND AN EARLIER VERSION OF THIS ENTRY
  OVERCLAIMED IT.** Minimal standalone probes do NOT reproduce the taint: bare
  `simp`, `simpa`, `omega`, `decide`, and `simp at hv` on a contradictory
  hypothesis with a non-arithmetic goal each came back `[propext]`. So "any
  decision tactic closing a non-arithmetic goal by contradiction" is a wider
  claim than the evidence supports. What IS established: **these six sites were
  tainted, explicit terms cleared them, and the only reliable detector is
  `#print axioms` — not a tactic-shape heuristic.** Reach for explicit
  discharge when a declaration measures dirty, not preemptively by grepping for
  tactics. **Guard each fix in the source** — shortening it back to the bare
  tactic is the natural edit and silently undoes it.
- **WHEN A DEPENDENCY BISECT SAYS "EVERY CHILD CLEAN, PARENT DIRTY", THE ANSWER IS
  IN THE PARENT'S TACTICS.** That reads as impossible and is not: a
  tactic-generated axiom has no constant to bisect, so the standard technique
  terminates with nothing to point at. **A clean dependency set is not evidence
  that a theorem is clean.** The technique that works is to rebuild the
  declaration line by line as a probe, printing axioms at each stage.
  Consumers see the taint with no indication of which upstream line caused it,
  so this is worth doing at the point of surprise rather than later.
- **AFTER VERIFYING A STAGED HASH, NEVER `git add` THAT PATH AGAIN.** The second
  `git add` re-stages whatever is on disk NOW, silently discarding the snapshot
  you verified. This defeated the fix for the rule below on its first use: the
  staged hash was checked, then the same command re-added the lane file
  alongside two docs, and the commit shipped bytes 25 lines newer than the
  message claimed. **Stage lane files and doc files in SEPARATE `git add`
  invocations, verify the lane file's staged hash last, and go straight to
  `git commit`** — or re-verify `git show :path | sha256sum` immediately before
  committing, since that is the only reading that survives an intervening add.
  **The general form, which is a category of its own: A CHECK'S RESULT HAS A
  LIFETIME, AND A LATER ACTION THAT LOOKS UNRELATED CAN EXPIRE IT.** The
  verification was correct when it ran; staging a documentation file destroyed
  its meaning, and nothing at the point of verification could have shown that.
  This is the rest of the file's instrument failures one level up — there the
  reading was wrong, here the reading was right and was silently invalidated.
  Ask of any check you rely on: **what could happen between this reading and the
  claim it licenses?**
- **COMPARE `git show :path | sha256sum` AGAINST THE VERDICT BEFORE COMPOSING THE
  COMMIT MESSAGE, NOT AFTER STAGING.** Checking the file's hash on disk and then
  `git add`ing it leaves a window the lane can write into; the commit then
  asserts a sha it does not contain. Happened once: verdict `b886241…`/13323
  lines, committed `12476f1…`/13346 lines, message claiming the former was
  "verified from the staged bytes". The mathematics was fine — the extra lines
  were the theorem bodies — but **the provenance line is the one that licenses
  trusting the rest**, so a false one is worse than a missing one. The rule is
  not "lanes must hold"; it is **nobody asserts what nobody measured**, and the
  coordinator has a half of it. **Do not amend to fix it** — this repo is pushed
  at times of the user's choosing, and rewriting a possibly-public commit trades
  one wrong record for a worse one. Correct forward with an explicit commit.
- **A SCATTERED PHENOMENON DOES NOT IMPLY A SCATTERED PROOF — do not predict
  proof difficulty from failure-mode similarity.** Coordinator heuristic offered
  and refuted the same hour: "if `c < a`'s failures cluster at the fixed-point
  boundary like `c = a`'s, the route follows; if they scatter, it is genuinely
  new." They scattered — `c = a` fails by a hair with `φ̄(a, g 0) = b` exactly,
  `c < a` fails because `d` outruns a low-starting sequence and `b` is not a
  fixed point of anything — **and the same route closed both, four lines apart.**
  Two motions that look like they need trading off (here `d` shrinking against
  `g`'s index growing) may need no measure at all: **the existential absorbs the
  index and the order absorbs the shrinkage.** That is the same answer the
  encoder side reached when its termination measures died and the route turned
  out to be the order.
- **`rw [← h]` REWRITES EVERY OCCURRENCE, INCLUDING INSIDE SUBTERMS OF THE
  VARIABLE ITSELF.** Rewriting a goal backwards over `p` also hits the `p` inside
  `predC p`, which is rarely what you want. **Transport the lemma instead**
  (`rw [h] at hlc`) rather than the goal. Cost of getting it wrong is not a
  failed tactic but a failed elaboration — see the `sorryAx` rule above, which
  this triggered twice.
- **CHECK A RECORDED CLAIM BEFORE ACTING ON IT, INCLUDING YOUR OWN.** A lane had
  written that §15.20 supplies `succT (predC ·)` only for `kindC`; it is stated
  at `kindV`, exactly the predicate the assembly dispatches on, so core (B)
  needed no bridge at all. **The alternative was re-deriving a lemma that already
  existed at the right generality** — the tenth ancestor-already-exists of the
  session, and the only one where the false record was the lane's own note rather
  than a guessed name.
- **A THEOREM WHOSE HYPOTHESES CANNOT BE MET COMPILES EXACTLY LIKE ONE WHOSE
  HYPOTHESES CAN. THE ONLY INSTRUMENT THAT DETECTS IT IS A CONSUMER.** The
  `asm_general*` assembly was verified, cleanly axiomed, four of five branches
  discharged, every hypothesis honestly stated — and vacuous, because `Hnf` is
  refuted by a counterexample three sections above it in the same file. **This
  is NOT the C4 vacuity already catalogued**: there an antecedent failed to fire
  *on a corpus*, and widening the corpus might have fired it; here it cannot
  fire at all. **Route a real consumer through any theorem whose hypotheses you
  wrote yourself, before proving more of it.** Two lanes hit this on unrelated
  work in one session (`sqv_decomp`'s five suppliers, the assembly's four
  branches); both times the cost was bounded only because the consumer was
  written at item one rather than item ten.
- **GUARDING A HYPOTHESIS BY ITS CASE DOES NOT RELATIVISE IT TO THE TERMS THAT
  CASE CAN RECEIVE.** A guard sits at BRANCH level; the quantifier sits at
  THEOREM level; a structural recursion only ever visits sub-terms of the `t` it
  is applied to. So a caller with one row is asked about terms their row never
  reaches — including exactly the ones the guard was written to exclude.
  **Relativise hypotheses to sub-terms of the recursion's argument, not merely
  to the case that consumes them.** And distinguish the damage before fixing:
  a hypothesis that is TRUE but unproved is badly *placed*; one that is FALSE is
  badly *stated*, and only the second invalidates the theorem.
- **AN ASSUMED BRANCH IS WORTH RE-READING ONCE THE RECURSION EXISTS.** The cost
  of an assumption is invisible at the point where it was made: the theorem
  compiles, the hypothesis looks reasonable, and nothing flags it. `asm_general`
  assumed core (C') because §15.19's branch list predated the recursion and was
  never revisited once it existed — while `a` is a structural subterm of
  `φ̄(a,0)`, so `induction t` had been handing the clauses over for free and the
  IH was being **discarded with an underscore**. **Sibling of the rule below,
  with the opposite conclusion: an unused HYPOTHESIS means the statement is
  wrong; an unused INDUCTION hypothesis means it is weaker than it needs to be.**
  Grep your own proofs for `_` in the induction-hypothesis position before
  accepting a hypothesis list as final.
- **AN UNUSED HYPOTHESIS IS A TELL THAT THE STATEMENT IS WRONG.** A proof that
  resists may be reporting a defect in its own statement rather than a hard
  piece of mathematics. The signal that distinguishes them: **you cannot find a
  use for one of the hypotheses you were given.** `hside` was attacked for a
  long stretch in the `le b (φ̄(a, g 0))` form, which is false; cofinality —
  clause 4 of `LimClauses` — was the clause that could not be used. Restated as
  `∃ k, lt b (φ̄(a, g k))`, two branches fell out of clause 4 in a dozen lines
  each. **Before grinding, list the hypotheses and point at where each one is
  consumed.** Any that has no consumer is either superfluous or the one the
  statement should have been built around.
- **THE FAILURE NO CONTROL CATCHES: AN EXPLANATION ATTACHED TO A CORRECT
  MEASUREMENT.** Both of one lane's substantive errors in a session were of this
  kind — the numbers were right and the sentence wrapped round them was wrong
  (`CarrierV` as "the fact that makes the assembly possible now"; `φ̄(0,ε₀)` as
  "is ε₀, not a normal form"). **A control tests whether the instrument can
  fire, not whether the story about the result is true**, so measurement
  discipline and axiom hygiene both leave this flank open. What caught both was
  **someone restating the claim back in a form its author could check** — which
  is an argument for relaying claims verbatim and for the coordinator
  re-deriving a lane's reason rather than only its number. Corollary for the
  coordinator: your own version of this is amplifying a scoped observation into
  a justification (below), and it has the same detector.
- **A WORD THAT IS TRUE OF THE ORDINALS CAN BE FALSE OF THE MATRICES — this is
  the correspondence the repo exists to establish, so never assume it.**
  `expand (epsM 1) k` has `oR` equal to `ω^(ε₀·2)`, `ω^(ω^(ε₀·2))`, … — a tower,
  genuinely. **The matrices are not `towerM`**: they are a two-column-per-step
  family `[j,0],[j+1,1]`, while `towerM` is one column per step and `famM`
  alternates `[0,0]`/`[1,1]`. `cert_tower` proves its family via `cert_padSq` on
  a `CN` term and these matrices are not `padRow (sq c)` for any `c`, because
  the second row is not constant. So "generalise `cert_tower` over its base" does
  not reach it — **the base is not what differs, the per-step block is.**
  Check the matrix shape by `#eval` before reusing a certificate family whose
  ORDINAL description matches.
- **LANE PROTOCOL: THE VERDICT IS THE LAST THING A LANE DOES, AND ACKS CARRY NO
  WORK.** After sending a verdict a lane makes no further writes to that file
  until the coordinator acks. Five sha mismatches in one evening, the last five
  lines wide; **the bytes were never wrong and every verdict was true when
  sent** — what kept passing was the moment, which the sha convention cannot
  catch and only the hold can. The coordinator half is the harder one: an ack
  that also assigns work **has no unambiguous END** — "resume, and also do X"
  makes the hold expire the instant the lane starts X, so the file moves before
  the coordinator can read the sha. Ack and task travel as separate messages;
  a lane receiving an ack with work in it treats it as "ack, then wait".
- **TWO INSTRUMENTS AGREEING ON 0 IS NOT CORROBORATION UNLESS BOTH HAVE
  CONTROLS.** A `branchOf` dispatch classifier's `FIFTH` bucket was dead code —
  it tested `kindV b` first and routed every successor `b` away before the
  fifth-shape test could run, and the fifth shape *is* `a` limit with `b` a
  successor, so the one case it existed for could never reach it
  (`branchOf (φ̄(ω,1))` returned `terminal`). Its 0 was vacuous **and it agreed
  with an independent detector's meaningful 0.** Indistinguishable from the
  output. Run the positive control on EVERY bucket that reports 0, including
  the ones a second instrument seems to confirm.
- **DISTINGUISH "NO INSTANCE ANYWHERE" FROM "NO INSTANCE DOWNSTREAM OF THIS
  CORPUS" — they both print 0.** At depth 4 the fifth shape is genuinely absent
  (detector returns 1 on a hand-built `φ̄(ω,1)`), while core (C') is also 0 yet
  reachable — `branchOf (φ̄(ω,0))` and `branchOf (φ̄(ε₀,0))` return `coreC'`, and
  `lim_clauses_phiW0` / `lim_clauses_phiE0` are proved rows that land there. A
  branch unreached by the closure of 21 roots is still required by the theorem.
  Collapsing the two readings drops a needed branch.
- **THE COORDINATOR'S RECURRING FAILURE IS AMPLIFYING A LANE'S SCOPED
  OBSERVATION INTO A JUSTIFICATION.** Twice in one session. A lane said the
  carrier is `BelowC`; that became "it is answered, not open" over four
  messages, and the answer was `CarrierV`. A lane said `CarrierV`/`wf_lt_cnv`
  answers §15.19's measure problem; that became "the fact that makes the
  assembly worth doing now", and then the spikes showed the assembly's
  recursion is STRUCTURAL and needs no measure at all — the observation was
  true and was not the justification. **The tell is a claim of the form "this
  is why X is possible now", which is a story rather than a measurement**, and
  it survives review because the underlying fact is real. Restate a lane's
  claim in their scope, and when tempted to say what it makes possible, ask for
  the spike instead.
- **A REQUEST TO CHARACTERISE SOMETHING IS WORTH ONE `#eval` BEFORE IT IS WORTH
  ONE THEOREM — the characterisation may already be a composition of things you
  have.** Asked for the 𝔗(M)-side facts about `summands (fsC ω² n)` because the
  row's subscript "was neither empty nor a replicate", a lane `#eval`ed the list
  first and found `fsC ω² n = repAdd ω n` — a replicate, uniform, length `n+1`,
  no degeneracy at `n = 0`. The premise of the task was false, and both halves
  were already proved, one per lane (`fsC_omegaSq` in `Evidence/WF.lean`,
  `summands_repAdd` in `Evidence/SqV.lean`); they compose in one `rw`.
  **Going straight to the proof would have produced a true, green,
  correctly-formed lemma duplicating two existing ones** — the wrong-form
  failure reached without anyone ever stating a wrong form. Measuring first
  did not shape the statement, **it deleted it**. A compound-looking argument
  (`φ̄(0,1+1)`) says nothing about the shape of its fundamental sequence.
- **THERE ARE THREE WAYS `Classical.choice` ARRIVES, AND ONLY THE FIRST IS OURS.**
  (1) *tactic-introduced* — the six `Evidence/WF.lean` sites; cleanable, cleaned.
  (2) *lemma-inherited* — the cited lemma itself carries choice.
  (3) **instance-inherited** — the lemma is clean and INSTANTIATING it is not.
  Measured, and the reason the gate cannot be cleaned:

  ```
  List.max?_mem                          [propext]
  List.max?_mem h  at α = Nat            [propext, Classical.choice, Quot.sound]
  Std.instMaxEqOrOfLawfulOrderLeftLeaningMax
                                         [propext, Classical.choice, Quot.sound]  ← the root
  Std.instLawfulOrderLeftLeaningMaxOfIsLinearOrderOfLawfulOrderSup   [propext]
  Nat.instIsLinearOrder                  [propext]
  BMS.parent                             [propext]
  ```

  Class 3 answers to neither tactic hygiene nor picking a different lemma —
  swapping `List.max?_eq_some_iff` for the clean `List.max?_mem` changes
  nothing. **So "def-side taint is core's, proof-side taint is ours" is wrong
  as stated: a PROOF can inherit from core through an INSTANCE**, and
  `Evidence.Cert.certIn_rows_inT` — the registry gate — does, through
  `List.max?` reached via `BMS.parent`, even though `BMS.parent` is `[propext]`.
  When a declaration measures dirty and its cited lemmas are clean, **print
  axioms of the synthesised instance** (`#synth` then `#print axioms`) before
  concluding anything about tactics.
- **Sweep for axiom hazards by OUTCOME, not by grep.** `#print axioms` over the
  public surface answers the question; grepping `omega` cannot, because the
  hazard is defined by what the GOAL was. A clean grep reads as a clean sweep and
  is not one. Report the full list including legitimate uses of choice — a sweep
  that reports only hits is indistinguishable from one that found nothing.
- **The coordinator must restart :12346 after every `lake build`, and must
  VERIFY the restart rather than assume it.** The server silently keeps serving
  the oleans it started with, so a lane that verifies against it after a rebuild
  gets stale-environment failures that look like real errors.
  The failure mode is NOT a skipped restart — it happened four times with the
  restart present, because putting the restart in the SAME command as the build
  races the build's own olean writes. Run it after `lake build` returns, then
  check mtimes:

  ```sh
  stat -c '%Y %n' .lake/build/lib/lean/Evidence/*.olean   # every one must be
  stat -c '%Y' /proc/$(ss -tlnp | grep -oP '12346.*pid=\K[0-9]+' | head -1)
  ```

  The server's start time must exceed every olean mtime. Then health-check
  against a name you know is NEW, by `severity`, never by substring.
- Parallel agents never run `lake build`; coordinator builds once. When a lane
  is mid-write, the coordinator's build will fail on THAT file — commit the
  other lane's verified file alone (no version bump, so no table regeneration)
  rather than waiting or committing an unverified state.
- **Editing a large file AFTER compaction**: do not reproduce it by a full-file
  `Write` from context — an 8000-line file is not in context any more, and
  regenerating it is the corruption the full-file rule exists to prevent. Instead:
  confirm the on-disk hash matches HEAD *before* touching anything (if it does
  not, someone else's work is uncommitted — stop), re-read each region
  immediately before editing it, make anchored `Edit`s against text just read,
  and POST the complete on-disk file afterwards. The verification half of the
  discipline is what matters and it stays intact; say in the checkpoint that the
  `Write` half was not used, so the coordinator knows rather than infers.
- **A refactor that claims to preserve statements must have the STATEMENTS
  compared, not just the build.** Green means the file elaborates, not that a
  theorem still says what it said. Extract the old text with
  `git show HEAD:<path>` and diff each signature, and diff the declaration-name
  lists both ways — removals should be exactly the specialised versions their
  general replacements subsume, and nothing else.
- **The REQUESTER's half of routing: state the shape you NEED and the weaker shape
  you could LIVE WITH, in the same message.** The producer cannot know how much
  slack exists unless you say. Twice tonight a routed fact came back STRONGER than
  requested — `le_plus_one_of_lt_cnv` without the limit hypothesis, `lt a (φ̄(a,b))`
  with no restriction — and both times the mechanism was the requester having named
  the fallback: aiming at the general statement was safe because a restricted one
  would still have landed. No incentive to under-reach, no risk in over-reaching.
- **RELAYING BETWEEN LANES IS ITSELF AN INSTRUMENT, and the coordinator is the
  only one who can check it.** A lane's measurement carries a scope; restating it
  for the other lane drops the scope unless you copy it deliberately. Happened
  twice: a count relayed as if it were a set, and a measurement reported as
  "0 violations of 40 on the RELEVANT terms" relayed as an unconditional identity
  — which was FALSE, 569 of 578, because "relevant" was carrying the hypothesis.
  **Quote the qualifier verbatim, or say you are dropping it.** The receiving lane
  cannot see the original and will prove what you wrote.
  **And the asymmetry that makes this bite: a lane can check its own measurement,
  and can check a lemma it is handed — but it CANNOT check a hypothesis that was
  never relayed.** There is nothing in the artifact to notice. Both of the cases
  above were caught only because the receiving lane MEASURED the claim before
  proving it, which means **measure-before-proving doubles as the relay check** —
  cheaper and more reliable than the coordinator auditing its own relays, which
  is the thing that failed twice. Tell a lane receiving a relayed claim to measure
  it first, and it will catch what you dropped.
- **DESCRIBE STATE FROM THE REPOSITORY, NOT FROM A LANE'S REPORT.** A checkpoint
  describes the world as it was when the lane started writing it; by the time it
  is read, the work it announces is committed. The coordinator once described a
  queue — "they still owe the bridge" — in the same turn as committing the file
  that contained the bridge, and routed from that model until a lane checked
  `git show HEAD:` and corrected it.
  **BUT HEAD IS STALE IN THE OTHER DIRECTION TOO, and that half bites harder: HEAD
  lags every lane's uncommitted work, and in this project the lanes cannot commit.
  The coordinator is the only path from verified-on-disk to HEAD.** Read state
  only from HEAD and verified work waits indefinitely with nothing in your model
  saying it is ready. The reconciler is mechanical:

      HEAD is authoritative for what has LANDED.
      A lane report is the only signal that something is READY to land.
      `git status` reconciles them: report says done + DIRTY tree for that lane's
      file -> commit it. Report says done + CLEAN tree -> it is already in and
      your model is behind.

  **And grep for the CONCEPT, not the name you expect — this is the one to do
  FIRST, because it is the only check here that fails SILENTLY.** Checking for
  `lt_fpDeep` and concluding the clause was unproved missed `le_fpDeep`, which was
  sitting on disk: the check was aimed at the right thing with a pattern that
  presumed its name, and **a wrong-name grep returns a clean empty result that
  looks exactly like a true absence.** The name was also unguessable on purpose —
  the conclusion is `le` because `fpDeep a t` returns `t` itself on 6 of 24
  triples, so `lt_fpDeep` was never going to exist. **A theorem's name is a
  neighbour of its statement.**
- **When a lane reports a MEASUREMENT, ask WHICH CORPUS before building on it.**
  The count-vs-set rule below has a twin: a number can be honest, verifiable and
  useless because the corpus could not reach the failure class. It happened —
  a route was proposed on the strength of "0 violations of 15", the 15 contained
  no `add`-headed components, and the route was false at exactly those. The lane
  did not hide the corpus; nobody asked. **"How many?" and "over what?" are two
  questions and only the second is ever omitted.** The reason is structural: the
  count travels with the claim and the corpus stays in the head of whoever ran it.
  **So the fix belongs on the REPORTING side — SHIP THE CORPUS WITH THE NUMBER.**
  One clause, and nobody has to remember to ask.
  **The same collapse has a second form: "defined on X" is not "produces X".** A
  total function is DEFINED on junk; that does not mean a legal input makes it
  produce junk arguments. Measured: from 169 legal starts, `encvF`'s recursion
  yields 0 targets outside 𝔗(M), while 10 of 42 junk starts do — so the junk
  behaviour was real and never occurred. Do not infer the reachable set from the
  domain.
- **When a lane reports a COUNT, ask for the SET before acting on it.** The
  coordinator cannot verify a count from a report — the members are not in it —
  so accepting one is accepting an unverified claim, and repeating it in an
  ack amplifies it. This happened: a lane reported that a candidate fix "does not
  move the four failures at all", the coordinator singled that sentence out as a
  good result, and the two failing sets turned out to be DISJOINT. Seeing the sets
  gave the correct condition on sight where the counts had given nothing. The
  rule the lanes are held to (decode a member before reporting a bucket) applies
  to the coordinator's reading of their reports, not only to their own work.
- **Commit messages carry the reasoning, not just the change — and the reason is
  that they are the only artifact read IN ORDER.** File state is read once, at
  whatever version you find; messages are read as a sequence, so a superseded
  claim in one needs its correction in a later one, not only in a diff. Tonight a
  lane caught a wrong target-shape claim in a commit message by reading the
  history the way a later reader would rather than the way its author did — and
  that is only possible because the messages are substantive. **If they were
  "fix" and "wip" there would be nothing to read wrongly, and also nothing to
  catch.**
- **NEVER RUN A MUTATING GIT COMMAND ON A LANE-OWNED FILE WHILE THAT LANE IS
  ACTIVE.** `git stash push -- <lane file>`, `git checkout -- <lane file>`,
  `git restore` — each reverts the lane's working file mid-edit. Done once, to
  isolate one file for verification; restored within seconds and byte-identical,
  so nothing was lost, but a write inside that window would have made the lane's
  own file look corrupted **for a reason the lane could not diagnose**. To verify
  one file in isolation, build the tree as it stands and read the axioms by name —
  the other lane's in-flight file either builds or names itself in the error.
  Tell the lane if it happens anyway: a file changing under an agent with no
  message is otherwise attributed to itself.
- **Read the SNAPSHOT, not the working file.** `git add` freezes the bytes; the
  lane keeps writing. Any math check done by `grep`/`sed` on the path afterwards
  is a check of the lane's CURRENT file, not of what is staged. Once, a commit
  message described a section that the commit did not contain, because the lane
  added it in the seconds between staging and reading. Verify with
  `git show :lean/Evidence/WF.lean | grep …` (or diff the staged blob), and
  compare the report's sha256 the moment it arrives — if it already differs, the
  snapshot opportunity is gone and the right move is to hold that file and ask
  the lane to re-report, not to commit bytes nobody has verified.
  **On any build failure, read WHICH FILE failed before deciding.** If it is
  another lane's file — tracked and mid-write, or a new UNTRACKED file it is
  drafting — the file you are committing may still be sound, and it is sound
  exactly when the build reached (and passed) it before failing. Do not commit
  first and check afterwards; that has worked by luck.
- Generate the table to a scratch path and `diff` before installing it:
  running `gentable` while a lane is mid-write truncated `table/r1-tm.md` once.
  `gentable` writes to STDOUT and must be run from `lean/`:
  `lake exe gentable > ../table/r1-tm.md`.
- **Grep before writing a lemma.** Five times in one session a lemma a lane was
  about to write already existed — usually stated for an earlier, narrower
  fragment (CN before CNV) or by a retired agent for a neighbouring row. Search
  `Evidence/` for the statement SHAPE (the conclusion's head symbol and the main
  hypothesis), not for the name you would have chosen; the existing name is
  rarely the one you would pick. Re-deriving now costs more than grepping.
  **And the reliable form: WRITE THE STATEMENT YOU WISH EXISTED, THEN GREP FOR
  IT.** Searching the words of your PROBLEM misses facts that answer it without
  resembling it — `cnv_of_lt_cnv` ("below a normal form there is nothing but
  normal forms") is the answer to "is `CNV` free on my carrier", and no grep
  phrased from the second finds the first. The lane that found it conjectured the
  statement and measured it, which reaches the same place more reliably than
  searching does.
  Related but distinct: when the ancestor exists for a narrower fragment, widen
  it by RE-DERIVING, not by porting (constitution W3).
- **The same applies to METHODS, not just lemmas.** When a step looks blocked,
  grep the section headers for how this file has handled the same shape before.
  The undershoot step sat recorded as blocked while §15's own header already
  named the technique that dissolves it — "put the unconstrained object on the
  side of the relation the decision procedure reads LAST" — and called it a
  reusable discipline. A file that documents its methods will hand you the
  answer before you design one.
  **The cheap tell that you are in a failing CATEGORY rather than a failing
  attempt: the second failure has the same ERROR TEXT as the first.** Not the same
  tactic — the same message. Twice tonight an improvement-loop ran four rounds
  where the second round's message already said the category ("motive is not type
  correct", "the goal's shape is not uniform"), and both times naming the category
  closed it in one. Read the message, not the tactic.
  **A template's value is the QUESTIONS IT FORCES, not the code it saves.**
  Reading `ltF_stable` before designing `encvF_saturate` did not supply the
  induction skeleton — that would have been reconstructed anyway. It supplied
  "what is its measure, and does mine work?", and the answer was that `deg`
  fails on exactly four terms. Ask a template what it assumes, not just what it
  does.

## Publishing rules (public repo)

- Committed docs (`README.md`, `plan/`, `table/`, `rathjen-ordinals.md`) must not
  reference local paths (`~/proofs/...`) — online readers can't see them; cite
  bibliographic info and public URLs instead
  (BM4 analysis sheet: <https://docs.google.com/spreadsheets/d/1Y4BV65KNPjJ6uBtBBFYDXKo6PFlmEuowyn39XmLh4MI/edit?usp=sharing>).
  This SKILL.md and comments in Lean sources are the exception (working notes).
- Math in .md uses GitHub-rendered MathJax; avoid `|` inside math in tables.
- git commit/push only when the user says so.
