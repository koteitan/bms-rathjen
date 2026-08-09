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
- `Rows.version` in `Rows/TM.lean` is rendered into the table header; bump it
  together with every /commitbump and regenerate the table before committing.

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

  Health check: POST `{"snippets":[{"id":"t","code":"import BMS\n#check @BMS.expand?"}]}`
  to `http://localhost:12346/api/check`. **Do NOT health-check by substring-matching
  the name in the response** — an "unknown identifier NAME" ERROR contains the name
  too, so the check reads "present" exactly when it is absent. Check the message
  `severity` instead, or match on the printed TYPE. Kill selectively by PID (check
  `/tmp/kimina-rathjen.log` vs `/tmp/kimina-pss.log` instances before pkill).
  General ops (start/health-check/restart rules, multi-agent verification
  discipline): global skill `use-kimina-lean-server`.
- **A cascade of `unknown constant`/`unknown namespace` on BASIC names (`String`,
  `TM`, core prelude) means the SERVER ENVIRONMENT is broken, not your snippet.**
  A genuine error names one identifier you wrote; a broken environment fails on
  names nobody typed. Reported once as an import-order defect ("these three
  imports together fail, any two work") — it did not reproduce under either
  `lake env lean` or the same server minutes later, and the real cause was a
  restart in flight. Before reporting an import or elaboration defect, re-run it
  after confirming the server is up and its start time postdates every olean.
- **HTTP 500 at ~31 s is a TIMEOUT, not a crash.** The default per-request
  ceiling is ~30 s, which full-file POSTs of `Evidence/WF.lean` started hitting
  once it passed ~8700 lines. Add a `timeout` field alongside `snippets`:
  `{"snippets":[…], "timeout": 300}`. With it the same file checks in ~78 s.
  Do not restart the server or bisect the file on a 500 near 31 s — raise the
  timeout first.
- After editing `BMS/ TM/ Trans/` libs: `lake build` + restart the rathjen
  instance (header cache). `Rows/` snippets sent as full text need no restart.
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
  Related but distinct: when the ancestor exists for a narrower fragment, widen
  it by RE-DERIVING, not by porting (constitution W3).

## Publishing rules (public repo)

- Committed docs (`README.md`, `plan/`, `table/`, `rathjen-ordinals.md`) must not
  reference local paths (`~/proofs/...`) — online readers can't see them; cite
  bibliographic info and public URLs instead
  (BM4 analysis sheet: <https://docs.google.com/spreadsheets/d/1Y4BV65KNPjJ6uBtBBFYDXKo6PFlmEuowyn39XmLh4MI/edit?usp=sharing>).
  This SKILL.md and comments in Lean sources are the exception (working notes).
- Math in .md uses GitHub-rendered MathJax; avoid `|` inside math in tables.
- git commit/push only when the user says so.
