---
name: pss-rathjen-lean
description: Repo-local conventions for Lean work on the BMS × Rathjen correspondence table in pss-rathjen — project layout, definition-fidelity rules for BMS and T(M), evidence lemma conventions (E1/E2/E3), table generation, yaBMS crosscheck, and this repo's kimina instance. Load whenever writing or verifying Lean, editing Rows/tables, or spawning agents for this repo. General kimina ops live in the global skill `use-kimina-lean-server`.
---

# pss-rathjen-lean

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

- Verify snippets via **this repo's own kimina instance**, NOT the pss-proof one:
  port 12345 serves pss-proof's project and cannot import `BMS.*`/`TM.*`.
  At S0, create a second instance: own `.env` with `LEAN_SERVER_PROJECT_DIR` →
  this repo's `lean/`, a fresh port (never 8000/8080), log `/tmp/kimina-rathjen.log`.
  General ops (start/health-check/restart rules, multi-agent verification
  discipline): global skill `use-kimina-lean-server`.
- After editing `BMS/ TM/ Trans/` libs: `lake build` + restart the rathjen
  instance (header cache). `Rows/` snippets sent as full text need no restart.
- Parallel agents never run `lake build`; coordinator builds once.

## Publishing rules (public repo)

- Committed docs (`README.md`, `plan/`, `table/`, `rathjen-ordinals.md`) must not
  reference local paths (`~/proofs/...`) — online readers can't see them; cite
  bibliographic info and public URLs instead
  (BM4 analysis sheet: <https://docs.google.com/spreadsheets/d/1Y4BV65KNPjJ6uBtBBFYDXKo6PFlmEuowyn39XmLh4MI/edit?usp=sharing>).
  This SKILL.md and comments in Lean sources are the exception (working notes).
- Math in .md uses GitHub-rendered MathJax; avoid `|` inside math in tables.
- git commit/push only when the user says so.
