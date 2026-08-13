import BMS
import TM
import Trans
import Rows
import Evidence
import Evidence.WF
import Evidence.Cert
import Evidence.StageB
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# `scripts/axiom_sweep.lean` — WHAT THE REPO ACTUALLY DEPENDS ON

Not part of the build.  Run it through the kimina instance (port 12346) as a full-file POST,
or `lake env lean scripts/axiom_sweep.lean`.

## Why this exists

`#print axioms` on a name you thought of is not a sweep.  This walks the ENVIRONMENT, so it
cannot miss a declaration by failing to guess its name — the failure mode that cost this repo a
night: a grep for `lt_fpDeep` returned clean because the theorem is called `le_fpDeep`.

## The one thing that does NOT work from here, and it is not a bug in this script

**Root attribution is impossible from an importing file.**  For an IMPORTED theorem,
`ConstantInfo.value?` is `none` — proof terms are not available across module boundaries, and
`env.setExporting false` does not restore them.  A dependency test run from here therefore reads
type-level constants only and reports nearly every tainted declaration as a "root".  Two agents
built that classifier independently, both got 234, and both were wrong.  **To attribute a root,
append `#print axioms` to the module's OWN source and analyse it in-module.**

## BEFORE YOU TRUST ANY NUMBER THIS PRINTS: CHECK THE SERVER, NOT ONLY THE HEADER

Run through kimina and the output is only as fresh as the oleans that instance loaded.  Two
checks are needed and **neither substitutes for the other**:

* **canary** — `#check` a name you know is newer than the last build.  This tells you about the
  HEADER YOU SENT, not about the server.  Measured 2026-08-10: a restart silently failed (the old
  process kept the port) and the canary passed anyway, resolving a name minutes old, because the
  header was elaborated fresh against stale oleans.
* **process/mtime** — compare the server process start time against the newest `.olean` mtime.
  This is what caught the failed restart.

A canary alone reports clean for a reason unrelated to the server being current — the same shape
as every other inverted check in this repo's history.  Pair them.

## EXPECTATION — what this printed on 2026-08-10, after `SqV` §25.3

    scanned 3032 | sorryAx 0 | Classical.choice 236

Third baseline.  History, because the round trip is the useful part:

    2972 | 0 | 236   HEAD 485c0b0
    2982 | 0 | 237   HEAD 93f6a30 — `Evidence.Cert.expand_epsEps0` landed with one
                     `Classical.choice`, taken knowingly.  Its `hblk` was closed by
                     `simp [BMS.ent, BMS.delta, BMS.ascends, …]`; `rfl`, an explicit
                     `show` of the reduced block and a fully-listed `simp only` were
                     each tried and each failed, so the `simp` was doing real work.
    2989 | 0 | 236   the choice is GONE.  `hblk` now `change`s to the two entries
                     written out, rewrites each atom by a `show … from rfl`, and
                     leaves `simp only` nothing but arithmetic.
    3757 | 0 | 239   HEAD after `Rows/Selected.lean` — three, and all three are
                     INHERITED, not new.  `Rows.Selected.F1.oLV_zeroLad` and the two
                     that use it (`val_F1`, `e3_of`) go through
                     `Evidence.StageB.oLV_eq` / `oLAux_eq_oLV` / `blocksP_append`,
                     each of which already carried `Classical.choice` before this file
                     existed (measured with `#print axioms` on each).  Nothing in
                     `Selected.lean` itself takes a classical step: its own `omega`s
                     and `decide`s are choice-free, which is why the other ten
                     declarations of the file report `[propext, Quot.sound]`.
                     **Cleaning this means cleaning StageB's fold machinery**, which
                     is a different job from the one that produced the file.
    4234 | 0 | 148   `Rows.ProofsB.blocksP_cons_zero` no longer closes its Bool branch
                     with unrestricted `simp`.  An explicit rewrite of
                     `r0 h == 0` removes `Classical.choice` from that lemma and from
                     the entire StageB chain through `blocksP_append`, `oLV_eq` and
                     `oLAux_eq_oLV`.  The selected-row proofs that inherit this chain
                     now report `[propext, Quot.sound]`.

**The residue certsound flagged as "attackable in isolation" was attackable**, and
what found it was a codex worker taking a wrong turn: told to cite the proved
`expand_epsEps0`, it re-derived the block computation by hand instead, and the
hand version came out choice-free.  Once lifted into `Cert`, its own detour became
unnecessary — the `SqvDecomp` row that motivated it is now five lines.

**A run that differs from this is a CHANGE, not a discovery.**  The baseline is here so no reader
has to re-derive whether a number is good news.  Which way to read a difference:

    sorryAx > 0             a regression — but see the caveat below, which is the ONLY thing
                            that makes it ambiguous
    Classical.choice ↑      something new became classical — find it and decide, do not assume
    Classical.choice ↓      an improvement, OR the namespace filter stopped seeing something
    scanned ↓               declarations vanished from the sweep before you celebrate the rest

**CHECK THE ERROR COUNT BEFORE BELIEVING A `sorryAx`.**  Lean fills a FAILED ELABORATION with
`sorryAx`, so a declaration whose elaboration errored reports `[propext, sorryAx, Quot.sound]`
with no `sorry` anywhere in the file.  Observed: a missing type annotation on a bound function
produced exactly that reading in the same POST as the error.  So `sorryAx > 0` is unambiguous
ONLY on a build with 0 errors — on a broken build it is a false alarm, and it fires on the one
number this repo treats as never-move.  Read the error count first; if it is not 0, the axiom
figures mean nothing at all.

CROSS-CHECKED: a second, independently written implementation scanned 3242 (it filtered
`.isInternal` names differently) and reported **the same 236 hit set**.  Different denominators,
identical hits — which is why the hit set is the number to watch and `scanned` is context.

`Classical.choice` is not unsoundness; this repo is classical in places and that is recorded, not
apologised for.  The standing summary, true as of this baseline:

> the project is `sorryAx`-free everywhere, and classical in places, with at least one classical
> dependency inherited from the Lean standard library.

`sorryAx` at anything other than 0 is a different matter entirely.

### TWO LIMITS, STATED AS LIMITS

* **236 is a FLOOR, not a total.**  Private declarations of IMPORTED modules carry mangled
  `_private.…` names and fail the namespace test below.  The in-module pass over
  `Evidence/Cert.lean` alone found 82 there, because in-module it sees the private ones.
  Do not add a `#guard` on 236: freezing a floor makes a future improvement look like a regression.
* **"Root" bounds project-local causes from ABOVE, not below.**  A declaration with no tainted
  dependency inside the project has *not* necessarily introduced the axiom itself — it may inherit
  from Lean core through a lemma (`String.trimAscii`) or, less obviously, through a TYPECLASS
  INSTANCE.  `Evidence.Cert.parent_lt` is the worked counterexample: `List.max?_mem` is `[propext]`
  and becomes classical the moment it is instantiated at `Nat`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let ours : List Name := [`Evidence, `Rows, `TM, `BMS, `Trans]
  let mut total := 0
  let mut choice : Array Name := #[]
  let mut sorries : Array Name := #[]
  let mut native : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    unless ours.any (fun r => r.isPrefixOf n) do continue
    match ci with
    | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
      total := total + 1
      let ax ← liftCoreM (Lean.collectAxioms n)
      if ax.contains ``sorryAx then sorries := sorries.push n
      if ax.contains ``Classical.choice then choice := choice.push n
      -- `native_decide` does NOT introduce `Lean.ofReduceBool` on this toolchain; it mints a
      -- PER-DECLARATION axiom `<decl>._native.native_decide.ax_N_N`.  So match the name, and
      -- keep the `ofReduce*` constants too for toolchains that do use them.  Verified against
      -- a real `native_decide` theorem — a guard for an axiom name nobody emits is not a guard.
      if ax.any (fun a =>
           let str := a.toString
           (str.splitOn "native_decide").length > 1
             || (str.splitOn "ofReduceBool").length > 1
             || (str.splitOn "ofReduceNat").length > 1) then
        native := native.push n
    | _ => pure ()
  logInfo s!"scanned {total} | sorryAx {sorries.size} | Classical.choice {choice.size} | native {native.size}"
  for s in sorries do logInfo s!"SORRY {s}"
  for c in choice do logInfo s!"CHOICE {c}"
  for m in native do logInfo s!"NATIVE {m}"
