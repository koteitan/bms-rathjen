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

## EXPECTATION — what this printed on 2026-08-10, at HEAD 485c0b0

    scanned 2972 | sorryAx 0 | Classical.choice 236

**A run that differs from this is a CHANGE, not a discovery.**  The baseline is here so no reader
has to re-derive whether a number is good news.  Which way to read a difference:

    sorryAx > 0             a regression, and the only one of the three that is unambiguous
    Classical.choice ↑      something new became classical — find it and decide, do not assume
    Classical.choice ↓      an improvement, OR the namespace filter stopped seeing something
    scanned ↓               declarations vanished from the sweep before you celebrate the rest

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
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    unless ours.any (fun r => r.isPrefixOf n) do continue
    match ci with
    | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
      total := total + 1
      let ax ← liftCoreM (Lean.collectAxioms n)
      if ax.contains ``sorryAx then sorries := sorries.push n
      if ax.contains ``Classical.choice then choice := choice.push n
    | _ => pure ()
  logInfo s!"scanned {total} | sorryAx {sorries.size} | Classical.choice {choice.size}"
  for s in sorries do logInfo s!"SORRY {s}"
  for c in choice do logInfo s!"CHOICE {c}"
