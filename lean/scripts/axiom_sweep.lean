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

## Counts as of 2026-08-10 (HEAD ≈ de08b52 + WF 5b76d6d259ea04a9)

    declarations scanned (Evidence/Rows/TM/BMS/Trans)   2972
    carrying sorryAx                                       0     ← the one that must stay 0
    carrying Classical.choice                            236
    Evidence.WF                                            0
    TM                                                     0

`Classical.choice` is not unsoundness; this repo is classical in places and that is recorded, not
apologised for.  `sorryAx` at anything other than 0 is a different matter entirely.

CAVEAT ON 236: private declarations of IMPORTED modules carry mangled `_private.…` names and are
filtered out by the namespace test below, so 236 is a FLOOR.  The in-module pass over
`Evidence/Cert.lean` alone found 82 where this script attributes fewer, precisely because it sees
the private ones.
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
