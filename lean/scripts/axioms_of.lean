/-
`lean/scripts/axioms_of.lean` — AXIOMS OF EVERY DECLARATION IN ONE FILE

Frozen because the throwaway version of this had a bug that cost a whole
measurement, twice over.  It parsed the TEXT of `#print axioms`, and
`#print axioms` has TWO output shapes:

    'X' depends on axioms: [propext, Quot.sound]
    'X' does not depend on any axioms

The parser matched only the first, so the CLEANEST declarations — the ones with
no axioms at all — were counted as "could not measure".  17 of 108 in one run.
An instrument that discards its best results as unmeasured (constitution C8).

The fix is not a better regex.  **Do not read the text at all.**
`Lean.collectAxioms` returns an array; "no axioms" is the empty array, not a
different sentence, so the second shape cannot be missed.  This is what
`axiom_sweep.lean` already did, and it is why the sweep was the only one of five
instruments that behaved tonight.

USE.  Copy the declarations to measure into a file that imports the project,
then append

    #eval axiomsOf `Evidence.Cert  -- or any namespace prefix

or call `axiomsReport` with an explicit list.  Output is one line per
declaration plus a summary, with `native`/`sorryAx`/`Classical.choice` counted
separately because those are the three that must never move.

SELF-TEST at the bottom, per constitution C0: the instrument is handed one
declaration of each kind it must distinguish — axiom-free, propext-only,
Classical.choice, native_decide, sorryAx — and must classify all five.  If the
report shapes ever change, this file fails rather than silently miscounting.
-/
import Lean.Elab.Command

open Lean Elab Command

/-- The axioms a declaration depends on, as data.  No text is parsed. -/
def axiomsOfName (n : Name) : CommandElabM (Array Name) := do
  liftCoreM (do
    let ax ← Lean.collectAxioms n
    return ax)

/-- `native_decide` mints a PER-DECLARATION axiom on this toolchain
    (`<decl>._native.native_decide.ax_N_N`), not `Lean.ofReduceBool`, so match the
    NAME.  A guard watching for a constant nobody emits is not a guard. -/
def isNativeAxiom (a : Name) : Bool :=
  let s := a.toString
  (s.splitOn "native_decide").length > 1
    || (s.splitOn "ofReduceBool").length > 1
    || (s.splitOn "ofReduceNat").length > 1

/-- The counts, as data, so the self-test can exercise the COUNTING path.
    The first version of this file tested `axiomsOfName` and the predicates only;
    the bug it was written to prevent lived in the tally, which the test never
    called, and a deliberately broken tally still reported "self-test passed".
    Testing the wrong layer is not testing (constitution C0). -/
structure AxCounts where
  total : Nat
  free : Nat
  sorries : Array Name
  choice : Array Name
  native : Array Name

def axiomsCount (pre : Name) : CommandElabM AxCounts := do
  let env ← getEnv
  let mut total := 0
  let mut free := 0
  let mut choice : Array Name := #[]
  let mut sorries : Array Name := #[]
  let mut native : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    unless pre.isPrefixOf n do continue
    match ci with
    | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
      total := total + 1
      let ax ← axiomsOfName n
      if ax.isEmpty then free := free + 1
      if ax.contains ``sorryAx then sorries := sorries.push n
      if ax.contains ``Classical.choice then choice := choice.push n
      if ax.any isNativeAxiom then native := native.push n
    | _ => pure ()
  return { total, free, sorries, choice, native }

/-- Report every declaration under `prefix` that is a theorem or definition. -/
def axiomsReportOld (pre : Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut total := 0
  let mut free := 0
  let mut choice : Array Name := #[]
  let mut sorries : Array Name := #[]
  let mut native : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    unless pre.isPrefixOf n do continue
    match ci with
    | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
      total := total + 1
      let ax ← axiomsOfName n
      if ax.isEmpty then free := free + 1
      if ax.contains ``sorryAx then sorries := sorries.push n
      if ax.contains ``Classical.choice then choice := choice.push n
      if ax.any isNativeAxiom then native := native.push n
    | _ => pure ()
  -- `free` is REPORTED, never silently folded into "unmeasured"
  logInfo s!"scanned {total} | axiom-free {free} | sorryAx {sorries.size} | \
Classical.choice {choice.size} | native {native.size}"
  for x in sorries do logInfo s!"SORRY {x}"
  for x in choice do logInfo s!"CHOICE {x}"
  for x in native do logInfo s!"NATIVE {x}"

def axiomsReport (pre : Name) : CommandElabM Unit := do
  let c ← axiomsCount pre
  logInfo s!"scanned {c.total} | axiom-free {c.free} | sorryAx {c.sorries.size} | \
Classical.choice {c.choice.size} | native {c.native.size}"
  for x in c.sorries do logInfo s!"SORRY {x}"
  for x in c.choice do logInfo s!"CHOICE {x}"
  for x in c.native do logInfo s!"NATIVE {x}"

namespace AxiomsOfSelfTest

theorem t_free : True := trivial
theorem t_propext (p q : Prop) (h : p ↔ q) : p = q := propext h
theorem t_choice : ∀ p : Prop, p ∨ ¬p := fun p => Classical.em p
theorem t_native : (List.range 4).all (fun n => n < 4) = true := by native_decide

-- POSITIVE CONTROL FOR THE sorryAx COUNTER.  This `sorry` is deliberate and must
-- stay.  Without it the self-test cannot tell "correctly counted 0 sorries" from
-- "the counter is broken" — verified: deleting the counter's `push` left the test
-- passing until this theorem existed (constitution C4: a check that only ever sees
-- negatives is indistinguishable from a check that always returns false).
-- It lives in `AxiomsOfSelfTest`, which is NOT among the namespaces
-- `axiom_sweep.lean` scans (`Evidence`, `Rows`, `TM`, `BMS`, `Trans`), and this file
-- is not imported by the library, so the project's `sorryAx 0` is unaffected.
theorem t_sorry : False := sorry

end AxiomsOfSelfTest

-- C0: hand the instrument one instance of each kind it must tell apart, and
-- check it tells them apart.  An instrument nobody has fired is not evidence.
-- (A doc comment cannot attach to `run_cmd`; this is the second time tonight.)
run_cmd do
  let expect : List (Name × Bool × Bool × Bool) :=
    -- name, axiom-free?, has choice?, is native?
    [(`AxiomsOfSelfTest.t_free,    true,  false, false),
     (`AxiomsOfSelfTest.t_propext, false, false, false),
     (`AxiomsOfSelfTest.t_choice,  false, true,  false),
     (`AxiomsOfSelfTest.t_native,  false, false, true)]
  let mut bad := 0
  for (n, wFree, wChoice, wNative) in expect do
    let ax ← axiomsOfName n
    let gFree := ax.isEmpty
    let gChoice := ax.contains ``Classical.choice
    let gNative := ax.any isNativeAxiom
    if gFree != wFree || gChoice != wChoice || gNative != wNative then
      bad := bad + 1
      logError s!"SELF-TEST FAILED for {n}: free={gFree} choice={gChoice} native={gNative}"
  -- and now the COUNTING path, over a namespace whose composition is known
  let c ← axiomsCount `AxiomsOfSelfTest
  if c.total != 5 then
    bad := bad + 1; logError s!"SELF-TEST: total {c.total}, want 5"
  if c.free != 1 then
    bad := bad + 1; logError s!"SELF-TEST: axiom-free {c.free}, want 1 (t_free)"
  if c.choice.size != 1 then
    bad := bad + 1; logError s!"SELF-TEST: choice {c.choice.size}, want 1 (t_choice)"
  if c.native.size != 1 then
    bad := bad + 1; logError s!"SELF-TEST: native {c.native.size}, want 1 (t_native)"
  if c.sorries.size != 1 then
    bad := bad + 1; logError s!"SELF-TEST: sorryAx {c.sorries.size}, want 1 (t_sorry)"
  if bad == 0 then
    logInfo "axioms_of self-test: 4 classifications + 5 tallies correct (incl. sorry control)"
