/-
Test/BPCLI.lean — the Lean half of `scripts/pss2bp` (lean_exe bpcli)

Takes one Bashicu matrix in the `(0,0)(1,1)` form on the command line (the empty
string is the empty matrix) and prints its BUCHHOLZ term — `Trans.Recal.oRB`,
which is `transPort ∘ ofMatrix`, the port of naruyoko's `common.js`.

**This is our port, not the reference implementation.**  `Trans/Recal.lean` §5
pins `oRB` against verbatim `pss2bp --raw` output, and that comparison is only
worth anything because the reference is a SECOND instrument.  This CLI is the
same instrument as the Lean library: it is a convenience for reading values, and
it must never be used to validate the port.  That is the v0.1.41 calibration
accident (see `plan/constitutions.md`) in one sentence.

`scripts/or` is the sibling that prints the 𝔗(M) side, i.e. `dict` of this.

Exit codes: 0 printed a term, 2 could not (unparseable, or outside `oRB`'s domain
— it is the 2-row fragment, `none` on any column of height 3 or more).
-/
import Trans.Recal

open Trans.Dict (BT)

/-- `stringifyBuchholz(t, false)` of `common.js`, so the output can be compared by
    eye with `node pss2bp.js --raw`.  Same function as `Trans.Recal.Test.showRaw`;
    repeated here because that one is inside the acceptance record's namespace. -/
def showRawF : Nat → BT → String
  | 0, _ => "?"
  | f + 1, t =>
    match t with
    | .zero => "0"
    | .D u a => "D_" ++ toString u ++ " " ++ showRawF f a
    | .sum _ _ => "(" ++ String.intercalate "," (t.toL.map (showRawF f)) ++ ")"

/-- The ψ notation: `D u a` is `ψ_u(a)`, written `pu(a)` — the subscript juxtaposed,
    no underscore — and a formal sum is `+`-separated.
    A run of `ψ_0(0)` collapses to a numeral, since `ψ_0(0) = 1`. -/
def showPsiF : Nat → BT → String
  | 0, _ => "?"
  | f + 1, t =>
    match t with
    | .zero => "0"
    | .D u a => "p" ++ toString u ++ "(" ++ showPsiF f a ++ ")"
    | .sum _ _ =>
      let l := t.toL
      if l.all (· == BT.D 0 BT.zero) then toString l.length
      else String.intercalate "+" (l.map (showPsiF f))

def showRaw (t : BT) : String := showRawF (BT.size t + 2) t
def showPsi (t : BT) : String := showPsiF (BT.size t + 2) t

def usage : String :=
  "usage: bpcli [--raw] <matrix>\n\
   \n\
   Prints the Buchholz term of the matrix.  Default is psi notation, p0(p1(0));\n\
   --raw is common.js's stringifyBuchholz form (D_u a, sums parenthesised and\n\
   comma-separated)."

def run (raw : Bool) (s : String) : IO UInt32 := do
  match BMS.parseMatrix s with
  | none =>
    IO.eprintln s!"bpcli: cannot parse the matrix: {s}"
    pure 2
  | some m =>
    match Trans.Recal.oRB m with
    | none =>
      if m.isEmpty then
        IO.eprintln "bpcli: the empty matrix is outside oRB's domain (a PSS pair \
          sequence is never empty; `scripts/or` reads it as 0 by this repository's \
          own convention, which oRB does not share)"
      else
        IO.eprintln "bpcli: outside oRB's domain (a column of height 3 or more)"
      pure 2
    | some t =>
      IO.println (if raw then showRaw t else showPsi t)
      pure 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--raw", s] => run true s
  | [s, "--raw"] => run true s
  | [s] => run false s
  | _ =>
    IO.eprintln usage
    pure 2
