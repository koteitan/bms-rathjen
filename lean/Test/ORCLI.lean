/-
Test/ORCLI.lean — the Lean half of `scripts/or` (lean_exe orcli)

Takes one Bashicu matrix in the `(0,0)(1,1)` form on the command line (the empty
string is the empty matrix) and prints `Trans.oR`'s 𝔗(M) term on one line.

It does NOT decide standard form: `BMS/Standard.lean` defines standardness as
reachability from the initial matrix and checks it from an explicit witness, so
there is no decision procedure here.  `scripts/or` asks the reference
implementation (yaBMS `bms -s`) instead, which is what `scripts/standard-audit.sh`
already does — a second, unvalidated standardness algorithm is exactly the kind of
instrument this repository does not trust.

Exit codes: 0 printed a term, 2 could not (unparseable, or outside `oR`'s domain —
`oR` is the 2-row fragment, `none` on any column of height 3 or more).
-/
import Trans.Recal

open TM TM.Term

/-- A term all of whose components are `1` is that many. -/
def natOf? (t : Term) : Option Nat :=
  let l := toList t
  if l.all (· == one) then some l.length else none

/-- 𝔗(M) term → plain ASCII.  The naming is `Rows/TM.lean`'s `tex` without the
    MathJax: finite terms collapse to a numeral, `φ̄(0,1)` prints as `w`, and `Z 0`
    as `Omega`. -/
partial def showT (t : Term) : String :=
  match natOf? t with
  | some n => toString n
  | none =>
    match t with
    | .zero => "0"
    | .M => "M"
    | .add a b => showT a ++ "+" ++ showT b
    | .omg a => "w^(" ++ showT a ++ ")"
    | .phi a b => if t == omega then "w" else "phi(" ++ showT a ++ "," ++ showT b ++ ")"
    | .psi k a => "psi_(" ++ showT k ++ ")(" ++ showT a ++ ")"
    | .Z a => if a == Term.zero then "Omega" else "Z(" ++ showT a ++ ")"

def main (args : List String) : IO UInt32 := do
  match args with
  | [s] =>
    match BMS.parseMatrix s with
    | none =>
      IO.eprintln s!"orcli: cannot parse the matrix: {s}"
      pure 2
    | some m =>
      match Trans.oR m with
      | none =>
        IO.eprintln "orcli: outside oR's domain (a column of height 3 or more)"
        pure 2
      | some t =>
        IO.println (showT t)
        pure 0
  | _ =>
    IO.eprintln "usage: orcli <matrix>"
    pure 2
