/-
Test/BP2PSS.lean — the Lean half of `scripts/bp2pss` (lean_exe bp2psscli)

The REVERSE of `Test/BPCLI.lean`: takes one Buchholz term on the command line and
prints the Bashicu matrix it is the value of, in the `(0,0)(1,1)` form.

The map is §85.1's `bInv85 : BT → B` (`Evidence/RegionNext3.lean`) followed by
`matB · 0`.  `bInv85` is a genuine inverse on the sub-region, and that is a
THEOREM, not a measurement:

  * `bVal_bInv85` :  `bValA71 (bInv85 b) = b`   for `b` standard of level ≤ 1
  * `bOnto85`     :  every standard `b` of level ≤ 1 whose components are all
                     `D 0` is `bValA71 u` for a standard index `u` — no hypothesis

so the domain this CLI accepts is exactly `bOnto85`'s: `BT.isStd b`, `btLe72 1 b`
and `Hd085 b` (every component of the formal sum is a `D 0`).  Anything else is
exit 2 with the clause that failed, because outside it `bInv85` still computes but
nothing says the answer means anything.

**WHAT IT INVERTS.**  `bValA71`, NOT `Trans`.  §71.2: `bValA71` is `bVal` without
the leading-`(0,0)` exception — "the Buchholz-side reading of `vOf`'s `1 +`" — and
the two differ on exactly the all-`(0,0)` matrices, i.e. the natural numbers.  So
against naruyoko's `TransRev` (which inverts `Trans`) this CLI is one `(0,0)`
column short on a natural-number input and identical everywhere else.
`scripts/bp2pss` states that identity and checks it; see there.

**This is our port, not the reference implementation.**  Like `bpcli` it is the
same instrument as the Lean library and must never be used to validate itself;
`scripts/bp2pss` gets the second opinion from `common.js`'s `TransRev`.

Input: both forms `bpcli` prints.
  * the ψ form,  `p0(p1(0))`, sums `+`-separated, a run of `p0(0)` as a numeral;
  * the `--raw` form, `D_0 D_1 0`, sums `(a,b,c)`.
`psi_0(...)` is accepted as a synonym of `p0(...)` (the notation `bpcli` used
before v0.1.x).  The empty term is `0`, whose matrix is the empty matrix.

Exit codes: 0 printed a matrix, 2 could not (unparseable, or outside `bOnto85`'s
domain).
-/
import Evidence.RegionNext3

open Trans.Dict (BT)
open Evidence.Region

namespace BP2PSS

/-- Drop leading whitespace. -/
def skipWs : List Char → List Char
  | c :: cs => if c.isWhitespace then skipWs cs else c :: cs
  | [] => []

/-- Read a decimal numeral off the front. -/
def readNat (cs : List Char) : Option (Nat × List Char) :=
  let ds := cs.takeWhile Char.isDigit
  if ds.isEmpty then none
  else (String.ofList ds).toNat?.map fun n => (n, cs.dropWhile Char.isDigit)

/-! The parser.  `pTerm` is a `+`-separated list of atoms; an atom is `0`, a
    numeral, `pu(<term>)` / `psi_u(<term>)`, `D_u <atom>`, or a raw parenthesised
    sum `(<term>,<term>,...)`.  `partial` as in `Test/ORCLI.lean`'s `showT`: the
    CLI is a reader, not a proof. -/

mutual

partial def pTerm (cs : List Char) : Option (BT × List Char) := do
  let (a, r) ← pAtom cs
  match skipWs r with
  | '+' :: r' => do
      let (b, r'') ← pTerm r'
      pure (BT.add a b, r'')
  | r' => pure (a, r')

partial def pSeq (cs : List Char) (acc : List BT) : Option (List BT × List Char) := do
  let (a, r) ← pTerm cs
  match skipWs r with
  | ',' :: r' => pSeq r' (acc ++ a.toL)
  | ')' :: r' => pure (acc ++ a.toL, r')
  | _ => none

partial def pAtom (cs0 : List Char) : Option (BT × List Char) :=
  match skipWs cs0 with
  | [] => none
  | '(' :: r => do
      let (l, r') ← pSeq r []
      pure (BT.ofL l, r')
  | c :: r =>
    if c == 'p' || c == 'ψ' then
      -- ψ form: the argument is always parenthesised.
      let r := if c == 'p' && r.take 2 == ['s', 'i'] then r.drop 2 else r
      let r := match r with | '_' :: r' => r' | r' => r'
      match readNat r with
      | none => none
      | some (u, r1) =>
        match skipWs r1 with
        | '(' :: r2 => do
            let (a, r3) ← pTerm r2
            match skipWs r3 with
            | ')' :: r4 => pure (BT.D u a, r4)
            | _ => none
        | _ => none
    else if c == 'D' then
      -- raw form: the argument is the next atom, unparenthesised.
      let r := match r with | '_' :: r' => r' | r' => r'
      match readNat r with
      | none => none
      | some (u, r1) => do
          let (a, r2) ← pAtom r1
          pure (BT.D u a, r2)
    else if c.isDigit then
      match readNat (c :: r) with
      | none => none
      | some (n, r1) => pure (BT.ofNat n, r1)
    else none

end

/-- `Hd085` as a `Bool`: every component of the formal sum has head `D 0`. -/
def hd0B (b : BT) : Bool :=
  b.toL.all fun x => match x with | .D 0 _ => true | _ => false

def parse (s : String) : Option BT :=
  match pTerm s.toList with
  | some (b, r) => if (skipWs r).isEmpty then some b else none
  | none => none

def usage : String :=
  "usage: bp2psscli <buchholz term>   |   bp2psscli --batch\n\
   \n\
   Prints the Bashicu matrix whose value the term is: §85's bInv85, then matB.\n\
   Accepts both forms bpcli prints -- p0(p1(0)) and D_0 D_1 0.\n\
   \n\
   The domain is bOnto85's: standard, level <= 1, every component a D 0\n\
   (equivalently, below Omega = p1(0)).  Outside it, exit 2.\n\
   \n\
   --batch answers every line with `= <matrix>` or `! <why it is out of domain>`\n\
   and always exits 0.  It exists because this executable imports the whole of\n\
   Evidence and so costs about two seconds to START; scripts/bp2pss-check.sh runs\n\
   a hundred terms through one process instead of a hundred processes."

/-- The answer, or the clause of `bOnto85`'s domain that failed. -/
def answer (s : String) : Except String String :=
  match parse s with
  | none => .error s!"cannot parse the Buchholz term: {s}"
  | some b =>
    if !BT.isStd b then
      .error "the term is not standard (isStandardBuchholz is false), so it is \
        outside bOnto85's domain"
    else if !btLe72 1 b then
      .error "the term carries a node of level 2 or more, so it is outside the \
        level-one sub-region (btLe72 1 is false).  §85 spends the level bound twice \
        and one level up the clause it serves is refuted (§85.6)"
    else if !hd0B b then
      .error "a component of the term is not a D 0, i.e. the term is not below \
        Omega = p1(0), so it is outside bOnto85's domain.  Omega itself is standard \
        and of level 1 and is the value of NO index (not_bValA71_om85)"
    else
      .ok (BMS.showMatrix (matB (bInv85 b) 0))

def run (s : String) : IO UInt32 := do
  match answer s with
  | .error e => IO.eprintln s!"bp2psscli: {e}"; pure 2
  | .ok m => IO.println m; pure 0

partial def batchLoop (h : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then pure ()        -- EOF
  else
    let s := line.trimAscii.toString
    match answer s with
    | .error e => IO.println s!"! {e}"
    | .ok m => IO.println s!"= {m}"
    batchLoop h

def batch : IO UInt32 := do
  batchLoop (← IO.getStdin)
  pure 0

end BP2PSS

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--batch"] => BP2PSS.batch
  | [s] => BP2PSS.run s
  | _ =>
    IO.eprintln BP2PSS.usage
    pure 2
