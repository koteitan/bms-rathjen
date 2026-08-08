/-
Test/CLI.lean — the CLI used to cross-check against yaBMS (lean_exe bmscli)

Reads one command per line from standard input:
  expand <matrix> <n>   → the expansion in "(0,0)(1,0)" form ("undefined" if none)
  cmp <m0> <m1>         → 1 / 0 / -1  (m0 > m1 / == / <), as in yaBMS -c
The empty matrix is written "".  One response line per input line.
-/
import BMS

open BMS

def runLine (line : String) : String :=
  let ws := ((trimS line).splitOn " ").filter (· ≠ "")
  match ws with
  | ["expand", ms, ns] =>
    match parseMatrix ms, ns.toNat? with
    | some M, some n =>
      match expand? M n with
      | some R => showMatrix R
      | none => "undefined"
    | _, _ => "parse-error"
  | ["expand", ns] =>
    -- expansion of the empty matrix, given as "expand <n>"
    match ns.toNat? with
    | some _ => "undefined"
    | none => "parse-error"
  | ["cmp", m0, m1] =>
    match parseMatrix m0, parseMatrix m1 with
    | some a, some b =>
      match cmpM a b with
      | .gt => "1"
      | .eq => "0"
      | .lt => "-1"
    | _, _ => "parse-error"
  | [] => ""
  | _ => "parse-error"

partial def loop (h : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then
    pure ()  -- EOF
  else
    -- exactly one output line per input line (an empty matrix prints an empty line)
    IO.println (runLine line)
    loop h

def main : IO Unit := do
  loop (← IO.getStdin)
