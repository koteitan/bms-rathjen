/- gentable: generates table/table-r1.md from the row database (to standard output).

   Each table row links to the line of Rows/TM.lean that defines it.  The line
   numbers are resolved here, by reading that file, so that they cannot drift out
   of date: CI regenerates the table and diffs it against the committed one. -/
import Rows.TM

/-- Is `needle` a substring of `s`? -/
def hasSub (s needle : String) : Bool := (s.splitOn needle).length > 1

/-- The path of Rows/TM.lean, whether the exe is run from `lean/` or from the repo root. -/
def sourcePath : IO String := do
  for p in ["Rows/TM.lean", "lean/Rows/TM.lean"] do
    if ← System.FilePath.pathExists p then return p
  throw (IO.userError "Rows/TM.lean not found (run from lean/ or from the repo root)")

/-- 1-based line number of the first line of `path` containing `key`.
    A missing file resolves nothing (used for not-yet-integrated proof files). -/
def lineFinder (path : String) : IO (String → Option Nat) := do
  if !(← System.FilePath.pathExists path) then
    return fun _ => none
  let lines := (← IO.FS.readFile path).splitOn "\n"
  return fun key => (lines.findIdx? (hasSub · key)).map (· + 1)

def main : IO Unit := do
  let dir := ((← sourcePath).dropEnd "Rows/TM.lean".length).toString
  let rowLine ← lineFinder (dir ++ "Rows/TM.lean")
  -- per-row proofs may live in either proof file; the first hit wins
  let proofFiles := ["Rows/Proofs.lean", "Rows/ProofsB.lean"]
  let finders ← proofFiles.mapM fun f => do pure (f, ← lineFinder (dir ++ f))
  let proofLine (key : String) : Option (String × Nat) :=
    finders.firstM fun (f, find) => (find key).map (f, ·)
  -- region proofs live in the file each region row names
  let regionFiles := (Rows.regions.map (·.proofFile)).eraseDups
  let rfinders ← regionFiles.mapM fun f => do pure (f, ← lineFinder (dir ++ f))
  let regionProofLine (file key : String) : Option Nat :=
    (rfinders.lookup file).bind (· key)
  IO.print (Rows.genTable rowLine proofLine regionProofLine)
