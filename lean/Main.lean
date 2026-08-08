/- gentable: generates table/r1-tm.md from the row database (to standard output) -/
import Rows.TM

def main : IO Unit := IO.print Rows.genTable
