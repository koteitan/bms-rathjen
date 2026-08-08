/- gentable: 行 DB から table/r1-tm.md を生成する (標準出力へ) -/
import Rows.TM

def main : IO Unit := IO.print Rows.genTable
