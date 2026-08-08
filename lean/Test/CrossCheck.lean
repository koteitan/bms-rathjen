/-
Test/CrossCheck.lean — smoke tests of expansion and comparison

The expected values are taken from the output of yaBMS (the C implementation):
  (0,0)(1,1)[2]               → (0,0)(1,0)(2,0)
  (0,0)(1,1)[3]               → (0,0)(1,0)(2,0)(3,0)
  (0,0,0)(1,1,1)[2]           → (0,0,0)(1,1,0)(2,2,0)
  (0,0,0)(1,1,1)(2,1,0)(1,1,1)[2]
    → (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,2,0)(2,2,0)(3,3,1)(4,3,0)
-/
import BMS

namespace BMS.Test

-- expansion
#guard expand? [[0,0],[1,1]] 2 = some [[0,0],[1,0],[2,0]]
#guard expand? [[0,0],[1,1]] 3 = some [[0,0],[1,0],[2,0],[3,0]]
#guard expand? [[0,0,0],[1,1,1]] 2 = some [[0,0,0],[1,1,0],[2,2,0]]
#guard expand? [[0,0,0],[1,1,1],[2,1,0],[1,1,1]] 2 =
  some [[0,0,0],[1,1,1],[2,1,0],[1,1,0],[2,2,1],[3,2,0],[2,2,0],[3,3,1],[4,3,0]]

-- (0,0)(1,0) is a limit with only row 0 nonzero (like (0)(1) = ω): copies of the zero column
#guard expand? [[0,0],[1,0]] 3 = some [[0,0],[0,0],[0,0],[0,0]]

-- successor (last column all zero → drop it)
#guard expand? [[0,0],[1,1],[0,0]] 5 = some [[0,0],[1,1]]
#guard expand? [[0,0]] 0 = some []

-- the empty matrix has no expansion
#guard expand? ([] : Matrix) 1 = none

-- classification
#guard kind ([] : Matrix) = .zero
#guard kind [[0,0],[1,1],[0,0]] = .succ
#guard kind [[0,0],[1,0]] = .lim
#guard kind [[0,0],[1,1]] = .lim

-- comparison (lexicographic)
#guard cmpM [[0,0],[1,1],[2,0]] [[0,0],[1,1],[1,1]] = .gt
#guard cmpM [[0,0]] [[0,0],[1,0]] = .lt
#guard cmpM [[0,0],[1,1]] [[0,0],[1,1]] = .eq

-- expansion makes the matrix smaller (a concrete instance)
#guard cmpM (expand [[0,0],[1,1]] 3) [[0,0],[1,1]] = .lt

-- printing and parsing
#guard showMatrix [[0,0,0],[1,1,1]] = "(0,0,0)(1,1,1)"
#guard parseMatrix "(0,0,0)(1,1,1)" = some [[0,0,0],[1,1,1]]
#guard parseMatrix "" = some []

-- example of checking standardness by a witness:
--   (0,0)(1,1) --[2]--> (0,0)(1,0)(2,0), so the latter is standard
#guard reachBy (init 2) [2] = some [[0,0],[1,0],[2,0]]

example : Standard 2 [[0,0],[1,0],[2,0]] :=
  reachBy_sound (M := init 2) (path := [2]) (by decide)

end BMS.Test
