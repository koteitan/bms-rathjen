/-
Test/TransTest.lean — checks of the translation o (Stage A: the one-row region)

- E1: direct checks of representative values
- checkAll: over a whole corpus — preservation of the classification, matching of
  predecessors, E2 (order embedding) and E3 in mutual-cofinality form
- strict bisim: in the CNF region the BMS expansions and the fundamental sequences
  agree (up to the index shift of one)
- a record of the fact that at ε₁ the two become different cofinal sequences for
  the same value
-/
import Evidence.Check
import Evidence.Bisim

namespace Trans.Test
open BMS TM.Term Trans Evidence

-- E1: representative values in the one-row region
#guard oPr [[0]] = one
#guard oPr [[0],[1]] = omega
#guard oPr [[0],[1],[0],[1]] = add omega omega          -- ω·2
#guard oPr [[0],[1],[1]] = phi zero (ofNat 2)           -- ω²
#guard oPr [[0],[1],[2]] = phi zero omega               -- ω^ω
#guard oPr [[0],[1],[2],[3]] = phi zero (phi zero omega) -- ω^ω^ω
#guard oPr [[0,0],[1,0],[2,0]] = phi zero omega         -- the same for a 2-row matrix whose row 1 is zero

-- exhaustive corpus checks (one row: depth 4, width 3 / two rows with row 1
-- zero: depth 3, width 3)
def c1 : List Matrix := corpus [[0],[1],[2]] 4 3
def c2 : List Matrix := corpus [[0,0],[1,0],[2,0]] 3 3
#guard c1.length ≥ 40
#guard checkAll oPr c1 3 6
#guard checkAll oPr c2 3 6

-- strict bisim: in the CNF region and at ε₀ the expansions match the fs
#guard bisim 5 [[0,0],[1,0]] omega 3
#guard bisim 5 [[0,0],[1,1]] (phi one zero) 3
-- they differ at ε₁ (BMS climbs an ε₀-tower, the fs an ω-tower; same value):
#guard !(bisim 3 [[0,0],[1,1],[1,1]] (phi one one) 3)

end Trans.Test
