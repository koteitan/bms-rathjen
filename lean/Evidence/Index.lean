import BMS
import Trans.Dict
/-
Evidence/Index.lean — the generalised index and its Buchholz inverse, as DEFINITIONS

Split out of `Evidence/RegionNext*.lean` so that a tool needing only to COMPUTE with
them does not have to import the whole of `Evidence`.  `lean_exe bp2psscli` did, and
paid 2.2 s of start-up for 176 MB of oleans; from here it pays milliseconds.

Nothing is stated here — every theorem about these definitions stays where it was
proved, and the names are unchanged:

    B, matB       §1 of Evidence/RegionNext.lean
    btLe72        §72 of Evidence/RegionNext2.lean
    bInvA85 …     §85.1 of Evidence/RegionNext3.lean

so this file is a move, not a redesign.  The imports are the point: `BMS` for
`Matrix` and `Trans.Dict` for `BT`, and nothing else.
-/

namespace Evidence.Region

open BMS

/-! ## The generalised index (§1) -/

/-- `nd v r a` = `r ⊕ ψ_v(a)`.  `Region.A` is the case `v ∈ {0,1}` with `ψ₁`'s argument
    forced to `0`. -/
inductive B where
  | nil : B
  | nd  : Nat → B → B → B
deriving DecidableEq, Inhabited

def matB : B → Nat → Matrix
  | .nil, _ => []
  | .nd v r a, d => matB r d ++ ([d, v] :: matB a (d + 1))

/-! ## The level bound on the Buchholz side (§72) -/

section
open Trans.Dict (BT)

/-- `BT` の側の添字の上限。 -/
def btLe72 (m : Nat) : BT → Bool
  | .zero => true
  | .D u a => decide (u ≤ m) && btLe72 m a
  | .sum a b => btLe72 m a && btLe72 m b

/-! ## The inverse of `bValA71` (§85.1) -/

/-- 段 1 以下では `bArg` の潰す枝が死んでいる (§71.6) ので、成分 `D u a` は
    「段 `u` の節、引数は `a` の逆像」にそのまま戻る。和は節を横に並べたものになる。 -/
def bInvA85 : B → BT → B
  | acc, .zero => acc
  | acc, .D u a => .nd u acc (bInvA85 .nil a)
  | acc, .sum x y => bInvA85 (bInvA85 acc x) y

def bInv85 (b : BT) : B := bInvA85 .nil b

end

end Evidence.Region
