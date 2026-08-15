import Evidence.Region
import Rows.TM
/-
Evidence/RegionNext.lean — WHICH ROWS ARE HEAVY, MEASURED

`Evidence/Region.lean` names the region below ε_ω and proves it closed under `BMS.expand`.
The natural next question is which of the shortlist's remaining rows that region reaches,
and how much further the others are.  This file measures it before anything is built —
`Evidence/Cert.lean` §22's discipline.

THE ANSWER IS NOT PER ROW.  Over the shortlist's width-two rows the expansion closure to
depth three has between 13 and 40 matrices, and the range does not track the tier: Γ₀ is
40, ε_ω is 28, and ε₀ — already registered — is 13.  Closure size does not separate them.  What separates them is the row-1 maximum, and that is
an INVARIANT of the closure: `lnz` of a width-two column is `0` or `1`, so `delta` never
touches row 1, and no expansion raises it.  The shortlist splits

    3   already registered                                    ω, ε₀, ω^(ε₀+1)
    1   reached by `Region.A`                                 ε_ω   (and ε₁, off the list)
   13   row-1 max 1, but ψ₁ carries an ARGUMENT               ζ₀ … Γ₀, the six disputed
    6   row-1 max 2                                           the ψ₀(Ω₂) block

AND THE THREE TIERS ARE ONE GENERALISATION, NOT THREE.  `Region.A` has two constructors,
`om r` for `r ⊕ Ω` and `ps r a` for `r ⊕ ψ₀(a)`; `Ω = ψ₁(0)` carries no argument, which is
exactly what caps the region at `ξ < Ω·ω`.  Merging them into one constructor with the
level as a `Nat` —

    nd v r a   =   r ⊕ ψ_v(a)

— gives an index that decodes **every width-two row of the table (52 of them) and every
matrix of their depth-three closures**, with 0 failures.  So one further generalisation
covers all twenty remaining shortlisted rows, and `Region.A` embeds in it (`embed_mat`).

WHY THAT IS NOT A LICENCE TO SKIP AHEAD.  The decoding is a measurement about SHAPE; the
expansion identity, the normal form and the limit clauses are what a certificate needs, and
none of them is measured here.  What the measurement does settle is the SHAPE OF THE NEXT
DESIGN: not three regions but one, and not a new recursion but one constructor.
-/

namespace Evidence.Region

open BMS

/-! ## §1 The generalised index -/

/-- `nd v r a` = `r ⊕ ψ_v(a)`.  `Region.A` is the case `v ∈ {0,1}` with `ψ₁`'s argument
    forced to `0`. -/
inductive B where
  | nil : B
  | nd  : Nat → B → B → B
deriving DecidableEq, Inhabited

def matB : B → Nat → Matrix
  | .nil, _ => []
  | .nd v r a, d => matB r d ++ ([d, v] :: matB a (d + 1))

/-- `Region.A` の埋め込み。 -/
def embed : A → B
  | .nil => .nil
  | .om r => .nd 1 (embed r) .nil
  | .ps r a => .nd 0 (embed r) (embed a)

/-- **埋め込みは行列を変えない。** いまの領域は新しい添字の真部分である。 -/
theorem embed_mat : ∀ (t : A) (d : Nat), matB (embed t) d = mat t d := by
  intro t
  induction t with
  | nil => intro d; rfl
  | om r ih =>
    intro d
    show matB (embed r) d ++ ([d, 1] :: matB .nil (d + 1)) = mat r d ++ [[d, 1]]
    rw [ih d]
    rfl
  | ps r a ihr iha =>
    intro d
    show matB (embed r) d ++ ([d, 0] :: matB (embed a) (d + 1))
      = mat r d ++ ([d, 0] :: mat a (d + 1))
    rw [ihr d, iha (d + 1)]

/-! ## §2 The measurement -/

partial def decB (d : Nat) (acc : B) : Matrix → B × Matrix
  | [] => (acc, [])
  | c :: rest =>
    if c.getD 0 0 != d then (acc, c :: rest)
    else
      let (a, tl) := decB (d + 1) .nil rest
      decB d (.nd (c.getD 1 0) acc a) tl

def decodeB (S : Matrix) : Option B :=
  let (a, tl) := decB 0 .nil S
  if tl.isEmpty && matB a 0 == S then some a else none

/-- 列の高さの最大。 -/
def widthOf (S : Matrix) : Nat := (S.map (fun c => c.length)).foldl max 0

/-- 行 1 の最大成分 = `ψ` の段。 -/
def lvlOf (S : Matrix) : Nat := (S.map (fun c => c.getD 1 0)).foldl max 0

/-- 展開の閉包 (深さ `d`、`n < N`)。 -/
def cloOf (M : Matrix) (N d : Nat) : List Matrix :=
  Nat.rec [M] (fun _ (acc : List Matrix) =>
    (acc ++ acc.flatMap (fun x => (List.range N).map (BMS.expand x))).eraseDups) d

/-- 表の幅 2 の行。 -/
def wideRows : List BMS.Matrix :=
  (Rows.rows.filter (fun r : Rows.Row => widthOf r.m == 2)).map (fun r : Rows.Row => r.m)

-- 表の幅は 0 (空行列)、1、2 しかない。
#guard ((Rows.rows.map fun r : Rows.Row => widthOf r.m).eraseDups.all
  (fun w => w == 0 || w == 1 || w == 2))
#guard wideRows.length == 52
-- 幅 2 の行はすべて一般化添字で書ける。
#guard wideRows.all fun M => (decodeB M).isSome
-- その深さ 3 の閉包もすべて書ける。
#guard wideRows.all fun M => (cloOf M 3 3).all fun S => S.isEmpty || (decodeB S).isSome
-- 段は閉包の不変量 — 展開は行 1 を上げない。
#guard wideRows.all fun M => (cloOf M 3 3).all fun S => lvlOf S ≤ lvlOf M
-- 閉包の大きさは行を分けない。選定行 (幅 2) 22 個はすべて 13〜40 に収まり、
-- その幅は段をまたいでいる。
def shortWide : List BMS.Matrix :=
  (Rows.rows.filter (fun r : Rows.Row => r.sel != "" && widthOf r.m == 2)).map
    (fun r : Rows.Row => r.m)

#guard shortWide.length == 22
#guard shortWide.all fun M => 13 ≤ (cloOf M 3 3).length && (cloOf M 3 3).length ≤ 40
-- 段 1 の Γ₀ は 40、段 1 の ε_ω は 28、登録済みの ε₀ は 13。
#guard (cloOf [[0, 0], [1, 1], [2, 1], [3, 1]] 3 3).length == 40
#guard (cloOf [[0, 0], [1, 1], [2, 0]] 3 3).length == 28
#guard (cloOf [[0, 0], [1, 1]] 3 3).length == 13

end Evidence.Region
